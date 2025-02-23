
use gimli::{AttributeValue, DW_AT_abstract_origin, DW_AT_call_column, DW_AT_call_file, DW_AT_call_line, DW_AT_decl_file, DW_AT_decl_line, DW_AT_frame_base, DW_AT_high_pc, DW_AT_linkage_name, DW_AT_location, DW_AT_low_pc, DW_AT_name, DW_AT_specification, DW_AT_type, DW_TAG_lexical_block, DebugInfo, DebuggingInformationEntry, Error, Operation, UnitHeader };
use object::{Object, ObjectSection};
use rustc_demangle::demangle;
use std::{borrow, env, error, fs::{self, File}, io::{BufWriter, Write}, path};
use serde::{Deserialize, Serialize};
use std::io;
use std::process;


#[derive(Debug, Default)]
struct RelocationMap(object::read::RelocationMap);

impl<'a> gimli::read::Relocate for &'a RelocationMap {
    fn relocate_address(&self, offset: usize, value: u64) -> gimli::Result<u64> {
        Ok(self.0.relocate(offset as u64, value))
    }

    fn relocate_offset(&self, offset: usize, value: usize) -> gimli::Result<usize> {
        <usize as gimli::ReaderOffset>::from_u64(self.0.relocate(offset as u64, value as u64))
    }
}
fn print_usage(opts: &getopts::Options) -> ! {
    let brief = format!("Usage: {} <options> <file>", env::args().next().unwrap());
    write!(&mut io::stderr(), "{}", opts.usage(&brief)).ok();
    process::exit(1);
}
fn main() {
    let mut opts = getopts::Options::new();
    opts.reqopt(
        "i",
        "inputFile",
        "The (relative or absolute) WASM input file ",
        "example.wasm"
    );
    opts.optopt(
        "o",
        "outputFile",
        "The path (relative or absolute) JSON output file",
        "example-dwarf-output.json"
    );
    opts.optflag("d", "demangle", "Demangle names in the output");


    let matches = match opts.parse(env::args().skip(1)) {
        Ok(m) => m,
        Err(e) => {
            writeln!(&mut io::stderr(), "{:?}\n", e).ok();
            print_usage(&opts);
        }
    };


    let input_file_path = if let Some(r) = matches.opt_str("i") {
        r
    } else {
        print_usage(&opts)
    };

    let mut flags = Flags::default();
    if matches.opt_present("d") {
        flags.demangle = true;
    } else{
        flags.demangle = false;
    }
    flags.output_file_path = if let Some(r) = matches.opt_str("o") {
        Some(r)
    } else {
        None
    };


    let file = fs::File::open(input_file_path).unwrap();
    let mmap = unsafe { memmap2::Mmap::map(&file).unwrap() };
    let object = object::File::parse(&*mmap).unwrap();
    let endian = if object.is_little_endian() {
        gimli::RunTimeEndian::Little
    } else {
        gimli::RunTimeEndian::Big
    };

    generate_jsondump(&flags, &object, endian).unwrap();
}

fn generate_jsondump(
    flags: &Flags,
    object: &object::File,
    endian: gimli::RunTimeEndian,
) -> Result<(), Box<dyn error::Error>> {

    // Load a section and return as `Cow<[u8]>`.
    let load_section = |id: gimli::SectionId| -> Result<borrow::Cow<[u8]>, Box<dyn error::Error>> {
        Ok(match object.section_by_name(id.name()) {
            Some(section) => section.uncompressed_data()?,
            None => borrow::Cow::Borrowed(&[]),
        })
    };

    // Borrow a `Cow<[u8]>` to create an `EndianSlice`.
    let borrow_section = |section| gimli::EndianSlice::new(borrow::Cow::as_ref(section), endian);

    // Load all of the sections.
    let dwarf_sections = gimli::DwarfSections::load(&load_section)?;

    // Create `EndianSlice`s for all of the sections.
    let dwarf = dwarf_sections.borrow(borrow_section);
    let debug_info_section = dwarf_sections.debug_info.borrow( borrow_section);

    // Iterate over the compilation units.
    let mut iter = dwarf.units();
    let mut compilation_unit_vec = Vec::new();
    while let Some(header) = iter.next()? {

        let address = header.offset().as_debug_info_offset().unwrap().0;
        let root_node = process_header(header, &dwarf, &debug_info_section, flags)?;


        let unit = dwarf.unit(header)?;
        let unit = unit.unit_ref(&dwarf);
        let mut line_info = Vec::new();


        // Get the line program for the compilation unit.
        if let Some(program) = unit.line_program.clone() {
            let comp_dir = if let Some(ref dir) = unit.comp_dir {
                path::PathBuf::from(dir.to_string_lossy().into_owned())
            } else {
                path::PathBuf::new()
            };

            // Iterate over the line program rows.
            let mut rows = program.rows();
            while let Some((header, row)) = rows.next_row()? {
                if row.end_sequence() {
                    // End of sequence indicates a possible gap in addresses.
                    line_info.push(LineNumberInfo{
                        address: row.address(),
                        file_path: "end-sequence".to_owned(),
                        line: 0,
                        col: 0
                    })
                } else {
                    // Determine the path. Real applications should cache this for performance.
                    let mut path = path::PathBuf::new();
                    if let Some(file) = row.file(header) {
                        path.clone_from(&comp_dir);

                        // The directory index 0 is defined to correspond to the compilation unit directory.
                        if file.directory_index() != 0 {
                            if let Some(dir) = file.directory(header) {
                                path.push(unit.attr_string(dir)?.to_string_lossy().as_ref());
                            }
                        }

                        path.push(
                            unit.attr_string(file.path_name())?
                                .to_string_lossy()
                                .as_ref(),
                        );
                    }

                    // Determine line/column. DWARF line/column is never 0, so we use that
                    // but other applications may want to display this differently.
                    let line = match row.line() {
                        Some(line) => line.get(),
                        None => 0,
                    };
                    let column = match row.column() {
                        gimli::ColumnType::LeftEdge => 0,
                        gimli::ColumnType::Column(column) => column.get(),
                    };

                    line_info.push(LineNumberInfo{
                        address: row.address(),
                        file_path: path.display().to_string(),
                        line: line,
                        col: column
                    })
                }
            }
        }
        compilation_unit_vec.push(CompilationUnit{
            address: format!("{:x}",address),
            line_number_info: line_info,
            dwarf_node: root_node}
        )
    }


    match &flags.output_file_path {
        Some(output_path) => {
            let file = File::create(output_path.clone())?;
            let mut writer = BufWriter::new(file);
            serde_json::to_writer(&mut writer, &compilation_unit_vec)?;
        }
        None => {
            println!("{}", serde_json::to_string_pretty(&compilation_unit_vec).unwrap());
        }
    }
   
    Ok(())
}

fn process_header<R>(header: UnitHeader<R>, dwarf: &gimli::Dwarf<R>, debug_info_section: &DebugInfo<R>, flags: &Flags) -> Result<DWARFSerializableTreeNode, gimli::Error>
where R: gimli::Reader{

    let unit = dwarf.unit(header)?;
    let unit_ref = unit.unit_ref(&dwarf);

    let mut tree = unit_ref.entries_tree(None)?;
    let root = tree.root()?;


    let node = process_tree( &debug_info_section, unit_ref, dwarf,  root, flags, 0)?;
    Ok(node)
}

/*
* This function takes a DIE and extracts the relevant attributes that will be persisted to JSON.
*
* The function calls itself recursively to resolve child attributes that contain relevant attributes in other places of the DWARF.
* When an attribute contains a UnitRef, this refers to another location in DWARF. This is the case, for instance, with DW_AT_specification.
* This UnitRef must first be resolved and on the resulting node, the function is called recursively.
 */
#[allow(non_upper_case_globals)]
fn create_dwarf_node_from_attr<R>(entry: &DebuggingInformationEntry<'_,'_,R>, unit_ref: gimli::UnitRef<'_,R>, dwarf: &gimli::Dwarf<R>, flags: &Flags, depth: u32) -> Result<DWARFSerializableTreeNode,Error>
where R: gimli::Reader
{
    let mut low_pc_value =None;
    let mut high_pc_value = None;
    let mut name = None;
    let mut decl_file = None;
    let mut linkage_name = None;
    let mut decl_line = None;

    let mut call_file = None;
    let mut call_line = None;
    let mut column = None;
    let mut type_name = None;
    let mut variable_offset = None;
    let mut variable_index = None;
    let mut frame_base = None;

    let mut attrs = entry.attrs();


    while let Some(attr) = attrs.next()? {
        //This code part needs refactorings...
        match attr.name() {

            DW_AT_frame_base => {
                if let Some(s) = attr.exprloc_value() {
                    let mut iter = s.operations(unit_ref.encoding());
                    while let Some(op) = iter.next()?{
                        match op {
                            Operation::WasmLocal{index
                            } => {
                                frame_base = Some(FrameBase{frame_base_type: "WasmLocal".to_owned(), index: index})
                            },
                            _ => ()
                        }
                    }
                }
            }
            DW_AT_location => {
                if let Some(s) = attr.exprloc_value() {
                    let mut iter = s.operations(unit_ref.encoding());
                    while let Some(op) = iter.next()?{
                        match op {
                            Operation::FrameOffset{offset
                            } => {
                                variable_offset = Some(offset)
                            },
                            Operation::WasmLocal{index
                            } => {
                                variable_index = Some(index)
                            },
                            _ => ()
                        }
                    }
                }
            }
            DW_AT_low_pc => {
                if let Ok(s) = unit_ref.attr_address(attr.value()) {
                    low_pc_value = s;
                }
            }
            DW_AT_high_pc => {
                match attr.value() {
                    AttributeValue::Udata(val) => high_pc_value = low_pc_value.map(|size| size + val),
                    attr =>
                        high_pc_value = unit_ref.attr_address(attr)?

                }
            }
            DW_AT_decl_file => {
                match attr.value() {
                    AttributeValue::FileIndex(val) => decl_file = dump_file_index(val, unit_ref),
                    _ => ()
                }
            }
            DW_AT_decl_line => {
                match attr.value() {
                    AttributeValue::Udata(val) => call_line = Some(val),
                    _ => ()
                }
            }
            DW_AT_call_file =>{
                match attr.value() {
                    AttributeValue::FileIndex(val) => call_file = dump_file_index(val, unit_ref),

                    _ => ()
                }
            }
            DW_AT_call_line => {
                match attr.value() {
                    AttributeValue::Udata(val) => call_line = Some(val),
                    _ => ()
                }
            }
            DW_AT_call_column => {
                match attr.value() {
                    AttributeValue::Udata(val) => column = Some(val),
                    _ => ()
                }
            }

            DW_AT_linkage_name =>{
                if let Ok(s) = unit_ref.attr_string(attr.value()) {
                    if let Ok(t) = s.to_string_lossy(){
                        let demangled = if flags.demangle {
                            format!("{:#}", demangle(&t.into_owned()))
                        } else{
                            format!("{}", t)
                        };
                        linkage_name = Some(format!("{}", demangled));
                    }

                }

                match attr.value() {
                    AttributeValue::DebugStrRef(r) => {
                        if let Ok(s) = dwarf.string(r) {
                            if let Ok(t) = s.to_string_lossy(){
                                let demangled = if flags.demangle {
                                    format!("{:#}", demangle(&t.into_owned()))
                                } else{
                                    format!("{}", t)
                                };
                                linkage_name = Some(format!("{}",demangled));
                            }
                        }

                    }
                    _ => ()
                }
            }
            DW_AT_name =>{
                if let Ok(s) = unit_ref.attr_string(attr.value()) {
                    if let Ok(t) = s.to_string_lossy(){
                        let demangled = if flags.demangle {
                            format!("{}", demangle(&t.into_owned()))
                        } else{
                            format!("{}", t)
                        };
                        name = Some(format!("{}", demangled));
                    }

                }

                match attr.value() {
                    AttributeValue::DebugStrRef(r) => {
                        if let Ok(s) = dwarf.string(r) {
                            if let Ok(t) = s.to_string_lossy(){
                                let demangled = if flags.demangle {
                                    format!("{}", demangle(&t.into_owned()))
                                } else{
                                    format!("{}", t)
                                };
                                name = Some(format!("{}",demangled));
                            }
                        }

                    }
                    _ => ()
                }
            }
            DW_AT_abstract_origin |
            DW_AT_specification => {
                //For these attributes, try to resolve the address recursively and push up all information from child to parent.
                //Please note, we don't currently maintain the entire tree of the information.
                //Theoretically, we loose information here as.
                match attr.value() {
                    AttributeValue::UnitRef(v) => {
                        if let Ok(r) = unit_ref.entry(v) {
                            if depth + 1 <= 2 {
                                if let Ok(t) = create_dwarf_node_from_attr(&r, unit_ref, dwarf, flags, depth + 1){
                                    if linkage_name == None{ linkage_name = t.linkage_name}
                                    if name == None{ name = t.name}
                                    if decl_file == None{ decl_file = t.decl_file}
                                    if decl_line == None{ decl_line = t.decl_line}
                                    if call_file == None{ call_file = t.call_file}
                                    if call_line == None{ call_line = t.call_line}
                                    if column == None{ column = t.column}
                                }
                            }
                        }
                    }
                    _ => ()
                }
            }
            DW_AT_type => {
                match attr.value() {
                    AttributeValue::UnitRef(v) => {
                        if let Ok(r) = unit_ref.entry(v) {
                            if depth + 1 <= 2 {
                                if let Ok(t) = create_dwarf_node_from_attr(&r, unit_ref, dwarf, flags, depth + 1){
                                    //
                                    // Resolve the reference and then assign name to type_name.
                                    // The logic here differs from the other locations: DW_AT_specification and DW_AT_abstract_origin
                                    //
                                    if type_name == None{ type_name = t.name}
                                }
                            }
                        }
                    }
                    _ => ()
                }
            }
            _ => ()
        }

    }
    Ok(DWARFSerializableTreeNode{
        depth: 0,
        dwarf_node_tag: None,
        children: Vec::new(),
        low_pc_value,
        high_pc_value,
        name,
        decl_file,
        linkage_name,
        type_name,
        column,
        decl_line,
        call_file,
        call_line,
        variable_offset,
        variable_index,
        frame_base
    })
}

fn process_tree<R>(debug_info_section: &DebugInfo<R>, unit_ref: gimli::UnitRef<R>, dwarf: &gimli::Dwarf<R>, node: gimli::EntriesTreeNode<R>, flags: &Flags, depth: u32) -> Result<DWARFSerializableTreeNode, gimli::Error>
where R: gimli::Reader
{

    let tag = node.entry().tag();
    let dwarf_node_tag = Some(format!("{}", tag));
    let json_attr_node = create_dwarf_node_from_attr(node.entry(), unit_ref, dwarf, flags, 0)?;

    let mut children = node.children();


    let next_depth = depth + 1;
    let mut json_children = Vec::new();
    while let Some(child) = children.next()? {
        // Recursively process a child.
        let json_result = process_tree(debug_info_section, unit_ref,dwarf, child, flags, next_depth);
        match json_result {
            Ok(res) => {
                    //We don't care about lexical blocks, this line just tells us to skip lexical blocks (i.e. by copying all information to the parent.)
                    //comparing strings - needs to be cleaned up.
                    if res.dwarf_node_tag == Some(format!("{}", DW_TAG_lexical_block)){
                        json_children.extend(res.children);
                    } else{
                        json_children.push(res)
                    }
                }
            _ => ()
        }

    }
    let curr_node = DWARFSerializableTreeNode{
        depth: depth,
        dwarf_node_tag: dwarf_node_tag,
        children: json_children,
        ..json_attr_node
    };
    Ok(curr_node)
}



fn dump_file_index<R>(
    file_index: u64,
    unit: gimli::UnitRef<R>,
) -> Option<String>
where R: gimli::Reader {
    if file_index == 0 && unit.header.version() <= 4 {
        return None;
    }
    let mut res: String = "".to_owned();
    let header = match unit.line_program {
        Some(ref program) => program.header(),
        None => return None,
    };
    let file = match header.file(file_index) {
        Some(file) => file,
        None => {
            return None;
        }
    };
    if let Some(directory) = file.directory(header) {
        let directory = unit.attr_string(directory).unwrap();
        let directory = directory.to_string_lossy().unwrap();
        if file.directory_index() != 0 && !directory.starts_with('/') {
            if let Some(ref comp_dir) = unit.comp_dir {
                res.push_str(&format!("{}/", comp_dir.to_string_lossy().unwrap()));
            }
        }
        res.push_str(&format!("{}/", directory));
    }
    res.push_str(&unit.attr_string(file.path_name()).unwrap().to_string_lossy().unwrap());
    Some(res)
}



//Data structures for JSON serialization below
#[derive(Serialize, Deserialize)]
struct DWARFSerializableTreeNode {
    children: Vec<DWARFSerializableTreeNode>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    low_pc_value: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    high_pc_value: Option<u64>,
    depth: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    dwarf_node_tag: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    decl_line: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    decl_file: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    call_file: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    call_line: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    linkage_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    type_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    column: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    variable_offset: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    variable_index: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    frame_base: Option<FrameBase>
}

#[derive(Serialize, Deserialize)]
struct CompilationUnit{
    dwarf_node: DWARFSerializableTreeNode,
    line_number_info: Vec<LineNumberInfo>,
    address: String
}

#[derive(Serialize, Deserialize)]
struct FrameBase{
    frame_base_type: String,
    index: u32
}

#[derive(Serialize, Deserialize)]
struct LineNumberInfo{
    address: u64,
    file_path: String,
    col: u64,
    line: u64
}
#[derive(Default)]
struct Flags {
    demangle: bool,
    output_file_path: Option<String>
}
