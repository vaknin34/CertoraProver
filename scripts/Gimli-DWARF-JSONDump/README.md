Gimli-DWARF-JSONDump
----
This rust program extract DWARF debug information into a JSON dump for further processing on the Kotlin side of CertoraProver 
(see class DebugSymbolLoader). It is based on https://github.com/gimli-rs/gimli a library for reading DWARF debug information 
from LLVM compiled binaries.

The JSON dump will contain all required information to enrich the TAC dump with debug information, this includes start and end 
addresses of function names, start and end ranges of function that have been inlined by the LLVM compiler, formal parameters 
and variable names. We also extract line number information from DWARF to be able to map all addresses back to the source code.  
 
Part of this program is derived from the examples provided in https://github.com/gimli-rs/gimli/tree/master/crates/examples/src/bin