/*
 *     The Certora Prover
 *     Copyright (C) 2025  Certora Ltd.
 *
 *     This program is free software: you can redistribute it and/or modify
 *     it under the terms of the GNU General Public License as published by
 *     the Free Software Foundation, version 3 of the License.
 *
 *     This program is distributed in the hope that it will be useful,
 *     but WITHOUT ANY WARRANTY; without even the implied warranty of
 *     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *     GNU General Public License for more details.
 *
 *     You should have received a copy of the GNU General Public License
 *     along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

/**
*  Base file for TAC.jflex, TACExprInfix.jflex
*  (using the %include directive - which copy paste the content of this file)
*/

%{
        boolean DEBUG = false;
        private StringBuffer sb, jsonBuffer;
        private Stack<Character> jsonBracketCounter = new Stack<>();
        private ComplexSymbolFactory symbolFactory;
        private int csline,cscolumn;
        private int prevState = YYINITIAL;
        public String theFilename;
        private void startState(int s) {
          debug("starting state:" + s);
          yybegin(s);
        }


        private void startJson(char c) {
          prevState = yystate();
          jsonBracketCounter.empty();
          jsonBracketCounter.push(c);
          jsonBuffer = new StringBuffer();
          jsonBuffer.append(c);
          startState(S_ParseJSON);
        }

        private boolean closeJsonParsing(char c) throws IOException{
            String expected;
            if (c=='[') {
                expected = String.valueOf(']');
            }
            else if (c == '{') {
                expected = String.valueOf('}');
            }
            else {
                assert(false);
                throw new IOException("Illegal character:" + c);
            }
            if (!expected.equals(yytext()))
                throw new IOException("found: " + yytext() + ", after: " + c);
            else if (jsonBracketCounter.isEmpty()) {
                return true;
            }
            return false;
        }
        //resets the data structures and returns a string
        private String endJsonParsing() {
          String ret = jsonBuffer.toString();
          startState(prevState);
          jsonBuffer = null;
          return ret;
        }

        private void debug(String ... args) {
          if (DEBUG) {
              System.out.println("[" + String.join(", ",args) + "] in line:" + yyline + ", col: "+ yycolumn);
          }
        }
         public Symbol symbol(int code,String name) {
                return symbolFactory.newSymbol(name, code,
                                new Location(yyline+1,yycolumn+1, yychar), // -yylength()
                                new Location(yyline+1,yycolumn+yylength(), yychar+yylength())
                        );
                }
                public Symbol symbol(int code, String name, String lexem) {
                return symbolFactory.newSymbol(name, code,
                                    new Location(yyline+1, yycolumn +1, yychar),
                                    new Location(yyline+1,yycolumn+yylength(), yychar+yylength()), lexem);
                }
                   public Symbol symbol(int id, String name, Object value) {
                  return symbolFactory.newSymbol(name, id,
                          new Location(yyline+1, yycolumn +1, yychar),
                          new Location(yyline+1,yycolumn+yylength(), yychar+yylength()), value);
                }
%}

LineTerminator = \r|\n|\r\n
InputCharacter = [^\r\n]
JsonInputCharacter = [^\r\n\{\}\"\[\]]
WhiteSpace     = {LineTerminator} | [ \t\f]
WhiteSpaceNoLineTerminator = [ \t\f]
UNESCAPED_CH = [^\"\\]
/* comments */
Comment = {TraditionalComment} | {EndOfLineComment} | {DocumentationComment}
TraditionalComment   = "/*" [^*] ~"*/" | "/*" "*"+ "/"
// Comment can be the last line of the file, without line terminator.
EndOfLineComment     = "//" {InputCharacter}* {LineTerminator}?
DocumentationComment = "/**" {CommentContent} "*"+ "/"
CommentContent       = ( [^*] | \*+ [^/*] )*
TACVarIdentifier = [A-Za-z_][A-Za-z_!$\.0-9]* //TAC vars can also contain "!,$"
DecimalLiteral = [0-9]+
BlockIdentifier = ({DecimalLiteral}_)+{DecimalLiteral}
DecIntegerLiteral = 0 | [1-9][0-9]*
builtInTags = ("bv" [0-9]+)
            | "bool"
            | "bytemap"
            | "wordmap"
            | "doublemap"
            | "robytemap"
            | "int"
            | "uf"
            | "rawarray"
            | "complexarray"
            | "array_Signed"
            | "array_Unsigned"
            | "array_Boolean"

tagName =  {builtInTags}

tagNameProduct = {tagName}
  | {tagName} "*" {tagNameProduct}



Hex = "0x"-?[0-9a-fA-F]+
booleanLiteral =  "true" | "false"

funcSym = name={value} #GhostFuncSym
  | name={identifierWithMetaArgs} ":bif" #BuiltinFuncSym

CmdName =   "JumpiCmd"
            |  "JumpdestCmd"
            |  "JumpCmd"
            |  "AssignExpCmd"
            |  "CallCore"
            |  "AssertCmd"
            |  "LabelCmd"
            |  "AssignSymCmd"
            |  "AssignAddCmd"
            |  "AssignMulCmd"
            |  "AssignSubCmd"
            |  "AssignDivCmd"
            |  "AssignSdivCmd"
            |  "AssignModCmd"
            |  "AssignSmodCmd"
            |  "AssignAddModCmd"
            |  "AssignMulModCmd"
            |  "AssignExponentCmd"
            |  "AssignSignextendCmd"
            |  "AssignLtCmd"
            |  "AssignGtCmd"
            |  "AssignSltCmd"
            |  "AssignSgtCmd"
            |  "AssignEqCmd"
            |  "AssignAndCmd"
            |  "AssignOrCmd"
            |  "AssignXorCmd"
            |  "AssignNotCmd"
            |  "AssignSha3Cmd"
            |  "AssignSimpleSha3Cmd"
            |  "AssignPcCmd"
            |  "AssignMsizeCmd"
            |  "AssignGasCmd"
            |  "LogCmd"
            |  "ReturnCmd"
            |  "ReturnSymCmd"
            |  "RevertCmd"
            |  "ThrowICmd"
            |  "AccessVarStoreCmd"
            |  "AccessVarSetCmd"
            |  "Original"
            |  "BeforeOriginal"
            |  "ReplacingOriginal"
            |  "ReplacingOriginalWithBlocks"
            |  "AssumeCmd"
            |  "AssumeNotCmd"
            |  "AssumeEqCmd"
            |  "AssumeAccessSelectEqCmd"
            |  "AssignSelectCmd"
            |  "AssignStoreCmd"
            |  "AssignSelect2DCmd"
            |  "AssignStore2DCmd"
            |  "ReturnFromCallback"
            |  "AssignInitArray"
            |  "AssignHavocCmd"
            |  "AssumeAccessVarForAll"
            |  "TransferBalance"
            |  "AssignIsException"
            |  "SetExceptionConditional"
            |  "NopCmd"
            |  "ThrowCmd"
            |  "AssignShiftLeft"
            |  "AssignShiftRightLogical"
            |  "AssignShiftRightArithmetical"
            |  "WordLoad"
            |  "WordStore"
            |  "ByteLoad"
            |  "ByteStore"
            |  "ByteLoadFromRO"
            |  "ByteStoreSingle"
            |  "ByteLongCopy"
            |  "AnnotationCmd"
            |  "AssumeExpCmd"
            |  "SummaryCmd"

expressionFunctions = "BV2Int"
      | "IntMul"
      | "IntDiv"
      | "IntMod"
      | "IntAdd"
      | "IntSub"
      | "Add"
      | "Sub"
      | "Mul"
      | "Div"
      | "SDiv"
      | "Mod"
      | "SMod"
      | "Ite"
      | "Eq"
      | "Sle"
      | "Le"
      | "Slt"
      | "Lt"
      | "Sge"
      | "Ge"
      | "Sgt"
      | "Gt"
      | "Exponent"
      | "IntExponent"
      | "BWAnd"
      | "BWOr"
      | "BWXOr"
      | "BWNot"
      | "ShiftRightLogical"
      | "ShiftRightArithmetical"
      | "ShiftLeft"
      | "Select"
      | "DoubleSelect"
      | "ResetStore"
      | "Store"
      | "LongStore"
      | "LAnd"
      | "LOr"
      | "LNot"
      | "SolVar"
      | "Forall"
      | "Exists"
      | "Hash"
      | "SimpleHash"
      | "SignExtend"
      | "MulMod"
      | "AddMod"
      | "MultiDimStore"
