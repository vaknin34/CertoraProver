import "Imported.spec";
//Provoke a clash when importing another alias A
import "ImportedB.spec";

methods { function A.blerp() external returns (uint) => NONDET;}
