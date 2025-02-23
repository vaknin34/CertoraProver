import "nestedImport/e.spec";

use invariant invInE;

sort invInE_instate; // Should collide with an auto-generated invariant rule

rule invInE(address addr) {  // Should collide with the imported invariant
    assert false;
}
