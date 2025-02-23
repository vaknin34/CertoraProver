import "./nestedImport/e.spec";

use invariant invInE;

invariant invInE() false ;// Should collide with the imported invariant

sort invInE_instate; // Should collide with an auto-generated invariant rule
