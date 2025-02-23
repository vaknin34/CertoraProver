contract Test {

    uint constant ENTRY_LABEL = 8888;
    uint constant EXIT_LABEL = 9999;


    function simpleLoop() public returns (uint) {
        uint i;
        uint toRet = 0;
        assembly{mstore(ENTRY_LABEL, ENTRY_LABEL)}
        for(i = 0; i < 2; i++) {
            toRet++;
        }
        assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
        return toRet;
    }

    function twoLoops() public returns (uint) {
        uint i;
        uint j;
        uint toRet = 0;
        assembly{mstore(ENTRY_LABEL, ENTRY_LABEL)}
        for(i = 0; i < 2; i++) {
            toRet++;
        }
        assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
        assembly{mstore(ENTRY_LABEL, ENTRY_LABEL)}
        for(j = 0; j < 2; j++) {
            toRet++;
        }
        assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
        return toRet;
    }

    function nestedLoop() public {
        uint i;
        uint toRet = 0;
        assembly{mstore(ENTRY_LABEL, ENTRY_LABEL)}
        for(i = 0; i < 2; i++) {
            assembly{mstore(ENTRY_LABEL, ENTRY_LABEL)}
            for(int j = 0; j < 3; j++) {
                toRet++;
            }
            assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
            toRet++;
        }
        assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
    }

    function nestedRevert() public {
        uint i;
        uint toRet = 0;
        assembly{mstore(ENTRY_LABEL, ENTRY_LABEL)}
        for(i = 0; i < 2; i++) {
            assembly{mstore(ENTRY_LABEL, ENTRY_LABEL)}
            for(int j = 0; j < 3; j++) {
                toRet++;
                if (i == 1 && j == 2)
                {
                    assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
                    revert();
                }
            }
            assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
            toRet++;
        }
        assembly{mstore(EXIT_LABEL, 2)}
    }

    function loopWithReturn() public returns (uint) {
        uint i;
        uint toRet = 0;
        assembly{mstore(ENTRY_LABEL, ENTRY_LABEL)}
        for(i = 0; i < 2; i++) {
            if (i == 1)
            {
                assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
                return toRet;
            }
        }
        assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
        return toRet;
    }

    function loopWithReturn2() public returns (uint) {
        uint i;
        uint toRet = 0;
        int a;
        assembly{mstore(ENTRY_LABEL, ENTRY_LABEL)}
        for(i = 0; i < 2; i++) {
            toRet++;
            if (a == 1)
            {
                assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
                return 1;
            }
        }
        assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
        return toRet;
    }

    function loopWithBreak() public returns (uint) {
        uint i;
        uint toRet = 0;
        int a;
        assembly{mstore(ENTRY_LABEL, ENTRY_LABEL)}
        for(i = 0; i < 2; i++) {
            toRet++;
            if (a == 1)
            {
                break;
            }
        }
        assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
        return toRet;
    }


    function loopWithRevert() public returns (uint) {
        uint i;
        uint toRet = 0;
        int a;
        assembly{mstore(ENTRY_LABEL, ENTRY_LABEL)}
        for(i = 0; i < 2; i++) {
            toRet++;
            if (a == 1)
            {
                assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
                revert();
            }
        }
        assembly{mstore(EXIT_LABEL, EXIT_LABEL)}
        return toRet;
    }
}