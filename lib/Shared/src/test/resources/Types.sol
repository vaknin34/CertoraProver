// This contract is used for [TestCVL.testCVLTypes]

struct TopLevelStruct {
    uint w;
}

enum TopLevelEnum {
    TOP_LEVEL_1, TOP_LEVEL_2
}

type TopLevelUDVT is uint;

contract Contract {
    struct ExampleStruct {
        uint x;
    }

    enum ExampleEnum {
        VALUE1, VALUE2
    }

    type ExampleUDVT is uint;

    Inheriting x;
}

contract Secondary {
    struct SecondaryStruct {
        uint y;
    }
}

interface Interface {
    struct InterfaceStruct {
        uint z;
    }
}

contract Inheriting is Interface {
}

