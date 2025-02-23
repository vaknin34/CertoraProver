library TestLibrary {
    enum EnumInALibrary { Wad, Ray, Sol }

    enum DuplicateEnum { Ruh, Roh }

    struct StructInALibrary {
        EnumInALibrary theEnum;
        uint256 theUint;
    }
}