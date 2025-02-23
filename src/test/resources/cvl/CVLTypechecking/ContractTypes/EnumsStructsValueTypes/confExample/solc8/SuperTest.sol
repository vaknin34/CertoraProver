import './SuperTestLibrary.sol';
import './EnumFile.sol';
contract SuperTest {
    enum EnumInASuperContract { Yeet, McGeet }

    SuperTestLibrary.EnumInALibraryInASuperContract public super_storage_slot;

    function super_storage_slot_is_internal(SuperTestLibrary.EnumInALibraryInASuperContract x) public returns (bool) {
        return x == super_storage_slot;
    }
}

contract Orthogonal {
    enum EnumInAnotherContractInAFileThatsImported { Hope, This, Doesnt, Show, Up }

    function hopeAFinderIsntGenerated(uint256 x) internal pure returns (uint256) {
        return x + x;
    }
}