pragma experimental ABIEncoderV2;

contract Test {
    struct Static {
        Dynamic yeet;
        uint b;
    }
    struct Dynamic {
        uint[] yolo;
        uint swag;
    }
    struct NestedDynamic {
        uint[][3] smokeWeed;
        uint b;
    }
    function test(uint256 n) public pure returns (uint) {
        uint[] memory yolo = new uint[](n);
        uint[][3] memory yeet = [yolo, yolo, yolo];
        Dynamic memory blazeit = Dynamic({
        yolo: yolo,
        swag: n
        });
        NestedDynamic memory everyday = NestedDynamic({
        smokeWeed: yeet,
        b: n
        });
        bytes memory x = abi.encode(yeet, blazeit, everyday);
        return x.length;
    }
}
