contract Test {
    mapping (address => string) yolo;
    function test() public returns (string memory) {
        return yolo[msg.sender];
    }
}