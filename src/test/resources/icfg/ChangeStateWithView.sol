pragma experimental ABIEncoderV2;

// For each function in this contract the documentation says what we will test with it.
//      Sanity - Test inserting a view function v to f, and then check end of f is reachable.
//      Same input = Same Output - Insert two view functions, assume the input is equal and
//                                  verify output is equal.
//      Different Input -> Different Output - Insert two view functions, and verify output is not equal.
contract Test {
    uint constant INSERT_LABEL = 8888;

    uint public foo;

    struct RetType {
        address a;
        bool b;
    }

    mapping (address => RetType) mappy;
    mapping (address => address) amappy;
    mapping (address => RetType) yppam;
    bytes bs;

    struct Book {
        string title;
        string author;
        uint book_id;
    }

    // Read output == 100 test
    function constantReturn(uint x, uint y) public view returns (uint) {
        return 100;
    }

    // Same input = Same Output
    // Different Input -> Different Output
    // Sanity
    function updateBookTitle(Book memory b) view public returns (string memory) {
        b.title = string(abi.encodePacked(b.title, ", but good"));
        return b.title;
    }

    // Check changing memory changes original value. Insert bookId updater between two get book id.
    function getBookId(Book memory b) view public returns (uint) {
        return b.book_id;
    }

    function updateBookId(Book memory b) view public {
        b.book_id = b.book_id + 5;
    }


    // Same input = Same Output
    // Different Input -> Different Output
    // Sanity
    function getBalance(address a, bool b) public view returns (address, bool) {
        if (b) {
            RetType memory ret = mappy[a];
            return (ret.a, ret.b);
        } else {
            RetType memory ret = yppam[a];
            return (ret.a, ret.b);
        }
    }

    // Sanity
    // Same input = Same Output
    // Different Input -> Different Output
    function twoParams(uint x, uint y) public view returns (uint) {
        return x + y;
    }

    // Sanity
    // Same input = Same Output
    // Different Input -> Different Output
    // Check output manually
    function lnot(bool b) public view returns (bool) {
        return !b;
    }

    // Sanity
    // Same input = Same Output
    // Different Input -> Different Output
    function memoryArgs(uint x, uint y, uint[] memory arr, Book memory book, Book[] memory books) public view returns (uint) {
        return x + y;
    }

    // Sanity
    // Same input = Same Output
    // Different Input -> Different Output
    function swag(uint x) view public returns (uint) {
        return foo + x;
    }

    // Change state test
    function blazeit(uint x) public {
        uint y = this.swag(x);
        foo += y;
        foo += x;
    }

    // Sanity
    // Same input = Same Output
    // Different Input -> Different Output
    function recurseTimes10(uint x) public view returns (uint) {
        if (x == 0) {
            return x;
        }
        return 10 + recurseTimes10(x - 1);
    }

    // Sanity
    // Same input = Same Output
    // Different Input -> Different Output
    function loopTimes10(uint x) public view returns (uint) {
        uint res = 0;
        for (uint i = 0; i < x; i++) {
            res += 10;
        }
        return res;
    }

    function test() public {
        uint origin = foo;
        assembly{mstore(INSERT_LABEL, INSERT_LABEL)}
        foo -= 1;
        assembly{mstore(INSERT_LABEL, INSERT_LABEL)}
    }
}
