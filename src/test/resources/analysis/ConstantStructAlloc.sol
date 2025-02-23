contract Test {
   struct Foo {
      uint x;
      uint y;
   }
   function test() public {
      Foo[] memory x = new Foo[](1);
   }
}