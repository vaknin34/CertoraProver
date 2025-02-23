contract HookWithStringType {
   mapping (string => uint) blerp;
   function bloop(string memory x) external returns (uint) {
      return blerp[x];
   }

   function loadString() external returns (uint) {
      return blerp["abc"];
   }


}
