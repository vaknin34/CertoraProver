contract HookWithUintType {
   mapping (uint256 => uint256) blerp;
   function bloop(uint256 x) external returns (uint256) {
     return blerp[x];
  }
}
