contract HookWithBytesType {
   mapping (bytes => uint) blerp;
   function bloop(bytes memory x) external returns (uint) {
      return blerp[x];
   }
}
