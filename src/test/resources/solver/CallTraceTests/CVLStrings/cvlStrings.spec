methods {
    function short() external returns (string) envfree;
    function medium() external returns (string) envfree;
    function long() external returns (string) envfree;
}

rule simpleStringNeqShort {
    string s1 = "Abcde";
    string s2 = short();
    assert s1 == s2;
}

rule simpleStringNeqMedium {
    string s1 = "Abcde";
    string s2 = medium();
    assert s1 == s2;
}

rule simpleStringNeqLong {
    string s1 = "Abcde";
    string s2 = long();
    assert s1 == s2;
}

rule makeOneUp1 {
    string s1;
    string s2 = medium();
    require s1.length == s2.length;
    assert s1 == s2;
}

rule makeOneUp2 {
    string s1;
    require s1.length == 12;
    bytes1 b0 = s1[0];
    // require b0 == to_bytes1(0x61); // seems like we're not ready for that?? -- getting vacuity..
    assert false;
}


