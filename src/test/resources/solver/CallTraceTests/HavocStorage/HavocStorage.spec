using HavocStorage as t;

rule havoc_of_storage_path_is_recognized() {
    env e;
    address k;
    uint i;

    require t.a[k][i].bar[i];           // force storage value to true
    bool value_at_i = t.a[k][i].bar[i]; // storage path for this value should now be concrete in StorageState

    havoc t.a[k][i].bar[i];
    
    assert t.a[k][i].bar[i], "should fail (value has been havoced and can change)";
}