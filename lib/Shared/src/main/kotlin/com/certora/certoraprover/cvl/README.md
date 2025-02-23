Java AST
========

These classes are here for historical reasons.  In the long long ago, we thought that we couldn't create Kotlin objects
directly from CUP, so we added an intermediate AST representation in Java.  The parser produced the Java AST objects,
and then a "kotlinization" pass converted the Java AST objects to the Kotlin AST.

Along the way, we started adding some other things to the kotlinization pass, so when we realized we could just create
the Kotlin objects from CUP, we couldn't just skip the Java AST entirely.  We still need the "kotlinization" pass.

However, Kotlin is a lot easier to work in than Java, so the classes in this package are direct translations of the old
Java AST and the kotlinization pass.

The hope is that we can remove the duplication here and just parse directly into the "real" kotlin AST.  To do so, we
need to analyze what the kotlinization is actually doing and add proper passes to do those things.  This is left for
future work.  You're welcome for the legacy code.
