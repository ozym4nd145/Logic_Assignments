use "2015CS10262.sml";
open FOL;

Control.Print.printDepth := 100;

val v1 = VAR "v1";
val v2 = VAR "v2";
val v3 = VAR "v3";
val c1 = CONST "c1";
val c2 = CONST "c2";
val c3 = CONST "c3";

val f1 = FUNC("f1",[(VAR "fv1"),(VAR "fv2"),(CONST "kc1")]);

val p1 = PRED("p1",[v1,v2,c2]);
val p2 = PRED("p2",[f1,v3,c3]);

val c1 = AND1(AND1(p1,OR1(p1,p1)),OR1(p1,p1));