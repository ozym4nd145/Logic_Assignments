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

val form3 = FORALL("x",OR1(EXISTS("y",PRED("phi",[VAR("y")])),IMP1((EXISTS("z",PRED("psi",[VAR("z")]))),PRED("rho",[VAR("x")]))));
val form4 = IMP1(OR1(PRED("phi",[]),EXISTS("x",PRED("psi",[]))),FORALL("z",PRED("rho",[])))

val refl = FORALL("x",PRED("p",[VAR "x",VAR "x"]));
val euc = FORALL("x",FORALL("y",FORALL("z",IMP1(AND1(PRED("p",[VAR "x",VAR "y"]),PRED("p",[VAR "x",VAR "z"])),PRED("p",[VAR "y",VAR "z"])))));
val symm = FORALL("x",FORALL("y",IMP1(PRED("p",[VAR "x",VAR "y"]),PRED("p",[VAR "y",VAR "x"]))));
val notsymm = NOT1(symm);
val prop = (AND1(euc,AND1(refl,notsymm)));

val standardForm = (standardizeVar prop)
val prenex = makePrenex standardForm
val pcnf = makePCNF prenex
val scnf = makeSCNF pcnf
val set = makeSet scnf
resolve prop;