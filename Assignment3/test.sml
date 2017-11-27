use "2015CS10262.sml";
open FOL;

Control.Print.printDepth := 100;

val refl = FORALL("x",PRED("p",[VAR "x",VAR "x"]));
val euc = FORALL("x",FORALL("y",FORALL("z",IMP1(AND1(PRED("p",[VAR "x",VAR "y"]),PRED("p",[VAR "x",VAR "z"])),PRED("p",[VAR "y",VAR "z"])))));
val symm = FORALL("x",FORALL("y",IMP1(PRED("p",[VAR "x",VAR "y"]),PRED("p",[VAR "y",VAR "x"]))));
val notsymm = NOT1(symm);
val prop = (AND1(notsymm,AND1(refl,euc)));

resolve prop;

val form1 = IMP1(PRED("p",[VAR("x")]),PRED("q",[VAR("x")]));
val form2 = FORALL("x",form1);
val form3 = PRED("p",[CONST("a")]);
val form4 = NOT1(PRED("q",[CONST("a")]));
val form5 = AND1(form1,form2);
val form6 = AND1(form3,form4);
val form7 = AND1(form5,form6);

val form8 = IMP1(PRED("p",[VAR("x")]),PRED("q",[VAR("x")]));
val form9 = PRED("p",[CONST("a")]);
val form10 = NOT1(PRED("q",[CONST("a")]));
val form11 = AND1(form8,form9);
val form12 = AND1(form10,form11);
