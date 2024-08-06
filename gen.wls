(* convert expr to egg *)
f[Plus[x_,y_]]:= StringTemplate["(+ `1` `2`)"][f[x], f[y]];
f[Subtract[x_,y_]]:= StringTemplate["(- `1` `2`)"][f[x], f[y]];
f[Times[x_,y_]]:= StringTemplate["(* `1` `2`)"][f[x], f[y]];
f[Divide[x_,y_]]:= StringTemplate["(/ `1` `2`)"][f[x], f[y]];
f[Power[x_,y_]]:= StringTemplate["(^ `1` `2`)"][f[x], f[y]];
f[Sin[x_]] := StringTemplate["(sin `1`)"][f[x]];
f[sin[x_]] := StringTemplate["(sin `1`)"][f[x]];
f[Cos[x_]] := StringTemplate["(cos `1`)"][f[x]];
f[cos[x_]] := StringTemplate["(cos `1`)"][f[x]];
f[Tan[x_]] := StringTemplate["(tan `1`)"][f[x]];
f[tan[x_]] := StringTemplate["(tan `1`)"][f[x]];

f[ArcSin[x_]] := StringTemplate["(arcsin `1`)"][f[x]];
f[ArcCos[x_]] := StringTemplate["(arccos `1`)"][f[x]];
f[ArcTan[x_]] := StringTemplate["(arctan `1`)"][f[x]];

f[Gamma[x_,y_]] := StringTemplate["(gamma `1` `2`)"][f[x], f[y]];
f[ArcTan[x_]] := StringTemplate["(arctan `1`)"][f[x]];
f[Sqrt[x_]] := StringTemplate["(sqrt `1`)"][f[x]];
f[Log[x_]] := StringTemplate["(ln `1`)"][f[x]];
f[Int[k_, x_]] := StringTemplate["(i `1` `2`)"][f[k], f[x]];
f[x_Symbol] := "?" <> ToString[x];
f[x_?IntegerQ] := ToString[x];
f[x_Rational] := StringTemplate["(/ `1` `2`)"][ToString[Numerator[x]], ToString[Denominator[x]]];

pred[And[x_,y_]] := StringTemplate["(`1` && `2`)"][pred[x],pred[y]];
pred[Or[x_,y_]] := StringTemplate["(`1` || `2`)"][pred[x], pred[y]];
pred[Not[x_]] := StringTemplate["(!`1`)"][pred[x]];
pred[GtQ[expr_, y_]] := StringTemplate["pred`len`( `parmlist`  , |`parm`| `expr1` > (`y`).into())"][
    <| 
        "len" -> Length[Variables[expr]],
        "parmlist" -> (Variables[expr] // Map[StringTemplate["\"?``\""]] // ToString // StringTake[#, {2,-2}]&) ,
        "parm" -> (Variables[expr] // ToString // StringTake[#, {2,-2}]&),
        "expr" -> expr,
        "y" -> y,
        "expr1" -> (CForm[expr] // ToString)
    |>];

pred[LtQ[expr_, y_]] := StringTemplate["pred`len`( `parmlist`  , |`parm`| `expr1` < (`y`).into())"][
    <| "len" -> Length[Variables[expr]],
        "parmlist" -> (Variables[expr] // Map[StringTemplate["\"?``\""]] // ToString // StringTake[#, {2,-2}]&) ,
        "parm" -> (Variables[expr] // ToString // StringTake[#, {2,-2}]&),
        "expr" -> expr,
        "y" -> y,
        "expr1" -> (CForm[expr] // ToString)
    |>];
pred[EqQ[expr_, y_]] := StringTemplate["pred`len`( `parmlist`  , |`parm`| `expr1` == (`y`).into())"][
    <| "len" -> Length[Variables[expr]],
        "parmlist" -> (Variables[expr] // Map[StringTemplate["\"?``\""]] // ToString // StringTake[#, {2,-2}]&) ,
        "parm" -> (Variables[expr] // ToString // StringTake[#, {2,-2}]&),
        "expr" -> expr,
        "y" -> y,
        "expr1" -> (CForm[expr] // ToString)
    |>];
pred[NeQ[expr_, y_]] := StringTemplate["pred`len`( `parmlist`  , |`parm`| `expr1` != (`y`).into())"][
    <| "len" -> Length[Variables[expr]],
        "parmlist" -> (Variables[expr] // Map[StringTemplate["\"?``\""]] // ToString // StringTake[#, {2,-2}]&) ,
        "parm" -> (Variables[expr] // ToString // StringTake[#, {2,-2}]&),
        "expr" -> expr,
        "y" -> y,
        "expr1" -> (CForm[expr] // ToString)
    |>];
pred[IGtQ[expr_, y_]] := StringTemplate["pred1( `parmlist` , |`parm`| is_integer(\"?`expr`\") && `expr` > (`y`).into())"][
    <| 
        "parmlist" -> (Variables[expr] // Map[StringTemplate["\"?``\""]] // ToString // StringTake[#, {2,-2}]&) ,
        "parm" -> (Variables[expr] // ToString // StringTake[#, {2,-2}]&) ,
        "expr" -> expr,
        "y" -> y
    |>];
pred[ILtQ[expr_, y_]] := StringTemplate["pred1( `parmlist` , |`parm`| is_integer(\"?`expr`\") && `expr` < (`y`).into())"][
    <| 
        "parmlist" -> (Variables[expr] // Map[StringTemplate["\"?``\""]] // ToString // StringTake[#, {2,-2}]&) ,
        "parm" -> (Variables[expr] // ToString // StringTake[#, {2,-2}]&) ,
        "expr" -> expr,
        "y" -> y
    |>];
pred[EqQ[expr_, y_]] := StringTemplate["pred`len`( `parmlist`  , |`parm`| `expr1` == (`y`).into())"][
    <| "len" -> Length[Variables[expr]],
        "parmlist" -> (Variables[expr] // Map[StringTemplate["\"?``\""]] // ToString // StringTake[#, {2,-2}]&) ,
        "parm" -> (Variables[expr] // ToString // StringTake[#, {2,-2}]&),
        "expr" -> ToString@CForm[expr],
        "y" -> y,
        "expr1" -> (InputForm[expr] // ToString)
    |>];
pred[PosQ[y_]] := pred[GtQ[y,0]];
pred[LeQ[expr_ ,y_]] := StringTemplate["pred`len`( `parmlist`  , |`parm`| `expr1` <= (`y`).into())"][
    <| "len" -> Length[Variables[expr]],
        "parmlist" -> (Variables[expr] // Map[StringTemplate["\"?``\""]] // ToString // StringTake[#, {2,-2}]&) ,
        "parm" -> (Variables[expr] // ToString // StringTake[#, {2,-2}]&),
        "expr" -> ToString@CForm[expr],
        "y" -> y,
        "expr1" -> (InputForm[expr] // ToString)
    |>];
pred[GeQ[expr_,y_]] := StringTemplate["pred`len`( `parmlist`  , |`parm`| `expr1` >= (`y`).into())"][
    <| "len" -> Length[Variables[expr]],
        "parmlist" -> (Variables[expr] // Map[StringTemplate["\"?``\""]] // ToString // StringTake[#, {2,-2}]&) ,
        "parm" -> (Variables[expr] // ToString // StringTake[#, {2,-2}]&),
        "expr" -> ToString@CForm[expr],
        "y" -> y,
        "expr1" -> (InputForm[expr] // ToString)
    |>];
pred[NegQ[expr_]] := pred[LtQ[expr, 0]];
pred[FractionQ[x_]] := StringTemplate["is_fractionq(`x`)"][
    <| "x" -> x
    |>
    ];
pred[IntegersQ[m_]] := {m} // Map[StringTemplate["is_integer(\"?``\")"]] // StringRiffle[#, " && "]& // StringTemplate["(``)"];
pred[IntegersQ[m_, n_]] := {m,n} // Map[StringTemplate["is_integer(\"?``\")"]] // StringRiffle[#, " && "]& // StringTemplate["(``)"];
       
pred[IntegersQ[p_, q_, r_]] := {p,q,r} // Map[StringTemplate["is_integer(\"?``\")"]] // StringRiffle[#, " && "]& // StringTemplate["(``)"];

pred[freeq[arr_List, x_]] := StringTemplate["freeq(&[ `parmlist` ], \"?`x`\")"][
    <| 
        "parmlist" -> (arr // Map[StringTemplate["\"?``\""]] // ToString // StringTake[#, {2,-2}]&) ,
        "x" -> x
    |>];
pred[freeq[expr_, x_]] := StringTemplate["freeq(&[ `parmlist` ], \"?`x`\")"][
    <| 
        "parmlist" -> ({expr} // Map[StringTemplate["\"?``\""]] // ToString // StringTake[#, {2,-2}]&) ,
        "x" -> x
    |>];
pred[integerQ[p_]] := StringTemplate["is_interger(\"?`p`\")"][<|"p" -> p|>]
pred[x_] := If[ StringTrim[ToString[x]] != "" , StringTemplate["not support `x` yet"][<|"x" -> ToString[x]|>]];


line[{id_, left_, right_}] := Print[StringTemplate["rw!( \"`1`\" ; \"`2`\" => \"`3`\" ),"][id, f[left], f[right]]];
line[{id_, left_, right_, cond_}] :=
    Print[StringTemplate["rw!( \"`id`\" ; \"`left`\" => \"`right`\" if `cond`),"][
        <|
            "id" -> id, 
            "left" -> f[left],
            "right" ->f[right], 
            "cond" -> pred[cond]
        |>
        ]];
Print["vec!["];
If[True,
    ReadString["./rules.wls"]//
    StringSplit[#, "\n"]&//
    Map[ToExpression] //
    Map[line]
]
Print["]"]
