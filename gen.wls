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


line[{id_, left_, right_}] := Print[StringTemplate["rw!( \"`1`\"   ;   `2`   =>  `3` )"][id, ToString@CForm@ left, ToString@CForm@ right]];
line[{id_, left_, right_, cond_}] :=
    Print[StringTemplate["rw!( \"`id`\"  ;   `left`   =>  `right` if `cond`)"][
        <|
            "id" -> id, 
            "left" -> ToString@CForm@ left,
            "right" ->ToString@CForm@ right, 
            "cond" -> pred[cond]
        |>
        ]];
If[True,
    ReadString["./rules.wls"]//
    StringSplit[#, "\n"]&//
    Map[ToExpression] //
    Map[line]
]

