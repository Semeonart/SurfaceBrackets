(* ::Package:: *)

BeginPackage["SurfaceBrackets`"]

Begin["`RibbonGraphs`"]
Inv:=Global`Inv;

(*General functions*)
DefineCategoryGenerators[cat_]:=Module[
	{edgeslist={},b,i,expr}
,
	cat["objects"]=Table[i,{i,1,Length[cat["boundaries"]]}];
	cat["ObjectQ"][b_]:=If[NumberQ[b],1<=b<=Length[cat["boundaries"]],False];
	For[b=1,b<=Length[cat["boundaries"]],b++,
		For[i=1,i<=Length[cat["boundaries"][[b]]],i++,
			Switch[expr=cat["boundaries"][[b,i]],
			_Inv,
				AppendTo[edgeslist,expr[[1]]];
				If[cat["ObjectQ"][cat["t"][expr[[1]]]],
					Print["Inconsistent data for the ribbon graph, multiple targets for edge ",expr[[1]]]
				,
					cat["t"][expr[[1]]]=b
				],
			_,
				AppendTo[edgeslist,expr];
				If[cat["ObjectQ"][cat["s"][expr]],
					Print["Inconsistent data for the ribbon graph, multiple sources for edge ",expr," ",{cat["s"][expr],b}]
				,
					cat["s"][expr]=b
				]
			];
		];
	];
	cat["groupoidgenerators"]=DeleteDuplicates[edgeslist];
	For[i=1,i<=Length[cat["generators"]],i++,
		If[!cat["ObjectQ"][cat["s"][cat["groupoidgenerators"][[i]]]],
			Print["Inconsistent data for the ribbon graph, source is not defined for edge ",cat["groupoidgenerators"][[i]]];
		];
		If[!cat["ObjectQ"][cat["t"][cat["groupoidgenerators"][[i]]]],
			Print["Inconsistent data for the ribbon graph, target is not defined for edge ",cat["groupoidgenerators"][[i]]];
		];
	];
];

(*Defining free category of polyvector fields*)
DefinePolyvectorFields[Dcat_,cat_,\[Delta]_,\[Gamma]_]:=Module[
	{i}
,
	cat["FreeDerivation"]=\[Delta];
	cat["Uniderivation"]=\[Gamma];
	AbstractAlgebra`FinitelyGenerated`DefineLinearGroupoidWithTensorProduct[cat];
	(*Defining Category of vector fields*)
	Dcat["vectorfields"]=Join[
		Map[Subscript[\[Delta], #]&,cat["groupoidgenerators"]]
	,
		Map[Subscript[\[Gamma], #]&,cat["objects"]]
	];
	cat["s"][Subscript[\[Delta], X_]]:=Dcat["t"][X];
	cat["t"][Subscript[\[Delta], X_]]:=Dcat["s"][X];
	Subscript[\[Delta], Inv[f_]]:=-cat["Composition"][f,Subscript[\[Delta], f],f];
	cat["s"][Subscript[\[Gamma], o_]]:=o;
	cat["t"][Subscript[\[Gamma], o_]]:=o;
	Dcat["s"]=cat["s"];
	Dcat["t"]=cat["t"];
	NonCommutativePoissonGeometry`PolyVectorFields`DefineCategoryOfPolyvectorFields[Dcat,cat];
	(*Defining VectorField Action*)
	Subscript[\[Delta], X_?(cat["GroupoidGeneratorQ"])][Y_?(cat["GroupoidGeneratorQ"])]:=If[X===Y,
		Subscript[cat["Id"], cat["s"][X]]\[CircleTimes]Subscript[cat["Id"], cat["t"][X]]
	,
		0
	];
	Subscript[\[Gamma], o_][x_?(cat["GeneratorQ"])]:=Piecewise[{
		{Subscript[cat["Id"], o]\[CircleTimes]x-x\[CircleTimes]Subscript[cat["Id"], o],cat["t"][x]===o&&cat["s"][x]===o}
	,
		{Subscript[cat["Id"], o]\[CircleTimes]x,cat["t"][x]=!=o&&cat["s"][x]===o}
	,
		{-x\[CircleTimes]Subscript[cat["Id"], o],cat["t"][x]===o&&cat["s"][x]=!=o}
	,
		{0,cat["t"][x]=!=o&&cat["s"][x]=!=o}
	}];
];

(*Contribution to the Double Poisson bivector, edges ordered counterclockwise*)
GetOrderedP[x_,\[Delta]_,cat_]:=1/2 Sum[cat["Composition"][x[[j]],Subscript[\[Delta], x[[i]]],x[[i]],Subscript[\[Delta], x[[j]]]]-cat["Composition"][x[[i]],Subscript[\[Delta], x[[j]]],x[[j]],Subscript[\[Delta], x[[i]]]],{j,2,Length[x]},{i,1,j-1}];

(*Define Double Quasi Poisson Bracket*)
DefineQuasiBracket[cat_]:=Module[
	{i,j,x,y,btab,btabx,btaby}
,
	cat["P"][i_]:=cat["P"][i]=GetOrderedP[cat["boundaries"][[i]],cat["FreeDerivation"],cat];
	cat["R"][i_]:=cat["R"][i]=cat["Dcat"]["Tr"][cat["P"][i]];
	cat["RF"][i_][expr_]:=(
		If[cat["P"][i]===0,
			Return[0]
		,
			Return[cat["R"][i][expr]];
		];
	);
	AbstractAlgebra`GroundField`SetMultiLinear[cat["DBracket"],cat["groundfield"]];
	NonCommutativePoissonGeometry`DoubleBrackets`DefineCategoricalBiderivation[cat["DBracket"],cat];
	For[i=1,i<=Length[cat["groupoidgenerators"]],i++,
		x=cat["groupoidgenerators"][[i]];
		For[j=1,j<=Length[cat["groupoidgenerators"]],j++,
			y=cat["groupoidgenerators"][[j]];
			btabx=DeleteDuplicates[{cat["s"][x],cat["t"][x]}];
			btaby=DeleteDuplicates[{cat["s"][y],cat["t"][y]}];
			btab=Intersection[btabx,btaby];
			cat["DBracket"][x\[CircleTimes]y]=Plus@@Map[cat["RF"][#][x\[CircleTimes]y]&,btab];
		];
	];
	cat["H0Bracket"][X_\[CircleTimes]Y_]:=cat["\[Mu]"][cat["DBracket"][X\[CircleTimes]Y]];
];

DefineQuasiPoissonCategory[cat_,\[Delta]_,\[Gamma]_]:=(
	DefineCategoryGenerators[cat];
	DefinePolyvectorFields[cat["Dcat"],cat,\[Delta],\[Gamma]];
	DefineQuasiBracket[cat];
);

End[]

EndPackage[]
