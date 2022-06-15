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
	cat["T"]:=cat["t"];
	cat["H"]:=cat["s"];
	For[b=1,b<=Length[cat["boundaries"]],b++,
		For[i=1,i<=Length[cat["boundaries"][[b]]],i++,
			Switch[expr=cat["boundaries"][[b,i]],
			_Inv,
				AppendTo[edgeslist,expr[[1]]];
				If[cat["ObjectQ"][cat["H"][expr[[1]]]],
					Print["Inconsistent data for the ribbon graph, multiple targets for edge ",expr[[1]]]
				,
					cat["H"][expr[[1]]]=b
				],
			_,
				AppendTo[edgeslist,expr];
				If[cat["ObjectQ"][cat["T"][expr]],
					Print["Inconsistent data for the ribbon graph, multiple sources for edge ",expr," ",{cat["T"][expr],b}]
				,
					cat["T"][expr]=b
				]
			];
		];
	];
	cat["groupoidgenerators"]=DeleteDuplicates[edgeslist];
	For[i=1,i<=Length[cat["generators"]],i++,
		If[!cat["ObjectQ"][cat["T"][cat["groupoidgenerators"][[i]]]],
			Print["Inconsistent data for the ribbon graph, source is not defined for edge ",cat["groupoidgenerators"][[i]]];
		];
		If[!cat["ObjectQ"][cat["H"][cat["groupoidgenerators"][[i]]]],
			Print["Inconsistent data for the ribbon graph, target is not defined for edge ",cat["groupoidgenerators"][[i]]];
		];
	];
];

(*Contribution to the Double Poisson bivector, edges ordered counterclockwise*)
GetOrderedP[x_,\[Delta]_,cat_]:=1/2 Sum[cat["Composition"][x[[i]],Subscript[\[Delta], x[[i]]],x[[j]],Subscript[\[Delta], x[[j]]]]-cat["Composition"][x[[j]],Subscript[\[Delta], x[[j]]],x[[i]],Subscript[\[Delta], x[[i]]]],{j,2,Length[x]},{i,1,j-1}];

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
			btabx=DeleteDuplicates[{cat["T"][x],cat["H"][x]}];
			btaby=DeleteDuplicates[{cat["T"][y],cat["H"][y]}];
			btab=Intersection[btabx,btaby];
			cat["DBracket"][x\[CircleTimes]y]=Plus@@Map[cat["RF"][#][x\[CircleTimes]y]&,btab];
		];
	];
	cat["H0Bracket"][X_\[CircleTimes]Y_]:=cat["\[Mu]"][cat["DBracket"][X\[CircleTimes]Y]];
];

DefineQuasiPoissonCategory[cat_]:=(
	DefineCategoryGenerators[cat];
	AbstractAlgebra`FinitelyGenerated`DefineLinearGroupoidWithTensorProduct[cat];
	NonCommutativePoissonGeometry`PolyVectorFields`DefineFreePolyvectorFields[cat["Dcat"],cat];
	DefineQuasiBracket[cat];
);

End[]

EndPackage[]
