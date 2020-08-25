(* ::Package:: *)

BeginPackage["CommutativeAlgebra`"]

Begin["`Graded`"]

silent=False;

DefineFiltration[commalg_,gradedflag_]:=(
	commalg["ZeroDeg"]=If[NumberQ[commalg["Deg"][commalg["generators"][[1]]]],
		0
	,
		Map[0&,commalg["Deg"][commalg["generators"][[1]]]]
	];
	commalg["Deg"][x_?(NumberQ)]:=commalg["ZeroDeg"];
	commalg["Deg"][x_Plus]:=Module[
		{xtab=x,ans}
	,
		xtab[[0]]=List;
		ans=DeleteDuplicates[Map[commalg["Deg"],xtab]];
		If[gradedflag&&(Length[ans]!=1),
			If[!silent,Print["Polynomial is not homogeneous ",x]];
			Return[Indeterminate];
		];
		ans=Sort[ans,Greater];
		Return[ans[[1]]];
	];
	commalg["Deg"][x_Times]:=Module[
		{xtab=x}
	,
		xtab[[0]]=List;
		Return[Plus@@Map[commalg["Deg"],xtab]];
	];
	commalg["Deg"][x_Power]:=x[[2]]commalg["Deg"][x[[1]]];
);

DefineFiltration[commalg_]:=DefineFiltration[commalg,False];

DefineGrading[commalg_]:=(
	DefineFiltration[commalg,True];
	commalg["GetHomogeneous"][poly_]:=Module[
		{expr=Expand[poly],tab,ans={},degtab={},pos,HandleTerm}
	,
		HandleTerm[monomial_]:=(
			pos=Position[degtab,commalg["Deg"][monomial]];
			Switch[Length[pos],
			0,
				AppendTo[ans,monomial];
				AppendTo[degtab,commalg["Deg"][monomial]],
			1,
				ans[[pos[[1,1]]]]+=monomial,
			_,
				Print["Unexpected Position List in GetHomogeneous, pos=",pos];
				Return[Indeterminate];
			];
		);
		Switch[expr,
		_Plus,
			expr[[0]]=List;
			Map[HandleTerm,expr];
			Return[ans],
		_, 
			Return[{expr}]
		];
	];
);

PosQ[xtab_]:=And@@Map[#>=0&,xtab]; (*Auxiliary function for StrictGradedBasis and StrictFilteredSpan*)

(*Defining graded basis for finitenly generated commutative algebra with generators of strictly positive degree*)
DefineStrictGradedSpan[commalg_,SimplifyF_]:=Module[
	{i,j}
,
	(*Defining basis recursively*)
	commalg["gspan"][deg_List]:=commalg["gspan"][deg]=Module[
		{ans={},k,lbasis}
	,
		If[DeleteCases[deg,0]=={},Return[{1}]];
		If[DeleteDuplicates[Map[NumberQ,deg]]=!={True},
			Print["Unexpected input in graded basis ",deg];
			Return[Indeterminate];
		];
		If[!PosQ[deg],Return[{}]];
		For[k=1,k<=Length[commalg["generators"]],k++,
			lbasis=commalg["gspan"][deg-commalg["Deg"][commalg["generators"][[k]]]];
			ans=Join[ans,Map[# commalg["generators"][[k]]&,lbasis]];
		];
		Return[DeleteDuplicates[SimplifyF[ans]]];
	];
];

DefineStrictGradedSpan[commalg_]:=DefineStrictGradedSpan[commalg,Factor];

(*Defining filtered span for finitenly generated commutative algebra with generators of strictly positive degree*)
DefineStrictFilteredSpan[commalg_,SimplifyF_]:=Module[
	{i,j}
,
	(*Defining basis recursively*)
	commalg["fspan"][deg_List]:=commalg["fspan"][deg]=Module[
		{ans={},k,lbasis,deglower}
	,
		If[DeleteCases[deg,0]=={},Return[{1}]];
		If[DeleteDuplicates[Map[NumberQ,deg]]=!={True},
			Print["Unexpected input in filtered span ",deg];
			Return[Indeterminate];
		];
		If[!PosQ[deg],Return[{}]];
		For[k=1,k<=Length[deg],k++,
			If[deg[[k]]>0,
				deglower=deg;
				deglower[[k]]--;
				ans=Join[ans,commalg["fspan"][deglower]];
			];
		];
		For[k=1,k<=Length[commalg["generators"]],k++,
			lbasis=commalg["fspan"][deg-commalg["Deg"][commalg["generators"][[k]]]];
			ans=Join[ans,Map[# commalg["generators"][[k]]&,lbasis]];
		];
		Return[DeleteDuplicates[SimplifyF[ans]]];
	];
];

DefineStrictFilteredSpan[commalg_]:=DefineStrictFilteredSpan[commalg,Factor];

End[]

Begin["`PolynomialAlgebra`"]

silent=False;
debug=False;
debugAll=False;

(*polynomialalg should be a graded free commutative algebra, \[Rho] is an injection to polynomial algebra*)
DefineStrictGradedAlgebra[commalg_,generators_,polynomialalg_,\[Rho]_]:=Module[
	{k,vars=polynomialalg["generators"]}
,
	ClearAll[commalg];
	commalg["generators"]=generators;
	commalg["GeneratorQ"][x_]:=Position[commalg["generators"],x,1]!={};
	commalg["\[Rho]"]=\[Rho];
	commalg["polynomialalg"]=polynomialalg;
	For[k=1,k<=Length[commalg["generators"]],k++,
		commalg["Deg"][commalg["generators"][[k]]]=polynomialalg["Deg"][\[Rho][commalg["generators"][[k]]]];
	];
	CommutativeAlgebra`Graded`DefineGrading[commalg];
	CommutativeAlgebra`Graded`DefineStrictGradedSpan[commalg];
	(*Defining coefficient rules for basis elements*)
	commalg["spanrules"][deg_]:=commalg["spanrules"][deg]=Module[
		{rulestab,maxpow=Table[1,Length[vars]],i,base,sparserules,j}
	,
		rulestab=Table[CoefficientRules[(Times@@vars)\[Rho][commalg["gspan"][deg][[i]]],vars],{i,1,Length[commalg["gspan"][deg]]}];
		For[i=1,i<=Length[rulestab],i++,
			For[j=1,j<=Length[rulestab[[i]]],j++,
				maxpow=Table[Max[maxpow[[k]],rulestab[[i,j,1,k]]],{k,1,Length[vars]}];
			];
		];
		commalg["baseNum"][deg]=maxpow;
		sparserules=Table[SparseArray[rulestab[[i]],maxpow],{i,1,Length[rulestab]}];
		Return[sparserules];
	];
	(*Defining decomposition of homogeneous monomials*)
	commalg["DecomposeHomogeneous"][poly0_]:=Module[
		{deg,spanrules,rules,diff,eqs,sol,poly,maxpow=Table[1,Length[vars]],j,ans,c}
	,
		poly=Factor[poly0];
		If[poly===0,Return[0]];
		deg=polynomialalg["Deg"][poly];
		(*Finding if there are any basis elements in such degree*)
		spanrules=commalg["spanrules"][deg];
		If[Length[spanrules]==0,
			If[!silent,Print["No elements in such degre, ",deg]];
			Return[Indeterminate];
		];
		(*Finding if maximum powers of generators in basis elements are large enough*)
		rules=CoefficientRules[(Times@@vars)poly,vars];
		For[j=1,j<=Length[rules],j++,
			maxpow=Table[Max[maxpow[[k]],rules[[j,1,k]]],{k,1,Length[vars]}];
		];
		If[Or@@Map[#>0&,maxpow-commalg["baseNum"][deg]],
			If[!silent,Print["No basis elements with appropriate powers of generators"]];
			Return[Indeterminate];
		];
		rules=SparseArray[rules,commalg["baseNum"][deg]];
		diff=ArrayRules[rules-Sum[Subscript[c, i]spanrules[[i]],{i,1,Length[spanrules]}]];
		eqs=DeleteDuplicates[Map[Factor[#[[2]]]==0&,diff]];
		sol=Solve[eqs,Table[Subscript[c, i],{i,1,Length[spanrules]}]];
		If[Length[sol]==0,
			If[!silent,Print["Failed to decompose ",poly]];
			If[debug,
				Print[commalg["gspan"][deg]];
				Print["sol=",sol,", eqs=",eqs];
			];
			Return[Indeterminate];
		];
		If[(Length[sol]>1)&&(!silent),
			Print["Multiple Solutions due to relations in algebra, returning a linear combination"];
		];
		ans=Sum[Subscript[c, i]commalg["gspan"][deg][[i]],{i,1,Length[commalg["gspan"][deg]]}]/.sol[[1]];
		If[debugAll,Print[ans]];
		ans=ans/.Table[Subscript[c, i]->0,{i,1,Length[commalg["gspan"][deg]]}];
		Return[commalg["CanonicalForm"][ans]];
	];
	commalg["DecomposePolynomial"][expr_]:=Module[
		{tab}
	,
		tab=polynomialalg["GetHomogeneous"][expr];
		tab=Map[commalg["DecomposeHomogeneous"],tab];
		Return[Plus@@tab];
	];
	commalg["DecomposeRational"][expr0_]:=Module[
		{num,den,expr}
	,
		expr=Factor[expr0];
		num=Numerator[expr];
		den=Denominator[expr];
		Return[Factor[commalg["DecomposePolynomial"][num]/commalg["DecomposePolynomial"][den]]];
	];
	(*Searching for relations*)
	commalg["GradedRelations"][deg_]:=commalg["GradedRelations"][deg]=Module[
		{span=commalg["gspan"][deg],c,diff,rules,eqs,sol}
	,
		If[Length[span]==0,Return[{}]];
		diff=Sum[Subscript[c, i] span[[i]],{i,1,Length[span]}];
		rules=CoefficientRules[commalg["\[Rho]"][diff],vars];
		eqs=Map[#[[2]]==0&,rules];
		Off[Solve::svars];
		sol=Solve[eqs,Table[Subscript[c, i],{i,1,Length[span]}]];
		On[Solve::svars];
		If[Length[sol]!=1,
			Print["Internal error in GradedRelations, sol=",sol,", span=",span];
			Return[Indeterminate];
		];
		diff=diff/.sol[[1]];
		Return[Map[#[[2]]&,CoefficientRules[diff,Table[Subscript[c, i],{i,1,Length[span]}]]]];
	];
	commalg["gbasis"][deg_]:=commalg["gbasis"][deg]=Module[
		{span=commalg["gspan"][deg],relations=commalg["GradedRelations"][deg],M,M1,ans={},i,j}
	,
		M=Orthogonalize[SparseArray[Table[Coefficient[relations[[i]],span[[j]]],{i,1,Length[relations]},{j,1,Length[span]}],{Length[relations],Length[span]}]];
		For[i=1,i<=Length[span],i++,
			M1=SparseArray[Join[M,{Table[KroneckerDelta[i,j],{j,1,Length[span]}]}]];
			M1=Orthogonalize[M1];
			If[Sum[Abs[M1[[-1,i]]],{i,1,Length[span]}]>0,
				AppendTo[ans,span[[i]]];
				M=M1;
			];
		];
		Return[ans];
	];
	commalg["CanonicalFormSubst"][deg_]:=(commalg["CanonicalFormSubst"][deg]=Module[
		{sol,c,ansatz,rules,eqs,span,basis,resolved,subst={},i,expr}
	,
		span=commalg["gspan"][deg];
		basis=commalg["gbasis"][deg];
		resolved=Complement[span,basis];
		For[i=1,i<=Length[resolved],i++,
			expr=resolved[[i]];
			deg=commalg["Deg"][expr];
			ansatz=Sum[Subscript[c, i]commalg["gbasis"][deg][[i]],{i,1,Length[commalg["gbasis"][deg]]}];
			rules=CoefficientRules[commalg["\[Rho]"][expr-ansatz],vars];
			eqs=Map[#[[2]]==0&,rules];
			sol=Solve[eqs];
			If[Length[sol]!=1,
				Print["Internal error in CanonicalFormSubst, sol=",sol,", expr=",expr,", rules=",rules];
				Return[Indeterminate];
			];
			AppendTo[subst,expr->(ansatz/.sol[[1]])];
		];
		Return[subst];
	];);
	commalg["CanonicalFormAux"][expr_]:=Expand[expr/.commalg["CanonicalFormSubst"][commalg["Deg"][expr]]];
	commalg["CanonicalForm"][expr_]:=Module[
		{tab}
	,
		tab=commalg["GetHomogeneous"][expr];
		tab=Map[commalg["CanonicalFormAux"],tab];
		Return[Plus@@tab];
	];
];

GetDimension[commalg_]:=Module[
	{jac,generators,vars,nsubst}
,
	generators=Map[commalg["\[Rho]"],commalg["generators"]];
	vars=commalg["polynomialalg"]["generators"];
	nsubst=Map[(#->RandomInteger[{100,1000}])&,vars];
	jac=Table[D[generators[[i]],vars[[j]]],{i,1,Length[generators]},{j,1,Length[vars]}];
	Return[MatrixRank[jac/.nsubst]];
];

DefineFilteredBasis[commalg_,generators_,polynomialalg_,\[Rho]_]:=Module[
	{k,vars=polynomialalg["generators"]}
,
	(*Defining coefficient rules for basis elements*)
	commalg["basisrules"][deg_]:=commalg["basisrules"][deg]=Module[
		{rulestab,maxpow=Table[1,Length[vars]],i,base,sparserules,j}
	,
		rulestab=Table[CoefficientRules[(Times@@vars)\[Rho][commalg["fspan"][deg][[i]]],vars],{i,1,Length[commalg["fspan"][deg]]}];
		For[i=1,i<=Length[rulestab],i++,
			For[j=1,j<=Length[rulestab[[i]]],j++,
				maxpow=Table[Max[maxpow[[k]],rulestab[[i,j,1,k]]],{k,1,Length[vars]}];
			];
		];
		commalg["baseNum"][deg]=maxpow;
		sparserules=Table[SparseArray[rulestab[[i]],maxpow],{i,1,Length[rulestab]}];
		Return[sparserules];
	];
	(*Defining decomposition of homogeneous monomials*)
	commalg["DecomposePolynomial"][poly0_]:=Module[
		{deg,basisrules,rules,c,diff,eqs,sol,poly,maxpow=Table[1,Length[vars]],j}
	,
		poly=Factor[poly0];
		If[poly===0,Return[0]];
		deg=polynomialalg["Deg"][poly];
		(*Finding if there are any basis elements in such degree*)
		basisrules=commalg["basisrules"][deg];
		If[Length[basisrules]==0,
			If[!silent,Print["No elements in such degre, ",deg]];
			Return[Indeterminate];
		];
		(*Finding if maximum powers of generators in basis elements are large enough*)
		rules=CoefficientRules[(Times@@vars)poly,vars];
		For[j=1,j<=Length[rules],j++,
			maxpow=Table[Max[maxpow[[k]],rules[[j,1,k]]],{k,1,Length[vars]}];
		];
		If[Or@@Map[#>0&,maxpow-commalg["baseNum"][deg]],
			If[!silent,Print["No basis elements with appropriate powers of generators"]];
			Return[Indeterminate];
		];
		rules=SparseArray[rules,commalg["baseNum"][deg]];
		diff=ArrayRules[rules-Sum[Subscript[c, i]basisrules[[i]],{i,1,Length[basisrules]}]];
		eqs=DeleteDuplicates[Map[Factor[#[[2]]]==0&,diff]];
		sol=Solve[eqs,Table[Subscript[c, i],{i,1,Length[basisrules]}]];
		If[Length[sol]==0,
			If[!silent,Print["Failed to decompose ",poly]];
			If[debug,
				Print[commalg["gspan"][deg]];
				Print["sol=",sol,", eqs=",eqs];
			];
			Return[Indeterminate];
		];
		If[(Length[sol]>1)&&(!silent),
			Print["Multiple Solutions due to relations in algebra, returning a linear combination"];
		];
		Return[(Sum[Subscript[c, i]commalg["gspan"][deg][[i]],{i,1,Length[commalg["gspan"][deg]]}]/.sol[[1]])/.Table[Subscript[c, i]->0,{i,1,Length[basisrules]}]];
	];
];

End[]

Begin["`FinitelyGenerated`"]

silent=False;

Define[commalg_]:=Module[
	{i}
,
	If[!ValueQ[commalg["generators"]],
		Print["Generators are not defined in ",commalg];
		Return[Indeterminate];
	];
	commalg["GeneratorQ"][expr_]:=(Or@@Map[MatchQ[expr,#]&,commalg["generators"]]);
	If[!ValueQ[commalg["relations"]],
		Print["Relations are not defined in ",commalg];
		Return[Indeterminate];
	];
	(*Default coefficient domain is rational functions in parameters*)
	If[!ValueQ[commalg["coefficientdomain"]],
		commalg["coefficientdomain"]=RationalFunctions;
	];
	(*Default weights used for monomial ordering is 1*)
	For[i=1,i<=Length[commalg["generators"]],i++,
		With[
			{x=commalg["generators"][[i]]}
		,
			If[!ValueQ[commalg["Deg"][x]],
				commalg["Deg"][x]=1;
			];
		];
	];
	(*Default monomial ordering is weighted degree reverse lexicographic*)
	If[!ValueQ[commalg["monomialorder"]],
		commalg["monomialorder"]=Prepend[Table[-KroneckerDelta[i,j],{i,1,Length[commalg["generators"]]-1},{j,1,Length[commalg["generators"]]}],Map[commalg["Deg"],commalg["generators"]]]
	];
	commalg["Weight"][monomial_]:=Module[
		{rules}
	,
		rules=CoefficientRules[monomial,commalg["generators"]];
		If[Length[rules]>1,
			Print["Incorrect input in ",commalg["Weight"],", rules=",rules];
			Return[Indeterminate];
		];
		Return[commalg["monomialorder"].rules[[1,1]]];
	];
	commalg["WeightLessQ"][monomial1_,monomial2_]:=Module[
		{wt1,wt2,j}
	,
		wt1=commalg["Weight"][monomial1];
		wt2=commalg["Weight"][monomial2];
		For[j=1,j<=Length[wt1],j++,
			If[wt1[[j]]<wt2[[j]],Return[True]];
			If[wt1[[j]]>wt2[[j]],Return[False]];
		];
		Return[False];
	];
	(*Defining Groebner Basis and Canonical Form*)
	If[!ValueQ[commalg["gb"]],
		commalg["gb"]:=(
			If[!silent,PrintTemporary["Computing Groebner Basis in ",commalg]];
			commalg["gb"]=GroebnerBasis[commalg["relations"],commalg["generators"],MonomialOrder->commalg["monomialorder"],CoefficientDomain->commalg["coefficientdomain"]];
			If[!silent,Print["Length of Groebner Basis in ",commalg," is ",Length[commalg["gb"]]]];
			commalg["gb"]
		);
	];
	commalg["CanonicalForm"][expr_]:=Collect[PolynomialReduce[expr,commalg["gb"],commalg["generators"],MonomialOrder->commalg["monomialorder"],CoefficientDomain->commalg["coefficientdomain"]][[2]],commalg["generators"],Factor];
	(*Defining Filtration*)
	CommutativeAlgebra`Graded`DefineFiltration[commalg];
	If[!Value[commalg["HomogeneousQ"][]],
		commalg["HomogeneousQ"]=True;
		For[i=1,i<=Length[commalg["relations"]],i++,
			If[Length[DeleteDuplicates[Map[commalg["Deg"],MonomialList[commalg["relations"][[i]],commalg["generators"]]]]]>0,
				commalg["GradedQ"]=False;
				Break[];
			];
		];
	];
	(*Defining basis by degree of the highest term*)
	commalg["gbasis"][deg_]:={}/;deg<0;
	commalg["gbasis"][0]={1};
	commalg["gbasis"][deg_]:=commalg["gbasis"][deg]=Module[
		{ans1,ans2,ans}
	,
		ans1=Select[commalg["generators"],commalg["Deg"][#]==deg&];
		ans2=Table[commalg["generators"][[i]]commalg["gbasis"][deg-commalg["Deg"][commalg["generators"][[i]]]],{i,1,Length[commalg["generators"]]}];
		commalg["gb"];(*Evaluating Groebner basis on a single core before executing Parallel Table*)
		ans=DeleteCases[ParallelMap[commalg["CanonicalForm"],DeleteDuplicates[Flatten[{ans1,ans2}]]],_Plus];
		ans=DeleteDuplicates[Map[FromCoefficientRules[{CoefficientRules[#,commalg["generators"]][[1,1]]->1},commalg["generators"]]&,ans]];
		Return[Select[ans,commalg["Deg"][#]==deg&]];
	];
	commalg["fbasis"][deg_]:={}/;deg<0;
	commalg["fbasis"][deg_]:=commalg["fbasis"][deg]=DeleteDuplicates[Join[commalg["fbasis"][deg-1],commalg["gbasis"][deg]]];
	(*Define Subleading Monomials*)
	commalg["SortedPowers"][expr_]:=Module[
		{monomials}
	,
		monomials=MonomialList[expr,commalg["generators"],commalg["monomialorder"]];
		Return[Map[FromCoefficientRules[{CoefficientRules[#,commalg["generators"]][[1,1]]->1},commalg["generators"]]&,monomials]];
	];
	commalg["SubleadingMonomials"][monomial_]:=Select[commalg["fbasis"][commalg["Deg"][monomial]],commalg["WeightLessQ"][#,monomial]&];
];

TestHomomorphism[algebra1_,algebra2_,subst_]:=Module[
	{i,diff}
,
	For[i=1,i<=Length[algebra1["relations"]],i++,
		diff=algebra2["CanonicalForm"][algebra1["relations"][[i]]/.subst];
		(*Print[{i,diff,algebra1["relations"][[i]]/.subst}];*)
		If[diff=!=0,
			Print["Defining ideal of ",algebra1," is not mapped to defining ideal of ",algebra2,", i=",i];
			Return[False];
		];
	];
	Return[True];
];

End[]

Begin["`Mixed`"]

silent=False;

(*Deg[x]={{graded degrees},{filtered degrees}}*)
DefineMixedFiltration[commalg_]:=(
	(*Defining Mixed Grading/Filtration*)
	commalg["DegM"][x_?(NumberQ)]:=Map[0&,commalg["DegM"][commalg["generators"][[1]]]];
	commalg["DegM"][x_Plus]:=Module[
		{xtab=x,ans,gradinglist,filtrationlist,i}
	,
		xtab[[0]]=List;
		ans=Map[commalg["DegM"],xtab];
		(*Testing that polynomial is homogeneous*)
		{gradinglist,filtrationlist}=Transpose[ans];
		If[Length[DeleteDuplicates[gradinglist]]!=1,
			If[!silent,Print["Element ",x," is not homogeneous"]];
			Return[Indeterminate];
		];
		filtrationlist=Reverse[SortBy[filtrationlist,Total]];
		For[i=2,i<=Length[filtrationlist],i++,
			If[Or@@Map[#<0&,filtrationlist[[i]]-filtrationlist[[1]]],
				If[!silent,Print["Element ",x," has no highest filtration component"]];
				Return[Indeterminate];
			];
		];
		Return[{gradinglist[[1]],filtrationlist[[1]]}];
	];
	commalg["DegM"][x_Times]:=Module[
		{xtab=x}
	,
		xtab[[0]]=List;
		Return[Plus@@Map[commalg["Deg"],xtab]];
	];
	commalg["DegM"][x_Power]:=x[[2]]commalg["Deg"][x[[1]]];
	(*Defining Grading and homogeneous components*)
	commalg["Deg"][expr_]:=commalg["DegM"][expr][[1]];
	commalg["GetHomogeneous"][poly_]:=Module[
		{expr=Expand[poly],tab,ans={},degtab={},pos,HandleTerm}
	,
		HandleTerm[monomial_]:=(
			pos=Position[degtab,commalg["Deg"][monomial]];
			Switch[Length[pos],
			0,
				AppendTo[ans,monomial];
				AppendTo[degtab,commalg["Deg"][monomial]],
			1,
				ans[[pos[[1,1]]]]+=monomial,
			_,
				Print["Unexpected Position List in GetHomogeneous, pos=",pos];
				Return[Indeterminate];
			];
		);
		Switch[expr,
		_Plus,
			expr[[0]]=List;
			Map[HandleTerm,expr];
			Return[ans],
		_, 
			Return[{expr}]
		];
	];
);

(*Defining graded/filtered basis for finitenly generated commutative algebra with generators of strictly positive degree*)
DefineMixedSpan[commalg_,SimplifyF_]:=Module[
	{i,j}
,
	(*Defining basis recursively*)
	PosQ[xtab_]:=And@@Map[#>=0&,Flatten[xtab]];
	commalg["mixedspan"][deg_List]:=commalg["mixedspan"][deg]=Module[
		{ans={},k,lbasis,gdeg,fdeg}
	,
		If[DeleteCases[deg,0,2]=={{},{}},Return[{1}]];
		If[DeleteDuplicates[Map[NumberQ,Flatten[deg]]]=!={True},
			Print["Unexpected input in graded basis ",deg];
			Return[Indeterminate];
		];
		If[!PosQ[deg],Return[{}]];
		{gdeg,fdeg}=deg;
		(*Adding all elements of the same gdeg and lower fdeg*)
		For[k=1,k<=Length[fdeg],k++,
			ans=Join[ans,commalg["mixedspan"][{gdeg,fdeg-Table[KroneckerDelta[j,k],{j,1,Length[fdeg]}]}]];
		];
		(*Adding all elements of lower graded degreees*)
		For[k=1,k<=Length[commalg["generators"]],k++,
			lbasis=commalg["mixedspan"][deg-commalg["Deg"][commalg["generators"][[k]]]];
			ans=Join[ans,Map[# commalg["generators"][[k]]&,lbasis]];
		];
		Return[DeleteDuplicates[SimplifyF[ans]]];
	];
];

End[]

EndPackage[]



