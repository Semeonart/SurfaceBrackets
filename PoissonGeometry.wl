(* ::Package:: *)

BeginPackage["PoissonGeometry`"]

Begin["`FinitelyGenerated`"]

silent=False;

DefineBiderivation[algebra_,Bracket_]:=(
	(*Subscript[algebra["Der"], i_][x_]:=Subscript[algebra["Der"], i][x]=D[x,algebra["generators"][[i]]];*)
	Bracket[x_,y_]:=Sum[Bracket[algebra["generators"][[i]],algebra["generators"][[j]]] D[x,algebra["generators"][[i]]]D[y,algebra["generators"][[j]]]
	,
		{i,1,Length[algebra["generators"]]},{j,1,Length[algebra["generators"]]}]
	/;
		!(algebra["GeneratorQ"][x]&&algebra["GeneratorQ"][y]);
	Bracket[x_,x_]:=0;
	Bracket[x_,y_]:=-Bracket[y,x]/;Module[
		{pos1,pos2}
	,
		If[algebra["GeneratorQ"][x]&&algebra["GeneratorQ"][y],
			pos1=Position[algebra["generators"],x,1][[1,1]];
			pos2=Position[algebra["generators"],y,1][[1,1]];
			Return[pos1>pos2]
		,
			Return[False];
		];
	];
);

(*SymplecticLeafDimension works for polynomial algebras only, generators are assumed to be algebraically independent*)
SymplecticLeafDimension[algebra_]:=Module[
	{jacobi,subst}
,
	jacobi=Table[algebra["PoissonBracket"][algebra["generators"][[i]],algebra["generators"][[j]]],{i,1,Length[algebra["generators"]]},{j,1,Length[algebra["generators"]]}];
	Print[MatrixForm[jacobi]];
	subst=Map[#->RandomInteger[{0,1000000}]&,algebra["generators"]];
	Return[MatrixRank[jacobi/.subst]];
];

End[]

Begin["`TestBrackets`"]

TestBracket[algebra_,SimplifyF_]:=Module[
	{i=0,j=0,k=0,diff,JacobiLHS,Bracket:=algebra["PoissonBracket"]}
,
	PrintTemporary[Dynamic[{i,j,k}]];
	(*Testing skew symmetry*)
	For[i=1,i<=Length[algebra["generators"]],i++,
		For[j=1,j<=i,j++,
			diff=Bracket[algebra["generators"][[i]],algebra["generators"][[j]]]+Bracket[algebra["generators"][[j]],algebra["generators"][[i]]];
			diff=SimplifyF[diff];
			If[diff=!=0,
				If[!silent,Print["Skew symmetry fails at {",algebra["generators"][[i]],",",algebra["generators"][[j]],"}, diff=",diff]];
				Return[False];
			];
		];
	];
	(*Testing Jacobi identity*)
	JacobiLHS[P_,Q_,R_]:=Bracket[P,Bracket[Q,R]]-Bracket[Q,Bracket[P,R]]-Bracket[Bracket[P,Q],R];
	For[i=1,i<=Length[algebra["generators"]],i++,
		For[j=1,j<=Length[algebra["generators"]],j++,
			For[k=1,k<=Length[algebra["generators"]],k++,
				diff=SimplifyF[JacobiLHS[algebra["generators"][[i]],algebra["generators"][[j]],algebra["generators"][[k]]]];
				If[diff=!=0,
					If[!silent,Print["Jacobi identity fails at ",{algebra["generators"][[i]],algebra["generators"][[j]],algebra["generators"][[k]]},", diff=",diff]];
					Return[False];
				];
			];
		];
	];
	Return[True];
];

TestBracket[algebra_]:=TestBracket[algebra,algebra["CanonicalForm"]];

CasimirQ[expr_,algebra_,SimplifyF_]:=Module[
	{i,diff}
,
	For[i=1,i<=Length[algebra["generators"]],i++,
		diff=SimplifyF[algebra["PoissonBracket"][algebra["generators"][[i]],expr]];
		If[diff=!=0,
			If[!silent,Print["Elements ",algebra["generators"][[i]]," and ",expr," do not Poisson commute"]];
			Return[False];
		];
	];
	Return[True];
];

CasimirQ[expr_,algebra_]:=CasimirQ[expr,algebra,algebra["CanonicalForm"]];

End[]

Begin["`Homomorphisms`"]

silent=False;

TestPoissonHomomorphism[commalg1_,commalg2_,substhom_]:=Module[
	{i,j,diff}
,
	CommutativeAlgebra`FinitelyGenerated`TestHomomorphism[commalg1,commalg2,substhom];
	For[j=2,j<=Length[commalg1["generators"]],i++,
		For[i=1,i<j,i++,
			diff=commalg2["CanonicalForm"][(commalg1["PoissonBracket"][commalg1["generators"][[i]],commalg2["generators"][[j]]]/.substhom)-commalg2["PoissonBracket"][commalg1["generators"][[i]]/.substhom,commalg2["generators"][[j]]/.substhom]];
			If[diff=!=0,
				If[!silent,Print["Poisson homomorphism fails at generators #=",{i,j}]];
				Return[False];
			];
		];
	];
	Return[True];
];

(*Trying to solve for the image of the generator*)
GetRel[gen1_,gen2_,commalg1_,commalg2_,substhom_,SimplifyF_]:=Module[
	{diff,vars,pos,ctab}
,
	diff=SimplifyF[(commalg1["PoissonBracket"][gen1,gen2]/.substhom)-commalg2["PoissonBracket"][gen1/.substhom,gen2/.substhom]];
	vars=Select[Variables[diff],commalg1["GeneratorQ"]];
	If[Length[vars]==1,
		pos=Position[diff,vars[[1]]];
		If[Length[pos]==1,
			ctab=CoefficientList[diff,vars[[1]]];
			If[Length[ctab]==2,
				Return[{vars[[1]]->-ctab[[1]]/ctab[[2]]}];
			];
		];
	];
	Return[{}];
];

GetRel[gen1_,gen2_,commalg1_,commalg2_,substhom_]:=GetRel[gen1,gen2,commalg1,commalg2,substhom,commalg2["CanonicalForm"]];

(*Trying to complete the substitution for Poisson homomorphism using elementary necessary requirements*)
ExtendHomomorphism[commalg1_,commalg2_,subst0_,SimplifyF_]:=Module[
	{i,j,ans}
,
	ans=subst0;
	For[j=2,j<=Length[commalg1["generators"]],j++,
		For[i=1,i<j,i++,
			ans=Join[ans,GetRel[commalg1["generators"][[i]],commalg1["generators"][[j]],commalg1,commalg2,ans,SimplifyF]];
			If[Length[ans]==Length[commalg1["generators"]],Break[]];
		];
	];
	Return[ans];
];

ExtendHomomorphism[commalg1_,commalg2_,subst0_]:=ExtendHomomorphism[commalg1,commalg2,subst0,commalg2["CanonicalForm"]];

End[]

Begin["`Constraints`"]

debugAll=True;

GetDiracBracket[algebra_,\[Phi]tab_]:=Module[
	{M,IM,DiracBracket,i,j}
,
	M=Table[Factor[algebra["PoissonBracket"][\[Phi]tab[[i]],\[Phi]tab[[j]]]],{i,1,Length[\[Phi]tab]},{j,1,Length[\[Phi]tab]}];
	If[debugAll,Print["M = ",MatrixForm[M]]];
	If[MatrixRank[M]!=Length[M],
		Print["Degenerate matrix of constraint brackets, Rank = ", MatrixRank[M]];
		Return[Indeterminate];
	];
	IM=Factor[Inverse[M]];
	(*Defining Dirac bracket*)
	PoissonGeometry`FinitelyGenerated`DefineBiderivation[algebra,DiracBracket];
	For[i=1,i<=Length[algebra["generators"]],i++,
		For[j=1,j<=Length[algebra["generators"]],j++,
			With[{
				f=algebra["generators"][[i]],
				g=algebra["generators"][[j]],
				Bracket=algebra["PoissonBracket"]
			},
				DiracBracket[f,g]=Factor[Bracket[f,g]-Sum[Bracket[f,\[Phi]tab[[k]]]IM[[k,l]]Bracket[\[Phi]tab[[l]],g],{k,1,Length[M]},{l,1,Length[M]}]];
			];
		];
	];
	Return[DiracBracket];
];

End[]

Begin["`RMatrix`"]

Id[n_]:=Id[n]=SparseArray[IdentityMatrix[n]];

(*Puts matrices A and B in i'th and j'th position in Mat(n)^\[CircleTimes]k*)
TensorPair[A_,B_,i_,j_,n_,k_]:=Module[
	{tab=Table[Id[n],k]}
,
	tab[[i]]=A;
	tab[[j]]=B;
	Return[TensorProduct@@tab];
];

(*Linear Lie Algebras Data*)
Rk:=LieAlgebras`Linear`Rk
Dim:=LieAlgebras`Linear`Dim;
\[CapitalNu][Subscript[X_, n_]]:=LieAlgebras`Linear`\[CapitalNu][Subscript[X, n]];
RootNum[Subscript[X_, n_]]:=Length[LieAlgebras`Linear`PositiveRootBasis[Subscript[X, n]]];
\[CapitalEpsilon]pos[Subscript[X_, n_]]:=LieAlgebras`Linear`PositiveRootBasis[Subscript[X, n]];
\[CapitalEpsilon]neg[Subscript[X_, n_]]:=LieAlgebras`Linear`DualPositiveRootBasis[Subscript[X, n]];
H[Subscript[X_, n_]]:=LieAlgebras`Linear`CartanOrthonormalBasis[Subscript[X, n]];
e[Subscript[X_, n_]]:=LieAlgebras`Linear`OrthonormalBasis[Subscript[X, n]];

(*Standard R-matrix*)
ClearAll[StandardRTensor,StandardRMatrix,r]

StandardRTensor[Subscript[X_, n_],a_,b_,k_]:=StandardRTensor[Subscript[X, n],a,b,k]=Sum[TensorPair[\[CapitalEpsilon]neg[Subscript[X, n]][[\[Alpha]]],\[CapitalEpsilon]pos[Subscript[X, n]][[\[Alpha]]],a,b,\[CapitalNu][Subscript[X, n]],k],{\[Alpha],1,RootNum[Subscript[X, n]]}]+1/2 Sum[TensorPair[H[Subscript[X, n]][[i]],H[Subscript[X, n]][[i]],a,b,\[CapitalNu][Subscript[X, n]],k],{i,1,Rk[Subscript[X, n]]}];
StandardRTensor[Subscript[X_, n_]]:=StandardRTensor[Subscript[X, n],1,2,2];

StandardRMatrix[Subscript[X_, n_],a_,b_,k_]:=StandardRMatrix[Subscript[X, n],a,b,k]=Flatten[StandardRTensor[Subscript[X, n],a,b,k],{Table[i,{i,1,2k,2}],Table[i,{i,2,2k,2}]}];
StandardRMatrix[Subscript[X_, n_]]:=StandardRMatrix[Subscript[X, n],1,2,2];

r[Subscript[X_, n_],i_,j_]:=r[Subscript[X, n],i,j]=Tr[Flatten[TensorProduct[e[Subscript[X, n]][[i]],e[Subscript[X, n]][[j]]],{{1,3},{2,4}}].StandardRMatrix[Subscript[X, n]]];

End[]

EndPackage[]
