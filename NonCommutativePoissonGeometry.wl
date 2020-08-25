(* ::Package:: *)

BeginPackage["NonCommutativePoissonGeometry`"]

Begin["`DoubleBrackets`"]

Inv:=Global`Inv;

DefineRMatrixDerivation[R_]:=(
	R[(a_**b__)\[CircleTimes]c_]:=(1\[CircleTimes]a)**R[NonCommutativeMultiply[b]\[CircleTimes]c]+R[a\[CircleTimes]c]**(NonCommutativeMultiply[b]\[CircleTimes]1);
	R[a_\[CircleTimes](b_**c__)]:=(b\[CircleTimes]1)**R[a\[CircleTimes]NonCommutativeMultiply[c]]+R[a\[CircleTimes]b]**(1\[CircleTimes]NonCommutativeMultiply[c]);
	R[Inv[a_]\[CircleTimes]b_]:=-(1\[CircleTimes]Inv[a])**R[a\[CircleTimes]b]**(Inv[a]\[CircleTimes]1);
	R[a_\[CircleTimes]Inv[b_]]:=-(Inv[b]\[CircleTimes]1)**R[a\[CircleTimes]b]**(1\[CircleTimes]Inv[b]);
	R[1\[CircleTimes]a_]:=0;
	R[a_\[CircleTimes]1]:=0;
);

DefineCategoricalBiderivation[R_,cat_]:=Module[
	{i}
,
	(*Defining basic properties*)
	AbstractAlgebra`GroundField`SetMultiLinear[R,cat["groundfield"]];
	For[i=1,i<=Length[cat["idmorphisms"]],i++,
		With[{e=cat["idmorphisms"][[i]]},
			R[e\[CircleTimes]x_]:=0;
			R[x_\[CircleTimes]e]:=0;
		];
	];
	(*Defining double Leibnitz identity*)
	With[{CompositionF=cat["Composition"]}
	,
		R[CompositionF[a_,b__]\[CircleTimes]c_]:=CompositionF[(Subscript[cat["Id"], cat["t"][c]]\[CircleTimes]a),R[CompositionF[b]\[CircleTimes]c]]+CompositionF[R[a\[CircleTimes]c],(CompositionF[b]\[CircleTimes]Subscript[cat["Id"], cat["s"][c]])];
		R[a_\[CircleTimes]CompositionF[b_,c__]]:=CompositionF[(b\[CircleTimes]Subscript[cat["Id"], cat["t"][a]]),R[a\[CircleTimes]CompositionF[c]]]+CompositionF[R[a\[CircleTimes]b],(Subscript[cat["Id"], cat["s"][a]]\[CircleTimes]CompositionF[c])];
		R[Inv[a_]\[CircleTimes]b_]:=-CompositionF[Subscript[cat["Id"], cat["t"][b]]\[CircleTimes]Inv[a],R[a\[CircleTimes]b],Inv[a]\[CircleTimes]Subscript[cat["Id"], cat["s"][b]]];
		R[a_\[CircleTimes]Inv[b_]]:=-CompositionF[Inv[b]\[CircleTimes]Subscript[cat["Id"], cat["t"][a]],R[a\[CircleTimes]b],Subscript[cat["Id"], cat["s"][a]]\[CircleTimes]Inv[b]];
	];
];

DefineCategoricalBiderivationTopConvention[R_,cat_]:=Module[
	{i}
,
	(*Defining basic properties*)
	AbstractAlgebra`GroundField`SetMultiLinear[R,cat["groundfield"]];
	For[i=1,i<=Length[cat["idmorphisms"]],i++,
		With[{e=cat["idmorphisms"][[i]]},
			R[e\[CircleTimes]x_]:=0;
			R[x_\[CircleTimes]e]:=0;
		];
	];
	(*Defining double Leibnitz identity*)
	With[{CompositionF=cat["Composition"]}
	,
		R[CompositionF[a_,b__]\[CircleTimes]c_]:=CompositionF[(Subscript[cat["Id"], cat["s"][c]]\[CircleTimes]a),R[CompositionF[b]\[CircleTimes]c]]+CompositionF[R[a\[CircleTimes]c],(CompositionF[b]\[CircleTimes]Subscript[cat["Id"], cat["t"][c]])];
		R[a_\[CircleTimes]CompositionF[b_,c__]]:=CompositionF[(b\[CircleTimes]Subscript[cat["Id"], cat["s"][a]]),R[a\[CircleTimes]CompositionF[c]]]+CompositionF[R[a\[CircleTimes]b],(Subscript[cat["Id"], cat["t"][a]]\[CircleTimes]CompositionF[c])];
		R[Inv[a_]\[CircleTimes]b_]:=-CompositionF[Subscript[cat["Id"], cat["s"][b]]\[CircleTimes]Inv[a],R[a\[CircleTimes]b],Inv[a]\[CircleTimes]Subscript[cat["Id"], cat["t"][b]]];
		R[a_\[CircleTimes]Inv[b_]]:=-CompositionF[Inv[b]\[CircleTimes]Subscript[cat["Id"], cat["s"][a]],R[a\[CircleTimes]b],Subscript[cat["Id"], cat["t"][a]]\[CircleTimes]Inv[b]];
	];
];

DefineGradedCategoricalBiderivation[R_,cat_]:=Module[
	{i}
,
	With[
		{NonCommutativeMultiply=cat["Composition"],CircleTimes=cat["CircleTimes"]}
	,
		(*Defining basic properties*)
		AbstractAlgebra`GroundField`SetMultiLinear[R,cat["groundfield"]];
		For[i=1,i<=Length[cat["idmorphisms"]],i++,
			With[{e=cat["idmorphisms"][[i]]},
				R[e\[CircleTimes]x_]:=0;
				R[x_\[CircleTimes]e]:=0;
			];
		];
		(*Defining double Leibnitz identity*)
		R[a_?(cat["ElementaryMorphismQ"][#]&)\[CircleTimes]NonCommutativeMultiply[b_?(cat["ElementaryMorphismQ"][#]&),c__]]:=(-1)^((cat["Deg"][a]+cat["Deg"][R])(cat["Deg"][b])) (b\[CircleTimes]Subscript[cat["Id"], cat["t"][a]])**R[a\[CircleTimes]NonCommutativeMultiply[c]]+R[a\[CircleTimes]b]**(Subscript[cat["Id"], cat["s"][a]]\[CircleTimes]NonCommutativeMultiply[c]);
		R[NonCommutativeMultiply[a__,b_?(cat["ElementaryMorphismQ"][#]&)]\[CircleTimes]c_?(cat["ElementaryMorphismQ"][#]&)]:=-(-1)^((cat["Deg"][a**b]+cat["Deg"][R])(cat["Deg"][c]+cat["Deg"][R]))\!\(\*SubscriptBox[\(cat["\<Graded\[CapitalSigma]\>"]\), \({2, 1}\)]\)[R[c\[CircleTimes]a**b]];
		R[a_?(cat["ElementaryMorphismQ"][#]&)\[CircleTimes]Inv[b_?(cat["ElementaryMorphismQ"])]]:=-(-1)^((cat["Deg"][a]+cat["Deg"][R])(cat["Deg"][b]))(Inv[b]\[CircleTimes]Subscript[cat["Id"], cat["t"][a]])**R[a\[CircleTimes]b]**(Subscript[cat["Id"], cat["s"][a]]\[CircleTimes]Inv[b]);
		R[Inv[b_?(cat["ElementaryMorphismQ"])]\[CircleTimes]a_?(cat["ElementaryMorphismQ"])]:=-(-1)^((cat["Deg"][a]+cat["Deg"][R])(cat["Deg"][b]+cat["Deg"][R]))\!\(\*SubscriptBox[\(cat["\<Graded\[CapitalSigma]\>"]\), \({2, 1}\)]\)[R[a\[CircleTimes]Inv[b]]];
	];
];

DefineGradedPermutation[cat_,s_]:=(
	Subscript[cat["Graded\[CapitalSigma]"],n_,\[Sigma]_]:=Subscript[cat["Graded\[CapitalSigma]"],n,\[Sigma]]=Module[
		{\[Sigma]Aux}
	,
		If[n==0,
			\[Sigma]Aux:=Subscript[s,\[Sigma]]
		,
			\[Sigma]Aux:=Subscript[s,n,\[Sigma]]
		];
		AbstractAlgebra`GroundField`SetMultiLinear[\[Sigma]Aux,cat["groundfield"]];
		\[Sigma]Aux[x_CircleTimes]:=Module[
			{xtab=x,i,j,sign=1}
		,
			xtab[[0]]=List;
			For[i=1,i<Length[xtab],i++,
				For[j=i+1,j<=Length[xtab],j++,
					If[\[Sigma][[i]]>\[Sigma][[j]],
						sign=sign (-1)^((cat["Deg"][xtab[[i]]]+n)(cat["Deg"][xtab[[j]]]+n));
					];
				];
			];
			xtab=Permute[xtab,\[Sigma]];
			Return[sign CircleTimes@@xtab];
		]/;cat["TensorMonomialQ"][x];
		Return[\[Sigma]Aux];
	];
	Subscript[cat["Graded\[CapitalSigma]"],\[Sigma]_]:=Subscript[cat["Graded\[CapitalSigma]"],0,\[Sigma]];
);

DefineGradedPermutation[cat_]:=DefineGradedPermutation[cat,Global`\[Sigma]];

End[]

Begin["`PolyVectorFields`"]

DefineVectorFieldsAction[vectorfields_,cat_,s_,t_]:=Module[
	{i}
,
	For[i=1,i<=Length[vectorfields],i++,
		With[{Inv=Global`Inv,Composition=cat["Composition"],\[Delta]=vectorfields[[i]]}
		,
			AbstractAlgebra`GroundField`SetMultilinear[\[Delta],cat["groundfield"]];
			\[Delta][Subscript[cat["Id"], _]]:=0;
			\[Delta][Inv[x_]]:=-Composition[(Subscript[cat["Id"], t[\[Delta]]]\[CircleTimes]Inv[x]),\[Delta][x],(Inv[x]\[CircleTimes]Subscript[cat["Id"], s[\[Delta]]])];
			\[Delta][x_Composition]:=Module[
				{xtab=x,ans=0,j}
			,
				xtab[[0]]=List;
				For[j=1,j<=Length[xtab],j++,
					ans+=Composition[(Subscript[cat["Id"], t[\[Delta]]]\[CircleTimes]Composition@@Append[Take[xtab,j-1],Subscript[cat["Id"], cat["t"][xtab[[j]]]]]),\[Delta][xtab[[j]]],(Composition@@Prepend[Drop[xtab,j],Subscript[cat["Id"], cat["s"][xtab[[j]]]]]\[CircleTimes]Subscript[cat["Id"], s[xtab[[j]]]])];		
				];
				Return[ans];
			]/;cat["ElementaryMorphismQ"][x];
		];
	];
];

DefineSweedlerVectorFields[\[CapitalDelta]tab_,Dcat_,cat_]:=Module[
	{i}
,
	For[i=1,i<=Length[\[CapitalDelta]tab],i++,
		With[{\[CapitalDelta]=\[CapitalDelta]tab[[i]]},
			AppendTo[cat["generators"],Superscript[\[CapitalDelta],_][_]];
			\[CapitalDelta][x_?(cat["GeneratorQ"])]:=Superscript[\[CapitalDelta],1][x]\[CircleTimes]Superscript[\[CapitalDelta],2][x];
			With[{\[CapitalDelta]1=Superscript[\[CapitalDelta],1],\[CapitalDelta]2=Superscript[\[CapitalDelta],2]},
				cat["s"][\[CapitalDelta]1[x_]]:=cat["s"][x];
				cat["t"][\[CapitalDelta]1[x_]]:=Dcat["t"][\[CapitalDelta]];
				cat["s"][\[CapitalDelta]2[x_]]:=Dcat["s"][\[CapitalDelta]];
				cat["t"][\[CapitalDelta]2[x_]]:=Dcat["t"][x];
			];
		];
	];
];

DefineOuterComposition[cat_]:=With[
	{CircleTimes=cat["CircleTimes"]}
,
	(*Defining Outer Composition of Tensor Monomials in cat*)
	AbstractAlgebra`Associative`DefineAssociativeMultiplication[cat["OuterComposition"],cat["groundfield"]];
	cat["OuterComposition"][x_]:=x;
	cat["OuterComposition"][x_?(cat["TensorMonomialQ"]),y_?(cat["TensorMonomialQ"]),z___]:=Module[
		{xtab,ytab}
	,
		Switch[x,
		_CircleTimes,
			xtab=x;
			xtab[[0]]=List,
		_,
			xtab={x}
		];
		Switch[y,
		_CircleTimes,
			ytab=y;
			ytab[[0]]=List,
		_,
			ytab={y}
		];
		ytab[[1]]=cat["Composition"][xtab[[-1]],ytab[[1]]];
		Return[cat["OuterComposition"][CircleTimes@@Join[Drop[xtab,-1],ytab],z]];
	];
	(*Defining Outer Trace*)
	AbstractAlgebra`GroundField`SetMultiLinear[cat["OuterTr"],cat["groundfield"]];
	cat["OuterTr"][x_?(cat["TensorMonomialQ"])]:=Switch[x,
	_CircleTimes,Module[
		{xtab=x}
	,
		xtab[[0]]=List;
		xtab[[1]]=cat["Composition"][xtab[[-1]],xtab[[1]]];
		Return[CircleTimes@@Drop[xtab,-1]]
	],
	_,
		Print["Unexpected input in Outer Trace ",x];
		Return[Indeterminate]
	];
];

DefineCategoryOfPolyvectorFields[Dcat_,cat_]:=(
	If[!ValueQ[Dcat["Composition"]],Dcat["Composition"]=cat["Composition"]];
	If[!ValueQ[Dcat["CircleTimes"]],Dcat["CircleTimes"]=cat["CircleTimes"]];
	With[
		{Composition=cat["Composition"],CircleTimes=Dcat["CircleTimes"],OuterCompose=cat["OuterComposition"]}
	,
		Dcat["groundfield"]=cat["groundfield"];
		Dcat["objects"]=cat["objects"];
		Dcat["generators"]=Join[cat["generators"],Dcat["vectorfields"]];
		(*Dcat["s"][x_?(cat["ElementaryMorphismQ"][#]&)]:=cat["s"][x];
		Dcat["t"][x_?(cat["ElementaryMorphismQ"][#]&)]:=cat["t"][x];*)
		Dcat["Id"]=cat["Id"];
		Dcat["cat"]=cat;
		AbstractAlgebra`FinitelyGenerated`DefineTensorCategory[Dcat];
		(*Standard boolean functions*)
		Dcat["VectorFieldQ"][expr_]:=Or@@Map[MatchQ[expr,#]&,Dcat["vectorfields"]];
		(*Defining Grading*)
		Dcat["GradingMultF"]=Plus;
		Dcat["Deg"][x_?(cat["ElementaryMorphismQ"])]:=0;
		Dcat["Deg"][x_?(Dcat["VectorFieldQ"])]:=1;
		Dcat["GradedOperationQ"][x_]:=Switch[x,
		_Times,True,
		_Composition,True,
		_CircleTimes,True,
		_,False
		];
		Dcat["Deg"][Times]=0;
		Dcat["Deg"][Composition]=0;
		Dcat["Deg"][CircleTimes]=0;
		AbstractAlgebra`Graded`DefineGraded[Dcat];
		NonCommutativePoissonGeometry`DoubleBrackets`DefineGradedPermutation[Dcat,Dcat["Graded\[Sigma]"]];
		(*Defining Action of Polyvectorfields*)
		DefineVectorFieldsAction[Dcat["vectorfields"],cat,Dcat["s"],Dcat["t"]];
		DefineOuterComposition[cat];
		AbstractAlgebra`CompositionAlgebra`DefineVectorSpaceOfOperators[Dcat["groundfield"]];
		Composition[x_,y__][0]=0;
		Composition[x_,y__][z_Plus]:=Module[
			{ztab=z}
		,
			ztab[[0]]=List;
			Return[Plus@@Map[Composition[x,y][#]&,ztab]];
		];
		Composition[x_,y__][m_Times]:=Module[
			{comm,ncm}
		,
			{comm,ncm}=AbstractAlgebra`GroundField`FactorFieldOut[m,cat["groundfield"]];
			Return[comm Composition[x,y][ncm]];
		];
		Composition[x_?(cat["ElementaryMorphismQ"]),y__][z_?(cat["TensorMonomialQ"])]:=OuterCompose[x,Composition[y][z]];
		Composition[x__,y_?(cat["ElementaryMorphismQ"])][z_?(cat["TensorMonomialQ"])]:=OuterCompose[Composition[x][z],y];
		Composition[x_?(Dcat["VectorFieldQ"]),y__][z_?(cat["TensorMonomialQ"])]:=Module[
			{argtab}
		,
			Switch[z,
			_?(cat["ElementaryMorphismQ"]),argtab={cat},
			_CircleTimes,
				argtab=z;
				argtab[[0]]=List,
			_,
				Print["Unexpected Tensor Monomial is Composition[][] ",z];
				Return[Indeterminate]
			];
			Return[OuterCompose[x[argtab[[1]]],Composition[y][CircleTimes@@Drop[argtab,1]]]];
		];
		(*Defining Trace of a PolyVectorfield*)
		NonCommutativePoissonGeometry`CyclicSpace`DefineCanonicalFormGraded[Dcat];
		(*Defining Action of a Trace of a Polyvectorfield*)
		AbstractAlgebra`GroundField`SetMultilinear[Dcat["Tr"],Dcat["groundfield"]];
		Dcat["Tr"][x_][y_?(cat["TensorMonomialQ"])]:=cat["OuterTr"][x[y]];
	];
);

End[]

Begin["`CyclicSpace`"]

Inv:=Global`Inv;

HashF[expr_]:=Hash[expr,"CRC32"];
HashSum[tab_,i_]:=Sum[tab[[Mod[i+j,Length[tab]]+1]]2^(32(j)),{j,0,Length[tab]-1}];

DefineCanonicalForm[algebra_,NonCommutativeMultiply_]:=(
	AbstractAlgebra`GroundField`SetMultiLinear[algebra["Cyclic"],algebra["groundfield"]];
	algebra["Cyclic"][NonCommutativeMultiply[a_,b__,Inv[a_]]]:=algebra["Cyclic"][NonCommutativeMultiply[b]];
	algebra["Cyclic"][NonCommutativeMultiply[Inv[a_],b__,a_]]:=algebra["Cyclic"][NonCommutativeMultiply[b]];
	algebra["Cyclic"][1]=1;
	algebra["Cyclic"][x_?(algebra["IdentityMorphismQ"])]:=x;
	algebra["Cyclic"][x_Inv]:=x;
	algebra["Cyclic"][x_?(algebra["GeneratorQ"])]:=x;
	algebra["Cyclic"][x_NonCommutativeMultiply]:=Module[
		{xtab=x,ans,maxhashsum,offset,i}
	,
		xtab[[0]]=List;
		ans=xtab;
		xtab=Map[HashF,xtab];
		offset=0;
		maxhashsum=HashSum[xtab,0];
		For[i=1,i<Length[xtab],i++,
			If[HashSum[xtab,i]>maxhashsum,
				offset=i;
				maxhashsum=HashSum[xtab,i];
			];
		];
		Return[NonCommutativeMultiply@@Join[Drop[ans,offset],Take[ans,offset]]];
	];
);

DefineCanonicalForm[algebra_]:=DefineCanonicalForm[algebra,NonCommutativeMultiply];

DefineCanonicalFormGraded[cat_]:=(
	AbstractAlgebra`GroundField`SetMultiLinear[cat["Cyclic"],cat["groundfield"]];
	With[
		{Composition=cat["Composition"],Inv=Global`Inv}
	,
		cat["Cyclic"][Composition[a_,b_,Inv[a_]]]:=cat["Cyclic"][Composition[b]]/;Mod[cat["Deg"][a],2]==0;
		cat["Cyclic"][Composition[Inv[a_],b_,a_]]:=cat["Cyclic"][Composition[b]]/;Mod[cat["Deg"][a],2]==0;
		cat["Cyclic"][x_?cat["IdentityMorphismQ"]]:=x;
		cat["Cyclic"][Inv[x_]]:=Inv[x];
		cat["Cyclic"][x_?(cat["GeneratorQ"])]:=x;
		cat["Cyclic"][x_Composition]:=Module[
			{xtab=x,ans,maxhashsum,offset,i,A,B}
		,
			xtab[[0]]=List;
			ans=xtab;
			xtab=Map[HashF,xtab];
			offset=0;
			maxhashsum=HashSum[xtab,0];
			For[i=1,i<Length[xtab],i++,
				If[HashSum[xtab,i]>maxhashsum,
					offset=i;
					maxhashsum=HashSum[xtab,i];
				];
			];
			A=Composition@@Take[ans,offset];
			B=Composition@@Drop[ans,offset];
			Return[(-1)^(cat["Deg"][A]cat["Deg"][B]) Composition[B,A]];
		];
	];
);

End[]

Begin["`InducedBrackets`"]

DefineCatRepBracket[cat_,DBracket_,Rep_,polynomialalg_]:=Module[
	{Bracket,m,n,x,P,Q,i,j,k,l,Db,T,Ni,Nj,Nk,Nl}
,
	PoissonGeometry`FinitelyGenerated`DefineBiderivation[polynomialalg,Bracket];
	x:=cat["groupoidgenerators"];
	For[m=1,m<=Length[x],m++,
		For[n=1,n<=Length[x],n++,
			P=x[[m]];
			Q=x[[n]];
			Db=DBracket[P\[CircleTimes]Q];
			If[debugAll,Print["Bracket on Representation Scheme ",{P,Q,Db}]];
			T=Rep[Db];
			Ni=Length[Rep[P]];
			Nj=Length[Rep[P][[1]]];
			Nk=Length[Rep[Q]];
			Nl=Length[Rep[Q][[1]]];
			For[i=1,i<=Ni,i++,
				For[j=1,j<=Nj,j++,
					For[k=1,k<=Nk,k++,
						For[l=1,l<=Nl,l++,
							If[T===0,
								Bracket[Subscript[P, i,j],Subscript[Q, k,l]]=0
							,
								Bracket[Subscript[P, i,j],Subscript[Q, k,l]]=T[[k,j,i,l]]
							];
						];
					];
				];
			];
		];
	];
	Return[Bracket];
];

End[]

Begin["`TestDoubleBrackets`"]

silent=False;

TestSkewSymmetry[cat_]:=Module[
	{i,j,diff,a,b}
,
	PrintTemporary["Testing skew-symmetry ",Dynamic[{i,j}]];
	For[j=1,j<=Length[cat["generators"]],j++,
		b=cat["generators"][[j]];
		For[i=1,i<=j,i++,
			a=cat["generators"][[i]];
			diff=cat["DBracket"][cat["CircleTimes"][a,b]]+\!\(\*SubscriptBox[\(cat["\<\[CapitalSigma]\>"]\), \({2, 1}\)]\)[cat["DBracket"][cat["CircleTimes"][b,a]]];
			diff=AbstractAlgebra`General`NCCollect[diff,cat["groundfield"]];
			If[diff=!=0,
				If[!silent,Print["Skew symmetry fails at ",{a,b},", diff=",diff]];
				Return[False];
			];
		];
	];
	Return[True];
];

TestDoubleQuasiJacobi[cat_,\[Lambda]_]:=Module[
	{i,j,k,diff,\[Gamma]=cat["Uniderivation"],f,g,h,R}
,
	(*Defining R matrix*)
	For[i=1,i<=3,i++,
		For[j=1,j<=3,j++,
			If[i!=j,AbstractAlgebra`GroundField`SetMultiLinear[Subscript[R, i,j],cat["groundfield"]]];
		];
	];
	Subscript[R, i_,j_][x_?(cat["TensorMonomialQ"])]:=Module[
		{xtab=x,a,b,rules,m,expr}
	,
		xtab[[0]]=List;
		a=xtab[[i]];
		b=xtab[[j]];
		expr=Factor[cat["DBracket"][a\[CircleTimes]b]];
		If[expr==0,Return[0]];
		rules=AbstractAlgebra`General`Rules[expr,cat["groundfield"]];
		For[m=1,m<=Length[rules],m++,
			xtab[[i]]=rules[[m,1,1]];
			xtab[[j]]=rules[[m,1,2]];
			rules[[m,1]]=CircleTimes@@xtab;
		];
		Return[Sum[rules[[m,1]] rules[[m,2]],{m,1,Length[rules]}]];
	];
	PrintTemporary["Testing Quasi Jacobi Identity ",Dynamic[{i,j,k}]];
	(*Testing Quasi Yang-Baxter equation*)
	For[i=1,i<=Length[cat["generators"]],i++,
		f=cat["generators"][[i]];
		For[j=1,j<=Length[cat["generators"]],j++,
			g=cat["generators"][[j]];
			For[k=1,k<=Length[cat["generators"]],k++,
				h=cat["generators"][[k]];
				diff=Subscript[R, 1,2][Subscript[R, 2,3][f\[CircleTimes]g\[CircleTimes]h]]-Subscript[R, 2,3][Subscript[R, 1,3][f\[CircleTimes]g\[CircleTimes]h]]-Subscript[R, 1,3][Subscript[R, 1,2][f\[CircleTimes]g\[CircleTimes]h]]-\[Lambda] cat["Dcat"]["Tr"][Total[Map[cat["Dcat"]["Composition"][Subscript[\[Gamma], #],Subscript[\[Gamma], #],Subscript[\[Gamma], #]]&,cat["objects"]]]][f\[CircleTimes]g\[CircleTimes]h];
				diff=AbstractAlgebra`General`NCCollect[diff,cat["groundfield"]];
				If[diff=!=0,
					If[!silent,Print["Double Quasi Jacobi Identity fails at ",{f,g,h},", diff=",diff]];
					(*Return[False];*)
				];
			];
		];
	];
	Return[True];
];

TestDoubleQuasiBracket[cat_,\[Lambda]_]:=(
	If[!TestSkewSymmetry[cat],
		Return[False]
	,
		Return[TestDoubleQuasiJacobi[cat,\[Lambda]]]
	];
);

TestDoubleQuasiBracket[cat_]:=TestDoubleQuasiBracket[cat,1/4];

TestDoubleBracket[cat_]:=TestDoubleQuasiBracket[cat,0];

End[]

Begin["`TestBrackets`"]

silent=False;
debug=False;
debugAll=False;
appsmode=False;

CheckLeftLodayJacobi[P_,Q_,R_,Bracket_,SimplifyF_]:=Module[
	{ans}
,
	ans=SimplifyF[Bracket[P,Bracket[Q,R]]-Bracket[Q,Bracket[P,R]]-Bracket[Bracket[P,Q],R]];
	If[ans=!=0,
		If[!silent,Print["Loday Jacobi identity fails at ",{P,Q,R}," diff=",ans]];
		If[debug,Print[ans]];
		Return[False];
	];
	If[debugAll,
		Print["Jacobi ok for ",{P,Q,R}];
	];
	Return[True];
];

(*Algebra assumed to be finitely generated*)
TestLeftLodayJacobi[Bracket_,algebra_,m_,SimplifyF_]:=Module[
	{notebookobject,basis,i,j,k}
,
	basis=algebra["basis"][m];
	If[!silent&&(Length[basis]>10),
		notebookobject=PrintTemporary[Dynamic[{i,j,k}]];
	];
	For[i=1,i<=Length[basis],i++,
		For[j=1,j<=Length[basis],j++,
			For[k=1,k<=Length[algebra["basis"][1]],k++,
				If[!CheckLeftLodayJacobi[basis[[i]],basis[[j]],algebra["basis"][1][[k]],Bracket,SimplifyF],
					Return[False];
				];
			];
		];
	];
	If[!silent&&Length[basis]>10,
		NotebookDelete[notebookobject];
	];
	Print["Left Loday-Jacobi is satisfied"];
	Return[True];
];

TestLeftLodayJacobi[Bracket_,algebra_,m_]:=TestLeftLodayJacobi[Bracket,algebra,m,Expand];

TestLeftLodayJacobi[Bracket_,algebra_]:=TestLeftLodayJacobi[Bracket,algebra,3];

AddEqDynamic[eqs0_,algebra_,message_]:=Module[
	{eqs,i}
,
	For[i=1,i<=Length[algebra["subst"]],i++,
		eqs=Factor[Map[#/.(algebra["subst"][[i]])&,eqs0]];
		eqs=DeleteCases[eqs,True];
		eqs=DeleteDuplicates[eqs];
		If[debug,Print["Eqs after subst ",eqs]];
		If[eqs!={},
			If[!silent,Print["Adding new equations for ",message]];
			algebra["eqsall"]=DeleteDuplicates[Join[algebra["eqsall"],eqs0]];
			algebra["subst"]=Factor[Solve[algebra["eqsall"],algebra["constants"]]];
			If[debug,Print["new subst= ",algebra["subst"]]];
			Break[];
		];
	];
];

AddEqStatic[eqs0_,algebra_,message_]:=Module[
	{eqs=DeleteDuplicates[DeleteCases[eqs0,True]],i}
	,
	If[eqs=={},Return[]];
	If[debug,Print["Adding equations ",eqs]];
	For[i=1,i<=Length[eqs],i++,
		If[Position[algebra["eqsall"],eqs[[i]]]=={},AppendTo[algebra["eqsall"],eqs[[i]]]];
	];
];

TuneConstantsJacobi[algebra_,basis_,AddEq_]:=Module[
	{
		i=0,j=0,k=0,P,Q,R,notebookobject,expr,
		Bracket,rules,eqs0
	}
,
	Bracket:=algebra["Bracket"];
	If[!silent&&!appsmode,notebookobject=PrintTemporary["TuneConstantsJacobi counter ",Dynamic[{i,j,k}]]];
	For[i=1,i<=Length[basis],i++,
		For[j=1,j<=Length[basis],j++,
			If[!silent&&appsmode,Print["Starting with ",{i,j}]];
			For[k=1,k<=Length[algebra["generators"]],k++,
				If[Setting[algebra["subst"]]=={},Break[]];
				P=basis[[i]];
				Q=basis[[j]];
				R=algebra["generators"][[k]];
				expr=Bracket[P,Bracket[Q,R]]-Bracket[Q,Bracket[P,R]]-Bracket[Bracket[P,Q],R];
				If[debugAll,Print[{P,Q,R}," ",expr]];
				rules=AbstractAlgebra`General`Rules[expr,algebra["groundfield"]];
				If[debugAll,Print[rules]];
				eqs0=Map[#[[2]]==0&,rules];
				If[debugAll,Print[eqs0]];
				AddEq[eqs0,algebra,{P,Q,R}];
			];
		];
	];
	If[!silent&&!appsmode,NotebookDelete[notebookobject]];
];

ParallelTuneConstantsJacobi[algebra_,basis_,AddEq_]:=Module[
	{
		Bracket,eqs,GenerateEq,timestart,i,j,k
	}
,
	Bracket:=algebra["Bracket"];
	GenerateEq[i_,j_,k_]:=Module[
		{P,Q,R,expr,rules,debugAll=False,eqs0}
	,
		If[Setting[algebra["subst"]]=={},Break[]];
		P=basis[[i]];
		Q=basis[[j]];
		R=algebra["generators"][[k]];
		expr=Bracket[P,Bracket[Q,R]]-Bracket[Q,Bracket[P,R]]-Bracket[Bracket[P,Q],R];
		If[debugAll,Print[{P,Q,R}," ",expr]];
		rules=AbstractAlgebra`General`Rules[expr,algebra["groundfield"]];
		If[debugAll,Print[rules]];
		eqs0=Map[#[[2]]==0&,rules];
		If[debugAll,Print[eqs0]];
		DeleteDuplicates[eqs0];
		Return[eqs0];
	];
	timestart=TimeUsed[];
	If[!silent&&!appsmode,Print["Adding equations to satisfy Jacobi identity"]];
	DistributeDefinitions["AbstractAlgebra`","Global`",basis,algebra,Bracket,GenerateEq];
	eqs=Flatten[ParallelTable[GenerateEq[i,j,k],{i,1,Length[basis]},{j,1,Length[basis]},{k,1,Length[algebra["generators"]]}]];
	If[!silent,Print["Equations generated, time used = ",TimeUsed[]-timestart]];
	AddEq[eqs,algebra,"ParallelJacobi"];
];

TuneConstantsJacobiRandom[algebra_,maxlength_,maxstep_,AddEq_]:=Module[
	{i=0,notebookobject,P,Q,R,expr,rules,eqs0,Bracket}
,
	Bracket:=algebra["Bracket"];
	If[!silent&&!appsmode,notebookobject=PrintTemporary["TuneConstantsJacobiRandom counter ",Dynamic[i]]];
	For[i=1,i<=maxstep,i++,
		P=NonCommutative`TestRelations`RandomMonomial[algebra["generators"],maxlength];
		Q=NonCommutative`TestRelations`RandomMonomial[algebra["generators"],maxlength];
		R=NonCommutative`TestRelations`RandomMonomial[algebra["generators"],maxlength];
		expr=Expand[Bracket[P,Bracket[Q,R]]-Bracket[Q,Bracket[P,R]]-Bracket[Bracket[P,Q],R]];
		If[debugAll,Print[{P,Q,R}," ",expr]];
		rules=AbstractAlgebra`General`Rules[expr,algebra["groundfield"]];
		If[debugAll,Print[rules]];
		eqs0=Map[#[[2]]==0&,rules];
		If[debugAll,Print[eqs0]];
		AddEq[eqs0,algebra,{P,Q,R}];
		If[Length[algebra["subst"]]==1,
			If[DeleteCases[algebra["contants"]/.algebra["subst"][[1]],0]=={},
				If[!silent,Print["Trivial solution only"]];
				If[!silent&&!appsmode,NotebookDelete[notebookobject]];
				Return[];
			];
		];
	];
	If[!silent&&!appsmode,NotebookDelete[notebookobject]];
];

TuneConstantsSkewSymmetry[algebra_,basis_,AddEq_]:=Module[
	{i,j,diff,eqs0,M,notebookobject}
,
	If[!silent&&!appsmode,notebookobject=PrintTemporary["TuneConstantsSkewSymmetry counter ",Dynamic[{i,j}]]];
	NonCommutativePoissonGeometry`CyclicSpace`DefineCanonicalForm[algebra];
	For[i=1,i<=Length[basis],i++,
		For[j=1,j<=Length[basis],j++,
			diff=algebra["Bracket"][basis[[i]],basis[[j]]]+algebra["Bracket"][basis[[j]],basis[[i]]];
			diff=algebra["Cyclic"][diff];
			If[debugAll,Print[{basis[[i]],basis[[j]]},", diff=",diff]];
			eqs0=Map[#[[2]]==0&,AbstractAlgebra`General`Rules[diff,algebra["groundfield"]]];
			AddEq[eqs0,algebra,{basis[[i]],basis[[j]]}];
		];
	];
	If[!silent&&!appsmode,NotebookDelete[notebookobject]];
];

TuneConstants[algebra_,maxlength_]:=Module[
	{basis,timestart,i,j}
,
	If[!ValueQ[algebra["eqsall"]],algebra["eqsall"]={}];
	If[!ValueQ[algebra["constants"]],algebra["constants"]={}];
	(*First testing bracket on pairs of generators*)
	basis=algebra["basis"][maxlength];
	If[debug,Print["Basis ",basis]];
	(*Adding Linear equations for SkewSymmetry*)
	TuneConstantsSkewSymmetry[algebra,basis,AddEqStatic];
	algebra["subst"]=Solve[algebra["eqsall"],algebra["constants"]];
	(*If[Length[algebra["subst"]]==1,
		If[!silent,Print["Resolving linear equations by Skew-Symmetry ",algebra["subst"]]];
		For[i=1,i<=Length[algebra["generators"]],i++,
			For[j=1,j<=Length[algebra["generators"]],j++,
				algebra["Bracket"][algebra["generators"][[i]],algebra["generators"][[j]]]=algebra["Bracket"][algebra["generators"][[i]],algebra["generators"][[j]]]/.algebra["subst"][[1]];
			];
		];
		algebra["subst"]={{}};
		algebra["eqsall"]={};
	];*)
	(*Adding Quadratic equations for Jacobi identity*)
	TuneConstantsJacobiRandom[algebra,maxlength,100,AddEqDynamic];
	(*TuneConstantsJacobi[algebra,algebra["generators"],AddEqStatic];*)
	If[!silent,Print["Minimal equations added"]];
	(*algebra["eqsall"]=DeleteDuplicates[algebra["eqsall"]];
	timestart=TimeUsed[];
	algebra["subst"]=Solve[algebra["eqsall"],algebra["constants"]];
	If[!silent,Print["Equations solved, time used ",TimeUsed[]-timestart]];
	If[!silent,Print[algebra["subst"]]];*)
	(*Defining Full basis*)
	basis=Delete[Flatten[NonCommutative`PolynomialIdeals`FreeAssociativeBasis[algebra["generators"],maxlength]],1];
	(*Testing Identities for all words*)
	(*TuneConstantsSkewSymmetry[algebra,basis,AddEqDynamic];*)
	(*TuneConstantsJacobi[algebra,basis,AddEqDynamic];*)
	(*Returning result*)
	If[algebra["subst"]==={},Return[False],Return[True]];
];

End[]

Begin["`Integrability`"]

silent=False;

AddEqHamilton[algebra_,i_,j_]:=Module[
	{h1,h2,expr,eqs,k}
,
	h1=Expand[NonCommutativeMultiply@@Table[algebra["h"],i]];
	h2=Expand[NonCommutativeMultiply@@Table[algebra["h"],j]];
	expr=Expand[Br[h1,h2]];
	expr=algebra["Cyclic"][expr];
	eqs=Map[#[[2]]==0&,AbstractAlgebra`General`Rules[expr,algebra["groundfield"]]];
	algebra["eqsallh"]=Join[algebra["eqsallh"],eqs];
	algebra["substh"]=Solve[algebra["eqsallh"],algebra["hconstants"]];
	If[!silent,
		For[k=1,k<=Length[algebra["substh"]],k++
			Print[Subscript["H", k]," = ",algebra["h"]/.algebra["substh"][[k]]];
		];
	];
];

TestHamiltonCommutativity[algebra_,maxpow_]:=Module[
	{snum,i,j,h,h1,h2,expr}
,
	For[snum=1,snum<=Length[algebra["substh"]],snum++,
		h=algebra["h"]/.algebra["substh"][[snum]];
		h1=h**h;
		For[i=3,i<=maxpow,i++,
			h1=h1**h;
			h2=1;
			For[j=1,j<i,j++,
				If[!silent,Print["Testing ",{i,j}]];
				h2=h2**h;
				expr=Expand[algebra["Bracket"][h1,h2]];
				expr=Expand[algebra["Cyclic"][expr]];
				If[expr=!=0,
					Print["Failure at ",{i,j},", adding new equations"];
					AddEqHamilton[algebra,i,j];
					Return[False];
				];
			];
		];
	];
	Return[True];
];

HamiltonSearch[algebra_,c_,maxlength_,maxpow_]:=Module[
	{basis,expr,i}
,
	AbstractAlgebra`InnerProduct`DefineAssociativeBasis[algebra];
	basis=algebra["basis"][maxlength];
	algebra["h"]=Sum[Subscript[c, i]basis[[i+1]],{i,1,Length[basis]-1}];
	algebra["hconstants"]=Table[Subscript[c, i],{i,1,Length[basis]}];
	(*Adding Basic Equations*)
	expr=Expand[algebra["Bracket"][algebra["h"],algebra["h"]**algebra["h"]]];
	expr=Expand[algebra["Cyclic"][expr]];
	algebra["eqsallh"]=Map[#[[2]]==0&,AbstractAlgebra`General`Rules[expr,algebra["groundfield"]],1];
	algebra["substh"]=DeleteDuplicates[Solve[algebra["eqsallh"],algebra["hconstants"]]];
	If[!silent,
		For[i=1,i<=Length[algebra["substh"]],i++,
			Print[Subscript["H", i]," = ",algebra["h"]/.algebra["substh"][[i]]];
		];
	];
	(*Testing higher powers*)
	While[!TestHamiltonCommutativity[algebra,maxpow]];
];

CasimirSearch[algebra_,c_,caslength_,testpow_]:=Module[
	{basis,i,cas,expr,eqs}
,
	AbstractAlgebra`InnerProduct`DefineAssociativeBasis[algebra];
	basis=algebra["basis"][caslength];
	algebra["c"]=Sum[Subscript[c, i]basis[[i]],{i,1,Length[basis]}];
	algebra["constantsc"]=Table[Subscript[c, i],{i,1,Length[basis]}];
	(*Main cycle*)
	basis=algebra["basis"][testpow];
	algebra["eqsallc"]={};
	algebra["substc"]={{}};
	cas=algebra["c"];
	For[i=1,i<=Length[basis],i++,
		expr=Expand[algebra["Bracket"][basis[[i]],cas]];
		If[expr=!=0,
			eqs=Map[#[[2]]==0&,AbstractAlgebra`General`Rules[expr,algebra["groundfield"]]];
			algebra["eqsallc"]=Join[algebra["eqsallc"],eqs];
			algebra["substc"]=Solve[algebra["eqsallc"],algebra["constantsc"]];
			algebra["substc"]=DeleteDuplicates[algebra["substc"]];
			If[Length[algebra["substc"]>1],
				Print["Unexpected number of solutions for linear equation in CasimirSearch ",algebra["substc"]];
				Return[Indeterminate];
			];
			cas=algebra["c"]/.algebra["substc"][[1]];
			If[!silent&&i>1,Print["New expression for Casimir ",cas]];
		];
	];
];

CasimirQ[cas_,algebra_,maxlength_]:=Module[
	{diff,i}
,
	For[i=1,i<=Length[algebra["basis"][maxlength]],i++,
		If[Expand[diff=algebra["Bracket"][algebra["basis"][2][[i]],cas]]=!=0,
			Return[False];
		];
	];
	Return[True];
];

CasimirQ[cas_,algebra_]:=CasimirQ[cas,algebra,2];

GroupCasimirSearch[algebra_,caslength_,testpow_]:=Module[
	{i=0,ans={},notebookobject}
,
	If[!silent&&Length[algebra["basis"][caslength]]>=100,
		notebookobject=PrintTemporary[Dynamic[i]];
	];
	For[i=1,i<=Length[algebra["basis"][caslength]],i++,
		If[CasimirQ[algebra["basis"][caslength][[i]],algebra,testpow],
			AppendTo[ans,algebra["basis"][caslength][[i]]];
		];
	];
	If[!silent&&Length[algebra["basis"][calength]]>=100,
		NotebookDelete[notebookobject];
	];
	Return[ans];
];

GroupCasimirSearch[algebra_,caslength_]:=GroupCasimirSearch[algebra,caslength,2];

End[]

Begin["`Homomorphisms`"]

debugAll=False;

CheckPolynomialHomomorphism[algebra1_,algebra2_,c_,degree_,R0_]:=Module[
	{F,counterc=0,i,j,eqs={},diff,u,v,sol,ans={},ftab,ftabcomm,jacobian,rank,GenericRHS}
,
	(*Defining generic Homomorphism*)
	GenericRHS:=Sum[\!\(\*SubscriptBox[\(c\), \(++counterc\)]\)algebra2["basis"][degree][[i]],{i,1,Length[algebra2["basis"][degree]]}];
	If[!ValueQ[algebra1["groupgenerators"]],algebra1["groupgenerators"]=algebra1["generators"]];
	AbstractAlgebra`Homomorphisms`DefineOnGenerators[F,algebra1];
	For[i=1,i<=Length[algebra1["groupgenerators"]],i++,
		F[algebra1["groupgenerators"][[i]]]=GenericRHS;
		If[debugAll,Print[F[algebra1["groupgenerators"][[i]]]]];
	];
	(*Looking for admissible values of generic parameters*)
	For[i=1,i<=Length[algebra1["groupgenerators"]],i++,
		For[j=1,j<=Length[algebra1["groupgenerators"]],j++,
			u=algebra1["groupgenerators"][[i]];
			v=algebra1["groupgenerators"][[j]];
			diff=F[algebra1["DBracket"][u\[CircleTimes]v]]-algebra2["DBracket"][F[u]\[CircleTimes]F[v]]+R0[F[u]\[CircleTimes]F[v]];
			eqs=Join[eqs,Map[#[[2]]==0&,AbstractAlgebra`General`Rules[diff,algebra2["groundfield"]]]];
		];
	];
	sol=DeleteDuplicates[Solve[eqs]];
	If[debugAll,Print[sol]];
	(*Calculating rank of transformation*)
	For[i=1,i<=Length[sol],i++,
		ftab=Map[F,algebra1["groupgenerators"]]/.sol[[i]];
		ftabcomm=ftab/.{Global`Inv->(1/#&),NonCommutativeMultiply->Times};
		jacobian=Map[Table[D[#,algebra2["groupgenerators"][[i]]],{i,1,Length[algebra2["groupgenerators"]]}]&,ftabcomm];
		If[debugAll,Print[MatrixForm[Factor[jacobian]]]];
		rank=MatrixRank[jacobian];
		If[2rank>Length[algebra1["groupgenerators"]],AppendTo[ans,{rank,ftab}]];
	];
	Return[Reverse[SortBy[ans,First]]];
];

CheckPolynomialHomomorphism[algebra1_,algebra2_,c_,degree_]:=CheckPolynomialHomomorphism[algebra1,algebra2,c,degree,0&];

CheckPolynomialHomomorphismGradedH0[algebra1_,algebra2_,c_,degree_]:=Module[
	{e,\[Lambda],i,u,counterc=0,P0,R0}
,
	(*Defning Trivial H0 bracket on algebra2*)
	If[!ValueQ[algebra2["groupgenerators"]],
	algebra2["groupgenerators"]=algebra2["generators"]];
	algebra2["vectorfields"]={e,\[Lambda]};
	NonCommutativePoissonGeometry`PolyVectorFields`DefineDoubleGerstenhaberAlgebra[algebra2];
	e[expr_]:=expr\[CircleTimes]1-1\[CircleTimes]expr;
	For[i=1,i<=Length[algebra2["groupgenerators"]],i++,
		u=algebra2["groupgenerators"][[i]];
		\[Lambda][u]=\!\(\*SubscriptBox[\(c\), \(--counterc\)]\)u\[CircleTimes]1+\!\(\*SubscriptBox[\(c\), \(--counterc\)]\)1\[CircleTimes]u;
	];
	P0=e\[Star]\[Lambda];
	R0=algebra2["TrA"][P0];
	Return[CheckPolynomialHomomorphism[algebra1,algebra2,c,degree,R0]];
];

CheckLinearHomomorphism[algebra1_,algebra2_,c_]:=CheckPolynomialHomomorphism[algebra1,algebra2,c,1];

CheckLinearHomomorphismGradedH0[algebra1_,algebra2_,c_]:=CheckPolynomialHomomorphismGradedH0[algebra1,algebra2,c,1];

CheckLinearIsomorphism[algebra1_,algebra2_,c_]:=Module[
	{F12tab,F21tab}
,
	F12tab=CheckLinearHomomorphism[algebra1,algebra2,c];
	F21tab=CheckLinearHomomorphism[algebra2,algebra1,c];
	If[F12tab=={}||F21tab=={},Return[False]];
	Return[F12tab[[1,1]]==F21tab[[1,1]]==Length[algebra1["groupgenerators"]]==Length[algebra2["groupgenerators"]]];
];

End[]

Begin["`Hochschild`"]

DefineHochschildChains[cat_]:=(
	AbstractAlgebra`GroundField`SetMultiLinear[cat["d"],cat["groundfield"]];
	cat["d"][x_?(cat["ElementaryMorphismQ"])]:=0;
	With[
		{CircleTimes=cat["CircleTimes"]}
	,
		cat["d"][x_CircleTimes]:=Module[
			{xtab=x,i,Ltab,Rtab,ans=0}
		,
			xtab[[0]]=List;
			For[i=1,i<Length[xtab],i++,
				Ltab=Take[xtab,i];
				Rtab=Drop[xtab,i+1];
				Ltab[[-1]]=cat["Composition"][Ltab[[-1]],xtab[[i+1]]];
				ans+=(-1)^(i-1) CircleTimes@@Join[Ltab,Rtab];
			];
			Ltab=Drop[xtab,-1];
			Ltab[[1]]=cat["Composition"][xtab[[-1]],Ltab[[1]]];
			ans+=(-1)^(Length[xtab]-1) CircleTimes@@Ltab;
			Return[ans];
		];
	];
);

End[]

EndPackage[]



