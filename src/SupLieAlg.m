(* ::Package:: *)

BeginPackage["SupLieAlg`"];
Print["Loading lie superalgebra functions..."];


(* ::Subsection::Closed:: *)
(*Main functions*)


(*symbolic parameters*)
\[Delta];\[Epsilon];e;f;h;\[CapitalGamma];n\[CapitalGamma];m;n;S;b;
(*check that if x match any of the patterns*)
AnyMatchQ;
(*check: roots of Super type C*)
RootSupCQ;
PosRootSupCQ;
OddRootSupCQ;
EvenRootSupCQ;
(*root to matrix*)
Root2MatrixC;
(*lie and lie super bracket*)
Lie;LieS;
(*Dynkin diagram of roots*)
DiagramSupC;

(*text functions*)
CoefSupC;
ReadBracket;

(*equations*)
(*GetLineCuts;*)
BreakApart;
CutLine;
MultiReplace;
MultiReplaces;

Error;ReplaceOne;
ImageTail;ImageHead;
CaseMatchHeadQ;
EquationItems;
Equation;


Begin["Private`"]


(* ::Subsection::Closed:: *)
(*Predefine invariables*)


(* ::Subsubsection::Closed:: *)
(*Symbolic root patterns*)


SetAttributes[S,Orderless];
Protect[\[Delta],\[Epsilon],e,f,h,\[CapitalGamma],n\[CapitalGamma],m,n,b];
pospatterns={Subscript[\[Epsilon], i_]-Subscript[\[Epsilon], j_],-Subscript[\[Delta], j_]+Subscript[\[Epsilon], i_],Subscript[\[Delta], i_]-Subscript[\[Delta], j_],
Subscript[\[Delta], i_]+Subscript[\[Delta], j_],2 Subscript[\[Delta], i_],Subscript[\[Delta], j_]+Subscript[\[Epsilon], i_],Subscript[\[Epsilon], i_]+Subscript[\[Epsilon], j_]};
rootpatterns=pospatterns~Join~-pospatterns;


(* ::Subsubsection::Closed:: *)
(*Symbolic root matrices*)


(*Note that -(Subscript[\[Epsilon], i]-Subscript[\[Epsilon], j])=Subscript[\[Epsilon], j]-Subscript[\[Epsilon], i] might have ambiguity*)
root2mat={(*positive even*)
Subscript[\[Epsilon], i_]-Subscript[\[Epsilon], j_]:>Subscript[e, i,j]-Subscript[e, n+j,n+i],
Subscript[\[Epsilon], i_]+Subscript[\[Epsilon], j_]:>Subscript[e, i,n+j]-Subscript[e, j,n+i],
Subscript[\[Delta], i_]-Subscript[\[Delta], j_]:>Subscript[e, i+2 n,j+2 n]-Subscript[e, j+m+2 n,i+m+2 n],
Subscript[\[Delta], i_]+Subscript[\[Delta], j_]:>Subscript[e, i+2 n,j+m+2 n]+Subscript[e, j+2 n,i+m+2 n],
2 Subscript[\[Delta], i_]:>Subscript[e, i+2 n,i+m+2 n],
(*positive odd*)
Subscript[\[Epsilon], i_]-Subscript[\[Delta], j_]:>Subscript[e, i,j+2n]-Subscript[e, j+m+2n,i+n],
Subscript[\[Epsilon], i_]+Subscript[\[Delta], j_]:>Subscript[e, i,j+m+2n]+Subscript[e, j+2n,i+n],
(*negative odd*)
Subscript[\[Delta], j_]-Subscript[\[Epsilon], i_]:>-Subscript[e, i+n,j+m+2 n]-Subscript[e, j+2 n,i],
-Subscript[\[Delta], j_]-Subscript[\[Epsilon], i_]:>Subscript[e, i+n,j+2 n]-Subscript[e, j+m+2 n,i]};
(*error message*)
NoneRoot::notroot="`` is not a root!";
NoneRoot::notposroot="`` is not a positive root!";


(* ::Subsubsection::Closed:: *)
(*roots and positive roots*)


positiveroots={Subscript[\[Epsilon], i]-Subscript[\[Epsilon], j],-Subscript[\[Delta], j]+Subscript[\[Epsilon], i],Subscript[\[Delta], i]-Subscript[\[Delta], j],
Subscript[\[Delta], i]+Subscript[\[Delta], j],2 Subscript[\[Delta], i],Subscript[\[Delta], j]+Subscript[\[Epsilon], i],Subscript[\[Epsilon], i]+Subscript[\[Epsilon], j]};
roots=positiveroots~Join~-positiveroots;
(*symbolic roots by switch i,j,k in "roots"*)
generalroots=(positiveroots/.Thread[{i,j,k}->#]&)/@Permutations[{i,j,k},{3}]//Flatten//DeleteDuplicates;


(* ::Subsubsection::Closed:: *)
(*Dynkin diagrams*)


posroot2diagram={
(*positive even roots*)
Subscript[\[Epsilon], i_]-Subscript[\[Epsilon], j_]:>StringForm["\!\(\*SubscriptBox[\(\[Alpha]\), \(``\)]\)-\!\(\*SubscriptBox[\(\[Alpha]\), \(``\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Alpha]\), \(``\)]\)",i,i+1,j-1],
Subscript[\[Epsilon], i_]+Subscript[\[Epsilon], j_]:>StringForm["\!\(\*SubscriptBox[\(\[Alpha]\), \(``\)]\)-\!\(\*SubscriptBox[\(\[Alpha]\), \(``\)]\)-\[CenterEllipsis]-(\!\(\*SubscriptBox[\(\[Alpha]\), \(n\)]\))-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + 1\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + m - 1\)]\)\[DoubleLongLeftArrow]\!\(\*SubscriptBox[\(\[Alpha]\), \(n + m\)]\)\[DoubleLongRightArrow]\!\(\*SubscriptBox[\(\[Alpha]\), \(n + m - 1\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + 1\)]\)-(\!\(\*SubscriptBox[\(\[Alpha]\), \(n\)]\))-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Alpha]\), \(``\)]\)-\!\(\*SubscriptBox[\(\[Alpha]\), \(``\)]\)",i,i+1,j+1,j],
Subscript[\[Delta], i_]-Subscript[\[Delta], j_]:>StringForm["\!\(\*SubscriptBox[\(\[Alpha]\), \(n + ``\)]\)-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + ``\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Alpha]\), \(n``\)]\)",i,i+1,j-1],
Subscript[\[Delta], i_]+Subscript[\[Delta], j_]:>StringForm["\!\(\*SubscriptBox[\(\[Alpha]\), \(n + ``\)]\)-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + ``\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + m - 1\)]\)\[DoubleLongLeftArrow]\!\(\*SubscriptBox[\(\[Alpha]\), \(n + m\)]\)\[DoubleLongRightArrow]\!\(\*SubscriptBox[\(\[Alpha]\), \(n + m - 1\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + ``\)]\)-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + ``\)]\)",i,i+1,j+1,j],
2 Subscript[\[Delta], i_]:>StringForm["\!\(\*SubscriptBox[\(\[Alpha]\), \(n + ``\)]\)-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + ``\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + m - 1\)]\)\[DoubleLongLeftArrow]\!\(\*SubscriptBox[\(\[Alpha]\), \(n + m\)]\)\[DoubleLongRightArrow]\!\(\*SubscriptBox[\(\[Alpha]\), \(n + m - 1\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + ``\)]\)-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + ``\)]\)",i,i+1,i+1,i],
(*positive odd roots*)
Subscript[\[Epsilon], i_]-Subscript[\[Delta], j_]:>StringForm["\!\(\*SubscriptBox[\(\[Alpha]\), \(``\)]\)-\!\(\*SubscriptBox[\(\[Alpha]\), \(``\)]\)-\[CenterEllipsis]-(\!\(\*SubscriptBox[\(\[Alpha]\), \(n\)]\))-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + 1\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Alpha]\), \(n``\)]\)",i,i+1,j-1],
Subscript[\[Epsilon], i_]+Subscript[\[Delta], j_]:>StringForm["\!\(\*SubscriptBox[\(\[Alpha]\), \(``\)]\)-\!\(\*SubscriptBox[\(\[Alpha]\), \(``\)]\)-\[CenterEllipsis]-(\!\(\*SubscriptBox[\(\[Alpha]\), \(n\)]\))-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + 1\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + m - 1\)]\)\[DoubleLongLeftArrow]\!\(\*SubscriptBox[\(\[Alpha]\), \(n + m\)]\)\[DoubleLongRightArrow]\!\(\*SubscriptBox[\(\[Alpha]\), \(n + m - 1\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + ``\)]\)-\!\(\*SubscriptBox[\(\[Alpha]\), \(n + ``\)]\)",i,i+1,j+1,j]};
negroot2diagram={
Subscript[\[Epsilon], i_]-Subscript[\[Epsilon], j_]:>StringForm["\!\(\*SubscriptBox[\(\[Beta]\), \(``\)]\)-\!\(\*SubscriptBox[\(\[Beta]\), \(``\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(``\)]\)",j-1,i+1,i],
Subscript[\[Epsilon], i_]+Subscript[\[Epsilon], j_]:>StringForm["\!\(\*SubscriptBox[\(\[Beta]\), \(``\)]\)-\!\(\*SubscriptBox[\(\[Beta]\), \(``\)]\)-\[CenterEllipsis]-(\!\(\*SubscriptBox[\(\[Beta]\), \(n\)]\))-\!\(\*SubscriptBox[\(\[Beta]\), \(n + 1\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(n + m - 1\)]\)\[DoubleLongLeftArrow]\!\(\*SubscriptBox[\(\[Beta]\), \(n + m\)]\)\[DoubleLongRightArrow]\!\(\*SubscriptBox[\(\[Beta]\), \(n + m - 1\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(n + 1\)]\)-(\!\(\*SubscriptBox[\(\[Beta]\), \(n\)]\))-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(``\)]\)-\!\(\*SubscriptBox[\(\[Beta]\), \(``\)]\)",j,j+1,i+1,i],
Subscript[\[Delta], i_]-Subscript[\[Delta], j_]:>StringForm["\!\(\*SubscriptBox[\(\[Beta]\), \(n``\)]\)-\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)",j-1,i+1,i],
Subscript[\[Delta], i_]+Subscript[\[Delta], j_]:>StringForm["\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)-\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(n + m - 1\)]\)\[DoubleLongLeftArrow]\!\(\*SubscriptBox[\(\[Beta]\), \(n + m\)]\)\[DoubleLongRightArrow]\!\(\*SubscriptBox[\(\[Beta]\), \(n + m - 1\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)-\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)",j,j+1,i+1,i],
2 Subscript[\[Delta], i_]:>StringForm["\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)-\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(n + m - 1\)]\)\[DoubleLongLeftArrow]\!\(\*SubscriptBox[\(\[Beta]\), \(n + m\)]\)\[DoubleLongRightArrow]\!\(\*SubscriptBox[\(\[Beta]\), \(n + m - 1\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)-\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)",i,i+1,i+1,i],
(*positive odd*)
Subscript[\[Epsilon], i_]-Subscript[\[Delta], j_]:>StringForm["\!\(\*SubscriptBox[\(\[Beta]\), \(n``\)]\)-\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(n + 1\)]\)-(\!\(\*SubscriptBox[\(\[Beta]\), \(n\)]\))-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(``\)]\)",j-1,i+1,i],
Subscript[\[Epsilon], i_]+Subscript[\[Delta], j_]:>StringForm["\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)-\!\(\*SubscriptBox[\(\[Beta]\), \(n + ``\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(n + m - 1\)]\)\[DoubleLongLeftArrow]\!\(\*SubscriptBox[\(\[Beta]\), \(n + m\)]\)\[DoubleLongRightArrow]\!\(\*SubscriptBox[\(\[Beta]\), \(n + m - 1\)]\)-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(n + 1\)]\)-(\!\(\*SubscriptBox[\(\[Beta]\), \(n\)]\))-\[CenterEllipsis]-\!\(\*SubscriptBox[\(\[Beta]\), \(``\)]\)-\!\(\*SubscriptBox[\(\[Beta]\), \(``\)]\)",j,j+1,i+1,i]};


(* ::Subsection::Closed:: *)
(*Basic functions*)


(* ::Subsubsection::Closed:: *)
(*Match function*)


(*check that if x match any of the patterns*)
AnyMatchQ[x_,patterns_]:=AnyTrue[patterns,MatchQ[x,#]&];
AnyMatchQ[patterns_][x_]:=AnyMatchQ[x,patterns];


(*check: roots of Super type C*)
RootSupCQ=AnyMatchQ[rootpatterns];
PosRootSupCQ=AnyMatchQ[pospatterns];
OddRootSupCQ=AnyMatchQ[{Subscript[\[Epsilon], i_]-Subscript[\[Delta], j_],Subscript[\[Epsilon], i_]+Subscript[\[Delta], j_],-Subscript[\[Epsilon], i_]-Subscript[\[Delta], j_],-Subscript[\[Epsilon], i_]+Subscript[\[Delta], j_]}];
EvenRootSupCQ=RootSupCQ[#]&&!OddRootSupCQ[#]&;


(* ::Subsubsection::Closed:: *)
(*Root -> matrix*)


Root2MatrixC[root_,pos_]:=Message[NoneRoot::notposroot,root]/;!PosRootSupCQ@root;
Root2MatrixC[root_]:=Message[NoneRoot::notposroot,root]/;!PosRootSupCQ@root;
Root2MatrixC[root_,pos_:True]:=Which[
(*positive root*)
pos,root/.root2mat,
(*negative odd root*)
OddRootSupCQ@root,(-root)/.root2mat,
(*negative even root*)
True,root/.root2mat/.Subscript[e, i_,j_]:>Subscript[e, j,i]];
(*Subscript[e, x_?PosRootSupCQ]:=Root2MatrixC@x;
Subscript[f, x_?PosRootSupCQ]:=Root2MatrixC[x,False];*)
Subscript[e, x_]:=Root2MatrixC@x;
Subscript[f, x_]:=Root2MatrixC[x,False];
Subscript[h, \[Alpha]_]:=LieS[Subscript[e, \[Alpha]],Subscript[f, \[Alpha]],EvenRootSupCQ@\[Alpha]];


(* ::Subsubsection::Closed:: *)
(*Matrix operation*)


(*matrix product*)
Subscript/:Subscript[e, i_,j_]**Subscript[e, k_,l_]:=If[j===k,Subscript[e, i,l],0];
Subscript/:Subscript[f, i_,j_]**Subscript[f, k_,l_]:=If[j===k,Subscript[f, i,l],0];
(*non-commutative product \[Rule] add linearity*)
Unprotect[NonCommutativeMultiply];
DownValues[NonCommutativeMultiply]={
(*HoldPattern[(x_+y_)**(a_+b_)]\[RuleDelayed]x**a+x**b+y**a+y**b,*)
HoldPattern[x_**(y_+z_)]:>x**y+x**z,
HoldPattern[(y_+z_)**x_]:>y**x+z**x,
HoldPattern[x_**(-y_)]:>-x**y,
HoldPattern[(-x_)**y_]:>-x**y};
Protect[NonCommutativeMultiply];
(*lie bracket*)
Lie[x_,y_]:=(x**y-y**x);
(*lie super bracket*)
LieS[x_,y_,anyeven_:True]:=If[anyeven,Lie[x,y],x**y+y**x];


(* ::Subsubsection::Closed:: *)
(*Dynkin diagram*)


(*Dynkin diagram of roots*)
DiagramSupC[root_,pos_]:=Message[NoneRoot::notposroot,root]/;!PosRootSupCQ@root;
DiagramSupC[root_,pos_:True]:=root/.If[pos,posroot2diagram,negroot2diagram];
Subscript[\[CapitalGamma], root_]:=DiagramSupC[root];
Subscript[n\[CapitalGamma], root_]:=DiagramSupC[root,False];


(* ::Subsubsection::Closed:: *)
(*Bilinear form*)


Subscript/:Subscript[\[Epsilon], i_] Subscript[\[Epsilon], j_]:=If[i===j,-1,0];
Subscript/:Subscript[\[Delta], i_] Subscript[\[Delta], j_]:=If[i===j,1,0];
Subscript/:Subscript[\[Epsilon], i_] Subscript[\[Delta], j_]:=0;
Subscript/:Subscript[\[Epsilon], i_]^2:=-1;
Subscript/:Subscript[\[Delta], i_]^2:=1;


(* ::Subsection::Closed:: *)
(*Text functions*)


(*structure coefficient*)
CoefSupC[\[Alpha]_,\[Beta]_,s\[Alpha]_:1,s\[Beta]_:1,s\[Gamma]_:1]:=Module[{x,y,z,\[Gamma]},
x=If[s\[Alpha]==1,Subscript[e, \[Alpha]],Subscript[f, \[Alpha]]];y=If[s\[Beta]==1,Subscript[e, \[Beta]],Subscript[f, \[Beta]]];
\[Gamma]=s\[Gamma](s\[Alpha] \[Alpha]+s\[Beta] \[Beta]);z=If[s\[Gamma]==1,Subscript[e, \[Gamma]],Subscript[f, \[Gamma]]];
LieS[x,y,AnyTrue[{\[Alpha],\[Beta]},EvenRootSupCQ]]/z//Simplify];


(*readable form of the result of lie bracket operation*)
ReadBracket[\[Alpha]_,\[Beta]_,s\[Alpha]_:1,s\[Beta]_:1,s\[Gamma]_:1]:=Module[{ea,eb,ec,\[Gamma],da,db,dc},
\[Gamma]=s\[Gamma](s\[Alpha] \[Alpha]+s\[Beta] \[Beta]);
{ea,da}=If[s\[Alpha]==1,{e,Subscript[\[CapitalGamma], \[Alpha]]},{f,Subscript[n\[CapitalGamma], \[Alpha]]}];
{eb,db}=If[s\[Beta]==1,{e,Subscript[\[CapitalGamma], \[Beta]]},{f,Subscript[n\[CapitalGamma], \[Beta]]}];
{ec,dc}=If[s\[Gamma]==1,{e,Subscript[\[CapitalGamma], \[Gamma]]},{f,Subscript[n\[CapitalGamma], \[Gamma]]}];
StringForm["abstract form:
\t(`1`) + (`2`) = `3` , [ \!\(\*SubscriptBox[\(`11`\), \(\[Alpha]\)]\) , \!\(\*SubscriptBox[\(`12`\), \(\[Beta]\)]\) ] = `10`\[CenterDot]\!\(\*SubscriptBox[\(`13`\), \(\[Gamma]\)]\) , \[Gamma] = `14`\[CenterDot]\[Alpha]+`15`\[CenterDot]\[Beta]
matrix form:
\t[`4` , `5` \!\(\*SubscriptBox[\(]\), \(s\)]\) = `10`\[CenterDot](`6`)
diagram form:
 \t[`7` , `8`]\n\t=`10`\[CenterDot]`9`",s\[Alpha] \[Alpha],s\[Beta] \[Beta],s\[Gamma] \[Gamma],Subscript[ea, \[Alpha]],Subscript[eb, \[Beta]],Subscript[ec, \[Gamma]],da,db,dc,CoefSupC[\[Alpha],\[Beta],s\[Alpha],s\[Beta],s\[Gamma]],ea,eb,ec,s\[Alpha],s\[Beta]]];


(* ::Subsection:: *)
(*Equations*)


GetLineCuts[part_]:=(part/.Subscript[\[Delta], i_]-Subscript[\[Delta], j_]:> Sequence[i,j])[[2;;-2;;2]];


BreakApart[up_,down_]:=Module[{upcuts,downcuts,intercuts,upposs,downposs,upparts,downparts},
{upcuts,downcuts}=GetLineCuts/@{up,down};
intercuts=upcuts\[Intersection]downcuts;
{upposs,downposs}=Function[x,FirstPosition[x,#]&/@intercuts//Flatten//Prepend[0]//Append[-1]]/@{upcuts,downcuts};
upparts=MapThread[up[[#1+1;;#2]]&,{upposs[[;;-2]],upposs[[2;;]]}];
downparts=MapThread[down[[#1+1;;#2]]&,{downposs[[;;-2]],downposs[[2;;]]}];
Thread@{upparts,downparts}];


CutLine[head_,tail_][body_]:=CutLine[{head,Sequence@@body,tail}];
CutLine[head_,tail_,body_]:=CutLine[{head,Sequence@@body,tail}];
CutLine[list_]:=MapThread[Subscript[\[Delta], #1]-Subscript[\[Delta], #2]&,{list[[;;-2]],list[[2;;]]}];


MultiReplace[list_,start_,end_]:=list/.Thread[start->end];
MultiReplace[start_,end_][list_]:=MultiReplace[list,start,end];
MultiReplaces[list_,start_,ends_]:=MultiReplace[list,start,#]&/@ends//Flatten[#,1]&;
MultiReplaces[start_,ends_][list_]:=MultiReplaces[list,start,ends];


Error::notmember="`` is not in ``";
ReplaceOne[list_,old_,new_]:=Message[Error::notmember,old,list]/;!MemberQ[list,old];
ReplaceOne[list_,old_,new_]:=Append[DeleteCases[list,old,1,1],new];


ImageTail[\[Alpha]_][case_]:=ImageTail[case,\[Alpha]];
ImageTail[case_,\[Alpha]_]:=Module[{f\[Beta],isroot},
f\[Beta]=S@@Flatten@case;
isroot=List@@Select[f\[Beta],RootSupCQ[#-\[Alpha]]&];
Merge[ReplaceOne[f\[Beta],#,#-\[Alpha]]->CoefSupC[\[Alpha],#,1,-1,-1]&/@isroot,Total]];


Error::match="match error";
ImageHead[\[Alpha]_][case_]:=ImageHead[case,\[Alpha]];
ImageHead[case_,\[Alpha]_]:=Message[Error::notmember,\[Alpha],case]/;!MemberQ[Flatten@case,\[Alpha]];
ImageHead[case_,\[Alpha]_]:=Module[{f\[Beta],i,j,value},
f\[Beta]=S@@Flatten@case;
{i,j}=\[Alpha]/.Subscript[\[Delta], i_]-Subscript[\[Delta], j_]:>{i,j};

value=Switch[{Count[f\[Beta],Subscript[\[Delta], j_]-Subscript[\[Delta], i]],Count[f\[Beta],Subscript[\[Delta], j]-Subscript[\[Delta], i_]]},
(*e.g. left cut\[Rule]{2,-} *)
{1,1},Subscript[b, i]-Subscript[b, j]+1,
{2,1},Subscript[b, i]-Subscript[b, j],
{1,2},Subscript[b, i]-Subscript[b, j]+2,
{2,2},Subscript[b, i]-Subscript[b, j]+1,
_,Message[Error::match]];
DeleteCases[f\[Beta],\[Alpha],1,1]->value];


EquationItems[headcase_,cases_,\[Alpha]_]:=Module[{head,coef,tailcases,tailcoefs},
{head,coef}=List@@ImageHead[headcase,\[Alpha]];
tailcases=Select[cases,CaseMatchHeadQ[head,\[Alpha]]];
tailcoefs=ImageTail[#,\[Alpha]][head]&/@tailcases;
{head,<|(Column/@headcase)->coef,Sequence@@Thread[(Column/@#)&/@tailcases->tailcoefs]|>}]
EquationItems[cases_,\[Alpha]_][headcase_]:=EquationItems[headcase,cases,\[Alpha]];


CaseMatchHeadQ[case_,match_,\[Alpha]_]:=Module[{isroot,roots},
roots=S@@Flatten@case;
isroot=Select[roots,RootSupCQ[#-\[Alpha]]&];
AnyTrue[isroot,ReplaceOne[roots,#,#-\[Alpha]]===match&]];
CaseMatchHeadQ[match_,\[Alpha]_][case_]:=CaseMatchHeadQ[case,match,\[Alpha]];


Equation[headcase_,cases_,\[Alpha]_]:=Module[{head,image,keys},
{head,image}=EquationItems[headcase,cases,\[Alpha]];
keys=Keys@image;
{head,(image@# f@@#&/@keys//Total)==0}];
Equation[cases_,\[Alpha]_][headcase_]:=Equation[headcase,cases,\[Alpha]];


(* ::Subsection::Closed:: *)
(*EndPackage*)


End[];
EndPackage[]
