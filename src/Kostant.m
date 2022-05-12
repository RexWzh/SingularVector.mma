(* ::Package:: *)

(* ::Subsection:: *)
(*Begin package*)


BeginPackage["Kostant`"];Print["Loading kostant functions..."];


(* ::Subsection:: *)
(*Main function*)


(* ::Subsubsection::Closed:: *)
(*\:904d\:5386\:7b97\:6cd5*)


(*traversal algorithm*)
(*\:6570\:636e\:7ed3\:6784*)
R;(*\:6839*)
S;(*\:89e3\:96c6*)
Diff;(*\:96c6\:5408\:4f5c\:5dee*)
(*ConsecutiveQ;(*\:5224\:516c\:5dee1*)*)

(* \:5224\:6b63\:6839 *)
(*PositiveRootAQ;
PositiveRootBQ;
PositiveRootCQ;
PositiveRootBCQ;
PositiveRootDQ;*)
PositiveRootQ;

(* \:751f\:6210\:6298\:53e0\:6839\:548c\:4e8f\:4e00\:6839 *)
(*FoldedRootOfTypeB;
FoldedRootOfTypeC;
FoldedRootOfTypeBC;
FoldedRootOfTypeD;
LackRoot;(*\:4e8f\:4e00\:6839\:6c47\:603b*)*)
FoldedRoot;(* \:6298\:53e0\:6839\:6c47\:603b *)


(*NextLevel;(*\:5e76\:6839\:6c42\:4e0b\:5c42\:89e3*)*)
KostantDecomposition;(*\:6c42\:6b63\:6839\:5206\:89e3\:ff0c\:6309\:957f\:5ea6\:5206\:5f00*)


(* ::Subsubsection::Closed:: *)
(*\:9012\:63a8\:7b97\:6cd5*)


(*recursive method*)
(*KostantSequenceGenerate;(*\:6570\:5217\:751f\:6210\:51fd\:6570*)
KostantSequenceOfTypeB;
KostantSequenceOfTypeC;
KostantSequenceOfTypeBC;
KostantSequenceOfTypeD;
KostantSequenceOfLackType;(*\:4e8f\:4e00\:578b\:6570\:5217*)
LackTypeC;(*C\:578b\:4e8f\:4e00\:6570\:5217\:ff0c\:4e09\:53c2*)*)
KostantSequence;(*\:6c47\:603b kostant \:6570\:5217*)


(*\:6c34\:7ba1\:ff0c\:7bb1\:5b50\:ff0c\:8fde\:63a5\:5668*)
(*TubesOO;(*\:9f50\:7aef\:6c34\:7ba1*)
TubesOX;(*\:975e\:9f50\:7aef\:6c34\:7ba1*)
CatenateBoxAndTube;(*\:8fde\:63a5\:5668*)
KostantBoxOfTypeC; (*C \:578b\:7bb1\:5b50*)*)
KostantBoxOfIsoType; (*\:8ff7\:5411\:7bb1\:5b50*)
FoldedDecomposition;(*\:6298\:53e0\:6839\:5206\:89e3*)


(* ::Subsubsection::Closed:: *)
(*\:6570\:636e\:5904\:7406*)


(*\:6570\:636e\:683c\:5f0f*)
(*Root2String;(*\:6839\:8f6c\:5b57\:7b26\:4e32*)
Roots2String;(*\:6839\:96c6\:8f6c\:5b57\:7b26\:4e32*)*)
Decomposition2String;(*\:6b63\:6839\:5206\:89e3\:8f6c\:5b57\:7b26\:4e32*)


(*\:77e9\:9635\:8fd0\:7b97*)
(*Delta2Matrix;(*\:6b63\:4ea4\:57fa\:8f6c\:77e9\:9635*)*)
MatchAnyQ;(*\:5339\:914d\:51fd\:6570*)
Root2Delta;(*\:6839\:8f6c\:6b63\:4ea4\:57fa*)
LieS;Lie;(*\:674e\:62ec\:53f7\:548c\:674e\:8d85\:62ec\:53f7*)

e;(*\:4ee3\:8868\:77e9\:9635\:ff0c\:4e5f\:7528\:4e8e\:6839\:548c\:6b63\:4ea4\:57fa \[Rule] \:77e9\:9635*)
f;h;(*\:6b63\:4ea4\:57fa\:6216\:6839 \[Rule] \:77e9\:9635*)
\[Delta];(*\:6b63\:4ea4\:57fa*)
m;


(*\:5355\:6839\:4f5c\:7528*)
(*AssociationAddTo;*)
KeyQ;(*\:5224\:65ad\:952e*)
B;(*\:5185\:79ef*)
ActOnBasis;(*\:5355\:6839\:4f5c\:7528\:51fd\:6570*)


(* ::Subsubsection:: *)
(*\:5bfc\:51fa\:7b49\:5f0f*)


a;(*\[Lambda]\:7cfb\:6570*)
(*\:5355\:6839\:4f5c\:7528\:5bfc\:51fa\:7b49\:5f0f*)
EquationsBySimpleRoot;
(*\:6c42k\:9636\:53d8\:91cf\:7684\:7b49\:5f0f\:4fe1\:606f*)
KostantEquationInfo;
(*\:6c42\:89e3\:7b49\:5f0f*)
SolveKostantEquations;
(*\:6392\:5e8f\:57fa\:5143*)
IsotropicBasis;
(*Combine;(*\:89e3\:96c6\:64cd\:4f5c\:ff1a\:5408\:5e76\:6839*)*)


(* ::Subsection::Closed:: *)
(*Begin Private*)


Begin["Private`"];


(* ::Subsection::Closed:: *)
(*traversal algorithm*)


(* ::Subsubsection::Closed:: *)
(*\:6570\:636e\:7ed3\:6784*)


(*\:89e3\:96c6*)
SetAttributes[S,{Protected,Orderless}];
(*\:6839\:96c6*)
SetAttributes[R,{Protected,Orderless}];
(*\:96c6\:5408\:4f5c\:5dee*)
Diff[l1_,l2_]:=Fold[DeleteCases[#1,#2,1,1]&,l1,List@@l2];
Unprotect[R,S];
R/:R[x__]-R[y__]:=Diff[R@x,R@y];
R/:R[x__]+R[y__]:=R[x]~Join~R[y];
S/:S[x__]-S[y__]:=Diff[S@x,S@y];
S/:S[x__]+S[y__]:=S[x]~Join~S[y];
Protect[R,S];


(* ::Subsubsection::Closed:: *)
(*\:5224\:522b\:6b63\:6839*)


(*\:5224\:65ad\:662f\:5426\:4e3a\:516c\:5dee1\:7684\:6570\:5217*)
ConsecutiveQ[list_]:=list===Range@@MinMax@list;
(* A \:578b\:6b63\:6839\:5224\:522b *)
PositiveRootAQ[root_R]:=Length@root!= 0&&Min@@root>0&&ConsecutiveQ[List@@root];


(* B \:578b\:6839\:5224\:522b *)
PositiveRootBQ[root_R]:=False/;Length@root==0||Min@@root<1;
PositiveRootBQ[root_R]:=Module[{max=Max@@root,subroot},
Which[
(* TypeA root*)
PositiveRootAQ@root,True,
(* Folded root *)
subroot=R@@Range@max;
!SubsetQ[root,subroot]||Count[root,max]==2,False,(*\:4e24\:7aef\:4e0d\:7b49*)
True,PositiveRootAQ[root-subroot]&&Count[root,1]==2]];


(*C \:578b\:6839\:5224\:522b\:ff0c\:8f93\:5165\:4e0d\:80fd\:4e3a\:8d1f*)
PositiveRootCQ[root_R]:=False/;Length@root==0||Min@@root<0;
PositiveRootCQ[root_R]:=Module[{max=Max@@root,subroot},
Which[
(* TypeA root*)
PositiveRootAQ@root,True,
(* Folded root *)
subroot=R@@Range[0,max];
!SubsetQ[root,subroot],False,
root===subroot,True,
True,PositiveRootAQ[root-subroot]&&Count[root,1]==2]];


(* BC \:578b\:6839\:5224\:522b *)
PositiveRootBCQ[root_R]:=False/;Length@root==0||Min@@root<1;
PositiveRootBCQ[root_R]:=Module[{subroot=R@@Range[Max@@root]},
Which[
(* TypeA root*)
PositiveRootAQ@root,True,
(* Folded root *)
!SubsetQ[root,subroot],False,
True,PositiveRootAQ[root-subroot]&&Count[root,1]==2]];


(* D \:578b\:6839\:5224\:522b\:ff0c\:5c3e\:5df4\:4e24\:6839\:8bb0\:4e3a 0\:ff0c-1 *)
PositiveRootDQ[root_R]:=False/;Length@root==0||Min@@root<-1;
PositiveRootDQ[root_R]:=Module[{max=Max@@root,subroot},
Which[
Length@root==1,True,
(* TypeA root*)
PositiveRootAQ@root,True,
(* Folded root *)
PositiveRootAQ[root-R[0,-1]]&&MemberQ[root,1],True,
!MemberQ[root,0]||!MemberQ[root,-1],False,
subroot=R@@Range[-1,max];
!SubsetQ[root,subroot]||Count[root,max]==2,False,(*\:4e24\:7aef\:4e0d\:7b49*)
True,PositiveRootAQ[root-subroot]&&Count[root,1]==2]];


(* ::Subsubsection::Closed:: *)
(*\:6298\:53e0\:6839*)


(* C \:578b\:6298\:53e0\:6839 *)
FoldedRootOfTypeC[left_,right_]:=(R@@Range[0,left])~Join~(R@@Range@right);
(* B \:578b\:6298\:53e0\:6839 *)
FoldedRootOfTypeB[left_,right_]:=(R@@Range@left)~Join~(R@@Range@right);
(* BC \:578b\:6298\:53e0\:6839 *)
FoldedRootOfTypeBC=FoldedRootOfTypeB;
(* D \:578b\:6298\:53e0\:6839 *)
FoldedRootOfTypeD[left_,right_]:=(R@@Range[-1,left])~Join~(R@@Range@right);


(* ::Subsubsection::Closed:: *)
(*\:4e8f\:4e00\:6839*)


(* C \:578b\:4e8f\:4e00\:6839 *)
LackRootOfTypeC[left_,right_,minus_]:=FoldedRootOfTypeC[left,right]-R[minus];
(* B \:578b\:4e8f\:4e00\:6839 *)
LackRootOfTypeB[left_,right_,minus_]:=FoldedRootOfTypeB[left,right]-R[minus];
(* BC \:578b\:4e8f\:4e00\:6839 *)
LackRootOfTypeBC=LackRootOfTypeB;
(* D \:578b\:4e8f\:4e00\:6839 *)
LackRootOfTypeD[left_,right_,minus_]:=FoldedRootOfTypeD[left,right]-R[minus];


(* ::Subsubsection::Closed:: *)
(*\:6b63\:6839\:5206\:89e3*)


SetAttributes[NextLevel,HoldRest];(*\:5141\:8bb8\:4fee\:6539\:8f93\:5165\:53c2\:6570*)
(* \:8f93\:5165\:4e00\:89e3\:ff0c\:6c42\:901a\:8fc7\[OpenCurlyDoubleQuote]\:5e76\:4e24\:6839\[CloseCurlyDoubleQuote]\:6784\:9020\:7684\:65b0\:89e3 *)
NextLevel[solution_S,RootQ_]:=Module[{combine,tworoots},
combine=Append[solution-#,(Join@@#)]&;
tworoots=Select[Subsets[solution,{2}],RootQ[Join@@#]&];
combine/@tworoots];
(* \:4ece\:65b0\:89e3\:4e2d\:7b5b\:9664\:91cd\:590d\:9879 *)
NextLevel[solution_S,hash_,RootQ_]:=Module[{seive,hashsol},
seive=If[MemberQ[hash,hashsol=Hash@#],False,AppendTo[hash,hashsol];True]&;
Select[NextLevel[solution,RootQ],seive]];


(*\:9010\:7ea7\:751f\:6210\:6b63\:6839\:5206\:89e3*)
KostantDecomposition[root_R,RootQ_]:=Module[{hash={},sol,next},
next=Function[level,NextLevel[#,hash,RootQ]&/@level//Flatten];
sol = R/@S@@root;(*\:521d\:59cb\:89e3*)
AppendTo[hash,Hash@sol];
NestWhileList[next,{sol},Length@#!=0&][[;;-2]]];


(* ::Subsubsection::Closed:: *)
(*\:51fd\:6570\:6536\:7eb3*)


(* \:6b63\:6839\:5224\:522b *)
PositiveRootQ=<|
"A"-> PositiveRootAQ,
"B"-> PositiveRootBQ,
"C"-> PositiveRootCQ,
"BC"-> PositiveRootCQ,
"D"-> PositiveRootDQ|>;


(* \:6298\:53e0\:6839 *)
FoldedRoot=<|
"B"-> FoldedRootOfTypeB,
"C"-> FoldedRootOfTypeC,
"BC"-> FoldedRootOfTypeBC,
"D"-> FoldedRootOfTypeD|>;


(*\:4e8f\:4e00\:6839*)
LackRoot=<|
"B"-> LackRootOfTypeB,
"C"-> LackRootOfTypeC,
"BC"-> LackRootOfTypeBC,
"D"-> LackRootOfTypeD|>;


(* ::Subsection::Closed:: *)
(*recursive algorithm*)


(* ::Subsubsection::Closed:: *)
(*\:6570\:5217\:751f\:6210\:51fd\:6570*)


(* Kostant \:6570\:5217 *)
KostantSequenceGenerate[]:=Module[{fun},
fun[l_,r_]:=fun[r,l]/;r>l>=0;
fun[l_,r_]:=2^(l-r-1) fun[r+1,r]/;l>r+1>0;
fun[l_,r_]:=fun[l,l]-fun[r,r]/;l==r+1>0;
fun[l_,r_]:=5(fun[r-1,r-1]-fun[r-2,r-2])/;l==r>=2;
fun]


(* ::Subsubsection::Closed:: *)
(*\:5404\:7c7b\:578b\:6570\:5217*)


(* \:5404\:7c7b Kostant \:6570\:5217 *)
KostantSequenceOfTypeC=KostantSequenceGenerate[];
KostantSequenceOfTypeC[0,0]=1;
KostantSequenceOfTypeC[1,1]=3;

KostantSequenceOfTypeD=KostantSequenceGenerate[];
KostantSequenceOfTypeD[0,0]=1;
KostantSequenceOfTypeD[1,1]=5;

KostantSequenceOfTypeB=KostantSequenceGenerate[];
(KostantSequenceOfTypeB[#[[1]],#[[2]]]=#[[3]])&/@{{0,0,1},{1,1,1},{1,0,1},{2,2,4}};

KostantSequenceOfTypeBC=KostantSequenceGenerate[];
(KostantSequenceOfTypeBC[#[[1]],#[[2]]]=#[[3]])&/@{{0,0,1},{1,1,2},{1,0,1},{2,2,6}};

(*\:4e8f\:4e00\:578b*)
KostantSequenceOfLackType=KostantSequenceGenerate[];
(KostantSequenceOfLackType[#[[1]],#[[2]]]=#[[3]])&/@{{0,0,1},{1,0,2},{1,1,2},{2,2,7}};
(*\:7aef\:70b9\:578b*)
KostantSequenceOfEndType=KostantSequenceGenerate[];
(KostantSequenceOfEndType[#[[1]],#[[2]]]=#[[3]])&/@{{0,0,1},{1,0,1},{1,1,1},{2,2,3}};

(*\:8ff7\:5411\:578b*)
KostantSequenceOfIsoType=KostantSequenceGenerate[];
(KostantSequenceOfIsoType[#[[1]],#[[2]]]=#[[3]])&/@{{0,0,1},{1,0,2},{1,1,2},{2,2,7}};


(*\:51fd\:6570\:6c47\:603b*)
KostantSequence=<|
"B"->KostantSequenceOfTypeB,
"C"->KostantSequenceOfTypeC,
"BC"->KostantSequenceOfTypeBC,
"D"->KostantSequenceOfTypeD,
"Lack"-> KostantSequenceOfLackType,
"End"->KostantSequenceOfEndType,
"Iso"-> KostantSequenceOfIsoType|>;


(* ::Subsubsection::Closed:: *)
(*C \:578b\:4e8f\:4e00\:6839*)


(*\:5e73\:51e1\:60c5\:5f62*)
LackTypeC[l_,0,0]:=2^(l-1)/;l>=1;
LackTypeC[0,0,0]=1;
LackTypeC[l_,r_,k_]:=0/;k>Max[l,r];
LackTypeC[l_,r_,k_]:=LackTypeC[r,l,k]/;r>l;
(*LackTypeC[l_,r_,k_]:=KostantSequence["C"][l,r-1]/;k\[Equal]r\[GreaterEqual]1;
LackTypeC[l_,r_,k_]:=KostantSequence["C"][l-1,r]/;k\[Equal]l\[GreaterEqual]1;*)
LackTypeC[l_,r_,k_]:=2^(l-k-1) KostantSequence["C"][k-1,r]/;l>k>r>=0;
(*\:8f6c\:5316\:4e3a kostant \:6570\:5217*)
LackTypeC[l_,r_,k_]:=KostantSequence["C"][k,k-1]KostantSequence["Lack"][l-k,r-k]/;0<k<=Min[l,r];
(*\:5904\:7406 k=0 \:60c5\:5f62*)
LackTypeC[l_,r_,0]:=KostantSequence["End"][l,r];
(*\:51fd\:6570 Curry \:5316*)
LackTypeC[k_][l_,r_]:=LackTypeC[l,r,k];


(* ::Subsubsection::Closed:: *)
(*\:9020\:6c34\:7ba1*)


(*\:4e24\:7aef\:9f50*)
TubesOO[roots_]:=Module[{o,x,res,recur},
(*\:53ea\:4e00\:6839\:ff0c\:8fd4\:56de\:4e00\:4e2a\:89e3*)
If[Length@roots==1,Return@{{roots,roots}}];
(*\:4e24\:5c3e\:7aef\:70b9*)
{o,x}={roots[[-1]],Join@@roots[[-2;;]]};
(*\:53cc\:5207*)
recur=TubesOO[roots[[;;-2]]]; (*\:4e0a\:5c42\:9012\:5f52\:7ed3\:679c*)
res={Append[#[[1]],o],Append[#[[2]],o]}&/@recur; (*\:8865\:88ab\:5207\:6839*)
(*\:53cc\:4e0d\:5207*)
recur=TubesOO[roots[[;;-3]]~Append~x]; 
res=res~Join~recur;
(*\:5355\:5207*)
recur=TubesOX[roots[[;;-3]],roots[[-2]],x];(*\:4f20\:9012\:7aef\:70b9\:4fe1\:606f*)
recur={Append[#[[1]],o],#[[2]]}&/@recur;(*\:8865\:88ab\:5207\:6839*)
res~Join~recur]/;Length@roots!=0;


(*\:4e24\:7aef\:4e0d\:9f50*)
TubesOX[roots_,u_,d_]:=Module[{o,x,res,recur},
(*\:5de6\:4fa7\:65e0\:6839\:ff0c\:8fd4\:56de\:4e00\:4e2a\:89e3*)
If[Length@roots==0,Return@{{{u},{d}}}];
(*\:53cc\:5207*)
recur=TubesOO[roots]; 
res={Append[#1,u],Append[#2,d]}&@@@recur; (*\:8865\:88ab\:5207\:6839*)
(*\:4e24\:5c3e\:7aef\:70b9*)
{o,x}={Join[roots[[-1]],u],Join[roots[[-1]],d]};
(*\:4e24\:7aef\:4e0d\:5207*)
recur=TubesOX[roots[[;;-2]],o,x]; 
res=res~Join~recur;
(*\:5355\:5207\:4e0a\:65b9*)
recur=TubesOX[roots[[;;-2]],roots[[-1]],x];
recur={Append[#1,u],#2}&@@@recur;(*\:8865\:88ab\:5207\:6839*)
res=res~Join~recur;
(*\:5355\:5207\:4e0b\:65b9*)
recur=TubesOX[roots[[;;-2]],o,roots[[-1]]];(*\:4f20\:9012\:7aef\:70b9\:4fe1\:606f*)
recur={#1,Append[#2,d]}&@@@recur;(*\:8865\:88ab\:5207\:6839*)
res~Join~recur]


(* ::Subsubsection::Closed:: *)
(*\:7bb1\:5b50\:548c\:8fde\:63a5\:5668*)


(*C\:578b\:7684\:5185\:90e8\:7ed3\:6784*)
KostantBoxOfTypeC[u_,d_]:=
{{Append[u,0],{},{d}},
{R[0],{u},{d}},
{Join[u,d,R[0]],{},{}}}/;u===d;
KostantBoxOfTypeC[u_,d_]:=
{{Append[u,0],{},{d}},
{Append[d,0],{u},{}},
{R[0],{u},{d}},
{Join[u,d,R[0]],{},{}}}/;!u===d;


KostantBoxOfIsoType[u_,d_]:=
{{R[0],{u},{d}},
{Append[u,0],{},{d}}}/;u===d;
KostantBoxOfIsoType[u_,d_]:=
{{R[0],{u},{d}},
{Append[u,0],{},{d}},
{Append[d,0],{u},{}}}/;!u===d;


(*\:63a5\:901a\:7ba1\:9053\:548c\:9ed1\:7bb1*)
CatenateBoxAndTube[tube_,box_]:=Module[{u,d,inner},
{u,d}={tube[[1,1]],tube[[2,1]]};
inner=box[u,d];
{#[[1]],Join[#[[2]],tube[[1,2;;]]],Join[#[[3]],tube[[2,2;;]]]}&/@inner];
CatenateBoxAndTube[box_][tube_]:=CatenateBoxAndTube[tube,box];
FoldedDecomposition[n_,box_]:=(CatenateBoxAndTube[box]/@TubesOO[R/@Range@n]//Flatten[#,1]&)/;n>0;


(* ::Subsection::Closed:: *)
(*data operate*)


(* ::Subsubsection::Closed:: *)
(*\:8f6c\:5b57\:7b26\:4e32*)


Root2String[root_R]:= StringJoin@Riffle[ToString/@List@@root,"-"];
Roots2String[roots_List]:=StringJoin@Riffle[Root2String/@roots,"|"];
Decomposition2String[roots_]:=StringJoin["<",Root2String@roots[[1]],"> ",Roots2String@roots[[2]]," & ",Roots2String@roots[[3]]];


(* ::Subsubsection::Closed:: *)
(*\:77e9\:9635\:8fd0\:7b97*)


Protect[e];
(*\:77e9\:9635\:8fd0\:7b97*)
Subscript/:Subscript[e,i_,j_]**Subscript[e,k_,l_]:=If[j===k,Subscript[e,i,l],0];
(*\:674e\:62ec\:53f7*)
Lie[x_,y_]:=x**y-y**x;
(*\:674e\:8d85\:62ec\:53f7*)
LieS[x_,y_,1]:=x**y+y**x;
LieS[x_,y_,0]:=x**y-y**x;
(*\:4e58\:6cd5\:7ebf\:6027\:6027*)
Unprotect[NonCommutativeMultiply];
DownValues[NonCommutativeMultiply]={
HoldPattern[x_**(y_+z_)]:>x**y+x**z,
HoldPattern[(y_+z_)**x_]:>y**x+z**x,
HoldPattern[x_**(-y_)]:>-x**y,
HoldPattern[(-x_)**y_]:>-x**y};
Protect[NonCommutativeMultiply];


(* ::Subsubsection::Closed:: *)
(*\:6570\:636e\:8f6c\:5316*)


(*\:5339\:914d\:51fd\:6570*)
MatchAnyQ[x_,patterns_]:=AnyTrue[patterns,MatchQ[x,#]&];
MatchAnyQ[patterns_][x_]:=MatchAnyQ[x,patterns];


(*\:6b63\:4ea4\:57fa\:8f6c\:77e9\:9635*)
Protect[f,m,\[Delta],h];(*sp\:53d8\:91cf\:6570\:76ee*)
(*\:5b9a\:4e49\:89c4\:5219\:ff0c\:6ce8\:610f\:89c4\:5219\:4e00\:4e0d\:80fd\:8986\:76d6\:540e\:8fb9\:7684*)
delta2matrules:={Subscript[\[Delta], i_]-Subscript[\[Delta], j_]:> Subscript[e, i,j]-Subscript[e, m+j,m+i]/;i j!=0,
Subscript[\[Delta], 0]-Subscript[\[Delta], j_]:> Subscript[e, -1,j]-Subscript[e, m+j,-2],
Subscript[\[Delta], i_]-Subscript[\[Delta], 0]:> -Subscript[e, i,-1]-Subscript[e, -2,m+i]};

(*\:6b63\:4ea4\:57fa\:8f6c\:77e9\:9635*)
Delta2Matrix[root_]:=(root/.delta2matrules)/;MatchQ[root,Subscript[\[Delta], i_]-Subscript[\[Delta], j_]];
(*\:7b80\:5199\:8bb0\:53f7*)
Subscript[e, \[Alpha]_]:=Delta2Matrix[\[Alpha]]/;MatchQ[\[Alpha],Subscript[\[Delta], i_]-Subscript[\[Delta], j_]];
Subscript[f, \[Alpha]_]:=Delta2Matrix[-\[Alpha]]/;MatchQ[\[Alpha],Subscript[\[Delta], i_]-Subscript[\[Delta], j_]];
Subscript[h, \[Alpha]_]:=If[MatchAnyQ[\[Alpha],{Subscript[\[Delta], i_]-Subscript[\[Delta], 0],Subscript[\[Delta], 0]-Subscript[\[Delta], j_]}],LieS[Subscript[e, \[Alpha]],Subscript[f, \[Alpha]],1],LieS[Subscript[e, \[Alpha]],Subscript[f, \[Alpha]],0]]/;MatchQ[\[Alpha],Subscript[\[Delta], i_]-Subscript[\[Delta], j_]];

(*\:6839\:8f6c\:6b63\:4ea4\:57fa\:548c\:77e9\:9635*)
Root2Delta[root_R]:=Total[List@@root/.{i_Integer:> Subscript[\[Delta], i]-Subscript[\[Delta], i+1]}];
Subscript[e, root_R]:=Subscript[e, Root2Delta@root];
Subscript[f, root_R]:=Subscript[f, Root2Delta@root];
Subscript[h, root_R]:=Subscript[h, Root2Delta@root];


(* ::Subsubsection::Closed:: *)
(*\:5355\:6839\:4f5c\:7528*)


(*\:5224\:65ad\:952e*)
KeyQ[assoc_,key_]:=MemberQ[Keys@assoc,key];
KeyQ[key_][assoc_]:=KeyQ[assoc,key];


(*\:7ed3\:5408\:5f8b\:5408\:5e76\:51fd\:6570*)
SetAttributes[AssociationAddTo,{HoldFirst}]
AssociationAddTo[assoc_,key_,value_]:=If[MemberQ[Keys[assoc],key],assoc[key]+=value,assoc[key]=value];


(*\:5b9a\:4e49\:5185\:79ef*)
Subscript/:Subscript[\[Delta], 0] Subscript[\[Delta], 0]:=-1;
Subscript/:Subscript[\[Delta], 0]^2:=-1;
Subscript/:Subscript[\[Delta], i_] Subscript[\[Delta], j_]:=If[i===j,1,0];
Subscript/:Subscript[\[Delta], i_]^2:=1;
B[\[Alpha]_,\[Beta]_]:=Simplify[\[Alpha] \[Beta]];


(*R[n]\:4f5c\:7528\:5728\:57fa\:5143\:4e0a\:ff0c\:57fa\:5143\:4e3a\:5c55\:5f00\:5f62\:5f0f*)
ActOnBasis[n_][roots_S]:=ActOnBasis[roots,n];
ActOnBasis[roots_S,n_]:=Module[{nearby,res=<||>,nearbyQ,LieSCoef,rightroot},
(*\:4e0d\:76f8\:7b49\:60c5\:5f62*)
(*\:5224\:65ad\:5728R[n]\:9644\:8fd1*)
nearbyQ[root_]:=!root===R[n]&&(First@root===n||Last@root===n);
(*\:6c42\:7cfb\:6570*)
LieSCoef[root_]:=LieS[Subscript[e, R[n]],Subscript[f, root],Boole[n==0&&MemberQ[root,0]]]/Subscript[f, root-R[n]]//Simplify;
(*\:4e0d\:76f8\:7b49\:60c5\:5f62*)
nearby=Select[roots,nearbyQ];(*\:88ab\:51cf\:6839*)
AssociationAddTo[res,(roots-S[#])+S[#-R[n],R[n]], LieSCoef@#]&/@nearby;

(*----\:76f8\:7b49\:60c5\:5f62-----*)
(*\:5c06\:4e34\:8fd1h\:53f3\:4fa7\:7684\:6839\:6c42\:548c*)
rightroot:=Module[{rule1,rule2,rightroots},
rule1=MemberQ[{n-1,n,n+1},First@#]||MemberQ[{n-1,n,n+1},Last@#]&;
rule2=!#===R[n]&&Min@@#>=n&;
rightroots=roots//Select[rule1]//Select[rule2];
List@@Root2Delta/@rightroots//Total];
Switch[Count[roots,R[n]],
1,AppendTo[res,roots-> B[Subscript[\[Delta], n]-Subscript[\[Delta], n+1],Subscript[a, n] Subscript[\[Delta], n]+Subscript[a, n+1] Subscript[\[Delta], n+1]-rightroot]],
2,AppendTo[res,roots->B[Subscript[\[Delta], n]-Subscript[\[Delta], n+1],-Subscript[\[Delta], n]+Subscript[\[Delta], n+1]+2(-2 Subscript[\[Delta], n+1]+Subscript[a, n] Subscript[\[Delta], n]+Subscript[a, n+1] Subscript[\[Delta], n+1])]]];
res];


(* ::Subsection:: *)
(*equation and solution*)


(* ::Subsubsection::Closed:: *)
(*\:5bfc\:51fa\:7b49\:5f0f*)


(*\:5355\:6839\:4f5c\:7528\:5bfc\:51fa\:7b49\:5f0f*)
EquationsBySimpleRoot[n_,tubelen_]:=Module[{basis,heads,equation,length,stringbasis,flattenbasis,relations},
basis=FoldedDecomposition[tubelen,KostantBoxOfIsoType];(*\:751f\:6210\:8ff7\:5411\:6298\:53e0\:6839*)
stringbasis=Decomposition2String/@basis;(*\:6298\:53e0\:6839\:8f6c\:5b57\:7b26\:4e32*)
flattenbasis=S@@@(Flatten/@basis);(*\:6298\:53e0\:6839\:5c55\:5e73*)
relations=ActOnBasis[n]/@flattenbasis;(*\:4f5c\:7528\:7ed3\:679c*)
length=Length@basis;
heads=Select[flattenbasis,MemberQ@R[n]];(*\:7b49\:5f0f\:5934\:90e8*)
(*\:51fd\:6570\:ff1a\:5bfc\:51fa\:7b49\:5f0f*)
equation[head_]:=Module[{pos},
pos=Select[Range@length,KeyQ[relations[[#]],head]&];(*\:542b\:952e\:503c\:7684\:4f4d\:7f6e*)
{relations[[#]][head],stringbasis[[#]]}&/@pos];(*\:7b49\:5f0f\:4e2d\:7684\:57fa\:5143\:548c\:7cfb\:6570*)
equation/@heads];


(*\:6c42k\:9636\:53d8\:91cf\:7684\:7b49\:5f0f\:4fe1\:606f*)
KostantEquationInfo[tubelen_]:=Join@@Table[EquationsBySimpleRoot[i-1,tubelen],{i,tubelen}]/;tubelen>0;


(* ::Subsubsection::Closed:: *)
(*\:6c42\:89e3\:7b49\:5f0f*)


Protect[x];
(*\:6c42\:89e3\:7b49\:5f0f*)
SolveKostantEquations[info_,stringbasis_]:=Module[{length,string2para,equation,equations,solution},
length=Length@stringbasis;(*\:57fa\:5143\:957f\:5ea6*)
string2para=stringbasis[[#]]->x[#]&/@Range@length;(*\:5b57\:7b26\:4e32\:8f6c\:53d8\:91cf*)
(*\:65b9\:7a0b\:4fe1\:606f\:8f6c Solve \:6c42\:89e3\:7684\:683c\:5f0f*)
equations=info/.string2para;
equation[eq_]:=(Times@@#&/@eq//Total)==0;
solution=Solve[Append[equation/@equations,x[1]==1],x/@Range@length];
{#,Sequence@@(#/.string2para/.solution)}&/@stringbasis//Simplify];
(*\:8f93\:5165\:7b80\:5316*)
SolveKostantEquations[tubelen_]:=
With[{info=KostantEquationInfo[tubelen],stringbasis=Decomposition2String/@FoldedDecomposition[tubelen,KostantBoxOfIsoType]},SolveKostantEquations[info,stringbasis]];


(* ::Subsubsection::Closed:: *)
(*\:9012\:63a8\:57fa\:5143*)


(*\:751f\:6210\:4e00\:4e2a\:51fd\:6570\:ff1a\:6839 a \:548c b \:90fd\:5b58\:5728\:65f6\:ff0c\:8fd4\:56de a b \:5408\:5e76\:7684\:7ed3\:679c\:ff0c\:5426\:5219\:8fd4\:56de Nothing*)
Combine[u_,v_]:=If[MemberQ[#,u]&&MemberQ[#,v],(#-S[u,v])+S[u+v],Nothing]&;
(*\:521d\:59cb\:5316\:ff0c\:7b2c0\:5c42*)
IsotropicBasis[n_]:=IsotropicBasis[n,0,{S@@(R/@Range[n])~Join~(R/@Range[0,n])}]; 
IsotropicBasis[n_,k_,uplevel_]:=Module[{act1,act2,single,double},
(*\:5df2\:5168\:90e8\:751f\:6210*)
If[k==n,Return@uplevel];
(*\:6dfb\:52a0\:4e0b\:5c42\:5355\:8fde*)
(*\:4f5c\:7528\:5728\:5217\:8868 level \:4e0a\:ff1a\:5c06 R[i] \:548c R[i+1...k+1] \:5408\:5e76*)
act1[level_,i_]:=Combine[R[i],R@@Range[i+1,k+1]]/@level;
single=FoldList[act1,uplevel,Range[k,0,-1]];
(*\:6dfb\:52a0\:4e0b\:5c42\:53cc\:8fde*)
(*\:4f5c\:7528\:5728\:591a\:91cd\:5217\:8868\:4e0a*)
act2[levels_,i_]:=act1[#,i]&/@levels[[2;;]];
double=FoldList[act2,single,Range[k,1,-1]];
IsotropicBasis[n,k+1,Flatten@double]]/;n>=0;


(* ::Subsection::Closed:: *)
(*End Package*)


End[];
EndPackage[];
