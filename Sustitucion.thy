theory Sustitucion
  imports Main
begin

type_synonym var = nat
type_synonym \<Sigma> = "var \<Rightarrow> int"
type_synonym \<Delta> = "var \<Rightarrow> var"

datatype \<Sigma>b = Norm \<Sigma> | Bottom

datatype intexp =
  Natconst nat
  | Var var
  | Neg intexp
  | Sum intexp intexp
  | Sub intexp intexp
  | Div intexp intexp
  | Mod intexp intexp
  | Prod intexp intexp

fun FVint :: "intexp \<Rightarrow> var set" where
  "FVint (Natconst _) = {}"
| "FVint (Var v) = {v}"
| "FVint (Neg e) = FVint e"
| "FVint (Sum e0 e1) = FVint e0 \<union> FVint e1"
| "FVint (Sub e0 e1) = FVint e0 \<union> FVint e1"
| "FVint (Div e0 e1) = FVint e0 \<union> FVint e1"
| "FVint (Mod e0 e1) = FVint e0 \<union> FVint e1"
| "FVint (Prod e0 e1) = FVint e0 \<union> FVint e1"

fun subint :: "intexp \<Rightarrow> \<Delta> \<Rightarrow> intexp" where
  "subint (Natconst n) _ = Natconst n"
| "subint (Var v) \<delta> = Var (\<delta> v)"
| "subint (Neg e) \<delta> = Neg (subint e \<delta>)"
| "subint (Sum e0 e1) \<delta> = Sum (subint e0 \<delta>) (subint e1 \<delta>)"
| "subint (Sub e0 e1) \<delta> = Sub (subint e0 \<delta>) (subint e1 \<delta>)"
| "subint (Div e0 e1) \<delta> = Div (subint e0 \<delta>) (subint e1 \<delta>)"
| "subint (Mod e0 e1) \<delta> = Mod (subint e0 \<delta>) (subint e1 \<delta>)"
| "subint (Prod e0 e1) \<delta> = Prod (subint e0 \<delta>) (subint e1 \<delta>)"

fun semint :: "intexp \<Rightarrow> \<Sigma> \<Rightarrow> int" where
  "semint (Natconst n) \<sigma> = int n"
| "semint (Var var) \<sigma> = \<sigma> var"
| "semint (Neg e) \<sigma> = -(semint e \<sigma>)"
| "semint (Sum e0 e1) \<sigma> = (semint e0 \<sigma>) + (semint e1 \<sigma>)"
| "semint (Sub e0 e1) \<sigma> = (semint e0 \<sigma>) - (semint e1 \<sigma>)"
| "semint (Div e0 e1) \<sigma> = (semint e0 \<sigma>) div (semint e1 \<sigma>)"
| "semint (Mod e0 e1) \<sigma> = (semint e0 \<sigma>) mod (semint e1 \<sigma>)"
| "semint (Prod e0 e1) \<sigma> = (semint e0 \<sigma>) * (semint e1 \<sigma>)"

datatype boolexp =
  Boolconst bool
  | Eq intexp intexp
  | Lt intexp intexp
  | Gt intexp intexp
  | Lte intexp intexp
  | Gte intexp intexp
  | Disj boolexp boolexp
  | Conj boolexp boolexp
  | Neg boolexp

fun FVbool :: "boolexp \<Rightarrow> var set" where
  "FVbool (Boolconst _) = {}"
| "FVbool (Eq e0 e1) = FVint e0 \<union> FVint e1"
| "FVbool (Lt e0 e1) = FVint e0 \<union> FVint e1"
| "FVbool (Gt e0 e1) = FVint e0 \<union> FVint e1"
| "FVbool (Lte e0 e1) = FVint e0 \<union> FVint e1"
| "FVbool (Gte e0 e1) = FVint e0 \<union> FVint e1"
| "FVbool (Disj b0 b1) = FVbool b0 \<union> FVbool b1"
| "FVbool (Conj b0 b1) = FVbool b0 \<union> FVbool b1"
| "FVbool (Neg b) = FVbool b"

fun sembool :: "boolexp \<Rightarrow> \<Sigma> \<Rightarrow> bool" where
  "sembool (Boolconst b) \<sigma> = b"
| "sembool (Eq e0 e1) \<sigma> = ((semint e0 \<sigma>) = (semint e1 \<sigma>))"
| "sembool (Lt e0 e1) \<sigma> = ((semint e0 \<sigma>) < (semint e1 \<sigma>))"
| "sembool (Gt e0 e1) \<sigma> = ((semint e0 \<sigma>) > (semint e1 \<sigma>))"
| "sembool (Lte e0 e1) \<sigma> = ((semint e0 \<sigma>) \<le> (semint e1 \<sigma>))"
| "sembool (Gte e0 e1) \<sigma> = ((semint e0 \<sigma>) \<ge> (semint e1 \<sigma>))"
| "sembool (Disj b0 b1) \<sigma> = ((sembool b0 \<sigma>) \<or> (sembool b1 \<sigma>))"
| "sembool (Conj b0 b1) \<sigma> = ((sembool b0 \<sigma>) \<and> (sembool b1 \<sigma>))"
| "sembool (Neg b) \<sigma> = -(sembool b \<sigma>)"

datatype comm =
  Skip
  | Assign var intexp
  | Seq comm comm
  | Cond boolexp comm comm
  | Newvar var intexp comm
  (*| While boolexp comm*)

fun star :: "(\<Sigma> \<Rightarrow> \<Sigma>b) \<Rightarrow> (\<Sigma>b \<Rightarrow> \<Sigma>b)" where
  "star f (Norm \<sigma>) = f \<sigma>"
| "star f Bottom = Bottom"

fun semcomm :: "comm \<Rightarrow> \<Sigma> \<Rightarrow> \<Sigma>b" where
  "semcomm Skip \<sigma> = Norm \<sigma>"
| "semcomm (Assign v e) \<sigma> = Norm (\<lambda>x. if x=v then (semint e \<sigma>) else \<sigma> v)"
| "semcomm (Seq c0 c1) \<sigma> = star (semcomm c1) (semcomm c0 \<sigma>)"
| "semcomm (Cond b c0 c1) \<sigma> = 
    (if (sembool b \<sigma>) then (semcomm c0 \<sigma>) else (semcomm c1 \<sigma>))"
| "semcomm (Newvar v e c) \<sigma> =
    star (\<lambda> \<sigma>'. Norm (\<lambda>x. if x=v then \<sigma> v else \<sigma>' x))
    (semcomm c (\<lambda>x. if x=v then (semint e \<sigma>) else \<sigma> x))"

fun FVcomm :: "comm \<Rightarrow> var set" where
  "FVcomm Skip = {}"
| "FVcomm (Assign v e) = {v} \<union> FVint e"
| "FVcomm (Seq c0 c1) = FVcomm c0 \<union> FVcomm c1"
| "FVcomm (Cond b c0 c1) = FVbool b \<union> FVcomm c0 \<union> FVcomm c1"
| "FVcomm (Newvar v e c) = FVint e \<union> (FVcomm c - {v})"

fun FA :: "comm \<Rightarrow> var set" where
  "FA Skip = {}"
| "FA (Assign v e) = {v}"
| "FA (Seq c0 c1) = FA c0 \<union> FA c1"
| "FA (Cond b c0 c1) = FA c0 \<union> FA c1"
| "FA (Newvar v e c) = FA c - {v}"

definition get_fresh_var :: "var set => var" where
  "get_fresh_var s = Max s + 1"

fun subcomm :: "comm \<Rightarrow> \<Delta> \<Rightarrow> comm" where
  "subcomm Skip _ = Skip"
| "subcomm (Assign v e) \<delta> = Assign (\<delta> v) (subint e \<delta>)"
| "subcomm (Seq c0 c1) \<delta> = Seq (subcomm c0 \<delta>) (subcomm c1 \<delta>)"
| "subcomm (Cond b c0 c1) \<delta> = Cond b (subcomm c0 \<delta>) (subcomm c1 \<delta>)"
| "subcomm (Newvar v e c) \<delta> =
    (let vnew = get_fresh_var {\<delta> v | v. v \<in> (FVcomm c - {v})}
     in Newvar vnew (subint e \<delta>) (subcomm c (\<lambda>x. if x=v then vnew else \<delta> x)))"

lemma "FA (subcomm c \<delta>) = {\<delta> w | w. w \<in> FA c}"
  proof(induction c)
    case Skip
    then show ?case sorry
  next
    case (Assign x1 x2)
    then show ?case sorry
  next
    case (Seq c1 c2)
    then show ?case sorry
  next
    case (Cond x1 c1 c2)
    then show ?case sorry
  next
    case (Newvar x1 x2 c)
    then show ?case sorry
  qed

end
