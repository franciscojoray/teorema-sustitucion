theory Sustitucion
  imports Main
begin

type_synonym var = string
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
| "semcomm (Assign v e) \<sigma> = Norm (\<lambda> x. if x = v then (semint e \<sigma>) else \<sigma> v)"
| "semcomm (Seq c0 c1) \<sigma> = star (semcomm c1) (semcomm c0 \<sigma>)"
| "semcomm (Cond b c0 c1) \<sigma> = 
    (if (sembool b \<sigma>) then (semcomm c0 \<sigma>) else (semcomm c1 \<sigma>))"
| "semcomm (Newvar v e c) \<sigma> =
    star (\<lambda> \<sigma>'. Norm (\<lambda> x. if x = v then \<sigma> v else \<sigma>' x))
    (semcomm c (\<lambda> x. if x = v then (semint e \<sigma>) else \<sigma> x))"

fun FA :: "comm \<Rightarrow> var set" where
  "FA Skip = {}"
| "FA (Assign v e) = {v}"
| "FA (Seq c0 c1) = FA c0 \<union> FA c1"
| "FA (Cond b c0 c1) = FA c0 \<union> FA c1"
| "FA (Newvar v e c) = FA c - {v}"

fun subcomm :: "comm \<Rightarrow> \<Delta> \<Rightarrow> comm" where
  "subcomm Skip _ = Skip"
| "subcomm (Assign v e) \<delta> = Assign (\<delta> v) (subint e \<delta>)"
| "subcomm (Seq c0 c1) \<delta> = Seq (subcomm c0 \<delta>) (subcomm c1 \<delta>)"
| "subcomm (Cond b c0 c1) \<delta> = Cond b (subcomm c0 \<delta>) (subcomm c1 \<delta>)"
(*| "subcomm (Newvar v e c) = ?"*)

end
