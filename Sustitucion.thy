theory Sustitucion
  imports Main
begin

type_synonym var = string
type_synonym \<Sigma> = "var \<Rightarrow> int"

datatype intexp =
  Natconst nat
  | Var var
  | Neg intexp
  | Sum intexp intexp
  | Sub intexp intexp
  | Div intexp intexp
  | Mod intexp intexp
  | Prod intexp intexp

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

fun semcomm :: "comm \<Rightarrow> \<Sigma> \<Rightarrow> \<Sigma>" where
  "semcomm Skip \<sigma> = \<sigma>"
| "semcomm (Assign v e) \<sigma> = (\<lambda> x. if x = v then (semint e \<sigma>) else \<sigma> v)"
| "semcomm (Seq c0 c1) \<sigma> = semcomm c1 (semcomm c0 \<sigma>)"
| "semcomm (Cond b c0 c1) \<sigma> = 
    (if (sembool b \<sigma>) then (semcomm c0 \<sigma>) else (semcomm c1 \<sigma>))"
| "semcomm (Newvar v e c) \<sigma> =
    (\<lambda> \<sigma>'. (\<lambda> x. if x = v then \<sigma> v else \<sigma>' x))
    (semcomm c (\<lambda> x. if x = v then (semint e \<sigma>) else \<sigma> x))"

end
