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
    (let vnew = get_fresh_var {\<delta> w | w. w \<in> (FVcomm c - {v})}
     in Newvar vnew (subint e \<delta>) (subcomm c (\<lambda>x. if x=v then vnew else \<delta> x)))"

lemma finite_FVint: "finite (FVint e)" proof (induction e)
  case (Natconst x)
  then show ?case by simp
next
  case (Var x)
  then show ?case by simp
next
  case (Neg e)
  then show ?case by simp
next
  case (Sum e1 e2)
  then show ?case by simp
next
  case (Sub e1 e2)
  then show ?case by simp
next
  case (Div e1 e2)
  then show ?case by simp
next
  case (Mod e1 e2)
  then show ?case by simp
next
  case (Prod e1 e2)
  then show ?case by simp
qed

lemma finite_FVbool: "finite (FVbool b)" proof (induction b)
  case (Boolconst x)
  then show ?case by simp
next
  case (Eq e1 e2)
  have "finite (FVint e1)" by (simp add: finite_FVint)
  moreover have "finite (FVint e2)" by (simp add: finite_FVint)
  ultimately show ?case by simp
next
  case (Lt e1 e2)
  have "finite (FVint e1)" by (simp add: finite_FVint)
  moreover have "finite (FVint e2)" by (simp add: finite_FVint)
  ultimately show ?case by simp
next
  case (Gt e1 e2)
  have "finite (FVint e1)" by (simp add: finite_FVint)
  moreover have "finite (FVint e2)" by (simp add: finite_FVint)
  ultimately show ?case by simp
next
  case (Lte e1 e2)
  have "finite (FVint e1)" by (simp add: finite_FVint)
  moreover have "finite (FVint e2)" by (simp add: finite_FVint)
  ultimately show ?case by simp
next
  case (Gte e1 e2)
  have "finite (FVint e1)" by (simp add: finite_FVint)
  moreover have "finite (FVint e2)" by (simp add: finite_FVint)
  ultimately show ?case by simp
next
  case (Disj b1 b2)
  then show ?case by simp
next
  case (Conj b1 b2)
  then show ?case by simp
next
  case (Neg b)
  then show ?case by simp
qed

lemma finite_FVcomm: "finite (FVcomm c)" proof (induction c)
  case Skip
  then show ?case by simp
next
  case (Assign v e)
  have "finite (FVint e)" by (simp add: finite_FVint)
  then show ?case by simp
next
  case (Seq c1 c2)
  then show ?case by simp
next
  case (Cond b c1 c2)
  have "finite (FVbool b)" by (simp add: finite_FVbool)
  moreover have "finite (FVcomm c1)" by (simp add: Cond)
  moreover have "finite (FVcomm c2)" by (simp add: Cond)
  ultimately show ?case by simp
next
  case (Newvar v e c0)
  have "finite (FVint e)" by (simp add: finite_FVint)
  moreover have "finite (FVcomm c0)" by (simp add: Newvar)
  ultimately show ?case by simp
qed

lemma subsets1: "A \<subseteq> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow> A \<subseteq> C \<union> D \<and> B \<subseteq> C \<union> D" by blast
lemma subsets2: "A \<subseteq> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow> A \<subseteq> E \<union> C \<union> D \<and> B \<subseteq> E \<union> C \<union> D" by blast
lemma subsets3: "A \<subseteq> C \<Longrightarrow> A - {x} \<subseteq> B \<union> (C - {x})" by blast
lemma FA_sub_FV: "FA c \<subseteq> FVcomm c"
proof (induction c)
  case Skip
  then show ?case by simp
next
  case (Assign x1 x2)
  then show ?case by simp
next
  case (Seq c1 c2)
  then show ?case by (simp add: subsets1)
next
  case (Cond x1 c1 c2)
  then show ?case by (simp add: subsets2)
next
  case (Newvar v e c)
  then show ?case by (simp add: subsets3)
qed

theorem SubstExp:
  fixes p :: intexp
  fixes \<delta> :: \<Delta>
  fixes \<sigma> :: \<Sigma>
  fixes \<sigma>':: \<Sigma>
  assumes s: "w \<in> FVint p \<longrightarrow> \<sigma> (\<delta> w) = \<sigma>' w"
  shows "semint (subint p \<delta>) \<sigma> = semint p \<sigma>'"
  sorry

theorem
  "(\<forall>w w'. {w, w'} \<subseteq> FVcomm c \<and> w \<noteq> w' \<longrightarrow> \<delta> w \<noteq> \<delta> w') \<and>
   (\<forall>w. w \<in> FVcomm c \<longrightarrow> \<sigma>'(\<delta> w) = \<sigma> w)
   \<Longrightarrow> ((semcomm c \<sigma> = Bottom \<and> semcomm (subcomm c \<delta>) \<sigma>' = Bottom) \<or>
       (\<exists> \<sigma>1 \<sigma>2. semcomm c \<sigma> = Norm \<sigma>1 \<and> semcomm (subcomm c \<delta>) \<sigma>' = Norm \<sigma>2
       \<and> (w \<in> FVcomm c \<longrightarrow> \<sigma>1 w = \<sigma>2 (\<delta> w))))"
proof (induction c arbitrary: \<delta> \<sigma> \<sigma>')
  case Skip
  then show ?case by simp
next
  case (Assign v e)
  have int_prem: "w \<in> FVint e \<longrightarrow> \<sigma>' (\<delta> w) = \<sigma> w" proof
    assume "w \<in> FVint e"
    hence "w \<in> FVcomm (Assign v e)" by simp
    with Assign.prems show "\<sigma>' (\<delta> w) = \<sigma> w" by blast
  qed
  have 1: "let \<sigma>1 = (\<lambda>x. if x = v then (semint e \<sigma>) else \<sigma> v) in semcomm (Assign v e) \<sigma> = Norm \<sigma>1" by simp
  have 2: "let \<sigma>2 = (\<lambda>x. if x = \<delta> v then (semint (subint e \<delta>) \<sigma>') else \<sigma>' (\<delta> v)) in 
    semcomm (subcomm (Assign v e) \<delta>) \<sigma>' = Norm \<sigma>2" by simp
  have 3: "w \<in> FVcomm (Assign v e) \<longrightarrow> (let \<sigma>1 = (\<lambda>x. if x = v then (semint e \<sigma>) else \<sigma> v) in
       let \<sigma>2 = (\<lambda>x. if x = \<delta> v then (semint (subint e \<delta>) \<sigma>') else \<sigma>' (\<delta> v)) in \<sigma>1 w = \<sigma>2 (\<delta> w))" proof
    assume winfv: "w \<in> FVcomm (Assign v e)"
    hence "w = v \<or> w \<noteq> v" by simp
    hence "let \<sigma>1 = (\<lambda>x. if x = v then (semint e \<sigma>) else \<sigma> v) in
       let \<sigma>2 = (\<lambda>x. if x = \<delta> v then (semint (subint e \<delta>) \<sigma>') else \<sigma>' (\<delta> v)) in
       \<sigma>1 w = \<sigma>2 (\<delta> w)" proof
      assume s: "w = v"
      hence "let \<sigma>1 = (\<lambda>x. if x = v then (semint e \<sigma>) else \<sigma> v) in \<sigma>1 w = (semint e \<sigma>)" by simp
      moreover have "let \<sigma>2 = (\<lambda>x. if x = \<delta> v then (semint (subint e \<delta>) \<sigma>') else \<sigma>' (\<delta> v)) in
         \<sigma>2 (\<delta> w) = (semint (subint e \<delta>) \<sigma>')" by (simp add :s)
      moreover from int_prem have "semint e \<sigma> = (semint (subint e \<delta>) \<sigma>')" by (simp add: SubstExp)
      ultimately show ?thesis by simp
    next
      assume s: "w \<noteq> v"
      hence sigma1:"let \<sigma>1 = (\<lambda>x. if x = v then (semint e \<sigma>) else \<sigma> v) in \<sigma>1 w = \<sigma> v" by simp
      from winfv have "{w, v} \<subseteq> FVcomm (Assign v e)" by simp
      with s have "{w, v} \<subseteq> FVcomm (Assign v e) \<and> w \<noteq> v" by simp
      with Assign.prems(1) have wnotv: "\<delta> w \<noteq> \<delta> v" by (simp add:s)
      hence sigma2: "let \<sigma>2 = (\<lambda>x. if x = \<delta> v then (semint (subint e \<delta>) \<sigma>') else \<sigma>' (\<delta> v)) in
         \<sigma>2 (\<delta> w) = \<sigma>' (\<delta> v)" by (simp add: s)
      from Assign.prems have "\<sigma> v = \<sigma>' (\<delta> v)" by simp
      with sigma1 sigma2 show ?thesis by simp
    qed
    thus "(let \<sigma>1 = (\<lambda>x. if x = v then (semint e \<sigma>) else \<sigma> v) in
       let \<sigma>2 = (\<lambda>x. if x = \<delta> v then (semint (subint e \<delta>) \<sigma>') else \<sigma>' (\<delta> v)) in \<sigma>1 w = \<sigma>2 (\<delta> w))" by simp
  qed
  hence "\<exists> \<sigma>1 \<sigma>2. let \<sigma>1 = (\<lambda>x. if x = v then (semint e \<sigma>) else \<sigma> v) in
         let \<sigma>2 = (\<lambda>x. if x = \<delta> v then (semint (subint e \<delta>) \<sigma>') else \<sigma>' (\<delta> v)) in
         semcomm (Assign v e) \<sigma> = Norm \<sigma>1 \<and> semcomm (subcomm (Assign v e) \<delta>) \<sigma>' = Norm \<sigma>2 \<and>
         (w \<in> FVcomm (Assign v e) \<longrightarrow> \<sigma>1 w = \<sigma>2 (\<delta> w))" by simp
  thus ?case by simp
next
  case (Seq c0 c1)
  hence "semcomm c0 \<sigma> = Bottom \<or> semcomm c0 \<sigma> \<noteq> Bottom" by simp
  then show ?case proof
    assume s: "semcomm c0 \<sigma> = Bottom"
    from Seq have "(semcomm c0 \<sigma> = Bottom \<and> semcomm (subcomm c0 \<delta>) \<sigma>' = Bottom) \<or>
       (\<exists> \<sigma>1 \<sigma>2. semcomm c0 \<sigma> = Norm \<sigma>1 \<and> semcomm (subcomm c0 \<delta>) \<sigma>' = Norm \<sigma>2
       \<and> (w \<in> FVcomm c0 \<longrightarrow> \<sigma>1 w = \<sigma>2 (\<delta> w)))" by simp
    with s have "(semcomm (subcomm c0 \<delta>) \<sigma>' = Bottom)" by simp
    hence "semcomm (subcomm (Seq c0 c1) \<delta>) \<sigma>' = Bottom" by simp
    moreover from s have "semcomm (Seq c0 c1) \<sigma> = Bottom" by simp
    ultimately show ?case by simp
  next
    assume s: "semcomm c0 \<sigma> \<noteq> Bottom"
    with  \<Sigma>b.exhaust have  "(\<exists>\<sigma>0. semcomm c0 \<sigma> = Norm \<sigma>0)" by (meson \<Sigma>b.exhaust)
    then obtain \<sigma>0 where "semcomm c0 \<sigma> = Norm \<sigma>0" by blast
    from Seq have "(semcomm c0 \<sigma> = Bottom \<and> semcomm (subcomm c0 \<delta>) \<sigma>' = Bottom) \<or>
       (\<exists> \<sigma>1 \<sigma>2. semcomm c0 \<sigma> = Norm \<sigma>1 \<and> semcomm (subcomm c0 \<delta>) \<sigma>' = Norm \<sigma>2
       \<and> (w \<in> FVcomm c0 \<longrightarrow> \<sigma>1 w = \<sigma>2 (\<delta> w)))" by simp
    with s have "\<exists> \<sigma>1 \<sigma>2. semcomm c0 \<sigma> = Norm \<sigma>1 \<and> semcomm (subcomm c0 \<delta>) \<sigma>' = Norm \<sigma>2
       \<and> (w \<in> FVcomm c0 \<longrightarrow> \<sigma>1 w = \<sigma>2 (\<delta> w))" by simp
    hence "\<exists>\<sigma>2. semcomm (subcomm c0 \<delta>) \<sigma>' = Norm \<sigma>2" by blast
    then obtain \<sigma>0' where "semcomm (subcomm c0 \<delta>) \<sigma>' = Norm \<sigma>0'" by blast
    have "\<forall>w. w \<in> FVcomm c1 \<longrightarrow> \<sigma>'(\<delta> w) = \<sigma> w" proof
      fix w
      show "w \<in> FVcomm c1 \<longrightarrow> \<sigma>'(\<delta> w) = \<sigma> w" proof
        assume "w \<in> FVcomm c1"
        hence "w \<in> FVcomm c0 \<or> w \<notin> FVcomm c0" by simp
        thus "\<sigma>'(\<delta> w) = \<sigma> w" proof
          assume s: "w \<in> FVcomm c0"
          from Seq have "\<sigma>'(\<delta> w) = \<sigma> w" by (simp add: s)
          thus ?thesis by simp
        next
          assume "w \<notin> FVcomm c0"
          thus ?thesis sorry
        qed
      qed
    qed
    then show ?case sorry
next
  case (Cond x1 c1 c2)
  then show ?case sorry
next
  case (Newvar x1 x2 c)
  then show ?case sorry
qed

lemma subsets4: "A \<subseteq> B \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B" by blast
lemma FA_in_FV: "x \<in> FA c \<longrightarrow> x \<in> FVcomm c"
proof
  assume "x \<in> FA c"
  moreover have "FA c \<subseteq> FVcomm c" by (simp add: FA_sub_FV)
  ultimately show "x \<in> FVcomm c" by (simp add: subsets4)
qed

lemma union_or: "{\<delta> x | x. x \<in> A} \<union> {\<delta> x | x. x \<in> B} = {\<delta> x | x. x \<in> A \<or> x \<in> B}" by blast
lemma "FA (subcomm c \<delta>) = {\<delta> w | w. w \<in> FA c}"
proof(induction c arbitrary: \<delta>)
  case Skip
  then show ?case by simp
next
  case (Assign x1 x2)
  then show ?case by simp
next
  case (Seq c1 c2)
  with union_or show ?case by simp
next
  case (Cond x1 c1 c2)
  with union_or show ?case by simp
next
  case (Newvar v e c0)
  show ?case (is "?L = ?R")
  proof
    show "?L \<subseteq> ?R"
    proof
      fix u
      assume h: "u \<in> ?L"
      hence "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in
             u \<in> FA(subcomm c0 \<delta>') \<and> u \<noteq> vnew" by (simp add: get_fresh_var_def)
      hence 0: "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in
             u \<in> {\<delta>' w | w. w \<in> FA c0} \<and> u \<noteq> vnew" by (simp add: get_fresh_var_def Newvar)
      hence  "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in
             \<exists>x. u = \<delta>' x \<and> x \<in> (FA c0) \<and> u \<noteq> vnew" by (simp add: get_fresh_var_def)
      hence  "\<exists>x. let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in
             u = \<delta>' x \<and> x \<in> (FA c0) \<and> u \<noteq> vnew" by (simp add: get_fresh_var_def)
      then obtain x where p: "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in
             u = \<delta>' x \<and> x \<in> (FA c0) \<and> u \<noteq> vnew" by blast
      from p have 1: "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in
             \<delta>' x = u" by (simp add: get_fresh_var_def)
      from p have "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             u \<noteq> vnew" by (simp add: get_fresh_var_def)
      hence 2: "\<not>(let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             u = vnew)" by simp
      have 3: "\<not>(x = v)" proof
        assume "x = v"
        hence "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
               let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in \<delta>' x = \<delta>' v" by simp
        hence "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
               let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in \<delta>' x = vnew" by simp
        with 1 have "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
               let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in u = vnew" by simp
        with 2 show "False" by simp
      qed
      from p 3 have "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in
             u = \<delta>' x \<and> x \<in> (FA c0) \<and> x \<noteq> v" by simp
      hence "u = \<delta> x \<and> x \<in> (FA c0) \<and> x \<noteq> v" by simp
      hence "\<exists>x. u = \<delta> x \<and> x \<in> (FA c0) \<and> x \<noteq> v" by blast
      hence "u \<in> {\<delta> w | w. w \<in> FA c0 - {v}}" by simp
      thus "u \<in> ?R" by simp
    qed
  next
    show "?R \<subseteq> ?L" proof
      fix u
      assume "u \<in> ?R"
      hence "\<exists> w. u = \<delta> w \<and> w \<in> FA c0 - {v}" by simp
      then obtain w where p: "u = \<delta> w \<and> w \<in> FA c0 - {v}" by blast
      hence 0: "u = \<delta> w \<and> w \<in> FA c0 \<and> w \<noteq> v" by simp
      hence "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in \<delta> w = \<delta>' w" by simp
      with 0 have "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in u = \<delta>' w \<and> w \<in> FA c0 \<and> w \<noteq> v" by simp
      hence 1: "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in u = \<delta>' w \<and> w \<in> FA c0" by simp
      have finite: "finite {\<delta> w | w. w \<in> FVcomm c0 - {v}}" by (simp add: finite_FVcomm)
      have u_not_vnew: "\<not>(let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in u = vnew)" proof
        assume "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in u = vnew"
        with p have 2: "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}}
          in vnew = \<delta> w \<and> w \<in> FA c0 - {v}" by simp
        hence "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}}
          in vnew = \<delta> w \<and> w \<in> FVcomm c0 - {v}" by (simp add: FA_in_FV)
        hence "\<exists> w. let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}}
          in vnew = \<delta> w \<and> w \<in> FVcomm c0 - {v}" by blast
        hence "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}}
          in vnew \<in> {\<delta> w | w. w \<in> FVcomm c0 - {v}}" by simp
        hence "(get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}}) \<in> {\<delta> w | w. w \<in> FVcomm c0 - {v}}" by simp
        hence "(Suc (Max {\<delta> w | w. w \<in> FVcomm c0 - {v}})) \<in> {\<delta> w | w. w \<in> FVcomm c0 - {v}}" by (simp add: get_fresh_var_def)
        with finite have "let A = {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
          finite {\<delta> w | w. w \<in> FVcomm c0 - {v}} \<and>
          (Suc (Max {\<delta> w | w. w \<in> FVcomm c0 - {v}})) \<in> {\<delta> w | w. w \<in> FVcomm c0 - {v}}" by simp
        hence "(Suc (Max {\<delta> w | w. w \<in> FVcomm c0 - {v}})) \<le> Max {\<delta> w | w. w \<in> FVcomm c0 - {v}}" by simp
        thus "False" by simp
      qed
      from 1 have "\<exists> w. let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in u = \<delta>' w \<and> w \<in> FA c0" by blast
      hence "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in \<exists> w. u = \<delta>' w \<and> w \<in> FA c0" by simp
      hence "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in u \<in> {\<delta>' w | w. w \<in> FA c0}" by simp
      hence "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in u \<in> FA (subcomm c0 \<delta>')" by (simp add: Newvar)
      with u_not_vnew have "let vnew = get_fresh_var {\<delta> w | w. w \<in> FVcomm c0 - {v}} in
             let \<delta>' = (\<lambda>x. if x=v then vnew else \<delta> x) in u \<in> FA (subcomm c0 \<delta>') - {vnew}" by simp
      value "?L"
      thus "u \<in> ?L" by (simp add: get_fresh_var_def)
  qed
qed
