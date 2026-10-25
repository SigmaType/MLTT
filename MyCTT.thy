theory MyCTT
  imports "~~/src/CTT/CTT"
begin

lemma ctx_ext_1:
  assumes premise: "A type"
  shows "\<And>x. x : A \<Longrightarrow> x : A"
proof -
  fix x
  assume x_A : "x : A"
  show "x : A" by (rule x_A)
qed

lemma ctx_xt_2:
  assumes A1_valid: "A1 type"
  assumes A2_valid: "\<And>x1. x1 : A1 \<Longrightarrow> A2(x1) type"
  shows "\<And>x1 x2. \<lbrakk> x1 : A1; x2 : A2(x1) \<rbrakk> \<Longrightarrow> x2 : A2(x1)"
proof -
  fix x1 x2
  assume x1 : "x1 : A1"
  assume x2 : "x2 : A2(x1)"
  show "x2 : A2(x1)" by (rule x2)
qed

lemma subst1_instance:
  assumes A_type: "A type"
  assumes a_A : "a : A"
  assumes b_B : "\<And>x. x : A \<Longrightarrow> b(x) : B(x)"
  shows "b(a) : B(a)"
proof -
  show "b(a) : B(a)" by (rule b_B [OF a_A])
qed

lemma elem_reflexivity:
  assumes A_type: "A type"
  assumes premise: "a : A"
  shows "a = a : A"
proof -
  show "a = a : A" by (rule refl_elem [OF premise])
qed

lemma elem_sym:
  assumes A_type: "A type"
  assumes a_eq_b: "a = b : A"
  shows "b = a : A"
proof -
  show "b = a : A" by (rule sym_elem [OF a_eq_b])
qed

lemma subst_elemL_example:
  assumes eq: "a = c : A"
    and fam: "\<And>z. z : A \<Longrightarrow> b(z) = d(z) : B(z)"
  shows "b(a) = d(c) : B(a)"
  by (rule subst_elemL) (rule eq, rule fam)

lemma subst_elemL_example1:
  assumes eq: "a = c : A"
    and fam: "\<And>z. z : A \<Longrightarrow> b(z) = d(z) : B(z)"
  shows "b(a) = d(c) : B(a)"
proof (rule subst_elemL [where a = a and c = c and d = d])
  show "a = c : A" by (rule eq)
next
  show "\<And>z. z : A \<Longrightarrow> b(z) = d(z) : B(z)" by (rule fam)
qed