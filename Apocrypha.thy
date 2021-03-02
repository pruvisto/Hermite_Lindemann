lemma tan_square_eq_1D:
  assumes "tan (z :: complex) ^ 2 = 1"
  shows "(\<exists>n. z = of_real ((of_int n + 1 / 2) * pi / 2))"
proof -
  from assms have "sin z ^ 2 = cos z ^ 2" "cos z \<noteq> 0"
    by (auto simp: tan_def field_simps)
  note this(1)
  also have "cos z ^ 2 = 1 - sin z ^ 2"
    by (simp add: cos_squared_eq)
  finally have "1 - 2 * sin z ^ 2 = 0"
    by simp
  also have "1 - 2 * sin z ^ 2 = cos (2 * z)"
    by (simp add: cos_double_sin)
  finally have "cos (2 * z) = 0" .
  then obtain n where "2 * z = complex_of_real (real_of_int n * pi) + complex_of_real pi / 2"
    unfolding cos_eq_0 by blast
  also have "\<dots> = (of_int n + 1/2) * pi"
    by (simp add: ring_distribs)
  finally have z: "z = (of_int n + 1/2) * pi / 2"
    by (simp add: mult_ac)
  thus "(\<exists>n. z = of_real ((of_int n + 1 / 2) * pi / 2))" ..
qed

lemma tan_eq_1_iff: "tan (z :: complex) = 1 \<longleftrightarrow> (\<exists>n. z = (of_int n + 1 / 4) * of_real pi)"
proof
  assume "\<exists>n. z = (of_int n + 1 / 4) * of_real pi"
  then obtain n where n: "z = (of_int n + 1 / 4) * of_real pi"
    by auto
  have "z = of_real ((real_of_int n + 1/4) * pi)"
    by (simp add: n)
  also have "tan \<dots> = of_real (tan ((real_of_int n + 1/4) * pi))"
    by (subst tan_of_real) auto
  also have "(real_of_int n + 1/4) * pi = pi / 4 + real_of_int n * pi"
    by (simp add: algebra_simps)
  also have "tan \<dots> = tan (pi / 4)"
    by (rule tan_periodic_int)
  also have "\<dots> = 1"
    by (simp add: tan_45)
  finally show "tan z = 1"
    by simp
next
  assume "tan z = 1"
  then obtain n where z: "z = (of_int n + 1/2) * pi / 2"
    using tan_square_eq_1D[of z] by auto
  define z' where "z' = (real_of_int n + 1/2) * pi / 2"
  have z': "z = of_real z'"
    by (simp add: z z'_def)

  have "even n"
  proof (rule ccontr)
    assume "odd n"
    then obtain k where k: "n = 2 * k + 1"
      by (elim oddE)
    have "tan z = of_real (tan z')"
      by (simp add: z' tan_of_real)
    also have "tan z' = tan (z' - (k + 1) * pi)"
      using tan_periodic_int[of z' "-(k + 1)"] by (simp add: algebra_simps)
    also have "z' - (k + 1) * pi = -pi / 4"
      by (simp add: z'_def field_simps k)
    also have "tan \<dots> = -1"
      by (simp add: tan_45)
    finally show False using \<open>tan z = 1\<close>
      by simp
  qed
  then obtain k where k: "n = 2 * k"
    by (elim evenE)
  have "z = (of_int k + 1 / 4) * of_real pi"
    by (simp add: k z)
  thus "\<exists>n. z = (of_int n + 1 / 4) * of_real pi" ..
qed

lemma tan_eq_neg1_iff: "tan (z :: complex) = -1 \<longleftrightarrow> (\<exists>n. z = (of_int n - 1 / 4) * of_real pi)"
proof
  assume "\<exists>n. z = (of_int n - 1 / 4) * of_real pi"
  then obtain n where n: "z = (of_int n - 1 / 4) * of_real pi"
    by auto
  have "z = of_real ((real_of_int n - 1/4) * pi)"
    by (simp add: n)
  also have "tan \<dots> = of_real (tan ((real_of_int n - 1/4) * pi))"
    by (subst tan_of_real) auto
  also have "(real_of_int n - 1/4) * pi = -pi / 4 + real_of_int n * pi"
    by (simp add: algebra_simps)
  also have "tan \<dots> = tan (-pi / 4)"
    by (rule tan_periodic_int)
  also have "\<dots> = -1"
    by (simp add: tan_45)
  finally show "tan z = -1"
    by simp
next
  assume "tan z = -1"
  hence "tan (-z) = 1"
    by simp
  then obtain n where n: "-z = (of_int n + 1 / 4) * of_real pi"
    by (subst (asm) tan_eq_1_iff) blast
  hence "z = (of_int (-n) - 1 / 4) * of_real pi"
    unfolding of_int_minus by (subst (asm) minus_equation_iff) (simp add: algebra_simps)
  thus "\<exists>n. z = (of_int n - 1 / 4) * of_real pi" ..
qed

lift_definition poly_roots :: "'a :: idom poly \<Rightarrow> 'a multiset" is
  "\<lambda>p x. if p = 0 then 0 else order x p"
proof -
  fix p :: "'a poly"
  have "{x. (if p = 0 then 0 else Polynomial.order x p) > 0} =
          (if p = 0 then {} else {x. poly p x = 0})"
    by (auto simp: order_root)
  also have "finite \<dots>"
    by (auto intro: poly_roots_finite)
  finally show "(\<lambda>x. if p = 0 then 0 else Polynomial.order x p) \<in> multiset"
    unfolding multiset_def by simp
qed

lemma poly_roots_0 [simp]: "poly_roots 0 = {#}"
  by transfer auto

lemma count_poly_roots [simp]:
  "p \<noteq> 0 \<Longrightarrow> count (poly_roots p) x = order x p"
  by transfer simp

lemma set_mset_poly_roots: "p \<noteq> 0 \<Longrightarrow> set_mset (poly_roots p) = {x. poly p x = 0}"
  by (simp add: set_mset_def order_root)

lemma in_poly_roots_iff: "p \<noteq> 0 \<Longrightarrow> x \<in># poly_roots p \<longleftrightarrow> poly p x = 0"
  by (simp add: set_mset_poly_roots)

lemma poly_roots_const [simp]: "poly_roots [:c:] = {#}"
  by transfer' (auto split: if_splits simp: fun_eq_iff order_0I)

lemma poly_roots_1 [simp]: "poly_roots 1 = {#}"
  unfolding one_pCons poly_roots_const ..

lemma poly_roots_smult: "poly_roots (Polynomial.smult c p) = (if c = 0 then {#} else poly_roots p)"
proof (cases "p = 0")
  case False
  thus ?thesis
    by (intro multiset_eqI) (auto simp: order_smult)
qed auto

lemma poly_roots_smult' [simp]: "c \<noteq> 0 \<Longrightarrow> poly_roots (Polynomial.smult c p) = poly_roots p"
  by (subst poly_roots_smult) auto

lemma poly_roots_uminus [simp]: "poly_roots (-p) = poly_roots p"
  using poly_roots_smult'[of "-1" p] by (simp del: poly_roots_smult')

lemma poly_roots_monom:
  "poly_roots (Polynomial.monom c n) = (if c = 0 then {#} else replicate_mset n 0)"
  by (intro multiset_eqI) (auto intro: order_0I simp: poly_monom)

lemma poly_roots_monom' [simp]:
  "c \<noteq> 0 \<Longrightarrow> poly_roots (Polynomial.monom c n) = replicate_mset n 0"
  by (subst poly_roots_monom) auto

lemma poly_roots_mult:
  assumes "p \<noteq> 0" "q \<noteq> 0"
  shows   "poly_roots (p * q) = poly_roots p + poly_roots q"
  using assms by (intro multiset_eqI) (auto simp: order_mult)

lemma poly_roots_power [simp]: "poly_roots (p ^ n) = repeat_mset n (poly_roots p)"
proof (cases "p = 0")
  case True
  thus ?thesis by (cases n) auto
next
  case False
  thus ?thesis by (induction n) (auto simp: poly_roots_mult)
qed

lemma poly_roots_prod:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows   "poly_roots (prod f A) = (\<Sum>x\<in>A. poly_roots (f x))"
  using assms by (induction A rule: infinite_finite_induct) (auto simp: poly_roots_mult)

lemma poly_roots_rsquarefree:
  assumes "rsquarefree p"
  shows   "poly_roots p = mset_set {x. poly p x = 0}"
proof -
  from assms have [simp]: "p \<noteq> 0"
    by (auto simp: rsquarefree_def)
  show ?thesis
  proof (rule multiset_eqI)
    fix x
    find_consts name:poly_roots
    show "count (poly_roots p)
  using assms poly_roots_finite[of p]
  apply (intro multiset_eqI)
  apply (auto simp: count_mset_set)