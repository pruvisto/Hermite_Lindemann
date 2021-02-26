(*
  File:     Hermite_Lindemann.thy
  Author:   Manuel Eberl, TU München
*)
section \<open>The Hermite--Lindemann Transcendence Theorem\<close>
theory Hermite_Lindemann
imports 
  Pi_Transcendental.Pi_Transcendental
  Algebraic_Numbers.Algebraic_Numbers
  "Power_Sum_Polynomials.Power_Sum_Polynomials_Library"
(*"Polynomial_Factorization.Square_Free_Factorization"*)
begin

subsection \<open>Auxiliary facts about univariate polynomials\<close>

lemma irreducible_imp_squarefree:
  assumes "irreducible p"
  shows   "squarefree p"
proof (rule squarefreeI)
  fix q assume "q ^ 2 dvd p"
  then obtain r where qr: "p = q ^ 2 * r"
    by (elim dvdE)
  have "q dvd 1 \<or> q * r dvd 1"
    by (intro irreducibleD[OF assms]) (use qr in \<open>simp_all add: power2_eq_square mult_ac\<close>)
  thus "q dvd 1"
    by (meson dvd_mult_left)
qed

lemma squarefree_imp_rsquarefree:
  fixes p :: "'a :: idom poly"
  assumes "squarefree p"
  shows   "rsquarefree p"
  unfolding rsquarefree_def
proof (intro conjI allI)
  fix x :: 'a
  have "order x p < 2"
  proof (rule ccontr)
    assume "\<not>(order x p < 2)"
    hence "[:-x, 1:] ^ 2 dvd p"
      by (subst order_divides) auto
    from assms and this have "[:-x, 1:] dvd 1"
      by (rule squarefreeD)
    hence "Polynomial.degree [:-x, 1:] \<le> Polynomial.degree (1 :: 'a poly)"
      by (rule dvd_imp_degree_le) auto
    thus False by simp
  qed
  thus "order x p = 0 \<or> order x p = 1"
    by linarith
qed (use assms in auto)

lemma squarefree_imp_coprime_pderiv:
  fixes p :: "'a :: {factorial_ring_gcd,semiring_gcd_mult_normalize,semiring_char_0} poly"
  assumes "squarefree p" and "content p = 1"
  shows   "Rings.coprime p (pderiv p)"
proof (rule coprimeI_primes)
  fix d assume d: "prime d" "d dvd p" "d dvd pderiv p"
  show False
  proof (cases "Polynomial.degree d = 0")
    case deg: False
    obtain q where dq: "p = d * q"
      using d by (elim dvdE)
    have \<open>d dvd q * pderiv d\<close>
      using d by (simp add: dq pderiv_mult dvd_add_right_iff)
    moreover have "\<not>d dvd pderiv d"
    proof
      assume "d dvd pderiv d"
      hence "Polynomial.degree d \<le> Polynomial.degree (pderiv d)"
        using d deg by (intro dvd_imp_degree_le) (auto simp: pderiv_eq_0_iff)
      hence "Polynomial.degree d = 0"
        by (subst (asm) degree_pderiv) auto
      thus False using deg by contradiction
    qed
    ultimately have "d dvd q"
      using d(1) by (simp add: prime_dvd_mult_iff)
    hence "d ^ 2 dvd p"
      by (auto simp: dq power2_eq_square)
    from assms(1) and this have "is_unit d"
      by (rule squarefreeD)
    thus False using \<open>prime d\<close> by auto
  next
    case True
    then obtain d' where [simp]: "d = [:d':]"
      by (elim degree_eq_zeroE)
    from d have "d' dvd content p"
      by (simp add: const_poly_dvd_iff_dvd_content)
    with assms and prime_imp_prime_elem[OF \<open>prime d\<close>] show False
      by auto
  qed
qed (use assms in auto)

lemma irreducible_imp_coprime_pderiv:
  fixes p :: "'a :: {idom_divide,semiring_char_0} poly"
  assumes "irreducible p" "Polynomial.degree p \<noteq> 0"
  shows   "Rings.coprime p (pderiv p)"
proof (rule Rings.coprimeI)
  fix d assume d: "d dvd p" "d dvd pderiv p"
  obtain q where dq: "p = d * q"
    using d by (elim dvdE)
  have "is_unit d \<or> is_unit q"
    using assms dq by (auto simp: irreducible_def)
  thus "is_unit d"
  proof
    assume unit: "is_unit q"
    with d have "p dvd pderiv p"
      using algebraic_semidom_class.mult_unit_dvd_iff dq by blast
    hence "Polynomial.degree p = 0"
      by (meson not_dvd_pderiv)
    with assms(2) show ?thesis by contradiction
  qed
qed

lemma poly_gcd_eq_0I:
  assumes "poly p x = 0" "poly q x = 0"
  shows   "poly (gcd p q) x = 0"
  using assms by (simp add: poly_eq_0_iff_dvd)

lemma poly_eq_0_coprime:
  assumes "Rings.coprime p q" "p \<noteq> 0" "q \<noteq> 0"
  shows   "poly p x \<noteq> 0 \<or> poly q x \<noteq> 0"
proof -
  have False if "poly p x = 0" "poly q x = 0"
  proof -
    have "[:-x, 1:] dvd p" "[:-x, 1:] dvd q"
      using that by (simp_all add: poly_eq_0_iff_dvd)
    hence "[:-x, 1:] dvd 1"
      using \<open>Rings.coprime p q\<close> by (meson not_coprimeI)
    thus False
      by (simp add: is_unit_poly_iff)
  qed
  thus ?thesis
    by blast
qed

lemma coprime_of_int_polyI:
  assumes "Rings.coprime p q"
  shows   "Rings.coprime (of_int_poly p) (of_int_poly q :: 'a :: {field_char_0,field_gcd} poly)"
  using assms gcd_of_int_poly[of p q, where ?'a = 'a] unfolding coprime_iff_gcd_eq_1 by simp

lemma irreducible_imp_rsquarefree_of_int_poly:
  fixes p :: "int poly"
  assumes "irreducible p" and "Polynomial.degree p > 0"
  shows   "rsquarefree (of_int_poly p :: 'a :: {field_gcd, field_char_0} poly)"
proof -
  {
    fix x :: 'a
    assume x: "poly (of_int_poly p) x = 0" "poly (pderiv (of_int_poly p)) x = 0"
    define d where "d = gcd (of_int_poly p) (pderiv (of_int_poly p) :: 'a poly)"
    have "poly d x = 0"
      using x unfolding d_def by (intro poly_gcd_eq_0I) auto
    moreover have "d \<noteq> 0"
      using assms by (auto simp: d_def)
    ultimately have "0 < Polynomial.degree d"
      by (intro Nat.gr0I) (auto elim!: degree_eq_zeroE)
    also have "Polynomial.degree d = Polynomial.degree (gcd p (pderiv p))"
      unfolding d_def of_int_hom.map_poly_pderiv[symmetric] gcd_of_int_poly by simp
    finally have deg: "\<dots> > 0" .
  
    have "gcd p (pderiv p) dvd p"
      by auto
    from irreducibleD'[OF assms(1) this] and deg have "p dvd gcd p (pderiv p)"
      by auto
    also have "\<dots> dvd pderiv p"
      by auto
    finally have "Polynomial.degree p = 0"
      by auto
    with assms have False by simp
  }
  thus ?thesis by (auto simp: rsquarefree_roots)
qed

lemma higher_pderiv_pcompose_linear:
   "(pderiv ^^ n) (pcompose p [:0, c:]) =
    Polynomial.smult (c ^ n) (pcompose ((pderiv ^^ n) p) [:0, c:])"
  by (induction n)  (simp_all add: pderiv_pcompose pderiv_smult pderiv_pCons pcompose_smult mult_ac)

lemma poly_poly_eq:
  "poly (poly p [:x:]) y = poly (eval_poly (\<lambda>p. [:poly p y:]) p [:0, 1:]) x"
  by (induction p) (auto simp: eval_poly_def)

lemma poly_poly_poly_y_x [simp]:
  fixes p :: "'a :: idom poly poly"
  shows "poly (poly (poly_y_x p) [:y:]) x = poly (poly p [:x:]) y"
proof (induction p)
  case (pCons a p)
  have "poly (poly (poly_y_x (pCons a p)) [:y:]) x = 
          poly a y + poly (poly (map_poly (pCons 0) (poly_y_x p)) [:y:]) x"
    by (simp add: poly_y_x_pCons eval_poly_def)
  also have "pCons 0 = (\<lambda>p::'a poly. Polynomial.monom 1 1 * p)"
    by (simp add: Polynomial.monom_altdef)
  also have "map_poly \<dots> (poly_y_x p) = Polynomial.smult (Polynomial.monom 1 1) (poly_y_x p)"
    by (simp add: smult_conv_map_poly)
  also have "poly \<dots> [:y:] = Polynomial.monom 1 1 * poly (poly_y_x p) [:y:]"
    by simp
  also have "poly a y + poly \<dots> x = poly (poly (pCons a p) [:x:]) y"
    by (simp add: pCons poly_monom)
  finally show ?case .
qed auto

lemma (in idom_hom) map_poly_higher_pderiv [hom_distribs]:
  "map_poly hom ((pderiv ^^ n) p) = (pderiv ^^ n) (map_poly hom p)"
  by (induction n) (simp_all add: map_poly_pderiv)

lemma coeff_prod_linear_factors:
  fixes f :: "'a \<Rightarrow> 'b :: comm_ring_1"
  assumes [intro]: "finite A"
  shows "Polynomial.coeff (\<Prod>x\<in>A. [:-f x, 1:] ^ e x) i =
           (\<Sum>X | X \<in> Pow (SIGMA x:A. {..<e x}) \<and> i = sum e A - card X.
             (-1) ^ card X * (\<Prod>x\<in>X. f (fst x)))"
proof -
  define poly_X where "poly_X = (Polynomial.monom 1 1 :: 'b poly)"
  have [simp]: "(- 1) ^ n = [:(- 1) ^ n :: 'b:]" for n :: nat
    by (simp flip: pCons_one)
  have "(\<Prod>x\<in>A. [:-f x, 1:] ^ e x) = (\<Prod>(x,_)\<in>Sigma A (\<lambda>x. {..<e x}). [:-f x, 1:])"
    by (subst prod.Sigma [symmetric]) auto
  also have "\<dots> = (\<Prod>(x,_)\<in>Sigma A (\<lambda>x. {..<e x}). poly_X - [:f x:])"
    by (intro prod.cong) (auto simp: poly_X_def monom_altdef)
  also have "\<dots> = (\<Sum>X\<in>Pow (SIGMA x:A. {..<e x}).
                    Polynomial.smult ((-1) ^ card X * (\<Prod>x\<in>X. f (fst x)))
                    (poly_X ^ card ((SIGMA x:A. {..<e x}) - X)))"
    unfolding case_prod_unfold 
    by (subst prod_diff1) (auto simp: mult_ac simp flip: coeff_lift_hom.hom_prod)
  also have "\<dots> = (\<Sum>X\<in>Pow (SIGMA x:A. {..<e x}).
       Polynomial.monom ((- 1) ^ card X * (\<Prod>x\<in>X. f (fst x))) (card ((SIGMA x:A. {..<e x}) - X)))"
    unfolding poly_X_def monom_power Polynomial.smult_monom by simp
  also have "Polynomial.coeff \<dots> i = (\<Sum>X\<in>{X\<in>Pow (SIGMA x:A. {..<e x}). i =
               sum e A - card X}. (- 1) ^ card X * (\<Prod>x\<in>X. f (fst x)))"
    unfolding Polynomial.coeff_sum
  proof (intro sum.mono_neutral_cong_right ballI, goal_cases)
    case (3 X)
    hence X: "X \<subseteq> (SIGMA x:A. {..<e x})"
      by auto
    have card_le: "card X \<le> card (SIGMA x:A. {..<e x})"
      using X by (intro card_mono) auto
    have "finite X"
      by (rule finite_subset[OF X]) auto
    hence "card ((SIGMA x:A. {..<e x}) - X) = card (SIGMA x:A. {..<e x}) - card X"
      using 3 by (intro card_Diff_subset) auto
    also have card_eq: "card (SIGMA x:A. {..<e x}) = sum e A"
      by (subst card_SigmaI) auto
    finally show ?case
      using 3 card_le card_eq by (auto simp: algebra_simps)
  next
    case (4 X)
    hence X: "X \<subseteq> (SIGMA x:A. {..<e x})"
      by auto
    have "finite X"
      by (rule finite_subset[OF X]) auto
    hence "card ((SIGMA x:A. {..<e x}) - X) = card (SIGMA x:A. {..<e x}) - card X"
      using 4 by (intro card_Diff_subset) auto
    also have card_eq: "card (SIGMA x:A. {..<e x}) = sum e A"
      by (subst card_SigmaI) auto
    finally show ?case
      using 4 card_eq by (auto simp: algebra_simps)
  qed auto
  finally show ?thesis .
qed

lemma (in comm_ring_hom) synthetic_div_hom:
  "synthetic_div (map_poly hom p) (hom x) = map_poly hom (synthetic_div p x)"
  by (induction p) (auto simp: map_poly_pCons_hom)

lemma synthetic_div_altdef:
  fixes p :: "'a :: field poly"
  shows "synthetic_div p c = p div [:-c, 1:]"
proof -
  define q where "q = p div [:- c, 1:]"
  have "Polynomial.degree (p mod [:-c, 1:]) = 0"
  proof (cases "p mod [:-c, 1:] = 0")
    case False
    hence "Polynomial.degree (p mod [:-c, 1:]) < Polynomial.degree [:-c, 1:]"
      by (intro degree_mod_less') auto
    thus ?thesis by simp
  qed auto
  then obtain d where d: "p mod [:-c, 1:] = [:d:]"
    by (elim degree_eq_zeroE)

  have p_eq: "p = q * [:-c, 1:] + [:d:]"
    unfolding q_def d [symmetric] by presburger
  have [simp]: "poly p c = d"
    by (simp add: p_eq)
  have "p + Polynomial.smult c q = pCons (poly p c) q"
    by (subst p_eq) auto
  from synthetic_div_unique[OF this] show ?thesis
    by (auto simp: q_def)
qed

lemma (in ring_closed) poly_closed [intro]:
  assumes "\<And>i. poly.coeff p i \<in> A" "x \<in> A"
  shows   "poly p x \<in> A"
  unfolding poly_altdef by (intro sum_closed mult_closed power_closed assms)

lemma (in ring_closed) coeff_pCons_closed [intro]:
  assumes "\<And>i. poly.coeff p i \<in> A" "x \<in> A"
  shows   "poly.coeff (pCons x p) i \<in> A"
  unfolding poly_altdef using assms by (auto simp: coeff_pCons split: nat.splits)

lemma (in ring_closed) coeff_poly_mult_closed [intro]:
  assumes "\<And>i. poly.coeff p i \<in> A" "\<And>i. poly.coeff q i \<in> A"
  shows   "poly.coeff (p * q) i \<in> A"
  unfolding coeff_mult using assms by auto

lemma (in ring_closed) coeff_poly_prod_closed [intro]:
  assumes "\<And>x i. x \<in> X \<Longrightarrow> poly.coeff (f x) i \<in> A"
  shows   "poly.coeff (prod f X) i \<in> A"
  using assms by (induction X arbitrary: i rule: infinite_finite_induct) auto

lemma (in ring_closed) coeff_poly_power_closed [intro]:
  assumes "\<And>i. poly.coeff p i \<in> A"
  shows   "poly.coeff (p ^ n) i \<in> A"
  using coeff_poly_prod_closed[of "{..<n}" "\<lambda>_. p" i] assms by simp

lemma (in ring_closed) synthetic_div_closed:
  assumes "\<And>i. poly.coeff p i \<in> A" "x \<in> A"
  shows   "poly.coeff (synthetic_div p x) i \<in> A"
proof -
  from assms(1) have "\<forall>i. poly.coeff p i \<in> A"
    by blast
  from this and assms(2) show ?thesis
    by (induction p arbitrary: i) (auto simp: coeff_pCons split: nat.splits)
qed

lemma pcompose_monom: "pcompose (Polynomial.monom c n) p = Polynomial.smult c (p ^ n)"
  by (simp add: monom_altdef pcompose_hom.hom_power pcompose_smult)



subsection \<open>Auxiliary facts about multivariate polynomials\<close>

lemma Var_altdef: "Var i = monom (Poly_Mapping.single i 1) 1"
  by transfer' (simp add: Var\<^sub>0_def)

lemma Const_0 [simp]: "Const 0 = 0"
  by transfer (auto simp: Const\<^sub>0_def)

lemma Const_1 [simp]: "Const 1 = 1"
  by transfer (auto simp: Const\<^sub>0_def)

lemma Const_conv_monom: "Const c = monom 0 c"
  by transfer' (auto simp: Const\<^sub>0_def)

lemma smult_conv_mult_Const: "smult c p = Const c * p"
  by (simp add: smult_conv_mult Const_conv_monom)

lemma mpoly_map_vars_Var [simp]: "bij f \<Longrightarrow> mpoly_map_vars f (Var i) = Var (f i)"
  unfolding Var_altdef
  by (subst mpoly_map_vars_monom) (auto simp: permutep_single bij_imp_bij_inv inv_inv_eq)

lemma symmetric_mpoly_symmetric_prod':
  assumes "\<And>\<pi>. \<pi> permutes A \<Longrightarrow> g \<pi> permutes X"
  assumes "\<And>x \<pi>. x \<in> X \<Longrightarrow> \<pi> permutes A \<Longrightarrow> mpoly_map_vars \<pi> (f x) = f (g \<pi> x)"
  shows "symmetric_mpoly A (\<Prod>x\<in>X. f x)"
  unfolding symmetric_mpoly_def
proof safe
  fix \<pi> assume \<pi>: "\<pi> permutes A"
  have "mpoly_map_vars \<pi> (prod f X) = (\<Prod>x\<in>X. mpoly_map_vars \<pi> (f x))"
    by simp
  also have "\<dots> = (\<Prod>x\<in>X. f (g \<pi> x))"
    by (intro prod.cong assms \<pi> refl)
  also have "\<dots> = (\<Prod>x\<in>g \<pi>`X. f x)"
    using assms(1)[OF \<pi>] by (subst prod.reindex) (auto simp: permutes_inj_on)
  also have "g \<pi> ` X = X"
    using assms(1)[OF \<pi>] by (simp add: permutes_image)
  finally show "mpoly_map_vars \<pi> (prod f X) = prod f X" .
qed


subsection \<open>Converting a univariate polynomial into a multivariate one\<close>

lift_definition mpoly_of_poly_aux :: "nat \<Rightarrow> 'a :: zero poly \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a" is
  "\<lambda>i c m. if Poly_Mapping.keys m \<subseteq> {i} then c (Poly_Mapping.lookup m i) else 0"
proof goal_cases
  case (1 i c)
  hence fin: "finite {n. c n \<noteq> 0}"
    by (metis eventually_cofinite)
  show "finite {x. (if keys x \<subseteq> {i} then c (lookup x i) else 0) \<noteq> 0}"
  proof (rule finite_subset)
    show "finite (Poly_Mapping.single i ` {n. c n \<noteq> 0})"
      by (intro finite_imageI fin)
  next
    show "{x. (if keys x \<subseteq> {i} then c (lookup x i) else 0) \<noteq> 0} \<subseteq>
            Poly_Mapping.single i ` {n. c n \<noteq> 0}"
    proof (safe, split if_splits)
      fix x :: "(nat \<Rightarrow>\<^sub>0 nat)"
      assume x: "keys x \<subseteq> {i}" "c (lookup x i) \<noteq> 0"
      hence "x = Poly_Mapping.single i (lookup x i)"
        by (metis Diff_eq_empty_iff keys_empty_iff lookup_single_eq
                  remove_key_keys remove_key_single remove_key_sum)
      thus "x \<in> Poly_Mapping.single i ` {n. c n \<noteq> 0}"
        using x by blast
    qed auto
  qed
qed

lift_definition mpoly_of_poly :: "nat \<Rightarrow> 'a :: zero poly \<Rightarrow> 'a mpoly" is
  "mpoly_of_poly_aux" .

lemma mpoly_of_poly_0 [simp]: "mpoly_of_poly i 0 = 0"
  by (transfer', transfer) auto

lemma coeff_mpoly_of_poly1 [simp]:
  "coeff (mpoly_of_poly i p) (Poly_Mapping.single i n) = poly.coeff p n"
  by (transfer', transfer') auto

lemma coeff_mpoly_of_poly2 [simp]:
  assumes "\<not>keys x \<subseteq> {i}"
  shows "coeff (mpoly_of_poly i p) x = 0"
  using assms by (transfer', transfer') auto

lemma coeff_mpoly_of_poly:
  "coeff (mpoly_of_poly i p) m =
     (poly.coeff p (Poly_Mapping.lookup m i) when keys m \<subseteq> {i})"
  by (transfer', transfer') auto

lemma poly_mapping_single_eq_0_iff [simp]: "Poly_Mapping.single i n = 0 \<longleftrightarrow> n = 0"
  by (metis lookup_single_eq single_zero)

lemma mpoly_of_poly_pCons [simp]:
  fixes p :: "'a :: semiring_1 poly"
  shows "mpoly_of_poly i (pCons c p) = Const c + Var i * mpoly_of_poly i p"
proof (rule mpoly_eqI)
  fix mon :: "nat \<Rightarrow>\<^sub>0 nat"
  define moni :: "nat \<Rightarrow>\<^sub>0 nat" where "moni = Poly_Mapping.single i 1"
  have "coeff (Var i * mpoly_of_poly i p) mon =
          (\<Sum>l. (1 when l = moni) * (\<Sum>q. coeff (mpoly_of_poly i p) q when mon = moni + q))"
    unfolding coeff_mpoly_times prod_fun_def coeff_Var moni_def
    by (rule Sum_any.cong) (auto simp: when_def)
  also have "\<dots> = (\<Sum>a. coeff (mpoly_of_poly i p) a when mon = moni + a)"
    by (subst Sum_any_left_distrib [symmetric]) simp_all
  finally have eq: "coeff (Var i * mpoly_of_poly i p) mon = \<dots>" .

  show "coeff (mpoly_of_poly i (pCons c p)) mon = coeff (Const c + Var i * mpoly_of_poly i p) mon"
  proof (cases "keys mon \<subseteq> {i}")
    case False
    hence [simp]: "mon \<noteq> 0"
      by auto
    obtain j where j: "j \<in> keys mon" "j \<noteq> i"
      using False by auto
    have "coeff (mpoly_of_poly i p) mon' = 0" if mon_eq: "mon = moni + mon'" for mon'
    proof -
      have "Poly_Mapping.lookup mon j \<noteq> 0"
        using j by (meson lookup_eq_zero_in_keys_contradict)
      also have "Poly_Mapping.lookup mon j = Poly_Mapping.lookup mon' j"
        unfolding mon_eq moni_def using j by (simp add: lookup_add lookup_single)
      finally have "j \<in> keys mon'"
        by (meson lookup_not_eq_zero_eq_in_keys)
      with j have "\<not>keys mon' \<subseteq> {i}"
        by blast
      thus ?thesis by simp
    qed
    hence "coeff (Var i * mpoly_of_poly i p) mon = 0"
      unfolding eq by (intro Sum_any_zeroI) (auto simp: when_def)
    thus ?thesis using False
      by (simp add: mpoly_coeff_Const)
  next
    case True
    define n where "n = Poly_Mapping.lookup mon i"
    have mon_eq: "mon = Poly_Mapping.single i n"
      using True unfolding n_def
      by (metis Diff_eq_empty_iff add_cancel_right_left keys_empty_iff remove_key_keys remove_key_sum)
    have eq': "mon = moni + mon' \<longleftrightarrow> n > 0 \<and> mon' = Poly_Mapping.single i (n - 1)" for mon'
    proof safe
      assume eq: "mon = moni + mon'"
      thus "n > 0" "mon' = Poly_Mapping.single i (n - 1)"
        unfolding moni_def mon_eq using gr0I by (force simp: single_diff)+
    next
      assume "n > 0" "mon' = Poly_Mapping.single i (n - 1)"
      thus "mon = moni + Poly_Mapping.single i (n - 1)"
        unfolding mon_eq moni_def by (subst single_add [symmetric]) auto
    qed
    have "coeff (Var i * mpoly_of_poly i p) mon = (poly.coeff p (n - 1) when (n > 0))"
      unfolding eq eq' by (auto simp: when_def)
    thus ?thesis
      by (auto simp: mon_eq when_def mpoly_coeff_Const coeff_pCons split: nat.splits)
  qed
qed

lemma mpoly_of_poly_1 [simp]: "mpoly_of_poly i 1 = 1"
  unfolding one_pCons mpoly_of_poly_pCons mpoly_of_poly_0 by simp

lemma mpoly_of_poly_uminus [simp]: "mpoly_of_poly i (-p) = -mpoly_of_poly i p"
  by (rule mpoly_eqI) (auto simp: coeff_mpoly_of_poly when_def)

lemma mpoly_of_poly_add [simp]: "mpoly_of_poly i (p + q) = mpoly_of_poly i p + mpoly_of_poly i q"
  by (rule mpoly_eqI) (auto simp: coeff_mpoly_of_poly when_def)

lemma mpoly_of_poly_diff [simp]: "mpoly_of_poly i (p - q) = mpoly_of_poly i p - mpoly_of_poly i q"
  by (rule mpoly_eqI) (auto simp: coeff_mpoly_of_poly when_def)

lemma mpoly_of_poly_smult [simp]:
  "mpoly_of_poly i (Polynomial.smult c p) = smult c (mpoly_of_poly i p)"
  by (rule mpoly_eqI) (auto simp: coeff_mpoly_of_poly when_def)

lemma mpoly_of_poly_mult [simp]:
  fixes p q :: "'a :: comm_semiring_1 poly"
  shows "mpoly_of_poly i (p * q) = mpoly_of_poly i p * mpoly_of_poly i q"
  by (induction p) (auto simp: algebra_simps smult_conv_mult_Const)

lemma insertion_mpoly_of_poly [simp]: "insertion f (mpoly_of_poly i p) = poly p (f i)"
  by (induction p) (auto simp: insertion_add insertion_mult)

lemma mapping_of_mpoly_of_poly [simp]: "mapping_of (mpoly_of_poly i p) = mpoly_of_poly_aux i p"
  by transfer' simp

lemma vars_mpoly_of_poly: "vars (mpoly_of_poly i p) \<subseteq> {i}"
proof -
  have "x = i" if "xa \<in> keys (mpoly_of_poly_aux i p)" "x \<in> keys xa" for x xa
    using that
    by (meson in_mono lookup_eq_zero_in_keys_contradict mpoly_of_poly_aux.rep_eq singletonD)
  thus ?thesis
    by (auto simp: vars_def)
qed

lemma mpoly_map_vars_mpoly_of_poly [simp]:
  assumes "bij f"
  shows   "mpoly_map_vars f (mpoly_of_poly i p) = mpoly_of_poly (f i) p"
proof (rule mpoly_eqI, goal_cases)
  case (1 mon)
  have "f -` keys mon \<subseteq> {i} \<longleftrightarrow> keys mon \<subseteq> {f i}"
    using assms by (simp add: vimage_subset_eq)
  thus ?case using assms
    by (simp add: coeff_mpoly_map_vars coeff_mpoly_of_poly lookup_permutep keys_permutep when_def)
qed


subsection \<open>Miscellaneous facts\<close>

lemma algebraic_int_fact [simp, intro]: "algebraic_int (fact n)"
  by (intro int_imp_algebraic_int fact_in_Ints)

lemma exponential_smallo_fact: "(\<lambda>n. c ^ n :: real) \<in> o(\<lambda>n. fact n)"
  by (rule smalloI_tendsto[OF power_over_fact_tendsto_0]) auto

lemma (in landau_pair) big_power:
  assumes "f \<in> L F g"
  shows   "(\<lambda>x. f x ^ n) \<in> L F (\<lambda>x. g x ^ n)"
  using big_prod[of "{..<n}" "\<lambda>_. f" F "\<lambda>_. g"] assms by simp

lemma (in landau_pair) small_power:
  assumes "f \<in> l F g" "n > 0"
  shows   "(\<lambda>x. f x ^ n) \<in> l F (\<lambda>x. g x ^ n)"
  using assms(2,1)
  by (induction rule: nat_induct_non_zero) (auto intro!: small.mult)

lemma pairwise_imp_disjoint_family_on:
  assumes "pairwise R A"
  assumes "\<And>m n. m \<in> A \<Longrightarrow> n \<in> A \<Longrightarrow> R m n \<Longrightarrow> f m \<inter> f n = {}"
  shows   "disjoint_family_on f A"
  using assms
  unfolding disjoint_family_on_def pairwise_def by blast

lemma (in comm_monoid_set) If_eq:
  assumes "y \<in> A" "finite A"
  shows   "F (\<lambda>x. g x (if x = y then h1 x else h2 x)) A = f (g y (h1 y)) (F (\<lambda>x. g x (h2 x)) (A-{y}))"
proof -
  have "F (\<lambda>x. g x (if x = y then h1 x else h2 x)) A =
          f (g y (h1 y)) (F (\<lambda>x. g x (if x = y then h1 x else h2 x)) (A-{y}))"
    using assms by (subst remove[of _ y]) auto
  also have "F (\<lambda>x. g x (if x = y then h1 x else h2 x)) (A-{y}) = F (\<lambda>x. g x (h2 x)) (A-{y})"
    by (intro cong) auto
  finally show ?thesis by simp
qed

lemma prod_nonzeroI:
  fixes f :: "'a \<Rightarrow> 'b :: {semiring_no_zero_divisors, comm_semiring_1}"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows "prod f A \<noteq> 0"
  using assms by (induction rule: infinite_finite_induct) auto

lemma frequently_prime_cofinite: "frequently (prime :: nat \<Rightarrow> bool) cofinite"
  using INFM_nat_le by blast

lemma frequently_eventually_mono:
  assumes "frequently Q F" "eventually P F" "\<And>x. P x \<Longrightarrow> Q x \<Longrightarrow> R x"
  shows   "frequently R F"
proof (rule frequently_mp[OF _ assms(1)])
  show "eventually (\<lambda>x. Q x \<longrightarrow> R x) F"
    using assms(2) by eventually_elim (use assms(3) in blast)
qed

lemma bij_betw_Diff:
  assumes "bij_betw f A B" "bij_betw f A' B'" "A' \<subseteq> A" "B' \<subseteq> B"
  shows   "bij_betw f (A - A') (B - B')"
  unfolding bij_betw_def
proof
  have "inj_on f A"
    using assms(1) by (auto simp: bij_betw_def)
  thus "inj_on f (A - A')"
    by (rule inj_on_subset) auto
  have "f ` (A - A') = f ` A - f ` A'"
    by (intro inj_on_image_set_diff[OF \<open>inj_on f A\<close>]) (use \<open>A' \<subseteq> A\<close> in auto)
  also have "\<dots> = B - B'"
    using assms(1,2) by (auto simp: bij_betw_def)
  finally show "f` (A - A') = B - B'" .
qed
    
lemma bij_betw_singleton: "bij_betw f {x} {y} \<longleftrightarrow> f x = y"
  by (auto simp: bij_betw_def)


subsection \<open>Turning an algebraic number into an algebraic integer\<close>

lemma algebraic_imp_algebraic_int:
  fixes x :: "'a :: field_char_0"
  assumes "ipoly p x = 0" "p \<noteq> 0"
  defines "c \<equiv> Polynomial.lead_coeff p"
  shows   "algebraic_int (of_int c * x)"
proof -
  define n where "n = Polynomial.degree p"
  define p' where "p' = Abs_poly (\<lambda>i. if i = n then 1 else c ^ (n - i - 1) * poly.coeff p i)"
  have "n > 0"
    using assms unfolding n_def by (intro Nat.gr0I) (auto elim!: degree_eq_zeroE)

  have coeff_p': "poly.coeff p' i =
                    (if i = n then 1 else c ^ (n - i - 1) * poly.coeff p i)"
    (is "_ = ?f i") for i unfolding p'_def
  proof (subst poly.Abs_poly_inverse)
    have "eventually (\<lambda>i. poly.coeff p i = 0) cofinite"
      using MOST_coeff_eq_0 by blast
    hence "eventually (\<lambda>i. ?f i = 0) cofinite"
      by eventually_elim (use assms in \<open>auto simp: deg_def n_def\<close>)
    thus "?f \<in> {f. eventually (\<lambda>i. f i = 0) cofinite}" by simp
  qed auto

  have deg_p': "Polynomial.degree p' = n"
  proof -
    from assms have "(\<lambda>n. \<forall>i>n. poly.coeff p' i = 0) = (\<lambda>n. \<forall>i>n. poly.coeff p i = 0)"
      by (auto simp: coeff_p' fun_eq_iff n_def)
    thus ?thesis
      by (simp add: Polynomial.degree_def n_def)
  qed

  have lead_coeff_p': "Polynomial.lead_coeff p' = 1"
    by (simp add: coeff_p' deg_p')

  have "0 = of_int (c ^ (n - 1)) * (\<Sum>i\<le>n. of_int (poly.coeff p i) * x ^ i)"
    using assms unfolding n_def poly_altdef by simp
  also have "\<dots> = (\<Sum>i\<le>n. of_int (c ^ (n - 1) * poly.coeff p i) * x ^ i)"
    by (simp add: sum_distrib_left sum_distrib_right mult_ac)
  also have "\<dots> = (\<Sum>i\<le>n. of_int (poly.coeff p' i) * (of_int c * x) ^ i)"
  proof (intro sum.cong, goal_cases)
    case (2 i)
    have "of_int (poly.coeff p' i) * (of_int c * x) ^ i =
          of_int (c ^ i * poly.coeff p' i) * x ^ i"
      by (simp add: algebra_simps)
    also have "c ^ i * poly.coeff p' i = c ^ (n - 1) * poly.coeff p i"
    proof (cases "i = n")
      case True
      hence "c ^ i * poly.coeff p' i = c ^ n"
        by (auto simp: coeff_p' simp flip: power_Suc)
      also have "n = Suc (n - 1)"
        using \<open>n > 0\<close> by simp
      also have "c ^ \<dots> = c * c ^ (n - 1)"
        by simp
      finally show ?thesis
        using True by (simp add: c_def n_def)
    next
      case False
      thus ?thesis using 2
        by (auto simp: coeff_p' simp flip: power_add)
    qed
    finally show ?case ..
  qed auto
  also have "\<dots> = ipoly p' (of_int c * x)"
    by (simp add: poly_altdef n_def deg_p')
  finally have "ipoly p' (of_int c * x) = 0" ..

  with lead_coeff_p' show ?thesis
    unfolding algebraic_int_altdef_ipoly by blast
qed

lemma algebraic_imp_algebraic_int':
  fixes x :: "'a :: field_char_0"
  assumes "ipoly p x = 0" "p \<noteq> 0" "Polynomial.lead_coeff p dvd c"
  shows   "algebraic_int (of_int c * x)"
proof -
  from assms(3) obtain c' where c_eq: "c = Polynomial.lead_coeff p * c'"
    by auto
  have "algebraic_int (of_int c' * (of_int (Polynomial.lead_coeff p) * x))"
    by (rule algebraic_int_times[OF _ algebraic_imp_algebraic_int]) (use assms in auto)
  also have "of_int c' * (of_int (Polynomial.lead_coeff p) * x) = of_int c * x"
    by (simp add: c_eq mult_ac)
  finally show ?thesis .
qed


subsection \<open>The minimal polynomial of an algebraic number\<close>

definition min_int_poly :: "'a :: field_char_0 \<Rightarrow> int poly" where
  "min_int_poly x =
     (if algebraic x then THE p. p represents x \<and> irreducible p \<and> Polynomial.lead_coeff p > 0
      else [:0, 1:])"

lemma
  fixes x :: "'a :: {field_char_0, field_gcd}"
  shows min_int_poly_represents [intro]: "algebraic x \<Longrightarrow> min_int_poly x represents x"
  and   min_int_poly_irreducible [intro]: "irreducible (min_int_poly x)"
  and   lead_coeff_min_int_poly_pos: "Polynomial.lead_coeff (min_int_poly x) > 0"
proof -
  note * = theI'[OF algebraic_imp_represents_unique, of x]
  show "min_int_poly x represents x" if "algebraic x"
    using *[OF that] by (simp add: that min_int_poly_def)
  have "irreducible [:0, 1::int:]"
    by (rule irreducible_linear_poly) auto
  thus "irreducible (min_int_poly x)"
    using * by (auto simp: min_int_poly_def)
  show "Polynomial.lead_coeff (min_int_poly x) > 0"
    using * by (auto simp: min_int_poly_def)
qed

lemma min_int_poly_nonzero [simp]:
  fixes x :: "'a :: {field_char_0, field_gcd}"
  shows "min_int_poly x \<noteq> 0"
  using lead_coeff_min_int_poly_pos[of x] by auto

lemma normalize_min_int_poly [simp]:
  fixes x :: "'a :: {field_char_0, field_gcd}"
  shows "normalize (min_int_poly x) = min_int_poly x"
  unfolding normalize_poly_def using lead_coeff_min_int_poly_pos[of x] by simp
  
lemma min_int_poly_conv_Gcd:
  fixes x :: "'a :: {field_char_0, field_gcd}"
  assumes "algebraic x"
  shows "min_int_poly x = Gcd {p. p \<noteq> 0 \<and> p represents x}"
proof (rule sym, rule Gcd_eqI, (safe)?)
  fix p assume p: "\<And>q. q \<in> {p. p \<noteq> 0 \<and> p represents x} \<Longrightarrow> p dvd q"
  show "p dvd min_int_poly x"
    using assms by (intro p) auto
next
  fix p assume p: "p \<noteq> 0" "p represents x"
  have "min_int_poly x represents x"
    using assms by auto
  hence "poly (gcd (of_int_poly (min_int_poly x)) (of_int_poly p)) x = 0"
    using p by (intro poly_gcd_eq_0I) auto
  hence "ipoly (gcd (min_int_poly x) p) x = 0"
    by (subst (asm) gcd_of_int_poly) auto
  hence "gcd (min_int_poly x) p represents x"
    using p unfolding represents_def by auto

  have "min_int_poly x dvd gcd (min_int_poly x) p \<or> is_unit (gcd (min_int_poly x) p)"
    by (intro irreducibleD') auto
  moreover from \<open>gcd (min_int_poly x) p represents x\<close> have "\<not>is_unit (gcd (min_int_poly x) p)"
    by (auto simp: represents_def)
  ultimately have "min_int_poly x dvd gcd (min_int_poly x) p"
    by blast
  also have "\<dots> dvd p"
    by blast
  finally show "min_int_poly x dvd p" .
qed auto

lemma min_int_poly_eqI:
  fixes x :: "'a :: {field_char_0, field_gcd}"
  assumes "p represents x" "irreducible p" "Polynomial.lead_coeff p \<ge> 0"
  shows   "min_int_poly x = p"
proof -
  from assms have [simp]: "p \<noteq> 0"
    by auto
  have "Polynomial.lead_coeff p \<noteq> 0"
    by auto
  with assms(3) have "Polynomial.lead_coeff p > 0"
    by linarith
  moreover have "algebraic x"
    using \<open>p represents x\<close> by (meson algebraic_iff_represents)
  ultimately show ?thesis
    unfolding min_int_poly_def
    using the1_equality[OF algebraic_imp_represents_unique[OF \<open>algebraic x\<close>], of p] assms by auto
qed


subsection \<open>Divisibility of algebraic integers\<close>

definition alg_dvd :: "'a :: field \<Rightarrow> 'a \<Rightarrow> bool" (infix "alg'_dvd" 50) where
  "x alg_dvd y \<longleftrightarrow> (x = 0 \<longrightarrow> y = 0) \<and> algebraic_int (y / x)"

lemma alg_dvd_imp_algebraic_int:
  fixes x y :: "'a :: field_char_0"
  shows "x alg_dvd y \<Longrightarrow> algebraic_int x \<Longrightarrow> algebraic_int y"
  using algebraic_int_times[of "y / x" x] by (auto simp: alg_dvd_def)

lemma alg_dvd_0_left_iff [simp]: "0 alg_dvd x \<longleftrightarrow> x = 0"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_0_right [iff]: "x alg_dvd 0"
  by (auto simp: alg_dvd_def)

lemma one_alg_dvd_iff [simp]: "1 alg_dvd x \<longleftrightarrow> algebraic_int x"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_of_int [intro]:
  assumes "x dvd y"
  shows   "of_int x alg_dvd of_int y"
proof (cases "of_int x = (0 :: 'a)")
  case False
  from assms obtain z where z: "y = x * z"
    by (elim dvdE)
  have "algebraic_int (of_int z)"
    by auto
  also have "of_int z = of_int y / (of_int x :: 'a)"
    using False by (simp add: z field_simps)
  finally show ?thesis
    using False by (simp add: alg_dvd_def)
qed (use assms in \<open>auto simp: alg_dvd_def\<close>)

lemma alg_dvd_of_nat [intro]:
  assumes "x dvd y"
  shows   "of_nat x alg_dvd of_nat y"
  using alg_dvd_of_int[of "int x" "int y"] assms by simp

lemma alg_dvd_of_int_iff [simp]:
  "(of_int x :: 'a :: field_char_0) alg_dvd of_int y \<longleftrightarrow> x dvd y"
proof
  assume "(of_int x :: 'a) alg_dvd of_int y"
  hence "of_int y / (of_int x :: 'a) \<in> \<int>" and nz: "of_int x = (0::'a) \<longrightarrow> of_int y = (0::'a)"
    by (auto simp: alg_dvd_def dest!: rational_algebraic_int_is_int)
  then obtain n where "of_int y / of_int x = (of_int n :: 'a)"
    by (elim Ints_cases)
  hence "of_int y = (of_int (x * n) :: 'a)"
    unfolding of_int_mult using nz by (auto simp: field_simps)
  hence "y = x * n"
    by (subst (asm) of_int_eq_iff)
  thus "x dvd y"
    by auto
qed blast

lemma alg_dvd_of_nat_iff [simp]:
  "(of_nat x :: 'a :: field_char_0) alg_dvd of_nat y \<longleftrightarrow> x dvd y"
proof -
  have "(of_int (int x) :: 'a) alg_dvd of_int (int y) \<longleftrightarrow> x dvd y"
    by (subst alg_dvd_of_int_iff) auto
  thus ?thesis unfolding of_int_of_nat_eq .
qed

lemma alg_dvd_add [intro]:
  fixes x y z :: "'a :: field_char_0"
  shows "x alg_dvd y \<Longrightarrow> x alg_dvd z \<Longrightarrow> x alg_dvd (y + z)"
  unfolding alg_dvd_def by (auto simp: add_divide_distrib)

lemma alg_dvd_uminus_right [intro]: "x alg_dvd y \<Longrightarrow> x alg_dvd -y"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_uminus_right_iff [simp]: "x alg_dvd -y \<longleftrightarrow> x alg_dvd y"
  using alg_dvd_uminus_right[of x y] alg_dvd_uminus_right[of x "-y"] by auto

lemma alg_dvd_diff [intro]:
  fixes x y z :: "'a :: field_char_0"
  shows "x alg_dvd y \<Longrightarrow> x alg_dvd z \<Longrightarrow> x alg_dvd (y - z)"
  unfolding alg_dvd_def by (auto simp: diff_divide_distrib)

lemma alg_dvd_triv_left [intro]: "algebraic_int y \<Longrightarrow> x alg_dvd x * y"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_triv_right [intro]: "algebraic_int x \<Longrightarrow> y alg_dvd x * y"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_triv_left_iff: "x alg_dvd x * y \<longleftrightarrow> x = 0 \<or> algebraic_int y"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_triv_right_iff: "y alg_dvd x * y \<longleftrightarrow> y = 0 \<or> algebraic_int x"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_triv_left_iff' [simp]: "x \<noteq> 0 \<Longrightarrow> x alg_dvd x * y \<longleftrightarrow> algebraic_int y"
  by (simp add: alg_dvd_triv_left_iff)

lemma alg_dvd_triv_right_iff' [simp]: "y \<noteq> 0 \<Longrightarrow> y alg_dvd x * y \<longleftrightarrow> algebraic_int x"
  by (simp add: alg_dvd_triv_right_iff)

lemma alg_dvd_trans [trans]:
  fixes x y z :: "'a :: field_char_0"
  shows "x alg_dvd y \<Longrightarrow> y alg_dvd z \<Longrightarrow> x alg_dvd z"
  using algebraic_int_times[of "y / x" "z / y"] by (auto simp: alg_dvd_def)

lemma alg_dvd_mono [simp]: 
  fixes a b c d :: "'a :: field_char_0"
  shows "a alg_dvd c \<Longrightarrow> b alg_dvd d \<Longrightarrow> (a * b) alg_dvd (c * d)"
  using algebraic_int_times[of "c / a" "d / b"] by (auto simp: alg_dvd_def)

lemma alg_dvd_mult [simp]: 
  fixes a b c :: "'a :: field_char_0"
  shows "a alg_dvd c \<Longrightarrow> algebraic_int b \<Longrightarrow> a alg_dvd (b * c)"
  using alg_dvd_mono[of a c 1 b] by (auto simp: mult.commute)

lemma alg_dvd_mult2 [simp]:
  fixes a b c :: "'a :: field_char_0"
  shows "a alg_dvd b \<Longrightarrow> algebraic_int c \<Longrightarrow> a alg_dvd (b * c)"
  using alg_dvd_mult[of a b c] by (simp add: mult.commute)

lemma alg_dvd_int_rat:
  fixes y :: "'a :: field_char_0"
  assumes "of_int x alg_dvd y" and "y \<in> \<rat>"
  shows   "\<exists>n. y = of_int n \<and> x dvd n"
proof (cases "x = 0")
  case False
  have "y / of_int x \<in> \<int>"
    by (intro rational_algebraic_int_is_int) (use assms in \<open>auto simp: alg_dvd_def\<close>)
  then obtain n where n: "of_int n = y / (of_int x :: 'a)"
    by (elim Ints_cases) auto
  hence "y = of_int (n * x)"
    using False by (simp add: field_simps)
  thus ?thesis by (intro exI[of _ "x * n"]) auto
qed (use assms in auto)

lemma prod_alg_dvd_prod:
  fixes f :: "'a \<Rightarrow> 'b :: field_char_0"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x alg_dvd g x"
  shows   "prod f A alg_dvd prod g A"
  using assms by (induction A rule: infinite_finite_induct) auto

lemma alg_dvd_sum:
  fixes f :: "'a \<Rightarrow> 'b :: field_char_0"
  assumes "\<And>x. x \<in> A \<Longrightarrow> y alg_dvd f x"
  shows   "y alg_dvd sum f A"
  using assms by (induction A rule: infinite_finite_induct) auto

lemma not_alg_dvd_sum:
  fixes f :: "'a \<Rightarrow> 'b :: field_char_0"
  assumes "\<And>x. x \<in> A-{x'} \<Longrightarrow> y alg_dvd f x"
  assumes "\<not>y alg_dvd f x'"
  assumes "x' \<in> A" "finite A"
  shows   "\<not>y alg_dvd sum f A"
proof
  assume *: "y alg_dvd sum f A"
  have "y alg_dvd sum f A - sum f (A - {x'})"
    using \<open>x' \<in> A\<close> by (intro alg_dvd_diff[OF * alg_dvd_sum] assms) auto
  also have "\<dots> = sum f (A - (A - {x'}))"
    using assms by (subst sum_diff) auto
  also have "A - (A - {x'}) = {x'}"
    using assms by auto
  finally show False using assms by simp
qed

lemma fact_alg_dvd_poly_higher_pderiv:
  fixes p :: "'a :: field_char_0 poly"
  assumes "\<And>i. algebraic_int (poly.coeff p i)" "algebraic_int x" "m \<le> k"
  shows   "fact m alg_dvd poly ((pderiv ^^ k) p) x"
  unfolding poly_altdef
proof (intro alg_dvd_sum, goal_cases)
  case (1 i)
  have "(of_int (fact m) :: 'a) alg_dvd (of_int (fact k))"
    by (intro alg_dvd_of_int fact_dvd assms)
  also have "(of_int (fact k) :: 'a) alg_dvd of_int (pochhammer (int i + 1) k)"
    using fact_dvd_pochhammer[of k "i + k"]
    by (intro alg_dvd_of_int fact_dvd_pochhammer) (auto simp: algebra_simps)
  finally have "fact m alg_dvd (pochhammer (of_nat i + 1) k :: 'a)"
    by (simp flip: pochhammer_of_int)
  also have "\<dots> alg_dvd pochhammer (of_nat i + 1) k * poly.coeff p (i + k)"
    by (rule alg_dvd_triv_left) (rule assms)
  also have "\<dots> = poly.coeff ((pderiv ^^ k) p) i"
    unfolding coeff_higher_pderiv by (simp add: add_ac flip: pochhammer_of_int)
  also have "\<dots> alg_dvd poly.coeff ((pderiv ^^ k) p) i * x ^ i"
    by (intro alg_dvd_triv_left algebraic_int_power assms)
  finally show ?case .
qed


subsection \<open>Main proof\<close>

text \<open>
  Following Baker, We first prove the following special form of the theorem:
  Let $m > 0$ and $q_1, \ldots, q_m \in\mathbb{Z}[X]$ be irreducible, non-constant,
  and pairwise coprime polynomials. Let $\beta_1, \ldots, \beta_m$ be non-zero integers. Then
  \[\sum_{i=1}^m \beta_i \sum_{q_i(\alpha) = 0} e^\alpha \neq 0\]
\<close>
lemma Hermite_Lindemann_aux1:
  fixes P :: "int poly set" and \<beta> :: "int poly \<Rightarrow> int"
  assumes "finite P" and "P \<noteq> {}"
  assumes distinct: "pairwise Rings.coprime P"
  assumes irred: "\<And>p. p \<in> P \<Longrightarrow> irreducible p"
  assumes nonconstant: "\<And>p. p \<in> P \<Longrightarrow> Polynomial.degree p > 0"
  assumes \<beta>_nz: "\<And>p. p \<in> P \<Longrightarrow> \<beta> p \<noteq> 0"
  defines "Roots \<equiv> (\<lambda>p. {\<alpha>::complex. poly (of_int_poly p) \<alpha> = 0})"
  shows   "(\<Sum>p\<in>P. of_int (\<beta> p) * (\<Sum>\<alpha>\<in>Roots p. exp \<alpha>)) \<noteq> 0"
proof
  note [intro] = \<open>finite P\<close>
  assume sum_eq_0: "(\<Sum>p\<in>P. of_int (\<beta> p) * (\<Sum>\<alpha>\<in>Roots p. exp \<alpha>)) = 0"

  define Roots' where "Roots' = (\<Union>p\<in>P. Roots p)"
  have finite_Roots [intro]: "finite (Roots p)" if "p \<in> P" for p
    using nonconstant[of p] that by (auto intro: poly_roots_finite simp: Roots_def)
  have [intro]: "finite Roots'"
    by (auto simp: Roots'_def)
  have [simp]: "0 \<notin> P"
    using nonconstant[of 0] by auto
  have [simp]: "p \<noteq> 0" if "p \<in> P" for p
    using that by auto

  text \<open>
    The polynomials in \<^term>\<open>P\<close> do not have multiple roots:
  \<close>
  have rsquarefree: "rsquarefree (of_int_poly q :: complex poly)" if "q \<in> P" for q
    by (rule irreducible_imp_rsquarefree_of_int_poly) (use that in \<open>auto intro: irred nonconstant\<close>)

  text \<open>
    No two different polynomials in \<^term>\<open>P\<close> have roots in common:
  \<close>
  have disjoint: "disjoint_family_on Roots P"
    using distinct
  proof (rule pairwise_imp_disjoint_family_on)
    fix p q assume P: "p \<in> P" "q \<in> P" and "Rings.coprime p q"
    hence "Rings.coprime (of_int_poly p :: complex poly) (of_int_poly q)"
      by (intro coprime_of_int_polyI)
    thus "Roots p \<inter> Roots q = {}"
      using poly_eq_0_coprime[of "of_int_poly p" "of_int_poly q :: complex poly"] P
      by (auto simp: Roots_def)
  qed

  define n_roots :: "int poly \<Rightarrow> nat" ("\<sharp>_")
    where "n_roots = (\<lambda>p. card (Roots p))"
  define n where "n = (\<Sum>p\<in>P. \<sharp>p)"
  have n_altdef: "n = card Roots'"
    unfolding n_def Roots'_def n_roots_def using disjoint
    by (subst card_UN_disjoint) (auto simp: disjoint_family_on_def)
  have Roots_nonempty: "Roots p \<noteq> {}" if "p \<in> P" for p
    using nonconstant[OF that] by (auto simp: Roots_def fundamental_theorem_of_algebra constant_degree)
  have "Roots' \<noteq> {}"
    using Roots_nonempty \<open>P \<noteq> {}\<close> by (auto simp: Roots'_def)
  have "n > 0"
    using \<open>Roots' \<noteq> {}\<close> \<open>finite Roots'\<close> by (auto simp: n_altdef)

  text \<open>
    We can split each polynomial in \<open>P\<close> into a product of linear factors:
  \<close>
  have of_int_poly_P:
     "of_int_poly q = Polynomial.smult (Polynomial.lead_coeff q) (\<Prod>x\<in>Roots q. [:-x, 1:])"
     if "q \<in> P" for q
    using complex_poly_decompose_rsquarefree[OF rsquarefree[OF that]] by (simp add: Roots_def)

  text \<open>
    We let \<open>l\<close> be an integer such that $l\alpha$ is an algebraic integer for all our roots \<open>\<alpha>\<close>:
  \<close>
  define l where "l = (LCM q\<in>P. Polynomial.lead_coeff q)"
  have alg_int: "algebraic_int (of_int l * x)" if "x \<in> Roots'" for x
  proof -
    from that obtain q where q: "q \<in> P" "ipoly q x = 0"
      by (auto simp: Roots'_def Roots_def)
    show ?thesis
      by (rule algebraic_imp_algebraic_int'[of q]) (use q in \<open>auto simp: l_def\<close>)
  qed
  have "l \<noteq> 0"
    using \<open>finite P\<close> by (auto simp: l_def Lcm_0_iff)
  moreover have "l \<ge> 0"
    unfolding l_def by (rule Lcm_int_greater_eq_0)
  ultimately have "l > 0" by linarith

  text \<open>
    We can split the product of all the polynomials in \<open>P\<close> into linear factors:
  \<close>
  define lc_factor where "lc_factor = (\<Prod>q\<in>P. l ^ Polynomial.degree q div Polynomial.lead_coeff q)"
  have lc_factor: "Polynomial.smult (of_int l ^ n) (\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>',1:]) =
                      of_int_poly (Polynomial.smult lc_factor (\<Prod>P))"
  proof -
    define lc where "lc = (\<lambda>q. Polynomial.lead_coeff q :: int)"
    define d where "d = (Polynomial.degree :: int poly \<Rightarrow> nat)"
    have "(\<Prod>q\<in>P. of_int_poly q) =
          (\<Prod>q\<in>P. Polynomial.smult (lc q) (\<Prod>x\<in>Roots q. [:-x, 1:]) :: complex poly)"
      unfolding lc_def by (intro prod.cong of_int_poly_P refl)
    also have "\<dots> = Polynomial.smult (\<Prod>q\<in>P. lc q) (\<Prod>q\<in>P. (\<Prod>x\<in>Roots q. [:-x, 1:]))"
      by (simp add: prod_smult)
    also have "(\<Prod>q\<in>P. (\<Prod>x\<in>Roots q. [:-x, 1:])) = (\<Prod>x\<in>Roots'. [:-x, 1:])"
      unfolding Roots'_def using disjoint
      by (intro prod.UNION_disjoint [symmetric]) (auto simp: disjoint_family_on_def)
    also have "Polynomial.smult (of_int lc_factor) (Polynomial.smult (\<Prod>q\<in>P. lc q) \<dots>) =
               Polynomial.smult (\<Prod>q\<in>P. of_int (l ^ d q div lc q * lc q)) (\<Prod>x\<in>Roots'. pCons (- x) 1)"
      by (simp add: lc_factor_def prod.distrib lc_def d_def)
    also have "(\<Prod>q\<in>P. of_int (l ^ d q div lc q * lc q)) = (\<Prod>q\<in>P. of_int l ^ d q :: complex)"
    proof (intro prod.cong, goal_cases)
      case (2 q)
      have "lc q dvd l"
        unfolding l_def lc_def using 2 by auto
      also have "\<dots> dvd l ^ d q"
        using 2 nonconstant[of q] by (intro dvd_power) (auto simp: d_def)
      finally show ?case by simp
    qed auto
    also have "\<dots> = l ^ (\<Sum>q\<in>P. d q)"
      by (simp add: power_sum)
    also have "(\<Sum>q\<in>P. d q) = (\<Sum>q\<in>P. n_roots q)"
    proof (intro sum.cong, goal_cases)
      case (2 q)
      thus ?case using rsquarefree[OF 2]
        by (subst (asm) rsquarefree_card_degree) (auto simp: d_def n_roots_def Roots_def)
    qed auto
    also have "\<dots> = n"
      by (simp add: n_def)
    finally show ?thesis
      by (simp add: of_int_hom.map_poly_hom_smult of_int_poly_hom.hom_prod)
  qed

  text \<open>
    We define \<open>R\<close> to be the radius of the smallest circle around the origin in which all our
    roots lie:
  \<close>
  define R :: real where "R = Max (norm ` Roots')"
  have R_ge: "R \<ge> norm \<alpha>" if "\<alpha> \<in> Roots'" for \<alpha>
    unfolding R_def using that by (intro Max_ge) auto
  have "R \<ge> 0"
  proof -
    from \<open>Roots' \<noteq> {}\<close> obtain \<alpha> where "\<alpha> \<in> Roots'"
      by auto
    have "0 \<le> norm \<alpha>"
      by simp
    also have "\<dots> \<le> R"
      by (intro R_ge) fact
    finally show "R \<ge> 0"
      by simp
  qed

  text \<open>
    Now the main part of the proof: for any sufficiently large prime \<open>p\<close>, our assumptions
    imply $(p-1)! ^ n \leq C' l^{np} (2R)^{np-1}$ for some constant $C'$:    
  \<close>
  define C :: "nat \<Rightarrow> real" where "C = (\<lambda>p. l ^ (n * p) * (2*R) ^ (n * p - 1))"
  define C' where
    "C' = (\<Prod>x\<in>Roots'. \<Sum>q\<in>P. real_of_int \<bar>\<beta> q\<bar> * (\<Sum>\<alpha>\<in>Roots q. cmod \<alpha> * exp (cmod \<alpha>)))"

  have ineq: "fact (p - 1) ^ n \<le> C' * C p ^ n"
    if p: "prime p" 
    and p_ineqs: "\<forall>q\<in>P. p > \<bar>\<beta> q\<bar>"
                 "real p > norm (\<Prod>\<alpha>\<in>Roots'. of_int (l^n) * (\<Prod>x\<in>Roots'-{\<alpha>}. \<alpha> - x))"
    for p :: nat
  proof -
    have "p > 1"
      using prime_gt_1_nat[OF p] .

    define f_poly :: "complex \<Rightarrow> complex poly" where
      "f_poly = (\<lambda>\<alpha>. Polynomial.smult (l^(n*p)) ((\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>', 1:]^p) div [:-\<alpha>, 1:]))"
    have f_poly_altdef: "f_poly \<alpha> = Polynomial.smult (l^(n*p))
                           ((\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>', 1:]^(if \<alpha>' = \<alpha> then p - 1 else p)))"
      if "\<alpha> \<in> Roots'" for \<alpha>
    proof -
      have "(\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>', 1:] ^ (if \<alpha>'=\<alpha> then p-1 else p)) * [:-\<alpha>, 1:] =
            [:- \<alpha>, 1:] ^ (p - 1) * (\<Prod>x\<in>Roots' - {\<alpha>}. [:- x, 1:] ^ p) * [:- \<alpha>, 1:]"
        using that by (subst prod.If_eq) (auto simp: algebra_simps)
      also have "\<dots> = (\<Prod>x\<in>Roots' - {\<alpha>}. [:- x, 1:] ^ p) * [:- \<alpha>, 1:] ^ Suc (p - 1)"
        by (simp only: power_Suc mult_ac)
      also have "Suc (p - 1) = p"
        using \<open>p > 1\<close> by auto
      also have "(\<Prod>x\<in>Roots' - {\<alpha>}. [:- x, 1:] ^ p) * [:- \<alpha>, 1:] ^ p = (\<Prod>x\<in>Roots'. [:- x, 1:] ^ p)"
        using that by (subst prod.remove[of _ \<alpha>]) auto
      finally have eq: "(\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>', 1:] ^ (if \<alpha>'=\<alpha> then p-1 else p)) * [:-\<alpha>, 1:] =
                        (\<Prod>x\<in>Roots'. [:- x, 1:] ^ p)" .
      show ?thesis
        unfolding f_poly_def eq[symmetric] by (subst nonzero_mult_div_cancel_right) auto
    qed
  
    define f :: "complex \<Rightarrow> complex \<Rightarrow> complex"
      where "f = (\<lambda>\<alpha> x. l^(n*p) * (\<Prod>\<alpha>'\<in>Roots'. (x - \<alpha>')^(if \<alpha>' = \<alpha> then p - 1 else p)))"
    have eval_f: "poly (f_poly \<alpha>) x = f \<alpha> x" if "\<alpha> \<in> Roots'" for \<alpha> x
      using that by (simp add: f_poly_altdef poly_prod f_def)
    have deg_f: "Polynomial.degree (f_poly \<alpha>) = n * p - 1" if "\<alpha> \<in> Roots'" for \<alpha>
    proof -
      have "Polynomial.degree (f_poly \<alpha>) = p - 1 + (n - 1) * p"
        unfolding f_poly_altdef[OF that] using that \<open>l > 0\<close> \<open>finite Roots'\<close>
        by (subst prod.If_eq) (auto simp: degree_prod_eq degree_power_eq degree_mult_eq n_altdef)
      also have "p - 1 + (n - 1) * p = n * p - 1"
        using \<open>n > 0\<close> \<open>p > 1\<close> by (cases n) auto
      finally show ?thesis .
    qed
    
    define I :: "complex \<Rightarrow> complex \<Rightarrow> complex"
      where "I = (\<lambda>\<alpha> x. lindemann_weierstrass_aux.I (f_poly \<alpha>) x)"
    define J :: "complex \<Rightarrow> complex"
      where "J = (\<lambda>\<alpha>. \<Sum>q\<in>P. \<beta> q * (\<Sum>x\<in>Roots q. I \<alpha> x))"
    define J' :: complex
      where "J' = (\<Prod>\<alpha>\<in>Roots'. J \<alpha>)"
  
    have J_eq: "J \<alpha> = -(\<Sum>q\<in>P. of_int (\<beta> q) * (\<Sum>x\<in>Roots q. \<Sum>j<n*p. poly ((pderiv ^^ j) (f_poly \<alpha>)) x))"
      if "\<alpha> \<in> Roots'" for \<alpha>
    proof -
      have "n * p \<ge> 1 * 2"
        using \<open>n > 0\<close> \<open>p > 1\<close> by (intro mult_mono) auto
      hence [simp]: "{..n*p-Suc 0} = {..<n*p}"
        by auto
      have "J \<alpha> = (\<Sum>q\<in>P. \<beta> q * (\<Sum>x\<in>Roots q. I \<alpha> x))"
        unfolding J_def ..
      also have "\<dots> = (\<Sum>q\<in>P. of_int (\<beta> q) * (\<Sum>x\<in>Roots q. exp x * (\<Sum>j<n*p. poly ((pderiv ^^ j) (f_poly \<alpha>)) 0))) -
                      (\<Sum>q\<in>P. of_int (\<beta> q) * (\<Sum>x\<in>Roots q. \<Sum>j<n*p. poly ((pderiv ^^ j) (f_poly \<alpha>)) x))"
        unfolding I_def lindemann_weierstrass_aux.I_def
        by (simp add: deg_f that ring_distribs sum_subtractf sum_distrib_left sum_distrib_right mult_ac)
      also have "\<dots> = -(\<Sum>q\<in>P. of_int (\<beta> q) * (\<Sum>x\<in>Roots q. \<Sum>j<n*p. poly ((pderiv ^^ j) (f_poly \<alpha>)) x))"
        unfolding sum_distrib_right [symmetric] mult.assoc [symmetric] sum_eq_0 by simp
      finally show ?thesis .
    qed
  
    have J: "fact (p - 1) alg_dvd J \<alpha>" "\<not>of_nat p alg_dvd J \<alpha>" if \<alpha>: "\<alpha> \<in> Roots'" for \<alpha>
    proof -
      define h where "h = (\<lambda>\<alpha>' j. poly ((pderiv ^^ j) (f_poly \<alpha>)) \<alpha>')"
      from \<alpha> obtain q where q: "q \<in> P" "\<alpha> \<in> Roots q"
        by (auto simp: Roots'_def)
  
      have "J \<alpha> = -(\<Sum>(q, \<alpha>')\<in>Sigma P Roots. \<Sum>j<n*p. of_int (\<beta> q) * h \<alpha>' j)"
        unfolding J_eq[OF \<alpha>] h_def sum_distrib_left by (subst (2) sum.Sigma) auto
      also have "\<dots> = -(\<Sum>((q,\<alpha>'),i)\<in>Sigma P Roots\<times>{..<n*p}. of_int (\<beta> q) * h \<alpha>' i)"
        by (subst (2) sum.Sigma [symmetric]) (auto simp: case_prod_unfold)
      finally have J_eq': "J \<alpha> = - (\<Sum>((q, \<alpha>'), i)\<in>Sigma P Roots \<times> {..<n * p}. of_int (\<beta> q) * h \<alpha>' i)" .
  
      have h_\<alpha>_pm1_eq: "h \<alpha> (p-1) = of_int (l^(n*p)) * fact (p-1) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (\<alpha>-\<alpha>')^p)"
      proof -
        have "h \<alpha> (p - 1) = of_int (l ^ (n * p)) *
                poly ((pderiv ^^ (p-1)) (\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>',1:] ^ (if \<alpha>' = \<alpha> then p - 1 else p))) \<alpha>"
          unfolding h_def f_poly_altdef[OF \<alpha>] higher_pderiv_smult poly_smult ..
        also have "(\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>',1:] ^ (if \<alpha>' = \<alpha> then p - 1 else p)) =
                    [:-\<alpha>,1:]^(p-1) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. [:-\<alpha>',1:]^p)"
          using \<alpha> by (subst prod.If_eq) auto
        also have "poly ((pderiv ^^ (p-1)) \<dots>) \<alpha> = fact (p - 1) * (\<Prod>\<alpha>'\<in>Roots' - {\<alpha>}. (\<alpha> - \<alpha>') ^ p)"
          by (subst poly_higher_pderiv_aux2) (simp_all add: poly_prod)
        finally show ?thesis by (simp only: mult.assoc)
      qed
  
      have "fact (p-1) alg_dvd h \<alpha> (p-1)"
      proof -
        have "fact (p-1) alg_dvd fact (p-1) * (of_int (l^p) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (l*\<alpha>-l*\<alpha>')^p))"
          by (intro alg_dvd_triv_left algebraic_int_times[of "of_int (l^p)"]
                    algebraic_int_prod algebraic_int_power algebraic_int_diff
                    alg_int \<alpha> algebraic_int_of_int) auto
        also have "(\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (l*\<alpha>-l*\<alpha>')^p) = (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. of_int l^p * (\<alpha>-\<alpha>')^p)"
          by (subst power_mult_distrib [symmetric]) (simp_all add: algebra_simps)
        also have "\<dots> = of_int (l ^ (p * (n-1))) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (\<alpha>-\<alpha>')^p)"
          using \<alpha> by (subst prod.distrib) (auto simp: card_Diff_subset n_altdef simp flip: power_mult)
        also have "of_int (l^p) * \<dots> = of_int (l^(p+p*(n-1))) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (\<alpha>-\<alpha>')^p)"
          unfolding mult.assoc [symmetric] power_add [symmetric] of_int_power ..
        also have "p + p * (n - 1) = n * p"
          using \<open>n > 0\<close> by (cases n) (auto simp: mult_ac)
        also have "fact (p - 1) * (of_int (l^(n*p)) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (\<alpha>-\<alpha>')^p)) = h \<alpha> (p-1)"
          unfolding h_\<alpha>_pm1_eq by (simp add: mult_ac)
        finally show ?thesis .
      qed
 
      have "\<not>of_nat p alg_dvd of_int (\<beta> q) * h \<alpha> (p-1)"
        unfolding h_\<alpha>_pm1_eq mult.assoc [symmetric] of_int_mult [symmetric]
      proof
        define r where "r = (\<lambda>\<alpha>. of_int (l^n) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. \<alpha>-\<alpha>'))"
        have alg_int_r: "algebraic_int (r \<alpha>)" if "\<alpha> \<in> Roots'" for \<alpha>
        proof -
          have "algebraic_int (of_int l * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. of_int l * \<alpha> - of_int l * \<alpha>'))"
            by (intro algebraic_int_times[OF algebraic_int_of_int] algebraic_int_prod 
                      algebraic_int_power algebraic_int_diff alg_int that) auto
          also have "\<dots> = of_int l * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. of_int l * (\<alpha> - \<alpha>'))"
            by (simp add: algebra_simps flip: power_mult_distrib)
          also have "\<dots> = of_int (l^(1 + (n-1))) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. \<alpha> - \<alpha>')"
            using that by (simp add: r_def prod.distrib card_Diff_subset
                                     n_altdef power_add mult_ac flip: power_mult)
          also have "1 + (n - 1) = n"
            using \<open>n > 0\<close> by auto
          finally show "algebraic_int (r \<alpha>)"
            unfolding r_def .
        qed

        have "(\<Prod>\<alpha>'\<in>Roots'. r \<alpha>') \<in> \<rat>"
        proof -
          obtain Root where Root_bij: "bij_betw Root {..<n} Roots'"
            using ex_bij_betw_nat_finite[OF \<open>finite Roots'\<close>] unfolding n_altdef atLeast0LessThan by metis
          have Root_in_Roots': "Root i \<in> Roots'" if "i < n" for i
            using Root_bij that by (auto simp: bij_betw_def)

          define R :: "complex mpoly" where
            "R = (\<Prod>i<n. Const (of_int (l^n)) * (\<Prod>j\<in>{..<n}-{i}. Var i - Var j))"
          have "insertion Root R \<in> \<rat>"
          proof (rule symmetric_poly_of_roots_in_subring)
            show "symmetric_mpoly {..<n} R"
              unfolding R_def
            proof (rule symmetric_mpoly_symmetric_prod'[of _ "\<lambda>\<pi>. \<pi>"], goal_cases)
              case (2 i \<pi>)
              from \<open>\<pi> permutes {..<n}\<close> have [simp]: "bij \<pi>"
                by (rule permutes_bij)
              have "mpoly_map_vars \<pi> (Const (of_int (l ^ n)) *
                      (\<Prod>j\<in>{..<n} - {i}. Var i - Var j):: complex mpoly) =
                    Const (of_int l ^ n) * (\<Prod>j\<in>{..<n} - {i}. Var (\<pi> i) - Var (\<pi> j))"
                by simp
              also have "(\<Prod>j\<in>{..<n} - {i}. Var (\<pi> i) - Var (\<pi> j)) =
                         (\<Prod>j\<in>{..<n} - {\<pi> i}. Var (\<pi> i) - Var j)"
                using 2 permutes_in_image[OF 2(2), of i]
                by (intro prod.reindex_bij_betw bij_betw_Diff permutes_imp_bij[OF 2(2)])
                   (auto simp: bij_betw_singleton)
              finally show ?case by simp
            qed
          next
            show "vars R \<subseteq> {..<n}" unfolding R_def
              by (intro order.trans[OF vars_prod] UN_least order.trans[OF vars_mult]
                        Un_least order.trans[OF vars_power] order.trans[OF vars_diff])
                 (auto simp: vars_Var)
          next
            show "ring_closed (\<rat> :: complex set)"
              by unfold_locales auto
            then interpret ring_closed "\<rat> :: complex set" .              
            show "\<forall>m. MPoly_Type.coeff R m \<in> \<rat>"
              unfolding R_def
              by (intro allI coeff_prod_closed coeff_mult_closed coeff_power_closed)
                 (auto simp: mpoly_coeff_Const coeff_Var when_def)
          next
            let ?lc = "of_int (\<Prod>p\<in>P. Polynomial.lead_coeff p) :: complex"
            have "(\<Prod>q\<in>P. of_int_poly q) = (\<Prod>q\<in>P. Polynomial.smult
                    (of_int (Polynomial.lead_coeff q)) (\<Prod>x\<in>Roots q. [:-x, 1:]))"
              by (intro prod.cong of_int_poly_P refl)
            also have "\<dots> = Polynomial.smult ?lc (\<Prod>q\<in>P. \<Prod>x\<in>Roots q. [:-x, 1:])"
              by (simp add: prod_smult)
            also have "(\<Prod>q\<in>P. \<Prod>x\<in>Roots q. [:-x, 1:]) = (\<Prod>x\<in>Roots'. [:-x, 1:])"
              unfolding Roots'_def using disjoint
              by (intro prod.UNION_disjoint [symmetric]) (auto simp: disjoint_family_on_def)
            also have "\<dots> = (\<Prod>i<n. [:- Root i, 1:])"
              by (intro prod.reindex_bij_betw [symmetric] Root_bij)
            finally show "of_int_poly (\<Prod>P) = Polynomial.smult ?lc (\<Prod>i<n. [:- Root i, 1:])"
              by (simp add: of_int_poly_hom.hom_prod)
            have "prod Polynomial.lead_coeff P \<noteq> 0"
              by (intro prod_nonzeroI) auto
            thus "inverse ?lc * ?lc = 1" "inverse ?lc \<in> \<rat>"
              by (auto simp: field_simps simp flip: of_int_prod)
          qed auto
          also have "insertion Root R = (\<Prod>i<n. of_int (l^n) * (\<Prod>j\<in>{..<n}-{i}. Root i - Root j))"
            by (simp add: R_def insertion_prod insertion_mult insertion_power insertion_diff)
          also have "\<dots> = (\<Prod>i<n. of_int (l^n) * (\<Prod>\<alpha>'\<in>Roots'-{Root i}. Root i - \<alpha>'))"
          proof (intro prod.cong, goal_cases)
            case (2 i)
            hence "(\<Prod>j\<in>{..<n}-{i}. Root i - Root j) = (\<Prod>\<alpha>'\<in>Roots'-{Root i}. Root i - \<alpha>')"
              by (intro prod.reindex_bij_betw bij_betw_Diff Root_bij)
                 (auto intro: Root_in_Roots' simp: bij_betw_singleton)
            thus ?case by simp
          qed auto
          also have "\<dots> = (\<Prod>\<alpha>'\<in>Roots'. r \<alpha>')"
            unfolding r_def by (intro prod.reindex_bij_betw Root_bij)
          finally show "(\<Prod>\<alpha>'\<in>Roots'. r \<alpha>') \<in> \<rat>" .
        qed
        moreover have "algebraic_int (\<Prod>\<alpha>'\<in>Roots'. r \<alpha>')"
          by (intro algebraic_int_prod alg_int_r)
        ultimately have is_int: "(\<Prod>\<alpha>'\<in>Roots'. r \<alpha>') \<in> \<int>"
          using rational_algebraic_int_is_int by blast
        then obtain R' where R': "(\<Prod>\<alpha>'\<in>Roots'. r \<alpha>') = of_int R'"
          by (elim Ints_cases)
        have "(\<Prod>\<alpha>'\<in>Roots'. r \<alpha>') \<noteq> 0"
          using \<open>l > 0\<close> by (intro prod_nonzeroI) (auto simp: r_def \<open>finite Roots'\<close>)
        with R' have [simp]: "R' \<noteq> 0"
          by auto

        assume "of_nat p alg_dvd of_int (\<beta> q * l^(n*p)) * fact (p-1) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (\<alpha>-\<alpha>') ^ p)"
        also have "\<dots> = of_int (\<beta> q) * fact (p-1) * r \<alpha> ^ p"
          by (simp add: r_def mult_ac power_mult_distrib power_mult prod_power_distrib)
        also have "\<dots> alg_dvd of_int (\<beta> q) * fact (p-1) * r \<alpha> ^ p * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. r \<alpha>') ^ p"
          by (intro alg_dvd_triv_left algebraic_int_prod alg_int_r algebraic_int_power) auto
        also have "\<dots> = of_int (\<beta> q) * fact (p-1) * (\<Prod>\<alpha>'\<in>Roots'. r \<alpha>') ^ p"
          using \<alpha> by (subst (2) prod.remove[of _ "\<alpha>"]) (auto simp: mult_ac power_mult_distrib)
        also have "\<dots> = of_int (\<beta> q * fact (p - 1) * R' ^ p)"
          by (simp add: R')
        also have "of_nat p = of_int (int p)"
          by simp
        finally have "int p dvd \<beta> q * fact (p - 1) * R' ^ p" 
          by (subst (asm) alg_dvd_of_int_iff)
        moreover have "prime (int p)"
          using \<open>prime p\<close> by auto
        ultimately have "int p dvd \<beta> q \<or> int p dvd fact (p - 1) \<or> int p dvd R' ^ p"
          by (simp add: prime_dvd_mult_iff)
        moreover have "\<not>int p dvd \<beta> q"
        proof
          assume "int p dvd \<beta> q"
          hence "int p \<le> \<bar>\<beta> q\<bar>"
            using \<beta>_nz[of q] dvd_imp_le_int[of "\<beta> q" "int p"] q by auto
          with p_ineqs(1) q show False by auto
        qed
        moreover have "\<not>int p dvd fact (p - 1)"
        proof -
          have "\<not>p dvd fact (p - 1)"
            using \<open>p > 1\<close> p by (subst prime_dvd_fact_iff) auto
          hence "\<not>int p dvd int (fact (p - 1))"
            by (subst int_dvd_int_iff)
          thus ?thesis unfolding of_nat_fact .
        qed
        moreover have "\<not>int p dvd R' ^ p"
        proof
          assume "int p dvd R' ^ p"
          hence "int p dvd R'"
            using \<open>prime (int p)\<close> prime_dvd_power by metis
          hence "int p \<le> \<bar>R'\<bar>"
            using \<beta>_nz[of q] dvd_imp_le_int[of R' "int p"] q by auto
          hence "real p \<le> real_of_int \<bar>R'\<bar>"
            by linarith
          also have "\<dots> = norm (\<Prod>\<alpha>\<in>Roots'. r \<alpha>)"
            unfolding R' by simp
          finally show False unfolding r_def using p_ineqs(2)
            by linarith
        qed
        ultimately show False
          by blast
      qed
  
      have fact_p_dvd: "fact p alg_dvd h \<alpha>' j" if "\<alpha>' \<in> Roots'" "\<alpha>' \<noteq> \<alpha> \<or> j \<noteq> p - 1" for \<alpha>' j
      proof (cases "j \<ge> p")
        case False
        with that have j: "j < (if \<alpha>' = \<alpha> then p - 1 else p)"
          by auto
        have "h \<alpha>' j = 0"
          unfolding h_def f_poly_altdef[OF \<alpha>]
          by (intro poly_higher_pderiv_aux1'[OF j] dvd_smult dvd_prodI that) auto
        thus ?thesis by simp
      next
        case True
        define e where "e = (\<lambda>x. if x = \<alpha> then p - 1 else p)"
        define Q where "Q = (\<Prod>x\<in>Roots'. [:-x, 1:] ^ e x)"
        define Q' where "Q' = Polynomial.smult (of_int (l^(n*p+j))) (pcompose Q [:0, 1 / of_int l:])"
        have "poly ((pderiv ^^ j) Q) \<alpha>' / l ^ j =
                poly ((pderiv ^^ j) (pcompose Q [:0, 1 / of_int l:])) (l * \<alpha>')"
          using \<open>l > 0\<close> by (simp add: higher_pderiv_pcompose_linear poly_pcompose field_simps)

        have "sum e Roots' = (n - 1) * p + (p - 1)"
          unfolding e_def using \<alpha>
          by (subst sum.If_eq) (auto simp: card_Diff_subset n_altdef algebra_simps)
        also have "\<dots> = n * p - 1"
          using \<open>n > 0\<close> \<open>p > 1\<close> by (cases n) auto
        finally have [simp]: "sum e Roots' = n * p - 1" .

        have "h \<alpha>' j = of_int (l^(n*p)) * poly ((pderiv ^^ j) Q) \<alpha>'"
          unfolding h_def f_poly_altdef[OF \<alpha>] higher_pderiv_smult poly_smult e_def Q_def ..
        also have "poly ((pderiv ^^ j) Q) \<alpha>' =
                     of_int l ^ j * poly ((pderiv ^^ j) (pcompose Q [:0, 1 / of_int l:])) (l * \<alpha>')"
          using \<open>l > 0\<close> by (simp add: higher_pderiv_pcompose_linear poly_pcompose field_simps)
        also have "of_int (l ^ (n * p)) * \<dots> = poly ((pderiv ^^ j) Q') (l * \<alpha>')"
          by (simp add: Q'_def higher_pderiv_smult power_add)
        also have "fact p alg_dvd \<dots>"
        proof (rule fact_alg_dvd_poly_higher_pderiv)
          show "j \<ge> p" by fact
          show "algebraic_int (of_int l * \<alpha>')"
            by (rule alg_int) fact
          interpret alg_int: ring_closed "{x::complex. algebraic_int x}"
            by standard auto
          show "algebraic_int (poly.coeff Q' i)" for i
          proof (cases "i \<le> Polynomial.degree Q'")
            case False
            thus ?thesis
              by (simp add: coeff_eq_0)
          next
            case True
            hence "i \<le> n * p - 1" using \<open>l > 0\<close>
              by (simp add: Q'_def degree_prod_eq Q_def degree_power_eq)
            also have "n * p > 0"
              using \<open>n > 0\<close> \<open>p > 1\<close> by auto
            hence "n * p - 1 < n * p"
              by simp
            finally have i: "i < n * p" .

            have "poly.coeff Q' i = of_int l ^ (n * p + j) / of_int l ^ i * poly.coeff Q i"
              by (simp add: Q'_def coeff_pcompose_linear field_simps)
            also have "of_int l ^ (n * p + j) = (of_int l ^ (n * p + j - i) :: complex) * of_int l ^ i"
              unfolding power_add [symmetric] using i by simp
            hence "of_int l ^ (n * p + j) / of_int l ^ i = (of_int l ^ (n * p + j - i) :: complex)"
              using \<open>l > 0\<close> by (simp add: field_simps)
            also have "\<dots> * poly.coeff Q i =
                (\<Sum>X\<in>{X. X \<subseteq> (SIGMA x:Roots'. {..<e x}) \<and> i = n * p - Suc (card X)}.
                of_int l ^ (n * p + j - (n * p - Suc (card X))) * ((- 1) ^ card X * prod fst X))"
              unfolding Q_def by (subst coeff_prod_linear_factors) (auto simp: sum_distrib_left)
            also have "algebraic_int \<dots>"
            proof (intro algebraic_int_sum, goal_cases)
              case (1 X)
              hence X: "X \<subseteq> (SIGMA x:Roots'. {..<e x})"
                by auto
              have card_eq: "card (SIGMA x:Roots'. {..<e x}) = n * p - 1"
                by (subst card_SigmaI) auto
              from X have "card X \<le> card (SIGMA x:Roots'. {..<e x})"
                by (intro card_mono) auto
              hence "card X \<le> n * p - 1"
                using card_eq by auto
              also have "\<dots> < n * p"
                using  \<open>n * p > 0\<close> by simp
              finally have card_less: "card X < n * p" .
              have "algebraic_int ((-1) ^ card X * of_int l ^ (j + 1) * (\<Prod>x\<in>X. of_int l * fst x))"
                using X by (intro algebraic_int_times algebraic_int_prod alg_int) auto
              thus ?case
                using card_less by (simp add: power_add prod.distrib mult_ac)
            qed
            finally show ?thesis .
          qed
        qed
        finally show ?thesis .
      qed
  
      have p_dvd: "of_nat p alg_dvd h \<alpha>' j" if "\<alpha>' \<in> Roots'" "\<alpha>' \<noteq> \<alpha> \<or> j \<noteq> p - 1" for \<alpha>' j
      proof -
        have "of_nat p alg_dvd (of_nat (fact p) :: complex)"
          by (intro alg_dvd_of_nat dvd_fact) (use \<open>p > 1\<close> in auto)
        hence "of_nat p alg_dvd (fact p :: complex)"
          by simp
        also have "\<dots> alg_dvd h \<alpha>' j"
          using that by (intro fact_p_dvd)
        finally show ?thesis .
      qed
  
      show "fact (p - 1) alg_dvd J \<alpha>"
        unfolding J_eq'
      proof (intro alg_dvd_uminus_right alg_dvd_sum, safe intro!: alg_dvd_mult algebraic_int_of_int)
        fix q \<alpha>' j
        assume "q \<in> P" "\<alpha>' \<in> Roots q" "j < n * p"
        hence "\<alpha>' \<in> Roots'"
          by (auto simp: Roots'_def)
        show "fact (p - 1) alg_dvd h \<alpha>' j"
        proof (cases "\<alpha>' = \<alpha> \<and> j = p - 1")
          case True
          thus ?thesis using \<open>fact (p - 1) alg_dvd h \<alpha> (p - 1)\<close>
            by simp
        next
          case False
          have "of_int (fact (p - 1)) alg_dvd (of_int (fact p) :: complex)"
            by (intro alg_dvd_of_int fact_dvd) auto
          hence "fact (p - 1) alg_dvd (fact p :: complex)"
            by simp
          also have "\<dots> alg_dvd h \<alpha>' j"
            using False \<open>\<alpha>' \<in> Roots'\<close> by (intro fact_p_dvd) auto
          finally show ?thesis .
        qed
      qed
  
      show "\<not>of_nat p alg_dvd J \<alpha>"
        unfolding J_eq' alg_dvd_uminus_right_iff
      proof (rule not_alg_dvd_sum)
        have "p - 1 < 1 * p"
          using \<open>p > 1\<close> by simp
        also have "1 * p \<le> n * p"
          using \<open>n > 0\<close> by (intro mult_right_mono) auto
        finally show "((q, \<alpha>), p - 1) \<in> Sigma P Roots \<times> {..<n*p}"
          using q \<open>n > 0\<close> by auto
      next
        fix z assume z: "z \<in> Sigma P Roots \<times> {..<n*p}-{((q,\<alpha>),p-1)}"
        from z have "snd (fst z) \<in> Roots'"
          by (auto simp: Roots'_def)
        moreover have "fst (fst z) = q" if "\<alpha> \<in> Roots (fst (fst z))"
        proof -
          have "\<alpha> \<in> Roots (fst (fst z)) \<inter> Roots q" "q \<in> P" "fst (fst z) \<in> P"
            using that q z by auto
          with disjoint show ?thesis
            unfolding disjoint_family_on_def by blast
        qed
        ultimately have "of_nat p alg_dvd h (snd (fst z)) (snd z)"
          using z by (intro p_dvd) auto
        thus  "of_nat p alg_dvd (case z of (x, xa) \<Rightarrow> (case x of (q, \<alpha>') \<Rightarrow> \<lambda>i. of_int (\<beta> q) * h \<alpha>' i) xa)"
          using z by auto
      qed (use \<open>\<not>of_nat p alg_dvd of_int (\<beta> q) * h \<alpha> (p-1)\<close> in auto)
    qed

    define g :: "int poly poly"
      where "g = synthetic_div (map_poly (\<lambda>x. [:x:])
                   ((Polynomial.smult lc_factor (\<Prod>P)) ^ p)) [:0, 1:]"
    have g: "map_poly (\<lambda>p. ipoly p \<alpha>) g = f_poly \<alpha>" if \<alpha>: "\<alpha> \<in> Roots'" for \<alpha>
    proof -
      interpret \<alpha>: comm_ring_hom "\<lambda>p. ipoly p \<alpha>"
        by standard (auto simp: of_int_hom.poly_map_poly_eval_poly of_int_poly_hom.hom_mult)
      define Q :: "int poly" where "Q = (Polynomial.smult lc_factor (\<Prod>P)) ^ p"
      have "f_poly \<alpha> = Polynomial.smult (of_int (l^(n*p))) ((\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>',1:])^p) div [:-\<alpha>,1:]"
        unfolding f_poly_def div_smult_left [symmetric] prod_power_distrib[symmetric] ..
      also have "of_int (l^(n*p)) = (of_int l^n)^p"
        by (simp add: power_mult)
      also have "Polynomial.smult \<dots> ((\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>',1:])^p) =
                   (Polynomial.smult (of_int l ^ n) (\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>',1:])) ^ p"
        by (simp only: smult_power)
      also have "\<dots> = of_int_poly Q"
        by (subst lc_factor) (simp_all add: Q_def of_int_poly_hom.hom_power)
      also have "\<dots> div [:-\<alpha>, 1:] = synthetic_div (of_int_poly Q) \<alpha>"
        unfolding synthetic_div_altdef ..
      also have "\<dots> = synthetic_div (map_poly (\<lambda>p. ipoly p \<alpha>) (map_poly (\<lambda>x. [:x:]) Q)) (ipoly [:0, 1:] \<alpha>)"
        by (simp add: map_poly_map_poly o_def)
      also have "\<dots> = map_poly (\<lambda>p. ipoly p \<alpha>) g"
        unfolding g_def Q_def by (rule \<alpha>.synthetic_div_hom)
      finally show ?thesis ..
    qed

    obtain Q where Q: "J \<alpha> = -(\<Sum>q\<in>P. of_int (\<beta> q) * eval_poly of_rat (Q q) \<alpha>)"
      if "\<alpha> \<in> Roots'" for \<alpha>
    proof -
      define g' :: "nat \<Rightarrow> complex poly poly"
        where "g' = (\<lambda>j.  (map_poly of_int_poly ((pderiv ^^ j) g)))"
      obtain root :: "int poly \<Rightarrow> nat \<Rightarrow> complex"
        where root: "\<And>q. q \<in> P \<Longrightarrow> bij_betw (root q) {..<\<sharp>q} (Roots q)"
        using ex_bij_betw_nat_finite[OF finite_Roots] unfolding n_roots_def atLeast0LessThan
        by metis
      have "\<exists>Q'. map_poly of_rat Q' = (\<Sum>x\<in>Roots q. poly (g' j) [:x:])" if q: "q \<in> P" for q j
      proof -
        define Q :: "nat \<Rightarrow> complex poly mpoly"
          where "Q = (\<lambda>j. (\<Sum>i<\<sharp>q. mpoly_of_poly i (g' j)))"
        define ratpolys :: "complex poly set" where "ratpolys = {p. \<forall>i. poly.coeff p i \<in> \<rat>}"
        have "insertion ((\<lambda>x. [:x:]) \<circ> root q) (Q j) \<in> ratpolys"
        proof (rule symmetric_poly_of_roots_in_subring)
          show "ring_closed ratpolys"
            by standard (auto simp: ratpolys_def intro!: coeff_mult_semiring_closed)
          show "\<forall>m. MPoly_Type.coeff (Q j) m \<in> ratpolys"
            by (auto simp: Q_def ratpolys_def Polynomial.coeff_sum coeff_mpoly_of_poly when_def g'_def
                     intro!: sum_in_Rats)
          show "vars (Q j) \<subseteq> {..<\<sharp>q}" unfolding Q_def
            by (intro order.trans[OF vars_sum] UN_least order.trans[OF vars_mpoly_of_poly]) auto
          show "symmetric_mpoly {..<\<sharp>q} (Q j)" unfolding Q_def
            by (rule symmetric_mpoly_symmetric_sum[of _ id]) (auto simp: permutes_bij)
          interpret coeff_lift_hom: map_poly_idom_hom "\<lambda>x. [:x:]"
            by standard
          define lc :: complex where "lc = of_int (Polynomial.lead_coeff q)"
          have "of_int_poly q = Polynomial.smult (Polynomial.lead_coeff q) (\<Prod>x\<in>Roots q. [:-x, 1:])"
            by (rule of_int_poly_P) fact
          also have "poly_lift \<dots> = Polynomial.smult [:lc:] (\<Prod>a\<in>Roots q. [:-[:a:], 1:])"
            by (simp add: poly_lift_def map_poly_smult coeff_lift_hom.hom_prod lc_def)
          also have "(\<Prod>a\<in>Roots q. [:-[:a:], 1:]) = (\<Prod>i<\<sharp>q. [:-[:root q i:], 1:])"
            by (intro prod.reindex_bij_betw [symmetric] root q)
          also have "\<dots> = (\<Prod>i<\<sharp>q. [:- ((\<lambda>x. [:x:]) \<circ> root q) i, 1:])"
            by simp
          finally show "poly_lift (Ring_Hom_Poly.of_int_poly q) = Polynomial.smult [:lc:] \<dots>" .
          have "lc \<noteq> 0"
            using q by (auto simp: lc_def)
          thus "[:inverse lc:] * [:lc:] = 1"
            by (simp add: field_simps)
        qed (auto simp: ratpolys_def coeff_pCons split: nat.splits)

        also have "insertion ((\<lambda>x. [:x:]) \<circ> root q) (Q j) = (\<Sum>i<\<sharp>q. poly (g' j) [:root q i:])"
          by (simp add: Q_def insertion_sum poly_sum)
        also have "\<dots> = (\<Sum>x\<in>Roots q. poly (g' j) [:x:])"
          by (intro sum.reindex_bij_betw root q)
        finally have "\<forall>i. poly.coeff (\<Sum>x\<in>Roots q. poly (g' j) [:x:]) i \<in> \<rat>"
          by (auto simp: ratpolys_def)
        thus ?thesis
          using ratpolyE by metis
      qed
      then obtain Q where Q: "\<And>q j. q \<in> P \<Longrightarrow> map_poly of_rat (Q q j) = (\<Sum>x\<in>Roots q. poly (g' j) [:x:])"
        by metis
      define Q' where "Q' = (\<lambda>q. \<Sum>j<n*p. Q q j)"

      have "J \<alpha> = - (\<Sum>q\<in>P. of_int (\<beta> q) * eval_poly of_rat (Q' q) \<alpha>)" if \<alpha>: "\<alpha> \<in> Roots'" for \<alpha>
      proof -
        have "J \<alpha> = -(\<Sum>q\<in>P. of_int (\<beta> q) * (\<Sum>x\<in>Roots q. \<Sum>j<n * p. poly ((pderiv ^^ j) (f_poly \<alpha>)) x))"
          (is "_ = -?S") unfolding J_eq[OF \<alpha>] ..
        also have "?S = (\<Sum>q\<in>P. of_int (\<beta> q) * eval_poly of_rat (Q' q) \<alpha>)"
        proof (rule sum.cong, goal_cases)
          case q: (2 q)
          interpret \<alpha>: idom_hom "\<lambda>p. ipoly p \<alpha>"
            by standard (auto simp: of_int_hom.poly_map_poly_eval_poly of_int_poly_hom.hom_mult)
  
          have "(\<Sum>x\<in>Roots q. \<Sum>j<n * p. poly ((pderiv ^^ j) (f_poly \<alpha>)) x) =
                (\<Sum>j<n * p. \<Sum>x\<in>Roots q. poly ((pderiv ^^ j) (f_poly \<alpha>)) x)"
            by (rule sum.swap)
          also have "\<dots> = (\<Sum>j<n * p. eval_poly of_rat (Q q j) \<alpha>)"
          proof (rule sum.cong, goal_cases)
            case j: (2 j)
            have "(\<Sum>x\<in>Roots q. poly ((pderiv ^^ j) (f_poly \<alpha>)) x) =
                  (\<Sum>x\<in>Roots q. poly (poly (g' j) [:x:]) \<alpha>)"
            proof (rule sum.cong, goal_cases)
              case (2 x)
              have "poly ((pderiv ^^ j) (f_poly \<alpha>)) x =
                    poly ((pderiv ^^ j) (map_poly (\<lambda>p. ipoly p \<alpha>) g)) x"
                by (subst g[OF \<alpha>, symmetric]) (rule refl)
              also have "\<dots> = poly (eval_poly ((\<lambda>p. [:poly p \<alpha>:]) \<circ> of_int_poly) ((pderiv ^^ j) g) [:0, 1:]) x"
                unfolding o_def \<alpha>.map_poly_higher_pderiv [symmetric]
                by (simp only: \<alpha>.map_poly_eval_poly)
              also have "\<dots> = poly (eval_poly (\<lambda>p. [:poly p \<alpha>:])
                                (map_poly of_int_poly ((pderiv ^^ j) g)) [:0, 1:]) x"
                unfolding eval_poly_def by (subst map_poly_map_poly) auto
              also have "\<dots> = poly (poly (map_poly of_int_poly ((pderiv ^^ j) g)) [:x:]) \<alpha>"
                by (rule poly_poly_eq [symmetric])
              also have "\<dots> = poly (poly (g' j) [:x:]) \<alpha>"
                by (simp add: g'_def)
              finally show ?case .
            qed auto
            also have "\<dots> = poly (\<Sum>x\<in>Roots q. poly (g' j) [:x:]) \<alpha>"
              by (simp add: poly_sum)
            also have "\<dots> = eval_poly of_rat (Q q j) \<alpha>"
              using q by (simp add: Q eval_poly_def)
            finally show ?case .
          qed auto
          also have "\<dots> = eval_poly of_rat (Q' q) \<alpha>"
            by (simp add: Q'_def of_rat_hom.eval_poly_sum)
          finally show ?case by simp
        qed auto
        finally show "J \<alpha> = - (\<Sum>q\<in>P. of_int (\<beta> q) * eval_poly of_rat (Q' q) \<alpha>)" .
      qed
      thus ?thesis using that[of Q'] by metis
    qed

    have "J' \<in> \<rat>"
    proof -
      have "(\<Prod>\<alpha>\<in>Roots q. J \<alpha>) \<in> \<rat>" if q: "q \<in> P" for q
      proof -
        obtain root where root: "bij_betw root {..<\<sharp>q} (Roots q)"
          using ex_bij_betw_nat_finite[OF finite_Roots[OF q]]
          unfolding atLeast0LessThan n_roots_def by metis
        define Q' :: "complex poly"
          where "Q' = -(\<Sum>q\<in>P. Polynomial.smult (of_int (\<beta> q)) (map_poly of_rat (Q q)))"

        have "(\<Prod>\<alpha>\<in>Roots q. J \<alpha>) = (\<Prod>\<alpha>\<in>Roots q. -(\<Sum>q\<in>P. of_int (\<beta> q) * eval_poly of_rat (Q q) \<alpha>))"
          by (intro prod.cong refl Q) (auto simp: Roots'_def q)
        also have "\<dots> = (\<Prod>\<alpha>\<in>Roots q. poly Q' \<alpha>)"
          by (simp add: Q'_def poly_sum eval_poly_def)
        also have "\<dots> = (\<Prod>i<\<sharp>q. poly Q' (root i))"
          by (intro prod.reindex_bij_betw [symmetric] root)
        also have "\<dots> = insertion root (\<Prod>i<\<sharp>q. mpoly_of_poly i Q')"
          by (simp add: insertion_prod)
        also have "\<dots> \<in> \<rat>"
        proof (rule symmetric_poly_of_roots_in_subring)
          show "ring_closed (\<rat> :: complex set)"
            by standard auto
          then interpret Q: ring_closed "\<rat> :: complex set" .
          show "\<forall>m. MPoly_Type.coeff (\<Prod>i<\<sharp>q. mpoly_of_poly i Q') m \<in> \<rat>"
            by (auto intro!: Q.coeff_prod_closed sum_in_Rats
                     simp: coeff_mpoly_of_poly when_def Q'_def Polynomial.coeff_sum)
          show "symmetric_mpoly {..<\<sharp>q} (\<Prod>i<\<sharp>q. mpoly_of_poly i Q')"
            by (intro symmetric_mpoly_symmetric_prod'[of _ id]) (auto simp: permutes_bij)
          show "vars (\<Prod>i<\<sharp>q. mpoly_of_poly i Q') \<subseteq> {..<\<sharp>q}"
            by (intro order.trans[OF vars_prod] order.trans[OF vars_mpoly_of_poly] UN_least) auto
          define lc where "lc = (of_int (Polynomial.lead_coeff q) :: complex)"
          have "of_int_poly q = Polynomial.smult lc (\<Prod>x\<in>Roots q. [:- x, 1:])"
            unfolding lc_def by (rule of_int_poly_P) fact
          also have "(\<Prod>x\<in>Roots q. [:- x, 1:]) = (\<Prod>i<\<sharp>q. [:- root i, 1:])"
            by (intro prod.reindex_bij_betw [symmetric] root)
          finally show "of_int_poly q = Polynomial.smult lc (\<Prod>i<\<sharp>q. [:- root i, 1:])" .
          have "lc \<noteq> 0"
            using q by (auto simp: lc_def)
          thus "inverse lc * lc = 1" "inverse lc \<in> \<rat>"
            by (auto simp: lc_def)
        qed auto
        finally show ?thesis .
      qed
      hence "(\<Prod>q\<in>P. \<Prod>\<alpha>\<in>Roots q. J \<alpha>) \<in> \<rat>"
        by (rule prod_in_Rats)
      also have "(\<Prod>q\<in>P. \<Prod>\<alpha>\<in>Roots q. J \<alpha>) = J'"
        unfolding Roots'_def J'_def using disjoint
        by (intro prod.UNION_disjoint [symmetric]) (auto simp: disjoint_family_on_def)
      finally show "J' \<in> \<rat>" .
    qed
    moreover have "algebraic_int J'"
      unfolding J'_def 
    proof (intro algebraic_int_prod)
      fix x assume "x \<in> Roots'"
      hence "fact (p - 1) alg_dvd J x"
        by (intro J)
      thus "algebraic_int (J x)"
        by (rule alg_dvd_imp_algebraic_int) auto
    qed
    ultimately have "J' \<in> \<int>"
      using rational_algebraic_int_is_int by blast
  
    have "J' \<noteq> 0"
      unfolding J'_def
    proof (intro prod_nonzeroI)
      fix \<alpha> assume "\<alpha> \<in> Roots'"
      hence "\<not>of_nat p alg_dvd J \<alpha>"
        using J(2)[of \<alpha>] by auto
      thus "J \<alpha> \<noteq> 0"
        by auto
    qed
  
    have "fact (p - 1) ^ n alg_dvd J'"
    proof -
      have "fact (p - 1) ^ n = (\<Prod>\<alpha>\<in>Roots'. fact (p - 1))"
        by (simp add: n_altdef)
      also have "\<dots> alg_dvd J'"
        unfolding J'_def by (intro prod_alg_dvd_prod J(1))
      finally show ?thesis .
    qed
  
    have "fact (p - 1) ^ n \<le> norm J'"
    proof -
      from \<open>J' \<in> \<int>\<close> obtain J'' where [simp]: "J' = of_int J''"
        by (elim Ints_cases)
      have "of_int (fact (p - 1) ^ n) = (fact (p - 1) ^ n :: complex)"
        by simp
      also have "\<dots> alg_dvd J'"
        by fact
      also have "J' = of_int J''"
        by fact
      finally have "fact (p - 1) ^ n dvd J''"
        by (subst (asm) alg_dvd_of_int_iff)
      moreover from \<open>J' \<noteq> 0\<close> have "J'' \<noteq> 0"
        by auto
      ultimately have "\<bar>J''\<bar> \<ge> \<bar>fact (p - 1) ^ n\<bar>"
        by (intro dvd_imp_le_int)
      hence "real_of_int \<bar>J''\<bar> \<ge> real_of_int \<bar>fact (p - 1) ^ n\<bar>"
        by linarith
      also have "real_of_int \<bar>J''\<bar> = norm J'"
        by simp
      finally show ?thesis
        by simp
    qed
  
    also have "norm J' \<le> C' * C p ^ n"
    proof -
      have "norm J' = (\<Prod>x\<in>Roots'. norm (J x))"
        unfolding J'_def prod_norm [symmetric] ..
      also have "\<dots> \<le> (\<Prod>x\<in>Roots'. \<Sum>q\<in>P. real_of_int \<bar>\<beta> q\<bar> * (\<Sum>\<alpha>\<in>Roots q. cmod \<alpha> * exp (cmod \<alpha>) * C p))"
      proof (intro prod_mono conjI)
        fix x assume x: "x \<in> Roots'"
        show "norm (J x) \<le> (\<Sum>q\<in>P. real_of_int \<bar>\<beta> q\<bar> * (\<Sum>\<alpha>\<in>Roots q. norm \<alpha> * exp (norm \<alpha>) * C p))"
          unfolding J_def
        proof (intro sum_norm_le)
          fix q assume "q \<in> P"
          show "norm (of_int (\<beta> q) * sum (I x) (Roots q)) \<le>
                  real_of_int \<bar>\<beta> q\<bar> * (\<Sum>\<alpha>\<in>Roots q. norm \<alpha> * exp (norm \<alpha>) * C p)"
            unfolding norm_mult norm_of_int of_int_abs
          proof (intro mult_left_mono sum_norm_le)
            fix \<alpha> assume "\<alpha> \<in> Roots q"
            hence \<alpha>: "\<alpha> \<in> Roots'"
              using \<open>q \<in> P\<close> by (auto simp: Roots'_def)
            show "norm (I x \<alpha>) \<le> norm \<alpha> * exp (norm \<alpha>) * C p"
              unfolding I_def
            proof (intro lindemann_weierstrass_aux.lindemann_weierstrass_integral_bound)
              fix t assume "t \<in> closed_segment 0 \<alpha>"
              also have "closed_segment 0 \<alpha> \<subseteq> cball 0 R"
                using \<open>R \<ge> 0\<close> R_ge[OF \<alpha>] by (intro closed_segment_subset) auto
              finally have "norm t \<le> R" by simp
  
              have norm_diff_le: "norm (t - y) \<le> 2 * R" if "y \<in> Roots'" for y
              proof -
                have "norm (t - y) \<le> norm t + norm y"
                  by (meson norm_triangle_ineq4)
                also have "\<dots> \<le> R + R"
                  by (intro add_mono[OF \<open>norm t \<le> R\<close> R_ge] that)
                finally show ?thesis by simp
              qed
  
              have "norm (poly (f_poly x) t) =
                      \<bar>real_of_int l\<bar> ^ (n * p) * (\<Prod>y\<in>Roots'. cmod (t - y) ^ (if y = x then p - 1 else p))"
                by (simp add: eval_f x f_def norm_mult norm_power flip: prod_norm)
              also have "\<dots> \<le> \<bar>real_of_int l\<bar> ^ (n * p) * (\<Prod>y\<in>Roots'. (2*R) ^ (if y = x then p - 1 else p))"
                by (intro mult_left_mono prod_mono conjI power_mono norm_diff_le) auto
              also have "\<dots> = \<bar>real_of_int l\<bar>^(n*p) * (2^(p-1) * R^(p-1) * (2^p*R^p)^(n-1))"
                using x by (subst prod.If_eq) (auto simp: card_Diff_subset n_altdef)
              also have "2^(p-1) * R^(p-1) * (2^p*R^p)^(n-1) = (2^((p-1)+p*(n-1))) * (R^((p-1)+p*(n-1)))"
                unfolding power_mult power_mult_distrib power_add by (simp add: mult_ac)
              also have "(p-1)+p*(n-1) = p*n - 1"
                using \<open>n > 0\<close> \<open>p > 1\<close> by (cases n) (auto simp: algebra_simps)
              also have "2 ^ (p * n - 1) * R ^ (p * n - 1) = (2*R)^(n * p-1)"
                unfolding power_mult_distrib by (simp add: mult_ac)
              finally show "norm (poly (f_poly x) t) \<le> C p"
                unfolding C_def using \<open>l > 0\<close> by simp
            qed (use \<open>R \<ge> 0\<close> \<open>l > 0\<close> in \<open>auto simp: C_def\<close>)
          qed auto
        qed
      qed auto
      also have "\<dots> = C' * C p ^ n"
        by (simp add: C'_def power_mult_distrib n_altdef flip: sum_distrib_right mult.assoc)
      finally show ?thesis .
    qed
  
    finally show "fact (p - 1) ^ n \<le> C' * C p ^ n" .
  qed

  text \<open>
    Some simple asymptotic estimates show that this is clearly a contradiction, since
    the left-hand side grows much faster than the right-hand side and there are infinitely many
    sufficiently large primes:
  \<close>
  have freq: "frequently prime sequentially"
    using frequently_prime_cofinite unfolding cofinite_eq_sequentially .
  have ev: "eventually (\<lambda>p. (\<forall>q\<in>P.  int p > \<bar>\<beta> q\<bar>) \<and>
              real p > norm (\<Prod>\<alpha>\<in>Roots'. of_int (l^n) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (\<alpha>-\<alpha>')))) sequentially"
    by (intro eventually_ball_finite \<open>finite P\<close> ballI eventually_conj filterlim_real_sequentially
          eventually_compose_filterlim[OF eventually_gt_at_top] filterlim_int_sequentially)

  have "frequently (\<lambda>p. fact (p - 1) ^ n \<le> C' * C p ^ n) sequentially"
    by (rule frequently_eventually_mono[OF freq ev]) (use ineq in blast)
  moreover have "eventually (\<lambda>p. fact (p - 1) ^ n > C' * C p ^ n) sequentially"
  proof (cases "R = 0")
    case True
    have "eventually (\<lambda>p. p * n > 1) at_top"
      using \<open>n > 0\<close> by real_asymp
    thus ?thesis 
      by eventually_elim (use \<open>n > 0\<close> True in \<open>auto simp: C_def power_0_left mult_ac\<close>)
  next
    case False
    hence "R > 0"
      using \<open>R \<ge> 0\<close> by auto
    define D :: real where "D = (2 * R * \<bar>real_of_int l\<bar>) ^ n" 
    have "D > 0"
      using \<open>R > 0\<close> \<open>l > 0\<close> unfolding D_def by (intro zero_less_power) auto

    have "(\<lambda>p. C' * C p ^ n) \<in> O(\<lambda>p. C p ^ n)"
      by simp
    also have "(\<lambda>p. C p ^ n) \<in> O(\<lambda>p. ((2 * R * l) ^ (n * p)) ^ n)"
    proof (rule landau_o.big_power[OF bigthetaD1])
      have np: "eventually (\<lambda>p::nat. n * p > 1) at_top"
        using \<open>n > 0\<close> by real_asymp
      have "eventually (\<lambda>p. (2 * R) * C p = (2 * R * l) ^ (n * p)) at_top"
        using np
      proof eventually_elim
        case (elim p)
        have "2 * R * C p = l ^ (n * p) * (2 * R) ^ (Suc (n * p - 1))"
          by (simp add: C_def algebra_simps)
        also have "Suc (n * p - 1) = n * p"
          using elim by auto
        finally show ?case
          by (simp add: algebra_simps)
      qed
      hence "(\<lambda>p. (2 * R) * C p) \<in> \<Theta>(\<lambda>p. (2 * R * l) ^ (n * p))"
        by (intro bigthetaI_cong)
      thus "C \<in> \<Theta>(\<lambda>p. (2 * R * l) ^ (n * p))"
        using \<open>R > 0\<close> by simp
    qed
    also have "\<dots> = O(\<lambda>p. (D ^ p) ^ n)"
      using \<open>l > 0\<close> by (simp flip: power_mult add: power2_eq_square mult_ac D_def)
    also have "(\<lambda>p. (D ^ p) ^ n) \<in> o(\<lambda>p. fact (p - 1) ^ n)"
    proof (intro landau_o.small_power)
      have "eventually (\<lambda>p. D ^ p = D * D ^ (p - 1)) at_top"
        using eventually_gt_at_top[of 0]
        by eventually_elim (use \<open>D > 0\<close> in \<open>auto simp flip: power_Suc\<close>)
      hence "(\<lambda>p. D ^ p) \<in> \<Theta>(\<lambda>p. D * D ^ (p - 1))"
        by (intro bigthetaI_cong)
      hence "(\<lambda>p. D ^ p) \<in> \<Theta>(\<lambda>p. D ^ (p - 1))"
        using \<open>D > 0\<close> by simp
      also have "(\<lambda>p. D ^ (p - 1)) \<in> o(\<lambda>p. fact (p - 1))"
        by (intro landau_o.small.compose[OF exponential_smallo_fact]) real_asymp
      finally show "(\<lambda>p. D ^ p) \<in> o(\<lambda>x. fact (x - 1))" .
    qed fact+
    finally have smallo: "(\<lambda>p. C' * C p ^ n) \<in> o(\<lambda>p. fact (p - 1) ^ n)" .
    have "eventually (\<lambda>p. \<bar>C' * C p ^ n\<bar> \<le> 1/2 * fact (p - 1) ^ n) at_top"
      using landau_o.smallD[OF smallo, of "1/2"] by simp
    thus "eventually (\<lambda>p. C' * C p ^ n < fact (p - 1) ^ n) at_top"
    proof eventually_elim
      case (elim p)
      have "C' * C p ^ n \<le> \<bar>C' * C p ^ n\<bar>"
        by simp
      also have "\<dots> \<le> 1/2 * fact (p - 1) ^ n"
        by fact
      also have "\<dots> < fact (p - 1) ^ n"
        by simp
      finally show ?case .
    qed
  qed
  ultimately have "frequently (\<lambda>p::nat. False) sequentially"
    by (rule frequently_eventually_mono) auto
  thus False
    by simp
qed

lemma Hermite_Lindemann_aux2:
  fixes \<alpha> :: "complex set" and \<beta> :: "complex \<Rightarrow> int"
  assumes [intro]: "finite X"
  assumes nz:   "\<And>x. x \<in> X \<Longrightarrow> \<beta> x \<noteq> 0"
  assumes alg:  "\<And>x. x \<in> X \<Longrightarrow> algebraic x"
  assumes sum0: "(\<Sum>\<alpha>\<in>X. of_int (\<beta> x) * exp \<alpha>) = 0"
  shows   "X = {}"
proof (rule ccontr)
  assume "X \<noteq> {}"
  show False
    sorry
qed

theorem Hermite_Lindemann:
  fixes c:: "complex \<Rightarrow> complex"
  assumes [intro]: "finite X"
  assumes alg1: "\<And>x. x \<in> X \<Longrightarrow> algebraic x"
  assumes alg2: "\<And>x. x \<in> X \<Longrightarrow> algebraic (c x)"
  assumes sum0: "(\<Sum>x\<in>X. c x * exp \<alpha>) = 0"
  shows   "\<forall>x\<in>X. c x = 0"
  sorry

end