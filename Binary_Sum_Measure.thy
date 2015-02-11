theory Binary_Sum_Measure
imports Probability
begin

definition sum_measure (infixr "\<Oplus>\<^sub>M" 70) where
  "A \<Oplus>\<^sub>M B = measure_of (space A <+> space B)
                        ({Inl`X |X. X \<in> sets A} \<union> {Inr`X |X. X \<in> sets B})
                        (\<lambda>X. emeasure A (Inl -` X) + emeasure B (Inr -` X))"

lemma sum_measure_closed: 
  "{Inl`X |X. X \<in> sets A} \<union> {Inr`X |X. X \<in> sets B} \<subseteq> Pow (space A <+> space B)"
  using sets.space_closed[of A] sets.space_closed[of B] by (auto intro!: imageI)
  
lemma space_sum_measure: "space (A \<Oplus>\<^sub>M B) = space A <+> space B"
  unfolding sum_measure_def by (rule space_measure_of[OF sum_measure_closed])

  
lemma Inl_vimage_Inr [simp]: "Inl -` Inr ` X = {}"
  and Inr_vimage_Inl [simp]: "Inr -` Inl ` Y = {}"
  by auto
  
lemma sets_sum_measure:
  "sets (sum_measure A B) = {Inl`X \<union> Inr`Y |X Y. X \<in> sets A \<and> Y \<in> sets B}"
proof-
  let ?\<Omega> = "space A <+> space B"
  let ?M = "{Inl`X |X. X \<in> sets A} \<union> {Inr`X |X. X \<in> sets B}"
  let ?M' = "{Inl`X \<union> Inr`Y |X Y. X \<in> sets A \<and> Y \<in> sets B}"
  have "sets (sum_measure A B) = sigma_sets ?\<Omega> ?M" 
    unfolding sum_measure_def using sum_measure_closed by (rule sets_measure_of)
  also have "... = ?M'"
  proof (intro equalityI subsetI)
    fix X assume "X \<in> ?M'"
    then obtain X1 X2 where X: "X = Inl`X1 \<union> Inr`X2" and "X1 \<in> sets A" "X2 \<in> sets B" by auto
    hence X12: "Inl`X1 \<in> ?M" "Inr`X2 \<in> ?M" by blast+
    thus "X \<in> sigma_sets ?\<Omega> ?M"
      by (subst X) (intro sigma_sets_Un[OF sigma_sets.Basic sigma_sets.Basic] X12)
  next
    fix X assume X: "X \<in> sigma_sets ?\<Omega> ?M"
    show "X \<in> ?M'"
    proof (induction rule: sigma_sets.induct[OF X])
      fix X assume "X \<in> ?M"
      thus "X \<in> ?M'" by blast
    next
      show "{} \<in> ?M'" by blast
    next
      fix X assume X: "X \<in> ?M'"
      then obtain X1 X2 where X: "X = Inl`X1 \<union> Inr`X2" and "X1 \<in> sets A" "X2 \<in> sets B" by auto
      hence "Inl`(space A - X1) \<union> Inr`(space B - X2) \<in> ?M'" by auto
      also have "Inl`(space A - X1) \<union> Inr`(space B - X2) = ?\<Omega> - X" by (subst X) blast
      finally show "?\<Omega> - X \<in> ?M'" .
    next
      fix X :: "nat \<Rightarrow> _"
      assume X: "\<And>i. X i \<in> ?M'"
      def X1 \<equiv> "\<lambda>i. Inl -` X i" and X2 \<equiv> "\<lambda>i. Inr -` X i"
      from X have X_decomp: "\<And>i. X i = Inl`X1 i \<union> Inr`X2 i"
        unfolding X1_def X2_def using UNIV_sum by auto
      hence "(\<Union>i. X i) = Inl`(\<Union>i. X1 i) \<union> Inr`(\<Union>i. X2 i)" by auto
      moreover {
        fix i
        from X[of i] have "X1 i \<in> sets A" "X2 i \<in> sets B" unfolding X1_def X2_def 
          by (force simp: inj_vimage_image_eq)+
      }
      hence "(\<Union>i. X1 i) \<in> sets A" "(\<Union>i. X2 i) \<in> sets B" using sets.countable_UN by blast+
      ultimately show "(\<Union>i. X i) \<in> ?M'" by blast
    qed
  qed
  finally show ?thesis .
qed

lemma sets_sum_measure_cong [measurable_cong, cong]:
  "sets M1 = sets M1' \<Longrightarrow> sets M2 = sets M2' \<Longrightarrow> sets (M1 \<Oplus>\<^sub>M M2) = sets (M1' \<Oplus>\<^sub>M M2')"
  unfolding sets_sum_measure by (simp cong: sets_eq_imp_space_eq)

lemma sum_measureI1 [intro, simp, measurable]: "x \<in> sets A \<Longrightarrow> Inl`x \<in> sets (A \<Oplus>\<^sub>M B)"
  and sum_measureI2 [intro, simp, measurable]: "x \<in> sets D \<Longrightarrow> Inr`x \<in> sets (C \<Oplus>\<^sub>M D)"
  by (auto simp: sets_sum_measure)

lemma sum_measureE:
  assumes "x \<in> sets (A \<Oplus>\<^sub>M B)"
  obtains x1 x2 where "x = Inl`x1 \<union> Inr`x2"
  using assms by (subst (asm) sets_sum_measure) blast 
  

lemma measurable_sum_measureI1:
  assumes 1: "f \<in> (space M1 <+> space M2) \<rightarrow> space M"
  assumes 2: "\<And>X. X \<in> sets M \<Longrightarrow> Inl -` f -` X \<inter> space M1 \<in> sets M1"
  assumes 3: "\<And>X. X \<in> sets M \<Longrightarrow> Inr -` f -` X \<inter> space M2 \<in> sets M2"
  shows "f \<in> measurable (M1 \<Oplus>\<^sub>M M2) M"
proof (rule measurableI)
  fix x assume "x \<in> space (M1 \<Oplus>\<^sub>M M2)"
  with 1 show "f x \<in> space M" by (simp add: space_sum_measure Pi_iff)
next
  fix X assume X: "X \<in> sets M"
  have "f -` X = Inl`Inl-`f-`X \<union> Inr`Inr-`f-`X"
    by (subst (1 2) image_vimage_eq, subst Int_Un_distrib[symmetric], subst UNIV_sum[symmetric]) simp
  hence "f -` X \<inter> space (M1 \<Oplus>\<^sub>M M2) = Inl`(Inl-`f-`X \<inter> space M1) \<union> Inr`(Inr-`f-`X \<inter> space M2)"
    by (auto simp: space_sum_measure)
  with 2[OF X] 3[OF X] show "f -` X \<inter> space (M1 \<Oplus>\<^sub>M M2) \<in> sets (M1 \<Oplus>\<^sub>M M2)"
    by (subst sets_sum_measure) blast
qed

lemma measurable_sum_measureI2:
  fixes M1 :: "'a measure" and M2 :: "'b measure"
  assumes 1: "f \<in> space M \<rightarrow> space M1 <+> space M2"
  assumes 2: "\<And>X. X \<in> sets M1 \<Longrightarrow> f -` Inl ` X \<inter> space M \<in> sets M"
  assumes 3: "\<And>X. X \<in> sets M2 \<Longrightarrow> f -` Inr ` X \<inter> space M \<in> sets M"
  shows "f \<in> measurable M (M1 \<Oplus>\<^sub>M M2)"
unfolding sum_measure_def
proof (rule measurable_measure_of)
  show "{Inl ` X |X. X \<in> sets M1} \<union> {Inr ` X |X. X \<in> sets M2} \<subseteq> Pow (space M1 <+> space M2)"
    by (fact sum_measure_closed)
  show "f \<in> space M \<rightarrow> space M1 <+> space M2" by fact
  fix X assume "X \<in> {Inl ` X |X. X \<in> sets M1} \<union> {Inr ` X |X. X \<in> sets M2}"
  thus "f -` X \<inter> space M \<in> sets M" using 2 3 by blast
qed

  
lemma measurable_Inl [measurable]: "Inl \<in> measurable M1 (M1 \<Oplus>\<^sub>M M2)"
  by (rule measurable_sum_measureI2) (auto simp: vimage_image_eq)

lemma measurable_Inr [measurable]: "Inr \<in> measurable M2 (M1 \<Oplus>\<^sub>M M2)"
  by (rule measurable_sum_measureI2) (auto simp: vimage_image_eq)
  
lemma measurable_case_sum [measurable (raw)]:
  "f \<in> measurable M1 M \<Longrightarrow> g \<in> measurable M2 M \<Longrightarrow> case_sum f g \<in> measurable (M1 \<Oplus>\<^sub>M M2) M"
  by (intro measurable_sum_measureI1) (auto dest: measurable_space simp: vimage_comp comp_def)

lemma measurable_sum:
  assumes "f \<circ> Inl \<in> measurable M1 M" "f \<circ> Inr \<in> measurable M2 M"
  shows   "f \<in> measurable (M1 \<Oplus>\<^sub>M M2) M"
proof (rule measurable_sum_measureI1)
  from assms show "f \<in> space M1 <+> space M2 \<rightarrow> space M"
    by (auto simp: comp_def[abs_def] dest: measurable_space )
  fix X assume X: "X \<in> sets M"
  from X and assms show "Inl -` f -` X \<inter> space M1 \<in> sets M1"
                    and "Inr -` f -` X \<inter> space M2 \<in> sets M2" by (auto simp: vimage_comp)
qed

lemma emeasure_sum_measure:
  assumes "A \<in> sets (M1 \<Oplus>\<^sub>M M2)"
  shows   "emeasure (M1 \<Oplus>\<^sub>M M2) A = emeasure M1 (Inl -` A) + emeasure M2 (Inr -` A)"
proof (rule emeasure_measure_of[OF sum_measure_def sum_measure_closed])
  show "A \<in> sets (M1 \<Oplus>\<^sub>M M2)" by fact
  show "positive (sets (M1 \<Oplus>\<^sub>M M2)) (\<lambda>X. emeasure M1 (Inl -` X) + emeasure M2 (Inr -` X))"
    by (auto simp: sets_sum_measure positive_def intro!: ereal_add_nonneg_nonneg)
  show "countably_additive (sets (M1 \<Oplus>\<^sub>M M2)) (\<lambda>X. emeasure M1 (Inl -` X) + emeasure M2 (Inr -` X))"
  proof (rule countably_additiveI)
    fix X :: "nat \<Rightarrow> _"
    assume range_X: "range X \<subseteq> sets (M1 \<Oplus>\<^sub>M M2)"
    assume disj_X:  "disjoint_family X"
    
    def X1 \<equiv> "\<lambda>i. Inl -` X i" and X2 \<equiv> "\<lambda>i. Inr -` X i"
    {
      fix i
      from range_X have "X i \<in> sets (M1 \<Oplus>\<^sub>M M2)" by blast
      hence "X1 i \<in> sets M1" "X2 i \<in> sets M2" unfolding X1_def X2_def
        by (force simp: inj_vimage_image_eq sets_sum_measure)+
    }
    hence range_X12: "range X1 \<subseteq> sets M1" "range X2 \<subseteq> sets M2" by blast+
    from disj_X have disj_X12: "disjoint_family X1" "disjoint_family X2"
      by (auto simp: X1_def X2_def disjoint_family_on_def)
    
    have "(\<Sum>i. emeasure M1 (Inl -` X i) + emeasure M2 (Inr -` X i)) =
          (\<Sum>i. emeasure M1 (X1 i)) + (\<Sum>i. emeasure M2 (X2 i))"
      unfolding X1_def X2_def by (intro suminf_add_ereal emeasure_nonneg)
    also have "(\<Sum>i. emeasure M1 (X1 i)) = emeasure M1 (\<Union>i. X1 i)"
      using range_X12(1) disj_X12(1) by (rule suminf_emeasure)
    also have "(\<Sum>i. emeasure M2 (X2 i)) = emeasure M2 (\<Union>i. X2 i)"
      using range_X12(2) disj_X12(2) by (rule suminf_emeasure)
    also have "(\<Union>i. X1 i) = Inl -` (\<Union>i. X i)" by (auto simp: X1_def)
    also have "(\<Union>i. X2 i) = Inr -` (\<Union>i. X i)" by (auto simp: X2_def)
    finally show "(\<Sum>i. emeasure M1 (Inl -` X i) + emeasure M2 (Inr -` X i)) =
                  emeasure M1 (Inl -` (\<Union>i. X i)) + emeasure M2 (Inr -` (\<Union>i. X i))" .
  qed
qed

lemma emeasure_sum_Inl: "A \<in> sets M1 \<Longrightarrow> emeasure (M1 \<Oplus>\<^sub>M M2) (Inl ` A) = emeasure M1 A"
  by (subst emeasure_sum_measure) (auto simp: vimage_image_eq)

lemma emeasure_sum_Inr: "A \<in> sets M2 \<Longrightarrow> emeasure (M1 \<Oplus>\<^sub>M M2) (Inr ` A) = emeasure M2 A"
  by (subst emeasure_sum_measure) (auto simp: vimage_image_eq)


locale sum_sigma_finite = M1: sigma_finite_measure M1 + M2: sigma_finite_measure M2
  for M1 :: "'a measure" and M2 :: "'b measure"

sublocale sum_sigma_finite \<subseteq> P: sigma_finite_measure "M1 \<Oplus>\<^sub>M M2"
proof-
  from M1.sigma_finite_countable guess A by (elim exE conjE)
  note A = this
  from M2.sigma_finite_countable guess B by (elim exE conjE)
  note B = this
  def AB \<equiv> "(\<lambda>X. Inl`X) ` A \<union> (\<lambda>X. Inr`X) ` B"
  show "sigma_finite_measure (M1 \<Oplus>\<^sub>M M2)"
  proof (unfold_locales, rule exI[of _ AB], intro conjI ballI)
    from A(1) B(1) show "countable AB" by (simp add: AB_def)
    from A(2) B(2) show "AB \<subseteq> sets (M1 \<Oplus>\<^sub>M M2)"
      by (auto simp: AB_def intro!: sum_measureI1)
      
    show "\<Union>AB = space (M1 \<Oplus>\<^sub>M M2)"
    proof (intro equalityI subsetI)
      fix x assume "x \<in> \<Union>AB"
      with A(2-3) B(2-3) show "x \<in> space (M1 \<Oplus>\<^sub>M M2)" unfolding AB_def
        by (cases x) (auto simp: space_sum_measure)
    next
      fix x assume "x \<in> space (M1 \<Oplus>\<^sub>M M2)"
      with A(3) B(3) show "x \<in> \<Union>AB"
      unfolding AB_def by (cases x) (auto simp: space_sum_measure inj_image_mem_iff)
    qed
    
    fix X assume "X \<in> AB"
    moreover with `AB \<subseteq> sets (M1 \<Oplus>\<^sub>M M2)` have "X \<in> sets (M1 \<Oplus>\<^sub>M M2)" by blast
    moreover note A(4) B(4)
    ultimately show "emeasure (M1 \<Oplus>\<^sub>M M2) X \<noteq> \<infinity>"
      unfolding AB_def by (fastforce simp: emeasure_sum_measure vimage_image_eq)
  qed
qed

lemma sigma_finite_sum_measure:
  assumes A: "sigma_finite_measure A" and B: "sigma_finite_measure B"
  shows "sigma_finite_measure (A \<Oplus>\<^sub>M B)"
proof -
  interpret A: sigma_finite_measure A by fact
  interpret B: sigma_finite_measure B by fact
  interpret AB: sum_sigma_finite A  B ..
  show ?thesis ..
qed


lemma AE_sum:
  "(AE x in (M1 \<Oplus>\<^sub>M M2). P x) \<longleftrightarrow> (AE x in M1. P (Inl x)) \<and> (AE x in M2. P (Inr x))" (is "?Q = ?R")
proof
  assume ?Q
  then guess X by (rule AE_E)
  note X = this
  from X(1) have "{x \<in> space M1. \<not>P (Inl x)} \<subseteq> Inl -` X"
             and "{x \<in> space M2. \<not>P (Inr x)} \<subseteq> Inr -` X"
    by (auto simp: space_sum_measure)
  moreover from X have "emeasure M1 (Inl -` X) + emeasure M2 (Inr -` X) = 0"
    by (auto simp: emeasure_sum_measure)
  hence "emeasure M1 (Inl -` X) = 0 \<and> emeasure M2 (Inr -` X) = 0"
    by (subst (asm) ereal_add_nonneg_eq_0_iff) (simp_all add: emeasure_nonneg)
  moreover from X have "Inl -` X \<in> sets M1" "Inr -` X \<in> sets M2"
    by (fastforce simp: sets_sum_measure vimage_image_eq)+
  ultimately show "(AE x in M1. P (Inl x)) \<and> (AE x in M2. P (Inr x))"
    by (intro conjI AE_I) simp_all
next
  assume ?R
  hence R1: "AE x in M1. P (Inl x)" and R2: "AE x in M2. P (Inr x)" by blast+
  from R1 guess X by (elim AE_E)
  note X = this
  from R2 guess Y by (elim AE_E)
  note Y = this
  from X Y have "{x \<in> space (M1 \<Oplus>\<^sub>M M2). \<not>P x} \<subseteq> Inl`X \<union> Inr`Y"
    by (auto simp: space_sum_measure)
  moreover from X Y have "emeasure (M1 \<Oplus>\<^sub>M M2) (Inl`X \<union> Inr`Y) = 0"
    by (subst plus_emeasure[symmetric]) (auto simp: emeasure_sum_Inl emeasure_sum_Inr)
  moreover from X Y have "Inl`X \<union> Inr`Y \<in> sets (M1 \<Oplus>\<^sub>M M2)" by simp
  ultimately show ?Q by (rule AE_I)
qed

lemma AE_sumI:
  "AE x in M1. P (Inl x) \<Longrightarrow> AE x in M2. P (Inr x) \<Longrightarrow> AE x in (M1 \<Oplus>\<^sub>M M2). P x"
  by (simp add: AE_sum)

lemma AE_sumD1: "AE x in (M1 \<Oplus>\<^sub>M M2). P x \<Longrightarrow> AE x in M1. P (Inl x)"
  and AE_sumD2: "AE x in (M1 \<Oplus>\<^sub>M M2). P x \<Longrightarrow> AE x in M2. P (Inr x)"
  by (simp_all add: AE_sum)

end
