import HRS.MC.E213U3B

/-!
# Packet E213U3, part C: the `L¹` theorem for integrable measurable coefficients

Density of continuous compactly supported functions (`Integrable.exists_hasCompactSupport_integral_sub_le`),
the Cauchy property of the tensors of the approximants (`u3_cont_L1` applied to differences, uniqueness of `SJ`)
and passage to the limit in the evaluation formula (`u3_Fser_bound`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U3

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDS

set_option maxSynthPendingDepth 3

variable {d : ℕ}

theorem u3_isClosed_proj (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] (k : ℕ) :
    IsClosed (projTensor B k : Set (TensorDual B k)) := by
  unfold projTensor
  exact Submodule.isClosed_topologicalClosure _

theorem u3_intOK_cont (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) {g : ℝ → NegSobolev d r} (hg : Continuous g)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ G) : IntOK Rb r m G g (Set.Ioc α β) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) G)).exists_bound_of_continuousOn
    hg.continuousOn
  exact u3_intOK_bdd Rb r hr m hm G hG hg.measurable hM measurableSet_Ioc
    (fun u hu => ⟨lt_of_le_of_lt hα hu.1, hu.2.trans hβ⟩)

/-- **The `L¹` theorem.** -/
theorem u3_L1 (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b₀ : ℝ, ∀ hb₀ : 0 ≤ b₀, ∀ (zr : ℝ → NegSobolev d r), Measurable zr →
      ∀ α β : ℝ, 0 ≤ α → β ≤ G → IntegrableOn (fun u => ‖zr u‖) (Set.Ioc α β) →
      ∃ J, SJ (HRS.MC.E213F.shift R b₀ hb₀) r m G zr (Set.Ioc α β) J ∧
        ‖J‖ ≤ C * ∫ u in Set.Ioc α β, ‖zr u‖ := by
  classical
  obtain ⟨C, hC0, hcont⟩ := u3_cont_L1 R r hr m hm G hG
  refine ⟨C, hC0, fun b₀ hb₀ zr hzr α β hα hβG hint => ?_⟩
  set Rb := HRS.MC.E213F.shift R b₀ hb₀ with hRb
  by_cases hαβ : α ≤ β
  swap
  · refine ⟨0, ?_, ?_⟩
    · rw [Set.Ioc_eq_empty (not_lt.2 (not_le.1 hαβ).le)]
      exact u3_SJ_empty Rb r m G zr
    · rw [Set.Ioc_eq_empty (not_lt.2 (not_le.1 hαβ).le)]
      simp
  have hsubG : Set.Ioc α β ⊆ Set.Ioc 0 G := fun u hu => ⟨lt_of_le_of_lt hα hu.1, hu.2.trans hβG⟩
  have hzint : IntegrableOn zr (Set.Ioc α β) :=
    (integrable_norm_iff hzr.aestronglyMeasurable).1 hint
  -- the approximants
  set f : ℝ → NegSobolev d r := Set.indicator (Set.Ioc α β) zr with hf
  have hfi : Integrable f := (integrable_indicator_iff measurableSet_Ioc).2 hzint
  have hex : ∀ n : ℕ, ∃ g : ℝ → NegSobolev d r, HasCompactSupport g ∧
      (∫ x, ‖f x - g x‖) ≤ 1 / ((n : ℝ) + 1) ∧ Continuous g ∧ Integrable g :=
    fun n => hfi.exists_hasCompactSupport_integral_sub_le (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose g hgs hgI hgc hgi using hex
  -- `L¹` distance on the interval
  have hdist : ∀ n, IntegrableOn (fun u => ‖zr u - g n u‖) (Set.Ioc α β) :=
    fun n => (hzint.sub (hgi n).integrableOn).norm
  have hdistb : ∀ n, (∫ u in Set.Ioc α β, ‖zr u - g n u‖) ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 : (∫ u in Set.Ioc α β, ‖f u - g n u‖) = ∫ u in Set.Ioc α β, ‖zr u - g n u‖ := by
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      simp only [hf, Set.indicator_of_mem hu]
    rw [← h1]
    refine le_trans (setIntegral_le_integral ((hfi.sub (hgi n)).norm)
      (Filter.Eventually.of_forall fun u => norm_nonneg _)) (hgI n)
  have hdist0 : ∀ n, 0 ≤ ∫ u in Set.Ioc α β, ‖zr u - g n u‖ :=
    fun n => setIntegral_nonneg measurableSet_Ioc fun u _ => norm_nonneg _
  -- tensors of the approximants
  have hex2 : ∀ n, ∃ J, SJ Rb r m G (g n) (Set.Ioc α β) J ∧ ‖J‖ ≤ C * ∫ u in Set.Ioc α β, ‖g n u‖ :=
    fun n => hcont b₀ hb₀ (g n) (hgc n) α β hα hαβ hβG
  choose J hJ hJn using hex2
  have hIg : ∀ n, IntOK Rb r m G (g n) (Set.Ioc α β) := fun n => u3_intOK_cont Rb r hr m hm G hG (hgc n) hα hβG
  have hIz : IntOK Rb r m G zr (Set.Ioc α β) := u3_intOK Rb r hr m hm G hG zr hzr measurableSet_Ioc hsubG hint
  -- Cauchy
  have hdiff : ∀ n k, ‖J n - J k‖ ≤ C * (1 / ((n : ℝ) + 1) + 1 / ((k : ℝ) + 1)) := by
    intro n k
    have hs := u3_SJ_sub Rb r hr m hm G hG measurableSet_Ioc (hJ n) (hJ k) (hIg n) (hIg k)
    obtain ⟨J', hJ', hJ'n⟩ := hcont b₀ hb₀ (fun v => g n v - g k v) ((hgc n).sub (hgc k)) α β hα hαβ hβG
    have heq : J n - J k = J' := u3_SJ_unique Rb r m G hs hJ'
    rw [heq]
    refine hJ'n.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC0
    have h1 : (∫ u in Set.Ioc α β, ‖g n u - g k u‖) ≤
        (∫ u in Set.Ioc α β, ‖zr u - g n u‖) + ∫ u in Set.Ioc α β, ‖zr u - g k u‖ := by
      rw [← integral_add (hdist n) (hdist k)]
      refine setIntegral_mono_on ?_ ((hdist n).add (hdist k)) measurableSet_Ioc fun u _ => ?_
      · exact ((hgi n).integrableOn.sub (hgi k).integrableOn).norm
      · calc ‖g n u - g k u‖ = ‖(zr u - g k u) - (zr u - g n u)‖ := by congr 1; abel
          _ ≤ ‖zr u - g k u‖ + ‖zr u - g n u‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
    linarith [hdistb n, hdistb k]
  have hcauchy : CauchySeq J := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 * C * (1 / ((N : ℝ) + 1))) (fun n k N hn hk => ?_) ?_
    · rw [dist_eq_norm]
      refine (hdiff n k).trans ?_
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
      have h2 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
      nlinarith
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * C)
  obtain ⟨Jlim, hJlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hmem : Jlim ∈ projTensor (PathSpace d m G) 2 :=
    (u3_isClosed_proj _ 2).mem_of_tendsto hJlim (Filter.Eventually.of_forall fun n => (hJ n).1)
  -- passage to the limit of the evaluations
  have hSJ : SJ Rb r m G zr (Set.Ioc α β) Jlim := by
    refine ⟨hmem, ?_⟩
    intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    obtain ⟨Cφ, hCφ0, hCφ⟩ := u3_Fser_bound Rb r hr m hm G hG ta tb hta htb φa φb hφa hφb
    set S : Set ℝ := Set.Ioc α β ∩ Set.Icc 0 (min ta tb) with hS
    have hSm : MeasurableSet S := measurableSet_Ioc.inter measurableSet_Icc
    have hSa : ∀ u ∈ S, u ≤ ta := fun u hu => hu.2.2.trans (min_le_left _ _)
    have hSb : ∀ u ∈ S, u ≤ tb := fun u hu => hu.2.2.trans (min_le_right _ _)
    have hL : Tendsto (fun n => J n (prodForm l₁ l₂)) atTop (𝓝 (Jlim (prodForm l₁ l₂))) :=
      ((ContinuousLinearMap.apply ℝ ℝ (prodForm l₁ l₂)).continuous.tendsto Jlim).comp hJlim
    have hbound : ∀ n, ‖(∫ u in S, Fser Rb r m (g n) ta tb φa φb u) -
        ∫ u in S, Fser Rb r m zr ta tb φa φb u‖ ≤ Cφ * (1 / ((n : ℝ) + 1)) := by
      intro n
      have i1 := hIg n ta tb φa φb hφa hφb hta htb
      have i2 := hIz ta tb φa φb hφa hφb hta htb
      rw [← integral_sub i1 i2]
      have hdn0 : IntegrableOn (fun u => ‖g n u - zr u‖) (Set.Ioc α β) :=
        ((hgi n).integrableOn.sub hzint).norm
      have hdn : IntegrableOn (fun u => ‖g n u - zr u‖) S := hdn0.mono_set Set.inter_subset_left
      calc ‖∫ u in S, (Fser Rb r m (g n) ta tb φa φb u - Fser Rb r m zr ta tb φa φb u)‖
          ≤ ∫ u in S, ‖Fser Rb r m (g n) ta tb φa φb u - Fser Rb r m zr ta tb φa φb u‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ u in S, Cφ * ‖g n u - zr u‖ := by
            refine setIntegral_mono_on (i1.sub i2).norm (hdn.const_mul Cφ) hSm fun u hu => ?_
            rw [← u3_Fser_sub Rb r hr m hm G hG ta tb hta htb φa φb hφa hφb (g n) zr u hu.2.1
              (hSa u hu) (hSb u hu), Real.norm_eq_abs]
            exact (hCφ (fun v => g n v - zr v) u hu.2.1 (hSa u hu) (hSb u hu)).2
        _ = Cφ * ∫ u in S, ‖g n u - zr u‖ := integral_const_mul _ _
        _ ≤ Cφ * ∫ u in Set.Ioc α β, ‖zr u - g n u‖ := by
            refine mul_le_mul_of_nonneg_left ?_ hCφ0
            calc (∫ u in S, ‖g n u - zr u‖) ≤ ∫ u in Set.Ioc α β, ‖g n u - zr u‖ :=
                  setIntegral_mono_set hdn0
                    (Filter.Eventually.of_forall fun u => norm_nonneg _)
                    (Filter.Eventually.of_forall Set.inter_subset_left)
              _ = ∫ u in Set.Ioc α β, ‖zr u - g n u‖ := by
                  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
                  exact norm_sub_rev _ _
        _ ≤ Cφ * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left (hdistb n) hCφ0
    have hR : Tendsto (fun n => (∫ u in S, Fser Rb r m (g n) ta tb φa φb u)) atTop
        (𝓝 (∫ u in S, Fser Rb r m zr ta tb φa φb u)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul Cφ
    have hR' := hR.const_mul (2 * Rb.D.invβ)
    have hEq : ∀ n, J n (prodForm l₁ l₂) = 2 * Rb.D.invβ * ∫ u in S, Fser Rb r m (g n) ta tb φa φb u :=
      fun n => (hJ n).2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    exact tendsto_nhds_unique hL (hR'.congr fun n => (hEq n).symm)
  refine ⟨Jlim, hSJ, ?_⟩
  -- the norm bound
  have hn1 : Tendsto (fun n => ‖J n‖) atTop (𝓝 ‖Jlim‖) := hJlim.norm
  have hn2 : Tendsto (fun n => C * ∫ u in Set.Ioc α β, ‖g n u‖) atTop
      (𝓝 (C * ∫ u in Set.Ioc α β, ‖zr u‖)) := by
    refine Tendsto.const_mul C ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [← integral_sub ((hgi n).integrableOn.norm) hint]
    calc ‖∫ u in Set.Ioc α β, (‖g n u‖ - ‖zr u‖)‖ ≤ ∫ u in Set.Ioc α β, ‖‖g n u‖ - ‖zr u‖‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioc α β, ‖zr u - g n u‖ := by
          refine setIntegral_mono_on (((hgi n).integrableOn.norm.sub hint).norm) (hdist n)
            measurableSet_Ioc fun u _ => ?_
          calc ‖‖g n u‖ - ‖zr u‖‖ ≤ ‖g n u - zr u‖ := abs_norm_sub_norm_le _ _
            _ = ‖zr u - g n u‖ := norm_sub_rev _ _
      _ ≤ 1 / ((n : ℝ) + 1) := hdistb n
  exact le_of_tendsto_of_tendsto' hn1 hn2 hJn

end HRS.MC.E213U3

end
