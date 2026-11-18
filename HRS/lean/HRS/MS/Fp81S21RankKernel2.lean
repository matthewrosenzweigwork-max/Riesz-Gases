import HRS.MS.Fp81S21RankKernel
import HRS.MS.R2ChaosAux43
import HRS.MS.R2S11Aux8

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS.Whole
open HRS.MS.R26T3

private theorem fp81s21_rankKernel_velocity_data
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ B C : ℝ, ∃ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
      0 ≤ B ∧ 0 ≤ C ∧
      (∀ θ : HRS.MS.R2S11.s11V p.d Λ,
        IsBoundedPairKernel p.s B (commutatorKernel p.d p.s θ.1)) ∧
      IsR2UniformApprox p.s C B (HRS.Whole.withDensityReal R.ρβ)
        (fun θ => commutatorKernel p.d p.s θ.1)
        (fun θ k => (D θ k).kernel) := by
  obtain ⟨B, C₂, hj, hbounded, happrox⟩ :=
    HRS.MS.R2S11.s11_velocity_uniform_approx p.hd p.hs0 p.hs p.ha p.hβ
      R.thermal Λ
  choose n c u hvalid hkernel using happrox.finiteRank
  let D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d :=
    fun θ k => ⟨n θ k, c θ k, u θ k, hvalid θ k⟩
  let C : ℝ := max C₂ 0
  have hB : 0 ≤ B := by
    let θ0 : HRS.MS.R2S11.s11V p.d Λ :=
      ⟨fun _ => 0, ⟨contDiff_const, by simp [cbNormVecE]⟩⟩
    have hdp : 0 < p.d := lt_of_lt_of_le (by decide : 0 < 2) p.hd
    letI : NeZero p.d := ⟨Nat.ne_of_gt hdp⟩
    letI : Nontrivial (Euc p.d) := inferInstance
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Euc p.d)
    have hz : commutatorKernel p.d p.s θ0.1 x y = 0 := by
      simp [θ0, commutatorKernel]
    have hbound := (hbounded θ0).bound x y hxy
    rw [hz, abs_zero] at hbound
    have hweight : 0 < 1 + rieszWeight p.s (x - y) := by
      have hw := HRS.MS.R2S11.s11_rieszWeight_nonneg (d := p.d) p.s (x - y)
      linarith
    nlinarith
  refine ⟨B, C, D, hB, le_max_right _ _, hbounded, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro θ k
    refine ⟨n θ k, c θ k, u θ k, hvalid θ k, ?_⟩
    rfl
  · intro θ k x y hxy
    have h := happrox.envelope θ k x y hxy
    have hEq : (D θ k).kernel = hj θ k := by
      dsimp [D, fp81s21_RankKernel.kernel]
      exact (hkernel θ k).symm
    rw [hEq]
    have hcoeff : C₂ * B ≤ C * B :=
      mul_le_mul_of_nonneg_right (le_max_left C₂ 0) hB
    exact h.trans (mul_le_mul_of_nonneg_right hcoeff (by
      have hw := HRS.MS.R2S11.s11_rieszWeight_nonneg (d := p.d) p.s (x - y)
      linarith))
  · intro r hr hrs
    simpa [D, fp81s21_RankKernel.kernel, hkernel] using
      happrox.converges r hr hrs

/-- A real profile for the moving product-law kernel error. The rank data and both
uniform envelope constants are selected before the velocity, approximation index,
and physical time. -/
theorem fp81s21_rankKernel_moving_product_profile
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
      ∃ B C : ℝ,
      ∃ κ : ℕ → ℝ,
        0 ≤ B ∧ 0 ≤ C ∧ (∀ k, 0 ≤ κ k) ∧
        Tendsto κ atTop (𝓝 0) ∧
        IsR2UniformApprox p.s C B (HRS.Whole.withDensityReal R.ρβ)
          (fun θ => commutatorKernel p.d p.s θ.1)
          (fun θ k => (D θ k).kernel) ∧
        ∀ θ k u, 0 ≤ u →
          eLpNorm (fun xy : Euc p.d × Euc p.d =>
            (D θ k).kernel xy.1 xy.2 - commutatorKernel p.d p.s θ.1 xy.1 xy.2)
            2 ((r26t3_mu R u).prod (r26t3_mu R u)) ≤ ENNReal.ofReal (κ k) := by
  obtain ⟨B, C, D, hB, hC, hcomm, happrox⟩ :=
    fp81s21_rankKernel_velocity_data p R Λ hΛ
  obtain ⟨Mref, Lref, _, hR2ref, _⟩ :=
    HRS.MS.R2S11.s11_thermal_round2 p.hd p.hs0 p.hs p.ha p.hβ R.thermal
  let Bdiff : ℝ := C * B + B
  have hBdiff : 0 ≤ Bdiff := by
    dsimp [Bdiff]
    positivity
  obtain ⟨Kref, hKref, hKbound⟩ :=
    HRS.MS.R2Chaos.s94_env_L2_bound p.hd p.hs0 p.hs hR2ref Bdiff hBdiff
  let refErr : ℕ → ℝ≥0∞ := fun k =>
    ⨆ θ : HRS.MS.R2S11.s11V p.d Λ,
      eLpNorm (fun xy : Euc p.d × Euc p.d =>
        (D θ k).kernel xy.1 xy.2 - commutatorKernel p.d p.s θ.1 xy.1 xy.2)
        2 ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ))
  have hrefBound : ∀ k, refErr k ≤ ENNReal.ofReal Kref := by
    intro k
    refine iSup_le fun θ => ?_
    have hdiff := HRS.MS.R2S11.s11_diff_unif hcomm happrox θ k
    simpa [Bdiff] using hKbound hdiff
  have hrefFinite : ∀ k, refErr k ≠ ⊤ := by
    intro k
    exact ne_of_lt (lt_of_le_of_lt (hrefBound k) ENNReal.ofReal_lt_top)
  have hrefConv : Tendsto refErr atTop (𝓝 0) := by
    simpa [refErr] using happrox.converges 2 (by norm_num) (by linarith [p.hs])
  let refReal : ℕ → ℝ := fun k => (refErr k).toReal
  have hrefRealConv : Tendsto refReal atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hrefConv
    change Tendsto (fun k => (refErr k).toReal) atTop (𝓝 0)
    exact h
  have hC1 : 0 ≤ p.C₁ := by
    have hρ0 : HRS.Whole.IsProbDensity (R.ρ 0) :=
      (R.resulting.global 0).density 0 (by simp)
    have hr := R.resulting.ratio 0 (by norm_num) (0 : Euc p.d)
    by_contra hnot
    have hneg : p.C₁ < 0 := lt_of_not_ge hnot
    have hprod : p.C₁ * R.ρβ 0 < 0 :=
      mul_neg_of_neg_of_pos hneg (HRS.Whole.u4_thermal_pos R.thermal 0)
    exact (not_lt_of_ge (hρ0.nonneg 0)) (hr.2.trans_lt hprod)
  let κ : ℕ → ℝ := fun k => p.C₁ * refReal k
  have hκnonneg : ∀ k, 0 ≤ κ k := by
    intro k
    exact mul_nonneg hC1 (ENNReal.toReal_nonneg)
  have hκConv : Tendsto κ atTop (𝓝 0) := by
    simpa [κ] using tendsto_const_nhds.mul hrefRealConv
  refine ⟨D, B, C, κ, hB, hC, hκnonneg, hκConv, happrox, ?_⟩
  intro θ k u hu
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  let μu : Measure (Euc p.d) := r26t3_mu R u
  let err : Euc p.d × Euc p.d → ℝ := fun xy =>
    (D θ k).kernel xy.1 xy.2 - commutatorKernel p.d p.s θ.1 xy.1 xy.2
  have hρle : ∀ x, R.ρ u x ≤ p.C₁ * R.ρβ x :=
    fun x => (R.resulting.ratio u hu x).2
  have hμdom : μu ≤ ENNReal.ofReal p.C₁ • μstar := by
    change HRS.Whole.withDensityReal (R.ρ u) ≤
      ENNReal.ofReal p.C₁ • HRS.Whole.withDensityReal R.ρβ
    exact HRS.MS.R2S11.s11_wd_le hC1 hρle
  haveI hμstar : IsProbabilityMeasure μstar := by
    change IsProbabilityMeasure (HRS.Whole.withDensityReal R.ρβ)
    exact HRS.MS.R2Mt.s92_isProb_mu R.thermal.2.1
  haveI hμu : IsProbabilityMeasure μu := by
    change IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ u))
    exact HRS.MS.R2Mt.s92_isProb_mu
      ((R.resulting.global (u + 1)).density u ⟨hu, by linarith⟩)
  have hprod : μu.prod μu ≤
      ENNReal.ofReal (p.C₁ * p.C₁) • (μstar.prod μstar) := by
    calc
      μu.prod μu ≤ (ENNReal.ofReal p.C₁ • μstar).prod
          (ENNReal.ofReal p.C₁ • μstar) := Measure.prod_mono hμdom hμdom
      _ = (ENNReal.ofReal p.C₁ * ENNReal.ofReal p.C₁) • (μstar.prod μstar) := by
        rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
      _ = ENNReal.ofReal (p.C₁ * p.C₁) • (μstar.prod μstar) := by
        rw [← ENNReal.ofReal_mul hC1]
  have herrClass : IsBoundedPairKernel p.s Bdiff (fun x y => err (x, y)) := by
    simpa [err, Bdiff] using HRS.MS.R2S11.s11_diff_unif hcomm happrox θ k
  have herrMeas0 : Measurable err := by
    simpa [Function.uncurry, err] using herrClass.measurable
  have herrMeas : AEStronglyMeasurable err (μstar.prod μstar) :=
    herrMeas0.aestronglyMeasurable
  have hmeasureScale :
      eLpNorm err 2 (μu.prod μu) ≤
        ENNReal.ofReal p.C₁ * eLpNorm err 2 (μstar.prod μstar) := by
    have hmono := eLpNorm_mono_measure err (p := 2) hprod
    have hc2 : ENNReal.ofReal (p.C₁ * p.C₁) =
        ENNReal.ofReal p.C₁ * ENNReal.ofReal p.C₁ := ENNReal.ofReal_mul hC1
    rw [hc2] at hmono
    rw [eLpNorm_smul_measure_of_ne_top (by simp) err _ herrMeas] at hmono
    simp only [ENNReal.toReal_ofNat, smul_eq_mul] at hmono
    have hExp : ((1 : ℝ≥0∞) / 2).toReal = (1 : ℝ) / 2 := by norm_num
    rw [hExp] at hmono
    rw [← ENNReal.ofReal_mul hC1] at hmono
    have hroot : (ENNReal.ofReal (p.C₁ * p.C₁)) ^ ((1 : ℝ) / 2) = ENNReal.ofReal p.C₁ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC1 hC1) (by norm_num)]
      rw [← Real.sqrt_eq_rpow, show p.C₁ * p.C₁ = p.C₁ ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg hC1]
    rw [hroot] at hmono
    exact hmono
  have href := le_iSup
    (fun θ' : HRS.MS.R2S11.s11V p.d Λ =>
      eLpNorm (fun xy : Euc p.d × Euc p.d =>
        (D θ' k).kernel xy.1 xy.2 - commutatorKernel p.d p.s θ'.1 xy.1 xy.2)
        2 (μstar.prod μstar)) θ
  have hprofile : eLpNorm err 2 (μu.prod μu) ≤ ENNReal.ofReal (κ k) := by
    calc
      eLpNorm err 2 (μu.prod μu) ≤ ENNReal.ofReal p.C₁ * eLpNorm err 2 (μstar.prod μstar) := hmeasureScale
      _ ≤ ENNReal.ofReal p.C₁ * refErr k :=
        mul_le_mul_of_nonneg_left href (by positivity)
      _ = ENNReal.ofReal (p.C₁ * refReal k) := by
        rw [ENNReal.ofReal_mul hC1, ENNReal.ofReal_toReal (hrefFinite k)]
      _ = ENNReal.ofReal (κ k) := by rfl
  simpa [μu, err, r26t3_mu] using hprofile

#print axioms fp81s21_rankKernel_moving_product_profile

end HRS.Fp81.S21
