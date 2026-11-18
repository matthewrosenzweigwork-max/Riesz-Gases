import HRS.MC.L2C4

/-!
# Packet L2C-5, helper 1: elementary analysis

* `l2c5_rho_cont`: joint continuity of `(v,x) ↦ ρ^v(x)` on `[0,T] × 𝕋^d`;
* `l2c5_sqrt_decay`: `(√ρ^v - √ρ_β)² ≤ C e^{-2 m v}` pointwise;
* `l2c5_pointwise`: the pointwise algebra `|√ρ u - √ρ' w|² ≤ 2(√ρ-√ρ')²|u|² + 2ρ'|u-w|²`;
* `l2c5_cont_param`, `l2c5_reflect`: parametric integral continuity and the reflection `v ↦ t - v`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE

namespace HRS.MC.L2C5

variable {d : ℕ}

/-- Joint continuity of the density path on `[0,T] × 𝕋^d`. -/
theorem l2c5_rho_cont (R : Regime d) (T : ℝ) :
    ContinuousOn (fun p : ℝ × Torus d => R.ρ p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) := by
  obtain ⟨K, ρc, hK1, hK2, hsol, hρ⟩ := HRS.MC.RegSet.rgs_sol R 0
  have hH := R.finiteRegHyp K hK2
  have hd : 1 ≤ d := by have := R.hd; omega
  have hreal := PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK hd R.D.s R.β R.β K R.D.V R.ρ₀ hH R.β
    ⟨le_rfl, le_rfl⟩ ρc hsol
  have hK3 : (d : ℝ) / 2 + 2 < K := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have h := (PDE.MFApriori.continuousOn_mfPath_prod_on hd R.D.s R.D.hs0 R.D.hsd K hK3 R.D.V R.ρ₀
    hH.hV R.β⁻¹ ρc (T := T)
    ⟨PDE.MFApriori.IsMFSolutionHK.toSolOn hsol T, fun τ hτ => hreal τ hτ.1⟩).1
  refine h.congr fun p hp => ?_
  simp only [hρ p.1 hp.1.1]

theorem l2c5_sqrt_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (a - b) ^ 2 / b := by
  rw [le_div_iff₀ hb]
  have h1 : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
    have := Real.sq_sqrt ha
    have := Real.sq_sqrt hb.le
    nlinarith
  have h2 : b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have := Real.sq_sqrt hb.le
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  rw [h1, mul_pow]
  exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

/-- `(√ρ^v - √ρ_β)² ≤ C e^{-2mv}` (pointwise), from `Regime.relax` and `ρ_β ≥ c₀ > 0`. -/
theorem l2c5_sqrt_decay (R : Regime d) {c₀ : ℝ} (hc₀ : 0 < c₀) (hlow : ∀ x, c₀ ≤ R.ρβ x) :
    ∃ C m : ℝ, 0 ≤ C ∧ 0 < m ∧ ∀ v : ℝ, 0 ≤ v → ∀ x,
      (Real.sqrt (R.ρ v x) - Real.sqrt (R.ρβ x)) ^ 2 ≤ C * Real.exp (-2 * m * v) := by
  obtain ⟨C0, c0, hc0, H0⟩ := HRS.MC.RegSet.relax_proof R 0
  obtain ⟨Λ, hΛ⟩ := HRS.MC.RegSet.reg_proof R 0
  refine ⟨C0 ^ 2 / c₀, c0, by positivity, hc0, fun v hv x => ?_⟩
  have hρ1 := (hΛ v v ⟨hv, le_rfl⟩).1
  have hρβ := HRS.MC.L2C3.l2c3_isCk_of_smooth R.thermal.2.1 0
  have hδ : Torus.IsCk ((0 : ℕ) : WithTop ℕ∞) (fun x => R.ρ v x - R.ρβ x) := hρ1.sub hρβ
  have hε : |R.ρ v x - R.ρβ x| ≤ C0 * Real.exp (-c0 * v) :=
    (HRS.PDE.R2Aux.abs_le_cbNorm hδ x).trans (H0 v hv)
  have hρnn : 0 ≤ R.ρ v x := by
    obtain ⟨m₀, M₀, hm₀, hb⟩ := R.bounds
    exact hm₀.le.trans (hb v hv x).1
  have hb : 0 < R.ρβ x := hc₀.trans_le (hlow x)
  refine (l2c5_sqrt_sq_le hρnn hb).trans ?_
  have hsq : (R.ρ v x - R.ρβ x) ^ 2 ≤ (C0 * Real.exp (-c0 * v)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hε 2
  have hexp : Real.exp (-c0 * v) ^ 2 = Real.exp (-2 * c0 * v) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (R.ρ v x - R.ρβ x) ^ 2 / R.ρβ x ≤ (C0 * Real.exp (-c0 * v)) ^ 2 / R.ρβ x :=
        div_le_div_of_nonneg_right hsq hb.le
    _ ≤ (C0 * Real.exp (-c0 * v)) ^ 2 / c₀ :=
        div_le_div_of_nonneg_left (sq_nonneg _) hc₀ (hlow x)
    _ = C0 ^ 2 / c₀ * Real.exp (-2 * c0 * v) := by
        rw [mul_pow, hexp]; ring

/-- The pointwise algebra behind the splitting `√ρ u - √ρ' w = (√ρ - √ρ') u + √ρ' (u - w)`. -/
theorem l2c5_pointwise {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u w : E)
    {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') :
    inner ℝ u u * Real.sqrt (r * r) + inner ℝ w w * Real.sqrt (r' * r') -
        2 * (inner ℝ u w * Real.sqrt (r * r')) ≤
      2 * (Real.sqrt r - Real.sqrt r') ^ 2 * ‖u‖ ^ 2 + 2 * r' * ‖u - w‖ ^ 2 := by
  have e1 : Real.sqrt (r * r) = r := Real.sqrt_mul_self hr
  have e2 : Real.sqrt (r' * r') = r' := Real.sqrt_mul_self hr'
  have e3 : Real.sqrt (r * r') = Real.sqrt r * Real.sqrt r' := Real.sqrt_mul hr _
  set p := Real.sqrt r with hp
  set q := Real.sqrt r' with hq
  have hpr : r = p ^ 2 := (Real.sq_sqrt hr).symm
  have hqr : r' = q ^ 2 := (Real.sq_sqrt hr').symm
  rw [e1, e2, e3]
  have key : 0 ≤ inner ℝ ((p - 2 * q) • u + q • w) ((p - 2 * q) • u + q • w) := real_inner_self_nonneg
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right] at key
  have hu : ‖u‖ ^ 2 = inner ℝ u u := (real_inner_self_eq_norm_sq u).symm
  have huw : ‖u - w‖ ^ 2 = inner ℝ u u - 2 * inner ℝ u w + inner ℝ w w := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm u w]
    ring
  rw [hu, huw, hpr, hqr]
  rw [real_inner_comm u w] at key
  nlinarith [key]

theorem l2c5_cont_param {t : ℝ} {g : ℝ → Torus d → ℝ}
    (hg : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => g p.1 p.2) :
    ContinuousOn (fun r => ∫ x, g r x) (Set.Icc 0 t) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have key := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d)))
    (f := fun (r : Set.Icc (0 : ℝ) t) (x : Torus d) => g r.1 x) hg isCompact_univ
  simp only [MeasureTheory.Measure.restrict_univ] at key
  exact key

theorem l2c5_reflect {t : ℝ} (ht : 0 ≤ t) (g : ℝ → ℝ) :
    ∫ v in Set.Icc (0 : ℝ) t, g v = ∫ σ in (0 : ℝ)..t, g (t - σ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_comp_sub_left g t, sub_self, sub_zero]

end HRS.MC.L2C5
