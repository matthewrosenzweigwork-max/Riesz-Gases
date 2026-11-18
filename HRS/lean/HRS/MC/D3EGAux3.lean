import HRS.MC.D3EGAux2

/-!
# Packet D3EG, helper 3: `g_λ = c₀ + G_λ` on `ℝ^d`, hence `g_λ` is smooth.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3EG

open HRS HRS.MC.FDLE HRS.MC.D3EW

variable {d : ℕ}

/-- The additive constant: `C - log λ` for `s = 0`, `0` otherwise. -/
def d3eg_c0 (s lam C : ℝ) : ℝ := if s = 0 then C - Real.log lam else 0

lemma d3eg_G_contDiff {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s : ℝ} (hs0 : 0 ≤ s) {b : ℝ}
    (hb0 : 0 < b) {lam : ℝ} (hl : 0 < lam) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (d3eg_G ψ s b lam) := by
  rw [contDiff_infty]
  intro n
  exact d3eg_contDiff_integral (J := Ioi lam) (U := Ioi 0) measurableSet_Ioi isOpen_Ioi
    (fun t ht => lt_trans hl ht) n (d3eg_K ψ s b) (d3eg_hyp hψ hs0 hb0 hl)

lemma d3eg_repr_pos {ψ : Euc d → ℝ} {s : ℝ} (hs : 0 < s) {b : ℝ} (hb : IsFDLConst ψ s b)
    {lam : ℝ} (hl : 0 < lam) {z : Euc d} (hz : z ≠ 0) :
    Whole.rieszKernel d s z - fdlWE ψ s b lam z = d3eg_G ψ s b lam z := by
  obtain ⟨hint, hg⟩ := hb.2.1 hs z hz
  have hf : IntegrableOn (fun t : ℝ => t ^ (-s - 1) * fdlPhi ψ (t⁻¹ • z)) (Ioi 0) :=
    hint.congr_fun (fun t ht => d3ew_integrand ψ s ht z) measurableSet_Ioi
  have hg' : Whole.rieszKernel d s z
      = b * ∫ t in Ioi (0 : ℝ), t ^ (-s - 1) * fdlPhi ψ (t⁻¹ • z) := by
    rw [hg]; congr 1
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => d3ew_integrand ψ s ht z)
  have hsplit : ∫ t in Ioi (0 : ℝ), t ^ (-s - 1) * fdlPhi ψ (t⁻¹ • z)
      = (∫ t in Ioc 0 lam, t ^ (-s - 1) * fdlPhi ψ (t⁻¹ • z))
        + ∫ t in Ioi lam, t ^ (-s - 1) * fdlPhi ψ (t⁻¹ • z) := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
      (hf.mono_set (fun t ht => ht.1)) (hf.mono_set (fun t ht => lt_trans hl ht)),
      Ioc_union_Ioi_eq_Ioi hl.le]
  have hw : fdlWE ψ s b lam z = b * ∫ t in Ioc 0 lam, t ^ (-s - 1) * fdlPhi ψ (t⁻¹ • z) := by
    rw [d3ew_rep, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioc (fun t ht => by simp only [mul_assoc])
  have hG : d3eg_G ψ s b lam z = b * ∫ t in Ioi lam, t ^ (-s - 1) * fdlPhi ψ (t⁻¹ • z) := by
    unfold d3eg_G
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [d3eg_K, d3eg_iota, hs.ne', mul_assoc]
  rw [hg', hw, hG, hsplit]; ring

lemma d3eg_rpow0 {t : ℝ} : t ^ (-(0 : ℝ) - 1) = t⁻¹ := by
  rw [show -(0 : ℝ) - 1 = -1 by norm_num, Real.rpow_neg_one]

lemma d3eg_repr_zero {ψ : Euc d → ℝ} (hd : 1 ≤ d) (hψ : IsFDLProfile ψ) {b : ℝ}
    (hb : IsFDLConst ψ 0 b) :
    ∃ C : ℝ, ∀ lam : ℝ, 0 < lam → ∀ z : Euc d, z ≠ 0 →
      Whole.rieszKernel d 0 z - fdlWE ψ 0 b lam z = (C - Real.log lam) + d3eg_G ψ 0 b lam z := by
  obtain ⟨C, hC⟩ := hb.2.2.1 rfl
  refine ⟨C, fun lam hl z hz => ?_⟩
  obtain ⟨hintR, htend⟩ := hC z hz
  have hb0 : 0 < b := hb.1
  have hbφ : b * fdlPhi ψ 0 = 1 := fdle_b_phi0 hd hb
  set φ0 := fdlPhi ψ 0 with hφ0
  set f : ℝ → ℝ := fun t => t⁻¹ * fdlPhi ψ (t⁻¹ • z) with hf
  set D : ℝ → ℝ := fun t => d3eg_K ψ 0 1 t z with hD
  have hDeq : ∀ t, D t = t⁻¹ * (fdlPhi ψ (t⁻¹ • z) - φ0) := by
    intro t; simp [hD, d3eg_K, d3eg_iota, Real.rpow_neg_one, hφ0]
  have hKD : ∀ t, d3eg_K ψ 0 b t z = b * D t := by
    intro t; simp [hD, d3eg_K, mul_assoc]
  have hAR : ∀ R : ℝ, 0 < R →
      ∫ t in Ioc 0 R, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t = ∫ t in Ioc 0 R, f t := by
    intro R hR
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    show t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t = t⁻¹ * fdlPhi ψ (t⁻¹ • z)
    rw [d3ew_integrand ψ 0 ht.1, d3eg_rpow0]
  have hfint : ∀ R : ℝ, 0 < R → IntegrableOn f (Ioc 0 R) := by
    intro R hR
    refine (hintR R hR).congr_fun (fun t ht => ?_) measurableSet_Ioc
    show t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t = t⁻¹ * fdlPhi ψ (t⁻¹ • z)
    rw [d3ew_integrand ψ 0 ht.1, d3eg_rpow0]
  have hDint : IntegrableOn D (Ioi lam) := d3eg_K_int hψ le_rfl one_pos hl z
  set I := ∫ t in Ioi lam, D t with hI
  set W0 := ∫ t in Ioc 0 lam, f t with hW0
  have hlim : Tendsto (fun R : ℝ => (∫ t in Ioc (0 : ℝ) R, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t z / t)
      - φ0 * Real.log R) atTop (𝓝 (W0 - φ0 * Real.log lam + I)) := by
    have h1 : Tendsto (fun R : ℝ => ∫ x in lam..R, D x) atTop (𝓝 I) :=
      intervalIntegral_tendsto_integral_Ioi lam hDint tendsto_id
    refine ((tendsto_const_nhds (x := W0 - φ0 * Real.log lam)).add h1).congr' ?_
    filter_upwards [eventually_gt_atTop lam] with R hR
    have hR0 : 0 < R := lt_trans hl hR
    rw [hAR R hR0, ← Ioc_union_Ioc_eq_Ioc hl.le hR.le,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        ((hfint lam hl).mono_set (fun t ht => ht))
        ((hfint R hR0).mono_set (fun t ht => ⟨lt_trans hl ht.1, ht.2⟩))]
    have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc lam R) :=
      (continuousOn_inv₀.mono (fun t ht => (lt_of_lt_of_le hl ht.1).ne')).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hDI : IntegrableOn D (Ioc lam R) := hDint.mono_set (fun t ht => ht.1)
    have hsplit : ∫ t in Ioc lam R, f t = (∫ t in Ioc lam R, D t) + φ0 * ∫ t in Ioc lam R, t⁻¹ := by
      rw [← integral_const_mul, ← integral_add hDI (hinv.const_mul φ0)]
      refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      show t⁻¹ * fdlPhi ψ (t⁻¹ • z) = D t + φ0 * t⁻¹
      rw [hDeq]; ring
    have hlog : ∫ t in Ioc lam R, t⁻¹ = Real.log R - Real.log lam := by
      rw [← intervalIntegral.integral_of_le hR.le, integral_inv_of_pos hl hR0,
        Real.log_div hR0.ne' hl.ne']
    rw [hsplit, hlog, intervalIntegral.integral_of_le hR.le]
    ring
  have hlim2 := tendsto_nhds_unique htend hlim
  have hw : fdlWE ψ 0 b lam z = b * W0 := by
    unfold fdlWE
    rw [hAR lam hl]
  have hG : d3eg_G ψ 0 b lam z = b * I := by
    unfold d3eg_G
    simp_rw [hKD]
    rw [integral_const_mul]
  rw [hw, hG]
  have h3 := (div_eq_iff hb0.ne').1 hlim2
  linear_combination h3 - Real.log lam * hbφ

end HRS.MC.D3EG
