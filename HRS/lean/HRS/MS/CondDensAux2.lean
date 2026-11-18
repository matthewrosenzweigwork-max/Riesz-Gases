import HRS.MS.CondDensAux1

/-!
# HRS.MS.CondDensAux2 -- conditional density of the pole law: generic estimates (S74, part 2)

Packet S74 (S7.4 `HRS.Whole.conditional_density`), namespace `HRS.MS.Wr`, helper prefix `s74_`.

Generic (any probability `μ` with `g*μ ≤ M_g`) facts about the cavity law `P` of `N = m + 2` particles:

* `s74_coord_marg`, `s74_coord_integral`: every coordinate marginal of `P` is `≤ e^{2βM_g} μ`;
* `s74_pole_le`: joint pole domination `P^{x,t} ≤ e^{β K M_g} P` (Jensen);
* `s74_abs_integral_le_sqrt`, `s74_exp_neg_sub_one_le`, `s74_fubini_bound`: elementary tools;
* `s74_ratio`: the pointwise bound `|e^{-u(Y',y)}/Zr(Y') - 1| ≤ e^{2βM_g}(|u(Y',y)| + λ M_g + ∫|u(Y',z)| dμ(z))`.

No frozen file is edited.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal BigOperators

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole (rieszKernel EucConfig)

variable {d : ℕ} {s : ℝ}

/-! ### Elementary tools -/

theorem s74_abs_integral_le_sqrt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {h : Ω → ℝ} (hm : Measurable h) {B : ℝ} (hb : ∀ ω, |h ω| ≤ B) :
    ∫ ω, |h ω| ∂P ≤ Real.sqrt (∫ ω, h ω ^ 2 ∂P) := by
  have hmem : MemLp (fun ω => |h ω|) 2 P :=
    MemLp.of_bound hm.abs.aestronglyMeasurable B (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_abs]; exact hb ω)
  have h1 := variance_eq_sub hmem
  have h2 := variance_nonneg (fun ω => |h ω|) P
  have h3 : (∫ ω, |h ω| ∂P) ^ 2 ≤ ∫ ω, h ω ^ 2 ∂P := by
    have e : ∫ ω, (fun ω => |h ω|) ω ^ 2 ∂P = ∫ ω, h ω ^ 2 ∂P := by
      simp only [sq_abs]
    simp only [Pi.pow_apply] at h1
    rw [e] at h1
    linarith
  have h4 := Real.abs_le_sqrt h3
  rwa [abs_of_nonneg (integral_nonneg fun ω => abs_nonneg _)] at h4

theorem s74_exp_neg_sub_one_le (U b : ℝ) (hb : 0 ≤ b) (hU : -U ≤ b) :
    |Real.exp (-U) - 1| ≤ Real.exp b * |U| := by
  have he1 : 1 ≤ Real.exp b := Real.one_le_exp hb
  rcases le_or_gt 0 U with hU0 | hU0
  · have h := Real.add_one_le_exp (-U)
    have h2 : Real.exp (-U) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg hU0]
    nlinarith
  · have h := Real.add_one_le_exp U
    have h2 : 1 ≤ Real.exp (-U) := Real.one_le_exp (by linarith)
    have h3 : Real.exp (-U) ≤ Real.exp b := Real.exp_le_exp.2 hU
    have h4 : Real.exp (-U) * (U + 1) ≤ Real.exp (-U) * Real.exp U :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h4
    rw [abs_of_nonneg (by linarith), abs_of_neg hU0]
    nlinarith [Real.exp_pos (-U)]

theorem s74_fubini_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (F : Ω → Euc d → ℝ)
    (hF : Measurable (fun p : Ω × Euc d => F p.1 p.2)) (hF0 : ∀ ω z, 0 ≤ F ω z)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ z, ∫ ω, F ω z ∂P ≤ c) (hi : ∀ z, Integrable (fun ω => F ω z) P)
    (hiz : ∀ ω, Integrable (fun z => F ω z) μ) :
    Integrable (fun ω => ∫ z, F ω z ∂μ) P ∧ ∫ ω, ∫ z, F ω z ∂μ ∂P ≤ c := by
  have hFe : Measurable (fun p : Ω × Euc d => ENNReal.ofReal (F p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp hF
  have h1 : ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (F ω z) ∂μ ∂P ≤ ENNReal.ofReal c := by
    rw [lintegral_lintegral_swap hFe.aemeasurable]
    calc ∫⁻ z, ∫⁻ ω, ENNReal.ofReal (F ω z) ∂P ∂μ = ∫⁻ z, ENNReal.ofReal (∫ ω, F ω z ∂P) ∂μ :=
          lintegral_congr fun z => (ofReal_integral_eq_lintegral_ofReal (hi z)
            (Filter.Eventually.of_forall fun ω => hF0 ω z)).symm
      _ ≤ ∫⁻ _z, ENNReal.ofReal c ∂μ := lintegral_mono fun z => ENNReal.ofReal_le_ofReal (h z)
      _ = ENNReal.ofReal c := by simp
  have hG : ∀ ω, ENNReal.ofReal (∫ z, F ω z ∂μ) = ∫⁻ z, ENNReal.ofReal (F ω z) ∂μ := fun ω =>
    ofReal_integral_eq_lintegral_ofReal (hiz ω) (Filter.Eventually.of_forall fun z => hF0 ω z)
  have hGm : StronglyMeasurable (fun ω => ∫ z, F ω z ∂μ) :=
    (hF.stronglyMeasurable (f := Function.uncurry F)).integral_prod_right' (ν := μ)
  have hG0 : ∀ ω, 0 ≤ ∫ z, F ω z ∂μ := fun ω => integral_nonneg fun z => hF0 ω z
  have h2 : ∫⁻ ω, ENNReal.ofReal (∫ z, F ω z ∂μ) ∂P ≤ ENNReal.ofReal c := by
    simpa only [hG] using h1
  refine ⟨⟨hGm.aestronglyMeasurable, ?_⟩, ?_⟩
  · calc ∫⁻ ω, ‖∫ z, F ω z ∂μ‖ₑ ∂P = ∫⁻ ω, ENNReal.ofReal (∫ z, F ω z ∂μ) ∂P :=
          lintegral_congr fun ω => Real.enorm_of_nonneg (hG0 ω)
      _ ≤ ENNReal.ofReal c := h2
      _ < ∞ := ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0) hGm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hc h2

/-! ### Coordinate marginals of the cavity law -/

section Marg

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β : ℝ}

theorem s74_coord_marg (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg) (hβ : 0 ≤ β)
    (m : ℕ) (j : Fin (m + 1)) :
    (HRS.Whole.cavityLaw d s (m + 2) β μ).map (fun Y : EucConfig d (m + 1) => Y j) ≤
      ENNReal.ofReal (Real.exp (2 * β * Mg)) • μ := by
  haveI := wr13a_cavityLaw_isProb hs0 hconv hβ (m + 2)
  have hexch := wr13c2_cavityLaw_exchangeable hs0 hconv hβ (m + 2)
  have e : (HRS.Whole.cavityLaw d s (m + 2) β μ).map (fun Y : EucConfig d (m + 1) => Y j) =
      HRS.Whole.firstMarginal (HRS.Whole.cavityLaw d s (m + 2) β μ) := by
    unfold HRS.Whole.firstMarginal
    rw [dif_pos (by omega : 0 < m + 2 - 1)]
    exact hexch.marginal_eq j ⟨0, by omega⟩
  rw [e, ← wr13c2_poleLaw_zero hs0 hconv hβ (m + 2) (0 : Euc d),
    s74_firstMarginal_A hs0 hint hconv hMg hβ le_rfl zero_le_one m 0, ← withDensity_const]
  refine withDensity_mono (Filter.Eventually.of_forall fun y => ?_)
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le
    (s74_a_le hs0 hint hconv hMg hβ le_rfl zero_le_one m 0 y)

theorem s74_coord_integral (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg) (hβ : 0 ≤ β)
    (m : ℕ) (j : Fin (m + 1)) {ψ : Euc d → ℝ} (hψ : Measurable ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hψi : Integrable ψ μ) :
    Integrable (fun Y : EucConfig d (m + 1) => ψ (Y j)) (HRS.Whole.cavityLaw d s (m + 2) β μ) ∧
      ∫ Y, ψ (Y j) ∂(HRS.Whole.cavityLaw d s (m + 2) β μ) ≤ Real.exp (2 * β * Mg) * ∫ z, ψ z ∂μ := by
  have hmarg := s74_coord_marg hs0 hint hconv hMg hβ m j
  have hi : Integrable ψ ((HRS.Whole.cavityLaw d s (m + 2) β μ).map (fun Y : EucConfig d (m + 1) => Y j)) :=
    (hψi.smul_measure (c := ENNReal.ofReal (Real.exp (2 * β * Mg))) ENNReal.ofReal_ne_top).mono_measure hmarg
  have hmeasj : Measurable (fun Y : EucConfig d (m + 1) => Y j) := measurable_pi_apply j
  refine ⟨(integrable_map_measure hψ.aestronglyMeasurable hmeasj.aemeasurable).1 hi, ?_⟩
  have hmap : ∫ Y, ψ (Y j) ∂(HRS.Whole.cavityLaw d s (m + 2) β μ) =
      ∫ z, ψ z ∂((HRS.Whole.cavityLaw d s (m + 2) β μ).map (fun Y : EucConfig d (m + 1) => Y j)) :=
    (integral_map hmeasj.aemeasurable hψ.aestronglyMeasurable).symm
  rw [hmap]
  calc ∫ z, ψ z ∂((HRS.Whole.cavityLaw d s (m + 2) β μ).map (fun Y : EucConfig d (m + 1) => Y j))
      ≤ ∫ z, ψ z ∂(ENNReal.ofReal (Real.exp (2 * β * Mg)) • μ) :=
        integral_mono_measure hmarg (Filter.Eventually.of_forall hψ0)
          (hψi.smul_measure ENNReal.ofReal_ne_top)
    _ = Real.exp (2 * β * Mg) * ∫ z, ψ z ∂μ := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]

end Marg

/-! ### Joint pole domination -/

section PoleLe

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β t : ℝ}

theorem s74_pole_le (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg) (hβ : 0 ≤ β)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) (x : Euc d) :
    HRS.Whole.poleLaw d s (m + 2) β μ x t ≤
      ENNReal.ofReal (Real.exp (β * (Real.exp (2 * β * Mg) * Mg))) •
        HRS.Whole.cavityLaw d s (m + 2) β μ := by
  set P : Measure (EucConfig d (m + 1)) := HRS.Whole.cavityLaw d s (m + 2) β μ with hP
  haveI : IsProbabilityMeasure P := wr13a_cavityLaw_isProb hs0 hconv hβ (m + 2)
  set lam : ℝ := β / ((m + 2 : ℕ) : ℝ) with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ (Nat.cast_nonneg _)
  set K0 : ℝ := Real.exp (2 * β * Mg) with hK0
  set Kc : ℝ := β * (K0 * Mg) with hKc
  have hgm : Measurable (rieszKernel d s) := wr13a_g_meas hs0
  have hcoord : ∀ j : Fin (m + 1),
      Integrable (fun Y : EucConfig d (m + 1) => rieszKernel d s (x - Y j)) P ∧
        ∫ Y, rieszKernel d s (x - Y j) ∂P ≤ K0 * Mg := by
    intro j
    obtain ⟨h1, h2⟩ := s74_coord_integral hs0 hint hconv hMg hβ m j
      (ψ := fun z => rieszKernel d s (x - z)) (hgm.comp (measurable_const.sub measurable_id))
      (fun z => wr13a_g_nonneg hs0 _) (hint x)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (hconv x) (Real.exp_pos _).le)⟩
  set u : EucConfig d (m + 1) → ℝ := fun Y => t * lam * ∑ j, rieszKernel d s (x - Y j) with hu
  have hui : Integrable u P :=
    (integrable_finsetSum _ fun j _ => (hcoord j).1).const_mul _
  have hu0 : ∀ Y, 0 ≤ u Y := fun Y =>
    mul_nonneg (mul_nonneg ht hlam) (Finset.sum_nonneg fun j _ => wr13a_g_nonneg hs0 _)
  have hcoef : t * lam * ((m + 1 : ℕ) : ℝ) ≤ β := by
    have h := wr13a_lam_mul_le' (r := ((m + 1 : ℕ) : ℝ)) (c := 1) hβ (N := ((m + 2 : ℕ) : ℝ)) (by positivity)
      (by push_cast; linarith)
    have h2 : 0 ≤ lam * ((m + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have huK : ∫ Y, u Y ∂P ≤ Kc := by
    simp only [hu]
    rw [integral_const_mul, integral_finsetSum _ fun j _ => (hcoord j).1]
    have h1 : ∑ j : Fin (m + 1), ∫ Y, rieszKernel d s (x - Y j) ∂P ≤ ∑ _j : Fin (m + 1), (K0 * Mg) :=
      Finset.sum_le_sum fun j _ => (hcoord j).2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have hKM : 0 ≤ K0 * Mg := mul_nonneg (Real.exp_pos _).le hMg
    calc t * lam * ∑ j : Fin (m + 1), ∫ Y, rieszKernel d s (x - Y j) ∂P
        ≤ t * lam * (((m + 1 : ℕ) : ℝ) * (K0 * Mg)) :=
          mul_le_mul_of_nonneg_left (by simpa using h1) (mul_nonneg ht hlam)
      _ = (t * lam * ((m + 1 : ℕ) : ℝ)) * (K0 * Mg) := by ring
      _ ≤ β * (K0 * Mg) := mul_le_mul_of_nonneg_right hcoef hKM
  have hj := wr13a_jensen P hui hu0 huK
  have hΦ : Real.exp (-Kc) ≤ HRS.Whole.poleNormalizer d s (m + 2) β μ x t := by
    refine hj.trans (le_of_eq ?_)
    unfold HRS.Whole.poleNormalizer
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    simp only [hu, HRS.Whole.poleWeight]
    congr 1
    rw [hlamdef]
    push_cast
    rw [neg_mul]
    rfl
  have hw1 : ∀ Y, HRS.Whole.poleWeight d s (m + 2) β x t Y ≤ 1 := fun Y =>
    wr13a_poleWeight_le_one hs0 hβ ht (m + 2) x Y
  refine Measure.le_iff.2 fun B hB => ?_
  unfold HRS.Whole.poleLaw
  rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hB]
  refine mul_le_mul' ?_ ?_
  · calc (ENNReal.ofReal (HRS.Whole.poleNormalizer d s (m + 2) β μ x t))⁻¹
        ≤ (ENNReal.ofReal (Real.exp (-Kc)))⁻¹ := ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal hΦ)
      _ = ENNReal.ofReal (Real.exp Kc) := by
          rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg]
  · calc ∫⁻ Y in B, ENNReal.ofReal (HRS.Whole.poleWeight d s (m + 2) β x t Y) ∂P
        ≤ ∫⁻ _Y in B, 1 ∂P := lintegral_mono fun Y => ENNReal.ofReal_le_one.2 (hw1 Y)
      _ = P B := by simp

end PoleLe

/-! ### The conditional ratio -/

section Ratio

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β t : ℝ}

theorem s74_exp_two (u w b : ℝ) (hb : 0 ≤ b) (hu : -u ≤ b) (hw : 0 ≤ w) :
    |Real.exp (-u - w) - 1| ≤ Real.exp b * (w + |u|) := by
  have he1 : 1 ≤ Real.exp b := Real.one_le_exp hb
  have h1 := s74_exp_neg_sub_one_le u b hb hu
  have h2 : Real.exp (-u) ≤ Real.exp b := Real.exp_le_exp.2 hu
  have h3 : |Real.exp (-w) - 1| ≤ w := by
    have := Real.add_one_le_exp (-w)
    have h4 : Real.exp (-w) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [abs_of_nonpos (by linarith)]
    linarith
  have e : Real.exp (-u - w) - 1 = Real.exp (-u) * (Real.exp (-w) - 1) + (Real.exp (-u) - 1) := by
    rw [sub_eq_add_neg (-u) w, Real.exp_add]
    ring
  rw [e]
  calc |Real.exp (-u) * (Real.exp (-w) - 1) + (Real.exp (-u) - 1)|
      ≤ |Real.exp (-u) * (Real.exp (-w) - 1)| + |Real.exp (-u) - 1| := abs_add_le _ _
    _ ≤ Real.exp b * w + Real.exp b * |u| := by
        refine add_le_add ?_ h1
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul h2 h3 (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp b * (w + |u|) := by ring

theorem s74_u_integrable (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (lam β : ℝ) {m : ℕ}
    (Y : EucConfig d m) : Integrable (fun z => s74_u d s μ lam β Y z) μ := by
  have hj : ∀ j, Integrable (fun y => rieszKernel d s (y - Y j)) μ := fun j => by
    have : (fun y => rieszKernel d s (y - Y j)) = fun y => rieszKernel d s (Y j - y) :=
      funext fun y => wr13a_g_sub_swap _ _
    rw [this]; exact hint _
  have h1 : Integrable (fun y => lam * ∑ j, rieszKernel d s (y - Y j)) μ :=
    (integrable_finsetSum _ fun j _ => hj j).const_mul _
  have h2 : Integrable (fun y => β * HRS.Whole.convMeasure (rieszKernel d s) μ y) μ :=
    Integrable.of_bound (C := |β| * |Mg|) (((wr13a_conv_meas hs0 μ).const_mul β).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_of_nonneg (wr13a_conv_nonneg hs0 μ y)]
        exact (hconv y).trans (le_abs_self _))
  exact h1.sub h2

/-- `Zr = (Zc).toReal` is the Bochner integral. -/
theorem s74_Zr_eq (hs0 : 0 < s) (lam β t : ℝ) (x : Euc d) {m : ℕ} (Y : EucConfig d m) :
    (s74_Zc d s μ lam β t x Y).toReal =
      ∫ z, Real.exp (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z)) ∂μ := by
  unfold s74_Zc
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)]
  exact (((Real.measurable_exp.comp (((s74_u_meas_y hs0 μ lam β Y).neg).sub
    (((wr13a_g_meas hs0).comp (measurable_const.sub measurable_id)).const_mul _)))).aestronglyMeasurable)

theorem s74_Zr_sub_one (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg)
    {lam : ℝ} (hlam : 0 ≤ lam) (hβ : 0 ≤ β) (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Euc d) {m : ℕ}
    (Y : EucConfig d m) :
    |(s74_Zc d s μ lam β t x Y).toReal - 1| ≤
      Real.exp (β * Mg) * (lam * Mg + ∫ z, |s74_u d s μ lam β Y z| ∂μ) := by
  set b : ℝ := β * Mg with hb
  have hb0 : 0 ≤ b := mul_nonneg hβ hMg
  have hui := s74_u_integrable hs0 hint hconv lam β Y
  have hgx : Integrable (fun z => rieszKernel d s (x - z)) μ := hint x
  have hwi : Integrable (fun z => t * lam * rieszKernel d s (x - z)) μ := hgx.const_mul _
  have hgm : Measurable (rieszKernel d s) := wr13a_g_meas hs0
  have hum := s74_u_meas_y hs0 μ lam β Y
  have hF : Measurable fun z => Real.exp (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z)) :=
    Real.measurable_exp.comp ((hum.neg).sub ((hgm.comp (measurable_const.sub measurable_id)).const_mul _))
  have hFi : Integrable (fun z => Real.exp (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z))) μ :=
    Integrable.of_bound (C := Real.exp b) hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.2 ?_
        have h1 := s74_neg_u_le hs0 hconv hlam hβ Y z
        have h2 : 0 ≤ t * lam * rieszKernel d s (x - z) :=
          mul_nonneg (mul_nonneg ht hlam) (wr13a_g_nonneg hs0 _)
        linarith)
  rw [s74_Zr_eq hs0]
  have e1 : ∫ z, Real.exp (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z)) ∂μ - 1 =
      ∫ z, (Real.exp (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z)) - 1) ∂μ := by
    rw [integral_sub hFi (integrable_const _)]
    simp
  rw [e1]
  have hdom : Integrable (fun z => Real.exp b * (t * lam * rieszKernel d s (x - z) +
      |s74_u d s μ lam β Y z|)) μ := (hwi.add hui.abs).const_mul _
  calc |∫ z, (Real.exp (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z)) - 1) ∂μ|
      ≤ ∫ z, |Real.exp (-(s74_u d s μ lam β Y z) - t * lam * rieszKernel d s (x - z)) - 1| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z, Real.exp b * (t * lam * rieszKernel d s (x - z) + |s74_u d s μ lam β Y z|) ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _) hdom
          (Filter.Eventually.of_forall fun z => ?_)
        exact s74_exp_two _ _ b hb0 (s74_neg_u_le hs0 hconv hlam hβ Y z)
          (mul_nonneg (mul_nonneg ht hlam) (wr13a_g_nonneg hs0 _))
    _ = Real.exp b * (t * lam * ∫ z, rieszKernel d s (x - z) ∂μ + ∫ z, |s74_u d s μ lam β Y z| ∂μ) := by
        rw [integral_const_mul, integral_add hwi hui.abs, integral_const_mul]
    _ ≤ Real.exp b * (lam * Mg + ∫ z, |s74_u d s μ lam β Y z| ∂μ) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have h1 : ∫ z, rieszKernel d s (x - z) ∂μ ≤ Mg := hconv x
        have h2 : 0 ≤ ∫ z, rieszKernel d s (x - z) ∂μ := integral_nonneg fun z => wr13a_g_nonneg hs0 _
        have h3 : t * lam * ∫ z, rieszKernel d s (x - z) ∂μ ≤ lam * Mg := by
          calc t * lam * ∫ z, rieszKernel d s (x - z) ∂μ ≤ 1 * lam * Mg := by
                refine mul_le_mul (mul_le_mul_of_nonneg_right ht1 hlam) h1 h2 (by positivity)
            _ = lam * Mg := by ring
        linarith

/-- The pointwise conditional-ratio bound (`S:eq:conditional-ratio`). -/
theorem s74_ratio (hs0 : 0 < s) (hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hMg : 0 ≤ Mg)
    {lam : ℝ} (hlam : 0 ≤ lam) (hβ : 0 ≤ β) (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Euc d) {m : ℕ}
    (hK : lam * (t + m) ≤ β) (Y : EucConfig d m) (y : Euc d) :
    |Real.exp (-(s74_u d s μ lam β Y y)) / (s74_Zc d s μ lam β t x Y).toReal - 1| ≤
      Real.exp (2 * β * Mg) * (|s74_u d s μ lam β Y y| + lam * Mg + ∫ z, |s74_u d s μ lam β Y z| ∂μ) := by
  set b : ℝ := β * Mg with hb
  have hb0 : 0 ≤ b := mul_nonneg hβ hMg
  set Z : ℝ := (s74_Zc d s μ lam β t x Y).toReal with hZ
  have hZup : Z ≤ Real.exp b := by
    have := s74_Zc_le hs0 hconv hlam hβ ht x Y
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le this
  have hZlo : Real.exp (-b) ≤ Z := by
    have h1 := s74_Zc_ge hs0 hint hconv hMg hlam hβ ht x Y hK
    have h2 : s74_Zc d s μ lam β t x Y ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (s74_Zc_le hs0 hconv hlam hβ ht x Y)
    exact (ENNReal.ofReal_le_iff_le_toReal h2).1 h1
  have hZpos : 0 < Z := lt_of_lt_of_le (Real.exp_pos _) hZlo
  have h1 := s74_exp_neg_sub_one_le (s74_u d s μ lam β Y y) b hb0 (s74_neg_u_le hs0 hconv hlam hβ Y y)
  have h2 := s74_Zr_sub_one hs0 hint hconv hMg hlam hβ ht ht1 x Y
  rw [← hZ, ← hb] at h2
  have he : Real.exp (2 * β * Mg) = Real.exp b * Real.exp b := by
    rw [← Real.exp_add]; congr 1; rw [hb]; ring
  have hinv : 1 / Z ≤ Real.exp b := by
    rw [div_le_iff₀ hZpos]
    have : Real.exp b * Real.exp (-b) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos b]
  have e : Real.exp (-(s74_u d s μ lam β Y y)) / Z - 1 =
      (Real.exp (-(s74_u d s μ lam β Y y)) - Z) / Z := by field_simp
  rw [e, abs_div, abs_of_pos hZpos, div_eq_mul_one_div]
  have h3 : |Real.exp (-(s74_u d s μ lam β Y y)) - Z| ≤
      Real.exp b * |s74_u d s μ lam β Y y| + Real.exp b * (lam * Mg + ∫ z, |s74_u d s μ lam β Y z| ∂μ) := by
    calc |Real.exp (-(s74_u d s μ lam β Y y)) - Z|
        = |(Real.exp (-(s74_u d s μ lam β Y y)) - 1) + (1 - Z)| := by ring_nf
      _ ≤ |Real.exp (-(s74_u d s μ lam β Y y)) - 1| + |1 - Z| := abs_add_le _ _
      _ ≤ _ := by rw [abs_sub_comm 1 Z]; exact add_le_add h1 h2
  calc |Real.exp (-(s74_u d s μ lam β Y y)) - Z| * (1 / Z)
      ≤ (Real.exp b * |s74_u d s μ lam β Y y| + Real.exp b * (lam * Mg + ∫ z, |s74_u d s μ lam β Y z| ∂μ)) *
          Real.exp b :=
        mul_le_mul h3 hinv (by positivity) (by positivity)
    _ = Real.exp (2 * β * Mg) * (|s74_u d s μ lam β Y y| + lam * Mg + ∫ z, |s74_u d s μ lam β Y z| ∂μ) := by
        rw [he]; ring

end Ratio

/-! ### The abstract decomposition of the conditional potential -/

section Abstract

variable {m : ℕ}

theorem s74_coord_int (P : Measure (EucConfig d (m + 1))) [IsProbabilityMeasure P]
    (hmarg : ∀ j : Fin (m + 1), P.map (fun Y : EucConfig d (m + 1) => Y j) =
      P.map (fun Y : EucConfig d (m + 1) => Y 0))
    {F : Euc d → ℝ} (hF : Measurable F) (h0 : Integrable (fun Y : EucConfig d (m + 1) => F (Y 0)) P)
    (j : Fin (m + 1)) :
    Integrable (fun Y : EucConfig d (m + 1) => F (Y j)) P ∧
      ∫ Y, F (Y j) ∂P = ∫ Y, F (Y 0) ∂P := by
  have hm0 : Measurable (fun Y : EucConfig d (m + 1) => Y 0) := measurable_pi_apply 0
  have hmj : Measurable (fun Y : EucConfig d (m + 1) => Y j) := measurable_pi_apply j
  have hi0 : Integrable F (P.map (fun Y : EucConfig d (m + 1) => Y 0)) :=
    (integrable_map_measure hF.aestronglyMeasurable hm0.aemeasurable).2 h0
  rw [← hmarg j] at hi0
  refine ⟨(integrable_map_measure hF.aestronglyMeasurable hmj.aemeasurable).1 hi0, ?_⟩
  calc ∫ Y, F (Y j) ∂P = ∫ z, F z ∂(P.map (fun Y : EucConfig d (m + 1) => Y j)) :=
        (integral_map hmj.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ z, F z ∂(P.map (fun Y : EucConfig d (m + 1) => Y 0)) := by rw [hmarg j]
    _ = ∫ Y, F (Y 0) ∂P := integral_map hm0.aemeasurable hF.aestronglyMeasurable

theorem s74_T_bound (P : Measure (EucConfig d (m + 1))) [IsProbabilityMeasure P]
    (hmarg : ∀ j : Fin (m + 1), P.map (fun Y : EucConfig d (m + 1) => Y j) =
      P.map (fun Y : EucConfig d (m + 1) => Y 0))
    {ψ : Euc d → ℝ} (hψm : Measurable ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hψi : Integrable (fun Y : EucConfig d (m + 1) => ψ (Y 0)) P) {H : ℝ} (hH : 0 < H)
    {lam κ : ℝ} (hlam : 0 ≤ lam) {Vb : ℝ}
    (hvar : ∫ Y, (∑ j : Fin (m + 1), min (ψ (Y j)) H -
        ((m : ℝ) + 1) * ∫ Y', min (ψ (Y' 0)) H ∂P) ^ 2 ∂P ≤ Vb) :
    Integrable (fun Y : EucConfig d (m + 1) => |lam * ∑ j : Fin m, ψ (Y j.succ) - κ|) P ∧
    ∫ Y, |lam * ∑ j : Fin m, ψ (Y j.succ) - κ| ∂P ≤
      lam * (Real.sqrt Vb + H) + 2 * (lam * m * ∫ Y, (ψ (Y 0) - min (ψ (Y 0)) H) ∂P) +
        |lam * m * ∫ Y, ψ (Y 0) ∂P - κ| := by
  set f : Euc d → ℝ := fun z => min (ψ z) H with hf
  have hfm : Measurable f := hψm.min measurable_const
  have hf0 : ∀ z, 0 ≤ f z := fun z => le_min (hψ0 z) hH.le
  have hfH : ∀ z, f z ≤ H := fun z => min_le_right _ _
  have hm0 : Measurable (fun Y : EucConfig d (m + 1) => Y 0) := measurable_pi_apply 0
  have hfi0 : Integrable (fun Y : EucConfig d (m + 1) => f (Y 0)) P :=
    Integrable.of_bound (C := H) (hfm.comp hm0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]; exact hfH _)
  have hdm : Measurable fun z => ψ z - f z := hψm.sub hfm
  have hdi0 : Integrable (fun Y : EucConfig d (m + 1) => ψ (Y 0) - f (Y 0)) P := hψi.sub hfi0
  have hψj := fun j => s74_coord_int P hmarg hψm hψi j
  have hfj := fun j => s74_coord_int P hmarg hfm hfi0 j
  have hdj := fun j => s74_coord_int P hmarg hdm hdi0 j
  set cH : ℝ := ∫ Y, f (Y 0) ∂P with hcH
  set G : ℝ := ∫ Y, ψ (Y 0) ∂P with hG
  set D : ℝ := ∫ Y, (ψ (Y 0) - f (Y 0)) ∂P with hD
  have hD0 : 0 ≤ D := integral_nonneg fun Y => by
    show (0 : ℝ) ≤ ψ (Y 0) - f (Y 0)
    have : f (Y 0) ≤ ψ (Y 0) := min_le_left _ _
    linarith
  have hcH0 : 0 ≤ cH := integral_nonneg fun Y => hf0 _
  have hcHH : cH ≤ H := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun Y : EucConfig d (m + 1) => f (Y 0)) (C := H)
      (Filter.Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]; exact hfH _)
    have h2 : |cH| ≤ H := by simpa [Real.norm_eq_abs] using this
    exact (le_abs_self _).trans h2
  have hGD : D = G - cH := integral_sub hψi hfi0
  -- the three pieces
  set V : EucConfig d (m + 1) → ℝ := fun Y => lam * ∑ j : Fin m, (f (Y j.succ) - cH) with hV
  set R : EucConfig d (m + 1) → ℝ := fun Y => lam * ∑ j : Fin m, (ψ (Y j.succ) - f (Y j.succ)) with hR
  set c : ℝ := lam * m * cH - κ with hc
  have hT : ∀ Y : EucConfig d (m + 1), lam * ∑ j : Fin m, ψ (Y j.succ) - κ = V Y + R Y + c := by
    intro Y
    simp only [hV, hR, hc]
    have : ∑ j : Fin m, ψ (Y j.succ) = ∑ j : Fin m, ((f (Y j.succ) - cH) +
        (ψ (Y j.succ) - f (Y j.succ))) + m * cH := by
      have h : ∀ j : Fin m, (f (Y j.succ) - cH) + (ψ (Y j.succ) - f (Y j.succ)) = ψ (Y j.succ) - cH :=
        fun j => by ring
      simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [this, Finset.sum_add_distrib]; ring
  have hVi : Integrable V P :=
    ((integrable_finsetSum _ fun j _ => (hfj j.succ).1.sub (integrable_const cH))).const_mul _
  have hRi : Integrable R P :=
    ((integrable_finsetSum _ fun j _ => (hψj j.succ).1.sub (hfj j.succ).1)).const_mul _
  have hRnn : ∀ Y, 0 ≤ R Y := fun Y => mul_nonneg hlam (Finset.sum_nonneg fun j _ => by
    have : f (Y j.succ) ≤ ψ (Y j.succ) := min_le_left _ _
    linarith)
  have hTi : Integrable (fun Y : EucConfig d (m + 1) => lam * ∑ j : Fin m, ψ (Y j.succ) - κ) P := by
    have : (fun Y : EucConfig d (m + 1) => lam * ∑ j : Fin m, ψ (Y j.succ) - κ) =
        fun Y => V Y + R Y + c := funext hT
    rw [this]
    exact (hVi.add hRi).add (integrable_const c)
  refine ⟨hTi.abs, ?_⟩
  -- bound for |V|
  set W : EucConfig d (m + 1) → ℝ := fun Y => ∑ j : Fin (m + 1), f (Y j) - ((m : ℝ) + 1) * cH with hW
  have hWm : Measurable W := (Finset.measurable_sum _ fun j _ => hfm.comp (measurable_pi_apply j)).sub
    measurable_const
  have hWb : ∀ Y, |W Y| ≤ ((m : ℝ) + 1) * H + ((m : ℝ) + 1) * H := by
    intro Y
    have h1 : ∑ j : Fin (m + 1), f (Y j) ≤ ((m : ℝ) + 1) * H := by
      have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (m + 1)))) (fun j _ => hfH (Y j))
      simpa using this
    have h2 : 0 ≤ ∑ j : Fin (m + 1), f (Y j) := Finset.sum_nonneg fun j _ => hf0 _
    have h3 : ((m : ℝ) + 1) * cH ≤ ((m : ℝ) + 1) * H :=
      mul_le_mul_of_nonneg_left hcHH (by positivity)
    have h4 : 0 ≤ ((m : ℝ) + 1) * cH := by positivity
    simp only [hW]
    rw [abs_le]; constructor <;> linarith
  have hWint : ∫ Y, |W Y| ∂P ≤ Real.sqrt Vb :=
    (s74_abs_integral_le_sqrt P hWm hWb).trans (Real.sqrt_le_sqrt (by simpa [hW, hcH] using hvar))
  have hVW : ∀ Y, |V Y| ≤ lam * |W Y| + lam * H := by
    intro Y
    have e : V Y = lam * (W Y - (f (Y 0) - cH)) := by
      simp only [hV, hW]
      rw [Fin.sum_univ_succ (fun j : Fin (m + 1) => f (Y j))]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    have hU : |f (Y 0) - cH| ≤ H := by
      rw [abs_le]; constructor <;> linarith [hf0 (Y 0), hfH (Y 0)]
    rw [e, abs_mul, abs_of_nonneg hlam]
    calc lam * |W Y - (f (Y 0) - cH)| ≤ lam * (|W Y| + H) :=
          mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add le_rfl hU)) hlam
      _ = lam * |W Y| + lam * H := by ring
  have hWi : Integrable (fun Y => |W Y|) P :=
    Integrable.of_bound (C := ((m : ℝ) + 1) * H + ((m : ℝ) + 1) * H) hWm.abs.aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => by rw [Real.norm_eq_abs, abs_abs]; exact hWb Y)
  have hRint : ∫ Y, R Y ∂P = lam * m * D := by
    simp only [hR]
    rw [integral_const_mul, integral_finsetSum _ fun j _ => (hψj j.succ).1.sub (hfj j.succ).1]
    have h : ∀ j : Fin m, ∫ Y, (ψ (Y j.succ) - f (Y j.succ)) ∂P = D := fun j => (hdj j.succ).2
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hpt : ∀ Y, |lam * ∑ j : Fin m, ψ (Y j.succ) - κ| ≤ lam * |W Y| + lam * H + R Y + |c| := by
    intro Y
    rw [hT Y]
    have h0 := hVW Y
    have h1 : |V Y + R Y + c| ≤ |V Y| + |R Y| + |c| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    rw [abs_of_nonneg (hRnn Y)] at h1
    linarith
  have hA : Integrable (fun Y => lam * |W Y| + lam * H) P :=
    (hWi.const_mul lam).add (integrable_const _)
  have hRHSi : Integrable (fun Y => lam * |W Y| + lam * H + R Y + |c|) P :=
    (hA.add hRi).add (integrable_const _)
  have hcabs : |c| ≤ |lam * m * G - κ| + lam * m * D := by
    have e : c = (lam * m * G - κ) - lam * m * D := by
      simp only [hc]
      have : cH = G - D := by linarith
      rw [this]; ring
    have hD' : 0 ≤ lam * m * D := by positivity
    rw [e]
    calc |(lam * m * G - κ) - lam * m * D| ≤ |lam * m * G - κ| + |lam * m * D| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg hD']
  calc ∫ Y, |lam * ∑ j : Fin m, ψ (Y j.succ) - κ| ∂P
      ≤ ∫ Y, (lam * |W Y| + lam * H + R Y + |c|) ∂P := integral_mono hTi.abs hRHSi hpt
    _ = lam * ∫ Y, |W Y| ∂P + lam * H + ∫ Y, R Y ∂P + |c| := by
        have hX : Integrable (fun Y => lam * |W Y| + lam * H + R Y) P := hA.add hRi
        have hZ : Integrable (fun Y => lam * |W Y|) P := hWi.const_mul lam
        rw [integral_add hX (integrable_const _), integral_add hA hRi,
          integral_add hZ (integrable_const _), integral_const_mul]
        simp
    _ ≤ lam * (Real.sqrt Vb + H) + 2 * (lam * m * D) + |lam * m * G - κ| := by
        have h1 : lam * ∫ Y, |W Y| ∂P ≤ lam * Real.sqrt Vb := mul_le_mul_of_nonneg_left hWint hlam
        rw [hRint]
        nlinarith [hcabs]

end Abstract

/-! ### Comparison of two marginals through a bounded density and total variation -/

section Close

theorem s74_close_abstract {μ ν π : Measure (Euc d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π] {K0 : ℝ} (hK0 : 0 ≤ K0) (hν : ν ≤ ENNReal.ofReal K0 • μ)
    {φ : Euc d → ℝ} (hφm : Measurable φ) {C0 : ℝ} (hφb : ∀ x, 0 ≤ φ x ∧ φ x ≤ C0)
    (hπ : π = μ.withDensity fun x => ENNReal.ofReal (φ x)) {r : ℝ}
    (hφL2 : Real.sqrt (∫ x, (φ x - 1) ^ 2 ∂μ) ≤ r) {t : ℝ}
    (hTV : HRS.External.Entropy.tvDist π ν ≤ t)
    {ψ : Euc d → ℝ} (hψm : Measurable ψ) (hψ0 : ∀ z, 0 ≤ ψ z) {H : ℝ} (hH : 0 < H) {E : ℝ}
    (hψi : Integrable (fun z => ψ z - min (ψ z) H) μ)
    (hE : ∫ z, (ψ z - min (ψ z) H) ∂μ ≤ E) :
    Integrable ψ ν ∧ Integrable ψ μ ∧
      |∫ z, ψ z ∂ν - ∫ z, ψ z ∂μ| ≤ (K0 + 1) * E + H * (t + r) := by
  set f : Euc d → ℝ := fun z => min (ψ z) H with hf
  have hfm : Measurable f := hψm.min measurable_const
  have hf0 : ∀ z, 0 ≤ f z := fun z => le_min (hψ0 z) hH.le
  have hfH : ∀ z, f z ≤ H := fun z => min_le_right _ _
  have hfb : ∀ z, |f z| ≤ H := fun z => by rw [abs_of_nonneg (hf0 z)]; exact hfH z
  have hfiμ : Integrable f μ := Integrable.of_bound (C := H) hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall hfb)
  have hfiν : Integrable f ν := Integrable.of_bound (C := H) hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall hfb)
  have hfiπ : Integrable f π := Integrable.of_bound (C := H) hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall hfb)
  have hdν : Integrable (fun z => ψ z - f z) ν :=
    (hψi.smul_measure (c := ENNReal.ofReal K0) ENNReal.ofReal_ne_top).mono_measure hν
  have hψμ : Integrable ψ μ := by
    have e : ψ = fun z => (ψ z - f z) + f z := by funext z; ring
    rw [e]; exact hψi.add hfiμ
  have hψν : Integrable ψ ν := by
    have e : ψ = fun z => (ψ z - f z) + f z := by funext z; ring
    rw [e]; exact hdν.add hfiν
  refine ⟨hψν, hψμ, ?_⟩
  have hd0 : ∀ z, 0 ≤ ψ z - f z := fun z => sub_nonneg.2 (min_le_left _ _)
  have hD0 : 0 ≤ ∫ z, (ψ z - f z) ∂μ := integral_nonneg hd0
  have hDν : ∫ z, (ψ z - f z) ∂ν ≤ K0 * ∫ z, (ψ z - f z) ∂μ := by
    calc ∫ z, (ψ z - f z) ∂ν ≤ ∫ z, (ψ z - f z) ∂(ENNReal.ofReal K0 • μ) :=
          integral_mono_measure hν (Filter.Eventually.of_forall hd0)
            (hψi.smul_measure ENNReal.ofReal_ne_top)
      _ = K0 * ∫ z, (ψ z - f z) ∂μ := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal hK0, smul_eq_mul]
  have hDν0 : 0 ≤ ∫ z, (ψ z - f z) ∂ν := integral_nonneg hd0
  -- total variation part
  have hA : |∫ z, f z ∂π - ∫ z, f z ∂ν| ≤ H * t := by
    have := HRS.External.RefSmall.abs_integral_sub_le_tvDist_of_nonneg π ν hfm hH.le hf0 hfH
    exact this.trans (mul_le_mul_of_nonneg_left hTV hH.le)
  -- density part
  have hB : |∫ z, f z ∂π - ∫ z, f z ∂μ| ≤ H * r := by
    have hlt : ∀ᵐ x ∂μ, ENNReal.ofReal (φ x) < ∞ := Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
    have e1 : ∫ z, f z ∂π = ∫ z, φ z * f z ∂μ := by
      have hφe : Measurable fun x => ENNReal.ofReal (φ x) := ENNReal.measurable_ofReal.comp hφm
      rw [hπ, integral_withDensity_eq_integral_toReal_smul hφe hlt]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [smul_eq_mul, ENNReal.toReal_ofReal (hφb z).1]
    have hφi : Integrable (fun z => φ z * f z) μ :=
      Integrable.of_bound (C := C0 * H) (hφm.mul hfm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hφb z).1 (hf0 z))]
          exact mul_le_mul (hφb z).2 (hfH z) (hf0 z) ((hφb z).1.trans (hφb z).2))
    have e2 : ∫ z, φ z * f z ∂μ - ∫ z, f z ∂μ = ∫ z, (φ z - 1) * f z ∂μ := by
      rw [← integral_sub hφi hfiμ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      ring
    have hφ1 : Measurable fun z => φ z - 1 := hφm.sub measurable_const
    have hb1 : ∀ z, |φ z - 1| ≤ C0 + 1 := fun z => by
      rw [abs_le]; constructor <;> linarith [(hφb z).1, (hφb z).2]
    have h1 : ∫ z, |φ z - 1| ∂μ ≤ r :=
      (s74_abs_integral_le_sqrt μ hφ1 hb1).trans (by simpa using hφL2)
    have h2 : |∫ z, (φ z - 1) * f z ∂μ| ≤ H * ∫ z, |φ z - 1| ∂μ := by
      have hi2 : Integrable (fun z => |φ z - 1|) μ :=
        Integrable.of_bound (C := C0 + 1) hφ1.abs.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_abs]; exact hb1 z)
      calc |∫ z, (φ z - 1) * f z ∂μ| ≤ ∫ z, |(φ z - 1) * f z| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ z, H * |φ z - 1| ∂μ := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
              (hi2.const_mul H) (Filter.Eventually.of_forall fun z => ?_)
            show |(φ z - 1) * f z| ≤ H * |φ z - 1|
            rw [abs_mul, abs_of_nonneg (hf0 z), mul_comm]
            exact mul_le_mul_of_nonneg_right (hfH z) (abs_nonneg _)
        _ = H * ∫ z, |φ z - 1| ∂μ := integral_const_mul _ _
    rw [e1, e2]
    exact h2.trans (mul_le_mul_of_nonneg_left h1 hH.le)
  have hsplit : ∫ z, ψ z ∂ν - ∫ z, ψ z ∂μ =
      (∫ z, (ψ z - f z) ∂ν - ∫ z, (ψ z - f z) ∂μ) +
        ((∫ z, f z ∂ν - ∫ z, f z ∂π) + (∫ z, f z ∂π - ∫ z, f z ∂μ)) := by
    have e1 : ∫ z, ψ z ∂ν = ∫ z, (ψ z - f z) ∂ν + ∫ z, f z ∂ν := by
      rw [← integral_add hdν hfiν]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp)
    have e2 : ∫ z, ψ z ∂μ = ∫ z, (ψ z - f z) ∂μ + ∫ z, f z ∂μ := by
      rw [← integral_add hψi hfiμ]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [hf]; ring)
    rw [e1, e2]; ring
  rw [hsplit]
  have hA' : |∫ z, f z ∂ν - ∫ z, f z ∂π| ≤ H * t := by rw [abs_sub_comm]; exact hA
  have hE0 : 0 ≤ E := hD0.trans hE
  have hmid : |(∫ z, f z ∂ν - ∫ z, f z ∂π) + (∫ z, f z ∂π - ∫ z, f z ∂μ)| ≤ H * t + H * r :=
    (abs_add_le _ _).trans (add_le_add hA' hB)
  have hfirst : |∫ z, (ψ z - f z) ∂ν - ∫ z, (ψ z - f z) ∂μ| ≤ (K0 + 1) * E := by
    have hDμE : ∫ z, (ψ z - f z) ∂μ ≤ E := hE
    rw [abs_le]; constructor <;> nlinarith
  calc |(∫ z, (ψ z - f z) ∂ν - ∫ z, (ψ z - f z) ∂μ) +
        ((∫ z, f z ∂ν - ∫ z, f z ∂π) + (∫ z, f z ∂π - ∫ z, f z ∂μ))|
      ≤ |∫ z, (ψ z - f z) ∂ν - ∫ z, (ψ z - f z) ∂μ| +
        |(∫ z, f z ∂ν - ∫ z, f z ∂π) + (∫ z, f z ∂π - ∫ z, f z ∂μ)| := abs_add_le _ _
    _ ≤ (K0 + 1) * E + (H * t + H * r) := add_le_add hfirst hmid
    _ = (K0 + 1) * E + H * (t + r) := by ring

end Close

end HRS.MS.Wr
