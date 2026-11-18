import HRS.Equilibrium.Parametrix.PX3aAuxY

/-!
# Packet PX3a auxiliaries Z: the symmetric cancellation at `c = 1` (oddness of `∇E`)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma Efund_neg (y : Euc d) : Efund d (-y) = Efund d y := by
  simp [Efund]

lemma Efund_fderiv_odd {y : Euc d} (hy : y ≠ 0) (h : Euc d) :
    fderiv ℝ (Efund d) (-y) h = -(fderiv ℝ (Efund d) y h) := by
  have h1 : HasFDerivAt (Efund d) (fderiv ℝ (Efund d) (-y)) (-y) :=
    ((contDiffAt_Efund 1 (neg_ne_zero.mpr hy)).differentiableAt (by simp)).hasFDerivAt
  have h2 : HasFDerivAt (fun x : Euc d => -x) (-(ContinuousLinearMap.id ℝ (Euc d))) y :=
    (hasFDerivAt_id y).neg
  have h3 := h1.comp y h2
  have e : (Efund d ∘ fun x : Euc d => -x) = Efund d := funext Efund_neg
  rw [e] at h3
  rw [h3.fderiv]
  simp

lemma Efund_fderiv_diff (hd : 2 ≤ d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (y₀ y₁ h : Euc d) (m : ℝ), 0 < m →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, m ≤ ‖y₀ + t • (y₁ - y₀)‖) →
      |fderiv ℝ (Efund d) y₁ h - fderiv ℝ (Efund d) y₀ h| ≤ M * m ^ (-(d : ℝ)) * ‖y₁ - y₀‖ * ‖h‖ := by
  obtain ⟨M, hM0, hM⟩ := norm_iteratedFDeriv_Efund_le hd (j := 2) (by norm_num)
  refine ⟨M, hM0, fun y₀ y₁ h m hm hseg => ?_⟩
  set φ : Euc d → ℝ := fun y => fderiv ℝ (Efund d) y h with hφ
  set s : Set (Euc d) := segment ℝ y₀ y₁ with hs
  have hmem : ∀ y ∈ s, ∃ t ∈ Set.Icc (0 : ℝ) 1, y = y₀ + t • (y₁ - y₀) := by
    intro y hy
    rw [hs, segment_eq_image'] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨t, ht, rfl⟩
  have hnorm : ∀ y ∈ s, m ≤ ‖y‖ := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hmem y hy
    exact hseg t ht
  have hne : ∀ y ∈ s, y ≠ 0 := fun y hy h0 => by
    have := hnorm y hy; rw [h0, norm_zero] at this; linarith
  have hderiv : ∀ y ∈ s, HasFDerivWithinAt φ (fderiv ℝ φ y) s y := by
    intro y hy
    have hc : ContDiffAt ℝ 2 (Efund d) y := contDiffAt_Efund 2 (hne y hy)
    have hc1 : ContDiffAt ℝ 1 (fderiv ℝ (Efund d)) y := hc.fderiv_right (m := 1) (by norm_num)
    have hφc : ContDiffAt ℝ 1 φ y := hc1.clm_apply contDiffAt_const
    exact ((hφc.differentiableAt (by simp)).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ y ∈ s, ‖fderiv ℝ φ y‖ ≤ M * m ^ (-(d : ℝ)) * ‖h‖ := by
    intro y hy
    have hy0 := hne y hy
    have hc : ContDiffAt ℝ 2 (Efund d) y := contDiffAt_Efund 2 (hy0)
    have hc1 : ContDiffAt ℝ 1 (fderiv ℝ (Efund d)) y := hc.fderiv_right (m := 1) (by norm_num)
    have h1 := norm_iteratedFDeriv_clm_apply_const (c := h) (n := 1) hc1 (by norm_num)
    rw [norm_iteratedFDeriv_fderiv] at h1
    rw [← norm_iteratedFDeriv_one]
    refine h1.trans ?_
    have h2 := hM y hy0
    have h3 : ‖y‖ ^ ((2 : ℝ) - d - (2 : ℕ)) ≤ m ^ (-(d : ℝ)) := by
      have : ((2 : ℝ) - d - (2 : ℕ)) = -(d : ℝ) := by push_cast; ring
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos hm (hnorm y hy) (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
    calc ‖h‖ * ‖iteratedFDeriv ℝ (1 + 1) (Efund d) y‖ ≤ ‖h‖ * (M * m ^ (-(d : ℝ))) :=
          mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hM0)) (norm_nonneg _)
      _ = _ := by ring
  have hconv : Convex ℝ s := convex_segment y₀ y₁
  have := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound (left_mem_segment ℝ y₀ y₁)
    (right_mem_segment ℝ y₀ y₁)
  rw [← Real.norm_eq_abs]
  calc ‖φ y₁ - φ y₀‖ ≤ M * m ^ (-(d : ℝ)) * ‖h‖ * ‖y₁ - y₀‖ := this
    _ = _ := by ring

/-- The `X`-slice jet of the source, evaluated on `u`. -/
def Gslice (g : Euc d × Euc d → ℝ) (a : ℕ) (X0 : Euc d) (u : Fin a → Euc d) (w : Euc d) : ℝ :=
  (iteratedFDeriv ℝ a (fun X' => g (X', w)) X0) u

lemma Gslice_even {g : Euc d × Euc d → ℝ} (heven : ∀ X w, g (X, -w) = g (X, w)) (a : ℕ) (X0 : Euc d)
    (u : Fin a → Euc d) (w : Euc d) : Gslice g a X0 u (-w) = Gslice g a X0 u w := by
  unfold Gslice
  have : (fun X' => g (X', -w)) = fun X' => g (X', w) := funext fun X' => heven X' w
  rw [this]

lemma Gslice_continuousOn {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g)
    {a : ℕ} (hac : a ≤ m) (X0 : Euc d) (u : Fin a → Euc d) :
    ContinuousOn (Gslice g a X0 u) {w : Euc d | w ≠ 0} := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ a g) {p : Euc d × Euc d | p.2 ≠ 0} := by
    have := h.smooth.continuousOn_iteratedFDerivWithin (m := a) (by exact_mod_cast hac)
      isOpen_ne_snd.uniqueDiffOn
    exact this.congr (iteratedFDerivWithin_of_isOpen a isOpen_ne_snd).symm
  have h2 : ContinuousOn (fun w : Euc d => iteratedFDeriv ℝ a g (X0, w)) {w : Euc d | w ≠ 0} :=
    hcont.comp (continuous_const.prodMk continuous_id).continuousOn (fun w hw => hw)
  have h3 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin a => Euc d × Euc d) ℝ
    (fun k => ((u k, (0 : Euc d)) : Euc d × Euc d))).continuous.comp_continuousOn h2
  refine h3.congr fun w hw => ?_
  have := iteratedFDeriv_slice_inl_n isOpen_ne_snd (h.smooth) (e₁ := X0) (e₂ := w) (show (X0, w) ∈ {p : Euc d × Euc d | p.2 ≠ 0} from hw)
    (i := a) (by exact_mod_cast hac)
  simp only [Function.comp, Gslice, this, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

lemma Gslice_aesm (hd1 : 1 ≤ d) {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ}
    (h : SrcCls d σ b m A g) {a : ℕ} (hac : a ≤ m) (X0 : Euc d) (u : Fin a → Euc d) :
    AEStronglyMeasurable (Gslice g a X0 u) (volume : Measure (Euc d)) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have := (Gslice_continuousOn h hac X0 u).aestronglyMeasurable (isOpen_ne.measurableSet) (μ := volume)
  rwa [show {w : Euc d | w ≠ 0} = ({0}ᶜ : Set (Euc d)) from rfl, restrict_compl_singleton] at this

/-- The odd part: `∇E(-w)·h₀ · G(w)` on the annulus `2r ≤ |w| < 1/16`. -/
def PsiOdd (d : ℕ) (r : ℝ) (h₀ : Euc d) (G : Euc d → ℝ) (w : Euc d) : ℝ :=
  if 2 * r ≤ ‖w‖ ∧ ‖w‖ < 1 / 16 then fderiv ℝ (Efund d) (-w) h₀ * G w else 0

lemma PsiOdd_neg {r : ℝ} (hr : 0 < r) (h₀ : Euc d) {G : Euc d → ℝ} (hG : ∀ w, w ≠ 0 → G (-w) = G w)
    (w : Euc d) : PsiOdd d r h₀ G (-w) = -PsiOdd d r h₀ G w := by
  unfold PsiOdd
  by_cases hc : 2 * r ≤ ‖w‖ ∧ ‖w‖ < 1 / 16
  · have hw0 : w ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hc; linarith [hc.1]
    have hc' : 2 * r ≤ ‖-w‖ ∧ ‖-w‖ < 1 / 16 := by simpa [norm_neg] using hc
    rw [if_pos hc, if_pos hc', neg_neg, hG w hw0, Efund_fderiv_odd hw0]
    ring
  · have hc' : ¬ (2 * r ≤ ‖-w‖ ∧ ‖-w‖ < 1 / 16) := by simpa [norm_neg] using hc
    rw [if_neg hc, if_neg hc']
    simp

lemma PsiOdd_integral_zero {r : ℝ} (hr : 0 < r) (h₀ : Euc d) {G : Euc d → ℝ}
    (hG : ∀ w, w ≠ 0 → G (-w) = G w) : ∫ w, PsiOdd d r h₀ G w = 0 := by
  have h1 : ∫ w, PsiOdd d r h₀ G (-w) = ∫ w, PsiOdd d r h₀ G w :=
    integral_neg_eq_self (fun w => PsiOdd d r h₀ G w) (volume : Measure (Euc d))
  have h2 : ∫ w, PsiOdd d r h₀ G (-w) = -∫ w, PsiOdd d r h₀ G w := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun w => PsiOdd_neg hr h₀ hG w)
  linarith

lemma continuousOn_fderiv_Efund_neg (h₀ : Euc d) :
    ContinuousOn (fun w : Euc d => fderiv ℝ (Efund d) (-w) h₀) {w : Euc d | w ≠ 0} := by
  have h1 : ContinuousOn (fderiv ℝ (Efund d)) ({0}ᶜ : Set (Euc d)) :=
    (contDiffOn_Efund (d := d) ∞').continuousOn_fderiv_of_isOpen isOpen_compl_singleton (by simp)
  have h2 : ContinuousOn (fun w : Euc d => fderiv ℝ (Efund d) (-w)) {w : Euc d | w ≠ 0} :=
    h1.comp continuous_neg.continuousOn (fun w hw => by simpa using hw)
  exact (ContinuousLinearMap.apply ℝ ℝ h₀).continuous.comp_continuousOn h2

lemma PsiOdd_aesm (hd1 : 1 ≤ d) {r : ℝ} (h₀ : Euc d) {G : Euc d → ℝ}
    (hG : AEStronglyMeasurable G (volume : Measure (Euc d))) :
    AEStronglyMeasurable (PsiOdd d r h₀ G) (volume : Measure (Euc d)) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have h1 : AEStronglyMeasurable (fun w : Euc d => fderiv ℝ (Efund d) (-w) h₀) (volume : Measure (Euc d)) := by
    have := (continuousOn_fderiv_Efund_neg h₀).aestronglyMeasurable (isOpen_ne.measurableSet) (μ := volume)
    rwa [show {w : Euc d | w ≠ 0} = ({0}ᶜ : Set (Euc d)) from rfl, restrict_compl_singleton] at this
  have hS : MeasurableSet {w : Euc d | 2 * r ≤ ‖w‖ ∧ ‖w‖ < 1 / 16} :=
    (measurableSet_le measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
  have := (h1.mul hG).indicator hS
  refine this.congr (Eventually.of_forall fun w => ?_)
  by_cases hc : 2 * r ≤ ‖w‖ ∧ ‖w‖ < 1 / 16
  · simp [Set.indicator, PsiOdd, hc]
  · simp [Set.indicator, PsiOdd, hc]

lemma Lf_fderiv_eq {ρ : ℝ} (hρ : 0 < ρ) (κ : ℝ) {y : Euc d} (hy1 : ρ < ‖y‖) (hy2 : ‖y‖ < 1 / 2) :
    fderiv ℝ (Lf d κ ρ) y = fderiv ℝ (Efund d) y := by
  have hev : Lf d κ ρ =ᶠ[𝓝 y] fun u => Efund d u - κ := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy1,
      (isOpen_lt continuous_norm continuous_const).mem_nhds hy2] with u hu1 hu2
    have hu1' : ρ < ‖u‖ := hu1
    have hu2' : ‖u‖ < 1 / 2 := hu2
    simp only [Lf, px3a_zeta_eq_zero hρ hu1'.le, px3a_zeta_eq_one one_pos (by linarith : ‖u‖ ≤ 1 / 2)]
    ring
  rw [hev.fderiv_eq]
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hy1; linarith
  have hd : DifferentiableAt ℝ (Efund d) y := (contDiffAt_Efund 1 hy0).differentiableAt (by simp)
  exact fderiv_sub_const _ |>.trans rfl

set_option maxHeartbeats 1600000 in
lemma region2_bound (hd : 2 ≤ d) {ME : ℝ} (hME0 : 0 ≤ ME)
    (hME : ∀ (y₀ y₁ h : Euc d) (m : ℝ), 0 < m → (∀ t ∈ Set.Icc (0 : ℝ) 1, m ≤ ‖y₀ + t • (y₁ - y₀)‖) →
      |fderiv ℝ (Efund d) y₁ h - fderiv ℝ (Efund d) y₀ h| ≤ ME * m ^ (-(d : ℝ)) * ‖y₁ - y₀‖ * ‖h‖)
    {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ} (h : SrcCls d 1 b m A g) (hA : 0 ≤ A) {a : ℕ}
    (hac : a + 1 ≤ m) {r : ℝ} (hr : 0 < r) (X0 z0 : Euc d) (hz0 : ‖z0‖ = r)
    (u : Fin a → Euc d) (v : Fin 1 → Euc d) {w : Euc d} (hw0 : 2 * r ≤ ‖w‖) (hw1 : ‖w‖ < 1 / 16) :
    |farPsi d g (Ekap d r) (r / 8) X0 z0 u v w - PsiOdd d r (v 0) (Gslice g a X0 u) w| ≤
      (ME * 2 ^ d * r * (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) *
        (‖w‖ ^ (-((d : ℝ) + 1)) * lw ‖w‖ ^ b) := by
  have hρ : 0 < r / 8 := by positivity
  have hwpos : 0 < ‖w‖ := by linarith
  have hw0' : w ≠ 0 := norm_pos_iff.mp hwpos
  have hfp := farPsi_eq h hρ (Ekap d r) (a := a) (c := 1) hac X0 z0 u v hw0'
  have hy1 : r / 8 < ‖z0 - w‖ := by
    have := norm_sub_norm_le w z0
    rw [norm_sub_rev] at this
    linarith
  have hy2 : ‖z0 - w‖ < 1 / 2 := by
    have := norm_sub_le z0 w
    linarith
  have hcond : 2 * r ≤ ‖w‖ ∧ ‖w‖ < 1 / 16 := ⟨hw0, hw1⟩
  have hdiff : farPsi d g (Ekap d r) (r / 8) X0 z0 u v w - PsiOdd d r (v 0) (Gslice g a X0 u) w =
      (fderiv ℝ (Efund d) (z0 - w) (v 0) - fderiv ℝ (Efund d) (-w) (v 0)) * Gslice g a X0 u w := by
    rw [hfp]
    unfold PsiOdd
    rw [if_pos hcond, iteratedFDeriv_one_apply, Lf_fderiv_eq hρ (Ekap d r) hy1 hy2]
    simp only [Gslice]
    ring
  rw [hdiff, abs_mul]
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖w‖ / 2 ≤ ‖-w + t • ((z0 - w) - (-w))‖ := by
    intro t ht
    have e : -w + t • ((z0 - w) - (-w)) = -w + t • z0 := by congr 2; abel
    rw [e]
    have h1 := norm_sub_norm_le (-w) (-(t • z0))
    have e2 : -w - -(t • z0) = -w + t • z0 := by abel
    rw [e2, norm_neg] at h1
    have h2 : ‖t • z0‖ ≤ r := by
      rw [norm_smul, Real.norm_of_nonneg ht.1, hz0]
      nlinarith [ht.2]
    rw [norm_neg] at h1
    linarith
  have hd1 := hME (-w) (z0 - w) (v 0) (‖w‖ / 2) (by positivity) hseg
  have e3 : (z0 - w) - (-w) = z0 := by abel
  rw [e3, hz0] at hd1
  have hpow : (‖w‖ / 2) ^ (-(d : ℝ)) = 2 ^ (d : ℝ) * ‖w‖ ^ (-(d : ℝ)) := by
    rw [Real.div_rpow hwpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    ring
  rw [hpow] at hd1
  -- the slice bound
  have hG : |Gslice g a X0 u w| ≤ (2 * A * (‖w‖ ^ (-(1 : ℝ)) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖ := by
    unfold Gslice
    rw [← Real.norm_eq_abs]
    refine ((iteratedFDeriv ℝ a (fun X' => g (X', w)) X0).le_opNorm u).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => norm_nonneg _)
    refine (h.slice_bound (by omega) X0 w hw0').trans ?_
    have hs := SrcCls.weight_pure (zero_le_one' ℝ) b hwpos (by linarith)
    have : A * (1 + ‖w‖ ^ (-(1 : ℝ)) * lw ‖w‖ ^ b) ≤ A * (2 * (‖w‖ ^ (-(1 : ℝ)) * lw ‖w‖ ^ b)) :=
      mul_le_mul_of_nonneg_left hs hA
    refine this.trans (le_of_eq ?_)
    ring
  have hv0 : ∏ j : Fin 1, ‖v j‖ = ‖v 0‖ := by simp
  have hexp : ‖w‖ ^ (-(d : ℝ)) * ‖w‖ ^ (-(1 : ℝ)) = ‖w‖ ^ (-((d : ℝ) + 1)) := by
    rw [← Real.rpow_add hwpos]; congr 1; ring
  have hPu : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hwl : 0 ≤ ‖w‖ ^ (-(1 : ℝ)) * lw ‖w‖ ^ b :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (lw_pos _).le b)
  calc |fderiv ℝ (Efund d) (z0 - w) (v 0) - fderiv ℝ (Efund d) (-w) (v 0)| * |Gslice g a X0 u w|
      ≤ (ME * (2 ^ (d : ℝ) * ‖w‖ ^ (-(d : ℝ))) * r * ‖v 0‖) *
          ((2 * A * (‖w‖ ^ (-(1 : ℝ)) * lw ‖w‖ ^ b)) * ∏ i, ‖u i‖) := by
        refine mul_le_mul hd1 hG (abs_nonneg _) ?_
        have : 0 ≤ ‖w‖ ^ (-(d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
        have : 0 ≤ (2 : ℝ) ^ (d : ℝ) := Real.rpow_nonneg (by norm_num) _
        positivity
    _ = (ME * 2 ^ d * r * (2 * A * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖))) *
          ((‖w‖ ^ (-(d : ℝ)) * ‖w‖ ^ (-(1 : ℝ))) * lw ‖w‖ ^ b) := by
        rw [hv0, Real.rpow_natCast]; ring
    _ = _ := by rw [hexp]

set_option maxHeartbeats 800000 in
lemma PsiOdd_integrable (hd : 2 ≤ d) {MJ : ℝ} (hMJ0 : 0 ≤ MJ)
    (hMJ : ∀ y : Euc d, y ≠ 0 → ‖iteratedFDeriv ℝ 1 (Efund d) y‖ ≤ MJ * ‖y‖ ^ ((2 : ℝ) - d - (1 : ℕ)))
    {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ} (h : SrcCls d 1 b m A g) (hA : 0 ≤ A) {a : ℕ}
    (hac : a ≤ m) {r : ℝ} (hr : 0 < r) (X0 : Euc d) (u : Fin a → Euc d) (h₀ : Euc d) :
    Integrable (PsiOdd d r h₀ (Gslice g a X0 u)) := by
  have hd1 : 1 ≤ d := by omega
  set Kc : ℝ := ‖h₀‖ * MJ * (2 * r) ^ ((2 : ℝ) - d - (1 : ℕ)) *
    (A * (1 + (2 * r) ^ (-(1 : ℝ)) * lw (2 * r) ^ b) * ∏ i, ‖u i‖) with hKc
  have hKc0 : 0 ≤ Kc := by
    have h1 : 0 ≤ (2 * r) ^ ((2 : ℝ) - d - (1 : ℕ)) := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ (2 * r) ^ (-(1 : ℝ)) * lw (2 * r) ^ b :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (pow_nonneg (lw_pos _).le _)
    have h3 : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    have : 0 ≤ 1 + (2 * r) ^ (-(1 : ℝ)) * lw (2 * r) ^ b := by linarith
    positivity
  have hint : Integrable ((Metric.closedBall (0 : Euc d) (1 / 16)).indicator (fun _ => Kc)) :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  refine Integrable.mono' hint (PsiOdd_aesm hd1 h₀ (Gslice_aesm hd1 h hac X0 u)) (Eventually.of_forall fun w => ?_)
  unfold PsiOdd
  by_cases hc : 2 * r ≤ ‖w‖ ∧ ‖w‖ < 1 / 16
  · rw [if_pos hc]
    have hwc : w ∈ Metric.closedBall (0 : Euc d) (1 / 16) := by simpa using hc.2.le
    rw [Set.indicator_of_mem hwc]
    have hwpos : 0 < ‖w‖ := by linarith [hc.1]
    have hw0 : w ≠ 0 := norm_pos_iff.mp hwpos
    rw [norm_mul]
    have e1 : ‖fderiv ℝ (Efund d) (-w) h₀‖ ≤ ‖h₀‖ * MJ * (2 * r) ^ ((2 : ℝ) - d - (1 : ℕ)) := by
      have h1 := (fderiv ℝ (Efund d) (-w)).le_opNorm h₀
      have h2 := hMJ (-w) (neg_ne_zero.mpr hw0)
      rw [norm_iteratedFDeriv_one, norm_neg] at h2
      have h3 : ‖w‖ ^ ((2 : ℝ) - d - (1 : ℕ)) ≤ (2 * r) ^ ((2 : ℝ) - d - (1 : ℕ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hc.1 (by
          have : (2 : ℝ) ≤ d := by exact_mod_cast hd
          push_cast; linarith)
      calc ‖fderiv ℝ (Efund d) (-w) h₀‖ ≤ ‖fderiv ℝ (Efund d) (-w)‖ * ‖h₀‖ := h1
        _ ≤ (MJ * ‖w‖ ^ ((2 : ℝ) - d - (1 : ℕ))) * ‖h₀‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ ≤ (MJ * (2 * r) ^ ((2 : ℝ) - d - (1 : ℕ))) * ‖h₀‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hMJ0) (norm_nonneg _)
        _ = _ := by ring
    have e2 : ‖Gslice g a X0 u w‖ ≤ A * (1 + (2 * r) ^ (-(1 : ℝ)) * lw (2 * r) ^ b) * ∏ i, ‖u i‖ := by
      unfold Gslice
      refine ((iteratedFDeriv ℝ a (fun X' => g (X', w)) X0).le_opNorm u).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => norm_nonneg _)
      refine (h.slice_bound hac X0 w hw0).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hA
      have h3 : ‖w‖ ^ (-(1 : ℝ)) ≤ (2 * r) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hc.1 (by norm_num)
      have h4 : lw ‖w‖ ^ b ≤ lw (2 * r) ^ b :=
        pow_le_pow_left₀ (lw_pos _).le (lw_anti (by positivity) hc.1 (by linarith [hc.2])) b
      have h5 : 0 ≤ ‖w‖ ^ (-(1 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
      have h6 : 0 ≤ (2 * r) ^ (-(1 : ℝ)) := Real.rpow_nonneg (by positivity) _
      have h7 : 0 ≤ lw ‖w‖ ^ b := pow_nonneg (lw_pos _).le b
      have : ‖w‖ ^ (-(1 : ℝ)) * lw ‖w‖ ^ b ≤ (2 * r) ^ (-(1 : ℝ)) * lw (2 * r) ^ b :=
        mul_le_mul h3 h4 h7 h6
      show 1 + ‖w‖ ^ (-(1 : ℝ)) * lw ‖w‖ ^ b ≤ 1 + (2 * r) ^ (-(1 : ℝ)) * lw (2 * r) ^ b
      linarith
    rw [Real.norm_eq_abs]
    exact mul_le_mul e1 (by simpa [Real.norm_eq_abs] using e2) (norm_nonneg _)
      (by have := norm_nonneg (fderiv ℝ (Efund d) (-w) h₀); nlinarith [e1])
  · rw [if_neg hc]
    simp only [norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hKc0) w

set_option maxHeartbeats 3200000 in
/-- Refined base estimate at `σ = 1`, `c = 1` for sources even in `w` (no extra logarithm). -/
theorem base_pos_sym (hd : 2 ≤ d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d × Euc d → ℝ} {A : ℝ} (_h : SrcCls d 1 b m A g), 0 ≤ A →
      (∀ X w : Euc d, g (X, -w) = g (X, w)) → ∀ {a : ℕ}, a + 1 ≤ m →
      ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc d), ‖z0‖ = r →
      ∀ (u : Fin a → Euc d) (v : Fin 1 → Euc d),
      |iteratedFDeriv ℝ (a + 1) (newtonPot d g) (X0, z0) (pat u v)| ≤
        C * A * (1 + lw r ^ b) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hσd : (1 : ℝ) < d := by linarith
  obtain ⟨Cn, hCn0, hCn⟩ := near_val_any hd (σ := 1) zero_le_one b m
  obtain ⟨Ck, hCk0, hCk⟩ := far_kernel_bound hd (c := 1) le_rfl
  obtain ⟨C1, C2, hC10, hC20, hfe⟩ := far_estimate hd hσd ((d : ℝ) + 1) b
  obtain ⟨ME, hME0, hME⟩ := Efund_fderiv_diff hd
  obtain ⟨MJ, hMJ0, hMJ⟩ := norm_iteratedFDeriv_Efund_le hd (j := 1) le_rfl
  have he0n : (2 : ℝ) - d - (1 : ℕ) < 0 := by push_cast; linarith
  set K1 : ℝ := (1 / 16 : ℝ) ^ ((2 : ℝ) - d - (1 : ℕ)) with hK1
  have hK10 : 0 ≤ K1 := Real.rpow_nonneg (by norm_num) _
  set K2 : ℝ := ME * 2 ^ d with hK2
  have hK20 : 0 ≤ K2 := by positivity
  refine ⟨Cn + 2 * C1 * Ck * K1 + 2 * C2 * K2, by positivity,
    fun {g} {A} h hA heven a hac r hr hr1 X0 z0 hz0 u v => ?_⟩
  set P : ℝ := (∏ i, ‖u i‖) * ∏ j, ‖v j‖ with hP
  have hP0 : 0 ≤ P :=
    mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hρ : 0 < r / 8 := by positivity
  rw [newtonPot_pat_eq hd hσd hA h hac le_rfl hr hr1 X0 z0 hz0 (Ekap d r) u v]
  have hnear := hCn h hA hac hr hr1 X0 z0 hz0 u v
  obtain ⟨hp1, -, hp3⟩ := far_pointwise hd zero_le_one h hA hac hr hr1 X0 z0 hz0 u v hCk0 (hCk r hr) he0n
  have hψi : Integrable (fun w => farPsi d g (Ekap d r) (r / 8) X0 z0 u v w) := by
    obtain ⟨-, -, hi⟩ := newtonPot_FL hd hσd hA h hr hr1 hz0 (Ekap d r)
    have hp0 : ((X0, z0) : Euc d × Euc d) ∈ {p : Euc d × Euc d | ‖p.2 - z0‖ < r / 16} := by
      show ‖z0 - z0‖ < r / 16
      simp; positivity
    exact integrable_eval (hi (a + 1) hac (X0, z0) hp0).2 (pat u v)
  have hGev : ∀ w, w ≠ 0 → Gslice g a X0 u (-w) = Gslice g a X0 u w := fun w _ => Gslice_even heven a X0 u w
  have hΨi : Integrable (PsiOdd d r (v 0) (Gslice g a X0 u)) :=
    PsiOdd_integrable hd hMJ0 hMJ h hA (by omega) hr X0 u (v 0)
  have hΨ0 : ∫ w, PsiOdd d r (v 0) (Gslice g a X0 u) w = 0 := PsiOdd_integral_zero hr (v 0) hGev
  set Ψ := PsiOdd d r (v 0) (Gslice g a X0 u) with hΨ
  set M1 : ℝ := Ck * (r / 16) ^ ((2 : ℝ) - d - (1 : ℕ)) * (2 * A * P) with hM1
  set M2 : ℝ := K2 * r * (2 * A * P) with hM2
  have hM10 : 0 ≤ M1 := mul_nonneg (mul_nonneg hCk0 (Real.rpow_nonneg (by positivity) _))
    (mul_nonneg (mul_nonneg (by norm_num) hA) hP0)
  have hM20 : 0 ≤ M2 := mul_nonneg (mul_nonneg hK20 hr.le) (mul_nonneg (mul_nonneg (by norm_num) hA) hP0)
  have hfar := hfe r M1 M2 hr hr1 hM10 hM20 (fun w => farPsi d g (Ekap d r) (r / 8) X0 z0 u v w - Ψ w)
    (hψi.sub hΨi) ?_ ?_ ?_
  rotate_left
  · filter_upwards [hp1] with w hw hw2
    have : Ψ w = 0 := by
      simp only [hΨ, PsiOdd]; rw [if_neg]; intro hc; linarith [hc.1]
    simp only [this, sub_zero]
    exact hw hw2
  · filter_upwards [ae_ne_zero_euc (d := d) (by omega)] with w hw0 hw2 hw3
    rw [Real.norm_eq_abs]
    exact region2_bound hd hME0 hME h hA hac hr X0 z0 hz0 u v hw2 hw3
  · filter_upwards [hp3] with w hw hw1
    have : Ψ w = 0 := by
      simp only [hΨ, PsiOdd]; rw [if_neg]; intro hc; linarith [hc.2]
    simp only [this, sub_zero]
    exact hw hw1
  have hsplit : ∫ w, farPsi d g (Ekap d r) (r / 8) X0 z0 u v w =
      ∫ w, (farPsi d g (Ekap d r) (r / 8) X0 z0 u v w - Ψ w) := by
    rw [integral_sub hψi hΨi, hΨ0, sub_zero]
  rw [hsplit]
  set L : ℝ := lw r ^ b with hL
  have hL0 : 0 ≤ L := pow_nonneg (lw_pos _).le b
  have hX : 0 ≤ A * P := mul_nonneg hA hP0
  -- near term
  have t1 : Cn * A * (r ^ (-(1 + ((1 : ℕ) : ℝ))) * lw r ^ b) * r ^ (2 : ℝ) * P = (Cn * (A * P)) * L := by
    have e : r ^ (-(1 + ((1 : ℕ) : ℝ))) * r ^ (2 : ℝ) = 1 := by
      rw [← Real.rpow_add hr]
      have : -(1 + ((1 : ℕ) : ℝ)) + 2 = 0 := by push_cast; ring
      rw [this, Real.rpow_zero]
    calc _ = Cn * (A * P) * ((r ^ (-(1 + ((1 : ℕ) : ℝ))) * r ^ (2 : ℝ)) * lw r ^ b) := by ring
      _ = _ := by rw [e, hL]; ring
  -- far term 1
  have t2 : C1 * M1 * (r ^ ((d : ℝ) - 1) * lw r ^ b) = (2 * C1 * Ck * K1 * (A * P)) * L := by
    have e : (r / 16) ^ ((2 : ℝ) - d - (1 : ℕ)) * r ^ ((d : ℝ) - 1) = K1 := by
      rw [show r / 16 = (1 / 16 : ℝ) * r by ring, Real.mul_rpow (by norm_num) hr.le, hK1, mul_assoc,
        ← Real.rpow_add hr]
      have : ((2 : ℝ) - d - (1 : ℕ)) + ((d : ℝ) - 1) = 0 := by push_cast; ring
      rw [this, Real.rpow_zero, mul_one]
    calc _ = 2 * C1 * Ck * (A * P) * (((r / 16) ^ ((2 : ℝ) - d - (1 : ℕ)) * r ^ ((d : ℝ) - 1)) * lw r ^ b) := by
          rw [hM1]; ring
      _ = _ := by rw [e, hL]; ring
  -- far term 2
  have hne : ¬ ((d : ℝ) - ((d : ℝ) + 1) = 0) := by intro h0; linarith
  have t3 : C2 * M2 * (1 + r ^ ((d : ℝ) - ((d : ℝ) + 1)) * lw r ^ (b + if (d : ℝ) - ((d : ℝ) + 1) = 0 then 1 else 0)) ≤
      (2 * C2 * K2 * (A * P)) * (1 + L) := by
    rw [if_neg hne, add_zero]
    have e : r ^ ((d : ℝ) - ((d : ℝ) + 1)) = r⁻¹ := by
      rw [show (d : ℝ) - ((d : ℝ) + 1) = -1 by ring, Real.rpow_neg_one]
    rw [e]
    have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
    calc C2 * M2 * (1 + r⁻¹ * lw r ^ b) = (2 * C2 * K2 * (A * P)) * (r + L) := by
          rw [hM2, ← hL]
          field_simp
      _ ≤ (2 * C2 * K2 * (A * P)) * (1 + L) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC20) hK20) hX)
          linarith
  have hsum : |(∫ x, Ln d (Ekap d r) (r / 8) x * iteratedFDeriv ℝ (a + 1) g (X0, z0 - x) (pat u v)) +
      ∫ w, (farPsi d g (Ekap d r) (r / 8) X0 z0 u v w - Ψ w)| ≤
      (Cn * (A * P)) * L + ((2 * C1 * Ck * K1 * (A * P)) * L + (2 * C2 * K2 * (A * P)) * (1 + L)) := by
    refine (abs_add_le _ _).trans ?_
    have e1 := hnear.trans_eq t1
    have e2 : |∫ w, (farPsi d g (Ekap d r) (r / 8) X0 z0 u v w - Ψ w)| ≤
        (2 * C1 * Ck * K1 * (A * P)) * L + (2 * C2 * K2 * (A * P)) * (1 + L) := by
      rw [← Real.norm_eq_abs]
      refine hfar.trans ?_
      rw [t2]
      linarith
    linarith
  refine hsum.trans ?_
  have h1L : L ≤ 1 + L := by linarith
  calc (Cn * (A * P)) * L + ((2 * C1 * Ck * K1 * (A * P)) * L + (2 * C2 * K2 * (A * P)) * (1 + L))
      ≤ (Cn * (A * P)) * (1 + L) + ((2 * C1 * Ck * K1 * (A * P)) * (1 + L) + (2 * C2 * K2 * (A * P)) * (1 + L)) := by
        have a1 : (Cn * (A * P)) * L ≤ (Cn * (A * P)) * (1 + L) :=
          mul_le_mul_of_nonneg_left h1L (mul_nonneg hCn0 hX)
        have a2 : (2 * C1 * Ck * K1 * (A * P)) * L ≤ (2 * C1 * Ck * K1 * (A * P)) * (1 + L) :=
          mul_le_mul_of_nonneg_left h1L (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC10) hCk0) hK10) hX)
        linarith
    _ = _ := by simp only [hL]; ring

end HRS.Parx

end
