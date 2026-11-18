import HRS.MS.CritForcePartition
import HRS.MS.CritForceCoordinates

/-!
# S8.2 (core X, step "one-dimensional Sobolev bound in the observed time")

For an almost surely absolutely continuous process `t ↦ Y_t` on `[0,T]` with derivative `Y'`:
`E sup_{t ≤ T} Y_t² ≤ (2/T) ∫_0^T E Y_s² ds + 2T ∫_0^T E Y'_s² ds`.
This is the observed-time Sobolev step that the source uses for every old unit block (isometry for the
stochastic part, one time derivative from `𝒜 U_v φ_j`); it is deterministic plus Tonelli and does not
need measurability of the supremum.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82BD

open HRS HRS.Whole

lemma s82_sob_pointwise (T : ℝ) (hT : 0 ≤ T) (f g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) T, f t = f 0 + ∫ u in Set.Icc 0 t, g u) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T) :
    (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |f t|) ≤
      ENNReal.ofReal |f s| + ∫⁻ u in Set.Icc 0 T, ENNReal.ofReal |g u| := by
  have hint : ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable g volume x y := fun x hx y hy =>
    (hg.mono_set (Set.uIcc_subset_Icc hx hy)).intervalIntegrable
  have hI : Integrable (fun u => |g u|) (volume.restrict (Set.Icc 0 T)) := hg.abs
  have hIe : ENNReal.ofReal (∫ u in Set.Icc 0 T, |g u|) = ∫⁻ u in Set.Icc 0 T, ENNReal.ofReal |g u| :=
    ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun u => abs_nonneg _)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  rw [← hIe, ← ENNReal.ofReal_add (abs_nonneg _) (setIntegral_nonneg measurableSet_Icc
    fun u _ => abs_nonneg _)]
  refine iSup_le fun t => ENNReal.ofReal_le_ofReal ?_
  have hdiff : f t - f s = ∫ u in s..t, g u := by
    rw [hf t t.2, hf s hs, s82_Icc_integral_eq g t.2.1, s82_Icc_integral_eq g hs.1]
    have := intervalIntegral.integral_interval_sub_left (f := g) (μ := volume)
      (hint 0 h0 t t.2) (hint 0 h0 s hs)
    linarith
  have hbd : |∫ u in s..t, g u| ≤ ∫ u in Set.Icc 0 T, |g u| := by
    rcases le_total s t with hst | hst
    · refine (intervalIntegral.abs_integral_le_integral_abs hst).trans ?_
      rw [intervalIntegral.integral_of_le hst]
      refine setIntegral_mono_set hI (Filter.Eventually.of_forall fun u => abs_nonneg _) ?_
      refine Filter.Eventually.of_forall ?_
      exact (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 t.2.2) : _)
    · rw [intervalIntegral.integral_symm, abs_neg]
      refine (intervalIntegral.abs_integral_le_integral_abs hst).trans ?_
      rw [intervalIntegral.integral_of_le hst]
      refine setIntegral_mono_set hI (Filter.Eventually.of_forall fun u => abs_nonneg _) ?_
      refine Filter.Eventually.of_forall ?_
      exact (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc t.2.1 hs.2) : _)
  have : |f t| ≤ |f s| + |f t - f s| := by
    have := abs_sub_abs_le_abs_sub (f t) (f s)
    linarith [abs_sub_comm (f t) (f s)]
  calc |f t| ≤ |f s| + |f t - f s| := this
    _ ≤ |f s| + ∫ u in Set.Icc 0 T, |g u| := by rw [hdiff]; linarith

/-- Cauchy-Schwarz on `[0,T]` in `ℝ≥0∞`. -/
lemma s82_sob_cs (T : ℝ) (_hT : 0 ≤ T) (h : ℝ → ℝ≥0∞)
    (hm : AEMeasurable h (volume.restrict (Set.Icc 0 T))) :
    (∫⁻ u in Set.Icc 0 T, h u) ^ 2 ≤ ENNReal.ofReal T * ∫⁻ u in Set.Icc 0 T, (h u) ^ 2 := by
  have hHC : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Icc (0 : ℝ) T)) hHC
    (f := fun _ => (1 : ℝ≥0∞)) (g := h) aemeasurable_const hm
  have e1 : (∫⁻ u in Set.Icc (0 : ℝ) T, (((fun _ => (1 : ℝ≥0∞)) * h : ℝ → ℝ≥0∞) u)) =
      ∫⁻ u in Set.Icc 0 T, h u := by
    simp
  have e2 : (∫⁻ u in Set.Icc (0 : ℝ) T, (1 : ℝ≥0∞) ^ (2 : ℝ)) = ENNReal.ofReal T := by
    simp
  rw [e1, e2] at key
  calc (∫⁻ u in Set.Icc 0 T, h u) ^ 2
      ≤ ((ENNReal.ofReal T) ^ (1 / 2 : ℝ) *
          (∫⁻ a in Set.Icc (0 : ℝ) T, h a ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 := by
        refine pow_le_pow_left' ?_ 2
        simpa using key
    _ = ENNReal.ofReal T * ∫⁻ u in Set.Icc 0 T, (h u) ^ 2 := by
        rw [mul_pow, s82_sqrt_sq, s82_sqrt_sq]
        simp only [ENNReal.rpow_two]

lemma s82_two_sq (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two] at h
  calc (a + b) ^ 2 ≤ (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) * (a ^ 2 + b ^ 2) := h
    _ = 2 * a ^ 2 + 2 * b ^ 2 := by
        norm_num [mul_add]

/-- Deterministic form, one sample: for every `s ∈ [0,T]`
`(sup_t |Y_t|)² ≤ 2|Y_s|² + 2T ∫_0^T |Y'|²`. -/
lemma s82_sob_sq_pointwise (T : ℝ) (hT : 0 ≤ T) (f g : ℝ → ℝ)
    (hg : IntegrableOn g (Set.Icc 0 T))
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) T, f t = f 0 + ∫ u in Set.Icc 0 t, g u) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T) :
    (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |f t|) ^ 2 ≤
      2 * ENNReal.ofReal (f s ^ 2) +
        2 * (ENNReal.ofReal T * ∫⁻ u in Set.Icc 0 T, ENNReal.ofReal (g u ^ 2)) := by
  have h1 := s82_sob_pointwise T hT f g hg hf hs
  have h2 := pow_le_pow_left' h1 2
  refine h2.trans ((s82_two_sq _ _).trans ?_)
  have e1 : ENNReal.ofReal |f s| ^ 2 = ENNReal.ofReal (f s ^ 2) := by
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hm : AEMeasurable (fun u => ENNReal.ofReal |g u|) (volume.restrict (Set.Icc 0 T)) :=
    hg.aestronglyMeasurable.aemeasurable.norm.ennreal_ofReal
  have e2 := s82_sob_cs T hT _ hm
  have e3 : (∫⁻ u in Set.Icc 0 T, ENNReal.ofReal |g u| ^ 2) =
      ∫⁻ u in Set.Icc 0 T, ENNReal.ofReal (g u ^ 2) := by
    refine lintegral_congr fun u => ?_
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [e3] at e2
  rw [e1]
  gcongr

/-- **Observed-time Sobolev bound in `L²(P)`**:
`E sup_{t ≤ T} Y_t² ≤ (2/T) ∫_0^T E Y_s² ds + 2T ∫_0^T E Y'_s² ds` for an almost surely absolutely
continuous process `Y_t = Y_0 + ∫_0^t Y'`. -/
theorem s82_sobolev_sup {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (hT : 0 < T) (Y Y' : ℝ → Ω → ℝ)
    (hY : ∀ᵐ ζ ∂P, IntegrableOn (fun u => Y' u ζ) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, Y t ζ = Y 0 ζ + ∫ u in Set.Icc 0 t, Y' u ζ)
    (hYm : AEMeasurable (fun p : Ω × ℝ => Y p.2 p.1) (P.prod (volume.restrict (Set.Icc 0 T))))
    (hY'm : AEMeasurable (fun p : Ω × ℝ => Y' p.2 p.1) (P.prod (volume.restrict (Set.Icc 0 T)))) :
    ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |Y t ζ|) ^ 2 ∂P ≤
      2 * (ENNReal.ofReal T)⁻¹ * (∫⁻ s in Set.Icc 0 T, ∫⁻ ζ, ENNReal.ofReal (Y s ζ ^ 2) ∂P) +
        2 * ENNReal.ofReal T * (∫⁻ s in Set.Icc 0 T, ∫⁻ ζ, ENNReal.ofReal (Y' s ζ ^ 2) ∂P) := by
  have hTpos : (ENNReal.ofReal T) ≠ 0 := by simpa using hT
  have hTtop : (ENNReal.ofReal T) ≠ ⊤ := ENNReal.ofReal_ne_top
  set ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  -- the two joint integrands
  have hy : AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal (Y p.2 p.1 ^ 2)) (P.prod ν) :=
    (hYm.pow_const 2).ennreal_ofReal
  have hy' : AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal (Y' p.2 p.1 ^ 2)) (P.prod ν) :=
    (hY'm.pow_const 2).ennreal_ofReal
  have hI1 : AEMeasurable (fun ζ => ∫⁻ s, ENNReal.ofReal (Y s ζ ^ 2) ∂ν) P :=
    hy.lintegral_prod_right'
  -- pointwise in the sample
  have hpt : ∀ᵐ ζ ∂P, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |Y t ζ|) ^ 2 ≤
      2 * (ENNReal.ofReal T)⁻¹ * ∫⁻ s, ENNReal.ofReal (Y s ζ ^ 2) ∂ν +
        2 * ENNReal.ofReal T * ∫⁻ u, ENNReal.ofReal (Y' u ζ ^ 2) ∂ν := by
    filter_upwards [hY] with ζ hζ
    obtain ⟨hg, hf⟩ := hζ
    have hs := fun s (hs : s ∈ Set.Icc (0 : ℝ) T) => s82_sob_sq_pointwise T hT.le (fun t => Y t ζ)
      (fun u => Y' u ζ) hg hf hs
    set S := (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |Y t ζ|) ^ 2 with hS
    set G := ∫⁻ u, ENNReal.ofReal (Y' u ζ ^ 2) ∂ν with hG
    have h1 : ∫⁻ _s, S ∂ν ≤ ∫⁻ s, (2 * ENNReal.ofReal (Y s ζ ^ 2) +
        2 * (ENNReal.ofReal T * G)) ∂ν := by
      refine setLIntegral_mono' measurableSet_Icc fun s hs' => ?_
      exact hs s hs'
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by simp),
      lintegral_const, lintegral_const] at h1
    have hν1 : ν Set.univ = ENNReal.ofReal T := by simp [hν]
    rw [hν1] at h1
    have h2 : ENNReal.ofReal T * S ≤ 2 * ∫⁻ s, ENNReal.ofReal (Y s ζ ^ 2) ∂ν +
        ENNReal.ofReal T * (2 * (ENNReal.ofReal T * G)) := by
      simpa [mul_comm] using h1
    have h3 := (ENNReal.mul_le_iff_le_inv hTpos hTtop).1 h2
    refine h3.trans (le_of_eq ?_)
    rw [mul_add, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hTpos hTtop, one_mul]
    ring
  calc ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |Y t ζ|) ^ 2 ∂P
      ≤ ∫⁻ ζ, (2 * (ENNReal.ofReal T)⁻¹ * ∫⁻ s, ENNReal.ofReal (Y s ζ ^ 2) ∂ν +
        2 * ENNReal.ofReal T * ∫⁻ u, ENNReal.ofReal (Y' u ζ ^ 2) ∂ν) ∂P := lintegral_mono_ae hpt
    _ = 2 * (ENNReal.ofReal T)⁻¹ * ∫⁻ ζ, ∫⁻ s, ENNReal.ofReal (Y s ζ ^ 2) ∂ν ∂P +
        2 * ENNReal.ofReal T * ∫⁻ ζ, ∫⁻ u, ENNReal.ofReal (Y' u ζ ^ 2) ∂ν ∂P := by
        rw [lintegral_add_left' (hI1.const_mul _), lintegral_const_mul'' _ hI1,
          lintegral_const_mul'' _ hy'.lintegral_prod_right']
    _ = _ := by
        rw [lintegral_lintegral_swap (f := fun ζ s => ENNReal.ofReal (Y s ζ ^ 2)) hy,
          lintegral_lintegral_swap (f := fun ζ s => ENNReal.ofReal (Y' s ζ ^ 2)) hy']

end HRS.MS.S82BD
