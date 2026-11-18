import HRS.MS.GenPathAux4

/-!
# S5.6 packet P3: the Duhamel remainder in `ℓ²` (`W:r2:general-orbits` consequence, S L4004-4012)

`s56_rem_l2`: if `|g_i(r)| ≤ A b_i e(r)` on `[0,t]` and `∑ b_i² < ∞`, then
`‖(∫_0^t g_i)_i‖_{ℓ²} ≤ A (∑ b_i²)^{1/2} ∫_0^T e`  (all in `ℝ≥0∞`, no integrability is assumed: the Bochner integral
of a non-integrable function is `0`).
`s56_rem_moment_p1`, `s56_rem_moment_p2`: `E ∫_0^T e ≤ T sup_r E e` and `(E (∫_0^T e)²)^{1/2} ≤ T sup_r (E e²)^{1/2}`.
Helper names carry the prefix `s56_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole

theorem s56_rem_l2 {ι : Type*} (b : ι → ℝ) (g : ι → ℝ → ℝ) {A : ℝ} (hA : 0 ≤ A) {t T : ℝ}
    (htT : t ≤ T) (e : ℝ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hg : ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) t, |g i r| ≤ A * b i * e r) :
    l2NormE (fun i => ∫ r in Set.Icc (0 : ℝ) t, g i r) ≤
      ENNReal.ofReal A * (∑' i, ENNReal.ofReal (b i ^ 2)) ^ (1 / 2 : ℝ) *
        ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (e r) := by
  set Ye : ℝ≥0∞ := ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (e r) with hYe
  have hone : ∀ i, ENNReal.ofReal |∫ r in Set.Icc (0 : ℝ) t, g i r| ≤ ENNReal.ofReal (A * b i) * Ye := by
    intro i
    have h1 : ENNReal.ofReal |∫ r in Set.Icc (0 : ℝ) t, g i r| ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal |g i r| := by
      have := enorm_integral_le_lintegral_enorm (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (g i)
      simpa [Real.enorm_eq_ofReal_abs] using this
    refine h1.trans ?_
    calc ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal |g i r|
        ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (A * b i) * ENNReal.ofReal (e r) := by
          refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
          rw [← ENNReal.ofReal_mul (mul_nonneg hA (hb i))]
          exact ENNReal.ofReal_le_ofReal (hg i r hr)
      _ = ENNReal.ofReal (A * b i) * ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (e r) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (A * b i) * Ye := by
          gcongr
          exact lintegral_mono_set (Set.Icc_subset_Icc_right htT)
  unfold l2NormE
  have hsq : ∀ i, ENNReal.ofReal ((∫ r in Set.Icc (0 : ℝ) t, g i r) ^ 2) ≤
      ENNReal.ofReal A ^ 2 * Ye ^ 2 * ENNReal.ofReal (b i ^ 2) := by
    intro i
    rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _)]
    calc ENNReal.ofReal |∫ r in Set.Icc (0 : ℝ) t, g i r| ^ 2
        ≤ (ENNReal.ofReal (A * b i) * Ye) ^ 2 := by gcongr; exact hone i
      _ = ENNReal.ofReal A ^ 2 * Ye ^ 2 * ENNReal.ofReal (b i ^ 2) := by
          rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_pow (hb i)]
          ring
  calc (∑' i, ENNReal.ofReal ((∫ r in Set.Icc (0 : ℝ) t, g i r) ^ 2)) ^ (1 / 2 : ℝ)
      ≤ (∑' i, ENNReal.ofReal A ^ 2 * Ye ^ 2 * ENNReal.ofReal (b i ^ 2)) ^ (1 / 2 : ℝ) := by
        gcongr with i
        exact hsq i
    _ = (ENNReal.ofReal A ^ 2 * Ye ^ 2 * ∑' i, ENNReal.ofReal (b i ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal A * (∑' i, ENNReal.ofReal (b i ^ 2)) ^ (1 / 2 : ℝ) * Ye := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        have h2 : ∀ x : ℝ≥0∞, (x ^ 2) ^ (1 / 2 : ℝ) = x := fun x => by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
        rw [h2, h2]
        ring

theorem s56_rem_moment_p1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ}
    (en : Ω → ℝ → ℝ)
    (hen : AEMeasurable (fun p : Ω × ℝ => en p.1 p.2) (P.prod (volume.restrict (Set.Icc 0 T))))
    {E : ℝ≥0∞} (hE : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ENNReal.ofReal (en ζ r) ∂P ≤ E) :
    ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (en ζ r)) ∂P ≤ E * ENNReal.ofReal T := by
  rw [lintegral_lintegral_swap hen.ennreal_ofReal]
  calc ∫⁻ r in Set.Icc (0 : ℝ) T, (∫⁻ ζ, ENNReal.ofReal (en ζ r) ∂P) ≤ ∫⁻ r in Set.Icc (0 : ℝ) T, E :=
        setLIntegral_mono' measurableSet_Icc hE
    _ = E * ENNReal.ofReal T := by rw [setLIntegral_const, Real.volume_Icc, sub_zero]

theorem s56_rem_moment_p2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ}
    (en : Ω → ℝ → ℝ)
    (hen : AEMeasurable (fun p : Ω × ℝ => en p.1 p.2) (P.prod (volume.restrict (Set.Icc 0 T))))
    {E : ℝ≥0∞} (hE : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ENNReal.ofReal (en ζ r) ^ (2 : ℝ) ∂P ≤ E ^ (2 : ℝ)) :
    (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (en ζ r)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤
      E * ENNReal.ofReal T := by
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  have hμuniv : μT Set.univ = ENNReal.ofReal T := by
    rw [hμT, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hsec : ∀ᵐ ζ ∂P, AEMeasurable (fun r => en ζ r) μT := by
    have := hen.aestronglyMeasurable.prodMk_left
    filter_upwards [this] with ζ hζ
    exact hζ.aemeasurable
  have h2 : ∀ᵐ ζ ∂P, (∫⁻ r, ENNReal.ofReal (en ζ r) ∂μT) ^ (2 : ℝ) ≤
      ENNReal.ofReal T * ∫⁻ r, ENNReal.ofReal (en ζ r) ^ (2 : ℝ) ∂μT := by
    filter_upwards [hsec] with ζ hζ
    have h := s56_lintegral_le_sqrt' μT hζ.ennreal_ofReal
    rw [hμuniv] at h
    calc (∫⁻ r, ENNReal.ofReal (en ζ r) ∂μT) ^ (2 : ℝ)
        ≤ (ENNReal.ofReal T ^ (1 / 2 : ℝ) * (∫⁻ r, ENNReal.ofReal (en ζ r) ^ (2 : ℝ) ∂μT) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal T * ∫⁻ r, ENNReal.ofReal (en ζ r) ^ (2 : ℝ) ∂μT := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          norm_num
  have hg2 : AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal (en p.1 p.2) ^ (2 : ℝ)) (P.prod μT) :=
    hen.ennreal_ofReal.pow_const _
  have h3 : ∫⁻ ζ, (∫⁻ r, ENNReal.ofReal (en ζ r) ∂μT) ^ (2 : ℝ) ∂P ≤ (E * ENNReal.ofReal T) ^ (2 : ℝ) := by
    calc ∫⁻ ζ, (∫⁻ r, ENNReal.ofReal (en ζ r) ∂μT) ^ (2 : ℝ) ∂P
        ≤ ∫⁻ ζ, ENNReal.ofReal T * ∫⁻ r, ENNReal.ofReal (en ζ r) ^ (2 : ℝ) ∂μT ∂P := lintegral_mono_ae h2
      _ = ENNReal.ofReal T * ∫⁻ ζ, ∫⁻ r, ENNReal.ofReal (en ζ r) ^ (2 : ℝ) ∂μT ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal T * ∫⁻ r, ∫⁻ ζ, ENNReal.ofReal (en ζ r) ^ (2 : ℝ) ∂P ∂μT := by
          rw [lintegral_lintegral_swap hg2]
      _ ≤ ENNReal.ofReal T * (E ^ (2 : ℝ) * ENNReal.ofReal T) := by
          gcongr
          calc ∫⁻ r, ∫⁻ ζ, ENNReal.ofReal (en ζ r) ^ (2 : ℝ) ∂P ∂μT ≤ ∫⁻ r, E ^ (2 : ℝ) ∂μT :=
                setLIntegral_mono' measurableSet_Icc hE
            _ = E ^ (2 : ℝ) * ENNReal.ofReal T := by rw [lintegral_const, hμuniv]
      _ = (E * ENNReal.ofReal T) ^ (2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
          have : ENNReal.ofReal T ^ (2 : ℝ) = ENNReal.ofReal T * ENNReal.ofReal T := by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, sq]
          rw [this]; ring
  calc (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (en ζ r)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ)
      ≤ ((E * ENNReal.ofReal T) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by gcongr
    _ = E * ENNReal.ofReal T := by rw [← ENNReal.rpow_mul]; norm_num

end HRS.MS.GenPath
