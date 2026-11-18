import HRS.Whole.Thermal
import HRS.MS.SteAux1
import HRS.MS.SteAux2

/-!
# C-STE: proof of `HRS.Whole.logThermal_stereographic`

Conjunct (2) (`HasSphericalBound`) is `ste_hasSphericalBound` (`SteAux1`), from the merged
`logThermal_bounds_proof` and boundedness of `(1+t)^{β/2+d} e^{-βat/2}`.

Conjunct (1): for measurable `S ⊂ ℝ^{d+1}` put `A = u⁻¹ S` (`u = stereoInv`).  On `E = ℝ^{d+1}`
(coordinates `z = (x, s)`) the map `G(x,s) = s (2x, |x|²-1) = s(1+|x|²) · u(x)` is injective on `s > 0`
with `|det G'| = (2s)^d (1+|x|²)` (`SteAux2`).  The image of `{x ∈ A, 0 < s < 1/(1+|x|²)}` lies in the cone
`(0,1)·(S ∩ S^d)`, whose volume times `d+1` is `sphereSurface d S` (`Measure.toSphere_apply'`).  By the change of
variables and Tonelli, `(d+1) · vol(G(B)) = ∫_A (2/(1+|x|²))^d dx`, and `ρ ≤ A₀ (1+|x|²)^{-d}`
(`ste_pointwise_bound`) gives `ν(S) = ∫_A ρ ≤ (A₀/2^d) · sphereSurface d S`.  No statement was adjusted.

Exports: `logThermal_stereographic_proof : type_of% @HRS.Whole.logThermal_stereographic`.
-/

open MeasureTheory
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- The point `x = (z_0, …, z_{d-1}) ∈ ℝ^d`. -/
def steX (z : Fin (d + 1) → ℝ) : Euc d := WithLp.toLp 2 (fun j => z (Fin.castSucc j))

lemma steX_norm_sq (z : Fin (d + 1) → ℝ) : ‖steX z‖ ^ 2 = steQ z := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [steX, steQ]

/-- The cone parametrisation `G(x, s) = s (1+|x|²) · u(x)` of the inverse stereographic
projection `u = stereoInv`. -/
lemma ste_toLp_G {z : Fin (d + 1) → ℝ} (hz : 0 < z (Fin.last d)) :
    WithLp.toLp 2 (steG z) = (z (Fin.last d) * (1 + ‖steX z‖ ^ 2)) • stereoInv (steX z) := by
  have hq : 0 < 1 + steQ z := by rw [← steX_norm_sq]; positivity
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [PiLp.smul_apply, stereoInv, smul_eq_mul, steX_norm_sq]
    rw [steG_last hz]
    simp only [Fin.snoc_last]
    field_simp
  · simp only [PiLp.smul_apply, stereoInv, smul_eq_mul, steX_norm_sq]
    rw [steG_castSucc hz]
    simp only [Fin.snoc_castSucc, steX]
    field_simp

lemma ste_norm_stereoInv (x : Euc d) : ‖stereoInv x‖ = 1 := by
  have hq : 0 < 1 + ‖x‖ ^ 2 := by positivity
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [stereoInv, Fin.snoc_castSucc, Fin.snoc_last, Real.norm_eq_abs, sq_abs]
  have hn : ∑ j : Fin d, x j ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  have hs : ∑ j : Fin d, (2 * x j / (1 + ‖x‖ ^ 2)) ^ 2 = 4 * ‖x‖ ^ 2 / (1 + ‖x‖ ^ 2) ^ 2 := by
    rw [← hn, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow]; ring
  rw [hs]
  field_simp
  ring

/-- `|y|²` on `ℝ^d` as a sum of squares. -/
def steQ' (y : Fin d → ℝ) : ℝ := ∑ j, y j ^ 2

lemma steQ'_nonneg (y : Fin d → ℝ) : 0 ≤ steQ' y := Finset.sum_nonneg fun j _ => sq_nonneg _

lemma steQ_eq (z : Fin (d + 1) → ℝ) : steQ z = steQ' (fun j => z (Fin.castSucc j)) := rfl

lemma steQ'_continuous : Continuous (steQ' : (Fin d → ℝ) → ℝ) := by
  unfold steQ'; fun_prop

/-- The radial integral `∫_0^{1/q} (2s)^d q ds = (2/q)^d/(d+1)`. -/
lemma ste_radial {q : ℝ} (hq : 0 < q) :
    ∫⁻ s in Set.Ioo (0 : ℝ) (1 / q), ENNReal.ofReal ((2 * s) ^ d * q) =
      ENNReal.ofReal ((2 / q) ^ d / (d + 1)) := by
  have hc : (0 : ℝ) ≤ 1 / q := by positivity
  have hcont : Continuous fun s : ℝ => (2 * s) ^ d * q := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun s hs => ?_))]
  · congr 1
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hc]
    simp only [mul_pow]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_pow]
    rw [zero_pow (Nat.succ_ne_zero d), sub_zero, div_pow, pow_succ]
    field_simp
    rw [div_pow]
    field_simp
    ring
  · have : 0 ≤ s := hs.1.le
    simp only [Pi.zero_apply]
    positivity

/-- The parameter region `{(x, s) : x ∈ A', 0 < s, s (1+|x|²) < 1}`. -/
def steB (A' : Set (Fin d → ℝ)) : Set (Fin (d + 1) → ℝ) :=
  {z | 0 < z (Fin.last d) ∧ z (Fin.last d) * (1 + steQ z) < 1 ∧ (fun j => z (Fin.castSucc j)) ∈ A'}

lemma steB_measurable {A' : Set (Fin d → ℝ)} (hA' : MeasurableSet A') : MeasurableSet (steB A') := by
  have hQ : Measurable (steQ : (Fin (d + 1) → ℝ) → ℝ) := by
    unfold steQ; fun_prop
  have hl : Measurable fun z : Fin (d + 1) → ℝ => z (Fin.last d) := measurable_pi_apply _
  have hx : Measurable fun z : Fin (d + 1) → ℝ => fun j : Fin d => z (Fin.castSucc j) :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  refine (measurableSet_lt measurable_const hl).inter
    ((measurableSet_lt (hl.mul (measurable_const.add hQ)) measurable_const).inter (hx hA'))

/-- Fubini for the cone parametrisation. -/
lemma ste_lintegral_B {A' : Set (Fin d → ℝ)} (hA' : MeasurableSet A') :
    ∫⁻ z in steB A', ENNReal.ofReal ((2 * z (Fin.last d)) ^ d * (1 + steQ z)) =
      ∫⁻ y in A', ENNReal.ofReal ((2 / (1 + steQ' y)) ^ d / (d + 1)) := by
  classical
  let F : (Fin (d + 1) → ℝ) → ℝ≥0∞ := fun z => ENNReal.ofReal ((2 * z (Fin.last d)) ^ d * (1 + steQ z))
  let T : Set (ℝ × (Fin d → ℝ)) := {p | 0 < p.1 ∧ p.1 * (1 + steQ' p.2) < 1 ∧ p.2 ∈ A'}
  let g : ℝ × (Fin d → ℝ) → ℝ≥0∞ := T.indicator fun p => ENNReal.ofReal ((2 * p.1) ^ d * (1 + steQ' p.2))
  have hT : MeasurableSet T := by
    have h2 : Measurable fun p : ℝ × (Fin d → ℝ) => steQ' p.2 :=
      steQ'_continuous.measurable.comp measurable_snd
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt (measurable_fst.mul (measurable_const.add h2)) measurable_const).inter
        (measurable_snd hA'))
  have hg : Measurable g := by
    refine Measurable.indicator ?_ hT
    refine ENNReal.measurable_ofReal.comp ?_
    have h2 : Measurable fun p : ℝ × (Fin d → ℝ) => steQ' p.2 :=
      steQ'_continuous.measurable.comp measurable_snd
    exact ((measurable_const.mul measurable_fst).pow_const d).mul (measurable_const.add h2)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d)
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d)
  have hind : ∀ z, (steB A').indicator F z = g (e z) := by
    intro z
    have he : e z = (z (Fin.last d), fun j => z (Fin.castSucc j)) := by
      refine Prod.ext ?_ (funext fun j => ?_)
      · simp [e]
      · simp [e, Fin.succAbove_last]; rfl
    rw [he]
    by_cases hz : z ∈ steB A'
    · have hz' : (z (Fin.last d), fun j => z (Fin.castSucc j)) ∈ T := by
        simpa [T, steB, steQ_eq] using hz
      simp only [g]
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz']
      simp [F, steQ_eq]
    · have hz' : (z (Fin.last d), fun j => z (Fin.castSucc j)) ∉ T := by
        simpa [T, steB, steQ_eq] using hz
      simp only [g]
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']
  have h1 : ∫⁻ z in steB A', ENNReal.ofReal ((2 * z (Fin.last d)) ^ d * (1 + steQ z)) =
      ∫⁻ z, g (e z) := by
    rw [← lintegral_congr hind]
    exact (lintegral_indicator (steB_measurable hA') F).symm
  rw [h1, hmp.lintegral_comp_emb e.measurableEmbedding g]
  rw [Measure.volume_eq_prod, lintegral_prod_symm g hg.aemeasurable]
  rw [← lintegral_indicator hA']
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ A'
  · rw [Set.indicator_of_mem hy]
    have hq : 0 < 1 + steQ' y := by have := steQ'_nonneg y; linarith
    rw [← ste_radial hq, ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ Set.Ioo (0 : ℝ) (1 / (1 + steQ' y))
    · rw [Set.indicator_of_mem hs]
      have : (s, y) ∈ T := by
        refine ⟨hs.1, ?_, hy⟩
        have := hs.2
        rwa [lt_div_iff₀ hq] at this
      simp [g, this]
    · rw [Set.indicator_of_notMem hs]
      have : (s, y) ∉ T := by
        rintro ⟨h1, h2, -⟩
        apply hs
        refine ⟨h1, ?_⟩
        rwa [lt_div_iff₀ hq]
      simp [g, this]
  · rw [Set.indicator_of_notMem hy]
    have : ∀ s : ℝ, g (s, y) = 0 := fun s => by
      have : (s, y) ∉ T := fun h => hy h.2.2
      simp [g, this]
    simp [this]

/-- Change of variables: the Lebesgue measure of the image of the parameter region. -/
lemma ste_volume_image {A' : Set (Fin d → ℝ)} (hA' : MeasurableSet A') :
    volume (steG '' steB A') =
      ∫⁻ z in steB A', ENNReal.ofReal ((2 * z (Fin.last d)) ^ d * (1 + steQ z)) := by
  have hB := steB_measurable hA'
  have hpos : ∀ z ∈ steB A', 0 < z (Fin.last d) := fun z hz => hz.1
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure (Fin (d + 1) → ℝ)) hB
    (f' := fun z => (steCLM (steMH (stePmap z))).comp (steCLM (steMP z)))
    (fun z hz => (ste_hasFDerivAt_G (hpos z hz)).hasFDerivWithinAt)
    (steG_injOn.mono fun z hz => hpos z hz)]
  refine setLIntegral_congr_fun hB fun z hz => ?_
  rw [ste_abs_det_G (hpos z hz)]

/-- The cone `(0,1) · (S ∩ S^d)`. -/
def steCone (S : Set (EuclideanSpace ℝ (Fin (d + 1)))) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 →
    EuclideanSpace ℝ (Fin (d + 1))) '' (Subtype.val ⁻¹' S))

/-- The cone over `S ∩ S^d` contains the image of the parameter region. -/
lemma ste_image_subset_cone {S : Set (EuclideanSpace ℝ (Fin (d + 1)))} :
    steG '' steB {y : Fin d → ℝ | stereoInv (WithLp.toLp 2 y) ∈ S} ⊆
      (fun w : Fin (d + 1) → ℝ => (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin (d + 1)))) ⁻¹'
        steCone S := by
  rintro _ ⟨z, ⟨hz0, hz1, hzA⟩, rfl⟩
  have hq : 0 < 1 + ‖steX z‖ ^ 2 := by positivity
  have hQ : ‖steX z‖ ^ 2 = steQ z := steX_norm_sq z
  have hmem : stereoInv (steX z) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 := by
    simp [ste_norm_stereoInv]
  refine Set.mem_smul.2 ⟨z (Fin.last d) * (1 + ‖steX z‖ ^ 2), ⟨by positivity, ?_⟩,
    stereoInv (steX z), ⟨⟨stereoInv (steX z), hmem⟩, hzA, rfl⟩, ?_⟩
  · rw [hQ]; exact hz1
  · exact (ste_toLp_G hz0).symm

lemma ste_continuous_stereoInv : Continuous (stereoInv : Euc d → EuclideanSpace ℝ (Fin (d + 1))) := by
  unfold stereoInv
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact (((continuous_norm.pow 2).sub continuous_const).div
      (continuous_const.add (continuous_norm.pow 2)) fun x => by positivity)
  · simp only [Fin.snoc_castSucc]
    exact ((continuous_const.mul ((EuclideanSpace.proj j).continuous)).div
      (continuous_const.add (continuous_norm.pow 2)) fun x => by positivity)

/-- Conjunct (1) of `logThermal_stereographic`. -/
lemma ste_pushforward (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ C : ℝ≥0, (thermalMeasure d 0 a β).map stereoInv ≤ C • sphereSurface d := by
  obtain ⟨A0, hA0, hρ⟩ := ste_pointwise_bound hd ha hβ
  refine ⟨Real.toNNReal (A0 / 2 ^ d), ?_⟩
  rw [Measure.le_iff]
  intro S hS
  have hmeas := ste_continuous_stereoInv (d := d)
  have hA : MeasurableSet (stereoInv ⁻¹' S : Set (Euc d)) := hmeas.measurable hS
  set A : Set (Euc d) := stereoInv ⁻¹' S with hAdef
  have hmpt := PiLp.volume_preserving_toLp (Fin d)
  have hembt := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
  set A' : Set (Fin d → ℝ) := {y | stereoInv (WithLp.toLp 2 y) ∈ S} with hA'def
  have hA'eq : A' = (WithLp.toLp 2 : (Fin d → ℝ) → Euc d) ⁻¹' A := rfl
  have hA' : MeasurableSet A' := by
    rw [hA'eq]; exact hmpt.measurable hA
  -- the surface measure of `S`
  have hσ : sphereSurface d S = (d + 1 : ℝ≥0∞) * volume (steCone S) := by
    unfold sphereSurface
    rw [Measure.map_apply measurable_subtype_coe hS,
      Measure.toSphere_apply' _ (measurable_subtype_coe hS)]
    simp [steCone]
  -- lower bound for the cone volume
  have hcone : volume (steG '' steB A') ≤ volume (steCone S) := by
    calc volume (steG '' steB A') ≤ volume ((WithLp.toLp 2 : (Fin (d + 1) → ℝ) →
          EuclideanSpace ℝ (Fin (d + 1))) ⁻¹' steCone S) := measure_mono ste_image_subset_cone
      _ = volume (steCone S) := (PiLp.volume_preserving_toLp (Fin (d + 1))).measure_preimage_emb
          (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).measurableEmbedding _
  -- the image volume as an integral over `A`
  have hvol : volume (steG '' steB A') =
      ∫⁻ x in A, ENNReal.ofReal ((2 / (1 + ‖x‖ ^ 2)) ^ d / (d + 1)) := by
    rw [ste_volume_image hA', ste_lintegral_B hA']
    have := hmpt.setLIntegral_comp_preimage_emb hembt
      (fun x : Euc d => ENNReal.ofReal ((2 / (1 + ‖x‖ ^ 2)) ^ d / (d + 1))) A
    rw [← this]
    refine setLIntegral_congr_fun hA' fun y _ => ?_
    have : ‖(WithLp.toLp 2 y : Euc d)‖ ^ 2 = steQ' y := by
      rw [EuclideanSpace.norm_sq_eq]; simp [steQ']
    rw [this]
  -- the density bound
  have hbd : ∀ x : Euc d, ENNReal.ofReal (thermalDensity d 0 a β x) ≤
      ENNReal.ofReal (A0 / 2 ^ d) * ((d + 1 : ℝ≥0∞) *
        ENNReal.ofReal ((2 / (1 + ‖x‖ ^ 2)) ^ d / (d + 1))) := by
    intro x
    have hpos : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
    have h1 := hρ x
    have h2 : A0 * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ)) = A0 / 2 ^ d * (2 / (1 + ‖x‖ ^ 2)) ^ d := by
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast, div_pow]
      field_simp
    have h3 : (d + 1 : ℝ≥0∞) = ENNReal.ofReal ((d : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; simp
    rw [h3, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [h2] at h1
    refine h1.trans (le_of_eq ?_)
    field_simp
  calc (thermalMeasure d 0 a β).map stereoInv S = ∫⁻ x in A, ENNReal.ofReal (thermalDensity d 0 a β x) := by
        rw [Measure.map_apply hmeas.measurable hS]
        exact withDensity_apply _ hA
    _ ≤ ∫⁻ x in A, ENNReal.ofReal (A0 / 2 ^ d) * ((d + 1 : ℝ≥0∞) *
        ENNReal.ofReal ((2 / (1 + ‖x‖ ^ 2)) ^ d / (d + 1))) := lintegral_mono hbd
    _ = ENNReal.ofReal (A0 / 2 ^ d) * ((d + 1 : ℝ≥0∞) *
        ∫⁻ x in A, ENNReal.ofReal ((2 / (1 + ‖x‖ ^ 2)) ^ d / (d + 1))) := by
        have hm : Measurable fun x : Euc d => ENNReal.ofReal ((2 / (1 + ‖x‖ ^ 2)) ^ d / (d + 1)) := by
          refine ENNReal.measurable_ofReal.comp ?_
          fun_prop
        rw [lintegral_const_mul _ (hm.const_mul _), lintegral_const_mul _ hm]
    _ ≤ ENNReal.ofReal (A0 / 2 ^ d) * ((d + 1 : ℝ≥0∞) * volume (steCone S)) := by
        rw [← hvol]; gcongr
    _ = _ := by
        rw [Measure.smul_apply, hσ, ENNReal.smul_def, smul_eq_mul]
        rfl

/-- **C-STE.**  The stereographic pushforward bound and the spherical density bound. -/
theorem logThermal_stereographic_proof : type_of% @HRS.Whole.logThermal_stereographic := by
  intro d hd a β ha hβ
  exact ⟨ste_pushforward hd ha hβ, ste_hasSphericalBound hd ha hβ⟩

end HRS.MS.Thm

end
