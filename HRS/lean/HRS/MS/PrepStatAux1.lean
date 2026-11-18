import HRS.MS.PrepBnd

/-!
# HRS.MS.PrepStatAux1 -- reweighting of a realization by a function of the initial datum (S3.2, part 1)

Packet S32 (`euclidean_preparations_stationary`), namespace `HRS.MS.PrepStat`.  Generic probability
infrastructure, no Euclidean content.

Let `P` be a probability measure, `X0 : Ω → α` measurable, `k : α → ℝ≥0∞` measurable with
`∫ k d(P.map X0) = 1` and `P' = P.withDensity (k ∘ X0)`.

* `s32_wd_inter`: `P'(X0⁻¹A ∩ Y⁻¹B) = P(Y⁻¹B) ∫_A k d(P.map X0)` whenever `X0 ⟂ Y` under `P`
  (`Y` is an arbitrary map: no measurability of `Y` is used, the sets `Y⁻¹B` need not be measurable).
* `s32_wd_preimage`, `s32_wd_indep`, `s32_wd_map_eq`: `P'` and `P` agree on `σ(Y)`, `X0 ⟂ Y` under `P'`,
  `P'.map Y = P.map Y`.
* `s32_isVectorBrownian_wd`: a vector Brownian motion independent of `X0` stays a vector Brownian
  motion under `P'`.

Helper lemmas carry the prefix `s32_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MS.PrepStat

section Reweight

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

theorem s32_wd_inter (P : Measure Ω) [IsProbabilityMeasure P] {X0 : Ω → α} (hX0 : Measurable X0)
    {k : α → ℝ≥0∞} (hk : Measurable k) {β : Type*} [MeasurableSpace β] {Y : Ω → β}
    (hind : IndepFun X0 Y P) {A0 : Set α} {B : Set β} (hA : MeasurableSet A0)
    (hB : MeasurableSet B) :
    (P.withDensity (fun ζ => k (X0 ζ))) (X0 ⁻¹' A0 ∩ Y ⁻¹' B) =
      P (Y ⁻¹' B) * ∫⁻ x in A0, k x ∂(P.map X0) := by
  have hmap : (P.restrict (Y ⁻¹' B)).map X0 = P (Y ⁻¹' B) • P.map X0 := by
    refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply hX0 hS, Measure.restrict_apply (hX0 hS), Measure.smul_apply,
      Measure.map_apply hX0 hS, smul_eq_mul,
      (indepFun_iff_measure_inter_preimage_eq_mul.1 hind) S B hS hB, mul_comm]
  rw [withDensity_apply' _ _, ← Measure.restrict_restrict (hX0 hA),
    ← setLIntegral_map hA hk hX0, hmap, Measure.restrict_smul, lintegral_smul_measure,
    smul_eq_mul]

theorem s32_wd_mapX0 (P : Measure Ω) [IsProbabilityMeasure P] {X0 : Ω → α} (hX0 : Measurable X0)
    {k : α → ℝ≥0∞} (hk : Measurable k) :
    (P.withDensity (fun ζ => k (X0 ζ))).map X0 = (P.map X0).withDensity k := by
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hX0 hS, withDensity_apply _ (hX0 hS), withDensity_apply _ hS,
    setLIntegral_map hS hk hX0]

theorem s32_wd_univ (P : Measure Ω) [IsProbabilityMeasure P] {X0 : Ω → α} (hX0 : Measurable X0)
    {k : α → ℝ≥0∞} (hk : Measurable k) :
    (P.withDensity (fun ζ => k (X0 ζ))) Set.univ = ∫⁻ x, k x ∂(P.map X0) := by
  have := s32_wd_mapX0 P hX0 hk
  have h2 := congrArg (fun m => m Set.univ) this
  simp only [Measure.map_apply hX0 MeasurableSet.univ, Set.preimage_univ] at h2
  rw [h2, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

theorem s32_wd_preimage (P : Measure Ω) [IsProbabilityMeasure P] {X0 : Ω → α} (hX0 : Measurable X0)
    {k : α → ℝ≥0∞} (hk : Measurable k) (hk1 : ∫⁻ x, k x ∂(P.map X0) = 1)
    {β : Type*} [MeasurableSpace β] {Y : Ω → β} (hind : IndepFun X0 Y P) {B : Set β}
    (hB : MeasurableSet B) :
    (P.withDensity (fun ζ => k (X0 ζ))) (Y ⁻¹' B) = P (Y ⁻¹' B) := by
  have := s32_wd_inter P hX0 hk hind MeasurableSet.univ hB
  rw [Set.preimage_univ, Set.univ_inter, Measure.restrict_univ, hk1, mul_one] at this
  exact this

theorem s32_wd_indep (P : Measure Ω) [IsProbabilityMeasure P] {X0 : Ω → α} (hX0 : Measurable X0)
    {k : α → ℝ≥0∞} (hk : Measurable k) (hk1 : ∫⁻ x, k x ∂(P.map X0) = 1)
    {β : Type*} [MeasurableSpace β] {Y : Ω → β} (hind : IndepFun X0 Y P) :
    IndepFun X0 Y (P.withDensity (fun ζ => k (X0 ζ))) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro S B hS hB
  rw [s32_wd_inter P hX0 hk hind hS hB, s32_wd_preimage P hX0 hk hk1 hind hB]
  have := congrArg (fun m => m S) (s32_wd_mapX0 P hX0 hk)
  simp only [Measure.map_apply hX0 hS, withDensity_apply _ hS] at this
  rw [← this, mul_comm]

theorem s32_wd_map_eq (P : Measure Ω) [IsProbabilityMeasure P] {X0 : Ω → α} (hX0 : Measurable X0)
    {k : α → ℝ≥0∞} (hk : Measurable k) (hk1 : ∫⁻ x, k x ∂(P.map X0) = 1)
    {β : Type*} [MeasurableSpace β] {Y : Ω → β} (hY : AEMeasurable Y P) (hind : IndepFun X0 Y P) :
    (P.withDensity (fun ζ => k (X0 ζ))).map Y = P.map Y := by
  have hac : P.withDensity (fun ζ => k (X0 ζ)) ≪ P := withDensity_absolutelyContinuous _ _
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply_of_aemeasurable (hY.mono_ac hac) hB, Measure.map_apply_of_aemeasurable hY hB]
  exact s32_wd_preimage P hX0 hk hk1 hind hB

/-- A vector Brownian motion independent of `X0` stays a vector Brownian motion under the
reweighted measure `P' = (k ∘ X0) P`. -/
theorem s32_isVectorBrownian_wd (P : Measure Ω) [IsProbabilityMeasure P] {X0 : Ω → α}
    (hX0 : Measurable X0) {k : α → ℝ≥0∞} (hk : Measurable k) (hk1 : ∫⁻ x, k x ∂(P.map X0) = 1)
    {d N : ℕ} {W : ℝ≥0 → Ω → (Fin N → HRS.Euc d)} (hW : HRS.IsVectorBrownian P W)
    (hind : IndepFun X0 (fun ζ t => W t ζ) P) :
    HRS.IsVectorBrownian (P.withDensity (fun ζ => k (X0 ζ))) W := by
  have hac : P.withDensity (fun ζ => k (X0 ζ)) ≪ P := withDensity_absolutelyContinuous _ _
  have hcoord : ∀ (i : Fin N) (j : Fin d), Measurable (fun x : HRS.Euc d => x j) := fun i j =>
    (EuclideanSpace.proj j).continuous.measurable
  refine ⟨fun i j => ?_, ?_⟩
  · refine ⟨⟨fun I => ?_⟩, hac.ae_le (hW.1 i j).cont⟩
    have hL := (hW.1 i j).hasLaw I
    have hψ : Measurable (fun w : ℝ≥0 → Fin N → HRS.Euc d => I.restrict (fun t => w t i j)) :=
      Measurable.of_eval fun t =>
        (hcoord i j).comp ((measurable_pi_apply i).comp (measurable_pi_apply (t : ℝ≥0)))
    have hY : IndepFun X0 (fun ζ => I.restrict (fun t => W t ζ i j)) P :=
      hind.comp measurable_id hψ
    exact ⟨hL.aemeasurable.mono_ac hac,
      (s32_wd_map_eq P hX0 hk hk1 hL.aemeasurable hY).trans hL.map_eq⟩
  · rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    let Wfam : Ω → (Fin N × Fin d → ℝ≥0 → ℝ) := fun ζ ij t => W t ζ ij.1 ij.2
    have hΦ : Measurable (fun w : ℝ≥0 → Fin N → HRS.Euc d =>
        (fun (ij : Fin N × Fin d) (t : ℝ≥0) => w t ij.1 ij.2 : Fin N × Fin d → ℝ≥0 → ℝ)) :=
      Measurable.of_eval fun ij => Measurable.of_eval fun t =>
        (hcoord ij.1 ij.2).comp ((measurable_pi_apply ij.1).comp (measurable_pi_apply t))
    have hindF : IndepFun X0 Wfam P := hind.comp measurable_id hΦ
    have hev : ∀ i : Fin N × Fin d, Measurable (fun g : Fin N × Fin d → ℝ≥0 → ℝ => g i) :=
      fun i => measurable_pi_apply i
    have key : ∀ T : Set (Fin N × Fin d → ℝ≥0 → ℝ), MeasurableSet T →
        (P.withDensity (fun ζ => k (X0 ζ))) (Wfam ⁻¹' T) = P (Wfam ⁻¹' T) :=
      fun T hT => s32_wd_preimage P hX0 hk hk1 hindF hT
    have e1 : (⋂ i ∈ S, (fun ζ t => W t ζ i.1 i.2) ⁻¹' sets i) =
        Wfam ⁻¹' (⋂ i ∈ S, (fun g : Fin N × Fin d → ℝ≥0 → ℝ => g i) ⁻¹' sets i) := by
      ext ζ; simp [Wfam]
    have hm1 : MeasurableSet (⋂ i ∈ S, (fun g : Fin N × Fin d → ℝ≥0 → ℝ => g i) ⁻¹' sets i) :=
      Finset.measurableSet_biInter S fun i hi => hev i (hsets i hi)
    rw [e1, key _ hm1]
    have := hW.2.measure_inter_preimage_eq_mul S hsets
    rw [e1] at this
    rw [this]
    refine Finset.prod_congr rfl fun i hi => ?_
    exact (key _ (hev i (hsets i hi))).symm

end Reweight

section KL

open InformationTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

theorem s32_llr_wd {γ : Type*} [MeasurableSpace γ] {P Q : Measure γ} [SigmaFinite Q] {r : γ → ℝ}
    (hr : Measurable r) (hpos : ∀ x, 0 < r x)
    (hPQ : P = Q.withDensity (fun x => ENNReal.ofReal (r x))) :
    P ≪ Q ∧ llr P Q =ᵐ[P] fun x => Real.log (r x) := by
  have hac : P ≪ Q := by rw [hPQ]; exact withDensity_absolutelyContinuous _ _
  refine ⟨hac, ?_⟩
  have hrn : P.rnDeriv Q =ᵐ[Q] fun x => ENNReal.ofReal (r x) := by
    conv_lhs => rw [hPQ]
    exact Measure.rnDeriv_withDensity Q (ENNReal.measurable_ofReal.comp hr)
  filter_upwards [hac.ae_le hrn] with x hx
  unfold llr
  rw [hx, ENNReal.toReal_ofReal (hpos x).le]

/-- The density `k = r⁻¹` is the inverse density: `Q = (P.map X0).withDensity k`. -/
theorem s32_inv_density {γ : Type*} [MeasurableSpace γ] {f0 Q : Measure γ} {r : γ → ℝ}
    (hr : Measurable r) (hpos : ∀ x, 0 < r x)
    (hf0 : f0 = Q.withDensity (fun x => ENNReal.ofReal (r x))) :
    Q = f0.withDensity (fun x => ENNReal.ofReal (r x)⁻¹) := by
  have hm1 : Measurable (fun x => ENNReal.ofReal (r x)) := ENNReal.measurable_ofReal.comp hr
  have hm2 : Measurable (fun x => ENNReal.ofReal (r x)⁻¹) :=
    ENNReal.measurable_ofReal.comp hr.inv
  rw [hf0, ← withDensity_mul _ hm1 hm2]
  have : ((fun x => ENNReal.ofReal (r x)) * (fun x => ENNReal.ofReal (r x)⁻¹)) = 1 := by
    funext x
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [← ENNReal.ofReal_mul (hpos x).le, mul_inv_cancel₀ (hpos x).ne', ENNReal.ofReal_one]
  rw [this, withDensity_one]

theorem s32_pullback_one (P : Measure Ω) [IsProbabilityMeasure P] {X0 : Ω → α} (hX0 : Measurable X0)
    {Q : Measure α} [IsProbabilityMeasure Q] {r : α → ℝ} (hr : Measurable r) (hpos : ∀ x, 0 < r x)
    (hf0 : P.map X0 = Q.withDensity (fun x => ENNReal.ofReal (r x))) :
    ∫⁻ x, ENNReal.ofReal (r x)⁻¹ ∂(P.map X0) = 1 := by
  have hQ := s32_inv_density hr hpos hf0
  have := congrArg (fun m => m Set.univ) hQ
  simp only [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  exact this.symm

theorem s32_pullback_prob (P : Measure Ω) [IsProbabilityMeasure P] {X0 : Ω → α} (hX0 : Measurable X0)
    {Q : Measure α} [IsProbabilityMeasure Q] {r : α → ℝ} (hr : Measurable r) (hpos : ∀ x, 0 < r x)
    (hf0 : P.map X0 = Q.withDensity (fun x => ENNReal.ofReal (r x))) :
    IsProbabilityMeasure (P.withDensity (fun ζ => ENNReal.ofReal (r (X0 ζ))⁻¹)) := by
  constructor
  rw [s32_wd_univ P hX0 (k := fun x => ENNReal.ofReal (r x)⁻¹) (ENNReal.measurable_ofReal.comp hr.inv)]
  exact s32_pullback_one P hX0 hr hpos hf0

theorem s32_pullback_map (P : Measure Ω) [IsProbabilityMeasure P] {X0 : Ω → α} (hX0 : Measurable X0)
    {Q : Measure α} [IsProbabilityMeasure Q] {r : α → ℝ} (hr : Measurable r) (hpos : ∀ x, 0 < r x)
    (hf0 : P.map X0 = Q.withDensity (fun x => ENNReal.ofReal (r x))) :
    (P.withDensity (fun ζ => ENNReal.ofReal (r (X0 ζ))⁻¹)).map X0 = Q := by
  rw [s32_wd_mapX0 P hX0 (k := fun x => ENNReal.ofReal (r x)⁻¹) (ENNReal.measurable_ofReal.comp hr.inv)]
  exact (s32_inv_density hr hpos hf0).symm

/-- **Entropy of the reweighted realization** `H(P | P') = H(law X0 | Q)`. -/
theorem s32_kl_pullback (P : Measure Ω) [IsProbabilityMeasure P] {X0 : Ω → α} (hX0 : Measurable X0)
    {Q : Measure α} [IsProbabilityMeasure Q] {r : α → ℝ} (hr : Measurable r) (hpos : ∀ x, 0 < r x)
    (hf0 : P.map X0 = Q.withDensity (fun x => ENNReal.ofReal (r x)))
    (hKL : klDiv (P.map X0) Q ≠ ∞) :
    klDiv P (P.withDensity (fun ζ => ENNReal.ofReal (r (X0 ζ))⁻¹)) = klDiv (P.map X0) Q := by
  have := s32_pullback_prob P hX0 hr hpos hf0
  set P' := P.withDensity (fun ζ => ENNReal.ofReal (r (X0 ζ))⁻¹) with hP'
  have hrX : Measurable (fun ζ => r (X0 ζ)) := hr.comp hX0
  have hm1 : Measurable (fun ζ => ENNReal.ofReal (r (X0 ζ))⁻¹) :=
    ENNReal.measurable_ofReal.comp hrX.inv
  have hm2 : Measurable (fun ζ => ENNReal.ofReal (r (X0 ζ))) := ENNReal.measurable_ofReal.comp hrX
  have hPP' : P = P'.withDensity (fun ζ => ENNReal.ofReal (r (X0 ζ))) := by
    rw [hP', ← withDensity_mul _ hm1 hm2]
    have : ((fun ζ => ENNReal.ofReal (r (X0 ζ))⁻¹) * (fun ζ => ENNReal.ofReal (r (X0 ζ)))) =
        1 := by
      funext ζ
      simp only [Pi.mul_apply, Pi.one_apply]
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 (hpos _).le), inv_mul_cancel₀ (hpos _).ne',
        ENNReal.ofReal_one]
    rw [this, withDensity_one]
  obtain ⟨hac, hllr⟩ := s32_llr_wd hrX (fun ζ => hpos _) hPP'
  obtain ⟨hac0, hllr0⟩ := s32_llr_wd hr hpos hf0
  have hint0 : Integrable (llr (P.map X0) Q) (P.map X0) := (klDiv_ne_top_iff.1 hKL).2
  have hlog0 : Integrable (fun x => Real.log (r x)) (P.map X0) := hint0.congr hllr0
  have hlogP : Integrable (fun ζ => Real.log (r (X0 ζ))) P :=
    (integrable_map_measure hlog0.aestronglyMeasurable hX0.aemeasurable).1 hlog0
  have hintP : Integrable (llr P P') P := hlogP.congr hllr.symm
  rw [klDiv_of_ac_of_integrable hac hintP, klDiv_of_ac_of_integrable hac0 hint0]
  congr 1
  have h1 : ∫ ζ, llr P P' ζ ∂P = ∫ x, llr (P.map X0) Q x ∂(P.map X0) := by
    rw [integral_congr_ae hllr, integral_congr_ae hllr0, integral_map hX0.aemeasurable
      (hr.log).aestronglyMeasurable]
  rw [h1]
  simp [measureReal_def]

/-- **Change of reference measure.**  If `Q = R.withDensity φ` (`φ > 0` measurable), `f ≪ Q` with
`H(f | Q) < ∞` and `log φ` is `f`-integrable, then `H(f | R) < ∞` and
`H(f | R) = H(f | Q) + ∫ log φ df` (as real numbers). -/
theorem s32_kl_refchange {γ : Type*} [MeasurableSpace γ] (f Q R : Measure γ)
    [IsProbabilityMeasure f] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] {φ : γ → ℝ}
    (hφ : Measurable φ) (hpos : ∀ x, 0 < φ x)
    (hQR : Q = R.withDensity (fun x => ENNReal.ofReal (φ x)))
    (hKL : klDiv f Q ≠ ∞) (hint : Integrable (fun x => Real.log (φ x)) f) :
    klDiv f R ≠ ∞ ∧ (klDiv f R).toReal = (klDiv f Q).toReal + ∫ x, Real.log (φ x) ∂f := by
  obtain ⟨hfQ, hint0⟩ := klDiv_ne_top_iff.1 hKL
  obtain ⟨hQR', hllrQ⟩ := s32_llr_wd hφ hpos hQR
  have hfR : f ≪ R := hfQ.trans hQR'
  have hrn : Q.rnDeriv R =ᵐ[R] fun x => ENNReal.ofReal (φ x) := by
    conv_lhs => rw [hQR]
    exact Measure.rnDeriv_withDensity R (ENNReal.measurable_ofReal.comp hφ)
  have hmul := Measure.rnDeriv_mul_rnDeriv (κ := R) hfQ
  have hpos' : ∀ᵐ x ∂f, 0 < f.rnDeriv Q x := Measure.rnDeriv_pos hfQ
  have hlt : ∀ᵐ x ∂f, f.rnDeriv Q x < ∞ := hfQ.ae_le (Measure.rnDeriv_lt_top f Q)
  have hllr : llr f R =ᵐ[f] fun x => llr f Q x + Real.log (φ x) := by
    filter_upwards [hfR.ae_le hmul, hfR.ae_le hrn, hpos', hlt] with x h1 h2 h3 h4
    unfold llr
    rw [← h1, Pi.mul_apply, h2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hpos x).le]
    have h5 : 0 < (f.rnDeriv Q x).toReal := ENNReal.toReal_pos h3.ne' h4.ne
    rw [Real.log_mul h5.ne' (hpos x).ne']
  have hint1 : Integrable (llr f R) f := (hint0.add hint).congr hllr.symm
  have hne : klDiv f R ≠ ∞ := klDiv_ne_top hfR hint1
  refine ⟨hne, ?_⟩
  rw [toReal_klDiv hfR hint1, toReal_klDiv hfQ hint0, integral_congr_ae hllr, integral_add hint0 hint]
  simp [measureReal_def]

end KL

end HRS.MS.PrepStat
