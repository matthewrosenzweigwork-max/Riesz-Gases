import HRS.MC.E213U7b
import HRS.MC.E213U3G
import HRS.MC.E213U6

/-!
# Packet e213u12 (part a): deterministic far-window bounds for the Riemann--Stieltjes integrals

* congruence of `winDrift`, `winJ`, `rsA`, `rsJ` in the coefficient (only the values on the integration range matter);
* the abstract far bound `u12_rs_bound_abstract` (comparison of an RS integral with `0` by a weighted finite measure);
* `u12_drift_far_bound`, `u12_J_far_bound`: for an `L¹` (resp. bounded) coefficient `bq` the far part of the RS integral is
  bounded by `C ∫_{(0,a+T] ∩ (-∞,b)} e^{-c(a-v)} ‖bq v‖ dv` (from `winDrift_far`, `winJ_far`, `rs_split_*`).
Namespace `HRS.MC.E213U12`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U12

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

/-! ### Congruence in the coefficient -/

theorem u12_driftInc_congr (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (b b' : ℝ → NegSobolev d m) (u u' : ℝ)
    (h : ∀ v ∈ Set.Ioc u u', b v = b' v) : driftInc D ρ m T b u u' = driftInc D ρ m T b' u u' := by
  unfold driftInc
  congr 1
  funext t
  refine setIntegral_congr_fun measurableSet_Ioc (fun v hv => ?_)
  show Vprop D ρ m t v (b v) = Vprop D ρ m t v (b' v)
  rw [h v ⟨hv.1, hv.2.trans (min_le_left _ _)⟩]

theorem u12_isJValue_congr (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (z z' : ℝ → NegSobolev d m) (I : Set ℝ)
    (hI : MeasurableSet I) (h : ∀ v ∈ I, z v = z' v) : IsJValue D ρ m T z I = IsJValue D ρ m T z' I := by
  funext J
  apply propext
  unfold IsJValue
  have key : ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ),
      ∫ u in I ∩ Set.Icc (0 : ℝ) (min ta tb), NegSobolev.eval (z u)
        (fun x => inner ℝ (Torus.grad (propagator D ρ u ta φa) x) (Torus.grad (propagator D ρ u tb φb) x)) =
      ∫ u in I ∩ Set.Icc (0 : ℝ) (min ta tb), NegSobolev.eval (z' u)
        (fun x => inner ℝ (Torus.grad (propagator D ρ u ta φa) x) (Torus.grad (propagator D ρ u tb φb) x)) := by
    intro ta tb φa φb
    refine setIntegral_congr_fun (hI.inter measurableSet_Icc) (fun v hv => ?_)
    show NegSobolev.eval (z v) _ = NegSobolev.eval (z' v) _
    rw [h v hv.1]
  simp only [key]

theorem u12_jTensor_congr (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (z z' : ℝ → NegSobolev d m) (I : Set ℝ)
    (hI : MeasurableSet I) (h : ∀ v ∈ I, z v = z' v) : jTensor D ρ m T z I = jTensor D ρ m T z' I := by
  unfold jTensor
  rw [u12_isJValue_congr D ρ m T z z' I hI h]

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u12_winDrift_congr (hE : EdgeworthHyp S β₀ m) (T a : ℝ) (ha : 0 ≤ a) (b b' : ℝ → NegSobolev d m) (u u' : ℝ)
    (h : ∀ v ∈ Set.Ioc u u', b v = b' v) :
    winDrift (regime S β₀ hE) m T a ha b u u' = winDrift (regime S β₀ hE) m T a ha b' u u' := by
  unfold winDrift
  rw [u12_driftInc_congr _ _ _ _ b b' u u' h]

theorem u12_winJ_congr (hE : EdgeworthHyp S β₀ m) (T a : ℝ) (ha : 0 ≤ a) (z z' : ℝ → NegSobolev d m) (I : Set ℝ)
    (hI : MeasurableSet I) (h : ∀ v ∈ I, z v = z' v) :
    winJ (regime S β₀ hE) m T a ha z I = winJ (regime S β₀ hE) m T a ha z' I := by
  unfold winJ
  rw [u12_jTensor_congr _ _ _ _ z z' I hI h]

theorem u12_rsLim_congr {T : ℝ} (hT : 0 < T) {S S' : ℝ → ℝ → ℝ → ℝ}
    (hSS : ∀ τ u u' : ℝ, 0 ≤ u → u ≤ τ → τ ≤ u' → u' ≤ T → S τ u u' = S' τ u u') : rsLim T S = rsLim T S' := by
  classical
  by_cases hex : ∃ I, IsRS T S I
  · obtain ⟨I, hI⟩ := hex
    have hI' := HRS.MC.E213U7.e213u7_isRS_congr hI hSS
    rw [HRS.MC.E213U7.e213u7_rsLim_eq hT hI, HRS.MC.E213U7.e213u7_rsLim_eq hT hI']
  · have hex' : ¬ ∃ I, IsRS T S' I := by
      rintro ⟨I, hI⟩
      exact hex ⟨I, HRS.MC.E213U7.e213u7_isRS_congr hI (fun τ u u' h1 h2 h3 h4 => (hSS τ u u' h1 h2 h3 h4).symm)⟩
    unfold rsLim
    rw [dif_neg hex, dif_neg hex']

theorem u12_rsA_congr (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (U : ℝ → PathSpace d m T → ℝ) (w : PathSpace d m (a + T)) (bq bq' : ℝ → NegSobolev d m)
    (h : ∀ v ∈ Set.Ioc 0 (a + T), bq v = bq' v) :
    rsA (regime S β₀ hE) m T a ha U w bq = rsA (regime S β₀ hE) m T a ha U w bq' := by
  unfold rsA
  refine u12_rsLim_congr (by linarith) (fun τ u u' hu hτ hτ' hu' => ?_)
  unfold rsSumD
  beta_reduce
  rw [u12_winDrift_congr hE T a ha bq bq' u u' (fun v hv => h v ⟨lt_of_le_of_lt hu hv.1, hv.2.trans hu'⟩)]

theorem u12_rsJ_congr (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (U : ℝ → PathSpace d m T → ℝ) (w : PathSpace d m (a + T)) (zq zq' : ℝ → NegSobolev d m)
    (h : ∀ v ∈ Set.Ioc 0 (a + T), zq v = zq' v) :
    rsJ (regime S β₀ hE) m T a ha U w zq = rsJ (regime S β₀ hE) m T a ha U w zq' := by
  unfold rsJ
  refine u12_rsLim_congr (by linarith) (fun τ u u' hu hτ hτ' hu' => ?_)
  unfold rsSumJ
  beta_reduce
  rw [u12_winJ_congr hE T a ha zq zq' (Set.Ioc u u') measurableSet_Ioc
    (fun v hv => h v ⟨lt_of_le_of_lt hu hv.1, hv.2.trans hu'⟩)]

/-! ### The abstract far bound -/

theorem u12_rs_bound_abstract {T : ℝ} (hT : 0 < T) {S : ℝ → ℝ → ℝ → ℝ} {I : ℝ} (hS : IsRS T S I)
    (f : ℝ → ℝ) (hf0 : ∀ v, 0 ≤ f v) (s : Set ℝ) (hs : MeasurableSet s) (hsub : s ⊆ Set.Ioc 0 T)
    (hfi : IntegrableOn f s) (κ : ℝ)
    (h : ∀ τ u u' : ℝ, 0 ≤ u → u ≤ τ → τ ≤ u' → u' ≤ T →
      |S τ u u'| ≤ κ * ∫ v in Set.Ioc u u' ∩ s, f v) :
    |I| ≤ κ * ∫ v in s, f v := by
  have hzero : IsRS T (fun _ _ _ => (0 : ℝ)) 0 := fun ε hε => ⟨1, one_pos, fun n u τ _ _ _ _ _ => by simpa using hε⟩
  let ν : Measure ℝ := (volume.restrict s).withDensity (fun v => ENNReal.ofReal (f v))
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hfi.2
  have hν : ∀ A : Set ℝ, MeasurableSet A → (ν A).toReal = ∫ v in A ∩ s, f v := by
    intro A hA
    simp only [ν]
    rw [withDensity_apply _ hA, Measure.restrict_restrict hA]
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
      (hfi.aestronglyMeasurable.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))]
  have key := HRS.MC.E213U1.isRS_sub_le_proof hT hS hzero ν κ (fun τ u u' hu h1 h2 h3 => by
    rw [sub_zero, hν _ measurableSet_Ioc]
    exact h τ u u' hu h1 h2 h3)
  rw [sub_zero, hν _ measurableSet_Ioc, Set.inter_eq_right.2 hsub] at key
  exact key

/-- The factor `e^{-c(a-v)} ≤ 1` for `v ≤ a`. -/
theorem u12_exp_le_one {c a v : ℝ} (hc : 0 < c) (hv : v ≤ a) : Real.exp (-c * (a - v)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  nlinarith

theorem u12_fderiv_norm_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : X → ℝ) (x : X) :
    ‖fderiv ℝ f x‖ = ‖iteratedFDeriv ℝ 1 f x‖ := by
  rw [← HRS.MC.E213U7.e213u7_curry_iter f x]
  exact (continuousMultilinearCurryFin1 ℝ X ℝ).norm_map _

/-- Integrability of the weighted norm on the far set from the integrability of the norm. -/
theorem u12_weighted_integrableOn {c a b H : ℝ} (hc : 0 < c) (hba : b ≤ a) {bq : ℝ → NegSobolev d (rLvl d)}
    (hbm : Measurable (nearCoef 0 bq)) (hbi : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 H)) {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Set.Ioc 0 H) (hsb : s ⊆ Set.Iic b) :
    IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖bq v‖) s := by
  have hs' : s ⊆ Set.Icc 0 H := fun v hv => ⟨(hsub hv).1.le, (hsub hv).2⟩
  have hae : AEStronglyMeasurable bq (volume.restrict s) :=
    HRS.MC.E213U1.u1_aesm_of_nearCoef hbm hs (fun v hv => Set.mem_Ici.2 (hsub hv).1.le)
  have hexp : AEStronglyMeasurable (fun v : ℝ => Real.exp (-c * (a - v))) (volume.restrict s) :=
    (by fun_prop : Continuous fun v : ℝ => Real.exp (-c * (a - v))).aestronglyMeasurable
  refine Integrable.mono' (hbi.mono_set hs') (hexp.mul hae.norm) (ae_restrict_of_forall_mem hs fun v hv => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (norm_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (u12_exp_le_one hc ((hsb hv).trans hba))

/-! ### The drift far bound -/

theorem u12_drift_far_bound (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ), Φ ∈ CbUnitBall (PathSpace d m T) 5 →
      ∀ (w : PathSpace d m (a + T)) (bq : ℝ → NegSobolev d (rLvl d)), Measurable (nearCoef 0 bq) →
      IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + T)) →
      ∀ (z : ℝ → NegSobolev d m), (∀ v ∈ Set.Ioc 0 (a + T), z v = NegSobolev.embed m (bq v)) →
      ∀ (b : ℝ), 0 ≤ b → b ≤ a →
        |rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b z)| ≤
          C * ∫ v in Set.Ioc 0 (a + T) ∩ Set.Iio b, Real.exp (-c * (a - v)) * ‖bq v‖ := by
  obtain ⟨C, c, hC, hc, hF⟩ := HRS.MC.E213U1.winDrift_far_proof hE T hT
  refine ⟨C, c, hC, hc, fun a ha Φ hΦ w bq hbm hbi z hz b hb hba => ?_⟩
  have hH : 0 < a + T := by linarith
  have hreg := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ ⟨hΦ.1, hΦ.2.1⟩
  have hcb : cbNorm 5 Φ ≤ 1 := hΦ.2.2
  have hcongr : rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b z) =
      rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b (fun v => NegSobolev.embed m (bq v))) := by
    refine u12_rsA_congr hE T hT a ha _ w _ _ (fun v hv => ?_)
    unfold farCoef
    rw [hz v hv]
  rw [hcongr]
  obtain ⟨_, hRS, _⟩ := HRS.MC.E213U7.rs_split_drift_proof hE T hT a ha Φ ⟨hΦ.1, hΦ.2.1⟩ w bq hbm hbi b hb hba
  have hs : MeasurableSet (Set.Ioc 0 (a + T) ∩ Set.Iio b) := measurableSet_Ioc.inter measurableSet_Iio
  have hsub : Set.Ioc 0 (a + T) ∩ Set.Iio b ⊆ Set.Ioc 0 (a + T) := Set.inter_subset_left
  have hfi := u12_weighted_integrableOn (c := c) (a := a) (b := b) hc hba hbm hbi hs hsub
    (fun v hv => (Set.mem_Iio.1 hv.2).le)
  refine u12_rs_bound_abstract hH hRS (fun v => Real.exp (-c * (a - v)) * ‖bq v‖)
    (fun v => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) _ hs hsub hfi C (fun τ u u' hu hτ hτ' hu' => ?_)
  have hint : IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖bq v‖) (Set.Ioc 0 (min b (a + T))) := by
    have hmin : min b (a + T) = b := min_eq_left (by linarith)
    have hsub2 : Set.Ioc 0 (min b (a + T)) ⊆ Set.Icc 0 (a + T) :=
      fun v hv => ⟨hv.1.le, hv.2.trans (min_le_right _ _)⟩
    have hae : AEStronglyMeasurable bq (volume.restrict (Set.Ioc 0 (min b (a + T)))) :=
      HRS.MC.E213U1.u1_aesm_of_nearCoef hbm measurableSet_Ioc (fun v hv => Set.mem_Ici.2 hv.1.le)
    have hexp : AEStronglyMeasurable (fun v : ℝ => Real.exp (-c * (a - v)))
        (volume.restrict (Set.Ioc 0 (min b (a + T)))) :=
      (by fun_prop : Continuous fun v : ℝ => Real.exp (-c * (a - v))).aestronglyMeasurable
    refine Integrable.mono' (hbi.mono_set hsub2) (hexp.mul hae.norm)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (norm_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (u12_exp_le_one hc ((hv.2.trans (min_le_left _ _)).trans hba))
  have hbd := hF a ha b hb bq hbm hint u u' hu (hτ.trans hτ') hu'
  have hset : Set.Ioc u u' ∩ (Set.Ioc 0 (a + T) ∩ Set.Iio b) = Set.Ioc u u' ∩ Set.Iio b := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, ⟨lt_of_le_of_lt hu h1.1, h1.2.trans hu'⟩, h3⟩
  rw [hset]
  have hnorm : |rsSumD (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha w τ)
        (fun u u' => winDrift (regime S β₀ hE) m T a ha (farCoef b (fun v => NegSobolev.embed m (bq v))) u u') τ u u'| ≤
      ‖fderiv ℝ (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha w τ)‖ *
        ‖winDrift (regime S β₀ hE) m T a ha (farCoef b (fun v => NegSobolev.embed m (bq v))) u u'‖ := by
    unfold rsSumD
    rw [← Real.norm_eq_abs]
    exact (fderiv ℝ (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha w τ)).le_opNorm _
  have hτH : τ ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hu.trans hτ, hτ'.trans hu'⟩
  have hf1 : ‖fderiv ℝ (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha w τ)‖ ≤ 1 := by
    rw [u12_fderiv_norm_le]
    exact (hreg.2.1 τ hτH 1 (by norm_num) _).trans hcb
  refine hnorm.trans ?_
  calc _ ≤ 1 * ‖winDrift (regime S β₀ hE) m T a ha (farCoef b (fun v => NegSobolev.embed m (bq v))) u u'‖ :=
        mul_le_mul_of_nonneg_right hf1 (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hbd

/-! ### The covariance far bound -/

theorem u12_J_far_bound (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ), Φ ∈ CbUnitBall (PathSpace d m T) 5 →
      ∀ (w : PathSpace d m (a + T)) (zq : ℝ → NegSobolev d (rLvl d)), Measurable (nearCoef 0 zq) →
      ∀ M : ℝ, (∀ v ∈ Set.Icc 0 (a + T), ‖zq v‖ ≤ M) →
      ∀ (z : ℝ → NegSobolev d m), (∀ v ∈ Set.Ioc 0 (a + T), z v = NegSobolev.embed m (zq v)) →
      ∀ (b : ℝ), 0 ≤ b → b ≤ a →
        |rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b z)| ≤
          C * ∫ v in Set.Ioc 0 (a + T) ∩ Set.Iio b, Real.exp (-c * (a - v)) * ‖zq v‖ := by
  obtain ⟨C, c, hC, hc, hF⟩ := HRS.MC.E213U3.winJ_far_proof hE T hT
  refine ⟨C, c, hC, hc, fun a ha Φ hΦ w zq hzm M hM z hz b hb hba => ?_⟩
  have hH : 0 < a + T := by linarith
  have hreg := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ ⟨hΦ.1, hΦ.2.1⟩
  have hcb : cbNorm 5 Φ ≤ 1 := hΦ.2.2
  have hbi : IntegrableOn (fun v => ‖zq v‖) (Set.Icc 0 (a + T)) := by
    have hg : IntegrableOn (fun _ : ℝ => M) (Set.Icc 0 (a + T)) := integrableOn_const (by simp)
    refine Integrable.mono' hg ?_ ?_
    · exact (HRS.MC.E213U1.u1_aesm_of_nearCoef hzm measurableSet_Icc (fun v hv => Set.mem_Ici.2 hv.1)).norm
    · exact ae_restrict_of_forall_mem measurableSet_Icc (fun v hv => by
        rw [norm_norm]
        exact hM v hv)
  have hcongr : rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b z) =
      rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b (fun v => NegSobolev.embed m (zq v))) := by
    refine u12_rsJ_congr hE T hT a ha _ w _ _ (fun v hv => ?_)
    unfold farCoef
    rw [hz v hv]
  rw [hcongr]
  obtain ⟨_, hRS, _⟩ := HRS.MC.E213U7.rs_split_J_proof hE T hT a ha Φ ⟨hΦ.1, hΦ.2.1⟩ w zq hzm M hM b hb hba
  have hs : MeasurableSet (Set.Ioc 0 (a + T) ∩ Set.Iio b) := measurableSet_Ioc.inter measurableSet_Iio
  have hsub : Set.Ioc 0 (a + T) ∩ Set.Iio b ⊆ Set.Ioc 0 (a + T) := Set.inter_subset_left
  have hfi := u12_weighted_integrableOn (c := c) (a := a) (b := b) hc hba hzm hbi hs hsub
    (fun v hv => (Set.mem_Iio.1 hv.2).le)
  refine u12_rs_bound_abstract hH hRS (fun v => Real.exp (-c * (a - v)) * ‖zq v‖)
    (fun v => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) _ hs hsub hfi C (fun τ u u' hu hτ hτ' hu' => ?_)
  have hint : IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖zq v‖) (Set.Ioc 0 (min b (a + T))) :=
    u12_weighted_integrableOn (c := c) (a := a) (b := b) hc hba hzm hbi measurableSet_Ioc
      (fun v hv => ⟨hv.1, hv.2.trans (min_le_right _ _)⟩) (fun v hv => hv.2.trans (min_le_left _ _))
  have hbd := (hF a ha b hb zq hzm hint u u' hu (hτ.trans hτ') hu').2
  have hset : Set.Ioc u u' ∩ (Set.Ioc 0 (a + T) ∩ Set.Iio b) = Set.Ioc u u' ∩ Set.Iio b := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, ⟨lt_of_le_of_lt hu h1.1, h1.2.trans hu'⟩, h3⟩
  rw [hset]
  have hτH : τ ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hu.trans hτ, hτ'.trans hu'⟩
  have hf2 : ‖iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha w τ)‖ ≤ 1 :=
    (hreg.2.1 τ hτH 2 (by norm_num) _).trans hcb
  have hnorm : |rsSumJ (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha w τ)
        (fun u u' => winJ (regime S β₀ hE) m T a ha (farCoef b (fun v => NegSobolev.embed m (zq v))) (Set.Ioc u u'))
        τ u u'| ≤
      ‖winJ (regime S β₀ hE) m T a ha (farCoef b (fun v => NegSobolev.embed m (zq v))) (Set.Ioc u u')‖ *
        ‖iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha w τ)‖ := by
    unfold rsSumJ
    rw [← Real.norm_eq_abs]
    exact ContinuousLinearMap.le_opNorm _ _
  refine hnorm.trans ?_
  calc _ ≤ ‖winJ (regime S β₀ hE) m T a ha (farCoef b (fun v => NegSobolev.embed m (zq v))) (Set.Ioc u u')‖ * 1 :=
        mul_le_mul_of_nonneg_left hf2 (ContinuousLinearMap.opNorm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact hbd

end HRS.MC.E213U12

end
