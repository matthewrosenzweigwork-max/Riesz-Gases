import HRS.MS.ProClosureS111ChartLinearAllTests
import HRS.MS.ProClosureS111ChartedOrbits
import HRS.MS.S111K4ATF
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
Actual time-product integrability of the source insertions. Clamping the
physical adjoint orbit provides globally measurable bounded coefficient
families, equal to the requested orbit on its integration interval.
Product-time L2 of the physical fields and Gaussian terminal L4 moments
then suffice for the drift and covariance products.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.FixEq HRS.MS.S111K4AT

variable {d : ℕ} {Pw : ℝ}

theorem inner_bounded_family_memLp {A Omega V : Type*}
    [MeasurableSpace A] [MeasurableSpace Omega]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (dt : Measure A) (P : Measure Omega)
    (q : A × Omega → V) (hq : MemLp q 2 (dt.prod P))
    (c : A → V) (hc : StronglyMeasurable c)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ t, ‖c t‖ ≤ B) :
    MemLp (fun p : A × Omega => inner ℝ (q p) (c p.1)) 2 (dt.prod P) := by
  have hm : AEStronglyMeasurable (fun p : A × Omega => inner ℝ (q p) (c p.1))
      (dt.prod P) := hq.aestronglyMeasurable.inner
        (hc.comp_measurable measurable_fst).aestronglyMeasurable
  have hi : Integrable (fun p => ‖q p‖ ^ 2) (dt.prod P) :=
    (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).1 hq
  apply (memLp_two_iff_integrable_sq hm).2
  refine (hi.const_mul (B ^ 2)).mono' (hm.pow 2) (ae_of_all _ fun p => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hinner : |inner ℝ (q p) (c p.1)| ≤ ‖q p‖ * B :=
    (norm_inner_le_norm (𝕜 := ℝ) (q p) (c p.1)).trans
      (mul_le_mul_of_nonneg_left (hb p.1) (norm_nonneg _))
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hinner 2
  simpa only [sq_abs, mul_pow, mul_comm] using hsq

theorem inner_bounded_family_mul_integrable {A Omega V : Type*}
    [MeasurableSpace A] [MeasurableSpace Omega]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (dt : Measure A) [IsFiniteMeasure dt] (P : Measure Omega) [SFinite P]
    (q : A × Omega → V) (hq : MemLp q 2 (dt.prod P))
    (c : A → V) (hc : StronglyMeasurable c)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ t, ‖c t‖ ≤ B)
    (X : Omega → ℝ) (hX : MemLp X 2 P) :
    Integrable (fun p : A × Omega => inner ℝ (q p) (c p.1) * X p.2) (dt.prod P) :=
  (inner_bounded_family_memLp dt P q hq c hc B hB hb).integrable_mul (hX.comp_snd dt)

theorem frozen_encode_le_jet_bound {r : ℕ}
    (E : r26t6_WeightedChart d r Pw) (hP : (d : ℝ) < 2 * Pw)
    (f : Euc d → ℝ) (hf : MemCb r f)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    ‖E.encode f‖ ≤ s57pC d r Pw * B := by
  rw [E.norm _ (chart_weighted_of_memCb hP hf)]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (s57p_E_le_cb hP hB hb)
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (s57pC_nonneg _ _ _) hB)] using h

/-- Uniform bounded jets on the entire clamped initial-time parameter.
The terminal test is any original oscillator test. -/
theorem physical_clamped_orbit_jets (hd : 2 ≤ d)
    {s a beta H t : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) (ht : t ∈ Icc (0 : ℝ) H)
    {phi : Euc d → ℝ} (hphi : IsOscTest (wholeSpaceIndex d) phi) :
    let C := r26t6_thermalCoeff d s a beta rho
    let F := fun v => propagatorW C (Set.projIcc 0 t ht.1 v) t phi
    StronglyMeasurable (fun p : ℝ × Euc d => F p.1 p.2) ∧
      (∀ v, MemCb (2 * d + 9) (F v)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ v, ∀ j ≤ 2 * d + 9, ∀ x,
        ‖iteratedFDeriv ℝ j (F v) x‖ ≤ B := by
  let C := r26t6_thermalCoeff d s a beta rho
  let F := fun v => propagatorW C (Set.projIcc 0 t ht.1 v) t phi
  obtain ⟨hm, hreg⟩ := physical_clamped_orbit hd hs0 hsd ha hbeta hrho ht hphi
  obtain ⟨B, hB, hb⟩ := physical_oscillator_cb_bound hd hs0 hsd ha hbeta hrho
    (ht.1.trans ht.2)
  have hjet : ∀ v, ∀ j ≤ 2 * d + 9, ∀ x,
      ‖iteratedFDeriv ℝ j (F v) x‖ ≤ B * oscNorm (wholeSpaceIndex d) phi := by
    intro v j hj x
    exact (chart_derivative_le_cbNorm (hreg v) hj x).trans
      (hb phi hphi (Set.projIcc 0 t ht.1 v) t
        (Set.projIcc 0 t ht.1 v).property.1
        (Set.projIcc 0 t ht.1 v).property.2 ht.2).2.2
  exact ⟨hm, hreg, B * oscNorm (wholeSpaceIndex d) phi,
    (norm_nonneg _).trans (hjet 0 0 (Nat.zero_le _) 0), hjet⟩

theorem physical_encoded_clamped_orbit (hd : 2 ≤ d)
    {s a beta H t : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    (hP : (d : ℝ) < 2 * Pw) (E : r26t6_WeightedChart d (2 * d + 8) Pw)
    (ht : t ∈ Icc (0 : ℝ) H)
    {phi : Euc d → ℝ} (hphi : IsOscTest (wholeSpaceIndex d) phi) :
    let C := r26t6_thermalCoeff d s a beta rho
    let F := fun v => propagatorW C (Set.projIcc 0 t ht.1 v) t phi
    StronglyMeasurable (fun v => E.encode (F v)) ∧
      (∀ v, IsR2WeightedTest (2 * d + 8) Pw (F v)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ v, ‖E.encode (F v)‖ ≤ B := by
  obtain ⟨hm, hreg, B, hB, hb⟩ :=
    physical_clamped_orbit_jets hd hs0 hsd ha hbeta hrho ht hphi
  let C := r26t6_thermalCoeff d s a beta rho
  let F := fun v => propagatorW C (Set.projIcc 0 t ht.1 v) t phi
  have hreg' : ∀ v, MemCb (2 * d + 8) (F v) :=
    fun v => chart_memCb_mono (by omega) (hreg v)
  refine ⟨chart_encode_stronglyMeasurable (nativeChartOfFrozen E) hP F hm hreg',
    fun v => chart_weighted_of_memCb hP (hreg' v),
    s57pC d (2 * d + 8) Pw * B, mul_nonneg (s57pC_nonneg _ _ _) hB, ?_⟩
  exact fun v => frozen_encode_le_jet_bound E hP _ (hreg' v) B hB
    (fun j hj x => hb v j (by omega) x)

theorem physical_encoded_clamped_gradient_pair (hd : 2 ≤ d)
    {s a beta H ta tb : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    (hP : (d : ℝ) < 2 * Pw) (E : r26t6_WeightedChart d (2 * d + 8) Pw)
    (hta : ta ∈ Icc (0 : ℝ) H) (htb : tb ∈ Icc (0 : ℝ) H)
    {phi psi : Euc d → ℝ}
    (hphi : IsOscTest (wholeSpaceIndex d) phi) (hpsi : IsOscTest (wholeSpaceIndex d) psi) :
    let C := r26t6_thermalCoeff d s a beta rho
    let F := fun v => propagatorW C (Set.projIcc 0 ta hta.1 v) ta phi
    let G := fun v => propagatorW C (Set.projIcc 0 tb htb.1 v) tb psi
    let A := fun v x => inner ℝ (gradient (F v) x) (gradient (G v) x)
    StronglyMeasurable (fun v => E.encode (A v)) ∧
      (∀ v, IsR2WeightedTest (2 * d + 8) Pw (A v)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ v, ‖E.encode (A v)‖ ≤ B := by
  obtain ⟨hFm, hFr, Bf, hBf, hf⟩ :=
    physical_clamped_orbit_jets hd hs0 hsd ha hbeta hrho hta hphi
  obtain ⟨hGm, hGr, Bg, hBg, hg⟩ :=
    physical_clamped_orbit_jets hd hs0 hsd ha hbeta hrho htb hpsi
  let C := r26t6_thermalCoeff d s a beta rho
  let F := fun v => propagatorW C (Set.projIcc 0 ta hta.1 v) ta phi
  let G := fun v => propagatorW C (Set.projIcc 0 tb htb.1 v) tb psi
  let A := fun v x => inner ℝ (gradient (F v) x) (gradient (G v) x)
  have hAm : StronglyMeasurable (fun p : ℝ × Euc d => A p.1 p.2) := by
    have hF := chart_joint_gradient F hFm
      (fun v => (hFr v).1.differentiable (by norm_num))
    have hG := chart_joint_gradient G hGm
      (fun v => (hGr v).1.differentiable (by norm_num))
    exact (hF.measurable.inner hG.measurable).stronglyMeasurable
  have hAr : ∀ v, MemCb (2 * d + 8) (A v) :=
    fun v => chart_memCb_gradient_inner (hFr v) (hGr v)
  let B := (d : ℝ) * (2 ^ (2 * d + 8) * (Bf * Bg))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : ∀ v, ∀ j ≤ 2 * d + 8, ∀ x, ‖iteratedFDeriv ℝ j (A v) x‖ ≤ B := by
    intro v j hj x
    have he : A v = k4Gf (F v) (G v) := funext (k4_inner_grad_eq _ _)
    rw [he]
    exact k4Gf_bound (hFr v).1 (hGr v).1 (hf v) (hg v) j hj x
  refine ⟨chart_encode_stronglyMeasurable (nativeChartOfFrozen E) hP A hAm hAr,
    fun v => chart_weighted_of_memCb hP (hAr v),
    s57pC d (2 * d + 8) Pw * B, mul_nonneg (s57pC_nonneg _ _ _) hB, ?_⟩
  exact fun v => frozen_encode_le_jet_bound E hP _ (hAr v) B hB (hb v)

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_encoded_clamped_orbit
#print axioms HRS.MS.ProClosureS111.physical_encoded_clamped_gradient_pair
