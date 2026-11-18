import HRS.MC.S7FCW3F2
import HRS.MC.S7S7bAux1
import HRS.MC.S7FCDefs
import HRS.Sections.Sec7Setting
import HRS.Stochastic.EmpiricalIto
import HRS.Energy.KIDAux3

/-!
# FC-F3 helpers (packet `S7FCW7`): analytic and algebraic facts for the mode identity

Helpers for `HRS/MC/S7FCW7F3.lean`: empirical-measure integrals, the kernel identity for the pair
interaction when `M = -1`, the boundedness and integrability of `x ↦ ∫ h_f(x,y) dμ(y)` for a bounded
density `μ = ρ dx`, and the algebraic identity between the modulated-energy integrand and the difference
of the particle and mean-field drifts.  Namespace `HRS.MC.Sec7.S7FCW7`, prefix `s7fcw7_`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW7

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec

variable {d : ℕ}

theorem s7fcw7_matVec_neg_one (v : Euc d) :
    Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) v = -v := by
  simp [Torus.matVec]

theorem s7fcw7_hT_self (s : ℝ) (f : Torus d → ℝ) (x : Torus d) : hTransport d s f x x = 0 := by
  unfold hTransport
  simp

theorem s7fcw7_hT_meas {s : ℝ} (hsd : s < d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Measurable (Function.uncurry (hTransport d s f)) :=
  (HRS.MC.Sec7.S7FCW3.s7fcw3_hT_meas_symm hsd hf).1

theorem s7fcw7_isCk2 {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Torus.IsCk 2 f :=
  HRS.KID.isCk2_of_smooth hf

/-- Integrals against the empirical measure of a measurable function. -/
theorem s7fcw7_int_emp {N : ℕ} (X : Config d N) {φ : Torus d → ℝ} (hφ : Measurable φ) :
    ∫ x, φ x ∂(empirical X) = (N : ℝ)⁻¹ * ∑ i, φ (X i) := by
  unfold empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac' _ _ hφ.stronglyMeasurable, Finset.mul_sum]
  · intro i _
    exact integrable_dirac enorm_lt_top

/-- With `M = -1` the pair interaction is `-½ ∬ h_f dν dν`. -/
theorem s7fcw7_ip_neg (D : DynData d) (hM : D.M = -1) (f : Torus d → ℝ) (ν : Measure (Torus d)) :
    interactionPairing D f ν ν = -((1 / 2) * ∫ x, ∫ y, hTransport d D.s f x y ∂ν ∂ν) := by
  have key : ∀ x y : Torus d, (if x = y then (0 : ℝ) else
      inner ℝ (Torus.grad f x - Torus.grad f y) (Torus.matVec D.M (periodicRieszGrad d D.s (x - y))))
      = -hTransport d D.s f x y := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp [hTransport]
    · simp only [hxy, if_false, hTransport, hM, s7fcw7_matVec_neg_one, inner_neg_right]
  unfold interactionPairing
  simp_rw [key, integral_neg]
  ring

set_option maxHeartbeats 400000 in
/-- The pair interaction on the empirical measure of `X`. -/
theorem s7fcw7_ip_emp {N : ℕ} (D : DynData d) (hM : D.M = -1) {s : ℝ} (hsd : s < d) (f : Torus d → ℝ)
    (hf : Torus.IsSmooth f) (X : Config d N) (hD : D.s = s) :
    interactionPairing D f (empirical X) (empirical X) =
      -((1 / 2) * ((N : ℝ)⁻¹ * ∑ i, (N : ℝ)⁻¹ * ∑ j, hTransport d s f (X i) (X j))) := by
  have hm := s7fcw7_hT_meas hsd hf
  have hmx : ∀ x : Torus d, Measurable (fun y => hTransport d s f x y) := fun x =>
    Measurable.of_uncurry_left hm
  have hmy : ∀ j : Fin N, Measurable (fun x => hTransport d s f x (X j)) := fun j =>
    Measurable.of_uncurry_right hm
  have inner_eq : ∀ x, ∫ y, hTransport d s f x y ∂(empirical X) =
      (N : ℝ)⁻¹ * ∑ j, hTransport d s f x (X j) := fun x => s7fcw7_int_emp X (hmx x)
  have hint : ∫ x, ∫ y, hTransport d s f x y ∂(empirical X) ∂(empirical X) =
      (N : ℝ)⁻¹ * ∑ i, (N : ℝ)⁻¹ * ∑ j, hTransport d s f (X i) (X j) := by
    simp only [inner_eq]
    have hφ : Measurable (fun x => (N : ℝ)⁻¹ * ∑ j, hTransport d s f x (X j)) :=
      measurable_const.mul (Finset.measurable_sum Finset.univ fun j _ => hmy j)
    rw [s7fcw7_int_emp X hφ]
  rw [s7fcw7_ip_neg D hM f, hD, hint]

/-- Bound on the mean of the transport kernel against a bounded density. -/
theorem s7fcw7_H_bound {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {f : Torus d → ℝ} (hf : Torus.IsSmooth f) {ρ : Torus d → ℝ} (hρm : Measurable ρ) {M0 : ℝ}
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M0) :
    ∃ C : ℝ, ∀ x, ‖∫ y, hTransport d s f x y ∂(withDensityReal ρ)‖ ≤ C := by
  obtain ⟨K, c, hK0, hc0, hwc, henv⟩ := HRS.MC.Sec7.S7b.s7b_envelope hd hs0 hs
  have hsd : s < (d : ℝ) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hck : Torus.IsCk 2 f := s7fcw7_isCk2 hf
  have hgc : ∀ z : Torus d, 0 ≤ periodicRiesz d s z + c := by
    intro z
    by_cases hz : z = 0
    · subst hz; exact hc0
    · linarith [hwc z hz]
  have hbd : ∀ x y : Torus d, |hTransport d s f x y| ≤
      (K * d * Torus.cbNorm 2 f) * (periodicRiesz d s (x - y) + c) := by
    intro x y
    rw [HRS.MC.Sec7.S7FCW3.s7fcw3_hT_q66 hf]
    have hL := henv (fun j => Torus.partialDeriv j f) (fun _ => Torus.cbNorm 2 f)
      (fun _ => HRS.MD.EQRem.eqrem_cbNorm_nonneg 2 _)
      (fun j => HRS.PDE.R2Aux.isLipschitz_partialDeriv hck j) x y
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hL
    calc _ ≤ _ := hL
      _ = _ := by ring
  have hB0 : 0 ≤ K * d * Torus.cbNorm 2 f := by
    have := HRS.MD.EQRem.eqrem_cbNorm_nonneg 2 f
    positivity
  have hM0 : 0 ≤ M0 := (hρ0 0).trans (hρM 0)
  have hgI : Integrable (fun z : Torus d => periodicRiesz d s z + c) :=
    (HRS.KernelAux.integrable_periodicRiesz hd hs0 hsd).add (integrable_const c)
  refine ⟨M0 * ((K * d * Torus.cbNorm 2 f) * ∫ z : Torus d, (periodicRiesz d s z + c)), fun x => ?_⟩
  rw [HRS.PDE.MFPairing.integral_withDensityReal hρm hρ0]
  have hint : Integrable (fun y : Torus d => M0 * ((K * d * Torus.cbNorm 2 f) *
      (periodicRiesz d s (x - y) + c))) := by
    refine Integrable.const_mul ?_ _
    refine Integrable.const_mul ?_ _
    exact (hgI.comp_sub_left x)
  calc ‖∫ y, ρ y * hTransport d s f x y‖
      ≤ ∫ y, M0 * ((K * d * Torus.cbNorm 2 f) * (periodicRiesz d s (x - y) + c)) := by
        refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 y)]
        exact mul_le_mul (hρM y) (hbd x y) (abs_nonneg _) hM0
    _ = M0 * ((K * d * Torus.cbNorm 2 f) * ∫ z : Torus d, (periodicRiesz d s z + c)) := by
        rw [integral_const_mul, integral_const_mul]
        congr 2
        exact integral_sub_left_eq_self (fun z : Torus d => periodicRiesz d s z + c) volume x

theorem s7fcw7_sd {s : ℝ} (hd : 2 ≤ d) (hs : s < (d : ℝ) / 2) : s < (d : ℝ) := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- Integrability of `x ↦ ∫ h_f(x,y) ρ(y) dy` against the density `ρ dx`. -/
theorem s7fcw7_H_integrable {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {f : Torus d → ℝ} (hf : Torus.IsSmooth f) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {M0 : ℝ}
    (hρM : ∀ y, ρ y ≤ M0) :
    Integrable (fun x => ∫ y, hTransport d s f x y ∂(withDensityReal ρ)) (withDensityReal ρ) := by
  haveI := HRS.isProb_withDensityReal hρ
  obtain ⟨C, hC⟩ := s7fcw7_H_bound hd hs0 hs hf hρ.measurable hρ.nonneg hρM
  have hmeas : Measurable (fun x => ∫ y, hTransport d s f x y ∂(withDensityReal ρ)) :=
    ((s7fcw7_hT_meas (s7fcw7_sd hd hs) hf).stronglyMeasurable.integral_prod_right'
      (ν := withDensityReal ρ)).measurable
  exact Integrable.mono' (integrable_const C) hmeas.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hC x)

theorem s7fcw7_inv_mul (r n F : ℝ) (hr : r ≠ 0) (hn : n = r * r) : r⁻¹ * (n * F) = r * F := by
  subst hn
  field_simp

/-- The pointwise identity: the integrand of the mode identity equals `√N` times the difference of the particle
and mean-field drifts (for a given density `μ` and the empirical measure of `X`). -/
theorem s7fcw7_alg {N : ℕ} (hN : 0 < N) {s : ℝ} (hsd : s < d) (D : DynData d) (hM : D.M = -1) (hDs : D.s = s)
    (f : Torus d → ℝ) (hf : Torus.IsSmooth f) (X : Config d N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (L : Torus d → ℝ) (hLm : Measurable L) (hL : Integrable L μ)
    (hH : Integrable (fun x => ∫ y, hTransport d s f x y ∂μ) μ) :
    Real.sqrt N * (pair (empirical X) (fun x => L x - ∫ y, hTransport d s f x y ∂μ) -
        pair μ (fun x => L x - ∫ y, hTransport d s f x y ∂μ)) -
      (Real.sqrt N)⁻¹ * ((N : ℝ) * modulatedEnergy (hTransport d s f) X μ) =
    Real.sqrt N * ((pair (empirical X) L + interactionPairing D f (empirical X) (empirical X)) -
      (pair μ L + interactionPairing D f μ μ)) := by
  have hm := s7fcw7_hT_meas hsd hf
  have hHm : Measurable (fun x => ∫ y, hTransport d s f x y ∂μ) :=
    (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have e1 : pair (empirical X) (fun x => L x - ∫ y, hTransport d s f x y ∂μ) =
      (N : ℝ)⁻¹ * ∑ i, (L (X i) - ∫ y, hTransport d s f (X i) y ∂μ) := by
    unfold pair
    exact s7fcw7_int_emp X (hLm.sub hHm)
  have e2 : pair (empirical X) L = (N : ℝ)⁻¹ * ∑ i, L (X i) := by
    unfold pair
    exact s7fcw7_int_emp X hLm
  have e3 : pair μ (fun x => L x - ∫ y, hTransport d s f x y ∂μ) =
      pair μ L - ∫ x, ∫ y, hTransport d s f x y ∂μ ∂μ := by
    unfold pair
    exact integral_sub hL hH
  have e4 := s7fcw7_ip_neg D hM f μ
  rw [hDs] at e4
  have e5 := s7fcw7_ip_emp (N := N) D hM hsd f hf X hDs
  have e6 : modulatedEnergy (hTransport d s f) X μ =
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j, hTransport d s f (X i) (X j)
        - (1 / (N : ℝ)) * ∑ i, ∫ y, hTransport d s f (X i) y ∂μ
        + (1 / 2) * ∫ x, ∫ y, hTransport d s f x y ∂μ ∂μ := by
    unfold modulatedEnergy
    have hsum : ∑ i, ∑ j ∈ Finset.univ.erase i, hTransport d s f (X i) (X j) =
        ∑ i, ∑ j, hTransport d s f (X i) (X j) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_erase _ (s7fcw7_hT_self s f (X i))
    rw [hsum]
  have e5' : interactionPairing D f (empirical X) (empirical X) =
      -((1 / 2) * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, hTransport d s f (X i) (X j))) := by
    rw [e5]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hs0 : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  have hsq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt (Nat.cast_nonneg N)).symm
  rw [e1, e2, e3, e4, e5', e6, s7fcw7_inv_mul _ _ _ hs0 hsq]
  rw [Finset.sum_sub_distrib]
  ring


end HRS.MC.Sec7.S7FCW7
