import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie

/-!
# S6.7 nonlinear, packet S6.7nl.41: bounded measurable scalar Volterra absorption

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4772-4774, 4844-4850, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definition: `s67bd_kernel`.
The kernel `(1 + t^(-a/2)) e^{-c t}` is integrable on translated intervals (beta integral), the
bounded measurable path `Y` gives integrability of the Volterra integrand, and the weighted
function `e^{c'(T-r)} Y r` has finite supremum, which is absorbed.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

def s67bd_kernel (a c t : ℝ) : ℝ := (1 + t ^ (-a / 2)) * Real.exp (-c * t)

lemma s67bd_kernel_nonneg (a c : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ s67bd_kernel a c t := by
  unfold s67bd_kernel
  have := Real.rpow_nonneg ht (-a / 2)
  positivity

lemma s67bd_kernel_eq (a κ t : ℝ) :
    s67bd_kernel a κ t = (1 + t ^ ((1 - a / 2) - 1)) * Real.exp (-(κ * t)) := by
  unfold s67bd_kernel
  have h : (1 - a / 2) - 1 = -a / 2 := by ring
  rw [h, neg_mul]

lemma s67bd_kernel_intervalIntegrable {a κ : ℝ} (ha : a < 2) (hκ : 0 < κ) {r T : ℝ}
    (hrT : r ≤ T) :
    IntervalIntegrable (fun v => s67bd_kernel a κ (v - r)) volume r T := by
  have hθ : 0 < 1 - a / 2 := by linarith
  have h0 := mnd_beta_intervalIntegrable hθ hκ (sub_nonneg.2 hrT)
  have h1 := h0.comp_sub_right r
  simp only [zero_add] at h1
  have h2 : (fun v => s67bd_kernel a κ (v - r)) =
      fun v => (1 + (v - r) ^ ((1 - a / 2) - 1)) * Real.exp (-(κ * (v - r))) := by
    funext v; exact s67bd_kernel_eq a κ (v - r)
  rw [h2]
  have h3 := h0.comp_sub_right r
  simpa using h3

lemma s67bd_kernel_integrableOn {a κ : ℝ} (ha : a < 2) (hκ : 0 < κ) {r T : ℝ}
    (hrT : r ≤ T) :
    IntegrableOn (fun v => s67bd_kernel a κ (v - r)) (Icc r T) volume := by
  have h := s67bd_kernel_intervalIntegrable ha hκ hrT
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrT] at h
  exact (integrableOn_Icc_iff_integrableOn_Ioc).2 h

lemma s67bd_kernel_integral_le {a κ : ℝ} (ha : a < 2) (hκ : 0 < κ) {r T : ℝ}
    (hrT : r ≤ T) :
    ∫ v in Icc r T, s67bd_kernel a κ (v - r) ≤ mndBeta (1 - a / 2) κ := by
  have hθ : 0 < 1 - a / 2 := by linarith
  have h1 := mnd_beta_le hθ hκ (sub_nonneg.2 hrT)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hrT]
  have h2 : (fun v => s67bd_kernel a κ (v - r)) =
      fun v => (fun τ : ℝ => (1 + τ ^ ((1 - a / 2) - 1)) * Real.exp (-(κ * τ))) (v - r) := by
    funext v; exact s67bd_kernel_eq a κ (v - r)
  rw [h2, intervalIntegral.integral_comp_sub_right
    (fun τ : ℝ => (1 + τ ^ ((1 - a / 2) - 1)) * Real.exp (-(κ * τ))) r]
  simpa using h1

theorem s67bd_volterra_absorb (T A η a c c' : ℝ)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hη : 0 ≤ η) (ha0 : 0 ≤ a) (ha2 : a < 2)
    (hc' : 0 < c') (hgap : c' < c) (Y : ℝ → ℝ)
    (hYmeas : AEStronglyMeasurable Y (volume.restrict (Icc (0 : ℝ) T)))
    (hYnonneg : ∀ r ∈ Icc (0 : ℝ) T, 0 ≤ Y r)
    (hYbdd : ∃ B : ℝ, ∀ r ∈ Icc (0 : ℝ) T, Y r ≤ B)
    (hvol : ∀ r ∈ Icc (0 : ℝ) T,
      Y r ≤ A * Real.exp (-c * (T - r)) +
        η * ∫ v in Icc r T, s67bd_kernel a c (v - r) * Y v)
    (hsmall : η * mndBeta (1 - a / 2) (c - c') ≤ 1 / 2) :
    (∀ r ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun v => s67bd_kernel a c (v - r) * Y v) (Icc r T) volume) ∧
    ∀ r ∈ Icc (0 : ℝ) T, Y r ≤ 2 * A * Real.exp (-c' * (T - r)) := by
  have hc : 0 < c := lt_trans hc' hgap
  have hκ : 0 < c - c' := sub_pos.2 hgap
  obtain ⟨B, hB⟩ := hYbdd
  have hint : ∀ r ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun v => s67bd_kernel a c (v - r) * Y v) (Icc r T) volume := by
    intro r hr
    have hker := s67bd_kernel_integrableOn ha2 hc hr.2
    have hmeas : AEStronglyMeasurable Y (volume.restrict (Icc r T)) :=
      hYmeas.mono_measure (Measure.restrict_mono (Icc_subset_Icc hr.1 le_rfl) le_rfl)
    refine Integrable.mul_bdd (c := max B 0) hker hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hv0 : v ∈ Icc (0 : ℝ) T := ⟨le_trans hr.1 hv.1, hv.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hYnonneg v hv0)]
    exact le_trans (hB v hv0) (le_max_left _ _)
  refine ⟨hint, ?_⟩
  -- the weighted path
  set Z : ℝ → ℝ := fun r => Real.exp (c' * (T - r)) * Y r with hZ
  have h0T : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hZnn : ∀ r ∈ Icc (0 : ℝ) T, 0 ≤ Z r := fun r hr =>
    mul_nonneg (Real.exp_pos _).le (hYnonneg r hr)
  have hZbdd : BddAbove (Z '' Icc (0 : ℝ) T) := by
    refine ⟨Real.exp (c' * T) * max B 0, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    have h1 : Real.exp (c' * (T - r)) ≤ Real.exp (c' * T) :=
      Real.exp_le_exp.2 (by nlinarith [hr.1])
    have h2 : Y r ≤ max B 0 := le_trans (hB r hr) (le_max_left _ _)
    have h3 : 0 ≤ Real.exp (c' * T) := (Real.exp_pos _).le
    calc Z r = Real.exp (c' * (T - r)) * Y r := rfl
      _ ≤ Real.exp (c' * T) * Y r := mul_le_mul_of_nonneg_right h1 (hYnonneg r hr)
      _ ≤ Real.exp (c' * T) * max B 0 := mul_le_mul_of_nonneg_left h2 h3
  set S : ℝ := sSup (Z '' Icc (0 : ℝ) T) with hS
  have hne : (Z '' Icc (0 : ℝ) T).Nonempty := ⟨Z 0, 0, h0T, rfl⟩
  have hZS : ∀ r ∈ Icc (0 : ℝ) T, Z r ≤ S := fun r hr => le_csSup hZbdd ⟨r, hr, rfl⟩
  have hS0 : 0 ≤ S := le_trans (hZnn 0 h0T) (hZS 0 h0T)
  have hstep : ∀ r ∈ Icc (0 : ℝ) T, Z r ≤ A + S / 2 := by
    intro r hr
    have hrT : r ≤ T := hr.2
    have hWint := s67bd_kernel_integrableOn ha2 hκ hrT
    have hWle := s67bd_kernel_integral_le ha2 hκ hrT
    have hpt : ∀ v ∈ Icc r T,
        Real.exp (c' * (T - r)) * (s67bd_kernel a c (v - r) * Y v) ≤
          s67bd_kernel a (c - c') (v - r) * S := by
      intro v hv
      have hv0 : v ∈ Icc (0 : ℝ) T := ⟨le_trans hr.1 hv.1, hv.2⟩
      have hexp : Real.exp (c' * (T - r)) * Real.exp (-c * (v - r)) =
          Real.exp (-(c - c') * (v - r)) * Real.exp (c' * (T - v)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have heq : Real.exp (c' * (T - r)) * (s67bd_kernel a c (v - r) * Y v) =
          s67bd_kernel a (c - c') (v - r) * Z v := by
        unfold s67bd_kernel
        simp only [hZ]
        calc Real.exp (c' * (T - r)) * ((1 + (v - r) ^ (-a / 2)) * Real.exp (-c * (v - r)) * Y v)
            = (1 + (v - r) ^ (-a / 2)) *
                (Real.exp (c' * (T - r)) * Real.exp (-c * (v - r))) * Y v := by ring
          _ = (1 + (v - r) ^ (-a / 2)) *
                (Real.exp (-(c - c') * (v - r)) * Real.exp (c' * (T - v))) * Y v := by rw [hexp]
          _ = (1 + (v - r) ^ (-a / 2)) * Real.exp (-(c - c') * (v - r)) *
                (Real.exp (c' * (T - v)) * Y v) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left (hZS v hv0)
        (s67bd_kernel_nonneg a _ (sub_nonneg.2 hv.1))
    have hI : Real.exp (c' * (T - r)) * ∫ v in Icc r T, s67bd_kernel a c (v - r) * Y v ≤
        mndBeta (1 - a / 2) (c - c') * S := by
      rw [← integral_const_mul]
      calc ∫ v in Icc r T, Real.exp (c' * (T - r)) * (s67bd_kernel a c (v - r) * Y v)
          ≤ ∫ v in Icc r T, s67bd_kernel a (c - c') (v - r) * S :=
            setIntegral_mono_on ((hint r hr).const_mul _) (hWint.mul_const S)
              measurableSet_Icc hpt
        _ = (∫ v in Icc r T, s67bd_kernel a (c - c') (v - r)) * S := integral_mul_const _ _
        _ ≤ mndBeta (1 - a / 2) (c - c') * S := mul_le_mul_of_nonneg_right hWle hS0
    have hE := Real.exp_pos (c' * (T - r))
    have hv := hvol r hr
    have hdec : Real.exp (c' * (T - r)) * Real.exp (-c * (T - r)) ≤ 1 := by
      rw [← Real.exp_add]
      exact Real.exp_le_one_iff.2 (by nlinarith [sub_nonneg.2 hrT])
    have hexp1 : Real.exp (c' * (T - r)) * (A * Real.exp (-c * (T - r))) ≤ A := by
      calc Real.exp (c' * (T - r)) * (A * Real.exp (-c * (T - r)))
          = A * (Real.exp (c' * (T - r)) * Real.exp (-c * (T - r))) := by ring
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hdec hA
        _ = A := mul_one A
    have hmul := mul_le_mul_of_nonneg_left hv hE.le
    have hk : η * (mndBeta (1 - a / 2) (c - c') * S) ≤ S / 2 := by
      calc η * (mndBeta (1 - a / 2) (c - c') * S)
          = (η * mndBeta (1 - a / 2) (c - c')) * S := by ring
        _ ≤ (1 / 2) * S := mul_le_mul_of_nonneg_right hsmall hS0
        _ = S / 2 := by ring
    have hηI := mul_le_mul_of_nonneg_left hI hη
    calc Z r = Real.exp (c' * (T - r)) * Y r := rfl
      _ ≤ Real.exp (c' * (T - r)) * (A * Real.exp (-c * (T - r)) +
            η * ∫ v in Icc r T, s67bd_kernel a c (v - r) * Y v) := hmul
      _ = Real.exp (c' * (T - r)) * (A * Real.exp (-c * (T - r))) +
            η * (Real.exp (c' * (T - r)) * ∫ v in Icc r T, s67bd_kernel a c (v - r) * Y v) := by
            ring
      _ ≤ A + S / 2 := by linarith
  have hSle : S ≤ A + S / 2 := csSup_le hne (by rintro _ ⟨r, hr, rfl⟩; exact hstep r hr)
  have hS2 : S ≤ 2 * A := by linarith
  intro r hr
  have hE := Real.exp_pos (c' * (T - r))
  have hZr : Z r ≤ 2 * A := le_trans (hZS r hr) hS2
  have hneg : Real.exp (-c' * (T - r)) * Real.exp (c' * (T - r)) = 1 := by
    rw [← Real.exp_add]; simp
  have hYr : Y r = Real.exp (-c' * (T - r)) * Z r := by
    simp only [hZ]
    calc Y r = (Real.exp (-c' * (T - r)) * Real.exp (c' * (T - r))) * Y r := by rw [hneg]; ring
      _ = _ := by ring
  rw [hYr]
  calc Real.exp (-c' * (T - r)) * Z r ≤ Real.exp (-c' * (T - r)) * (2 * A) :=
        mul_le_mul_of_nonneg_left hZr (Real.exp_pos _).le
    _ = 2 * A * Real.exp (-c' * (T - r)) := by ring

end HRS.MS.BreakdownS67
