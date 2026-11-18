import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD41

/-!
# S6.7 nonlinear, packet S6.7nl.59C: scalar short-time absorption with a common slab length

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4835-4851, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions: none.
The kernel `s67bd_kernel 1 0 w = 1 + w^(-1/2)` has mass `t + 2 sqrt t` on `[0,t]`; the slab
`tau* = delta^2`, `delta = 1/(6 (C Mb + 1))`, makes the Volterra feedback at most one half of the
finite supremum `S` of the bounded nonnegative path, and `S <= 2 D + C MJ <= (2 + C)(D + MJ)`.
Only the upper bound on the Volterra integral is used (nonnegative integrand against an
integrable majorant), so no measurability of `Y` is needed beyond the supplied hypothesis.
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

lemma s67bd59c_ker (w : ℝ) : s67bd_kernel 1 0 w = 1 + w ^ ((-1 : ℝ) / 2) := by
  unfold s67bd_kernel; simp

lemma s67bd59c_mass {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun v => s67bd_kernel 1 0 (t - v)) (Icc (0 : ℝ) t) volume ∧
      ∫ v in Icc (0 : ℝ) t, s67bd_kernel 1 0 (t - v) = t + 2 * Real.sqrt t := by
  have hr : IntervalIntegrable (fun x : ℝ => x ^ ((-1 : ℝ) / 2)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h1 : IntervalIntegrable (fun x : ℝ => 1 + x ^ ((-1 : ℝ) / 2)) volume 0 t :=
    intervalIntegrable_const.add hr
  have h2 : IntervalIntegrable (fun v : ℝ => 1 + (t - v) ^ ((-1 : ℝ) / 2)) volume 0 t := by
    have := (h1.comp_sub_left t).symm
    simpa using this
  have hfun : (fun v => s67bd_kernel 1 0 (t - v)) = fun v => 1 + (t - v) ^ ((-1 : ℝ) / 2) := by
    funext v; exact s67bd59c_ker _
  rw [hfun]
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at h2
    exact (integrableOn_Icc_iff_integrableOn_Ioc).2 h2
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => 1 + x ^ ((-1 : ℝ) / 2)) t]
    simp only [sub_self, sub_zero]
    rw [intervalIntegral.integral_add intervalIntegrable_const hr]
    have hp := integral_rpow (a := 0) (b := t) (r := (-1 : ℝ) / 2) (Or.inl (by norm_num))
    rw [hp]
    have e1 : (-1 : ℝ) / 2 + 1 = 1 / 2 := by norm_num
    rw [e1, Real.zero_rpow (by norm_num), ← Real.sqrt_eq_rpow]
    simp
    ring

theorem s67bd_short_kernel_absorb (C Mb : ℝ) (hC : 0 ≤ C) (hMb : 0 ≤ Mb) :
    ∃ τstar K : ℝ, 0 < τstar ∧ 1 ≤ K ∧
      ∀ T D MJ : ℝ, 0 ≤ T → T ≤ τstar → 0 ≤ D → 0 ≤ MJ →
      ∀ Y : ℝ → ℝ,
      AEStronglyMeasurable Y (volume.restrict (Icc (0 : ℝ) T)) →
      (∀ t ∈ Icc (0 : ℝ) T, 0 ≤ Y t) →
      (∃ A : ℝ, ∀ t ∈ Icc (0 : ℝ) T, Y t ≤ A) →
      (∀ t ∈ Icc (0 : ℝ) T, Y t ≤ D + C * ∫ v in Icc (0 : ℝ) t,
        s67bd_kernel 1 0 (t - v) * (Mb * Y v + MJ)) →
      ∀ t ∈ Icc (0 : ℝ) T, Y t ≤ K * (D + MJ) := by
  have hCMb : 0 ≤ C * Mb := mul_nonneg hC hMb
  set L : ℝ := C * Mb + 1 with hL
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  set δ : ℝ := 1 / (6 * L) with hδ
  have hδpos : 0 < δ := by positivity
  have hδL : 6 * L * δ = 1 := by rw [hδ]; field_simp
  have hδ1 : δ ≤ 1 := by nlinarith
  refine ⟨δ ^ 2, 2 + C, by positivity, by linarith, ?_⟩
  intro T D MJ hT hTτ hD hMJ Y _ hY0 hbdd hvol t ht
  obtain ⟨A, hA⟩ := hbdd
  have h0T : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hbd : BddAbove (Y '' Icc (0 : ℝ) T) := ⟨A, by rintro _ ⟨r, hr, rfl⟩; exact hA r hr⟩
  have hne : (Y '' Icc (0 : ℝ) T).Nonempty := ⟨Y 0, 0, h0T, rfl⟩
  set S : ℝ := sSup (Y '' Icc (0 : ℝ) T) with hS
  have hYS : ∀ r ∈ Icc (0 : ℝ) T, Y r ≤ S := fun r hr => le_csSup hbd ⟨r, hr, rfl⟩
  have hS0 : 0 ≤ S := (hY0 0 h0T).trans (hYS 0 h0T)
  -- mass bound
  have hmass : ∀ r ∈ Icc (0 : ℝ) T, r + 2 * Real.sqrt r ≤ 3 * δ := by
    intro r hr
    have hr' : r ≤ δ ^ 2 := hr.2.trans hTτ
    have hs : Real.sqrt r ≤ δ := by
      calc Real.sqrt r ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt hr'
        _ = δ := Real.sqrt_sq hδpos.le
    nlinarith
  have hstep : ∀ r ∈ Icc (0 : ℝ) T, Y r ≤ D + S / 2 + C * MJ / 2 := by
    intro r hr
    obtain ⟨hkint, hkmass⟩ := s67bd59c_mass hr.1
    have hc0 : 0 ≤ Mb * S + MJ := by positivity
    have hker : ∀ v ∈ Icc (0 : ℝ) r, 0 ≤ s67bd_kernel 1 0 (r - v) := fun v hv =>
      s67bd_kernel_nonneg 1 0 (sub_nonneg.2 hv.2)
    have hI : ∫ v in Icc (0 : ℝ) r, s67bd_kernel 1 0 (r - v) * (Mb * Y v + MJ) ≤
        (3 * δ) * (Mb * S + MJ) := by
      calc ∫ v in Icc (0 : ℝ) r, s67bd_kernel 1 0 (r - v) * (Mb * Y v + MJ)
          ≤ ∫ v in Icc (0 : ℝ) r, s67bd_kernel 1 0 (r - v) * (Mb * S + MJ) := by
            refine integral_mono_of_nonneg ?_ (hkint.mul_const _) ?_
            · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
              exact mul_nonneg (hker v hv)
                (by have := hY0 v ⟨hv.1, hv.2.trans hr.2⟩; positivity)
            · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
              have := hYS v ⟨hv.1, hv.2.trans hr.2⟩
              exact mul_le_mul_of_nonneg_left (by nlinarith) (hker v hv)
        _ = (r + 2 * Real.sqrt r) * (Mb * S + MJ) := by rw [integral_mul_const, hkmass]
        _ ≤ (3 * δ) * (Mb * S + MJ) :=
            mul_le_mul_of_nonneg_right (hmass r hr) hc0
    have e1 : C * Mb * (3 * δ) ≤ 1 / 2 := by nlinarith [hδpos]
    have e2 : 3 * δ ≤ 1 / 2 := by nlinarith
    have hfin : C * ((3 * δ) * (Mb * S + MJ)) ≤ S / 2 + C * MJ / 2 := by
      have a1 := mul_le_mul_of_nonneg_right e1 hS0
      have a2 := mul_le_mul_of_nonneg_left e2 (mul_nonneg hC hMJ)
      nlinarith
    have := hvol r hr
    nlinarith [mul_le_mul_of_nonneg_left hI hC]
  have hSle : S ≤ D + S / 2 + C * MJ / 2 :=
    csSup_le hne (by rintro _ ⟨r, hr, rfl⟩; exact hstep r hr)
  have hS2 : S ≤ 2 * D + C * MJ := by linarith
  calc Y t ≤ S := hYS t ht
    _ ≤ 2 * D + C * MJ := hS2
    _ ≤ (2 + C) * (D + MJ) := by nlinarith [mul_nonneg hC hD]

end HRS.MS.BreakdownS67
