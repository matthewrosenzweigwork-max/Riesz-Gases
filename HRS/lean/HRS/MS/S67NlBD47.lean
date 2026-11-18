import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD14
import HRS.MS.S67NlBD43
import HRS.MS.S67NlBD44
import HRS.MS.S67NlBD45
import HRS.MS.S67NlBD46

/-!
# S6.7 nonlinear breakdown, packet 47: bound for the nonlocal term `J`

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4842-4851 area, nonlinear part of
`S:W:lem:r2mov-global-adjoint`. No owned definitions.
Route: `ρ r ∂_i u = (√ρ₀ + v) W_iψ =: h_i` (46), `h_i` is `C^{j+4}`, `L¹` and `H^{M-1}` with a bound by
`‖ψ‖_{Σ^M}` (45); the cancellation force of `h_i` is `local + far` (14); the local part is `C^{j+2}`
by 43 (margin `M - 1 - (movA - 1) > j + 2 + d/2`), the far part by 44; sum over the `d` coordinates.
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

theorem s67bd_J_bound (H : Mov2dTh d s β q ρ₀) (j M m : ℕ)
    (hM : (d : ℝ) / 2 + j + 5 < M) (hm : (d : ℝ) / 2 + 7 < m)
    (hmM : (M : ℝ) + 4 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R0 c0 : ℝ, 0 ≤ R0 → R0 ≤ 1 → 0 ≤ c0 →
      ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ →
      ∀ (r : ℝ), 0 ≤ r → ∀ u : Euc d → ℝ, MemCb 2 u →
      MemOsc (M : ℝ) (s67psi ρ₀ u) →
      ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) (s67J d s (ρ r) u) ∧
      ∀ l ≤ j + 2, ∀ x, ‖iteratedFDeriv ℝ l (s67J d s (ρ r) u) x‖ ≤
        C * oscNorm (M : ℝ) (s67psi ρ₀ u) := by
  have hd := H.hd
  have hs0 := H.hs0
  have hsd := H.hsd
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hM5 : 5 < M := by exact_mod_cast (show (5 : ℝ) < M by linarith)
  have ha2 : movA d s < 2 := by
    unfold movA; exact max_lt (by norm_num) (by linarith)
  have hkcast : (((M - 1 : ℕ)) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hkj : (((M - 1 : ℕ)) : ℝ) - (movA d s - 1) > (((j + 2 : ℕ)) : ℝ) + (d : ℝ) / 2 := by
    rw [hkcast]; push_cast; linarith
  obtain ⟨C45, hC45, h45⟩ := s67bd_J_product H j M m hM hm hmM
  obtain ⟨C43, hC43, h43⟩ := s67bd_force_local_cb hd hs0 hsd (M - 1) (j + 2) hkj
  obtain ⟨C44, hC44, h44⟩ := s67bd_force_far_cb hd hs0 hsd (j + 2)
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hsqsm : ContDiff ℝ ∞ (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hψs]; exact ψs.smooth _
  refine ⟨(d : ℝ) * ((C43 + C44) * C45), by positivity,
    fun R0 c0 hR0 hR1 hc0 f0 ρ hcls r hr u hu hψ => ?_⟩
  have hu1 : ContDiff ℝ 1 u := hu.1.of_le (by norm_num)
  -- the perturbation
  have hvcont : Continuous (movV ρ₀ ρ r) := by
    show Continuous (fun x => (ρ r x - ρ₀ x) / Real.sqrt (ρ₀ x))
    exact ((hcls.regular r hr).sub hρsm.continuous).div hsqsm.continuous
      (fun x => (Real.sqrt_pos.2 (hρpos x)).ne')
  obtain ⟨hvm, hvnorm⟩ := hcls.weighted r hr
  have hv1 : oscNorm (m : ℝ) (movV ρ₀ ρ r) ≤ 1 := by
    refine hvnorm.trans ?_
    have : Real.exp (-c0 * r) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith
  have hprod := fun i => h45 (movV ρ₀ ρ r) u hvcont hvm hv1 hu hψ i
  set h : Fin d → Euc d → ℝ := fun i x =>
    (Real.sqrt (ρ₀ x) + movV ρ₀ ρ r x) * s67bd_W ρ₀ i (s67psi ρ₀ u) x with hh
  set g : Fin d → Euc d → ℝ := fun i x =>
    s67bd_local d s (h i) i x + s67bd_far d s (h i) i x with hg
  have hosc : 0 ≤ oscNorm (M : ℝ) (s67psi ρ₀ u) := Real.sqrt_nonneg _
  have key : ∀ i : Fin d, ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) (g i) ∧
      ∀ l ≤ j + 2, ∀ x, ‖iteratedFDeriv ℝ l (g i) x‖ ≤
        (C43 + C44) * C45 * oscNorm (M : ℝ) (s67psi ρ₀ u) := by
    intro i
    obtain ⟨hCD, hI, hS, hbd⟩ := hprod i
    have hS' : HRS.PDE.ToolboxRd.MemSobolev (((M - 1 : ℕ)) : ℝ) (h i) := by
      rw [hkcast]; exact hS
    have hCD1 : ContDiff ℝ 1 (h i) := hCD.of_le (by exact_mod_cast (by omega : 1 ≤ j + 4))
    obtain ⟨hl, hlb⟩ := h43 (h i) hCD hI hS' i
    obtain ⟨hf, hfb⟩ := h44 (h i) hI i
    refine ⟨hl.add hf, fun l hl' x => ?_⟩
    have hlc : ContDiffAt ℝ (l : ℕ) (s67bd_local d s (h i) i) x :=
      (hl.of_le (by exact_mod_cast hl')).contDiffAt
    have hfc : ContDiffAt ℝ (l : ℕ) (s67bd_far d s (h i) i) x :=
      (hf.of_le (by exact_mod_cast hl')).contDiffAt
    have hsum : iteratedFDeriv ℝ l (g i) x = iteratedFDeriv ℝ l (s67bd_local d s (h i) i) x +
        iteratedFDeriv ℝ l (s67bd_far d s (h i) i) x :=
      iteratedFDeriv_add_apply hlc hfc
    rw [hsum]
    refine (norm_add_le _ _).trans ?_
    have e1 := hlb l hl' x
    have e2 := hfb l hl' x
    rw [hkcast] at e1
    have hI0 : 0 ≤ ∫ x, |h i x| := integral_nonneg (fun y => abs_nonneg _)
    have hH0 : 0 ≤ s67bd_Hnorm ((M : ℝ) - 1) (h i) := Real.sqrt_nonneg _
    calc _ ≤ C43 * ((∫ x, |h i x|) + s67bd_Hnorm ((M : ℝ) - 1) (h i)) + C44 * ∫ x, |h i x| :=
          add_le_add e1 e2
      _ ≤ C43 * (C45 * oscNorm (M : ℝ) (s67psi ρ₀ u)) + C44 * (C45 * oscNorm (M : ℝ) (s67psi ρ₀ u)) :=
          add_le_add (mul_le_mul_of_nonneg_left hbd hC43)
            (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right hH0).trans hbd) hC44)
      _ = _ := by ring
  have hJeq : s67J d s (ρ r) u = fun x => ∑ i : Fin d, g i x := by
    funext x
    rw [(s67bd_J_identity H ρ r u hu1).2 x]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨hCD, hI, -, -⟩ := hprod i
    have hCD1 : ContDiff ℝ 1 (h i) := hCD.of_le (by exact_mod_cast (by omega : 1 ≤ j + 4))
    exact ((s67bd_force_split hd hs0 hsd (h i) hCD1 hI x).2 i).2.2
  rw [hJeq]
  refine ⟨ContDiff.sum (fun i _ => (key i).1), fun l hl x => ?_⟩
  have hc : ∀ i ∈ (Finset.univ : Finset (Fin d)), ContDiffAt ℝ (l : ℕ) (g i) x := fun i _ =>
    ((key i).1.of_le (by exact_mod_cast hl)).contDiffAt
  rw [iteratedFDeriv_fun_sum_apply hc]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin d, ‖iteratedFDeriv ℝ l (g i) x‖
      ≤ ∑ _i : Fin d, (C43 + C44) * C45 * oscNorm (M : ℝ) (s67psi ρ₀ u) :=
        Finset.sum_le_sum fun i _ => (key i).2 l hl x
    _ = _ := by simp; ring

end HRS.MS.BreakdownS67
