import HRS.MS.R26T8AO04

/-!
# S8.2 T8A O06 (part a): `Psi` and the corrected pair statistic do not see additive constants
Used to pass from the projected orbit `projMean μ (propagatorW 0 v φ)` to the literal propagator in O06.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_o06_psi_const {a beta M C : ℝ} {rho : Euc d → ℝ} {Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ}
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi) {A : ℝ} {g : Euc d → ℝ}
    (hg : TestBound (testOrder d) A g) (c : ℝ) :
    Psi (fun x => g x + c) = Psi g := by
  have h1 : TestBound (testOrder d) 0 (fun _ : Euc d => (1 : ℝ)) := by
    refine ⟨contDiff_const, fun j hj1 hjk x => ?_⟩
    have : iteratedFDeriv ℝ j (fun _ : Euc d => (1 : ℝ)) x = 0 := by
      simp [iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
    rw [this, norm_zero]
  have := hPsi.linear g (fun _ => 1) A 0 hg h1 c
  have e : (fun x => g x + c) = g + c • (fun _ : Euc d => (1 : ℝ)) := by
    funext x; simp
  rw [e, this, hPsi.constants 1]
  simp

theorem r26t8a_o06_Q_const (N : ℕ) {a beta M C : ℝ} {rho : Euc d → ℝ}
    {Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ} (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi) {A : ℝ}
    {g : Euc d → ℝ} (hg : TestBound (testOrder d) A g) (c : ℝ) :
    r26t8a_correctedQ (N := N) a beta Psi (fun x => g x + c) = r26t8a_correctedQ (N := N) a beta Psi g := by
  unfold r26t8a_correctedQ Phase2S82.correctedQ
  rw [r26t8a_o06_psi_const hPsi hg c]

theorem r26t8a_o06_Q_proj (N : ℕ) {a beta M C : ℝ} {rho : Euc d → ℝ}
    {Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ} (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi) {A : ℝ}
    {g : Euc d → ℝ} (hg : TestBound (testOrder d) A g) (mu : Measure (Euc d)) :
    r26t8a_correctedQ (N := N) a beta Psi (HRS.Whole.projMean mu g) = r26t8a_correctedQ (N := N) a beta Psi g := by
  have e : HRS.Whole.projMean mu g = fun x => g x + (-(HRS.Whole.pair mu g)) := by
    funext x; unfold HRS.Whole.projMean; ring
  rw [e]
  exact r26t8a_o06_Q_const N hPsi hg _

end HRS.MS.R26T8A

end
