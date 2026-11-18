/-
# HRS.Equilibrium.Q84dAuxAA — packet Q84d: strictly measurable modifications of `B_ψ`
-/
import HRS.Equilibrium.Q84dAuxZ

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- Measurable surrogate of `B_ψ(x,y)` (equal to `B_ψ` off the diagonal). -/
def BsurK (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  ∑ k, (periodicRieszGrad d s (x - y)) k * (gK ψ k x y - gK ψ k y x) -
    2 * (∑ k, (forceField d s ρ x) k * gK ψ k x y + ∑ k, (forceField d s ρ y) k * gK ψ k y x)

theorem q84d_Bpsi_eq_BsurK {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ} (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {x y : Torus d}
    (hxy : x ≠ y) : Bpsi d s ρ ψ x y = BsurK d s ρ ψ x y := by
  have h1 : ∀ k, (gradFst ψ x y) k = gK ψ k x y := fun k => q84d_grad_comp hsm hxy k
  have h2 : ∀ k, (gradSnd ψ x y) k = gK ψ k y x := fun k => by
    rw [Q84a.q84a_gradSnd_eq hsymm]; exact q84d_grad_comp hsm hxy.symm k
  unfold Bpsi Vpsi BsurK
  simp only [PiLp.inner_apply, PiLp.sub_apply, h1, h2]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]
  · congr 1
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp [mul_comm]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp [mul_comm]

open Classical in
/-- Symmetrised, diagonal-killed version of `BsurK`. -/
def Btil (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  if x = y then 0 else (1 / 2) * (BsurK d s ρ ψ x y + BsurK d s ρ ψ y x)

theorem q84d_measurable_BsurK (hsd : s < d) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) :
    Measurable (fun p : Torus d × Torus d => BsurK d s ρ ψ p.1 p.2) := by
  have hgrav : ∀ k, Measurable (fun p : Torus d × Torus d => (periodicRieszGrad d s (p.1 - p.2)) k) :=
    fun k => (EuclideanSpace.proj k).continuous.measurable.comp
      ((KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd))
  have hF1 : ∀ k, Measurable (fun p : Torus d × Torus d => (forceField d s ρ p.1) k) := fun k =>
    ((EuclideanSpace.proj k).continuous.measurable.comp (q84d_measurable_grad _)).comp measurable_fst
  have hF2 : ∀ k, Measurable (fun p : Torus d × Torus d => (forceField d s ρ p.2) k) := fun k =>
    ((EuclideanSpace.proj k).continuous.measurable.comp (q84d_measurable_grad _)).comp measurable_snd
  have hg1 : ∀ k, Measurable (fun p : Torus d × Torus d => gK ψ k p.1 p.2) := q84d_measurable_gK ψ
  have hg2 : ∀ k, Measurable (fun p : Torus d × Torus d => gK ψ k p.2 p.1) := fun k =>
    q84d_measurable_swap_arg (hg1 k)
  unfold BsurK
  refine (Finset.measurable_sum _ fun k _ => (hgrav k).mul ((hg1 k).sub (hg2 k))).sub
    (measurable_const.mul ((Finset.measurable_sum _ fun k _ => (hF1 k).mul (hg1 k)).add
      (Finset.measurable_sum _ fun k _ => (hF2 k).mul (hg2 k))))

theorem q84d_Btil_props (hsd : s < d) {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ} {B : ℝ}
    (hsymm : IsSymmPair ψ) (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d))
    (hB0 : 0 ≤ B) (hB : ∀ x y : Torus d, x ≠ y → |Bpsi d s ρ ψ x y| ≤ B * wEnv s x y ^ 2) :
    Measurable (fun p : Torus d × Torus d => Btil d s ρ ψ p.1 p.2) ∧ IsSymmPair (Btil d s ρ ψ) ∧
      (∀ x y : Torus d, x ≠ y → |Btil d s ρ ψ x y| ≤ B * wEnv s x y ^ 2) ∧
      (∀ x y : Torus d, x ≠ y → Btil d s ρ ψ x y = Bpsi d s ρ ψ x y) := by
  classical
  have hBsymm : ∀ x y : Torus d, Bpsi d s ρ ψ x y = Bpsi d s ρ ψ y x := fun x y =>
    Q84.q84_Bpsi_symm hsd hsymm x y
  have heq : ∀ x y : Torus d, x ≠ y → Btil d s ρ ψ x y = Bpsi d s ρ ψ x y := by
    intro x y hxy
    unfold Btil
    rw [if_neg hxy, ← q84d_Bpsi_eq_BsurK hsymm hsm hxy, ← q84d_Bpsi_eq_BsurK hsymm hsm hxy.symm,
      ← hBsymm x y]
    ring
  refine ⟨?_, ?_, ?_, heq⟩
  · unfold Btil
    have hS := q84d_measurable_BsurK hsd ρ ψ
    have hS' := q84d_measurable_swap_arg (F := fun x y => BsurK d s ρ ψ x y) hS
    exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
      (measurable_const.mul (hS.add hS'))
  · intro x y
    unfold Btil
    by_cases h : x = y
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), add_comm]
  · intro x y hxy
    rw [heq x y hxy]; exact hB x y hxy

end HRS.Q84d

end
