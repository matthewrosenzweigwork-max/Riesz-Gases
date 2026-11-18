/-
# HRS.Equilibrium.NormalForm (packet Q84, partial)

Algebraic parts of Lemma 4.15 (`triple_canonical`): symmetry of `G_ψ` and `B_ψ` for a symmetric `ψ`.
Still open (Q84): the canonicity `∫ G_ψ(x,y,z) μ(dz) = 0`, which needs the singular principal-value
identities for `Jop`/`forceField` (d = 2), the singular integration by parts `μ(B ψ(·,y)) = 0`,
`μ_y[J_yψ(x,y)] = -∫F_μ·∇_zψ(x,z) μ(dz)`; the size bounds; and for `normal_form` the stationarity
`E_P[particleGen (Fstat ψ)] = 0`, joint measurability of `Jpair ψ`, and the `ζ_N(a_f)` bound.
-/
import HRS.Equilibrium.PairCorrection

open MeasureTheory Filter Topology

noncomputable section

namespace HRS

variable {d : ℕ}

namespace Q84

variable {s : ℝ}

theorem q84_gradSnd_eq {ψ : Torus d → Torus d → ℝ} (hψ : IsSymmPair ψ) (x y : Torus d) :
    gradSnd ψ x y = gradFst ψ y x := by
  unfold gradSnd gradFst
  have : (fun z => ψ x z) = fun z => ψ z x := funext fun z => hψ x z
  rw [this]

theorem q84_gradFst_eq {ψ : Torus d → Torus d → ℝ} (hψ : IsSymmPair ψ) (x y : Torus d) :
    gradFst ψ x y = gradSnd ψ y x := by
  rw [q84_gradSnd_eq hψ]

theorem q84_Jpair_symm {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : IsSymmPair ψ)
    (x y : Torus d) : Jpair d s ρ ψ x y = Jpair d s ρ ψ y x := by
  unfold Jpair
  have h1 : (fun w => ψ w y) = fun w => ψ y w := funext fun w => hψ w y
  have h2 : (fun w => ψ x w) = fun w => ψ w x := funext fun w => hψ x w
  rw [h1, h2, add_comm]

theorem q84_Tpsi_symm {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : IsSymmPair ψ)
    (x y z : Torus d) : Tpsi d s ρ ψ x y z = Tpsi d s ρ ψ y x z := by
  unfold Tpsi
  rw [q84_gradFst_eq hψ y x, q84_gradSnd_eq hψ y x]
  ring

theorem q84_Gpsi_symm {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : IsSymmPair ψ) :
    IsSymmTriple (Gpsi d s ρ ψ) := by
  intro x y z
  have T := fun a b c => q84_Tpsi_symm (s := s) (ρ := ρ) hψ a b c
  have J := fun a b => q84_Jpair_symm (s := s) (ρ := ρ) hψ a b
  constructor
  · unfold Gpsi
    rw [T x y z, J x y]
    ring
  · unfold Gpsi
    rw [T z y x, J z y]
    ring

theorem q84_Bpsi_symm {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ} (hsd : s < d)
    (hψ : IsSymmPair ψ) : IsSymmPair (Bpsi d s ρ ψ) := by
  intro x y
  unfold Bpsi Vpsi
  rw [q84_gradFst_eq hψ y x, q84_gradSnd_eq hψ y x]
  have e : y - x = -(x - y) := by abel
  rw [e, HRS.KernelGrad.periodicRieszGrad_neg_of_lt hsd]
  simp only [inner_neg_left, inner_sub_right, inner_sub_left]
  ring

end Q84

end HRS
