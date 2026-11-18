import HRS.MS.S104eEx3
import HRS.MS.UlOu

/-!
# S104E route C, packet C0: shared definitions (see `docs/handoff/wip/S104E_C_spec.md`)

`ouQ`: the OU matrix `a·I`.  `HolB j η B f`: `f ∈ C^{j+1,η}` with norm at most `B` (jets up to `j+1` bounded by `B`, `D^{j+1}f` `η`-Hölder with constant `B`).
`VanB N f`: jets up to order `N` vanish at infinity.
-/

noncomputable section

open Filter Topology
open scoped ContDiff

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL

variable {d : ℕ}

def ouQ (d : ℕ) (a : ℝ) : Matrix (Fin d) (Fin d) ℝ := a • (1 : Matrix (Fin d) (Fin d) ℝ)

def HolB (j : ℕ) (η B : ℝ) (f : Euc d → ℝ) : Prop :=
  Bd (j + 1) B f ∧ ∀ x z : Euc d,
    ‖iteratedFDeriv ℝ (j + 1) f (x + z) - iteratedFDeriv ℝ (j + 1) f x‖ ≤ B * ‖z‖ ^ η

def VanB (N : ℕ) (f : Euc d → ℝ) : Prop :=
  ∀ i ≤ N, Tendsto (fun x : Euc d => ‖iteratedFDeriv ℝ i f x‖) (cocompact (Euc d)) (𝓝 0)

theorem HolB.bd {j : ℕ} {η B : ℝ} {f : Euc d → ℝ} (h : HolB j η B f) : Bd (j + 1) B f := h.1

theorem HolB.mono_B {j : ℕ} {η B B' : ℝ} {f : Euc d → ℝ} (h : HolB j η B f) (hB : B ≤ B') (hη : 0 ≤ η) :
    HolB j η B' f := by
  refine ⟨⟨h.1.1, fun i hi x => (h.1.2 i hi x).trans hB⟩, fun x z => (h.2 x z).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg (norm_nonneg _) _)

end HRS.MS.S104e.C
