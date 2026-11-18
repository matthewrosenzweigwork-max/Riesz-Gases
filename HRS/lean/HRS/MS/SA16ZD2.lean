import HRS.MS.SA16ZD1

/-!
# S.A.16 (SA16Z) D2: the top-order decomposition of `∂^idx (P_μ φ)`

`sa16z_decomp`: `∂^idx(P_μφ) = -c μ Λ^θ ∂^idxφ + ∑_l [(c_s - c c_θ) ∂_lμ pv_l ∂^idxφ - c_s Q_l(∂_aμ pv_l ∂^κφ)] + Err_idx`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section D2
variable {d : ℕ}

/-- `pvOdd_l G (x)` -/
abbrev sa16z_pv (d : ℕ) (θ : ℝ) (l : Fin d) (G : Euc d → ℝ) (x : Euc d) : ℝ :=
  pvOdd d θ (fun u : Euc d => u l) G x

/-- the commutator `pv_l (a G) - a pv_l G` -/
def sa16z_Cm (d : ℕ) (θ : ℝ) (l : Fin d) (a G : Euc d → ℝ) (x : Euc d) : ℝ :=
  sa16z_pv d θ l (fun y => a y * G y) x - a x * sa16z_pv d θ l G x

/-- the error of the Λ-commutator expansion -/
def sa16z_Rp (d : ℕ) (θ cθ : ℝ) (μ G : Euc d → ℝ) (x : Euc d) : ℝ :=
  lamComm d θ μ G x - cθ * ∑ l : Fin d, sa16z_dm μ l x * sa16z_pv d θ l G x

/-- the total error -/
def sa16z_Err (s c cθ : ℝ) (μ φ : Euc d → ℝ) (j : ℕ) (idx : Fin j → Fin d) (x : Euc d) : ℝ :=
  sa16z_Rem s μ φ j idx x - c * sa16z_Rp d (s + 2 - d) cθ μ (partialDeriv idx φ) x +
    HRS.CZ.Hls.hlsg_c s * ∑ l : Fin d, sa16z_Cm d (s + 2 - d) l (sa16z_dm μ l) (partialDeriv idx φ) x -
    HRS.CZ.Hls.hlsg_c s * ∑ l : Fin d, sa16z_Q j idx l
      (fun a κ => sa16z_Cm d (s + 2 - d) l (sa16z_dm μ a) (partialDeriv κ φ) x)

theorem sa16z_decomp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c cθ : ℝ} {μ φ : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ)
    (hP : ∀ {ψ : Euc d → ℝ}, IsCcInfty ψ → ∀ x : Euc d,
      sa16z_P s μ ψ x = -c * fracLap d (s + 2 - d) (fun y => μ y * ψ y) x +
        HRS.CZ.Hls.hlsg_c s * ∑ i : Fin d, sa16z_pv d (s + 2 - d) i (fun y => sa16z_dm μ i y * ψ y) x)
    (j : ℕ) (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv idx (sa16z_P s μ φ) x =
      -c * (μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x) +
      ∑ l : Fin d, ((HRS.CZ.Hls.hlsg_c s - c * cθ) * (sa16z_dm μ l x * sa16z_pv d (s + 2 - d) l (partialDeriv idx φ) x) -
        HRS.CZ.Hls.hlsg_c s * sa16z_Q j idx l (fun a κ => sa16z_dm μ a x * sa16z_pv d (s + 2 - d) l (partialDeriv κ φ) x)) +
      sa16z_Err s c cθ μ φ j idx x := by
  have h1 : partialDeriv idx (sa16z_P s μ φ) x = sa16z_Rem s μ φ j idx x +
      sa16z_P s μ (partialDeriv idx φ) x + sa16z_C1 s μ φ j idx x := by unfold sa16z_Rem; ring
  have h2 := hP (sa16s_cc_partialDeriv hφ idx) x
  have h3 : fracLap d (s + 2 - d) (fun y => μ y * partialDeriv idx φ y) x =
      μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x + sa16z_Rp d (s + 2 - d) cθ μ (partialDeriv idx φ) x +
        cθ * ∑ l : Fin d, sa16z_dm μ l x * sa16z_pv d (s + 2 - d) l (partialDeriv idx φ) x := by
    unfold sa16z_Rp lamComm; ring
  have h4 : ∀ i : Fin d, sa16z_pv d (s + 2 - d) i (fun y => sa16z_dm μ i y * partialDeriv idx φ y) x =
      sa16z_dm μ i x * sa16z_pv d (s + 2 - d) i (partialDeriv idx φ) x +
        sa16z_Cm d (s + 2 - d) i (sa16z_dm μ i) (partialDeriv idx φ) x := fun i => by unfold sa16z_Cm; ring
  have h5 := sa16z_C1_Q hd hs0 hsd hμ hφ j idx x
  have h6 : ∀ l : Fin d, sa16z_Q j idx l (fun a κ => pvOdd d (s + 2 - d) (fun u : Euc d => u l)
        (fun y => sa16z_dm μ a y * partialDeriv κ φ y) x) =
      sa16z_Q j idx l (fun a κ => sa16z_dm μ a x * sa16z_pv d (s + 2 - d) l (partialDeriv κ φ) x) +
        sa16z_Q j idx l (fun a κ => sa16z_Cm d (s + 2 - d) l (sa16z_dm μ a) (partialDeriv κ φ) x) := by
    intro l
    rw [← sa16z_Q_add]
    refine sa16z_Q_congr j idx l fun a κ => ?_
    unfold sa16z_Cm; simp only [sa16z_pv]; ring
  simp_rw [h6, Finset.sum_add_distrib] at h5
  simp_rw [h4] at h2
  rw [h3] at h2
  rw [h1, h2, h5]
  unfold sa16z_Err
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub, ← Finset.mul_sum]
  ring

end D2

end HRS.Whole.AppendixA.Phase2SA16R
