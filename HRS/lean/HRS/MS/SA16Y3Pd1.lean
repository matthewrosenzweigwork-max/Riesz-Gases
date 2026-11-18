import HRS.MS.SA16ZR5
import HRS.MS.SA16Y3Lin1

/-!
# S.A.16 (SA16Y3) Pd1: `L^p` bound of the coordinate derivatives of `P_μ φ` (packet P7 iso, step (a))

`sa16y3_pd_P_bound`: for `μ ∈ C^∞` with `‖D^kμ‖ ≤ Λ` (`k ≤ j+2`) and `φ ∈ C_c^∞`, every coordinate derivative of order `j` of
`P_μ φ` satisfies `‖∂^idx (P_μ φ)‖_p ≤ K_j Λ ∑_{k ≤ j+2} ‖|D^kφ|‖_p` (from `∂^idx P_μφ = P_μ ∂^idxφ + C1 + Rem`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Pd1
variable {d : ℕ} {s : ℝ}

theorem sa16y3_pd_P_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 1 < p)
    (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {μ φ : Euc d → ℝ}, ContDiff ℝ ∞ μ → IsCcInfty φ → ∀ {Λ : ℝ}, 0 ≤ Λ →
      sa16z_Cb (j + 2) Λ μ → ∀ idx : Fin j → Fin d,
      eLpNorm (partialDeriv idx (sa16z_P s μ φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (K * Λ) * sa16z_S p φ (j + 2) := by
  obtain ⟨CP, hCP, hP⟩ := sa16z_P_jet_bound hd hs0 hsd hθ1 hp
  obtain ⟨C1c, hC1c, hC1⟩ := sa16z_C1_bound hd hs0 hsd hθ1 hp
  obtain ⟨-, -, hRem⟩ := sa16z_Rem_bound hd hs0 hsd hθ1 hp
  obtain ⟨KR, hKR0, hKR⟩ := hRem j
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    have : (1 : ℝ) ≤ p := hp.le
    simpa using ENNReal.ofReal_le_ofReal this
  refine ⟨CP * 2 * ((d : ℝ) * (1 + d)) + C1c * j + KR, by positivity, fun {μ φ} hμ hφ {Λ} hΛ hCb idx => ?_⟩
  have hfun : partialDeriv idx (sa16z_P s μ φ) = (fun x => sa16z_Rem s μ φ j idx x) +
      sa16z_P s μ (partialDeriv idx φ) + (fun x => sa16z_C1 s μ φ j idx x) := by
    funext x
    simp only [Pi.add_apply, sa16z_Rem]
    ring
  have e1 : eLpNorm (fun x => sa16z_Rem s μ φ j idx x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (KR * Λ) * sa16z_S p φ (j + 2) :=
    (hKR hμ hφ hΛ hCb idx).trans (by gcongr; exact sa16z_S_mono φ (by omega))
  have e2 : eLpNorm (sa16z_P s μ (partialDeriv idx φ)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (CP * (Λ + Λ) * ((d : ℝ) * (1 + d))) * sa16z_S p φ (j + 2) :=
    hP hμ hφ hΛ hΛ (sa16z_Cb_abs (sa16z_Cb_mono (by omega) hCb))
      (sa16z_Cb_fderiv (sa16z_Cb_mono (by omega) hCb)) idx
  have e3 : eLpNorm (fun x => sa16z_C1 s μ φ j idx x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (C1c * Λ * j) * sa16z_S p φ (j + 2) := by
    cases j with
    | zero =>
      have : (fun x => sa16z_C1 s μ φ 0 idx x) = 0 := rfl
      rw [this, eLpNorm_zero]; exact zero_le
    | succ n =>
      have := hC1 hμ hφ hΛ (sa16z_Cb_mono (by omega) hCb) n idx
      refine this.trans ?_
      push_cast
      gcongr
      · exact sa16z_S_mono φ (by omega)
  rw [hfun]
  calc eLpNorm ((fun x => sa16z_Rem s μ φ j idx x) + sa16z_P s μ (partialDeriv idx φ) +
        (fun x => sa16z_C1 s μ φ j idx x)) (ENNReal.ofReal p) volume
      ≤ (eLpNorm (fun x => sa16z_Rem s μ φ j idx x) (ENNReal.ofReal p) volume +
          eLpNorm (sa16z_P s μ (partialDeriv idx φ)) (ENNReal.ofReal p) volume) +
          eLpNorm (fun x => sa16z_C1 s μ φ j idx x) (ENNReal.ofReal p) volume :=
        (eLpNorm_add_le hp1).trans (by gcongr; exact eLpNorm_add_le hp1)
    _ ≤ (ENNReal.ofReal (KR * Λ) * sa16z_S p φ (j + 2) +
          ENNReal.ofReal (CP * (Λ + Λ) * ((d : ℝ) * (1 + d))) * sa16z_S p φ (j + 2)) +
          ENNReal.ofReal (C1c * Λ * j) * sa16z_S p φ (j + 2) := by gcongr
    _ = ENNReal.ofReal ((CP * 2 * ((d : ℝ) * (1 + d)) + C1c * j + KR) * Λ) * sa16z_S p φ (j + 2) := by
        rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2; ring

end Pd1

end HRS.Whole.AppendixA.Phase2SA16R
