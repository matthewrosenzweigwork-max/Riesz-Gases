import HRS.MS.SA16ZE10

/-!
# S.A.16 (SA16Z) F1: the isotropic dissipation inequality of the jet energy on `C_c^∞` (`d-1 < s < d`)

`sa16z_iso_pairing`: for `μ ≥ 0` in `C_b^∞` with `‖D^kμ‖ ≤ Λ` (`k ≤ m+3`) and `φ ∈ C_c^∞`,
`∫ sa16sz_dens m p φ (P_μ φ) ≤ C ∑_{k ≤ m} ∫ |D^kφ|^p`, i.e.
`d(jetEnergy_m)_{Jφ}(J(λ P_μ φ)) = p λ ∫ dens ≤ p λ C jetEnergy_m(Jφ)` (`sa16sz_fderiv_cc`, `sa16sz_energy_cc`),
with `λ P_μ = -𝒢` for `M = -λ I` (`P_μ φ = eucNonlocal s I μ φ`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.BreakdownSA16

section F1
variable {d : ℕ} {s : ℝ}

theorem sa16z_iso_pairing (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 2 ≤ p)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ φ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) → IsCcInfty φ →
      sa16z_Cb (m + 3) Λ μ →
      ∫ x, sa16sz_dens m p φ (sa16z_P s μ φ) x ≤
        C * ∑ k : Fin (m + 1), ∫ x, sa16sz_vn φ k x ^ p := by
  have hlev := fun j : ℕ => sa16z_level hd hs0 hsd hθ1 hp Λ hΛ j
  choose Cj hCj0 hCj using hlev
  refine ⟨∑ j ∈ Finset.range (m + 1), Cj j, Finset.sum_nonneg fun j _ => hCj0 j, fun {μ φ} hμ hpos hφ hCb => ?_⟩
  have hV0 : ∀ k, 0 ≤ ∫ x, sa16sz_vn φ k x ^ p := fun k =>
    integral_nonneg fun x => Real.rpow_nonneg (sa16sz_vn_nonneg φ k x) _
  have hμs : ContDiff ℝ ∞ μ := hμ.1
  have e : ∀ x, sa16sz_dens m p φ (sa16z_P s μ φ) x = ∑ j ∈ Finset.range (m + 1),
      sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x *
        partialDeriv idx (sa16z_P s μ φ) x := by
    intro x
    unfold sa16sz_dens
    exact Fin.sum_univ_eq_sum_range (fun j => sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d,
      partialDeriv idx φ x * partialDeriv idx (sa16z_P s μ φ) x) (m + 1)
  have hint : ∀ j ∈ Finset.range (m + 1), Integrable (fun x => sa16sz_vn φ j x ^ (p - 2) *
      ∑ idx : Fin j → Fin d, partialDeriv idx φ x * partialDeriv idx (sa16z_P s μ φ) x) :=
    fun j _ => sa16z_I_int hs0 hsd hμs hφ hp j
  simp_rw [e]
  rw [integral_finsetSum _ hint]
  have hsumk : ∑ k : Fin (m + 1), ∫ x, sa16sz_vn φ k x ^ p = ∑ k ∈ Finset.range (m + 1), ∫ x, sa16sz_vn φ k x ^ p :=
    Fin.sum_univ_eq_sum_range (fun k => ∫ x, sa16sz_vn φ k x ^ p) (m + 1)
  rw [hsumk]
  calc ∑ j ∈ Finset.range (m + 1), ∫ x, sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d,
        partialDeriv idx φ x * partialDeriv idx (sa16z_P s μ φ) x
      ≤ ∑ j ∈ Finset.range (m + 1), Cj j * ∑ k ∈ Finset.range (m + 1), ∫ x, sa16sz_vn φ k x ^ p := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjm : j ≤ m := by have := Finset.mem_range.1 hj; omega
        refine (hCj j hμ hpos hφ (sa16z_Cb_mono (by omega) hCb)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (hCj0 j)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun k _ _ => hV0 k
    _ = _ := by rw [Finset.sum_mul]

end F1

end HRS.Whole.AppendixA.Phase2SA16R
