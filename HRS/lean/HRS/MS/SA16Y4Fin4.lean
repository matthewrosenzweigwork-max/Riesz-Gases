import HRS.MS.SA16Y4Tc1
import HRS.MS.SA16Y4Dr1
import HRS.MS.SA16PForce6
import HRS.MS.SA16SNl4

/-!
# S.A.16 (SA16Y4) Fin4: drift constants and time continuity for `AdjointRdData` (sub case)

`sa16y4_drift_const`: constants `A, L ≥ 0` (depending on `d, s, m, MB, Λ, ΛV, G₀` only) with `‖b_r‖_{C^{m+2}}`-type bounds for the drift
`b_r = meanFieldDriftW D (μ r)` for every `AdjointRdData` and `r ∈ [0,T]`.
`sa16y4_drift_time`: from `AdjointRdData`, `r ↦ b_r(x)_j` and `r ↦ μ_r(y)` are continuous on `[0,T]`.
`sa16y4_comp_lip`: components of a drift with `‖D b‖ ≤ L` are `L`-Lipschitz.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Fin4
variable {d : ℕ}

theorem sa16y4_drift_const (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (MB Λ ΛV G₀ : ℝ) :
    ∃ A L : ℝ, 0 ≤ A ∧ 0 ≤ L ∧ ∀ (νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → ∀ r ∈ Icc (0 : ℝ) T,
        ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (meanFieldDriftW D (μ r)) ∧ ‖meanFieldDriftW D (μ r) 0‖ ≤ A ∧
          ∀ j, 1 ≤ j → j ≤ m + 2 → ∀ x, ‖iteratedFDeriv ℝ j (meanFieldDriftW D (μ r)) x‖ ≤ L := by
  refine ⟨|((d : ℝ) * d * MB) * ((d : ℝ) * (Phase2SA16P.sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s *
        ((d : ℝ) ^ (m + 3) * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2)))) + G₀|,
    |((d : ℝ) * d * MB) * ((d : ℝ) * (Phase2SA16P.sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s *
          ((d : ℝ) ^ (m + 3) * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2)))) + ΛV|, abs_nonneg _, abs_nonneg _,
    fun νbar T D μ hD r hr => ?_⟩
  obtain ⟨hDs, -, -⟩ := hD.hs
  have hρ : IsRegularDensityW (m + 3) Λ (μ r) := sa16so_regDensity_of_MF hD.hμ.regular hr
  obtain ⟨h1, h2, h3⟩ := Phase2SA16P.sa16p_drift_bounds hd hs0 hsd m hDs hD.hM hD.hV hρ
  exact ⟨h1, h2.trans (le_abs_self _), fun j hj1 hj2 x => (h3 j hj1 hj2 x).trans (le_abs_self _)⟩

theorem sa16y4_drift_time (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} {MB Λ ΛV G₀ νbar T : ℝ}
    {D : WholeDyn d} {μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ} (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) :
    (∀ x j, ContinuousOn (fun r => meanFieldDriftW D (μ r) x j) (Icc (0 : ℝ) T)) ∧
      ∀ y, ContinuousOn (fun r => μ r y) (Icc (0 : ℝ) T) := by
  obtain ⟨hDs, -, -⟩ := hD.hs
  obtain ⟨A, hA0, hdec, hpt⟩ := sa16y4_mu_data hd hD.hμ
  exact ⟨fun x j => sa16y4_drift_pointwise hd D (by rw [hDs]; exact hs0) (by rw [hDs]; exact hsd) hA0 hdec hpt x j,
    hpt⟩

lemma sa16y4_comp_lip {k : ℕ} (hk : 1 ≤ k) {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hb : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) b) {L : ℝ} (hL : ∀ x, ‖iteratedFDeriv ℝ 1 b x‖ ≤ L) (j : Fin d)
    (x y : EuclideanSpace ℝ (Fin d)) : |b x j - b y j| ≤ L * ‖x - y‖ := by
  have hdiff : Differentiable ℝ b := hb.differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hk)
  have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := b) (s := Set.univ)
    (fun z _ => hdiff z) (fun z _ => by simpa [norm_iteratedFDeriv_one] using hL z) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  have h2 : |b x j - b y j| ≤ ‖b x - b y‖ := by
    rw [← Real.norm_eq_abs]
    simpa using PiLp.norm_apply_le (b x - b y) j
  exact h2.trans (by rw [norm_sub_rev] at h1; simpa [norm_sub_rev] using h1)

end Fin4

end HRS.Whole.AppendixA.Phase2SA16R
