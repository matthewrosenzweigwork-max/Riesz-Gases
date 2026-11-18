import HRS.MS.R2SeAux12

/-!
# S9.9 `r2_static_edgeworth`, packet 13: the exact expansion (D1)

Worker S99, namespace `S99`.  `s99_D1`: for `f` in the Stein class solving the Stein equation of `Φ` for the Gaussian `G` (coordinate
covariances `C_{jk} = Cov(φ_j, φ_k)`),

`E Φ(W_N) - E Φ(G) = ∑'_{(j,k)} E[(C_{jk} - μ_N(w_{jk})) ∂_k∂_j f(W_N)] + ∑'_j E[(Bq_j/√N) ∂_j f(W_N)]`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The constant of `s99_wF_cb`. -/
def Kw (d : ℕ) (γ : ℝ) {s a β : ℝ} {φ : ℕ → Euc d → ℝ} (F : FamData d s a β γ φ) : ℝ :=
  ((k0 d : ℝ) + 1) * 2 ^ k0 d * (γ⁻¹ * F.K)

theorem s99_Kw_nonneg {s a β γ : ℝ} {φ : ℕ → Euc d → ℝ} (F : FamData d s a β γ φ) (hγ : 0 < γ) :
    0 ≤ Kw d γ F := by
  unfold Kw
  have := F.hK
  positivity

theorem s99_T_bound (hd : 2 ≤ d) {s a β γ : ℝ} (hγ : 0 < γ) {φ : ℕ → Euc d → ℝ}
    (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ) (hN : 1 ≤ N) (j k : ℕ)
    (X : EucConfig d N) :
    |pair (empirical X) (wF F j k)| ≤ Kw d γ F * (cbNorm (J1 d) (φ j) * cbNorm (J1 d) (φ k)) := by
  have hw := s99_wF_cb hd hγ hφ.1 F j k
  have hsup : ∀ x, |wF F j k x| ≤ cbNorm (k0 d) (wF F j k) := fun x => by
    have := s99_norm_iter_le_cb hw.1 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  refine (s45_abs_pair_empirical_le hN hsup X).trans (hw.2.trans ?_)
  unfold Kw
  have : (0 : ℝ) ≤ cbNorm (J1 d) (φ k) := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have : (0 : ℝ) ≤ cbNorm (J1 d) (φ j) := HRS.MS.Tc5.tc5_cb_nonneg _ _
  nlinarith

theorem s99_chi_B2 {s a β γ : ℝ} {φ : ℕ → Euc d → ℝ} (F : FamData d s a β γ φ) (j : ℕ) (x : Euc d) :
    ‖fderiv ℝ (gradient (F.χ j)) x‖ ≤ F.K * cbNorm (J1 d) (φ j) := by
  have hχ2 : ContDiff ℝ 2 (F.χ j) := (F.smooth j).of_le (by
    exact_mod_cast (by unfold k0; omega : 2 ≤ k0 d + 1))
  exact (S45.s45_norm_fderiv_gradient hχ2 x).trans (F.deriv j x 1 (by unfold k0; omega))

theorem s99_Wc_bound (hN : 1 ≤ N) {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ)
    {ν : Measure (Euc d)} [IsProbabilityMeasure ν] (j : ℕ) (X : EucConfig d N) :
    |SeqL2.coord (featureVec φ ν X) j| ≤ 2 * Real.sqrt N * cbNorm (J1 d) (φ j) := by
  have e : SeqL2.coord (featureVec φ ν X) j =
      Real.sqrt N * (pair (empirical X) (φ j) - pair ν (φ j)) :=
    s45_coord_ofSeq (s45_feature_memℓp hN hφ X) j
  rw [e]
  exact s45_feature_bound hN hφ.1 (ν := ν) X j

end S99

end
