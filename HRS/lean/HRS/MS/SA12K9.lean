import HRS.MS.SA12K8

/-!
# S.A.12 C1, uniform-in-time helper estimates for the density path

Weighted jet bounds, uniform continuity of the jets in time on compacts, local calculus of the mollification, and
the uniform closeness `Z_L(τ) → 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB HRS.MS.ToriConv

variable {d : ℕ}

theorem sa12k_den_weight {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ) :
    ∃ BG : ℝ, 0 ≤ BG ∧ ∀ τ ∈ Icc (0 : ℝ) T, ∀ i ≤ m + 3, ∀ w : Euc d,
      ‖iteratedFDeriv ℝ i (ρ τ) w‖ ≤ BG * tca_g w := by
  refine ⟨∑ i ∈ Finset.range (m + 4), (d : ℝ) ^ i * |Λ|,
    Finset.sum_nonneg fun i _ => by positivity, fun τ hτ i hi w => ?_⟩
  obtain ⟨-, hW, -⟩ := sa12k_den_facts hρ hτ
  have h1 := tca_abs_le_weight (fun w => ‖iteratedFDeriv ℝ i (ρ τ) w‖) ((d : ℝ) ^ i * |Λ|)
    (fun y' => by rw [abs_norm]; exact hW i hi y') w
  rw [abs_norm] at h1
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := fun i : ℕ => (d : ℝ) ^ i * |Λ|) (fun i _ => by positivity)
      (Finset.mem_range.2 (by omega))) (tca_g_nonneg w)

theorem sa12k_jet_uc {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ)
    {K : Set (Euc d)} (hK : IsCompact K) {i : ℕ} (hi : i ≤ m + 2) {τs : ℝ}
    (hτs : τs ∈ Icc (0 : ℝ) T) {η : ℝ} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ τ ∈ Icc (0 : ℝ) T, |τ - τs| < r → ∀ y ∈ K,
      ‖iteratedFDeriv ℝ i (ρ τ) y - iteratedFDeriv ℝ i (ρ τs) y‖ ≤ η := by
  have hS : IsCompact (Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  have hc : ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ i (ρ q.1) q.2) (Icc (0 : ℝ) T ×ˢ K) :=
    (sa12k_joint_jets hρ i hi).mono (prod_mono subset_rfl (subset_univ _))
  obtain ⟨r, hr, h⟩ := Metric.uniformContinuousOn_iff.1 (hS.uniformContinuousOn_of_continuous hc) η hη
  refine ⟨r, hr, fun τ hτ hτr y hy => ?_⟩
  have := h (τ, y) ⟨hτ, hy⟩ (τs, y) ⟨hτs, hy⟩ (by
    rw [Prod.dist_eq]
    simp only [dist_self, Real.dist_eq]
    rw [max_lt_iff]
    exact ⟨hτr, hr⟩)
  rw [dist_eq_norm] at this
  exact this.le

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
variable {δ : ℝ} {η : Euc d → ℝ}

theorem sa12k_moll_smul (η : Euc d → ℝ) (c : ℝ) (f : Euc d → W) (x : Euc d) :
    sa12k_moll η (fun y => c • f y) x = c • sa12k_moll η f x := by
  unfold sa12k_moll
  rw [← integral_smul]
  congr 1
  funext u
  rw [smul_comm]

theorem sa12k_moll_congr (hη : SA12KMoll δ η) {f g : Euc d → W} (x : Euc d)
    (h : ∀ u : Euc d, ‖u‖ ≤ δ → f (x - u) = g (x - u)) :
    sa12k_moll η f x = sa12k_moll η g x := by
  unfold sa12k_moll
  congr 1
  funext u
  by_cases hu : δ < ‖u‖
  · rw [hη.support u hu]; simp
  · rw [h u (not_lt.1 hu)]

theorem sa12k_Z_close_unif {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ)
    {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ L : ℝ, 0 < L → (N : ℝ) ≤ L / 4 → ∀ τ ∈ Icc (0 : ℝ) T,
      |(∫ y, ζ (L⁻¹ • y) * ρ τ y) - 1| ≤ ε := by
  obtain ⟨N, hN⟩ := tca_tail (d := d) (ε / (|Λ| + 1)) (by positivity)
  refine ⟨N, fun L hL hLN τ hτ => ?_⟩
  obtain ⟨-, hW, hprob⟩ := sa12k_den_facts hρ hτ
  have hρB : ∀ y : Euc d, |ρ τ y| ≤ |Λ| * tca_g y := by
    intro y
    exact tca_abs_le_weight (ρ τ) |Λ| (fun y' => by
      have := hW 0 (Nat.zero_le _) y'
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, one_mul] at this
      exact this) y
  have := tcv_Z_close hζ (ρ τ) hprob |Λ| (abs_nonneg _) hρB L hL N hLN _ hN
  refine this.trans ?_
  rw [mul_div_assoc']
  rw [div_le_iff₀ (by positivity)]
  nlinarith [abs_nonneg Λ]

end HRS.MH.AdjointRd.Phase2SA12Construction
