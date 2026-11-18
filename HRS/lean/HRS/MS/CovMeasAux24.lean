import HRS.MS.CovMeasAux23

/-!
# S10.1 (worker S101B), part 24: the observation vectors of a finite combination `φ = Σ c_α φ_α` and their pairings with the feature

`Pφ_t = Σ c_α P_{t,α}`, `Qφ = Σ c_α Q_α`.  `s101_recon_eval`: `(𝒯y)(t)(φ) = ⟨y(T), Pφ_t⟩ + ⟨y(t), Qφ⟩`.
`s101g_Pc`: `⟨Γ_τ(x), Pφ_t⟩ = 1_{τ<t} (U^{τ,t}φ - U^{τ,τ}φ)(x)`, `s101g_Qc`: `⟨Γ_τ(x), Qφ⟩ = U^{τ,τ}φ(x)` (uses `hlin`).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ}

/-- `Pφ_t = Σ c_α P_{t,α}`. -/
def s101Pc (m T t : ℝ) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) : KSpace d m T :=
  ∑ α ∈ S, c α • s101P m T t α

/-- `Qφ = Σ c_α Q_α`. -/
def s101Qc (m T : ℝ) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) : KSpace d m T :=
  ∑ α ∈ S, c α • s101Q m T α

theorem s101_recon_eval (hT : 0 ≤ T) (y : PathSp T (KSpace d m T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    OscDual.eval (r2PathAt (s56_reconCLM hT y : OscPath d m T) t) (fun x => ∑ α ∈ S, c α * oscTestFun m α x) =
      inner ℝ (pcm y ⟨T, hT, le_rfl⟩) (s101Pc m T t S c) + inner ℝ (pcm y ⟨t, ht⟩) (s101Qc m T S c) := by
  rw [s101_eval_combo]
  simp_rw [s101_recon_coord hT y ht]
  unfold s101Pc s101Qc
  rw [inner_sum, inner_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [inner_smul_right, inner_smul_right]
  ring

variable (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ, IsR2DualCombo m φ →
    IsR2DualCombo m ψ → propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ)

include hlin in
theorem s101g_Pc {c : MultiIndex d → ℝ} {r : ℕ} (hD : S101Data C m T r c) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (S : Finset (MultiIndex d))
    (a : MultiIndex d → ℝ) (x : Euc d) :
    inner ℝ (s101Gamma C m T τ x) (s101Pc m T t S a) =
      if τ < t then propagatorW C τ t (fun x => ∑ α ∈ S, a α * oscTestFun m α x) x -
        propagatorW C τ τ (fun x => ∑ α ∈ S, a α * oscTestFun m α x) x else 0 := by
  unfold s101Pc
  rw [inner_sum]
  have h1 : ∀ α ∈ S, inner ℝ (s101Gamma C m T τ x) (a α • s101P m T t α) =
      a α * (if τ < t then propagatorW C τ t (oscTestFun m α) x - propagatorW C τ τ (oscTestFun m α) x
        else 0) := by
    intro α _
    rw [inner_smul_right]
    have := s101g_P hD hτ ht α x
    unfold s101g at this
    unfold s101P
    rw [this]
  rw [Finset.sum_congr rfl h1]
  by_cases h : τ < t
  · simp only [h, if_true]
    rw [s101_prop_comb hlin hτ.1 h.le ht.2, s101_prop_comb hlin hτ.1 le_rfl hτ.2]
    simp only [mul_sub, Finset.sum_sub_distrib]
  · simp [h]

include hlin in
theorem s101g_Qc {c : MultiIndex d → ℝ} {r : ℕ} (hD : S101Data C m T r c) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) (x : Euc d) :
    inner ℝ (s101Gamma C m T τ x) (s101Qc m T S a) =
      propagatorW C τ τ (fun x => ∑ α ∈ S, a α * oscTestFun m α x) x := by
  unfold s101Qc
  rw [inner_sum]
  have h1 : ∀ α ∈ S, inner ℝ (s101Gamma C m T τ x) (a α • s101Q m T α) =
      a α * propagatorW C τ τ (oscTestFun m α) x := by
    intro α _
    rw [inner_smul_right]
    have := s101g_Q hD hτ α x
    unfold s101g at this
    unfold s101Q
    rw [this]
  rw [Finset.sum_congr rfl h1, s101_prop_comb hlin hτ.1 le_rfl hτ.2]

end HRS.MS.CovMeas
