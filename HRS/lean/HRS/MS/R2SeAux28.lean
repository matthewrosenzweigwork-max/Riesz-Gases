import HRS.MS.R2SeAux27
import HRS.MS.R2MtAux3

/-!
# S9.9 `r2_static_edgeworth`, packet 28: the quadratic statistic of a bounded pair kernel

Worker S99, namespace `S99`.  `s99_Bkernel`: for `h ∈ IsBoundedPairKernel s B` and every `ε > 0` there is `N₀` with
`|E[B_h ψ(W_N)] - ½ ∑_{l,q} Q_h(l,q) E[∂_q∂_lψ(G)]| ≤ ε` for `N ≥ N₀`, uniformly in `ψ ∈ Bd 4`.
Finite-rank approximation (S9.1), tails uniform in `N` (S9.2), `s99_FR`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section Approx

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)

include hd hs0 hs ha hβ hγ hT hS

/-- A finite-rank approximant is a bounded pair kernel. -/
theorem s99_approx_bounded {B C₁ : ℝ} {h : Euc d → Euc d → ℝ} {hj : ℕ → Euc d → Euc d → ℝ}
    (ha' : IsRound2Approx s C₁ B (thermalMeasure d s a β) h hj) (n : ℕ) :
    IsBoundedPairKernel s (C₁ * B) (hj n) := by
  obtain ⟨m, cc, u, hu, e⟩ := ha'.finiteRank n
  refine ⟨?_, ?_, fun x y hxy => ha'.envelope n x y hxy⟩
  · have := HRS.MS.R2Mt.s92_finiteRank_meas hu
    rw [e]; exact this
  · intro x y; rw [e]; exact HRS.MS.R2Mt.s92_finiteRank_symm hu x y

/-- The kernel is `Wr8Ok`: integrable rows and integrable on `μ ⊗ μ`. -/
theorem s99_kernel_wr8 {B : ℝ} {k : Euc d → Euc d → ℝ} (hk : IsBoundedPairKernel s B k) :
    HRS.MS.Wr.Wr8Ok (thermalMeasure d s a β) k := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨L, hL, -⟩ := s99_round2_density hT
  obtain ⟨h1, h2, -⟩ := HRS.MS.R2Mt.s92_kernel_integrable (by omega) hs0 hsd C hL.prob hL.bdd hk
  exact ⟨hk.measurable, h1, h2⟩

/-- The pair energy of a bounded pair kernel is `P`-integrable. -/
theorem s99_pairE_int {B : ℝ} {k : Euc d → Euc d → ℝ} (hk : IsBoundedPairKernel s B k) {N : ℕ}
    (hN : 2 ≤ N) :
    Integrable (fun X : EucConfig d N => pairEnergy k X (thermalMeasure d s a β))
      (S46.s46_P d s a β γ N) := by
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hB : 0 ≤ B := HRS.MS.Wr.wr14a_nonneg_of_bound (by omega) (s := s) hk.bound
  obtain ⟨C₁, hC₁, hm, -⟩ := s99_mom hd hs0 hs ha hβ hγ hT hS 1 le_rfl
  have h1 := (hm N hN B hB k hk).1
  have hmeas : Measurable fun X : EucConfig d N => pairEnergy k X (thermalMeasure d s a β) :=
    HRS.MS.Wr.wr9_measurable_pairEnergy hk.measurable
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hmeas' : AEStronglyMeasurable (fun X : EucConfig d N => (N : ℝ) * pairEnergy k X
      (thermalMeasure d s a β)) (S46.s46_P d s a β γ N) := (measurable_const.mul hmeas).aestronglyMeasurable
  have h1' : eLpNorm (fun X : EucConfig d N => (N : ℝ) * pairEnergy k X (thermalMeasure d s a β)) 1
      (S46.s46_P d s a β γ N) ≤ ENNReal.ofReal (C₁ * B) := by simpa using h1
  obtain ⟨hi, -⟩ := s99_l1_bound (mul_nonneg hC₁ hB) hmeas' h1'
  have := hi.const_mul (N : ℝ)⁻¹
  refine this.congr (Filter.Eventually.of_forall fun X => ?_)
  simp only
  field_simp

end Approx

end S99

end
