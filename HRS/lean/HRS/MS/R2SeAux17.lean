import HRS.MS.R2SeAux16

/-!
# S9.9 `r2_static_edgeworth`, packet 17: the linear-term limit with a rate

Worker S99, namespace `S99`.  `s99_A_rate`: for every `f` in the Stein class and every `p = (j,k)`,
`|Aterm N f p - Alim f p| ≤ K b_j b_k / √N` (`b_j = ‖φ_j‖_{C_b^{J1}}`), where
`Aterm = √N E[(C_{jk} - μ_N(w_{jk})) ∂_k∂_j f(W_N)]` and `Alim = -∑_m c_{jk,m} E ∂_m∂_k∂_j f(G)`, `c_{jk,m} = ∫ w_{jk} a_m dμ`.
Proof: `√N(C - μ_N(w)) = -(Y_w + β_w)`; the plain Stein identity for `w` (corrector from `s99_chi1`) gives `E[Y_w ψ(W)]`; the
remaining terms are controlled by the LLN (`s99_T_L2`), the CLT (`s99_clt`), the bias (`s99_bias`) and `s99_Bq_bound`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_pair_smul (hN : 1 ≤ N) (c : ℝ) (f : Euc d → ℝ) (X : EucConfig d N) :
    pair (empirical X) (fun x => c * f x) = c * pair (empirical X) f := by
  have hN' : 0 < N := hN
  rw [pair_empirical hN', pair_empirical hN', ← Finset.mul_sum]
  ring

/-- `∫ |pair μ_N u - μ u| ≤ K B/√N`. -/
theorem s99_T_L1 {s : ℝ} {a β γ C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
    (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N) {KT : ℝ} (hKT0 : 0 ≤ KT)
    (hTL2 : ∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B → ∀ u : Euc d → ℝ, Measurable u → (∀ x, |u x| ≤ B) →
      ∫ X, (pair (empirical X) u - pair (thermalMeasure d s a β) u) ^ 2 ∂(S46.s46_P d s a β γ N) ≤
        (KT * B) ^ 2 / N)
    {N : ℕ} (hN : 2 ≤ N) {B : ℝ} (hB : 0 ≤ B) {u : Euc d → ℝ} (hu : Measurable u)
    (hub : ∀ x, |u x| ≤ B) :
    ∫ X, |pair (empirical X) u - pair (thermalMeasure d s a β) u| ∂(S46.s46_P d s a β γ N) ≤
      KT * B / Real.sqrt N := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hmeas : Measurable fun X : EucConfig d N => pair (empirical X) u - pair (thermalMeasure d s a β) u :=
    (s45_measurable_pair_empirical hN1 hu).sub measurable_const
  have hbd : ∀ X : EucConfig d N, |pair (empirical X) u - pair (thermalMeasure d s a β) u| ≤ B + B := by
    intro X
    have h1 := s45_abs_pair_empirical_le hN1 hub X
    have h2 : |pair (thermalMeasure d s a β) u| ≤ B :=
      HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hub x)
    calc _ ≤ |pair (empirical X) u| + |pair (thermalMeasure d s a β) u| := abs_sub _ _
      _ ≤ B + B := add_le_add h1 h2
  have hmem : MemLp (fun X : EucConfig d N => pair (empirical X) u - pair (thermalMeasure d s a β) u) 2
      (S46.s46_P d s a β γ N) :=
    MemLp.of_bound hmeas.aestronglyMeasurable (B + B) (Filter.Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact hbd X)
  refine (s99_integral_abs_le_sqrt hmem).trans ?_
  have h2 := hTL2 N hN B hB u hu hub
  have hsq : Real.sqrt ((KT * B) ^ 2 / N) = KT * B / Real.sqrt N := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (mul_nonneg hKT0 hB)]
  rw [← hsq]
  exact Real.sqrt_le_sqrt h2

end S99

end
