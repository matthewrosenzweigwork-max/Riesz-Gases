import HRS.MS.R2SeAux29

/-!
# S9.9 `r2_static_edgeworth`, packet 30: the limit of the quadratic term for a bounded pair kernel

Worker S99, namespace `S99`.  `s99_Bkernel`: for `h ∈ IsBoundedPairKernel s B`, every `ε > 0` and `N ≥ N₀(ε,h)`,
`|E[B_h ψ(W_N)] - ½ ∑_{l,q} Q_h(l,q) E[∂_q∂_lψ(G)]| ≤ ε`, uniformly in `ψ ∈ Bd 4`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_tsum2_sub {b : ℕ → ℝ} (hb0 : ∀ j, 0 ≤ b j) (hbs : Summable b) {A1 A2 D : ℝ}
    {f g : ℕ → ℕ → ℝ} (hf : ∀ l q, |f l q| ≤ A1 * (b l * b q)) (hg : ∀ l q, |g l q| ≤ A2 * (b l * b q))
    (hfg : ∀ l q, |f l q - g l q| ≤ D * (b l * b q)) :
    |∑' l, ∑' q, f l q - ∑' l, ∑' q, g l q| ≤ D * (∑' j, b j) ^ 2 := by
  have hsum : ∀ (A : ℝ) (l : ℕ) (u : ℕ → ℝ), (∀ q, |u q| ≤ A * (b l * b q)) → Summable u := by
    intro A l u hu
    exact Summable.of_norm_bounded (hbs.mul_left (A * b l)) (fun q => by
      rw [Real.norm_eq_abs]; exact (hu q).trans (le_of_eq (by ring)))
  have hbd : ∀ (A : ℝ) (l : ℕ) (u : ℕ → ℝ), (∀ q, |u q| ≤ A * (b l * b q)) →
      |∑' q, u q| ≤ A * b l * ∑' j, b j := by
    intro A l u hu
    have hg' : HasSum (fun q => A * b l * b q) (A * b l * ∑' j, b j) := hbs.hasSum.mul_left _
    have := tsum_of_norm_bounded hg' (f := u) (fun q => by
      rw [Real.norm_eq_abs]; exact (hu q).trans (le_of_eq (by ring)))
    rwa [Real.norm_eq_abs] at this
  have hSf : Summable fun l => ∑' q, f l q := Summable.of_norm_bounded (hbs.mul_left (A1 * ∑' j, b j))
    (fun l => by
      rw [Real.norm_eq_abs]
      exact (hbd A1 l (f l) (hf l)).trans (le_of_eq (by ring)))
  have hSg : Summable fun l => ∑' q, g l q := Summable.of_norm_bounded (hbs.mul_left (A2 * ∑' j, b j))
    (fun l => by
      rw [Real.norm_eq_abs]
      exact (hbd A2 l (g l) (hg l)).trans (le_of_eq (by ring)))
  rw [← hSf.tsum_sub hSg]
  have hg' : HasSum (fun l => D * (∑' j, b j) * b l) (D * (∑' j, b j) * ∑' j, b j) :=
    hbs.hasSum.mul_left _
  have := tsum_of_norm_bounded hg' (f := fun l => ∑' q, f l q - ∑' q, g l q) (fun l => by
    rw [Real.norm_eq_abs, ← (hsum A1 l (f l) (hf l)).tsum_sub (hsum A2 l (g l) (hg l))]
    refine (hbd D l (fun q => f l q - g l q) (hfg l)).trans (le_of_eq ?_)
    ring)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  ring

section Bk

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

theorem s99_Qk_diff {k1 k2 : Euc d → Euc d → ℝ}
    (h1 : Integrable (Function.uncurry k1) ((thermalMeasure d s a β).prod (thermalMeasure d s a β)))
    (h2 : Integrable (Function.uncurry k2) ((thermalMeasure d s a β).prod (thermalMeasure d s a β)))
    (l q : ℕ) :
    |Qk d s a β γ φ k1 l q - Qk d s a β γ φ k2 l q| ≤
      (F.K * cbNorm (J1 d) (φ l)) * (F.K * cbNorm (J1 d) (φ q)) *
        ∫ p : Euc d × Euc d, |k1 p.1 p.2 - k2 p.1 p.2|
          ∂((thermalMeasure d s a β).prod (thermalMeasure d s a β)) := by
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  set μ := thermalMeasure d s a β with hμdef
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hal : ∀ l, Continuous (aRep d s a β γ (φ l)) := fun l => (F.amem l).1.continuous
  have hab : ∀ l x, |aRep d s a β γ (φ l) x| ≤ F.K * b l := fun l x => by
    have h1 := s99_norm_iter_le_cb (F.amem l) (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
    exact h1.trans (F.anorm l)
  set w : Euc d × Euc d → ℝ := fun p => aRep d s a β γ (φ l) p.1 * aRep d s a β γ (φ q) p.2 with hw
  have hwc : Continuous w := ((hal l).comp continuous_fst).mul ((hal q).comp continuous_snd)
  have hwb : ∀ p, |w p| ≤ (F.K * b l) * (F.K * b q) := fun p => by
    simp only [hw]; rw [abs_mul]
    exact mul_le_mul (hab l _) (hab q _) (abs_nonneg _) ((abs_nonneg _).trans (hab l 0))
  have hint : ∀ {k : Euc d → Euc d → ℝ}, Integrable (Function.uncurry k) (μ.prod μ) →
      Integrable (fun p : Euc d × Euc d => k p.1 p.2 * w p) (μ.prod μ) := fun {k} hk =>
    (hk.bdd_mul (f := w) (c := (F.K * b l) * (F.K * b q)) hwc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hwb p)).congr
      (Filter.Eventually.of_forall fun p => by simp only [Function.uncurry_apply_pair]; exact mul_comm _ _)
  have hQ : ∀ k : Euc d → Euc d → ℝ, Qk d s a β γ φ k l q = ∫ p : Euc d × Euc d, k p.1 p.2 * w p ∂(μ.prod μ) := by
    intro k
    unfold Qk
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [hw]; ring
  rw [hQ k1, hQ k2, ← integral_sub (hint h1) (hint h2)]
  have hA0 : 0 ≤ (F.K * b l) * (F.K * b q) := (abs_nonneg _).trans (hwb 0)
  have hdiff : Integrable (fun p : Euc d × Euc d => |k1 p.1 p.2 - k2 p.1 p.2|) (μ.prod μ) :=
    (h1.sub h2).abs
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  have e : ∀ A : ℝ, (F.K * b l) * (F.K * b q) * A = A * ((F.K * b l) * (F.K * b q)) := fun A => mul_comm _ _
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _)
    (hdiff.const_mul _) (Filter.Eventually.of_forall fun p => ?_)
  beta_reduce
  rw [← sub_mul, Real.norm_eq_abs, abs_mul]
  calc |k1 p.1 p.2 - k2 p.1 p.2| * |w p| ≤ |k1 p.1 p.2 - k2 p.1 p.2| * ((F.K * b l) * (F.K * b q)) :=
        mul_le_mul_of_nonneg_left (hwb p) (abs_nonneg _)
    _ = _ := mul_comm _ _

end Bk

end S99

end
