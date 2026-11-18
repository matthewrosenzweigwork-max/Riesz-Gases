import HRS.MS.R2SeAux39

/-!
# S9.9 `r2_static_edgeworth`, packet 40: identification of the limit coefficient

Worker S99, namespace `S99`.  With `T_{jkm}(f) = E ∂_m∂_k∂_j f(G)` and `κ_{jkm} = ∫ a_j a_k a_m dμ`:
the limit `∑_p Alim(f,p) + ∑_j ½ ∑_{lq} Q_j(l,q) T_{jlq}(f)` equals `-½ ∑_{jkm} κ_{jkm} T_{jkm}(f)`
(symmetry of `T` in the last two indices, symmetry of `Q_j`, and the cubic cancellation `s99_cancel`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- `κ_{jkm} = ∫ a_j a_k a_m dμ`. -/
def kap3 (d : ℕ) (s a β γ : ℝ) (φ : ℕ → Euc d → ℝ) (j k m : ℕ) : ℝ :=
  ∫ x, aRep d s a β γ (φ j) x * aRep d s a β γ (φ k) x * aRep d s a β γ (φ m) x ∂(thermalMeasure d s a β)

/-- `T_{jkm}(f) = ∫ ∂_m∂_k∂_j f dG`. -/
def T3 (G : Measure SeqL2) (f : SeqL2 → ℝ) (j k m : ℕ) : ℝ := ∫ z, pd (pd (pd f j) k) m z ∂G

theorem s99_pd_symm {g : SeqL2 → ℝ} (hg : ContDiff ℝ 2 g) (k m : ℕ) (z : SeqL2) :
    pd (pd g k) m z = pd (pd g m) k z := by
  rw [s99_pd_pd hg k m z, s99_pd_pd hg m k z]
  have := (hg.contDiffAt (x := z)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  exact this _ _

theorem T3_symm (G : Measure SeqL2) {f : SeqL2 → ℝ} (hf : SteinCl f) (j k m : ℕ) :
    T3 G f j k m = T3 G f j m k := by
  unfold T3
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact s99_pd_symm ((hf.pd j).1.of_le (by norm_num)) k m z

theorem T3_abs_le (G : Measure SeqL2) [IsProbabilityMeasure G] {f : SeqL2 → ℝ} (hf : SteinCl f) (j k m : ℕ) :
    |T3 G f j k m| ≤ 1 := by
  unfold T3
  have := norm_integral_le_of_norm_le_const (μ := G) (f := pd (pd (pd f j) k) m) (C := 1)
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact (((hf.pd j).pd k).pd m).abs_le z)
  simpa [Real.norm_eq_abs] using this

section Ident

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

theorem s99_Qk_symm {B : ℝ} {k : Euc d → Euc d → ℝ} (hk : IsBoundedPairKernel s B k) (l q : ℕ) :
    Qk d s a β γ φ k l q = Qk d s a β γ φ k q l := by
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  unfold Qk
  have := integral_prod_swap (μ := thermalMeasure d s a β) (ν := thermalMeasure d s a β)
    (fun p : Euc d × Euc d => k p.1 p.2 * aRep d s a β γ (φ l) p.1 * aRep d s a β γ (φ q) p.2)
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [hk.symm p.2 p.1]; ring

theorem s99_Qk_bd {B : ℝ} {k : Euc d → Euc d → ℝ} (hk : IsBoundedPairKernel s B k) (l q : ℕ) :
    |Qk d s a β γ φ k l q| ≤ F.K ^ 2 * (∫ p : Euc d × Euc d, |k p.1 p.2|
      ∂((thermalMeasure d s a β).prod (thermalMeasure d s a β))) *
      (cbNorm (J1 d) (φ l) * cbNorm (J1 d) (φ q)) := by
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hwr := s99_kernel_wr8 hd hs0 hs ha hβ hγ hT hS hk
  have hzero : Integrable (Function.uncurry fun (_ _ : Euc d) => (0 : ℝ))
      ((thermalMeasure d s a β).prod (thermalMeasure d s a β)) := integrable_const (0 : ℝ)
  have hQ0 : Qk d s a β γ φ (fun _ _ => (0 : ℝ)) l q = 0 := by unfold Qk; simp
  have := s99_Qk_diff hd hs0 hs ha hβ hγ hT hS hφ F hwr.prod hzero l q
  rw [hQ0, sub_zero] at this
  simp only [sub_zero] at this
  refine this.trans (le_of_eq ?_)
  ring

theorem s99_kap3_bd (j k m : ℕ) :
    |kap3 d s a β γ φ j k m| ≤ F.K ^ 3 * (cbNorm (J1 d) (φ j) * cbNorm (J1 d) (φ k) * cbNorm (J1 d) (φ m)) := by
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨-, hj, -⟩ := s99_ua hd hs0 hs ha hβ hγ hT hφ F j
  obtain ⟨-, hk, -⟩ := s99_ua hd hs0 hs ha hβ hγ hT hφ F k
  obtain ⟨-, hm, -⟩ := s99_ua hd hs0 hs ha hβ hγ hT hφ F m
  unfold kap3
  have := norm_integral_le_of_norm_le_const (μ := thermalMeasure d s a β)
    (f := fun x => aRep d s a β γ (φ j) x * aRep d s a β γ (φ k) x * aRep d s a β γ (φ m) x)
    (C := (F.K * cbNorm (J1 d) (φ j)) * (F.K * cbNorm (J1 d) (φ k)) * (F.K * cbNorm (J1 d) (φ m)))
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h0 : 0 ≤ F.K * cbNorm (J1 d) (φ j) := (abs_nonneg _).trans (hj 0)
      have h1 : 0 ≤ F.K * cbNorm (J1 d) (φ k) := (abs_nonneg _).trans (hk 0)
      exact mul_le_mul (mul_le_mul (hj x) (hk x) (abs_nonneg _) h0) (hm x) (abs_nonneg _) (mul_nonneg h0 h1))
  simp only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] at this
  refine this.trans (le_of_eq ?_)
  ring

end Ident

end S99

end
