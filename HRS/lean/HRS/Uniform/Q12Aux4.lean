import HRS.Uniform.Q12Aux3
import HRS.PDE.MeanFieldPairInverse

/-!
# Q12, part 4: the Fourier side for the heat filter and the comparison of `heatGen^[L]` with `Δ^L`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS HRS.CoercAux

namespace HRS.Uniform.Q12

variable {d : ℕ}

/-- `Δ^m φ = (4π²)^m (Δ/4π²)^m φ`. -/
lemma q12_laplacian_iter_eq (L : ℕ) {φ : Torus d → ℝ}
    (hφ : Torus.IsCk ((2 * L : ℕ) : WithTop ℕ∞) φ) :
    ∀ m, m ≤ L → ∀ x, ((Torus.laplacian : (Torus d → ℝ) → Torus d → ℝ)^[m] φ) x =
      (4 * Real.pi ^ 2) ^ m * ((heatGen)^[m] φ) x := by
  intro m
  induction m with
  | zero => intro _ x; simp
  | succ m ih =>
    intro hm x
    have hm' : m ≤ L := by omega
    have h2 : Torus.IsCk 2 ((heatGen)^[m] φ) := by
      have := q12_isCk_iter (n := 2) m (ψ := φ) (hφ.of_le (by exact_mod_cast (by omega : 2 + 2 * m ≤ 2 * L)))
      exact this
    have e : ((Torus.laplacian : (Torus d → ℝ) → Torus d → ℝ)^[m] φ) =
        fun y => (4 * Real.pi ^ 2) ^ m * ((heatGen)^[m] φ) y := funext (ih hm')
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', e,
      PDE.MFPair.laplacian_smul_fun h2]
    have hpi : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
    have : Torus.laplacian ((heatGen)^[m] φ) x = (4 * Real.pi ^ 2) * heatGen ((heatGen)^[m] φ) x := by
      simp only [heatGen]; field_simp
    rw [this]; ring

lemma q12_heatGen_iter_bound (L : ℕ) {φ : Torus d → ℝ}
    (hφ : Torus.IsCk ((2 * L : ℕ) : WithTop ℕ∞) φ) {A : ℝ}
    (hA : ∀ x, |((Torus.laplacian : (Torus d → ℝ) → Torus d → ℝ)^[L] φ) x| ≤ A) (x : Torus d) :
    |((heatGen)^[L] φ) x| ≤ A := by
  have h := q12_laplacian_iter_eq L hφ L le_rfl x
  have hpi : (0 : ℝ) < (4 * Real.pi ^ 2) ^ L := by positivity
  have h1 := hA x
  rw [h, abs_mul, abs_of_pos hpi] at h1
  have h2 : (1 : ℝ) ≤ (4 * Real.pi ^ 2) ^ L := by
    apply one_le_pow₀
    nlinarith [Real.pi_gt_three]
  have h3 := abs_nonneg (((heatGen)^[L] φ) x)
  nlinarith

lemma q12_cT_anti (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ε ε' : ℝ} (hε : 0 < ε)
    (hεε : ε ≤ ε') (k : Lattice d) : cT d s ε' k ≤ cT d s ε k := by
  unfold cT
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk, if_neg hk]
    refine mul_le_mul_of_nonneg_left ?_ (subA_nonneg_one hd hs0 hsd)
    have ha : 0 < ((d : ℝ) - s) / 2 := by
      have : (s : ℝ) < d := hsd
      linarith
    refine setIntegral_mono_set (integrableOn_T ha hε k hk) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have : (0 : ℝ) < u := lt_of_lt_of_le hε (le_of_lt hu)
      positivity
    · exact Filter.Eventually.of_forall (Ioi_subset_Ioi hεε)

lemma q12_Esq_anti (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ε ε' : ℝ} (hε : 0 < ε)
    (hεε : ε ≤ ε') {N : ℕ} (hN : 0 < N) (X : Config d N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] : Esq d s ε' X μ ≤ Esq d s ε X μ := by
  have hε' : 0 < ε' := lt_of_lt_of_le hε hεε
  have hsum : ∀ {e : ℝ}, 0 < e → Summable fun k : Lattice d =>
      cT d s e k * ‖deltaF X μ k‖ ^ 2 := by
    intro e he
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (cT_nonneg hd hs0 hsd he k) (sq_nonneg _))
      (fun k => ?_) ((summable_cT hd hs0 hsd he).mul_right 4)
    refine mul_le_mul_of_nonneg_left ?_ (cT_nonneg hd hs0 hsd he k)
    have h2 : ‖deltaF X μ k‖ ≤ 2 := delta_norm_le hN X μ k
    have h3 := norm_nonneg (deltaF X μ k)
    nlinarith
  unfold Esq
  exact (hsum hε').tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right (q12_cT_anti hd hs0 hsd hε hεε k)
    (sq_nonneg _)) (hsum hε)

end HRS.Uniform.Q12
