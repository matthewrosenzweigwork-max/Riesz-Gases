import HRS.MC.SEdgeVocab

/-!
# Packet B4c: `sed_B4c_iid_moment` (even moments of the empirical mean under the product law)

Route: the centred summands `u(x_i) - mu(u)` are independent and bounded, hence sub-Gaussian
(Hoeffding's lemma); the sum `Z` is sub-Gaussian with parameter `N kappa`; and
`(Z/N)^{2m} N^m = (Z/sqrt N)^{2m} <= (2m)! (exp(Z/sqrt N) + exp(-Z/sqrt N))`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B4c

open HRS

theorem b4c_pair_empirical {d N : ℕ} (X : Config d N) {u : Torus d → ℝ} (hu : Measurable u) :
    pair (empirical X) u = (∑ i, u (X i)) / N := by
  unfold pair empirical
  rw [integral_smul_measure, integral_finset_sum_measure]
  · simp only [integral_dirac' _ _ hu.stronglyMeasurable, smul_eq_mul]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    ring
  · intro i _
    exact integrable_dirac' hu.stronglyMeasurable (by simp)


/-- `y^(2m) <= (2m)! (exp y + exp (-y))`. -/
theorem b4c_pow_le (m : ℕ) (y : ℝ) :
    y ^ (2 * m) ≤ ((2 * m).factorial : ℝ) * (Real.exp y + Real.exp (-y)) := by
  have h1 : |y| ^ (2 * m) / ((2 * m).factorial : ℝ) ≤ Real.exp |y| :=
    Real.pow_div_factorial_le_exp |y| (abs_nonneg y) (2 * m)
  have hf : (0 : ℝ) < ((2 * m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h2 : |y| ^ (2 * m) ≤ ((2 * m).factorial : ℝ) * Real.exp |y| := by
    have := (div_le_iff₀ hf).1 h1
    linarith
  have h3 : y ^ (2 * m) = |y| ^ (2 * m) := by
    rw [pow_mul, pow_mul, sq_abs]
  have h4 : Real.exp |y| ≤ Real.exp y + Real.exp (-y) := by
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; have := Real.exp_pos (-y); linarith
    · rw [h]; have := Real.exp_pos y; linarith
  rw [h3]
  exact h2.trans (mul_le_mul_of_nonneg_left h4 hf.le)

theorem b4c_main {d : ℕ} (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (M : ℝ) (m : ℕ) :
    ∃ C : ℝ, ∀ u : Torus d → ℝ, Measurable u → (∀ x, |u x| ≤ M) → ∀ N : ℕ, 1 ≤ N →
      ∫ X : Config d N, (pair (empirical X) u - pair μ u) ^ (2 * m)
        ∂(Measure.pi fun _ : Fin N => μ) ≤ C / (N : ℝ) ^ m := by
  set κ : ℝ≥0 := (‖M - -M‖₊ / 2) ^ 2 with hκ
  refine ⟨2 * ((2 * m).factorial : ℝ) * Real.exp ((κ : ℝ) / 2), ?_⟩
  intro u hum hb N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set ν : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hν
  -- sub-Gaussian coordinates
  have h1 : HasSubgaussianMGF (fun x => u x - μ[u]) κ μ :=
    hasSubgaussianMGF_of_mem_Icc (a := -M) (b := M) hum.aemeasurable
      (ae_of_all _ fun x => abs_le.1 (hb x))
  have h2 : ∀ i : Fin N, HasSubgaussianMGF (fun ω : Config d N => u (ω i) - μ[u]) κ ν := by
    intro i
    have hY : AEMeasurable (fun ω : Config d N => ω i) ν := (measurable_pi_apply i).aemeasurable
    have := HasSubgaussianMGF.of_map (μ := ν) hY
      (by rwa [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq] : HasSubgaussianMGF
        (fun x => u x - μ[u]) κ (ν.map fun ω : Config d N => ω i))
    exact this
  have hind : iIndepFun (fun (i : Fin N) (ω : Config d N) => u (ω i) - μ[u]) ν :=
    iIndepFun_pi (X := fun _ : Fin N => fun x : Torus d => u x - μ[u]) (μ := fun _ => μ)
      (fun _ => (hum.sub_const _).aemeasurable)
  have h3 := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ) (fun i _ => h2 i)
  set Z : Config d N → ℝ := fun ω => ∑ i, (u (ω i) - μ[u]) with hZ
  have hZmeas : Measurable Z := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (hum.comp (measurable_pi_apply i)).sub_const _
  have hcoe : ((∑ _i : Fin N, κ : ℝ≥0) : ℝ) = N * κ := by simp
  -- the quantity
  have hq : ∀ X : Config d N, pair (empirical X) u - pair μ u = Z X / N := by
    intro X
    rw [b4c_pair_empirical X hum]
    simp only [hZ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, pair]
    field_simp
  simp_rw [hq]
  -- the pointwise bound
  set s : ℝ := 1 / Real.sqrt N with hs
  have hs2 : s ^ 2 = 1 / N := by
    rw [hs, div_pow, Real.sq_sqrt hNpos.le]; ring
  have hpt : ∀ ω, (N : ℝ) ^ m * (Z ω / N) ^ (2 * m) ≤
      ((2 * m).factorial : ℝ) * (Real.exp (s * Z ω) + Real.exp (-s * Z ω)) := by
    intro ω
    have := b4c_pow_le m (s * Z ω)
    have heq : (s * Z ω) ^ (2 * m) = (N : ℝ) ^ m * (Z ω / N) ^ (2 * m) := by
      calc (s * Z ω) ^ (2 * m) = ((s * Z ω) ^ 2) ^ m := pow_mul _ _ _
        _ = ((N : ℝ) * (Z ω / N) ^ 2) ^ m := by
          congr 1
          rw [mul_pow, hs2]
          field_simp
        _ = (N : ℝ) ^ m * ((Z ω / N) ^ 2) ^ m := mul_pow _ _ _
        _ = (N : ℝ) ^ m * (Z ω / N) ^ (2 * m) := by rw [pow_mul]
    rw [heq] at this
    simpa [neg_mul] using this
  have hint1 : Integrable (fun ω => Real.exp (s * Z ω)) ν := h3.integrable_exp_mul s
  have hint2 : Integrable (fun ω => Real.exp (-s * Z ω)) ν := h3.integrable_exp_mul (-s)
  have hg : Integrable (fun ω => ((2 * m).factorial : ℝ) *
      (Real.exp (s * Z ω) + Real.exp (-s * Z ω))) ν := (hint1.add hint2).const_mul _
  have hfmeas : Measurable fun ω => (N : ℝ) ^ m * (Z ω / N) ^ (2 * m) :=
    measurable_const.mul ((hZmeas.div_const _).pow_const _)
  have hfnn : ∀ ω, 0 ≤ (N : ℝ) ^ m * (Z ω / N) ^ (2 * m) := fun ω => by
    have : 0 ≤ (Z ω / N) ^ (2 * m) := by rw [pow_mul]; positivity
    positivity
  have hf : Integrable (fun ω => (N : ℝ) ^ m * (Z ω / N) ^ (2 * m)) ν :=
    hg.mono' hfmeas.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (hfnn ω)]; exact hpt ω)
  have hmono := integral_mono hf hg hpt
  rw [integral_const_mul, integral_const_mul, integral_add hint1 hint2] at hmono
  have hm1 : ∫ ω, Real.exp (s * Z ω) ∂ν ≤ Real.exp ((κ : ℝ) / 2) := by
    have := h3.mgf_le s
    unfold mgf at this
    refine this.trans (le_of_eq ?_)
    rw [hcoe, hs2]; congr 1; field_simp
  have hm2 : ∫ ω, Real.exp (-s * Z ω) ∂ν ≤ Real.exp ((κ : ℝ) / 2) := by
    have := h3.mgf_le (-s)
    unfold mgf at this
    refine this.trans (le_of_eq ?_)
    rw [hcoe, neg_sq, hs2]; congr 1; field_simp
  have hfac : (0 : ℝ) < ((2 * m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hNm : (0 : ℝ) < (N : ℝ) ^ m := by positivity
  rw [le_div_iff₀ hNm, mul_comm]
  calc (N : ℝ) ^ m * ∫ ω, (Z ω / N) ^ (2 * m) ∂ν
      ≤ ((2 * m).factorial : ℝ) * (∫ ω, Real.exp (s * Z ω) ∂ν + ∫ ω, Real.exp (-s * Z ω) ∂ν) := by
        exact hmono
    _ ≤ ((2 * m).factorial : ℝ) * (Real.exp ((κ : ℝ) / 2) + Real.exp ((κ : ℝ) / 2)) := by
        gcongr
    _ = 2 * ((2 * m).factorial : ℝ) * Real.exp ((κ : ℝ) / 2) := by ring


theorem sed_B4c_iid_moment_proof {d : ℕ} (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (M : ℝ) (m : ℕ) :
    ∃ C : ℝ, ∀ u : Torus d → ℝ, Measurable u → (∀ x, |u x| ≤ M) → ∀ N : ℕ, 1 ≤ N →
      ∫ X : Config d N, (pair (empirical X) u - pair μ u) ^ (2 * m)
        ∂(Measure.pi fun _ : Fin N => μ) ≤ C / (N : ℝ) ^ m :=
  b4c_main μ M m


end HRS.MC.SEdge.B4c
