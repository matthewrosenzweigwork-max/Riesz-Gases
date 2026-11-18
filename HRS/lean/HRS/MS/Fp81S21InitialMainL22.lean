import HRS.MS.Fp81S21InitialMainL2

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45 S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-- The actual-law `D1) identity, after multiplication by `√N), is precisely the
finite-`N) sum of the actual `Aterm) and `Bterm). -/
theorem fp81s21_initial_D1_scaled
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ (φ i) (φ j)))
    {Φ : SeqL2 → ℝ} (hΦc : Continuous Φ)
    (hΦb : ∀ z, |Φ z| ≤ 1)
    {f : SeqL2 → ℝ} (hf : SteinCl f)
    (hst : ∀ x, ∫ z, iteratedFDeriv ℝ 2 f x ![z, z] ∂G - fderiv ℝ f x x =
      Φ x - ∫ z, Φ z ∂G)
    {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt N *
        ((∫ X, Φ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
          ∫ z, Φ z ∂G) =
      (∑' q : ℕ × ℕ, fp81s21_initial_Aterm F N f q) +
        ∑' j, fp81s21_initial_Bterm R φ N
          (commutatorKernel p.d p.s (gradient (F.χ j))) (S99.pd f j) := by
  have hGcf : IsCenteredGaussianSeq G
      (fun i j => fp81s21_initialCf R (φ i) (φ j)) := by
    simpa [fp81s21_initialCf] using hG
  have hD1 := fp81s21_initial_D1 E hγ hφ F hGcf hΦc
    (CΦ := 1) hΦb hf hst hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  rw [hD1, mul_add, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  · refine tsum_congr fun j : ℕ => ?_
    unfold fp81s21_initial_Bterm
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [fp81s21_initialBq]
    field_simp [hsqN.ne']

/-- The actual initial-law ℓ² Edgeworth expansion. The cutoff `N₀) is selected
before the C⁵ test function, uniformly over all tests whose derivatives of orders zero
through five have norm at most one. -/
theorem fp81s21_initial_main_l2
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ (φ i) (φ j))) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 2 ≤ N →
      ∀ {Φ : SeqL2 → ℝ}, ContDiff ℝ 5 Φ →
        (∀ i : ℕ, i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i Φ z‖ ≤ 1) →
        |Real.sqrt N *
            ((∫ X, Φ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
              ∫ z, Φ z ∂G) -
          (1 / 6) * ∫ z, ∫ x,
            iteratedFDeriv ℝ 3 Φ z
              ![fp81s21_initial_ellv R φ x, fp81s21_initial_ellv R φ x,
                fp81s21_initial_ellv R φ x]
            ∂(r26t3_mu R 0) ∂G| ≤ ε := by
  have hAB :=
    (fp81s21_initial_ULimA hδ hδh R E hγ hφ F hG).add
      (fp81s21_initial_ULimB hδ hδh R E hγ hφ F hG)
  intro ε hε
  obtain ⟨Nlim, hNlim⟩ := hAB ε hε
  refine ⟨max Nlim 2, fun N hN hN2 Φ hΦ hb => ?_⟩
  obtain ⟨f, hf, hst, hthird⟩ :=
    fp81s21_initial_stein_package R hG hΦ hb
  have hΦb : ∀ z, |Φ z| ≤ 1 := fun z => by
    have h := hb 0 (by norm_num) z
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have hL := fp81s21_initial_D1_scaled E hγ hφ F hG
    hΦ.continuous hΦb hf hst hN2
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.of_le (by norm_num)
  have hser := fp81s21_initial_third_series hδ hδh R E hγ hφ F
    (G := G) hΦ3 (hb 3 (by norm_num))
  have hthirdT : ∀ j k m,
      ∫ z, iteratedFDeriv ℝ 3 Φ z
          ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] ∂G =
        -3 * S99.T3 G f j k m := by
    intro j k m
    let v : Fin 3 → SeqL2 :=
      ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)]
    have h3 := hthird v
    have h2 :
        ∫ z, iteratedFDeriv ℝ 3 f z
            ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] ∂G =
          S99.T3 G f j k m := by
      unfold S99.T3
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      exact s99_third_apply (hf.1.of_le (by norm_num)) z j k m
    rw [h2] at h3
    exact h3
  have hlim := fp81s21_initial_limit_ident (G := G) hδ hδh R E hγ hφ F hf
  have hR :
      (1 / 6) * ∫ z, ∫ x,
          iteratedFDeriv ℝ 3 Φ z
            ![fp81s21_initial_ellv R φ x, fp81s21_initial_ellv R φ x,
              fp81s21_initial_ellv R φ x] ∂(r26t3_mu R 0) ∂G =
        (∑' q : ℕ × ℕ, fp81s21_initial_Alim F G f q) +
          (∑' j, (1 / 2) * ∑' l, ∑' q,
            fp81s21_initial_Qk R φ
              (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
              ∫ z, S99.pd (S99.pd (S99.pd f j) l) q z ∂G) := by
    rw [hser]
    have hT3pd : ∀ j l q,
        (∫ z, S99.pd (S99.pd (S99.pd f j) l) q z ∂G) =
          S99.T3 G f j l q := fun _ _ _ => rfl
    simp_rw [hT3pd]
    rw [hlim]
    simp_rw [hthirdT]
    have hmul : ∀ j k m : ℕ,
        fp81s21_initial_kap3 R φ j k m * (-3 * S99.T3 G f j k m) =
          -3 * (fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m) :=
      fun j k m => by ring
    simp_rw [hmul, tsum_mul_left]
    ring
  rw [hL, hR]
  have h := hNlim N ((le_max_left Nlim 2).trans hN) f hf
  simp only [hN2, ite_true] at h
  exact h

#print axioms fp81s21_initial_D1_scaled
#print axioms fp81s21_initial_main_l2

end HRS.Fp81.S21

end
