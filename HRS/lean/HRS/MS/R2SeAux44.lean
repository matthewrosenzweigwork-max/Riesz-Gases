import HRS.MS.R2SeAux43

/-!
# S9.9 `r2_static_edgeworth`, packet 44: the Edgeworth expansion in `ℓ²`

Worker S99, namespace `S99`.  `s99_main_l2`: for `W_N = featureVec φ ν` and the centered Gaussian `G` on `ℓ²`, uniformly over
`Φ ∈ C_b^5(ℓ²)` with `‖D^iΦ‖ ≤ 1`: `√N (E Φ(W_N) - E Φ(G)) → (1/6) ∫_G ∫_μ D³Φ(z)[ℓ_x,ℓ_x,ℓ_x]`.
Stein solution (`HRS.stein_bounds`, `stein_equation`, `stein_third_derivative`), the decomposition `s99_D1`, the
uniform limits `s99_ULimA`, `s99_ULimB`, the identification `s99_limit_ident` and the series `s99_third_series`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section Main

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

set_option maxHeartbeats 4000000 in
theorem s99_main_l2 {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (φ i) (φ j))) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 2 ≤ N → ∀ {Φ : SeqL2 → ℝ}, ContDiff ℝ 5 Φ →
      (∀ i : ℕ, i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i Φ z‖ ≤ 1) →
      |Real.sqrt N * ((∫ X, Φ (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N)) -
          ∫ z, Φ z ∂G) -
        (1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ z ![ellv d s a β γ φ x, ellv d s a β γ φ x,
          ellv d s a β γ φ x] ∂(thermalMeasure d s a β) ∂G| ≤ ε := by
  have hAB := (s99_ULimA hd hs0 hs ha hβ hγ hT hS hφ F hG).add (s99_ULimB hd hs0 hs ha hβ hγ hT hS hφ F hG)
  intro ε hε
  obtain ⟨N0, hN0⟩ := hAB ε hε
  refine ⟨max N0 2, fun N hN hN2 Φ hΦ hb => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0r
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN2).prob
  haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
  have hMem : HRS.MemCb 5 Φ := ⟨hΦ, fun j hj => ⟨1, by rintro _ ⟨x, rfl⟩; exact hb j hj x⟩⟩
  have hGauss : HRS.IsCenteredGaussian (HRS.law G (id : SeqL2 → SeqL2)) := by
    have : HRS.law G (id : SeqL2 → SeqL2) = G := by unfold HRS.law; exact Measure.map_id
    rw [this]; exact hG.1
  obtain ⟨-, hf5, hfb⟩ := HRS.stein_bounds G (id : SeqL2 → SeqL2) aemeasurable_id hGauss Φ hMem
  set f := HRS.steinSolution G (id : SeqL2 → SeqL2) Φ with hfdef
  have hf : SteinCl f := ⟨hf5, fun i hi1 hi5 z => by
    refine (hfb i hi1 hi5 z).trans ?_
    have hsup : (⨆ y, ‖iteratedFDeriv ℝ i Φ y‖) ≤ 1 := ciSup_le fun y => hb i hi5 y
    have hi : ((i : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hi1)
    have h0 : 0 ≤ ⨆ y, ‖iteratedFDeriv ℝ i Φ y‖ := Real.iSup_nonneg fun _ => norm_nonneg _
    calc ((i : ℝ))⁻¹ * ⨆ y, ‖iteratedFDeriv ℝ i Φ y‖ ≤ 1 * 1 :=
          mul_le_mul hi hsup h0 zero_le_one
      _ = 1 := one_mul 1⟩
  have hst : ∀ x, ∫ z, iteratedFDeriv ℝ 2 f x ![z, z] ∂G - fderiv ℝ f x x = Φ x - ∫ z, Φ z ∂G := fun x =>
    HRS.stein_equation G (id : SeqL2 → SeqL2) aemeasurable_id hGauss Φ hMem x
  have hΦb : ∀ z, |Φ z| ≤ 1 := fun z => by
    have := hb 0 (by norm_num) z
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hD1 := s99_D1 hd hs0 hs ha hβ hγ hT hS hφ F hG hΦ.continuous hΦb hf hst hN2
  -- the left-hand side
  have hL : Real.sqrt N * ((∫ X, Φ (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N)) -
      ∫ z, Φ z ∂G) = (∑' p : ℕ × ℕ, Aterm d s a β γ F N f p) +
        ∑' j, Bterm d s a β γ φ N (commutatorKernel d s (gradient (F.χ j))) (pd f j) := by
    rw [hD1, mul_add, ← tsum_mul_left, ← tsum_mul_left]
    congr 1
    refine tsum_congr fun j => ?_
    unfold Bterm
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show Real.sqrt N * (Bq d s a β γ N (F.χ j) X / Real.sqrt N * _) = Bh d s a β γ N _ X * _
    rw [Bq_eq_Bh]
    field_simp
  -- the right-hand side
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.of_le (by norm_num)
  have hser := s99_third_series hd hs0 hs ha hβ hγ hT hS hφ F (G := G) hΦ3 (hb 3 (by norm_num))
  have hthird : ∀ j k m, ∫ z, iteratedFDeriv ℝ 3 Φ z ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] ∂G =
      -3 * T3 G f j k m := by
    intro j k m
    have h1 := HRS.stein_third_derivative G (id : SeqL2 → SeqL2) aemeasurable_id hGauss Φ hMem
      ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)]
    have h2 : ∫ z, iteratedFDeriv ℝ 3 f z ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] ∂G =
        T3 G f j k m := by
      unfold T3
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      exact s99_third_apply (hf5.of_le (by norm_num)) z j k m
    simp only [id] at h1
    rw [h2] at h1
    linarith
  have hlim := s99_limit_ident (G := G) hd hs0 hs ha hβ hγ hT hS hφ F hf
  have hR : (1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ z ![ellv d s a β γ φ x, ellv d s a β γ φ x,
          ellv d s a β γ φ x] ∂(thermalMeasure d s a β) ∂G =
      (∑' p : ℕ × ℕ, Alim d s a β γ F G f p) + (∑' j, (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ
        (commutatorKernel d s (gradient (F.χ j))) l q * ∫ z, pd (pd (pd f j) l) q z ∂G) := by
    rw [hser, hlim]
    simp_rw [hthird]
    have : ∀ j k m : ℕ, kap3 d s a β γ φ j k m * (-3 * T3 G f j k m) =
        -3 * (kap3 d s a β γ φ j k m * T3 G f j k m) := fun j k m => by ring
    simp_rw [this, tsum_mul_left]
    ring
  rw [hL, hR]
  have := hN0 N ((le_max_left N0 2).trans hN) f hf
  simp only [hN2, ite_true] at this
  exact this

end Main

end S99

end
