import HRS.MS.S21L_G11H

/-!
# S21L G11 -- `r26t3_vector_wick` (R26-T3.G11): Hilbert-valued Wick isometry for a moving covariance

Contract of packet R26-T3.G11 (`origin/pro/fine-breakdown`, `docs/breakdown/R26-T3.packets.json`), with the three skeleton fixes of
the S21G11 handoff: no `ContDiff` in the scoped opens (it makes `ω` a token), the binder `(f g : Euc d → ℝ) (c : ℝ)` of `hlinear`
is typed, and `import HRS.Whole.Round2` (via the imports).  The statement is otherwise verbatim.

Route: replace `ξ` by a measurable version, bundle the hypotheses on `η` (`S21LEta`, G11A); replace `H` by a measurable
symmetric representative `K`; if no orthonormal basis `a0` exists take `Q = 0`, otherwise `Q = ½ lim ∑ (z_i z_j - E) • V_ij`
(G11G/H) with `V_ij = ∬ e_i e_j K`; basis independence is G11D.  Helpers carry the prefix `s21l_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.deprecated false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS HRS.MC.E213U13 HRS.MS.R2Chaos HRS.Whole

section Transfer

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem s21l_first_congr {ξ ξ' : ℕ → Ω → ℝ} (hae : ∀ i, ξ i =ᵐ[P] ξ' i) {q : ℝ} {J : Ω → ℝ}
    (h : InFirstChaos P ξ q J) : InFirstChaos P ξ' q J := by
  obtain ⟨hJ, n, c, hlim⟩ := h
  refine ⟨hJ, n, c, hlim.congr fun m => lintegral_congr_ae ?_⟩
  filter_upwards [ae_all_iff.2 hae] with ω hω
  simp only [hω]

theorem s21l_second_congr {ξ ξ' : ℕ → Ω → ℝ} (hae : ∀ i, ξ i =ᵐ[P] ξ' i) {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] {q : ℝ} {D : Ω → B} (h : InSecondChaos P ξ q D) : InSecondChaos P ξ' q D := by
  obtain ⟨hD, n, c, hlim⟩ := h
  refine ⟨hD, n, c, hlim.congr fun m => lintegral_congr_ae ?_⟩
  filter_upwards [ae_all_iff.2 hae] with ω hω
  simp only [hω]

end Transfer

theorem s21l_coeff_prod {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℕ → Euc d → ℝ}
    (hat : ∀ i, IsR2Test (a i)) {k : Euc d → Euc d → ℝ}
    (hk : Integrable (fun z : Euc d × Euc d => k z.1 z.2) (μ.prod μ)) (i j : ℕ) :
    r2WickCoeff μ a k i j =
      ∫ q, k q.1 q.2 * (Whole.projMean μ (a i) q.1 * Whole.projMean μ (a j) q.2) ∂(μ.prod μ) := by
  obtain ⟨C, hC⟩ := s94E2_bounded (μ := μ) hat (i, j)
  have hint : Integrable (fun q : Euc d × Euc d => k q.1 q.2 * s94E2 μ a (i, j) q) (μ.prod μ) :=
    hk.mul_bdd (s94E2_measurable hat (i, j)).aestronglyMeasurable (c := C)
      (ae_of_all _ fun q => by simpa using hC q)
  have h1 := integral_prod _ hint
  unfold r2WickCoeff
  rw [show (∫ q, k q.1 q.2 * (Whole.projMean μ (a i) q.1 * Whole.projMean μ (a j) q.2) ∂(μ.prod μ)) =
    ∫ q, k q.1 q.2 * s94E2 μ a (i, j) q ∂(μ.prod μ) from rfl, h1]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [s94E2]
  ring

theorem r26t3_vector_wick {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : HRS.IsStdGaussianSeq P ξ) (η : (Euc d → ℝ) → Ω → ℝ)
    (hη : ∀ f, MemLp f 2 μ → HRS.InFirstChaos P ξ 2 (η f))
    (hlinear : ∀ (f g : Euc d → ℝ) (c : ℝ), MemLp f 2 μ → MemLp g 2 μ →
      (η (f+c•g))=ᵐ[P] (η f+c•η g))
    (hconst : η (fun _ => 1)=ᵐ[P] 0)
    (Λ : ℝ) (hΛ : 0≤Λ) (hcov : ∀ f, MemLp f 2 μ → ∫ ω, η f ω^2 ∂P≤Λ*∫ x, f x^2 ∂μ)
    (H : Euc d → Euc d → B) (hH : MemLp (fun z : Euc d × Euc d => H z.1 z.2) 2 (μ.prod μ))
    (hsym : ∀ x y, H x y=H y x) :
    ∃ Q : Ω → B, AEStronglyMeasurable Q P ∧ HRS.InSecondChaos P ξ 3 Q ∧
      (∀ ℓ : B →L[ℝ] ℝ, ∀ a, IsR2ZeroMeanONB μ a →
        IsR2WickChaos P μ a (fun j => η (a j)) (r2CenterKernel μ (fun x y => ℓ (H x y)))
          (fun ω => 2*ℓ (Q ω))) ∧
      ∫ ω, ‖Q ω‖^2 ∂P≤(Λ^2/2)*∫ z : Euc d × Euc d, ‖H z.1 z.2‖^2 ∂(μ.prod μ) := by
  classical
  by_cases hex : ∃ a, IsR2ZeroMeanONB μ a
  swap
  · refine ⟨fun _ => 0, aestronglyMeasurable_const, ?_, fun ℓ a hb => absurd ⟨a, hb⟩ hex, ?_⟩
    · refine ⟨aestronglyMeasurable_const, fun _ => 0, fun _ _ _ => 0, ?_⟩
      simp
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
      exact mul_nonneg (by positivity) (integral_nonneg fun z => sq_nonneg _)
  obtain ⟨a0, hb0⟩ := hex
  obtain ⟨hat0, hon0, hcomp0⟩ := hb0
  -- a measurable version of the Gaussian sequence
  set ξ' : ℕ → Ω → ℝ := fun i => (hξ.aemeasurable i).mk (ξ i) with hξ'
  have hm' : ∀ i, Measurable (ξ' i) := fun i => (hξ.aemeasurable i).measurable_mk
  have hae : ∀ i, ξ i =ᵐ[P] ξ' i := fun i => (hξ.aemeasurable i).ae_eq_mk
  have hξ'G : HRS.IsStdGaussianSeq P ξ' := by
    refine ⟨(ProbabilityTheory.iIndepFun_congr hae).1 hξ.1, fun i => ?_⟩
    have h1 : P.map (ξ i) = gaussianReal 0 1 := hξ.2 i
    show P.map (ξ' i) = gaussianReal 0 1
    rw [← Measure.map_congr (hae i)]
    exact h1
  have hfirst' : ∀ f, MemLp f 2 μ → HRS.InFirstChaos P ξ' 2 (η f) := fun f hf => s21l_first_congr hae (hη f hf)
  have hEta : S21LEta μ P η Λ := s21l_eta_of_contract hξ'G hm' hfirst' hlinear hconst hcov
  -- a measurable symmetric representative `K` of `H`
  have hHm := hH.aestronglyMeasurable
  set G : Euc d × Euc d → B := hHm.mk (fun z : Euc d × Euc d => H z.1 z.2) with hG
  have hGm : Measurable G := hHm.stronglyMeasurable_mk.measurable
  have e1 : (fun z : Euc d × Euc d => H z.1 z.2) =ᵐ[μ.prod μ] G := hHm.ae_eq_mk
  set K : Euc d → Euc d → B := fun x y => (1 / 2 : ℝ) • (G (x, y) + G (y, x)) with hK
  have hKm : Measurable fun q : Euc d × Euc d => K q.1 q.2 :=
    Measurable.const_smul (hGm.add (hGm.comp measurable_swap)) _
  have hKs : ∀ x y, K x y = K y x := fun x y => by simp only [hK, add_comm]
  have e2 : (fun z : Euc d × Euc d => H z.2 z.1) =ᵐ[μ.prod μ] fun z => G (z.2, z.1) :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae_eq_comp e1
  have hKH : (fun q : Euc d × Euc d => K q.1 q.2) =ᵐ[μ.prod μ] fun q => H q.1 q.2 := by
    filter_upwards [e1, e2] with q h1 h2
    simp only [hK]
    rw [← h1, ← h2, hsym q.2 q.1, ← two_smul ℝ (H q.1 q.2), smul_smul]
    norm_num
  have hK2 : MemLp (fun q : Euc d × Euc d => K q.1 q.2) 2 (μ.prod μ) := hH.ae_eq hKH.symm
  -- the coefficient data
  have hVc := s21l_V_coord (μ := μ) hat0 hKm hK2
  have hVs : ∀ i j, s21l_V μ a0 K i j = s21l_V μ a0 K j i := fun i j => s21l_V_symm hKs i j
  have hM := s21l_V_bessel hat0 hon0 hKm hK2
  obtain ⟨Q, hQm, hQ2c, hQwick, hQb⟩ := s21l_core hξ'G hm' hEta hΛ hfirst' ⟨hat0, hon0, hcomp0⟩ hKm hKs hK2
    (s21l_V μ a0 K) hVc hVs hM
  refine ⟨Q, hQm, s21l_second_congr (fun i => (hae i).symm) hQ2c, ?_, ?_⟩
  · intro ℓ a hb
    have hw := hQwick ℓ a hb
    obtain ⟨hat, -, -⟩ := hb
    have hkH : Integrable (fun z : Euc d × Euc d => ℓ (H z.1 z.2)) (μ.prod μ) :=
      (ℓ.comp_memLp' hH).integrable one_le_two
    have hkK : Integrable (fun z : Euc d × Euc d => ℓ (K z.1 z.2)) (μ.prod μ) :=
      (ℓ.comp_memLp' hK2).integrable one_le_two
    have hcoef : ∀ i j, r2WickCoeff μ a (r2CenterKernel μ (fun x y => ℓ (H x y))) i j =
        r2WickCoeff μ a (r2CenterKernel μ (fun x y => ℓ (K x y))) i j := fun i j => by
      rw [s21l_coeff_center hat hkH, s21l_coeff_center hat hkK, s21l_coeff_prod hat hkH,
        s21l_coeff_prod hat hkK]
      refine integral_congr_ae ?_
      filter_upwards [hKH] with q hq
      rw [hq]
    unfold IsR2WickChaos at hw ⊢
    simp only [hcoef]
    exact hw
  · have : ∫ z : Euc d × Euc d, ‖K z.1 z.2‖ ^ 2 ∂(μ.prod μ) = ∫ z : Euc d × Euc d, ‖H z.1 z.2‖ ^ 2 ∂(μ.prod μ) := by
      refine integral_congr_ae ?_
      filter_upwards [hKH] with q hq
      rw [hq]
    rw [← this]
    exact hQb

end HRS.MS.R26T3
