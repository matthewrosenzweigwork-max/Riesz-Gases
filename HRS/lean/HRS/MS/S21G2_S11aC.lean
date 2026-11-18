import HRS.MS.S21G2_S11aB

/-!
# S21G2 S11a (part C) -- helpers: Parseval sequence, Gaussian vectors from 1-d laws, first chaos (R26-T3.S11a)

* `s21g2_s11a_parseval`: every separable real Hilbert space has an `ℕ`-indexed sequence (zero-padded Hilbert basis) with
  `∑ ⟪e_n,h⟫⟪e_n,h'⟫ = ⟪h,h'⟫` (finite or empty bases allowed).
* `s21g2_s11a_gauss_of_laws`: a random vector in `ℝ^n` all of whose linear functionals are centred Gaussian has a centred
  Gaussian law.
* `s21g2_s11a_firstChaos`: `L²` convergence of the partial sums gives `HRS.InFirstChaos P ξ 2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s21g2_s11a_parseval (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] :
    ∃ e : ℕ → H, ∀ h h' : H, HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h') (inner ℝ h h') := by
  classical
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ H
  haveI : Countable w := HRS.HilbertCLTAux.countable_of_orthonormal b.orthonormal
  obtain ⟨τ, hτ⟩ := Countable.exists_injective_nat w
  let e : ℕ → H := fun n => if hn : ∃ i, τ i = n then b hn.choose else 0
  have he : ∀ i, e (τ i) = b i := fun i => by
    have hn : ∃ j, τ j = τ i := ⟨i, rfl⟩
    simp only [e, dif_pos hn]
    exact congrArg b (hτ hn.choose_spec)
  have he0 : ∀ n, n ∉ Set.range τ → e n = 0 := fun n hn => by
    have : ¬ ∃ i, τ i = n := fun ⟨i, hi⟩ => hn ⟨i, hi⟩
    simp only [e, dif_neg this]
  refine ⟨e, fun h h' => ?_⟩
  have hs := b.hasSum_inner_mul_inner h h'
  refine (hτ.hasSum_iff (f := fun n => inner ℝ (e n) h * inner ℝ (e n) h') (fun n hn => ?_)).1 ?_
  · simp [he0 n hn]
  · convert hs using 1
    ext i
    simp only [Function.comp, he, real_inner_comm h (b i)]

theorem s21g2_s11a_gauss_of_laws {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {Z : Ω → (Fin n → ℝ)} (hZ : AEMeasurable Z P)
    (h : ∀ c : Fin n → ℝ, ∃ v : ℝ≥0, P.map (fun ω => ∑ i, c i * Z ω i) = gaussianReal 0 v) :
    HRS.IsCenteredGaussian (P.map Z) := by
  classical
  have hmap : ∀ L : StrongDual ℝ (Fin n → ℝ), ∃ v : ℝ≥0, (P.map Z).map L = gaussianReal 0 v := fun L => by
    obtain ⟨v, hv⟩ := h fun i => L (fun j => if i = j then 1 else 0)
    refine ⟨v, ?_⟩
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hZ, ← hv]
    congr 1
    funext ω
    have := L.toLinearMap.pi_apply_eq_sum_univ (Z ω)
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    simp only [Function.comp, this, mul_comm]
  have hmean : ∀ L : StrongDual ℝ (Fin n → ℝ), ∫ z, L z ∂(P.map Z) = 0 := fun L => by
    obtain ⟨v, hv⟩ := hmap L
    have := integral_map (μ := P.map Z) (φ := L) (f := fun y : ℝ => y) L.continuous.measurable.aemeasurable
      aestronglyMeasurable_id
    rw [hv, integral_id_gaussianReal] at this
    exact this.symm
  refine ⟨⟨fun L => ?_⟩, hmean⟩
  obtain ⟨v, hv⟩ := hmap L
  have hvar : variance (fun z => L z) (P.map Z) = v := by
    have := variance_map (μ := P.map Z) (Y := L) (X := fun y : ℝ => y)
      (by rw [hv]; exact aemeasurable_id) L.continuous.measurable.aemeasurable
    rw [hv, variance_fun_id_gaussianReal] at this
    exact this.symm
  rw [hmean L, hvar, hv, Real.toNNReal_coe]

theorem s21g2_s11a_firstChaos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : ∀ i, MemLp (ξ i) 2 P) (a : ℕ → ℝ) {F : Ω → ℝ} (hF : MemLp F 2 P)
    (hlim : Tendsto (fun m => ∫ ω, (∑ i ∈ Finset.range m, a i * ξ i ω - F ω) ^ 2 ∂P) atTop (𝓝 0)) :
    HRS.InFirstChaos P ξ 2 F := by
  refine ⟨hF.aestronglyMeasurable, id, fun _ i => a i, ?_⟩
  have hpt : ∀ (x : ℝ), ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg x) (by norm_num),
      Real.rpow_two, sq_abs]
  have hmem : ∀ m : ℕ, MemLp (fun ω => ∑ i ∈ Finset.range m, a i * ξ i ω - F ω) 2 P := fun m =>
    (memLp_finsetSum (f := fun i ω => a i * ξ i ω) (Finset.range m) fun i _ => (hξ i).const_mul (a i)).sub hF
  have hE : ∀ m : ℕ, ∫⁻ ω, ‖(∑ i ∈ Finset.range (id m), ξ i ω • a i) - F ω‖ₑ ^ (2 : ℝ) ∂P =
      ENNReal.ofReal (∫ ω, (∑ i ∈ Finset.range m, a i * ξ i ω - F ω) ^ 2 ∂P) := fun m => by
    rw [ofReal_integral_eq_lintegral_ofReal (hmem m).integrable_sq (ae_of_all _ fun _ => sq_nonneg _)]
    refine lintegral_congr fun ω => ?_
    rw [hpt]
    simp only [id, smul_eq_mul, mul_comm]
  simp_rw [hE]
  simpa using ENNReal.tendsto_ofReal hlim

end HRS.MS.R26T3
