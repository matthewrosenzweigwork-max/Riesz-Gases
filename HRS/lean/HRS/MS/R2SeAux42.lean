import HRS.MS.R2SeAux41

/-!
# S9.9 `r2_static_edgeworth`, packet 42: the cubic form as a triple series

Worker S99, namespace `S99`.  For `ℓ_x = (a_j(x))_j ∈ ℓ²` and a continuous trilinear form `T`,
`T[ℓ,ℓ,ℓ] = ∑_j ∑_k ∑_m ℓ_j ℓ_k ℓ_m T[e_m,e_k,e_j]`; integrating (`s99_int_tsum3`) in `x` against `μ` and in `z` against `G`:
`∫_G ∫_μ D³Φ'(z)[ℓ_x,ℓ_x,ℓ_x] = ∑_{jkm} κ_{jkm} ∫_G D³Φ'(z)[e_m,e_k,e_j]`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_clm_expand (L : SeqL2 →L[ℝ] ℝ) (x : SeqL2) :
    L x = ∑' j, SeqL2.coord x j * L (s45_e1 j (1 : ℝ)) := by
  have h := (s99_coord_hasSum x).mapL L
  rw [← h.tsum_eq]
  refine tsum_congr fun j => ?_
  rw [map_smul, smul_eq_mul]

theorem s99_third_expand (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => SeqL2) ℝ) (ℓ : SeqL2) :
    T ![ℓ, ℓ, ℓ] = ∑' j, ∑' k, ∑' m, SeqL2.coord ℓ j * SeqL2.coord ℓ k * SeqL2.coord ℓ m *
      T ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] := by
  have h2 : ∀ w : SeqL2, T.toContinuousLinearMap ![ℓ, ℓ, ℓ] 2 w = T ![ℓ, ℓ, w] := fun w => by
    simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    ext i; fin_cases i <;> simp
  have h1 : ∀ (u v : SeqL2) (w : SeqL2), T.toContinuousLinearMap ![ℓ, v, u] 1 w = T ![ℓ, w, u] := fun u v w => by
    simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    ext i; fin_cases i <;> simp
  have h0 : ∀ (u v w x : SeqL2), T.toContinuousLinearMap ![u, v, w] 0 x = T ![x, v, w] := fun u v w x => by
    simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    ext i; fin_cases i <;> simp
  have s2 := s99_clm_expand (T.toContinuousLinearMap ![ℓ, ℓ, ℓ] 2) ℓ
  simp only [h2] at s2
  have e2 : ∀ j : ℕ, T ![ℓ, ℓ, s45_e1 j (1 : ℝ)] =
      ∑' k, ∑' m, SeqL2.coord ℓ k * SeqL2.coord ℓ m * T ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] := by
    intro j
    have s1 := s99_clm_expand (T.toContinuousLinearMap ![ℓ, ℓ, s45_e1 j (1 : ℝ)] 1) ℓ
    simp only [h1] at s1
    rw [s1]
    refine tsum_congr fun k => ?_
    have s0 := s99_clm_expand (T.toContinuousLinearMap ![ℓ, s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] 0) ℓ
    simp only [h0] at s0
    rw [s0, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    ring
  rw [s2]
  refine tsum_congr fun j => ?_
  rw [e2 j, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  ring

theorem s99_meas_tsum {α : Type*} [MeasurableSpace α] {g : ℕ → α → ℝ} (hm : ∀ m, Measurable (g m))
    (hs : ∀ x, Summable fun m => g m x) : Measurable fun x => ∑' m, g m x := by
  refine measurable_of_tendsto_metrizable (f := fun n x => ∑ m ∈ Finset.range n, g m x) (fun n => ?_) ?_
  · exact Finset.measurable_sum _ fun m _ => hm m
  · refine tendsto_pi_nhds.2 fun x => ?_
    exact (hs x).hasSum.tendsto_sum_nat

theorem s99_int_tsum1 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {g : ℕ → α → ℝ} {M : ℕ → ℝ} (hM : Summable M) (hm : ∀ m, Measurable (g m))
    (hb : ∀ m x, |g m x| ≤ M m) : ∫ x, ∑' m, g m x ∂μ = ∑' m, ∫ x, g m x ∂μ :=
  (s99_integral_tsum hM (fun m => (hm m).aestronglyMeasurable) hb).symm

theorem s99_int_tsum3 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (g : ℕ → ℕ → ℕ → α → ℝ) {b : ℕ → ℝ} (hbs : Summable b) (hb0 : ∀ j, 0 ≤ b j)
    (hg : ∀ j k m x, |g j k m x| ≤ b j * b k * b m) (hm : ∀ j k m, Measurable (g j k m)) :
    ∫ x, ∑' j, ∑' k, ∑' m, g j k m x ∂μ = ∑' j, ∑' k, ∑' m, ∫ x, g j k m x ∂μ := by
  set S : ℝ := ∑' i, b i with hS
  have hsm : ∀ j k x, Summable fun m => g j k m x := fun j k x =>
    Summable.of_norm_bounded (hbs.mul_left (b j * b k)) (fun m => by
      rw [Real.norm_eq_abs]; exact (hg j k m x).trans (le_of_eq (by ring)))
  have hbm : ∀ j k x, |∑' m, g j k m x| ≤ b j * b k * S := fun j k x => by
    have hh : HasSum (fun m => b j * b k * b m) (b j * b k * S) := hbs.hasSum.mul_left _
    have := tsum_of_norm_bounded hh (f := fun m => g j k m x) (fun m => by
      rw [Real.norm_eq_abs]; exact hg j k m x)
    rwa [Real.norm_eq_abs] at this
  have hmm : ∀ j k, Measurable fun x => ∑' m, g j k m x := fun j k => s99_meas_tsum (hm j k) (hsm j k)
  have hsk : ∀ j x, Summable fun k => ∑' m, g j k m x := fun j x =>
    Summable.of_norm_bounded (hbs.mul_left (b j * S)) (fun k => by
      rw [Real.norm_eq_abs]; exact (hbm j k x).trans (le_of_eq (by ring)))
  have hbk : ∀ j x, |∑' k, ∑' m, g j k m x| ≤ b j * S * S := fun j x => by
    have hh : HasSum (fun k => b j * S * b k) (b j * S * S) := hbs.hasSum.mul_left _
    have := tsum_of_norm_bounded hh (f := fun k => ∑' m, g j k m x) (fun k => by
      rw [Real.norm_eq_abs]; exact (hbm j k x).trans (le_of_eq (by ring)))
    rwa [Real.norm_eq_abs] at this
  have hmk : ∀ j, Measurable fun x => ∑' k, ∑' m, g j k m x := fun j => s99_meas_tsum (hmm j) (hsk j)
  rw [s99_int_tsum1 (M := fun j => b j * S * S) ((hbs.mul_right S).mul_right S) hmk (fun j x => hbk j x)]
  refine tsum_congr fun j => ?_
  rw [s99_int_tsum1 (M := fun k => b j * b k * S) ((hbs.mul_left (b j)).mul_right S) (hmm j)
    (fun k x => hbm j k x)]
  refine tsum_congr fun k => ?_
  exact s99_int_tsum1 (M := fun m => b j * b k * b m) (hbs.mul_left (b j * b k)) (hm j k) (hg j k)

end S99

end
