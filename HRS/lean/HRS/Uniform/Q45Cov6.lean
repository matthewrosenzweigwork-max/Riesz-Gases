import HRS.Uniform.Q45Cov5

/-!
# Q45 (Lemma 3.20): `L²` passage to the limit for products
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section L2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} {l : Filter ι}

lemma eLpNorm_two_eq {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) :
    eLpNorm f 2 P = (∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp [ENNReal.toReal_ofNat]

lemma eLpNorm_two_tendsto {f : ι → Ω → ℝ} (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (h : Tendsto (fun i => ∫⁻ ω, ‖f i ω‖ₑ ^ 2 ∂P) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) 2 P) l (𝓝 0) := by
  have e : ∀ i, eLpNorm (f i) 2 P = (∫⁻ ω, ‖f i ω‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) := fun i =>
    eLpNorm_two_eq (hf i)
  simp_rw [e]
  have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)] using this

lemma memLp_two_of_tendsto [l.NeBot] {a : Ω → ℝ} (ha : AEStronglyMeasurable a P) {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (h : Tendsto (fun i => eLpNorm (X i - a) 2 P) l (𝓝 0)) :
    MemLp a 2 P := by
  obtain ⟨i, hi⟩ := (h.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))).exists
  have h1 : MemLp (X i - a) 2 P := lt_of_lt_of_le hi le_top
  have h2 := (hX i).sub h1
  refine h2.ae_eq (Eventually.of_forall fun ω => ?_)
  simp

lemma tendsto_integral_mul_L2 {a b : Ω → ℝ} {X Y : ι → Ω → ℝ} (ha : MemLp a 2 P) (hb : MemLp b 2 P)
    (hX : ∀ i, MemLp (X i) 2 P) (hY : ∀ i, MemLp (Y i) 2 P)
    (h1 : Tendsto (fun i => eLpNorm (X i - a) 2 P) l (𝓝 0))
    (h2 : Tendsto (fun i => eLpNorm (Y i - b) 2 P) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω, X i ω * Y i ω ∂P) l (𝓝 (∫ ω, a ω * b ω ∂P)) := by
  have A := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fi := l) X hX a ha).2 h1
  have B := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fi := l) Y hY b hb).2 h2
  have e : ∀ (f g : Ω → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P),
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂P := by
    intro f g hf hg
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have hT := Filter.Tendsto.inner (𝕜 := ℝ) A B
  simp only [e] at hT
  exact hT

end L2

end HRS.Uniform.Q45
