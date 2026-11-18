import HRS.MC.E213U11e

/-!
# Packet e213u11, file f: elementary tools for the uniform moments

Cauchy--Schwarz on a unit block, weighted Jensen for finite sums, geometric sums, and the moment of a weighted sum
of random variables.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U11

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

/-- Cauchy--Schwarz on a unit block: `∫_{[0,1]} ‖f‖ ≤ ‖f‖_{L²}`. -/
theorem u11_cs_unit {r : ℝ} {f : ℝ → NegSobolev d r}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∫ t in Set.Icc (0 : ℝ) 1, ‖f t‖ ≤ ‖toL2 r 1 f‖ := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμ
  haveI : IsProbabilityMeasure μ := ⟨by simp [hμ]⟩
  have hg : MemLp (fun t => ‖f t‖) 2 μ := hf.norm
  have hv := variance_nonneg (fun t => ‖f t‖) μ
  rw [variance_eq_sub hg] at hv
  have h2 : μ[(fun t => ‖f t‖) ^ 2] = ‖toL2 r 1 f‖ ^ 2 := by
    rw [HRS.MC.Sec7.S7FCH3.S7FCH3_toL2_norm_sq r 1 hf]
    rfl
  rw [h2] at hv
  have hnn := norm_nonneg (toL2 r 1 f)
  by_contra hcon
  push_neg at hcon
  have : ‖toL2 r 1 f‖ ^ 2 < (μ[fun t => ‖f t‖]) ^ 2 := by nlinarith
  linarith

/-- Weighted Jensen for finite sums. -/
theorem u11_sum_pow_le {ι : Type*} (s : Finset ι) (α Y : ι → ℝ) (hα : ∀ i ∈ s, 0 ≤ α i)
    (hY : ∀ i ∈ s, 0 ≤ Y i) (q : ℕ) (hq : 1 ≤ q) :
    (∑ i ∈ s, α i * Y i) ^ q ≤ (∑ i ∈ s, α i) ^ (q - 1) * ∑ i ∈ s, α i * Y i ^ q := by
  by_cases hA : ∑ i ∈ s, α i = 0
  · have h0 : ∀ i ∈ s, α i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hα).1 hA
    have : ∑ i ∈ s, α i * Y i = 0 := Finset.sum_eq_zero fun i hi => by rw [h0 i hi, zero_mul]
    have h2 : ∑ i ∈ s, α i * Y i ^ q = 0 := Finset.sum_eq_zero fun i hi => by rw [h0 i hi, zero_mul]
    rw [this, hA, h2, zero_pow (by omega)]
    simp
  · have hApos : 0 < ∑ i ∈ s, α i := lt_of_le_of_ne (Finset.sum_nonneg hα) (Ne.symm hA)
    set A := ∑ i ∈ s, α i with hAdef
    have hJ := Real.pow_arith_mean_le_arith_mean_pow s (fun i => α i / A) Y
      (fun i hi => div_nonneg (hα i hi) hApos.le)
      (by rw [← Finset.sum_div, ← hAdef, div_self hA]) hY q
    have e1 : ∑ i ∈ s, α i / A * Y i = (∑ i ∈ s, α i * Y i) / A := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i ∈ s, α i / A * Y i ^ q = (∑ i ∈ s, α i * Y i ^ q) / A := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, div_pow] at hJ
    have hAq : 0 < A ^ q := pow_pos hApos q
    have h3 : (∑ i ∈ s, α i * Y i) ^ q ≤ A ^ q * ((∑ i ∈ s, α i * Y i ^ q) / A) := by
      have := mul_le_mul_of_nonneg_left hJ hAq.le
      rwa [mul_div_cancel₀ _ hAq.ne'] at this
    refine h3.trans (le_of_eq ?_)
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [pow_succ]
    field_simp

/-- The moment of a weighted finite sum of nonnegative random variables with bounded `q`-th moments. -/
theorem u11_wsum_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (n : ℕ) (α : ℕ → ℝ) (Y : ℕ → Ω → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hY0 : ∀ i ω, 0 ≤ Y i ω) (hYm : ∀ i, AEMeasurable (Y i) P) (q : ℕ) (hq : 1 ≤ q)
    (M : ℝ) (hYint : ∀ i, Integrable (fun ω => Y i ω ^ q) P) (hYM : ∀ i, ∫ ω, Y i ω ^ q ∂P ≤ M) :
    Integrable (fun ω => (∑ i ∈ Finset.range n, α i * Y i ω) ^ q) P ∧
      ∫ ω, (∑ i ∈ Finset.range n, α i * Y i ω) ^ q ∂P ≤ (∑ i ∈ Finset.range n, α i) ^ q * M := by
  set A := ∑ i ∈ Finset.range n, α i with hA
  have hpt : ∀ ω, (∑ i ∈ Finset.range n, α i * Y i ω) ^ q ≤
      A ^ (q - 1) * ∑ i ∈ Finset.range n, α i * Y i ω ^ q := fun ω =>
    u11_sum_pow_le _ _ _ (fun i _ => hα i) (fun i _ => hY0 i ω) q hq
  have hIr : Integrable (fun ω => A ^ (q - 1) * ∑ i ∈ Finset.range n, α i * Y i ω ^ q) P :=
    ((integrable_finsetSum _ fun i _ => (hYint i).const_mul (α i))).const_mul _
  have hmeas : AEMeasurable (fun ω => (∑ i ∈ Finset.range n, α i * Y i ω) ^ q) P := by
    have hs : AEMeasurable (fun ω => ∑ i ∈ Finset.range n, α i * Y i ω) P :=
      Finset.aemeasurable_fun_sum _ fun i _ => (hYm i).const_mul (α i)
    exact hs.pow_const q
  refine ⟨hIr.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hα i) (hY0 i ω)) _)]
    exact hpt ω
  · refine (integral_mono_of_nonneg (Eventually.of_forall fun ω =>
        pow_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hα i) (hY0 i ω)) _) hIr
        (Eventually.of_forall hpt)).trans ?_
    rw [integral_const_mul, integral_finset_sum _ fun i _ => (hYint i).const_mul (α i)]
    have h1 : ∑ i ∈ Finset.range n, ∫ ω, α i * Y i ω ^ q ∂P ≤ ∑ i ∈ Finset.range n, α i * M := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hYM i) (hα i)
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => hα i
    calc A ^ (q - 1) * ∑ i ∈ Finset.range n, ∫ ω, α i * Y i ω ^ q ∂P
        ≤ A ^ (q - 1) * ∑ i ∈ Finset.range n, α i * M := mul_le_mul_of_nonneg_left h1 (pow_nonneg hA0 _)
      _ = A ^ q * M := by
        rw [← Finset.sum_mul, ← hA]
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring

/-- Geometric bound on the weights `e^{-c(a-(k+1))}`, `k < ⌈a+T⌉`, uniformly in `a ≥ 0`. -/
theorem u11_weights_bound (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ a : ℝ, 0 ≤ a →
      ∑ k ∈ Finset.range ⌈a + T⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1))) ≤ A := by
  set n0 := Real.exp c with hn0
  have hn1 : 1 < n0 := by have := Real.add_one_lt_exp hc.ne'; linarith
  refine ⟨Real.exp (c * (T + 2)) / (n0 - 1), by
    have : 0 < n0 - 1 := by linarith
    positivity, fun a ha => ?_⟩
  have hterm : ∀ k : ℕ, Real.exp (-c * (a - ((k : ℝ) + 1))) = Real.exp (c * (1 - a)) * n0 ^ k := by
    intro k
    rw [hn0, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, geom_sum_eq hn1.ne']
  have hn : (⌈a + T⌉₊ : ℝ) < a + T + 1 := Nat.ceil_lt_add_one (by linarith)
  have hpos : 0 < n0 - 1 := by linarith
  have h1 : n0 ^ ⌈a + T⌉₊ ≤ Real.exp (c * (a + T + 1)) := by
    rw [hn0, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by nlinarith)
  calc Real.exp (c * (1 - a)) * ((n0 ^ ⌈a + T⌉₊ - 1) / (n0 - 1))
      ≤ Real.exp (c * (1 - a)) * (Real.exp (c * (a + T + 1)) / (n0 - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact div_le_div_of_nonneg_right (by linarith) hpos.le
    _ = Real.exp (c * (T + 2)) / (n0 - 1) := by
        rw [← mul_div_assoc, ← Real.exp_add]
        congr 2; ring

end HRS.MC.E213U11

end
