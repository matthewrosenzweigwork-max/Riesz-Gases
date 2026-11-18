import HRS.MS.S21L_G11D
import HRS.MS.S21L_G11F
import HRS.MS.S21L_G11G

/-!
# S21L G11H -- the vector Wick chaos of a measurable symmetric kernel (R26-T3.G11, ninth step)

For a measurable symmetric `K ∈ L²(μ⊗μ; B)` and an orthonormal basis `a0` of `L²_0(μ)`, with `V_ij = ∬ e_i(x) e_j(y) K(x,y)`:
`Q = ½ lim ∑_{i,j<n} (z_i z_j - E z_i z_j) • V_ij` (G11G) satisfies: coordinates lie in the scalar second chaos
(so `Q ∈ InSecondChaos P ξ 3`, G11F), `2 ℓ(Q)` is the Wick chaos of `ℓ ∘ K` in EVERY orthonormal basis (basis independence,
G11D), and `E ‖Q‖² ≤ (Λ²/2) ∬ ‖K‖²`.  Prefix `s21l_`.
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

variable {d : ℕ} {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- The coefficient vectors `V_ij = ∬ e_i(x) e_j(y) K(x,y)`. -/
def s21l_V (μ : Measure (Euc d)) (a : ℕ → Euc d → ℝ) (K : Euc d → Euc d → B) (i j : ℕ) : B :=
  ∫ q, (Whole.projMean μ (a i) q.1 * Whole.projMean μ (a j) q.2) • K q.1 q.2 ∂(μ.prod μ)

theorem s21l_V_int {a : ℕ → Euc d → ℝ} (hat : ∀ i, IsR2Test (a i))
    {K : Euc d → Euc d → B} (hKm : Measurable fun q : Euc d × Euc d => K q.1 q.2)
    (hK2 : MemLp (fun q : Euc d × Euc d => K q.1 q.2) 2 (μ.prod μ)) (i j : ℕ) :
    Integrable (fun q : Euc d × Euc d =>
      (Whole.projMean μ (a i) q.1 * Whole.projMean μ (a j) q.2) • K q.1 q.2) (μ.prod μ) := by
  obtain ⟨C1, h1⟩ := s94_projMean_bounded μ (hat i)
  obtain ⟨C2, h2⟩ := s94_projMean_bounded μ (hat j)
  have hφ : Measurable fun q : Euc d × Euc d => Whole.projMean μ (a i) q.1 * Whole.projMean μ (a j) q.2 :=
    ((s94_projMean_continuous μ (hat i)).measurable.comp measurable_fst).mul
      ((s94_projMean_continuous μ (hat j)).measurable.comp measurable_snd)
  have hK1 : Integrable (fun q : Euc d × Euc d => K q.1 q.2) (μ.prod μ) := hK2.integrable one_le_two
  refine Integrable.mono' (hK1.norm.const_mul (C1 * C2)) (hφ.aestronglyMeasurable.smul hKm.aestronglyMeasurable)
    (ae_of_all _ fun q => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  have hC1 : 0 ≤ C1 := (abs_nonneg _).trans (h1 q.1)
  exact mul_le_mul_of_nonneg_right (mul_le_mul (h1 q.1) (h2 q.2) (abs_nonneg _) hC1) (norm_nonneg _)

theorem s21l_V_coord {a : ℕ → Euc d → ℝ} (hat : ∀ i, IsR2Test (a i))
    {K : Euc d → Euc d → B} (hKm : Measurable fun q : Euc d × Euc d => K q.1 q.2)
    (hK2 : MemLp (fun q : Euc d × Euc d => K q.1 q.2) 2 (μ.prod μ)) (ℓ : B →L[ℝ] ℝ) (i j : ℕ) :
    ℓ (s21l_V μ a K i j) = r2WickCoeff μ a (fun x y => ℓ (K x y)) i j := by
  unfold s21l_V
  rw [← ContinuousLinearMap.integral_comp_comm ℓ (s21l_V_int hat hKm hK2 i j)]
  have hkm : Measurable fun q : Euc d × Euc d => ℓ (K q.1 q.2) := ℓ.continuous.measurable.comp hKm
  have hk2 : MemLp (fun q : Euc d × Euc d => ℓ (K q.1 q.2)) 2 (μ.prod μ) := ℓ.comp_memLp' hK2
  rw [s94_coeff_eq_prod hat hkm hk2 i j]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [map_smul, smul_eq_mul, s94E2]
  ring

theorem s21l_V_symm {a : ℕ → Euc d → ℝ} {K : Euc d → Euc d → B} (hsym : ∀ x y, K x y = K y x) (i j : ℕ) :
    s21l_V μ a K i j = s21l_V μ a K j i := by
  unfold s21l_V
  have := integral_prod_swap (μ := μ) (ν := μ) (fun q : Euc d × Euc d =>
    (Whole.projMean μ (a i) q.1 * Whole.projMean μ (a j) q.2) • K q.1 q.2)
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [hsym q.2 q.1, mul_comm]

theorem s21l_V_bessel {a : ℕ → Euc d → ℝ} (hat : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {K : Euc d → Euc d → B} (hKm : Measurable fun q : Euc d × Euc d => K q.1 q.2)
    (hK2 : MemLp (fun q : Euc d × Euc d => K q.1 q.2) 2 (μ.prod μ)) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ‖s21l_V μ a K i j‖ ^ 2 ≤
      ∫ q, ‖K q.1 q.2‖ ^ 2 ∂(μ.prod μ) := by
  obtain ⟨ι, hι, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := B)
  have hP := s21l_hasSum_sq b hK2
  have hG : HasSum (fun s => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (inner ℝ (b s) (s21l_V μ a K i j)) ^ 2)
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ‖s21l_V μ a K i j‖ ^ 2) := by
    refine hasSum_sum fun i _ => ?_
    refine hasSum_sum fun j _ => ?_
    exact s21l_hasSum_norm_sq b _
  refine hasSum_le (fun s => ?_) hG hP
  have hkm : Measurable fun q : Euc d × Euc d => inner ℝ (b s) (K q.1 q.2) :=
    (innerSL ℝ (b s)).continuous.measurable.comp hKm
  have hk2 : MemLp (fun q : Euc d × Euc d => inner ℝ (b s) (K q.1 q.2)) 2 (μ.prod μ) :=
    (innerSL ℝ (b s)).comp_memLp' hK2
  have := s94_bessel (μ := μ) hat hon (k := fun x y => inner ℝ (b s) (K x y)) hkm hk2
    (Finset.range n ×ˢ Finset.range n)
  rw [Finset.sum_product] at this
  refine le_trans (le_of_eq ?_) this
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := s21l_V_coord hat hKm hK2 (innerSL ℝ (b s)) i j
  simp only [innerSL_apply_apply] at this
  rw [this]

section Core

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

theorem s21l_clm_tendsto {Sn : ℕ → Ω → B} {Q0 : Ω → B} (hSn : ∀ n, MemLp (Sn n) 2 P) (hQ0 : MemLp Q0 2 P)
    (h : Tendsto (fun n => ∫ ω, ‖Sn n ω - Q0 ω‖ ^ 2 ∂P) atTop (𝓝 0)) (ℓ : B →L[ℝ] ℝ) :
    Tendsto (fun n => ∫ ω, (ℓ (Sn n ω) - ℓ (Q0 ω)) ^ 2 ∂P) atTop (𝓝 0) := by
  have h2 := h.const_mul (‖ℓ‖ ^ 2)
  rw [mul_zero] at h2
  refine squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) (fun n => ?_) h2
  have hd : MemLp (fun ω => Sn n ω - Q0 ω) 2 P := (hSn n).sub hQ0
  rw [← integral_const_mul]
  refine integral_mono ?_ ((HilbertCLTAux.integrable_sq_norm_of_memLp2 hd).const_mul _) (fun ω => ?_)
  · have := (ℓ.comp_memLp' hd).integrable_sq
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp [map_sub]
  · show (ℓ (Sn n ω) - ℓ (Q0 ω)) ^ 2 ≤ ‖ℓ‖ ^ 2 * ‖Sn n ω - Q0 ω‖ ^ 2
    rw [← map_sub]
    have h1 := ℓ.le_opNorm (Sn n ω - Q0 ω)
    calc (ℓ (Sn n ω - Q0 ω)) ^ 2 = ‖ℓ (Sn n ω - Q0 ω)‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      _ ≤ (‖ℓ‖ * ‖Sn n ω - Q0 ω‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = _ := by ring

theorem s21l_tendsto_lintegral {Y : ℕ → Ω → ℝ} {Z : Ω → ℝ} (hZ : MemLp Z 2 P) (hY : ∀ n, MemLp (Y n) 2 P)
    (h : Tendsto (fun n => ∫ ω, (Y n ω - Z ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, ‖Y n ω - Z ω‖ₑ ^ (2 : ℝ) ∂P) atTop (𝓝 0) := by
  have := (HRS.tendstoL2_of_memLp hZ hY h).2
  refine this.congr fun n => lintegral_congr fun ω => ?_
  rw [ENNReal.rpow_two]

theorem s21l_core (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) {η : (Euc d → ℝ) → Ω → ℝ} {Λ : ℝ}
    (h : S21LEta μ P η Λ) (hΛ0 : 0 ≤ Λ) (hfirst : ∀ f, MemLp f 2 μ → InFirstChaos P ξ 2 (η f))
    {a0 : ℕ → Euc d → ℝ} (hb0 : IsR2ZeroMeanONB μ a0)
    {K : Euc d → Euc d → B} (hKm : Measurable fun q : Euc d × Euc d => K q.1 q.2) (hsym : ∀ x y, K x y = K y x)
    (hK2 : MemLp (fun q : Euc d × Euc d => K q.1 q.2) 2 (μ.prod μ))
    (V : ℕ → ℕ → B) (hVc : ∀ (ℓ : B →L[ℝ] ℝ) (i j : ℕ), ℓ (V i j) = r2WickCoeff μ a0 (fun x y => ℓ (K x y)) i j)
    (hVs : ∀ i j, V i j = V j i)
    (hM : ∀ n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ‖V i j‖ ^ 2 ≤ ∫ q, ‖K q.1 q.2‖ ^ 2 ∂(μ.prod μ)) :
    ∃ Q : Ω → B, AEStronglyMeasurable Q P ∧ InSecondChaos P ξ 3 Q ∧
      (∀ ℓ : B →L[ℝ] ℝ, ∀ a, IsR2ZeroMeanONB μ a → IsR2WickChaos P μ a (fun j => η (a j))
        (r2CenterKernel μ (fun x y => ℓ (K x y))) (fun ω => 2 * ℓ (Q ω))) ∧
      ∫ ω, ‖Q ω‖ ^ 2 ∂P ≤ (Λ ^ 2 / 2) * ∫ q, ‖K q.1 q.2‖ ^ 2 ∂(μ.prod μ) := by
  obtain ⟨hat0, hon0, hcomp0⟩ := hb0
  have hb0' : IsR2ZeroMeanONB μ a0 := ⟨hat0, hon0, hcomp0⟩
  set z : ℕ → Ω → ℝ := fun i ζ => η (a0 i) ζ with hz
  have hzS : S94GSeq P z Λ := s21l_gseq h hat0 hon0
  obtain ⟨Q0, hQ0m, hQ0L, hQ0lim, hQ0b⟩ := s21l_sections_limit hzS hΛ0 hVs hM
  have hSL : ∀ n, MemLp (fun ω => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • V i j) 2 P := fun n => (s21l_vec_isometry hzS hΛ0 hVs n).1
  have hQ1 : ∀ i, InQ1 hξ hm (z i) := fun i => s21l_inQ1_of_first hξ hm (hfirst _ (s21l_test_memLp (hat0 i)))
  have hw : ∀ i j, InQ2 hξ (fun ω => z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) := fun i j =>
    InQ2.mul_centered hξ hm (hQ1 i) (hQ1 j)
  refine ⟨fun ω => (1 / 2 : ℝ) • Q0 ω, hQ0m.const_smul _, ?_, ?_, ?_⟩
  · refine s21l_inSecondChaos_of_coords hξ hm (hQ0m.const_smul _) (hQ0L.const_smul _) fun v => ?_
    set Y : ℕ → Ω → ℝ := fun n ω => (1 / 2 : ℝ) * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      inner ℝ v (V i j) * (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) with hY
    have hYi : ∀ n, InQ2 hξ (Y n) := fun n =>
      InQ2.const_mul _ (InQ2.sum _ fun i _ => InQ2.sum _ fun j _ => InQ2.const_mul _ (hw i j))
    have hYL : ∀ n, MemLp (Y n) 2 P := fun n => (hYi n).1
    have hZ : MemLp (fun ω => inner ℝ v ((1 / 2 : ℝ) • Q0 ω)) 2 P :=
      (innerSL ℝ v).comp_memLp' (hQ0L.const_smul _)
    refine InQ2.of_tendsto (l := atTop) hYi hZ.aestronglyMeasurable ?_
    refine s21l_tendsto_lintegral hZ hYL ?_
    have hc := s21l_clm_tendsto hSL hQ0L hQ0lim (innerSL ℝ v)
    have h4 := hc.const_mul (1 / 4 : ℝ)
    rw [mul_zero] at h4
    refine h4.congr fun n => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    beta_reduce
    have hSe : (innerSL ℝ v) (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • V i j) = 2 * Y n ω := by
      simp only [hY, innerSL_apply_apply, inner_sum, inner_smul_right]
      rw [← mul_assoc]; norm_num
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hZe : inner ℝ v ((1 / 2 : ℝ) • Q0 ω) = (1 / 2) * (innerSL ℝ v) (Q0 ω) := by
      simp [inner_smul_right]
    have hYe : Y n ω = (1 / 2) * (innerSL ℝ v) (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • V i j) := by
      rw [hSe]; ring
    rw [hYe, hZe]
    ring
  · intro ℓ a hb
    obtain ⟨hat, hon, hcomp⟩ := hb
    set k : Euc d → Euc d → ℝ := fun x y => ℓ (K x y) with hk
    have hkm : Measurable fun q : Euc d × Euc d => k q.1 q.2 := ℓ.continuous.measurable.comp hKm
    have hks : ∀ x y, k x y = k y x := fun x y => by simp only [hk, hsym x y]
    have hk2 : MemLp (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ) := ℓ.comp_memLp' hK2
    have hk1 : Integrable (fun q : Euc d × Euc d => k q.1 q.2) (μ.prod μ) := hk2.integrable one_le_two
    have hA0 : s94WickL2 P μ a0 z k (fun ω => ℓ (Q0 ω)) := by
      refine ⟨ℓ.comp_memLp' hQ0L, ?_⟩
      have := s21l_clm_tendsto hSL hQ0L hQ0lim ℓ
      refine this.congr fun n => ?_
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      beta_reduce
      have e : ℓ (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P) • V i j) =
          s94Sec P z (fun i j => r2WickCoeff μ a0 k i j) n ω := by
        simp only [s94Sec, map_sum, map_smul, smul_eq_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hVc ℓ i j]
        ring
      rw [e]
    have hza : S94GSeq P (fun i ζ => η (a i) ζ) Λ := s21l_gseq h hat hon
    obtain ⟨Qa, hQa, -⟩ := s94_wick_exists hza hΛ0 hat hon hkm hks hk2
    have heq : (fun ω => ℓ (Q0 ω)) =ᵐ[P] Qa :=
      s21l_wick_unique h hΛ0 hb0' ⟨hat, hon, hcomp⟩ hkm hks hk2 hA0 hQa
    have hAa : s94WickL2 P μ a (fun i ζ => η (a i) ζ) k (fun ω => ℓ (Q0 ω)) := by
      refine ⟨ℓ.comp_memLp' hQ0L, ?_⟩
      refine hQa.2.congr fun n => integral_congr_ae ?_
      filter_upwards [heq] with ω hω
      rw [hω]
    have hc := s21l_wickL2_center hat hk1 hAa
    have := s94WickL2.isWick hza hc
    have e : (fun ω => 2 * ℓ ((1 / 2 : ℝ) • Q0 ω)) = fun ω => ℓ (Q0 ω) := by
      funext ω
      simp only [map_smul, smul_eq_mul]
      ring
    rw [e]
    exact this
  · have : ∫ ω, ‖(1 / 2 : ℝ) • Q0 ω‖ ^ 2 ∂P = (1 / 4) * ∫ ω, ‖Q0 ω‖ ^ 2 ∂P := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      beta_reduce
      rw [norm_smul]
      simp only [Real.norm_eq_abs]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      ring
    rw [this]
    nlinarith [hQ0b]

end Core

end HRS.MS.R26T3
