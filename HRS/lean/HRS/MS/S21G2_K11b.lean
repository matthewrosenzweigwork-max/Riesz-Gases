import HRS.MS.S21G2_K11bC

/-!
# S21G2 K11b -- the kernel contraction identifies the limit half-Wick pairing (R26-T3.K11b)

`E[Q X Y] = ∬ h u ⊗ v` where `2Q` is the Wick chaos of the centred kernel `h_c` and `E[z_i X] = ⟪a_i, u⟫`, `E[z_i Y] = ⟪a_i, v⟫`.
Route: K11a for the `n × n` section, `L²` convergence of the sections (Cauchy-Schwarz against `XY ∈ L²`), the finite sums become
`B(F_n, G_n)` (centering terms vanish, part B), which converges to `B(u, v)` along the orthonormal expansions (parts A, C).
Contract verbatim (qualified names); helpers carry the prefix `s21g2_k11b_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s21g2_k11b_cs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    |∫ ω, f ω * g ω ∂P| ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) * Real.sqrt (∫ ω, g ω ^ 2 ∂P) := by
  refine (abs_integral_le_integral_abs).trans ?_
  have h1 : MemLp (fun ω => |f ω|) (ENNReal.ofReal 2) P := by simpa [Real.norm_eq_abs] using hf.norm
  have h2 : MemLp (fun ω => |g ω|) (ENNReal.ofReal 2) P := by simpa [Real.norm_eq_abs] using hg.norm
  have := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (ae_of_all _ fun ω => abs_nonneg (f ω)) (ae_of_all _ fun ω => abs_nonneg (g ω)) h1 h2
  simp_rw [abs_mul]
  refine this.trans (le_of_eq ?_)
  simp only [Real.rpow_two, sq_abs]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

theorem s21g2_k11b_sq_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {S : ℕ → Ω → ℝ} {R : Ω → ℝ} (hS : ∀ n, MemLp (S n) 2 P) (hR : MemLp R 2 P)
    (hT : Tendsto (fun n => ∫⁻ ω, ‖S n ω - R ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (S n ω - R ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hE : ∀ n, ∫ ω, (S n ω - R ω) ^ 2 ∂P = (∫⁻ ω, ‖S n ω - R ω‖ₑ ^ 2 ∂P).toReal := fun n => by
    have hm : MemLp (fun ω => S n ω - R ω) 2 P := (hS n).sub hR
    have : ∫⁻ ω, ‖S n ω - R ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ ω, (S n ω - R ω) ^ 2 ∂P) := by
      rw [ofReal_integral_eq_lintegral_ofReal hm.integrable_sq (ae_of_all _ fun _ => sq_nonneg _)]
      refine lintegral_congr fun ω => ?_
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
    rw [this, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  simp_rw [hE]
  simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT

theorem r26t3_kernel_wick_pair {d : ℕ} (μ : Measure (HRS.Euc d)) [IsProbabilityMeasure μ]
    (a : ℕ → HRS.Euc d → ℝ) (ha : HRS.Whole.IsR2ZeroMeanONB μ a)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒢 : Submodule ℝ (Ω → ℝ)) (h𝒢 : HRS.MC.QRSpec.Wick.QrpwG4 P 𝒢)
    (z : ℕ → Ω → ℝ) (hz : ∀ i, z i∈𝒢) (X Y Q : Ω → ℝ)
    (hX : X∈𝒢) (hY : Y∈𝒢) (hQ : MemLp Q 2 P)
    (h : HRS.Euc d → HRS.Euc d → ℝ) (hsym : ∀ x y, h x y=h y x)
    (hh : MemLp (fun z : HRS.Euc d × HRS.Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hW : HRS.Whole.IsR2WickChaos P μ a z (HRS.Whole.r2CenterKernel μ h) (fun ω => 2*Q ω))
    (u v : HRS.Euc d → ℝ) (hu : HRS.Whole.MemL2Zero μ u) (hv : HRS.Whole.MemL2Zero μ v)
    (hcovX : ∀ i, ∫ ω, z i ω*X ω ∂P=∫ x, a i x*u x ∂μ)
    (hcovY : ∀ i, ∫ ω, z i ω*Y ω ∂P=∫ x, a i x*v x ∂μ) :
    Integrable (fun z : HRS.Euc d × HRS.Euc d => h z.1 z.2*u z.1*v z.2) (μ.prod μ) ∧
    (∫ ω, Q ω*X ω*Y ω ∂P)=∫ x, ∫ y, h x y*u x*v y ∂μ ∂μ := by
  classical
  have ha' := ha
  obtain ⟨hat, hon, hcomp⟩ := ha
  set e : ℕ → HRS.Euc d → ℝ := fun i => HRS.Whole.projMean μ (a i) with he
  have hem : ∀ i, MemLp (e i) 2 μ := fun i => HRS.MS.R2Chaos.s94_memLp_projMean (hat i)
  have hec : ∀ i, Continuous (e i) := fun i => HRS.MS.R2Chaos.s94_projMean_continuous μ (hat i)
  have hbd : ∀ i, ∃ C, ∀ x, |e i x| ≤ C := fun i => HRS.MS.R2Chaos.s94_projMean_bounded μ (hat i)
  have hmz : ∀ i, ∫ x, e i x ∂μ = 0 := fun i => HRS.MS.R2Chaos.s94_integral_projMean (hat i)
  have hk1 : Integrable (fun z : HRS.Euc d × HRS.Euc d => h z.1 z.2) (μ.prod μ) := hh.integrable one_le_two
  set A : ℕ → ℕ → ℝ := fun i j => HRS.Whole.r2WickCoeff μ a (HRS.Whole.r2CenterKernel μ h) i j with hAdef
  have hA : ∀ i j, A i j = s21g2_k11b_B μ h (e i) (e j) := fun i j => by
    obtain ⟨Ci, hCi⟩ := hbd i
    obtain ⟨Cj, hCj⟩ := hbd j
    have := s21g2_k11b_center hk1 (hec i) (hec j) hCi hCj (hmz i) (hmz j)
    refine this.trans ?_
    unfold s21g2_k11b_B
    rw [integral_prod _ (s21g2_k11b_B_bound hh (hem i) (hem j)).1]
    exact integral_congr_ae (ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun y => by ring))
  have hAs : ∀ i j, A i j = A j i := fun i j => by
    rw [hA, hA]
    unfold s21g2_k11b_B
    rw [← integral_prod_swap (μ := μ) (ν := μ) (fun z : HRS.Euc d × HRS.Euc d => h z.1 z.2 * (e i z.1 * e j z.2))]
    exact integral_congr_ae (ae_of_all _ fun z => by simp only [Prod.fst_swap, Prod.snd_swap]; rw [hsym z.2 z.1]; ring)
  have hcov : ∀ (w : HRS.Euc d → ℝ), HRS.Whole.MemL2Zero μ w → ∀ i, ∫ x, a i x * w x ∂μ = ∫ y, w y * e i y ∂μ := by
    intro w hw i
    have h1 : Integrable (fun x => a i x * w x) μ :=
      (hw.1.integrable one_le_two).bdd_mul (hat i).1.continuous.aestronglyMeasurable
        (c := (HRS.MS.R2Chaos.s94_test_bounded (hat i)).choose) (ae_of_all _ fun x => by
          simpa using (HRS.MS.R2Chaos.s94_test_bounded (hat i)).choose_spec x)
    have h2 : Integrable (fun x => HRS.Whole.pair μ (a i) * w x) μ := (hw.1.integrable one_le_two).const_mul _
    have : ∀ y, w y * e i y = a i y * w y - HRS.Whole.pair μ (a i) * w y := fun y => by
      simp only [he, HRS.Whole.projMean]; ring
    simp_rw [this]
    rw [integral_sub h1 h2, integral_const_mul, hw.2]; simp
  set γ : ℕ → ℝ := fun i => ∫ y, u y * e i y ∂μ with hγ
  set δ : ℕ → ℝ := fun i => ∫ y, v y * e i y ∂μ with hδ
  have hX4 := (h𝒢 X hX).1
  have hY4 := (h𝒢 Y hY).1
  have hz4 : ∀ i, MemLp (z i) 4 P := fun i => (h𝒢 _ (hz i)).1
  have hXY : MemLp (fun ω => X ω * Y ω) 2 P := HRS.MC.QRSpec.Wick.qrpw_memLp2_mul hX4 hY4
  have hzz : ∀ i j, MemLp (fun ω => z i ω * z j ω) 2 P := fun i j => HRS.MC.QRSpec.Wick.qrpw_memLp2_mul (hz4 i) (hz4 j)
  set R : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    HRS.Whole.r2WickCoeff μ a (HRS.Whole.r2CenterKernel μ h) i j * (z i ω * z j ω - ∫ ω', z i ω' * z j ω' ∂P) with hR
  have hRm : ∀ n, MemLp (R n) 2 P := fun n =>
    memLp_finsetSum (f := fun i ω => ∑ j ∈ Finset.range n, A i j * (z i ω * z j ω - ∫ ω', z i ω' * z j ω' ∂P))
      _ fun i _ => memLp_finsetSum (f := fun j ω => A i j * (z i ω * z j ω - ∫ ω', z i ω' * z j ω' ∂P)) _
        fun j _ => ((hzz i j).sub (memLp_const _)).const_mul _
  have hF := s21g2_k11b_expand ha' hu.1 hu.2
  -- finite section identity
  have hsec : ∀ n, ∫ ω, ((1 / 2) * R n ω) * X ω * Y ω ∂P = s21g2_k11b_B μ h
      (fun x => ∑ i ∈ Finset.range n, γ i * e i x) (fun x => ∑ i ∈ Finset.range n, δ i * e i x) := by
    intro n
    have hK := r26t3_finite_wick_pair P 𝒢 h𝒢 n (fun i : Fin n => z i) (fun i => hz i) X Y hX hY
      (fun i j : Fin n => A i j) (fun i j => hAs i j)
    have e1 : ∀ ω, R n ω = ∑ i : Fin n, ∑ j : Fin n, A i j *
        (z i ω * z j ω - ∫ ω', z i ω' * z j ω' ∂P) := fun ω => by
      simp only [hR, hAdef, Finset.sum_range]
    simp_rw [e1]
    rw [hK]
    have e2 : ∀ i j : Fin n, A i j * (∫ ω, z i ω * X ω ∂P) * (∫ ω, z j ω * Y ω ∂P) =
        γ i * δ j * s21g2_k11b_B μ h (e i) (e j) := fun i j => by
      rw [hcovX, hcovY, hcov u hu, hcov v hv, hA]; ring
    simp_rw [e2]
    rw [s21g2_k11b_B_finsum hh n γ δ e hem]
    simp only [Finset.sum_range]
  have hB := s21g2_k11b_B_tendsto ha' hh hu hv
  have hQXY : Integrable (fun ω => Q ω * (X ω * Y ω)) P := hQ.integrable_mul hXY
  have hsq := s21g2_k11b_sq_tendsto (S := R) (R := fun ω => 2 * Q ω) hRm (hQ.const_mul 2) hW.2
  have hlimL : Tendsto (fun n => ∫ ω, ((1 / 2) * R n ω) * X ω * Y ω ∂P) atTop
      (𝓝 (∫ ω, Q ω * X ω * Y ω ∂P)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have hb : Tendsto (fun n => Real.sqrt ((1 / 4) * ∫ ω, (R n ω - 2 * Q ω) ^ 2 ∂P) *
        Real.sqrt (∫ ω, (X ω * Y ω) ^ 2 ∂P)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => (1 / 4 : ℝ) * ∫ ω, (R n ω - 2 * Q ω) ^ 2 ∂P) atTop (𝓝 0) := by
        simpa using hsq.const_mul (1 / 4 : ℝ)
      have := ((Real.continuous_sqrt.tendsto 0).comp h0).mul_const
        (Real.sqrt (∫ ω, (X ω * Y ω) ^ 2 ∂P))
      simpa [Function.comp_def] using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
    have hi1 : Integrable (fun ω => ((1 / 2) * R n ω) * (X ω * Y ω)) P :=
      (((hRm n).const_mul (1 / 2)).integrable_mul hXY)
    have e1 : ∀ ω, ((1 / 2) * R n ω) * X ω * Y ω = ((1 / 2) * R n ω) * (X ω * Y ω) := fun ω => by ring
    have e2 : ∀ ω, Q ω * X ω * Y ω = Q ω * (X ω * Y ω) := fun ω => by ring
    simp_rw [e1, e2]
    rw [← integral_sub hi1 hQXY, Real.norm_eq_abs]
    have hd : MemLp (fun ω => (1 / 2) * R n ω - Q ω) 2 P := ((hRm n).const_mul (1 / 2)).sub hQ
    have := s21g2_k11b_cs hd hXY
    have e3 : ∀ ω, ((1 / 2) * R n ω) * (X ω * Y ω) - Q ω * (X ω * Y ω) =
        ((1 / 2) * R n ω - Q ω) * (X ω * Y ω) := fun ω => by ring
    simp_rw [e3]
    refine this.trans (le_of_eq ?_)
    congr 2
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  have hlim := tendsto_nhds_unique (hlimL.congr hsec) hB
  have hint := (s21g2_k11b_B_bound hh hu.1 hv.1).1
  refine ⟨hint.congr (ae_of_all _ fun z => by ring), ?_⟩
  rw [hlim]
  unfold s21g2_k11b_B
  rw [integral_prod _ hint]
  exact integral_congr_ae (ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun y => by ring))

end HRS.MS.R26T3
