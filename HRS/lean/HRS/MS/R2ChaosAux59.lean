import HRS.MS.R2ChaosAux58

/-!
# HRS.MS.R2ChaosAux59 -- S9.6 (P4): a.s. `L²(dt)` membership and uniform moments for polynomial kernels

Packet S94 (S9.6), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole HRS.MS.R2Poly

variable {d : ℕ}

section PMoments

variable {s T b p K M L C₀ c₀ Pw : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_quad_ae_memLp_of_bound (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ)
    {kf : ℝ → Euc d → Euc d → ℝ} (hkm : Measurable fun q : ℝ × Euc d × Euc d => kf q.1 q.2.1 q.2.2)
    [IsProbabilityMeasure (Whole.withDensityReal ρ)] {N : ℕ} {C : ℝ}
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T, eLpNorm (fun ζ => r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ) 2 (P N) ≤ ENNReal.ofReal C) :
    ∀ᵐ ζ ∂(P N), MemLp (fun t => r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  have hQ := s94_quad_measurable (μ := Whole.withDensityReal ρ) (P := P N) hkm (X N) (hset.measX N)
  let I : Ω N → ℝ≥0∞ := fun ζ => ∫⁻ t in Set.Icc (0 : ℝ) T,
    ‖r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ‖ₑ ^ 2 ∂volume
  have hQ2 : Measurable fun q : ℝ × Ω N =>
      ‖r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) q.1 q.2‖ₑ ^ 2 := hQ.enorm.pow_const 2
  have hIm : Measurable I := (hQ2.comp measurable_swap).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) T))
  have hswap : ∫⁻ ζ, I ζ ∂(P N) = ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ζ,
      ‖r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ‖ₑ ^ 2 ∂(P N) :=
    lintegral_lintegral_swap (hQ2.comp measurable_swap).aemeasurable
  have hbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ‖r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ‖ₑ ^ 2
      ∂(P N) ≤ ENNReal.ofReal C ^ 2 := by
    intro t ht
    have hsm_t : AEStronglyMeasurable (fun ζ => r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ) (P N) :=
      (hQ.comp (measurable_prodMk_left (x := t))).aestronglyMeasurable
    rw [s94_lintegral_sq_eq hsm_t]
    exact pow_le_pow_left' (hbd t ht) 2
  have hfin : ∫⁻ ζ, I ζ ∂(P N) < ⊤ := by
    rw [hswap]
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Icc hbd) ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (by simp)
  filter_upwards [ae_lt_top hIm hfin.ne] with ζ hζ
  have hsm : AEStronglyMeasurable (fun t => r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    (hQ.comp (measurable_prodMk_right (y := ζ))).aestronglyMeasurable
  have := s94_lintegral_sq_eq hsm
  have h2 : eLpNorm (fun t => r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) ^ 2 < ⊤ := by rw [← this]; exact hζ
  by_contra hne
  have htop : eLpNorm (fun t => r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) = ⊤ := by
    by_contra h'
    exact hne (lt_top_iff_ne_top.2 h')
  rw [htop] at h2
  simp at h2


theorem s94_pquad_ae_memLp (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ) (hG : HasR2GaussianUpper C₀ c₀ ρ) (hPw : 0 ≤ Pw)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {B : ℝ} (hB : 0 ≤ B)
    {h : ℝ → Euc d → Euc d → ℝ} (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsR2PolyPairKernel s Pw B (h t)) {N : ℕ} (hN : 2 ≤ N) :
    ∀ᵐ ζ ∂(P N), MemLp (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hC⟩ := s94_ptime_bounds hd hs0 hs hb hp hρ hG hPw hset (r := 2) (by norm_num)
  refine s94_quad_ae_memLp_of_bound hset hmeas (C := C * B) fun t ht => ?_
  have hb2 := (hC t ht N hN B hB (h t) (hker t ht)).2
  have e2 : ENNReal.ofReal 2 = 2 := by norm_num
  rw [e2] at hb2
  exact hb2

theorem s94_pmoment_y (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ) (hG : HasR2GaussianUpper C₀ c₀ ρ) (hPw : 0 ≤ Pw)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 < T) {B : ℝ} (hB : 0 ≤ B)
    {h : ℝ → Euc d → Euc d → ℝ} (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsR2PolyPairKernel s Pw B (h t))
    {k : ℕ} {aa : Fin k → Euc d → ℝ} (haa : ∀ i, IsR2Test (aa i)) {q : ℝ} (hq : 2 ≤ q) :
    ∃ Mq : ℝ, 0 ≤ Mq ∧ ∀ N : ℕ, 2 ≤ N →
      ∫⁻ ζ, ENNReal.ofReal (‖s94_mkH T (fun i => r2L2Path T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ))
        (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ))‖ ^ q) ∂(P N)
        ≤ ENNReal.ofReal Mq := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  obtain ⟨Cl, hCl⟩ := s94_linear_moment hd hs0 hs hb hp hρ hset (r := q) hq1
  obtain ⟨Cq, hCq⟩ := s94_ptime_bounds hd hs0 hs hb hp hρ hG hPw hset (r := q) hq1
  have hA : ∀ i, ∃ A : ℝ, 0 ≤ A ∧ ∀ x, |aa i x| ≤ A := fun i => by
    obtain ⟨A, hA⟩ := s94_test_bounded (haa i)
    exact ⟨A, (abs_nonneg _).trans (hA 0), hA⟩
  choose A hA0 hAb using hA
  have hC0 : ∀ i, 0 ≤ |Cl| * A i := fun i => mul_nonneg (abs_nonneg _) (hA0 i)
  have hCq0 : 0 ≤ |Cq * B| := abs_nonneg _
  have hterm : ∀ i, 0 ≤ T ^ (q / 2) * (|Cl| * A i) ^ q := fun i =>
    mul_nonneg (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg (hC0 i) _)
  have htermq : 0 ≤ T ^ (q / 2) * |Cq * B| ^ q := mul_nonneg (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg hCq0 _)
  refine ⟨((k : ℝ) + 1) ^ (q - 1) * (∑ i, T ^ (q / 2) * (|Cl| * A i) ^ q + T ^ (q / 2) * |Cq * B| ^ q),
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (add_nonneg (Finset.sum_nonneg fun i _ => hterm i) htermq),
    fun N hN => ?_⟩
  set μ := Whole.withDensityReal ρ with hμ
  let fi : Fin k → ℝ × Ω N → ℝ := fun i z => r2EmpFluct μ (aa i) (X N) z.2 z.1
  let fq : ℝ × Ω N → ℝ := fun z => r2QuadFluct μ h (P N) (X N) z.1 z.2
  have hfi : ∀ i, Measurable (fi i) := fun i => s94_empFluct_measurable (haa i) (X N) (hset.measX N)
  have hfq : Measurable fq := s94_quad_measurable (μ := μ) hmeas (X N) (hset.measX N)
  have hmi : ∀ i, ∫⁻ ζ, ENNReal.ofReal (‖r2L2Path T (fun t => fi i (t, ζ))‖ ^ q) ∂(P N) ≤
      ENNReal.ofReal (T ^ (q / 2) * (|Cl| * A i) ^ q) := by
    intro i
    refine s94_moment_L2path hT (hfi i) hq (hC0 i) fun t ht => ?_
    refine (hCl N hN t ht (aa i) (A i) (haa i).1.continuous.measurable (hAb i)).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) (hA0 i))
  have hmq : ∫⁻ ζ, ENNReal.ofReal (‖r2L2Path T (fun t => fq (t, ζ))‖ ^ q) ∂(P N) ≤
      ENNReal.ofReal (T ^ (q / 2) * |Cq * B| ^ q) := by
    refine s94_moment_L2path hT hfq hq hCq0 fun t ht => ?_
    refine ((hCq t ht N hN B hB (h t) (hker t ht)).2).trans ?_
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  -- pointwise power-mean bound
  have hpt : ∀ ζ, ENNReal.ofReal (‖s94_mkH T (fun i => r2L2Path T (r2EmpFluct μ (aa i) (X N) ζ))
      (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ))‖ ^ q) ≤
      ENNReal.ofReal (((k : ℝ) + 1) ^ (q - 1)) * (∑ i, ENNReal.ofReal (‖r2L2Path T (fun t => fi i (t, ζ))‖ ^ q) +
        ENNReal.ofReal (‖r2L2Path T (fun t => fq (t, ζ))‖ ^ q)) := by
    intro ζ
    have h1 := s94_normH_pow_le (s94_mkH T (fun i => r2L2Path T (r2EmpFluct μ (aa i) (X N) ζ))
      (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ))) hq1
    rw [Fin.sum_univ_castSucc] at h1
    simp only [s94_mkH_castSucc, s94_mkH_last] at h1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => by positivity)
      (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h1
  have hmeasi : ∀ i, Measurable fun ζ => ENNReal.ofReal (‖r2L2Path T (fun t => fi i (t, ζ))‖ ^ q) := fun i =>
    ENNReal.measurable_ofReal.comp ((s94_measurable_r2L2Path T (fi i ∘ Prod.map id id) (hfi i)).norm.pow_const q)
  have hmeasq : Measurable fun ζ => ENNReal.ofReal (‖r2L2Path T (fun t => fq (t, ζ))‖ ^ q) :=
    ENNReal.measurable_ofReal.comp ((s94_measurable_r2L2Path T fq hfq).norm.pow_const q)
  calc _ ≤ ∫⁻ ζ, ENNReal.ofReal (((k : ℝ) + 1) ^ (q - 1)) * (∑ i, ENNReal.ofReal (‖r2L2Path T (fun t => fi i (t, ζ))‖ ^ q) +
        ENNReal.ofReal (‖r2L2Path T (fun t => fq (t, ζ))‖ ^ q)) ∂(P N) := lintegral_mono hpt
    _ = ENNReal.ofReal (((k : ℝ) + 1) ^ (q - 1)) * (∑ i, ∫⁻ ζ, ENNReal.ofReal (‖r2L2Path T (fun t => fi i (t, ζ))‖ ^ q) ∂(P N) +
        ∫⁻ ζ, ENNReal.ofReal (‖r2L2Path T (fun t => fq (t, ζ))‖ ^ q) ∂(P N)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (Finset.measurable_sum _ fun i _ => hmeasi i),
          lintegral_finset_sum _ fun i _ => hmeasi i]
    _ ≤ ENNReal.ofReal (((k : ℝ) + 1) ^ (q - 1)) * (∑ i, ENNReal.ofReal (T ^ (q / 2) * (|Cl| * A i) ^ q) +
        ENNReal.ofReal (T ^ (q / 2) * |Cq * B| ^ q)) := by
        refine mul_le_mul_right (add_le_add (Finset.sum_le_sum fun i _ => hmi i) hmq) _
    _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hterm i), ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => hterm i)
          htermq, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]


end PMoments

end HRS.MS.R2Chaos
