import HRS.Main.GFB2Aux2
import HRS.Uniform.Q54cAux58

/-!
# Packet GFB2, part 3: moment of the trace-norm covariance error (`gf_trace_moment`), conditional on `gf_trace_error`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

theorem gfb2_jensen_sqrt {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Ω → ℝ) (hGm : Measurable G) (hG0 : ∀ᵐ ω ∂P, 0 ≤ G ω) (hGi : Integrable G P) :
    Integrable (fun ω => Real.sqrt (G ω)) P ∧ ∫ ω, Real.sqrt (G ω) ∂P ≤ Real.sqrt (∫ ω, G ω ∂P) := by
  have hum : Measurable fun ω => Real.sqrt (G ω) := hGm.sqrt
  have hsq : (fun ω => Real.sqrt (G ω) ^ 2) =ᵐ[P] G := by
    filter_upwards [hG0] with ω hω using Real.sq_sqrt hω
  have hint2 : Integrable (fun ω => Real.sqrt (G ω) ^ 2) P := hGi.congr hsq.symm
  have hmem : MemLp (fun ω => Real.sqrt (G ω)) 2 P :=
    (memLp_two_iff_integrable_sq hum.aestronglyMeasurable).2 hint2
  have hu1 : Integrable (fun ω => Real.sqrt (G ω)) P := hmem.integrable one_le_two
  refine ⟨hu1, ?_⟩
  have hv := variance_nonneg (fun ω => Real.sqrt (G ω)) P
  rw [variance_eq_sub hmem] at hv
  have h1 : ∫ ω, Real.sqrt (G ω) ∂P ≤ |∫ ω, Real.sqrt (G ω) ∂P| := le_abs_self _
  refine h1.trans (Real.abs_le_sqrt ?_)
  have e : P[(fun ω => Real.sqrt (G ω)) ^ 2] = ∫ ω, G ω ∂P := integral_congr_ae hsq
  rw [e] at hv
  linarith


/-- The completed energy with time clamped to `[0,T]` (jointly measurable version). -/
def gfb2_G (S : GeneralSetup d) (N : ℕ) {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) (r : ℝ) (ω : Ω) : ℝ :=
  rieszEnergy d S.s (X (Real.toNNReal (Q54c.clampT S.T r)) ω) (withDensityReal (S.ρ N (Q54c.clampT S.T r))) +
    oN d S.s S.C₀ N

theorem gfb2_G_meas (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → Config d N)
    (hprog : IsProgressive ℱ (ofNNRealTime X)) :
    Measurable fun p : ℝ × Ω => gfb2_G S N X p.1 p.2 := by
  have hZ := gfb2_progressive_meas ℱ X hprog S.hT.le
  have h := (gfb2_energy_meas S M hMF N).comp (measurable_fst.prodMk hZ)
  exact h

theorem gfb2_G_eq (S : GeneralSetup d) (N : ℕ) {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) S.T) (ω : Ω) :
    S.energyCompletion N (X (Real.toNNReal r) ω) r = gfb2_G S N X r ω := by
  simp only [gfb2_G, Q54c.clampT_of_mem hr]
  rfl

theorem gfb2_trace_core (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
    (hF : ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
    (hE : S.EnergyMomentFinite P N X) (C q n : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hn : 0 ≤ n)
    (hpt : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∀ x : Config d N, x ∉ collisionSet d N →
      traceNormForm (covForm (S.γ : ℝ) q (empirical x) - covForm (S.γ : ℝ) q (withDensityReal (S.ρ N r))) ≤
        C * q * (Real.sqrt (S.energyCompletion N x r) + n)) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
      (covForm (S.γ : ℝ) q (empirical (X (Real.toNNReal r) ω)) -
        covForm (S.γ : ℝ) q (withDensityReal (S.ρ N r))))) ∂P ≤
      ENNReal.ofReal (S.T * (C * q * (Real.sqrt (S.energyMoment P N X) + n))) := by
  have hnn := (gf_energy_integral_moment_proof S M hMF N hN P X₀ W X hX hF hE).1
  obtain ⟨ℱ, W', hFil⟩ := hF
  have hT : 0 ≤ S.T := S.hT.le
  have hGm := gfb2_G_meas S M hMF N ℱ X hFil.progressive
  have hnnG : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) S.T, 0 ≤ gfb2_G S N X r ω := by
    filter_upwards [hnn] with ω hω r hr
    rw [← gfb2_G_eq S N X hr ω]; exact hω r hr
  have hjm : Measurable fun p : ℝ × Ω =>
      ENNReal.ofReal (C * q * (Real.sqrt (gfb2_G S N X p.1 p.2) + n)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hGm.sqrt.add_const n))
  have step1 : ∀ᵐ ω ∂P, ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
      (covForm (S.γ : ℝ) q (empirical (X (Real.toNNReal r) ω)) -
        covForm (S.γ : ℝ) q (withDensityReal (S.ρ N r)))) ≤
      ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (C * q * (Real.sqrt (gfb2_G S N X r ω) + n)) := by
    filter_upwards [hX.no_collision] with ω hω
    refine setLIntegral_mono' measurableSet_Icc fun r hr => ENNReal.ofReal_le_ofReal ?_
    rw [← gfb2_G_eq S N X hr ω]
    refine hpt r hr _ (hω (Real.toNNReal r) ?_)
    rw [Real.coe_toNNReal r hr.1]; exact hr.2
  have hswap : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (C * q * (Real.sqrt (gfb2_G S N X r ω) + n))) ∂P =
      ∫⁻ r in Set.Icc (0 : ℝ) S.T, (∫⁻ ω,
        ENNReal.ofReal (C * q * (Real.sqrt (gfb2_G S N X r ω) + n)) ∂P) := by
    rw [lintegral_lintegral_swap]
    exact (hjm.comp measurable_swap).aemeasurable
  have hper : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∫⁻ ω,
      ENNReal.ofReal (C * q * (Real.sqrt (gfb2_G S N X r ω) + n)) ∂P ≤
        ENNReal.ofReal (C * q * (Real.sqrt (S.energyMoment P N X) + n)) := by
    intro r hr
    have hGr : Measurable (gfb2_G S N X r) := Measurable.of_uncurry_left hGm
    have hfun : (fun ω => S.energyCompletion N (X (Real.toNNReal r) ω) r) = gfb2_G S N X r :=
      funext fun ω => gfb2_G_eq S N X hr ω
    have hGi : Integrable (gfb2_G S N X r) P := by rw [← hfun]; exact hE.1 r hr
    have hG0 : ∀ᵐ ω ∂P, 0 ≤ gfb2_G S N X r ω := by
      filter_upwards [hnnG] with ω hω using hω r hr
    have hjs := gfb2_jensen_sqrt P _ hGr hG0 hGi
    have hui := hjs.1
    have hJ := hjs.2
    have hint : Integrable (fun ω => C * q * (Real.sqrt (gfb2_G S N X r ω) + n)) P :=
      (hui.add (integrable_const n)).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω =>
      mul_nonneg (mul_nonneg hC hq) (add_nonneg (Real.sqrt_nonneg _) hn))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul, integral_add hui (integrable_const n)]
    rw [integral_const]; simp only [probReal_univ, one_smul, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one]
    have hsq : Real.sqrt (∫ ω, gfb2_G S N X r ω ∂P) ≤ Real.sqrt (S.energyMoment P N X) := by
      refine Real.sqrt_le_sqrt ?_
      have := le_ciSup hE.2 (⟨r, hr⟩ : Set.Icc (0 : ℝ) S.T)
      rw [← hfun]
      exact this
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC hq)
  calc ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
      (covForm (S.γ : ℝ) q (empirical (X (Real.toNNReal r) ω)) -
        covForm (S.γ : ℝ) q (withDensityReal (S.ρ N r))))) ∂P
      ≤ ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
          ENNReal.ofReal (C * q * (Real.sqrt (gfb2_G S N X r ω) + n))) ∂P := lintegral_mono_ae step1
    _ = ∫⁻ r in Set.Icc (0 : ℝ) S.T, (∫⁻ ω,
        ENNReal.ofReal (C * q * (Real.sqrt (gfb2_G S N X r ω) + n)) ∂P) := hswap
    _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (C * q * (Real.sqrt (S.energyMoment P N X) + n)) :=
        setLIntegral_mono' measurableSet_Icc hper
    _ = ENNReal.ofReal (S.T * (C * q * (Real.sqrt (S.energyMoment P N X) + n))) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_mul hT, mul_comm]


/-- `gf_trace_moment` from the pointwise packet `gf_trace_error` (given as a hypothesis `herr`). -/
theorem gfb2_trace_moment_of_error (herr : type_of% @HRS.GF.gf_trace_error)
    (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P (S.dynM M N) S.T X₀ W X →
        (∃ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        S.EnergyMomentFinite P N X →
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
          (covForm (S.γ : ℝ) (qN S N) (empirical (X (Real.toNNReal r) ω)) -
            covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ∂P ≤
          ENNReal.ofReal (C * qN S N *
            (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) := by
  classical
  by_cases hex : ∃ S₀ : GeneralSetup d, S₀.s = b.s ∧ S₀.γ = b.γ
  · obtain ⟨S₀, hs₀, hγ₀⟩ := hex
    have hd1 : 1 ≤ d := by have := S₀.hd; omega
    have hs0 : 0 ≤ b.s := hs₀ ▸ S₀.hs0
    have hsd : b.s < d := hs₀ ▸ S₀.hsd
    have hγ : 2 * d + 10 < b.γ := hγ₀ ▸ S₀.hγ
    obtain ⟨C₀min, h⟩ := herr hd1 b.s hs0 hsd b.γ hγ b.Λ
    refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
    obtain ⟨C, hCpos, hpt⟩ := h C₀ hC₀
    refine ⟨C * (|b.T| + 1), by positivity, ?_⟩
    intro S hS hMF N hN Ω _ P _ X₀ W X hX hF hE
    unfold GeneralSetup.Within at hS
    obtain ⟨hs, hT, hγ', hΛ, hβ, hC0, hV⟩ := hS
    have hC0' : S.C₀ = C₀ := hC0
    have hq : 0 ≤ qN S N := (Q54c.qScale_bounds (by omega) (S.hκ N) (S.hinvβ N)).1
    have hn : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    obtain ⟨hMFN, hReg⟩ := hMF N
    have hpt' : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∀ x : Config d N, x ∉ collisionSet d N →
        traceNormForm (covForm (S.γ : ℝ) (qN S N) (empirical x) -
          covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))) ≤
          C * qN S N * (Real.sqrt (S.energyCompletion N x r) + (N : ℝ) ^ (-(2 : ℝ) / d)) := by
      intro r hr x hx
      have hck : Torus.IsCk (b.γ + 2 * d + 12) (S.ρ N r) := by rw [← hγ']; exact (hReg r hr).1
      have hcb : Torus.cbNorm (b.γ + 2 * d + 12) (S.ρ N r) ≤ b.Λ := by
        rw [← hγ', ← hΛ]; exact (hReg r hr).2
      have h1 := hpt N hN (S.ρ N r) (hMFN.density r hr) hck hcb x hx (qN S N) hq
      unfold GeneralSetup.energyCompletion
      rw [hγ', hs, hC0']
      exact h1
    have hcore := gfb2_trace_core S M hMF N hN P X₀ W X hX hF hE C (qN S N) _ hCpos.le hq hn hpt'
    refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
    have hA : 0 ≤ C * qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d)) :=
      mul_nonneg (mul_nonneg hCpos.le hq) (add_nonneg (Real.sqrt_nonneg _) hn)
    have hTle : S.T ≤ |b.T| + 1 := by rw [hT]; linarith [le_abs_self b.T]
    calc S.T * (C * qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d)))
        ≤ (|b.T| + 1) * (C * qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) :=
          mul_le_mul_of_nonneg_right hTle hA
      _ = C * (|b.T| + 1) * qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d)) := by ring
  · refine ⟨0, fun C₀ _ => ⟨1, one_pos, ?_⟩⟩
    intro S hS
    exact absurd ⟨S, hS.1, hS.2.2.1⟩ hex

theorem gf_trace_moment_proof (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P (S.dynM M N) S.T X₀ W X →
        (∃ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        S.EnergyMomentFinite P N X →
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
          (covForm (S.γ : ℝ) (qN S N) (empirical (X (Real.toNNReal r) ω)) -
            covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ∂P ≤
          ENNReal.ofReal (C * qN S N *
            (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) :=
  gfb2_trace_moment_of_error (@HRS.GF.gf_trace_error) b M

example := (@gf_trace_moment_proof : type_of% @HRS.GF.gf_trace_moment)

end HRS.GF
