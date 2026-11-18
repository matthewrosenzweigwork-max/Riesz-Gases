import HRS.MS.R2S11Aux4
import HRS.MS.Fp81S21InitialBkernel

open MeasureTheory Filter Topology ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/-- Uniform control of the actual-centered initial quadratic statistic by
product-law `L²` distance, for kernels with one common singular envelope. -/
theorem fp81s21_initial_Bh_small_of_L2
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ) :
    ∀ B : ℝ, 0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ η : ℝ, 0 < η ∧
        ∀ h : Euc p.d → Euc p.d → ℝ,
          IsBoundedPairKernel p.s B h →
          eLpNorm (Function.uncurry h) 2 ((r26t3_mu R 0).prod (r26t3_mu R 0))
            ≤ ENNReal.ofReal η →
          ∀ N : ℕ, 2 ≤ N →
            Integrable (fp81s21_initial_Bh R N h) (r26t3_Q R N) ∧
            eLpNorm (fp81s21_initial_Bh R N h) 1 (r26t3_Q R N)
              ≤ ENNReal.ofReal ε := by
  intro B hB ε hε
  classical
  by_contra hno
  have hbad : ∀ η : ℝ, 0 < η →
      ∃ h : Euc p.d → Euc p.d → ℝ,
        IsBoundedPairKernel p.s B h ∧
        eLpNorm (Function.uncurry h) 2 ((r26t3_mu R 0).prod (r26t3_mu R 0))
          ≤ ENNReal.ofReal η ∧
        ∃ N : ℕ, 2 ≤ N ∧
          (Integrable (fp81s21_initial_Bh R N h) (r26t3_Q R N) →
            ENNReal.ofReal ε <
              eLpNorm (fp81s21_initial_Bh R N h) 1 (r26t3_Q R N)) := by
    intro η hη
    have hnot : ¬ (∀ h : Euc p.d → Euc p.d → ℝ,
        IsBoundedPairKernel p.s B h →
        eLpNorm (Function.uncurry h) 2 ((r26t3_mu R 0).prod (r26t3_mu R 0))
          ≤ ENNReal.ofReal η →
        ∀ N : ℕ, 2 ≤ N →
          Integrable (fp81s21_initial_Bh R N h) (r26t3_Q R N) ∧
          eLpNorm (fp81s21_initial_Bh R N h) 1 (r26t3_Q R N)
            ≤ ENNReal.ofReal ε) := by
      intro hall
      exact hno ⟨η, hη, hall⟩
    push Not at hnot
    exact hnot
  let ηseq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hηseq : ∀ n, 0 < ηseq n := by
    intro n
    positivity
  choose kernels hkernel hsmall hNexists using fun n => hbad (ηseq n) (hηseq n)
  choose Ns hNs hfail using hNexists

  obtain ⟨M, L, hρ0⟩ := s21f_round2Density_init hδ hδh R
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hρ0.prob
  have hprob : ∀ N : ℕ, 2 ≤ N → IsProbabilityMeasure (r26t3_Q R N) :=
    (r26t3_static_pressure hδ hδh R hγ).1
  let ρ : Unit → Euc p.d → ℝ := fun _ => R.ρ 0
  have hρ : ∀ k : Unit, IsRound2Density p.d p.s M L (ρ k) := by
    intro k
    simpa [ρ] using hρ0
  let P : Unit → ∀ N : ℕ, Measure (EucConfig p.d N) := fun _ => r26t3_Q R
  have hP : ∀ k N, 2 ≤ N →
      HasR2ActualDensity p.s p.γ 2 1 (HRS.Whole.withDensityReal (ρ k)) (P k N) := by
    intro k N hN
    have hq := hprob N hN
    letI : IsProbabilityMeasure (r26t3_Q R N) := hq
    refine ⟨hq, Measure.AbsolutelyContinuous.refl _, ?_⟩
    have hae : (fun X : EucConfig p.d N =>
        ((r26t3_Q R N).rnDeriv (r26t3_Q R N) X).toReal) =ᵐ[r26t3_Q R N]
        fun _ => (1 : ℝ) :=
      (Measure.rnDeriv_self (r26t3_Q R N)).mono fun X hX => by simp [hX]
    show eLpNorm (fun X : EucConfig p.d N =>
        ((r26t3_Q R N).rnDeriv (r26t3_Q R N) X).toReal)
      (ENNReal.ofReal 2) (r26t3_Q R N) ≤ ENNReal.ofReal 1
    rw [eLpNorm_congr_ae hae, eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero _)]
    norm_num

  let D : Unit → ℕ → Euc p.d → Euc p.d → ℝ := fun _ n => kernels n
  let τ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((ηseq n) ^ 2)
  have hτ : Tendsto τ atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => (ηseq n) ^ 2) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
      simpa [ηseq] using h
    have h := ENNReal.tendsto_ofReal hreal
    simpa [τ] using h
  have hD : ∀ k j, IsBoundedPairKernel p.s (0 * B + B) (D k j) := by
    intro k j
    simpa [D] using hkernel j
  have hτb : ∀ k j,
      (eLpNorm (fun z : Euc p.d × Euc p.d => D k j z.1 z.2) (ENNReal.ofReal 2)
        ((HRS.Whole.withDensityReal (ρ k)).prod (HRS.Whole.withDensityReal (ρ k)))) ^ 2
        ≤ τ j := by
    intro k j
    have hnorm : eLpNorm (Function.uncurry (kernels j)) (ENNReal.ofReal 2)
        ((r26t3_mu R 0).prod (r26t3_mu R 0)) ≤ ENNReal.ofReal (ηseq j) := by
      simpa using hsmall j
    calc
      _ ≤ (ENNReal.ofReal (ηseq j)) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hnorm 2
      _ = τ j := by
        rw [← ENNReal.ofReal_pow (hηseq j).le]
  obtain ⟨J, hJ⟩ :=
    (HRS.MS.R2S11.s11_tail_key_fam (κ := Unit) (d := p.d)
      p.hd p.hs0 p.hs M L p.γ 2 1 B 1 0 hγ (by norm_num) (by norm_num)
      (ρ := ρ) hρ (P := P) hP (D := D) hD (τ := τ) hτ hτb
      (θ := ε / 2) (by positivity)).exists
  have hplain : ∀ N : ℕ, 2 ≤ N →
      eLpNorm (fun X : EucConfig p.d N => (N : ℝ) *
        pairEnergy (kernels J) X (r26t3_mu R 0)) (ENNReal.ofReal 1) (r26t3_Q R N)
        ≤ ENNReal.ofReal (ε / 2) := by
    intro N hN
    have h := hJ () N hN
    simpa [D, ρ, P, r26t3_mu] using h
  have hcent : ∀ N : ℕ, 2 ≤ N →
      eLpNorm (fp81s21_initial_Bh R N (kernels J)) (ENNReal.ofReal 1) (r26t3_Q R N)
        ≤ ENNReal.ofReal ε := by
    intro N hN
    letI : IsProbabilityMeasure (r26t3_Q R N) := hprob N hN
    let U : EucConfig p.d N → ℝ := fun X => (N : ℝ) *
      pairEnergy (kernels J) X (r26t3_mu R 0)
    have hUm : Measurable U := by
      exact measurable_const.mul
        (HRS.MS.Wr.wr9_measurable_pairEnergy (hkernel J).measurable)
    have hunc : eLpNorm U (ENNReal.ofReal 1) (r26t3_Q R N)
        ≤ ENNReal.ofReal (ε / 2) := by
      simpa [U] using hplain N hN
    have hc := HRS.MS.R2Mt.s92_centered_le (r26t3_Q R N) hUm
      (by norm_num : (1 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ ε / 2) hunc
    have hEq : (fun X : EucConfig p.d N => U X - ∫ Y, U Y ∂(r26t3_Q R N)) =
        fun X => fp81s21_initial_Bh R N (kernels J) X := by
      funext X
      dsimp [U, fp81s21_initial_Bh]
      rw [integral_const_mul]
      ring
    have hcentered : eLpNorm (fun X : EucConfig p.d N =>
        U X - ∫ Y, U Y ∂(r26t3_Q R N)) (ENNReal.ofReal 1) (r26t3_Q R N)
        ≤ ENNReal.ofReal ε := by
      have hreal : 2 * (ε / 2) = ε := by ring
      simpa [hreal] using hc
    change eLpNorm (fun X => fp81s21_initial_Bh R N (kernels J) X)
      (ENNReal.ofReal 1) (r26t3_Q R N) ≤ ENNReal.ofReal ε
    rw [← hEq]
    exact hcentered

  have hgood : Integrable (fp81s21_initial_Bh R (Ns J) (kernels J))
      (r26t3_Q R (Ns J)) ∧
      eLpNorm (fp81s21_initial_Bh R (Ns J) (kernels J)) 1 (r26t3_Q R (Ns J))
        ≤ ENNReal.ofReal ε := by
    refine ⟨fp81s21_initial_Bh_int hδ hδh R E hγ (hkernel J) (hNs J), ?_⟩
    simpa using hcent (Ns J) (hNs J)
  exact (not_lt_of_ge hgood.2) (hfail J hgood.1)

#print axioms fp81s21_initial_Bh_small_of_L2

end HRS.Fp81.S21

end

