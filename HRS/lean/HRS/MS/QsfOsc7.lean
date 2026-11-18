import HRS.MS.QsfOsc6

/-!
# S4.5 oscillator clause, part 7: scaling of the susceptibility covariance and Gaussian transport
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s45_U_smul {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {ψ : Euc d → ℝ}
    (hψ : MemLp ψ 2 ν) (c : ℝ) :
    s45_U (fun x => c * ψ x) (hψ.const_mul c) = c • s45_U ψ hψ := by
  refine Lp.ext ?_
  filter_upwards [s45_U_ae (hψ.const_mul c), s45_U_ae hψ, Lp.coeFn_smul c (s45_U ψ hψ)]
    with x h1 h2 h3
  rw [h3, Pi.smul_apply, smul_eq_mul, h1, h2]
  unfold projMean pair
  rw [integral_const_mul]
  ring

theorem s45_cov_smul (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU : ℝ}
    (hβ : 0 < β) (hT : ThermalData d s a β C c BU) {φ ψ : Euc d → ℝ}
    (hφ : MemLp φ 2 (thermalMeasure d s a β)) (hψ : MemLp ψ 2 (thermalMeasure d s a β))
    (c₁ c₂ : ℝ) :
    susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β (fun x => c₁ * φ x)
        (fun x => c₂ * ψ x) =
      c₁ * c₂ * susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β φ ψ := by
  have hd1 : 1 ≤ d := by omega
  haveI : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨L, hL⟩ := s45_thermal_logmoment2 hT
  have hM : ∀ x, thermalDensity d s a β x ≤ C := fun x => (le_abs_self _).trans
    ((hT.h0 x).trans (by
      have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hT.hc])
      nlinarith [hT.C0]))
  obtain ⟨K, hK⟩ : ∃ K : Lp ℝ 2 (thermalMeasure d s a β) →L[ℝ] Lp ℝ 2 (thermalMeasure d s a β),
      IsKData (thermalMeasure d s a β) (rieszKernel d s) K :=
    s45_kdata hd1 hs0 hsd hT.prob hM (L := L) (fun _ => hL)
  rw [s45_susceptibilityCov_eq hK hβ (hφ.const_mul c₁) (hψ.const_mul c₂),
    s45_susceptibilityCov_eq hK hβ hφ hψ, s45_U_smul hφ c₁, s45_U_smul hψ c₂, map_smul,
    inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  ring

theorem s45_coord_continuous (i : ℕ) : Continuous fun z : SeqL2 => SeqL2.coord z i := by
  have : (fun z : SeqL2 => SeqL2.coord z i) = fun z => ⟪s45_seqBasis i, z⟫ :=
    funext fun z => (s45_inner_seqBasis i z).symm
  rw [this]
  exact continuous_const.inner continuous_id

/-- Transport of the Gaussian from `B_m` to `ℓ²`. -/
theorem s45_gauss_transport {m : ℝ} (e : ℕ ≃ MultiIndex d) {γ : Measure (OscDual d m)}
    {Cv : (Euc d → ℝ) → (Euc d → ℝ) → ℝ} (hγ : IsCenteredGaussianOsc m γ Cv) :
    IsCenteredGaussianSeq (γ.map (s45_Psi m e)) fun i j =>
      oscEigenvalue d (e i) ^ (-(m / 2)) * oscEigenvalue d (e j) ^ (-(m / 2)) *
        Cv (hermiteFunD (e i)) (hermiteFunD (e j)) := by
  obtain ⟨⟨hG, hcen⟩, hcov⟩ := hγ
  have hΨc : Continuous (s45_Psi m e) := (s45_Psi m e).continuous
  have hΨm : Measurable (s45_Psi m e) := hΨc.measurable
  refine ⟨⟨?_, fun L => ?_⟩, fun i j => ?_⟩
  · exact isGaussian_map_equiv (μ := γ) (s45_Psi m e).toContinuousLinearEquiv
  · rw [integral_map hΨm.aemeasurable L.continuous.aestronglyMeasurable]
    have := hcen (L.comp (s45_Psi m e).toContinuousLinearEquiv.toContinuousLinearMap)
    simpa using this
  · have hcm : AEStronglyMeasurable (fun z : SeqL2 => SeqL2.coord z i * SeqL2.coord z j)
        (γ.map (s45_Psi m e)) :=
      ((s45_coord_continuous i).mul (s45_coord_continuous j)).aestronglyMeasurable
    have hform : ∀ u : OscDual d m, SeqL2.coord (s45_Psi m e u) i * SeqL2.coord (s45_Psi m e u) j =
        oscEigenvalue d (e i) ^ (-(m / 2)) * oscEigenvalue d (e j) ^ (-(m / 2)) *
          (OscDual.hermiteCoeff u (e i) * OscDual.hermiteCoeff u (e j)) := by
      intro u
      rw [s45_Psi_coord, s45_Psi_coord, s45_coord_eq_hermiteCoeff u (e i),
        s45_coord_eq_hermiteCoeff u (e j)]
      ring
    obtain ⟨hint, hval⟩ := hcov (e i) (e j)
    refine ⟨(integrable_map_measure hcm hΨm.aemeasurable).2 ?_, ?_⟩
    · have : (fun u => SeqL2.coord (s45_Psi m e u) i * SeqL2.coord (s45_Psi m e u) j) =
          fun u => oscEigenvalue d (e i) ^ (-(m / 2)) * oscEigenvalue d (e j) ^ (-(m / 2)) *
            (OscDual.hermiteCoeff u (e i) * OscDual.hermiteCoeff u (e j)) := funext hform
      show Integrable (fun u => SeqL2.coord (s45_Psi m e u) i * SeqL2.coord (s45_Psi m e u) j) γ
      rw [this]
      exact hint.const_mul _
    · rw [integral_map hΨm.aemeasurable hcm]
      simp_rw [hform]
      rw [integral_const_mul, hval]

end S45

end
