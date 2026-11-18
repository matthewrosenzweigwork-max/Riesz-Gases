import HRS.MS.S21F_S05a
import HRS.MS.S21F_D02
import HRS.MS.ThCorrFarAux2
import HRS.MS.S81G_Sing

/-!
# S21F, packet R26-T3.S05: static normalizers, probabilities and Gibbs weight power bounds

At the actual initial reference `μ₀ = (1+εψ)ρ_β dx` (Gaussian bound, `ρ₀ ≤ |M₀|`, finite second moment hence the logarithmic moment),
`s92_normalizer_bounds` (native `euclidean_pressure_proof` at `θ = 0`, `h = 0`, `Nδ_N = 1`) gives `GibbsWellDefined` and
`|log K_{N,b}| ≤ C₀` uniformly for `b ∈ [γ, rγ]`, `N ≥ 2`; hence `Q_{N,γ}` is a probability measure and
`‖dQ/dμ^{⊗N}‖_{L^r} ≤ (e^{(r+1)C₀})^{1/r}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem s21f_logmoment {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (hm2 : Integrable (fun y : Euc d => ‖y‖ ^ 2) μ) :
    HasLogMoment μ (∫ x, (2 + ‖x‖ ^ 2) ∂μ) := by
  have hb : Integrable (fun x : Euc d => 2 + ‖x‖ ^ 2) μ := (integrable_const _).add hm2
  have hle : ∀ x : Euc d, Real.log (2 + ‖x‖) ≤ 2 + ‖x‖ ^ 2 := fun x => by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + ‖x‖ by positivity)
    nlinarith [sq_nonneg (‖x‖ - 1 / 2), norm_nonneg x]
  have hmeas : Measurable (fun x : Euc d => Real.log (2 + ‖x‖)) :=
    Real.measurable_log.comp (measurable_const.add measurable_norm)
  have hpos : ∀ x : Euc d, 0 ≤ Real.log (2 + ‖x‖) := fun x =>
    Real.log_nonneg (by linarith [norm_nonneg x])
  have hint : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) μ :=
    hb.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hpos x)]; exact hle x)
  exact ⟨hint, integral_mono hint hb hle⟩

theorem r26t3_static_pressure {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) :
    (∀ N, 2 ≤ N → IsProbabilityMeasure (r26t3_Q R N)) ∧
    ∀ r : ℝ, 1 < r → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      eLpNorm (fun X : EucConfig p.d N =>
        ((r26t3_Q R N).rnDeriv (Measure.pi fun _ : Fin N => r26t3_mu R 0) X).toReal)
        (ENNReal.ofReal r) (Measure.pi fun _ : Fin N => r26t3_mu R 0) ≤ ENNReal.ofReal C := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M₀, c, S, hc, hTc⟩ := href 0
  have hd := p.hd
  have hP : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hm2 : Integrable (fun y : Euc p.d => ‖y‖ ^ 2) (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.MS.TcF.tc4_sq_integrable hTc hc
  have hρ : IsRound2Density p.d p.s |M₀| (∫ x, (2 + ‖x‖ ^ 2) ∂(HRS.Whole.withDensityReal (R.ρ 0)))
      (R.ρ 0) := by
    refine ⟨hTc.prob, fun x => ?_, fun _ => s21f_logmoment hm2⟩
    calc R.ρ 0 x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2) := hTc.gauss x
      _ ≤ |M₀| * Real.exp (-c * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ |M₀| * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])) (abs_nonneg _)
      _ = |M₀| := mul_one _
  set M := |M₀|
  set L := ∫ x, (2 + ‖x‖ ^ 2) ∂(HRS.Whole.withDensityReal (R.ρ 0))
  have hGm : Measurable (Function.uncurry fun x y : Euc p.d => rieszKernel p.d p.s (x - y)) :=
    (HRS.MS.S81G.s81g_riesz_meas p.s).comp (measurable_fst.sub measurable_snd)
  constructor
  · obtain ⟨C0, -, hn⟩ := HRS.MS.R2Mt.s92_normalizer_bounds hd p.hs0 p.hs M L p.γ (p.γ + 1) hγ (by linarith)
    intro N hN
    have hW := (hn (R.ρ 0) hρ N hN p.γ ⟨le_rfl, by linarith⟩).1
    show IsProbabilityMeasure (pairGibbs (fun x y => rieszKernel p.d p.s (x - y)) N p.γ
      (HRS.Whole.withDensityReal (R.ρ 0)))
    exact HRS.MS.Wr.wr9_gibbs_prob hW
  · intro r hr
    have hr0 : 0 < r := by linarith
    obtain ⟨C0, -, hn⟩ := HRS.MS.R2Mt.s92_normalizer_bounds hd p.hs0 p.hs M L p.γ (r * p.γ) hγ
      (by nlinarith)
    refine ⟨Real.exp ((r + 1) * C0) ^ (1 / r), fun N hN => ?_⟩
    have h1 := hn (R.ρ 0) hρ N hN p.γ ⟨le_rfl, by nlinarith⟩
    have h2 := hn (R.ρ 0) hρ N hN (r * p.γ) ⟨by nlinarith, le_rfl⟩
    exact HRS.MS.R26T3.s21f_dens_Lr (μ := HRS.Whole.withDensityReal (R.ρ 0)) hGm hr h1.1 h2.1 h1.2 h2.2

end HRS.MS.R26T3
