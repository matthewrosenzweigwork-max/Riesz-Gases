import HRS.ME.UIPath
import HRS.MD.EQGaussWindow
import HRS.MD.EQGaussLyapDet

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathInitial

open HRS HRS.Main

variable {d : ℕ}

/-- Helper (packet IR4): a vector of a.e. measurable real coordinates is a.e. measurable in `ℝ^p`. -/
theorem p_ir4_aemeasurable_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℕ}
    {f : Fin p → Ω → ℝ} (hf : ∀ a, AEMeasurable (f a) μ) :
    AEMeasurable (fun ω => (WithLp.toLp 2 fun a => f a ω : EuclideanSpace ℝ (Fin p))) μ :=
  (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp_aemeasurable
    ((aemeasurable_pi_iff (g := fun ω a => f a ω)).2 hf)

/-- Helper (packet IR4): evaluation at a smooth test function is measurable on `E_m`. -/
theorem p_ir4_eval_measurable {m : ℝ} {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    Measurable fun F : NegSobolev d m => NegSobolev.eval F ψ :=
  (HRS.MD.EQGaussWindow.eqgw_eval_continuous hψ).measurable

/-- Helper (packet IR4): the frozen propagator `U^{0,t} φ` of a smooth test is smooth (`t ≥ 0`). -/
theorem p_ir4_prop_smooth (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) {t : ℝ} (ht : 0 ≤ t) :
    Torus.IsSmooth (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 t φ) :=
  HRS.MD.EQGaussLyapDet.eqgld_prop_smooth (by omega) hs0 hsd V hV hβ ρβ hρβ.1 hρS hρpos φ hφ
    0 t le_rfl ht

/-- **R4** (identification of the limit vector; scope note, R4).  For a solution `Y` of the linearised equation
(`IsLinearFluctuationSolution`, background `ρ ≡ ρβ`, `q = β⁻¹`) with initial value `η₀`, finitely many smooth
tests `φ_a` and times `t_a ∈ [0,T]`, the Gaussian part `G'_a = ⟨φ_a, Y^{t_a}⟩ - ⟨U^{0,t_a}φ_a, η₀⟩` is an
a.e. measurable Gaussian vector with the noise covariance (`noiseCovMatrix` is syntactically the matrix of
`gaussian_part` for `ρ = fun _ => ρβ`, `q = β⁻¹`), independent of `η₀`, and the limit vector of R3 equals, a.s.,
the finite-dimensional vector `(⟨(toPath m T Y) t_a, φ_a⟩)_a` of the limit path (only a.s.: `toPath` is the `0`
path off the null set where `Y` is not continuous on `[0,T]`).  `AEMeasurable η₀` is not assumed: it follows from
`hY.init` and `hY.meas 0`.  Route: `hY.gaussian_part p ts φ hts hφ` (with `IndepFun.symm`), `hY.cont`
(`toPath m T Y ω = Y · ω` on `[0,T]` when `Y · ω` is continuous there), measurability of `eval · ψ` for the
smooth `ψ = U^{0,t_a}φ_a`. -/
theorem limit_vector_identification (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 ≤ T)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P' (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m β⁻¹ T η₀ Y)
    (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    ∃ G' : Ω' → EuclideanSpace ℝ (Fin p), AEMeasurable G' P' ∧
      law P' G' = ProbabilityTheory.multivariateGaussian 0
        (noiseCovMatrix (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) β⁻¹ ts φ) ∧
      ProbabilityTheory.IndepFun η₀ G' P' ∧
      ∀ᵐ ω' ∂P', (WithLp.toLp 2 fun a =>
          NegSobolev.eval (η₀ ω')
            (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (ts a) (φ a))
            + G' ω' a : EuclideanSpace ℝ (Fin p)) =
        (WithLp.toLp 2 fun a =>
          NegSobolev.eval ((toPath m T Y ω').at' ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p)) := by
  obtain ⟨hind, hlaw⟩ := hY.gaussian_part p ts φ hts hφ
  have hη : AEMeasurable η₀ P' := (hY.meas 0).aemeasurable.congr hY.init
  refine ⟨fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (ts a) ω) (φ a)
      - NegSobolev.eval (η₀ ω) (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (ts a) (φ a))
      : EuclideanSpace ℝ (Fin p)), ?_, ?_, ?_, ?_⟩
  · apply p_ir4_aemeasurable_toLp
    intro a
    exact AEMeasurable.sub
      ((p_ir4_eval_measurable (hφ a)).comp_aemeasurable (hY.meas (ts a)).aemeasurable)
      ((p_ir4_eval_measurable
        (p_ir4_prop_smooth hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos (φ a) (hφ a) (hts a).1)).comp_aemeasurable hη)
  · exact hlaw
  · exact hind.symm
  · filter_upwards [hY.cont] with ω hω
    have hc : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω :=
      continuousOn_iff_continuous_domRestrict.1 hω
    have hat : ∀ a, (toPath m T Y ω).at' ⟨ts a, hts a⟩ = Y (ts a) ω := fun a => by
      simp [toPath, hc, PathSpace.at']
    congr 1
    funext a
    simp only [hat]
    ring

end HRS.ME.UIPathInitial
