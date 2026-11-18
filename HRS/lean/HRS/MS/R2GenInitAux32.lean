import HRS.MS.R2GenInitAux31
import HRS.MS.GenPathAux58

/-!
# S10.5 window comparison, packet D3: coordinate arrays of the linear window process and of the Gaussian window martingale

Window analogues of `GenPathAux49-57`: the array `Ψ_c(n,α) = η₀(U(0,b+s_n)φ_α)` of the prescribed initial field, the array
`F(n,α) = ⟨G_{b+s_n}, y1(s_n,α)⟩` of the Gaussian martingale, the independence/law of the Gaussian part of `Y`
(`s105_VD_law`, `s105_Vc_props`) and `s105_D_law`, `s105_D_range`, `s105_Y_array_law`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.Uniform.Q54c

variable {d : ℕ}

/-- The coordinate array `η₀(U^{0,b+s n}φ_α)` of the prescribed initial field along the window. -/
def s105Psic (C : WholeCoeff d) (m b : ℝ) {T : ℝ} {Ω : Type*} (s : ℕ → Set.Icc (0 : ℝ) T)
    (η₀ : Ω → (Euc d → ℝ) → ℝ) (ζ : Ω) : ℕ × MultiIndex d → ℝ :=
  fun i => η₀ ζ (propagatorW C 0 (b + s i.1) (oscTestFun m i.2))

/-- The array `(n,α) ↦ ⟨G_{b+s n}, y1(s n, α)⟩`. -/
def s105FArr (m T b : ℝ) {Ω : Type*} (s : ℕ → Set.Icc (0 : ℝ) T) (G : ℝ → Ω → KSpace d m T) (ζ : Ω) :
    ℕ × MultiIndex d → ℝ :=
  fun i => inner ℝ (G (b + s i.1) ζ) (s52y1 m T (s i.1) i.2)

theorem s105_VD_law (C : WholeCoeff d) (m b q T : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d m)
    (hb : 0 ≤ b)
    (hY : IsLinearFluctuationSolutionW P C m q (b + T) η₀ Y)
    (s : ℕ → Set.Icc (0 : ℝ) T) {p : ℕ} (f : Fin p → ℕ × MultiIndex d) :
    IndepFun (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s (fun t ζ => Y (b + t) ζ) ζ (f a) -
        s105Psic C m b s η₀ ζ (f a) : EuclideanSpace ℝ (Fin p))) η₀ P ∧
    P.map (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s (fun t ζ => Y (b + t) ζ) ζ (f a) -
        s105Psic C m b s η₀ ζ (f a) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun i j => noiseCovW C q (b + (s (f i).1 : ℝ)) (b + (s (f j).1 : ℝ))
        (oscTestFun m (f i).2) (oscTestFun m (f j).2)) := by
  have h := hY.gaussian_part p (fun a => b + (s (f a).1 : ℝ)) (fun a => oscTestFun m (f a).2)
    (fun a => ⟨by linarith [(s (f a).1).2.1], by linarith [(s (f a).1).2.2]⟩)
    (fun a => s56_isOscTest m (f a).2)
  simp only [OscDual.eval_oscTestFun] at h
  exact h

theorem s105_Vc_props (C : WholeCoeff d) (m b q T : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d m)
    (hb : 0 ≤ b) (hYm : ∀ t, Measurable (Y t))
    (hY : IsLinearFluctuationSolutionW P C m q (b + T) η₀ Y)
    (s : ℕ → Set.Icc (0 : ℝ) T)
    (hη : ∀ i : ℕ × MultiIndex d, AEMeasurable (fun ζ => s105Psic C m b s η₀ ζ i) P)
    {p : ℕ} (f : Fin p → ℕ × MultiIndex d) :
    AEMeasurable (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s (fun t ζ => Y (b + t) ζ) ζ (f a) -
        s105Psic C m b s η₀ ζ (f a) : EuclideanSpace ℝ (Fin p))) P ∧
    AEMeasurable (fun ζ => (WithLp.toLp 2 fun a => s105Psic C m b s η₀ ζ (f a) : EuclideanSpace ℝ (Fin p))) P ∧
    IndepFun (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s (fun t ζ => Y (b + t) ζ) ζ (f a) -
        s105Psic C m b s η₀ ζ (f a) : EuclideanSpace ℝ (Fin p)))
      (fun ζ => (WithLp.toLp 2 fun a => s105Psic C m b s η₀ ζ (f a) : EuclideanSpace ℝ (Fin p))) P := by
  obtain ⟨hind, hlaw⟩ := s105_VD_law C m b q T P η₀ Y hb hY s f
  have hV0m : Measurable (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s (fun t ζ => Y (b + t) ζ) ζ (f a) :
      EuclideanSpace ℝ (Fin p))) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => (measurable_pi_apply (f a)).comp
        (s56_Psi0_meas s (fun t ζ => Y (b + t) ζ) (fun t => hYm (b + t))))
  have hVcm : AEMeasurable (fun ζ => (WithLp.toLp 2 fun a => s105Psic C m b s η₀ ζ (f a) :
      EuclideanSpace ℝ (Fin p))) P :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp_aemeasurable
      (aemeasurable_pi_iff.2 fun a => hη (f a))
  have hDm : AEMeasurable (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s (fun t ζ => Y (b + t) ζ) ζ (f a) -
      s105Psic C m b s η₀ ζ (f a) : EuclideanSpace ℝ (Fin p))) P := by
    have : (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s (fun t ζ => Y (b + t) ζ) ζ (f a) -
        s105Psic C m b s η₀ ζ (f a) : EuclideanSpace ℝ (Fin p))) =
        fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s (fun t ζ => Y (b + t) ζ) ζ (f a) :
          EuclideanSpace ℝ (Fin p)) - (WithLp.toLp 2 fun a => s105Psic C m b s η₀ ζ (f a) :
          EuclideanSpace ℝ (Fin p)) := by
      funext ζ; ext a; simp
    rw [this]
    exact hV0m.aemeasurable.sub hVcm
  refine ⟨hDm, hVcm, ?_⟩
  have hmeasF : Measurable (fun g : (Euc d → ℝ) → ℝ => (WithLp.toLp 2 fun a : Fin p =>
      g (propagatorW C 0 (b + (s (f a).1 : ℝ)) (oscTestFun m (f a).2)) : EuclideanSpace ℝ (Fin p))) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => measurable_pi_apply _)
  exact hind.comp measurable_id hmeasF

end HRS.MS.R2GenInit
