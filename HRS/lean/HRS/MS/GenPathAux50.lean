import HRS.MS.GenPathAux49

/-!
# S5.6 packet P7h: independence, a.e. measurability of the coordinate arrays of the initial path
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole

variable {d : ℕ}

theorem s56_Vc_props (b : WholeBounds d) (S : WholeSetup b) (N : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d b.m)
    (hYm : ∀ t, Measurable (Y t))
    (hY : IsLinearFluctuationSolutionW P (S.coeff N) b.m (S.q N) b.T (fun ζ f => S.A N * η₀ ζ f) Y)
    (s : ℕ → Set.Icc (0 : ℝ) b.T)
    (hη : ∀ i : ℕ × MultiIndex d, AEMeasurable (fun ζ => s56Psic S N s η₀ ζ i) P)
    {p : ℕ} (f : Fin p → ℕ × MultiIndex d) :
    AEMeasurable (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) - s56Psic S N s η₀ ζ (f a) :
        EuclideanSpace ℝ (Fin p))) P ∧
    AEMeasurable (fun ζ => (WithLp.toLp 2 fun a => s56Psic S N s η₀ ζ (f a) : EuclideanSpace ℝ (Fin p))) P ∧
    IndepFun (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) - s56Psic S N s η₀ ζ (f a) :
        EuclideanSpace ℝ (Fin p)))
      (fun ζ => (WithLp.toLp 2 fun a => s56Psic S N s η₀ ζ (f a) : EuclideanSpace ℝ (Fin p))) P := by
  obtain ⟨hind, hlaw⟩ := s56_VD_law b S N P η₀ Y hY s f
  have hV0m : Measurable (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) : EuclideanSpace ℝ (Fin p))) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => (measurable_pi_apply (f a)).comp (s56_Psi0_meas s Y hYm))
  have hVcm : AEMeasurable (fun ζ => (WithLp.toLp 2 fun a => s56Psic S N s η₀ ζ (f a) :
      EuclideanSpace ℝ (Fin p))) P :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp_aemeasurable
      (aemeasurable_pi_iff.2 fun a => hη (f a))
  have hDm : AEMeasurable (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) - s56Psic S N s η₀ ζ (f a) :
      EuclideanSpace ℝ (Fin p))) P := by
    have : (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) - s56Psic S N s η₀ ζ (f a) :
        EuclideanSpace ℝ (Fin p))) = fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) :
          EuclideanSpace ℝ (Fin p)) - (WithLp.toLp 2 fun a => s56Psic S N s η₀ ζ (f a) :
          EuclideanSpace ℝ (Fin p)) := by
      funext ζ; ext a; simp
    rw [this]
    exact hV0m.aemeasurable.sub hVcm
  refine ⟨hDm, hVcm, ?_⟩
  have hmeasF : Measurable (fun g : (Euc d → ℝ) → ℝ => (WithLp.toLp 2 fun a : Fin p =>
      g (propagatorW (S.coeff N) 0 (s (f a).1) (oscTestFun b.m (f a).2)) : EuclideanSpace ℝ (Fin p))) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => measurable_pi_apply _)
  exact hind.comp measurable_id hmeasF

end HRS.MS.GenPath
