import HRS.MC.S7FCDefs
import HRS.Sections.AllTimeAux1

/-!
# `field_chaos` packets D1a/D1b (worker fcw4): proofs of `s7_FC_D1_prep` and `s7_FC_D1_linear`

Statements copied verbatim from `HRS/MC/S7FCPlan.lean` (spec, sorry); proofs here, no sorried module imported.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW4

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec
open HRS.MC.Sec7.FCPlan

variable {d : ℕ}

lemma S7FCW4_dyn (R : Regime d) : (s7fcPrep R).dyn = R.D := (alltime_D_eq R).symm

lemma S7FCW4_rho_eq (R : Regime d) {t : ℝ} (ht : 0 ≤ t) : (s7fcPrep R).ρ t = R.ρ t := by
  show R.ρ (max t 0) = R.ρ t
  rw [max_eq_left ht]

lemma S7FCW4_refMeasure (R : Regime d) (N : ℕ) :
    (s7fcPrep R).refMeasure N 0 =
      modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀) := by
  show modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ (max 0 0))) = _
  rw [max_self, R.init]

/-- Classical adjoint solutions on `[0,t]` only see `ρ` on `[0,t]`. -/
lemma S7FCW4_isCAS_iff (D : DynData d) (ρ ρ' : ℝ → Torus d → ℝ) (h : ∀ s, 0 ≤ s → ρ s = ρ' s)
    (t : ℝ) (φ : Torus d → ℝ) (f : ℝ → Torus d → ℝ) :
    IsClassicalAdjointSolution D ρ t φ f ↔ IsClassicalAdjointSolution D ρ' t φ f := by
  have key : ∀ {ρ ρ' : ℝ → Torus d → ℝ}, (∀ s, 0 ≤ s → ρ s = ρ' s) →
      IsClassicalAdjointSolution D ρ t φ f → IsClassicalAdjointSolution D ρ' t φ f := by
    intro ρ ρ' h hf
    refine ⟨hf.c2, hf.cont_c2, hf.terminal, ?_, ?_⟩
    · intro x r hr
      have e := h r (le_of_lt hr.1)
      have := hf.time_deriv x r hr
      rw [e] at this
      exact this
    · have e : ∀ p : Set.Icc (0 : ℝ) t × Torus d,
          backwardGenerator D (ρ p.1) (f p.1) p.2 = backwardGenerator D (ρ' p.1) (f p.1) p.2 :=
        fun p => by rw [h p.1.1 p.1.2.1]
      exact (hf.cont_time_deriv).congr e
  exact ⟨key h, key fun s hs => (h s hs).symm⟩

open Classical in
lemma S7FCW4_dite_congr (P P' : (ℝ → Torus d → ℝ) → Prop) (hP : P = P') (r : ℝ) :
    (if h : ∃ f, P f then h.choose r else 0) = (if h : ∃ f, P' f then h.choose r else 0) := by
  subst hP
  rfl

/-- The adjoint propagator depends on `ρ` only through `ρ` on `[0,∞)`. -/
lemma S7FCW4_propagator_congr (D : DynData d) (ρ ρ' : ℝ → Torus d → ℝ) (h : ∀ s, 0 ≤ s → ρ s = ρ' s)
    (r t : ℝ) (φ : Torus d → ℝ) : propagator D ρ r t φ = propagator D ρ' r t φ := by
  have hfun : IsClassicalAdjointSolution D ρ t φ = IsClassicalAdjointSolution D ρ' t φ := by
    funext f
    exact propext (S7FCW4_isCAS_iff D ρ ρ' h t φ f)
  unfold propagator
  exact S7FCW4_dite_congr _ _ hfun r

theorem s7_FC_D1_prep_proof (R : Regime d) :
    (s7fcPrep R).dyn = R.D ∧ (∀ t : ℝ, 0 ≤ t → (s7fcPrep R).ρ t = R.ρ t) ∧
      (s7fcPrep R).μ0 = withDensityReal R.ρ₀ ∧
      ∀ N : ℕ, (s7fcPrep R).refMeasure N 0 =
        modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal R.ρ₀) := by
  exact ⟨S7FCW4_dyn R, fun t ht => S7FCW4_rho_eq R ht, rfl, S7FCW4_refMeasure R⟩

theorem s7_FC_D1_linear_proof (R : Regime d) (r : ℝ) (hr : (d : ℝ) + 2 < r) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    IsCenteredGaussianWithCov r (law P' (η 0))
        (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) ∧
      ∀ T' : ℝ, HRS.Main.IsPreparedLinear (s7fcPrep R) r T' (law P' (η 0)) P' (η 0) η := by
  obtain ⟨Y₀, hcov, hlin⟩ := hη
  have hinit : η 0 =ᵐ[P'] Y₀ := (hlin 0).init
  have hlaw : law P' (η 0) = law P' Y₀ := Measure.map_congr hinit
  refine ⟨?_, fun T' => ?_⟩
  · rw [hlaw]
    exact hcov
  · have hT := hlin T'
    refine ⟨(hlin 0).meas 0, rfl, ?_⟩
    rw [S7FCW4_dyn R]
    refine ⟨Eventually.of_forall fun _ => rfl, hT.cont, hT.meas, ?_⟩
    intro p ts φ hts hφ
    dsimp only
    obtain ⟨hind, hlawG⟩ := hT.gaussian_part p ts φ hts hφ
    have hSρ : ∀ s, 0 ≤ s → (s7fcPrep R).ρ s = R.ρ s := fun s hs => S7FCW4_rho_eq R hs
    have hprop : ∀ r t φ', propagator R.D (s7fcPrep R).ρ r t φ' = propagator R.D R.ρ r t φ' :=
      fun r t φ' => S7FCW4_propagator_congr R.D _ _ hSρ r t φ'
    simp only [hprop]
    have hGR : IndepFun (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (η (ts a) ω) (φ a) -
        NegSobolev.eval (η 0 ω) (propagator R.D R.ρ 0 (ts a) (φ a))) : Ω' → EuclideanSpace ℝ (Fin p))
        (η 0) P' :=
      hind.congr (by filter_upwards [hinit] with ω hω; rw [hω]) hinit.symm
    have hlawR : law P' (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (η (ts a) ω) (φ a) -
        NegSobolev.eval (η 0 ω) (propagator R.D R.ρ 0 (ts a) (φ a))) : Ω' → EuclideanSpace ℝ (Fin p)) =
        law P' (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (η (ts a) ω) (φ a) -
          NegSobolev.eval (Y₀ ω) (propagator R.D R.ρ 0 (ts a) (φ a))) : Ω' → EuclideanSpace ℝ (Fin p)) :=
      Measure.map_congr (by filter_upwards [hinit] with ω hω; rw [hω])
    refine ⟨hGR, ?_⟩
    rw [hlawR, hlawG]
    congr 1
    ext a b
    simp only [Matrix.of_apply, R.hDβ]
    congr 1
    exact setIntegral_congr_fun measurableSet_Icc (fun r hr => by simp only [hSρ r hr.1])

end HRS.MC.Sec7.S7FCW4

end
