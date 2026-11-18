import HRS.Main.Det22Aux1
import HRS.Main.Headline

/-!
# Packet DET22, part 2: the deterministic linear solution (`q = 0`) and its identification with `transportField`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Det22

variable {d : ℕ}

/-- `V^{t,0} z = transportField t z` for a dual evolution (`IsDualOn`). -/
theorem det22_VE_eq_transport (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ)
    (VE : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hdual : HRS.GF.IsDualOn D ρ m T VE)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (z : NegSobolev d m) :
    VE t 0 z = HRS.Main.transportField D ρ t m z := by
  unfold HRS.Main.transportField
  have h : (fun k : NonzeroLattice d => NegSobolev.eval z (propagator D ρ 0 t (Torus.realMode k))) =
      NegSobolev.fourierCoeff (VE t 0 z) := by
    funext k
    rw [← HRS.A33.a33_eval_realMode, hdual 0 t le_rfl ht0 htT z _ (HRS.FieldSingAux.isSmooth_realMode k)]
  rw [h, HRS.A33.a33_ofSeq_fourierCoeff]

theorem det22_mvGaussian_zero (p : ℕ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (0 : Matrix (Fin p) (Fin p) ℝ) =
      Measure.dirac 0 := by
  simp [multivariateGaussian, Measure.map_const]

/-- The deterministic linear solution at noise level `q = 0`: `Y^t = V^{t,0} y₀`. -/
theorem det22_linearSol (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (VE : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hdual : HRS.GF.IsDualOn D ρ m T VE)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) T, VE t t = 1)
    (hcont : ∀ y, ContinuousOn (fun p : ℝ × ℝ => VE p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (hT : 0 ≤ T) (y₀ : NegSobolev d m) (Y₀ : Ω → NegSobolev d m) (hY₀ : ∀ ω, Y₀ ω = y₀) :
    IsLinearFluctuationSolution P D ρ m 0 T Y₀ (fun t _ => VE t 0 y₀) := by
  refine ⟨?_, ?_, fun t => measurable_const, ?_⟩
  · refine Eventually.of_forall fun ω => ?_
    show VE 0 0 y₀ = Y₀ ω
    rw [hself 0 ⟨le_rfl, hT⟩, hY₀]; rfl
  · refine Eventually.of_forall fun ω => ?_
    have := (hcont y₀).comp (f := fun t : ℝ => ((t, 0) : ℝ × ℝ)) (by fun_prop)
      (s := Set.Icc 0 T) (fun t ht => ⟨le_rfl, ht.1, ht.2⟩)
    exact this
  · intro p ts φ hts hφ G
    have hG : G = fun _ => 0 := by
      funext ω
      ext a
      show NegSobolev.eval (VE (ts a) 0 y₀) (φ a) -
        NegSobolev.eval (Y₀ ω) (propagator D ρ 0 (ts a) (φ a)) = 0
      rw [hY₀, hdual 0 (ts a) le_rfl (hts a).1 (hts a).2 y₀ (φ a) (hφ a), sub_self]
    have hM : (Matrix.of fun a b : Fin p => 2 * (0 : ℝ) * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
        inner ℝ (Torus.grad (propagator D ρ r (ts a) (φ a)) x)
          (Torus.grad (propagator D ρ r (ts b) (φ b)) x) * ρ r x) = 0 := by
      ext a b; simp
    refine ⟨?_, ?_⟩
    · rw [hG]; exact indepFun_const_left _ _
    · rw [hM, det22_mvGaussian_zero, hG]
      simp [Measure.map_const]

end HRS.Det22
