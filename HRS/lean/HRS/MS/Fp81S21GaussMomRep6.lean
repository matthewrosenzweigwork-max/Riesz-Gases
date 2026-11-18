import HRS.MS.Fp81S21GaussMomRep5
import HRS.MS.Fp81S21PredMap

/-! A common compact-test event from testwise agreement. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111 HRS.MS.S111X1

theorem fp81s21_oscillator_compact_event_of_testwise_agreement
    {d r : ℕ} {Pw m : ℝ}
    {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw)
    (P : Measure Ω) (Z : Ω → OscDual d m)
    (q : Ω → r26t6_Coeff)
    (hfixed : ∀ f : Euc d → ℝ, IsR2Test f →
      (fun ω => fp81s21_chartAction E (q ω) f) =ᵐ[P]
        (fun ω => OscDual.eval (Z ω) f)) :
    ∀ᵐ ω ∂P,
      (∀ f, IsR2Test f →
        fp81s21_chartAction E (q ω) f =
          OscDual.eval (Z ω) f) ∧
      (∀ f, IsR2Test f →
        |OscDual.eval (Z ω) f| ≤
          ‖q ω‖ * (weightedSobolevE r Pw f).toReal) := by
  letI : TopologicalSpace.SeparableSpace (OscSpace d m) :=
    HRS.StaticLimitAux.separable_lp (ι := MultiIndex d)
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  let F : compactSmoothSubmodule d → OscSpace d m × r26t6_Coeff :=
    fun f => (OscSpace.ofFun m f, E.encode f)
  let S := Set.range F
  obtain ⟨D, hDc, hDS, hSD⟩ := TopologicalSpace.exists_countable_dense_subset S
  letI : Countable D := hDc.to_subtype
  have hex : ∀ x : D, ∃ f : compactSmoothSubmodule d, F f = x := by
    intro x
    exact hDS x.property
  let test : D → compactSmoothSubmodule d := fun x => Classical.choose (hex x)
  have htest : ∀ x : D, F (test x) = x := fun x => Classical.choose_spec (hex x)
  have hae : ∀ᵐ ω ∂P, ∀ x : D,
      fp81s21_chartAction E (q ω) (test x) = OscDual.eval (Z ω) (test x) :=
    ae_all_iff.mpr fun x => hfixed (test x) (test x).property
  filter_upwards [hae] with ω hω
  have hall : ∀ f : compactSmoothSubmodule d,
      fp81s21_chartAction E (q ω) f = OscDual.eval (Z ω) f := by
    intro f
    let A : OscSpace d m × r26t6_Coeff → ℝ := fun p =>
      OscDual.toDual (Z ω) p.1 - inner ℝ (q ω) p.2
    have hcont : Continuous A :=
      ((OscDual.toDual (Z ω)).continuous.comp continuous_fst).sub
        (continuous_const.inner continuous_snd)
    have hclosed : IsClosed {p | A p = 0} := isClosed_eq hcont continuous_const
    have hD : D ⊆ {p | A p = 0} := by
      intro p hp
      let x : D := ⟨p, hp⟩
      have hx := hω x
      have hfx := htest x
      change F (test x) = p at hfx
      have ht := OscDual.toDual_ofFun (Z ω) (test x)
        (r2Test_isOscTest m (test x).property).2
      change A p = 0
      rw [← hfx]
      dsimp [A, F]
      rw [ht]
      change OscDual.eval (Z ω) (test x) - fp81s21_chartAction E (q ω) (test x) = 0
      linarith
    have hf : F f ∈ {p | A p = 0} :=
      closure_minimal hD hclosed (hSD ⟨f, rfl⟩)
    change OscDual.toDual (Z ω) (OscSpace.ofFun m f) -
      fp81s21_chartAction E (q ω) f = 0 at hf
    rw [OscDual.toDual_ofFun _ _ (r2Test_isOscTest m f.property).2] at hf
    linarith
  refine ⟨?_, ?_⟩
  · intro f hf
    exact hall ⟨f, hf⟩
  · intro f hf
    rw [← hall ⟨f, hf⟩]
    exact fp81s21_chartAction_weighted_bound E (q ω) f
      (weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP hf))

#print axioms fp81s21_oscillator_compact_event_of_testwise_agreement
end HRS.Fp81.S21
end
