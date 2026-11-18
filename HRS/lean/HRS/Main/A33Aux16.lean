import Mathlib
import HRS.Main.A33Aux15

/-!
# Packet A33, helper 16: uniqueness of the finite-dimensional laws (Proposition A.33)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

theorem a33_unique (S : A33Setup d) (q : ℝ) (e : ℕ ≃ NonzeroLattice d)
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (ν₁ : Measure (NegSobolev d (S.J : ℝ)))
    (Y₀₁ : Ω₁ → NegSobolev d (S.J : ℝ)) (Y₀₂ : Ω₂ → NegSobolev d (S.J : ℝ))
    (Y₁ : ℝ → Ω₁ → NegSobolev d (S.J : ℝ)) (Y₂ : ℝ → Ω₂ → NegSobolev d (S.J : ℝ))
    (hl₁ : P₁.map Y₀₁ = ν₁) (hl₂ : P₂.map Y₀₂ = ν₁)
    (h₁ : A33Proc S q P₁ Y₀₁ Y₁) (h₂ : A33Proc S q P₂ Y₀₂ Y₂)
    (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc 0 S.T)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    P₁.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Y₁ (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) =
      P₂.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Y₂ (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) := by
  obtain ⟨K, hK0, hK⟩ := S.U_bound
  set z : NegSobolev d (S.J : ℝ) → EuclideanSpace ℝ (Fin p) := fun F => WithLp.toLp 2 fun a =>
    NegSobolev.eval F (propagator S.D S.ρ 0 (ts a) (φ a)) with hz
  have hzm : Measurable z :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a =>
      a33_eval_measurable e (a33_ws_of_memSobolev (hK (hts a) (hφ a)).1))
  -- the law of a process, in terms of the law of `G` and of the initial field
  have key : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Y₀ : Ω → NegSobolev d (S.J : ℝ)) (Y : ℝ → Ω → NegSobolev d (S.J : ℝ))
      (h : A33Proc S q P Y₀ Y) (hl : P.map Y₀ = ν₁),
      P.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) =
      (multivariateGaussian 0 (Matrix.of fun a b =>
        2 * q * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x : Torus d,
          inner ℝ (Torus.grad (propagator S.D S.ρ r (ts a) (φ a)) x)
            (Torus.grad (propagator S.D S.ρ r (ts b) (φ b)) x) * S.ρ r x)) ∗ (ν₁.map z) := by
    intro Ω _ P _ Y₀ Y h hl
    obtain ⟨hind, hlaw⟩ := h.gauss p ts φ hts hφ
    set G : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (Y (ts a) ω) (φ a) -
        NegSobolev.eval (Y₀ ω) (propagator S.D S.ρ 0 (ts a) (φ a)) with hG
    have hY₀ : AEMeasurable Y₀ P := (h.meas 0).aemeasurable.congr h.init
    have hZ : AEMeasurable (z ∘ Y₀) P := hzm.comp_aemeasurable hY₀
    have hXm : Measurable (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) :=
      (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a =>
        (a33_eval_measurable e (a33_ws_smooth (S.J : ℝ) (hφ a))).comp (h.meas (ts a)))
    have hGm : AEMeasurable G P := by
      have : G = fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (ts a) ω) (φ a) :
          EuclideanSpace ℝ (Fin p)) - (z ∘ Y₀) ω := by
        funext ω
        ext a
        simp [hG, hz]
      rw [this]
      exact hXm.aemeasurable.sub hZ
    have hindZ : IndepFun G (z ∘ Y₀) P := hind.comp measurable_id hzm
    have hX : (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) = G + (z ∘ Y₀) := by
      funext ω
      ext a
      simp [hG, hz]
    rw [hX, hindZ.map_add_eq_map_conv_map₀ hGm hZ, hlaw]
    congr 1
    rw [← hl]
    exact (AEMeasurable.map_map_of_aemeasurable hzm.aemeasurable hY₀).symm
  rw [key P₁ Y₀₁ Y₁ h₁ hl₁, key P₂ Y₀₂ Y₂ h₂ hl₂]

end HRS.A33
