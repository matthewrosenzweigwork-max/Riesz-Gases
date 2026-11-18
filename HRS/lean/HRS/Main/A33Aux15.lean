import Mathlib
import HRS.Main.A33Aux14
import HRS.Main.A33Aux1

/-!
# Packet A33, helper 15: the limit process (existence part of Proposition A.33)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

/-- The solution concept of `IsLinearFluctuationProcess` for the data `S` and noise level `q`
(fields `init`, `meas`, `gaussian_part`). -/
structure A33Proc (S : A33Setup d) (q : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y₀ : Ω → NegSobolev d (S.J : ℝ)) (Y : ℝ → Ω → NegSobolev d (S.J : ℝ)) : Prop where
  init : ∀ᵐ ω ∂P, Y 0 ω = Y₀ ω
  meas : ∀ t, Measurable (Y t)
  gauss : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ), (∀ a, ts a ∈ Set.Icc 0 S.T) →
    (∀ a, Torus.IsSmooth (φ a)) →
    let G : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (Y (ts a) ω) (φ a) -
        NegSobolev.eval (Y₀ ω) (propagator S.D S.ρ 0 (ts a) (φ a))
    ProbabilityTheory.IndepFun G Y₀ P ∧
      P.map G = multivariateGaussian 0 (Matrix.of fun a b =>
        2 * q * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x : Torus d,
          inner ℝ (Torus.grad (propagator S.D S.ρ r (ts a) (φ a)) x)
            (Torus.grad (propagator S.D S.ρ r (ts b) (φ b)) x) * S.ρ r x)

theorem a33_exists_process (S : A33Setup d) (q : ℝ) (hq : 0 ≤ q)
    (ν₁ : Measure (NegSobolev d (S.J : ℝ))) [IsProbabilityMeasure ν₁] :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (Y₀ : Ω' → NegSobolev d (S.J : ℝ)) (Y : ℝ → Ω' → NegSobolev d (S.J : ℝ)),
      Measurable Y₀ ∧ P'.map Y₀ = ν₁ ∧ A33Proc S q P' Y₀ Y := by
  classical
  obtain ⟨e⟩ := a33_exists_equiv S.hd
  obtain ⟨Ω, mΩ, P, hP, W, hm, h2, hl, hf, hi, hs1, hg⟩ :=
    a33_isonormal (Lp (Euc d) 2 (a33_nu d S.T S.ρ))
  have hI : A33Iso P W := ⟨hm, h2, hl, hf, hi, hs1, hg⟩
  haveI := hP
  have hT0 : (0 : ℝ) ∈ Set.Icc 0 S.T := ⟨le_rfl, S.hT.le⟩
  refine ⟨NegSobolev d (S.J : ℝ) × Ω, inferInstance, ν₁.prod P, inferInstance, fun ω => ω.1,
    fun t ω => if t ∈ Set.Icc 0 S.T then a33_transport S t ω.1 + a33_Gfield S q W t ω.2 else 0,
    measurable_fst, ?_, ?_⟩
  · rw [Measure.map_fst_prod, measure_univ, one_smul]
  refine ⟨?_, ?_, ?_⟩
  · -- initial condition
    have hz := a33_Gfield_zero_ae S q W hI
    have hz' : ∀ᵐ ω ∂(ν₁.prod P), a33_Gfield S q W 0 ω.2 = 0 :=
      Measure.quasiMeasurePreserving_snd.ae hz
    filter_upwards [hz'] with ω hω
    simp only [if_pos hT0]
    rw [S.transport_zero, hω, add_zero]
  · intro t
    by_cases ht : t ∈ Set.Icc 0 S.T
    · simp only [if_pos ht]
      exact ((S.transport_measurable ht e).comp measurable_fst).add
        ((a33_Gfield_meas S q W e hI t).comp measurable_snd)
    · simp only [if_neg ht]
      exact measurable_const
  · intro p ts φ hts hφ G
    set g : Ω → EuclideanSpace ℝ (Fin p) := fun ω₂ => WithLp.toLp 2 fun a =>
      NegSobolev.eval (a33_Gfield S q W (ts a) ω₂) (φ a) with hgdef
    have hGeq : G = fun ω => g ω.2 := by
      funext ω
      refine congrArg (WithLp.toLp 2) (funext fun a => ?_)
      simp only [if_pos (hts a)]
      rw [a33_eval_add_left _ _ (a33_ws_smooth (S.J : ℝ) (hφ a)), S.eval_transport (hts a) e ω.1 (hφ a)]
      show _ + _ - NegSobolev.eval ω.1 (S.U (ts a) (φ a)) = _
      ring
    have hgm : Measurable g :=
      (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a =>
        (a33_eval_measurable e (a33_ws_smooth (S.J : ℝ) (hφ a))).comp
          (a33_Gfield_meas S q W e hI (ts a)))
    refine ⟨?_, ?_⟩
    · rw [hGeq]
      exact (indepFun_prod (μ := ν₁) (ν := P) (X := fun F : NegSobolev d (S.J : ℝ) => F) (Y := g)
        measurable_id hgm).symm
    · rw [hGeq]
      have e1 : (fun ω : NegSobolev d (S.J : ℝ) × Ω => g ω.2) = g ∘ Prod.snd := rfl
      rw [e1, ← Measure.map_map hgm measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
      have hae : g =ᵐ[P] fun ω => (WithLp.toLp 2 fun a => W (a33_vec S q (ts a) (φ a)) ω :
          EuclideanSpace ℝ (Fin p)) := by
        have hall : ∀ᵐ ω ∂P, ∀ a : Fin p, NegSobolev.eval (a33_Gfield S q W (ts a) ω) (φ a) =
            W (a33_vec S q (ts a) (φ a)) ω :=
          Filter.eventually_all.2 fun a => a33_eval_ae S q W e hI (hts a) (hφ a)
        filter_upwards [hall] with ω hω
        exact congrArg (WithLp.toLp 2) (funext hω)
      rw [Measure.map_congr hae]
      have := hg (Fin p) (fun a => a33_vec S q (ts a) (φ a))
      rw [this]
      congr 1
      ext a b
      simp only [Matrix.of_apply]
      exact S.gram q hq (hts a) (hts b) (hφ a) (hφ b)

end HRS.A33
