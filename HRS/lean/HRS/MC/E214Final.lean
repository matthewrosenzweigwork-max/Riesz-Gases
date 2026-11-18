import HRS.MC.E214PD
import HRS.MC.E214H9
import HRS.MC.E214L4
import HRS.MC.E214N11
import HRS.MC.E214N1
import HRS.MC.E214O9

/-!
# E214Final: Corollary 2.14 (`HRS.Main.stationary_tensor_relaxation`) from the covariance-tensor comparison

`stationary_tensor_relaxation_cond` is the statement of `HRS.Main.stationary_tensor_relaxation` with one extra hypothesis,
`hJ`: the comparison `WinJCompare` of the covariance tensors `winJ` of the prepared and the stationary regime (the
statement of `E214Plan.winJ_compare`, the one analytic estimate of the corollary that is not proved).  Everything else
(uniqueness of `K`, the coupled pair, the path-supremum estimate, the relaxation of the correction data, the
stationary limit `Kst`, the covariance clause) is proved without hypotheses and with the standard axioms only.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214Final

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.E214O

variable {d : ℕ}

theorem norm_sub_le_exp' (x y z : ℝ) {C₁ c₁ C₂ c₂ : ℝ} (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hC₂ : 0 < C₂) (hc₂ : 0 < c₂)
    (a : ℝ) (_ha : 0 ≤ a) (h1 : x ≤ C₁ * Real.exp (-c₁ * a)) (h2 : y ≤ C₂ * Real.exp (-c₂ * a)) (hz : z ≤ x + y) :
    z ≤ (C₁ + C₂) * Real.exp (-(min c₁ c₂) * a) := by
  have e1 : Real.exp (-c₁ * a) ≤ Real.exp (-(min c₁ c₂) * a) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left c₁ c₂])
  have e2 : Real.exp (-c₂ * a) ≤ Real.exp (-(min c₁ c₂) * a) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right c₁ c₂])
  nlinarith [mul_le_mul_of_nonneg_left e1 hC₁.le, mul_le_mul_of_nonneg_left e2 hC₂.le]

theorem stationary_cauchy_proof {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}
    (sd : StatDatum S β₀ m hE) (gds : GaussData sd.Ss S.β sd.hEs) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a h : ℝ, 0 ≤ a → 0 ≤ h →
      ‖gds.Kproj T (a + h) - gds.Kproj T a‖ ≤ C * Real.exp (-c * a) := by
  obtain ⟨C, c, hC, hc, H⟩ := HRS.MC.E214N.shift_identity_proof sd gds T hT
  refine ⟨C, c, hC, hc, fun a h ha hh => ?_⟩
  have := H a h ha hh
  rwa [Kproj_eq_of_gd T hT (HRS.MC.E214N.shiftGD_proof sd gds h hh) gds a ha] at this

/-- **Corollary 2.14** (`HRS.Main.stationary_tensor_relaxation`) under the covariance-tensor comparison `hJ`. -/
theorem stationary_tensor_relaxation_cond (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (K : ℝ → projTensor (PathSpace d m T) 3)
    (ε : ℕ → ℝ) (hK : IsWindowEdgeworth S β₀ m T K ε)
    (hJ : ∀ sd : StatDatum S β₀ m hE, WinJCompare sd T hT) :
    ∃ (Kst : projTensor (PathSpace d m T) 3) (C c : ℝ), 0 < C ∧ 0 < c ∧
      (∀ a : ℝ, 0 ≤ a → ‖K a - Kst‖ ≤ C * Real.exp (-c * a)) ∧
      ∀ a : ℝ, 0 ≤ a →
      ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Z₀ Z →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Zs : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Zs →
        covDist P' P'' (windowPath m T a Z) (windowPath m T 0 Zs) ≤ C * Real.exp (-c * a) := by
  obtain ⟨sd⟩ := HRS.MC.E214L.exists_statDatum_proof (hE := hE) (β₀ := β₀) ρβ hρβ
  obtain ⟨pg⟩ := HRS.MC.E214L.exists_pairGD_proof sd
  obtain ⟨C₁, c₁, hC₁, hc₁, h₁⟩ := Kwin_relax_cond_proof pg T hT (hJ sd)
  obtain ⟨C₂, c₂, hC₂, hc₂, h₂⟩ := stationary_cauchy_proof sd pg.gds T hT
  obtain ⟨Kst, hKst⟩ := HRS.MC.E214N.exists_limit_of_cauchy_proof (fun a => pg.gds.Kproj T a) C₂ c₂ hC₂ hc₂ h₂
  obtain ⟨C₃, c₃, hC₃, hc₃, h₃⟩ := HRS.MC.E214H.covariance_relaxation_proof S β₀ m T hE hT ρβ hρβ
  refine ⟨Kst, (C₁ + C₂) + C₃, min (min c₁ c₂) c₃, by positivity, lt_min (lt_min hc₁ hc₂) hc₃, ?_, ?_⟩
  · intro a ha
    have hK1 : K a = pg.gd.Kproj T a := K_eq_Kproj T hT hK pg.gd a ha
    have t1 := h₁ a ha
    have t2 := hKst a ha
    have tri : ‖K a - Kst‖ ≤ ‖pg.gd.Kproj T a - pg.gds.Kproj T a‖ + ‖pg.gds.Kproj T a - Kst‖ := by
      rw [hK1]
      calc ‖pg.gd.Kproj T a - Kst‖ = ‖(pg.gd.Kproj T a - pg.gds.Kproj T a) + (pg.gds.Kproj T a - Kst)‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have := norm_sub_le_exp' _ _ _ hC₁ hc₁ hC₂ hc₂ a ha t1 t2 tri
    refine this.trans ?_
    have e : Real.exp (-(min c₁ c₂) * a) ≤ Real.exp (-(min (min c₁ c₂) c₃) * a) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left (min c₁ c₂) c₃])
    nlinarith [mul_le_mul_of_nonneg_left e (by positivity : (0 : ℝ) ≤ C₁ + C₂),
      Real.exp_pos (-(min (min c₁ c₂) c₃) * a)]
  · intro a ha ν hν Ω' _ P' _ Z₀ Z hZ Ω'' _ P'' _ Zs hZs
    have := h₃ a ha ν hν P' Z₀ Z hZ P'' Zs hZs
    refine this.trans ?_
    have e : Real.exp (-c₃ * a) ≤ Real.exp (-(min (min c₁ c₂) c₃) * a) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right (min c₁ c₂) c₃])
    nlinarith [mul_le_mul_of_nonneg_right (show C₃ ≤ (C₁ + C₂) + C₃ by linarith) (Real.exp_pos (-c₃ * a)).le,
      mul_le_mul_of_nonneg_left e (by positivity : (0 : ℝ) ≤ (C₁ + C₂) + C₃)]

end HRS.MC.E214Final

end
