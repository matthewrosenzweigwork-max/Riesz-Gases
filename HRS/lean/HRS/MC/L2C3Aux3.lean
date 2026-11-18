import HRS.MC.L2C3Aux2

/-!
# Packet L2C-3, helper 3: the Lyapunov context and the centering operator on `L²(μ_β)`

* `Ctx R` bundles the constants and operators of the `A_β⁻¹`-Lyapunov functional of the regime
  (density bounds `c₀ ≤ ρ_β ≤ Λ₀`, the inverse `Rop = A⁻¹`, the form bounds `κ₁, κ₂`, the weighted Poincaré
  constant `cP`);
* `l2c3_P` is the centering operator `P x = x - ⟨1, x⟩ 1` on `L²(μ_β)` (`μ_β` a probability measure) and
  `l2c3_P_ae` identifies `P [f]` with the class of `projMean μ_β f`;
* `l2c3_inner_one_Rop`: `A⁻¹` preserves the mean.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

namespace HRS.MC.L2C3

variable {d : ℕ}

instance l2c3_instProb (R : Regime d) : IsProbabilityMeasure (withDensityReal R.ρβ) :=
  MFSemigroup.isProb_withDensityReal R.thermal.1.1

/-- The data of the Lyapunov functional `F(y) = ⟨y, A_β⁻¹ y⟩_{L²(μ_β)}` for a regime. -/
structure Ctx (R : Regime d) where
  c₀ : ℝ
  Λ₀ : ℝ
  cP : ℝ
  κ₁ : ℝ
  κ₂ : ℝ
  hc₀ : 0 < c₀
  hcP : 0 < cP
  hκ₁ : 0 < κ₁
  hκ₂ : 0 < κ₂
  H : FrozenHyp d R.D.s (2 * mStar d + 4) R.β⁻¹ R.β⁻¹ c₀ Λ₀ R.β R.D.V R.ρβ
  hKS : KS (periodicRiesz d R.D.s) R.ρβ Λ₀
  Rop : Lp ℝ 2 (withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 (withDensityReal R.ρβ)
  hRA : ∀ y, ALp hKS R.β (Rop y) = y
  hRA' : ∀ x, Rop (ALp hKS R.β x) = x
  hRs : ∀ x y, inner ℝ (Rop x) y = inner ℝ x (Rop y)
  hform : ∀ y : Lp ℝ 2 (withDensityReal R.ρβ),
    ‖y‖ ^ 2 ≤ κ₁ * inner ℝ y (Rop y) ∧ inner ℝ y (Rop y) ≤ κ₂ * ‖y‖ ^ 2
  hPo : ∀ f : Torus d → ℝ, Torus.IsCk 1 f → pair (withDensityReal R.ρβ) f = 0 →
    cP * l2Inner (withDensityReal R.ρβ) f f ≤ ∫ x, R.ρβ x * ‖Torus.grad f x‖ ^ 2

theorem l2c3_ctx (R : Regime d) : Nonempty (Ctx R) := by
  obtain ⟨hth, hsm, hpos⟩ := R.thermal
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨c₀, Λ₀, H⟩ := PDE.MFPair.frozenHyp_of_smooth (d := d) R.D.s R.D.hs0 R.D.hsd R.β R.hβ
    R.D.V R.hV R.ρβ hth hsm hpos (2 * PDE.mStar d + 4)
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hKS := KS_of_frozen hd1 H
  have hρc : Continuous R.ρβ := H.cont (by omega)
  obtain ⟨Rop, hRA', hRA, hRs, -⟩ := exists_inverse hd1 R.D.s H.hs0 H.hsd hKS hρc R.β H.hβ.le
  obtain ⟨κ₁, κ₂, hκ₁, hκ₂, hform⟩ :=
    HRS.MC.L2C1.l2c1_form_bounds hd1 R.D.s H.hs0 H.hsd hKS hρc R.β H.hβ.le Rop hRA
  obtain ⟨cP, hcP, hPoin⟩ := exists_weighted_poincare (d := d) c₀ Λ₀ H.hc₀
  exact ⟨⟨c₀, Λ₀, cP, κ₁, κ₂, H.hc₀, hcP, hκ₁, hκ₂, H, hKS, Rop, hRA, hRA', hRs, hform,
    hPoin R.ρβ H.thermal.1 hρc H.hlow H.le_Lam⟩⟩

namespace Ctx

variable {R : Regime d}

theorem hprob (Cx : Ctx R) : IsProbDensity R.ρβ := Cx.H.thermal.1

theorem hρc (Cx : Ctx R) : Continuous R.ρβ := by
  have h3 := ClassicalPart.three_le_mStar d
  exact Cx.H.cont (by omega)

theorem hlow' (Cx : Ctx R) : ∀ x, Cx.c₀ ≤ R.ρβ x := Cx.H.hlow

theorem hup (Cx : Ctx R) : ∀ x, R.ρβ x ≤ Cx.Λ₀ := Cx.H.le_Lam

theorem hd1 (_Cx : Ctx R) : 1 ≤ d := by have := R.hd; omega

theorem hΛ₀ (Cx : Ctx R) : 0 < Cx.Λ₀ := lt_of_lt_of_le Cx.hc₀ ((Cx.hlow' 0).trans (Cx.hup 0))

end Ctx

/-! ### The centering operator -/

section Center

variable (μ : Measure (Torus d)) [IsFiniteMeasure μ]

/-- The constant function `1` in `L²(μ)`. -/
def l2c3_one : Lp ℝ 2 μ := (memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ))

theorem l2c3_one_ae : ⇑(l2c3_one μ) =ᵐ[μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _

/-- `P x = x - ⟨1, x⟩ 1`. -/
def l2c3_P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.id ℝ _ - (innerSL ℝ (l2c3_one μ)).smulRight (l2c3_one μ)

theorem l2c3_P_apply (x : Lp ℝ 2 μ) : l2c3_P μ x = x - inner ℝ (l2c3_one μ) x • l2c3_one μ := rfl

end Center

section Center2

variable {ρ : Torus d → ℝ} [IsFiniteMeasure (withDensityReal ρ)]

theorem l2c3_inner_one (x : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (l2c3_one (withDensityReal ρ)) x = ∫ y, x y ∂(withDensityReal ρ) := by
  rw [innerLp_eq_l2Inner]
  unfold l2Inner
  refine integral_congr_ae ?_
  filter_upwards [l2c3_one_ae (withDensityReal ρ)] with y hy
  rw [hy, one_mul]

theorem l2c3_P_ae [IsProbabilityMeasure (withDensityReal ρ)] (y : Lp ℝ 2 (withDensityReal ρ))
    {f : Torus d → ℝ} (hy : ⇑y =ᵐ[withDensityReal ρ] f) :
    ⇑(l2c3_P (withDensityReal ρ) y) =ᵐ[withDensityReal ρ] projMean (withDensityReal ρ) f := by
  rw [l2c3_P_apply]
  filter_upwards [Lp.coeFn_sub y (inner ℝ (l2c3_one (withDensityReal ρ)) y • l2c3_one (withDensityReal ρ)),
    Lp.coeFn_smul (inner ℝ (l2c3_one (withDensityReal ρ)) y) (l2c3_one (withDensityReal ρ)),
    l2c3_one_ae (withDensityReal ρ), hy] with x h1 h2 h3 h4
  rw [h1]
  simp only [Pi.sub_apply]
  rw [h2]
  simp only [Pi.smul_apply, smul_eq_mul, h3, mul_one, h4, projMean, pair]
  rw [l2c3_inner_one]
  congr 1
  exact integral_congr_ae hy

theorem l2c3_inner_one_TLp {g : Torus d → ℝ} {Λ : ℝ} (H : KS g ρ Λ)
    (u : Lp ℝ 2 (withDensityReal ρ)) [IsProbabilityMeasure (withDensityReal ρ)] :
    inner ℝ (l2c3_one (withDensityReal ρ)) (TLp H u) = 0 := by
  rw [innerLp_eq_l2Inner]
  have : l2Inner (withDensityReal ρ) ⇑(l2c3_one (withDensityReal ρ)) ⇑(TLp H u) =
      l2Inner (withDensityReal ρ) (fun _ => (1 : ℝ))
        (Kop g (withDensityReal ρ) (projMean (withDensityReal ρ) ⇑u)) :=
    l2Inner_congr_ae (l2c3_one_ae _) (TLp_coe H u)
  rw [this]
  unfold l2Inner
  simp only [one_mul]
  have := MFSemigroup.pair_projMean (withDensityReal ρ)
    (fun x => ∫ y, g (x - y) * (projMean (withDensityReal ρ) ⇑u) y ∂(withDensityReal ρ))
  exact this

theorem l2c3_inner_one_A {g : Torus d → ℝ} {Λ : ℝ} (H : KS g ρ Λ) (β : ℝ)
    (u : Lp ℝ 2 (withDensityReal ρ)) [IsProbabilityMeasure (withDensityReal ρ)] :
    inner ℝ (l2c3_one (withDensityReal ρ)) (ALp H β u) = inner ℝ (l2c3_one (withDensityReal ρ)) u := by
  have e : ALp H β u = u + β • TLp H u := rfl
  rw [e, inner_add_right, real_inner_smul_right, l2c3_inner_one_TLp, mul_zero, add_zero]

end Center2

theorem l2c3_inner_one_Rop {R : Regime d} (Cx : Ctx R) (y : Lp ℝ 2 (withDensityReal R.ρβ)) :
    inner ℝ (l2c3_one (withDensityReal R.ρβ)) (Cx.Rop y) =
      inner ℝ (l2c3_one (withDensityReal R.ρβ)) y := by
  conv_rhs => rw [← Cx.hRA y]
  rw [l2c3_inner_one_A]

end HRS.MC.L2C3
