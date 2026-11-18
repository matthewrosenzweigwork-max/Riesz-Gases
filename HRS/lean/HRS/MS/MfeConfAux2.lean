import HRS.MS.SuppU8
import HRS.Whole.AppendixBEnergy

/-!
# S.B.1 (sub-Coulomb alternative): the affine part of the transport has zero fractional derivative

TeX S L11136-11144: for `V(x) = ½ xᵀQx + b·x + c` one has `|∇|^{a/2}∇V = 0` "as a homogeneous distribution" (`a/2 > 1`).  In
the repository the transport bound is `HasFracTransportBound α p v K` (`IsFracDerivRep`, a Schwartz-test identity), so the claim
needed is `IsFracDerivRep α (affine) 0` for `α > 1`.  This file proves it (`sb1_fracDeriv_affine`) and the consequence for
the transport bound (`sb1_transport_add_affine`: `HasFracTransportBound α p u K → HasFracTransportBound α p (u + Qx + b) (K + ‖Q‖)`).

Route: the `U8` representation `|D|^α φ = M⁻¹ ∫ ‖y‖^{-d-α} Δ_y^ℓ φ dy` (`u8_Lam_eq`, `ℓ = ⌊α⌋+1 ≥ 2`), the pointwise decay
`|·| ≲ ⟨x⟩^{-(b+α)}` with `b + α > d + 1` (possible since `α > 1`), Fubini, and the adjoint identity of the central difference for
a field of linear growth (the `U8` adjoint is for bounded fields); an affine field is annihilated by any difference of order `≥ 2`.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace HRS.MS.MfeConf

open HRS.U8

variable {d : ℕ}

/-! ### Differences of affine functions -/

theorem sb1_fd_zero (L : List (EuclideanSpace ℝ (Fin d))) :
    u8_fd L (fun _ => (0 : ℂ)) = fun _ => 0 := by
  induction L with
  | nil => rfl
  | cons h hs ih =>
    rw [u8_fd_cons]
    have : (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℂ) - 0) = fun _ => 0 := by
      funext x; simp
    rw [this]
    exact ih

theorem sb1_fd_const (c : ℂ) (h : EuclideanSpace ℝ (Fin d)) (hs : List (EuclideanSpace ℝ (Fin d))) :
    u8_fd (h :: hs) (fun _ => c) = fun _ => 0 := by
  rw [u8_fd_cons]
  have : (fun _ : EuclideanSpace ℝ (Fin d) => c - c) = fun _ => 0 := by
    funext x; simp
  rw [this]
  exact sb1_fd_zero hs

theorem sb1_fd_affine (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (e : ℝ)
    (L : List (EuclideanSpace ℝ (Fin d))) (hL : 2 ≤ L.length) :
    u8_fd L (fun x => ((ℓ x + e : ℝ) : ℂ)) = fun _ => 0 := by
  match L, hL with
  | h :: k :: hs, _ =>
    rw [u8_fd_cons]
    have : (fun x : EuclideanSpace ℝ (Fin d) => ((ℓ (x + h) + e : ℝ) : ℂ) - ((ℓ x + e : ℝ) : ℂ)) =
        fun _ => ((ℓ h : ℝ) : ℂ) := by
      funext x
      rw [map_add]
      push_cast
      ring
    rw [this]
    exact sb1_fd_const _ k hs

/-! ### Adjoint identity for a field of linear growth -/

/-- Continuous, of linear growth with constant `B ≥ 0`. -/
def Lw (B : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℂ) : Prop :=
  0 ≤ B ∧ Continuous f ∧ ∀ x, ‖f x‖ ≤ B * (1 + ‖x‖)

/-- Continuous with `(1+‖x‖) ‖g‖` integrable. -/
def Gw (g : EuclideanSpace ℝ (Fin d) → ℂ) : Prop :=
  Continuous g ∧ Integrable (fun x => (1 + ‖x‖) * ‖g x‖)

theorem sb1_Lw_shift {B : ℝ} {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : Lw B f)
    (h : EuclideanSpace ℝ (Fin d)) : Lw (B * (1 + ‖h‖)) (fun x => f (x + h)) := by
  obtain ⟨hB, hc, hb⟩ := hf
  refine ⟨by positivity, hc.comp (continuous_id.add continuous_const), fun x => ?_⟩
  have h1 : 1 + ‖x + h‖ ≤ (1 + ‖h‖) * (1 + ‖x‖) := by
    nlinarith [norm_add_le x h, norm_nonneg x, norm_nonneg h]
  calc ‖f (x + h)‖ ≤ B * (1 + ‖x + h‖) := hb _
    _ ≤ B * ((1 + ‖h‖) * (1 + ‖x‖)) := mul_le_mul_of_nonneg_left h1 hB
    _ = B * (1 + ‖h‖) * (1 + ‖x‖) := by ring

theorem sb1_Lw_diff {B : ℝ} {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : Lw B f)
    (h : EuclideanSpace ℝ (Fin d)) : Lw (B * (1 + ‖h‖) + B) (fun x => f (x + h) - f x) := by
  obtain ⟨hB, hc, hb⟩ := hf
  have h1 := sb1_Lw_shift ⟨hB, hc, hb⟩ h
  refine ⟨by positivity, h1.2.1.sub hc, fun x => ?_⟩
  calc ‖f (x + h) - f x‖ ≤ ‖f (x + h)‖ + ‖f x‖ := norm_sub_le _ _
    _ ≤ B * (1 + ‖h‖) * (1 + ‖x‖) + B * (1 + ‖x‖) := add_le_add (h1.2.2 x) (hb x)
    _ = (B * (1 + ‖h‖) + B) * (1 + ‖x‖) := by ring

theorem sb1_Lw_fd (L : List (EuclideanSpace ℝ (Fin d))) :
    ∀ (B : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℂ), Lw B f → ∃ B', Lw B' (u8_fd L f) := by
  induction L with
  | nil => intro B f hf; exact ⟨B, hf⟩
  | cons h hs ih =>
    intro B f hf
    rw [u8_fd_cons]
    exact ih _ _ (sb1_Lw_diff hf h)

theorem sb1_Gw_shift {g : EuclideanSpace ℝ (Fin d) → ℂ} (hg : Gw g) (h : EuclideanSpace ℝ (Fin d)) :
    Gw (fun x => g (x + h)) := by
  obtain ⟨hc, hi⟩ := hg
  refine ⟨hc.comp (continuous_id.add continuous_const), ?_⟩
  have h1 : Integrable (fun x => (1 + ‖h‖) * ((1 + ‖x + h‖) * ‖g (x + h)‖)) :=
    (hi.comp_add_right h).const_mul _
  refine h1.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((continuous_const.add continuous_norm).mul
      (hc.comp (continuous_id.add continuous_const)).norm).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have h1 : 1 + ‖x‖ ≤ (1 + ‖h‖) * (1 + ‖x + h‖) := by
      have := norm_sub_le (x + h) h
      rw [add_sub_cancel_right] at this
      nlinarith [norm_nonneg x, norm_nonneg h, norm_nonneg (x + h)]
    calc (1 + ‖x‖) * ‖g (x + h)‖ ≤ ((1 + ‖h‖) * (1 + ‖x + h‖)) * ‖g (x + h)‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = (1 + ‖h‖) * ((1 + ‖x + h‖) * ‖g (x + h)‖) := by ring

theorem sb1_Gw_diff {g : EuclideanSpace ℝ (Fin d) → ℂ} (hg : Gw g) (h : EuclideanSpace ℝ (Fin d)) :
    Gw (fun x => g (x + h) - g x) := by
  have h1 := sb1_Gw_shift hg h
  refine ⟨h1.1.sub hg.1, ?_⟩
  refine (h1.2.add hg.2).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((continuous_const.add continuous_norm).mul (h1.1.sub hg.1).norm).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    calc (1 + ‖x‖) * ‖g (x + h) - g x‖ ≤ (1 + ‖x‖) * (‖g (x + h)‖ + ‖g x‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ = (1 + ‖x‖) * ‖g (x + h)‖ + (1 + ‖x‖) * ‖g x‖ := by ring

theorem sb1_int_mul {B : ℝ} {F g : EuclideanSpace ℝ (Fin d) → ℂ} (hF : Lw B F) (hg : Gw g) :
    Integrable (fun x => F x * g x) := by
  have h1 : Integrable (fun x => B * ((1 + ‖x‖) * ‖g x‖)) := hg.2.const_mul B
  refine h1.mono' (hF.2.1.mul hg.1).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  calc ‖F x‖ * ‖g x‖ ≤ (B * (1 + ‖x‖)) * ‖g x‖ :=
        mul_le_mul_of_nonneg_right (hF.2.2 x) (norm_nonneg _)
    _ = B * ((1 + ‖x‖) * ‖g x‖) := by ring

theorem sb1_fd_adjoint_lin (L : List (EuclideanSpace ℝ (Fin d))) :
    ∀ (f g : EuclideanSpace ℝ (Fin d) → ℂ), (∃ B, Lw B f) → Gw g →
      ∫ x, f x * u8_fd L g x = ∫ x, u8_fd (L.map Neg.neg) f x * g x := by
  induction L with
  | nil => intro f g _ _; rfl
  | cons h hs ih =>
    intro f g ⟨B, hf⟩ hg
    rw [u8_fd_cons]
    have hg' := sb1_Gw_diff hg h
    rw [ih f _ ⟨B, hf⟩ hg']
    set F := u8_fd (hs.map Neg.neg) f with hF
    obtain ⟨B', hFB⟩ := sb1_Lw_fd (hs.map Neg.neg) B f hf
    have hFB' : Lw B' F := hFB
    have hcomm : u8_fd ((h :: hs).map Neg.neg) f = fun x => F (x + -h) - F x := by
      rw [List.map_cons, u8_fd_cons]
      exact u8_fd_comm _ f (-h)
    rw [hcomm]
    have hgs := sb1_Gw_shift hg h
    have i1 : Integrable (fun x => F x * g (x + h)) := sb1_int_mul hFB' hgs
    have i2 : Integrable (fun x => F x * g x) := sb1_int_mul hFB' hg
    have i3 : Integrable (fun x => F (x + -h) * g x) := sb1_int_mul (sb1_Lw_shift hFB' (-h)) hg
    have e1 : ∫ x, F x * (g (x + h) - g x) = (∫ x, F x * g (x + h)) - ∫ x, F x * g x := by
      rw [← integral_sub i1 i2]
      congr 1; funext x; ring
    have e2 : ∫ x, (F (x + -h) - F x) * g x = (∫ x, F (x + -h) * g x) - ∫ x, F x * g x := by
      rw [← integral_sub i3 i2]
      congr 1; funext x; ring
    have e3 : ∫ x, F x * g (x + h) = ∫ x, F (x + -h) * g x := by
      have := integral_add_right_eq_self (μ := volume) (fun x => F (x + -h) * g x) h
      simp only [add_neg_cancel_right] at this
      exact this
    rw [e1, e2, e3]

/-! ### The Schwartz-test identity for an affine field -/

theorem sb1_vanish (hd : 1 ≤ d) (α : ℝ) (hα : 1 < α) (m : ℕ) (hm2 : 2 ≤ m)
    (ℓv : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (e : ℝ) (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
    (γ Cφ : ℝ) (hγ : (d : ℝ) + 1 < γ)
    (hφP1 : ∀ x, Integrable (fun y => ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) (⇑φ) x))
    (hφP2 : ∀ x, ∫ y, ‖‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) (⇑φ) x‖ ≤
      Cφ * (1 + ‖x‖) ^ (-γ)) :
    ∫ x, ((ℓv x + e : ℝ) : ℂ) * ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) (⇑φ) x = 0 := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨vC, hvC⟩ : ∃ vC : EuclideanSpace ℝ (Fin d) → ℂ, vC = fun x => ((ℓv x + e : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  have e0 : ∀ x, ((ℓv x + e : ℝ) : ℂ) = vC x := fun x => by rw [hvC]
  simp only [e0]
  have hvc : Continuous vC := by
    rw [hvC]
    exact Complex.continuous_ofReal.comp (ℓv.continuous.add continuous_const)
  obtain ⟨Bv, hBv0, hvb⟩ : ∃ Bv : ℝ, 0 ≤ Bv ∧ ∀ x, ‖vC x‖ ≤ Bv * (1 + ‖x‖) := by
    refine ⟨‖ℓv‖ + |e|, by positivity, fun x => ?_⟩
    rw [hvC]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have h1 : |ℓv x| ≤ ‖ℓv‖ * ‖x‖ := by
      have := ℓv.le_opNorm x
      rwa [Real.norm_eq_abs] at this
    calc |ℓv x + e| ≤ |ℓv x| + |e| := abs_add_le _ _
      _ ≤ ‖ℓv‖ * ‖x‖ + |e| := by linarith
      _ ≤ (‖ℓv‖ + |e|) * (1 + ‖x‖) := by
          nlinarith [norm_nonneg ℓv, abs_nonneg e, norm_nonneg x, mul_nonneg (abs_nonneg e) (norm_nonneg x)]
  have hKm : Measurable (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ ^ (-((d : ℝ) + α))) :=
    measurable_norm.pow_const _
  obtain ⟨f, hf⟩ : ∃ f : (EuclideanSpace ℝ (Fin d) → ℂ) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) → ℂ, f = fun u x y =>
        ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) u x := ⟨_, rfl⟩
  have hfeq : ∀ u x y, f u x y = ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) u x :=
    fun u x y => by rw [hf]
  have hmφ : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      f (⇑φ) p.1 p.2) := by
    have hc : Continuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        u8_fd (u8_L m p.2) (⇑φ) p.1) := (u8_L_cont_joint m φ.continuous).comp continuous_swap
    rw [hf]
    exact (hKm.comp measurable_snd).smul hc.measurable
  simp only [← hfeq] at hφP1 hφP2 ⊢
  have hIA : Integrable (Function.uncurry fun x y => vC x * f (⇑φ) x y)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) := by
    have hm : AEStronglyMeasurable (Function.uncurry fun x y => vC x * f (⇑φ) x y)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) :=
      ((hvc.measurable.comp measurable_fst).mul hmφ).aestronglyMeasurable
    rw [integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall (fun x => (hφP1 x).const_mul (vC x)), ?_⟩
    have hmaj : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        Bv * Cφ * (1 + ‖x‖) ^ (-(γ - 1))) :=
      (integrable_one_add_norm (by simpa using (by linarith : (d : ℝ) < γ - 1))).const_mul _
    refine Integrable.mono' hmaj hm.norm.integral_prod_right' (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
    have h1 : ∀ y, ‖Function.uncurry (fun x y => vC x * f (⇑φ) x y) (x, y)‖ =
        ‖vC x‖ * ‖f (⇑φ) x y‖ := fun y => by simp [Function.uncurry, norm_mul]
    have h2 : ∫ y, ‖Function.uncurry (fun x y => vC x * f (⇑φ) x y) (x, y)‖ =
        ‖vC x‖ * ∫ y, ‖f (⇑φ) x y‖ := by
      rw [← integral_const_mul]
      congr 1; funext y; exact h1 y
    rw [h2]
    have hx : 0 < 1 + ‖x‖ := by positivity
    have hpow : (1 + ‖x‖) ^ (-(γ - 1)) = (1 + ‖x‖) * (1 + ‖x‖) ^ (-γ) := by
      have : -(γ - 1) = 1 + -γ := by ring
      rw [this, Real.rpow_add hx, Real.rpow_one]
    rw [hpow]
    calc ‖vC x‖ * ∫ y, ‖f (⇑φ) x y‖ ≤ (Bv * (1 + ‖x‖)) * (Cφ * (1 + ‖x‖) ^ (-γ)) :=
          mul_le_mul (hvb x) (hφP2 x) (integral_nonneg (fun y => norm_nonneg _))
            (by positivity)
      _ = Bv * Cφ * ((1 + ‖x‖) * (1 + ‖x‖) ^ (-γ)) := by ring
  have e1 : ∀ x, vC x * (∫ y, f (⇑φ) x y) = ∫ y, vC x * f (⇑φ) x y := by
    intro x; exact (integral_const_mul _ _).symm
  simp_rw [e1]
  rw [integral_integral_swap hIA]
  -- each slice vanishes
  obtain ⟨Bφ', hBφ', hφ'0, -⟩ := u8_schwartz_bounds φ 0 ((d : ℝ) + 2) (by positivity)
  have hGw : Gw (⇑φ) := by
    refine ⟨φ.continuous, ?_⟩
    have hmaj : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Bφ' * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) :=
      (integrable_one_add_norm (by simp)).const_mul _
    refine hmaj.mono' ((continuous_const.add continuous_norm).mul φ.continuous.norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have hx : 0 < 1 + ‖x‖ := by positivity
    have hpow : (1 + ‖x‖) ^ (-((d : ℝ) + 1)) = (1 + ‖x‖) * (1 + ‖x‖) ^ (-((d : ℝ) + 2)) := by
      have : -((d : ℝ) + 1) = 1 + -((d : ℝ) + 2) := by ring
      rw [this, Real.rpow_add hx, Real.rpow_one]
    rw [hpow]
    calc (1 + ‖x‖) * ‖φ x‖ ≤ (1 + ‖x‖) * (Bφ' * (1 + ‖x‖) ^ (-((d : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left (hφ'0 x) hx.le
      _ = Bφ' * ((1 + ‖x‖) * (1 + ‖x‖) ^ (-((d : ℝ) + 2))) := by ring
  have hLw : Lw (Bv) vC := ⟨hBv0, hvc, hvb⟩
  have hslice : ∀ y : EuclideanSpace ℝ (Fin d),
      ∫ x, vC x * f (⇑φ) x y = 0 := by
    intro y
    have s1 : ∀ x, vC x * f (⇑φ) x y =
        ‖y‖ ^ (-((d : ℝ) + α)) • (vC x * u8_fd (u8_L m y) (⇑φ) x) := by
      intro x; rw [hfeq]; exact mul_smul_comm _ _ _
    simp_rw [s1]
    rw [integral_smul, sb1_fd_adjoint_lin (u8_L m y) vC (⇑φ) ⟨Bv, hLw⟩ hGw]
    have hlen : 2 ≤ ((u8_L m y).map Neg.neg).length := by
      rw [List.length_map, u8_L_length]; omega
    have hz : u8_fd ((u8_L m y).map Neg.neg) vC = fun _ => 0 := by
      rw [hvC]; exact sb1_fd_affine ℓv e _ hlen
    rw [hz]
    simp
  simp_rw [hslice]
  simp

/-- **`IsFracDerivRep α (affine) 0` for `α > 1`**: the affine field `x ↦ ℓ x + e` has zero distributional
fractional derivative `|D|^α` (TeX S L11139-11143, the sub-Coulomb alternative of S.B.1). -/
theorem sb1_fracDeriv_affine (hd : 1 ≤ d) (α : ℝ) (hα : 1 < α)
    (ℓv : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (e : ℝ) :
    HRS.Whole.IsFracDerivRep α (fun x : EuclideanSpace ℝ (Fin d) => ℓv x + e) (fun _ => 0) := by
  intro φ
  have hα0 : 0 < α := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌊α⌋₊ + 1 := ⟨_, rfl⟩
  have hαm : α < m := by rw [hm]; exact_mod_cast Nat.lt_floor_add_one α
  have hm2 : 2 ≤ m := by
    have : 1 ≤ ⌊α⌋₊ := Nat.le_floor (by simpa using hα.le)
    omega
  have hm1 : 1 ≤ m := by omega
  have hα2m : α < 2 * (m : ℝ) := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  obtain ⟨M, hM0, hM⟩ := u8_sym_eq hd m hm1 α hα0 hα2m
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨b2, hb2pos, hb2d, hb2α⟩ : ∃ b2 : ℝ, 0 < b2 ∧ b2 < d ∧ (d : ℝ) + 1 < b2 + α := by
    refine ⟨max ((d : ℝ) - (α - 1) / 2) ((d : ℝ) / 2), ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (by positivity) (le_max_right _ _)
    · exact max_lt (by linarith) (by linarith)
    · have := le_max_left ((d : ℝ) - (α - 1) / 2) ((d : ℝ) / 2)
      linarith
  obtain ⟨C2, hC2nn, hC2⟩ := u8_pointwise hd α b2 hα0 hb2pos hb2d m m hm1 hαm (by omega)
  obtain ⟨Bφ, hBφ, hφ0, hφ1⟩ := u8_schwartz_bounds φ m b2 hb2pos.le
  have hφs : ContDiff ℝ m (⇑φ) := by exact_mod_cast φ.smooth m
  have hPφ := fun x => hC2 ℂ (⇑φ) Bφ hBφ hφs hφ0 hφ1 x
  have hΨ : ∀ x, 𝓕⁻ (fun ξ : EuclideanSpace ℝ (Fin d) =>
      (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x =
      ((M⁻¹ : ℝ) : ℂ) * ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) (⇑φ) x := by
    intro x
    rw [u8_Lam_eq hd m hm1 α hα0 hα2m M hM φ x]
    have : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
    push_cast
    field_simp
  simp_rw [hΨ]
  have hvan := sb1_vanish hd α hα m hm2 ℓv e φ (b2 + α) (C2 * Bφ) hb2α
    (fun x => (hPφ x).1) (fun x => (hPφ x).2.1)
  refine ⟨?_, ?_, ?_⟩
  · -- integrability of `v · |D|^α φ`
    obtain ⟨Bv, hBv0, hvb⟩ : ∃ Bv : ℝ, 0 ≤ Bv ∧ ∀ x : EuclideanSpace ℝ (Fin d),
        ‖((ℓv x + e : ℝ) : ℂ)‖ ≤ Bv * (1 + ‖x‖) := by
      refine ⟨‖ℓv‖ + |e|, by positivity, fun x => ?_⟩
      simp only [Complex.norm_real, Real.norm_eq_abs]
      have h1 : |ℓv x| ≤ ‖ℓv‖ * ‖x‖ := by
        have := ℓv.le_opNorm x
        rwa [Real.norm_eq_abs] at this
      calc |ℓv x + e| ≤ |ℓv x| + |e| := abs_add_le _ _
        _ ≤ ‖ℓv‖ * ‖x‖ + |e| := by linarith
        _ ≤ (‖ℓv‖ + |e|) * (1 + ‖x‖) := by
            nlinarith [norm_nonneg ℓv, abs_nonneg e, norm_nonneg x,
              mul_nonneg (abs_nonneg e) (norm_nonneg x)]
    have hmaj : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        Bv * (M⁻¹ * (C2 * Bφ)) * (1 + ‖x‖) ^ (-(b2 + α - 1))) :=
      (integrable_one_add_norm (by simpa using (by linarith : (d : ℝ) < b2 + α - 1))).const_mul _
    refine Integrable.mono' hmaj ?_ (Filter.Eventually.of_forall (fun x => ?_))
    · exact ((Complex.continuous_ofReal.comp (ℓv.continuous.add continuous_const)).aestronglyMeasurable).mul
        ((aestronglyMeasurable_const).mul (u8_Lam_aesm m α (⇑φ) φ.continuous))
    · rw [norm_mul, norm_mul]
      have hx : 0 < 1 + ‖x‖ := by positivity
      have hpow : (1 + ‖x‖) ^ (-(b2 + α - 1)) = (1 + ‖x‖) * (1 + ‖x‖) ^ (-(b2 + α)) := by
        have : -(b2 + α - 1) = 1 + -(b2 + α) := by ring
        rw [this, Real.rpow_add hx, Real.rpow_one]
      rw [hpow]
      have hMn : ‖((M⁻¹ : ℝ) : ℂ)‖ = M⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hM0)]
      rw [hMn]
      have h3 := (hPφ x).2.2
      calc ‖((ℓv x + e : ℝ) : ℂ)‖ * (M⁻¹ * ‖∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) (⇑φ) x‖)
          ≤ (Bv * (1 + ‖x‖)) * (M⁻¹ * (C2 * Bφ * (1 + ‖x‖) ^ (-(b2 + α)))) :=
            mul_le_mul (hvb x) (mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hM0.le))
              (by positivity) (by positivity)
        _ = Bv * (M⁻¹ * (C2 * Bφ)) * ((1 + ‖x‖) * (1 + ‖x‖) ^ (-(b2 + α))) := by ring
  · simp
  · have h1 : ∀ x : EuclideanSpace ℝ (Fin d), ((ℓv x + e : ℝ) : ℂ) * (((M⁻¹ : ℝ) : ℂ) *
        ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) (⇑φ) x) =
        ((M⁻¹ : ℝ) : ℂ) * (((ℓv x + e : ℝ) : ℂ) *
        ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) (⇑φ) x) := fun x => by ring
    simp_rw [h1]
    rw [integral_const_mul, hvan]
    simp

/-! ### Consequence for the transport bound -/

theorem sb1_isFracDerivRep_add {α : ℝ} {v₁ v₂ w₁ w₂ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h₁ : HRS.Whole.IsFracDerivRep α v₁ w₁) (h₂ : HRS.Whole.IsFracDerivRep α v₂ w₂) :
    HRS.Whole.IsFracDerivRep α (fun x => v₁ x + v₂ x) (fun x => w₁ x + w₂ x) := by
  intro φ
  obtain ⟨i1, j1, e1⟩ := h₁ φ
  obtain ⟨i2, j2, e2⟩ := h₂ φ
  refine ⟨?_, ?_, ?_⟩
  · refine (i1.add i2).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    push_cast
    ring
  · refine (j1.add j2).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    push_cast
    ring
  · have f1 : (fun x => (((v₁ x + v₂ x : ℝ)) : ℂ) *
        𝓕⁻ (fun ξ : EuclideanSpace ℝ (Fin d) => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x) =
        fun x => (((v₁ x : ℝ)) : ℂ) *
          𝓕⁻ (fun ξ : EuclideanSpace ℝ (Fin d) => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x +
        (((v₂ x : ℝ)) : ℂ) *
          𝓕⁻ (fun ξ : EuclideanSpace ℝ (Fin d) => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x := by
      funext x; push_cast; ring
    have f2 : (fun x => (((w₁ x + w₂ x : ℝ)) : ℂ) * φ x) =
        fun x => (((w₁ x : ℝ)) : ℂ) * φ x + (((w₂ x : ℝ)) : ℂ) * φ x := by
      funext x; push_cast; ring
    rw [f1, f2, integral_add i1 i2, integral_add j1 j2, e1, e2]

/-- **The sub-Coulomb transport of S.B.1(ii)**: adding the affine field `x ↦ Qx + b` to a transport with
`HasFracTransportBound α p u K` (`α > 1`) keeps the fractional part (`|D|^α` of an affine field is zero) and adds
`‖Q‖` to the Lipschitz constant. -/
theorem sb1_transport_add_affine (hd : 1 ≤ d) {α p : ℝ} (hα : 1 < α)
    {u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {K : ℝ}
    (hu : HRS.Whole.HasFracTransportBound α p u K)
    (Q : Matrix (Fin d) (Fin d) ℝ) (b : EuclideanSpace ℝ (Fin d)) :
    HRS.Whole.HasFracTransportBound α p (fun x => u x + (Torus.matVec Q x + b))
      (K + ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q‖) := by
  obtain ⟨L, F, hF, hLip, ⟨w, hw, hnorm⟩, hLK⟩ := hu
  refine ⟨L + ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q‖₊, F, hF, ?_, ⟨w, ?_, hnorm⟩, ?_⟩
  · have h1 : LipschitzWith ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q‖₊
        (fun x => Torus.matVec Q x + b) := by
      have e : ∀ x, Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q x = Torus.matVec Q x := fun x =>
        LinearMap.congr_fun (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (n := Fin d) (𝕜 := ℝ) Q) x
      have := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q).lipschitz.add
        (LipschitzWith.const b)
      simp only [add_zero] at this
      convert this using 2 with x
      rw [e x]
    exact hLip.add h1
  · intro i
    have hA := sb1_fracDeriv_affine hd α hα
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).comp
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q)) (b i)
    have hS := sb1_isFracDerivRep_add (hw i) hA
    have e1 : (fun x : EuclideanSpace ℝ (Fin d) => (u x + (Torus.matVec Q x + b)) i) =
        fun x => u x i + (((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).comp
          (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q)) x + b i) := by
      funext x
      simp [Torus.matVec]
    have e2 : (fun x : EuclideanSpace ℝ (Fin d) => w x i) = fun x => w x i + 0 := by
      funext x; simp
    rw [e1, e2]
    exact hS
  · have : ((L + ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q‖₊ : NNReal) : ℝ) =
        (L : ℝ) + ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q‖ := by
      simp
    rw [this]
    linarith

end HRS.MS.MfeConf

end
