import HRS.MS.Mov63FAux4

/-!
# S6.3, packet N7 (part 5): positivity and the ratio bound

Namespace `HRS.MS.Mov63`, prefix `mnf_`.  See `Mov63FAux1`.

**`mnf_ratio`**: for a mild solution `v` with `‖v_t‖ ≤ K e^{-at}` and `(4C_A+1) K ≤ a` (`C_A` = the sup bound of the zero-order coefficient
`A_u`, `|A_u| ≤ C_A ‖u‖`), and with `sup |f₀| ≤ 1/4` for the initial relative perturbation `f₀ = V_0/√ρ` (`Q_0 = 1 + f₀`): for all `t ≥ 0`, `x`,
`ρ(x)/2 ≤ ρ_t(x) ≤ 2ρ(x)` (so `ρ_t ≥ 0`, indeed `> 0`).

Proof: three applications of `mnf_master` (the maximum principle in the Gaussian growth class) with `Λ(t) = (C_A K/a)(1 - e^{-at}) ≤ 1/4`,
`Λ' = C_A K e^{-at} ≥ |A_t|`:
(i) `P = e^{-Λ} Q` (`c = A - Λ' ≤ 0`): `Q ≥ 0`;
(ii) `P = 5/4 - e^{-Λ} Q` (`c = A - Λ'`, source `-c·5/4 ≥ 0`): `Q ≤ (5/4) e^{Λ} ≤ 5/3`;
(iii) `P = e^{Λ} Q - 3/4` (`c = 0`, source `e^Λ(Λ' + A) Q ≥ 0` by (i)): `Q ≥ (3/4) e^{-Λ} ≥ 9/16`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Lambda

lemma mnf_Lam_deriv (Kc a : ℝ) (ha : 0 < a) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (Kc / a) * (1 - Real.exp (-a * t))) (Kc * Real.exp (-a * t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => -a * t) (-a) t := by
    simpa using (hasDerivAt_id t).const_mul (-a)
  have h2 := (h1.exp).const_sub 1
  have h3 := h2.const_mul (Kc / a)
  convert h3 using 1
  field_simp

end Lambda

section Ratio

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m)

include hm in
theorem mnf_ratio (H : Mov2dTh d s β q ρ) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ (v : ℝ → OscSpace d (m : ℝ)), MneMild H hm v → ∀ K a : ℝ, 0 ≤ K → 0 < a →
      (∀ t, 0 ≤ t → ‖v t‖ ≤ K * Real.exp (-a * t)) → Cs * K ≤ a →
      (∀ x, |mneF0fun d ρ hm v x| ≤ 1 / 4) →
      ∀ t, 0 ≤ t → ∀ x, ρ x / 2 ≤ mneRho ρ hm (v t) x ∧ mneRho ρ hm (v t) x ≤ 2 * ρ x := by
  obtain ⟨CA, hCA0, hCA⟩ := mnf_Abound hm H
  obtain ⟨CV, hCV0, hCV⟩ := mnf_Vbound hm H
  obtain ⟨M0, hM00, hM0⟩ := mnf_M0 hm H
  refine ⟨4 * CA + 1, by positivity, fun v hmild K a hK ha hvK hsmall hf0 t ht x => ?_⟩
  have hβ := H.hβ
  have hq := H.hq
  have hρpos := (mnb_rhoData H).pos
  set Kc : ℝ := CA * K with hKc
  have hKc0 : 0 ≤ Kc := mul_nonneg hCA0 hK
  have hΛinf : Kc / a ≤ 1 / 4 := by
    rw [div_le_iff₀ ha]; nlinarith
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ → ℝ, Λ = fun t => (Kc / a) * (1 - Real.exp (-a * t)) := ⟨_, rfl⟩
  have hΛd : ∀ t, HasDerivAt Λ (Kc * Real.exp (-a * t)) t := fun t => by
    rw [hΛ]; exact mnf_Lam_deriv Kc a ha t
  have hΛ0 : Λ 0 = 0 := by rw [hΛ]; simp
  have hΛnn : ∀ t, 0 ≤ t → 0 ≤ Λ t := fun t ht => by
    rw [hΛ]
    have : Real.exp (-a * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    exact mul_nonneg (by positivity) (by linarith)
  have hΛle : ∀ t, 0 ≤ t → Λ t ≤ 1 / 4 := fun t ht => by
    rw [hΛ]
    have h1 : 0 < Real.exp (-a * t) := Real.exp_pos _
    have h2 : (Kc / a) * (1 - Real.exp (-a * t)) ≤ Kc / a := by
      have : 0 ≤ Kc / a := by positivity
      nlinarith
    linarith
  -- exponentials of Λ
  have hexpm : ∀ t, 0 ≤ t → 3 / 4 ≤ Real.exp (-Λ t) := fun t ht => by
    have := Real.add_one_le_exp (-Λ t)
    linarith [hΛle t ht]
  have hexpp : ∀ t, 0 ≤ t → Real.exp (Λ t) ≤ 4 / 3 := fun t ht => by
    have h1 : Real.exp (Λ t) * Real.exp (-Λ t) = 1 := by rw [← Real.exp_add]; simp
    have := hexpm t ht
    have := Real.exp_pos (Λ t)
    nlinarith
  have hexpm1 : ∀ t, 0 ≤ t → Real.exp (-Λ t) ≤ 1 := fun t ht =>
    Real.exp_le_one_iff.2 (by linarith [hΛnn t ht])
  -- coefficient bounds
  have hvK' : ∀ t, 0 ≤ t → ‖v t‖ ≤ K := fun t ht => (hvK t ht).trans (by
    have : Real.exp (-a * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith)
  have hAb : ∀ t, 0 ≤ t → ∀ y, |mnfA d s ρ hm (v t) y| ≤ Kc * Real.exp (-a * t) := fun t ht y =>
    (hCA (v t) y).trans (by
      rw [hKc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hvK t ht) hCA0)
  -- the growth class
  set KQ : ℝ := 1 + (CV * K) * ((Real.sqrt (ρ 0))⁻¹ * Real.exp (β * M0 ^ 2 / q)) with hKQ
  have hKQ1 : 1 ≤ KQ := by
    rw [hKQ]
    have : 0 ≤ (CV * K) * ((Real.sqrt (ρ 0))⁻¹ * Real.exp (β * M0 ^ 2 / q)) := by positivity
    linarith
  have hQg : ∀ t, 0 ≤ t → ∀ y, |mneQ ρ hm (v t) y| ≤ KQ * Real.exp ((5 * β * q / 16) * ‖y‖ ^ 2) := fun t ht y => by
    refine mnf_Q_growth hm H hM0 (mul_nonneg hCV0 hK) (v t) (fun z => ?_) y
    exact (hCV (v t) z).trans (mul_le_mul_of_nonneg_left (hvK' t ht) hCV0)
  have hE1 : ∀ y : Euc d, 1 ≤ Real.exp ((5 * β * q / 16) * ‖y‖ ^ 2) := fun y =>
    Real.one_le_exp (by positivity)
  have hKE : ∀ y : Euc d, 1 ≤ KQ * Real.exp ((5 * β * q / 16) * ‖y‖ ^ 2) := fun y => by
    nlinarith [hE1 y]
  -- initial data
  have hQ0 : ∀ y, mneQ ρ hm (v 0) y = 1 + mneF0fun d ρ hm v y := fun y => mnf_Q_eq hm H (v 0) y
  have hf0' : ∀ y, 3 / 4 ≤ mneQ ρ hm (v 0) y ∧ mneQ ρ hm (v 0) y ≤ 5 / 4 := fun y => by
    rw [hQ0]; have := abs_le.1 (hf0 y); constructor <;> linarith [this.1, this.2]
  -- (i) positivity
  have hα1 : ∀ t, HasDerivAt (fun t => Real.exp (-Λ t))
      (-(Kc * Real.exp (-a * t)) * Real.exp (-Λ t)) t := fun t => by
    have h := (hΛd t).neg.exp
    simp only [Pi.neg_apply] at h
    convert h using 1; ring
  have hconst : ∀ r : ℝ, ∀ t, HasDerivAt (fun _ : ℝ => r) (0 : ℝ) t := fun r t => hasDerivAt_const t r
  have hpos : ∀ T, 0 ≤ T → ∀ t ∈ Icc 0 T, ∀ y, 0 ≤ mneQ ρ hm (v t) y := by
    intro T hT t ht y
    have key := mnf_master hm H hmild hvK' (K := K) (T := T) (α := fun t => Real.exp (-Λ t)) (γ := fun _ => (0:ℝ))
      (α' := fun t => -(Kc * Real.exp (-a * t)) * Real.exp (-Λ t)) (γ' := fun _ => (0:ℝ)) hα1 (hconst 0)
      (c := fun t y => mnfA d s ρ hm (v t) y - Kc * Real.exp (-a * t))
      (fun t ht y => by
        have := (abs_le.1 (hAb t ht.1.le y)).2
        linarith)
      (fun t ht y => by
        apply le_of_eq
        ring)
      (Kp := KQ) (by linarith)
      (fun t ht y => by
        simp only [zero_add]
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        calc Real.exp (-Λ t) * |mneQ ρ hm (v t) y| ≤ 1 * |mneQ ρ hm (v t) y| :=
              mul_le_mul_of_nonneg_right (hexpm1 t ht.1) (abs_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact hQg t ht.1 y)
      (fun y => by
        simp only [hΛ0, neg_zero, Real.exp_zero, zero_add, one_mul]
        linarith [(hf0' y).1])
    have := key t ht y
    simp only [zero_add] at this
    exact nonneg_of_mul_nonneg_right this (Real.exp_pos _)
  -- (ii) upper bound
  have hupper : ∀ T, 0 ≤ T → ∀ t ∈ Icc 0 T, ∀ y, mneQ ρ hm (v t) y ≤ 5 / 3 := by
    intro T hT t ht y
    have key := mnf_master hm H hmild hvK' (K := K) (T := T) (α := fun t => -Real.exp (-Λ t)) (γ := fun _ => (5 / 4 : ℝ))
      (α' := fun t => (Kc * Real.exp (-a * t)) * Real.exp (-Λ t)) (γ' := fun _ => (0:ℝ))
      (fun t => by
        have := (hα1 t).neg
        convert this using 1; ring)
      (hconst _)
      (c := fun t y => mnfA d s ρ hm (v t) y - Kc * Real.exp (-a * t))
      (fun t ht y => by
        have := (abs_le.1 (hAb t ht.1.le y)).2
        linarith)
      (fun t ht y => by
        have hc := (abs_le.1 (hAb t ht.1.le y)).2
        nlinarith)
      (Kp := 3 * KQ) (by linarith)
      (fun t ht y => by
        have h1 := hQg t ht.1 y
        have h2 := hKE y
        have h3 : |(5 / 4 : ℝ) + -Real.exp (-Λ t) * mneQ ρ hm (v t) y| ≤ 5 / 4 + |mneQ ρ hm (v t) y| := by
          calc _ ≤ |(5 / 4 : ℝ)| + |-Real.exp (-Λ t) * mneQ ρ hm (v t) y| := abs_add_le _ _
            _ = 5 / 4 + Real.exp (-Λ t) * |mneQ ρ hm (v t) y| := by
              rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]; norm_num
            _ ≤ 5 / 4 + 1 * |mneQ ρ hm (v t) y| := by
              have := mul_le_mul_of_nonneg_right (hexpm1 t ht.1) (abs_nonneg (mneQ ρ hm (v t) y))
              linarith
            _ = _ := by rw [one_mul]
        nlinarith)
      (fun y => by
        simp only [hΛ0, neg_zero, Real.exp_zero]
        linarith [(hf0' y).2])
    have h := key t ht y
    have hq0 := hpos T hT t ht y
    have h34 := hexpm t ht.1
    nlinarith
  -- (iii) lower bound
  have hlower : ∀ T, 0 ≤ T → ∀ t ∈ Icc 0 T, ∀ y, 9 / 16 ≤ mneQ ρ hm (v t) y := by
    intro T hT t ht y
    have key := mnf_master hm H hmild hvK' (K := K) (T := T) (α := fun t => Real.exp (Λ t)) (γ := fun _ => (-(3 / 4) : ℝ))
      (α' := fun t => (Kc * Real.exp (-a * t)) * Real.exp (Λ t)) (γ' := fun _ => (0:ℝ))
      (fun t => by
        have := (hΛd t).exp
        convert this using 1; ring)
      (hconst _)
      (c := fun _ _ => (0 : ℝ))
      (fun _ _ _ => le_refl _)
      (fun t ht y => by
        have hA := (abs_le.1 (hAb t ht.1.le y)).1
        have hQ := hpos T hT t ⟨ht.1.le, ht.2⟩ y
        have he := Real.exp_pos (Λ t)
        simp only [zero_mul]
        have : 0 ≤ (Kc * Real.exp (-a * t) * Real.exp (Λ t) + Real.exp (Λ t) * mnfA d s ρ hm (v t) y) *
            mneQ ρ hm (v t) y := by
          have : 0 ≤ Kc * Real.exp (-a * t) * Real.exp (Λ t) + Real.exp (Λ t) * mnfA d s ρ hm (v t) y := by
            nlinarith
          exact mul_nonneg this hQ
        linarith)
      (Kp := 3 * KQ) (by linarith)
      (fun t ht y => by
        have h1 := hQg t ht.1 y
        have h2 := hKE y
        have he := hexpp t ht.1
        have he0 := Real.exp_pos (Λ t)
        have h3 : |(-(3 / 4) : ℝ) + Real.exp (Λ t) * mneQ ρ hm (v t) y| ≤ 3 / 4 + (4 / 3) * |mneQ ρ hm (v t) y| := by
          calc _ ≤ |(-(3 / 4) : ℝ)| + |Real.exp (Λ t) * mneQ ρ hm (v t) y| := abs_add_le _ _
            _ = 3 / 4 + Real.exp (Λ t) * |mneQ ρ hm (v t) y| := by
              rw [abs_mul, abs_of_pos he0]; norm_num
            _ ≤ 3 / 4 + (4 / 3) * |mneQ ρ hm (v t) y| := by
              have := mul_le_mul_of_nonneg_right he (abs_nonneg (mneQ ρ hm (v t) y))
              linarith
        nlinarith)
      (fun y => by
        simp only [hΛ0, Real.exp_zero, one_mul]
        linarith [(hf0' y).1])
    have h := key t ht y
    have hq0 := hpos T hT t ht y
    have h43 := hexpp t ht.1
    nlinarith
  have hQup := hupper t ht t ⟨ht, le_rfl⟩ x
  have hQlow := hlower t ht t ⟨ht, le_rfl⟩ x
  have hρQ : mneRho ρ hm (v t) x = ρ x * mneQ ρ hm (v t) x := by
    have := (hρpos x).ne'
    simp only [mneQ]
    field_simp
  rw [hρQ]
  have := hρpos x
  constructor <;> nlinarith

end Ratio

end HRS.MS.Mov63

end
