import HRS.MS.Mov63FAux2
import HRS.MS.Mov63EAux12

/-!
# S6.3, packet N7 (part 3): thermal data, uniform bounds, and the growth class of `Q`

Namespace `HRS.MS.Mov63`, prefix `mnf_`.  See `Mov63FAux1`.

* `mnf_euler`: `ν ∇log ρ = -(q x + ∇g*ρ)` (Euler equation, `mv0_thermal_force`); `mnf_M0`: `‖∇g*ρ‖ ≤ M₀`;
* `mnf_rho_lower`: the Gaussian lower bound `ρ(x) ≥ ρ(0) exp(-(βq/2)‖x‖² - βM₀‖x‖)` (integrate `∇log ρ` along the ray `τ ↦ τx`);
* `mnf_Vbound`, `mnf_Fbound`, `mnf_Abound`: `|V_u|, |F_u|, |A_u| ≤ C‖u‖_{Σ^m}` (sup norms; `mn_force_bound`, `j = 0`), `A_u = div F_u + ⟨∇log ρ, F_u⟩`;
* `mnf_drift_bound`: `⟨ν∇log ρ + F_u, x⟩ ≤ -q‖x‖² + (M₀ + C‖u‖)‖x‖`;
* `mnf_Q_growth`: `|Q_u(x)| ≤ K exp((5βq/16)‖x‖²)` for `‖u‖ ≤ B` (`Q_u = ρ_u/ρ = 1 + V_u/√ρ`);
* `mnf_hgrow`: the coercivity hypothesis of `mnf_comparison` from a bound `|P| ≤ K exp(κ₀‖x‖²)`, `κ₀ < κ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.PoissonSpike

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Thermal

variable (H : Mov2dTh d s β q ρ)

include H in
lemma mnf_euler (x : Euc d) :
    β⁻¹ • gradient (fun y => Real.log (ρ y)) x = -(q • x + movForce d s ρ x) := by
  have hE := HRS.MS.Mov0.mv0_thermal_force H.hd H.hs0 H.hsd H.hq H.hβ H.hρ x
  have h0 : β⁻¹ • gradient (fun y => Real.log (ρ y)) x + (q • x + movForce d s ρ x) = 0 := by
    rw [← add_assoc]; exact hE
  exact eq_neg_of_add_eq_zero_left h0

include H in
lemma mnf_grad_log (x : Euc d) :
    gradient (fun y => Real.log (ρ y)) x = -(β • (q • x + movForce d s ρ x)) := by
  have h := mnf_euler H x
  have hβ : β ≠ 0 := H.hβ.ne'
  calc gradient (fun y => Real.log (ρ y)) x = β • (β⁻¹ • gradient (fun y => Real.log (ρ y)) x) := by
        rw [smul_smul, mul_inv_cancel₀ hβ, one_smul]
    _ = _ := by rw [h, smul_neg]

lemma mnf_log_cd (H : Mov2dTh d s β q ρ) : ContDiff ℝ 2 (fun y => Real.log (ρ y)) := by
  have hpos := (mnb_rhoData H).pos
  have := (mnc_rho_smooth H).log (fun x => (hpos x).ne')
  exact this.of_le (by simp)

include H in
/-- The Gaussian lower bound of the thermal density along rays. -/
lemma mnf_rho_lower {M0 : ℝ} (hM0 : ∀ x, ‖movForce d s ρ x‖ ≤ M0) (x : Euc d) :
    ρ 0 * Real.exp (-(β * q / 2) * ‖x‖ ^ 2 - β * M0 * ‖x‖) ≤ ρ x := by
  have hpos := (mnb_rhoData H).pos
  have hcd := mnf_log_cd H
  set r : ℝ := ‖x‖ with hr
  set h : ℝ → ℝ := fun τ => Real.log (ρ (τ • x)) + (β * q * r ^ 2 / 2) * τ ^ 2 + β * M0 * r * τ with hh
  have hhd : ∀ τ, HasDerivAt h (fderiv ℝ (fun y => Real.log (ρ y)) (τ • x) x + β * q * r ^ 2 * τ + β * M0 * r) τ := by
    intro τ
    have h1 := line_hasDerivAt hcd 0 x τ
    simp only [zero_add] at h1
    have h2 : HasDerivAt (fun τ : ℝ => (β * q * r ^ 2 / 2) * τ ^ 2) (β * q * r ^ 2 * τ) τ := by
      have := ((hasDerivAt_pow 2 τ).const_mul (β * q * r ^ 2 / 2))
      convert this using 1
      simp; ring
    have h3 : HasDerivAt (fun τ : ℝ => β * M0 * r * τ) (β * M0 * r) τ := by
      simpa using (hasDerivAt_id τ).const_mul (β * M0 * r)
    exact (h1.add h2).add h3
  have hmono : Monotone h := by
    refine monotone_of_deriv_nonneg (fun τ => (hhd τ).differentiableAt) (fun τ => ?_)
    rw [(hhd τ).deriv]
    rw [← HRS.MS.PoisKolm.kl_inner_gradient, mnf_grad_log H]
    have hF : inner ℝ x (movForce d s ρ (τ • x)) ≤ r * M0 :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hM0 _) (norm_nonneg _))
    have hβ := H.hβ
    have hb := mul_le_mul_of_nonneg_left hF hβ.le
    simp only [inner_neg_right, inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq]
    rw [← hr]
    nlinarith
  have h01 := hmono (zero_le_one : (0:ℝ) ≤ 1)
  simp only [hh] at h01
  simp only [zero_smul, one_smul, zero_pow two_ne_zero, mul_zero, add_zero, one_pow, mul_one] at h01
  have hρx := hpos x
  have hρ0 := hpos 0
  have hlog : Real.log (ρ 0) ≤ Real.log (ρ x) + β * q * r ^ 2 / 2 + β * M0 * r := h01
  have hexp : ρ 0 ≤ ρ x * Real.exp (β * q * r ^ 2 / 2 + β * M0 * r) := by
    have h2 : Real.log (ρ 0) ≤ Real.log (ρ x * Real.exp (β * q * r ^ 2 / 2 + β * M0 * r)) := by
      rw [Real.log_mul hρx.ne' (Real.exp_pos _).ne', Real.log_exp]
      linarith
    exact (Real.log_le_log_iff hρ0 (by positivity)).1 h2
  have e1 : Real.exp (-(β * q / 2) * r ^ 2 - β * M0 * r) =
      (Real.exp (β * q * r ^ 2 / 2 + β * M0 * r))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [e1, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact hexp

end Thermal

section Bounds

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) (H : Mov2dTh d s β q ρ)

lemma mnf_norm_le_cbNorm {f : Euc d → ℝ} {r : ℕ} (hf : MemCb r f) {j : ℕ} (hj : j ≤ r) (x : Euc d) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ HRS.cbNorm r f := by
  unfold HRS.cbNorm
  have hmem : j ∈ Finset.range (r + 1) := Finset.mem_range.2 (by omega)
  have h1 : ‖iteratedFDeriv ℝ j f x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j f z‖ :=
    le_ciSup (hf.2 j hj) x
  have h2 : ⨆ z, ‖iteratedFDeriv ℝ j f z‖ ≤ ∑ i ∈ Finset.range (r + 1), ⨆ z, ‖iteratedFDeriv ℝ i f z‖ :=
    Finset.single_le_sum (f := fun i => ⨆ z, ‖iteratedFDeriv ℝ i f z‖)
      (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) hmem
  exact h1.trans h2

include H in
/-- `|V_u(x)| ≤ C‖u‖` (sup-norm embedding). -/
lemma mnf_Vbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : OscSpace d (m : ℝ)) (x : Euc d), |mneV hm u x| ≤ C * ‖u‖ := by
  have hm0 : (d : ℝ) / 2 + ((0 : ℕ) : ℝ) + 2 < m := by push_cast; linarith
  obtain ⟨C, hC0, hC⟩ := mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ 0 m hm0
  refine ⟨C, hC0, fun u x => ?_⟩
  obtain ⟨-, h2, -, -, -⟩ := hC (mneV hm u) (mneV_cd hm u).continuous (mneV_memOsc hm u)
  have := h2 0 (by norm_num) x
  rw [norm_iteratedFDeriv_zero, mneV_norm hm u] at this
  simpa [Real.norm_eq_abs] using this

include H in
/-- `|A_u(x)| ≤ C‖u‖`, `A_u = div F_u + ⟨∇log ρ, F_u⟩` (the zero-order coefficient of the `Q`-equation). -/
lemma mnf_Abound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : OscSpace d (m : ℝ)) (x : Euc d),
    |movDiv (mneFo d s ρ hm u) x + inner ℝ (gradient (fun y => Real.log (ρ y)) x) (mneFo d s ρ hm u x)| ≤
      C * ‖u‖ := by
  have hm0 : (d : ℝ) / 2 + ((0 : ℕ) : ℝ) + 2 < m := by push_cast; linarith
  obtain ⟨C, hC0, hC⟩ := mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ 0 m hm0
  refine ⟨C, hC0, fun u x => ?_⟩
  obtain ⟨-, -, -, h4, h5⟩ := hC (mneV hm u) (mneV_cd hm u).continuous (mneV_memOsc hm u)
  rw [mneV_norm hm u] at h5
  have hB : 0 ≤ C * ‖u‖ := mul_nonneg hC0 (norm_nonneg _)
  have h6 : ENNReal.ofReal (HRS.cbNorm 0 (fun x => movDiv (movForce d s (fun y => Real.sqrt (ρ y) * mneV hm u y)) x +
        inner ℝ (gradient (fun y => Real.log (ρ y)) x)
          (movForce d s (fun y => Real.sqrt (ρ y) * mneV hm u y) x))) ≤ ENNReal.ofReal (C * ‖u‖) :=
    le_trans le_add_self h5
  have h7 := (ENNReal.ofReal_le_ofReal_iff hB).1 h6
  have h8 := mnf_norm_le_cbNorm h4 (le_refl 0) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h8
  exact h8.trans h7

include H in
/-- The drift `b_u = ν ∇log ρ + F_u` satisfies `⟨b_u(x), x⟩ ≤ -q‖x‖² + (M₀ + C‖u‖)‖x‖`. -/
lemma mnf_drift_bound {M0 C : ℝ} (hM0 : ∀ x, ‖movForce d s ρ x‖ ≤ M0)
    (hC : ∀ (u : OscSpace d (m : ℝ)) x, ‖mneFo d s ρ hm u x‖ ≤ C * ‖u‖) (u : OscSpace d (m : ℝ)) (x : Euc d) :
    inner ℝ (β⁻¹ • gradient (fun y => Real.log (ρ y)) x + mneFo d s ρ hm u x) x ≤
      -q * ‖x‖ ^ 2 + (M0 + C * ‖u‖) * ‖x‖ := by
  rw [mnf_euler H x, inner_add_left, inner_neg_left, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
  have h1 : inner ℝ (movForce d s ρ x) x ≥ -(M0 * ‖x‖) := by
    have := neg_le_of_abs_le (abs_real_inner_le_norm (movForce d s ρ x) x)
    nlinarith [mul_le_mul_of_nonneg_right (hM0 x) (norm_nonneg x), norm_nonneg (movForce d s ρ x)]
  have h2 : inner ℝ (mneFo d s ρ hm u x) x ≤ C * ‖u‖ * ‖x‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hC u x) (norm_nonneg _))
  simp only [conj_trivial]
  nlinarith

include hm H in
/-- `‖∇g*ρ‖ ≤ M₀` for the thermal state. -/
lemma mnf_M0 : ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ x, ‖movForce d s ρ x‖ ≤ M0 := by
  obtain ⟨C, hC0, hC⟩ := mne_force_facts (s := s) (β := β) (q := q) (ρ := ρ) hm H
  refine ⟨C * ‖mneU0 m ρ‖, mul_nonneg hC0 (norm_nonneg _), fun x => ?_⟩
  rw [congrFun (mneF0 hm H) x]
  exact (hC (mneU0 m ρ)).2.1 x

include H in
lemma mnf_Q_eq (u : OscSpace d (m : ℝ)) (x : Euc d) :
    mneQ ρ hm u x = 1 + mneV hm u x / Real.sqrt (ρ x) := by
  have hρx := (mnb_rhoData H).pos x
  have hσ : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 hρx
  have hss : Real.sqrt (ρ x) * Real.sqrt (ρ x) = ρ x := Real.mul_self_sqrt hρx.le
  show (ρ x + Real.sqrt (ρ x) * mneV hm u x) / ρ x = 1 + mneV hm u x / Real.sqrt (ρ x)
  generalize Real.sqrt (ρ x) = σ at hσ hss
  generalize mneV hm u x = V
  rw [← hss]
  field_simp

include H in
/-- **Growth class of `Q_u`**: `|Q_u(x)| ≤ K exp((5βq/16)‖x‖²)` when `|V_u| ≤ V_b`. -/
lemma mnf_Q_growth {M0 Vb : ℝ} (hM0 : ∀ x, ‖movForce d s ρ x‖ ≤ M0) (hVb : 0 ≤ Vb)
    (u : OscSpace d (m : ℝ)) (hV : ∀ x, |mneV hm u x| ≤ Vb) (x : Euc d) :
    |mneQ ρ hm u x| ≤ (1 + Vb * ((Real.sqrt (ρ 0))⁻¹ * Real.exp (β * M0 ^ 2 / q))) *
      Real.exp ((5 * β * q / 16) * ‖x‖ ^ 2) := by
  have hpos := (mnb_rhoData H).pos
  have hρx := hpos x
  have hρ0 := hpos 0
  have hσ : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 hρx
  have hσ0 : 0 < Real.sqrt (ρ 0) := Real.sqrt_pos.2 hρ0
  have hβ := H.hβ
  have hq := H.hq
  set r : ℝ := ‖x‖ with hr
  set E : ℝ := β * q * r ^ 2 / 2 + β * M0 * r with hE
  have hlow := mnf_rho_lower H hM0 x
  have e1 : Real.exp (-(β * q / 2) * r ^ 2 - β * M0 * r) = Real.exp (-E) := by
    congr 1; rw [hE]; ring
  rw [e1] at hlow
  set a : ℝ := Real.sqrt (ρ 0) * Real.exp (-(E / 2)) with ha
  have hapos : 0 < a := by positivity
  have ha2 : a * a = ρ 0 * Real.exp (-E) := by
    rw [ha]
    have : Real.exp (-(E / 2)) * Real.exp (-(E / 2)) = Real.exp (-E) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.sqrt (ρ 0) * Real.exp (-(E / 2)) * (Real.sqrt (ρ 0) * Real.exp (-(E / 2)))
        = (Real.sqrt (ρ 0) * Real.sqrt (ρ 0)) * (Real.exp (-(E / 2)) * Real.exp (-(E / 2))) := by ring
      _ = _ := by rw [this, Real.mul_self_sqrt hρ0.le]
  have haσ : a ≤ Real.sqrt (ρ x) := by
    have hss : Real.sqrt (ρ x) * Real.sqrt (ρ x) = ρ x := Real.mul_self_sqrt hρx.le
    by_contra hcon
    push Not at hcon
    nlinarith
  have hVx := hV x
  have h1 : |mneV hm u x / Real.sqrt (ρ x)| ≤ Vb / a := by
    rw [abs_div, abs_of_pos hσ]
    calc |mneV hm u x| / Real.sqrt (ρ x) ≤ Vb / Real.sqrt (ρ x) :=
          div_le_div_of_nonneg_right hVx hσ.le
      _ ≤ Vb / a := div_le_div_of_nonneg_left hVb hapos haσ
  have h2 : Vb / a = Vb * ((Real.sqrt (ρ 0))⁻¹ * Real.exp (E / 2)) := by
    rw [ha, Real.exp_neg]
    field_simp
  have h3 : Real.exp (E / 2) ≤ Real.exp (β * M0 ^ 2 / q) * Real.exp ((5 * β * q / 16) * r ^ 2) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : 0 ≤ (β / q) * (q * r / 4 - M0) ^ 2 := by positivity
    have e : (β / q) * (q * r / 4 - M0) ^ 2 = β * q * r ^ 2 / 16 - β * M0 * r / 2 + β * M0 ^ 2 / q := by
      field_simp; ring
    rw [hE]
    nlinarith
  have h4 : 1 ≤ Real.exp ((5 * β * q / 16) * r ^ 2) := Real.one_le_exp (by positivity)
  rw [mnf_Q_eq hm H u x]
  have hnn : 0 ≤ Vb * (Real.sqrt (ρ 0))⁻¹ := by positivity
  calc |1 + mneV hm u x / Real.sqrt (ρ x)| ≤ 1 + |mneV hm u x / Real.sqrt (ρ x)| := by
        calc _ ≤ |(1:ℝ)| + |mneV hm u x / Real.sqrt (ρ x)| := abs_add_le _ _
          _ = _ := by rw [abs_one]
    _ ≤ 1 + Vb * ((Real.sqrt (ρ 0))⁻¹ * (Real.exp (β * M0 ^ 2 / q) * Real.exp ((5 * β * q / 16) * r ^ 2))) := by
        have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ Vb * (Real.sqrt (ρ 0))⁻¹)
        nlinarith
    _ ≤ _ := by
        have := Real.exp_pos (β * M0 ^ 2 / q)
        nlinarith [mul_nonneg hnn this.le]

end Bounds

section Growth

/-- Coercivity: a bound `|P| ≤ K exp(κ₀‖x‖²)`, `κ₀ < κ`, gives `P > -ε φ` outside a ball, for the Lyapunov function. -/
lemma mnf_hgrow {K κ0 κ l T : ℝ} (hK : 0 ≤ K) (hκ : κ0 < κ) (hl : 0 ≤ l) {P : ℝ → Euc d → ℝ}
    (hP : ∀ t ∈ Icc 0 T, ∀ x, |P t x| ≤ K * Real.exp (κ0 * ‖x‖ ^ 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x : Euc d, R ≤ ‖x‖ → -(ε * mnf_lyap l κ t x) < P t x := by
  intro ε hε
  set δ : ℝ := κ - κ0 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  refine ⟨K / (ε * δ) + 1, fun t ht x hx => ?_⟩
  set r : ℝ := ‖x‖ with hr
  have hKp : 0 ≤ K / (ε * δ) := by positivity
  have hr1 : 1 ≤ r := by linarith
  have hr2 : K / (ε * δ) < r ^ 2 := by nlinarith
  have h1 : K < ε * δ * r ^ 2 := by
    have := (div_lt_iff₀ (by positivity : 0 < ε * δ)).1 hr2
    linarith
  have h2 : δ * r ^ 2 < Real.exp (δ * r ^ 2) := by
    have := Real.add_one_lt_exp (show δ * r ^ 2 ≠ 0 by positivity)
    linarith
  have h3 : K < ε * Real.exp (δ * r ^ 2) := by nlinarith
  have h4 : Real.exp (κ * r ^ 2) = Real.exp (κ0 * r ^ 2) * Real.exp (δ * r ^ 2) := by
    rw [← Real.exp_add]; congr 1; rw [hδ]; ring
  have h5 : Real.exp (κ * r ^ 2) ≤ mnf_lyap l κ t x := by
    unfold mnf_lyap
    refine Real.exp_le_exp.2 ?_
    nlinarith [ht.1]
  have h6 : K * Real.exp (κ0 * r ^ 2) < ε * mnf_lyap l κ t x := by
    have : K * Real.exp (κ0 * r ^ 2) < ε * Real.exp (δ * r ^ 2) * Real.exp (κ0 * r ^ 2) :=
      mul_lt_mul_of_pos_right h3 (Real.exp_pos _)
    have h7 : ε * Real.exp (κ * r ^ 2) ≤ ε * mnf_lyap l κ t x := mul_le_mul_of_nonneg_left h5 hε.le
    rw [h4] at h7
    nlinarith
  have := hP t ht x
  have := neg_abs_le (P t x)
  linarith

end Growth

end HRS.MS.Mov63

end
