import HRS.MS.Mov63FAux5

/-!
# S6.3, packet N7 (part 6): the output theorems for N9

Namespace `HRS.MS.Mov63`, prefix `mnf_`.  See `Mov63FAux1`.

* `mnf_bridge`: for `f₀ ∈ C³` with `√ρ f₀ ∈ Σ^m`, the `C³` representative of `x₀ = ofFun (√ρ f₀)` is `√ρ f₀` and `f₀ = V_{x₀}/√ρ`
  (so `mneF0fun = f₀` for every `v` with `v 0 = x₀`);
* `mnf_sup_of_initial`: `MovInitialClass ρ j m ε_* f₀` with `ε_* ≤ 1/4` gives `|f₀| ≤ 1/4` (`cbNorm` is the sum convention);
* **`mov63_positive_solution`**: for the thermal data `H`: the rate `c > 0` of `mov63_mild_existence`, and for every integer `m > d/2+3` there are `ε, C > 0`
  such that for every mass-zero `x₀ ∈ Σ^m` with `‖x₀‖ ≤ ε` and `|V_{x₀}| ≤ (1/4)√ρ` (equivalently `sup |f₀| ≤ 1/4`), the mild solution `v` gives a member
  of `MovInSmallClass .. (C‖x₀‖) (c/2) f₀ ρ_·` with `ρ/2 ≤ ρ_t ≤ 2ρ` for all `t ≥ 0`, `x` (in particular `ρ_t > 0`);
* `mov63_positive_solution_f0`: the same with the datum given as `f₀` (the form of `MovInitialClass`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Bridge

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m)

include hm in
lemma mnf_bridge (H : Mov2dTh d s β q ρ) {f0 : Euc d → ℝ} (hf0 : ContDiff ℝ 3 f0)
    (hosc : MemOsc (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x)) :
    mneV hm (OscSpace.ofFun (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x)) = fun x => Real.sqrt (ρ x) * f0 x := by
  have hc : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun x => Real.sqrt (ρ x) * f0 x) := by
    have h1 : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun x => Real.sqrt (ρ x)) :=
      (mnb_rhoData H).sqrt_smooth.of_le (by simp)
    exact h1.mul (by exact_mod_cast hf0)
  exact mn_repFun_ofFun (mne_hn hm) hosc hc

include hm in
lemma mnf_F0_eq (H : Mov2dTh d s β q ρ) {f0 : Euc d → ℝ} (hf0 : ContDiff ℝ 3 f0)
    (hosc : MemOsc (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x)) {v : ℝ → OscSpace d (m : ℝ)}
    (hv0 : v 0 = OscSpace.ofFun (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x)) :
    mneF0fun d ρ hm v = f0 := by
  funext x
  have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 ((mnb_rhoData H).pos x)
  unfold mneF0fun
  rw [hv0, congrFun (mnf_bridge hm H hf0 hosc) x]
  field_simp

end Bridge

lemma mnf_sup_of_initial {j m : ℕ} {εstar : ℝ} (hε : εstar ≤ 1 / 4) {f0 : Euc d → ℝ}
    (h : MovInitialClass ρ j m εstar f0) (x : Euc d) : |f0 x| ≤ 1 / 4 := by
  have h1 := mnf_norm_le_cbNorm h.cb (Nat.zero_le (j + 1)) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
  have h2 : 0 ≤ oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) := Real.sqrt_nonneg _
  have := h.small
  linarith

section Final

/-- **N7 output (assembly of N5, N6, N7)** -/
theorem mov63_positive_solution (H : Mov2dTh d s β q ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (hm : (d : ℝ) / 2 + 3 < m), ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ x0 : OscSpace d (m : ℝ), MovMassZero ρ (mnd_m_nonneg hm) x0 → ‖x0‖ ≤ ε →
        (∀ x, |mneV hm x0 x| ≤ (1 / 4) * Real.sqrt (ρ x)) →
        ∃ v : ℝ → OscSpace d (m : ℝ), MneMild H hm v ∧ v 0 = x0 ∧
          (∀ t, 0 ≤ t → ‖v t‖ ≤ C * ‖x0‖ * Real.exp (-(c / 2) * t)) ∧
          MovInSmallClass d s q β ρ m (C * ‖x0‖) (c / 2) (mneF0fun d ρ hm v) (mneP d ρ hm v) ∧
          (∀ t, 0 ≤ t → ∀ x, ρ x / 2 ≤ mneP d ρ hm v t x ∧ mneP d ρ hm v t x ≤ 2 * ρ x) := by
  obtain ⟨c, hc, h⟩ := mov63_signed_solution H
  refine ⟨c, hc, fun m hm => ?_⟩
  obtain ⟨ε, C, hε, hC, h2⟩ := h m hm
  obtain ⟨Cs, hCs, hratio⟩ := mnf_ratio hm H
  refine ⟨min ε (c / (2 * Cs * C)), C, lt_min hε (by positivity), hC, fun x0 hmass hnorm hsup => ?_⟩
  have hnε : ‖x0‖ ≤ ε := hnorm.trans (min_le_left _ _)
  have hn2 : ‖x0‖ ≤ c / (2 * Cs * C) := hnorm.trans (min_le_right _ _)
  obtain ⟨v, hM, hv0, hbd, hcls, -, -⟩ := h2 x0 hmass hnε
  -- the ratio bound
  have hsmall : Cs * (C * ‖x0‖) ≤ c / 2 := by
    have h1 : ‖x0‖ * (2 * Cs * C) ≤ c := by
      rwa [le_div_iff₀ (by positivity)] at hn2
    nlinarith
  have hf0 : ∀ x, |mneF0fun d ρ hm v x| ≤ 1 / 4 := fun x => by
    have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 ((mnb_rhoData H).pos x)
    unfold mneF0fun
    rw [hv0, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact hsup x
  have hbd' : ∀ t, 0 ≤ t → ‖v t‖ ≤ (C * ‖x0‖) * Real.exp (-(c / 2) * t) := hbd
  have hrat := hratio v hM (C * ‖x0‖) (c / 2) (mul_nonneg hC.le (norm_nonneg _)) (by positivity) hbd' hsmall hf0
  have hrat' : ∀ t, 0 ≤ t → ∀ x, ρ x / 2 ≤ mneP d ρ hm v t x ∧ mneP d ρ hm v t x ≤ 2 * ρ x := by
    intro t ht x
    rw [mneP_eq hm ht]
    exact hrat t ht x
  have hnn : ∀ t, 0 ≤ t → ∀ x, 0 ≤ mneP d ρ hm v t x := fun t ht x => by
    have := (mnb_rhoData H).pos x
    linarith [(hrat' t ht x).1]
  exact ⟨v, hM, hv0, hbd, hcls hnn, hrat'⟩

/-- The same with the datum given by `f₀` (the form of `MovInitialClass`): `f₀ ∈ C³`, `√ρ f₀ ∈ Σ^m` of small norm, mass zero, `sup |f₀| ≤ 1/4`. -/
theorem mov63_positive_solution_f0 (H : Mov2dTh d s β q ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (hm : (d : ℝ) / 2 + 3 < m), ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ f0 : Euc d → ℝ, ContDiff ℝ 3 f0 → ∀ hosc : MemOsc (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x),
        MovMassZero ρ (mnd_m_nonneg hm) (OscSpace.ofFun (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x)) →
        oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) ≤ ε → (∀ x, |f0 x| ≤ 1 / 4) →
        ∃ v : ℝ → OscSpace d (m : ℝ), MneMild H hm v ∧
          v 0 = OscSpace.ofFun (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) ∧
          (∀ t, 0 ≤ t → ‖v t‖ ≤ C * oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) * Real.exp (-(c / 2) * t)) ∧
          MovInSmallClass d s q β ρ m (C * oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x)) (c / 2) f0
            (mneP d ρ hm v) ∧
          (∀ t, 0 ≤ t → ∀ x, ρ x / 2 ≤ mneP d ρ hm v t x ∧ mneP d ρ hm v t x ≤ 2 * ρ x) := by
  obtain ⟨c, hc, h⟩ := mov63_positive_solution H
  refine ⟨c, hc, fun m hm => ?_⟩
  obtain ⟨ε, C, hε, hC, h2⟩ := h m hm
  refine ⟨ε, C, hε, hC, fun f0 hf0 hosc hmass hnorm hsup => ?_⟩
  set x0 := OscSpace.ofFun (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) with hx0
  have hn : ‖x0‖ = oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) := OscSpace.norm_ofFun _ hosc
  have hV := mnf_bridge hm H hf0 hosc
  obtain ⟨v, hM, hv0, hbd, hcls, hrat⟩ := h2 x0 hmass (hn ▸ hnorm) (fun x => by
    rw [hx0, congrFun hV x, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sqrt_nonneg (ρ x), hsup x, abs_nonneg (f0 x)])
  have hF := mnf_F0_eq hm H hf0 hosc hv0
  rw [hF, hn] at hcls
  exact ⟨v, hM, hv0, fun t ht => by rw [← hn]; exact hbd t ht, hcls, hrat⟩

end Final

end HRS.MS.Mov63

end
