import HRS.MS.Mov63CAux10

/-!
# S6.3, uniqueness chain (N3b, part 6): the coefficient identity for the difference of two solutions

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  See `Mov63CAux1` for the plan.
For two members `P₁, P₂` of the class with the same initial datum, `w = u₁ - u₂` and
`G = -R w + B(u₁,w) + B(w,u₂)`:
`⟨h̃_α,w_t⟩ = ∫_{[0,t]} (-q|α| ⟨h̃_α,w_x⟩ + ⟨h̃_α,G_x⟩) dx` (`mnc_diff_coeff`), and the scalar ODE lemma
(`mnc_ode_formula`) turns this into the variation-of-constants formula.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Diff

variable (H : Mov2dTh d s β q ρ) {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) (P1 P2 : ℝ → Euc d → ℝ)

/-- `w = u₁ - u₂`. -/
def mnc_w (ρ : Euc d → ℝ) (P1 P2 : ℝ → Euc d → ℝ) (m : ℕ) (x : ℝ) : OscSpace d (m : ℝ) :=
  mnc_u ρ P1 m x - mnc_u ρ P2 m x

/-- The forcing `G = -R w + B(u₁,w) + B(w,u₂)` of the difference equation. -/
def mnc_G (x : ℝ) : OscSpace d ((m : ℝ) - movA d s) :=
  -(mov2d_R d s β q ρ (m : ℝ) (mnc_w ρ P1 P2 m x)) +
    mov_B_ext H hm (mnc_u ρ P1 m x) (mnc_w ρ P1 P2 m x) + mov_B_ext H hm (mnc_w ρ P1 P2 m x) (mnc_u ρ P2 m x)

variable {P1 P2}

lemma mnc_F_eigen {α : MultiIndex d} (hα : mnc_Good d β q (mnc_hα d β q α)) (hS : ∀ x, mov_S0 d β q (mnc_hα d β q α) x =
    (q * (α.degree : ℝ)) * mnc_hα d β q α x) (x : ℝ) (P : ℝ → Euc d → ℝ) :
    mnc_F (β := β) H hm P (mnc_hα d β q α) x =
      -(q * (α.degree : ℝ)) * mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (mnc_u ρ P m x) -
        mnc_ipL (mnc_hα d β q α) (mnb_sub_a_nonneg H hm) (mov2d_R d s β q ρ (m : ℝ) (mnc_u ρ P m x)) +
        mnc_ipL (mnc_hα d β q α) (mnb_sub_a_nonneg H hm) (mov_B_ext H hm (mnc_u ρ P m x) (mnc_u ρ P m x)) := by
  unfold mnc_F
  have e : mov_S0 d β q (mnc_hα d β q α) = fun y => (q * (α.degree : ℝ)) * mnc_hα d β q α y := funext hS
  rw [e, mnc_ipL_smul hα.l2]
  ring

theorem mnc_diff_coeff (hβ : 0 < β) (hq : 0 < q) {r1 r2 c1 c2 : ℝ} {f0 : Euc d → ℝ}
    (hcls1 : MovInSmallClass d s q β ρ m r1 c1 f0 P1) (hcls2 : MovInSmallClass d s q β ρ m r2 c2 f0 P2)
    (α : MultiIndex d) {t : ℝ} (ht : 0 ≤ t) :
    mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (mnc_w ρ P1 P2 m t) =
      ∫ x in Set.Icc (0 : ℝ) t,
        (-(q * (α.degree : ℝ)) * mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (mnc_w ρ P1 P2 m x) +
          mnc_ipL (mnc_hα d β q α) (mnb_sub_a_nonneg H hm) (mnc_G H hm P1 P2 x)) := by
  obtain ⟨hg, hgr⟩ := mnc_hα_good (d := d) (β := β) (q := q) hβ hq α
  have hS := mnc_S0_hα (d := d) (β := β) (q := q) hβ hq α
  have Z1 := mnc_Psi_good_zero H hm hcls1 ht hg hgr
  have Z2 := mnc_Psi_good_zero H hm hcls2 ht hg hgr
  unfold mnc_Psi at Z1 Z2
  have h0 : mnc_u ρ P1 m 0 = mnc_u ρ P2 m 0 := by
    unfold mnc_u
    have : movV ρ P1 0 = movV ρ P2 0 := by
      funext x
      unfold movV
      rw [hcls1.init x, hcls2.init x]
    rw [this]
  have i1 := (mnc_F_cont H hm hcls1 (mnc_hα d β q α) t ht).integrableOn_Icc (μ := (volume : Measure ℝ))
  have i2 := (mnc_F_cont H hm hcls2 (mnc_hα d β q α) t ht).integrableOn_Icc (μ := (volume : Measure ℝ))
  have hdiff : mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (mnc_w ρ P1 P2 m t) =
      (∫ x in Set.Icc (0 : ℝ) t, mnc_F (β := β) H hm P1 (mnc_hα d β q α) x) -
        ∫ x in Set.Icc (0 : ℝ) t, mnc_F (β := β) H hm P2 (mnc_hα d β q α) x := by
    have h0' : mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (mnc_u ρ P1 m 0) =
        mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (mnc_u ρ P2 m 0) := by rw [h0]
    have hw : mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (mnc_w ρ P1 P2 m t) =
        mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (mnc_u ρ P1 m t) -
          mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (mnc_u ρ P2 m t) := by
      unfold mnc_w; rw [map_sub]
    rw [hw]
    linarith
  rw [hdiff, ← integral_sub i1 i2]
  refine setIntegral_congr_fun measurableSet_Icc (fun x _ => ?_)
  rw [mnc_F_eigen H hm hg hS x P1, mnc_F_eigen H hm hg hS x P2]
  unfold mnc_G mnc_w
  simp only [map_sub, map_add, map_neg, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply]
  ring

end Diff


/-- Variation of constants for the scalar equation `c' = -λ c + g`, `c(0) = 0` (integral form). -/
theorem mnc_ode_formula {lam T : ℝ} (hT : 0 ≤ T) {c g : ℝ → ℝ} (hc : ContinuousOn c (Set.Icc 0 T))
    (hg : ContinuousOn g (Set.Icc 0 T))
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, c t = ∫ x in Set.Icc (0 : ℝ) t, (-lam * c x + g x)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, c t = ∫ x in Set.Icc (0 : ℝ) t, Real.exp (-lam * (t - x)) * g x := by
  intro t ht
  set f : ℝ → ℝ := fun x => -lam * c x + g x with hf
  have hfc : ContinuousOn f (Set.Icc 0 T) := (continuousOn_const.mul hc).add hg
  have hc' : c 0 = 0 := by simpa using h 0 ⟨le_rfl, hT⟩
  have hcI : ∀ t' ∈ Set.Icc (0 : ℝ) T, c t' = ∫ x in (0 : ℝ)..t', f x := fun t' ht' => by
    rw [h t' ht', intervalIntegral.integral_of_le ht'.1, integral_Icc_eq_integral_Ioc]
  have hder : ∀ t' ∈ Set.Ioo (0 : ℝ) T, HasDerivAt c (f t') t' := by
    intro t' ht'
    have hnhds : Set.Icc (0 : ℝ) T ∈ 𝓝 t' := Icc_mem_nhds ht'.1 ht'.2
    have hcont : ContinuousAt f t' := hfc.continuousAt hnhds
    have hint : IntervalIntegrable f volume 0 t' :=
      (hfc.mono (Set.Icc_subset_Icc le_rfl ht'.2.le)).intervalIntegrable_of_Icc ht'.1.le
    have hd := intervalIntegral.integral_hasDerivAt_right hint
      ((hfc.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t' ht') hcont
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with y hy
    exact hcI y hy
  have hE : ∀ t' ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (fun y => Real.exp (lam * y) * c y)
      (Real.exp (lam * t') * g t') t' := by
    intro t' ht'
    have h1 : HasDerivAt (fun y => Real.exp (lam * y)) (Real.exp (lam * t') * lam) t' := by
      simpa using ((hasDerivAt_id t').const_mul lam).exp
    have h2 := h1.mul (hder t' ht')
    convert h2 using 1
    simp only [hf]
    ring
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    simp [hc']
  · have htT : t ≤ T := ht.2
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl htT
    have hcontE : ContinuousOn (fun y => Real.exp (lam * y) * c y) (Set.Icc 0 t) :=
      ((continuous_const.mul continuous_id).rexp.continuousOn).mul (hc.mono hsub)
    have hcontg : ContinuousOn (fun x => Real.exp (lam * x) * g x) (Set.Icc 0 t) :=
      ((continuous_const.mul continuous_id).rexp.continuousOn).mul (hg.mono hsub)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpos.le hcontE
      (fun x hx => hE x ⟨hx.1, lt_of_lt_of_le hx.2 htT⟩) (hcontg.intervalIntegrable_of_Icc hpos.le)
    simp only [mul_zero, Real.exp_zero, one_mul, hc', sub_zero] at hftc
    have e : ∀ x, Real.exp (-lam * (t - x)) * g x = Real.exp (-lam * t) * (Real.exp (lam * x) * g x) := by
      intro x
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpos.le, hftc,
      ← mul_assoc, ← Real.exp_add]
    simp

end HRS.MS.Mov63
