import HRS.Uniform.Q54Aux16

/-!
# Q54, part 17: strong continuity of the dual evolution on `E_r`

From the function-level Hölder estimate (`HoldAt` at level `r - 2`), the cocycle law and quasi-contractivity at the levels
`r - 2` and `r`, the block bounds `E_{r-2} → E_r` of the differences `V^{t',u} - V^{t,u}` and `V^{t,u} - V^{t,u'}` give a
Hölder-`1/2` estimate on finite vectors; uniform boundedness and density give strong continuity on the triangle.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.Uniform.Q48b

variable {d : ℕ}

/-- the Hölder estimate at the diagonal, at level `a`. -/
def HoldAt (J : ℕ) (Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ) (a A B : ℝ) : Prop :=
  ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ φ, Dom J φ →
    MemSobolev a (fun x => Up u t φ x - φ x) ∧
      sobolevNorm a (fun x => Up u t φ x - φ x) ^ 2 ≤
        B * sobolevNorm (a + 2) φ ^ 2 * (t - u) * Real.exp (A * (t - u))

structure ContData (J : ℕ) (Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ) (r : ℝ)
    (Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r) (C C₂ A B : ℝ) : Prop where
  core : EvoCore J Up
  hr : r ≤ J
  quasi : QuasiAt J Up r C
  quasi2 : QuasiAt J Up (r - 2) C₂
  hold : HoldAt J Up (r - 2) A B
  hB : 0 ≤ B
  dual : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ (z : NegSobolev d r) (φ : Torus d → ℝ), Dom J φ →
    NegSobolev.eval (Vev t u z) φ = NegSobolev.eval z (Up u t φ)
  bound : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp (C * (t - u))

theorem exp_mul_le (C : ℝ) {x T : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ T) :
    Real.exp (C * x) ≤ Real.exp (|C| * T) := by
  refine Real.exp_le_exp.2 ?_
  calc C * x ≤ |C| * x := mul_le_mul_of_nonneg_right (le_abs_self C) hx0
    _ ≤ |C| * T := mul_le_mul_of_nonneg_left hxT (abs_nonneg C)

theorem eval_sub_left {r : ℝ} (F G : NegSobolev d r) {φ : Torus d → ℝ} (hφ : MemSobolev r φ) :
    NegSobolev.eval (F - G) φ = NegSobolev.eval F φ - NegSobolev.eval G φ := by
  rw [eval_eq_inner r (F - G) hφ, eval_eq_inner r F hφ, eval_eq_inner r G hφ, inner_sub_left]

section Func

variable {J : ℕ} {Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ} {r : ℝ}
  {Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r} {C C₂ A B : ℝ}

/-- `t`-direction function-level estimate. -/
theorem fn_hold_t (h : ContData J Up r Vev C C₂ A B) (T : ℝ) {u t t' : ℝ} (hu : 0 ≤ u) (hut : u ≤ t)
    (htt' : t ≤ t') (ht'T : t' ≤ T) {φ : Torus d → ℝ} (hφ : Dom J φ) :
    MemSobolev (r - 2) (fun x => Up u t' φ x - Up u t φ x) ∧
      sobolevNorm (r - 2) (fun x => Up u t' φ x - Up u t φ x) ^ 2 ≤
        (Real.exp (|C₂| * T) ^ 2 * B * Real.exp (|A| * T)) * (t' - t) * sobolevNorm r φ ^ 2 := by
  have ht : 0 ≤ t := hu.trans hut
  have hφ' : Dom J (Up t t' φ) := h.core.dom t t' ht htt' φ hφ
  have hcoc := h.core.cocycle u t t' hu hut htt' φ hφ
  set ψ : Torus d → ℝ := fun x => 1 * Up t t' φ x + (-1) * φ x with hψ
  have hψd : Dom J ψ := dom_closed hφ' hφ 1 (-1)
  have hdiff : (fun x => Up u t' φ x - Up u t φ x) = Up u t ψ := by
    rw [hψ, h.core.lin u t hu hut _ _ hφ' hφ 1 (-1), hcoc]
    funext x; ring
  have hψe : (fun x => Up t t' φ x - φ x) = ψ := by
    funext x; simp only [hψ]; ring
  obtain ⟨hq1, hq2⟩ := h.quasi2 u t hu hut ψ hψd
  obtain ⟨hh1, hh2⟩ := h.hold t t' ht htt' φ hφ
  rw [hψe] at hh1 hh2
  rw [hdiff]
  refine ⟨hq1, ?_⟩
  have e2 : r - 2 + 2 = r := by ring
  rw [e2] at hh2
  have hn0 : 0 ≤ sobolevNorm (r - 2) ψ := Real.sqrt_nonneg _
  have hE : Real.exp (C₂ * (t - u)) ≤ Real.exp (|C₂| * T) :=
    exp_mul_le C₂ (by linarith) (by linarith)
  have hE2 : Real.exp (A * (t' - t)) ≤ Real.exp (|A| * T) :=
    exp_mul_le A (by linarith) (by linarith)
  have hsq : sobolevNorm (r - 2) (Up u t ψ) ^ 2 ≤
      (Real.exp (|C₂| * T) * sobolevNorm (r - 2) ψ) ^ 2 := by
    refine pow_le_pow_left₀ (Real.sqrt_nonneg _) (hq2.trans ?_) 2
    exact mul_le_mul_of_nonneg_right hE hn0
  refine hsq.trans ?_
  rw [mul_pow]
  have hN : 0 ≤ sobolevNorm r φ ^ 2 := sq_nonneg _
  have hτ : 0 ≤ t' - t := by linarith
  calc Real.exp (|C₂| * T) ^ 2 * sobolevNorm (r - 2) ψ ^ 2
      ≤ Real.exp (|C₂| * T) ^ 2 * (B * sobolevNorm r φ ^ 2 * (t' - t) * Real.exp (A * (t' - t))) :=
        mul_le_mul_of_nonneg_left hh2 (sq_nonneg _)
    _ ≤ Real.exp (|C₂| * T) ^ 2 * (B * sobolevNorm r φ ^ 2 * (t' - t) * Real.exp (|A| * T)) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hE2 (mul_nonneg (mul_nonneg h.hB hN) hτ)
    _ = _ := by ring

/-- `u`-direction function-level estimate. -/
theorem fn_hold_u (h : ContData J Up r Vev C C₂ A B) (T : ℝ) {u u' t : ℝ} (hu : 0 ≤ u) (huu' : u ≤ u')
    (hu't : u' ≤ t) (htT : t ≤ T) {φ : Torus d → ℝ} (hφ : Dom J φ) :
    MemSobolev (r - 2) (fun x => Up u t φ x - Up u' t φ x) ∧
      sobolevNorm (r - 2) (fun x => Up u t φ x - Up u' t φ x) ^ 2 ≤
        (Real.exp (|C| * T) ^ 2 * B * Real.exp (|A| * T)) * (u' - u) * sobolevNorm r φ ^ 2 := by
  have hu' : 0 ≤ u' := hu.trans huu'
  have hχ : Dom J (Up u' t φ) := h.core.dom u' t hu' hu't φ hφ
  have hcoc := h.core.cocycle u u' t hu huu' hu't φ hφ
  have hdiff : (fun x => Up u t φ x - Up u' t φ x) =
      fun x => Up u u' (Up u' t φ) x - Up u' t φ x := by
    funext x
    rw [hcoc]
  obtain ⟨hh1, hh2⟩ := h.hold u u' hu huu' (Up u' t φ) hχ
  obtain ⟨-, hq⟩ := h.quasi u' t hu' hu't φ hφ
  rw [hdiff]
  refine ⟨hh1, ?_⟩
  have e2 : r - 2 + 2 = r := by ring
  rw [e2] at hh2
  have hE : Real.exp (C * (t - u')) ≤ Real.exp (|C| * T) :=
    exp_mul_le C (by linarith) (by linarith)
  have hE2 : Real.exp (A * (u' - u)) ≤ Real.exp (|A| * T) :=
    exp_mul_le A (by linarith) (by linarith)
  have hsq : sobolevNorm r (Up u' t φ) ^ 2 ≤ (Real.exp (|C| * T) * sobolevNorm r φ) ^ 2 := by
    refine pow_le_pow_left₀ (Real.sqrt_nonneg _) (hq.trans ?_) 2
    exact mul_le_mul_of_nonneg_right hE (Real.sqrt_nonneg _)
  have hτ : 0 ≤ u' - u := by linarith
  refine hh2.trans ?_
  rw [mul_pow] at hsq
  calc B * sobolevNorm r (Up u' t φ) ^ 2 * (u' - u) * Real.exp (A * (u' - u))
      ≤ B * (Real.exp (|C| * T) ^ 2 * sobolevNorm r φ ^ 2) * (u' - u) * Real.exp (A * (u' - u)) := by
        gcongr
        exact h.hB
    _ ≤ B * (Real.exp (|C| * T) ^ 2 * sobolevNorm r φ ^ 2) * (u' - u) * Real.exp (|A| * T) := by
        refine mul_le_mul_of_nonneg_left hE2 ?_
        exact mul_nonneg (mul_nonneg h.hB (mul_nonneg (sq_nonneg _) (sq_nonneg _))) hτ
    _ = _ := by ring

end Func

section Op

variable {J : ℕ} {Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ} {r : ℝ}
  {Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r} {C C₂ A B : ℝ}

/-- the difference of two dual operators is dual to the difference of the function maps. -/
theorem dual_diff (h : ContData J Up r Vev C C₂ A B) {u₁ t₁ u₂ t₂ : ℝ} (h1 : 0 ≤ u₁) (h1' : u₁ ≤ t₁)
    (h2 : 0 ≤ u₂) (h2' : u₂ ≤ t₂) (z : NegSobolev d r) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    NegSobolev.eval ((Vev t₁ u₁ - Vev t₂ u₂) z) φ =
      NegSobolev.eval z (fun x => Up u₁ t₁ φ x - Up u₂ t₂ φ x) := by
  have hD : Dom J φ := dom_smooth hφ
  have hM : MemSobolev r φ := memSobolev_of_dom h.hr hD
  have hf := h.core.dom u₁ t₁ h1 h1' φ hD
  have hg := h.core.dom u₂ t₂ h2 h2' φ hD
  have hfg := dom_sub hf hg
  rw [ContinuousLinearMap.sub_apply, eval_sub_left _ _ hM, h.dual u₁ t₁ h1 h1' z φ hD,
    h.dual u₂ t₂ h2 h2' z φ hD,
    eval_sub_fun z (memSobolev_of_dom h.hr hfg) (memSobolev_of_dom h.hr hf) (memSobolev_of_dom h.hr hg)]

/-- block bound for a difference, from a function-level bound on all `φ ∈ Dom J`. -/
theorem fin_bound_of_fn (h : ContData J Up r Vev C C₂ A B) {u₁ t₁ u₂ t₂ : ℝ} (h1 : 0 ≤ u₁)
    (h1' : u₁ ≤ t₁) (h2 : 0 ≤ u₂) (h2' : u₂ ≤ t₂) (κ : ℝ) (hκ : 0 ≤ κ)
    (hfn : ∀ φ : Torus d → ℝ, Dom J φ →
      MemSobolev (r - 2) (fun x => Up u₁ t₁ φ x - Up u₂ t₂ φ x) ∧
        sobolevNorm (r - 2) (fun x => Up u₁ t₁ φ x - Up u₂ t₂ φ x) ^ 2 ≤ κ * sobolevNorm r φ ^ 2)
    (S : Finset (NonzeroLattice d)) (ζ : NonzeroLattice d → ℝ) :
    ‖(Vev t₁ u₁ - Vev t₂ u₂) (q48bFin r S ζ)‖ ^ 2 ≤
      κ * ∑ k ∈ S, q48bW k ^ (-2 * (r - 2)) * ζ k ^ 2 := by
  have hW : WB2 r (r - 2) (Real.sqrt κ) (q48bMat r (Vev t₁ u₁ - Vev t₂ u₂)) := by
    refine wb2_of_duality (fun φ x => Up u₁ t₁ φ x - Up u₂ t₂ φ x) _
      (fun z φ hφ => dual_diff h h1 h1' h2 h2' z hφ) _ (Real.sqrt_nonneg _) fun T c => ?_
    obtain ⟨hm, hn⟩ := hfn (q48bTest T c) (dom_smooth (q48bTest_smooth T c))
    refine ⟨hm, ?_⟩
    have hN : sobolevNorm r (q48bTest T c) = Real.sqrt (∑ l ∈ T, q48bW l ^ (2 * r) * c l ^ 2) :=
      q48bTest_sobolevNorm T c r
    rw [← hN]
    have hs : 0 ≤ Real.sqrt κ * sobolevNorm r (q48bTest T c) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    refine le_of_sq_le_sq ?_ hs
    rw [mul_pow, Real.sq_sqrt hκ]
    exact hn
  have := norm_fin_le (Vev t₁ u₁ - Vev t₂ u₂) hW S ζ
  rwa [Real.sq_sqrt hκ] at this

end Op

/-- Hölder-`1/2` continuity on a set implies continuity. -/
theorem continuousOn_of_holder {E : Type*} [NormedAddCommGroup E] (f : ℝ × ℝ → E) (s : Set (ℝ × ℝ))
    (c : ℝ) (h : ∀ p ∈ s, ∀ q ∈ s,
      ‖f p - f q‖ ≤ c * (Real.sqrt |p.1 - q.1| + Real.sqrt |p.2 - q.2|)) : ContinuousOn f s := by
  rw [Metric.continuousOn_iff]
  intro p hp ε hε
  have hc : 0 < |c| + 1 := by positivity
  set η : ℝ := ε / (2 * (|c| + 1)) with hη
  have hη0 : 0 < η := by positivity
  refine ⟨η ^ 2, by positivity, fun q hq hdist => ?_⟩
  rw [dist_eq_norm]
  have hd1 : |q.1 - p.1| < η ^ 2 := by
    have := (le_max_left (dist q.1 p.1) (dist q.2 p.2)).trans_lt (by rwa [Prod.dist_eq] at hdist)
    rwa [Real.dist_eq] at this
  have hd2 : |q.2 - p.2| < η ^ 2 := by
    have := (le_max_right (dist q.1 p.1) (dist q.2 p.2)).trans_lt (by rwa [Prod.dist_eq] at hdist)
    rwa [Real.dist_eq] at this
  have hs1 : Real.sqrt |q.1 - p.1| ≤ η := by
    rw [show η = Real.sqrt (η ^ 2) from (Real.sqrt_sq hη0.le).symm]
    exact Real.sqrt_le_sqrt hd1.le
  have hs2 : Real.sqrt |q.2 - p.2| ≤ η := by
    rw [show η = Real.sqrt (η ^ 2) from (Real.sqrt_sq hη0.le).symm]
    exact Real.sqrt_le_sqrt hd2.le
  have hb := h q hq p hp
  have h3 : c * (Real.sqrt |q.1 - p.1| + Real.sqrt |q.2 - p.2|) ≤ |c| * (2 * η) := by
    calc c * (Real.sqrt |q.1 - p.1| + Real.sqrt |q.2 - p.2|)
        ≤ |c| * (Real.sqrt |q.1 - p.1| + Real.sqrt |q.2 - p.2|) :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
      _ ≤ |c| * (2 * η) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
  refine hb.trans_lt (h3.trans_lt ?_)
  have : |c| * (2 * η) = ε * (|c| / (|c| + 1)) := by
    rw [hη]; field_simp
  rw [this]
  have hlt : |c| / (|c| + 1) < 1 := by
    rw [div_lt_one hc]; linarith
  nlinarith

end HRS.Uniform.Q54
