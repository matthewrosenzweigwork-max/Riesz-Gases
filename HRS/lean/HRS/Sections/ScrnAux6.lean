import HRS.Sections.ScrnAux5

/-!
# Packet SCRN, part 6: the covariance kernel `K(t,u;b,ρ)` of the limiting Gaussian evolution

Radial profile of `O:eq:meso-limit-cov`: with `a = b⁻¹ρ² + cρ^{2-q}`, `S = ρ^q/(ρ^q + bc)`,
`k_b(τ₁,τ₂,ρ) = S e^{-τ₁ a} + (1-S) e^{-τ₂ a}` (`τ₁ = t-u`, `τ₂ = t+u`), which equals
`e^{-(t-u)a}[S + (1-S)e^{-2ua}]`.  Bounds uniform in `τ₁, τ₂ ≥ 0` (all `ρ > 0`):
`0 ≤ k ≤ 1`, `|∂_ρ k| ≤ C/ρ`, `|∂_b k| ≤ 2/b`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace HRS

/-- `a_b(ρ) = b⁻¹ ρ² + c ρ^{2-q}`. -/
def scrnA (c q b ρ : ℝ) : ℝ := b⁻¹ * ρ ^ 2 + c * ρ ^ (2 - q)

/-- `S_b(ρ) = ρ^q / (ρ^q + b c)`. -/
def scrnS (c q b ρ : ℝ) : ℝ := ρ ^ q / (ρ ^ q + b * c)

/-- the radial kernel `S e^{-τ₁ a} + (1-S) e^{-τ₂ a}`. -/
def scrnk (c q b τ₁ τ₂ ρ : ℝ) : ℝ :=
  scrnS c q b ρ * Real.exp (-τ₁ * scrnA c q b ρ) +
    (1 - scrnS c q b ρ) * Real.exp (-τ₂ * scrnA c q b ρ)

section Props

variable {c q b ρ : ℝ}

lemma scrnA_pos (hc : 0 < c) (hb : 0 < b) (hρ : 0 < ρ) : 0 < scrnA c q b ρ := by
  unfold scrnA
  have := Real.rpow_pos_of_pos hρ (2 - q)
  positivity

lemma scrnS_pos (hc : 0 < c) (hb : 0 < b) (hρ : 0 < ρ) : 0 < scrnS c q b ρ := by
  unfold scrnS
  have := Real.rpow_pos_of_pos hρ q
  positivity

lemma scrnS_lt_one (hc : 0 < c) (hb : 0 < b) (hρ : 0 < ρ) : scrnS c q b ρ < 1 := by
  unfold scrnS
  have h1 := Real.rpow_pos_of_pos hρ q
  rw [div_lt_one (by positivity)]
  have : 0 < b * c := mul_pos hb hc
  linarith

lemma scrnk_nonneg (hc : 0 < c) (hb : 0 < b) (hρ : 0 < ρ) {τ₁ τ₂ : ℝ} :
    0 ≤ scrnk c q b τ₁ τ₂ ρ := by
  have h1 := scrnS_pos hc hb hρ (q := q)
  have h2 := scrnS_lt_one hc hb hρ (q := q)
  unfold scrnk
  have := Real.exp_pos (-τ₁ * scrnA c q b ρ)
  have := Real.exp_pos (-τ₂ * scrnA c q b ρ)
  have : 0 ≤ 1 - scrnS c q b ρ := by linarith
  positivity

lemma scrnk_le_one (hc : 0 < c) (hb : 0 < b) (hρ : 0 < ρ) {τ₁ τ₂ : ℝ} (h1 : 0 ≤ τ₁) (h2 : 0 ≤ τ₂) :
    scrnk c q b τ₁ τ₂ ρ ≤ 1 := by
  have hS := scrnS_pos hc hb hρ (q := q)
  have hS1 := scrnS_lt_one hc hb hρ (q := q)
  have hA := scrnA_pos hc hb hρ (q := q)
  unfold scrnk
  have e1 : Real.exp (-τ₁ * scrnA c q b ρ) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  have e2 : Real.exp (-τ₂ * scrnA c q b ρ) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  have : 0 ≤ 1 - scrnS c q b ρ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left e1 hS.le, mul_le_mul_of_nonneg_left e2 this]

/-- `x e^{-x} ≤ 1` for `x ≥ 0`. -/
lemma scrn_mul_exp_le {x : ℝ} (hx : 0 ≤ x) : x * Real.exp (-x) ≤ 1 := by
  have h := Real.add_one_le_exp x
  have hp := Real.exp_pos x
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hp]
  linarith

end Props


section Deriv

variable {c q b ρ : ℝ}

lemma hasDerivAt_scrnA (hρ : 0 < ρ) :
    HasDerivAt (scrnA c q b) (b⁻¹ * (2 * ρ) + c * ((2 - q) * ρ ^ (2 - q - 1))) ρ := by
  unfold scrnA
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * ρ) ρ := by
    simpa using hasDerivAt_pow 2 ρ
  have h2 : HasDerivAt (fun x : ℝ => x ^ (2 - q)) ((2 - q) * ρ ^ (2 - q - 1)) ρ :=
    Real.hasDerivAt_rpow_const (Or.inl hρ.ne')
  exact (h1.const_mul b⁻¹).add (h2.const_mul c)

lemma hasDerivAt_scrnS (hc : 0 < c) (hb : 0 < b) (hρ : 0 < ρ) :
    HasDerivAt (scrnS c q b)
      ((q * ρ ^ (q - 1) * (ρ ^ q + b * c) - ρ ^ q * (q * ρ ^ (q - 1))) / (ρ ^ q + b * c) ^ 2) ρ := by
  unfold scrnS
  have h1 : HasDerivAt (fun x : ℝ => x ^ q) (q * ρ ^ (q - 1)) ρ :=
    Real.hasDerivAt_rpow_const (Or.inl hρ.ne')
  have hD : ρ ^ q + b * c ≠ 0 := by
    have := Real.rpow_pos_of_pos hρ q
    have : 0 < b * c := mul_pos hb hc
    positivity
  exact h1.div (h1.add_const (b * c)) hD

/-- `ρ A'(ρ) = 2ρ²/b + (2-q) c ρ^{2-q}`. -/
lemma rho_mul_derivA (hρ : 0 < ρ) :
    ρ * (b⁻¹ * (2 * ρ) + c * ((2 - q) * ρ ^ (2 - q - 1))) =
      2 * (b⁻¹ * ρ ^ 2) + (2 - q) * (c * ρ ^ (2 - q)) := by
  have : ρ * ρ ^ (2 - q - 1) = ρ ^ (2 - q) := by
    rw [Real.rpow_sub_one hρ.ne']; field_simp
  calc ρ * (b⁻¹ * (2 * ρ) + c * ((2 - q) * ρ ^ (2 - q - 1)))
      = 2 * (b⁻¹ * ρ ^ 2) + c * (2 - q) * (ρ * ρ ^ (2 - q - 1)) := by ring
    _ = _ := by rw [this]; ring

lemma abs_rho_derivA_le (hc : 0 < c) (hb : 0 < b) (hρ : 0 < ρ) :
    |ρ * (b⁻¹ * (2 * ρ) + c * ((2 - q) * ρ ^ (2 - q - 1)))| ≤ (2 + |2 - q|) * scrnA c q b ρ := by
  rw [rho_mul_derivA hρ]
  have h1 : 0 ≤ b⁻¹ * ρ ^ 2 := by positivity
  have h2 : 0 ≤ c * ρ ^ (2 - q) := by have := Real.rpow_pos_of_pos hρ (2 - q); positivity
  unfold scrnA
  have e1 : |2 * (b⁻¹ * ρ ^ 2) + (2 - q) * (c * ρ ^ (2 - q))| ≤
      2 * (b⁻¹ * ρ ^ 2) + |2 - q| * (c * ρ ^ (2 - q)) := by
    have h3 : |2 * (b⁻¹ * ρ ^ 2)| = 2 * (b⁻¹ * ρ ^ 2) := abs_of_nonneg (by positivity)
    have h4 : |(2 - q) * (c * ρ ^ (2 - q))| = |2 - q| * (c * ρ ^ (2 - q)) := by
      rw [abs_mul, abs_of_nonneg h2]
    calc _ ≤ |2 * (b⁻¹ * ρ ^ 2)| + |(2 - q) * (c * ρ ^ (2 - q))| := abs_add_le _ _
      _ = 2 * (b⁻¹ * ρ ^ 2) + |2 - q| * (c * ρ ^ (2 - q)) := by rw [h3, h4]
  refine e1.trans ?_
  nlinarith [abs_nonneg (2 - q)]

/-- `ρ S'(ρ) = q S (1 - S)`. -/
lemma rho_mul_derivS (hc : 0 < c) (hb : 0 < b) (hρ : 0 < ρ) :
    ρ * ((q * ρ ^ (q - 1) * (ρ ^ q + b * c) - ρ ^ q * (q * ρ ^ (q - 1))) / (ρ ^ q + b * c) ^ 2) =
      q * (scrnS c q b ρ * (1 - scrnS c q b ρ)) := by
  have hp := Real.rpow_pos_of_pos hρ q
  have hbc : 0 < b * c := mul_pos hb hc
  have hD : ρ ^ q + b * c ≠ 0 := by positivity
  have : ρ * ρ ^ (q - 1) = ρ ^ q := by
    rw [Real.rpow_sub_one hρ.ne']; field_simp
  unfold scrnS
  field_simp
  calc ρ * q * ρ ^ (q - 1) = q * (ρ * ρ ^ (q - 1)) := by ring
    _ = q * ρ ^ q := by rw [this]


lemma scrnk_hasDerivAt (hc : 0 < c) (hb : 0 < b) (hρ : 0 < ρ) (τ₁ τ₂ : ℝ) :
    ∃ k' : ℝ, HasDerivAt (scrnk c q b τ₁ τ₂) k' ρ ∧
      ρ * k' = (q * (scrnS c q b ρ * (1 - scrnS c q b ρ))) *
          (Real.exp (-τ₁ * scrnA c q b ρ) - Real.exp (-τ₂ * scrnA c q b ρ)) +
        scrnS c q b ρ * (Real.exp (-τ₁ * scrnA c q b ρ) * (-τ₁ *
          (ρ * (b⁻¹ * (2 * ρ) + c * ((2 - q) * ρ ^ (2 - q - 1)))))) +
        (1 - scrnS c q b ρ) * (Real.exp (-τ₂ * scrnA c q b ρ) * (-τ₂ *
          (ρ * (b⁻¹ * (2 * ρ) + c * ((2 - q) * ρ ^ (2 - q - 1)))))) := by
  have hA := hasDerivAt_scrnA (c := c) (q := q) (b := b) hρ
  have hS := hasDerivAt_scrnS (q := q) hc hb hρ
  have e1 := ((hA.const_mul (-τ₁)).exp)
  have e2 := ((hA.const_mul (-τ₂)).exp)
  have hk : HasDerivAt (scrnk c q b τ₁ τ₂) _ ρ :=
    (hS.mul e1).add ((hS.const_sub 1).mul e2)
  refine ⟨_, hk, ?_⟩
  have h1 := rho_mul_derivS (q := q) hc hb hρ
  linear_combination (Real.exp (-τ₁ * scrnA c q b ρ) - Real.exp (-τ₂ * scrnA c q b ρ)) * h1


lemma scrnk_rho_deriv_bound (hc : 0 < c) (hb : 0 < b) (hρ : 0 < ρ) (hq : 0 ≤ q) {τ₁ τ₂ : ℝ}
    (h1 : 0 ≤ τ₁) (h2 : 0 ≤ τ₂) :
    ∃ k' : ℝ, HasDerivAt (scrnk c q b τ₁ τ₂) k' ρ ∧ |ρ * k'| ≤ q / 4 + (2 + |2 - q|) := by
  obtain ⟨k', hk, hid⟩ := scrnk_hasDerivAt (q := q) hc hb hρ τ₁ τ₂
  refine ⟨k', hk, ?_⟩
  rw [hid]
  set S := scrnS c q b ρ with hS
  set A := scrnA c q b ρ with hA
  set R := ρ * (b⁻¹ * (2 * ρ) + c * ((2 - q) * ρ ^ (2 - q - 1))) with hR
  have hS0 : 0 < S := scrnS_pos hc hb hρ
  have hS1 : S < 1 := scrnS_lt_one hc hb hρ
  have hA0 : 0 < A := scrnA_pos hc hb hρ
  have hRb : |R| ≤ (2 + |2 - q|) * A := abs_rho_derivA_le hc hb hρ
  set e1 := Real.exp (-τ₁ * A) with he1
  set e2 := Real.exp (-τ₂ * A) with he2
  have e1p : 0 < e1 := Real.exp_pos _
  have e2p : 0 < e2 := Real.exp_pos _
  have e1le : e1 ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have e2le : e2 ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have t1 : τ₁ * A * e1 ≤ 1 := by
    have := scrn_mul_exp_le (x := τ₁ * A) (by positivity)
    rw [he1, neg_mul]; exact this
  have t2 : τ₂ * A * e2 ≤ 1 := by
    have := scrn_mul_exp_le (x := τ₂ * A) (by positivity)
    rw [he2, neg_mul]; exact this
  set M : ℝ := 2 + |2 - q| with hM
  have hM0 : 0 ≤ M := by positivity
  have b1 : |q * (S * (1 - S)) * (e1 - e2)| ≤ q / 4 := by
    have hs4 : S * (1 - S) ≤ 1 / 4 := by nlinarith [sq_nonneg (S - 1 / 2)]
    have hs0 : 0 ≤ S * (1 - S) := mul_nonneg hS0.le (by linarith)
    have hd : |e1 - e2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    rw [abs_mul, abs_mul, abs_of_nonneg hq, abs_of_nonneg hs0]
    calc q * (S * (1 - S)) * |e1 - e2| ≤ q * (1 / 4) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hs4 hq) hd (abs_nonneg _) (by positivity)
      _ = q / 4 := by ring
  have b2 : |S * (e1 * (-τ₁ * R))| ≤ S * M := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hS0, abs_of_pos e1p, abs_neg, abs_of_nonneg h1]
    calc S * (e1 * (τ₁ * |R|)) ≤ S * (e1 * (τ₁ * (M * A))) := by gcongr
      _ = S * (M * (τ₁ * A * e1)) := by ring
      _ ≤ S * (M * 1) := by gcongr
      _ = S * M := by ring
  have b3 : |(1 - S) * (e2 * (-τ₂ * R))| ≤ (1 - S) * M := by
    have h1S : 0 < 1 - S := by linarith
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos h1S, abs_of_pos e2p, abs_neg, abs_of_nonneg h2]
    calc (1 - S) * (e2 * (τ₂ * |R|)) ≤ (1 - S) * (e2 * (τ₂ * (M * A))) := by gcongr
      _ = (1 - S) * (M * (τ₂ * A * e2)) := by ring
      _ ≤ (1 - S) * (M * 1) := by gcongr
      _ = (1 - S) * M := by ring
  calc |q * (S * (1 - S)) * (e1 - e2) + S * (e1 * (-τ₁ * R)) + (1 - S) * (e2 * (-τ₂ * R))|
      ≤ |q * (S * (1 - S)) * (e1 - e2)| + |S * (e1 * (-τ₁ * R))| + |(1 - S) * (e2 * (-τ₂ * R))| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ q / 4 + S * M + (1 - S) * M := by linarith
    _ = q / 4 + M := by ring

lemma scrnk_lip (hc : 0 < c) (hb : 0 < b) (hq : 0 ≤ q) {τ₁ τ₂ : ℝ} (h1 : 0 ≤ τ₁) (h2 : 0 ≤ τ₂)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ : ρ₁ ≤ ρ₂) :
    |scrnk c q b τ₁ τ₂ ρ₂ - scrnk c q b τ₁ τ₂ ρ₁| ≤
      (q / 4 + (2 + |2 - q|)) * |ρ₂ - ρ₁| / ρ₁ := by
  set B := q / 4 + (2 + |2 - q|) with hB
  have hder : ∀ x ∈ Set.Icc ρ₁ ρ₂, HasDerivAt (scrnk c q b τ₁ τ₂) (deriv (scrnk c q b τ₁ τ₂) x) x := by
    intro x hx
    obtain ⟨k', hk, -⟩ := scrnk_rho_deriv_bound (q := q) hc hb (lt_of_lt_of_le hρ₁ hx.1) hq h1 h2
    exact hk.differentiableAt.hasDerivAt
  have hbd : ∀ x ∈ Set.Icc ρ₁ ρ₂, ‖deriv (scrnk c q b τ₁ τ₂) x‖ ≤ B / ρ₁ := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hρ₁ hx.1
    obtain ⟨k', hk, hb'⟩ := scrnk_rho_deriv_bound (q := q) hc hb hx0 hq h1 h2
    rw [hk.deriv, Real.norm_eq_abs]
    have : |k'| ≤ B / x := by
      rw [le_div_iff₀ hx0]
      calc |k'| * x = |x * k'| := by rw [abs_mul, abs_of_pos hx0]; ring
        _ ≤ B := hb'
    refine this.trans ?_
    exact div_le_div_of_nonneg_left (by positivity) hρ₁ hx.1
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := scrnk c q b τ₁ τ₂) (f' := deriv (scrnk c q b τ₁ τ₂)) (s := Set.Icc ρ₁ ρ₂)
    (fun x hx => (hder x hx).hasDerivWithinAt) hbd (convex_Icc _ _)
    (Set.left_mem_Icc.2 hρ) (Set.right_mem_Icc.2 hρ)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  calc _ ≤ B / ρ₁ * |ρ₂ - ρ₁| := this
    _ = _ := by ring


/-- Derivative in `b`. -/
lemma scrnk_b_hasDerivAt (hc : 0 < c) (hb : 0 < b) (hρ : 0 < ρ) (τ₁ τ₂ : ℝ) :
    ∃ k' : ℝ, HasDerivAt (fun b' => scrnk c q b' τ₁ τ₂ ρ) k' b ∧
      k' = (-(ρ ^ q * c) / (ρ ^ q + b * c) ^ 2) *
          (Real.exp (-τ₁ * scrnA c q b ρ) - Real.exp (-τ₂ * scrnA c q b ρ)) +
        scrnS c q b ρ * (Real.exp (-τ₁ * scrnA c q b ρ) * (-τ₁ * (-(b ^ 2)⁻¹ * ρ ^ 2))) +
        (1 - scrnS c q b ρ) * (Real.exp (-τ₂ * scrnA c q b ρ) * (-τ₂ * (-(b ^ 2)⁻¹ * ρ ^ 2))) := by
  have hp := Real.rpow_pos_of_pos hρ q
  have hD : ρ ^ q + b * c ≠ 0 := by
    have : 0 < b * c := mul_pos hb hc
    positivity
  have hA : HasDerivAt (fun b' => scrnA c q b' ρ) (-(b ^ 2)⁻¹ * ρ ^ 2) b := by
    unfold scrnA
    have h1 : HasDerivAt (fun x : ℝ => x⁻¹) (-(b ^ 2)⁻¹) b := hasDerivAt_inv hb.ne'
    have := (h1.mul_const (ρ ^ 2)).add_const (c * ρ ^ (2 - q))
    exact this
  have hS : HasDerivAt (fun b' => scrnS c q b' ρ) (-(ρ ^ q * c) / (ρ ^ q + b * c) ^ 2) b := by
    unfold scrnS
    have h1 : HasDerivAt (fun x : ℝ => ρ ^ q + x * c) c b := by
      simpa using ((hasDerivAt_id b).mul_const c).const_add (ρ ^ q)
    have := (hasDerivAt_const b (ρ ^ q)).div h1 hD
    convert this using 1
    ring
  have e1 := ((hA.const_mul (-τ₁)).exp)
  have e2 := ((hA.const_mul (-τ₂)).exp)
  have hk : HasDerivAt (fun b' => scrnk c q b' τ₁ τ₂ ρ) _ b :=
    (hS.mul e1).add ((hS.const_sub 1).mul e2)
  refine ⟨_, hk, ?_⟩
  simp only [scrnA]
  ring

lemma scrnk_b_deriv_bound (hc : 0 < c) (hb : 0 < b) (hρ : 0 < ρ) {τ₁ τ₂ : ℝ}
    (h1 : 0 ≤ τ₁) (h2 : 0 ≤ τ₂) :
    ∃ k' : ℝ, HasDerivAt (fun b' => scrnk c q b' τ₁ τ₂ ρ) k' b ∧ |k'| ≤ 2 / b := by
  obtain ⟨k', hk, hid⟩ := scrnk_b_hasDerivAt (q := q) hc hb hρ τ₁ τ₂
  refine ⟨k', hk, ?_⟩
  rw [hid]
  have hp := Real.rpow_pos_of_pos hρ q
  have hbc : 0 < b * c := mul_pos hb hc
  set S := scrnS c q b ρ with hS
  set A := scrnA c q b ρ with hA
  have hS0 : 0 < S := scrnS_pos hc hb hρ
  have hS1 : S < 1 := scrnS_lt_one hc hb hρ
  have hA0 : 0 < A := scrnA_pos hc hb hρ
  have hAb : (b ^ 2)⁻¹ * ρ ^ 2 ≤ A / b := by
    have : b⁻¹ * ρ ^ 2 ≤ A := by
      simp only [hA, scrnA]
      have : 0 ≤ c * ρ ^ (2 - q) := by have := Real.rpow_pos_of_pos hρ (2 - q); positivity
      linarith
    rw [le_div_iff₀ hb]
    calc (b ^ 2)⁻¹ * ρ ^ 2 * b = b⁻¹ * ρ ^ 2 := by field_simp
      _ ≤ A := this
  set e1 := Real.exp (-τ₁ * A) with he1
  set e2 := Real.exp (-τ₂ * A) with he2
  have e1p : 0 < e1 := Real.exp_pos _
  have e2p : 0 < e2 := Real.exp_pos _
  have e1le : e1 ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have e2le : e2 ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have t1 : τ₁ * A * e1 ≤ 1 := by
    have := scrn_mul_exp_le (x := τ₁ * A) (by positivity)
    rw [he1, neg_mul]; exact this
  have t2 : τ₂ * A * e2 ≤ 1 := by
    have := scrn_mul_exp_le (x := τ₂ * A) (by positivity)
    rw [he2, neg_mul]; exact this
  have hSb : |-(ρ ^ q * c) / (ρ ^ q + b * c) ^ 2| ≤ 1 / b := by
    have hD : 0 < ρ ^ q + b * c := by positivity
    rw [abs_div, abs_neg, abs_of_pos (mul_pos hp hc), abs_of_pos (by positivity)]
    rw [div_le_div_iff₀ (by positivity) hb]
    nlinarith [mul_pos hp hc, mul_pos hb hc, mul_pos (mul_pos hp hc) hb, mul_pos (mul_pos hp hc) (mul_pos hb hc)]
  have b1 : |(-(ρ ^ q * c) / (ρ ^ q + b * c) ^ 2) * (e1 - e2)| ≤ 1 / b := by
    have hd : |e1 - e2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    rw [abs_mul]
    calc _ ≤ (1 / b) * 1 := mul_le_mul hSb hd (abs_nonneg _) (by positivity)
      _ = 1 / b := mul_one _
  set Ab : ℝ := -(b ^ 2)⁻¹ * ρ ^ 2 with hAb'
  have hAb2 : |Ab| ≤ A / b := by
    rw [hAb', neg_mul, abs_neg, abs_of_nonneg (by positivity)]; exact hAb
  have b2 : |S * (e1 * (-τ₁ * Ab))| ≤ S / b := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hS0, abs_of_pos e1p, abs_neg, abs_of_nonneg h1]
    calc S * (e1 * (τ₁ * |Ab|)) ≤ S * (e1 * (τ₁ * (A / b))) := by gcongr
      _ = S * (1 / b) * (τ₁ * A * e1) := by field_simp
      _ ≤ S * (1 / b) * 1 := by gcongr
      _ = S / b := by ring
  have b3 : |(1 - S) * (e2 * (-τ₂ * Ab))| ≤ (1 - S) / b := by
    have h1S : 0 < 1 - S := by linarith
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos h1S, abs_of_pos e2p, abs_neg, abs_of_nonneg h2]
    calc (1 - S) * (e2 * (τ₂ * |Ab|)) ≤ (1 - S) * (e2 * (τ₂ * (A / b))) := by gcongr
      _ = (1 - S) * (1 / b) * (τ₂ * A * e2) := by field_simp
      _ ≤ (1 - S) * (1 / b) * 1 := by gcongr
      _ = (1 - S) / b := by ring
  calc |(-(ρ ^ q * c) / (ρ ^ q + b * c) ^ 2) * (e1 - e2) + S * (e1 * (-τ₁ * Ab)) +
        (1 - S) * (e2 * (-τ₂ * Ab))|
      ≤ |(-(ρ ^ q * c) / (ρ ^ q + b * c) ^ 2) * (e1 - e2)| + |S * (e1 * (-τ₁ * Ab))| +
          |(1 - S) * (e2 * (-τ₂ * Ab))| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 1 / b + S / b + (1 - S) / b := by linarith
    _ = 2 / b := by field_simp; ring

lemma scrnk_b_lip (hc : 0 < c) (hρ : 0 < ρ) {τ₁ τ₂ : ℝ} (h1 : 0 ≤ τ₁) (h2 : 0 ≤ τ₂)
    {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) :
    |scrnk c q b₂ τ₁ τ₂ ρ - scrnk c q b₁ τ₁ τ₂ ρ| ≤ 2 / b₁ * |b₂ - b₁| := by
  have hder : ∀ x ∈ Set.Icc b₁ b₂,
      HasDerivAt (fun b' => scrnk c q b' τ₁ τ₂ ρ) (deriv (fun b' => scrnk c q b' τ₁ τ₂ ρ) x) x := by
    intro x hx
    obtain ⟨k', hk, -⟩ := scrnk_b_deriv_bound (q := q) hc (lt_of_lt_of_le hb₁ hx.1) hρ h1 h2
    exact hk.differentiableAt.hasDerivAt
  have hbd : ∀ x ∈ Set.Icc b₁ b₂, ‖deriv (fun b' => scrnk c q b' τ₁ τ₂ ρ) x‖ ≤ 2 / b₁ := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hb₁ hx.1
    obtain ⟨k', hk, hb'⟩ := scrnk_b_deriv_bound (q := q) hc hx0 hρ h1 h2
    rw [hk.deriv, Real.norm_eq_abs]
    exact hb'.trans (div_le_div_of_nonneg_left (by norm_num) hb₁ hx.1)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun b' => scrnk c q b' τ₁ τ₂ ρ) (f' := deriv (fun b' => scrnk c q b' τ₁ τ₂ ρ))
    (s := Set.Icc b₁ b₂) (fun x hx => (hder x hx).hasDerivWithinAt) hbd (convex_Icc _ _)
    (Set.left_mem_Icc.2 hb) (Set.right_mem_Icc.2 hb)
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at this

end Deriv

end HRS
