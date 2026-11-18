import HRS.MC.CepP2Aux2

/-!
# Packet CEPP2 (aux 3): the integer-order bootstrap `S(s) ⇒ S(s+1)`
-/

open MeasureTheory

noncomputable section
namespace HRS.MC.CepP2

variable {n : ℕ} {O : Set (XS n)}

/-- The parabolic weight `w(ζ) = 1 + |τ| + ‖ξ‖²`. -/
def wt (ζ : XS n) : ℝ := 1 + |ζ.1| + ‖ζ.2‖ ^ 2

lemma one_le_wt (ζ : XS n) : 1 ≤ wt ζ := by
  unfold wt; nlinarith [abs_nonneg ζ.1, sq_nonneg ‖ζ.2‖]

lemma wt_pos (ζ : XS n) : 0 < wt ζ := lt_of_lt_of_le one_pos (one_le_wt ζ)

lemma continuous_wt : Continuous (wt : XS n → ℝ) := by
  unfold wt; fun_prop

lemma norm_sq_le_wt (ζ : XS n) : ‖ζ.2‖ ^ 2 ≤ wt ζ := by unfold wt; have := abs_nonneg ζ.1; linarith

section key

variable {invβ : ℝ} {b : XS n → EuclideanSpace ℝ (Fin n)} {ρ : Measure (XS n)} {χ : XS n → ℝ}

/-- The pointwise symbol inequality. -/
lemma key_ineq (hO : IsOpen O) (hb : ContDiffOn ℝ smTop b O)
    (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) (hW : WeakEq O invβ b ρ) (hβ : 0 < invβ)
    (hχ : IsTest O χ) (ζ : XS n) :
    wt ζ ^ 2 * Nf ρ χ ζ ≤ 3 * Nf ρ χ ζ + 2 * (3 + 3 / invβ ^ 2) * Nf ρ (feq invβ b χ) ζ
      + 2 * (3 + 3 / invβ ^ 2) * wt ζ * ∑ k, Nf ρ (gone invβ b χ k) ζ := by
  have I1 := identity_cos hO hb hρ hW hχ ζ
  have I2 := identity_sin hO hb hρ hW hχ ζ
  set τ := ζ.1 with hτ
  set A := Cf ρ χ ζ
  set B := Sf ρ χ ζ
  set a := invβ * ‖ζ.2‖ ^ 2 with ha
  set X := ‖ζ.2‖ ^ 2 with hX
  have hXnorm : X = ∑ k, ζ.2 k ^ 2 := by simp [hX, EuclideanSpace.norm_sq_eq]
  set Cg := Cf ρ (feq invβ b χ) ζ
  set Sg := Sf ρ (feq invβ b χ) ζ
  set SS := ∑ k, ζ.2 k * Sf ρ (gone invβ b χ k) ζ with hSS
  set CC := ∑ k, ζ.2 k * Cf ρ (gone invβ b χ k) ζ with hCC
  have hP : a * A + τ * B = Cg - SS := by linarith
  have hQ : τ * A - a * B = -Sg - CC := by linarith
  have hL : (a * A + τ * B) ^ 2 + (τ * A - a * B) ^ 2 = (a ^ 2 + τ ^ 2) * (A ^ 2 + B ^ 2) := by ring
  have cs1 : SS ^ 2 ≤ X * ∑ k, Sf ρ (gone invβ b χ k) ζ ^ 2 := by
    rw [hXnorm]; exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have cs2 : CC ^ 2 ≤ X * ∑ k, Cf ρ (gone invβ b χ k) ζ ^ 2 := by
    rw [hXnorm]; exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hNk : ∑ k, Nf ρ (gone invβ b χ k) ζ =
      ∑ k, Cf ρ (gone invβ b χ k) ζ ^ 2 + ∑ k, Sf ρ (gone invβ b χ k) ζ ^ 2 := by
    simp only [Nf, Finset.sum_add_distrib]
  have hNkn : 0 ≤ ∑ k, Nf ρ (gone invβ b χ k) ζ :=
    Finset.sum_nonneg fun k _ => Nf_nonneg _ _ _
  have hX0 : 0 ≤ X := by positivity
  have h1 : (a ^ 2 + τ ^ 2) * (A ^ 2 + B ^ 2) ≤
      2 * Nf ρ (feq invβ b χ) ζ + 2 * X * ∑ k, Nf ρ (gone invβ b χ k) ζ := by
    rw [← hL, hP, hQ, hNk]
    have e1 : (Cg - SS) ^ 2 ≤ 2 * Cg ^ 2 + 2 * SS ^ 2 := by nlinarith [sq_nonneg (Cg + SS)]
    have e2 : (-Sg - CC) ^ 2 ≤ 2 * Sg ^ 2 + 2 * CC ^ 2 := by nlinarith [sq_nonneg (Sg - CC)]
    have e3 : Nf ρ (feq invβ b χ) ζ = Cg ^ 2 + Sg ^ 2 := rfl
    rw [e3]
    have e4 : 2 * X * (∑ k, Cf ρ (gone invβ b χ k) ζ ^ 2 + ∑ k, Sf ρ (gone invβ b χ k) ζ ^ 2)
        = 2 * (X * ∑ k, Cf ρ (gone invβ b χ k) ζ ^ 2) + 2 * (X * ∑ k, Sf ρ (gone invβ b χ k) ζ ^ 2) := by
      ring
    rw [e4]
    linarith
  have hc0 : 0 ≤ 3 / invβ ^ 2 := by positivity
  have hw2 : wt ζ ^ 2 ≤ 3 + (3 + 3 / invβ ^ 2) * (a ^ 2 + τ ^ 2) := by
    have h3 : wt ζ ^ 2 ≤ 3 * (1 + τ ^ 2 + X ^ 2) := by
      unfold wt
      have : |τ| ^ 2 = τ ^ 2 := sq_abs τ
      nlinarith [sq_nonneg (1 - |τ|), sq_nonneg (1 - X), sq_nonneg (|τ| - X), abs_nonneg τ]
    have h4 : 3 * X ^ 2 = (3 / invβ ^ 2) * a ^ 2 := by
      rw [ha]; field_simp
    have h5 : 0 ≤ a ^ 2 := sq_nonneg _
    have h6 : 0 ≤ τ ^ 2 := sq_nonneg _
    nlinarith
  have hN : 0 ≤ A ^ 2 + B ^ 2 := by positivity
  have hNchi : Nf ρ χ ζ = A ^ 2 + B ^ 2 := rfl
  rw [hNchi]
  have hXw : X ≤ wt ζ := norm_sq_le_wt ζ
  calc wt ζ ^ 2 * (A ^ 2 + B ^ 2)
      ≤ (3 + (3 + 3 / invβ ^ 2) * (a ^ 2 + τ ^ 2)) * (A ^ 2 + B ^ 2) :=
        mul_le_mul_of_nonneg_right hw2 hN
    _ = 3 * (A ^ 2 + B ^ 2) + (3 + 3 / invβ ^ 2) * ((a ^ 2 + τ ^ 2) * (A ^ 2 + B ^ 2)) := by ring
    _ ≤ 3 * (A ^ 2 + B ^ 2) + (3 + 3 / invβ ^ 2) *
          (2 * Nf ρ (feq invβ b χ) ζ + 2 * X * ∑ k, Nf ρ (gone invβ b χ k) ζ) := by
        gcongr
    _ ≤ 3 * (A ^ 2 + B ^ 2) + (3 + 3 / invβ ^ 2) *
          (2 * Nf ρ (feq invβ b χ) ζ + 2 * wt ζ * ∑ k, Nf ρ (gone invβ b χ k) ζ) := by
        gcongr
    _ = _ := by ring

end key


lemma integrable_inv_pow_real (m : ℕ) (hm : 2 ≤ m) :
    Integrable (fun τ : ℝ => ((1 + |τ|) ^ m)⁻¹) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := (volume : Measure ℝ)) (r := (m : ℝ))
    (by simpa using (by exact_mod_cast hm : (1 : ℝ) < m) )
  refine h.congr (Filter.Eventually.of_forall fun τ => ?_)
  simp [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |τ|)]

lemma integrable_inv_pow_euc (m : ℕ) (hm : n < 2 * m) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => ((1 + ‖ξ‖ ^ 2) ^ m)⁻¹) := by
  have h := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin n)) (μ := (volume : Measure _))
    (r := ((2 * m : ℕ) : ℝ)) (by simpa using (by exact_mod_cast hm : (n : ℝ) < (2 * m : ℕ)))
  refine ((h.const_mul (2 ^ m : ℝ)).mono' ?_ ?_)
  · exact (Continuous.inv₀ (by fun_prop) (fun ξ => by positivity) : Continuous fun ξ : EuclideanSpace ℝ (Fin n) => ((1 + ‖ξ‖ ^ 2) ^ m)⁻¹).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ξ => ?_
    have hx : 0 ≤ ‖ξ‖ := norm_nonneg ξ
    have e : (1 + ‖ξ‖) ^ (-((2 * m : ℕ) : ℝ)) = ((1 + ‖ξ‖) ^ (2 * m))⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), e]
    have h2 : (1 + ‖ξ‖) ^ 2 ≤ 2 * (1 + ‖ξ‖ ^ 2) := by nlinarith [sq_nonneg (1 - ‖ξ‖)]
    have h3 : (1 + ‖ξ‖) ^ (2 * m) / 2 ^ m ≤ (1 + ‖ξ‖ ^ 2) ^ m := by
      rw [div_le_iff₀ (by positivity), pow_mul, ← mul_pow, mul_comm]
      exact pow_le_pow_left₀ (by positivity) h2 m
    calc ((1 + ‖ξ‖ ^ 2) ^ m)⁻¹ ≤ ((1 + ‖ξ‖) ^ (2 * m) / 2 ^ m)⁻¹ := inv_anti₀ (by positivity) h3
      _ = _ := by rw [inv_div, div_eq_mul_inv]


lemma integrable_wt_inv (n : ℕ) :
    Integrable (fun ζ : XS n => (wt ζ ^ (2 * (n + 2)))⁻¹) := by
  have h1 := integrable_inv_pow_real (n + 2) (by omega)
  have h2 := integrable_inv_pow_euc (n := n) (n + 2) (by omega)
  have h3 : Integrable (fun ζ : XS n => ((1 + |ζ.1|) ^ (n + 2))⁻¹ * ((1 + ‖ζ.2‖ ^ 2) ^ (n + 2))⁻¹)
      (volume : Measure (XS n)) := h1.mul_prod h2
  refine h3.mono' ?_ ?_
  · exact (Continuous.inv₀ (by unfold wt; fun_prop) (fun ζ => by have := wt_pos ζ; positivity) :
      Continuous fun ζ : XS n => (wt ζ ^ (2 * (n + 2)))⁻¹).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ζ => ?_
    have hw := wt_pos ζ
    have hτ : 0 ≤ |ζ.1| := abs_nonneg _
    have hX : 0 ≤ ‖ζ.2‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_inv, pow_mul]
    refine inv_anti₀ (by positivity) ?_
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    unfold wt
    nlinarith [mul_nonneg hτ hX]


variable {O : Set (XS n)}

/-- `S(s)`: for every test function `g`, `w^s N_g` is integrable. -/
def SobFin (O : Set (XS n)) (ρ : Measure (XS n)) (s : ℤ) : Prop :=
  ∀ g : XS n → ℝ, IsTest O g → Integrable (fun ζ : XS n => wt ζ ^ s * Nf ρ g ζ)

lemma continuous_Nf {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) {g : XS n → ℝ}
    (hg : IsTest O g) : Continuous (Nf ρ g) := by
  unfold Nf
  exact ((continuous_Cf hρ hg).pow 2).add ((continuous_Sf hρ hg).pow 2)

lemma continuous_wt_zpow_mul {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤)
    {g : XS n → ℝ} (hg : IsTest O g) (s : ℤ) : Continuous fun ζ : XS n => wt ζ ^ s * Nf ρ g ζ :=
  ((continuous_wt.zpow₀ s fun ζ => Or.inl (wt_pos ζ).ne').mul (continuous_Nf hρ hg))

lemma sobFin_base {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) :
    SobFin O ρ (-(2 * ((n : ℤ) + 2))) := by
  intro g hg
  have hI := (integrable_wt_inv n).const_mul (2 * Mf ρ g ^ 2)
  refine hI.mono' (continuous_wt_zpow_mul hρ hg _).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ζ => ?_
  have hw : wt ζ ^ (-(2 * ((n : ℤ) + 2))) = (wt ζ ^ (2 * (n + 2)))⁻¹ := by
    rw [zpow_neg, ← zpow_natCast]; push_cast; rfl
  rw [hw, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.2 (by have := wt_pos ζ; positivity))
    (Nf_nonneg _ _ _))]
  have := Nf_le hρ hg ζ
  have hp : 0 ≤ (wt ζ ^ (2 * (n + 2)))⁻¹ := inv_nonneg.2 (by have := wt_pos ζ; positivity)
  calc (wt ζ ^ (2 * (n + 2)))⁻¹ * Nf ρ g ζ ≤ (wt ζ ^ (2 * (n + 2)))⁻¹ * (2 * Mf ρ g ^ 2) :=
        mul_le_mul_of_nonneg_left this hp
    _ = _ := by ring

lemma sobFin_mono {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) {s s' : ℤ}
    (hS : SobFin O ρ s) (h : s' ≤ s) : SobFin O ρ s' := by
  intro g hg
  refine (hS g hg).mono' (continuous_wt_zpow_mul hρ hg _).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ζ => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (zpow_nonneg (wt_pos ζ).le _) (Nf_nonneg _ _ _))]
  exact mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ (one_le_wt ζ) h) (Nf_nonneg _ _ _)


section step

variable {invβ : ℝ} {b : XS n → EuclideanSpace ℝ (Fin n)} {ρ : Measure (XS n)}

lemma sobFin_step (hO : IsOpen O) (hb : ContDiffOn ℝ smTop b O)
    (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) (hW : WeakEq O invβ b ρ) (hβ : 0 < invβ) (s : ℤ)
    (hS : SobFin O ρ (s - 1)) : SobFin O ρ s := by
  intro χ hχ
  set c0 : ℝ := 2 * (3 + 3 / invβ ^ 2) with hc0
  have hc0n : 0 ≤ c0 := by positivity
  have i1 := hS χ hχ
  have i2 := hS _ (isTest_feq hO hb invβ hχ)
  have i3 : Integrable (fun ζ : XS n => ∑ k, wt ζ ^ (s - 1) * Nf ρ (gone invβ b χ k) ζ) :=
    integrable_finsetSum _ fun k _ => hS _ (isTest_gone hO hb invβ hχ k)
  have hB := ((i1.const_mul 3).add (i2.const_mul c0)).add (i3.const_mul c0)
  refine hB.mono' (continuous_wt_zpow_mul hρ hχ s).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ζ => ?_
  have hW0 : wt ζ ≠ 0 := (wt_pos ζ).ne'
  have hk := key_ineq hO hb hρ hW hβ hχ ζ
  set W := wt ζ with hWdef
  have hWs : W ^ s = W ^ (s - 2) * W ^ 2 := by
    rw [← zpow_natCast, ← zpow_add₀ hW0]; congr 1; push_cast; ring
  have hWs1 : W ^ (s - 2) * W = W ^ (s - 1) := by
    rw [← zpow_add_one₀ hW0]; congr 1; ring
  have hle : W ^ (s - 2) ≤ W ^ (s - 1) := zpow_le_zpow_right₀ (one_le_wt ζ) (by omega)
  have hp : 0 ≤ W ^ (s - 2) := zpow_nonneg (wt_pos ζ).le _
  have hN := Nf_nonneg ρ χ ζ
  have hN0 := Nf_nonneg ρ (feq invβ b χ) ζ
  have hNk : 0 ≤ ∑ k, Nf ρ (gone invβ b χ k) ζ := Finset.sum_nonneg fun k _ => Nf_nonneg _ _ _
  have hsum : ∑ k, W ^ (s - 1) * Nf ρ (gone invβ b χ k) ζ = W ^ (s - 1) * ∑ k, Nf ρ (gone invβ b χ k) ζ := by
    rw [Finset.mul_sum]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (zpow_nonneg (wt_pos ζ).le _) hN)]
  show W ^ s * Nf ρ χ ζ ≤ 3 * (W ^ (s - 1) * Nf ρ χ ζ) + c0 * (W ^ (s - 1) * Nf ρ (feq invβ b χ) ζ)
    + c0 * ∑ k, W ^ (s - 1) * Nf ρ (gone invβ b χ k) ζ
  rw [hsum]
  have hk' : W ^ 2 * Nf ρ χ ζ ≤ 3 * Nf ρ χ ζ + c0 * Nf ρ (feq invβ b χ) ζ
      + c0 * W * ∑ k, Nf ρ (gone invβ b χ k) ζ := by
    simpa [hc0] using hk
  calc W ^ s * Nf ρ χ ζ = W ^ (s - 2) * (W ^ 2 * Nf ρ χ ζ) := by rw [hWs]; ring
    _ ≤ W ^ (s - 2) * (3 * Nf ρ χ ζ + c0 * Nf ρ (feq invβ b χ) ζ
          + c0 * W * ∑ k, Nf ρ (gone invβ b χ k) ζ) := mul_le_mul_of_nonneg_left hk' hp
    _ = 3 * (W ^ (s - 2) * Nf ρ χ ζ) + c0 * (W ^ (s - 2) * Nf ρ (feq invβ b χ) ζ)
          + c0 * (W ^ (s - 2) * W * ∑ k, Nf ρ (gone invβ b χ k) ζ) := by ring
    _ ≤ 3 * (W ^ (s - 1) * Nf ρ χ ζ) + c0 * (W ^ (s - 1) * Nf ρ (feq invβ b χ) ζ)
          + c0 * (W ^ (s - 1) * ∑ k, Nf ρ (gone invβ b χ k) ζ) := by
        rw [hWs1]
        gcongr

/-- `S(s)` holds for all integers `s`. -/
theorem sobFin_all (hO : IsOpen O) (hb : ContDiffOn ℝ smTop b O)
    (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) (hW : WeakEq O invβ b ρ) (hβ : 0 < invβ) (s : ℤ) :
    SobFin O ρ s := by
  have hup : ∀ k : ℕ, SobFin O ρ (-(2 * ((n : ℤ) + 2)) + k) := by
    intro k
    induction k with
    | zero => simpa using sobFin_base hρ
    | succ k ih =>
      have := sobFin_step hO hb hρ hW hβ (-(2 * ((n : ℤ) + 2)) + (k + 1 : ℕ)) (by
        have e : -(2 * ((n : ℤ) + 2)) + ((k + 1 : ℕ) : ℤ) - 1 = -(2 * ((n : ℤ) + 2)) + k := by push_cast; ring
        rw [e]; exact ih)
      exact this
  by_cases h : s ≤ -(2 * ((n : ℤ) + 2))
  · exact sobFin_mono hρ (sobFin_base hρ) h
  · rw [not_le] at h
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s = -(2 * ((n : ℤ) + 2)) + k := ⟨(s + 2 * ((n : ℤ) + 2)).toNat, by omega⟩
    rw [hk]; exact hup k

end step


end HRS.MC.CepP2
