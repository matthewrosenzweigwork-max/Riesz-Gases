import Mathlib

/-!
# Q48b, interpolation of weighted operator bounds (finite matrices)

Hadamard's three-lines theorem for the weighted matrix norms `‖D_T^{-α} A D_S^{α}‖`: if a real matrix `A`
(rows `T`, columns `S`, finite) satisfies the weighted `ℓ²` bounds `M₁` at level `α₁` and `M₂` at level `α₂`,
then it satisfies `M₁^{1-θ} M₂^θ` at level `(1-θ) α₁ + θ α₂`.
-/

noncomputable section

namespace HRS.Uniform.Q48b

open Complex Finset

variable {ι : Type*}

/-- The weighted bound `Σ_{l∈T} w_l^{-2α} (A z)_l² ≤ M² Σ_{k∈S} w_k^{-2α} z_k²` for all real `z`. -/
def WBound (w : ι → ℝ) (a : ι → ι → ℝ) (S T : Finset ι) (α M : ℝ) : Prop :=
  ∀ z : ι → ℝ, ∑ l ∈ T, w l ^ (-2 * α) * (∑ k ∈ S, a l k * z k) ^ 2 ≤
    M ^ 2 * ∑ k ∈ S, w k ^ (-2 * α) * z k ^ 2

theorem q48b_wbound_complex {w : ι → ℝ} (hw : ∀ i, 0 < w i) {a : ι → ι → ℝ} {S T : Finset ι}
    {α M : ℝ} (h : WBound w a S T α M) (z : ι → ℂ) :
    ∑ l ∈ T, w l ^ (-2 * α) * ‖∑ k ∈ S, (a l k : ℂ) * z k‖ ^ 2 ≤
      M ^ 2 * ∑ k ∈ S, w k ^ (-2 * α) * ‖z k‖ ^ 2 := by
  have h1 := h (fun k => (z k).re)
  have h2 := h (fun k => (z k).im)
  have e1 : ∀ l, ‖∑ k ∈ S, (a l k : ℂ) * z k‖ ^ 2 =
      (∑ k ∈ S, a l k * (z k).re) ^ 2 + (∑ k ∈ S, a l k * (z k).im) ^ 2 := by
    intro l
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.re_sum, Complex.im_sum, sq]
  have e2 : ∀ k, ‖z k‖ ^ 2 = (z k).re ^ 2 + (z k).im ^ 2 := fun k => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp_rw [e1, e2, mul_add, Finset.sum_add_distrib]
  nlinarith [h1, h2]

/-- The bound on a line of the strip. -/
theorem q48b_wbound_line {w : ι → ℝ} (hw : ∀ i, 0 < w i) {a : ι → ι → ℝ} {S T : Finset ι}
    {α M : ℝ} (hM : 0 ≤ M) (h : WBound w a S T α M) (y u : ι → ℂ) (γ : ℂ) (hγ : γ.re = α) :
    ‖∑ l ∈ T, ∑ k ∈ S, y l * (a l k : ℂ) * u k *
        cexp (γ * (((Real.log (w k) - Real.log (w l) : ℝ)) : ℂ))‖ ≤
      M * Real.sqrt (∑ l ∈ T, ‖y l‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖u k‖ ^ 2) := by
  -- norms of the exponential factors
  have hn : ∀ i, ‖cexp (γ * ((Real.log (w i) : ℝ) : ℂ))‖ = w i ^ α := by
    intro i
    rw [Complex.norm_exp, Complex.re_mul_ofReal, hγ, Real.rpow_def_of_pos (hw i), mul_comm]
  set z : ι → ℂ := fun k => u k * cexp (γ * ((Real.log (w k) : ℝ) : ℂ)) with hz
  set Y : ι → ℂ := fun l => y l * (cexp (γ * ((Real.log (w l) : ℝ) : ℂ)))⁻¹ with hY
  have hsplit : ∀ l k, y l * (a l k : ℂ) * u k *
        cexp (γ * (((Real.log (w k) - Real.log (w l) : ℝ)) : ℂ)) = Y l * ((a l k : ℂ) * z k) := by
    intro l k
    have : cexp (γ * (((Real.log (w k) - Real.log (w l) : ℝ)) : ℂ)) =
        cexp (γ * ((Real.log (w k) : ℝ) : ℂ)) * (cexp (γ * ((Real.log (w l) : ℝ) : ℂ)))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      push_cast; ring
    rw [this, hY, hz]
    ring
  simp_rw [hsplit, ← Finset.mul_sum]
  set X : ι → ℂ := fun l => ∑ k ∈ S, (a l k : ℂ) * z k with hX
  have hYn : ∀ l, ‖Y l‖ = ‖y l‖ * w l ^ (-α) := by
    intro l
    rw [hY]; simp only [norm_mul, norm_inv, hn, Real.rpow_neg (hw l).le]
  have hzn : ∀ k, ‖z k‖ = ‖u k‖ * w k ^ α := by
    intro k; rw [hz]; simp only [norm_mul, hn]
  have hCS : (∑ l ∈ T, ‖y l‖ * (w l ^ (-α) * ‖X l‖)) ^ 2 ≤
      (∑ l ∈ T, ‖y l‖ ^ 2) * ∑ l ∈ T, (w l ^ (-α) * ‖X l‖) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq T (fun l => ‖y l‖) (fun l => w l ^ (-α) * ‖X l‖)
  have hrhs : ∑ l ∈ T, (w l ^ (-α) * ‖X l‖) ^ 2 ≤ M ^ 2 * ∑ k ∈ S, ‖u k‖ ^ 2 := by
    have hb := q48b_wbound_complex hw h z
    have e : ∀ l, (w l ^ (-α) * ‖X l‖) ^ 2 = w l ^ (-2 * α) * ‖X l‖ ^ 2 := by
      intro l
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (hw l).le]
      norm_num
      left; ring_nf
    have e' : ∀ k, w k ^ (-2 * α) * ‖z k‖ ^ 2 = ‖u k‖ ^ 2 := by
      intro k
      have h2 : (w k ^ α) ^ 2 = w k ^ (2 * α) := by rw [two_mul, Real.rpow_add (hw k), sq]
      have h3 : w k ^ (-2 * α) * w k ^ (2 * α) = 1 := by
        rw [← Real.rpow_add (hw k), show -2 * α + 2 * α = 0 by ring, Real.rpow_zero]
      rw [hzn, mul_pow, h2, mul_comm (‖u k‖ ^ 2), ← mul_assoc, h3, one_mul]
    simp_rw [e]
    refine hb.trans ?_
    simp_rw [e']
    exact le_rfl
  have hlow : ‖∑ l ∈ T, Y l * X l‖ ≤ ∑ l ∈ T, ‖y l‖ * (w l ^ (-α) * ‖X l‖) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_))
    rw [norm_mul, hYn]; ring
  have hP : 0 ≤ ∑ l ∈ T, ‖y l‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ : 0 ≤ ∑ k ∈ S, ‖u k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : (∑ l ∈ T, ‖y l‖ * (w l ^ (-α) * ‖X l‖)) ^ 2 ≤
      (M * Real.sqrt (∑ l ∈ T, ‖y l‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖u k‖ ^ 2)) ^ 2 := by
    refine hCS.trans ?_
    have : (M * Real.sqrt (∑ l ∈ T, ‖y l‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖u k‖ ^ 2)) ^ 2 =
        (∑ l ∈ T, ‖y l‖ ^ 2) * (M ^ 2 * ∑ k ∈ S, ‖u k‖ ^ 2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hP, Real.sq_sqrt hQ]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hrhs hP
  have hnn : 0 ≤ M * Real.sqrt (∑ l ∈ T, ‖y l‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖u k‖ ^ 2) := by positivity
  have hcm : ∑ l ∈ T, ‖y l‖ * (w l ^ (-α) * ‖X l‖) ≤
      M * Real.sqrt (∑ l ∈ T, ‖y l‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖u k‖ ^ 2) := by
    have h0 : 0 ≤ ∑ l ∈ T, ‖y l‖ * (w l ^ (-α) * ‖X l‖) :=
      Finset.sum_nonneg fun l _ => mul_nonneg (norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (hw l).le _) (norm_nonneg _))
    exact le_of_sq_le_sq hsq hnn |>.trans le_rfl
  exact hlow.trans hcm


/-- Three-lines estimate for the entire function `ζ ↦ ∑∑ y_l a_lk u_k w_k^{γ(ζ)} w_l^{-γ(ζ)}`. -/
theorem q48b_wbound_three_lines {w : ι → ℝ} (hw : ∀ i, 0 < w i) {a : ι → ι → ℝ} {S T : Finset ι}
    {α₁ α₂ M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (h₁ : WBound w a S T α₁ M₁)
    (h₂ : WBound w a S T α₂ M₂) (y u : ι → ℂ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖∑ l ∈ T, ∑ k ∈ S, y l * (a l k : ℂ) * u k *
        cexp (((α₁ + θ * (α₂ - α₁) : ℝ) : ℂ) * (((Real.log (w k) - Real.log (w l) : ℝ)) : ℂ))‖ ≤
      (M₁ * Real.sqrt (∑ l ∈ T, ‖y l‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖u k‖ ^ 2)) ^ (1 - θ) *
      (M₂ * Real.sqrt (∑ l ∈ T, ‖y l‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖u k‖ ^ 2)) ^ θ := by
  set f : ℂ → ℂ := fun ζ => ∑ l ∈ T, ∑ k ∈ S, y l * (a l k : ℂ) * u k *
        cexp (((α₁ : ℂ) + ζ * ((α₂ - α₁ : ℝ) : ℂ)) * (((Real.log (w k) - Real.log (w l) : ℝ)) : ℂ))
    with hf
  have hdiff : Differentiable ℂ f := by
    rw [hf]
    fun_prop
  -- boundedness on the closed strip
  have hB : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨∑ l ∈ T, ∑ k ∈ S, ‖y l‖ * |a l k| * ‖u k‖ *
      Real.exp ((|α₁| + |α₂ - α₁|) * |Real.log (w k) - Real.log (w l)|), ?_⟩
    rintro _ ⟨ζ, hζ, rfl⟩
    simp only [Function.comp]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (((α₁ : ℂ) + ζ * ((α₂ - α₁ : ℝ) : ℂ)) *
        (((Real.log (w k) - Real.log (w l) : ℝ)) : ℂ)).re =
        (α₁ + ζ.re * (α₂ - α₁)) * (Real.log (w k) - Real.log (w l)) := by
      rw [Complex.re_mul_ofReal]
      simp
    rw [hre]
    have hζ0 : 0 ≤ ζ.re := hζ.1
    have hζ1 : ζ.re ≤ 1 := hζ.2
    have hle : (α₁ + ζ.re * (α₂ - α₁)) * (Real.log (w k) - Real.log (w l)) ≤
        (|α₁| + |α₂ - α₁|) * |Real.log (w k) - Real.log (w l)| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      calc |α₁ + ζ.re * (α₂ - α₁)| ≤ |α₁| + |ζ.re * (α₂ - α₁)| := abs_add_le _ _
        _ ≤ |α₁| + |α₂ - α₁| := by
          have h3 : |ζ.re * (α₂ - α₁)| ≤ |α₂ - α₁| := by
            rw [abs_mul, abs_of_nonneg hζ0]
            exact mul_le_of_le_one_left (abs_nonneg _) hζ1
          linarith
    have := Real.exp_le_exp.mpr hle
    gcongr
  have hline : ∀ (ζ : ℂ) (α M : ℝ), 0 ≤ M → WBound w a S T α M →
      (α₁ + ζ.re * (α₂ - α₁) = α) →
      ‖f ζ‖ ≤ M * Real.sqrt (∑ l ∈ T, ‖y l‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖u k‖ ^ 2) := by
    intro ζ α M hM hW hα
    refine q48b_wbound_line hw hM hW y u _ ?_
    rw [Complex.add_re, Complex.re_mul_ofReal, Complex.ofReal_re]
    simp [hα.symm]
  have key := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' f
    (z := (θ : ℂ)) (a := M₁ * Real.sqrt (∑ l ∈ T, ‖y l‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖u k‖ ^ 2))
    (b := M₂ * Real.sqrt (∑ l ∈ T, ‖y l‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖u k‖ ^ 2))
    ⟨by simpa using hθ0, by simpa using hθ1⟩ hdiff.diffContOnCl hB
    (fun ζ hζ => hline ζ α₁ M₁ hM₁ h₁ (by simpa using congrArg (fun x => α₁ + x * (α₂ - α₁)) (show ζ.re = 0 from hζ)))
    (fun ζ hζ => hline ζ α₂ M₂ hM₂ h₂ (by
      have : ζ.re = 1 := hζ
      rw [this]; ring))
  simpa [hf] using key


/-- Interpolation of weighted bounds. -/
theorem q48b_wbound_interp {w : ι → ℝ} (hw : ∀ i, 0 < w i) {a : ι → ι → ℝ} {S T : Finset ι}
    {α₁ α₂ M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (h₁ : WBound w a S T α₁ M₁)
    (h₂ : WBound w a S T α₂ M₂) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    WBound w a S T (α₁ + θ * (α₂ - α₁)) (M₁ ^ (1 - θ) * M₂ ^ θ) := by
  intro z
  set β : ℝ := α₁ + θ * (α₂ - α₁) with hβ
  set A : ι → ℝ := fun l => ∑ k ∈ S, a l k * z k with hA
  set y : ι → ℂ := fun l => ((w l ^ (-β) * A l : ℝ) : ℂ) with hy
  set u : ι → ℂ := fun k => ((w k ^ (-β) * z k : ℝ) : ℂ) with hu
  have key := q48b_wbound_three_lines hw hM₁ hM₂ h₁ h₂ y u θ hθ0 hθ1
  set P : ℝ := ∑ l ∈ T, w l ^ (-2 * β) * A l ^ 2 with hP
  set Q : ℝ := ∑ k ∈ S, w k ^ (-2 * β) * z k ^ 2 with hQ
  have hyn : ∀ l, ‖y l‖ ^ 2 = w l ^ (-2 * β) * A l ^ 2 := by
    intro l
    rw [hy]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hw l).le]
    norm_num
    left; ring_nf
  have hun : ∀ k, ‖u k‖ ^ 2 = w k ^ (-2 * β) * z k ^ 2 := by
    intro k
    rw [hu]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hw k).le]
    norm_num
    left; ring_nf
  have hPn : 0 ≤ P := Finset.sum_nonneg fun l _ => mul_nonneg (Real.rpow_nonneg (hw l).le _) (sq_nonneg _)
  have hQn : 0 ≤ Q := Finset.sum_nonneg fun k _ => mul_nonneg (Real.rpow_nonneg (hw k).le _) (sq_nonneg _)
  simp_rw [hyn, hun] at key
  -- the value of the function at `θ`
  have hval : (∑ l ∈ T, ∑ k ∈ S, y l * (a l k : ℂ) * u k *
        cexp (((α₁ + θ * (α₂ - α₁) : ℝ) : ℂ) * (((Real.log (w k) - Real.log (w l) : ℝ)) : ℂ))) =
        ((P : ℝ) : ℂ) := by
    have : ∀ l k, y l * (a l k : ℂ) * u k *
        cexp (((α₁ + θ * (α₂ - α₁) : ℝ) : ℂ) * (((Real.log (w k) - Real.log (w l) : ℝ)) : ℂ)) =
        (((w l ^ (-β) * A l) * (w l ^ (-β) * (a l k * z k)) : ℝ) : ℂ) := by
      intro l k
      have hexp : cexp (((α₁ + θ * (α₂ - α₁) : ℝ) : ℂ) * (((Real.log (w k) - Real.log (w l) : ℝ)) : ℂ)) =
          ((w k ^ β * w l ^ (-β) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
        congr 1
        rw [Real.rpow_def_of_pos (hw k), Real.rpow_def_of_pos (hw l), ← Real.exp_add]
        congr 1
        rw [← hβ]; ring
      rw [hexp, hy, hu]
      have hk : w k ^ (-β) * w k ^ β = 1 := by
        rw [← Real.rpow_add (hw k)]; simp
      push_cast
      have hk' : ((w k ^ (-β) : ℝ) : ℂ) * ((w k ^ β : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, hk]; simp
      linear_combination ((w l ^ (-β) : ℝ) : ℂ) * (A l : ℂ) * (a l k : ℂ) * (z k : ℂ) * ((w l ^ (-β) : ℝ) : ℂ) * hk'
    simp_rw [this]
    simp only [← Complex.ofReal_sum]
    congr 1
    rw [hP]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h2 : w l ^ (-2 * β) = w l ^ (-β) * w l ^ (-β) := by
      rw [← Real.rpow_add (hw l)]; congr 1; ring
    calc ∑ k ∈ S, (w l ^ (-β) * A l) * (w l ^ (-β) * (a l k * z k))
        = (w l ^ (-β) * A l) * (w l ^ (-β) * ∑ k ∈ S, a l k * z k) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = w l ^ (-2 * β) * A l ^ 2 := by
          rw [show ∑ k ∈ S, a l k * z k = A l from rfl, h2]; ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hPn] at key
  -- `P ≤ (M₁^{1-θ} M₂^θ)^2 Q`
  set M : ℝ := M₁ ^ (1 - θ) * M₂ ^ θ with hM
  have hMn : 0 ≤ M := mul_nonneg (Real.rpow_nonneg hM₁ _) (Real.rpow_nonneg hM₂ _)
  have hcomb : (M₁ * Real.sqrt P * Real.sqrt Q) ^ (1 - θ) * (M₂ * Real.sqrt P * Real.sqrt Q) ^ θ =
      M * (Real.sqrt P * Real.sqrt Q) := by
    have hs : 0 ≤ Real.sqrt P * Real.sqrt Q := by positivity
    rw [mul_assoc M₁, mul_assoc M₂, Real.mul_rpow hM₁ hs, Real.mul_rpow hM₂ hs, hM]
    have : (Real.sqrt P * Real.sqrt Q) ^ (1 - θ) * (Real.sqrt P * Real.sqrt Q) ^ θ =
        Real.sqrt P * Real.sqrt Q := by
      rw [← Real.rpow_add' hs (by linarith : (1 - θ) + θ ≠ 0)]
      simp
    calc M₁ ^ (1 - θ) * (Real.sqrt P * Real.sqrt Q) ^ (1 - θ) *
          (M₂ ^ θ * (Real.sqrt P * Real.sqrt Q) ^ θ)
        = M₁ ^ (1 - θ) * M₂ ^ θ *
          ((Real.sqrt P * Real.sqrt Q) ^ (1 - θ) * (Real.sqrt P * Real.sqrt Q) ^ θ) := by ring
      _ = _ := by rw [this]
  rw [hcomb] at key
  show P ≤ M ^ 2 * Q
  rcases eq_or_lt_of_le hPn with h0 | hpos
  · rw [← h0]; positivity
  · have hsP : 0 < Real.sqrt P := Real.sqrt_pos.mpr hpos
    have h1 : Real.sqrt P ≤ M * Real.sqrt Q := by
      have : Real.sqrt P * Real.sqrt P ≤ M * (Real.sqrt P * Real.sqrt Q) := by
        rw [Real.mul_self_sqrt hPn]; exact key
      nlinarith [this]
    have h2 : P = Real.sqrt P ^ 2 := (Real.sq_sqrt hPn).symm
    rw [h2]
    calc Real.sqrt P ^ 2 ≤ (M * Real.sqrt Q) ^ 2 := pow_le_pow_left₀ hsP.le h1 2
      _ = M ^ 2 * Q := by rw [mul_pow, Real.sq_sqrt hQn]

end HRS.Uniform.Q48b
