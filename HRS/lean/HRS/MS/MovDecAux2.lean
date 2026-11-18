import HRS.MS.MovDecAux1
import HRS.MS.MovLinAux5

/-!
# MOV-2e (2): the energy identity `⟨W_v, S v⟩ = ∫ ρ |∇ A f|²` for Schwartz `v`  (S6.2, TeX L4278-4343)

Namespace `HRS.MS.MovDec`, helper prefix `mov2e_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

With `ψ = √ρ`, `ν = β⁻¹`, `h = ψ v`, `U = g * h`, `F = ∇U = movForce h` and
`W = ν v + ψ U = ψ · A f` (`mov2eW`), `f = v/ψ`, the ground-state frame gives
* `Z_i = ν(∂_i v - ½ v ℓ_i) + ψ F_i` (`mov2eZ`), `ℓ = ∇ log ρ`, with `ψ ∇(A f) = Z`, `∂_i W = Z_i + ½ ℓ_i W`;
* `S v = -∑_i (∂_i Z_i + ½ ℓ_i Z_i)` (`mov2e_S_eq`), i.e. `S = D^* D`-type with `D = ∇ - ½ ℓ`;
* the pointwise identity `W · S v = ∑_i Z_i² - ∑_i ∂_i (W Z_i)` (`mov2e_WS_identity`);
* the divergence theorem for the rapidly decreasing `C¹` fields `W Z_i` (`Mov2eGD`, Mathlib's
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` with `g = 1`), giving
  `∫ W S v = ∫ ∑_i Z_i² = ∫ ρ |∇ (A f)|²` (`mov2e_energy_identity`).

The classes `Mov2ePB` (polynomially bounded `C¹` with polynomially bounded derivative) and `Mov2eGD` (all weights)
carry the bookkeeping of the Gaussian and Schwartz decay; the potential `U` is only of linear growth (`|U| ≤ |U(0)| +
B‖x‖`, `‖∇U‖ = ‖F‖ ≤ B`), which is all that is needed (`s = 0` included).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovDec

open HRS.Whole

variable {d : ℕ}

/-! ### Decay classes -/

/-- Polynomially bounded `C¹` function with polynomially bounded derivative. -/
def Mov2ePB (φ : Euc d → ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧ ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ x, |φ x| + ‖fderiv ℝ φ x‖ ≤ C * (1 + ‖x‖) ^ N

/-- `C¹` function which, with its derivative, decays faster than every polynomial. -/
def Mov2eGD (φ : Euc d → ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ N * (|φ x| + ‖fderiv ℝ φ x‖) ≤ C

lemma mov2e_one_add_pow_ge (x : Euc d) (N : ℕ) : 1 ≤ (1 + ‖x‖) ^ N :=
  one_le_pow₀ (by linarith [norm_nonneg x])

lemma mov2e_one_add_pow_pos (x : Euc d) (N : ℕ) : 0 < (1 + ‖x‖) ^ N :=
  pow_pos (by linarith [norm_nonneg x]) N

namespace Mov2ePB

variable {φ ψ : Euc d → ℝ}

lemma add (a : Mov2ePB φ) (b : Mov2ePB ψ) : Mov2ePB (fun x => φ x + ψ x) := by
  obtain ⟨ha, C₁, N₁, hC₁, h₁⟩ := a
  obtain ⟨hb, C₂, N₂, hC₂, h₂⟩ := b
  refine ⟨ha.add hb, C₁ + C₂, max N₁ N₂, by positivity, fun x => ?_⟩
  have hd : fderiv ℝ (fun x => φ x + ψ x) x = fderiv ℝ φ x + fderiv ℝ ψ x :=
    fderiv_add (ha.differentiable (by norm_num) x) (hb.differentiable (by norm_num) x)
  rw [hd]
  have e1 : (1 + ‖x‖) ^ N₁ ≤ (1 + ‖x‖) ^ max N₁ N₂ := pow_le_pow_right₀ (by linarith [norm_nonneg x]) (le_max_left _ _)
  have e2 : (1 + ‖x‖) ^ N₂ ≤ (1 + ‖x‖) ^ max N₁ N₂ := pow_le_pow_right₀ (by linarith [norm_nonneg x]) (le_max_right _ _)
  have := h₁ x
  have := h₂ x
  calc |φ x + ψ x| + ‖fderiv ℝ φ x + fderiv ℝ ψ x‖ ≤ (|φ x| + ‖fderiv ℝ φ x‖) + (|ψ x| + ‖fderiv ℝ ψ x‖) := by
        linarith [abs_add_le (φ x) (ψ x), norm_add_le (fderiv ℝ φ x) (fderiv ℝ ψ x)]
    _ ≤ C₁ * (1 + ‖x‖) ^ N₁ + C₂ * (1 + ‖x‖) ^ N₂ := add_le_add (h₁ x) (h₂ x)
    _ ≤ C₁ * (1 + ‖x‖) ^ max N₁ N₂ + C₂ * (1 + ‖x‖) ^ max N₁ N₂ :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hC₁) (mul_le_mul_of_nonneg_left e2 hC₂)
    _ = _ := by ring

lemma const_mul (a : Mov2ePB φ) (t : ℝ) : Mov2ePB (fun x => t * φ x) := by
  obtain ⟨ha, C, N, hC, h⟩ := a
  refine ⟨contDiff_const.mul ha, |t| * C, N, by positivity, fun x => ?_⟩
  have hd : fderiv ℝ (fun x => t * φ x) x = t • fderiv ℝ φ x :=
    fderiv_const_mul (ha.differentiable (by norm_num) x) t
  rw [hd, norm_smul, Real.norm_eq_abs, abs_mul]
  calc |t| * |φ x| + |t| * ‖fderiv ℝ φ x‖ = |t| * (|φ x| + ‖fderiv ℝ φ x‖) := by ring
    _ ≤ |t| * (C * (1 + ‖x‖) ^ N) := mul_le_mul_of_nonneg_left (h x) (abs_nonneg _)
    _ = _ := by ring

lemma mul (a : Mov2ePB φ) (b : Mov2ePB ψ) : Mov2ePB (fun x => φ x * ψ x) := by
  obtain ⟨ha, C₁, N₁, hC₁, h₁⟩ := a
  obtain ⟨hb, C₂, N₂, hC₂, h₂⟩ := b
  refine ⟨ha.mul hb, C₁ * C₂, N₁ + N₂, by positivity, fun x => ?_⟩
  have hd : fderiv ℝ (fun x => φ x * ψ x) x = φ x • fderiv ℝ ψ x + ψ x • fderiv ℝ φ x :=
    fderiv_mul (ha.differentiable (by norm_num) x) (hb.differentiable (by norm_num) x)
  rw [hd]
  have p1 := h₁ x
  have p2 := h₂ x
  have n1 := norm_nonneg (fderiv ℝ φ x)
  have n2 := norm_nonneg (fderiv ℝ ψ x)
  have a1 := abs_nonneg (φ x)
  have a2 := abs_nonneg (ψ x)
  have hn : ‖φ x • fderiv ℝ ψ x + ψ x • fderiv ℝ φ x‖ ≤ |φ x| * ‖fderiv ℝ ψ x‖ + |ψ x| * ‖fderiv ℝ φ x‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have : |φ x * ψ x| + ‖φ x • fderiv ℝ ψ x + ψ x • fderiv ℝ φ x‖ ≤
      (|φ x| + ‖fderiv ℝ φ x‖) * (|ψ x| + ‖fderiv ℝ ψ x‖) := by
    rw [abs_mul]; nlinarith [mul_nonneg n1 n2, mul_nonneg a1 n2, mul_nonneg a2 n1]
  calc _ ≤ (|φ x| + ‖fderiv ℝ φ x‖) * (|ψ x| + ‖fderiv ℝ ψ x‖) := this
    _ ≤ (C₁ * (1 + ‖x‖) ^ N₁) * (C₂ * (1 + ‖x‖) ^ N₂) :=
        mul_le_mul p1 p2 (by positivity) (by positivity)
    _ = _ := by ring

lemma neg (a : Mov2ePB φ) : Mov2ePB (fun x => -φ x) := by
  simpa using a.const_mul (-1)

lemma sub (a : Mov2ePB φ) (b : Mov2ePB ψ) : Mov2ePB (fun x => φ x - ψ x) := by
  simpa [sub_eq_add_neg] using a.add b.neg

end Mov2ePB

namespace Mov2eGD

variable {φ ψ : Euc d → ℝ}

lemma toPB (a : Mov2eGD φ) : Mov2ePB φ := by
  obtain ⟨ha, h⟩ := a
  obtain ⟨C, hC, hb⟩ := h 0
  exact ⟨ha, C, 0, hC, fun x => by simpa using hb x⟩

lemma add (a : Mov2eGD φ) (b : Mov2eGD ψ) : Mov2eGD (fun x => φ x + ψ x) := by
  refine ⟨a.1.add b.1, fun N => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := a.2 N
  obtain ⟨C₂, hC₂, h₂⟩ := b.2 N
  refine ⟨C₁ + C₂, by positivity, fun x => ?_⟩
  have hd : fderiv ℝ (fun x => φ x + ψ x) x = fderiv ℝ φ x + fderiv ℝ ψ x :=
    fderiv_add (a.1.differentiable (by norm_num) x) (b.1.differentiable (by norm_num) x)
  rw [hd]
  have hp := mov2e_one_add_pow_pos x N
  calc (1 + ‖x‖) ^ N * (|φ x + ψ x| + ‖fderiv ℝ φ x + fderiv ℝ ψ x‖)
      ≤ (1 + ‖x‖) ^ N * ((|φ x| + ‖fderiv ℝ φ x‖) + (|ψ x| + ‖fderiv ℝ ψ x‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hp.le
        linarith [abs_add_le (φ x) (ψ x), norm_add_le (fderiv ℝ φ x) (fderiv ℝ ψ x)]
    _ = (1 + ‖x‖) ^ N * (|φ x| + ‖fderiv ℝ φ x‖) + (1 + ‖x‖) ^ N * (|ψ x| + ‖fderiv ℝ ψ x‖) := by ring
    _ ≤ C₁ + C₂ := add_le_add (h₁ x) (h₂ x)

lemma const_mul (a : Mov2eGD φ) (t : ℝ) : Mov2eGD (fun x => t * φ x) := by
  refine ⟨contDiff_const.mul a.1, fun N => ?_⟩
  obtain ⟨C, hC, h⟩ := a.2 N
  refine ⟨|t| * C, by positivity, fun x => ?_⟩
  have hd : fderiv ℝ (fun x => t * φ x) x = t • fderiv ℝ φ x :=
    fderiv_const_mul (a.1.differentiable (by norm_num) x) t
  rw [hd, norm_smul, Real.norm_eq_abs, abs_mul]
  calc (1 + ‖x‖) ^ N * (|t| * |φ x| + |t| * ‖fderiv ℝ φ x‖)
      = |t| * ((1 + ‖x‖) ^ N * (|φ x| + ‖fderiv ℝ φ x‖)) := by ring
    _ ≤ |t| * C := mul_le_mul_of_nonneg_left (h x) (abs_nonneg _)

lemma neg (a : Mov2eGD φ) : Mov2eGD (fun x => -φ x) := by
  simpa using a.const_mul (-1)

lemma sub (a : Mov2eGD φ) (b : Mov2eGD ψ) : Mov2eGD (fun x => φ x - ψ x) := by
  simpa [sub_eq_add_neg] using a.add b.neg

/-- `GD · PB ⊂ GD`. -/
lemma mul_pb (a : Mov2eGD φ) (b : Mov2ePB ψ) : Mov2eGD (fun x => φ x * ψ x) := by
  refine ⟨a.1.mul b.1, fun N => ?_⟩
  obtain ⟨hb, C₂, N₂, hC₂, h₂⟩ := b
  obtain ⟨C₁, hC₁, h₁⟩ := a.2 (N + N₂)
  refine ⟨C₁ * C₂, by positivity, fun x => ?_⟩
  have hd : fderiv ℝ (fun x => φ x * ψ x) x = φ x • fderiv ℝ ψ x + ψ x • fderiv ℝ φ x :=
    fderiv_mul (a.1.differentiable (by norm_num) x) (hb.differentiable (by norm_num) x)
  rw [hd]
  have p1 := h₁ x
  have p2 := h₂ x
  have n1 := norm_nonneg (fderiv ℝ φ x)
  have n2 := norm_nonneg (fderiv ℝ ψ x)
  have a1 := abs_nonneg (φ x)
  have a2 := abs_nonneg (ψ x)
  have hn : ‖φ x • fderiv ℝ ψ x + ψ x • fderiv ℝ φ x‖ ≤ |φ x| * ‖fderiv ℝ ψ x‖ + |ψ x| * ‖fderiv ℝ φ x‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have key : |φ x * ψ x| + ‖φ x • fderiv ℝ ψ x + ψ x • fderiv ℝ φ x‖ ≤
      (|φ x| + ‖fderiv ℝ φ x‖) * (|ψ x| + ‖fderiv ℝ ψ x‖) := by
    rw [abs_mul]; nlinarith [mul_nonneg n1 n2, mul_nonneg a1 n2, mul_nonneg a2 n1]
  have hp := mov2e_one_add_pow_pos x N
  calc (1 + ‖x‖) ^ N * (|φ x * ψ x| + ‖φ x • fderiv ℝ ψ x + ψ x • fderiv ℝ φ x‖)
      ≤ (1 + ‖x‖) ^ N * ((|φ x| + ‖fderiv ℝ φ x‖) * (|ψ x| + ‖fderiv ℝ ψ x‖)) :=
        mul_le_mul_of_nonneg_left key hp.le
    _ ≤ (1 + ‖x‖) ^ N * ((|φ x| + ‖fderiv ℝ φ x‖) * (C₂ * (1 + ‖x‖) ^ N₂)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left p2 (by positivity)) hp.le
    _ = ((1 + ‖x‖) ^ (N + N₂) * (|φ x| + ‖fderiv ℝ φ x‖)) * C₂ := by rw [pow_add]; ring
    _ ≤ C₁ * C₂ := mul_le_mul_of_nonneg_right p1 hC₂

lemma mul (a : Mov2eGD φ) (b : Mov2eGD ψ) : Mov2eGD (fun x => φ x * ψ x) := a.mul_pb b.toPB

/-- A decay-class function is integrable. -/
lemma integrable (a : Mov2eGD φ) : Integrable φ := by
  obtain ⟨C, hC, h⟩ := a.2 (d + 1)
  have hint := integrable_one_add_norm (E := Euc d) (μ := (volume : Measure (Euc d))) (r := ((d + 1 : ℕ) : ℝ))
    (by simp)
  refine Integrable.mono' (hint.const_mul C) a.1.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  have hp := mov2e_one_add_pow_pos x (d + 1)
  have e : (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) = ((1 + ‖x‖) ^ (d + 1))⁻¹ := by
    rw [Real.rpow_neg (by linarith [norm_nonneg x]), Real.rpow_natCast]
  rw [e]
  have h1 := h x
  have : |φ x| * (1 + ‖x‖) ^ (d + 1) ≤ (1 + ‖x‖) ^ (d + 1) * (|φ x| + ‖fderiv ℝ φ x‖) := by
    nlinarith [mul_nonneg hp.le (norm_nonneg (fderiv ℝ φ x))]
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  linarith

/-- The directional derivatives are integrable. -/
lemma integrable_fderiv (a : Mov2eGD φ) (e : Euc d) : Integrable (fun x => fderiv ℝ φ x e) := by
  obtain ⟨C, hC, h⟩ := a.2 (d + 1)
  have hint := integrable_one_add_norm (E := Euc d) (μ := (volume : Measure (Euc d))) (r := ((d + 1 : ℕ) : ℝ))
    (by simp)
  refine Integrable.mono' (hint.const_mul (C * ‖e‖)) ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · exact ((a.1.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable
  rw [Real.norm_eq_abs]
  have hp := mov2e_one_add_pow_pos x (d + 1)
  have e1 : (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) = ((1 + ‖x‖) ^ (d + 1))⁻¹ := by
    rw [Real.rpow_neg (by linarith [norm_nonneg x]), Real.rpow_natCast]
  rw [e1]
  have h1 := h x
  have h2 : |fderiv ℝ φ x e| ≤ ‖fderiv ℝ φ x‖ * ‖e‖ := by
    simpa [Real.norm_eq_abs] using (fderiv ℝ φ x).le_opNorm e
  have h3 : (1 + ‖x‖) ^ (d + 1) * ‖fderiv ℝ φ x‖ ≤ C := by
    nlinarith [mul_nonneg hp.le (abs_nonneg (φ x))]
  have h4 : |fderiv ℝ φ x e| * (1 + ‖x‖) ^ (d + 1) ≤ C * ‖e‖ := by
    calc |fderiv ℝ φ x e| * (1 + ‖x‖) ^ (d + 1) ≤ (‖fderiv ℝ φ x‖ * ‖e‖) * (1 + ‖x‖) ^ (d + 1) :=
          mul_le_mul_of_nonneg_right h2 hp.le
      _ = ((1 + ‖x‖) ^ (d + 1) * ‖fderiv ℝ φ x‖) * ‖e‖ := by ring
      _ ≤ C * ‖e‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  linarith

/-- **Divergence theorem on `ℝ^d`**: `∫ ∂_e φ = 0` for `φ` in the decay class. -/
lemma integral_fderiv_zero (a : Mov2eGD φ) (e : Euc d) : ∫ x, fderiv ℝ φ x e = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := φ) (g := fun _ : Euc d => (1 : ℝ)) (v := e)
    (by simpa using a.integrable_fderiv e) (by simpa using (integrable_zero (Euc d) ℝ volume))
    (by simpa using a.integrable)
    (fun x _ => a.1.differentiable (by norm_num) x) (fun x _ => differentiableAt_const _)
  simpa using h.symm

end Mov2eGD

/-! ### Atoms of the decay classes -/

lemma mov2e_schwartz_GD (a : SchwartzMap (Euc d) ℝ) : Mov2eGD (a : Euc d → ℝ) := by
  refine ⟨a.smooth 1, fun N => ?_⟩
  set S := (Finset.Iic (N, 1)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) a with hS
  have h00 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 1)) (k := N) (n := 0)
    le_rfl (by norm_num) a 0
  have hS0 : 0 ≤ 2 ^ (N, 1).1 * S := by
    refine le_trans ?_ h00
    positivity
  refine ⟨2 * (2 ^ N * S), by simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hS0, fun x => ?_⟩
  have h0 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 1)) (k := N) (n := 0)
    le_rfl (by norm_num) a x
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 1)) (k := N) (n := 1)
    le_rfl le_rfl a x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
  rw [norm_iteratedFDeriv_one] at h1
  simp only at h0 h1
  nlinarith

lemma mov2e_schwartz_pderiv_GD (a : SchwartzMap (Euc d) ℝ) (e : Euc d) :
    Mov2eGD (fun x => fderiv ℝ a x e) := by
  have := mov2e_schwartz_GD (LineDeriv.lineDerivOp e a)
  have hfun : (fun x => fderiv ℝ a x e) = ⇑(LineDeriv.lineDerivOp e a) := by
    funext x; exact (SchwartzMap.lineDerivOp_apply_eq_fderiv e a x).symm
  rw [hfun]; exact this

/-- A `C¹` function with Gaussian bounds on itself and its derivative lies in `Mov2eGD`. -/
lemma mov2e_gauss_GD {φ : Euc d → ℝ} (hφ : ContDiff ℝ 1 φ) {C₀ c₀ C₁ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (h0 : ∀ x, |φ x| ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2))
    (h1 : ∀ x, ‖fderiv ℝ φ x‖ ≤ C₁ * Real.exp (-c₁ * ‖x‖ ^ 2)) : Mov2eGD φ := by
  have hC₀ : 0 ≤ C₀ := by
    have := h0 0
    simp only [norm_zero, mul_zero, zero_pow two_ne_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  have hC₁ : 0 ≤ C₁ := by
    have := h1 0
    simp only [norm_zero, mul_zero, zero_pow two_ne_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have key : ∀ (c : ℝ), 0 < c → ∀ N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 ≤ r →
      (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ K := by
    intro c hc N
    refine ⟨N.factorial * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)), by positivity, fun r hr => ?_⟩
    have := HRS.MS.Mov0.mov0_pow_exp_bound (a := 2 * c) (M := 0) (by positivity) N r hr
    have e : -(2 * c * r ^ 2 / 2) + 0 * r = -c * r ^ 2 := by ring
    rw [e] at this
    refine this.trans ?_
    have : Real.exp (-(2 * c / 4) * r ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg r])
    calc _ ≤ (N.factorial : ℝ) * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)) * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  refine ⟨hφ, fun N => ?_⟩
  obtain ⟨K₀, hK₀, hk₀⟩ := key c₀ hc₀ N
  obtain ⟨K₁, hK₁, hk₁⟩ := key c₁ hc₁ N
  refine ⟨C₀ * K₀ + C₁ * K₁, by positivity, fun x => ?_⟩
  have hp := mov2e_one_add_pow_pos x N
  calc (1 + ‖x‖) ^ N * (|φ x| + ‖fderiv ℝ φ x‖)
      ≤ (1 + ‖x‖) ^ N * (C₀ * Real.exp (-c₀ * ‖x‖ ^ 2) + C₁ * Real.exp (-c₁ * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add (h0 x) (h1 x)) hp.le
    _ = C₀ * ((1 + ‖x‖) ^ N * Real.exp (-c₀ * ‖x‖ ^ 2)) + C₁ * ((1 + ‖x‖) ^ N * Real.exp (-c₁ * ‖x‖ ^ 2)) := by
        ring
    _ ≤ C₀ * K₀ + C₁ * K₁ :=
        add_le_add (mul_le_mul_of_nonneg_left (hk₀ _ (norm_nonneg x)) hC₀)
          (mul_le_mul_of_nonneg_left (hk₁ _ (norm_nonneg x)) hC₁)

lemma Mov2eRho.psi_GD {ρ : Euc d → ℝ} (hρ : Mov2eRho d ρ) : Mov2eGD (fun x => Real.sqrt (ρ x)) := by
  obtain ⟨C₀, c₀, hc₀, hb₀⟩ := hρ.data.sqrt_gauss 0
  obtain ⟨C₁, c₁, hc₁, hb₁⟩ := hρ.data.sqrt_gauss 1
  refine mov2e_gauss_GD (C₀ := C₀) (C₁ := C₁) (hρ.data.sqrt_smooth.of_le (by exact_mod_cast le_top)) hc₀ hc₁
    (fun x => ?_) (fun x => ?_)
  · have := hb₀ x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · have := hb₁ x
    rwa [norm_iteratedFDeriv_one] at this

lemma Mov2eRho.rho_GD {ρ : Euc d → ℝ} (hρ : Mov2eRho d ρ) : Mov2eGD ρ := by
  have h := hρ.psi_GD.mul hρ.psi_GD
  have e : (fun x => Real.sqrt (ρ x) * Real.sqrt (ρ x)) = ρ := funext hρ.psi_sq
  rwa [e] at h

/-- The data on `ℓ = ∇ log ρ` and the Gaussian rate used by the force bounds (all provided by MOV-0). -/
structure Mov2eEll (d : ℕ) (ρ : Euc d → ℝ) : Prop where
  ex : ∃ c a M0 : ℝ, 0 < c ∧ 0 ≤ a ∧ 0 ≤ M0 ∧
    (∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρ y)) x‖ ≤
      C * Real.exp (-c * ‖x‖ ^ 2)) ∧
    ContDiff ℝ ∞ (fun x => gradient (fun y => Real.log (ρ y)) x) ∧
    (∀ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ≤ a * ‖x‖ + M0) ∧
    (∀ l : ℕ, 1 ≤ l → ∃ Df : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ l (fun y => gradient (fun z => Real.log (ρ z)) y) x‖ ≤ Df)

lemma Mov2eEll.smooth {ρ : Euc d → ℝ} (h : Mov2eEll d ρ) :
    ContDiff ℝ ∞ (fun x => gradient (fun y => Real.log (ρ y)) x) := by
  obtain ⟨c, a, M0, -, -, -, -, hs, -, -⟩ := h.ex
  exact hs

/-- Components of a vector valued function with polynomially bounded value and derivative. -/
lemma mov2e_PB_coord {F : Euc d → Euc d} (hF : ContDiff ℝ 1 F) {B : ℝ} {N : ℕ} (hB : 0 ≤ B)
    (hb : ∀ x, ‖F x‖ + ‖fderiv ℝ F x‖ ≤ B * (1 + ‖x‖) ^ N) (i : Fin d) :
    Mov2ePB (fun x => F x i) := by
  refine ⟨contDiff_euclidean.1 hF i, B, N, hB, fun x => ?_⟩
  have hd : DifferentiableAt ℝ F x := hF.differentiable (by norm_num) x
  have hder : fderiv ℝ (fun y => F y i) x = (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ F x) :=
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  rw [hder]
  have h1 : |F x i| ≤ ‖F x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (F x) i
  have h2 : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ F x)‖ ≤ ‖fderiv ℝ F x‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have := HRS.MS.MovForce.movb2_norm_proj_le (d := d) i
    nlinarith [norm_nonneg (fderiv ℝ F x)]
  linarith [hb x]

lemma Mov2eEll.ell_PB {ρ : Euc d → ℝ} (h : Mov2eEll d ρ) (i : Fin d) :
    Mov2ePB (fun x => gradient (fun y => Real.log (ρ y)) x i) := by
  obtain ⟨c, a, M0, -, ha, hM0, -, hs, hlin, hD⟩ := h.ex
  obtain ⟨Df, hDf⟩ := hD 1 le_rfl
  have hDf0 : 0 ≤ Df := (norm_nonneg _).trans (hDf 0)
  refine mov2e_PB_coord (hs.of_le (by exact_mod_cast le_top)) (B := a + M0 + Df) (N := 1) (by positivity)
    (fun x => ?_) i
  have h1 := hlin x
  have h2 := hDf x
  rw [norm_iteratedFDeriv_one] at h2
  nlinarith [norm_nonneg x]


/-! ### The force and the potential -/

section Force

variable {s : ℝ} {ρ : Euc d → ℝ}

/-- `h = ψ v`. -/
abbrev mov2eH (ρ : Euc d → ℝ) (v : Euc d → ℝ) : Euc d → ℝ := fun x => Real.sqrt (ρ x) * v x

/-- The force `F = ∇g * (ψ v)` of a Schwartz `v` is `C¹` with bounded value and derivative (`mov_operators_force_gen`,
`j = 0`). -/
lemma mov2e_force_bdd (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (v : SchwartzMap (Euc d) ℝ) :
    ContDiff ℝ 1 (movForce d s (mov2eH ρ v)) ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      ‖movForce d s (mov2eH ρ v) x‖ ≤ B ∧ ‖fderiv ℝ (movForce d s (mov2eH ρ v)) x‖ ≤ B := by
  obtain ⟨c, a, M0, hc, ha, hM0, hψb, hfs, hf0, hfD⟩ := hE.ex
  obtain ⟨C, hC0, hC⟩ := HRS.MS.MovForce.mov_operators_force_gen hd hs0 hsd hc ha hM0
    hρ.data.sqrt_smooth hψb hfs hf0 hfD 0
  obtain ⟨m0, hm0⟩ := HRS.MS.MovForce.mv1_schwartz_bdd v 0
  obtain ⟨m1, hm1⟩ := HRS.MS.MovForce.mv1_schwartz_bdd v 1
  obtain ⟨m2, hm2⟩ := HRS.MS.MovForce.mv1_schwartz_bdd v 2
  set M : ℝ := |m0| + |m1| + |m2| with hM
  have hM0' : 0 ≤ M := by positivity
  obtain ⟨h1, -, h3⟩ := hC v M hM0' (by simpa using v.smooth 2) (fun k hk x => by
    interval_cases k
    · exact (hm0 x).trans (by simp only [hM]; linarith [le_abs_self m0, abs_nonneg m1, abs_nonneg m2])
    · exact (hm1 x).trans (by simp only [hM]; linarith [le_abs_self m1, abs_nonneg m0, abs_nonneg m2])
    · exact (hm2 x).trans (by simp only [hM]; linarith [le_abs_self m2, abs_nonneg m0, abs_nonneg m1]))
  have hCM : 0 ≤ C * M := mul_nonneg hC0 hM0'
  have key : ∀ i : ℕ, i < 2 → ∀ x, ‖iteratedFDeriv ℝ i (HRS.MS.MovForce.movb2_F d s ρ v) x‖ ≤ C * M := by
    intro i hi x
    have h4 : ENNReal.ofReal ‖iteratedFDeriv ℝ i (HRS.MS.MovForce.movb2_F d s ρ v) x‖ ≤
        ENNReal.ofReal (C * M) := by
      refine le_trans ?_ (le_trans le_self_add h3)
      unfold cbNormVecE
      refine le_trans (le_iSup (fun x => ENNReal.ofReal ‖iteratedFDeriv ℝ i
        (HRS.MS.MovForce.movb2_F d s ρ v) x‖) x) ?_
      exact Finset.single_le_sum (f := fun i => ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ i
        (HRS.MS.MovForce.movb2_F d s ρ v) x‖) (fun _ _ => bot_le) (Finset.mem_range.2 (by omega))
    exact (ENNReal.ofReal_le_ofReal_iff hCM).1 h4
  refine ⟨(show ContDiff ℝ 1 (HRS.MS.MovForce.movb2_F d s ρ v) by exact_mod_cast h1), C * M, hCM,
    fun x => ⟨?_, ?_⟩⟩
  · have := key 0 (by norm_num) x
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  · have := key 1 (by norm_num) x
    rw [norm_iteratedFDeriv_one] at this
    exact this

/-- The potential `U = g * (ψ v)`: `C¹`, `∇U = F`, linear growth. -/
lemma mov2e_U_data (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (v : SchwartzMap (Euc d) ℝ) :
    (∀ x, movForce d s (mov2eH ρ v) x =
      gradient (HRS.Whole.convFun (rieszKernel d s) (mov2eH ρ v)) x) ∧
    Differentiable ℝ (HRS.Whole.convFun (rieszKernel d s) (mov2eH ρ v)) ∧
    ContDiff ℝ 1 (HRS.Whole.convFun (rieszKernel d s) (mov2eH ρ v)) ∧
    Mov2ePB (HRS.Whole.convFun (rieszKernel d s) (mov2eH ρ v)) := by
  obtain ⟨hF1, B, hB0, hB⟩ := mov2e_force_bdd hd hs0 hsd hρ hE v
  have hg := HRS.MS.MovForce.mv1_h_movGauss hρ.data v 1
  obtain ⟨C, c, hC, hc, h0, h1⟩ := HRS.MS.MovForce.mv1_gauss01 hg
  have hh1 : ContDiff ℝ 1 (mov2eH ρ v) :=
    ((HRS.MS.MovForce.mv1_h_gauss hρ.data v).1).of_le (by exact_mod_cast le_top)
  have hsplit := fun x => HRS.MS.MovForce.mv1_force_eq_grad hd hs0 hsd hc hC hh1 h0 h1 x
  set U := HRS.Whole.convFun (rieszKernel d s) (mov2eH ρ v) with hU
  have hdiff : Differentiable ℝ U := fun x => (hsplit x).2
  have hfd : ∀ x, fderiv ℝ U x = (InnerProductSpace.toDual ℝ (Euc d)) (movForce d s (mov2eH ρ v) x) := by
    intro x
    rw [(hsplit x).1]
    simp [gradient]
  have hcont : Continuous (fderiv ℝ U) := by
    have : fderiv ℝ U = fun x => (InnerProductSpace.toDual ℝ (Euc d)) (movForce d s (mov2eH ρ v) x) :=
      funext hfd
    rw [this]
    exact (InnerProductSpace.toDual ℝ (Euc d)).continuous.comp hF1.continuous
  have hC1 : ContDiff ℝ 1 U := contDiff_one_iff_fderiv.2 ⟨hdiff, hcont⟩
  refine ⟨fun x => (hsplit x).1, hdiff, hC1, hC1, |U 0| + 2 * B, 1, by positivity, fun x => ?_⟩
  have hn : ‖fderiv ℝ U x‖ ≤ B := by
    rw [hfd x, LinearIsometryEquiv.norm_map]; exact (hB x).1
  have hlip : ‖U x - U 0‖ ≤ B * ‖x - 0‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun y _ => hdiff y)
      (fun y _ => by rw [hfd y, LinearIsometryEquiv.norm_map]; exact (hB y).1)
      (Set.mem_univ 0) (Set.mem_univ x)
  rw [sub_zero, Real.norm_eq_abs] at hlip
  have : |U x| ≤ |U 0| + |U x - U 0| := by
    have := abs_add_le (U 0) (U x - U 0)
    simpa using this
  rw [pow_one]
  nlinarith [norm_nonneg x, abs_nonneg (U 0)]

end Force


/-! ### The ground-state frame: `W`, `Z_i`, `S v = -∑ (∂_i Z_i + ½ ℓ_i Z_i)` -/

section Frame

variable {s : ℝ} {ρ : Euc d → ℝ}

/-- `Z_i = ν(∂_i v - ½ v ℓ_i) + ψ F_i`: the components of `ψ ∇(A f)`. -/
def mov2eZ (d : ℕ) (s β : ℝ) (ρ : Euc d → ℝ) (v : Euc d → ℝ) (i : Fin d) (x : Euc d) : ℝ :=
  β⁻¹ * (fderiv ℝ v x (EuclideanSpace.single i 1) -
      (1 / 2) * (v x * gradient (fun y => Real.log (ρ y)) x i)) +
    Real.sqrt (ρ x) * movForce d s (mov2eH ρ v) x i

lemma mov2e_movDiv_coord {G : Euc d → Euc d} {x : Euc d} (hG : DifferentiableAt ℝ G x) :
    movDiv G x = ∑ i, fderiv ℝ (fun y => G y i) x (EuclideanSpace.single i 1) := by
  unfold movDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  have hder : fderiv ℝ (fun y => G y i) x = (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ G x) :=
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x hG.hasFDerivAt).fderiv
  rw [hder]
  rfl

lemma mov2e_force_PB (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (v : SchwartzMap (Euc d) ℝ) (i : Fin d) :
    Mov2ePB (fun x => movForce d s (mov2eH ρ v) x i) := by
  obtain ⟨hF1, B, hB0, hB⟩ := mov2e_force_bdd hd hs0 hsd hρ hE v
  refine mov2e_PB_coord hF1 (B := 2 * B) (N := 0) (by positivity) (fun x => ?_) i
  have := hB x
  simp only [pow_zero, mul_one]
  linarith [this.1, this.2]

lemma mov2e_W_GD (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (β : ℝ)
    (v : SchwartzMap (Euc d) ℝ) : Mov2eGD (mov2eW d s β ρ v) := by
  have hU := (mov2e_U_data hd hs0 hsd hρ hE v).2.2.2
  have h1 := (mov2e_schwartz_GD v).const_mul β⁻¹
  have h2 := hρ.psi_GD.mul_pb hU
  exact h1.add h2

lemma mov2e_Z_GD (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (β : ℝ)
    (v : SchwartzMap (Euc d) ℝ) (i : Fin d) : Mov2eGD (mov2eZ d s β ρ v i) := by
  have hA := mov2e_schwartz_pderiv_GD v (EuclideanSpace.single i 1)
  have hB := (mov2e_schwartz_GD v).mul_pb (hE.ell_PB i)
  have hC := hρ.psi_GD.mul_pb (mov2e_force_PB hd hs0 hsd hρ hE v i)
  exact (hA.sub (hB.const_mul (1 / 2))).const_mul β⁻¹ |>.add hC

/-- `∂_i W = Z_i + ½ ℓ_i W`. -/
lemma mov2e_W_deriv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (β : ℝ)
    (v : SchwartzMap (Euc d) ℝ) (i : Fin d) (x : Euc d) :
    fderiv ℝ (mov2eW d s β ρ v) x (EuclideanSpace.single i 1) =
      mov2eZ d s β ρ v i x + (1 / 2) * gradient (fun y => Real.log (ρ y)) x i * mov2eW d s β ρ v x := by
  obtain ⟨hgrad, hUd, -, -⟩ := mov2e_U_data hd hs0 hsd hρ hE v
  set U := HRS.Whole.convFun (rieszKernel d s) (mov2eH ρ v) with hU
  have hψd : DifferentiableAt ℝ (fun y => Real.sqrt (ρ y)) x :=
    (hρ.data.sqrt_smooth.differentiable (by simp)) x
  have hvd : DifferentiableAt ℝ (fun y => v y) x := v.differentiableAt
  have hW : mov2eW d s β ρ v = fun y => β⁻¹ * v y + Real.sqrt (ρ y) * U y := by
    funext y; rfl
  rw [hW]
  have hρd : DifferentiableAt ℝ ρ x := (hρ.data.smooth.differentiable (by simp)) x
  have hsq := HRS.MS.MovForce.mv1_fderiv_sqrt hρd (hρ.pos x) (EuclideanSpace.single i 1)
  have hlog : fderiv ℝ (fun y => Real.log (ρ y)) x (EuclideanSpace.single i 1) =
      gradient (fun y => Real.log (ρ y)) x i := (movtr_gradient_apply _ x i).symm
  have hUi : fderiv ℝ U x (EuclideanSpace.single i 1) = movForce d s (mov2eH ρ v) x i := by
    rw [hgrad x, movtr_gradient_apply]
  have hd1 : HasFDerivAt (fun y => β⁻¹ * v y + Real.sqrt (ρ y) * U y)
      (β⁻¹ • fderiv ℝ (fun y => v y) x + (Real.sqrt (ρ x) • fderiv ℝ U x +
        U x • fderiv ℝ (fun y => Real.sqrt (ρ y)) x)) x :=
    (hvd.hasFDerivAt.const_mul β⁻¹).add (hψd.hasFDerivAt.mul (hUd x).hasFDerivAt)
  rw [hd1.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hsq, hlog, hUi]
  unfold mov2eZ
  dsimp only
  ring

/-- **`S v = -∑_i (∂_i Z_i + ½ ℓ_i Z_i)`**: the ground-state frame of the linearised generator. -/
theorem mov2e_S_eq (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (β : ℝ)
    (v : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    movS d s β ρ v x = -∑ i, (fderiv ℝ (mov2eZ d s β ρ v i) x (EuclideanSpace.single i 1) +
      (1 / 2) * gradient (fun y => Real.log (ρ y)) x i * mov2eZ d s β ρ v i x) := by
  have hpos := hρ.data.pos
  have hρs := hρ.data.smooth
  have hρd : Differentiable ℝ ρ := hρs.differentiable (by simp)
  have hψ := hρ.data.sqrt_smooth
  have hψx : 0 < Real.sqrt (ρ x) := hρ.psi_pos x
  have hv : ContDiff ℝ ∞ (v : Euc d → ℝ) := v.smooth ⊤
  obtain ⟨hF1, -⟩ := mov2e_force_bdd hd hs0 hsd hρ hE v
  have hFd : DifferentiableAt ℝ (movForce d s (mov2eH ρ v)) x := (hF1.differentiable (by norm_num)) x
  set A : Euc d → Euc d := fun y => ρ y • gradient (fun z => β⁻¹ * (v z / Real.sqrt (ρ z))) y with hA
  set B : Euc d → Euc d := fun y => ρ y • movForce d s (mov2eH ρ v) y with hB
  have hAeq : A = fun y => (β⁻¹ * Real.sqrt (ρ y)) • gradient (v : Euc d → ℝ) y +
      (-(β⁻¹ * v y)) • gradient (fun z => Real.sqrt (ρ z)) y :=
    funext fun y => HRS.MS.MovLin.mov2a_flux hρs hpos hv y
  have hc1 : DifferentiableAt ℝ (fun y => β⁻¹ * Real.sqrt (ρ y)) x :=
    (hψ.differentiable (by simp) x).const_mul _
  have hc2 : DifferentiableAt ℝ (fun y => -(β⁻¹ * v y)) x :=
    ((hv.differentiable (by simp) x).const_mul _).neg
  have hAd : DifferentiableAt ℝ A x := by
    rw [hAeq]
    exact (hc1.smul (HRS.MS.MovLin.mov2a_gradient_diff hv x)).add
      (hc2.smul (HRS.MS.MovLin.mov2a_gradient_diff hψ x))
  have hBd : DifferentiableAt ℝ B x := (hρd x).smul hFd
  have hsum : movS d s β ρ v x = -(Real.sqrt (ρ x))⁻¹ * movDiv (fun y => A y + B y) x := by
    unfold movS movP
    rw [HRS.MS.MovLin.mov2a_movDiv_add hAd hBd]
    ring
  -- coordinates of `A + B`
  have hcoord : ∀ y (i : Fin d), (A y + B y) i = Real.sqrt (ρ y) * mov2eZ d s β ρ v i y := by
    intro y i
    have hs := HRS.MS.MovLin.mov2a_grad_sqrt hρd hpos y
    have e1 : (A y + B y) i = (β⁻¹ * Real.sqrt (ρ y)) * gradient (v : Euc d → ℝ) y i +
        (-(β⁻¹ * v y)) * gradient (fun z => Real.sqrt (ρ z)) y i + ρ y * movForce d s (mov2eH ρ v) y i := by
      simp only [hA, hB]
      rw [HRS.MS.MovLin.mov2a_flux hρs hpos hv y]
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [e1, hs]
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [movtr_gradient_apply]
    have := hρ.psi_sq y
    unfold mov2eZ
    rw [← this]
    simp only [Real.sqrt_mul_self (Real.sqrt_nonneg _)]
    ring
  have hABd : DifferentiableAt ℝ (fun y => A y + B y) x := hAd.add hBd
  have hdiv := mov2e_movDiv_coord hABd
  have hfun : ∀ i : Fin d, (fun y => (A y + B y) i) = fun y => Real.sqrt (ρ y) * mov2eZ d s β ρ v i y :=
    fun i => funext fun y => hcoord y i
  rw [hsum, hdiv]
  simp_rw [hfun]
  have hψd : DifferentiableAt ℝ (fun y => Real.sqrt (ρ y)) x := (hψ.differentiable (by simp)) x
  have hρd' : DifferentiableAt ℝ ρ x := hρd x
  have hterm : ∀ i : Fin d, fderiv ℝ (fun y => Real.sqrt (ρ y) * mov2eZ d s β ρ v i y) x
      (EuclideanSpace.single i 1) =
      Real.sqrt (ρ x) * (fderiv ℝ (mov2eZ d s β ρ v i) x (EuclideanSpace.single i 1) +
        (1 / 2) * gradient (fun y => Real.log (ρ y)) x i * mov2eZ d s β ρ v i x) := by
    intro i
    have hZd : DifferentiableAt ℝ (mov2eZ d s β ρ v i) x :=
      ((mov2e_Z_GD hd hs0 hsd hρ hE β v i).1.differentiable (by norm_num)) x
    have h1 : fderiv ℝ (fun y => Real.sqrt (ρ y) * mov2eZ d s β ρ v i y) x =
        Real.sqrt (ρ x) • fderiv ℝ (mov2eZ d s β ρ v i) x +
          mov2eZ d s β ρ v i x • fderiv ℝ (fun y => Real.sqrt (ρ y)) x :=
      (hψd.hasFDerivAt.mul hZd.hasFDerivAt).fderiv
    rw [h1]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [HRS.MS.MovForce.mv1_fderiv_sqrt hρd' (hρ.pos x),
      (movtr_gradient_apply (fun y => Real.log (ρ y)) x i).symm]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, neg_mul, inv_mul_cancel_left₀ hψx.ne']

/-- The product field `X_i = W Z_i`. -/
lemma mov2e_X_GD (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (β : ℝ)
    (v : SchwartzMap (Euc d) ℝ) (i : Fin d) :
    Mov2eGD (fun y => mov2eW d s β ρ v y * mov2eZ d s β ρ v i y) :=
  (mov2e_W_GD hd hs0 hsd hρ hE β v).mul (mov2e_Z_GD hd hs0 hsd hρ hE β v i)

/-- **Pointwise identity** `W · S v = ∑ Z_i² - ∑ ∂_i (W Z_i)`. -/
theorem mov2e_WS_identity (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (v : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    mov2eW d s β ρ v x * movS d s β ρ v x =
      ∑ i, (mov2eZ d s β ρ v i x) ^ 2 -
        ∑ i, fderiv ℝ (fun y => mov2eW d s β ρ v y * mov2eZ d s β ρ v i y) x (EuclideanSpace.single i 1) := by
  rw [mov2e_S_eq hd hs0 hsd hρ hE β v x, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  have hmul : ∀ i : Fin d, fderiv ℝ (fun y => mov2eW d s β ρ v y * mov2eZ d s β ρ v i y) x
      (EuclideanSpace.single i 1) =
      (mov2eZ d s β ρ v i x + (1 / 2) * gradient (fun y => Real.log (ρ y)) x i * mov2eW d s β ρ v x) *
        mov2eZ d s β ρ v i x +
      mov2eW d s β ρ v x * fderiv ℝ (mov2eZ d s β ρ v i) x (EuclideanSpace.single i 1) := by
    intro i
    have hWd : DifferentiableAt ℝ (mov2eW d s β ρ v) x :=
      ((mov2e_W_GD hd hs0 hsd hρ hE β v).1.differentiable (by norm_num)) x
    have hZd : DifferentiableAt ℝ (mov2eZ d s β ρ v i) x :=
      ((mov2e_Z_GD hd hs0 hsd hρ hE β v i).1.differentiable (by norm_num)) x
    have h1 : fderiv ℝ (fun y => mov2eW d s β ρ v y * mov2eZ d s β ρ v i y) x =
        mov2eW d s β ρ v x • fderiv ℝ (mov2eZ d s β ρ v i) x +
          mov2eZ d s β ρ v i x • fderiv ℝ (mov2eW d s β ρ v) x :=
      (hWd.hasFDerivAt.mul hZd.hasFDerivAt).fderiv
    rw [h1]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [mov2e_W_deriv hd hs0 hsd hρ hE β v i x]
    ring
  simp_rw [hmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The energy identity**: `∫ W · S v = ∫ ∑ Z_i² = ∫ ρ |∇(A f)|²`, all integrals absolutely convergent. -/
theorem mov2e_energy_identity (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) (β : ℝ) (v : SchwartzMap (Euc d) ℝ) :
    Integrable (fun x => mov2eW d s β ρ v x * movS d s β ρ v x) ∧
      ∫ x, mov2eW d s β ρ v x * movS d s β ρ v x = ∫ x, ∑ i, (mov2eZ d s β ρ v i x) ^ 2 := by
  have hZ : ∀ i : Fin d, Integrable (fun x => (mov2eZ d s β ρ v i x) ^ 2) := fun i => by
    have := ((mov2e_Z_GD hd hs0 hsd hρ hE β v i).mul (mov2e_Z_GD hd hs0 hsd hρ hE β v i)).integrable
    exact this.congr (Filter.Eventually.of_forall fun x => by simp [sq])
  have hD : ∀ i : Fin d, Integrable (fun x => fderiv ℝ (fun y => mov2eW d s β ρ v y *
      mov2eZ d s β ρ v i y) x (EuclideanSpace.single i 1)) := fun i =>
    (mov2e_X_GD hd hs0 hsd hρ hE β v i).integrable_fderiv _
  have hZs : Integrable (fun x => ∑ i, (mov2eZ d s β ρ v i x) ^ 2) := integrable_finsetSum _ fun i _ => hZ i
  have hDs : Integrable (fun x => ∑ i, fderiv ℝ (fun y => mov2eW d s β ρ v y * mov2eZ d s β ρ v i y) x
      (EuclideanSpace.single i 1)) := integrable_finsetSum _ fun i _ => hD i
  have hid : (fun x => mov2eW d s β ρ v x * movS d s β ρ v x) = fun x => ∑ i, (mov2eZ d s β ρ v i x) ^ 2 -
      ∑ i, fderiv ℝ (fun y => mov2eW d s β ρ v y * mov2eZ d s β ρ v i y) x (EuclideanSpace.single i 1) :=
    funext fun x => mov2e_WS_identity hd hs0 hsd hρ hE β v x
  rw [hid]
  refine ⟨hZs.sub hDs, ?_⟩
  rw [integral_sub hZs hDs, integral_finset_sum _ fun i _ => hD i]
  have : ∑ i : Fin d, ∫ x, fderiv ℝ (fun y => mov2eW d s β ρ v y * mov2eZ d s β ρ v i y) x
      (EuclideanSpace.single i 1) = 0 :=
    Finset.sum_eq_zero fun i _ => (mov2e_X_GD hd hs0 hsd hρ hE β v i).integral_fderiv_zero _
  rw [this, sub_zero]

lemma mov2e_W_memLp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (β : ℝ)
    (v : SchwartzMap (Euc d) ℝ) : MemLp (mov2eW d s β ρ v) 2 volume := by
  have hW := mov2e_W_GD hd hs0 hsd hρ hE β v
  refine (memLp_two_iff_integrable_sq hW.1.continuous.aestronglyMeasurable).2 ?_
  exact (hW.mul hW).integrable.congr (Filter.Eventually.of_forall fun x => by simp [sq])

end Frame

end HRS.MS.MovDec

end
