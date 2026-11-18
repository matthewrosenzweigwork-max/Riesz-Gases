import HRS.MS.CzElemBAux1

/-!
# ELEM-B, part 2: `lp_tensor_absorption`

Packet ELEM-B (CZ development), namespace `HRS.CZ.ElemB`.  Helper lemmas are prefixed `elemb_`.

`lp_tensor_absorption_proof` has exactly the type of the frozen `HRS.Whole.AppendixA.lp_tensor_absorption`
(`AppendixAAdjoint.lean:953`); the tie is in `CzElemBTie.lean`.  The statement is not changed.  The general smooth odd
`Ω` of the frozen statement is handled: only measurability, boundedness and oddness of `Ω` on the unit sphere are used
(`isPvKernel_of_oddSmooth`).

Proof (all inequalities in `ℝ≥0∞`, which makes the junk values of the Bochner integral harmless:
`‖∫ F‖ₑ ≤ ∫⁻ ‖F‖ₑ` holds for every `F`):

1. `|F(x)| ≤ (card ι · b) · (√μ(x) |W|^{p-1}) · ∑_j |pvOdd W_j (x)|` (`elemb_real_chain`, `b = |Bb|`);
2. `|pvOdd W_j(x)| ≤ ‖Ω‖_S (Lx + Gx)` (`elemb_pvOdd_le`: local difference part plus far part);
3. the local part is absorbed pointwise by `X Y ≤ η X² + Y²/(4η)` into `η μ(x) 𝔡_p[W](x) + (4η)^{-1}|W|^p J`
   (`elemb_local_bound`), the far part by `a^{p-1} G ≤ a^p + G^p` (`elemb_far_bound`);
4. integrate in `x`: only the term `ofReal(μ x) 𝔡_p(x)` is not known to be measurable (`μ` is a bare function), it
   is integrated against a constant (`lintegral_const_mul'`); the other terms are measurable
   (`lintegral_add_right`); Young's inequality (`elemb_Gx_young`) bounds `∫ Gx^p` by `C ∫ |W|^p`.

The constant is `C = (ι'^4 B² + ι'^2 B) J/(4ε) + ι'^2 B √Λ (1 + Ck^p)` with `ι' = card ι`, `B` a bound of `Ω` on the
sphere, `J = ∫_{|z|≤1}|z|^{2-d-θ}`, `Ck = ∫_{|z|>1}|z|^{1-d-θ}`; the hypothesis `p ≥ 2` is used for `𝔡_p`, `θ ∈ (1,2)`
for the finiteness of `J` and `Ck`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.ElemB

open HRS.CZ.Pv HRS.CZ.ElemA
open HRS.Whole.AppendixA (vnorm dissipationDensity pvOdd IsOddSmooth)

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

section Tensor

variable {ι : Type*} [Fintype ι]

/-- the real chain: `|V^{p-2} ∑_i W_i (√a ∑_j B_ij P_j)| ≤ (card · b) (√a V^{p-1}) ∑_j |P_j|` -/
lemma elemb_real_chain (Wx : ι → ℝ) (Bm : Matrix ι ι ℝ) (P : ι → ℝ) {a b p : ℝ} (hp : 2 ≤ p) (ha : 0 ≤ a)
    (hb : ∀ i j, |Bm i j| ≤ b) :
    |vnorm Wx ^ (p - 2) * ∑ i, Wx i * (√a * ∑ j, Bm i j * P j)| ≤
      ((Fintype.card ι : ℝ) * b) * (√a * vnorm Wx ^ (p - 1)) * ∑ j, |P j| := by
  have hV := elemb_vnorm_nonneg Wx
  have hb0 : ∀ i j, 0 ≤ b := fun i j => (abs_nonneg _).trans (hb i j)
  have hS : 0 ≤ ∑ j, |P j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  -- each row
  have hrow : ∀ i, |∑ j, Bm i j * P j| ≤ b * ∑ j, |P j| := fun i => by
    calc |∑ j, Bm i j * P j| ≤ ∑ j, |Bm i j * P j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, b * |P j| := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hb i j) (abs_nonneg _)
      _ = b * ∑ j, |P j| := by rw [Finset.mul_sum]
  have hinner : |∑ i, Wx i * (√a * ∑ j, Bm i j * P j)| ≤
      (∑ i, |Wx i|) * (√a * (b * ∑ j, |P j|)) := by
    calc |∑ i, Wx i * (√a * ∑ j, Bm i j * P j)| ≤ ∑ i, |Wx i * (√a * ∑ j, Bm i j * P j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |Wx i| * (√a * (b * ∑ j, |P j|)) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hrow i) (Real.sqrt_nonneg _))
            (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  have hsum := elemb_sum_abs_le Wx
  have hq : 0 ≤ √a * (b * ∑ j, |P j|) := by
    have : ∀ i : ι, 0 ≤ b := fun i => hb0 i i
    by_cases hne : Nonempty ι
    · obtain ⟨i⟩ := hne
      exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hb0 i i) hS)
    · have : ∑ j : ι, |P j| = 0 := by
        haveI : IsEmpty ι := not_nonempty_iff.1 hne
        simp
      rw [this]; simp
  have hVp : vnorm Wx ^ (p - 2) * vnorm Wx = vnorm Wx ^ (p - 1) := by
    rw [← Real.rpow_add_one' hV (by linarith)]
    congr 1; ring
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hV _)]
  calc vnorm Wx ^ (p - 2) * |∑ i, Wx i * (√a * ∑ j, Bm i j * P j)|
      ≤ vnorm Wx ^ (p - 2) * (((Fintype.card ι : ℝ) * vnorm Wx) * (√a * (b * ∑ j, |P j|))) :=
        mul_le_mul_of_nonneg_left (hinner.trans (mul_le_mul_of_nonneg_right hsum hq))
          (Real.rpow_nonneg hV _)
    _ = ((Fintype.card ι : ℝ) * b) * (√a * (vnorm Wx ^ (p - 2) * vnorm Wx)) * ∑ j, |P j| := by ring
    _ = _ := by rw [hVp]


/-- the pointwise bound of the integrand of `lp_tensor_absorption` -/
lemma elemb_pointwise (hd : 1 ≤ d) {θ p Λ η b B : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) (hp : 2 ≤ p)
    {Ω : 𝔼 → ℝ} (hK : IsPvKernel Ω B) (hη : 0 < η) (hb0 : 0 ≤ b)
    (μ : 𝔼 → ℝ) (Bm : 𝔼 → Matrix ι ι ℝ) (hμ : ∀ x, 0 ≤ μ x ∧ μ x ≤ Λ) (hB : ∀ x i j, |Bm x i j| ≤ b)
    (W : ι → 𝓢(𝔼, ℝ)) (x : 𝔼) :
    ENNReal.ofReal |vnorm (fun i => W i x) ^ (p - 2) * ∑ i, W i x *
        (Real.sqrt (μ x) * ∑ j, Bm x i j * pvOdd d θ Ω (fun y => W j y) x)| ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * b * B) *
        (ENNReal.ofReal η * (ENNReal.ofReal (μ x) * dissipationDensity d θ p (fun y i => W i y) x) +
          (ENNReal.ofReal (1 / (4 * η)) * (ENNReal.ofReal (elemb_V W x ^ p) * elemb_J d θ) +
            ENNReal.ofReal (√Λ) * (ENNReal.ofReal (elemb_V W x ^ p) + elemb_Gx θ W x ^ p))) := by
  have hθ0 : 0 < θ := by linarith
  have ha : 0 ≤ μ x := (hμ x).1
  have hr : 0 ≤ √(μ x) * elemb_V W x ^ (p - 1) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (elemb_V_nonneg W x) _)
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have h1 := elemb_real_chain (fun i => W i x) (Bm x) (fun j => pvOdd d θ Ω (fun y => W j y) x) hp ha
    (hB x)
  have hVeq : vnorm (fun i => W i x) = elemb_V W x := rfl
  rw [hVeq] at h1 ⊢
  have hsum : ENNReal.ofReal (∑ j, |pvOdd d θ Ω (fun y => W j y) x|) ≤
      ENNReal.ofReal (Fintype.card ι : ℝ) * (ENNReal.ofReal B * (elemb_Lx θ W x + elemb_Gx θ W x)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => abs_nonneg _]
    calc ∑ j, ENNReal.ofReal |pvOdd d θ Ω (fun y => W j y) x|
        ≤ ∑ _j : ι, ENNReal.ofReal B * (elemb_Lx θ W x + elemb_Gx θ W x) :=
          Finset.sum_le_sum fun j _ => elemb_pvOdd_le hd hθ0 hθ2 hK W j x
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_natCast]
  have hloc := elemb_local_bound hd hθ0 hp ha hη W x
  have hfar := elemb_far_bound hp ha (hμ x).2 W x θ
  have hc0 : ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * b * B) =
      ENNReal.ofReal ((Fintype.card ι : ℝ) * b) * ENNReal.ofReal (Fintype.card ι : ℝ) * ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hcard hb0),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hcard hb0) hcard)]
    congr 1; ring
  calc ENNReal.ofReal |elemb_V W x ^ (p - 2) * ∑ i, W i x *
        (Real.sqrt (μ x) * ∑ j, Bm x i j * pvOdd d θ Ω (fun y => W j y) x)|
      ≤ ENNReal.ofReal (((Fintype.card ι : ℝ) * b) * (√(μ x) * elemb_V W x ^ (p - 1)) *
          ∑ j, |pvOdd d θ Ω (fun y => W j y) x|) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * b) * ENNReal.ofReal (√(μ x) * elemb_V W x ^ (p - 1)) *
          ENNReal.ofReal (∑ j, |pvOdd d θ Ω (fun y => W j y) x|) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hcard hb0) hr),
          ENNReal.ofReal_mul (mul_nonneg hcard hb0)]
    _ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * b) * ENNReal.ofReal (√(μ x) * elemb_V W x ^ (p - 1)) *
          (ENNReal.ofReal (Fintype.card ι : ℝ) * (ENNReal.ofReal B * (elemb_Lx θ W x + elemb_Gx θ W x))) :=
        mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * b * B) *
          (ENNReal.ofReal (√(μ x) * elemb_V W x ^ (p - 1)) * elemb_Lx θ W x +
            ENNReal.ofReal (√(μ x) * elemb_V W x ^ (p - 1)) * elemb_Gx θ W x) := by
        rw [hc0]; ring
    _ ≤ _ := by
        rw [← add_assoc]
        exact mul_le_mul' le_rfl (add_le_add hloc hfar)


/-- the integrated form, with explicit constants -/
lemma elemb_integrated (hd : 1 ≤ d) {θ p Λ η b B Ck : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) (hp : 2 ≤ p)
    {Ω : 𝔼 → ℝ} (hK : IsPvKernel Ω B) (hη : 0 < η) (hb0 : 0 ≤ b) (hCk : 0 ≤ Ck)
    (hY : ∀ W : ι → 𝓢(𝔼, ℝ), ∫⁻ x, elemb_Gx θ W x ^ p ≤
      ENNReal.ofReal (Ck ^ p) * ∫⁻ x, ENNReal.ofReal (elemb_V W x ^ p))
    (μ : 𝔼 → ℝ) (Bm : 𝔼 → Matrix ι ι ℝ) (hμ : ∀ x, 0 ≤ μ x ∧ μ x ≤ Λ) (hB : ∀ x i j, |Bm x i j| ≤ b)
    (W : ι → 𝓢(𝔼, ℝ)) :
    ENNReal.ofReal |∫ x, vnorm (fun i => W i x) ^ (p - 2) * ∑ i, W i x *
        (Real.sqrt (μ x) * ∑ j, Bm x i j * pvOdd d θ Ω (fun y => W j y) x)| ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * b * B * η) *
          (∫⁻ x, ENNReal.ofReal (μ x) * dissipationDensity d θ p (fun y i => W i y) x) +
        ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * b * B * (1 / (4 * η)) * (elemb_J d θ).toReal +
            (Fintype.card ι : ℝ) ^ 2 * b * B * √Λ * (1 + Ck ^ p)) *
          ∫⁻ x, ENNReal.ofReal (vnorm (fun i => W i x) ^ p) := by
  set c0 : ℝ := (Fintype.card ι : ℝ) ^ 2 * b * B with hc0
  have hc0nn : 0 ≤ c0 := by
    have := hK.nonneg
    positivity
  set Mv : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (vnorm (fun i => W i x) ^ p) with hMv
  have hJt := elemb_J_ne_top hd hθ2 (d := d)
  set Jr : ℝ := (elemb_J d θ).toReal with hJr
  have hJe : elemb_J d θ = ENNReal.ofReal Jr := (ENNReal.ofReal_toReal hJt).symm
  have hJnn : 0 ≤ Jr := ENNReal.toReal_nonneg
  set A : 𝔼 → ℝ≥0∞ := fun x => ENNReal.ofReal c0 * (ENNReal.ofReal η *
    (ENNReal.ofReal (μ x) * dissipationDensity d θ p (fun y i => W i y) x)) with hA
  set g : 𝔼 → ℝ≥0∞ := fun x => ENNReal.ofReal c0 *
    (ENNReal.ofReal (1 / (4 * η)) * (ENNReal.ofReal (elemb_V W x ^ p) * elemb_J d θ) +
      ENNReal.ofReal (√Λ) * (ENNReal.ofReal (elemb_V W x ^ p) + elemb_Gx θ W x ^ p)) with hg
  have hpt : ∀ x : 𝔼, ENNReal.ofReal |vnorm (fun i => W i x) ^ (p - 2) * ∑ i, W i x *
        (Real.sqrt (μ x) * ∑ j, Bm x i j * pvOdd d θ Ω (fun y => W j y) x)| ≤ A x + g x := fun x => by
    refine (elemb_pointwise hd hθ1 hθ2 hp hK hη hb0 μ Bm hμ hB W x).trans ?_
    rw [← hc0, mul_add]
  have hVm : Measurable fun x : 𝔼 => ENNReal.ofReal (elemb_V W x ^ p) :=
    ENNReal.measurable_ofReal.comp ((elemb_V_measurable W).pow_const p)
  have hGm : Measurable fun x : 𝔼 => elemb_Gx θ W x ^ p := (elemb_Gx_measurable θ W).pow_const p
  have hgm : Measurable g := by
    refine measurable_const.mul ?_
    exact (measurable_const.mul (hVm.mul measurable_const)).add (measurable_const.mul (hVm.add hGm))
  have h1 : ENNReal.ofReal |∫ x, vnorm (fun i => W i x) ^ (p - 2) * ∑ i, W i x *
        (Real.sqrt (μ x) * ∑ j, Bm x i j * pvOdd d θ Ω (fun y => W j y) x)| ≤
      ∫⁻ x, ENNReal.ofReal |vnorm (fun i => W i x) ^ (p - 2) * ∑ i, W i x *
        (Real.sqrt (μ x) * ∑ j, Bm x i j * pvOdd d θ Ω (fun y => W j y) x)| := by
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun x => ?_))
    exact Real.enorm_eq_ofReal_abs _
  refine h1.trans ((lintegral_mono hpt).trans ?_)
  rw [lintegral_add_right _ hgm]
  refine add_le_add ?_ ?_
  · simp only [hA]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← mul_assoc, ← ENNReal.ofReal_mul hc0nn]
  · simp only [hg]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hm1 : Measurable fun x : 𝔼 => ENNReal.ofReal (1 / (4 * η)) *
        (ENNReal.ofReal (elemb_V W x ^ p) * elemb_J d θ) := measurable_const.mul (hVm.mul measurable_const)
    rw [lintegral_add_left hm1]
    have e1 : ∫⁻ x : 𝔼, ENNReal.ofReal (1 / (4 * η)) * (ENNReal.ofReal (elemb_V W x ^ p) * elemb_J d θ) =
        ENNReal.ofReal (1 / (4 * η)) * (Mv * elemb_J d θ) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_mul_const' _ _ hJt]
      rfl
    have e2 : ∫⁻ x : 𝔼, ENNReal.ofReal (√Λ) * (ENNReal.ofReal (elemb_V W x ^ p) + elemb_Gx θ W x ^ p) =
        ENNReal.ofReal (√Λ) * (Mv + ∫⁻ x, elemb_Gx θ W x ^ p) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hVm]
      rfl
    rw [e1, e2]
    have hK' : ENNReal.ofReal (c0 * (1 / (4 * η)) * Jr + c0 * √Λ * (1 + Ck ^ p)) =
        ENNReal.ofReal c0 * ENNReal.ofReal (1 / (4 * η)) * ENNReal.ofReal Jr +
          ENNReal.ofReal c0 * ENNReal.ofReal (√Λ) * (1 + ENNReal.ofReal (Ck ^ p)) := by
      have hη' : 0 ≤ 1 / (4 * η) := by positivity
      have hs : 0 ≤ √Λ := Real.sqrt_nonneg _
      have hc : 0 ≤ Ck ^ p := Real.rpow_nonneg hCk _
      have t1 : ENNReal.ofReal (c0 * (1 / (4 * η)) * Jr) =
          ENNReal.ofReal c0 * ENNReal.ofReal (1 / (4 * η)) * ENNReal.ofReal Jr := by
        rw [ENNReal.ofReal_mul (mul_nonneg hc0nn hη'), ENNReal.ofReal_mul hc0nn]
      have t2 : ENNReal.ofReal (c0 * √Λ * (1 + Ck ^ p)) =
          ENNReal.ofReal c0 * ENNReal.ofReal (√Λ) * (1 + ENNReal.ofReal (Ck ^ p)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hc0nn hs), ENNReal.ofReal_mul hc0nn,
          ENNReal.ofReal_add zero_le_one hc, ENNReal.ofReal_one]
      rw [ENNReal.ofReal_add (mul_nonneg (mul_nonneg hc0nn hη') hJnn)
        (mul_nonneg (mul_nonneg hc0nn hs) (add_nonneg zero_le_one hc)), t1, t2]
    have hY' := hY W
    calc ENNReal.ofReal c0 * (ENNReal.ofReal (1 / (4 * η)) * (Mv * elemb_J d θ) +
          ENNReal.ofReal (√Λ) * (Mv + ∫⁻ x, elemb_Gx θ W x ^ p))
        ≤ ENNReal.ofReal c0 * (ENNReal.ofReal (1 / (4 * η)) * (Mv * ENNReal.ofReal Jr) +
          ENNReal.ofReal (√Λ) * (Mv + ENNReal.ofReal (Ck ^ p) * Mv)) := by
          rw [hJe]
          exact mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add le_rfl hY')))
      _ = _ := by rw [hK']; ring

end Tensor

/-- **`lp_tensor_absorption`** (S.A.15(iv)): the type of the frozen `HRS.Whole.AppendixA.lp_tensor_absorption`
(`AppendixAAdjoint.lean:953`), statement unchanged. -/
theorem lp_tensor_absorption_proof (hd : 1 ≤ d) (θ p : ℝ) (hθ1 : 1 < θ) (hθ2 : θ < 2) (hp : 2 ≤ p)
    (Ω : Euc d → ℝ) (hΩ : IsOddSmooth Ω) (Λ : ℝ) (ε : ℝ) (hε : 0 < ε) (ι : Type*) [Fintype ι] :
    ∃ C : ℝ, ∀ (μ : Euc d → ℝ) (B : Euc d → Matrix ι ι ℝ) (Bb : ℝ), (∀ x, 0 ≤ μ x ∧ μ x ≤ Λ) →
      (∀ x i j, |B x i j| ≤ Bb) → ∀ W : ι → SchwartzMap (Euc d) ℝ,
        ENNReal.ofReal |∫ x, vnorm (fun i => W i x) ^ (p - 2) *
            ∑ i, W i x * (Real.sqrt (μ x) * ∑ j, B x i j * pvOdd d θ Ω (fun y => W j y) x)| ≤
          ENNReal.ofReal ε * (∫⁻ x, ENNReal.ofReal (μ x) *
              dissipationDensity d θ p (fun y i => W i y) x) +
            ENNReal.ofReal (C * (1 + Bb ^ 2)) *
              ∫⁻ x, ENNReal.ofReal (vnorm (fun i => W i x) ^ p) := by
  obtain ⟨Bo, hK⟩ := isPvKernel_of_oddSmooth hΩ
  obtain ⟨Ck, hCk, hY⟩ := elemb_Gx_young (ι := ι) hd hθ1 (p := p) (by linarith)
  have hJt := elemb_J_ne_top hd hθ2 (d := d)
  set Jr : ℝ := (elemb_J d θ).toReal with hJr
  have hJnn : 0 ≤ Jr := ENNReal.toReal_nonneg
  set X : ℝ := (Fintype.card ι : ℝ) ^ 2 * Bo with hX
  have hXnn : 0 ≤ X := by
    have := hK.nonneg
    positivity
  have hsΛ : 0 ≤ √Λ := Real.sqrt_nonneg _
  have hCknn : 0 ≤ Ck ^ p := Real.rpow_nonneg hCk _
  refine ⟨(X ^ 2 + X) * Jr / (4 * ε) + X * √Λ * (1 + Ck ^ p), ?_⟩
  intro μ Bm Bb hμ hB W
  set b : ℝ := |Bb| with hb
  have hb0 : 0 ≤ b := abs_nonneg _
  have hB' : ∀ x i j, |Bm x i j| ≤ b := fun x i j => (hB x i j).trans (le_abs_self _)
  set c0 : ℝ := (Fintype.card ι : ℝ) ^ 2 * b * Bo with hc0
  have hc0X : c0 = X * b := by rw [hc0, hX]; ring
  have hc0nn : 0 ≤ c0 := by rw [hc0X]; positivity
  set η : ℝ := ε / (c0 + 1) with hη
  have hηpos : 0 < η := by positivity
  have hmain := elemb_integrated hd hθ1 hθ2 hp hK hηpos hb0 hCk (fun W' => hY W') μ Bm hμ hB' W
  refine hmain.trans (add_le_add ?_ ?_)
  · refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have : c0 * η ≤ ε := by
      rw [hη, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    simpa [hc0] using this
  · refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have h1η : 1 / (4 * η) = (c0 + 1) / (4 * ε) := by
      rw [hη]
      field_simp
    have hq : 0 ≤ 1 + b ^ 2 - b := by nlinarith [sq_nonneg (b - 1 / 2)]
    have hT : 0 ≤ Jr / (4 * ε) := by positivity
    have hS : 0 ≤ √Λ * (1 + Ck ^ p) := mul_nonneg hsΛ (by linarith)
    have hb2 : b ^ 2 = Bb ^ 2 := sq_abs Bb
    have e : (Fintype.card ι : ℝ) ^ 2 * b * Bo * (1 / (4 * η)) * Jr +
        (Fintype.card ι : ℝ) ^ 2 * b * Bo * √Λ * (1 + Ck ^ p) =
        X * b * (X * b + 1) * (Jr / (4 * ε)) + X * b * (√Λ * (1 + Ck ^ p)) := by
      rw [← hc0, hc0X, h1η]
      rw [hc0X]
      field_simp
    rw [e, ← hb2]
    have e2 : ((X ^ 2 + X) * Jr / (4 * ε) + X * √Λ * (1 + Ck ^ p)) * (1 + b ^ 2) -
        (X * b * (X * b + 1) * (Jr / (4 * ε)) + X * b * (√Λ * (1 + Ck ^ p))) =
        (Jr / (4 * ε)) * (X ^ 2 + X * (1 + b ^ 2 - b)) + X * (√Λ * (1 + Ck ^ p)) * (1 + b ^ 2 - b) := by
      ring
    have : 0 ≤ (Jr / (4 * ε)) * (X ^ 2 + X * (1 + b ^ 2 - b)) + X * (√Λ * (1 + Ck ^ p)) * (1 + b ^ 2 - b) := by
      have := mul_nonneg hXnn hq
      have := mul_nonneg hT (add_nonneg (sq_nonneg X) this)
      have := mul_nonneg (mul_nonneg hXnn hS) hq
      positivity
    linarith

end HRS.CZ.ElemB
