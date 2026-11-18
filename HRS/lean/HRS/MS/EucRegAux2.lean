import HRS.MS.EucRegAux1
import HRS.MS.LogReg

/-!
# C-REG-e (part 2): derivative bounds for `ρ = e^φ/Z` and the bootstrap in the thermal equation (`0 < s`, `s + 1 < d`)

Pure analysis on `ℝ^d`, namespace `HRS.MS.Thm`, helper prefix `rege_`.

* `rege_exponent_bound`: derivatives of `φ = -β (a‖x‖²/2 + U)` of order `1 ≤ i ≤ n` are `≤ C (1 + ‖x‖)`
  whenever those of `U` are bounded (the quadratic part has `‖D^i ‖x‖²‖ ≤ 2 (1 + ‖x‖)` for `i ≥ 1`).
* `rege_rho_deriv`: `ρ = e^φ/Z` with `ρ ≤ C₀ e^{-βa‖x‖²/2}` satisfies `‖D^j ρ‖ ≤ K (1+‖x‖)^j e^{-βa‖x‖²/2}`
  (Faà di Bruno for `exp ∘ φ`, `lreg_exp_deriv_bound`).
* `rege_bootstrap`: for a measurable `ρ` solving `ρ = exp(-β(a‖x‖²/2 + U))/Z`, `U = ∫ ‖x-y‖^{-s} ρ(y) dy`, `ρ ≤ C₀ e^{-βa‖x‖²/2}`,
  the potential `U` is `C^∞` with bounded derivatives of every positive order (induction on the order:
  `∇U = -s κ_s ⋆ ρ` by `rege_potential`, `κ_s ⋆ ρ ∈ C^k` by `lreg_conv_smooth`).
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace HRS.MS.Thm

open HRS HRS.Whole HRS.MS.LogReg

variable {d : ℕ}

/-! ### Polynomial times Gaussian -/

/-- `(1+r)^m e^{-b r²} ≤ C e^{-(b/2) r²}`. -/
lemma rege_poly_gauss {b : ℝ} (hb : 0 < b) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r → (1 + r) ^ m * Real.exp (-b * r ^ 2) ≤ C * Real.exp (-(b / 2) * r ^ 2) := by
  obtain ⟨C1, hC1, hC1b⟩ := cb_rpow_le_exp (p := (m : ℝ)) (b := b / 4) (by positivity) (by positivity)
  refine ⟨C1 * Real.exp (2 * (b / 4)), by positivity, fun r hr => ?_⟩
  have h1 : (1 + r) ^ m ≤ C1 * Real.exp (b / 4 * (1 + r) ^ 2) := by
    have := hC1b (1 + r) (by positivity)
    rwa [Real.rpow_natCast] at this
  have h2 : (1 + r) ^ 2 ≤ 2 + 2 * r ^ 2 := by nlinarith [sq_nonneg (1 - r)]
  have h3 : Real.exp (b / 4 * (1 + r) ^ 2) ≤
      Real.exp (2 * (b / 4)) * Real.exp (2 * (b / 4) * r ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : 0 ≤ b / 4 := by positivity
    nlinarith
  calc (1 + r) ^ m * Real.exp (-b * r ^ 2)
      ≤ (C1 * (Real.exp (2 * (b / 4)) * Real.exp (2 * (b / 4) * r ^ 2))) * Real.exp (-b * r ^ 2) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h3 hC1.le)
    _ = C1 * Real.exp (2 * (b / 4)) * Real.exp (-(b / 2) * r ^ 2) := by
        have : Real.exp (2 * (b / 4) * r ^ 2) * Real.exp (-b * r ^ 2) = Real.exp (-(b / 2) * r ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
        calc C1 * (Real.exp (2 * (b / 4)) * Real.exp (2 * (b / 4) * r ^ 2)) * Real.exp (-b * r ^ 2)
            = C1 * Real.exp (2 * (b / 4)) * (Real.exp (2 * (b / 4) * r ^ 2) * Real.exp (-b * r ^ 2)) := by
              ring
          _ = _ := by rw [this]

/-- Bounded: `(1+r)^m e^{-b r²} ≤ C`. -/
lemma rege_poly_gauss_bdd {b : ℝ} (hb : 0 < b) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r → (1 + r) ^ m * Real.exp (-b * r ^ 2) ≤ C := by
  obtain ⟨C, hC, h⟩ := rege_poly_gauss hb m
  refine ⟨C, hC, fun r hr => (h r hr).trans ?_⟩
  have : Real.exp (-(b / 2) * r ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg r]
  nlinarith

/-- Integrable: `x ↦ (1+‖x‖)^m e^{-b‖x‖²}`. -/
lemma rege_poly_gauss_integrable {b : ℝ} (hb : 0 < b) (m : ℕ) :
    Integrable (fun x : Euc d => (1 + ‖x‖) ^ m * Real.exp (-b * ‖x‖ ^ 2)) := by
  obtain ⟨C, hC, h⟩ := rege_poly_gauss hb m
  refine ((cb_integrable_gauss (d := d) (c := b / 2) (by positivity)).const_mul C).mono' ?_
    (ae_of_all _ fun x => ?_)
  · exact (((measurable_const.add measurable_norm).pow_const m).mul
      (Real.measurable_exp.comp ((measurable_norm.pow_const 2).const_mul _))).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact h _ (norm_nonneg x)

/-! ### Derivatives of the exponent -/

lemma rege_fderiv_normsq :
    fderiv ℝ (fun x : Euc d => ‖x‖ ^ 2) = fun x => (2 : ℝ) • (innerSL ℝ x : Euc d →L[ℝ] ℝ) := by
  funext x
  rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  ext w
  simp [two_smul]

lemma rege_normsq_deriv_bound {i : ℕ} (hi : 1 ≤ i) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (fun x : Euc d => ‖x‖ ^ 2) x‖ ≤ 2 * (1 + ‖x‖) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv, rege_fderiv_normsq]
  have hc : ContDiffAt ℝ m (fun x : Euc d => (innerSL ℝ x : Euc d →L[ℝ] ℝ)) x :=
    (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).contDiff.contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hc, norm_smul]
  have := lreg_T_bound m x
  rw [Real.norm_eq_abs, abs_two]
  gcongr

lemma rege_exponent_bound (a β : ℝ) {U : Euc d → ℝ} {n : ℕ} (hU : ContDiff ℝ n U) {M : ℝ} (hM : 0 ≤ M)
    (hUb : ∀ i, 1 ≤ i → i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i U x‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, 1 ≤ i → i ≤ n → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + U x)) x‖ ≤ C * (1 + ‖x‖) := by
  refine ⟨|(-β * a / 2)| * 2 + |(-β)| * M, by positivity, fun i hi hin x => ?_⟩
  have hqd : ContDiff ℝ n (fun x : Euc d => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hfun : (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + U x)) =
      (fun x : Euc d => (-β * a / 2) • ‖x‖ ^ 2) + (fun x => (-β) • U x) := by
    funext x; simp only [Pi.add_apply, smul_eq_mul]; ring
  have hx1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hqi : ContDiffAt ℝ i (fun x : Euc d => ‖x‖ ^ 2) x :=
    (hqd.of_le (by exact_mod_cast hin)).contDiffAt
  have hUi : ContDiffAt ℝ i U x := (hU.of_le (by exact_mod_cast hin)).contDiffAt
  rw [hfun, iteratedFDeriv_add_apply (hqi.const_smul _) (hUi.const_smul _),
    iteratedFDeriv_const_smul_apply' hqi, iteratedFDeriv_const_smul_apply' hUi]
  calc ‖(-β * a / 2) • iteratedFDeriv ℝ i (fun x : Euc d => ‖x‖ ^ 2) x +
        (-β) • iteratedFDeriv ℝ i U x‖
      ≤ ‖(-β * a / 2) • iteratedFDeriv ℝ i (fun x : Euc d => ‖x‖ ^ 2) x‖ +
        ‖(-β) • iteratedFDeriv ℝ i U x‖ := norm_add_le _ _
    _ ≤ |(-β * a / 2)| * (2 * (1 + ‖x‖)) + |(-β)| * M := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
        · exact rege_normsq_deriv_bound hi x
        · exact hUb i hi hin x
    _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hx1 (mul_nonneg (abs_nonneg (-β)) hM)
        nlinarith [h, abs_nonneg (-β * a / 2)]

/-- Derivative bounds for `ρ = e^φ/Z` with the Gaussian envelope. -/
lemma rege_rho_deriv {a β Z C0 : ℝ} (hZ : 0 < Z) {ρ φ : Euc d → ℝ}
    (hρ : ∀ x, ρ x = Real.exp (φ x) / Z) (hup : ∀ x, ρ x ≤ C0 * Real.exp (-β * a * ‖x‖ ^ 2 / 2))
    {n : ℕ} (hφ : ContDiff ℝ n φ) {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ C * (1 + ‖x‖)) :
    ContDiff ℝ n ρ ∧ ∀ j ≤ n, ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
      ‖iteratedFDeriv ℝ j ρ x‖ ≤ K * (1 + ‖x‖) ^ j * Real.exp (-β * a * ‖x‖ ^ 2 / 2) := by
  have hρeq : ρ = fun x => Z⁻¹ • Real.exp (φ x) :=
    funext fun x => by rw [hρ x, smul_eq_mul, div_eq_inv_mul]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hρeq]; exact (Real.contDiff_exp.comp hφ).const_smul Z⁻¹
  · have hφj : ContDiff ℝ j φ := hφ.of_le (by exact_mod_cast hj)
    refine ⟨(Nat.factorial j : ℝ) * max C0 0 * (max C 1) ^ j, by positivity, fun x => ?_⟩
    have hx1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    set D : ℝ := max C 1 * (1 + ‖x‖) with hDdef
    have hD1 : 1 ≤ D := by
      have : (1 : ℝ) ≤ max C 1 := le_max_right _ _
      nlinarith
    have hDi : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i φ x‖ ≤ D ^ i := fun i hi hij =>
      calc _ ≤ C * (1 + ‖x‖) := hD i hi (hij.trans hj) x
        _ ≤ D := by rw [hDdef]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
        _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)
    have hb := lreg_exp_deriv_bound hφj x hDi
    have hρj : iteratedFDeriv ℝ j ρ x = Z⁻¹ • iteratedFDeriv ℝ j (fun y => Real.exp (φ y)) x := by
      rw [hρeq]; exact iteratedFDeriv_const_smul_apply' (Real.contDiff_exp.comp hφj).contDiffAt
    have hn : ‖iteratedFDeriv ℝ j ρ x‖ ≤ (Nat.factorial j : ℝ) * ρ x * D ^ j := by
      rw [hρj, norm_smul, norm_inv, Real.norm_of_nonneg hZ.le, hρ x]
      calc Z⁻¹ * ‖iteratedFDeriv ℝ j (fun y => Real.exp (φ y)) x‖
          ≤ Z⁻¹ * ((Nat.factorial j : ℝ) * Real.exp (φ x) * D ^ j) :=
            mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hZ.le)
        _ = _ := by ring
    have hρx : ρ x ≤ max C0 0 * Real.exp (-β * a * ‖x‖ ^ 2 / 2) :=
      (hup x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hDj : D ^ j = (max C 1) ^ j * (1 + ‖x‖) ^ j := by rw [hDdef, mul_pow]
    calc ‖iteratedFDeriv ℝ j ρ x‖ ≤ (Nat.factorial j : ℝ) * ρ x * D ^ j := hn
      _ ≤ (Nat.factorial j : ℝ) * (max C0 0 * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) * D ^ j := by
          gcongr
      _ = _ := by rw [hDj]; ring

/-- Rapid decay from the Gaussian envelope. -/
lemma rege_rdec_of_gauss {b : ℝ} (hb : 0 < b) {G : Type*} [NormedAddCommGroup G] {F : Euc d → G} {j : ℕ}
    {K : ℝ} (hK : 0 ≤ K) (h : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖) ^ j * Real.exp (-b * ‖x‖ ^ 2)) :
    lreg_RDec F := by
  intro N
  obtain ⟨C, hC, hCb⟩ := rege_poly_gauss_bdd hb (N + j)
  refine ⟨K * C, fun x => ?_⟩
  calc (1 + ‖x‖) ^ N * ‖F x‖ ≤ (1 + ‖x‖) ^ N * (K * (1 + ‖x‖) ^ j * Real.exp (-b * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (h x) (by positivity)
    _ = K * ((1 + ‖x‖) ^ (N + j) * Real.exp (-b * ‖x‖ ^ 2)) := by rw [pow_add]; ring
    _ ≤ K * C := mul_le_mul_of_nonneg_left (hCb _ (norm_nonneg x)) hK

lemma rege_exp_form {a β : ℝ} (x : Euc d) :
    Real.exp (-β * a * ‖x‖ ^ 2 / 2) = Real.exp (-(β * a / 2) * ‖x‖ ^ 2) := by
  congr 1; ring


lemma rege_W_eq_conv (s : ℝ) (F : Euc d → ℝ) :
    rege_W s F = lreg_conv ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euc d →L[ℝ] Euc d).flip)
      (rege_kap s) F := by
  funext x
  unfold rege_W lreg_conv
  have := integral_sub_left_eq_self (fun z : Euc d => F (x - z) • rege_kap s z) volume x
  simp only [sub_sub_cancel] at this
  rw [this]
  rfl

lemma rege_L_opnorm {s : ℝ} (hs : 0 ≤ s) : ‖(rege_L s : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)‖ ≤ s := by
  unfold rege_L
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [norm_neg, Real.norm_of_nonneg hs]
  have := norm_innerSL_le (𝕜 := ℝ) (E := Euc d)
  nlinarith

/-- **Bootstrap in the thermal equation**: the potential `U = ∫ ‖x-y‖^{-s} ρ(y) dy` is `C^∞`, with bounded
derivatives of every positive order. -/
theorem rege_bootstrap {s θ a β Z C0 : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθd : s + 1 + θ < d) (ha : 0 < a) (hβ : 0 < β) (hZ : 0 < Z) {ρ : Euc d → ℝ}
    (hm : Measurable ρ)
    (heq : ∀ x, ρ x = Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + rege_U s ρ x)) / Z)
    (hup : ∀ x, ρ x ≤ C0 * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) :
    ∀ k : ℕ, ContDiff ℝ k (rege_U s ρ) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      ‖iteratedFDeriv ℝ i (rege_U s ρ) x‖ ≤ M := by
  have hσ : s + 1 < d := by linarith
  have hb2 : 0 < β * a / 2 := by positivity
  have hρpos : ∀ x, 0 < ρ x := fun x => by rw [heq x]; positivity
  have hdec : lreg_RDec ρ := by
    refine rege_rdec_of_gauss (j := 0) hb2 (K := max C0 0) (le_max_right _ _) (fun x => ?_)
    rw [Real.norm_of_nonneg (hρpos x).le, pow_zero, mul_one, ← rege_exp_form]
    exact (hup x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  obtain ⟨hWc, hderiv, hWb⟩ := rege_potential hd1 hs hθ0 hθ1 hθd hm.aestronglyMeasurable hdec
  have hfd : fderiv ℝ (rege_U s ρ) = fun x => rege_L s (rege_W s ρ x) :=
    funext fun x => (hderiv x).fderiv
  have hdiff : Differentiable ℝ (rege_U s ρ) := fun x => (hderiv x).differentiableAt
  obtain ⟨Cb, hCb, h0⟩ := lreg_bound_of_rdec hdec 0
  have hQ1 : ContDiff ℝ 1 (rege_U s ρ) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ i, 1 ≤ i → i ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ i (rege_U s ρ) x‖ ≤ M := by
    refine ⟨contDiff_one_iff_fderiv.2 ⟨hdiff, by rw [hfd]; exact (rege_L s).continuous.comp hWc⟩,
      s * (Cb * lreg_A d (s + 1)), mul_nonneg hs.le (mul_nonneg hCb lreg_A_nonneg), fun i hi hi1 x => ?_⟩
    obtain rfl : i = 1 := le_antisymm hi1 hi
    rw [norm_iteratedFDeriv_one, hfd, rege_L_norm hs.le]
    exact mul_le_mul_of_nonneg_left (hWb Cb hCb (fun y => by simpa using h0 y) x) hs.le
  have hstep : ∀ k : ℕ, 1 ≤ k → (ContDiff ℝ k (rege_U s ρ) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      ‖iteratedFDeriv ℝ i (rege_U s ρ) x‖ ≤ M) →
      (ContDiff ℝ (k + 1 : ℕ) (rege_U s ρ) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ x,
      ‖iteratedFDeriv ℝ i (rege_U s ρ) x‖ ≤ M) := by
    intro k hk ⟨hUk, M, hM0, hM⟩
    obtain ⟨C, hC, hD⟩ := rege_exponent_bound a β hUk hM0 hM
    have hφ : ContDiff ℝ k (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + rege_U s ρ x)) :=
      contDiff_const.mul (((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2).add hUk)
    obtain ⟨hρk, hρD⟩ := rege_rho_deriv hZ heq hup hφ hC hD
    have hρdec : ∀ j ≤ k, lreg_RDec (iteratedFDeriv ℝ j ρ) := by
      intro j hj
      obtain ⟨K, hK, hKb⟩ := hρD j hj
      refine rege_rdec_of_gauss (j := j) hb2 hK (fun x => ?_)
      rw [← rege_exp_form]; exact hKb x
    obtain ⟨Ck, hCk, hbk⟩ := lreg_bound_of_rdec (hρdec k le_rfl) 0
    set B : Euc d →L[ℝ] ℝ →L[ℝ] Euc d :=
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euc d →L[ℝ] Euc d).flip with hBdef
    have hB : ∀ v w, ‖B v w‖ ≤ 1 * ‖v‖ * ‖w‖ := by
      intro v w
      simp [hBdef, norm_smul, mul_comm]
    obtain ⟨hWk, hWbk⟩ := lreg_conv_smooth hd1 hσ (by linarith)
      (rege_kap_measurable s).aestronglyMeasurable (rege_kap_norm_le s) k B zero_le_one hB hρk hρdec
    rw [← rege_W_eq_conv] at hWk hWbk
    have hbound := hWbk Ck hCk (fun y => by simpa using hbk y)
    refine ⟨?_, max M (s * (1 * (Ck * lreg_A d (s + 1)))), le_max_of_le_right (by
      have := lreg_A_nonneg (d := d) (σ := s + 1); positivity), fun i hi hik x => ?_⟩
    · have hc : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hc, contDiff_succ_iff_fderiv]
      refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
      rw [hfd]
      exact (rege_L s).contDiff.comp hWk
    · rcases Nat.lt_or_ge i (k + 1) with hlt | hge
      · exact (hM i hi (by omega) x).trans (le_max_left _ _)
      · obtain rfl : i = k + 1 := le_antisymm hik hge
        refine le_trans ?_ (le_max_right _ _)
        rw [← norm_iteratedFDeriv_fderiv, hfd]
        have h1 := (rege_L s : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
          (f := rege_W s ρ) (x := x) (n := k) hWk.contDiffAt (by exact_mod_cast le_rfl)
        calc _ ≤ ‖(rege_L s : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ k (rege_W s ρ) x‖ := h1
          _ ≤ s * (1 * (Ck * lreg_A d (s + 1))) := by
              gcongr
              · exact rege_L_opnorm hs.le
              · exact hbound x
  intro k
  by_cases hk : 1 ≤ k
  · exact Nat.le_induction hQ1 (fun k hk ih => hstep k hk ih) k hk
  · refine ⟨hQ1.1.of_le (by exact_mod_cast (by omega : k ≤ 1)), 0, le_rfl, fun i hi hik => ?_⟩
    omega

end HRS.MS.Thm

end
