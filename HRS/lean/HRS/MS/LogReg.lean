import HRS.MS.LogRegAux2
import HRS.MS.CanThmAux1
import HRS.MS.ThmConsAux2
import HRS.MS.LogBnd

/-!
# C8: proof of `HRS.Whole.logThermal_regularity`

Namespace `HRS.MS.LogReg`, helper prefix `lreg_`.  No statement was adjusted.

* `lreg_bootstrap`: for a measurable, rapidly decaying `ρ` solving `ρ = exp(-β(a‖x‖²/2 + U))/Z` with
  `U = ∫ -log‖x-y‖ ρ(y) dy` (`d ≥ 2`), `U` is `C^∞` with bounded derivatives of every positive order.
  Induction on the order: `U ∈ C¹` (`lreg_potential`, `∇U = κ ⋆ ρ`), the derivatives of `ρ = e^φ/Z` decay
  rapidly (Faà di Bruno for `exp ∘ φ`, `lreg_rho_decay`), hence `κ ⋆ ρ ∈ C^k` (`lreg_conv_smooth`), hence `U ∈ C^{k+1}`.
* `lreg_l_bound`: all derivatives of positive order of `½ log (1 + ‖x‖²)` are bounded (via `ψ = (1+‖x‖²)⁻¹`,
  `‖D^n ψ‖ ≤ K ψ`).
* `lreg_UL_bound`: `U + ½ log (1 + ‖x‖²)` is bounded (two-sided bounds `LogBnd` and the thermal equation).
* `logThermal_regularity_proof : type_of% @HRS.Whole.logThermal_regularity`.
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace HRS.MS.LogReg

open HRS HRS.Whole HRS.MS.Thm HRS.MS.Can2

variable {d : ℕ}

/-- `n`-th derivative of `exp ∘ f`. -/
lemma lreg_exp_deriv_bound {f : Euc d → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) (x : Euc d) {D : ℝ}
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (fun y => Real.exp (f y)) x‖ ≤ (Nat.factorial n : ℝ) * Real.exp (f x) * D ^ n := by
  have h := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := Real.exp) (f := f) (N := n) (n := n)
    Real.contDiff_exp hf le_rfl x (C := Real.exp (f x)) (D := D) ?_ hD
  · exact h
  · intro i _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.norm_of_nonneg (Real.exp_pos _).le]

/-- Smoothness and rapid decay of the derivatives of `ρ = e^φ / Z`. -/
lemma lreg_rho_decay {ρ φ : Euc d → ℝ} {Z : ℝ} (hZ : 0 < Z)
    (hρ : ∀ x, ρ x = Real.exp (φ x) / Z) (hdec : lreg_RDec ρ) {n : ℕ} (hφ : ContDiff ℝ n φ)
    {k0 : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ C * (1 + ‖x‖) ^ k0) :
    ContDiff ℝ n ρ ∧ ∀ j ≤ n, lreg_RDec (iteratedFDeriv ℝ j ρ) := by
  have hρeq : ρ = fun x => Z⁻¹ • Real.exp (φ x) :=
    funext fun x => by rw [hρ x, smul_eq_mul, div_eq_inv_mul]
  refine ⟨?_, fun j hj N => ?_⟩
  · rw [hρeq]; exact (Real.contDiff_exp.comp hφ).const_smul Z⁻¹
  · have hφj : ContDiff ℝ j φ := hφ.of_le (by exact_mod_cast hj)
    obtain ⟨C0, hC0⟩ := hdec (N + k0 * j)
    refine ⟨(Nat.factorial j : ℝ) * (1 + C) ^ j * max C0 0, fun x => ?_⟩
    have hx1 : 1 ≤ (1 + ‖x‖) ^ k0 := one_le_pow₀ (by linarith [norm_nonneg x])
    set D : ℝ := (1 + C) * (1 + ‖x‖) ^ k0 with hDdef
    have hD1 : 1 ≤ D := by nlinarith
    have hDi : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i φ x‖ ≤ D ^ i := fun i hi hij =>
      calc _ ≤ C * (1 + ‖x‖) ^ k0 := hD i hi (hij.trans hj) x
        _ ≤ D := by rw [hDdef]; nlinarith
        _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)
    have hb := lreg_exp_deriv_bound hφj x hDi
    have hρj : iteratedFDeriv ℝ j ρ x = Z⁻¹ • iteratedFDeriv ℝ j (fun y => Real.exp (φ y)) x := by
      rw [hρeq]; exact iteratedFDeriv_const_smul_apply' (Real.contDiff_exp.comp hφj).contDiffAt
    have hρpos : 0 < ρ x := by rw [hρ x]; positivity
    have hn : ‖iteratedFDeriv ℝ j ρ x‖ ≤ (Nat.factorial j : ℝ) * ρ x * D ^ j := by
      rw [hρj, norm_smul, norm_inv, Real.norm_of_nonneg hZ.le, hρ x]
      calc Z⁻¹ * ‖iteratedFDeriv ℝ j (fun y => Real.exp (φ y)) x‖
          ≤ Z⁻¹ * ((Nat.factorial j : ℝ) * Real.exp (φ x) * D ^ j) :=
            mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hZ.le)
        _ = _ := by ring
    have hDj : D ^ j = (1 + C) ^ j * (1 + ‖x‖) ^ (k0 * j) := by
      rw [hDdef, mul_pow, ← pow_mul]
    have hCx := hC0 x
    rw [Real.norm_of_nonneg hρpos.le, pow_add] at hCx
    calc (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j ρ x‖
        ≤ (1 + ‖x‖) ^ N * ((Nat.factorial j : ℝ) * ρ x * ((1 + C) ^ j * (1 + ‖x‖) ^ (k0 * j))) := by
          rw [← hDj]; exact mul_le_mul_of_nonneg_left hn (by positivity)
      _ = (Nat.factorial j : ℝ) * (1 + C) ^ j * ((1 + ‖x‖) ^ N * (1 + ‖x‖) ^ (k0 * j) * ρ x) := by ring
      _ ≤ (Nat.factorial j : ℝ) * (1 + C) ^ j * max C0 0 := by
          gcongr
          exact hCx.trans (le_max_left _ _)

/-- Polynomial bounds for the derivatives of the exponent `φ = -β (a‖x‖²/2 + U)`. -/
lemma lreg_exponent_bound (a β : ℝ) {U : Euc d → ℝ} {n : ℕ} (hU : ContDiff ℝ n U) {M : ℝ} (hM : 0 ≤ M)
    (hUb : ∀ i, 1 ≤ i → i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i U x‖ ≤ M) :
    ∃ (k0 : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ i, 1 ≤ i → i ≤ n → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + U x)) x‖ ≤
        C * (1 + ‖x‖) ^ k0 := by
  obtain ⟨k0, Cq, hCq, hq⟩ :=
    (Function.hasTemperateGrowth_norm_sq (Euc d)).norm_iteratedFDeriv_le_uniform n
  refine ⟨k0, |(-β * a / 2)| * Cq + |(-β)| * M, by positivity, fun i hi hin x => ?_⟩
  have hqd : ContDiff ℝ n (fun x : Euc d => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hfun : (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + U x)) =
      (fun x : Euc d => (-β * a / 2) • ‖x‖ ^ 2) + (fun x => (-β) • U x) := by
    funext x; simp only [Pi.add_apply, smul_eq_mul]; ring
  have hx1 : 1 ≤ (1 + ‖x‖) ^ k0 := one_le_pow₀ (by linarith [norm_nonneg x])
  have hqi : ContDiffAt ℝ i (fun x : Euc d => ‖x‖ ^ 2) x :=
    (hqd.of_le (by exact_mod_cast hin)).contDiffAt
  have hUi : ContDiffAt ℝ i U x := (hU.of_le (by exact_mod_cast hin)).contDiffAt
  rw [hfun, iteratedFDeriv_add_apply (hqi.const_smul _) (hUi.const_smul _),
    iteratedFDeriv_const_smul_apply' hqi, iteratedFDeriv_const_smul_apply' hUi]
  calc ‖(-β * a / 2) • iteratedFDeriv ℝ i (fun x : Euc d => ‖x‖ ^ 2) x +
        (-β) • iteratedFDeriv ℝ i U x‖
      ≤ ‖(-β * a / 2) • iteratedFDeriv ℝ i (fun x : Euc d => ‖x‖ ^ 2) x‖ +
        ‖(-β) • iteratedFDeriv ℝ i U x‖ := norm_add_le _ _
    _ ≤ |(-β * a / 2)| * (Cq * (1 + ‖x‖) ^ k0) + |(-β)| * M := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
        · exact hq i hin x
        · exact hUb i hi hin x
    _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hx1 (mul_nonneg (abs_nonneg (-β)) hM)
        nlinarith [h]

lemma lreg_W_eq_conv (F : Euc d → ℝ) :
    lreg_W F = lreg_conv ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euc d →L[ℝ] Euc d).flip)
      lreg_kap F := by
  funext x
  unfold lreg_W lreg_conv
  have := integral_sub_left_eq_self (fun z : Euc d => F (x - z) • lreg_kap z) volume x
  simp only [sub_sub_cancel] at this
  rw [this]
  rfl

/-- Bootstrap in the thermal equation: the potential `U = ∫ -log‖x-y‖ ρ(y) dy` is `C^∞`, with bounded
derivatives of every positive order. -/
theorem lreg_bootstrap (hd2 : 2 ≤ d) {a β Z : ℝ} (hZ : 0 < Z) {ρ : Euc d → ℝ}
    (hm : Measurable ρ) (hdec : lreg_RDec ρ)
    (heq : ∀ x, ρ x = Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + lreg_U ρ x)) / Z) :
    ∀ k : ℕ, ContDiff ℝ k (lreg_U ρ) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      ‖iteratedFDeriv ℝ i (lreg_U ρ) x‖ ≤ M := by
  have hd1 : 1 ≤ d := by omega
  have hσ : (1 : ℝ) < d := by exact_mod_cast hd2
  obtain ⟨hWc, hderiv, hWb⟩ := lreg_potential hd2 hm.aestronglyMeasurable hdec
  have hfd : fderiv ℝ (lreg_U ρ) = fun x => innerSL ℝ (lreg_W ρ x) :=
    funext fun x => (hderiv x).fderiv
  have hdiff : Differentiable ℝ (lreg_U ρ) := fun x => (hderiv x).differentiableAt
  obtain ⟨C0, hC0, h0⟩ := lreg_bound_of_rdec hdec 0
  have hQ1 : ContDiff ℝ 1 (lreg_U ρ) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ i, 1 ≤ i → i ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ i (lreg_U ρ) x‖ ≤ M := by
    refine ⟨contDiff_one_iff_fderiv.2 ⟨hdiff, by rw [hfd]; exact (innerSL ℝ).continuous.comp hWc⟩,
      C0 * lreg_A d 1, mul_nonneg hC0 lreg_A_nonneg, fun i hi hi1 x => ?_⟩
    obtain rfl : i = 1 := le_antisymm hi1 hi
    rw [norm_iteratedFDeriv_one, hfd, innerSL_apply_norm]
    exact hWb C0 hC0 (fun y => by simpa using h0 y) x
  have hstep : ∀ k : ℕ, 1 ≤ k → (ContDiff ℝ k (lreg_U ρ) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      ‖iteratedFDeriv ℝ i (lreg_U ρ) x‖ ≤ M) →
      (ContDiff ℝ (k + 1 : ℕ) (lreg_U ρ) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ x,
      ‖iteratedFDeriv ℝ i (lreg_U ρ) x‖ ≤ M) := by
    intro k hk ⟨hUk, M, hM0, hM⟩
    obtain ⟨k0, C, hC, hD⟩ := lreg_exponent_bound a β hUk hM0 hM
    have hφ : ContDiff ℝ k (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + lreg_U ρ x)) :=
      contDiff_const.mul (((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2).add hUk)
    obtain ⟨hρk, hρdec⟩ := lreg_rho_decay hZ heq hdec hφ hC hD
    obtain ⟨Ck, hCk, hbk⟩ := lreg_bound_of_rdec (hρdec k le_rfl) 0
    set B : Euc d →L[ℝ] ℝ →L[ℝ] Euc d :=
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euc d →L[ℝ] Euc d).flip with hBdef
    have hB : ∀ v w, ‖B v w‖ ≤ 1 * ‖v‖ * ‖w‖ := by
      intro v w
      simp [hBdef, norm_smul, mul_comm]
    obtain ⟨hWk, hWbk⟩ := lreg_conv_smooth hd1 hσ zero_le_one lreg_kap_measurable.aestronglyMeasurable
      lreg_kap_le k B zero_le_one hB hρk hρdec
    rw [← lreg_W_eq_conv] at hWk hWbk
    have hbound := hWbk Ck hCk (fun y => by simpa using hbk y)
    refine ⟨?_, max M (1 * (Ck * lreg_A d 1)), le_max_of_le_right (by
      have := lreg_A_nonneg (d := d) (σ := 1); positivity), fun i hi hik x => ?_⟩
    · have hc : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hc, contDiff_succ_iff_fderiv]
      refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
      rw [hfd]
      exact (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).contDiff.comp hWk
    · rcases Nat.lt_or_ge i (k + 1) with hlt | hge
      · exact (hM i hi (by omega) x).trans (le_max_left _ _)
      · obtain rfl : i = k + 1 := le_antisymm hik hge
        refine le_trans ?_ (le_max_right _ _)
        rw [← norm_iteratedFDeriv_fderiv, hfd]
        have h1 := (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
          (f := lreg_W ρ) (x := x) (n := k) hWk.contDiffAt (by exact_mod_cast le_rfl)
        have h2 : ‖(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)‖ ≤ 1 := norm_innerSL_le ℝ
        calc _ ≤ ‖(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ k (lreg_W ρ) x‖ := h1
          _ ≤ 1 * (1 * (Ck * lreg_A d 1)) := by
              gcongr
              · exact hbound x
          _ = _ := by ring
  intro k
  by_cases hk : 1 ≤ k
  · exact Nat.le_induction hQ1 (fun k hk ih => hstep k hk ih) k hk
  · refine ⟨hQ1.1.of_le (by exact_mod_cast (by omega : k ≤ 1)), 0, le_rfl, fun i hi hik => ?_⟩
    omega

/-! ### Bounded derivatives of `½ log (1 + ‖x‖²)` -/

/-- `ψ(x) = (1 + ‖x‖²)⁻¹`. -/
def lreg_psi (x : Euc d) : ℝ := (1 + ‖x‖ ^ 2)⁻¹

lemma lreg_psi_pos (x : Euc d) : 0 < lreg_psi x := by unfold lreg_psi; positivity

lemma lreg_psi_contDiff {n : ℕ∞ω} : ContDiff ℝ n (lreg_psi : Euc d → ℝ) := by
  unfold lreg_psi
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).inv (fun x => by positivity)

lemma lreg_psi_mul_le (x : Euc d) : lreg_psi x * (1 + ‖x‖) ≤ 2 := by
  unfold lreg_psi
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (‖x‖ - 1 / 4), norm_nonneg x]

lemma lreg_psi_fderiv (x : Euc d) :
    fderiv ℝ (lreg_psi : Euc d → ℝ) x = (-2 * lreg_psi x ^ 2) • innerSL ℝ x := by
  have h1 : HasFDerivAt (fun x : Euc d => 1 + ‖x‖ ^ 2) (2 • innerSL ℝ x) x :=
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_add 1
  have hne : (1 + ‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have h2 := (hasDerivAt_inv hne).comp_hasFDerivAt x h1
  have h3 : fderiv ℝ (lreg_psi : Euc d → ℝ) x =
      (-((1 + ‖x‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ x) := h2.fderiv
  rw [h3]
  unfold lreg_psi
  ext w
  simp
  ring

lemma lreg_T_bound (m : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ m (fun x : Euc d => (innerSL ℝ x : Euc d →L[ℝ] ℝ)) x‖ ≤ 1 + ‖x‖ := by
  rcases m with _ | m
  · rw [norm_iteratedFDeriv_zero, innerSL_apply_norm]; linarith
  · rw [← norm_iteratedFDeriv_fderiv]
    have hf : fderiv ℝ (fun x : Euc d => (innerSL ℝ x : Euc d →L[ℝ] ℝ)) =
        fun _ => (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) := by
      funext y; exact (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).fderiv
    rw [hf]
    rcases m with _ | m
    · rw [norm_iteratedFDeriv_zero]
      have := norm_innerSL_le (𝕜 := ℝ) (E := Euc d)
      linarith [norm_nonneg x]
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero m)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

lemma lreg_psi_bound (n : ℕ) : ∃ K : ℝ, 1 ≤ K ∧ ∀ j ≤ n, ∀ x : Euc d,
    ‖iteratedFDeriv ℝ j (lreg_psi : Euc d → ℝ) x‖ ≤ K * lreg_psi x := by
  induction n with
  | zero =>
    refine ⟨1, le_rfl, fun j hj x => ?_⟩
    obtain rfl : j = 0 := by omega
    rw [norm_iteratedFDeriv_zero, Real.norm_of_nonneg (lreg_psi_pos x).le, one_mul]
  | succ n ih =>
    obtain ⟨K, hK1, hK⟩ := ih
    refine ⟨max K (4 ^ (n + 1) * K ^ 2), le_max_of_le_left hK1, fun j hj x => ?_⟩
    rcases Nat.lt_or_ge j (n + 1) with hlt | hge
    · exact (hK j (by omega) x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (lreg_psi_pos x).le)
    obtain rfl : j = n + 1 := le_antisymm hj hge
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (lreg_psi_pos x).le)
    have hψ0 := lreg_psi_pos x
    -- derivatives of `s = -2 ψ²`
    have hs : ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun y : Euc d => -2 * lreg_psi y ^ 2) x‖ ≤
        2 * 2 ^ i * K ^ 2 * lreg_psi x ^ 2 := by
      intro i hi
      have hfun : (fun y : Euc d => -2 * lreg_psi y ^ 2) = fun y => (-2 : ℝ) • (lreg_psi y * lreg_psi y) := by
        funext y; simp [smul_eq_mul, sq]
      have hmul : ContDiff ℝ i (fun y : Euc d => lreg_psi y * lreg_psi y) :=
        lreg_psi_contDiff.mul lreg_psi_contDiff
      rw [hfun, iteratedFDeriv_const_smul_apply' hmul.contDiffAt, norm_smul]
      have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (i : ℕ∞ω)) (lreg_psi_contDiff (n := i))
        (lreg_psi_contDiff (n := i)) x (n := i) le_rfl
      have h2 : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j lreg_psi x‖ *
          ‖iteratedFDeriv ℝ (i - j) lreg_psi x‖ ≤ 2 ^ i * (K * lreg_psi x) ^ 2 := by
        calc _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (K * lreg_psi x) * (K * lreg_psi x) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
              gcongr
              · exact hK j (hj'.trans hi) x
              · exact hK (i - j) ((Nat.sub_le _ _).trans hi) x
          _ = 2 ^ i * (K * lreg_psi x) ^ 2 := by
              rw [← Finset.sum_mul, ← Finset.sum_mul]
              have : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) = 2 ^ i := by
                exact_mod_cast Nat.sum_range_choose i
              rw [this]; ring
      calc ‖(-2 : ℝ)‖ * ‖iteratedFDeriv ℝ i (fun y : Euc d => lreg_psi y * lreg_psi y) x‖
          ≤ 2 * (2 ^ i * (K * lreg_psi x) ^ 2) := by
            rw [Real.norm_eq_abs, abs_neg, abs_two]
            gcongr
            exact h1.trans h2
        _ = _ := by ring
    -- the Leibniz estimate
    rw [← norm_iteratedFDeriv_fderiv]
    have hfd : fderiv ℝ (lreg_psi : Euc d → ℝ) =
        fun y => (-2 * lreg_psi y ^ 2) • (innerSL ℝ y : Euc d →L[ℝ] ℝ) :=
      funext lreg_psi_fderiv
    rw [hfd]
    have hsd : ContDiff ℝ n (fun y : Euc d => -2 * lreg_psi y ^ 2) :=
      contDiff_const.mul (lreg_psi_contDiff.pow 2)
    have hTd : ContDiff ℝ n (fun y : Euc d => (innerSL ℝ y : Euc d →L[ℝ] ℝ)) :=
      (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).contDiff
    have h1 := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (N := (n : ℕ∞ω)) hsd hTd x (n := n) le_rfl
    refine h1.trans ?_
    have hbd : ∀ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : Euc d => -2 * lreg_psi y ^ 2) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : Euc d => (innerSL ℝ y : Euc d →L[ℝ] ℝ)) x‖ ≤
        (n.choose i : ℝ) * (2 * 2 ^ n * K ^ 2 * lreg_psi x ^ 2 * (1 + ‖x‖)) := by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have h2 : ‖iteratedFDeriv ℝ i (fun y : Euc d => -2 * lreg_psi y ^ 2) x‖ ≤
          2 * 2 ^ n * K ^ 2 * lreg_psi x ^ 2 :=
        (hs i hi').trans (by
          have : (2 : ℝ) ^ i ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hi'
          gcongr)
      rw [mul_assoc]
      gcongr
      exact lreg_T_bound _ x
    refine (Finset.sum_le_sum hbd).trans ?_
    rw [← Finset.sum_mul]
    have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    rw [hsum]
    have hpm := lreg_psi_mul_le x
    calc 2 ^ n * (2 * 2 ^ n * K ^ 2 * lreg_psi x ^ 2 * (1 + ‖x‖))
        = 2 ^ n * 2 * 2 ^ n * K ^ 2 * lreg_psi x * (lreg_psi x * (1 + ‖x‖)) := by ring
      _ ≤ 2 ^ n * 2 * 2 ^ n * K ^ 2 * lreg_psi x * 2 := by gcongr
      _ = 4 ^ (n + 1) * K ^ 2 * lreg_psi x := by
          rw [pow_succ, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring

lemma lreg_l_contDiff {n : ℕ∞ω} :
    ContDiff ℝ n (fun x : Euc d => (1 / 2 : ℝ) * Real.log (1 + ‖x‖ ^ 2)) :=
  contDiff_const.mul ((contDiff_const.add (contDiff_norm_sq ℝ)).log (fun x => by positivity))

lemma lreg_l_fderiv (x : Euc d) :
    fderiv ℝ (fun x : Euc d => (1 / 2 : ℝ) * Real.log (1 + ‖x‖ ^ 2)) x =
      lreg_psi x • (innerSL ℝ x : Euc d →L[ℝ] ℝ) := by
  have h1 : HasFDerivAt (fun x : Euc d => 1 + ‖x‖ ^ 2) (2 • innerSL ℝ x) x :=
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_add 1
  have hne : (1 + ‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have h2 := (h1.log hne).const_mul (1 / 2 : ℝ)
  rw [h2.fderiv]
  unfold lreg_psi
  ext w
  simp
  ring

/-- All derivatives of positive order of `½ log (1 + ‖x‖²)` up to order `n` are bounded. -/
lemma lreg_l_bound (n : ℕ) : ∃ M : ℝ, ∀ j, 1 ≤ j → j ≤ n → ∀ x : Euc d,
    ‖iteratedFDeriv ℝ j (fun x : Euc d => (1 / 2 : ℝ) * Real.log (1 + ‖x‖ ^ 2)) x‖ ≤ M := by
  obtain ⟨K, hK1, hK⟩ := lreg_psi_bound (d := d) n
  refine ⟨2 ^ n * K * 2, fun j hj hjn x => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have hfd : fderiv ℝ (fun x : Euc d => (1 / 2 : ℝ) * Real.log (1 + ‖x‖ ^ 2)) =
      fun y => lreg_psi y • (innerSL ℝ y : Euc d →L[ℝ] ℝ) := funext lreg_l_fderiv
  rw [hfd]
  have hTd : ContDiff ℝ m (fun y : Euc d => (innerSL ℝ y : Euc d →L[ℝ] ℝ)) :=
    (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).contDiff
  have h1 := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (N := (m : ℕ∞ω)) (lreg_psi_contDiff (n := m)) hTd x
    (n := m) le_rfl
  refine h1.trans ?_
  have hbd : ∀ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i lreg_psi x‖ *
      ‖iteratedFDeriv ℝ (m - i) (fun y : Euc d => (innerSL ℝ y : Euc d →L[ℝ] ℝ)) x‖ ≤
      (m.choose i : ℝ) * (K * (lreg_psi x * (1 + ‖x‖))) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hab : ‖iteratedFDeriv ℝ i lreg_psi x‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun y : Euc d => (innerSL ℝ y : Euc d →L[ℝ] ℝ)) x‖ ≤
        K * (lreg_psi x * (1 + ‖x‖)) :=
      calc _ ≤ (K * lreg_psi x) * (1 + ‖x‖) :=
            mul_le_mul (hK i (by omega) x) (lreg_T_bound _ x) (norm_nonneg _)
              (mul_nonneg (by linarith) (lreg_psi_pos x).le)
        _ = _ := by ring
    calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i lreg_psi x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y : Euc d => (innerSL ℝ y : Euc d →L[ℝ] ℝ)) x‖
        = (m.choose i : ℝ) * (‖iteratedFDeriv ℝ i lreg_psi x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y : Euc d => (innerSL ℝ y : Euc d →L[ℝ] ℝ)) x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum hbd).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = 2 ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  rw [hsum]
  have hpm := lreg_psi_mul_le x
  have h2m : (2 : ℝ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
  calc 2 ^ m * (K * (lreg_psi x * (1 + ‖x‖))) ≤ 2 ^ m * (K * 2) := by gcongr
    _ ≤ 2 ^ n * (K * 2) := by gcongr
    _ = _ := by ring

/-! ### Assembly for the logarithmic thermal density -/

lemma lreg_w_eq {a β : ℝ} (x : Euc d) :
    (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2) = t67w a β x := by
  have hpos : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  rw [Real.rpow_def_of_pos hpos, ← Real.exp_add]
  unfold t67w t67l confinement
  congr 1
  ring

lemma lreg_rdec_of_le {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ} {C : ℝ}
    (h0 : ∀ x, 0 ≤ ρ x)
    (hle : ∀ x, ρ x ≤ C * ((1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2))) :
    lreg_RDec ρ := by
  intro N
  set K0 := Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2) with hK0
  obtain ⟨C1, hC1, hC1b⟩ := cb_rpow_le_exp (p := (N : ℝ)) (b := β * a / 16) (by positivity)
    (by positivity)
  refine ⟨C1 * Real.exp (2 * (β * a / 16)) * (max C 0 * K0), fun x => ?_⟩
  set r := ‖x‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg x
  have hw := lreg_w_eq (a := a) (β := β) x
  have hwle := t67w_le (d := d) ha hβ x
  have hwpos := t67w_pos (d := d) a β x
  have hρ : ρ x ≤ max C 0 * t67w a β x := by
    calc ρ x ≤ C * ((1 + r ^ 2) ^ (β / 2) * Real.exp (-β * a * r ^ 2 / 2)) := hle x
      _ = C * t67w a β x := by rw [hw]
      _ ≤ max C 0 * t67w a β x := mul_le_mul_of_nonneg_right (le_max_left _ _) hwpos.le
  have h1 : (1 + r) ^ N ≤ C1 * Real.exp (β * a / 16 * (1 + r) ^ 2) := by
    have := hC1b (1 + r) (by positivity)
    rwa [Real.rpow_natCast] at this
  have h2 : (1 + r) ^ 2 ≤ 2 + 2 * r ^ 2 := by nlinarith [sq_nonneg (1 - r)]
  have h3 : Real.exp (β * a / 16 * (1 + r) ^ 2) ≤
      Real.exp (2 * (β * a / 16)) * Real.exp (2 * (β * a / 16) * r ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : 0 ≤ β * a / 16 := by positivity
    nlinarith
  have h4 : t67w a β x ≤ K0 * Real.exp (-(β * a / 4) * r ^ 2) := hwle
  calc (1 + r) ^ N * ‖ρ x‖ = (1 + r) ^ N * ρ x := by rw [Real.norm_of_nonneg (h0 x)]
    _ ≤ (C1 * (Real.exp (2 * (β * a / 16)) * Real.exp (2 * (β * a / 16) * r ^ 2))) *
          (max C 0 * (K0 * Real.exp (-(β * a / 4) * r ^ 2))) := by
        refine mul_le_mul ?_ ?_ (h0 x) (by positivity)
        · exact h1.trans (mul_le_mul_of_nonneg_left h3 hC1.le)
        · exact hρ.trans (mul_le_mul_of_nonneg_left h4 (le_max_right _ _))
    _ = C1 * Real.exp (2 * (β * a / 16)) * (max C 0 * K0) *
          Real.exp ((2 * (β * a / 16) - β * a / 4) * r ^ 2) := by
        have : Real.exp ((2 * (β * a / 16) - β * a / 4) * r ^ 2) =
            Real.exp (2 * (β * a / 16) * r ^ 2) * Real.exp (-(β * a / 4) * r ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this]; ring
    _ ≤ C1 * Real.exp (2 * (β * a / 16)) * (max C 0 * K0) * 1 := by
        gcongr
        rw [Real.exp_le_one_iff]
        have : 0 ≤ β * a := by positivity
        nlinarith [sq_nonneg r]
    _ = _ := by ring

lemma lreg_data (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ Z c C : ℝ, 0 < Z ∧ 0 < c ∧ 0 < C ∧
      (∀ x, 0 ≤ thermalDensity d 0 a β x) ∧ Measurable (thermalDensity d 0 a β) ∧
      (∀ x, thermalDensity d 0 a β x = Real.exp (-β * (a * ‖x‖ ^ 2 / 2 +
        lreg_U (thermalDensity d 0 a β) x)) / Z) ∧
      (∀ x, c * (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2) ≤
          thermalDensity d 0 a β x ∧
        thermalDensity d 0 a β x ≤ C * (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) ∧
      (∀ x, HRS.Whole.convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β) x =
        lreg_U (thermalDensity d 0 a β) x) := by
  obtain ⟨hP, heq0⟩ := can2_isThermalDensity_log hd ha hβ
  obtain ⟨c, hc, C, hbd⟩ := logThermal_bounds_proof hd a β ha hβ
  set ρ := thermalDensity d 0 a β with hρ
  have hU : ∀ x, HRS.Whole.convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β) x = lreg_U ρ x := by
    intro x
    unfold thermalMeasure
    rw [HRS.MS.Thm.convMeasure_withDensityReal _ hP.measurable hP.nonneg x]
    unfold lreg_U
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [t67_g]
  have hconv : ∀ x, HRS.Whole.convMeasure (rieszKernel d 0) (HRS.Whole.withDensityReal ρ) x = lreg_U ρ x := hU
  set Z : ℝ := ∫ y, Real.exp (-β * (HRS.Whole.confinement a y + HRS.Whole.convMeasure (rieszKernel d 0)
    (HRS.Whole.withDensityReal ρ) y)) with hZ
  have hZ0 : 0 ≤ Z := integral_nonneg fun y => (Real.exp_pos _).le
  have hZpos : 0 < Z := by
    rcases hZ0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hρ0 : ∀ x, ρ x = 0 := fun x => by rw [heq0 x, ← h, div_zero]
      have := hP.integral_one
      simp [hρ0] at this
  have heq : ∀ x, ρ x = Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + lreg_U ρ x)) / Z := by
    intro x
    rw [heq0 x, hconv x]
    rfl
  have hCpos : 0 < C := by
    have h := hbd 0
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.one_rpow,
      mul_one, mul_zero, neg_mul, zero_div, Real.exp_zero] at h
    linarith [h.1, h.2]
  exact ⟨Z, c, C, hZpos, hc, hCpos, hP.nonneg, hP.measurable, heq, hbd, hU⟩

/-- `U + ½ log (1 + ‖x‖²)` is bounded, from the two-sided bounds and the thermal equation. -/
lemma lreg_UL_bound {a β Z c C : ℝ} (hβ : 0 < β) (hZ : 0 < Z) (hc : 0 < c) (hC : 0 < C)
    {ρ : Euc d → ℝ}
    (heq : ∀ x, ρ x = Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + lreg_U ρ x)) / Z)
    (hbd : ∀ x, c * (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2) ≤ ρ x ∧
      ρ x ≤ C * (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) :
    ∃ B : ℝ, ∀ x, |lreg_U ρ x + (1 / 2 : ℝ) * Real.log (1 + ‖x‖ ^ 2)| ≤ B := by
  refine ⟨|Real.log c + Real.log Z| / β + |Real.log C + Real.log Z| / β, fun x => ?_⟩
  have hA : (0 : ℝ) < (1 + ‖x‖ ^ 2) ^ (β / 2) := by positivity
  have hB : (0 : ℝ) < Real.exp (-β * a * ‖x‖ ^ 2 / 2) := Real.exp_pos _
  have hlogA : Real.log ((1 + ‖x‖ ^ 2) ^ (β / 2)) = β / 2 * Real.log (1 + ‖x‖ ^ 2) :=
    Real.log_rpow (by positivity) _
  have hρlog : Real.log (ρ x) = -β * (a * ‖x‖ ^ 2 / 2 + lreg_U ρ x) - Real.log Z := by
    rw [heq x, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  have hρpos : 0 < ρ x := lt_of_lt_of_le (by positivity) (hbd x).1
  have hlo := Real.log_le_log (by positivity) (hbd x).1
  have hhi := Real.log_le_log hρpos (hbd x).2
  rw [Real.log_mul (by positivity) hB.ne', Real.log_mul hc.ne' hA.ne', hlogA, Real.log_exp] at hlo
  rw [Real.log_mul (by positivity) hB.ne', Real.log_mul hC.ne' hA.ne', hlogA, Real.log_exp] at hhi
  rw [hρlog] at hlo hhi
  set t := lreg_U ρ x + (1 / 2 : ℝ) * Real.log (1 + ‖x‖ ^ 2) with ht
  have h1 : β * t ≤ -(Real.log c + Real.log Z) := by rw [ht]; nlinarith
  have h2 : -(Real.log C + Real.log Z) ≤ β * t := by rw [ht]; nlinarith
  rw [abs_le]
  constructor
  · have : -(|Real.log C + Real.log Z| / β) ≤ t := by
      rw [← neg_div, div_le_iff₀ hβ]
      nlinarith [le_abs_self (Real.log C + Real.log Z)]
    have h3 : 0 ≤ |Real.log c + Real.log Z| / β := by positivity
    linarith
  · have : t ≤ |Real.log c + Real.log Z| / β := by
      rw [le_div_iff₀ hβ]
      nlinarith [neg_le_abs (Real.log c + Real.log Z)]
    have h3 : 0 ≤ |Real.log C + Real.log Z| / β := by positivity
    linarith

/-- **C8.**  Regularity of the logarithmic thermal density (Proposition S4.1). -/
theorem logThermal_regularity_proof : type_of% @HRS.Whole.logThermal_regularity := by
  intro d hd a β ha hβ
  obtain ⟨Z, c, C, hZ, hc, hC, hρ0, hρm, heq, hbd, hU⟩ := lreg_data hd ha hβ
  set ρ := thermalDensity d 0 a β with hρ
  have hdec : lreg_RDec ρ :=
    lreg_rdec_of_le ha hβ hρ0 (fun x => by simpa [mul_assoc] using (hbd x).2)
  have boot := lreg_bootstrap hd hZ hρm hdec heq
  have hfun : HRS.Whole.convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β) = lreg_U ρ :=
    funext hU
  have hρn : ∀ n : ℕ, ContDiff ℝ n ρ ∧ ∀ j ≤ n, lreg_RDec (iteratedFDeriv ℝ j ρ) := by
    intro n
    obtain ⟨hUn, M, hM0, hM⟩ := boot n
    obtain ⟨k0, C', hC', hD⟩ := lreg_exponent_bound a β hUn hM0 hM
    have hφ : ContDiff ℝ n (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + lreg_U ρ x)) :=
      contDiff_const.mul (((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2).add hUn)
    exact lreg_rho_decay hZ heq hdec hφ hC' hD
  rw [hfun]
  refine ⟨?_, contDiff_infty.2 fun k => (boot k).1, fun k hk => ?_, fun k => ?_⟩
  · refine ⟨⟨ρ, contDiff_infty.2 fun n => (hρn n).1, fun k n => ?_⟩, fun x => rfl⟩
    obtain ⟨C1, hC1⟩ := (hρn n).2 n le_rfl k
    refine ⟨C1, fun x => ?_⟩
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ρ x‖ ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n ρ x‖ := by
          gcongr; linarith
      _ ≤ C1 := hC1 x
  · obtain ⟨_, M, _, hM⟩ := boot k
    exact ⟨M, fun x => hM k hk le_rfl x⟩
  · obtain ⟨hUk, M, hM0, hM⟩ := boot k
    obtain ⟨Ml, hMl⟩ := lreg_l_bound (d := d) k
    obtain ⟨B, hB⟩ := lreg_UL_bound hβ hZ hc hC heq hbd
    refine ⟨hUk.add lreg_l_contDiff, fun j hj => ?_⟩
    refine ⟨max B (M + Ml), ?_⟩
    rintro _ ⟨x, rfl⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact (hB x).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have hj1 : (j : ℕ∞ω) ≤ k := by exact_mod_cast hj
      have h1 : ContDiffAt ℝ j (lreg_U ρ) x := (hUk.of_le (by exact_mod_cast hj)).contDiffAt
      have h2 : ContDiffAt ℝ j (fun x : Euc d => (1 / 2 : ℝ) * Real.log (1 + ‖x‖ ^ 2)) x :=
        lreg_l_contDiff.contDiffAt
      have e : iteratedFDeriv ℝ j (fun x : Euc d => lreg_U ρ x + (1 / 2 : ℝ) * Real.log (1 + ‖x‖ ^ 2)) x =
          iteratedFDeriv ℝ j (lreg_U ρ) x +
            iteratedFDeriv ℝ j (fun x : Euc d => (1 / 2 : ℝ) * Real.log (1 + ‖x‖ ^ 2)) x :=
        iteratedFDeriv_add_apply h1 h2
      show ‖iteratedFDeriv ℝ j (fun x : Euc d => lreg_U ρ x + (1 / 2 : ℝ) * Real.log (1 + ‖x‖ ^ 2)) x‖ ≤ _
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add (hM j hj0 hj x) (hMl j hj0 hj x))

end HRS.MS.LogReg

end
