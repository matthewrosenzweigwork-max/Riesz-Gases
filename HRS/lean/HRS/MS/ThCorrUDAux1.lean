import HRS.MS.ThCorrUAux3
import HRS.MS.EucReg
import HRS.MS.LogReg
import HRS.MS.GapRefAux2
import HRS.MS.ThCorrDefs

/-!
# TC-U2 (part 1): uniform bootstrap for a kernel with an integrable gradient (`s < d - 1` and `s = 0`)

Namespace `HRS.MS.TcU`; helper lemmas carry the prefix `tcu2_`.

The merged bootstraps `rege_bootstrap` (`0 < s < d - 1`) and `lreg_bootstrap` (`s = 0`) return `∃ M` AFTER all
parameters.  Here the induction of their proofs is repeated with the constants tracked: for the structure
`TcuInst` (a thermal instance: `a ∈ [am, ap]`, `β ∈ [βm, βp]`, `Z ≥ z₀`, `ρ = exp(-β(a‖x‖²/2 + U ρ))/Z`,
`ρ ≤ C₀ exp(-b‖x‖²)`) the theorem `tcu2_boot` returns, for every order `k`, ONE constant `M` such that all
instances satisfy `‖D^i (U ρ)‖ ≤ M` for `1 ≤ i ≤ k`.  The potential operator `U`, its gradient operator `W`, the kernel
`κ` of the gradient and the constants of the gradient step are abstract (`hpot`, `hconv`), so the same proof serves
the kernels `‖z‖^{-s}` (`rege_potential`) and `-log ‖z‖` (`lreg_potential`).

Also here: the explicit-constant Faà di Bruno bound for `ρ = e^φ/Z` (`tcu2_rho_deriv`) and the exponent bound.
No existing file is edited.
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace HRS.MS.TcU

open HRS HRS.Whole HRS.MS.LogReg HRS.MS.Thm

variable {d : ℕ}

/-! ### Explicit-constant lemmas -/

/-- Derivatives of the exponent `φ = -β (a‖x‖²/2 + U)` of order `1 ≤ i ≤ n`, with an explicit constant. -/
lemma tcu2_exponent_bound (a β : ℝ) (ha : 0 ≤ a) (hβ : 0 ≤ β) {U : Euc d → ℝ} {n : ℕ}
    (hU : ContDiff ℝ n U) {M : ℝ} (hM : 0 ≤ M)
    (hUb : ∀ i, 1 ≤ i → i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i U x‖ ≤ M) :
    ∀ i, 1 ≤ i → i ≤ n → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + U x)) x‖ ≤
        (β * a + β * M) * (1 + ‖x‖) := by
  intro i hi hin x
  have hqd : ContDiff ℝ n (fun x : Euc d => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hfun : (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + U x)) =
      (fun x : Euc d => (-β * a / 2) • ‖x‖ ^ 2) + (fun x => (-β) • U x) := by
    funext x; simp only [Pi.add_apply, smul_eq_mul]; ring
  have hx1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hqi : ContDiffAt ℝ i (fun x : Euc d => ‖x‖ ^ 2) x :=
    (hqd.of_le (by exact_mod_cast hin)).contDiffAt
  have hUi : ContDiffAt ℝ i U x := (hU.of_le (by exact_mod_cast hin)).contDiffAt
  have e1 : |(-β * a / 2)| = β * a / 2 := by
    rw [show (-β * a / 2) = -(β * a / 2) by ring, abs_neg, abs_of_nonneg (by positivity)]
  have e2 : |(-β)| = β := by rw [abs_neg, abs_of_nonneg hβ]
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
    _ ≤ (β * a + β * M) * (1 + ‖x‖) := by
        rw [e1, e2]
        have h := mul_le_mul_of_nonneg_left hx1 (mul_nonneg hβ hM)
        nlinarith [h, mul_nonneg hβ ha]

/-- Derivative bounds for `ρ = e^φ/Z` with an explicit constant: `‖D^j ρ‖ ≤ j! C₀ (max C 1)^j (1+‖x‖)^j e^{-b‖x‖²}`. -/
lemma tcu2_rho_deriv {b Z C0 : ℝ} (hZ : 0 < Z) {ρ φ : Euc d → ℝ}
    (hρ : ∀ x, ρ x = Real.exp (φ x) / Z) (hup : ∀ x, ρ x ≤ C0 * Real.exp (-b * ‖x‖ ^ 2))
    {n : ℕ} (hφ : ContDiff ℝ n φ) {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ C * (1 + ‖x‖)) :
    ContDiff ℝ n ρ ∧ ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j ρ x‖ ≤
      ((Nat.factorial j : ℝ) * max C0 0 * (max C 1) ^ j) * (1 + ‖x‖) ^ j * Real.exp (-b * ‖x‖ ^ 2) := by
  have hρeq : ρ = fun x => Z⁻¹ • Real.exp (φ x) :=
    funext fun x => by rw [hρ x, smul_eq_mul, div_eq_inv_mul]
  refine ⟨?_, fun j hj x => ?_⟩
  · rw [hρeq]; exact (Real.contDiff_exp.comp hφ).const_smul Z⁻¹
  · have hφj : ContDiff ℝ j φ := hφ.of_le (by exact_mod_cast hj)
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
    have hρx : ρ x ≤ max C0 0 * Real.exp (-b * ‖x‖ ^ 2) :=
      (hup x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hDj : D ^ j = (max C 1) ^ j * (1 + ‖x‖) ^ j := by rw [hDdef, mul_pow]
    calc ‖iteratedFDeriv ℝ j ρ x‖ ≤ (Nat.factorial j : ℝ) * ρ x * D ^ j := hn
      _ ≤ (Nat.factorial j : ℝ) * (max C0 0 * Real.exp (-b * ‖x‖ ^ 2)) * D ^ j := by
          gcongr
      _ = _ := by rw [hDj]; ring

/-- `(1+r)^j e^{-b r²}`-envelopes give the `(1+‖y‖)^{-(d+1)}` decay of `lreg_bound_of_rdec`, with an explicit constant. -/
lemma tcu2_phi_bound {b : ℝ} (hb : 0 < b) (j : ℕ) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ {K : ℝ}, 0 ≤ K → ∀ n : Euc d → ℝ,
      (∀ x, n x ≤ K * (1 + ‖x‖) ^ j * Real.exp (-b * ‖x‖ ^ 2)) →
      ∀ y, n y ≤ (K * Cp) * lreg_phi d y := by
  obtain ⟨Cp, hCp, hCpb⟩ := rege_poly_gauss_bdd hb (d + 1 + j)
  refine ⟨Cp, hCp.le, fun {K} hK n hn y => ?_⟩
  have hp : (0 : ℝ) < (1 + ‖y‖) ^ (d + 1) := by positivity
  unfold lreg_phi
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  calc n y * (1 + ‖y‖) ^ (d + 1) ≤ (K * (1 + ‖y‖) ^ j * Real.exp (-b * ‖y‖ ^ 2)) * (1 + ‖y‖) ^ (d + 1) :=
        mul_le_mul_of_nonneg_right (hn y) hp.le
    _ = K * ((1 + ‖y‖) ^ (d + 1 + j) * Real.exp (-b * ‖y‖ ^ 2)) := by rw [pow_add]; ring
    _ ≤ K * Cp := mul_le_mul_of_nonneg_left (hCpb _ (norm_nonneg y)) hK

/-! ### Thermal instances -/

/-- A thermal instance for the potential operator `Uop`. -/
structure TcuInst (d : ℕ) (Uop : (Euc d → ℝ) → Euc d → ℝ) (am ap βm βp b C0 z₀ : ℝ)
    (a β Z : ℝ) (ρ : Euc d → ℝ) : Prop where
  ha1 : am ≤ a
  ha2 : a ≤ ap
  hβ1 : βm ≤ β
  hβ2 : β ≤ βp
  hZ : z₀ ≤ Z
  hm : Measurable ρ
  heq : ∀ x, ρ x = Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + Uop ρ x)) / Z
  hup : ∀ x, ρ x ≤ C0 * Real.exp (-b * ‖x‖ ^ 2)

/-- The statement `P k M`: all instances have `U ρ ∈ C^k` with `‖D^i (U ρ)‖ ≤ M`, `1 ≤ i ≤ k`. -/
def TcuP (d : ℕ) (Uop : (Euc d → ℝ) → Euc d → ℝ) (am ap βm βp b C0 z₀ : ℝ) (k : ℕ) (M : ℝ) : Prop :=
  ∀ (a β Z : ℝ) (ρ : Euc d → ℝ), TcuInst d Uop am ap βm βp b C0 z₀ a β Z ρ →
    ContDiff ℝ k (Uop ρ) ∧ ∀ i, 1 ≤ i → i ≤ k → ∀ x, ‖iteratedFDeriv ℝ i (Uop ρ) x‖ ≤ M

section Inst

variable {Uop : (Euc d → ℝ) → Euc d → ℝ} {am ap βm βp b C0 z₀ a β Z : ℝ} {ρ : Euc d → ℝ}

lemma TcuInst.pos_a (h : TcuInst d Uop am ap βm βp b C0 z₀ a β Z ρ) (ham : 0 < am) : 0 < a :=
  ham.trans_le h.ha1

lemma TcuInst.pos_β (h : TcuInst d Uop am ap βm βp b C0 z₀ a β Z ρ) (hβm : 0 < βm) : 0 < β :=
  hβm.trans_le h.hβ1

lemma TcuInst.pos_Z (h : TcuInst d Uop am ap βm βp b C0 z₀ a β Z ρ) (hz₀ : 0 < z₀) : 0 < Z :=
  hz₀.trans_le h.hZ

lemma TcuInst.pos (h : TcuInst d Uop am ap βm βp b C0 z₀ a β Z ρ) (hz₀ : 0 < z₀) (x : Euc d) :
    0 < ρ x := by
  rw [h.heq x]
  have := h.pos_Z hz₀
  positivity

lemma TcuInst.rdec (h : TcuInst d Uop am ap βm βp b C0 z₀ a β Z ρ) (hz₀ : 0 < z₀) (hb : 0 < b)
    (hC0 : 0 ≤ C0) : lreg_RDec ρ := by
  refine rege_rdec_of_gauss (j := 0) hb (K := C0) hC0 (fun x => ?_)
  rw [Real.norm_of_nonneg (h.pos hz₀ x).le, pow_zero, mul_one]
  exact h.hup x

end Inst

/-! ### The uniform bootstrap -/

/-- **Uniform bootstrap** for a kernel whose gradient kernel `κ` is integrable at the singularity
(`‖κ z‖ ≤ ‖z‖^{-σ}`, `σ < d`).  For every `k` there is one constant `M` working for all thermal instances. -/
theorem tcu2_boot (hd1 : 1 ≤ d) {σ lam : ℝ} (hσd : σ < d) (hσ0 : 0 ≤ σ) (hlam : 0 ≤ lam)
    {κ : Euc d → Euc d} (hκm : AEStronglyMeasurable κ volume) (hκ : ∀ z, ‖κ z‖ ≤ ‖z‖ ^ (-σ))
    {Lop : Euc d →L[ℝ] Euc d →L[ℝ] ℝ} (hL : ‖Lop‖ ≤ lam)
    {Uop : (Euc d → ℝ) → Euc d → ℝ} {Wop : (Euc d → ℝ) → Euc d → Euc d}
    (hpot : ∀ F : Euc d → ℝ, AEStronglyMeasurable F volume → lreg_RDec F → Continuous (Wop F) ∧
      (∀ x, HasFDerivAt (Uop F) (Lop (Wop F x)) x) ∧
      ∀ C : ℝ, 0 ≤ C → (∀ y, ‖F y‖ ≤ C * lreg_phi d y) → ∀ x, ‖Wop F x‖ ≤ C * lreg_A d σ)
    (hconv : ∀ F : Euc d → ℝ, Wop F = lreg_conv
      ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euc d →L[ℝ] Euc d).flip) κ F)
    {am ap βm βp b C0 z₀ : ℝ} (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp)
    (hz₀ : 0 < z₀) (hb : 0 < b) (hC0 : 0 ≤ C0) :
    ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ TcuP d Uop am ap βm βp b C0 z₀ k M := by
  obtain ⟨Cp0, hCp0, hphi0⟩ := tcu2_phi_bound (d := d) hb 0
  have hAn : 0 ≤ lreg_A d σ := lreg_A_nonneg
  -- the first order
  have hQ1 : ∃ M : ℝ, 0 ≤ M ∧ TcuP d Uop am ap βm βp b C0 z₀ 1 M := by
    refine ⟨lam * ((C0 * Cp0) * lreg_A d σ), mul_nonneg hlam (mul_nonneg (mul_nonneg hC0 hCp0) hAn),
      fun a β Z ρ h => ?_⟩
    have hdec := h.rdec hz₀ hb hC0
    obtain ⟨hWc, hderiv, hWb⟩ := hpot ρ h.hm.aestronglyMeasurable hdec
    have hfd : fderiv ℝ (Uop ρ) = fun x => Lop (Wop ρ x) :=
      funext fun x => (hderiv x).fderiv
    have hdiff : Differentiable ℝ (Uop ρ) := fun x => (hderiv x).differentiableAt
    have hb0 : ∀ y, ‖ρ y‖ ≤ (C0 * Cp0) * lreg_phi d y := by
      intro y
      refine hphi0 hC0 (fun x => ‖ρ x‖) (fun x => ?_) y
      rw [Real.norm_of_nonneg (h.pos hz₀ x).le, pow_zero, mul_one]
      exact h.hup x
    refine ⟨contDiff_one_iff_fderiv.2 ⟨hdiff, by rw [hfd]; exact Lop.continuous.comp hWc⟩,
      fun i hi hi1 x => ?_⟩
    obtain rfl : i = 1 := le_antisymm hi1 hi
    rw [norm_iteratedFDeriv_one, hfd]
    calc ‖Lop (Wop ρ x)‖ ≤ ‖Lop‖ * ‖Wop ρ x‖ := Lop.le_opNorm _
      _ ≤ lam * ((C0 * Cp0) * lreg_A d σ) :=
          mul_le_mul hL (hWb _ (mul_nonneg hC0 hCp0) hb0 x) (norm_nonneg _) hlam
  -- the induction step
  have hstep : ∀ k : ℕ, 1 ≤ k → (∃ M : ℝ, 0 ≤ M ∧ TcuP d Uop am ap βm βp b C0 z₀ k M) →
      ∃ M : ℝ, 0 ≤ M ∧ TcuP d Uop am ap βm βp b C0 z₀ (k + 1) M := by
    intro k hk ⟨M, hM0, hP⟩
    obtain ⟨Cpk, hCpk, hphik⟩ := tcu2_phi_bound (d := d) hb k
    have hap0 : 0 < ap := ham.trans_le hap
    have hβp0 : 0 < βp := hβm.trans_le hβp
    set Cu : ℝ := βp * ap + βp * M with hCu
    have hCu0 : 0 ≤ Cu := by positivity
    set Kk : ℝ := (Nat.factorial k : ℝ) * max C0 0 * (max Cu 1) ^ k with hKk
    have hKk0 : 0 ≤ Kk := by positivity
    refine ⟨max M (lam * (1 * ((Kk * Cpk) * lreg_A d σ))), le_max_of_le_left hM0, fun a β Z ρ h => ?_⟩
    have ha := h.pos_a ham
    have hβ := h.pos_β hβm
    have hZ := h.pos_Z hz₀
    obtain ⟨hUk, hUb⟩ := hP a β Z ρ h
    have hD := tcu2_exponent_bound a β ha.le hβ.le hUk hM0 hUb
    have hD' : ∀ i, 1 ≤ i → i ≤ k → ∀ x : Euc d,
        ‖iteratedFDeriv ℝ i (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + Uop ρ x)) x‖ ≤
          Cu * (1 + ‖x‖) := by
      intro i hi hik x
      refine (hD i hi hik x).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have h1 : β * a ≤ βp * ap := mul_le_mul h.hβ2 h.ha2 ha.le hβp0.le
      have h2 : β * M ≤ βp * M := mul_le_mul_of_nonneg_right h.hβ2 hM0
      linarith
    have hφ : ContDiff ℝ k (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + Uop ρ x)) :=
      contDiff_const.mul (((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2).add hUk)
    obtain ⟨hρk, hρD⟩ := tcu2_rho_deriv hZ h.heq h.hup hφ hCu0 hD'
    have hρdec : ∀ j ≤ k, lreg_RDec (iteratedFDeriv ℝ j ρ) := fun j hj =>
      rege_rdec_of_gauss (j := j) hb
        (K := (Nat.factorial j : ℝ) * max C0 0 * (max Cu 1) ^ j) (by positivity) (hρD j hj)
    have hbk : ∀ y, ‖iteratedFDeriv ℝ k ρ y‖ ≤ (Kk * Cpk) * lreg_phi d y :=
      hphik hKk0 (fun x => ‖iteratedFDeriv ℝ k ρ x‖) (hρD k le_rfl)
    obtain ⟨hWc, hderiv, hWb⟩ := hpot ρ h.hm.aestronglyMeasurable (h.rdec hz₀ hb hC0)
    have hfd : fderiv ℝ (Uop ρ) = fun x => Lop (Wop ρ x) :=
      funext fun x => (hderiv x).fderiv
    have hdiff : Differentiable ℝ (Uop ρ) := fun x => (hderiv x).differentiableAt
    set B : Euc d →L[ℝ] ℝ →L[ℝ] Euc d :=
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euc d →L[ℝ] Euc d).flip with hBdef
    have hB : ∀ v w, ‖B v w‖ ≤ 1 * ‖v‖ * ‖w‖ := by
      intro v w
      simp [hBdef, norm_smul, mul_comm]
    obtain ⟨hWk, hWbk⟩ := lreg_conv_smooth hd1 hσd hσ0 hκm hκ k B zero_le_one hB hρk hρdec
    rw [← hconv ρ] at hWk hWbk
    have hbound := hWbk (Kk * Cpk) (mul_nonneg hKk0 hCpk) hbk
    refine ⟨?_, fun i hi hik x => ?_⟩
    · have hc : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hc, contDiff_succ_iff_fderiv]
      refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
      rw [hfd]
      exact Lop.contDiff.comp hWk
    · rcases Nat.lt_or_ge i (k + 1) with hlt | hge
      · exact (hUb i hi (by omega) x).trans (le_max_left _ _)
      · obtain rfl : i = k + 1 := le_antisymm hik hge
        refine le_trans ?_ (le_max_right _ _)
        rw [← norm_iteratedFDeriv_fderiv, hfd]
        have h1 := Lop.norm_iteratedFDeriv_comp_left
          (f := Wop ρ) (x := x) (n := k) hWk.contDiffAt (by exact_mod_cast le_rfl)
        calc _ ≤ ‖Lop‖ * ‖iteratedFDeriv ℝ k (Wop ρ) x‖ := h1
          _ ≤ lam * (1 * ((Kk * Cpk) * lreg_A d σ)) := mul_le_mul hL (hbound x) (norm_nonneg _) hlam
  intro k
  by_cases hk : 1 ≤ k
  · exact Nat.le_induction hQ1 (fun k hk ih => hstep k hk ih) k hk
  · obtain ⟨M, hM0, hP⟩ := hQ1
    refine ⟨M, hM0, fun a β Z ρ h => ?_⟩
    obtain ⟨h1, -⟩ := hP a β Z ρ h
    exact ⟨h1.of_le (by exact_mod_cast (by omega : k ≤ 1)), fun i hi hik => by omega⟩

/-! ### Assembly: `TcRef` and `TcDrift` from the uniform bootstrap -/

section Assembly

variable {Uop : (Euc d → ℝ) → Euc d → ℝ} {am ap βm βp b C0 z₀ : ℝ}

/-- Derivative bounds of `ρ` for an instance, from bounds on the derivatives of `U ρ`. -/
lemma tcu2_inst_deriv_of (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp)
    (hz₀ : 0 < z₀) {k : ℕ} {M : ℝ} (hM0 : 0 ≤ M)
    {a β Z : ℝ} {ρ : Euc d → ℝ} (h : TcuInst d Uop am ap βm βp b C0 z₀ a β Z ρ)
    (hUk : ContDiff ℝ k (Uop ρ))
    (hUb : ∀ i, 1 ≤ i → i ≤ k → ∀ x, ‖iteratedFDeriv ℝ i (Uop ρ) x‖ ≤ M) :
    ContDiff ℝ k ρ ∧ ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ρ x‖ ≤
      ((Nat.factorial j : ℝ) * max C0 0 * (max (βp * ap + βp * M) 1) ^ j) * (1 + ‖x‖) ^ j *
        Real.exp (-b * ‖x‖ ^ 2) := by
  have hap0 : 0 < ap := ham.trans_le hap
  have hβp0 : 0 < βp := hβm.trans_le hβp
  have ha := h.pos_a ham
  have hβ := h.pos_β hβm
  have hZ := h.pos_Z hz₀
  have hD := tcu2_exponent_bound a β ha.le hβ.le hUk hM0 hUb
  have hCu0 : 0 ≤ βp * ap + βp * M := by positivity
  have hD' : ∀ i, 1 ≤ i → i ≤ k → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + Uop ρ x)) x‖ ≤
        (βp * ap + βp * M) * (1 + ‖x‖) := by
    intro i hi hik x
    refine (hD i hi hik x).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 : β * a ≤ βp * ap := mul_le_mul h.hβ2 h.ha2 ha.le hβp0.le
    have h2 : β * M ≤ βp * M := mul_le_mul_of_nonneg_right h.hβ2 hM0
    linarith
  have hφ : ContDiff ℝ k (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + Uop ρ x)) :=
    contDiff_const.mul (((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2).add hUk)
  exact tcu2_rho_deriv hZ h.heq h.hup hφ hCu0 hD'

/-- Derivative bounds of `ρ` for an instance, from `TcuP k M`. -/
lemma tcu2_inst_deriv (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp)
    (hz₀ : 0 < z₀) {k : ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hP : TcuP d Uop am ap βm βp b C0 z₀ k M)
    {a β Z : ℝ} {ρ : Euc d → ℝ} (h : TcuInst d Uop am ap βm βp b C0 z₀ a β Z ρ) :
    ContDiff ℝ k ρ ∧ ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ρ x‖ ≤
      ((Nat.factorial j : ℝ) * max C0 0 * (max (βp * ap + βp * M) 1) ^ j) * (1 + ‖x‖) ^ j *
        Real.exp (-b * ‖x‖ ^ 2) := by
  obtain ⟨hUk, hUb⟩ := hP a β Z ρ h
  exact tcu2_inst_deriv_of ham hβm hap hβp hz₀ hM0 h hUk hUb

/-- `TcRef` for every instance, with one constant `S`. -/
theorem tcu2_ref_of_boot (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp)
    (hz₀ : 0 < z₀) (hb : 0 < b) (hC0 : 0 < C0)
    (hboot : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ TcuP d Uop am ap βm βp b C0 z₀ k M) (N : ℕ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (a β Z : ℝ) (ρ : Euc d → ℝ),
      TcuInst d Uop am ap βm βp b C0 z₀ a β Z ρ → HRS.Whole.IsProbDensity ρ →
      HRS.MS.TcDefs.TcRef d ρ C0 b S N := by
  obtain ⟨M, hM0, hP⟩ := hboot N
  refine ⟨∑ j ∈ Finset.range (N + 1), (Nat.factorial j : ℝ) * max C0 0 * (max (βp * ap + βp * M) 1) ^ j,
    Finset.sum_nonneg fun j _ => by positivity, fun a β Z ρ h hρ => ?_⟩
  refine ⟨hρ, h.pos hz₀, ?_, fun x => ?_, fun k hk x => ?_⟩
  · refine contDiff_infty.2 fun n => ?_
    obtain ⟨Mn, hMn0, hPn⟩ := hboot n
    exact (tcu2_inst_deriv ham hβm hap hβp hz₀ hMn0 hPn h).1
  · simpa using h.hup x
  · obtain ⟨-, hD⟩ := tcu2_inst_deriv ham hβm hap hβp hz₀ hM0 hP h
    refine (hD k hk x).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
      (Real.exp_pos _).le
    exact Finset.single_le_sum (f := fun j => (Nat.factorial j : ℝ) * max C0 0 *
      (max (βp * ap + βp * M) 1) ^ j) (fun j _ => by positivity)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

/-- `‖D^j (-β U - log Z)‖ ≤ β M` for `1 ≤ j ≤ k`. -/
lemma tcu2_G_deriv {k : ℕ} {M β Z : ℝ} {U : Euc d → ℝ} (hβ : 0 < β) (hU : ContDiff ℝ k U)
    (hUb : ∀ i, 1 ≤ i → i ≤ k → ∀ x, ‖iteratedFDeriv ℝ i U x‖ ≤ M) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun x => -β * U x - Real.log Z) x‖ ≤ β * M := by
  have e : (fun x => -β * U x - Real.log Z) = (fun x => (-β) • U x) + fun _ => -Real.log Z := by
    funext x; simp [sub_eq_add_neg]
  have hA : ContDiffAt ℝ j (fun x => (-β) • U x) x :=
    ((hU.of_le (by exact_mod_cast hjk)).const_smul (-β)).contDiffAt
  have hB : ContDiffAt ℝ j (fun _ : Euc d => -Real.log Z) x := contDiff_const.contDiffAt
  rw [e, iteratedFDeriv_add_apply hA hB, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, add_zero,
    iteratedFDeriv_const_smul_apply' (hU.of_le (by exact_mod_cast hjk)).contDiffAt, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_pos hβ]
  exact mul_le_mul_of_nonneg_left (hUb j hj hjk x) hβ.le

/-- `TcDrift` for every instance, with one constant `Mb`. -/
theorem tcu2_drift_of_boot (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp)
    (hz₀ : 0 < z₀)
    (hboot : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ TcuP d Uop am ap βm βp b C0 z₀ k M) (m : ℕ) :
    ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ (a β Z : ℝ) (ρ : Euc d → ℝ) (m₂ : ℝ),
      TcuInst d Uop am ap βm βp b C0 z₀ a β Z ρ → Integrable ρ → ∫ x, ρ x = 1 →
      Integrable (fun x => ‖x‖ ^ 2 * ρ x) → (∫ x, ‖x‖ ^ 2 * ρ x) ≤ m₂ →
      HRS.MS.TcDefs.TcDrift d ρ (β * a) Mb m₂ m := by
  have hβp0 : 0 < βp := hβm.trans_le hβp
  obtain ⟨M, hM0, hP⟩ := hboot (m + 1)
  refine ⟨βp * M, mul_nonneg hβp0.le hM0, fun a β Z ρ m₂ h hint h1 hmom hm₂ => ?_⟩
  have hβ := h.pos_β hβm
  have hZ := h.pos_Z hz₀
  set G : Euc d → ℝ := fun x => -β * Uop ρ x - Real.log Z with hG
  have hUsm : ContDiff ℝ ∞ (Uop ρ) := by
    refine contDiff_infty.2 fun n => ?_
    obtain ⟨Mn, -, hPn⟩ := hboot n
    exact (hPn a β Z ρ h).1
  have hGsm : ContDiff ℝ ∞ G := (contDiff_const.mul hUsm).sub contDiff_const
  have hGb : ∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j G x‖ ≤ C := by
    intro j hj
    obtain ⟨Mj, -, hPj⟩ := hboot j
    obtain ⟨hUj, hUb⟩ := hPj a β Z ρ h
    exact ⟨β * Mj, fun x => tcu2_G_deriv hβ hUj hUb hj le_rfl x⟩
  have hρ : ∀ x, ρ x = Real.exp (-((β * a) / 2) * ‖x‖ ^ 2 + G x) := by
    intro x
    rw [h.heq x]
    have : -((β * a) / 2) * ‖x‖ ^ 2 + G x = -β * (a * ‖x‖ ^ 2 / 2 + Uop ρ x) - Real.log Z := by
      rw [hG]; ring
    rw [this, Real.exp_sub, Real.exp_log hZ]
  refine ⟨⟨gradient G, HRS.MS.Gap.gap_of_logDensity hGsm hGb hρ hint h1 hmom,
    HRS.MS.Gap.gap1_contDiff_gradient hGsm m, ?_⟩, hm₂⟩
  · intro j hj x
    rw [HRS.MS.Gap.gap1_norm_iter_gradient]
    obtain ⟨hUk, hUb⟩ := hP a β Z ρ h
    refine (tcu2_G_deriv hβ hUk hUb (by omega) (by omega) x).trans ?_
    exact mul_le_mul_of_nonneg_right h.hβ2 hM0

end Assembly

end HRS.MS.TcU

end
