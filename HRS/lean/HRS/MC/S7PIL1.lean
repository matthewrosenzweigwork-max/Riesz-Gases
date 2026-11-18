import HRS.Prob.Gaussian
import HRS.Prob.Metrics

/-!
# Packet piL, part 1: derivative calculus for the sections `ψ_w(c) = D^jΦ(x₀ + Λ c)[w]`

`ψ_w = ev_w ∘ D^jΦ ∘ (x₀ + Λ ·)`; for `Φ ∈ C_b^5`, `j ≤ 3`: `ψ_w ∈ C_b²`, and
`D²ψ_w(c)(a,b) = D²(D^jΦ)(x₀ + Λ c)(Λa, Λb)[w]` with `‖D²(D^jΦ)(x)‖ = ‖D^{j+2}Φ(x)‖ ≤ cbNorm 5 Φ`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIL

open HRS

section Gen

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The evaluation of a `j`-linear form at `w`, as a continuous linear functional. -/
def S7PIL_ev {j : ℕ} (w : Fin j → E) : (E [×j]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => f w
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
    (∏ i, ‖w i‖) (fun f => by
      show ‖f w‖ ≤ (∏ i, ‖w i‖) * ‖f‖
      rw [mul_comm]; exact f.le_opNorm w)

theorem S7PIL_ev_apply {j : ℕ} (w : Fin j → E) (f : E [×j]→L[ℝ] ℝ) : S7PIL_ev w f = f w := rfl

theorem S7PIL_ev_norm {j : ℕ} (w : Fin j → E) : ‖S7PIL_ev w‖ ≤ ∏ i, ‖w i‖ :=
  LinearMap.mkContinuous_norm_le _ (Finset.prod_nonneg fun i _ => norm_nonneg _) _

/-- The section `ψ(c) = F(x₀ + Λ c)[w]` of a `j`-linear-form valued function. -/
def S7PIL_psi {j : ℕ} (F : E → E [×j]→L[ℝ] ℝ) (x0 : E) (Λ : H →L[ℝ] E) (w : Fin j → E) (c : H) : ℝ :=
  F (x0 + Λ c) w

theorem S7PIL_psi_eq {j : ℕ} (F : E → E [×j]→L[ℝ] ℝ) (x0 : E) (Λ : H →L[ℝ] E) (w : Fin j → E) :
    S7PIL_psi F x0 Λ w = (S7PIL_ev w) ∘ ((fun z => F (x0 + z)) ∘ Λ) := by
  funext c; rfl

/-- The iterated derivatives of the section. -/
theorem S7PIL_psi_iter {j : ℕ} {F : E → E [×j]→L[ℝ] ℝ} (hF : ContDiff ℝ 2 F) (x0 : E) (Λ : H →L[ℝ] E)
    (w : Fin j → E) (c : H) {i : ℕ} (hi : i ≤ 2) :
    iteratedFDeriv ℝ i (S7PIL_psi F x0 Λ w) c =
      (S7PIL_ev w).compContinuousMultilinearMap
        ((iteratedFDeriv ℝ i F (x0 + Λ c)).compContinuousLinearMap fun _ => Λ) := by
  have hG : ContDiff ℝ 2 (fun z => F (x0 + z)) := hF.comp (contDiff_const.add contDiff_id)
  have hGΛ : ContDiff ℝ 2 ((fun z => F (x0 + z)) ∘ Λ) := hG.comp Λ.contDiff
  rw [S7PIL_psi_eq]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left (S7PIL_ev w) (hGΛ.contDiffAt) (by exact_mod_cast hi)]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right Λ hG c (by exact_mod_cast hi)]
  rw [iteratedFDeriv_comp_add_left]

theorem S7PIL_psi_contDiff {j : ℕ} {F : E → E [×j]→L[ℝ] ℝ} (hF : ContDiff ℝ 2 F) (x0 : E) (Λ : H →L[ℝ] E)
    (w : Fin j → E) : ContDiff ℝ 2 (S7PIL_psi F x0 Λ w) := by
  have hG : ContDiff ℝ 2 (fun z => F (x0 + z)) := hF.comp (contDiff_const.add contDiff_id)
  rw [S7PIL_psi_eq]
  exact (S7PIL_ev w).contDiff.comp (hG.comp Λ.contDiff)

/-- The second derivative of the section is the second derivative of `F` on `Λa, Λb`, applied to `w`. -/
theorem S7PIL_psi_two {j : ℕ} {F : E → E [×j]→L[ℝ] ℝ} (hF : ContDiff ℝ 2 F) (x0 : E) (Λ : H →L[ℝ] E)
    (w : Fin j → E) (c a b : H) :
    iteratedFDeriv ℝ 2 (S7PIL_psi F x0 Λ w) c ![a, b] =
      iteratedFDeriv ℝ 2 F (x0 + Λ c) ![Λ a, Λ b] w := by
  rw [S7PIL_psi_iter hF x0 Λ w c le_rfl]
  have : (fun i => Λ (![a, b] i)) = ![Λ a, Λ b] := by
    ext i; fin_cases i <;> rfl
  simp [S7PIL_ev_apply, this]

/-- `‖D^i Φ(x)‖ ≤ cbNorm k Φ` for `i ≤ k`, `Φ ∈ C_b^k`. -/
theorem S7PIL_le_cbNorm {Φ : E → ℝ} {k : ℕ} (hΦ : MemCb k Φ) {i : ℕ} (hi : i ≤ k) (x : E) :
    ‖iteratedFDeriv ℝ i Φ x‖ ≤ cbNorm k Φ := by
  unfold cbNorm
  have h1 : ‖iteratedFDeriv ℝ i Φ x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ i Φ z‖ :=
    le_ciSup (f := fun z => ‖iteratedFDeriv ℝ i Φ z‖) (hΦ.2 i hi) x
  refine h1.trans ?_
  exact Finset.single_le_sum (f := fun j => ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

theorem S7PIL_cbNorm_nonneg {Φ : E → ℝ} {k : ℕ} (hΦ : MemCb k Φ) (x : E) :
    0 ≤ cbNorm k Φ :=
  (norm_nonneg _).trans (S7PIL_le_cbNorm hΦ (Nat.zero_le k) x)

/-- `D^jΦ` is `C²` for `Φ ∈ C^5`, `j ≤ 3`. -/
theorem S7PIL_iter_contDiff {Φ : E → ℝ} (hΦ : ContDiff ℝ 5 Φ) {j : ℕ} (hj : j ≤ 3) :
    ContDiff ℝ 2 (iteratedFDeriv ℝ j Φ) := by
  refine hΦ.iteratedFDeriv_right (m := 2) (i := j) ?_
  have : ((2 : ℕ) : WithTop ℕ∞) + (j : WithTop ℕ∞) ≤ ((5 : ℕ) : WithTop ℕ∞) := by
    rw [← Nat.cast_add]; exact_mod_cast (by omega : 2 + j ≤ 5)
  simpa using this

/-- First derivative of a section of `D^kΦ`: it is the section of `D^{k+1}Φ` with the direction prepended. -/
theorem S7PIL_psi_fderiv {Φ : E → ℝ} (hΦ : ContDiff ℝ 5 Φ) {k : ℕ} (hk : k + 1 ≤ 5) (m : Fin k → E) (x0 : E)
    (Λ : H →L[ℝ] E) (c a : H) :
    fderiv ℝ (S7PIL_psi (iteratedFDeriv ℝ k Φ) x0 Λ m) c a =
      S7PIL_psi (iteratedFDeriv ℝ (k + 1) Φ) x0 Λ (Fin.cons (Λ a) m : Fin (k + 1) → E) c := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ k Φ) :=
    hΦ.differentiable_iteratedFDeriv (m := k) (by
      have : ((k : ℕ) : WithTop ℕ∞) < ((5 : ℕ) : WithTop ℕ∞) := by exact_mod_cast (by omega : k < 5)
      exact_mod_cast this)
  have h1 : HasFDerivAt (iteratedFDeriv ℝ k Φ) (fderiv ℝ (iteratedFDeriv ℝ k Φ) (x0 + Λ c)) (x0 + Λ c) :=
    (hdiff _).hasFDerivAt
  have h2 : HasFDerivAt (fun c => x0 + Λ c) Λ c := Λ.hasFDerivAt.const_add x0
  have h3 := h1.comp c h2
  have h4 := (S7PIL_ev m).hasFDerivAt.comp c h3
  have h5 : S7PIL_psi (iteratedFDeriv ℝ k Φ) x0 Λ m = (S7PIL_ev m) ∘ (iteratedFDeriv ℝ k Φ ∘ fun c => x0 + Λ c) := by
    funext c; rfl
  rw [h5, h4.fderiv]
  simp only [ContinuousLinearMap.comp_apply, S7PIL_ev_apply, S7PIL_psi]
  rw [iteratedFDeriv_succ_apply_left]
  simp [Fin.tail_cons]

/-- The second derivative of a section of `D^jΦ` in terms of `D^{j+2}Φ`. -/
theorem S7PIL_psi_two_cons {Φ : E → ℝ} (hΦ : ContDiff ℝ 5 Φ) {j : ℕ} (hj : j ≤ 3) (w : Fin j → E) (x0 : E)
    (Λ : H →L[ℝ] E) (c a b : H) :
    iteratedFDeriv ℝ 2 (S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w) c ![a, b] =
      iteratedFDeriv ℝ (j + 1 + 1) Φ (x0 + Λ c)
        (Fin.cons (Λ a) (Fin.cons (Λ b) w : Fin (j + 1) → E) : Fin (j + 1 + 1) → E) := by
  have hF := S7PIL_iter_contDiff hΦ hj
  have hψ := S7PIL_psi_contDiff hF x0 Λ w
  have hd1 : Differentiable ℝ (fderiv ℝ (S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w)) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have h6 : fderiv ℝ (fderiv ℝ (S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w)) c a b =
      fderiv ℝ (fun c' => fderiv ℝ (S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w) c' b) c a := by
    have := (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp c (hd1 c).hasFDerivAt
    rw [show (fun c' => fderiv ℝ (S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w) c' b) =
      (ContinuousLinearMap.apply ℝ ℝ b) ∘ (fderiv ℝ (S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w)) from rfl, this.fderiv]
    rfl
  rw [h6]
  have h7 : (fun c' => fderiv ℝ (S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w) c' b) =
      S7PIL_psi (iteratedFDeriv ℝ (j + 1) Φ) x0 Λ (Fin.cons (Λ b) w : Fin (j + 1) → E) := by
    funext c'; exact S7PIL_psi_fderiv hΦ (by omega) w x0 Λ c' b
  rw [h7, S7PIL_psi_fderiv hΦ (by omega)]
  rfl

/-- The bilinear form `N_x(a,b) = D^{j+2}Φ(x)[a, b, w]`. -/
def S7PIL_N {Φ : E → ℝ} (j : ℕ) (w : Fin j → E) (x : E) : E [×2]→L[ℝ] ℝ :=
  (S7PIL_ev w).compContinuousMultilinearMap (iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ j Φ) x)

theorem S7PIL_N_apply {Φ : E → ℝ} (hΦ : ContDiff ℝ 5 Φ) {j : ℕ} (hj : j ≤ 3) (w : Fin j → E) (x a b : E) :
    S7PIL_N (Φ := Φ) j w x ![a, b] =
      iteratedFDeriv ℝ (j + 1 + 1) Φ x (Fin.cons a (Fin.cons b w : Fin (j + 1) → E) : Fin (j + 1 + 1) → E) := by
  have hF := S7PIL_iter_contDiff hΦ hj
  have h1 := S7PIL_psi_two (H := E) hF 0 (ContinuousLinearMap.id ℝ E) w x a b
  have h2 := S7PIL_psi_two_cons (H := E) hΦ hj w 0 (ContinuousLinearMap.id ℝ E) x a b
  simp only [zero_add, ContinuousLinearMap.id_apply] at h1 h2
  show (S7PIL_ev w) (iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ j Φ) x ![a, b]) = _
  rw [S7PIL_ev_apply, ← h1, h2]

theorem S7PIL_N_norm_le {Φ : E → ℝ} (hΦ : ContDiff ℝ 5 Φ) {j : ℕ} (hj : j ≤ 3) (w : Fin j → E) (x : E) :
    ‖S7PIL_N (Φ := Φ) j w x‖ ≤ ‖iteratedFDeriv ℝ (j + 1 + 1) Φ x‖ * ∏ k, ‖w k‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have hm : m = ![m 0, m 1] := by
    ext i; fin_cases i <;> rfl
  rw [hm, S7PIL_N_apply hΦ hj]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  simp [Fin.prod_univ_succ, Fin.prod_univ_two]
  nlinarith [norm_nonneg (iteratedFDeriv ℝ (j + 1 + 1) Φ x)]

/-- The sections of `D^jΦ` are `C_b²` functions of `c`. -/
theorem S7PIL_psi_memCb {Φ : E → ℝ} (hΦ : MemCb 5 Φ) {j : ℕ} (hj : j ≤ 3) (x0 : E)
    (Λ : H →L[ℝ] E) (w : Fin j → E) : MemCb 2 (S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w) := by
  have hF := S7PIL_iter_contDiff hΦ.1 hj
  refine ⟨S7PIL_psi_contDiff hF x0 Λ w, fun i hi => ?_⟩
  have hcb : ∀ {k : ℕ}, k ≤ 5 → ∀ (m : Fin k → E) (y : E),
      |iteratedFDeriv ℝ k Φ y m| ≤ cbNorm 5 Φ * ∏ l, ‖m l‖ := fun {k} hk m y => by
    rw [← Real.norm_eq_abs]
    exact ((iteratedFDeriv ℝ k Φ y).le_opNorm m).trans
      (mul_le_mul_of_nonneg_right (S7PIL_le_cbNorm hΦ hk y) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  have hP : 0 ≤ ∏ l, ‖w l‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hC : 0 ≤ cbNorm 5 Φ := S7PIL_cbNorm_nonneg hΦ 0
  have hΛ : 0 ≤ ‖Λ‖ := norm_nonneg _
  refine ⟨cbNorm 5 Φ * (1 + ‖Λ‖) ^ 2 * ∏ l, ‖w l‖, ?_⟩
  rintro _ ⟨c, rfl⟩
  beta_reduce
  interval_cases i
  · rw [norm_iteratedFDeriv_zero]
    have := hcb (k := j) (by omega) w (x0 + Λ c)
    rw [← Real.norm_eq_abs] at this
    refine this.trans ?_
    show _ ≤ _
    have h1 : (1 : ℝ) ≤ (1 + ‖Λ‖) ^ 2 := by nlinarith
    nlinarith [mul_nonneg hC hP]
  · rw [norm_iteratedFDeriv_one]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
    rw [S7PIL_psi_fderiv hΦ.1 (by omega) w x0 Λ c a]
    have := hcb (k := j + 1) (by omega) (Fin.cons (Λ a) w : Fin (j + 1) → E) (x0 + Λ c)
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at this
    refine this.trans ?_
    have h2 : ‖Λ a‖ ≤ ‖Λ‖ * ‖a‖ := Λ.le_opNorm a
    have h3 : ‖Λ‖ ≤ (1 + ‖Λ‖) ^ 2 := by nlinarith
    calc cbNorm 5 Φ * (‖Λ a‖ * ∏ l, ‖w l‖) ≤ cbNorm 5 Φ * ((‖Λ‖ * ‖a‖) * ∏ l, ‖w l‖) := by gcongr
      _ ≤ cbNorm 5 Φ * (((1 + ‖Λ‖) ^ 2 * ‖a‖) * ∏ l, ‖w l‖) := by gcongr
      _ = _ := by ring
  · refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
    have hm : m = ![m 0, m 1] := by
      ext i; fin_cases i <;> rfl
    rw [hm, S7PIL_psi_two_cons hΦ.1 hj w x0 Λ c]
    have := hcb (k := j + 1 + 1) (by omega) (Fin.cons (Λ (m 0)) (Fin.cons (Λ (m 1)) w : Fin (j + 1) → E) : Fin (j + 1 + 1) → E) (x0 + Λ c)
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at this
    refine this.trans ?_
    have h2 : ‖Λ (m 0)‖ ≤ ‖Λ‖ * ‖m 0‖ := Λ.le_opNorm _
    have h2' : ‖Λ (m 1)‖ ≤ ‖Λ‖ * ‖m 1‖ := Λ.le_opNorm _
    have h4 : ‖Λ (m 0)‖ * ‖Λ (m 1)‖ ≤ (‖Λ‖ * ‖m 0‖) * (‖Λ‖ * ‖m 1‖) :=
      mul_le_mul h2 h2' (norm_nonneg _) (by positivity)
    have h5 : ‖Λ‖ ^ 2 ≤ (1 + ‖Λ‖) ^ 2 := by nlinarith
    have h6 : 0 ≤ ‖m 0‖ * ‖m 1‖ := by positivity
    have h7 : ‖Λ (m 0)‖ * (‖Λ (m 1)‖ * ∏ l, ‖w l‖) ≤ (1 + ‖Λ‖) ^ 2 * (‖m 0‖ * ‖m 1‖) * ∏ l, ‖w l‖ := by
      calc ‖Λ (m 0)‖ * (‖Λ (m 1)‖ * ∏ l, ‖w l‖) = (‖Λ (m 0)‖ * ‖Λ (m 1)‖) * ∏ l, ‖w l‖ := by ring
        _ ≤ ((‖Λ‖ * ‖m 0‖) * (‖Λ‖ * ‖m 1‖)) * ∏ l, ‖w l‖ := by gcongr
        _ = ‖Λ‖ ^ 2 * (‖m 0‖ * ‖m 1‖) * ∏ l, ‖w l‖ := by ring
        _ ≤ (1 + ‖Λ‖) ^ 2 * (‖m 0‖ * ‖m 1‖) * ∏ l, ‖w l‖ := by gcongr
    simp only [Fin.prod_univ_two]
    calc cbNorm 5 Φ * (‖Λ (m 0)‖ * (‖Λ (m 1)‖ * ∏ l, ‖w l‖)) ≤
          cbNorm 5 Φ * ((1 + ‖Λ‖) ^ 2 * (‖m 0‖ * ‖m 1‖) * ∏ l, ‖w l‖) := by gcongr
      _ = _ := by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring

end Gen

end HRS.MC.Sec7.S7PIL

end
