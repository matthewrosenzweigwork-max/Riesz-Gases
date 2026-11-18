import HRS.MS.Mov63EAux10

/-!
# S6.3, packet N6 (part 11): the pointwise `Q`-equation

Namespace `HRS.MS.Mov63`, prefix `mne_`.  See `Mov63EAux1`.  `Q_u = ρ_u/ρ = 1 + V_u/√ρ` (`mneQ`, `C³`).  `mne_Y_eq`: `Y_u = ρ (ν∇Q_u + Q_u F_u)` (Euler
equation `mv0_thermal_force`); `mne_Q_eq`, `mne_Q_eq'`: `div Y_u/ρ = νΔQ + ⟨ν∇log ρ + F, ∇Q⟩ + (div F + ⟨∇log ρ, F⟩) Q`;
**`mne_Q_hasDeriv`**, `mne_Q_hasDerivAt`: the classical equation `∂_t Q_t(x) = ...` for every `x` and `t ≥ 0`.  No positivity is used.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section QEq

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) (H : Mov2dTh d s β q ρ)

/-- The relative density `Q_u = ρ_u / ρ = 1 + V_u/√ρ`. -/
abbrev mneQ (ρ : Euc d → ℝ) (hm : (d : ℝ) / 2 + 3 < m) (u : OscSpace d (m : ℝ)) : Euc d → ℝ :=
  fun y => mneRho ρ hm u y / ρ y

lemma mne_grad_mul {a b : Euc d → ℝ} {x : Euc d} (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    gradient (fun y => a y * b y) x = a x • gradient b x + b x • gradient a x := by
  refine ext_inner_left ℝ fun e => ?_
  rw [HRS.MS.PoisKolm.kl_inner_gradient, inner_add_right, inner_smul_right, inner_smul_right,
    HRS.MS.PoisKolm.kl_inner_gradient, HRS.MS.PoisKolm.kl_inner_gradient]
  have h : fderiv ℝ (fun y => a y * b y) x = a x • fderiv ℝ b x + b x • fderiv ℝ a x :=
    (ha.hasFDerivAt.mul hb.hasFDerivAt).fderiv
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma mne_grad_rho (H : Mov2dTh d s β q ρ) (x : Euc d) :
    gradient ρ x = ρ x • gradient (fun y => Real.log (ρ y)) x := by
  have hpos := (mnb_rhoData H).pos
  have hd : DifferentiableAt ℝ ρ x := ((mnc_rho_smooth H).differentiable (by simp)) x
  refine ext_inner_left ℝ fun e => ?_
  rw [HRS.MS.PoisKolm.kl_inner_gradient, inner_smul_right, HRS.MS.PoisKolm.kl_inner_gradient]
  exact mv1_fderiv_rho hd (hpos x) e

include H in
lemma mneQ_cd (u : OscSpace d (m : ℝ)) : ContDiff ℝ 3 (mneQ ρ hm u) :=
  (mne_rho_cd hm H u).div ((mnc_rho_smooth H).of_le (by simp)) (fun x => ((mnb_rhoData H).pos x).ne')

include H in
/-- The flux in terms of `Q_u`: `Y_u = ρ (ν ∇Q_u + Q_u F_u)` (Euler equation of `ρ`). -/
lemma mne_Y_eq (u : OscSpace d (m : ℝ)) (x : Euc d) :
    mneY d s q β ρ hm u x =
      ρ x • (β⁻¹ • gradient (mneQ ρ hm u) x + mneQ ρ hm u x • mneFo d s ρ hm u x) := by
  have hpos := (mnb_rhoData H).pos
  have hQcd := mneQ_cd hm H u
  have hQd : DifferentiableAt ℝ (mneQ ρ hm u) x := (hQcd.differentiable (by norm_num)) x
  have hρd : DifferentiableAt ℝ ρ x := ((mnc_rho_smooth H).differentiable (by simp)) x
  have hR : mneRho ρ hm u = fun y => ρ y * mneQ ρ hm u y := by
    funext y
    simp only [mneQ]
    rw [mul_div_cancel₀ _ (hpos y).ne']
  have hgrad : gradient (mneRho ρ hm u) x = ρ x • gradient (mneQ ρ hm u) x + mneQ ρ hm u x • gradient ρ x := by
    rw [hR]; exact mne_grad_mul hρd hQd
  have hgρ := mne_grad_rho H x
  have hE := HRS.MS.Mov0.mv0_thermal_force H.hd H.hs0 H.hsd H.hq H.hβ H.hρ x
  have hF := mne_force_split hm H u x
  have hRx : mneRho ρ hm u x = ρ x * mneQ ρ hm u x := congrFun hR x
  unfold mneY
  rw [hgrad, hF, hRx, hgρ]
  have hq : q • x + movForce d s ρ x = -(β⁻¹ • gradient (fun y => Real.log (ρ y)) x) := by
    have h0 : q • x + movForce d s ρ x + β⁻¹ • gradient (fun y => Real.log (ρ y)) x = 0 := by
      rw [show q • x + movForce d s ρ x + β⁻¹ • gradient (fun y => Real.log (ρ y)) x =
        β⁻¹ • gradient (fun y => Real.log (ρ y)) x + q • x + movForce d s ρ x by abel]
      exact hE
    exact eq_neg_of_add_eq_zero_left h0
  rw [← add_assoc (q • x) (movForce d s ρ x), hq]
  module


lemma mne_movDiv_const_smul (c : ℝ) {F : Euc d → Euc d} {x : Euc d} (hF : DifferentiableAt ℝ F x) :
    movDiv (fun y => c • F y) x = c * movDiv F x := by
  have := mv1_movDiv_smul (c := fun _ => c) (F := F) (x := x) (differentiableAt_const _) hF
  have h0 : fderiv ℝ (fun _ : Euc d => c) x = 0 := (hasFDerivAt_const c x).fderiv
  rw [this, h0]
  simp

include H in
/-- **The pointwise `Q`-equation** (division-free form): `div Y_u = ρ (ν ΔQ + Q div F + ⟨∇Q,F⟩) + ⟨∇ρ, ν ∇Q + Q F⟩`,
`Q = ρ_u/ρ`, `F = ∇g * (√ρ V_u)` (the force of the perturbation). -/
theorem mne_Q_eq (u : OscSpace d (m : ℝ)) (x : Euc d) :
    movDiv (mneY d s q β ρ hm u) x =
      ρ x * (β⁻¹ * Laplacian.laplacian (mneQ ρ hm u) x +
        (mneQ ρ hm u x * movDiv (mneFo d s ρ hm u) x + inner ℝ (gradient (mneQ ρ hm u) x) (mneFo d s ρ hm u x))) +
      inner ℝ (gradient ρ x) (β⁻¹ • gradient (mneQ ρ hm u) x + mneQ ρ hm u x • mneFo d s ρ hm u x) := by
  obtain ⟨C, hC0, hC⟩ := mne_force_facts (s := s) (β := β) (q := q) (ρ := ρ) hm H
  have hQcd := mneQ_cd hm H u
  have hQd : DifferentiableAt ℝ (mneQ ρ hm u) x := (hQcd.differentiable (by norm_num)) x
  have hgQ2 : ContDiff ℝ 1 (gradient (mneQ ρ hm u)) := by
    have := mne_grad_cd (n := 2) (f := mneQ ρ hm u) (by exact_mod_cast hQcd)
    exact this.of_le (by norm_num)
  have hgQd : DifferentiableAt ℝ (gradient (mneQ ρ hm u)) x := (hgQ2.differentiable (by norm_num)) x
  have hρd : DifferentiableAt ℝ ρ x := ((mnc_rho_smooth H).differentiable (by simp)) x
  have hFd : DifferentiableAt ℝ (mneFo d s ρ hm u) x := ((hC u).1.differentiable (by norm_num)) x
  have hY : mneY d s q β ρ hm u = fun y => ρ y • (β⁻¹ • gradient (mneQ ρ hm u) y +
      mneQ ρ hm u y • mneFo d s ρ hm u y) := funext (mne_Y_eq hm H u)
  have hZd : DifferentiableAt ℝ (fun y => β⁻¹ • gradient (mneQ ρ hm u) y +
      mneQ ρ hm u y • mneFo d s ρ hm u y) x := (hgQd.const_smul β⁻¹).add (hQd.smul hFd)
  rw [hY, mv1_movDiv_smul hρd hZd, mov2a_sum_fderiv_mul]
  rw [mov2a_movDiv_add (A := fun y => β⁻¹ • gradient (mneQ ρ hm u) y)
    (B := fun y => mneQ ρ hm u y • mneFo d s ρ hm u y) (hgQd.const_smul β⁻¹ : DifferentiableAt ℝ
      (fun y => β⁻¹ • gradient (mneQ ρ hm u) y) x) (hQd.smul hFd),
    mne_movDiv_const_smul β⁻¹ hgQd, mv1_movDiv_smul hQd hFd, mov2a_sum_fderiv_mul,
    HRS.MS.S98.s98_movDiv_gradient (hQcd.of_le (by norm_num)) x]

include H in
/-- The `Q`-equation in the form `∂_t Q = ν ΔQ + ⟨ν ∇log ρ + F, ∇Q⟩ + (div F + ⟨∇ log ρ, F⟩) Q`. -/
theorem mne_Q_eq' (u : OscSpace d (m : ℝ)) (x : Euc d) :
    (ρ x)⁻¹ * movDiv (mneY d s q β ρ hm u) x =
      β⁻¹ * Laplacian.laplacian (mneQ ρ hm u) x +
        inner ℝ (β⁻¹ • gradient (fun y => Real.log (ρ y)) x + mneFo d s ρ hm u x) (gradient (mneQ ρ hm u) x) +
        (movDiv (mneFo d s ρ hm u) x + inner ℝ (gradient (fun y => Real.log (ρ y)) x) (mneFo d s ρ hm u x)) *
          mneQ ρ hm u x := by
  have hpos : 0 < ρ x := (mnb_rhoData H).pos x
  rw [mne_Q_eq hm H u x, mne_grad_rho H x]
  simp only [inner_smul_left, inner_add_left, inner_add_right, inner_smul_right, conj_trivial, real_inner_comm]
  field_simp
  ring


variable {v : ℝ → OscSpace d (m : ℝ)}

include H in
/-- **Pointwise classical `Q`-equation** for the mild solution (`t ≥ 0`, right derivative at `t = 0`):
`∂_t Q_t(x) = ν ΔQ_t + ⟨ν ∇log ρ + F_t, ∇Q_t⟩ + (div F_t + ⟨∇log ρ, F_t⟩) Q_t`, `Q_t = ρ_t/ρ = 1 + V_t/√ρ`,
`F_t = ∇g * (√ρ V_t)`.  No positivity is used. -/
theorem mne_Q_hasDeriv (hmild : MneMild H hm v) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    HasDerivWithinAt (fun τ => mneQ ρ hm (v τ) x)
      (β⁻¹ * Laplacian.laplacian (mneQ ρ hm (v t)) x +
        inner ℝ (β⁻¹ • gradient (fun y => Real.log (ρ y)) x + mneFo d s ρ hm (v t) x) (gradient (mneQ ρ hm (v t)) x) +
        (movDiv (mneFo d s ρ hm (v t)) x + inner ℝ (gradient (fun y => Real.log (ρ y)) x) (mneFo d s ρ hm (v t) x)) *
          mneQ ρ hm (v t) x) (Ici 0) t := by
  rw [← mne_Q_eq' hm H (v t) x]
  have := (mne_hasDeriv hm H hmild ht x).div_const (ρ x)
  simpa [div_eq_inv_mul] using this

include H in
theorem mne_Q_hasDerivAt (hmild : MneMild H hm v) {t : ℝ} (ht : 0 < t) (x : Euc d) :
    HasDerivAt (fun τ => mneQ ρ hm (v τ) x)
      (β⁻¹ * Laplacian.laplacian (mneQ ρ hm (v t)) x +
        inner ℝ (β⁻¹ • gradient (fun y => Real.log (ρ y)) x + mneFo d s ρ hm (v t) x) (gradient (mneQ ρ hm (v t)) x) +
        (movDiv (mneFo d s ρ hm (v t)) x + inner ℝ (gradient (fun y => Real.log (ρ y)) x) (mneFo d s ρ hm (v t) x)) *
          mneQ ρ hm (v t) x) t := by
  rw [← mne_Q_eq' hm H (v t) x]
  have := (mne_hasDerivAt hm H hmild ht x).div_const (ρ x)
  simpa [div_eq_inv_mul] using this

end QEq

end HRS.MS.Mov63

end
