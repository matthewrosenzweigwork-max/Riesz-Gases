import HRS.MS.Mov63GAux16

/-!
# S6.3, packet N8 (part 17): the decay clauses at a fixed time

Namespace `HRS.MS.Mov63`, prefix `mng_`.  `mng_movU_eq`: `movU d s q β ρ_t = ν ∇log Q_t + F_t` (Euler equation of `ρ`);
**`mng_decay_at`**: at a fixed time `t ≥ 0`, `∇ log(ρ_t/ρ)` and `movU` are `C^j` and
`cbNormVecE j (∇log(ρ_t/ρ)) + cbNormVecE j (movU) ≤ ofReal(...)`, linear in `ε ≥ ‖D^i Q_t‖` and in `B_f ≥ ‖D^k F_t‖`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.PoisKolm

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Final

variable {m : ℕ} (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m)

include H hm in
lemma mng_movU_eq {u : OscSpace d (m : ℝ)} (hu : ∀ y, 0 < mneQ ρ hm u y) (hcd : ContDiff ℝ 1 (mneQ ρ hm u)) (x : Euc d) :
    movU d s q β (mneRho ρ hm u) x = β⁻¹ • gradient (fun y => Real.log (mneQ ρ hm u y)) x + mneFo d s ρ hm u x := by
  have hρpos := (mnb_rhoData H).pos
  have hlogρ : DifferentiableAt ℝ (fun y => Real.log (ρ y)) x := ((mng_logrho_cd H).differentiable (by simp)) x
  have hlogQ : DifferentiableAt ℝ (fun y => Real.log (mneQ ρ hm u y)) x :=
    ((hcd.log (fun y => (hu y).ne')).differentiable (by simp)) x
  have e : (fun y => Real.log (mneRho ρ hm u y)) = fun y => Real.log (mneQ ρ hm u y) + 1 * Real.log (ρ y) := by
    funext y
    have h1 : mneRho ρ hm u y = mneQ ρ hm u y * ρ y := by
      show mneRho ρ hm u y = mneRho ρ hm u y / ρ y * ρ y
      field_simp [(hρpos y).ne']
    rw [h1, Real.log_mul (hu y).ne' (hρpos y).ne']
    ring
  have hg : gradient (fun y => Real.log (mneRho ρ hm u y)) x =
      gradient (fun y => Real.log (mneQ ρ hm u y)) x + gradient (fun y => Real.log (ρ y)) x := by
    rw [e, mnf_gradient_add_smul hlogQ hlogρ 1, one_smul]
  have hE := mnf_euler H x
  unfold movU
  rw [hg, mne_force_split hm H u x, smul_add]
  have : β⁻¹ • gradient (fun y => Real.log (ρ y)) x + q • x + movForce d s ρ x = 0 := by
    rw [hE]; abel
  calc _ = β⁻¹ • gradient (fun y => Real.log (mneQ ρ hm u y)) x + mneFo d s ρ hm u x +
        (β⁻¹ • gradient (fun y => Real.log (ρ y)) x + q • x + movForce d s ρ x) := by abel
    _ = _ := by rw [this, add_zero]

include H hm in
theorem mng_decay_at {u : OscSpace d (m : ℝ)} {j : ℕ} (hj : 1 ≤ j)
    (hu : ∀ y, 1 / 2 ≤ mneQ ρ hm u y ∧ mneQ ρ hm u y ≤ 2) (hcd : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (mneQ ρ hm u))
    {ε Bf : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hBf0 : 0 ≤ Bf)
    (hQD : ∀ i, 1 ≤ i → i ≤ j + 1 → ∀ y, ‖iteratedFDeriv ℝ i (mneQ ρ hm u) y‖ ≤ ε)
    (hFcd : ContDiff ℝ (j : WithTop ℕ∞) (mneFo d s ρ hm u))
    (hFD : ∀ k ≤ j, ∀ y, ‖iteratedFDeriv ℝ k (mneFo d s ρ hm u) y‖ ≤ Bf) :
    ContDiff ℝ (j : WithTop ℕ∞) (fun x => gradient (fun y => Real.log (mneRho ρ hm u y / ρ y)) x) ∧
    ContDiff ℝ (j : WithTop ℕ∞) (movU d s q β (mneRho ρ hm u)) ∧
    cbNormVecE j (fun x => gradient (fun y => Real.log (mneRho ρ hm u y / ρ y)) x) +
        cbNormVecE j (movU d s q β (mneRho ρ hm u)) ≤
      ENNReal.ofReal (((j : ℝ) + 1) * (((j + 1).factorial : ℝ) * (1 + ((j + 1).factorial : ℝ) * 2 ^ (j + 1)) * ε) +
        ((j : ℝ) + 1) * (β⁻¹ * (((j + 1).factorial : ℝ) * (1 + ((j + 1).factorial : ℝ) * 2 ^ (j + 1)) * ε) + Bf)) := by
  have hβ := H.hβ
  set Q : Euc d → ℝ := mneQ ρ hm u with hQdef
  have hpos : ∀ y, 0 < Q y := fun y => by linarith [(hu y).1]
  have hlogcd : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fun y => Real.log (Q y)) := hcd.log (fun y => (hpos y).ne')
  have hgcd : ContDiff ℝ (j : WithTop ℕ∞) (fun x => gradient (fun y => Real.log (Q y)) x) :=
    mne_grad_cd (n := j) hlogcd
  have hU : movU d s q β (mneRho ρ hm u) = fun x => β⁻¹ • gradient (fun y => Real.log (Q y)) x + mneFo d s ρ hm u x :=
    funext fun x => mng_movU_eq H hm hpos (hcd.of_le (by exact_mod_cast (by omega : 1 ≤ j + 1))) x
  have hLB0 : 0 ≤ ((j + 1).factorial : ℝ) * (1 + ((j + 1).factorial : ℝ) * 2 ^ (j + 1)) * ε := by positivity
  set B1 : ℝ := ((j + 1).factorial : ℝ) * (1 + ((j + 1).factorial : ℝ) * 2 ^ (j + 1)) * ε with hB1
  have hLog : ∀ k ≤ j, ∀ y, ‖iteratedFDeriv ℝ k (fun x => gradient (fun y => Real.log (Q y)) x) y‖ ≤ B1 := by
    intro k hk y
    rw [mng_norm_iter_grad]
    have h1 := mng_logQ_bound (n := k + 1) (by omega) (hcd.of_le (by exact_mod_cast (by omega : k + 1 ≤ j + 1)))
      hpos y (hu y).1 (hu y).2 hε0 hε1 (fun i hi1 hik => hQD i hi1 (by omega) y)
    refine h1.trans ?_
    rw [hB1]
    have hf : ((k + 1).factorial : ℝ) ≤ ((j + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
    have hp : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : ((k + 1).factorial : ℝ) * 2 ^ (k + 1) ≤ ((j + 1).factorial : ℝ) * 2 ^ (j + 1) :=
      mul_le_mul hf hp (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_right _ hε0
    exact mul_le_mul hf (by linarith) (by positivity) (by positivity)
  have hmov : ∀ k ≤ j, ∀ y, ‖iteratedFDeriv ℝ k (movU d s q β (mneRho ρ hm u)) y‖ ≤ β⁻¹ * B1 + Bf := by
    intro k hk y
    rw [hU]
    have hc1 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun x => β⁻¹ • gradient (fun y => Real.log (Q y)) x) y :=
      ((hgcd.const_smul β⁻¹).of_le (by exact_mod_cast hk)).contDiffAt
    have hc2 : ContDiffAt ℝ (k : WithTop ℕ∞) (mneFo d s ρ hm u) y := (hFcd.of_le (by exact_mod_cast hk)).contDiffAt
    have e1 := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := k) hc1 hc2
    have e2 : iteratedFDeriv ℝ k (fun x => β⁻¹ • gradient (fun y => Real.log (Q y)) x) y =
        β⁻¹ • iteratedFDeriv ℝ k (fun x => gradient (fun y => Real.log (Q y)) x) y := by
      have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := β⁻¹) (i := k)
        (f := fun x => gradient (fun y => Real.log (Q y)) x) (x := y) ((hgcd.of_le (by exact_mod_cast hk)).contDiffAt)
      exact this
    show ‖iteratedFDeriv ℝ k ((fun x => β⁻¹ • gradient (fun y => Real.log (Q y)) x) + mneFo d s ρ hm u) y‖ ≤ _
    rw [e1, e2]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hFD k hk y))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hβ.le)]
    exact mul_le_mul_of_nonneg_left (hLog k hk y) (inv_nonneg.2 hβ.le)
  refine ⟨hgcd, by rw [hU]; exact (hgcd.const_smul β⁻¹).add hFcd, ?_⟩
  have c1 := mng_cbVecE_le (j := j) hLB0 hLog
  have c2 := mng_cbVecE_le (j := j) (by positivity : 0 ≤ β⁻¹ * B1 + Bf) hmov
  calc _ ≤ ENNReal.ofReal (((j : ℝ) + 1) * B1) + ENNReal.ofReal (((j : ℝ) + 1) * (β⁻¹ * B1 + Bf)) := add_le_add c1 c2
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]

end Final

end HRS.MS.Mov63

end
