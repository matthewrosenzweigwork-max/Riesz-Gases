import HRS.MS.Mov63GAux11

/-!
# S6.3, packet N8 (part 12): the core estimate `‖D^i Q_t‖ ≤ C K e^{-ct}`

Namespace `HRS.MS.Mov63`, prefix `mng_`.  Helper lemmas (`mng_lip_of_fderiv`, `mng_S_le_norm_sq`, the drift identity and the form of the
`Q`-equation needed by `mng_lip_decay`).  The core theorem `mng_core` combines: the Lipschitz decay (`mng_lip_decay`, stage A), the growth
(`mng_crude`, `mng_growth_iter`) and the Bernstein cascade (`mng_cascade`, stage B).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.PoisKolm

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

lemma mng_lip_of_fderiv {g : Euc d → ℝ} (hg : Differentiable ℝ g) {M : ℝ} (h : ∀ y, ‖fderiv ℝ g y‖ ≤ M)
    (x y : Euc d) : |g x - g y| ≤ M * ‖x - y‖ := by
  have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
    (f := g) (C := M) (fun z _ => hg z) (fun z _ => h z) (mem_univ y) (mem_univ x)
  rwa [Real.norm_eq_abs] at this

lemma mng_fderiv_le_of_lip {g : Euc d → ℝ} {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x y, |g x - g y| ≤ L * ‖x - y‖)
    (x : Euc d) : ‖fderiv ℝ g x‖ ≤ L :=
  norm_fderiv_le_of_lip' ℝ hL0 (Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact hL y x)

lemma mng_S_le_norm_sq {Q : ℝ → Euc d → ℝ} {N : ℕ} (hQ : ∀ t, ContDiff ℝ N (Q t)) {n : ℕ} (hn : n ≤ N)
    (t : ℝ) (x : Euc d) : mngS Q n t x ≤ (d : ℝ) ^ n * ‖iteratedFDeriv ℝ n (Q t) x‖ ^ 2 := by
  have hS : mngS Q n t x = ∑ σ : Fin n → Fin d, (mngJt Q (List.ofFn σ) t x) ^ 2 := by
    unfold mngS
    rw [mng_sum_vector (fun l => mngJt Q l t x * mngJt Q l t x)]
    exact Finset.sum_congr rfl fun σ _ => (sq _).symm
  rw [hS]
  have h1 : ∀ σ : Fin n → Fin d, (mngJt Q (List.ofFn σ) t x) ^ 2 ≤ ‖iteratedFDeriv ℝ n (Q t) x‖ ^ 2 := fun σ => by
    rw [← sq_abs (mngJt Q (List.ofFn σ) t x)]
    exact pow_le_pow_left₀ (abs_nonneg _) (mng_jt_sq_le hQ hn σ t x) 2
  calc ∑ σ : Fin n → Fin d, (mngJt Q (List.ofFn σ) t x) ^ 2 ≤ ∑ σ : Fin n → Fin d, ‖iteratedFDeriv ℝ n (Q t) x‖ ^ 2 :=
        Finset.sum_le_sum fun σ _ => h1 σ
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]
section LipConc

variable {m : ℕ} (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m)

include H hm in
lemma mng_Q_cd {N : ℕ} (hN : (d : ℝ) / 2 + N + 2 < m) (u : OscSpace d (m : ℝ)) :
    ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) (mneQ ρ hm u) := by
  obtain ⟨C0, hC00, hU⟩ := mng_unif H hm hN
  rw [mng_Q_eq H hm u]
  exact contDiff_const.add (((mngW_cd H).of_le (mng_cast_le_infty _)).mul (hU u).1)

lemma mng_Qeq_form {B : Euc d → Euc d} (hR : HRS.MS.Gap.GapRef d ρ (β * q) B) (hβ : 0 < β)
    (u : OscSpace d (m : ℝ)) (x : Euc d) :
    β⁻¹ * Laplacian.laplacian (mneQ ρ hm u) x +
      inner ℝ (β⁻¹ • gradient (fun y => Real.log (ρ y)) x + mneFo d s ρ hm u x) (gradient (mneQ ρ hm u) x) +
      (movDiv (mneFo d s ρ hm u) x + inner ℝ (gradient (fun y => Real.log (ρ y)) x) (mneFo d s ρ hm u x)) *
        mneQ ρ hm u x =
    β⁻¹ * kolmL (β * q) (fun z => B z + β • mneFo d s ρ hm u z) (mneQ ρ hm u) x +
      mnfA d s ρ hm u x * mneQ ρ hm u x := by
  have hb : β⁻¹ • gradient (fun y => Real.log (ρ y)) x + mneFo d s ρ hm u x =
      β⁻¹ • (-(β * q) • x + (B x + β • mneFo d s ρ hm u x)) := by
    have e : β⁻¹ • (β • mneFo d s ρ hm u x) = mneFo d s ρ hm u x := by
      rw [smul_smul, inv_mul_cancel₀ hβ.ne', one_smul]
    rw [HRS.MS.Mov0.mov0_grad_log hR x]
    simp only [smul_add, e]
    abel
  unfold kolmL
  rw [hb, inner_smul_left]
  simp only [mnfA, conj_trivial]
  ring

end LipConc


end HRS.MS.Mov63

end
