import HRS.Sections.ScrnAux18

/-!
# Packet SCRN, part 19: Lipschitz bounds for gradients from sup bounds of the derivatives (no `C^0` term)

For `C²` torus functions `g` with `‖D¹ g‖ ≤ B₁`, `‖D² g‖ ≤ B₂` (of the lift, everywhere):
* `‖∇g‖ ≤ B₁`, `|∂_j g| ≤ B₁` (`scrn_grad_norm_le`);
* `∂_c g` is `‖c‖ B₂`-Lipschitz (`scrn_dirTor_lip`);
* the field `gfb2_v (-1) g = -∇g` is `B₂`-Lipschitz (`scrn_lipVF`);
* the product `∇f·∇g` is `d (G_f H_g + G_g H_f)`-Lipschitz (`scrn_prod_lip`).
In contrast to `Torus.cbNorm 2`, no bound on `‖g‖_∞` enters: this is what gives time-decaying constants.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace HRS

variable {d : ℕ}

/-- The transport field `-∇g` (equal to `gfb2_v (-1) g`). -/
def scrnV (g : Torus d → ℝ) (x : Torus d) : Euc d := -(Torus.grad g x)

lemma scrn_inner_grad_eq_dirTor (ψ : Torus d → ℝ) (c : Euc d) (x : Torus d) :
    inner ℝ (Torus.grad ψ x) c = KernelGrad.dirTor ψ c x := by
  have h1 : inner ℝ (Torus.grad ψ x) c = fderiv ℝ (Torus.lift ψ) (Torus.rep x) c := by
    unfold Torus.grad
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
  rw [h1]
  have h2 := congrFun (KernelGrad.lift_dirTor ψ c) (Torus.rep x)
  simp only [Torus.lift, Function.comp, Torus.mk_rep] at h2
  exact h2.symm

lemma scrn_grad_norm_le {g : Torus d → ℝ} {B₁ : ℝ}
    (hB : ∀ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift g) y‖ ≤ B₁) (x : Torus d) :
    ‖Torus.grad g x‖ ≤ B₁ := by
  unfold Torus.grad gradient
  rw [LinearIsometryEquiv.norm_map, ← KernelGrad.norm_iteratedFDeriv_one']
  exact hB _

lemma scrn_abs_partialDeriv_le {g : Torus d → ℝ} {B₁ : ℝ}
    (hB : ∀ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift g) y‖ ≤ B₁) (j : Fin d) (x : Torus d) :
    |Torus.partialDeriv j g x| ≤ B₁ := by
  have h := scrn_grad_norm_le hB x
  have e : Torus.partialDeriv j g x = (Torus.grad g x) j := by
    unfold Torus.grad Torus.partialDeriv
    have h0 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single j (1 : ℝ))
      (y := fderiv ℝ (Torus.lift g) (Torus.rep x))
    have e1 : gradient (Torus.lift g) (Torus.rep x) = (InnerProductSpace.toDual ℝ (Euc d)).symm
        (fderiv ℝ (Torus.lift g) (Torus.rep x)) := rfl
    rw [e1]
    generalize (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (Torus.lift g) (Torus.rep x)) = G
      at h0 ⊢
    rw [EuclideanSpace.inner_single_right] at h0
    simpa using h0.symm
  rw [e]
  have := PiLp.norm_apply_le (Torus.grad g x) j
  rw [Real.norm_eq_abs] at this
  exact this.trans h

lemma scrn_dirTor_lip {g : Torus d → ℝ} (hg : Torus.IsCk 2 g) {B₂ : ℝ}
    (hB : ∀ y : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift g) y‖ ≤ B₂) (c : Euc d) :
    KernelGrad.IsLipschitz (‖c‖ * B₂) (KernelGrad.dirTor g c) := by
  intro x y
  have htd : 0 ≤ KernelGrad.tdist x y := by unfold KernelGrad.tdist; exact norm_nonneg _
  have hB0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB 0)
  by_cases hc : c = 0
  · subst hc
    have : KernelGrad.dirTor g (0 : Euc d) = fun _ => 0 := by
      funext z; simp [KernelGrad.dirTor, KernelGrad.Dtor]
    simp [this]
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
  set w : Euc d := ‖c‖⁻¹ • c with hw
  have hwn : ‖w‖ ≤ 1 := by
    rw [hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hcn.ne']
  have hdir : KernelGrad.dirTor g c = fun z => ‖c‖ * KernelGrad.dirTor g w z := by
    funext z
    have : c = ‖c‖ • w := by rw [hw, smul_smul, mul_inv_cancel₀ hcn.ne', one_smul]
    conv_lhs => rw [this]
    simp [KernelGrad.dirTor, KernelGrad.Dtor, map_smul]
  have h2 : Torus.IsCk 1 (KernelGrad.dirTor g w) := by
    have h2' : Torus.IsCk ((1 + 1 : ℕ) : WithTop ℕ∞) g := by exact_mod_cast hg
    exact_mod_cast KernelGrad.isCk_dirTor h2' w
  have hL : KernelGrad.IsLipschitz B₂ (KernelGrad.dirTor g w) := by
    refine KernelGrad.isLipschitz_of_fderiv_le h2 fun y => ?_
    rw [← KernelGrad.norm_iteratedFDeriv_one' (f := Torus.lift (KernelGrad.dirTor g w))]
    have hD : ContDiffAt ℝ 1 (fderiv ℝ (Torus.lift g)) y := by
      have h2'' : Torus.IsCk ((1 + 1 : ℕ) : WithTop ℕ∞) g := by exact_mod_cast hg
      have := KernelGrad.isCk_Dtor h2''
      unfold Torus.IsCk at this
      rw [KernelGrad.lift_Dtor] at this
      exact this.contDiffAt
    rw [KernelGrad.lift_dirTor]
    have h1 := (ContinuousLinearMap.apply ℝ ℝ w).norm_iteratedFDeriv_comp_left hD (n := 1)
      (by exact_mod_cast le_rfl)
    have h3 : ‖ContinuousLinearMap.apply ℝ ℝ w‖ ≤ ‖w‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
      simpa [mul_comm] using f.le_opNorm w
    calc ‖iteratedFDeriv ℝ 1 (fun y => (fderiv ℝ (Torus.lift g)) y w) y‖
        = ‖iteratedFDeriv ℝ 1 ((ContinuousLinearMap.apply ℝ ℝ w) ∘ fderiv ℝ (Torus.lift g)) y‖ := rfl
      _ ≤ ‖ContinuousLinearMap.apply ℝ ℝ w‖ * ‖iteratedFDeriv ℝ 1 (fderiv ℝ (Torus.lift g)) y‖ := h1
      _ ≤ 1 * ‖iteratedFDeriv ℝ 1 (fderiv ℝ (Torus.lift g)) y‖ := by
          gcongr; exact h3.trans hwn
      _ = ‖iteratedFDeriv ℝ 2 (Torus.lift g) y‖ := by
          rw [one_mul, norm_iteratedFDeriv_fderiv]
      _ ≤ B₂ := hB y
  rw [hdir]
  simp only
  rw [← mul_sub, abs_mul, abs_of_pos hcn, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hL x y) hcn.le

lemma scrn_lipVF {g : Torus d → ℝ} (hg : Torus.IsCk 2 g) {B₂ : ℝ}
    (hB : ∀ y : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift g) y‖ ≤ B₂) :
    IsLipschitzVF B₂ (scrnV g) := by
  intro x y
  set u : Euc d := Torus.grad g x - Torus.grad g y with hu
  have hnu : ‖scrnV g x - scrnV g y‖ = ‖u‖ := by
    unfold scrnV
    rw [hu, ← norm_neg]; congr 1; abel
  rw [hnu]
  have htd : 0 ≤ KernelGrad.tdist x y := by unfold KernelGrad.tdist; exact norm_nonneg _
  have hB0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB 0)
  by_cases h0 : u = 0
  · rw [h0, norm_zero]
    exact mul_nonneg hB0 htd
  have hun : 0 < ‖u‖ := norm_pos_iff.2 h0
  set e : Euc d := ‖u‖⁻¹ • u with he
  have hen : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hun.ne']
  have hue : inner ℝ u e = ‖u‖ := by
    rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have h1 : inner ℝ u e = KernelGrad.dirTor g e x - KernelGrad.dirTor g e y := by
    rw [hu, inner_sub_left, scrn_inner_grad_eq_dirTor, scrn_inner_grad_eq_dirTor]
  have h2 := scrn_dirTor_lip hg hB e x y
  calc ‖u‖ = inner ℝ u e := hue.symm
    _ = KernelGrad.dirTor g e x - KernelGrad.dirTor g e y := h1
    _ ≤ |KernelGrad.dirTor g e x - KernelGrad.dirTor g e y| := le_abs_self _
    _ ≤ ‖e‖ * B₂ * KernelGrad.tdist x y := h2
    _ = B₂ * KernelGrad.tdist x y := by rw [hen]; ring

lemma scrn_partialDeriv_eq_dirTor (f : Torus d → ℝ) (j : Fin d) :
    Torus.partialDeriv j f = KernelGrad.dirTor f (EuclideanSpace.single j (1 : ℝ)) := by
  funext x
  rw [← scrn_inner_grad_eq_dirTor f _ x]
  have h0 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single j (1 : ℝ))
    (y := fderiv ℝ (Torus.lift f) (Torus.rep x))
  unfold Torus.grad Torus.partialDeriv
  have e1 : gradient (Torus.lift f) (Torus.rep x) = (InnerProductSpace.toDual ℝ (Euc d)).symm
      (fderiv ℝ (Torus.lift f) (Torus.rep x)) := rfl
  rw [e1]
  generalize (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (Torus.lift f) (Torus.rep x)) = G
    at h0 ⊢
  rw [EuclideanSpace.inner_single_right] at h0
  simpa [EuclideanSpace.inner_single_right] using h0.symm

lemma scrn_inner_grad (f g : Torus d → ℝ) (x : Torus d) :
    inner ℝ (Torus.grad f x) (Torus.grad g x) =
      ∑ j, Torus.partialDeriv j f x * Torus.partialDeriv j g x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∀ h : Torus d → ℝ, (Torus.grad h x) j = Torus.partialDeriv j h x := by
    intro h
    have h1 := scrn_inner_grad_eq_dirTor h (EuclideanSpace.single j (1 : ℝ)) x
    rw [← scrn_partialDeriv_eq_dirTor] at h1
    simpa [EuclideanSpace.inner_single_right] using h1
  rw [e f, e g]
  simp [mul_comm]

lemma scrn_prod_lip {f g : Torus d → ℝ} (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g)
    {Gf Gg Hf Hg : ℝ}
    (hGf : ∀ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift f) y‖ ≤ Gf)
    (hGg : ∀ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift g) y‖ ≤ Gg)
    (hHf : ∀ y : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift f) y‖ ≤ Hf)
    (hHg : ∀ y : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift g) y‖ ≤ Hg) :
    KernelGrad.IsLipschitz ((d : ℝ) * (Gf * Hg + Gg * Hf))
      (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) := by
  intro x y
  have htd : 0 ≤ KernelGrad.tdist x y := by unfold KernelGrad.tdist; exact norm_nonneg _
  have hGf0 : 0 ≤ Gf := (norm_nonneg _).trans (hGf 0)
  have hGg0 : 0 ≤ Gg := (norm_nonneg _).trans (hGg 0)
  have hLf : ∀ j : Fin d, |Torus.partialDeriv j f x - Torus.partialDeriv j f y| ≤
      Hf * KernelGrad.tdist x y := by
    intro j
    have := scrn_dirTor_lip hf hHf (EuclideanSpace.single j (1 : ℝ)) x y
    rw [scrn_partialDeriv_eq_dirTor]
    simpa using this
  have hLg : ∀ j : Fin d, |Torus.partialDeriv j g x - Torus.partialDeriv j g y| ≤
      Hg * KernelGrad.tdist x y := by
    intro j
    have := scrn_dirTor_lip hg hHg (EuclideanSpace.single j (1 : ℝ)) x y
    rw [scrn_partialDeriv_eq_dirTor]
    simpa using this
  simp only [scrn_inner_grad]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j : Fin d, |Torus.partialDeriv j f x * Torus.partialDeriv j g x -
      Torus.partialDeriv j f y * Torus.partialDeriv j g y| ≤
      (Gf * Hg + Gg * Hf) * KernelGrad.tdist x y := by
    intro j
    have e : Torus.partialDeriv j f x * Torus.partialDeriv j g x -
        Torus.partialDeriv j f y * Torus.partialDeriv j g y =
        Torus.partialDeriv j f x * (Torus.partialDeriv j g x - Torus.partialDeriv j g y) +
        Torus.partialDeriv j g y * (Torus.partialDeriv j f x - Torus.partialDeriv j f y) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 := mul_le_mul (scrn_abs_partialDeriv_le hGf j x) (hLg j) (abs_nonneg _) hGf0
    have h2 := mul_le_mul (scrn_abs_partialDeriv_le hGg j y) (hLf j) (abs_nonneg _) hGg0
    nlinarith
  calc ∑ j : Fin d, |Torus.partialDeriv j f x * Torus.partialDeriv j g x -
        Torus.partialDeriv j f y * Torus.partialDeriv j g y|
      ≤ ∑ _j : Fin d, (Gf * Hg + Gg * Hf) * KernelGrad.tdist x y :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (d : ℝ) * (Gf * Hg + Gg * Hf) * KernelGrad.tdist x y := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end HRS
