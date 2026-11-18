/-
# TRR helper 9: the point `θ = 0` (ρ_0 = 1, ∂_θρ_0 = cos/(1+βĝ)).
-/
import HRS.Equilibrium.TRRAux8
import HRS.Equilibrium.StaticLimitsAux
import HRS.Main.Q42Aux1

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.TRR

variable {d : ℕ} {s β : ℝ}

lemma Nc_zero : Nc (0 : Cb d) = 1 := by
  ext x
  rw [Nc_apply, trr_Zc_eq]
  simp

lemma conv_one (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (x : Torus d) :
    convFun (periodicRiesz d s) (fun _ => (1 : ℝ)) x = 0 := by
  unfold convFun
  simp only [mul_one]
  rw [integral_sub_left_eq_self (fun y => periodicRiesz d s y) volume x]
  exact (integral_periodicRiesz hd hs0 hsd).2

section Zero

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (k : Lattice d)

lemma Lam_zero : Lam (trr_gint hd hs0 hsd) β (0 : Cb d) = 0 := by
  ext x
  rw [trr_Lam_apply (trr_gint hd hs0 hsd), Nc_zero]
  have := conv_one hd hs0 hsd (s := s) x
  have e : ((1 : Cb d) : Torus d → ℝ) = fun _ => (1 : ℝ) := rfl
  rw [e, this]; simp

lemma Wc_zero : Wc hd hs0 hsd hβ k 0 = 0 := by
  unfold Wc
  rw [zero_smul]
  exact (Wsol_unique hd hs0 hsd hβ 0 0 (Lam_zero hd hs0 hsd)).symm

lemma Rc_zero : Rc hd hs0 hsd hβ k 0 = 1 := by
  unfold Rc
  rw [Wc_zero hd hs0 hsd hβ k, Nc_zero]


lemma intC_cosC (hk : k ≠ 0) : intC (cosC k) = 0 := by
  rw [intC_apply]
  have := q42_integral_cosMode k
  rw [if_neg hk] at this
  exact this

lemma Dlam_zero_cos (hk : k ≠ 0) (a : ℝ) :
    Dlam (trr_gint hd hs0 hsd) β (0 : Cb d) (a • cosC k) =
      (a * (1 + β * rieszCoeff d s k)) • cosC k := by
  ext x
  rw [trr_Dlam_apply, Nc_zero]
  have hi : intC ((1 : Cb d) * (a • cosC k)) = 0 := by
    rw [one_mul, map_smul, intC_cosC k hk, smul_zero]
  rw [hi]
  have hc : convFun (periodicRiesz d s) (fun y => (1 : Cb d) y * ((a • cosC k) y - 0)) x =
      a * (rieszCoeff d s k * Torus.cosMode k x) := by
    unfold convFun
    rw [← StaticLimitsAux.conv_cos hd hs0 hsd k x, ← integral_const_mul]
    congr 1; funext y
    simp [cosC]; ring
  rw [hc]
  simp [cosC]
  ring

lemma Wd_zero (hk : k ≠ 0) :
    Wd hd hs0 hsd hβ k 0 = (1 + β * rieszCoeff d s k)⁻¹ • cosC k := by
  have hpos : 0 < 1 + β * rieszCoeff d s k := by
    have := rieszCoeff_pos hd hs0 hsd k hk
    positivity
  have h1 := Wd_eq hd hs0 hsd hβ k 0
  rw [Wc_zero hd hs0 hsd hβ k] at h1
  have h2 := Dlam_zero_cos hd hs0 hsd (β := β) k hk (1 + β * rieszCoeff d s k)⁻¹
  rw [inv_mul_cancel₀ hpos.ne', one_smul] at h2
  have h3 : Dlam (trr_gint hd hs0 hsd) β (0 : Cb d)
      (Wd hd hs0 hsd hβ k 0 - (1 + β * rieszCoeff d s k)⁻¹ • cosC k) = 0 := by
    rw [map_sub, h1, h2, sub_self]
  exact sub_eq_zero.1 (trr_dlam_injective hd hs0 hsd hβ 0 _ h3)


lemma intC_cos_sq (hk : k ≠ 0) : intC (cosC k * cosC k) = 1 / 2 := by
  rw [intC_apply]
  have hint : ∀ a : Lattice d, Integrable (fun x : Torus d => Torus.cosMode a x) := fun a =>
    (Torus.continuous_cosMode a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e : ∀ x, (cosC k * cosC k) x = (Torus.cosMode (k + k) x + Torus.cosMode (k - k) x) / 2 :=
    fun x => q42_cosMode_mul k k x
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall e)) ?_
  rw [integral_div, integral_add (hint _) (hint _), q42_integral_cosMode, q42_integral_cosMode]
  have h2 : ¬ (k + k = 0) := fun h => hk (by
    funext i
    have := congrFun h i
    simp at this ⊢
    omega)
  simp [h2]

lemma Rd_zero (hk : k ≠ 0) :
    Nder (Wc hd hs0 hsd hβ k 0) (Wd hd hs0 hsd hβ k 0) =
      (1 + β * rieszCoeff d s k)⁻¹ • cosC k := by
  ext x
  rw [trr_Nder_apply, Wc_zero hd hs0 hsd hβ k, Nc_zero, Wd_zero hd hs0 hsd hβ k hk]
  have hi : intC ((1 : Cb d) * ((1 + β * rieszCoeff d s k)⁻¹ • cosC k)) = 0 := by
    rw [one_mul, map_smul, intC_cosC k hk, smul_zero]
  rw [hi]
  simp

lemma intC_Rd_zero (θ : ℝ) : intC (Nder (Wc hd hs0 hsd hβ k θ) (Wd hd hs0 hsd hβ k θ)) = 0 := by
  have h1 := intC.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_Rc hd hs0 hsd hβ k θ)
  have e : (⇑intC ∘ Rc hd hs0 hsd hβ k) = fun _ => (1 : ℝ) := funext fun θ' => by
    simp only [Function.comp_apply, Rc, intC_Nc]
  rw [e] at h1
  exact h1.unique (hasDerivAt_const θ 1)

lemma intC_Rdd_zero :
    intC (deriv (deriv (Rc hd hs0 hsd hβ k)) 0) = 0 := by
  have hd1 : Differentiable ℝ (deriv (Rc hd hs0 hsd hβ k)) :=
    (contDiff_deriv_Rc hd hs0 hsd hβ k).differentiable (by simp [InfOrd])
  have h1 := intC.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd1 0).hasDerivAt
  have e : (⇑intC ∘ deriv (Rc hd hs0 hsd hβ k)) = fun _ => (0 : ℝ) := funext fun θ' => by
    simp only [Function.comp_apply]
    rw [(hasDerivAt_Rc hd hs0 hsd hβ k θ').deriv]
    exact intC_Rd_zero hd hs0 hsd hβ k θ'
  rw [e] at h1
  exact h1.unique (hasDerivAt_const (0 : ℝ) 0)

lemma Psi_zero (hk : k ≠ 0) : Psi hd hs0 hsd hβ k 0 = 0 := by
  unfold Psi
  rw [Rc_zero hd hs0 hsd hβ k, Rd_zero hd hs0 hsd hβ k hk, one_mul, map_smul,
    intC_cosC k hk, smul_zero]

lemma hasDerivAt_Psi_zero (hk : k ≠ 0) :
    HasDerivAt (Psi hd hs0 hsd hβ k) ((1 + β * rieszCoeff d s k)⁻¹ ^ 2 / 2) 0 := by
  have hd1 : Differentiable ℝ (deriv (Rc hd hs0 hsd hβ k)) :=
    (contDiff_deriv_Rc hd hs0 hsd hβ k).differentiable (by simp [InfOrd])
  have hR : HasDerivAt (Rc hd hs0 hsd hβ k) (deriv (Rc hd hs0 hsd hβ k) 0) 0 := by
    exact (((contDiff_Rc hd hs0 hsd hβ k).differentiable (by simp [InfOrd])) 0).hasDerivAt
  have hprod := hR.mul (hd1 0).hasDerivAt
  have h1 := intC.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hprod
  have e : Psi hd hs0 hsd hβ k = ⇑intC ∘ fun y => Rc hd hs0 hsd hβ k y * deriv (Rc hd hs0 hsd hβ k) y :=
    funext (Psi_eq hd hs0 hsd hβ k)
  rw [e]
  convert h1 using 1
  have hD0 : deriv (Rc hd hs0 hsd hβ k) 0 = (1 + β * rieszCoeff d s k)⁻¹ • cosC k := by
    rw [(hasDerivAt_Rc hd hs0 hsd hβ k 0).deriv, Rd_zero hd hs0 hsd hβ k hk]
  rw [map_add, Rc_zero hd hs0 hsd hβ k, one_mul, intC_Rdd_zero hd hs0 hsd hβ k, add_zero, hD0]
  have : (1 + β * rieszCoeff d s k)⁻¹ • cosC k * (1 + β * rieszCoeff d s k)⁻¹ • cosC k =
      ((1 + β * rieszCoeff d s k)⁻¹ ^ 2) • (cosC k * cosC k) := by
    rw [smul_mul_smul_comm]; simp [sq]
  rw [this, map_smul, intC_cos_sq k hk]
  simp; ring

end Zero

end HRS.TRR
