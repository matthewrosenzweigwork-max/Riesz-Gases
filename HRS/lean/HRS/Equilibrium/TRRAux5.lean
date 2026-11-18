/-
# TRR helper 5: translation covariance, the density curve, joint smoothness (clause 1).
-/
import HRS.Equilibrium.TRRAux4

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.TRR

variable {d : ℕ} {s β : ℝ}

/-- translation of a continuous function -/
def shiftC (x : Torus d) (f : Cb d) : Cb d :=
  ⟨fun y => f (y + x), f.continuous.comp (continuous_id.add continuous_const)⟩

lemma shiftC_apply (x : Torus d) (f : Cb d) (y : Torus d) : shiftC x f y = f (y + x) := rfl

def cosC (k : Lattice d) : Cb d := ⟨Torus.cosMode k, Torus.continuous_cosMode k⟩
def sinC (k : Lattice d) : Cb d := ⟨Torus.sinMode k, Torus.continuous_sinMode k⟩

lemma trr_mode_add (k : Lattice d) (x y : Torus d) :
    Torus.mode k (x + y) = Torus.mode k x * Torus.mode k y := by
  unfold Torus.mode UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul, Finset.prod_mul_distrib]

lemma trr_cos_add (k : Lattice d) (x y : Torus d) :
    Torus.cosMode k (y + x) = Torus.cosMode k y * Torus.cosMode k x -
      Torus.sinMode k y * Torus.sinMode k x := by
  simp [Torus.cosMode, Torus.sinMode, trr_mode_add, Complex.mul_re]

lemma shiftC_cos (k : Lattice d) (θ : ℝ) (x : Torus d) :
    shiftC x (θ • cosC k) = (θ * Torus.cosMode k x) • cosC k + (-(θ * Torus.sinMode k x)) • sinC k := by
  ext y
  simp only [shiftC_apply, ContinuousMap.smul_apply, cosC, sinC, ContinuousMap.coe_mk,
    ContinuousMap.add_apply, smul_eq_mul, trr_cos_add]
  ring

section Cov

variable {g : Torus d → ℝ}

lemma shiftC_conv (hg : Integrable g) (x : Torus d) (v : Cb d) (y : Torus d) :
    convFun g (shiftC x v) y = convFun g v (y + x) := by
  unfold convFun
  rw [← integral_add_right_eq_self (fun z => g (y + x - z) * v z) x]
  congr 1; funext z
  simp only [shiftC_apply, add_sub_add_right_eq_sub]

lemma Zc_shift (x : Torus d) (w : Cb d) : Zc (shiftC x w) = Zc w := by
  rw [trr_Zc_eq, trr_Zc_eq]
  exact integral_add_right_eq_self (fun y => Real.exp (w y)) x

lemma Nc_shift (x : Torus d) (w : Cb d) : Nc (shiftC x w) = shiftC x (Nc w) := by
  ext y
  rw [Nc_apply, Zc_shift]
  show _ = Nc w (y + x)
  rw [Nc_apply]; rfl

end Cov

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)

lemma Lam_shift (hg : Integrable (periodicRiesz d s)) (x : Torus d) (w : Cb d) :
    Lam hg β (shiftC x w) = shiftC x (Lam hg β w) := by
  ext y
  rw [trr_Lam_apply hg, Nc_shift, shiftC_conv hg]
  show _ = Lam hg β w (y + x)
  rw [trr_Lam_apply hg]; rfl

include hd hs0 hsd in
lemma Wsol_shift (hβ : 0 < β) (x : Torus d) (ψ : Cb d) :
    shiftC x (Wsol hd hs0 hsd hβ ψ) = Wsol hd hs0 hsd hβ (shiftC x ψ) :=
  Wsol_unique hd hs0 hsd hβ _ _ (by
    rw [Lam_shift (trr_gint hd hs0 hsd), Wsol_spec])


section Family

lemma trr_rateV_eq (k : Lattice d) (β θ : ℝ) :
    rateV k β θ = fun x => -((θ • cosC k) x) / β := by
  funext x; simp [rateV, cosC]

include hd hs0 hsd in
lemma trr_rho_eq (k : Lattice d) (θ : ℝ) {ρ : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d s) (rateV k β θ) β ρ) :
    ρ = Nc (Wsol hd hs0 hsd hβ (θ • cosC k)) := by
  rw [trr_rateV_eq] at hρ
  have hVc : Continuous fun x : Torus d => -((θ • cosC k) x) / β :=
    ((θ • cosC k).continuous.neg).div_const β
  obtain ⟨-, hc⟩ := Q41.q41_thermal_pos_cont hd hs0 hsd hβ hVc hρ
  obtain ⟨w, hN, hw⟩ := trr_lam_of_thermal hd hs0 hsd (trr_gint hd hs0 hsd) hβ _ ρ hρ hc
  rw [← hN, Wsol_unique hd hs0 hsd hβ _ w hw]

/-- the two-parameter solution profile -/
def Phi (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (k : Lattice d) (p : ℝ × ℝ) : ℝ :=
  Nc (Wsol hd hs0 hsd hβ (p.1 • cosC k + p.2 • sinC k)) 0

lemma contDiff_Phi (k : Lattice d) : ContDiff ℝ InfOrd (Phi hd hs0 hsd hβ k) := by
  have h1 : ContDiff ℝ InfOrd (fun p : ℝ × ℝ => p.1 • cosC k + p.2 • sinC k) :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  have h2 := (ContinuousMap.evalCLM ℝ (0 : Torus d)).contDiff.comp
    (contDiff_Nc.comp ((contDiff_Wsol hd hs0 hsd hβ).comp h1))
  exact h2

lemma trr_dot_contDiff (k : Lattice d) : ContDiff ℝ InfOrd (fun y : Euc d => Lattice.dot k y) := by
  unfold Lattice.dot
  refine ContDiff.sum fun i _ => ?_
  exact contDiff_const.mul ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff)

include hd hs0 hsd in
lemma trr_rho_apply (k : Lattice d) (θ : ℝ) {ρ : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d s) (rateV k β θ) β ρ) (x : Torus d) :
    ρ x = Phi hd hs0 hsd hβ k (θ * Torus.cosMode k x, -(θ * Torus.sinMode k x)) := by
  rw [trr_rho_eq hd hs0 hsd hβ k θ hρ]
  have : Nc (Wsol hd hs0 hsd hβ (θ • cosC k)) x =
      shiftC x (Nc (Wsol hd hs0 hsd hβ (θ • cosC k))) 0 := by
    simp [shiftC_apply]
  rw [this, ← Nc_shift, Wsol_shift hd hs0 hsd hβ, shiftC_cos]
  rfl

theorem trr_clause1 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (k : Lattice d)
    (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) :
    ContDiff ℝ InfOrd (fun p : ℝ × Euc d => ρ p.1 (Torus.mk p.2)) := by
  have hfun : (fun p : ℝ × Euc d => ρ p.1 (Torus.mk p.2)) = fun p =>
      Phi hd hs0 hsd hβ k (p.1 * Real.cos (2 * Real.pi * Lattice.dot k p.2),
        -(p.1 * Real.sin (2 * Real.pi * Lattice.dot k p.2))) := by
    funext p
    rw [trr_rho_apply hd hs0 hsd hβ k p.1 (hρ p.1), Torus.cosMode_mk, Torus.sinMode_mk]
  rw [hfun]
  have hdot : ContDiff ℝ InfOrd (fun p : ℝ × Euc d => 2 * Real.pi * Lattice.dot k p.2) :=
    contDiff_const.mul ((trr_dot_contDiff k).comp contDiff_snd)
  refine (contDiff_Phi hd hs0 hsd hβ k).comp (ContDiff.prodMk ?_ ?_)
  · exact contDiff_fst.mul (Real.contDiff_cos.comp hdot)
  · exact (contDiff_fst.mul (Real.contDiff_sin.comp hdot)).neg

end Family

end HRS.TRR
