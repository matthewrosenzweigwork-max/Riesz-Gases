/-
# TRR helper 4: thermal equation <-> `Λ w = ψ`; `Λ` is bijective; translation covariance.
-/
import HRS.Equilibrium.TRRAux3

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.TRR

variable {d : ℕ} {s β : ℝ}

section Bij

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)

include hd hs0 hsd in
lemma trr_gint : Integrable (periodicRiesz d s) := (integral_periodicRiesz hd hs0 hsd).1

lemma trr_Lam_apply (hg : Integrable (periodicRiesz d s)) (w : Cb d) (x : Torus d) :
    Lam hg β w x = w x + β * convFun (periodicRiesz d s) (Nc w) x := by
  simp [Lam, convCLM_apply]

lemma trr_Zc_eq (w : Cb d) : Zc w = ∫ y, Real.exp (w y) := by
  unfold Zc; rw [intC_apply]; simp only [expC_apply]

lemma trr_thermal_of_lam (hg : Integrable (periodicRiesz d s)) (hβ : 0 < β) (w ψ : Cb d)
    (hw : Lam hg β w = ψ) :
    IsThermalDensity (periodicRiesz d s) (fun x => -(ψ x) / β) β (Nc w) := by
  refine ⟨trr_isProb_Nc w, fun x => ?_⟩
  have hx : ∀ y, -β * (-(ψ y) / β + convFun (periodicRiesz d s) (Nc w) y) = w y := fun y => by
    have := trr_Lam_apply (β := β) hg w y
    rw [hw] at this
    field_simp
    linarith
  simp only [hx]
  rw [Nc_apply, trr_Zc_eq]

lemma trr_lam_of_thermal (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hg : Integrable (periodicRiesz d s))
    (hβ : 0 < β) (ψ : Cb d) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) (fun x => -(ψ x) / β) β ρ) (hρc : Continuous ρ) :
    ∃ w : Cb d, (Nc w : Torus d → ℝ) = ρ ∧ Lam hg β w = ψ := by
  obtain ⟨hpos, -⟩ := Q41.q41_thermal_pos_cont hd hs0 hsd hβ
    ((ψ.continuous.neg).div_const β) hρ
  have hcont : Continuous fun x => -β * (-(ψ x) / β + convFun (periodicRiesz d s) ρ x) :=
    continuous_const.mul ((ψ.continuous.neg.div_const β).add (PDE.MFAux.continuous_convFun hg hρc))
  set w : Cb d := ⟨_, hcont⟩ with hw
  have hwx : ∀ x, w x = -β * (-(ψ x) / β + convFun (periodicRiesz d s) ρ x) := fun x => rfl
  have hN : (Nc w : Torus d → ℝ) = ρ := by
    funext x
    rw [Nc_apply, trr_Zc_eq, hρ.2 x]
    simp only [hwx]
  refine ⟨w, hN, ?_⟩
  ext x
  rw [trr_Lam_apply hg, hN, hwx]
  field_simp
  ring

theorem trr_lam_inj (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hg : Integrable (periodicRiesz d s))
    (hβ : 0 < β) : Function.Injective (Lam hg β) := by
  intro w₁ w₂ h
  have t1 := trr_thermal_of_lam hg hβ w₁ (Lam hg β w₁) rfl
  have t2 := trr_thermal_of_lam hg hβ w₂ (Lam hg β w₁) h.symm
  have hN := PDE.MFThermal.thermal_unique hd s hs0 hsd β hβ _ (Nc w₁) (Nc w₂) t1
    (Nc w₁).continuous (Nc_pos w₁) t2 (Nc w₂).continuous (Nc_pos w₂)
  ext x
  have e1 := trr_Lam_apply (β := β) hg w₁ x
  have e2 := trr_Lam_apply (β := β) hg w₂ x
  rw [h] at e1
  have hN' : (Nc w₂ : Torus d → ℝ) = Nc w₁ := hN
  rw [hN'] at e2
  linarith

theorem trr_lam_surj (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hg : Integrable (periodicRiesz d s))
    (hβ : 0 < β) : Function.Surjective (Lam hg β) := by
  intro ψ
  obtain ⟨ρ, hρ, hc, -⟩ := PDE.MFThermalAssembly.thermal_exists_continuous (by omega) s hs0 hsd
    (fun x => -(ψ x) / β) ((ψ.continuous.neg).div_const β) β hβ
  obtain ⟨w, -, hw⟩ := trr_lam_of_thermal hd hs0 hsd hg hβ ψ ρ hρ hc
  exact ⟨w, hw⟩

/-- the global inverse of `Λ` -/
def Wsol (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) : Cb d → Cb d :=
  Function.surjInv (trr_lam_surj (β := β) hd hs0 hsd (trr_gint hd hs0 hsd) hβ)

theorem Wsol_spec (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (ψ : Cb d) :
    Lam (trr_gint hd hs0 hsd) β (Wsol hd hs0 hsd hβ ψ) = ψ :=
  Function.surjInv_eq (trr_lam_surj (β := β) hd hs0 hsd (trr_gint hd hs0 hsd) hβ) ψ

theorem Wsol_unique (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (ψ w : Cb d)
    (hw : Lam (trr_gint hd hs0 hsd) β w = ψ) : w = Wsol hd hs0 hsd hβ ψ :=
  trr_lam_inj hd hs0 hsd (trr_gint hd hs0 hsd) hβ (hw.trans (Wsol_spec hd hs0 hsd hβ ψ).symm)

theorem contDiff_Wsol (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) :
    ContDiff ℝ InfOrd (Wsol hd hs0 hsd hβ) := by
  refine contDiff_iff_contDiffAt.2 fun ψ₀ => ?_
  set hg := trr_gint hd hs0 hsd with hghg
  set w₀ := Wsol hd hs0 hsd hβ ψ₀ with hw₀
  obtain ⟨L, hL⟩ := trr_dlam_equiv hd hs0 hsd hβ w₀
  have hf : ContDiffAt ℝ InfOrd (Lam hg β) w₀ := (contDiff_Lam hg β).contDiffAt
  have hf' : HasFDerivAt (Lam hg β) (L : Cb d →L[ℝ] Cb d) w₀ := by
    rw [hL]; exact hasFDerivAt_Lam hg β w₀
  have hn : InfOrd ≠ 0 := by simp [InfOrd]
  have h1 := hf.to_localInverse hf' hn
  have hfw : Lam hg β w₀ = ψ₀ := Wsol_spec hd hs0 hsd hβ ψ₀
  rw [hfw] at h1
  refine h1.congr_of_eventuallyEq ?_
  have hev := (hf.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  rw [hfw] at hev
  filter_upwards [hev] with y hy
  exact (Wsol_unique hd hs0 hsd hβ y _ hy).symm

end Bij

end HRS.TRR
