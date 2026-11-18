import HRS.Uniform.Q12P11
import HRS.Uniform.Q12W3c

/-!
# Q12, Peyre part 12: the Lagrangian field of the interpolation `ρ_t = (1-θ)g + θ f`
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Real

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_two_le_top : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  have e : (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) := by norm_num
  rw [e]; exact WithTop.coe_le_coe.2 le_top

lemma q12_three_le_top : (2 : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  have : ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  have e : (2 : WithTop ℕ∞) + 1 = ((3 : ℕ∞) : WithTop ℕ∞) := by norm_num
  rw [e]; exact this

/-- Data of the smooth Moser interpolation. -/
structure PeyreData (d : ℕ) where
  f : Torus d → ℝ
  g : Torus d → ℝ
  u : Torus d → ℝ
  m : ℝ
  hm : 0 < m
  hf : IsProbDensity f
  hg : IsProbDensity g
  hfs : Torus.IsSmooth f
  hgs : Torus.IsSmooth g
  hus : Torus.IsSmooth u
  hfpos : ∀ x, 0 < f x
  hgm : ∀ x, m ≤ g x
  hΔ : ∀ x, Torus.laplacian u x = g x - f x

namespace PeyreData

variable (D : PeyreData d)

/-- `θ(t) = sin²(πt/2)`. -/
def theta (t : ℝ) : ℝ := Real.sin (π * t / 2) ^ 2

/-- `θ'(t) = (π/2) sin(πt)`. -/
def theta' (t : ℝ) : ℝ := (π / 2) * Real.sin (π * t)

def rho (t : ℝ) (y : Euc d) : ℝ := (1 - theta t) * D.g (Torus.mk y) + theta t * D.f (Torus.mk y)

def gradU (y : Euc d) : Euc d := gradient (Torus.lift D.u) y

def vf (t : ℝ) (y : Euc d) : Euc d := (theta' t / D.rho t y) • D.gradU y

def rhoT (t : ℝ) (x : Torus d) : ℝ := (1 - theta t) * D.g x + theta t * D.f x

def muT (t : ℝ) : Measure (Torus d) := withDensityReal (D.rhoT t)

lemma theta_mem (t : ℝ) : 0 ≤ theta t ∧ theta t ≤ 1 := by
  unfold theta
  exact ⟨sq_nonneg _, by nlinarith [Real.sin_sq_add_cos_sq (π * t / 2), sq_nonneg (Real.cos (π * t / 2))]⟩

lemma theta_zero : theta 0 = 0 := by simp [theta]
lemma theta_one : theta 1 = 1 := by
  unfold theta
  rw [show π * 1 / 2 = π / 2 by ring, Real.sin_pi_div_two]; norm_num

lemma theta'_sq (t : ℝ) : theta' t ^ 2 = π ^ 2 * theta t * (1 - theta t) := by
  unfold theta' theta
  have h2 : Real.sin (π * t) = 2 * Real.sin (π * t / 2) * Real.cos (π * t / 2) := by
    rw [← Real.sin_two_mul]; congr 1; ring
  rw [h2]
  have := Real.sin_sq_add_cos_sq (π * t / 2)
  have hc : Real.cos (π * t / 2) ^ 2 = 1 - Real.sin (π * t / 2) ^ 2 := by linarith
  calc (π / 2 * (2 * Real.sin (π * t / 2) * Real.cos (π * t / 2))) ^ 2
      = π ^ 2 * Real.sin (π * t / 2) ^ 2 * Real.cos (π * t / 2) ^ 2 := by ring
    _ = _ := by rw [hc]

lemma rho_eq (t : ℝ) (y : Euc d) : D.rho t y = D.rhoT t (Torus.mk y) := rfl

lemma rho_rep (t : ℝ) (x : Torus d) : D.rho t (Torus.rep x) = D.rhoT t x := by
  rw [rho_eq, Torus.mk_rep]

lemma rho_per (t : ℝ) : Torus.Per (D.rho t) := fun y n => by
  show D.rhoT t (Torus.mk (y + Lattice.toEuc n)) = D.rhoT t (Torus.mk y)
  rw [Torus.mk_add, Torus.mk_toEuc, add_zero]

/-- A positive lower bound for the density along the whole path. -/
lemma exists_rho_lower : ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ D.m ∧ ∀ t x, c₀ ≤ D.rhoT t x := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Torus d))
    (Torus.continuous_of_continuous_lift (show Continuous (Torus.lift D.f) from
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift D.f) from D.hfs).continuous)).continuousOn
  refine ⟨min (D.f x₀) D.m, lt_min (D.hfpos x₀) D.hm, min_le_right _ _, fun t x => ?_⟩
  have hf : D.f x₀ ≤ D.f x := hx₀ (Set.mem_univ x)
  have hg : D.m ≤ D.g x := D.hgm x
  obtain ⟨h0, h1⟩ := theta_mem t
  have hc : min (D.f x₀) D.m ≤ D.f x := (min_le_left _ _).trans hf
  have hc' : min (D.f x₀) D.m ≤ D.g x := (min_le_right _ _).trans hg
  unfold rhoT
  nlinarith [mul_le_mul_of_nonneg_left hc' (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hc h0]


lemma contDiff_theta : ContDiff ℝ 2 theta := by
  unfold theta
  exact (Real.contDiff_sin.comp (((contDiff_const.mul contDiff_id)).div_const 2)).pow 2

lemma contDiff_theta' : ContDiff ℝ 2 theta' := by
  unfold theta'
  exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))

lemma contDiff_lift_u : ContDiff ℝ 2 (Torus.lift D.u) :=
  (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift D.u) from D.hus).of_le q12_two_le_top

lemma contDiff_lift_f : ContDiff ℝ 2 (Torus.lift D.f) :=
  (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift D.f) from D.hfs).of_le q12_two_le_top

lemma contDiff_lift_g : ContDiff ℝ 2 (Torus.lift D.g) :=
  (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift D.g) from D.hgs).of_le q12_two_le_top

lemma contDiff_gradU : ContDiff ℝ 2 D.gradU := by
  have hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift D.u) := D.hus
  have h1 : ContDiff ℝ 2 (fderiv ℝ (Torus.lift D.u)) :=
    hu.fderiv_right q12_three_le_top
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp h1

lemma contDiff_rho_joint : ContDiff ℝ 2 (fun p : ℝ × Euc d => D.rho p.1 p.2) := by
  unfold rho
  have hg : ContDiff ℝ 2 (fun p : ℝ × Euc d => D.g (Torus.mk p.2)) :=
    (D.contDiff_lift_g).comp contDiff_snd
  have hf : ContDiff ℝ 2 (fun p : ℝ × Euc d => D.f (Torus.mk p.2)) :=
    (D.contDiff_lift_f).comp contDiff_snd
  have ht : ContDiff ℝ 2 (fun p : ℝ × Euc d => theta p.1) := contDiff_theta.comp contDiff_fst
  exact ((contDiff_const.sub ht).mul hg).add (ht.mul hf)

lemma contDiff_vf_joint : ContDiff ℝ 2 (fun p : ℝ × Euc d => D.vf p.1 p.2) := by
  obtain ⟨c₀, hc₀, -, hlow⟩ := D.exists_rho_lower
  unfold vf
  have h1 : ContDiff ℝ 2 (fun p : ℝ × Euc d => theta' p.1 / D.rho p.1 p.2) :=
    (contDiff_theta'.comp contDiff_fst).div D.contDiff_rho_joint (fun p => by
      have := hlow p.1 (Torus.mk p.2)
      have h : D.rho p.1 p.2 = D.rhoT p.1 (Torus.mk p.2) := rfl
      rw [h]; exact (lt_of_lt_of_le hc₀ this).ne')
  exact h1.smul (D.contDiff_gradU.comp contDiff_snd)

lemma per_gradU : Torus.Per D.gradU := fun y n => by
  have hp : Torus.Per (Torus.lift D.u) := fun y n => by
    show D.u (Torus.mk (y + Lattice.toEuc n)) = D.u (Torus.mk y)
    rw [Torus.mk_add, Torus.mk_toEuc, add_zero]
  show gradient (Torus.lift D.u) (y + Lattice.toEuc n) = gradient (Torus.lift D.u) y
  unfold gradient
  rw [q12_per_fderiv hp]

lemma per_vf (t : ℝ) : Torus.Per (D.vf t) := fun y n => by
  show (theta' t / D.rho t (y + Lattice.toEuc n)) • D.gradU (y + Lattice.toEuc n) =
    (theta' t / D.rho t y) • D.gradU y
  rw [D.rho_per t y n, D.per_gradU y n]

end PeyreData

end HRS.Uniform.Q12
