import HRS.MC.L2C3Aux4
import HRS.MC.L2C0

/-!
# Packet L2C-3, helper 5: the classical solution and the Lyapunov path

* `l2c3_classical`: for `t > 0` and smooth `φ` the adjoint propagator along `ρ^s` on `[0,t]` is a classical adjoint
  solution `F` (Proposition 3.9), `F r = U^{r,t} φ`.
* `l2c3_y`, `l2c3_y'`: the path `y(τ) = P_β [F(t-τ)] - [S(τ)] ∈ L²(μ_β)` (`P_β` centering, `S` a path of the frozen
  type) and its derivative; `l2c3_path_deriv` shows that `y` is continuous on `[0,t]` and differentiable on `(0,t)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

namespace HRS.MC.L2C3

variable {d : ℕ}

theorem l2c3_classical (R : Regime d) {t : ℝ} (ht : 0 < t) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ F : ℝ → Torus d → ℝ, IsClassicalAdjointSolution R.D R.ρ t φ F ∧
      ∀ r ∈ Set.Icc 0 t, propagator R.D R.ρ r t φ = F r := by
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hν : 0 < R.D.invβ := by rw [R.hDβ]; exact inv_pos.2 R.hβ
  obtain ⟨hprob, hcont⟩ := HRS.MC.L2C0.l2c0_rho_prob_cont R
  have hA := HRS.MC.L2C0.l2c0_adjointData_generic R.D R.hM R.hV hν R.ρ hprob
    (fun j => HRS.MC.RegSet.reg_proof R j) hcont
  have hm1 : 1 ≤ mStar d := by have := ClassicalPart.three_le_mStar d; omega
  obtain ⟨Rg, MB, Λ, VB, ν₀, hAD⟩ := hA (mStar d) hm1 t ht
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd1 R.D.s R.D.hs0 R.D.hsd (mStar d) le_rfl
    Rg MB Λ VB
  have hφc : Continuous φ := continuous_of_isSmooth hφ
  obtain ⟨h1, h2, -⟩ := hmain R.D ν₀ t R.ρ hAD t ⟨ht, le_rfl⟩ φ hφc
    (MFSemigroup.memSobolev_of_isSmooth hφ _)
  exact ⟨_, h1, h2⟩

theorem l2c3_cont_F {D : DynData d} {μ : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    {F : ℝ → Torus d → ℝ} (hF : IsClassicalAdjointSolution D μ t φ F) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => F p.1 p.2 := by
  refine ClassicalAux.continuous_prod_of_lift (X := Set.Icc (0 : ℝ) t) (fun r x => F r x) ?_
  have h0 := ClassicalAux.continuous_iteratedFDeriv_eval
    (G := fun r : Set.Icc (0 : ℝ) t => Torus.lift (F r)) 0 (hF.cont_c2 0 (by norm_num)) ![]
  simp only [iteratedFDeriv_zero_apply] at h0
  exact h0

/-- The reversed-time map `[0,t] → [0,t]`, `τ ↦ t - τ`. -/
def l2c3_rev (t : ℝ) (τ : Set.Icc (0 : ℝ) t) : Set.Icc (0 : ℝ) t :=
  ⟨t - τ.1, by linarith [τ.2.2], by linarith [τ.2.1]⟩

theorem l2c3_rev_cont (t : ℝ) : Continuous (l2c3_rev t) :=
  Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _

/-- The path `y(τ) = P_β [F(t-τ)] - [S(τ)]`. -/
def l2c3_y (R : Regime d) (t : ℝ) (F S : ℝ → Torus d → ℝ) : ℝ → Lp ℝ 2 (withDensityReal R.ρβ) :=
  fun τ => l2c3_P (withDensityReal R.ρβ) (pL (withDensityReal R.ρβ) (fun τ' => F (t - τ')) τ) -
    pL (withDensityReal R.ρβ) S τ

/-- The derivative of `l2c3_y`. -/
def l2c3_y' (R : Regime d) (t : ℝ) (F S : ℝ → Torus d → ℝ) : ℝ → Lp ℝ 2 (withDensityReal R.ρβ) :=
  fun τ => l2c3_P (withDensityReal R.ρβ)
      (pL (withDensityReal R.ρβ) (fun τ' x => backwardGenerator R.D (R.ρ (t - τ')) (F (t - τ')) x) τ) -
    pL (withDensityReal R.ρβ) (fun τ' => equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S τ')) τ

theorem l2c3_path_generic (μ : Measure (Torus d)) [IsFiniteMeasure μ] {t : ℝ}
    {G G' S S' : ℝ → Torus d → ℝ}
    (hcG : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (G τ))
    (hcG' : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (G' τ))
    (hGj : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => G p.1 p.2)
    (hGj' : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => G' p.1 p.2)
    (hdG : ∀ x : Torus d, ∀ v ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (fun v => G v x) (G' v x) v)
    (hcS : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (S τ))
    (hcS' : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (S' τ))
    (hSj : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => S p.1 p.2)
    (hSj' : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => S' p.1 p.2)
    (hdS : ∀ x : Torus d, ∀ v ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (fun v => S v x) (S' v x) v) :
    ContinuousOn (fun τ => l2c3_P μ (pL μ G τ) - pL μ S τ) (Set.Icc 0 t) ∧
      ∀ τ ∈ Set.Ioo (0 : ℝ) t,
        HasDerivAt (fun τ => l2c3_P μ (pL μ G τ) - pL μ S τ) (l2c3_P μ (pL μ G' τ) - pL μ S' τ) τ := by
  refine ⟨?_, fun τ hτ => ?_⟩
  · have h1 := continuousOn_pL μ hcG hGj
    have h2 := continuousOn_pL μ hcS hSj
    exact ((l2c3_P μ).continuous.comp_continuousOn h1).sub h2
  · have h1 := hasDerivAt_pL μ hcG hcG' hGj' hdG hτ
    have h2 := hasDerivAt_pL μ hcS hcS' hSj' hdS hτ
    have h3 := (l2c3_P μ).hasFDerivAt.comp_hasDerivAt τ h1
    exact h3.sub h2

theorem l2c3_path_deriv (R : Regime d) {t : ℝ} {φ : Torus d → ℝ} {F : ℝ → Torus d → ℝ}
    (hF : IsClassicalAdjointSolution R.D R.ρ t φ F) {S : ℝ → Torus d → ℝ}
    (hS2 : ∀ τ ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 2 (S τ))
    (hSc : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => S p.1 p.2)
    (hSg : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d =>
      equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S p.1) p.2)
    (hSd : ∀ x : Torus d, ∀ τ ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt (fun τ' => S τ' x) (equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S τ) x) τ) :
    ContinuousOn (l2c3_y R t F S) (Set.Icc 0 t) ∧
      ∀ τ ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (l2c3_y R t F S) (l2c3_y' R t F S τ) τ := by
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) t, t - τ ∈ Set.Icc (0 : ℝ) t := fun τ hτ =>
    ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hrev : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => (l2c3_rev t p.1, p.2) :=
    ((l2c3_rev_cont t).comp continuous_fst).prodMk continuous_snd
  have hGj : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => F (t - p.1) p.2 :=
    (l2c3_cont_F hF).comp hrev
  have hGj' : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d =>
      backwardGenerator R.D (R.ρ (t - p.1)) (F (t - p.1)) p.2 :=
    (hF.cont_time_deriv.comp hrev).congr fun p => rfl
  have hdG : ∀ x : Torus d, ∀ v ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (fun v => F (t - v) x)
      (backwardGenerator R.D (R.ρ (t - v)) (F (t - v)) x) v := by
    intro x v hv
    have h := hF.time_deriv x (t - v) ⟨by linarith [hv.2], by linarith [hv.1]⟩
    exact (h.comp v ((hasDerivAt_id v).const_sub t)).congr_deriv (by simp)
  have hcS : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (S τ) := fun τ hτ =>
    MFAux.continuous_of_isCk ((hS2 τ hτ).of_le (by norm_num))
  have hcS' : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S τ)) :=
    fun τ hτ => l2c3_eqGen_cont R (hS2 τ hτ)
  have hcG : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (F (t - τ)) := fun τ hτ =>
    ClassicalAux.continuous_f_apply hF (hmem τ hτ)
  have hcG' : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      Continuous (backwardGenerator R.D (R.ρ (t - τ)) (F (t - τ))) := fun τ hτ =>
    ClassicalAux.continuous_bg_apply hF (hmem τ hτ)
  exact l2c3_path_generic (withDensityReal R.ρβ) (t := t) (G := fun τ' => F (t - τ'))
    (G' := fun τ' x => backwardGenerator R.D (R.ρ (t - τ')) (F (t - τ')) x)
    (S := S) (S' := fun τ' => equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S τ'))
    hcG hcG' hGj hGj' hdG hcS hcS' hSc hSg hSd

end HRS.MC.L2C3
