import HRS.Uniform.Q54cAux24

/-!
# Q54c, part 25: bounds and Lipschitz estimates of the path data
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

theorem norm_snd_Sv_le {j : ℝ} {F : Coeff d} (hF : Adm j F) : ‖(Sv j F).2‖ ≤ HRS.PDE.hsNorm j F :=
  (norm_snd_le _).trans hF.norm_Sv_le

namespace PdeSetup

variable (P : PdeSetup d)

def ka1 : ℝ := P.c.Cop P.n + 1
def ka2 : ℝ := P.c.Cg P.n * (P.c.Cop (P.n + 2) + 1)
def ka3 : ℝ := P.c.Cop (P.n + 2) + 1
def kb1 : ℝ := 2 * (P.c.Cop P.n + 1) * (P.c.Cg P.n * P.c.Cop (P.n + 2))
def kb2 : ℝ := P.c.Cg P.n * (2 * (P.c.Cop (P.n + 2) + 1) * (P.c.Cg (P.n + 2) * P.c.Cop (P.n + 4)))
def kb3 : ℝ := 2 * (P.c.Cop (P.n + 2) + 1) * (P.c.Cg (P.n + 2) * P.c.Cop (P.n + 4))

/-- the uniform constant of the path data -/
def Kc : ℝ := P.ka1 + P.ka2 + P.ka3 + P.kb1 + P.kb2 + P.kb3

theorem k_nonneg : 0 ≤ P.ka1 ∧ 0 ≤ P.ka2 ∧ 0 ≤ P.ka3 ∧ 0 ≤ P.kb1 ∧ 0 ≤ P.kb2 ∧ 0 ≤ P.kb3 := by
  have h1 := P.c.Cop_nonneg P.n
  have h2 := P.c.Cop_nonneg (P.n + 2)
  have h3 := P.c.Cop_nonneg (P.n + 4)
  have g1 := P.c.Cg_nonneg P.n
  have g2 := P.c.Cg_nonneg (P.n + 2)
  unfold ka1 ka2 ka3 kb1 kb2 kb3
  refine ⟨by positivity, by positivity, by positivity, by positivity, by positivity, by positivity⟩

theorem ka1_le : P.ka1 ≤ P.Kc := by
  obtain ⟨-, a2, a3, b1, b2, b3⟩ := P.k_nonneg; unfold Kc; linarith
theorem ka2_le : P.ka2 ≤ P.Kc := by
  obtain ⟨a1, -, a3, b1, b2, b3⟩ := P.k_nonneg; unfold Kc; linarith
theorem ka3_le : P.ka3 ≤ P.Kc := by
  obtain ⟨a1, a2, -, b1, b2, b3⟩ := P.k_nonneg; unfold Kc; linarith
theorem kb1_le : P.kb1 ≤ P.Kc := by
  obtain ⟨a1, a2, a3, -, b2, b3⟩ := P.k_nonneg; unfold Kc; linarith
theorem kb2_le : P.kb2 ≤ P.Kc := by
  obtain ⟨a1, a2, a3, b1, -, b3⟩ := P.k_nonneg; unfold Kc; linarith
theorem kb3_le : P.kb3 ≤ P.Kc := by
  obtain ⟨a1, a2, a3, b1, b2, -⟩ := P.k_nonneg; unfold Kc; linarith
theorem Kc_nonneg : 0 ≤ P.Kc := by
  obtain ⟨a1, a2, a3, b1, b2, b3⟩ := P.k_nonneg; unfold Kc; linarith

variable {P} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

include h

theorem Data.bd_y {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    ‖(P.pd D μ).y t φ σ‖ ≤ P.Kc * sobolevNorm ((P.n : ℝ) + 4) φ := by
  have hτ : t - σ ∈ Set.Icc 0 t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hA := h.flow_adm0 ht hφ hτ (j := (P.n : ℝ)) (by have := lev_ge_n2 (P := P); linarith)
  have h1 := norm_snd_Sv_le hA
  have h2 := h.flow_hsNorm0 ht hφ hτ (j := P.n) (hn1 (P := P)) (by omega)
  have h3 := sobolevNorm_mono_idx hφ (a := (P.n : ℝ)) (b := (P.n : ℝ) + 4) (by linarith)
  have hS := sobolevNorm_nonneg' ((P.n : ℝ) + 4) φ
  have hk := P.ka1_le
  have hk0 := P.k_nonneg.1
  show ‖(Sv (P.n : ℝ) (P.flow D μ t φ (t - σ))).2‖ ≤ _
  calc _ ≤ _ := h1.trans h2
    _ ≤ P.ka1 * sobolevNorm ((P.n : ℝ) + 4) φ := by
        unfold ka1
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hk hS

theorem Data.bd_y' {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    ‖(P.pd D μ).y' t φ σ‖ ≤ P.Kc * sobolevNorm ((P.n : ℝ) + 4) φ := by
  have hτ : t - σ ∈ Set.Icc 0 t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hA := h.gen_adm0 ht hφ hτ (j := P.n) (by omega) P.hnd
  have h1 := norm_snd_Sv_le hA
  have h2 := h.gen_bd0 ht hφ hτ (j := P.n) (by omega)
  have h3 := sobolevNorm_mono_idx hφ (a := (P.n : ℝ) + 2) (b := (P.n : ℝ) + 4) (by linarith)
  have hS := sobolevNorm_nonneg' ((P.n : ℝ) + 4) φ
  have hk := P.ka2_le
  have hk0 := P.k_nonneg.2.1
  have g0 := P.c.Cg_nonneg P.n
  have c0 := P.c.Cop_nonneg (P.n + 2)
  show ‖-(Sv (P.n : ℝ) (P.gen D μ t φ (t - σ))).2‖ ≤ _
  rw [norm_neg]
  calc _ ≤ _ := h1.trans h2
    _ ≤ P.ka2 * sobolevNorm ((P.n : ℝ) + 4) φ := by
        unfold ka2
        have := mul_le_mul_of_nonneg_left h3 (show 0 ≤ P.c.Cop (P.n + 2) + 1 by positivity)
        nlinarith [mul_le_mul_of_nonneg_left this g0]
    _ ≤ _ := mul_le_mul_of_nonneg_right hk hS

theorem Data.bd_w {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ‖(P.pd D μ).w t φ‖ ≤ P.Kc * sobolevNorm ((P.n : ℝ) + 4) φ := by
  have hτ : t ∈ Set.Icc 0 t := ⟨ht.1, le_rfl⟩
  have hA := h.flow_adm0 ht hφ hτ (j := (P.n : ℝ) + 2) lev_ge_n2
  have h1 := norm_snd_Sv_le hA
  have h2 := h.flow_hsNorm0 ht hφ hτ (j := P.n + 2) (by omega) (by omega)
  have hcast : ((P.n + 2 : ℕ) : ℝ) = (P.n : ℝ) + 2 := by push_cast; ring
  rw [hcast] at h2
  have h3 := sobolevNorm_mono_idx hφ (a := (P.n : ℝ) + 2) (b := (P.n : ℝ) + 4) (by linarith)
  have hS := sobolevNorm_nonneg' ((P.n : ℝ) + 4) φ
  have hk := P.ka3_le
  have hk0 := P.k_nonneg.2.2.1
  show ‖(Sv ((P.n : ℝ) + 2) (P.flow D μ t φ t)).2‖ ≤ _
  calc _ ≤ _ := h1.trans h2
    _ ≤ P.ka3 * sobolevNorm ((P.n : ℝ) + 4) φ := by
        unfold ka3
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hk hS

end PdeSetup

end HRS.Uniform.Q54c
