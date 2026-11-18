import HRS.Uniform.Q54cAux25

/-!
# Q54c, part 26: Lipschitz fields of the path data, and `PathData.Spec`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

namespace PdeSetup

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

include h

theorem Data.lip_y_one {t t' : ℝ} (ht : t ∈ Set.Icc 0 P.T) (htt : t' ≤ t) (ht' : 0 ≤ t')
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t') :
    ‖(P.pd D μ).y t φ σ - (P.pd D μ).y t' φ σ‖ ≤
      P.kb1 * (t - t') * sobolevNorm ((P.n : ℝ) + 4) φ := by
  have ht'T : t' ∈ Set.Icc 0 P.T := ⟨ht', htt.trans ht.2⟩
  have hτ : t - σ ∈ Set.Icc 0 t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hτ' : t' - σ ∈ Set.Icc 0 t' := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hle : (P.n : ℝ) ≤ P.lev := by have := lev_ge_n2 (P := P); linarith
  have a1 := h.flow_adm0 ht hφ hτ hle
  have a2 := h.flow_adm0 ht'T hφ hτ' hle
  have e : (P.pd D μ).y t φ σ - (P.pd D μ).y t' φ σ =
      (Sv (P.n : ℝ) (P.flow D μ t φ (t - σ) - P.flow D μ t' φ (t' - σ))).2 := by
    rw [Sv_sub a1 a2]; rfl
  rw [e]
  refine (norm_snd_Sv_le (a1.sub a2)).trans ?_
  have hl := h.lip_flow ht htt ht' hφ hσ (j := P.n) (hn1 (P := P)) (by omega)
  have h3 := sobolevNorm_mono_idx hφ (a := (P.n : ℝ) + 2) (b := (P.n : ℝ) + 4) (by linarith)
  have hS := sobolevNorm_nonneg' ((P.n : ℝ) + 4) φ
  have htt0 : 0 ≤ t - t' := by linarith
  refine hl.trans ?_
  unfold kb1
  have g0 := P.c.Cg_nonneg P.n
  have c1 := P.c.Cop_nonneg P.n
  have c2 := P.c.Cop_nonneg (P.n + 2)
  have := mul_le_mul_of_nonneg_left h3 (mul_nonneg g0 c2)
  have hh : 0 ≤ 2 * (P.c.Cop P.n + 1) * (t - t') := by positivity
  calc _ = (2 * (P.c.Cop P.n + 1) * (t - t')) *
        (P.c.Cg P.n * (P.c.Cop (P.n + 2) * sobolevNorm ((P.n : ℝ) + 2) φ)) := by ring
    _ ≤ (2 * (P.c.Cop P.n + 1) * (t - t')) *
        (P.c.Cg P.n * (P.c.Cop (P.n + 2) * sobolevNorm ((P.n : ℝ) + 4) φ)) := by
        apply mul_le_mul_of_nonneg_left _ hh
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 c2) g0
    _ = _ := by ring

theorem Data.lip_w_one {t t' : ℝ} (ht : t ∈ Set.Icc 0 P.T) (htt : t' ≤ t) (ht' : 0 ≤ t')
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ‖(P.pd D μ).w t φ - (P.pd D μ).w t' φ‖ ≤ P.kb3 * (t - t') * sobolevNorm ((P.n : ℝ) + 4) φ := by
  have ht'T : t' ∈ Set.Icc 0 P.T := ⟨ht', htt.trans ht.2⟩
  have hσ : (0 : ℝ) ∈ Set.Icc 0 t' := ⟨le_rfl, ht'⟩
  have hτ : t - 0 ∈ Set.Icc 0 t := ⟨by linarith [ht.1], by linarith [ht.1]⟩
  have hτ' : t' - 0 ∈ Set.Icc 0 t' := ⟨by linarith, by linarith⟩
  have a1 := h.flow_adm0 ht hφ hτ (j := (P.n : ℝ) + 2) lev_ge_n2
  have a2 := h.flow_adm0 ht'T hφ hτ' (j := (P.n : ℝ) + 2) lev_ge_n2
  have e : (P.pd D μ).w t φ - (P.pd D μ).w t' φ =
      (Sv ((P.n : ℝ) + 2) (P.flow D μ t φ (t - 0) - P.flow D μ t' φ (t' - 0))).2 := by
    rw [Sv_sub a1 a2, sub_zero, sub_zero]; rfl
  rw [e]
  refine (norm_snd_Sv_le (a1.sub a2)).trans ?_
  have hl := h.lip_flow ht htt ht' hφ hσ (j := P.n + 2) (by omega) (by omega)
  have hcast : ((P.n + 2 : ℕ) : ℝ) = (P.n : ℝ) + 2 := by push_cast; ring
  have hcast2 : ((P.n : ℝ) + 2) + 2 = (P.n : ℝ) + 4 := by ring
  have hn4 : P.n + 2 + 2 = P.n + 4 := rfl
  rw [hcast, hcast2, hn4] at hl
  refine hl.trans (le_of_eq ?_)
  unfold kb3
  ring

theorem Data.lip_y'_one {t t' : ℝ} (ht : t ∈ Set.Icc 0 P.T) (htt : t' ≤ t) (ht' : 0 ≤ t')
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t') :
    ‖(P.pd D μ).y' t φ σ - (P.pd D μ).y' t' φ σ‖ ≤
      P.kb2 * (t - t') * sobolevNorm ((P.n : ℝ) + 4) φ := by
  have ht'T : t' ∈ Set.Icc 0 P.T := ⟨ht', htt.trans ht.2⟩
  have hσT : σ ∈ Set.Icc 0 P.T := ⟨hσ.1, hσ.2.trans ht'T.2⟩
  have hτ : t - σ ∈ Set.Icc 0 t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hτ' : t' - σ ∈ Set.Icc 0 t' := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have g1 := h.gen_adm0 ht hφ hτ (j := P.n) (by omega) P.hnd
  have g2 := h.gen_adm0 ht'T hφ hτ' (j := P.n) (by omega) P.hnd
  have hle : (P.n : ℝ) + 2 ≤ P.lev := lev_ge_n2
  have f1 := h.flow_adm0 ht hφ hτ hle
  have f2 := h.flow_adm0 ht'T hφ hτ' hle
  have e : (P.pd D μ).y' t φ σ - (P.pd D μ).y' t' φ σ =
      -(Sv (P.n : ℝ) (P.gen D μ t φ (t - σ) - P.gen D μ t' φ (t' - σ))).2 := by
    rw [Sv_sub g1 g2]; show -(_) - -(_) = _; simp; abel
  rw [e, norm_neg]
  refine (norm_snd_Sv_le (g1.sub g2)).trans ?_
  -- the difference of generator paths
  obtain ⟨h0, hb⟩ := h.mem0 hσT
  have f1' := h.flow_adm0 ht hφ hτ (j := 1) (by have := P.hJ1; exact_mod_cast this)
  have f2' := h.flow_adm0 ht'T hφ hτ' (j := 1) (by have := P.hJ1; exact_mod_cast this)
  have eg : P.gen D μ t φ (t - σ) - P.gen D μ t' φ (t' - σ) =
      forwardGen D (μ σ) (P.flow D μ t φ (t - σ) - P.flow D μ t' φ (t' - σ)) := by
    unfold PdeSetup.gen
    rw [sub_sub_cancel, sub_sub_cancel, forwardGen_sub_H1 D (μ σ) h0 hb f1'.2.2 f2'.2.2]
  rw [eg]
  have hs : MemHs ((P.n : ℝ) + 2) (P.flow D μ t φ (t - σ) - P.flow D μ t' φ (t' - σ)) :=
    (f1.sub f2).2.2
  have hn2 : P.n + 2 ≤ P.n + 4 := by omega
  have hgb := (P.c.gen D ν₀ μ h.hA h.hν σ hσT P.n (by omega) _ hs).2
  refine hgb.trans ?_
  have hl := h.lip_flow ht htt ht' hφ hσ (j := P.n + 2) (by omega) (by omega)
  have hcast : ((P.n + 2 : ℕ) : ℝ) = (P.n : ℝ) + 2 := by push_cast; ring
  have hcast2 : ((P.n : ℝ) + 2) + 2 = (P.n : ℝ) + 4 := by ring
  have hn4 : P.n + 2 + 2 = P.n + 4 := rfl
  rw [hcast, hcast2, hn4] at hl
  refine (mul_le_mul_of_nonneg_left hl (P.c.Cg_nonneg P.n)).trans (le_of_eq ?_)
  unfold kb2
  ring

end PdeSetup

end HRS.Uniform.Q54c
