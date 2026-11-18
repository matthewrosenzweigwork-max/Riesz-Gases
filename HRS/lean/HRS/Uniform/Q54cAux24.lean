import HRS.Uniform.Q54cAux23

/-!
# Q54c, part 24: derivative, continuity and norm bounds of the path data
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

theorem Adm.sub {j : ℝ} {a b : Coeff d} (ha : Adm j a) (hb : Adm j b) : Adm j (a - b) := by
  have := ha.comb hb 1 (-1)
  convert this using 1
  funext k; simp [sub_eq_add_neg]

theorem Sv_sub {j : ℝ} {a b : Coeff d} (ha : Adm j a) (hb : Adm j b) :
    Sv j (a - b) = Sv j a - Sv j b := by
  have := Sv_comb ha hb 1 (-1)
  have e : (fun k => ((1 : ℝ) : ℂ) * a k + ((-1 : ℝ) : ℂ) * b k) = a - b := by
    funext k; simp [sub_eq_add_neg]
  rw [e] at this
  rw [this]; simp [sub_eq_add_neg]

namespace PdeSetup

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

theorem lev_sub2 : P.lev - 2 = (P.n : ℝ) + 2 := by
  unfold PdeSetup.lev; push_cast; ring

include h

theorem Data.deriv_y {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    HasDerivWithinAt (fun s => (P.pd D μ).y t φ s) ((P.pd D μ).y' t φ σ) (Set.Icc 0 t) σ := by
  by_cases h0 : t = 0
  · subst h0
    have : σ = 0 := le_antisymm hσ.2 hσ.1
    subst this
    exact hasDerivWithinAt_Icc_zero _ _
  · have ht' : t ∈ Set.Ioc 0 P.T := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
    have hD := HRS.Uniform.Q54.dom_smooth (J := P.n + 4) hφ
    have hτ : t - σ ∈ Set.Icc 0 t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hd := h.hasDeriv ht' hD hτ (j := P.n) (by omega)
    have hd2 : HasDerivWithinAt (fun τ' => (Sv (P.n : ℝ) (P.flow D μ t φ τ')).2)
        (Sv (P.n : ℝ) (P.gen D μ t φ (t - σ))).2 (Set.Icc 0 t) (t - σ) :=
      (ContinuousLinearMap.snd ℝ ℝ (NegSobolev d (P.n : ℝ))).hasFDerivAt.comp_hasDerivWithinAt _ hd
    have hh : HasDerivWithinAt (fun s : ℝ => t - s) (-1) (Set.Icc 0 t) σ := by
      simpa using (hasDerivWithinAt_id σ (Set.Icc 0 t)).const_sub t
    have hmap : Set.MapsTo (fun s : ℝ => t - s) (Set.Icc 0 t) (Set.Icc 0 t) := fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have := hd2.scomp σ hh hmap
    have e : (P.pd D μ).y' t φ σ = (-1 : ℝ) • (Sv (P.n : ℝ) (P.gen D μ t φ (t - σ))).2 := by
      show -(Sv (P.n : ℝ) (P.gen D μ t φ (t - σ))).2 = (-1 : ℝ) • (Sv (P.n : ℝ) (P.gen D μ t φ (t - σ))).2
      simp
    rw [e]
    exact this

theorem Data.gen_contSv {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ContinuousOn (fun τ => Sv (P.n : ℝ) (P.gen D μ t φ τ)) (Set.Icc 0 t) := by
  have hD := HRS.Uniform.Q54.dom_smooth (J := P.n + 4) hφ
  have ht0 : t ∈ Set.Icc 0 P.T := ⟨ht.1.le, ht.2⟩
  intro τ₀ hτ₀
  have hc := (h.gen_cont ht hD).2 τ₀ hτ₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hc
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have a1 := h.gen_adm0 ht0 hφ hτ (j := P.n + 2) (by omega) (by
    have := P.hnd; push_cast; linarith)
  have a2 := h.gen_adm0 ht0 hφ hτ₀ (j := P.n + 2) (by omega) (by
    have := P.hnd; push_cast; linarith)
  have hcast : ((P.n + 2 : ℕ) : ℝ) = (P.n : ℝ) + 2 := by push_cast; ring
  rw [hcast] at a1 a2
  have b1 := h.gen_adm0 ht0 hφ hτ (j := P.n) (by omega) P.hnd
  have b2 := h.gen_adm0 ht0 hφ hτ₀ (j := P.n) (by omega) P.hnd
  rw [← Sv_sub b1 b2]
  refine b1.sub b2 |>.norm_Sv_le.trans ?_
  rw [lev_sub2 (P := P)]
  exact hsNorm_mono_q (by linarith) (a1.sub a2).2.2

theorem Data.cont_y' {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ContinuousOn ((P.pd D μ).y' t φ) (Set.Icc 0 t) := by
  by_cases h0 : t = 0
  · subst h0
    rw [Set.Icc_self]
    exact continuousOn_singleton _ _
  · have ht' : t ∈ Set.Ioc 0 P.T := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
    have hc := h.gen_contSv ht' hφ
    have hmap : Set.MapsTo (fun s : ℝ => t - s) (Set.Icc 0 t) (Set.Icc 0 t) := fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h2 : ContinuousOn (fun s : ℝ => (Sv (P.n : ℝ) (P.gen D μ t φ (t - s))).2) (Set.Icc 0 t) :=
      (continuous_snd.comp_continuousOn hc).comp (continuous_const.sub continuous_id).continuousOn hmap
    exact h2.neg

end PdeSetup

end HRS.Uniform.Q54c
