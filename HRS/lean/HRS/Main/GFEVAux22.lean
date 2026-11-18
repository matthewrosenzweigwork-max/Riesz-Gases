import HRS.Main.GFEVAux21

/-!
# Packet GFEVG, part 22: `GFProj`, the tail estimate for the Galerkin projections
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem gfevP_mem (γ : ℕ) (S : Finset (NonzeroLattice d)) (x : NegSobolev d (γ : ℝ)) :
    (gfevP S (show L2 d from x) : NegSobolev d (γ : ℝ)) ∈ gfevD d γ := by
  classical
  set Px : NegSobolev d (γ : ℝ) := (gfevP S (show L2 d from x) : NegSobolev d (γ : ℝ)) with hPx
  refine ⟨q48bFin ((γ : ℝ) - 4) S (fun k => NegSobolev.fourierCoeff Px k), ?_⟩
  show NegSobolev.embed (γ : ℝ) _ = _
  refine gfev_ext_fc fun k => ?_
  rw [gfev_fourierCoeff_embed (gfev_le4 γ), q48bFin_fourierCoeff]
  by_cases hk : k ∈ S
  · rw [if_pos hk]
  · rw [if_neg hk]
    have : NegSobolev.coord Px k = 0 := by
      show (gfevP S (show L2 d from x)) k = 0
      rw [gfevP_coord, if_neg hk]
    unfold NegSobolev.fourierCoeff
    rw [this]; simp

theorem GFEV_proj (d γ : ℕ) : GFProj (gfevD d γ) (fun n => (gfevP (gfevSn d n) : NegSobolev d (γ : ℝ) →L[ℝ] NegSobolev d (γ : ℝ))) :=
  ⟨fun _ x => gfevP_idem _ x, fun _ x y => gfevP_symm _ x y, fun _ => gfevP_findim _,
    fun _ x => gfevP_mem γ _ x, fun x => gfevP_tendsto x⟩

theorem gfev_jp_ge {n : ℕ} {k : NonzeroLattice d} (hk : ¬ InBox n k.1) : (n : ℝ) + 1 ≤ Lattice.jp k.1 := by
  unfold InBox at hk
  push_neg at hk
  obtain ⟨i, hi⟩ := hk
  have h1 : ((n : ℤ) + 1 : ℤ) ≤ |k.1 i| := by omega
  have h2 : (n : ℝ) + 1 ≤ |((k.1 i : ℤ) : ℝ)| := by
    have : ((n : ℤ) + 1 : ℤ) ≤ |k.1 i| := h1
    exact_mod_cast (by rw [← Int.cast_abs]; exact_mod_cast this : (((n : ℤ) + 1 : ℤ) : ℝ) ≤ |((k.1 i : ℤ) : ℝ)|)
  have h3 : |((k.1 i : ℤ) : ℝ)| ≤ Lattice.enorm k.1 := by
    have := PiLp.norm_apply_le (Lattice.toEuc k.1) i
    simpa [Lattice.toEuc, Lattice.enorm] using this
  unfold Lattice.jp
  have h4 : (Lattice.enorm k.1) ≤ Real.sqrt (1 + 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2) := by
    refine Real.le_sqrt_of_sq_le ?_
    have h5 : (0 : ℝ) ≤ 4 * Real.pi ^ 2 - 1 := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_nonneg h5 (sq_nonneg (Lattice.enorm k.1))]
  linarith

end HRS.GF
