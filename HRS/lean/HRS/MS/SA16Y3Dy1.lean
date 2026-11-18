import HRS.MS.SA16Y3Iw2
import HRS.MS.SA16SNl3
import HRS.MS.SA16RDuh2
import HRS.MS.SA16RExt3

/-!
# S.A.16 (SA16Y3) Dy1: duality of the iso operator on `WmpSpace` (packet P8, iso case, step b1)

`sa16y3_conj_bridge`: `X = ENNReal.conjExponent (ENNReal.ofReal p)` is finite, `> 1` and `ofReal X.toReal = X` (`2 ≤ p`).
`sa16y3_dual_memLp`: the iso dual `sa16y3_dualIW s μ ψ` lies in `L^X` (from `sa16y3_dual_Lp`).
`sa16y3_iso_duality`: for `T : W^{m+2,p} →L W^{m,p}` with the En1 property on `Jcc`,
  `sa16r_ell d m p hψ (T G) = sa16so_ellN d (m+2) p hN G = ∫ wrep G · sa16y3_dualIW s μ ψ`.
Proof: density of `Jcc` (`sa16r_Jcc_dense`), then `sa16y3_iso_dual` (Iw1).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Dy1
variable {d : ℕ} {s : ℝ}

lemma sa16y3_conj_bridge {p : ℝ} (hp : 2 ≤ p) :
    ENNReal.conjExponent (ENNReal.ofReal p) ≠ ⊤ ∧ 1 < (ENNReal.conjExponent (ENNReal.ofReal p)).toReal ∧
      ENNReal.ofReal (ENNReal.conjExponent (ENNReal.ofReal p)).toReal = ENNReal.conjExponent (ENNReal.ofReal p) := by
  have h2 : (1 : ℝ≥0∞) + 1 ≤ ENNReal.ofReal p := by
    rw [one_add_one_eq_two, ← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal hp
  have hA : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p - 1 :=
    (ENNReal.add_sub_cancel_right ENNReal.one_ne_top).symm.le.trans (tsub_le_tsub_right h2 1)
  have hinv : (ENNReal.ofReal p - 1)⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hA
  have hne : ENNReal.ofReal p - 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top tsub_le_self
  have hpos : (ENNReal.ofReal p - 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hne
  have hXle : ENNReal.conjExponent (ENNReal.ofReal p) ≤ 2 := by
    unfold ENNReal.conjExponent
    calc 1 + (ENNReal.ofReal p - 1)⁻¹ ≤ 1 + 1 := add_le_add le_rfl hinv
      _ = 2 := one_add_one_eq_two
  have hXtop : ENNReal.conjExponent (ENNReal.ofReal p) ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num) hXle
  have hX1 : 1 < ENNReal.conjExponent (ENNReal.ofReal p) := by
    unfold ENNReal.conjExponent
    exact ENNReal.lt_add_right ENNReal.one_ne_top hpos
  refine ⟨hXtop, ?_, ENNReal.ofReal_toReal hXtop⟩
  have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hXtop).2 hX1
  simpa using this

lemma sa16y3_partial_wZero {m : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (κ : Fin ((wZero d m).1 : ℕ) → Fin d) :
    partialDeriv κ f = f := by
  funext x
  unfold partialDeriv
  exact iteratedFDeriv_zero_apply _

lemma sa16y3_S_lt_top_any {q : ℝ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (N : ℕ) :
    sa16z_S q ψ N < ⊤ := by
  unfold sa16z_S sa16z_JJ
  exact ENNReal.sum_lt_top.2 fun k _ =>
    ((sa16sz_vn_cont ψ hψ.1 k).memLp_of_hasCompactSupport (sa16sz_vn_cs hψ k)).eLpNorm_lt_top

lemma sa16y3_dual_memLp {p : ℝ} [Fact (2 ≤ p)] (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (hθ1 : 1 < s + 2 - d) {μ ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hμ : ContDiff ℝ ∞ μ) (hψ : IsCcInfty ψ)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hCb : sa16z_Cb 1 Λ μ) :
    MemLp (sa16y3_dualIW s μ ψ) (ENNReal.conjExponent (ENNReal.ofReal p)) volume := by
  obtain ⟨_, hX1, hXe⟩ := sa16y3_conj_bridge (p := p) (Fact.out : 2 ≤ p)
  obtain ⟨C, _, hC⟩ := sa16y3_dual_Lp (s := s) hd hs0 hsd hθ1 hX1
  have h := hC hμ hψ hΛ hCb
  rw [hXe] at h
  exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (sa16y3_S_lt_top_any hψ 2))

theorem sa16y3_iso_duality {p : ℝ} [Fact (2 ≤ p)] (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {m : ℕ} {μ ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hμ : ContDiff ℝ ∞ μ) (hψ : IsCcInfty ψ)
    (hN : MemLp (sa16y3_dualIW s μ ψ) (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (T : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hTJ : ∀ φ : ccSub d, (((T (sa16r_Jcc d (m + 1 + 1) p φ) : WmpSpace d m p) : WLp d m p) :
      EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) =ᵐ[volume] wJet m (sa16z_P s μ φ.1))
    (G : WmpSpace d (m + 1 + 1) p) :
    sa16r_ell d m p hψ (T G) = sa16so_ellN d (m + 1 + 1) p hN G := by
  refine (sa16r_Jcc_dense d (m + 1 + 1) p).induction_on G (isClosed_eq ?_ ?_) (fun φ => ?_)
  · exact (sa16r_ell d m p hψ).continuous.comp T.continuous
  · exact (sa16so_ellN d (m + 1 + 1) p hN).continuous
  · rw [sa16r_ell_apply, sa16so_ellN_apply]
    have e1 : ∫ x, wrep d m p (T (sa16r_Jcc d (m + 1 + 1) p φ)) x * ψ x =
        ∫ x, sa16z_P s μ φ.1 x * ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [hTJ φ] with x hx
      unfold wrep
      rw [hx]
      show partialDeriv (wZero d m).2 (sa16z_P s μ φ.1) x * ψ x = _
      rw [sa16y3_partial_wZero]
    have e2 : ∫ x, wrep d (m + 1 + 1) p (sa16r_Jcc d (m + 1 + 1) p φ) x *
        sa16y3_dualIW s μ ψ x = ∫ x, φ.1 x * sa16y3_dualIW s μ ψ x := by
      rw [sa16r_Jcc_eq]
      refine integral_congr_ae ?_
      filter_upwards [sa16r_cc_elt_wrep (p := p) φ.2 (m + 1 + 1)] with x hx
      rw [hx]
    rw [e1, e2]
    exact sa16y3_iso_dual hd hs0 hsd hμ φ.2 hψ

end Dy1

end HRS.Whole.AppendixA.Phase2SA16R
