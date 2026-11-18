import HRS.MS.SA16SOp4
import HRS.MS.SA16QFin6

/-!
# S.A.16 (SA16S) Op5: the nonlocal operator `G_μ` on `WmpSpace` (from SA16Q `sub_nonlocal_bound`)

For `0 ≤ s ≤ d-2`, `d < p (s+1)`, `μ` a `(m+3, Λ)`-regular density and `|M_ij| ≤ MB`:
`sa16so_G_exists`: there is `C > 0` (uniform in `M, μ`) and a continuous linear `T : W^{m,p} → W^{m,p}` with `‖T‖ ≤ C`
whose zeroth component on the jet of `φ ∈ C_c^∞` is `eucNonlocal s M μ φ`.  The operator is unique (density).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Op5
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- `φ ∈ C_c^∞` as a Schwartz function -/
def sa16so_schw (φ : ccSub d) : 𝓢(Euc d, ℝ) := φ.2.2.toSchwartzMap φ.2.1

lemma sa16so_schw_coe (φ : ccSub d) : ⇑(sa16so_schw φ) = φ.1 := rfl

lemma sa16so_lift_exists (m : ℕ) {f : Euc d → ℝ} (h : wNormE m p f < ⊤) :
    ∃ G : WmpSpace d m p, wrep d m p G =ᵐ[volume] f := by
  by_contra hne
  refine absurd h (not_lt.2 (le_of_eq ?_))
  refine (eq_top_iff.2 ?_).symm
  unfold wNormE
  refine le_iInf₂ fun G hG => absurd ⟨G, hG⟩ hne

lemma sa16so_wNormE_cc (m : ℕ) (φ : ccSub d) :
    wNormE m p φ.1 = ENNReal.ofReal ‖sa16r_Jcc d m p φ‖ := by
  refine wNormE_eq_lift_norm d m p (sa16r_Jcc d m p φ) φ.1 ?_
  rw [sa16r_Jcc_eq]
  exact sa16r_cc_elt_wrep (p := p) φ.2 m

section Lin
variable (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
include hd hs hs2

lemma sa16so_F_add (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) {B0 B1 : ℝ}
    (hB0 : ∀ x, |a x| ≤ B0) (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1) (u v : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M a ⇑(u + v) x =
      HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x + HRS.MH.AdjointRd.eucNonlocal s M a ⇑v x := by
  rw [sa16q_F_pointwise hd hs hs2 M ha1 hB0 hB1 (u + v) x, sa16q_F_pointwise hd hs hs2 M ha1 hB0 hB1 u x,
    sa16q_F_pointwise hd hs hs2 M ha1 hB0 hB1 v x, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_add, ← integral_add (sa16q_Fint_integrable hd hs hs2 ha1 hB0 hB1 u i j x)
    (sa16q_Fint_integrable hd hs hs2 ha1 hB0 hB1 v i j x)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h1 : fderiv ℝ ⇑(u + v) (x - y) = fderiv ℝ ⇑u (x - y) + fderiv ℝ ⇑v (x - y) := by
    rw [show ⇑(u + v) = ⇑u + ⇑v from funext fun x => rfl, fderiv_add u.differentiableAt v.differentiableAt]
  simp only [h1, ContinuousLinearMap.add_apply]
  ring

lemma sa16so_F_smul (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) {B0 B1 : ℝ}
    (hB0 : ∀ x, |a x| ≤ B0) (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1) (c : ℝ) (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M a ⇑(c • u) x = c * HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x := by
  rw [sa16q_F_pointwise hd hs hs2 M ha1 hB0 hB1 (c • u) x, sa16q_F_pointwise hd hs hs2 M ha1 hB0 hB1 u x,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ y, fderiv ℝ ⇑(c • u) y = c • fderiv ℝ ⇑u y := fun y => by
    rw [show ⇑(c • u) = c • ⇑u from funext fun x => rfl, fderiv_const_smul u.differentiableAt]
  have h2 : ∫ y, sa16q_K1E s 0 i y * (a (x - y) * fderiv ℝ ⇑(c • u) (x - y) (EuclideanSpace.single j (1 : ℝ))) =
      c * ∫ y, sa16q_K1E s 0 i y * (a (x - y) * fderiv ℝ ⇑u (x - y) (EuclideanSpace.single j (1 : ℝ))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [h1, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [h2]
  ring

end Lin

/-- **The nonlocal operator on `W^{m,p}`** (constant uniform in `M`, `μ`) -/
theorem sa16so_G_exists (d m : ℕ) (hd : 1 ≤ d) (s p MB Λ : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs2 : s ≤ (d : ℝ) - 2) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) → ∀ μ : Euc d → ℝ,
      IsRegularDensityW (m + 3) Λ μ →
        ∃ T : WmpSpace d m p →L[ℝ] WmpSpace d m p, ‖T‖ ≤ C ∧ ∀ φ : ccSub d,
          wrep d m p (T (sa16r_Jcc d m p φ)) =ᵐ[volume]
            HRS.MH.AdjointRd.eucNonlocal s M μ φ.1 := by
  obtain ⟨C, hC, hbd⟩ := sub_nonlocal_bound d m hd s p MB Λ hs0 hs2 hfar
  refine ⟨C, hC, fun M hM μ hμ => ?_⟩
  have hd2 : 2 ≤ d := by
    have : (2 : ℝ) ≤ d := by linarith
    exact_mod_cast this
  obtain ⟨hCd, hbdd, -⟩ := sa16q_reg_data hμ
  have hμ1 : ContDiff ℝ 1 μ := hCd.of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
  set B0 := max Λ 0
  have hB0 := sa16q_reg_abs hμ
  have hB1 := sa16q_reg_fderiv hμ
  -- finiteness and bound
  have hfin : ∀ φ : ccSub d, wNormE m p (HRS.MH.AdjointRd.eucNonlocal s M μ φ.1) ≤
      ENNReal.ofReal (C * ‖sa16r_Jcc d m p φ‖) := by
    intro φ
    have h := hbd M hM μ hμ (sa16so_schw φ)
    rw [sa16so_schw_coe, sa16so_wNormE_cc] at h
    rwa [ENNReal.ofReal_mul hC.le]
  have hex : ∀ φ : ccSub d, ∃ G : WmpSpace d m p,
      wrep d m p G =ᵐ[volume] HRS.MH.AdjointRd.eucNonlocal s M μ φ.1 := fun φ =>
    sa16so_lift_exists m (lt_of_le_of_lt (hfin φ) ENNReal.ofReal_lt_top)
  choose A hA using hex
  have hAnorm : ∀ φ : ccSub d, ‖A φ‖ ≤ C * ‖sa16r_Jcc d m p φ‖ := by
    intro φ
    have h1 := wNormE_eq_lift_norm d m p (A φ) (HRS.MH.AdjointRd.eucNonlocal s M μ φ.1) (by
      filter_upwards [hA φ] with x hx
      exact hx)
    have h2 := hfin φ
    rw [h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le (norm_nonneg _))).1 h2
  -- linearity
  have hadd : ∀ φ ψ : ccSub d, A (φ + ψ) = A φ + A ψ := by
    intro φ ψ
    refine sa16r_wrep_inj d m p _ _ ?_
    filter_upwards [hA (φ + ψ), hA φ, hA ψ, sa16r_wrep_add d m p (A φ) (A ψ)] with x h1 h2 h3 h4
    rw [h4, h1, h2, h3]
    have := sa16so_F_add hd2 hs0 hs2 M hμ1 hB0 hB1 (sa16so_schw φ) (sa16so_schw ψ) x
    exact this
  have hsmul : ∀ (c : ℝ) (φ : ccSub d), A (c • φ) = c • A φ := by
    intro c φ
    refine sa16r_wrep_inj d m p _ _ ?_
    filter_upwards [hA (c • φ), hA φ, sa16r_wrep_smul d m p c (A φ)] with x h1 h2 h3
    rw [h3, h1, h2]
    have := sa16so_F_smul hd2 hs0 hs2 M hμ1 hB0 hB1 c (sa16so_schw φ) x
    exact this
  let Al : ccSub d →ₗ[ℝ] WmpSpace d m p := { toFun := A, map_add' := hadd, map_smul' := hsmul }
  obtain ⟨T, hT1, hT2, -⟩ := sa16r_ext_abstract (sa16r_Jcc d m p) (sa16r_Jcc_dense d m p) Al hC.le hAnorm
  refine ⟨T, hT1, fun φ => ?_⟩
  rw [hT2 φ]
  exact hA φ

end Op5

end HRS.Whole.AppendixA.Phase2SA16R
