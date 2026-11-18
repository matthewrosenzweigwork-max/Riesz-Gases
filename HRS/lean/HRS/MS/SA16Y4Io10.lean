import HRS.MS.SA16Y4Io9
import HRS.MS.SA16SOp5

/-!
# S.A.16 (SA16Y4) Io10: the order-one nonlocal operator `W^{m+1,p} → W^{m,p}` (`0 ≤ s < d-1`)

`sa16y4io_G_exists`: for `1 ≤ d`, `0 ≤ s < d-1`, `d < p(s+1)`, `|M_{ij}| ≤ MB`, `μ` a `(m+3,Λ)`-regular density: there is `C > 0`
(uniform in `M, μ`) and a CLM `T : W^{m+1,p} → W^{m,p}`, `‖T‖ ≤ C`, with `wrep (T (Jcc φ)) = eucNonlocal s M μ φ` a.e. for `φ ∈ C_c^∞`
(the exact analogue of `sa16so_G_exists` with one derivative of loss; this is the operator needed in `sa16r_fixedn_mild` for `iso`/`hilbert`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Io10
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

section Lin
variable (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1)
include hd hs hs1

lemma sa16y4io_F_add (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) {B0 B1 : ℝ}
    (hB0 : ∀ x, |a x| ≤ B0) (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1) (u v : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M a ⇑(u + v) x =
      HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x + HRS.MH.AdjointRd.eucNonlocal s M a ⇑v x := by
  rw [sa16y4io_F_pointwise hd hs hs1 M ha1 hB0 hB1 (u + v) x, sa16y4io_F_pointwise hd hs hs1 M ha1 hB0 hB1 u x,
    sa16y4io_F_pointwise hd hs hs1 M ha1 hB0 hB1 v x, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_add, ← integral_add (sa16y4io_Fint_integrable hd hs hs1 ha1 hB0 hB1 u i j x)
    (sa16y4io_Fint_integrable hd hs hs1 ha1 hB0 hB1 v i j x)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h1 : fderiv ℝ ⇑(u + v) (x - y) = fderiv ℝ ⇑u (x - y) + fderiv ℝ ⇑v (x - y) := by
    rw [show ⇑(u + v) = ⇑u + ⇑v from funext fun x => rfl, fderiv_add u.differentiableAt v.differentiableAt]
  simp only [h1, ContinuousLinearMap.add_apply]
  ring

lemma sa16y4io_F_smul (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) {B0 B1 : ℝ}
    (hB0 : ∀ x, |a x| ≤ B0) (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1) (c : ℝ) (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M a ⇑(c • u) x = c * HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x := by
  rw [sa16y4io_F_pointwise hd hs hs1 M ha1 hB0 hB1 (c • u) x, sa16y4io_F_pointwise hd hs hs1 M ha1 hB0 hB1 u x,
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

/-- **The order-one nonlocal operator `W^{m+1,p} → W^{m,p}`** (constant uniform in `M`, `μ`) -/
theorem sa16y4io_G_exists (d m : ℕ) (hd : 1 ≤ d) (s p MB Λ : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs1 : s < (d : ℝ) - 1) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) → ∀ μ : Euc d → ℝ,
      IsRegularDensityW (m + 3) Λ μ →
        ∃ T : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d m p, ‖T‖ ≤ C ∧ ∀ φ : ccSub d,
          wrep d m p (T (sa16r_Jcc d (m + 1) p φ)) =ᵐ[volume]
            HRS.MH.AdjointRd.eucNonlocal s M μ φ.1 := by
  obtain ⟨C, hC, hbd⟩ := sa16y4io_nonlocal_bound d m hd s p MB Λ hs0 hs1 hfar
  refine ⟨C, hC, fun M hM μ hμ => ?_⟩
  obtain ⟨hCd, hbdd, -⟩ := sa16q_reg_data hμ
  have hμ1 : ContDiff ℝ 1 μ := hCd.of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
  set B0 := max Λ 0
  have hB0 := sa16q_reg_abs hμ
  have hB1 := sa16q_reg_fderiv hμ
  -- finiteness and bound
  have hfin : ∀ φ : ccSub d, wNormE m p (HRS.MH.AdjointRd.eucNonlocal s M μ φ.1) ≤
      ENNReal.ofReal (C * ‖sa16r_Jcc d (m + 1) p φ‖) := by
    intro φ
    have h := hbd M hM μ hμ (sa16so_schw φ)
    rw [sa16so_schw_coe, sa16so_wNormE_cc (m + 1)] at h
    rwa [ENNReal.ofReal_mul hC.le]
  have hex : ∀ φ : ccSub d, ∃ G : WmpSpace d m p,
      wrep d m p G =ᵐ[volume] HRS.MH.AdjointRd.eucNonlocal s M μ φ.1 := fun φ =>
    sa16so_lift_exists m (lt_of_le_of_lt (hfin φ) ENNReal.ofReal_lt_top)
  choose A hA using hex
  have hAnorm : ∀ φ : ccSub d, ‖A φ‖ ≤ C * ‖sa16r_Jcc d (m + 1) p φ‖ := by
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
    have := sa16y4io_F_add hd hs0 hs1 M hμ1 hB0 hB1 (sa16so_schw φ) (sa16so_schw ψ) x
    exact this
  have hsmul : ∀ (c : ℝ) (φ : ccSub d), A (c • φ) = c • A φ := by
    intro c φ
    refine sa16r_wrep_inj d m p _ _ ?_
    filter_upwards [hA (c • φ), hA φ, sa16r_wrep_smul d m p c (A φ)] with x h1 h2 h3
    rw [h3, h1, h2]
    have := sa16y4io_F_smul hd hs0 hs1 M hμ1 hB0 hB1 c (sa16so_schw φ) x
    exact this
  let Al : ccSub d →ₗ[ℝ] WmpSpace d m p := { toFun := A, map_add' := hadd, map_smul' := hsmul }
  obtain ⟨T, hT1, hT2, -⟩ := sa16r_ext_abstract (sa16r_Jcc d (m + 1) p) (sa16r_Jcc_dense d (m + 1) p) Al hC.le hAnorm
  refine ⟨T, hT1, fun φ => ?_⟩
  rw [hT2 φ]
  exact hA φ


end Io10

end HRS.Whole.AppendixA.Phase2SA16R
