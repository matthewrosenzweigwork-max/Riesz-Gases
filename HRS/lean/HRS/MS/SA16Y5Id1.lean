import HRS.MS.SA16Y5Gm2
import HRS.MS.SA16Y5Pa1
import HRS.MS.SA16Y5Vw2
import HRS.MS.SA16Y3EnD14

/-!
# S.A.16 (SA16Y5) Id1: the heat-composed nonlocal operator `Q_a = Γ_{a/2} Γ_{a/2} N` on `W^{m+2,p}` (K3/B8)

For a bounded `N : W^{m+2,p} → W^{m,p}` with `wrep (N (Jcc φ)) = eucNonlocal s M μ φ`:
`Qh a N := Γ^{(m+1)}_{a/2} ∘ Γ^{(m)}_{a/2} ∘ N : W^{m+2,p} → W^{m+2,p}`.
`sa16y5_Qh_eq_Pa`: `Qh a N = P_a` (the operator of `Pa1`) for `0 < a ≤ 1`; `sa16y5_Qh_bound`: `‖Qh a N‖ ≤ C a^{-(s+2-d)/2}`;
`sa16y5_Qh_iota`: `ι (Qh a N x) = Γ^{(m)}_a (N x)` (so the weak heat identity of `Γ` transfers).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Id1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)] {s : ℝ}

def sa16y5_Qh (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (a : ℝ) (N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p) :
    WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1 + 1) p :=
  (sa16r_Gam d (m + 1) p (a / 2)).comp ((sa16r_Gam d m p (a / 2)).comp N)

lemma sa16y5_euc_cont_bdd (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1)
    (M : Matrix (Fin d) (Fin d) ℝ) {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) :
    Continuous (HRS.MH.AdjointRd.eucNonlocal s M μ φ) ∧
      ∃ B, ∀ x, |HRS.MH.AdjointRd.eucNonlocal s M μ φ x| ≤ B := by
  rw [sa16y5_euc_eq]
  refine ⟨continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    continuous_const.mul (sa16y5_S_cont hd hs hsd hμ hφ i j), ?_⟩
  choose Bf hBf using fun i j => sa16y5_S_bdd hd hs hsd hsd1 hμ hφ i j
  refine ⟨∑ i, ∑ j, |M j i| * Bf i j, fun x => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hBf i j x) (abs_nonneg _)

lemma sa16y5_cv_bdd' {κ F : Euc d → ℝ} (hκ : Integrable κ) {B : ℝ} (hB : ∀ y, |F y| ≤ B) (x : Euc d) :
    |sa16r_cv κ F x| ≤ (∫ z, |κ z|) * B := by
  unfold sa16r_cv
  rw [← Real.norm_eq_abs]
  calc ‖∫ z, κ z * F (x - z)‖ ≤ ∫ z, |κ z| * B := by
        refine norm_integral_le_of_norm_le (hκ.abs.mul_const B) (Eventually.of_forall fun z => ?_)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
    _ = _ := by rw [integral_mul_const]

theorem sa16y5_Qh_wrep (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) (m : ℕ)
    {a : ℝ} (ha : 0 < a) (M : Matrix (Fin d) (Fin d) ℝ) {μ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ)
    (N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hN : ∀ φ : ccSub d, wrep d m p (N (sa16r_Jcc d (m + 1 + 1) p φ)) =ᵐ[volume]
      HRS.MH.AdjointRd.eucNonlocal s M μ φ.1) (φ : ccSub d) :
    wrep d (m + 1 + 1) p (sa16y5_Qh d m p a N (sa16r_Jcc d (m + 1 + 1) p φ)) =ᵐ[volume]
      sa16r_cv (sa16r_g d a) (HRS.MH.AdjointRd.eucNonlocal s M μ φ.1) ∧
    wrep d (m + 1) p (sa16r_Gam d m p (a / 2) (N (sa16r_Jcc d (m + 1 + 1) p φ))) =ᵐ[volume]
      sa16r_cv (sa16r_g d (a / 2)) (HRS.MH.AdjointRd.eucNonlocal s M μ φ.1) := by
  have ha2 : 0 < a / 2 := by linarith
  obtain ⟨hFc, B, hB⟩ := sa16y5_euc_cont_bdd hd hs hsd hsd1 M hμ φ.2
  have h1 := sa16y5_Gam_wrep ha2 m (N (sa16r_Jcc d (m + 1 + 1) p φ)) (hN φ) hFc hB
  refine ⟨?_, h1⟩
  -- the intermediate function `g_{a/2} ⋆ F` is continuous and bounded
  have hf1 : sa16r_cv (sa16r_g d (a / 2)) (HRS.MH.AdjointRd.eucNonlocal s M μ φ.1) =
      sa16y5_Fam d s (a / 2) M μ φ.1 :=
    (sa16y5_Fam_eq hd hs hsd hsd1 ha2 M hμ φ.2).symm
  have hf1c : Continuous (sa16r_cv (sa16r_g d (a / 2)) (HRS.MH.AdjointRd.eucNonlocal s M μ φ.1)) := by
    rw [hf1]; exact (sa16y5_Fam_smooth hd hs hsd hsd1 ha2 M hμ φ.2).continuous
  have hf1b : ∀ x, |sa16r_cv (sa16r_g d (a / 2)) (HRS.MH.AdjointRd.eucNonlocal s M μ φ.1) x| ≤
      (∫ z, |sa16r_g d (a / 2) z|) * B := sa16y5_cv_bdd' (sa16r_g_int ha2) hB
  have h2 := sa16y5_Gam_wrep ha2 (m + 1) (sa16r_Gam d m p (a / 2) (N (sa16r_Jcc d (m + 1 + 1) p φ))) h1 hf1c hf1b
  unfold sa16y5_Qh
  simp only [ContinuousLinearMap.comp_apply]
  refine h2.trans (Eventually.of_forall fun x => ?_)
  have := sa16y5_gg_conv ha2 ha2 hFc hB x
  rw [show a / 2 + a / 2 = a by ring] at this
  exact this

end Id1

end HRS.Whole.AppendixA.Phase2SA16R
