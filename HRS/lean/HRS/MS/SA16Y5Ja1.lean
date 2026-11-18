import HRS.MS.SA16Y5Ex0
import HRS.MH.AdjointRdDefs

/-!
# S.A.16 (SA16Y5) Ja1: the heat-convolved nonlocal operator equals the `T`-form (K2/K3)

`sa16y5_euc_eq`: `eucNonlocal s M μ φ = ∑_{ij} M_{ji} ∂_i (ρ ⋆ (μ ∂_jφ))`, with `cv` for the convolution.
`sa16y5_cv_euc`: `g_a ⋆ eucNonlocal s M μ φ = ∑_{ij} M_{ji} Tm a μ i j φ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Ja1
variable {d : ℕ} {s : ℝ}

/-- `S_ij = ∂_i (ρ ⋆ (μ ∂_j φ))` -/
def sa16y5_S (d : ℕ) (s : ℝ) (μ φ : Euc d → ℝ) (i j : Fin d) (y : Euc d) : ℝ :=
  fderiv ℝ (sa16r_cv (rieszKernel d s) (fun y' => μ y' * fderiv ℝ φ y' (sa16z_e j))) y (sa16z_e i)

lemma sa16y5_euc_eq (M : Matrix (Fin d) (Fin d) ℝ) (μ φ : Euc d → ℝ) :
    HRS.MH.AdjointRd.eucNonlocal s M μ φ = fun y => ∑ i, ∑ j, M j i * sa16y5_S d s μ φ i j y := by
  funext y
  unfold HRS.MH.AdjointRd.eucNonlocal sa16y5_S
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hF : (fun x' => ∫ y', rieszKernel d s (x' - y') * (μ y' * fderiv ℝ φ y' (EuclideanSpace.single j (1 : ℝ)))) =
      sa16r_cv (rieszKernel d s) (fun y' => μ y' * fderiv ℝ φ y' (sa16z_e j)) := by
    funext x'
    unfold sa16r_cv
    rw [← integral_sub_left_eq_self (fun z => rieszKernel d s z *
      (μ (x' - z) * fderiv ℝ φ (x' - z) (sa16z_e j))) volume x']
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sub_sub_cancel]
  rw [hF]

lemma sa16y5_S_cont (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ)
    (hφ : IsCcInfty φ) (i j : Fin d) : Continuous (sa16y5_S d s μ φ i j) := by
  have hw : IsCcInfty (fun y' => μ y' * fderiv ℝ φ y' (sa16z_e j)) :=
    sa16y5_cc_mul hμ (sa16s_cc_fderiv hφ (sa16z_e j))
  have h := sa16y5_cv_cc_contDiff (sa16y5_rho_loc hd hs hsd) hw
  exact (h.continuous_fderiv (by simp)).clm_apply continuous_const

lemma sa16y5_S_bdd (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {μ φ : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) (i j : Fin d) : ∃ B, ∀ y, |sa16y5_S d s μ φ i j y| ≤ B := by
  have hw : IsCcInfty (fun y' => μ y' * fderiv ℝ φ y' (sa16z_e j)) :=
    sa16y5_cc_mul hμ (sa16s_cc_fderiv hφ (sa16z_e j))
  have hwi : IsCcInfty (fun y => fderiv ℝ (fun y' => μ y' * fderiv ℝ φ y' (sa16z_e j)) y (sa16z_e i)) :=
    sa16s_cc_fderiv hw (sa16z_e i)
  obtain ⟨Cf, -, hCf⟩ := sa16y5_V_L1 hd hs hsd1 (s := s)
  have hrn := (sa16y5_rn_L1 hd hs hsd (ε := 1) one_pos).1
  have hV := (hCf 1 one_pos i).1
  obtain ⟨b1, hb1⟩ := sa16y5_cv_bdd hrn hwi
  obtain ⟨b2, hb2⟩ := sa16y5_cv_bdd hV hw
  refine ⟨b1 + b2, fun y => ?_⟩
  have := sa16y5_D1 hd hs hsd hw i one_pos y
  unfold sa16y5_S
  rw [this]
  exact (abs_add_le _ _).trans (add_le_add (hb1 y) (hb2 y))

lemma sa16y5_cv_finsum {κ : Euc d → ℝ} (hκ : Integrable κ) {S : Fin d → Fin d → Euc d → ℝ}
    (c : Fin d → Fin d → ℝ) (hS : ∀ i j, Continuous (S i j)) (hb : ∀ i j, ∃ B, ∀ y, |S i j y| ≤ B)
    (x : Euc d) :
    sa16r_cv κ (fun y => ∑ i, ∑ j, c i j * S i j y) x = ∑ i, ∑ j, c i j * sa16r_cv κ (S i j) x := by
  have hint : ∀ i j, Integrable (fun z => κ z * S i j (x - z)) := fun i j => by
    obtain ⟨B, hB⟩ := hb i j
    exact sa16y5_int_bdd hκ (hS i j) hB x
  unfold sa16r_cv
  have e : ∀ z, κ z * ∑ i, ∑ j, c i j * S i j (x - z) = ∑ i, ∑ j, c i j * (κ z * S i j (x - z)) := by
    intro z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun i _ => (integrable_finsetSum _ fun j _ => (hint i j).const_mul (c i j)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul (c i j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

theorem sa16y5_cv_euc (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {a : ℝ} (ha : 0 < a)
    (M : Matrix (Fin d) (Fin d) ℝ) {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) (x : Euc d) :
    sa16r_cv (sa16r_g d a) (HRS.MH.AdjointRd.eucNonlocal s M μ φ) x =
      ∑ i, ∑ j, M j i * sa16y5_Tm d s a μ i j φ x := by
  rw [sa16y5_euc_eq]
  exact sa16y5_cv_finsum (sa16r_g_int ha) (fun i j => M j i) (fun i j => sa16y5_S_cont hd hs hsd hμ hφ i j)
    (fun i j => sa16y5_S_bdd hd hs hsd hsd1 hμ hφ i j) x

end Ja1

end HRS.Whole.AppendixA.Phase2SA16R
