import HRS.MS.SA16Y11Nl1
import HRS.MS.SA16Y5Dn1
import HRS.MS.SA16Y4Ip3
import HRS.MS.SA16QFin2

/-!
# S.A.16 (SA16Y11) Nl2: the interpolated order-one nonlocal operator is Lipschitz in the density (sharp constant)

`sa16y11_NInt_diff`: for two regular density families (`IsRegularDensityW (m+3) Λ`) whose difference has weights `δ` through order `m+2`,
`‖ι_m((NInt μ¹ σ - NInt μ² σ) y)‖ ≤ C δ ‖y‖`, `C = C(d,m,s,p,MB,Λ)`, uniformly in `N ≥ 1`, `t`, `σ`, `M`.
Mollification costs `d^{m+2} 2^{d+3}` on the weight (`sa16y11_mol_Dec`, valid for any weighted `f`, not only densities).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Nl2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y11_pd_le {κ : ℕ} (f : Euc d → ℝ) (r : Fin κ → Fin d) (x : Euc d) :
    |partialDeriv r f x| ≤ ‖iteratedFDeriv ℝ κ f x‖ := by
  unfold partialDeriv
  have h := (iteratedFDeriv ℝ κ f x).le_opNorm (fun l => EuclideanSpace.single (r l) (1 : ℝ))
  have h1 : ∏ l : Fin κ, ‖(EuclideanSpace.single (r l) (1 : ℝ) : Euc d)‖ = 1 := by
    simp
  rw [h1, mul_one] at h
  simpa [Real.norm_eq_abs] using h

lemma sa16y11_mol_Dec (N : ℕ) {k : ℕ} {δ : ℝ} {f : Euc d → ℝ} (hd : 1 ≤ d) (hf : ContDiff ℝ k f)
    (hD : sa16y5_Dec k δ f) :
    sa16y5_Dec k ((d : ℝ) ^ k * (2 ^ (d + 3) * δ)) (sa16q_mol N f) := by
  intro κ hκ x
  have hfκ : ContDiff ℝ κ f := hf.of_le (by exact_mod_cast hκ)
  have hw : ∀ r : Fin κ → Fin d, ∀ x, |partialDeriv r f x| * (1 + ‖x‖) ^ (d + 3) ≤ δ := by
    intro r x
    have h1 := (sa16y11_pd_le f r x).trans (hD κ hκ x)
    have hpos : 0 < (1 + ‖x‖) ^ (d + 3) := by positivity
    have e1 : (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) = ((1 + ‖x‖) ^ (d + 3))⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    rw [e1, ← div_eq_mul_inv, le_div_iff₀ hpos] at h1
    exact h1
  have hw2 : ∀ r : Fin κ → Fin d, ∀ x, |partialDeriv r (sa16q_mol N f) x| * (1 + ‖x‖) ^ (d + 3) ≤
      2 ^ (d + 3) * δ := fun r x => sa16q_mol_pd_weight N hfκ hw r x
  have h := sa16q_weight_conv (a := sa16q_mol N f) (κ := κ) hw2 x
  refine h.trans ?_
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpw : (d : ℝ) ^ κ ≤ (d : ℝ) ^ k := pow_le_pow_right₀ hd0 hκ
  have hδ : 0 ≤ δ := by
    have := hD 0 (Nat.zero_le _) 0
    have h0 : 0 ≤ ‖iteratedFDeriv ℝ 0 f 0‖ := norm_nonneg _
    have hω : 0 < (1 + ‖(0 : Euc d)‖) ^ (-((d + 3 : ℕ) : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    nlinarith
  have hc : 0 ≤ 2 ^ (d + 3) * δ := by positivity
  have hω : 0 ≤ (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpw hc) hω

lemma sa16y11_mol_sub (N : ℕ) {f g : Euc d → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (fun x => sa16q_mol N f x - sa16q_mol N g x) = sa16q_mol N (fun y => f y - g y) := by
  funext x
  unfold sa16q_mol sa16j_conv
  have hρ : Continuous (sa16y_rho d N) := (sa16y_rho_smooth N).continuous
  have hint : ∀ u : Euc d → ℝ, Continuous u → Integrable (fun z => sa16y_rho d N z * u (x - z)) := fun u hu =>
    (hρ.mul (hu.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ((sa16y_rho_compact N).mul_right)
  rw [← integral_sub (hint f hf) (hint g hg)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [mul_sub]

set_option maxHeartbeats 3200000 in
theorem sa16y11_NInt_diff (d m : ℕ) (hd : 1 ≤ d) (s p MB Λ : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs1 : s < (d : ℝ) - 1) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) →
      ∀ (t : ℝ), 0 < t → ∀ μ1 μ2 : ℝ → Euc d → ℝ,
      (∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ1 r)) →
      (∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ2 r)) →
      ∀ δ : ℝ, 0 ≤ δ → (∀ r ∈ Icc (0 : ℝ) t, sa16y5_Dec (m + 2) δ (fun y => μ1 r y - μ2 r y)) →
      ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Icc (0 : ℝ) t, ∀ y : WmpSpace d (m + 1 + 1) p,
        ‖sa16r_iota d m p ((sa16y5_NInt d m N p s M t μ1 σ - sa16y5_NInt d m N p s M t μ2 σ) y)‖ ≤ C * δ * ‖y‖ := by
  obtain ⟨Wd, hWd0, hdens⟩ := sa16y5_density_data hd m Λ
  obtain ⟨C0, hC0, hG⟩ := sa16y11_Gop_diff d m hd s p MB hs0 hs1 hfar Wd hWd0
  set cm : ℝ := (d : ℝ) ^ (m + 2) * 2 ^ (d + 3) with hcm
  have hcm0 : 0 < cm := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    rw [hcm]; positivity
  refine ⟨C0 * cm, by positivity, fun M hM t ht μ1 μ2 h1 h2 δ hδ hDd N hN σ hσ y => ?_⟩
  have hnode := fun i (hi : i ∈ Finset.range (N + 1)) => sa16y4_node_mem hN ht hi
  have hterm : ∀ i ∈ Finset.range (N + 1),
      ‖sa16r_iota d m p ((sa16y5_Gop d m p s M (sa16q_mol N (μ1 (t - (i : ℝ) * t / N))) -
        sa16y5_Gop d m p s M (sa16q_mol N (μ2 (t - (i : ℝ) * t / N)))) y)‖ ≤ C0 * (cm * δ) * ‖y‖ := by
    intro i hi
    set r := t - (i : ℝ) * t / N with hr
    have hrm : r ∈ Icc (0 : ℝ) t := hnode i hi
    obtain ⟨-, hS1⟩ := hdens (μ1 r) (h1 r hrm)
    obtain ⟨-, hS2⟩ := hdens (μ2 r) (h2 r hrm)
    obtain ⟨hSB1, hDec1, -⟩ := hS1 N
    obtain ⟨hSB2, hDec2, -⟩ := hS2 N
    have hc1 : Continuous (μ1 r) := (h1 r hrm).1.continuous
    have hc2 : Continuous (μ2 r) := (h2 r hrm).1.continuous
    have hdiff : ContDiff ℝ (m + 2 : ℕ) (fun y => μ1 r y - μ2 r y) :=
      ((h1 r hrm).1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 3))).sub
        ((h2 r hrm).1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 3)))
    have hmD := sa16y11_mol_Dec N hd hdiff (hDd r hrm)
    rw [← sa16y11_mol_sub N hc1 hc2] at hmD
    have := hG M hM _ _ hSB1 hSB2 hDec1 hDec2 _ (by positivity) hmD y
    refine this.trans (le_of_eq ?_)
    rw [hcm]; ring
  have hy : (sa16y5_NInt d m N p s M t μ1 σ - sa16y5_NInt d m N p s M t μ2 σ) y =
      ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ •
        ((sa16y5_Gop d m p s M (sa16q_mol N (μ1 (t - (i : ℝ) * t / N))) -
          sa16y5_Gop d m p s M (sa16q_mol N (μ2 (t - (i : ℝ) * t / N)))) y) := by
    unfold sa16y5_NInt
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_sub, Finset.sum_sub_distrib]
  rw [hy, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have hsum := sa16y4_hat_sum hN ht hσ
  calc ∑ i ∈ Finset.range (N + 1), ‖sa16r_iota d m p (sa16y4_hat N t i σ •
        ((sa16y5_Gop d m p s M (sa16q_mol N (μ1 (t - (i : ℝ) * t / N))) -
          sa16y5_Gop d m p s M (sa16q_mol N (μ2 (t - (i : ℝ) * t / N)))) y))‖
      ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * (C0 * (cm * δ) * ‖y‖) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sa16y4_hat_nonneg N t i σ)]
        exact mul_le_mul_of_nonneg_left (hterm i hi) (sa16y4_hat_nonneg N t i σ)
    _ = C0 * cm * δ * ‖y‖ := by
        rw [← Finset.sum_mul, hsum]; ring

end Nl2

end HRS.Whole.AppendixA.Phase2SA16R

end
