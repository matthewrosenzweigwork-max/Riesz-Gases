import HRS.MS.SA16Y4Li1
import HRS.MS.SA16Y3S5c

/-!
# S.A.16 (SA16Y5) Li2: weak identity, bounded integrand and equi-Lipschitz pairings for `K = B_b - N'` (order-one nonlocal term)

The order-one analogues of `sa16y3_K_pair_eq`, `sa16y3_K_pair_bound`, `sa16y4_weak_integrand`, `sa16y3_lip_trunc` where the nonlocal term is a
CLM `N' : W^{m+2,p} → W^{m+1,p}` (not `T1 ι`), whose pairing satisfies `|ℓ_ψ(N' y)| ≤ Cn ‖ι² y‖` (weaker norm; `Cn` from the derivative-on-the-solution
form of the nonlocal pairing, see Nf1).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Li2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y5_K_pair_eq {m : ℕ} {B' : ℝ} {bc : Fin d → Euc d → ℝ}
    (hbo : SA16BddCoef (m + 1) B' bc) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    (N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p) (ℓn : WmpSpace d m p → ℝ)
    (hN : ∀ y, sa16r_ell d (m + 1) p hψ (N y) = ℓn (sa16sz_iota2 d m p y))
    (K : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : K = sa16so_B d (m + 1) p bc - N) (y : WmpSpace d (m + 1 + 1) p) :
    sa16r_ell d (m + 1) p hψ (K y) =
      -(∫ x, wrep d m p (sa16sz_iota2 d m p y) x * sa16so_divFun bc ψ x) - ℓn (sa16sz_iota2 d m p y) := by
  have h1 : sa16r_ell d (m + 1) p hψ (K y) =
      -sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y - ℓn (sa16sz_iota2 d m p y) := by
    rw [hK, sub_apply, map_sub, sa16so_ell_B hbo hψ y, hN y]
  rw [h1, ← sa16y3_ell_iota2 (sa16so_cc_div hbo hψ), sa16r_ell_apply]

set_option maxHeartbeats 1000000 in
theorem sa16y5_K_pair_bound {m : ℕ} {B' Cn cN R0 : ℝ} {bc : Fin d → Euc d → ℝ}
    (hbo : SA16BddCoef (m + 1) B' bc) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    (hNb : ∀ x, |sa16so_divFun bc ψ x| ≤ cN * (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) x)
    (hcN : 0 ≤ cN) (N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hNn : ∀ y, |sa16r_ell d (m + 1) p hψ (N y)| ≤ Cn * ‖sa16sz_iota2 d m p y‖)
    (K : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : K = sa16so_B d (m + 1) p bc - N) (y : WmpSpace d (m + 1 + 1) p) :
    |sa16r_ell d (m + 1) p hψ (K y)| ≤
      (cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) + Cn) *
        ‖sa16sz_iota2 d m p y‖ := by
  have hsplit : sa16r_ell d (m + 1) p hψ (K y) =
      -sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y - sa16r_ell d (m + 1) p hψ (N y) := by
    rw [hK, sub_apply, map_sub, sa16so_ell_B hbo hψ y]
  have hA : |sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y| ≤
      cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) *
        ‖sa16sz_iota2 d m p y‖ := by
    rw [← sa16y3_ell_iota2 (sa16so_cc_div hbo hψ), sa16r_ell_apply]
    exact sa16y3_ell_sup_bound _ (sa16so_cc_div hbo hψ).1.continuous.aestronglyMeasurable hcN hNb
  rw [hsplit]
  calc |-sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y - sa16r_ell d (m + 1) p hψ (N y)|
      ≤ |sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y| + |sa16r_ell d (m + 1) p hψ (N y)| := by
        rw [sub_eq_add_neg, ← abs_neg (sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y)]
        simpa [abs_neg] using abs_add_le (-sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y)
          (-sa16r_ell d (m + 1) p hψ (N y))
    _ ≤ _ := (add_le_add hA (hNn y)).trans (le_of_eq (by ring))

set_option maxHeartbeats 1600000 in
theorem sa16y5_weak_integrand {m : ℕ} {ν T B' Bk Cn cN R0 Bm : ℝ} (hν : 0 < ν) (hT : 0 < T) (hcN : 0 ≤ cN)
    (hCn : 0 ≤ Cn)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbo : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) B' (bc r))
    (N : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ r, K r = sa16so_B d (m + 1) p (bc r) - N r)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ Bk)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (m + 1 + 1) p)
    {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    (hNn : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, |sa16r_ell d (m + 1) p hψ (N r y)| ≤ Cn * ‖sa16sz_iota2 d m p y‖)
    (hNb : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, |sa16so_divFun (bc r) ψ x| ≤
      cN * (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) x)
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (gainKer (sa16r_GamT d (m + 1) p ν) K) u τ)
    (hbd : ∀ r ∈ Icc (0 : ℝ) T, ‖sa16sz_iota2 d m p (u r)‖ ≤ Bm) :
    let f : ℝ → ℝ := fun σ => ν * sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (u σ) +
      sa16r_ell d (m + 1) p hψ (K σ (u σ))
    (∀ τ ∈ Icc (0 : ℝ) T, sa16r_ell d (m + 1 + 1) p hψ (u τ) =
        sa16r_ell d (m + 1 + 1) p hψ φ + ∫ σ in (0 : ℝ)..τ, f σ) ∧
      ContinuousOn f (Icc 0 T) ∧
      ∀ σ ∈ Icc (0 : ℝ) T, |f σ| ≤ (ν * ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ +
        cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) + Cn) * Bm := by
  intro f
  have hBK0 : 0 ≤ Bk := (ContinuousLinearMap.opNorm_nonneg _).trans (hKb 0 ⟨le_rfl, hT.le⟩)
  have hid := sa16r_fixedn_weak (B := Bk) hν hT hBK0 (m + 1) K hKb hKc φ hψ (sa16sw_cc_lap hψ)
    (sa16sw_heatWeak hν T (m + 1) hψ) hu hsol
  have hcont : ContinuousOn f (Icc 0 T) := by
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_const.mul ((sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ)).continuous.comp_continuousOn hu)
    · exact (sa16r_ell d (m + 1) p hψ).continuous.comp_continuousOn (sa16y3_K_continuousOn K hKb hKc hu)
  refine ⟨fun τ hτ => hid τ hτ, hcont, fun σ hσ => ?_⟩
  have h1 : |sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (u σ)| ≤ ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ * Bm := by
    rw [← sa16y3_ell_iota2 (sa16sw_cc_lap hψ), ← Real.norm_eq_abs]
    exact ((sa16r_ell d m p _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hbd σ hσ) (ContinuousLinearMap.opNorm_nonneg _))
  have h2 := sa16y5_K_pair_bound (hbo σ hσ) hψ (hNb σ hσ) hcN (N σ) (hNn σ hσ) (K σ) (hK σ) (u σ)
  have h3 : |sa16r_ell d (m + 1) p hψ (K σ (u σ))| ≤
      (cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) + Cn) * Bm :=
    h2.trans (mul_le_mul_of_nonneg_left (hbd σ hσ)
      (add_nonneg (mul_nonneg hcN (Real.rpow_nonneg ENNReal.toReal_nonneg _)) hCn))
  calc |f σ| ≤ |ν * sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (u σ)| +
        |sa16r_ell d (m + 1) p hψ (K σ (u σ))| := abs_add_le _ _
    _ ≤ ν * (‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ * Bm) + (cN * (volume (closedBall (0 : Euc d) R0)).toReal ^
        (1 / Real.conjExponent p) + Cn) * Bm := by
        refine add_le_add ?_ h3
        rw [abs_mul, abs_of_pos hν]
        exact mul_le_mul_of_nonneg_left h1 hν.le
    _ = _ := by ring

theorem sa16y5_lip_trunc {m : ℕ} {ν T B' Bk Cn cN R0 Bm : ℝ} (hν : 0 < ν) (hT : 0 < T) (hcN : 0 ≤ cN)
    (hCn : 0 ≤ Cn)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbo : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) B' (bc r))
    (N : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ r, K r = sa16so_B d (m + 1) p (bc r) - N r)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ Bk)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (m + 1 + 1) p)
    {ψ χ : Euc d → ℝ} (hψ : IsCcInfty ψ) (hχ : IsCcInfty χ) (hHW : SA16RHeatWeak d (m + 1) p ν T hψ hχ)
    (hNn : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, |sa16r_ell d (m + 1) p hψ (N r y)| ≤ Cn * ‖sa16sz_iota2 d m p y‖)
    (hNb : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, |sa16so_divFun (bc r) ψ x| ≤
      cN * (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) x)
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (gainKer (sa16r_GamT d (m + 1) p ν) K) u τ)
    (hbd : ∀ r ∈ Icc (0 : ℝ) T, ‖sa16sz_iota2 d m p (u r)‖ ≤ Bm) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ τ' ∈ Icc (0 : ℝ) T,
      |sa16r_ell d (m + 1 + 1) p hψ (u τ) - sa16r_ell d (m + 1 + 1) p hψ (u τ')| ≤
        (ν * ‖sa16r_ell d m p hχ‖ + cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) +
          Cn) * Bm * |τ - τ'| := by
  have hBm0 : 0 ≤ Bm := (norm_nonneg _).trans (hbd 0 ⟨le_rfl, hT.le⟩)
  have h := sa16y3_lip_pairD (k := m + 1) (ν := ν) (T := T) (B := Bk) (BK := Bk)
    (Lψ := (cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) + Cn) * Bm)
    (Lχ := ‖sa16r_ell d m p hχ‖ * Bm) hν hT
    ((ContinuousLinearMap.opNorm_nonneg _).trans (hKb 0 ⟨le_rfl, hT.le⟩)) K hKb hKc φ hψ hχ hHW hu hsol
    (fun r hr => by
      rw [← sa16y3_ell_iota2 hχ, ← Real.norm_eq_abs]
      exact ((sa16r_ell d m p hχ).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbd r hr) (ContinuousLinearMap.opNorm_nonneg _)))
    (fun r hr => by
      have := sa16y5_K_pair_bound (hbo r hr) hψ (hNb r hr) hcN (N r) (hNn r hr) (K r) (hK r) (u r)
      exact this.trans (mul_le_mul_of_nonneg_left (hbd r hr)
        (add_nonneg (mul_nonneg hcN (Real.rpow_nonneg ENNReal.toReal_nonneg _)) hCn)))
  intro τ hτ τ' hτ'
  refine (h τ hτ τ' hτ').trans (le_of_eq ?_)
  ring

end Li2

end HRS.Whole.AppendixA.Phase2SA16R
