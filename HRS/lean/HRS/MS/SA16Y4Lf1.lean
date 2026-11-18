import HRS.MS.SA16Y3Ex8
import HRS.MS.SA16Y3Yg2
import HRS.MS.SA16Y4Fam1
import HRS.MS.SA16Y3Ex7
import HRS.MS.SA16RExt3

/-!
# S.A.16 (SA16Y4) Lf1: derivatives of the cut-off mollification fall on the mollifier (level-gaining bound)

`sa16y4_cutmol_pd_eLp`: for `ψ ∈ C_c^∞`, every coordinate derivative of `cutmol_n ψ = ρ_n ⋆ (χ_{n+1} ψ)` satisfies
`‖∂^κ cutmol_n ψ‖_{L^p} ≤ (∫|∂^κ ρ_n|) ‖ψ‖_{L^p}` (derivative on the kernel + Young).  The constant depends on `n, κ` only.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q

section Lf1
variable {d : ℕ}

lemma sa16y4_cutmol_pd_eLp {p : ℝ} (hp : 1 ≤ p) (n : ℕ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    {j : ℕ} (κ : Fin j → Fin d) :
    eLpNorm (partialDeriv κ (sa16y3_cutmol d n ψ)) (ENNReal.ofReal p) volume ≤
      (∫⁻ y, ‖partialDeriv κ (sa16y_rho d n) y‖ₑ) * eLpNorm ψ (ENNReal.ofReal p) volume := by
  set h : EuclideanSpace ℝ (Fin d) → ℝ := fun y => sa16y3_cut d n y * ψ y with hh
  have hhc : IsCcInfty h := sa16y3_cut_cc hψ n
  have hρc := sa16y4_rho_cc (d := d) n
  -- representation with the derivative on the kernel
  have hrep : sa16y3_cutmol d n ψ = fun x => ∫ y, h y * sa16y_rho d n (x - y) := by
    funext x
    rw [sa16y3_cutmol_eq_int, ← integral_sub_left_eq_self (fun y => h y * sa16y_rho d n (x - y)) volume x]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hh, sub_sub_cancel]
    ring
  have hpd : partialDeriv κ (sa16y3_cutmol d n ψ) =
      fun x => ∫ z, partialDeriv κ (sa16y_rho d n) z * h (x - z) := by
    rw [hrep, sa16y3_conv_pd (sa16s_integrable_of_cc hhc.1.continuous hhc.2) hρc κ]
    funext x
    rw [← integral_sub_left_eq_self (fun y => h y * partialDeriv κ (sa16y_rho d n) (x - y)) volume x]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sub_sub_cancel]
    ring
  rw [hpd]
  refine (sa16y3_young_eLp hp _ _ (sa16s_cc_partialDeriv hρc κ).1.continuous.measurable
    hhc.1.continuous.measurable).trans ?_
  refine mul_le_mul' le_rfl ?_
  refine eLpNorm_mono hhc.1.continuous.aestronglyMeasurable fun x => ?_
  rw [hh]
  simp only [Real.norm_eq_abs, abs_mul]
  have h0 : |sa16y3_cut d n x| ≤ 1 := by
    unfold sa16y3_cut sa16j_chi
    rw [abs_of_nonneg ((sa16j_bump d).nonneg)]
    exact (sa16j_bump d).le_one
  calc |sa16y3_cut d n x| * |ψ x| ≤ 1 * |ψ x| := mul_le_mul_of_nonneg_right h0 (abs_nonneg _)
    _ = |ψ x| := one_mul _

lemma sa16y4_eLp_le_jet {p : ℝ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (m : ℕ) :
    eLpNorm ψ (ENNReal.ofReal p) volume ≤ eLpNorm (wJet m ψ) (ENNReal.ofReal p) volume := by
  refine eLpNorm_mono hψ.1.continuous.aestronglyMeasurable fun x => ?_
  rw [Real.norm_eq_abs]
  have := sa16j_pd_le_jet m ψ x (Nat.zero_le m) (fun l => l.elim0)
  simpa [partialDeriv, iteratedFDeriv_zero_apply] using this

set_option maxHeartbeats 1600000 in
theorem sa16y4_extend_cutmol_gain {p : ℝ} [Fact (2 ≤ p)] (hp : 1 ≤ p) (m n : ℕ) :
    ∃ S : WmpSpace d m p →L[ℝ] WmpSpace d (m + 1 + 1) p,
      (∀ ψ : ccSub d, S (sa16r_Jcc d m p ψ) =
        sa16r_Jcc d (m + 1 + 1) p ⟨sa16y3_cutmol d n ψ.1, sa16y3_cutmol_cc ψ.2 n⟩) ∧
      ∀ T : WmpSpace d m p →L[ℝ] WmpSpace d m p,
        (∀ ψ : ccSub d, T (sa16r_Jcc d m p ψ) = sa16r_J d m p (sa16y3_Lop m p n ψ)) →
          ∀ G, sa16sz_iota2 d m p (S G) = T G := by
  set Kn : ℝ≥0∞ := ∑ j ∈ Finset.range (m + 1 + 1 + 1), ∑ idx : Fin j → Fin d,
    ∫⁻ y, ‖partialDeriv idx (sa16y_rho d n) y‖ₑ with hKn
  have hKnt : Kn ≠ ⊤ := by
    refine ENNReal.sum_ne_top.2 fun j _ => ENNReal.sum_ne_top.2 fun idx _ => ?_
    have := (sa16s_cc_partialDeriv (sa16y4_rho_cc (d := d) n) idx)
    exact (this.1.continuous.integrable_of_hasCompactSupport this.2).hasFiniteIntegral.ne
  set c : ℝ := (Fintype.card (WIndex d (m + 1 + 1)) : ℝ) * Kn.toReal with hc
  have hc0 : 0 ≤ c := by positivity
  have hb : ∀ ψ : ccSub d, ‖sa16r_J d (m + 1 + 1) p (sa16y3_Lop (m + 1 + 1) p n ψ)‖ ≤
      c * ‖sa16r_Jcc d m p ψ‖ := by
    intro ψ
    have hcc := sa16y3_cutmol_cc ψ.2 n
    rw [sa16y3_Lop_eq, sa16r_Jcc_norm, sa16r_Jcc_norm]
    have hS : MemLp (sa16j_S d (m + 1 + 1) (sa16y3_cutmol d n ψ.1)) (ENNReal.ofReal p) volume :=
      sa16y3_cutmol_S (p := p) ψ.2 (m + 1 + 1) n
    have hE : eLpNorm ψ.1 (ENNReal.ofReal p) volume < ⊤ :=
      (ψ.2.1.continuous.memLp_of_hasCompactSupport ψ.2.2).eLpNorm_lt_top
    have hw := sa16y_wnorm_of_pd d (m + 1 + 1) p (f := sa16y3_cutmol d n ψ.1) hcc.1
      (K := Kn * eLpNorm ψ.1 (ENNReal.ofReal p) volume) (ENNReal.mul_lt_top hKnt.lt_top hE)
      (fun {j} hj idx => by
        refine (sa16y4_cutmol_pd_eLp hp n ψ.2 idx).trans (mul_le_mul' ?_ le_rfl)
        rw [hKn]
        exact (Finset.single_le_sum (f := fun idx : Fin j → Fin d => ∫⁻ y, ‖partialDeriv idx (sa16y_rho d n) y‖ₑ)
          (fun _ _ => bot_le) (Finset.mem_univ idx)).trans
          (Finset.single_le_sum (f := fun j => ∑ idx : Fin j → Fin d, ∫⁻ y, ‖partialDeriv idx (sa16y_rho d n) y‖ₑ)
            (fun _ _ => bot_le) (Finset.mem_range.2 (by omega))))
    rw [← sa16j_wNormE_eq d (m + 1 + 1) p hcc.1 hS]
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top hKnt hE.ne)) hw
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at h2
    refine h2.trans ?_
    rw [hc]
    have h3 : (eLpNorm ψ.1 (ENNReal.ofReal p) volume).toReal ≤ (eLpNorm (wJet m ψ.1) (ENNReal.ofReal p) volume).toReal :=
      ENNReal.toReal_mono (sa16r_jet_memLp_cc (p := p) ψ.2 m).eLpNorm_lt_top.ne (sa16y4_eLp_le_jet ψ.2 m)
    simp only [ENNReal.toReal_natCast]
    calc (Fintype.card (WIndex d (m + 1 + 1)) : ℝ) * (Kn.toReal * (eLpNorm ψ.1 (ENNReal.ofReal p) volume).toReal)
        ≤ (Fintype.card (WIndex d (m + 1 + 1)) : ℝ) * (Kn.toReal * (eLpNorm (wJet m ψ.1) (ENNReal.ofReal p) volume).toReal) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 ENNReal.toReal_nonneg) (by positivity)
      _ = _ := by ring
  obtain ⟨S, hS1, hS2, -⟩ := sa16r_extend_cc d m (m + 1 + 1) p (sa16y3_Lop (m + 1 + 1) p n) hc0 hb
  refine ⟨S, fun ψ => by rw [hS2 ψ, sa16y3_Lop_eq], fun T hT G => ?_⟩
  refine (sa16r_Jcc_dense d m p).induction_on G (isClosed_eq ?_ ?_) (fun ψ => ?_)
  · exact (sa16sz_iota2 d m p).continuous.comp S.continuous
  · exact T.continuous
  · rw [hS2 ψ, hT ψ, sa16y3_Lop_eq, sa16y3_Lop_eq, sa16sz_iota2_Jcc]

end Lf1

end HRS.Whole.AppendixA.Phase2SA16R
