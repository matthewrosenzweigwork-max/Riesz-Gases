import HRS.MS.SA16Y5Nf1
import HRS.MS.SA16Y4Nc6

/-!
# S.A.16 (SA16Y5) Nf2: the derivative-on-the-solution nonlocal functional `Φ_a` on `W^{m,p}`: uniform bound and limit

`sa16y5_Phi a w = -∑_{ij} M_{ji} ∫ w_{e_j} (a κ_i)`, a bounded functional on `W^{m,p}` (`m ≥ 1`) for a decaying coefficient `a`.
`sa16y5_nl_data`: uniform `L^{p'}` bound of `a κ_i` for all continuous `a` with `|a| ≤ W (1+|x|)^{-(d+3)}`;
`sa16y5_Phi_bound`: `|Φ_a w| ≤ d² MB cψ ‖w‖`; `sa16y5_nl_rep`: `ℓ_ψ(N y) = Φ_a(ι² y)` for an order-one operator `N` of `a` (from Nf1);
`sa16y5_Phi_tendsto`: `Φ_{a_j}(g_j) → Φ_μ(G)` for bounded weakly convergent `g_j ⇀ G` and `a_j → μ` pointwise with a common decay bound
(copy of the tail of `sa16y4_nl_tendsto`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Nf2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the nonlocal functional with the derivative on the solution -/
def sa16y5_Phi (d m : ℕ) (hm : 1 ≤ m) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    (a ψ : EuclideanSpace ℝ (Fin d) → ℝ) (w : WmpSpace d m p) : ℝ :=
  -∑ i : Fin d, ∑ j : Fin d, M j i *
    ∫ x, sa16y4_cmp d m p (sa16y4_tau1 d m hm j) w x * (a x * kernelConvDeriv d s i ψ x)

set_option maxHeartbeats 1600000 in
theorem sa16y5_nl_data (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {W : ℝ} (hW : 0 ≤ W)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) :
    ∃ cψ Cb : ℝ, 0 ≤ cψ ∧ 0 ≤ Cb ∧ (∀ i, Continuous (kernelConvDeriv d s i ψ)) ∧
      (∀ (f : EuclideanSpace ℝ (Fin d) → ℝ), (∀ x, |f x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) → ∀ i x,
        |f x * kernelConvDeriv d s i ψ x| ≤ (W * Cb) * (1 + ‖x‖) ^ (-((d : ℝ) + 2))) ∧
      ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ), Continuous f → (∀ x, |f x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) →
        ∀ i, MemLp (fun x => f x * kernelConvDeriv d s i ψ x) (ENNReal.conjExponent (ENNReal.ofReal p)) volume ∧
          (eLpNorm (fun x => f x * kernelConvDeriv d s i ψ x) (ENNReal.conjExponent (ENNReal.ofReal p)) volume).toReal
            ≤ cψ := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by simp)
  have hq := (sa16y3_conj_bridge (Fact.out : 2 ≤ p))
  have hq1 : 1 ≤ ENNReal.conjExponent (ENNReal.ofReal p) := by
    have := hq.2.1
    have h2 : (1 : ℝ≥0∞) ≤ ENNReal.conjExponent (ENNReal.ofReal p) := by
      rw [← ENNReal.ofReal_toReal hq.1, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal this.le
    exact h2
  have hκc : ∀ i, Continuous (kernelConvDeriv d s i ψ) := fun i =>
    HRS.MS.UniqT3.K_cont hs0 hsd (HRS.MS.UniqT3.D1_contDiff hψ2 i).continuous (HRS.MS.UniqT3.D1_supp hψ.2 i)
  choose Ck hCk using fun i : Fin d => HRS.MS.UniqT3.conv_bound hs0 hsd
    (HRS.MS.UniqT3.D1_contDiff hψ2 i).continuous (HRS.MS.UniqT3.D1_supp hψ.2 i)
  set Cb : ℝ := ∑ i, |Ck i| with hCb
  have hCb0 : 0 ≤ Cb := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hκb : ∀ i x, |kernelConvDeriv d s i ψ x| ≤ Cb * (1 + ‖x‖) := by
    intro i x
    have h1 : |kernelConvDeriv d s i ψ x| ≤ |Ck i| * (1 + ‖x‖) := by
      refine (hCk i x).trans ?_
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact Finset.single_le_sum (f := fun i => |Ck i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have hprod : ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (i : Fin d), (∀ x, |f x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) →
      ∀ x, |f x * kernelConvDeriv d s i ψ x| ≤ (W * Cb) * (1 + ‖x‖) ^ (-((d : ℝ) + 2)) := by
    intro f i hf x
    have hx1 : 0 < 1 + ‖x‖ := by positivity
    rw [abs_mul]
    calc |f x| * |kernelConvDeriv d s i ψ x| ≤ (W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) * (Cb * (1 + ‖x‖)) :=
          mul_le_mul (hf x) (hκb i x) (abs_nonneg _) (by positivity)
      _ = (W * Cb) * ((1 + ‖x‖) ^ (-((d : ℝ) + 3)) * (1 + ‖x‖)) := by ring
      _ = (W * Cb) * (1 + ‖x‖) ^ (-((d : ℝ) + 2)) := by
          congr 1
          rw [show -((d : ℝ) + 2) = -((d : ℝ) + 3) + 1 by ring, Real.rpow_add hx1, Real.rpow_one]
  have hd2 : (d : ℝ) < (d : ℝ) + 2 := by linarith
  set h0 : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (W * Cb) * (1 + ‖x‖) ^ (-((d : ℝ) + 2)) with hh0
  have hh0c : Continuous h0 := by
    refine continuous_const.mul ?_
    exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))
  have hh0b : ∀ x, |h0 x| ≤ (W * Cb) * (1 + ‖x‖) ^ (-((d : ℝ) + 2)) := fun x => by
    rw [hh0, abs_of_nonneg (by positivity)]
  have hh0m : MemLp h0 (ENNReal.conjExponent (ENNReal.ofReal p)) volume :=
    sa16y4_memLp_pow hh0c (by positivity) hd2 hh0b hq1 hq.1
  refine ⟨(eLpNorm h0 (ENNReal.conjExponent (ENNReal.ofReal p)) volume).toReal, Cb, ENNReal.toReal_nonneg, hCb0, hκc,
    fun f hf i x => hprod f i hf x, fun f hfc hf i => ⟨?_, ?_⟩⟩
  · exact sa16y4_memLp_pow (hfc.mul (hκc i)) (by positivity) hd2 (hprod f i hf) hq1 hq.1
  · refine ENNReal.toReal_mono hh0m.eLpNorm_lt_top.ne ?_
    refine eLpNorm_mono_real ((hfc.mul (hκc i)).aestronglyMeasurable) (fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hprod f i hf x

theorem sa16y5_Phi_bound {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (M : Matrix (Fin d) (Fin d) ℝ) {MB cψ : ℝ}
    (hM : ∀ i j, |M i j| ≤ MB) (hcψ : 0 ≤ cψ) {a ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hmem : ∀ i, MemLp (fun x => a x * kernelConvDeriv d s i ψ x) (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (hbd : ∀ i, (eLpNorm (fun x => a x * kernelConvDeriv d s i ψ x) (ENNReal.conjExponent (ENNReal.ofReal p))
      volume).toReal ≤ cψ)
    (hKc : ∀ i, AEStronglyMeasurable (fun x => a x * kernelConvDeriv d s i ψ x) volume) (w : WmpSpace d m p) :
    |sa16y5_Phi d m hm p s M a ψ w| ≤ ((d : ℝ) * d * MB * cψ) * ‖w‖ := by
  unfold sa16y5_Phi
  rw [abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i j : Fin d, |M j i * ∫ x, sa16y4_cmp d m p (sa16y4_tau1 d m hm j) w x *
      (a x * kernelConvDeriv d s i ψ x)| ≤ MB * (cψ * ‖w‖) := by
    intro i j
    rw [abs_mul]
    refine mul_le_mul (hM j i) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hM j i))
    refine (sa16y4_comp_Lq_bound (p := p) (sa16y4_tau1 d m hm j) w (hKc i) (hmem i)).trans ?_
    calc ‖w‖ * (eLpNorm _ _ volume).toReal ≤ ‖w‖ * cψ := mul_le_mul_of_nonneg_left (hbd i) (norm_nonneg _)
      _ = cψ * ‖w‖ := mul_comm _ _
  calc ∑ i : Fin d, |∑ j : Fin d, M j i * ∫ x, sa16y4_cmp d m p (sa16y4_tau1 d m hm j) w x *
        (a x * kernelConvDeriv d s i ψ x)|
      ≤ ∑ i : Fin d, ∑ j : Fin d, |M j i * ∫ x, sa16y4_cmp d m p (sa16y4_tau1 d m hm j) w x *
        (a x * kernelConvDeriv d s i ψ x)| := Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, MB * (cψ * ‖w‖) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = ((d : ℝ) * d * MB * cψ) * ‖w‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem sa16y5_nl_rep {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ)
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha1 : ContDiff ℝ 1 a) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    (hN : ∀ i : Fin d, MemLp (fun x => a x * kernelConvDeriv d s i ψ x)
      (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hT : ∀ φ : ccSub d, wrep d (m + 1) p (N (sa16r_Jcc d (m + 1 + 1) p φ)) =ᵐ[volume]
      HRS.MH.AdjointRd.eucNonlocal s M a φ.1) (y : WmpSpace d (m + 1 + 1) p) :
    sa16r_ell d (m + 1) p hψ (N y) = sa16y5_Phi d m hm p s M a ψ (sa16sz_iota2 d m p y) := by
  have := sa16y5_nl_ibp (p := p) hm (sa16y4_cf d s M a) 0 hs0 hsd ha1 hψ hN N hT y
  exact this

end Nf2

end HRS.Whole.AppendixA.Phase2SA16R
