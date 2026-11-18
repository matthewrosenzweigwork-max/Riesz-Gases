import HRS.MS.SA16Y4Nc5

/-!
# S.A.16 (SA16Y4) Nc6: limit of the nonlocal pairing along pointwise convergent coefficients (see Nc5 header)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Nc6
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the coefficient bundle with `ρ ≡ a` -/
def sa16y4_cf (d : ℕ) (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (a : EuclideanSpace ℝ (Fin d) → ℝ) : WholeCoeff d :=
  ⟨s, M, 0, fun _ _ => 0, fun _ => a⟩

set_option maxHeartbeats 1600000 in
theorem sa16y4_nl_tendsto {m : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) {W Bm : ℝ} (hW : 0 ≤ W)
    (a : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (μ : EuclideanSpace ℝ (Fin d) → ℝ)
    (ha1 : ∀ j, ContDiff ℝ 1 (a j)) (hμ1 : ContDiff ℝ 1 μ)
    (haW : ∀ j x, |a j x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) (hμW : ∀ x, |μ x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3)))
    (hpt : ∀ x, Tendsto (fun j => a j x) atTop (𝓝 (μ x)))
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    (T0 : ℕ → WmpSpace d m p →L[ℝ] WmpSpace d m p) (hT0 : ∀ j, SA16SubOp d m p s M (a j) (T0 j))
    (Tμ : WmpSpace d m p →L[ℝ] WmpSpace d m p) (hTμ : SA16SubOp d m p s M μ Tμ)
    (gs : ℕ → WmpSpace d m p) (G : WmpSpace d m p) (hbd : ∀ j, ‖gs j‖ ≤ Bm)
    (hw : ∀ ℓ : StrongDual ℝ (WmpSpace d m p), Tendsto (fun j => ℓ (gs j)) atTop (𝓝 (ℓ G))) :
    Tendsto (fun j => sa16r_ell d m p hψ (T0 j (gs j))) atTop (𝓝 (sa16r_ell d m p hψ (Tμ G))) := by
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
  have hmem : ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ), Continuous f → (∀ x, |f x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) →
      ∀ i, MemLp (fun x => f x * kernelConvDeriv d s i ψ x) (ENNReal.conjExponent (ENNReal.ofReal p)) volume :=
    fun f hc hf i => sa16y4_memLp_pow (hc.mul (hκc i)) (by positivity) hd2 (hprod f i hf) hq1 hq.1
  have hrep : ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf1 : ContDiff ℝ 1 f)
      (hfW : ∀ x, |f x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) (T : WmpSpace d m p →L[ℝ] WmpSpace d m p)
      (hT : SA16SubOp d m p s M f T) (y : WmpSpace d m p),
      sa16r_ell d m p hψ (T y) = -∑ i : Fin d, ∑ k : Fin d, M k i *
        ∫ x, sa16y4_cmp d m p (sa16y4_tau1 d m hm k) y x * (f x * kernelConvDeriv d s i ψ x) := by
    intro f hf1 hfW T hT y
    exact sa16y4_nl_ibp (p := p) hm (sa16y4_cf d s M f) 0 hs0 hsd hf1 hψ (hmem f hf1.continuous hfW) T hT y
  refine Tendsto.congr (fun j => (hrep (a j) (ha1 j) (haW j) (T0 j) (hT0 j) (gs j)).symm) ?_
  rw [hrep μ hμ1 hμW Tμ hTμ G]
  refine (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun k _ => ?_).neg
  refine (sa16y4_comp_tendsto_Lq (p := p) (sa16y4_tau1 d m hm k) gs G hbd hw (fun j x => a j x * kernelConvDeriv d s i ψ x)
    (fun x => μ x * kernelConvDeriv d s i ψ x) (fun j => ((ha1 j).continuous.mul (hκc i)).aestronglyMeasurable)
    (hμ1.continuous.mul (hκc i)).aestronglyMeasurable (fun j => hmem (a j) (ha1 j).continuous (haW j) i)
    (hmem μ hμ1.continuous hμW i) ?_).const_mul (M k i)
  refine sa16y4_Lq_dominated hq.1 hq.2.1.le hd2 (fun j x => a j x * kernelConvDeriv d s i ψ x)
    (fun x => μ x * kernelConvDeriv d s i ψ x) (fun j => (ha1 j).continuous.mul (hκc i))
    (hμ1.continuous.mul (hκc i)) (fun j x => hprod (a j) i (haW j) x) (hprod μ i hμW)
    (fun x => (hpt x).mul_const _)

end Nc6

end HRS.Whole.AppendixA.Phase2SA16R
