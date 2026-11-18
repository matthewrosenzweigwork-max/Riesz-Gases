import HRS.MS.UlocCbAux1
import HRS.Whole.AppendixALemmas

/-!
# MS-ULOC-CB: Lemma S.A.31(iii), `H^m_uloc ↪ C_b^j` for `m > j + d/2`

Statement identical to `HRS.Whole.AppendixALemmas.uloc_embedding_cb`.  Route: local embedding
`ucb_local_embedding` for each `χ(·-z) u ∈ H^m`, gluing of the continuous representatives `g_z`
(they agree on overlaps of unit balls), `v x := g_x x`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate

open HRS.Whole.AppendixA

namespace HRS.MS.UlocCb

variable {d : ℕ}

theorem uloc_embedding_cb_proof (m j : ℕ) (hmj : (j : ℝ) + (d : ℝ) / 2 < m) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, ∀ u : Euc d → ℝ, ulocNormE m χ u < ⊤ →
      ∃ v : Euc d → ℝ, v =ᵐ[volume] u ∧ MemCb j v ∧ cbNorm j v ≤ C * (ulocNormE m χ u).toReal := by
  obtain ⟨C0, hC0, hloc⟩ := ucb_local_embedding (d := d) j hmj
  refine ⟨((j : ℝ) + 1) * C0, fun u hu => ?_⟩
  set U : ℝ := (ulocNormE m χ u).toReal with hU
  have hle : ∀ z : Euc d, HRS.Whole.sobolevNormE (m : ℝ) (fun x => χ (x - z) * u x) ≤
      ulocNormE m χ u := fun z => le_iSup (fun z : Euc d =>
        HRS.Whole.sobolevNormE (m : ℝ) fun x => χ (x - z) * u x) z
  have hmem : ∀ z : Euc d, HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (fun x => χ (x - z) * u x) := by
    intro z
    by_contra h
    have h1 : HRS.Whole.sobolevNormE (m : ℝ) (fun x => χ (x - z) * u x) = ⊤ := by
      unfold HRS.Whole.sobolevNormE; rw [if_neg h]
    have := hle z
    rw [h1] at this
    exact absurd hu (not_lt.2 this)
  have hnorm : ∀ z : Euc d, Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ)
      (fun x => χ (x - z) * u x)) ≤ U := by
    intro z
    have h1 : HRS.Whole.sobolevNormE (m : ℝ) (fun x => χ (x - z) * u x) =
        ENNReal.ofReal (Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ)
          (fun x => χ (x - z) * u x))) := by
      unfold HRS.Whole.sobolevNormE; rw [if_pos (hmem z)]
    have h2 := ENNReal.toReal_mono hu.ne (hle z)
    rwa [h1, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h2
  have hex := fun z : Euc d => hloc (fun x => χ (x - z) * u x) (hmem z)
  choose g hgae hgcd hgb using hex
  -- `g z = u` a.e. on the unit ball around `z`
  have hgu : ∀ z : Euc d, ∀ᵐ x ∂(volume.restrict (Metric.ball z 1)), g z x = u x := by
    intro z
    have h1 : ∀ᵐ x ∂(volume.restrict (Metric.ball z 1)), g z x = χ (x - z) * u x :=
      ae_restrict_of_ae (hgae z)
    filter_upwards [h1, ae_restrict_mem measurableSet_ball] with x hx hxb
    have : χ (x - z) = 1 := by
      apply hχ.2.2.2.2
      rw [mem_closedBall_zero_iff]
      have : dist x z < 1 := hxb
      rw [dist_eq_norm] at this
      exact this.le
    rw [hx, this, one_mul]
  have hgg : ∀ z z' : Euc d, ∀ x ∈ Metric.ball z 1 ∩ Metric.ball z' 1, g z x = g z' x := by
    intro z z'
    have hae : g z =ᵐ[volume.restrict (Metric.ball z 1 ∩ Metric.ball z' 1)] g z' := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hgu z),
        ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hgu z')] with x h1 h2
      rw [h1, h2]
    exact Measure.eqOn_open_of_ae_eq hae (Metric.isOpen_ball.inter Metric.isOpen_ball)
      (hgcd z).continuous.continuousOn (hgcd z').continuous.continuousOn
  set v : Euc d → ℝ := fun x => g x x with hv
  have hv_eq : ∀ z : Euc d, ∀ x ∈ Metric.ball z 1, v x = g z x := fun z x hx =>
    hgg x z x ⟨Metric.mem_ball_self one_pos, hx⟩
  have hev : ∀ z : Euc d, v =ᶠ[𝓝 z] g z := fun z =>
    Filter.eventually_of_mem (Metric.ball_mem_nhds z one_pos) (hv_eq z)
  have hvcd : ContDiff ℝ j v := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (hgcd z).contDiffAt.congr_of_eventuallyEq (hev z)
  have hvb : ∀ i ≤ j, ∀ z : Euc d, ‖iteratedFDeriv ℝ i v z‖ ≤ C0 * U := by
    intro i hi z
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ (hev z) i).eq_of_nhds]
    exact (hgb z i hi z).trans (mul_le_mul_of_nonneg_left (hnorm z) hC0)
  have hvae : v =ᵐ[volume] u := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_null_of_locally_null _ fun x _ => ?_
    refine ⟨{a | ¬ v a = u a} ∩ Metric.ball x 1, inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x one_pos)), ?_⟩
    have h1 := (ae_restrict_iff' measurableSet_ball).1 (hgu x)
    rw [ae_iff] at h1
    refine measure_mono_null (fun a ha => ?_) h1
    intro hh
    exact ha.1 ((hv_eq x a ha.2).trans (hh ha.2))
  refine ⟨v, hvae, ⟨hvcd, fun i hi => ⟨C0 * U, ?_⟩⟩, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact hvb i hi z
  · unfold cbNorm
    calc ∑ i ∈ Finset.range (j + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ i v z‖
        ≤ ∑ i ∈ Finset.range (j + 1), C0 * U := by
          refine Finset.sum_le_sum fun i hi => ciSup_le fun z => ?_
          exact hvb i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) z
      _ = ((j : ℝ) + 1) * C0 * U := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring

end HRS.MS.UlocCb

example := (@HRS.MS.UlocCb.uloc_embedding_cb_proof :
  type_of% @HRS.Whole.AppendixALemmas.uloc_embedding_cb)
