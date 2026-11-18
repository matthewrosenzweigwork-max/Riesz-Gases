import HRS.MS.UlocCb
import HRS.MS.SA12LimitL16
import HRS.MS.SA12LimitL12
import HRS.MS.SA12CompB2

/-!
# S.A.12 B3: a jointly continuous `C²` representative of a solution at order `m_*`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Limit

variable {d : ℕ}

theorem sa12y_single_le_cb {k : ℕ} {f : Euc d → ℝ} (hf : MemCb k f) {j : ℕ} (hj : j ≤ k)
    (x : Euc d) : ‖iteratedFDeriv ℝ j f x‖ ≤ cbNorm k f := by
  unfold cbNorm
  refine le_trans ?_ (Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  exact le_ciSup (hf.2 j hj) x

-- BEGIN SA12.B3
theorem continuous_c2_representative (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ Cemb : ℝ, 0<Cemb ∧ ∀ (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ)
      (F : ℝ → Euc d → ℝ), 0<t → IsUlocSolutionRd χ (mStar d) C t φ F →
      ∃ F' : ℝ → Euc d → ℝ,
        (∀ τ ∈ Icc (0 : ℝ) t, F' τ =ᵐ[volume] F τ) ∧
        (∀ τ ∈ Icc (0 : ℝ) t, MemCb 2 (F' τ) ∧
          cbNorm 2 (F' τ) ≤ Cemb*(ulocNormE (mStar d) χ (F τ)).toReal) ∧
        (∃ B : ℝ, ∀ j ≤ 2, ∀ τ ∈ Icc (0 : ℝ) t, ∀ x,
          ‖iteratedFDeriv ℝ j (F' τ) x‖ ≤ B) ∧
        ∀ j ≤ 2, ContinuousOn
          (fun q : ℝ × Euc d => iteratedFDeriv ℝ j (F' q.1) q.2)
          (Icc (0 : ℝ) t ×ˢ univ) := by
  have h1 : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by
    have : d ≤ 2 * (d / 2) + 1 := by omega
    exact_mod_cast this
  have hq : ((2 : ℕ) : ℝ) + d / 2 < (mStar d : ℝ) := by
    unfold mStar; push_cast; linarith
  have hq' : ((2 : ℕ) : ℝ) + d / 2 < (mStar d : ℝ) - 1 / 4 := by
    unfold mStar; push_cast; linarith
  obtain ⟨C0, hC0⟩ := HRS.MS.UlocCb.uloc_embedding_cb_proof (d := d) (mStar d) 2 hq χ hχ
  obtain ⟨C1, hC1, hE⟩ := HRS.MS.UlocCb.ucb_local_embedding (d := d) 2 hq'
  refine ⟨max C0 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro C t φ F ht hF
  obtain ⟨B, hB⟩ := hF.bounded
  have hex : ∀ τ : ℝ, ∃ v : Euc d → ℝ, τ ∈ Icc (0 : ℝ) t →
      (v =ᵐ[volume] F τ ∧ MemCb 2 v ∧ cbNorm 2 v ≤ C0 * (ulocNormE (mStar d) χ (F τ)).toReal) := by
    intro τ
    by_cases hτ : τ ∈ Icc (0 : ℝ) t
    · obtain ⟨v, hv1, hv2, hv3⟩ := hC0 (F τ) ((hB τ hτ).trans_lt ENNReal.ofReal_lt_top)
      exact ⟨v, fun _ => ⟨hv1, hv2, hv3⟩⟩
    · exact ⟨F τ, fun h => absurd h hτ⟩
  choose F' hF' using hex
  have hnn : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ (ulocNormE (mStar d) χ (F τ)).toReal := fun _ _ =>
    ENNReal.toReal_nonneg
  have hcb : ∀ τ ∈ Icc (0 : ℝ) t, MemCb 2 (F' τ) ∧
      cbNorm 2 (F' τ) ≤ max C0 1 * (ulocNormE (mStar d) χ (F τ)).toReal := fun τ hτ =>
    ⟨(hF' τ hτ).2.1, (hF' τ hτ).2.2.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn τ hτ))⟩
  refine ⟨F', fun τ hτ => (hF' τ hτ).1, hcb, ?_, ?_⟩
  · refine ⟨max C0 1 * max B 0, fun j hj τ hτ x => ?_⟩
    have h1 := sa12y_single_le_cb (hcb τ hτ).1 hj x
    refine h1.trans ((hcb τ hτ).2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity)))
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hB τ hτ)
    rwa [ENNReal.toReal_ofReal'] at this
  · intro j hj
    intro q0 hq0
    obtain ⟨τ0, x0⟩ := q0
    have hτ0 : τ0 ∈ Icc (0 : ℝ) t := hq0.1
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hε1 : 0 < ε / (2 * (C1 + 1)) := by positivity
    obtain ⟨δ1, hδ1, hδ1'⟩ := hF.cont ((mStar d : ℝ) - 1 / 4) (by linarith) x0 τ0 hτ0 _ hε1
    have hcont0 : Continuous (iteratedFDeriv ℝ j (F' τ0)) :=
      (hcb τ0 hτ0).1.1.continuous_iteratedFDeriv (by exact_mod_cast hj)
    obtain ⟨δ2, hδ2, hδ2'⟩ := Metric.continuous_iff.1 hcont0 x0 (ε / 2) (by positivity)
    refine ⟨min δ1 (min δ2 1), by positivity, ?_⟩
    rintro ⟨τ, x⟩ hτx hdist
    have hτ : τ ∈ Icc (0 : ℝ) t := hτx.1
    have hd1 : |τ - τ0| < δ1 := by
      have h2 : dist τ τ0 < min δ1 (min δ2 1) := lt_of_le_of_lt (le_max_left _ _) (by simpa [Prod.dist_eq] using hdist)
      rw [Real.dist_eq] at h2
      exact lt_of_lt_of_le h2 (min_le_left _ _)
    have hd2 : dist x x0 < min δ2 1 := by
      have h2 : dist x x0 < min δ1 (min δ2 1) :=
        lt_of_le_of_lt (le_max_right _ _) (by simpa [Prod.dist_eq] using hdist)
      exact lt_of_lt_of_le h2 (min_le_right _ _)
    have hxball : x ∈ Metric.ball x0 1 := by
      rw [Metric.mem_ball]; exact lt_of_lt_of_le hd2 (min_le_right _ _)
    -- the local difference estimate
    have hsob := hδ1' τ hτ hd1
    obtain ⟨hmem, hS⟩ := sa12x_sobE_le hε1.le hsob
    obtain ⟨g, hge, hg2, hgb⟩ := hE _ hmem
    have hlocae : (fun y => F' τ y - F' τ0 y) =ᵐ[volume.restrict (Metric.ball x0 1)] g := by
      have h1 : (fun y => F' τ y - F' τ0 y) =ᵐ[volume] fun y => F τ y - F τ0 y := by
        filter_upwards [(hF' τ hτ).1, (hF' τ0 hτ0).1] with y a b
        rw [a, b]
      have h2 : g =ᵐ[volume.restrict (Metric.ball x0 1)]
          fun y => χ (y - x0) * (F τ y - F τ0 y) := ae_restrict_of_ae hge
      have h3 : ∀ y ∈ Metric.ball x0 1, χ (y - x0) * (F τ y - F τ0 y) = F τ y - F τ0 y := by
        intro y hy
        have hy1 : y - x0 ∈ Metric.closedBall (0 : Euc d) 1 := by
          rw [mem_closedBall_zero_iff, ← dist_eq_norm]
          exact (Metric.mem_ball.1 hy).le
        rw [hχ.2.2.2.2 _ hy1, one_mul]
      have h4 : (fun y => F τ y - F τ0 y) =ᵐ[volume.restrict (Metric.ball x0 1)]
          fun y => χ (y - x0) * (F τ y - F τ0 y) := by
        filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        exact (h3 y hy).symm
      have h1' : (fun y => F' τ y - F' τ0 y) =ᵐ[volume.restrict (Metric.ball x0 1)]
          fun y => F τ y - F τ0 y := ae_restrict_of_ae h1
      exact Filter.EventuallyEq.trans h1' (Filter.EventuallyEq.trans h4 h2.symm)
    have hcF : ContinuousOn (fun y => F' τ y - F' τ0 y) (Metric.ball x0 1) :=
      ((hcb τ hτ).1.1.continuous.sub (hcb τ0 hτ0).1.1.continuous).continuousOn
    have heq := Measure.eqOn_open_of_ae_eq hlocae Metric.isOpen_ball hcF hg2.continuous.continuousOn
    have hev : (fun y => F' τ y - F' τ0 y) =ᶠ[𝓝 x] g :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hxball) heq
    have hjd := (Filter.EventuallyEq.iteratedFDeriv ℝ hev j).self_of_nhds
    have hsubj : iteratedFDeriv ℝ j (fun y => F' τ y - F' τ0 y) x =
        iteratedFDeriv ℝ j (F' τ) x - iteratedFDeriv ℝ j (F' τ0) x :=
      iteratedFDeriv_sub_apply ((hcb τ hτ).1.1.contDiffAt.of_le (by exact_mod_cast hj))
        ((hcb τ0 hτ0).1.1.contDiffAt.of_le (by exact_mod_cast hj))
    have hgj : ‖iteratedFDeriv ℝ j g x‖ ≤ C1 * (ε / (2 * (C1 + 1))) := by
      refine (hgb j hj x).trans (mul_le_mul_of_nonneg_left ?_ hC1)
      calc Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq ((mStar d : ℝ) - 1 / 4)
            (fun x_1 => χ (x_1 - x0) * (F τ x_1 - F τ0 x_1))) ≤ Real.sqrt ((ε / (2 * (C1 + 1))) ^ 2) :=
            Real.sqrt_le_sqrt hS
        _ = _ := Real.sqrt_sq hε1.le
    have hdiff : ‖iteratedFDeriv ℝ j (F' τ) x - iteratedFDeriv ℝ j (F' τ0) x‖ ≤
        C1 * (ε / (2 * (C1 + 1))) := by
      rw [← hsubj, hjd]; exact hgj
    have hxc := hδ2' x (lt_of_lt_of_le hd2 (min_le_left _ _))
    rw [dist_eq_norm] at hxc ⊢
    calc ‖iteratedFDeriv ℝ j (F' τ) x - iteratedFDeriv ℝ j (F' τ0) x0‖
        = ‖(iteratedFDeriv ℝ j (F' τ) x - iteratedFDeriv ℝ j (F' τ0) x) +
            (iteratedFDeriv ℝ j (F' τ0) x - iteratedFDeriv ℝ j (F' τ0) x0)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ < ε := by
          have h5 : C1 * (ε / (2 * (C1 + 1))) ≤ ε / 2 := by
            rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [hε, hC1]
          linarith [hdiff, hxc]
-- END SA12.B3

end HRS.MH.AdjointRd.Phase2SA12Companions
