import HRS.MS.R26T8AP06d9
import HRS.MS.R26T8AP06d10

/-!
# S8.2 local Newton layer, packet T8A.P06d (part 11): continuous extension of the JOINT jets of `midPair F`
`r26t8a_joint_ext`: under `Conormal (k+1) b M sigma A F`, `k < -sigma`, `j <= k`, the joint jet `D^j (midPair F)` (`z != 0`) has a continuous
extension to `E x E`.  Uniform Cauchy rate from `r26t8a_nest_cauchy` + `r26t8a_joint_diff_le` (per-pair cutoff `psiCut`), then `r26t8a_cauchy_ext`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_joint_ext (hd : 2 ≤ d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ : ℝ) (hM : 0 ≤ M)
    (hk : (k : ℝ) < -σ) {A : ℝ} (hA : 0 ≤ A) {F : Euc d → Euc d → ℝ} (hF : Conormal (k + 1) b M σ A F)
    (j : ℕ) (hj : j ≤ k) :
    ∃ g : Euc d × Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d × Euc d) ℝ,
      Continuous g ∧ ∀ w : Euc d × Euc d, w.2 ≠ 0 →
        g w = iteratedFDeriv ℝ j (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) w := by
  have hF1 := hF.1
  have hC : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (q ≤ j → ∀ X z z' : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 → 0 < ‖z'‖ → ‖z'‖ ≤ 1 / 2 →
      ‖r26t8a_nest (j - q) q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) X z -
        r26t8a_nest (j - q) q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) X z'‖ ≤
      C * A * (3 ^ (2 * M) * jbracket X ^ (2 * M)) *
        (‖z‖ ^ (min (-σ - (((k - (j - q) : ℕ)) : ℝ)) 1 / 2) + ‖z'‖ ^ (min (-σ - (((k - (j - q) : ℕ)) : ℝ)) 1 / 2))) := by
    intro q
    by_cases hq : q ≤ j
    · obtain ⟨C, hC0, hC⟩ := r26t8a_nest_cauchy hd hchi k b M σ hM hk (j - q) q (by omega)
      exact ⟨C, hC0, fun _ => hC A hA F hF⟩
    · exact ⟨0, le_rfl, fun h => absurd h hq⟩
  choose Cq hCq0 hCq using hC
  obtain ⟨W, hW⟩ : ∃ W : Euc d → ℝ, W = fun X => 3 ^ (2 * M) * jbracket X ^ (2 * M) := ⟨_, rfl⟩
  have hW0 : ∀ X, 0 ≤ W X := fun X => by
    rw [hW]; exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (s83_jb_pos X).le _)
  set C' : ℝ := ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) * Cq q with hC'
  have hC'0 : 0 ≤ C' := Finset.sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _) (hCq0 q)
  set ε : ℝ := min (-σ - (k : ℝ)) 1 / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]; have := lt_min (by linarith : 0 < -σ - (k : ℝ)) one_pos; linarith
  obtain ⟨K, hK⟩ : ∃ K : Euc d → ℝ, K = fun X => C' * A * W X := ⟨_, rfl⟩
  have hK0 : ∀ X, 0 ≤ K X := fun X => by rw [hK]; exact mul_nonneg (mul_nonneg hC'0 hA) (hW0 X)
  have hKc : Continuous K := by
    rw [hK, hW]
    refine continuous_const.mul ?_
    exact continuous_const.mul ((r26t8a_jbracket_continuous (d := d)).rpow_const (fun x => Or.inr (by positivity)))
  -- cutoff data attached to a radius
  have hcut : ∀ R : ℝ, 0 < R → ContDiff ℝ (j : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) := fun R hR =>
    (r26t8a_gtilde_contDiff hchi hR hF1).of_le (by exact_mod_cast (by omega : j ≤ k + 1))
  have hgerm : ∀ (R : ℝ) (hR : 0 < R) (X z : Euc d), R / 4 < ‖z‖ →
      iteratedFDeriv ℝ j (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) (X, z) =
        iteratedFDeriv ℝ j (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (X, z) := by
    intro R hR X z hz
    have hopen : IsOpen {w : Euc d × Euc d | R / 4 < ‖w.2‖} := isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
    have hev : (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) =ᶠ[𝓝 (X, z)]
        (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) := by
      filter_upwards [hopen.mem_nhds (show R / 4 < ‖(X, z).2‖ from hz)] with w hw
      simp only [r26t8a_psiCut_one hchi hR (le_of_lt hw), one_mul]
    exact (hev.iteratedFDeriv ℝ j).self_of_nhds
  have hCauchy : ∀ X z z' : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 → 0 < ‖z'‖ → ‖z'‖ ≤ 1 / 2 →
      ‖iteratedFDeriv ℝ j (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (X, z) -
        iteratedFDeriv ℝ j (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (X, z')‖ ≤
        K X * (‖z‖ ^ ε + ‖z'‖ ^ ε) := by
    intro X z z' hz hz1 hz' hz1'
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * min ‖z‖ ‖z'‖ := ⟨_, rfl⟩
    have hm : 0 < min ‖z‖ ‖z'‖ := lt_min hz hz'
    have hR : 0 < R := by rw [hRdef]; positivity
    have hl1 : R / 4 < ‖z‖ := by
      rw [hRdef]; have := min_le_left ‖z‖ ‖z'‖; linarith
    have hl2 : R / 4 < ‖z'‖ := by
      rw [hRdef]; have := min_le_right ‖z‖ ‖z'‖; linarith
    rw [← hgerm R hR X z hl1, ← hgerm R hR X z' hl2]
    refine (r26t8a_joint_diff_le j (hcut R hR) X z z').trans ?_
    have hterm : ∀ q ∈ Finset.range (j + 1), (j.choose q : ℝ) *
        ‖r26t8a_nest (j - q) q (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) X z -
          r26t8a_nest (j - q) q (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) X z'‖ ≤
        (j.choose q : ℝ) * (Cq q * A * W X * (‖z‖ ^ ε + ‖z'‖ ^ ε)) := by
      intro q hq
      have hq' : q ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have hn1 : r26t8a_nest (j - q) q (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) X z =
          r26t8a_nest (j - q) q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) X z :=
        (r26t8a_nest_gtilde hchi hR (F := F) (j - q) q X z hl1).trans rfl
      have hn2 : r26t8a_nest (j - q) q (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) X z' =
          r26t8a_nest (j - q) q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) X z' :=
        (r26t8a_nest_gtilde hchi hR (F := F) (j - q) q X z' hl2).trans rfl
      rw [hn1, hn2]
      refine (hCq q hq' X z z' hz hz1 hz' hz1').trans ?_
      have hεq : ε ≤ min (-σ - (((k - (j - q) : ℕ)) : ℝ)) 1 / 2 := by
        rw [hεdef]
        have : (((k - (j - q) : ℕ)) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k (j - q)
        have := min_le_min (show -σ - (k : ℝ) ≤ -σ - (((k - (j - q) : ℕ)) : ℝ) by linarith) (le_refl (1 : ℝ))
        linarith
      have a1 : ‖z‖ ^ (min (-σ - (((k - (j - q) : ℕ)) : ℝ)) 1 / 2) ≤ ‖z‖ ^ ε :=
        Real.rpow_le_rpow_of_exponent_ge hz (by linarith) hεq
      have a2 : ‖z'‖ ^ (min (-σ - (((k - (j - q) : ℕ)) : ℝ)) 1 / 2) ≤ ‖z'‖ ^ ε :=
        Real.rpow_le_rpow_of_exponent_ge hz' (by linarith) hεq
      have hnn : 0 ≤ Cq q * A * (3 ^ (2 * M) * jbracket X ^ (2 * M)) :=
        mul_nonneg (mul_nonneg (hCq0 q) hA)
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (s83_jb_pos X).le _))
      have hWX : W X = 3 ^ (2 * M) * jbracket X ^ (2 * M) := by rw [hW]
      rw [hWX]
      exact mul_le_mul_of_nonneg_left (add_le_add a1 a2) hnn
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [hK, hC']
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hcont : ContinuousOn (fun w : Euc d × Euc d => iteratedFDeriv ℝ j (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) w)
      {w | w.2 ≠ 0} := by
    intro w0 hw0
    have hn : 0 < ‖w0.2‖ := norm_pos_iff.2 hw0
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * ‖w0.2‖ := ⟨_, rfl⟩
    have hR : 0 < R := by rw [hRdef]; positivity
    have hopen : IsOpen {w : Euc d × Euc d | R / 4 < ‖w.2‖} := isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
    have hc := ((hcut R hR).continuous_iteratedFDeriv le_rfl).continuousAt (x := w0)
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [hopen.mem_nhds (show R / 4 < ‖w0.2‖ by rw [hRdef]; linarith)] with w hw
    exact hgerm R hR w.1 w.2 hw
  have hKloc : ∀ X0 : Euc d, ∃ r K0 : ℝ, 0 < r ∧ ∀ X ∈ Metric.ball X0 r, K X ≤ K0 := fun X0 => by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hKc.continuousAt 1 one_pos
    refine ⟨δ, K X0 + 1, hδ, fun X hX => ?_⟩
    have := hδ' (by simpa using hX : dist X X0 < δ)
    rw [Real.dist_eq] at this
    linarith [(abs_lt.1 this).2]
  haveI : CompleteSpace (ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d × Euc d) ℝ) :=
    ContinuousMultilinearMap.instCompleteSpace
  exact r26t8a_cauchy_ext (by omega) (fun X z => iteratedFDeriv ℝ j (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (X, z))
    K hK0 hε hCauchy hcont hKloc

end HRS.MS.R26T8A
