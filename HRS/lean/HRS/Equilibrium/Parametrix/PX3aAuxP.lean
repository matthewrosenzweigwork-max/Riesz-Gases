import HRS.Equilibrium.Parametrix.PX3aAuxO

/-!
# Packet PX3a auxiliaries P: the kernel `ofChart N` of a chart function
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Vectors with integer coordinates. -/
def IsLat (n : Euc d) : Prop := ∀ i, ∃ k : ℤ, n i = k

lemma isLat_zero : IsLat (0 : Euc d) := fun i => ⟨0, by simp⟩

lemma mk_isLat {n : Euc d} (hn : IsLat n) : Torus.mk n = 0 := px3a_mk_int n hn

lemma cR_mk_of_small (z : Euc d) (hz : ∀ i, |z i| < 1 / 2) : Torus.centeredRep (Torus.mk z) = z := by
  ext i
  obtain ⟨n, hn⟩ := px3a_exists_int_of_mk_eq (px3a_mk_cR (Torus.mk z)) i
  have h1 := px3a_abs_cR_le (Torus.mk z) i
  have h2 : |(n : ℝ)| < 1 := by
    have : (n : ℝ) = Torus.centeredRep (Torus.mk z) i - z i := by linarith
    rw [this]
    calc |Torus.centeredRep (Torus.mk z) i - z i| ≤ |Torus.centeredRep (Torus.mk z) i| + |z i| := abs_sub _ _
      _ < 1 := by linarith [hz i]
  have h3 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast h2
    exact abs_lt.mp this |> fun h => by omega
  rw [hn, h3]; simp

lemma cR_exists_lat (w : Euc d) : ∃ n : Euc d, IsLat n ∧ Torus.centeredRep (Torus.mk w) = w - n := by
  refine ⟨w - Torus.centeredRep (Torus.mk w), fun i => ?_, by abel⟩
  obtain ⟨n, hn⟩ := px3a_exists_int_of_mk_eq (px3a_mk_cR (Torus.mk w)) i
  exact ⟨-n, by simp; linarith⟩

lemma rep_exists_lat (a : Euc d) : ∃ k : Euc d, IsLat k ∧ Torus.rep (Torus.mk a) = a + k := by
  refine ⟨Torus.rep (Torus.mk a) - a, fun i => ?_, by abel⟩
  obtain ⟨n, hn⟩ := px3a_exists_int_of_mk_eq (Torus.mk_rep (Torus.mk a)) i
  exact ⟨n, by simp; linarith⟩

lemma norm_cR_le (w n : Euc d) (hn : IsLat n) : ‖Torus.centeredRep (Torus.mk w)‖ ≤ ‖w - n‖ := by
  obtain ⟨n', hn', hc⟩ := cR_exists_lat w
  rw [hc]
  have hcoord : ∀ i, |(w - n') i| ≤ |(w - n) i| := by
    intro i
    have h1 : |(w - n') i| ≤ 1 / 2 := by
      have := px3a_abs_cR_le (Torus.mk w) i
      rwa [hc] at this
    obtain ⟨k, hk⟩ := hn i
    obtain ⟨k', hk'⟩ := hn' i
    by_cases hkk : k = k'
    · simp [hk, hk', hkk]
    · have hj : (1 : ℝ) ≤ |(k' : ℝ) - k| := by
        have : (k' - k : ℤ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hkk)
        have := Int.one_le_abs this
        exact_mod_cast this
      have e : (w - n) i = (w - n') i + ((k' : ℝ) - k) := by
        simp only [PiLp.sub_apply, hk, hk']; ring
      rw [e]
      have h2 : |((k' : ℝ) - k)| ≤ |(w - n') i + ((k' : ℝ) - k)| + |(w - n') i| := by
        calc |((k' : ℝ) - k)| = |((w - n') i + ((k' : ℝ) - k)) - (w - n') i| := by congr 1; ring
          _ ≤ _ := abs_sub _ _
      linarith
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2

lemma mk_sub_lat (x' y' n : Euc d) (hn : IsLat n) :
    Torus.mk (x' - y' - n) = Torus.mk x' - Torus.mk y' := by
  rw [mk_sub_eq, mk_isLat hn, sub_zero, mk_sub_eq]

lemma ofChart_eq {N : Euc d × Euc d → ℝ}
    (hper : ∀ (X z k : Euc d), IsLat k → N (X + k, z) = N (X, z))
    {x' y' n : Euc d} (hn : IsLat n) (hz : ∀ i, |(x' - y' - n) i| < 1 / 2)
    (hne : Torus.mk x' ≠ Torus.mk y') :
    ofChart N (Torus.mk x') (Torus.mk y') = N ((1 / 2 : ℝ) • (x' + y' - n), x' - y' - n) := by
  unfold ofChart
  rw [if_neg hne]
  have hcR : Torus.centeredRep (Torus.mk x' - Torus.mk y') = x' - y' - n := by
    rw [← mk_sub_lat x' y' n hn]; exact cR_mk_of_small _ hz
  obtain ⟨k, hk, hrep⟩ := rep_exists_lat y'
  rw [hcR, hrep]
  have : y' + k + (1 / 2 : ℝ) • (x' - y' - n) = (1 / 2 : ℝ) • (x' + y' - n) + k := by module
  rw [this]
  exact hper _ _ k hk

lemma ofChart_eq_zero {N : Euc d × Euc d → ℝ} (hsupp : ∀ X w : Euc d, 1 / 16 ≤ ‖w‖ → N (X, w) = 0)
    {x' y' : Euc d} (h : ∀ n, IsLat n → 1 / 16 ≤ ‖x' - y' - n‖) :
    ofChart N (Torus.mk x') (Torus.mk y') = 0 := by
  unfold ofChart
  by_cases hne : Torus.mk x' = Torus.mk y'
  · rw [if_pos hne]
  · rw [if_neg hne]
    obtain ⟨n', hn', hc⟩ := cR_exists_lat (x' - y')
    have : Torus.mk x' - Torus.mk y' = Torus.mk (x' - y') := (mk_sub_eq x' y').symm
    rw [this, hc]
    exact hsupp _ _ (h n' hn')

lemma norm_coord_lt_half {z : Euc d} (hz : ‖z‖ < 1 / 2) (i : Fin d) : |z i| < 1 / 2 := by
  have := PiLp.norm_apply_le z i
  rw [Real.norm_eq_abs] at this
  linarith

set_option maxHeartbeats 800000 in
lemma lift2_ofChart_contDiffAt {m : ℕ} {N : Euc d × Euc d → ℝ}
    (hsm : ContDiffOn ℝ (m : WithTop ℕ∞) N {p : Euc d × Euc d | p.2 ≠ 0})
    (hper : ∀ (X z k : Euc d), IsLat k → N (X + k, z) = N (X, z))
    (hsupp : ∀ X w : Euc d, 1 / 16 ≤ ‖w‖ → N (X, w) = 0) {p : Euc d × Euc d} (hp : p ∈ offDiag d) :
    ContDiffAt ℝ (m : WithTop ℕ∞) (lift2 (ofChart N)) p := by
  by_cases hA : ∃ n : Euc d, IsLat n ∧ ‖p.1 - p.2 - n‖ < 1 / 8
  · obtain ⟨n, hn, hlt⟩ := hA
    set Φ : Euc d × Euc d → Euc d × Euc d :=
      fun q => ((1 / 2 : ℝ) • (q.1 + q.2 - n), q.1 - q.2 - n) with hΦ
    have hΦc : ContDiff ℝ (m : WithTop ℕ∞) Φ := by
      refine ContDiff.prodMk ?_ ?_
      · exact (((contDiff_fst).add contDiff_snd).sub contDiff_const).const_smul (1 / 2 : ℝ)
      · exact (contDiff_fst.sub contDiff_snd).sub contDiff_const
    have hz0 : p.1 - p.2 - n ≠ 0 := by
      intro h0
      apply hp
      have := mk_sub_lat p.1 p.2 n hn
      rw [h0, show Torus.mk (0 : Euc d) = 0 from mk_isLat isLat_zero] at this
      exact sub_eq_zero.mp this.symm
    have hN : ContDiffAt ℝ (m : WithTop ℕ∞) N (Φ p) := hsm.contDiffAt (isOpen_ne_snd.mem_nhds hz0)
    have hev : lift2 (ofChart N) =ᶠ[𝓝 p] N ∘ Φ := by
      have h1 : IsOpen {q : Euc d × Euc d | ‖q.1 - q.2 - n‖ < 1 / 8} :=
        isOpen_lt (by fun_prop) continuous_const
      filter_upwards [px2_isOpen_offDiag.mem_nhds hp, h1.mem_nhds hlt] with q hq1 hq2
      have hq2' : ‖q.1 - q.2 - n‖ < 1 / 8 := hq2
      exact ofChart_eq hper hn (fun i => norm_coord_lt_half (by linarith) i) hq1
    exact (hN.comp p hΦc.contDiffAt).congr_of_eventuallyEq hev
  · push_neg at hA
    have hev : lift2 (ofChart N) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      have h1 : IsOpen {q : Euc d × Euc d | ‖(q.1 - q.2) - (p.1 - p.2)‖ < 1 / 16} :=
        isOpen_lt (by fun_prop) continuous_const
      filter_upwards [h1.mem_nhds (by simp)] with q hq
      have hq' : ‖(q.1 - q.2) - (p.1 - p.2)‖ < 1 / 16 := hq
      refine ofChart_eq_zero hsupp (fun n hn => ?_)
      have h8 := hA n hn
      have e : p.1 - p.2 - n = (q.1 - q.2 - n) - ((q.1 - q.2) - (p.1 - p.2)) := by abel
      have := norm_sub_le (q.1 - q.2 - n) ((q.1 - q.2) - (p.1 - p.2))
      rw [← e] at this
      linarith
    exact contDiffAt_const.congr_of_eventuallyEq hev

lemma toChart_ofChart {N : Euc d × Euc d → ℝ}
    (hper : ∀ (X z k : Euc d), IsLat k → N (X + k, z) = N (X, z)) {X z : Euc d} (hz0 : z ≠ 0)
    (hz : ‖z‖ < r0) : toChart (ofChart N) (X, z) = N (X, z) := by
  have hmem : Torus.mk (X + (1 / 2 : ℝ) • z) ≠ Torus.mk (X - (1 / 2 : ℝ) • z) := mem_Uc hz0 hz
  show ofChart N (Torus.mk (X + (1 / 2 : ℝ) • z)) (Torus.mk (X - (1 / 2 : ℝ) • z)) = _
  have e1 : (1 / 2 : ℝ) • ((X + (1 / 2 : ℝ) • z) + (X - (1 / 2 : ℝ) • z) - 0) = X := by module
  have e2 : (X + (1 / 2 : ℝ) • z) - (X - (1 / 2 : ℝ) • z) - 0 = z := by module
  have := ofChart_eq hper isLat_zero (x' := X + (1 / 2 : ℝ) • z) (y' := X - (1 / 2 : ℝ) • z)
    (fun i => by rw [e2]; exact norm_coord_lt_half (by unfold r0 at hz; linarith) i) hmem
  rw [this, e1, e2]

lemma mixedDeriv_ofChart {N : Euc d × Euc d → ℝ}
    (hper : ∀ (X z k : Euc d), IsLat k → N (X + k, z) = N (X, z)) (a c : ℕ) {X z : Euc d}
    (hz0 : z ≠ 0) (hz : ‖z‖ < r0) :
    mixedDeriv a c (toChart (ofChart N)) X z = mixedDeriv a c N X z := by
  have hU : IsOpen {z' : Euc d | z' ≠ 0 ∧ ‖z'‖ < r0} :=
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  exact mixedDeriv_congr a c X z (U := {z' : Euc d | z' ≠ 0 ∧ ‖z'‖ < r0}) (hU.mem_nhds ⟨hz0, hz⟩)
    fun X' z' hz' => toChart_ofChart hper hz'.1 hz'.2

lemma lift2_ofChart_far {N : Euc d × Euc d → ℝ}
    (hsupp : ∀ X w : Euc d, 1 / 16 ≤ ‖w‖ → N (X, w) = 0) {p : Euc d × Euc d}
    (hdist : r0 ≤ Torus.eucDist (Torus.mk p.1) (Torus.mk p.2)) :
    lift2 (ofChart N) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
  have hcR : Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) =
      ‖Torus.centeredRep (Torus.mk p.1 - Torus.mk p.2)‖ :=
    eucDist_mk_sub_eq (px3a_mk_cR _) (px3a_abs_cR_le _)
  have h1 : IsOpen {q : Euc d × Euc d | ‖(q.1 - q.2) - (p.1 - p.2)‖ < 1 / 16} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [h1.mem_nhds (by simp)] with q hq
  have hq' : ‖(q.1 - q.2) - (p.1 - p.2)‖ < 1 / 16 := hq
  refine ofChart_eq_zero hsupp (fun n hn => ?_)
  have hmk : Torus.mk p.1 - Torus.mk p.2 = Torus.mk (p.1 - p.2) := (mk_sub_eq _ _).symm
  have h8 : r0 ≤ ‖p.1 - p.2 - n‖ := by
    refine hdist.trans ?_
    rw [hcR, hmk]
    exact norm_cR_le _ _ hn
  have e : p.1 - p.2 - n = (q.1 - q.2 - n) - ((q.1 - q.2) - (p.1 - p.2)) := by abel
  have := norm_sub_le (q.1 - q.2 - n) ((q.1 - q.2) - (p.1 - p.2))
  rw [← e] at this
  unfold r0 at h8
  linarith

theorem conormalL_ofChart {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} (hB : 0 ≤ B) {N : Euc d × Euc d → ℝ}
    (hsm : ContDiffOn ℝ (m : WithTop ℕ∞) N {p : Euc d × Euc d | p.2 ≠ 0})
    (hper : ∀ (X z k : Euc d), IsLat k → N (X + k, z) = N (X, z))
    (hsupp : ∀ X w : Euc d, 1 / 16 ≤ ‖w‖ → N (X, w) = 0)
    (hnear : ∀ a c : ℕ, a + c ≤ m → ∀ X z : Euc d, z ≠ 0 → ‖z‖ < r0 →
      ‖mixedDeriv a c N X z‖ ≤ B * (1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ b c)) :
    ConormalL σ b m B (ofChart N) where
  smooth := fun p hp => (lift2_ofChart_contDiffAt hsm hper hsupp hp).contDiffWithinAt
  near := fun a c hac X z hz hzr => by
    rw [mixedDeriv_ofChart hper a c hz hzr]
    exact hnear a c hac X z hz hzr
  far := fun k hk p hp hdist => by
    rw [((lift2_ofChart_far hsupp hdist).iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_zero_fun]
    simpa using hB

end HRS.Parx

end
