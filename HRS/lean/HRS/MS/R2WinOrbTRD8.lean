import HRS.MS.R2WinOrbTRD7

/-!
# S10.3 packet [D], part 2: completeness of `C^k_b` (uniform Cauchy sequences in all jets up to order `k` have a `C^k` limit)

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

variable {d : ℕ}

theorem s103c_iter_sub {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : Euc d → F} {j : ℕ}
    (ha : ContDiff ℝ (j : WithTop ℕ∞) a) (hb : ContDiff ℝ (j : WithTop ℕ∞) b) (x : Euc d) :
    iteratedFDeriv ℝ j a x - iteratedFDeriv ℝ j b x = iteratedFDeriv ℝ j (fun y => a y - b y) x := by
  have e : (fun y => a y - b y) = a - b := rfl
  rw [e, iteratedFDeriv_sub_apply ha.contDiffAt hb.contDiffAt]

theorem s103c_ck_limit0 {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℕ → Euc d → F) (hg : ∀ n, Continuous (g n))
    (hC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ x, ‖g n x - g m x‖ ≤ ε) :
    ∃ u : Euc d → F, Continuous u ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, ‖g n x - u x‖ ≤ ε := by
  have hcau : ∀ x, CauchySeq (fun n => g n x) := by
    intro x
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hC (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn N le_rfl x
    rw [dist_eq_norm]
    linarith
  choose u hu using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hbound : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, ‖g n x - u x‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn x => ?_⟩
    have hlim : Tendsto (fun m => ‖g n x - g m x‖) atTop (𝓝 ‖g n x - u x‖) :=
      (tendsto_const_nhds.sub (hu x)).norm
    exact le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨N, fun m hm => hN n hn m hm x⟩)
  have hunif : TendstoUniformly g u atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hbound (ε / 2) (by positivity)
    refine Filter.eventually_atTop.2 ⟨N, fun n hn x => ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact (hN n hn x).trans_lt (by linarith)
  exact ⟨u, hunif.continuous (Filter.Eventually.of_forall hg).frequently, hbound⟩

theorem s103c_ck_limit : ∀ (k : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℕ → Euc d → F), (∀ n, ContDiff ℝ (k : WithTop ℕ∞) (g n)) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (g n) x - iteratedFDeriv ℝ j (g m) x‖ ≤ ε) →
    ∃ u : Euc d → F, ContDiff ℝ (k : WithTop ℕ∞) u ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (g n) x - iteratedFDeriv ℝ j u x‖ ≤ ε := by
  intro k
  induction k with
  | zero =>
    intro F _ _ _ g hg hC
    obtain ⟨u, hu, hb⟩ := s103c_ck_limit0 g (fun n => (hg n).continuous) (fun ε hε => by
      obtain ⟨N, hN⟩ := hC ε hε
      refine ⟨N, fun n hn m hm x => ?_⟩
      have := hN n hn m hm 0 le_rfl x
      rw [s103c_iter_sub (hg n) (hg m)] at this
      simpa [norm_iteratedFDeriv_zero] using this)
    have hu0 : ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞) u := contDiff_zero.2 hu
    refine ⟨u, hu0, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := hb ε hε
    refine ⟨N, fun n hn j hj x => ?_⟩
    have hj0 : j = 0 := by omega
    subst hj0
    rw [s103c_iter_sub (hg n) hu0]
    simpa [norm_iteratedFDeriv_zero] using hN n hn x
  | succ k ih =>
    intro F _ _ _ g hg hC
    have hg1 : ∀ n, ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ (g n)) := fun n =>
      (hg n).fderiv_right (by exact_mod_cast le_refl (k + 1))
    have hrel : ∀ (a b : Euc d → F), ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) a →
        ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) b →
        ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fderiv ℝ a) x - iteratedFDeriv ℝ j (fderiv ℝ b) x‖ =
          ‖iteratedFDeriv ℝ (j + 1) a x - iteratedFDeriv ℝ (j + 1) b x‖ := by
      intro a b ha hb j hj x
      have hda : Differentiable ℝ a := ha.differentiable (by exact_mod_cast Nat.succ_ne_zero k)
      have hdb : Differentiable ℝ b := hb.differentiable (by exact_mod_cast Nat.succ_ne_zero k)
      have e1 : fderiv ℝ (fun y => a y - b y) = fun y => fderiv ℝ a y - fderiv ℝ b y := by
        funext y; exact fderiv_sub (hda y) (hdb y)
      have hca : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ a) :=
        ha.fderiv_right (by exact_mod_cast le_refl (k + 1))
      have hcb : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ b) :=
        hb.fderiv_right (by exact_mod_cast le_refl (k + 1))
      have hjk : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hj
      have hjk1 : ((j + 1 : ℕ) : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast Nat.succ_le_succ hj
      rw [s103c_iter_sub (hca.of_le hjk) (hcb.of_le hjk), ← e1, norm_iteratedFDeriv_fderiv,
        ← s103c_iter_sub (ha.of_le hjk1) (hb.of_le hjk1)]
    have hCG : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ j ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ j (fderiv ℝ (g n)) x - iteratedFDeriv ℝ j (fderiv ℝ (g m)) x‖ ≤ ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hC ε hε
      refine ⟨N, fun n hn m hm j hj x => ?_⟩
      rw [hrel (g n) (g m) (hg n) (hg m) j hj x]
      exact hN n hn m hm (j + 1) (Nat.succ_le_succ hj) x
    obtain ⟨U, hUk, hUc⟩ := ih (fun n => fderiv ℝ (g n)) hg1 hCG
    obtain ⟨u₀, hu₀c, hu₀b⟩ := s103c_ck_limit0 g (fun n => (hg n).continuous) (fun ε hε => by
      obtain ⟨N, hN⟩ := hC ε hε
      refine ⟨N, fun n hn m hm x => ?_⟩
      have := hN n hn m hm 0 (Nat.zero_le _) x
      rw [s103c_iter_sub ((hg n).of_le (by exact_mod_cast Nat.zero_le _)) ((hg m).of_le (by exact_mod_cast Nat.zero_le _))] at this
      simpa [norm_iteratedFDeriv_zero] using this)
    have hUb : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, ‖fderiv ℝ (g n) x - U x‖ ≤ ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hUc ε hε
      refine ⟨N, fun n hn x => ?_⟩
      have := hN n hn 0 (Nat.zero_le _) x
      rw [s103c_iter_sub (hg1 n |>.of_le (by exact_mod_cast Nat.zero_le _)) (hUk.of_le (by exact_mod_cast Nat.zero_le _))] at this
      simpa [norm_iteratedFDeriv_zero] using this
    have hUunif : TendstoUniformly (fun n => fderiv ℝ (g n)) U atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hUb (ε / 2) (by positivity)
      refine Filter.eventually_atTop.2 ⟨N, fun n hn x => ?_⟩
      rw [dist_comm, dist_eq_norm]
      exact (hN n hn x).trans_lt (by linarith)
    have hpt : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (u₀ x)) := by
      intro x
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
      · exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha (norm_nonneg _)
      · obtain ⟨N, hN⟩ := hu₀b (a / 2) (by linarith)
        exact Filter.eventually_atTop.2 ⟨N, fun n hn => (hN n hn x).trans_lt (by linarith)⟩
    have hderiv : ∀ x, HasFDerivAt u₀ (U x) x := fun x =>
      hasFDerivAt_of_tendstoUniformly hUunif
        (fun n x => ((hg n).differentiable (by exact_mod_cast Nat.succ_ne_zero k) x).hasFDerivAt) hpt x
    have hfd : fderiv ℝ u₀ = U := funext fun x => (hderiv x).fderiv
    have hu₀ : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u₀ := by
      rw [show (((k + 1 : ℕ)) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hderiv x).differentiableAt, by simp, ?_⟩
      rw [hfd]; exact hUk
    refine ⟨u₀, hu₀, fun ε hε => ?_⟩
    obtain ⟨N0, hN0⟩ := hu₀b ε hε
    obtain ⟨N1, hN1⟩ := hUc ε hε
    refine ⟨max N0 N1, fun n hn j hj x => ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hjp
    · rw [s103c_iter_sub ((hg n).of_le (by exact_mod_cast Nat.zero_le _)) (hu₀.of_le (by exact_mod_cast Nat.zero_le _))]
      simpa [norm_iteratedFDeriv_zero] using hN0 n (le_trans (le_max_left _ _) hn) x
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [← hrel (g n) u₀ (hg n) hu₀ j' (by omega) x, hfd]
      exact hN1 n (le_trans (le_max_right _ _) hn) j' (by omega) x

end HRS.MS.R2WinOrbNL

end
