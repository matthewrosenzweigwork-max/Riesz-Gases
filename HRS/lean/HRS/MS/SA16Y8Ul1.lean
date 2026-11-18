import HRS.MS.SA16Y8Rp1

/-!
# S.A.16 (SA16Y8) Ul1: uniform Cauchy sequences of functions converge uniformly (helper for the `C²` representative)
-/

noncomputable section
set_option autoImplicit false
open Filter Topology Set

namespace HRS.Whole.AppendixA.Phase2SA16Q

theorem sa16y8_unif_of_cauchy {X G : Type*} [NormedAddCommGroup G] [CompleteSpace G] (F : ℕ → X → G)
    (hC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n k : ℕ, N ≤ n → N ≤ k → ∀ x, ‖F n x - F k x‖ ≤ ε) :
    ∃ g : X → G, TendstoUniformly F g atTop ∧ ∀ x, Tendsto (fun n => F n x) atTop (nhds (g x)) := by
  have hpt : ∀ x, ∃ y, Tendsto (fun n => F n x) atTop (nhds y) := by
    intro x
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
    obtain ⟨N, hN⟩ := hC (ε / 2) (by linarith)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hN n N hn le_rfl x) (by linarith)
  choose g hg using hpt
  refine ⟨g, ?_, hg⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hC (ε / 2) (by linarith)
  filter_upwards [eventually_ge_atTop N] with n hn x
  have h1 : ‖F n x - g x‖ ≤ ε / 2 := by
    have : Tendsto (fun k => ‖F n x - F k x‖) atTop (nhds ‖F n x - g x‖) :=
      ((tendsto_const_nhds.sub (hg x)).norm)
    exact le_of_tendsto this (by
      filter_upwards [eventually_ge_atTop N] with k hk using hN n k hn hk x)
  rw [dist_comm, dist_eq_norm]
  exact lt_of_le_of_lt h1 (by linarith)

end HRS.Whole.AppendixA.Phase2SA16Q
