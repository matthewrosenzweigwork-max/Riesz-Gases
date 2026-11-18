import HRS.MS.R26T8AP00

/-!
# S8.2 local Newton layer, packet T8A.P06d (part 2): uniqueness of continuous extensions off the diagonal
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Set

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_offdiag_dense (hd : 1 ≤ d) : Dense {p : Euc d × Euc d | p.1 ≠ p.2} := by
  obtain ⟨e, he⟩ : ∃ e : Euc d, ‖e‖ = 1 := ⟨EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by simp⟩
  have he0 : e ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; norm_num)
  intro p
  by_cases hp : p.1 ≠ p.2
  · exact subset_closure hp
  · push Not at hp
    have hlim : Tendsto (fun t : ℝ => (p.1, p.2 + t • e)) (𝓝[>] 0) (𝓝 p) := by
      have : Tendsto (fun t : ℝ => (p.1, p.2 + t • e)) (𝓝 0) (𝓝 (p.1, p.2 + (0 : ℝ) • e)) :=
        (continuous_const.prodMk (continuous_const.add (continuous_id.smul continuous_const))).tendsto 0
      simp only [zero_smul, add_zero, Prod.mk.eta] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    show p.1 ≠ p.2 + t • e
    intro h
    have : t • e = 0 := by
      have h2 : p.2 + t • e = p.2 := by rw [← h, hp]
      simpa using h2
    rcases smul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (ne_of_gt ht)
    · exact he0 h0

theorem r26t8a_unique_ext (hd : 1 ≤ d) {F Fext G : Euc d → Euc d → ℝ} (hFe : Continuous (Function.uncurry Fext))
    (hG : Continuous (Function.uncurry G)) (h1 : ∀ x y, x ≠ y → Fext x y = F x y)
    (h2 : ∀ x y, x ≠ y → G x y = F x y) : G = Fext := by
  have : Function.uncurry G = Function.uncurry Fext :=
    Continuous.ext_on (r26t8a_offdiag_dense hd) hG hFe (fun p hp => by
      show G p.1 p.2 = Fext p.1 p.2
      rw [h2 p.1 p.2 hp, h1 p.1 p.2 hp])
  funext x y
  exact congrFun this (x, y)

end HRS.MS.R26T8A
