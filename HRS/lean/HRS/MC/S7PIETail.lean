import Mathlib

/-!
# Packet PI-E, part 4: coordinatewise convergence plus a uniform higher weighted bound gives `ℓ²` convergence
-/

open Filter Topology Finset

noncomputable section

namespace HRS.MC.Sec7.PIE

variable {ι : Type*} {X : Type*}

/-- If `x_t → x_0` coordinatewise along `l` and the weighted squares `(w^p x_t)²` have sums bounded by `B`
(sublevel sets of the weight `w ≥ 1` finite, `p > 0`), then `x_t → x_0` in `ℓ²`. -/
theorem pie_tail_tendsto (l : Filter X) (w : ι → ℝ) (hw : ∀ k, 1 ≤ w k)
    (hfin : ∀ R : ℝ, {k | w k ≤ R}.Finite) (x : X → ι → ℝ) (x0 : ι → ℝ) {p : ℝ} (hp : 0 < p)
    (hcoord : ∀ k, Tendsto (fun t => x t k) l (𝓝 (x0 k))) {B : ℝ}
    (hB : ∀ᶠ t in l, Summable (fun k => (w k ^ p * x t k) ^ 2) ∧ ∑' k, (w k ^ p * x t k) ^ 2 ≤ B)
    (hB0 : Summable (fun k => (w k ^ p * x0 k) ^ 2) ∧ ∑' k, (w k ^ p * x0 k) ^ 2 ≤ B) :
    (∀ᶠ t in l, Summable fun k => (x t k - x0 k) ^ 2) ∧
      Tendsto (fun t => ∑' k, (x t k - x0 k) ^ 2) l (𝓝 0) := by
  classical
  have hwp : ∀ k, 1 ≤ w k ^ p := fun k => Real.one_le_rpow (hw k) hp.le
  have hsq : ∀ y : ι → ℝ, Summable (fun k => (w k ^ p * y k) ^ 2) → Summable fun k => y k ^ 2 := by
    intro y hy
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hy
    have : 1 ≤ (w k ^ p) ^ 2 := one_le_pow₀ (hwp k)
    rw [mul_pow]
    nlinarith [sq_nonneg (y k)]
  have hdiff : ∀ y z : ι → ℝ, Summable (fun k => y k ^ 2) → Summable (fun k => z k ^ 2) →
      Summable fun k => (y k - z k) ^ 2 := by
    intro y z hy hz
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) ((hy.add hz).mul_left 2)
    nlinarith [sq_nonneg (y k + z k)]
  have hsum_ev : ∀ᶠ t in l, Summable fun k => (x t k - x0 k) ^ 2 := by
    filter_upwards [hB] with t ht
    exact hdiff _ _ (hsq _ ht.1) (hsq _ hB0.1)
  refine ⟨hsum_ev, ?_⟩
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · exact Eventually.of_forall fun t => lt_of_lt_of_le ha (tsum_nonneg fun k => sq_nonneg _)
  · have hBnn : 0 ≤ B := le_trans (tsum_nonneg fun k => sq_nonneg _) hB0.2
    obtain ⟨R, hR1, hR⟩ : ∃ R : ℝ, 1 ≤ R ∧ 4 * B / R ^ (2 * p) < a / 2 := by
      have h1 : Tendsto (fun R : ℝ => R ^ (2 * p)) atTop atTop :=
        tendsto_rpow_atTop (by positivity)
      have h2 : Tendsto (fun R : ℝ => 4 * B / R ^ (2 * p)) atTop (𝓝 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds h1
      have := (h2.eventually (gt_mem_nhds (show (0 : ℝ) < a / 2 by linarith))).and
        (eventually_ge_atTop (1 : ℝ))
      obtain ⟨R, hR⟩ := this.exists
      exact ⟨R, hR.2, hR.1⟩
    set S : Finset ι := (hfin R).toFinset with hS
    have hmemS : ∀ k, k ∈ S ↔ w k ≤ R := fun k => by simp [hS]
    have hfinpart : Tendsto (fun t => ∑ k ∈ S, (x t k - x0 k) ^ 2) l (𝓝 0) := by
      have : Tendsto (fun t => ∑ k ∈ S, (x t k - x0 k) ^ 2) l (𝓝 (∑ k ∈ S, (x0 k - x0 k) ^ 2)) :=
        tendsto_finset_sum _ fun k _ => ((hcoord k).sub_const (x0 k)).pow 2
      simpa using this
    have hev := (hfinpart.eventually (gt_mem_nhds (show (0 : ℝ) < a / 2 by linarith))).and
      (hB.and hsum_ev)
    filter_upwards [hev] with t ht
    obtain ⟨h1, ⟨hBt, hBt2⟩, hsumt⟩ := ht
    rw [← Summable.sum_add_tsum_compl (s := S) hsumt]
    have hRp : 0 < R ^ (2 * p) := Real.rpow_pos_of_pos (by linarith) _
    set g1 : ι → ℝ := fun k => (w k ^ p * x t k) ^ 2 with hg1
    set g2 : ι → ℝ := fun k => (w k ^ p * x0 k) ^ 2 with hg2
    have hterm : ∀ k : ↑((S : Set ι)ᶜ), (x t k - x0 k) ^ 2 ≤
        (2 / R ^ (2 * p)) * (g1 k + g2 k) := by
      rintro ⟨k, hk⟩
      have hk' : k ∉ S := hk
      have hwk : R < w k := by
        by_contra h; exact hk' ((hmemS k).2 (not_lt.1 h))
      have hwk2 : R ^ (2 * p) ≤ (w k ^ p) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [hw k])]
        have : p * (2 : ℕ) = 2 * p := by push_cast; ring
        rw [this]
        exact Real.rpow_le_rpow (by linarith) hwk.le (by positivity)
      have e1 : (x t k) ^ 2 ≤ g1 k / R ^ (2 * p) := by
        rw [le_div_iff₀ hRp]
        simp only [hg1, mul_pow]
        nlinarith [sq_nonneg (x t k)]
      have e2 : (x0 k) ^ 2 ≤ g2 k / R ^ (2 * p) := by
        rw [le_div_iff₀ hRp]
        simp only [hg2, mul_pow]
        nlinarith [sq_nonneg (x0 k)]
      have e3 : (x t k - x0 k) ^ 2 ≤ 2 * (x t k) ^ 2 + 2 * (x0 k) ^ 2 := by
        nlinarith [sq_nonneg (x t k + x0 k)]
      calc (x t k - x0 k) ^ 2 ≤ 2 * (x t k) ^ 2 + 2 * (x0 k) ^ 2 := e3
        _ ≤ 2 * (g1 k / R ^ (2 * p)) + 2 * (g2 k / R ^ (2 * p)) := by linarith
        _ = (2 / R ^ (2 * p)) * (g1 k + g2 k) := by field_simp
    have hg1s : Summable g1 := hBt
    have hg2s : Summable g2 := hB0.1
    have hsub : ∀ g : ι → ℝ, (∀ k, 0 ≤ g k) → Summable g →
        ∑' k : ↑((S : Set ι)ᶜ), g k ≤ ∑' k, g k := fun g hg hs => Summable.tsum_subtype_le g _ hg hs
    have htail : ∑' k : ↑((S : Set ι)ᶜ), (x t k - x0 k) ^ 2 ≤ 4 * B / R ^ (2 * p) := by
      have hs1 : Summable fun k : ↑((S : Set ι)ᶜ) => g1 k := hg1s.subtype _
      have hs2 : Summable fun k : ↑((S : Set ι)ᶜ) => g2 k := hg2s.subtype _
      have hsc : Summable fun k : ↑((S : Set ι)ᶜ) => (2 / R ^ (2 * p)) * (g1 k + g2 k) :=
        (hs1.add hs2).mul_left _
      calc ∑' k : ↑((S : Set ι)ᶜ), (x t k - x0 k) ^ 2
          ≤ ∑' k : ↑((S : Set ι)ᶜ), (2 / R ^ (2 * p)) * (g1 k + g2 k) :=
            Summable.tsum_le_tsum hterm (hsumt.subtype _) hsc
        _ = (2 / R ^ (2 * p)) * (∑' k : ↑((S : Set ι)ᶜ), g1 k + ∑' k : ↑((S : Set ι)ᶜ), g2 k) := by
            rw [tsum_mul_left, Summable.tsum_add hs1 hs2]
        _ ≤ (2 / R ^ (2 * p)) * (B + B) := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
            · exact (hsub g1 (fun k => sq_nonneg _) hg1s).trans hBt2
            · exact (hsub g2 (fun k => sq_nonneg _) hg2s).trans hB0.2
        _ = 4 * B / R ^ (2 * p) := by field_simp; ring
    linarith

end HRS.MC.Sec7.PIE

end
