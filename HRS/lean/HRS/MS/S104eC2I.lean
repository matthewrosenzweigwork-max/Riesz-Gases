import HRS.MS.S104eC2H

/-!
# S104E route C, packet C2, part I: families with jointly continuous jets (`JC`) and their algebra

Prefix `s104c2_`, namespace `HRS.MS.S104e.C`.  `JC S N f`: every `f v` (`v ∈ S`) is `C^N` and the jets `≤ N` of `(v,y) ↦ f v y` are jointly continuous on `S × ℝ^d`.
`JC` is closed under sums, constant multiples and products `u_v · w_v` provided `u_v` is bounded in `C^N`, depends continuously on `v` in the sup norm of its jets, and
`w_v` is bounded in `C^N` with `w ∈ JC` (`s104c2_JC_mul`; Leibniz inequality of Mathlib applied to the increments).
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.R2WinOrbNL

variable {d : ℕ}

/-- Jointly continuous jets of a family. -/
def JC (S : Set ℝ) (N : ℕ) (f : ℝ → Euc d → ℝ) : Prop :=
  (∀ v ∈ S, ContDiff ℝ N (f v)) ∧
    ∀ m ≤ N, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ m (f p.1) p.2) (S ×ˢ univ)

lemma JC.add {S : Set ℝ} {N : ℕ} {f g : ℝ → Euc d → ℝ} (hf : JC S N f) (hg : JC S N g) :
    JC S N (fun v y => f v y + g v y) := by
  refine ⟨fun v hv => (hf.1 v hv).add (hg.1 v hv), fun m hm => ?_⟩
  refine ((hf.2 m hm).add (hg.2 m hm)).congr fun p hp => ?_
  have e : (fun y => f p.1 y + g p.1 y) = f p.1 + g p.1 := rfl
  have hmN : (m : ℕ∞ω) ≤ (N : ℕ∞ω) := by exact_mod_cast hm
  show iteratedFDeriv ℝ m (fun y => f p.1 y + g p.1 y) p.2 = _
  rw [e, iteratedFDeriv_add_apply ((hf.1 p.1 hp.1).of_le hmN).contDiffAt ((hg.1 p.1 hp.1).of_le hmN).contDiffAt]
  rfl

lemma JC.const_mul {S : Set ℝ} {N : ℕ} {f : ℝ → Euc d → ℝ} (hf : JC S N f) (c : ℝ) :
    JC S N (fun v y => c * f v y) := by
  refine ⟨fun v hv => contDiff_const.mul (hf.1 v hv), fun m hm => ?_⟩
  refine ((hf.2 m hm).const_smul c).congr fun p hp => ?_
  have e : (fun y => c * f p.1 y) = c • f p.1 := by funext y; simp
  have hmN : (m : ℕ∞ω) ≤ (N : ℕ∞ω) := by exact_mod_cast hm
  show iteratedFDeriv ℝ m (fun y => c * f p.1 y) p.2 = _
  rw [e, iteratedFDeriv_const_smul_apply ((hf.1 p.1 hp.1).of_le hmN).contDiffAt]
  rfl

lemma JC.sum {S : Set ℝ} {N : ℕ} {ι : Type*} (u : Finset ι) {f : ι → ℝ → Euc d → ℝ}
    (hf : ∀ i ∈ u, JC S N (f i)) : JC S N (fun v y => ∑ i ∈ u, f i v y) := by
  refine ⟨fun v hv => ContDiff.sum fun i hi => (hf i hi).1 v hv, fun m hm => ?_⟩
  refine (continuousOn_finset_sum u fun i hi => (hf i hi).2 m hm).congr fun p hp => ?_
  have hmN : (m : ℕ∞ω) ≤ (N : ℕ∞ω) := by exact_mod_cast hm
  show iteratedFDeriv ℝ m (fun y => ∑ i ∈ u, f i p.1 y) p.2 = _
  rw [iteratedFDeriv_fun_sum_apply fun i hi => ((hf i hi).1 p.1 hp.1).of_le hmN |>.contDiffAt]

/-- The Leibniz estimate for the increment of a product. -/
lemma s104c2_PJ_est {N : ℕ} {u u0 w w0 : Euc d → ℝ} (hu : ContDiff ℝ N u) (hu0 : ContDiff ℝ N u0)
    (hw : ContDiff ℝ N w) (hw0 : ContDiff ℝ N w0) {Mu Mw ε1 ε2 : ℝ} (hMu : ∀ a ≤ N, ∀ y, ‖iteratedFDeriv ℝ a u0 y‖ ≤ Mu)
    (hMw : ∀ a ≤ N, ∀ y, ‖iteratedFDeriv ℝ a w y‖ ≤ Mw) (y : Euc d)
    (h1 : ∀ a ≤ N, ‖iteratedFDeriv ℝ a u y - iteratedFDeriv ℝ a u0 y‖ ≤ ε1)
    (h2 : ∀ a ≤ N, ‖iteratedFDeriv ℝ a w y - iteratedFDeriv ℝ a w0 y‖ ≤ ε2) {m : ℕ} (hm : m ≤ N) :
    ‖iteratedFDeriv ℝ m (fun z => u z * w z) y - iteratedFDeriv ℝ m (fun z => u0 z * w0 z) y‖ ≤
      2 ^ m * (ε1 * Mw + Mu * ε2) := by
  have hmN : (m : ℕ∞ω) ≤ (N : ℕ∞ω) := by exact_mod_cast hm
  have hMw0 : 0 ≤ Mw := (norm_nonneg _).trans (hMw 0 (Nat.zero_le _) y)
  have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu 0 (Nat.zero_le _) y)
  have hε1 : 0 ≤ ε1 := (norm_nonneg _).trans (h1 0 (Nat.zero_le _))
  have hε2 : 0 ≤ ε2 := (norm_nonneg _).trans (h2 0 (Nat.zero_le _))
  have hA : ContDiff ℝ N (fun z => u z * w z) := hu.mul hw
  have hA0 : ContDiff ℝ N (fun z => u0 z * w0 z) := hu0.mul hw0
  have hdu : ContDiff ℝ N (fun z => u z - u0 z) := hu.sub hu0
  have hdw : ContDiff ℝ N (fun z => w z - w0 z) := hw.sub hw0
  have hsplit : (fun z => u z * w z) - (fun z => u0 z * w0 z) =
      (fun z => (u z - u0 z) * w z) + (fun z => u0 z * (w z - w0 z)) := by funext z; simp; ring
  have e1 : iteratedFDeriv ℝ m (fun z => u z * w z) y - iteratedFDeriv ℝ m (fun z => u0 z * w0 z) y =
      iteratedFDeriv ℝ m ((fun z => u z * w z) - (fun z => u0 z * w0 z)) y :=
    (iteratedFDeriv_sub_apply (hA.of_le hmN).contDiffAt (hA0.of_le hmN).contDiffAt).symm
  rw [e1, hsplit, iteratedFDeriv_add_apply ((hdu.mul hw).of_le hmN).contDiffAt ((hu0.mul hdw).of_le hmN).contDiffAt]
  refine (norm_add_le _ _).trans ?_
  have hsum : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = 2 ^ m := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; rfl
  have T1 : ‖iteratedFDeriv ℝ m (fun z => (u z - u0 z) * w z) y‖ ≤ 2 ^ m * (ε1 * Mw) := by
    refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (N : ℕ∞ω)) hdu hw y (n := m) hmN).trans ?_
    rw [← hsum, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := h1 i (by omega)
    rw [← iteratedFDeriv_sub_apply (hu.of_le (by exact_mod_cast (by omega : i ≤ N))).contDiffAt
      (hu0.of_le (by exact_mod_cast (by omega : i ≤ N))).contDiffAt] at this
    exact mul_le_mul this (hMw (m - i) (by omega) y) (norm_nonneg _) hε1
  have T2 : ‖iteratedFDeriv ℝ m (fun z => u0 z * (w z - w0 z)) y‖ ≤ 2 ^ m * (Mu * ε2) := by
    refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (N : ℕ∞ω)) hu0 hdw y (n := m) hmN).trans ?_
    rw [← hsum, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := h2 (m - i) (by omega)
    rw [← iteratedFDeriv_sub_apply (hw.of_le (by exact_mod_cast (by omega : m - i ≤ N))).contDiffAt
      (hw0.of_le (by exact_mod_cast (by omega : m - i ≤ N))).contDiffAt] at this
    exact mul_le_mul (hMu i (by omega) y) this (norm_nonneg _) hMu0
  nlinarith

theorem s104c2_JC_mul {S : Set ℝ} {N : ℕ} {u w : ℝ → Euc d → ℝ} {Mu Mw : ℝ}
    (hu : ∀ v ∈ S, ContDiff ℝ N (u v)) (hw : JC S N w)
    (hMu : ∀ v ∈ S, ∀ a ≤ N, ∀ y, ‖iteratedFDeriv ℝ a (u v) y‖ ≤ Mu)
    (hMw : ∀ v ∈ S, ∀ a ≤ N, ∀ y, ‖iteratedFDeriv ℝ a (w v) y‖ ≤ Mw)
    (huc : ∀ v0 ∈ S, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ S, |v - v0| < δ → ∀ a ≤ N, ∀ y,
      ‖iteratedFDeriv ℝ a (u v) y - iteratedFDeriv ℝ a (u v0) y‖ ≤ ε) :
    JC S N (fun v y => u v y * w v y) := by
  refine ⟨fun v hv => (hu v hv).mul (hw.1 v hv), fun m hm p0 hp0 => ?_⟩
  have hv0 : p0.1 ∈ S := hp0.1
  have hMw0 : 0 ≤ Mw := (norm_nonneg _).trans (hMw p0.1 hv0 0 (Nat.zero_le _) p0.2)
  have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu p0.1 hv0 0 (Nat.zero_le _) p0.2)
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  set c : ℝ := 2 ^ m * (Mw + Mu + 1) with hc
  have hcpos : 0 < c := by positivity
  set ε' : ℝ := ε / (4 * c) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨δu, hδu, hδ⟩ := huc p0.1 hv0 ε' hε'pos
  set l : Filter (ℝ × Euc d) := 𝓝[S ×ˢ univ] p0 with hl
  have F0 : ∀ᶠ p in l, p ∈ S ×ˢ univ := self_mem_nhdsWithin
  have F1 : ∀ᶠ p in l, |p.1 - p0.1| < δu := by
    have := (continuous_fst.continuousAt (x := p0)).tendsto.mono_left (nhdsWithin_le_nhds (s := S ×ˢ univ))
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 this δu hδu)
  have F2 : ∀ᶠ p in l, ∀ a ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ a (w p.1) p.2 - iteratedFDeriv ℝ a (w p0.1) p0.2‖ < ε' / 2 := by
    rw [Filter.eventually_all_finset]
    intro a ha
    have := hw.2 a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) p0 hp0
    have h2 := Metric.tendsto_nhds.1 this (ε' / 2) (by positivity)
    simpa [Real.dist_eq, dist_eq_norm] using h2
  have F3 : ∀ᶠ p in l, ∀ a ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ a (w p0.1) p.2 - iteratedFDeriv ℝ a (w p0.1) p0.2‖ < ε' / 2 := by
    rw [Filter.eventually_all_finset]
    intro a ha
    have hcont : Continuous (iteratedFDeriv ℝ a (w p0.1)) :=
      (hw.1 p0.1 hv0).continuous_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
    have h1 : Tendsto (fun p : ℝ × Euc d => p.2) l (𝓝 p0.2) :=
      (continuous_snd.continuousAt (x := p0)).tendsto.mono_left nhdsWithin_le_nhds
    have h2 := (hcont.continuousAt (x := p0.2)).tendsto.comp h1
    simpa [dist_eq_norm] using Metric.tendsto_nhds.1 h2 (ε' / 2) (by positivity)
  have F4 : ∀ᶠ p in l, ‖iteratedFDeriv ℝ m (fun y => u p0.1 y * w p0.1 y) p.2 -
      iteratedFDeriv ℝ m (fun y => u p0.1 y * w p0.1 y) p0.2‖ < ε / 2 := by
    have hcont : Continuous (iteratedFDeriv ℝ m (fun y => u p0.1 y * w p0.1 y)) :=
      ((hu p0.1 hv0).mul (hw.1 p0.1 hv0)).continuous_iteratedFDeriv (by exact_mod_cast hm)
    have h1 : Tendsto (fun p : ℝ × Euc d => p.2) l (𝓝 p0.2) :=
      (continuous_snd.continuousAt (x := p0)).tendsto.mono_left nhdsWithin_le_nhds
    have h2 := (hcont.continuousAt (x := p0.2)).tendsto.comp h1
    simpa [dist_eq_norm] using Metric.tendsto_nhds.1 h2 (ε / 2) (by positivity)
  filter_upwards [F0, F1, F2, F3, F4] with p hp h1 h2 h3 h4
  have hpS : p.1 ∈ S := hp.1
  have hest := s104c2_PJ_est (hu p.1 hpS) (hu p0.1 hv0) (hw.1 p.1 hpS) (hw.1 p0.1 hv0) (Mu := Mu) (Mw := Mw)
    (ε1 := ε') (ε2 := ε') (hMu p0.1 hv0) (hMw p.1 hpS) p.2 (fun a ha => hδ p.1 hpS h1 a ha p.2)
    (fun a ha => by
      have ha' : a ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
      have := norm_sub_le_norm_sub_add_norm_sub (iteratedFDeriv ℝ a (w p.1) p.2) (iteratedFDeriv ℝ a (w p0.1) p0.2)
        (iteratedFDeriv ℝ a (w p0.1) p.2)
      have e := h3 a ha'
      have f := h2 a ha'
      have e2 := norm_sub_rev (iteratedFDeriv ℝ a (w p0.1) p0.2) (iteratedFDeriv ℝ a (w p0.1) p.2)
      linarith) hm
  show dist (iteratedFDeriv ℝ m (fun y => u p.1 y * w p.1 y) p.2) (iteratedFDeriv ℝ m (fun y => u p0.1 y * w p0.1 y) p0.2) < ε
  rw [dist_eq_norm]
  have htri := norm_sub_le_norm_sub_add_norm_sub (iteratedFDeriv ℝ m (fun y => u p.1 y * w p.1 y) p.2)
    (iteratedFDeriv ℝ m (fun y => u p0.1 y * w p0.1 y) p.2) (iteratedFDeriv ℝ m (fun y => u p0.1 y * w p0.1 y) p0.2)
  have hbd : 2 ^ m * (ε' * Mw + Mu * ε') ≤ ε / 4 := by
    have : 2 ^ m * (ε' * Mw + Mu * ε') ≤ c * ε' := by
      have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
      rw [hc]
      nlinarith [mul_nonneg h2m hε'pos.le, mul_nonneg (mul_nonneg h2m hε'pos.le) hMw0,
        mul_nonneg (mul_nonneg h2m hε'pos.le) hMu0]
    have e : c * ε' = ε / 4 := by rw [hε']; field_simp
    linarith
  linarith

end HRS.MS.S104e.C

end
