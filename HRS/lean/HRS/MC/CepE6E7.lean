import HRS.MC.CepE6E6

/-!
# Packet CEPE6E, file 7: probabilistic selection lemmas

* `cepe6e_subseq`: from uniform convergence in probability on `[0,T]` extract a deterministic subsequence converging
  uniformly a.s. (Borel–Cantelli).
* `cepe6e_select`: Fatou + Markov + Borel–Cantelli selection of sub-subsequences along which the weighted sums
  `Y k j` stay below `2 · 2^{-k}`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6E

open HRS HRS.MC.Cepa HRS.MC.CepE6D

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cepe6e_subseq [IsProbabilityMeasure P] {Zn : ℕ → ℝ → Ω → Ch N} {Zl : ℝ → Ω → Ch N} {T : ℝ}
    (hZn : ∀ n ω, Continuous fun t => Zn n t ω) (hZl : ∀ ω, Continuous fun t => Zl t ω)
    (hprob : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
      P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Zn n t ω - Zl t ω‖}) atTop (𝓝 0)) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ i, 1 ≤ m i) ∧ ∀ᵐ ω ∂P,
      TendstoUniformlyOn (fun i t => Zn (m i) t ω) (fun t => Zl t ω) atTop (Icc 0 T) := by
  classical
  have h : ∀ k : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      P {ω | (1 / ((k : ℝ) + 1)) < ⨆ t : Set.Icc (0 : ℝ) T, ‖Zn n t ω - Zl t ω‖} < (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    have h1 := hprob (1 / ((k : ℝ) + 1)) (by positivity)
    have hpos : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ k := ENNReal.pow_pos (by simp) k
    exact eventually_atTop.1 (h1.eventually (gt_mem_nhds hpos))
  choose nk hnk using h
  set m : ℕ → ℕ := fun k => k + 1 + (Finset.range (k + 1)).sup nk with hm
  have hmono : StrictMono m := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    have : (Finset.range (k + 1)).sup nk ≤ (Finset.range (k + 1 + 1)).sup nk :=
      Finset.sup_mono (Finset.range_mono (by omega))
    simp only [hm]; omega
  have hmk : ∀ k, nk k ≤ m k := fun k => by
    have := Finset.le_sup (f := nk) (Finset.mem_range.2 (show k < k + 1 by omega))
    simp only [hm]; omega
  refine ⟨m, hmono, fun i => by simp only [hm]; omega, ?_⟩
  set S : ℕ → Set Ω := fun k => {ω | (1 / ((k : ℝ) + 1)) <
    ⨆ t : Set.Icc (0 : ℝ) T, ‖Zn (m k) t ω - Zl t ω‖} with hS
  have hsum : ∑' k, P (S k) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k) ?_ ?_
    · rw [ENNReal.tsum_geometric]
      refine ENNReal.inv_ne_top.2 ?_
      simp
    · exact ENNReal.tsum_le_tsum fun k => (hnk k (m k) (hmk k)).le
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω, eventually_ge_atTop k₀] with k hk hkk t ht
  have hbdd : BddAbove (Set.range fun s : Set.Icc (0 : ℝ) T => ‖Zn (m k) s ω - Zl s ω‖) := by
    have hc : Continuous fun s : Set.Icc (0 : ℝ) T => ‖Zn (m k) s ω - Zl s ω‖ :=
      (((hZn (m k) ω).sub (hZl ω)).norm).comp continuous_subtype_val
    exact (isCompact_range hc).bddAbove
  have h1 : ‖Zn (m k) t ω - Zl t ω‖ ≤ ⨆ s : Set.Icc (0 : ℝ) T, ‖Zn (m k) s ω - Zl s ω‖ :=
    le_ciSup hbdd ⟨t, ht⟩
  have h2 : (⨆ s : Set.Icc (0 : ℝ) T, ‖Zn (m k) s ω - Zl s ω‖) ≤ 1 / ((k : ℝ) + 1) := by
    by_contra hcon
    exact hk (not_le.1 hcon)
  have h3 : 1 / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (k₀ : ℝ) ≤ k := by exact_mod_cast hkk
    linarith
  rw [dist_comm, dist_eq_norm]
  linarith

/-- Fatou + Markov + Borel–Cantelli selection. -/
theorem cepe6e_select [IsProbabilityMeasure P] {Y : ℕ → ℕ → Ω → ℝ≥0∞}
    (hY : ∀ k j, AEMeasurable (Y k j) P) {c : ℝ} (hc : 0 ≤ c)
    (hint : ∀ k, liminf (fun j => ∫⁻ ω, Y k j ω ∂P) atTop ≤ ENNReal.ofReal (c * (1 / 4) ^ k)) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j, Y k (φ j) ω < ENNReal.ofReal (2 * (1 / 2) ^ k) := by
  classical
  set Ψ : ℕ → Ω → ℝ≥0∞ := fun k ω => liminf (fun j => Y k j ω) atTop with hΨ
  have hΨm : ∀ k, AEMeasurable (Ψ k) P := fun k => AEMeasurable.liminf (hY k)
  have hΨi : ∀ k, ∫⁻ ω, Ψ k ω ∂P ≤ ENNReal.ofReal (c * (1 / 4) ^ k) := fun k =>
    (lintegral_liminf_le' (hY k)).trans (hint k)
  set S : ℕ → Set Ω := fun k => {ω | ENNReal.ofReal ((1 / 2) ^ k) ≤ Ψ k ω} with hS
  have hSb : ∀ k, P (S k) ≤ ENNReal.ofReal c * (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    have hpos : (0 : ℝ) < (1 / 2) ^ k := by positivity
    have h1 := mul_meas_ge_le_lintegral₀ (hΨm k) (ENNReal.ofReal ((1 / 2) ^ k))
    have h2 : ENNReal.ofReal ((1 / 2) ^ k) * P (S k) ≤ ENNReal.ofReal (c * (1 / 4) ^ k) :=
      h1.trans (hΨi k)
    have h3 : c * (1 / 4) ^ k = ((1 / 2) ^ k) * (c * (1 / 2) ^ k) := by
      rw [show ((1 : ℝ) / 4) = (1 / 2) * (1 / 2) by norm_num, mul_pow]; ring
    rw [h3, ENNReal.ofReal_mul hpos.le] at h2
    have h4 : ENNReal.ofReal ((1 / 2) ^ k) ≠ 0 := by simpa using hpos
    have h5 := (ENNReal.mul_le_mul_iff_right (a := ENNReal.ofReal ((1 / 2) ^ k)) h4
      ENNReal.ofReal_ne_top).1 h2
    refine h5.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_pow (by norm_num)]
    congr 2
    rw [show ((1 : ℝ) / 2) = ((2 : ℝ)⁻¹) by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  have hsum : ∑' k, P (S k) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, ENNReal.ofReal c * (2⁻¹ : ℝ≥0∞) ^ k) ?_ ?_
    · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 ?_)
      simp
    · exact ENNReal.tsum_le_tsum hSb
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with k hk
  have hlt : Ψ k ω < ENNReal.ofReal (2 * (1 / 2) ^ k) := by
    have h1 : Ψ k ω < ENNReal.ofReal ((1 / 2) ^ k) := not_le.1 hk
    refine h1.trans_le (ENNReal.ofReal_le_ofReal ?_)
    have : (0 : ℝ) < (1 / 2) ^ k := by positivity
    linarith
  have hfr : ∃ᶠ j in atTop, Y k j ω < ENNReal.ofReal (2 * (1 / 2) ^ k) :=
    Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
  exact Filter.extraction_of_frequently_atTop hfr

end HRS.MC.CepE6E
