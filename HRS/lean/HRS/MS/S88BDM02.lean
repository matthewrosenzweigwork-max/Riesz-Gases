import HRS.MS.S88BDM01
import HRS.MS.S88BDDefs

/-!
# S8.8.M02: countable sampling closure of the dyadic maximal estimate

`s88_countable_maximal`: the dyadic bound of M01 passes to any countable family of sample times in `[0,T]`.
For one sample time `s`, the dyadic points `d_n` with `|s - d_n| ≤ T 2^{-n}` satisfy
`∑_n E(Y_s - Y_{d_n})² < ∞`, hence `Y_{d_n} → Y_s` almost surely, and `Y_s² ≤ sup_n max_{grid n} Y²` a.e.;
only countably many null sets are intersected.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S88Breakdown

theorem s88_ratTime_countable (T : ℝ) : Countable (S88RatTime T) := by
  classical
  refine Function.Injective.countable (f := fun t : S88RatTime T => Classical.choose t.2.2) ?_
  intro t t' h
  refine Subtype.ext ?_
  have h1 := Classical.choose_spec t.2.2
  have h2 := Classical.choose_spec t'.2.2
  rw [← h1, ← h2]
  exact congrArg (fun q : ℚ => (q : ℝ)) h

theorem s88_countable_maximal {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T B D : ℝ)
    (hT : 0 < T) (hB : 0 ≤ B) (hD : 0 ≤ D) (Y : ℝ → Ω → ℝ)
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) T, MemLp (Y t) 2 P)
    (hbase : (∫⁻ z, ENNReal.ofReal ((Y 0 z) ^ 2) ∂P) ≤ ENNReal.ofReal B)
    (hinc : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ z, ENNReal.ofReal ((Y s z - Y t z) ^ 2) ∂P) ≤
        ENNReal.ofReal (D * (s - t) ^ 2))
    {ι : Type*} [Countable ι] (σ : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc (0 : ℝ) T) :
    AEMeasurable (fun z => ⨆ i : ι, ENNReal.ofReal ((Y (σ i) z) ^ 2)) P ∧
      (∫⁻ z, (⨆ i : ι, ENNReal.ofReal ((Y (σ i) z) ^ 2)) ∂P) ≤
        ENNReal.ofReal (64 * (B + T ^ 2 * D)) := by
  have hpt : ∀ j k : ℕ, k ≤ 2 ^ j → T * (k : ℝ) / 2 ^ j ∈ Set.Icc (0 : ℝ) T := by
    intro j k hk
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    have : (k : ℝ) ≤ 2 ^ j := by exact_mod_cast hk
    nlinarith
  have hmeasY : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z => ENNReal.ofReal (Y t z ^ 2)) P := fun t ht =>
    ((hmem t ht).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  refine ⟨AEMeasurable.iSup fun i => hmeasY _ (hσ i), ?_⟩
  set G : ℕ → Ω → ℝ≥0∞ := fun n z => ⨆ j : Fin (2 ^ n + 1),
    ENNReal.ofReal ((Y (T * ((j : ℕ) : ℝ) / (2 : ℝ) ^ n) z) ^ 2) with hG
  have hGmeas : ∀ n, AEMeasurable (G n) P := fun n =>
    AEMeasurable.iSup fun j => hmeasY _ (hpt n j (Nat.lt_succ_iff.1 j.2))
  have hGmono : ∀ z, Monotone fun n => G n z := by
    intro z
    refine monotone_nat_of_le_succ fun n => ?_
    refine iSup_le fun j => ?_
    refine le_iSup_of_le (⟨2 * (j : ℕ), by have := j.2; rw [pow_succ]; omega⟩ : Fin (2 ^ (n + 1) + 1)) ?_
    refine le_of_eq ?_
    congr 3
    push_cast
    rw [pow_succ]; field_simp
  set H : Ω → ℝ≥0∞ := fun z => ⨆ n, G n z with hH
  have hHint : ∫⁻ z, H z ∂P ≤ ENNReal.ofReal (64 * (B + T ^ 2 * D)) := by
    simp only [hH]
    rw [lintegral_iSup' hGmeas (Filter.Eventually.of_forall hGmono)]
    exact iSup_le fun n => s88_dyadic_maximal P T B D hT hB hD Y hmem hbase hinc n
  -- one sample time
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ᵐ z ∂P, ENNReal.ofReal (Y s z ^ 2) ≤ H z := by
    intro s hs
    set jn : ℕ → ℕ := fun n => ⌊s * 2 ^ n / T⌋₊ with hjn
    have hjle : ∀ n, jn n ≤ 2 ^ n := fun n => by
      refine Nat.floor_le_of_le ?_
      push_cast
      rw [div_le_iff₀ hT]
      have : (0 : ℝ) < 2 ^ n := by positivity
      nlinarith [mul_nonneg (sub_nonneg.2 hs.2) this.le]
    have hdn : ∀ n, T * ((jn n : ℕ) : ℝ) / 2 ^ n ∈ Set.Icc (0 : ℝ) T := fun n => hpt n _ (hjle n)
    have hdist : ∀ n, (s - T * ((jn n : ℕ) : ℝ) / 2 ^ n) ^ 2 ≤ (T / 2 ^ n) ^ 2 := by
      intro n
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      have hnn : 0 ≤ s * 2 ^ n / T := by have := hs.1; positivity
      have h1 : ((jn n : ℕ) : ℝ) ≤ s * 2 ^ n / T := Nat.floor_le hnn
      have h2 : s * 2 ^ n / T < ((jn n : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [le_div_iff₀ hT] at h1
      rw [div_lt_iff₀ hT] at h2
      have e1 : T * ((jn n : ℕ) : ℝ) / 2 ^ n ≤ s := by
        rw [div_le_iff₀ h2n]; nlinarith
      have e2 : s < T * ((jn n : ℕ) : ℝ) / 2 ^ n + T / 2 ^ n := by
        rw [← add_div, lt_div_iff₀ h2n]; nlinarith
      have : s - T * ((jn n : ℕ) : ℝ) / 2 ^ n ≤ T / 2 ^ n := by linarith
      nlinarith
    -- summability of the L² errors
    have hterm : ∀ n, ∫⁻ z, ENNReal.ofReal ((Y s z - Y (T * ((jn n : ℕ) : ℝ) / 2 ^ n) z) ^ 2) ∂P ≤
        ENNReal.ofReal (D * T ^ 2 * (1 / 4 : ℝ) ^ n) := by
      intro n
      refine (hinc s hs _ (hdn n)).trans (ENNReal.ofReal_le_ofReal ?_)
      calc D * (s - T * ((jn n : ℕ) : ℝ) / 2 ^ n) ^ 2 ≤ D * (T / 2 ^ n) ^ 2 :=
            mul_le_mul_of_nonneg_left (hdist n) hD
        _ = _ := by
            have e : (1 / 4 : ℝ) ^ n = 1 / ((2 : ℝ) ^ n) ^ 2 := by
              rw [one_div, one_div, inv_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
            rw [e, div_pow]
            field_simp
    have hsumm : Summable fun n : ℕ => D * T ^ 2 * (1 / 4 : ℝ) ^ n :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hsum_fin : ∑' n, ∫⁻ z, ENNReal.ofReal ((Y s z - Y (T * ((jn n : ℕ) : ℝ) / 2 ^ n) z) ^ 2) ∂P
        ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
      exact ENNReal.ofReal_ne_top
    have hmeasD : ∀ n, AEMeasurable (fun z => ENNReal.ofReal
        ((Y s z - Y (T * ((jn n : ℕ) : ℝ) / 2 ^ n) z) ^ 2)) P := by
      intro n
      have : MemLp (fun z => Y s z - Y (T * ((jn n : ℕ) : ℝ) / 2 ^ n) z) 2 P :=
        (hmem s hs).sub (hmem _ (hdn n))
      exact (this.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
    have hfin : ∫⁻ z, ∑' n, ENNReal.ofReal
        ((Y s z - Y (T * ((jn n : ℕ) : ℝ) / 2 ^ n) z) ^ 2) ∂P ≠ ⊤ := by
      rw [lintegral_tsum hmeasD]; exact hsum_fin
    have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hmeasD) hfin
    filter_upwards [hae] with z hz
    have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hz.ne
    have h1 : Tendsto (fun n => (Y s z - Y (T * ((jn n : ℕ) : ℝ) / 2 ^ n) z) ^ 2) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
      refine this.congr (fun n => ?_)
      simp [ENNReal.toReal_ofReal (sq_nonneg _)]
    have h2 : Tendsto (fun n => Y s z - Y (T * ((jn n : ℕ) : ℝ) / 2 ^ n) z) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at this
      refine tendsto_zero_iff_abs_tendsto_zero _ |>.2 (this.congr fun n => ?_)
      simp [Real.sqrt_sq_eq_abs]
    have h3 : Tendsto (fun n => Y (T * ((jn n : ℕ) : ℝ) / 2 ^ n) z) atTop (𝓝 (Y s z)) := by
      have := (tendsto_const_nhds (x := Y s z)).sub h2
      simp only [sub_zero] at this
      refine this.congr (fun n => ?_)
      ring
    have h4 := ENNReal.tendsto_ofReal (h3.pow 2)
    refine le_of_tendsto' h4 fun n => ?_
    refine le_trans ?_ (le_iSup (fun n => G n z) n)
    exact le_iSup_of_le (⟨jn n, Nat.lt_succ_of_le (hjle n)⟩ : Fin (2 ^ n + 1)) le_rfl
  have hall : ∀ᵐ z ∂P, ∀ i, ENNReal.ofReal (Y (σ i) z ^ 2) ≤ H z :=
    ae_all_iff.2 fun i => hpoint _ (hσ i)
  calc (∫⁻ z, (⨆ i : ι, ENNReal.ofReal ((Y (σ i) z) ^ 2)) ∂P) ≤ ∫⁻ z, H z ∂P :=
        lintegral_mono_ae (hall.mono fun z hz => iSup_le hz)
    _ ≤ _ := hHint

end HRS.MS.S88Breakdown
