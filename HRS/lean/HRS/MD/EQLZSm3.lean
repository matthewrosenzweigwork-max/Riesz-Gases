import HRS.MD.EQLZSm2

/-!
# EQ-LZ packet SM, part 3: abstract limit lemmas

* `sm_fatou_core`: Fatou in the level `n` for the grid maximal function (processes that agree eventually, pathwise,
  on `[0, a+T]`).
* `sm_dyadic_le`: for a continuous path, the value at every time of `[a, a+T]` is dominated by the supremum over the
  dyadic grids `a + j T/2^i` (squared increments).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS

namespace MD

namespace EQLZSm

/-- The grid points `a + j (T/m)`, `j ≤ m`, lie in `[a, a+T]`. -/
theorem sm_grid_mem {a T : ℝ} (hT : 0 ≤ T) {m : ℕ} (j : Fin (m + 1)) :
    a ≤ a + (j : ℕ) * (T / m) ∧ a + (j : ℕ) * (T / m) ≤ a + T := by
  have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.1 j.2
  refine ⟨by have : 0 ≤ (j : ℕ) * (T / m) := by positivity
             linarith, ?_⟩
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0
    have : (j : ℕ) = 0 := by omega
    simp [this, hT]
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have : ((j : ℕ) : ℝ) * (T / m) ≤ m * (T / m) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)
    have h2 : (m : ℝ) * (T / m) = T := by field_simp
    linarith

/-- Fatou in the level for the grid maximal function. -/
theorem sm_fatou_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {E : Type*} [MeasurableSpace E]
    (Z : ℕ → ℝ → Ω → E) (Zl : ℝ → Ω → E) (Φ : E → ℝ) (hΦ : Measurable Φ)
    (hmeas : ∀ n t, Measurable (Z n t)) (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (m : ℕ)
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ a + T → Z n t ω = Zl t ω)
    (b : ℕ → ℝ) (b' : ℝ) (hb : Tendsto b atTop (𝓝 b'))
    (hbound : ∀ n, ∫⁻ ω, ⨆ j : Fin (m + 1),
      ENNReal.ofReal ((Φ (Z n (a + (j : ℕ) * (T / m)) ω) - Φ (Z n a ω)) ^ 2) ∂P ≤ ENNReal.ofReal (b n)) :
    ∫⁻ ω, ⨆ j : Fin (m + 1),
      ENNReal.ofReal ((Φ (Zl (a + (j : ℕ) * (T / m)) ω) - Φ (Zl a ω)) ^ 2) ∂P ≤ ENNReal.ofReal b' := by
  set S : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨆ j : Fin (m + 1),
    ENNReal.ofReal ((Φ (Z n (a + (j : ℕ) * (T / m)) ω) - Φ (Z n a ω)) ^ 2) with hS
  have hSm : ∀ n, Measurable (S n) := fun n =>
    Measurable.iSup fun j => ENNReal.measurable_ofReal.comp
      (((hΦ.comp (hmeas n _)).sub (hΦ.comp (hmeas n a))).pow_const 2)
  have hlim : ∀ᵐ ω ∂P, (⨆ j : Fin (m + 1),
      ENNReal.ofReal ((Φ (Zl (a + (j : ℕ) * (T / m)) ω) - Φ (Zl a ω)) ^ 2)) = liminf (fun n => S n ω) atTop := by
    filter_upwards [hev] with ω hω
    have h1 : ∀ᶠ n in atTop, (⨆ j : Fin (m + 1),
        ENNReal.ofReal ((Φ (Zl (a + (j : ℕ) * (T / m)) ω) - Φ (Zl a ω)) ^ 2)) = S n ω := by
      filter_upwards [hω] with n hn
      simp only [hS]
      congr 1
      funext j
      obtain ⟨h1, h2⟩ := sm_grid_mem (a := a) hT j
      rw [hn _ (ha.trans h1) h2, hn a ha (by linarith)]
    have : Tendsto (fun n => S n ω) atTop (𝓝 (⨆ j : Fin (m + 1),
        ENNReal.ofReal ((Φ (Zl (a + (j : ℕ) * (T / m)) ω) - Φ (Zl a ω)) ^ 2))) :=
      tendsto_const_nhds.congr' (h1.mono fun n hn => hn)
    exact this.liminf_eq.symm
  rw [lintegral_congr_ae hlim]
  refine (lintegral_liminf_le hSm).trans ?_
  have hb' : Tendsto (fun n => ENNReal.ofReal (b n)) atTop (𝓝 (ENNReal.ofReal b')) :=
    ENNReal.tendsto_ofReal hb
  rw [← hb'.liminf_eq]
  exact liminf_le_liminf (Filter.Eventually.of_forall hbound)

/-- The dyadic grid maximal function of a path `g` (any `ℝ≥0∞`-valued function of time). -/
def smGrid (g : ℝ → ℝ≥0∞) (a T : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ⨆ j : Fin (m + 1), g (a + (j : ℕ) * (T / m))

theorem smGrid_mono (g : ℝ → ℝ≥0∞) (a T : ℝ) : Monotone fun i : ℕ => smGrid g a T (2 ^ i) := by
  refine monotone_nat_of_le_succ fun i => ?_
  unfold smGrid
  refine iSup_le fun j => ?_
  have hj : 2 * (j : ℕ) < 2 ^ (i + 1) + 1 := by
    have := j.2
    rw [pow_succ]; omega
  refine le_trans (le_of_eq ?_) (le_iSup (fun j' : Fin (2 ^ (i + 1) + 1) =>
    g (a + (j' : ℕ) * (T / ((2 ^ (i + 1) : ℕ) : ℝ)))) ⟨2 * (j : ℕ), hj⟩)
  congr 1
  have h2 : (((2 ^ (i + 1) : ℕ) : ℝ)) = 2 * ((2 ^ i : ℕ) : ℝ) := by push_cast; ring
  have h3 : (0 : ℝ) < ((2 ^ i : ℕ) : ℝ) := by positivity
  simp only [Nat.cast_mul, Nat.cast_ofNat, h2]
  field_simp

/-- A continuous path: the squared increment at any time of `[a, a+T]` is dominated by the supremum over
the dyadic grids. -/
theorem sm_dyadic_le (f : ℝ → ℝ) (a T : ℝ) (hT : 0 ≤ T) (hf : ContinuousOn f (Set.Icc a (a + T)))
    {t : ℝ} (ht : t ∈ Set.Icc a (a + T)) :
    ENNReal.ofReal ((f t - f a) ^ 2) ≤
      ⨆ i : ℕ, smGrid (fun s => ENNReal.ofReal ((f s - f a) ^ 2)) a T (2 ^ i) := by
  rcases hT.eq_or_lt with h0 | hpos
  · subst h0
    have : t = a := by have := ht.1; have := ht.2; linarith
    subst this
    simp
  · set x := (t - a) / T with hx
    have hx0 : 0 ≤ x := div_nonneg (by linarith [ht.1]) hT
    have hx1 : x ≤ 1 := by rw [hx, div_le_one hpos]; linarith [ht.2]
    set j : ℕ → ℕ := fun i => ⌊x * 2 ^ i⌋₊ with hj
    have hjle : ∀ i, j i ≤ 2 ^ i := fun i => Nat.floor_le_of_le (by
      have : (0 : ℝ) < 2 ^ i := by positivity
      calc x * 2 ^ i ≤ 1 * 2 ^ i := by gcongr
        _ = ((2 ^ i : ℕ) : ℝ) := by push_cast; ring)
    set tt : ℕ → ℝ := fun i => a + (j i : ℝ) * (T / ((2 ^ i : ℕ) : ℝ)) with htt
    have hpow : ∀ i : ℕ, (0 : ℝ) < ((2 ^ i : ℕ) : ℝ) := fun i => by positivity
    have hlow : ∀ i, tt i ≤ t := by
      intro i
      have h1 : (j i : ℝ) ≤ x * 2 ^ i := Nat.floor_le (by positivity)
      have h2 : (j i : ℝ) * (T / ((2 ^ i : ℕ) : ℝ)) ≤ t - a := by
        have : (j i : ℝ) * (T / ((2 ^ i : ℕ) : ℝ)) ≤ x * 2 ^ i * (T / ((2 ^ i : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by have := hpow i; positivity)
        have h3 : x * 2 ^ i * (T / ((2 ^ i : ℕ) : ℝ)) = x * T := by
          push_cast; field_simp
        rw [h3, hx] at this
        rwa [div_mul_cancel₀ _ hpos.ne'] at this
      simp only [htt]; linarith
    have hup : ∀ i, t - T / ((2 ^ i : ℕ) : ℝ) ≤ tt i := by
      intro i
      have h1 : x * 2 ^ i < (j i : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : t - a - T / ((2 ^ i : ℕ) : ℝ) ≤ (j i : ℝ) * (T / ((2 ^ i : ℕ) : ℝ)) := by
        have h3 : x * 2 ^ i * (T / ((2 ^ i : ℕ) : ℝ)) = t - a := by
          have : x * 2 ^ i * (T / ((2 ^ i : ℕ) : ℝ)) = x * T := by push_cast; field_simp
          rw [this, hx, div_mul_cancel₀ _ hpos.ne']
        have h4 : ((j i : ℝ) + 1) * (T / ((2 ^ i : ℕ) : ℝ)) ≥ t - a := by
          rw [← h3]
          exact mul_le_mul_of_nonneg_right h1.le (by have := hpow i; positivity)
        nlinarith
      simp only [htt]; linarith
    have hT0 : Tendsto (fun i : ℕ => T / ((2 ^ i : ℕ) : ℝ)) atTop (𝓝 0) := by
      have : Tendsto (fun i : ℕ => T * ((1 / 2 : ℝ) ^ i)) atTop (𝓝 (T * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul T
      rw [mul_zero] at this
      refine this.congr fun i => ?_
      push_cast
      rw [one_div, inv_pow, div_eq_mul_inv]
    have htt_t : Tendsto tt atTop (𝓝 t) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hup hlow
      simpa using (tendsto_const_nhds (x := t)).sub hT0
    have hmem : ∀ i, tt i ∈ Set.Icc a (a + T) := by
      intro i
      refine ⟨?_, (hlow i).trans ht.2⟩
      simp only [htt]
      have := hpow i
      have : 0 ≤ (j i : ℝ) * (T / ((2 ^ i : ℕ) : ℝ)) := by positivity
      linarith
    have hcts : Tendsto (fun i => f (tt i)) atTop (𝓝 (f t)) :=
      (hf t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨htt_t, Filter.Eventually.of_forall hmem⟩)
    have hcts2 : Tendsto (fun i => ENNReal.ofReal ((f (tt i) - f a) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((f t - f a) ^ 2))) :=
      ENNReal.tendsto_ofReal (((hcts.sub_const (f a))).pow 2)
    refine le_of_tendsto' hcts2 fun i => ?_
    refine le_trans ?_ (le_iSup (fun i : ℕ => smGrid (fun s => ENNReal.ofReal ((f s - f a) ^ 2)) a T (2 ^ i)) i)
    unfold smGrid
    exact le_iSup (fun j' : Fin ((2 ^ i : ℕ) + 1) => ENNReal.ofReal ((f (a + (j' : ℕ) *
      (T / ((2 ^ i : ℕ) : ℝ))) - f a) ^ 2)) ⟨j i, Nat.lt_succ_of_le (hjle i)⟩

end EQLZSm

end MD

end HRS

end
