import HRS.Uniform.Q48dAux4

/-!
# Q48d, part 5: window pieces and the history estimate (infrastructure for Lemma 3.31)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Uniform.Q48d

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

lemma enorm_apply_le (L : E →L[ℝ] E) {c : ℝ} (hc : 0 ≤ c) (hL : ‖L‖ ≤ c) (z : E) :
    ‖L z‖ₑ ≤ ENNReal.ofReal c * ‖z‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal ((L.le_opNorm z).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _)))

/-- A window piece: the convolution on `[a, a+T]` of the process stopped at `S`, its maximal estimate. -/
lemma window_piece {V : ℝ → ℝ → E →L[ℝ] E} {T C : ℝ} (hC0 : 0 ≤ C) (hWT : WinMaxU.{u} V T C)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (D : ℝ → Ω → E) (Sd : ℝ → Ω → (E →L[ℝ] E →L[ℝ] ℝ))
    (hD : ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S (fun τ ω => D (min τ S) ω)
      (fun r ω => if r ≤ S then Sd r ω else 0))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ r : ℝ, 0 ≤ r → ∫⁻ ω, ENNReal.ofReal (traceNormForm (Sd r ω)) ∂P ≤ ENNReal.ofReal K)
    {a S : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (haS : a ≤ S) (hSa : S ≤ a + T) :
    ∃ W : ℝ → Ω → E, (∀ t ∈ Icc a S, IsStochConv P V (ContinuousLinearMap.id ℝ E) D a t (W t)) ∧
      (∀ t ∈ Icc a (a + T), AEStronglyMeasurable (W t) P) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) (Icc a (a + T))) ∧
      ∫⁻ ω, (⨆ t ∈ Icc a (a + T), ‖W t ω‖ₑ) ^ 2 ∂P ≤ ENNReal.ofReal (C * (K * T)) := by
  have hS0 : 0 ≤ S := ha.trans haS
  have hh := isHMC_extend hS0 hSa (hD S hS0)
  obtain ⟨W, h1, h2, h3, h4⟩ := hWT Ω P ℱ a ha _ _ hh
  refine ⟨W, fun t ht => (isStochConv_stop_iff ht.2).1 (h1 t ⟨ht.1, ht.2.trans hSa⟩), h2, h3, ?_⟩
  refine h4.trans ?_
  rw [ENNReal.ofReal_mul hC0]
  exact mul_le_mul' le_rfl (window_rhs_le hh hK0 hK ha hT)

/-- The block variable `∫_a^S V(S,u) dD_u` with its `L²` bound. -/
lemma block_piece {V : ℝ → ℝ → E →L[ℝ] E} {T C : ℝ} (hC0 : 0 ≤ C) (hWT : WinMaxU.{u} V T C)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (D : ℝ → Ω → E) (Sd : ℝ → Ω → (E →L[ℝ] E →L[ℝ] ℝ))
    (hD : ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S (fun τ ω => D (min τ S) ω)
      (fun r ω => if r ≤ S then Sd r ω else 0))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ r : ℝ, 0 ≤ r → ∫⁻ ω, ENNReal.ofReal (traceNormForm (Sd r ω)) ∂P ≤ ENNReal.ofReal K)
    {a S : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (haS : a ≤ S) (hSa : S ≤ a + T) :
    ∃ Y : Ω → E, AEStronglyMeasurable Y P ∧
      IsStochConv P V (ContinuousLinearMap.id ℝ E) D a S Y ∧
      eLpNorm Y 2 P ≤ ENNReal.ofReal (Real.sqrt (C * (K * T))) := by
  obtain ⟨W, h1, h2, h3, h4⟩ := window_piece hC0 hWT P ℱ D Sd hD hK0 hK ha hT haS hSa
  have hSm : S ∈ Icc a (a + T) := ⟨haS, hSa⟩
  refine ⟨W S, h2 S hSm, h1 S ⟨haS, le_rfl⟩, ?_⟩
  rw [eLpNorm_two_eq (h2 S hSm)]
  have hle : ∫⁻ ω, ‖W S ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (C * (K * T)) := by
    refine le_trans (lintegral_mono fun ω => ?_) h4
    gcongr
    exact le_iSup₂ (f := fun t (_ : t ∈ Icc a (a + T)) => ‖W t ω‖ₑ) S hSm
  calc (∫⁻ ω, ‖W S ω‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (C * (K * T))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hle (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (C * (K * T))) := by
        rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]

/-- The history estimate: `‖Z_a‖_{L²} ≤ C K^{1/2}` uniformly in `a ≥ 0`, by unit blocks and exponential decay. -/
theorem history_bound {V : ℝ → ℝ → E →L[ℝ] E} (hV : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution V T)
    {C₀ c : ℝ} (hC0 : 0 ≤ C₀) (hc : 0 < c)
    (hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖V t u‖ ≤ C₀ * Real.exp (-c * (t - u)))
    {C₁ : ℝ} (hC1 : 0 ≤ C₁) (h1 : WinMaxU.{u} V 1 C₁)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (D : ℝ → Ω → E) (Sd : ℝ → Ω → (E →L[ℝ] E →L[ℝ] ℝ))
    (hD : ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S (fun τ ω => D (min τ S) ω)
      (fun r ω => if r ≤ S then Sd r ω else 0))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ r : ℝ, 0 ≤ r → ∫⁻ ω, ENNReal.ofReal (traceNormForm (Sd r ω)) ∂P ≤ ENNReal.ofReal K)
    (Z : ℝ → Ω → E) (hZ : ∀ t : ℝ, 0 ≤ t → IsStochConv P V (ContinuousLinearMap.id ℝ E) D 0 t (Z t))
    (hZm : ∀ t : ℝ, 0 ≤ t → AEStronglyMeasurable (Z t) P) {a : ℝ} (ha : 0 ≤ a) :
    eLpNorm (Z a) 2 P ≤ ENNReal.ofReal
      (C₀ * (1 / (1 - Real.exp (-c / 2))) * Real.sqrt (C₁ * (K * 1))) := by
  classical
  have hDm : ∀ τ : ℝ, 0 ≤ τ → AEStronglyMeasurable (D τ) P := by
    intro τ hτ
    have := (hD τ hτ).sq_int τ ⟨hτ, le_rfl⟩
    simpa using this.aestronglyMeasurable
  set n : ℕ := ⌈a⌉₊ with hn
  set h : ℝ := a / n with hh
  set b : ℕ → ℝ := fun l => a - l * h with hb
  have hna : a ≤ n := Nat.le_ceil a
  have hnh : (n : ℝ) * h = a := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have : a ≤ 0 := Nat.ceil_eq_zero.1 h0
      have : a = 0 := le_antisymm this ha
      simp [h0, this]
    · have : (n : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
      rw [hh]; field_simp
  have hh0 : 0 ≤ h := div_nonneg ha (Nat.cast_nonneg _)
  have hh1 : h ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [hh, h0]
    · have : (0 : ℝ) < n := by exact_mod_cast h0
      rw [hh, div_le_one this]; exact hna
  have hbn : b n = 0 := by simp only [hb]; rw [hnh]; ring
  have hb0 : ∀ l, l ≤ n → 0 ≤ b l := by
    intro l hl
    simp only [hb]
    have : (l : ℝ) * h ≤ n * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hh0
    linarith
  have hba : ∀ l, b l ≤ a := fun l => by simp only [hb]; nlinarith [mul_nonneg (Nat.cast_nonneg l : (0:ℝ) ≤ l) hh0]
  have hbs : ∀ l, b (l + 1) = b l - h := fun l => by simp only [hb]; push_cast; ring
  have hbm : ∀ l, b (l + 1) ≤ b l := fun l => by rw [hbs]; linarith
  have hb00 : b 0 = a := by simp [hb]
  -- the decay of the distance
  have hdist : ∀ l, l < n → (l : ℝ) / 2 ≤ a - b l := by
    intro l hl
    simp only [hb]
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · simp [h0]
    · have hn2 : 2 ≤ n := by omega
      have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hlt : (n : ℝ) < a + 1 := Nat.ceil_lt_add_one ha
      have hnpos : (0 : ℝ) < n := by linarith
      have : (1 : ℝ) / 2 ≤ h := by
        rw [hh, le_div_iff₀ hnpos]; linarith
      have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      nlinarith
  -- the block variables
  have hY : ∀ l : ℕ, ∃ Y : Ω → E, l < n → (AEStronglyMeasurable Y P ∧
      IsStochConv P V (ContinuousLinearMap.id ℝ E) D (b (l + 1)) (b l) Y ∧
      eLpNorm Y 2 P ≤ ENNReal.ofReal (Real.sqrt (C₁ * (K * 1)))) := by
    intro l
    by_cases hl : l < n
    · have hb1 : 0 ≤ b (l + 1) := hb0 _ (by omega)
      obtain ⟨Y, hY1, hY2, hY3⟩ := block_piece hC1 h1 P ℱ D Sd hD hK0 hK hb1 zero_le_one (hbm l)
        (by rw [hbs]; linarith)
      exact ⟨Y, fun _ => ⟨hY1, hY2, hY3⟩⟩
    · exact ⟨0, fun h' => absurd h' hl⟩
  choose Y hY using hY
  -- the one-step relation
  have hstep : ∀ l, l < n → (Z (b l)) =ᵐ[P] fun ω => V (b l) (b (l + 1)) (Z (b (l + 1)) ω) + Y l ω := by
    intro l hl
    obtain ⟨hYm, hYc, -⟩ := hY l hl
    have hb1 : 0 ≤ b (l + 1) := hb0 _ (by omega)
    have hbl : 0 ≤ b l := hb1.trans (hbm l)
    have hDt : ∀ τ ∈ Icc (0 : ℝ) (b l), AEStronglyMeasurable (D τ) P := fun τ hτ => hDm τ hτ.1
    have hDs : ∀ τ ∈ Icc (b (l + 1)) (b l), AEStronglyMeasurable (D τ) P :=
      fun τ hτ => hDm τ (hb1.trans hτ.1)
    have hDa : ∀ τ ∈ Icc (0 : ℝ) (b (l + 1)), AEStronglyMeasurable (D τ) P :=
      fun τ hτ => hDm τ hτ.1
    refine sc_concat hb1 (hbm l) hDt (fun r hr0 hra => ?_) (hZm _ hbl) (hZm _ hb1) hYm
      ((isStochConv_iff (hZm _ hbl) hDt).1 (hZ _ hbl)) ((isStochConv_iff (hZm _ hb1) hDa).1 (hZ _ hb1))
      ((isStochConv_iff hYm hDs).1 hYc)
    exact (hV (b l) hbl).2.1 r (b (l + 1)) (b l) hr0 hra (hbm l) le_rfl
  -- unwinding
  have hunwind : ∀ k, k ≤ n → (Z a) =ᵐ[P] fun ω =>
      ∑ l ∈ Finset.range k, V a (b l) (Y l ω) + V a (b k) (Z (b k) ω) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hself := (hV a ha).1 a ⟨ha, le_rfl⟩
      refine Eventually.of_forall fun ω => ?_
      simp [hb00, hself]
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hb1 : 0 ≤ b (k + 1) := hb0 _ hk
      have hcoc : (V a (b k)).comp (V (b k) (b (k + 1))) = V a (b (k + 1)) :=
        (hV a ha).2.1 (b (k + 1)) (b k) a hb1 (hbm k) (hba k) le_rfl
      filter_upwards [ih hkn.le, hstep k hkn] with ω h1 h2
      rw [h1, h2, map_add, Finset.sum_range_succ]
      have := congrArg (fun F : E →L[ℝ] E => F (Z (b (k + 1)) ω)) hcoc
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [this]
      abel
  -- the history is the sum of the blocks
  have hZ0 : Z 0 =ᵐ[P] 0 := by
    have hDt : ∀ τ ∈ Icc (0 : ℝ) 0, AEStronglyMeasurable (D τ) P := fun τ hτ => hDm τ hτ.1
    exact sc_unique le_rfl hDt (hZm 0 le_rfl) aestronglyMeasurable_zero
      ((isStochConv_iff (hZm 0 le_rfl) hDt).1 (hZ 0 le_rfl)) sc_zero_interval
  have hsum : (Z a) =ᵐ[P] fun ω => ∑ l ∈ Finset.range n, V a (b l) (Y l ω) := by
    filter_upwards [hunwind n le_rfl, hZ0] with ω h1 h2
    rw [h1, hbn]
    simp [h2]
  -- the norm
  set q : ℝ := Real.exp (-c / 2) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have hterm : ∀ l, l < n → eLpNorm (fun ω => V a (b l) (Y l ω)) 2 P ≤
      ENNReal.ofReal (C₀ * q ^ l * Real.sqrt (C₁ * (K * 1))) := by
    intro l hl
    obtain ⟨hYm, -, hYn⟩ := hY l hl
    have hbl0 := hb0 l hl.le
    have hVn : ‖V a (b l)‖ ≤ C₀ * q ^ l := by
      refine (hdec (b l) a hbl0 (hba l)).trans ?_
      have : Real.exp (-c * (a - b l)) ≤ q ^ l := by
        rw [hq, ← Real.exp_nat_mul]
        refine Real.exp_le_exp.2 ?_
        have := hdist l hl
        nlinarith
      exact mul_le_mul_of_nonneg_left this hC0
    have hVn0 : 0 ≤ C₀ * q ^ l := by positivity
    calc eLpNorm (fun ω => V a (b l) (Y l ω)) 2 P
        ≤ ENNReal.ofReal (C₀ * q ^ l) * eLpNorm (Y l) 2 P :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul
            ((V a (b l)).continuous.comp_aestronglyMeasurable hYm)
            (Eventually.of_forall fun ω => ((V a (b l)).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right hVn (norm_nonneg _))) 2
      _ ≤ ENNReal.ofReal (C₀ * q ^ l) * ENNReal.ofReal (Real.sqrt (C₁ * (K * 1))) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul hVn0]
  have hgeom : ∑ l ∈ Finset.range n, C₀ * q ^ l * Real.sqrt (C₁ * (K * 1)) ≤
      C₀ * (1 / (1 - q)) * Real.sqrt (C₁ * (K * 1)) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC0) (Real.sqrt_nonneg _)
    have hs : Summable fun l : ℕ => q ^ l := summable_geometric_of_lt_one hq0.le hq1
    calc ∑ l ∈ Finset.range n, q ^ l ≤ ∑' l, q ^ l :=
          hs.sum_le_tsum _ fun l _ => by positivity
      _ = 1 / (1 - q) := by rw [tsum_geometric_of_lt_one hq0.le hq1, one_div]
  calc eLpNorm (Z a) 2 P = eLpNorm (fun ω => ∑ l ∈ Finset.range n, V a (b l) (Y l ω)) 2 P :=
        eLpNorm_congr_ae hsum
    _ ≤ ∑ l ∈ Finset.range n, eLpNorm (fun ω => V a (b l) (Y l ω)) 2 P := by
        have := eLpNorm_sum_le (μ := P) (p := 2) (s := Finset.range n)
          (f := fun l ω => V a (b l) (Y l ω)) (by norm_num)
        simpa [Finset.sum_fn] using this
    _ ≤ ∑ l ∈ Finset.range n, ENNReal.ofReal (C₀ * q ^ l * Real.sqrt (C₁ * (K * 1))) :=
        Finset.sum_le_sum fun l hl => hterm l (Finset.mem_range.1 hl)
    _ = ENNReal.ofReal (∑ l ∈ Finset.range n, C₀ * q ^ l * Real.sqrt (C₁ * (K * 1))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro l _; positivity
    _ ≤ _ := ENNReal.ofReal_le_ofReal hgeom

end HRS.Uniform.Q48d
