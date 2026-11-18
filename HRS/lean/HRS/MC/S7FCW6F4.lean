import HRS.Stochastic.BDG

/-!
# FC-F4: Doob's `L^q` maximal inequality for a.s. continuous martingales (real `q > 1`)

Packet prefix `s7fcw6_`.  Route: layer-cake for the truncated maximum (`s7fcw6_layer`), Hoelder
(`s7fcw6_core`), discrete grid version (`s7fcw6_discrete`), then dyadic grids and a.s. continuity
(`s7fcw6_doob_cont`), generalising `doob_four_cont` (`HRS/Stochastic/BDG.lean`) from `q = 4` to real `q > 1`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.S7FCW6

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Layer-cake form of the weak-type bound: `E Y^q ≤ (q/(q-1)) E[F Y^(q-1)]`. -/
theorem s7fcw6_layer {μ : Measure Ω} {Y F : Ω → ℝ} {q : ℝ} (hq : 1 < q)
    (hY : Measurable Y) (hF : Measurable F) (hY0 : 0 ≤ Y)
    (hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {ω | t ≤ Y ω} ≤
      ∫⁻ ω in {ω | t ≤ Y ω}, ENNReal.ofReal (F ω) ∂μ) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ ≤
      ENNReal.ofReal (q / (q - 1)) *
        ∫⁻ ω, ENNReal.ofReal (F ω) * ENNReal.ofReal (Y ω ^ (q - 1)) ∂μ := by
  have hq0 : (0 : ℝ) < q := by linarith
  have h1 := lintegral_rpow_eq_lintegral_meas_le_mul μ (Eventually.of_forall hY0) hY.aemeasurable hq0
  set ν : Measure Ω := μ.withDensity (fun ω => ENNReal.ofReal (F ω)) with hν
  have h2 : ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t ≤ Y a} * ENNReal.ofReal (t ^ (q - 1)) ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ν {a | t ≤ Y a} * ENNReal.ofReal (t ^ (q - 2)) := by
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    have hmeas : MeasurableSet {a | t ≤ Y a} := measurableSet_le measurable_const hY
    have hsplit : ENNReal.ofReal (t ^ (q - 1)) = ENNReal.ofReal t * ENNReal.ofReal (t ^ (q - 2)) := by
      rw [← ENNReal.ofReal_mul ht'.le]
      congr 1
      rw [show q - 1 = 1 + (q - 2) by ring, Real.rpow_add ht', Real.rpow_one]
    calc μ {a | t ≤ Y a} * ENNReal.ofReal (t ^ (q - 1))
        = (ENNReal.ofReal t * μ {a | t ≤ Y a}) * ENNReal.ofReal (t ^ (q - 2)) := by
          rw [hsplit]; ring
      _ ≤ ν {a | t ≤ Y a} * ENNReal.ofReal (t ^ (q - 2)) := by
          gcongr
          rw [hν, withDensity_apply _ hmeas]
          exact hweak t ht'
  have h3 : ∫⁻ t in Set.Ioi (0 : ℝ), ν {a | t ≤ Y a} * ENNReal.ofReal (t ^ (q - 2)) =
      ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..Y ω, t ^ (q - 2)) ∂ν := by
    refine (lintegral_comp_eq_lintegral_meas_le_mul ν (g := fun t : ℝ => t ^ (q - 2))
      (Eventually.of_forall hY0) hY.aemeasurable (fun t _ => intervalIntegral.intervalIntegrable_rpow' (by linarith)) ?_).symm
    exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht => Real.rpow_nonneg (le_of_lt ht) _
  have hint : ∀ ω, ∫ t in (0 : ℝ)..Y ω, t ^ (q - 2) = Y ω ^ (q - 1) / (q - 1) := by
    intro ω
    rw [integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith : q - 2 + 1 ≠ 0),
      show q - 2 + 1 = q - 1 by ring, sub_zero]
  have hmeasY : Measurable fun ω => ENNReal.ofReal (Y ω ^ (q - 1)) :=
    ((hY.pow_const (q - 1))).ennreal_ofReal
  have h5 : ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..Y ω, t ^ (q - 2)) ∂ν =
      ENNReal.ofReal (1 / (q - 1)) *
        ∫⁻ ω, ENNReal.ofReal (F ω) * ENNReal.ofReal (Y ω ^ (q - 1)) ∂μ := by
    simp only [hint]
    rw [hν, lintegral_withDensity_eq_lintegral_mul _ hF.ennreal_ofReal
      ((hY.pow_const (q - 1)).div_const (q - 1)).ennreal_ofReal]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ω => ?_
    simp only [Pi.mul_apply]
    have hq1 : (0 : ℝ) ≤ 1 / (q - 1) := by apply div_nonneg <;> linarith
    rw [show Y ω ^ (q - 1) / (q - 1) = (1 / (q - 1)) * Y ω ^ (q - 1) by ring,
      ENNReal.ofReal_mul hq1]
    ring
  calc ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ = ENNReal.ofReal q * ∫⁻ t in Set.Ioi (0 : ℝ),
        μ {a | t ≤ Y a} * ENNReal.ofReal (t ^ (q - 1)) := by
          rw [h1]
    _ ≤ ENNReal.ofReal q * ∫⁻ t in Set.Ioi (0 : ℝ), ν {a | t ≤ Y a} * ENNReal.ofReal (t ^ (q - 2)) :=
          by gcongr
    _ = ENNReal.ofReal q * ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..Y ω, t ^ (q - 2)) ∂ν := by rw [h3]
    _ = ENNReal.ofReal q * (ENNReal.ofReal (1 / (q - 1)) *
          ∫⁻ ω, ENNReal.ofReal (F ω) * ENNReal.ofReal (Y ω ^ (q - 1)) ∂μ) := by rw [h5]
    _ = ENNReal.ofReal (q / (q - 1)) *
          ∫⁻ ω, ENNReal.ofReal (F ω) * ENNReal.ofReal (Y ω ^ (q - 1)) ∂μ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hq0.le,
            show q * (1 / (q - 1)) = q / (q - 1) by ring]

/-- Hoelder step: `E Y^q ≤ (q/(q-1))^q E F^q` once `E Y^q < ∞`. -/
theorem s7fcw6_core {μ : Measure Ω} {Y F : Ω → ℝ} {q : ℝ} (hq : 1 < q)
    (hY : Measurable Y) (hF : Measurable F) (hY0 : 0 ≤ Y) (hF0 : 0 ≤ F)
    (hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {ω | t ≤ Y ω} ≤
      ∫⁻ ω in {ω | t ≤ Y ω}, ENNReal.ofReal (F ω) ∂μ)
    (hA : ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ ≤
      ENNReal.ofReal ((q / (q - 1)) ^ q) * ∫⁻ ω, ENNReal.ofReal (F ω ^ q) ∂μ := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  have hqne : q ≠ 0 := hq0.ne'
  have hpq : q.HolderConjugate (q / (q - 1)) := (Real.holderConjugate_iff_eq_conjExponent hq).2 rfl
  have hp'0 : (0 : ℝ) < q / (q - 1) := div_pos hq0 hq1
  have hsum : 1 / q + 1 / (q / (q - 1)) = 1 := by
    field_simp
    ring
  have hf_eq : ∀ ω, ENNReal.ofReal (F ω) ^ q = ENNReal.ofReal (F ω ^ q) := fun ω =>
    ENNReal.ofReal_rpow_of_nonneg (hF0 ω) hq0.le
  have hg_eq : ∀ ω, (ENNReal.ofReal (Y ω ^ (q - 1))) ^ (q / (q - 1)) = ENNReal.ofReal (Y ω ^ q) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hY0 ω) _) hp'0.le, ← Real.rpow_mul (hY0 ω)]
    congr 2
    field_simp
  have hD := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (f := fun ω => ENNReal.ofReal (F ω)) (g := fun ω => ENNReal.ofReal (Y ω ^ (q - 1)))
    hF.ennreal_ofReal.aemeasurable (((hY.pow_const (q - 1))).ennreal_ofReal).aemeasurable
  simp only [Pi.mul_apply, hf_eq, hg_eq] at hD
  have hL := s7fcw6_layer hq hY hF hY0 hweak
  set A := ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ with hAdef
  set B := ∫⁻ ω, ENNReal.ofReal (F ω ^ q) ∂μ with hBdef
  set p' := q / (q - 1) with hp'
  have hmain : A ≤ ENNReal.ofReal (q / (q - 1)) * B ^ (1 / q) * A ^ (1 / p') := by
    calc A ≤ ENNReal.ofReal (q / (q - 1)) *
          (∫⁻ ω, ENNReal.ofReal (F ω) * ENNReal.ofReal (Y ω ^ (q - 1)) ∂μ) := hL
      _ ≤ ENNReal.ofReal (q / (q - 1)) * (B ^ (1 / q) * A ^ (1 / p')) := by gcongr
      _ = _ := by ring
  rcases eq_or_ne A 0 with hA0 | hA0
  · rw [hA0]; exact zero_le
  have hsplit : A = A ^ (1 / q) * A ^ (1 / p') := by
    rw [← ENNReal.rpow_add _ _ hA0 hA, hsum, ENNReal.rpow_one]
  have hne0 : A ^ (1 / p') ≠ 0 := (ENNReal.rpow_pos (pos_of_ne_zero hA0) hA).ne'
  have hnetop : A ^ (1 / p') ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hA
  have hcancel : A ^ (1 / q) ≤ ENNReal.ofReal (q / (q - 1)) * B ^ (1 / q) := by
    have h' : A ^ (1 / p') * A ^ (1 / q) ≤
        A ^ (1 / p') * (ENNReal.ofReal (q / (q - 1)) * B ^ (1 / q)) := by
      calc A ^ (1 / p') * A ^ (1 / q) = A ^ (1 / q) * A ^ (1 / p') := mul_comm _ _
        _ = A := hsplit.symm
        _ ≤ ENNReal.ofReal (q / (q - 1)) * B ^ (1 / q) * A ^ (1 / p') := hmain
        _ = A ^ (1 / p') * (ENNReal.ofReal (q / (q - 1)) * B ^ (1 / q)) := by ring
    exact (ENNReal.mul_le_mul_iff_right hne0 hnetop).1 h'
  have hpow : ∀ x : ENNReal, (x ^ (1 / q)) ^ q = x := fun x => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hqne, ENNReal.rpow_one]
  have h1 := ENNReal.rpow_le_rpow hcancel hq0.le
  rw [hpow, ENNReal.mul_rpow_of_nonneg _ _ hq0.le, hpow,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le] at h1
  exact h1

/-- Doob's `L^q` maximal inequality for a non-negative submartingale on `{0, …, N}`. -/
theorem s7fcw6_discrete {μ : Measure Ω} [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ mΩ}
    {f : ℕ → Ω → ℝ} (hsub : Submartingale f 𝒢 μ) (hnn : 0 ≤ f) {q : ℝ} (hq : 1 < q) (N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((range (N + 1)).sup' nonempty_range_add_one fun k => f k ω) ^ q) ∂μ ≤
      ENNReal.ofReal ((q / (q - 1)) ^ q) * ∫⁻ ω, ENNReal.ofReal (f N ω ^ q) ∂μ := by
  have hq0 : (0 : ℝ) < q := by linarith
  set X : Ω → ℝ := fun ω => (range (N + 1)).sup' nonempty_range_add_one fun k => f k ω with hX
  have hfm : ∀ k, Measurable (f k) := fun k => (hsub.stronglyMeasurable k).measurable.le (𝒢.le k)
  have hXm : Measurable X := measurable_range_sup'' fun n _ => hfm n
  have hX0 : 0 ≤ X := fun ω => le_trans (hnn 0 ω) (le_sup' (fun k => f k ω) (by simp))
  have key : ∀ c : ℕ, ∫⁻ ω, ENNReal.ofReal (min (X ω) c ^ q) ∂μ ≤
      ENNReal.ofReal ((q / (q - 1)) ^ q) * ∫⁻ ω, ENNReal.ofReal (f N ω ^ q) ∂μ := by
    intro c
    set Y : Ω → ℝ := fun ω => min (X ω) c with hY
    have hYm : Measurable Y := hXm.min measurable_const
    have hY0 : 0 ≤ Y := fun ω => le_min (hX0 ω) (Nat.cast_nonneg c)
    have hYc : ∀ ω, Y ω ≤ c := fun ω => min_le_right _ _
    have hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {ω | t ≤ Y ω} ≤
        ∫⁻ ω in {ω | t ≤ Y ω}, ENNReal.ofReal (f N ω) ∂μ := by
      intro t ht
      by_cases htc : t ≤ c
      · have hset : {ω | t ≤ Y ω} = {ω | t ≤ X ω} := by
          ext ω; simp [hY, htc]
        rw [hset]
        have := maximal_ineq hsub hnn (ε := t.toNNReal) N
        have hcoe : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.le
        simp only [hcoe] at this
        rw [show ENNReal.ofReal t = ((t.toNNReal : ℝ≥0) : ℝ≥0∞) from rfl]
        refine this.trans (le_of_eq ?_)
        rw [ofReal_integral_eq_lintegral_ofReal]
        · exact (hsub.integrable N).integrableOn
        · exact Eventually.of_forall (hnn N)
      · push Not at htc
        have : {ω | t ≤ Y ω} = ∅ := by
          ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
          exact lt_of_le_of_lt (hYc ω) htc
        rw [this]; simp
    have hfin : ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ENNReal.ofReal ((c : ℝ) ^ q)) ENNReal.ofReal_ne_top ?_
      calc ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ ≤ ∫⁻ _ω, ENNReal.ofReal ((c : ℝ) ^ q) ∂μ :=
            lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
              (Real.rpow_le_rpow (hY0 ω) (hYc ω) hq0.le)
        _ = _ := by simp
    exact s7fcw6_core hq hYm (hfm N) hY0 (hnn N) hweak hfin
  have hmono : Monotone fun (c : ℕ) ω => ENNReal.ofReal (min (X ω) c ^ q) := by
    intro c d hcd ω
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (le_min (hX0 ω) (Nat.cast_nonneg c)) ?_ hq0.le)
    exact min_le_min le_rfl (by exact_mod_cast hcd)
  have hsup : ∀ ω, ENNReal.ofReal (X ω ^ q) = ⨆ c : ℕ, ENNReal.ofReal (min (X ω) c ^ q) := by
    intro ω
    refine le_antisymm ?_ (iSup_le fun c => ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (le_min (hX0 ω) (Nat.cast_nonneg c)) (min_le_left _ _) hq0.le))
    obtain ⟨c, hc⟩ := exists_nat_ge (X ω)
    exact le_iSup_of_le c (by rw [min_eq_left hc])
  calc ∫⁻ ω, ENNReal.ofReal (X ω ^ q) ∂μ
      = ∫⁻ ω, ⨆ c : ℕ, ENNReal.ofReal (min (X ω) c ^ q) ∂μ := lintegral_congr hsup
    _ = ⨆ c : ℕ, ∫⁻ ω, ENNReal.ofReal (min (X ω) c ^ q) ∂μ := by
        refine lintegral_iSup (fun c => ?_) hmono
        exact ((hXm.min measurable_const).pow_const q).ennreal_ofReal
    _ ≤ _ := iSup_le key

/-- Doob's `L^q` maximal inequality for an a.s. continuous martingale (`q > 1` real). -/
theorem s7fcw6_doob_cont {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} (hM : Martingale M ℱ μ) (hc : ∀ᵐ ω ∂μ, Continuous fun t => M t ω)
    {q : ℝ} (hq : 1 < q) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ q ∂μ ≤
      ENNReal.ofReal ((q / (q - 1)) ^ q) * ∫⁻ ω, ‖M T ω‖ₑ ^ q ∂μ := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hqne : q ≠ 0 := hq0.ne'
  have hpow : ∀ x : ENNReal, (x ^ q) ^ (1 / q) = x := fun x => by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hqne, ENNReal.rpow_one]
  have hpow' : ∀ x : ENNReal, (x ^ (1 / q)) ^ q = x := fun x => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hqne, ENNReal.rpow_one]
  -- the dyadic grids
  let τ : ℕ → ℕ → ℝ := fun n k => T * k / 2 ^ n
  have hτmono : ∀ n, Monotone (τ n) := fun n i j hij => by
    simp only [τ]; gcongr
  let 𝒢 : ℕ → Filtration ℕ mΩ := fun n =>
    ⟨fun k => ℱ (τ n k), fun i j hij => ℱ.mono (hτmono n hij), fun k => ℱ.le _⟩
  let F : ℕ → ℕ → Ω → ℝ := fun n k ω => ‖M (τ n k) ω‖
  have hsub : ∀ n, Submartingale (F n) (𝒢 n) μ := by
    intro n
    refine ⟨fun k => ((hM.stronglyMeasurable _).norm : _), fun i j hij => ?_, fun k => (hM.integrable _).norm⟩
    have h1 := norm_condExp_le (μ := μ) (m := ℱ (τ n i)) (M (τ n j))
    have h2 := hM.condExp_ae_eq (hτmono n hij)
    filter_upwards [h1, h2] with ω hω1 hω2
    simp only [F]
    rw [← hω2]
    exact hω1
  have hnn : ∀ n, 0 ≤ F n := fun n k ω => norm_nonneg _
  have hdoob := fun n => s7fcw6_discrete (hsub n) (hnn n) hq (2 ^ n)
  let g : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal
    (((Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one fun k => F n k ω) ^ q)
  have hFm : ∀ n k, Measurable (F n k) := fun n k =>
    ((hM.stronglyMeasurable (τ n k)).measurable.le (ℱ.le _)).norm
  have hgm : ∀ n, Measurable (g n) := fun n =>
    ((Finset.measurable_range_sup'' fun k _ => hFm n k).pow_const q).ennreal_ofReal
  have hgle : ∀ n, ∫⁻ ω, g n ω ∂μ ≤ ENNReal.ofReal ((q / (q - 1)) ^ q) * ∫⁻ ω, ‖M T ω‖ₑ ^ q ∂μ := by
    intro n
    refine (hdoob n).trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun ω => ?_
    have : τ n (2 ^ n) = T := by simp only [τ]; push_cast; field_simp
    simp only [F, this]
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le]
  -- pointwise bound along grids (for continuous paths)
  have hpt : ∀ ω, Continuous (fun t => M t ω) → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖M t ω‖ₑ ^ q ≤ liminf (fun n => g n ω) atTop := by
    intro ω hcont t ht
    obtain ⟨k, hk0, hkle, hkT⟩ : ∃ k : ℕ → ℕ, (∀ n, k n ≤ 2 ^ n) ∧ (∀ n, τ n (k n) ≤ t) ∧
        Tendsto (fun n => τ n (k n)) atTop (𝓝 t) := by
      rcases hT.eq_or_lt with h0 | hpos
      · subst h0
        have ht0 : t = 0 := le_antisymm ht.2 ht.1
        subst ht0
        refine ⟨fun _ => 0, fun n => Nat.zero_le _, fun n => by simp [τ], ?_⟩
        simp [τ]
      · exact HRS.exists_dyadic_grid hpos ht
    have hk : Tendsto (fun n => ‖M (τ n (k n)) ω‖ₑ ^ q) atTop (𝓝 (‖M t ω‖ₑ ^ q)) :=
      ((ENNReal.continuous_rpow_const (y := q)).tendsto _).comp
        ((continuous_enorm.tendsto _).comp ((hcont.tendsto t).comp hkT))
    rw [← hk.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    simp only [g]
    have hle : ‖M (τ n (k n)) ω‖ ≤ (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
        fun j => F n j ω :=
      Finset.le_sup' (fun j => F n j ω) (Finset.mem_range.2 (Nat.lt_succ_of_le (hk0 n)))
    calc ‖M (τ n (k n)) ω‖ₑ ^ q = ENNReal.ofReal (‖M (τ n (k n)) ω‖ ^ q) := by
          rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le, ofReal_norm]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) hle hq0.le)
  -- pointwise bound for the supremum
  have hsupb : ∀ ω, Continuous (fun t => M t ω) →
      (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ q ≤ liminf (fun n => g n ω) atTop := by
    intro ω hcont
    have hL : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ ≤ (liminf (fun n => g n ω) atTop) ^ (1 / q) := by
      intro t ht
      calc ‖M t ω‖ₑ = (‖M t ω‖ₑ ^ q) ^ (1 / q) := (hpow _).symm
        _ ≤ _ := ENNReal.rpow_le_rpow (hpt ω hcont t ht) (by positivity)
    have hs : (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ≤ (liminf (fun n => g n ω) atTop) ^ (1 / q) :=
      iSup₂_le hL
    calc (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ q ≤ ((liminf (fun n => g n ω) atTop) ^ (1 / q)) ^ q :=
          ENNReal.rpow_le_rpow hs hq0.le
      _ = _ := hpow' _
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ q ∂μ
      ≤ ∫⁻ ω, liminf (fun n => g n ω) atTop ∂μ := lintegral_mono_ae (hc.mono fun ω hω => hsupb ω hω)
    _ ≤ liminf (fun n => ∫⁻ ω, g n ω ∂μ) atTop := lintegral_liminf_le hgm
    _ ≤ _ := by
        refine (liminf_le_limsup).trans (limsup_le_of_le (by isBoundedDefault) ?_)
        exact Eventually.of_forall hgle

/-- **F4 (Doob's `L^q` maximal inequality for a.s. continuous martingales, real `q > 1`)**. -/
theorem s7_FC_F4_doob_Lq_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (M : ℝ → Ω → ℝ) (hM : Martingale M ℱ P)
    (hc : ∀ᵐ ω ∂P, Continuous fun t => M t ω) (q : ℝ) (hq : 1 < q) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ q ∂P ≤
      ENNReal.ofReal ((q / (q - 1)) ^ q) * ∫⁻ ω, ‖M T ω‖ₑ ^ q ∂P :=
  s7fcw6_doob_cont hM hc hq hT

end HRS.MC.Sec7.S7FCW6

end
