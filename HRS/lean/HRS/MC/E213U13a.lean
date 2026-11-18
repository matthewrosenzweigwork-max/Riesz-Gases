import HRS.Prob.Gaussian
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U13

theorem lintegral_rpow_interp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → ℝ≥0∞}
    (hg : AEMeasurable g P) {q r : ℝ} (hq : 2 < q) (hqr : q < r) :
    ∫⁻ ω, g ω ^ q ∂P ≤ (∫⁻ ω, g ω ^ (2 : ℝ) ∂P) ^ ((r - q) / (r - 2)) *
      (∫⁻ ω, g ω ^ r ∂P) ^ ((q - 2) / (r - 2)) := by
  set θ : ℝ := (r - q) / (r - 2) with hθ
  have hr2 : 0 < r - 2 := by linarith
  have hθ0 : 0 < θ := div_pos (by linarith) hr2
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one hr2]; linarith
  have hne1 : 1 - θ ≠ 0 := by linarith
  have hne0 : θ ≠ 0 := hθ0.ne'
  have h1θ : 1 - θ = (q - 2) / (r - 2) := by rw [hθ]; field_simp; ring
  have hconj : (1 / θ).HolderConjugate (1 / (1 - θ)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hθ0]; linarith
    · rw [one_div, one_div, inv_inv, inv_inv]; ring
  have key : ∀ ω, g ω ^ q = g ω ^ (2 * θ) * g ω ^ (r * (1 - θ)) := by
    intro ω
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by nlinarith)]
    congr 1
    rw [hθ]; field_simp; ring
  calc ∫⁻ ω, g ω ^ q ∂P = ∫⁻ ω, (fun ω => g ω ^ (2 * θ)) ω * (fun ω => g ω ^ (r * (1 - θ))) ω ∂P :=
        lintegral_congr fun ω => key ω
    _ ≤ (∫⁻ ω, (g ω ^ (2 * θ)) ^ (1 / θ) ∂P) ^ (1 / (1 / θ)) *
        (∫⁻ ω, (g ω ^ (r * (1 - θ))) ^ (1 / (1 - θ)) ∂P) ^ (1 / (1 / (1 - θ))) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj (hg.pow_const _) (hg.pow_const _)
    _ = _ := by
        have e1 : ∫⁻ ω, (g ω ^ (2 * θ)) ^ (1 / θ) ∂P = ∫⁻ ω, g ω ^ (2 : ℝ) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [← ENNReal.rpow_mul]; congr 1; field_simp
        have e2 : ∫⁻ ω, (g ω ^ (r * (1 - θ))) ^ (1 / (1 - θ)) ∂P = ∫⁻ ω, g ω ^ r ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [← ENNReal.rpow_mul]; congr 1; field_simp
        rw [e1, e2, one_div_one_div, one_div_one_div, h1θ]


section Transfer

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The `L²`-closure of an increasing union of subspaces. -/
def Qc (K : ℕ → Submodule ℝ (Lp ℝ 2 P)) : Submodule ℝ (Lp ℝ 2 P) := (⨆ n, K n).topologicalClosure

theorem mem_Qc_iff {K : ℕ → Submodule ℝ (Lp ℝ 2 P)} (hK : Monotone K) {y : Lp ℝ 2 P} :
    y ∈ Qc K ↔ ∀ ε > 0, ∃ n, ∃ p ∈ K n, dist p y < ε := by
  unfold Qc
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨b, hb, hd⟩ := h ε hε
    have hb' : b ∈ ⨆ n, K n := hb
    rw [Submodule.mem_iSup_of_directed _ hK.directed_le] at hb'
    obtain ⟨n, hn⟩ := hb'
    exact ⟨n, b, hn, by rwa [dist_comm]⟩
  · intro h ε hε
    obtain ⟨n, p, hp, hd⟩ := h ε hε
    exact ⟨p, (le_iSup K n) hp, by rwa [dist_comm]⟩

theorem eLpNorm_sub_eq_dist (p : Lp ℝ 2 P) {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    eLpNorm ((p : Ω → ℝ) - Y) 2 P = ENNReal.ofReal (dist p (hY.toLp Y)) := by
  rw [Lp.dist_def]
  have h1 : eLpNorm ((p : Ω → ℝ) - Y) 2 P = eLpNorm ((p : Ω → ℝ) - (hY.toLp Y : Ω → ℝ)) 2 P :=
    eLpNorm_congr_ae (by filter_upwards [hY.coeFn_toLp] with ω h; simp [h])
  rw [h1, ENNReal.ofReal_toReal]
  exact ((Lp.memLp p).sub (Lp.memLp _)).eLpNorm_lt_top.ne


theorem eLpNorm_condExp_sub_le {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (p : Lp ℝ 2 P) {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) :
    eLpNorm (P[(p : Ω → ℝ) | m] - P[Y | m]) 2 P ≤ eLpNorm ((p : Ω → ℝ) - Y) 2 P := by
  have hp : Integrable (p : Ω → ℝ) P := (Lp.memLp p).integrable (by norm_num)
  have hY1 : Integrable Y P := hY.integrable (by norm_num)
  have h := condExp_sub hp hY1 m
  rw [← eLpNorm_congr_ae h]
  exact eLpNorm_condExp_le_eLpNorm _ (by norm_num)

theorem exists_condExp_mem {K : ℕ → Submodule ℝ (Lp ℝ 2 P)} [∀ n, FiniteDimensional ℝ (K n)]
    (hK : Monotone K) {m : ℕ → MeasurableSpace Ω} (hm : ∀ n, m n ≤ mΩ)
    (hmem : ∀ n k, ∀ x ∈ K n, ∃ y ∈ K k, P[(x : Ω → ℝ) | m k] =ᵐ[P] (y : Ω → ℝ))
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) (hYc : hY.toLp Y ∈ Qc K) (k : ℕ) :
    ∃ y ∈ K k, P[Y | m k] =ᵐ[P] (y : Ω → ℝ) := by
  have hE : MemLp (P[Y | m k]) 2 P := hY.condExp (by norm_num)
  have hcl : IsClosed (K k : Set (Lp ℝ 2 P)) := Submodule.closed_of_finiteDimensional (K k)
  have hmemE : hE.toLp (P[Y | m k]) ∈ K k := by
    rw [← SetLike.mem_coe, ← hcl.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, p, hp, hd⟩ := (mem_Qc_iff hK).1 hYc ε hε
    obtain ⟨y, hy, hpy⟩ := hmem n k p hp
    refine ⟨y, hy, ?_⟩
    rw [dist_comm]
    have h1 := eLpNorm_condExp_sub_le (hm k) p hY
    have h2 : eLpNorm ((y : Ω → ℝ) - (hE.toLp (P[Y | m k]) : Ω → ℝ)) 2 P =
        eLpNorm (P[(p : Ω → ℝ) | m k] - P[Y | m k]) 2 P := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [hpy, hE.coeFn_toLp] with ω h1 h2
      simp [h1, h2]
    have h3 : dist y (hE.toLp (P[Y | m k])) =
        (eLpNorm (P[(p : Ω → ℝ) | m k] - P[Y | m k]) 2 P).toReal := by
      rw [Lp.dist_def, ← h2]
    rw [h3]
    have h4 : eLpNorm ((p : Ω → ℝ) - Y) 2 P = ENNReal.ofReal (dist p (hY.toLp Y)) :=
      eLpNorm_sub_eq_dist p hY
    have h5 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h1.trans_eq h4)
    rw [ENNReal.toReal_ofReal dist_nonneg] at h5
    exact lt_of_le_of_lt h5 hd
  exact ⟨_, hmemE, hE.coeFn_toLp.symm⟩


theorem tendsto_condExp_L2 {K : ℕ → Submodule ℝ (Lp ℝ 2 P)}
    (hK : Monotone K) {m : ℕ → MeasurableSpace Ω} (hm : ∀ n, m n ≤ mΩ)
    (hself : ∀ n, ∀ x ∈ K n, ∀ k, n ≤ k → P[(x : Ω → ℝ) | m k] =ᵐ[P] (x : Ω → ℝ))
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) (hYc : hY.toLp Y ∈ Qc K) :
    Tendsto (fun k => eLpNorm (P[Y | m k] - Y) 2 P) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  have hr : (0 : ℝ) < r := by exact_mod_cast hr0
  obtain ⟨N, p, hp, hd⟩ := (mem_Qc_iff hK).1 hYc (r / 2) (by positivity)
  refine Filter.eventually_atTop.2 ⟨N, fun k hk => ?_⟩
  have hpk : P[(p : Ω → ℝ) | m k] =ᵐ[P] (p : Ω → ℝ) := hself N p hp k hk
  have hp2 : MemLp (p : Ω → ℝ) 2 P := Lp.memLp p
  have hE : MemLp (P[Y | m k]) 2 P := hY.condExp (by norm_num)
  have h1 : eLpNorm (P[Y | m k] - Y) 2 P ≤
      eLpNorm (P[Y | m k] - (p : Ω → ℝ)) 2 P + eLpNorm ((p : Ω → ℝ) - Y) 2 P := by
    have : P[Y | m k] - Y = (P[Y | m k] - (p : Ω → ℝ)) + ((p : Ω → ℝ) - Y) := by
      funext ω; simp
    rw [this]
    exact eLpNorm_add_le (by norm_num)
  have h2 : eLpNorm (P[Y | m k] - (p : Ω → ℝ)) 2 P = eLpNorm (P[(p : Ω → ℝ) | m k] - P[Y | m k]) 2 P := by
    rw [← eLpNorm_neg]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hpk] with ω h
    simp [h]
  have h3 := eLpNorm_condExp_sub_le (hm k) p hY
  have h4 : eLpNorm ((p : Ω → ℝ) - Y) 2 P = ENNReal.ofReal (dist p (hY.toLp Y)) :=
    eLpNorm_sub_eq_dist p hY
  have h5 : ENNReal.ofReal (dist p (hY.toLp Y)) ≤ ENNReal.ofReal (r / 2) :=
    ENNReal.ofReal_le_ofReal hd.le
  calc eLpNorm (P[Y | m k] - Y) 2 P ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) := by
        refine h1.trans (add_le_add ?_ ?_)
        · rw [h2]; exact h3.trans (h4.le.trans h5)
        · exact h4.le.trans h5
    _ = r := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; simp
    _ ≤ ε := hrε.le

theorem lintegral_enorm_rpow_two {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) :
    ∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P = eLpNorm f 2 P ^ (2 : ℝ) := by
  have h := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := P) (p := 2) (by norm_num) (by norm_num) hf
  simp only [ENNReal.toReal_ofNat] at h
  rw [h, ← ENNReal.rpow_mul]
  norm_num

theorem lintegral_enorm_rpow_eq {E : Type*} [NormedAddCommGroup E] {f : Ω → E}
    (hf : AEStronglyMeasurable f P) {r : ℝ} (hr : 0 < r) :
    ∫⁻ ω, ‖f ω‖ₑ ^ r ∂P = eLpNorm f (ENNReal.ofReal r) P ^ r := by
  have h := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := P) (p := ENNReal.ofReal r)
    (by simpa using hr) ENNReal.ofReal_ne_top hf
  rw [h, ENNReal.toReal_ofReal hr.le, ← ENNReal.rpow_mul]
  rw [one_div, inv_mul_cancel₀ hr.ne']
  simp


/-- **Transfer lemma.**  An element of the `L²`-closure of the finite-dimensional "polynomial spaces" `K n`
(stable under the conditional expectations `P[· | m k]`) that lies in `L^r`, `r > q ≥ 2`, is an `L^q`-limit of
polynomials. -/
theorem transfer {K : ℕ → Submodule ℝ (Lp ℝ 2 P)} [∀ n, FiniteDimensional ℝ (K n)]
    (hK : Monotone K) {m : ℕ → MeasurableSpace Ω} (hm : ∀ n, m n ≤ mΩ)
    (hmem : ∀ n k, ∀ x ∈ K n, ∃ y ∈ K k, P[(x : Ω → ℝ) | m k] =ᵐ[P] (y : Ω → ℝ))
    (hself : ∀ n, ∀ x ∈ K n, ∀ k, n ≤ k → P[(x : Ω → ℝ) | m k] =ᵐ[P] (x : Ω → ℝ))
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) (hYc : hY.toLp Y ∈ Qc K) {q r : ℝ} (hq : 2 ≤ q) (hqr : q < r)
    (hYr : MemLp Y (ENNReal.ofReal r) P) :
    ∃ y : ℕ → Lp ℝ 2 P, (∀ k, y k ∈ K k) ∧
      Tendsto (fun k => ∫⁻ ω, ‖(y k : Ω → ℝ) ω - Y ω‖ₑ ^ q ∂P) atTop (𝓝 0) := by
  choose y hyK hyE using exists_condExp_mem hK hm hmem hY hYc
  refine ⟨y, hyK, ?_⟩
  have hr0 : 0 < r := by linarith
  have hL2 := tendsto_condExp_L2 hK hm hself hY hYc
  have hcongr : ∀ k, ∫⁻ ω, ‖(y k : Ω → ℝ) ω - Y ω‖ₑ ^ q ∂P = ∫⁻ ω, ‖P[Y | m k] ω - Y ω‖ₑ ^ q ∂P := by
    intro k
    refine lintegral_congr_ae ?_
    filter_upwards [hyE k] with ω h
    rw [h]
  simp_rw [hcongr]
  have hmeas : ∀ k, AEStronglyMeasurable (P[Y | m k] - Y) P := fun k =>
    ((hY.condExp (m := m k) (by norm_num)).aestronglyMeasurable).sub hY.aestronglyMeasurable
  have hA : Tendsto (fun k => ∫⁻ ω, ‖P[Y | m k] ω - Y ω‖ₑ ^ (2 : ℝ) ∂P) atTop (𝓝 0) := by
    have : ∀ k, ∫⁻ ω, ‖P[Y | m k] ω - Y ω‖ₑ ^ (2 : ℝ) ∂P = eLpNorm (P[Y | m k] - Y) 2 P ^ (2 : ℝ) :=
      fun k => lintegral_enorm_rpow_two (hmeas k)
    simp_rw [this]
    have h0 : (0 : ℝ≥0∞) = 0 ^ (2 : ℝ) := by simp
    rw [h0]
    exact (ENNReal.continuous_rpow_const.tendsto 0).comp hL2
  rcases hq.eq_or_lt with hq2 | hq2
  · subst hq2; exact hA
  -- interpolation
  set M : ℝ≥0∞ := (2 * eLpNorm Y (ENNReal.ofReal r) P) ^ r with hM
  have hMfin : M ≠ ∞ := by
    refine ENNReal.rpow_ne_top_of_nonneg hr0.le (ENNReal.mul_ne_top (by simp) hYr.eLpNorm_lt_top.ne)
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hB : ∀ k, ∫⁻ ω, ‖P[Y | m k] ω - Y ω‖ₑ ^ r ∂P ≤ M := by
    intro k
    have e := lintegral_enorm_rpow_eq (hmeas k) hr0
    simp only [Pi.sub_apply] at e
    rw [e]
    refine ENNReal.rpow_le_rpow ?_ hr0.le
    have h1 : eLpNorm (P[Y | m k] - Y) (ENNReal.ofReal r) P ≤
        eLpNorm (P[Y | m k]) (ENNReal.ofReal r) P + eLpNorm Y (ENNReal.ofReal r) P := by
      have : P[Y | m k] - Y = P[Y | m k] + (-Y) := by funext ω; simp [sub_eq_add_neg]
      rw [this]
      refine (eLpNorm_add_le hr1).trans ?_
      rw [eLpNorm_neg]
    have h2 := eLpNorm_condExp_le_eLpNorm (m := m k) (μ := P) Y hr1
    calc _ ≤ _ := h1
      _ ≤ eLpNorm Y (ENNReal.ofReal r) P + eLpNorm Y (ENNReal.ofReal r) P := add_le_add h2 le_rfl
      _ = 2 * eLpNorm Y (ENNReal.ofReal r) P := by rw [two_mul]
  set θ : ℝ := (r - q) / (r - 2) with hθ
  have hθ0 : 0 < θ := div_pos (by linarith) (by linarith)
  have hint : ∀ k, ∫⁻ ω, ‖P[Y | m k] ω - Y ω‖ₑ ^ q ∂P ≤
      (∫⁻ ω, ‖P[Y | m k] ω - Y ω‖ₑ ^ (2 : ℝ) ∂P) ^ θ * M ^ ((q - 2) / (r - 2)) := by
    intro k
    refine (lintegral_rpow_interp (P := P) (g := fun ω => ‖P[Y | m k] ω - Y ω‖ₑ)
      (hmeas k).enorm hq2 hqr).trans ?_
    exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hB k) (div_nonneg (by linarith) (by linarith)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun k => bot_le) hint
  have h0 : (0 : ℝ≥0∞) = 0 ^ θ * M ^ ((q - 2) / (r - 2)) := by
    rw [ENNReal.zero_rpow_of_pos hθ0, zero_mul]
  rw [h0]
  refine ENNReal.Tendsto.mul_const ((ENNReal.continuous_rpow_const.tendsto 0).comp hA) (Or.inr ?_)
  exact ENNReal.rpow_ne_top_of_nonneg (div_nonneg (by linarith) (by linarith)) hMfin


section LqTools

variable {E : Type*} [NormedAddCommGroup E]

theorem tendsto_lintegral_iff_eLpNorm {f : ℕ → Ω → E} (hf : ∀ m, AEStronglyMeasurable (f m) P) {q : ℝ}
    (hq : 0 < q) :
    Tendsto (fun m => ∫⁻ ω, ‖f m ω‖ₑ ^ q ∂P) atTop (𝓝 0) ↔
      Tendsto (fun m => eLpNorm (f m) (ENNReal.ofReal q) P) atTop (𝓝 0) := by
  have h : ∀ m, ∫⁻ ω, ‖f m ω‖ₑ ^ q ∂P = eLpNorm (f m) (ENNReal.ofReal q) P ^ q :=
    fun m => lintegral_enorm_rpow_eq (hf m) hq
  simp_rw [h]
  constructor
  · intro ht
    have := (ENNReal.continuous_rpow_const (y := 1 / q)).tendsto 0 |>.comp ht
    have h0 : (0 : ℝ≥0∞) ^ (1 / q) = 0 := ENNReal.zero_rpow_of_pos (by positivity)
    rw [h0] at this
    refine this.congr fun m => ?_
    simp only [Function.comp]
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]
  · intro ht
    have := (ENNReal.continuous_rpow_const (y := q)).tendsto 0 |>.comp ht
    have h0 : (0 : ℝ≥0∞) ^ q = 0 := ENNReal.zero_rpow_of_pos hq
    rw [h0] at this
    exact this

/-- Diagonal argument. -/
theorem exists_diag {B : Type*} [NormedAddCommGroup B] {p : ℝ≥0∞} (hp : 1 ≤ p)
    (g : ℕ → ℕ → Ω → B) (F : ℕ → Ω → B) (G : Ω → B)
    (h1 : ∀ j, Tendsto (fun m => eLpNorm (g j m - F j) p P) atTop (𝓝 0))
    (h2 : Tendsto (fun j => eLpNorm (F j - G) p P) atTop (𝓝 0)) :
    ∃ mm : ℕ → ℕ, Tendsto (fun j => eLpNorm (g j (mm j) - G) p P) atTop (𝓝 0) := by
  have hpos : ∀ j : ℕ, (0 : ℝ≥0∞) < ((j : ℝ≥0∞) + 1)⁻¹ := fun j =>
    ENNReal.inv_pos.2 (by simp)
  have hex : ∀ j, ∃ m, eLpNorm (g j m - F j) p P < ((j : ℝ≥0∞) + 1)⁻¹ := by
    intro j
    exact ((h1 j).eventually (gt_mem_nhds (hpos j))).exists
  choose mm hmm using hex
  refine ⟨mm, ?_⟩
  have h3 : Tendsto (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.tendsto_inv_nat_nhds_zero
    have h4 := (tendsto_add_atTop_iff_nat 1).2 this
    refine h4.congr fun j => ?_
    simp
  have h5 : Tendsto (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹ + eLpNorm (F j - G) p P) atTop (𝓝 0) := by
    simpa using h3.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h5 (fun j => bot_le) (fun j => ?_)
  have : g j (mm j) - G = (g j (mm j) - F j) + (F j - G) := by funext ω; simp
  rw [this]
  exact (eLpNorm_add_le hp).trans (add_le_add (hmm j).le le_rfl)

/-- `‖u • b‖` in `L^p`. -/
theorem eLpNorm_smul_const_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {u : Ω → ℝ}
    (hu : AEStronglyMeasurable u P) (b : B)
    (p : ℝ≥0∞) : eLpNorm (fun ω => u ω • b) p P ≤ ‖b‖ₑ * eLpNorm u p P := by
  have h : eLpNorm (fun ω => u ω • b) p P ≤ eLpNorm (‖b‖ • u) p P := by
    refine eLpNorm_mono_enorm (hu.smul_const b) (fun ω => ?_)
    simp [enorm_smul, Pi.smul_apply, mul_comm]
  refine h.trans ?_
  rw [eLpNorm_const_smul]
  simp

theorem eLpNorm_finsum_smul_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {ι : Type*}
    (S : Finset ι) (b : ι → B) (u : ι → Ω → ℝ) (hu : ∀ s ∈ S, AEStronglyMeasurable (u s) P) {p : ℝ≥0∞}
    (hp : 1 ≤ p) :
    eLpNorm (fun ω => ∑ s ∈ S, u s ω • b s) p P ≤ ∑ s ∈ S, ‖b s‖ₑ * eLpNorm (u s) p P := by
  have h := eLpNorm_sum_le (μ := P) (f := fun s ω => u s ω • b s) (s := S) hp
  have e : (fun ω => ∑ s ∈ S, u s ω • b s) = ∑ s ∈ S, (fun ω => u s ω • b s) := by
    funext ω; simp
  rw [e]
  refine h.trans (Finset.sum_le_sum fun s hs => eLpNorm_smul_const_le (hu s hs) (b s) p)

end LqTools

end Transfer

end HRS.MC.E213U13
