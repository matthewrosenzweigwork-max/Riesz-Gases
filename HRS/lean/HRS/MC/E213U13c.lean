import HRS.MC.E213U13b

/-!
# E213U13c: scalar chaos approximation and the vector-valued lift

For `Y` in the `L²`-closure of the polynomial spaces `K1` / `K2` and in some `L^r`, `r > q ≥ 2`, `Y` is an
`L^q`-limit of polynomials (`firstApprox_of_InQ1`, `secondApprox_of_InQ2`), and a Banach-valued random
variable which is the `L^q`-limit of finite-rank projections whose scalar coordinates are such `Y`s is in the
(first/second) chaos (`inFirstChaos_of_approx`, `inSecondChaos_of_approx`).
-/

open MeasureTheory ProbabilityTheory Filter Topology HRS
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U13

section Lift

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

/-- `Y` lies in the `L²` closure of the linear polynomials in `ξ`. -/
def InQ1 (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) (Y : Ω → ℝ) : Prop :=
  ∃ h : MemLp Y 2 P, h.toLp Y ∈ Qc (K1 hξ hm)

/-- `Y` lies in the `L²` closure of the centred quadratic polynomials in `ξ`. -/
def InQ2 (hξ : IsStdGaussianSeq P ξ) (Y : Ω → ℝ) : Prop :=
  ∃ h : MemLp Y 2 P, h.toLp Y ∈ Qc (K2 hξ)

theorem firstApprox_of_InQ1 (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) {Y : Ω → ℝ}
    (hQ : InQ1 hξ hm Y) {q r : ℝ} (hq : 2 ≤ q) (hqr : q < r) (hYr : MemLp Y (ENNReal.ofReal r) P) :
    ∃ c : ℕ → ℕ → ℝ, Tendsto (fun m => ∫⁻ ω, ‖(∑ i ∈ Finset.range m, ξ i ω • c m i) - Y ω‖ₑ ^ q ∂P)
      atTop (𝓝 0) := by
  obtain ⟨hY2, hYc⟩ := hQ
  obtain ⟨y, hyK, hyT⟩ := transfer (K1_mono hξ hm) (sig_le hm) (K1_hmem hξ hm) (K1_hself hξ hm) hY2 hYc hq hqr hYr
  have := fun k => K1_poly hξ hm (y k) (hyK k)
  choose a ha using this
  refine ⟨a, hyT.congr fun k => ?_⟩
  refine lintegral_congr_ae ?_
  filter_upwards [ha k] with ω h
  rw [h]

theorem secondApprox_of_InQ2 (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) {Y : Ω → ℝ}
    (hQ : InQ2 hξ Y) {q r : ℝ} (hq : 2 ≤ q) (hqr : q < r) (hYr : MemLp Y (ENNReal.ofReal r) P) :
    ∃ c : ℕ → ℕ → ℕ → ℝ, Tendsto (fun m => ∫⁻ ω, ‖(∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        (ξ i ω * ξ j ω - if i = j then 1 else 0) • c m i j) - Y ω‖ₑ ^ q ∂P) atTop (𝓝 0) := by
  obtain ⟨hY2, hYc⟩ := hQ
  obtain ⟨y, hyK, hyT⟩ := transfer (K2_mono hξ) (sig_le hm) (K2_hmem hξ hm) (K2_hself hξ hm) hY2 hYc hq hqr hYr
  have := fun k => K2_poly hξ (y k) (hyK k)
  choose a ha using this
  refine ⟨a, hyT.congr fun k => ?_⟩
  refine lintegral_congr_ae ?_
  filter_upwards [ha k] with ω h
  rw [h]


theorem dct_proj {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {W : Ω → B}
    (hW : AEStronglyMeasurable W P) {q : ℝ} (hq : 1 ≤ q) (hWq : MemLp W (ENNReal.ofReal q) P)
    (Pn : ℕ → B →L[ℝ] B) (hPn : ∀ n x, ‖Pn n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => Pn n x) atTop (𝓝 x)) :
    Tendsto (fun n => eLpNorm (fun ω => Pn n (W ω) - W ω) (ENNReal.ofReal q) P) atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have hm : ∀ n, AEStronglyMeasurable (fun ω => Pn n (W ω) - W ω) P := fun n =>
    ((Pn n).continuous.comp_aestronglyMeasurable hW).sub hW
  rw [← tendsto_lintegral_iff_eLpNorm hm hq0]
  have hfin : ∫⁻ ω, ‖W ω‖ₑ ^ q ∂P ≠ ∞ := by
    rw [lintegral_enorm_rpow_eq hW hq0]
    exact ENNReal.rpow_ne_top_of_nonneg hq0.le hWq.eLpNorm_lt_top.ne
  have key : Tendsto (fun n => ∫⁻ ω, ‖Pn n (W ω) - W ω‖ₑ ^ q ∂P) atTop (𝓝 (∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P)) := by
   refine tendsto_lintegral_of_dominated_convergence' (fun ω => (2 * ‖W ω‖ₑ) ^ q)
    (fun n => (hm n).enorm.pow_const q) ?_ ?_ ?_
   · -- bound
     intro n
     refine Filter.Eventually.of_forall fun ω => ?_
     refine ENNReal.rpow_le_rpow ?_ hq0.le
     calc ‖Pn n (W ω) - W ω‖ₑ ≤ ‖Pn n (W ω)‖ₑ + ‖W ω‖ₑ := enorm_sub_le
       _ ≤ ‖W ω‖ₑ + ‖W ω‖ₑ := by
         gcongr
         rw [← ofReal_norm, ← ofReal_norm]
         exact ENNReal.ofReal_le_ofReal (hPn n _)
       _ = 2 * ‖W ω‖ₑ := by rw [two_mul]
   · -- finiteness of the bound
     have : ∀ ω, (2 * ‖W ω‖ₑ) ^ q = 2 ^ q * ‖W ω‖ₑ ^ q := fun ω =>
       ENNReal.mul_rpow_of_nonneg _ _ hq0.le
     simp_rw [this]
     rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le (by simp))]
     exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq0.le (by simp)) hfin
   · refine Filter.Eventually.of_forall fun ω => ?_
     have h1 : Tendsto (fun n => Pn n (W ω) - W ω) atTop (𝓝 0) := by
       simpa using (hlim (W ω)).sub_const (W ω)
     have h2 : Tendsto (fun n => ‖Pn n (W ω) - W ω‖ₑ) atTop (𝓝 0) := by
       have := (continuous_enorm.tendsto (0 : B)).comp h1
       rw [enorm_zero] at this
       exact this
     have h3 := (ENNReal.continuous_rpow_const (y := q)).tendsto 0 |>.comp h2
     rwa [ENNReal.zero_rpow_of_pos hq0] at h3

  simpa using key


theorem memLp_clm_comp {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {W : Ω → B} {p : ℝ≥0∞}
    (hW : MemLp W p P) (ℓ : B →L[ℝ] ℝ) : MemLp (fun ω => ℓ (W ω)) p P :=
  ℓ.comp_memLp' hW

theorem inFirstChaos_of_approx (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    {W : Ω → B} (hW : AEStronglyMeasurable W P) {q r : ℝ} (hq : 2 ≤ q) (hqr : q < r)
    (hWr : MemLp W (ENNReal.ofReal r) P)
    (Pn : ℕ → B →L[ℝ] B) (hPn : ∀ n x, ‖Pn n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => Pn n x) atTop (𝓝 x))
    {ι : Type*} (S : ℕ → Finset ι) (ℓ : ι → B →L[ℝ] ℝ) (b : ℕ → ι → B)
    (hfin : ∀ n x, Pn n x = ∑ s ∈ S n, ℓ s x • b n s)
    (hscal : ∀ n, ∀ s ∈ S n, InQ1 hξ hm (fun ω => ℓ s (W ω))) :
    InFirstChaos P ξ q W := by
  classical
  have hq1 : 1 ≤ q := by linarith
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 hq1
  have hWq : MemLp W (ENNReal.ofReal q) P := hWr.mono_exponent (ENNReal.ofReal_le_ofReal hqr.le)
  have hex : ∀ n, ∀ s ∈ S n, ∃ c : ℕ → ℕ → ℝ, Tendsto (fun m => ∫⁻ ω,
      ‖(∑ i ∈ Finset.range m, ξ i ω • c m i) - ℓ s (W ω)‖ₑ ^ q ∂P) atTop (𝓝 0) := fun n s hs =>
    firstApprox_of_InQ1 hξ hm (hscal n s hs) hq hqr (memLp_clm_comp hWr (ℓ s))
  choose! c hc using hex
  -- scalar polynomials
  set poly : ℕ → ι → ℕ → Ω → ℝ := fun n s m ω => ∑ i ∈ Finset.range m, ξ i ω • c n s m i with hpoly
  have hpm : ∀ n s m, Measurable (poly n s m) := by
    intro n s m
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (hm i).smul_const _
  have hum : ∀ n s m, AEStronglyMeasurable (fun ω => poly n s m ω - ℓ s (W ω)) P := fun n s m =>
    (hpm n s m).aestronglyMeasurable.sub ((ℓ s).continuous.comp_aestronglyMeasurable hW)
  have hu0 : ∀ n, ∀ s ∈ S n, Tendsto (fun m => eLpNorm (fun ω => poly n s m ω - ℓ s (W ω))
      (ENNReal.ofReal q) P) atTop (𝓝 0) := fun n s hs =>
    (tendsto_lintegral_iff_eLpNorm (hum n s) (by linarith)).1 (hc n s hs)
  set g : ℕ → ℕ → Ω → B := fun n m ω => ∑ s ∈ S n, poly n s m ω • b n s with hg
  set F : ℕ → Ω → B := fun n ω => Pn n (W ω) with hF
  have h1 : ∀ n, Tendsto (fun m => eLpNorm (g n m - F n) (ENNReal.ofReal q) P) atTop (𝓝 0) := by
    intro n
    have heq : ∀ m, g n m - F n = fun ω => ∑ s ∈ S n, (poly n s m ω - ℓ s (W ω)) • b n s := by
      intro m; funext ω
      simp only [hg, hF, Pi.sub_apply, hfin n (W ω), sub_smul, Finset.sum_sub_distrib]
    simp_rw [heq]
    have hb : ∀ m, eLpNorm (fun ω => ∑ s ∈ S n, (poly n s m ω - ℓ s (W ω)) • b n s) (ENNReal.ofReal q) P ≤
        ∑ s ∈ S n, ‖b n s‖ₑ * eLpNorm (fun ω => poly n s m ω - ℓ s (W ω)) (ENNReal.ofReal q) P := fun m =>
      eLpNorm_finsum_smul_le (S n) (b n) (fun s ω => poly n s m ω - ℓ s (W ω)) (fun s _ => hum n s m) hp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun m => bot_le) hb
    have : Tendsto (fun m => ∑ s ∈ S n, ‖b n s‖ₑ * eLpNorm (fun ω => poly n s m ω - ℓ s (W ω))
        (ENNReal.ofReal q) P) atTop (𝓝 (∑ s ∈ S n, ‖b n s‖ₑ * 0)) := by
      refine tendsto_finsetSum _ fun s hs => ?_
      exact ENNReal.Tendsto.const_mul (hu0 n s hs) (Or.inr (by simp))
    simpa using this
  have h2 : Tendsto (fun n => eLpNorm (F n - W) (ENNReal.ofReal q) P) atTop (𝓝 0) :=
    dct_proj hW hq1 hWq Pn hPn hlim
  obtain ⟨mm, hmm⟩ := exists_diag hp g F W h1 h2
  refine ⟨hW, mm, fun j i => ∑ s ∈ S j, c j s (mm j) i • b j s, ?_⟩
  have hmeas : ∀ j, AEStronglyMeasurable (fun ω => (∑ i ∈ Finset.range (mm j), ξ i ω •
      (∑ s ∈ S j, c j s (mm j) i • b j s)) - W ω) P := by
    intro j
    refine AEStronglyMeasurable.sub ?_ hW
    refine (Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_)
    exact (hm i).aestronglyMeasurable.smul_const _
  rw [tendsto_lintegral_iff_eLpNorm hmeas (by linarith)]
  refine hmm.congr fun j => ?_
  congr 1
  funext ω
  simp only [hg, Pi.sub_apply, hpoly, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp


theorem inSecondChaos_of_approx (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    {W : Ω → B} (hW : AEStronglyMeasurable W P) {q r : ℝ} (hq : 2 ≤ q) (hqr : q < r)
    (hWr : MemLp W (ENNReal.ofReal r) P)
    (Pn : ℕ → B →L[ℝ] B) (hPn : ∀ n x, ‖Pn n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => Pn n x) atTop (𝓝 x))
    {ι : Type*} (S : ℕ → Finset ι) (ℓ : ι → B →L[ℝ] ℝ) (b : ℕ → ι → B)
    (hfin : ∀ n x, Pn n x = ∑ s ∈ S n, ℓ s x • b n s)
    (hscal : ∀ n, ∀ s ∈ S n, InQ2 hξ (fun ω => ℓ s (W ω))) :
    InSecondChaos P ξ q W := by
  classical
  have hq1 : 1 ≤ q := by linarith
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 hq1
  have hWq : MemLp W (ENNReal.ofReal q) P := hWr.mono_exponent (ENNReal.ofReal_le_ofReal hqr.le)
  have hex : ∀ n, ∀ s ∈ S n, ∃ c : ℕ → ℕ → ℕ → ℝ, Tendsto (fun m => ∫⁻ ω,
      ‖(∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (ξ i ω * ξ j ω - if i = j then 1 else 0) • c m i j) -
        ℓ s (W ω)‖ₑ ^ q ∂P) atTop (𝓝 0) := fun n s hs =>
    secondApprox_of_InQ2 hξ hm (hscal n s hs) hq hqr (memLp_clm_comp hWr (ℓ s))
  choose! c hc using hex
  set poly : ℕ → ι → ℕ → Ω → ℝ := fun n s m ω =>
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (ξ i ω * ξ j ω - if i = j then 1 else 0) • c n s m i j with hpoly
  have hpm : ∀ n s m, Measurable (poly n s m) := by
    intro n s m
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact (((hm i).mul (hm j)).sub measurable_const).smul_const _
  have hum : ∀ n s m, AEStronglyMeasurable (fun ω => poly n s m ω - ℓ s (W ω)) P := fun n s m =>
    (hpm n s m).aestronglyMeasurable.sub ((ℓ s).continuous.comp_aestronglyMeasurable hW)
  have hu0 : ∀ n, ∀ s ∈ S n, Tendsto (fun m => eLpNorm (fun ω => poly n s m ω - ℓ s (W ω))
      (ENNReal.ofReal q) P) atTop (𝓝 0) := fun n s hs =>
    (tendsto_lintegral_iff_eLpNorm (hum n s) (by linarith)).1 (hc n s hs)
  set g : ℕ → ℕ → Ω → B := fun n m ω => ∑ s ∈ S n, poly n s m ω • b n s with hg
  set F : ℕ → Ω → B := fun n ω => Pn n (W ω) with hF
  have h1 : ∀ n, Tendsto (fun m => eLpNorm (g n m - F n) (ENNReal.ofReal q) P) atTop (𝓝 0) := by
    intro n
    have heq : ∀ m, g n m - F n = fun ω => ∑ s ∈ S n, (poly n s m ω - ℓ s (W ω)) • b n s := by
      intro m; funext ω
      simp only [hg, hF, Pi.sub_apply, hfin n (W ω), sub_smul, Finset.sum_sub_distrib]
    simp_rw [heq]
    have hb : ∀ m, eLpNorm (fun ω => ∑ s ∈ S n, (poly n s m ω - ℓ s (W ω)) • b n s) (ENNReal.ofReal q) P ≤
        ∑ s ∈ S n, ‖b n s‖ₑ * eLpNorm (fun ω => poly n s m ω - ℓ s (W ω)) (ENNReal.ofReal q) P := fun m =>
      eLpNorm_finsum_smul_le (S n) (b n) (fun s ω => poly n s m ω - ℓ s (W ω)) (fun s _ => hum n s m) hp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun m => bot_le) hb
    have : Tendsto (fun m => ∑ s ∈ S n, ‖b n s‖ₑ * eLpNorm (fun ω => poly n s m ω - ℓ s (W ω))
        (ENNReal.ofReal q) P) atTop (𝓝 (∑ s ∈ S n, ‖b n s‖ₑ * 0)) := by
      refine tendsto_finsetSum _ fun s hs => ?_
      exact ENNReal.Tendsto.const_mul (hu0 n s hs) (Or.inr (by simp))
    simpa using this
  have h2 : Tendsto (fun n => eLpNorm (F n - W) (ENNReal.ofReal q) P) atTop (𝓝 0) :=
    dct_proj hW hq1 hWq Pn hPn hlim
  obtain ⟨mm, hmm⟩ := exists_diag hp g F W h1 h2
  refine ⟨hW, mm, fun j i k => ∑ s ∈ S j, c j s (mm j) i k • b j s, ?_⟩
  have hmeas : ∀ j, AEStronglyMeasurable (fun ω => (∑ i ∈ Finset.range (mm j), ∑ k ∈ Finset.range (mm j),
      (ξ i ω * ξ k ω - if i = k then 1 else 0) • (∑ s ∈ S j, c j s (mm j) i k • b j s)) - W ω) P := by
    intro j
    refine AEStronglyMeasurable.sub ?_ hW
    refine (Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_)
    exact (((hm i).mul (hm k)).sub measurable_const).aestronglyMeasurable.smul_const _
  rw [tendsto_lintegral_iff_eLpNorm hmeas (by linarith)]
  refine hmm.congr fun j => ?_
  congr 1
  funext ω
  simp only [hg, Pi.sub_apply, hpoly, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine congrArg (fun x => x - W ω) (Finset.sum_congr rfl fun s _ => ?_)
  rw [Finset.sum_comm]
  simp only [smul_eq_mul]


/-- Continuous linear maps preserve `L^q` convergence of coefficient polynomials. -/
theorem tendsto_clm_lintegral {B₁ B₂ : Type*} [NormedAddCommGroup B₁] [NormedSpace ℝ B₁]
    [NormedAddCommGroup B₂] [NormedSpace ℝ B₂] (Λ : B₁ →L[ℝ] B₂) {f : ℕ → Ω → B₁} {q : ℝ} (hq : 0 < q)
    (h : Tendsto (fun m => ∫⁻ ω, ‖f m ω‖ₑ ^ q ∂P) atTop (𝓝 0)) :
    Tendsto (fun m => ∫⁻ ω, ‖Λ (f m ω)‖ₑ ^ q ∂P) atTop (𝓝 0) := by
  have hb : ∀ m, ∫⁻ ω, ‖Λ (f m ω)‖ₑ ^ q ∂P ≤ ENNReal.ofReal ‖Λ‖ ^ q * ∫⁻ ω, ‖f m ω‖ₑ ^ q ∂P := by
    intro m
    have hpt : ∀ ω, ‖Λ (f m ω)‖ₑ ^ q ≤ ENNReal.ofReal ‖Λ‖ ^ q * ‖f m ω‖ₑ ^ q := by
      intro ω
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
      refine ENNReal.rpow_le_rpow ?_ hq.le
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (Λ.le_opNorm _)
    calc ∫⁻ ω, ‖Λ (f m ω)‖ₑ ^ q ∂P ≤ ∫⁻ ω, ENNReal.ofReal ‖Λ‖ ^ q * ‖f m ω‖ₑ ^ q ∂P := lintegral_mono hpt
      _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun m => bot_le) hb
  have := ENNReal.Tendsto.const_mul h (Or.inr (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top) :
    (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal ‖Λ‖ ^ q ≠ ∞)
  simpa using this

theorem InFirstChaos.clm {B₁ B₂ : Type*} [NormedAddCommGroup B₁] [NormedSpace ℝ B₁]
    [NormedAddCommGroup B₂] [NormedSpace ℝ B₂]
    (Λ : B₁ →L[ℝ] B₂) {W : Ω → B₁} {q : ℝ} (hq : 0 < q) (h : InFirstChaos P ξ q W) :
    InFirstChaos P ξ q (fun ω => Λ (W ω)) := by
  obtain ⟨hm, n, c, ht⟩ := h
  refine ⟨Λ.continuous.comp_aestronglyMeasurable hm, n, fun m i => Λ (c m i), ?_⟩
  have := tendsto_clm_lintegral (P := P) Λ hq ht
  refine this.congr fun m => ?_
  congr 1; funext ω
  simp [map_sum, map_sub]

theorem InSecondChaos.clm {B₁ B₂ : Type*} [NormedAddCommGroup B₁] [NormedSpace ℝ B₁]
    [NormedAddCommGroup B₂] [NormedSpace ℝ B₂]
    (Λ : B₁ →L[ℝ] B₂) {W : Ω → B₁} {q : ℝ} (hq : 0 < q) (h : InSecondChaos P ξ q W) :
    InSecondChaos P ξ q (fun ω => Λ (W ω)) := by
  obtain ⟨hm, n, c, ht⟩ := h
  refine ⟨Λ.continuous.comp_aestronglyMeasurable hm, n, fun m i j => Λ (c m i j), ?_⟩
  have := tendsto_clm_lintegral (P := P) Λ hq ht
  refine this.congr fun m => ?_
  congr 1; funext ω
  simp [map_sum, map_sub]

end Lift

end HRS.MC.E213U13
