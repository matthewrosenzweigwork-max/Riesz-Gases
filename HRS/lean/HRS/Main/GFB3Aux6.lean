import HRS.Uniform.Q07cAux5
import HRS.Main.GFB3Aux5

/-!
# Packet GFB3, part 6: the continuous `H`-valued version of a Hilbert-Schmidt Itô integral

For a cylindrical Brownian motion `𝔚` over a countable index set and a progressive Hilbert-Schmidt integrand `Z`
(`∀ T, IsHSIntegrand P ℱ T Z`) there is a process `N` with everywhere continuous paths, adapted, vanishing on `(-∞,0]`,
whose coordinates `⟨N_τ, x⟩` are (a.s.) the countable-index Itô integrals of `⟨Z, x⟩`.
Route: coordinates `J^l` along a Hilbert basis, Doob's inequality for each `J^l`, `E ∑_l sup_{t ≤ T} |J^l_t|² < ∞`,
and `N = ∑_l J^l e_l` on the full-measure set where these sums are finite for every `T ∈ ℕ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.HilbertCLTAux

section Tail

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {A : Type*} [Countable A] {ι : Type*} [Countable ι] {𝔚 : ℝ≥0 → Ω → A → ℝ}

/-- Parseval in `ℝ≥0∞`: `∑_l ‖⟨z, e_l⟩‖² = ‖z‖²`. -/
lemma gfb3_parseval_enorm (e : HilbertBasis ι ℝ H) (z : H) :
    ∑' l, ‖inner ℝ z (e l)‖ₑ ^ 2 = ‖z‖ₑ ^ 2 := by
  have h := e.hasSum_inner_mul_inner z z
  have h2 : HasSum (fun l => inner ℝ z (e l) ^ 2) (‖z‖ ^ 2) := by
    rw [← real_inner_self_eq_norm_sq]
    convert h using 2 with l
    rw [real_inner_comm (e l) z, sq]
  rw [enorm_tsum_sq_of_hasSum h2]
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]

lemma gfb3_tsum_cT_eq (e : HilbertBasis ι ℝ H) {Z : ℝ → Ω → A → H}
    (hZ : ∀ T, IsHSIntegrand P ℱ T Z) (T : ℝ) :
    ∑' l, ∑' a, cT P (fun r ω a => inner ℝ (Z r ω a) (e l)) a T = hsSqIntegralOn P Z T := by
  set ξ' : ℝ → Ω → ι × A → ℝ := fun r ω p => inner ℝ (Z r ω p.2) (e p.1) with hξ'
  have hprog : ∀ p : ι × A, IsProgressive ℱ (fun r ω => ξ' r ω p) := fun p =>
    fun i => ((hZ 0).prog p.2 i).inner measurable_const
  have h1 := tsum_lintegral_set_eq (P := P) hprog (S := Set.univ) (R := Set.Icc (0 : ℝ) T)
    measurableSet_Icc (fun r hr => hr.2 : Set.Icc (0 : ℝ) T ⊆ Set.Iic T)
  simp only [Measure.restrict_univ] at h1
  have h2 : ∑' l, ∑' a, cT P (fun r ω a => inner ℝ (Z r ω a) (e l)) a T =
      ∑' p : ι × A, ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ‖ξ' r ω p‖ₑ ^ 2) ∂P := by
    rw [← ENNReal.tsum_prod (f := fun l a => cT P (fun r ω a => inner ℝ (Z r ω a) (e l)) a T)]
    rfl
  rw [h2, h1]
  unfold hsSqIntegralOn
  refine lintegral_congr fun ω => lintegral_congr fun r => ?_
  have h3 : ∑' p : ι × A, ‖ξ' r ω p‖ₑ ^ 2 = ∑' l, ∑' a, ‖ξ' r ω (l, a)‖ₑ ^ 2 :=
    ENNReal.tsum_prod (f := fun l a => ‖ξ' r ω (l, a)‖ₑ ^ 2)
  rw [h3, ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  exact gfb3_parseval_enorm e (Z r ω a)

/-- Doob's inequality for the coordinates, summed over the basis. -/
lemma gfb3_doob_sum (hW : IsCylindricalBrownian P ℱ 𝔚) (e : HilbertBasis ι ℝ H) {Z : ℝ → Ω → A → H}
    (hZ : ∀ T, IsHSIntegrand P ℱ T Z) {J : ι → ℝ → Ω → ℝ}
    (hJ : ∀ l, IsItoC P ℱ 𝔚 (fun r ω a => inner ℝ (Z r ω a) (e l)) (J l)) (T : ℝ) (hT : 0 ≤ T) :
    ∫⁻ ω, ∑' l, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖J l t ω‖ₑ) ^ 2 ∂P ≤ 4 * hsSqIntegralOn P Z T := by
  have hctbl : ∀ l, IsCtbl P ℱ (fun r ω a => inner ℝ (Z r ω a) (e l)) := fun l => HRS.Uniform.Q07c.ctbl_coord hZ (e l)
  have hmeas : ∀ l, Measurable fun ω => (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖J l t ω‖ₑ) ^ 2 := fun l =>
    (measurable_iSup_Icc_enorm (fun t => ((hJ l).adapted t).mono (ℱ.le t) le_rfl) (hJ l).cont T).pow_const 2
  rw [lintegral_tsum fun l => (hmeas l).aemeasurable]
  have hl : ∀ l, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖J l t ω‖ₑ) ^ 2 ∂P ≤
      4 * ∑' a, cT P (fun r ω a => inner ℝ (Z r ω a) (e l)) a T := by
    intro l
    have hmart := (hJ l).martingale (hctbl l) hW
    have hL2 : ∀ t, MemLp (J l t) 2 P := fun t => by
      rcases lt_or_ge t 0 with ht | ht
      · have : J l t = fun _ => 0 := funext fun ω => (hJ l).zero t ht.le ω
        rw [this]; exact MemLp.zero'
      · exact (hJ l).memLp (hctbl l) hW ht
    refine (SimpleIntegrand.doob_L2_continuous hmart (hJ l).cont hL2 T).trans ?_
    exact mul_le_mul' le_rfl ((hJ l).lintegral_sq_le (hctbl l) hW hT)
  calc ∑' l, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖J l t ω‖ₑ) ^ 2 ∂P
      ≤ ∑' l, 4 * ∑' a, cT P (fun r ω a => inner ℝ (Z r ω a) (e l)) a T := ENNReal.tsum_le_tsum hl
    _ = 4 * ∑' l, ∑' a, cT P (fun r ω a => inner ℝ (Z r ω a) (e l)) a T := ENNReal.tsum_mul_left
    _ = 4 * hsSqIntegralOn P Z T := by rw [gfb3_tsum_cT_eq e hZ T]

end Tail

section Build

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*} [Countable ι]

/-- The supremum of `|J^l|` on `[0,n]`, in `ℝ≥0∞`. -/
def gfb3m_B (J : ι → ℝ → Ω → ℝ) (n : ℕ) (l : ι) (ω : Ω) : ℝ≥0∞ := ⨆ t ∈ Set.Icc (0 : ℝ) n, ‖J l t ω‖ₑ

/-- The full-measure set on which `∑_l (sup_{[0,n]} |J^l|)²` is finite for every `n`. -/
def gfb3_G (J : ι → ℝ → Ω → ℝ) : Set Ω := {ω | ∀ n : ℕ, ∑' l, gfb3m_B J n l ω ^ 2 < ⊤}

lemma gfb3_enorm_le_B (J : ι → ℝ → Ω → ℝ) (hz : ∀ l, ∀ t ≤ 0, ∀ ω, J l t ω = 0) (n : ℕ) (l : ι)
    (ω : Ω) {τ : ℝ} (hτ : τ ≤ n) : ‖J l τ ω‖ₑ ≤ gfb3m_B J n l ω := by
  rcases le_or_gt τ 0 with h | h
  · rw [hz l τ h ω]; simp
  · exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) n) => ‖J l t ω‖ₑ) τ ⟨h.le, hτ⟩

lemma gfb3_B_ne_top {J : ι → ℝ → Ω → ℝ} {ω : Ω} (hω : ω ∈ gfb3_G J) (n : ℕ) (l : ι) :
    gfb3m_B J n l ω ≠ ⊤ := by
  have h := hω n
  have h1 : gfb3m_B J n l ω ^ 2 ≤ ∑' l, gfb3m_B J n l ω ^ 2 := ENNReal.le_tsum (f := fun l => gfb3m_B J n l ω ^ 2) l
  have h2 : gfb3m_B J n l ω ^ 2 < ⊤ := lt_of_le_of_lt h1 h
  intro htop
  rw [htop] at h2
  simp at h2

lemma gfb3_summable_B {J : ι → ℝ → Ω → ℝ} {ω : Ω} (hω : ω ∈ gfb3_G J) (n : ℕ) :
    Summable fun l => ((gfb3m_B J n l ω).toReal) ^ 2 := by
  have h := ENNReal.summable_toReal (f := fun l => gfb3m_B J n l ω ^ 2) (hω n).ne
  refine h.congr fun l => ?_
  simp [ENNReal.toReal_pow]

lemma gfb3_abs_le_B {J : ι → ℝ → Ω → ℝ} (hz : ∀ l, ∀ t ≤ 0, ∀ ω, J l t ω = 0) {ω : Ω}
    (hω : ω ∈ gfb3_G J) (n : ℕ) (l : ι) {τ : ℝ} (hτ : τ ≤ n) :
    |J l τ ω| ≤ (gfb3m_B J n l ω).toReal := by
  have h := gfb3_enorm_le_B J hz n l ω hτ
  have h2 := ENNReal.toReal_mono (gfb3_B_ne_top hω n l) h
  simpa using h2

lemma gfb3_summable_sq {J : ι → ℝ → Ω → ℝ} (hz : ∀ l, ∀ t ≤ 0, ∀ ω, J l t ω = 0) {ω : Ω}
    (hω : ω ∈ gfb3_G J) (τ : ℝ) : Summable fun l => J l τ ω ^ 2 := by
  obtain ⟨n, hn⟩ := exists_nat_ge τ
  refine (gfb3_summable_B hω n).of_nonneg_of_le (fun l => sq_nonneg _) fun l => ?_
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (gfb3_abs_le_B hz hω n l hn) 2

open Classical in
/-- The `H`-valued process `N_τ = ∑_l J^l_τ e_l` on the good set, `0` elsewhere. -/
def gfb3_N (e : HilbertBasis ι ℝ H) (J : ι → ℝ → Ω → ℝ) (τ : ℝ) (ω : Ω) : H :=
  if h : Memℓp (fun l => J l τ ω) 2 ∧ ω ∈ gfb3_G J then
    e.repr.symm (⟨fun l => J l τ ω, h.1⟩ : lp (fun _ : ι => ℝ) 2) else 0

/-- The coefficient sequence of `N_τ(ω)` in `ℓ²`. -/
def gfb3_c {J : ι → ℝ → Ω → ℝ} (hz : ∀ l, ∀ t ≤ 0, ∀ ω, J l t ω = 0) {ω : Ω} (hω : ω ∈ gfb3_G J)
    (τ : ℝ) : lp (fun _ : ι => ℝ) 2 :=
  ⟨fun l => J l τ ω, (Torus.memℓp_two_iff _).2 (gfb3_summable_sq hz hω τ)⟩

lemma gfb3_N_of_mem (e : HilbertBasis ι ℝ H) {J : ι → ℝ → Ω → ℝ}
    (hz : ∀ l, ∀ t ≤ 0, ∀ ω, J l t ω = 0) {ω : Ω} (hω : ω ∈ gfb3_G J) (τ : ℝ) :
    gfb3_N e J τ ω = e.repr.symm (gfb3_c hz hω τ) := by
  unfold gfb3_N
  rw [dif_pos ⟨(Torus.memℓp_two_iff _).2 (gfb3_summable_sq hz hω τ), hω⟩]
  rfl

lemma gfb3_N_of_not_mem (e : HilbertBasis ι ℝ H) {J : ι → ℝ → Ω → ℝ} {ω : Ω}
    (hω : ω ∉ gfb3_G J) (τ : ℝ) : gfb3_N e J τ ω = 0 := by
  unfold gfb3_N
  rw [dif_neg (fun h => hω h.2)]

lemma gfb3_N_of_nonpos (e : HilbertBasis ι ℝ H) {J : ι → ℝ → Ω → ℝ}
    (hz : ∀ l, ∀ t ≤ 0, ∀ ω, J l t ω = 0) {τ : ℝ} (hτ : τ ≤ 0) (ω : Ω) : gfb3_N e J τ ω = 0 := by
  by_cases hω : ω ∈ gfb3_G J
  · rw [gfb3_N_of_mem e hz hω]
    have : gfb3_c hz hω τ = 0 := by
      ext l
      simp [gfb3_c, hz l τ hτ ω]
    rw [this, map_zero]
  · exact gfb3_N_of_not_mem e hω τ

lemma gfb3_norm_sub_sq (e : HilbertBasis ι ℝ H) {J : ι → ℝ → Ω → ℝ}
    (hz : ∀ l, ∀ t ≤ 0, ∀ ω, J l t ω = 0) {ω : Ω} (hω : ω ∈ gfb3_G J) (τ τ' : ℝ) :
    ‖gfb3_N e J τ ω - gfb3_N e J τ' ω‖ ^ 2 = ∑' l, (J l τ ω - J l τ' ω) ^ 2 := by
  rw [gfb3_N_of_mem e hz hω, gfb3_N_of_mem e hz hω, ← map_sub, LinearIsometryEquiv.norm_map]
  have := Torus.lp_two_sq (gfb3_c hz hω τ - gfb3_c hz hω τ')
  rw [this.2]
  refine tsum_congr fun l => ?_
  simp [gfb3_c]
  rfl

lemma gfb3_hasSum_inner (e : HilbertBasis ι ℝ H) {J : ι → ℝ → Ω → ℝ}
    (hz : ∀ l, ∀ t ≤ 0, ∀ ω, J l t ω = 0) {ω : Ω} (hω : ω ∈ gfb3_G J) (τ : ℝ) (x : H) :
    HasSum (fun l => J l τ ω * inner ℝ (e l) x) (inner ℝ (gfb3_N e J τ ω) x) := by
  rw [gfb3_N_of_mem e hz hω]
  have h := e.hasSum_repr_symm (gfb3_c hz hω τ)
  have h2 := h.mapL (innerSL ℝ x)
  convert h2 using 1
  · funext l
    simp only [innerSL_apply_apply, inner_smul_right, real_inner_comm x (e l)]
    simp [gfb3_c]
  · simp [innerSL_apply_apply, real_inner_comm]

lemma gfb3_N_continuous (e : HilbertBasis ι ℝ H) {J : ι → ℝ → Ω → ℝ}
    (hz : ∀ l, ∀ t ≤ 0, ∀ ω, J l t ω = 0) (hc : ∀ l ω, Continuous fun t => J l t ω) (ω : Ω) :
    Continuous fun τ => gfb3_N e J τ ω := by
  by_cases hω : ω ∈ gfb3_G J
  · refine continuous_iff_continuousAt.2 fun τ₀ => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    obtain ⟨n, hn⟩ := exists_nat_ge (|τ₀| + 1)
    have hsq : Tendsto (fun τ => ‖gfb3_N e J τ ω - gfb3_N e J τ₀ ω‖ ^ 2) (𝓝 τ₀) (𝓝 0) := by
      simp_rw [gfb3_norm_sub_sq e hz hω]
      have h0 : (0 : ℝ) = ∑' l : ι, (0 : ℝ) := by simp
      rw [h0]
      refine tendsto_tsum_of_dominated_convergence (bound := fun l => 4 * ((gfb3m_B J n l ω).toReal) ^ 2)
        ((gfb3_summable_B hω n).mul_left 4) (fun l => ?_) ?_
      · have : Tendsto (fun τ => (J l τ ω - J l τ₀ ω) ^ 2) (𝓝 τ₀) (𝓝 ((J l τ₀ ω - J l τ₀ ω) ^ 2)) :=
          (((hc l ω).sub continuous_const).pow 2).continuousAt.tendsto
        simpa using this
      · have hnb : ∀ᶠ τ in 𝓝 τ₀, τ ∈ Set.Ioo (τ₀ - 1) (τ₀ + 1) := Ioo_mem_nhds (by linarith) (by linarith)
        filter_upwards [hnb] with τ hτ l
        have h1 := gfb3_abs_le_B hz hω n l (τ := τ) (by
          have := hτ.2; have := le_abs_self τ₀; linarith)
        have h2 := gfb3_abs_le_B hz hω n l (τ := τ₀) (by
          have := le_abs_self τ₀; linarith)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h3 : |J l τ ω - J l τ₀ ω| ≤ 2 * (gfb3m_B J n l ω).toReal := by
          calc |J l τ ω - J l τ₀ ω| ≤ |J l τ ω| + |J l τ₀ ω| := abs_sub _ _
            _ ≤ _ := by linarith
        calc (J l τ ω - J l τ₀ ω) ^ 2 = |J l τ ω - J l τ₀ ω| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * (gfb3m_B J n l ω).toReal) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
          _ = _ := by ring
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  · have : (fun τ => gfb3_N e J τ ω) = fun _ => 0 := funext fun τ => gfb3_N_of_not_mem e hω τ
    rw [this]; exact continuous_const

lemma gfb3_N_adapted [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] (e : HilbertBasis ι ℝ H) {J : ι → ℝ → Ω → ℝ}
    (hz : ∀ l, ∀ t ≤ 0, ∀ ω, J l t ω = 0) (hℱ : IsCompleteFiltration P ℱ)
    (hJad : ∀ l τ, Measurable[ℱ τ] (J l τ)) (hGm : MeasurableSet (gfb3_G J)) (hG0 : P (gfb3_G J)ᶜ = 0)
    (τ : ℝ) : Measurable[ℱ τ] (gfb3_N e J τ) := by
  classical
  rcases le_or_gt τ 0 with hτ | hτ
  · have : gfb3_N e J τ = fun _ => 0 := funext fun ω => gfb3_N_of_nonpos e hz hτ ω
    rw [this]; exact measurable_const
  · have hGτ : MeasurableSet[ℱ τ] (gfb3_G J) := by
      have := hℱ τ (gfb3_G J)ᶜ hGm.compl hG0
      simpa using this.compl
    obtain ⟨F, hF⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset ι))
    set f : ℕ → Ω → H := fun m ω => if ω ∈ gfb3_G J then ∑ l ∈ F m, J l τ ω • e l else 0 with hf
    have hfm : ∀ m, Measurable[ℱ τ] (f m) := by
      intro m
      refine Measurable.ite hGτ ?_ measurable_const
      refine Finset.measurable_sum _ fun l _ => ?_
      exact (hJad l τ).smul_const _
    letI : MeasurableSpace Ω := ℱ τ
    refine measurable_of_tendsto_metrizable hfm ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ gfb3_G J
    · have hs := e.hasSum_repr_symm (gfb3_c hz hω τ)
      have h1 := hs.comp hF
      have h2 : Tendsto (fun m => f m ω) atTop (𝓝 (e.repr.symm (gfb3_c hz hω τ))) := by
        refine h1.congr fun m => ?_
        simp [hf, hω, gfb3_c]
      simpa [gfb3_N_of_mem e hz hω] using h2
    · simp [hf, hω, gfb3_N_of_not_mem e hω]

lemma gfb3_G_measurable {J : ι → ℝ → Ω → ℝ} (hJad : ∀ l τ, Measurable[ℱ τ] (J l τ))
    (hc : ∀ l ω, Continuous fun t => J l t ω) :
    MeasurableSet (gfb3_G J) ∧ ∀ n : ℕ, Measurable fun ω => ∑' l, gfb3m_B J n l ω ^ 2 := by
  have hm : ∀ n : ℕ, Measurable fun ω => ∑' l, gfb3m_B J n l ω ^ 2 := fun n =>
    Measurable.ennreal_tsum fun l =>
      (measurable_iSup_Icc_enorm (fun t => (hJad l t).mono (ℱ.le t) le_rfl) (hc l) n).pow_const 2
  refine ⟨?_, hm⟩
  have : gfb3_G J = ⋂ n : ℕ, {ω | ∑' l, gfb3m_B J n l ω ^ 2 < ⊤} := by
    ext ω; simp [gfb3_G]
  rw [this]
  exact MeasurableSet.iInter fun n => measurableSet_lt (hm n) measurable_const

end Build

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ}

open HRS.Uniform.Q07c in
/-- The identification of the coordinates of `N` with the Itô integrals of `⟨Z, x⟩`. -/
theorem gfb3_coord_identification (hW : IsCylindricalBrownian P ℱ 𝔚) {Z : ℝ → Ω → A → H}
    (hZ : ∀ T, IsHSIntegrand P ℱ T Z) {ι : Type} [Countable ι] (e : HilbertBasis ι ℝ H)
    {J : ι → ℝ → Ω → ℝ}
    (hJ : ∀ l, IsItoC P ℱ 𝔚 (fun r ω a => inner ℝ (Z r ω a) (e l)) (J l))
    (hz : ∀ l, ∀ t ≤ 0, ∀ ω, J l t ω = 0)
    (hG0 : P (gfb3_G J)ᶜ = 0) (x : H) {Jx : ℝ → Ω → ℝ}
    (hJx : IsItoC P ℱ 𝔚 (fun r ω a => inner ℝ (Z r ω a) x) Jx) {τ : ℝ} (hτ : 0 ≤ τ)
    (hNm : AEMeasurable (fun ω => inner ℝ (gfb3_N e J τ ω) x) P) :
    (fun ω => inner ℝ (gfb3_N e J τ ω) x) =ᵐ[P] Jx τ := by
  classical
  have hctbl : ∀ y : H, IsCtbl P ℱ (fun r ω a => inner ℝ (Z r ω a) y) := fun y => ctbl_coord hZ y
  obtain ⟨F, hF⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset ι))
  set cl : ι → ℝ := fun l => inner ℝ (e l) x with hcl
  set S : ℕ → Ω → ℝ := fun m ω => ∑ l ∈ F m, J l τ ω * cl l with hS
  set y : ℕ → H := fun m => x - ∑ l ∈ F m, cl l • e l with hy
  -- the finite partial sums are Itô integrals
  have hξl : ∀ l, IsCtbl P ℱ (fun r ω a => cl l * inner ℝ (Z r ω a) (e l)) := by
    intro l
    have := hctbl (cl l • e l)
    simpa [inner_smul_right] using this
  have hIl : ∀ m, ∀ l ∈ F m, IsItoC P ℱ 𝔚 (fun r ω a => cl l * inner ℝ (Z r ω a) (e l))
      (fun t ω => cl l * J l t ω) := fun m l _ => (hJ l).smul hW (HRS.Uniform.Q07c.ctbl_coord hZ (e l)) (cl l)
  have hsum := fun m => IsItoC.finset_sum hW (F m)
    (fun l r ω a => cl l * inner ℝ (Z r ω a) (e l)) (fun l t ω => cl l * J l t ω)
    (fun l _ => hξl l) (hIl m)
  have hsub := fun m => IsItoC.sub hW (hctbl x) (hsum m).1 hJx (hsum m).2
  have hsub_eq : ∀ m, (fun r ω a => inner ℝ (Z r ω a) x - ∑ l ∈ F m, cl l * inner ℝ (Z r ω a) (e l)) =
      fun r ω a => inner ℝ (Z r ω a) (y m) := by
    intro m; funext r ω a
    simp [hy, inner_sub_right, inner_sum, inner_smul_right]
  have hI : ∀ m, IsItoC P ℱ 𝔚 (fun r ω a => inner ℝ (Z r ω a) (y m))
      (fun t ω => Jx t ω - ∑ l ∈ F m, cl l * J l t ω) := by
    intro m
    have h := hsub m
    rw [← hsub_eq m]
    exact h
  have hsq_top : hsSqIntegralOn P Z τ ≠ ⊤ := (hZ τ).sq.ne
  have hbound : ∀ m, ∫⁻ ω, ‖Jx τ ω - S m ω‖ₑ ^ 2 ∂P ≤ hsSqIntegralOn P Z τ * ‖y m‖ₑ ^ 2 := by
    intro m
    have h1 := (hI m).lintegral_sq_le (hctbl (y m)) hW hτ
    have e1 : ∀ ω, Jx τ ω - ∑ l ∈ F m, cl l * J l τ ω = Jx τ ω - S m ω := fun ω => by
      simp only [hS]
      congr 1
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    simp_rw [e1] at h1
    refine h1.trans ?_
    have hs := tsum_lintegral_set_eq (P := P) (ξ := fun r ω a => inner ℝ (Z r ω a) (y m))
      (hctbl (y m)).prog (S := Set.univ) (R := Set.Icc (0 : ℝ) τ) measurableSet_Icc
      (fun r hr => hr.2 : Set.Icc (0 : ℝ) τ ⊆ Set.Iic τ)
    simp only [Measure.restrict_univ] at hs
    unfold cT
    rw [hs]
    have hpt : ∀ r ω, ∑' a, ‖inner ℝ (Z r ω a) (y m)‖ₑ ^ 2 ≤ (∑' a, ‖Z r ω a‖ₑ ^ 2) * ‖y m‖ₑ ^ 2 := by
      intro r ω
      rw [← ENNReal.tsum_mul_right]
      exact ENNReal.tsum_le_tsum fun a => pc_enorm_inner_sq_le _ _
    calc ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) τ, ∑' a, ‖inner ℝ (Z r ω a) (y m)‖ₑ ^ 2) ∂P
        ≤ ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) τ, (∑' a, ‖Z r ω a‖ₑ ^ 2) * ‖y m‖ₑ ^ 2) ∂P :=
          lintegral_mono fun ω => lintegral_mono fun r => hpt r ω
      _ = hsSqIntegralOn P Z τ * ‖y m‖ₑ ^ 2 := by
          unfold hsSqIntegralOn
          rw [← lintegral_mul_const' _ _ (pc_enorm_sq_ne_top (y m))]
          refine lintegral_congr fun ω => ?_
          rw [lintegral_mul_const' _ _ (pc_enorm_sq_ne_top (y m))]
  -- `y m → 0`
  have hy0 : Tendsto (fun m => ‖y m‖ₑ ^ 2) atTop (𝓝 0) := by
    have hs : HasSum (fun l => cl l • e l) x := by
      have := e.hasSum_repr x
      convert this using 2 with l
      simp [hcl, HilbertBasis.repr_apply_apply]
    have h1 := hs.comp hF
    have h2 : Tendsto y atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := x)).sub h1
      simpa [hy] using this
    have h3 := ((ENNReal.continuous_pow 2).comp continuous_enorm).tendsto (0 : H)
    simpa [Function.comp_def] using h3.comp h2
  have hv : Tendsto (fun m => hsSqIntegralOn P Z τ * ‖y m‖ₑ ^ 2) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hy0 (Or.inr hsq_top)
  have hu : Tendsto (fun m => ∫⁻ ω, ‖Jx τ ω - S m ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hv (fun m => zero_le) hbound
  -- pointwise convergence on the good set
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun m => S m ω) atTop (𝓝 (inner ℝ (gfb3_N e J τ ω) x)) := by
    have hG : ∀ᵐ ω ∂P, ω ∈ gfb3_G J := by
      rw [ae_iff]
      exact hG0
    filter_upwards [hG] with ω hω
    exact (gfb3_hasSum_inner e hz hω τ x).comp hF
  have hSm : ∀ m, AEMeasurable (S m) P := fun m => by
    refine (Finset.measurable_sum _ fun l _ => ?_).aemeasurable
    exact (((hJ l).adapted τ).mono (ℱ.le τ) le_rfl).mul_const _
  have hJxm : AEMeasurable (Jx τ) P := (((hJx.adapted τ).mono (ℱ.le τ) le_rfl)).aemeasurable
  have hF2 := lintegral_enorm_sq_le_liminf (P := P) (X := S) (Y := fun ω => inner ℝ (gfb3_N e J τ ω) x)
    (Z := Jx τ) hSm hJxm hlim
  rw [hu.liminf_eq] at hF2
  have h0 : ∫⁻ ω, ‖(Jx τ ω - inner ℝ (gfb3_N e J τ ω) x)‖ₑ ^ 2 ∂P = 0 := le_antisymm hF2 zero_le
  have := ae_eq_zero_of_lintegral_enorm_sq_eq_zero (hJxm.sub hNm) h0
  filter_upwards [this] with ω hω
  have : Jx τ ω - inner ℝ (gfb3_N e J τ ω) x = 0 := hω
  linarith

open HRS.Uniform.Q07c in
/-- **The continuous `H`-valued version of the Hilbert-Schmidt Itô integral.** -/
theorem gfb3_exists_hilbert_version (hW : IsCylindricalBrownian P ℱ 𝔚) {Z : ℝ → Ω → A → H}
    (hZ : ∀ T, IsHSIntegrand P ℱ T Z) :
    ∃ N : ℝ → Ω → H, (∀ ω, Continuous fun τ => N τ ω) ∧ (∀ τ, Measurable[ℱ τ] (N τ)) ∧
      (∀ τ, τ ≤ 0 → ∀ ω, N τ ω = 0) ∧
      ∀ x : H, ∃ J : ℝ → Ω → ℝ, IsItoC P ℱ 𝔚 (fun r ω a => inner ℝ (Z r ω a) x) J ∧
        ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (N τ ω) x) =ᵐ[P] J τ := by
  classical
  obtain ⟨ι, hι, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  haveI := hι
  have hctbl := fun l => ctbl_coord hZ (e l)
  choose J hJ using fun l => exists_isItoC hW (hctbl l)
  have hz : ∀ l t, t ≤ 0 → ∀ ω, J l t ω = 0 := fun l => (hJ l).zero
  have hc : ∀ l ω, Continuous fun t => J l t ω := fun l => (hJ l).cont
  have hJad : ∀ l τ, Measurable[ℱ τ] (J l τ) := fun l => (hJ l).adapted
  have hℱ : IsCompleteFiltration P ℱ := (hW ∅).complete
  obtain ⟨hGm, hmeas⟩ := gfb3_G_measurable hJad hc
  have hG0 : P (gfb3_G J)ᶜ = 0 := by
    have h1 : ∀ n : ℕ, ∀ᵐ ω ∂P, ∑' l, gfb3m_B J n l ω ^ 2 < ⊤ := fun n =>
      ae_lt_top (hmeas n) (ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (by simp) (hZ n).sq.ne) (gfb3_doob_sum hW e hZ hJ n (Nat.cast_nonneg n)))
    have h2 := ae_all_iff.2 h1
    rw [ae_iff] at h2
    exact h2
  refine ⟨gfb3_N e J, gfb3_N_continuous e hz hc, gfb3_N_adapted e hz hℱ hJad hGm hG0,
    fun τ hτ ω => gfb3_N_of_nonpos e hz hτ ω, fun x => ?_⟩
  obtain ⟨Jx, hJx⟩ := exists_isItoC hW (ctbl_coord hZ x)
  refine ⟨Jx, hJx, fun τ hτ => gfb3_coord_identification hW hZ e hJ hz hG0 x hJx hτ ?_⟩
  exact ((((gfb3_N_adapted e hz hℱ hJad hGm hG0 τ).mono (ℱ.le τ) le_rfl)).inner
    measurable_const).aemeasurable

end Main

end HRS.GF
