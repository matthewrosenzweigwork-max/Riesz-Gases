import HRS.Uniform.Comp28W1

/-!
# COMP-28, Wasserstein part, W2: orthogonality of martingale increments and the `L²` size of an increment

For an `H`-valued Hilbert martingale `D` with covariation density `Sg` on `[0,S]`:
* `orth_vec`: `E⟨ξ, D_{s'} - D_s⟩ = 0` for `ξ ∈ L²(ℱ_s; H)`;
* `sq_incr`: `E‖D_{s'} - D_s‖² ≤ E∫_s^{s'} ‖Sg_σ‖_{𝔖₁} dσ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q07c

section Incr

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {D : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} {S : ℝ}

/-- `D τ` is `ℱ τ`-measurable. -/
lemma measurable_D (hD : IsHilbertMartingaleWithCovariation P ℱ S D Sg) (τ : ℝ) :
    Measurable[ℱ τ] (D τ) := by
  obtain ⟨ι₀, hι₀, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  haveI := hι₀
  letI : MeasurableSpace Ω := ℱ τ
  refine measurable_of_inner_basis b fun i => ?_
  have := ((hD.martingale (b i)).1 τ).measurable
  simpa [real_inner_comm] using this

lemma memLp_D (hD : IsHilbertMartingaleWithCovariation P ℱ S D Sg) (hS : 0 ≤ S) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ S) : MemLp (D τ) 2 P := hD.sq_int τ ⟨hτ0, hτ⟩

/-- Orthogonality of an `ℱ_s`-measurable `L²` vector and a martingale increment. -/
theorem orth_vec (hD : IsHilbertMartingaleWithCovariation P ℱ S D Sg) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') (hs'S : s' ≤ S) {ξ : Ω → H} (hξ : Measurable[ℱ s] ξ) (hξ2 : MemLp ξ 2 P) :
    ∫ ω, inner ℝ (ξ ω) (D s' ω - D s ω) ∂P = 0 := by
  classical
  have hS : 0 ≤ S := hs.trans (hss'.trans hs'S)
  obtain ⟨ι, hι, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  haveI := hι
  have hmeasξ : Measurable ξ := hξ.mono (ℱ.le s) le_rfl
  have hΔ2 : MemLp (fun ω => D s' ω - D s ω) 2 P :=
    (memLp_D hD hS (hs.trans hss') hs'S).sub (memLp_D hD hS hs (hss'.trans hs'S))
  -- the coordinate terms
  have hterm : ∀ k, ∫ ω, inner ℝ (ξ ω) (b k) * inner ℝ (b k) (D s' ω - D s ω) ∂P = 0 := by
    intro k
    have hZ : StronglyMeasurable[ℱ s] (fun ω => inner ℝ (ξ ω) (b k)) :=
      (hξ.inner measurable_const).stronglyMeasurable
    have hZ2 : MemLp (fun ω => inner ℝ (ξ ω) (b k)) 2 P := hξ2.inner_const (𝕜 := ℝ) (b k)
    have h1 := LindebergAux.integral_mul_martingale (P := P) ℱ (hD.martingale (b k)) hss' hZ hZ2
      (memLp_inner_aux hD hS (b k) hs'S)
    have e : ∀ ω, inner ℝ (ξ ω) (b k) * inner ℝ (b k) (D s' ω - D s ω) =
        inner ℝ (ξ ω) (b k) * inner ℝ (D s' ω) (b k) - inner ℝ (ξ ω) (b k) * inner ℝ (D s ω) (b k) := by
      intro ω; rw [← real_inner_comm (b k) (D s' ω - D s ω), inner_sub_left]; ring
    simp_rw [e]
    have i1 : Integrable (fun ω => inner ℝ (ξ ω) (b k) * inner ℝ (D s' ω) (b k)) P :=
      hZ2.integrable_mul (memLp_inner_aux hD hS (b k) hs'S)
    have i2 : Integrable (fun ω => inner ℝ (ξ ω) (b k) * inner ℝ (D s ω) (b k)) P :=
      hZ2.integrable_mul (memLp_inner_aux hD hS (b k) (hss'.trans hs'S))
    rw [integral_sub i1 i2, h1, sub_self]
  -- partial sums
  have hbound : ∀ (F : Finset ι) ω, |∑ k ∈ F, inner ℝ (ξ ω) (b k) * inner ℝ (b k) (D s' ω - D s ω)| ≤
      ‖ξ ω‖ * ‖D s' ω - D s ω‖ := by
    intro F ω
    have h1 := b.orthonormal.sum_inner_products_le (ξ ω) (s := F)
    have h2 := b.orthonormal.sum_inner_products_le (D s' ω - D s ω) (s := F)
    simp only [Real.norm_eq_abs, sq_abs] at h1 h2
    have e1 : ∀ k, inner ℝ (b k) (ξ ω) = inner ℝ (ξ ω) (b k) := fun k => real_inner_comm _ _
    simp only [e1] at h1
    have hcs := Finset.abs_sum_le_sum_abs (fun k => inner ℝ (ξ ω) (b k) * inner ℝ (b k) (D s' ω - D s ω)) F
    have hcs2 : (∑ k ∈ F, |inner ℝ (ξ ω) (b k) * inner ℝ (b k) (D s' ω - D s ω)|) ≤
        Real.sqrt (∑ k ∈ F, inner ℝ (ξ ω) (b k) ^ 2) * Real.sqrt (∑ k ∈ F, inner ℝ (b k) (D s' ω - D s ω) ^ 2) := by
      have := Finset.sum_mul_sq_le_sq_mul_sq F (fun k => |inner ℝ (ξ ω) (b k)|)
        (fun k => |inner ℝ (b k) (D s' ω - D s ω)|)
      rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      refine Real.le_sqrt_of_sq_le ?_
      simp only [abs_mul, sq_abs] at this ⊢
      exact this
    refine hcs.trans (hcs2.trans ?_)
    refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (norm_nonneg _)
    · exact Real.sqrt_le_iff.2 ⟨norm_nonneg _, h1⟩
    · exact Real.sqrt_le_iff.2 ⟨norm_nonneg _, h2⟩
  have hint : Integrable (fun ω => ‖ξ ω‖ * ‖D s' ω - D s ω‖) P :=
    hξ2.norm.integrable_mul hΔ2.norm
  have hlim : Tendsto (fun F : Finset ι => ∫ ω, ∑ k ∈ F, inner ℝ (ξ ω) (b k) *
      inner ℝ (b k) (D s' ω - D s ω) ∂P) atTop (𝓝 (∫ ω, inner ℝ (ξ ω) (D s' ω - D s ω) ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun ω => ‖ξ ω‖ * ‖D s' ω - D s ω‖) ?_ ?_ hint ?_
    · refine Filter.Eventually.of_forall fun F => ?_
      refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
      exact ((hmeasξ.inner measurable_const).mul
        (measurable_const.inner ((measurable_of_isHM hD s').sub (measurable_of_isHM hD s)))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun F => ae_of_all _ fun ω => ?_
      rw [Real.norm_eq_abs]; exact hbound F ω
    · refine ae_of_all _ fun ω => ?_
      have := b.hasSum_inner_mul_inner (ξ ω) (D s' ω - D s ω)
      exact this
  have hzero : ∀ F : Finset ι, ∫ ω, ∑ k ∈ F, inner ℝ (ξ ω) (b k) *
      inner ℝ (b k) (D s' ω - D s ω) ∂P = 0 := by
    intro F
    rw [integral_finsetSum]
    · exact Finset.sum_eq_zero fun k _ => hterm k
    · intro k _
      exact (hξ2.inner_const (𝕜 := ℝ) (b k)).integrable_mul (hΔ2.const_inner (𝕜 := ℝ) (b k))
  simp_rw [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- `E⟨D_τ,x⟩² = E ∫_0^τ Sg(x,x)` (random covariation density). -/
theorem second_moment_rand (hD : IsHilbertMartingaleWithCovariation P ℱ S D Sg) {τ : ℝ} (hτ : 0 ≤ τ)
    (hτS : τ ≤ S) (x : H) :
    ∫ ω, inner ℝ (D τ ω) x ^ 2 ∂P = ∫ ω, (∫ σ in Set.Icc 0 τ, Sg σ ω x x) ∂P := by
  have hS : 0 ≤ S := hτ.trans hτS
  have hmart := hD.covariation x x
  have h := hmart.setIntegral_eq hτ MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  have h0 : ∫ ω, (inner ℝ (D 0 ω) x * inner ℝ (D 0 ω) x - ∫ σ in Set.Icc 0 0, Sg σ ω x x) ∂P = 0 := by
    have : (fun ω => inner ℝ (D 0 ω) x * inner ℝ (D 0 ω) x - ∫ σ in Set.Icc 0 0, Sg σ ω x x) =ᵐ[P]
        fun _ => (0 : ℝ) := by
      filter_upwards [hD.zero] with ω hω
      simp [hω]
    rw [integral_congr_ae this]; simp
  rw [h0] at h
  have hint : Integrable (fun ω => inner ℝ (D τ ω) x * inner ℝ (D τ ω) x) P :=
    (memLp_inner_aux hD hS x hτS).integrable_mul (memLp_inner_aux hD hS x hτS)
  have hF := hmart.integrable τ
  have hA : Integrable (fun ω => ∫ σ in Set.Icc 0 τ, Sg σ ω x x) P := by
    have := hint.sub hF
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp
  have h2 := h.symm
  rw [integral_sub hint hA] at h2
  simp only [sq]
  linarith

theorem second_moment_incr (hD : IsHilbertMartingaleWithCovariation P ℱ S D Sg) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') (hs'S : s' ≤ S) (x : H) :
    ∫ ω, inner ℝ (D s' ω - D s ω) x ^ 2 ∂P = ∫ ω, (∫ σ in Set.Ioc s s', Sg σ ω x x) ∂P := by
  have hS : 0 ≤ S := hs.trans (hss'.trans hs'S)
  have hs'0 : 0 ≤ s' := hs.trans hss'
  have hL' := memLp_inner_aux hD hS x hs'S
  have hL := memLp_inner_aux hD hS x (hss'.trans hs'S)
  have hmix := LindebergAux.integral_mul_martingale (P := P) ℱ (hD.martingale x) hss'
    (Z := fun ω => inner ℝ (D s ω) x) ((hD.martingale x).1 s) hL hL'
  have i1 : Integrable (fun ω => inner ℝ (D s' ω) x ^ 2) P :=
    (hL'.integrable_mul hL').congr (Filter.Eventually.of_forall fun ω => by simp [sq])
  have i2 : Integrable (fun ω => inner ℝ (D s ω) x ^ 2) P :=
    (hL.integrable_mul hL).congr (Filter.Eventually.of_forall fun ω => by simp [sq])
  have i3 : Integrable (fun ω => inner ℝ (D s ω) x * inner ℝ (D s' ω) x) P := hL.integrable_mul hL'
  have e : ∀ ω, inner ℝ (D s' ω - D s ω) x ^ 2 =
      inner ℝ (D s' ω) x ^ 2 - 2 * (inner ℝ (D s ω) x * inner ℝ (D s' ω) x) + inner ℝ (D s ω) x ^ 2 := by
    intro ω; rw [inner_sub_left]; ring
  simp_rw [e]
  have i13 : Integrable (fun ω => inner ℝ (D s' ω) x ^ 2 - 2 * (inner ℝ (D s ω) x * inner ℝ (D s' ω) x)) P :=
    i1.sub (i3.const_mul 2)
  rw [integral_add i13 i2, integral_sub i1 (i3.const_mul 2), integral_const_mul, hmix,
    second_moment_rand hD hs'0 hs'S x]
  have hs2 : ∫ ω, inner ℝ (D s ω) x * inner ℝ (D s ω) x ∂P = ∫ ω, inner ℝ (D s ω) x ^ 2 ∂P := by
    simp [sq]
  rw [hs2, second_moment_rand hD hs (hss'.trans hs'S) x]
  -- the pathwise difference
  have hent := hD.sigma_entry_int
  have hAint : ∀ τ ∈ Set.Icc (0 : ℝ) S, Integrable (fun ω => ∫ σ in Set.Icc 0 τ, Sg σ ω x x) P := by
    intro τ hτ
    have hint : Integrable (fun ω => inner ℝ (D τ ω) x * inner ℝ (D τ ω) x) P :=
      (memLp_inner_aux hD hS x hτ.2).integrable_mul (memLp_inner_aux hD hS x hτ.2)
    have := hint.sub ((hD.covariation x x).integrable τ)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp
  have hdiff : ∀ᵐ ω ∂P, (∫ σ in Set.Icc 0 s', Sg σ ω x x) - (∫ σ in Set.Icc 0 s, Sg σ ω x x) =
      ∫ σ in Set.Ioc s s', Sg σ ω x x := by
    filter_upwards [hent] with ω hω
    have hI : IntegrableOn (fun σ => Sg σ ω x x) (Set.Icc 0 s') :=
      (hω x x).mono_set (Set.Icc_subset_Icc_right hs'S)
    have hu : Set.Icc (0 : ℝ) s' = Set.Icc 0 s ∪ Set.Ioc s s' := (Set.Icc_union_Ioc_eq_Icc hs hss').symm
    have hd : Disjoint (Set.Icc (0 : ℝ) s) (Set.Ioc s s') := by
      rw [Set.disjoint_left]
      intro σ h1 h2
      exact absurd h2.1 (not_lt.2 h1.2)
    rw [hu, setIntegral_union hd measurableSet_Ioc (hI.mono_set (Set.Icc_subset_Icc_right hss'))
      (hI.mono_set (fun σ h => ⟨hs.trans h.1.le, h.2⟩))]
    ring
  have hrhs : ∫ ω, (∫ σ in Set.Ioc s s', Sg σ ω x x) ∂P =
      ∫ ω, (∫ σ in Set.Icc 0 s', Sg σ ω x x) ∂P - ∫ ω, (∫ σ in Set.Icc 0 s, Sg σ ω x x) ∂P := by
    rw [← integral_sub (hAint s' ⟨hs'0, hs'S⟩) (hAint s ⟨hs, hss'.trans hs'S⟩)]
    exact (integral_congr_ae hdiff).symm
  rw [hrhs]
  ring

/-- Integrability and nonnegativity of the increment of the compensator. -/
lemma compensator_incr_integrable (hD : IsHilbertMartingaleWithCovariation P ℱ S D Sg) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') (hs'S : s' ≤ S) (x : H) :
    Integrable (fun ω => ∫ σ in Set.Ioc s s', Sg σ ω x x) P := by
  have hS : 0 ≤ S := hs.trans (hss'.trans hs'S)
  have hs'0 : 0 ≤ s' := hs.trans hss'
  have hAint : ∀ τ ∈ Set.Icc (0 : ℝ) S, Integrable (fun ω => ∫ σ in Set.Icc 0 τ, Sg σ ω x x) P := by
    intro τ hτ
    have hint : Integrable (fun ω => inner ℝ (D τ ω) x * inner ℝ (D τ ω) x) P :=
      (memLp_inner_aux hD hS x hτ.2).integrable_mul (memLp_inner_aux hD hS x hτ.2)
    have := hint.sub ((hD.covariation x x).integrable τ)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp
  have hdiff : ∀ᵐ ω ∂P, (∫ σ in Set.Icc 0 s', Sg σ ω x x) - (∫ σ in Set.Icc 0 s, Sg σ ω x x) =
      ∫ σ in Set.Ioc s s', Sg σ ω x x := by
    filter_upwards [hD.sigma_entry_int] with ω hω
    have hI : IntegrableOn (fun σ => Sg σ ω x x) (Set.Icc 0 s') :=
      (hω x x).mono_set (Set.Icc_subset_Icc_right hs'S)
    have hu : Set.Icc (0 : ℝ) s' = Set.Icc 0 s ∪ Set.Ioc s s' := (Set.Icc_union_Ioc_eq_Icc hs hss').symm
    have hd : Disjoint (Set.Icc (0 : ℝ) s) (Set.Ioc s s') := by
      rw [Set.disjoint_left]
      intro σ h1 h2
      exact absurd h2.1 (not_lt.2 h1.2)
    rw [hu, setIntegral_union hd measurableSet_Ioc (hI.mono_set (Set.Icc_subset_Icc_right hss'))
      (hI.mono_set (fun σ h => ⟨hs.trans h.1.le, h.2⟩))]
    ring
  have := (hAint s' ⟨hs'0, hs'S⟩).sub (hAint s ⟨hs, hss'.trans hs'S⟩)
  exact this.congr hdiff

/-- The `L²` size of a martingale increment. -/
theorem sq_incr (hD : IsHilbertMartingaleWithCovariation P ℱ S D Sg) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') (hs'S : s' ≤ S) :
    ∫⁻ ω, ‖D s' ω - D s ω‖ₑ ^ 2 ∂P ≤
      ∫⁻ ω, (∫⁻ σ in Set.Ioc s s', ENNReal.ofReal (traceNormForm (Sg σ ω))) ∂P := by
  classical
  have hS : 0 ≤ S := hs.trans (hss'.trans hs'S)
  obtain ⟨ι, hι, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  haveI := hι
  have hmeasΔ : Measurable (fun ω => D s' ω - D s ω) :=
    (measurable_of_isHM hD s').sub (measurable_of_isHM hD s)
  have hΔ2 : MemLp (fun ω => D s' ω - D s ω) 2 P :=
    (memLp_D hD hS (hs.trans hss') hs'S).sub (memLp_D hD hS hs (hss'.trans hs'S))
  -- pointwise expansion
  have hexp : ∀ ω, ‖D s' ω - D s ω‖ₑ ^ 2 =
      ∑' k, ENNReal.ofReal (inner ℝ (D s' ω - D s ω) (b k) ^ 2) := by
    intro ω
    have hsum := b.hasSum_inner_mul_inner (D s' ω - D s ω) (D s' ω - D s ω)
    have hnn : ∀ k, 0 ≤ inner ℝ (D s' ω - D s ω) (b k) ^ 2 := fun k => sq_nonneg _
    have hsq : HasSum (fun k => inner ℝ (D s' ω - D s ω) (b k) ^ 2) (‖D s' ω - D s ω‖ ^ 2) := by
      have e : ∀ k, inner ℝ (D s' ω - D s ω) (b k) * inner ℝ (b k) (D s' ω - D s ω) =
          inner ℝ (D s' ω - D s ω) (b k) ^ 2 := fun k => by
        rw [real_inner_comm (D s' ω - D s ω) (b k)]; ring
      have := hsum
      simp only [e, real_inner_self_eq_norm_sq] at this
      exact this
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsq.summable, hsq.tsum_eq, ← ofReal_norm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
  -- measurability of the coordinate functions
  have hmeask : ∀ k, Measurable (fun ω => ENNReal.ofReal (inner ℝ (D s' ω - D s ω) (b k) ^ 2)) := fun k =>
    ((hmeasΔ.inner measurable_const).pow_const 2).ennreal_ofReal
  have hjm : ∀ x y : H, Measurable (fun p : Ω × ℝ => Sg p.2 p.1 x y) := fun x y =>
    (hD.sigma_meas x y).comp (measurable_swap (α := Ω) (β := ℝ))
  have hmeasσ : ∀ x : H, Measurable (fun ω => ∫⁻ σ in Set.Ioc s s', ENNReal.ofReal (Sg σ ω x x)) := fun x =>
    ((hjm x x).ennreal_ofReal).lintegral_prod_right' (ν := volume.restrict (Set.Ioc s s'))
  -- each coordinate
  have hk : ∀ k, ∫⁻ ω, ENNReal.ofReal (inner ℝ (D s' ω - D s ω) (b k) ^ 2) ∂P =
      ∫⁻ ω, (∫⁻ σ in Set.Ioc s s', ENNReal.ofReal (Sg σ ω (b k) (b k))) ∂P := by
    intro k
    have hint : Integrable (fun ω => inner ℝ (D s' ω - D s ω) (b k) ^ 2) P :=
      (hΔ2.inner_const (𝕜 := ℝ) (b k)).integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => sq_nonneg _),
      second_moment_incr hD hs hss' hs'S (b k)]
    have hnn : ∀ᵐ ω ∂P, ∀ σ ∈ Set.Icc 0 S, 0 ≤ Sg σ ω (b k) (b k) := by
      filter_upwards [hD.sigma_traceClass] with ω hω σ hσ
      exact (hω σ hσ).nonneg _
    rw [ofReal_integral_eq_lintegral_ofReal (compensator_incr_integrable hD hs hss' hs'S (b k))
      (by
        filter_upwards [hnn] with ω hω
        exact setIntegral_nonneg measurableSet_Ioc fun σ hσ =>
          hω σ ⟨hs.trans hσ.1.le, hσ.2.trans hs'S⟩)]
    refine lintegral_congr_ae ?_
    filter_upwards [hnn, hD.sigma_entry_int] with ω hω hent
    rw [ofReal_integral_eq_lintegral_ofReal
      ((hent (b k) (b k)).mono_set (fun σ hσ => ⟨hs.trans hσ.1.le, hσ.2.trans hs'S⟩))
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun σ hσ =>
        hω σ ⟨hs.trans hσ.1.le, hσ.2.trans hs'S⟩))]
  calc ∫⁻ ω, ‖D s' ω - D s ω‖ₑ ^ 2 ∂P
      = ∑' k, ∫⁻ ω, ENNReal.ofReal (inner ℝ (D s' ω - D s ω) (b k) ^ 2) ∂P := by
        simp_rw [hexp]
        exact lintegral_tsum fun k => (hmeask k).aemeasurable
    _ = ∑' k, ∫⁻ ω, (∫⁻ σ in Set.Ioc s s', ENNReal.ofReal (Sg σ ω (b k) (b k))) ∂P := tsum_congr hk
    _ = ∫⁻ ω, ∑' k, (∫⁻ σ in Set.Ioc s s', ENNReal.ofReal (Sg σ ω (b k) (b k))) ∂P :=
        (lintegral_tsum fun k => (hmeasσ (b k)).aemeasurable).symm
    _ ≤ ∫⁻ ω, (∫⁻ σ in Set.Ioc s s', ENNReal.ofReal (traceNormForm (Sg σ ω))) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hD.sigma_traceClass] with ω hω
        have hmσ : ∀ k, AEMeasurable (fun σ => ENNReal.ofReal (Sg σ ω (b k) (b k)))
            (volume.restrict (Set.Ioc s s')) := fun k =>
          (((hjm (b k) (b k)).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal).aemeasurable
        rw [← lintegral_tsum hmσ]
        refine lintegral_mono_ae ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
        have hσ' : σ ∈ Set.Icc (0 : ℝ) S := ⟨hs.trans hσ.1.le, hσ.2.trans hs'S⟩
        obtain ⟨T, hT, -⟩ := (hω σ hσ').hasSum_basis b
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (hω σ hσ').nonneg _) hT.summable]
        exact ENNReal.ofReal_le_ofReal ((hω σ hσ').tsum_basis_le b)

end Incr

end HRS.Uniform.Comp28
