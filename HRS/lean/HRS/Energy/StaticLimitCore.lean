import HRS.Prob.HilbertCLT
import HRS.Energy.StaticLimitTilt

/-!
# The tilted CLT transfer (work package STAT-4.21)

A generic Hilbert-space statement: the `W₂` distance between the tilted law of the normalised
i.i.d. sum and the tilted Gaussian, pushed forward by a `1`-Lipschitz map, is uniformly small.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.StaticLimitAux

section Weight

variable {H : Type*} [NormedAddCommGroup H]

/-- The tilting weight `exp(-(β/2) q(v)²)`. -/
def tw (q : H → ℝ) (β : ℝ) (v : H) : ℝ := Real.exp (-(β / 2) * q v ^ 2)

theorem tw_pos (q : H → ℝ) (β : ℝ) (v : H) : 0 < tw q β v := Real.exp_pos _

theorem tw_le_one (q : H → ℝ) {β : ℝ} (hβ : 0 ≤ β) (v : H) : tw q β v ≤ 1 := by
  unfold tw
  rw [Real.exp_le_one_iff]
  have : 0 ≤ β / 2 * q v ^ 2 := by positivity
  linarith

theorem abs_mul_exp_le (u : ℝ) : |u| * Real.exp (-u ^ 2 / 2) ≤ 1 := by
  have h1 : u ^ 2 / 2 + 1 ≤ Real.exp (u ^ 2 / 2) := by
    have := Real.add_one_le_exp (u ^ 2 / 2); linarith
  have h2 : |u| ≤ u ^ 2 / 2 + 1 := by
    nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have h3 : Real.exp (-u ^ 2 / 2) = (Real.exp (u ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [h3, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  exact h2.trans h1

theorem exp_gauss_lip {β : ℝ} (hβ : 0 ≤ β) (a b : ℝ) :
    |Real.exp (-(β / 2) * a ^ 2) - Real.exp (-(β / 2) * b ^ 2)| ≤ Real.sqrt β * |a - b| := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.exp (-(β / 2) * t ^ 2))
      (Real.exp (-(β / 2) * t ^ 2) * (-(β / 2) * (2 * t))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(β / 2) * t ^ 2) (-(β / 2) * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (-(β / 2)))
    exact h1.exp
  have hbd : ∀ t : ℝ, ‖Real.exp (-(β / 2) * t ^ 2) * (-(β / 2) * (2 * t))‖ ≤ Real.sqrt β := by
    intro t
    have hs := Real.sq_sqrt hβ
    have hs0 : 0 ≤ Real.sqrt β := Real.sqrt_nonneg _
    set s := Real.sqrt β with hsdef
    rw [Real.norm_eq_abs]
    have key := abs_mul_exp_le (s * t)
    have e : Real.exp (-(β / 2) * t ^ 2) * (-(β / 2) * (2 * t)) =
        -(s * ((s * t) * Real.exp (-(s * t) ^ 2 / 2))) := by
      have : -(β / 2) * t ^ 2 = -(s * t) ^ 2 / 2 := by rw [← hs]; ring
      rw [this, ← hs]; ring
    have h : |s * t * Real.exp (-(s * t) ^ 2 / 2)| ≤ 1 := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]; exact key
    rw [e, abs_neg, abs_mul, abs_of_nonneg hs0]
    calc s * |s * t * Real.exp (-(s * t) ^ 2 / 2)| ≤ s * 1 := by gcongr
      _ = s := mul_one s
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => Real.exp (-(β / 2) * t ^ 2))
    (f' := fun t => Real.exp (-(β / 2) * t ^ 2) * (-(β / 2) * (2 * t))) (s := Set.univ)
    (C := Real.sqrt β)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hbd t) convex_univ (Set.mem_univ b)
    (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using this

theorem tw_lip (q : H → ℝ) {β : ℝ} (hβ : 0 ≤ β) (hq : ∀ x y, |q x - q y| ≤ ‖x - y‖) (x y : H) :
    |tw q β x - tw q β y| ≤ Real.sqrt β * ‖x - y‖ := by
  unfold tw
  refine (exp_gauss_lip hβ (q x) (q y)).trans ?_
  gcongr
  exact hq x y

end Weight


section IID

variable {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The infinite product law. -/
abbrev Pinf (μ : Measure X) : Measure (ℕ → X) := Measure.infinitePi fun _ => μ

/-- The `i`-th summand. -/
def Xi (Y : X → H) (i : ℕ) (ω : ℕ → X) : H := Y (ω i)

/-- The normalised sum over a finite configuration. -/
def Ssum (Y : X → H) (N : ℕ) (z : Fin N → X) : H := (Real.sqrt N)⁻¹ • ∑ j, Y (z j)

theorem iid_Xi {Y : X → H} (hY : Measurable Y) : HRS.IsIIDCopies (Pinf μ) (Xi Y) := by
  refine ⟨?_, fun i j => ?_⟩
  · exact ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ => Y)
      (fun _ => hY)
  · have h : ∀ i, HRS.law (Pinf μ) (Xi Y i) = μ.map Y := by
      intro i
      unfold HRS.law Xi
      have := Measure.infinitePi_map_eval (μ := fun _ : ℕ => μ) i
      have e : (fun ω : ℕ → X => Y (ω i)) = Y ∘ (fun ω : ℕ → X => ω i) := rfl
      rw [e, ← Measure.map_map hY (measurable_pi_apply i), this]
    rw [h i, h j]

theorem map_restrict_eq (N : ℕ) :
    (Pinf μ).map (fun (ω : ℕ → X) (j : Fin N) => ω j) = Measure.pi fun _ : Fin N => μ := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hr : Measurable (fun (ω : ℕ → X) (j : Fin N) => ω j) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  rw [Measure.map_apply hr (MeasurableSet.univ_pi hs)]
  have e : ((fun (ω : ℕ → X) (j : Fin N) => ω j) ⁻¹' Set.univ.pi s) =
      Set.pi (Finset.range N : Set ℕ) (fun i => if h : i < N then s ⟨i, h⟩ else Set.univ) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Finset.coe_range,
      Set.mem_Iio]
    constructor
    · intro h i hi
      simp only [hi, dite_true]
      exact h ⟨i, hi⟩
    · intro h j
      have := h j.1 j.2
      simpa [j.2] using this
  rw [e]
  have := Measure.infinitePi_pi (μ := fun _ : ℕ => μ) (s := Finset.range N)
    (t := fun i => if h : i < N then s ⟨i, h⟩ else Set.univ) (fun i hi => by
      have hi' : i < N := Finset.mem_range.mp hi
      simpa [hi'] using hs ⟨i, hi'⟩)
  rw [this, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [j.2]

theorem law_normalizedSum (Y : X → H) (hY : Measurable Y) (N : ℕ) :
    HRS.law (Pinf μ) (HRS.normalizedSum (Xi Y) N) =
      (Measure.pi fun _ : Fin N => μ).map (Ssum Y N) := by
  rw [← map_restrict_eq μ N]
  unfold HRS.law
  have hm : Measurable (Ssum Y N) := by
    unfold Ssum
    exact (Finset.measurable_sum _ fun j _ => hY.comp (measurable_pi_apply j)).const_smul _
  have hr : Measurable (fun (ω : ℕ → X) (j : Fin N) => ω j) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  rw [Measure.map_map hm hr]
  congr 1
  funext ω
  simp only [Function.comp, HRS.normalizedSum, Ssum, Xi]
  rw [Finset.sum_range (fun i => Y (ω i))]

end IID


section Moments

variable {H : Type*} [NormedAddCommGroup H] [MeasurableSpace H]

/-- Jensen lower bound for the tilting mass. -/
theorem jensen_mass (ν : Measure H) [IsProbabilityMeasure ν] (q : H → ℝ) (hq : Measurable q)
    {β : ℝ} (hβ : 0 ≤ β) {J : ℝ} (hint : Integrable (fun v => q v ^ 2) ν)
    (hJ : ∫ v, q v ^ 2 ∂ν ≤ J) : Real.exp (-(β / 2) * J) ≤ ∫ v, tw q β v ∂ν := by
  have hfi : Integrable (fun v => -(β / 2) * q v ^ 2) ν := hint.const_mul _
  have hgi : Integrable (Real.exp ∘ fun v => -(β / 2) * q v ^ 2) ν := by
    refine Integrable.of_bound (C := 1) ?_ ?_
    · exact (Real.measurable_exp.comp (measurable_const.mul (hq.pow_const 2))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun v => ?_
      have := tw_pos q β v
      have h1 := tw_le_one q hβ v
      rw [Real.norm_eq_abs]
      show |tw q β v| ≤ 1
      rw [abs_of_pos this]
      exact h1
  have := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hfi hgi
  refine le_trans ?_ this
  apply Real.exp_le_exp.mpr
  rw [integral_const_mul]
  have : 0 ≤ β / 2 := by positivity
  nlinarith

end Moments


section SMoments

variable {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem law_Xi {Y : X → H} (hY : Measurable Y) (i : ℕ) :
    HRS.law (Pinf μ) (Xi Y i) = μ.map Y := by
  unfold HRS.law Xi
  have := Measure.infinitePi_map_eval (μ := fun _ : ℕ => μ) i
  have e : (fun ω : ℕ → X => Y (ω i)) = Y ∘ (fun ω : ℕ → X => ω i) := rfl
  rw [e, ← Measure.map_map hY (measurable_pi_apply i), this]

theorem measurable_Xi {Y : X → H} (hY : Measurable Y) (i : ℕ) : Measurable (Xi Y i) :=
  hY.comp (measurable_pi_apply i)

theorem measurable_S {Y : X → H} (hY : Measurable Y) (N : ℕ) :
    Measurable (HRS.normalizedSum (Xi Y) N) := by
  unfold HRS.normalizedSum
  exact (Finset.measurable_sum _ fun i _ => measurable_Xi hY i).const_smul _

theorem S_bound {Y : X → H} {M : ℝ} (hYM : ∀ x, ‖Y x‖ ≤ M) (N : ℕ) (ω : ℕ → X) :
    ‖HRS.normalizedSum (Xi Y) N ω‖ ≤ (Real.sqrt N)⁻¹ * (N * M) := by
  unfold HRS.normalizedSum
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range N, ‖Xi Y i ω‖ ≤ ∑ _i ∈ Finset.range N, M :=
        Finset.sum_le_sum fun i _ => hYM _
    _ = N * M := by simp

theorem fourth_S {Y : X → H} (hY : Measurable Y) {M : ℝ} (hM : 0 ≤ M) (hYM : ∀ x, ‖Y x‖ ≤ M)
    (hmean : ∫ x, Y x ∂μ = 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖HRS.normalizedSum (Xi Y) N ω‖ ^ 4 ∂(Pinf μ) ≤ 4 * M ^ 4 := by
  have hmean' : ∫ ω, Xi Y 0 ω ∂(Pinf μ) = 0 := by
    have := integral_map (μ := Pinf μ) (measurable_pi_apply (0 : ℕ)).aemeasurable
      hY.aestronglyMeasurable
    have e := Measure.infinitePi_map_eval (μ := fun _ : ℕ => μ) 0
    rw [e] at this
    unfold Xi
    rw [← this, hmean]
  have hL4 : MemLp (Xi Y 0) 4 (Pinf μ) :=
    MemLp.of_bound (measurable_Xi hY 0).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => hYM _)
  have h := HRS.iid_fourth_moment_bound (Pinf μ) (Xi Y) (iid_Xi μ hY)
    (fun i => (measurable_Xi hY i).aemeasurable) hL4 hmean' N hN
  refine h.trans ?_
  have hb : ∀ k : ℕ, ∫ ω, ‖Xi Y 0 ω‖ ^ k ∂(Pinf μ) ≤ M ^ k := by
    intro k
    calc ∫ ω, ‖Xi Y 0 ω‖ ^ k ∂(Pinf μ) ≤ ∫ _ω, M ^ k ∂(Pinf μ) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
            (integrable_const _) (Filter.Eventually.of_forall fun ω => ?_)
          exact pow_le_pow_left₀ (norm_nonneg _) (hYM _) k
      _ = M ^ k := by simp
  have h4 := hb 4
  have h2 := hb 2
  have h2' : 0 ≤ ∫ ω, ‖Xi Y 0 ω‖ ^ 2 ∂(Pinf μ) := integral_nonneg fun ω => by positivity
  have hN' : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hN)
  have hNn : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have h4' : 0 ≤ ∫ ω, ‖Xi Y 0 ω‖ ^ 4 ∂(Pinf μ) := integral_nonneg fun ω => by positivity
  have : (∫ ω, ‖Xi Y 0 ω‖ ^ 2 ∂(Pinf μ)) ^ 2 ≤ (M ^ 2) ^ 2 := pow_le_pow_left₀ h2' h2 2
  nlinarith [mul_le_mul hN' h4 h4' zero_le_one, pow_nonneg hM 4]

theorem second_S {Y : X → H} (hY : Measurable Y) {M : ℝ} (hM : 0 ≤ M) (hYM : ∀ x, ‖Y x‖ ≤ M)
    (hmean : ∫ x, Y x ∂μ = 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖HRS.normalizedSum (Xi Y) N ω‖ ^ 2 ∂(Pinf μ) ≤ 2 * M ^ 2 := by
  set S := HRS.normalizedSum (Xi Y) N with hS
  have hSm : Measurable S := measurable_S hY N
  set C := (Real.sqrt N)⁻¹ * (N * M)
  have hb : ∀ ω, ‖S ω‖ ≤ C := fun ω => S_bound hYM N ω
  have hi2 : Integrable (fun ω => ‖S ω‖ ^ 2) (Pinf μ) :=
    Integrable.of_bound (C := C ^ 2) (hSm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb ω) 2)
  have hi4 : Integrable (fun ω => ‖S ω‖ ^ 4) (Pinf μ) :=
    Integrable.of_bound (C := C ^ 4) (hSm.norm.pow_const 4).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb ω) 4)
  have hj := (convexOn_pow 2).map_integral_le (μ := Pinf μ) (f := fun ω => ‖S ω‖ ^ 2)
    (continuousOn_pow 2) isClosed_Ici (Filter.Eventually.of_forall fun ω => by
      simp only [Set.mem_Ici]; positivity) hi2 (by
        refine hi4.congr (Filter.Eventually.of_forall fun ω => ?_)
        simp only [Function.comp]; ring)
  have h4 := fourth_S μ hY hM hYM hmean N hN
  have e : ∫ ω, (‖S ω‖ ^ 2) ^ 2 ∂(Pinf μ) = ∫ ω, ‖S ω‖ ^ 4 ∂(Pinf μ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show (‖S ω‖ ^ 2) ^ 2 = ‖S ω‖ ^ 4
    ring
  have hnn : 0 ≤ ∫ ω, ‖S ω‖ ^ 2 ∂(Pinf μ) := integral_nonneg fun ω => by positivity
  rw [e] at hj
  nlinarith [sq_nonneg (∫ ω, ‖S ω‖ ^ 2 ∂(Pinf μ) - 2 * M ^ 2), pow_nonneg hM 2]

end SMoments


section Main

variable {X : Type} [MeasurableSpace X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

theorem exists_delta (L c Q ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ L * δ ≤ c ∧ tiltBound L c Q δ ≤ ε := by
  have hcont : Continuous fun δ : ℝ => tiltBound L c Q δ := by
    unfold tiltBound
    fun_prop
  have h0 : tiltBound L c Q 0 = 0 := by simp [tiltBound]
  have h1 : ∀ᶠ δ in 𝓝 (0 : ℝ), tiltBound L c Q δ < ε := by
    have := hcont.tendsto 0
    rw [h0] at this
    exact this.eventually (Iio_mem_nhds hε)
  have h2 : ∀ᶠ δ in 𝓝 (0 : ℝ), L * δ < c := by
    have : Continuous fun δ : ℝ => L * δ := by fun_prop
    have := this.tendsto 0
    rw [mul_zero] at this
    exact this.eventually (Iio_mem_nhds hc)
  obtain ⟨δ, ⟨h1', h2'⟩, hpos⟩ := (((h1.and h2).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
  exact ⟨δ, hpos, h2'.le, h1'.le⟩

theorem tilt_clt_transfer (q : H → ℝ) (hqm : Measurable q) (hq1 : ∀ x y, |q x - q y| ≤ ‖x - y‖)
    (hq0 : ∀ v, |q v| ≤ ‖v‖)
    (T : H → E) (hT : Measurable T) (hTL : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (K : ℕ → Submodule ℝ H) [∀ n, (K n).HasOrthogonalProjection]
    (hK : ∀ n, FiniteDimensional ℝ (K n)) (τ : ℕ → ℝ) (hτ : Tendsto τ atTop (𝓝 0))
    (M : ℝ) (hM : 0 ≤ M) (B : ℝ) (hB : 0 ≤ B) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (μ : Measure X) [IsProbabilityMeasure μ] (Y : X → H),
      Measurable Y → (∀ x, ‖Y x‖ ≤ M) → ∫ x, Y x ∂μ = 0 →
      (∀ n x, ‖Y x - (K n).starProjection (Y x)‖ ^ 2 ≤ τ n) →
      ∀ β ∈ Set.Icc (0 : ℝ) B, ∀ Γ : Measure H, HRS.IsCenteredGaussian Γ →
        (∀ x y, ProbabilityTheory.covarianceBilin Γ x y =
          ProbabilityTheory.covarianceBilin (μ.map Y) x y) →
        wassersteinE 2 ((tiltMeasure (tw q β) Γ).map T)
          ((tiltMeasure (tw q β) ((Measure.pi fun _ : Fin N => μ).map (Ssum Y N))).map T) ≤
          ENNReal.ofReal ε := by
  intro ε hε
  have hc : 0 < Real.exp (-(B * M ^ 2)) / 2 := by positivity
  obtain ⟨δ, hδ, hLδ, hbd⟩ := exists_delta (Real.sqrt B) (Real.exp (-(B * M ^ 2)) / 2) (4 * M ^ 4)
    ε hc hε
  obtain ⟨N₀', hN₀'⟩ := HRS.hilbert_clt_uniform K hK τ hτ M (δ / 2) (by positivity)
  refine ⟨max N₀' 1, fun N hN μ _ Y hYm hYM hYmean hYtail β hβ Γ hΓ hcov => ?_⟩
  have hN0 : N₀' ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hβ0 : 0 ≤ β := hβ.1
  have hβB : β ≤ B := hβ.2
  haveI : IsProbabilityMeasure Γ := hΓ.1.toIsProbabilityMeasure
  -- the CLT
  have hmean' : ∫ ω, Xi Y 0 ω ∂(Pinf μ) = 0 := by
    have := integral_map (μ := Pinf μ) (measurable_pi_apply (0 : ℕ)).aemeasurable
      hYm.aestronglyMeasurable
    have e := Measure.infinitePi_map_eval (μ := fun _ : ℕ => μ) 0
    rw [e] at this
    unfold Xi
    rw [← this, hYmean]
  have hL2 : MemLp (Xi Y 0) 2 (Pinf μ) :=
    MemLp.of_bound (measurable_Xi hYm 0).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => hYM _)
  have hclt := hN₀' N hN0 (Pinf μ) (Xi Y) (iid_Xi μ hYm)
    (fun i => (measurable_Xi hYm i).aemeasurable) hL2 hmean'
    (fun n => by
      calc ∫ ω, ‖Xi Y 0 ω - (K n).starProjection (Xi Y 0 ω)‖ ^ 2 ∂(Pinf μ) ≤
          ∫ _ω, τ n ∂(Pinf μ) := integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun ω => by positivity) (integrable_const _)
            (Filter.Eventually.of_forall fun ω => hYtail n _)
        _ = τ n := by simp)
    (Filter.Eventually.of_forall fun ω => hYM _) Γ hΓ
    (fun x y => by rw [hcov x y, law_Xi μ hYm 0])
  set ν := HRS.law (Pinf μ) (HRS.normalizedSum (Xi Y) N) with hν
  haveI : IsProbabilityMeasure ν :=
    haveI : AEMeasurable (HRS.normalizedSum (Xi Y) N) (Pinf μ) := (measurable_S hYm N).aemeasurable
    inferInstance
  have hW : wassersteinE 2 Γ ν < ENNReal.ofReal δ := by
    rw [HRS.HilbertCLTAux.wassersteinE_comm]
    refine lt_of_le_of_lt hclt ?_
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr (by linarith)
  -- moment bounds
  have h4 := fourth_S μ hYm hM hYM hYmean N hN1
  have h2 := second_S μ hYm hM hYM hYmean N hN1
  have hSm := measurable_S hYm N
  have hbS := S_bound (Y := Y) hYM N
  set C := (Real.sqrt N)⁻¹ * (N * M)
  have hQ : ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 4) ∂ν ≤ ENNReal.ofReal (4 * M ^ 4) := by
    have hm4 : Measurable fun y : H => ENNReal.ofReal (‖y‖ ^ 4) :=
      ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 4)
    rw [hν]; unfold HRS.law
    rw [lintegral_map hm4 hSm]
    have hi4 : Integrable (fun ω => ‖HRS.normalizedSum (Xi Y) N ω‖ ^ 4) (Pinf μ) :=
      Integrable.of_bound (C := C ^ 4) (hSm.norm.pow_const 4).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hbS ω) 4)
    rw [← ofReal_integral_eq_lintegral_ofReal hi4 (Filter.Eventually.of_forall fun ω => by positivity)]
    exact ENNReal.ofReal_le_ofReal h4
  have hA₂ : 2 * (Real.exp (-(B * M ^ 2)) / 2) ≤ ∫ v, tw q β v ∂ν := by
    have hqsq : Integrable (fun v => q v ^ 2) ν := by
      rw [hν]; unfold HRS.law
      rw [integrable_map_measure (hqm.pow_const 2).aestronglyMeasurable hSm.aemeasurable]
      refine Integrable.of_bound (C := C ^ 2) ((hqm.comp hSm).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      show q (HRS.normalizedSum (Xi Y) N ω) ^ 2 ≤ C ^ 2
      calc q (HRS.normalizedSum (Xi Y) N ω) ^ 2 = |q (HRS.normalizedSum (Xi Y) N ω)| ^ 2 :=
            (sq_abs _).symm
        _ ≤ ‖HRS.normalizedSum (Xi Y) N ω‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hq0 _) 2
        _ ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hbS ω) 2
    have hJ : ∫ v, q v ^ 2 ∂ν ≤ 2 * M ^ 2 := by
      rw [hν]; unfold HRS.law
      rw [integral_map hSm.aemeasurable (hqm.pow_const 2).aestronglyMeasurable]
      refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
        ?_ (Filter.Eventually.of_forall fun ω => ?_)) h2
      · refine Integrable.of_bound (C := C ^ 2) (hSm.norm.pow_const 2).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbS ω) 2
      · show q (HRS.normalizedSum (Xi Y) N ω) ^ 2 ≤ ‖HRS.normalizedSum (Xi Y) N ω‖ ^ 2
        calc q (HRS.normalizedSum (Xi Y) N ω) ^ 2 = |q (HRS.normalizedSum (Xi Y) N ω)| ^ 2 :=
              (sq_abs _).symm
          _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (hq0 _) 2
    have hj := jensen_mass ν q hqm hβ0 hqsq hJ
    have hexp : Real.exp (-(B * M ^ 2)) ≤ Real.exp (-(β / 2) * (2 * M ^ 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg M]
    linarith
  have hwm : Measurable (tw q β) :=
    Real.measurable_exp.comp (measurable_const.mul (hqm.pow_const 2))
  have key := tilt_W2_le (tw q β) hwm (fun x => (tw_pos q β x).le) (tw_le_one q hβ0)
    (Real.sqrt B) (Real.sqrt_nonneg _)
    (fun x y => (tw_lip q hβ0 hq1 x y).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hβB) (norm_nonneg _)))
    T hT hTL Γ ν (Real.exp (-(B * M ^ 2)) / 2) hc hA₂ (4 * M ^ 4) hQ δ hδ.le hLδ hW
  have e : (Measure.pi fun _ : Fin N => μ).map (Ssum Y N) = ν := (law_normalizedSum μ Y hYm N).symm
  rw [e]
  exact key.trans (ENNReal.ofReal_le_ofReal hbd)

end Main

end HRS.StaticLimitAux
