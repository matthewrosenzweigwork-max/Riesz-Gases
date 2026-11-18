import HRS.MS.SA16PRiesz5

/-!
# SA16P, part 6: Hölder, vector-valued Riesz representation, weak convergence from dense pairings

* `sa16p_holder`: `|∫ F G| ≤ ‖F‖_p ‖G‖_q` for `F ∈ L^p`, `G ∈ L^q`.
* `sa16p_riesz_vec`: for a bounded functional `ℓ` on `L^p(μ; ℝ^ι)` (`ι` finite, sup norm) there are `g_i ∈ L^q`
  with `ℓ u = ∑_i ∫ u_i g_i`.
* `sa16p_weak_of_pairings`: if `(u_n)` is bounded in `L^p(μ;ℝ^ι)`, `u` is bounded, and `∫ (u_n)_i ψ → ∫ u_i ψ` for all
  `ψ` in a DENSE subset of `L^q`, then `ℓ u_n → ℓ u` for every `ℓ` in the strong dual (weak convergence).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P

section Vec
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {p q : ℝ}

lemma sa16p_Lp_norm_eq {E : Type*} [NormedAddCommGroup E] (hp : 0 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (F : Lp E (ENNReal.ofReal p) μ) : ‖F‖ = (∫ x, ‖F x‖ ^ p ∂μ) ^ (1 / p) := by
  have hp1 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  rw [Lp.norm_def, (Lp.memLp F).eLpNorm_eq_integral_rpow_norm hp1 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _),
    ENNReal.toReal_ofReal hp.le, one_div]

/-- Hölder's inequality for `L^p × L^q`. -/
lemma sa16p_holder (hpq : p.HolderConjugate q) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (F : Lp ℝ (ENNReal.ofReal p) μ) (G : Lp ℝ (ENNReal.ofReal q) μ) :
    |∫ x, F x * G x ∂μ| ≤ ‖F‖ * ‖G‖ := by
  have h1 : |∫ x, F x * G x ∂μ| ≤ ∫ x, ‖F x‖ * ‖G x‖ ∂μ := by
    have := norm_integral_le_integral_norm (μ := μ) (fun x => F x * G x)
    simpa [norm_mul] using this
  refine h1.trans ?_
  rw [sa16p_Lp_norm_eq hpq.pos F, sa16p_Lp_norm_eq hpq.symm.pos G]
  exact integral_mul_norm_le_Lp_mul_Lq hpq (Lp.memLp F) (Lp.memLp G)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the coordinate projection `L^p(μ;ℝ^ι) → L^p(μ;ℝ)` -/
def sa16p_proj (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (i : ι) :
    Lp (ι → ℝ) (ENNReal.ofReal p) μ →L[ℝ] Lp ℝ (ENNReal.ofReal p) μ :=
  ContinuousLinearMap.compLpL (ENNReal.ofReal p) μ (ContinuousLinearMap.proj i)

/-- the coordinate embedding `L^p(μ;ℝ) → L^p(μ;ℝ^ι)` -/
def sa16p_emb (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (i : ι) :
    Lp ℝ (ENNReal.ofReal p) μ →L[ℝ] Lp (ι → ℝ) (ENNReal.ofReal p) μ :=
  ContinuousLinearMap.compLpL (ENNReal.ofReal p) μ (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)

lemma sa16p_proj_coe [Fact (1 ≤ ENNReal.ofReal p)] (i : ι) (u : Lp (ι → ℝ) (ENNReal.ofReal p) μ) :
    (sa16p_proj p i u : α → ℝ) =ᵐ[μ] fun x => u x i :=
  ContinuousLinearMap.coeFn_compLpL _ u

lemma sa16p_proj_norm_le [Fact (1 ≤ ENNReal.ofReal p)] (i : ι) (u : Lp (ι → ℝ) (ENNReal.ofReal p) μ) :
    ‖sa16p_proj p i u‖ ≤ ‖u‖ := by
  have h1 : ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
      simpa using norm_le_pi_norm f i)
  have h2 := ContinuousLinearMap.le_opNorm (sa16p_proj (μ := μ) p i) u
  have h3 : ‖sa16p_proj (μ := μ) p i‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans h1
  nlinarith [norm_nonneg u, norm_nonneg (sa16p_proj p i u), norm_nonneg (sa16p_proj (μ := μ) p i)]

lemma sa16p_coeFn_sum {E : Type*} [NormedAddCommGroup E] {r : ℝ≥0∞} [Fact (1 ≤ r)] {κ : Type*}
    (F : κ → Lp E r μ) (s : Finset κ) :
    (↑↑(∑ i ∈ s, F i) : α → E) =ᵐ[μ] ∑ i ∈ s, (↑↑(F i) : α → E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact Lp.coeFn_zero E r μ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2]
    simp

lemma sa16p_sum_emb_proj [Fact (1 ≤ ENNReal.ofReal p)] (u : Lp (ι → ℝ) (ENNReal.ofReal p) μ) :
    ∑ i, sa16p_emb p i (sa16p_proj p i u) = u := by
  apply Lp.ext
  have h1 : ∀ i, (sa16p_emb p i (sa16p_proj p i u) : α → ι → ℝ) =ᵐ[μ]
      fun x => Pi.single i ((sa16p_proj p i u : α → ℝ) x) := fun i =>
    ContinuousLinearMap.coeFn_compLpL _ _
  have h2 : ∀ᵐ x ∂μ, ∀ i, (sa16p_proj p i u : α → ℝ) x = u x i :=
    ae_all_iff.2 fun i => sa16p_proj_coe i u
  have h3 := ae_all_iff.2 h1
  filter_upwards [sa16p_coeFn_sum (fun i => sa16p_emb p i (sa16p_proj p i u)) Finset.univ, h3, h2] with x h4 h5 h6
  rw [h4, Finset.sum_apply]
  have : ∀ i, (↑↑(sa16p_emb p i (sa16p_proj p i u)) : α → ι → ℝ) x = Pi.single i (u x i) := fun i => by
    rw [h5 i, h6 i]
  simp only [this]
  exact Finset.univ_sum_single (u x)

theorem sa16p_riesz_vec (hpq : p.HolderConjugate q) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)] (ℓ : Lp (ι → ℝ) (ENNReal.ofReal p) μ →L[ℝ] ℝ) :
    ∃ g : ι → α → ℝ, (∀ i, Measurable (g i) ∧ MemLp (g i) (ENNReal.ofReal q) μ) ∧
      ∀ u : Lp (ι → ℝ) (ENNReal.ofReal p) μ, ℓ u = ∑ i, ∫ x, u x i * g i x ∂μ := by
  have := fun i : ι => sa16p_riesz hpq (ℓ.comp (sa16p_emb p i))
  choose g hgm hgmem hgn hrep using this
  refine ⟨g, fun i => ⟨hgm i, hgmem i⟩, fun u => ?_⟩
  conv_lhs => rw [← sa16p_sum_emb_proj u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hrep i (sa16p_proj p i u)
  simp only [ContinuousLinearMap.comp_apply] at this
  rw [this]
  exact integral_congr_ae (by filter_upwards [sa16p_proj_coe i u] with x hx; rw [hx])

/-- the pairing of the `i`-th component with an `L^q` function -/
def sa16p_pair (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (i : ι) (u : Lp (ι → ℝ) (ENNReal.ofReal p) μ)
    (H : α → ℝ) : ℝ := ∫ x, u x i * H x ∂μ

lemma sa16p_pair_bound (hpq : p.HolderConjugate q) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)] (i : ι) (u : Lp (ι → ℝ) (ENNReal.ofReal p) μ)
    (H : Lp ℝ (ENNReal.ofReal q) μ) : |sa16p_pair p i u H| ≤ ‖u‖ * ‖H‖ := by
  have h1 := sa16p_holder hpq (sa16p_proj p i u) H
  have h2 : ∫ x, (sa16p_proj p i u : α → ℝ) x * H x ∂μ = sa16p_pair p i u H :=
    integral_congr_ae (by filter_upwards [sa16p_proj_coe i u] with x hx; rw [hx])
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (sa16p_proj_norm_le i u) (norm_nonneg _))

lemma sa16p_pair_sub (hpq : p.HolderConjugate q) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)] (i : ι) (u : Lp (ι → ℝ) (ENNReal.ofReal p) μ)
    (H₁ H₂ : Lp ℝ (ENNReal.ofReal q) μ) :
    sa16p_pair p i u (H₁ - H₂ : Lp ℝ (ENNReal.ofReal q) μ) = sa16p_pair p i u H₁ - sa16p_pair p i u H₂ := by
  have := hpq.ennrealOfReal
  have hu : MemLp (fun x => u x i) (ENNReal.ofReal p) μ := by
    refine (Lp.memLp (sa16p_proj p i u)).ae_eq ?_
    exact sa16p_proj_coe i u
  have i1 : Integrable (fun x => u x i * H₁ x) μ := hu.integrable_mul (Lp.memLp H₁)
  have i2 : Integrable (fun x => u x i * H₂ x) μ := hu.integrable_mul (Lp.memLp H₂)
  unfold sa16p_pair
  rw [← integral_sub i1 i2]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub H₁ H₂] with x hx
  rw [hx, Pi.sub_apply, mul_sub]

lemma sa16p_pair_integrable (hpq : p.HolderConjugate q) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)] (i : ι) (u : Lp (ι → ℝ) (ENNReal.ofReal p) μ)
    (H : Lp ℝ (ENNReal.ofReal q) μ) : Integrable (fun x => u x i * H x) μ := by
  have := hpq.ennrealOfReal
  have hu : MemLp (fun x => u x i) (ENNReal.ofReal p) μ :=
    (Lp.memLp (sa16p_proj p i u)).ae_eq (sa16p_proj_coe i u)
  exact hu.integrable_mul (Lp.memLp H)

lemma sa16p_pair_add (hpq : p.HolderConjugate q) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)] (i : ι) (u : Lp (ι → ℝ) (ENNReal.ofReal p) μ)
    (H₁ H₂ : Lp ℝ (ENNReal.ofReal q) μ) :
    sa16p_pair p i u (H₁ + H₂ : Lp ℝ (ENNReal.ofReal q) μ) = sa16p_pair p i u H₁ + sa16p_pair p i u H₂ := by
  unfold sa16p_pair
  rw [← integral_add (sa16p_pair_integrable hpq i u H₁) (sa16p_pair_integrable hpq i u H₂)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add H₁ H₂] with x hx
  rw [hx, Pi.add_apply, mul_add]

lemma sa16p_pair_smul (hpq : p.HolderConjugate q) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)] (i : ι) (u : Lp (ι → ℝ) (ENNReal.ofReal p) μ) (c : ℝ)
    (H : Lp ℝ (ENNReal.ofReal q) μ) :
    sa16p_pair p i u (c • H : Lp ℝ (ENNReal.ofReal q) μ) = c * sa16p_pair p i u H := by
  unfold sa16p_pair
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c H] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Weak convergence from pairings against a dense class.** -/
theorem sa16p_weak_of_pairings (hpq : p.HolderConjugate q) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)] (D : Set (Lp ℝ (ENNReal.ofReal q) μ)) (hD : Dense D) {B : ℝ}
    (u : ℕ → Lp (ι → ℝ) (ENNReal.ofReal p) μ) (u₀ : Lp (ι → ℝ) (ENNReal.ofReal p) μ)
    (hu : ∀ n, ‖u n‖ ≤ B) (hu₀ : ‖u₀‖ ≤ B)
    (hconv : ∀ i, ∀ ψ ∈ D, Tendsto (fun n => sa16p_pair p i (u n) ψ) atTop
      (𝓝 (sa16p_pair p i u₀ ψ)))
    (ℓ : Lp (ι → ℝ) (ENNReal.ofReal p) μ →L[ℝ] ℝ) :
    Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ u₀)) := by
  obtain ⟨g, hg, hrep⟩ := sa16p_riesz_vec hpq ℓ
  simp_rw [hrep]
  refine tendsto_finset_sum _ fun i _ => ?_
  set G : Lp ℝ (ENNReal.ofReal q) μ := (hg i).2.toLp (g i) with hG
  have hGg : ∀ v : Lp (ι → ℝ) (ENNReal.ofReal p) μ, sa16p_pair p i v G = ∫ x, v x i * g i x ∂μ :=
    fun v => integral_congr_ae (by
      filter_upwards [MemLp.coeFn_toLp (hg i).2] with x hx
      rw [hx])
  simp_rw [← hGg]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hu 0)
  have hδ : 0 < ε / (4 * (B + 1)) := by positivity
  obtain ⟨ψ, hψD, hψ⟩ := hD.exists_dist_lt G hδ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv i ψ hψD) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hGψ : ‖G - ψ‖ < ε / (4 * (B + 1)) := by rwa [dist_eq_norm] at hψ
  have e1 := sa16p_pair_sub hpq i (u n) G ψ
  have e2 := sa16p_pair_sub hpq i u₀ G ψ
  have b1 := sa16p_pair_bound hpq i (u n) (G - ψ)
  have b2 := sa16p_pair_bound hpq i u₀ (G - ψ)
  have hN' := hN n hn
  rw [Real.dist_eq] at hN' ⊢
  have c1 : ‖u n‖ * ‖G - ψ‖ ≤ B * (ε / (4 * (B + 1))) :=
    mul_le_mul (hu n) hGψ.le (norm_nonneg _) hB0
  have c2 : ‖u₀‖ * ‖G - ψ‖ ≤ B * (ε / (4 * (B + 1))) :=
    mul_le_mul hu₀ hGψ.le (norm_nonneg _) hB0
  have c3 : B * (ε / (4 * (B + 1))) ≤ ε / 4 := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  set d : α → ℝ := (((G - ψ : Lp ℝ (ENNReal.ofReal q) μ)) : α → ℝ) with hd
  have key : sa16p_pair p i (u n) (G : α → ℝ) - sa16p_pair p i u₀ (G : α → ℝ) =
      sa16p_pair p i (u n) d + (sa16p_pair p i (u n) (ψ : α → ℝ) - sa16p_pair p i u₀ (ψ : α → ℝ)) -
        sa16p_pair p i u₀ d := by
    rw [hd, e1, e2]; ring
  rw [key]
  have t1 := abs_add_le (sa16p_pair p i (u n) d)
    (sa16p_pair p i (u n) (ψ : α → ℝ) - sa16p_pair p i u₀ (ψ : α → ℝ))
  have t2 := abs_sub (sa16p_pair p i (u n) d + (sa16p_pair p i (u n) (ψ : α → ℝ) -
    sa16p_pair p i u₀ (ψ : α → ℝ))) (sa16p_pair p i u₀ d)
  linarith

/-- **Existence of a weak limit** from convergence of the pairings against a dense class. -/
theorem sa16p_exists_weak_limit (hpq : p.HolderConjugate q) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)] (D : Set (Lp ℝ (ENNReal.ofReal q) μ)) (hD : Dense D) {B : ℝ}
    (u : ℕ → Lp (ι → ℝ) (ENNReal.ofReal p) μ) (hu : ∀ n, ‖u n‖ ≤ B)
    (hconv : ∀ i, ∀ ψ ∈ D, ∃ c, Tendsto (fun n => sa16p_pair p i (u n) ψ) atTop (𝓝 c)) :
    ∃ u₀ : Lp (ι → ℝ) (ENNReal.ofReal p) μ, ‖u₀‖ ≤ (Fintype.card ι : ℝ) * B ∧
      ∀ i, ∀ ψ : Lp ℝ (ENNReal.ofReal q) μ,
        Tendsto (fun n => sa16p_pair p i (u n) ψ) atTop (𝓝 (sa16p_pair p i u₀ ψ)) := by
  have hB0 : ∀ n, 0 ≤ B := fun n => (norm_nonneg _).trans (hu n)
  -- Step 1: for every `i` and every `ψ`, the pairings converge
  have hall : ∀ i, ∀ ψ : Lp ℝ (ENNReal.ofReal q) μ, ∃ c, Tendsto (fun n => sa16p_pair p i (u n) ψ) atTop (𝓝 c) := by
    intro i ψ
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
    have hB := hB0 0
    have hδ : 0 < ε / (4 * (B + 1)) := by positivity
    obtain ⟨ψ', hψ'D, hψ'⟩ := hD.exists_dist_lt ψ hδ
    obtain ⟨c, hc⟩ := hconv i ψ' hψ'D
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hc.cauchySeq (ε / 2) (by positivity)
    refine ⟨N, fun n hn m hm => ?_⟩
    have hψψ : ‖ψ - ψ'‖ < ε / (4 * (B + 1)) := by rwa [dist_eq_norm] at hψ'
    have e1 := sa16p_pair_sub hpq i (u n) ψ ψ'
    have e2 := sa16p_pair_sub hpq i (u m) ψ ψ'
    have b1 := sa16p_pair_bound hpq i (u n) (ψ - ψ')
    have b2 := sa16p_pair_bound hpq i (u m) (ψ - ψ')
    have hNN := hN n hn m hm
    rw [Real.dist_eq] at hNN ⊢
    have c1 : ‖u n‖ * ‖ψ - ψ'‖ ≤ B * (ε / (4 * (B + 1))) :=
      mul_le_mul (hu n) hψψ.le (norm_nonneg _) hB
    have c2 : ‖u m‖ * ‖ψ - ψ'‖ ≤ B * (ε / (4 * (B + 1))) :=
      mul_le_mul (hu m) hψψ.le (norm_nonneg _) hB
    have c3 : B * (ε / (4 * (B + 1))) ≤ ε / 4 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    set d : α → ℝ := (((ψ - ψ' : Lp ℝ (ENNReal.ofReal q) μ)) : α → ℝ) with hd
    have key : sa16p_pair p i (u n) (ψ : α → ℝ) - sa16p_pair p i (u m) (ψ : α → ℝ) =
        sa16p_pair p i (u n) d + (sa16p_pair p i (u n) (ψ' : α → ℝ) - sa16p_pair p i (u m) (ψ' : α → ℝ)) -
          sa16p_pair p i (u m) d := by
      rw [hd, e1, e2]; ring
    rw [key]
    have t1 := abs_add_le (sa16p_pair p i (u n) d)
      (sa16p_pair p i (u n) (ψ' : α → ℝ) - sa16p_pair p i (u m) (ψ' : α → ℝ))
    have t2 := abs_sub (sa16p_pair p i (u n) d + (sa16p_pair p i (u n) (ψ' : α → ℝ) -
      sa16p_pair p i (u m) (ψ' : α → ℝ))) (sa16p_pair p i (u m) d)
    linarith
  -- Step 2: the limit functionals
  choose Λ hΛ using hall
  have hΛlin : ∀ i, ∀ ψ₁ ψ₂ : Lp ℝ (ENNReal.ofReal q) μ, Λ i (ψ₁ + ψ₂) = Λ i ψ₁ + Λ i ψ₂ := by
    intro i ψ₁ ψ₂
    refine tendsto_nhds_unique (hΛ i (ψ₁ + ψ₂)) ?_
    have := (hΛ i ψ₁).add (hΛ i ψ₂)
    refine this.congr fun n => ?_
    rw [sa16p_pair_add hpq]
  have hΛsmul : ∀ i, ∀ (c : ℝ) (ψ : Lp ℝ (ENNReal.ofReal q) μ), Λ i (c • ψ) = c * Λ i ψ := by
    intro i c ψ
    refine tendsto_nhds_unique (hΛ i (c • ψ)) ?_
    have := (hΛ i ψ).const_mul c
    refine this.congr fun n => ?_
    rw [sa16p_pair_smul hpq]
  have hΛb : ∀ i, ∀ ψ : Lp ℝ (ENNReal.ofReal q) μ, ‖Λ i ψ‖ ≤ B * ‖ψ‖ := by
    intro i ψ
    have h1 := (hΛ i ψ).norm
    refine le_of_tendsto h1 (Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs]
    exact (sa16p_pair_bound hpq i (u n) ψ).trans (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg _))
  let L : ι → Lp ℝ (ENNReal.ofReal q) μ →L[ℝ] ℝ := fun i =>
    LinearMap.mkContinuous
      { toFun := Λ i
        map_add' := hΛlin i
        map_smul' := fun c ψ => by simpa using hΛsmul i c ψ } B (fun ψ => by
          simpa [mul_comm] using hΛb i ψ)
  have hLapp : ∀ i ψ, L i ψ = Λ i ψ := fun i ψ => rfl
  have hLn : ∀ i, ‖L i‖ ≤ B := fun i =>
    ContinuousLinearMap.opNorm_le_bound _ (hB0 0) (fun ψ => by rw [hLapp]; simpa [mul_comm] using hΛb i ψ)
  -- Step 3: Riesz for each functional
  have hR := fun i => sa16p_riesz hpq.symm (L i)
  choose g hgm hgmem hgn hrep using hR
  set G : ι → Lp ℝ (ENNReal.ofReal p) μ := fun i => (hgmem i).toLp (g i) with hG
  have hGnorm : ∀ i, ‖G i‖ ≤ B := by
    intro i
    rw [hG, Lp.norm_toLp]
    have := (hgn i)
    have h2 : eLpNorm (g i) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B :=
      this.trans (ENNReal.ofReal_le_ofReal (hLn i))
    exact (ENNReal.toReal_le_of_le_ofReal (hB0 0) h2)
  refine ⟨∑ i, sa16p_emb p i (G i), ?_, fun i ψ => ?_⟩
  · calc ‖∑ i, sa16p_emb p i (G i)‖ ≤ ∑ i, ‖sa16p_emb p i (G i)‖ := norm_sum_le _ _
      _ ≤ ∑ i : ι, B := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : ‖(ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i : ℝ →L[ℝ] (ι → ℝ))‖ ≤ 1 :=
          ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun a => by
            rw [one_mul]
            refine (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2 fun j => ?_
            by_cases hj : j = i
            · subst hj; simp
            · simp [hj])
        have h2 := ContinuousLinearMap.le_opNorm (sa16p_emb (μ := μ) p i) (G i)
        have h3 : ‖sa16p_emb (μ := μ) p i‖ ≤ 1 :=
          (ContinuousLinearMap.norm_compLpL_le _).trans h1
        nlinarith [norm_nonneg (G i), norm_nonneg (sa16p_emb (μ := μ) p i), hGnorm i]
      _ = (Fintype.card ι : ℝ) * B := by simp
  · have hcoe : ∀ᵐ x ∂μ, (↑↑(∑ j, sa16p_emb p j (G j)) : α → ι → ℝ) x i = g i x := by
      have h1 : ∀ j, (sa16p_emb p j (G j) : α → ι → ℝ) =ᵐ[μ]
          fun x => Pi.single j ((G j : α → ℝ) x) := fun j => ContinuousLinearMap.coeFn_compLpL _ _
      have h3 := ae_all_iff.2 h1
      have h5 : ∀ j, (G j : α → ℝ) =ᵐ[μ] g j := fun j => MemLp.coeFn_toLp (hgmem j)
      have h6 := ae_all_iff.2 h5
      filter_upwards [sa16p_coeFn_sum (fun j => sa16p_emb p j (G j)) Finset.univ, h3, h6]
        with x h4 h5' h6'
      rw [h4, Finset.sum_apply, Finset.sum_apply]
      have : ∀ j, (↑↑(sa16p_emb p j (G j)) : α → ι → ℝ) x i = if i = j then g j x else 0 := fun j => by
        rw [h5' j, Pi.single_apply, h6' j]
      simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hpair : sa16p_pair p i (∑ j, sa16p_emb p j (G j)) ψ = Λ i ψ := by
      rw [← hLapp, hrep i ψ]
      unfold sa16p_pair
      refine integral_congr_ae ?_
      filter_upwards [hcoe] with x hx
      rw [hx, mul_comm]
    rw [hpair]
    exact hΛ i ψ

end Vec

end HRS.Whole.AppendixA.Phase2SA16P
