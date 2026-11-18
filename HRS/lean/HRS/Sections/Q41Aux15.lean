import HRS.Sections.Q41Aux3

/-!
# Packet Q41, helper 15: the susceptibility form as a bounded bilinear form on continuous functions

For the frozen data `(V, ρ_β)` the form `C(φ,ψ) = susceptibilityCov …` is `⟨Yφ, R Yψ⟩_{L²(μ)}` with
`Yφ` the `L²(μ)` class of `φ - ∫φ dμ`.  Hence it is bilinear, unchanged by adding constants and
bounded by `K ‖φ‖_∞ ‖ψ‖_∞` on continuous functions.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Q41

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

variable {d : ℕ}

/-- The `L²(μ)` class of the mean-zero projection of a function. -/
def q41_Y (ρβ : Torus d → ℝ) [IsFiniteMeasure (withDensityReal ρβ)] (φ : Torus d → ℝ) :
    Lp ℝ 2 (withDensityReal ρβ) :=
  pL (withDensityReal ρβ) (fun _ => projMean (withDensityReal ρβ) φ) 0

section Cov

variable {ρβ : Torus d → ℝ} [IsProbabilityMeasure (withDensityReal ρβ)]

lemma q41_projMean_cont {φ : Torus d → ℝ} (hφ : Continuous φ) :
    Continuous (projMean (withDensityReal ρβ) φ) := by
  unfold projMean
  exact hφ.sub continuous_const

lemma q41_Y_ae {φ : Torus d → ℝ} (hφ : Continuous φ) :
    ⇑(q41_Y ρβ φ) =ᵐ[withDensityReal ρβ] projMean (withDensityReal ρβ) φ :=
  pL_ae (G := fun _ => projMean (withDensityReal ρβ) φ) (v := 0) (q41_projMean_cont hφ)

lemma q41_pair_lin {φ ψ : Torus d → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) (a b : ℝ) :
    pair (withDensityReal ρβ) (fun x => a * φ x + b * ψ x) =
      a * pair (withDensityReal ρβ) φ + b * pair (withDensityReal ρβ) ψ := by
  have h1 : Integrable φ (withDensityReal ρβ) :=
    hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable ψ (withDensityReal ρβ) :=
    hψ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold pair
  rw [integral_add (h1.const_mul a) (h2.const_mul b), integral_const_mul, integral_const_mul]

lemma q41_pair_add_const {φ : Torus d → ℝ} (hφ : Continuous φ) (c : ℝ) :
    pair (withDensityReal ρβ) (fun x => φ x + c) = pair (withDensityReal ρβ) φ + c := by
  have h1 : Integrable φ (withDensityReal ρβ) :=
    hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold pair
  rw [integral_add h1 (integrable_const c)]
  simp

lemma q41_Y_lin {φ ψ : Torus d → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) (a b : ℝ) :
    q41_Y ρβ (fun x => a * φ x + b * ψ x) = a • q41_Y ρβ φ + b • q41_Y ρβ ψ := by
  have hc : Continuous fun x => a * φ x + b * ψ x := (continuous_const.mul hφ).add (continuous_const.mul hψ)
  refine Lp.ext ?_
  filter_upwards [q41_Y_ae (ρβ := ρβ) hc, q41_Y_ae (ρβ := ρβ) hφ, q41_Y_ae (ρβ := ρβ) hψ,
    Lp.coeFn_add (a • q41_Y ρβ φ) (b • q41_Y ρβ ψ), Lp.coeFn_smul a (q41_Y ρβ φ),
    Lp.coeFn_smul b (q41_Y ρβ ψ)] with x h1 h2 h3 h4 h5 h6
  rw [h1, h4]
  simp only [Pi.add_apply]
  rw [h5, h6]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2, h3]
  simp only [projMean]
  rw [q41_pair_lin hφ hψ]
  ring

lemma q41_Y_add_const {φ : Torus d → ℝ} (hφ : Continuous φ) (c : ℝ) :
    q41_Y ρβ (fun x => φ x + c) = q41_Y ρβ φ := by
  have hc : Continuous fun x => φ x + c := hφ.add continuous_const
  refine Lp.ext ?_
  filter_upwards [q41_Y_ae (ρβ := ρβ) hc, q41_Y_ae (ρβ := ρβ) hφ] with x h1 h2
  rw [h1, h2]
  simp only [projMean]
  rw [q41_pair_add_const hφ]
  ring

lemma q41_Y_norm_le {φ : Torus d → ℝ} (hφ : Continuous φ) {a : ℝ} (ha : ∀ x, |φ x| ≤ a) :
    ‖q41_Y ρβ φ‖ ≤ 2 * a := by
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha 0)
  have hpair : |pair (withDensityReal ρβ) φ| ≤ a := by
    unfold pair
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρβ) (f := φ) (C := a)
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using ha x)
    simpa [Real.norm_eq_abs] using this
  have h := Lp.norm_le_of_ae_bound (f := q41_Y ρβ φ) (C := 2 * a) (by positivity) (by
    filter_upwards [q41_Y_ae (ρβ := ρβ) hφ] with x hx
    rw [hx, Real.norm_eq_abs]
    simp only [projMean]
    calc |φ x - pair (withDensityReal ρβ) φ| ≤ |φ x| + |pair (withDensityReal ρβ) φ| := abs_sub _ _
      _ ≤ 2 * a := by linarith [ha x])
  simpa [measureUnivNNReal] using h

end Cov

/-- The algebraic and analytic properties of the susceptibility form used below. -/
structure CovProps (Cv : (Torus d → ℝ) → (Torus d → ℝ) → ℝ) : Prop where
  lin1 : ∀ (φ1 φ2 ψ : Torus d → ℝ) (a b : ℝ), Continuous φ1 → Continuous φ2 → Continuous ψ →
    Cv (fun x => a * φ1 x + b * φ2 x) ψ = a * Cv φ1 ψ + b * Cv φ2 ψ
  lin2 : ∀ (φ ψ1 ψ2 : Torus d → ℝ) (a b : ℝ), Continuous φ → Continuous ψ1 → Continuous ψ2 →
    Cv φ (fun x => a * ψ1 x + b * ψ2 x) = a * Cv φ ψ1 + b * Cv φ ψ2
  const1 : ∀ (φ ψ : Torus d → ℝ) (c : ℝ), Continuous φ → Continuous ψ →
    Cv (fun x => φ x + c) ψ = Cv φ ψ
  const2 : ∀ (φ ψ : Torus d → ℝ) (c : ℝ), Continuous φ → Continuous ψ →
    Cv φ (fun x => ψ x + c) = Cv φ ψ
  bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (φ ψ : Torus d → ℝ) (a b : ℝ), Continuous φ → Continuous ψ →
    (∀ x, |φ x| ≤ a) → (∀ x, |ψ x| ≤ b) → |Cv φ ψ| ≤ K * a * b
  symm : ∀ (φ ψ : Torus d → ℝ), Continuous φ → Continuous ψ → Cv φ ψ = Cv ψ φ

theorem q41_covProps (hd : 1 ≤ d) {s β c₀ Λ₀ : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s (2 * mStar d + 4) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ) :
    CovProps (d := d) (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β) := by
  have hKS := KS_of_frozen hd H
  have hρc : Continuous ρβ := H.cont (by have := ClassicalPart.three_le_mStar d; omega)
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := hKS.isProb
  obtain ⟨R, hRA, hAR, hRs, hRpos⟩ := exists_inverse hd s H.hs0 H.hsd hKS hρc β H.hβ.le
  have hrep : ∀ φ ψ : Torus d → ℝ, Continuous φ → Continuous ψ →
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ ψ =
        inner ℝ (q41_Y ρβ φ) (R (q41_Y ρβ ψ)) := fun φ ψ hφ hψ =>
    susceptibilityCov_eq_inner hd s H.hs0 H.hsd hKS hρc β H.hβ R hAR φ ψ hψ _ _ (q41_Y_ae hφ)
      (q41_Y_ae hψ)
  have hlc : ∀ (φ1 φ2 : Torus d → ℝ) (a b : ℝ), Continuous φ1 → Continuous φ2 →
      Continuous fun x => a * φ1 x + b * φ2 x := fun φ1 φ2 a b h1 h2 =>
    (continuous_const.mul h1).add (continuous_const.mul h2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ1 φ2 ψ a b h1 h2 hψ
    rw [hrep _ _ (hlc _ _ a b h1 h2) hψ, hrep _ _ h1 hψ, hrep _ _ h2 hψ, q41_Y_lin h1 h2,
      inner_add_left, real_inner_smul_left, real_inner_smul_left]
  · intro φ ψ1 ψ2 a b hφ h1 h2
    rw [hrep _ _ hφ (hlc _ _ a b h1 h2), hrep _ _ hφ h1, hrep _ _ hφ h2, q41_Y_lin h1 h2,
      map_add, map_smul, map_smul, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  · intro φ ψ c hφ hψ
    rw [hrep _ _ (show Continuous fun x => φ x + c from hφ.add continuous_const) hψ, hrep _ _ hφ hψ, q41_Y_add_const hφ]
  · intro φ ψ c hφ hψ
    rw [hrep _ _ hφ (show Continuous fun x => ψ x + c from hψ.add continuous_const), hrep _ _ hφ hψ, q41_Y_add_const hψ]
  · refine ⟨‖R‖ * 4, by positivity, fun φ ψ a b hφ hψ ha hb => ?_⟩
    have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha 0)
    have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0)
    rw [hrep _ _ hφ hψ]
    have h1 := q41_Y_norm_le (ρβ := ρβ) hφ ha
    have h2 := q41_Y_norm_le (ρβ := ρβ) hψ hb
    calc |inner ℝ (q41_Y ρβ φ) (R (q41_Y ρβ ψ))| ≤ ‖q41_Y ρβ φ‖ * ‖R (q41_Y ρβ ψ)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖q41_Y ρβ φ‖ * (‖R‖ * ‖q41_Y ρβ ψ‖) :=
          mul_le_mul_of_nonneg_left (R.le_opNorm _) (norm_nonneg _)
      _ ≤ (2 * a) * (‖R‖ * (2 * b)) := by gcongr
      _ = ‖R‖ * 4 * a * b := by ring
  · intro φ ψ hφ hψ
    rw [hrep _ _ hφ hψ, hrep _ _ hψ hφ, ← hRs, real_inner_comm]

section Derived

variable {Cv : (Torus d → ℝ) → (Torus d → ℝ) → ℝ}

theorem CovProps.sum1 (hC : CovProps (d := d) Cv) {ι : Type*} (t : Finset ι) (c : ι → ℝ)
    (g : ι → Torus d → ℝ) (hg : ∀ i, Continuous (g i)) (ψ : Torus d → ℝ) (hψ : Continuous ψ) :
    Cv (fun x => ∑ i ∈ t, c i * g i x) ψ = ∑ i ∈ t, c i * Cv (g i) ψ := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h := hC.lin1 (fun _ => 0) (fun _ => 0) ψ 0 0 continuous_const continuous_const hψ
    simpa using h
  | insert a t ha ih =>
    have hs : Continuous fun x => ∑ i ∈ t, c i * g i x :=
      continuous_finset_sum _ fun i _ => continuous_const.mul (hg i)
    have := hC.lin1 (g a) (fun x => ∑ i ∈ t, c i * g i x) ψ (c a) 1 (hg a) hs hψ
    simp only [Finset.sum_insert ha]
    rw [show (fun x => c a * g a x + ∑ i ∈ t, c i * g i x) =
        fun x => c a * g a x + 1 * ∑ i ∈ t, c i * g i x by funext x; ring, this, ih]
    ring

theorem CovProps.sum2 (hC : CovProps (d := d) Cv) {ι : Type*} (t : Finset ι) (c : ι → ℝ)
    (g : ι → Torus d → ℝ) (hg : ∀ i, Continuous (g i)) (φ : Torus d → ℝ) (hφ : Continuous φ) :
    Cv φ (fun x => ∑ i ∈ t, c i * g i x) = ∑ i ∈ t, c i * Cv φ (g i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h := hC.lin2 φ (fun _ => 0) (fun _ => 0) 0 0 hφ continuous_const continuous_const
    simpa using h
  | insert a t ha ih =>
    have hs : Continuous fun x => ∑ i ∈ t, c i * g i x :=
      continuous_finset_sum _ fun i _ => continuous_const.mul (hg i)
    have := hC.lin2 φ (g a) (fun x => ∑ i ∈ t, c i * g i x) (c a) 1 hφ (hg a) hs
    simp only [Finset.sum_insert ha]
    rw [show (fun x => c a * g a x + ∑ i ∈ t, c i * g i x) =
        fun x => c a * g a x + 1 * ∑ i ∈ t, c i * g i x by funext x; ring, this, ih]
    ring

/-- Continuity of the form under uniform convergence in both slots. -/
theorem CovProps.tendsto (hC : CovProps (d := d) Cv) {f g : Torus d → ℝ} (hf : Continuous f)
    (hg : Continuous g) {fn gn : ℕ → Torus d → ℝ} (hfn : ∀ n, Continuous (fn n))
    (hgn : ∀ n, Continuous (gn n)) {ef eg : ℕ → ℝ} (hef : Tendsto ef atTop (𝓝 0))
    (heg : Tendsto eg atTop (𝓝 0)) (hf' : ∀ n x, |fn n x - f x| ≤ ef n)
    (hg' : ∀ n x, |gn n x - g x| ≤ eg n) :
    Tendsto (fun n => Cv (fn n) (gn n)) atTop (𝓝 (Cv f g)) := by
  obtain ⟨K, hK0, hK⟩ := hC.bound
  obtain ⟨bf, hbf⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨bg, hbg⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  have hbf' : ∀ x, |f x| ≤ bf := fun x => by simpa [Real.norm_eq_abs] using hbf x (Set.mem_univ x)
  have hbg' : ∀ x, |g x| ≤ bg := fun x => by simpa [Real.norm_eq_abs] using hbg x (Set.mem_univ x)
  have hbf0 : 0 ≤ bf := (abs_nonneg _).trans (hbf' 0)
  have hbg0 : 0 ≤ bg := (abs_nonneg _).trans (hbg' 0)
  have hef0 : ∀ n, 0 ≤ ef n := fun n => (abs_nonneg _).trans (hf' n 0)
  have heg0 : ∀ n, 0 ≤ eg n := fun n => (abs_nonneg _).trans (hg' n 0)
  have hdecomp : ∀ n, Cv (fn n) (gn n) - Cv f g =
      Cv (fun x => fn n x - f x) (gn n) + Cv f (fun x => gn n x - g x) := by
    intro n
    have e1 := hC.lin1 f (fun x => fn n x - f x) (gn n) 1 1 hf ((hfn n).sub hf) (hgn n)
    have e2 := hC.lin2 f g (fun x => gn n x - g x) 1 1 hf hg ((hgn n).sub hg)
    have hfn' : (fun x => 1 * f x + 1 * (fn n x - f x)) = fn n := by funext x; ring
    have hgn' : (fun x => 1 * g x + 1 * (gn n x - g x)) = gn n := by funext x; ring
    rw [hfn'] at e1
    rw [hgn'] at e2
    rw [e1, e2]
    ring
  have hbound : ∀ n, |Cv (fn n) (gn n) - Cv f g| ≤ K * ef n * (bg + eg n) + K * bf * eg n := by
    intro n
    rw [hdecomp n]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact hK _ _ _ _ ((hfn n).sub hf) (hgn n) (fun x => hf' n x) (fun x => by
        have := hg' n x
        have h2 : |gn n x| ≤ |g x| + |gn n x - g x| := by
          calc |gn n x| = |g x + (gn n x - g x)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        linarith [hbg' x])
    · exact hK _ _ _ _ hf ((hgn n).sub hg) hbf' (fun x => hg' n x)
  have hlim : Tendsto (fun n => K * ef n * (bg + eg n) + K * bf * eg n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => K * ef n * (bg + eg n)) atTop (𝓝 (K * 0 * (bg + 0))) :=
      ((hef.const_mul K).mul (heg.const_add bg))
    have h2 : Tendsto (fun n => K * bf * eg n) atTop (𝓝 (K * bf * 0)) := heg.const_mul _
    simpa using h1.add h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  rw [Real.norm_eq_abs]
  exact hbound n

end Derived

end HRS.Q41
