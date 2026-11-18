import HRS.MC.CepP2Aux1

/-!
# Packet CEPP2 (aux 2): Fourier-side functions `C_g, S_g` and the symbol identities
-/

open MeasureTheory

noncomputable section
namespace HRS.MC.CepP2

variable {n : ℕ} {O : Set (XS n)}

/-- The weak equation `∫ feq Φ dρ = 0` for all test functions supported in `O`. -/
def WeakEq (O : Set (XS n)) (invβ : ℝ) (b : XS n → EuclideanSpace ℝ (Fin n)) (ρ : Measure (XS n)) :
    Prop :=
  ∀ Φ : XS n → ℝ, ContDiff ℝ smTop Φ → HasCompactSupport Φ → tsupport Φ ⊆ O →
    ∫ p, feq invβ b Φ p ∂ρ = 0

/-- Cosine transform `C_g(ζ) = ∫ g cos ℓ_ζ dρ`. -/
def Cf (ρ : Measure (XS n)) (g : XS n → ℝ) (ζ : XS n) : ℝ := ∫ p, g p * Real.cos (ell ζ p) ∂ρ

/-- Sine transform `S_g(ζ) = ∫ g sin ℓ_ζ dρ`. -/
def Sf (ρ : Measure (XS n)) (g : XS n → ℝ) (ζ : XS n) : ℝ := ∫ p, g p * Real.sin (ell ζ p) ∂ρ

/-- `N_g = C_g² + S_g²`. -/
def Nf (ρ : Measure (XS n)) (g : XS n → ℝ) (ζ : XS n) : ℝ := Cf ρ g ζ ^ 2 + Sf ρ g ζ ^ 2

lemma continuous_ell_apply (ζ : XS n) : Continuous fun p => ell ζ p := (ell ζ).continuous

lemma isTest_mul_cos {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) {g : XS n → ℝ}
    (hg : IsTest O g) (ζ : XS n) : Integrable (fun p => g p * Real.cos (ell ζ p)) ρ := by
  refine integrable_of_supp hρ (hg.1.continuous.mul (Real.continuous_cos.comp (ell ζ).continuous))
    (hg.2.1.mul_right (f' := fun p => Real.cos (ell ζ p))) ?_
  exact (tsupport_mul_subset_left (f := g) (g := fun p => Real.cos (ell ζ p))).trans hg.2.2

lemma isTest_mul_sin {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) {g : XS n → ℝ}
    (hg : IsTest O g) (ζ : XS n) : Integrable (fun p => g p * Real.sin (ell ζ p)) ρ := by
  refine integrable_of_supp hρ (hg.1.continuous.mul (Real.continuous_sin.comp (ell ζ).continuous))
    (hg.2.1.mul_right (f' := fun p => Real.sin (ell ζ p))) ?_
  exact (tsupport_mul_subset_left (f := g) (g := fun p => Real.sin (ell ζ p))).trans hg.2.2

/-- The mass `M_g = ∫ |g| dρ`. -/
def Mf (ρ : Measure (XS n)) (g : XS n → ℝ) : ℝ := ∫ p, |g p| ∂ρ

lemma abs_Cf_le {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) {g : XS n → ℝ}
    (hg : IsTest O g) (ζ : XS n) : |Cf ρ g ζ| ≤ Mf ρ g := by
  have h := (hg.integrable hρ).abs
  have := norm_integral_le_of_norm_le (μ := ρ) (f := fun p => g p * Real.cos (ell ζ p))
    h (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
  simpa [Cf, Mf] using this

lemma abs_Sf_le {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) {g : XS n → ℝ}
    (hg : IsTest O g) (ζ : XS n) : |Sf ρ g ζ| ≤ Mf ρ g := by
  have h := (hg.integrable hρ).abs
  have := norm_integral_le_of_norm_le (μ := ρ) (f := fun p => g p * Real.sin (ell ζ p))
    h (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
  simpa [Sf, Mf] using this

lemma Nf_le {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) {g : XS n → ℝ}
    (hg : IsTest O g) (ζ : XS n) : Nf ρ g ζ ≤ 2 * Mf ρ g ^ 2 := by
  have h1 := abs_Cf_le hρ hg ζ
  have h2 := abs_Sf_le hρ hg ζ
  have h3 : Cf ρ g ζ ^ 2 ≤ Mf ρ g ^ 2 := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
  have h4 : Sf ρ g ζ ^ 2 ≤ Mf ρ g ^ 2 := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
  unfold Nf
  linarith

lemma Nf_nonneg (ρ : Measure (XS n)) (g : XS n → ℝ) (ζ : XS n) : 0 ≤ Nf ρ g ζ := by
  unfold Nf; positivity

lemma continuous_Cf {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) {g : XS n → ℝ}
    (hg : IsTest O g) : Continuous (Cf ρ g) := by
  refine continuous_of_dominated (bound := fun p => |g p|) (fun ζ => (isTest_mul_cos hρ hg ζ).1)
    (fun ζ => Filter.Eventually.of_forall fun p => ?_) (hg.integrable hρ).abs
    (Filter.Eventually.of_forall fun p => ?_)
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · exact continuous_const.mul (Real.continuous_cos.comp (by
      simp only [ell_apply]
      fun_prop))

lemma continuous_Sf {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) {g : XS n → ℝ}
    (hg : IsTest O g) : Continuous (Sf ρ g) := by
  refine continuous_of_dominated (bound := fun p => |g p|) (fun ζ => (isTest_mul_sin hρ hg ζ).1)
    (fun ζ => Filter.Eventually.of_forall fun p => ?_) (hg.integrable hρ).abs
    (Filter.Eventually.of_forall fun p => ?_)
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  · exact continuous_const.mul (Real.continuous_sin.comp (by
      simp only [ell_apply]
      fun_prop))


section identities

variable {invβ : ℝ} {b : XS n → EuclideanSpace ℝ (Fin n)} {ρ : Measure (XS n)} {χ : XS n → ℝ}

/-- Integral of the `τ, ξ`-combination. -/
lemma integral_combo {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤)
    (hO : IsOpen O) (hb : ContDiffOn ℝ smTop b O) (invβ : ℝ) {χ : XS n → ℝ} (hχ : IsTest O χ)
    (ζ : XS n) (ψ : XS n → ℝ) (hψc : ∀ g, IsTest O g → Integrable (fun p => g p * ψ p) ρ) :
    ∫ p, (ζ.1 * (χ p * ψ p) + ∑ k, ζ.2 k * (gone invβ b χ k p * ψ p)) ∂ρ =
      ζ.1 * ∫ p, χ p * ψ p ∂ρ + ∑ k, ζ.2 k * ∫ p, gone invβ b χ k p * ψ p ∂ρ := by
  rw [integral_add ((hψc χ hχ).const_mul _)
    (integrable_finsetSum _ fun k _ => (hψc _ (isTest_gone hO hb invβ hχ k)).const_mul _),
    integral_const_mul, integral_finset_sum _ fun k _ =>
      (hψc _ (isTest_gone hO hb invβ hχ k)).const_mul _]
  simp only [integral_const_mul]

/-- First real identity: `a C_χ + τ S_χ = C_{g0} − ξ·S_{G1}` in the form `… = 0`. -/
lemma identity_cos (hO : IsOpen O) (hb : ContDiffOn ℝ smTop b O)
    (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) (hW : WeakEq O invβ b ρ)
    (hχ : IsTest O χ) (ζ : XS n) :
    Cf ρ (feq invβ b χ) ζ - ζ.1 * Sf ρ χ ζ - ∑ k, ζ.2 k * Sf ρ (gone invβ b χ k) ζ
      - invβ * ‖ζ.2‖ ^ 2 * Cf ρ χ ζ = 0 := by
  have hΦ : IsTest O (fun q => χ q * Real.cos (ell ζ q)) := by
    refine ⟨hχ.1.mul (Real.contDiff_cos.comp (ell ζ).contDiff), hχ.2.1.mul_right, ?_⟩
    exact (tsupport_mul_subset_left (f := χ) (g := fun p => Real.cos (ell ζ p))).trans hχ.2.2
  have h := hW _ hΦ.1 hΦ.2.1 hΦ.2.2
  have e : (fun p => feq invβ b (fun q => χ q * Real.cos (ell ζ q)) p) =
      fun p => feq invβ b χ p * Real.cos (ell ζ p)
        - (ζ.1 * (χ p * Real.sin (ell ζ p)) + ∑ k, ζ.2 k * (gone invβ b χ k p * Real.sin (ell ζ p)))
        - invβ * ‖ζ.2‖ ^ 2 * (χ p * Real.cos (ell ζ p)) := by
    funext p
    rw [feq_cos invβ b hχ.1 ζ p, add_mul, Finset.sum_mul]
    simp only [mul_assoc]
  have h2 : ∫ p, (feq invβ b χ p * Real.cos (ell ζ p)
        - (ζ.1 * (χ p * Real.sin (ell ζ p)) + ∑ k, ζ.2 k * (gone invβ b χ k p * Real.sin (ell ζ p)))
        - invβ * ‖ζ.2‖ ^ 2 * (χ p * Real.cos (ell ζ p))) ∂ρ = 0 := by
    refine (integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)).trans h
    exact (congrFun e p).symm
  have hsin : ∀ g, IsTest O g → Integrable (fun p => g p * Real.sin (ell ζ p)) ρ :=
    fun g hg => isTest_mul_sin hρ hg ζ
  have iA := isTest_mul_cos hρ (isTest_feq hO hb invβ hχ) ζ
  have iB : Integrable (fun p => ζ.1 * (χ p * Real.sin (ell ζ p))
      + ∑ k, ζ.2 k * (gone invβ b χ k p * Real.sin (ell ζ p))) ρ :=
    ((hsin χ hχ).const_mul _).add (integrable_finsetSum _ fun k _ =>
      (hsin _ (isTest_gone hO hb invβ hχ k)).const_mul _)
  have iC := (isTest_mul_cos hρ hχ ζ).const_mul (invβ * ‖ζ.2‖ ^ 2)
  have iAB : Integrable (fun p => feq invβ b χ p * Real.cos (ell ζ p)
      - (ζ.1 * (χ p * Real.sin (ell ζ p)) + ∑ k, ζ.2 k * (gone invβ b χ k p * Real.sin (ell ζ p)))) ρ :=
    iA.sub iB
  rw [integral_sub iAB iC, integral_sub iA iB, integral_const_mul,
    integral_combo hρ hO hb invβ hχ ζ (fun p => Real.sin (ell ζ p)) hsin] at h2
  unfold Cf Sf
  linarith

/-- Second real identity (sine test function). -/
lemma identity_sin (hO : IsOpen O) (hb : ContDiffOn ℝ smTop b O)
    (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) (hW : WeakEq O invβ b ρ)
    (hχ : IsTest O χ) (ζ : XS n) :
    Sf ρ (feq invβ b χ) ζ + ζ.1 * Cf ρ χ ζ + ∑ k, ζ.2 k * Cf ρ (gone invβ b χ k) ζ
      - invβ * ‖ζ.2‖ ^ 2 * Sf ρ χ ζ = 0 := by
  have hΦ : IsTest O (fun q => χ q * Real.sin (ell ζ q)) := by
    refine ⟨hχ.1.mul (Real.contDiff_sin.comp (ell ζ).contDiff), hχ.2.1.mul_right, ?_⟩
    exact (tsupport_mul_subset_left (f := χ) (g := fun p => Real.sin (ell ζ p))).trans hχ.2.2
  have h := hW _ hΦ.1 hΦ.2.1 hΦ.2.2
  have e : (fun p => feq invβ b (fun q => χ q * Real.sin (ell ζ q)) p) =
      fun p => feq invβ b χ p * Real.sin (ell ζ p)
        + (ζ.1 * (χ p * Real.cos (ell ζ p)) + ∑ k, ζ.2 k * (gone invβ b χ k p * Real.cos (ell ζ p)))
        - invβ * ‖ζ.2‖ ^ 2 * (χ p * Real.sin (ell ζ p)) := by
    funext p
    rw [feq_sin invβ b hχ.1 ζ p, add_mul, Finset.sum_mul]
    simp only [mul_assoc]
  have h2 : ∫ p, (feq invβ b χ p * Real.sin (ell ζ p)
        + (ζ.1 * (χ p * Real.cos (ell ζ p)) + ∑ k, ζ.2 k * (gone invβ b χ k p * Real.cos (ell ζ p)))
        - invβ * ‖ζ.2‖ ^ 2 * (χ p * Real.sin (ell ζ p))) ∂ρ = 0 := by
    refine (integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)).trans h
    exact (congrFun e p).symm
  have hcos : ∀ g, IsTest O g → Integrable (fun p => g p * Real.cos (ell ζ p)) ρ :=
    fun g hg => isTest_mul_cos hρ hg ζ
  have iA := isTest_mul_sin hρ (isTest_feq hO hb invβ hχ) ζ
  have iB : Integrable (fun p => ζ.1 * (χ p * Real.cos (ell ζ p))
      + ∑ k, ζ.2 k * (gone invβ b χ k p * Real.cos (ell ζ p))) ρ :=
    ((hcos χ hχ).const_mul _).add (integrable_finsetSum _ fun k _ =>
      (hcos _ (isTest_gone hO hb invβ hχ k)).const_mul _)
  have iC := (isTest_mul_sin hρ hχ ζ).const_mul (invβ * ‖ζ.2‖ ^ 2)
  have iAB : Integrable (fun p => feq invβ b χ p * Real.sin (ell ζ p)
      + (ζ.1 * (χ p * Real.cos (ell ζ p)) + ∑ k, ζ.2 k * (gone invβ b χ k p * Real.cos (ell ζ p)))) ρ :=
    iA.add iB
  rw [integral_sub iAB iC, integral_add iA iB, integral_const_mul,
    integral_combo hρ hO hb invβ hχ ζ (fun p => Real.cos (ell ζ p)) hcos] at h2
  unfold Cf Sf
  linarith

end identities

end HRS.MC.CepP2
