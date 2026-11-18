import HRS.Prob.HilbertMartingale

/-!
# U9 (aux 1): the covariance form `2q ∑_a ∫ ⟨Γ_a,·⟩⟨Γ_a,·⟩ dν` of bounded measurable features is a
bounded bilinear form, positive trace class, with trace at most `2 n B² q ν(univ)`
(clause (i) of `HRS.Whole.orbit_maximal`, for an arbitrary separable Hilbert space).
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.U9

section Gen

variable {X : Type*} [MeasurableSpace X] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma u9_meas_inner {g : X → H} (hg : Measurable g) (u : H) :
    Measurable fun x => inner ℝ (g x) u :=
  (continuous_id.inner continuous_const).measurable.comp hg

lemma u9_integrable_prod {ν : Measure X} [IsFiniteMeasure ν] {B : ℝ} {g : X → H}
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ B) (u v : H) :
    Integrable (fun x => inner ℝ (g x) u * inner ℝ (g x) v) ν := by
  refine Integrable.mono' (integrable_const (B ^ 2 * ‖u‖ * ‖v‖))
    ((u9_meas_inner hg u).mul (u9_meas_inner hg v)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb x)
  have h1 := abs_real_inner_le_norm (g x) u
  have h2 := abs_real_inner_le_norm (g x) v
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |inner ℝ (g x) u| * |inner ℝ (g x) v| ≤ (‖g x‖ * ‖u‖) * (‖g x‖ * ‖v‖) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ ≤ (B * ‖u‖) * (B * ‖v‖) := by gcongr <;> exact hb x
    _ = B ^ 2 * ‖u‖ * ‖v‖ := by ring

/-- The form `(u,v) ↦ 2q ∑_a ∫ ⟨Γ_a x,u⟩⟨Γ_a x,v⟩ dν`. -/
def u9_form (q : ℝ) {n : ℕ} (Γ : Fin n → X → H) (ν : Measure X) (u v : H) : ℝ :=
  2 * q * ∑ a, ∫ x, inner ℝ (Γ a x) u * inner ℝ (Γ a x) v ∂ν

variable {n : ℕ} {Γ : Fin n → X → H} {ν : Measure X} [IsFiniteMeasure ν] {B : ℝ} {q : ℝ}

lemma u9_form_add_left (hΓ : ∀ a, Measurable (Γ a)) (hb : ∀ a x, ‖Γ a x‖ ≤ B) (u u' v : H) :
    u9_form q Γ ν (u + u') v = u9_form q Γ ν u v + u9_form q Γ ν u' v := by
  unfold u9_form
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← integral_add (u9_integrable_prod (hΓ a) (hb a) u v) (u9_integrable_prod (hΓ a) (hb a) u' v)]
  congr 1; funext x; rw [inner_add_right, add_mul]

lemma u9_form_smul_left (c : ℝ) (u v : H) :
    u9_form q Γ ν (c • u) v = c * u9_form q Γ ν u v := by
  unfold u9_form
  have : ∀ a, ∫ x, c * inner ℝ (Γ a x) u * inner ℝ (Γ a x) v ∂ν =
      c * ∫ x, inner ℝ (Γ a x) u * inner ℝ (Γ a x) v ∂ν := fun a => by
    rw [← integral_const_mul]; congr 1; funext x; ring
  simp only [real_inner_smul_right, this, ← Finset.mul_sum]
  ring

lemma u9_form_symm (u v : H) : u9_form q Γ ν u v = u9_form q Γ ν v u := by
  unfold u9_form
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1; funext x; ring

lemma u9_form_bound (hq : 0 ≤ q) (hΓ : ∀ a, Measurable (Γ a)) (hb : ∀ a x, ‖Γ a x‖ ≤ B) (u v : H) :
    ‖u9_form q Γ ν u v‖ ≤ (2 * q * n * B ^ 2 * (ν Set.univ).toReal) * ‖u‖ * ‖v‖ := by
  unfold u9_form
  have hterm : ∀ a, ‖∫ x, inner ℝ (Γ a x) u * inner ℝ (Γ a x) v ∂ν‖ ≤
      B ^ 2 * ‖u‖ * ‖v‖ * (ν Set.univ).toReal := by
    intro a
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
    have hB : 0 ≤ B := (norm_nonneg _).trans (hb a x)
    have h1 := abs_real_inner_le_norm (Γ a x) u
    have h2 := abs_real_inner_le_norm (Γ a x) v
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |inner ℝ (Γ a x) u| * |inner ℝ (Γ a x) v| ≤ (‖Γ a x‖ * ‖u‖) * (‖Γ a x‖ * ‖v‖) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ (B * ‖u‖) * (B * ‖v‖) := by gcongr <;> exact hb a x
      _ = B ^ 2 * ‖u‖ * ‖v‖ := by ring
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * q)]
  calc 2 * q * ‖∑ a, ∫ x, inner ℝ (Γ a x) u * inner ℝ (Γ a x) v ∂ν‖
      ≤ 2 * q * ∑ a : Fin n, B ^ 2 * ‖u‖ * ‖v‖ * (ν Set.univ).toReal := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hterm a)
    _ = (2 * q * n * B ^ 2 * (ν Set.univ).toReal) * ‖u‖ * ‖v‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma u9_form_nonneg (hq : 0 ≤ q) (u : H) : 0 ≤ u9_form q Γ ν u u := by
  unfold u9_form
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => integral_nonneg fun x => ?_)
  exact mul_self_nonneg _

/-- Pointwise: `∑_i |⟨g,e_i⟩⟨g,f_i⟩| ≤ ‖g‖²` for orthonormal families. -/
lemma u9_pair_sum_le {k : ℕ} {e f : Fin k → H} (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (g : H) : ∑ i, |inner ℝ g (e i) * inner ℝ g (f i)| ≤ ‖g‖ ^ 2 := by
  have h1 := he.sum_inner_products_le (s := Finset.univ) g
  have h2 := hf.sum_inner_products_le (s := Finset.univ) g
  have h3 : ∑ i, |inner ℝ g (e i) * inner ℝ g (f i)| ≤
      ∑ i, (‖inner ℝ (e i) g‖ ^ 2 + ‖inner ℝ (f i) g‖ ^ 2) / 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs, real_inner_comm g (e i),
      real_inner_comm g (f i)]
    nlinarith [sq_nonneg (|inner ℝ g (e i)| - |inner ℝ g (f i)|)]
  have h4 : ∑ i, (‖inner ℝ (e i) g‖ ^ 2 + ‖inner ℝ (f i) g‖ ^ 2) / 2 =
      (∑ i, ‖inner ℝ (e i) g‖ ^ 2 + ∑ i, ‖inner ℝ (f i) g‖ ^ 2) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  linarith


lemma u9_trace_bound (hq : 0 ≤ q) (hΓ : ∀ a, Measurable (Γ a)) (hb : ∀ a x, ‖Γ a x‖ ≤ B)
    (Bf : H →L[ℝ] H →L[ℝ] ℝ) (hBf : ∀ u v, Bf u v = u9_form q Γ ν u v) :
    traceNormForm Bf ≤ 2 * n * B ^ 2 * q * (ν Set.univ).toReal := by
  haveI : Nonempty (OrthonormalPairs H) :=
    ⟨⟨⟨0, fun i => i.elim0, fun i => i.elim0⟩, ⟨fun i => i.elim0, fun i => i.elim0⟩,
      ⟨fun i => i.elim0, fun i => i.elim0⟩⟩⟩
  refine ciSup_le fun p => ?_
  obtain ⟨⟨k, e, f⟩, he, hf⟩ := p
  simp only
  have hint : ∀ a (i : Fin k), Integrable (fun x => |inner ℝ (Γ a x) (e i) * inner ℝ (Γ a x) (f i)|) ν :=
    fun a i => (u9_integrable_prod (hΓ a) (hb a) (e i) (f i)).abs
  have hsum : ∀ a, ∑ i : Fin k, ∫ x, |inner ℝ (Γ a x) (e i) * inner ℝ (Γ a x) (f i)| ∂ν ≤
      B ^ 2 * (ν Set.univ).toReal := by
    intro a
    rw [← integral_finsetSum _ (fun i _ => hint a i)]
    calc ∫ x, ∑ i : Fin k, |inner ℝ (Γ a x) (e i) * inner ℝ (Γ a x) (f i)| ∂ν
        ≤ ∫ x, B ^ 2 ∂ν := by
          refine integral_mono (integrable_finsetSum _ fun i _ => hint a i)
            (integrable_const _) fun x => ?_
          refine (u9_pair_sum_le he hf (Γ a x)).trans ?_
          have hB : 0 ≤ B := (norm_nonneg _).trans (hb a x)
          gcongr; exact hb a x
      _ = B ^ 2 * (ν Set.univ).toReal := by
          rw [integral_const, smul_eq_mul, mul_comm]; rfl
  calc ∑ i : Fin k, |Bf (e i) (f i)|
      ≤ ∑ i : Fin k, 2 * q * ∑ a, ∫ x, |inner ℝ (Γ a x) (e i) * inner ℝ (Γ a x) (f i)| ∂ν := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hBf, u9_form, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * q)]
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        exact abs_integral_le_integral_abs
    _ = 2 * q * ∑ a, ∑ i : Fin k, ∫ x, |inner ℝ (Γ a x) (e i) * inner ℝ (Γ a x) (f i)| ∂ν := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 2 * q * ∑ a : Fin n, B ^ 2 * (ν Set.univ).toReal := by
        gcongr with a _
        exact hsum a
    _ = 2 * n * B ^ 2 * q * (ν Set.univ).toReal := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma u9_exists_form (hq : 0 ≤ q) (hΓ : ∀ a, Measurable (Γ a)) (hb : ∀ a x, ‖Γ a x‖ ≤ B) :
    ∃ Bf : H →L[ℝ] H →L[ℝ] ℝ, (∀ u v, Bf u v = u9_form q Γ ν u v) ∧ IsTraceClassCov Bf ∧
      traceNormForm Bf ≤ 2 * n * B ^ 2 * q * (ν Set.univ).toReal := by
  let L : H →ₗ[ℝ] H →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (u9_form q Γ ν)
    (fun u u' v => u9_form_add_left hΓ hb u u' v)
    (fun c u v => u9_form_smul_left c u v)
    (fun u v v' => by
      rw [u9_form_symm, u9_form_add_left hΓ hb, u9_form_symm (u := u), u9_form_symm (u := u)])
    (fun c u v => by rw [u9_form_symm, u9_form_smul_left, u9_form_symm, smul_eq_mul])
  let Bf : H →L[ℝ] H →L[ℝ] ℝ := LinearMap.mkContinuous₂ L (2 * q * n * B ^ 2 * (ν Set.univ).toReal)
    (fun u v => u9_form_bound hq hΓ hb u v)
  have hBf : ∀ u v, Bf u v = u9_form q Γ ν u v := fun u v => rfl
  refine ⟨Bf, hBf, ⟨fun x y => ?_, fun x => ?_, ?_⟩, u9_trace_bound hq hΓ hb Bf hBf⟩
  · rw [hBf, hBf, u9_form_symm]
  · rw [hBf]; exact u9_form_nonneg hq x
  · obtain ⟨w, b, hbw⟩ := exists_hilbertBasis ℝ H
    refine ⟨w, b, ?_⟩
    have hon := b.orthonormal
    refine summable_of_sum_le (c := 2 * q * (n * (B ^ 2 * (ν Set.univ).toReal)))
      (fun i => by rw [hBf]; exact u9_form_nonneg hq _) fun s => ?_
    have hint : ∀ a (i : w), Integrable (fun x => inner ℝ (Γ a x) (b i) * inner ℝ (Γ a x) (b i)) ν :=
      fun a i => u9_integrable_prod (hΓ a) (hb a) (b i) (b i)
    have hsum : ∀ a, ∑ i ∈ s, ∫ x, inner ℝ (Γ a x) (b i) * inner ℝ (Γ a x) (b i) ∂ν ≤
        B ^ 2 * (ν Set.univ).toReal := by
      intro a
      rw [← integral_finsetSum _ (fun i _ => hint a i)]
      calc ∫ x, ∑ i ∈ s, inner ℝ (Γ a x) (b i) * inner ℝ (Γ a x) (b i) ∂ν
          ≤ ∫ x, B ^ 2 ∂ν := by
            refine integral_mono (integrable_finsetSum _ fun i _ => hint a i)
              (integrable_const _) fun x => ?_
            have h1 := hon.sum_inner_products_le (s := s) (Γ a x)
            have hB : 0 ≤ B := (norm_nonneg _).trans (hb a x)
            have h2 : ‖Γ a x‖ ^ 2 ≤ B ^ 2 := by gcongr; exact hb a x
            refine le_trans (le_of_eq ?_) (h1.trans h2)
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Real.norm_eq_abs, sq_abs, real_inner_comm, sq]
        _ = B ^ 2 * (ν Set.univ).toReal := by
            rw [integral_const, smul_eq_mul, mul_comm]; rfl
    calc ∑ i ∈ s, Bf (b i) (b i)
        = 2 * q * ∑ a, ∑ i ∈ s, ∫ x, inner ℝ (Γ a x) (b i) * inner ℝ (Γ a x) (b i) ∂ν := by
          simp only [hBf, u9_form]
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ 2 * q * ∑ a : Fin n, B ^ 2 * (ν Set.univ).toReal := by
          gcongr with a _
          exact hsum a
      _ = 2 * q * (n * (B ^ 2 * (ν Set.univ).toReal)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Gen

end HRS.MS.U9
