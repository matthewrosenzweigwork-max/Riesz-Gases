import HRS.Commutator.Torus.TLOWVAux1

/-!
# T-LOWV helpers, part 2: `∬ Q dσ dσ` for a trigonometric-polynomial kernel `Q`

Prefix `tlowv_`.  If `Q(x,y) = ∑_i γ_i e_{p_i}(x) e_{q_i}(y)` (finite sum), then
`∬ Q dσ dσ = ∑_i γ_i σ̂(-p_i) σ̂(-q_i)`; consequently the pairing only depends on the coefficients
`σ̂(-p_i), σ̂(-q_i)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tlowv_tenSint_finsum (σ : SMT d) (hσ : σ.IsFinite) {ι : Type*} (S : Finset ι)
    (g : ι → Torus d → ℂ) (hg : ∀ i, Continuous (g i)) :
    tenSint σ (fun x => ∑ i ∈ S, g i x) = ∑ i ∈ S, tenSint σ (g i) := by
  obtain ⟨hp, hn⟩ := hσ
  have hint : ∀ (μ : Measure (Torus d)) [IsFiniteMeasure μ] (i : ι), Integrable (g i) μ :=
    fun μ _ i => (hg i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold tenSint
  rw [integral_finset_sum _ (fun i _ => hint σ.pos i), integral_finset_sum _ (fun i _ => hint σ.neg i),
    ← Finset.sum_sub_distrib]

lemma tlowv_tenSint_const_mul (σ : SMT d) (hσ : σ.IsFinite) (c : ℂ) (g : Torus d → ℂ)
    (hg : Continuous g) : tenSint σ (fun x => c * g x) = c * tenSint σ g := by
  unfold tenSint
  rw [integral_const_mul, integral_const_mul, mul_sub]

/-- Pairing of a finite signed measure against a trigonometric-polynomial kernel. -/
theorem tlowv_pair2_trig (σ : SMT d) (hσ : σ.IsFinite) {ι : Type*} (S : Finset ι) (p q : ι → Lattice d)
    (γ : ι → ℂ) (Q : Torus d → Torus d → ℝ)
    (hQ : ∀ x y, ((Q x y : ℝ) : ℂ) = ∑ i ∈ S, γ i * Torus.mode (p i) x * Torus.mode (q i) y) :
    ((σ.pair2 Q : ℝ) : ℂ) = ∑ i ∈ S, γ i * σ.coef (-(p i)) * σ.coef (-(q i)) := by
  have hinner : ∀ x : Torus d, ((σ.int (fun y => Q x y) : ℝ) : ℂ) =
      ∑ i ∈ S, (γ i * σ.coef (-(q i))) * Torus.mode (p i) x := by
    intro x
    rw [ten_ofReal]
    simp_rw [hQ]
    rw [tlowv_tenSint_finsum σ hσ S (fun i y => γ i * Torus.mode (p i) x * Torus.mode (q i) y)
      (fun i => continuous_const.mul (Torus.continuous_mode _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tlowv_tenSint_const_mul σ hσ _ _ (Torus.continuous_mode _), ten_tenSint_mode]
    ring
  unfold SMT.pair2
  rw [ten_ofReal σ (fun x => σ.int (fun y => Q x y))]
  have hfun : (fun x : Torus d => ((σ.int (fun y => Q x y) : ℝ) : ℂ)) =
      fun x => ∑ i ∈ S, (γ i * σ.coef (-(q i))) * Torus.mode (p i) x := funext hinner
  rw [hfun, tlowv_tenSint_finsum σ hσ S (fun i x => (γ i * σ.coef (-(q i))) * Torus.mode (p i) x)
    (fun i => continuous_const.mul (Torus.continuous_mode _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tlowv_tenSint_const_mul σ hσ _ _ (Torus.continuous_mode _), ten_tenSint_mode]
  ring

/-- The pairing depends only on the coefficients at the frequencies `-p_i, -q_i`. -/
theorem tlowv_pair2_congr (σ τ : SMT d) (hσ : σ.IsFinite) (hτ : τ.IsFinite) {ι : Type*}
    (S : Finset ι) (p q : ι → Lattice d) (γ : ι → ℂ) (Q : Torus d → Torus d → ℝ)
    (hQ : ∀ x y, ((Q x y : ℝ) : ℂ) = ∑ i ∈ S, γ i * Torus.mode (p i) x * Torus.mode (q i) y)
    (hE : ∀ i ∈ S, γ i ≠ 0 → σ.coef (-(p i)) = τ.coef (-(p i)) ∧ σ.coef (-(q i)) = τ.coef (-(q i))) :
    σ.pair2 Q = τ.pair2 Q := by
  have h1 := tlowv_pair2_trig σ hσ S p q γ Q hQ
  have h2 := tlowv_pair2_trig τ hτ S p q γ Q hQ
  have : ((σ.pair2 Q : ℝ) : ℂ) = ((τ.pair2 Q : ℝ) : ℂ) := by
    rw [h1, h2]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h0 : γ i = 0
    · simp [h0]
    · rw [(hE i hi h0).1, (hE i hi h0).2]
  exact_mod_cast this

end HRS.Commutator.TorusNote
