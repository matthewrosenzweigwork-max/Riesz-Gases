import HRS.Commutator.Torus.Defs

/-!
# Torus energy layer (packet T-EN), helper part 1: Fourier identities for `kerEnergyT`

Prefix `ten_`.  For a continuous real kernel `g : 𝕋^d → ℝ` whose Fourier coefficients `c k` are
absolutely summable, and a finite signed measure `σ`, the energy is the Fourier sum
`kerEnergyT g σ = ∑_k c_k |σ̂(k)|²` (`σ̂(k) = σ.coef k`).  No assumption on `g` beyond this.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- Complex-valued signed integral `∫ F dσ⁺ - ∫ F dσ⁻`. -/
def tenSint (σ : SMT d) (F : Torus d → ℂ) : ℂ := ∫ x, F x ∂σ.pos - ∫ x, F x ∂σ.neg

/-- Point additivity of the monomials on the torus. -/
theorem ten_mode_add (k : Lattice d) (x y : Torus d) :
    Torus.mode k (x + y) = Torus.mode k x * Torus.mode k y := by
  simp only [Torus.mode, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- `e_k(x - y) = e_k(x) conj(e_k(y))` on the torus. -/
theorem ten_mode_sub (k : Lattice d) (x y : Torus d) :
    Torus.mode k (x - y) = Torus.mode k x * conj (Torus.mode k y) := by
  have h1 : Torus.mode k x = Torus.mode k (x - y) * Torus.mode k y := by
    rw [← ten_mode_add, sub_add_cancel]
  have h2 : Torus.mode k y * conj (Torus.mode k y) = 1 := by
    rw [RCLike.mul_conj, Torus.norm_mode]; simp
  calc Torus.mode k (x - y)
      = Torus.mode k (x - y) * (Torus.mode k y * conj (Torus.mode k y)) := by rw [h2, mul_one]
    _ = (Torus.mode k (x - y) * Torus.mode k y) * conj (Torus.mode k y) := by ring
    _ = Torus.mode k x * conj (Torus.mode k y) := by rw [← h1]

/-- Pointwise Fourier expansion of a continuous function with absolutely summable coefficients. -/
theorem ten_hasSum_expand {g : Torus d → ℝ} (hg : Continuous g) {c : Lattice d → ℝ}
    (hc : Summable (fun k => |c k|)) (hcoef : ∀ k, Torus.fcoef g k = (c k : ℂ)) (x : Torus d) :
    HasSum (fun k => (c k : ℂ) * Torus.mode k x) ((g x : ℂ)) := by
  have hs : Summable (fun k => ‖Torus.fcoef g k‖) := by
    simp_rw [hcoef, Complex.norm_real, Real.norm_eq_abs]
    exact hc
  have h := Torus.hasSum_fcoef_series hg hs x
  simp only [hcoef] at h
  exact h

/-- Integrability of a continuous, bounded complex function against a finite measure. -/
theorem ten_integrable {μ : Measure (Torus d)} [IsFiniteMeasure μ] {F : Torus d → ℂ}
    (hF : Continuous F) (C : ℝ) (hC : ∀ x, ‖F x‖ ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hC)

/-- Bound `‖∫ F dμ‖ ≤ C μ(𝕋^d)` for bounded `F`. -/
theorem ten_integral_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] (F : Torus d → E) (C : ℝ)
    (hC : ∀ x, ‖F x‖ ≤ C) : ‖∫ x, F x ∂μ‖ ≤ C * μ.real Set.univ :=
  norm_integral_le_of_norm_le_const (ae_of_all _ hC)

/-- Interchange of a summable series of bounded continuous functions with a finite signed integral. -/
theorem ten_sint_tsum (σ : SMT d) (hσ : σ.IsFinite) (a : Lattice d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (F : Lattice d → Torus d → ℂ) (hF : ∀ k, Continuous (F k))
    (hb : ∀ k x, ‖F k x‖ ≤ 1) :
    tenSint σ (fun x => ∑' k, a k * F k x) = ∑' k, a k * tenSint σ (F k) := by
  obtain ⟨hpos, hneg⟩ := hσ
  have key : ∀ μ : Measure (Torus d), IsFiniteMeasure μ →
      ∫ x, (∑' k, a k * F k x) ∂μ = ∑' k, a k * ∫ x, F k x ∂μ := by
    intro μ hμ
    have hint : ∀ k, Integrable (fun x => a k * F k x) μ := fun k =>
      ten_integrable ((hF k).const_mul (a k)) (‖a k‖) (fun x => by
        rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hb k x))
    have hsum : Summable (fun k => ∫ x, ‖a k * F k x‖ ∂μ) := by
      refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _) (fun k => ?_)
        (ha.mul_right (μ.real Set.univ))
      have hb' : ∀ x, ‖a k * F k x‖ ≤ ‖a k‖ := fun x => by
        rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hb k x)
      have := integral_mono (hint k).norm (integrable_const (‖a k‖)) hb'
      have e : ∫ _x, ‖a k‖ ∂μ = ‖a k‖ * μ.real Set.univ := by
        rw [integral_const, smul_eq_mul, mul_comm]
      linarith
    have := integral_tsum_of_summable_integral_norm hint hsum
    rw [← this]
    exact tsum_congr fun k => integral_const_mul _ _
  have hs : ∀ μ : Measure (Torus d), IsFiniteMeasure μ →
      Summable (fun k => a k * ∫ x, F k x ∂μ) := by
    intro μ hμ
    refine Summable.of_norm_bounded (ha.mul_right (μ.real Set.univ)) (fun k => ?_)
    rw [norm_mul]
    have h1 := ten_integral_bound (μ := μ) (F k) 1 (hb k)
    rw [one_mul] at h1
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have : IsFiniteMeasure σ.pos := hpos
  have : IsFiniteMeasure σ.neg := hneg
  unfold tenSint
  rw [key σ.pos hpos, key σ.neg hneg, ← Summable.tsum_sub (hs σ.pos hpos) (hs σ.neg hneg)]
  exact tsum_congr fun k => by ring

/-- `tenSint` of a real function is the real signed integral. -/
theorem ten_ofReal (σ : SMT d) (f : Torus d → ℝ) :
    ((σ.int f : ℝ) : ℂ) = tenSint σ (fun x => (f x : ℂ)) := by
  unfold SMT.int tenSint
  rw [Complex.ofReal_sub, integral_complex_ofReal, integral_complex_ofReal]

/-- The signed integral of the monomial `e_k` is the Fourier coefficient at `-k`. -/
theorem ten_tenSint_mode (σ : SMT d) (k : Lattice d) :
    tenSint σ (fun y => Torus.mode k y) = σ.coef (-k) := by
  unfold tenSint SMT.coef
  rw [neg_neg]

/-- The signed integral of `conj e_k` is the conjugate. -/
theorem ten_tenSint_conj (σ : SMT d) (k : Lattice d) :
    tenSint σ (fun y => conj (Torus.mode k y)) = conj (σ.coef (-k)) := by
  rw [← ten_tenSint_mode]
  unfold tenSint
  simp only [integral_conj]
  rw [map_sub]

/-- Reality of a finite signed measure: `σ̂(-k) = conj σ̂(k)`. -/
theorem ten_coef_neg (σ : SMT d) (k : Lattice d) : σ.coef (-k) = conj (σ.coef k) := by
  unfold SMT.coef
  rw [map_sub, ← integral_conj, ← integral_conj]
  simp only [Torus.mode_neg, Complex.conj_conj, neg_neg]

/-- Norm bound `‖σ̂(k)‖ ≤ σ⁺(𝕋^d) + σ⁻(𝕋^d)` for a finite signed measure. -/
theorem ten_coef_norm_le (σ : SMT d) (hσ : σ.IsFinite) (k : Lattice d) :
    ‖σ.coef k‖ ≤ (σ.pos Set.univ).toReal + (σ.neg Set.univ).toReal := by
  obtain ⟨hpos, hneg⟩ := hσ
  unfold SMT.coef
  have h1 := ten_integral_bound (μ := σ.pos) (fun x => Torus.mode (-k) x) 1
    (fun x => by rw [Torus.norm_mode])
  have h2 := ten_integral_bound (μ := σ.neg) (fun x => Torus.mode (-k) x) 1
    (fun x => by rw [Torus.norm_mode])
  have hp : σ.pos.real Set.univ = (σ.pos Set.univ).toReal := rfl
  have hn : σ.neg.real Set.univ = (σ.neg Set.univ).toReal := rfl
  rw [hp, one_mul] at h1
  rw [hn, one_mul] at h2
  calc ‖(∫ x, Torus.mode (-k) x ∂σ.pos) - ∫ x, Torus.mode (-k) x ∂σ.neg‖
      ≤ ‖∫ x, Torus.mode (-k) x ∂σ.pos‖ + ‖∫ x, Torus.mode (-k) x ∂σ.neg‖ := norm_sub_le _ _
    _ ≤ (σ.pos Set.univ).toReal + (σ.neg Set.univ).toReal := by linarith [h1, h2]

/-- The Fourier identity for the energy: `kerEnergyT g σ = ∑_k c_k |σ̂(k)|²`, for a continuous kernel `g`
whose Fourier coefficients are `c` (absolutely summable). -/
theorem ten_kerEnergy_fourier (σ : SMT d) (hσ : σ.IsFinite) {g : Torus d → ℝ} (hg : Continuous g)
    {c : Lattice d → ℝ} (hc : Summable (fun k => |c k|)) (hcoef : ∀ k, Torus.fcoef g k = (c k : ℂ)) :
    kerEnergyT g σ = ∑' k, c k * ‖σ.coef k‖ ^ 2 := by
  -- inner integral, for each `x`
  have hinner : ∀ x : Torus d, ((σ.int (fun y => g (x - y)) : ℝ) : ℂ) =
      ∑' k, ((c k : ℂ) * Torus.mode k x) * conj (σ.coef (-k)) := by
    intro x
    rw [ten_ofReal]
    have hfun : (fun y : Torus d => ((g (x - y) : ℝ) : ℂ)) =
        fun y => ∑' k, ((c k : ℂ) * Torus.mode k x) * conj (Torus.mode k y) := by
      funext y
      rw [← (ten_hasSum_expand hg hc hcoef (x - y)).tsum_eq]
      exact tsum_congr fun k => by rw [ten_mode_sub]; ring
    have hA : Summable (fun k => ‖(c k : ℂ) * Torus.mode k x‖) := by
      simpa [norm_mul, Torus.norm_mode, Real.norm_eq_abs] using hc
    rw [hfun, ten_sint_tsum σ hσ (fun k => (c k : ℂ) * Torus.mode k x) hA
      (fun k y => conj (Torus.mode k y)) (fun k => Complex.continuous_conj.comp (Torus.continuous_mode k))
      (fun k y => by simp [Torus.norm_mode])]
    exact tsum_congr fun k => by rw [ten_tenSint_conj]
  -- the coefficient sequence of the outer integral
  have hsumz : Summable (fun k => ‖(c k : ℂ) * conj (σ.coef (-k))‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (hc.mul_right ((σ.pos Set.univ).toReal + (σ.neg Set.univ).toReal))
    rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (ten_coef_norm_le σ hσ (-k)) (abs_nonneg _)
  have hcomplex : ((kerEnergyT g σ : ℝ) : ℂ) =
      ∑' k, ((c k : ℂ) * conj (σ.coef (-k))) * σ.coef (-k) := by
    unfold kerEnergyT SMT.pair2
    rw [ten_ofReal σ (fun x => σ.int (fun y => g (x - y)))]
    have hfun : (fun x : Torus d => ((σ.int (fun y => g (x - y)) : ℝ) : ℂ)) =
        fun x => ∑' k, ((c k : ℂ) * conj (σ.coef (-k))) * Torus.mode k x := by
      funext x
      rw [hinner x]
      exact tsum_congr fun k => by ring
    rw [hfun, ten_sint_tsum σ hσ (fun k => (c k : ℂ) * conj (σ.coef (-k))) hsumz
      (fun k x => Torus.mode k x) (fun k => Torus.continuous_mode k)
      (fun k x => by simp [Torus.norm_mode])]
    exact tsum_congr fun k => by rw [ten_tenSint_mode]
  have hreal : ∑' k, ((c k : ℂ) * conj (σ.coef (-k))) * σ.coef (-k) =
      ((∑' k, c k * ‖σ.coef k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun k => ?_
    rw [ten_coef_neg, Complex.conj_conj, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  exact_mod_cast hcomplex.trans hreal

end HRS.Commutator.TorusNote
