import HRS.PDE.EnergyEstimate
import HRS.PDE.Hadamard

/-!
# Q13: Lemma 3.18 (`gradient_energy`) from the `H^γ` energy estimate of Prop 3.13/3.14

Route: for `u = Λ^{-2γ} c` (same support as `c`), `⟨c, A c⟩_{H^{-γ}} = ⟨𝓛 u, u⟩_{H^γ}` where
`A` is the forward linearisation and `𝓛 = forwardGen` is its coefficient-level adjoint; then
`energy_form_estimate` (regimes R1, R2b, R2c with `M = -I`) bounds the right-hand side.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q13

open HRS HRS.PDE

variable {d : ℕ}

/-- The finite pairing `∑_{k ∈ box} f(k) conj g(k)`. -/
def pr (n : ℕ) (f g : Coeff d) : ℂ := ∑ k ∈ boxFin d n, f k * conj (g k)

theorem q13_pr_sum_left {ι : Type*} (n : ℕ) (s : Finset ι) (f : ι → Coeff d) (g : Coeff d) :
    pr n (fun k => ∑ i ∈ s, f i k) g = ∑ i ∈ s, pr n (f i) g := by
  unfold pr
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

theorem q13_pr_sum_right {ι : Type*} (n : ℕ) (s : Finset ι) (c : Coeff d) (f : ι → Coeff d) :
    pr n c (fun k => ∑ i ∈ s, f i k) = ∑ i ∈ s, pr n c (f i) := by
  unfold pr
  simp_rw [map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem q13_pr_ofReal_left (n : ℕ) (a : ℝ) (f g : Coeff d) :
    pr n (fun k => (a : ℂ) * f k) g = (a : ℂ) * pr n f g := by
  unfold pr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem q13_pr_ofReal_right (n : ℕ) (a : ℝ) (f g : Coeff d) :
    pr n f (fun k => (a : ℂ) * g k) = (a : ℂ) * pr n f g := by
  unfold pr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, Complex.conj_ofReal]; ring

theorem q13_pr_neg_left (n : ℕ) (f g : Coeff d) :
    pr n (fun k => - f k) g = - pr n f g := by
  unfold pr
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem q13_pr_neg_right (n : ℕ) (f g : Coeff d) :
    pr n f (fun k => - g k) = - pr n f g := by
  unfold pr
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [map_neg]; ring

theorem q13_pr_add_left (n : ℕ) (f f' g : Coeff d) :
    pr n (fun k => f k + f' k) g = pr n f g + pr n f' g := by
  unfold pr
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem q13_pr_sub_left (n : ℕ) (f f' g : Coeff d) :
    pr n (fun k => f k - f' k) g = pr n f g - pr n f' g := by
  unfold pr
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem q13_pr_add_right (n : ℕ) (c g g' : Coeff d) :
    pr n c (fun k => g k + g' k) = pr n c g + pr n c g' := by
  unfold pr
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [map_add]; ring

theorem q13_pr_sub_right (n : ℕ) (c g g' : Coeff d) :
    pr n c (fun k => g k - g' k) = pr n c g - pr n c g' := by
  unfold pr
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [map_sub]; ring

/-! ### Realness lemmas -/

theorem q13_real_deriv (j : Fin d) {c : Coeff d} (hc : IsRealCoeff c) :
    IsRealCoeff (derivCoeff j c) := by
  intro k
  unfold derivCoeff
  rw [map_mul, hc k]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat,
    Pi.neg_apply, Int.cast_neg]
  ring

theorem q13_real_riesz (s : ℝ) {c : Coeff d} (hc : IsRealCoeff c) :
    IsRealCoeff (rieszMult d s c) := by
  intro k
  unfold rieszMult
  rw [map_mul, hc k, rieszCoeff_neg, Complex.conj_ofReal]

theorem q13_real_gradRiesz (s : ℝ) (i : Fin d) {c : Coeff d} (hc : IsRealCoeff c) :
    IsRealCoeff (gradRieszCoeff d s i c) :=
  q13_real_deriv i (q13_real_riesz s hc)

theorem q13_real_drift (D : DynData d) {μ : Torus d → ℝ} (hμ : IsRealCoeff (coeffOf μ))
    (hV : IsRealCoeff (coeffOf D.V)) (j : Fin d) : IsRealCoeff (driftCoeff D μ j) := by
  intro k
  unfold driftCoeff
  rw [map_sub, map_sum]
  have h1 := q13_real_deriv j hV k
  have h2 : ∀ i, (starRingEnd ℂ) (((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i (coeffOf μ) k) =
      ((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i (coeffOf μ) (-k) := fun i => by
    rw [map_mul, Complex.conj_ofReal, q13_real_gradRiesz D.s i hμ k]
  rw [Finset.sum_congr rfl fun i _ => h2 i, h1]

/-! ### Adjointness of the building blocks on the box -/

theorem q13_mul_selfadj {n : ℕ} {a : Coeff d} (ha : IsRealCoeff a) {x y : Coeff d}
    (hx : IsTrigPoly n x) (hy : IsTrigPoly n y) :
    pr n (mulCoeff a x) y = pr n x (mulCoeff a y) := by
  have hm : ∀ z : Coeff d, IsTrigPoly n z → ∀ k, mulCoeff a z k = ∑ j ∈ boxFin d n, a (k - j) * z j := by
    intro z hz k
    unfold mulCoeff
    refine tsum_eq_sum fun j hj => ?_
    rw [eq_zero_of_isTrigPoly hz hj]; simp
  unfold pr
  simp_rw [hm x hx, hm y hy, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  have : conj (a (k - j)) = a (j - k) := by
    have := ha (k - j)
    rw [neg_sub] at this
    exact this.symm
  rw [map_mul, this]
  ring

theorem q13_deriv_adj (n : ℕ) (j : Fin d) (f g : Coeff d) :
    pr n (derivCoeff j f) g = - pr n f (derivCoeff j g) := by
  unfold pr
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold derivCoeff
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
  ring

theorem q13_gradRiesz_adj (n : ℕ) (s : ℝ) (j : Fin d) (f g : Coeff d) :
    pr n (gradRieszCoeff d s j f) g = - pr n f (gradRieszCoeff d s j g) := by
  unfold pr
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold gradRieszCoeff derivCoeff rieszMult
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
  ring

theorem q13_lap_adj (n : ℕ) (f g : Coeff d) :
    pr n (laplaceCoeff f) g = pr n f (laplaceCoeff g) := by
  unfold pr
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold laplaceCoeff
  simp only [map_mul, map_neg, Complex.conj_ofReal]
  ring

theorem q13_isTrig_deriv {n : ℕ} (j : Fin d) {c : Coeff d} (hc : IsTrigPoly n c) :
    IsTrigPoly n (derivCoeff j c) := by
  intro k hk
  apply hc
  intro h0
  apply hk
  unfold derivCoeff; rw [h0]; simp

theorem q13_isTrig_gradRiesz {n : ℕ} (s : ℝ) (j : Fin d) {c : Coeff d} (hc : IsTrigPoly n c) :
    IsTrigPoly n (gradRieszCoeff d s j c) := by
  intro k hk
  apply hc
  intro h0
  apply hk
  unfold gradRieszCoeff derivCoeff rieszMult; rw [h0]; simp

/-- The adjointness of the forward linearisation and the forward generator on the box. -/
theorem q13_adjoint {n : ℕ} (D : DynData d) {μ : Torus d → ℝ} (hμ : IsRealCoeff (coeffOf μ))
    (hV : IsRealCoeff (coeffOf D.V)) {c u : Coeff d} (hc : IsTrigPoly n c)
    (hu : IsTrigPoly n u) :
    pr n (fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff c k
        - ∑ j : Fin d, derivCoeff j (mulCoeff (driftCoeff D μ j) c) k
        + forwardNonlocalCoeff D μ c k) u = pr n c (forwardGen D μ u) := by
  have hdr := q13_real_drift D hμ hV
  -- the three pieces
  have P1 : pr n (fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff c k) u =
      pr n c (fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff u k) := by
    rw [q13_pr_ofReal_left, q13_pr_ofReal_right, q13_lap_adj]
  have P2 : pr n (fun k => ∑ j : Fin d, derivCoeff j (mulCoeff (driftCoeff D μ j) c) k) u =
      - pr n c (transportCoeff D μ u) := by
    rw [q13_pr_sum_left]
    unfold transportCoeff
    rw [q13_pr_sum_right, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [q13_deriv_adj, q13_mul_selfadj (hdr j) hc (q13_isTrig_deriv j hu)]
  have P3 : pr n (forwardNonlocalCoeff D μ c) u = - pr n c (nonlocalCoeff D μ u) := by
    have e1 : forwardNonlocalCoeff D μ c = fun k => - ∑ i : Fin d, ∑ j : Fin d,
        ((D.M i j : ℝ) : ℂ) * derivCoeff i (mulCoeff (coeffOf μ) (gradRieszCoeff d D.s j c)) k := by
      funext k
      unfold forwardNonlocalCoeff derivCoeff
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have e2 : nonlocalCoeff D μ u = fun k => ∑ i : Fin d, ∑ j : Fin d,
        ((D.M i j : ℝ) : ℂ) * gradRieszCoeff d D.s j (mulCoeff (coeffOf μ) (derivCoeff i u)) k := by
      funext k
      unfold nonlocalCoeff
      rw [Finset.sum_comm]
    rw [e1, e2, q13_pr_neg_left, q13_pr_sum_left, q13_pr_sum_right]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [q13_pr_sum_left, q13_pr_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [q13_pr_ofReal_left, q13_pr_ofReal_right, q13_deriv_adj,
      q13_mul_selfadj hμ (q13_isTrig_gradRiesz D.s j hc) (q13_isTrig_deriv i hu),
      q13_gradRiesz_adj]
    ring
  rw [q13_pr_add_left, q13_pr_sub_left, P1, P2, P3]
  have : forwardGen D μ u = fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff u k + transportCoeff D μ u k
      - nonlocalCoeff D μ u k := rfl
  rw [this, q13_pr_sub_right, q13_pr_add_right]
  ring

end HRS.Uniform.Q13
