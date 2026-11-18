import HRS.MS.R2InterpAux29
import HRS.MC.S7PIF6D

/-!
# S10.2 (worker S102), part 30 (packet B1): the Gram identity for the covariance rate of the grid observations

`∑_{k,k'} rate_{kk'}(u) N(Λe_k, Λe_{k'}) = 2ν ∫ ρ_u(x) ∑_a N(Λ v_a(x), Λ v_a(x)) dx` with `v_a(x)_k = 1[u ≤ t_k] ∂_aU^{u,t_k}φ_{α_k}(x)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq HRS.MC.Sec7.S7PIF6

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

/-- The node of the `k`-th observation. -/
def s102_tk (hT : 0 < T) (L : ℕ) (k : Fin (s102_q d L)) : ℝ := ((s102_tauk hT L k : Set.Icc (0 : ℝ) T) : ℝ)

/-- The Gram integral `∫ ∇ψ_k·∇ψ_{k'} ρ_u dx` (before the cut-off `1[u ≤ t_k ∧ t_{k'}]`). -/
def s102_gram (C : WholeCoeff d) (m : ℝ) (hT : 0 < T) (L : ℕ) (u : ℝ) (k k' : Fin (s102_q d L)) : ℝ :=
  ∫ x, inner ℝ (gradient (propagatorW C u (s102_tk hT L k) (oscTestFun m (s102_alk L k))) x)
    (gradient (propagatorW C u (s102_tk hT L k') (oscTestFun m (s102_alk L k'))) x) * C.ρ u x

/-- The covariance rate of the grid observations. -/
def s102_rateM (C : WholeCoeff d) (m : ℝ) (hT : 0 < T) (L : ℕ) (u : ℝ) :
    Matrix (Fin (s102_q d L)) (Fin (s102_q d L)) ℝ :=
  Matrix.of fun k k' => 2 * C.ν *
    (if u ≤ min (s102_tk hT L k) (s102_tk hT L k') then s102_gram C m hT L u k k' else 0)

/-- The coefficient vector `v_a(x)` in `ℝ^q`. -/
def s102_vv (C : WholeCoeff d) (m : ℝ) (hT : 0 < T) (L : ℕ) (u : ℝ) (x : Euc d) (a : Fin d) :
    EuclideanSpace ℝ (Fin (s102_q d L)) :=
  WithLp.toLp 2 fun k => s102_cc C m hT L u x a (s102_pk d L k)

theorem s102_integral_triple_sum {X : Type*} [MeasurableSpace X] (μ : Measure X) {ι κ : Type*} [Fintype ι]
    [Fintype κ] (f : ι → κ → κ → X → ℝ) (hf : ∀ a k k', Integrable (f a k k') μ) :
    ∫ x, ∑ a, ∑ k, ∑ k', f a k k' x ∂μ = ∑ a, ∑ k, ∑ k', ∫ x, f a k k' x ∂μ := by
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun k' _ => hf a k k')]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun k' _ => hf a k k')]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finset_sum _ (fun k' _ => hf a k k')]

theorem s102_abs_gradient_le (f : Euc d → ℝ) (x : Euc d) (a : Fin d) :
    |gradient f x a| ≤ ‖iteratedFDeriv ℝ 1 f x‖ := by
  have hn : ‖fderiv ℝ f x‖ = ‖iteratedFDeriv ℝ 1 f x‖ := by
    have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0) (f := f) (x := x)
    simpa using this
  rw [s102_gradient_apply, ← hn]
  have := (fderiv ℝ f x).le_opNorm (EuclideanSpace.single a (1 : ℝ))
  simpa using this

/-- Boundedness of the gradient components of the orbits. -/
theorem s102_cc_bound (hD : S101Data C m T r c) (hT : 0 < T) (L : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T)
    (x : Euc d) (a : Fin d) (p : ℕ × MultiIndex d) : |s102_cc C m hT L u x a p| ≤ c p.2 := by
  unfold s102_cc
  split_ifs with h
  · have hti : ((s102_node hT L p.1 : Set.Icc (0 : ℝ) T) : ℝ) ∈ Icc u T := ⟨h, (s102_node hT L p.1).2.2⟩
    exact (s102_abs_gradient_le _ x a).trans (hD.bddU p.2 u hu _ hti 1 (by omega) x)
  · simpa using hD.nonneg p.2

theorem s102_inner_eq_sum (g g' : Euc d) : inner ℝ g g' = ∑ a, g a * g' a := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem s102_Lam_vec (T : ℝ) (L : ℕ) (v : EuclideanSpace ℝ (Fin (s102_q d L))) :
    (s102_Lam T L v : OscPath d m T) = ∑ k, v k • s102_Lam T L (EuclideanSpace.single k (1 : ℝ)) := by
  conv_lhs => rw [S7PIF6_vec_expand v]
  simp [map_sum, map_smul]

theorem s102_cc_continuous (hD : S101Data C m T r c) (hT : 0 < T) (L : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T)
    (a : Fin d) (p : ℕ × MultiIndex d) : Continuous fun x => s102_cc C m hT L u x a p := by
  unfold s102_cc
  split_ifs with h
  · have hti : ((s102_node hT L p.1 : Set.Icc (0 : ℝ) T) : ℝ) ∈ Icc u T := ⟨h, (s102_node hT L p.1).2.2⟩
    have hc1 : ContDiff ℝ 1 (propagatorW C u ((s102_node hT L p.1 : Set.Icc (0 : ℝ) T) : ℝ) (oscTestFun m p.2)) :=
      (hD.smoothU p.2 u hu _ hti).of_le (by exact_mod_cast Nat.le_add_left 1 r)
    have : (fun x => gradient (propagatorW C u ((s102_node hT L p.1 : Set.Icc (0 : ℝ) T) : ℝ)
        (oscTestFun m p.2)) x a) = fun x => fderiv ℝ (propagatorW C u ((s102_node hT L p.1 : Set.Icc (0 : ℝ) T) : ℝ)
        (oscTestFun m p.2)) x (EuclideanSpace.single a (1 : ℝ)) := funext fun x => s102_gradient_apply _ x a
    rw [this]
    exact (hc1.continuous_fderiv (by simp)).clm_apply continuous_const
  · exact continuous_const

end HRS.MS.R2Interp

end
