import HRS.MS.SpecAux50
import HRS.MS.QsfAux3
import HRS.MS.SuppU11Aux1
import HRS.Whole.CriticalNoise

/-!
# S8R: covariance entries of the empirical noise integrand (S8.7, coupling block C3)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  With `cs x a l = exp(-τ om_l/2) ∂_a e_l(x)` the coordinate sequence of the
feature `s8p_Gv x a ∈ ℓ²` (junk value `0` off the `good` set where the sequence is not square summable),

* `s8p_hsCov_entry`: for a configuration with all particles good, the `(i,j)` entry (in the standard basis `S45.s45_seqBasis`)
  of the covariance form `hsCovForm Φ` of `Φ(ia) = √(2/(Nβ)) • s8p_Gv (X_ia.1) ia.2` is
  `(2/β) exp(-τ(om_i+om_j)/2) μ_N(∇e_i·∇e_j)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole

variable {d : ℕ}

/-- The coordinate sequence `l ↦ exp(-τ om_l/2) ∂_a e_l(x)`. -/
def s8p_cs (om : ℕ → ℝ) (e : ℕ → Euc d → ℝ) (τ : ℝ) (x : Euc d) (a : Fin d) (l : ℕ) : ℝ :=
  Real.exp (-(τ * om l) / 2) * gradient (e l) x a

/-- The feature vector in `ℓ²` (`0` if the coordinate sequence is not square summable). -/
def s8p_Gv (om : ℕ → ℝ) (e : ℕ → Euc d → ℝ) (τ : ℝ) (x : Euc d) (a : Fin d) : SeqL2 :=
  SeqL2.ofSeq (s8p_cs om e τ x a)

/-- Good points: all coordinate sequences are square summable. -/
def s8p_good (om : ℕ → ℝ) (e : ℕ → Euc d → ℝ) (τ : ℝ) (x : Euc d) : Prop :=
  ∀ a, Memℓp (s8p_cs om e τ x a) 2

/-- The pair product `∇e_i·∇e_j`. -/
def s8p_f (e : ℕ → Euc d → ℝ) (i j : ℕ) (x : Euc d) : ℝ :=
  inner ℝ (gradient (e i) x) (gradient (e j) x)

theorem s8p_coord_smul (c : ℝ) (z : SeqL2) (l : ℕ) :
    SeqL2.coord (c • z) l = c * SeqL2.coord z l := rfl

theorem s8p_inner_basis (i : ℕ) (z : SeqL2) : ⟪z, S45.s45_seqBasis i⟫ = SeqL2.coord z i := by
  rw [real_inner_comm, S45.s45_inner_seqBasis]

theorem s8p_coord_Gv {om : ℕ → ℝ} {e : ℕ → Euc d → ℝ} {τ : ℝ} {x : Euc d}
    (hx : s8p_good om e τ x) (a : Fin d) (l : ℕ) :
    SeqL2.coord (s8p_Gv om e τ x a) l = s8p_cs om e τ x a l :=
  u11_coord_ofSeq (hx a) l

theorem s8p_cs_mul_sum (om : ℕ → ℝ) (e : ℕ → Euc d → ℝ) (τ : ℝ) (x : Euc d) (i j : ℕ) :
    ∑ a, s8p_cs om e τ x a i * s8p_cs om e τ x a j =
      Real.exp (-(τ * (om i + om j)) / 2) * s8p_f e i j x := by
  unfold s8p_cs s8p_f
  rw [PiLp.inner_apply]
  have h : Real.exp (-(τ * (om i + om j)) / 2) =
      Real.exp (-(τ * om i) / 2) * Real.exp (-(τ * om j) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem s8p_hsCov_entry {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 0 < β) (om : ℕ → ℝ)
    (e : ℕ → Euc d → ℝ) (τ : ℝ) (X : EucConfig d N) (hX : ∀ i, s8p_good om e τ (X i)) (i j : ℕ) :
    hsCovForm (fun ia : Fin N × Fin d => Real.sqrt (2 / (N * β)) • s8p_Gv om e τ (X ia.1) ia.2)
        (S45.s45_seqBasis i) (S45.s45_seqBasis j) =
      (2 / β) * Real.exp (-(τ * (om i + om j)) / 2) * linStat (s8p_f e i j) X := by
  unfold hsCovForm
  rw [tsum_fintype]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : Real.sqrt (2 / (N * β)) ^ 2 = 2 / (N * β) := Real.sq_sqrt (by positivity)
  have e1 : ∀ k : Fin N × Fin d,
      ⟪Real.sqrt (2 / (N * β)) • s8p_Gv om e τ (X k.1) k.2, S45.s45_seqBasis i⟫ *
        ⟪Real.sqrt (2 / (N * β)) • s8p_Gv om e τ (X k.1) k.2, S45.s45_seqBasis j⟫ =
      (2 / (N * β)) * (s8p_cs om e τ (X k.1) k.2 i * s8p_cs om e τ (X k.1) k.2 j) := by
    intro k
    rw [s8p_inner_basis, s8p_inner_basis, s8p_coord_smul, s8p_coord_smul,
      s8p_coord_Gv (hX k.1), s8p_coord_Gv (hX k.1)]
    rw [show ∀ u v : ℝ, Real.sqrt (2 / (N * β)) * u * (Real.sqrt (2 / (N * β)) * v) =
      (Real.sqrt (2 / (N * β)) * Real.sqrt (2 / (N * β))) * (u * v) from fun u v => by ring,
      Real.mul_self_sqrt (by positivity)]
  simp_rw [e1]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  have e2 : ∑ x : Fin N, ∑ y : Fin d, s8p_cs om e τ (X x) y i * s8p_cs om e τ (X x) y j =
      Real.exp (-(τ * (om i + om j)) / 2) * ∑ x : Fin N, s8p_f e i j (X x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => s8p_cs_mul_sum om e τ (X x) i j
  rw [e2]
  unfold linStat
  rw [HRS.Whole.pair_empirical hN]
  field_simp

end HRS.MS.Spec
