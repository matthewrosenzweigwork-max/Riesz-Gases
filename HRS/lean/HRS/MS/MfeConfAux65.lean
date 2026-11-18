import HRS.MS.MfeConfAux64

/-!
# S.B.1, packet F6 (part 26): the source for a one-body tilt

For the tilt of the regularised system, `Ψ_s(Z) = ∑_i ψ_s(Z_i) + κ_s` with `∇ψ_s = -u_s`, the gradient field is the one-body
field `w_s(Z)_i = -u_s(Z_i)`.  `sb1_div_one` computes its divergence and `sb1_S_onebody` the source:
`S = ∑_i [div u(Z_i) + ⟨u(Z_i), b_i⟩/θ + |u(Z_i)|²/θ + ∂_sψ(Z_i)/θ] + κ̇/θ`.
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- The divergence of a one-body vector field on `ℝ^d`. -/
def sb1divE (u : Euc d → Euc d) (x : Euc d) : ℝ :=
  ∑ j : Fin d, fderiv ℝ (fun y => u y j) x (EuclideanSpace.single j 1)

/-- The one-body field `Z ↦ (i ↦ -u(Z_i))` on configuration space. -/
def sb1wOne (u : Euc d → Euc d) (Z : EucConfig d N) : EucConfig d N := fun i => -(u (Z i))

theorem sb1_div_one {u : Euc d → Euc d} (hu : ContDiff ℝ 1 u) (Z : EucConfig d N) :
    sb1div (sb1wOne u) Z = -∑ i, sb1divE u (Z i) := by
  have hj : ∀ j : Fin d, ContDiff ℝ 1 (fun y => u y j) := fun j => contDiff_euclidean.1 hu j
  unfold sb1div sb1divE
  rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hg := ((hj j).differentiable (by norm_num) (Z i)).hasFDerivAt
  have h1 := (hg.comp (f := fun Y : EucConfig d N => Y i) Z (hasFDerivAt_apply i Z)).fun_neg
  have h3 : fderiv ℝ (fun Y : EucConfig d N => -(u (Y i) j)) Z =
      -((fderiv ℝ (fun y => u y j) (Z i)).comp (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin N => Euc d) i)) := h1.fderiv
  have h2 : (fun Y : EucConfig d N => sb1wOne u Y i j) = fun Y => -(u (Y i) j) := by
    funext Y; simp [sb1wOne]
  rw [h2, h3]
  simp [configBasis]

theorem sb1_S_onebody {θ : ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {uv : ℝ → Euc d → Euc d}
    (huv : ∀ r, ContDiff ℝ 1 (uv r)) {Wψ : ℝ → EucConfig d N → ℝ} {wψ1 : ℝ → Euc d → ℝ} {κ : ℝ → ℝ}
    (hW : ∀ r Z, Wψ r Z = ∑ i, wψ1 r (Z i) + κ r) (r : ℝ) (Z : EucConfig d N) :
    sb1S θ b (fun r => sb1wOne (uv r)) Wψ r Z =
      ∑ i, (sb1divE (uv r) (Z i) + inner ℝ (uv r (Z i)) (b r Z i) / θ + ‖uv r (Z i)‖ ^ 2 / θ +
        wψ1 r (Z i) / θ) + κ r / θ := by
  have hip : p4InnerL (sb1wOne (uv r) Z) (b r Z) = -∑ i, inner ℝ (uv r (Z i)) (b r Z i) := by
    rw [p4k_p4InnerL_apply]
    simp [sb1wOne, inner_neg_left, Finset.sum_neg_distrib]
  have hq : p4m_q (sb1wOne (uv r) Z) = ∑ i, ‖uv r (Z i)‖ ^ 2 := by
    unfold p4m_q
    simp [sb1wOne]
  have e : ∑ i, (sb1divE (uv r) (Z i) + inner ℝ (uv r (Z i)) (b r Z i) / θ + ‖uv r (Z i)‖ ^ 2 / θ +
      wψ1 r (Z i) / θ) = ∑ i, sb1divE (uv r) (Z i) + (∑ i, inner ℝ (uv r (Z i)) (b r Z i)) / θ +
        (∑ i, ‖uv r (Z i)‖ ^ 2) / θ + (∑ i, wψ1 r (Z i)) / θ := by
    simp only [Finset.sum_add_distrib, Finset.sum_div]
  unfold sb1S
  rw [sb1_div_one (huv r), hW, hip, hq, e]
  ring

end HRS.MS.MfeConf
