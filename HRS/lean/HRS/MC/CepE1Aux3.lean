import HRS.MC.CepE1Aux2
import HRS.Dynamics.Setup

/-!
# Packet CEPE1, auxiliary 3: the potential `V` along a line, periodicity of its gradient, and the matrix action
-/

open Set Real
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE1

open HRS HRS.MC.CepK1

theorem cepe1_exists_int {x x' : Euc 1} (h : Torus.mk x = Torus.mk x') :
    ∃ n : ℤ, x' = x + Lattice.toEuc (fun _ => n) := by
  have h0 := congrFun h 0
  simp only [Torus.mk] at h0
  have h1 : (((x' 0 - x 0 : ℝ)) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, ← h0, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at h1
  obtain ⟨n, hn⟩ := h1
  refine ⟨n, ?_⟩
  ext i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  simp [Lattice.toEuc]
  simp at hn
  linarith [hn]

theorem cepe1_gradient_mk_eq {V : Torus 1 → ℝ} {x x' : Euc 1} (h : Torus.mk x = Torus.mk x') :
    gradient (Torus.lift V) x' = gradient (Torus.lift V) x := by
  obtain ⟨n, hn⟩ := cepe1_exists_int h
  have hp : (fun w => Torus.lift V (w + Lattice.toEuc (fun _ : Fin 1 => n))) = Torus.lift V :=
    funext fun w => Torus.lift_periodic V w _
  unfold gradient
  rw [hn, ← fderiv_comp_add_right (Lattice.toEuc (fun _ : Fin 1 => n)) (f := Torus.lift V) (x := x), hp]

theorem cepe1_V {V : Torus 1 → ℝ} (h1 : Torus.IsCk 1 V) {L : ℝ≥0}
    (hL : LipschitzWith L (gradient (Torus.lift V))) :
    ContDiff ℝ 1 (fun u : ℝ => Torus.lift V (cepk1_ι u)) ∧
    (∀ u, HasDerivAt (fun u : ℝ => Torus.lift V (cepk1_ι u))
      ((gradient (Torus.lift V) (cepk1_ι u)) 0) u) ∧
    LipschitzWith L (fun u : ℝ => (gradient (Torus.lift V) (cepk1_ι u)) 0) := by
  have hdiff : Differentiable ℝ (Torus.lift V) := h1.differentiable (by simp)
  refine ⟨h1.comp (cepk1_contDiff_ι.of_le (by exact_mod_cast le_top)), fun u => ?_, ?_⟩
  · have hι : HasDerivAt cepk1_ι (cepk1_ι 1) u := by
      have : cepk1_ι = fun u : ℝ => u • cepk1_ι 1 := by
        funext u; ext i; simp [cepk1_ι]
      rw [this]
      simpa using (hasDerivAt_id u).smul_const (cepk1_ι 1)
    have := (hdiff (cepk1_ι u)).hasFDerivAt.comp_hasDerivAt u hι
    have e : (fderiv ℝ (Torus.lift V) (cepk1_ι u)) (cepk1_ι 1) =
        (gradient (Torus.lift V) (cepk1_ι u)) 0 := by
      calc (fderiv ℝ (Torus.lift V) (cepk1_ι u)) (cepk1_ι 1)
          = inner ℝ (gradient (Torus.lift V) (cepk1_ι u)) (cepk1_ι 1) := (inner_gradient_left).symm
        _ = _ := by rw [PiLp.inner_apply]; simp [cepk1_ι]
    rw [e] at this
    exact this
  · refine LipschitzWith.of_dist_le_mul fun u v => ?_
    have h1 := hL.dist_le_mul (cepk1_ι u) (cepk1_ι v)
    have h2 : dist (cepk1_ι u) (cepk1_ι v) = dist u v := by
      rw [dist_eq_norm, Real.dist_eq, ← cepk1_norm_ι]
      congr 1
    have h3 : dist ((gradient (Torus.lift V) (cepk1_ι u)) 0) ((gradient (Torus.lift V) (cepk1_ι v)) 0) ≤
        dist (gradient (Torus.lift V) (cepk1_ι u)) (gradient (Torus.lift V) (cepk1_ι v)) := by
      rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs]
      exact (PiLp.norm_apply_le _ 0).trans_eq' (by simp)
    rw [h2] at h1
    exact h3.trans h1

theorem cepe1_hasDerivAt_neglog {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u : ℝ => -Real.log (2 * Real.sin (π * u)))
      (-(π * (Real.cos (π * u) / Real.sin (π * u)))) u := by
  have hs : 0 < Real.sin (π * u) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hu.1) (by nlinarith [Real.pi_pos, hu.2])
  have h1 : HasDerivAt (fun u : ℝ => 2 * Real.sin (π * u)) (2 * (Real.cos (π * u) * π)) u := by
    have := ((Real.hasDerivAt_sin (π * u)).comp u ((hasDerivAt_id u).const_mul π))
    simpa using this.const_mul 2
  have := (h1.log (by positivity)).neg
  convert this using 1
  field_simp

theorem cepe1_matVec {a : ℝ} {M : Matrix (Fin 1) (Fin 1) ℝ} (hM : M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
    (v : Euc 1) : (Torus.matVec M v) 0 = -a * v 0 := by
  subst hM
  simp [Torus.matVec]

end HRS.MC.CepE1
