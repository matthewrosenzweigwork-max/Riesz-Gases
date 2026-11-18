import HRS.MS.Fp81S21MovingInputs2
import HRS.MS.R2InterpAux53
import HRS.MS.SpecAux91

/-!
# HRS S2.1(iii): moving-density Gram continuity

The moving Gram entries are continuous in their active starting-time interval.  The proof uses
the jointly continuous moving density and its uniform Gaussian upper envelope as the dominated-
convergence majorant.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

private theorem fp81s21_moving_density_joint_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    Continuous fun z : ℝ≥0 × Euc p.d => R.ρ z.1 z.2 := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρβc : Continuous R.ρβ := by
    obtain ⟨-, ψ', hψ'⟩ := HRS.MS.S21.s21_schwartz_thermal
      p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ']
    exact ψ'.continuous
  have hρβpos : ∀ x, 0 < R.ρβ x := fun x => HRS.Whole.u4_thermal_pos R.thermal x
  have hm : (p.d : ℝ) / 2 < ((102 * p.d + 1020 : ℕ) : ℝ) := by
    rw [HRS.MS.R2WinOrbNL.s103n_cast_m]
    nlinarith
  have hclass := HRS.MS.R2WinOrbNL.s103n_small_class R.resulting
    (r := p.C₁ * δ) le_rfl
  exact HRS.MS.R2S11.s11_class_continuous hρβc hρβpos hm hclass

/-- Moving-density analogue of `s102_gram_cont`, on the exact active interval used by `hGram`. -/
theorem fp81s21_moving_gram_continuous_of_fields
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    (hnn : ∀ u ∈ Icc (0 : ℝ) H, ∀ x, 0 ≤ R.ρ u x)
    (hgauss : ∃ C₀ c₀ : ℝ, 0 < c₀ ∧
      ∀ u ∈ Icc (0 : ℝ) H, ∀ x,
        R.ρ u x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2))
    (hcls : ∀ (α : MultiIndex p.d) (t : ℝ), t ∈ Icc (0 : ℝ) H →
      ∃ f, IsClassicalAdjointW (r26t3_coeff R) t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) f) :
    ∀ (L : ℕ) (i j : Fin (s102_q p.d L)),
      ContinuousOn
        (fun u => s102_gram (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) hH L u i j)
        (Icc 0 (min (s102_tk hH L i) (s102_tk hH L j))) := by
  obtain ⟨C₀, c₀, hc₀, hC₀⟩ := hgauss
  have hjoint := fp81s21_moving_density_joint_continuous p R hδ hδh
  intro L i j
  have hi : s102_tk hH L i ∈ Icc (0 : ℝ) H := (s102_tauk hH L i).2
  have hj : s102_tk hH L j ∈ Icc (0 : ℝ) H := (s102_tauk hH L j).2
  have hF := s102_propagator_classical (hcls (s102_alk L i) _ hi)
  have hG := s102_propagator_classical (hcls (s102_alk L j) _ hj)
  obtain ⟨BF, hBF⟩ := s102_grad_bdd hF
  obtain ⟨BG, hBG⟩ := s102_grad_bdd hG
  set S : Set ℝ := Icc 0 (min (s102_tk hH L i) (s102_tk hH L j)) with hS
  have hSi : S ⊆ Icc 0 (s102_tk hH L i) := Icc_subset_Icc le_rfl (min_le_left _ _)
  have hSj : S ⊆ Icc 0 (s102_tk hH L j) := Icc_subset_Icc le_rfl (min_le_right _ _)
  have hC₀nonneg : 0 ≤ C₀ := by
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) H := ⟨le_rfl, hH.le⟩
    have hz := hC₀ 0 hzero (0 : Euc p.d)
    have hnz := hnn 0 hzero (0 : Euc p.d)
    simpa using le_trans hnz hz
  have hdom : Integrable
      (fun x : Euc p.d => ((p.d : ℝ) * |BF| * |BG| * C₀) *
        Real.exp (-c₀ * ‖x‖ ^ 2)) := by
    simpa [mul_assoc] using
      (HRS.MS.Spec.s8p_integrable_exp_neg_mul_sq_norm (V := Euc p.d) hc₀).const_mul
        ((p.d : ℝ) * |BF| * |BG| * C₀)
  unfold s102_gram
  refine continuousOn_of_dominated
    (bound := fun x : Euc p.d => ((p.d : ℝ) * |BF| * |BG| * C₀) *
      Real.exp (-c₀ * ‖x‖ ^ 2)) ?_ ?_ ?_ ?_
  · intro u hu
    have huH : u ∈ Icc (0 : ℝ) H := by
      have hu' := (hSi hu)
      exact ⟨hu'.1, le_trans hu'.2 hi.2⟩
    have hρx : Continuous (fun x : Euc p.d => R.ρ u x) := by
      let uNN : ℝ≥0 := ⟨u, huH.1⟩
      have hmap : Continuous (fun x : Euc p.d => (uNN, x)) := by fun_prop
      have hc := hjoint.comp hmap
      have heq : (fun x : Euc p.d => R.ρ (↑uNN) x) = fun x => R.ρ u x := by
        funext x
        rfl
      exact heq ▸ hc
    refine AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_) hρx.aestronglyMeasurable
    simp_rw [s102_inner_eq_sum]
    exact continuous_finsetSum _ fun a _ =>
      (s102_grad_contAt_x hF (hSi hu) a).mul (s102_grad_contAt_x hG (hSj hu) a)
  · intro u hu
    have huH : u ∈ Icc (0 : ℝ) H := by
      have hu' := (hSi hu)
      exact ⟨hu'.1, le_trans hu'.2 hi.2⟩
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [show (r26t3_coeff R).ρ u x = R.ρ u x by rfl,
      abs_of_nonneg (hnn u huH x)]
    rw [s102_inner_eq_sum]
    have h1 :
        |∑ a : Fin p.d,
          gradient (propagatorW (r26t3_coeff R) u (s102_tk hH L i)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) (s102_alk L i))) x a *
          gradient (propagatorW (r26t3_coeff R) u (s102_tk hH L j)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) (s102_alk L j))) x a| ≤
          (p.d : ℝ) * |BF| * |BG| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc
        _ ≤ ∑ _a : Fin p.d, |BF| * |BG| := Finset.sum_le_sum fun a _ => by
              rw [abs_mul]
              exact mul_le_mul
                ((hBF u (hSi hu) x a).trans (le_abs_self _))
                ((hBG u (hSj hu) x a).trans (le_abs_self _))
                (abs_nonneg _) (abs_nonneg _)
        _ = _ := by simp [mul_assoc]
    have hcoef : 0 ≤ (p.d : ℝ) * |BF| * |BG| := by positivity
    calc
      |∑ a : Fin p.d,
          gradient (propagatorW (r26t3_coeff R) u (s102_tk hH L i)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) (s102_alk L i))) x a *
          gradient (propagatorW (r26t3_coeff R) u (s102_tk hH L j)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) (s102_alk L j))) x a| * R.ρ u x
          ≤ ((p.d : ℝ) * |BF| * |BG|) * R.ρ u x :=
            mul_le_mul_of_nonneg_right h1 (hnn u huH x)
      _ ≤ ((p.d : ℝ) * |BF| * |BG|) *
            (C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hC₀ u huH x) hcoef
      _ = ((p.d : ℝ) * |BF| * |BG| * C₀) *
            Real.exp (-c₀ * ‖x‖ ^ 2) := by ring
  · exact hdom
  · have hρtime : ∀ x : Euc p.d, ContinuousOn (fun u : ℝ => R.ρ u x) S := by
      intro x
      rw [continuousOn_iff_continuous_domRestrict]
      let hmap : S → ℝ≥0 × Euc p.d := fun u =>
        (⟨(u : ℝ), u.property.1⟩, x)
      have hmapc : Continuous hmap := by fun_prop
      have hc := hjoint.comp hmapc
      exact hc
    refine Filter.Eventually.of_forall fun x => ?_
    refine ContinuousOn.mul ?_ (hρtime x)
    simp_rw [s102_inner_eq_sum]
    exact continuousOn_finsetSum _ fun a _ =>
      ((s102_grad_contOn hF x a).mono hSi).mul
        ((s102_grad_contOn hG x a).mono hSj)

#print axioms HRS.Fp81.S21.fp81s21_moving_gram_continuous_of_fields

end HRS.Fp81.S21

end
