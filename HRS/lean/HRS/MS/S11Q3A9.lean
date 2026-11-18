import HRS.MS.S11Q3A8
import HRS.MP.RdRemainder

/-!
# S11.3 / S11.4 (worker S11Q3), A9: the normalizer `K̂(t) = ∫ W_t(X) dX` is positive, continuous and `C¹` on `[0,∞)`

`s11q3_Khat_facts`: for a regular family, `K̂ > 0` on `[0,∞)`, `K̂` and `K̂' = ∫ ∂_tW` are continuous on `[0,∞)`, and `K̂' ` is the derivative
(two-sided for `t > 0`, right derivative at all `t ≥ 0`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11Q3

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.S113BD

variable {d : ℕ} {s : ℝ}

theorem s11q3_slice_t {f : ℝ → Euc d → ℝ} (hf : ContinuousOn (fun p : ℝ × Euc d => f p.1 p.2) (Ici 0 ×ˢ univ))
    (x : Euc d) : ContinuousOn (fun τ => f τ x) (Ici 0) :=
  hf.comp (continuous_id.prodMk continuous_const).continuousOn fun τ hτ => ⟨hτ, mem_univ _⟩

theorem s11q3_F0_measurable {N : ℕ} : Measurable (s11q3_F0 d s N) := by
  unfold s11q3_F0
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
  exact (HRS.MP.RdRem.mrr_measurable_rieszKernel s).comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

section Khat

variable {ρ D : ℝ → Euc d → ℝ} {c B : ℝ}

def s11q3_Khat (d : ℕ) (s β : ℝ) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (t : ℝ) : ℝ := ∫ X : EucConfig d N, s11q3_W d s β N ρ t X

def s11q3_Khat' (d : ℕ) (s β : ℝ) (N : ℕ) (ρ D : ℝ → Euc d → ℝ) (t : ℝ) : ℝ :=
  ∫ X : EucConfig d N, s11q3_W' d s β N ρ D t X

theorem s11q3_Reg.gamD_cont (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (s11q3_Gam d s (D t)) :=
  (s11q3_GamD_cont (s := s) hd hs0 hsd R).comp_continuous (continuous_const.prodMk continuous_id)
    (fun x => ⟨Set.mem_Ici.2 ht, mem_univ _⟩)

theorem s11q3_Khat_facts (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 1 ≤ N) :
    (∀ t, 0 ≤ t → 0 < s11q3_Khat d s β N ρ t) ∧ ContinuousOn (s11q3_Khat d s β N ρ) (Ici 0) ∧
      ContinuousOn (s11q3_Khat' d s β N ρ D) (Ici 0) ∧
      (∀ t, 0 < t → HasDerivAt (s11q3_Khat d s β N ρ) (s11q3_Khat' d s β N ρ D t) t) ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt (s11q3_Khat d s β N ρ) (s11q3_Khat' d s β N ρ D t) (Ici t) t) := by
  obtain ⟨a0, a1, k0, k1, hk0, hk1, hbd⟩ := s11q3_W_bound hd hs0 hsd R hβ hN
  have hint : Integrable (s11q3_h (d := d) a0 a1 B c k0 k1) := s11q3_h_integrable hd R.hc R.hB hk0 hk1
  have hbint : Integrable (fun X : EucConfig d N => (N : ℝ) * ∏ a, s11q3_h a0 a1 B c k0 k1 (X a)) volume :=
    (Integrable.fintype_prod (f := fun _ x => s11q3_h (d := d) a0 a1 B c k0 k1 x) (μ := fun _ => volume)
      (fun _ => hint)).const_mul _
  -- pointwise continuity in `t`
  have hρt : ∀ x, ContinuousOn (fun τ => ρ τ x) (Ici 0) := s11q3_slice_t R.j0
  have hDt : ∀ x, ContinuousOn (fun τ => D τ x) (Ici 0) := s11q3_slice_t R.jD
  have hΓt : ∀ x, ContinuousOn (fun τ => s11q3_Gam d s (ρ τ) x) (Ici 0) :=
    s11q3_slice_t (s11q3_Gam_cont0 hd hs0 hsd R)
  have hΓDt : ∀ x, ContinuousOn (fun τ => s11q3_Gam d s (D τ) x) (Ici 0) :=
    s11q3_slice_t (s11q3_GamD_cont hd hs0 hsd R)
  have hEc : ∀ X : EucConfig d N, ContinuousOn (fun τ => s11q3_E d s β N ρ τ X) (Ici 0) := fun X => by
    unfold s11q3_E
    refine Real.continuous_exp.comp_continuousOn (continuousOn_const.add (continuousOn_const.mul ?_))
    exact continuousOn_finset_sum _ fun a _ => hΓt (X a)
  have hPc : ∀ X : EucConfig d N, ContinuousOn (fun τ => s11q3_P ρ τ X) (Ici 0) := fun X => by
    unfold s11q3_P
    exact continuousOn_finset_prod _ fun a _ => hρt (X a)
  have hWc : ∀ X : EucConfig d N, ContinuousOn (fun τ => s11q3_W d s β N ρ τ X) (Ici 0) := fun X =>
    (hEc X).mul (hPc X)
  have hW'c : ∀ X : EucConfig d N, ContinuousOn (fun τ => s11q3_W' d s β N ρ D τ X) (Ici 0) := fun X => by
    unfold s11q3_W'
    refine (((hEc X).mul (continuousOn_const.mul (continuousOn_finset_sum _ fun a _ => hΓDt (X a)))).mul (hPc X)).add
      ((hEc X).mul (continuousOn_finset_sum _ fun a _ => ?_))
    exact (continuousOn_finset_prod _ fun j _ => hρt (X j)).mul (hDt (X a))
  -- measurability
  have hEm : ∀ t, 0 ≤ t → Measurable (s11q3_E d s β N ρ t) := fun t ht => by
    unfold s11q3_E
    refine Real.measurable_exp.comp (Measurable.add (Measurable.const_mul s11q3_F0_measurable _) (Measurable.const_mul ?_ _))
    exact Finset.measurable_sum _ fun a _ =>
      ((s11q3_Gam_contDiff hd hs0 hsd R ht).continuous.measurable).comp (measurable_pi_apply a)
  have hPm : ∀ t, 0 ≤ t → Measurable (s11q3_P (N := N) ρ t) := fun t ht => by
    unfold s11q3_P
    exact Finset.measurable_prod _ fun a _ => ((R.cd t ht).continuous.measurable).comp (measurable_pi_apply a)
  have hWm : ∀ t, 0 ≤ t → AEStronglyMeasurable (s11q3_W d s β N ρ t) volume := fun t ht =>
    ((hEm t ht).mul (hPm t ht)).aestronglyMeasurable
  have hW'm : ∀ t, 0 ≤ t → AEStronglyMeasurable (s11q3_W' d s β N ρ D t) volume := fun t ht => by
    unfold s11q3_W'
    refine Measurable.aestronglyMeasurable (Measurable.add (((hEm t ht).mul (Measurable.const_mul ?_ _)).mul (hPm t ht))
      ((hEm t ht).mul (Finset.measurable_sum _ fun a _ => ?_)))
    · exact Finset.measurable_sum _ fun a _ => ((R.gamD_cont hd hs0 hsd ht).measurable).comp (measurable_pi_apply a)
    · exact (Finset.measurable_prod _ fun j _ => ((R.cd t ht).continuous.measurable).comp (measurable_pi_apply j)).mul
        ((R.sliceD_cont ht).measurable.comp (measurable_pi_apply a))
  -- derivative
  have hder : ∀ t, 0 < t → ∀ X : EucConfig d N,
      HasDerivAt (fun τ => s11q3_W d s β N ρ τ X) (s11q3_W' d s β N ρ D t X) t := by
    intro t ht X
    have hG : ∀ a ∈ (Finset.univ : Finset (Fin N)),
        HasDerivAt (fun τ => s11q3_Gam d s (ρ τ) (X a)) (s11q3_Gam d s (D t) (X a)) t :=
      fun a _ => s11q3_Gam_dt hd hs0 hsd R ht (X a)
    have hE : HasDerivAt (fun τ => s11q3_E d s β N ρ τ X)
        (s11q3_E d s β N ρ t X * (β * ∑ a, s11q3_Gam d s (D t) (X a))) t := by
      have := ((HasDerivAt.fun_sum hG).const_mul β).const_add (-β * N * s11q3_F0 d s N X)
      exact this.exp
    have hP : HasDerivAt (fun τ => s11q3_P ρ τ X)
        (∑ a, (∏ j ∈ Finset.univ.erase a, ρ t (X j)) • D t (X a)) t :=
      HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin N))) (f := fun a τ => ρ τ (X a))
        (f' := fun a => D t (X a)) (x := t) (fun a _ => R.dA t ht (X a))
    have := hE.mul hP
    unfold s11q3_W s11q3_W'
    refine this.congr_deriv ?_
    simp only [smul_eq_mul]
  obtain ⟨hD1, hC0, hC1⟩ := s11q3_param_C1 (μ := volume) (F := fun τ X => s11q3_W d s β N ρ τ X)
    (F' := fun τ X => s11q3_W' d s β N ρ D τ X) hbint hWm hW'm
    (fun t ht X => by rw [Real.norm_eq_abs]; exact (hbd t ht X).1)
    (fun t ht X => by rw [Real.norm_eq_abs]; exact (hbd t ht X).2) hder hWc hW'c
  have hKd : ∀ t, 0 < t → HasDerivAt (s11q3_Khat d s β N ρ) (s11q3_Khat' d s β N ρ D t) t := hD1
  refine ⟨fun t ht => ?_, hC0, hC1, hKd, s11q3_rightDeriv hC0 hKd hC1⟩
  have hpos : ∀ X : EucConfig d N, 0 < s11q3_W d s β N ρ t X := fun X => by
    unfold s11q3_W s11q3_E s11q3_P
    exact mul_pos (Real.exp_pos _) (Finset.prod_pos fun a _ => R.pos t ht (X a))
  have hWi : Integrable (s11q3_W d s β N ρ t) volume :=
    hbint.mono' (hWm t ht) (Filter.Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact (hbd t ht X).1)
  unfold s11q3_Khat
  rw [integral_pos_iff_support_of_nonneg (fun X => (hpos X).le) hWi]
  have : Function.support (s11q3_W d s β N ρ t) = univ :=
    Set.eq_univ_of_forall fun X => (hpos X).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 (NeZero.ne _)

end Khat

end HRS.MS.S11Q3

end
