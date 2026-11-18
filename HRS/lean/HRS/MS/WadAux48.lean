import HRS.MS.WadAux47

/-!
# S8.3 (Route A): `r ↦ ℒ f_r (x₀)` is continuous for `C²_b` families

See `WadAux47`.  Used to show that the mean `m(r) = μ(ℒ f_r)` of a projected solution is continuous in `r`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem s85_grad_cont_r {t : ℝ} {f : ℝ → Euc d → ℝ}
    (hD1 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (f q.1) q.2) (Set.Icc 0 t ×ˢ Set.univ)) (y : Euc d) :
    ContinuousOn (fun r => gradient (f r) y) (Set.Icc 0 t) := by
  have h1 : ContinuousOn (fun r => fderiv ℝ (f r) y) (Set.Icc 0 t) :=
    hD1.comp (Continuous.prodMk continuous_id continuous_const).continuousOn
      (fun r hr => ⟨hr, Set.mem_univ _⟩)
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn h1

theorem s85_u_cont_r {t : ℝ} {f : ℝ → Euc d → ℝ} {ρ : Euc d → ℝ}
    (hgrad : ∀ y : Euc d, ContinuousOn (fun r => gradient (f r) y) (Set.Icc 0 t)) (j : Fin d) (y : Euc d) :
    ContinuousOn (fun r => ρ y *
      (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient (f r) y)) j) (Set.Icc 0 t) := by
  have e : (fun r => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient (f r) y)) j) =
      fun r => ρ y * (-(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) (gradient (f r) y)) := by
    funext r
    rw [s84_matVec_neg_T]
    simp
  rw [e]
  exact continuousOn_const.mul (((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp_continuousOn
    (hgrad y)).neg)

theorem s85_conv_cont_r (hd : 2 ≤ d) {t : ℝ} {ρ : Euc d → ℝ} {u : ℝ → Euc d → ℝ} {A : ℝ} (hA0 : 0 ≤ A)
    (hmeas : ∀ r ∈ Set.Icc (0 : ℝ) t, Measurable (u r))
    (hA : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ y, |u r y| ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (hH : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ z : Euc d, ‖z‖ ≤ 1 / 4 → ∀ x', |u r (x' - z) - u r x'| ≤ A * ‖z‖ ^ (1 / 2 : ℝ))
    (hcont : ∀ y : Euc d, ContinuousOn (fun r => u r y) (Set.Icc 0 t)) (x₀ : Euc d) :
    ContinuousOn (fun r => convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) (u r) x₀) (Set.Icc 0 t) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hs1 : (d : ℝ) / 2 + 1 / 2 < (d : ℝ) := by linarith
  obtain ⟨bd, hbdi, hbd⟩ := s85_conv_dom hd hs0 hs1 (A := A) (H := A) hA0 hA0 x₀
  unfold convGradConvW
  refine continuousOn_of_dominated (bound := bd) (fun r hr => ?_) (fun r hr => ?_) hbdi
    (Filter.Eventually.of_forall fun y => ?_)
  · have hGm : Measurable (rieszKernelGrad d ((d : ℝ) / 2)) := movtr_rieszKernelGrad_measurable _
    refine Measurable.aestronglyMeasurable (Measurable.ite
      (measurableSet_le (measurable_norm.comp (measurable_const.sub measurable_id)) measurable_const) ?_ ?_)
    · exact ((hmeas r hr).sub measurable_const).smul (hGm.comp (measurable_const.sub measurable_id))
    · exact (hmeas r hr).smul (hGm.comp (measurable_const.sub measurable_id))
  · exact hbd (hA r hr) (hH r hr)
  · by_cases hc : ‖x₀ - y‖ ≤ 1 / 4
    · simp only [hc, if_true]
      exact ((hcont y).sub (hcont x₀)).smul continuousOn_const
    · simp only [hc, if_false]
      exact (hcont y).smul continuousOn_const

theorem s85_gen_cont_r (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} {f : ℝ → Euc d → ℝ}
    (hc2 : ∀ r ∈ Set.Icc 0 t, ContDiff ℝ 2 (f r))
    (hB : ∃ B : ℝ, ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (f r) y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ (f r)) y‖ ≤ B)
    (hD1 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (f q.1) q.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hD2 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (fderiv ℝ (f q.1)) q.2) (Set.Icc 0 t ×ˢ Set.univ))
    (x₀ : Euc d) :
    ContinuousOn (fun r => generatorW (critCoeff d a β ρβ) r (f r) x₀) (Set.Icc 0 t) := by
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  obtain ⟨B, hB⟩ := hB
  obtain ⟨Lu, hLu0, hLu⟩ := s84_u_facts hd hg
  have hgrad := s85_grad_cont_r (f := f) hD1
  have hL0' := (s83_L0_contOn a β⁻¹ hD1 hD2).comp (Continuous.prodMk continuous_id (continuous_const (y := x₀))).continuousOn
    (fun (r : ℝ) (hr : r ∈ Set.Icc 0 t) => (⟨hr, Set.mem_univ x₀⟩ : (r, x₀) ∈ Set.Icc 0 t ×ˢ (Set.univ : Set (Euc d))))
  have hL0 : ContinuousOn (fun r => s83_L0 a β⁻¹ (f r) x₀) (Set.Icc 0 t) := hL0'
  have hin : ContinuousOn (fun r => inner ℝ (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρβ x₀)) (gradient (f r) x₀)) (Set.Icc 0 t) :=
    continuousOn_const.inner (hgrad x₀)
  have hC2 : ∀ r ∈ Set.Icc (0 : ℝ) t, s84_C2b (f r) (max B 0) := fun r hr => ⟨hc2 r hr, fun y =>
    ⟨(hB r hr y).1.trans (le_max_left _ _), (hB r hr y).2.trans (le_max_left _ _)⟩⟩
  have hsum : ContinuousOn (fun r => ∑ j : Fin d, (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
      (fun y => ρβ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient (f r) y)) j) x₀) j)
      (Set.Icc 0 t) := by
    refine continuousOn_finset_sum _ fun j _ => ?_
    have hv := s85_conv_cont_r hd (t := t) (ρ := ρβ)
      (u := fun r y => ρβ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient (f r) y)) j)
      (A := Lu * max B 0) (by positivity) (fun r hr => (hLu (hC2 r hr) j).1)
      (fun r hr => (hLu (hC2 r hr) j).2.1) (fun r hr => (hLu (hC2 r hr) j).2.2)
      (fun y => s85_u_cont_r hgrad j y) x₀
    exact (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp_continuousOn hv
  refine (hL0.add (hin.sub hsum)).congr fun r _ => ?_
  exact s83_generator_decomp a β ρβ r (f r) x₀

end HRS.MS.Wad
