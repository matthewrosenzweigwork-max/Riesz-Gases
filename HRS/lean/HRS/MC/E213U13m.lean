import HRS.MC.E213U13l
import HRS.Sections.QuenchAux18

/-!
# E213U13m: time integrals of bounded linear functionals of a field with second-chaos coordinates
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U13

section Lin

open HRS HRS.Qch

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}
  {ν : Measure ℝ} [SFinite ν] {r : ℝ}

theorem coord_eq_fourierCoeff (x : NegSobolev d r) (j : NonzeroLattice d) :
    NegSobolev.coord x j = (Lattice.jp j.1 ^ r)⁻¹ * NegSobolev.fourierCoeff x j := by
  unfold NegSobolev.fourierCoeff
  have : 0 < Lattice.jp j.1 ^ r := Real.rpow_pos_of_pos (Torus.jp_pos j.1) r
  field_simp

theorem measurable_eproj (F : Finset (NonzeroLattice d)) : Measurable (fun x : NegSobolev d r => eproj F x) := by
  unfold eproj
  exact Finset.measurable_sum _ fun j _ => (measurable_coord j).smul_const _

theorem InQ2.of_linear_integral {hξ : IsStdGaussianSeq P ξ} (Bf : ℝ → Ω → NegSobolev d r)
    (hBm : Measurable (fun p : Ω × ℝ => Bf p.2 p.1))
    (hB1 : ∀ᵐ v ∂ν, ∀ k, InQ2 hξ (fun ω => NegSobolev.fourierCoeff (Bf v ω) k))
    (hBint : ∀ᵐ ω ∂P, Integrable (fun v => ‖Bf v ω‖) ν)
    (hBL2 : MemLp (fun ω => ∫ v, ‖Bf v ω‖ ∂ν) 2 P)
    (Λ : ℝ → NegSobolev d r →L[ℝ] ℝ) (C0 : ℝ) (hC0 : 0 ≤ C0) (hΛ : ∀ v, ‖Λ v‖ ≤ C0)
    (hΛm : Measurable (fun p : ℝ × NegSobolev d r => Λ p.1 p.2))
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZ : Z =ᵐ[P] fun ω => ∫ v, Λ v (Bf v ω) ∂ν) : InQ2 hξ Z := by
  classical
  obtain ⟨F, hF⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset (NonzeroLattice d)))
  have hBm' : Measurable (fun p : Ω × ℝ => Λ p.2 (Bf p.2 p.1)) :=
    hΛm.comp (measurable_snd.prodMk hBm)
  refine InQ2.of_prod_limit (ν := ν) (f := fun n ω v => Λ v (eproj (F n) (Bf v ω)))
    (g := fun ω v => Λ v (Bf v ω)) (B := fun ω v => C0 * ‖Bf v ω‖) hZ2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hZ
  · intro n
    exact hΛm.comp (measurable_snd.prodMk ((measurable_eproj (F n)).comp hBm))
  · exact hBm'
  · exact (measurable_const.mul hBm.norm)
  · intro ω v; exact mul_nonneg hC0 (norm_nonneg _)
  · intro n
    filter_upwards [hB1] with v hv
    have e : ∀ ω, Λ v (eproj (F n) (Bf v ω)) = ∑ j ∈ F n, (Λ v (esingle r j) * (Lattice.jp j.1 ^ r)⁻¹) *
        NegSobolev.fourierCoeff (Bf v ω) j := by
      intro ω
      unfold eproj
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, coord_eq_fourierCoeff]
      ring
    simp_rw [e]
    exact InQ2.sum _ fun j _ => InQ2.const_mul _ (hv j)
  · intro ω v
    exact ((Λ v).continuous.tendsto _).comp ((by
      have := hasSum_esingle (Bf v ω)
      exact this.comp hF : Tendsto (fun n => eproj (F n) (Bf v ω)) atTop (𝓝 (Bf v ω))))
  · intro n ω v
    rw [← Real.norm_eq_abs]
    calc ‖Λ v (eproj (F n) (Bf v ω))‖ ≤ ‖Λ v‖ * ‖eproj (F n) (Bf v ω)‖ := (Λ v).le_opNorm _
      _ ≤ C0 * ‖Bf v ω‖ := mul_le_mul (hΛ v) (norm_eproj_le _ _) (norm_nonneg _) hC0
  · filter_upwards [hBint] with ω hω
    exact hω.const_mul C0
  · have e : (fun ω => ∫ v, C0 * ‖Bf v ω‖ ∂ν) = fun ω => C0 * ∫ v, ‖Bf v ω‖ ∂ν := by
      funext ω; exact integral_const_mul _ _
    rw [e]
    exact hBL2.const_mul C0

end Lin

end HRS.MC.E213U13
