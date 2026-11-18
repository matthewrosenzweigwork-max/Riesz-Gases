import HRS.Energy.Commutator.RenormStjPoint

/-!
# Route S, packet STJ: integrating the master inequality in `l`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

theorem lint_bound {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (h0 : ∀ l ∈ Ioi (0 : ℝ), 0 ≤ f l) {B : ℝ}
    (hB : ∫ l in Ioi (0 : ℝ), f l ≤ B) :
    ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (f l) ≤ ENNReal.ofReal B ∧ 0 ≤ B ∧
      AEMeasurable (fun l => ENNReal.ofReal (f l)) (volume.restrict (Ioi (0 : ℝ))) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall h0)
  refine ⟨?_, (integral_nonneg_of_ae hnn).trans hB, hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hf hnn]
  exact ENNReal.ofReal_le_ofReal hB

theorem measurable_Jl_l (d : ℕ) : Measurable fun l : ℝ => Jl d l := by
  unfold Jl
  have h : Measurable fun q : ℝ × Torus d => KernelGrad.tdist q.2 0 * ‖SliceAux.sgv q.1 q.2‖ :=
    (EnergyAux.measurable_tdist_zero.comp measurable_snd).mul SliceAux.measurable_sgv.norm
  exact (h.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Torus d)))).measurable

theorem measurable_Wb_l (d : ℕ) (ρ : ℝ) : Measurable fun l : ℝ => Wb d l ρ := by
  unfold Wb
  have h : Measurable fun q : ℝ × Torus d => if KernelGrad.tdist q.2 0 ≤ ρ then ‖SliceAux.sgv q.1 q.2‖ else 0 :=
    Measurable.ite (measurableSet_le (EnergyAux.measurable_tdist_zero.comp measurable_snd) measurable_const)
      SliceAux.measurable_sgv.norm measurable_const
  exact (h.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Torus d)))).measurable

theorem aemeasurable_mass (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) :
    AEMeasurable (fun l : ℝ => mass d l η) (volume.restrict (Ioi (0 : ℝ))) := by
  have h : Measurable fun l : ℝ => l * yukawa d l η * (η ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1)) +
      cflm d l η * (volume : Measure (Euc d)).toSphere.real univ :=
    ((measurable_id.mul (measurable_yukawa_l d η)).mul_const _).add ((measurable_cflm_l d η).mul_const _)
  refine h.aemeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
  have hl' : (0 : ℝ) < l := hl
  rw [mass_eq hd hl' hη, cfl_eq_cflm hd hl' hη]

theorem aemeasurable_muMaj (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) :
    AEMeasurable (fun l : ℝ => muMaj d l η) (volume.restrict (Ioi (0 : ℝ))) := by
  unfold muMaj
  exact (measurable_Wt_l d η).aemeasurable.add ((aemeasurable_mass hd hη).mul
    ((measurable_Wt_l d (2 * η)).aemeasurable.add ((measurable_Wb_l d (2 * η)).const_mul η).aemeasurable))

theorem muMaj_nonneg (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) : 0 ≤ muMaj d l η := by
  unfold muMaj
  have h1 : ∀ ρ : ℝ, 0 ≤ Wt d l ρ := fun ρ => integral_nonneg fun z => by
    dsimp only; split_ifs
    · exact mul_nonneg (KernelGrad.tdist_nonneg z 0) (norm_nonneg _)
    · exact le_rfl
  have h2 : ∀ ρ : ℝ, 0 ≤ Wb d l ρ := fun ρ => integral_nonneg fun z => by
    dsimp only; split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hm : 0 ≤ mass d l η := measureReal_nonneg
  have a1 := h1 η
  have a2 := h1 (2 * η)
  have a3 := h2 (2 * η)
  have a4 : 0 ≤ η := hη.le
  positivity

theorem split_bound {ι : Type*} [Fintype ι] (w a1 a2 a3 c : ℝ) (mm tt : ι → ℝ) (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hmm : ∀ i, 0 ≤ mm i) (htt : ∀ i, 0 ≤ tt i) :
    ENNReal.ofReal w * ENNReal.ofReal (a1 + a2 + a3 + c * ∑ i, mm i + c * ∑ i, tt i) ≤
      ENNReal.ofReal (w * a1) + ENNReal.ofReal (w * a2) + ENNReal.ofReal w * ENNReal.ofReal a3 +
        ∑ i, ENNReal.ofReal c * (ENNReal.ofReal w * ENNReal.ofReal (mm i)) +
        ∑ i, ENNReal.ofReal c * (ENNReal.ofReal w * ENNReal.ofReal (tt i)) := by
  have h1 : ENNReal.ofReal (a1 + a2 + a3 + c * ∑ i, mm i + c * ∑ i, tt i) ≤
      ENNReal.ofReal a1 + ENNReal.ofReal a2 + ENNReal.ofReal a3 + ENNReal.ofReal (c * ∑ i, mm i) +
        ENNReal.ofReal (c * ∑ i, tt i) := by
    refine ENNReal.ofReal_add_le.trans (add_le_add ?_ le_rfl)
    refine ENNReal.ofReal_add_le.trans (add_le_add ?_ le_rfl)
    exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
  have e1 : ENNReal.ofReal (c * ∑ i, mm i) = ∑ i, ENNReal.ofReal c * ENNReal.ofReal (mm i) := by
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_sum_of_nonneg (fun i _ => hmm i), Finset.mul_sum]
  have e2 : ENNReal.ofReal (c * ∑ i, tt i) = ∑ i, ENNReal.ofReal c * ENNReal.ofReal (tt i) := by
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_sum_of_nonneg (fun i _ => htt i), Finset.mul_sum]
  refine (mul_le_mul' le_rfl h1).trans (le_of_eq ?_)
  rw [e1, e2, mul_add, mul_add, mul_add, mul_add, ENNReal.ofReal_mul hw, ENNReal.ofReal_mul hw,
    Finset.mul_sum, Finset.mul_sum]
  have e3 : ∀ f : ι → ℝ, ∑ i, ENNReal.ofReal w * (ENNReal.ofReal c * ENNReal.ofReal (f i)) =
      ∑ i, ENNReal.ofReal c * (ENNReal.ofReal w * ENNReal.ofReal (f i)) :=
    fun f => Finset.sum_congr rfl fun i _ => by ring
  rw [e3 mm, e3 tt]

end HRS.Commutator.Stj
