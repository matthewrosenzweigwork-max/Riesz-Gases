import HRS.MC.CepH2Ent2

/-!
# CEPH2, lower semicontinuity of the cylinder entropy under mollification
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_liminf_sub_const (a : ℕ → ℝ≥0∞) (c : ℝ) :
    (((liminf a atTop : ℝ≥0∞) : EReal)) - (c : EReal) = liminf (fun n => (a n : EReal) - (c : EReal)) atTop := by
  have e : (fun x : ℝ≥0∞ => (x : EReal) - (c : EReal)) = fun x : ℝ≥0∞ => (x : EReal) + ((-c : ℝ) : EReal) := by
    funext x; rw [sub_eq_add_neg, EReal.coe_neg]
  have hmono : Monotone (fun x : ℝ≥0∞ => (x : EReal) - (c : EReal)) := by
    rw [e]; intro x y hxy
    exact add_le_add_left (EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy) _
  have hcont : Continuous (fun x : ℝ≥0∞ => (x : EReal) - (c : EReal)) := by
    rw [e]
    refine continuous_iff_continuousAt.2 fun x => ?_
    have hadd := EReal.continuousAt_add (p := ((x : EReal), ((-c : ℝ) : EReal))) (Or.inr (EReal.coe_ne_bot _))
      (Or.inr (EReal.coe_ne_top _))
    have hf : ContinuousAt (fun y : ℝ≥0∞ => ((y : EReal), ((-c : ℝ) : EReal))) x :=
      continuous_coe_ennreal_ereal.continuousAt.prodMk continuousAt_const
    exact ContinuousAt.comp (g := fun p : EReal × EReal => p.1 + p.2)
      (f := fun y : ℝ≥0∞ => ((y : EReal), ((-c : ℝ) : EReal))) hadd hf
  exact hmono.map_liminf_of_continuousAt a hcont.continuousAt

/-- **C5 (a)**: lower semicontinuity of the cylinder entropy along the Gaussian mollification. -/
theorem cepH2_entropy_lsc {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {θ : ℝ} (hθ : 0 < θ) {μ : Measure (Ch N)} [IsProbabilityMeasure μ] (hcell : μ (cep_cell N)ᶜ = 0)
    (hmom : ∫⁻ z, ENNReal.ofReal (‖h2_perp z‖ ^ 2) ∂μ < ⊤) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    cep_cylEntropy θ U μ ≤ liminf (fun n => ((h2_free θ U (h2_mol θ (ε n) μ) : ℝ) : EReal)) atTop := by
  have hUc : Continuous U := hU.continuous
  have hmom' : Integrable (fun y => ‖h2_perp y‖ ^ 2) μ :=
    ⟨(h2_continuous_perp.norm.pow 2).aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)]; exact hmom⟩
  set v : ℕ → ℝ := fun n => 2 * θ * ε n with hv
  have hvpos : ∀ n, 0 < v n := fun n => by have := hε n; simp only [hv]; positivity
  have hv0 : Tendsto v atTop (𝓝 0) := by
    have := hε0.const_mul (2 * θ)
    simpa [hv, mul_assoc] using this
  haveI := h2_cylRef_prob hUc hconf hθ
  haveI : ∀ n, IsProbabilityMeasure (h2_molMeas (v n) μ) := fun n => h2_molMeas_prob (hvpos n) μ
  set ref := cep_cylRef θ U with href
  set Lz : ℝ := Real.log (cep_cylPartition θ U).toReal with hLz
  -- the entropy of the mollified density
  have hkey : ∀ n, ((h2_free θ U (h2_mol θ (ε n) μ) : ℝ) : EReal) = ((klDiv (h2_molMeas (v n) μ) ref : ℝ≥0∞) : EReal) - (Lz : EReal) := by
    intro n
    have hρ0 : ∀ x, 0 ≤ h2_mu (v n) μ x := fun x => (h2_mu_pos (hvpos n) μ x).le
    obtain ⟨hne, hval⟩ := h2_klDiv_density hUc hconf hθ (h2_continuous_mu (hvpos n) μ).measurable hρ0
      (h2_lintegral_cell_mu_one (hvpos n) μ)
      (h2_integrable_Phi_single hθ (hvpos n) hU hUper hK μ hcell hmom')
    have hne' : klDiv (h2_molMeas (v n) μ) ref ≠ ⊤ := hne
    have hval' : (klDiv (h2_molMeas (v n) μ) ref).toReal = _ := hval
    rw [← EReal.coe_ennreal_toReal hne', hval', ← EReal.coe_sub, h2_mol_eq]
    congr 1
    unfold h2_free
    ring
  simp_rw [hkey]
  rw [← h2_liminf_sub_const (fun n => klDiv (h2_molMeas (v n) μ) ref) Lz]
  unfold cep_cylEntropy relEntropy
  have hle : klDiv μ ref ≤ liminf (fun n => klDiv (h2_molMeas (v n) μ) ref) atTop :=
    h2_klDiv_liminf_cell hcell (h2_cylRef_compl hUc θ) (fun n => h2_molMeas_compl (hvpos n) μ)
      (fun ψ hψ hper hb => by
        obtain ⟨C, hC⟩ := hb
        exact h2_molMeas_tendsto μ hvpos hv0 hψ hper hC)
  have hmono : Monotone (fun x : ℝ≥0∞ => (x : EReal) - (Lz : EReal)) := fun x y hxy => by
    show (x : EReal) - (Lz : EReal) ≤ (y : EReal) - (Lz : EReal)
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add_left (EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy) _
  exact hmono hle

end HRS.MC.CepH2
