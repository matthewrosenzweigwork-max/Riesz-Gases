import HRS.MS.S21F_C09

/-!
# S21F, packet R26-T3.S02a: the canonical response representative agrees with `responseInverse` a.e.

`ResponseForm` at `θ = γ ≥ 0` for the ACTUAL initial reference (`s111x2_krep_of_tcref` at the `TcRef` datum of `r26t3_reference_data`;
`γ = 0` included) gives `h + γ K h = P f` a.e. for `h = responseInverse`, hence `responseRepW = P f - γ K h = h` a.e.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

theorem s21f_responseForm_init {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) :
    ∃ η : ℝ, HRS.MS.S111X2.ResponseForm (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ η := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  have hd := p.hd
  have hsd : p.s < (p.d : ℝ) := by
    have := p.hs
    have : (0 : ℝ) < p.d := by exact_mod_cast (by omega : 0 < p.d)
    linarith
  have hP : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hP' : IsProbabilityMeasure (r26t3_mu R 0) := hP
  obtain ⟨Mg, K, hK⟩ := HRS.MS.S111X2.s111x2_krep_of_tcref (by omega) p.hs0 hsd hc hTc
  exact ⟨_, HRS.MS.S111X2.s111x2_responseForm hK p.hγ le_rfl⟩

theorem r26t3_response_ae {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (f : Euc p.d → ℝ) (hf : MemLp f 2 (r26t3_mu R 0)) :
    r26t3_a R f =ᵐ[r26t3_mu R 0]
      HRS.Whole.responseInverse (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ f := by
  obtain ⟨η, hform⟩ := s21f_responseForm_init hδ hδh R
  obtain ⟨-, hae⟩ := hform.solution f hf
  filter_upwards [hae] with x hx
  show HRS.Whole.projMean (r26t3_mu R 0) f x - p.γ *
    HRS.Whole.Kop (rieszKernel p.d p.s) (r26t3_mu R 0)
      (HRS.Whole.responseInverse (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ f) x = _
  linarith

end HRS.MS.R26T3
