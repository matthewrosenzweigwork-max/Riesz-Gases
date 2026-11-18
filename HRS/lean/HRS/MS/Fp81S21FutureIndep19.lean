import HRS.MS.Fp81S21FutureIndep17
import HRS.MS.Fp81S21RawGauss2
import HRS.MS.LimFieldAux1

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.GenPath HRS.MS.R2Interp HRS.MS.U10 HRS.MS.R26T3 HRS.MS.ProClosureS111

/-- A continuous feature curve extends an almost-sure dense-time coordinate
identity to each time.  The exceptional set may depend on the time. -/
theorem fp81s21_source_coordinate_at_every_time
    {d : ℕ} {m H : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hParseval : ∀ h h' : GaussianFeatureHilbert,
      HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h') (inner ℝ h h'))
    (hstd : HRS.IsStdGaussianSeq P ξ)
    (hW2 : ∀ h, MemLp (W h) 2 P)
    (hWlim : ∀ h, Tendsto (fun n : ℕ =>
      ∫ ω, (s21g2_s11a_S ξ (fun k => inner ℝ (e k) h) n ω - W h ω) ^ 2 ∂P)
        atTop (𝓝 0))
    (X : Ω → OscPath d m H) (hXm : Measurable X)
    (s : ℕ → Icc (0 : ℝ) H) (hs : DenseRange s)
    (F : Icc (0 : ℝ) H → GaussianFeatureHilbert) (hF : Continuous F)
    (α : MultiIndex d)
    (hcoord : ∀ n, (fun ω => OscDual.coord (OscPath.at' (X ω) (s n)) α)
      =ᵐ[P] W (F (s n)))
    (t : Icc (0 : ℝ) H) :
    (fun ω => OscDual.coord (OscPath.at' (X ω) t) α) =ᵐ[P] W (F t) := by
  have ht : t ∈ closure (Set.range s) := by rw [hs.closure_eq]; trivial
  obtain ⟨q, hq, hqt⟩ := mem_closure_iff_seq_limit.1 ht
  choose k hk using hq
  have hkq : ∀ n, s (k n) = q n := fun n => hk n
  have hst : Tendsto (fun n => s (k n)) atTop (𝓝 t) := by simpa only [hkq] using hqt
  let U : ℕ → Ω → ℝ := fun n ω => OscDual.coord (OscPath.at' (X ω) (s (k n))) α
  let V : Ω → ℝ := fun ω => OscDual.coord (OscPath.at' (X ω) t) α
  have hUm : ∀ n, AEStronglyMeasurable (U n) P := by
    intro n
    exact ((s102_ell (s (k n)) α).continuous.measurable.comp hXm).aestronglyMeasurable
  have hpoint : ∀ᵐ ω ∂P, Tendsto (fun n => U n ω) atTop (𝓝 (V ω)) := by
    apply Filter.Eventually.of_forall
    intro ω
    have hc : Continuous (fun u : Icc (0 : ℝ) H =>
        OscDual.coord (OscPath.at' (X ω) u) α) :=
      (s102_coordCLM α).continuous.comp (X ω).continuous
    exact hc.continuousAt.tendsto.comp hst
  have hleft : TendstoInMeasure P U atTop V := tendstoInMeasure_of_tendsto_ae hUm hpoint
  let Z : ℕ → Ω → ℝ := fun n => W (F (s (k n)))
  have hdist : Tendsto (fun n => ∫ ω, (Z n ω - W (F t) ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have hFt : Tendsto (fun n => F (s (k n))) atTop (𝓝 (F t)) :=
      hF.continuousAt.tendsto.comp hst
    have hnorm := (tendsto_iff_norm_sub_tendsto_zero).1 hFt
    have hsq : Tendsto (fun n => ‖F (s (k n)) - F t‖ ^ 2) atTop (𝓝 0) := by
      simpa using hnorm.pow 2
    apply hsq.congr
    intro n
    exact (fp81s21_series_distance e ξ W hParseval hstd hW2 hWlim _ _).symm
  have hL2 : HRS.TendstoL2 P Z (W (F t)) :=
    HRS.tendstoL2_of_memLp (hW2 _) (fun n => hW2 _) hdist
  have hright : TendstoInMeasure P Z atTop (W (F t)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (hL2.tendsto_eLpNorm (fun n => (hW2 _).aestronglyMeasurable))
  have hright' : TendstoInMeasure P U atTop (W (F t)) := by
    apply hright.congr
    · intro n
      exact (hcoord (k n)).symm
    · exact Filter.Eventually.of_forall fun _ => rfl
  exact tendstoInMeasure_ae_unique hleft hright'

#print axioms fp81s21_source_coordinate_at_every_time
end HRS.Fp81.S21
end
