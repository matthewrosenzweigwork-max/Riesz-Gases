import HRS.MS.PROS15dFiniteScalarE24
import HRS.MS.S21T4ProdF
import HRS.MS.PROS15dTiltTransfer

/-!
# S15d: exact finite physical first-chaos laws under a normalized Gaussian tilt

Finite linear combinations are formed as *spatial functions*, then evaluated
by the original physical ProductGaussian field. First-chaos linearity and
absolute continuity identify their tilted laws with Gaussian spectral sums.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_finite_span_tilted_gaussian
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (W : I.Ω → ℝ)
    (hW : AEMeasurable W I.P)
    (hExp : Integrable (fun ω => Real.exp (-W ω)) I.P)
    (e : ℕ → HRS.Euc d → ℝ)
    (he : ∀ j, MemLp (e j) 2 μ)
    (n : ℕ) (v : Fin n → ℝ≥0)
    (hLaw : (r26t3_tilt I.P W).map
      (fun ω (j : Fin n) => I.η (e j) ω) =
      Measure.pi (fun j : Fin n => gaussianReal 0 (v j)))
    (a : Fin n → ℝ) :
    HRS.IsCenteredGaussian
      ((r26t3_tilt I.P W).map
        (I.η (fun x => ∑ j : Fin n, a j * e j x))) := by
  classical
  letI := I.mΩ
  letI := I.prob
  let Pt := r26t3_tilt I.P W
  letI : IsProbabilityMeasure Pt :=
    r26t3_tilt_isProb I.P hW hExp
  have hAC : Pt ≪ I.P := by
    unfold Pt r26t3_tilt
    intro s hs
    simp [withDensity_absolutelyContinuous I.P _ hs]
  have hfinite :
      I.η (fun x => ∑ j : Fin n, a j * e j x) =ᵐ[I.P]
        fun ω => ∑ j : Fin n, a j * I.η (e j) ω := by
    simpa only [] using
      s21l_eta_sum (s21t4_product_eta_bundle I)
        Finset.univ a (fun j : Fin n => e j)
        (fun j _ => he j)
  have hfinitePt :
      I.η (fun x => ∑ j : Fin n, a j * e j x) =ᵐ[Pt]
        fun ω => ∑ j : Fin n, a j * I.η (e j) ω :=
    hAC hfinite
  have hXm : ∀ j : Fin n, AEMeasurable (I.η (e j)) Pt :=
    fun j => (I.meas (e j) (he j)).aemeasurable.mono_ac hAC
  have hGaussian :
      HRS.IsCenteredGaussian
        (Pt.map (fun ω => ∑ j : Fin n, a j * I.η (e j) ω)) :=
    s15d_finite_scalar_linear_gaussian
      (fun j : Fin n => I.η (e j)) hXm v hLaw a
  rw [Measure.map_congr hfinitePt]
  exact hGaussian

#print axioms s15d_physical_finite_span_tilted_gaussian
end HRS.MS.R26T3
