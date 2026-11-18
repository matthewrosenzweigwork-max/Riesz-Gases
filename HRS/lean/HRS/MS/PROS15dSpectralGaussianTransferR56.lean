import HRS.MS.PROS15dPhysicalLinearSpectral
import HRS.MS.PROS15dGaussianLimitB18

/-!
# S15d: Gaussianity of L² limits of physical finite spectral observables

The approximation hypothesis is explicit. This theorem concerns the
genuine physical Hilbert--Schmidt tilt on the original ProductGaussian
space; it does not assert that arbitrary physical tests admit the required
spectral approximation, nor identify the physical Wick quadratic.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_riesz_finite_spectral_L2_gaussian
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (I : ProductGaussian (r26t3_mu R 0))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ (lam : ℕ → ℝ) (e : ℕ → HRS.Euc p.d → ℝ) (Q : I.Ω → ℝ),
      (∀ j, 0 ≤ lam j ∧ HRS.Whole.MemL2Zero (r26t3_mu R 0) (e j)) ∧
      Summable (fun j => lam j ^ 2) ∧
      HRS.TendstoL2 I.P (fun n ω =>
        (1 / 2 : ℝ) * ∑ j ∈ Finset.range n,
          lam j * (I.η (e j) ω ^ 2 - 1)) Q ∧
      Integrable (fun ω => Real.exp (-γ * Q ω)) I.P ∧
      ∀ (m : ℕ)
        (A : (n : ℕ) → ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))
        (Y : I.Ω → (Fin m → ℝ)),
        Tendsto (fun n => eLpNorm
          (fun ω => A n (fun i : Fin n => I.η (e i) ω) - Y ω)
          2 (r26t3_tilt I.P (fun ω => γ * Q ω))) atTop (𝓝 0) →
        HRS.IsCenteredGaussian
          ((r26t3_tilt I.P (fun ω => γ * Q ω)).map Y) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_mu_prob hδ hδh R
  letI := I.mΩ
  letI := I.prob
  obtain ⟨lam, e, Q, he, hs, hQ, hInt, hGauss⟩ :=
    s15d_physical_riesz_linear_spectral_gaussian hδ hδh R I γ hγ
  let Pt := r26t3_tilt I.P (fun ω => γ * Q ω)
  have hV : AEMeasurable (fun ω => γ * Q ω) I.P :=
    (hQ.1.const_mul γ).aemeasurable
  have hIntPrime : Integrable (fun ω => Real.exp (-(γ * Q ω))) I.P := by
    simpa only [neg_mul] using hInt
  letI : IsProbabilityMeasure Pt :=
    r26t3_tilt_isProb I.P hV hIntPrime
  have hAC : Pt ≪ I.P := by
    unfold Pt r26t3_tilt
    intro s hs0
    simp [withDensity_absolutelyContinuous I.P _ hs0]
  refine ⟨lam, e, Q, he, hs, hQ, hInt, ?_⟩
  intro m A Y hL2
  let X : ℕ → I.Ω → (Fin m → ℝ) := fun n ω =>
    A n (fun i : Fin n => I.η (e i) ω)
  have hXm : ∀ n, AEStronglyMeasurable (X n) Pt := by
    intro n
    have hCoords : AEMeasurable (fun ω (i : Fin n) => I.η (e i) ω) Pt :=
      AEMeasurable.of_eval (fun i =>
        (I.meas (e i) (he i).2.1).aemeasurable.mono_ac hAC)
    exact ((A n).continuous.measurable.comp_aemeasurable hCoords).aestronglyMeasurable
  have hXGauss : ∀ n, HRS.IsCenteredGaussian (Pt.map (X n)) := by
    intro n
    simpa only [X, Pt] using hGauss n m (A n)
  have hDiff : ∀ n, (X n - Y) = (fun ω => X n ω - Y ω) := by
    intro n
    funext ω
    rfl
  have hL2' : Tendsto (fun n => eLpNorm (X n - Y) 2 Pt) atTop (𝓝 0) := by
    simp only [hDiff]
    exact hL2
  exact s15d_centered_gaussian_L2_limit Pt X Y hXm hXGauss hL2'

#print axioms s15d_physical_riesz_finite_spectral_L2_gaussian
end HRS.MS.R26T3
