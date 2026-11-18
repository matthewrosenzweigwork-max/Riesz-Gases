import HRS.MS.S113X2A1f

/-!
# S11.3 X2 part A1g: time-independent test functions and integrals against the killed law
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

/-- The spatial generator `β⁻¹ Δ φ + Dφ[b]` of a time-independent test function. -/
def s113a_genx (d : ℕ) (s q β : ℝ) (N : ℕ) (phi : EucConfig d N → ℝ) (x : EucConfig d N) : ℝ :=
  β⁻¹ * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ phi) x (HRS.configBasis d N k) (HRS.configBasis d N k) +
    fderiv ℝ phi x (fun i => particleDriftW (quadraticGradientDyn d s q β) x i)

theorem s113a_gen_timeindep (s q β : ℝ) {phi : EucConfig d N → ℝ} (hphi : ContDiff ℝ 2 phi) (r : ℝ)
    (x : EucConfig d N) :
    s113a_gen d s q β N (fun p => phi p.2) (r, x) = s113a_genx d s q β N phi x := by
  have hPhi : ContDiff ℝ 2 (fun p : ℝ × EucConfig d N => phi p.2) := hphi.comp contDiff_snd
  have hd : Differentiable ℝ (fun p : ℝ × EucConfig d N => phi p.2) := hPhi.differentiable (by norm_num)
  have h1 : ∀ v, fderiv ℝ phi x v = fderiv ℝ (fun p : ℝ × EucConfig d N => phi p.2) (r, x) (0, v) := by
    intro v
    exact s113a_slice_fderiv (fun p : ℝ × EucConfig d N => phi p.2) hd r x v
  have h2 : ∀ v w, fderiv ℝ (fderiv ℝ phi) x v w =
      fderiv ℝ (fderiv ℝ (fun p : ℝ × EucConfig d N => phi p.2)) (r, x) (0, v) (0, w) := by
    intro v w
    exact s113a_slice_fderiv2 (fun p : ℝ × EucConfig d N => phi p.2) hPhi r x v w
  have h3 : fderiv ℝ (fun p : ℝ × EucConfig d N => phi p.2) (r, x) (1, 0) = 0 := by
    have this : HasFDerivAt (fun p : ℝ × EucConfig d N => phi p.2)
        ((fderiv ℝ phi x).comp (ContinuousLinearMap.snd ℝ ℝ (EucConfig d N))) (r, x) :=
      ((hphi.differentiable (by norm_num)) x).hasFDerivAt.comp (r, x)
        (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := EucConfig d N) (p := (r, x)))
    rw [this.fderiv]
    simp
  unfold s113a_gen HRS.MC.CepP3.Lop s113a_genx s113a_drift
  rw [h3, zero_add]
  simp only [h1, h2]

open Classical in
/-- Integrals against the killed law at a fixed time, through the exit time. -/
theorem s113a_killedLaw_integral {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → EucConfig d N) (X : ℝ≥0 → Ω → EucConfig d N) (hX0 : Measurable (X 0))
    (hinit : ∀ᵐ ζ ∂P, X 0 ζ = X₀ ζ) (D : Set (EucConfig d N)) (chi : EucConfig d N → ℝ)
    (hchi : Measurable chi) (hchi0 : ∀ z, 0 ≤ chi z) (t : ℝ≥0) (hXt : Measurable (X t))
    (τ : Ω → WithTop ℝ) (hτt : MeasurableSet {ζ | ((t : ℝ) : WithTop ℝ) < τ ζ})
    (hsurv : ∀ᵐ ζ ∂P, ζ ∈ s113a_survives D X t ↔ ((t : ℝ) : WithTop ℝ) < τ ζ)
    (g : EucConfig d N → ℝ) (hg : Measurable g) :
    ∫ x, g x ∂(s113a_killedLaw P D X₀ X chi t) =
      ∫ ζ, (if ((t : ℝ) : WithTop ℝ) < τ ζ then chi (X 0 ζ) * g (X t ζ) else 0) ∂P := by
  set w' : Ω → ℝ≥0∞ := fun ζ => if ((t : ℝ) : WithTop ℝ) < τ ζ then ENNReal.ofReal (chi (X 0 ζ)) else 0
    with hw'
  have hw'm : Measurable w' :=
    Measurable.ite hτt (ENNReal.measurable_ofReal.comp (hchi.comp hX0)) measurable_const
  have hwr : (fun ζ => if ζ ∈ s113a_survives D X t then ENNReal.ofReal (chi (X₀ ζ)) else 0)
      =ᵐ[P] w' := by
    filter_upwards [hsurv, hinit] with ζ h1 h2
    simp only [hw', h2]
    by_cases hs : ζ ∈ s113a_survives D X t
    · rw [if_pos hs, if_pos (h1.1 hs)]
    · rw [if_neg hs, if_neg (fun h => hs (h1.2 h))]
  unfold s113a_killedLaw
  rw [withDensity_congr_ae hwr, integral_map hXt.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hw'm (ae_of_all _ fun ζ => (by
      simp only [hw']; split_ifs <;> simp))]
  refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
  simp only [hw']
  split_ifs
  · rw [ENNReal.toReal_ofReal (hchi0 _), smul_eq_mul]
  · simp

end HRS.MS.S113X2

end
