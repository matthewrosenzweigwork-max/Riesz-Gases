import HRS.MS.Fp81S21GaussianWickInput
import HRS.MS.Fp81S21GaussianO1Moments
import HRS.MS.Fp81S21GaussianPhysicalPackage2
import HRS.MS.Fp81S21GaussLaw2

/-! GaussianAt and O1 on the retained physical source. The proposed WickAll
shorthand is expanded into a definition; p, δ and R are implicit binders.
Existing probability instances are installed locally, without new hypotheses.
The bound is chosen before the start. The public existence theorem intersects
response, Wick and physical-existence radii; law identification needs no radius. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E
variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
attribute [local instance] fp81s21_initialMeasure_isProbability

/-- The exact all-start, all-test Wick certificate on the retained source. -/
def fp81s21_WickAll (Q : fp81s21_Physical35 p R) : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∀ (τ : Fin 3 → Icc (0 : ℝ) p.T)
    (φ : Fin 3 → Euc p.d → ℝ) (χ : Fin 3 → ℝ → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)),
  S21eChiClause p.d p.s p.a p.β p.γ R.ρ p.T a τ φ χ →
  fp81s21_WickInput (d := p.d) (s := p.s) (a := p.a) (β := p.β)
    (β₀ := p.γ) (T := p.T) (a₀ := a) (ρ := R.ρ) Q.src.G0.P
    (initialKappa R a) (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a)
    (r26t3_Zpath Q.src.G0 a)
    (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
      TensorDual (Window p) 2)) τ φ χ hφ

/-- Assemble every GaussianAt field from the same physical selection. -/
def fp81s21_gaussianAt_of_physical35 (Q : fp81s21_Physical35 p R)
    (Kresponse : ℝ) (hresp : fp81s21_Response9 R Kresponse)
    (hwick : fp81s21_WickAll Q) (a : ℝ) (ha : 0 ≤ a) :
    fp81s21_GaussianAt p.d p.s p.a p.β p.γ p.T R.ρ a := by
  letI := fp81s21_initialMeasure_isProbability p R
  have hm := Q.moments a ha
  refine {
    Ω := Q.src.G0.Ω
    mΩ := Q.src.G0.mΩ
    P := Q.src.G0.P
    hP := Q.src.G0.prob
    process := Q.src.G0.Z
    evolution := Q.src.G0.evolution
    window := r26t3_Zpath Q.src.G0 a
    window_eq := fun _ => rfl
    window_meas := hm.2.2.2.2.1.aestronglyMeasurable.aemeasurable
    law_identification := ?_
    κ₀ := initialKappa R a
    κ₀_mem := (hresp.1 a ha).2.2.2.1
    κ₀_symm := hresp.2 a ha
    D := fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a
    Zpath := r26t3_Zpath Q.src.G0 a
    J := fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
      TensorDual (Window p) 2)
    Zpath_eq := rfl
    D_meas := hm.1.aestronglyMeasurable
    Z_meas := hm.2.2.2.2.1.aestronglyMeasurable
    J_meas := continuous_subtype_val.comp_aestronglyMeasurable
      hm.2.2.1.aestronglyMeasurable
    DZZ_integrable := (Q.integrabilities a ha).2.2.1
    JZ_integrable := (Q.integrabilities a ha).2.2.2
    J_projective := ae_of_all _ (fun ω =>
      (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω).property)
    J_symmetric := ?_
    wick := hwick a ha }
  · intro Ω' mΩ' P' hP' Z hZ
    let G : GaussianRealization R :=
      { Ω := Ω', mΩ := mΩ', P := P', prob := hP', Z := Z, evolution := hZ }
    exact fp81s21_gaussian_window_law_eq p R Q.src.G0 G a ha
  · apply ae_of_all
    intro ω x y
    have hswap : (HRS.MC.E213U18.mk2 x y).domDomCongr (Equiv.swap 0 1) =
        HRS.MC.E213U18.mk2 y x := by
      ext v
      simp only [ContinuousMultilinearMap.domDomCongr_apply, HRS.MC.E213U18.mk2_apply]
      change x (v ((Equiv.swap (0 : Fin 2) 1) 0)) *
        y (v ((Equiv.swap (0 : Fin 2) 1) 1)) = y (v 0) * x (v 1)
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
      exact mul_comm _ _
    simpa only [hswap] using Q.symmetry a ha ω (HRS.MC.E213U18.mk2 x y)

/-- The literal unit-9 bound packages O1, uniformly before every start. -/
def fp81s21_gaussianO1_of_physical35 (Q : fp81s21_Physical35 p R)
    (Kresponse : ℝ) (hresp : fp81s21_Response9 R Kresponse)
    (hwick : fp81s21_WickAll Q)
    (hbound : ∀ a : ℝ, 0 ≤ a →
      ‖initialKappa R a‖ + 3 * fp81s21_ID Q a + 3 * fp81s21_IJ Q a ≤
        Kresponse ^ 3 + 3 * (Q.MD ^ (1 / 3 : ℝ) * Q.MZ ^ (1 / 2 : ℝ) +
          Q.MJ ^ (1 / 2 : ℝ) * Q.MZ ^ (1 / 4 : ℝ))) :
    fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ where
  Kb := Kresponse ^ 3 + 3 * (Q.MD ^ (1 / 3 : ℝ) * Q.MZ ^ (1 / 2 : ℝ) +
    Q.MJ ^ (1 / 2 : ℝ) * Q.MZ ^ (1 / 4 : ℝ))
  data := fp81s21_gaussianAt_of_physical35 Q Kresponse hresp hwick
  moment_bound := hbound

/-- O1's projective tensor is the physical cubic correction, with literal D/J/Z. -/
theorem fp81s21_gaussianO1_kappa_eq (Q : fp81s21_Physical35 p R)
    (Kresponse : ℝ) (hresp : fp81s21_Response9 R Kresponse)
    (hwick : fp81s21_WickAll Q)
    (hbound : ∀ a : ℝ, 0 ≤ a →
      ‖initialKappa R a‖ + 3 * fp81s21_ID Q a + 3 * fp81s21_IJ Q a ≤
        Kresponse ^ 3 + 3 * (Q.MD ^ (1 / 3 : ℝ) * Q.MZ ^ (1 / 2 : ℝ) +
          Q.MJ ^ (1 / 2 : ℝ) * Q.MZ ^ (1 / 4 : ℝ)))
    (a : ℝ) (ha : 0 ≤ a) :
    (fp81s21_O1_kappa (fp81s21_gaussianO1_of_physical35 Q Kresponse hresp hwick hbound) a :
      TensorDual (Window p) 3) =
    s21eKappa Q.src.G0.P (initialKappa R a)
      (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a)
      (r26t3_Zpath Q.src.G0 a)
      (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
        TensorDual (Window p) 2)) :=
  fp81s21_O1_kappa_eq _ a ha

/-- A common radius supplies the complete O1 record, including existence of Q. -/
theorem fp81s21_gaussianO1_package (p : Parameters) :
    fp81s21_Rad p (fun _ R =>
      Nonempty (fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)) := by
  obtain ⟨δR, hR, hhalf, hresponse⟩ := fp81s21_gaussian35_O1_moment_bound p
  obtain ⟨δW, hW, _, hwick⟩ := fp81s21_gaussian_wick_input p
  obtain ⟨δP, hP, _, hphysical⟩ := fp81s21_gaussian_physical_package p
  refine ⟨min δR (min δW δP), lt_min hR (lt_min hW hP),
    (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R
  have hl : δ ≤ δR ∧ δ ≤ δW ∧ δ ≤ δP := by
    simpa only [le_min_iff] using hδle
  obtain ⟨K, _, hresp, hbound⟩ := hresponse δ hδ hl.1 R
  obtain ⟨Q⟩ := hphysical δ hδ hl.2.2 R
  exact ⟨fp81s21_gaussianO1_of_physical35 Q K hresp
    (hwick δ hδ hl.2.1 R Q) (hbound Q)⟩

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_gaussianAt_of_physical35
#print axioms HRS.Fp81.S21.fp81s21_gaussianO1_of_physical35
#print axioms HRS.Fp81.S21.fp81s21_gaussianO1_kappa_eq
#print axioms HRS.Fp81.S21.fp81s21_gaussianO1_package
