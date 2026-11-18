import HRS.MS.Fp81S21Gaussian35Selection
import HRS.MS.Fp81S21Gaussian35SourceAgreement
import HRS.MS.Fp81S21Gaussian35DriftIdentification
import HRS.MS.Fp81S21Gaussian35CovarianceIdentification
import HRS.MS.Fp81S21Gaussian35Chaos
import HRS.MS.Fp81S21Gaussian35Moments
import HRS.MS.Fp81S21Gaussian35MixedExplicit

/-! Packet 35, unit 8: the retained physical package.
The implicit trajectory radius is explicit in the telescope. The plan's fixed
charts and selection witnesses/histories are inherited from Gaussian35Selection.
D and J are definitions, including the required zero extension. Every certificate
refers to these same witnesses. Existence is proved in GaussianPhysicalPackage2. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.S111K2

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

/-- Literal full-horizon drift, extended by zero at negative shifts. -/
def fp81s21_physical35_D (Q : fp81s21_Gaussian35Selection p R) {c K : ℝ}
    (OD : ∀ a : ℝ, 0 ≤ a → r26t6_IntervalOperators Q.E (r26t3_coeff R) p.T a c K)
    (a : ℝ) : Q.src.G0.Ω → Window p :=
  if ha : 0 ≤ a then fp81s21_gaussian_Dcum (OD a ha)
    (add_nonneg ha p.hT.le) (Q.UB a ha) (a + p.T) else 0

/-- Literal full-horizon covariance, retaining the projective tensor type. -/
def fp81s21_physical35_J (Q : fp81s21_Gaussian35Selection p R) {c K : ℝ}
    (OJ : ∀ a : ℝ, 0 ≤ a → r26t6_IntervalOperators Q.E (r26t3_coeff R) p.T a c K)
    (a : ℝ) : Q.src.G0.Ω → projTensor (Window p) 2 :=
  if ha : 0 ≤ a then fp81s21_gaussian_Jcum (OJ a ha)
    (add_nonneg ha p.hT.le) (Q.UG a ha) (a + p.T) else 0

/-- All physical, source, chaos, and moment certificates on one retained source. -/
structure fp81s21_Physical35 (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    extends fp81s21_Gaussian35Selection p R where
  cD : ℝ
  KD : ℝ
  cJ : ℝ
  KJ : ℝ
  MD : ℝ
  MJ : ℝ
  MZ : ℝ
  Cmix : ℝ
  cdec : ℝ
  hcD : 0 < cD
  hKD : 0 ≤ KD
  hcJ : 0 < cJ
  hKJ : 0 ≤ KJ
  hMD : 0 ≤ MD
  hMJ : 0 ≤ MJ
  hMZ : 0 ≤ MZ
  hCmix : 0 ≤ Cmix
  hcdec : 0 < cdec
  OD : ∀ a : ℝ, 0 ≤ a → r26t6_IntervalOperators E (r26t3_coeff R) p.T a cD KD
  OJ : ∀ a : ℝ, 0 ≤ a → r26t6_IntervalOperators E (r26t3_coeff R) p.T a cJ KJ
  source : IsStdGaussianSeq src.G0.P (fp81s21_gaussian_source_measurableXi src) ∧
    (∀ n, Measurable (fp81s21_gaussian_source_measurableXi src n)) ∧
    (∀ n, src.ξ n =ᵐ[src.G0.P] fp81s21_gaussian_source_measurableXi src n)
  supplied_half_wick : ∀ u : ℝ, 0 ≤ u →
    ∃ hL : ‖S.T src.G0 u‖ ≤ S.Kstar,
    ∃ hJoint : ∀ n (v : Fin n → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
      IsCenteredGaussian (src.G0.P.map fun ω => fun i => (S.T src.G0 u (v i)) ω),
      S.W src.G0 u = fp81s21_wickFam_operator R src.G0 (S.T src.G0 u) S.Kstar hL hJoint
  T_oscillator : ∀ u : ℝ, 0 ≤ u → ∀ φ : Euc p.d → ℝ,
    IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
    ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
      (S.T src.G0 u (hφ.toLp φ) : src.G0.Ω → ℝ) =ᵐ[src.G0.P]
        fun ω => OscDual.eval (src.G0.Z u ω) φ
  weighted : let qG := fp81s21_gaussian_embedFamily p Es E (canon.q src.G0)
    let μ := HRS.Whole.withDensityReal R.ρβ
    let kf := fun (f : Euc p.d → ℝ) (xy : Euc p.d × Euc p.d) =>
      commutatorKernel p.d p.s (gradient f) xy.1 xy.2
    ∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ,
      IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f →
      ∃ hf : MemLp f 2 μ, ∃ hk : MemLp (kf f) 2 (μ.prod μ),
        (fun ω => fp81s21_chartAction E (qG u ω) f) =ᵐ[src.G0.P]
          (S.T src.G0 u (hf.toLp f) : src.G0.Ω → ℝ) ∧
        (fun ω => fp81s21_chartAction E (S.qe src.G0 u ω) f) =ᵐ[src.G0.P]
          (S.W src.G0 u (hk.toLp (kf f)) : src.G0.Ω → ℝ)
  DPhysical : ∀ (a : ℝ) (ha : 0 ≤ a),
    let Dcum := fp81s21_gaussian_Dcum (OD a ha) (add_nonneg ha p.hT.le) (UB a ha)
    ∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T →
      (fun ω => Dcum r ω - Dcum v ω) =ᵐ[src.G0.P]
        fun ω => fp81s21_weightedDrift_windowInc ha le_rfl (r26t3_coeff R)
          (fun s f => fp81s21_chartAction E (S.qe src.G0 s ω) f) v r
  DRegularity : ∀ (a : ℝ) (ha : 0 ≤ a),
    let VB := fun ω => fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UB a ha ω)
    let Dcum := fp81s21_gaussian_Dcum (OD a ha) (add_nonneg ha p.hT.le) (UB a ha)
    (∀ r, AEStronglyMeasurable (Dcum r) src.G0.P) ∧
    (∀ ω, ContinuousOn (fun r => Dcum r ω) (Icc 0 (a + p.T)) ∧
      BoundedVariationOn (fun r => Dcum r ω) (Icc 0 (a + p.T))) ∧
    (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T → ∀ ω,
      Dcum r ω - Dcum v ω = (OD a ha).drift v r (VB ω)) ∧
    (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T → ∀ ω,
      eVariationOn (fun s => Dcum s ω) (Icc v r) ≤
        ENNReal.ofReal (KD * ∫ s in Ioc v r, s111k2_age cD a s * ‖VB ω s‖))
  JPhysical : ∀ (a : ℝ) (ha : 0 ≤ a),
    let Jcum := fp81s21_gaussian_Jcum (OJ a ha) (add_nonneg ha p.hT.le) (UG a ha)
    let qG := fp81s21_gaussian_embedFamily p Es E (canon.q src.G0)
    ∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T → ∀ᵐ ω ∂src.G0.P,
      fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
        (fun s f => fp81s21_chartAction E (qG s ω) f) (Ioc v r)
        ((Jcum r ω - Jcum v ω : projTensor (Window p) 2) : TensorDual (Window p) 2)
  JMeasure : ∀ (a : ℝ) (ha : 0 ≤ a),
    let Jcum := fp81s21_gaussian_Jcum (OJ a ha) (add_nonneg ha p.hT.le) (UG a ha)
    let qG := fp81s21_gaussian_embedFamily p Es E (canon.q src.G0)
    ∀ᵐ ω ∂src.G0.P, ∃ I : fp81s21_WindowLocalInput (r26t3_coeff R)
      (wholeSpaceIndex p.d) p.T a (2 * p.d + 8) ((p.d : ℝ) + 2)
      (fun s f => fp81s21_chartAction E (qG s ω) f) Cmix cdec,
      ∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T →
        Jcum r ω - Jcum v ω = fp81s21_window_covariance_measure I v r
  JRegularity : ∀ (a : ℝ) (ha : 0 ≤ a),
    let VG := fun ω => fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UG a ha ω)
    let Jcum := fp81s21_gaussian_Jcum (OJ a ha) (add_nonneg ha p.hT.le) (UG a ha)
    (∀ r, AEStronglyMeasurable (Jcum r) src.G0.P) ∧
    (∀ ω, ContinuousOn (fun r => Jcum r ω) (Icc 0 (a + p.T)) ∧
      BoundedVariationOn (fun r => Jcum r ω) (Icc 0 (a + p.T))) ∧
    (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T → ∀ ω,
      Jcum r ω - Jcum v ω = (OJ a ha).covariance v r (VG ω)) ∧
    (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T → ∀ ω,
      eVariationOn (fun s => Jcum s ω) (Icc v r) ≤ ENNReal.ofReal
        (KJ * |2 * (r26t3_coeff R).ν| * ∫ s in Ioc v r,
          s111k2_age cJ a s ^ 2 * ‖VG ω s‖))
  symmetry : let J := fp81s21_physical35_J tofp81s21_Gaussian35Selection OJ
    ∀ a : ℝ, 0 ≤ a → ∀ ω (M : Window p [×2]→L[ℝ] ℝ),
      (J a ω : TensorDual (Window p) 2) M =
        (J a ω : TensorDual (Window p) 2) (M.domDomCongr (Equiv.swap 0 1))
  chaos : let D := fp81s21_physical35_D tofp81s21_Gaussian35Selection OD
    let J := fp81s21_physical35_J tofp81s21_Gaussian35Selection OJ
    let ξ' := fp81s21_gaussian_source_measurableXi src
    ∀ a : ℝ, 0 ≤ a →
      IsCenteredGaussian (law src.G0.P (r26t3_Zpath src.G0 a)) ∧
      InFirstChaos src.G0.P ξ' 2 (r26t3_Zpath src.G0 a) ∧
      InSecondChaos src.G0.P ξ' 3 (D a) ∧ InFirstChaos src.G0.P ξ' 2 (J a)
  moments : let D := fp81s21_physical35_D tofp81s21_Gaussian35Selection OD
    let J := fp81s21_physical35_J tofp81s21_Gaussian35Selection OJ
    ∀ a : ℝ, 0 ≤ a →
      MemLp (D a) 3 src.G0.P ∧ (∫ ω, ‖D a ω‖ ^ 3 ∂src.G0.P) ≤ MD ∧
      MemLp (J a) 2 src.G0.P ∧ (∫ ω, ‖J a ω‖ ^ 2 ∂src.G0.P) ≤ MJ ∧
      MemLp (r26t3_Zpath src.G0 a) 4 src.G0.P ∧
      (∫ ω, ‖r26t3_Zpath src.G0 a ω‖ ^ 4 ∂src.G0.P) ≤ MZ
  integrabilities : let D := fp81s21_physical35_D tofp81s21_Gaussian35Selection OD
    let J := fp81s21_physical35_J tofp81s21_Gaussian35Selection OJ
    let Z := r26t3_Zpath src.G0
    ∀ a : ℝ, 0 ≤ a →
      Integrable (fun ω => ‖D a ω‖) src.G0.P ∧
      Integrable (fun ω => ‖(J a ω : TensorDual (Window p) 2)‖) src.G0.P ∧
      Integrable (fun ω => ‖D a ω‖ * ‖Z a ω‖ * ‖Z a ω‖) src.G0.P ∧
      Integrable (fun ω => ‖J a ω‖ * ‖Z a ω‖) src.G0.P
  mixed_bound : let D := fp81s21_physical35_D tofp81s21_Gaussian35Selection OD
    let J := fp81s21_physical35_J tofp81s21_Gaussian35Selection OJ
    let Z := r26t3_Zpath src.G0
    ∀ a : ℝ, 0 ≤ a →
      (∫ ω, ‖D a ω‖ * ‖Z a ω‖ * ‖Z a ω‖ ∂src.G0.P) +
        (∫ ω, ‖J a ω‖ * ‖Z a ω‖ ∂src.G0.P) ≤
        MD ^ (1 / 3 : ℝ) * MZ ^ (1 / 2 : ℝ) + MJ ^ (1 / 2 : ℝ) * MZ ^ (1 / 4 : ℝ)

#print axioms fp81s21_physical35_D
#print axioms fp81s21_physical35_J
#print axioms fp81s21_Physical35
end HRS.Fp81.S21
end
