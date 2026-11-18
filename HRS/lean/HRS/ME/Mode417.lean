import HRS.MD.DOMFinal
import HRS.MD.DOMMeas
import HRS.Equilibrium.NormalFormProof
import HRS.Equilibrium.Parametrix.Assembly
import HRS.Equilibrium.Q84dStationary
import HRS.Equilibrium.Q84eAuxM
import HRS.Equilibrium.LocalDivTorus
import HRS.Equilibrium.QuadraticVariance
import HRS.Stochastic.LyonsZhengSpec
import HRS.Equilibrium.Q84dAuxA
import HRS.Equilibrium.Q84dAuxD
import HRS.Equilibrium.Q84dAuxF
import HRS.Equilibrium.Q84dAuxK
import HRS.Equilibrium.Q84dAuxX
import HRS.Equilibrium.Q84aAuxA
import HRS.Kernel.GradBasic

/-!
# Packet M8 (row 4.17): proof of the mode package `mode_package`

Proof of `mode_package` of `HRS/ME/Spec417Mode.lean` (statement copied verbatim as `mode_package_proof`;
`HRS/ME/Spec417Mode.lean` is not imported).  Helpers carry the prefix `m417_`.

Witnesses: `F = centeredUnder μ (Fstat ψ)`; `G = 𝟙_{collision-free} · particleGen (Fstat ψ)`, which is strictly
measurable by `domp_measurable_particleGen`; `E = (√N/2) centeredUnder μ (quadStat h_f) + G`.  The identity of
conjunct 6 then holds by `ring`; off collisions `E` equals the centred error statistic of `normal_form_proof`,
which gives the `L²` bounds (`eLpNorm` is insensitive to the `μ`-null collision set).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-! ### Generic helpers -/

theorem m417_sq_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} (g : α → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hg : AEStronglyMeasurable g μ) (h : eLpNorm g 2 μ ≤ ENNReal.ofReal b) :
    ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ ≤ ENNReal.ofReal (b ^ 2) := by
  have key := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := 2) (by norm_num) hg
  have e : ∀ x, ENNReal.ofReal (g x ^ 2) = ‖g x‖ₑ ^ ((2 : ℝ≥0) : ℝ) := by
    intro x
    rw [NNReal.coe_ofNat, ENNReal.rpow_two, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      sq_abs]
  rw [lintegral_congr e, ← key]
  calc eLpNorm g 2 μ ^ ((2 : ℝ≥0) : ℝ) ≤ (ENNReal.ofReal b) ^ ((2 : ℝ≥0) : ℝ) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal (b ^ 2) := by
        rw [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.ofReal_pow hb]

theorem m417_sq_of_half {x : ℝ≥0∞} {b : ℝ} (hb : 0 ≤ b) (h : x ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal b) :
    x ≤ ENNReal.ofReal (b ^ 2) := by
  have h1 : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
    rw [← ENNReal.rpow_mul]; norm_num
  calc x = (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := h1.symm
    _ ≤ (ENNReal.ofReal b) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (b ^ 2) := by rw [ENNReal.rpow_two, ENNReal.ofReal_pow hb]

theorem m417_rpow_sq (N : ℕ) (hN : 0 < (N : ℝ)) : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  have h2 : -(1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = -1 := by norm_num
  rw [h2, Real.rpow_neg_one, one_div]

/-! ### Topology of the collision-free set -/

theorem m417_isOpen_compl_collision (N : ℕ) : IsOpen (collisionSet d N)ᶜ :=
  (isClosed_collisionSet d N).isOpen_compl

theorem m417_isOpen_coverFree (N : ℕ) : IsOpen (coverFree d N) :=
  (isClosed_collisionSet d N).isOpen_compl.preimage
    (continuous_pi fun i => Q84a.q84a_continuous_mk.comp (continuous_apply i))

theorem m417_rep_mem {N : ℕ} (X : Config d N) (hX : X ∉ collisionSet d N) :
    (fun k => Torus.rep (X k)) ∈ coverFree d N := by
  have e : (fun i => (Torus.mk ((fun k => Torus.rep (X k)) i) : Torus d)) = X :=
    funext fun i => Torus.mk_rep (X i)
  show (fun i => (Torus.mk (Torus.rep (X i)) : Torus d)) ∉ collisionSet d N
  rw [show (fun i => (Torus.mk (Torus.rep (X i)) : Torus d)) = X from e]
  exact hX

/-! ### Regularity of `Fstat` on the covering space -/

theorem m417_contDiffOn_Fstat {N : ℕ} (ψ : Torus d → Torus d → ℝ)
    (hψ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => Fstat (N := N) ψ) 0) (coverFree d N) := by
  have hfun : configLift (fun _ => Fstat (N := N) ψ) 0 = fun Y : Fin N → Euc d =>
      (N : ℝ) ^ (-(3 / 2 : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, lift2 ψ (Y i, Y j) := by
    funext Y
    simp only [configLift, Fstat, pairSumOrdered, lift2, Finset.mul_sum]
  rw [hfun]
  refine ContDiffOn.mul contDiffOn_const ?_
  refine ContDiffOn.sum fun i _ => ?_
  refine ContDiffOn.sum fun j hj => ?_
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  have hmap : Set.MapsTo (fun Y : Fin N → Euc d => (Y i, Y j)) (coverFree d N) (offDiag d) := by
    intro Y hY
    show Torus.mk (Y i) ≠ Torus.mk (Y j)
    intro h
    exact hY ⟨i, j, hij, h⟩
  have p1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y : Fin N → Euc d => Y i) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).contDiff
  have p2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y : Fin N → Euc d => Y j) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j).contDiff
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y : Fin N → Euc d => (Y i, Y j)) :=
    p1.prodMk p2
  exact hψ.comp hpair.contDiffOn hmap

/-! ### Slices along one particle -/

theorem m417_affine_contDiff {N : ℕ} (Y0 : Fin N → Euc d) (i : Fin N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : Euc d => Y0 + (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) u) :=
  contDiff_const.add (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i).contDiff

theorem m417_slice_eq {N : ℕ} (Φ : Config d N → ℝ) (X : Config d N) (i : Fin N) (u : Euc d) :
    HRS.MD.DOMProof.slice Φ X i u = configLift (fun _ => Φ) 0
      ((fun k => Torus.rep (X k)) + (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) u) := by
  unfold HRS.MD.DOMProof.slice configLift
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp [HRS.MD.DOMProof.shiftX, Torus.mk_add, Torus.mk_rep]
  · simp [HRS.MD.DOMProof.shiftX, hk, Torus.mk_rep]

theorem m417_fderiv_slice {N : ℕ} (Φ : Config d N → ℝ) {X : Config d N} (i : Fin N) (a : Fin d)
    (hL : DifferentiableAt ℝ (configLift (fun _ => Φ) 0) (fun k => Torus.rep (X k))) :
    fderiv ℝ (HRS.MD.DOMProof.slice Φ X i) 0 (EuclideanSpace.single a 1) =
      fderiv ℝ (configLift (fun _ => Φ) 0) (fun k => Torus.rep (X k)) (configBasis d N (i, a)) := by
  set Y0 : Fin N → Euc d := fun k => Torus.rep (X k) with hY0
  set S := ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i with hS
  have h0 : Y0 + S 0 = Y0 := by simp
  have hA : HasFDerivAt (fun u : Euc d => Y0 + S u) S 0 := by
    simpa using S.hasFDerivAt.const_add Y0
  have hL' : HasFDerivAt (configLift (fun _ => Φ) 0) (fderiv ℝ (configLift (fun _ => Φ) 0) Y0) (Y0 + S 0) := by
    rw [h0]; exact hL.hasFDerivAt
  have hcomp := hL'.comp (0 : Euc d) hA
  have hfun : HRS.MD.DOMProof.slice Φ X i = fun u => configLift (fun _ => Φ) 0 (Y0 + S u) :=
    funext fun u => m417_slice_eq Φ X i u
  rw [hfun, show (fun u => configLift (fun _ => Φ) 0 (Y0 + S u)) =
      configLift (fun _ => Φ) 0 ∘ (fun u => Y0 + S u) from rfl, hcomp.fderiv]
  rfl

theorem m417_norm_sq_gradient (g : Euc d → ℝ) :
    ‖gradient g 0‖ ^ 2 = ∑ a : Fin d, (fderiv ℝ g 0 (EuclideanSpace.single a 1)) ^ 2 := by
  have hi : ∀ v : Euc d, inner ℝ (gradient g 0) v = fderiv ℝ g 0 v := fun v => by
    unfold gradient
    exact InnerProductSpace.toDual_symm_apply
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner (gradient g 0) (gradient g 0)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hb : inner ℝ (EuclideanSpace.single a 1) (gradient g 0) = fderiv ℝ g 0 (EuclideanSpace.single a 1) := by
    rw [real_inner_comm]; exact hi _
  have hb2 : inner ℝ (gradient g 0) (EuclideanSpace.single a 1) = fderiv ℝ g 0 (EuclideanSpace.single a 1) :=
    hi _
  rw [EuclideanSpace.basisFun_apply, hb2, hb, sq]

theorem m417_configGradSq_eq {N : ℕ} (Φ : Config d N → ℝ) {X : Config d N} (hX : X ∉ collisionSet d N)
    (hL : DifferentiableAt ℝ (configLift (fun _ => Φ) 0) (fun k => Torus.rep (X k))) :
    configGradSq Φ X = ∑ i, ‖configGrad Φ X i‖ ^ 2 := by
  have _hX := hX
  unfold configGradSq
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hg : configGrad Φ X i = gradient (HRS.MD.DOMProof.slice Φ X i) 0 := rfl
  rw [hg, m417_norm_sq_gradient]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [m417_fderiv_slice Φ i a hL]

theorem m417_configGrad_sub_const {N : ℕ} (Φ : Config d N → ℝ) (c : ℝ) (X : Config d N) (i : Fin N) :
    configGrad (fun Y => Φ Y - c) X i = configGrad Φ X i := by
  unfold configGrad gradient
  rw [fderiv_sub_const]

theorem m417_configGradSq_nonneg {N : ℕ} (Φ : Config d N → ℝ) (X : Config d N) :
    0 ≤ configGradSq Φ X := by
  unfold configGradSq
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

theorem m417_measurable_configGradSq {N : ℕ} (Φ : Config d N → ℝ) :
    Measurable (configGradSq Φ) := by
  unfold configGradSq
  have hrep : Measurable (fun X : Config d N => fun i => Torus.rep (X i)) :=
    measurable_pi_iff.mpr fun i => (HRS.Q84d.q84d_measurable_rep d).comp (measurable_pi_apply i)
  have hD : Measurable (fun X : Config d N =>
      fderiv ℝ (configLift (fun _ => Φ) 0) (fun i => Torus.rep (X i))) :=
    (measurable_fderiv (𝕜 := ℝ) (f := configLift (fun _ => Φ) 0)).comp hrep
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (((ContinuousLinearMap.apply ℝ ℝ (configBasis d N k)).continuous.measurable.comp hD)).pow_const 2

/-- The measurable witness `G`: the honest generator on the collision-free set, zero on collisions. -/
theorem m417_measurable_G {s : ℝ} {N : ℕ} (hsd : s < d) (V : Torus d → ℝ) (β : ℝ)
    (ψ : Torus d → Torus d → ℝ) (hψm : Measurable (Function.uncurry ψ))
    (hψs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) :
    Measurable ((collisionSet d N)ᶜ.indicator (particleGen d s V β (Fstat (N := N) ψ))) := by
  refine HRS.MD.DOMProof.domp_measurable_particleGen V β hsd (Q84e.q84e_measurable_Fstat hψm)
    (m417_isOpen_compl_collision N) ?_
  intro X hX i
  have hY0 := m417_rep_mem X hX
  have hL : ContDiffAt ℝ 2 (configLift (fun _ => Fstat (N := N) ψ) 0) (fun k => Torus.rep (X k)) :=
    ((m417_contDiffOn_Fstat ψ hψs).contDiffAt ((m417_isOpen_coverFree N).mem_nhds hY0)).of_le (by simp)
  have hsl : HRS.MD.DOMProof.slice (Fstat (N := N) ψ) X i =
      (configLift (fun _ => Fstat (N := N) ψ) 0) ∘
        (fun u : Euc d => (fun k => Torus.rep (X k)) +
          (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) u) := by
    funext u
    exact m417_slice_eq _ X i u
  rw [hsl]
  have h0 : (fun k => Torus.rep (X k)) + (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) (0 : Euc d)
      = fun k => Torus.rep (X k) := by simp
  have hg : ContDiffAt ℝ 2 (configLift (fun _ => Fstat (N := N) ψ) 0)
      (((fun u : Euc d => (fun k => Torus.rep (X k)) +
          (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) u) 0)) := by
    rw [show ((fun u : Euc d => (fun k => Torus.rep (X k)) +
          (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) u) 0) = fun k => Torus.rep (X k) from h0]
    exact hL
  exact ContDiffAt.comp (0 : Euc d) hg
    ((m417_affine_contDiff (fun k => Torus.rep (X k)) i).contDiffAt.of_le (by simp))

/-! ### The `L²` identity for `E` and the energy -/

theorem m417_ofReal_configGradSq {N : ℕ} (Φ : Config d N → ℝ) (X : Config d N)
    (hX : X ∉ collisionSet d N)
    (hL : DifferentiableAt ℝ (configLift (fun _ => Φ) 0) (fun k => Torus.rep (X k))) :
    ENNReal.ofReal (configGradSq Φ X) = ∑ i, ‖configGrad Φ X i‖ₑ ^ 2 := by
  rw [m417_configGradSq_eq Φ hX hL, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

/-! ### The mode package -/

theorem mode_package_proof (hd : 2 ≤ d) {s : ℝ} (hcrit : s = d / 2) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (hρS : Torus.IsSmooth ρβ) (hρpos : ∀ x, 0 < ρβ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 2 ≤ N → ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      ∃ F G E : Config d N → ℝ,
        Measurable F ∧ Measurable G ∧ Measurable E ∧
        IsLZTest (canonicalGibbs (periodicRiesz d s) V N β) F ∧
        ContDiffOn ℝ 1 (configLift (fun _ => F) 0) (coverFree d N) ∧
        MD.DOM.IsInClosedGenerator d s V β (canonicalGibbs (periodicRiesz d s) V N β) F G ∧
        ∫ Y, F Y ∂(canonicalGibbs (periodicRiesz d s) V N β) = 0 ∧
        (∀ X : Config d N, X ∉ collisionSet d N →
          Real.sqrt N / 2 * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
              (quadStat (hTransport d s f) (withDensityReal ρβ)) X = -G X + E X) ∧
        ∫⁻ Y, ENNReal.ofReal (F Y ^ 2) ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) ∧
        ∫⁻ Y, ENNReal.ofReal (E Y ^ 2) ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) ∧
        ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2 ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) ∧
        ∫⁻ Y, ENNReal.ofReal (configGradSq F Y) ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  have hρs : SmoothPosDensity ρβ := ⟨hρβ.1, hρS, hρpos⟩
  obtain ⟨Ψ, Cpp, -, hPP⟩ := HRS.pair_poisson_proof hd hcrit β hβ V hV ρβ hρβ hρs
  obtain ⟨Cnf, hNF⟩ := HRS.normal_form_proof hd hcrit β hβ V hV ρβ hρβ hρs
  have hdom := HRS.MD.DOMProof.normal_form_domain_proof hd hcrit β hβ V hV ρβ hρβ hρs
  obtain ⟨c0, hc0def⟩ : ∃ c0 : ℝ, c0 = max Cnf 0 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c0 := hc0def ▸ le_max_right _ _
  have hCnf : Cnf ≤ c0 := hc0def ▸ le_max_left _ _
  refine ⟨3 * c0 * (|Cpp| + 1), mul_nonneg (mul_nonneg (by norm_num) hc0) (by positivity),
    fun N hN f hf => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  haveI : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) :=
    Q84d.q84d_isProb hd hcrit hV hβ hN1 (N := N)
  obtain ⟨hψ, -, -⟩ := hPP f hf
  obtain ⟨hQint, hFint, herrint, hid, hbound⟩ := hNF f _ (Ψ f) hf hψ N hN
  have hdomN := hdom f _ (Ψ f) hf hψ N hN
  have hK0 : 0 ≤ Cpp * posSeminorm (8 * d + 80) f := Q84d.q84d_K_nonneg hd hcrit hψ
  have hP0 : 0 ≤ posSeminorm (8 * d + 80) f := Q84d.q84d_posSeminorm_nonneg _ f
  generalize hP : posSeminorm (8 * d + 80) f = P at hP0 hbound hψ hdomN hK0 ⊢
  generalize hK : Cpp * P = K₁ at hK0 hbound hψ hdomN
  set μ := canonicalGibbs (periodicRiesz d s) V N β with hμ
  have hac : μ ≪ (volume : Measure (Config d N)) := Q84d.q84d_gibbs_ac
  have hae : ∀ᵐ X ∂μ, X ∉ collisionSet d N :=
    hac.ae_le (Q84d.q84d_ae_not_collision (d := d) (N := N) (by omega))
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (N : ℝ) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  rw [← hr] at hbound
  have hr0 : 0 ≤ r := hr ▸ Real.rpow_nonneg hNpos.le _
  have hKP0 : 0 ≤ K₁ + P := by linarith
  have hKP : K₁ + P ≤ (|Cpp| + 1) * P := by
    rw [← hK]; nlinarith [mul_le_mul_of_nonneg_right (le_abs_self Cpp) hP0]
  obtain ⟨B0, hB0⟩ : ∃ B : ℝ, B = c0 * (K₁ + P) * r := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 3 * c0 * (|Cpp| + 1) * P * r := ⟨_, rfl⟩
  have hB0nn : 0 ≤ B0 := by rw [hB0]; exact mul_nonneg (mul_nonneg hc0 hKP0) hr0
  have hMB : 3 * B0 ≤ M := by
    rw [hB0, hM]
    have h1 : (K₁ + P) * r ≤ ((|Cpp| + 1) * P) * r := mul_le_mul_of_nonneg_right hKP hr0
    have h2 := mul_le_mul_of_nonneg_left h1 hc0
    nlinarith [h2]
  have hB0le : B0 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hbB : ENNReal.ofReal (Cnf * (K₁ + P) * r) ≤ ENNReal.ofReal B0 := by
    apply ENNReal.ofReal_le_ofReal
    rw [hB0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCnf hKP0) hr0
  have hsum := hbound.trans hbB
  -- the four terms of the normal-form bound
  have tA : eLpNorm (centeredUnder μ (Fstat (N := N) (Ψ f))) 2 μ ≤ ENNReal.ofReal B0 :=
    ((le_self_add.trans le_self_add).trans le_self_add).trans hsum
  have tB : (∫⁻ X, ∑ i, ‖configGrad (Fstat (N := N) (Ψ f)) X i‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal B0 :=
    ((le_add_self.trans le_self_add).trans le_self_add).trans hsum
  have tC : eLpNorm (centeredUnder μ (errStat d s ρβ (N := N) (Ψ f))) 2 μ ≤ ENNReal.ofReal B0 :=
    (le_add_self.trans le_self_add).trans hsum
  have tD : ENNReal.ofReal (1 / (N : ℝ)) * eLpNorm (fun X : Config d N => Real.sqrt N *
      centeredUnder μ (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X) 2 μ ≤
      ENNReal.ofReal B0 :=
    le_add_self.trans hsum
  -- the constant
  have hMsq : M ^ 2 = (3 * c0 * (|Cpp| + 1) * P) ^ 2 / N := by
    rw [hM, mul_pow, hr, m417_rpow_sq N hNpos]
    ring
  rw [← hMsq]
  have tB' : ∫⁻ X, ∑ i, ‖configGrad (Fstat (N := N) (Ψ f)) X i‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (M ^ 2) :=
    (m417_sq_of_half hB0nn tB).trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hB0nn hB0le 2))
  -- the witnesses
  obtain ⟨F, hF⟩ : ∃ F : Config d N → ℝ, F = centeredUnder μ (Fstat (N := N) (Ψ f)) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Config d N → ℝ,
      G = (collisionSet d N)ᶜ.indicator (particleGen d s V β (Fstat (N := N) (Ψ f))) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Config d N → ℝ, E = fun X => Real.sqrt N / 2 *
      centeredUnder μ (quadStat (hTransport d s f) (withDensityReal ρβ)) X + G X := ⟨_, rfl⟩
  -- measurability
  have hFm : Measurable F := by
    rw [hF]; exact (Q84e.q84e_measurable_Fstat hψ.measurable).sub measurable_const
  have hGm : Measurable G := by
    rw [hG]; exact m417_measurable_G hsd V β (Ψ f) hψ.measurable hψ.size.smooth
  have hcqm : Measurable (fun X : Config d N =>
      centeredUnder μ (quadStat (hTransport d s f) (withDensityReal ρβ)) X) :=
    (HRS.Quad.measurable_quadStat (h := hTransport d s f)
      (HRS.LocalDivAux.measurable_hTransport hsd hf) (withDensityReal ρβ)).sub measurable_const
  have hEm : Measurable E := by
    rw [hE]; exact (hcqm.const_mul _).add hGm
  -- regularity of F
  have hFcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => F) 0) (coverFree d N) := by
    rw [hF]; exact (m417_contDiffOn_Fstat (N := N) (Ψ f) hψ.size.smooth).sub contDiffOn_const
  have hcd1 : ContDiffOn ℝ 1 (configLift (fun _ => F) 0) (coverFree d N) :=
    hFcd.of_le (by exact_mod_cast le_top)
  have hdiff : ∀ X : Config d N, X ∉ collisionSet d N →
      DifferentiableAt ℝ (configLift (fun _ => F) 0) (fun k => Torus.rep (X k)) := fun X hX =>
    (hFcd.contDiffAt ((m417_isOpen_coverFree N).mem_nhds (m417_rep_mem X hX))).differentiableAt
      (by simp)
  -- energy
  have hconf : ∀ X : Config d N, ∀ i : Fin N,
      configGrad F X i = configGrad (Fstat (N := N) (Ψ f)) X i := by
    intro X i; rw [hF]; exact m417_configGrad_sub_const _ _ X i
  have hsumF : ∀ᵐ X ∂μ, ENNReal.ofReal (configGradSq F X) = ∑ i, ‖configGrad F X i‖ₑ ^ 2 := by
    filter_upwards [hae] with X hX
    exact m417_ofReal_configGradSq F X hX (hdiff X hX)
  have hLint : ∫⁻ X, ENNReal.ofReal (configGradSq F X) ∂μ ≤ ENNReal.ofReal (M ^ 2) := by
    rw [lintegral_congr_ae hsumF]
    simp_rw [hconf]
    exact tB'
  have hnn : ∀ X, ‖configGradSq F X‖ₑ = ENNReal.ofReal (configGradSq F X) :=
    fun X => Real.enorm_eq_ofReal (m417_configGradSq_nonneg F X)
  have hen : Integrable (configGradSq F) μ := by
    refine ⟨(m417_measurable_configGradSq F).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [hnn]
    exact lt_of_le_of_lt hLint ENNReal.ofReal_lt_top
  -- the `L²` bounds
  have tF : eLpNorm F 2 μ ≤ ENNReal.ofReal M := by
    rw [hF]; exact tA.trans (ENNReal.ofReal_le_ofReal hB0le)
  have bF : ∫⁻ Y, ENNReal.ofReal (F Y ^ 2) ∂μ ≤ ENNReal.ofReal (M ^ 2) :=
    m417_sq_bound F hM0 hFm.aestronglyMeasurable tF
  -- the error statistic
  have hA1 : Measurable (aCoef d s ρβ f) := HRS.Q84d.q84d_measurable_aCoef hsd hρs.density hf
  have hζ0 : Measurable (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => hA1.comp (measurable_pi_apply i))
  have hgζm : Measurable (fun X : Config d N => Real.sqrt N *
      centeredUnder μ (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X) :=
    measurable_const.mul (hζ0.sub measurable_const)
  have hcen : AEStronglyMeasurable (fun X : Config d N =>
      centeredUnder μ (errStat d s ρβ (N := N) (Ψ f)) X) μ :=
    herrint.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hz2 : AEStronglyMeasurable (fun X : Config d N =>
      (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X)) μ :=
    ((measurable_const.mul hgζm)).aestronglyMeasurable
  have hEeq : E =ᵐ[μ] fun X : Config d N => centeredUnder μ (errStat d s ρβ (N := N) (Ψ f)) X -
      (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X) := by
    filter_upwards [hae] with X hX
    have h1 := hid X hX
    simp only [hE, hG]
    rw [Set.indicator_of_mem (show X ∈ (collisionSet d N)ᶜ from hX)]
    linarith [h1]
  have hsub : eLpNorm (fun X : Config d N => centeredUnder μ (errStat d s ρβ (N := N) (Ψ f)) X -
      (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X)) 2 μ ≤
      eLpNorm (fun X : Config d N => centeredUnder μ (errStat d s ρβ (N := N) (Ψ f)) X) 2 μ +
      eLpNorm (fun X : Config d N => (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X)) 2 μ :=
    eLpNorm_sub_le (by norm_num)
  have hc2 : eLpNorm (fun X : Config d N => (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X)) 2 μ =
      2 * (ENNReal.ofReal (1 / (N : ℝ)) * eLpNorm (fun X : Config d N => Real.sqrt N *
        centeredUnder μ (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X) 2 μ) := by
    rw [show (fun X : Config d N => (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X)) =
        (2 / (N : ℝ)) • (fun X : Config d N => Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X) from rfl,
      eLpNorm_const_smul, Real.enorm_of_nonneg (by positivity)]
    rw [show (2 / (N : ℝ)) = 2 * (1 / (N : ℝ)) by ring, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat]
    ring
  have hE3 : eLpNorm E 2 μ ≤ ENNReal.ofReal (3 * B0) := by
    rw [eLpNorm_congr_ae hEeq]
    have h3 : ENNReal.ofReal (3 * B0) =
        ENNReal.ofReal B0 + (ENNReal.ofReal B0 + ENNReal.ofReal B0) := by
      rw [show 3 * B0 = B0 + (B0 + B0) by ring, ENNReal.ofReal_add hB0nn (by linarith),
        ENNReal.ofReal_add hB0nn hB0nn]
    rw [h3]
    refine hsub.trans (add_le_add tC ?_)
    rw [hc2]
    exact (mul_le_mul_of_nonneg_left tD (by norm_num : (0 : ℝ≥0∞) ≤ 2)).trans (two_mul _).le
  have bE : ∫⁻ Y, ENNReal.ofReal (E Y ^ 2) ∂μ ≤ ENNReal.ofReal (M ^ 2) :=
    (m417_sq_bound E (by linarith) hEm.aestronglyMeasurable hE3).trans
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith) (by linarith) 2))
  -- conjuncts
  have hint0 : ∫ Y, F Y ∂μ = 0 := by
    rw [hF]
    simp only [centeredUnder]
    rw [integral_sub hFint (integrable_const _)]
    simp
  have hGae : particleGen d s V β (Fstat (N := N) (Ψ f)) =ᵐ[μ] G := by
    filter_upwards [hae] with X hX
    rw [hG, Set.indicator_of_mem (show X ∈ (collisionSet d N)ᶜ from hX)]
  have hclos : MD.DOM.IsInClosedGenerator d s V β μ F G := by
    rw [hF]; exact hdomN.congr_ae hGae
  have hident : ∀ X : Config d N, X ∉ collisionSet d N →
      Real.sqrt N / 2 * centeredUnder μ (quadStat (hTransport d s f) (withDensityReal ρβ)) X =
        -G X + E X := by
    intro X _
    simp only [hE]
    ring
  have tF' : ∫⁻ Y, ENNReal.ofReal (F Y ^ 2) ∂μ ≤ ENNReal.ofReal (M ^ 2) := bF
  have hgrad : ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (M ^ 2) := by
    simp_rw [hconf]
    exact tB'
  refine ⟨F, G, E, hFm, hGm, hEm, ⟨hFm, lt_of_le_of_lt tF ENNReal.ofReal_lt_top,
    hcd1, hen⟩, hcd1, hclos, hint0, hident, bF, bE, hgrad, hLint⟩

end HRS.ME

end
