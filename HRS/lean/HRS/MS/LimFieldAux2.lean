import HRS.MS.LimFieldAux1

/-!
# SB7, part 2: uniqueness half of `limit_field_rd_duality` and the weak form
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace Matrix

namespace HRS.MS.U10

open HRS HRS.Whole HRS.MP.HNegInfra

variable {d : ℕ}

/-! ### Uniqueness in law -/

/-- The law of `G + Ψ(η)` for `G` independent of `η` depends only on the laws of `G` and `η`. -/
theorem sb7_law_add_indep {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {G : Ω → E} {η : Ω → Z} (hG : AEMeasurable G P)
    (hη : AEMeasurable η P) (hind : IndepFun G η P) {Ψ : Z → E} (hΨ : Measurable Ψ) :
    law P (fun ω => G ω + Ψ (η ω)) =
      ((law P G).prod (law P η)).map (fun z => z.1 + Ψ z.2) := by
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hG hη).1 hind
  have hf : Measurable fun z : E × Z => z.1 + Ψ z.2 := measurable_fst.add (hΨ.comp measurable_snd)
  show P.map _ = _
  rw [← h1, AEMeasurable.map_map_of_aemeasurable hf.aemeasurable (hG.prodMk hη)]
  rfl

theorem sb7_aemeas_vec {Γ : ℝ} {C : WholeCoeff d} {A q T : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {η : Ω → (Euc d → ℝ) → ℝ} {Y : ℝ → Ω → HNeg d Γ}
    (h : IsAdjointDualityLimitW P C Γ A q T η Y) (hη : AEMeasurable η P) {p : ℕ}
    {ts : Fin p → ℝ} {φ : Fin p → Euc d → ℝ}
    (hφ : ∀ a, IsSobolevTest Γ (φ a)) :
    AEMeasurable (fun ζ => (WithLp.toLp 2 fun a =>
      HNeg.pairing (φ a) (Y (ts a) ζ) - A * η ζ (propagatorW C 0 (ts a) (φ a)) :
        EuclideanSpace ℝ (Fin p))) P := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp_aemeasurable
    (aemeasurable_pi_iff.2 fun a => ?_)
  refine AEMeasurable.sub ((mhn_continuous_pairing (hφ a)).measurable.comp (h.meas (ts a))).aemeasurable ?_
  exact ((measurable_pi_apply _).comp_aemeasurable hη).const_mul A


/-- Uniqueness in law of the adjoint-duality solution (S.B.7(iii)(b)): the finite-dimensional laws of
`(⟨φ_a, Y^{t_a}⟩)_a` depend only on the law of the initial functional. -/
theorem sb7_duality_unique {Γ : ℝ} {C : WholeCoeff d} {A q T : ℝ}
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁)
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (η₁ : Ω₁ → (Euc d → ℝ) → ℝ) (η₂ : Ω₂ → (Euc d → ℝ) → ℝ)
    (Y₁ : ℝ → Ω₁ → HNeg d Γ) (Y₂ : ℝ → Ω₂ → HNeg d Γ) (hη₁ : AEMeasurable η₁ P₁)
    (hη₂ : AEMeasurable η₂ P₂) :
    law P₁ η₁ = law P₂ η₂ →
    IsAdjointDualityLimitW P₁ C Γ A q T η₁ Y₁ → IsAdjointDualityLimitW P₂ C Γ A q T η₂ Y₂ →
    ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ),
      (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) → (∀ a, IsSobolevTest Γ (φ a)) →
      law P₁ (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (φ a) (Y₁ (ts a) ζ) :
          EuclideanSpace ℝ (Fin p))) =
        law P₂ (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (φ a) (Y₂ (ts a) ζ) :
          EuclideanSpace ℝ (Fin p))) := by
  intro hlaw h₁ h₂ p ts φ hts hφ
  obtain ⟨hi₁, hl₁⟩ := h₁.gaussian_part p ts φ hts hφ
  obtain ⟨hi₂, hl₂⟩ := h₂.gaussian_part p ts φ hts hφ
  have hΨ : Measurable fun z : (Euc d → ℝ) → ℝ =>
      (WithLp.toLp 2 fun a => A * z (propagatorW C 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => by fun_prop)
  have hG₁ : AEMeasurable (fun ζ => (WithLp.toLp 2 fun a =>
      HNeg.pairing (φ a) (Y₁ (ts a) ζ) - A * η₁ ζ (propagatorW C 0 (ts a) (φ a)) :
        EuclideanSpace ℝ (Fin p))) P₁ :=
    sb7_aemeas_vec h₁ hη₁ hφ
  have hG₂ : AEMeasurable (fun ζ => (WithLp.toLp 2 fun a =>
      HNeg.pairing (φ a) (Y₂ (ts a) ζ) - A * η₂ ζ (propagatorW C 0 (ts a) (φ a)) :
        EuclideanSpace ℝ (Fin p))) P₂ :=
    sb7_aemeas_vec h₂ hη₂ hφ
  have e₁ : (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (φ a) (Y₁ (ts a) ζ) :
      EuclideanSpace ℝ (Fin p))) = fun ζ => (WithLp.toLp 2 fun a =>
      HNeg.pairing (φ a) (Y₁ (ts a) ζ) - A * η₁ ζ (propagatorW C 0 (ts a) (φ a)) :
        EuclideanSpace ℝ (Fin p)) + (WithLp.toLp 2 fun a =>
      A * η₁ ζ (propagatorW C 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p)) := by
    funext ζ; ext a; simp
  have e₂ : (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (φ a) (Y₂ (ts a) ζ) :
      EuclideanSpace ℝ (Fin p))) = fun ζ => (WithLp.toLp 2 fun a =>
      HNeg.pairing (φ a) (Y₂ (ts a) ζ) - A * η₂ ζ (propagatorW C 0 (ts a) (φ a)) :
        EuclideanSpace ℝ (Fin p)) + (WithLp.toLp 2 fun a =>
      A * η₂ ζ (propagatorW C 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p)) := by
    funext ζ; ext a; simp
  rw [e₁, e₂, sb7_law_add_indep P₁ hG₁ hη₁ hi₁ hΨ, sb7_law_add_indep P₂ hG₂ hη₂ hi₂ hΨ,
    hl₁, hl₂, hlaw]


/-! ### Joint Gaussian laws independent of `η`: characteristic formula and `L²` closure -/

section Char

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {P : Measure Ω}
  [IsProbabilityMeasure P] {m : ℕ}

/-- the joint characteristic integrand -/
def sb7_cf (V : Ω → EuclideanSpace ℝ (Fin m)) (η : Ω → Z) (t : EuclideanSpace ℝ (Fin m))
    (S : Set Z) (ω : Ω) : ℂ :=
  Complex.exp (⟪V ω, t⟫ * Complex.I) * (S.indicator (fun _ => (1 : ℂ)) (η ω))

theorem sb7_char_of_indep_law {V : Ω → EuclideanSpace ℝ (Fin m)} {η : Ω → Z} (hV : Measurable V)
    (hη : Measurable η) {S' : Matrix (Fin m) (Fin m) ℝ} (hS' : S'.PosSemidef)
    (hind : IndepFun V η P) (hlaw : law P V = multivariateGaussian 0 S')
    (t : EuclideanSpace ℝ (Fin m)) {S : Set Z} (hS : MeasurableSet S) :
    ∫ ω, sb7_cf V η t S ω ∂P =
      Complex.exp (-((t ⬝ᵥ S' *ᵥ t : ℝ) : ℂ) / 2) * ((P (η ⁻¹' S)).toReal : ℂ) := by
  have h1 := hind.integral_fun_comp_mul_comp (𝕜 := ℂ) (f := fun v => Complex.exp (⟪v, t⟫ * Complex.I))
    (g := fun z => S.indicator (fun _ => (1 : ℂ)) z) hV.aemeasurable hη.aemeasurable
    (by fun_prop) ((measurable_const.indicator hS).aestronglyMeasurable)
  unfold sb7_cf
  rw [h1]
  congr 1
  · have : ∫ ω, Complex.exp (⟪V ω, t⟫ * Complex.I) ∂P = charFun (law P V) t := by
      rw [charFun_apply]
      show _ = ∫ x, _ ∂(P.map V)
      rw [integral_map hV.aemeasurable (by fun_prop)]
    rw [this, hlaw, charFun_multivariateGaussian hS']
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    congr 1
    ring
  · have : ∫ ω, S.indicator (fun _ => (1 : ℂ)) (η ω) ∂P = ((P (η ⁻¹' S)).toReal : ℂ) := by
      have e : (fun ω => S.indicator (fun _ => (1 : ℂ)) (η ω)) =
          (η ⁻¹' S).indicator (fun _ => (1 : ℂ)) := by
        funext ω; simp only [Set.indicator, Set.mem_preimage]; rfl
      rw [e, integral_indicator_const _ (hη hS)]
      simp [Measure.real]
    exact this

theorem sb7_indep_law_of_char {V : Ω → EuclideanSpace ℝ (Fin m)} {η : Ω → Z} (hV : Measurable V)
    (hη : Measurable η) {S' : Matrix (Fin m) (Fin m) ℝ} (hS' : S'.PosSemidef)
    (hchar : ∀ (t : EuclideanSpace ℝ (Fin m)) (S : Set Z), MeasurableSet S →
      ∫ ω, sb7_cf V η t S ω ∂P =
        Complex.exp (-((t ⬝ᵥ S' *ᵥ t : ℝ) : ℂ) / 2) * ((P (η ⁻¹' S)).toReal : ℂ)) :
    IndepFun V η P ∧ law P V = multivariateGaussian 0 S' := by
  set N := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S' with hN
  have hmu : ∀ S : Set Z, MeasurableSet S →
      (P.restrict (η ⁻¹' S)).map V = P (η ⁻¹' S) • N := by
    intro S hS
    haveI : IsFiniteMeasure (P (η ⁻¹' S) • N) := Measure.smul_finite N (measure_ne_top P _)
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [charFun_apply, charFun_apply, integral_map hV.aemeasurable (by fun_prop),
      integral_smul_measure, ← charFun_apply, hN, charFun_multivariateGaussian hS']
    have h1 := hchar t S hS
    have e : (fun ω => sb7_cf V η t S ω) = (η ⁻¹' S).indicator
        (fun ω => Complex.exp (⟪V ω, t⟫ * Complex.I)) := by
      funext ω
      unfold sb7_cf
      by_cases h : η ω ∈ S
      · have : ω ∈ η ⁻¹' S := h
        simp [Set.indicator, h, this]
      · have : ω ∉ η ⁻¹' S := h
        simp [Set.indicator, h, this]
    rw [e, integral_indicator (hη hS)] at h1
    rw [h1]
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    simp only [Complex.real_smul]
    rw [mul_comm]
    congr 2
    ring
  have hlaw : law P V = N := by
    have := hmu Set.univ MeasurableSet.univ
    simpa [law] using this
  refine ⟨?_, hlaw⟩
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have h1 := congrArg (fun μ => μ s) (hmu t ht)
  simp only [Measure.smul_apply, smul_eq_mul] at h1
  rw [Measure.map_apply hV hs, Measure.restrict_apply (hV hs)] at h1
  have h2 : N s = P (V ⁻¹' s) := by
    rw [← hlaw]; exact Measure.map_apply hV hs
  rw [h2] at h1
  rw [h1, mul_comm]

/-! ### Scalar closure -/

/-- Gram matrix of `L²` functions is positive semidefinite. -/
theorem sb7_gram_psd_fn {κ : Type} [Fintype κ] [DecidableEq κ] (g : κ → Ω → ℝ)
    (hg : ∀ a, MemLp (g a) 2 P) :
    (Matrix.of fun a b => ∫ ω, g a ω * g b ω ∂P : Matrix κ κ ℝ).PosSemidef := by
  have h := HRS.A33.a33_gram_psd (fun a => (hg a).toLp (g a))
  have e : (Matrix.of fun a b => ∫ ω, g a ω * g b ω ∂P : Matrix κ κ ℝ) =
      Matrix.of fun a b => inner ℝ ((hg a).toLp (g a)) ((hg b).toLp (g b)) := by
    ext a b
    simp only [Matrix.of_apply]
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hg a).coeFn_toLp, (hg b).coeFn_toLp] with ω h1 h2
    simp [h1, h2, mul_comm]
  rw [e]; exact h

/-- The scalar characteristic formula for a real random variable `h`. -/
def Sb7Sc (P : Measure Ω) (η : Ω → Z) (h : Ω → ℝ) : Prop :=
  ∀ S : Set Z, MeasurableSet S →
    ∫ ω, Complex.exp ((h ω : ℂ) * Complex.I) * (S.indicator (fun _ => (1 : ℂ)) (η ω)) ∂P =
      Complex.exp (-((∫ ω, h ω ^ 2 ∂P : ℝ) : ℂ) / 2) * ((P (η ⁻¹' S)).toReal : ℂ)

theorem Sb7Sc.congr {η : Ω → Z} {h h' : Ω → ℝ} (hh : Sb7Sc P η h) (e : h =ᵐ[P] h') :
    Sb7Sc P η h' := by
  intro S hS
  have h1 := hh S hS
  have e1 : ∫ ω, Complex.exp ((h' ω : ℂ) * Complex.I) * (S.indicator (fun _ => (1 : ℂ)) (η ω)) ∂P =
      ∫ ω, Complex.exp ((h ω : ℂ) * Complex.I) * (S.indicator (fun _ => (1 : ℂ)) (η ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [e] with ω hω
    rw [hω]
  have e2 : ∫ ω, h' ω ^ 2 ∂P = ∫ ω, h ω ^ 2 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [e] with ω hω
    rw [hω]
  rw [e1, e2]; exact h1

/-- The data of a "Gaussian family independent of `η`". -/
structure Sb7Fam {Θ : Type*} (P : Measure Ω) (η : Ω → Z) (X : Θ → Ω → ℝ) (cov : Θ → Θ → ℝ) :
    Prop where
  meas : ∀ θ, Measurable (X θ)
  memLp : ∀ θ, MemLp (X θ) 2 P
  cov_eq : ∀ θ θ', ∫ ω, X θ ω * X θ' ω ∂P = cov θ θ'
  fdd : ∀ (k : ℕ) (θ : Fin k → Θ),
    IndepFun (fun ω => (WithLp.toLp 2 fun i => X (θ i) ω : EuclideanSpace ℝ (Fin k))) η P ∧
    law P (fun ω => (WithLp.toLp 2 fun i => X (θ i) ω : EuclideanSpace ℝ (Fin k))) =
      multivariateGaussian 0 (Matrix.of fun i j => cov (θ i) (θ j))

theorem Sb7Fam.sc_fin {Θ : Type*} {η : Ω → Z} {X : Θ → Ω → ℝ} {cov : Θ → Θ → ℝ}
    (hF : Sb7Fam P η X cov) (hη : Measurable η) (k : ℕ) (θ : Fin k → Θ) (τ : Fin k → ℝ) :
    Sb7Sc P η (fun ω => ∑ i, τ i * X (θ i) ω) := by
  classical
  obtain ⟨hind, hlaw⟩ := hF.fdd k θ
  have hpsd : (Matrix.of fun i j => cov (θ i) (θ j) : Matrix (Fin k) (Fin k) ℝ).PosSemidef := by
    have := sb7_gram_psd_fn (P := P) (fun i => X (θ i)) (fun i => hF.memLp _)
    convert this using 2
    funext a b
    exact (hF.cov_eq _ _).symm
  have hV : Measurable (fun ω => (WithLp.toLp 2 fun i => X (θ i) ω : EuclideanSpace ℝ (Fin k))) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun i => hF.meas _)
  intro S hS
  have h1 := sb7_char_of_indep_law hV hη hpsd hind hlaw
    (WithLp.toLp 2 τ : EuclideanSpace ℝ (Fin k)) hS
  have e1 : ∀ ω, ⟪(WithLp.toLp 2 fun i => X (θ i) ω : EuclideanSpace ℝ (Fin k)),
      (WithLp.toLp 2 τ : EuclideanSpace ℝ (Fin k))⟫ = ∑ i, τ i * X (θ i) ω := by
    intro ω
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have e2 : ∫ ω, (∑ i, τ i * X (θ i) ω) ^ 2 ∂P =
      (WithLp.toLp 2 τ : EuclideanSpace ℝ (Fin k)).ofLp ⬝ᵥ
        (Matrix.of fun i j => cov (θ i) (θ j)) *ᵥ (WithLp.toLp 2 τ : EuclideanSpace ℝ (Fin k)).ofLp := by
    have hint : ∀ i j, Integrable (fun ω => X (θ i) ω * X (θ j) ω) P := fun i j =>
      (hF.memLp (θ i)).integrable_mul (hF.memLp (θ j))
    have : ∀ ω, (∑ i, τ i * X (θ i) ω) ^ 2 =
        ∑ i, ∑ j, (τ i * τ j) * (X (θ i) ω * X (θ j) ω) := by
      intro ω
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp_rw [this]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _)]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hF.cov_eq]
    ring
  have e3 : (fun ω => sb7_cf (fun ω => (WithLp.toLp 2 fun i => X (θ i) ω : EuclideanSpace ℝ (Fin k)))
      η (WithLp.toLp 2 τ : EuclideanSpace ℝ (Fin k)) S ω) = fun ω =>
      Complex.exp (((∑ i, τ i * X (θ i) ω : ℝ) : ℂ) * Complex.I) *
        (S.indicator (fun _ => (1 : ℂ)) (η ω)) := by
    funext ω; unfold sb7_cf; rw [e1]
  rw [e3] at h1
  rw [h1, e2]

theorem sb7_finsupp_fin {Θ M : Type*} [AddCommMonoid M] [Module ℝ M] (c : Θ →₀ ℝ) (F : Θ → M) :
    ∃ (k : ℕ) (θ : Fin k → Θ) (τ : Fin k → ℝ), (c.sum fun θ a => a • F θ) = ∑ i, τ i • F (θ i) := by
  classical
  refine ⟨c.support.card, fun i => (c.support.equivFin.symm i).1,
    fun i => c (c.support.equivFin.symm i).1, ?_⟩
  rw [Finsupp.sum, ← Finset.sum_coe_sort c.support]
  exact (Equiv.sum_comp c.support.equivFin.symm
    (fun x : c.support => c x.1 • F x.1)).symm

theorem Sb7Fam.coeFn_comb {Θ : Type*} {η : Ω → Z} {X : Θ → Ω → ℝ} {cov : Θ → Θ → ℝ}
    (hF : Sb7Fam P η X cov) {k : ℕ} (θ : Fin k → Θ) (τ : Fin k → ℝ) :
    ⇑(∑ i, τ i • (hF.memLp (θ i)).toLp (X (θ i))) =ᵐ[P] fun ω => ∑ i, τ i * X (θ i) ω := by
  have h1 := HRS.A33.a33_coeFn_sum (P := P) Finset.univ (fun i => τ i • (hF.memLp (θ i)).toLp (X (θ i)))
  have h2 : ∀ᵐ ω ∂P, ∀ i, (τ i • (hF.memLp (θ i)).toLp (X (θ i)) : Lp ℝ 2 P) ω = τ i * X (θ i) ω := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (τ i) ((hF.memLp (θ i)).toLp (X (θ i))),
      (hF.memLp (θ i)).coeFn_toLp] with ω a b
    rw [a]; simp [b]
  filter_upwards [h1, h2] with ω a b
  rw [a]
  exact Finset.sum_congr rfl fun i _ => b i

theorem sb7_cf1_norm_sub (η : Ω → Z) (S : Set Z) (a b : ℝ) (ω : Ω) :
    ‖Complex.exp ((a : ℂ) * Complex.I) * (S.indicator (fun _ => (1 : ℂ)) (η ω)) -
      Complex.exp ((b : ℂ) * Complex.I) * (S.indicator (fun _ => (1 : ℂ)) (η ω))‖ ≤ |a - b| := by
  rw [← sub_mul, norm_mul]
  have h1 : ‖S.indicator (fun _ => (1 : ℂ)) (η ω)‖ ≤ 1 := by
    by_cases h : η ω ∈ S <;> simp [Set.indicator, h]
  calc _ ≤ ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ |a - b| := by rw [mul_one]; exact HRS.A33.a33_norm_exp_sub a b

theorem Sb7Fam.sc_closure {Θ : Type*} {η : Ω → Z} {X : Θ → Ω → ℝ} {cov : Θ → Θ → ℝ}
    (hF : Sb7Fam P η X cov) (hη : Measurable η) (f : Lp ℝ 2 P)
    (hf : f ∈ (Submodule.span ℝ
      (Set.range fun θ => (hF.memLp θ).toLp (X θ))).topologicalClosure) :
    Sb7Sc P η (f : Ω → ℝ) := by
  set K := Submodule.span ℝ (Set.range fun θ => (hF.memLp θ).toLp (X θ)) with hK
  -- step 1: elements of the span
  have hspan : ∀ g ∈ K, Sb7Sc P η (g : Ω → ℝ) := by
    intro g hg
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hg
    obtain ⟨k, θ, τ, hτ⟩ := sb7_finsupp_fin c (fun θ => (hF.memLp θ).toLp (X θ))
    rw [← hc, hτ]
    exact (hF.sc_fin hη k θ τ).congr (hF.coeFn_comb θ τ).symm
  -- step 2: limits
  have hf' : f ∈ closure (K : Set (Lp ℝ 2 P)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hf
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hf'
  intro S hS
  set A : (Ω → ℝ) → ℂ := fun h => ∫ ω, Complex.exp ((h ω : ℂ) * Complex.I) *
    (S.indicator (fun _ => (1 : ℂ)) (η ω)) ∂P with hA
  set B : (Ω → ℝ) → ℂ := fun h => Complex.exp (-((∫ ω, h ω ^ 2 ∂P : ℝ) : ℂ) / 2) *
    ((P (η ⁻¹' S)).toReal : ℂ) with hB
  have hint : ∀ h : Lp ℝ 2 P, Integrable (fun ω => Complex.exp (((h : Ω → ℝ) ω : ℂ) * Complex.I) *
      (S.indicator (fun _ => (1 : ℂ)) (η ω))) P := by
    intro h
    refine Integrable.of_bound (C := 1) ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ ?_
      · exact (Complex.continuous_exp.comp_aestronglyMeasurable
          ((Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.aestronglyMeasurable h)).mul
            aestronglyMeasurable_const))
      · exact ((measurable_const.indicator hS).comp hη).aestronglyMeasurable
    · refine Eventually.of_forall fun ω => ?_
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      by_cases h : η ω ∈ S <;> simp [Set.indicator, h]
  have hA_tend : Tendsto (fun n => A (u n : Ω → ℝ)) atTop (𝓝 (A (f : Ω → ℝ))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_iff_norm_sub_tendsto_zero.1 hlim)
    simp only [hA]
    rw [← integral_sub (hint _) (hint _)]
    have hd : MemLp (fun ω => (u n : Ω → ℝ) ω - (f : Ω → ℝ) ω) 2 P :=
      (Lp.memLp (u n)).sub (Lp.memLp f)
    calc ‖∫ ω, _ ∂P‖ ≤ ∫ ω, |(u n : Ω → ℝ) ω - (f : Ω → ℝ) ω| ∂P :=
          norm_integral_le_of_norm_le (hd.abs.integrable (by norm_num))
            (Eventually.of_forall fun ω => sb7_cf1_norm_sub η S _ _ ω)
      _ ≤ Real.sqrt (∫ ω, ((u n : Ω → ℝ) ω - (f : Ω → ℝ) ω) ^ 2 ∂P) :=
          HRS.A33.a33_integral_abs_le _ hd
      _ = ‖u n - f‖ := by
          rw [← Real.sqrt_sq (norm_nonneg (u n - f)), HRS.A33.a33_lp_norm_sq]
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_sub (u n) f] with ω h
          rw [h]; rfl
  have hB_tend : Tendsto (fun n => B (u n : Ω → ℝ)) atTop (𝓝 (B (f : Ω → ℝ))) := by
    have e : ∀ g : Lp ℝ 2 P, ∫ ω, (g : Ω → ℝ) ω ^ 2 ∂P = ‖g‖ ^ 2 := fun g =>
      (HRS.A33.a33_lp_norm_sq g).symm
    simp only [hB, e]
    have h1 : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖f‖) := (continuous_norm.tendsto f).comp hlim
    have h2 : Tendsto (fun n => ((‖u n‖ ^ 2 : ℝ) : ℂ)) atTop (𝓝 ((‖f‖ ^ 2 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp ((continuous_pow 2).tendsto _ |>.comp h1)
    exact ((Complex.continuous_exp.tendsto _).comp ((h2.neg).div_const 2)).mul_const _
  have hAB : ∀ n, A (u n : Ω → ℝ) = B (u n : Ω → ℝ) := fun n => hspan (u n) (hu n) S hS
  exact tendsto_nhds_unique hA_tend (by simpa only [← hAB] using hB_tend)

theorem sb7_coeFn_comb {m : ℕ} (g : Fin m → Ω → ℝ) (hg2 : ∀ a, MemLp (g a) 2 P) (τ : Fin m → ℝ) :
    ⇑(∑ a, τ a • (hg2 a).toLp (g a)) =ᵐ[P] fun ω => ∑ a, τ a * g a ω := by
  have h1 := HRS.A33.a33_coeFn_sum (P := P) Finset.univ
    (fun a => τ a • (hg2 a).toLp (g a))
  have h2 : ∀ᵐ ω ∂P, ∀ a, (τ a • (hg2 a).toLp (g a) : Lp ℝ 2 P) ω = τ a * g a ω := by
    rw [ae_all_iff]
    intro a
    filter_upwards [Lp.coeFn_smul (τ a) ((hg2 a).toLp (g a)), (hg2 a).coeFn_toLp] with ω x y
    rw [x]; simp [y]
  filter_upwards [h1, h2] with ω x y
  rw [x]
  exact Finset.sum_congr rfl fun a _ => y a

theorem sb7_int_sq_comb {m : ℕ} (g : Fin m → Ω → ℝ) (hg2 : ∀ a, MemLp (g a) 2 P) (τ : Fin m → ℝ) :
    ∫ ω, (∑ a, τ a * g a ω) ^ 2 ∂P =
      τ ⬝ᵥ (Matrix.of fun a b => ∫ ω, g a ω * g b ω ∂P) *ᵥ τ := by
  have hint : ∀ i j, Integrable (fun ω => g i ω * g j ω) P := fun i j =>
    (hg2 i).integrable_mul (hg2 j)
  have : ∀ ω, (∑ i, τ i * g i ω) ^ 2 = ∑ i, ∑ j, (τ i * τ j) * (g i ω * g j ω) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _)]
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  ring

theorem Sb7Fam.closure_vec {Θ : Type*} {η : Ω → Z} {X : Θ → Ω → ℝ} {cov : Θ → Θ → ℝ}
    (hF : Sb7Fam P η X cov) (hη : Measurable η) {m : ℕ} (g : Fin m → Ω → ℝ)
    (hgm : ∀ a, Measurable (g a)) (hg2 : ∀ a, MemLp (g a) 2 P)
    (hg : ∀ a, (hg2 a).toLp (g a) ∈ (Submodule.span ℝ
      (Set.range fun θ => (hF.memLp θ).toLp (X θ))).topologicalClosure) :
    IndepFun (fun ω => (WithLp.toLp 2 fun a => g a ω : EuclideanSpace ℝ (Fin m))) η P ∧
      law P (fun ω => (WithLp.toLp 2 fun a => g a ω : EuclideanSpace ℝ (Fin m))) =
        multivariateGaussian 0 (Matrix.of fun a b => ∫ ω, g a ω * g b ω ∂P) := by
  have hV : Measurable (fun ω => (WithLp.toLp 2 fun a => g a ω : EuclideanSpace ℝ (Fin m))) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => hgm a)
  refine sb7_indep_law_of_char hV hη (sb7_gram_psd_fn g hg2) ?_
  intro t S hS
  set τ : Fin m → ℝ := t.ofLp with hτ
  have hmem : (∑ a, τ a • (hg2 a).toLp (g a)) ∈ (Submodule.span ℝ
      (Set.range fun θ => (hF.memLp θ).toLp (X θ))).topologicalClosure :=
    Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hg a)
  have hsc := (hF.sc_closure hη _ hmem).congr (sb7_coeFn_comb g hg2 τ)
  have e1 : ∀ ω, ⟪(WithLp.toLp 2 fun a => g a ω : EuclideanSpace ℝ (Fin m)), t⟫ =
      ∑ a, τ a * g a ω := by
    intro ω
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hτ]
  have h1 := hsc S hS
  rw [sb7_int_sq_comb g hg2 τ] at h1
  have e3 : (fun ω => sb7_cf (fun ω => (WithLp.toLp 2 fun a => g a ω : EuclideanSpace ℝ (Fin m)))
      η t S ω) = fun ω => Complex.exp (((∑ a, τ a * g a ω : ℝ) : ℂ) * Complex.I) *
        (S.indicator (fun _ => (1 : ℂ)) (η ω)) := by
    funext ω; unfold sb7_cf; rw [e1]
  rw [e3, h1]

end Char

/-! ### Classical adjoint solutions: gradients -/

theorem sb7_grad_coord (g : Euc d → ℝ) (x : Euc d) (j : Fin d) :
    gradient g x j = fderiv ℝ g x (EuclideanSpace.single j 1) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Euc d)
    (x := EuclideanSpace.single j 1) (y := fderiv ℝ g x)
  have h2 : inner ℝ (gradient g x) (EuclideanSpace.single j (1 : ℝ)) = gradient g x j := by
    rw [EuclideanSpace.inner_single_right]; simp
  rw [← h2]
  exact h

/-- A classical adjoint solution gives a continuous gradient on `[0,t] × ℝ^d`. -/
theorem sb7_grad_cls {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) :
    Continuous (fun p : Set.Icc (0 : ℝ) t × Euc d => gradient (f p.1) p.2) := by
  have h1 := hf.cont_c2 1 (by norm_num)
  have e : (fun p : Set.Icc (0 : ℝ) t × Euc d => gradient (f p.1) p.2) = fun p =>
      (WithLp.toLp 2 fun j => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ
        (fun _ => EuclideanSpace.single j (1 : ℝ))) (iteratedFDeriv ℝ 1 (f p.1) p.2) :
          Euc d) := by
    funext p; ext j
    simp [sb7_grad_coord, iteratedFDeriv_one_apply]
  rw [e]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
    (continuous_pi fun j => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ
      (fun _ => EuclideanSpace.single j (1 : ℝ))).continuous.comp h1)

theorem sb7_grad_bdd {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) :
    ∃ B : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖gradient (f r) x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hf.bdd 1 (by norm_num)
  refine ⟨B, fun r hr x => ?_⟩
  have := hB r hr x
  rw [norm_iteratedFDeriv_one] at this
  simpa [gradient] using this

/-- The clamped gradient of the adjoint propagator. -/
def sb7_Gr (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ) (p : ℝ × Euc d) : Euc d :=
  gradient (propagatorW C (max 0 (min p.1 t)) t φ) p.2

/-- The gradient of the adjoint propagator, cut off to `r ≤ t`. -/
def sb7_H (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ) (p : ℝ × Euc d) : Euc d :=
  if p.1 ≤ t then sb7_Gr C t φ p else 0

open Classical in
theorem sb7_prop_eq {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ}
    (h : ∃ f, IsClassicalAdjointW C t φ f) :
    ∃ f, IsClassicalAdjointW C t φ f ∧ ∀ r, propagatorW C r t φ = f r :=
  ⟨h.choose, h.choose_spec, fun r => by simp [propagatorW, h]⟩

theorem sb7_Gr_cont {C : WholeCoeff d} {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (h : ∃ f, IsClassicalAdjointW C t φ f) : Continuous (sb7_Gr C t φ) := by
  obtain ⟨f, hf, hfe⟩ := sb7_prop_eq h
  have hc := sb7_grad_cls hf
  have hmem : ∀ r : ℝ, max 0 (min r t) ∈ Set.Icc (0 : ℝ) t := fun r =>
    ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩
  have : sb7_Gr C t φ = fun p => gradient (f (max 0 (min p.1 t))) p.2 := by
    funext p; simp [sb7_Gr, hfe]
  rw [this]
  have hcl : Continuous (fun p : ℝ × Euc d => max 0 (min p.1 t)) :=
    continuous_const.max (continuous_fst.min continuous_const)
  exact hc.comp ((hcl.subtype_mk (fun p => hmem p.1)).prodMk continuous_snd)

theorem sb7_Gr_bdd {C : WholeCoeff d} {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (h : ∃ f, IsClassicalAdjointW C t φ f) : ∃ B : ℝ, ∀ p, ‖sb7_Gr C t φ p‖ ≤ B := by
  obtain ⟨f, hf, hfe⟩ := sb7_prop_eq h
  obtain ⟨B, hB⟩ := sb7_grad_bdd hf
  refine ⟨B, fun p => ?_⟩
  simp only [sb7_Gr, hfe]
  exact hB _ ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩ _

theorem sb7_Gr_eq {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t)
    (x : Euc d) : sb7_Gr C t φ (r, x) = gradient (propagatorW C r t φ) x := by
  have : max 0 (min r t) = r := by
    rw [min_eq_left hr.2, max_eq_right hr.1]
  simp [sb7_Gr, this]

theorem sb7_H_meas {C : WholeCoeff d} {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (h : ∃ f, IsClassicalAdjointW C t φ f) : Measurable (sb7_H C t φ) :=
  Measurable.ite (measurableSet_le measurable_fst measurable_const)
    (sb7_Gr_cont ht h).measurable measurable_const

theorem sb7_H_bdd {C : WholeCoeff d} {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (h : ∃ f, IsClassicalAdjointW C t φ f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖sb7_H C t φ p‖ ≤ B := by
  obtain ⟨B, hB⟩ := sb7_Gr_bdd ht h
  refine ⟨max B 0, le_max_right _ _, fun p => ?_⟩
  unfold sb7_H
  split_ifs
  · exact (hB p).trans (le_max_left _ _)
  · simp

theorem sb7_H_eq {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t)
    (x : Euc d) : sb7_H C t φ (r, x) = gradient (propagatorW C r t φ) x := by
  simp [sb7_H, hr.2, sb7_Gr_eq hr]

theorem sb7_H_eq_zero {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {r : ℝ} (hr : t < r)
    (x : Euc d) : sb7_H C t φ (r, x) = 0 := by
  simp [sb7_H, not_le.2 hr]

/-- `noiseCovW` as an `L²(ν)` inner product of the cut-off gradients, `ν = ρ_r dx dr`. -/
theorem sb7_noiseCov_eq {C : WholeCoeff d} {q T : ℝ} (hT : 0 ≤ T)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ)) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) {φ ψ : Euc d → ℝ}
    (hφ : ∃ f, IsClassicalAdjointW C s φ f) (hψ : ∃ f, IsClassicalAdjointW C t ψ f) :
    noiseCovW C q s t φ ψ =
      2 * q * ∫ p, inner ℝ (sb7_H C s φ p) (sb7_H C t ψ p) ∂(u10_mu d T C.ρ) := by
  haveI := u10_isFinite hT hρ hρm
  unfold noiseCovW
  congr 1
  set m := min s t with hm
  have hmT : m ≤ T := (min_le_left _ _).trans hs.2
  obtain ⟨B₁, -, hB₁⟩ := sb7_H_bdd hs.1 hφ
  obtain ⟨B₂, -, hB₂⟩ := sb7_H_bdd ht.1 hψ
  have hgm : Measurable (fun p => inner ℝ (sb7_H C s φ p) (sb7_H C t ψ p)) :=
    (sb7_H_meas hs.1 hφ).inner (sb7_H_meas ht.1 hψ)
  have hgb : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x : Euc d,
      ‖inner ℝ (sb7_H C s φ (r, x)) (sb7_H C t ψ (r, x))‖ ≤ B₁ * B₂ := fun r _ x =>
    (norm_inner_le_norm _ _).trans (mul_le_mul (hB₁ (r, x)) (hB₂ (r, x)) (norm_nonneg _)
      ((norm_nonneg _).trans (hB₁ (r, x))))
  rw [(u10_integral_eq hT hρ hρm hgm hgb).2]
  have h1 : ∀ r ∈ Set.Icc (0 : ℝ) T,
      ∫ x, inner ℝ (sb7_H C s φ (r, x)) (sb7_H C t ψ (r, x)) * C.ρ r x =
        (Set.Icc (0 : ℝ) m).indicator (fun r => ∫ x, inner ℝ (gradient (propagatorW C r s φ) x)
          (gradient (propagatorW C r t ψ) x) * C.ρ r x) r := by
    intro r hr
    by_cases hrm : r ∈ Set.Icc (0 : ℝ) m
    · rw [Set.indicator_of_mem hrm]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      beta_reduce
      rw [sb7_H_eq ⟨hrm.1, hrm.2.trans (min_le_left _ _)⟩,
        sb7_H_eq ⟨hrm.1, hrm.2.trans (min_le_right _ _)⟩]
    · rw [Set.indicator_of_notMem hrm]
      have : ¬ r ≤ m := fun h => hrm ⟨hr.1, h⟩
      have h2 : s < r ∨ t < r := by
        by_contra hcon
        rw [not_or] at hcon
        exact this (le_min (not_lt.1 hcon.1) (not_lt.1 hcon.2))
      refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
      rcases h2 with h2 | h2
      · simp [sb7_H_eq_zero h2]
      · simp [sb7_H_eq_zero h2]
  rw [setIntegral_congr_fun measurableSet_Icc h1, setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_right.2 (Set.Icc_subset_Icc_right hmT)]

/-- Gram representation: the noise covariance matrix is positive semidefinite. -/
theorem sb7_noiseCov_psd {C : WholeCoeff d} {q T : ℝ} (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ)) {k : ℕ} (ts : Fin k → ℝ) (φ : Fin k → Euc d → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ a, ∃ f, IsClassicalAdjointW C (ts a) (φ a) f) :
    (Matrix.of fun a b => noiseCovW C q (ts a) (ts b) (φ a) (φ b) : Matrix (Fin k) (Fin k) ℝ).PosSemidef := by
  haveI := u10_isFinite hT hρ hρm
  have hmem : ∀ a, MemLp (sb7_H C (ts a) (φ a)) 2 (u10_mu d T C.ρ) := by
    intro a
    obtain ⟨B, -, hB⟩ := sb7_H_bdd (hts a).1 (hφ a)
    exact MemLp.of_bound (sb7_H_meas (hts a).1 (hφ a)).aestronglyMeasurable B
      (Eventually.of_forall hB)
  have h := HRS.A33.a33_gram_psd (fun a => Real.sqrt (2 * q) • (hmem a).toLp (sb7_H C (ts a) (φ a)))
  have e : (Matrix.of fun a b => noiseCovW C q (ts a) (ts b) (φ a) (φ b) : Matrix (Fin k) (Fin k) ℝ) =
      Matrix.of fun a b => inner ℝ (Real.sqrt (2 * q) • (hmem a).toLp (sb7_H C (ts a) (φ a)))
        (Real.sqrt (2 * q) • (hmem b).toLp (sb7_H C (ts b) (φ b))) := by
    ext a b
    simp only [Matrix.of_apply]
    rw [sb7_noiseCov_eq hT hρ hρm (hts a) (hts b) (hφ a) (hφ b), real_inner_smul_left,
      real_inner_smul_right, MeasureTheory.L2.inner_def, ← mul_assoc,
      show Real.sqrt (2 * q) * Real.sqrt (2 * q) = 2 * q from Real.mul_self_sqrt (by linarith)]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [(hmem a).coeFn_toLp, (hmem b).coeFn_toLp] with p h1 h2
    rw [h1, h2]
  rw [e]; exact h


/-- Second moments of a centered Gaussian vector. -/
theorem sb7_second_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {k : ℕ} {V : Ω → EuclideanSpace ℝ (Fin k)} (hV : Measurable V)
    {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef)
    (hlaw : law P V = multivariateGaussian 0 S) (i j : Fin k) :
    ∫ ω, V ω i * V ω j ∂P = S i j := by
  have hc := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin k))) hS i j
  have hm : ∀ l : Fin k, MemLp (fun x : EuclideanSpace ℝ (Fin k) => x l) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S) := fun l => by
    have := IsGaussian.memLp_dual (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S)
      (EuclideanSpace.proj l) 2 (by simp)
    simpa using this
  have hmean : ∀ l : Fin k, ∫ x, x l ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S) = 0 := by
    intro l
    have h1 := (measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin k)))
      hS (i := l)).map_eq
    have h2 : ∫ x, x l ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S) =
        ∫ y, y ∂((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S).map (fun x => x l)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    rw [h2, h1]
    simp
  rw [covariance_eq_sub (hm i) (hm j), hmean i, hmean j] at hc
  have e : ∫ ω, V ω i * V ω j ∂P =
      ∫ x, x i * x j ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S) := by
    rw [← hlaw]
    show _ = ∫ x, _ ∂(P.map V)
    rw [integral_map hV.aemeasurable (by fun_prop)]
  rw [e]
  simpa [Pi.mul_apply] using hc


/-! ### Cauchy-Schwarz -/

theorem sb7_cs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ∫ ω, |f ω * g ω| ∂P ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) * Real.sqrt (∫ ω, g ω ^ 2 ∂P) := by
  have hfa : MemLp (fun ω => |f ω|) 2 P := hf.abs
  have hga : MemLp (fun ω => |g ω|) 2 P := hg.abs
  have h1 : ∫ ω, |f ω * g ω| ∂P = inner ℝ (hfa.toLp (fun ω => |f ω|)) (hga.toLp (fun ω => |g ω|)) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hfa.coeFn_toLp, hga.coeFn_toLp] with ω a b
    rw [a, b, abs_mul]
    simp [mul_comm]
  have h2 : ‖hfa.toLp (fun ω => |f ω|)‖ = Real.sqrt (∫ ω, f ω ^ 2 ∂P) := by
    rw [← Real.sqrt_sq (norm_nonneg _), HRS.A33.a33_lp_norm_sq]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hfa.coeFn_toLp] with ω a
    rw [a]; simp [sq_abs]
  have h3 : ‖hga.toLp (fun ω => |g ω|)‖ = Real.sqrt (∫ ω, g ω ^ 2 ∂P) := by
    rw [← Real.sqrt_sq (norm_nonneg _), HRS.A33.a33_lp_norm_sq]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hga.coeFn_toLp] with ω a
    rw [a]; simp [sq_abs]
  rw [h1, ← h2, ← h3]
  exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)

/-- Cauchy-Schwarz for the integral over a finite measure. -/
theorem sb7_sq_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun a => f a ^ 2) μ) :
    (∫ a, f a ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ a, f a ^ 2 ∂μ := by
  rcases (measureReal_nonneg (μ := μ) (s := Set.univ)).eq_or_lt with h0 | hpos
  · have : μ = 0 := by
      have : μ Set.univ = 0 := by
        rw [Measure.real] at h0
        exact (ENNReal.toReal_eq_zero_iff _ |>.1 h0.symm).resolve_right (measure_ne_top _ _)
      exact Measure.measure_univ_eq_zero.1 this
    subst this
    simp
  · set c := (∫ a, f a ∂μ) / μ.real Set.univ with hc
    have h1 : 0 ≤ ∫ a, (f a - c) ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
    have h2 : ∫ a, (f a - c) ^ 2 ∂μ =
        ∫ a, f a ^ 2 ∂μ - 2 * c * ∫ a, f a ∂μ + c ^ 2 * μ.real Set.univ := by
      have : ∀ a, (f a - c) ^ 2 = f a ^ 2 - 2 * c * f a + c ^ 2 := fun a => by ring
      simp_rw [this]
      rw [integral_add (f := fun a => f a ^ 2 - 2 * c * f a) (g := fun _ => c ^ 2)
        (hf2.sub (hf.const_mul _)) (integrable_const _),
        integral_sub (f := fun a => f a ^ 2) (g := fun a => 2 * c * f a) hf2 (hf.const_mul _),
        integral_const_mul, integral_const]
      simp [Measure.real, smul_eq_mul]
      ring
    rw [h2] at h1
    have h3 : 2 * c * ∫ a, f a ∂μ - c ^ 2 * μ.real Set.univ =
        (∫ a, f a ∂μ) ^ 2 / μ.real Set.univ := by
      rw [hc]; field_simp; ring
    have h4 : (∫ a, f a ∂μ) ^ 2 / μ.real Set.univ ≤ ∫ a, f a ^ 2 ∂μ := by linarith
    rw [div_le_iff₀ hpos] at h4
    linarith

/-! ### Fubini for time integrals of an `L²`-bounded jointly measurable process -/

section Fub

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A jointly measurable process `G : ℝ × Ω → ℝ` that is `L²(P)`-bounded on a set `I` of times. -/
structure Sb7Noise (P : Measure Ω) (I : Set ℝ) (G : ℝ × Ω → ℝ) (V : ℝ) : Prop where
  meas : Measurable G
  memLp : ∀ r ∈ I, MemLp (fun ζ => G (r, ζ)) 2 P
  bound : ∀ r ∈ I, ∫ ζ, G (r, ζ) ^ 2 ∂P ≤ V

variable {I : Set ℝ} {G : ℝ × Ω → ℝ} {V : ℝ}

theorem Sb7Noise.integrable_mul (hG : Sb7Noise P I G V) (hI : MeasurableSet I)
    (hIv : volume I < ∞) {z : Ω → ℝ} (hzm : Measurable z) (hz : MemLp z 2 P) :
    Integrable (fun p : ℝ × Ω => G p * z p.2) ((volume.restrict I).prod P) := by
  haveI : IsFiniteMeasure (volume.restrict I) := ⟨by simpa [Measure.restrict_apply_univ] using hIv⟩
  have hfm : Measurable (fun p : ℝ × Ω => G p * z p.2) := hG.meas.mul (hzm.comp measurable_snd)
  rw [integrable_prod_iff hfm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem hI] with r hr
    exact (hG.memLp r hr).integrable_mul hz
  · refine Integrable.of_bound (C := Real.sqrt V * Real.sqrt (∫ ζ, z ζ ^ 2 ∂P)) ?_ ?_
    · exact (hfm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hI] with r hr
      have h1 : ∫ ζ, ‖G (r, ζ) * z ζ‖ ∂P ≤ Real.sqrt V * Real.sqrt (∫ ζ, z ζ ^ 2 ∂P) := by
        calc ∫ ζ, ‖G (r, ζ) * z ζ‖ ∂P = ∫ ζ, |G (r, ζ) * z ζ| ∂P := by simp [Real.norm_eq_abs]
          _ ≤ Real.sqrt (∫ ζ, G (r, ζ) ^ 2 ∂P) * Real.sqrt (∫ ζ, z ζ ^ 2 ∂P) :=
              sb7_cs (hG.memLp r hr) hz
          _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hG.bound r hr))
              (Real.sqrt_nonneg _)
      rw [Real.norm_of_nonneg (integral_nonneg fun ζ => norm_nonneg _)]
      exact h1

theorem Sb7Noise.integral_swap (hG : Sb7Noise P I G V) (hI : MeasurableSet I)
    (hIv : volume I < ∞) {z : Ω → ℝ} (hzm : Measurable z) (hz : MemLp z 2 P) :
    ∫ ζ, z ζ * (∫ r in I, G (r, ζ)) ∂P = ∫ r in I, ∫ ζ, z ζ * G (r, ζ) ∂P := by
  have hint := hG.integrable_mul hI hIv hzm hz
  have h1 : ∀ ζ, z ζ * (∫ r in I, G (r, ζ)) = ∫ r in I, G (r, ζ) * z ζ := by
    intro ζ; rw [integral_mul_const, mul_comm]
  simp_rw [h1]
  have := integral_integral_swap (μ := volume.restrict I) (ν := P)
    (f := fun r ζ => G (r, ζ) * z ζ) hint
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  simp [mul_comm]

theorem Sb7Noise.integrable_sq (hG : Sb7Noise P I G V) (hI : MeasurableSet I)
    (hIv : volume I < ∞) :
    Integrable (fun p : ℝ × Ω => G p ^ 2) ((volume.restrict I).prod P) := by
  haveI : IsFiniteMeasure (volume.restrict I) := ⟨by simpa [Measure.restrict_apply_univ] using hIv⟩
  have hfm : Measurable (fun p : ℝ × Ω => G p ^ 2) := hG.meas.pow_const 2
  rw [integrable_prod_iff hfm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem hI] with r hr
    exact (hG.memLp r hr).integrable_sq
  · refine Integrable.of_bound (C := V) ?_ ?_
    · exact (hfm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hI] with r hr
      have : ∫ ζ, ‖G (r, ζ) ^ 2‖ ∂P = ∫ ζ, G (r, ζ) ^ 2 ∂P :=
        integral_congr_ae (Eventually.of_forall fun ζ => by simp [Real.norm_eq_abs, sq_abs])
      rw [this, Real.norm_of_nonneg (integral_nonneg fun ζ => sq_nonneg _)]
      exact hG.bound r hr

theorem Sb7Noise.ae_integrable (hG : Sb7Noise P I G V) (hI : MeasurableSet I)
    (hIv : volume I < ∞) : ∀ᵐ ζ ∂P, Integrable (fun r => G (r, ζ)) (volume.restrict I) := by
  haveI : IsFiniteMeasure (volume.restrict I) := ⟨by simpa [Measure.restrict_apply_univ] using hIv⟩
  have h1 := (hG.integrable_sq hI hIv).prod_left_ae
  filter_upwards [h1] with ζ hζ
  exact ((memLp_two_iff_integrable_sq (hG.meas.comp measurable_prodMk_right).aestronglyMeasurable).2
    hζ).integrable (by norm_num)

theorem Sb7Noise.J_measurable (hG : Sb7Noise P I G V) :
    Measurable (fun ζ => ∫ r in I, G (r, ζ)) :=
  (hG.meas.stronglyMeasurable.integral_prod_left' (μ := volume.restrict I)).measurable

theorem Sb7Noise.J_memLp (hG : Sb7Noise P I G V) (hI : MeasurableSet I) (hIv : volume I < ∞) :
    MemLp (fun ζ => ∫ r in I, G (r, ζ)) 2 P := by
  haveI : IsFiniteMeasure (volume.restrict I) := ⟨by simpa [Measure.restrict_apply_univ] using hIv⟩
  rw [memLp_two_iff_integrable_sq hG.J_measurable.aestronglyMeasurable]
  have hΦ : Integrable (fun ζ => ∫ r in I, G (r, ζ) ^ 2) P :=
    (hG.integrable_sq hI hIv).integral_prod_right
  have h2 := (hG.integrable_sq hI hIv).prod_left_ae
  refine Integrable.mono' (hΦ.const_mul ((volume.restrict I).real Set.univ))
    (hG.J_measurable.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [h2, hG.ae_integrable hI hIv] with ζ h2ζ h1ζ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sb7_sq_integral_le h1ζ h2ζ

end Fub


/-! ### Abstract Fubini algebra for the Duhamel expansion; time integrals in the closed span -/

section RA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]

/-- inner product with a bounded measurable time integral -/
theorem sb7_inner_timeint {f : ℝ × α → E} (hf : Measurable f) {K : ℝ} (hK : ∀ q, ‖f q‖ ≤ K)
    {I : Set ℝ} (hIv : volume I < ∞) (c : E) (p : α) :
    inner ℝ c (∫ r in I, f (r, p)) = ∫ r in I, inner ℝ c (f (r, p)) := by
  haveI : IsFiniteMeasure (volume.restrict I) := ⟨by simpa [Measure.restrict_apply_univ] using hIv⟩
  have hi : Integrable (fun r => f (r, p)) (volume.restrict I) :=
    Integrable.of_bound (hf.comp measurable_prodMk_right).aestronglyMeasurable K
      (Eventually.of_forall fun r => hK _)
  exact (integral_inner hi c).symm

theorem sb7_RA {a₀ b₀ : α → E} {La Lb : ℝ × α → E} {K : ℝ}
    (ha₀ : Measurable a₀) (hb₀ : Measurable b₀) (hLa : Measurable La) (hLb : Measurable Lb)
    (ha₀K : ∀ p, ‖a₀ p‖ ≤ K) (hb₀K : ∀ p, ‖b₀ p‖ ≤ K) (hLaK : ∀ q, ‖La q‖ ≤ K)
    (hLbK : ∀ q, ‖Lb q‖ ≤ K) (hK0 : 0 ≤ K) {Ia Ib : Set ℝ} (hIav : volume Ia < ∞)
    (hIbv : volume Ib < ∞) :
    ∫ p, inner ℝ (a₀ p - ∫ r in Ia, La (r, p)) (b₀ p - ∫ u in Ib, Lb (u, p)) ∂ν =
      (∫ p, inner ℝ (a₀ p) (b₀ p) ∂ν) - (∫ u in Ib, ∫ p, inner ℝ (a₀ p) (Lb (u, p)) ∂ν)
      - (∫ r in Ia, ∫ p, inner ℝ (La (r, p)) (b₀ p) ∂ν)
      + (∫ u in Ib, ∫ r in Ia, ∫ p, inner ℝ (La (r, p)) (Lb (u, p)) ∂ν) := by
  haveI : IsFiniteMeasure (volume.restrict Ia) := ⟨by simpa [Measure.restrict_apply_univ] using hIav⟩
  haveI : IsFiniteMeasure (volume.restrict Ib) := ⟨by simpa [Measure.restrict_apply_univ] using hIbv⟩
  -- pointwise expansion
  have hpt : ∀ p, inner ℝ (a₀ p - ∫ r in Ia, La (r, p)) (b₀ p - ∫ u in Ib, Lb (u, p)) =
      inner ℝ (a₀ p) (b₀ p) - (∫ u in Ib, inner ℝ (a₀ p) (Lb (u, p)))
      - (∫ r in Ia, inner ℝ (La (r, p)) (b₀ p))
      + (∫ u in Ib, ∫ r in Ia, inner ℝ (La (r, p)) (Lb (u, p))) := by
    intro p
    have e1 : inner ℝ (a₀ p) (∫ u in Ib, Lb (u, p)) = ∫ u in Ib, inner ℝ (a₀ p) (Lb (u, p)) :=
      sb7_inner_timeint hLb hLbK hIbv _ p
    have e2 : inner ℝ (∫ r in Ia, La (r, p)) (b₀ p) = ∫ r in Ia, inner ℝ (La (r, p)) (b₀ p) := by
      rw [real_inner_comm, sb7_inner_timeint hLa hLaK hIav _ p]
      exact integral_congr_ae (Eventually.of_forall fun r => real_inner_comm _ _)
    have e3 : inner ℝ (∫ r in Ia, La (r, p)) (∫ u in Ib, Lb (u, p)) =
        ∫ u in Ib, ∫ r in Ia, inner ℝ (La (r, p)) (Lb (u, p)) := by
      rw [sb7_inner_timeint hLb hLbK hIbv _ p]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show inner ℝ (∫ r in Ia, La (r, p)) (Lb (u, p)) = _
      rw [real_inner_comm, sb7_inner_timeint hLa hLaK hIav _ p]
      exact integral_congr_ae (Eventually.of_forall fun r => real_inner_comm _ _)
    rw [inner_sub_left, inner_sub_right, inner_sub_right, e1, e2, e3]
    ring
  -- measurability and bounds of the four integrands
  set μa : Measure ℝ := volume.restrict Ia with hμa
  set μb : Measure ℝ := volume.restrict Ib with hμb
  have hAm : Measurable fun p => inner ℝ (a₀ p) (b₀ p) := ha₀.inner hb₀
  have hAb : ∀ p, ‖inner ℝ (a₀ p) (b₀ p)‖ ≤ K * K := fun p =>
    (norm_inner_le_norm _ _).trans (mul_le_mul (ha₀K p) (hb₀K p) (norm_nonneg _) hK0)
  have hBf : Measurable fun q : ℝ × α => inner ℝ (a₀ q.2) (Lb q) := (ha₀.comp measurable_snd).inner hLb
  have hBb : ∀ q : ℝ × α, ‖inner ℝ (a₀ q.2) (Lb q)‖ ≤ K * K := fun q =>
    (norm_inner_le_norm _ _).trans (mul_le_mul (ha₀K q.2) (hLbK q) (norm_nonneg _) hK0)
  have hCf : Measurable fun q : ℝ × α => inner ℝ (La q) (b₀ q.2) := hLa.inner (hb₀.comp measurable_snd)
  have hCb : ∀ q : ℝ × α, ‖inner ℝ (La q) (b₀ q.2)‖ ≤ K * K := fun q =>
    (norm_inner_le_norm _ _).trans (mul_le_mul (hLaK q) (hb₀K q.2) (norm_nonneg _) hK0)
  -- triple function (r, (u, p))
  have hFm : Measurable fun z : ℝ × ℝ × α => inner ℝ (La (z.1, z.2.2)) (Lb (z.2.1, z.2.2)) :=
    (hLa.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).inner
      (hLb.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
  have hFb : ∀ z : ℝ × ℝ × α, ‖inner ℝ (La (z.1, z.2.2)) (Lb (z.2.1, z.2.2))‖ ≤ K * K := fun z =>
    (norm_inner_le_norm _ _).trans (mul_le_mul (hLaK _) (hLbK _) (norm_nonneg _) hK0)
  -- the inner integral over r
  set Gf : ℝ × α → ℝ := fun q => ∫ r in Ia, inner ℝ (La (r, q.2)) (Lb (q.1, q.2)) ∂volume with hGf
  have hGm : Measurable Gf :=
    (hFm.stronglyMeasurable.integral_prod_left' (μ := μa)).measurable
  have hGb : ∀ q, ‖Gf q‖ ≤ K * K * μa.real Set.univ := fun q => by
    have := norm_integral_le_of_norm_le_const (μ := μa)
      (f := fun r => inner ℝ (La (r, q.2)) (Lb (q.1, q.2))) (C := K * K)
      (Eventually.of_forall fun r => hFb (r, q))
    simpa [Gf, hμa] using this
  have hBm : Measurable fun p => ∫ u in Ib, inner ℝ (a₀ p) (Lb (u, p)) :=
    (hBf.stronglyMeasurable.integral_prod_left' (μ := μb)).measurable
  have hBb' : ∀ p, ‖∫ u in Ib, inner ℝ (a₀ p) (Lb (u, p))‖ ≤ K * K * μb.real Set.univ := fun p => by
    have := norm_integral_le_of_norm_le_const (μ := μb)
      (f := fun u => inner ℝ (a₀ p) (Lb (u, p))) (C := K * K) (Eventually.of_forall fun u => hBb (u, p))
    simpa [hμb] using this
  have hCm : Measurable fun p => ∫ r in Ia, inner ℝ (La (r, p)) (b₀ p) :=
    (hCf.stronglyMeasurable.integral_prod_left' (μ := μa)).measurable
  have hCb' : ∀ p, ‖∫ r in Ia, inner ℝ (La (r, p)) (b₀ p)‖ ≤ K * K * μa.real Set.univ := fun p => by
    have := norm_integral_le_of_norm_le_const (μ := μa)
      (f := fun r => inner ℝ (La (r, p)) (b₀ p)) (C := K * K) (Eventually.of_forall fun r => hCb (r, p))
    simpa [hμa] using this
  have hDm : Measurable fun p => ∫ u in Ib, Gf (u, p) :=
    ((hGm.stronglyMeasurable).integral_prod_left' (μ := μb)).measurable
  have hDb : ∀ p, ‖∫ u in Ib, Gf (u, p)‖ ≤ K * K * μa.real Set.univ * μb.real Set.univ := fun p => by
    have := norm_integral_le_of_norm_le_const (μ := μb) (f := fun u => Gf (u, p))
      (C := K * K * μa.real Set.univ) (Eventually.of_forall fun u => hGb (u, p))
    simpa [hμb] using this
  have hint : ∀ {f : α → ℝ} {C : ℝ}, Measurable f → (∀ p, ‖f p‖ ≤ C) → Integrable f ν :=
    fun hf hC => Integrable.of_bound hf.aestronglyMeasurable _ (Eventually.of_forall hC)
  have hAi := hint hAm hAb
  have hBi := hint hBm hBb'
  have hCi := hint hCm hCb'
  have hDi := hint hDm hDb
  have hAB : Integrable (fun p => inner ℝ (a₀ p) (b₀ p) - ∫ u in Ib, inner ℝ (a₀ p) (Lb (u, p))) ν :=
    hAi.sub hBi
  have hABC : Integrable (fun p => inner ℝ (a₀ p) (b₀ p) - (∫ u in Ib, inner ℝ (a₀ p) (Lb (u, p)))
      - (∫ r in Ia, inner ℝ (La (r, p)) (b₀ p))) ν := hAB.sub hCi
  simp_rw [hpt]
  rw [integral_add hABC hDi, integral_sub hAB hCi, integral_sub hAi hBi]
  -- swap the orders of integration
  have eB : ∫ p, (∫ u in Ib, inner ℝ (a₀ p) (Lb (u, p))) ∂ν =
      ∫ u in Ib, ∫ p, inner ℝ (a₀ p) (Lb (u, p)) ∂ν := by
    refine integral_integral_swap (μ := ν) (ν := μb) (f := fun p u => inner ℝ (a₀ p) (Lb (u, p))) ?_
    refine Integrable.of_bound (C := K * K) ?_ (Eventually.of_forall fun z => hBb (z.2, z.1))
    exact (hBf.comp measurable_swap).aestronglyMeasurable
  have eC : ∫ p, (∫ r in Ia, inner ℝ (La (r, p)) (b₀ p)) ∂ν =
      ∫ r in Ia, ∫ p, inner ℝ (La (r, p)) (b₀ p) ∂ν := by
    refine integral_integral_swap (μ := ν) (ν := μa) (f := fun p r => inner ℝ (La (r, p)) (b₀ p)) ?_
    refine Integrable.of_bound (C := K * K) ?_ (Eventually.of_forall fun z => hCb (z.2, z.1))
    exact (hCf.comp measurable_swap).aestronglyMeasurable
  have eD : ∫ p, (∫ u in Ib, ∫ r in Ia, inner ℝ (La (r, p)) (Lb (u, p))) ∂ν =
      ∫ u in Ib, ∫ r in Ia, ∫ p, inner ℝ (La (r, p)) (Lb (u, p)) ∂ν := by
    have h1 : ∫ p, (∫ u in Ib, Gf (u, p)) ∂ν = ∫ u in Ib, ∫ p, Gf (u, p) ∂ν := by
      refine integral_integral_swap (μ := ν) (ν := μb) (f := fun p u => Gf (u, p)) ?_
      refine Integrable.of_bound (C := K * K * μa.real Set.univ) ?_
        (Eventually.of_forall fun z => hGb (z.2, z.1))
      exact (hGm.comp measurable_swap).aestronglyMeasurable
    refine h1.trans (integral_congr_ae (Eventually.of_forall fun u => ?_))
    show ∫ p, (∫ r in Ia, inner ℝ (La (r, p)) (Lb (u, p))) ∂ν =
      ∫ r in Ia, ∫ p, inner ℝ (La (r, p)) (Lb (u, p)) ∂ν
    refine integral_integral_swap (μ := ν) (ν := μa)
      (f := fun p r => inner ℝ (La (r, p)) (Lb (u, p))) ?_
    refine Integrable.of_bound (C := K * K) ?_ (Eventually.of_forall fun z => hFb (z.2, u, z.1))
    exact (hFm.comp ((measurable_snd.prodMk (measurable_const.prodMk measurable_fst)))).aestronglyMeasurable
  rw [eB, eC, eD]

end RA

section JMem

variable {Ω Z : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Θ : Type*} {η : Ω → Z} {X : Θ → Ω → ℝ} {cov : Θ → Θ → ℝ}

/-- The time integral of a noise process made of members of the family lies in the closed span. -/
theorem sb7_J_mem [MeasurableSpace Z] (hF : Sb7Fam P η X cov) {I : Set ℝ} {G : ℝ × Ω → ℝ} {V : ℝ}
    (hG : Sb7Noise P I G V) (hI : MeasurableSet I) (hIv : volume I < ∞)
    (hGX : ∀ r ∈ I, ∃ θ : Θ, ∀ ζ, G (r, ζ) = X θ ζ) :
    (hG.J_memLp hI hIv).toLp (fun ζ => ∫ r in I, G (r, ζ)) ∈ (Submodule.span ℝ
      (Set.range fun θ => (hF.memLp θ).toLp (X θ))).topologicalClosure := by
  set K := Submodule.span ℝ (Set.range fun θ => (hF.memLp θ).toLp (X θ)) with hK
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro z hz
  rw [Submodule.mem_orthogonal] at hz
  -- measurable representative of `z`
  set z' : Ω → ℝ := (Lp.aestronglyMeasurable z).mk _ with hz'
  have hz'm : Measurable z' := (Lp.aestronglyMeasurable z).stronglyMeasurable_mk.measurable
  have hzz' : (z : Ω → ℝ) =ᵐ[P] z' := (Lp.aestronglyMeasurable z).ae_eq_mk
  have hz'2 : MemLp z' 2 P := (Lp.memLp z).ae_eq hzz'
  have h1 : inner ℝ z ((hG.J_memLp hI hIv).toLp (fun ζ => ∫ r in I, G (r, ζ))) =
      ∫ ζ, z' ζ * (∫ r in I, G (r, ζ)) ∂P := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hG.J_memLp hI hIv).coeFn_toLp, hzz'] with ζ a b
    rw [a, b]
    simp [mul_comm]
  rw [h1, hG.integral_swap hI hIv hz'm hz'2]
  refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
  obtain ⟨θ, hθ⟩ := hGX r hr
  have h2 : ∫ ζ, z' ζ * G (r, ζ) ∂P = inner ℝ z ((hF.memLp θ).toLp (X θ)) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hF.memLp θ).coeFn_toLp, hzz'] with ζ a b
    rw [a, b, hθ]
    simp [mul_comm]
  rw [h2]
  rw [real_inner_comm]
  exact hz _ (Submodule.subset_span ⟨θ, rfl⟩)

end JMem


/-! ### The Gaussian family of the duality solution -/

/-- The index set of the noise family: times in `[0,T]` and smooth tests of `H^Γ`. -/
def Sb7Theta (d : ℕ) (Γ T : ℝ) : Type :=
  {θ : ℝ × (Euc d → ℝ) // θ.1 ∈ Set.Icc (0 : ℝ) T ∧ IsSobolevTest Γ θ.2}

/-- `X(t,φ) = ⟨φ, Y^t⟩ - A η₀(U^{0,t} φ)`. -/
def sb7_Xf {Ω : Type*} (C : WholeCoeff d) {Γ : ℝ} (A : ℝ) (η₀ : Ω → (Euc d → ℝ) → ℝ)
    (Y : ℝ → Ω → HNeg d Γ) (θ : ℝ × (Euc d → ℝ)) (ζ : Ω) : ℝ :=
  HNeg.pairing θ.2 (Y θ.1 ζ) - A * η₀ ζ (propagatorW C 0 θ.1 θ.2)

section Fam

variable {Γ : ℝ} {C : WholeCoeff d} {A q T : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {η₀ : Ω → (Euc d → ℝ) → ℝ} {Y : ℝ → Ω → HNeg d Γ}

theorem sb7_Xf_meas (hη₀m : Measurable η₀) (hYm : ∀ t, Measurable (Y t)) {θ : ℝ × (Euc d → ℝ)}
    (hθ : IsSobolevTest Γ θ.2) : Measurable (sb7_Xf C A η₀ Y θ) := by
  unfold sb7_Xf
  exact ((mhn_continuous_pairing hθ).measurable.comp (hYm _)).sub
    (((measurable_pi_apply _).comp hη₀m).const_mul A)

theorem sb7_fam (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ))
    (hcls : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ, IsSobolevTest Γ φ → ∃ f, IsClassicalAdjointW C t φ f)
    (hη₀m : Measurable η₀) (hdual : IsAdjointDualityLimitW P C Γ A q T η₀ Y) :
    Sb7Fam P η₀ (fun θ : Sb7Theta d Γ T => sb7_Xf C A η₀ Y θ.1)
      (fun θ θ' => noiseCovW C q θ.1.1 θ'.1.1 θ.1.2 θ'.1.2) := by
  have hfdd : ∀ (k : ℕ) (θ : Fin k → Sb7Theta d Γ T),
      IndepFun (fun ω => (WithLp.toLp 2 fun i => sb7_Xf C A η₀ Y (θ i).1 ω :
        EuclideanSpace ℝ (Fin k))) η₀ P ∧
      law P (fun ω => (WithLp.toLp 2 fun i => sb7_Xf C A η₀ Y (θ i).1 ω :
        EuclideanSpace ℝ (Fin k))) = multivariateGaussian 0
          (Matrix.of fun i j => noiseCovW C q (θ i).1.1 (θ j).1.1 (θ i).1.2 (θ j).1.2) :=
    fun k θ => hdual.gaussian_part k (fun i => (θ i).1.1) (fun i => (θ i).1.2)
      (fun i => (θ i).2.1) (fun i => (θ i).2.2)
  have hmeas : ∀ θ : Sb7Theta d Γ T, Measurable (sb7_Xf C A η₀ Y θ.1) := fun θ =>
    sb7_Xf_meas hη₀m hdual.meas θ.2.2
  have hpsd : ∀ (k : ℕ) (θ : Fin k → Sb7Theta d Γ T),
      (Matrix.of fun i j => noiseCovW C q (θ i).1.1 (θ j).1.1 (θ i).1.2 (θ j).1.2 :
        Matrix (Fin k) (Fin k) ℝ).PosSemidef := fun k θ =>
    sb7_noiseCov_psd hq hT hρ hρm (fun i => (θ i).1.1) (fun i => (θ i).1.2) (fun i => (θ i).2.1)
      (fun i => hcls _ (θ i).2.1 _ (θ i).2.2)
  have hvec : ∀ (k : ℕ) (θ : Fin k → Sb7Theta d Γ T), Measurable (fun ω =>
      (WithLp.toLp 2 fun i => sb7_Xf C A η₀ Y (θ i).1 ω : EuclideanSpace ℝ (Fin k))) :=
    fun k θ => (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun i => hmeas _)
  have hmemLp : ∀ θ : Sb7Theta d Γ T, MemLp (sb7_Xf C A η₀ Y θ.1) 2 P := by
    intro θ
    obtain ⟨-, hlaw⟩ := hfdd 1 (fun _ => θ)
    haveI : IsGaussian (P.map (fun ω => (WithLp.toLp 2 fun i : Fin 1 => sb7_Xf C A η₀ Y θ.1 ω :
        EuclideanSpace ℝ (Fin 1)))) := by
      have : law P (fun ω => (WithLp.toLp 2 fun i : Fin 1 => sb7_Xf C A η₀ Y θ.1 ω :
        EuclideanSpace ℝ (Fin 1))) = _ := hlaw
      rw [show P.map _ = law P _ from rfl, this]
      infer_instance
    have h1 : MemLp (fun ω => (WithLp.toLp 2 fun i : Fin 1 => sb7_Xf C A η₀ Y θ.1 ω :
        EuclideanSpace ℝ (Fin 1))) 2 P :=
      (IsGaussian.hasGaussianLaw (hvec 1 (fun _ => θ)).aemeasurable).memLp_two
    refine h1.mono (hmeas θ).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    have := PiLp.norm_apply_le (WithLp.toLp 2 fun i : Fin 1 => sb7_Xf C A η₀ Y θ.1 ω :
        EuclideanSpace ℝ (Fin 1)) 0
    simpa using this
  refine ⟨hmeas, hmemLp, fun θ θ' => ?_, hfdd⟩
  obtain ⟨-, hlaw⟩ := hfdd 2 (![θ, θ'])
  have := sb7_second_moment (hvec 2 ![θ, θ']) (hpsd 2 ![θ, θ']) hlaw 0 1
  simpa using this

end Fam

/-! ### The noise integrand of a weak test -/

/-- The noise integrand `g(r,ζ) = ⟨𝓛_rϑ, Y^r⟩ - A η₀(U^{0,r} 𝓛_rϑ)`, cut off to `r ∈ [0,T]`. -/
def sb7_g {Ω : Type*} (C : WholeCoeff d) {Γ : ℝ} (A T : ℝ) (η₀ : Ω → (Euc d → ℝ) → ℝ)
    (Y : ℝ → Ω → HNeg d Γ) (ϑ : Euc d → ℝ) (q : ℝ × Ω) : ℝ :=
  if q.1 ∈ Set.Icc (0 : ℝ) T then sb7_Xf C A η₀ Y (q.1, generatorW C q.1 ϑ) q.2 else 0

/-- The Duhamel gradient integrand `∇U^{w,r}(𝓛_rϑ)(x)` at `q = (r, (w, x))`, cut off to
`0 ≤ w ≤ r ≤ T`. -/
def sb7_Lam3 (C : WholeCoeff d) (T : ℝ) (ϑ : Euc d → ℝ) (q : ℝ × (ℝ × Euc d)) : Euc d :=
  if 0 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.1 ≤ T then
    gradient (propagatorW C q.2.1 q.1 (generatorW C q.1 ϑ)) q.2.2 else 0

theorem sb7_Lam3_bdd {C : WholeCoeff d} {T : ℝ} {ϑ : Euc d → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ T → ∀ x, ‖gradient (propagatorW C s r (generatorW C r ϑ)) x‖ ≤ B)
    (q : ℝ × (ℝ × Euc d)) : ‖sb7_Lam3 C T ϑ q‖ ≤ B := by
  unfold sb7_Lam3
  split_ifs with h
  · exact hB _ _ h.1 h.2.1 h.2.2 _
  · simpa using hB0

/-- The set of ν-a.e. points has `w ∈ [0,T]`. -/
theorem sb7_ae_nu {C : WholeCoeff d} (T : ℝ) :
    ∀ᵐ p ∂(u10_mu d T C.ρ), p.1 ∈ Set.Icc (0 : ℝ) T :=
  (withDensity_absolutelyContinuous _ _).ae_le (u10_ae_mem T)

section Fam2

variable {Γ : ℝ} {C : WholeCoeff d} {A q T : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {η₀ : Ω → (Euc d → ℝ) → ℝ} {Y : ℝ → Ω → HNeg d Γ}

theorem sb7_noise_theta (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ))
    (hcls : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ, IsSobolevTest Γ φ → ∃ f, IsClassicalAdjointW C t φ f)
    (hF : Sb7Fam P η₀ (fun θ : Sb7Theta d Γ T => sb7_Xf C A η₀ Y θ.1)
      (fun θ θ' => noiseCovW C q θ.1.1 θ'.1.1 θ.1.2 θ'.1.2))
    {ϑ : Euc d → ℝ} (hϑ : IsWeakTestFn Γ C T ϑ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ T → ∀ x,
      ‖gradient (propagatorW C s r (generatorW C r ϑ)) x‖ ≤ B)
    (hgm : Measurable (sb7_g C A T η₀ Y ϑ)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Sb7Noise P (Set.Icc (0 : ℝ) t) (sb7_g C A T η₀ Y ϑ) (2 * q * T * B ^ 2) := by
  haveI := u10_isFinite hT hρ hρm
  have hθ : ∀ r ∈ Set.Icc (0 : ℝ) t, ∃ θ : Sb7Theta d Γ T, θ.1 = (r, generatorW C r ϑ) ∧ ∀ ζ,
      sb7_g C A T η₀ Y ϑ (r, ζ) = sb7_Xf C A η₀ Y θ.1 ζ := by
    intro r hr
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
    refine ⟨⟨(r, generatorW C r ϑ), hrT, hϑ.2.2 r hrT⟩, rfl, fun ζ => ?_⟩
    simp [sb7_g, hrT]
  refine ⟨hgm, fun r hr => ?_, fun r hr => ?_⟩
  · obtain ⟨θ, -, hθ⟩ := hθ r hr
    simp_rw [hθ]
    exact hF.memLp θ
  · obtain ⟨θ, hθ1, hθ⟩ := hθ r hr
    simp_rw [hθ]
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
    have h1 : ∫ ζ, sb7_Xf C A η₀ Y θ.1 ζ ^ 2 ∂P = noiseCovW C q r r (generatorW C r ϑ)
        (generatorW C r ϑ) := by
      have := hF.cov_eq θ θ
      simp only [hθ1] at this ⊢
      simpa [sq] using this
    rw [h1]
    have hcl := hcls r hrT (generatorW C r ϑ) (hϑ.2.2 r hrT)
    rw [sb7_noiseCov_eq hT hρ hρm hrT hrT hcl hcl]
    have hbound : ∀ᵐ p ∂(u10_mu d T C.ρ),
        ‖inner ℝ (sb7_H C r (generatorW C r ϑ) p) (sb7_H C r (generatorW C r ϑ) p)‖ ≤ B ^ 2 := by
      filter_upwards [sb7_ae_nu (C := C) T] with p hp
      rw [real_inner_self_eq_norm_sq, Real.norm_of_nonneg (sq_nonneg _)]
      have : ‖sb7_H C r (generatorW C r ϑ) p‖ ≤ B := by
        unfold sb7_H
        split_ifs with hpr
        · have := sb7_Gr_eq (C := C) (t := r) (φ := generatorW C r ϑ) ⟨hp.1, hpr⟩ p.2
          have e : sb7_Gr C r (generatorW C r ϑ) p = gradient (propagatorW C p.1 r (generatorW C r ϑ)) p.2 := by
            simpa using this
          rw [e]
          exact hB _ _ hp.1 hpr hrT.2 _
        · simpa using hB0
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have h2 := norm_integral_le_of_norm_le_const (μ := u10_mu d T C.ρ) hbound
    rw [u10_real_univ hT hρ hρm] at h2
    have h3 : ∫ p, inner ℝ (sb7_H C r (generatorW C r ϑ) p) (sb7_H C r (generatorW C r ϑ) p)
        ∂(u10_mu d T C.ρ) ≤ B ^ 2 * T := (le_abs_self _).trans (by simpa using h2)
    calc 2 * q * ∫ p, inner ℝ (sb7_H C r (generatorW C r ϑ) p) (sb7_H C r (generatorW C r ϑ) p)
          ∂(u10_mu d T C.ρ) ≤ 2 * q * (B ^ 2 * T) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = 2 * q * T * B ^ 2 := by ring

theorem sb7_memCb_schwartz (ψ : SchwartzMap (Euc d) ℝ) : MemCb 1 (⇑ψ) :=
  ⟨ψ.smooth 1, fun j _ => ⟨SchwartzMap.seminorm ℝ 0 j ψ, by
    rintro _ ⟨x, rfl⟩
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ ψ j x⟩⟩

theorem sb7_M_eq (hT : 0 ≤ T) (hlin : IsLinearOnCb1 P η₀)
    (horbit : ∀ᵐ ζ ∂P, ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∀ t ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun r => η₀ ζ (propagatorW C 0 r (generatorW C r ϑ))) (Set.Icc (0 : ℝ) t) ∧
      η₀ ζ (fun x => ∫ r in Set.Icc (0 : ℝ) t, propagatorW C 0 r (generatorW C r ϑ) x) =
        ∫ r in Set.Icc (0 : ℝ) t, η₀ ζ (propagatorW C 0 r (generatorW C r ϑ)))
    {ϑ : Euc d → ℝ} (hϑ : IsWeakTestFn Γ C T ϑ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hcb : MemCb 1 (propagatorW C 0 t ϑ))
    (hduh0 : ∀ x, propagatorW C 0 t ϑ x - ϑ x =
      ∫ r in Set.Icc (0 : ℝ) t, propagatorW C 0 r (generatorW C r ϑ) x)
    {V : ℝ} (hG : Sb7Noise P (Set.Icc (0 : ℝ) t) (sb7_g C A T η₀ Y ϑ) V) :
    ∀ᵐ ζ ∂P, HNeg.pairing ϑ (Y t ζ) - A * η₀ ζ ϑ -
        ∫ r in Set.Icc (0 : ℝ) t, HNeg.pairing (generatorW C r ϑ) (Y r ζ) =
      sb7_Xf C A η₀ Y (t, ϑ) ζ - ∫ r in Set.Icc (0 : ℝ) t, sb7_g C A T η₀ Y ϑ (r, ζ) := by
  have hI : MeasurableSet (Set.Icc (0 : ℝ) t) := measurableSet_Icc
  have hIv : volume (Set.Icc (0 : ℝ) t) < ∞ := by simp
  obtain ⟨ψ, hψ⟩ := hϑ.1
  have hcbϑ : MemCb 1 ϑ := hψ ▸ sb7_memCb_schwartz ψ
  filter_upwards [horbit, hlin, hG.ae_integrable hI hIv] with ζ h1 h2 h3
  obtain ⟨h1a, h1b⟩ := h1 ϑ hϑ t ht
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) t, HNeg.pairing (generatorW C r ϑ) (Y r ζ) =
      sb7_g C A T η₀ Y ϑ (r, ζ) + A * η₀ ζ (propagatorW C 0 r (generatorW C r ϑ)) := by
    intro r hr
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
    simp [sb7_g, sb7_Xf, hrT]
  rw [setIntegral_congr_fun hI hpt, integral_add h3 (h1a.const_mul A), integral_const_mul, h1b.symm]
  have e : (fun x => ∫ r in Set.Icc (0 : ℝ) t, propagatorW C 0 r (generatorW C r ϑ) x) =
      propagatorW C 0 t ϑ + (-1 : ℝ) • ϑ := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hduh0 x]; ring
  rw [e, h2 _ _ _ hcb hcbϑ]
  unfold sb7_Xf
  ring

theorem sb7_Lam3_eq_H {C : WholeCoeff d} {T : ℝ} {ϑ : Euc d → ℝ} {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ p ∂(u10_mu d T C.ρ), sb7_Lam3 C T ϑ (r, p) = sb7_H C r (generatorW C r ϑ) p := by
  filter_upwards [sb7_ae_nu (C := C) T] with p hp
  obtain ⟨w, x⟩ := p
  unfold sb7_Lam3 sb7_H
  by_cases hwr : w ≤ r
  · rw [if_pos ⟨hp.1, hwr, hr.2⟩, if_pos hwr]
    exact (sb7_Gr_eq ⟨hp.1, hwr⟩ x).symm
  · rw [if_neg (fun h => hwr h.2.1), if_neg hwr]

theorem sb7_duhamel_pt {C : WholeCoeff d} {T : ℝ} {ϑ : Euc d → ℝ} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hduh : ∀ w : ℝ, 0 ≤ w → w ≤ t → ∀ x,
      gradient (propagatorW C w t ϑ) x - gradient ϑ x =
        ∫ r in Set.Icc w t, gradient (propagatorW C w r (generatorW C r ϑ)) x)
    {w : ℝ} (hw : 0 ≤ w) (x : Euc d) :
    sb7_H C t ϑ (w, x) - ∫ r in Set.Icc (0 : ℝ) t, sb7_Lam3 C T ϑ (r, (w, x)) =
      if w ≤ t then gradient ϑ x else 0 := by
  by_cases hwt : w ≤ t
  · have h1 : ∫ r in Set.Icc (0 : ℝ) t, sb7_Lam3 C T ϑ (r, (w, x)) =
        ∫ r in Set.Icc w t, gradient (propagatorW C w r (generatorW C r ϑ)) x := by
      have e : ∀ r ∈ Set.Icc (0 : ℝ) t, sb7_Lam3 C T ϑ (r, (w, x)) =
          (Set.Ici w).indicator (fun r => gradient (propagatorW C w r (generatorW C r ϑ)) x) r := by
        intro r hr
        unfold sb7_Lam3
        by_cases hwr : w ≤ r
        · rw [if_pos ⟨hw, hwr, hr.2.trans ht.2⟩, Set.indicator_of_mem (show r ∈ Set.Ici w from hwr)]
        · rw [if_neg (fun h => hwr h.2.1), Set.indicator_of_notMem (show r ∉ Set.Ici w from hwr)]
      have hset : Set.Icc (0 : ℝ) t ∩ Set.Ici w = Set.Icc w t := by
        ext r
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h3, h2⟩; exact ⟨⟨hw.trans h3, h2⟩, h3⟩
      rw [setIntegral_congr_fun measurableSet_Icc e, setIntegral_indicator measurableSet_Ici, hset]
    rw [h1, ← hduh w hw hwt x, sb7_H_eq ⟨hw, hwt⟩ x, if_pos hwt]
    exact sub_sub_cancel _ _
  · have h1 : ∫ r in Set.Icc (0 : ℝ) t, sb7_Lam3 C T ϑ (r, (w, x)) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
      unfold sb7_Lam3
      rw [if_neg]
      intro h
      exact hwt (h.2.1.trans hr.2)
    rw [h1, if_neg hwt, sb7_H_eq_zero (not_le.1 hwt)]
    simp

/-- Bundle of the regularity hypotheses on a weak test `ϑ` (used in the weak form). -/
structure Sb7WT {Ω : Type*} [MeasurableSpace Ω] (Γ : ℝ) (C : WholeCoeff d) (A T : ℝ)
    (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → HNeg d Γ) (ϑ : Euc d → ℝ) : Prop where
  weak : IsWeakTestFn Γ C T ϑ
  duh : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
    (∃ B : ℝ, ∀ r ∈ Set.Icc s t, ∀ x, ‖gradient (propagatorW C s r (generatorW C r ϑ)) x‖ ≤ B) ∧
    ∀ x, propagatorW C s t ϑ x - ϑ x = ∫ r in Set.Icc s t, propagatorW C s r (generatorW C r ϑ) x ∧
      gradient (propagatorW C s t ϑ) x - gradient ϑ x =
        ∫ r in Set.Icc s t, gradient (propagatorW C s r (generatorW C r ϑ)) x
  bd : ∃ B : ℝ, 0 ≤ B ∧ ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ T → ∀ x,
    ‖gradient (propagatorW C s r (generatorW C r ϑ)) x‖ ≤ B
  Lm : Measurable (sb7_Lam3 C T ϑ)
  gm : Measurable (sb7_g C A T η₀ Y ϑ)

theorem sb7_timeint_meas {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {α : Type*} [MeasurableSpace α]
    {f : ℝ × α → E} (hf : Measurable f) (I : Set ℝ) : Measurable fun p => ∫ r in I, f (r, p) :=
  (hf.stronglyMeasurable.integral_prod_left' (μ := volume.restrict I)).measurable

theorem sb7_timeint_bdd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α : Type*}
    {f : ℝ × α → E} {K : ℝ} (hK : ∀ q, ‖f q‖ ≤ K) (I : Set ℝ) (hIv : volume I < ∞) (p : α) :
    ‖∫ r in I, f (r, p)‖ ≤ K * (volume.restrict I).real Set.univ := by
  haveI : IsFiniteMeasure (volume.restrict I) := ⟨by simpa [Measure.restrict_apply_univ] using hIv⟩
  have := norm_integral_le_of_norm_le_const (μ := volume.restrict I) (f := fun r => f (r, p))
    (C := K) (Eventually.of_forall fun r => hK _)
  simpa [mul_comm] using this

end Fam2



section Expand

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem sb7_expand {Ia Ib : Set ℝ} {Ga Gb : ℝ × Ω → ℝ} {Va Vb : ℝ}
    (hGa : Sb7Noise P Ia Ga Va) (hGb : Sb7Noise P Ib Gb Vb)
    (hIa : MeasurableSet Ia) (hIb : MeasurableSet Ib) (hIav : volume Ia < ∞) (hIbv : volume Ib < ∞)
    {Xa Xb : Ω → ℝ} (hXam : Measurable Xa) (hXbm : Measurable Xb) (hXa : MemLp Xa 2 P)
    (hXb : MemLp Xb 2 P) :
    ∫ ζ, (Xa ζ - ∫ r in Ia, Ga (r, ζ)) * (Xb ζ - ∫ u in Ib, Gb (u, ζ)) ∂P =
      (∫ ζ, Xa ζ * Xb ζ ∂P) - (∫ u in Ib, ∫ ζ, Xa ζ * Gb (u, ζ) ∂P)
      - (∫ r in Ia, ∫ ζ, Xb ζ * Ga (r, ζ) ∂P)
      + (∫ u in Ib, ∫ r in Ia, ∫ ζ, Gb (u, ζ) * Ga (r, ζ) ∂P) := by
  have hJa2 := hGa.J_memLp hIa hIav
  have hJb2 := hGb.J_memLp hIb hIbv
  have hJam := hGa.J_measurable
  have hJbm := hGb.J_measurable
  have i1 : Integrable (fun ζ => Xa ζ * Xb ζ) P := hXa.integrable_mul hXb
  have i2 : Integrable (fun ζ => Xa ζ * ∫ u in Ib, Gb (u, ζ)) P := hXa.integrable_mul hJb2
  have i3 : Integrable (fun ζ => (∫ r in Ia, Ga (r, ζ)) * Xb ζ) P := hJa2.integrable_mul hXb
  have i4 : Integrable (fun ζ => (∫ r in Ia, Ga (r, ζ)) * ∫ u in Ib, Gb (u, ζ)) P :=
    hJa2.integrable_mul hJb2
  have e : ∀ ζ, (Xa ζ - ∫ r in Ia, Ga (r, ζ)) * (Xb ζ - ∫ u in Ib, Gb (u, ζ)) =
      Xa ζ * Xb ζ - Xa ζ * (∫ u in Ib, Gb (u, ζ)) - (∫ r in Ia, Ga (r, ζ)) * Xb ζ +
        (∫ r in Ia, Ga (r, ζ)) * ∫ u in Ib, Gb (u, ζ) := fun ζ => by ring
  have i12 : Integrable (fun ζ => Xa ζ * Xb ζ - Xa ζ * (∫ u in Ib, Gb (u, ζ))) P := i1.sub i2
  have i123 : Integrable (fun ζ => Xa ζ * Xb ζ - Xa ζ * (∫ u in Ib, Gb (u, ζ)) -
      (∫ r in Ia, Ga (r, ζ)) * Xb ζ) P := i12.sub i3
  simp_rw [e]
  rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2]
  -- the three Fubini identities
  have f2 : ∫ ζ, Xa ζ * (∫ u in Ib, Gb (u, ζ)) ∂P = ∫ u in Ib, ∫ ζ, Xa ζ * Gb (u, ζ) ∂P :=
    hGb.integral_swap hIb hIbv hXam hXa
  have f3 : ∫ ζ, (∫ r in Ia, Ga (r, ζ)) * Xb ζ ∂P = ∫ r in Ia, ∫ ζ, Xb ζ * Ga (r, ζ) ∂P := by
    simp_rw [mul_comm (∫ r in Ia, Ga (r, _)) _]
    exact hGa.integral_swap hIa hIav hXbm hXb
  have f4 : ∫ ζ, (∫ r in Ia, Ga (r, ζ)) * (∫ u in Ib, Gb (u, ζ)) ∂P =
      ∫ u in Ib, ∫ r in Ia, ∫ ζ, Gb (u, ζ) * Ga (r, ζ) ∂P := by
    rw [hGb.integral_swap hIb hIbv hJam hJa2]
    refine setIntegral_congr_fun hIb fun u hu => ?_
    have hum : Measurable (fun ζ => Gb (u, ζ)) := hGb.meas.comp measurable_prodMk_left
    have := hGa.integral_swap hIa hIav hum (hGb.memLp u hu)
    rw [show (fun ζ => (∫ r in Ia, Ga (r, ζ)) * Gb (u, ζ)) = fun ζ => Gb (u, ζ) * ∫ r in Ia, Ga (r, ζ)
      from funext fun ζ => mul_comm _ _]
    exact this
  rw [f2, f3, f4]

end Expand

section Cov

variable {Γ : ℝ} {C : WholeCoeff d} {A q T : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {η₀ : Ω → (Euc d → ℝ) → ℝ} {Y : ℝ → Ω → HNeg d Γ}

/-- The cut-off Duhamel remainder `D_ϑ(w,x) = H_t(w,x) - ∫_0^t Λ_r(w,x) dr`. -/
theorem sb7_D_int (hT : 0 ≤ T) (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ))
    (hcls : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ, IsSobolevTest Γ φ → ∃ f, IsClassicalAdjointW C t φ f)
    {ϑa ϑb : Euc d → ℝ} (ha : Sb7WT Γ C A T η₀ Y ϑa) (hb : Sb7WT Γ C A T η₀ Y ϑb)
    {ta tb : ℝ} (hta : ta ∈ Set.Icc (0 : ℝ) T) (htb : tb ∈ Set.Icc (0 : ℝ) T) :
    ∫ p, inner ℝ (sb7_H C ta ϑa p - ∫ r in Set.Icc (0 : ℝ) ta, sb7_Lam3 C T ϑa (r, p))
        (sb7_H C tb ϑb p - ∫ r in Set.Icc (0 : ℝ) tb, sb7_Lam3 C T ϑb (r, p)) ∂(u10_mu d T C.ρ) =
      ∫ r in Set.Icc (0 : ℝ) (min ta tb), ∫ x, inner ℝ (gradient ϑa x) (gradient ϑb x) * C.ρ r x := by
  haveI := u10_isFinite hT hρ hρm
  obtain ⟨Ba, hBa0, hBa⟩ := ha.bd
  obtain ⟨Bb, hBb0, hBb⟩ := hb.bd
  have hcla := hcls ta hta ϑa ha.weak.2.1
  have hclb := hcls tb htb ϑb hb.weak.2.1
  obtain ⟨Ka, -, hKa⟩ := sb7_H_bdd hta.1 hcla
  obtain ⟨Kb, -, hKb⟩ := sb7_H_bdd htb.1 hclb
  set m := min ta tb with hm
  have hmT : m ≤ T := (min_le_left _ _).trans hta.2
  have hIta : volume (Set.Icc (0 : ℝ) ta) < ∞ := by simp
  have hItb : volume (Set.Icc (0 : ℝ) tb) < ∞ := by simp
  have hDam : Measurable fun p => sb7_H C ta ϑa p - ∫ r in Set.Icc (0 : ℝ) ta, sb7_Lam3 C T ϑa (r, p) :=
    (sb7_H_meas hta.1 hcla).sub (sb7_timeint_meas ha.Lm _)
  have hDbm : Measurable fun p => sb7_H C tb ϑb p - ∫ r in Set.Icc (0 : ℝ) tb, sb7_Lam3 C T ϑb (r, p) :=
    (sb7_H_meas htb.1 hclb).sub (sb7_timeint_meas hb.Lm _)
  have hDab : ∀ p, ‖sb7_H C ta ϑa p - ∫ r in Set.Icc (0 : ℝ) ta, sb7_Lam3 C T ϑa (r, p)‖ ≤
      Ka + Ba * (volume.restrict (Set.Icc (0 : ℝ) ta)).real Set.univ := fun p =>
    (norm_sub_le _ _).trans (add_le_add (hKa p) (sb7_timeint_bdd (sb7_Lam3_bdd hBa0 hBa) _ hIta p))
  have hDbb : ∀ p, ‖sb7_H C tb ϑb p - ∫ r in Set.Icc (0 : ℝ) tb, sb7_Lam3 C T ϑb (r, p)‖ ≤
      Kb + Bb * (volume.restrict (Set.Icc (0 : ℝ) tb)).real Set.univ := fun p =>
    (norm_sub_le _ _).trans (add_le_add (hKb p) (sb7_timeint_bdd (sb7_Lam3_bdd hBb0 hBb) _ hItb p))
  have hgm : Measurable fun p => inner ℝ
      (sb7_H C ta ϑa p - ∫ r in Set.Icc (0 : ℝ) ta, sb7_Lam3 C T ϑa (r, p))
      (sb7_H C tb ϑb p - ∫ r in Set.Icc (0 : ℝ) tb, sb7_Lam3 C T ϑb (r, p)) := hDam.inner hDbm
  have hgb : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x : Euc d, ‖inner ℝ
      (sb7_H C ta ϑa (r, x) - ∫ r' in Set.Icc (0 : ℝ) ta, sb7_Lam3 C T ϑa (r', (r, x)))
      (sb7_H C tb ϑb (r, x) - ∫ r' in Set.Icc (0 : ℝ) tb, sb7_Lam3 C T ϑb (r', (r, x)))‖ ≤
      (Ka + Ba * (volume.restrict (Set.Icc (0 : ℝ) ta)).real Set.univ) *
        (Kb + Bb * (volume.restrict (Set.Icc (0 : ℝ) tb)).real Set.univ) := fun r _ x =>
    (norm_inner_le_norm _ _).trans (mul_le_mul (hDab (r, x)) (hDbb (r, x)) (norm_nonneg _)
      ((norm_nonneg _).trans (hDab (r, x))))
  rw [(u10_integral_eq hT hρ hρm hgm hgb).2]
  have hDa : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x : Euc d,
      sb7_H C ta ϑa (r, x) - ∫ r' in Set.Icc (0 : ℝ) ta, sb7_Lam3 C T ϑa (r', (r, x)) =
        if r ≤ ta then gradient ϑa x else 0 := fun r hr x =>
    sb7_duhamel_pt hta (fun w hw hwt x => ((ha.duh w ta hw hwt hta.2).2 x).2) hr.1 x
  have hDb : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x : Euc d,
      sb7_H C tb ϑb (r, x) - ∫ r' in Set.Icc (0 : ℝ) tb, sb7_Lam3 C T ϑb (r', (r, x)) =
        if r ≤ tb then gradient ϑb x else 0 := fun r hr x =>
    sb7_duhamel_pt htb (fun w hw hwt x => ((hb.duh w tb hw hwt htb.2).2 x).2) hr.1 x
  have h1 : ∀ r ∈ Set.Icc (0 : ℝ) T,
      ∫ x, inner ℝ (sb7_H C ta ϑa (r, x) - ∫ r' in Set.Icc (0 : ℝ) ta, sb7_Lam3 C T ϑa (r', (r, x)))
        (sb7_H C tb ϑb (r, x) - ∫ r' in Set.Icc (0 : ℝ) tb, sb7_Lam3 C T ϑb (r', (r, x))) *
          C.ρ r x =
        (Set.Icc (0 : ℝ) m).indicator (fun r => ∫ x, inner ℝ (gradient ϑa x) (gradient ϑb x) *
          C.ρ r x) r := by
    intro r hr
    by_cases hrm : r ∈ Set.Icc (0 : ℝ) m
    · rw [Set.indicator_of_mem hrm]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      beta_reduce
      rw [hDa r hr x, hDb r hr x, if_pos (hrm.2.trans (min_le_left _ _)),
        if_pos (hrm.2.trans (min_le_right _ _))]
    · rw [Set.indicator_of_notMem hrm]
      have : ¬ r ≤ m := fun h => hrm ⟨hr.1, h⟩
      have h2 : ta < r ∨ tb < r := by
        by_contra hcon
        rw [not_or] at hcon
        exact this (le_min (not_lt.1 hcon.1) (not_lt.1 hcon.2))
      refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
      beta_reduce
      rw [hDa r hr x, hDb r hr x]
      rcases h2 with h2 | h2
      · simp [not_le.2 h2]
      · simp [not_le.2 h2]
  rw [setIntegral_congr_fun measurableSet_Icc h1, setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_right.2 (Set.Icc_subset_Icc_right hmT)]

theorem sb7_cov_M (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ))
    (hcls : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ, IsSobolevTest Γ φ → ∃ f, IsClassicalAdjointW C t φ f)
    (hF : Sb7Fam P η₀ (fun θ : Sb7Theta d Γ T => sb7_Xf C A η₀ Y θ.1)
      (fun θ θ' => noiseCovW C q θ.1.1 θ'.1.1 θ.1.2 θ'.1.2))
    {ϑa ϑb : Euc d → ℝ} (ha : Sb7WT Γ C A T η₀ Y ϑa) (hb : Sb7WT Γ C A T η₀ Y ϑb)
    {ta tb : ℝ} (hta : ta ∈ Set.Icc (0 : ℝ) T) (htb : tb ∈ Set.Icc (0 : ℝ) T) :
    ∫ ζ, (sb7_Xf C A η₀ Y (ta, ϑa) ζ - ∫ r in Set.Icc (0 : ℝ) ta, sb7_g C A T η₀ Y ϑa (r, ζ)) *
        (sb7_Xf C A η₀ Y (tb, ϑb) ζ - ∫ r in Set.Icc (0 : ℝ) tb, sb7_g C A T η₀ Y ϑb (r, ζ)) ∂P =
      2 * q * ∫ r in Set.Icc (0 : ℝ) (min ta tb), ∫ x,
        inner ℝ (gradient ϑa x) (gradient ϑb x) * C.ρ r x := by
  haveI := u10_isFinite hT hρ hρm
  obtain ⟨Ba, hBa0, hBa⟩ := ha.bd
  obtain ⟨Bb, hBb0, hBb⟩ := hb.bd
  have hGa := sb7_noise_theta hq hT hρ hρm hcls hF ha.weak hBa0 hBa ha.gm hta
  have hGb := sb7_noise_theta hq hT hρ hρm hcls hF hb.weak hBb0 hBb hb.gm htb
  have hIta : volume (Set.Icc (0 : ℝ) ta) < ∞ := by simp
  have hItb : volume (Set.Icc (0 : ℝ) tb) < ∞ := by simp
  set θa : Sb7Theta d Γ T := ⟨(ta, ϑa), hta, ha.weak.2.1⟩ with hθa
  set θb : Sb7Theta d Γ T := ⟨(tb, ϑb), htb, hb.weak.2.1⟩ with hθb
  rw [sb7_expand hGa hGb measurableSet_Icc measurableSet_Icc hIta hItb (hF.meas θa) (hF.meas θb)
    (hF.memLp θa) (hF.memLp θb)]
  -- identification of the covariances
  have hθ : ∀ {ϑ : Euc d → ℝ}, Sb7WT Γ C A T η₀ Y ϑ → ∀ r ∈ Set.Icc (0 : ℝ) T,
      ∃ θ : Sb7Theta d Γ T, θ.1 = (r, generatorW C r ϑ) ∧
        ∀ ζ, sb7_g C A T η₀ Y ϑ (r, ζ) = sb7_Xf C A η₀ Y θ.1 ζ := by
    intro ϑ h r hr
    refine ⟨⟨(r, generatorW C r ϑ), hr, h.weak.2.2 r hr⟩, rfl, fun ζ => ?_⟩
    simp [sb7_g, hr]
  have c1 : ∫ ζ, sb7_Xf C A η₀ Y (ta, ϑa) ζ * sb7_Xf C A η₀ Y (tb, ϑb) ζ ∂P =
      noiseCovW C q ta tb ϑa ϑb := hF.cov_eq θa θb
  have c2 : ∀ u ∈ Set.Icc (0 : ℝ) tb, ∫ ζ, sb7_Xf C A η₀ Y (ta, ϑa) ζ * sb7_g C A T η₀ Y ϑb (u, ζ) ∂P =
      noiseCovW C q ta u ϑa (generatorW C u ϑb) := by
    intro u hu
    obtain ⟨θ, hθ1, hθ2⟩ := hθ hb u ⟨hu.1, hu.2.trans htb.2⟩
    simp_rw [hθ2]
    have := hF.cov_eq θa θ
    simp only [hθ1, hθa] at this ⊢
    exact this
  have c3 : ∀ r ∈ Set.Icc (0 : ℝ) ta, ∫ ζ, sb7_Xf C A η₀ Y (tb, ϑb) ζ * sb7_g C A T η₀ Y ϑa (r, ζ) ∂P =
      noiseCovW C q tb r ϑb (generatorW C r ϑa) := by
    intro r hr
    obtain ⟨θ, hθ1, hθ2⟩ := hθ ha r ⟨hr.1, hr.2.trans hta.2⟩
    simp_rw [hθ2]
    have := hF.cov_eq θb θ
    simp only [hθ1, hθb] at this ⊢
    exact this
  have c4 : ∀ u ∈ Set.Icc (0 : ℝ) tb, ∀ r ∈ Set.Icc (0 : ℝ) ta,
      ∫ ζ, sb7_g C A T η₀ Y ϑb (u, ζ) * sb7_g C A T η₀ Y ϑa (r, ζ) ∂P =
        noiseCovW C q u r (generatorW C u ϑb) (generatorW C r ϑa) := by
    intro u hu r hr
    obtain ⟨θ, hθ1, hθ2⟩ := hθ hb u ⟨hu.1, hu.2.trans htb.2⟩
    obtain ⟨θ', hθ1', hθ2'⟩ := hθ ha r ⟨hr.1, hr.2.trans hta.2⟩
    simp_rw [hθ2, hθ2']
    have := hF.cov_eq θ θ'
    simp only [hθ1, hθ1'] at this ⊢
    exact this
  -- the ν-integral forms
  have hcla := hcls ta hta ϑa ha.weak.2.1
  have hclb := hcls tb htb ϑb hb.weak.2.1
  obtain ⟨Ka, hKa0, hKa⟩ := sb7_H_bdd hta.1 hcla
  obtain ⟨Kb, hKb0, hKb⟩ := sb7_H_bdd htb.1 hclb
  have hLH : ∀ {ϑ : Euc d → ℝ} (r : ℝ), r ∈ Set.Icc (0 : ℝ) T →
      ∀ᵐ p ∂(u10_mu d T C.ρ), sb7_Lam3 C T ϑ (r, p) = sb7_H C r (generatorW C r ϑ) p :=
    fun r hr => sb7_Lam3_eq_H hr
  have e1 : noiseCovW C q ta tb ϑa ϑb =
      2 * q * ∫ p, inner ℝ (sb7_H C ta ϑa p) (sb7_H C tb ϑb p) ∂(u10_mu d T C.ρ) :=
    sb7_noiseCov_eq hT hρ hρm hta htb hcla hclb
  have e2 : ∀ u ∈ Set.Icc (0 : ℝ) tb, noiseCovW C q ta u ϑa (generatorW C u ϑb) =
      2 * q * ∫ p, inner ℝ (sb7_H C ta ϑa p) (sb7_Lam3 C T ϑb (u, p)) ∂(u10_mu d T C.ρ) := by
    intro u hu
    have huT : u ∈ Set.Icc (0 : ℝ) T := ⟨hu.1, hu.2.trans htb.2⟩
    rw [sb7_noiseCov_eq hT hρ hρm hta huT hcla (hcls u huT _ (hb.weak.2.2 u huT))]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hLH (ϑ := ϑb) u huT] with p hp
    rw [hp]
  have e3 : ∀ r ∈ Set.Icc (0 : ℝ) ta, noiseCovW C q tb r ϑb (generatorW C r ϑa) =
      2 * q * ∫ p, inner ℝ (sb7_Lam3 C T ϑa (r, p)) (sb7_H C tb ϑb p) ∂(u10_mu d T C.ρ) := by
    intro r hr
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans hta.2⟩
    rw [sb7_noiseCov_eq hT hρ hρm htb hrT hclb (hcls r hrT _ (ha.weak.2.2 r hrT))]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hLH (ϑ := ϑa) r hrT] with p hp
    rw [hp, real_inner_comm]
  have e4 : ∀ u ∈ Set.Icc (0 : ℝ) tb, ∀ r ∈ Set.Icc (0 : ℝ) ta,
      noiseCovW C q u r (generatorW C u ϑb) (generatorW C r ϑa) =
        2 * q * ∫ p, inner ℝ (sb7_Lam3 C T ϑa (r, p)) (sb7_Lam3 C T ϑb (u, p))
          ∂(u10_mu d T C.ρ) := by
    intro u hu r hr
    have huT : u ∈ Set.Icc (0 : ℝ) T := ⟨hu.1, hu.2.trans htb.2⟩
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans hta.2⟩
    rw [sb7_noiseCov_eq hT hρ hρm huT hrT (hcls u huT _ (hb.weak.2.2 u huT))
      (hcls r hrT _ (ha.weak.2.2 r hrT))]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hLH (ϑ := ϑa) r hrT, hLH (ϑ := ϑb) u huT] with p hp1 hp2
    rw [hp1, hp2, real_inner_comm]
  -- the abstract expansion
  have hK0 : 0 ≤ Ka + Kb + Ba + Bb := by linarith
  have hRA := sb7_RA (ν := u10_mu d T C.ρ) (a₀ := sb7_H C ta ϑa) (b₀ := sb7_H C tb ϑb)
    (La := sb7_Lam3 C T ϑa) (Lb := sb7_Lam3 C T ϑb) (K := Ka + Kb + Ba + Bb)
    (sb7_H_meas hta.1 hcla) (sb7_H_meas htb.1 hclb) ha.Lm hb.Lm
    (fun p => (hKa p).trans (by linarith)) (fun p => (hKb p).trans (by linarith))
    (fun q' => (sb7_Lam3_bdd hBa0 hBa q').trans (by linarith))
    (fun q' => (sb7_Lam3_bdd hBb0 hBb q').trans (by linarith)) hK0 hIta hItb
  rw [sb7_D_int hT hρ hρm hcls ha hb hta htb] at hRA
  -- assemble
  have s2 : ∫ u in Set.Icc (0 : ℝ) tb, ∫ ζ, sb7_Xf C A η₀ Y (ta, ϑa) ζ * sb7_g C A T η₀ Y ϑb (u, ζ) ∂P =
      2 * q * ∫ u in Set.Icc (0 : ℝ) tb, ∫ p, inner ℝ (sb7_H C ta ϑa p) (sb7_Lam3 C T ϑb (u, p))
        ∂(u10_mu d T C.ρ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
    rw [c2 u hu, e2 u hu]
  have s3 : ∫ r in Set.Icc (0 : ℝ) ta, ∫ ζ, sb7_Xf C A η₀ Y (tb, ϑb) ζ * sb7_g C A T η₀ Y ϑa (r, ζ) ∂P =
      2 * q * ∫ r in Set.Icc (0 : ℝ) ta, ∫ p, inner ℝ (sb7_Lam3 C T ϑa (r, p)) (sb7_H C tb ϑb p)
        ∂(u10_mu d T C.ρ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [c3 r hr, e3 r hr]
  have s4 : ∫ u in Set.Icc (0 : ℝ) tb, ∫ r in Set.Icc (0 : ℝ) ta, ∫ ζ,
      sb7_g C A T η₀ Y ϑb (u, ζ) * sb7_g C A T η₀ Y ϑa (r, ζ) ∂P =
      2 * q * ∫ u in Set.Icc (0 : ℝ) tb, ∫ r in Set.Icc (0 : ℝ) ta, ∫ p,
        inner ℝ (sb7_Lam3 C T ϑa (r, p)) (sb7_Lam3 C T ϑb (u, p)) ∂(u10_mu d T C.ρ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [c4 u hu r hr, e4 u hu r hr]
  rw [c1, s2, s3, s4, e1, hRA]
  ring

end Cov



/-! ### Assembly of the weak form -/

section Final

variable {Γ : ℝ} {C : WholeCoeff d} {A q T : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {η₀ : Ω → (Euc d → ℝ) → ℝ} {Y : ℝ → Ω → HNeg d Γ}

theorem sb7_toLp_sub {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (hfg : MemLp (fun ζ => f ζ - g ζ) 2 P) :
    hfg.toLp (fun ζ => f ζ - g ζ) = hf.toLp f - hg.toLp g := by
  refine Lp.ext ?_
  filter_upwards [hfg.coeFn_toLp, Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp,
    hg.coeFn_toLp] with ζ a b c e
  rw [a, b]; simp [c, e]

theorem sb7_g_eq_X {ϑ : Euc d → ℝ} (hϑ : IsWeakTestFn Γ C T ϑ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    ∃ θ : Sb7Theta d Γ T, θ.1 = (r, generatorW C r ϑ) ∧
      ∀ ζ, sb7_g C A T η₀ Y ϑ (r, ζ) = sb7_Xf C A η₀ Y θ.1 ζ := by
  refine ⟨⟨(r, generatorW C r ϑ), hr, hϑ.2.2 r hr⟩, rfl, fun ζ => ?_⟩
  simp [sb7_g, hr]

/-- The Gaussian part of the weak equation. -/
theorem sb7_weak_gauss (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ))
    (hcls : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ, IsSobolevTest Γ φ → ∃ f, IsClassicalAdjointW C t φ f)
    (hη₀m : Measurable η₀) (hlin : IsLinearOnCb1 P η₀)
    (horbit : ∀ᵐ ζ ∂P, ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∀ t ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun r => η₀ ζ (propagatorW C 0 r (generatorW C r ϑ))) (Set.Icc (0 : ℝ) t) ∧
      η₀ ζ (fun x => ∫ r in Set.Icc (0 : ℝ) t, propagatorW C 0 r (generatorW C r ϑ) x) =
        ∫ r in Set.Icc (0 : ℝ) t, η₀ ζ (propagatorW C 0 r (generatorW C r ϑ)))
    (hdual : IsAdjointDualityLimitW P C Γ A q T η₀ Y)
    (hcb : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∀ t ∈ Set.Icc (0 : ℝ) T,
      MemCb 1 (propagatorW C 0 t ϑ))
    (hW : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → Sb7WT Γ C A T η₀ Y ϑ)
    (p : ℕ) (ts : Fin p → ℝ) (ϑ : Fin p → Euc d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (hϑ : ∀ a, IsWeakTestFn Γ C T (ϑ a)) :
    IndepFun (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (ϑ a) (Y (ts a) ζ) - A * η₀ ζ (ϑ a) -
        ∫ r in Set.Icc (0 : ℝ) (ts a), HNeg.pairing (generatorW C r (ϑ a)) (Y r ζ) :
          EuclideanSpace ℝ (Fin p))) η₀ P ∧
      law P (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (ϑ a) (Y (ts a) ζ) - A * η₀ ζ (ϑ a) -
        ∫ r in Set.Icc (0 : ℝ) (ts a), HNeg.pairing (generatorW C r (ϑ a)) (Y r ζ) :
          EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a b => 2 * q * ∫ r in Set.Icc (0 : ℝ) (min (ts a) (ts b)),
          ∫ x, inner ℝ (gradient (ϑ a) x) (gradient (ϑ b) x) * C.ρ r x) := by
  have hF := sb7_fam hq hT hρ hρm hcls hη₀m hdual
  set Mf : Fin p → Ω → ℝ := fun a ζ => sb7_Xf C A η₀ Y (ts a, ϑ a) ζ -
    ∫ r in Set.Icc (0 : ℝ) (ts a), sb7_g C A T η₀ Y (ϑ a) (r, ζ) with hMf
  have hG : ∀ a, ∃ V, Sb7Noise P (Set.Icc (0 : ℝ) (ts a)) (sb7_g C A T η₀ Y (ϑ a)) V := by
    intro a
    obtain ⟨B, hB0, hB⟩ := (hW _ (hϑ a)).bd
    exact ⟨_, sb7_noise_theta hq hT hρ hρm hcls hF (hϑ a) hB0 hB (hW _ (hϑ a)).gm (hts a)⟩
  choose V hG using hG
  have hIv : ∀ a, volume (Set.Icc (0 : ℝ) (ts a)) < ∞ := fun a => by simp
  have hθ : ∀ a, ∃ θ : Sb7Theta d Γ T, θ.1 = (ts a, ϑ a) :=
    fun a => ⟨⟨(ts a, ϑ a), hts a, (hϑ a).2.1⟩, rfl⟩
  have hMm : ∀ a, Measurable (Mf a) := fun a =>
    (sb7_Xf_meas hη₀m hdual.meas (hϑ a).2.1).sub (hG a).J_measurable
  have hM2 : ∀ a, MemLp (Mf a) 2 P := fun a =>
    (hF.memLp ⟨(ts a, ϑ a), hts a, (hϑ a).2.1⟩).sub ((hG a).J_memLp measurableSet_Icc (hIv a))
  have hMK : ∀ a, (hM2 a).toLp (Mf a) ∈ (Submodule.span ℝ
      (Set.range fun θ : Sb7Theta d Γ T => (hF.memLp θ).toLp (sb7_Xf C A η₀ Y θ.1))).topologicalClosure := by
    intro a
    have h1 := (hF.memLp ⟨(ts a, ϑ a), hts a, (hϑ a).2.1⟩)
    have h2 := (hG a).J_memLp measurableSet_Icc (hIv a)
    have e := sb7_toLp_sub h1 h2 (hM2 a)
    refine e ▸ Submodule.sub_mem _ ?_ ?_
    · exact Submodule.le_topologicalClosure _ (Submodule.subset_span
        ⟨⟨(ts a, ϑ a), hts a, (hϑ a).2.1⟩, rfl⟩)
    · refine sb7_J_mem hF (hG a) measurableSet_Icc (hIv a) ?_
      intro r hr
      obtain ⟨θ, -, hθ⟩ := sb7_g_eq_X (A := A) (η₀ := η₀) (Y := Y) (hϑ a) ⟨hr.1, hr.2.trans (hts a).2⟩
      exact ⟨θ, hθ⟩
  obtain ⟨hind, hlaw⟩ := hF.closure_vec hη₀m Mf hMm hM2 hMK
  have hmat : (Matrix.of fun a b => ∫ ζ, Mf a ζ * Mf b ζ ∂P : Matrix (Fin p) (Fin p) ℝ) =
      Matrix.of fun a b => 2 * q * ∫ r in Set.Icc (0 : ℝ) (min (ts a) (ts b)),
        ∫ x, inner ℝ (gradient (ϑ a) x) (gradient (ϑ b) x) * C.ρ r x := by
    ext a b
    exact sb7_cov_M hq hT hρ hρm hcls hF (hW _ (hϑ a)) (hW _ (hϑ b)) (hts a) (hts b)
  rw [hmat] at hlaw
  have hae : (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (ϑ a) (Y (ts a) ζ) - A * η₀ ζ (ϑ a) -
        ∫ r in Set.Icc (0 : ℝ) (ts a), HNeg.pairing (generatorW C r (ϑ a)) (Y r ζ) :
          EuclideanSpace ℝ (Fin p))) =ᵐ[P] fun ζ => (WithLp.toLp 2 fun a => Mf a ζ :
          EuclideanSpace ℝ (Fin p)) := by
    have : ∀ a, ∀ᵐ ζ ∂P, HNeg.pairing (ϑ a) (Y (ts a) ζ) - A * η₀ ζ (ϑ a) -
        ∫ r in Set.Icc (0 : ℝ) (ts a), HNeg.pairing (generatorW C r (ϑ a)) (Y r ζ) = Mf a ζ := by
      intro a
      obtain ⟨B, hB0, hB⟩ := (hW _ (hϑ a)).bd
      exact sb7_M_eq hT hlin horbit (hϑ a) (hts a) (hcb _ (hϑ a) _ (hts a))
        (fun x => (((hW _ (hϑ a)).duh 0 (ts a) le_rfl (hts a).1 (hts a).2).2 x).1) (hG a)
    filter_upwards [ae_all_iff.2 this] with ζ hζ
    ext a
    exact hζ a
  exact ⟨hind.congr hae.symm (Filter.EventuallyEq.refl _ _), (Measure.map_congr hae).trans hlaw⟩

theorem sb7_prop_zero {ϑ : Euc d → ℝ}
    (h : ∃ f, IsClassicalAdjointW C 0 ϑ f) : propagatorW C 0 0 ϑ = ϑ := by
  obtain ⟨f, hf, hfe⟩ := sb7_prop_eq h
  rw [hfe 0]
  exact hf.terminal

theorem sb7_weak_init (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ))
    (hcls : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ, IsSobolevTest Γ φ → ∃ f, IsClassicalAdjointW C t φ f)
    (hη₀m : Measurable η₀) (hdual : IsAdjointDualityLimitW P C Γ A q T η₀ Y)
    {ϑ : Euc d → ℝ} (hϑ : IsWeakTestFn Γ C T ϑ) :
    ∀ᵐ ζ ∂P, HNeg.pairing ϑ (Y 0 ζ) = A * η₀ ζ ϑ := by
  have hF := sb7_fam hq hT hρ hρm hcls hη₀m hdual
  set θ0 : Sb7Theta d Γ T := ⟨(0, ϑ), ⟨le_rfl, hT⟩, hϑ.2.1⟩ with hθ0
  have h1 : ∫ ζ, sb7_Xf C A η₀ Y θ0.1 ζ * sb7_Xf C A η₀ Y θ0.1 ζ ∂P =
      noiseCovW C q 0 0 ϑ ϑ := hF.cov_eq θ0 θ0
  have h0 : noiseCovW C q 0 0 ϑ ϑ = 0 := by
    unfold noiseCovW
    simp
  rw [h0] at h1
  have hnn : (0 : Ω → ℝ) ≤ fun ζ => sb7_Xf C A η₀ Y θ0.1 ζ * sb7_Xf C A η₀ Y θ0.1 ζ :=
    fun ζ => mul_self_nonneg _
  have hint : Integrable (fun ζ => sb7_Xf C A η₀ Y θ0.1 ζ * sb7_Xf C A η₀ Y θ0.1 ζ) P :=
    (hF.memLp θ0).integrable_mul (hF.memLp θ0)
  have h2 := (integral_eq_zero_iff_of_nonneg hnn hint).1 h1
  have h3 := hcls 0 ⟨le_rfl, hT⟩ ϑ hϑ.2.1
  filter_upwards [h2] with ζ hζ
  have : sb7_Xf C A η₀ Y θ0.1 ζ = 0 := by
    have := hζ
    simpa using this
  simp only [hθ0, sb7_Xf, sb7_prop_zero h3] at this
  linarith

/-- The weak form `IsWeakLimitSPDEW` from the duality identity, under the regularity hypotheses
(`hbd`, `hΛm`, `hgm`, `hη₀m` are the added technical hypotheses documented in the tie file). -/
theorem sb7_weak_form_main {K : ℝ} (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ)) (hU : AdjointInputOne Γ C T K)
    (hduh : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      (∃ B : ℝ, ∀ r ∈ Set.Icc s t, ∀ x,
        ‖gradient (propagatorW C s r (generatorW C r ϑ)) x‖ ≤ B) ∧
      ∀ x, propagatorW C s t ϑ x - ϑ x =
          ∫ r in Set.Icc s t, propagatorW C s r (generatorW C r ϑ) x ∧
        gradient (propagatorW C s t ϑ) x - gradient ϑ x =
          ∫ r in Set.Icc s t, gradient (propagatorW C s r (generatorW C r ϑ)) x)
    (hbd : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∃ B : ℝ, ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ T →
      ∀ x, ‖gradient (propagatorW C s r (generatorW C r ϑ)) x‖ ≤ B)
    (hΛm : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → Measurable (sb7_Lam3 C T ϑ))
    (hη₀m : Measurable η₀) (hlin : IsLinearOnCb1 P η₀)
    (horbit : ∀ᵐ ζ ∂P, ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∀ t ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun r => η₀ ζ (propagatorW C 0 r (generatorW C r ϑ))) (Set.Icc (0 : ℝ) t) ∧
      η₀ ζ (fun x => ∫ r in Set.Icc (0 : ℝ) t, propagatorW C 0 r (generatorW C r ϑ) x) =
        ∫ r in Set.Icc (0 : ℝ) t, η₀ ζ (propagatorW C 0 r (generatorW C r ϑ)))
    (hgm : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → Measurable (sb7_g C A T η₀ Y ϑ))
    (hdual : IsAdjointDualityLimitW P C Γ A q T η₀ Y) : IsWeakLimitSPDEW P C Γ A q T η₀ Y := by
  have hcls : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ, IsSobolevTest Γ φ → ∃ f, IsClassicalAdjointW C t φ f :=
    fun t ht φ hφ => (hU t ht).1 φ hφ
  have hcb : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∀ t ∈ Set.Icc (0 : ℝ) T,
      MemCb 1 (propagatorW C 0 t ϑ) := fun ϑ hϑ t ht => ((hU t ht).2.2 ϑ hϑ.2.1).1
  have hW : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → Sb7WT Γ C A T η₀ Y ϑ := by
    intro ϑ hϑ
    obtain ⟨B, hB⟩ := hbd ϑ hϑ
    exact ⟨hϑ, hduh ϑ hϑ, ⟨max B 0, le_max_right _ _, fun s r h1 h2 h3 x =>
      (hB s r h1 h2 h3 x).trans (le_max_left _ _)⟩, hΛm ϑ hϑ, hgm ϑ hϑ⟩
  exact ⟨hρm, hdual.meas, fun ϑ hϑ => sb7_weak_init hq hT hρ hρm hcls hη₀m hdual hϑ,
    fun p ts ϑ hts hϑ => sb7_weak_gauss hq hT hρ hρm hcls hη₀m hlin horbit hdual hcb hW p ts ϑ hts hϑ⟩

end Final


end HRS.MS.U10
