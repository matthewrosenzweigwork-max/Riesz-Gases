import HRS.MS.Fp81S21MovingEncodedOrbit2
import HRS.MS.Fp81S21GaussianCrossDensity
import HRS.MS.Fp81S21TimeRep3

/-! Absolute probability–time integrability on the actual active intervals.
The radius precedes the physical package and all observation data. The density
uses the selected coefficient fields, with no replacement of the realization.
No joint time measurability of an arbitrary chi family is required. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

/-- Actual moving test, without clamping. -/
def fp81s21_wick_time_f (R : Trajectory p δ) (a : ℝ)
    (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
    (i : Fin 3) (r : ℝ) : Euc p.d → ℝ :=
  propagatorW (r26t3_coeff R) r (a + τ i) (φ i)

/-- Random drift time density, before taking expectation. -/
def fp81s21_wick_time_D (Q : fp81s21_Physical35 p R) (a : ℝ)
    (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i))
    (i : Fin 3) (ω : Q.src.G0.Ω) (r : ℝ) : ℝ :=
  fp81s21_chartAction Q.E (Q.S.qe Q.src.G0 r ω) (fp81s21_wick_time_f R a τ φ i r) *
    fp81s21_cross37_X Q a τ φ hφ (i + 1) ω * fp81s21_cross37_X Q a τ φ hφ (i + 2) ω

/-- Random covariance time density before the deterministic factor `2 / beta`. -/
def fp81s21_wick_time_J (Q : fp81s21_Physical35 p R) (a : ℝ)
    (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i))
    (i : Fin 3) (ω : Q.src.G0.Ω) (r : ℝ) : ℝ :=
  fp81s21_chartAction Q.E
    (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q Q.src.G0) r ω)
    (fun x => inner ℝ (gradient (fp81s21_wick_time_f R a τ φ i r) x)
      (gradient (fp81s21_wick_time_f R a τ φ (i + 1) r) x)) *
    fp81s21_cross37_X Q a τ φ hφ (i + 2) ω

/-- Signed and absolute L1 on probability times the exact active time interval.
In particular these conclusions justify both orders of Fubini, including the
absolute densities; they do not assert an integrated Wick identity. -/
def fp81s21_WickTimeDom (Q : fp81s21_Physical35 p R) (a : ℝ)
    (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) : Prop :=
  ∀ i, let dtD := volume.restrict (Icc (0 : ℝ) (a + τ i))
       let dtJ := volume.restrict (Icc (0 : ℝ) (min (a + τ i) (a + τ (i + 1))))
       let D := fun z : Q.src.G0.Ω × ℝ => fp81s21_wick_time_D Q a τ φ hφ i z.1 z.2
       let J := fun z : Q.src.G0.Ω × ℝ => fp81s21_wick_time_J Q a τ φ hφ i z.1 z.2
       Integrable D (Q.src.G0.P.prod dtD) ∧ Integrable (fun z => |D z|) (Q.src.G0.P.prod dtD) ∧
       Integrable J (Q.src.G0.P.prod dtJ) ∧ Integrable (fun z => |J z|) (Q.src.G0.P.prod dtJ)

/-- The moving encoded orbit bounds give absolute domination for the selected
linear and quadratic coefficient fields and the actual endpoint observations. -/
theorem fp81s21_gaussian_wick_time_dom (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Physical35 p R, ∀ (a : ℝ), 0 ≤ a →
      ∀ (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
        (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)),
      fp81s21_WickTimeDom Q a τ φ hφ := by
  obtain ⟨δ₀, hδ₀, hhalf, horbit⟩ := fp81s21_moving_encoded_clamped_orbits p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R Q a ha τ φ hφ
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff := HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff := UniformSpace.secondCountable_of_separable _
  let F := fun (i : Fin 3) (r : ℝ) => propagatorW (r26t3_coeff R)
    (projIcc 0 (a + (τ i : ℝ)) (add_nonneg ha (τ i).property.1) r) (a + τ i) (φ i)
  obtain ⟨hF, hB⟩ := horbit δ hδ hδle R Q.E a ha τ φ hφ
  obtain ⟨G, hG, _, hX, hXm⟩ := fp81s21_cross37_common_source Q a ha τ φ hφ
  have hqB := (Q.S.payload Q.src.G0).2.2.2.2.1
  have hqG := (Q.canon.payload Q.src.G0).coefficients.weak_momentRep
  have hclamp (i : Fin 3) (r : ℝ) (hr : r ∈ Icc 0 (a + τ i)) :
      F i r = fp81s21_wick_time_f R a τ φ i r := by
    simp only [F, projIcc_of_mem _ hr, fp81s21_wick_time_f]
  intro i
  have ht : 0 ≤ a + (τ i : ℝ) := add_nonneg ha (τ i).property.1
  have htJ : 0 ≤ min (a + (τ i : ℝ)) (a + (τ (i + 1) : ℝ)) :=
    le_min ht (add_nonneg ha (τ (i + 1)).property.1)
  have hBD := (fp81s21_MomentRep_time_product Q.E Q.src.G0.P _ _ _ 0
    (a + τ i) hqB le_rfl ht).1
  have hGJ := (fp81s21_MomentRep_time_product Q.E Q.src.G0.P _ _ _ 0
    (min (a + τ i) (a + τ (i + 1))) hqG le_rfl htJ).1
  simp only [zero_add] at hBD hGJ
  obtain ⟨BD, hBD0, hBDb⟩ := (hF i).2.2
  have hXY := HRS.MC.QRSpec.Wick.qrpw_memLp2_mul
    (hG _ (hX (i + 1))).1 (hG _ (hX (i + 2))).1
  have hD := inner_bounded_family_mul_integrable _ Q.src.G0.P _ hBD
    (fun r => Q.E.encode (F i r)) (hF i).1 BD hBD0 hBDb _ hXY
  have hD' : Integrable
      (fun z : ℝ × Q.src.G0.Ω => fp81s21_wick_time_D Q a τ φ hφ i z.2 z.1)
      ((volume.restrict (Icc 0 (a + (τ i : ℝ)))).prod Q.src.G0.P) := by
    apply hD.congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz
    simp only [fp81s21_wick_time_D, fp81s21_chartAction, hclamp i z.1 hz, mul_assoc]
  obtain ⟨BJ, hBJ0, hBJb⟩ := (hB i (i + 1)).2.2
  have hJ := inner_bounded_family_mul_integrable _ Q.src.G0.P _ hGJ
    (fun r => Q.E.encode (fun x => inner ℝ (gradient (F i r) x)
      (gradient (F (i + 1) r) x))) (hB i (i + 1)).1 BJ hBJ0 hBJb _ (hXm (i + 2))
  have hJ' : Integrable
      (fun z : ℝ × Q.src.G0.Ω => fp81s21_wick_time_J Q a τ φ hφ i z.2 z.1)
      ((volume.restrict (Icc 0 (min (a + (τ i : ℝ)) (a + (τ (i + 1) : ℝ))))).prod Q.src.G0.P) := by
    apply hJ.congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz
    have hi : z.1 ∈ Icc 0 (a + (τ i : ℝ)) := ⟨hz.1, hz.2.trans (min_le_left _ _)⟩
    have hj : z.1 ∈ Icc 0 (a + (τ (i + 1) : ℝ)) := ⟨hz.1, hz.2.trans (min_le_right _ _)⟩
    simp only [fp81s21_wick_time_J, fp81s21_chartAction, hclamp i z.1 hi, hclamp (i + 1) z.1 hj]
  exact ⟨hD'.swap, hD'.swap.abs, hJ'.swap, hJ'.swap.abs⟩

/-- Fixed-time linear pairing, transferred to any spatially equal density. -/
theorem fp81s21_wick_time_linear_pair
    (Q : fp81s21_Physical35 p R) (a : ℝ)
    (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
    (χ : Fin 3 → ℝ → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i))
    (hcross : fp81s21_Cross37 Q a τ φ χ hφ) (i : Fin 3)
    (r : ℝ) (hr : r ∈ Icc 0 (a + p.T)) (f : Euc p.d → ℝ)
    (hf : IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f) :
    (∫ ω, fp81s21_chartAction Q.E
      (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q Q.src.G0) r ω) f *
      fp81s21_cross37_X Q a τ φ hφ i ω ∂Q.src.G0.P) = ∫ x, f x * χ i r x := by
  obtain ⟨G, hG, hT, hX, u, hu⟩ := hcross
  obtain ⟨hfμ, hk, hlin, hquad⟩ := Q.weighted r hr.1 f hf
  calc
    _ = ∫ ω, Q.S.T Q.src.G0 r (hfμ.toLp f) ω *
        fp81s21_cross37_X Q a τ φ hφ i ω ∂Q.src.G0.P :=
      integral_congr_ae (hlin.mono fun ω hω => congrArg (fun z => z * _) hω)
    _ = ∫ x, (hfμ.toLp f) x * u i r x ∂HRS.Whole.withDensityReal R.ρβ :=
      ((hu i r hr).1 _).2
    _ = ∫ x, f x * u i r x ∂HRS.Whole.withDensityReal R.ρβ :=
      integral_congr_ae (hfμ.coeFn_toLp.mono fun x hx => congrArg (fun z => z * _) hx)
    _ = ∫ x, f x * (u i r x * R.ρβ x) := by
      unfold HRS.Whole.withDensityReal
      rw [integral_withDensity_eq_integral_toReal_smul R.thermal.1.1.measurable.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_eq_mul, ENNReal.toReal_ofReal (R.thermal.1.1.nonneg x)]
      ring
    _ = _ := HRS.MS.S21E.s21e_int_congr (hu i r hr).2 f

/-- Clause 5, with arbitrary supplied chi and the exact covariance interval. -/
theorem fp81s21_gaussian_wick_time_cov (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Physical35 p R, ∀ (a : ℝ), 0 ≤ a →
      ∀ (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
        (χ : Fin 3 → ℝ → Euc p.d → ℝ)
        (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)),
      S21eChiClause p.d p.s p.a p.β p.γ R.ρ p.T a τ φ χ →
      ∀ i : Fin 3, IntegrableOn (fun r => ∫ x,
        inner ℝ (gradient (fp81s21_wick_time_f R a τ φ i r) x)
          (gradient (fp81s21_wick_time_f R a τ φ (i + 1) r) x) * χ (i + 2) r x)
        (Icc (0 : ℝ) (min (a + τ i) (a + τ (i + 1)))) := by
  obtain ⟨δD, hδD, hhalf, hdom⟩ := fp81s21_gaussian_wick_time_dom p
  obtain ⟨δE, hδE, _, horbit⟩ := fp81s21_moving_encoded_clamped_orbits p
  obtain ⟨δC, hδC, _, hcross⟩ := fp81s21_gaussian_cross_density p
  refine ⟨min δD (min δE δC), lt_min hδD (lt_min hδE hδC),
    (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R Q a ha τ φ χ hφ hχ i
  have hle : δ ≤ δD ∧ δ ≤ δE ∧ δ ≤ δC := by simpa only [le_min_iff] using hδle
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  have hd := (hdom δ hδ hle.1 R Q a ha τ φ hφ i).2.2.1
  have hc := hcross δ hδ hle.2.2 R Q a ha τ φ χ hφ hχ
  have hb := (horbit δ hδ hle.2.1 R Q.E a ha τ φ hφ).2 i (i + 1)
  apply hd.integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  have hi : r ∈ Icc 0 (a + (τ i : ℝ)) := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hj : r ∈ Icc 0 (a + (τ (i + 1) : ℝ)) := ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
  have hw := hb.2.1 r
  simp only [projIcc_of_mem _ hi, projIcc_of_mem _ hj] at hw
  exact fp81s21_wick_time_linear_pair Q a τ φ χ hφ hc (i + 2) r
    ⟨hr.1, hi.2.trans (by linarith [(τ i).property.2])⟩ _ hw

#print axioms fp81s21_gaussian_wick_time_dom
#print axioms fp81s21_wick_time_linear_pair
#print axioms fp81s21_gaussian_wick_time_cov
end HRS.Fp81.S21
end
