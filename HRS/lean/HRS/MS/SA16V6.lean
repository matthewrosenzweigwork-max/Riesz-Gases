import HRS.MS.SA16V5

/-!
# S.A.16 T1, part 2: `Ψ(f) = ∫ ‖f‖^p` on `L^p(V)` (`V` an inner product space, `p ≥ 2`)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16V

section LpPart
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]

lemma sa16v_continuous_g {r : ℝ} (hr : 0 ≤ r) : Continuous (fun v : V => sa16v_g r v) := by
  unfold sa16v_g
  exact (continuous_norm.rpow_const (fun _ => Or.inr hr)).smul continuous_id

lemma sa16v_norm_g (r : ℝ) (hr : 0 ≤ r) (v : V) : ‖sa16v_g r v‖ = ‖v‖ ^ (r + 1) := by
  unfold sa16v_g
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  by_cases hv : ‖v‖ = 0
  · rw [hv, mul_zero, Real.zero_rpow (by linarith : r + 1 ≠ 0)]
  · rw [Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)), Real.rpow_one]

/-- `g ∘ f` is in `L^{p'}` when `f ∈ L^p` -/
lemma sa16v_g_memLp {p : ℝ} (hp : 2 ≤ p) {f : α → V} (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (fun x => sa16v_g (p - 2) (f x)) (ENNReal.ofReal (Real.conjExponent p)) μ := by
  have hp1 : 1 < p := by linarith
  have hq : 0 < p - 1 := by linarith
  have h := hf.norm_rpow_div (ENNReal.ofReal (p - 1))
  rw [ENNReal.toReal_ofReal hq.le, ← ENNReal.ofReal_div_of_pos hq] at h
  have e : p / (p - 1) = Real.conjExponent p := rfl
  rw [e] at h
  have hm : AEStronglyMeasurable (fun x => sa16v_g (p - 2) (f x)) μ :=
    (sa16v_continuous_g (by linarith)).comp_aestronglyMeasurable hf.aestronglyMeasurable
  refine h.of_le hm (Eventually.of_forall fun x => ?_)
  rw [sa16v_norm_g _ (by linarith)]
  have : p - 2 + 1 = p - 1 := by ring
  rw [this, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

/-- a Hölder triple `(q₁, P, P')` with `q₁⁻¹ = (p-2)/p`, and the `L^{q₁}` norm of `N^{p-2}` -/
lemma sa16v_triple {p : ℝ} (hp : 2 ≤ p) :
    ∃ q1 : ℝ≥0∞, ENNReal.HolderTriple q1 (ENNReal.ofReal p) (ENNReal.ofReal (Real.conjExponent p)) ∧
      ∀ N : α → ℝ, (∀ x, 0 ≤ N x) → AEStronglyMeasurable N μ →
        eLpNorm (fun x => N x ^ (p - 2)) q1 μ ≤ eLpNorm N (ENNReal.ofReal p) μ ^ (p - 2) := by
  rcases hp.eq_or_lt with rfl | hgt
  · have hc : Real.conjExponent 2 = 2 := by norm_num [Real.conjExponent]
    rw [hc]
    refine ⟨⊤, ENNReal.HolderTriple.symm (p := ENNReal.ofReal 2) (q := ⊤) (r := ENNReal.ofReal 2), ?_⟩
    intro N hN hNm
    simp only [sub_self, Real.rpow_zero, ENNReal.rpow_zero]
    rw [eLpNorm_exponent_top]
    · exact eLpNormEssSup_le_of_ae_enorm_bound (Eventually.of_forall fun x => by simp)
    · exact aestronglyMeasurable_const
  · have hp2 : 0 < p - 2 := by linarith
    have hp1 : 0 < p - 1 := by linarith
    have hT : Real.HolderTriple (p / (p - 2)) p (Real.conjExponent p) := by
      refine ⟨?_, by positivity, by linarith⟩
      unfold Real.conjExponent
      field_simp
      ring
    refine ⟨ENNReal.ofReal (p / (p - 2)), hT.ennrealOfReal, ?_⟩
    intro N hN hNm
    have h := eLpNorm_norm_rpow N hNm (p := ENNReal.ofReal (p / (p - 2))) hp2
    have e : ENNReal.ofReal (p / (p - 2)) * ENNReal.ofReal (p - 2) = ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    rw [e] at h
    have e2 : (fun x => ‖N x‖ ^ (p - 2)) = fun x => N x ^ (p - 2) := by
      funext x; rw [Real.norm_of_nonneg (hN x)]
    rw [e2] at h
    exact h.le

/-- the key `L^{p'}` Lipschitz estimate of `g ∘ ·` -/
lemma sa16v_g_sub_eLpNorm {p : ℝ} (hp : 2 ≤ p) {f f' : α → V}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hf' : MemLp f' (ENNReal.ofReal p) μ) :
    eLpNorm (fun x => sa16v_g (p - 2) (f x) - sa16v_g (p - 2) (f' x)) (ENNReal.ofReal (Real.conjExponent p)) μ ≤
      ENNReal.ofReal (p - 1) *
        ((eLpNorm f (ENNReal.ofReal p) μ + eLpNorm f' (ENNReal.ofReal p) μ) ^ (p - 2) *
          eLpNorm (fun x => f x - f' x) (ENNReal.ofReal p) μ) := by
  obtain ⟨q1, htrip, hN⟩ := sa16v_triple (μ := μ) hp
  have hp2 : 0 ≤ p - 2 := by linarith
  have hgm : AEStronglyMeasurable (fun x => sa16v_g (p - 2) (f x) - sa16v_g (p - 2) (f' x)) μ :=
    ((sa16v_continuous_g hp2).comp_aestronglyMeasurable hf.aestronglyMeasurable).sub
      ((sa16v_continuous_g hp2).comp_aestronglyMeasurable hf'.aestronglyMeasurable)
  set N : α → ℝ := fun x => ‖f x‖ + ‖f' x‖ with hNdef
  set c : α → ℝ := fun x => ‖f x - f' x‖ with hcdef
  have hNm : AEStronglyMeasurable N μ := hf.aestronglyMeasurable.norm.add hf'.aestronglyMeasurable.norm
  have hcm : AEStronglyMeasurable c μ := (hf.aestronglyMeasurable.sub hf'.aestronglyMeasurable).norm
  have hpt : ∀ x, ‖sa16v_g (p - 2) (f x) - sa16v_g (p - 2) (f' x)‖ ≤ (p - 1) * (N x ^ (p - 2) * c x) := by
    intro x
    have h := sa16v_g_lip (p - 2) hp2 (f x) (f' x)
    have e : 1 + (p - 2) = p - 1 := by ring
    rw [e] at h
    calc _ ≤ (p - 1) * (‖f x‖ + ‖f' x‖) ^ (p - 2) * ‖f x - f' x‖ := h
      _ = (p - 1) * (N x ^ (p - 2) * c x) := by simp only [hNdef, hcdef]; ring
  have h1 : eLpNorm (fun x => sa16v_g (p - 2) (f x) - sa16v_g (p - 2) (f' x))
      (ENNReal.ofReal (Real.conjExponent p)) μ ≤
      eLpNorm (fun x => (p - 1) * (N x ^ (p - 2) * c x)) (ENNReal.ofReal (Real.conjExponent p)) μ :=
    eLpNorm_mono_real hgm hpt
  refine h1.trans ?_
  have e1 : (fun x => (p - 1) * (N x ^ (p - 2) * c x)) = (p - 1) • (fun x => N x ^ (p - 2) * c x) := by
    funext x; simp
  have hp1 : 0 ≤ p - 1 := by linarith
  rw [e1, eLpNorm_const_smul, Real.enorm_eq_ofReal hp1]
  refine mul_le_mul' le_rfl ?_
  have := htrip
  have h2 := eLpNorm_smul_le_mul_eLpNorm (μ := μ) (p := q1) (q := ENNReal.ofReal p)
    (r := ENNReal.ofReal (Real.conjExponent p)) (φ := fun x => N x ^ (p - 2)) (f := c)
    (hφ := (hNm.aemeasurable.pow_const _).aestronglyMeasurable) hcm
  have e2 : ((fun x => N x ^ (p - 2)) • c) = fun x => N x ^ (p - 2) * c x := by
    funext x; simp
  rw [e2] at h2
  refine h2.trans (mul_le_mul' ?_ ?_)
  · refine (hN N (fun x => by simp only [hNdef]; positivity) hNm).trans ?_
    refine ENNReal.rpow_le_rpow ?_ hp2
    calc eLpNorm N (ENNReal.ofReal p) μ ≤ eLpNorm (fun x => ‖f x‖) (ENNReal.ofReal p) μ +
          eLpNorm (fun x => ‖f' x‖) (ENNReal.ofReal p) μ :=
          eLpNorm_add_le (f := fun x => ‖f x‖) (g := fun x => ‖f' x‖) (by
            have : (1 : ℝ) ≤ p := by linarith
            simpa using ENNReal.ofReal_le_ofReal this)
      _ = eLpNorm f (ENNReal.ofReal p) μ + eLpNorm f' (ENNReal.ofReal p) μ := by
          rw [eLpNorm_norm _ hf.aestronglyMeasurable, eLpNorm_norm _ hf'.aestronglyMeasurable]
  · rw [hcdef]
    exact le_of_eq (eLpNorm_norm _ (hf.aestronglyMeasurable.sub hf'.aestronglyMeasurable))

end LpPart

/-! ### `Ψ(f) = ∫ ‖f‖^p` on `L^p(V)` is `C¹` -/

section LpDeriv
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] (p : ℝ) [hp2 : Fact (2 ≤ p)]

instance sa16v_factPc : Fact (1 ≤ ENNReal.ofReal (Real.conjExponent p)) := by
  have hp1 : 1 < p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal (Real.conjExponent p)) :=
    (Real.HolderConjugate.conjExponent hp1).ennrealOfReal
  exact ⟨ENNReal.HolderConjugate.one_le _ (ENNReal.ofReal p)⟩

instance sa16v_hconj : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal (Real.conjExponent p)) :=
  (Real.HolderConjugate.conjExponent (by have : (2 : ℝ) ≤ p := Fact.out; linarith)).ennrealOfReal

/-- the element `g ∘ f ∈ L^{p'}` -/
def sa16v_uLp (f : Lp V (ENNReal.ofReal p) μ) : Lp V (ENNReal.ofReal (Real.conjExponent p)) μ :=
  (sa16v_g_memLp (Fact.out : 2 ≤ p) (Lp.memLp f)).toLp _

lemma sa16v_uLp_coe (f : Lp V (ENNReal.ofReal p) μ) :
    (sa16v_uLp p f : α → V) =ᵐ[μ] fun x => sa16v_g (p - 2) (f x) :=
  MemLp.coeFn_toLp _

/-- the derivative `h ↦ p ∫ ⟪h, g(f)⟫` -/
def sa16v_D (f : Lp V (ENNReal.ofReal p) μ) : Lp V (ENNReal.ofReal p) μ →L[ℝ] ℝ :=
  p • (((innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).lpPairing μ (ENNReal.ofReal p)
    (ENNReal.ofReal (Real.conjExponent p))).flip (sa16v_uLp p f))

lemma sa16v_D_apply (f h : Lp V (ENNReal.ofReal p) μ) :
    sa16v_D p f h = p * ∫ x, ⟪h x, sa16v_g (p - 2) (f x)⟫ ∂μ := by
  unfold sa16v_D
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [sa16v_uLp_coe p f] with x hx
  rw [hx]
  rfl

lemma sa16v_eLpNorm_lp {q : ℝ≥0∞} [Fact (1 ≤ q)] (f : Lp V q μ) : eLpNorm (f : α → V) q μ = ENNReal.ofReal ‖f‖ :=
  (Lp.enorm_def f).symm.trans (ofReal_norm f).symm

lemma sa16v_uLp_sub_le (f f' : Lp V (ENNReal.ofReal p) μ) :
    ‖sa16v_uLp p f - sa16v_uLp p f'‖ ≤ (p - 1) * ((‖f‖ + ‖f'‖) ^ (p - 2) * ‖f - f'‖) := by
  have hpp : 2 ≤ p := Fact.out
  have h := sa16v_g_sub_eLpNorm hpp (Lp.memLp f) (Lp.memLp f')
  have hcoe : ((sa16v_uLp p f - sa16v_uLp p f' : Lp V _ μ) : α → V) =ᵐ[μ]
      fun x => sa16v_g (p - 2) (f x) - sa16v_g (p - 2) (f' x) := by
    filter_upwards [Lp.coeFn_sub (sa16v_uLp p f) (sa16v_uLp p f'), sa16v_uLp_coe p f, sa16v_uLp_coe p f']
      with x h1 h2 h3
    rw [h1]; simp [h2, h3]
  have hcoe2 : eLpNorm (fun x => f x - f' x) (ENNReal.ofReal p) μ = ENNReal.ofReal ‖f - f'‖ := by
    rw [← sa16v_eLpNorm_lp (f - f')]
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub f f'] with x hx
    rw [hx]; rfl
  rw [Lp.norm_def, eLpNorm_congr_ae hcoe]
  rw [sa16v_eLpNorm_lp f, sa16v_eLpNorm_lp f', hcoe2] at h
  have hpm1 : 0 ≤ p - 1 := by linarith
  have e : ENNReal.ofReal (p - 1) * ((ENNReal.ofReal ‖f‖ + ENNReal.ofReal ‖f'‖) ^ (p - 2) * ENNReal.ofReal ‖f - f'‖) =
      ENNReal.ofReal ((p - 1) * ((‖f‖ + ‖f'‖) ^ (p - 2) * ‖f - f'‖)) := by
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hpm1]
  rw [e] at h
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

lemma sa16v_pair_le (h : Lp V (ENNReal.ofReal p) μ) (u : Lp V (ENNReal.ofReal (Real.conjExponent p)) μ) :
    |∫ x, ⟪h x, u x⟫ ∂μ| ≤ ‖h‖ * ‖u‖ := by
  set B : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ with hB
  have hBn : ‖B‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul, hB, innerSL_apply_norm]
  set H : Lp ℝ 1 μ := B.holder 1 h u with hH
  have hcoe : (H : α → ℝ) =ᵐ[μ] fun x => ⟪h x, u x⟫ := by
    filter_upwards [B.coeFn_holder (r := 1) h u] with x hx
    rw [hx, hB, innerSL_apply_apply]
  have h1 : ‖H‖ ≤ ‖h‖ * ‖u‖ := by
    have := B.norm_holder_apply_apply_le (r := 1) h u
    calc ‖H‖ ≤ ‖B‖ * ‖h‖ * ‖u‖ := this
      _ ≤ 1 * ‖h‖ * ‖u‖ := by gcongr
      _ = ‖h‖ * ‖u‖ := by ring
  have h2 : ‖H‖ = ∫ x, ‖H x‖ ∂μ := L1.norm_eq_integral_norm H
  calc |∫ x, ⟪h x, u x⟫ ∂μ| = ‖∫ x, H x ∂μ‖ := by
        rw [Real.norm_eq_abs]; congr 1; exact (integral_congr_ae hcoe).symm
    _ ≤ ∫ x, ‖H x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ‖H‖ := h2.symm
    _ ≤ ‖h‖ * ‖u‖ := h1

lemma sa16v_D_sub_le (f f' h : Lp V (ENNReal.ofReal p) μ) :
    sa16v_D p f h - sa16v_D p f' h ≤ p * ((p - 1) * ((‖f‖ + ‖f'‖) ^ (p - 2) * ‖f - f'‖)) * ‖h‖ := by
  have hpp : 2 ≤ p := Fact.out
  have e : sa16v_D p f h - sa16v_D p f' h = p * ∫ x, ⟪h x, (sa16v_uLp p f - sa16v_uLp p f') x⟫ ∂μ := by
    rw [sa16v_D_apply, sa16v_D_apply, ← mul_sub]
    congr 1
    have hi : ∀ g : Lp V (ENNReal.ofReal p) μ, Integrable (fun x => ⟪h x, sa16v_g (p - 2) (g x)⟫) μ := by
      intro g
      have := (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).memLp_of_bilin (μ := μ) (p := ENNReal.ofReal p)
        (q := ENNReal.ofReal (Real.conjExponent p)) (r := 1) (Lp.memLp h) (sa16v_g_memLp hpp (Lp.memLp g))
      exact memLp_one_iff_integrable.1 this
    rw [← integral_sub (hi f) (hi f')]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (sa16v_uLp p f) (sa16v_uLp p f'), sa16v_uLp_coe p f, sa16v_uLp_coe p f']
      with x h1 h2 h3
    rw [h1]; simp [h2, h3, inner_sub_right]
  rw [e]
  have h1 := sa16v_pair_le p h (sa16v_uLp p f - sa16v_uLp p f')
  have h2 := sa16v_uLp_sub_le p f f'
  have hp0 : 0 ≤ p := by linarith
  calc p * ∫ x, ⟪h x, (sa16v_uLp p f - sa16v_uLp p f') x⟫ ∂μ
      ≤ p * (‖h‖ * ‖sa16v_uLp p f - sa16v_uLp p f'‖) := by
        refine mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1) hp0
    _ ≤ p * (‖h‖ * ((p - 1) * ((‖f‖ + ‖f'‖) ^ (p - 2) * ‖f - f'‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) hp0
    _ = p * ((p - 1) * ((‖f‖ + ‖f'‖) ^ (p - 2) * ‖f - f'‖)) * ‖h‖ := by ring

/-- the functional `Ψ(f) = ∫ ‖f‖^p` -/
def sa16v_Psi (f : Lp V (ENNReal.ofReal p) μ) : ℝ := ∫ x, ‖f x‖ ^ p ∂μ

lemma sa16v_integrable_pow (f : Lp V (ENNReal.ofReal p) μ) : Integrable (fun x => ‖f x‖ ^ p) μ := by
  have hp0 : 0 < p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  have h := (Lp.memLp f).integrable_norm_rpow (by simpa using hp0) ENNReal.ofReal_ne_top
  simpa [ENNReal.toReal_ofReal hp0.le] using h

lemma sa16v_inner_integrable (h g : Lp V (ENNReal.ofReal p) μ) :
    Integrable (fun x => ⟪h x, sa16v_g (p - 2) (g x)⟫) μ := by
  have hpp : 2 ≤ p := Fact.out
  have := (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).memLp_of_bilin (μ := μ) (p := ENNReal.ofReal p)
    (q := ENNReal.ofReal (Real.conjExponent p)) (r := 1) (Lp.memLp h) (sa16v_g_memLp hpp (Lp.memLp g))
  exact memLp_one_iff_integrable.1 this

lemma sa16v_remainder (f h : Lp V (ENNReal.ofReal p) μ) :
    0 ≤ sa16v_Psi p (f + h) - sa16v_Psi p f - sa16v_D p f h ∧
      sa16v_Psi p (f + h) - sa16v_Psi p f - sa16v_D p f h ≤
        p * ((p - 1) * ((‖f + h‖ + ‖f‖) ^ (p - 2) * ‖f + h - f‖)) * ‖h‖ := by
  have hpp : 2 ≤ p := Fact.out
  have hp1 : 1 < p := by linarith
  have hfh : ∀ᵐ x ∂μ, (f + h : Lp V _ μ) x = f x + h x := Lp.coeFn_add f h
  set r : α → ℝ := fun x => ‖(f + h : Lp V _ μ) x‖ ^ p - ‖f x‖ ^ p - p * ⟪h x, sa16v_g (p - 2) (f x)⟫ with hr
  have hI1 := sa16v_integrable_pow p (f + h)
  have hI2 := sa16v_integrable_pow p f
  have hI3 := sa16v_inner_integrable p h f
  have hI4 := sa16v_inner_integrable p h (f + h)
  have hA : Integrable (fun x => ‖(f + h : Lp V _ μ) x‖ ^ p - ‖f x‖ ^ p) μ := hI1.sub hI2
  have hB : Integrable (fun x => p * ⟪h x, sa16v_g (p - 2) (f x)⟫) μ := hI3.const_mul p
  have hr_int : Integrable r μ := hA.sub hB
  have hint : sa16v_Psi p (f + h) - sa16v_Psi p f - sa16v_D p f h = ∫ x, r x ∂μ := by
    unfold sa16v_Psi
    rw [sa16v_D_apply, hr]
    simp only []
    rw [integral_sub hA hB, integral_sub hI1 hI2, integral_const_mul]
  have hpt1 : ∀ᵐ x ∂μ, 0 ≤ r x := by
    filter_upwards [hfh] with x hx
    have := sa16v_tangent_lower hp1 (f x) (h x)
    simp only [hr]
    rw [hx]
    have c1 : ⟪h x, sa16v_g (p - 2) (f x)⟫ = ⟪sa16v_g (p - 2) (f x), h x⟫ := real_inner_comm _ _
    rw [c1]
    linarith
  have hpt2 : ∀ᵐ x ∂μ, r x ≤ p * ⟪h x, sa16v_g (p - 2) ((f + h : Lp V _ μ) x)⟫ -
      p * ⟪h x, sa16v_g (p - 2) (f x)⟫ := by
    filter_upwards [hfh] with x hx
    have := sa16v_tangent_upper hp1 (f x) (h x)
    simp only [hr]
    rw [hx]
    have c1 : ⟪h x, sa16v_g (p - 2) (f x)⟫ = ⟪sa16v_g (p - 2) (f x), h x⟫ := real_inner_comm _ _
    have c2 : ⟪h x, sa16v_g (p - 2) (f x + h x)⟫ = ⟪sa16v_g (p - 2) (f x + h x), h x⟫ := real_inner_comm _ _
    rw [c1, c2]
    linarith
  refine ⟨?_, ?_⟩
  · rw [hint]; exact integral_nonneg_of_ae hpt1
  · rw [hint]
    have h2 : ∫ x, r x ∂μ ≤ ∫ x, (p * ⟪h x, sa16v_g (p - 2) ((f + h : Lp V _ μ) x)⟫ -
        p * ⟪h x, sa16v_g (p - 2) (f x)⟫) ∂μ :=
      integral_mono_ae hr_int ((hI4.const_mul p).sub hB) hpt2
    refine h2.trans ?_
    rw [integral_sub (hI4.const_mul p) hB, integral_const_mul, integral_const_mul]
    have := sa16v_D_sub_le p (f + h) f h
    rw [sa16v_D_apply, sa16v_D_apply] at this
    linarith

theorem sa16v_hasFDerivAt (f : Lp V (ENNReal.ofReal p) μ) :
    HasFDerivAt (sa16v_Psi p : Lp V (ENNReal.ofReal p) μ → ℝ) (sa16v_D p f) f := by
  have hpp : 2 ≤ p := Fact.out
  have hp0 : 0 ≤ p := by linarith
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  set K : ℝ := p * ((p - 1) * (2 * ‖f‖ + 1) ^ (p - 2)) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ (2 * ‖f‖ + 1) ^ (p - 2) := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ p - 1 := by linarith
    positivity
  set δ : ℝ := min 1 (c / (K + 1)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hc (by linarith))
  filter_upwards [Metric.ball_mem_nhds (0 : Lp V (ENNReal.ofReal p) μ) hδ0] with h hh
  have hh' : ‖h‖ < δ := by simpa using hh
  have hh1 : ‖h‖ ≤ 1 := (hh'.trans_le (min_le_left _ _)).le
  have hh2 : ‖h‖ ≤ c / (K + 1) := (hh'.trans_le (min_le_right _ _)).le
  obtain ⟨hR0, hR1⟩ := sa16v_remainder p f h
  rw [Real.norm_eq_abs, abs_of_nonneg hR0]
  refine hR1.trans ?_
  have e : f + h - f = h := by abel
  rw [e]
  have hsum : ‖f + h‖ + ‖f‖ ≤ 2 * ‖f‖ + 1 := by
    have := norm_add_le f h
    linarith
  have hpow : (‖f + h‖ + ‖f‖) ^ (p - 2) ≤ (2 * ‖f‖ + 1) ^ (p - 2) :=
    Real.rpow_le_rpow (by positivity) hsum (by linarith)
  have hp1 : 0 ≤ p - 1 := by linarith
  calc p * ((p - 1) * ((‖f + h‖ + ‖f‖) ^ (p - 2) * ‖h‖)) * ‖h‖
      ≤ p * ((p - 1) * ((2 * ‖f‖ + 1) ^ (p - 2) * ‖h‖)) * ‖h‖ := by gcongr
    _ = K * ‖h‖ * ‖h‖ := by rw [hK]; ring
    _ ≤ K * (c / (K + 1)) * ‖h‖ := by gcongr
    _ ≤ c * ‖h‖ := by
        have : K * (c / (K + 1)) ≤ c := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

lemma sa16v_D_lip (f f' : Lp V (ENNReal.ofReal p) μ) :
    ‖sa16v_D p f - sa16v_D p f'‖ ≤ p * ((p - 1) * ((‖f‖ + ‖f'‖) ^ (p - 2) * ‖f - f'‖)) := by
  have hpp : 2 ≤ p := Fact.out
  have hC0 : 0 ≤ p * ((p - 1) * ((‖f‖ + ‖f'‖) ^ (p - 2) * ‖f - f'‖)) := by
    have : 0 ≤ p - 1 := by linarith
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun h => ?_
  have h1 := sa16v_D_sub_le p f f' h
  have h2 := sa16v_D_sub_le p f f' (-h)
  rw [map_neg, map_neg, norm_neg] at h2
  rw [ContinuousLinearMap.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [h1, h2]

theorem sa16v_D_continuous : Continuous (sa16v_D p : Lp V (ENNReal.ofReal p) μ → _) := by
  have hpp : 2 ≤ p := Fact.out
  refine continuous_iff_continuousAt.2 fun f => ?_
  refine (tendsto_iff_norm_sub_tendsto_zero (E := Lp V (ENNReal.ofReal p) μ →L[ℝ] ℝ)).2 ?_
  have hc : Continuous (fun f' : Lp V (ENNReal.ofReal p) μ =>
      p * ((p - 1) * ((‖f‖ + ‖f'‖) ^ (p - 2) * ‖f - f'‖))) := by
    have h1 : Continuous (fun f' : Lp V (ENNReal.ofReal p) μ => (‖f‖ + ‖f'‖) ^ (p - 2)) :=
      (continuous_const.add continuous_norm).rpow_const (fun _ => Or.inr (by linarith))
    exact continuous_const.mul (continuous_const.mul (h1.mul (continuous_const.sub continuous_id).norm))
  have h0 := hc.tendsto f
  simp only [sub_self, norm_zero, mul_zero] at h0
  refine squeeze_zero (fun f' => by exact norm_nonneg (sa16v_D p f' - sa16v_D p f)) (fun f' => ?_) h0
  rw [norm_sub_rev]
  exact sa16v_D_lip p f' f |>.trans (le_of_eq (by rw [add_comm, norm_sub_rev]))

end LpDeriv

end HRS.Whole.AppendixA.Phase2SA16V
