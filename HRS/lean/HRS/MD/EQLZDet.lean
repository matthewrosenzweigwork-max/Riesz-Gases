import HRS.PDE.TorusFPExistAux5

/-!
# EQ-LZ shared lemma: finite measures on `(𝕋^n)^ι` are determined by products of smooth functions

If two finite Borel measures `μ, ν` on `ι → Torus n` (`ι` finite) satisfy
`∫ ∏ᵢ gᵢ(zᵢ) dμ = ∫ ∏ᵢ gᵢ(zᵢ) dν` for all families of smooth `gᵢ`, then `μ = ν`.
Proof: the linear span of such products is a subalgebra of `C(ι → 𝕋^n, ℝ)` separating points
(smooth functions are uniformly dense: `d1_exists_smooth_approx`), so it is dense (Stone-Weierstrass), and
`μ`, `ν` are finite; then `ext_of_forall_integral_eq_of_IsFiniteMeasure`.
The corollary `lzdet_ext_single` is the one-factor case, `lzdet_ext_cons` the case `𝕋^n × (𝕋^n)^k`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators

namespace HRS.MD.EQLZDet

variable {n : ℕ}

theorem lzdet_smooth_const (c : ℝ) : Torus.IsSmooth (fun _ : Torus n => c) := d1_isSmooth_const c

theorem lzdet_smooth_mul {f g : Torus n → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) :
    Torus.IsSmooth (fun x => f x * g x) := by
  have e1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  have e2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift g) := hg
  exact e1.mul e2

theorem lzdet_continuous {f : Torus n → ℝ} (hf : Torus.IsSmooth f) : Continuous f :=
  StaticLimitAux.continuous_of_smooth hf

/-- Smooth functions separate the points of the torus. -/
theorem lzdet_separate {a b : Torus n} (hab : a ≠ b) :
    ∃ ψ : Torus n → ℝ, Torus.IsSmooth ψ ∧ ψ a ≠ ψ b := by
  have hd : 0 < dist b a := dist_pos.mpr (Ne.symm hab)
  obtain ⟨ψ, hψ, hψd⟩ := d1_exists_smooth_approx (f := fun x : Torus n => dist x a)
    (continuous_id.dist continuous_const) (half_pos (half_pos hd))
  refine ⟨ψ, hψ, ?_⟩
  intro h
  have h1 := hψd a
  have h2 := hψd b
  simp only [dist_self] at h1
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

variable {ι : Type} [Fintype ι]

/-- The pure product `z ↦ ∏ᵢ gᵢ(zᵢ)`. -/
def lzdetProd (g : ι → Torus n → ℝ) (z : ι → Torus n) : ℝ := ∏ i, g i (z i)

theorem lzdetProd_continuous {g : ι → Torus n → ℝ} (hg : ∀ i, Torus.IsSmooth (g i)) :
    Continuous (lzdetProd g) :=
  continuous_finsetProd _ fun i _ => (lzdet_continuous (hg i)).comp (continuous_apply i)

/-- The set of pure products of smooth functions, inside `C(ι → 𝕋^n, ℝ)`. -/
def lzdetSet (ι : Type) [Fintype ι] (n : ℕ) : Set C(ι → Torus n, ℝ) :=
  {f | ∃ g : ι → Torus n → ℝ, (∀ i, Torus.IsSmooth (g i)) ∧ ∀ z, f z = lzdetProd g z}

theorem lzdetSet_one : (1 : C(ι → Torus n, ℝ)) ∈ lzdetSet ι n :=
  ⟨fun _ _ => 1, fun _ => lzdet_smooth_const 1, fun z => by simp [lzdetProd]⟩

theorem lzdetSet_mul {f₁ f₂ : C(ι → Torus n, ℝ)} (h₁ : f₁ ∈ lzdetSet ι n) (h₂ : f₂ ∈ lzdetSet ι n) :
    f₁ * f₂ ∈ lzdetSet ι n := by
  obtain ⟨g₁, hg₁, e₁⟩ := h₁
  obtain ⟨g₂, hg₂, e₂⟩ := h₂
  refine ⟨fun i x => g₁ i x * g₂ i x, fun i => lzdet_smooth_mul (hg₁ i) (hg₂ i), fun z => ?_⟩
  simp only [ContinuousMap.mul_apply, e₁, e₂, lzdetProd, Finset.prod_mul_distrib]

theorem lzdet_span_mul {f₁ f₂ : C(ι → Torus n, ℝ)} (h₁ : f₁ ∈ Submodule.span ℝ (lzdetSet ι n))
    (h₂ : f₂ ∈ Submodule.span ℝ (lzdetSet ι n)) : f₁ * f₂ ∈ Submodule.span ℝ (lzdetSet ι n) := by
  induction h₁ using Submodule.span_induction with
  | mem x hx =>
    induction h₂ using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (lzdetSet_mul hx hy)
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

/-- The subalgebra of `C(ι → 𝕋^n, ℝ)` spanned by the pure products of smooth functions. -/
def lzdetAlg (ι : Type) [Fintype ι] (n : ℕ) : Subalgebra ℝ C(ι → Torus n, ℝ) :=
  (Submodule.span ℝ (lzdetSet ι n)).toSubalgebra (Submodule.subset_span lzdetSet_one)
    (fun _ _ => lzdet_span_mul)

theorem lzdetAlg_separates : (lzdetAlg ι n).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  obtain ⟨ψ, hψ, hψxy⟩ := lzdet_separate hi
  let g : ι → Torus n → ℝ := fun j => if j = i then ψ else fun _ => 1
  have hg : ∀ j, Torus.IsSmooth (g j) := by
    intro j
    by_cases hj : j = i
    · simp only [g, if_pos hj]; exact hψ
    · simp only [g, if_neg hj]; exact lzdet_smooth_const 1
  have hprod : ∀ z : ι → Torus n, lzdetProd g z = ψ (z i) := by
    intro z
    simp only [lzdetProd, g]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  let f : C(ι → Torus n, ℝ) := ⟨lzdetProd g, lzdetProd_continuous hg⟩
  have hf : f ∈ lzdetAlg ι n :=
    Submodule.subset_span ⟨g, hg, fun z => rfl⟩
  refine ⟨f, ⟨f, hf, rfl⟩, ?_⟩
  show lzdetProd g x ≠ lzdetProd g y
  rw [hprod, hprod]
  exact hψxy

/-- **Determination by pure products of smooth functions.** -/
theorem lzdet_ext {μ ν : Measure (ι → Torus n)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ g : ι → Torus n → ℝ, (∀ i, Torus.IsSmooth (g i)) →
      ∫ z, ∏ i, g i (z i) ∂μ = ∫ z, ∏ i, g i (z i) ∂ν) : μ = ν := by
  have : SecondCountableTopology (Torus n) := inferInstance
  have : BorelSpace (Torus n) := inferInstance
  have : BorelSpace (ι → Torus n) := Pi.borelSpace
  have : HasOuterApproxClosed (ι → Torus n) := inferInstance
  have hint : ∀ (f : C(ι → Torus n, ℝ)) (ρ : Measure (ι → Torus n)) [IsFiniteMeasure ρ],
      Integrable (fun z => f z) ρ := by
    intro f ρ _
    exact (BoundedContinuousFunction.mkOfCompact f).integrable ρ
  -- the identity on the span
  have hspan : ∀ f ∈ Submodule.span ℝ (lzdetSet ι n), ∫ z, f z ∂μ = ∫ z, f z ∂ν := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, e⟩ := hx
      have := h g hg
      simpa only [e, lzdetProd] using this
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [ContinuousMap.add_apply]
      rw [integral_add (hint x μ) (hint y μ), integral_add (hint x ν) (hint y ν), hx, hy]
    | smul a x _ hx =>
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul, hx]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro fb
  set f : C(ι → Torus n, ℝ) := fb.toContinuousMap with hfdef
  show ∫ z, f z ∂μ = ∫ z, f z ∂ν
  by_contra hne
  set D := ∫ z, f z ∂μ - ∫ z, f z ∂ν with hD
  have hDpos : 0 < |D| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set C : ℝ := μ.real Set.univ + ν.real Set.univ + 1 with hC
  have hCpos : 0 < C := by
    have := measureReal_nonneg (μ := μ) (s := Set.univ)
    have := measureReal_nonneg (μ := ν) (s := Set.univ)
    linarith
  obtain ⟨a, ha⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (lzdetAlg ι n) lzdetAlg_separates f (|D| / (2 * C)) (by positivity)
  have haspan : (a : C(ι → Torus n, ℝ)) ∈ Submodule.span ℝ (lzdetSet ι n) := a.2
  have hb : ∀ (ρ : Measure (ι → Torus n)) [IsFiniteMeasure ρ],
      |∫ z, f z ∂ρ - ∫ z, (a : C(ι → Torus n, ℝ)) z ∂ρ| ≤ |D| / (2 * C) * ρ.real Set.univ := by
    intro ρ _
    rw [← integral_sub (hint f ρ) (hint a ρ)]
    have := norm_integral_le_of_norm_le_const (μ := ρ) (f := fun z => f z - (a : C(ι → Torus n, ℝ)) z)
      (C := |D| / (2 * C)) (Filter.Eventually.of_forall fun z => by
        have h1 := ContinuousMap.norm_coe_le_norm ((a : C(ι → Torus n, ℝ)) - f) z
        simp only [ContinuousMap.sub_apply, Real.norm_eq_abs] at h1 ⊢
        rw [abs_sub_comm]
        exact h1.trans ha.le)
    simpa [Real.norm_eq_abs] using this
  have h1 := hb μ
  have h2 := hb ν
  have h3 := hspan _ haspan
  have hD2 : |D| ≤ |D| / (2 * C) * (μ.real Set.univ + ν.real Set.univ) := by
    have : D = (∫ z, f z ∂μ - ∫ z, (a : C(ι → Torus n, ℝ)) z ∂μ) -
        (∫ z, f z ∂ν - ∫ z, (a : C(ι → Torus n, ℝ)) z ∂ν) := by rw [hD]; linarith [h3]
    have hle : |D| ≤ |∫ z, f z ∂μ - ∫ z, (a : C(ι → Torus n, ℝ)) z ∂μ| +
        |∫ z, f z ∂ν - ∫ z, (a : C(ι → Torus n, ℝ)) z ∂ν| := by
      calc |D| = |(∫ z, f z ∂μ - ∫ z, (a : C(ι → Torus n, ℝ)) z ∂μ) -
            (∫ z, f z ∂ν - ∫ z, (a : C(ι → Torus n, ℝ)) z ∂ν)| := by rw [← this]
        _ ≤ _ := abs_sub _ _
    calc |D| ≤ _ := hle
      _ ≤ |D| / (2 * C) * μ.real Set.univ + |D| / (2 * C) * ν.real Set.univ := add_le_add h1 h2
      _ = _ := by ring
  have hmu := measureReal_nonneg (μ := μ) (s := Set.univ)
  have hnu := measureReal_nonneg (μ := ν) (s := Set.univ)
  have : |D| / (2 * C) * (μ.real Set.univ + ν.real Set.univ) ≤ |D| / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (μ.real Set.univ + ν.real Set.univ) ≤ C := by rw [hC]; linarith
    nlinarith [abs_nonneg D]
  linarith

/-- One factor: finite measures on `𝕋^n` are determined by smooth test functions. -/
theorem lzdet_ext_single {μ ν : Measure (Torus n)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ g : Torus n → ℝ, Torus.IsSmooth g → ∫ x, g x ∂μ = ∫ x, g x ∂ν) : μ = ν := by
  let e : Torus n → (Fin 1 → Torus n) := fun x _ => x
  have he : Measurable e := measurable_pi_iff.mpr fun _ => measurable_id
  have hev : Measurable (fun z : Fin 1 → Torus n => z 0) := measurable_pi_apply 0
  have hcomp : (fun z : Fin 1 → Torus n => z 0) ∘ e = id := rfl
  have key : μ.map e = ν.map e := by
    apply lzdet_ext
    intro g hg
    rw [integral_map he.aemeasurable, integral_map he.aemeasurable]
    · simpa [e] using h (g 0) (hg 0)
    · exact (lzdetProd_continuous hg).aestronglyMeasurable
    · exact (lzdetProd_continuous hg).aestronglyMeasurable
  have := congrArg (fun m => m.map (fun z : Fin 1 → Torus n => z 0)) key
  simpa only [Measure.map_map hev he, hcomp, Measure.map_id] using this

/-- First factor separated: finite measures on `𝕋^n × (𝕋^n)^k` are determined by `g₀(x) ∏ᵢ gᵢ(yᵢ)`. -/
theorem lzdet_ext_cons {k : ℕ} {μ ν : Measure (Torus n × (Fin k → Torus n))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (g₀ : Torus n → ℝ) (g : Fin k → Torus n → ℝ), Torus.IsSmooth g₀ → (∀ i, Torus.IsSmooth (g i)) →
      ∫ p, g₀ p.1 * ∏ i, g i (p.2 i) ∂μ = ∫ p, g₀ p.1 * ∏ i, g i (p.2 i) ∂ν) : μ = ν := by
  let e : Torus n × (Fin k → Torus n) → (Fin (k + 1) → Torus n) := fun p => Fin.cons p.1 p.2
  let e' : (Fin (k + 1) → Torus n) → Torus n × (Fin k → Torus n) := fun w => (w 0, fun i => w i.succ)
  have he : Measurable e := by
    refine measurable_pi_iff.mpr fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [e] using measurable_fst
    · simp only [e, Fin.cons_succ]
      exact (measurable_pi_apply j).comp measurable_snd
  have he' : Measurable e' :=
    (measurable_pi_apply 0).prodMk (measurable_pi_iff.mpr fun i => measurable_pi_apply i.succ)
  have hcomp : e' ∘ e = id := by
    funext p
    simp [e, e']
  have key : μ.map e = ν.map e := by
    apply lzdet_ext
    intro G hG
    have hc : Continuous (fun z : Fin (k + 1) → Torus n => ∏ i, G i (z i)) := lzdetProd_continuous hG
    rw [integral_map he.aemeasurable hc.aestronglyMeasurable,
      integral_map he.aemeasurable hc.aestronglyMeasurable]
    have := h (G 0) (fun i => G i.succ) (hG 0) (fun i => hG i.succ)
    simpa [e, Fin.prod_univ_succ] using this
  have := congrArg (fun m => m.map e') key
  simpa only [Measure.map_map he' he, hcomp, Measure.map_id] using this

/-! ### Integrability helpers -/

theorem lzdet_integrable_cont {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {f : X → ℝ} (hf : Continuous f) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable f μ :=
  (BoundedContinuousFunction.mkOfCompact (⟨f, hf⟩ : C(X, ℝ))).integrable μ

theorem lzdet_integrable_comp {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {f : X → ℝ} (hf : Continuous f) {Z : Ω → X} (hZ : Measurable Z) :
    Integrable (fun ω => f (Z ω)) P :=
  (integrable_map_measure hf.aestronglyMeasurable hZ.aemeasurable).mp (lzdet_integrable_cont hf _)

theorem lzdet_bdd {f : Torus n → ℝ} (hf : Continuous f) : ∃ C : ℝ, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus n)).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩

end HRS.MD.EQLZDet

end
