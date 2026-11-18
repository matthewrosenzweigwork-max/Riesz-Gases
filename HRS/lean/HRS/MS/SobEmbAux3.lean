import HRS.MS.SobEmbAux2

/-!
# SA1, Aux3: Hölder interpolation and the Sobolev ladder `Reach`

* `sa1_interp`: `‖g‖_r ≤ ‖g‖_a + ‖g‖_b` for `0 < a ≤ r ≤ b`.
* `sa1_Reach a₀ j r`: `‖D^i f‖_r ≤ C Σ_{t ≤ j} ‖D^{i+t} f‖_{a₀}` for all smooth `f` and all `i`.
* `sa1_reach_all`: for `a₀ ≥ 1`, `Reach a₀ j r` holds whenever `a₀ ≤ r` and `1/r ≥ 1/a₀ - j/d`.
-/

noncomputable section

open MeasureTheory Filter Topology Module
open scoped ENNReal NNReal ContDiff

namespace HRS.SA1

variable {d : ℕ}

instance sa1_fd (i : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin d)) ℝ) :=
  Module.Finite.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ) (A := ℝ) (ι := Fin i)
      (M₁ := fun _ : Fin i => EuclideanSpace ℝ (Fin d)) (M₂ := ℝ))
    (fun _ _ h => ContinuousMultilinearMap.toMultilinearMap_injective h)

/-- Hölder interpolation: `‖g‖_r ≤ ‖g‖_a + ‖g‖_b` for `0 < a ≤ r ≤ b`. -/
theorem sa1_interp {α G : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup G]
    (g : α → G) (hg : AEStronglyMeasurable g μ) {a r b : ℝ} (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) :
    eLpNorm g (ENNReal.ofReal r) μ ≤ eLpNorm g (ENNReal.ofReal a) μ + eLpNorm g (ENNReal.ofReal b) μ := by
  rcases har.eq_or_lt with rfl | h1
  · exact le_self_add
  rcases hrb.eq_or_lt with rfl | h2
  · exact le_add_self
  have hr : 0 < r := ha.trans h1
  have hb : 0 < b := hr.trans h2
  have hab : 1 / b < 1 / a := one_div_lt_one_div_of_lt ha (h1.trans h2)
  set θ : ℝ := (1 / r - 1 / b) / (1 / a - 1 / b) with hθ
  have hden : 0 < 1 / a - 1 / b := by linarith
  have hθ0 : 0 < θ := div_pos (by have := one_div_lt_one_div_of_lt hr h2; linarith) hden
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one hden]
    have := one_div_lt_one_div_of_lt ha h1
    linarith
  have hθeq : θ / a + (1 - θ) / b = 1 / r := by
    have e := div_mul_cancel₀ (1 / r - 1 / b) hden.ne'
    calc θ / a + (1 - θ) / b = θ * (1 / a - 1 / b) + 1 / b := by ring
      _ = 1 / r := by rw [hθ, e]; ring
  set p : ℝ := a / θ with hp
  set q : ℝ := b / (1 - θ) with hq
  have hp0 : 0 < p := div_pos ha hθ0
  have hq0 : 0 < q := div_pos hb (by linarith)
  have hpq : p⁻¹ + q⁻¹ = r⁻¹ := by
    rw [hp, hq, inv_div, inv_div, hθeq, one_div]
  have hholder : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) (ENNReal.ofReal r) := by
    refine ⟨?_⟩
    rw [← ENNReal.ofReal_inv_of_pos hp0, ← ENNReal.ofReal_inv_of_pos hq0, ← ENNReal.ofReal_inv_of_pos hr,
      ← ENNReal.ofReal_add (inv_nonneg.2 hp0.le) (inv_nonneg.2 hq0.le), hpq]
  have hgc : AEStronglyMeasurable (fun x => ‖g x‖) μ := hg.norm
  have hf1 : AEStronglyMeasurable (fun x => ‖g x‖ ^ θ) μ :=
    (Real.continuous_rpow_const hθ0.le).comp_aestronglyMeasurable hgc
  have hf2 : AEStronglyMeasurable (fun x => ‖g x‖ ^ (1 - θ)) μ :=
    (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 - θ)).comp_aestronglyMeasurable hgc
  have hprod : eLpNorm g (ENNReal.ofReal r) μ =
      eLpNorm (fun x => (fun s t : ℝ => s * t) (‖g x‖ ^ θ) (‖g x‖ ^ (1 - θ))) (ENNReal.ofReal r) μ := by
    rw [← eLpNorm_norm g hg]
    congr 1
    funext x
    simp only
    rw [← Real.rpow_add' (norm_nonneg _) (by linarith)]
    simp
  have hH := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := ENNReal.ofReal p) (q := ENNReal.ofReal q)
    (r := ENNReal.ofReal r) (μ := μ) (f := fun x => ‖g x‖ ^ θ) (g := fun x => ‖g x‖ ^ (1 - θ))
    (fun s t : ℝ => s * t) 1 continuous_mul hf1 hf2
    (Eventually.of_forall fun x => by simp [norm_mul])
  have e1 : eLpNorm (fun x => ‖g x‖ ^ θ) (ENNReal.ofReal p) μ = eLpNorm g (ENNReal.ofReal a) μ ^ θ := by
    rw [eLpNorm_norm_rpow g hg hθ0, ← ENNReal.ofReal_mul hp0.le, hp, div_mul_cancel₀ _ hθ0.ne']
  have e2 : eLpNorm (fun x => ‖g x‖ ^ (1 - θ)) (ENNReal.ofReal q) μ = eLpNorm g (ENNReal.ofReal b) μ ^ (1 - θ) := by
    have h1θ : 0 < 1 - θ := by linarith
    rw [eLpNorm_norm_rpow g hg h1θ, ← ENNReal.ofReal_mul hq0.le, hq, div_mul_cancel₀ _ h1θ.ne']
  rw [hprod]
  refine hH.trans ?_
  rw [e1, e2]
  simp only [ENNReal.coe_one, one_mul]
  exact sa1_amgm _ _ hθ0.le hθ1.le


/-- Real-exponent version of `sa1_step`. -/
theorem sa1_step_real {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {q q' γ : ℝ} (hq : 1 ≤ q) (hqd : q < d) (hq'0 : 0 < q') (hq' : q'⁻¹ = q⁻¹ - (d : ℝ)⁻¹)
    (hγ : 1 ≤ γ) :
    ∃ K : ℝ≥0, ∀ u : EuclideanSpace ℝ (Fin d) → F, ContDiff ℝ 1 u →
      eLpNorm u (ENNReal.ofReal (γ * q')) volume ≤
        K * (eLpNorm u (ENNReal.ofReal (γ * q)) volume +
          eLpNorm (fderiv ℝ u) (ENNReal.ofReal (γ * q)) volume) := by
  have hγ0 : 0 ≤ γ := by linarith
  have hq1 : 1 ≤ q.toNNReal := by
    rw [← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal hq
  have hqd' : (q.toNNReal : ℝ) < d := by rw [Real.coe_toNNReal _ (by linarith)]; exact hqd
  have hq'' : (q'.toNNReal : ℝ)⁻¹ = (q.toNNReal : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
    rw [Real.coe_toNNReal _ hq'0.le, Real.coe_toNNReal _ (by linarith)]; exact hq'
  have hγ' : 1 ≤ γ.toNNReal := by
    rw [← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal hγ
  obtain ⟨K, -, hK⟩ := sa1_step (F := F) (d := d) hq1 hqd' hq'' hγ'
  refine ⟨K, fun u hu => ?_⟩
  have h := hK u hu
  have e1 : ENNReal.ofReal (γ * q') = (((γ.toNNReal * q'.toNNReal : ℝ≥0)) : ℝ≥0∞) := by
    rw [ENNReal.ofReal, Real.toNNReal_mul hγ0]
  have e2 : ENNReal.ofReal (γ * q) = (((γ.toNNReal * q.toNNReal : ℝ≥0)) : ℝ≥0∞) := by
    rw [ENNReal.ofReal, Real.toNNReal_mul hγ0]
  rw [e1, e2]
  exact h

/-- the `L^r` norm of `D^i f` -/
def sa1_nrm (i : ℕ) (r : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  eLpNorm (iteratedFDeriv ℝ i f) (ENNReal.ofReal r) volume

/-- `‖D^i f‖_r ≤ C_i Σ_{t ≤ j} ‖D^{i+t} f‖_{a₀}` for all smooth `f` (constants depend on `i`). -/
def sa1_Reach (d : ℕ) (a0 : ℝ) (j : ℕ) (r : ℝ) : Prop :=
  ∀ i : ℕ, ∃ C : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ f →
    sa1_nrm i r f ≤ C * ∑ t ∈ Finset.range (j + 1), sa1_nrm (i + t) a0 f

theorem sa1_top_le (k : ℕ) : ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

theorem sa1_cont_iter {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f) (i : ℕ) :
    Continuous (iteratedFDeriv ℝ i f) := hf.continuous_iteratedFDeriv (sa1_top_le i)

theorem sa1_smooth_iter {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f) (i : ℕ) :
    ContDiff ℝ ∞ (iteratedFDeriv ℝ i f) := hf.iteratedFDeriv_right (by simp)

theorem sa1_nrm_succ {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f) (i : ℕ) (p : ℝ≥0∞) :
    eLpNorm (fderiv ℝ (iteratedFDeriv ℝ i f)) p volume = eLpNorm (iteratedFDeriv ℝ (i + 1) f) p volume :=
  eLpNorm_congr_norm_ae ((sa1_smooth_iter hf i).continuous_fderiv (by simp)).aestronglyMeasurable
    (sa1_cont_iter hf (i + 1)).aestronglyMeasurable (Eventually.of_forall fun x => norm_fderiv_iteratedFDeriv)

theorem sa1_reach_self (a0 : ℝ) (j : ℕ) : sa1_Reach d a0 j a0 := by
  intro i
  refine ⟨1, fun f _ => ?_⟩
  rw [ENNReal.coe_one, one_mul]
  have := Finset.single_le_sum (f := fun t => sa1_nrm (i + t) a0 f) (fun _ _ => zero_le)
    (Finset.mem_range.2 (Nat.succ_pos j) : 0 ∈ Finset.range (j + 1))
  simpa using this

theorem sa1_reach_mono {a0 : ℝ} {j : ℕ} {r : ℝ} (h : sa1_Reach d a0 j r) : sa1_Reach d a0 (j + 1) r := by
  intro i
  obtain ⟨C, hC⟩ := h i
  refine ⟨C, fun f hf => (hC f hf).trans ?_⟩
  refine mul_le_mul le_rfl ?_ (zero_le) (zero_le)
  exact Finset.sum_le_sum_of_subset (f := fun t => sa1_nrm (i + t) a0 f) (Finset.range_mono (Nat.le_succ _))

theorem sa1_reach_interp {a0 : ℝ} {j : ℕ} {r1 r r2 : ℝ} (h1 : sa1_Reach d a0 j r1) (h2 : sa1_Reach d a0 j r2)
    (hr1 : 0 < r1) (hr1r : r1 ≤ r) (hrr2 : r ≤ r2) : sa1_Reach d a0 j r := by
  intro i
  obtain ⟨C1, hC1⟩ := h1 i
  obtain ⟨C2, hC2⟩ := h2 i
  refine ⟨C1 + C2, fun f hf => ?_⟩
  have h := sa1_interp (iteratedFDeriv ℝ i f) (sa1_cont_iter hf i).aestronglyMeasurable (μ := volume)
    hr1 hr1r hrr2
  have h' : sa1_nrm i r f ≤ sa1_nrm i r1 f + sa1_nrm i r2 f := h
  refine h'.trans ?_
  have := add_le_add (hC1 f hf) (hC2 f hf)
  rw [← add_mul] at this
  simpa using this


/-- One ladder step: `Reach j (γq) → Reach (j+1) (γq')`. -/
theorem sa1_reach_step {a0 : ℝ} {j : ℕ} {q q' γ : ℝ} (hq : 1 ≤ q) (hqd : q < d) (hq'0 : 0 < q')
    (hq' : q'⁻¹ = q⁻¹ - (d : ℝ)⁻¹) (hγ : 1 ≤ γ) (h : sa1_Reach d a0 j (γ * q)) :
    sa1_Reach d a0 (j + 1) (γ * q') := by
  intro i
  obtain ⟨K, hK⟩ := sa1_step_real (F := ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin d)) ℝ)
    (d := d) hq hqd hq'0 hq' hγ
  obtain ⟨C0, hC0⟩ := h i
  obtain ⟨C1, hC1⟩ := h (i + 1)
  refine ⟨K * (C0 + C1), fun f hf => ?_⟩
  have h1 := hK (iteratedFDeriv ℝ i f) ((sa1_smooth_iter hf i).of_le (by simp))
  rw [sa1_nrm_succ hf] at h1
  have hs0 : ∑ t ∈ Finset.range (j + 1), sa1_nrm (i + t) a0 f ≤
      ∑ t ∈ Finset.range (j + 1 + 1), sa1_nrm (i + t) a0 f :=
    Finset.sum_le_sum_of_subset (f := fun t => sa1_nrm (i + t) a0 f) (Finset.range_mono (Nat.le_succ _))
  have hs1 : ∑ t ∈ Finset.range (j + 1), sa1_nrm (i + 1 + t) a0 f ≤
      ∑ t ∈ Finset.range (j + 1 + 1), sa1_nrm (i + t) a0 f := by
    rw [Finset.sum_range_succ' (fun t => sa1_nrm (i + t) a0 f) (j + 1)]
    refine le_trans (le_of_eq ?_) le_self_add
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show i + 1 + t = i + (t + 1) by ring]
  have e0 := hC0 f hf
  have e1 := hC1 f hf
  calc sa1_nrm i (γ * q') f ≤ K * (sa1_nrm i (γ * q) f + sa1_nrm (i + 1) (γ * q) f) := h1
    _ ≤ K * (C0 * ∑ t ∈ Finset.range (j + 1 + 1), sa1_nrm (i + t) a0 f +
          C1 * ∑ t ∈ Finset.range (j + 1 + 1), sa1_nrm (i + t) a0 f) := by
        gcongr
        · exact e0.trans (by gcongr)
        · exact e1.trans (by gcongr)
    _ = ((K * (C0 + C1) : ℝ≥0) : ℝ≥0∞) * ∑ t ∈ Finset.range (j + 1 + 1), sa1_nrm (i + t) a0 f := by
        push_cast; ring


theorem sa1_reach_coreA (hd : 2 ≤ d) {a0 : ℝ} {j : ℕ} {a r : ℝ} (ha : 1 ≤ a) (hR : sa1_Reach d a0 j a)
    (hr : 0 < r) (h1 : 1 / r ≤ 1 / a - 1 / a / d) (h2 : 1 / a - 1 / d ≤ 1 / r) :
    sa1_Reach d a0 (j + 1) r := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha0 : 0 < a := by linarith
  have hz : 0 < 1 / r := by positivity
  set x : ℝ := 1 / a with hx
  set z : ℝ := 1 / r with hz'
  have hax : a * x = 1 := by rw [hx]; field_simp
  have hrz : r * z = 1 := by rw [hz']; field_simp
  have hx0 : 0 < x := by positivity
  have hxd : 0 < x / d := by positivity
  set τ : ℝ := d * (x - z) with hτ
  have hτ0 : 0 < τ := by
    rw [hτ]; apply mul_pos (by linarith); linarith
  have haτ1 : 1 ≤ a * τ := by
    have : x / d ≤ x - z := by linarith
    have h3 : x ≤ d * (x - z) := by
      rw [div_le_iff₀ (by linarith)] at this; linarith
    calc (1 : ℝ) = a * x := hax.symm
      _ ≤ a * τ := by rw [hτ]; exact mul_le_mul_of_nonneg_left h3 ha0.le
  have haτd : a * τ < d := by
    have : a * τ = d * (1 - a * z) := by rw [hτ]; nlinarith [hax]
    have haz : 0 < a * z := by positivity
    rw [this]; nlinarith
  have hτ1 : τ ≤ 1 := by
    have h6 : x - z ≤ 1 / d := by linarith
    rw [le_div_iff₀ (by linarith)] at h6
    rw [hτ]; linarith
  have hdaτ : 0 < (d : ℝ) - a * τ := by linarith
  set γ : ℝ := 1 / τ with hγ
  set q : ℝ := a * τ with hq
  set q' : ℝ := a * τ * d / (d - a * τ) with hq'
  have hγ1 : 1 ≤ γ := by rw [hγ, le_div_iff₀ hτ0]; linarith
  have hq'0 : 0 < q' := by rw [hq']; positivity
  have hq'inv : q'⁻¹ = q⁻¹ - (d : ℝ)⁻¹ := by
    rw [hq', hq]
    have : (a * τ) ≠ 0 := by positivity
    have : (d : ℝ) ≠ 0 := by positivity
    have : (d : ℝ) - a * τ ≠ 0 := hdaτ.ne'
    field_simp
  have hγq : γ * q = a := by rw [hγ, hq]; field_simp
  have hγq' : γ * q' = r := by
    have hdaz : (d : ℝ) - a * τ = d * a * z := by
      rw [hτ]
      have : a * (d * (x - z)) = d * (a * x) - d * a * z := by ring
      rw [this, hax]; ring
    rw [hγ, hq']
    have h5 : τ ≠ 0 := hτ0.ne'
    rw [hdaz]
    have : (d : ℝ) ≠ 0 := by positivity
    have : z ≠ 0 := hz.ne'
    have : a ≠ 0 := ha0.ne'
    field_simp
    nlinarith [hrz]
  have := sa1_reach_step (d := d) (a0 := a0) (j := j) (q := q) (q' := q') (γ := γ) haτ1 haτd hq'0 hq'inv hγ1
    (by rw [hγq]; exact hR)
  rwa [hγq'] at this


theorem sa1_reach_core (hd : 2 ≤ d) {a0 : ℝ} {j : ℕ} {a r : ℝ} (ha : 1 ≤ a) (hR : sa1_Reach d a0 j a)
    (hr : 0 < r) (hlt : 1 / r < 1 / a) (hge : 1 / a - 1 / d ≤ 1 / r) : sa1_Reach d a0 (j + 1) r := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha0 : 0 < a := by linarith
  by_cases hA : 1 / r ≤ 1 / a - 1 / a / d
  · exact sa1_reach_coreA hd ha hR hr hA hge
  · push Not at hA
    set x : ℝ := 1 / a with hx
    have hx0 : 0 < x := by positivity
    have hx1 : x ≤ 1 := by rw [hx, div_le_one ha0]; exact ha
    have hw : 0 < x - x / d := by
      have : x / d < x := div_lt_self hx0 (by linarith)
      linarith
    set r2 : ℝ := 1 / (x - x / d) with hr2
    have hr20 : 0 < r2 := by positivity
    have hr2z : 1 / r2 = x - x / d := by rw [hr2, one_div_one_div]
    have hR2 : sa1_Reach d a0 (j + 1) r2 := by
      refine sa1_reach_coreA hd ha hR hr20 (by rw [hr2z]) ?_
      rw [hr2z]
      have : x / d ≤ 1 / d := div_le_div_of_nonneg_right hx1 (by linarith)
      linarith
    have har : a ≤ r := by
      have := (one_div_lt_one_div hr ha0).1 hlt
      exact this.le
    have hrr2 : r ≤ r2 := by
      have : 1 / r2 ≤ 1 / r := by rw [hr2z]; exact hA.le
      exact (one_div_le_one_div hr20 hr).1 this
    exact sa1_reach_interp (sa1_reach_mono hR) hR2 ha0 har hrr2

/-- The ladder: for `a₀ ≥ 1`, `‖D^i f‖_r ≤ C_i Σ_{t ≤ j} ‖D^{i+t} f‖_{a₀}` whenever `a₀ ≤ r` and `1/r ≥ 1/a₀ - j/d`. -/
theorem sa1_reach_all (hd : 2 ≤ d) {a0 : ℝ} (ha0 : 1 ≤ a0) :
    ∀ j : ℕ, ∀ r : ℝ, a0 ≤ r → 1 / a0 - (j : ℝ) / d ≤ 1 / r → sa1_Reach d a0 j r := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  intro j
  induction j with
  | zero =>
    intro r h1 h2
    have hr : 0 < r := by linarith
    have : r ≤ a0 := by
      simp only [Nat.cast_zero, zero_div, sub_zero] at h2
      exact (one_div_le_one_div (show (0 : ℝ) < a0 by linarith) hr).1 h2
    have : r = a0 := le_antisymm this h1
    subst this
    exact sa1_reach_self r 0
  | succ j ih =>
    intro r h1 h2
    have hr : 0 < r := by linarith
    by_cases hc : 1 / a0 - (j : ℝ) / d ≤ 1 / r
    · exact sa1_reach_mono (ih r h1 hc)
    · push Not at hc
      set x : ℝ := 1 / a0 - (j : ℝ) / d with hx
      have hxr : 0 < x := lt_trans (by positivity) hc
      have hxa : x ≤ 1 / a0 := by
        rw [hx]; have : (0 : ℝ) ≤ (j : ℝ) / d := by positivity
        linarith
      set r1 : ℝ := 1 / x with hr1
      have hr10 : 0 < r1 := by positivity
      have hr1x : 1 / r1 = x := by rw [hr1, one_div_one_div]
      have ha0r1 : a0 ≤ r1 := by
        have h3 : 1 / r1 ≤ 1 / a0 := by rw [hr1x]; exact hxa
        exact (one_div_le_one_div hr10 (by linarith)).1 h3
      have hR1 : sa1_Reach d a0 j r1 := ih r1 ha0r1 (by rw [hr1x])
      refine sa1_reach_core hd (by linarith) hR1 hr (by rw [hr1x]; exact hc) ?_
      rw [hr1x, hx]
      push_cast at h2
      have : (1 : ℝ) / a0 - ((j : ℝ) + 1) / d = 1 / a0 - (j : ℝ) / d - 1 / d := by ring
      linarith

end HRS.SA1
