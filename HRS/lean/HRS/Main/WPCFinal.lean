import HRS.Main.SpecSW2

/-!
# WPC: proof of `HRS.Main.SpecSW2.weak_reference_pinned_cavity`

Route.  A pinned weight on `n` free coordinates is `pairWeight` on `n + 1` coordinates evaluated at
`Fin.insertNth p y Z`; its one-site kernels are those of the unpinned ensemble at the configuration
`Fin.insertNth p y x` and the site `p.succAbove i`, so the unpinned estimates
`WeakKernel.siteKernel_le`, `WeakKernel.siteKernel_coeff` apply with `N = n + 1`.  The cavity weight is the
`fieldWeight` of the abstract weak specification (`HRS/External/WeakSpec.lean`) with the empty pin, so
`weak_siteKernel_le`, `weak_dobrushin` apply.  The witness matrix is the constant matrix `κ`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.Main.WPC

variable {d : ℕ}

lemma wpc_measurable_insertNth {n : ℕ} (p : Fin (n + 1)) (y : Torus d) :
    Measurable (fun Z : Config d n => Fin.insertNth (α := fun _ => Torus d) p y Z) := by
  refine measurable_pi_iff.2 fun j => ?_
  rcases Fin.eq_self_or_eq_succAbove p j with rfl | ⟨k, rfl⟩
  · simp only [Fin.insertNth_apply_same]; exact measurable_const
  · simp only [Fin.insertNth_apply_succAbove]; exact measurable_pi_apply k

lemma wpc_siteKernel_pinned {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {q : Torus d → Torus d → ℝ} {b : ℝ} {n : ℕ} (hW : Measurable (pairWeight q (n + 1) b μ))
    (p : Fin (n + 1)) (y : Torus d) (i : Fin n) (x : Config d n) :
    External.siteKernel μ (SpecSW2.pinnedWeight q μ b n p y) i x
      = External.siteKernel μ (pairWeight q (n + 1) b μ) (p.succAbove i)
          (Fin.insertNth (α := fun _ => Torus d) p y x) := by
  have hP : Measurable (SpecSW2.pinnedWeight q μ b n p y) :=
    hW.comp (wpc_measurable_insertNth p y)
  have hupd : ∀ (x : Config d n) (z : Torus d),
      Fin.insertNth (α := fun _ => Torus d) p y (Function.update x i z)
        = Function.update (Fin.insertNth (α := fun _ => Torus d) p y x) (p.succAbove i) z :=
    fun x z => Fin.insertNth_update (α := fun _ => Torus d) p y i z x
  rw [External.siteKernel_apply hP, External.siteKernel_apply hW]
  have hn : External.normalizer μ (SpecSW2.pinnedWeight q μ b n p y) i x
      = External.normalizer μ (pairWeight q (n + 1) b μ) (p.succAbove i)
          (Fin.insertNth (α := fun _ => Torus d) p y x) := by
    unfold External.normalizer
    simp only [SpecSW2.pinnedWeight, hupd]
  rw [hn]
  simp only [SpecSW2.pinnedWeight, hupd]

lemma wpc_insertNth_agree {n : ℕ} (p : Fin (n + 1)) (y : Torus d) (j : Fin n) {x x' : Config d n}
    (hxy : ∀ k, k ≠ j → x k = x' k) :
    ∀ k, k ≠ p.succAbove j → Fin.insertNth (α := fun _ => Torus d) p y x k
      = Fin.insertNth (α := fun _ => Torus d) p y x' k := by
  intro k hk
  rcases Fin.eq_self_or_eq_succAbove p k with rfl | ⟨k', rfl⟩
  · simp
  · simp only [Fin.insertNth_apply_succAbove]
    exact hxy k' fun h => hk (by rw [h])

lemma wpc_bounds_of {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {n : ℕ}
    {W : Config d n → ℝ≥0∞} {C κ : ℝ}
    (h1 : ∀ (i : Fin n) (x : Config d n), External.siteKernel μ W i x ≤ ENNReal.ofReal C • μ)
    (h2 : ∀ i j : Fin n, i ≠ j → ∀ x y : Config d n, (∀ k, k ≠ j → x k = y k) →
      ∀ S : Set (Torus d), MeasurableSet S →
        |(External.siteKernel μ W i x).real S - (External.siteKernel μ W i y).real S| ≤ κ)
    (hκ : 0 ≤ κ) (hsum : (n : ℝ) * κ < 1 / 2) :
    SpecSW2.WeakConditionalBounds μ W C κ := by
  refine ⟨h1, fun _ _ => κ, fun _ _ => ⟨hκ, le_rfl⟩, ?_, ?_, h2⟩
  · intro i; simpa using hsum
  · intro j; simpa using hsum


open WeakRef in
/-- Cavity law: one-site kernels, via the abstract weak specification with empty pin. -/
lemma wpc_cavity_bounds {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : ℝ}
    {q : Torus d → Torus d → ℝ} (h : WeakKernel μ a q) (ha : 0 ≤ a) {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    (∀ (i : Fin n) (x : Config d n),
      External.siteKernel μ (SpecSW2.cavityWeight q μ b (n + 1) (n := n)) i x
        ≤ ENNReal.ofReal (Real.exp (b * a + 0 + b * a)) • μ) ∧
    (∀ i j : Fin n, i ≠ j → ∀ x y : Config d n, (∀ k, k ≠ j → x k = y k) →
      ∀ S : Set (Torus d), MeasurableSet S →
        |(External.siteKernel μ (SpecSW2.cavityWeight q μ b (n + 1) (n := n)) i x).real S
          - (External.siteKernel μ (SpecSW2.cavityWeight q μ b (n + 1) (n := n)) i y).real S|
        ≤ 4 * Real.exp (b * a + 0 + b * a) * (b * a) / ((n + 1 : ℕ) : ℝ)) := by
  have iH : Integrable (rowInt q μ) μ :=
    integrable_of_bdd' μ h.measurable_rowInt (M := a) fun z => by
      rw [abs_of_nonneg (h.rowInt_nonneg z)]; exact h.rowInt_le ha z
  let V : External.WeakPotential μ :=
    { φ := fun z => b * rowInt q μ z
      q := q
      M := b * a
      M' := 0
      γ := a
      measurable_φ := h.measurable_rowInt.const_mul b
      measurable_q := h.meas
      q_nonneg := h.nonneg
      q_symm := h.symm
      γ_nonneg := ha
      φ_le := fun x => mul_le_mul_of_nonneg_left (h.rowInt_le ha x) hb
      integrable_φ := iH.const_mul b
      neg_le_integral_φ := by
        have : 0 ≤ ∫ x, b * rowInt q μ x ∂μ :=
          integral_nonneg fun x => mul_nonneg hb (h.rowInt_nonneg x)
        linarith
      integrable_q := h.integrable_row
      row_le := fun x => h.rowInt_le ha x }
  let a0 : Empty → Torus d := fun e => e.elim
  have hlam : 0 ≤ b / ((n + 1 : ℕ) : ℝ) := div_nonneg hb (Nat.cast_nonneg _)
  have hcav : SpecSW2.cavityWeight q μ b (n + 1) (n := n)
      = fun Z => External.fieldWeight V (External.pinField V (b / ((n + 1 : ℕ) : ℝ)) a0)
          (b / ((n + 1 : ℕ) : ℝ)) Z := by
    funext Z
    unfold SpecSW2.cavityWeight External.fieldWeight External.pairEnergy External.pinField
    congr 2
    simp [V, rowInt, Finset.mul_sum]
  have hψ := External.isField_pinField V hlam a0
  have hK0 := (External.fieldNorm_pos hψ.measurable V (b / ((n + 1 : ℕ) : ℝ)) n).ne'
  have hKt := (External.fieldNorm_lt_top (V := V) hψ hlam n).ne
  have hker : ∀ i : Fin n, External.siteKernel μ (SpecSW2.cavityWeight q μ b (n + 1) (n := n)) i
      = External.siteKernel μ (External.pinnedDensity V (b / ((n + 1 : ℕ) : ℝ)) n a0) i := by
    intro i
    rw [hcav]
    unfold External.pinnedDensity External.fieldDensity
    simp only [← div_eq_mul_inv]
    exact (siteKernel_div_const μ _ _ hK0 hKt i).symm
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hN : n + Fintype.card Empty ≤ n + 1 := by simp
  refine ⟨fun i x => ?_, fun i j hij x y hxy S hS => ?_⟩
  · rw [hker i]
    exact External.weak_siteKernel_le V hb hN0 hN a0 i x
  · rw [hker i]
    have := External.weak_dobrushin V hb hN0 hN a0 i j hij x y hxy S hS
    refine this.trans (le_of_eq ?_)
    simp only [External.weakKappa, V]

end HRS.Main.WPC

namespace HRS.Main.SpecSW2

variable {d : ℕ}

theorem weak_reference_pinned_cavity_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℕ → ℝ) (A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → ∀ [IsProbabilityMeasure (withDensityReal ρ)],
        Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
        (∀ k : ℕ, Torus.cbNorm k ρ ≤ Λ k) →
      ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) → (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ n : ℕ, 1 ≤ n → ∀ β ∈ Set.Icc βm βp, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        (∀ (p : Fin (n + 1)) (y : Torus d),
          WeakConditionalBounds (withDensityReal ρ)
            (pinnedWeight q (withDensityReal ρ) (τ * β) n p y) C (C * τ * β * a / ((n + 1 : ℕ) : ℝ))) ∧
        WeakConditionalBounds (withDensityReal ρ)
          (cavityWeight q (withDensityReal ρ) (τ * β) (n + 1) (n := n)) C
          (C * τ * β * a / ((n + 1 : ℕ) : ℝ)) := by
  set P : ℝ := max βp 0 with hP
  have hP0 : 0 ≤ P := le_max_right _ _
  set C : ℝ := 4 * Real.exp (2 * P) with hC
  have hCpos : 0 < C := by positivity
  have hpos : 0 < 4 * C * (P + 1) := by positivity
  refine ⟨min 1 (1 / (4 * C * (P + 1))), C, lt_min one_pos (by positivity), ?_⟩
  intro ρ hρ hprob hsm hc0 hΛ q hqm hqs hq0 hqA a ha0 ha hrow n hn β hβ τ hτ
  have h : WeakRef.WeakKernel (withDensityReal ρ) a q := ⟨hqm, hqs, hq0, hrow⟩
  have ha1 : a < 1 := lt_of_lt_of_le ha (min_le_left _ _)
  have ha2 : a < 1 / (4 * C * (P + 1)) := lt_of_lt_of_le ha (min_le_right _ _)
  have hβpos : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hb0 : 0 ≤ τ * β := mul_nonneg hτ.1 hβpos.le
  have hbP : τ * β ≤ P := by
    have h1 : τ * β ≤ β := by nlinarith [hτ.2]
    have h2 : β ≤ P := hβ.2.trans (le_max_left _ _)
    linarith
  have hba : τ * β * a ≤ P := by nlinarith
  have hexp : Real.exp (2 * (τ * β * a)) ≤ C := by
    have h1 : Real.exp (2 * (τ * β * a)) ≤ Real.exp (2 * P) :=
      Real.exp_le_exp.2 (by linarith)
    have := Real.exp_pos (2 * P)
    rw [hC]; linarith
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set κ : ℝ := C * τ * β * a / ((n + 1 : ℕ) : ℝ) with hκ
  have hκ0 : 0 ≤ κ := by
    rw [hκ]
    refine div_nonneg ?_ hN0.le
    have : C * τ * β * a = C * (τ * β * a) := by ring
    rw [this]
    exact mul_nonneg hCpos.le (mul_nonneg hb0 ha0)
  have hcoeff : 4 * Real.exp (2 * (τ * β * a)) * (τ * β) * a / ((n + 1 : ℕ) : ℝ) ≤ κ := by
    rw [hκ]
    refine div_le_div_of_nonneg_right ?_ hN0.le
    have h1 : 4 * Real.exp (2 * (τ * β * a)) ≤ C := by
      have := Real.exp_pos (2 * (τ * β * a))
      rw [hC]
      have h2 : Real.exp (2 * (τ * β * a)) ≤ Real.exp (2 * P) :=
        Real.exp_le_exp.2 (by linarith)
      linarith
    have h3 : 0 ≤ τ * β * a := mul_nonneg hb0 ha0
    calc 4 * Real.exp (2 * (τ * β * a)) * (τ * β) * a
        = (4 * Real.exp (2 * (τ * β * a))) * (τ * β * a) := by ring
      _ ≤ C * (τ * β * a) := mul_le_mul_of_nonneg_right h1 h3
      _ = C * τ * β * a := by ring
  have hsum : (n : ℝ) * κ < 1 / 2 := by
    have h1 : (n : ℝ) * κ ≤ C * τ * β * a := by
      rw [hκ, ← mul_div_assoc, div_le_iff₀ hN0]
      have h3 : 0 ≤ C * τ * β * a := by
        have := mul_nonneg hb0 ha0
        have : C * τ * β * a = C * (τ * β * a) := by ring
        rw [this]; positivity
      push_cast
      nlinarith
    have h2 : C * τ * β * a ≤ C * (P + 1) * a := by
      have : τ * β ≤ P + 1 := by linarith
      have h4 : C * τ * β * a = C * (τ * β) * a := by ring
      rw [h4]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hCpos.le) ha0
    have h5 : a * (4 * C * (P + 1)) < 1 := by
      rwa [lt_div_iff₀ hpos] at ha2
    nlinarith
  have hW := h.measurable_pairWeight (n + 1) (τ * β)
  refine ⟨fun p y => ?_, ?_⟩
  · refine WPC.wpc_bounds_of (fun i x => ?_) (fun i j hij x' y' hxy S hS => ?_) hκ0 hsum
    · rw [WPC.wpc_siteKernel_pinned hW p y i x]
      exact h.siteKernel_le ha0 hb0 (Nat.succ_pos n) _ _ hexp
    · rw [WPC.wpc_siteKernel_pinned hW p y i x', WPC.wpc_siteKernel_pinned hW p y i y']
      exact (h.siteKernel_coeff ha0 hb0 (Nat.succ_pos n) (p.succAbove i) (p.succAbove j)
        ((Fin.succAbove_right_injective (p := p)).ne hij) _ _
        (WPC.wpc_insertNth_agree p y j hxy) S hS).trans hcoeff
  · obtain ⟨hc1, hc2⟩ := WPC.wpc_cavity_bounds h ha0 hb0 n
    have e : τ * β * a + 0 + τ * β * a = 2 * (τ * β * a) := by ring
    simp only [e] at hc1 hc2
    refine WPC.wpc_bounds_of (fun i x => ?_) (fun i j hij x' y' hxy S hS => ?_) hκ0 hsum
    · refine (hc1 i x).trans ?_
      refine Measure.le_iff.2 fun S hS => ?_
      simp only [Measure.smul_apply, smul_eq_mul]
      gcongr
    · refine (hc2 i j hij x' y' hxy S hS).trans ?_
      calc 4 * Real.exp (2 * (τ * β * a)) * (τ * β * a) / ((n + 1 : ℕ) : ℝ)
          = 4 * Real.exp (2 * (τ * β * a)) * (τ * β) * a / ((n + 1 : ℕ) : ℝ) := by ring
        _ ≤ κ := hcoeff

example := (@weak_reference_pinned_cavity_proof :
  type_of% @HRS.Main.SpecSW2.weak_reference_pinned_cavity)

end HRS.Main.SpecSW2
