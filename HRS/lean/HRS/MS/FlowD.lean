import HRS.MS.FlowDAux1
import HRS.MS.FlowDAux2

/-!
# MS-FLOW-D: conjuncts (iii), (iv) of Lemma S.A.32

`flow_covering_separation`: elementary consequences of a bi-Lipschitz bijection `Ψ τ` with Lipschitz
inverse; the constant depends on `d` and `Λ` only.  Route: `FlowDPlan.md`.
-/

open Set MeasureTheory
open scoped ENNReal ContDiff
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

namespace HRS.MS.FlowD

theorem continuous_of_lip {d : ℕ} (K : ℝ) (hK : 0 ≤ K) (f : Euc d → Euc d)
    (h : ∀ y y', ‖f y - f y'‖ ≤ K * ‖y - y'‖) : Continuous f :=
  (LipschitzWith.of_dist_le_mul (K := K.toNNReal) fun x y => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal K hK]; exact h x y).continuous

theorem tsupport_one_sub_subset {d : ℕ} (χh : Euc d → ℝ) (hχh : IsCutoffRad 6 8 χh) :
    tsupport (fun w => 1 - χh w) ⊆ {w : Euc d | 6 ≤ ‖w‖} := by
  refine closure_minimal (fun w hw => ?_) (isClosed_le continuous_const continuous_norm)
  by_contra hlt
  have hlt' : ‖w‖ < 6 := by simpa using hlt
  exact hw (by simp [hχh.2.2.2.2 w (by simpa using hlt'.le)])

/-- Conjunct (iii). -/
theorem sep_iii {d : ℕ} (Λ C : ℝ) (hC : Λ ≤ C) (χ χh : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (hχh : IsCutoffRad 6 8 χh) (Ψinv : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ)
    (hτ : 0 ≤ τ)
    (hlip : ∀ y y', ‖Ψinv τ y - Ψinv τ y'‖ ≤ Real.exp (Λ * τ) * ‖y - y'‖) :
    ∀ z : Euc d, ∀ x y : Euc d, x ∈ tsupport (fun x => χ (Ψinv τ x - z)) →
      y ∈ tsupport (fun y => 1 - χh (Ψinv τ y - z)) →
      4 * Real.exp (-(C * τ)) ≤ ‖x - y‖ := by
  intro z x y hx hy
  have hc : Continuous fun x => Ψinv τ x - z :=
    (continuous_of_lip _ (Real.exp_pos _).le _ hlip).sub continuous_const
  have h1 : Ψinv τ x - z ∈ tsupport χ :=
    tsupport_comp_subset_preimage (f := fun x => Ψinv τ x - z) χ hc hx
  have h2 : Ψinv τ y - z ∈ tsupport (fun w => 1 - χh w) :=
    tsupport_comp_subset_preimage (f := fun x => Ψinv τ x - z) (fun w => 1 - χh w) hc hy
  have h1' : ‖Ψinv τ x - z‖ < 2 := by simpa using hχ.2.2.1 h1
  have h2' : 6 ≤ ‖Ψinv τ y - z‖ := tsupport_one_sub_subset χh hχh h2
  have h3 : 4 ≤ ‖Ψinv τ x - Ψinv τ y‖ := by
    have e : Ψinv τ y - z = -(Ψinv τ x - Ψinv τ y) + (Ψinv τ x - z) := by abel
    have := norm_add_le (-(Ψinv τ x - Ψinv τ y)) (Ψinv τ x - z)
    rw [← e, norm_neg] at this
    linarith
  have h4 : 4 ≤ Real.exp (Λ * τ) * ‖x - y‖ := h3.trans (hlip x y)
  have h5 : Real.exp (-(C * τ)) ≤ Real.exp (-(Λ * τ)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h6 : 4 * Real.exp (-(Λ * τ)) ≤ ‖x - y‖ := by
    have e : Real.exp (-(Λ * τ)) * Real.exp (Λ * τ) = 1 := by
      rw [← Real.exp_add]; simp
    calc 4 * Real.exp (-(Λ * τ)) ≤ Real.exp (-(Λ * τ)) * (Real.exp (Λ * τ) * ‖x - y‖) := by
          rw [mul_comm]; gcongr
      _ = ‖x - y‖ := by rw [← mul_assoc, e, one_mul]
  calc 4 * Real.exp (-(C * τ)) ≤ 4 * Real.exp (-(Λ * τ)) := by gcongr
    _ ≤ ‖x - y‖ := h6

/-- Conjunct (iv). -/
theorem sep_iv {d : ℕ} (Λ C : ℝ) (hΛ : 0 ≤ Λ) (hC : Λ ≤ C) (hC2 : (2 : ℝ) ^ d ≤ C)
    (hC5 : (5 : ℝ) ^ d ≤ C) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (Ψ Ψinv : ℝ → Euc d → Euc d) (τ : ℝ) (hτ : 0 ≤ τ)
    (h1 : ∀ x, Ψinv τ (Ψ τ x) = x) (h2 : ∀ y, Ψ τ (Ψinv τ y) = y)
    (hlip : ∀ y y', ‖Ψinv τ y - Ψinv τ y'‖ ≤ Real.exp (Λ * τ) * ‖y - y'‖) :
    ((⋃ z : Fin d → ℤ, Ψ τ '' latticeCell z) = Set.univ ∧
      (∀ y : Euc d, {z : Fin d → ℤ | y ∈ Ψ τ '' latticeCell z}.encard ≤
        ((⌊C * Real.exp (C * d * τ)⌋₊ : ℕ) : ℕ∞)) ∧
      (∀ G : Euc d → ℝ≥0∞, Measurable G →
        ∫⁻ x, G x ≤ ∑' z : Fin d → ℤ, ∫⁻ x in Ψ τ '' latticeCell z, G x ∧
        (∑' z : Fin d → ℤ, ∫⁻ x in Ψ τ '' latticeCell z, G x) ≤
          ENNReal.ofReal (C * Real.exp (C * d * τ)) * ∫⁻ x, G x) ∧
      ∀ (A : Set (Euc d)) (ρ : ℝ), 0 ≤ ρ → Metric.ediam A ≤ ENNReal.ofReal ρ →
        {z : Fin d → ℤ | (A ∩ tsupport (fun x => χ (Ψinv τ x - latticePt z))).Nonempty}.encard ≤
          ((⌊C * (1 + ρ) ^ d * Real.exp (C * d * τ)⌋₊ : ℕ) : ℕ∞)) := by
  have hcont : Continuous (Ψinv τ) := continuous_of_lip _ (Real.exp_pos _).le _ hlip
  have hexp1 : 1 ≤ Real.exp (C * d * τ) :=
    Real.one_le_exp (by have : 0 ≤ C := hΛ.trans hC; positivity)
  have hC0 : 0 ≤ C := hΛ.trans hC
  have himg : ∀ z, Ψ τ '' latticeCell z = Ψinv τ ⁻¹' latticeCell z := by
    intro z
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [h1] using hx
    · intro hy
      exact ⟨Ψinv τ y, hy, h2 y⟩
  have hmem : ∀ z y, y ∈ Ψ τ '' latticeCell z ↔ Ψinv τ y ∈ latticeCell z := fun z y => by
    rw [himg]; rfl
  have hmeas : ∀ z, MeasurableSet (Ψ τ '' latticeCell z) := fun z => by
    rw [himg]; exact hcont.measurable (isClosed_cell z).measurableSet
  have hmult : ∀ y, ∃ F : Finset (Fin d → ℤ), F.card ≤ 2 ^ d ∧
      ∀ z, y ∈ Ψ τ '' latticeCell z → z ∈ F := by
    intro y
    obtain ⟨F, hF1, hF2⟩ := cell_multiplicity (Ψinv τ y)
    refine ⟨F, ?_, fun z hz => hF2 z ((hmem z y).1 hz)⟩
    exact_mod_cast hF1
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine eq_univ_of_forall fun y => ?_
    obtain ⟨z, hz⟩ := exists_cell (Ψinv τ y)
    exact mem_iUnion.2 ⟨z, (hmem z y).2 hz⟩
  · intro y
    obtain ⟨F, hF1, hF2⟩ := hmult y
    calc {z : Fin d → ℤ | y ∈ Ψ τ '' latticeCell z}.encard ≤ (F : Set (Fin d → ℤ)).encard :=
          Set.encard_le_encard (fun z hz => hF2 z hz)
      _ = (F.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard F
      _ ≤ _ := by
          refine Nat.cast_le.2 (Nat.le_floor ?_)
          have : (F.card : ℝ) ≤ 2 ^ d := by exact_mod_cast hF1
          nlinarith
  · intro G hG
    have hle : ((2 ^ d : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (C * Real.exp (C * d * τ)) := by
      rw [← ENNReal.ofReal_natCast]
      refine ENNReal.ofReal_le_ofReal ?_
      push_cast
      nlinarith
    obtain ⟨hA, hB⟩ := lintegral_cover (fun z => Ψ τ '' latticeCell z) hmeas (2 ^ d)
      (fun y => by
        obtain ⟨z, hz⟩ := exists_cell (Ψinv τ y)
        exact ⟨z, (hmem z y).2 hz⟩) hmult G hG
    exact ⟨hA, hB.trans (by gcongr)⟩
  · intro A ρ hρ hA
    rcases (Set.eq_empty_or_nonempty {z : Fin d → ℤ |
        (A ∩ tsupport (fun x => χ (Ψinv τ x - latticePt z))).Nonempty}) with hM | ⟨z1, a0, ha0A, ha0⟩
    · rw [hM]; simp
    · set w0 := Ψinv τ a0
      set R := Real.exp (Λ * τ) * ρ + 2 with hR
      have hR0 : 0 ≤ R := by positivity
      obtain ⟨F, hF1, hF2⟩ := box_finset (fun i => w0 i) R hR0
      have hsub : {z : Fin d → ℤ |
          (A ∩ tsupport (fun x => χ (Ψinv τ x - latticePt z))).Nonempty} ⊆ (F : Set (Fin d → ℤ)) := by
        rintro z ⟨a, haA, ha⟩
        refine hF1 z fun i => ?_
        have hc : Continuous fun x => Ψinv τ x - latticePt z := hcont.sub continuous_const
        have hts : Ψinv τ a - latticePt z ∈ tsupport χ :=
          tsupport_comp_subset_preimage (f := fun x => Ψinv τ x - latticePt z) χ hc ha
        have hb : ‖Ψinv τ a - latticePt z‖ < 2 := by simpa using hχ.2.2.1 hts
        have hd : ‖a - a0‖ ≤ ρ := by
          have := Metric.edist_le_ediam_of_mem haA ha0A
          have h3 : edist a a0 ≤ ENNReal.ofReal ρ := this.trans hA
          rw [edist_dist, dist_eq_norm] at h3
          have := (ENNReal.ofReal_le_ofReal_iff hρ).1 h3
          exact this
        have he : ‖Ψinv τ a - w0‖ ≤ Real.exp (Λ * τ) * ρ :=
          (hlip a a0).trans (by gcongr)
        have hz2 : ‖latticePt z - w0‖ ≤ R := by
          have : latticePt z - w0 = -(Ψinv τ a - latticePt z) + (Ψinv τ a - w0) := by abel
          rw [this]
          refine (norm_add_le _ _).trans ?_
          rw [norm_neg, hR]
          linarith
        have := PiLp.norm_apply_le (latticePt z - w0) i
        rw [Real.norm_eq_abs] at this
        have e : (latticePt z - w0) i = (z i : ℝ) - w0 i := rfl
        rw [e] at this
        exact this.trans hz2
      calc _ ≤ (F : Set (Fin d → ℤ)).encard := Set.encard_le_encard hsub
        _ = (F.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard F
        _ ≤ _ := by
          refine Nat.cast_le.2 (Nat.le_floor ?_)
          have he1 : 1 ≤ Real.exp (Λ * τ) := Real.one_le_exp (by positivity)
          have hbase : 2 * R + 1 ≤ 5 * Real.exp (Λ * τ) * (1 + ρ) := by
            rw [hR]; nlinarith [mul_nonneg hρ (sub_nonneg.2 he1), he1]
          have hp : (2 * R + 1) ^ d ≤ (5 * Real.exp (Λ * τ) * (1 + ρ)) ^ d :=
            pow_le_pow_left₀ (by linarith) hbase d
          have hexp : Real.exp (Λ * τ) ^ d ≤ Real.exp (C * d * τ) := by
            rw [← Real.exp_nat_mul]
            exact Real.exp_le_exp.2 (by
              have : (d : ℝ) * (Λ * τ) ≤ C * d * τ := by nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hC) (Nat.cast_nonneg (α := ℝ) d)) hτ]
              exact this)
          calc (F.card : ℝ) ≤ (2 * R + 1) ^ d := hF2
            _ ≤ (5 * Real.exp (Λ * τ) * (1 + ρ)) ^ d := hp
            _ = 5 ^ d * Real.exp (Λ * τ) ^ d * (1 + ρ) ^ d := by
                rw [mul_pow, mul_pow]
            _ ≤ C * Real.exp (C * d * τ) * (1 + ρ) ^ d := by
                gcongr
            _ = C * (1 + ρ) ^ d * Real.exp (C * d * τ) := by ring

/-- (iii) and (iv) of `uloc_bilip`, with a constant depending on `d` and `Λ` only. -/
theorem flow_covering_separation (d : ℕ) (Λ : ℝ) (hΛ : 0 ≤ Λ) (χ χh : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) (hχh : IsCutoffRad 6 8 χh) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ψ Ψinv : ℝ → Euc d → Euc d) (τ : ℝ), 0 ≤ τ →
      (∀ x, Ψinv τ (Ψ τ x) = x) → (∀ y, Ψ τ (Ψinv τ y) = y) →
      (∀ y y', ‖Ψinv τ y - Ψinv τ y'‖ ≤ Real.exp (Λ * τ) * ‖y - y'‖) →
      (∀ x x', ‖Ψ τ x - Ψ τ x'‖ ≤ Real.exp (Λ * τ) * ‖x - x'‖) →
      -- (iii)
      (∀ z : Euc d, ∀ x y : Euc d, x ∈ tsupport (fun x => χ (Ψinv τ x - z)) →
        y ∈ tsupport (fun y => 1 - χh (Ψinv τ y - z)) →
        4 * Real.exp (-(C * τ)) ≤ ‖x - y‖) ∧
      -- (iv)
      ((⋃ z : Fin d → ℤ, Ψ τ '' latticeCell z) = Set.univ ∧
        (∀ y : Euc d, {z : Fin d → ℤ | y ∈ Ψ τ '' latticeCell z}.encard ≤
          ((⌊C * Real.exp (C * d * τ)⌋₊ : ℕ) : ℕ∞)) ∧
        (∀ G : Euc d → ℝ≥0∞, Measurable G →
          ∫⁻ x, G x ≤ ∑' z : Fin d → ℤ, ∫⁻ x in Ψ τ '' latticeCell z, G x ∧
          (∑' z : Fin d → ℤ, ∫⁻ x in Ψ τ '' latticeCell z, G x) ≤
            ENNReal.ofReal (C * Real.exp (C * d * τ)) * ∫⁻ x, G x) ∧
        ∀ (A : Set (Euc d)) (ρ : ℝ), 0 ≤ ρ → Metric.ediam A ≤ ENNReal.ofReal ρ →
          {z : Fin d → ℤ | (A ∩ tsupport (fun x => χ (Ψinv τ x - latticePt z))).Nonempty}.encard ≤
            ((⌊C * (1 + ρ) ^ d * Real.exp (C * d * τ)⌋₊ : ℕ) : ℕ∞)) := by
  have h2 : (2 : ℝ) ^ d ≤ 5 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have h5 : (0 : ℝ) < 5 ^ d := by positivity
  refine ⟨5 ^ d + Λ + 1, by positivity, ?_⟩
  intro Ψ Ψinv τ hτ h1 h2' hlip _
  exact ⟨sep_iii Λ _ (by linarith) χ χh hχ hχh Ψinv Ψ τ hτ hlip,
    sep_iv Λ _ hΛ (by linarith) (by linarith) (by linarith) χ hχ Ψ Ψinv τ hτ h1 h2' hlip⟩

/-- First clause of (ii) of `uloc_bilip`: `∂_τ χ(Ψ_τ^{-1}x - z) = b^τ(x) · ∇(χ(Ψ_τ^{-1}· - z))(x)`. -/
theorem flow_cutoff_hasDerivWithinAt {d : ℕ} {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ}
    {b : ℝ → Euc d → Euc d} (hb : IsDriftBounds T m Λ b) {Ψ : ℝ → Euc d → Euc d}
    (hΨ : IsNegDriftFlow T b Ψ) (Ψinv : ℝ → Euc d → Euc d)
    (hinv : ∀ τ ∈ Icc (0 : ℝ) T, (∀ x, Ψinv τ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Ψinv τ y) = y))
    (χ : Euc d → ℝ) (hχ : ContDiff ℝ ∞ χ) (z : Euc d) :
    ∀ x : Euc d, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun τ' => χ (Ψinv τ' x - z))
        (inner ℝ (b τ x) (gradient (fun y => χ (Ψinv τ y - z)) x)) (Icc 0 T) τ := by
  intro x τ hτ
  have hv := flow_inv_hasDerivWithinAt hT hb hΨ Ψinv hinv x τ hτ
  have hcd := (FlowB.flow_inv_contDiff hT hb hΨ τ hτ (Ψinv τ) (hinv τ hτ).1 (hinv τ hτ).2).1
  have hdiff : DifferentiableAt ℝ (Ψinv τ) x :=
    hcd.differentiable (by exact_mod_cast Nat.succ_ne_zero m) x
  have hχd : HasFDerivAt χ (fderiv ℝ χ (Ψinv τ x - z)) (Ψinv τ x - z) :=
    ((hχ.differentiable (by simp)) _).hasFDerivAt
  have h1 := hχd.comp_hasDerivWithinAt τ (hv.sub_const z)
  have h2 : HasFDerivAt (fun y => χ (Ψinv τ y - z))
      ((fderiv ℝ χ (Ψinv τ x - z)).comp (fderiv ℝ (Ψinv τ) x)) x :=
    hχd.comp x (hdiff.hasFDerivAt.sub_const z)
  have h3 : inner ℝ (b τ x) (gradient (fun y => χ (Ψinv τ y - z)) x) =
      fderiv ℝ χ (Ψinv τ x - z) (fderiv ℝ (Ψinv τ) x (b τ x)) := by
    rw [real_inner_comm]
    unfold gradient
    rw [InnerProductSpace.toDual_symm_apply, h2.fderiv]
    rfl
  rw [h3]
  exact h1

end HRS.MS.FlowD
