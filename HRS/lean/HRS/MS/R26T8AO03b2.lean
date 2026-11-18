import HRS.MS.R26T8AO03b1

/-!
# S8.2 T8A O03b (part 2): an abstract derivative lemma for bounded linear functionals of age families
If `Φ` is linear and bounded (`|Φ f| ≤ CK A`) on `TestBound A` functions, and the `testSizeE` difference quotient of an age family
tends to `0`, then `v ↦ Φ (G₀ v)` is differentiable within `[0,∞)` with derivative `Φ (G₁ v)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure r26t8a_o03b_Lin (d : ℕ) (Φ : (Euc d → ℝ) → E) : Prop where
  hadd : ∀ (A B : ℝ) (f g : Euc d → ℝ), TestBound (testOrder d) A f → TestBound (testOrder d) B g →
    Φ (f + g) = Φ f + Φ g
  hsmul : ∀ (A c : ℝ) (f : Euc d → ℝ), TestBound (testOrder d) A f → Φ (c • f) = c • Φ f

theorem r26t8a_o03b_quot_eq {Φ : (Euc d → ℝ) → E} (hΦ : r26t8a_o03b_Lin d Φ) {A0 A1 A2 : ℝ} {g0 g1 g2 : Euc d → ℝ}
    (h0 : TestBound (testOrder d) A0 g0) (h1 : TestBound (testOrder d) A1 g1) (h2 : TestBound (testOrder d) A2 g2)
    (c : ℝ) :
    Φ (fun x => c * (g0 x - g1 x) - g2 x) = c • (Φ g0 - Φ g1) - Φ g2 := by
  have e : (fun x => c * (g0 x - g1 x) - g2 x) = c • g0 + ((-c) • g1 + (-1 : ℝ) • g2) := by
    funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e]
  have t1 := r26t8a_o03b_tb_smul c h0
  have t2 := r26t8a_o03b_tb_smul (-c) h1
  have t3 := r26t8a_o03b_tb_smul (-1 : ℝ) h2
  rw [hΦ.hadd _ _ _ _ t1 (r26t8a_o03b_tb_add t2 t3), hΦ.hadd _ _ _ _ t2 t3, hΦ.hsmul _ _ _ h0,
    hΦ.hsmul _ _ _ h1, hΦ.hsmul _ _ _ h2]
  simp only [neg_smul, one_smul, smul_sub]
  abel

theorem r26t8a_o03b_deriv {Φ : (Euc d → ℝ) → E} (hΦ : r26t8a_o03b_Lin d Φ) {CK : ℝ} (hCK : 0 ≤ CK)
    (hbd : ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A → TestBound (testOrder d) A f → ‖Φ f‖ ≤ CK * A)
    (G0 G1 : ℝ → Euc d → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hG0 : ∀ s : ℝ, 0 ≤ s → ∃ A, TestBound (testOrder d) A (G0 s))
    (hG1 : ∃ A, TestBound (testOrder d) A (G1 v))
    (hq : Tendsto (fun h : ℝ => testSizeE (testOrder d) (fun x => h⁻¹ * (G0 (v + h) x - G0 v x) - G1 v x))
      (𝓝[({h : ℝ | 0 ≤ v + h} ∩ {0}ᶜ)] 0) (𝓝 0)) :
    HasDerivWithinAt (fun s => Φ (G0 s)) (Φ (G1 v)) (Ici 0) v := by
  set F : Filter ℝ := 𝓝[({h : ℝ | 0 ≤ v + h} ∩ {0}ᶜ)] 0 with hF
  obtain ⟨A0, hA0⟩ := hG0 v hv
  obtain ⟨A2, hA2⟩ := hG1
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  have hmem : ∀ᶠ h in F, 0 ≤ v + h ∧ h ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh using ⟨hh.1, hh.2⟩
  have hfin : ∀ᶠ h in F, testSizeE (testOrder d) (fun x => h⁻¹ * (G0 (v + h) x - G0 v x) - G1 v x) < 1 :=
    hq.eventually (gt_mem_nhds zero_lt_one)
  -- the functional on the quotient tends to zero
  have hΦq : Tendsto (fun h : ℝ => Φ (fun x => h⁻¹ * (G0 (v + h) x - G0 v x) - G1 v x)) F (𝓝 0) := by
    have hreal : Tendsto (fun h : ℝ => (testSizeE (testOrder d) (fun x => h⁻¹ * (G0 (v + h) x - G0 v x) - G1 v x)).toReal)
        F (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hq
      rw [ENNReal.toReal_zero] at this
      exact this
    refine squeeze_zero_norm' ?_ (by simpa using hreal.const_mul CK)
    filter_upwards [hmem, hfin] with h hh hs
    obtain ⟨hh1, hh2⟩ := hh
    obtain ⟨A1, hA1⟩ := hG0 (v + h) hh1
    have hne : testSizeE (testOrder d) (fun x => h⁻¹ * (G0 (v + h) x - G0 v x) - G1 v x) ≠ ⊤ := (hs.trans ENNReal.one_lt_top).ne
    have hsm : ContDiff ℝ ∞ (fun x => h⁻¹ * (G0 (v + h) x - G0 v x) - G1 v x) := by
      have e : (fun x => h⁻¹ * (G0 (v + h) x - G0 v x) - G1 v x) =
          h⁻¹ • G0 (v + h) + ((-h⁻¹) • G0 v + (-1 : ℝ) • G1 v) := by
        funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      exact (r26t8a_o03b_tb_add (r26t8a_o03b_tb_smul h⁻¹ hA1)
        (r26t8a_o03b_tb_add (r26t8a_o03b_tb_smul (-h⁻¹) hA0) (r26t8a_o03b_tb_smul (-1 : ℝ) hA2))).1
    have hTB := r26t8a_o03b_tb_of_testSize hsm _ ENNReal.toReal_nonneg
      (le_of_eq (ENNReal.ofReal_toReal hne).symm)
    exact hbd _ _ ENNReal.toReal_nonneg hTB
  -- slopes
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hshift : Tendsto (fun t : ℝ => t - v) (𝓝[Ici 0 \ {v}] v) F := by
    rw [hF, tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => t - v) (𝓝 v) (𝓝 (v - v)) := (continuous_id.sub continuous_const).tendsto v
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact ⟨by simpa using ht.1, fun h => ht.2 (by simpa [sub_eq_zero] using h)⟩
  have := (hΦq.comp hshift).add_const (Φ (G1 v))
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hh1 : 0 ≤ v + (t - v) := by simpa using ht.1
  have hh2 : t - v ≠ 0 := sub_ne_zero.2 ht.2
  obtain ⟨A1, hA1⟩ := hG0 (v + (t - v)) hh1
  simp only [Function.comp]
  rw [r26t8a_o03b_quot_eq hΦ hA1 hA0 hA2 (t - v)⁻¹]
  have : v + (t - v) = t := by ring
  rw [this]
  simp only [slope, vsub_eq_sub]
  rw [smul_sub]
  abel

end HRS.MS.R26T8A
