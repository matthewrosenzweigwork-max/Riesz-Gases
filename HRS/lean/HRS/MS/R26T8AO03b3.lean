import HRS.MS.R26T8AO03b2

/-!
# S8.2 T8A O03b (part 3): an abstract joint continuity lemma for families of bounded linear functionals
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_o03b_cont {T : Type*} [TopologicalSpace T] (Φ : T → (Euc d → ℝ) → E) (S : Set T)
    (G : ℝ → Euc d → ℝ) (v0 : ℝ) (hv0 : 0 ≤ v0) (x0 : T) (hx0 : x0 ∈ S)
    (hlin : ∀ x ∈ S, r26t8a_o03b_Lin d (Φ x))
    (hbd : ∃ U ∈ 𝓝[S] x0, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ x ∈ U, ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A →
      TestBound (testOrder d) A f → ‖Φ x f‖ ≤ CK * A)
    (hG : ∀ s : ℝ, 0 ≤ s → ∃ A, TestBound (testOrder d) A (G s))
    (hsize : Tendsto (fun v : ℝ => testSizeE (testOrder d) (fun x => G v x - G v0 x)) (𝓝[Ici 0] v0) (𝓝 0))
    (hcont : ContinuousWithinAt (fun x => Φ x (G v0)) S x0) :
    ContinuousWithinAt (fun p : ℝ × T => Φ p.2 (G p.1)) (Ici 0 ×ˢ S) (v0, x0) := by
  obtain ⟨U, hU, CK, hCK, hb⟩ := hbd
  obtain ⟨A0, hA0⟩ := hG v0 hv0
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  rw [ContinuousWithinAt, nhdsWithin_prod_eq]
  set F1 : Filter ℝ := 𝓝[Ici 0] v0 with hF1
  set F2 : Filter T := 𝓝[S] x0 with hF2
  -- the size term
  have hreal : Tendsto (fun v : ℝ => (testSizeE (testOrder d) (fun x => G v x - G v0 x)).toReal) F1 (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsize
    rw [ENNReal.toReal_zero] at this
    exact this
  have hfin : ∀ᶠ v in F1, testSizeE (testOrder d) (fun x => G v x - G v0 x) < 1 :=
    hsize.eventually (gt_mem_nhds zero_lt_one)
  have hmemv : ∀ᶠ v in F1, 0 ≤ v := self_mem_nhdsWithin
  have hterm1 : Tendsto (fun p : ℝ × T => CK * (testSizeE (testOrder d) (fun x => G p.1 x - G v0 x)).toReal)
      (F1 ×ˢ F2) (𝓝 0) := by
    have := (hreal.const_mul CK).comp (tendsto_fst (f := F1) (g := F2))
    rw [mul_zero] at this
    exact this
  have hterm2 : Tendsto (fun p : ℝ × T => Φ p.2 (G v0) - Φ x0 (G v0)) (F1 ×ˢ F2) (𝓝 0) := by
    have := (tendsto_sub_nhds_zero_iff.2 hcont).comp (tendsto_snd (f := F1) (g := F2))
    exact this
  have hterm2' : Tendsto (fun p : ℝ × T => ‖Φ p.2 (G v0) - Φ x0 (G v0)‖) (F1 ×ˢ F2) (𝓝 0) := by
    simpa using hterm2.norm
  have hbound := hterm1.add hterm2'
  rw [add_zero] at hbound
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun p => norm_nonneg _) ?_ hbound
  have hev : ∀ᶠ p : ℝ × T in F1 ×ˢ F2, (testSizeE (testOrder d) (fun x => G p.1 x - G v0 x) < 1 ∧ 0 ≤ p.1) ∧
      (p.2 ∈ U ∧ p.2 ∈ S) :=
    (hfin.and hmemv).prod_mk (Filter.inter_mem hU self_mem_nhdsWithin)
  filter_upwards [hev] with p hp
  obtain ⟨⟨hs, hv⟩, hxU, hxS⟩ := hp
  obtain ⟨A1, hA1⟩ := hG p.1 hv
  have hne : testSizeE (testOrder d) (fun x => G p.1 x - G v0 x) ≠ ⊤ := (hs.trans ENNReal.one_lt_top).ne
  have hdv : (fun x => G p.1 x - G v0 x) = G p.1 + (-1 : ℝ) • G v0 := by
    funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hTBd : TestBound (testOrder d) (A1 + |(-1 : ℝ)| * A0) (fun x => G p.1 x - G v0 x) := by
    rw [hdv]; exact r26t8a_o03b_tb_add hA1 (r26t8a_o03b_tb_smul (-1 : ℝ) hA0)
  have hTB := r26t8a_o03b_tb_of_testSize hTBd.1 _ ENNReal.toReal_nonneg
    (le_of_eq (ENNReal.ofReal_toReal hne).symm)
  have hsplit : Φ p.2 (G p.1) = Φ p.2 (fun x => G p.1 x - G v0 x) + Φ p.2 (G v0) := by
    have e : G p.1 = (fun x => G p.1 x - G v0 x) + G v0 := by funext x; simp
    conv_lhs => rw [e]
    exact (hlin p.2 hxS).hadd _ _ _ _ hTBd hA0
  have h1 := hb p.2 hxU _ _ ENNReal.toReal_nonneg hTB
  calc ‖Φ p.2 (G p.1) - Φ x0 (G v0)‖
      = ‖Φ p.2 (fun x => G p.1 x - G v0 x) + (Φ p.2 (G v0) - Φ x0 (G v0))‖ := by
        rw [hsplit]; congr 1; abel
    _ ≤ ‖Φ p.2 (fun x => G p.1 x - G v0 x)‖ + ‖Φ p.2 (G v0) - Φ x0 (G v0)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 le_rfl

end HRS.MS.R26T8A
