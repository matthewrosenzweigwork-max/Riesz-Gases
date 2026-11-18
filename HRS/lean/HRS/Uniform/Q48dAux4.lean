import HRS.Uniform.Q48dAux3

/-!
# Q48d, part 4: the window hypothesis, `L²` helpers, and the global stochastic convolution
(infrastructure for Lemma 3.31)

`WinMaxU` is the universe-polymorphic form of the window maximal estimate of Lemma 3.27 (3) for an evolution `V`,
with the a.e.-strong measurability of the convolutions recorded (`IsStochConv` alone cannot determine a
non-measurable `Z`, see `HRS/Uniform/Q48dAux1.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Uniform.Q48d

universe u

section Defs

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The window maximal estimate on windows `[a, a+T]`, `a ≥ 0`, for probability spaces in universe `u`, with
constant `C`; the convolutions are a.e.-strongly measurable. -/
def WinMaxU (V : ℝ → ℝ → E →L[ℝ] E) (T C : ℝ) : Prop :=
  ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (a : ℝ), 0 ≤ a →
    ∀ (M : ℝ → Ω → E) (Sg : ℝ → Ω → (E →L[ℝ] E →L[ℝ] ℝ)),
      IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg →
      ∃ Z : ℝ → Ω → E,
        (∀ t ∈ Icc a (a + T), IsStochConv P V (ContinuousLinearMap.id ℝ E) M a t (Z t)) ∧
        (∀ t ∈ Icc a (a + T), AEStronglyMeasurable (Z t) P) ∧
        (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Icc a (a + T))) ∧
        ∫⁻ ω, (⨆ t ∈ Icc a (a + T), ‖Z t ω‖ₑ) ^ 2 ∂P ≤
          ENNReal.ofReal C * ∫⁻ ω, (∫⁻ r in Icc a (a + T), ENNReal.ofReal (traceNormForm (Sg r ω))) ∂P

end Defs

section Helpers

variable {E : Type*} [NormedAddCommGroup E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

lemma eLpNorm_two_eq {f : Ω → E} (hf : AEStronglyMeasurable f P) :
    eLpNorm f 2 P = (∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp [ENNReal.rpow_two]

/-- Two continuous functions on `[a,b]` that agree on the countable dense set agree on `[a,b]`. -/
lemma eqOn_Icc_of_ratIcc {f g : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (h : ∀ q ∈ ratIcc a b, f q = g q) : ∀ t ∈ Icc a b, f t = g t := by
  have hclosed : IsClosed (Icc a b ∩ (fun t => f t - g t) ⁻¹' {0}) :=
    (hf.sub hg).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hsub : ratIcc a b ⊆ Icc a b ∩ (fun t => f t - g t) ⁻¹' {0} := fun q hq =>
    ⟨ratIcc_subset hab hq, by simp [h q hq]⟩
  intro t ht
  have := (closure_minimal hsub hclosed (Icc_subset_closure_ratIcc hab ht)).2
  simpa [sub_eq_zero] using this

lemma lintegral_sq_add_le {f g : Ω → ℝ≥0∞} (hf : AEMeasurable f P) (hg : AEMeasurable g P) :
    (∫⁻ ω, (f ω + g ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      (∫⁻ ω, f ω ^ 2 ∂P) ^ (1 / 2 : ℝ) + (∫⁻ ω, g ω ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  have := ENNReal.lintegral_Lp_add_le (μ := P) (p := 2) hf hg (by norm_num)
  simpa [ENNReal.rpow_two] using this

end Helpers

section Global

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The global stochastic convolution `Z_t = ∫_0^t V(t,u) dD_u`, `t ≥ 0`, glued from the finite windows. -/
theorem exists_globalZ {V : ℝ → ℝ → E →L[ℝ] E}
    (hW : ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 ≤ C ∧ WinMaxU.{u} V T C)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (D : ℝ → Ω → E) (Sd : ℝ → Ω → (E →L[ℝ] E →L[ℝ] ℝ))
    (hD : ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S (fun τ ω => D (min τ S) ω)
      (fun r ω => if r ≤ S then Sd r ω else 0)) :
    ∃ Z : ℝ → Ω → E, (∀ t : ℝ, 0 ≤ t → IsStochConv P V (ContinuousLinearMap.id ℝ E) D 0 t (Z t)) ∧
      (∀ t : ℝ, 0 ≤ t → AEStronglyMeasurable (Z t) P) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Ici 0)) := by
  classical
  -- measurability of the martingale
  have hDm : ∀ τ : ℝ, 0 ≤ τ → AEStronglyMeasurable (D τ) P := by
    intro τ hτ
    have := (hD τ hτ).sq_int τ ⟨hτ, le_rfl⟩
    simpa using this.aestronglyMeasurable
  -- the window convolutions on `[0, n+1]`
  have hex : ∀ n : ℕ, ∃ Zn : ℝ → Ω → E,
      (∀ t ∈ Icc (0 : ℝ) (n + 1), IsStochConv P V (ContinuousLinearMap.id ℝ E) D 0 t (Zn t)) ∧
      (∀ t ∈ Icc (0 : ℝ) (n + 1), AEStronglyMeasurable (Zn t) P) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => Zn t ω) (Icc 0 (n + 1))) := by
    intro n
    obtain ⟨C, -, hC⟩ := hW ((n : ℝ) + 1) (by positivity)
    have hS : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hh := hD ((n : ℝ) + 1) hS
    have hh' : IsHilbertMartingaleWithCovariation P ℱ (0 + ((n : ℝ) + 1))
        (fun τ ω => D (min τ ((n : ℝ) + 1)) ω)
        (fun r ω => if r ≤ (n : ℝ) + 1 then Sd r ω else 0) := by rwa [zero_add]
    obtain ⟨Z, h1, h2, h3, -⟩ := hC Ω P ℱ 0 le_rfl _ _ hh'
    rw [zero_add] at h1 h2 h3
    refine ⟨Z, fun t ht => ?_, h2, h3⟩
    exact (isStochConv_stop_iff (S := (n : ℝ) + 1) ht.2).1 (h1 t ht)
  choose Zn hZ1 hZ2 hZ3 using hex
  -- agreement of the windows
  have hagree : ∀ n n' : ℕ, n ≤ n' → ∀ t ∈ Icc (0 : ℝ) (n + 1), Zn n t =ᵐ[P] Zn n' t := by
    intro n n' hnn t ht
    have hn' : (n : ℝ) + 1 ≤ (n' : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnn
    have ht' : t ∈ Icc (0 : ℝ) (n' + 1) := ⟨ht.1, ht.2.trans hn'⟩
    have hDt : ∀ τ ∈ Icc (0 : ℝ) t, AEStronglyMeasurable (D τ) P := fun τ hτ => hDm τ hτ.1
    refine sc_unique (V := V) ht.1 hDt (hZ2 n t ht) (hZ2 n' t ht') ?_ ?_
    · exact (isStochConv_iff (hZ2 n t ht) hDt).1 (hZ1 n t ht)
    · exact (isStochConv_iff (hZ2 n' t ht') hDt).1 (hZ1 n' t ht')
  have hgood : ∀ᵐ ω ∂P, (∀ n : ℕ, ContinuousOn (fun t => Zn n t ω) (Icc 0 ((n : ℝ) + 1))) ∧
      ∀ n n' : ℕ, n ≤ n' → ∀ q ∈ ratIcc 0 ((n : ℝ) + 1), Zn n q ω = Zn n' q ω := by
    rw [eventually_and, ae_all_iff]
    refine ⟨hZ3, ?_⟩
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro n'
    by_cases hnn : n ≤ n'
    · have hc := (countable_ratIcc 0 ((n : ℝ) + 1))
      have : ∀ᵐ ω ∂P, ∀ q ∈ ratIcc 0 ((n : ℝ) + 1), Zn n q ω = Zn n' q ω := by
        rw [ae_ball_iff hc]
        intro q hq
        exact hagree n n' hnn q (ratIcc_subset (by positivity) hq)
      filter_upwards [this] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hnn
  -- the glued process
  refine ⟨fun t ω => Zn ⌈t⌉₊ t ω, ?_, ?_, ?_⟩
  · intro t ht
    exact hZ1 _ t ⟨ht, (Nat.le_ceil t).trans (by linarith)⟩
  · intro t ht
    exact hZ2 _ t ⟨ht, (Nat.le_ceil t).trans (by linarith)⟩
  · filter_upwards [hgood] with ω ⟨hc, hr⟩
    have hpt : ∀ n n' : ℕ, n ≤ n' → ∀ t ∈ Icc (0 : ℝ) (n + 1), Zn n t ω = Zn n' t ω := by
      intro n n' hnn t ht
      have hn' : (n : ℝ) + 1 ≤ (n' : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnn
      exact eqOn_Icc_of_ratIcc (a := 0) (b := (n : ℝ) + 1) (by positivity) (hc n)
        ((hc n').mono (Icc_subset_Icc_right hn')) (hr n n' hnn) t ht
    intro t0 ht0
    set N : ℕ := ⌈t0⌉₊ + 1 with hN
    have htN : t0 < N := by
      have := Nat.le_ceil t0
      rw [hN]; push_cast; linarith
    have hEq : ∀ t ∈ Icc (0 : ℝ) N, Zn ⌈t⌉₊ t ω = Zn N t ω := by
      intro t ht
      have hle : ⌈t⌉₊ ≤ N := Nat.ceil_le.2 ht.2
      exact hpt _ _ hle t ⟨ht.1, (Nat.le_ceil t).trans (by linarith)⟩
    have hcw : ContinuousWithinAt (fun t => Zn N t ω) (Icc 0 (N : ℝ)) t0 :=
      ((hc N).mono (Icc_subset_Icc_right (by linarith))) t0 ⟨ht0, htN.le⟩
    have hcw2 : ContinuousWithinAt (fun t => Zn ⌈t⌉₊ t ω) (Icc 0 (N : ℝ)) t0 :=
      hcw.congr (fun t ht => hEq t ht) (hEq t0 ⟨ht0, htN.le⟩)
    refine hcw2.mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Iio N, isOpen_Iio, htN, fun t ht => ⟨ht.2, ht.1.le⟩⟩

end Global

end HRS.Uniform.Q48d
