import HRS.Uniform.Q48dAux4
import HRS.Uniform.KotConv
import HRS.Prob.MartingaleRep

/-!
# Q48e, part 1: the window maximal estimate for a quasi-contractive plain evolution

`winmax_of_quasi`: for a strongly continuous evolution `V` on a separable Hilbert space (`IsPlainEvolution V T` for every
`T ≥ 0`) with `‖V(t,u)‖ ≤ exp (K (t-u)/2)`, the window estimate `Q48d.WinMaxU V T (Kot.CD 2 K T)` holds for probability
spaces of every universe `u`; the constant depends only on `(K, T)`.  The proof is Kotelenez's (`KotConv`, whose
`variable {Ω : Type}` was generalised to `Type*`) applied to the shifted martingale
`M'_τ = M_{a + clamp τ} - M_a` in the shifted filtration (`isHMC_window`, via the stopping calculus of `MRepAux1/12`).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Uniform.Q48e

open HRS HRS.MRep

lemma integral_Icc_shift (f : ℝ → ℝ) (a T : ℝ) (hT : 0 ≤ T) :
    ∫ σ in Icc 0 T, f (a + σ) = ∫ σ in Icc a (a + T), f σ := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_comp_add_left, add_zero]

lemma preimage_add_Icc (a T : ℝ) : (fun σ : ℝ => a + σ) ⁻¹' Icc a (a + T) = Icc 0 T := by
  ext σ; simp [mem_Icc]

lemma integrableOn_Icc_shift (f : ℝ → ℝ) (a T : ℝ) :
    IntegrableOn (fun σ => f (a + σ)) (Icc 0 T) ↔ IntegrableOn f (Icc a (a + T)) := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) a).integrableOn_comp_preimage
    (measurableEmbedding_addLeft a) (f := f) (s := Icc a (a + T))
  rw [preimage_add_Icc] at h
  exact h

lemma lintegral_Icc_shift (f : ℝ → ℝ≥0∞) (a T : ℝ) :
    ∫⁻ σ in Icc 0 T, f (a + σ) = ∫⁻ σ in Icc a (a + T), f σ := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) a).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addLeft a) f (Icc a (a + T))
  rw [preimage_add_Icc] at h
  exact h

lemma integral_Icc_shift_sub (f : ℝ → ℝ) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hf : IntegrableOn f (Icc 0 (a + c))) :
    ∫ σ in Icc 0 c, f (a + σ) = (∫ σ in Icc 0 (a + c), f σ) - ∫ σ in Icc 0 a, f σ := by
  rw [integral_Icc_shift f a c hc, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_of_le ha, ← intervalIntegral.integral_of_le (by linarith)]
  have h1 : IntervalIntegrable f volume 0 (a + c) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 hf
  have h2 : IntervalIntegrable f volume 0 a :=
    h1.mono_set (by
      rw [uIcc_of_le ha, uIcc_of_le (by linarith)]
      exact Icc_subset_Icc_right (by linarith))
  rw [intervalIntegral.integral_interval_sub_left h1 h2]


section Window

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The time map of the window `[a, a+T]`. -/
def wt (a T τ : ℝ) : ℝ := a + MRep.clampT T τ

lemma wt_mem {a T : ℝ} (hT : 0 ≤ T) (τ : ℝ) : wt a T τ ∈ Icc a (a + T) := by
  have := MRep.clampT_mem hT τ
  exact ⟨by unfold wt; linarith [this.1], by unfold wt; linarith [this.2]⟩

lemma wt_of_mem {a T τ : ℝ} (hτ : τ ∈ Icc 0 T) : wt a T τ = a + τ := by
  simp [wt, MRep.clampT_of_mem hτ]

lemma clampT_nonneg' (T τ : ℝ) : 0 ≤ MRep.clampT T τ := by simp [MRep.clampT]

lemma clampT_mono' (T : ℝ) : Monotone (MRep.clampT T) := by
  intro i j h
  simp only [MRep.clampT]
  gcongr

lemma le_clampT_of_le {T σ : ℝ} (h : σ ≤ T) : σ ≤ MRep.clampT T σ := by
  simp [MRep.clampT, h]

lemma wt_ge (a T τ : ℝ) : a ≤ wt a T τ := by
  unfold wt
  linarith [clampT_nonneg' T τ]

lemma le_wt_of_le {a T σ : ℝ} (h : σ ≤ T) : a + σ ≤ wt a T σ := by
  unfold wt
  linarith [le_clampT_of_le h]

lemma wt_zero {a T : ℝ} (hT : 0 ≤ T) : wt a T 0 = a := by
  simp [wt, MRep.clampT, hT]

lemma wt_mono (a T : ℝ) : Monotone (wt a T) := by
  intro i j h
  unfold wt
  linarith [clampT_mono' T h]

lemma continuous_wt (a T : ℝ) : Continuous (wt a T) :=
  continuous_const.add (MRep.continuous_clampT T)

/-- The filtration of the window: `ℱ'_τ = ℱ_{a + clamp τ}`. -/
def winFiltration (ℱ : Filtration ℝ mΩ) (a T : ℝ) : Filtration ℝ mΩ where
  seq τ := ℱ (wt a T τ)
  mono' := fun i j h => ℱ.mono (wt_mono a T h)
  le' := fun τ => ℱ.le _

lemma martingale_wt {F : ℝ → Ω → ℝ} (hF : Martingale F ℱ P) (a T : ℝ) :
    Martingale (fun τ => F (wt a T τ)) (winFiltration ℱ a T) P :=
  ⟨fun τ => hF.1 (wt a T τ), fun i j h => hF.2 _ _ (wt_mono a T h)⟩

lemma martingale_const_win {a T : ℝ} {β : Ω → ℝ} (hβm : StronglyMeasurable[ℱ a] β)
    (hβi : Integrable β P) : Martingale (fun _ => β) (winFiltration ℱ a T) P := by
  have hle : ∀ τ, ℱ a ≤ ℱ (wt a T τ) := fun τ => ℱ.mono (wt_ge a T τ)
  refine ⟨fun τ => hβm.mono (hle τ), fun i j _ => ?_⟩
  exact (condExp_of_stronglyMeasurable ((winFiltration ℱ a T).le i) (hβm.mono (hle i)) hβi).eventuallyEq

omit [BorelSpace H] [SecondCountableTopology H] in
lemma memLp_inner_win {t : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg) (x : H) {τ : ℝ} (hτ : τ ≤ t) :
    MemLp (fun ω => inner ℝ (M τ ω) x) 2 P := by
  by_cases h : 0 ≤ τ
  · exact (hM.sq_int τ ⟨h, hτ⟩).inner_const (𝕜 := ℝ) x
  · have h1 := (hM.martingale x).2 τ 0 (not_le.1 h).le
    have h0 : (fun ω => inner ℝ (M 0 ω) x) =ᵐ[P] 0 := hM.zero.mono fun ω h => by simp [h]
    have h2 : (fun ω => inner ℝ (M τ ω) x) =ᵐ[P] 0 := by
      calc (fun ω => inner ℝ (M τ ω) x) =ᵐ[P] P[fun ω => inner ℝ (M 0 ω) x | ℱ τ] := h1.symm
        _ =ᵐ[P] P[(0 : Ω → ℝ) | ℱ τ] := condExp_congr_ae h0
        _ =ᵐ[P] 0 := by rw [condExp_zero]
    exact MemLp.ae_eq h2.symm MemLp.zero

lemma four_piece {U V Λ : ℝ → Ω → ℝ} (hU : Martingale U ℱ P) (hV : Martingale V ℱ P)
    (hU2 : ∀ t, MemLp (U t) 2 P) (hV2 : ∀ t, MemLp (V t) 2 P)
    (hΛ : Martingale (fun t ω => U t ω * V t ω - Λ t ω) ℱ P) (a : ℝ) :
    Martingale (fun s ω => (U s ω - U (min a s) ω) * (V s ω - V (min a s) ω) -
      (Λ s ω - Λ (min a s) ω)) ℱ P := by
  have h2 := martingale_stop_mul hU hV hU2 hV2 hΛ a
  have hΛ' : Martingale (fun t ω => V t ω * U t ω - Λ t ω) ℱ P := by
    have : (fun t ω => V t ω * U t ω - Λ t ω) = fun t ω => U t ω * V t ω - Λ t ω := by
      funext t ω; ring
    rw [this]; exact hΛ
  have h3 := martingale_stop_mul hV hU hV2 hU2 hΛ' a
  have h4 := martingale_stopped_mul hU hV hU2 hV2 hΛ a
  have e : (fun s ω => (U s ω - U (min a s) ω) * (V s ω - V (min a s) ω) -
      (Λ s ω - Λ (min a s) ω)) = fun s ω => (U s ω * V s ω - Λ s ω) -
        (U (min a s) ω * V s ω - Λ (min a s) ω) - (V (min a s) ω * U s ω - Λ (min a s) ω) +
        (U (min a s) ω * V (min a s) ω - Λ (min a s) ω) := by
    funext s ω; ring
  rw [e]
  exact ((hΛ.sub h2).sub h3).add h4


lemma integral_cut_shift {a T τ : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (g : ℝ → ℝ)
    (hg : IntegrableOn g (Icc 0 (a + T))) :
    ∫ σ in Icc 0 τ, (if σ ≤ T then g (a + σ) else 0) =
      (∫ σ in Icc 0 (wt a T τ), g σ) - ∫ σ in Icc 0 a, g σ := by
  by_cases hτ : 0 ≤ τ
  · rw [integral_ite_Icc T τ (fun σ => g (a + σ))]
    have hw : wt a T τ = a + min T τ := by
      unfold wt; rw [MRep.clampT_of_nonneg hT hτ, min_comm]
    rw [hw]
    refine integral_Icc_shift_sub g ha (le_min hT hτ) (hg.mono_set (Icc_subset_Icc_right ?_))
    linarith [min_le_left T τ]
  · push Not at hτ
    rw [Set.Icc_eq_empty (not_le.2 hτ), wt, MRep.clampT_of_nonpos hτ.le]
    simp

theorem cov_window (hℱ : IsCompleteFiltration P ℱ) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg) (x y : H) :
    Martingale (fun τ ω => inner ℝ (M (wt a T τ) ω - M a ω) x * inner ℝ (M (wt a T τ) ω - M a ω) y -
      ∫ σ in Icc 0 τ, (if σ ≤ T then Sg (a + σ) ω x y else 0)) (winFiltration ℱ a T) P := by
  have hS0 : 0 ≤ a + T := by linarith
  have haS : a ∈ Icc (0 : ℝ) (a + T) := ⟨ha, by linarith⟩
  have hU : Martingale (fun t ω => inner ℝ (M (min (a + T) t) ω) x) ℱ P :=
    martingale_stop_time (F := fun τ ω => inner ℝ (M τ ω) x) (hM.martingale x) (a + T)
  have hV : Martingale (fun t ω => inner ℝ (M (min (a + T) t) ω) y) ℱ P :=
    martingale_stop_time (F := fun τ ω => inner ℝ (M τ ω) y) (hM.martingale y) (a + T)
  have hΛ : Martingale (fun t ω => inner ℝ (M (min (a + T) t) ω) x * inner ℝ (M (min (a + T) t) ω) y -
      ∫ σ in Icc 0 (min (a + T) t), Sg σ ω x y) ℱ P :=
    martingale_stop_time (F := fun τ ω => inner ℝ (M τ ω) x * inner ℝ (M τ ω) y -
      ∫ σ in Icc 0 τ, Sg σ ω x y) (hM.covariation x y) (a + T)
  have hE := four_piece (U := fun t ω => inner ℝ (M (min (a + T) t) ω) x)
    (V := fun t ω => inner ℝ (M (min (a + T) t) ω) y)
    (Λ := fun t ω => ∫ σ in Icc 0 (min (a + T) t), Sg σ ω x y) hU hV
    (fun t => memLp_inner_win hM x (min_le_left _ _)) (fun t => memLp_inner_win hM y (min_le_left _ _))
    hΛ a
  have hEw := martingale_wt hE a T
  have hℱ' : IsCompleteFiltration P (winFiltration ℱ a T) := fun τ s hs h0 => hℱ (wt a T τ) s hs h0
  have hgm : Measurable fun p : ℝ × Ω => if p.1 ≤ T then Sg (a + p.1) p.2 x y else 0 := by
    refine Measurable.ite (measurableSet_le measurable_fst measurable_const) ?_ measurable_const
    exact (hM.sigma_meas x y).comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  refine martingale_congr_complete hℱ' hEw (fun τ => ?_) (fun τ => ?_)
  · have hUm : ∀ t, Measurable fun ω => inner ℝ (M t ω) x := fun t =>
      ((hM.martingale x).1 t).measurable.mono (ℱ.le t) le_rfl
    have hVm : ∀ t, Measurable fun ω => inner ℝ (M t ω) y := fun t =>
      ((hM.martingale y).1 t).measurable.mono (ℱ.le t) le_rfl
    simp only [inner_sub_left]
    exact (((hUm _).sub (hUm _)).mul ((hVm _).sub (hVm _))).sub
      (MRep.measurable_setIntegral_Icc (g := fun σ ω => if σ ≤ T then Sg (a + σ) ω x y else 0) hgm τ)
  · filter_upwards [hM.sigma_entry_int] with ω hω
    have hw := wt_mem (a := a) hT τ
    have h1 : min (a + T) (wt a T τ) = wt a T τ := min_eq_right hw.2
    have h2 : min a (wt a T τ) = a := min_eq_left hw.1
    have h3 : min (a + T) a = a := min_eq_right (by linarith)
    have h4 : min (a + T) (min a (wt a T τ)) = a := by rw [h2, h3]
    show (inner ℝ (M (min (a + T) (wt a T τ)) ω) x - inner ℝ (M (min (a + T) (min a (wt a T τ))) ω) x) *
        (inner ℝ (M (min (a + T) (wt a T τ)) ω) y - inner ℝ (M (min (a + T) (min a (wt a T τ))) ω) y) -
      ((∫ σ in Icc 0 (min (a + T) (wt a T τ)), Sg σ ω x y) -
        ∫ σ in Icc 0 (min (a + T) (min a (wt a T τ))), Sg σ ω x y) =
      inner ℝ (M (wt a T τ) ω - M a ω) x * inner ℝ (M (wt a T τ) ω - M a ω) y -
        ∫ σ in Icc 0 τ, (if σ ≤ T then Sg (a + σ) ω x y else 0)
    rw [h1, h4, integral_cut_shift ha hT (fun σ => Sg σ ω x y) (hω x y), inner_sub_left, inner_sub_left]


/-- The window of a Hilbert martingale: `M'_τ = M_{a+τ} - M_a` on `[0,T]` (clamped outside), in the shifted
filtration, with covariation density `Σ_{a+σ}` cut at `T`. -/
theorem isHMC_window (hℱ : IsCompleteFiltration P ℱ) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg) :
    IsHilbertMartingaleWithCovariation P (winFiltration ℱ a T) T
      (fun τ ω => M (wt a T τ) ω - M a ω) (fun σ ω => if σ ≤ T then Sg (a + σ) ω else 0) := by
  have hS0 : 0 ≤ a + T := by linarith
  have haS : a ∈ Icc (0 : ℝ) (a + T) := ⟨ha, by linarith⟩
  have hmeas : ∀ x y : H, Measurable (fun p : ℝ × Ω => if p.1 ≤ T then Sg (a + p.1) p.2 x y else 0) := by
    intro x y
    refine Measurable.ite (measurableSet_le measurable_fst measurable_const) ?_ measurable_const
    exact (hM.sigma_meas x y).comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hmeasQ : ∀ x y : H, Measurable (fun p : ℝ × Ω =>
      (if p.1 ≤ T then Sg (a + p.1) p.2 else 0) x y) := by
    intro x y
    have : (fun p : ℝ × Ω => (if p.1 ≤ T then Sg (a + p.1) p.2 else 0) x y) =
        fun p : ℝ × Ω => if p.1 ≤ T then Sg (a + p.1) p.2 x y else 0 := by
      funext p; by_cases h : p.1 ≤ T <;> simp [h]
    rw [this]; exact hmeas x y
  have hTN : Measurable (fun p : ℝ × Ω => traceNormForm (Sg p.1 p.2)) :=
    measurable_traceNormForm (H := H) (α := ℝ × Ω) (fun p => Sg p.1 p.2) (fun x y => hM.sigma_meas x y)
  refine ⟨fun x => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x y => ?_⟩
  · -- martingale
    have h1 := martingale_wt (F := fun τ ω => inner ℝ (M τ ω) x) (hM.martingale x) a T
    have hβ := (hM.martingale x)
    have h2 : Martingale (fun (_ : ℝ) ω => inner ℝ (M a ω) x) (winFiltration ℱ a T) P :=
      martingale_const_win (hβ.1 a) (hβ.integrable a)
    have e : (fun τ ω => inner ℝ (M (wt a T τ) ω - M a ω) x) =
        (fun τ ω => inner ℝ (M (wt a T τ) ω) x) - (fun _ ω => inner ℝ (M a ω) x) := by
      funext τ ω; simp [inner_sub_left]
    rw [e]
    exact h1.sub h2
  · exact Eventually.of_forall fun ω => by simp [wt_zero hT]
  · filter_upwards [hM.cont] with ω hω
    refine ContinuousOn.sub ?_ continuousOn_const
    refine hω.comp (continuous_wt a T).continuousOn fun τ _ => ?_
    have := wt_mem (a := a) hT τ
    exact ⟨ha.trans this.1, this.2⟩
  · intro τ hτ
    have h1 := hM.sq_int (wt a T τ) ⟨ha.trans (wt_mem (a := a) hT τ).1, (wt_mem hT τ).2⟩
    exact h1.sub (hM.sq_int a haS)
  · intro x y
    have : Function.uncurry (fun σ ω => (fun σ ω => if σ ≤ T then Sg (a + σ) ω else 0) σ ω x y) =
        fun p : ℝ × Ω => if p.1 ≤ T then Sg (a + p.1) p.2 x y else 0 := by
      funext p; by_cases h : p.1 ≤ T <;> simp [Function.uncurry, h]
    rw [this]; exact hmeas x y
  · intro σ x y
    by_cases h : σ ≤ T
    · have := hM.sigma_adapted (a + σ) x y
      have e : (fun ω => (if σ ≤ T then Sg (a + σ) ω else 0) x y) = fun ω => Sg (a + σ) ω x y := by
        funext ω; simp [h]
      rw [e]
      exact this.mono (ℱ.mono (le_wt_of_le h)) le_rfl
    · have e : (fun ω => (if σ ≤ T then Sg (a + σ) ω else 0) x y) = fun _ => (0 : ℝ) := by
        funext ω; simp [h]
      rw [e]
      exact measurable_const
  · filter_upwards [hM.sigma_traceClass] with ω hω σ hσ
    rw [if_pos hσ.2]
    exact hω (a + σ) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  · -- sigma_int
    have hsm : StronglyMeasurable fun ω => ∫ σ in Icc 0 T,
        traceNormForm (if σ ≤ T then Sg (a + σ) ω else 0) := by
      have hm : Measurable (fun p : ℝ × Ω => traceNormForm (if p.1 ≤ T then Sg (a + p.1) p.2 else 0)) :=
        measurable_traceNormForm (H := H) (α := ℝ × Ω)
          (fun p => if p.1 ≤ T then Sg (a + p.1) p.2 else 0) hmeasQ
      have := (hm.comp (measurable_swap (α := Ω) (β := ℝ))).stronglyMeasurable
      exact this.integral_prod_right' (ν := volume.restrict (Icc 0 T))
    refine Integrable.mono' hM.sigma_int hsm.aestronglyMeasurable ?_
    filter_upwards [hM.sigma_pathint] with ω hω
    have e1 : ∫ σ in Icc 0 T, traceNormForm (if σ ≤ T then Sg (a + σ) ω else 0) =
        ∫ σ in Icc a (a + T), traceNormForm (Sg σ ω) := by
      rw [← integral_Icc_shift (fun σ => traceNormForm (Sg σ ω)) a T hT]
      refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
      simp only [hσ.2, if_true]
    rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _), e1]
    exact setIntegral_mono_set hω (Eventually.of_forall fun σ => traceNormForm_nonneg _)
      (Eventually.of_forall (Icc_subset_Icc_left ha))
  · filter_upwards [hM.sigma_pathint] with ω hω
    have h1 : IntegrableOn (fun σ => traceNormForm (Sg (a + σ) ω)) (Icc 0 T) :=
      (integrableOn_Icc_shift (fun σ => traceNormForm (Sg σ ω)) a T).2
        (hω.mono_set (Icc_subset_Icc_left ha))
    refine h1.congr_fun (fun σ hσ => ?_) measurableSet_Icc
    simp only [hσ.2, if_true]
  · filter_upwards [hM.sigma_entry_int] with ω hω x y
    have h1 : IntegrableOn (fun σ => Sg (a + σ) ω x y) (Icc 0 T) :=
      (integrableOn_Icc_shift (fun σ => Sg σ ω x y) a T).2 ((hω x y).mono_set (Icc_subset_Icc_left ha))
    refine h1.congr_fun (fun σ hσ => ?_) measurableSet_Icc
    simp only [hσ.2, if_true]
  · have := cov_window hℱ ha hT hM x y
    have e : ∀ τ ω, ∫ σ in Icc 0 τ, (if σ ≤ T then Sg (a + σ) ω else 0) x y =
        ∫ σ in Icc 0 τ, (if σ ≤ T then Sg (a + σ) ω x y else 0) := fun τ ω =>
      integral_congr_ae (Eventually.of_forall fun σ => by by_cases h : σ ≤ T <;> simp [h])
    show Martingale (fun τ ω => inner ℝ (M (wt a T τ) ω - M a ω) x * inner ℝ (M (wt a T τ) ω - M a ω) y -
      ∫ σ in Icc 0 τ, (if σ ≤ T then Sg (a + σ) ω else 0) x y) (winFiltration ℱ a T) P
    simp_rw [e]
    exact this

end Window

section WinMax

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The window maximal estimate for a quasi-contractive plain evolution: `WinMaxU` with the Kotelenez constant
`CD 2 K T` (depending on the window length `T` and the quasi-contractivity constant `K` only). -/
theorem winmax_of_quasi {V : ℝ → ℝ → E →L[ℝ] E} (hV : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution V T) {K : ℝ}
    (hK : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖V t u‖ ≤ Real.exp (K * (t - u) / 2)) {T : ℝ} (hT : 0 ≤ T) :
    Q48d.WinMaxU.{u} V T (Kot.CD 2 K T) := by
  intro Ω mΩ P _ ℱ a ha M Sg hM
  have hcomp : IsCompleteFiltration P (augFiltration P ℱ) := augFiltration_isComplete ℱ
  have hM' := Kot.isHMC_aug hM
  have hW := isHMC_window hcomp ha hT hM'
  set V' : ℝ → ℝ → E →L[ℝ] E := fun t r => V (a + t) (a + r) with hV'def
  obtain ⟨hself, hcomp0, hcont0⟩ := hV (a + T) (by linarith)
  have hEV : Kot.EvolBound V' K T :=
    { norm_le := fun r t hr hrt htT => by
        have := hK (a + r) (a + t) (by linarith) (by linarith)
        simpa [hV'def, add_sub_add_left_eq_sub] using this
      comp := fun r t u hr hrt htu huT => by
        have := hcomp0 (a + r) (a + t) (a + u) (by linarith) (by linarith) (by linarith) (by linarith)
        exact this
      self := fun t ht0 htT => hself (a + t) ⟨by linarith, by linarith⟩ }
  have hcont' : ∀ x : E, ContinuousOn (fun p : ℝ × ℝ => V' p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} := by
    intro x
    have h := hcont0 x
    have hc : ContinuousOn (fun p : ℝ × ℝ => (a + p.1, a + p.2)) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} :=
      ((continuous_const.add continuous_fst).prodMk (continuous_const.add continuous_snd)).continuousOn
    refine h.comp hc fun p hp => ?_
    exact ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hcomp' : IsCompleteFiltration P (winFiltration (augFiltration P ℱ) a T) :=
    fun τ s hs h0 => hcomp (wt a T τ) s hs h0
  obtain ⟨m, Z', hm, hZc, hlim⟩ := Kot.exists_dyadic_limit hcomp' hW hEV hcont' hT
  have hmem : ∀ t ∈ Icc a (a + T), t - a ∈ Icc (0 : ℝ) T :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨fun t ω => Z' (t - a) ω, ?_, ?_, ?_, ?_⟩
  · -- the stochastic convolution
    intro t ht ε hε
    obtain ⟨δ, hδ, hconv⟩ := Kot.hconv_Z hcomp' hW hEV hcont' hT hm hlim (hmem t ht) ε hε
    refine ⟨δ, hδ, fun n r hr0 hrn hmono hmesh => ?_⟩
    have hr' := hconv n (fun i => r i - a) (by simp [hr0]) (by simp [hrn, sub_eq_zero]) 
      (fun i j h => by simpa using hmono h) (fun i => by simpa using hmesh i)
    refine lt_of_le_of_lt (le_of_eq ?_) hr'
    refine lintegral_congr fun ω => ?_
    congr 3
    rw [Q48d.riemannSum_id]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi1 : r i.castSucc - a ∈ Icc (0 : ℝ) T := by
      have := Q48d.mem_Icc_of_part hr0 hrn hmono i.castSucc
      exact ⟨by linarith [this.1], by linarith [this.2, ht.2]⟩
    have hi2 : r i.succ - a ∈ Icc (0 : ℝ) T := by
      have := Q48d.mem_Icc_of_part hr0 hrn hmono i.succ
      exact ⟨by linarith [this.1], by linarith [this.2, ht.2]⟩
    simp only [hV'def, wt_of_mem hi1, wt_of_mem hi2, add_sub_cancel]
    congr 1
    abel
  · -- measurability
    intro t ht
    have hτ := hmem t ht
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun k ω =>
      Kot.rsProc V' (fun τ ω => M (wt a T τ) ω - M a ω) (Kot.dy T (m k)) (2 ^ m k) (t - a) ω)
      (fun k => ?_) ?_
    · exact Kot.aestronglyMeasurable_rsTag hW (Kot.dy_mono hT _) (by rw [Kot.dy_zero]) (by rw [Kot.dy_top]) _ (t - a)
    · filter_upwards [hlim] with ω hω
      exact hω (t - a) hτ
  · -- continuity
    filter_upwards [hZc] with ω hω
    exact hω.comp (continuous_id.sub continuous_const).continuousOn fun t ht => hmem t ht
  · -- the bound
    have hb := Kot.sup_Z_bound hcomp' hW hEV hT hZc hlim (p := 2) (by norm_num)
    have hsup : ∀ ω, (⨆ t ∈ Icc a (a + T), ‖Z' (t - a) ω‖ₑ) = ⨆ τ ∈ Icc (0 : ℝ) T, ‖Z' τ ω‖ₑ := by
      intro ω
      refine le_antisymm (iSup₂_le fun t ht => ?_) (iSup₂_le fun τ hτ => ?_)
      · exact le_iSup₂ (f := fun τ (_ : τ ∈ Icc (0 : ℝ) T) => ‖Z' τ ω‖ₑ) (t - a) (hmem t ht)
      · have : a + τ ∈ Icc a (a + T) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        have h := le_iSup₂ (f := fun t (_ : t ∈ Icc a (a + T)) => ‖Z' (t - a) ω‖ₑ) (a + τ) this
        simpa using h
    calc ∫⁻ ω, (⨆ t ∈ Icc a (a + T), ‖Z' (t - a) ω‖ₑ) ^ 2 ∂P
        = ∫⁻ ω, (⨆ τ ∈ Icc (0 : ℝ) T, ‖Z' τ ω‖ₑ) ^ (2 : ℝ) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [hsup ω, ENNReal.rpow_two]
      _ ≤ ENNReal.ofReal (Kot.CD 2 K T) * ∫⁻ ω, (∫⁻ r in Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm
            ((fun σ ω => if σ ≤ T then Sg (a + σ) ω else 0) r ω))) ^ (2 / 2 : ℝ) ∂P := hb
      _ = ENNReal.ofReal (Kot.CD 2 K T) * ∫⁻ ω, (∫⁻ r in Icc a (a + T), ENNReal.ofReal (traceNormForm (Sg r ω))) ∂P := by
          congr 1
          refine lintegral_congr fun ω => ?_
          norm_num only
          rw [ENNReal.rpow_one, ← lintegral_Icc_shift (fun r => ENNReal.ofReal (traceNormForm (Sg r ω))) a T]
          refine setLIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
          simp only [hσ.2, if_true]

end WinMax

end HRS.Uniform.Q48e
