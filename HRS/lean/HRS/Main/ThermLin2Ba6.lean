import HRS.Main.ThermLin2Ba5

/-!
# THERMLIN2, packet Ba, part 6: D4' (`tl2_zero_start_law_unique`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- The two spellings of the window path agree. -/
theorem tl2Ba_uwin_eq {Ω : Type} (m T a : ℝ) (Z : ℝ → Ω → NegSobolev d m) :
    (Uniform.windowPath a T Z : Ω → PathSp T (NegSobolev d m)) = HRS.Main.windowPath m T a Z := by
  rw [HRS.Uniform.Comp28.windowPath_shift]
  funext ω
  exact (toPath_eq_windowPath m T _ ω).symm

/-- Finite-dimensional laws of a zero-start `W`-stochastic convolution depend only on `(W, Cb)`. -/
theorem tl2Ba_zb_fdd {m T K : ℝ} (hT : 0 < T) (hK : 0 ≤ K)
    (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hplain : IsPlainEvolution Wev T)
    (hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖Wev t r‖ ≤ K)
    (Cb : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)
    (hCb0 : ∀ σ : ℝ, σ ∉ Set.Icc 0 T → Cb σ = 0)
    {Ω₂ : Type} [mΩ₂ : MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂] {ℱ₂ : Filtration ℝ mΩ₂}
    (Ĝ₂ Zb₂ : ℝ → Ω₂ → NegSobolev d m)
    (hĜ₂ : IsHilbertMartingaleWithCovariation P₂ ℱ₂ T Ĝ₂ (fun r _ => Cb r))
    (hZ₂ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P₂ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ₂ 0 t (Zb₂ t))
    (hm₂ : ∀ t, Measurable (Zb₂ t)) {p : ℕ} (τ : Fin p → ℝ) (hτ : ∀ i, τ i ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ i, MemSobolev m (φ i)) :
    P₂.map (fun ω => (WithLp.toLp 2 fun i => NegSobolev.eval (Zb₂ (τ i) ω) (φ i) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a b =>
        ∫ σ in Set.Icc 0 (min (τ a) (τ b)),
          Cb σ (pullbackVec (HRS.Uniform.Comp28.plainData Wev) (τ a) σ (gfb4_ell m (φ a)))
            (pullbackVec (HRS.Uniform.Comp28.plainData Wev) (τ b) σ (gfb4_ell m (φ b)))) := by
  obtain ⟨G', hG', hGc, hGz, hGG⟩ := gfb4_modify P₂ ℱ₂ hT.le Ĝ₂ Cb hCb0 hĜ₂
  have hZ' : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsStochConv P₂ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G' 0 t (Zb₂ t) :=
    fun t ht => gfb4_isStochConv_congr P₂ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) ht.1
      (fun τ hτ => hGG τ ⟨hτ.1, hτ.2.trans ht.2⟩) (hZ₂ t ht)
  exact t25p_Zb_gaussian hK hT Wev hplain.2.2 hWb P₂ G' Cb hG' hGc hGz Zb₂ hZ' hm₂ τ hτ φ hφ

/-- D4' proof. -/
theorem tl2_zero_start_law_unique_proof {m T a K : ℝ} (hT : 0 < T) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hplain : IsPlainEvolution Wev (a + T))
    (hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖Wev t r‖ ≤ K)
    (Cb : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)
    {Ω₂ Ω₃ : Type} [mΩ₂ : MeasurableSpace Ω₂] [mΩ₃ : MeasurableSpace Ω₃]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂] (P₃ : Measure Ω₃) [IsProbabilityMeasure P₃]
    {ℱ₂ : Filtration ℝ mΩ₂} {ℱ₃ : Filtration ℝ mΩ₃} (Ĝ₂ Zb₂ : ℝ → Ω₂ → NegSobolev d m) (Ĝ₃ Zb₃ : ℝ → Ω₃ → NegSobolev d m)
    (hĜ₂ : IsHilbertMartingaleWithCovariation P₂ ℱ₂ (a + T) Ĝ₂ (fun r _ => Cb r))
    (hĜ₃ : IsHilbertMartingaleWithCovariation P₃ ℱ₃ (a + T) Ĝ₃ (fun r _ => Cb r))
    (hCb0 : ∀ σ : ℝ, σ ∉ Set.Icc 0 (a + T) → Cb σ = 0)
    (hZ₂ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), IsStochConv P₂ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ₂ 0 t (Zb₂ t))
    (hZ₃ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), IsStochConv P₃ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ₃ 0 t (Zb₃ t))
    (hm₂ : ∀ t, Measurable (Zb₂ t)) (hm₃ : ∀ t, Measurable (Zb₃ t))
    (hc₂ : ∀ᵐ ω ∂P₂, ContinuousOn (fun t => Zb₂ t ω) (Set.Icc 0 (a + T)))
    (hc₃ : ∀ᵐ ω ∂P₃, ContinuousOn (fun t => Zb₃ t ω) (Set.Icc 0 (a + T))) :
    law P₂ (Uniform.windowPath a T Zb₂) = law P₃ (Uniform.windowPath a T Zb₃) := by
  have hT' : 0 < a + T := by linarith
  rw [tl2Ba_uwin_eq, tl2Ba_uwin_eq]
  refine tl2Ba_window_law_eq hT.le ha ha P₂ P₃ Zb₂ Zb₃ hm₂ hm₃ hc₂ hc₃ ?_
  intro p ts φ hts hφ
  have hts' : ∀ i, a + ts i ∈ Set.Icc (0 : ℝ) (a + T) := fun i =>
    ⟨by linarith [(hts i).1], by linarith [(hts i).2]⟩
  have hmem : ∀ i, MemSobolev m (φ i) := fun i => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ i) m
  rw [tl2Ba_zb_fdd hT' hK Wev hplain hWb Cb hCb0 P₂ Ĝ₂ Zb₂ hĜ₂ hZ₂ hm₂ (fun i => a + ts i) hts' φ hmem,
    tl2Ba_zb_fdd hT' hK Wev hplain hWb Cb hCb0 P₃ Ĝ₃ Zb₃ hĜ₃ hZ₃ hm₃ (fun i => a + ts i) hts' φ hmem]

example := (@tl2_zero_start_law_unique_proof : type_of% @tl2_zero_start_law_unique)

end HRS.ThermLin.Plan2
