import HRS.Main.GFB4Aux5

/-!
# GFB4, part 6: joint Gaussian law of the pairings `⟨Z̄_{t_a}, φ_a⟩`
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Q45

variable {d : ℕ}

/-- The functional `z ↦ z(φ)` on `E_m`, for a test function `φ ∈ H^m`. -/
def gfb4_ell (m : ℝ) (φ : Torus d → ℝ) : NegSobolev d m →L[ℝ] ℝ := innerSL ℝ (lpFun m φ)

theorem gfb4_ell_apply {m : ℝ} {φ : Torus d → ℝ} (hφ : MemSobolev m φ) (z : NegSobolev d m) :
    gfb4_ell m φ z = NegSobolev.eval z φ := by
  unfold gfb4_ell
  rw [eval_lpFun z hφ]
  simp [real_inner_comm]

theorem gfb4_pullback_weak {γ m T : ℝ} (EV : EvolData (NegSobolev d γ) (NegSobolev d m))
    (hev : EV.IsEvolution T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (ℓ : NegSobolev d m →L[ℝ] ℝ)
    (x : NegSobolev d γ) :
    ContinuousOn (fun σ => inner ℝ (pullbackVec EV t σ ℓ) x) (Set.Icc 0 t) := by
  have e : (fun σ => inner ℝ (pullbackVec EV t σ ℓ) x) = fun σ => ℓ (EV.VE t σ (EV.j x)) :=
    funext fun σ => pullback_inner EV t σ ℓ x
  rw [e]
  have hc := hev.cont_E (EV.j x)
  have hmap : Set.MapsTo (fun r : ℝ => (t, r)) (Set.Icc 0 t)
      {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} := fun r hr => ⟨hr.1, hr.2, ht.2⟩
  exact ℓ.continuous.comp_continuousOn (hc.comp (Continuous.continuousOn (by fun_prop)) hmap)

theorem gfb4_Zb_gaussian {γ m T K : ℝ} (hT0 : 0 < T) (EV : EvolData (NegSobolev d γ) (NegSobolev d m))
    (hS : EV.MaxHyp T K) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (P' : Measure Ω')
    [IsProbabilityMeasure P'] {ℱ'' : Filtration ℝ mΩ'} (G : ℝ → Ω' → NegSobolev d γ)
    (Cd : ℝ → NegSobolev d γ →L[ℝ] NegSobolev d γ →L[ℝ] ℝ)
    (hG : IsHilbertMartingaleWithCovariation P' ℱ'' T G (fun r _ => Cd r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (Zb : ℝ → Ω' → NegSobolev d m)
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P' EV.VE EV.j G 0 t (Zb t))
    (hZbm : ∀ t, Measurable (Zb t)) {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, MemSobolev m (φ a)) :
    P'.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Zb (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a b =>
        ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
          Cd σ (pullbackVec EV (ts a) σ (gfb4_ell m (φ a))) (pullbackVec EV (ts b) σ (gfb4_ell m (φ b)))) := by
  have hT : 0 ≤ T := hT0.le
  set B : ℝ := detConst T K * ∑ b, ‖gfb4_ell m (φ b)‖ with hB
  refine gfb4_vec_gaussian hG hGc hGz hT0 ts hts (fun a σ => pullbackVec EV (ts a) σ (gfb4_ell m (φ a)))
    (B := B) ?_ ?_ _ ?_ ?_
  · intro a σ hσ
    have h1 := norm_pullback_le hT hS hσ.1 hσ.2 (hts a).2 (gfb4_ell m (φ a))
    refine h1.trans ?_
    unfold detConst
    refine mul_le_mul_of_nonneg_left ?_ (detConst_pos T K).le
    exact Finset.single_le_sum (f := fun b => ‖gfb4_ell m (φ b)‖) (fun b _ => norm_nonneg _) (Finset.mem_univ a)
  · intro a x
    exact gfb4_pullback_weak EV hS.1 (hts a) _ x
  · refine measurable_toLp_eval fun a => ?_
    exact (continuous_eval_const (hφ a)).measurable.comp (hZbm _)
  · intro a
    refine gfb4_L2_of_stochConv P' EV G hT (hts a).1 (hts a).2 (Zb (ts a)) (hZb _ (hts a)) (gfb4_ell m (φ a)) _ ?_
    intro ω
    simp [gfb4_ell_apply (hφ a)]

end HRS.GF
