import HRS.MC.S7PIG5Core
import HRS.MC.S7PIG1
import HRS.MC.S7PIG3
import HRS.MC.S7PIS1Path2
import HRS.MC.S7PICMain
import HRS.MC.S7PIDefs

/-!
# Packet piG5 (PI-G5): the `J` Riemann-Stieltjes integral, removal of the projection

`s7_PIG_RS_J_proof` (statement copied verbatim from `HRS/MC/S7PIPlan.lean`).  Route: `S7PIG5_core` (the abstract
`measure_projection_proof` on `E = projTensor X 2`) applied to `Jc`, `M τ = D²u_Φ(τ, 𝖳_τ w)`,
`ML L τ = projHeatD γ Φ (Pj L) 2 τ (𝖳_τ w)`; the continuity and the uniform convergence of the packet G3
(`s7_PIG_conv_equicont_proof`, `j = 2`); `jPair = Jc b - Jc a` by PI-C; G1 identifies `D²(heat of Φ∘Pj L)` with
`projHeatD ∘ Pj^{⊗2}`.  Namespace `HRS.MC.Sec7.S7PIG5`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIG5

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- `jPair` of an interval `(a,b]` is the increment of the cumulative path. -/
theorem S7PIG5_jPair_eq (R : Regime d) (m T : ℝ) (z : ℝ → NegSobolev d m)
    (Jc : ℝ → TensorDual (PathSpace d m T) 2)
    (hJ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IsJValue R.D R.ρ m T z (Set.Ioc a b) (Jc b - Jc a))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    jPair R.D R.ρ m T z (Set.Ioc a b) M = (Jc b - Jc a) M := by
  have h : ∃ J, IsJValue R.D R.ρ m T z (Set.Ioc a b) J := ⟨_, hJ a b ha hab hb⟩
  unfold jPair
  rw [dif_pos h]
  have := HRS.MC.Sec7.S7PIC.s7_PI_C_J_unique_proof R m T z (Set.Ioc a b) _ _ h.choose_spec (hJ a b ha hab hb)
  rw [this]

/-- The second derivative of the heat function of a projected functional. -/
theorem S7PIG5_deriv_eq {m T : ℝ} (γ : ℝ → Measure (PathSpace d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (P : PathSpace d m T →L[ℝ] PathSpace d m T) {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ)
    (u : ℝ) (y : PathSpace d m T) :
    iteratedFDeriv ℝ 2 (heatFn γ (fun x => Φ (P x)) u) y =
      (projHeatD γ Φ P 2 u y).compContinuousLinearMap (fun _ => P) := by
  ext v
  rw [HRS.MC.Sec7.S7PIG1.s7_PIG_proj_deriv_proof γ hγp P hΦ 2 (by norm_num) u y v]
  rfl

/-- Pointwise bound of `projHeatD` of order `2`. -/
theorem S7PIG5_projHeatD_norm_le {m T : ℝ} (γ : ℝ → Measure (PathSpace d m T))
    (hγp : ∀ u, IsProbabilityMeasure (γ u)) (P : PathSpace d m T →L[ℝ] PathSpace d m T)
    {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ) (u : ℝ) (y : PathSpace d m T) :
    ‖projHeatD γ Φ P 2 u y‖ ≤ cbNorm 5 Φ := by
  have := hγp u
  unfold projHeatD
  have hb := norm_integral_le_of_norm_le_const (μ := γ u)
    (f := fun z => iteratedFDeriv ℝ 2 Φ (P (y + z))) (C := cbNorm 5 Φ)
    (Filter.Eventually.of_forall fun z => HRS.MC.Sec7.S7PIL.S7PIL_le_cbNorm hΦ (by norm_num) _)
  simpa [Measure.real] using hb

/-- The second derivative of the heat function of `Φ ∘ P` is bounded by `cbNorm 5 Φ` (`‖P‖ ≤ 1`). -/
theorem S7PIG5_deriv_norm_le {m T : ℝ} (γ : ℝ → Measure (PathSpace d m T))
    (hγp : ∀ u, IsProbabilityMeasure (γ u)) (P : PathSpace d m T →L[ℝ] PathSpace d m T) (hP : ‖P‖ ≤ 1)
    {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ) (u : ℝ) (y : PathSpace d m T) :
    ‖iteratedFDeriv ℝ 2 (heatFn γ (fun x => Φ (P x)) u) y‖ ≤ cbNorm 5 Φ := by
  rw [S7PIG5_deriv_eq γ hγp P hΦ u y]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin 2, ‖P‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hP
  calc ‖projHeatD γ Φ P 2 u y‖ * ∏ _i : Fin 2, ‖P‖ ≤ ‖projHeatD γ Φ P 2 u y‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ cbNorm 5 Φ := by rw [mul_one]; exact S7PIG5_projHeatD_norm_le γ hγp P hΦ u y

/-- **G5 (the `𝒥` Riemann-Stieltjes integral: removal of the projection, deterministic)**. -/
theorem s7_PIG_RS_J_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    (hγp : ∀ u, IsProbabilityMeasure (γ u)) (Pj : ℕ → (PathSpace d m T →L[ℝ] PathSpace d m T))
    (hPj : ∀ L w, Pj L w = projPoly m T hT.le L w) (hP1 : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    (hTconv : ∀ (j : ℕ) (v : TensorDual (PathSpace d m T) j), v ∈ projTensor (PathSpace d m T) j →
      Tendsto (fun L => tensorPow j (Pj L) v) atTop (𝓝 v))
    {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ) (w : PathSpace d m T) (z : ℝ → NegSobolev d m)
    (Jc : ℝ → TensorDual (PathSpace d m T) 2) (K : ℝ) (hJc0 : Jc 0 = 0)
    (hJ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IsJValue R.D R.ρ m T z (Set.Ioc a b) (Jc b - Jc a))
    (hLip : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → ‖Jc b - Jc a‖ ≤ K * (b - a)) :
    ∃ I : ℝ, IsRS T (fun τ a b' => jPair R.D R.ρ m T z (Set.Ioc a b')
        (iteratedFDeriv ℝ 2 (heatFn γ Φ τ) (predicted R.D R.ρ w τ))) I ∧ |I| ≤ cbNorm 5 Φ * (K * T) ∧
      ∃ IL : ℕ → ℝ, (∀ L, IsRS T (fun τ a b' => jPair R.D R.ρ m T z (Set.Ioc a b')
          (iteratedFDeriv ℝ 2 (heatFn γ (fun x => Φ (Pj L x)) τ) (predicted R.D R.ρ w τ))) (IL L)) ∧
        (∀ L, |IL L| ≤ cbNorm 5 Φ * (K * T)) ∧ Tendsto IL atTop (𝓝 I) := by
  have hY : ContinuousOn (fun τ => predicted R.D R.ρ w τ) (Set.Icc 0 T) :=
    continuousOn_iff_continuous_domRestrict.2
      ((HRS.MC.Sec7.S7PIS1.s7_PIS_path_facts_proof R m hm T hT).2.2 w)
  obtain ⟨hc, hcL, hu⟩ := HRS.MC.Sec7.S7PIG3.s7_PIG_conv_equicont_proof R m hm T hT γ hγ hγp Pj hPj hP1 hconv
    hΦ (fun τ => predicted R.D R.ρ w τ) hY 2 le_rfl
  have hK0 : 0 ≤ K := by
    have h := hLip 0 T le_rfl hT.le le_rfl
    have : 0 ≤ K * (T - 0) := (ContinuousLinearMap.opNorm_nonneg _).trans h
    rw [sub_zero] at this
    exact nonneg_of_mul_nonneg_left this hT
  have hC0 : 0 ≤ cbNorm 5 Φ := HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΦ 0
  obtain ⟨I, hI, IL, hIL, hlim⟩ := S7PIG5_core T hT Pj hP1 (fun v hv => hTconv 2 v hv) Jc K hJc0
    (fun a b ha hab hb => (hJ a b ha hab hb).1) hLip
    (fun τ => iteratedFDeriv ℝ 2 (heatFn γ Φ τ) (predicted R.D R.ρ w τ))
    (fun L τ => projHeatD γ Φ (Pj L) 2 τ (predicted R.D R.ρ w τ)) hc hcL hu
  have hI' : IsRS T (fun τ a b' => jPair R.D R.ρ m T z (Set.Ioc a b')
        (iteratedFDeriv ℝ 2 (heatFn γ Φ τ) (predicted R.D R.ρ w τ))) I :=
    S7PIG5_rs_congr hI (fun τ a b ha haτ hτb hbT => (S7PIG5_jPair_eq R m T z Jc hJ a b ha
      (haτ.trans hτb) hbT _).symm)
  have hIL' : ∀ L, IsRS T (fun τ a b' => jPair R.D R.ρ m T z (Set.Ioc a b')
          (iteratedFDeriv ℝ 2 (heatFn γ (fun x => Φ (Pj L x)) τ) (predicted R.D R.ρ w τ))) (IL L) := by
    intro L
    refine S7PIG5_rs_congr (hIL L) (fun τ a b ha haτ hτb hbT => ?_)
    rw [S7PIG5_jPair_eq R m T z Jc hJ a b ha (haτ.trans hτb) hbT, S7PIG5_deriv_eq γ hγp (Pj L) hΦ]
    rfl
  have hbound : ∀ (M : ℝ → PathSpace d m T [×2]→L[ℝ] ℝ), (∀ τ, ‖M τ‖ ≤ cbNorm 5 Φ) →
      ∀ τ a b : ℝ, 0 ≤ a → a ≤ τ → τ ≤ b → b ≤ T →
        |jPair R.D R.ρ m T z (Set.Ioc a b) (M τ)| ≤ (cbNorm 5 Φ * K) * (b - a) := by
    intro M hM τ a b ha haτ hτb hbT
    rw [S7PIG5_jPair_eq R m T z Jc hJ a b ha (haτ.trans hτb) hbT, ← Real.norm_eq_abs]
    calc ‖(Jc b - Jc a) (M τ)‖ ≤ ‖Jc b - Jc a‖ * ‖M τ‖ := (Jc b - Jc a).le_opNorm _
      _ ≤ (K * (b - a)) * cbNorm 5 Φ :=
          mul_le_mul (hLip a b ha (haτ.trans hτb) hbT) (hM τ) (norm_nonneg _)
            (mul_nonneg hK0 (by linarith [haτ.trans hτb]))
      _ = (cbNorm 5 Φ * K) * (b - a) := by ring
  refine ⟨I, hI', ?_, IL, hIL', ?_, hlim⟩
  · have := S7PIG5_rs_bound hT hI' (hbound (fun τ => iteratedFDeriv ℝ 2 (heatFn γ Φ τ) (predicted R.D R.ρ w τ))
      (fun τ => S7PIG5_deriv_norm_le γ hγp (ContinuousLinearMap.id ℝ _) ContinuousLinearMap.norm_id_le hΦ τ _))
    calc |I| ≤ (cbNorm 5 Φ * K) * T := this
      _ = cbNorm 5 Φ * (K * T) := by ring
  · intro L
    have := S7PIG5_rs_bound hT (hIL' L) (hbound
      (fun τ => iteratedFDeriv ℝ 2 (heatFn γ (fun x => Φ (Pj L x)) τ) (predicted R.D R.ρ w τ))
      (fun τ => S7PIG5_deriv_norm_le γ hγp (Pj L) (hP1 L) hΦ τ _))
    calc |IL L| ≤ (cbNorm 5 Φ * K) * T := this
      _ = cbNorm 5 Φ * (K * T) := by ring

end HRS.MC.Sec7.S7PIG5

end
