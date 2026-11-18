import HRS.Sections.QuenchAux14
import HRS.Sections.QuenchAux30

/-!
# Packet QUENCH (Q27): Proposition 7.13 (final assembly)

Relocation pattern: `Sec7Quench.lean` is not edited; the statements of `quench_modes`,
`quench_window_tensors`, `quench_equal_temperature` are reproduced verbatim as `<name>_proof`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Sec7

variable {d : ℕ}

theorem quench_modes_proof (hd : 2 ≤ d) {s β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀) (hne : β₀ ≠ β)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0)) (m : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P Z) :
    (∀ (k : PosHalf d) (b : Bool), ∃ B : ℝ≥0 → Ω → ℝ, IsBrownianReal B P ∧
        IndepFun (fun ω => NegSobolev.eval (Z 0 ω) (modeFn k.1 b)) (fun ω => fun t => B t ω) P ∧
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, NegSobolev.eval (Z t ω) (modeFn k.1 b) =
          NegSobolev.eval (Z 0 ω) (modeFn k.1 b) -
            lamMode d s β k.1 * (∫ u in Set.Icc (0 : ℝ) t, NegSobolev.eval (Z u ω) (modeFn k.1 b)) +
            Real.sqrt (2 / β) * (2 * Real.pi * Lattice.enorm k.1) * B t ω) ∧
    (∀ (k : PosHalf d) (b : Bool),
      ∫ ω, NegSobolev.eval (Z 0 ω) (modeFn k.1 b) ^ 2 ∂P = varMode d s β₀ k.1) ∧
    iIndepFun (fun (kb : PosHalf d × Bool) ω => fun t : ℝ≥0 =>
      NegSobolev.eval (Z t ω) (modeFn kb.1.1 kb.2)) P ∧
    (∀ (k : PosHalf d) (b : Bool) (a t r : ℝ), 0 ≤ a → 0 ≤ t → 0 ≤ r →
      ∫ ω, NegSobolev.eval (Z (a + t) ω) (modeFn k.1 b) * NegSobolev.eval (Z (a + r) ω) (modeFn k.1 b) ∂P =
        varMode d s β k.1 * Real.exp (-lamMode d s β k.1 * |t - r|) +
          deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
            Real.exp (-lamMode d s β k.1 * (t + r))) :=
  Qch.quench_modes_core hd hβ hβ₀ D hD m P Z hZ

example := (@quench_modes_proof : type_of% @HRS.Sec7.quench_modes)

theorem quench_window_tensors_proof (hd : 2 ≤ d) {s β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀) (hne : β₀ ≠ β)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0)) (m : ℝ) (hm : (d : ℝ) / 2 + 1 < m)
    (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P Z)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Zs : ℝ → Ω' → NegSobolev d m) (hZs : IsGaussianLimitField D (fun _ _ => 1) volume β m P' Zs) :
    let Δ : ℝ → (PathSpace d m T [×2]→L[ℝ] ℝ) → ℝ := fun a M =>
      ∫ ω, M ![procWin m T a Z ω, procWin m T a Z ω] ∂P -
        ∫ ω, M ![procWin m T 0 Zs ω, procWin m T 0 Zs ω] ∂P'
    (0 < lamStar d s β ∧ {k : PosHalf d | lamMode d s β k.1 = lamStar d s β}.Finite ∧
      {k : PosHalf d | lamMode d s β k.1 = lamStar d s β}.Nonempty) ∧
    (∀ a : ℝ, 0 ≤ a →
      Summable (fun k : PosHalf d => |deltaVar d s β β₀ k.1| * Real.exp (-2 * lamMode d s β k.1 * a) *
        (‖modePath m T (lamMode d s β k.1) (modeFn k.1 true)‖ ^ 2 +
          ‖modePath m T (lamMode d s β k.1) (modeFn k.1 false)‖ ^ 2)) ∧
      ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, Δ a M =
        ∑' k : PosHalf d, deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
          (M ![modePath m T (lamMode d s β k.1) (modeFn k.1 true),
               modePath m T (lamMode d s β k.1) (modeFn k.1 true)] +
            M ![modePath m T (lamMode d s β k.1) (modeFn k.1 false),
               modePath m T (lamMode d s β k.1) (modeFn k.1 false)])) ∧
    (∀ ε : ℝ, 0 < ε → ∃ a₀ : ℝ, ∀ a ≥ a₀, ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
      |Real.exp (2 * lamStar d s β * a) * Δ a M - slowTensor d s β β₀ m T M| ≤ ε) ∧
    (∃ M : PathSpace d m T [×2]→L[ℝ] ℝ, slowTensor d s β β₀ m T M ≠ 0) ∧
    ∃ cT CT : ℝ, 0 < cT ∧ cT ≤ CT ∧ ∀ a : ℝ, 0 ≤ a →
      (∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 → |Δ a M| ≤ CT * Real.exp (-2 * lamStar d s β * a)) ∧
      cT * Real.exp (-2 * lamStar d s β * a) ≤
        ⨆ M : {M : PathSpace d m T [×2]→L[ℝ] ℝ // ‖M‖ ≤ 1}, |Δ a M.1|
 := by
  intro Δ
  have hs0 : 0 ≤ s := hD.1 ▸ D.hs0
  have hsd : s < d := hD.1 ▸ D.hsd
  obtain ⟨Y, mf⟩ := Qch.modeField_of_limit hd hβ hβ₀ D hD P Z hZ
  obtain ⟨Ys, mf'⟩ := Qch.modeField_of_limit hd hβ hβ D hD P' Zs hZs
  have hser : ∀ a : ℝ, 0 ≤ a → ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, Δ a M =
      ∑' k : PosHalf d, deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
          (M ![modePath m T (lamMode d s β k.1) (modeFn k.1 true),
               modePath m T (lamMode d s β k.1) (modeFn k.1 true)] +
            M ![modePath m T (lamMode d s β k.1) (modeFn k.1 false),
               modePath m T (lamMode d s β k.1) (modeFn k.1 false)]) :=
    fun a ha M => Qch.window_series hd hs0 hsd hβ hβ₀ hm mf mf' hT ha M
  have hW : 0 ≤ ∑' k : PosHalf d, Qch.wk d s β β₀ m T k := tsum_nonneg fun k => by
    unfold Qch.wk; positivity
  have hup : ∀ a : ℝ, 0 ≤ a → ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 → |Δ a M| ≤
      (∑' k : PosHalf d, Qch.wk d s β β₀ m T k) * Real.exp (-2 * lamStar d s β * a) := by
    intro a ha M hM
    have h1 := Qch.upper_bound hd hs0 hsd hβ Δ hβ₀ hm hT hser ha M
    have h2 : 0 ≤ Real.exp (-2 * lamStar d s β * a) * ∑' k, Qch.wk d s β β₀ m T k :=
      mul_nonneg (Real.exp_pos _).le hW
    calc |Δ a M| ≤ ‖M‖ * (Real.exp (-2 * lamStar d s β * a) * ∑' k, Qch.wk d s β β₀ m T k) := h1
      _ ≤ 1 * (Real.exp (-2 * lamStar d s β * a) * ∑' k, Qch.wk d s β β₀ m T k) :=
          mul_le_mul_of_nonneg_right hM h2
      _ = _ := by ring
  obtain ⟨M0, c0, hM0, hc0, hslow, hΔ0⟩ := Qch.test_form hd hs0 hsd hβ Δ hβ₀ hne hT hser
  refine ⟨Qch.gap_facts hd hs0 hsd hβ, fun a ha =>
    ⟨Qch.summable_stmt hd hs0 hsd hβ hβ₀ hm hT ha, fun M => hser a ha M⟩, ?_, ⟨M0, by rw [hslow]; exact hc0⟩, ?_⟩
  · intro ε hε
    have ht := Qch.tendsto_tail (m := m) (T := T) hd hs0 hsd hβ hβ₀ hm hT
    have h1 : ∀ᶠ a : ℝ in atTop, (∑' k, Qch.gk d s β β₀ m T a k) < ε := ht.eventually (gt_mem_nhds hε)
    obtain ⟨a₀, ha₀⟩ := eventually_atTop.1 (h1.and (eventually_ge_atTop (0 : ℝ)))
    refine ⟨a₀, fun a ha M hM => ?_⟩
    obtain ⟨h2, h3⟩ := ha₀ a ha
    have h4 := Qch.tail_bound hd hs0 hsd hβ Δ hβ₀ hm hT hser h3 M
    have h5 : 0 ≤ ∑' k, Qch.gk d s β β₀ m T a k :=
      tsum_nonneg fun k => Qch.gk_nonneg hd hs0 hsd hβ hβ₀ k
    calc _ ≤ ‖M‖ * ∑' k, Qch.gk d s β β₀ m T a k := h4
      _ ≤ 1 * ∑' k, Qch.gk d s β β₀ m T a k := mul_le_mul_of_nonneg_right hM h5
      _ ≤ ε := by linarith
  · refine ⟨|c0|, |c0| + ∑' k : PosHalf d, Qch.wk d s β β₀ m T k, abs_pos.2 hc0,
      le_add_of_nonneg_right hW, fun a ha => ⟨fun M hM => ?_, ?_⟩⟩
    · calc |Δ a M| ≤ (∑' k : PosHalf d, Qch.wk d s β β₀ m T k) * Real.exp (-2 * lamStar d s β * a) :=
            hup a ha M hM
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg c0]) (Real.exp_pos _).le
    · have hbdd : BddAbove (Set.range fun M : {M : PathSpace d m T [×2]→L[ℝ] ℝ // ‖M‖ ≤ 1} => |Δ a M.1|) :=
        ⟨_, by rintro _ ⟨M, rfl⟩; exact hup a ha M.1 M.2⟩
      refine le_ciSup_of_le hbdd ⟨M0, hM0⟩ ?_
      show |c0| * Real.exp (-2 * lamStar d s β * a) ≤ |Δ a M0|
      rw [hΔ0 a ha, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact le_of_eq (mul_comm _ _)

example := (@quench_window_tensors_proof : type_of% @HRS.Sec7.quench_window_tensors)

theorem quench_equal_temperature_proof (hd : 2 ≤ d) {s β : ℝ} (hβ : 0 < β)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0)) (m : ℝ) (hm : (d : ℝ) / 2 + 1 < m)
    (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β m P Z)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Zs : ℝ → Ω' → NegSobolev d m) (hZs : IsGaussianLimitField D (fun _ _ => 1) volume β m P' Zs) :
    ∀ a : ℝ, 0 ≤ a → ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ,
      ∫ ω, M ![procWin m T a Z ω, procWin m T a Z ω] ∂P =
        ∫ ω, M ![procWin m T 0 Zs ω, procWin m T 0 Zs ω] ∂P'
 := by
  intro a ha M
  have hs0 : 0 ≤ s := hD.1 ▸ D.hs0
  have hsd : s < d := hD.1 ▸ D.hsd
  obtain ⟨Y, mf⟩ := Qch.modeField_of_limit hd hβ hβ D hD P Z hZ
  obtain ⟨Ys, mf'⟩ := Qch.modeField_of_limit hd hβ hβ D hD P' Zs hZs
  have h := Qch.window_series hd hs0 hsd hβ hβ hm mf mf' hT ha M
  have h0 : ∀ k : PosHalf d, deltaVar d s β β k.1 = 0 := fun k => by unfold deltaVar; exact sub_self _
  simp only [h0, zero_mul, tsum_zero] at h
  exact sub_eq_zero.1 h

example := (@quench_equal_temperature_proof : type_of% @HRS.Sec7.quench_equal_temperature)

end Sec7

end HRS
