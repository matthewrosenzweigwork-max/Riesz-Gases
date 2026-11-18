import HRS.Sections.QuenchFinal
import HRS.MC.Q714GTMain
import HRS.MD.EQInterpHolder

/-!
# Packet ASM (row 7.14), part 1: elementary lemmas for the assembly

* bounds from `Φ ∈ CbUnitBall B 5`;
* the waiting-time algebra `√N e^{-2λ a} = exp(-2λ(a - log N/(4λ)))`;
* sequence lemmas turning the window-level estimates (P2), (P3) into the statements of Corollary 7.14;
* `slowTensor` and a uniformly bounded family of bilinear forms integrate to a continuous linear functional.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.Asm

open HRS HRS.Sec7

/-! ### Test functions -/

section Cb

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

theorem asm_memCb4 {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5) : MemCb 4 Φ :=
  ⟨hΦ.1.of_le (by norm_num), fun j hj => hΦ.2.1 j (by omega)⟩

theorem asm_norm2 {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5) (y : B) :
    ‖iteratedFDeriv ℝ 2 Φ y‖ ≤ 1 :=
  iteratedFDeriv_norm_le_of_mem hΦ (by norm_num) y

theorem asm_norm4 {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5) (y : B) :
    ‖iteratedFDeriv ℝ 4 Φ y‖ ≤ 1 :=
  iteratedFDeriv_norm_le_of_mem hΦ (by norm_num) y

/-- Integrating a continuous linear functional of `D²Φ(G)`. -/
theorem asm_integral_clm {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → B} (hG : AEMeasurable G P) {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5)
    (L S : (B [×2]→L[ℝ] ℝ) →L[ℝ] ℝ) (c r η : ℝ)
    (h : ∀ M : B [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 → |c * L M - r * S M| ≤ η) :
    |c * ∫ ω, L (iteratedFDeriv ℝ 2 Φ (G ω)) ∂P - r * ∫ ω, S (iteratedFDeriv ℝ 2 Φ (G ω)) ∂P|
      ≤ η := by
  have hcont : Continuous (iteratedFDeriv ℝ 2 Φ) := hΦ.1.continuous_iteratedFDeriv (by norm_num)
  have hHint : Integrable (fun ω => iteratedFDeriv ℝ 2 Φ (G ω)) P :=
    Integrable.of_bound (hcont.comp_aestronglyMeasurable hG.aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => asm_norm2 hΦ _)
  have e : c * ∫ ω, L (iteratedFDeriv ℝ 2 Φ (G ω)) ∂P - r * ∫ ω, S (iteratedFDeriv ℝ 2 Φ (G ω)) ∂P
      = ∫ ω, (c * L (iteratedFDeriv ℝ 2 Φ (G ω)) - r * S (iteratedFDeriv ℝ 2 Φ (G ω))) ∂P := by
    rw [integral_sub ((L.integrable_comp hHint).const_mul c) ((S.integrable_comp hHint).const_mul r),
      integral_const_mul, integral_const_mul]
  rw [e]
  have hη : 0 ≤ η := by
    have := h 0 (by simp)
    simp at this
    exact this
  have := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun ω => c * L (iteratedFDeriv ℝ 2 Φ (G ω)) - r * S (iteratedFDeriv ℝ 2 Φ (G ω))) (C := η)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact h _ (asm_norm2 hΦ _))
  simpa [Real.norm_eq_abs] using this

end Cb

/-! ### Waiting-time algebra -/

theorem asm_sqrt_mul_exp {l : ℝ} (hl : l ≠ 0) (N : ℕ) (hN : 1 ≤ N) (a : ℝ) :
    Real.sqrt N * Real.exp (-2 * l * a) =
      Real.exp (-2 * l * (a - Real.log N / (4 * l))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : Real.sqrt N = Real.exp (Real.log N / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos]; congr 1; ring
  rw [h1, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem asm_waiting_iff {l : ℝ} (hl : 0 < l) (a : ℕ → ℝ) :
    Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-2 * l * a N)) atTop (𝓝 0) ↔
      Tendsto (fun N : ℕ => a N - Real.log N / (4 * l)) atTop atTop := by
  have hev : (fun N : ℕ => Real.sqrt N * Real.exp (-2 * l * a N)) =ᶠ[atTop]
      fun N : ℕ => Real.exp (-2 * l * (a N - Real.log N / (4 * l))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN using asm_sqrt_mul_exp hl.ne' N hN (a N)
  rw [tendsto_congr' hev, Real.tendsto_exp_comp_nhds_zero]
  set x : ℕ → ℝ := fun N => a N - Real.log N / (4 * l) with hx
  have h2l : 0 < 2 * l := by linarith
  constructor
  · intro h
    have h1 : Tendsto (fun N => -(2 * l * x N)) atTop atBot := h.congr fun N => by ring
    have h2 := tendsto_neg_atBot_iff.1 h1
    have := h2.const_mul_atTop (inv_pos.2 h2l)
    exact this.congr fun N => inv_mul_cancel_left₀ h2l.ne' _
  · intro h
    have h' := h.const_mul_atTop h2l
    have := tendsto_neg_atTop_atBot.comp h'
    exact this.congr fun N => by simp only [Function.comp]; ring

theorem asm_tendsto_shift {l τ : ℝ} (hl : 0 < l) (a : ℕ → ℝ)
    (h : Tendsto (fun N : ℕ => a N - Real.log N / (4 * l) - τ) atTop (𝓝 0)) :
    Tendsto a atTop atTop ∧
      Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-2 * l * a N)) atTop
        (𝓝 (Real.exp (-2 * l * τ))) := by
  have hx : Tendsto (fun N : ℕ => a N - Real.log N / (4 * l)) atTop (𝓝 τ) := by
    have := h.add_const τ
    simpa using this
  refine ⟨?_, ?_⟩
  · have hlog : Tendsto (fun N : ℕ => Real.log N / (4 * l)) atTop atTop :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by positivity)
    have := hlog.atTop_add hx
    refine this.congr fun N => by simp
  · have h2 : Tendsto (fun N : ℕ => Real.exp (-2 * l * (a N - Real.log N / (4 * l)))) atTop
        (𝓝 (Real.exp (-2 * l * τ))) :=
      ((Real.continuous_exp.tendsto _).comp (hx.const_mul (-2 * l)))
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN using (asm_sqrt_mul_exp hl.ne' N hN (a N)).symm

/-! ### Sequence lemmas -/

section Seq

variable {ι : Type}

/-- From the window-level expansion (P2), (P3) to the critical expansion along `a_N`. -/
theorem asm_seq_expansion {l τ : ℝ} (hl : 0 < l) (S : Set ι) (D : ℝ → ι → ℝ) (Sl : ι → ℝ)
    (C : ℝ)
    (hP2 : ∀ a : ℝ, 0 ≤ a → ∀ i ∈ S, |D a i| ≤ C * Real.exp (-2 * l * a))
    (hP3 : ∀ ε : ℝ, 0 < ε → ∃ a₀ : ℝ, ∀ a : ℝ, a₀ ≤ a → ∀ i ∈ S,
      |Real.exp (2 * l * a) * D a i - Sl i / 2| ≤ ε)
    (a : ℕ → ℝ)
    (h : Tendsto (fun N : ℕ => a N - Real.log N / (4 * l) - τ) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ i ∈ S,
      |Real.sqrt N * D (a N) i - Real.exp (-2 * l * τ) / 2 * Sl i| ≤ ε := by
  obtain ⟨hatop, hr⟩ := asm_tendsto_shift hl a h
  set r' := Real.exp (-2 * l * τ) with hr'
  have hr'pos : 0 < r' := Real.exp_pos _
  -- bound on `Sl/2`
  obtain ⟨a₁, ha₁⟩ := hP3 1 one_pos
  have hSl : ∀ i ∈ S, |Sl i / 2| ≤ |C| + 1 := by
    intro i hi
    set b := max a₁ 0
    have h1 := ha₁ b (le_max_left _ _) i hi
    have h2 := hP2 b (le_max_right _ _) i hi
    have h3 : |Real.exp (2 * l * b) * D b i| ≤ |C| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (2 * l * b) * |D b i| ≤ Real.exp (2 * l * b) * (C * Real.exp (-2 * l * b)) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = C := by
            rw [← mul_assoc, mul_comm _ C, mul_assoc, ← Real.exp_add]; simp
        _ ≤ |C| := le_abs_self C
    have := abs_sub_abs_le_abs_sub (Sl i / 2) (Real.exp (2 * l * b) * D b i)
    rw [abs_sub_comm (Sl i / 2)] at this
    linarith
  set ε₁ := ε / (2 * (r' + 1)) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  obtain ⟨a₀, ha₀⟩ := hP3 ε₁ hε₁pos
  have hev1 : ∀ᶠ N : ℕ in atTop, max a₀ 0 ≤ a N := hatop.eventually_ge_atTop _
  have hev2 : ∀ᶠ N : ℕ in atTop, Real.sqrt N * Real.exp (-2 * l * a N) ≤ r' + 1 :=
    hr.eventually_le_const (by linarith)
  have hev3 : ∀ᶠ N : ℕ in atTop,
      |Real.sqrt N * Real.exp (-2 * l * a N) - r'| * (|C| + 1) ≤ ε / 2 := by
    have h4 : Tendsto (fun N : ℕ => |Real.sqrt N * Real.exp (-2 * l * a N) - r'| * (|C| + 1))
        atTop (𝓝 (|r' - r'| * (|C| + 1))) :=
      ((hr.sub_const r').abs).mul_const _
    simp only [sub_self, abs_zero, zero_mul] at h4
    exact h4.eventually_le_const (by linarith)
  obtain ⟨N₀, hN₀⟩ := (hev1.and (hev2.and hev3)).exists_forall_of_atTop
  refine ⟨N₀, fun N hN hN1 i hi => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hN₀ N hN
  set rN := Real.sqrt N * Real.exp (-2 * l * a N) with hrN
  have hrN0 : 0 ≤ rN := by positivity
  have hD := ha₀ (a N) (le_trans (le_max_left _ _) h1) i hi
  have hsq : Real.sqrt N = rN * Real.exp (2 * l * a N) := by
    rw [hrN, mul_assoc, ← Real.exp_add]; simp
  have key : Real.sqrt N * D (a N) i - r' / 2 * Sl i =
      rN * (Real.exp (2 * l * a N) * D (a N) i - Sl i / 2) + (rN - r') * (Sl i / 2) := by
    rw [hsq]; ring
  rw [show r' / 2 * Sl i = r' * (Sl i / 2) by ring] at key ⊢
  rw [key]
  calc _ ≤ |rN * (Real.exp (2 * l * a N) * D (a N) i - Sl i / 2)| + |(rN - r') * (Sl i / 2)| :=
        abs_add_le _ _
    _ ≤ rN * ε₁ + |rN - r'| * (|C| + 1) := by
        have e1 : |rN * (Real.exp (2 * l * a N) * D (a N) i - Sl i / 2)| =
            rN * |Real.exp (2 * l * a N) * D (a N) i - Sl i / 2| := by
          rw [abs_mul, abs_of_nonneg hrN0]
        have e2 : |(rN - r') * (Sl i / 2)| = |rN - r'| * |Sl i / 2| := abs_mul _ _
        rw [e1, e2]
        gcongr
        · exact hSl i hi
    _ ≤ (r' + 1) * ε₁ + ε / 2 := by
        gcongr
    _ = ε := by rw [hε₁]; field_simp; ring

/-- Sufficiency: `√N e^{-2λ a_N} → 0` gives uniform smallness of `√N D(a_N)`. -/
theorem asm_seq_small {l : ℝ} (S : Set ι) (D : ℝ → ι → ℝ) (C : ℝ)
    (hP2 : ∀ a : ℝ, 0 ≤ a → ∀ i ∈ S, |D a i| ≤ C * Real.exp (-2 * l * a))
    (a : ℕ → ℝ) (hatop : Tendsto a atTop atTop)
    (hr : Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-2 * l * a N)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ i ∈ S, |Real.sqrt N * D (a N) i| ≤ ε := by
  have hev1 : ∀ᶠ N : ℕ in atTop, 0 ≤ a N := hatop.eventually_ge_atTop _
  have hev2 : ∀ᶠ N : ℕ in atTop, |C| * (Real.sqrt N * Real.exp (-2 * l * a N)) ≤ ε := by
    have := (hr.const_mul |C|)
    simp only [mul_zero] at this
    exact this.eventually_le_const hε
  obtain ⟨N₀, hN₀⟩ := (hev1.and hev2).exists_forall_of_atTop
  refine ⟨N₀, fun N hN _ i hi => ?_⟩
  obtain ⟨h1, h2⟩ := hN₀ N hN
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt N * |D (a N) i| ≤ Real.sqrt N * (C * Real.exp (-2 * l * a N)) :=
        mul_le_mul_of_nonneg_left (hP2 _ h1 i hi) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt N * (|C| * Real.exp (-2 * l * a N)) := by
        gcongr; exact le_abs_self C
    _ = |C| * (Real.sqrt N * Real.exp (-2 * l * a N)) := by ring
    _ ≤ ε := h2

/-- Necessity: a lower bound at a single test function forces `√N e^{-2λ a_N} → 0`. -/
theorem asm_seq_necessary {l : ℝ} (D : ℝ → ℝ) (c a₀ : ℝ) (hc : 0 < c)
    (hlow : ∀ a : ℝ, a₀ ≤ a → c * Real.exp (-2 * l * a) ≤ |D a|)
    (a : ℕ → ℝ) (hatop : Tendsto a atTop atTop)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → |Real.sqrt N * D (a N)| ≤ ε) :
    Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-2 * l * a N)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hsmall (c * ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hatop.eventually_ge_atTop a₀)
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have h1 := hN₁ N hN1 hN3
  have h2 := hlow (a N) (hN₂ N hN2)
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at h1
  have h3 : Real.sqrt N * (c * Real.exp (-2 * l * a N)) ≤ c * ε / 2 :=
    le_trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)) h1
  have h4 : 0 ≤ Real.sqrt N * Real.exp (-2 * l * a N) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h4]
  have : c * (Real.sqrt N * Real.exp (-2 * l * a N)) ≤ c * (ε / 2) := by
    calc _ = Real.sqrt N * (c * Real.exp (-2 * l * a N)) := by ring
      _ ≤ _ := by rw [← mul_div_assoc]; exact h3
  have := le_of_mul_le_mul_left this hc
  linarith

end Seq

/-! ### `slowTensor` as a continuous linear functional -/

section Slow

variable {d : ℕ}

theorem asm_slow_clm (s β β₀ m T : ℝ)
    (hfin : {k : PosHalf d | lamMode d s β k.1 = lamStar d s β}.Finite) :
    ∃ S : (PathSpace d m T [×2]→L[ℝ] ℝ) →L[ℝ] ℝ, ∀ M, S M = slowTensor d s β β₀ m T M := by
  have : Finite {k : PosHalf d // lamMode d s β k.1 = lamStar d s β} := hfin.to_subtype
  have : Fintype {k : PosHalf d // lamMode d s β k.1 = lamStar d s β} := Fintype.ofFinite _
  let ev : PathSpace d m T → (PathSpace d m T [×2]→L[ℝ] ℝ) →L[ℝ] ℝ := fun x =>
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => PathSpace d m T) ℝ ![x, x]
  refine ⟨∑ k : {k : PosHalf d // lamMode d s β k.1 = lamStar d s β},
    deltaVar d s β β₀ k.1.1 •
      (ev (modePath m T (lamMode d s β k.1.1) (modeFn k.1.1 true)) +
        ev (modePath m T (lamMode d s β k.1.1) (modeFn k.1.1 false))), fun M => ?_⟩
  rw [slowTensor, tsum_fintype]
  simp [ev]
  exact Finset.sum_congr rfl fun k _ => by ring

end Slow

end HRS.MC.Q714.Asm

end
