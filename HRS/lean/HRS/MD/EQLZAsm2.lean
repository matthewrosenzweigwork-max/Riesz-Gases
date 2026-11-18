import HRS.MD.EQLZAsm1

/-!
# EQ-LZ packet ASM, part 2: `asm_finite`, the passage `G_k → F` on a finite set of times
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace HRS.MD.EQLZ.Asm

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The centred discrepancy has `L²` norm at most that of the discrepancy. -/
theorem asm_centered_le (μ : Measure α) [IsProbabilityMeasure μ] (h : α → ℝ) (hh : MemLp h 2 μ) :
    ∫ x, (h x - ∫ x', h x' ∂μ) ^ 2 ∂μ ≤ ∫ x, (h x) ^ 2 ∂μ := by
  have h1 := variance_le_expectation_sq (μ := μ) hh.aestronglyMeasurable
  rw [variance_eq_integral hh.aemeasurable] at h1
  simpa [Pi.pow_apply] using h1

theorem asm_finite (P : Measure Ω) (μ : Measure α) [IsProbabilityMeasure μ] (Y : ℝ → Ω → α)
    (S : Finset ℝ) (hY : ∀ t ∈ S, Measurable (Y t)) (hlaw : ∀ t ∈ S, P.map (Y t) = μ) (C W E : ℝ)
    (F : α → ℝ) (hFm : Measurable F) (hF2 : MemLp F 2 μ)
    (G : ℕ → α → ℝ) (hGm : ∀ k, Measurable (G k)) (hGb : ∀ k, ∃ B : ℝ, ∀ x, |G k x| ≤ B)
    (e : ℕ → ℝ)
    (hGF : Tendsto (fun k => ∫ x, (G k x - F x) ^ 2 ∂μ) atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 E))
    (hG : ∀ k, ∫⁻ ω, ⨆ t ∈ (S : Set ℝ), ENNReal.ofReal ((G k (Y t ω) - ∫ x, G k x ∂μ) ^ 2) ∂P ≤
      ENNReal.ofReal C * (ENNReal.ofReal (∫ x, (G k x - ∫ x', G k x' ∂μ) ^ 2 ∂μ) +
        ENNReal.ofReal W * ENNReal.ofReal (e k))) :
    ∫⁻ ω, ⨆ t ∈ (S : Set ℝ), ENNReal.ofReal ((F (Y t ω) - ∫ x, F x ∂μ) ^ 2) ∂P ≤
      ENNReal.ofReal C * (ENNReal.ofReal (∫ x, (F x - ∫ x', F x' ∂μ) ^ 2 ∂μ) +
        ENNReal.ofReal W * ENNReal.ofReal E) := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∫ x, F x ∂μ := ⟨_, rfl⟩
  obtain ⟨mk, hmk⟩ : ∃ mk : ℕ → ℝ, ∀ k, mk k = ∫ x, G k x ∂μ := ⟨_, fun _ => rfl⟩
  simp only [← hmk] at hG
  rw [← hm]
  obtain ⟨V0, hV0⟩ : ∃ V0 : ℝ, V0 = ∫ x, (F x - m) ^ 2 ∂μ := ⟨_, rfl⟩
  rw [← hV0]
  have hF1 : Integrable F μ := hF2.integrable one_le_two
  have hG2 : ∀ k, MemLp (G k) 2 μ := fun k => by
    obtain ⟨B, hB⟩ := hGb k
    exact MemLp.of_bound (hGm k).aestronglyMeasurable B
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hG1 : ∀ k, Integrable (G k) μ := fun k => (hG2 k).integrable one_le_two
  -- the discrepancy
  obtain ⟨c, hc⟩ : ∃ c : ℕ → α → ℝ, ∀ k x, c k x = (F x - m) - (G k x - mk k) := ⟨_, fun _ _ => rfl⟩
  have hc2 : ∀ k, MemLp (c k) 2 μ := fun k => by
    have : c k = fun x => (F x - m) - (G k x - mk k) := funext (hc k)
    rw [this]
    exact (hF2.sub (memLp_const m)).sub ((hG2 k).sub (memLp_const _))
  have hcm : ∀ k, Measurable (c k) := fun k => by
    have : c k = fun x => (F x - m) - (G k x - mk k) := funext (hc k)
    rw [this]
    exact (hFm.sub_const m).sub ((hGm k).sub_const _)
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ, ∀ k, I k = ∫ x, (c k x) ^ 2 ∂μ := ⟨_, fun _ => rfl⟩
  have hI0 : ∀ k, 0 ≤ I k := fun k => by rw [hI]; exact integral_nonneg fun x => sq_nonneg _
  have hIle : ∀ k, I k ≤ ∫ x, (G k x - F x) ^ 2 ∂μ := by
    intro k
    have hh : MemLp (fun x => G k x - F x) 2 μ := (hG2 k).sub hF2
    have h1 := asm_centered_le μ _ hh
    have h3 : ∫ x, (G k x - F x) ∂μ = mk k - m := by
      rw [integral_sub (hG1 k) hF1, hmk, hm]
    rw [h3] at h1
    rw [hI]
    refine le_trans (le_of_eq ?_) h1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hc]; ring
  have hIt : Tendsto I atTop (𝓝 0) := squeeze_zero hI0 hIle hGF
  have hIt' : Tendsto (fun k => ENNReal.ofReal (I k)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hIt
  have het : Tendsto (fun k => ENNReal.ofReal (e k)) atTop (𝓝 (ENNReal.ofReal E)) :=
    ENNReal.tendsto_ofReal he
  have hV0nn : 0 ≤ V0 := by rw [hV0]; exact integral_nonneg fun x => sq_nonneg _
  -- fixed ε
  have key : ∀ ε : ℝ, 0 < ε → ∀ k,
      ∫⁻ ω, ⨆ t ∈ (S : Set ℝ), ENNReal.ofReal ((F (Y t ω) - m) ^ 2) ∂P ≤
        ENNReal.ofReal (1 + ε) * (ENNReal.ofReal C * (ENNReal.ofReal (1 + ε) * ENNReal.ofReal V0 +
            ENNReal.ofReal (1 + 1 / ε) * ENNReal.ofReal (I k) +
            ENNReal.ofReal W * ENNReal.ofReal (e k))) +
          ENNReal.ofReal (1 + 1 / ε) * ((S.card : ℝ≥0∞) * ENNReal.ofReal (I k)) := by
    intro ε hε k
    have hstep := asm_step P μ Y S hY hlaw (fun x => F x - m) (fun x => G k x - mk k) (c k)
      ((hGm k).sub_const _) (hcm k) (fun x => by simp only [hc]; ring) hε
    have hlint : ∫⁻ x, ENNReal.ofReal (c k x ^ 2) ∂μ = ENNReal.ofReal (I k) := by
      rw [hI, ofReal_integral_eq_lintegral_ofReal (hc2 k).integrable_sq (ae_of_all _ fun x => sq_nonneg _)]
    rw [hlint] at hstep
    -- variance bound
    have hVk : ∫ x, (G k x - mk k) ^ 2 ∂μ ≤ (1 + ε) * V0 + (1 + 1 / ε) * I k := by
      rw [hV0, hI, ← integral_const_mul, ← integral_const_mul, ← integral_add]
      · refine integral_mono (((hG2 k).sub (memLp_const _)).integrable_sq) ?_ (fun x => ?_)
        · exact (((hF2.sub (memLp_const m)).integrable_sq).const_mul _).add
            (((hc2 k).integrable_sq).const_mul _)
        · have h := asm_sq_le hε (F x - m) (-(c k x))
          have e1 : F x - m + -(c k x) = G k x - mk k := by simp only [hc]; ring
          rw [e1, neg_sq] at h
          exact h
      · exact ((hF2.sub (memLp_const m)).integrable_sq).const_mul _
      · exact ((hc2 k).integrable_sq).const_mul _
    have hV' : ENNReal.ofReal (∫ x, (G k x - mk k) ^ 2 ∂μ) ≤
        ENNReal.ofReal (1 + ε) * ENNReal.ofReal V0 + ENNReal.ofReal (1 + 1 / ε) * ENNReal.ofReal (I k) := by
      refine (ENNReal.ofReal_le_ofReal hVk).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_add (by positivity) (by have := hI0 k; positivity),
        ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_mul (by positivity)]
    refine hstep.trans (add_le_add ?_ le_rfl)
    refine mul_le_mul_right ((hG k).trans (mul_le_mul_right ?_ _)) _
    exact add_le_add hV' le_rfl
  -- limit in k
  have hlim : ∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, ⨆ t ∈ (S : Set ℝ), ENNReal.ofReal ((F (Y t ω) - m) ^ 2) ∂P ≤
        ENNReal.ofReal (1 + ε) * (ENNReal.ofReal C * (ENNReal.ofReal (1 + ε) * ENNReal.ofReal V0 +
            ENNReal.ofReal (1 + 1 / ε) * 0 + ENNReal.ofReal W * ENNReal.ofReal E)) +
          ENNReal.ofReal (1 + 1 / ε) * ((S.card : ℝ≥0∞) * 0) := by
    intro ε hε
    refine ge_of_tendsto' (x := atTop) (f := fun k => ENNReal.ofReal (1 + ε) * (ENNReal.ofReal C *
        (ENNReal.ofReal (1 + ε) * ENNReal.ofReal V0 + ENNReal.ofReal (1 + 1 / ε) * ENNReal.ofReal (I k) +
          ENNReal.ofReal W * ENNReal.ofReal (e k))) +
        ENNReal.ofReal (1 + 1 / ε) * ((S.card : ℝ≥0∞) * ENNReal.ofReal (I k))) ?_ (key ε hε)
    refine Tendsto.add (ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top))
      (Or.inr ENNReal.ofReal_ne_top)) (ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul hIt'
        (Or.inr (ENNReal.natCast_ne_top _))) (Or.inr ENNReal.ofReal_ne_top))
    exact Tendsto.add (Tendsto.add tendsto_const_nhds
      (ENNReal.Tendsto.const_mul hIt' (Or.inr ENNReal.ofReal_ne_top)))
      (ENNReal.Tendsto.const_mul het (Or.inr ENNReal.ofReal_ne_top))
  -- simplify and let ε → 0
  have hone : ∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, ⨆ t ∈ (S : Set ℝ), ENNReal.ofReal ((F (Y t ω) - m) ^ 2) ∂P ≤
        ENNReal.ofReal ((1 + ε) * (1 + ε)) *
          (ENNReal.ofReal C * (ENNReal.ofReal V0 + ENNReal.ofReal W * ENNReal.ofReal E)) := by
    intro ε hε
    refine (hlim ε hε).trans ?_
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + ε) := ENNReal.one_le_ofReal.mpr (by linarith)
    rw [ENNReal.ofReal_mul (by linarith)]
    simp only [mul_zero, add_zero]
    calc ENNReal.ofReal (1 + ε) * (ENNReal.ofReal C * (ENNReal.ofReal (1 + ε) * ENNReal.ofReal V0 +
            ENNReal.ofReal W * ENNReal.ofReal E))
        ≤ ENNReal.ofReal (1 + ε) * (ENNReal.ofReal C * (ENNReal.ofReal (1 + ε) *
            (ENNReal.ofReal V0 + ENNReal.ofReal W * ENNReal.ofReal E))) := by
          gcongr
          rw [mul_add]
          exact add_le_add le_rfl (le_mul_of_one_le_left bot_le h1)
      _ = _ := by ring
  have hseq : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) * (1 + 1 / ((n : ℝ) + 1))))
      atTop (𝓝 1) := by
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1)) * (1 + 1 / ((n : ℝ) + 1))) atTop
        (𝓝 ((1 + 0) * (1 + 0))) := (tendsto_const_nhds.add h0).mul (tendsto_const_nhds.add h0)
    simpa using ENNReal.tendsto_ofReal h2
  have hR : ENNReal.ofReal C * (ENNReal.ofReal V0 + ENNReal.ofReal W * ENNReal.ofReal E) ≠ ⊤ := by
    simp [ENNReal.mul_eq_top]
  have := ge_of_tendsto' (ENNReal.Tendsto.mul_const hseq (Or.inr hR))
    (fun n => hone (1 / ((n : ℝ) + 1)) (by positivity))
  simpa using this

end HRS.MD.EQLZ.Asm

end
