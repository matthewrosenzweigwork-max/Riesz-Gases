import HRS.Sections.Sec7Setting
import HRS.MC.RegSet
import HRS.MC.L2C0

/-!
# Packet E213F: `Regime.shift` and the uniform `AdjointData` bundle for Theorem 2.13

* `E213F.shift R b hb`: the regime restarted at time `b ≥ 0` (`ρ_b(t) = ρ(b+t)`, initial density `ρ(b)`).
  `Regime` has exactly the fields `D β β₀ ρ₀ ρ hd hM hs hβ hDβ hβ₀ hV hρ₀ init sol`
  (`reg`, `relax` are theorems, not fields, and are not used).
* `E213F.adjointData_uniform`: one `AdjointData` bundle for all horizons and all shifts `ρ_b`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS HRS.PDE HRS.Sec7

namespace HRS.MC.E213F

variable {d : ℕ}

/-- `ρ(b)` is a smooth positive probability density. -/
theorem shift_smoothPos (R : Regime d) (b : ℝ) (hb : 0 ≤ b) : SmoothPosDensity (R.ρ b) := by
  refine ⟨(HRS.MC.L2C0.l2c0_rho_prob_cont R).1 b hb, ?_, ?_⟩
  · unfold Torus.IsSmooth Torus.IsCk
    rw [contDiff_infty]
    intro n
    obtain ⟨Λ, hΛ⟩ := HRS.MC.RegSet.reg_proof R n
    exact (hΛ b b ⟨hb, le_rfl⟩).1
  · obtain ⟨m₀, M₀, hm₀, h⟩ := R.bounds
    exact fun x => lt_of_lt_of_le hm₀ (h b hb x).1

/-- The coefficient solution restarted at `b`. -/
theorem shift_sol (R : Regime d) (b : ℝ) (hb : 0 ≤ b) (K : ℕ) (hK : (d : ℝ) / 2 + 6 < K) :
    ∃ ρc : ℝ → Coeff d, IsMFSolutionHK d R.D.s R.D.V R.D.invβ (K : ℝ) (R.ρ b) ρc ∧
      ∀ t : ℝ, 0 ≤ t → R.ρ (b + t) = mfPath ρc t := by
  obtain ⟨ρc, hρc, hρ⟩ := R.sol K hK
  have hd : 1 ≤ d := by have := R.hd; omega
  have hH := R.finiteRegHyp K hK
  have hρc' : IsMFSolutionHK d R.D.s R.D.V R.β⁻¹ (K : ℝ) R.ρ₀ ρc := by
    rw [R.hDβ] at hρc; exact hρc
  have hreal := MFGlobal.isRealCoeff_of_isMFSolutionHK hd R.D.s R.β R.β K R.D.V R.ρ₀ hH R.β
    ⟨le_rfl, le_rfl⟩ ρc hρc'
  have hK0 : (d : ℝ) / 2 < K := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hsum : Summable fun k => ‖ρc b k‖ := summable_norm_of_memHs (K : ℝ) hK0 _ (hρc.cont.1 b hb)
  have hco : coeffOf (R.ρ b) = ρc b := by
    rw [hρ b hb]; exact coeffOf_toFun _ (hreal b hb) hsum
  have hmem : ∀ τ : ℝ, 0 ≤ τ → 0 ≤ b + τ := fun τ hτ => add_nonneg hb hτ
  refine ⟨fun τ => ρc (b + τ), ⟨?_, ?_, ?_, ?_⟩, fun t ht => ?_⟩
  · simp [hco]
  · refine ⟨fun τ hτ => hρc.cont.1 _ (hmem τ hτ), fun τ0 hτ0 => ?_⟩
    have h := hρc.cont.2 (b + τ0) (hmem τ0 hτ0)
    have ht : Tendsto (fun τ : ℝ => b + τ) (𝓝[Set.Ici 0] τ0) (𝓝[Set.Ici 0] (b + τ0)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨((continuous_const.add continuous_id).tendsto τ0).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun τ hτ => hmem τ hτ⟩
    exact h.comp ht
  · intro k t ht
    have h1 := hρc.integrable k (b + t) (hmem t ht)
    have h2 : IntervalIntegrable (fun σ => mfRhsCoeff d R.D.s R.D.V R.D.invβ (ρc σ) k) volume
        (b + 0) (b + t) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
      exact h1.mono_set (Set.Icc_subset_Icc (by simpa using hb) le_rfl)
    have h3 := h2.comp_add_left b
    simp only [add_zero, add_sub_cancel_left, sub_self] at h3
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le ht).1 h3
  · intro k t ht
    have hint : ∀ a c : ℝ, 0 ≤ a → 0 ≤ c →
        IntervalIntegrable (fun σ => mfRhsCoeff d R.D.s R.D.V R.D.invβ (ρc σ) k) volume a c := by
      intro a c ha hc
      have h0 := fun u (hu : 0 ≤ u) =>
        (intervalIntegrable_iff_integrableOn_Icc_of_le hu).2 (hρc.integrable k u hu)
      exact (h0 a ha).symm.trans (h0 c hc)
    have e1 := hρc.eq k (b + t) (hmem t ht)
    have e2 := hρc.eq k b hb
    have e3 := intervalIntegral.integral_add_adjacent_intervals (hint 0 b le_rfl hb)
      (hint b (b + t) hb (hmem t ht))
    have e4 : ∫ σ in (0 : ℝ)..t, mfRhsCoeff d R.D.s R.D.V R.D.invβ (ρc (b + σ)) k =
        ∫ σ in b..(b + t), mfRhsCoeff d R.D.s R.D.V R.D.invβ (ρc σ) k := by
      rw [intervalIntegral.integral_comp_add_left
        (fun σ => mfRhsCoeff d R.D.s R.D.V R.D.invβ (ρc σ) k) b]
      simp
    show ρc (b + t) k = coeffOf (R.ρ b) k + _
    rw [e4, hco]
    linear_combination e1 - e2 - e3
  · rw [hρ (b + t) (hmem t ht)]; rfl

/-- The regime restarted at time `b ≥ 0`. -/
def shift (R : Regime d) (b : ℝ) (hb : 0 ≤ b) : Regime d where
  D := R.D
  β := R.β
  β₀ := R.β₀
  ρ₀ := R.ρ b
  ρ := fun t => R.ρ (b + t)
  hd := R.hd
  hM := R.hM
  hs := R.hs
  hβ := R.hβ
  hDβ := R.hDβ
  hβ₀ := R.hβ₀
  hV := R.hV
  hρ₀ := shift_smoothPos R b hb
  init := by simp
  sol := fun K hK => shift_sol R b hb K hK

/-! ### Characterising lemmas of `shift` -/

section shift_lemmas

variable (R : Regime d) (b : ℝ) (hb : 0 ≤ b)

@[simp] theorem shift_D : (shift R b hb).D = R.D := rfl
@[simp] theorem shift_ρ (t : ℝ) : (shift R b hb).ρ t = R.ρ (b + t) := rfl
@[simp] theorem shift_β : (shift R b hb).β = R.β := rfl
@[simp] theorem shift_β₀ : (shift R b hb).β₀ = R.β₀ := rfl
@[simp] theorem shift_ρ₀ : (shift R b hb).ρ₀ = R.ρ b := rfl

theorem shift_zero (h0 : (0 : ℝ) ≤ 0) (t : ℝ) : (shift R 0 h0).ρ t = R.ρ t := by simp

theorem shift_shift (b' : ℝ) (hb' : 0 ≤ b') (t : ℝ) :
    (shift (shift R b hb) b' hb').ρ t = R.ρ (b + (b' + t)) := rfl

end shift_lemmas

/-! ### The uniform `AdjointData` bundle -/

/-- `CoeffHyp` transfers to a time shift: if it holds for `μ` on `[0, b+G]` then it holds for
`μ(b+·)` on `[0, G]`. -/
theorem coeffHyp_shift {m : ℕ} {Λ : ℝ} {μ : ℝ → Torus d → ℝ} {b G : ℝ} (hb : 0 ≤ b)
    (h : CoeffHyp m Λ (b + G) μ) : CoeffHyp m Λ G (fun t => μ (b + t)) := by
  have hmap : ∀ r ∈ Set.Icc (0 : ℝ) G, b + r ∈ Set.Icc (0 : ℝ) (b + G) := fun r hr =>
    ⟨add_nonneg hb hr.1, by linarith [hr.2]⟩
  refine ⟨fun r hr => h.prob _ (hmap r hr), fun r hr => h.smooth _ (hmap r hr),
    fun r hr => h.bound _ (hmap r hr), fun ψ hψ => ?_⟩
  exact (h.cont ψ hψ).comp ((continuous_const.add continuous_id).continuousOn) hmap

/-- Uniform `AdjointData` bundle: for every level `m ≥ 1` there are constants `Rg MB Λ VB ν₀`, chosen
before the horizon `G` and the shift `b`, such that `AdjointData` holds for all `G > 0` and all `b ≥ 0`
for the shifted density path `t ↦ ρ(b+t)`. -/
theorem adjointData_uniform (R : Regime d) (m : ℕ) :
    ∃ (Rg : PDE.Regime) (MB Λ VB ν₀ : ℝ), ∀ G : ℝ, 0 < G → ∀ b : ℝ, 0 ≤ b →
      AdjointData R.D.s m Rg MB Λ VB R.D ν₀ G (fun t => R.ρ (b + t)) := by
  obtain ⟨Rg, hRg⟩ : ∃ Rg : PDE.Regime, ∀ (M : Matrix (Fin d) (Fin d) ℝ) (invβ ν₀ T : ℝ)
      (μ : ℝ → Torus d → ℝ), 0 < ν₀ → ν₀ ≤ invβ → Rg.Holds d R.D.s M invβ ν₀ T μ := by
    rcases le_or_gt R.D.s ((d : ℝ) - 2) with h | h
    · exact ⟨.R1, fun _ _ _ _ _ _ _ => h⟩
    · exact ⟨.R3, fun _ _ _ _ _ h1 h2 => ⟨h, h1, h2⟩⟩
  have hν : 0 < R.D.invβ := by rw [R.hDβ]; exact inv_pos.mpr R.hβ
  obtain ⟨Λ, hΛ⟩ := HRS.MC.RegSet.reg_proof R (m + 3)
  obtain ⟨hprob, hcont⟩ := HRS.MC.L2C0.l2c0_rho_prob_cont R
  have hVm : Torus.IsCk (m + 3) R.D.V :=
    PDE.ClassicalAux.isCk_of_le (WithTop.coe_le_coe.2 le_top) R.hV
  refine ⟨Rg, 1, Λ, Torus.cbNorm (m + 3) R.D.V, R.D.invβ, fun G hG b hb => ?_⟩
  refine ⟨rfl, ?_, ⟨hVm, le_rfl⟩, ?_, hG, hRg _ _ _ _ _ hν le_rfl⟩
  · intro i k
    rw [R.hM, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> norm_num
  · refine coeffHyp_shift hb ⟨fun r hr => hprob r hr.1, fun r hr => ?_, fun r hr => ?_, hcont (b + G)⟩
    · exact (hΛ (b + G) r hr).1
    · exact (hΛ (b + G) r hr).2

end HRS.MC.E213F
