import HRS.MD.LT337Vocab
import HRS.MD.LT337P1
import HRS.MD.LT337P3
import HRS.Energy.G336C1Aux3
import HRS.Energy.KIDFinal

/-!
# Packet LT5 (chunk D), file A: the localised Coulomb energy identity of Prop 3.37

`lt5_stopped_identity_proof` (file `LT337P5C`) is the statement `HRS.MD.LT337.lt5_stopped_identity`
(M L3131-3137, the stopped `B:eq:coulomb-energy-identity`).

## Plan (sub-lemmas and status; all DONE)

File A (this file, `LT337P5A`):
* `lt5_kid_pathwise_all` [done]: copy-adapted `kid_pathwise` (KIDAux7): a.s. for ALL `τ' ∈ [0,t]` simultaneously,
  `E_h(X_τ', ρ_τ') - E_h(X_0, ρ_0) = ∫_{[0,τ']} Jfull + I_1(τ') - I_2(τ')` (smooth even kernel `h`).
* stopping-time bookkeeping [done]: `lt5_stoppedProcess_eq`, `lt5_measurable_stopTime` (`σ = t ∧ τ`),
  `lt5_measurableSet_lt` (`{(r,ω) : r < τ ω}`).
File B (`LT337P5B`):
* `lt5_measurable_energy_clamp` [done]: `(r, X) ↦ E_h(X, ρ_{r ∧ T})` is jointly measurable.
* `lt5_energy_bound_sep` [done]: `|E_{g_n}(X, ρ)| ≤ B` uniformly in `n` for `a`-separated `X`.
* `lt5_jfull_bound` [done]: `|Jfull_{g_n}| ≤ B` for `n ≥ n₀`, `a`-separated `X` (`g336c1_comm_bound`, `g336c1_micro_bound`,
  `lt3_diffusion_bound_proof`, `main_alg`); `lt5_jfull_tendsto` [done]: `Jfull_{g_n} → ltDrift` for collision-free `X`.
File C (`LT337P5C`):
* `lt5_integral_stop`, `lt5_G_bound` [done]; `lt5_fixed_kernel` [done]: fixed smooth even kernel `h`, stopping time `τ ≥ 0` with
  `|Jfull_h| ≤ B` on `{r < τ}`: `E[E_h(X_σ,ρ_σ)] - E[E_h(X_0,ρ_0)] = ∫_0^t E[1_{r<τ} Jfull_h(r)] dr`, with integrability
  (optional stopping `integral_stoppedProcess_itoIntegral`, Fubini `integral_integral_swap`).
File D (`LT337P5D`):
* `lt5_pos_time` [done]: `t ∈ (0,T]`, `n → ∞` by dominated convergence on `{r < τ_ε}` (separation `≥ ε`) for energies and drifts.
* `lt5_stopped_identity_proof` [done]: the case `t = 0` and assembly into `StoppedIdentity`.
Tie: `LT337P5Tie`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.Uniform.Q54c HRS.KID HRS.MD.LT337Vocab

namespace HRS.MD.LT337P5

variable {d N : ℕ}

/-! ### Pathwise identity at all times simultaneously -/

section Pathwise

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
  {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
  {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem lt5_kid_pathwise_all (c : MFctx D T Λ ρ) (hN : 2 ≤ N) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T)
    (hsol : IsStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x) :
    IsProgressiveL2 P ℱ (fun s ω k => fkeRef D t (Φpp h) X s ω k) ∧
    IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t (fK h ρ) X) ∧
    ∀ᵐ ω ∂P, ∀ τ' ∈ Set.Icc (0 : ℝ) t,
      modulatedEnergyKernel h (X (Real.toNNReal τ') ω) (withDensityReal (ρ τ')) -
        modulatedEnergyKernel h (X 0 ω) (withDensityReal (ρ 0)) =
      (∫ r in Set.Icc (0 : ℝ) τ', Jfull D h ρ X r ω) +
        itoIntegral P ℱ W' (fun s ω k => fkeRef D t (Φpp h) X s ω k) τ' ω -
        itoIntegral P ℱ W' (empiricalNoiseIntegrand D t (fK h ρ) X) τ' ω := by
  have hN0 : 0 < N := by omega
  obtain ⟨hΨpp, hpp⟩ := kid_pp_ito c.hV ht0.le htT hsol.toContact hF hsm hev
  obtain ⟨hΨf, hf⟩ := kid_f_ito c hN ht0 htT hsol hF hsm hev
  refine ⟨hΨpp, hΨf, ?_⟩
  filter_upwards [hpp, hf] with ω hωpp hωf
  intro τ' hτ'
  have hu : ((Real.toNNReal τ' : ℝ≥0) : ℝ) = τ' := Real.coe_toNNReal τ' hτ'.1
  have h1 := hωpp.2 (Real.toNNReal τ') (by rw [hu]; exact hτ'.2)
  rw [hu] at h1
  obtain ⟨hint_f, h2⟩ := hωf τ' hτ'
  have hτT : τ' ∈ Set.Icc (0 : ℝ) T := ⟨hτ'.1, hτ'.2.trans htT⟩
  have hsub : Set.Icc (0 : ℝ) τ' ⊆ Set.Icc 0 t := Set.Icc_subset_Icc le_rfl hτ'.2
  have hWc : IntegrableOn (fun r : ℝ => wkG D ρ (fK h ρ r) r) (Set.Icc 0 τ') :=
    ((c.continuousOn_Wdiag hsm hev).mono (Set.Icc_subset_Icc le_rfl hτT.2)).integrableOn_Icc
  have hDg := c.Dg_eq hsm hev hτT
  have hDg' : Dg h ρ τ' - Dg h ρ 0 = 2 * ∫ τ in Set.Icc (0 : ℝ) τ', wkG D ρ (fK h ρ τ) τ := by
    rw [hDg, intervalIntegral.integral_of_le hτ'.1, ← integral_Icc_eq_integral_Ioc,
      ← integral_const_mul]
  have h2' : (∫ r in (0 : ℝ)..τ', fDrift D h ρ r (X (Real.toNNReal r) ω)) =
      ∫ r in Set.Icc (0 : ℝ) τ', fDrift D h ρ r (X (Real.toNNReal r) ω) := by
    rw [intervalIntegral.integral_of_le hτ'.1, ← integral_Icc_eq_integral_Ioc]
  rw [h2'] at h2
  unfold Jfull
  have hpp' : IntegrableOn (fun s : ℝ => ppDrift D h (X (Real.toNNReal s) ω)) (Set.Icc 0 τ') :=
    hωpp.1.mono_set hsub
  have hi : IntegrableOn (fun r : ℝ => ppDrift D h (X (Real.toNNReal r) ω) -
      fDrift D h ρ r (X (Real.toNNReal r) ω)) (Set.Icc 0 τ') := hpp'.sub hint_f
  rw [integral_add hi hWc, integral_sub hpp' hint_f]
  rw [energy_eq hev hN0, energy_eq hev hN0]
  simp only [empiricalMartingale] at h2
  rw [hu] at h2
  linarith

end Pathwise

/-! ### Bookkeeping for `σ = t ∧ τ` -/

section Stop

theorem lt5_stopTime_le (t : ℝ) (τ : WithTop ℝ) : stopTime t τ ≤ t := min_le_left _ _

theorem lt5_stopTime_nonneg {t : ℝ} (ht : 0 ≤ t) {τ : WithTop ℝ} (hτ : 0 ≤ τ) : 0 ≤ stopTime t τ := by
  unfold stopTime
  refine le_min ht ?_
  induction τ using WithTop.recTopCoe with
  | top => simpa using ht
  | coe c => simpa using hτ

theorem lt5_coe_stopTime_le (t : ℝ) (τ : WithTop ℝ) : ((stopTime t τ : ℝ) : WithTop ℝ) ≤ τ := by
  induction τ using WithTop.recTopCoe with
  | top => exact le_top
  | coe c => simpa [stopTime] using (min_le_right t c)

theorem lt5_stopTime_zero {t : ℝ} (ht : 0 ≤ t) : stopTime t 0 = 0 := by
  show min t (WithTop.untopD t ((0 : ℝ) : WithTop ℝ)) = 0
  rw [WithTop.untopD_coe]
  exact min_eq_right ht

theorem lt5_le_stopTime {r t : ℝ} {τ : WithTop ℝ} (hrt : r ≤ t) (hr : (r : WithTop ℝ) < τ) :
    r ≤ stopTime t τ := by
  unfold stopTime
  refine le_min hrt ?_
  induction τ using WithTop.recTopCoe with
  | top => simpa using hrt
  | coe c => simpa using (WithTop.coe_lt_coe.1 hr).le

theorem lt5_lt_of_lt_stopTime {r t : ℝ} {τ : WithTop ℝ} (hr : r < stopTime t τ) :
    (r : WithTop ℝ) < τ :=
  lt_of_lt_of_le (WithTop.coe_lt_coe.2 hr) (lt5_coe_stopTime_le t τ)

theorem lt5_stoppedProcess_eq {Ω : Type*} (M : ℝ → Ω → ℝ) (τ : Ω → WithTop ℝ) (t : ℝ) (ω : Ω) :
    stoppedProcess M τ t ω = M (stopTime t (τ ω)) ω := by
  cases h : τ ω with
  | top => rw [stoppedProcess_apply_top h]; simp [stopTime, h]
  | coe c => rw [stoppedProcess_apply_coe h]; simp [stopTime, h]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ mΩ}

theorem lt5_measurableSet_le {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ) (a : ℝ) :
    MeasurableSet {ω | τ ω ≤ (a : WithTop ℝ)} :=
  ℱ.le a _ (hτ.measurableSet_le a)

theorem lt5_measurable_stopTime {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ) (t : ℝ) :
    Measurable fun ω => stopTime t (τ ω) := by
  refine measurable_of_Iic fun a => ?_
  by_cases hta : t ≤ a
  · have : (fun ω => stopTime t (τ ω)) ⁻¹' Iic a = univ := by
      ext ω; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (lt5_stopTime_le t _).trans hta
    rw [this]; exact MeasurableSet.univ
  · have hat : a < t := not_le.1 hta
    have : (fun ω => stopTime t (τ ω)) ⁻¹' Iic a = {ω | τ ω ≤ (a : WithTop ℝ)} := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_setOf_eq]
      induction h : τ ω using WithTop.recTopCoe with
      | top => simp [stopTime, not_le.2 hat |> fun _ => hta]
      | coe c => simp [stopTime, min_le_iff, hta]
    rw [this]; exact lt5_measurableSet_le hτ a

theorem lt5_measurableSet_lt {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet {p : ℝ × Ω | ((p.1 : ℝ) : WithTop ℝ) < τ p.2} := by
  have : {p : ℝ × Ω | ((p.1 : ℝ) : WithTop ℝ) < τ p.2} =
      ⋃ q : ℚ, {p : ℝ × Ω | p.1 < (q : ℝ)} ∩ {p : ℝ × Ω | ((q : ℝ) : WithTop ℝ) < τ p.2} := by
    ext ⟨r, ω⟩
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro hr
      induction h : τ ω using WithTop.recTopCoe with
      | top =>
        obtain ⟨q, hq⟩ := exists_rat_gt r
        exact ⟨q, hq, by simp⟩
      | coe c =>
        rw [h] at hr
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (WithTop.coe_lt_coe.1 hr)
        exact ⟨q, hq1, WithTop.coe_lt_coe.2 hq2⟩
    · rintro ⟨q, hq1, hq2⟩
      exact (WithTop.coe_lt_coe.2 hq1).trans hq2
  rw [this]
  refine MeasurableSet.iUnion fun q => (measurableSet_lt measurable_fst measurable_const).inter ?_
  have : {p : ℝ × Ω | ((q : ℝ) : WithTop ℝ) < τ p.2} = Prod.snd ⁻¹' {ω | τ ω ≤ (((q : ℚ) : ℝ) : WithTop ℝ)}ᶜ := by
    ext p; simp [not_le]
  rw [this]
  exact measurable_snd (lt5_measurableSet_le hτ (q : ℝ)).compl

end Stop

end HRS.MD.LT337P5
