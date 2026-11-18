import HRS.PDE.MeanFieldLocalB
import HRS.PDE.MeanFieldAprioriMain
import HRS.PDE.MeanFieldAprioriClassicalOn

/-!
# Global existence, uniqueness and a priori bounds for the finite-regularity mean-field
equation, packet P6 (package MF-01; `MeanFieldAprioriAmendment.md` §4)

Continuation argument: the time-local a priori bound `MFApriori.mf_apriori_bound_real_on`
(constants independent of `T`) gives `sup ‖ρ̂(t)‖_{H^K} ≤ R` on every `[0, T]`, so the local
existence time `T₀(R)` of `MFLocal.local_exists_coeff` does not depend on the step; gluing
`n` steps gives real solutions on `[0, n T₀]`, which are coherent by `MFLocal.unique_on_Icc'`.

NOTE: `MFApriori.mf_apriori_bound_real_on` (AP7, `MeanFieldAprioriMain.lean`) is now proved; this file
has no `sorry` upstream.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace HRS.PDE.MFGlobal

open MFApriori

variable {d : ℕ}

theorem solOn_iff {s : ℝ} {V : Torus d → ℝ} {ν K : ℝ} {ρ₀ : Torus d → ℝ} {ρc : ℝ → Coeff d}
    {T : ℝ} : MFLocal.IsMFSolutionHKOn d s V ν K (coeffOf ρ₀) ρc T ↔ MFSolOn d s V ν K ρ₀ ρc T :=
  ⟨fun h => ⟨h.init, h.cont, h.integrable, h.eq⟩, fun h => ⟨h.init, h.cont, h.integrable, h.eq⟩⟩

/-! ### Helpers on `ContinuousInHsOn` -/

theorem contInHsOn_congr {m : ℝ} {F G : ℝ → Coeff d} {S : Set ℝ} (h : ContinuousInHsOn m F S)
    (hFG : ∀ τ ∈ S, F τ = G τ) : ContinuousInHsOn m G S := by
  refine ⟨fun τ hτ => (hFG τ hτ) ▸ h.1 τ hτ, fun τ0 hτ0 => ?_⟩
  refine (h.2 τ0 hτ0).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  rw [hFG τ hτ, hFG τ0 hτ0]

theorem contInHsOn_comp_add {m : ℝ} {F : ℝ → Coeff d} {S S' : Set ℝ} (a : ℝ)
    (h : ContinuousInHsOn m F S) (hmem : ∀ τ ∈ S', τ + a ∈ S) :
    ContinuousInHsOn m (fun τ => F (τ + a)) S' := by
  refine ⟨fun τ hτ => h.1 _ (hmem τ hτ), fun τ0 hτ0 => ?_⟩
  have ht : Tendsto (fun τ : ℝ => τ + a) (𝓝[S'] τ0) (𝓝[S] (τ0 + a)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨((continuous_id.add continuous_const).tendsto τ0).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall hmem⟩
  exact (h.2 (τ0 + a) (hmem τ0 hτ0)).comp ht

theorem contInHsOn_union {m : ℝ} {F : ℝ → Coeff d} {S₁ S₂ : Set ℝ} (h₁ : IsClosed S₁)
    (h₂ : IsClosed S₂) (hF₁ : ContinuousInHsOn m F S₁) (hF₂ : ContinuousInHsOn m F S₂) :
    ContinuousInHsOn m F (S₁ ∪ S₂) := by
  refine ⟨fun τ hτ => hτ.elim (hF₁.1 τ) (hF₂.1 τ), fun τ0 hτ0 => ?_⟩
  rw [nhdsWithin_union, tendsto_sup]
  have key : ∀ S : Set ℝ, IsClosed S → ContinuousInHsOn m F S →
      Tendsto (fun τ => hsNorm m (F τ - F τ0)) (𝓝[S] τ0) (𝓝 0) := by
    intro S hS hF
    by_cases hτ : τ0 ∈ S
    · exact hF.2 τ0 hτ
    · have : 𝓝[S] τ0 = ⊥ := by
        rw [← not_neBot, mem_closure_iff_nhdsWithin_neBot.symm, hS.closure_eq]
        exact hτ
      rw [this]
      exact tendsto_bot
  have hF : ∀ S : Set ℝ, IsClosed S → ContinuousInHsOn m F S → τ0 ∈ S₁ ∪ S₂ →
      Tendsto (fun τ => hsNorm m (F τ - F τ0)) (𝓝[S] τ0) (𝓝 0) := fun S hS hF _ => key S hS hF
  exact ⟨hF S₁ h₁ hF₁ hτ0, hF S₂ h₂ hF₂ hτ0⟩


theorem MFSolOn.congr {s : ℝ} {V : Torus d → ℝ} {ν K : ℝ} {ρ₀ : Torus d → ℝ}
    {ρc ρc' : ℝ → Coeff d} {T : ℝ} (hT : 0 ≤ T) (H : MFSolOn d s V ν K ρ₀ ρc T)
    (h : ∀ t ∈ Set.Icc 0 T, ρc t = ρc' t) : MFSolOn d s V ν K ρ₀ ρc' T := by
  have hrhs : ∀ t ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 t, ∀ k,
      mfRhsCoeff d s V ν (ρc σ) k = mfRhsCoeff d s V ν (ρc' σ) k := fun t ht σ hσ k => by
    rw [h σ ⟨hσ.1, hσ.2.trans ht.2⟩]
  refine ⟨?_, contInHsOn_congr H.cont h, fun k t ht => ?_, fun k t ht => ?_⟩
  · rw [← h 0 ⟨le_rfl, hT⟩]
    exact H.init
  · exact (H.integrable k t ht).congr_fun (fun σ hσ => hrhs t ht σ hσ k) measurableSet_Icc
  · rw [← h t ht]
    rw [H.eq k t ht]
    congr 1
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [Set.uIcc_of_le ht.1] at hσ
    exact hrhs t ht σ hσ k


/-- Gluing a solution on `[0,T₁]` with a solution on `[0,T₂]` started from `ρ^{T₁}`. -/
theorem glue {s : ℝ} {V : Torus d → ℝ} {ν K : ℝ} (hK : (d : ℝ) / 2 < K) {ρ₀ : Torus d → ℝ}
    {ρc σc : ℝ → Coeff d} {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (H₁ : MFSolRealOn d s V ν K ρ₀ ρc T₁) (H₂ : MFSolRealOn d s V ν K (mfPath ρc T₁) σc T₂) :
    MFSolRealOn d s V ν K ρ₀ (fun t => if t ≤ T₁ then ρc t else σc (t - T₁)) (T₁ + T₂) := by
  set ρ' : ℝ → Coeff d := fun t => if t ≤ T₁ then ρc t else σc (t - T₁) with hρ'
  have hT1mem : T₁ ∈ Set.Icc 0 T₁ := ⟨hT₁, le_rfl⟩
  have hsum : Summable fun k => ‖ρc T₁ k‖ :=
    summable_norm_of_memHs K hK _ (H₁.sol.cont.1 T₁ hT1mem)
  have hco : coeffOf (mfPath ρc T₁) = ρc T₁ := coeffOf_toFun _ (H₁.real T₁ hT1mem) hsum
  have hσ0 : σc 0 = ρc T₁ := by rw [H₂.sol.init, hco]
  have hA : ∀ t, t ≤ T₁ → ρ' t = ρc t := fun t ht => by simp [ρ', ht]
  have hB : ∀ t, T₁ ≤ t → ρ' t = σc (t - T₁) := by
    intro t ht
    by_cases h : t ≤ T₁
    · rw [le_antisymm h ht, hA T₁ le_rfl, sub_self, hσ0]
    · simp [ρ', h]
  have hmem2 : ∀ t ∈ Set.Icc T₁ (T₁ + T₂), t - T₁ ∈ Set.Icc 0 T₂ := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- continuity
  have hcont : ContinuousInHsOn K ρ' (Set.Icc 0 (T₁ + T₂)) := by
    have h1 : ContinuousInHsOn K ρ' (Set.Icc 0 T₁) :=
      contInHsOn_congr H₁.sol.cont (fun τ hτ => (hA τ hτ.2).symm)
    have h2 : ContinuousInHsOn K ρ' (Set.Icc T₁ (T₁ + T₂)) := by
      have := contInHsOn_comp_add (-T₁) H₂.sol.cont
        (S' := Set.Icc T₁ (T₁ + T₂)) (fun τ hτ => by
          have := hmem2 τ hτ
          simpa [sub_eq_add_neg] using this)
      refine contInHsOn_congr this fun τ hτ => ?_
      rw [hB τ hτ.1, sub_eq_add_neg]
    have := contInHsOn_union isClosed_Icc isClosed_Icc h1 h2
    rwa [Set.Icc_union_Icc_eq_Icc hT₁ (by linarith)] at this
  -- interval integrability, modewise
  have hint : ∀ k, ∀ t ∈ Set.Icc 0 (T₁ + T₂),
      IntegrableOn (fun σ => mfRhsCoeff d s V ν (ρ' σ) k) (Set.Icc 0 t) := by
    intro k t ht
    have hf1 : ∀ t' ∈ Set.Icc 0 T₁, IntegrableOn (fun σ => mfRhsCoeff d s V ν (ρ' σ) k)
        (Set.Icc 0 t') := by
      intro t' ht'
      refine (H₁.sol.integrable k t' ht').congr_fun (fun σ hσ => ?_) measurableSet_Icc
      simp only [hA σ (hσ.2.trans ht'.2)]
    by_cases hle : t ≤ T₁
    · exact hf1 t ⟨ht.1, hle⟩
    · replace hle := not_le.mp hle
      have hI2 : IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (σc (σ - T₁)) k) volume
          T₁ t := by
        have h0 := (intervalIntegrable_iff_integrableOn_Icc_of_le (show (0 : ℝ) ≤ t - T₁ by
          linarith)).2 (H₂.sol.integrable k (t - T₁) (hmem2 t ⟨hle.le, ht.2⟩))
        have := h0.comp_sub_right T₁
        simpa using this
      have hI2' : IntegrableOn (fun σ => mfRhsCoeff d s V ν (ρ' σ) k) (Set.Icc T₁ t) := by
        refine ((intervalIntegrable_iff_integrableOn_Icc_of_le hle.le).1 hI2).congr_fun
          (fun σ hσ => ?_) measurableSet_Icc
        simp only [hB σ hσ.1]
      have := (hf1 T₁ hT1mem).union hI2'
      rwa [Set.Icc_union_Icc_eq_Icc hT₁ hle.le] at this
  refine ⟨⟨?_, hcont, hint, ?_⟩, ?_⟩
  · rw [hA 0 hT₁]; exact H₁.sol.init
  · intro k t ht
    by_cases hle : t ≤ T₁
    · rw [hA t hle, H₁.sol.eq k t ⟨ht.1, hle⟩]
      congr 1
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [Set.uIcc_of_le ht.1] at hσ
      simp only [hA σ (hσ.2.trans hle)]
    · replace hle := not_le.mp hle
      have hmt : t - T₁ ∈ Set.Icc 0 T₂ := hmem2 t ⟨hle.le, ht.2⟩
      have hJ1 : IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρ' σ) k) volume 0 T₁ :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le hT₁).2 (hint k T₁ ⟨hT₁, by linarith⟩)
      have hJt : IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρ' σ) k) volume 0 t :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2 (hint k t ht)
      have hJ2 : IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρ' σ) k) volume T₁ t :=
        hJ1.symm.trans hJt
      have e1 := intervalIntegral.integral_add_adjacent_intervals hJ1 hJ2
      have e2 : ∫ σ in (0 : ℝ)..T₁, mfRhsCoeff d s V ν (ρ' σ) k =
          ∫ σ in (0 : ℝ)..T₁, mfRhsCoeff d s V ν (ρc σ) k := by
        refine intervalIntegral.integral_congr fun σ hσ => ?_
        rw [Set.uIcc_of_le hT₁] at hσ
        simp only [hA σ hσ.2]
      have e3 : ∫ σ in T₁..t, mfRhsCoeff d s V ν (ρ' σ) k =
          ∫ σ in (0 : ℝ)..(t - T₁), mfRhsCoeff d s V ν (σc σ) k := by
        have : ∫ σ in T₁..t, mfRhsCoeff d s V ν (ρ' σ) k =
            ∫ σ in T₁..t, mfRhsCoeff d s V ν (σc (σ - T₁)) k := by
          refine intervalIntegral.integral_congr fun σ hσ => ?_
          rw [Set.uIcc_of_le hle.le] at hσ
          simp only [hB σ hσ.1]
        rw [this, intervalIntegral.integral_comp_sub_right (fun σ => mfRhsCoeff d s V ν (σc σ) k)
          T₁]
        simp
      have e4 := H₂.sol.eq k (t - T₁) hmt
      have e5 := H₁.sol.eq k T₁ hT1mem
      rw [hB t hle.le, e4, ← e1, e2, e3]
      rw [hco]
      linear_combination e5
  · intro t ht
    by_cases hle : t ≤ T₁
    · rw [hA t hle]; exact H₁.real t ⟨ht.1, hle⟩
    · replace hle := not_le.mp hle
      rw [hB t hle.le]; exact H₂.real _ (hmem2 t ⟨hle.le, ht.2⟩)


theorem inv_pos_of_mem {βm βp β : ℝ} (hβm : 0 < βm) (hβ : β ∈ Set.Icc βm βp) :
    0 < β⁻¹ := inv_pos.2 (lt_of_lt_of_le hβm hβ.1)

/-- Continuation: a real solution on `[0, n T₀]` for every `n`, with `T₀ = T₀(R)` from
`MFLocal.local_exists_coeff` and `R` the `T`-uniform `H^K` bound of `mf_apriori_bound_real_on`. -/
theorem exists_solRealOn_nat (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (β : ℝ) (hβ : β ∈ Set.Icc βm βp) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ, ∃ ρc : ℝ → Coeff d, MFSolRealOn d s V β⁻¹ K ρ₀ ρc (n * T₀) := by
  have hK1 : (d : ℝ) / 2 + 1 < K := by linarith [H.hK]
  have hKd : (d : ℝ) / 2 < K := by linarith [H.hK]
  have hν : 0 < β⁻¹ := inv_pos_of_mem H.hβm hβ
  obtain ⟨c, C, -, hbd⟩ := MFApriori.mf_apriori_bound_real_on hd s βm βp K V ρ₀ H
  have LH := MFLocal.localHyp_of_isCk hd H.hs0 H.hsd K hK1 H.hV
  obtain ⟨T₀, hT₀, hex⟩ := MFLocal.local_exists_coeff LH β⁻¹ hν (max C 0) (le_max_right _ _)
  have hVint : Integrable V := by
    have hVc : Continuous V := MFAux.continuous_of_isCk (H.hV.of_le (by exact_mod_cast
      (show (1 : ℕ) ≤ K + 2 by omega)))
    exact hVc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hρint : Integrable ρ₀ := H.hρ₀H.1.integrable one_le_two
  have hmem0 : MemHs (K : ℝ) (coeffOf ρ₀) := (hsNormSq_coeffOf (K : ℝ) ρ₀ H.hρ₀H).1
  refine ⟨T₀, hT₀, fun n => ?_⟩
  induction n with
  | zero =>
    refine ⟨fun _ => coeffOf ρ₀, ⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩⟩
    · simpa using MFLocal.contInHs_const hmem0 (Set.Icc 0 ((0 : ℕ) * T₀))
    · intro k t ht
      exact integrableOn_const (by simp) (by simp)
    · intro k t ht
      have : t = 0 := by simpa using le_antisymm (by simpa using ht.2) ht.1
      subst this
      simp
    · intro t ht
      exact isRealCoeff_coeffOf ρ₀ hρint
  | succ n ih =>
    obtain ⟨ρc, hρc⟩ := ih
    have htn : (n : ℝ) * T₀ ∈ Set.Icc 0 ((n : ℝ) * T₀) :=
      ⟨by positivity, le_rfl⟩
    have hb := (hbd β hβ _ ρc hρc _ htn).2
    obtain ⟨σc, hσ, -, -, hreal⟩ := hex (ρc ((n : ℝ) * T₀)) (hρc.sol.cont.1 _ htn)
      (hb.trans (le_max_left _ _))
    have hsum : Summable fun k => ‖ρc ((n : ℝ) * T₀) k‖ :=
      summable_norm_of_memHs K hKd _ (hρc.sol.cont.1 _ htn)
    have hco : coeffOf (mfPath ρc ((n : ℝ) * T₀)) = ρc ((n : ℝ) * T₀) :=
      coeffOf_toFun _ (hρc.real _ htn) hsum
    rw [← hco] at hσ
    have hσ' := solOn_iff.1 hσ
    have hreal' : ∀ t ∈ Set.Icc 0 T₀, IsRealCoeff (σc t) := by
      rw [hco] at hσ
      exact hreal (isRealCoeff_coeffOf V hVint) (hρc.real _ htn)
    refine ⟨fun t => if t ≤ (n : ℝ) * T₀ then ρc t else σc (t - (n : ℝ) * T₀), ?_⟩
    have := glue hKd (by positivity) hT₀.le hρc ⟨hσ', hreal'⟩
    rw [show ((n + 1 : ℕ) : ℝ) * T₀ = (n : ℝ) * T₀ + T₀ by push_cast; ring]
    exact this


/-- Uniqueness of solutions on `[0,T]` under `FiniteRegHyp` (from `MFLocal.unique_on_Icc'`). -/
theorem unique_of_solOn (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (β : ℝ) (hβ : β ∈ Set.Icc βm βp)
    {ρc ρc' : ℝ → Coeff d} {T : ℝ} (h : MFSolOn d s V β⁻¹ K ρ₀ ρc T)
    (h' : MFSolOn d s V β⁻¹ K ρ₀ ρc' T) : ∀ t ∈ Set.Icc 0 T, ρc t = ρc' t := by
  have hK1 : (d : ℝ) / 2 + 1 < K := by linarith [H.hK]
  refine MFLocal.unique_on_Icc' hd s H.hs0 H.hsd K hK1 V H.hV β⁻¹ (inv_pos_of_mem H.hβm hβ) T
    ρc ρc' h.cont h'.cont (by rw [h.init, h'.init]) (fun k t ht => ?_) (fun k t ht => ?_)
  · rw [h.init]; exact h.eq k t ht
  · rw [h'.init]; exact h'.eq k t ht

/-- Existence of a global real solution (coherence of the `[0, n T₀]` solutions by
`MFLocal.unique_on_Icc'`, then `isMFSolutionHK_of_forall_solOn`). -/
theorem exists_global_real (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (β : ℝ) (hβ : β ∈ Set.Icc βm βp) :
    ∃ ρc : ℝ → Coeff d, IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc ∧ ∀ t, 0 ≤ t → IsRealCoeff (ρc t) := by
  obtain ⟨T₀, hT₀, hfam⟩ := exists_solRealOn_nat hd s βm βp K V ρ₀ H β hβ
  choose ρn hρn using hfam
  have hcoh : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Set.Icc 0 ((m : ℝ) * T₀), ρn n t = ρn m t := by
    intro m n hmn t ht
    have hle : (m : ℝ) * T₀ ≤ n * T₀ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hT₀.le
    exact unique_of_solOn hd s βm βp K V ρ₀ H β hβ ((hρn n).sol.mono hle) (hρn m).sol t ht
  have hceil : ∀ t : ℝ, t ≤ (⌈t / T₀⌉₊ : ℝ) * T₀ := fun t => by
    have := Nat.le_ceil (t / T₀)
    rwa [div_le_iff₀ hT₀] at this
  set ρc : ℝ → Coeff d := fun t => ρn ⌈t / T₀⌉₊ t with hρc
  have key : ∀ n : ℕ, ∀ t ∈ Set.Icc 0 ((n : ℝ) * T₀), ρc t = ρn n t := by
    intro n t ht
    have hm : ⌈t / T₀⌉₊ ≤ n := Nat.ceil_le.2 (by rw [div_le_iff₀ hT₀]; exact ht.2)
    exact (hcoh _ n hm t ⟨ht.1, hceil t⟩).symm
  have hglob : ∀ T, 0 ≤ T → MFSolOn d s V β⁻¹ K ρ₀ ρc T := by
    intro T hT
    exact MFSolOn.congr hT ((hρn ⌈T / T₀⌉₊).sol.mono (hceil T))
      (fun t ht => (key _ t ⟨ht.1, ht.2.trans (hceil T)⟩).symm)
  refine ⟨ρc, isMFSolutionHK_of_forall_solOn hglob, fun t ht => ?_⟩
  have htm : t ∈ Set.Icc 0 ((⌈t / T₀⌉₊ : ℝ) * T₀) := ⟨ht, hceil t⟩
  rw [key _ t htm]
  exact (hρn _).real t htm

/-- Reality of an arbitrary global solution = uniqueness against the real one. -/
theorem isRealCoeff_of_isMFSolutionHK (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρc : ℝ → Coeff d)
    (h : IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc) : ∀ t, 0 ≤ t → IsRealCoeff (ρc t) := by
  obtain ⟨ρβ, hρβ, hreal⟩ := exists_global_real hd s βm βp K V ρ₀ H β hβ
  intro t ht
  have := unique_of_solOn hd s βm βp K V ρ₀ H β hβ (MFApriori.IsMFSolutionHK.toSolOn hρβ t)
    (MFApriori.IsMFSolutionHK.toSolOn h t) t ⟨ht, le_rfl⟩
  rw [← this]
  exact hreal t ht

/-- The body of `finite_reg_exists_unique`. -/
theorem finite_reg_exists_unique (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) :
    ∀ β ∈ Set.Icc βm βp, ∃ ρc : ℝ → Coeff d,
      IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc ∧ (∀ t, 0 ≤ t → IsRealCoeff (ρc t)) ∧
      ContinuousInHsOn ((K : ℝ) - 2) (fun t => mfRhsCoeff d s V β⁻¹ (ρc t)) (Set.Ici 0) ∧
      (∀ t, 0 ≤ t → Tendsto (fun t' => hsNorm ((K : ℝ) - 2)
          (fun k => (ρc t' k - ρc t k) / ((t' - t : ℝ) : ℂ) - mfRhsCoeff d s V β⁻¹ (ρc t) k))
        (𝓝[Set.Ici 0 \ {t}] t) (𝓝 0)) ∧
      ∀ ρc' : ℝ → Coeff d, IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc' → ∀ t, 0 ≤ t → ρc' t = ρc t := by
  intro β hβ
  have hK1 : (d : ℝ) / 2 + 1 < K := by linarith [H.hK]
  obtain ⟨ρc, hρc, hreal⟩ := exists_global_real hd s βm βp K V ρ₀ H β hβ
  have LH := MFLocal.localHyp_of_isCk hd H.hs0 H.hsd K hK1 H.hV
  refine ⟨ρc, hρc, hreal, rhs_continuousInHsOn' hd s H.hs0 H.hsd K hK1 V H.hV β⁻¹ ρc _ hρc.cont,
    fun t ht => ?_, fun ρc' hρc' t ht => ?_⟩
  · have hsol := solOn_iff.2 (MFApriori.IsMFSolutionHK.toSolOn hρc (t + 1))
    have := (MFLocal.local_time_reg LH hsol).2 t ⟨ht, by linarith⟩
    refine this.mono_left (nhdsWithin_le_of_mem ?_)
    exact mem_nhdsWithin.2 ⟨Set.Iio (t + 1), isOpen_Iio, by simp,
      fun x hx => ⟨⟨hx.2.1, hx.1.le⟩, hx.2.2⟩⟩
  · exact (unique_of_solOn hd s βm βp K V ρ₀ H β hβ (MFApriori.IsMFSolutionHK.toSolOn hρc t)
      (MFApriori.IsMFSolutionHK.toSolOn hρc' t) t ⟨ht, le_rfl⟩).symm

/-- The body of `finite_reg_uniform_bounds`. -/
theorem finite_reg_uniform_bounds (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) :
    ∃ c C : ℝ, 0 < c ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρc : ℝ → Coeff d,
      IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc → ∀ t, 0 ≤ t →
        (∀ x, c ≤ mfPath ρc t x ∧ mfPath ρc t x ≤ C) ∧ hsNorm K (ρc t) ≤ C := by
  obtain ⟨c, C, hc, hbd⟩ := MFApriori.mf_apriori_bound_real_on hd s βm βp K V ρ₀ H
  refine ⟨c, C, hc, fun β hβ ρc hρc t ht => ?_⟩
  have hreal := isRealCoeff_of_isMFSolutionHK hd s βm βp K V ρ₀ H β hβ ρc hρc
  exact hbd β hβ t ρc ⟨MFApriori.IsMFSolutionHK.toSolOn hρc t, fun τ hτ => hreal τ hτ.1⟩ t
    ⟨ht, le_rfl⟩

/-- (I3) verbatim (`MFInputs.mf_apriori_bound`). -/
theorem mf_apriori_bound (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (m₁ : ℝ) (hm₁ : (d : ℝ) / 2 + 1 < m₁) (hm₁K : m₁ ≤ K) :
    ∃ c C : ℝ, 0 < c ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρc : ℝ → Coeff d,
      IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc → ∀ t, 0 ≤ t →
        (∀ x, c ≤ mfPath ρc t x ∧ mfPath ρc t x ≤ C) ∧ hsNorm m₁ (ρc t) ≤ C := by
  obtain ⟨c, C, hc, hb⟩ := finite_reg_uniform_bounds hd s βm βp K V ρ₀ H
  refine ⟨c, C, hc, fun β hβ ρc hρc t ht => ⟨(hb β hβ ρc hρc t ht).1, ?_⟩⟩
  exact (MFLocal.hsNorm_mono_idx hm₁K (hρc.cont.1 t ht)).trans (hb β hβ ρc hρc t ht).2

end HRS.PDE.MFGlobal
