import HRS.MS.MovAdjAux10

/-!
# S6.7 (packet P2, part 6): `ψ_r = T(t-r)† ψ_t` and the `Σ^M` decay of `ψ_r`

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

* `s67_inner_psi`: `⟨ψ[u], v⟩ = ∫ u √ρ v` for `v ∈ L²_0` (the constant drops by orthogonality to `√ρ`);
* `s67_psi_eq`: `ψ[f_r] = T(t-r)† ψ[φ]` in `L²_0` (`s67_bridge` and the density of the Schwartz core);
* `s67_spectral`: **`ψ[f_r] ∈ Σ^m` with `‖ψ[f_r]‖_{Σ^m} ≤ C e^{-c(t-r)} ‖ψ[φ]‖_{Σ^m}`** (the merged S6.2 bounds for the adjoint semigroup).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.MovLin HRS.MS.Mov63

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- `⟨ψ[u], v⟩ = ∫ u √ρ v` for `v ∈ L²_0`. -/
theorem s67_inner_psi (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {u : Euc d → ℝ} (hu : AEStronglyMeasurable u (volume : Measure (Euc d))) {B : ℝ} (hb : ∀ x, |u x| ≤ B)
    (v : MovL2Zero ρ) :
    inner ℝ ((s67mk H ψ0 hψ0 hu hb : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) (v : Lp ℝ 2 (volume : Measure (Euc d))) =
      ∫ x, u x * (Real.sqrt (ρ x) * movFun v x) := by
  have hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
    rw [← hψ0]; exact ψ0.memLp 2
  have hvL : MemLp (movFun v) 2 (volume : Measure (Euc d)) := Lp.memLp _
  have hI : Integrable (fun x => Real.sqrt (ρ x) * movFun v x) := hgL.integrable_mul hvL
  have hI1 : Integrable (fun x => u x * (Real.sqrt (ρ x) * movFun v x)) :=
    hI.bdd_mul (c := B) hu (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  set c : ℝ := ∫ y, u y * ρ y with hc
  have hcoe : ((s67mk H ψ0 hψ0 hu hb : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) =
      (s67_psi_memLp hgL hu hb).toLp (s67psi ρ u) := rfl
  rw [hcoe, s67_inner_toLp_left]
  have e : ∀ x, s67psi ρ u x * movFun v x =
      u x * (Real.sqrt (ρ x) * movFun v x) - c * (Real.sqrt (ρ x) * movFun v x) := by
    intro x; unfold s67psi; rw [← hc]; ring
  simp_rw [e]
  rw [integral_sub hI1 (hI.const_mul c), integral_const_mul, s67_orth_of_mem H ψ0 hψ0 v]
  ring

theorem s67_inner_psi' (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {u : Euc d → ℝ} (hu : AEStronglyMeasurable u (volume : Measure (Euc d))) (hbdd : ∃ B : ℝ, ∀ x, |u x| ≤ B)
    (v : MovL2Zero ρ) :
    inner ℝ ((s67mk' H ψ0 hψ0 hu hbdd : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))
        (v : Lp ℝ 2 (volume : Measure (Euc d))) =
      ∫ x, u x * (Real.sqrt (ρ x) * movFun v x) :=
  s67_inner_psi H ψ0 hψ0 hu hbdd.choose_spec v

theorem s67_f_aux {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    AEStronglyMeasurable (f r) (volume : Measure (Euc d)) ∧ ∃ B : ℝ, ∀ x, |f r x| ≤ B := by
  obtain ⟨B, -, hB⟩ := s67_f_bdd hf
  exact ⟨(hf.c2 r hr).continuous.aestronglyMeasurable, B, hB r hr⟩

theorem s67_phi_aux {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (ht : 0 ≤ t) :
    AEStronglyMeasurable φ (volume : Measure (Euc d)) ∧ ∃ B : ℝ, ∀ x, |φ x| ≤ B := by
  have := s67_f_aux hf (r := t) ⟨ht, le_rfl⟩
  rw [hf.terminal] at this
  exact this

/-- Abstract density step. -/
theorem s67_eq_of_core (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (A B : MovL2Zero ρ)
    (h : ∀ v : MovL2Zero ρ, (∃ φ₀ : 𝓢R, ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ₀ x) →
      inner ℝ A v = inner ℝ B v) : A = B := by
  set e : MovL2Zero ρ := A - B with he
  have hdense := mov2d_dense_core H ψ0 hψ0
  have hS : IsClosed {v : MovL2Zero ρ | inner ℝ e v = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hcore : ∀ v ∈ {v : MovL2Zero ρ | ∃ φ₀ : 𝓢R, ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ₀ x},
      inner ℝ e v = 0 := by
    intro v hv
    rw [he, inner_sub_left, h v hv, sub_self]
  have hall : ∀ v : MovL2Zero ρ, inner ℝ e v = 0 := by
    intro v
    have h1 := hS.closure_subset_iff.2 (fun v hv => hcore v hv)
    have hv : v ∈ closure {v : MovL2Zero ρ | ∃ φ₀ : 𝓢R, ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ₀ x} := by
      rw [hdense.closure_eq]; exact Set.mem_univ v
    exact h1 hv
  exact sub_eq_zero.1 (inner_self_eq_zero.1 (hall e))

/-- **`ψ[f_r] = T(t-r)† ψ[φ]`.** -/
theorem s67_psi_eq (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) t φ f) (ht : 0 ≤ t)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    s67mk' H ψ0 hψ0 (s67_f_aux hf hr).1 (s67_f_aux hf hr).2 =
      ContinuousLinearMap.adjoint (mov2d_T H ψ0 hψ0 (t - r))
        (s67mk' H ψ0 hψ0 (s67_phi_aux hf ht).1 (s67_phi_aux hf ht).2) := by
  refine s67_eq_of_core H ψ0 hψ0 _ _ (fun v ⟨φ₀, hv⟩ => ?_)
  rw [ContinuousLinearMap.adjoint_inner_left]
  have h1 := s67_inner_psi' H ψ0 hψ0 (s67_f_aux hf hr).1 (s67_f_aux hf hr).2 v
  have h2 := s67_inner_psi' H ψ0 hψ0 (s67_phi_aux hf ht).1 (s67_phi_aux hf ht).2
    (mov2d_T H ψ0 hψ0 (t - r) v)
  have hb := s67_bridge H ψ0 hψ0 hf hr hv
  exact (h1.trans hb).trans h2.symm

set_option maxHeartbeats 1600000 in
/-- **The spectral input**: `Σ^m` membership and decay of `ψ[f_r]`. -/
theorem s67_spectral {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, movA d s ≤ m → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 ≤ t →
        IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) t φ f →
        MemOsc m (s67psi ρ φ) → ∀ r ∈ Set.Icc (0 : ℝ) t,
          MemOsc m (s67psi ρ (f r)) ∧
            oscNorm m (s67psi ρ (f r)) ≤ C * Real.exp (-c * (t - r)) * oscNorm m (s67psi ρ φ) := by
  have H : Mov2dTh d s β q ρ := ⟨hd, hs0, hsd, hβ, hq, hρ⟩
  obtain ⟨T', hT', huniq, c, hc, hall⟩ := mov_linear_proof hd hs0 hsd β q hβ hq ρ hρ
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  refine ⟨c, hc, fun m hm => ?_⟩
  obtain ⟨C, hCb⟩ := hall m hm
  refine ⟨max C 0, le_max_right _ _, fun t φ f ht hf hφ r hr => ?_⟩
  have hτ : 0 ≤ t - r := sub_nonneg.2 hr.2
  have hEq := s67_psi_eq H ψ0 hψ0 hf ht hr
  have hBae := s67mk'_ae H ψ0 hψ0 (s67_phi_aux hf ht).1 (s67_phi_aux hf ht).2
  have hAae := s67mk'_ae H ψ0 hψ0 (s67_f_aux hf hr).1 (s67_f_aux hf hr).2
  have hBtmem : MemOsc m (movFun (s67mk' H ψ0 hψ0 (s67_phi_aux hf ht).1 (s67_phi_aux hf ht).2)) :=
    mov2b_memOsc_congr (hBae.mono fun x hx => hx.symm) m hφ
  have hTeq : mov2d_T H ψ0 hψ0 (t - r) = T' (t - r) := huniq _ (mov2d_isSemigroup H ψ0 hψ0) (t - r) hτ
  obtain ⟨hmem, hnorm⟩ := hCb.2.1 (t - r) hτ _ hBtmem
  beta_reduce at hmem hnorm
  rw [← hTeq, ← hEq] at hmem hnorm
  have hmemA : MemOsc m (s67psi ρ (f r)) := mov2b_memOsc_congr hAae m hmem
  refine ⟨hmemA, ?_⟩
  rw [← mov2b_oscNorm_congr hAae m]
  refine hnorm.trans ?_
  rw [mov2b_oscNorm_congr hBae m]
  have h0 : 0 ≤ Real.exp (-c * (t - r)) * oscNorm m (s67psi ρ φ) :=
    mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  calc C * Real.exp (-c * (t - r)) * oscNorm m (s67psi ρ φ)
      = C * (Real.exp (-c * (t - r)) * oscNorm m (s67psi ρ φ)) := by ring
    _ ≤ max C 0 * (Real.exp (-c * (t - r)) * oscNorm m (s67psi ρ φ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ = _ := by ring

end HRS.MS.MovAdj
