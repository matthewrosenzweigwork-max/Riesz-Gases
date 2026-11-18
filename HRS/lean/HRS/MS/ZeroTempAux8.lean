import HRS.MS.ZeroTempAux7
import HRS.MS.SuppU15Aux1
import HRS.MS.SuppU15Aux2
import HRS.MS.SuppU15Aux3
import HRS.MS.S1c2Aux3
import HRS.Commutator.Whole.Bridge
import HRS.MH.CommSuperCS10

/-!
# SA11, packet C1b: the commutator bound along the adjoint orbit

* `sa11_iter_le_cbNorm`, `sa11_hasLipBound`, `sa11_cM_le`: Lipschitz bound of `Mᵀ∇f` from the `C_b^{m_*}` bound.
* `sa11_transport`: for `α > 0`, `p > 1`, `⌊α⌋ + 2 ≤ m_*`, the fractional transport bound of `Mᵀ∇f` for `f ∈ C^{m_*}` with a weak
  jet `G ∈ W^{m,p}` (`fracLp_rep` applied to `∂_i f`; classical derivatives are the weak ones, `sa11_weak_eq_classical`).
* `sa11_oN_cmp`: `oNΛ C₀' (max Λ 1) N ≤ oNΛ C₀ Λ N` for `C₀ ≥ C₀min`.
* `sa11_density_facts`: `ρ ≤ max Λ 1` and the weighted bound from the regularity in `RdStanding`.
-/

noncomputable section

open MeasureTheory
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.ZeroTemp

variable {d : ℕ}

theorem sa11_iter_le_cbNorm {k : ℕ} {f : Euc d → ℝ} (hf : MemCb k f) {i : ℕ} (hi : i ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ HRS.cbNorm k f := by
  have h1 := le_ciSup (hf.2 i hi) x
  refine h1.trans ?_
  unfold HRS.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (by omega))

theorem sa11_hasLipBound (N : Matrix (Fin d) (Fin d) ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) {σ : ℝ}
    (hσ : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ σ) :
    HasLipBoundW (fun x => Torus.matVec N (gradient f x)) (HRS.MS.SuppU15.u15_cM N * σ) := by
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans (hσ 0)
  refine ⟨⟨HRS.MS.SuppU15.u15_cM N * σ, mul_nonneg (HRS.MS.SuppU15.u15_cM_nonneg N) hσ0⟩, ?_, le_rfl⟩
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have e : Torus.matVec N (gradient f x) - Torus.matVec N (gradient f y) =
      Torus.matVec N (gradient f x - gradient f y) := by
    unfold Torus.matVec; simp
  rw [e]
  calc ‖Torus.matVec N (gradient f x - gradient f y)‖
      ≤ HRS.MS.SuppU15.u15_cM N * ‖gradient f x - gradient f y‖ := HRS.MS.SuppU15.u15_matVec_norm_le _ _
    _ ≤ HRS.MS.SuppU15.u15_cM N * (σ * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (HRS.MS.SuppU15.u15_grad_lip hf hσ x y) (HRS.MS.SuppU15.u15_cM_nonneg N)
    _ = (⟨HRS.MS.SuppU15.u15_cM N * σ, mul_nonneg (HRS.MS.SuppU15.u15_cM_nonneg N) hσ0⟩ : ℝ≥0) * ‖x - y‖ := by
        show _ = (HRS.MS.SuppU15.u15_cM N * σ) * ‖x - y‖
        ring

theorem sa11_cM_le (N : Matrix (Fin d) (Fin d) ℝ) {B : ℝ} (hN : ∀ i j, |N i j| ≤ B) :
    HRS.MS.SuppU15.u15_cM N ≤ (d : ℝ) ^ 2 * B := by
  have hB : 0 ≤ B ∨ d = 0 := by
    by_cases hd : d = 0
    · exact Or.inr hd
    · left
      have : 0 < d := Nat.pos_of_ne_zero hd
      exact (abs_nonneg _).trans (hN ⟨0, this⟩ ⟨0, this⟩)
  have hB0 : 0 ≤ B ∨ (d : ℝ) ^ 2 = 0 := by
    rcases hB with h | h
    · exact Or.inl h
    · right; subst h; simp
  have hrhs : 0 ≤ (d : ℝ) ^ 2 * B := by
    rcases hB0 with h | h
    · positivity
    · rw [h]; simp
  unfold HRS.MS.SuppU15.u15_cM
  refine ContinuousLinearMap.opNorm_le_bound _ hrhs fun v => ?_
  show ‖Matrix.toEuclideanLin N v‖ ≤ _
  have hcomp : ∀ i, |(Matrix.toEuclideanLin N v) i| ≤ (d : ℝ) * B * ‖v‖ := by
    intro i
    have e : (Matrix.toEuclideanLin N v) i = ∑ j, N i j * v j := HRS.MS.SuppU15.u15_matVec_apply N v i
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |N i j * v j| ≤ ∑ _j : Fin d, B * ‖v‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hN i j) (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v j) (abs_nonneg _)
            ((abs_nonneg _).trans (hN i j))
      _ = (d : ℝ) * B * ‖v‖ := by simp [mul_assoc]
  calc ‖Matrix.toEuclideanLin N v‖ ≤ ∑ i, |(Matrix.toEuclideanLin N v) i| := HRS.MS.SuppU15.u15_norm_le_sum _
    _ ≤ ∑ _i : Fin d, (d : ℝ) * B * ‖v‖ := Finset.sum_le_sum fun i _ => hcomp i
    _ = (d : ℝ) ^ 2 * B * ‖v‖ := by simp; ring

/-! ### The comparison of the completion terms -/

theorem sa11_oN_cmp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (C₀' Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ N : ℕ, 1 ≤ N →
      oNΛ d s C₀' (max Λ 1) N ≤ oNΛ d s C₀ Λ N := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨max C₀' ((C₀' + |Real.log Λ| / (2 * d)) / Λ ^ (s / d)), fun C₀ hC₀ N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hΛs : 0 < Λ ^ (s / d) := Real.rpow_pos_of_pos hΛ _
  have hNs : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg hN0.le _
  have hC1 : C₀' ≤ C₀ := (le_max_left _ _).trans hC₀
  have hC2 : C₀' + |Real.log Λ| / (2 * d) ≤ C₀ * Λ ^ (s / d) := by
    have := (div_le_iff₀ hΛs).1 ((le_max_right _ _).trans hC₀)
    linarith
  unfold oNΛ
  rcases le_total 1 Λ with h1 | h1
  · rw [max_eq_left h1]
    have h2 : C₀' * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) ≤ C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hΛs.le) hNs
    linarith
  · rw [max_eq_right h1]
    have hl : Real.log Λ ≤ 0 := Real.log_nonpos hΛ.le h1
    have hrpow : (1 : ℝ) ^ (s / d) = 1 := Real.one_rpow _
    by_cases hs : s = 0
    · have hs' : s / d = 0 := by rw [hs]; simp
      simp only [if_pos hs, hs', Real.rpow_zero, mul_one, zero_sub, Real.rpow_neg_one]
      rw [hs', Real.rpow_zero] at hC2
      rw [abs_of_nonpos hl] at hC2
      have hlog : Real.log ((N : ℝ) * Λ) = Real.log N + Real.log Λ := Real.log_mul hN0.ne' hΛ.ne'
      rw [hlog]
      have hInv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.2 hN0.le
      have e : (Real.log N + Real.log Λ) / (2 * d * N) + C₀ * (N : ℝ)⁻¹ -
          (Real.log N / (2 * d * N) + C₀' * (N : ℝ)⁻¹) =
          (N : ℝ)⁻¹ * (C₀ - C₀' + Real.log Λ / (2 * d)) := by
        field_simp
        ring
      have key : 0 ≤ C₀ - C₀' + Real.log Λ / (2 * d) := by
        have : -Real.log Λ / (2 * d) = -(Real.log Λ / (2 * d)) := by ring
        rw [this] at hC2
        linarith
      have := mul_nonneg hInv key
      linarith
    · rw [if_neg hs, if_neg hs, hrpow, mul_one]
      have habs : 0 ≤ |Real.log Λ| / (2 * (d : ℝ)) := by positivity
      have h2 : C₀' * (N : ℝ) ^ (s / d - 1) ≤ C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hNs
      linarith

/-! ### The density facts -/

theorem sa11_density_facts {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
    {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    (∀ x, S.ρ N t x ≤ max Λ 1) ∧ (∀ x, jbracket x ^ ((d : ℝ) + 3) * |S.ρ N t x| ≤ max Λ 0) := by
  obtain ⟨hcb, hfin, hle⟩ := (hS.mean_field.regular N hN).1 t ht
  have hcb0 : 0 ≤ HRS.cbNorm r (S.ρ N t) := Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hw0 : 0 ≤ (weightedSupE r ((d : ℝ) + 3) (S.ρ N t)).toReal := ENNReal.toReal_nonneg
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have h1 : |S.ρ N t x| ≤ HRS.cbNorm r (S.ρ N t) := by
      have := sa11_iter_le_cbNorm hcb (Nat.zero_le r) x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    calc S.ρ N t x ≤ |S.ρ N t x| := le_abs_self _
      _ ≤ Λ := by linarith
      _ ≤ max Λ 1 := le_max_left _ _
  · refine HRS.MS.SuppU15.u15_weighted_zero (k := r) ?_ x
    have h2 : (weightedSupE r ((d : ℝ) + 3) (S.ρ N t)).toReal ≤ Λ := by linarith
    calc weightedSupE r ((d : ℝ) + 3) (S.ρ N t)
        = ENNReal.ofReal (weightedSupE r ((d : ℝ) + 3) (S.ρ N t)).toReal := (ENNReal.ofReal_toReal hfin.ne).symm
      _ ≤ ENNReal.ofReal Λ := ENNReal.ofReal_le_ofReal h2

/-! ### The fractional transport bound of `Mᵀ∇f` from the weak jet -/

section Transport

variable {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa11_transport (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (hℓ : ⌊α⌋₊ + 2 ≤ mStar d) (hmm : mStar d ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Nm : Matrix (Fin d) (Fin d) ℝ) (G : WmpSpace d m p) (f : Euc d → ℝ) (σ : ℝ),
      ContDiff ℝ ((mStar d : ℕ) : WithTop ℕ∞) f →
      (∀ᵐ x ∂(volume : Measure (Euc d)), ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = f x) →
      (∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ σ) →
      HasFracTransportBound α p (fun x => Torus.matVec Nm (gradient f x))
        (HRS.MS.SuppU15.u15_cM Nm * (σ + C * ‖G‖)) := by
  have hp2 : 2 ≤ p := Fact.out
  have hp1 : 1 < p := by linarith
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨C0, hC0, hrep⟩ := HRS.S1C2.fracLp_rep hd hα hp1
  set ℓ : ℕ := ⌊α⌋₊ + 1 with hℓdef
  refine ⟨(d : ℝ) * C0 * (1 + (d : ℝ) ^ (ℓ + 1)), by positivity, fun Nm G f σ hf hG hσ => ?_⟩
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by exact_mod_cast (by omega : 2 ≤ mStar d))
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast (by omega : 1 ≤ mStar d))
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans (hσ 0)
  set EG : ℝ≥0∞ := eLpNorm ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) (ENNReal.ofReal p) volume with hEG
  have hEGfin : EG < ⊤ := Lp.eLpNorm_lt_top (G : WLp d m p)
  have hGnorm : ‖G‖ = EG.toReal := Lp.norm_def (G : WLp d m p)
  -- the weak jet: classical derivatives of order `ℓ + 1` and `1`
  have hj1 : 1 < m + 1 := by omega
  have hjℓ : ℓ + 1 < m + 1 := by omega
  have hweak1 : ∀ i0 : Fin d, ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x ⟨⟨1, hj1⟩, fun _ => i0⟩ = partialDeriv (fun _ : Fin 1 => i0) f x :=
    fun i0 => sa11_weak_eq_classical G ⟨1, hj1⟩ (fun _ => i0) (by simpa using hf1) hG
  have hweakℓ : ∀ i : Fin (ℓ + 1) → Fin d, ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x ⟨⟨ℓ + 1, hjℓ⟩, i⟩ = partialDeriv i f x :=
    fun i => sa11_weak_eq_classical G ⟨ℓ + 1, hjℓ⟩ i
      (hf.of_le (by exact_mod_cast (by omega : ℓ + 1 ≤ mStar d))) hG
  have hDℓ := sa11_iter_le_weak (f := f) (j := ℓ + 1) hjℓ (G : WLp d m p) hweakℓ
  -- the components `v_i`
  have hcomp : ∀ i0 : Fin d, ∃ w : Euc d → ℝ, IsFracDerivRep α (fun x => gradient f x i0) w ∧
      MemLp w (ENNReal.ofReal p) volume ∧
      eLpNorm w (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (C0 * (1 + (d : ℝ) ^ (ℓ + 1))) * EG := by
    intro i0
    set v : Euc d → ℝ := fun x => gradient f x i0 with hv
    have hveq : ∀ x, v x = fderiv ℝ f x (EuclideanSpace.single i0 1) := fun x => q09_gradient_apply f x i0
    have hvcd : ContDiff ℝ (ℓ : WithTop ℕ∞) v := by
      have h1 : ContDiff ℝ (ℓ : WithTop ℕ∞) (fderiv ℝ f) :=
        hf.fderiv_right (by exact_mod_cast (by omega : ℓ + 1 ≤ mStar d))
      have : v = fun x => (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i0 1 : Euc d)) (fderiv ℝ f x) := by
        funext x; exact hveq x
      rw [this]
      exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i0 1 : Euc d)).contDiff.comp h1
    have hvc : Continuous v := hvcd.continuous
    -- `‖v x‖ ≤ ‖G x‖`
    have hv_le : ∀ᵐ x ∂(volume : Measure (Euc d)), ‖v x‖ ≤ ‖((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x‖ := by
      filter_upwards [hweak1 i0] with x hx
      have h1 := norm_le_pi_norm (((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x) (⟨⟨1, hj1⟩, fun _ => i0⟩ : WIndex d m)
      rw [hx] at h1
      have e : partialDeriv (fun _ : Fin 1 => i0) f x = v x := by
        unfold partialDeriv
        rw [iteratedFDeriv_one_apply]
        exact (hveq x).symm
      rw [e] at h1
      exact h1
    have hv_eL : eLpNorm v (ENNReal.ofReal p) volume ≤ EG := eLpNorm_mono_ae hvc.aestronglyMeasurable hv_le
    -- the `ℓ`-th derivative of `v`
    have hDvc : Continuous (iteratedFDeriv ℝ ℓ v) := hvcd.continuous_iteratedFDeriv le_rfl
    have hDv_le : ∀ᵐ x ∂(volume : Measure (Euc d)), ‖iteratedFDeriv ℝ ℓ v x‖ ≤
        ‖((d : ℝ) ^ (ℓ + 1)) • ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x‖ := by
      filter_upwards [hDℓ] with x hx
      have h1 : ‖iteratedFDeriv ℝ ℓ v x‖ ≤ ‖iteratedFDeriv ℝ (ℓ + 1) f x‖ := by
        have hc : ContDiffAt ℝ (ℓ : WithTop ℕ∞) (fderiv ℝ f) x :=
          (hf.fderiv_right (by exact_mod_cast (by omega : ℓ + 1 ≤ mStar d))).contDiffAt
        have e : v = fun y => (fderiv ℝ f y) (EuclideanSpace.single i0 (1 : ℝ)) := funext hveq
        rw [e]
        have := norm_iteratedFDeriv_clm_apply_const (c := (EuclideanSpace.single i0 (1 : ℝ) : Euc d)) (n := ℓ) hc le_rfl
        rw [norm_iteratedFDeriv_fderiv] at this
        simpa using this
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact h1.trans hx
    have hDv_eL : eLpNorm (iteratedFDeriv ℝ ℓ v) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((d : ℝ) ^ (ℓ + 1)) * EG := by
      calc eLpNorm (iteratedFDeriv ℝ ℓ v) (ENNReal.ofReal p) volume
          ≤ eLpNorm (((d : ℝ) ^ (ℓ + 1)) • ((G : WLp d m p) : Euc d → (WIndex d m → ℝ))) (ENNReal.ofReal p) volume :=
            eLpNorm_mono_ae hDvc.aestronglyMeasurable hDv_le
        _ = ENNReal.ofReal ((d : ℝ) ^ (ℓ + 1)) * EG := by
            rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    have hvmem : MemLp v (ENNReal.ofReal p) volume := lt_of_le_of_lt hv_eL hEGfin
    have hDvmem : MemLp (iteratedFDeriv ℝ ℓ v) (ENNReal.ofReal p) volume :=
      lt_of_le_of_lt hDv_eL (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hEGfin)
    obtain ⟨w, -, hwrep, hwmem, hwle⟩ := hrep v (by simpa [hℓdef] using hvcd) hvmem (by simpa [hℓdef] using hDvmem)
    refine ⟨w, hwrep, hwmem, hwle.trans ?_⟩
    calc ENNReal.ofReal C0 * (eLpNorm v (ENNReal.ofReal p) volume + eLpNorm (iteratedFDeriv ℝ (⌊α⌋₊ + 1) v) (ENNReal.ofReal p) volume)
        ≤ ENNReal.ofReal C0 * (EG + ENNReal.ofReal ((d : ℝ) ^ (ℓ + 1)) * EG) := by
          gcongr
        _ = ENNReal.ofReal (C0 * (1 + (d : ℝ) ^ (ℓ + 1))) * EG := by
          rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
          ring
  choose w hwrep hwmem hwle using hcomp
  -- assemble
  have hsup : (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) ≤ ENNReal.ofReal σ :=
    iSup_le fun x => ENNReal.ofReal_le_ofReal (hσ x)
  have hsum : ∑ i, eLpNorm (w i) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((d : ℝ) * C0 * (1 + (d : ℝ) ^ (ℓ + 1))) * EG := by
    calc ∑ i, eLpNorm (w i) (ENNReal.ofReal p) volume
        ≤ ∑ _i : Fin d, ENNReal.ofReal (C0 * (1 + (d : ℝ) ^ (ℓ + 1))) * EG := Finset.sum_le_sum fun i _ => hwle i
      _ = ENNReal.ofReal ((d : ℝ) * C0 * (1 + (d : ℝ) ^ (ℓ + 1))) * EG := by
          have e : ENNReal.ofReal ((d : ℝ) * C0 * (1 + (d : ℝ) ^ (ℓ + 1))) =
              (d : ℝ≥0∞) * ENNReal.ofReal (C0 * (1 + (d : ℝ) ^ (ℓ + 1))) := by
            rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, e, mul_assoc]
  have hfinS : (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) + ∑ i, eLpNorm (w i) (ENNReal.ofReal p) volume ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (add_le_add hsup hsum)
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEGfin.ne⟩
  have hT := HRS.MS.SuppU15.u15_transport Nm (p := p) hp1.le hf2 hwrep hwmem hfinS
  refine HRS.MS.SuppU15.u15_hasFrac_mono hT ?_
  refine mul_le_mul_of_nonneg_left ?_ (HRS.MS.SuppU15.u15_cM_nonneg Nm)
  have hfin2 : ENNReal.ofReal σ + ENNReal.ofReal ((d : ℝ) * C0 * (1 + (d : ℝ) ^ (ℓ + 1))) * EG ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEGfin.ne⟩
  have h1 := ENNReal.toReal_mono hfin2 (add_le_add hsup hsum)
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEGfin.ne),
    ENNReal.toReal_ofReal hσ0, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← hGnorm] at h1
  exact h1

end Transport

end HRS.MS.ZeroTemp
