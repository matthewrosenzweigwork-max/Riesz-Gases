import HRS.MS.Fp81S21GaussianW0
import HRS.MS.Fp81S21MovingStd3
import HRS.MS.Fp81S21SLin
import HRS.MS.R2InterpAux108
import HRS.MS.ProClosureS111SourceIntegrability

/-! Quantitative series estimates for moving encoded orbits. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp
open HRS.MS.ProClosureS111 HRS.MS.S111K4J01 HRS.MS.R26T6 HRS.MS.S111X1

/-- Cauchy–Schwarz for the coefficients and the square-summable jet envelope. -/
theorem fp81s21_moving_series_cauchy {d : ℕ} (a c : MultiIndex d → ℝ)
    (ha : Summable fun α => a α ^ 2) (hc : Summable fun α => c α ^ 2)
    (hc0 : ∀ α, 0 ≤ c α) :
    Summable (fun α => |a α| * c α) ∧
      (∑' α, |a α| * c α) ≤
        Real.sqrt (∑' α, a α ^ 2) * Real.sqrt (∑' α, c α ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have ha' : Summable (fun α => |a α| ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two, sq_abs] using ha
  have hc' : Summable (fun α => c α ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two] using hc
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq
    (fun α => abs_nonneg (a α)) hc0 ha' hc'
  constructor
  · exact h.1
  · simpa only [Real.rpow_two, sq_abs, Real.sqrt_eq_rpow] using h.2

/-- A square-summable family of coefficient-weighted modes has bounded
spatial jets, with a bound linear in the coefficient ℓ² norm. -/
theorem fp81s21_moving_series_jets {d k : ℕ}
    (a c : MultiIndex d → ℝ) (g : MultiIndex d → Euc d → ℝ)
    (ha : Summable fun α => a α ^ 2) (hc : Summable fun α => c α ^ 2)
    (hc0 : ∀ α, 0 ≤ c α)
    (hg : ∀ α, ContDiff ℝ (k : WithTop ℕ∞) (g α))
    (hb : ∀ α j, j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j (g α) x‖ ≤ c α) :
    let f := fun x => ∑' α, a α * g α x
    MemCb k f ∧ ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j f x‖ ≤
        Real.sqrt (∑' α, a α ^ 2) * Real.sqrt (∑' α, c α ^ 2) := by
  obtain ⟨hs, hsbound⟩ := fp81s21_moving_series_cauchy a c ha hc hc0
  have hcd : ∀ α, ContDiff ℝ (k : WithTop ℕ∞) (fun x => a α * g α x) :=
    fun α => contDiff_const.mul (hg α)
  have hbd : ∀ (j : ℕ) (α : MultiIndex d) (x : Euc d), (j : ℕ∞) ≤ k →
      ‖iteratedFDeriv ℝ j (fun y => a α * g α y) x‖ ≤ |a α| * c α := by
    intro j α x hj
    have hjk : j ≤ k := by exact_mod_cast hj
    change ‖iteratedFDeriv ℝ j (a α • g α) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply (a := a α) (i := j) (f := g α)
      ((hg α).of_le (by exact_mod_cast hjk)).contDiffAt, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb α j hjk x) (abs_nonneg _)
  have hreg : ContDiff ℝ (k : WithTop ℕ∞) (fun x => ∑' α, a α * g α x) :=
    contDiff_tsum (𝕜 := ℝ) (N := (k : ℕ∞)) (v := fun _ α => |a α| * c α)
      hcd (fun _ _ => hs) hbd
  have hjet : ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => ∑' α, a α * g α y) x‖ ≤
        Real.sqrt (∑' α, a α ^ 2) * Real.sqrt (∑' α, c α ^ 2) := by
    intro j hj x
    have hnorm : Summable (fun α => ‖iteratedFDeriv ℝ j
        (fun y => a α * g α y) x‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun α => hbd j α x (by exact_mod_cast hj)) hs
    rw [iteratedFDeriv_tsum_apply (𝕜 := ℝ) (N := (k : ℕ∞))
      (v := fun _ α => |a α| * c α) hcd (fun _ _ => hs) hbd
      (by exact_mod_cast hj) x]
    exact (norm_tsum_le_tsum_norm hnorm).trans
      ((Summable.tsum_le_tsum (fun α => hbd j α x (by exact_mod_cast hj))
        hnorm hs).trans hsbound)
  exact ⟨⟨hreg, fun j hj => ⟨_, by rintro _ ⟨x, rfl⟩; exact hjet j hj x⟩⟩, hjet⟩

/-- Uniform moving-mode jets for an arbitrary oscillator test on a fixed horizon. -/
theorem fp81s21_moving_orbit_jet_bound
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    {φ : Euc p.d → ℝ} (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ)
    {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc u H) :
    MemCb (2 * p.d + 9) (propagatorW (r26t3_coeff R) u t φ) ∧
      ∀ j ≤ 2 * p.d + 9, ∀ x,
        ‖iteratedFDeriv ℝ j (propagatorW (r26t3_coeff R) u t φ) x‖ ≤
          oscNorm (wholeSpaceIndex p.d : ℝ) φ * Real.sqrt (∑' α, c α ^ 2) := by
  let m : ℝ := wholeSpaceIndex p.d
  let a : MultiIndex p.d → ℝ := fun α => oscEigenvalue p.d α ^ (m / 2) * hermiteCoeff φ α
  let g : MultiIndex p.d → Euc p.d → ℝ := fun α =>
    propagatorW (r26t3_coeff R) u t (oscTestFun m α)
  have haeq : ∀ α, a α ^ 2 = oscEigenvalue p.d α ^ m * hermiteCoeff φ α ^ 2 := by
    intro α
    dsimp [a]
    rw [mul_pow, rpow_half_sq _ _ (oscEv_pos α)]
  have ha : Summable (fun α => a α ^ 2) := by
    simpa only [haeq] using hφ.2.2
  have hnorm : Real.sqrt (∑' α, a α ^ 2) = oscNorm m φ := by
    unfold oscNorm
    congr 1
    exact tsum_congr haeq
  have hg : ∀ α, ContDiff ℝ ((2 * p.d + 9 : ℕ) : WithTop ℕ∞) (g α) := by
    intro α
    have he : 2 * p.d + 9 = (2 * p.d + 8) + 1 := by omega
    rw [he]
    exact hstd.hD.smoothU α u hu t ht
  have hb : ∀ α j, j ≤ 2 * p.d + 9 → ∀ x,
      ‖iteratedFDeriv ℝ j (g α) x‖ ≤ c α := by
    intro α j hj x
    exact hstd.hD.bddU α u hu t ht j (by omega) x
  have hser := fp81s21_moving_series_jets a c g ha hstd.hD.summable hstd.hD.nonneg hg hb
  have hs := (fp81s21_moving_series_cauchy a c ha hstd.hD.summable hstd.hD.nonneg).1
  have hsum : ∀ x, Summable (fun α => a α * g α x) := by
    intro x
    apply Summable.of_norm_bounded hs
    intro α
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h0 := hb α 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
    exact mul_le_mul_of_nonneg_left h0 (abs_nonneg _)
  let ψ : oscSub p.d m := ⟨φ, hφ⟩
  have hfinite : ∀ n, propagatorW (r26t3_coeff R) u t
      (HRS.MS.MovOsc.mo_pSum φ n) = fun x =>
        ∑ α ∈ HRS.MS.MovOsc.mova2_S p.d n, a α * g α x := by
    intro n
    have hsec := HRS.MS.ProClosureS111.initialTestSection_coe ψ n
    have hsec' : (HRS.MS.ProClosureS111.initialTestSection ψ n : Euc p.d → ℝ) =
        fun x => ∑ α ∈ HRS.MS.MovOsc.mova2_S p.d n, a α * oscTestFun m α x := by
      funext x
      exact HRS.MS.ProClosureS111.initialTestSection_apply ψ n x
    rw [← hsec, hsec']
    exact s102_prop_sum (fp81s21_S102Lin p R H) hu.1 ht.1 ht.2 _ _
  have heq : propagatorW (r26t3_coeff R) u t φ = fun x => ∑' α, a α * g α x := by
    funext x
    have hlim := (fp81s21_gaussian_W0_propagator_truncation p R
      (hu.1.trans ht.1) u ⟨hu.1, ht.1⟩ φ hφ).tendsto_at x
    have hlim' := (hsum x).hasSum.comp
      (tendsto_atTop_finset_of_monotone HRS.MS.MovOsc.mova2_S_mono
        HRS.MS.MovOsc.mova2_S_exh)
    apply tendsto_nhds_unique hlim
    simpa only [Function.comp_def, hfinite] using hlim'
  rw [heq]
  simpa only [hnorm] using hser

#print axioms fp81s21_moving_series_cauchy
#print axioms fp81s21_moving_orbit_jet_bound
#print axioms fp81s21_moving_series_jets
end HRS.Fp81.S21
end
