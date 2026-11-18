import HRS.MS.SA12X2C
import HRS.MS.SA12NN2F

/-!
# S.A.12 N2 (SA12X2), part D: `hess_comm_finite` (all `0 ≤ s ≤ d - 1`)

Endpoint `s = d - 1`: `a Hv - H(av) = Σ_l ∂_l a Q_l - H(r_x v)(x)`, the first sum bounded by `sa12x2_Q_bound`,
the second by `sa12n_young_pow` with `t = s`; `s < d - 1` is `sa12n_comm_lt`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0
  HRS.MH.Screened HRS.MS.UniqN1a HRS.MS.UniqN2b

variable {d : ℕ}

theorem sa12x2_comm_endpoint (hd : 1 ≤ d) :
    ∃ C C₀ : ℝ, 0 < C ∧ 0 ≤ C₀ ∧ ∀ (i j : Fin d) (ρ : ℝ), 1 ≤ ρ →
      ∀ a : Euc d → ℝ, MemCb 2 a →
      ∀ (c : Euc d) (v : Euc d → ℝ), MemCb 2 v →
      Function.support v ⊆ Metric.closedBall c ρ →
      ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
        eLpNorm ((Metric.closedBall c' r').indicator (fun x =>
          a x * hessRiesz d ((d : ℝ) - 1) i j v x -
            hessRiesz d ((d : ℝ) - 1) i j (fun y => a y * v y) x)) 2 volume ≤
          ENNReal.ofReal (C * cbNorm 2 a * ρ ^ C₀) * eLpNorm v 2 volume := by
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 1 < d := by linarith
  obtain ⟨CQ, hCQ0, hCQ⟩ := sa12x2_Q_bound hd
  obtain ⟨C1, hC10, hC1⟩ := sa12n_young_pow hd (t := (d : ℝ) - 1) hs0 hsd
  set m : ℝ := max 1 ((d : ℝ) - 1) * (((d : ℝ) - 1) + 3) with hm
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) ≤ max 1 ((d : ℝ) - 1) := le_trans zero_le_one (le_max_left _ _)
    positivity
  refine ⟨d * CQ + m * C1 + 1, (d : ℝ), by positivity, Nat.cast_nonneg _,
    fun i j ρ hρ a ha c v hv hsupp c' r' hr' => ?_⟩
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  obtain ⟨hv2, hvc⟩ := sa12z3_memCb_cc hv hsupp
  have hA := sa12z3_cb_nonneg ha
  have hρ0 : 0 ≤ ρ := by linarith
  set s : ℝ := (d : ℝ) - 1 with hs
  set B : Set (Euc d) := closedBall c' r' with hB
  -- the pieces
  set Q : Fin d → Euc d → ℝ := fun l x => x l * hessRiesz d s i j v x -
    hessRiesz d s i j (fun y => y l * v y) x with hQdef
  set g : Fin d → Euc d → ℝ := fun l x => fderiv ℝ a x (EuclideanSpace.single l 1) with hgdef
  have hQc : ∀ l, Continuous (Q l) := fun l => by
    refine ((EuclideanSpace.proj l : Euc d →L[ℝ] ℝ).continuous.mul
      (sa12n_hess_continuous hs0 hsd i j hv2 hvc)).sub
      (sa12n_hess_continuous hs0 hsd i j ((EuclideanSpace.proj l : Euc d →L[ℝ] ℝ).contDiff.mul hv2)
        hvc.mul_left)
  have hgc : ∀ l, Continuous (g l) := fun l =>
    ((ha2.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  set S : Euc d → ℝ := fun x => ∑ l, g l x * Q l x with hSdef
  set T : Euc d → ℝ := fun x => (a x * hessRiesz d s i j v x -
    hessRiesz d s i j (fun y => a y * v y) x) - S x with hTdef
  have hSc : Continuous S := continuous_finsetSum _ fun l _ => (hgc l).mul (hQc l)
  have hCc : Continuous (fun x => a x * hessRiesz d s i j v x -
      hessRiesz d s i j (fun y => a y * v y) x) :=
    (ha2.continuous.mul (sa12n_hess_continuous hs0 hsd i j hv2 hvc)).sub
      (sa12n_hess_continuous hs0 hsd i j (ha2.mul hv2) hvc.mul_left)
  have hTc : Continuous T := hCc.sub hSc
  have hTeq : ∀ x, T x = - hessRiesz d s i j (fun y => sa12x2_r a x y * v y) x := fun x => by
    simp only [hTdef, hSdef, hgdef, hQdef]
    rw [sa12x2_comm_decomp hs0 hsd i j ha hv2 hvc x]; ring
  -- split
  have hsplit : B.indicator (fun x => a x * hessRiesz d s i j v x -
      hessRiesz d s i j (fun y => a y * v y) x) = ∑ l, B.indicator (fun x => g l x * Q l x) +
        B.indicator T := by
    funext x
    by_cases hx : x ∈ B
    · rw [Pi.add_apply, Finset.sum_apply]
      simp only [Set.indicator_of_mem hx, hTdef, hSdef]; ring
    · simp [Set.indicator_of_notMem hx]
  have hTb : eLpNorm (B.indicator T) 2 volume ≤
      ENNReal.ofReal (m * cbNorm 2 a * C1 * ρ ^ (d : ℝ)) * eLpNorm v 2 volume := by
    refine hC1 (m * cbNorm 2 a) (by positivity) ρ hρ c v hv2.continuous.measurable hsupp c' r' hr'
      T hTc.aestronglyMeasurable (fun x _ => ?_)
    rw [hTeq x]
    simpa using sa12x2_E_bound hd hs0 hsd i j ha hv hvc x
  have hSb : ∀ l, eLpNorm (B.indicator (fun x => g l x * Q l x)) 2 volume ≤
      ENNReal.ofReal (cbNorm 2 a * CQ) * eLpNorm v 2 volume := fun l => by
    have h1 : eLpNorm (B.indicator (fun x => g l x * Q l x)) 2 volume ≤
        eLpNorm (cbNorm 2 a • B.indicator (Q l)) 2 volume := by
      refine eLpNorm_mono (((hgc l).mul (hQc l)).aestronglyMeasurable.indicator
        measurableSet_closedBall) fun x => ?_
      by_cases hx : x ∈ B
      · simp only [Set.indicator_of_mem hx, Pi.smul_apply, smul_eq_mul, norm_mul]
        have : ‖g l x‖ ≤ cbNorm 2 a := by
          have := sa12n_fderiv_apply_le ha x l
          simpa [hgdef, Real.norm_eq_abs] using this
        calc ‖g l x‖ * ‖Q l x‖ ≤ cbNorm 2 a * ‖Q l x‖ := by gcongr
          _ = ‖cbNorm 2 a‖ * ‖Q l x‖ := by rw [Real.norm_of_nonneg hA]
      · simp [Set.indicator_of_notMem hx]
    refine h1.trans ?_
    rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg hA, ENNReal.ofReal_mul hA, mul_assoc]
    gcongr
    exact hCQ i j l v hv2 hvc c' r'
  rw [hsplit]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  have hsum : eLpNorm (∑ l, B.indicator (fun x => g l x * Q l x)) 2 volume ≤
      ENNReal.ofReal (d * (cbNorm 2 a * CQ)) * eLpNorm v 2 volume := by
    refine (eLpNorm_sum_le (by norm_num)).trans ?_
    refine (Finset.sum_le_sum fun l _ => hSb l).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]
  refine (add_le_add hsum hTb).trans ?_
  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have hρd : 1 ≤ ρ ^ (d : ℝ) := Real.one_le_rpow hρ (Nat.cast_nonneg _)
  have hρd0 : 0 ≤ ρ ^ (d : ℝ) := by linarith
  calc (d : ℝ) * (cbNorm 2 a * CQ) + m * cbNorm 2 a * C1 * ρ ^ (d : ℝ)
      ≤ d * CQ * cbNorm 2 a * ρ ^ (d : ℝ) + m * C1 * cbNorm 2 a * ρ ^ (d : ℝ) := by
        have : (d : ℝ) * (cbNorm 2 a * CQ) ≤ d * CQ * cbNorm 2 a * ρ ^ (d : ℝ) := by
          have h0 : 0 ≤ (d : ℝ) * CQ * cbNorm 2 a := by positivity
          nlinarith
        nlinarith
    _ ≤ (d * CQ + m * C1 + 1) * cbNorm 2 a * ρ ^ (d : ℝ) := by
        have : 0 ≤ cbNorm 2 a * ρ ^ (d : ℝ) := by positivity
        nlinarith

/-- N2: local order-zero Hessian commutator (all `0 ≤ s ≤ d - 1`). -/
theorem hess_comm_finite (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ (d : ℝ)-1) :
    ∃ C C₀ : ℝ, 0 < C ∧ 0 ≤ C₀ ∧ ∀ (i j : Fin d) (ρ : ℝ), 1 ≤ ρ →
      ∀ a : Euc d → ℝ, MemCb 2 a →
      ∀ (c : Euc d) (v : Euc d → ℝ), MemCb 2 v →
      Function.support v ⊆ Metric.closedBall c ρ →
      ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
        eLpNorm ((Metric.closedBall c' r').indicator (fun x =>
          a x*hessRiesz d s i j v x-hessRiesz d s i j (fun y => a y*v y) x)) 2 volume ≤
          ENNReal.ofReal (C*cbNorm 2 a*ρ^C₀)*eLpNorm v 2 volume := by
  rcases hs1.eq_or_lt with h | h
  · subst h
    exact sa12x2_comm_endpoint hd
  · exact sa12n_comm_lt hd s hs0 h

end HRS.MH.AdjointRd.Phase2SA12Near
