import HRS.MS.SA16Y5Ip1

/-!
# S.A.16 (SA16Y5) Hl2: the energy pairing of `C_c^∞` jets with any smooth `ψ` whose jets are bounded in `L^p` by `S_j(φ)`

`sa16y5_dens_le`: if `‖∂^idx ψ‖_p ≤ K S_j(φ)` for all `j ≤ m` and `|idx| = j`, then
`∫ sa16sz_dens m p φ ψ ≤ C ∑_{k ≤ m} ∫ |D^kφ|^p`, `C = C(d,p,m,K)` (Young `sa16z_young_pair`, as the error pairing of `sa16z_level`).
Used for `ψ = ±P^A_μ φ` (`sa16y5_PA_bound`): the skew part of the Hilbert operator costs only a bounded energy term.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.BreakdownSA16

section Hl2
variable {d : ℕ}

theorem sa16y5_dens_level {p : ℝ} (hp : 2 ≤ p) (j : ℕ) {K : ℝ} (hK0 : 0 ≤ K) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ {φ ψ : Euc d → ℝ}, IsCcInfty φ → ContDiff ℝ ∞ ψ →
      (∀ idx : Fin j → Fin d, eLpNorm (partialDeriv idx ψ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal K * sa16z_S p φ j) →
      ∫ x, sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x * partialDeriv idx ψ x ≤
        Cj * ∑ k ∈ Finset.range (j + 1), ∫ x, sa16sz_vn φ k x ^ p := by
  have hp0 : 0 < p := by linarith
  set N : ℝ := (d : ℝ) ^ j with hN
  have hNpos : 0 ≤ N := by positivity
  refine ⟨N * ((p - 1) / p) + (1 / p) * N * (K ^ p * ((j : ℝ) + 1) ^ (p - 1)), ?_, fun {φ ψ} hφ hψ hb => ?_⟩
  · have h3 : 0 ≤ N * ((p - 1) / p) := mul_nonneg hNpos (div_nonneg (by linarith) hp0.le)
    have h4 : 0 ≤ (1 / p) * N * (K ^ p * ((j : ℝ) + 1) ^ (p - 1)) :=
      mul_nonneg (mul_nonneg (by positivity) hNpos)
        (mul_nonneg (Real.rpow_nonneg hK0 _) (Real.rpow_nonneg (by positivity) _))
    linarith
  set V : ℕ → ℝ := fun k => ∫ x, sa16sz_vn φ k x ^ p with hV
  have hV0 : ∀ k, 0 ≤ V k := fun k => integral_nonneg fun x => Real.rpow_nonneg (sa16sz_vn_nonneg φ k x) _
  have hVj : V j ≤ ∑ k ∈ Finset.range (j + 1), V k :=
    Finset.single_le_sum (f := V) (fun k _ => hV0 k) (Finset.mem_range.2 (by omega))
  have hSfin : sa16z_S p φ j ≠ ⊤ := by
    unfold sa16z_S
    exact (ENNReal.sum_lt_top.2 fun k _ => sa16z_JJ_lt_top hφ k).ne
  have hErr' : ∀ idx : Fin j → Fin d, Integrable (fun x => |partialDeriv idx ψ x| ^ p) ∧
      ∫ x, |partialDeriv idx ψ x| ^ p ≤ (K * (sa16z_S p φ j).toReal) ^ p := by
    intro idx
    have hne : ENNReal.ofReal K * sa16z_S p φ j ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfin
    have := sa16z_rpow_int_of_eLpNorm (sa16j_pd_smooth hψ idx).continuous.aestronglyMeasurable hp0 hne (hb idx)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0] at this
    exact this
  have hVint : Integrable (fun x => sa16sz_vn φ j x ^ p) := by
    exact (sa16sz_vn_pow_cont φ hφ.1 j hp0.le).integrable_of_hasCompactSupport
      ((sa16sz_vn_cs hφ j).comp_left (g := fun y : ℝ => y ^ p) (Real.zero_rpow hp0.ne'))
  set h : Euc d → ℝ := fun x => ∑ idx : Fin j → Fin d, (((p - 1) / p) * sa16sz_vn φ j x ^ p +
    (1 / p) * |partialDeriv idx ψ x| ^ p) with hh
  have hyoung : ∀ x, sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x * partialDeriv idx ψ x ≤
      h x := fun x =>
    sa16z_young_pair hp (fun idx => partialDeriv idx φ x) (fun idx => partialDeriv idx ψ x)
  have hh0 : ∀ x, 0 ≤ h x := fun x => Finset.sum_nonneg fun idx _ => add_nonneg
    (mul_nonneg (div_nonneg (by linarith) hp0.le) (Real.rpow_nonneg (sa16sz_vn_nonneg φ j x) _))
    (mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _))
  have hInt : ∀ idx : Fin j → Fin d, Integrable (fun x => ((p - 1) / p) * sa16sz_vn φ j x ^ p +
      (1 / p) * |partialDeriv idx ψ x| ^ p) :=
    fun idx => (hVint.const_mul _).add ((hErr' idx).1.const_mul _)
  have hhint : Integrable h := integrable_finsetSum _ fun idx _ => hInt idx
  have hE1 := sa16z_integral_le_of_le hyoung hhint hh0
  have hcard : (Fintype.card (Fin j → Fin d) : ℝ) = N := by simp [hN]
  have hE2 : ∫ x, h x ≤ N * ((p - 1) / p) * V j + (1 / p) * N * (K ^ p * ((sa16z_S p φ j).toReal) ^ p) := by
    have e : ∫ x, h x = ∑ idx : Fin j → Fin d, ((((p - 1) / p) * V j) +
        (1 / p) * ∫ x, |partialDeriv idx ψ x| ^ p) := by
      simp only [hh]
      rw [integral_finsetSum _ fun idx _ => hInt idx]
      refine Finset.sum_congr rfl fun idx _ => ?_
      rw [integral_add (hVint.const_mul _) ((hErr' idx).1.const_mul _), integral_const_mul, integral_const_mul]
    rw [e]
    calc ∑ idx : Fin j → Fin d, ((((p - 1) / p) * V j) + (1 / p) * ∫ x, |partialDeriv idx ψ x| ^ p)
        ≤ ∑ idx : Fin j → Fin d, ((((p - 1) / p) * V j) + (1 / p) * (K * (sa16z_S p φ j).toReal) ^ p) :=
          Finset.sum_le_sum fun idx _ => by
            have := (hErr' idx).2
            have : 0 < 1 / p := by positivity
            nlinarith
      _ = N * ((p - 1) / p) * V j + (1 / p) * N * (K ^ p * ((sa16z_S p φ j).toReal) ^ p) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, Real.mul_rpow hK0 ENNReal.toReal_nonneg]
          ring
  have hSp := sa16z_S_rpow_le hφ j (by linarith : 1 ≤ p)
  have hE3 : (1 / p) * N * (K ^ p * ((sa16z_S p φ j).toReal) ^ p) ≤
      (1 / p) * N * (K ^ p * ((j : ℝ) + 1) ^ (p - 1)) * ∑ k ∈ Finset.range (j + 1), V k := by
    have h0 : 0 ≤ (1 / p) * N * K ^ p := mul_nonneg (mul_nonneg (by positivity) hNpos) (Real.rpow_nonneg hK0 _)
    calc (1 / p) * N * (K ^ p * ((sa16z_S p φ j).toReal) ^ p)
        = ((1 / p) * N * K ^ p) * ((sa16z_S p φ j).toReal) ^ p := by ring
      _ ≤ ((1 / p) * N * K ^ p) * (((j : ℝ) + 1) ^ (p - 1) * ∑ k ∈ Finset.range (j + 1), V k) :=
          mul_le_mul_of_nonneg_left hSp h0
      _ = _ := by ring
  have hc3 : 0 ≤ N * ((p - 1) / p) := mul_nonneg hNpos (div_nonneg (by linarith) hp0.le)
  have e3 : N * ((p - 1) / p) * V j ≤ N * ((p - 1) / p) * ∑ k ∈ Finset.range (j + 1), V k :=
    mul_le_mul_of_nonneg_left hVj hc3
  nlinarith [hE1, hE2, hE3, e3]

theorem sa16y5_dens_le {p : ℝ} (hp : 2 ≤ p) (m : ℕ) {K : ℝ} (hK0 : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {φ ψ : Euc d → ℝ}, IsCcInfty φ → ContDiff ℝ ∞ ψ →
      (∀ j ≤ m, ∀ idx : Fin j → Fin d, eLpNorm (partialDeriv idx ψ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal K * sa16z_S p φ j) →
      ∫ x, sa16sz_dens m p φ ψ x ≤ C * ∑ k : Fin (m + 1), ∫ x, sa16sz_vn φ k x ^ p := by
  have hlev := fun j : ℕ => sa16y5_dens_level (d := d) hp j hK0
  choose Cj hCj0 hCj using hlev
  refine ⟨∑ j ∈ Finset.range (m + 1), Cj j, Finset.sum_nonneg fun j _ => hCj0 j, fun {φ ψ} hφ hψ hb => ?_⟩
  have hV0 : ∀ k, 0 ≤ ∫ x, sa16sz_vn φ k x ^ p := fun k =>
    integral_nonneg fun x => Real.rpow_nonneg (sa16sz_vn_nonneg φ k x) _
  have e : ∀ x, sa16sz_dens m p φ ψ x = ∑ j ∈ Finset.range (m + 1),
      sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x * partialDeriv idx ψ x := by
    intro x
    unfold sa16sz_dens
    exact Fin.sum_univ_eq_sum_range (fun j => sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d,
      partialDeriv idx φ x * partialDeriv idx ψ x) (m + 1)
  have hint : ∀ j ∈ Finset.range (m + 1), Integrable (fun x => sa16sz_vn φ j x ^ (p - 2) *
      ∑ idx : Fin j → Fin d, partialDeriv idx φ x * partialDeriv idx ψ x) := by
    intro j _
    simp_rw [Finset.mul_sum]
    refine integrable_finset_sum _ fun idx _ => ?_
    exact sa16z_cc_mul_int (sa16sz_vn_pow_cont φ hφ.1 j (by linarith)) (sa16j_pd_smooth hφ.1 idx).continuous
      (sa16j_pd_smooth hψ idx).continuous (sa16s_cc_partialDeriv hφ idx).2
  simp_rw [e]
  rw [integral_finsetSum _ hint]
  have hsumk : ∑ k : Fin (m + 1), ∫ x, sa16sz_vn φ k x ^ p = ∑ k ∈ Finset.range (m + 1), ∫ x, sa16sz_vn φ k x ^ p :=
    Fin.sum_univ_eq_sum_range (fun k => ∫ x, sa16sz_vn φ k x ^ p) (m + 1)
  rw [hsumk]
  calc ∑ j ∈ Finset.range (m + 1), ∫ x, sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d,
        partialDeriv idx φ x * partialDeriv idx ψ x
      ≤ ∑ j ∈ Finset.range (m + 1), Cj j * ∑ k ∈ Finset.range (m + 1), ∫ x, sa16sz_vn φ k x ^ p := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjm : j ≤ m := by have := Finset.mem_range.1 hj; omega
        refine (hCj j hφ hψ (hb j hjm)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (hCj0 j)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun k _ _ => hV0 k
    _ = _ := by rw [Finset.sum_mul]

end Hl2

end HRS.Whole.AppendixA.Phase2SA16R
