import HRS.MS.WadAux3
import HRS.MS.ToriCoefAAux1

/-!
# S8.3, packet D2 (part 2): translation to `MemCMj` / `weightedSupE` and the Mehler bound on `C_M^j`

* `s83_memCMj_iff`: `MemCMj M j f ↔ ContDiff ℝ j f ∧ ∀ i ≤ j, CMs M (iteratedFDeriv ℝ i f)`.
* `s83_wsup_le_iff`: `weightedSupE j (-M) f ≤ ofReal K ↔` all partial derivatives of order `≤ j` are `≤ K ⟨x⟩^M`.
* `s83_P_memCMj`: for `f ∈ C_M^j`, `M ≥ 0`: `P_t f ∈ C_M^j` and
  `‖P_t f‖_{M,j} ≤ 2^M mom d^j ‖f‖_{M,j}`, uniformly in `t ≥ 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s83_abs_partial_le (i : ℕ) (idx : Fin i → Fin d) (f : Euc d → ℝ) (x : Euc d) :
    |partialDeriv idx f x| ≤ ‖iteratedFDeriv ℝ i f x‖ := by
  unfold partialDeriv
  have := (iteratedFDeriv ℝ i f x).le_opNorm (fun l => (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d))
  simp only [EuclideanSpace.norm_single, norm_one, Finset.prod_const_one, mul_one] at this
  rwa [Real.norm_eq_abs] at this

theorem s83_norm_iter_le_card {K : ℝ} (hK : 0 ≤ K) (i : ℕ) (f : Euc d → ℝ) (x : Euc d)
    (h : ∀ idx : Fin i → Fin d, |partialDeriv idx f x| ≤ K) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ (d : ℝ) ^ i * K := by
  refine (HRS.MS.ToriCoefA.tca_norm_iteratedFDeriv_le_sum i f x).trans ?_
  calc ∑ idx : Fin i → Fin d, |partialDeriv idx f x| ≤ ∑ idx : Fin i → Fin d, K :=
        Finset.sum_le_sum fun idx _ => h idx
    _ = (d : ℝ) ^ i * K := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]

/-- `MemCMj` in terms of the iterated Fréchet derivatives. -/
theorem s83_memCMj_iff (M : ℝ) (j : ℕ) (f : Euc d → ℝ) :
    MemCMj M j f ↔ ContDiff ℝ j f ∧ ∀ i ≤ j, CMs M (iteratedFDeriv ℝ i f) := by
  have hp : ∀ x : Euc d, 0 < jbracket x ^ M := fun x => Real.rpow_pos_of_pos (s83_jb_pos x) _
  constructor
  · rintro ⟨hf, h⟩
    refine ⟨hf, fun i hi => ⟨hf.continuous_iteratedFDeriv (by exact_mod_cast hi), ?_⟩⟩
    have hsum : Tendsto (fun x : Euc d => ∑ idx : Fin i → Fin d, |partialDeriv idx f x| / jbracket x ^ M)
        (cocompact (Euc d)) (𝓝 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin i → Fin d)) (fun idx _ => by
        have h1 := (tendsto_zero_iff_norm_tendsto_zero.1 (h i hi idx))
        refine h1.congr fun x => ?_
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (hp x)])
      simpa using this
    refine squeeze_zero (fun x => div_nonneg (norm_nonneg _) (hp x).le) (fun x => ?_) hsum
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (HRS.MS.ToriCoefA.tca_norm_iteratedFDeriv_le_sum i f x) (hp x).le
  · rintro ⟨hf, h⟩
    refine ⟨hf, fun i hi idx => ?_⟩
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun x => norm_nonneg _) (fun x => ?_) (h i hi).2
    rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg (hp x).le]
    exact div_le_div_of_nonneg_right (s83_abs_partial_le i idx f x) (hp x).le

theorem s83_wsup_le_iff {M K : ℝ} (hK : 0 ≤ K) (j : ℕ) (f : Euc d → ℝ) :
    weightedSupE j (-M) f ≤ ENNReal.ofReal K ↔
      ∀ i ≤ j, ∀ idx : Fin i → Fin d, ∀ x, |partialDeriv idx f x| ≤ K * jbracket x ^ M := by
  have hp : ∀ x : Euc d, 0 < jbracket x ^ M := fun x => Real.rpow_pos_of_pos (s83_jb_pos x) _
  have hneg : ∀ x : Euc d, jbracket x ^ (-M) = (jbracket x ^ M)⁻¹ := fun x =>
    Real.rpow_neg (s83_jb_pos x).le _
  unfold weightedSupE derivSupE
  simp only [iSup_le_iff]
  constructor
  · intro h i hi idx x
    have := h ⟨i, by omega⟩ idx x
    rw [ENNReal.ofReal_le_ofReal_iff hK, hneg, inv_mul_le_iff₀ (hp x)] at this
    rwa [mul_comm]
  · intro h i idx x
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hneg, inv_mul_le_iff₀ (hp x), mul_comm]
    exact h i.1 (by omega) idx x

/-- A `C_M^j` function has finite weighted norm. -/
theorem s83_wsup_ne_top {M : ℝ} {j : ℕ} {f : Euc d → ℝ} (hf : MemCMj M j f) :
    weightedSupE j (-M) f ≠ ⊤ := by
  obtain ⟨-, hcm⟩ := (s83_memCMj_iff M j f).1 hf
  have : ∀ i : Fin (j + 1), ∃ C, Wt M C (iteratedFDeriv ℝ i f) := fun i => s83_cm_wt (hcm i (by omega))
  choose C hC using this
  set K := ∑ i : Fin (j + 1), |C i| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((s83_wsup_le_iff hK0 j f).2 ?_)
  intro i hi idx x
  refine (s83_abs_partial_le i idx f x).trans ((hC ⟨i, by omega⟩ x).trans ?_)
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (s83_jb_pos x).le _)
  refine (le_abs_self _).trans ?_
  exact Finset.single_le_sum (f := fun i : Fin (j + 1) => |C i|) (fun i _ => abs_nonneg _)
    (Finset.mem_univ (⟨i, by omega⟩ : Fin (j + 1)))

/-- **D1/D2 for `C_M^j`**: the Mehler semigroup preserves `C_M^j` with a bound independent of `t`. -/
theorem s83_P_memCMj {M : ℝ} (hM : 0 ≤ M) {j : ℕ} {f : Euc d → ℝ} (hf : MemCMj M j f) {a ν t : ℝ}
    (ha : 0 < a) (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    MemCMj M j (s83_P a ν t f) ∧
      weightedSupE j (-M) (s83_P a ν t f) ≤
        ENNReal.ofReal (2 ^ M * mom d M (Real.sqrt (ν / a)) * ((d : ℝ) + 1) ^ j) *
          weightedSupE j (-M) f := by
  obtain ⟨hcd, hcm⟩ := (s83_memCMj_iff M j f).1 hf
  obtain ⟨hG1, hG2, hG3⟩ := s83_G_iter hM (s83_mc_pos a t) (s83_mc_le_one ha.le ht)
    (s83_abs_ms_le ha hν ht) j f hcd hcm
  refine ⟨(s83_memCMj_iff M j _).2 ⟨hG1, hG2⟩, ?_⟩
  have hW := s83_wsup_ne_top hf
  set K0 := (weightedSupE j (-M) f).toReal with hK0
  have hK00 : 0 ≤ K0 := ENNReal.toReal_nonneg
  have hle : weightedSupE j (-M) f ≤ ENNReal.ofReal K0 := by rw [hK0, ENNReal.ofReal_toReal hW]
  have hpart := (s83_wsup_le_iff hK00 j f).1 hle
  set K := 2 ^ M * mom d M (Real.sqrt (ν / a)) with hK
  have hKnn : 0 ≤ K := mul_nonneg (by positivity) (s83_mom_nonneg _ _ (Real.sqrt_nonneg _))
  have hc1 := s83_mc_le_one ha.le ht
  have hc0 := s83_mc_pos a t
  have hbound : weightedSupE j (-M) (s83_P a ν t f) ≤ ENNReal.ofReal (K * ((d : ℝ) + 1) ^ j * K0) := by
    rw [s83_wsup_le_iff (by positivity) j]
    intro i hi idx x
    have hW1 : Wt M ((d : ℝ) ^ i * K0) (iteratedFDeriv ℝ i f) := fun y => by
      have := s83_norm_iter_le_card (K := K0 * jbracket y ^ M)
        (mul_nonneg hK00 (Real.rpow_nonneg (s83_jb_pos y).le _)) i f y
        (fun idx' => hpart i hi idx' y)
      calc ‖iteratedFDeriv ℝ i f y‖ ≤ (d : ℝ) ^ i * (K0 * jbracket y ^ M) := this
        _ = (d : ℝ) ^ i * K0 * jbracket y ^ M := by ring
    have h2 := hG3 i hi _ hW1 x
    refine (s83_abs_partial_le i idx _ x).trans (h2.trans ?_)
    have hci : s83_mc a t ^ i ≤ 1 := pow_le_one₀ hc0.le hc1
    have hdi : (d : ℝ) ^ i ≤ ((d : ℝ) + 1) ^ j :=
      calc (d : ℝ) ^ i ≤ ((d : ℝ) + 1) ^ i := pow_le_pow_left₀ (by positivity) (by linarith) i
        _ ≤ ((d : ℝ) + 1) ^ j := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) hi
    have hjb : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (s83_jb_pos x).le _
    show 2 ^ M * mom d M (Real.sqrt (ν / a)) * s83_mc a t ^ i * ((d : ℝ) ^ i * K0) * jbracket x ^ M ≤ _
    refine mul_le_mul_of_nonneg_right ?_ hjb
    calc K * s83_mc a t ^ i * ((d : ℝ) ^ i * K0) ≤ K * 1 * (((d : ℝ) + 1) ^ j * K0) := by
          gcongr
      _ = K * ((d : ℝ) + 1) ^ j * K0 := by ring
  refine hbound.trans ?_
  rw [ENNReal.ofReal_mul (by positivity), hK0, ENNReal.ofReal_toReal hW]

end HRS.MS.Wad
