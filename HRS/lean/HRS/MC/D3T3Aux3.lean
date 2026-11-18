import HRS.MC.D3T3Aux2

/-!
# Packet D3T3, auxiliary facts: decay of `ψ̂`, uniform bound for `Pφ_t - ∫φ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform

namespace HRS.MC.D3T3

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1

variable {d : ℕ}

lemma d3f_psiHat_cont {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : Continuous (fdlPsiHat ψ) := by
  have h2 : ∀ ξ : Euc d, (𝓕 (perSchwartz hψ)) ξ = ((fdlPsiHat ψ ξ : ℝ) : ℂ) := by
    intro ξ
    rw [← per_fourier_psiC hψ ξ]
    exact congrFun (SchwartzMap.fourier_coe (perSchwartz hψ)) ξ
  have : fdlPsiHat ψ = fun ξ => ((𝓕 (perSchwartz hψ)) ξ).re := by
    funext ξ; rw [h2]; simp
  rw [this]
  exact Complex.continuous_re.comp (𝓕 (perSchwartz hψ)).continuous

lemma d3f_enorm_ge_one {k : Lattice d} (hk : k ≠ 0) : 1 ≤ Lattice.enorm k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
    have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    exact_mod_cast this
  calc (1 : ℝ) ≤ |(k i : ℝ)| := h1
    _ = ‖(Lattice.toEuc k) i‖ := by simp [Lattice.toEuc]
    _ ≤ ‖Lattice.toEuc k‖ := PiLp.norm_apply_le _ i

lemma d3f_norm_smul_toEuc {t : ℝ} (ht : 0 < t) (k : Lattice d) :
    ‖t • Lattice.toEuc k‖ = t * Lattice.enorm k := by
  rw [norm_smul, Real.norm_of_nonneg ht.le]; rfl

/-- Schwartz decay of `ψ̂(tk)²`. -/
lemma d3f_psi_sq {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ k : Lattice d, k ≠ 0 →
      fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 ≤
        C * t ^ (-(2 * (q : ℝ))) * Lattice.enorm k ^ (-(2 * (q : ℝ))) := by
  obtain ⟨C0, hC0, hdec⟩ := per_psiHat_decay hψ q
  refine ⟨C0 ^ 2, sq_nonneg _, fun t ht k hk => ?_⟩
  have hen : 0 < Lattice.enorm k := lt_of_lt_of_le one_pos (d3f_enorm_ge_one hk)
  have h1 := hdec (t • Lattice.toEuc k)
  rw [d3f_norm_smul_toEuc ht] at h1
  have hp : 0 < (t * Lattice.enorm k) ^ q := pow_pos (mul_pos ht hen) q
  have h2 : |fdlPsiHat ψ (t • Lattice.toEuc k)| ≤ C0 / (t * Lattice.enorm k) ^ q := by
    rw [le_div_iff₀ hp]; linarith
  have h3 : fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 ≤ (C0 / (t * Lattice.enorm k) ^ q) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  refine h3.trans (le_of_eq ?_)
  have e1 : t ^ (-(2 * (q : ℝ))) = ((t ^ q) ^ 2)⁻¹ := by
    rw [Real.rpow_neg ht.le, show (2 * (q : ℝ)) = ((2 * q : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul']
  have e2 : Lattice.enorm k ^ (-(2 * (q : ℝ))) = ((Lattice.enorm k ^ q) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hen.le, show (2 * (q : ℝ)) = ((2 * q : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul']
  rw [e1, e2, div_pow, mul_pow, mul_pow]
  field_simp


lemma d3f_rpow_comb {t : ℝ} (ht : 0 < t) (a r : ℝ) :
    t ^ a / t * t ^ r = t ^ (a - 1 + r) := by
  rw [← Real.rpow_sub_one ht.ne', ← Real.rpow_add ht]

/-- Integrability of `t^{d-s} ψ̂(tk)² / t` on `(λ, ∞)` for `k ≠ 0`. -/
lemma d3f_int_psi {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s : ℝ} (hs0 : 0 ≤ s) {lam : ℝ}
    (hlam : 0 < lam) {k : Lattice d} (hk : k ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t)
      (Ioi lam) := by
  obtain ⟨C, hC0, hC⟩ := d3f_psi_sq hψ (d + 1)
  have hen : 0 < Lattice.enorm k := lt_of_lt_of_le one_pos (d3f_enorm_ge_one hk)
  have hg : IntegrableOn (fun t : ℝ => (C * Lattice.enorm k ^ (-(2 * ((d + 1 : ℕ) : ℝ)))) *
      t ^ ((d : ℝ) - s - 1 + (-(2 * ((d + 1 : ℕ) : ℝ))))) (Ioi lam) := by
    refine Integrable.const_mul (integrableOn_Ioi_rpow_of_lt ?_ hlam) _
    push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine Integrable.mono' hg ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hc := d3f_psiHat_cont hψ
    refine ContinuousOn.div (ContinuousOn.mul ?_ ?_) continuousOn_id (fun t ht => (lt_trans hlam ht).ne')
    · exact ContinuousOn.rpow_const continuousOn_id (fun t ht => Or.inl (lt_trans hlam ht).ne')
    · exact ((hc.comp (continuous_id.smul continuous_const)).pow 2).continuousOn
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := lt_trans hlam ht
    have h1 := hC t ht0 k hk
    have hnn : 0 ≤ t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t :=
      div_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (sq_nonneg _)) ht0.le
    rw [Real.norm_of_nonneg hnn]
    calc t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t
        = (t ^ ((d : ℝ) - s) / t) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 := by ring
      _ ≤ (t ^ ((d : ℝ) - s) / t) * (C * t ^ (-(2 * ((d + 1 : ℕ) : ℝ))) *
            Lattice.enorm k ^ (-(2 * ((d + 1 : ℕ) : ℝ)))) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg (Real.rpow_nonneg ht0.le _) ht0.le)
      _ = (C * Lattice.enorm k ^ (-(2 * ((d + 1 : ℕ) : ℝ)))) *
            (t ^ ((d : ℝ) - s) / t * t ^ (-(2 * ((d + 1 : ℕ) : ℝ)))) := by ring
      _ = _ := by rw [d3f_rpow_comb ht0]

/-- Uniform bound `|Pφ_t - ∫φ| ≤ K t^{-(2d+2)}` for all `t > 0`. -/
lemma d3f_unif_bound (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → ∀ x : Torus d,
      |fdlPer (fdlPhiScale ψ t) x - ∫ y, fdlPhi ψ y| ≤ K * t ^ (-(2 * ((d + 1 : ℕ) : ℝ))) := by
  obtain ⟨C, hC0, hC⟩ := d3f_psi_sq hψ (d + 1)
  have hsum := summable_enorm_rpow_aux (d := d) (-(2 * ((d + 1 : ℕ) : ℝ)))
    (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  set S0 : ℝ := ∑' k : NonzeroLattice d, Lattice.enorm k.1 ^ (-(2 * ((d + 1 : ℕ) : ℝ))) with hS
  have hS0 : 0 ≤ S0 := tsum_nonneg fun k => Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨C * S0, mul_nonneg hC0 hS0, fun t ht x => ?_⟩
  have hcont : Continuous (perQ ψ t) := (per_fdlPer_continuous hψ ht).sub continuous_const
  have hco : ∀ k : Lattice d, k ≠ 0 →
      ‖Torus.fcoef (perQ ψ t) k‖ ≤ (C * t ^ (-(2 * ((d + 1 : ℕ) : ℝ)))) *
        Lattice.enorm k ^ (-(2 * ((d + 1 : ℕ) : ℝ))) := by
    intro k hk
    rw [per_fcoef_Q hd hψ ht k, if_neg hk, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    exact hC t ht k hk
  have hsumA : Summable (fun k : NonzeroLattice d => (C * t ^ (-(2 * ((d + 1 : ℕ) : ℝ)))) *
      Lattice.enorm k.1 ^ (-(2 * ((d + 1 : ℕ) : ℝ)))) := hsum.mul_left _
  have hsumN : Summable (fun k : Lattice d => ‖Torus.fcoef (perQ ψ t) k‖) := by
    rw [Torus.summable_lattice_iff]
    exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hco k.1 k.2) hsumA
  have h1 := Torus.abs_le_tsum_fcoef hcont hsumN x
  refine h1.trans ?_
  rw [Torus.tsum_lattice _ hsumN]
  have h0 : ‖Torus.fcoef (perQ ψ t) 0‖ = 0 := by
    rw [per_fcoef_Q hd hψ ht 0]; simp
  rw [h0, zero_add]
  calc ∑' k : NonzeroLattice d, ‖Torus.fcoef (perQ ψ t) k.1‖
      ≤ ∑' k : NonzeroLattice d, (C * t ^ (-(2 * ((d + 1 : ℕ) : ℝ)))) *
        Lattice.enorm k.1 ^ (-(2 * ((d + 1 : ℕ) : ℝ))) :=
        Summable.tsum_le_tsum (fun k => hco k.1 k.2) ((Torus.summable_lattice_iff _).mp hsumN) hsumA
    _ = (C * t ^ (-(2 * ((d + 1 : ℕ) : ℝ)))) * S0 := by rw [tsum_mul_left]
    _ = _ := by ring

end HRS.MC.D3T3
