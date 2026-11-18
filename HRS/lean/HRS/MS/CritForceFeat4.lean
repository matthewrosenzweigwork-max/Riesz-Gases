import HRS.MS.CritForceFeat3

/-!
# S8.2 core X1, part 4: weighted decay of the gradient features from S8.3

`s82_feature_grad_decay` (hypothesis `h83 : type_of% @HRS.Whole.weighted_adjoint_decay`): for every weight
exponent `M > 0` and derivative order `j` there are constants `C, c > 0`, independent of the Hermite index
`α`, of the smoothness index `m` and of the thermal density, such that for every terminal time `v` and
every classical adjoint solution `w` of the critical backward equation with datum `φ_α = oscTestFun m α`
and `r ∈ [0,v]`, the function `w r` is `C^j` and, for `1 ≤ i ≤ j`,
`‖D^i (w r)(x)‖ ≤ C λ_α^{(⌊j+d/2⌋+1-m)/2} e^{-c(v-r)} ⟨x⟩^M`.
(Derivatives of order `≥ 1` ignore the additive constant between `propagatorW` and the projected
semigroup.)  For `v - r < 1` the bound is the weighted boundedness (S8.3 clause 3); for `v - r ≥ 1`
the exponential decay with smoothing (S8.3 clause 2).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82BD

open HRS HRS.Whole HRS.MP.RdInit

variable {d : ℕ}

theorem s82_weightedSupE_mono {k k' : ℕ} (hk : k ≤ k') (L : ℝ) (f : Euc d → ℝ) :
    weightedSupE k L f ≤ weightedSupE k' L f := by
  unfold weightedSupE derivSupE
  refine iSup_le fun jj => iSup_le fun idx => iSup_le fun x => ?_
  exact le_iSup_of_le (⟨jj.1, by have := jj.2; omega⟩ : Fin (k' + 1))
    (le_iSup_of_le idx (le_iSup_of_le x le_rfl))

theorem s82_weightedSupE_pointwise {k : ℕ} {M N : ℝ} (hN : 0 ≤ N) {f : Euc d → ℝ}
    (h : weightedSupE k (-M) f ≤ ENNReal.ofReal N) {i : ℕ} (hi : i ≤ k) (idx : Fin i → Fin d)
    (x : Euc d) : |partialDeriv idx f x| ≤ N * jbracket x ^ M := by
  have h1 : ENNReal.ofReal (jbracket x ^ (-M) * |partialDeriv idx f x|) ≤ ENNReal.ofReal N := by
    refine le_trans ?_ h
    unfold weightedSupE derivSupE
    exact le_iSup_of_le (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (k + 1))
      (le_iSup_of_le idx (le_iSup_of_le x le_rfl))
  have h2 := (ENNReal.ofReal_le_ofReal_iff hN).1 h1
  have hpos : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (s82_one_le_jb x)) _
  have h3 : jbracket x ^ (-M) = (jbracket x ^ M)⁻¹ := Real.rpow_neg (by linarith [s82_one_le_jb x]) M
  rw [h3, ← div_eq_inv_mul, div_le_iff₀ hpos] at h2
  exact h2

theorem s82_memCM_of_memCMj {M : ℝ} {j : ℕ} {ψ : Euc d → ℝ} (h : MemCMj M j ψ) : MemCM M ψ := by
  refine ⟨(h.1.continuous), ?_⟩
  have := h.2 0 (Nat.zero_le j) (fun l => (Fin.elim0 l : Fin d))
  simpa [partialDeriv] using this

/-- General datum version: for any datum `ψ ∈ C_M^j` with weighted norm at most `S`, the gradient
part of the classical solution decays exponentially in `v - r` with the constant independent of
`ψ` and of the thermal density. -/
theorem s82_datum_grad_decay (h83 : type_of% @HRS.Whole.weighted_adjoint_decay)
    (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) {M : ℝ} (hM : 0 < M) (j : ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ →
      ∀ ψ : Euc d → ℝ, MemCMj M j ψ → ∀ S : ℝ, 0 ≤ S → weightedSupE j (-M) ψ ≤ ENNReal.ofReal S →
      ∀ v : ℝ, 0 ≤ v → ∀ w : ℝ → Euc d → ℝ, IsClassicalAdjointW (critCoeff d a β ρ) v ψ w →
      ∀ r ∈ Set.Icc 0 v,
        ContDiff ℝ j (w r) ∧ ∀ i : ℕ, 1 ≤ i → i ≤ j → ∀ x : Euc d,
          ‖iteratedFDeriv ℝ i (w r) x‖ ≤ C * S * Real.exp (-c * (v - r)) * jbracket x ^ M := by
  by_cases hex : ∃ ρ₁ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ₁
  swap
  · exact ⟨0, 1, le_rfl, one_pos, fun ρ hρ => absurd ⟨ρ, hρ⟩ hex⟩
  obtain ⟨ρ₁, hρ₁⟩ := hex
  have hs0 : 0 ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hU := HRS.MS.Wad.s85_exists_semigroup hd ha hβ hρ₁ hM
  obtain ⟨-, hrest⟩ := h83 hd a β ha hβ ρ₁ hρ₁ M hM
  obtain ⟨-, hc2, hc3, -⟩ := hrest _ hU
  obtain ⟨Cj, c, hc, hCj⟩ := hc2 j
  obtain ⟨K, hK⟩ := hc3 j 1 zero_le_one
  set Cbd : ℝ := max (max Cj 0) (max K 0 * Real.exp c) with hCbd
  have hCbd0 : 0 ≤ Cbd := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨(max 1 (d : ℝ)) ^ j * Cbd, c,
    mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) hCbd0, hc,
    fun ρ hρ ψ hψj S hS0 hψE v hv w hw r hr => ?_⟩
  have hρeq : ρ = ρ₁ := (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ).trans
    (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ₁).symm
  subst hρeq
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set U := HRS.MS.Wad.s85_Ulim a β ρ M with hUdef
  have hψM : MemCM M ψ := s82_memCM_of_memCMj hψj
  set t := v - r with ht
  have ht0 : 0 ≤ t := by linarith [hr.2]
  obtain ⟨c0, hc0⟩ := s82_classical_eq_Ulim hd ha hβ hρ hM hv hψM hw hr
  have hψE0 : weightedSupE 0 (-M) ψ ≤ ENNReal.ofReal S :=
    (s82_weightedSupE_mono (Nat.zero_le j) _ _).trans hψE
  have hexp_pos : 0 < Real.exp (-c * t) := Real.exp_pos _
  -- the function `G` and its bound
  obtain ⟨G, c1, hGM, hGE, hwG⟩ : ∃ (G : Euc d → ℝ) (c1 : ℝ), MemCMj M j G ∧
      weightedSupE j (-M) G ≤ ENNReal.ofReal (Cbd * S * Real.exp (-c * t)) ∧
      ∀ x, w r x = G x + c1 := by
    by_cases ht1 : 1 ≤ t
    · obtain ⟨hmem, hbd⟩ := hCj t ht1 ψ hψM
      have hproj : HRS.Whole.projMean μ ψ = ψ + (fun _ : Euc d => -(HRS.Whole.pair μ ψ)) := by
        funext x; simp [HRS.Whole.projMean]; ring
      have hUp : U t (HRS.Whole.projMean μ ψ) = fun x => U t ψ x - HRS.Whole.pair μ ψ := by
        rw [hproj, hU.add t ht0 _ _ hψM (s82_const_memCM hM _)]
        funext x
        have this : U t (fun _ : Euc d => -(HRS.Whole.pair μ ψ)) x = -(HRS.Whole.pair μ ψ) :=
          s82_U_const hd ha hβ hρ hM ht0 (-(HRS.Whole.pair μ ψ)) x
        simp only [Pi.add_apply]
        rw [this]
        ring
      refine ⟨U t (HRS.Whole.projMean μ ψ), HRS.Whole.pair μ ψ + c0, hmem, ?_, fun x => ?_⟩
      · have hCj' : ENNReal.ofReal (Cj * Real.exp (-c * t)) ≤
            ENNReal.ofReal (max Cj 0 * Real.exp (-c * t)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hexp_pos.le)
        refine hbd.trans ((mul_le_mul' hCj' hψE0).trans ?_)
        rw [← ENNReal.ofReal_mul (mul_nonneg (le_max_right _ _) hexp_pos.le)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : max Cj 0 ≤ Cbd := le_max_left _ _
        calc max Cj 0 * Real.exp (-c * t) * S = max Cj 0 * S * Real.exp (-c * t) := by ring
          _ ≤ Cbd * S * Real.exp (-c * t) := by gcongr
      · rw [hc0 x, hUp]; ring
    · push Not at ht1
      obtain ⟨hmem, hbd⟩ := hK t ⟨ht0, ht1.le⟩ ψ hψj
      refine ⟨U t ψ, c0, hmem, ?_, hc0⟩
      refine hbd.trans ?_
      have hKle : ENNReal.ofReal K ≤ ENNReal.ofReal (max K 0) :=
        ENNReal.ofReal_le_ofReal (le_max_left _ _)
      refine (mul_le_mul' hKle hψE).trans ?_
      rw [← ENNReal.ofReal_mul (le_max_right K 0)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : max K 0 * Real.exp c ≤ Cbd := le_max_right _ _
      have h2 : 1 ≤ Real.exp c * Real.exp (-c * t) := by
        rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
      calc max K 0 * S = max K 0 * S * 1 := by ring
        _ ≤ max K 0 * S * (Real.exp c * Real.exp (-c * t)) := by
            gcongr
        _ = (max K 0 * Real.exp c) * S * Real.exp (-c * t) := by ring
        _ ≤ Cbd * S * Real.exp (-c * t) := by gcongr
  -- smoothness and derivative bounds
  have hwfun : w r = fun x => G x + c1 := funext hwG
  refine ⟨?_, fun i hi1 hij x => ?_⟩
  · rw [hwfun]; exact hGM.1.add contDiff_const
  · rw [hwfun, s82_iteratedFDeriv_add_const c1 hi1]
    have hN : 0 ≤ Cbd * S * Real.exp (-c * t) :=
      mul_nonneg (mul_nonneg hCbd0 hS0) hexp_pos.le
    have hpt := fun idx => s82_weightedSupE_pointwise hN hGE hij idx x
    have hjx : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (by linarith [s82_one_le_jb x]) _
    have := s82_iter_norm_le i G x (Cbd * S * Real.exp (-c * t) * jbracket x ^ M)
      (mul_nonneg hN hjx) hpt
    refine this.trans ?_
    have hdi : (d : ℝ) ^ i ≤ (max 1 (d : ℝ)) ^ j := by
      calc (d : ℝ) ^ i ≤ (max 1 (d : ℝ)) ^ i := by gcongr; exact le_max_right _ _
        _ ≤ (max 1 (d : ℝ)) ^ j := pow_le_pow_right₀ (le_max_left _ _) hij
    have hB : 0 ≤ Cbd * S * Real.exp (-c * t) * jbracket x ^ M := mul_nonneg hN hjx
    calc (d : ℝ) ^ i * (Cbd * S * Real.exp (-c * t) * jbracket x ^ M)
        ≤ (max 1 (d : ℝ)) ^ j * (Cbd * S * Real.exp (-c * t) * jbracket x ^ M) :=
          mul_le_mul_of_nonneg_right hdi hB
      _ = _ := by rw [ht]; ring

theorem s82_feature_grad_decay (h83 : type_of% @HRS.Whole.weighted_adjoint_decay)
    (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) {M : ℝ} (hM : 0 < M) (j : ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ →
      ∀ (m : ℝ) (α : MultiIndex d) (v : ℝ), 0 ≤ v → ∀ w : ℝ → Euc d → ℝ,
      IsClassicalAdjointW (critCoeff d a β ρ) v (oscTestFun m α) w → ∀ r ∈ Set.Icc 0 v,
        ContDiff ℝ j (w r) ∧ ∀ i : ℕ, 1 ≤ i → i ≤ j → ∀ x : Euc d,
          ‖iteratedFDeriv ℝ i (w r) x‖ ≤ C *
            oscEigenvalue d α ^ ((((⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) - m) / 2) *
            Real.exp (-c * (v - r)) * jbracket x ^ M := by
  obtain ⟨C, c, hC0, hc, hmain⟩ := s82_datum_grad_decay h83 hd a β ha hβ hM j
  obtain ⟨Cφ, hCφ0, hCφ⟩ := s82_hermite_weightedSupE_le (d := d) hM j
  refine ⟨C * Cφ, c, mul_nonneg hC0 hCφ0, hc, fun ρ hρ m α v hv w hw r hr => ?_⟩
  have hlame : 0 ≤ oscEigenvalue d α ^ ((((⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) - m) / 2) :=
    Real.rpow_nonneg (by unfold oscEigenvalue
                         have : (0 : ℝ) ≤ (α.degree : ℝ) := Nat.cast_nonneg _
                         have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
                         linarith) _
  obtain ⟨h1, h2⟩ := hmain ρ hρ _ (s82_hermite_memCMj hM j m α) _
    (mul_nonneg hCφ0 hlame) (hCφ m α) v hv w hw r hr
  refine ⟨h1, fun i hi hij x => (h2 i hi hij x).trans (le_of_eq ?_)⟩
  ring

end HRS.MS.S82BD
