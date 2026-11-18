import HRS.MS.SuppU3Aux5

/-!
# U3, part 6: `u3_abstract` (see `SuppU3Aux5`)
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.SuppU3
open HRS.Whole.AppendixA

variable {d : ℕ}

theorem u3_abstract (d m : ℕ) (hm : 2 ≤ m) (K : ℝ) (hK : 0 ≤ K) (χ : Euc d → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    ∃ C : ℝ, ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      {ι : Type} (ℓ : ι → H →L[ℝ] ℝ) (nrm : ι → ℝ),
      (∀ (F : H) (c : ℝ), 0 ≤ c → (∀ i, |ℓ i F| ≤ c * nrm i) → ‖F‖ ≤ c) →
      ∀ (Φ : Fin d → Euc d → H), (∀ j i, ContDiff ℝ m (fun x => ℓ i (Φ j x))) →
      (∀ j i, ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k (fun x => ℓ i (Φ j x)) x‖ ≤ K * nrm i) →
      ∀ B : H →L[ℝ] H, ‖B‖ ≤ 1 →
        (⨆ x : Euc d, ENNReal.ofReal |∑ j, inner ℝ (B (Φ j x)) (Φ j x)|) +
          (⨆ p : {p : Euc d × Euc d // p.1 ≠ p.2},
            ENNReal.ofReal (|∑ j, inner ℝ (B (Φ j p.1.1)) (Φ j p.1.1) -
              ∑ j, inner ℝ (B (Φ j p.1.2)) (Φ j p.1.2)| / ‖p.1.1 - p.1.2‖)) +
          ulocNormE m χ (fun x => ∑ j, inner ℝ (B (Φ j x)) (Φ j x)) ≤ ENNReal.ofReal C := by
  obtain ⟨C0, hC0, hlimit⟩ := u3_sobE_prod_limit d m
  have hS : HRS.Whole.sobolevNormE (m : ℝ) χ ≠ ⊤ :=
    HRS.MS.UlocMW.um_chi_finite hχ hχc (Nat.cast_nonneg m)
  set S : ℝ≥0∞ := HRS.Whole.sobolevNormE (m : ℝ) χ with hSdef
  set A : ℝ := (m + 1) * (d * 2 ^ m * K ^ 2) with hAdef
  have hA0 : 0 ≤ A := by positivity
  refine ⟨d * K ^ 2 + 2 * d * K ^ 2 + C0 * A * S.toReal, ?_⟩
  intro H _ _ _ ι ℓ nrm hnorm Φ hΦ hΦb B hB
  -- boundedness and Lipschitz continuity of `Φ_j`
  have hΦn : ∀ j x, ‖Φ j x‖ ≤ K := fun j x => by
    refine hnorm (Φ j x) K hK (fun i => ?_)
    have := hΦb j i 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this
  have hΦL : ∀ j x y, ‖Φ j x - Φ j y‖ ≤ K * ‖x - y‖ := fun j x y => by
    refine hnorm _ _ (by positivity) (fun i => ?_)
    have hd : Differentiable ℝ (fun x => ℓ i (Φ j x)) :=
      (hΦ j i).differentiable (by exact_mod_cast (by omega : m ≠ 0))
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fun x => ℓ i (Φ j x)) (s := Set.univ)
      (C := K * nrm i) (x := y) (y := x) (fun z _ => hd z) (fun z _ => by
        rw [← norm_iteratedFDeriv_one]; exact hΦb j i 1 (by omega) z) convex_univ trivial trivial
    rw [map_sub, ← Real.norm_eq_abs]
    calc ‖ℓ i (Φ j x) - ℓ i (Φ j y)‖ ≤ K * nrm i * ‖x - y‖ := this
      _ = K * ‖x - y‖ * nrm i := by ring
  have hΦc : ∀ j, Continuous (Φ j) := fun j => by
    have : LipschitzWith K.toNNReal (Φ j) := LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK]; exact hΦL j x y
    exact this.continuous
  set h : Euc d → ℝ := fun x => ∑ j, inner ℝ (B (Φ j x)) (Φ j x) with hh
  have hhb : ∀ x, |h x| ≤ d * K ^ 2 := fun x => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |inner ℝ (B (Φ j x)) (Φ j x)| ≤ ∑ _j : Fin d, K ^ 2 :=
          Finset.sum_le_sum fun j _ => u3_quad_bd B hB hK (hΦn j x)
      _ = d * K ^ 2 := by simp
  have hhL : ∀ x y, |h x - h y| ≤ 2 * d * K ^ 2 * ‖x - y‖ := fun x y => by
    have : h x - h y = ∑ j, (inner ℝ (B (Φ j x)) (Φ j x) - inner ℝ (B (Φ j y)) (Φ j y)) := by
      simp only [hh, Finset.sum_sub_distrib]
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |inner ℝ (B (Φ j x)) (Φ j x) - inner ℝ (B (Φ j y)) (Φ j y)|
        ≤ ∑ _j : Fin d, (2 * K * (K * ‖x - y‖)) :=
          Finset.sum_le_sum fun j _ =>
            (u3_quad_lip B hB hK (hΦn j x) (hΦn j y)).trans
              (mul_le_mul_of_nonneg_left (hΦL j x y) (by positivity))
      _ = 2 * d * K ^ 2 * ‖x - y‖ := by simp; ring
  -- the Lipschitz part
  have lip1 : (⨆ x : Euc d, ENNReal.ofReal |h x|) ≤ ENNReal.ofReal (d * K ^ 2) :=
    iSup_le fun x => ENNReal.ofReal_le_ofReal (hhb x)
  have lip2 : (⨆ p : {p : Euc d × Euc d // p.1 ≠ p.2},
      ENNReal.ofReal (|h p.1.1 - h p.1.2| / ‖p.1.1 - p.1.2‖)) ≤ ENNReal.ofReal (2 * d * K ^ 2) :=
    iSup_le fun p => ENNReal.ofReal_le_ofReal (by
      rw [div_le_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 p.2))]
      exact hhL _ _)
  -- the uniformly local part
  have hΨ : ∀ n j, ContDiff ℝ ∞ (u3_moll (u3_bump (d := d) n) (Φ j)) := fun n j =>
    u3_moll_contDiff _ _ (hΦc j)
  have hΨb : ∀ n j, ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k (u3_moll (u3_bump (d := d) n) (Φ j)) x‖ ≤ K :=
    fun n j k hk x => u3_moll_bound ℓ nrm hnorm _ (u3_bump_rOut_le n) (Φ j) (hΦc j) m hK (hΦ j)
      (hΦb j) k hk x
  have hcb := fun n => u3_h_cb B hB (fun j => u3_moll (u3_bump (d := d) n) (Φ j)) (hΨ n) m hK (hΨb n)
  have hconv : ∀ x, Tendsto (fun n => ∑ j, inner ℝ (B (u3_moll (u3_bump (d := d) n) (Φ j) x))
      (u3_moll (u3_bump (d := d) n) (Φ j) x)) atTop (𝓝 (h x)) := by
    intro x
    refine tendsto_finset_sum _ fun j _ => ?_
    have hj : Tendsto (fun n => u3_moll (u3_bump (d := d) n) (Φ j) x) atTop (𝓝 (Φ j x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => u3_moll_dist _ _ (hΦc j) hK (hΦL j) x) ?_
      simpa using u3_bump_tendsto.const_mul K
    exact (B.continuous.continuousAt.tendsto.comp hj).inner hj
  have huloc : ulocNormE m χ h ≤ ENNReal.ofReal (C0 * A * S.toReal) := by
    unfold ulocNormE
    refine iSup_le fun z => ?_
    have hfin : HRS.Whole.sobolevNormE (m : ℝ) (fun x => χ (x - z)) ≠ ⊤ := by
      rw [HRS.MS.SobMul.sobolevNormE_translate]; exact hS
    have := hlimit A (fun n x => ∑ j, inner ℝ (B (u3_moll (u3_bump (d := d) n) (Φ j) x))
      (u3_moll (u3_bump (d := d) n) (Φ j) x)) h (fun n => (hcb n).1) (fun n => (hcb n).2) hconv
      (fun x => χ (x - z)) hfin
    have e : (fun x => χ (x - z) * h x) = fun x => h x * χ (x - z) := funext fun x => mul_comm _ _
    rw [e]
    refine this.trans ?_
    rw [HRS.MS.SobMul.sobolevNormE_translate, ← hSdef]
    rw [← ENNReal.ofReal_toReal hS, ← ENNReal.ofReal_mul (by positivity)]
    simp [hSdef]
  calc _ ≤ ENNReal.ofReal (d * K ^ 2) + ENNReal.ofReal (2 * d * K ^ 2) +
        ENNReal.ofReal (C0 * A * S.toReal) := add_le_add (add_le_add lip1 lip2) huloc
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

end HRS.MS.SuppU3
