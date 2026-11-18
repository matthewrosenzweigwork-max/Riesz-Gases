import HRS.MS.WhoAux6

/-!
# S54 part 7: sup bound and weighted bound of the smoothed perturbation `ouSg (ulPert φ)`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff Matrix

namespace HRS.MS.Who

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

/-- quantitative sup bound for `ulPert` -/
theorem who_pert_sup {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (ψ : SchwartzMap (Euc d) ℝ) {c : Euc d → Euc d} (hc : IsSmoothBounded c) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {B : ℝ} {φ : Euc d → ℝ}, ContDiff ℝ ((r + 3 : ℕ) : WithTop ℕ∞) φ →
      (∀ l ≤ r + 3, ∀ y, ‖iteratedFDeriv ℝ l φ y‖ ≤ B) →
      ContDiff ℝ r (ulPert s M ψ c φ) ∧ ∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i (ulPert s M ψ c φ) y‖ ≤ C * B := by
  obtain ⟨Cn, hCn0, hCn⟩ := ul_nl_cont hs0 hsd M ψ ⟨ψ, rfl⟩ (r + 3) (by omega)
  choose Bc hBc using hc.2
  set BcT : ℝ := ∑ j ∈ Finset.range (r + 1), |Bc j| with hBcT
  have hBcT0 : 0 ≤ BcT := Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨Cn * ((r + 3 : ℕ) + 1 : ℝ) + BcT * 2 ^ r + 0, by positivity, fun {B} {φ} hφ hB => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  have hmem : MemCb (r + 3) φ := ⟨hφ, fun j hj => ⟨B, by rintro _ ⟨y, rfl⟩; exact hB j hj y⟩⟩
  have hcb : cbNorm (r + 3) φ ≤ ((r + 3 : ℕ) + 1 : ℝ) * B := by
    unfold cbNorm
    calc ∑ j ∈ Finset.range (r + 3 + 1), ⨆ z, ‖iteratedFDeriv ℝ j φ z‖
        ≤ ∑ j ∈ Finset.range (r + 3 + 1), B := by
          refine Finset.sum_le_sum fun j hj => ciSup_le fun z => hB j (by have := Finset.mem_range.1 hj; omega) z
      _ = _ := by simp
  obtain ⟨hnl, hnlb⟩ := hCn φ hmem
  have hpe : ulPert s M ψ c φ = fun x => fderiv ℝ φ x (c x) - ulNL s M ψ φ x := by
    funext x; simp only [ulPert, ul4_inner_eq]
  have hfd : ContDiff ℝ ((r + 2 : ℕ) : WithTop ℕ∞) (fderiv ℝ φ) :=
    hφ.fderiv_right (by exact_mod_cast le_refl (r + 3))
  have hc2 : ContDiff ℝ ((r + 2 : ℕ) : WithTop ℕ∞) c := contDiff_infty.1 hc.1 (r + 2)
  have htr : ContDiff ℝ ((r + 2 : ℕ) : WithTop ℕ∞) (fun x => fderiv ℝ φ x (c x)) := hfd.clm_apply hc2
  have hnlc : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (ulNL s M ψ φ) := by
    have := hnl.1
    simpa using this
  refine ⟨?_, fun i hi y => ?_⟩
  · rw [hpe]
    exact (htr.of_le (by exact_mod_cast (by omega : r ≤ r + 2))).sub (hnlc.of_le (by exact_mod_cast (by omega : r ≤ r + 1)))
  · rw [hpe]
    have hsub := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := i) (f := fun x => fderiv ℝ φ x (c x))
      (g := ulNL s M ψ φ) (x := y) ((htr.of_le (by exact_mod_cast (by omega : i ≤ r + 2))).contDiffAt)
      ((hnlc.of_le (by exact_mod_cast (by omega : i ≤ r + 1))).contDiffAt)
    have e : (fun x => fderiv ℝ φ x (c x) - ulNL s M ψ φ x) =
        (fun x => fderiv ℝ φ x (c x)) - ulNL s M ψ φ := rfl
    rw [e, hsub]
    have b1 : ‖iteratedFDeriv ℝ i (fun x => fderiv ℝ φ x (c x)) y‖ ≤ BcT * 2 ^ r * B := by
      refine (norm_iteratedFDeriv_clm_apply (N := ((r + 2 : ℕ) : WithTop ℕ∞)) hfd hc2 y
        (by exact_mod_cast (by omega : i ≤ r + 2))).trans ?_
      calc ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fderiv ℝ φ) y‖ *
            ‖iteratedFDeriv ℝ (i - l) c y‖
          ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * B * BcT := by
            refine Finset.sum_le_sum fun l hl => ?_
            have hl' : l ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
            have h1 : ‖iteratedFDeriv ℝ l (fderiv ℝ φ) y‖ ≤ B := by
              rw [norm_iteratedFDeriv_fderiv]; exact hB (l + 1) (by omega) y
            have h2 : ‖iteratedFDeriv ℝ (i - l) c y‖ ≤ BcT :=
              (hBc (i - l) y).trans ((le_abs_self _).trans (Finset.single_le_sum
                (f := fun j => |Bc j|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))
            exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _) (by positivity)
        _ = B * BcT * 2 ^ i := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
        _ ≤ BcT * 2 ^ r * B := by
            have : (2 : ℝ) ^ i ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hi
            nlinarith [mul_nonneg hB0 hBcT0]
    have b2 : ‖iteratedFDeriv ℝ i (ulNL s M ψ φ) y‖ ≤ Cn * (((r + 3 : ℕ) + 1 : ℝ) * B) := by
      have := ul1_cb_deriv_le hnl (b := i) (by omega) y
      refine this.trans ?_
      calc cbNorm (r + 3 - 2) (ulNL s M ψ φ) ≤ Cn * cbNorm (r + 3) φ := hnlb
        _ ≤ Cn * (((r + 3 : ℕ) + 1 : ℝ) * B) := mul_le_mul_of_nonneg_left hcb hCn0
    calc _ ≤ _ + _ := norm_sub_le _ _
      _ ≤ BcT * 2 ^ r * B + Cn * (((r + 3 : ℕ) + 1 : ℝ) * B) := add_le_add b1 b2
      _ = _ := by ring


/-- linearity of `ouSg` on bounded continuous functions -/
theorem who_ouSg_lin (Q : Matrix (Fin d) (Fin d) ℝ) (ν η : ℝ) {H0 : Euc d → ℝ} {H : Fin d → Euc d → ℝ}
    (h0 : Continuous H0) (hb0 : ∃ B, ∀ y, |H0 y| ≤ B) (hc : ∀ k, Continuous (H k))
    (hb : ∀ k, ∃ B, ∀ y, |H k y| ≤ B) (x : Euc d) :
    ouSg Q ν η (fun y => H0 y + ∑ k, H k y) x = ouSg Q ν η H0 x + ∑ k, ouSg Q ν η (H k) x := by
  have hint : ∀ {F : Euc d → ℝ}, Continuous F → (∃ B, ∀ y, |F y| ≤ B) →
      Integrable (fun w => F (ouExp Q η x + sOU Q ν η w)) (stdGaussian (Euc d)) := by
    intro F hF ⟨B, hB⟩
    exact Integrable.of_bound (hF.comp (continuous_const.add (sOU Q ν η).continuous)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hB _)
  have hcs : Continuous fun y => H0 y + ∑ k, H k y := h0.add (continuous_finset_sum _ fun k _ => hc k)
  rw [who_ouSg_eq Q ν η hcs x, who_ouSg_eq Q ν η h0 x]
  simp only [who_ouSg_eq Q ν η (hc _) x]
  rw [← integral_finsetSum _ (fun k _ => hint (hc k) (hb k)), ← integral_add (hint h0 hb0)
    (integrable_finset_sum _ fun k _ => hint (hc k) (hb k))]

/-- **weighted bound of the smoothed perturbation** -/
theorem who_Wpert (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (ψ : SchwartzMap (Euc d) ℝ) {c : Euc d → Euc d} (hc : IsSmoothBounded c) {P : ℝ}
    (hP : (d : ℝ) / 2 < P) (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η ∈ Set.Ioc (0 : ℝ) T, ∀ {φ : Euc d → ℝ}, CbCls (r + 3) φ → ∀ {i : ℕ}, i ≤ r →
      wSq P (fun x => ‖iteratedFDeriv ℝ i (ouSg Q ν η (ulPert s M ψ c φ)) x‖) ≤
        ENNReal.ofReal (C * (1 + η⁻¹)) * Nsq r P φ := by
  have hP0 : 0 ≤ P := by linarith [show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity]
  obtain ⟨CG, hCG0, hG⟩ := who_G_main hd hs0 hs1 M ψ hc hP r
  obtain ⟨C1, hC10, hW1⟩ := who_W1 hP0 Q hν T r
  obtain ⟨C2, hC20, hW2⟩ := who_W2 hP0 Q hν T r
  refine ⟨2 * (C1 * CG + d * d * C2 * CG), by positivity, fun η hη φ hφ i hi => ?_⟩
  have hη0 : 0 < η := hη.1
  have hφ2 : CbCls (r + 2) φ := who_cb_mono (by omega) hφ
  obtain ⟨hGk, hG0, hwGk, hwG0⟩ := hG hφ2
  have hφ3 : CbCls 3 φ := who_cb_mono (by omega) hφ
  -- the splitting
  have hsplit : ulPert s M ψ c φ = fun y => G0 s M ψ c φ y + ∑ k, fderiv ℝ (Gk s M ψ c k φ) y (EuclideanSpace.single k 1) := by
    funext y
    rw [who_decomp hd hs0 (by linarith) M ψ hc hφ3 y]; ring
  have hdir : ∀ k, CbCls r (fun y => fderiv ℝ (Gk s M ψ c k φ) y (EuclideanSpace.single k 1)) :=
    fun k => who_dir_cb (hGk k) _
  have hbdd : ∀ {F : Euc d → ℝ}, CbCls r F → ∃ B, ∀ y, |F y| ≤ B := by
    intro F ⟨_, B, hB⟩
    exact ⟨B, fun y => by simpa using hB 0 (Nat.zero_le _) y⟩
  have hlin : ouSg Q ν η (ulPert s M ψ c φ) = fun x => ouSg Q ν η (G0 s M ψ c φ) x +
      ∑ k, (1 : ℝ) * ouSg Q ν η (fun y => fderiv ℝ (Gk s M ψ c k φ) y (EuclideanSpace.single k 1)) x := by
    funext x
    rw [hsplit]
    simp only [one_mul]
    exact who_ouSg_lin Q ν η hG0.1.continuous (hbdd hG0) (fun k => (hdir k).1.continuous)
      (fun k => hbdd (hdir k)) x
  -- smoothness of the pieces
  have hsm0 : ContDiff ℝ r (ouSg Q ν η (G0 s M ψ c φ)) := by
    obtain ⟨hc0, B, hB⟩ := hG0
    have hfun : ouSg Q ν η (G0 s M ψ c φ) = fun x => ∫ w, (fun _ : Euc d => (1 : ℝ)) w *
        G0 s M ψ c φ (ouExp Q η x + sOU Q ν η w) ∂(stdGaussian (Euc d)) := by
      funext x; rw [who_ouSg_eq Q ν η hc0.continuous x]; simp
    rw [hfun]
    exact (who_gav_smooth (ouExp Q η) (sOU Q ν η) hc0 hB continuous_const (integrable_const _)).1
  have hsmk : ∀ k, ContDiff ℝ r (ouSg Q ν η (fun y => fderiv ℝ (Gk s M ψ c k φ) y (EuclideanSpace.single k 1))) := by
    intro k
    obtain ⟨hc0, B, hB⟩ := hdir k
    have hfun : ouSg Q ν η (fun y => fderiv ℝ (Gk s M ψ c k φ) y (EuclideanSpace.single k 1)) =
        fun x => ∫ w, (fun _ : Euc d => (1 : ℝ)) w *
          (fun y => fderiv ℝ (Gk s M ψ c k φ) y (EuclideanSpace.single k 1)) (ouExp Q η x + sOU Q ν η w)
          ∂(stdGaussian (Euc d)) := by
      funext x; rw [who_ouSg_eq Q ν η hc0.continuous x]; simp
    rw [hfun]
    exact (who_gav_smooth (ouExp Q η) (sOU Q ν η) hc0 hB continuous_const (integrable_const _)).1
  rw [hlin]
  refine (who_wSq_lin (P := P) (n := r) (i := i) hi hsm0 hsmk (fun _ => 1)).trans ?_
  -- bounds of the pieces
  have h0 : wSq P (fun x => ‖iteratedFDeriv ℝ i (ouSg Q ν η (G0 s M ψ c φ)) x‖) ≤
      ENNReal.ofReal (C1 * CG) * Nsq r P φ := by
    obtain ⟨hc0, B, hB⟩ := hG0
    refine (hW1 η ⟨hη.1.le, hη.2⟩ hi (hc0.of_le (by exact_mod_cast hi)) ⟨B, fun l hl => hB l (by omega)⟩).trans ?_
    rw [ENNReal.ofReal_mul hC10, mul_assoc]
    exact mul_le_mul' le_rfl (hwG0 hi)
  have hk : ∀ k : Fin d, wSq P (fun x => ‖iteratedFDeriv ℝ i
      (ouSg Q ν η (fun y => fderiv ℝ (Gk s M ψ c k φ) y (EuclideanSpace.single k 1))) x‖) ≤
      ENNReal.ofReal (C2 * η⁻¹ * CG) * Nsq r P φ := by
    intro k
    obtain ⟨hc0, B, hB⟩ := hGk k
    refine (hW2 η hη k hi hc0 ⟨B, hB⟩).trans ?_
    calc ENNReal.ofReal (C2 * η⁻¹) * wSq P (fun y => ‖iteratedFDeriv ℝ i (Gk s M ψ c k φ) y‖)
        ≤ ENNReal.ofReal (C2 * η⁻¹) * (ENNReal.ofReal CG * Nsq r P φ) := mul_le_mul' le_rfl (hwGk k hi)
      _ = ENNReal.ofReal (C2 * η⁻¹ * CG) * Nsq r P φ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hηi : 0 ≤ η⁻¹ := inv_nonneg.2 hη0.le
  calc 2 * (wSq P (fun x => ‖iteratedFDeriv ℝ i (ouSg Q ν η (G0 s M ψ c φ)) x‖) +
        (d : ℝ≥0∞) * ∑ k, ENNReal.ofReal ((1 : ℝ) ^ 2) * wSq P (fun x => ‖iteratedFDeriv ℝ i
          (ouSg Q ν η (fun y => fderiv ℝ (Gk s M ψ c k φ) y (EuclideanSpace.single k 1))) x‖))
      ≤ 2 * (ENNReal.ofReal (C1 * CG) * Nsq r P φ + (d : ℝ≥0∞) * ∑ k : Fin d, ENNReal.ofReal ((1 : ℝ) ^ 2) *
          (ENNReal.ofReal (C2 * η⁻¹ * CG) * Nsq r P φ)) := by
        gcongr with k
        exact hk k
    _ = ENNReal.ofReal (2 * (C1 * CG + d * ∑ k : Fin d, (1 : ℝ) ^ 2 * (C2 * η⁻¹ * CG))) * Nsq r P φ :=
        who_comb_bound (mul_nonneg hC10 hCG0) (fun _ => C2 * η⁻¹ * CG)
          (fun _ => by positivity) (fun _ => 1) _
    _ ≤ ENNReal.ofReal (2 * (C1 * CG + d * d * C2 * CG) * (1 + η⁻¹)) * Nsq r P φ := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        simp only [one_pow, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 : 0 ≤ C1 * CG := mul_nonneg hC10 hCG0
        have h2 : 0 ≤ (d : ℝ) * d * C2 * CG := by positivity
        nlinarith [mul_nonneg h2 hηi, mul_nonneg h1 hηi]

end HRS.MS.Who
