import HRS.Commutator.Torus.TKRAux8

/-!
# T-KR helpers, part 9: far-field decay of `∇g_{>}` (summation by parts on `ℤ^d`)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad HRS.PDE.Kern

variable {d : ℕ} {s η : ℝ}

lemma tkr_mode_zero (k : Lattice d) : Torus.mode k (0 : Torus d) = 1 := by
  have h0 : (0 : Torus d) = Torus.mk 0 := by funext i; simp [Torus.mk]
  rw [h0, Torus.mode_mk]
  simp [Lattice.dot]

lemma tkr_mode_eI_sub_one_le (j : Fin d) (x : Torus d) :
    ‖Torus.mode (eI j) x - 1‖ ≤ 2 * Real.pi * ‖x‖ := by
  have hm := Torus.mode_mk (eI j) (centeredRep x)
  rw [mk_centeredRep] at hm
  rw [hm]
  have hdot : Lattice.dot (eI j) (centeredRep x) = centeredRep x j := by
    simp [Lattice.dot, eI, Pi.single_apply]
  rw [hdot]
  have h1 : Complex.exp (((2 * Real.pi * centeredRep x j : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((2 * Real.pi * centeredRep x j : ℝ) : ℂ)) := by rw [mul_comm]
  rw [h1]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  have h2 : |centeredRep x j| = ‖x j‖ := (norm_apply_eq x j).symm
  have h3 : ‖x j‖ ≤ ‖x‖ := norm_le_pi_norm x j
  rw [h2]
  have : (|(2 : ℝ)|) = 2 := abs_two
  rw [this]
  nlinarith [Real.pi_pos, norm_nonneg (x j)]

lemma tkr_G_continuousAt (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {x : Torus d} (hx : x ≠ 0) :
    ContinuousAt (periodicRieszGrad d s : Torus d → Euc d) x := by
  have hsm := periodicRieszGrad_smoothOffZero hd hs0 hsd
  have hy : Torus.mk (centeredRep x) = x := mk_centeredRep x
  have hmem : centeredRep x ∈ {y : Euc d | Torus.mk y ≠ 0} := by
    simpa [hy] using hx
  have h1 : ContinuousAt (Torus.lift (periodicRieszGrad d s)) (centeredRep x) :=
    (hsm.continuousOn.continuousAt (((isOpen_compl_singleton (x := (0 : Torus d))).preimage Torus.continuous_mk).mem_nhds hmem))
  have h2 := (isOpenQuotientMap_mk (d := d)).continuousAt_comp_iff
    (g := (periodicRieszGrad d s : Torus d → Euc d)) (x := centeredRep x)
  rw [hy] at h2
  exact h2.1 h1

lemma tkr_far_comp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (N : ℕ)
    (hN : s + 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (i j : Fin d) (x : Torus d),
      ‖Torus.mode (eI j) x - 1‖ ^ N * |ghiForceT s η x i| ≤ K * η ^ ((N : ℝ) - (s + 1)) := by
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by linarith
  have hp : 1 ≤ (N : ℝ) - (s + 1) := by linarith
  obtain ⟨K0, hK0, hK⟩ := tkr_dls_sum (d := d) (by omega) s N hp
  obtain ⟨K1, hK10, hK1⟩ := tkr_ghi_near hd2 hs0 hsd1
  refine ⟨‖((2 * Real.pi * HDB.kapC d s : ℝ) : ℂ) * Complex.I‖ * K0, by positivity,
    fun η hη hη1 i j x => ?_⟩
  have hN1 : N ≠ 0 := by
    intro h; subst h; simp at hN; linarith
  set a0 : ℂ := ((2 * Real.pi * HDB.kapC d s : ℝ) : ℂ) * Complex.I with ha0
  set g : Torus d → ℂ := fun x => ((ghiForceT s η x i : ℝ) : ℂ) with hg
  have hF : Integrable g := tkr_ghi_integrable hd2 hs0 hsd1 hη i
  set U : Torus d → ℂ := fun x => (Torus.mode (eI j) x - 1) ^ N * g x with hU
  have hcoef : ∀ k : Lattice d, ∫ x : Torus d, Torus.mode (-k) x * U x =
      a0 * Dls (List.replicate N j) (tkrCG d s η i) k := by
    intro k
    simp only [hU]
    rw [tkr_coef_mulJ_pow hF j N k]
    have : (fun l : Lattice d => ∫ x : Torus d, Torus.mode (-l) x * g x) =
        fun l => a0 * tkrCG d s η i l := by
      funext l
      simp only [hg]
      rw [tkr_ghi_coef hd2 hs0 hsd1 hη i l, tkr_coef_eq (by linarith : s < d) hη hη1 i l]
    rw [this, tkr_Dls_smul]
  -- continuity of `U`
  have hGc : ∀ y : Torus d, y ≠ 0 → ContinuousAt (fun z : Torus d => ghiForceT s η z i) y := by
    intro y hy
    have h1 := tkr_G_continuousAt hd2 hs0 (by linarith : s < d) hy
    have h2 : Continuous fun z : Torus d => PleqT η (periodicRieszGrad d s) z i :=
      tkr_glo_continuous hd2 hs0 hsd1 hη i
    have h3 : ContinuousAt (fun z : Torus d => periodicRieszGrad d s z i) y :=
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.continuousAt.comp h1
    exact h3.sub h2.continuousAt
  have hUc : Continuous U := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y = 0
    · subst hy
      have hU0 : U 0 = 0 := by
        simp only [hU]
        rw [tkr_mode_zero, sub_self, zero_pow hN1, zero_mul]
      rw [ContinuousAt, hU0]
      set c : ℝ := (2 * Real.pi) ^ N * K1 with hc
      set B : Torus d → ℝ := fun z => c * (‖z‖ ^ ((N : ℝ) - (s + 1)) +
        η ^ (-(s + 1)) * ‖z‖ ^ (N : ℝ)) with hB
      have hBc : Continuous B := by
        refine continuous_const.mul ((Real.continuous_rpow_const (by linarith)).comp continuous_norm
          |>.add (continuous_const.mul ((Real.continuous_rpow_const (by positivity)).comp continuous_norm)))
      have hB0 : B 0 = 0 := by
        simp only [hB, norm_zero]
        rw [Real.zero_rpow (by linarith), Real.zero_rpow (by exact_mod_cast hN1)]
        simp
      refine squeeze_zero_norm (a := B) (fun z => ?_) (by simpa [hB0] using hBc.tendsto 0)
      by_cases hz : z = 0
      · subst hz; rw [hU0, norm_zero, hB0]
      · have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
        have h1 : ‖U z‖ = ‖Torus.mode (eI j) z - 1‖ ^ N * |ghiForceT s η z i| := by
          simp only [hU, hg]
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        rw [h1]
        have h2 : |ghiForceT s η z i| ≤ ‖ghiForceT s η z‖ := by
          simpa using PiLp.norm_apply_le (ghiForceT s η z) i
        have h3 := hK1 η hη hη1 z hz
        have h4 : KernelGrad.tdist z 0 ^ (-s - 1) ≤ ‖z‖ ^ (-s - 1) :=
          Real.rpow_le_rpow_of_nonpos hzn (norm_le_tdist z) (by linarith)
        have h5 := tkr_mode_eI_sub_one_le j z
        have h6 : ‖Torus.mode (eI j) z - 1‖ ^ N ≤ (2 * Real.pi * ‖z‖) ^ N :=
          pow_le_pow_left₀ (norm_nonneg _) h5 N
        calc ‖Torus.mode (eI j) z - 1‖ ^ N * |ghiForceT s η z i|
            ≤ (2 * Real.pi * ‖z‖) ^ N * (K1 * (‖z‖ ^ (-s - 1) + η ^ (-(s + 1)))) := by
              refine mul_le_mul h6 (h2.trans (h3.trans ?_)) (abs_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_left (by linarith) hK10
          _ = B z := by
              simp only [hB, hc]
              have e1 : ‖z‖ ^ N * ‖z‖ ^ (-s - 1) = ‖z‖ ^ ((N : ℝ) - (s + 1)) := by
                rw [← Real.rpow_natCast, ← Real.rpow_add hzn]; congr 1; ring
              have e2 : ‖z‖ ^ N = ‖z‖ ^ (N : ℝ) := (Real.rpow_natCast _ _).symm
              rw [mul_pow, ← e2]
              rw [← e1]
              ring
    · have := hGc y hy
      have h1 : ContinuousAt (fun z : Torus d => g z) y :=
        Complex.continuous_ofReal.continuousAt.comp this
      have h2 : Continuous fun z : Torus d => (Torus.mode (eI j) z - 1) ^ N :=
        ((Torus.continuous_mode _).sub continuous_const).pow N
      exact h2.continuousAt.mul h1
  -- Fourier series of `U`
  have hnorm : ∀ k : Lattice d, ‖∫ x : Torus d, Torus.mode (-k) x * U x‖ =
      ‖a0‖ * ‖Dls (List.replicate N j) (tkrCG d s η i) k‖ := by
    intro k; rw [hcoef k, norm_mul]
  obtain ⟨hsumm, htsum⟩ := hK η hη hη1 i j
  have hsum : Summable fun k : Lattice d => ‖∫ x : Torus d, Torus.mode (-k) x * U x‖ := by
    simp_rw [hnorm]; exact hsumm.mul_left _
  have hser := tkr_series hUc hsum x
  have hsum2 : Summable fun k : Lattice d => ‖(∫ x : Torus d, Torus.mode (-k) x * U x) * Torus.mode k x‖ := by
    simp_rw [norm_mul, Torus.norm_mode, mul_one]; exact hsum
  have hb : ‖U x‖ ≤ ‖a0‖ * (K0 * η ^ ((N : ℝ) - (s + 1))) := by
    rw [← hser.tsum_eq]
    refine (norm_tsum_le_tsum_norm hsum2).trans ?_
    simp_rw [norm_mul, Torus.norm_mode, mul_one, hnorm]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left htsum (norm_nonneg _)
  have h1 : ‖U x‖ = ‖Torus.mode (eI j) x - 1‖ ^ N * |ghiForceT s η x i| := by
    simp only [hU, hg]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [h1] at hb
  calc _ ≤ _ := hb
    _ = _ := by ring

theorem tkr_ghi_far (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (N : ℕ) (hN : s + 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 ^ N * ‖ghiForceT s η x‖ ≤ K * η ^ ((N : ℝ) - (s + 1)) := by
  obtain ⟨K, hK0, hK⟩ := tkr_far_comp hd hs0 hsd N hN
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  refine ⟨d * (d / 4) ^ N * K, by positivity, fun η hη hη1 x hx => ?_⟩
  set r := KernelGrad.tdist x 0 with hr
  have hr0 : 0 < r := tdist_pos hx
  obtain ⟨j, hj⟩ := HDB.exists_qf_ge (by omega : 1 ≤ d) x
  have hj' : (4 * r / d) ≤ ‖Torus.mode (eI j) x - 1‖ := by
    have h1 : (4 * r / d) ^ 2 ≤ ‖Torus.mode (eI j) x - 1‖ ^ 2 := by
      have : (4 * r / d) ^ 2 ≤ 16 * r ^ 2 / d := by
        rw [div_pow, mul_pow]
        norm_num
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg r) (by positivity : (0:ℝ) ≤ d)) (sub_nonneg.2 hd0)]
      exact this.trans hj
    exact (abs_le_of_sq_le_sq' h1 (norm_nonneg _)).2
  have hcomp : ∀ i : Fin d, (4 * r / d) ^ N * |ghiForceT s η x i| ≤ K * η ^ ((N : ℝ) - (s + 1)) := by
    intro i
    refine le_trans ?_ (hK η hη hη1 i j x)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hj' N) (abs_nonneg _)
  have hnorm := tkr_norm_le_sum (ghiForceT s η x)
  have hsum : (4 * r / d) ^ N * ‖ghiForceT s η x‖ ≤ d * (K * η ^ ((N : ℝ) - (s + 1))) := by
    calc (4 * r / d) ^ N * ‖ghiForceT s η x‖ ≤ (4 * r / d) ^ N * ∑ i, |ghiForceT s η x i| :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = ∑ i, (4 * r / d) ^ N * |ghiForceT s η x i| := by rw [Finset.mul_sum]
      _ ≤ ∑ _i : Fin d, K * η ^ ((N : ℝ) - (s + 1)) := Finset.sum_le_sum fun i _ => hcomp i
      _ = _ := by simp
  have hq : (4 * r / d) ^ N = (4 / d) ^ N * r ^ N := by rw [← mul_pow]; congr 1; ring
  have hpos : 0 < (4 / (d : ℝ)) ^ N := by positivity
  have : (4 / (d : ℝ)) ^ N * (r ^ N * ‖ghiForceT s η x‖) ≤ (4 / (d : ℝ)) ^ N *
      (d * (d / 4) ^ N * K * η ^ ((N : ℝ) - (s + 1))) := by
    calc (4 / (d : ℝ)) ^ N * (r ^ N * ‖ghiForceT s η x‖) = (4 * r / d) ^ N * ‖ghiForceT s η x‖ := by
          rw [hq]; ring
      _ ≤ d * (K * η ^ ((N : ℝ) - (s + 1))) := hsum
      _ = (4 / (d : ℝ)) ^ N * (d * (d / 4) ^ N * K * η ^ ((N : ℝ) - (s + 1))) := by
          have : (4 / (d : ℝ)) ^ N * (d / 4) ^ N = 1 := by
            rw [← mul_pow]; field_simp; simp
          calc (d : ℝ) * (K * η ^ ((N : ℝ) - (s + 1))) = d * K * η ^ ((N : ℝ) - (s + 1)) * 1 := by ring
            _ = d * K * η ^ ((N : ℝ) - (s + 1)) * ((4 / (d : ℝ)) ^ N * (d / 4) ^ N) := by rw [this]
            _ = _ := by ring
  exact le_of_mul_le_mul_left this hpos

end HRS.Commutator.TorusNote
