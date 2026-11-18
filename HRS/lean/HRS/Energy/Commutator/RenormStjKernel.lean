import HRS.Energy.Commutator.RenormStjProfile

/-!
# Route S, packet STJ: kernel-side `l`-integral bounds for the Stieltjes slices
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.Stj

section PsiAbs

open HRS HRS.KernelAux HRS.KernelGrad
open scoped Real

variable {d : ℕ}

/-- Copy of `SliceAux.psiG_abs_bound` with the hypothesis `0 ≤ s` weakened to `-2 < s` (needed for `s = d - 2 = -1`, `d = 1`). -/
theorem stj_psiG_abs_bound {s : ℝ} (hs0 : -2 < s) (hsd : s < d) (j : Fin d) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ y : Euc d, (∀ i, |y i| ≤ 1 / 2) → y ≠ 0 →
      IntegrableOn (fun t : ℝ => t ^ (((d : ℝ) - s) / 2 - 1) * |psiG j (Torus.mk y) t|) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), t ^ (((d : ℝ) - s) / 2 - 1) * |psiG j (Torus.mk y) t| ≤
        C1 * ‖y‖ ^ (-s - 1) + C2 := by
  obtain ⟨K, hK0, hK⟩ := psiG_small_bound (d := d) j
  obtain ⟨M1, hM10, hM1⟩ := psiG_large_bound (d := d) j
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set n : ℝ := (d:ℝ) / 2 + 1 with hn_def
  have hn : 0 < n := by rw [hn_def]; positivity
  have han : a < n := by rw [ha_def, hn_def]; linarith
  set c : ℝ := n ^ n * Real.exp (-n) with hc_def
  have hc0 : 0 ≤ c := by positivity
  set P : ℝ := 2 * π ^ 2 * Real.sqrt π ^ d with hP
  have hP0 : 0 ≤ P := by positivity
  set C0 : ℝ := ∫ v in Ioi (0:ℝ), v ^ (a - 1) * min c (v ^ (-n)) with hC0
  have hC00 : 0 ≤ C0 := by
    refine setIntegral_nonneg measurableSet_Ioi fun v hv => ?_
    have hv0 : (0:ℝ) < v := hv
    have := le_min hc0 (Real.rpow_nonneg hv0.le (-n))
    have := Real.rpow_pos_of_pos hv0 (a - 1)
    positivity
  set θ2 : ℝ := π ^ 2 / 8 with hθ2
  have hθ2p : 0 < θ2 := by positivity
  refine ⟨P * C0 * π ^ (-(s + 2)), P * K * (θ2 ^ (a - n) * C0) + M1 * Real.Gamma a,
    by positivity, by have := (Real.Gamma_pos_of_pos ha).le; positivity,
    fun y hy hy0 => ?_⟩
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  set θ1 : ℝ := π ^ 2 * ‖y‖ ^ 2 with hθ1
  have hθ1p : 0 < θ1 := by positivity
  set m1 : ℝ → ℝ := fun u => min (c * θ1 ^ (-n)) (u ^ (-n)) with hm1
  set m2 : ℝ → ℝ := fun u => min (c * θ2 ^ (-n)) (u ^ (-n)) with hm2
  set Bm : ℝ → ℝ := fun t => P * ‖y‖ * m1 t + P * K * m2 t + M1 * Real.exp (-t) with hBm
  -- antitone majorants
  have hmono : ∀ (X : ℝ) {t u : ℝ}, 0 < t → t ≤ u → min X (u ^ (-n)) ≤ min X (t ^ (-n)) := by
    intro X t u ht htu
    exact min_le_min_left _ (Real.rpow_le_rpow_of_nonpos ht htu (by linarith))
  have hexpmin : ∀ (θ : ℝ), 0 < θ → ∀ u : ℝ, 0 < u →
      u ^ (-n) * Real.exp (-θ / u) ≤ min (c * θ ^ (-n)) (u ^ (-n)) := by
    intro θ hθ u hu
    refine le_min (t_pow_exp_bound hn hθ hu) ?_
    have : Real.exp (-θ / u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ θ / u := by positivity
      rw [neg_div]; linarith
    have hp := Real.rpow_nonneg hu.le (-n)
    nlinarith
  have hpsi : ∀ u : ℝ, 0 < u → |psiG j (Torus.mk y) u| ≤ Bm u := by
    intro u hu
    have h1 : 0 ≤ P * ‖y‖ * m1 u := by
      have := le_min (mul_nonneg hc0 (Real.rpow_nonneg hθ1p.le (-n))) (Real.rpow_nonneg hu.le (-n))
      positivity
    have h2 : 0 ≤ P * K * m2 u := by
      have := le_min (mul_nonneg hc0 (Real.rpow_nonneg hθ2p.le (-n))) (Real.rpow_nonneg hu.le (-n))
      positivity
    have h3 : 0 ≤ M1 * Real.exp (-u) := by positivity
    rcases le_or_gt u 1 with hu1 | hu1
    · have h := hK y hy u hu hu1
      have hpow : Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) = P * u ^ (-n) := by
        rw [sqrt_div_pow_eq d hu, hP, div_eq_mul_inv (2 * π ^ 2), ← Real.rpow_neg_one u,
          hn_def]
        have : Real.sqrt π ^ d * u ^ (-(d:ℝ)/2) * (2 * π ^ 2 * u ^ (-1:ℝ)) =
            2 * π ^ 2 * Real.sqrt π ^ d * (u ^ (-(d:ℝ)/2) * u ^ (-1:ℝ)) := by ring
        rw [this, ← Real.rpow_add hu]
        congr 2; ring
      have e1 : Real.exp (-(π ^ 2 * ‖y‖ ^ 2 / u)) = Real.exp (-θ1 / u) := by rw [hθ1, neg_div]
      have e2 : Real.exp (-(π ^ 2 / (8 * u))) = Real.exp (-θ2 / u) := by
        rw [hθ2]; congr 1; field_simp
      rw [hpow, e1, e2] at h
      refine h.trans ?_
      have k1 := hexpmin θ1 hθ1p u hu
      have k2 := hexpmin θ2 hθ2p u hu
      have : P * u ^ (-n) * (‖y‖ * Real.exp (-θ1 / u) + K * Real.exp (-θ2 / u)) =
          P * ‖y‖ * (u ^ (-n) * Real.exp (-θ1 / u)) + P * K * (u ^ (-n) * Real.exp (-θ2 / u)) := by ring
      rw [this]
      simp only [hBm]
      have := mul_le_mul_of_nonneg_left k1 (mul_nonneg hP0 hr.le)
      have := mul_le_mul_of_nonneg_left k2 (mul_nonneg hP0 hK0)
      simp only [hm1, hm2]
      linarith
    · have h := hM1 (Torus.mk y) u hu1.le
      refine h.trans ?_
      simp only [hBm]
      linarith [mul_comm M1 (Real.exp (-u))]
  -- integrals
  obtain ⟨hi1, hv1⟩ := integral_min_rpow ha han hc0 hθ1p
  obtain ⟨hi2, hv2⟩ := integral_min_rpow ha han hc0 hθ2p
  have hGi := Real.GammaIntegral_convergent ha
  have heq : ∀ t : ℝ, t ^ (a - 1) * Bm t = P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n))) +
      P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n))) +
      M1 * (Real.exp (-t) * t ^ (a - 1)) := by
    intro t; simp only [hBm, hm1, hm2]; ring
  have hBi : IntegrableOn (fun t => t ^ (a - 1) * Bm t) (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ => P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n))) +
      P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n))) +
      M1 * (Real.exp (-t) * t ^ (a - 1))) (Ioi 0) :=
      ((hi1.const_mul _).add (hi2.const_mul _)).add (hGi.const_mul _)
    exact h.congr_fun (fun t _ => (heq t).symm) measurableSet_Ioi
  have hBint : ∫ t in Ioi (0:ℝ), t ^ (a - 1) * Bm t =
      P * ‖y‖ * (θ1 ^ (a - n) * C0) + P * K * (θ2 ^ (a - n) * C0) + M1 * Real.Gamma a := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => heq t)]
    have f1 : IntegrableOn (fun t : ℝ => P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n)))) (Ioi 0) :=
      hi1.const_mul _
    have f2 : IntegrableOn (fun t : ℝ => P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n)))) (Ioi 0) :=
      hi2.const_mul _
    have f3 : IntegrableOn (fun t : ℝ => M1 * (Real.exp (-t) * t ^ (a - 1))) (Ioi 0) := hGi.const_mul _
    have f12 : IntegrableOn (fun t : ℝ => P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n))) +
        P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n)))) (Ioi 0) := f1.add f2
    rw [integral_add f12 f3, integral_add f1 f2, integral_const_mul, integral_const_mul,
      integral_const_mul, hv1, hv2, ← Real.Gamma_eq_integral ha]
  have hpsiI : IntegrableOn (fun t : ℝ => t ^ (a - 1) * |psiG j (Torus.mk y) t|) (Ioi 0) := by
    refine Integrable.mono' hBi ?_ ?_
    · exact (ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht))
        (psiG_continuousOn j _).abs).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have ht0 : (0:ℝ) < t := ht
      have hp := Real.rpow_pos_of_pos ht0 (a - 1)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hpsi t ht0) hp.le
  have hθ1pow : ‖y‖ * θ1 ^ (a - n) = π ^ (-(s + 2)) * ‖y‖ ^ (-s - 1) := by
    have hexp : a - n = -(s / 2 + 1) := by rw [ha_def, hn_def]; ring
    rw [hexp, hθ1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_mul hr.le]
    have e3 : ‖y‖ * (π ^ ((2:ℕ) * -(s / 2 + 1) : ℝ) * ‖y‖ ^ ((2:ℕ) * -(s / 2 + 1) : ℝ)) =
        π ^ ((2:ℕ) * -(s / 2 + 1) : ℝ) * (‖y‖ ^ (1:ℝ) * ‖y‖ ^ ((2:ℕ) * -(s / 2 + 1) : ℝ)) := by
      rw [Real.rpow_one]; ring
    rw [e3, ← Real.rpow_add hr]
    congr 2 <;> push_cast <;> ring
  refine ⟨hpsiI, ?_⟩
  have hle : ∫ t in Ioi (0:ℝ), t ^ (a - 1) * |psiG j (Torus.mk y) t| ≤
      ∫ t in Ioi (0:ℝ), t ^ (a - 1) * Bm t := by
    refine setIntegral_mono_on hpsiI hBi measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := ht
    have hp := Real.rpow_pos_of_pos ht0 (a - 1)
    exact mul_le_mul_of_nonneg_left (hpsi t ht0) hp.le
  refine hle.trans ?_
  rw [hBint]
  have e : P * ‖y‖ * (θ1 ^ (a - n) * C0) = P * C0 * (π ^ (-(s + 2)) * ‖y‖ ^ (-s - 1)) := by
    rw [← hθ1pow]; ring
  linarith [e]


end PsiAbs

section Unif

variable {d : ℕ}

/-- **Uniform-in-`l` bound of the slice force**: `|∂_j 𝒢_l(z)| ≤ K (|z|^{1-d} + 1)` for all `l ≥ 0`. -/
theorem sgc_unif_bound (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : Fin d) (l : ℝ), 0 ≤ l → ∀ z : Torus d, z ≠ 0 →
    |SliceAux.sgc j l z| ≤ K * (KernelGrad.tdist z 0 ^ (1 - (d : ℝ)) + 1) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hs2 : -2 < (d : ℝ) - 2 := by linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  choose C1 C2 hC1 hC2 hC using fun j : Fin d => stj_psiG_abs_bound hs2 hsd j
  set Cs : ℝ := ∑ j, (C1 j + C2 j) with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun j _ => add_nonneg (hC1 j) (hC2 j)
  have hb : 0 < 4 * Real.pi ^ 2 := by positivity
  refine ⟨Cs / (4 * Real.pi ^ 2), by positivity, fun j l hl z hz => ?_⟩
  obtain ⟨y, rfl, hy⟩ := KernelGrad.exists_mk_box z
  have hy0 : y ≠ 0 := SliceAux.mk_ne_zero_ne_zero hz
  obtain ⟨hI, hJ⟩ := hC j y hy hy0
  have e0 : ((d : ℝ) - ((d : ℝ) - 2)) / 2 - 1 = 0 := by ring
  simp only [e0, Real.rpow_zero, one_mul] at hI hJ
  set H : ℝ → ℝ := fun u => |HRS.KernelAux.psiG j (Torus.mk y) u| with hH
  have hI' : IntegrableOn (fun t : ℝ => H (4 * Real.pi ^ 2 * t)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff H 0 hb).mpr (by simpa using hI)
    simpa using this
  have hscale : ∫ t in Ioi (0 : ℝ), H (4 * Real.pi ^ 2 * t) = (4 * Real.pi ^ 2)⁻¹ * ∫ u in Ioi (0 : ℝ), H u := by
    have := integral_comp_mul_left_Ioi H 0 hb
    simpa using this
  have h1 : |SliceAux.sgc j l (Torus.mk y)| ≤ ∫ t in Ioi (0 : ℝ), H (4 * Real.pi ^ 2 * t) := by
    refine (SliceAux.abs_sgc_le j (Torus.mk y)).trans ?_
    refine setIntegral_mono_on ?_ hI' measurableSet_Ioi fun t ht => ?_
    · -- integrability of the left side
      refine Integrable.mono' hI' ?_ ?_
      · have h2 : Measurable fun t : ℝ => HRS.KernelAux.psiG j (Torus.mk y) (4 * Real.pi ^ 2 * t) :=
          (SliceAux.measurable_psiG_uncurry j).comp (measurable_const.prodMk (measurable_const.mul measurable_id))
        exact ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul h2.abs).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
        have ht' : (0 : ℝ) < t := ht
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
        have : Real.exp (-l * t) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
        simp only [hH]
        nlinarith [abs_nonneg (HRS.KernelAux.psiG j (Torus.mk y) (4 * Real.pi ^ 2 * t))]
    · have ht' : (0 : ℝ) < t := ht
      have : Real.exp (-l * t) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
      simp only [hH]
      nlinarith [abs_nonneg (HRS.KernelAux.psiG j (Torus.mk y) (4 * Real.pi ^ 2 * t))]
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have h2 : ∫ u in Ioi (0 : ℝ), H u ≤ Cs * (‖y‖ ^ (1 - (d : ℝ)) + 1) := by
    have e1 : (-((d : ℝ) - 2) - 1) = 1 - (d : ℝ) := by ring
    rw [e1] at hJ
    have hC1' : C1 j ≤ Cs := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => C1 j + C2 j)
        (fun i _ => add_nonneg (hC1 i) (hC2 i)) (Finset.mem_univ j))
      linarith [hC2 j]
    have hC2' : C2 j ≤ Cs := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => C1 j + C2 j)
        (fun i _ => add_nonneg (hC1 i) (hC2 i)) (Finset.mem_univ j))
      linarith [hC1 j]
    have hp : 0 ≤ ‖y‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg hr.le _
    refine hJ.trans ?_
    nlinarith [mul_le_mul_of_nonneg_right hC1' hp, hC2', hC1 j, hC2 j]
  rw [KernelGrad.tdist_mk hy]
  calc |SliceAux.sgc j l (Torus.mk y)| ≤ ∫ t in Ioi (0 : ℝ), H (4 * Real.pi ^ 2 * t) := h1
    _ = (4 * Real.pi ^ 2)⁻¹ * ∫ u in Ioi (0 : ℝ), H u := hscale
    _ ≤ (4 * Real.pi ^ 2)⁻¹ * (Cs * (‖y‖ ^ (1 - (d : ℝ)) + 1)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Cs / (4 * Real.pi ^ 2) * (‖y‖ ^ (1 - (d : ℝ)) + 1) := by ring

theorem sgv_unif_bound (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (l : ℝ), 0 ≤ l → ∀ z : Torus d, z ≠ 0 →
    ‖SliceAux.sgv l z‖ ≤ K * (KernelGrad.tdist z 0 ^ (1 - (d : ℝ)) + 1) := by
  obtain ⟨K, hK0, hK⟩ := sgc_unif_bound hd
  refine ⟨d * K, by positivity, fun l hl z hz => ?_⟩
  refine (SliceAux.norm_sgv_le l z).trans ?_
  calc ∑ j, |SliceAux.sgc j l z| ≤ ∑ _j : Fin d, K * (KernelGrad.tdist z 0 ^ (1 - (d : ℝ)) + 1) :=
        Finset.sum_le_sum fun j _ => hK j l hl z hz
    _ = d * K * (KernelGrad.tdist z 0 ^ (1 - (d : ℝ)) + 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### Joint measurability of the slice kernel and a lower bound -/

theorem measurable_sliceG_uncurry (d : ℕ) : Measurable fun p : ℝ × Torus d => sliceG d p.1 p.2 := by
  unfold sliceG
  have hm : Measurable fun q : (ℝ × Torus d) × ℝ =>
      Real.exp (-q.1.1 * q.2) * psiFn q.1.2 (4 * Real.pi ^ 2 * q.2) := by
    refine Measurable.mul (Real.measurable_exp.comp (measurable_fst.fst.neg.mul measurable_snd)) ?_
    exact EnergyAux.measurable_psiFn_uncurry.comp (measurable_fst.snd.prodMk (measurable_const.mul measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

theorem sliceG_lower (d : ℕ) : ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ l : ℝ, 0 < l → ∀ z : Torus d,
    -(min Cm (1 / l)) ≤ sliceG d l z := by
  obtain ⟨K, hK0, hK⟩ := EnergyAux.psiFn_ge_neg_exp d
  have hb : 0 < 4 * Real.pi ^ 2 := by positivity
  refine ⟨K / (4 * Real.pi ^ 2), by positivity, fun l hl z => ?_⟩
  have hmin0 : 0 ≤ min (K / (4 * Real.pi ^ 2)) (1 / l) := le_min (by positivity) (by positivity)
  by_cases hz : z = 0
  · subst hz
    have h1 : 0 ≤ sliceG d l (0 : Torus d) := by
      unfold sliceG
      exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (Real.exp_pos _).le (CoercAux.psi_zero_nonneg (by have : (0 : ℝ) < t := ht; positivity))
    linarith
  · have hI := SliceAux.integrableOn_slice_psi hl.le hz
    refine neg_le.mpr (le_min ?_ ?_)
    · have hE : IntegrableOn (fun t : ℝ => K * Real.exp (-(4 * Real.pi ^ 2 * t))) (Ioi 0) := by
        have := integrableOn_exp_mul_Ioi (a := -(4 * Real.pi ^ 2)) (by linarith) (0 : ℝ)
        have h2 : IntegrableOn (fun t : ℝ => K * Real.exp (-(4 * Real.pi ^ 2) * t)) (Ioi 0) :=
          this.const_mul K
        refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
        simp [neg_mul]
      have hint : ∫ t in Ioi (0 : ℝ), K * Real.exp (-(4 * Real.pi ^ 2 * t)) = K / (4 * Real.pi ^ 2) := by
        rw [integral_const_mul]
        have := integral_exp_mul_Ioi (a := -(4 * Real.pi ^ 2)) (by linarith) (0 : ℝ)
        simp only [neg_mul, mul_zero, Real.exp_zero] at this ⊢
        rw [this]; field_simp
      have hle : ∫ t in Ioi (0 : ℝ), -(K * Real.exp (-(4 * Real.pi ^ 2 * t))) ≤ sliceG d l z := by
        unfold sliceG
        refine setIntegral_mono_on hE.neg hI measurableSet_Ioi fun t ht => ?_
        have ht' : (0 : ℝ) < t := ht
        have h1 := hK z (4 * Real.pi ^ 2 * t) (by positivity)
        have h2 : Real.exp (-l * t) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
        have h3 : 0 ≤ K * Real.exp (-(4 * Real.pi ^ 2 * t)) := by positivity
        have h4 := Real.exp_pos (-l * t)
        nlinarith [mul_le_mul_of_nonneg_left h1 h4.le, mul_le_mul_of_nonneg_right h2 h3]
      rw [integral_neg, hint] at hle
      linarith
    · have hE : IntegrableOn (fun t : ℝ => Real.exp (-l * t)) (Ioi 0) :=
        integrableOn_exp_mul_Ioi (a := -l) (by linarith) (0 : ℝ)
      have hint : ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) = 1 / l := by
        have := integral_exp_mul_Ioi (a := -l) (by linarith) (0 : ℝ)
        simp only [mul_zero, Real.exp_zero] at this
        rw [this]; field_simp
      have hle : ∫ t in Ioi (0 : ℝ), -(Real.exp (-l * t)) ≤ sliceG d l z := by
        unfold sliceG
        refine setIntegral_mono_on hE.neg hI measurableSet_Ioi fun t ht => ?_
        have ht' : (0 : ℝ) < t := ht
        have h1 := EnergyAux.one_add_psiFn_nonneg' z (u := 4 * Real.pi ^ 2 * t) (by positivity)
        nlinarith [mul_nonneg (Real.exp_pos (-l * t)).le h1]
      rw [integral_neg, hint] at hle
      linarith

end Unif

section Upper

variable {d : ℕ}

theorem local_sing_all (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz d s (Torus.mk x) = selfScale d s ‖x‖ + r (Torus.mk x) := by
  rcases Nat.lt_or_ge d 2 with h | h
  · obtain rfl : d = 1 := by omega
    by_cases hs : s = 0
    · subst hs
      obtain ⟨r, δ, hδ, hr, hx⟩ := HRS.periodicLog_local_singularity_d1
      exact ⟨r, δ, hδ, hr, fun x hx' hx0 => by rw [hx x hx' hx0]; simp [selfScale]⟩
    · have hpos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hs1 : s < 1 := by exact_mod_cast hsd
      obtain ⟨r, δ, hδ, hr, hx⟩ := HRS.periodicRiesz_local_singularity_d1 hpos hs1
      exact ⟨r, δ, hδ, hr, fun x hx' hx0 => by rw [hx x hx' hx0]; simp [selfScale, hs]⟩
  · exact Renorm.local_sing_unified h hs0 hsd

theorem euc_le_card_mul_sup (y : Fin d → ℝ) : ‖(WithLp.toLp 2 y : Euc d)‖ ≤ d * ‖y‖ := by
  refine (HRS.KernelAux.norm_toLp_le_sum y).trans ?_
  calc ∑ i, |y i| ≤ ∑ _i : Fin d, ‖y‖ := Finset.sum_le_sum fun i _ => by
        rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y i
    _ = d * ‖y‖ := by simp

theorem periodicRiesz_upper (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Torus d, z ≠ 0 →
      periodicRiesz d s z ≤ selfScale d s (KernelGrad.tdist z 0) + C := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨r, δ, hδ, hr, hloc⟩ := local_sing_all hd hs0 hsd
  have hrc : Continuous (Torus.lift r) :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous
  obtain ⟨R, hR⟩ := (isCompact_closedBall (0 : Euc d) (δ / 2)).exists_bound_of_continuousOn hrc.continuousOn
  obtain ⟨C1, C2, hC1, hC2, hbox⟩ := HRS.CoercAux.periodicRiesz_box_bound_one hd hs0 hsd
  have hsc : ∃ L : ℝ, 0 ≤ L ∧ ∀ t : ℝ, 0 < t → t ≤ d → -L ≤ selfScale d s t := by
    refine ⟨|Real.log d|, abs_nonneg _, fun t ht htd => ?_⟩
    unfold selfScale
    split_ifs with h0
    · have h1 : Real.log t ≤ Real.log d := Real.log_le_log ht htd
      have h2 := le_abs_self (Real.log d)
      linarith
    · have := Real.rpow_nonneg ht.le (-s)
      have := abs_nonneg (Real.log d)
      linarith
  obtain ⟨L, hL0, hL⟩ := hsc
  set e : ℝ := (s + d) / 2 with he
  have he0 : 0 < e := by rw [he]; positivity
  refine ⟨|R| + (C1 * (δ / (2 * d)) ^ (-e) + C2) + L, by positivity, fun z hz => ?_⟩
  have ht : 0 < KernelGrad.tdist z 0 := KernelGrad.tdist_pos hz
  have hsc0 := hL _ ht (SliceAux.tdist_le_dim z)
  by_cases hsm : KernelGrad.tdist z 0 < δ / 2
  · set x' : Euc d := KernelGrad.centeredRep z with hx'
    have hn : ‖x'‖ = KernelGrad.tdist z 0 := EnergyAux.norm_centeredRep_eq z
    have hmk : Torus.mk x' = z := KernelGrad.mk_centeredRep z
    have hx'0 : x' ≠ 0 := by
      intro h; rw [h, norm_zero] at hn; linarith
    have h1 := hloc x' (by rw [hn]; linarith) hx'0
    rw [hmk, hn] at h1
    have h2 : |r z| ≤ |R| := by
      have := hR x' (by simpa [Metric.mem_closedBall, dist_zero_right, hn] using hsm.le)
      have e1 : Torus.lift r x' = r z := by simp [Torus.lift, hmk]
      rw [e1] at this
      exact (Real.norm_eq_abs _ ▸ this).trans (le_abs_self _)
    have h3 := (le_abs_self (r z)).trans h2
    have h4 : 0 ≤ C1 * (δ / (2 * d)) ^ (-e) + C2 := by positivity
    rw [h1]
    linarith
  · push Not at hsm
    set y : Fin d → ℝ := fun i => KernelGrad.centeredRep z i with hy
    have hyB : y ∈ KernelAux.Box d := EnergyAux.centeredRep_mem_box z
    have hbp : KernelAux.boxPt y = z := EnergyAux.boxPt_centeredRep z
    have hyn : ‖(WithLp.toLp 2 y : Euc d)‖ = KernelGrad.tdist z 0 := by
      rw [← EnergyAux.norm_centeredRep_eq z]
    have hy0 : y ≠ 0 := by
      intro h
      have : (WithLp.toLp 2 y : Euc d) = 0 := by rw [h]; rfl
      rw [this, norm_zero] at hyn; linarith
    have hcmp := euc_le_card_mul_sup y
    rw [hyn] at hcmp
    have hsup : δ / (2 * d) ≤ ‖y‖ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hb := hbox y hyB hy0
    rw [hbp] at hb
    have h5 : ‖y‖ ^ (-e) ≤ (δ / (2 * d)) ^ (-e) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hsup (by linarith)
    have h6 : periodicRiesz d s z ≤ C1 * (δ / (2 * d)) ^ (-e) + C2 := by
      have := (le_abs_self _).trans hb
      have h7 : C1 * ‖y‖ ^ (-((s + d) / 2)) ≤ C1 * (δ / (2 * d)) ^ (-e) := by
        rw [← he]; exact mul_le_mul_of_nonneg_left h5 hC1
      linarith
    have h8 := abs_nonneg R
    linarith

theorem sliceG_stieltjes_int (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d)
    {z : Torus d} (hz : z ≠ 0) :
    IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * sliceG d l z) (Ioi 0) := by
  have hβ1 : bexp d s < 1 := by unfold bexp; linarith
  have hi := KernelAux.integrableOn_psi hsd z hz
  have hc := HRS.psi_continuousOn z
  have hb : bexp d s - 1 = ((d : ℝ) - s) / 2 - 1 := rfl
  exact (SliceAux.bridge hβ1 hc (by rwa [hb])).1

theorem Theta_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) {c : ℝ}
    (hc : 0 < c)
    (hker : ∀ x : Torus d, x ≠ 0 →
      periodicRiesz d s x = c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * sliceG d l x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Torus d, z ≠ 0 →
      IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * |sliceG d l z|) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * |sliceG d l z| ≤
        c⁻¹ * selfScale d s (KernelGrad.tdist z 0) + C := by
  have hβ0 : 0 < bexp d s := by unfold bexp; linarith
  have hβ1 : bexp d s < 1 := by unfold bexp; linarith
  obtain ⟨Cm, hCm0, hCm⟩ := sliceG_lower d
  obtain ⟨Cu, hCu0, hCu⟩ := periodicRiesz_upper hd hs0 hsd
  have hT : 0 < Cm + 1 := by linarith
  obtain ⟨hmI, hmJ⟩ := integral_min_inv hβ0 hβ1 hT
  refine ⟨c⁻¹ * Cu + 2 * ((1 / bexp d s + 1 / (1 - bexp d s)) * (Cm + 1) ^ bexp d s), by
    have : 0 < 1 - bexp d s := by linarith
    positivity, fun z hz => ?_⟩
  have hI := sliceG_stieltjes_int hd hs0 hs hsd hz
  have hmeas : AEStronglyMeasurable (fun l : ℝ => l ^ (-bexp d s) * |sliceG d l z|) (volume.restrict (Ioi (0 : ℝ))) := by
    have h1 : Measurable fun l : ℝ => sliceG d l z :=
      (measurable_sliceG_uncurry d).comp (measurable_id.prodMk measurable_const)
    exact ((measurable_id.pow_const _).mul h1.abs).aestronglyMeasurable
  have hdom : ∀ l ∈ Ioi (0 : ℝ), l ^ (-bexp d s) * |sliceG d l z| ≤
      l ^ (-bexp d s) * sliceG d l z + 2 * (l ^ (-bexp d s) * min (Cm + 1) (1 / l)) := by
    intro l hl
    have hl' : (0 : ℝ) < l := hl
    have hp : 0 ≤ l ^ (-bexp d s) := Real.rpow_nonneg hl'.le _
    have h1 := hCm l hl' z
    have h2 : min Cm (1 / l) ≤ min (Cm + 1) (1 / l) := min_le_min_right _ (by linarith)
    have h3 : |sliceG d l z| ≤ sliceG d l z + 2 * min (Cm + 1) (1 / l) := by
      rw [abs_le]; constructor <;> nlinarith [le_abs_self (sliceG d l z), neg_abs_le (sliceG d l z),
        le_min (by linarith : (0 : ℝ) ≤ Cm + 1) (by positivity : (0 : ℝ) ≤ 1 / l)]
    calc l ^ (-bexp d s) * |sliceG d l z| ≤ l ^ (-bexp d s) * (sliceG d l z + 2 * min (Cm + 1) (1 / l)) :=
          mul_le_mul_of_nonneg_left h3 hp
      _ = _ := by ring
  have hdomi : IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * sliceG d l z +
      2 * (l ^ (-bexp d s) * min (Cm + 1) (1 / l))) (Ioi 0) := hI.add (hmI.const_mul 2)
  have hint : IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * |sliceG d l z|) (Ioi 0) := by
    refine Integrable.mono' hdomi hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl => ?_)
    have hl' : (0 : ℝ) < l := hl
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hl'.le _) (abs_nonneg _))]
    exact hdom l hl
  refine ⟨hint, ?_⟩
  have h1 : ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * |sliceG d l z| ≤
      ∫ l in Ioi (0 : ℝ), (l ^ (-bexp d s) * sliceG d l z + 2 * (l ^ (-bexp d s) * min (Cm + 1) (1 / l))) :=
    setIntegral_mono_on hint hdomi measurableSet_Ioi hdom
  rw [integral_add hI (hmI.const_mul 2), integral_const_mul] at h1
  have h2 : ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * sliceG d l z = c⁻¹ * periodicRiesz d s z := by
    rw [hker z hz]; field_simp
  rw [h2] at h1
  have h3 := hCu z hz
  have h4 : c⁻¹ * periodicRiesz d s z ≤ c⁻¹ * (selfScale d s (KernelGrad.tdist z 0) + Cu) :=
    mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hc.le)
  have h5 : 2 * ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * min (Cm + 1) (1 / l) ≤
      2 * ((1 / bexp d s + 1 / (1 - bexp d s)) * (Cm + 1) ^ bexp d s) := by linarith [hmJ]
  linarith

end Upper

end HRS.Commutator.Stj
