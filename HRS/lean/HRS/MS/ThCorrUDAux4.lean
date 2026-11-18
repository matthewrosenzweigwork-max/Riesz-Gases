import HRS.MS.ThCorrUDAux3

/-!
# TC-U2 (part 4): the uniform hard-regime bootstrap `d - 1 ≤ s < d`

Namespace `HRS.MS.TcU`; helper lemmas carry the prefix `tcu2_`.

The Hölder gain and the crossing of `EucRegHAux3` (`regh_gain_rec`, `regh_cross_rec`) are repeated for the quantitative
class `qC` (`ThCorrUDAux3`): `tcu2_gain_q`, `tcu2_cross_q` return, for every order `k` and constants `L`, `Cd`
(`‖D^j F‖ ≤ Cd (1+‖x‖)^{-(d+1)}`), one constant `L'`.  Then `tcu2_rho_of_U` passes from the class of `U ρ` to that of
`ρ` (`ρ = g · exp (-β U)` with the Gaussian profile `g`, `tcu2_gauss_q`), and `tcu2_boot_hard` redoes the loop of
`regh_bootstrap` (lift, loop, base, crossing) with the quantifier order `∀ k, ∃ M, ∀ instances`.
The main theorem is `tcu_uniform_hard`.
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace HRS.MS.TcU

open HRS HRS.Whole HRS.MS.LogReg HRS.MS.Thm

variable {d : ℕ}

/-! ### Gain and crossing at all orders, quantitative -/

/-- The Hölder gain, at all differentiability orders, with one output constant. -/
lemma tcu2_gain_q {s σ θ θ' : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (hσs : s ≤ σ) (hσ2 : σ ≤ s + 2) (hσd : σ < d) (hθ : 0 < θ) (hθ'0 : 0 ≤ θ') (hθ'θ : θ' ≤ θ)
    (hθ'a : θ' + ((d : ℝ) - σ) < 1) :
    ∀ (k : ℕ) (L Cd : ℝ), ∃ L' : ℝ, ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] {F : Euc d → E}, qC d θ k E F L →
      (∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j F y‖ ≤ Cd * lreg_phi d y) → regh_Rl k F →
      qC d (θ' + ((d : ℝ) - σ)) k E (regh_T s F) L' := by
  obtain ⟨C, hC0, hC⟩ := tcu2_T_hold hd1 hs hsd hs2 hσs hσ2 hσd hθ'0 hθ'a
  have hpos : 0 < θ' + ((d : ℝ) - σ) := by linarith
  intro k
  induction k with
  | zero =>
    intro L Cd
    refine ⟨max (Cd * lreg_A d s) (C * (L + 2 * L) + s * (Cd * ∫ y, lreg_phi d y) +
      2 * (Cd * lreg_A d s)), ?_⟩
    intro E _ _ _ F hF hdec hR
    obtain ⟨hm, hB, hK⟩ := hF
    have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hB 0)
    have hCd : 0 ≤ Cd := (mul_nonneg_iff_of_pos_right (lreg_phi_pos (0 : Euc d))).1
      ((norm_nonneg _).trans (by simpa [norm_iteratedFDeriv_zero] using hdec 0 le_rfl 0))
    have hb : ∀ y, ‖F y‖ ≤ Cd * lreg_phi d y := fun y => by
      simpa [norm_iteratedFDeriv_zero] using hdec 0 le_rfl y
    have hK' := regh_hol_mono hθ'θ hL0 hL0 hB hK hθ'0
    obtain ⟨hTb, hTh⟩ := hC hm (regh_R_rdec hR) (K := L + 2 * L) (by positivity) hCd hb hK'
    have hTh' : ∀ x h, ‖regh_T s F (x + h) - regh_T s F x‖ ≤
        (C * (L + 2 * L) + s * (Cd * ∫ y, lreg_phi d y) + 2 * (Cd * lreg_A d s)) *
          ‖h‖ ^ (θ' + ((d : ℝ) - σ)) := hTh
    refine ⟨(regh_hol_cont hpos hTh').aestronglyMeasurable, fun x => (hTb x).trans (le_max_left _ _),
      fun x h => (hTh' x h).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg h) _)
  | succ k ih =>
    intro L Cd
    obtain ⟨L0, hL0⟩ := ih L Cd
    refine ⟨max (Cd * lreg_A d s) L0, ?_⟩
    intro E _ _ _ F hF hdec hR
    have hcF : Continuous F := hF.1.continuous
    obtain ⟨hd, hB, hF'⟩ := hF
    obtain ⟨hR0, hR'⟩ := hR
    have hcF' : Continuous (fderiv ℝ F) := qC_cont hθ hF'
    have hF1 : ContDiff ℝ 1 F := contDiff_one_iff_fderiv.2 ⟨hd, hcF'⟩
    have hT : ∀ x, HasFDerivAt (regh_T s F) (regh_T s (fderiv ℝ F) x) x := fun x =>
      regh_T_hasFDerivAt hd1 hs hsd hF1 hR0 (regh_R_rdec hR') x
    have hCd : 0 ≤ Cd := (mul_nonneg_iff_of_pos_right (lreg_phi_pos (0 : Euc d))).1
      ((norm_nonneg _).trans (by simpa [norm_iteratedFDeriv_zero] using hdec 0 (Nat.zero_le _) 0))
    have hb : ∀ y, ‖F y‖ ≤ Cd * lreg_phi d y := fun y => by
      simpa [norm_iteratedFDeriv_zero] using hdec 0 (Nat.zero_le _) y
    refine ⟨fun x => (hT x).differentiableAt, fun x =>
      ((regh_T_integrable hd1 hs hsd hcF.aestronglyMeasurable hCd hb x).2).trans (le_max_left _ _), ?_⟩
    have e : fderiv ℝ (regh_T s F) = regh_T s (fderiv ℝ F) := funext fun x => (hT x).fderiv
    rw [e]
    refine qC_mono_L k (le_max_right _ _) (hL0 hF' (fun j hj y => ?_) hR')
    rw [norm_iteratedFDeriv_fderiv]
    exact hdec (j + 1) (by omega) y

/-- The crossing, at all differentiability orders, with one output constant. -/
lemma tcu2_cross_q {s θ θ' : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hθ'0 : 0 ≤ θ') (hθθ : θ' < θ) (hθ'a : 1 < θ' + ((d : ℝ) - s))
    (hθb : θ + ((d : ℝ) - s) < 2) :
    ∀ (k : ℕ) (L Cd : ℝ), ∃ L' : ℝ, ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] {F : Euc d → E}, qC d θ k E F L →
      (∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j F y‖ ≤ Cd * lreg_phi d y) → regh_Rl k F →
      qC d (θ - θ') (k + 1) E (regh_T s F) L' := by
  obtain ⟨C, hC0, hC⟩ := tcu2_cross hd1 hs hsd hs2 hθ hθ1 hθ'0 hθθ.le hθ'a hθb
  intro k
  induction k with
  | zero =>
    intro L Cd
    refine ⟨max (Cd * lreg_A d s) (max (C * (L + Cd) + s * (Cd * ∫ y, lreg_phi d y))
      (C * L + s * (s + 3) * (Cd * ∫ y, lreg_phi d y) +
        2 * (C * (L + Cd) + s * (Cd * ∫ y, lreg_phi d y)))), ?_⟩
    intro E _ _ _ F hF hdec hR
    obtain ⟨hm, hB, hK⟩ := hF
    have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hB 0)
    have hCd : 0 ≤ Cd := (mul_nonneg_iff_of_pos_right (lreg_phi_pos (0 : Euc d))).1
      ((norm_nonneg _).trans (by simpa [norm_iteratedFDeriv_zero] using hdec 0 le_rfl 0))
    have hb : ∀ y, ‖F y‖ ≤ Cd * lreg_phi d y := fun y => by
      simpa [norm_iteratedFDeriv_zero] using hdec 0 le_rfl y
    obtain ⟨P, hP, hPb, hPh⟩ := hC hm (regh_R_rdec hR) (K := L) hL0 hCd hb hK
    refine ⟨fun x => (hP x).differentiableAt, fun x =>
      ((regh_T_integrable hd1 hs hsd hm hCd hb x).2).trans (le_max_left _ _), ?_⟩
    have e : fderiv ℝ (regh_T s F) = P := funext fun x => (hP x).fderiv
    rw [e]
    refine ⟨(regh_hol_cont (sub_pos.2 hθθ) hPh).aestronglyMeasurable, fun x => (hPb x).trans
      ((le_max_left _ _).trans (le_max_right _ _)), fun x h => (hPh x h).trans ?_⟩
    exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _))
      (Real.rpow_nonneg (norm_nonneg h) _)
  | succ k ih =>
    intro L Cd
    obtain ⟨L0, hL0⟩ := ih L Cd
    refine ⟨max (Cd * lreg_A d s) L0, ?_⟩
    intro E _ _ _ F hF hdec hR
    have hcF : Continuous F := hF.1.continuous
    obtain ⟨hd, hB, hF'⟩ := hF
    obtain ⟨hR0, hR'⟩ := hR
    have hcF' : Continuous (fderiv ℝ F) := qC_cont hθ hF'
    have hF1 : ContDiff ℝ 1 F := contDiff_one_iff_fderiv.2 ⟨hd, hcF'⟩
    have hT : ∀ x, HasFDerivAt (regh_T s F) (regh_T s (fderiv ℝ F) x) x := fun x =>
      regh_T_hasFDerivAt hd1 hs hsd hF1 hR0 (regh_R_rdec hR') x
    have hCd : 0 ≤ Cd := (mul_nonneg_iff_of_pos_right (lreg_phi_pos (0 : Euc d))).1
      ((norm_nonneg _).trans (by simpa [norm_iteratedFDeriv_zero] using hdec 0 (Nat.zero_le _) 0))
    have hb : ∀ y, ‖F y‖ ≤ Cd * lreg_phi d y := fun y => by
      simpa [norm_iteratedFDeriv_zero] using hdec 0 (Nat.zero_le _) y
    refine ⟨fun x => (hT x).differentiableAt, fun x =>
      ((regh_T_integrable hd1 hs hsd hcF.aestronglyMeasurable hCd hb x).2).trans (le_max_left _ _), ?_⟩
    have e : fderiv ℝ (regh_T s F) = regh_T s (fderiv ℝ F) := funext fun x => (hT x).fderiv
    rw [e]
    refine qC_mono_L (k + 1) (le_max_right _ _) (hL0 hF' (fun j hj y => ?_) hR')
    rw [norm_iteratedFDeriv_fderiv]
    exact hdec (j + 1) (by omega) y

/-! ### From the class of `U ρ` to the class of `ρ` -/

/-- `ρ = g · exp (-β U ρ)`: from `U ρ ∈ qC θ k L` to `ρ ∈ qC θ k L'`, a decay bound for the derivatives of `ρ`
and the qualitative decay `regh_Rl k ρ`; the constants `L'`, `Cd` do not depend on the instance. -/
lemma tcu2_rho_of_U {s : ℝ} {am ap βm βp b C0 z₀ θ : ℝ} (ham : 0 < am) (hβm : 0 < βm)
    (hap : am ≤ ap) (hβp : βm ≤ βp) (hz₀ : 0 < z₀) (hb : 0 < b) (hC0 : 0 ≤ C0) (hθpos : 0 < θ)
    (hθ1 : θ ≤ 1) (k : ℕ) (L : ℝ) :
    ∃ L' Cd : ℝ, ∀ (a β Z : ℝ) (ρ : Euc d → ℝ),
      TcuInst d (rege_U s) am ap βm βp b C0 z₀ a β Z ρ → qC d θ k ℝ (rege_U s ρ) L →
      qC d θ k ℝ ρ L' ∧ (∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j ρ y‖ ≤ Cd * lreg_phi d y) ∧ regh_Rl k ρ := by
  have hap0 : 0 < ap := ham.trans_le hap
  have hβp0 : 0 < βp := hβm.trans_le hβp
  obtain ⟨Lg, hLg⟩ := tcu2_gauss_q (d := d) hθpos.le hθ1 ham hβm hap hβp hz₀ k
  obtain ⟨Le, hLe⟩ := qC_exp (d := d) hθpos.le hθ1 k (βp * L)
  obtain ⟨Lp, hLp⟩ := qC_prod (d := d) hθpos.le hθ1 k 1 Lg Le
  have hCp : ∀ j : ℕ, ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ {K : ℝ}, 0 ≤ K → ∀ n : Euc d → ℝ,
      (∀ x, n x ≤ K * (1 + ‖x‖) ^ j * Real.exp (-b * ‖x‖ ^ 2)) →
      ∀ y, n y ≤ (K * Cp) * lreg_phi d y := fun j => tcu2_phi_bound hb j
  choose Cp hCp0 hCpb using hCp
  set Kj : ℕ → ℝ := fun j => (Nat.factorial j : ℝ) * max C0 0 * (max (βp * ap + βp * L) 1) ^ j
    with hKj
  refine ⟨Lp, ∑ j ∈ Finset.range (k + 1), Kj j * Cp j, fun a β Z ρ h hU => ?_⟩
  have hL0 : 0 ≤ L := qC_nonneg hU
  have ha := h.pos_a ham
  have hβ := h.pos_β hβm
  have hZ := h.pos_Z hz₀
  obtain ⟨hUc, hUb⟩ := qC_contDiff hθpos k hU
  obtain ⟨-, hρD⟩ := tcu2_inst_deriv_of ham hβm hap hβp hz₀ hL0 h hUc (fun i _ hik x => hUb i hik x)
  have hKj0 : ∀ j, 0 ≤ Kj j := fun j => by positivity
  refine ⟨?_, fun j hj y => ?_, ?_⟩
  · -- the class of `ρ`
    have hgq := hLg a β Z h.ha1 h.ha2 h.hβ1 h.hβ2 h.hZ
    have hsm : qC d θ k ℝ (fun x => (-β) • rege_U s ρ x) (βp * L) := by
      refine qC_mono_L k ?_ (qC_smul (-β) k hU)
      rw [abs_neg, abs_of_pos hβ]
      exact mul_le_mul_of_nonneg_right h.hβ2 hL0
    have hex := hLe hsm
    have e : ρ = fun x => (ContinuousLinearMap.mul ℝ ℝ)
        (Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + 0)) / Z) (Real.exp ((-β) • rege_U s ρ x)) := by
      funext x
      rw [h.heq x, ContinuousLinearMap.mul_apply', smul_eq_mul,
        show -β * (a * ‖x‖ ^ 2 / 2 + rege_U s ρ x) = -β * (a * ‖x‖ ^ 2 / 2 + 0) + -β * rege_U s ρ x by ring,
        Real.exp_add]
      ring
    rw [e]
    exact hLp (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.opNorm_mul_le ℝ ℝ) hgq hex
  · -- decay of the derivatives
    have h1 := hCpb j (hKj0 j) (fun x => ‖iteratedFDeriv ℝ j ρ x‖) (hρD j hj) y
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (lreg_phi_pos y).le)
    exact Finset.single_le_sum (f := fun j => Kj j * Cp j) (fun j _ => mul_nonneg (hKj0 j) (hCp0 j))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  · exact regh_R_of_iter k fun j hj =>
      rege_rdec_of_gauss (j := j) hb (hKj0 j) (hρD j hj)

/-! ### The loop -/

/-- All instances have `U ρ ∈ qC θ k` with the constant `L`. -/
def TcuQ (d : ℕ) (s : ℝ) (am ap βm βp b C0 z₀ θ : ℝ) (k : ℕ) (L : ℝ) : Prop :=
  ∀ (a β Z : ℝ) (ρ : Euc d → ℝ), TcuInst d (rege_U s) am ap βm βp b C0 z₀ a β Z ρ →
    qC d θ k ℝ (rege_U s ρ) L

/-- **The uniform bootstrap in the hard regime** `d - 1 ≤ s < d`. -/
theorem tcu2_boot_hard (hd1 : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) (hs1 : (d : ℝ) - 1 ≤ s)
    {am ap βm βp b C0 z₀ : ℝ} (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp)
    (hz₀ : 0 < z₀) (hb : 0 < b) (hC0 : 0 ≤ C0) :
    ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ TcuP d (rege_U s) am ap βm βp b C0 z₀ k M := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (d : ℝ) - s := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α ≤ 1 := by rw [hα]; linarith
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 1 - α / 4 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; linarith
  have hT1 : T < 1 := by rw [hT]; linarith
  have hs2 : (d : ℝ) < s + 2 := by linarith
  have hσe : (d : ℝ) - (s + α / 2) = α / 2 := by rw [hα]; ring
  have hσd : s + α / 2 < d := by linarith
  have hσs : s ≤ s + α / 2 := by linarith
  have hσ2 : s + α / 2 ≤ s + 2 := by linarith
  have hUeq : ∀ ρ : Euc d → ℝ, rege_U s ρ = regh_T s ρ := fun ρ => regh_U_eq s ρ
  let Q : ℝ → ℕ → Prop := fun θ k => ∃ L : ℝ, TcuQ d s am ap βm βp b C0 z₀ θ k L
  -- raising the Hölder exponent
  have hlift : ∀ (k : ℕ) (θ : ℝ), 0 < θ → θ ≤ T → Q θ k → Q (min (θ + α / 2) T) k := by
    intro k θ hθ hθT ⟨L, hL⟩
    obtain ⟨Lρ, Cd, hρ⟩ := tcu2_rho_of_U (s := s) ham hβm hap hβp hz₀ hb hC0 hθ (by linarith) k L
    obtain ⟨L'', hL''⟩ := tcu2_gain_q hd1 hs hsd hs2 (σ := s + α / 2) hσs hσ2 hσd hθ
      (θ' := min θ (T - α / 2)) (le_min hθ.le (by rw [hT]; linarith)) (min_le_left _ _)
      (by rw [hσe]; have := min_le_right θ (T - α / 2); linarith) k Lρ Cd
    refine ⟨L'', fun a β Z ρ h => ?_⟩
    obtain ⟨hρC, hρD, hρR⟩ := hρ a β Z ρ h (hL a β Z ρ h)
    have := hL'' hρC hρD hρR
    have e : min θ (T - α / 2) + ((d : ℝ) - (s + α / 2)) = min (θ + α / 2) T := by
      rw [hσe]; simp only [min_def]; split_ifs <;> linarith
    rw [e] at this
    rw [hUeq]
    exact this
  have hloopn : ∀ (n k : ℕ) (θ : ℝ), 0 < θ → θ ≤ T → Q θ k → T ≤ θ + n * (α / 2) → Q T k := by
    intro n
    induction n with
    | zero =>
      intro k θ hθ hθT hU hle
      have : θ = T := le_antisymm hθT (by simpa using hle)
      rwa [this] at hU
    | succ n ih =>
      intro k θ hθ hθT hU hle
      have h1 := hlift k θ hθ hθT hU
      by_cases hc : T ≤ θ + α / 2
      · rwa [min_eq_right hc] at h1
      · push_neg at hc
        rw [min_eq_left hc.le] at h1
        exact ih k (θ + α / 2) (by linarith) hc.le h1 (by push_cast at hle; linarith)
  have hloop : ∀ (k : ℕ) (θ : ℝ), 0 < θ → θ ≤ T → Q θ k → Q T k := by
    intro k θ hθ hθT hU
    obtain ⟨n, hn⟩ := exists_nat_ge (T / (α / 2))
    refine hloopn n k θ hθ hθT hU ?_
    have : T ≤ n * (α / 2) := by rwa [div_le_iff₀ (by positivity)] at hn
    linarith
  -- the base case: Hölder continuity of `U ρ` of order `α / 2`
  have hbase : Q (α / 2) 0 := by
    obtain ⟨Cp0, hCp0, hphi0⟩ := tcu2_phi_bound (d := d) hb 0
    obtain ⟨C, hC0', hC⟩ := tcu2_T_hold hd1 hs hsd hs2 (σ := s + α / 2) hσs hσ2 hσd (θ := 0) le_rfl
      (by rw [hσe]; linarith)
    refine ⟨max ((C0 * Cp0) * lreg_A d s) (C * (2 * (C0 * Cp0)) +
      s * ((C0 * Cp0) * ∫ y, lreg_phi d y) + 2 * ((C0 * Cp0) * lreg_A d s)), fun a β Z ρ h => ?_⟩
    have hdec := h.rdec hz₀ hb hC0
    have hCb : 0 ≤ C0 * Cp0 := mul_nonneg hC0 hCp0
    have hb0 : ∀ y, ‖ρ y‖ ≤ (C0 * Cp0) * lreg_phi d y := by
      intro y
      refine hphi0 hC0 (fun x => ‖ρ x‖) (fun x => ?_) y
      rw [Real.norm_of_nonneg (h.pos hz₀ x).le, pow_zero, mul_one]
      exact h.hup x
    have hB : ∀ y, ‖ρ y‖ ≤ C0 * Cp0 := fun y =>
      (hb0 y).trans (by nlinarith [lreg_phi_le_one (d := d) y])
    have hK : ∀ x h, ‖ρ (x + h) - ρ x‖ ≤ (2 * (C0 * Cp0)) * ‖h‖ ^ (0 : ℝ) := fun x h => by
      rw [Real.rpow_zero, mul_one]
      calc _ ≤ ‖ρ (x + h)‖ + ‖ρ x‖ := norm_sub_le _ _
        _ ≤ C0 * Cp0 + C0 * Cp0 := add_le_add (hB _) (hB _)
        _ = _ := by ring
    obtain ⟨hTb, hTh⟩ := hC h.hm.aestronglyMeasurable hdec (K := 2 * (C0 * Cp0)) (by positivity) hCb
      hb0 hK
    have hTh' : ∀ x h, ‖regh_T s ρ (x + h) - regh_T s ρ x‖ ≤
        (C * (2 * (C0 * Cp0)) + s * ((C0 * Cp0) * ∫ y, lreg_phi d y) +
          2 * ((C0 * Cp0) * lreg_A d s)) * ‖h‖ ^ (α / 2) := by
      intro x h
      have := hTh x h
      rwa [show (0 : ℝ) + ((d : ℝ) - (s + α / 2)) = α / 2 by rw [hσe]; ring] at this
    rw [hUeq]
    exact ⟨(regh_hol_cont (by positivity) hTh').aestronglyMeasurable,
      fun x => (hTb x).trans (le_max_left _ _), fun x h => (hTh' x h).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg h) _))⟩
  -- crossing
  have hcross : ∀ k : ℕ, Q T k → Q (α / 4) (k + 1) := by
    intro k ⟨L, hL⟩
    obtain ⟨Lρ, Cd, hρ⟩ := tcu2_rho_of_U (s := s) ham hβm hap hβp hz₀ hb hC0 hT0 hT1.le k L
    obtain ⟨L', hL'⟩ := tcu2_cross_q hd1 hs hsd hs2 hT0 hT1.le (θ' := 1 - α / 2) (by linarith)
      (by linarith) (by rw [← hα]; linarith) (by rw [← hα]; linarith) k Lρ Cd
    refine ⟨L', fun a β Z ρ h => ?_⟩
    obtain ⟨hρC, hρD, hρR⟩ := hρ a β Z ρ h (hL a β Z ρ h)
    have := hL' hρC hρD hρR
    have e : T - (1 - α / 2) = α / 4 := by rw [hT]; ring
    rw [e] at this
    rw [hUeq]
    exact this
  have hmain : ∀ k : ℕ, Q T k := by
    intro k
    induction k with
    | zero => exact hloop 0 (α / 2) (by positivity) (by rw [hT]; linarith) hbase
    | succ k ih => exact hloop (k + 1) (α / 4) (by positivity) (by rw [hT]; linarith) (hcross k ih)
  intro k
  obtain ⟨L, hL⟩ := hmain k
  refine ⟨max L 0, le_max_right _ _, fun a β Z ρ h => ?_⟩
  obtain ⟨hc, hbd⟩ := qC_contDiff hT0 k (hL a β Z ρ h)
  exact ⟨hc, fun i _ hik x => (hbd i hik x).trans (le_max_left _ _)⟩

/-- **TC-U2 (`d - 1 ≤ s < d`).**  `TcRef` and `TcDrift` for the thermal densities, uniformly over compact
`(a, β)`. -/
theorem tcu_uniform_hard (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hs1 : (d : ℝ) - 1 ≤ s)
    {am ap βm βp : ℝ} (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp) :
    ∃ c M₀ m₂ : ℝ, 0 < c ∧ 0 < M₀ ∧
      (∀ N : ℕ, ∃ S : ℝ, 0 ≤ S ∧ ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
        HRS.MS.TcDefs.TcRef d (thermalDensity d s a β) M₀ c S N) ∧
      (∀ m : ℕ, ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
        HRS.MS.TcDefs.TcDrift d (thermalDensity d s a β) (β * a) Mb m₂ m) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, M₀, z₀, m₂, UB, hc, hM₀, hz₀, hall⟩ :=
    tcu_apriori_pos hd1 hs0 hsd ham hβm hap hβp
  refine ⟨c, M₀, m₂, hc, hM₀, tcu2_final (s := s) (Uop := rege_U s) ham hβm hap hβp hz₀ hc hM₀ ?_
    (tcu2_boot_hard hd1 hs0 hsd hs1 ham hβm hap hβp hz₀ hc hM₀.le)⟩
  intro a β h1 h2 h3 h4
  obtain ⟨hZ, hgauss, hint, hm2, -⟩ := hall a β h1 h2 h3 h4
  obtain ⟨hP, heq⟩ := tcu2_data_pos hd hs0 hsd (ham.trans_le h1) (hβm.trans_le h3)
  exact ⟨⟨h1, h2, h3, h4, hZ, hP.measurable, heq, hgauss⟩, hP, hint, hm2⟩

end HRS.MS.TcU

end
