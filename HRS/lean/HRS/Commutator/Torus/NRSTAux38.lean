import HRS.Commutator.Torus.NRSTAux37

/-!
# NRS-T, part 38: `‖|∇|^{τ+1} v_c‖_{L^{d/τ}} ≲ ‖|∇|^{(d-s)/2} v‖_{L^{2d/(d-s-2)}}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ} {s : ℝ}

lemma nrstr_isRealT_of_im {A : NRST.TPA d} (hA : ∀ x, (NRST.ev A x).im = 0) : NRST.IsRealT A :=
  fun k => (NRST.conj_coeff_of_real A hA k).symm

lemma nrstr_rpow_lw {α : ℝ} (hα : α ≠ 0) (k : Lattice d) :
    (2 * Real.pi * Lattice.enorm k) ^ α = NRST.lw α k := by
  by_cases hk : k = 0
  · subst hk; simp [NRST.lw_zero, NRST.enorm_zero, Real.zero_rpow hα]
  · unfold NRST.lw; rw [if_neg hk]

lemma nrstr_ofReal_inv_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (ENNReal.ofReal (a / b))⁻¹ = ENNReal.ofReal (b / a) := by
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]

lemma nrstr_U_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {τ : ℝ} (hτ : 0 < τ)
    (hτα : τ ≤ ((d : ℝ) - s) / 2 - 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Fin d → NRST.TPA d), (∀ j x, (NRST.ev (V j) x).im = 0) → ∀ F : ℝ, 0 ≤ F →
      ∀ w : Torus d → Euc d, IsFracDeriv (((d : ℝ) - s) / 2) (NRST.vOf V) w →
        eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - s - 2))) volume ≤ ENNReal.ofReal F →
        ∀ c : Fin d, eLpNorm (NRST.ev (NRST.lam (τ + 1) (V c))) (ENNReal.ofReal (d / τ)) volume ≤
          ENNReal.ofReal (C * F) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  set α : ℝ := ((d : ℝ) - s) / 2 with hα
  have hα1 : τ + 1 ≤ α := by linarith
  have hαd : α ≤ d / 2 := by rw [hα]; linarith
  have hαpos : 0 < α := by linarith
  have hP0r : 2 * (d : ℝ) / ((d : ℝ) - s - 2) = d / (α - 1) := by
    have h1 : (d : ℝ) - s - 2 = 2 * (α - 1) := by rw [hα]; ring
    rw [h1]; field_simp
  have hα1pos : 0 < α - 1 := by linarith
  -- common facts on the regularised component
  have common : ∀ (V : Fin d → NRST.TPA d), (∀ j x, (NRST.ev (V j) x).im = 0) → ∀ F : ℝ, 0 ≤ F →
      ∀ w : Torus d → Euc d, IsFracDeriv α (NRST.vOf V) w →
      eLpNorm w (ENNReal.ofReal (d / (α - 1))) volume ≤ ENNReal.ofReal F → ∀ c : Fin d,
      MemLp (fun x => regW w x c) (ENNReal.ofReal (d / (α - 1))) volume ∧
      eLpNorm (fun x => regW w x c) (ENNReal.ofReal (d / (α - 1))) volume ≤ ENNReal.ofReal F ∧
      ∀ k, Torus.fcoef (fun x => regW w x c) k = ((NRST.lw α k : ℝ) : ℂ) * (V c).coeff k := by
    intro V hVr F hF0 w hw hwn c
    have hmeas : AEStronglyMeasurable (fun x => regW w x c) volume :=
      ((EuclideanSpace.proj c : Euc d →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
        (aestronglyMeasurable_regW w))
    have hle : eLpNorm (fun x => regW w x c) (ENNReal.ofReal (d / (α - 1))) volume ≤ ENNReal.ofReal F := by
      refine le_trans ?_ hwn
      refine eLpNorm_mono hmeas fun x => ?_
      exact (PiLp.norm_apply_le (regW w x) c).trans (norm_regW_le w x)
    refine ⟨lt_of_le_of_lt hle ENNReal.ofReal_lt_top, hle, fun k => ?_⟩
    rw [fcoef_regW w c k, hw c k]
    have : Torus.fcoef (fun x => NRST.vOf V x c) k = (V c).coeff k :=
      nrstr_fcoef_re (nrstr_isRealT_of_im (hVr c)) k
    rw [this, nrstr_rpow_lw hαpos.ne']
  by_cases hlt : τ + 1 < α
  · -- the case σ₀ = α - 1 - τ > 0: HLS
    have hσ : 0 < α - 1 - τ := by linarith
    have hP0 : 1 < ENNReal.ofReal (d / (α - 1)) := by
      rw [← ENNReal.ofReal_one]
      refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
      rw [lt_div_iff₀ hα1pos]; linarith
    have hPP : ENNReal.ofReal (d / (α - 1)) < ENNReal.ofReal (d / τ) := by
      refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
      exact div_lt_div_of_pos_left hdpos hτ (by linarith)
    have hrel : (ENNReal.ofReal (d / τ))⁻¹ =
        (ENNReal.ofReal (d / (α - 1)))⁻¹ - ENNReal.ofReal ((α - 1 - τ) / d) := by
      rw [nrstr_ofReal_inv_div hdpos hτ, nrstr_ofReal_inv_div hdpos hα1pos,
        ← ENNReal.ofReal_sub _ (by positivity)]
      congr 1
      field_simp
      ring
    obtain ⟨C1, hC1, hH⟩ := nrstr_hls_trig hd1 hσ hP0 hPP ENNReal.ofReal_lt_top hrel
    refine ⟨C1 + 1, by positivity, fun V hVr F hF0 w hw hwn c => ?_⟩
    rw [hP0r] at hwn
    obtain ⟨hmem, hnorm, hcoef⟩ := common V hVr F hF0 w hw hwn c
    have hU := nrstr_isRealT_lam (τ + 1) (nrstr_isRealT_of_im (hVr c))
    have h := hH (NRST.lam (τ + 1) (V c)) hU (by simp [NRST.lam, NRST.lw_zero]) _ hmem (fun k => by
      rw [hcoef k]
      unfold NRST.lam
      rw [NRST.coeff_mulSeq, ← mul_assoc, ← Complex.ofReal_mul, ← NRST.lw_mul]
      congr 3
      ring)
    refine h.trans ?_
    calc ENNReal.ofReal C1 * eLpNorm (fun x => regW w x c) (ENNReal.ofReal (d / (α - 1))) volume
        ≤ ENNReal.ofReal C1 * ENNReal.ofReal F := by gcongr
      _ = ENNReal.ofReal (C1 * F) := (ENNReal.ofReal_mul hC1.le).symm
      _ ≤ ENNReal.ofReal ((C1 + 1) * F) :=
          ENNReal.ofReal_le_ofReal (by nlinarith)
  · -- the endpoint case τ + 1 = α
    have heq : τ + 1 = α := le_antisymm hα1 (not_lt.1 hlt)
    have hτe : τ = α - 1 := by linarith
    refine ⟨2, by norm_num, fun V hVr F hF0 w hw hwn c => ?_⟩
    rw [hP0r] at hwn
    obtain ⟨hmem, hnorm, hcoef⟩ := common V hVr F hF0 w hw hwn c
    have hU := nrstr_isRealT_lam (τ + 1) (nrstr_isRealT_of_im (hVr c))
    have hint : Integrable (fun x => regW w x c) volume :=
      hmem.integrable (by
        rw [← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ hα1pos]; linarith)
    have h := nrstr_eLpNorm_of_fcoef hU hint (fun k => by
      rw [hcoef k]
      unfold NRST.lam
      rw [NRST.coeff_mulSeq, heq]) (ENNReal.ofReal (d / (α - 1)))
    have e : ENNReal.ofReal ((d : ℝ) / τ) = ENNReal.ofReal (d / (α - 1)) := by rw [hτe]
    rw [e, ← h]
    refine hnorm.trans (ENNReal.ofReal_le_ofReal (by nlinarith))

end HRS.Commutator.TorusNote
