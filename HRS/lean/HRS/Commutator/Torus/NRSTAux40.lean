import HRS.Commutator.Torus.NRSTAux39

/-!
# NRS-T, part 40: the multiplier bound `‖|∇|^τ (∂_a v_c · Γ)‖₂ ≲ K ‖|∇|^τ Γ‖₂` for a fixed exponent `τ`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ} {s : ℝ}

lemma nrstr_integrable_re (T : NRST.TPA d) : Integrable (fun x => (NRST.ev T x).re) volume :=
  (Complex.continuous_re.comp (NRST.continuous_ev T)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma nrstr_mul_tau (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {τ : ℝ} (hτ : 0 < τ)
    (hτα : τ ≤ ((d : ℝ) - s) / 2 - 1) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (V : Fin d → NRST.TPA d), (∀ j x, (NRST.ev (V j) x).im = 0) → ∀ K : ℝ,
      TorusSubTransport d s (NRST.vOf V) K → ∀ (a c : Fin d) (Γ : NRST.TPA d), NRST.IsRealT Γ →
        Γ.coeff 0 = 0 → NRST.hom τ (NRST.dd a (V c) * Γ) ≤ (CB * K) ^ 2 * NRST.hom τ Γ := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hτd2 : τ < (d : ℝ) / 2 := by linarith
  have hτd : τ < d := by linarith
  have hden : 0 < (d : ℝ) - 2 * τ := by linarith
  have hPr1 : 1 < (d : ℝ) / τ := by rw [lt_div_iff₀ hτ]; linarith
  have hQr1 : 1 < 2 * (d : ℝ) / ((d : ℝ) - 2 * τ) := by rw [lt_div_iff₀ hden]; linarith
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have h1 : (ENNReal.ofReal ((d : ℝ) / τ))⁻¹ + (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 2 * τ)))⁻¹ =
      (2 : ℝ≥0∞)⁻¹ := by
    rw [nrstr_ofReal_inv_div hdpos hτ, nrstr_ofReal_inv_div (by positivity) hden, h2,
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have hp1 : (1 : ℝ≥0∞) < ENNReal.ofReal ((d : ℝ) / τ) := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hPr1
  have hq1 : (1 : ℝ≥0∞) < ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 2 * τ)) := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hQr1
  obtain ⟨CL, hCL, hL⟩ := leibt_main hd1 τ hτ 2 (ENNReal.ofReal ((d : ℝ) / τ))
    (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 2 * τ))) 2 ⊤ (by norm_num) (by norm_num) hp1 hq1
    (by norm_num) (by simp) h1 (by simp)
  have hCj : ∀ a : Fin d, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ W : NRST.TPA d,
      eLpNorm (NRST.ev (nrstr_Jb τ (NRST.dd a W))) (ENNReal.ofReal ((d : ℝ) / τ)) volume ≤
        C * eLpNorm (NRST.ev (NRST.lam (τ + 1) W)) (ENNReal.ofReal ((d : ℝ) / τ)) volume :=
    fun a => nrstr_Jb_dd_bound hd hτ hτd hPr1 a
  choose Cj hCjt hCjb using hCj
  set cj : ℝ := ∑ a, (Cj a).toReal with hcj
  have hcj0 : 0 ≤ cj := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hCjle : ∀ a, Cj a ≤ ENNReal.ofReal cj := fun a => by
    rw [← ENNReal.ofReal_toReal (hCjt a)]
    exact ENNReal.ofReal_le_ofReal (Finset.single_le_sum (f := fun a => (Cj a).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ a))
  obtain ⟨CU, hCU, hU⟩ := nrstr_U_bound hd hs0 hsd hτ hτα
  obtain ⟨Cs, hCs, hS⟩ := nrstr_sob_Gamma hd1 hτ hτd2
  have h2τ : (0 : ℝ) < 2 ^ (τ / 2) := by positivity
  set CB : ℝ := CL * (cj * CU * Cs + 2 ^ (τ / 2)) with hCB
  have hCB0 : 0 ≤ CB := mul_nonneg hCL.le (add_nonneg (mul_nonneg (mul_nonneg hcj0 hCU.le) hCs.le) h2τ.le)
  refine ⟨CB, hCB0, fun V hVr K hv a c Γ hΓ hΓ0 => ?_⟩
  obtain ⟨L, F, hL0, hF0, hLip, ⟨w, hw, hwn⟩, hLF⟩ := hv
  have hLK : L ≤ K := by linarith
  have hFK : F ≤ K := by linarith
  have hK0 : 0 ≤ K := hL0.trans hLK
  have hVc : NRST.IsRealT (V c) := nrstr_isRealT_of_im (hVr c)
  have hmR : NRST.IsRealT (NRST.dd a (V c)) := hVc.dd a
  have hmΓ : NRST.IsRealT (NRST.dd a (V c) * Γ) := nrstr_isRealT_mul hmR hΓ
  set m : NRST.TPA d := NRST.dd a (V c) with hm
  set X : ℝ≥0∞ := eLpNorm (NRST.ev (NRST.lam τ Γ)) 2 volume with hX
  have hlam := nrstr_N2_lam_le_Jb hτ.le (m * Γ)
  have hLb := hL 1 one_pos le_rfl (fun x => (NRST.ev m x).re) (fun x => (NRST.ev Γ x).re)
    (fun x => (NRST.ev (m * Γ) x).re) (fun x => (NRST.ev (nrstr_Jb τ m) x).re)
    (fun x => (NRST.ev (nrstr_Jb τ Γ) x).re) (fun x => (NRST.ev (nrstr_Jb τ (m * Γ)) x).re)
    (nrstr_isSmooth_re m) (nrstr_isSmooth_re Γ) (fun x => nrstr_re_ev_mul hmR hΓ x)
    (nrstr_integrable_re _) (nrstr_integrable_re _) (nrstr_integrable_re _)
    (nrstr_besselRep hmR τ) (nrstr_besselRep hΓ τ) (nrstr_besselRep hmΓ τ)
  rw [nrstr_eLpNorm_re (nrstr_isRealT_Jb τ hmΓ), nrstr_eLpNorm_re (nrstr_isRealT_Jb τ hmR),
    nrstr_eLpNorm_re hΓ, nrstr_eLpNorm_re (nrstr_isRealT_Jb τ hΓ)] at hLb
  have hf : eLpNorm (fun x => (NRST.ev m x).re) ⊤ volume ≤ ENNReal.ofReal L :=
    nrstr_eLpNorm_top_re_le (norm_ev_dd_le_of_lip V hVr hL0 hLip a c)
  have hJm := hCjb a (V c)
  have hUb := hU V hVr F hF0 w hw hwn c
  have hQb := hS Γ hΓ hΓ0
  have hJΓ := nrstr_N2_Jb_le hτ.le Γ hΓ0
  have hmain : eLpNorm (NRST.ev (NRST.lam τ (m * Γ))) 2 volume ≤ X * ENNReal.ofReal (CB * K) := by
    calc eLpNorm (NRST.ev (NRST.lam τ (m * Γ))) 2 volume
        ≤ eLpNorm (NRST.ev (nrstr_Jb τ (m * Γ))) 2 volume := hlam
      _ ≤ ENNReal.ofReal CL * (eLpNorm (NRST.ev (nrstr_Jb τ m)) (ENNReal.ofReal ((d : ℝ) / τ)) volume *
            eLpNorm (NRST.ev Γ) (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 2 * τ))) volume +
          eLpNorm (NRST.ev (nrstr_Jb τ Γ)) 2 volume * eLpNorm (fun x => (NRST.ev m x).re) ⊤ volume) := hLb
      _ ≤ ENNReal.ofReal CL * ((ENNReal.ofReal cj * (ENNReal.ofReal CU * ENNReal.ofReal K)) *
            (ENNReal.ofReal Cs * X) + (ENNReal.ofReal (2 ^ (τ / 2)) * X) * ENNReal.ofReal K) := by
          refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
          · refine mul_le_mul' (hJm.trans (mul_le_mul' (hCjle a) (hUb.trans ?_))) hQb
            rw [ENNReal.ofReal_mul hCU.le]
            exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hFK)
          · exact mul_le_mul' hJΓ (hf.trans (ENNReal.ofReal_le_ofReal hLK))
      _ = X * (ENNReal.ofReal CL * (ENNReal.ofReal cj * ENNReal.ofReal CU * ENNReal.ofReal Cs +
            ENNReal.ofReal (2 ^ (τ / 2))) * ENNReal.ofReal K) := by ring
      _ = X * ENNReal.ofReal (CB * K) := by
          congr 1
          rw [hCB, ENNReal.ofReal_mul (mul_nonneg hCL.le (add_nonneg (mul_nonneg (mul_nonneg hcj0 hCU.le) hCs.le) h2τ.le)),
            ENNReal.ofReal_mul hCL.le, ENNReal.ofReal_add (mul_nonneg (mul_nonneg hcj0 hCU.le) hCs.le) h2τ.le,
            ENNReal.ofReal_mul (mul_nonneg hcj0 hCU.le), ENNReal.ofReal_mul hcj0]
  rw [nrstr_N2_lam τ (m * Γ)] at hmain
  rw [hX, nrstr_N2_lam τ Γ] at hmain
  have hmain' : ENNReal.ofReal (Real.sqrt (NRST.hom τ (m * Γ))) ≤
      ENNReal.ofReal (Real.sqrt (NRST.hom τ Γ) * (CB * K)) := by
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]; exact hmain
  have hs := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCB0 hK0))).1 hmain'
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rw [Real.sq_sqrt (NRST.hom_nonneg _ _), mul_pow, Real.sq_sqrt (NRST.hom_nonneg _ _)] at hsq
  nlinarith [hsq]

end HRS.Commutator.TorusNote
