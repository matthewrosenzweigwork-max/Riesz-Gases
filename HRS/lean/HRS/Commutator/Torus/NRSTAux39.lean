import HRS.Commutator.Torus.NRSTAux38

/-!
# NRS-T, part 39: Sobolev for `Γ`, and the multiplier bound at a fixed exponent `τ`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ} {s : ℝ}

lemma nrstr_sob_Gamma (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) (hτd : τ < (d : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ Γ : NRST.TPA d, NRST.IsRealT Γ → Γ.coeff 0 = 0 →
      eLpNorm (NRST.ev Γ) (ENNReal.ofReal (2 * d / ((d : ℝ) - 2 * τ))) volume ≤
        ENNReal.ofReal C * eLpNorm (NRST.ev (NRST.lam τ Γ)) 2 volume := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 2 * τ := by linarith
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have hlt : (2 : ℝ≥0∞) < ENNReal.ofReal (2 * d / ((d : ℝ) - 2 * τ)) := by
    rw [h2]
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
    rw [lt_div_iff₀ hden]; linarith
  have hrel : (ENNReal.ofReal (2 * d / ((d : ℝ) - 2 * τ)))⁻¹ = (2 : ℝ≥0∞)⁻¹ - ENNReal.ofReal (τ / d) := by
    rw [nrstr_ofReal_inv_div (by positivity) hden, h2, ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    field_simp
  obtain ⟨C, hC, hH⟩ := nrstr_hls_trig hd hτ (p := 2) (by norm_num) hlt ENNReal.ofReal_lt_top hrel
  refine ⟨C, hC, fun Γ hΓ hΓ0 => ?_⟩
  have hl := nrstr_isRealT_lam τ hΓ
  have hcont : Continuous fun x => (NRST.ev (NRST.lam τ Γ) x).re :=
    Complex.continuous_re.comp (NRST.continuous_ev _)
  have hmem : MemLp (fun x => (NRST.ev (NRST.lam τ Γ) x).re) 2 volume :=
    hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have := hH Γ hΓ hΓ0 _ hmem (fun k => by
    rw [nrstr_fcoef_re hl]
    unfold NRST.lam
    rw [NRST.coeff_mulSeq])
  rwa [nrstr_eLpNorm_re hl] at this

end HRS.Commutator.TorusNote
