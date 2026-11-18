import HRS.Sections.ScrnAux30
import HRS.Main.A8PAux4

/-!
# Packet SCRN, part 31: the transport seminorm of `-∇g` from `‖D²g‖_∞` and a weighted `ℓ²` sum

`scrn_transport`: for `C²` `g` with `‖D² lift g‖ ≤ B₂` and `∑ (2π|k|)^{d+4} ‖ĝ(k)‖² ≤ H²`,
`HasTransportBound d s (-∇g) (B₂ + d C_s H)` (Lipschitz part `B₂`; fractional part by the torus
Hardy-Littlewood-Sobolev inequality `a8p_fracDeriv_scalar`).  Contrast with `a8p_transport_bound`: no
`C⁰` term and no Sobolev norm, so the constants are sharp in `ℓ` and decay in time.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

open HRS.Main.A8P HRS.Uniform PDE

variable {d : ℕ}

lemma scrn_deriv_coeff_le {h : Torus d → ℝ} (hh : Torus.IsCk 1 h) (j : Fin d) (k : Lattice d) :
    ‖coeffOf (Torus.partialDeriv j h) k‖ ≤ 2 * Real.pi * Lattice.enorm k * ‖coeffOf h k‖ := by
  rw [coeffOf_partialDeriv j h hh]
  simp only [derivCoeff, norm_mul, Complex.norm_real, Complex.norm_I, Complex.norm_ofNat,
    mul_one, Real.norm_eq_abs]
  have hkj : |((k j : ℤ) : ℝ)| ≤ Lattice.enorm k := by
    have := PiLp.norm_apply_le (Lattice.toEuc k) j
    simpa [Lattice.toEuc, Lattice.enorm, Real.norm_eq_abs] using this
  rw [abs_of_pos Real.pi_pos]
  have : ‖((k j : ℤ) : ℂ)‖ = |((k j : ℤ) : ℝ)| := by
    rw [show (((k j : ℤ)) : ℂ) = (((k j : ℤ) : ℝ) : ℂ) by simp, Complex.norm_real, Real.norm_eq_abs]
  rw [this]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkj (by positivity)) (norm_nonneg _)

lemma scrn_fcoef_neg_fun (u : Torus d → ℝ) (k : Lattice d) :
    Torus.fcoef (fun x => -u x) k = -Torus.fcoef u k := by
  unfold Torus.fcoef
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_neg]

theorem scrn_scrnV_apply (g : Torus d → ℝ) (j : Fin d) (x : Torus d) :
    scrnV g x j = -Torus.partialDeriv j g x := by
  unfold scrnV
  have e := (scrn_inner_grad_eq_dirTor g (EuclideanSpace.single j (1 : ℝ)) x)
  rw [← scrn_partialDeriv_eq_dirTor] at e
  simp only [PiLp.neg_apply, neg_inj]
  simpa [EuclideanSpace.inner_single_right] using e

theorem scrn_transport (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (g : Torus d → ℝ) (B2 H : ℝ), 0 ≤ B2 → 0 ≤ H → Torus.IsCk 2 g →
      (∀ y : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift g) y‖ ≤ B2) →
      (Summable fun k : Lattice d => (2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 4) *
        ‖coeffOf g k‖ ^ 2) →
      (∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 4) * ‖coeffOf g k‖ ^ 2 ≤ H ^ 2) →
      HasTransportBound d s (scrnV g) (B2 + d * Cs * H) := by
  classical
  obtain ⟨Cs, hCs0, hCs⟩ : ∃ Cs : ℝ, 0 ≤ Cs ∧ (3 ≤ d → ∀ (v : Torus d → ℝ) (A : ℝ), 0 ≤ A → Integrable v →
      (Summable fun k : Lattice d => ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) *
        ‖Torus.fcoef v k‖ ^ 2) →
      (∑' k : Lattice d, ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) * ‖Torus.fcoef v k‖ ^ 2 ≤ A ^ 2) →
      ∃ w : Torus d → ℝ, MemLp w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ∧
        (∀ k : Lattice d, Torus.fcoef w k =
          (((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 1) / 2) : ℝ) : ℂ) * Torus.fcoef v k) ∧
        eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ≤ ENNReal.ofReal (Cs * A)) := by
    by_cases hd3 : 3 ≤ d
    · obtain ⟨C, hC0, hC⟩ := a8p_fracDeriv_scalar hd3
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hd3⟩
  refine ⟨Cs, hCs0, fun g B2 H hB2 hH hg hB hsum hbd => ?_⟩
  have hg1 : Torus.IsCk 1 g := hg.of_le (by exact_mod_cast (by norm_num : 1 ≤ 2))
  refine ⟨B2, d * Cs * H, hB2, by positivity, scrn_lipVF hg hB, fun hs => ?_, ?_⟩
  · have hd3 : 3 ≤ d := by
      by_contra h
      push Not at h
      have : (d : ℝ) ≤ 2 := by exact_mod_cast (by omega : d ≤ 2)
      linarith
    have hex : ∀ j : Fin d, ∃ w : Torus d → ℝ,
        MemLp w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ∧
          (∀ k : Lattice d, Torus.fcoef w k =
            (((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 1) / 2) : ℝ) : ℂ) *
              Torus.fcoef (Torus.partialDeriv j g) k) ∧
          eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ≤ ENNReal.ofReal (Cs * H) := fun j => by
      have hterm : ∀ k : Lattice d, ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) *
          ‖Torus.fcoef (Torus.partialDeriv j g) k‖ ^ 2 ≤
          (2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 4) * ‖coeffOf g k‖ ^ 2 := by
        intro k
        have hx : 0 ≤ 2 * Real.pi * Lattice.enorm k := scrn_two_pi_enorm_nonneg k
        have h1 := scrn_deriv_coeff_le hg1 j k
        rw [← coeffOf_eq_fcoef]
        have h2 : ‖coeffOf (Torus.partialDeriv j g) k‖ ^ 2 ≤
            ((2 * Real.pi * Lattice.enorm k) * ‖coeffOf g k‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        have h3 : (2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 4) =
            (2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2) * (2 * Real.pi * Lattice.enorm k) ^ 2 := by
          rw [← Real.rpow_natCast (2 * Real.pi * Lattice.enorm k) 2, ← Real.rpow_add' hx (by positivity)]
          congr 1; push_cast; ring
        rw [h3]
        calc (2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2) * ‖coeffOf (Torus.partialDeriv j g) k‖ ^ 2
            ≤ (2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2) *
              ((2 * Real.pi * Lattice.enorm k) * ‖coeffOf g k‖) ^ 2 :=
              mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx _)
          _ = _ := by ring
      have hsj : Summable fun k : Lattice d => ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) *
          ‖Torus.fcoef (Torus.partialDeriv j g) k‖ ^ 2 :=
        Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (scrn_two_pi_enorm_nonneg k) _)
          (sq_nonneg _)) hterm hsum
      have hbj : ∑' k : Lattice d, ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) *
          ‖Torus.fcoef (Torus.partialDeriv j g) k‖ ^ 2 ≤ H ^ 2 :=
        (hsj.tsum_le_tsum hterm hsum).trans hbd
      have hvint : Integrable (Torus.partialDeriv j g) := by
        have hcont : Continuous (Torus.partialDeriv j g) := continuous_partialDeriv j g hg1
        exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      exact hCs hd3 (Torus.partialDeriv j g) H hH hvint hsj hbj
    choose h hmem hcoef hhn using hex
    obtain ⟨hp1, hpq, hqt, -, -⟩ := dynconv_hls_exps hd3
    refine ⟨fun x => WithLp.toLp 2 (fun j => -h j x), ?_, ?_⟩
    · intro j k
      have hfun : (fun x => (WithLp.toLp 2 (fun j => -h j x) : Euc d) j) = fun x => -h j x := by
        funext x; simp
      rw [hfun, scrn_fcoef_neg_fun, hcoef j k]
      have hv : (fun x => scrnV g x j) = fun x => -Torus.partialDeriv j g x := by
        funext x; exact scrn_scrnV_apply g j x
      rw [hv, scrn_fcoef_neg_fun]; ring
    · have hwm : AEStronglyMeasurable (fun x => (WithLp.toLp 2 (fun j => -h j x) : Euc d)) volume := by
        refine AEMeasurable.aestronglyMeasurable ?_
        exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable
          (aemeasurable_pi_iff.2 fun j => (hmem j).aemeasurable.neg)
      have hle : ∀ x, ‖(WithLp.toLp 2 (fun j => -h j x) : Euc d)‖ ≤
          ‖(∑ j : Fin d, fun x => ‖h j x‖) x‖ := by
        intro x
        have h1 := HRS.Commutator.Whole.cmxHLS_norm_toLp_le (d := d) (fun j => -h j x)
        refine h1.trans (le_of_eq ?_)
        rw [Finset.sum_apply, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
        simp [Real.norm_eq_abs]
      calc eLpNorm (fun x => (WithLp.toLp 2 (fun j => -h j x) : Euc d))
            (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume
          ≤ eLpNorm (∑ j : Fin d, fun x => ‖h j x‖) (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume :=
            eLpNorm_mono hwm hle
        _ ≤ ∑ j : Fin d, eLpNorm (fun x => ‖h j x‖) (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume :=
            eLpNorm_sum_le (hp1.trans hpq).le
        _ ≤ ∑ _j : Fin d, ENNReal.ofReal (Cs * H) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [eLpNorm_norm _ (hmem j).aestronglyMeasurable]
            exact hhn j
        _ = ENNReal.ofReal (d * (Cs * H)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal (d * Cs * H) := by congr 1; ring
  · split_ifs
    · linarith
    · have : 0 ≤ (d : ℝ) * Cs * H := by positivity
      linarith

end HRS
