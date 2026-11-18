import HRS.Commutator.Torus.TSAMPAux9

/-!
# T-SAMP helpers, part 10: `potential_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tsamp_hls_exps (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    (1 : ℝ≥0∞) < 2 ∧ (2 : ℝ≥0∞) < ENNReal.ofReal (Whole.p2E d s) ∧
      ENNReal.ofReal (Whole.p2E d s) < ⊤ ∧ 0 < Whole.alphaE d s - 1 ∧
      (ENNReal.ofReal (Whole.p2E d s))⁻¹ =
        (2 : ℝ≥0∞)⁻¹ - ENNReal.ofReal ((Whole.alphaE d s - 1) / d) := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs2 : 0 < s + 2 := by linarith
  have hdpos : 0 < (d : ℝ) := by linarith
  refine ⟨by norm_num, ?_, ENNReal.ofReal_lt_top, ?_, ?_⟩
  · rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ENNReal.ofReal_lt_ofReal_iff (by unfold Whole.p2E; positivity)]
    unfold Whole.p2E
    rw [lt_div_iff₀ hs2]; linarith
  · unfold Whole.alphaE; linarith
  · rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by unfold Whole.p2E; positivity),
      ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_sub _ (by unfold Whole.alphaE; apply div_nonneg <;> linarith)]
    congr 1
    unfold Whole.p2E Whole.alphaE
    field_simp
    ring

theorem tsamp_potential_component (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∀ σ : SMT d, σ.IsFinite → ∀ j : Fin d,
      eLpNorm (fun x => (σ.convForce (gloForceT s η) x) j) (ENNReal.ofReal (Whole.p2E d s)) volume ≤
        ENNReal.ofReal C * (homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef)) ^ ((1 : ℝ) / 2) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hp1, hpq, hqt, hσpos, hrel⟩ := tsamp_hls_exps hd hs0 hsd
  obtain ⟨Ch, hCh, hhls⟩ := text_hls_main (d := d) hd1 (Whole.alphaE d s - 1) 2
    (ENNReal.ofReal (Whole.p2E d s)) hp1 hpq hqt hσpos hrel
  refine ⟨Ch * (|rieszConst d s| + 1), by positivity, fun η hη σ hσ j => ?_⟩
  set n : ℕ := ⌈2 / η⌉₊ with hn
  set e : Lattice d → ℂ := fun k => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s j k * σ.coef k with he
  have hT3 : HRS.PDE.IsTrigPoly n e := tkr_isTrigPoly hη (fun k hk => by
    intro h0; apply hk; simp [he, h0])
  set h : Torus d → ℝ := fun x => (σ.convForce (gloForceT s η) x) j with hh
  have hhe : ∀ x, ((h x : ℝ) : ℂ) = HRS.PDE.Kern.trig e x :=
    fun x => tsamp_convForce_trig hd hs0 hsd hη σ hσ x j
  have hcont : Continuous h := by
    have : h = fun x => (HRS.PDE.Kern.trig e x).re := by
      funext x; rw [← hhe x]; simp
    rw [this]
    exact Complex.continuous_re.comp (HRS.PDE.Kern.continuous_trig hT3)
  have hfc : ∀ k, Torus.fcoef h k = e k := tsamp_trig_fcoef hT3 hhe
  have hhint : Integrable h := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRe : HRS.PDE.IsRealCoeff e := by
    have h1 : HRS.PDE.coeffOf h = e := by
      funext k; rw [← tsamp_fcoef_eq_coeffOf, hfc]
    rw [← h1]
    exact HRS.PDE.isRealCoeff_coeffOf h hhint
  -- the Sobolev-weighted coefficients
  set r : Lattice d → ℝ := fun k => if k = 0 then 0 else (2 * Real.pi * Lattice.enorm k) ^ (Whole.alphaE d s - 1)
    with hr
  set dd : Lattice d → ℂ := fun k => ((r k : ℝ) : ℂ) * e k with hdd
  have hRd : HRS.PDE.IsRealCoeff dd := by
    intro k
    have h1 : e (-k) = (starRingEnd ℂ) (e k) := hRe k
    have h2 : r (-k) = r k := by simp [hr, HRS.enorm_neg]
    show ((r (-k) : ℝ) : ℂ) * e (-k) = (starRingEnd ℂ) (((r k : ℝ) : ℂ) * e k)
    have h3 : (starRingEnd ℂ) (((r k : ℝ) : ℂ) * e k) =
        ((r k : ℝ) : ℂ) * (starRingEnd ℂ) (e k) := by
      rw [map_mul (starRingEnd ℂ) ((r k : ℝ) : ℂ) (e k), Complex.conj_ofReal]
    rw [h2, h1, h3]
  have hTd : HRS.PDE.IsTrigPoly n dd := fun k hk => hT3 k (fun h0 => hk (by simp [hdd, h0]))
  obtain ⟨f, hfcont, hf, hffc⟩ := tsamp_real_trig hRd hTd
  have hfmem : MemLp f 2 volume := HRS.PDE.R2Aux.memLp_of_continuous_real hfcont
  have hf0 : Torus.fcoef f 0 = 0 := by
    rw [hffc 0]; simp [hdd, hr]
  obtain ⟨h', hh'mem, hh'0, hh'k, hh'n⟩ := hhls f hfmem hf0
  have e0 : e 0 = 0 := by simp [he, tkrCI]
  have hfc' : ∀ k, Torus.fcoef h' k = e k := by
    intro k
    by_cases hk : k = 0
    · rw [hk, hh'0, e0]
    · rw [hh'k k hk, hffc k]
      simp only [hdd, hr, hk, if_false]
      have hten : 0 < 2 * Real.pi * Lattice.enorm k := by
        have := HRS.one_le_enorm k hk
        positivity
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hten]
      simp
  have hh'int : Integrable h' := hh'mem.integrable (by
    exact le_of_lt (lt_trans hp1 hpq))
  have hae : h =ᵐ[volume] h' := by
    have := text_ae_eq_zero_of_fcoef (g := fun x => h' x - h x) (hh'int.sub hhint) (fun k => by
      rw [text_fcoef_sub hh'int hhint, hfc', hfc]; ring)
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  rw [eLpNorm_congr_ae hae]
  refine hh'n.trans ?_
  rw [tsamp_eLpNorm_trig hTd hfcont hf]
  have hS := tsamp_sum_le_hom hd hs0 hsd hη σ j n
  have hS' : ENNReal.ofReal (∑ k ∈ HRS.PDE.Kern.boxF d n, ‖dd k‖ ^ 2) ≤
      ENNReal.ofReal (rieszConst d s ^ 2) * homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef) := by
    refine le_trans (le_of_eq ?_) hS
    congr 2
  have hsq : 0 ≤ ∑ k ∈ HRS.PDE.Kern.boxF d n, ‖dd k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
  have hrpow : ENNReal.ofReal ((∑ k ∈ HRS.PDE.Kern.boxF d n, ‖dd k‖ ^ 2) ^ ((2 : ℝ)⁻¹)) ≤
      ENNReal.ofReal |rieszConst d s| * (homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef)) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hsq (by norm_num)]
    calc (ENNReal.ofReal (∑ k ∈ HRS.PDE.Kern.boxF d n, ‖dd k‖ ^ 2)) ^ ((2 : ℝ)⁻¹)
        ≤ (ENNReal.ofReal (rieszConst d s ^ 2) *
            homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef)) ^ ((2 : ℝ)⁻¹) :=
          ENNReal.rpow_le_rpow hS' (by norm_num)
      _ = ENNReal.ofReal |rieszConst d s| *
            (homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef)) ^ ((1 : ℝ) / 2) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← one_div,
            ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num)]
          congr 2
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  calc ENNReal.ofReal Ch * ENNReal.ofReal ((∑ k ∈ HRS.PDE.Kern.boxF d n, ‖dd k‖ ^ 2) ^ ((2 : ℝ)⁻¹))
      ≤ ENNReal.ofReal Ch * (ENNReal.ofReal |rieszConst d s| *
          (homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef)) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_right hrpow _
    _ ≤ ENNReal.ofReal (Ch * (|rieszConst d s| + 1)) *
          (homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef)) ^ ((1 : ℝ) / 2) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCh.le]
        refine mul_le_mul_left ?_ _
        exact ENNReal.ofReal_le_ofReal (by nlinarith)


lemma tsamp_convForce_continuous (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ}
    (hη : 0 < η) (σ : SMT d) (hσ : σ.IsFinite) :
    Continuous (fun x => σ.convForce (gloForceT s η) x) := by
  refine tsamp_continuous_euc fun j => ?_
  set e : Lattice d → ℂ := fun k => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s j k * σ.coef k with he
  have hT3 : HRS.PDE.IsTrigPoly ⌈2 / η⌉₊ e := tkr_isTrigPoly hη (fun k hk => by
    intro h0; apply hk; simp [he, h0])
  have : (fun x => (σ.convForce (gloForceT s η) x) j) = fun x => (HRS.PDE.Kern.trig e x).re := by
    funext x
    rw [← tsamp_convForce_trig hd hs0 hsd hη σ hσ x j]; simp
  rw [this]
  exact Complex.continuous_re.comp (HRS.PDE.Kern.continuous_trig hT3)

theorem tsamp_potential_core (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ σ : SMT d, σ.IsFinite →
      eLpNorm (fun x => ‖σ.convForce (gloForceT s η) x‖) (ENNReal.ofReal (Whole.p2E d s)) volume ≤
        ENNReal.ofReal C * (homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef)) ^ ((1 : ℝ) / 2) := by
  obtain ⟨C₁, hC₁, hcomp⟩ := tsamp_potential_component hd hs0 hsd
  have hd1 : 1 ≤ d := by omega
  refine ⟨d * C₁, by have : (0 : ℝ) < d := by exact_mod_cast hd1
                     positivity, fun η hη _ σ hσ => ?_⟩
  set V : Torus d → Euc d := fun x => σ.convForce (gloForceT s η) x with hV
  have hVc : Continuous V := tsamp_convForce_continuous hd hs0 hsd hη σ hσ
  have hle : ∀ x, ‖V x‖ ≤ ∑ j, ‖V x j‖ := fun x => by
    have := Whole.cmxHLS_norm_toLp_le (d := d) (fun j => V x j)
    simpa using this
  have h1 : eLpNorm (fun x => ‖V x‖) (ENNReal.ofReal (Whole.p2E d s)) volume ≤
      eLpNorm (fun x => ∑ j, ‖V x j‖) (ENNReal.ofReal (Whole.p2E d s)) volume := by
    refine eLpNorm_mono_ae (hVc.norm.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
    exact hle x
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Whole.p2E d s) := by
    obtain ⟨hp1, hpq, -⟩ := tsamp_hls_exps hd hs0 hsd
    exact le_of_lt (lt_trans hp1 hpq)
  have h2 : eLpNorm (fun x => ∑ j, ‖V x j‖) (ENNReal.ofReal (Whole.p2E d s)) volume ≤
      ∑ j, eLpNorm (fun x => ‖V x j‖) (ENNReal.ofReal (Whole.p2E d s)) volume := by
    have := eLpNorm_sum_le (μ := (volume : Measure (Torus d))) (s := Finset.univ)
      (f := fun j x => ‖V x j‖) hp1
    convert this using 2
    funext x; simp
  have h3 : ∀ j, eLpNorm (fun x => ‖V x j‖) (ENNReal.ofReal (Whole.p2E d s)) volume ≤
      ENNReal.ofReal C₁ * (homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef)) ^ ((1 : ℝ) / 2) := by
    intro j
    rw [eLpNorm_norm]
    · exact hcomp η hη σ hσ j
    · exact ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp hVc).aestronglyMeasurable
  calc eLpNorm (fun x => ‖V x‖) (ENNReal.ofReal (Whole.p2E d s)) volume
      ≤ ∑ j : Fin d, (ENNReal.ofReal C₁ * (homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef)) ^ ((1 : ℝ) / 2)) :=
        h1.trans (h2.trans (Finset.sum_le_sum fun j _ => h3 j))
    _ = ENNReal.ofReal (d * C₁) * (homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef)) ^ ((1 : ℝ) / 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast, mul_assoc]

end HRS.Commutator.TorusNote
