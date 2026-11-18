import HRS.MC.QRAsmFinal
import HRS.MC.E214PD
import HRS.MC.E214L1

/-!
# Packet E214L, part 3: pointwise-in-`t` version of `qrs_assembly_proof` (route fix of PLANREVIEW row 6)

`qrs_assembly_proof` uses the measurability and Wick hypotheses of `B, Bs` only at the final time `t`; this is the
same proof (copied verbatim) with these hypotheses stated at the single time `t`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214L

open HRS HRS.Sec7 HRS.MC.QRSpec HRS.MC.QRSpec.Asm

variable {d : ℕ}

theorem qrs_assembly_pointwise_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6)
    (h6a : type_of% (HRS.MC.L2C6a.l2c6a_proof R r hr))
    (h6b : type_of% (HRS.MC.L2C6b.l2c6b_proof R r hr))
    (h6c : type_of% (HRS.MC.L2C6c.l2c6c_proof R r hr))
    (hmode : type_of% @HRS.MC.L2C7.l2c7_proof)
    (hwci : type_of% @HRS.MC.WCI.wci_proof)
    (hmarg : type_of% (@HRS.MC.QRSpec.Marg.qrs_gauss_marginals_proof d R r hr))
    (hhd : ∃ C : ℝ, 0 < C ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → ∀ Mρ : ℝ, (∀ x, ρ x ≤ Mρ) →
      ∀ (k : NonzeroLattice d) (L : ℕ), 1 ≤ L →
        (Summable fun p : NonzeroLattice d × NonzeroLattice d =>
          wickCoeff (withDensityReal ρ) (hTransport d R.D.s (Torus.realMode k)) p.1 p.2 ^ 2) ∧
        tailHS (wickCoeff (withDensityReal ρ) (hTransport d R.D.s (Torus.realMode k))) ∅ ≤
          C * Lattice.jp k.1 ^ ((d : ℝ) + 3) ∧
        ∀ F : Finset (NonzeroLattice d), (∀ a : NonzeroLattice d, (∀ i, |a.1 i| ≤ (L : ℤ)) → a ∈ F) →
          tailHS (wickCoeff (withDensityReal ρ) (hTransport d R.D.s (Torus.realMode k))) F ≤
            C * Lattice.jp k.1 ^ ((d : ℝ) + 3) * (L : ℝ) ^ (-((d : ℝ) - 2 * R.D.s)))
    (hchaos : type_of% HRS.MC.QRSpec.Chaos.qrs_chaos_lp_lim_proof)
    (hgauss : type_of% HRS.MC.QRSpec.GaussEr.qrs_gauss_er_proof) :
    ∀ p : ℝ, 1 ≤ p → ∃ C c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Y₀ Ys₀ : Ω → NegSobolev d r) (η ηs : ℝ → Ω → NegSobolev d r),
        IsCenteredGaussianWithCov r (P.map Y₀)
          (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) →
        IsCenteredGaussianWithCov r (P.map Ys₀)
          (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρβ) R.β) →
        IndepFun Y₀ Ys₀ P →
        (∀ T : ℝ, IsLinearFluctuationSolution P R.D R.ρ r R.D.invβ T Y₀ η) →
        (∀ T : ℝ, IsLinearFluctuationSolution P R.D (fun _ => R.ρβ) r R.D.invβ T Ys₀ ηs) →
        IsSameNoise R.D R.ρ (fun _ => R.ρβ) r P Y₀ Ys₀ η ηs →
        ∀ (B Bs : ℝ → Ω → NegSobolev d r) (t : ℝ), 0 ≤ t →
          Measurable (B t) → Measurable (Bs t) →
          IsWickQuadraticField R.D.s P (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t) →
          IsWickQuadraticField R.D.s P (fun ω => ηs t ω) (withDensityReal R.ρβ) (Bs t) →
            eLpNorm (fun ω => B t ω - Bs t ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (C * Real.exp (-c * t)) := by
  intro p hp
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hs0 := R.D.hs0
  have hsd := R.D.hsd
  have hθ : 0 < (d : ℝ) - 2 * R.D.s := by have := R.hs; linarith
  set p' : ℝ := max p 2 with hp'
  have hp'2 : 2 ≤ p' := le_max_right _ _
  have hpp' : p ≤ p' := le_max_left _ _
  have hp'1 : 1 ≤ p' := by linarith
  obtain ⟨C6a, H6a⟩ := h6a
  obtain ⟨C6b, H6b⟩ := h6b
  obtain ⟨Cε, c0, hc0, H6c⟩ := h6c
  obtain ⟨Cch, hCch, Hch⟩ := hchaos p' hp'2
  obtain ⟨Cg, hCg, Hg⟩ := hgauss (2 * p') (by linarith)
  obtain ⟨Chd, hChd, Hhd⟩ := hhd
  obtain ⟨Mρ, Hρ, Hρβ, HρβM⟩ := asm_regime_density R
  set K : ℝ := max (max C6a C6b) 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hKa : C6a ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKb : C6b ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  set Cε' : ℝ := max Cε 0 with hCε'
  have hCε'0 : 0 ≤ Cε' := le_max_right _ _
  have hCεle : Cε ≤ Cε' := le_max_left _ _
  set Sr : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * r) with hSr
  have hSr0 : 0 ≤ Sr := tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  set SS : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * r) *
    (Lattice.jp k.1 ^ (((d : ℝ) + 3) / 2)) ^ 2 with hSS
  set Zc : ℝ := ((3 : ℝ) ^ d * (1 + 2 * Real.pi * Real.sqrt d) ^ r) ^ 2 with hZc
  have hZc0 : 0 ≤ Zc := sq_nonneg _
  set a1 : ℝ := 2 * Cch * K * Real.sqrt Chd with ha1
  set a2 : ℝ := Real.sqrt Chd * (Cg * Real.sqrt (Cε' * Sr)) *
    (Cg * Real.sqrt (Sr * K) + Cg * Real.sqrt (Sr * K)) * Zc with ha2
  have ha10 : 0 ≤ a1 := by positivity
  have ha20 : 0 ≤ a2 := by positivity
  obtain ⟨C', c', hC', hc', Hchoose⟩ := asm_choose_L (mm := 2 * (d : ℝ) + 2 * r) ha10 ha20 hθ
    (by positivity) hc0
  refine ⟨C' * Real.sqrt SS, c', hc', ?_⟩
  intro Ω _ P _ Y₀ Ys₀ η ηs hY hYs hind hη hηs hsame B Bs t ht hBm hBsm hB hBs
  have hηm : Measurable (η t) := (hη t).meas t
  have hηsm : Measurable (ηs t) := (hηs t).meas t
  obtain ⟨hG1, hG2, hG3⟩ := hmarg P Y₀ Ys₀ η ηs hY hYs hind hη hηs hsame t ht
  have hcov1 : ModeCovBound P (η t) K := asm_modeCov_mono hKa
    (hmode P r (η t) C6a (fun φ hφ => H6a P Y₀ η hY hη t ht φ hφ))
  have hcov2 : ModeCovBound P (ηs t) K := asm_modeCov_mono hKb
    (hmode P r (ηs t) C6b (fun φ hφ => H6b P Ys₀ ηs hYs hηs t ht φ hφ))
  have hmom1 : ∀ k, ∫ ω, NegSobolev.fourierCoeff (η t ω) k ^ 2 ∂P ≤ K := fun k => by
    simpa using hcov1 {k} (fun _ => 1)
  have hmom2 : ∀ k, ∫ ω, NegSobolev.fourierCoeff (ηs t ω) k ^ 2 ∂P ≤ K := fun k => by
    simpa using hcov2 {k} (fun _ => 1)
  have hε : ∀ k, ∫ ω, NegSobolev.fourierCoeff (η t ω - ηs t ω) k ^ 2 ∂P ≤
      Cε' * Real.exp (-c0 * t) := by
    intro k
    have h := (H6c P Y₀ Ys₀ η ηs hY hYs hind hη hηs hsame t ht (Torus.realMode k)
      (HRS.FieldSingAux.isSmooth_realMode k)).2
    simp only [Marg.qm_eval_realMode] at h
    have hl2 : PDE.l2NormSq (Torus.realMode k : Torus d → ℝ) = 1 := by
      simp [PDE.l2NormSq, sq, Torus.realMode_orthonormal]
    rw [hl2, mul_one] at h
    simp only [Marg.qm_fc_sub]
    exact h.trans (mul_le_mul_of_nonneg_right hCεle (Real.exp_pos _).le)
  have egr : ∀ (X : Ω → NegSobolev d r) (b : ℝ), Measurable X → HasFiniteGaussianCoeffs P X → 0 ≤ b →
      (∀ k, ∫ ω, NegSobolev.fourierCoeff (X ω) k ^ 2 ∂P ≤ b) →
      eLpNorm (fun ω => ‖X ω‖) (ENNReal.ofReal (2 * p')) P ≤
        ENNReal.ofReal (Cg * Real.sqrt (Sr * b)) := by
    intro X b hXm hXG hb hXb
    have hwm : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-2 * r) := asm_summable_w hr
    have hnn : ∀ k : NonzeroLattice d, 0 ≤ Lattice.jp k.1 ^ (-2 * r) *
        ∫ ω, NegSobolev.fourierCoeff (X ω) k ^ 2 ∂P := fun k =>
      mul_nonneg (Real.rpow_nonneg (Torus.jp_pos k.1).le _) (integral_nonneg fun ω => sq_nonneg _)
    have hle : ∀ k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * r) *
        ∫ ω, NegSobolev.fourierCoeff (X ω) k ^ 2 ∂P ≤ Lattice.jp k.1 ^ (-2 * r) * b := fun k =>
      mul_le_mul_of_nonneg_left (hXb k) (Real.rpow_nonneg (Torus.jp_pos k.1).le _)
    have hsm : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-2 * r) *
        ∫ ω, NegSobolev.fourierCoeff (X ω) k ^ 2 ∂P :=
      Summable.of_nonneg_of_le hnn hle (hwm.mul_right b)
    refine (Hg d r P X hXm hXG hsm).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hCg.le
    calc ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * r) * ∫ ω, NegSobolev.fourierCoeff (X ω) k ^ 2 ∂P
        ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * r) * b := hsm.tsum_le_tsum hle (hwm.mul_right b)
      _ = Sr * b := by rw [tsum_mul_right]
  have hNx := egr (η t) K hηm hG1 hK0 hmom1
  have hNy := egr (ηs t) K hηsm hG2 hK0 hmom2
  have hNδ := egr (fun ω => η t ω - ηs t ω) (Cε' * Real.exp (-c0 * t)) (hηm.sub hηsm) hG3
    (by positivity) hε
  have hNδeq : Real.sqrt (Sr * (Cε' * Real.exp (-c0 * t))) =
      Real.sqrt (Cε' * Sr) * Real.exp (-c0 * t / 2) := by
    rw [← asm_sqrt_eps Cε' Sr c0 t hCε'0 hSr0]; congr 1; ring
  obtain ⟨L, hL1, hLb⟩ := Hchoose t ht
  have hLpos : (0 : ℝ) < L := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    linarith
  set Mt : ℝ := a1 * (L : ℝ) ^ (-(((d : ℝ) - 2 * R.D.s) / 2)) +
    a2 * Real.exp (-c0 * t / 2) * (L : ℝ) ^ (2 * (d : ℝ) + 2 * r) with hMt
  have hMt0 : 0 ≤ Mt := by positivity
  have hmodes : ∀ k : NonzeroLattice d, eLpNorm (fun ω => NegSobolev.fourierCoeff (B t ω - Bs t ω) k)
      (ENNReal.ofReal p') P ≤ ENNReal.ofReal (Mt * Lattice.jp k.1 ^ (((d : ℝ) + 3) / 2)) := by
    intro k
    set j : ℝ := Lattice.jp k.1 ^ (((d : ℝ) + 3) / 2) with hj
    have hjpos : 0 < j := Real.rpow_pos_of_pos (Torus.jp_pos k.1) _
    set h := hTransport d R.D.s (Torus.realMode k) with hh
    obtain ⟨hsum1, hall1, htail1⟩ := Hhd (R.ρ t) (Hρ t ht).1 Mρ (Hρ t ht).2 k L hL1
    obtain ⟨hsum2, hall2, htail2⟩ := Hhd R.ρβ Hρβ Mρ HρβM k L hL1
    have hQm : AEStronglyMeasurable (fun ω => NegSobolev.eval (B t ω) (Torus.realMode k)) P := by
      simp only [Marg.qm_eval_realMode]; exact (asm_meas_fc (hBm) k).aestronglyMeasurable
    have hQsm : AEStronglyMeasurable (fun ω => NegSobolev.eval (Bs t ω) (Torus.realMode k)) P := by
      simp only [Marg.qm_eval_realMode]; exact (asm_meas_fc (hBsm) k).aestronglyMeasurable
    have t1 := Hch d r P (η t) hG1 K hK0 hcov1 _ _ _ (hB k) hQm hsum1 (asmCube d L)
    have t2 := Hch d r P (ηs t) hG2 K hK0 hcov2 _ _ _ (hBs k) hQsm hsum2 (asmCube d L)
    have hcube : ∀ a : NonzeroLattice d, (∀ i, |a.1 i| ≤ (L : ℤ)) → a ∈ asmCube d L :=
      fun a ha => mem_asmCube.2 ha
    have hT : ∀ tl : ℝ, tl ≤ Chd * Lattice.jp k.1 ^ ((d : ℝ) + 3) * (L : ℝ) ^ (-((d : ℝ) - 2 * R.D.s)) →
        Cch * K * Real.sqrt tl ≤ Cch * K * (Real.sqrt Chd * j *
          (L : ℝ) ^ (-(((d : ℝ) - 2 * R.D.s) / 2))) := by
      intro tl htl
      rw [← asm_sqrt_tail hChd.le (Torus.jp_pos k.1) hLpos d ((d : ℝ) - 2 * R.D.s)]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htl) (mul_nonneg hCch.le hK0)
    have hT0 : 0 ≤ Cch * K * (Real.sqrt Chd * j * (L : ℝ) ^ (-(((d : ℝ) - 2 * R.D.s) / 2))) := by positivity
    have T1 := t1.trans (ENNReal.ofReal_le_ofReal (hT _ (htail1 _ hcube)))
    have T2 := t2.trans (ENNReal.ofReal_le_ofReal (hT _ (htail2 _ hcube)))
    have hAA : wickCoeff (withDensityReal R.ρβ) h = wickCoeff (withDensityReal (R.ρ t)) h := by
      funext a b
      exact hwci R.D.s hs0 hsd R.ρβ (R.ρ t) Hρβ (Hρ t ht).1 Mρ HρβM (Hρ t ht).2 (Torus.realMode k)
        (HRS.FieldSingAux.isSmooth_realMode k) a b
    have T2' : eLpNorm (fun ω => NegSobolev.eval (Bs t ω) (Torus.realMode k) -
        asmSec P (wickCoeff (withDensityReal (R.ρ t)) h) (fun a ω => NegSobolev.fourierCoeff (ηs t ω) a)
          (asmCube d L) ω) (ENNReal.ofReal p') P ≤ ENNReal.ofReal (Cch * K * (Real.sqrt Chd * j *
          (L : ℝ) ^ (-(((d : ℝ) - 2 * R.D.s) / 2)))) := by
      rw [← hAA]; exact T2
    have hH : ∀ a b, |wickCoeff (withDensityReal (R.ρ t)) h a b| ≤ Real.sqrt Chd * j := by
      intro a b
      have := asm_entry_le hsum1 hall1 a b
      rwa [asm_sqrt_H hChd.le (Torus.jp_pos k.1) d] at this
    have key := asm_mode_bound (P := P) hr0 hp'1 (η t) (ηs t) hηm hηsm
      (wickCoeff (withDensityReal (R.ρ t)) h) (fun ω => NegSobolev.eval (B t ω) (Torus.realMode k))
      (fun ω => NegSobolev.eval (Bs t ω) (Torus.realMode k)) _ _ _
      (mul_nonneg hCg.le (Real.sqrt_nonneg _)) (mul_nonneg hCg.le (Real.sqrt_nonneg _))
      (mul_nonneg hCg.le (Real.sqrt_nonneg _)) hNδ hNx hNy (Real.sqrt Chd * j)
      (mul_nonneg (Real.sqrt_nonneg _) hjpos.le) hH L hL1 _ _ hT0 hT0 T1 T2'
    have e1 : (fun ω => NegSobolev.fourierCoeff (B t ω - Bs t ω) k) = fun ω =>
        NegSobolev.eval (B t ω) (Torus.realMode k) - NegSobolev.eval (Bs t ω) (Torus.realMode k) := by
      funext ω; rw [Marg.qm_fc_sub, Marg.qm_eval_realMode, Marg.qm_eval_realMode]
    rw [e1]
    refine key.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hNδeq]
    simp only [hMt, ha1, ha2, hZc]
    ring
  have hfin := asm_final_sum hr (fun ω => B t ω - Bs t ω) ((hBm).sub (hBsm)) hp'2 Mt hMt0 hmodes
  calc eLpNorm (fun ω => B t ω - Bs t ω) (ENNReal.ofReal p) P
      ≤ eLpNorm (fun ω => B t ω - Bs t ω) (ENNReal.ofReal p') P :=
        eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpp')
    _ = eLpNorm (fun ω => ‖B t ω - Bs t ω‖) (ENNReal.ofReal p') P :=
        (eLpNorm_norm _ ((hBm).sub (hBsm)).aestronglyMeasurable).symm
    _ ≤ ENNReal.ofReal (Mt * Real.sqrt SS) := hfin
    _ ≤ ENNReal.ofReal ((C' * Real.sqrt SS) * Real.exp (-c' * t)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := mul_le_mul_of_nonneg_right hLb (Real.sqrt_nonneg SS)
        linarith


section PairBExp

open HRS.MC.E214Plan HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} {sd : StatDatum S β₀ m hE}

theorem pair_B_exp_proof (pg : PairGD sd) (p : ℝ) (hp : 1 ≤ p) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
      eLpNorm (fun ω => ‖pg.B t ω - pg.Bs t ω‖) (ENNReal.ofReal p) pg.P ≤ ENNReal.ofReal (C * Real.exp (-c * t)) := by
  set R := regime S β₀ hE with hR
  obtain ⟨C₁, c, hc, H⟩ := qrs_assembly_pointwise_proof R (rLvl d) rfl
    (HRS.MC.L2C6a.l2c6a_proof R (rLvl d) rfl) (HRS.MC.L2C6b.l2c6b_proof R (rLvl d) rfl)
    (HRS.MC.L2C6c.l2c6c_proof R (rLvl d) rfl) (@HRS.MC.L2C7.l2c7_proof) (@HRS.MC.WCI.wci_proof)
    (HRS.MC.QRSpec.Marg.qrs_gauss_marginals_proof R (rLvl d) rfl)
    (HRS.MC.QRSpec.Hd.qrs_hd_commutator_tail_proof R.D.s R.D.hs0 R.hs R.hd)
    HRS.MC.QRSpec.Chaos.qrs_chaos_lp_lim_proof HRS.MC.QRSpec.GaussEr.qrs_gauss_er_proof p hp
  refine ⟨max C₁ 1, c, lt_max_of_lt_right one_pos, hc, ?_⟩
  obtain ⟨hY, hYs, hind, hη, hηs, hN⟩ := pg.pair
  have hs : sd.Ss.s = R.D.s := congrArg (fun D => D.s) sd.hD
  filter_upwards [pg.B_wick, pg.Bs_wick, ae_restrict_mem measurableSet_Ici] with t hBw hBsw ht
  have ht' : 0 ≤ t := ht
  have hBm : Measurable (pg.B t) := pg.B_meas.comp measurable_prodMk_left
  have hBsm : Measurable (pg.Bs t) := pg.Bs_meas.comp measurable_prodMk_left
  have hρt : sd.Ss.ρ t = R.ρβ := congrFun sd.hρ t
  rw [hρt, hs] at hBsw
  have h := H pg.P pg.Y₀ pg.Ys₀ pg.η pg.ηs hY hYs hind hη hηs hN pg.B pg.Bs t ht' hBm hBsm hBw hBsw
  have hn : eLpNorm (fun ω => ‖pg.B t ω - pg.Bs t ω‖) (ENNReal.ofReal p) pg.P =
      eLpNorm (fun ω => pg.B t ω - pg.Bs t ω) (ENNReal.ofReal p) pg.P :=
    eLpNorm_norm (fun ω => pg.B t ω - pg.Bs t ω) ((hBm.sub hBsm).aestronglyMeasurable)
  rw [hn]
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end PairBExp

end HRS.MC.E214L

end
