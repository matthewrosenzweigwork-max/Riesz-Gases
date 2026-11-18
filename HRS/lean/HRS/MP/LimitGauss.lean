import HRS.MP.MartModulus
import HRS.MP.KolmChentsov
import HRS.MP.FidiCov

/-!
# Packet MPLGS: the limiting Gaussian stochastic convolution has a continuous version; S.A.24 (torus)

(A) `mlg_limit_cont`: a process `Y` with `Y_0 = 0` and the Gaussian structure of
`IsLinearFluctuationProcess` has a continuous `H^{-q_T}`-valued version on `[0,T]`.  Route:
Kolmogorov-Chentsov with `p = 4`, `β = 1` (`HRS.MP.KC.kolmogorov_modulus_tightness_proof`) for the single
process `Y`.  The increments `Y_t(e_k) - Y_s(e_k)` are centered Gaussian with variance
`‖h_t - h_s‖²_{L²(ρ dr dx)}` (the Gram representation `HRS.MP.FidiCov.fi3b_rep`), bounded by
`C jp_k^{2ℓ} |t-s|` by the sup bounds of `mmm_pde`; the fourth moment of a centered Gaussian is
`M v²`; the modes are summed with `mmm_sum_fourth`.

(B) `path_martingale_modulus_torus_proof`: the frozen lemma `path_martingale_modulus_torus`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.LimGauss

open HRS HRS.PDE HRS.Whole.AppendixALemmas HRS.MP.MartMod HRS.MP.KernIncr HRS.MP.FidiCov HRS.A33 HRS.A34

variable {d : ℕ}

/-! ### The Gaussian part -/

theorem mlg_gauss_fourth : ∃ M : ℝ, 0 ≤ M ∧ ∀ v : ℝ, 0 ≤ v →
    ∫⁻ y, ‖y‖ₑ ^ 4 ∂(gaussianReal 0 v.toNNReal) ≤ ENNReal.ofReal (M * v ^ 2) := by
  have hmem : MemLp id 4 (gaussianReal 0 1) := memLp_id_gaussianReal' 4 (by simp)
  have hfin : ∫⁻ z, ‖z‖ₑ ^ ((4 : ℝ≥0∞).toReal) ∂(gaussianReal 0 1) < ∞ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by simp) (by simp) hmem.eLpNorm_lt_top
  have h4 : ((4 : ℝ≥0∞).toReal) = 4 := by norm_num
  rw [h4] at hfin
  set m0 : ℝ≥0∞ := ∫⁻ z, ‖z‖ₑ ^ ((4 : ℝ)) ∂(gaussianReal 0 1) with hm0
  refine ⟨m0.toReal, ENNReal.toReal_nonneg, fun v hv => ?_⟩
  have hmap : gaussianReal 0 v.toNNReal = (gaussianReal 0 1).map (fun z => Real.sqrt v * z) := by
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero]
    congr 1
    ext
    simp [Real.sq_sqrt hv, hv]
  rw [hmap, lintegral_map (by fun_prop) (by fun_prop)]
  have : ∀ z : ℝ, ‖Real.sqrt v * z‖ₑ ^ 4 = ENNReal.ofReal (v ^ 2) * ‖z‖ₑ ^ 4 := by
    intro z
    rw [enorm_mul, mul_pow]
    congr 1
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    congr 1
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hv]
  simp_rw [this]
  rw [lintegral_const_mul _ (by fun_prop)]
  have h4' : ∀ z : ℝ, ‖z‖ₑ ^ (4 : ℕ) = ‖z‖ₑ ^ (4 : ℝ) := fun z => by
    rw [← ENNReal.rpow_natCast]; norm_num
  simp_rw [h4']
  rw [← hm0, ← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_mul (by positivity)]
  exact le_of_eq (by congr 1; rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg] ; ring)

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

theorem mlg_fourth_diff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (G : Ω → ℝ²)
    (hG : Measurable G) (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.PosSemidef)
    (hlaw : P.map G = multivariateGaussian 0 S) (M : ℝ)
    (hM : ∀ v : ℝ, 0 ≤ v → ∫⁻ y, ‖y‖ₑ ^ 4 ∂(gaussianReal 0 v.toNNReal) ≤ ENNReal.ofReal (M * v ^ 2)) :
    ∫⁻ ω, ‖G ω 0 - G ω 1‖ₑ ^ 4 ∂P ≤
      ENNReal.ofReal (M * (S 0 0 - S 0 1 - S 1 0 + S 1 1) ^ 2) := by
  set w : ℝ² := WithLp.toLp 2 ![1, -1] with hw
  set L : StrongDual ℝ ℝ² := innerSL ℝ w with hL
  have hLx : ∀ x : ℝ², L x = x 0 - x 1 := by
    intro x
    simp [hL, hw, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hvar : Var[L; multivariateGaussian (0 : ℝ²) S] = S 0 0 - S 0 1 - S 1 0 + S 1 1 := by
    have h1 := covarianceBilin_self (μ := multivariateGaussian (0 : ℝ²) S) IsGaussian.memLp_two_id w
    rw [covarianceBilin_multivariateGaussian hS] at h1
    have h2 : (fun u : ℝ² => (inner ℝ w u : ℝ)) = L := by
      funext u; rfl
    rw [h2] at h1
    rw [← h1]
    simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec, hw]
    ring
  have hmean : (multivariateGaussian (0 : ℝ²) S)[L] = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id L]
    simp
  have hmap : (multivariateGaussian (0 : ℝ²) S).map L = gaussianReal 0
      (S 0 0 - S 0 1 - S 1 0 + S 1 1).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal L, hmean, hvar]
  have hv0 : 0 ≤ S 0 0 - S 0 1 - S 1 0 + S 1 1 := by
    rw [← hvar]; exact variance_nonneg _ _
  calc ∫⁻ ω, ‖G ω 0 - G ω 1‖ₑ ^ 4 ∂P = ∫⁻ ω, ‖L (G ω)‖ₑ ^ 4 ∂P := by
        simp only [hLx]
    _ = ∫⁻ y, ‖L y‖ₑ ^ 4 ∂(P.map G) := by
        rw [lintegral_map (by fun_prop) hG]
    _ = ∫⁻ y, ‖y‖ₑ ^ 4 ∂((multivariateGaussian (0 : ℝ²) S).map L) := by
        rw [hlaw, lintegral_map (by fun_prop) (by fun_prop)]
    _ ≤ _ := by rw [hmap]; exact hM _ hv0

theorem mlg_eval_zero {m : ℝ} (φ : Torus d → ℝ) : NegSobolev.eval (0 : NegSobolev d m) φ = 0 := by
  have h0 : ∀ k : NonzeroLattice d, NegSobolev.fourierCoeff (0 : NegSobolev d m) k = 0 := by
    intro k
    have : NegSobolev.coord (0 : NegSobolev d m) k = 0 := rfl
    unfold NegSobolev.fourierCoeff
    rw [this, mul_zero]
  unfold NegSobolev.eval
  simp [h0]

/-! ### The variance of an increment -/

theorem mlg_norm_sq_le (w : Euc d) (B : ℝ) (h : ∀ j, |w j| ≤ B) : ‖w‖ ^ 2 ≤ d * B ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ j, ‖w j‖ ^ 2 ≤ ∑ _j : Fin d, B ^ 2 := Finset.sum_le_sum fun j _ => by
        rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
    _ = d * B ^ 2 := by simp

theorem mlg_rho_int {T : ℝ} {ρ : ℝ → Torus d → ℝ} (hρ : A33Rho T ρ) (c : ℝ → ℝ)
    (hc : Measurable c) {Bc : ℝ} (hb : ∀ r, |c r| ≤ Bc) :
    Integrable (fun p : ℝ × Torus d => ρ p.1 p.2 * c p.1) (a33_mu0 d T) ∧
    ∫ p, ρ p.1 p.2 * c p.1 ∂(a33_mu0 d T) = ∫ r in Set.Icc 0 T, c r := by
  obtain ⟨Bρ, hBρ⟩ := hρ.bound
  have hint : Integrable (fun p : ℝ × Torus d => ρ p.1 p.2 * c p.1) (a33_mu0 d T) := by
    refine Integrable.of_bound
      (hρ.aemeasurable.mul (hc.comp measurable_fst).aemeasurable).aestronglyMeasurable (Bρ * Bc) ?_
    filter_upwards [a33_ae_mu0 (d := d) T] with p hp
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hBρ p.1 hp p.2) (hb _) (abs_nonneg _) ((abs_nonneg _).trans (hBρ p.1 hp p.2))
  refine ⟨hint, ?_⟩
  have hprod : a33_mu0 d T = (volume.restrict (Set.Icc 0 T)).prod volume := rfl
  have hint' : Integrable (fun p : ℝ × Torus d => ρ p.1 p.2 * c p.1)
      ((volume.restrict (Set.Icc 0 T)).prod volume) := by rw [← hprod]; exact hint
  rw [hprod, integral_prod _ hint']
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  rw [integral_mul_const, hρ.one r hr, one_mul]

theorem mlg_cint {T s t a b : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    ∫ r in Set.Icc 0 T, ((Set.Icc 0 s).indicator (fun _ => a) r + (Set.Ioc s t).indicator (fun _ => b) r) =
      a * s + b * (t - s) := by
  have h1 : Integrable ((Set.Icc (0 : ℝ) s).indicator fun _ => a) (volume.restrict (Set.Icc 0 T)) :=
    (integrable_const a).indicator measurableSet_Icc
  have h2 : Integrable ((Set.Ioc s t).indicator fun _ => b) (volume.restrict (Set.Icc 0 T)) :=
    (integrable_const b).indicator measurableSet_Ioc
  rw [integral_add h1 h2, integral_indicator measurableSet_Icc, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Icc, Measure.restrict_restrict measurableSet_Ioc,
    setIntegral_const, setIntegral_const]
  have e1 : Set.Icc (0 : ℝ) s ∩ Set.Icc 0 T = Set.Icc 0 s :=
    Set.inter_eq_left.2 (Set.Icc_subset_Icc le_rfl (hst.trans htT))
  have e2 : Set.Ioc s t ∩ Set.Icc 0 T = Set.Ioc s t :=
    Set.inter_eq_left.2 fun x hx => ⟨hs.trans hx.1.le, hx.2.trans htT⟩
  rw [e1, e2]
  simp [Real.volume_real_Icc, Real.volume_real_Ioc, hs, hst, smul_eq_mul]
  ring

theorem mlg_X_bound {s t T C₂ C₃ u : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    s * (C₃ * (t - s) * u) ^ 2 + (t - s) * (C₂ * u) ^ 2 ≤
      u ^ 2 * (t - s) * (T ^ 2 * C₃ ^ 2 + C₂ ^ 2) := by
  have hδ : 0 ≤ t - s := sub_nonneg.2 hst
  set δ := t - s with hδdef
  have hδT : δ ≤ T := by linarith
  have hsT : s ≤ T := by linarith
  have hT : 0 ≤ T := by linarith
  have h1 : s * δ ≤ T * T := mul_le_mul hsT hδT hδ hT
  have h2 : s * δ ^ 2 ≤ T ^ 2 * δ := by
    have : s * δ ^ 2 = (s * δ) * δ := by ring
    rw [this]
    nlinarith
  have e : s * (C₃ * δ * u) ^ 2 + δ * (C₂ * u) ^ 2 = u ^ 2 * (C₃ ^ 2 * (s * δ ^ 2) + C₂ ^ 2 * δ) := by
    ring
  rw [e]
  have : C₃ ^ 2 * (s * δ ^ 2) ≤ C₃ ^ 2 * (T ^ 2 * δ) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  nlinarith

theorem mlg_pt {D : DynData d} {ρ : ℝ → Torus d → ℝ} {q : ℝ} (hq : 0 ≤ q) (e : Torus d → ℝ)
    {s t B₁ B₂ : ℝ} (hst : s ≤ t)
    (hB₁ : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x j, |Torus.grad (propagator D ρ r t e) x j| ≤ B₁)
    (hB₂ : ∀ r ∈ Set.Icc (0 : ℝ) s, ∀ x j,
      |Torus.grad (propagator D ρ r t e) x j - Torus.grad (propagator D ρ r s e) x j| ≤ B₂)
    (r : ℝ) (hr : 0 < r) (x : Torus d) :
    ‖a33_g D ρ q t e (r, x) - a33_g D ρ q s e (r, x)‖ ^ 2 ≤
      (Set.Icc 0 s).indicator (fun _ => 2 * q * d * B₂ ^ 2) r +
        (Set.Ioc s t).indicator (fun _ => 2 * q * d * B₁ ^ 2) r := by
  have hq2 : 0 ≤ 2 * q := by positivity
  by_cases h1 : r ≤ s
  · have hrs : r ∈ Set.Icc 0 s := ⟨hr.le, h1⟩
    have hrt : r ∈ Set.Icc 0 t := ⟨hr.le, h1.trans hst⟩
    have hs0 : 0 < s := hr.trans_le h1
    have ht0 : 0 < t := hs0.trans_le hst
    have hn : r ∉ Set.Ioc s t := fun h => absurd h.1 (not_lt.2 h1)
    simp only [a33_g, hrs, hs0, hrt, ht0, and_self, ite_true]
    rw [Set.indicator_of_mem hrs, Set.indicator_of_notMem hn, add_zero, ← smul_sub, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hq2]
    calc 2 * q * ‖Torus.grad (propagator D ρ r t e) x - Torus.grad (propagator D ρ r s e) x‖ ^ 2
        ≤ 2 * q * (d * B₂ ^ 2) := by
          refine mul_le_mul_of_nonneg_left (mlg_norm_sq_le _ _ fun j => ?_) hq2
          simpa [PiLp.sub_apply] using hB₂ r hrs x j
      _ = _ := by ring
  · by_cases h2 : r ≤ t
    · have hrt : r ∈ Set.Icc 0 t := ⟨hr.le, h2⟩
      have ht0 : 0 < t := hr.trans_le h2
      have hrs : r ∉ Set.Icc 0 s := fun h => h1 h.2
      have hn : r ∈ Set.Ioc s t := ⟨not_le.1 h1, h2⟩
      simp only [a33_g, hrt, ht0, and_self, ite_true, hrs, false_and, ite_false, sub_zero]
      rw [Set.indicator_of_notMem hrs, Set.indicator_of_mem hn, zero_add, norm_smul,
        mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hq2]
      calc 2 * q * ‖Torus.grad (propagator D ρ r t e) x‖ ^ 2 ≤ 2 * q * (d * B₁ ^ 2) := by
            refine mul_le_mul_of_nonneg_left (mlg_norm_sq_le _ _ fun j => ?_) hq2
            exact hB₁ r hrt x j
        _ = _ := by ring
    · have hrt : r ∉ Set.Icc 0 t := fun h => h2 h.2
      have hrs : r ∉ Set.Icc 0 s := fun h => h1 h.2
      have hn : r ∉ Set.Ioc s t := fun h => h2 h.2
      simp only [a33_g, hrt, hrs, false_and, ite_false, sub_zero, norm_zero]
      rw [Set.indicator_of_notMem hrs, Set.indicator_of_notMem hn]
      simp

theorem mlg_var {Rg : Regime} {MB Λ VB ν₀ T : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hA : AdjointData D.s (Main.gammaIdx d + 2) Rg MB Λ VB D ν₀ T ρ) {q : ℝ} (hq : 0 ≤ q) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (k : NonzeroLattice d) (s t : ℝ), s ∈ Set.Icc (0 : ℝ) T →
      t ∈ Set.Icc (0 : ℝ) T → s ≤ t →
      0 ≤ (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 0 0 -
        (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 0 1 -
        (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 1 0 +
        (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 1 1 ∧
      (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 0 0 -
        (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 0 1 -
        (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 1 0 +
        (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 1 1 ≤
      V * Lattice.jp k.1 ^ (2 * ((mStar d + 1 + 2 : ℕ) : ℝ)) * (t - s) := by
  have hd : 1 ≤ d := by
    have h0 := D.hs0
    have h1 := D.hsd
    have : (0 : ℝ) < d := lt_of_le_of_lt h0 h1
    exact_mod_cast this
  have hA' : AdjointData D.s (mStar d + 1 + 2) Rg MB Λ VB D ν₀ T ρ :=
    StabAux.adjointData_mono (by unfold Main.gammaIdx; omega) hA
  obtain ⟨hm, hm2⟩ := mmm_ell_bounds d
  obtain ⟨C₂, C₃, hC₂, hC₃, hP⟩ := mmm_pde hd D.s D.hs0 D.hsd (mStar d + 1) hm hm2 Rg ν₀ MB Λ T VB
    D.invβ
  set K : ℝ := T ^ 2 * C₃ ^ 2 + C₂ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * q * d * K, by positivity, ?_⟩
  intro k s t hs ht hst
  set ℓ : ℝ := ((mStar d + 1 + 2 : ℕ) : ℝ) with hℓ
  set u : ℝ := Lattice.jp k.1 ^ ℓ with hu
  set δ : ℝ := t - s with hδ
  have hsm := mpk_test_realMode (d := d) k
  have hnorm := mmm_sobolevNorm_realMode (d := d) ℓ k
  have hB₁ : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x j,
      |Torus.grad (propagator D ρ r t (Torus.realMode k)) x j| ≤ C₂ * u := by
    intro r hr x j
    have := (hP D ρ hA' le_rfl j x).1 r t hr.1 hr.2 ht.2 _ hsm.1
    rwa [hnorm] at this
  have hB₂ : ∀ r ∈ Set.Icc (0 : ℝ) s, ∀ x j,
      |Torus.grad (propagator D ρ r t (Torus.realMode k)) x j -
        Torus.grad (propagator D ρ r s (Torus.realMode k)) x j| ≤ C₃ * |t - s| * u := by
    intro r hr x j
    have := (hP D ρ hA' le_rfl j x).2 r s t hr.1 hr.2 hst ht.2 _ hsm.1
    rwa [hnorm] at this
  rw [abs_of_nonneg (sub_nonneg.2 hst)] at hB₂
  have hρ := fi3b_rho D ρ hA
  have hts : ∀ a : Fin 2, (![t, s] : Fin 2 → ℝ) a ∈ Set.Icc (0 : ℝ) T := by
    intro a
    fin_cases a
    · exact ht
    · exact hs
  have hφ : ∀ a : Fin 2, Torus.IsSmooth ((fun _ : Fin 2 => (Torus.realMode k : Torus d → ℝ)) a) :=
    fun _ => hsm.1
  have hrep := fi3b_rep D ρ hA hq ![t, s] hts (fun _ => (Torus.realMode k : Torus d → ℝ)) hφ
  obtain ⟨hmt, Bt, hBt⟩ := fi3b_facts D ρ hA q ht hsm.1
  obtain ⟨hms, Bs, hBs⟩ := fi3b_facts D ρ hA q hs hsm.1
  set H0 := a34_h D ρ q t (Torus.realMode k : Torus d → ℝ) with hH0
  set H1 := a34_h D ρ q s (Torus.realMode k : Torus d → ℝ) with hH1
  have i00 := fi3b_inner_int hρ D hmt hmt hBt hBt
  have i01 := fi3b_inner_int hρ D hmt hms hBt hBs
  have i10 := fi3b_inner_int hρ D hms hmt hBs hBt
  have i11 := fi3b_inner_int hρ D hms hms hBs hBs
  have e00 : (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 0 0 =
      ∫ p, inner ℝ (H0 p) (H0 p) ∂(a33_mu0 d T) := hrep 0 0
  have e01 : (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 0 1 =
      ∫ p, inner ℝ (H0 p) (H1 p) ∂(a33_mu0 d T) := hrep 0 1
  have e10 : (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 1 0 =
      ∫ p, inner ℝ (H1 p) (H0 p) ∂(a33_mu0 d T) := hrep 1 0
  have e11 : (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 1 1 =
      ∫ p, inner ℝ (H1 p) (H1 p) ∂(a33_mu0 d T) := hrep 1 1
  have j1 : Integrable (fun p => inner ℝ (H0 p) (H0 p) - inner ℝ (H0 p) (H1 p))
      (a33_mu0 d T) := i00.sub i01
  have j2 : Integrable (fun p => inner ℝ (H0 p) (H0 p) - inner ℝ (H0 p) (H1 p) -
      inner ℝ (H1 p) (H0 p)) (a33_mu0 d T) := j1.sub i10
  have hsum : Integrable (fun p => inner ℝ (H0 p) (H0 p) - inner ℝ (H0 p) (H1 p) -
      inner ℝ (H1 p) (H0 p) + inner ℝ (H1 p) (H1 p)) (a33_mu0 d T) := j2.add i11
  have hpw : ∀ p, inner ℝ (H0 p) (H0 p) - inner ℝ (H0 p) (H1 p) -
      inner ℝ (H1 p) (H0 p) + inner ℝ (H1 p) (H1 p) = ‖H0 p - H1 p‖ ^ 2 := by
    intro p
    have h1 := norm_sub_sq_real (H0 p) (H1 p)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm (H0 p) (H1 p)]
    linarith
  have hquad : (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 0 0 -
        (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 0 1 -
        (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 1 0 +
        (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) 1 1 =
      ∫ p, ‖H0 p - H1 p‖ ^ 2 ∂(a33_mu0 d T) := by
    rw [e00, e01, e10, e11]
    simp_rw [← hpw]
    rw [integral_add j2 i11, integral_sub j1 i10, integral_sub i00 i01]
  -- the bounding function
  set a : ℝ := 2 * q * d * (C₃ * δ * u) ^ 2 with ha
  set b : ℝ := 2 * q * d * (C₂ * u) ^ 2 with hb
  set cf : ℝ → ℝ := fun r => (Set.Icc 0 s).indicator (fun _ => a) r +
    (Set.Ioc s t).indicator (fun _ => b) r with hcf
  have hcfm : Measurable cf :=
    ((measurable_const.indicator measurableSet_Icc).add (measurable_const.indicator measurableSet_Ioc))
  have hcfb : ∀ r, |cf r| ≤ |a| + |b| := by
    intro r
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · by_cases h : r ∈ Set.Icc 0 s
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]; simp
    · by_cases h : r ∈ Set.Ioc s t
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]; simp
  obtain ⟨hcfi, hcfe⟩ := mlg_rho_int hρ cf hcfm hcfb
  have hae0 : ∀ᵐ p ∂(a33_mu0 d T), p.1 ≠ 0 := by
    have h0 : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 0 := by
      have := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
      filter_upwards [this] with r hr
      simpa using hr
    have h1 : ∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Icc 0 T)), r ≠ 0 :=
      ae_restrict_of_ae h0
    exact (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ).restrict (Set.Icc 0 T))
      (ν := (volume : Measure (Torus d)))).ae h1
  have hpt : ∀ᵐ p ∂(a33_mu0 d T), ‖H0 p - H1 p‖ ^ 2 ≤ ρ p.1 p.2 * cf p.1 := by
    filter_upwards [a33_ae_mu0 (d := d) T, hae0] with p hp hp0
    have hr0 : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    have hpt := mlg_pt (D := D) (ρ := ρ) hq (Torus.realMode k : Torus d → ℝ) hst hB₁ hB₂ p.1 hr0 p.2
    have hρ0 := hρ.nonneg p.1 hp p.2
    have e : H0 p - H1 p = Real.sqrt (ρ p.1 p.2) • (a33_g D ρ q t (Torus.realMode k) p -
        a33_g D ρ q s (Torus.realMode k) p) := by
      simp only [hH0, hH1, a34_h, smul_sub]
    rw [e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hρ0]
    exact mul_le_mul_of_nonneg_left hpt hρ0
  have hmono := integral_mono_ae (hsum.congr (Eventually.of_forall hpw)) hcfi hpt
  rw [hquad]
  refine ⟨integral_nonneg fun p => sq_nonneg _, hmono.trans ?_⟩
  rw [hcfe]
  have := mlg_cint (T := T) (a := a) (b := b) hs.1 hst ht.2
  rw [hcf]
  simp only
  rw [this]
  have hX := mlg_X_bound (T := T) (C₂ := C₂) (C₃ := C₃) (u := u) hs.1 hst ht.2
  calc a * s + b * (t - s) = 2 * q * d * (s * (C₃ * δ * u) ^ 2 + δ * (C₂ * u) ^ 2) := by
        rw [ha, hb, hδ]; ring
    _ ≤ 2 * q * d * (u ^ 2 * δ * K) := by
        refine mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 2 * q * d * K * Lattice.jp k.1 ^ (2 * ℓ) * (t - s) := by
        have : Lattice.jp k.1 ^ (2 * ℓ) = u ^ 2 := by
          rw [hu]; exact (Torus.jp_rpow_sq ℓ k.1).symm
        rw [this, hδ]; ring

/-! ### The fourth moment of an increment of the limiting convolution -/

theorem mlg_fourth_moment {Rg : Regime} {MB Λ VB ν₀ T : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hA : AdjointData D.s (Main.gammaIdx d + 2) Rg MB Λ VB D ν₀ T ρ) {q : ℝ} (hq : 0 ≤ q)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : ℝ → Ω' → NegSobolev d ((qT d : ℕ) : ℝ))
    (hY : Main.IsLinearFluctuationProcess P' D ρ ((qT d : ℕ) : ℝ) q T (fun _ => 0) Y) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖Y t ζ - Y s ζ‖ₑ ^ 4 ∂P' ≤ ENNReal.ofReal (C * |t - s| ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := mlg_gauss_fourth
  obtain ⟨V, hV0, hVb⟩ := mlg_var D ρ hA hq
  set A : ℝ := M * V ^ 2 with hAdef
  have hA0 : 0 ≤ A := by positivity
  set Lam : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) with hLam
  set Sm : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(3 * (d : ℝ) + 7)) with hSm
  refine ⟨Lam * Sm * A, ?_⟩
  set ℓ : ℝ := ((mStar d + 1 + 2 : ℕ) : ℝ) with hℓ
  have core : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T, s ≤ t →
      ∫⁻ ζ, ‖Y t ζ - Y s ζ‖ₑ ^ 4 ∂P' ≤ ENNReal.ofReal (Lam * Sm * A * |t - s| ^ 2) := by
    intro s hs t ht hst
    have hmeasF : Measurable fun ζ => Y t ζ - Y s ζ := (hY.meas t).sub (hY.meas s)
    have hmode : ∀ k : NonzeroLattice d, ∫⁻ ζ, ‖NegSobolev.fourierCoeff (Y t ζ - Y s ζ) k‖ₑ ^ 4 ∂P' ≤
        ENNReal.ofReal (A * Lattice.jp k.1 ^ (4 * ℓ) * |t - s| ^ 2) := by
      intro k
      have hsm := mpk_test_realMode (d := d) k
      have hts : ∀ a : Fin 2, (![t, s] : Fin 2 → ℝ) a ∈ Set.Icc (0 : ℝ) T := by
        intro a
        fin_cases a
        · exact ht
        · exact hs
      have hφ : ∀ a : Fin 2, Torus.IsSmooth ((fun _ : Fin 2 => (Torus.realMode k : Torus d → ℝ)) a) :=
        fun _ => hsm.1
      obtain ⟨-, hlaw⟩ := hY.gaussian_part 2 ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))
        hts hφ
      set G : Ω' → EuclideanSpace ℝ (Fin 2) := fun ω => WithLp.toLp 2 fun a : Fin 2 =>
        NegSobolev.eval (Y (![t, s] a) ω) (Torus.realMode k : Torus d → ℝ) with hG
      have hGeq : G = fun ω => (WithLp.toLp 2 (fun a : Fin 2 =>
          NegSobolev.eval (Y (![t, s] a) ω) ((fun _ : Fin 2 => (Torus.realMode k : Torus d → ℝ)) a) -
          NegSobolev.eval ((fun _ : Ω' => (0 : NegSobolev d ((qT d : ℕ) : ℝ))) ω)
            (propagator D ρ 0 (![t, s] a) ((fun _ : Fin 2 => (Torus.realMode k : Torus d → ℝ)) a))) :
          EuclideanSpace ℝ (Fin 2)) := by
        funext ω
        simp only [hG, mlg_eval_zero, sub_zero]
      have hlawG : P'.map G = multivariateGaussian 0
          (Main.surrogateCov D ρ q ![t, s] (fun _ => (Torus.realMode k : Torus d → ℝ))) := by
        rw [hGeq]
        exact hlaw
      have hmemq : MemSobolev ((qT d : ℕ) : ℝ) (Torus.realMode k : Torus d → ℝ) :=
        MFSemigroup.memSobolev_of_isSmooth hsm.1 _
      have hmeasG : Measurable G := by
        refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp ?_
        exact Measurable.of_eval fun a => (fi_eval_meas hmemq).comp (hY.meas _)
      have hpsd := fi3b_psd D ρ hA hq ![t, s] hts (fun _ => (Torus.realMode k : Torus d → ℝ)) hφ
      have h4 := mlg_fourth_diff P' G hmeasG _ hpsd hlawG M hM
      obtain ⟨hv0, hv1⟩ := hVb k s t hs ht hst
      have hae : ∀ ζ, NegSobolev.fourierCoeff (Y t ζ - Y s ζ) k = G ζ 0 - G ζ 1 := by
        intro ζ
        rw [mmm_fc_sub, ← mmm_eval_realMode, ← mmm_eval_realMode]
        rfl
      simp_rw [hae]
      refine h4.trans (ENNReal.ofReal_le_ofReal ?_)
      have hsq := pow_le_pow_left₀ hv0 hv1 2
      have hj : Lattice.jp k.1 ^ (4 * ℓ) = (Lattice.jp k.1 ^ (2 * ℓ)) ^ 2 := by
        rw [Torus.jp_rpow_sq]; congr 1; ring
      rw [hj, hAdef]
      calc M * _ ≤ M * (V * Lattice.jp k.1 ^ (2 * ℓ) * (t - s)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hM0
        _ = _ := by
            rw [abs_of_nonneg (sub_nonneg.2 hst)]; ring
    have hq' : ((qT d : ℕ) : ℝ) = ℓ + d + 2 := mmm_cast d
    have hs' := mmm_sum_fourth P' ℓ ((qT d : ℕ) : ℝ) hq' (fun ζ => Y t ζ - Y s ζ) hmeasF A
      (|t - s| ^ 2) hA0 (sq_nonneg _) hmode
    refine hs'.trans (le_of_eq ?_)
    congr 1; ring
  intro s hs t ht
  rcases le_total s t with h | h
  · exact core s hs t ht h
  · have := core t ht s hs h
    rw [abs_sub_comm] at this
    refine le_trans (le_of_eq ?_) this
    exact lintegral_congr fun ζ => by rw [enorm_sub_rev]

/-! ### (A) The continuous version -/

theorem mlg_rpow4 (x : ℝ≥0∞) : x ^ (4 : ℝ) = x ^ 4 := by
  rw [← ENNReal.rpow_natCast]; norm_num

theorem mlg_rpow2 (x : ℝ) : x ^ (1 + (1 : ℝ)) = x ^ 2 := by
  rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two]

theorem mlg_cvt_to_has {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {Ω' : Type} [MeasurableSpace Ω'] {T : ℝ} (P' : Measure Ω') (Y : ℝ → Ω' → E)
    (Zc : ℕ → ℝ → Ω' → E)
    (h : ContVersionTight T (fun _ : ℕ => P') (fun _ => Y) Zc) :
    HasContVersion T P' Y (Zc 1) := by
  obtain ⟨c1, c2, -⟩ := h
  refine ⟨fun t ht => c1 1 le_rfl t ht, ?_⟩
  filter_upwards [c2 1 le_rfl] with ζ hζ
  exact continuousOn_iff_continuous_restrict.2 hζ

theorem mlg_limit_cont {Rg : Regime} {MB Λ VB ν₀ T : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hA : AdjointData D.s (Main.gammaIdx d + 2) Rg MB Λ VB D ν₀ T ρ) {q : ℝ} (hq : 0 ≤ q)
    (hT : 0 < T) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : ℝ → Ω' → NegSobolev d ((qT d : ℕ) : ℝ))
    (hY : Main.IsLinearFluctuationProcess P' D ρ ((qT d : ℕ) : ℝ) q T (fun _ => 0) Y) :
    ∃ Yc, HasContVersion T P' Y Yc := by
  obtain ⟨C, hC⟩ := mlg_fourth_moment D ρ hA hq P' Y hY
  have hmom : ∀ N : ℕ, 1 ≤ N → ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖(fun (_ : ℕ) => Y) N t ζ - (fun (_ : ℕ) => Y) N s ζ‖ₑ ^ (4 : ℝ) ∂((fun _ : ℕ => P') N) ≤
        ENNReal.ofReal (C * |t - s| ^ (1 + (1 : ℝ))) := by
    intro N _ s hs t ht
    simp only [mlg_rpow4, mlg_rpow2]
    exact hC s hs t ht
  obtain ⟨Zc, hZc⟩ := HRS.MP.KC.kolmogorov_modulus_tightness_proof
    (E := NegSobolev d ((qT d : ℕ) : ℝ)) (Ω := fun _ : ℕ => Ω') T hT (fun _ => P')
    (fun _ => Y) (fun _ _ => hY.meas) 4 1 C (by norm_num) (by norm_num) hmom
  exact ⟨Zc 1, mlg_cvt_to_has P' Y Zc hZc⟩

/-! ### (B) Lemma S.A.24, torus -/

/-- Lemma S.A.24, torus (frozen statement `HRS.Whole.AppendixALemmas.path_martingale_modulus_torus`,
copied verbatim): conjunct 1 is `path_martingale_modulus_torus_moment`, conjunct 2 is Kolmogorov-Chentsov
(`p = 4`, `β = 1`), conjunct 3 is `mlg_limit_cont`. -/
theorem path_martingale_modulus_torus_proof (s : ℝ) (Rg : PDE.Regime)
    (ν₀ MB Λ T VB C₀ Cc νbar : ℝ) :
    ∃ C : ℝ, ∀ (S : Main.MainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      ∀ (R : ∀ N, Main.Realization d N) (𝔈 : ℕ → ℝ),
        Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) C₀ Cc 𝔈 →
        ∀ (ℱ : ∀ N, Filtration ℝ (R N).mΩ) (W' : ∀ N, ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
        (∀ N : ℕ, 1 ≤ N → IsFilteredSolution (R N).P (ℱ N) (W' N) (R N).W (R N).X) →
        ∀ (Mq : ∀ N, ℝ → (R N).Ω → NegSobolev d ((qT d : ℕ) : ℝ)),
        (∀ N : ℕ, 1 ≤ N → IsStochConvT (R N).P (ℱ N) (W' N) (S.dyn N) (S.ρ N) (S.sigma N)
          ((qT d : ℕ) : ℝ) T (R N).X (Mq N)) →
        (∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖Mq N t ζ - Mq N s' ζ‖ₑ ^ 4 ∂(R N).P ≤ ENNReal.ofReal (C * |t - s'| ^ 2)) ∧
        (∃ Zc, ContVersionTight (E := NegSobolev d ((qT d : ℕ) : ℝ)) T (fun N => (R N).P) Mq Zc) ∧
        (∀ L : Main.LimitCoeffs d,
          Main.CoeffConvergence S L Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) (Main.gammaIdx d) →
          ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
            (Y : ℝ → Ω' → NegSobolev d ((qT d : ℕ) : ℝ)),
          Main.IsLinearFluctuationProcess P' (L.dyn S) L.ρ ((qT d : ℕ) : ℝ) L.invβstar T
            (fun _ => 0) Y → ∃ Yc, HasContVersion T P' Y Yc) := by
  obtain ⟨C, hC⟩ := HRS.MP.MartMod.path_martingale_modulus_torus_moment (d := d) s Rg ν₀ MB Λ T VB
    C₀ Cc νbar
  refine ⟨C, fun S hs hT hν R 𝔈 hS ℱ W' hF Mq hM => ?_⟩
  have h1 := hC S hs hT hν R 𝔈 hS ℱ W' hF Mq hM
  have hTpos : 0 < T := hT ▸ S.hT
  refine ⟨h1, ?_, ?_⟩
  · have hmom : ∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∫⁻ ζ, ‖Mq N t ζ - Mq N s' ζ‖ₑ ^ (4 : ℝ) ∂(R N).P ≤
          ENNReal.ofReal (C * |t - s'| ^ (1 + (1 : ℝ))) := by
      intro N hN s' hs' t ht
      simp only [mlg_rpow4, mlg_rpow2]
      exact h1 N hN s' hs' t ht
    exact HRS.MP.KC.kolmogorov_modulus_tightness_proof (E := NegSobolev d ((qT d : ℕ) : ℝ))
      (Ω := fun N => (R N).Ω) T hTpos (fun N => (R N).P) Mq (fun N hN t => (hM N hN).1 t) 4 1 C
      (by norm_num) (by norm_num) hmom
  · intro L hcoef Ω' _ P' _ Y hY
    have hA : AdjointData (L.dyn S).s (Main.gammaIdx d + 2) Rg MB Λ VB (L.dyn S) ν₀ T L.ρ := by
      have := hcoef.limit_adjoint
      rw [hT] at this
      exact this
    exact mlg_limit_cont (L.dyn S) L.ρ hA L.hinvβstar hTpos P' Y hY

example := (@path_martingale_modulus_torus_proof :
  type_of% @HRS.Whole.AppendixALemmas.path_martingale_modulus_torus)

end HRS.MP.LimGauss
