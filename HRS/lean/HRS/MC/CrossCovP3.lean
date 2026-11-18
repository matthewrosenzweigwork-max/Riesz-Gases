import HRS.Main.HeadlineEdgeworth
import HRS.PDE.MeanFieldProduct
import HRS.PDE.MeanFieldAprioriClassical
import HRS.PDE.MeanFieldAprioriPositive
import HRS.PDE.EnergyDrift
import HRS.PDE.Hadamard
import HRS.PDE.Uniqueness
import HRS.Uniform.Q54Aux5
import HRS.Kernel.ResponseAux
import HRS.MC.IID3
import HRS.PDE.Classical
import HRS.Equilibrium.PoleCavity

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CrossCov

open HRS HRS.Main

variable {d : ℕ}

section P3Aux

open HRS.PDE HRS.PDE.MFProduct

theorem p_cc3_memHs_mono {m n : ℝ} (hmn : m ≤ n) {c : Coeff d} (hc : MemHs n c) :
    MemHs m c := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (MFProduct.sobWeight_nonneg m k) (sq_nonneg _))
    (fun k => ?_) hc
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  unfold sobWeight
  exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (by positivity)) hmn

theorem p_cc3_memHs_sub_smul {m : ℝ} {x y : Coeff d} (hx : MemHs m x) (hy : MemHs m y) (z : ℂ) :
    MemHs m (fun k => x k - z * y k) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (MFProduct.sobWeight_nonneg m k) (sq_nonneg _))
    (fun k => ?_) ((hx.mul_left 2).add (hy.mul_left (2 * ‖z‖ ^ 2)))
  have h1 : ‖x k - z * y k‖ ≤ ‖x k‖ + ‖z‖ * ‖y k‖ := (norm_sub_le _ _).trans (by rw [norm_mul])
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2 : ‖x k - z * y k‖ ^ 2 ≤ 2 * ‖x k‖ ^ 2 + 2 * ‖z‖ ^ 2 * ‖y k‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x k‖ - ‖z‖ * ‖y k‖)]
  have hw := MFProduct.sobWeight_nonneg m k
  calc sobWeight m k * ‖x k - z * y k‖ ^ 2
      ≤ sobWeight m k * (2 * ‖x k‖ ^ 2 + 2 * ‖z‖ ^ 2 * ‖y k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hw
    _ = _ := by ring

theorem p_cc3_memHs_zero {u : Torus d → ℝ} (hu : MemLp u 2 volume) : MemHs 0 (coeffOf u) := by
  rw [memHs_zero_iff]
  have hF : MemLp (fun x => (u x : ℂ)) 2 volume := hu.ofReal
  have h := hasSum_parseval _ _ hF hF
  have hs : Summable fun n : Lattice d => ((‖coeffOf u n‖ ^ 2 : ℝ) : ℂ) := by
    refine h.summable.congr fun n => ?_
    show (starRingEnd ℂ) (coeffOf u n) * coeffOf u n = _
    rw [Complex.conj_mul']
    push_cast
    ring
  exact Complex.summable_ofReal.1 hs

theorem p_cc3_bdd {f : Torus d → ℝ} (hf : Continuous f) : ∃ C : ℝ, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_range hf).isBounded.exists_norm_le
  exact ⟨C, fun x => by simpa using hC _ (Set.mem_range_self x)⟩

theorem p_cc3_isCk {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (n : ℕ) : Torus.IsCk n φ := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) := hφ
  exact h.of_le (by exact_mod_cast le_top)

theorem p_cc3_continuous {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Continuous φ := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) := hφ
  exact Torus.continuous_of_continuous_lift h.continuous

theorem p_cc3_smooth_mul {f g : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) :
    Torus.IsSmooth fun x => f x * g x := by
  unfold Torus.IsSmooth Torus.IsCk at *
  exact hf.mul hg

theorem p_cc3_smooth_sub {f g : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) :
    Torus.IsSmooth fun x => f x - g x := by
  unfold Torus.IsSmooth Torus.IsCk at *
  exact hf.sub hg

theorem p_cc3_smooth_const (c : ℝ) : Torus.IsSmooth fun _ : Torus d => c := by
  unfold Torus.IsSmooth Torus.IsCk
  exact contDiff_const

theorem p_cc3_memHs_smooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (b : ℝ) :
    MemHs b (coeffOf φ) := by
  obtain ⟨n, hn⟩ := exists_nat_ge b
  exact p_cc3_memHs_mono hn (PDE.memHs_coeffOf_cbNorm n φ (p_cc3_isCk hφ n)).1

theorem p_cc3_weighted_summable {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (b : ℝ) :
    Summable fun k => sobWeight (b / 2) k * ‖coeffOf φ k‖ := by
  obtain ⟨N, hN⟩ := exists_nat_ge b
  obtain ⟨n, hn⟩ := exists_nat_gt ((d : ℝ) / 2 + N)
  have hs := summable_jp_pow_norm (n : ℝ) _ (p_cc3_memHs_smooth hφ n) N hn
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (norm_nonneg _))
    (fun k => ?_) hs
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [sobWeight_eq_jp, show 2 * (b / 2) = b by ring, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one k) hN

theorem p_cc3_riesz_gain {s : ℝ} (hsd : s < d) (a : ℝ) (c : Coeff d) (hc : MemHs a c) :
    MemHs (a + ((d : ℝ) - s)) (rieszMult d s c) := by
  have hm : ∀ k : Lattice d, sobWeight ((d : ℝ) - s) k * ‖((rieszCoeff d s k : ℝ) : ℂ)‖ ^ 2 ≤
      (HRS.Uniform.Q54.Cg d s) ^ 2 := by
    intro k
    rw [sobWeight_eq_jp, Complex.norm_real, Real.norm_eq_abs]
    have h1 := HRS.Uniform.Q54.abs_rieszCoeff_le_jp s hsd k
    have hj := Torus.jp_pos k
    have h2 : Lattice.jp k ^ (2 * ((d : ℝ) - s)) * |rieszCoeff d s k| ^ 2 =
        (Lattice.jp k ^ ((d : ℝ) - s) * |rieszCoeff d s k|) ^ 2 := by
      rw [mul_pow, Torus.jp_rpow_sq]
    rw [h2]
    have h3 : Lattice.jp k ^ ((d : ℝ) - s) * |rieszCoeff d s k| ≤ HRS.Uniform.Q54.Cg d s := by
      calc _ ≤ Lattice.jp k ^ ((d : ℝ) - s) * (HRS.Uniform.Q54.Cg d s * Lattice.jp k ^ (s - d)) := by
            gcongr
        _ = HRS.Uniform.Q54.Cg d s * (Lattice.jp k ^ ((d : ℝ) - s) * Lattice.jp k ^ (s - (d : ℝ))) := by
            ring
        _ = HRS.Uniform.Q54.Cg d s := by rw [← Real.rpow_add hj]; simp
    exact pow_le_pow_left₀ (by positivity) h3 2
  exact (HRS.PDE.MFApriori.Aux.hs_mult (fun k : Lattice d => ((rieszCoeff d s k : ℝ) : ℂ)) a
    ((d : ℝ) - s) (HRS.Uniform.Q54.Cg d s) (HRS.Uniform.Q54.Cg_nonneg d s) hm c hc).1

/-- Multiplication by a coefficient sequence with a weighted `ℓ¹` bound preserves `H^a`. -/
theorem p_cc3_mulCoeff_memHs (a : ℝ) (ha : 0 ≤ a) (f c : Coeff d)
    (hf1 : Summable fun k => ‖f k‖)
    (hfw : Summable fun k => sobWeight (a / 2) k * ‖f k‖) (hc : MemHs a c) :
    MemHs a (mulCoeff f c) := by
  set w : Lattice d → ℝ := sobWeight (a / 2) with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => MFProduct.sobWeight_nonneg _ k
  have hC2 : Summable fun k => (w k * ‖c k‖) ^ 2 := hc.congr fun k => by
    rw [mul_pow, hw, sobWeight_half_sq]
  have hc0 : MemHs 0 c := p_cc3_memHs_mono ha hc
  have hC0 : Summable fun k => ‖c k‖ ^ 2 := (memHs_zero_iff c).1 hc0
  obtain ⟨hQs, hQ2, -⟩ := young_nonneg (fun k => ‖f k‖) (fun k => w k * ‖c k‖)
    (fun _ => norm_nonneg _) (fun k => mul_nonneg (hw0 k) (norm_nonneg _)) hf1 hC2
  obtain ⟨hPs, hP2, -⟩ := young_nonneg (fun k => w k * ‖f k‖) (fun k => ‖c k‖)
    (fun k => mul_nonneg (hw0 k) (norm_nonneg _)) (fun _ => norm_nonneg _) hfw hC0
  obtain ⟨hSs, -, -⟩ := young_nonneg (fun k => ‖f k‖) (fun k => ‖c k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hf1 hC0
  set P := conv (fun k => w k * ‖f k‖) (fun k => ‖c k‖) with hP
  set Q := conv (fun k => ‖f k‖) (fun k => w k * ‖c k‖) with hQ
  have hP0 : ∀ k, 0 ≤ P k := fun k =>
    conv_nonneg (fun k => mul_nonneg (hw0 k) (norm_nonneg _)) (fun _ => norm_nonneg _) k
  have hQ0 : ∀ k, 0 ≤ Q k :=
    conv_nonneg (fun _ => norm_nonneg _) (fun k => mul_nonneg (hw0 k) (norm_nonneg _))
  obtain ⟨hPQs, -⟩ := minkowski_sq P Q hP0 hQ0 hP2 hQ2
  have hpt : ∀ k, w k * ‖mulCoeff f c k‖ ≤ 2 ^ a * (P k + Q k) := by
    intro k
    have hS := hSs k
    have ht1 : Summable fun j => (w (k - j) * ‖f (k - j)‖) * ‖c j‖ := hPs k
    have ht2 : Summable fun j => ‖f (k - j)‖ * (w j * ‖c j‖) := hQs k
    have hnm := norm_mulCoeff_le_conv f c k hS
    have hterm : ∀ j, w k * (‖f (k - j)‖ * ‖c j‖) ≤
        2 ^ a * ((w (k - j) * ‖f (k - j)‖) * ‖c j‖ + ‖f (k - j)‖ * (w j * ‖c j‖)) := by
      intro j
      have h1 : w k ≤ 2 ^ a * (w (k - j) + w j) := by
        have := sobWeight_add_le a ha (k - j) j
        rwa [sub_add_cancel] at this
      have h2 : 0 ≤ ‖f (k - j)‖ * ‖c j‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc w k * (‖f (k - j)‖ * ‖c j‖) ≤ (2 ^ a * (w (k - j) + w j)) * (‖f (k - j)‖ * ‖c j‖) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = _ := by ring
    calc w k * ‖mulCoeff f c k‖ ≤ w k * conv (fun k => ‖f k‖) (fun k => ‖c k‖) k :=
          mul_le_mul_of_nonneg_left hnm (hw0 k)
      _ = ∑' j, w k * (‖f (k - j)‖ * ‖c j‖) := by unfold conv; rw [tsum_mul_left]
      _ ≤ ∑' j, 2 ^ a * ((w (k - j) * ‖f (k - j)‖) * ‖c j‖ + ‖f (k - j)‖ * (w j * ‖c j‖)) :=
          (hS.mul_left _).tsum_le_tsum hterm ((ht1.add ht2).mul_left _)
      _ = 2 ^ a * (P k + Q k) := by
          rw [tsum_mul_left, ht1.tsum_add ht2]
          rfl
  have hm0 : ∀ k, 0 ≤ w k * ‖mulCoeff f c k‖ := fun k => mul_nonneg (hw0 k) (norm_nonneg _)
  have h2a : (0 : ℝ) ≤ 2 ^ a := by positivity
  obtain ⟨hms, -⟩ := sq_summable_le_mul h2a hm0 hpt hPQs
  exact hms.congr fun k => by rw [mul_pow, hw, sobWeight_half_sq]

theorem p_cc3_coeff_cv (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {u : Torus d → ℝ}
    (hu : MemLp u 2 volume) :
    coeffOf (ResponseAux.cv (periodicRiesz d s) u) = rieszMult d s (coeffOf u) := by
  have hg := (integral_periodicRiesz hd hs0 hsd).1
  have hu1 : Integrable u := hu.integrable one_le_two
  funext k
  have h1 := ResponseAux.fourier_cv hg hu1 (rieszCoeff d s)
    (fun n => ResponseAux.hcoef_of_funFourierCoeff (ĝ := rieszCoeff d s)
      (periodicRiesz_fourierCoeff hd hs0 hsd) n) k
  simpa only [ClassicalAux.coeffOf_apply, rieszMult] using h1

theorem p_cc3_bootstrap (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ A u : Torus d → ℝ}
    (hρ : Torus.IsSmooth ρ) (hA : Torus.IsSmooth A) (β : ℝ) (hu : MemLp u 2 volume)
    (hE : u =ᵐ[volume] fun x => ρ x * (A x - β * ResponseAux.cv (periodicRiesz d s) u x)) :
    ∀ N : ℕ, MemHs (N : ℝ) (coeffOf u) := by
  have hρc : Continuous ρ := p_cc3_continuous hρ
  have hAc : Continuous A := p_cc3_continuous hA
  have hρ2 : MemLp ρ 2 volume := ClassicalAux.memLp_two_of_continuous hρc
  have hg := (integral_periodicRiesz hd hs0 hsd).1
  have hgm := PoleCavityAux.measurable_periodicRiesz hd hs0 hsd
  have hcv2 : MemLp (ResponseAux.cv (periodicRiesz d s) u) 2 volume :=
    (ResponseAux.memLp_cv hgm hg hu).1
  have hcvc := p_cc3_coeff_cv hd hs0 hsd hu
  obtain ⟨C, hC⟩ := p_cc3_bdd hρc
  have hint1 : Integrable fun x => ρ x * A x := ClassicalAux.integrable_of_continuous (hρc.mul hAc)
  have hint2 : Integrable fun x => β * (ρ x * ResponseAux.cv (periodicRiesz d s) u x) :=
    ((hcv2.integrable one_le_two).bdd_mul (c := C) hρc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using hC x)).const_mul β
  have hcoefE : coeffOf u = fun k => coeffOf (fun x => ρ x * A x) k -
      (β : ℂ) * mulCoeff (coeffOf ρ) (rieszMult d s (coeffOf u)) k := by
    have e1 : coeffOf u = coeffOf (fun x => ρ x * (A x - β * ResponseAux.cv (periodicRiesz d s) u x)) := by
      funext k
      rw [ClassicalAux.coeffOf_apply, ClassicalAux.coeffOf_apply]
      refine integral_congr_ae ?_
      filter_upwards [hE] with x hx
      rw [hx]
    have e2 : (fun x => ρ x * (A x - β * ResponseAux.cv (periodicRiesz d s) u x)) =
        fun x => ρ x * A x - β * (ρ x * ResponseAux.cv (periodicRiesz d s) u x) := by
      funext x; ring
    refine e1.trans ?_
    rw [e2, ClassicalAux.coeffOf_sub hint1 hint2, ClassicalAux.coeffOf_const_mul,
      coeffOf_mul ρ _ hρ2 hcv2, hcvc]
  have hρw : ∀ b : ℝ, Summable fun k => sobWeight (b / 2) k * ‖coeffOf ρ k‖ :=
    p_cc3_weighted_summable hρ
  have hρ1 : Summable fun k => ‖coeffOf ρ k‖ := by
    simpa [zero_div, sobWeight_zero] using hρw 0
  have hρA : Torus.IsSmooth fun x => ρ x * A x := by
    unfold Torus.IsSmooth Torus.IsCk at *
    exact hρ.mul hA
  set ε : ℝ := (d : ℝ) - s with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hstep : ∀ a : ℝ, 0 ≤ a → MemHs a (coeffOf u) → MemHs (a + ε) (coeffOf u) := by
    intro a ha hc
    have h1 := p_cc3_riesz_gain hsd a (coeffOf u) hc
    have h2 := p_cc3_mulCoeff_memHs (a + ε) (by linarith) (coeffOf ρ) _ hρ1 (hρw _) h1
    have h3 := p_cc3_memHs_smooth hρA (a + ε)
    have h4 := p_cc3_memHs_sub_smul h3 h2 (β : ℂ)
    rw [hcoefE]
    exact h4
  have hind : ∀ n : ℕ, MemHs ((n : ℝ) * ε) (coeffOf u) := by
    intro n
    induction n with
    | zero => simpa using p_cc3_memHs_zero hu
    | succ n ih =>
      have := hstep _ (by positivity) ih
      have e : ((n + 1 : ℕ) : ℝ) * ε = (n : ℝ) * ε + ε := by push_cast; ring
      rw [e]
      exact this
  intro N
  obtain ⟨n, hn⟩ := exists_nat_ge ((N : ℝ) / ε)
  have hNn : (N : ℝ) ≤ n * ε := by rwa [div_le_iff₀ hεpos] at hn
  exact p_cc3_memHs_mono hNn (hind n)

end P3Aux

section P3Resp

open HRS.PDE

theorem p_cc3_response (S : PreparedData d) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) {g : Torus d → ℝ}
    (hg : Torus.IsSmooth g) :
    IsResponse (periodicRiesz d S.s) S.μ0 β₀ g
      (responseInverse (periodicRiesz d S.s) S.μ0 β₀ g) := by
  have hρ := S.hρ0
  obtain ⟨Λ, hΛ⟩ := p_cc3_bdd (p_cc3_continuous hρ.smooth)
  haveI : IsProbabilityMeasure (withDensityReal S.ρ0) :=
    ResponseAux.isProbabilityMeasure_dens hρ.density
  have hg2 : MemLp g 2 (withDensityReal S.ρ0) :=
    (p_cc3_continuous hg).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact HRS.MC.IID.isResponse_responseInverse S.hd S.hs0 S.hsd S.ρ0 hρ.density Λ
    (fun x => (le_abs_self _).trans (hΛ x)) hβ₀ g hg2

theorem p_cc3_response_smooth (S : PreparedData d) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀)
    {g : Torus d → ℝ} (hg : Torus.IsSmooth g) :
    ∃ h : Torus d → ℝ, Torus.IsSmooth h ∧
      responseInverse (periodicRiesz d S.s) S.μ0 β₀ g =ᵐ[S.μ0] h := by
  classical
  have hρ := S.hρ0
  have hρc : Continuous S.ρ0 := p_cc3_continuous hρ.smooth
  obtain ⟨Λ, hΛ⟩ := p_cc3_bdd hρc
  have hΛ' : ∀ x, S.ρ0 x ≤ Λ := fun x => (le_abs_self _).trans (hΛ x)
  obtain ⟨hR2, hR0, hRae⟩ := p_cc3_response S β₀ hβ₀ hg
  set R := responseInverse (periodicRiesz d S.s) S.μ0 β₀ g with hR
  have hR2' : MemLp R 2 (withDensityReal S.ρ0) := hR2
  set u : Torus d → ℝ := fun x => S.ρ0 x * R x with hu
  have hu2 : MemLp u 2 volume := (ResponseAux.rho_mul_memLp hρ.density hΛ' hR2').1
  set pg := pair S.μ0 g with hpg
  set c1 := pair S.μ0 (ResponseAux.Kt (periodicRiesz d S.s) S.μ0 R) with hc1
  set A : Torus d → ℝ := fun x => g x - pg + β₀ * c1 with hA
  have hRae' : ∀ᵐ x ∂(withDensityReal S.ρ0),
      R x = A x - β₀ * ResponseAux.cv (periodicRiesz d S.s) u x := by
    filter_upwards [hRae] with x hx
    have e1 : Kop (periodicRiesz d S.s) S.μ0 R x =
        ResponseAux.Kt (periodicRiesz d S.s) S.μ0 R x - c1 := rfl
    have e2 : projMean S.μ0 g x = g x - pg := rfl
    have e3 : ResponseAux.Kt (periodicRiesz d S.s) S.μ0 R x =
        ResponseAux.cv (periodicRiesz d S.s) u x :=
      congrFun (ResponseAux.Kt_eq_cv hρ.density (periodicRiesz d S.s) R) x
    rw [e1, e2, e3] at hx
    simp only [hA]
    linarith
  have hE : u =ᵐ[volume] fun x => S.ρ0 x *
      (A x - β₀ * ResponseAux.cv (periodicRiesz d S.s) u x) :=
    ResponseAux.ae_vol_of_ae_dens hρ.density hRae'
  have hAs : Torus.IsSmooth A := by
    have h1 := p_cc3_smooth_sub hg (p_cc3_smooth_const (d := d) pg)
    unfold Torus.IsSmooth Torus.IsCk at *
    exact h1.add contDiff_const
  have Boot := p_cc3_bootstrap S.hd S.hs0 S.hsd hρ.smooth hAs β₀ hu2 hE
  set c := coeffOf u with hc
  have hreal : IsRealCoeff (rieszMult d S.s c) :=
    HRS.PDE.MFApriori.isRealCoeff_rieszMult S.s c (isRealCoeff_coeffOf u (hu2.integrable one_le_two))
  have hdec : ∀ N : ℕ, MemHs (N : ℝ) (rieszMult d S.s c) := fun N =>
    (HRS.PDE.MFApriori.hs_rieszMult S.s S.hsd N c (Boot N)).1
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast S.hd
  have hsum : Summable fun k => ‖rieszMult d S.s c k‖ :=
    summable_norm_of_memHs (d : ℝ) (by linarith) _ (hdec d)
  have hH : Torus.IsSmooth (toFun (rieszMult d S.s c)) := isSmooth_toFun_of_decay _ hreal hdec
  have hcoefH : coeffOf (toFun (rieszMult d S.s c)) = rieszMult d S.s c := coeffOf_toFun _ hreal hsum
  have hcv2 : MemLp (ResponseAux.cv (periodicRiesz d S.s) u) 2 volume :=
    (ResponseAux.memLp_cv (PoleCavityAux.measurable_periodicRiesz S.hd S.hs0 S.hsd)
      (integral_periodicRiesz S.hd S.hs0 S.hsd).1 hu2).1
  have hcvc := p_cc3_coeff_cv S.hd S.hs0 S.hsd hu2
  have hae : ResponseAux.cv (periodicRiesz d S.s) u =ᵐ[volume] toFun (rieszMult d S.s c) :=
    HRS.PDE.MFApriori.ae_eq_of_funFourierCoeff_eq_of_memLp hcv2 (p_cc3_continuous hH)
      (fun k => congrFun (hcvc.trans hcoefH.symm) k)
  refine ⟨fun x => A x - β₀ * toFun (rieszMult d S.s c) x, ?_, ?_⟩
  · have h1 := p_cc3_smooth_mul (p_cc3_smooth_const (d := d) β₀) hH
    exact p_cc3_smooth_sub hAs h1
  · have h1 : ∀ᵐ x ∂(withDensityReal S.ρ0),
        ResponseAux.cv (periodicRiesz d S.s) u x = toFun (rieszMult d S.s c) x :=
      (ResponseAux.dens_ac S.ρ0).ae_eq hae
    filter_upwards [hRae', h1] with x hx1 hx2
    rw [hx1, hx2]

end P3Resp

/-- **CCD3 (analytic core)** (`ccd_response_smooth`, note §3 CCD3, part E).  The response `R_{β₀,μ°}P_{μ°}g =
(I + β₀K_{μ°})^{-1}P_{μ°}g` of a smooth `g` (for `β₀ ≥ 0`, `K` with the Riesz kernel `periodicRiesz d s`) has a smooth
representative, `μ°`-a.e. (equivalently Lebesgue-a.e., `ρ° > 0`).  For `β₀ = 0` it is `g - μ°(g)`; for `β₀ > 0` the
solution exists (positivity of `K`) and `h = P g - β₀ K h` is bootstrapped, `K` gaining `d - s > 0` Sobolev
derivatives and multiplication by the smooth `ρ°` being bounded on `H^j`. -/
theorem ccd_response_smooth (S : PreparedData d) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀)
    {g : Torus d → ℝ} (hg : Torus.IsSmooth g) :
    ∃ h : Torus d → ℝ, Torus.IsSmooth h ∧
      responseInverse (periodicRiesz d S.s) S.μ0 β₀ g =ᵐ[S.μ0] h := by
  exact p_cc3_response_smooth S β₀ hβ₀ hg


/-- **CCD3** (`ccd_preparedCov_density`, note §3 CCD3).  The initial covariance `Cov_ν(f, g) = preparedCov f g` has a smooth
density in `f`: `preparedCov f g = ∫ f w dx` for all smooth `f`, with `w` smooth of mean zero.  Route: `β₀ = 0`:
`w = ρ°(g - μ°(g))`; `β₀ > 0`: `w = ρ° h` with `h` from `ccd_response_smooth` (`μ°(h) = 0` gives `∫ w = 0`), unfolding
`susceptibilityCov`, `l2Inner`, `projMean`. -/
theorem ccd_preparedCov_density (S : PreparedData d) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀)
    {g : Torus d → ℝ} (hg : Torus.IsSmooth g) :
    ∃ w : Torus d → ℝ, Torus.IsSmooth w ∧ Torus.mean w = 0 ∧
      ∀ f : Torus d → ℝ, Torus.IsSmooth f → preparedCov d S.s β₀ S.μ0 f g = ∫ x, f x * w x := by
  classical
  have hρ := S.hρ0
  have hρc : Continuous S.ρ0 := p_cc3_continuous hρ.smooth
  have hgc : Continuous g := p_cc3_continuous hg
  haveI : IsProbabilityMeasure S.μ0 := ResponseAux.isProbabilityMeasure_dens hρ.density
  have hdens : ∀ h : Torus d → ℝ, ∫ x, h x ∂S.μ0 = ∫ x, S.ρ0 x * h x :=
    fun h => ResponseAux.integral_dens hρ.density h
  have hρ1 : ∫ x, S.ρ0 x = 1 := hρ.density.integral_one
  have hρi : Integrable S.ρ0 := ResponseAux.integrable_rho hρ.density
  by_cases hb : β₀ = 0
  · refine ⟨fun x => S.ρ0 x * (g x - pair S.μ0 g), ?_, ?_, ?_⟩
    · exact p_cc3_smooth_mul hρ.smooth (p_cc3_smooth_sub hg (p_cc3_smooth_const _))
    · have i1 : Integrable fun x => S.ρ0 x * g x :=
        HRS.PDE.ClassicalAux.integrable_of_continuous (hρc.mul hgc)
      have i2 : Integrable fun x => pair S.μ0 g * S.ρ0 x := hρi.const_mul _
      unfold Torus.mean
      have e : ∀ x, S.ρ0 x * (g x - pair S.μ0 g) = S.ρ0 x * g x - pair S.μ0 g * S.ρ0 x := by
        intro x; ring
      simp_rw [e]
      rw [integral_sub i1 i2, integral_const_mul, hρ1]
      have := hdens g
      unfold pair
      rw [this]
      ring
    · intro f hf
      have hfc : Continuous f := p_cc3_continuous hf
      have i1 : Integrable fun x => S.ρ0 x * (f x * g x) :=
        HRS.PDE.ClassicalAux.integrable_of_continuous (hρc.mul (hfc.mul hgc))
      have i2 : Integrable fun x => S.ρ0 x * f x :=
        HRS.PDE.ClassicalAux.integrable_of_continuous (hρc.mul hfc)
      unfold preparedCov
      rw [if_pos hb]
      unfold iidCov
      have e : ∀ x, f x * (S.ρ0 x * (g x - pair S.μ0 g)) =
          S.ρ0 x * (f x * g x) - pair S.μ0 g * (S.ρ0 x * f x) := by
        intro x; ring
      simp_rw [e]
      rw [integral_sub i1 (i2.const_mul _), integral_const_mul]
      have p1 : pair S.μ0 (fun x => f x * g x) = ∫ x, S.ρ0 x * (f x * g x) := hdens _
      have p2 : pair S.μ0 f = ∫ x, S.ρ0 x * f x := hdens _
      rw [p1, p2]
      ring
  · obtain ⟨H, hH, hae⟩ := ccd_response_smooth S β₀ hβ₀ hg
    obtain ⟨-, hR0, -⟩ := p_cc3_response S β₀ hβ₀ hg
    set R := responseInverse (periodicRiesz d S.s) S.μ0 β₀ g with hR
    have hHint : ∫ x, H x ∂S.μ0 = 0 := by
      rw [← hR0]
      unfold pair
      exact integral_congr_ae hae.symm
    have hHc : Continuous H := p_cc3_continuous hH
    have hw0 : ∫ x, S.ρ0 x * H x = 0 := by rw [← hdens H]; exact hHint
    refine ⟨fun x => S.ρ0 x * H x, ?_, ?_, ?_⟩
    · exact p_cc3_smooth_mul hρ.smooth hH
    · exact hw0
    · intro f hf
      have hfc : Continuous f := p_cc3_continuous hf
      have i1 : Integrable fun x => f x * (S.ρ0 x * H x) :=
        HRS.PDE.ClassicalAux.integrable_of_continuous (hfc.mul (hρc.mul hHc))
      unfold preparedCov
      rw [if_neg hb]
      unfold susceptibilityCov l2Inner
      have h1 : ∫ x, projMean S.μ0 f x * R x ∂S.μ0 = ∫ x, projMean S.μ0 f x * H x ∂S.μ0 :=
        integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
      rw [h1, hdens]
      have e : ∀ x, S.ρ0 x * (projMean S.μ0 f x * H x) =
          f x * (S.ρ0 x * H x) - pair S.μ0 f * (S.ρ0 x * H x) := by
        intro x; unfold projMean; ring
      simp_rw [e]
      have i0 : Integrable fun x => S.ρ0 x * H x :=
        HRS.PDE.ClassicalAux.integrable_of_continuous (hρc.mul hHc)
      rw [integral_sub i1 (i0.const_mul (pair S.μ0 f)), integral_const_mul, hw0]
      ring

end HRS.MC.CrossCov
