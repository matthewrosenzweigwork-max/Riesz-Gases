import HRS.MC.E213U18k

/-!
# Packet e213u18 (part l): `⟨ℓ_x, ψ⟩ = (R P ψ)(x)` for smooth `ψ`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.Main HRS.MC.SEdge HRS.MC.Sec7 HRS.MC.Sec7.S7e

variable {d : ℕ}

section EvalEll

variable {s : ℝ} {ρ : Torus d → ℝ}

theorem u18_a_bound {γ r : ℝ} {a : NonzeroLattice d → Torus d → ℝ}
    {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C : ℝ} (hmode : s7_ModeData d s γ ρ r a v C)
    (k : NonzeroLattice d) (x : Torus d) :
    |a k x| ≤ |C| * Lattice.jp k.1 ^ (-((d : ℝ) + 3)) := by
  have h1 := HRS.PDE.R2Aux.abs_le_cbNorm (HRS.Q66.q66_isCk_of_smooth (hmode.smooth_a k) 1) x
  refine h1.trans ((hmode.bound_a k).trans ?_)
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (Torus.jp_pos k.1).le _)

theorem u18_a_mem {γ r : ℝ} {a : NonzeroLattice d → Torus d → ℝ}
    {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C : ℝ} (hmode : s7_ModeData d s γ ρ r a v C)
    (x : Torus d) : Memℓp (fun k => a k x) 2 := by
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos _
  set b : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-((d : ℝ) + 3)) with hbdef
  have hb0 : ∀ k, 0 ≤ b k := fun k => (Real.rpow_pos_of_pos (hjp k) _).le
  have hb1 : ∀ k, b k ≤ 1 := fun k =>
    Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one _) (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
  have hb : Summable b := by
    have := summable_jp_rpow (d := d) (((d : ℝ) + 3) / 2) (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
    refine this.congr fun k => ?_
    simp only [hbdef]; congr 1; ring
  rw [memℓp_gen_iff (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hb.mul_left (|C| ^ 2))
  have h1 := u18_a_bound hmode k x
  calc |a k x| ^ (2 : ℝ) = |a k x| ^ 2 := by rw [Real.rpow_two]
    _ ≤ (|C| * b k) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = |C| ^ 2 * (b k * b k) := by ring
    _ ≤ |C| ^ 2 * b k := by
        gcongr
        exact mul_le_of_le_one_left (hb0 k) (hb1 k)

theorem u18_resp_mode (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    (hρ : SmoothPosDensity ρ) {r : ℝ} {a : NonzeroLattice d → Torus d → ℝ}
    {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C : ℝ} (hmode : s7_ModeData d s γ ρ r a v C)
    (k : NonzeroLattice d) (x : Torus d) :
    responseRep (periodicRiesz d s) (withDensityReal ρ) γ (Torus.realMode k) x =
      Lattice.jp k.1 ^ r * a k x := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  set μ := withDensityReal ρ with hμ
  have hjp : 0 < Lattice.jp k.1 := Torus.jp_pos _
  have hcont : Continuous (a k) := HRS.Q66.q66_cont_of_smooth (hmode.smooth_a k)
  have hjr : Lattice.jp k.1 ^ r * Lattice.jp k.1 ^ (-r) = 1 := by
    rw [← Real.rpow_add hjp]; simp
  refine s7e_responseRep_eq_of_eq hd hs0 hs hγ hρ (h := fun x => Lattice.jp k.1 ^ r * a k x)
    ((s7e_continuous_realMode k).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (continuous_const.mul hcont) ?_ ?_ x
  · unfold pair
    rw [integral_const_mul, hmode.mean_zero k, mul_zero]
  · intro y
    rw [s7e_kop_const_mul]
    have h1 := hmode.resp k y
    have hproj : projMean μ (s7_phi r k) y = Lattice.jp k.1 ^ (-r) * projMean μ (Torus.realMode k) y := by
      unfold projMean pair s7_phi
      rw [integral_const_mul]; ring
    rw [hproj] at h1
    calc Lattice.jp k.1 ^ r * a k y + γ * (Lattice.jp k.1 ^ r * Kop (periodicRiesz d s) μ (a k) y)
        = Lattice.jp k.1 ^ r * (a k y + γ * Kop (periodicRiesz d s) μ (a k) y) := by ring
      _ = Lattice.jp k.1 ^ r * (Lattice.jp k.1 ^ (-r) * projMean μ (Torus.realMode k) y) := by rw [h1]
      _ = projMean μ (Torus.realMode k) y := by rw [← mul_assoc, hjr, one_mul]

theorem u18_fc_ellPt (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    (hρ : SmoothPosDensity ρ) {r : ℝ} {a : NonzeroLattice d → Torus d → ℝ}
    {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C : ℝ} (hmode : s7_ModeData d s γ ρ r a v C)
    (k : NonzeroLattice d) (x : Torus d) :
    NegSobolev.fourierCoeff (ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x) k =
      Lattice.jp k.1 ^ r * a k x := by
  have hmem' : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) *
      responseRep (periodicRiesz d s) (withDensityReal ρ) γ (Torus.realMode k) x) 2 := by
    have hw : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) *
        responseRep (periodicRiesz d s) (withDensityReal ρ) γ (Torus.realMode k) x) = fun k => a k x := by
      funext k
      rw [u18_resp_mode hd hs0 hs hγ hρ hmode k x, ← mul_assoc]
      have : Lattice.jp k.1 ^ (-r) * Lattice.jp k.1 ^ r = 1 := by
        rw [← Real.rpow_add (Torus.jp_pos k.1)]; simp
      rw [this, one_mul]
    rw [hw]; exact u18_a_mem hmode x
  unfold ellPt
  rw [HRS.Q41.q41_fourierCoeff_ofSeq hmem' k]
  exact u18_resp_mode hd hs0 hs hγ hρ hmode k x

theorem u18_projMean_series {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {ψ : Torus d → ℝ}
    (hψ : Torus.IsSmooth ψ) (y : Torus d) :
    HasSum (fun k : NonzeroLattice d => Torus.funRealCoeff ψ k * projMean μ (Torus.realMode k) y)
      (projMean μ ψ y) := by
  have hd : ∀ n : ℕ, ContDiff ℝ n (Torus.lift ψ) := fun n =>
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ψ) from hψ).of_le (by exact_mod_cast le_top)
  have hcont : Continuous ψ :=
    (KernelGrad.isOpenQuotientMap_mk (d := d)).continuous_comp_iff.mp (hd 0).continuous
  have hs := Torus.summable_fcoef_of_contDiff hd
  have hexp : ∀ z : Torus d, HasSum (fun k : NonzeroLattice d =>
      Torus.funRealCoeff ψ k * Torus.realMode k z) (ψ z - Torus.mean ψ) :=
    fun z => Torus.hasSum_realExpansion hcont hs z
  have hsum1 := u18_summable_weighted hψ 1
  have hfi : ∀ k : NonzeroLattice d, Integrable (fun z => Torus.funRealCoeff ψ k * Torus.realMode k z) μ :=
    fun k => HRS.MC.E213L.e213l_integrable (μ := μ) (continuous_const.mul (Torus.continuous_realMode k))
  have hsum : Summable fun k : NonzeroLattice d =>
      ∫ z, ‖Torus.funRealCoeff ψ k * Torus.realMode k z‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun z => norm_nonneg _) (fun k => ?_)
      (hsum1.mul_left (Real.sqrt 2))
    calc ∫ z, ‖Torus.funRealCoeff ψ k * Torus.realMode k z‖ ∂μ
        ≤ ∫ z, |Torus.funRealCoeff ψ k| * Real.sqrt 2 ∂μ := by
          refine integral_mono (hfi k).norm (integrable_const _) fun z => ?_
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (Torus.abs_realMode_le k z) (abs_nonneg _)
      _ = |Torus.funRealCoeff ψ k| * Real.sqrt 2 := by simp
      _ ≤ Real.sqrt 2 * (|Torus.funRealCoeff ψ k| * Lattice.jp k.1 ^ 1) := by
          have := Torus.jp_ge_one k.1
          rw [pow_one]
          nlinarith [mul_nonneg (sub_nonneg.2 this) (mul_nonneg (abs_nonneg (Torus.funRealCoeff ψ k)) (Real.sqrt_nonneg 2))]
  have h1 := hasSum_integral_of_summable_integral_norm hfi hsum
  have e : ∀ z : Torus d, ∑' k : NonzeroLattice d, Torus.funRealCoeff ψ k * Torus.realMode k z =
      ψ z - Torus.mean ψ := fun z => (hexp z).tsum_eq
  simp_rw [e] at h1
  have hψi : Integrable ψ μ := HRS.MC.E213L.e213l_integrable (μ := μ) hcont
  have e2 : ∫ z, (ψ z - Torus.mean ψ) ∂μ = pair μ ψ - Torus.mean ψ := by
    rw [integral_sub hψi (integrable_const _)]
    simp [pair]
  rw [e2] at h1
  have h0 : ∀ k : NonzeroLattice d, ∫ z, Torus.funRealCoeff ψ k * Torus.realMode k z ∂μ =
      Torus.funRealCoeff ψ k * pair μ (Torus.realMode k) := fun k => by
    rw [integral_const_mul]; rfl
  have e0 : (fun k : NonzeroLattice d => ∫ z, Torus.funRealCoeff ψ k * Torus.realMode k z ∂μ) =
      fun k => Torus.funRealCoeff ψ k * pair μ (Torus.realMode k) := funext h0
  rw [e0] at h1
  have h3 := (hexp y).sub h1
  convert h3 using 1
  · funext k
    unfold projMean
    ring
  · unfold projMean
    ring

theorem u18_eval_ellPt (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    (hρ : SmoothPosDensity ρ) {r : ℝ} (hr : r = 2 * (d : ℝ) + 6) {ψ : Torus d → ℝ}
    (hψ : Torus.IsSmooth ψ) (x : Torus d) :
    NegSobolev.eval (ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x) ψ =
      responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x := by
  classical
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨a, v, C, hmode⟩ := HRS.MC.Sec7.S7a.s7_S7a_mode_data_proof hd hs0 hs r hr γ hγ ρ hρ
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos _
  have hcont : ∀ k, Continuous (a k) := fun k => HRS.Q66.q66_cont_of_smooth (hmode.smooth_a k)
  obtain ⟨c, hc⟩ : ∃ c : NonzeroLattice d → ℝ, c = fun k => Torus.funRealCoeff ψ k := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : NonzeroLattice d → ℝ, cc = fun k => c k * Lattice.jp k.1 ^ r := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : NonzeroLattice d → Torus d → ℝ, f = fun k y => cc k * a k y := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : NonzeroLattice d → ℝ,
      w = fun k => |C| * (|c k| * Lattice.jp k.1 ^ (d + 3)) := ⟨_, rfl⟩
  have hwsum : Summable w := by
    rw [hw, hc]
    exact (u18_summable_weighted hψ (d + 3)).mul_left |C|
  have hfb : ∀ k y, |f k y| ≤ w k := by
    intro k y
    have h1 := u18_a_bound hmode k y
    have e : Lattice.jp k.1 ^ r * Lattice.jp k.1 ^ (-((d : ℝ) + 3)) = Lattice.jp k.1 ^ (d + 3) := by
      rw [← Real.rpow_add (hjp k)]
      have : r + -((d : ℝ) + 3) = ((d + 3 : ℕ) : ℝ) := by rw [hr]; push_cast; ring
      rw [this, Real.rpow_natCast]
    have hnn : 0 ≤ |c k| * Lattice.jp k.1 ^ r := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (hjp k).le _)
    rw [hf, hw]
    simp only
    calc |cc k * a k y| = |c k| * Lattice.jp k.1 ^ r * |a k y| := by
          rw [hcc]
          simp only [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hjp k) r)]
      _ ≤ |c k| * Lattice.jp k.1 ^ r * (|C| * Lattice.jp k.1 ^ (-((d : ℝ) + 3))) :=
          mul_le_mul_of_nonneg_left h1 hnn
      _ = |C| * (|c k| * Lattice.jp k.1 ^ (d + 3)) := by rw [← e]; ring
  have hfc : ∀ k, Continuous (f k) := fun k => by rw [hf]; exact continuous_const.mul (hcont k)
  obtain ⟨H, hH⟩ : ∃ H : Torus d → ℝ, H = fun y => ∑' k, f k y := ⟨_, rfl⟩
  have hHc : Continuous H := by
    rw [hH]
    exact continuous_tsum hfc hwsum (fun k y => by rw [Real.norm_eq_abs]; exact hfb k y)
  have hfsum : ∀ y, HasSum (fun k => f k y) (H y) := fun y => by
    rw [hH]
    exact (Summable.of_norm_bounded hwsum (fun k => by rw [Real.norm_eq_abs]; exact hfb k y)).hasSum
  have hev : NegSobolev.eval (ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x) ψ = H x := by
    unfold NegSobolev.eval
    rw [hH]
    refine tsum_congr fun k => ?_
    rw [u18_fc_ellPt hd hs0 hs hγ hρ hmode k x, hf, hcc, hc]
    simp only
    ring
  have hmean : pair (withDensityReal ρ) H = 0 := by
    have hfi : ∀ k, Integrable (f k) (withDensityReal ρ) := fun k =>
      HRS.MC.E213L.e213l_integrable (μ := withDensityReal ρ) (hfc k)
    have hsum : Summable fun k => ∫ z, ‖f k z‖ ∂(withDensityReal ρ) := by
      refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun z => norm_nonneg _) (fun k => ?_) hwsum
      calc ∫ z, ‖f k z‖ ∂(withDensityReal ρ) ≤ ∫ z, w k ∂(withDensityReal ρ) :=
            integral_mono (hfi k).norm (integrable_const _)
              (fun z => by rw [Real.norm_eq_abs]; exact hfb k z)
        _ = w k := by simp
    have h1 := hasSum_integral_of_summable_integral_norm hfi hsum
    have h0 : ∀ k, ∫ z, f k z ∂(withDensityReal ρ) = 0 := fun k => by
      rw [hf]
      simp only
      rw [integral_const_mul, hmode.mean_zero k, mul_zero]
    have e0 : (fun k => ∫ z, f k z ∂(withDensityReal ρ)) = fun _ => 0 := funext h0
    rw [e0] at h1
    unfold pair
    rw [hH]
    exact (hasSum_zero.unique h1).symm
  have heq : ∀ y, H y + γ * Kop (periodicRiesz d s) (withDensityReal ρ) H y =
      projMean (withDensityReal ρ) ψ y := by
    intro y
    obtain ⟨M, hM⟩ := HRS.Q66.q66_bound_of_smooth hρ.smooth
    have hΛ0 : 0 ≤ max M 0 := le_max_right _ _
    have hKS : HRS.PDE.MFLinear.KS (periodicRiesz d s) ρ (max M 0) :=
      ⟨HRS.PDE.MFOneLe.integrable_periodicRiesz (by omega) s hs0 (by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith), fun z => periodicRiesz_neg z, hρ.density,
        fun z => (le_abs_self _).trans ((hM z).trans (le_max_left _ _))⟩
    have hK := u18_kop_hasSum hKS hΛ0 f hfc hwsum hfb y
    have hKf : ∀ k, Kop (periodicRiesz d s) (withDensityReal ρ) (f k) y =
        cc k * Kop (periodicRiesz d s) (withDensityReal ρ) (a k) y := fun k => by
      rw [hf]
      exact HRS.PDE.MFPair.Kop_smul_fun hρ.density (a k) (cc k) y
    have h2 : HasSum (fun k => f k y + γ * Kop (periodicRiesz d s) (withDensityReal ρ) (f k) y)
        (H y + γ * Kop (periodicRiesz d s) (withDensityReal ρ) H y) := by
      have hK' : HasSum (fun k => Kop (periodicRiesz d s) (withDensityReal ρ) (f k) y)
          (Kop (periodicRiesz d s) (withDensityReal ρ) H y) := by
        rw [hH]; exact hK
      exact (hfsum y).add (hK'.mul_left γ)
    have h3 : HasSum (fun k => c k * projMean (withDensityReal ρ) (Torus.realMode k) y)
        (projMean (withDensityReal ρ) ψ y) := by
      rw [hc]; exact u18_projMean_series hψ y
    have e : (fun k => f k y + γ * Kop (periodicRiesz d s) (withDensityReal ρ) (f k) y) =
        fun k => c k * projMean (withDensityReal ρ) (Torus.realMode k) y := by
      funext k
      rw [hKf k]
      have h1 := hmode.resp k y
      have hproj : projMean (withDensityReal ρ) (s7_phi r k) y =
          Lattice.jp k.1 ^ (-r) * projMean (withDensityReal ρ) (Torus.realMode k) y := by
        unfold projMean pair s7_phi
        rw [integral_const_mul]; ring
      rw [hproj] at h1
      have hjr : Lattice.jp k.1 ^ r * Lattice.jp k.1 ^ (-r) = 1 := by
        rw [← Real.rpow_add (hjp k)]; simp
      rw [hf]
      simp only
      calc cc k * a k y + γ * (cc k * Kop (periodicRiesz d s) (withDensityReal ρ) (a k) y)
          = cc k * (a k y + γ * Kop (periodicRiesz d s) (withDensityReal ρ) (a k) y) := by ring
        _ = cc k * (Lattice.jp k.1 ^ (-r) * projMean (withDensityReal ρ) (Torus.realMode k) y) := by
            rw [h1]
        _ = c k * projMean (withDensityReal ρ) (Torus.realMode k) y := by
            rw [hcc]
            simp only
            calc c k * Lattice.jp k.1 ^ r * (Lattice.jp k.1 ^ (-r) * projMean (withDensityReal ρ) (Torus.realMode k) y)
                = c k * (Lattice.jp k.1 ^ r * Lattice.jp k.1 ^ (-r)) *
                    projMean (withDensityReal ρ) (Torus.realMode k) y := by ring
              _ = _ := by rw [hjr]; ring
    rw [e] at h2
    exact h2.unique h3
  rw [hev]
  exact (s7e_responseRep_eq_of_eq hd hs0 hs hγ hρ (HRS.MC.Sec7.S7d.s7d_memLp_smooth hρ hψ) hHc hmean heq x).symm

end EvalEll

end HRS.MC.E213U18

end
