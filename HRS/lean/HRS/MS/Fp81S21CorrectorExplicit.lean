import HRS.MS.DerCorAux2
import HRS.MS.Fp81S21InitialFam2

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc MemCb cbNorm)
open HRS.Whole
open HRS.MS.R26T3

/-- The visible input order required by the S4.8 derivative corrector at k₀. -/
def fp81s21_correctorOrder (d : ℕ) : ℕ :=
  Nat.ceil ((fp81s21_k0 d : ℝ) + 2 + (d : ℝ) / 2) + 1

theorem fp81s21_correctorOrder_spec (d : ℕ) :
    ((fp81s21_k0 d + 2 : ℕ) : ℝ) + (d : ℝ) / 2 <
      fp81s21_correctorOrder d := by
  unfold fp81s21_correctorOrder
  have h := Nat.le_ceil ((fp81s21_k0 d : ℝ) + 2 + (d : ℝ) / 2)
  push_cast at h ⊢
  linarith

theorem fp81s21_correctorOrder_le (d : ℕ) (hd : 2 ≤ d) :
    fp81s21_correctorOrder d ≤ r26t3_J d := by
  unfold fp81s21_correctorOrder fp81s21_k0 r26t3_J
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hceil :
      Nat.ceil (((2 * d + 10 : ℕ) : ℝ) + 2 + (d : ℝ) / 2) ≤ 4 * d + 39 := by
    apply Nat.ceil_le.2
    push_cast
    nlinarith
  omega

/-- The S4.8 construction with its Sobolev input order fixed in the hypotheses. -/
theorem fp81s21_corrector_from_pkg
    {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (k J M N : ℕ) (hmJ : k + 2 ≤ J)
    (hJ : ((k + 2 : ℕ) : ℝ) + (d : ℝ) / 2 < J)
    (hMs : ((k + 2 : ℕ) : ℝ) + (d : ℝ) / 2 < M * ((d : ℝ) - s))
    (hN : (J : ℝ) + M * ((d : ℝ) - s) + d < N)
    {ρ : Euc d → ℝ} {q γ γp M₀ c S Mb m₂ : ℝ}
    (hq : 0 < q) (hγ : 0 < γ) (hγp : γ ≤ γp) (hc : 0 < c)
    (P : HRS.MS.S48.S48Pkg d ρ q M₀ c S Mb m₂ N J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Euc d → ℝ, MemCb J φ →
      ∃ aφ χ : Euc d → ℝ,
        HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ aφ ∧
        ContDiff ℝ (k + 1) aφ ∧
        (∀ i : ℕ, 1 ≤ i → i ≤ k + 1 → ∀ x,
          ‖iteratedFDeriv ℝ i aφ x‖ ≤
            C * HRS.MS.S48.s48_Q (μ := HRS.Whole.withDensityReal ρ) J φ) ∧
        ContDiff ℝ (k + 2) χ ∧
        (∀ x, weightedGen ρ χ x = aφ x) ∧
        HasCbBound k (C * HRS.MS.S48.s48_Q (μ := HRS.Whole.withDensityReal ρ) J φ) (gradient χ) := by
  have hd1 : 1 ≤ d := by omega
  have hm : k + 2 ≤ J := hmJ
  obtain ⟨Cr, hCr0, hCr⟩ :=
    HRS.MS.S48.s48_resolvent hs0 hsd (k + 2) J M hm hJ hMs γp q Mb M₀ c S hc N hN
  obtain ⟨Cm, hCm0, hCm⟩ :=
    HRS.MS.S48.s48_poisson_deriv hd1 q q Mb (3 / 2 * |m₂|) hq (k + 2) (by omega)
  obtain ⟨B, hR, hcb⟩ := P.drift
  refine ⟨max (γ⁻¹ * Cr) (Cm * (γ⁻¹ * Cr)), ?_, fun φ hφ => ?_⟩
  · exact le_max_of_le_left (by positivity)
  let μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ
  have hgamma : 0 < γ⁻¹ := inv_pos.mpr hγ
  obtain ⟨hprob, hint2, hmom⟩ := HRS.MS.Gap.gap_moment hR
  set Q : ℝ := HRS.MS.S48.s48_Q μ J φ
  have hQ0 : 0 ≤ Q := HRS.MS.S48.s48_Q_nonneg μ J φ
  have habs : |q| ≤ q := by rw [abs_of_pos hq]
  obtain ⟨r₀, r, hr0, hreq, hrcd, hrder, hrae⟩ :=
    hCr q habs ρ B P.ref hR hcb γ hγ hγp φ hφ
  let aφ : Euc d → ℝ := fun x => γ⁻¹ * r x
  have haφae : aφ =ᵐ[μ] fun x => γ⁻¹ * r₀ x := by
    filter_upwards [hrae] with x hx
    simp only [aφ, hx]
  have haφ0 : MemL2Zero μ aφ := by
    have hz : MemL2Zero μ (fun x => γ⁻¹ * r₀ x) :=
      ⟨hr0.1.const_mul _, by rw [integral_const_mul, hr0.2, mul_zero]⟩
    exact ⟨hz.1.ae_eq haφae.symm, by rw [integral_congr_ae haφae]; exact hz.2⟩
  have hresp : HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) μ γ φ aφ := by
    refine ⟨haφ0, ?_⟩
    have hk : HRS.Whole.Kop (HRS.Whole.rieszKernel d s) μ aφ =
        HRS.Whole.Kop (HRS.Whole.rieszKernel d s) μ (fun x => γ⁻¹ * r₀ x) :=
      HRS.MS.S98.s98_kop_congr_ae haφae
    filter_upwards [hreq, haφae] with x hx hx'
    rw [hk, HRS.MS.S98.s98_kop_smul, hx']
    have hγne : γ ≠ 0 := hγ.ne'
    have hx'' : r₀ x + γ * HRS.Whole.Kop (HRS.Whole.rieszKernel d s) μ r₀ x =
        γ * HRS.Whole.projMean μ φ x := hx
    calc γ⁻¹ * r₀ x + γ * (γ⁻¹ * HRS.Whole.Kop (HRS.Whole.rieszKernel d s) μ r₀ x)
        = γ⁻¹ * (r₀ x + γ * HRS.Whole.Kop (HRS.Whole.rieszKernel d s) μ r₀ x) := by field_simp
      _ = _ := by rw [hx'']; field_simp
  have haφs : ContDiff ℝ (k + 2) aφ := contDiff_const.mul hrcd
  let Dfac : ℝ := γ⁻¹ * Cr
  let D : ℝ := Dfac * Q
  have hDfac0 : 0 ≤ Dfac := by dsimp [Dfac]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; exact mul_nonneg hDfac0 hQ0
  have haφder : ∀ i : ℕ, 1 ≤ i → i ≤ k + 2 → ∀ x,
      ‖iteratedFDeriv ℝ i aφ x‖ ≤ D := by
    intro i hi1 hik x
    have he : iteratedFDeriv ℝ i aφ x = γ⁻¹ • iteratedFDeriv ℝ i r x := by
      have h := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := γ⁻¹)
        (f := r) (i := i) (x := x) (hrcd.of_le (by exact_mod_cast hik)).contDiffAt
      simpa [smul_eq_mul, aφ] using h
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hgamma]
    have hri := hrder i hi1 hik x
    calc γ⁻¹ * ‖iteratedFDeriv ℝ i r x‖
        ≤ γ⁻¹ * (Cr * Q) := mul_le_mul_of_nonneg_left hri hgamma.le
      _ = D := by dsimp [D, Dfac]; ring
  obtain ⟨χ, hχcd, hχi, hχ0, hχeq, hχder⟩ :=
    hCm q ⟨le_rfl, le_rfl⟩ B (HRS.MS.S48.s48_hasCb_mono hmJ hcb) μ
      (HRS.MS.Gap.gap_invariant hR) hint2
      (by
        rw [hmom]
        have hnonneg : 0 ≤ ∫ x, ‖x‖ ^ 2 * ρ x :=
          integral_nonneg fun x => by have := hR.pos x; positivity
        calc ∫ x, ‖x‖ ^ 2 * ρ x ≤ m₂ := P.moment
          _ ≤ 3 / 2 * |m₂| := by nlinarith [abs_nonneg m₂, le_abs_self m₂])
      aφ haφs D (by
        intro i hi1 hik x
        exact haφder i hi1 hik x)
      haφ0.2
  have hQ : HRS.MS.S48.s48_Q μ J φ = Q := rfl
  have hfac1 : Cm * Dfac ≤ max Dfac (Cm * Dfac) :=
    le_max_right _ _
  have hfac2 : Dfac ≤ max Dfac (Cm * Dfac) :=
    le_max_left _ _
  have hχcd1 : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) χ := hχcd.of_le (by
    exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  have hgradcd : ContDiff ℝ (k : WithTop ℕ∞) (gradient χ) :=
    HRS.MS.R26T3.s21h2_s03_grad_cd hχcd1
  have hgrad : HasCbBound k
      (max Dfac (Cm * Dfac) * Q) (gradient χ) := by
    refine ⟨hgradcd, ?_⟩
    intro i hi x
    rw [HRS.MS.Gap.gap1_norm_iter_gradient]
    have h := hχder (i + 1) (by omega) (by omega) x
    calc ‖iteratedFDeriv ℝ (i + 1) χ x‖ ≤ Cm * D := h
      _ = (Cm * Dfac) * Q := by dsimp [D]; ring
      _ ≤ max Dfac (Cm * Dfac) * Q :=
        mul_le_mul_of_nonneg_right hfac1 hQ0
  have hχgen : ∀ x, weightedGen ρ χ x = aφ x := by
    intro x
    have hgl := HRS.MS.Gap.gap_gradient_log hR x
    show -Laplacian.laplacian χ x -
      inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient χ x) = aφ x
    rw [hgl]
    have hx := hχeq x
    unfold poissonOp at hx
    exact hx
  refine ⟨aφ, χ, hresp, haφs.of_le (by exact_mod_cast (show k + 1 ≤ k + 2 by omega)),
    ?_, hχcd, hχgen, ?_⟩
  · intro i hi1 hik x
    have h := haφder i hi1 (by omega) x
    calc ‖iteratedFDeriv ℝ i aφ x‖ ≤ Dfac * Q := by simpa [D] using h
      _ ≤ max Dfac (Cm * Dfac) * Q :=
        mul_le_mul_of_nonneg_right hfac2 hQ0
  · simpa [Dfac, hQ] using hgrad

/-- At the actual initial law, the canonical response and a compatible derivative corrector
obey the explicit S4.8 order ceil(k₀ + 2 + d/2) + 1. The common constant is selected before q. -/
theorem fp81s21_initial_corrector_explicit
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Euc p.d → ℝ,
      MemCb (fp81s21_correctorOrder p.d) q →
        ContDiff ℝ ((fp81s21_k0 p.d + 1 : ℕ) : WithTop ℕ∞)
          (r26t3_a R q) ∧
        (∀ i : ℕ, 1 ≤ i → i ≤ fp81s21_k0 p.d + 1 → ∀ x,
          ‖iteratedFDeriv ℝ i (r26t3_a R q) x‖ ≤
            C * HRS.MS.S48.s48_Q (r26t3_mu R 0) (fp81s21_correctorOrder p.d) q) ∧
        ∃ χ : Euc p.d → ℝ,
          ContDiff ℝ ((fp81s21_k0 p.d + 2 : ℕ) : WithTop ℕ∞) χ ∧
          (∀ x, weightedGen (R.ρ 0) χ x = r26t3_a R q x) ∧
          HasCbBound (fp81s21_k0 p.d)
            (C * HRS.MS.S48.s48_Q (r26t3_mu R 0) (fp81s21_correctorOrder p.d) q)
            (gradient χ) := by
  have hdp : 2 ≤ p.d := p.hd
  have hsd : p.s < p.d := by
    have hdpos : (0 : ℝ) < p.d := by exact_mod_cast (show 0 < p.d by omega)
    have hdhalf : (p.d : ℝ) / 2 ≤ p.d := by
      have hdp : (2 : ℝ) ≤ p.d := by exact_mod_cast p.hd
      nlinarith
    exact lt_of_lt_of_le p.hs hdhalf
  have hJle := fp81s21_correctorOrder_le p.d p.hd
  have hJspec := fp81s21_correctorOrder_spec p.d
  have hd1 : 1 ≤ p.d := by omega
  have hqβ : 0 < p.a * p.β := mul_pos p.ha p.hβ
  let k : ℕ := fp81s21_k0 p.d
  let J : ℕ := fp81s21_correctorOrder p.d
  let m : ℕ := k + 2
  let M : ℕ := Nat.ceil (((m : ℝ) + (p.d : ℝ) / 2) / ((p.d : ℝ) - p.s)) + 1
  let N : ℕ := J + Nat.ceil ((M : ℝ) * ((p.d : ℝ) - p.s) + p.d) + 1
  have hmJ : m ≤ J := by
    have hmcast : (m : ℝ) ≤ J := by
      have hs := hJspec
      dsimp [m, k, J] at hs ⊢
      push_cast at hs ⊢
      linarith
    exact_mod_cast hmcast
  have hJ : (m : ℝ) + p.d / 2 < J := by
    have hs := hJspec
    dsimp [m, k, J] at hs ⊢
    push_cast at hs ⊢
    linarith
  have hM : (m : ℝ) + p.d / 2 < M * ((p.d : ℝ) - p.s) :=
    HRS.MS.Tc5.tc5_M_spec hsd m
  have hN : (J : ℝ) + M * ((p.d : ℝ) - p.s) + p.d < N := by
    have hceil := Nat.le_ceil ((M : ℝ) * ((p.d : ℝ) - p.s) + p.d)
    have hle : (J : ℝ) + (Nat.ceil ((M : ℝ) * ((p.d : ℝ) - p.s) + p.d) : ℕ) + 1 ≤ N := by
      dsimp [N]
      push_cast
      linarith
    linarith
  have hmN : m ≤ N := by
    dsimp [N]
    omega
  have hNtc : (M : ℝ) * ((p.d : ℝ) - p.s) + p.d < N := by
    have hJ0 : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
    linarith
  have hA := R.admissible
  have hRes := R.resulting
  have hρβ : R.ρβ = thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hosc : 0 ≤ oscNorm (102 * (p.d : ℝ) + 1020)
      (fun x => R.ε * Real.sqrt (R.ρβ x) * R.ψ x) := Real.sqrt_nonneg _
  have hcb : cbNorm (100 * p.d + 1001) (fun x => R.ε * R.ψ x) ≤ δ := by
    have := hA.small
    linarith
  have hcb0 := HRS.MS.S48.s48_cbu_bound hA.smooth hA.compactSupport R.ε δ
    (100 * p.d + 1001) hcb 0 (Nat.zero_le _)
  have htilt : IsTiltData p.d p.s p.a p.β R.ψ R.ε :=
    ⟨hA.smooth, hA.compactSupport, by rw [← hρβ]; exact hA.meanZero, fun x => by
      have := hcb0 x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      linarith⟩
  have hρ0 : R.ρ 0 =
      perturbedDensity (thermalDensity p.d p.s p.a p.β) R.ε R.ψ := by
    rw [hRes.init, hρβ]
  have hstatic : IsStaticReference p.d p.s p.a p.β R.ψ (R.ρ 0) := by
    rw [hρ0]
    exact IsStaticReference.perturbed R.ε htilt
  obtain ⟨c, M₀, m₂, hc, hM₀, hpk⟩ :=
    HRS.MS.S48.s48_ref_data p.hd p.hs0 hsd p.ha p.hβ le_rfl le_rfl R.ψ
  obtain ⟨S, Mb, hpkN⟩ := hpk N J
  have P : HRS.MS.S48.S48Pkg p.d (R.ρ 0) (p.a * p.β) M₀ c S Mb m₂ N J :=
    hpkN p.a p.β le_rfl le_rfl le_rfl le_rfl (R.ρ 0) hstatic
  have hQPkg := fp81s21_corrector_from_pkg p.hd p.hs0 hsd k J M N hmJ hJ hM hN
    hqβ hγ le_rfl hc P
  obtain ⟨C, hC0, hcorrector⟩ := hQPkg
  obtain ⟨C5, hC50, hC5ρ⟩ := HRS.MS.Tc5.tc5_resolvent_rep
    (d := p.d) p.hs0 hsd m J M hmJ hM p.γ M₀ c S hc N hmN hNtc
  refine ⟨C, hC0, fun q hq => ?_⟩
  obtain ⟨aφ, χ, hresp, haφcd, haφder, hχcd, hχgen, hgrad⟩ := hcorrector q hq
  obtain ⟨r₀', r', hr₀', hreq', hr'cb, hr'bd, hr'ae⟩ :=
    hC5ρ (R.ρ 0) P.ref p.γ hγ le_rfl q hq
  obtain ⟨hrep, hrespCanon⟩ := HRS.MS.S98.s98_resp_rep (d := p.d) hd1
    p.hs0 hsd hc P.ref hγ hq.1.continuous hr'cb.1.continuous
    (B := cbNorm m r') (fun x => by
      have h := HRS.MS.Tc5.tc5_cb_sup_le hr'cb x
      rwa [Real.norm_eq_abs] at h) hr₀' hreq' hr'ae
  have hcanonEq : ∀ x, r26t3_a R q x = p.γ⁻¹ * r' x := by
    intro x
    simpa [r26t3_a, r26t3_mu] using hrep x
  have hrespAE : aφ =ᵐ[r26t3_mu R 0] r26t3_a R q :=
    HRS.MS.S98.s98_resp_unique hd1 p.hs0 hsd hc P.ref hγ hresp hrespCanon
  have hρmeas : Measurable (fun x : Euc p.d => ENNReal.ofReal (R.ρ 0 x)) :=
    ENNReal.measurable_ofReal.comp E.reference.smooth.continuous.measurable
  have hrespVol : ∀ᵐ x ∂(volume : Measure (Euc p.d)),
      aφ x = r26t3_a R q x := by
    have h := (ae_withDensity_iff hρmeas).1 hrespAE
    filter_upwards [h] with x hx
    exact hx (by simpa using E.reference.pos x)
  have hcanonCont : Continuous (r26t3_a R q) := by
    have he : r26t3_a R q = fun x => p.γ⁻¹ * r' x := funext hcanonEq
    rw [he]
    exact continuous_const.mul hr'cb.1.continuous
  have hacanCD : ContDiff ℝ ((fp81s21_k0 p.d + 1 : ℕ) : WithTop ℕ∞)
      (r26t3_a R q) := by
    have he : r26t3_a R q = fun x => p.γ⁻¹ * r' x := funext hcanonEq
    rw [he]
    exact contDiff_const.mul (hr'cb.1.of_le (by exact_mod_cast (show k + 1 ≤ m by dsimp [m, k]; omega)))
  have hall : ∀ x : Euc p.d, aφ x = r26t3_a R q x := by
    have h := (Continuous.ae_eq_iff_eq (volume : Measure (Euc p.d))
      haφcd.continuous hcanonCont).1 hrespVol
    exact fun x => congrFun h x
  have hfun : aφ = r26t3_a R q := funext hall
  refine ⟨hacanCD, ?_, ?_⟩
  · intro i hi1 hik x
    rw [← hfun]
    have h := haφder i hi1 hik x
    simpa [r26t3_mu] using h
  · refine ⟨χ, hχcd, ?_, ?_⟩
    · intro x
      rw [hχgen x, hall x]
    · simpa [r26t3_mu] using hgrad

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_correctorOrder_spec
#print axioms HRS.Fp81.S21.fp81s21_correctorOrder_le
#print axioms HRS.Fp81.S21.fp81s21_corrector_from_pkg
#print axioms HRS.Fp81.S21.fp81s21_initial_corrector_explicit
