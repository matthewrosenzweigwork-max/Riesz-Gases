import HRS.Sections.ScrnAux36
import HRS.PDE.MeanFieldLinearGaussian

/-!
# Packet SCRN, part 37: the particle covariance matrix `Q_N`, its entries and its comparison with `mesoCovMatrix`

`scrnQ f ts T invβ = Cov_Haar(f^0) + ∫_0^T Σ̄` (the covariance of the Gaussian in `scrn_assembly`).
* `scrn_sig_det`, `scrn_Q_psd`: `Σ̄` is a deterministic covariance density and `Q_N` is positive semidefinite.
* `scrn_Q_entry`: `Q_N^{ac} = Re ∑_{k≠0} ℓ^d scrnGab(ℓk)` (Fourier side).
* `scrn_Q_gauss`: `d₃(N(0,Q_N), N(0,mesoCov)) ≤ ½ p² C (ℓ + |b_N - b|)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

variable {d : ℕ}

open PDE

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-- The covariance `Cov_Haar(f^0) + ∫_0^T Σ̄` of the Gaussian of `scrn_assembly`. -/
def scrnQ {p : ℕ} (f : Fin p → ℝ → Torus d → ℝ) (ts : Fin p → ℝ) (T invβ : ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  (Matrix.of fun a b => ∫ y, (scrnFvec f y a - (∫ y', scrnFvec f y' ∂(volume : Measure (Torus d))) a) *
      (scrnFvec f y b - (∫ y', scrnFvec f y' ∂(volume : Measure (Torus d))) b)
      ∂(volume : Measure (Torus d))) +
    integratedCov T (scrnSig ts (scrnGc ts f) (2 * invβ))

theorem scrn_sig_det {p : ℕ} {T : ℝ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc 0 T)
    (f : Fin p → ℝ → Torus d → ℝ) (hC12 : ∀ a, ∃ ft, IsC12Test (ts a) (f a) ft) {c : ℝ}
    (hc : 0 ≤ c) : IsDetCovMatrix T (scrnSig ts (scrnGc ts f) c) := by
  have hGm : ∀ a, Measurable fun p : ℝ × Torus d => scrnGc ts f a p.1 p.2 := by
    intro a
    obtain ⟨ft, hft⟩ := hC12 a
    have hm := measurable_grad_clamp (hts a).1 hft
    have e : (fun p : ℝ × Torus d => scrnGc ts f a p.1 p.2) = fun p =>
        if p.1 ∈ Set.Icc (0 : ℝ) (ts a) then Torus.grad (f a (clampTI (ts a) p.1)) p.2 else 0 := by
      funext p
      unfold scrnGc
      split_ifs with h
      · rw [clampTI_of_mem h]
      · rfl
    rw [e]
    exact Measurable.ite (measurableSet_Icc.preimage measurable_fst) hm measurable_const
  have hGb : ∀ a r x, ‖scrnGc ts f a r x‖ ≤ ∑ a', |(grad_bound (hts a').1 (hC12 a').choose_spec).choose| := by
    intro a r x
    have hnn : ∀ a', 0 ≤ |(grad_bound (hts a').1 (hC12 a').choose_spec).choose| := fun a' => abs_nonneg _
    refine le_trans ?_ (Finset.single_le_sum (fun a' _ => hnn a') (Finset.mem_univ a))
    unfold scrnGc
    split_ifs with h
    · exact ((grad_bound (hts a).1 (hC12 a).choose_spec).choose_spec r h x).trans (le_abs_self _)
    · simp only [norm_zero]; exact hnn a
  exact scrnSig_isDet (ts := ts) (G := scrnGc ts f) (c := c) hGm hGb hc T

theorem scrn_Q_psd {p : ℕ} {T : ℝ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc 0 T)
    (f : Fin p → ℝ → Torus d → ℝ) (hC12 : ∀ a, ∃ ft, IsC12Test (ts a) (f a) ft)
    (hfc : ∀ a, Continuous (f a 0)) {invβ : ℝ} (hβ : 0 ≤ invβ) :
    (scrnQ f ts T invβ).PosSemidef := by
  unfold scrnQ
  refine Matrix.PosSemidef.add ?_ (integratedCov_psd (scrn_sig_det ts hts f hC12 (by positivity)))
  have h := scrn_gram_psd (d := d) (fun a y => f a 0 y - ∫ y', f a 0 y' ∂(volume : Measure (Torus d)))
    (fun a => (hfc a).sub continuous_const)
  convert h using 2
  ext a b
  simp only [Matrix.of_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  rw [scrn_integral_fvec_apply hfc a, scrn_integral_fvec_apply hfc b]
  rfl


theorem scrn_Q_entry (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β ℓ : ℝ} (hβ : 0 < β)
    (hℓ : 0 < ℓ) (x₀ : Euc d) {p : ℕ} (φ : Fin p → Euc d → ℝ)
    (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a))
    (t : Fin p → ℝ) (ht : ∀ a, 0 ≤ t a) {T : ℝ}
    (hT : ∀ a, ℓ ^ (2 - ((d : ℝ) - s)) * t a ≤ T) (f : Fin p → ℝ → Torus d → ℝ)
    (hfc : ∀ a, ∀ r ∈ Set.Icc 0 (ℓ ^ (2 - ((d : ℝ) - s)) * t a), ∀ k : Lattice d,
      coeffOf (f a r) k = ((Real.exp (-(ℓ ^ (2 - ((d : ℝ) - s)) * t a - r) * scrnLam d s β⁻¹ k) : ℝ) : ℂ) *
        coeffOf (mesoTest d ℓ x₀ (φ a)) k)
    (hf2 : ∀ a, ∀ r ∈ Set.Icc 0 (ℓ ^ (2 - ((d : ℝ) - s)) * t a), Torus.IsCk 2 (f a r))
    (hfcont : ∀ a, Continuous (f a 0)) (a c : Fin p) :
    scrnQ f (fun a => ℓ ^ (2 - ((d : ℝ) - s)) * t a) T β⁻¹ a c =
      (∑' k : Lattice d, if k = 0 then (0 : ℂ) else
        ((ℓ ^ d : ℝ) : ℂ) * scrnGab d s (β * ℓ ^ ((d : ℝ) - s)) t φ a c (ℓ • Lattice.toEuc k)).re := by
  have hcr : 0 < rieszConst d s := rieszConst_pos hd hs0 hsd
  have hts0 : ∀ a, 0 ≤ ℓ ^ (2 - ((d : ℝ) - s)) * t a := fun a =>
    mul_nonneg (Real.rpow_nonneg hℓ.le _) (ht a)
  have hlam0 : ∀ k, 0 ≤ scrnLam d s β⁻¹ k := fun k => scrn_lam_nonneg hcr (inv_nonneg.2 hβ.le) k
  have hlam : ∀ k : Lattice d, k ≠ 0 → 0 < scrnLam d s β⁻¹ k := by
    intro k hk
    rw [scrn_lam_eq _ hk]
    have hr : 0 < 2 * Real.pi * Lattice.enorm k := by
      have := one_le_enorm_of_ne_zero hk
      positivity
    have := inv_pos.2 hβ
    positivity
  have hψ : ∀ a, Torus.IsCk 2 (mesoTest d ℓ x₀ (φ a)) := fun a =>
    isCk_mesoTest hℓ x₀ (hφ a).1 (hφ a).2 2 (by
      have h : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
      exact h)
  have h1 := scrn_Q_formula (ts := fun a => ℓ ^ (2 - ((d : ℝ) - s)) * t a) hts0 hT β⁻¹
    (scrnLam d s β⁻¹) hlam0 hlam (fun a => mesoTest d ℓ x₀ (φ a)) hψ f hf2 hfc a c
  have h2 := scrn_lattice_hasSum hd hs0 hsd hβ hℓ x₀ φ hφ t ht a c
  have h3 := h1.unique h2
  have hsig : scrnSig (fun a => ℓ ^ (2 - ((d : ℝ) - s)) * t a)
      (scrnGc (fun a => ℓ ^ (2 - ((d : ℝ) - s)) * t a) f) (2 * β⁻¹) =
      scrnSigBar (fun a => ℓ ^ (2 - ((d : ℝ) - s)) * t a) f (2 * β⁻¹) :=
    funext (scrnSig_eq_scrnSigBar _ f _)
  rw [← h3]
  unfold scrnQ
  rw [hsig]
  simp only [Matrix.add_apply, Matrix.of_apply, integratedCov]
  rw [scrn_integral_fvec_apply hfcont a, scrn_integral_fvec_apply hfcont c]
  rfl

theorem scrn_Q_gauss (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {p : ℕ}
    (φ : Fin p → Euc d → ℝ) (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a))
    (x₀ : Euc d) {bm : ℝ} (hbm : 0 < bm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {β ℓ b : ℝ}, 0 < β → 0 < ℓ → ℓ ≤ 1 → bm ≤ β * ℓ ^ ((d : ℝ) - s) → bm ≤ b →
      ∀ (t : Fin p → ℝ), (∀ a, 0 ≤ t a) → ∀ {T : ℝ}, (∀ a, ℓ ^ (2 - ((d : ℝ) - s)) * t a ≤ T) →
      ∀ (f : Fin p → ℝ → Torus d → ℝ),
      (∀ a, ∀ r ∈ Set.Icc 0 (ℓ ^ (2 - ((d : ℝ) - s)) * t a), ∀ k : Lattice d,
        coeffOf (f a r) k = ((Real.exp (-(ℓ ^ (2 - ((d : ℝ) - s)) * t a - r) * scrnLam d s β⁻¹ k) : ℝ) : ℂ) *
          coeffOf (mesoTest d ℓ x₀ (φ a)) k) →
      (∀ a, ∀ r ∈ Set.Icc 0 (ℓ ^ (2 - ((d : ℝ) - s)) * t a), Torus.IsCk 2 (f a r)) →
      (∀ a, Continuous (f a 0)) →
      (∀ a, ∃ ft, IsC12Test (ℓ ^ (2 - ((d : ℝ) - s)) * t a) (f a) ft) →
      smoothDist 3 (multivariateGaussian 0
          (scrnQ f (fun a => ℓ ^ (2 - ((d : ℝ) - s)) * t a) T β⁻¹))
        (multivariateGaussian 0 (mesoCovMatrix d s b t φ)) ≤
      C * (ℓ + |β * ℓ ^ ((d : ℝ) - s) - b|) := by
  obtain ⟨Cc, hCc, hcmp⟩ := scrn_cov_compare hd hs0 hsd φ hφ hbm
  refine ⟨(p : ℝ) ^ 2 * Cc, by positivity, fun {β ℓ b} hβ hℓ hℓ1 hbN hb t ht {T} hT f hfc hf2 hfcont hC12 => ?_⟩
  have hts0 : ∀ a, 0 ≤ ℓ ^ (2 - ((d : ℝ) - s)) * t a := fun a =>
    mul_nonneg (Real.rpow_nonneg hℓ.le _) (ht a)
  have hbpos : 0 < b := hbm.trans_le hb
  have hQ := scrn_Q_psd (T := T) (fun a => ℓ ^ (2 - ((d : ℝ) - s)) * t a)
    (fun a => ⟨hts0 a, hT a⟩) f hC12 hfcont (inv_nonneg.2 hβ.le)
  have hQ' := scrn_mesoCov_psd hd hs0 hsd φ hφ hbpos t ht
  have hent : ∀ i j : Fin p, |(scrnQ f (fun a => ℓ ^ (2 - ((d : ℝ) - s)) * t a) T β⁻¹ -
      mesoCovMatrix d s b t φ) i j| ≤ Cc * (ℓ + |β * ℓ ^ ((d : ℝ) - s) - b|) := by
    intro i j
    rw [Matrix.sub_apply, scrn_Q_entry hd hs0 hsd hβ hℓ x₀ φ hφ t ht hT f hfc hf2 hfcont i j]
    exact hcmp t ht ℓ hℓ hℓ1 (β * ℓ ^ ((d : ℝ) - s)) b hbN hb i j
  have htr := HRS.PDE.MFLinear.traceNormMatrix_le_sum (scrnQ f (fun a => ℓ ^ (2 - ((d : ℝ) - s)) * t a) T β⁻¹ -
      mesoCovMatrix d s b t φ)
  have hsum : ∑ i : Fin p, ∑ j : Fin p, |(scrnQ f (fun a => ℓ ^ (2 - ((d : ℝ) - s)) * t a) T β⁻¹ -
          mesoCovMatrix d s b t φ) i j| ≤ (p : ℝ) ^ 2 * (Cc * (ℓ + |β * ℓ ^ ((d : ℝ) - s) - b|)) := by
    calc _ ≤ ∑ _i : Fin p, ∑ _j : Fin p, Cc * (ℓ + |β * ℓ ^ ((d : ℝ) - s) - b|) := by
          gcongr with i _ j _
          exact hent i j
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hE : 0 ≤ Cc * (ℓ + |β * ℓ ^ ((d : ℝ) - s) - b|) := by positivity
  calc _ ≤ _ := smoothDist_gaussian_covariance _ _ hQ hQ'
    _ ≤ 1 / 2 * ((p : ℝ) ^ 2 * (Cc * (ℓ + |β * ℓ ^ ((d : ℝ) - s) - b|))) := by
        gcongr
        exact htr.trans hsum
    _ ≤ (p : ℝ) ^ 2 * Cc * (ℓ + |β * ℓ ^ ((d : ℝ) - s) - b|) := by
        have : 0 ≤ (p : ℝ) ^ 2 * (Cc * (ℓ + |β * ℓ ^ ((d : ℝ) - s) - b|)) := by positivity
        nlinarith

end HRS
