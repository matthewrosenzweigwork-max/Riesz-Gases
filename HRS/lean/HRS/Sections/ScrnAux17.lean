import HRS.Sections.ScrnAux16

/-!
# Packet SCRN, part 17: the particle covariance as the lattice sum compared in `scrn_cov_compare`

For `ψ_a = mesoTest d ℓ x₀ φ_a`, `λ_k = scrnLam d s β⁻¹ k`, `T_a = ℓ^{2-q} t_a`, `b_N = β ℓ^q`:
`conj(ψ̂_a(k)) ψ̂_c(k) κ_k` has real part `Re(ℓ^d scrnGab(b_N, t)(ℓk))`, so the Fourier-side series of
`scrn_Q_formula` has the sum `(∑' k≠0, ℓ^d scrnGab(ℓk)).re` (`scrn_lattice_hasSum`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate FourierTransform

namespace HRS

variable {d : ℕ}

open PDE

lemma scrn_summable_prod_norm {u v : Torus d → ℝ} (hu : Continuous u) (hv : Continuous v) :
    Summable fun k : Lattice d => ‖coeffOf u k‖ * ‖coeffOf v k‖ := by
  have h1 := (scrn_parseval_re hu hu).summable
  have h2 := (scrn_parseval_re hv hv).summable
  have e : ∀ (w : Torus d → ℝ) (k : Lattice d),
      (conj (coeffOf w k) * coeffOf w k).re = ‖coeffOf w k‖ ^ 2 := by
    intro w k
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((h1.add h2).mul_left (1 / 2))
  have := e u k
  have := e v k
  nlinarith [sq_nonneg (‖coeffOf u k‖ - ‖coeffOf v k‖)]

lemma scrn_kappa_eq {s : ℝ} (hc : 0 < rieszConst d s) {β ℓ : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ)
    {p : ℕ} (t : Fin p → ℝ) (a c : Fin p) {k : Lattice d} (hk : k ≠ 0) :
    scrnKappa β⁻¹ (scrnLam d s β⁻¹) (ℓ ^ (2 - ((d : ℝ) - s)) * t a)
        (ℓ ^ (2 - ((d : ℝ) - s)) * t c) k =
      scrnKab d s (β * ℓ ^ ((d : ℝ) - s)) t a c (ℓ • Lattice.toEuc k) := by
  unfold scrnKappa scrnKab scrnk
  rw [norm_smul_toEuc hℓ k]
  have hS := scrn_S_scale (s := s) hβ hℓ hk hc
  have hA := scrn_lam_scale (s := s) hβ hℓ hk
  rw [← hS]
  have hℓp : 0 < ℓ ^ (2 - ((d : ℝ) - s)) := Real.rpow_pos_of_pos hℓ _
  rw [← mul_sub, abs_mul, abs_of_pos hℓp, ← mul_add]
  have e1 : -(ℓ ^ (2 - ((d : ℝ) - s)) * |t a - t c|) * scrnLam d s β⁻¹ k =
      -|t a - t c| * scrnA (rieszConst d s) ((d : ℝ) - s) (β * ℓ ^ ((d : ℝ) - s))
        (2 * Real.pi * (ℓ * Lattice.enorm k)) := by
    rw [← hA]; ring
  have e2 : -(ℓ ^ (2 - ((d : ℝ) - s)) * (t a + t c)) * scrnLam d s β⁻¹ k =
      -(t a + t c) * scrnA (rieszConst d s) ((d : ℝ) - s) (β * ℓ ^ ((d : ℝ) - s))
        (2 * Real.pi * (ℓ * Lattice.enorm k)) := by
    rw [← hA]; ring
  rw [e1, e2]

lemma scrn_re_conj_psi {ℓ : ℝ} (hℓ : 0 < ℓ) (x₀ : Euc d) {φ φ' : Euc d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hφ' : ContDiff ℝ (⊤ : ℕ∞) φ') (hc' : HasCompactSupport φ') (k : Lattice d) :
    (conj (coeffOf (mesoTest d ℓ x₀ φ) k) * coeffOf (mesoTest d ℓ x₀ φ') k).re =
      ℓ ^ d * (𝓕 (scrnPhiC φ) (ℓ • Lattice.toEuc k) *
        conj (𝓕 (scrnPhiC φ') (ℓ • Lattice.toEuc k))).re := by
  rw [PDE.coeffOf_eq_fcoef, PDE.coeffOf_eq_fcoef, scrn_fcoef_mesoTest hℓ x₀ hφ hc,
    scrn_fcoef_mesoTest hℓ x₀ hφ' hc']
  set θ : ℝ := -(2 * Real.pi * Lattice.dot k x₀) with hθ
  set P := 𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) (ℓ • Lattice.toEuc k) with hP
  set P' := 𝓕 (fun x : Euc d => ((φ' x : ℝ) : ℂ)) (ℓ • Lattice.toEuc k) with hP'
  have hl : ((ℓ ^ ((d : ℝ) / 2) : ℝ) : ℂ) * ((ℓ ^ ((d : ℝ) / 2) : ℝ) : ℂ) = ((ℓ ^ d : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hℓ]
    congr 1
    rw [← two_mul, mul_div_cancel₀ _ (two_ne_zero)]
    exact Real.rpow_natCast ℓ d
  have hE : conj (Complex.exp ((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show (θ : ℂ) * -Complex.I + (θ : ℂ) * Complex.I = 0 by ring]
    simp
  have e : conj (((ℓ ^ ((d : ℝ) / 2) : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * P) *
      (((ℓ ^ ((d : ℝ) / 2) : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * P') =
      ((ℓ ^ d : ℝ) : ℂ) * (conj P * P') := by
    simp only [map_mul, Complex.conj_ofReal]
    calc _ = (((ℓ ^ ((d : ℝ) / 2) : ℝ) : ℂ) * ((ℓ ^ ((d : ℝ) / 2) : ℝ) : ℂ)) *
          (conj (Complex.exp ((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I)) *
          (conj P * P') := by ring
      _ = _ := by rw [hl, hE]; ring
  rw [e, Complex.re_ofReal_mul]
  congr 1
  have : (conj P * P').re = (P * conj P').re := by
    have h := Complex.conj_re (conj P * P')
    rw [← h]; simp [mul_comm]
  rw [this]
  rfl

lemma scrn_norm_psi {ℓ : ℝ} (hℓ : 0 < ℓ) (x₀ : Euc d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (k : Lattice d) :
    ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ =
      ℓ ^ ((d : ℝ) / 2) * ‖𝓕 (scrnPhiC φ) (ℓ • Lattice.toEuc k)‖ := by
  rw [PDE.coeffOf_eq_fcoef, scrn_fcoef_mesoTest hℓ x₀ hφ hc, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hℓ _), mul_one]
  rfl

theorem scrn_lattice_hasSum (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β ℓ : ℝ}
    (hβ : 0 < β) (hℓ : 0 < ℓ) (x₀ : Euc d) {p : ℕ} (φ : Fin p → Euc d → ℝ)
    (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a))
    (t : Fin p → ℝ) (ht : ∀ a, 0 ≤ t a) (a c : Fin p) :
    HasSum (fun k : Lattice d => if k = 0 then (0 : ℝ) else
        (conj (coeffOf (mesoTest d ℓ x₀ (φ a)) k) * coeffOf (mesoTest d ℓ x₀ (φ c)) k).re *
          scrnKappa β⁻¹ (scrnLam d s β⁻¹) (ℓ ^ (2 - ((d : ℝ) - s)) * t a)
            (ℓ ^ (2 - ((d : ℝ) - s)) * t c) k)
      ((∑' k : Lattice d, if k = 0 then (0 : ℂ) else
        ((ℓ ^ d : ℝ) : ℂ) * scrnGab d s (β * ℓ ^ ((d : ℝ) - s)) t φ a c (ℓ • Lattice.toEuc k)).re) := by
  have hcr : 0 < rieszConst d s := rieszConst_pos hd hs0 hsd
  have hb : 0 < β * ℓ ^ ((d : ℝ) - s) := mul_pos hβ (Real.rpow_pos_of_pos hℓ _)
  have hcont : ∀ b, Continuous (mesoTest d ℓ x₀ (φ b)) := fun b =>
    scrn_cont_of_ck2 (isCk_mesoTest hℓ x₀ (hφ b).1 (hφ b).2 2
      (by have h : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
          exact h))
  set z : Lattice d → ℂ := fun k => if k = 0 then (0 : ℂ) else
        ((ℓ ^ d : ℝ) : ℂ) * scrnGab d s (β * ℓ ^ ((d : ℝ) - s)) t φ a c (ℓ • Lattice.toEuc k) with hz
  have hsum : Summable z := by
    refine Summable.of_norm_bounded (scrn_summable_prod_norm (hcont a) (hcont c)) (fun k => ?_)
    by_cases hk : k = 0
    · simp only [hz, hk, if_true, norm_zero]
      positivity
    · simp only [hz, hk, if_false]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hℓ d),
        scrn_norm_psi hℓ x₀ (hφ a).1 (hφ a).2, scrn_norm_psi hℓ x₀ (hφ c).1 (hφ c).2]
      unfold scrnGab
      rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      have hK0 : 0 ≤ scrnKab d s (β * ℓ ^ ((d : ℝ) - s)) t a c (ℓ • Lattice.toEuc k) :=
        scrnk_nonneg' hcr hb (by positivity)
      have hK1 : scrnKab d s (β * ℓ ^ ((d : ℝ) - s)) t a c (ℓ • Lattice.toEuc k) ≤ 1 :=
        scrnk_le_one' hcr hb (by positivity) (abs_nonneg _) (add_nonneg (ht a) (ht c))
      rw [abs_of_nonneg hK0]
      have hl : ℓ ^ d = ℓ ^ ((d : ℝ) / 2) * ℓ ^ ((d : ℝ) / 2) := by
        rw [← Real.rpow_add hℓ, ← two_mul, mul_div_cancel₀ _ (two_ne_zero)]
        exact (Real.rpow_natCast ℓ d).symm
      have hn : 0 ≤ ‖𝓕 (scrnPhiC (φ a)) (ℓ • Lattice.toEuc k)‖ *
          ‖𝓕 (scrnPhiC (φ c)) (ℓ • Lattice.toEuc k)‖ := by positivity
      calc ℓ ^ d * (‖𝓕 (scrnPhiC (φ a)) (ℓ • Lattice.toEuc k)‖ *
            ‖𝓕 (scrnPhiC (φ c)) (ℓ • Lattice.toEuc k)‖ *
            scrnKab d s (β * ℓ ^ ((d : ℝ) - s)) t a c (ℓ • Lattice.toEuc k))
          ≤ ℓ ^ d * (‖𝓕 (scrnPhiC (φ a)) (ℓ • Lattice.toEuc k)‖ *
            ‖𝓕 (scrnPhiC (φ c)) (ℓ • Lattice.toEuc k)‖ * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK1 hn) (pow_nonneg hℓ.le _)
        _ = _ := by rw [hl]; ring
  have hre : HasSum (fun k => (z k).re) ((∑' k, z k).re) := Complex.reCLM.hasSum hsum.hasSum
  convert hre using 1
  funext k
  by_cases hk : k = 0
  · simp [hz, hk]
  · simp only [hz, hk, if_false]
    rw [scrn_re_conj_psi hℓ x₀ (hφ a).1 (hφ a).2 (hφ c).1 (hφ c).2,
      scrn_kappa_eq hcr hβ hℓ t a c hk]
    unfold scrnGab
    have : ∀ (w : ℂ) (K : ℝ), (((ℓ ^ d : ℝ) : ℂ) * (w * ((K : ℝ) : ℂ))).re = ℓ ^ d * (w.re * K) := by
      intro w K
      rw [Complex.re_ofReal_mul, Complex.re_mul_ofReal]
    rw [this]
    ring

end HRS
