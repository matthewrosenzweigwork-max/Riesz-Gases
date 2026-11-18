import HRS.PDE.MeanFieldDefs
import HRS.PDE.Toolbox.Levy

/-!
# (I3) AP5a: Bernstein-type bound for the smoothly truncated force (package MF-01)

`forceLow d s i n c` is the Fourier multiplier `χ(2^{-n}k) · 2πi k_i ĝ(k)`.  Since `χ(2k) = 0` on
the lattice minus `0`, `χ(2^{-n}k) = ∑_{ℓ ≤ n} ψ(2^{-ℓ}k)` there (`psiF_sum`), and the `ℓ`-th
piece is the trigonometric polynomial with coefficients `2^{ℓ(s-d+1)} · kcoef Ψ 2^{-ℓ}`,
`Ψ = Dpr i (Phi m₀)`, `m₀ = c_{d,s}(2π‖·‖)^{s-d}`.  Hence `exists_forceLow_sup_bound` follows
from `Kern.kern_L1_bound` and the convolution identity `Fried.kconv`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.MFApriori
variable {d : ℕ}

/-- Smooth low-frequency part of the force multiplier `2πi k_i ĝ(k)` at scale `2^n`
(`chiF = 1` on the unit ball, `0` outside radius `2`). -/
def forceLow (d : ℕ) (s : ℝ) (i : Fin d) (n : ℕ) (c : Coeff d) : Coeff d :=
  fun k => ((LevyAux.chiF d (LevyAux.eps n • Lattice.toEuc k) : ℝ) : ℂ) * gradRieszCoeff d s i c k

/-- the homogeneous symbol `ĝ(ξ) = c_{d,s} (2π‖ξ‖)^{s-d}` -/
def m0 (d : ℕ) (s : ℝ) (ξ : Euc d) : ℝ := rieszConst d s * (2 * Real.pi * ‖ξ‖) ^ (s - (d : ℝ))

theorem m0_smul (d : ℕ) (s : ℝ) {c : ℝ} (hc : 0 < c) (ξ : Euc d) :
    m0 d s (c • ξ) = c ^ (s - (d : ℝ)) * m0 d s ξ := by
  unfold m0
  rw [norm_smul, Real.norm_of_nonneg hc.le, show 2 * Real.pi * (c * ‖ξ‖) = c * (2 * Real.pi * ‖ξ‖) by ring,
    Real.mul_rpow hc.le (by positivity)]
  ring

theorem contDiffOn_m0 (d : ℕ) (s : ℝ) : ContDiffOn ℝ ∞ (m0 d s) {ξ | ξ ≠ 0} := by
  intro ξ hξ
  have hξ' : ξ ≠ 0 := hξ
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ ∞ (fun ξ : Euc d => ‖ξ‖) ξ := contDiffAt_norm ℝ hξ'
  have h2 : ContDiffAt ℝ ∞ (fun ξ : Euc d => 2 * Real.pi * ‖ξ‖) ξ := contDiffAt_const.mul h1
  have h3 : (2 * Real.pi * ‖ξ‖) ≠ 0 := by
    have := norm_pos_iff.2 hξ'; positivity
  exact contDiffAt_const.mul (h2.rpow_const_of_ne h3)

/-- the kernel profile whose dyadic scalings give the pieces of the force -/
def Psi (d : ℕ) (s : ℝ) (i : Fin d) : Euc d → ℂ := LevyAux.Dpr i (LevyAux.Phi (m0 d s))

/-- the `ℓ`-th dyadic piece of the multiplier `2πi k_i ĝ(k)` -/
def forceMult (d : ℕ) (s : ℝ) (i : Fin d) (ℓ : ℕ) (k : Lattice d) : ℂ :=
  ((LevyAux.psiF d (LevyAux.eps ℓ • Lattice.toEuc k) : ℝ) : ℂ) *
    (2 * Real.pi * Complex.I * (k i : ℂ) * ((rieszCoeff d s k : ℝ) : ℂ))

theorem scale_coef (d : ℕ) (s : ℝ) (i : Fin d) (ℓ : ℕ) (k : Lattice d) :
    ((((2 : ℝ) ^ ℓ) ^ (s - (d : ℝ) + 1) : ℝ) : ℂ) * Kern.kcoef (Psi d s i) (LevyAux.eps ℓ) k =
      forceMult d s i ℓ k := by
  by_cases hk : k = 0
  · subst hk
    have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext j; simp [Lattice.toEuc]
    simp [forceMult, Kern.kcoef, Psi, LevyAux.Dpr, h0]
  · have hR : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
    have hm : m0 d s (LevyAux.eps ℓ • Lattice.toEuc k) =
        LevyAux.eps ℓ ^ (s - (d : ℝ)) * rieszCoeff d s k := by
      rw [m0_smul d s (LevyAux.eps_pos ℓ)]
      congr 1
      simp [m0, rieszCoeff, hk, Lattice.enorm]
    have hscal : ((2 : ℝ) ^ ℓ) ^ (s - (d : ℝ) + 1) * (LevyAux.eps ℓ ^ (s - (d : ℝ)) * LevyAux.eps ℓ) = 1 := by
      unfold LevyAux.eps
      rw [Real.inv_rpow hR.le, Real.rpow_add_one hR.ne']
      field_simp
    simp only [Kern.kcoef, Psi, LevyAux.Dpr, LevyAux.Phi, LevyAux.PhiR, forceMult]
    have hi : (LevyAux.eps ℓ • Lattice.toEuc k) i = LevyAux.eps ℓ * (k i : ℝ) := by
      simp [Lattice.toEuc]
    rw [hi, hm]
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) hscal
    simp only [Complex.ofReal_mul, Complex.ofReal_one] at h2
    push_cast
    linear_combination (2 * Real.pi * Complex.I * (k i : ℂ) * ((rieszCoeff d s k : ℝ) : ℂ) *
      ((LevyAux.psiF d (LevyAux.eps ℓ • Lattice.toEuc k) : ℝ) : ℂ)) * h2


theorem forceLow_eq_sum (d : ℕ) (s : ℝ) (i : Fin d) (n : ℕ) (c : Coeff d) (k : Lattice d) :
    forceLow d s i n c k = ∑ ℓ ∈ Finset.range (n + 1), forceMult d s i ℓ k * c k := by
  by_cases hk : k = 0
  · subst hk
    simp [forceLow, forceMult, gradRieszCoeff, derivCoeff]
  · have hsum := LevyAux.psiF_sum (Lattice.toEuc k) n
    have h2 : LevyAux.chiF d ((2 : ℝ) • Lattice.toEuc k) = 0 := by
      apply LevyAux.chiF_zero
      rw [norm_smul]
      have := LevyAux.one_le_norm_toEuc hk
      simp; linarith
    rw [h2, sub_zero] at hsum
    simp only [forceLow, gradRieszCoeff, derivCoeff, rieszMult, forceMult]
    have e : ∀ ℓ, ((LevyAux.psiF d (LevyAux.eps ℓ • Lattice.toEuc k) : ℝ) : ℂ) *
        (2 * Real.pi * Complex.I * (k i : ℂ) * ((rieszCoeff d s k : ℝ) : ℂ)) * c k =
        ((LevyAux.psiF d (LevyAux.eps ℓ • Lattice.toEuc k) : ℝ) : ℂ) *
        (2 * Real.pi * Complex.I * (k i : ℂ) * ((rieszCoeff d s k : ℝ) : ℂ) * c k) := fun ℓ => by ring
    simp_rw [e]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum]
    ring


theorem norm_trig_mul_coeffOf_le {N : ℕ} {a : Lattice d → ℂ} (ha : IsTrigPoly N a) {f : Torus d → ℝ}
    (hf : Continuous f) (x : Torus d) :
    ‖Kern.trig (fun l => a l * coeffOf f l) x‖ ≤ (∫ z, ‖Kern.trig a z‖) * Torus.supNorm f := by
  have hfc : Continuous fun y => ((f y : ℝ) : ℂ) := Complex.continuous_ofReal.comp hf
  have hint : Integrable fun y => ((f y : ℝ) : ℂ) := Fried.integrable_of_continuous_torusC hfc
  have hk := Fried.kconv ha hint x
  have hco : (fun l => a l * coeffOfC (fun y => ((f y : ℝ) : ℂ)) l) = fun l => a l * coeffOf f l := rfl
  rw [hco] at hk
  rw [← hk]
  have hbd : BddAbove (Set.range fun y => ‖f y‖) :=
    (isCompact_range hf.norm).bddAbove
  have hS : ∀ y, ‖f y‖ ≤ Torus.supNorm f := fun y => le_ciSup hbd y
  have hGc : Continuous fun y => Kern.trig a (x - y) := Fried.continuous_trig_sub ha x
  have hGi : Integrable fun y => ‖Kern.trig a (x - y)‖ :=
    (hGc.norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ‖∫ y, Kern.trig a (x - y) * ((f y : ℝ) : ℂ)‖
      ≤ ∫ y, ‖Kern.trig a (x - y)‖ * Torus.supNorm f := by
        refine norm_integral_le_of_norm_le (hGi.mul_const _) (Filter.Eventually.of_forall fun y => ?_)
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left (hS y) (norm_nonneg _)
    _ = (∫ z, ‖Kern.trig a z‖) * Torus.supNorm f := by
        rw [integral_mul_const, integral_sub_left_eq_self (fun y => ‖Kern.trig a y‖) volume x]


theorem contDiff_Psi (d : ℕ) (s : ℝ) (i : Fin d) : ContDiff ℝ ∞ (Psi d s i) :=
  LevyAux.contDiff_Dpr i (LevyAux.contDiff_Phi (contDiffOn_m0 d s))

theorem Psi_large (d : ℕ) (s : ℝ) (i : Fin d) : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → Psi d s i ξ = 0 :=
  LevyAux.Dpr_large i (fun _ h => LevyAux.Phi_large (m0 d s) h)

theorem forceMult_eq (d : ℕ) (s : ℝ) (i : Fin d) (ℓ : ℕ) :
    forceMult d s i ℓ = fun k => ((((2 : ℝ) ^ ℓ) ^ (s - (d : ℝ) + 1) : ℝ) : ℂ) *
      Kern.kcoef (Psi d s i) (LevyAux.eps ℓ) k :=
  funext fun k => (scale_coef d s i ℓ k).symm

theorem isTrigPoly_forceMult (d : ℕ) (s : ℝ) (i : Fin d) (ℓ : ℕ) :
    IsTrigPoly ⌈2 / LevyAux.eps ℓ⌉₊ (forceMult d s i ℓ) := by
  intro k hk
  refine Kern.isTrigPoly_kcoef (Psi_large d s i) (LevyAux.eps_pos ℓ) k ?_
  intro h
  apply hk
  rw [forceMult_eq]
  simp [h]

theorem trig_forceMult (d : ℕ) (s : ℝ) (i : Fin d) (ℓ : ℕ) (z : Torus d) :
    Kern.trig (forceMult d s i ℓ) z = ((((2 : ℝ) ^ ℓ) ^ (s - (d : ℝ) + 1) : ℝ) : ℂ) *
      Kern.kern (Psi d s i) (LevyAux.eps ℓ) z := by
  rw [forceMult_eq]
  unfold Kern.trig Kern.kern
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  rfl

theorem integral_norm_trig_forceMult_le (d : ℕ) (s : ℝ) (i : Fin d) {C0 : ℝ}
    (hC0 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun z => ‖Kern.kern (Psi d s i) ε z‖) ∧ ∫ z, ‖Kern.kern (Psi d s i) ε z‖ ≤ C0)
    (ℓ : ℕ) :
    ∫ z, ‖Kern.trig (forceMult d s i ℓ) z‖ ≤ ((2 : ℝ) ^ ℓ) ^ (s - (d : ℝ) + 1) * C0 := by
  have hr : 0 ≤ ((2 : ℝ) ^ ℓ) ^ (s - (d : ℝ) + 1) := by positivity
  have h := hC0 (LevyAux.eps ℓ) (LevyAux.eps_pos ℓ) (LevyAux.eps_le_one ℓ)
  simp_rw [trig_forceMult, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left h.2 hr


theorem toFun_forceLow_eq (d : ℕ) (s : ℝ) (i : Fin d) (n : ℕ) (c : Coeff d) (x : Torus d) :
    toFun (forceLow d s i n c) x = (Kern.trig (fun k => ∑ ℓ ∈ Finset.range (n + 1), forceMult d s i ℓ k * c k) x).re := by
  have : forceLow d s i n c = fun k => ∑ ℓ ∈ Finset.range (n + 1), forceMult d s i ℓ k * c k :=
    funext fun k => forceLow_eq_sum d s i n c k
  rw [this]
  rfl

/-- geometric sum bound -/
theorem sum_rpow_two_pow_le {θ b : ℝ} (hb : 0 < b) (hθ : θ ≤ b) (n : ℕ) :
    ∑ ℓ ∈ Finset.range (n + 1), ((2 : ℝ) ^ ℓ) ^ θ ≤
      ((2 : ℝ) ^ n) ^ b * ((2 : ℝ) ^ b / ((2 : ℝ) ^ b - 1)) := by
  set ρ : ℝ := (2 : ℝ) ^ b with hρ
  have hρ1 : 1 < ρ := Real.one_lt_rpow (by norm_num) hb
  have h1 : ∀ ℓ : ℕ, ((2 : ℝ) ^ ℓ) ^ θ ≤ ρ ^ ℓ := fun ℓ => by
    calc ((2 : ℝ) ^ ℓ) ^ θ ≤ ((2 : ℝ) ^ ℓ) ^ b :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hθ
      _ = ρ ^ ℓ := LevyAux.rpow_two_pow ℓ b
  calc ∑ ℓ ∈ Finset.range (n + 1), ((2 : ℝ) ^ ℓ) ^ θ ≤ ∑ ℓ ∈ Finset.range (n + 1), ρ ^ ℓ :=
        Finset.sum_le_sum fun ℓ _ => h1 ℓ
    _ = (ρ ^ (n + 1) - 1) / (ρ - 1) := geom_sum_eq hρ1.ne' _
    _ ≤ ρ ^ (n + 1) / (ρ - 1) := by
        gcongr
        linarith
    _ = ((2 : ℝ) ^ n) ^ b * (ρ / (ρ - 1)) := by
        rw [LevyAux.rpow_two_pow n b, pow_succ]; ring

set_option linter.unusedVariables false in
theorem exists_forceLow_sup_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (b : ℝ)
    (hb : max (s - d + 1) 0 < b) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (f : Torus d → ℝ), Continuous f → ∀ x,
      |toFun (forceLow d s i n (coeffOf f)) x| ≤ C * ((2 : ℝ) ^ n) ^ b * Torus.supNorm f := by
  obtain ⟨C0, hC0, hK⟩ := Kern.kern_L1_bound (contDiff_Psi d s i) (Psi_large d s i)
  have hb0 : 0 < b := lt_of_le_of_lt (le_max_right _ _) hb
  have hθb : s - d + 1 ≤ b := (le_max_left _ _).trans hb.le
  have hρ1 : 1 < (2 : ℝ) ^ b := Real.one_lt_rpow (by norm_num) hb0
  refine ⟨C0 * ((2 : ℝ) ^ b / ((2 : ℝ) ^ b - 1)), by
    have : 0 < (2 : ℝ) ^ b - 1 := by linarith
    positivity, fun n f hf x => ?_⟩
  have hbd : BddAbove (Set.range fun y => ‖f y‖) := (isCompact_range hf.norm).bddAbove
  have hS0 : 0 ≤ Torus.supNorm f := (norm_nonneg (f x)).trans (le_ciSup hbd x)
  rw [toFun_forceLow_eq]
  have hterm : ∀ ℓ ∈ Finset.range (n + 1),
      IsTrigPoly (⌈2 / LevyAux.eps ℓ⌉₊) (fun k => forceMult d s i ℓ k * coeffOf f k) :=
    fun ℓ _ => Fried.isTrigPoly_mul_left (isTrigPoly_forceMult d s i ℓ) _
  have hsplit : Kern.trig (fun k => ∑ ℓ ∈ Finset.range (n + 1), forceMult d s i ℓ k * coeffOf f k) x =
      ∑ ℓ ∈ Finset.range (n + 1), Kern.trig (fun k => forceMult d s i ℓ k * coeffOf f k) x := by
    unfold Kern.trig
    rw [← Summable.tsum_finsetSum (fun ℓ hℓ => Kern.summable_trig (hterm ℓ hℓ) x)]
    refine tsum_congr fun k => ?_
    rw [Finset.sum_mul]
  rw [hsplit]
  calc |(∑ ℓ ∈ Finset.range (n + 1), Kern.trig (fun k => forceMult d s i ℓ k * coeffOf f k) x).re|
      ≤ ‖∑ ℓ ∈ Finset.range (n + 1), Kern.trig (fun k => forceMult d s i ℓ k * coeffOf f k) x‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑ ℓ ∈ Finset.range (n + 1), ‖Kern.trig (fun k => forceMult d s i ℓ k * coeffOf f k) x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ ℓ ∈ Finset.range (n + 1), ((2 : ℝ) ^ ℓ) ^ (s - (d : ℝ) + 1) * C0 * Torus.supNorm f :=
        Finset.sum_le_sum fun ℓ _ => by
          refine (norm_trig_mul_coeffOf_le (isTrigPoly_forceMult d s i ℓ) hf x).trans ?_
          exact mul_le_mul_of_nonneg_right (integral_norm_trig_forceMult_le d s i hK ℓ) hS0
    _ = (∑ ℓ ∈ Finset.range (n + 1), ((2 : ℝ) ^ ℓ) ^ (s - (d : ℝ) + 1)) * C0 * Torus.supNorm f := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ (((2 : ℝ) ^ n) ^ b * ((2 : ℝ) ^ b / ((2 : ℝ) ^ b - 1))) * C0 * Torus.supNorm f := by
        gcongr
        exact sum_rpow_two_pow_le hb0 hθb n
    _ = C0 * ((2 : ℝ) ^ b / ((2 : ℝ) ^ b - 1)) * ((2 : ℝ) ^ n) ^ b * Torus.supNorm f := by ring


theorem chiF_nonneg (d : ℕ) (ξ : Euc d) : 0 ≤ LevyAux.chiF d ξ := (LevyAux.bumpD d).nonneg' ξ

theorem chiF_le_one (d : ℕ) (ξ : Euc d) : LevyAux.chiF d ξ ≤ 1 := (LevyAux.bumpD d).le_one

theorem abs_two_pi_le (k : Lattice d) (i : Fin d) :
    |2 * Real.pi * (k i : ℝ)| ≤ 2 * Real.pi * Lattice.enorm k := by
  have h : |(k i : ℝ)| ≤ Lattice.enorm k := by
    have h2 : ‖(Lattice.toEuc k) i‖ ≤ ‖Lattice.toEuc k‖ := PiLp.norm_apply_le _ i
    simpa [Lattice.toEuc, Lattice.enorm] using h2
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- the elementary symbol bound `|2π k_i ĝ(k)|² ≤ C ⟨k⟩^{2(s-d+1)}` -/
theorem sq_symbol_le (d : ℕ) (s : ℝ) (i : Fin d) (k : Lattice d) :
    (2 * Real.pi * |(k i : ℝ)| * |rieszCoeff d s k|) ^ 2 ≤
      rieszConst d s ^ 2 * (1 + (2 : ℝ) ^ (-(s - (d : ℝ) + 1))) *
        sobWeight (s - (d : ℝ) + 1) k := by
  by_cases hk : k = 0
  · subst hk
    simp [rieszCoeff]
    unfold sobWeight
    positivity
  · set r : ℝ := 2 * Real.pi * Lattice.enorm k with hr
    have hr1 : 1 ≤ r := by
      have := one_le_enorm k hk
      nlinarith [Real.pi_gt_three]
    have hr0 : 0 < r := by linarith
    have hg : rieszCoeff d s k = rieszConst d s * r ^ (s - (d : ℝ)) := by
      simp [rieszCoeff, hk, hr]
    have hki : 2 * Real.pi * |(k i : ℝ)| ≤ r := by
      have := abs_two_pi_le k i
      rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at this
    set θ : ℝ := s - (d : ℝ) + 1 with hθ
    have hu : 0 < r ^ 2 := by positivity
    have hsw : sobWeight θ k = (1 + r ^ 2) ^ θ := by
      unfold sobWeight; rw [hr]; ring_nf
    have hlhs : (2 * Real.pi * |(k i : ℝ)| * |rieszCoeff d s k|) ^ 2 ≤
        rieszConst d s ^ 2 * (r ^ 2) ^ θ := by
      have h1 : 2 * Real.pi * |(k i : ℝ)| * |rieszCoeff d s k| ≤ r * (|rieszConst d s| * r ^ (s - (d : ℝ))) := by
        rw [hg, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr0.le _)]
        exact mul_le_mul_of_nonneg_right hki (by positivity)
      calc (2 * Real.pi * |(k i : ℝ)| * |rieszCoeff d s k|) ^ 2
          ≤ (r * (|rieszConst d s| * r ^ (s - (d : ℝ)))) ^ 2 := by gcongr
        _ = rieszConst d s ^ 2 * ((r ^ (s - (d : ℝ))) ^ 2 * r ^ 2) := by
            simp only [mul_pow, sq_abs]; ring
        _ = rieszConst d s ^ 2 * (r ^ 2) ^ θ := by
            rw [Real.rpow_pow_comm hr0.le, hθ, Real.rpow_add_one hu.ne']
    have hmain : (r ^ 2) ^ θ ≤ (1 + (2 : ℝ) ^ (-θ)) * (1 + r ^ 2) ^ θ := by
      have hp : 0 ≤ (1 + r ^ 2) ^ θ := by positivity
      have h2p : 0 ≤ (2 : ℝ) ^ (-θ) := by positivity
      rcases le_or_gt 0 θ with h | h
      · calc (r ^ 2) ^ θ ≤ (1 + r ^ 2) ^ θ :=
              Real.rpow_le_rpow hu.le (by linarith) h
          _ ≤ _ := by nlinarith
      · have h3 : (2 * r ^ 2) ^ θ ≤ (1 + r ^ 2) ^ θ :=
          Real.rpow_le_rpow_of_nonpos (by linarith) (by nlinarith) h.le
        have h4 : (2 * r ^ 2) ^ θ = 2 ^ θ * (r ^ 2) ^ θ := Real.mul_rpow (by norm_num) hu.le
        have h5 : (2 : ℝ) ^ θ * (2 : ℝ) ^ (-θ) = 1 := by
          rw [← Real.rpow_add (by norm_num)]; simp
        calc (r ^ 2) ^ θ = (2 : ℝ) ^ (-θ) * (2 ^ θ * (r ^ 2) ^ θ) := by
              rw [← mul_assoc, mul_comm ((2 : ℝ) ^ (-θ)), h5, one_mul]
          _ ≤ (2 : ℝ) ^ (-θ) * (1 + r ^ 2) ^ θ := by rw [← h4]; gcongr
          _ ≤ _ := by nlinarith
    rw [hsw]
    calc _ ≤ rieszConst d s ^ 2 * (r ^ 2) ^ θ := hlhs
      _ ≤ rieszConst d s ^ 2 * ((1 + (2 : ℝ) ^ (-θ)) * (1 + r ^ 2) ^ θ) := by gcongr
      _ = _ := by ring


theorem sub_forceLow (d : ℕ) (s : ℝ) (i : Fin d) (n : ℕ) (c : Coeff d) (k : Lattice d) :
    gradRieszCoeff d s i c k - forceLow d s i n c k =
      (1 - ((LevyAux.chiF d (LevyAux.eps n • Lattice.toEuc k) : ℝ) : ℂ)) * gradRieszCoeff d s i c k := by
  unfold forceLow; ring

theorem norm_gradRieszCoeff (d : ℕ) (s : ℝ) (i : Fin d) (c : Coeff d) (k : Lattice d) :
    ‖gradRieszCoeff d s i c k‖ = 2 * Real.pi * |(k i : ℝ)| * |rieszCoeff d s k| * ‖c k‖ := by
  simp only [gradRieszCoeff, derivCoeff, rieszMult, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, Complex.norm_ofNat, Complex.norm_intCast]
  rw [abs_of_pos Real.pi_pos]
  simp
  ring

set_option linter.unusedVariables false in
theorem forceHigh_l2_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (c : Coeff d) (k : Lattice d),
      ‖gradRieszCoeff d s i c k - forceLow d s i n c k‖ ^ 2 ≤
        C * (if (2 : ℝ) ^ n ≤ Lattice.enorm k then sobWeight (s - d + 1) k * ‖c k‖ ^ 2 else 0) := by
  refine ⟨rieszConst d s ^ 2 * (1 + (2 : ℝ) ^ (-(s - (d : ℝ) + 1))), by positivity, fun n c k => ?_⟩
  rw [sub_forceLow]
  by_cases h : (2 : ℝ) ^ n ≤ Lattice.enorm k
  · simp only [h, ↓reduceIte]
    have hχ0 := chiF_nonneg d (LevyAux.eps n • Lattice.toEuc k)
    have hχ1 := chiF_le_one d (LevyAux.eps n • Lattice.toEuc k)
    have h1 : ‖(1 - ((LevyAux.chiF d (LevyAux.eps n • Lattice.toEuc k) : ℝ) : ℂ))‖ ≤ 1 := by
      have : (1 - ((LevyAux.chiF d (LevyAux.eps n • Lattice.toEuc k) : ℝ) : ℂ)) =
          ((1 - LevyAux.chiF d (LevyAux.eps n • Lattice.toEuc k) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have h2 : ‖(1 - ((LevyAux.chiF d (LevyAux.eps n • Lattice.toEuc k) : ℝ) : ℂ)) *
        gradRieszCoeff d s i c k‖ ≤ ‖gradRieszCoeff d s i c k‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) h1
    calc ‖(1 - ((LevyAux.chiF d (LevyAux.eps n • Lattice.toEuc k) : ℝ) : ℂ)) *
          gradRieszCoeff d s i c k‖ ^ 2 ≤ ‖gradRieszCoeff d s i c k‖ ^ 2 := by gcongr
      _ = (2 * Real.pi * |(k i : ℝ)| * |rieszCoeff d s k|) ^ 2 * ‖c k‖ ^ 2 := by
          rw [norm_gradRieszCoeff]; ring
      _ ≤ (rieszConst d s ^ 2 * (1 + (2 : ℝ) ^ (-(s - (d : ℝ) + 1))) *
            sobWeight (s - (d : ℝ) + 1) k) * ‖c k‖ ^ 2 := by
          gcongr
          exact sq_symbol_le d s i k
      _ = _ := by ring
  · simp only [h, ↓reduceIte, mul_zero]
    have hlt : Lattice.enorm k < (2 : ℝ) ^ n := not_le.1 h
    have hχ : LevyAux.chiF d (LevyAux.eps n • Lattice.toEuc k) = 1 := by
      apply LevyAux.chiF_one
      rw [norm_smul, Real.norm_of_nonneg (LevyAux.eps_pos n).le]
      unfold LevyAux.eps
      have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      rw [inv_mul_le_iff₀ hp]
      have : ‖Lattice.toEuc k‖ = Lattice.enorm k := rfl
      linarith
    rw [hχ]
    simp

end HRS.PDE.MFApriori
