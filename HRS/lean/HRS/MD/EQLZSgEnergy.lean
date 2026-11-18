import HRS.MD.EQLZSgSmooth
import HRS.MD.EQLZSgSemigroup
import HRS.MD.EQLZSgInvariant
import HRS.MD.EQLZSgSymm
import HRS.PDE.TorusFPExistAux10

/-!
# EQ-LZ packet SG-5: Dirichlet-form bounds for `P_t` (`eqlz_sg_energy`), proof

Notation `⟨a,b⟩ = ∫ a b dπ`, `D(s) = ⟨φ, φ - P_sφ⟩`.

* Doubling: `D(2x) ≤ 2 D(x)` (semigroup law and symmetry give `⟨φ,P_{2x}φ⟩ = ‖P_xφ‖²`; the claim is `‖P_xφ - φ‖² ≥ 0`).
  Iterating, `D(t) ≤ 2^k D(t/2^k)`.
* `D(h)/h → κ∫|∇φ|² dπ` as `h → 0⁺` (uniform difference quotients `d1_P_diff_quot`, Green's identity `d3a_green_P`).
* `‖φ - P_tφ‖² ≤ D(t)`: with `a = P_{t/2}φ`, `⟨φ,P_tφ⟩ = ‖a‖²` and `‖P_{t/2}a‖² ≤ ‖a‖²` (`L²(π)`-contraction by
  Jensen: `(P ψ)² ≤ P(ψ²)` from positivity, linearity, `P 1 = 1`, and invariance of `π`).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS

namespace HRS.MD.EQLZSgEnergy

variable {n : ℕ}

section Aux

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)

theorem eqlzsg_smooth_mul {ψ₁ ψ₂ : Torus n → ℝ} (h₁ : Torus.IsSmooth ψ₁) (h₂ : Torus.IsSmooth ψ₂) :
    Torus.IsSmooth (fun x => ψ₁ x * ψ₂ x) := by
  have e1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ψ₁) := h₁
  have e2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ψ₂) := h₂
  exact e1.mul e2

/-- Pointwise Jensen: `(P_t ψ)² ≤ P_t (ψ²)`. -/
theorem eqlzsg_jensen {t : ℝ} (ht : 0 ≤ t) {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ) (x : Torus n) :
    (d1_P hn hκ hU t ψ x) ^ 2 ≤ d1_P hn hκ hU t (fun y => ψ y * ψ y) x := by
  set lam := d1_P hn hκ hU t ψ x with hlam
  have hu : Torus.IsSmooth (fun y => ψ y * ψ y) := eqlzsg_smooth_mul hψ hψ
  have h1 : Torus.IsSmooth (fun _ : Torus n => (1 : ℝ)) := d1_isSmooth_const 1
  have hv : Torus.IsSmooth (fun y => (-2 * lam) * ψ y + (lam ^ 2) * (fun _ : Torus n => (1 : ℝ)) y) :=
    d1_isSmooth_comb _ _ hψ h1
  have hw : Torus.IsSmooth (fun y => (1 : ℝ) * (ψ y * ψ y) + (1 : ℝ) *
      ((-2 * lam) * ψ y + (lam ^ 2) * (fun _ : Torus n => (1 : ℝ)) y)) :=
    d1_isSmooth_comb _ _ hu hv
  have hnn := d1_P_nonneg hn hκ hU ht hw (fun y => by
    simp only [mul_one, one_mul]
    nlinarith [sq_nonneg (ψ y - lam)]) x
  rw [d1_P_lincomb hn hκ hU ht hu hv 1 1 x, d1_P_lincomb hn hκ hU ht hψ h1 (-2 * lam) (lam ^ 2) x] at hnn
  have hc : d1_P hn hκ hU t (fun _ : Torus n => (1 : ℝ)) x = 1 := d1_P_const hn hκ hU ht 1 x
  rw [hc, ← hlam] at hnn
  nlinarith [hnn]

include hU in
/-- Continuous functions on the torus are integrable for the Gibbs probability measure. -/
theorem eqlzsg_hint {g : Torus n → ℝ} (hg : Continuous g) : Integrable g (d1_gibbsMeasure κ U) := by
  haveI := d3a_gibbs_isProb (κ := κ) hU
  exact hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem eqlzsg_cont {t : ℝ} (ht : 0 ≤ t) {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ) :
    Continuous (d1_P hn hκ hU t ψ) := d1_P_continuous hn hκ hU ht hψ

/-- `L²(π)`-contraction on smooth data. -/
theorem eqlzsg_contr {t : ℝ} (ht : 0 ≤ t) {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ) :
    ∫ x, d1_P hn hκ hU t ψ x * d1_P hn hκ hU t ψ x ∂(d1_gibbsMeasure κ U) ≤
      ∫ x, ψ x * ψ x ∂(d1_gibbsMeasure κ U) := by
  have hu : Torus.IsSmooth (fun y => ψ y * ψ y) := eqlzsg_smooth_mul hψ hψ
  have hPc := eqlzsg_cont hn hκ hU ht hψ
  have hPuc := eqlzsg_cont hn hκ hU ht hu
  have hψc := StaticLimitAux.continuous_of_smooth hψ
  calc ∫ x, d1_P hn hκ hU t ψ x * d1_P hn hκ hU t ψ x ∂(d1_gibbsMeasure κ U)
      ≤ ∫ x, d1_P hn hκ hU t (fun y => ψ y * ψ y) x ∂(d1_gibbsMeasure κ U) := by
        refine integral_mono (eqlzsg_hint hU (hPc.mul hPc)) (eqlzsg_hint hU hPuc) fun x => ?_
        have := eqlzsg_jensen hn hκ hU ht hψ x
        nlinarith [this]
    _ = ∫ x, ψ x * ψ x ∂(d1_gibbsMeasure κ U) :=
        HRS.MD.EQLZSgInvariant.eqlz_sg_invariant_proof hn hκ hU ht hu

include hU in
theorem eqlzsg_E1 {a b : Torus n → ℝ} (ha : Continuous a) (hb : Continuous b) :
    ∫ x, a x * (a x - b x) ∂(d1_gibbsMeasure κ U) =
      ∫ x, a x * a x ∂(d1_gibbsMeasure κ U) - ∫ x, a x * b x ∂(d1_gibbsMeasure κ U) := by
  simp_rw [mul_sub]
  exact integral_sub (eqlzsg_hint hU (ha.mul ha)) (eqlzsg_hint hU (ha.mul hb))

include hU in
theorem eqlzsg_E2 {a b : Torus n → ℝ} (ha : Continuous a) (hb : Continuous b) :
    ∫ x, (a x - b x) * (a x - b x) ∂(d1_gibbsMeasure κ U) =
      ∫ x, a x * a x ∂(d1_gibbsMeasure κ U) - 2 * ∫ x, a x * b x ∂(d1_gibbsMeasure κ U) +
        ∫ x, b x * b x ∂(d1_gibbsMeasure κ U) := by
  have i1 : Integrable (fun x => a x * a x) (d1_gibbsMeasure κ U) := eqlzsg_hint hU (ha.mul ha)
  have i2 : Integrable (fun x => a x * b x) (d1_gibbsMeasure κ U) := eqlzsg_hint hU (ha.mul hb)
  have i3 : Integrable (fun x => b x * b x) (d1_gibbsMeasure κ U) := eqlzsg_hint hU (hb.mul hb)
  have : (fun x => (a x - b x) * (a x - b x)) =
      fun x => (a x * a x - 2 * (a x * b x)) + b x * b x := funext fun x => by ring
  have i2' : Integrable (fun x => 2 * (a x * b x)) (d1_gibbsMeasure κ U) := i2.const_mul 2
  have i12 : Integrable (fun x => a x * a x - 2 * (a x * b x)) (d1_gibbsMeasure κ U) := i1.sub i2'
  rw [this, integral_add i12 i3, integral_sub i1 i2', integral_const_mul]

/-- Doubling: `D(2x) ≤ 2 D(x)`. -/
theorem eqlzsg_double {x : ℝ} (hx : 0 ≤ x) {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) :
    ∫ y, φ y * (φ y - d1_P hn hκ hU (2 * x) φ y) ∂(d1_gibbsMeasure κ U) ≤
      2 * ∫ y, φ y * (φ y - d1_P hn hκ hU x φ y) ∂(d1_gibbsMeasure κ U) := by
  have hφc := StaticLimitAux.continuous_of_smooth hφ
  have hcs : Torus.IsSmooth (d1_P hn hκ hU x φ) := HRS.MD.EQLZSgSmooth.eqlz_sg_smooth_proof hn hκ hU hx hφ
  have hcc := eqlzsg_cont hn hκ hU hx hφ
  have hsem : d1_P hn hκ hU (2 * x) φ = d1_P hn hκ hU x (d1_P hn hκ hU x φ) := by
    rw [two_mul]
    exact HRS.MD.EQLZSgSemigroup.eqlz_sg_semigroup_proof hn hκ hU hx hx hφ
  have hsymm := HRS.MD.EQLZSgSymm.eqlz_sg_symm_proof hn hκ hU hx hφ hcs
  rw [hsem, eqlzsg_E1 hU hφc (eqlzsg_cont hn hκ hU hx hcs), eqlzsg_E1 hU hφc hcc]
  have hnn : 0 ≤ ∫ y, (d1_P hn hκ hU x φ y - φ y) * (d1_P hn hκ hU x φ y - φ y)
      ∂(d1_gibbsMeasure κ U) := integral_nonneg fun y => mul_self_nonneg _
  rw [eqlzsg_E2 hU hcc hφc] at hnn
  have hcomm : ∫ y, d1_P hn hκ hU x φ y * φ y ∂(d1_gibbsMeasure κ U) =
      ∫ y, φ y * d1_P hn hκ hU x φ y ∂(d1_gibbsMeasure κ U) :=
    integral_congr_ae (ae_of_all _ fun y => mul_comm _ _)
  linarith

/-- Second inequality: `‖φ - P_tφ‖² ≤ ⟨φ, φ - P_tφ⟩`. -/
theorem eqlzsg_second {t : ℝ} (ht : 0 ≤ t) {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) :
    ∫ y, (φ y - d1_P hn hκ hU t φ y) ^ 2 ∂(d1_gibbsMeasure κ U) ≤
      ∫ y, φ y * (φ y - d1_P hn hκ hU t φ y) ∂(d1_gibbsMeasure κ U) := by
  have hφc := StaticLimitAux.continuous_of_smooth hφ
  have ht2 : 0 ≤ t / 2 := by positivity
  have has : Torus.IsSmooth (d1_P hn hκ hU (t / 2) φ) :=
    HRS.MD.EQLZSgSmooth.eqlz_sg_smooth_proof hn hκ hU ht2 hφ
  have hac := eqlzsg_cont hn hκ hU ht2 hφ
  have hKeq : d1_P hn hκ hU t φ = d1_P hn hκ hU (t / 2) (d1_P hn hκ hU (t / 2) φ) := by
    have := HRS.MD.EQLZSgSemigroup.eqlz_sg_semigroup_proof hn hκ hU ht2 ht2 hφ
    rwa [add_halves] at this
  have hKc : Continuous (d1_P hn hκ hU t φ) := eqlzsg_cont hn hκ hU ht hφ
  have hsymm := HRS.MD.EQLZSgSymm.eqlz_sg_symm_proof hn hκ hU ht2 hφ has
  have hcontr := eqlzsg_contr hn hκ hU ht2 has
  rw [← hKeq] at hcontr
  have hBeq : ∫ y, φ y * d1_P hn hκ hU t φ y ∂(d1_gibbsMeasure κ U) =
      ∫ y, d1_P hn hκ hU (t / 2) φ y * d1_P hn hκ hU (t / 2) φ y ∂(d1_gibbsMeasure κ U) := by
    rw [hKeq]; exact hsymm.symm
  have e2 := eqlzsg_E2 (κ := κ) hU hφc hKc
  have e1 := eqlzsg_E1 (κ := κ) hU hφc hKc
  simp_rw [sq]
  rw [e2, e1]
  linarith

/-- Iterated doubling: `D(t) ≤ 2^k D(t/2^k)`. -/
theorem eqlzsg_iter {t : ℝ} (ht : 0 ≤ t) {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) (k : ℕ) :
    ∫ y, φ y * (φ y - d1_P hn hκ hU t φ y) ∂(d1_gibbsMeasure κ U) ≤
      2 ^ k * ∫ y, φ y * (φ y - d1_P hn hκ hU (t / 2 ^ k) φ y) ∂(d1_gibbsMeasure κ U) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hx : 0 ≤ t / 2 ^ (k + 1) := by positivity
    have h2 := eqlzsg_double hn hκ hU hx hφ
    have e : 2 * (t / 2 ^ (k + 1)) = t / 2 ^ k := by
      rw [pow_succ]; field_simp
    rw [e] at h2
    calc _ ≤ _ := ih
      _ ≤ 2 ^ k * (2 * ∫ y, φ y * (φ y - d1_P hn hκ hU (t / 2 ^ (k + 1)) φ y)
            ∂(d1_gibbsMeasure κ U)) := by gcongr
      _ = _ := by rw [pow_succ]; ring

/-- First inequality: `⟨φ, φ - P_tφ⟩ ≤ t κ ∫|∇φ|² dπ`. -/
theorem eqlzsg_first {t : ℝ} (ht : 0 ≤ t) {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) :
    ∫ y, φ y * (φ y - d1_P hn hκ hU t φ y) ∂(d1_gibbsMeasure κ U) ≤
      t * (κ * ∫ x, ‖Torus.grad φ x‖ ^ 2 ∂(d1_gibbsMeasure κ U)) := by
  haveI := d3a_gibbs_isProb (κ := κ) hU
  have hφc := StaticLimitAux.continuous_of_smooth hφ
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    rw [HRS.MD.EQLZSgSemigroup.eqlzsg_P_zero hn hκ hU]
    simp
  set π := d1_gibbsMeasure κ U with hπ
  set L := d1_gen κ (d1_gradDrift U) with hL
  -- the Dirichlet form
  have hφ2 : Torus.IsCk 2 φ := ContDiff.of_le
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ) (WithTop.coe_le_coe.2 le_top)
  have hgreen := d3a_green_P hκ hU hφ2 hφ2
  have hE : ∫ y, φ y * (-(L φ y)) ∂π = κ * ∫ x, ‖Torus.grad φ x‖ ^ 2 ∂π := by
    have h1 : ∫ y, φ y * (-(L φ y)) ∂π = -∫ y, L φ y * φ y ∂π := by
      rw [← integral_neg]
      exact integral_congr_ae (ae_of_all _ fun y => by ring)
    rw [h1, hgreen]
    simp_rw [real_inner_self_eq_norm_sq]
    ring
  have hLc : Continuous (L φ) := d1_gen_continuous (d1_gradDrift_continuous hU) hφ2
  obtain ⟨Cφ, hCφ⟩ := (isCompact_univ (X := Torus n)).exists_bound_of_continuousOn hφc.continuousOn
  set C0 := max Cφ 0 with hC0
  have hC0nn : 0 ≤ C0 := le_max_right _ _
  have hφC : ∀ y, |φ y| ≤ C0 := fun y => by
    have := hCφ y (Set.mem_univ y)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hden : 0 < t * (C0 + 1) := by positivity
  set ε := η / (t * (C0 + 1)) with hε
  have hεpos : 0 < ε := div_pos hη hden
  obtain ⟨δ, hδ, hquot⟩ := d1_P_diff_quot hn hκ hU hφ hεpos
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (t / δ) (one_lt_two : (1 : ℝ) < 2)
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  set h := t / 2 ^ k with hh
  have hhpos : 0 < h := div_pos hpos h2k
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ h2k]
    rw [div_lt_iff₀ hδ] at hk
    linarith
  have hiter := eqlzsg_iter hn hκ hU ht hφ k
  -- bound on D(h)
  have hDh : ∫ y, φ y * (φ y - d1_P hn hκ hU h φ y) ∂π ≤ h * (κ * ∫ x, ‖Torus.grad φ x‖ ^ 2 ∂π + C0 * ε) := by
    have hpt : ∀ y, φ y * (φ y - d1_P hn hκ hU h φ y) ≤ h * (φ y * (-(L φ y)) + C0 * ε) := by
      intro y
      have hq := hquot h hhpos hhδ y
      set e := (d1_P hn hκ hU h φ y - φ y) / h - L φ y with he
      have hexp : φ y * (φ y - d1_P hn hκ hU h φ y) = h * (φ y * (-(L φ y)) + φ y * (-e)) := by
        rw [he]; field_simp; ring
      rw [hexp]
      refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hhpos.le
      calc φ y * (-e) ≤ |φ y * (-e)| := le_abs_self _
        _ = |φ y| * |e| := by rw [abs_mul, abs_neg]
        _ ≤ C0 * ε := mul_le_mul (hφC y) hq (abs_nonneg _) hC0nn
    have hLint : Continuous fun y => h * (φ y * (-(L φ y)) + C0 * ε) :=
      continuous_const.mul ((hφc.mul hLc.neg).add continuous_const)
    calc ∫ y, φ y * (φ y - d1_P hn hκ hU h φ y) ∂π
        ≤ ∫ y, h * (φ y * (-(L φ y)) + C0 * ε) ∂π := by
          refine integral_mono (eqlzsg_hint hU (hφc.mul (hφc.sub (eqlzsg_cont hn hκ hU hhpos.le hφ))))
            (eqlzsg_hint hU hLint) hpt
      _ = h * (κ * ∫ x, ‖Torus.grad φ x‖ ^ 2 ∂π + C0 * ε) := by
          rw [integral_const_mul]
          congr 1
          have i1 : Integrable (fun y => φ y * (-(L φ y))) π := eqlzsg_hint hU (hφc.mul hLc.neg)
          rw [integral_add i1 (integrable_const _), hE]
          simp
  have h2kh : (2 : ℝ) ^ k * h = t := by rw [hh]; field_simp
  calc ∫ y, φ y * (φ y - d1_P hn hκ hU t φ y) ∂π
      ≤ 2 ^ k * ∫ y, φ y * (φ y - d1_P hn hκ hU h φ y) ∂π := hiter
    _ ≤ 2 ^ k * (h * (κ * ∫ x, ‖Torus.grad φ x‖ ^ 2 ∂π + C0 * ε)) :=
        mul_le_mul_of_nonneg_left hDh h2k.le
    _ = t * (κ * ∫ x, ‖Torus.grad φ x‖ ^ 2 ∂π) + t * (C0 * ε) := by
        rw [← mul_assoc, h2kh]; ring
    _ ≤ t * (κ * ∫ x, ‖Torus.grad φ x‖ ^ 2 ∂π) + η := by
        have : t * (C0 * ε) ≤ η := by
          rw [hε]
          have : t * (C0 * (η / (t * (C0 + 1)))) = η * (C0 / (C0 + 1)) := by
            field_simp
          rw [this]
          have hfrac : C0 / (C0 + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          nlinarith
        linarith

end Aux

/-- (SG-5, `eqlz_sg_energy`.)  Statement copied verbatim from `HRS.MD.EQLZ.eqlz_sg_energy`. -/
theorem eqlz_sg_energy_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {t : ℝ}
    (ht : 0 ≤ t) {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) :
    ∫ x, φ x * (φ x - d1_P hn hκ hU t φ x) ∂(d1_gibbsMeasure κ U) ≤
        t * (κ * ∫ x, ‖Torus.grad φ x‖ ^ 2 ∂(d1_gibbsMeasure κ U)) ∧
      ∫ x, (φ x - d1_P hn hκ hU t φ x) ^ 2 ∂(d1_gibbsMeasure κ U) ≤
        ∫ x, φ x * (φ x - d1_P hn hκ hU t φ x) ∂(d1_gibbsMeasure κ U) :=
  ⟨eqlzsg_first hn hκ hU ht hφ, eqlzsg_second hn hκ hU ht hφ⟩

end HRS.MD.EQLZSgEnergy

end
