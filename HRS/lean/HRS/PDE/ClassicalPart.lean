import HRS.PDE.Classical
import HRS.PDE.Galerkin
import HRS.PDE.GalerkinLimit
import HRS.PDE.Assembly
import HRS.PDE.Uniqueness

/-!
# Torus PDE layer: auxiliary `ℓ¹`-type analysis for the classical part of Proposition 3.9

Helper file for `adjoint_torus_joint_continuity`, `adjoint_torus_classical`,
`adjoint_torus_planewave_classical`, `propagator_semigroup` (`HRS/PDE/WellPosed.lean`).

* weighted `ℓ¹` norms `WN p c = ∑ ⟨k⟩^p |c(k)|` and the Cauchy–Schwarz bridge `H^m ⊂ WS p`;
* the convolution (Young) inequality for the coefficient product `mulCoeff`;
* continuity of `(ρ, c) ↦ forwardGen D ρ c` into `ℓ¹` for `ρ̂ ∈ WS 1`, `c ∈ WS 2`;
* `H^N` bounds of the coefficients of a `C^N` function (Parseval), continuity in time of the
  coefficients of the density path in `WS 1`.

Everything lives in the namespace `HRS.PDE.ClassicalPart`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.ClassicalPart

variable {d : ℕ}

/-! ### Weighted `ℓ¹` norms -/

/-- `∑ ⟨k⟩^p |c(k)| < ∞`. -/
def WS (p : ℕ) (c : Coeff d) : Prop := Summable fun k : Lattice d => Lattice.jp k ^ p * ‖c k‖

/-- `∑ ⟨k⟩^p |c(k)|`. -/
def WN (p : ℕ) (c : Coeff d) : ℝ := ∑' k : Lattice d, Lattice.jp k ^ p * ‖c k‖

lemma jp_pow_nonneg (p : ℕ) (k : Lattice d) : 0 ≤ Lattice.jp k ^ p :=
  pow_nonneg (Torus.jp_pos k).le p

lemma one_le_jp_pow (p : ℕ) (k : Lattice d) : 1 ≤ Lattice.jp k ^ p :=
  one_le_pow₀ (Torus.jp_ge_one k)

lemma WN_nonneg (p : ℕ) (c : Coeff d) : 0 ≤ WN p c :=
  tsum_nonneg fun k => mul_nonneg (jp_pow_nonneg p k) (norm_nonneg _)

lemma WS.mono {p q : ℕ} (h : q ≤ p) {c : Coeff d} (hc : WS p c) : WS q c := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (jp_pow_nonneg q k) (norm_nonneg _))
    (fun k => ?_) hc
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (Torus.jp_ge_one k) h) (norm_nonneg _)

lemma WN_mono {p q : ℕ} (h : q ≤ p) {c : Coeff d} (hc : WS p c) : WN q c ≤ WN p c :=
  Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (Torus.jp_ge_one k) h) (norm_nonneg _)) (hc.mono h) hc

lemma WS.add {p : ℕ} {a b : Coeff d} (ha : WS p a) (hb : WS p b) : WS p (a + b) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (jp_pow_nonneg p k) (norm_nonneg _))
    (fun k => ?_) (Summable.add ha hb)
  simp only [Pi.add_apply]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (jp_pow_nonneg p k)

lemma WS.neg {p : ℕ} {a : Coeff d} (ha : WS p a) : WS p (-a) := by
  simpa [WS] using ha

lemma WS.sub {p : ℕ} {a b : Coeff d} (ha : WS p a) (hb : WS p b) : WS p (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

lemma WS.smul {p : ℕ} {a : Coeff d} (ha : WS p a) (z : ℂ) : WS p (z • a) := by
  unfold WS
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact (ha.mul_left ‖z‖).congr fun k => by ring

lemma WS.zero (p : ℕ) : WS p (0 : Coeff d) := by simp [WS]

lemma WN_add_le {p : ℕ} {a b : Coeff d} (ha : WS p a) (hb : WS p b) :
    WN p (a + b) ≤ WN p a + WN p b := by
  unfold WN
  rw [← Summable.tsum_add ha hb]
  refine Summable.tsum_le_tsum (fun k => ?_) (WS.add ha hb) (Summable.add ha hb)
  simp only [Pi.add_apply]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (jp_pow_nonneg p k)

lemma WN_sub_le {p : ℕ} {a b : Coeff d} (ha : WS p a) (hb : WS p b) :
    WN p (a - b) ≤ WN p a + WN p b := by
  have h : WS p (a - b) := ha.sub hb
  unfold WN
  rw [← Summable.tsum_add ha hb]
  refine Summable.tsum_le_tsum (fun k => ?_) h (Summable.add ha hb)
  simp only [Pi.sub_apply]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (jp_pow_nonneg p k)

lemma WN_smul {p : ℕ} (a : Coeff d) (z : ℂ) : WN p (z • a) = ‖z‖ * WN p a := by
  unfold WN
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

lemma norm_le_WN {c : Coeff d} (hc : WS 0 c) (k : Lattice d) : ‖c k‖ ≤ WN 0 c := by
  have := hc.le_tsum k (fun j _ => mul_nonneg (jp_pow_nonneg 0 j) (norm_nonneg _))
  simpa [WN] using this

/-! ### Cauchy–Schwarz: `H^m ⊂ WS p` for `m > d/2 + p` -/

lemma exists_ws_bound (p : ℕ) (m : ℝ) (hm : (d : ℝ) / 2 + p < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : Coeff d, MemHs m c → WS p c ∧ WN p c ≤ C * hsNorm m c := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hd : (d : ℝ) < 2 * (m - p) := by linarith
  set a : Lattice d → ℝ := fun k => Lattice.jp k ^ (-(m - p)) with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => Real.rpow_nonneg (Torus.jp_pos k).le _
  have ha2 : Summable fun k => a k ^ 2 := by
    rw [Torus.summable_lattice_iff]
    refine (summable_jp_rpow (d := d) (m - p) hd).congr fun k => ?_
    simp only [ha]; rw [Torus.jp_rpow_sq]; ring_nf
  refine ⟨Real.sqrt (∑' k, a k ^ 2), Real.sqrt_nonneg _, fun c hc => ?_⟩
  set b : Lattice d → ℝ := fun k => Lattice.jp k ^ m * ‖c k‖ with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k =>
    mul_nonneg (Real.rpow_nonneg (Torus.jp_pos k).le _) (norm_nonneg _)
  have hbsq : ∀ k, b k ^ 2 = sobWeight m k * ‖c k‖ ^ 2 := by
    intro k
    simp only [hb]; rw [mul_pow, Torus.jp_rpow_sq, sobWeight_eq_jp]
  have hb2 : Summable fun k => b k ^ 2 := hc.congr fun k => (hbsq k).symm
  have hcs := Torus.cs_tsum a b ha0 hb0 ha2 hb2
  have hab : ∀ k, a k * b k = Lattice.jp k ^ p * ‖c k‖ := by
    intro k
    simp only [ha, hb]
    rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k)]
    have : -(m - (p : ℝ)) + m = p := by ring
    rw [this, Real.rpow_natCast]
  have hS : WS p c := hcs.1.congr hab
  refine ⟨hS, ?_⟩
  have e : WN p c = ∑' k, a k * b k := by
    unfold WN; exact tsum_congr fun k => (hab k).symm
  rw [e]
  refine hcs.2.trans ?_
  have : Real.sqrt (∑' k, b k ^ 2) = hsNorm m c := by
    unfold hsNorm hsNormSq
    congr 1
    exact tsum_congr hbsq
  rw [this]

/-! ### Young's inequality for the coefficient product -/

/-- The shear `(k, j) ↦ (k - j, j)` of `ℤ^d × ℤ^d`. -/
def shearEquiv (d : ℕ) : Lattice d × Lattice d ≃ Lattice d × Lattice d where
  toFun x := (x.1 - x.2, x.2)
  invFun x := (x.1 + x.2, x.2)
  left_inv x := by simp
  right_inv x := by simp

lemma summable_conv_prod {α β : Lattice d → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hα : Summable α) (hβ : Summable β) :
    Summable (fun x : Lattice d × Lattice d => α (x.1 - x.2) * β x.2) ∧
      ∑' x : Lattice d × Lattice d, α (x.1 - x.2) * β x.2 = (∑' k, α k) * (∑' k, β k) := by
  have hG : Summable (fun x : Lattice d × Lattice d => α x.1 * β x.2) :=
    Summable.mul_of_nonneg hα hβ (fun k => hα0 k) (fun k => hβ0 k)
  have e : (fun x : Lattice d × Lattice d => α (x.1 - x.2) * β x.2) =
      (fun x : Lattice d × Lattice d => α x.1 * β x.2) ∘ (shearEquiv d) := rfl
  refine ⟨?_, ?_⟩
  · rw [e]; exact (Equiv.summable_iff (shearEquiv d)).2 hG
  · rw [e]
    have := Equiv.tsum_eq (shearEquiv d) (fun x : Lattice d × Lattice d => α x.1 * β x.2)
    refine this.trans ?_
    exact (tsum_mul_tsum_of_summable_norm (by simpa [Real.norm_eq_abs, abs_of_nonneg (hα0 _)] using hα)
      (by simpa [Real.norm_eq_abs, abs_of_nonneg (hβ0 _)] using hβ)).symm

/-- Admissible weights for the Young inequality: nonnegative and `w k ≤ w (k - j) + w j`. -/
structure SubWeight (w : Lattice d → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ w k
  sub : ∀ k j, w k ≤ w (k - j) + w j

lemma SubWeight.one : SubWeight (fun _ : Lattice d => (1 : ℝ)) :=
  ⟨fun _ => zero_le_one, fun _ _ => by norm_num⟩

lemma enorm_sub_le (k j : Lattice d) : Lattice.enorm k ≤ Lattice.enorm (k - j) + Lattice.enorm j := by
  unfold Lattice.enorm
  have : Lattice.toEuc k = Lattice.toEuc (k - j) + Lattice.toEuc j := by
    ext i; simp [Lattice.toEuc]
  rw [this]
  exact norm_add_le _ _

lemma jp_sub_le (k j : Lattice d) : Lattice.jp k ≤ Lattice.jp (k - j) + Lattice.jp j := by
  have h1 := Torus.jp_pos (k - j)
  have h2 := Torus.jp_pos j
  have hk : 0 ≤ Lattice.enorm k := norm_nonneg _
  have e1 := Torus.two_pi_enorm_le_jp (k - j)
  have e2 := Torus.two_pi_enorm_le_jp j
  have hq : ∀ x : Lattice d, Lattice.jp x ^ 2 = 1 + 4 * Real.pi ^ 2 * Lattice.enorm x ^ 2 := by
    intro x
    unfold Lattice.jp
    exact Real.sq_sqrt (by positivity)
  have htri := enorm_sub_le k j
  have hn1 : 0 ≤ Lattice.enorm (k - j) := norm_nonneg _
  have hn2 : 0 ≤ Lattice.enorm j := norm_nonneg _
  apply le_of_sq_le_sq _ (by linarith)
  rw [hq k, add_sq, hq (k - j), hq j]
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hs : Lattice.enorm k ^ 2 ≤ (Lattice.enorm (k - j) + Lattice.enorm j) ^ 2 :=
    pow_le_pow_left₀ hk htri 2
  have hprod : (2 * Real.pi * Lattice.enorm (k - j)) * (2 * Real.pi * Lattice.enorm j) ≤
      Lattice.jp (k - j) * Lattice.jp j :=
    mul_le_mul e1 e2 (by positivity) h1.le
  nlinarith [hs, hprod, sq_nonneg Real.pi]

lemma SubWeight.jp : SubWeight (fun k : Lattice d => Lattice.jp k) :=
  ⟨fun k => (Torus.jp_pos k).le, jp_sub_le⟩

/-- **Young's inequality** for the coefficient product, with a subadditive weight. -/
lemma conv_estimate {w : Lattice d → ℝ} (hw : SubWeight w) {a c : Coeff d}
    (ha0 : Summable fun k => ‖a k‖) (haw : Summable fun k => w k * ‖a k‖)
    (hc0 : Summable fun k => ‖c k‖) (hcw : Summable fun k => w k * ‖c k‖) :
    (∀ k, Summable fun j => ‖a (k - j)‖ * ‖c j‖) ∧
    Summable (fun k => w k * ‖mulCoeff a c k‖) ∧
    ∑' k, w k * ‖mulCoeff a c k‖ ≤
      (∑' k, w k * ‖a k‖) * (∑' k, ‖c k‖) + (∑' k, ‖a k‖) * (∑' k, w k * ‖c k‖) := by
  have hnn : ∀ k, 0 ≤ ‖a k‖ := fun k => norm_nonneg _
  have hnc : ∀ k, 0 ≤ ‖c k‖ := fun k => norm_nonneg _
  have P0 := summable_conv_prod hnn hnc ha0 hc0
  have P1 := summable_conv_prod (fun k => mul_nonneg (hw.nonneg k) (hnn k)) hnc haw hc0
  have P2 := summable_conv_prod hnn (fun k => mul_nonneg (hw.nonneg k) (hnc k)) ha0 hcw
  set H : Lattice d × Lattice d → ℝ := fun x => w x.1 * (‖a (x.1 - x.2)‖ * ‖c x.2‖) with hH
  have hHle : ∀ x, H x ≤ (w (x.1 - x.2) * ‖a (x.1 - x.2)‖) * ‖c x.2‖ +
      ‖a (x.1 - x.2)‖ * (w x.2 * ‖c x.2‖) := by
    intro x
    have := hw.sub x.1 x.2
    have h3 : 0 ≤ ‖a (x.1 - x.2)‖ * ‖c x.2‖ := mul_nonneg (hnn _) (hnc _)
    simp only [hH]
    nlinarith [mul_le_mul_of_nonneg_right this h3]
  have hH0 : ∀ x, 0 ≤ H x := fun x =>
    mul_nonneg (hw.nonneg _) (mul_nonneg (hnn _) (hnc _))
  have hHs : Summable H := Summable.of_nonneg_of_le hH0 hHle (P1.1.add P2.1)
  have hHt : ∑' x, H x ≤ (∑' k, w k * ‖a k‖) * (∑' k, ‖c k‖) +
      (∑' k, ‖a k‖) * (∑' k, w k * ‖c k‖) := by
    calc ∑' x, H x ≤ ∑' x : Lattice d × Lattice d, ((w (x.1 - x.2) * ‖a (x.1 - x.2)‖) * ‖c x.2‖ +
          ‖a (x.1 - x.2)‖ * (w x.2 * ‖c x.2‖)) :=
          Summable.tsum_le_tsum hHle hHs (P1.1.add P2.1)
      _ = _ := by rw [Summable.tsum_add P1.1 P2.1, P1.2, P2.2]
  have hbound : ∀ k, w k * ‖mulCoeff a c k‖ ≤ ∑' j, H (k, j) := by
    intro k
    have hin : Summable fun j => ‖a (k - j)‖ * ‖c j‖ := P0.1.prod_factor k
    have h1 : ‖mulCoeff a c k‖ ≤ ∑' j, ‖a (k - j)‖ * ‖c j‖ := by
      unfold mulCoeff
      refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
      · exact hin.congr fun j => (norm_mul _ _).symm
      · exact tsum_congr fun j => norm_mul _ _
    calc w k * ‖mulCoeff a c k‖ ≤ w k * ∑' j, ‖a (k - j)‖ * ‖c j‖ :=
          mul_le_mul_of_nonneg_left h1 (hw.nonneg k)
      _ = ∑' j, H (k, j) := by rw [← tsum_mul_left]
  have hSk : Summable fun k => ∑' j, H (k, j) := hHs.prod
  refine ⟨fun k => P0.1.prod_factor k, ?_, ?_⟩
  · exact Summable.of_nonneg_of_le (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _)) hbound hSk
  · refine (Summable.tsum_le_tsum hbound (Summable.of_nonneg_of_le
      (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _)) hbound hSk) hSk).trans ?_
    rw [← hHs.tsum_prod]
    exact hHt

/-! ### Wrappers for the two weights -/

lemma WS_zero_iff (c : Coeff d) : WS 0 c ↔ Summable fun k => ‖c k‖ := by
  simp [WS]

lemma WN_zero (c : Coeff d) : WN 0 c = ∑' k, ‖c k‖ := by
  simp [WN]

lemma WS_one_iff (c : Coeff d) : WS 1 c ↔ Summable fun k => Lattice.jp k * ‖c k‖ := by
  simp [WS]

lemma WN_one (c : Coeff d) : WN 1 c = ∑' k, Lattice.jp k * ‖c k‖ := by
  simp [WN]

lemma conv0 {a c : Coeff d} (ha : WS 0 a) (hc : WS 0 c) :
    WS 0 (mulCoeff a c) ∧ WN 0 (mulCoeff a c) ≤ 2 * (WN 0 a * WN 0 c) := by
  rw [WS_zero_iff] at ha hc
  have h := conv_estimate (SubWeight.one (d := d)) (a := a) (c := c) ha (by simpa using ha)
    hc (by simpa using hc)
  refine ⟨(WS_zero_iff _).2 (by simpa using h.2.1), ?_⟩
  rw [WN_zero, WN_zero, WN_zero]
  have := h.2.2
  simp only [one_mul] at this
  linarith

lemma conv1 {a c : Coeff d} (ha : WS 1 a) (hc : WS 1 c) :
    WS 1 (mulCoeff a c) ∧
      WN 1 (mulCoeff a c) ≤ WN 1 a * WN 0 c + WN 0 a * WN 1 c := by
  have ha0 : WS 0 a := ha.mono (Nat.zero_le _)
  have hc0 : WS 0 c := hc.mono (Nat.zero_le _)
  rw [WS_zero_iff] at ha0 hc0
  rw [WS_one_iff] at ha hc
  have h := conv_estimate (SubWeight.jp (d := d)) (a := a) (c := c) ha0 ha hc0 hc
  refine ⟨(WS_one_iff _).2 h.2.1, ?_⟩
  rw [WN_one, WN_one, WN_one, WN_zero, WN_zero]
  exact h.2.2

lemma summable_mulTerm {a c : Coeff d} (ha : WS 0 a) (hc : WS 0 c) (k : Lattice d) :
    Summable fun j => a (k - j) * c j := by
  rw [WS_zero_iff] at ha hc
  have h := (conv_estimate (SubWeight.one (d := d)) (a := a) (c := c) ha (by simpa using ha)
    hc (by simpa using hc)).1 k
  exact Summable.of_norm (h.congr fun j => (norm_mul _ _).symm)

lemma mulCoeff_sub_left {a a' c : Coeff d} (ha : WS 0 a) (ha' : WS 0 a') (hc : WS 0 c) :
    mulCoeff (a - a') c = mulCoeff a c - mulCoeff a' c := by
  funext k
  simp only [mulCoeff, Pi.sub_apply, sub_mul]
  exact Summable.tsum_sub (summable_mulTerm ha hc k) (summable_mulTerm ha' hc k)

lemma mulCoeff_sub_right {a c c' : Coeff d} (ha : WS 0 a) (hc : WS 0 c) (hc' : WS 0 c') :
    mulCoeff a (c - c') = mulCoeff a c - mulCoeff a c' := by
  funext k
  simp only [mulCoeff, Pi.sub_apply, mul_sub]
  exact Summable.tsum_sub (summable_mulTerm ha hc k) (summable_mulTerm ha hc' k)

lemma mulCoeff_diff {a a' c c' : Coeff d} (ha : WS 0 a) (ha' : WS 0 a') (hc : WS 0 c)
    (hc' : WS 0 c') :
    mulCoeff a c - mulCoeff a' c' = mulCoeff (a - a') c + mulCoeff a' (c - c') := by
  rw [mulCoeff_sub_left ha ha' hc, mulCoeff_sub_right ha' hc hc']
  abel

lemma mulCoeff_zero_right (a : Coeff d) : mulCoeff a 0 = 0 := by
  funext k; simp [mulCoeff]

/-! ### Differential operators on `WS` -/

lemma derivCoeff_sub (j : Fin d) (x y : Coeff d) :
    derivCoeff j (x - y) = derivCoeff j x - derivCoeff j y := by
  funext k; simp [derivCoeff, mul_sub]

lemma gradRieszCoeff_sub (s : ℝ) (i : Fin d) (x y : Coeff d) :
    gradRieszCoeff d s i (x - y) = gradRieszCoeff d s i x - gradRieszCoeff d s i y := by
  funext k; simp [gradRieszCoeff, rieszMult, derivCoeff, mul_sub]

lemma laplaceCoeff_sub (x y : Coeff d) :
    laplaceCoeff (x - y) = laplaceCoeff x - laplaceCoeff y := by
  funext k; simp [laplaceCoeff, mul_sub]

lemma norm_derivCoeff_le (j : Fin d) (c : Coeff d) (k : Lattice d) :
    ‖derivCoeff j c k‖ ≤ Lattice.jp k * ‖c k‖ := by
  rw [norm_derivCoeff]
  exact mul_le_mul_of_nonneg_right (two_pi_abs_coord_le_jp k j) (norm_nonneg _)

lemma norm_laplaceCoeff_le (c : Coeff d) (k : Lattice d) :
    ‖laplaceCoeff c k‖ ≤ Lattice.jp k ^ 2 * ‖c k‖ := by
  show ‖(-((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ)) * c k‖ ≤ _
  rw [norm_mul, norm_neg, Complex.norm_real]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h4 : ‖(4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ)‖ = 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 :=
    by rw [Real.norm_eq_abs]; exact abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
  rw [h4]
  have := Torus.two_pi_enorm_le_jp k
  have h0 : 0 ≤ 2 * Real.pi * Lattice.enorm k :=
    mul_nonneg (by positivity) (norm_nonneg _)
  nlinarith

lemma norm_gradRieszCoeff_le (s : ℝ) (hsd : s ≤ d) (i : Fin d) (c : Coeff d) (k : Lattice d) :
    ‖gradRieszCoeff d s i c k‖ ≤ |rieszConst d s| * (Lattice.jp k * ‖c k‖) := by
  rw [norm_gradRieszCoeff]
  have := abs_rieszCoeff_mul_le s hsd k i
  calc 2 * Real.pi * |((k i : ℤ) : ℝ)| * (|rieszCoeff d s k| * ‖c k‖)
      = (|rieszCoeff d s k| * (2 * Real.pi * |((k i : ℤ) : ℝ)|)) * ‖c k‖ := by ring
    _ ≤ (|rieszConst d s| * Lattice.jp k) * ‖c k‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = _ := by ring

lemma WS_of_le {p q : ℕ} {c : Coeff d} {C : ℝ} {e : Coeff d} (hc : WS q c)
    (h : ∀ k, Lattice.jp k ^ p * ‖e k‖ ≤ C * (Lattice.jp k ^ q * ‖c k‖)) :
    WS p e ∧ WN p e ≤ C * WN q c := by
  have hs : WS p e := Summable.of_nonneg_of_le
    (fun k => mul_nonneg (jp_pow_nonneg p k) (norm_nonneg _)) h (hc.mul_left C)
  refine ⟨hs, ?_⟩
  unfold WN
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum h hs (hc.mul_left C)

lemma WS_derivCoeff {p : ℕ} {c : Coeff d} (hc : WS (p + 1) c) (j : Fin d) :
    WS p (derivCoeff j c) ∧ WN p (derivCoeff j c) ≤ 1 * WN (p + 1) c := by
  refine WS_of_le hc fun k => ?_
  calc Lattice.jp k ^ p * ‖derivCoeff j c k‖ ≤ Lattice.jp k ^ p * (Lattice.jp k * ‖c k‖) :=
        mul_le_mul_of_nonneg_left (norm_derivCoeff_le j c k) (jp_pow_nonneg p k)
    _ = 1 * (Lattice.jp k ^ (p + 1) * ‖c k‖) := by ring

lemma WS_laplaceCoeff {p : ℕ} {c : Coeff d} (hc : WS (p + 2) c) :
    WS p (laplaceCoeff c) ∧ WN p (laplaceCoeff c) ≤ 1 * WN (p + 2) c := by
  refine WS_of_le hc fun k => ?_
  calc Lattice.jp k ^ p * ‖laplaceCoeff c k‖ ≤ Lattice.jp k ^ p * (Lattice.jp k ^ 2 * ‖c k‖) :=
        mul_le_mul_of_nonneg_left (norm_laplaceCoeff_le c k) (jp_pow_nonneg p k)
    _ = 1 * (Lattice.jp k ^ (p + 2) * ‖c k‖) := by ring

lemma WS_gradRieszCoeff (s : ℝ) (hsd : s ≤ d) {p : ℕ} {c : Coeff d} (hc : WS (p + 1) c)
    (i : Fin d) :
    WS p (gradRieszCoeff d s i c) ∧ WN p (gradRieszCoeff d s i c) ≤ |rieszConst d s| * WN (p + 1) c := by
  refine WS_of_le hc fun k => ?_
  calc Lattice.jp k ^ p * ‖gradRieszCoeff d s i c k‖
      ≤ Lattice.jp k ^ p * (|rieszConst d s| * (Lattice.jp k * ‖c k‖)) :=
        mul_le_mul_of_nonneg_left (norm_gradRieszCoeff_le s hsd i c k) (jp_pow_nonneg p k)
    _ = |rieszConst d s| * (Lattice.jp k ^ (p + 1) * ‖c k‖) := by ring

/-! ### Finite sums -/

lemma WS_sum {ι : Type*} (S : Finset ι) (f : ι → Coeff d) (p : ℕ) (h : ∀ i ∈ S, WS p (f i)) :
    WS p (∑ i ∈ S, f i) ∧ WN p (∑ i ∈ S, f i) ≤ ∑ i ∈ S, WN p (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [WS.zero, WN]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have h2 := h a (Finset.mem_insert_self _ _)
    exact ⟨WS.add h2 h1.1, (WN_add_le h2 h1.1).trans (by linarith [h1.2])⟩

lemma sum_apply_coeff {ι : Type*} (S : Finset ι) (f : ι → Coeff d) (k : Lattice d) :
    (∑ i ∈ S, f i) k = ∑ i ∈ S, f i k := Finset.sum_apply k S f

/-! ### The forward generator with a free density coefficient -/

/-- `∑_i M_{ji} ∂_i g * r` (the nonlocal part of the drift). -/
def Bop (D : DynData d) (r : Coeff d) (j : Fin d) : Coeff d := fun k =>
  ∑ i : Fin d, ((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i r k

/-- `∂_j V` in Fourier space. -/
def Vd (D : DynData d) (j : Fin d) : Coeff d := derivCoeff j (coeffOf D.V)

/-- The drift `b_j = ∑_i M_{ji} ∂_i g * r - ∂_j V`. -/
def driftOf (D : DynData d) (r : Coeff d) (j : Fin d) : Coeff d := Bop D r j - Vd D j

def T1 (D : DynData d) (c : Coeff d) : Coeff d := fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff c k

def T2 (D : DynData d) (r c : Coeff d) : Coeff d := fun k =>
  ∑ j : Fin d, mulCoeff (driftOf D r j) (derivCoeff j c) k

def T3 (D : DynData d) (r c : Coeff d) : Coeff d := fun k =>
  ∑ i : Fin d, ∑ j : Fin d, ((D.M j i : ℝ) : ℂ) *
    gradRieszCoeff d D.s i (mulCoeff r (derivCoeff j c)) k

/-- `forwardGen` with the density coefficient `r` in place of `coeffOf ρ`. -/
def fwd (D : DynData d) (r c : Coeff d) : Coeff d := fun k => T1 D c k + T2 D r c k - T3 D r c k

lemma forwardGen_eq_fwd (D : DynData d) (ρ : Torus d → ℝ) (c : Coeff d) :
    forwardGen D ρ c = fwd D (coeffOf ρ) c := rfl

/-! ### Bounds for the pieces -/

section Pieces

variable (D : DynData d)

lemma Bop_sub (r r' : Coeff d) (j : Fin d) : Bop D (r - r') j = Bop D r j - Bop D r' j := by
  funext k
  simp only [Bop, gradRieszCoeff_sub, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The constant `a_j = (∑_i |M_{ji}|) |c_{d,s}|`. -/
def aCoef (j : Fin d) : ℝ := (∑ i, |D.M j i|) * |rieszConst d D.s|

lemma aCoef_nonneg (j : Fin d) : 0 ≤ aCoef D j :=
  mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (abs_nonneg _)

lemma Bop_eq_sum (r : Coeff d) (j : Fin d) :
    Bop D r j = ∑ i, ((D.M j i : ℝ) : ℂ) • gradRieszCoeff d D.s i r := by
  funext k
  simp [Bop, Finset.sum_apply]

lemma Bop_bound {r : Coeff d} (hr : WS 1 r) (j : Fin d) :
    WS 0 (Bop D r j) ∧ WN 0 (Bop D r j) ≤ aCoef D j * WN 1 r := by
  have hsd : D.s ≤ d := D.hsd.le
  rw [Bop_eq_sum]
  have h := WS_sum Finset.univ (fun i => ((D.M j i : ℝ) : ℂ) • gradRieszCoeff d D.s i r) 0
    (fun i _ => (WS_gradRieszCoeff D.s hsd hr i).1.smul _)
  refine ⟨h.1, h.2.trans ?_⟩
  calc ∑ i, WN 0 (((D.M j i : ℝ) : ℂ) • gradRieszCoeff d D.s i r)
      ≤ ∑ i, |D.M j i| * (|rieszConst d D.s| * WN 1 r) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [WN_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (WS_gradRieszCoeff D.s hsd hr i).2 (abs_nonneg _)
    _ = aCoef D j * WN 1 r := by
        unfold aCoef
        rw [← Finset.sum_mul]; ring

lemma Vd_bound (hV : WS 1 (coeffOf D.V)) (j : Fin d) :
    WS 0 (Vd D j) ∧ WN 0 (Vd D j) ≤ WN 1 (coeffOf D.V) := by
  have := WS_derivCoeff hV j
  exact ⟨this.1, by simpa [Vd] using this.2⟩

lemma driftOf_bound {r : Coeff d} (hr : WS 1 r) (hV : WS 1 (coeffOf D.V)) (j : Fin d) :
    WS 0 (driftOf D r j) ∧ WN 0 (driftOf D r j) ≤ aCoef D j * WN 1 r + WN 1 (coeffOf D.V) := by
  have h1 := Bop_bound D hr j
  have h2 := Vd_bound D hV j
  refine ⟨WS.sub h1.1 h2.1, (WN_sub_le h1.1 h2.1).trans ?_⟩
  linarith [h1.2, h2.2]

lemma driftOf_sub (r r' : Coeff d) (j : Fin d) :
    driftOf D r j - driftOf D r' j = Bop D (r - r') j := by
  unfold driftOf
  rw [Bop_sub]; abel

lemma WS_deriv0 {c : Coeff d} (hc : WS 1 c) (j : Fin d) : WS 0 (derivCoeff j c) :=
  (WS_derivCoeff (p := 0) hc j).1

lemma WN_deriv0 {c : Coeff d} (hc : WS 1 c) (j : Fin d) :
    WN 0 (derivCoeff j c) ≤ WN 1 c := by
  simpa using (WS_derivCoeff (p := 0) hc j).2

lemma T2_diff_eq (r r' c c' : Coeff d) (hr : WS 1 r) (hr' : WS 1 r') (hV : WS 1 (coeffOf D.V))
    (hc : WS 1 c) (hc' : WS 1 c') :
    T2 D r c - T2 D r' c' = ∑ j, (mulCoeff (Bop D (r - r') j) (derivCoeff j c) +
      mulCoeff (driftOf D r' j) (derivCoeff j (c - c'))) := by
  funext k
  simp only [T2, Pi.sub_apply, sum_apply_coeff, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (mulCoeff_diff (a := driftOf D r j) (a' := driftOf D r' j)
    (c := derivCoeff j c) (c' := derivCoeff j c') (driftOf_bound D hr hV j).1
    (driftOf_bound D hr' hV j).1 (WS_deriv0 hc j) (WS_deriv0 hc' j)) k
  simp only [Pi.sub_apply, Pi.add_apply] at h
  rw [h, driftOf_sub, derivCoeff_sub]
  rfl

lemma T2_diff_bound (r r' c c' : Coeff d) (hr : WS 1 r) (hr' : WS 1 r')
    (hV : WS 1 (coeffOf D.V)) (hc : WS 2 c) (hc' : WS 2 c') :
    WS 0 (T2 D r c - T2 D r' c') ∧ WN 0 (T2 D r c - T2 D r' c') ≤
      ∑ j : Fin d, (2 * (aCoef D j * WN 1 (r - r') * WN 2 c) +
        2 * ((aCoef D j * WN 1 r' + WN 1 (coeffOf D.V)) * WN 2 (c - c'))) := by
  have hc1 : WS 1 c := hc.mono (by norm_num)
  have hc1' : WS 1 c' := hc'.mono (by norm_num)
  rw [T2_diff_eq D r r' c c' hr hr' hV hc1 hc1']
  have hrr : WS 1 (r - r') := hr.sub hr'
  have hcc : WS 2 (c - c') := hc.sub hc'
  have hcc1 : WS 1 (c - c') := hcc.mono (by norm_num)
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      WS 0 (mulCoeff (Bop D (r - r') j) (derivCoeff j c) +
        mulCoeff (driftOf D r' j) (derivCoeff j (c - c'))) ∧
      WN 0 (mulCoeff (Bop D (r - r') j) (derivCoeff j c) +
        mulCoeff (driftOf D r' j) (derivCoeff j (c - c'))) ≤
      2 * (aCoef D j * WN 1 (r - r') * WN 2 c) +
        2 * ((aCoef D j * WN 1 r' + WN 1 (coeffOf D.V)) * WN 2 (c - c')) := by
    intro j _
    have b1 := Bop_bound D hrr j
    have b2 := driftOf_bound D hr' hV j
    have c1 := conv0 b1.1 (WS_deriv0 hc1 j)
    have c2 := conv0 b2.1 (WS_deriv0 hcc1 j)
    refine ⟨WS.add c1.1 c2.1, (WN_add_le c1.1 c2.1).trans ?_⟩
    have d1 : WN 0 (derivCoeff j c) ≤ WN 2 c :=
      (WN_deriv0 hc1 j).trans (WN_mono (by norm_num) hc)
    have d2 : WN 0 (derivCoeff j (c - c')) ≤ WN 2 (c - c') :=
      (WN_deriv0 hcc1 j).trans (WN_mono (by norm_num) hcc)
    have e1 : WN 0 (mulCoeff (Bop D (r - r') j) (derivCoeff j c)) ≤
        2 * (aCoef D j * WN 1 (r - r') * WN 2 c) := by
      refine c1.2.trans ?_
      have := WN_nonneg 0 (derivCoeff j c)
      have := WN_nonneg 0 (Bop D (r - r') j)
      have := aCoef_nonneg D j
      have := WN_nonneg 1 (r - r')
      have := WN_nonneg 2 c
      nlinarith [mul_le_mul b1.2 d1 (WN_nonneg 0 _) (mul_nonneg (aCoef_nonneg D j) (WN_nonneg 1 _))]
    have e2 : WN 0 (mulCoeff (driftOf D r' j) (derivCoeff j (c - c'))) ≤
        2 * ((aCoef D j * WN 1 r' + WN 1 (coeffOf D.V)) * WN 2 (c - c')) := by
      refine c2.2.trans ?_
      have := mul_le_mul b2.2 d2 (WN_nonneg 0 _) (add_nonneg
        (mul_nonneg (aCoef_nonneg D j) (WN_nonneg 1 _)) (WN_nonneg 1 _))
      linarith
    linarith
  have h := WS_sum Finset.univ (fun j => mulCoeff (Bop D (r - r') j) (derivCoeff j c) +
        mulCoeff (driftOf D r' j) (derivCoeff j (c - c'))) 0 (fun j hj => (hterm j hj).1)
  refine ⟨h.1, h.2.trans (Finset.sum_le_sum fun j hj => (hterm j hj).2)⟩

lemma T3_diff_eq (r r' c c' : Coeff d) (hr : WS 1 r) (hr' : WS 1 r') (hc : WS 1 c)
    (hc' : WS 1 c') :
    T3 D r c - T3 D r' c' = ∑ i, ∑ j, ((D.M j i : ℝ) : ℂ) •
      gradRieszCoeff d D.s i (mulCoeff (r - r') (derivCoeff j c) +
        mulCoeff r' (derivCoeff j (c - c'))) := by
  funext k
  simp only [T3, Pi.sub_apply, sum_apply_coeff, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := mulCoeff_diff (a := r) (a' := r') (c := derivCoeff j c) (c' := derivCoeff j c')
    (hr.mono (Nat.zero_le _)) (hr'.mono (Nat.zero_le _)) (WS_deriv0 hc j) (WS_deriv0 hc' j)
  rw [← derivCoeff_sub] at h
  rw [← mul_sub, ← Pi.sub_apply, ← gradRieszCoeff_sub, h]

def S2 : ℝ := ∑ j : Fin d, aCoef D j

def S3 : ℝ := ∑ i : Fin d, ∑ j : Fin d, |D.M j i| * |rieszConst d D.s|

lemma S2_nonneg : 0 ≤ S2 D := Finset.sum_nonneg fun j _ => aCoef_nonneg D j

lemma S3_nonneg : 0 ≤ S3 D :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

lemma T3_diff_bound (r r' c c' : Coeff d) (hr : WS 1 r) (hr' : WS 1 r') (hc : WS 2 c)
    (hc' : WS 2 c') :
    WS 0 (T3 D r c - T3 D r' c') ∧ WN 0 (T3 D r c - T3 D r' c') ≤
      S3 D * (2 * (WN 1 (r - r') * WN 2 c) + 2 * (WN 1 r' * WN 2 (c - c'))) := by
  have hsd : D.s ≤ d := D.hsd.le
  have hc1 : WS 1 c := hc.mono (by norm_num)
  have hc1' : WS 1 c' := hc'.mono (by norm_num)
  rw [T3_diff_eq D r r' c c' hr hr' hc1 hc1']
  have hrr : WS 1 (r - r') := hr.sub hr'
  have hcc : WS 2 (c - c') := hc.sub hc'
  have hcc1 : WS 1 (c - c') := hcc.mono (by norm_num)
  have hX := WN_nonneg 1 (r - r')
  have hY := WN_nonneg 2 c
  have hZ := WN_nonneg 1 r'
  have hU := WN_nonneg 2 (c - c')
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)), ∀ j ∈ (Finset.univ : Finset (Fin d)),
      WS 0 (((D.M j i : ℝ) : ℂ) • gradRieszCoeff d D.s i (mulCoeff (r - r') (derivCoeff j c) +
        mulCoeff r' (derivCoeff j (c - c')))) ∧
      WN 0 (((D.M j i : ℝ) : ℂ) • gradRieszCoeff d D.s i (mulCoeff (r - r') (derivCoeff j c) +
        mulCoeff r' (derivCoeff j (c - c')))) ≤
        |D.M j i| * |rieszConst d D.s| * (2 * (WN 1 (r - r') * WN 2 c) + 2 * (WN 1 r' * WN 2 (c - c'))) := by
    intro i _ j _
    have hd1 : WS 1 (derivCoeff j c) := (WS_derivCoeff (p := 1) hc j).1
    have hd2 : WS 1 (derivCoeff j (c - c')) := (WS_derivCoeff (p := 1) hcc j).1
    have c1 := conv1 hrr hd1
    have c2 := conv1 hr' hd2
    have hs : WS 1 (mulCoeff (r - r') (derivCoeff j c) + mulCoeff r' (derivCoeff j (c - c'))) :=
      WS.add c1.1 c2.1
    have g := WS_gradRieszCoeff D.s hsd (p := 0) hs i
    refine ⟨g.1.smul _, ?_⟩
    rw [WN_smul, Complex.norm_real, Real.norm_eq_abs]
    -- bounds on the four factors
    have n1 : WN 1 (derivCoeff j c) ≤ WN 2 c := by simpa using (WS_derivCoeff (p := 1) hc j).2
    have n2 : WN 1 (derivCoeff j (c - c')) ≤ WN 2 (c - c') := by
      simpa using (WS_derivCoeff (p := 1) hcc j).2
    have n3 : WN 0 (derivCoeff j c) ≤ WN 2 c := (WN_deriv0 hc1 j).trans (WN_mono (by norm_num) hc)
    have n4 : WN 0 (derivCoeff j (c - c')) ≤ WN 2 (c - c') :=
      (WN_deriv0 hcc1 j).trans (WN_mono (by norm_num) hcc)
    have n5 : WN 0 (r - r') ≤ WN 1 (r - r') := WN_mono (by norm_num) hrr
    have n6 : WN 0 r' ≤ WN 1 r' := WN_mono (by norm_num) hr'
    have p1 : WN 1 (mulCoeff (r - r') (derivCoeff j c)) ≤ 2 * (WN 1 (r - r') * WN 2 c) := by
      refine c1.2.trans ?_
      have := mul_le_mul_of_nonneg_left n3 hX
      have := mul_le_mul n5 n1 (WN_nonneg 1 _) hX
      nlinarith
    have p2 : WN 1 (mulCoeff r' (derivCoeff j (c - c'))) ≤ 2 * (WN 1 r' * WN 2 (c - c')) := by
      refine c2.2.trans ?_
      have := mul_le_mul_of_nonneg_left n4 hZ
      have := mul_le_mul n6 n2 (WN_nonneg 1 _) hZ
      nlinarith
    have p3 := WN_add_le c1.1 c2.1
    have : WN 0 (gradRieszCoeff d D.s i (mulCoeff (r - r') (derivCoeff j c) +
        mulCoeff r' (derivCoeff j (c - c')))) ≤ |rieszConst d D.s| *
        (2 * (WN 1 (r - r') * WN 2 c) + 2 * (WN 1 r' * WN 2 (c - c'))) := by
      refine g.2.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      linarith
    calc |D.M j i| * WN 0 (gradRieszCoeff d D.s i (mulCoeff (r - r') (derivCoeff j c) +
        mulCoeff r' (derivCoeff j (c - c'))))
        ≤ |D.M j i| * (|rieszConst d D.s| *
        (2 * (WN 1 (r - r') * WN 2 c) + 2 * (WN 1 r' * WN 2 (c - c'))))  :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      WS 0 (∑ j, ((D.M j i : ℝ) : ℂ) • gradRieszCoeff d D.s i (mulCoeff (r - r') (derivCoeff j c) +
        mulCoeff r' (derivCoeff j (c - c')))) ∧
      WN 0 (∑ j, ((D.M j i : ℝ) : ℂ) • gradRieszCoeff d D.s i (mulCoeff (r - r') (derivCoeff j c) +
        mulCoeff r' (derivCoeff j (c - c')))) ≤ ∑ j : Fin d,
        |D.M j i| * |rieszConst d D.s| * (2 * (WN 1 (r - r') * WN 2 c) + 2 * (WN 1 r' * WN 2 (c - c'))) := by
    intro i hi
    have := WS_sum Finset.univ (fun j => ((D.M j i : ℝ) : ℂ) • gradRieszCoeff d D.s i
      (mulCoeff (r - r') (derivCoeff j c) + mulCoeff r' (derivCoeff j (c - c')))) 0
      (fun j hj => (hterm i hi j hj).1)
    exact ⟨this.1, this.2.trans (Finset.sum_le_sum fun j hj => (hterm i hi j hj).2)⟩
  have h2 := WS_sum Finset.univ (fun i => ∑ j, ((D.M j i : ℝ) : ℂ) • gradRieszCoeff d D.s i
      (mulCoeff (r - r') (derivCoeff j c) + mulCoeff r' (derivCoeff j (c - c')))) 0
      (fun i hi => (h1 i hi).1)
  refine ⟨h2.1, h2.2.trans ((Finset.sum_le_sum fun i hi => (h1 i hi).2).trans ?_)⟩
  unfold S3
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]

lemma T1_diff_bound (c c' : Coeff d) (hc : WS 2 c) (hc' : WS 2 c') :
    WS 0 (T1 D c - T1 D c') ∧ WN 0 (T1 D c - T1 D c') ≤ D.invβ * WN 2 (c - c') := by
  have hcc : WS 2 (c - c') := hc.sub hc'
  have e : T1 D c - T1 D c' = ((D.invβ : ℝ) : ℂ) • laplaceCoeff (c - c') := by
    funext k
    simp [T1, laplaceCoeff_sub, mul_sub]
  rw [e]
  have h := WS_laplaceCoeff (p := 0) hcc
  refine ⟨h.1.smul _, ?_⟩
  rw [WN_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg D.hβ]
  exact mul_le_mul_of_nonneg_left (by simpa using h.2) D.hβ

/-- The Lipschitz constant of the forward generator. -/
def Kgen : ℝ := D.invβ + 2 * S2 D + 2 * S3 D + 2 * d

lemma Kgen_nonneg : 0 ≤ Kgen D := by
  unfold Kgen
  have := D.hβ
  have := S2_nonneg D
  have := S3_nonneg D
  positivity

/-- **Main estimate**: the forward generator is Lipschitz from `(WS 1) × (WS 2)` into `WS 0`. -/
lemma fwd_diff_bound (r r' c c' : Coeff d) (hr : WS 1 r) (hr' : WS 1 r')
    (hV : WS 1 (coeffOf D.V)) (hc : WS 2 c) (hc' : WS 2 c') :
    WS 0 (fwd D r c - fwd D r' c') ∧ WN 0 (fwd D r c - fwd D r' c') ≤
      Kgen D * (WN 1 (r - r') * WN 2 c +
        (1 + WN 1 r' + WN 1 (coeffOf D.V)) * WN 2 (c - c')) := by
  have t1 := T1_diff_bound D c c' hc hc'
  have t2 := T2_diff_bound D r r' c c' hr hr' hV hc hc'
  have t3 := T3_diff_bound D r r' c c' hr hr' hc hc'
  have e : fwd D r c - fwd D r' c' = (T1 D c - T1 D c') + (T2 D r c - T2 D r' c') -
      (T3 D r c - T3 D r' c') := by
    funext k; simp [fwd]; ring
  rw [e]
  refine ⟨WS.sub (WS.add t1.1 t2.1) t3.1, ?_⟩
  refine (WN_sub_le (WS.add t1.1 t2.1) t3.1).trans ?_
  refine (add_le_add (WN_add_le t1.1 t2.1) le_rfl).trans ?_
  set X := WN 1 (r - r') with hX
  set Y := WN 2 c with hY
  set Z := WN 1 r' with hZ
  set W := WN 1 (coeffOf D.V) with hW
  set U := WN 2 (c - c') with hU
  have hX0 : 0 ≤ X := WN_nonneg _ _
  have hY0 : 0 ≤ Y := WN_nonneg _ _
  have hZ0 : 0 ≤ Z := WN_nonneg _ _
  have hW0 : 0 ≤ W := WN_nonneg _ _
  have hU0 : 0 ≤ U := WN_nonneg _ _
  have hsum2 : ∑ j : Fin d, (2 * (aCoef D j * X * Y) + 2 * ((aCoef D j * Z + W) * U)) =
      S2 D * (2 * X * Y + 2 * Z * U) + d * (2 * W * U) := by
    calc ∑ j : Fin d, (2 * (aCoef D j * X * Y) + 2 * ((aCoef D j * Z + W) * U))
        = ∑ j : Fin d, (aCoef D j * (2 * X * Y + 2 * Z * U) + 2 * W * U) :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          simp [S2]
  have hν := D.hβ
  have hS2 := S2_nonneg D
  have hS3 := S3_nonneg D
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have key : D.invβ * U + ∑ j : Fin d, (2 * (aCoef D j * X * Y) + 2 * ((aCoef D j * Z + W) * U)) +
      S3 D * (2 * (X * Y) + 2 * (Z * U)) ≤ Kgen D * (X * Y + (1 + Z + W) * U) := by
    rw [hsum2]
    have e2 : Kgen D * (X * Y + (1 + Z + W) * U) - (D.invβ * U + (S2 D * (2 * X * Y + 2 * Z * U) +
        d * (2 * W * U)) + S3 D * (2 * (X * Y) + 2 * (Z * U))) =
        (D.invβ + 2 * d) * (X * Y) + (2 * S2 D + 2 * S3 D + 2 * d) * U +
        (D.invβ + 2 * d) * (Z * U) + (D.invβ + 2 * S2 D + 2 * S3 D) * (W * U) := by
      unfold Kgen; ring
    have : 0 ≤ (D.invβ + 2 * d) * (X * Y) + (2 * S2 D + 2 * S3 D + 2 * d) * U +
        (D.invβ + 2 * d) * (Z * U) + (D.invβ + 2 * S2 D + 2 * S3 D) * (W * U) := by positivity
    linarith
  have h1 := t1.2
  have h2 := t2.2
  have h3 := t3.2
  linarith

end Pieces

/-! ### `H^N` bounds of the coefficients of a `C^N` function -/

lemma cbNorm_partialDeriv_le (N : ℕ) (φ : Torus d → ℝ) (hφ : Torus.IsCk ((N + 1 : ℕ) : WithTop ℕ∞) φ)
    (j : Fin d) :
    Torus.IsCk (N : WithTop ℕ∞) (Torus.partialDeriv j φ) ∧
      Torus.cbNorm N (Torus.partialDeriv j φ) ≤ Torus.cbNorm (N + 1) φ := by
  have h1 : Torus.IsCk 1 φ := hφ.of_le (by exact_mod_cast Nat.le_add_left 1 N)
  have hA : ContDiff ℝ (N : WithTop ℕ∞) (fderiv ℝ (Torus.lift φ)) :=
    ContDiff.fderiv_right (m := (N : WithTop ℕ∞)) hφ (by push_cast; exact le_rfl)
  set ev : (Euc d →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))
    with hev
  have hlift : Torus.lift (Torus.partialDeriv j φ) = fun y => ev (fderiv ℝ (Torus.lift φ) y) := by
    rw [lift_partialDeriv j φ h1]; rfl
  have hcd : Torus.IsCk (N : WithTop ℕ∞) (Torus.partialDeriv j φ) := by
    unfold Torus.IsCk
    rw [hlift]
    exact ev.contDiff.comp hA
  refine ⟨hcd, ?_⟩
  have hev1 : ‖ev‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    simp only [hev, ContinuousLinearMap.apply_apply, PiLp.norm_single, norm_one, mul_one]
    have := f.le_opNorm (EuclideanSpace.single j (1 : ℝ))
    simpa [PiLp.norm_single] using this
  have hpt : ∀ i ≤ N, ∀ y : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift (Torus.partialDeriv j φ)) y‖ ≤
      ‖iteratedFDeriv ℝ (i + 1) (Torus.lift φ) y‖ := by
    intro i hi y
    rw [hlift]
    have hAi : ContDiffAt ℝ (i : WithTop ℕ∞) (fderiv ℝ (Torus.lift φ)) y :=
      (hA.of_le (by exact_mod_cast hi)).contDiffAt
    have := ev.norm_iteratedFDeriv_comp_left hAi (le_refl _)
    refine this.trans ?_
    rw [norm_iteratedFDeriv_fderiv]
    calc ‖ev‖ * ‖iteratedFDeriv ℝ (i + 1) (Torus.lift φ) y‖
        ≤ 1 * ‖iteratedFDeriv ℝ (i + 1) (Torus.lift φ) y‖ :=
          mul_le_mul_of_nonneg_right hev1 (norm_nonneg _)
      _ = _ := one_mul _
  unfold Torus.cbNorm
  have hsum : ∀ i ∈ Finset.range (N + 1),
      (⨆ x : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift (Torus.partialDeriv j φ)) x‖) ≤
        ⨆ x : Euc d, ‖iteratedFDeriv ℝ (i + 1) (Torus.lift φ) x‖ := by
    intro i hi
    have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hb := Torus.bddAbove_norm_iteratedFDeriv_lift (i + 1) φ
      (hφ.of_le (by exact_mod_cast Nat.succ_le_succ hiN))
    refine ciSup_le fun x => (hpt i hiN x).trans (le_ciSup hb x)
  refine (Finset.sum_le_sum hsum).trans ?_
  rw [Finset.sum_range_succ' (fun i => ⨆ x : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift φ) x‖) (N + 1)]
  have : 0 ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift φ) x‖ :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  linarith

lemma cbNorm_mono_succ (N : ℕ) (φ : Torus d → ℝ) : Torus.cbNorm N φ ≤ Torus.cbNorm (N + 1) φ := by
  unfold Torus.cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ _ |> Nat.succ_le_succ))
    (fun i _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)

lemma sobWeight_succ_expand (N : ℕ) (u : Coeff d) (k : Lattice d) :
    sobWeight ((N + 1 : ℕ) : ℝ) k * ‖u k‖ ^ 2 =
      sobWeight (N : ℝ) k * ‖u k‖ ^ 2 + ∑ j : Fin d, sobWeight (N : ℝ) k * ‖derivCoeff j u k‖ ^ 2 := by
  have h1 : sobWeight ((N + 1 : ℕ) : ℝ) k = sobWeight (N : ℝ) k * sobWeight 1 k := by
    rw [← sobWeight_add]; push_cast; rfl
  rw [h1, sobWeight_one_eq_sum]
  have h2 : ∀ j : Fin d, ‖derivCoeff j u k‖ ^ 2 = (2 * Real.pi * ((k j : ℤ) : ℝ)) ^ 2 * ‖u k‖ ^ 2 := by
    intro j
    rw [norm_derivCoeff, mul_pow, ← sq_abs (2 * Real.pi * ((k j : ℤ) : ℝ)), abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  simp_rw [h2]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma memHs_coeffOf_cbNorm (N : ℕ) : ∀ (φ : Torus d → ℝ), Torus.IsCk (N : WithTop ℕ∞) φ →
    MemHs (N : ℝ) (coeffOf φ) ∧
      hsNormSq (N : ℝ) (coeffOf φ) ≤ (1 + d) ^ N * Torus.cbNorm N φ ^ 2 := by
  induction N with
  | zero =>
    intro φ hφ
    have hc : Continuous φ := Torus.continuous_of_continuous_lift (hφ.continuous)
    have := memHs_zero_coeffOf_le φ hc (Torus.cbNorm 0 φ) (abs_le_cbNorm 0 φ hφ)
    simpa using this
  | succ N ih =>
    intro φ hφ
    have h1 : Torus.IsCk 1 φ := hφ.of_le (by exact_mod_cast Nat.le_add_left 1 N)
    have hφN : Torus.IsCk (N : WithTop ℕ∞) φ := hφ.of_le (by exact_mod_cast Nat.le_succ N)
    have iφ := ih φ hφN
    have iD := fun j : Fin d => ih (Torus.partialDeriv j φ) (cbNorm_partialDeriv_le N φ hφ j).1
    have cD := fun j : Fin d => (cbNorm_partialDeriv_le N φ hφ j).2
    have hcoef : ∀ j : Fin d, coeffOf (Torus.partialDeriv j φ) = derivCoeff j (coeffOf φ) :=
      fun j => coeffOf_partialDeriv j φ h1
    set u := coeffOf φ with hu
    have iD' : ∀ j : Fin d, MemHs (N : ℝ) (derivCoeff j u) ∧
        hsNormSq (N : ℝ) (derivCoeff j u) ≤ (1 + d) ^ N * Torus.cbNorm N (Torus.partialDeriv j φ) ^ 2 := by
      intro j; rw [← hcoef j]; exact iD j
    have hcb0 := fun j : Fin d => (Finset.sum_nonneg fun i _ => Real.iSup_nonneg fun _ =>
      norm_nonneg (iteratedFDeriv ℝ i (Torus.lift (Torus.partialDeriv j φ)) _) :
      0 ≤ Torus.cbNorm N (Torus.partialDeriv j φ))
    have hbound : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight ((N + 1 : ℕ) : ℝ) k * ‖u k‖ ^ 2 ≤
        (1 + d) ^ (N + 1) * Torus.cbNorm (N + 1) φ ^ 2 := by
      intro S
      simp_rw [sobWeight_succ_expand]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      have e1 := (sum_le_hsNormSq iφ.1 S).trans iφ.2
      have e2 : ∀ j : Fin d, ∑ k ∈ S, sobWeight (N : ℝ) k * ‖derivCoeff j u k‖ ^ 2 ≤
          (1 + d) ^ N * Torus.cbNorm (N + 1) φ ^ 2 := by
        intro j
        refine ((sum_le_hsNormSq (iD' j).1 S).trans (iD' j).2).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (hcb0 j) (cD j) 2
      have e3 : Torus.cbNorm N φ ^ 2 ≤ Torus.cbNorm (N + 1) φ ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _)
          (cbNorm_mono_succ N φ) 2
      calc _ ≤ (1 + d) ^ N * Torus.cbNorm (N + 1) φ ^ 2 +
            ∑ j : Fin d, (1 + d) ^ N * Torus.cbNorm (N + 1) φ ^ 2 :=
          add_le_add (e1.trans (mul_le_mul_of_nonneg_left e3 (by positivity)))
            (Finset.sum_le_sum fun j _ => e2 j)
        _ = (1 + d) ^ (N + 1) * Torus.cbNorm (N + 1) φ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    exact memHs_of_sum_le hbound

lemma cbNorm_nonneg'' (N : ℕ) (φ : Torus d → ℝ) : 0 ≤ Torus.cbNorm N φ :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

/-- `WS p` of the coefficients of a `C^N` function, `N > d/2 + p`, with a bound by `cbNorm N`. -/
lemma exists_ws_cbNorm (N p : ℕ) (hN : (d : ℝ) / 2 + p < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Torus d → ℝ, Torus.IsCk (N : WithTop ℕ∞) φ →
      WS p (coeffOf φ) ∧ WN p (coeffOf φ) ≤ C * Torus.cbNorm N φ := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_ws_bound (d := d) p (N : ℝ) hN
  refine ⟨C₁ * Real.sqrt ((1 + d) ^ N), by positivity, fun φ hφ => ?_⟩
  obtain ⟨hm, hb⟩ := memHs_coeffOf_cbNorm N φ hφ
  obtain ⟨hS, hW⟩ := h₁ _ hm
  refine ⟨hS, hW.trans ?_⟩
  have : hsNorm (N : ℝ) (coeffOf φ) ≤ Real.sqrt ((1 + d) ^ N) * Torus.cbNorm N φ := by
    unfold hsNorm
    calc Real.sqrt (hsNormSq (N : ℝ) (coeffOf φ)) ≤ Real.sqrt ((1 + d) ^ N * Torus.cbNorm N φ ^ 2) :=
          Real.sqrt_le_sqrt hb
      _ = _ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (cbNorm_nonneg'' N φ)]
  calc C₁ * hsNorm (N : ℝ) (coeffOf φ) ≤ C₁ * (Real.sqrt ((1 + d) ^ N) * Torus.cbNorm N φ) :=
        mul_le_mul_of_nonneg_left this hC₁
    _ = _ := by ring

/-! ### The density path in `WS 1` -/

/-- The coefficients of the density path `τ ↦ μ(t-τ)` are bounded and continuous in `WS 1`. -/
lemma density_path_ws1 {m : ℕ} {Λ T : ℝ} {μ : ℝ → Torus d → ℝ} (hμ : CoeffHyp m Λ T μ)
    (hmd : (d : ℝ) / 2 < m) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) :
    (∃ K : ℝ, ∀ τ ∈ Set.Icc 0 t, WS 1 (coeffOf (μ (t - τ))) ∧ WN 1 (coeffOf (μ (t - τ))) ≤ K) ∧
    ∀ τ₀ ∈ Set.Icc 0 t, Tendsto
      (fun τ => WN 1 (coeffOf (μ (t - τ)) - coeffOf (μ (t - τ₀))))
      (𝓝[Set.Icc 0 t] τ₀) (𝓝 0) := by
  have hmap : ∀ τ ∈ Set.Icc 0 t, t - τ ∈ Set.Icc 0 T := fun τ hτ =>
    ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩
  obtain ⟨C₀, hC₀, h₀⟩ := exists_ws_cbNorm (d := d) (m + 3) 1 (by
    push_cast; linarith)
  refine ⟨⟨C₀ * Λ, fun τ hτ => ?_⟩, ?_⟩
  · have hτ' := hmap τ hτ
    obtain ⟨h1, h2⟩ := h₀ (μ (t - τ)) (by exact_mod_cast hμ.smooth _ hτ')
    refine ⟨h1, h2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (hμ.bound _ hτ') hC₀
  · intro τ₀ hτ₀
    set G : ℝ → Coeff d := fun τ => coeffOf (μ (t - τ)) with hG
    have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) t, MemHs ((m + 3 : ℕ) : ℝ) (G τ) ∧
        hsNormSq ((m + 3 : ℕ) : ℝ) (G τ) ≤ (1 + d) ^ (m + 3) * Torus.cbNorm (m + 3) (μ (t - τ)) ^ 2 :=
      fun τ hτ => memHs_coeffOf_cbNorm (m + 3) _ (by exact_mod_cast hμ.smooth _ (hmap τ hτ))
    have hcoord : ∀ k, ContinuousOn (fun τ => G τ k) (Set.Icc 0 t) := by
      intro k
      have h := continuousOn_coeffOf_family (T := T) (ρ := μ) (fun r hr =>
        continuous_of_isCkU (hμ.smooth r hr)) hμ.cont k
      exact h.comp (continuous_const.sub continuous_id).continuousOn hmap
    set B : ℝ := Real.sqrt ((1 + d) ^ (m + 3) * Λ ^ 2) with hB
    have hweak : WeakContinuousInHs ((m + 3 : ℕ) : ℝ) G t := by
      refine weakContinuous_of_bdd (fun τ hτ => (hmem τ hτ).1) B (Real.sqrt_nonneg _)
        (fun τ hτ => ?_) hcoord
      rw [hB, Real.sq_sqrt (by positivity)]
      refine (hmem τ hτ).2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact pow_le_pow_left₀ (cbNorm_nonneg'' _ _) (hμ.bound _ (hmap τ hτ)) 2
    have hlt : ((m + 2 : ℕ) : ℝ) < ((m + 3 : ℕ) : ℝ) := by push_cast; linarith
    have hcont := continuousInHs_of_weak hweak ((m + 2 : ℕ) : ℝ) hlt
    obtain ⟨C₁, hC₁, h₁⟩ := exists_ws_bound (d := d) 1 ((m + 2 : ℕ) : ℝ) (by
      push_cast; linarith)
    have hsq := hcont.2 τ₀ hτ₀
    have hmemd : ∀ τ ∈ Set.Icc (0 : ℝ) t, MemHs ((m + 2 : ℕ) : ℝ) (G τ - G τ₀) := fun τ hτ =>
      memHs_sub (hcont.1 τ hτ) (hcont.1 τ₀ hτ₀)
    have hup : Tendsto (fun τ => C₁ * hsNorm ((m + 2 : ℕ) : ℝ) (G τ - G τ₀)) (𝓝[Set.Icc 0 t] τ₀)
        (𝓝 0) := by simpa using hsq.const_mul C₁
    refine squeeze_zero' (Filter.Eventually.of_forall fun τ => WN_nonneg _ _) ?_ hup
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (h₁ _ (hmemd τ hτ)).2

/-! ### Continuity of the generator path in `ℓ¹` -/

lemma fwd_zero_right (D : DynData d) (r : Coeff d) : fwd D r 0 = 0 := by
  funext k
  have h1 : ∀ j : Fin d, derivCoeff j (0 : Coeff d) = 0 := fun j => by
    funext l; simp [derivCoeff]
  have h2 : ∀ i : Fin d, gradRieszCoeff d D.s i (0 : Coeff d) = 0 := fun i => by
    funext l; simp [gradRieszCoeff, rieszMult, derivCoeff]
  simp [fwd, T1, T2, T3, laplaceCoeff, h1, mulCoeff_zero_right, h2]

lemma ws0_fwd (D : DynData d) {r c : Coeff d} (hr : WS 1 r) (hV : WS 1 (coeffOf D.V))
    (hc : WS 2 c) : WS 0 (fwd D r c) := by
  have h := (fwd_diff_bound D r r c 0 hr hr hV hc (WS.zero 2)).1
  rwa [fwd_zero_right, sub_zero] at h

lemma tendsto_fwd {l : Filter ℝ} (D : DynData d) {r : ℝ → Coeff d} {r₀ : Coeff d} {c : ℝ → Coeff d}
    {c₀ : Coeff d} (hr₀ : WS 1 r₀) (hV : WS 1 (coeffOf D.V))
    (hc₀ : WS 2 c₀) (hr : ∀ᶠ τ in l, WS 1 (r τ)) (hc : ∀ᶠ τ in l, WS 2 (c τ))
    (hrt : Tendsto (fun τ => WN 1 (r τ - r₀)) l (𝓝 0))
    (hct : Tendsto (fun τ => WN 2 (c τ - c₀)) l (𝓝 0)) :
    Tendsto (fun τ => WN 0 (fwd D (r τ) (c τ) - fwd D r₀ c₀)) l (𝓝 0) := by
  set K := Kgen D
  set Z := WN 1 r₀
  set W := WN 1 (coeffOf D.V)
  set Y₀ := WN 2 c₀
  have hbd : Tendsto (fun τ => K * (WN 1 (r τ - r₀) * (Y₀ + WN 2 (c τ - c₀)) +
      (1 + Z + W) * WN 2 (c τ - c₀))) l (𝓝 0) := by
    have h1 : Tendsto (fun τ => WN 1 (r τ - r₀) * (Y₀ + WN 2 (c τ - c₀)) +
        (1 + Z + W) * WN 2 (c τ - c₀)) l (𝓝 0) := by
      have := (hrt.mul (hct.const_add Y₀)).add (hct.const_mul (1 + Z + W))
      simpa using this
    simpa using h1.const_mul K
  refine squeeze_zero' (Filter.Eventually.of_forall fun τ => WN_nonneg _ _) ?_ hbd
  filter_upwards [hr, hc] with τ hrτ hcτ
  have h := (fwd_diff_bound D (r τ) r₀ (c τ) c₀ hrτ hr₀ hV hcτ hc₀).2
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Kgen_nonneg D))
  have hY : WN 2 (c τ) ≤ Y₀ + WN 2 (c τ - c₀) := by
    have := WN_add_le (hcτ.sub hc₀) hc₀
    rw [sub_add_cancel] at this
    linarith
  have hX := WN_nonneg 1 (r τ - r₀)
  have hU := WN_nonneg 2 (c τ - c₀)
  nlinarith [mul_le_mul_of_nonneg_left hY hX]

/-! ### Pointwise values of `toFun` for `ℓ¹` coefficients -/

lemma series_sub {a b : Coeff d} (ha : WS 0 a) (hb : WS 0 b) (x : Torus d) :
    series (a - b) x = series a x - series b x := by
  rw [WS_zero_iff] at ha hb
  unfold series
  simp only [Pi.sub_apply, sub_mul]
  exact Summable.tsum_sub (summable_series_terms a ha x) (summable_series_terms b hb x)

lemma toFun_sub {a b : Coeff d} (ha : WS 0 a) (hb : WS 0 b) (x : Torus d) :
    toFun (a - b) x = toFun a x - toFun b x := by
  unfold toFun
  rw [series_sub ha hb, Complex.sub_re]

lemma abs_toFun_le_WN {c : Coeff d} (hc : WS 0 c) (x : Torus d) : |toFun c x| ≤ WN 0 c := by
  rw [WS_zero_iff] at hc
  rw [WN_zero]
  exact abs_toFun_le c hc x

lemma norm_series_le_WN {c : Coeff d} (hc : WS 0 c) (x : Torus d) : ‖series c x‖ ≤ WN 0 c := by
  rw [WS_zero_iff] at hc
  rw [WN_zero]
  unfold series
  have hn : Summable fun k => ‖c k * Torus.mode k x‖ :=
    hc.congr (fun k => by simp [Torus.norm_mode])
  refine (norm_tsum_le_tsum_norm hn).trans (le_of_eq (tsum_congr fun k => ?_))
  simp [Torus.norm_mode]

/-- Joint continuity of `(τ, x) ↦ toFun (g τ) x` from `ℓ¹`-continuity of `g`. -/
lemma continuous_toFun_family {X : Type*} [TopologicalSpace X] (g : X → Coeff d)
    (hg : ∀ x, WS 0 (g x)) (hc : ∀ x₀, Tendsto (fun x => WN 0 (g x - g x₀)) (𝓝 x₀) (𝓝 0)) :
    Continuous fun p : X × Torus d => toFun (g p.1) p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, y₀⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hc1 := (continuous_toFun (g x₀) ((WS_zero_iff _).1 (hg x₀))).continuousAt (x := y₀)
  have h1 : ∀ᶠ y in 𝓝 y₀, |toFun (g x₀) y - toFun (g x₀) y₀| < ε / 2 := by
    have := Metric.tendsto_nhds.1 hc1 (ε / 2) (half_pos hε)
    simpa [Real.dist_eq] using this
  have h2 : ∀ᶠ x in 𝓝 x₀, WN 0 (g x - g x₀) < ε / 2 := by
    have := (Metric.tendsto_nhds.1 (hc x₀)) (ε / 2) (half_pos hε)
    filter_upwards [this] with x hx
    rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (WN_nonneg _ _)] at hx
  filter_upwards [h2.prod_inl_nhds y₀, h1.prod_inr_nhds x₀] with p hp1 hp2
  rw [Real.dist_eq]
  have e : toFun (g p.1) p.2 - toFun (g x₀) y₀ =
      toFun (g p.1 - g x₀) p.2 + (toFun (g x₀) p.2 - toFun (g x₀) y₀) := by
    rw [toFun_sub (hg _) (hg _)]; ring
  rw [e]
  refine lt_of_le_of_lt (abs_add_le _ _) ?_
  have := abs_toFun_le_WN ((hg p.1).sub (hg x₀)) p.2
  linarith [hp2]

/-! ### Integration in time of `ℓ¹`-continuous coefficient paths -/

section TimeIntegral

variable {F g : ℝ → Coeff d} {φc : Coeff d} {t : ℝ}

lemma continuousOn_coord_of_WN (hg : ∀ τ ∈ Set.Icc 0 t, WS 0 (g τ))
    (hgc : ∀ τ₀ ∈ Set.Icc 0 t, Tendsto (fun τ => WN 0 (g τ - g τ₀)) (𝓝[Set.Icc 0 t] τ₀) (𝓝 0))
    (k : Lattice d) : ContinuousOn (fun σ => g σ k) (Set.Icc 0 t) := by
  intro τ₀ hτ₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ (hgc τ₀ hτ₀)
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact norm_le_WN ((hg τ hτ).sub (hg τ₀ hτ₀)) k

lemma continuousOn_toFun_path (hg : ∀ τ ∈ Set.Icc 0 t, WS 0 (g τ))
    (hgc : ∀ τ₀ ∈ Set.Icc 0 t, Tendsto (fun τ => WN 0 (g τ - g τ₀)) (𝓝[Set.Icc 0 t] τ₀) (𝓝 0))
    (x : Torus d) : ContinuousOn (fun σ => toFun (g σ) x) (Set.Icc 0 t) := by
  intro τ₀ hτ₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ (hgc τ₀ hτ₀)
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  rw [Real.norm_eq_abs, ← toFun_sub (hg τ hτ) (hg τ₀ hτ₀)]
  exact abs_toFun_le_WN ((hg τ hτ).sub (hg τ₀ hτ₀)) x

lemma exists_bound_WN (hg : ∀ τ ∈ Set.Icc 0 t, WS 0 (g τ))
    (hgc : ∀ τ₀ ∈ Set.Icc 0 t, Tendsto (fun τ => WN 0 (g τ - g τ₀)) (𝓝[Set.Icc 0 t] τ₀) (𝓝 0)) :
    ∃ B : ℝ, ∀ τ ∈ Set.Icc 0 t, WN 0 (g τ) ≤ B := by
  have hcont : ContinuousOn (fun τ => WN 0 (g τ)) (Set.Icc 0 t) := by
    intro τ₀ hτ₀
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ (hgc τ₀ hτ₀)
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [Real.norm_eq_abs, abs_le]
    have h1 := WN_sub_le (hg τ hτ) (hg τ₀ hτ₀)
    have h2 := WN_sub_le (hg τ₀ hτ₀) (hg τ hτ)
    have e : g τ₀ - g τ = -(g τ - g τ₀) := by abel
    have e2 : WN 0 (g τ₀ - g τ) = WN 0 (g τ - g τ₀) := by
      rw [e]
      have := WN_smul (p := 0) (g τ - g τ₀) (-1)
      simpa using this
    have h3 : WN 0 (g τ) ≤ WN 0 (g τ₀) + WN 0 (g τ - g τ₀) := by
      have := WN_add_le ((hg τ hτ).sub (hg τ₀ hτ₀)) (hg τ₀ hτ₀)
      rw [sub_add_cancel] at this
      linarith
    have h4 : WN 0 (g τ₀) ≤ WN 0 (g τ) + WN 0 (g τ - g τ₀) := by
      have := WN_add_le ((hg τ₀ hτ₀).sub (hg τ hτ)) (hg τ hτ)
      rw [sub_add_cancel, e2] at this
      linarith
    constructor <;> linarith
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨B, fun τ hτ => (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_nonneg (WN_nonneg _ _)] using hB τ hτ)⟩

/-- **Integral representation** of `toFun (F b) x - toFun (F a) x`. -/
lemma toFun_sub_eq_integral (hF : ∀ τ ∈ Set.Icc 0 t, WS 0 (F τ)) (hg : ∀ τ ∈ Set.Icc 0 t, WS 0 (g τ))
    (hgc : ∀ τ₀ ∈ Set.Icc 0 t, Tendsto (fun τ => WN 0 (g τ - g τ₀)) (𝓝[Set.Icc 0 t] τ₀) (𝓝 0))
    (heq : ∀ k, ∀ τ ∈ Set.Icc 0 t, F τ k = φc k + ∫ σ in (0 : ℝ)..τ, g σ k)
    (x : Torus d) {a b : ℝ} (ha : a ∈ Set.Icc 0 t) (hb : b ∈ Set.Icc 0 t) :
    toFun (F b) x - toFun (F a) x = ∫ σ in a..b, toFun (g σ) x := by
  have hsub : Set.uIcc a b ⊆ Set.Icc 0 t := Set.uIcc_subset_Icc ha hb
  have hcoord : ∀ k, ContinuousOn (fun σ => g σ k) (Set.Icc 0 t) := continuousOn_coord_of_WN hg hgc
  have hii : ∀ k (u v : ℝ), u ∈ Set.Icc 0 t → v ∈ Set.Icc 0 t →
      IntervalIntegrable (fun σ => g σ k) volume u v := fun k u v hu hv =>
    ((hcoord k).mono (Set.uIcc_subset_Icc hu hv)).intervalIntegrable
  have h0 : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, ha.1.trans ha.2⟩
  have hdiff : ∀ k, (F b - F a) k = ∫ σ in a..b, g σ k := by
    intro k
    simp only [Pi.sub_apply]
    rw [heq k b hb, heq k a ha, add_sub_add_left_eq_sub]
    exact intervalIntegral.integral_interval_sub_left (hii k 0 b h0 hb) (hii k 0 a h0 ha)
  have hFd : WS 0 (F b - F a) := (hF b hb).sub (hF a ha)
  have hHas : HasSum (fun k => (F b - F a) k * Torus.mode k x) (series (F b - F a) x) :=
    (summable_series_terms _ ((WS_zero_iff _).1 hFd) x).hasSum
  have hpart : ∀ s : Finset (Lattice d), ∑ k ∈ s, (F b - F a) k * Torus.mode k x =
      ∫ σ in a..b, ∑ k ∈ s, g σ k * Torus.mode k x := by
    intro s
    rw [intervalIntegral.integral_finset_sum (fun k _ => ((hii k a b ha hb).mul_const _))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hdiff k, intervalIntegral.integral_mul_const]
  obtain ⟨B, hB⟩ := exists_bound_WN hg hgc
  have hlim : Tendsto (fun s : Finset (Lattice d) => ∫ σ in a..b, ∑ k ∈ s, g σ k * Torus.mode k x)
      atTop (𝓝 (∫ σ in a..b, series (g σ) x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun s => ?_
      have : ContinuousOn (fun σ => ∑ k ∈ s, g σ k * Torus.mode k x) (Set.uIcc a b) :=
        continuousOn_finset_sum _ fun k _ => ((hcoord k).mono hsub).mul continuousOn_const
      exact (this.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · refine Filter.Eventually.of_forall fun s => Filter.Eventually.of_forall fun σ hσ => ?_
      have hσ' : σ ∈ Set.Icc 0 t := hsub (Set.uIoc_subset_uIcc hσ)
      refine (norm_sum_le _ _).trans ?_
      have hs := (WS_zero_iff _).1 (hg σ hσ')
      calc ∑ k ∈ s, ‖g σ k * Torus.mode k x‖ = ∑ k ∈ s, ‖g σ k‖ :=
            Finset.sum_congr rfl fun k _ => by simp [Torus.norm_mode]
        _ ≤ ∑' k, ‖g σ k‖ := hs.sum_le_tsum s fun k _ => norm_nonneg _
        _ ≤ B := by simpa [WN_zero] using hB σ hσ'
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun σ hσ => ?_
      have hσ' : σ ∈ Set.Icc 0 t := hsub (Set.uIoc_subset_uIcc hσ)
      exact (summable_series_terms _ ((WS_zero_iff _).1 (hg σ hσ')) x).hasSum
  have hcs : ContinuousOn (fun σ => series (g σ) x) (Set.Icc 0 t) := by
    intro τ₀ hτ₀
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ (hgc τ₀ hτ₀)
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [← series_sub (hg τ hτ) (hg τ₀ hτ₀)]
    exact norm_series_le_WN ((hg τ hτ).sub (hg τ₀ hτ₀)) x
  have hlim' : Tendsto (fun s : Finset (Lattice d) => ∑ k ∈ s, (F b - F a) k * Torus.mode k x)
      atTop (𝓝 (∫ σ in a..b, series (g σ) x)) := by
    simpa only [hpart] using hlim
  have hser : series (F b - F a) x = ∫ σ in a..b, series (g σ) x := tendsto_nhds_unique hHas hlim'
  rw [← toFun_sub (hF b hb) (hF a ha)]
  unfold toFun
  rw [hser]
  have := intervalIntegral.intervalIntegral_re (μ := volume) (f := fun σ => series (g σ) x) (a := a) (b := b)
    ((hcs.mono hsub).intervalIntegrable)
  simpa using this.symm

lemma hasDerivAt_toFun_path (hF : ∀ τ ∈ Set.Icc 0 t, WS 0 (F τ))
    (hg : ∀ τ ∈ Set.Icc 0 t, WS 0 (g τ))
    (hgc : ∀ τ₀ ∈ Set.Icc 0 t, Tendsto (fun τ => WN 0 (g τ - g τ₀)) (𝓝[Set.Icc 0 t] τ₀) (𝓝 0))
    (heq : ∀ k, ∀ τ ∈ Set.Icc 0 t, F τ k = φc k + ∫ σ in (0 : ℝ)..τ, g σ k)
    (x : Torus d) {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 t) :
    HasDerivAt (fun τ' => toFun (F τ') x) (toFun (g τ) x) τ := by
  have hψ := continuousOn_toFun_path hg hgc x
  have h0 : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, (hτ.1.trans hτ.2).le⟩
  have hτ' : τ ∈ Set.Icc 0 t := Set.Ioo_subset_Icc_self hτ
  have hnhds : Set.Icc 0 t ∈ 𝓝 τ := Icc_mem_nhds hτ.1 hτ.2
  have hint : IntervalIntegrable (fun σ => toFun (g σ) x) volume 0 τ :=
    (hψ.mono (Set.uIcc_subset_Icc h0 hτ')).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter (fun σ => toFun (g σ) x) (𝓝 τ) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hψ.mono Set.Ioo_subset_Icc_self) τ hτ
  have hca : ContinuousAt (fun σ => toFun (g σ) x) τ := hψ.continuousAt hnhds
  have hd := (intervalIntegral.integral_hasDerivAt_right hint hmeas hca).const_add (toFun (F 0) x)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with τ' hτ''
  have := toFun_sub_eq_integral hF hg hgc heq x h0 hτ''
  linarith

end TimeIntegral

/-! ### Joint continuity of the derivatives of `toFun` along an `H^{m''}`-continuous path -/

lemma isRealCoeff_sub {a b : Coeff d} (ha : IsRealCoeff a) (hb : IsRealCoeff b) :
    IsRealCoeff (a - b) := by
  intro k
  simp only [Pi.sub_apply, map_sub, ha k, hb k]

lemma toFun_sub_fun {a b : Coeff d} (ha : WS 0 a) (hb : WS 0 b) :
    toFun (a - b) = fun x => toFun a x - toFun b x :=
  funext fun x => toFun_sub ha hb x

lemma ws0_of_memHs {m : ℝ} (hm : (d : ℝ) / 2 < m) {c : Coeff d} (hc : MemHs m c) : WS 0 c :=
  (WS_zero_iff _).2 (summable_norm_of_memHs m hm c hc)

/-- If `G : X → Coeff d` is a path of real coefficients, continuous into `H^{m''}` with
`m'' > d/2 + j`, then `(x, y) ↦ D^j (toFun (G x)) (y)` (on `ℝ^d`) is jointly continuous. -/
lemma continuous_iteratedFDeriv_toFun {X : Type*} [TopologicalSpace X] (G : X → Coeff d) (j : ℕ)
    (m'' : ℝ) (hm'' : (d : ℝ) / 2 + j < m'') (hreal : ∀ x, IsRealCoeff (G x))
    (hmem : ∀ x, MemHs m'' (G x))
    (hcont : ∀ x₀, Tendsto (fun x => hsNorm m'' (G x - G x₀)) (𝓝 x₀) (𝓝 0)) :
    Continuous fun p : X × Euc d => iteratedFDeriv ℝ j (Torus.lift (toFun (G p.1))) p.2 := by
  obtain ⟨C, hC⟩ := toFun_isCk_le (d := d) j m'' hm''
  have hd2 : (d : ℝ) / 2 < m'' := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, y₀⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hck : ∀ x, Torus.IsCk (j : WithTop ℕ∞) (toFun (G x)) := fun x => (hC _ (hmem x) (hreal x)).1
  have hc1 : ContinuousAt (fun y => iteratedFDeriv ℝ j (Torus.lift (toFun (G x₀))) y) y₀ :=
    ((hck x₀).continuous_iteratedFDeriv le_rfl).continuousAt
  have h1 : ∀ᶠ y in 𝓝 y₀, dist (iteratedFDeriv ℝ j (Torus.lift (toFun (G x₀))) y)
      (iteratedFDeriv ℝ j (Torus.lift (toFun (G x₀))) y₀) < ε / 2 :=
    Metric.tendsto_nhds.1 hc1 (ε / 2) (half_pos hε)
  have h2 : ∀ᶠ x in 𝓝 x₀, max C 0 * hsNorm m'' (G x - G x₀) < ε / 2 := by
    have := ((hcont x₀).const_mul (max C 0))
    rw [mul_zero] at this
    exact (this.eventually (gt_mem_nhds (half_pos hε)))
  filter_upwards [h2.prod_inl_nhds y₀, h1.prod_inr_nhds x₀] with p hp2 hp1
  obtain ⟨x, y⟩ := p
  simp only at hp1 hp2 ⊢
  have hmd := memHs_sub (hmem x) (hmem x₀)
  have hrd := isRealCoeff_sub (hreal x) (hreal x₀)
  have hbd := (hC _ hmd hrd)
  have hnn : 0 ≤ hsNorm m'' (G x - G x₀) := Real.sqrt_nonneg _
  have hws : ∀ z, WS 0 (G z) := fun z => ws0_of_memHs hd2 (hmem z)
  have hsplit : Torus.lift (toFun (G x)) = Torus.lift (toFun (G x₀)) +
      Torus.lift (toFun (G x - G x₀)) := by
    funext z
    simp only [Torus.lift, Function.comp, Pi.add_apply, toFun_sub (hws x) (hws x₀)]
    ring
  have hdfn : ContDiffAt ℝ (j : WithTop ℕ∞) (Torus.lift (toFun (G x₀))) y :=
    (hck x₀).contDiffAt
  have hdfn2 : ContDiffAt ℝ (j : WithTop ℕ∞) (Torus.lift (toFun (G x - G x₀))) y :=
    (hC _ hmd hrd).1.contDiffAt
  have hsum : iteratedFDeriv ℝ j (Torus.lift (toFun (G x))) y =
      iteratedFDeriv ℝ j (Torus.lift (toFun (G x₀))) y +
        iteratedFDeriv ℝ j (Torus.lift (toFun (G x - G x₀))) y := by
    rw [hsplit, iteratedFDeriv_add_apply hdfn hdfn2]
  have hb1 : ‖iteratedFDeriv ℝ j (Torus.lift (toFun (G x - G x₀))) y‖ ≤
      max C 0 * hsNorm m'' (G x - G x₀) := by
    refine (norm_iteratedFDeriv_le_cbNorm j j le_rfl _ hbd.1 y).trans ?_
    exact hbd.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hnn)
  rw [dist_eq_norm, hsum]
  have e : iteratedFDeriv ℝ j (Torus.lift (toFun (G x₀))) y +
      iteratedFDeriv ℝ j (Torus.lift (toFun (G x - G x₀))) y -
      iteratedFDeriv ℝ j (Torus.lift (toFun (G x₀))) y₀ =
      iteratedFDeriv ℝ j (Torus.lift (toFun (G x - G x₀))) y +
        (iteratedFDeriv ℝ j (Torus.lift (toFun (G x₀))) y -
          iteratedFDeriv ℝ j (Torus.lift (toFun (G x₀))) y₀) := by abel
  rw [e]
  refine lt_of_le_of_lt (norm_add_le _ _) ?_
  rw [dist_eq_norm] at hp1
  linarith

/-! ### The regularity package for the generator path -/

lemma tendsto_subtype_of_within {t : ℝ} (f : ℝ → ℝ) (x₀ : Set.Icc (0 : ℝ) t)
    (h : Tendsto f (𝓝[Set.Icc 0 t] (x₀ : ℝ)) (𝓝 0)) :
    Tendsto (fun x : Set.Icc (0 : ℝ) t => f x) (𝓝 x₀) (𝓝 0) := by
  rw [nhdsWithin_eq_map_subtype_coe x₀.2, tendsto_map'_iff] at h
  exact h

theorem gen_path_facts {s : ℝ} {m : ℕ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ}
    {μ : ℝ → Torus d → ℝ} (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (hmd : (d : ℝ) / 2 < m)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {φc : Coeff d} {F : ℝ → Coeff d}
    (hsol : IsForwardSolution D μ t φc F) (hreal : ∀ τ ∈ Set.Icc 0 t, IsRealCoeff (F τ))
    {m'' : ℝ} (hm'' : (d : ℝ) / 2 + 2 < m'') (hcont : ContinuousInHs m'' F t) :
    (∀ τ ∈ Set.Icc 0 t, WS 0 (forwardGen D (μ (t - τ)) (F τ)) ∧
        IsRealCoeff (forwardGen D (μ (t - τ)) (F τ))) ∧
    (∀ τ₀ ∈ Set.Icc 0 t, Tendsto
      (fun τ => WN 0 (forwardGen D (μ (t - τ)) (F τ) - forwardGen D (μ (t - τ₀)) (F τ₀)))
      (𝓝[Set.Icc 0 t] τ₀) (𝓝 0)) ∧
    (∀ x : Torus d, ∀ τ ∈ Set.Ioo 0 t,
      HasDerivAt (fun τ' => toFun (F τ') x) (toFun (forwardGen D (μ (t - τ)) (F τ)) x) τ) ∧
    Continuous fun p : Set.Icc (0 : ℝ) t × Torus d =>
      toFun (forwardGen D (μ (t - p.1)) (F p.1)) p.2 := by
  have hmap : ∀ τ ∈ Set.Icc 0 t, t - τ ∈ Set.Icc 0 T := fun τ hτ =>
    ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩
  -- `WS 2` and continuity of `F`
  obtain ⟨C₂, hC₂, h₂⟩ := exists_ws_bound (d := d) 2 m'' (by push_cast; linarith)
  have hWS2 : ∀ τ ∈ Set.Icc (0 : ℝ) t, WS 2 (F τ) := fun τ hτ => (h₂ _ (hcont.1 τ hτ)).1
  have hFc : ∀ τ₀ ∈ Set.Icc (0 : ℝ) t, Tendsto (fun τ => WN 2 (F τ - F τ₀))
      (𝓝[Set.Icc 0 t] τ₀) (𝓝 0) := by
    intro τ₀ hτ₀
    have hsq := hcont.2 τ₀ hτ₀
    have hup : Tendsto (fun τ => C₂ * hsNorm m'' (F τ - F τ₀)) (𝓝[Set.Icc 0 t] τ₀) (𝓝 0) := by
      simpa using hsq.const_mul C₂
    refine squeeze_zero' (Filter.Eventually.of_forall fun τ => WN_nonneg _ _) ?_ hup
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (h₂ _ (memHs_sub (hcont.1 τ hτ) (hcont.1 τ₀ hτ₀))).2
  -- the potential
  obtain ⟨C₁, hC₁, h₁⟩ := exists_ws_cbNorm (d := d) (m + 3) 1 (by push_cast; linarith)
  have hVws : WS 1 (coeffOf D.V) := (h₁ D.V (by exact_mod_cast hA.hV.1)).1
  -- the density path
  obtain ⟨⟨K, hK⟩, hρc⟩ := density_path_ws1 hA.hμ hmd ht
  have hρ : ∀ τ ∈ Set.Icc (0 : ℝ) t, WS 1 (coeffOf (μ (t - τ))) := fun τ hτ => (hK τ hτ).1
  -- continuity of the generator path
  have hg : ∀ τ ∈ Set.Icc (0 : ℝ) t, WS 0 (forwardGen D (μ (t - τ)) (F τ)) := fun τ hτ =>
    ws0_fwd D (hρ τ hτ) hVws (hWS2 τ hτ)
  have hgc : ∀ τ₀ ∈ Set.Icc (0 : ℝ) t, Tendsto
      (fun τ => WN 0 (forwardGen D (μ (t - τ)) (F τ) - forwardGen D (μ (t - τ₀)) (F τ₀)))
      (𝓝[Set.Icc 0 t] τ₀) (𝓝 0) := by
    intro τ₀ hτ₀
    refine tendsto_fwd (l := 𝓝[Set.Icc 0 t] τ₀) D (r := fun τ => coeffOf (μ (t - τ)))
      (c := F) (hρ τ₀ hτ₀) hVws (hWS2 τ₀ hτ₀) ?_ ?_ (hρc τ₀ hτ₀) (hFc τ₀ hτ₀)
    · filter_upwards [self_mem_nhdsWithin] with τ hτ using hρ τ hτ
    · filter_upwards [self_mem_nhdsWithin] with τ hτ using hWS2 τ hτ
  have hF0 : ∀ τ ∈ Set.Icc (0 : ℝ) t, WS 0 (F τ) := fun τ hτ => (hWS2 τ hτ).mono (Nat.zero_le _)
  refine ⟨fun τ hτ => ⟨hg τ hτ, ?_⟩, hgc, ?_, ?_⟩
  · have hρr := isRealCoeff_coeffOf_density hA.hμ (hmap τ hτ)
    have hVr := isRealCoeff_coeffOf_V hA.hV
    have := forwardGen_reflConj D (μ (t - τ)) hρr hVr (F τ)
    have hr := (isRealCoeff_iff_reflConj _).1 (hreal τ hτ)
    refine (isRealCoeff_iff_reflConj _).2 ?_
    rw [← this, hr]
  · intro x τ hτ
    exact hasDerivAt_toFun_path (F := F) (g := fun τ => forwardGen D (μ (t - τ)) (F τ)) (φc := φc)
      hF0 hg hgc hsol.eq x hτ
  · refine continuous_toFun_family (X := Set.Icc (0 : ℝ) t)
      (fun x => forwardGen D (μ (t - x.1)) (F x.1)) (fun x => hg x.1 x.2) (fun x₀ => ?_)
    exact tendsto_subtype_of_within (t := t) (fun τ => WN 0 (forwardGen D (μ (t - τ)) (F τ) -
      forwardGen D (μ (t - (x₀ : ℝ))) (F x₀))) x₀ (hgc x₀ x₀.2)

/-! ### Complex conjugation of forward solutions -/

lemma memHs_reflConj {m : ℝ} {c : Coeff d} (h : MemHs m c) : MemHs m (reflConj c) := by
  have := (Equiv.neg (Lattice d)).summable_iff.2 h
  refine this.congr fun k => ?_
  simp [reflConj, sobWeight_neg]

lemma hsInner_reflConj (m : ℝ) (F G : Coeff d) :
    hsInner m (reflConj F) G = conj (hsInner m F (reflConj G)) := by
  unfold hsInner
  rw [Complex.conj_tsum, ← (Equiv.neg (Lattice d)).tsum_eq]
  refine tsum_congr fun k => ?_
  simp [reflConj, sobWeight_neg]

lemma weakContinuousInHs_reflConj {m : ℝ} {F : ℝ → Coeff d} {t : ℝ}
    (hF : WeakContinuousInHs m F t) : WeakContinuousInHs m (fun τ => reflConj (F τ)) t := by
  refine ⟨fun τ hτ => memHs_reflConj (hF.1 τ hτ), fun G hG => ?_⟩
  have := Complex.continuous_conj.comp_continuousOn (hF.2 (reflConj G) (memHs_reflConj hG))
  refine this.congr fun τ _ => ?_
  simp only [Function.comp]
  rw [hsInner_reflConj]

lemma isForwardSolution_reflConj {D : DynData d} {μ : ℝ → Torus d → ℝ} {t : ℝ} {φc : Coeff d}
    {F : ℝ → Coeff d} (hsol : IsForwardSolution D μ t φc F) (ht : 0 ≤ t)
    (hρ : ∀ σ ∈ Set.Icc (0 : ℝ) t, IsRealCoeff (coeffOf (μ (t - σ))))
    (hV : IsRealCoeff (coeffOf D.V)) :
    IsForwardSolution D μ t (reflConj φc) (fun τ => reflConj (F τ)) := by
  have hgen : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ k, forwardGen D (μ (t - σ)) (reflConj (F σ)) k =
      conj (forwardGen D (μ (t - σ)) (F σ) (-k)) := fun σ hσ k => by
    rw [forwardGen_reflConj D _ (hρ σ hσ) hV]; rfl
  refine ⟨fun τ hτ => memHs_reflConj (hsol.h1 τ hτ), fun k => ?_, fun k τ hτ => ?_⟩
  · have h1 : IntegrableOn (fun σ => conj (forwardGen D (μ (t - σ)) (F σ) (-k))) (Set.Icc 0 t) :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (hsol.integrable (-k))
    refine h1.congr_fun (fun σ hσ => ?_) measurableSet_Icc
    exact (hgen σ hσ k).symm
  · have h0 : (0 : ℝ) ≤ τ := hτ.1
    have e := hsol.eq (-k) τ hτ
    have hc : ∀ g : ℝ → ℂ, conj (∫ σ in (0 : ℝ)..τ, g σ) = ∫ σ in (0 : ℝ)..τ, conj (g σ) := by
      intro g
      simp only [intervalIntegral.integral_of_le h0]
      exact integral_conj.symm
    show conj (F τ (-k)) = _
    rw [e, map_add, hc]
    show _ = conj (φc (-k)) + _
    congr 1
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    have hσ' : σ ∈ Set.Icc 0 t := Set.uIcc_subset_Icc ⟨le_rfl, ht⟩ hτ hσ
    exact (hgen σ hσ' k).symm

/-! ### From coefficients to the classical backward equation -/

lemma adjointData_mono {s : ℝ} {m m' : ℕ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ}
    {μ : ℝ → Torus d → ℝ} (h : AdjointData s m R MB Λ VB D ν₀ T μ) (hm : m' ≤ m) :
    AdjointData s m' R MB Λ VB D ν₀ T μ := by
  have hle : ((m' : ℕ) : WithTop ℕ∞) + 3 ≤ (m : WithTop ℕ∞) + 3 := by
    gcongr
  refine ⟨h.hs, h.hM, ⟨?_, ?_⟩, ⟨h.hμ.prob, fun r hr => ?_, fun r hr => ?_, h.hμ.cont⟩, h.hT,
    h.regime⟩
  · exact (h.hV.1).of_le hle
  · exact (cbNorm_monoU (by omega) _).trans h.hV.2
  · exact (h.hμ.smooth r hr).of_le hle
  · exact (cbNorm_monoU (by omega) _).trans (h.hμ.bound r hr)

open ClassicalAux in
lemma continuous_backwardGenerator (D : DynData d) (hK : ConvKernelFacts d D.s)
    (hV : Torus.IsCk 1 D.V) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) {u : Torus d → ℝ}
    (hu : Torus.IsCk 2 u) : Continuous (backwardGenerator D ρ u) := by
  have hdu : ∀ j, Continuous (Torus.partialDeriv j u) := fun j =>
    continuous_partialDeriv j u (isCk_of_le (by norm_num) hu)
  have hb := fun j => continuous_bfun hK hV hρ j
  have hlap := continuous_laplacian hu
  have hnl : ∀ j, Continuous (fun x => convGradConv (periodicRieszGrad d D.s) (wfun D ρ u j) x j) :=
    fun j => (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp
      (hK.cont _ (isCk_wfun D hρ hu j)))
  rw [backwardGenerator_eq_fun]
  exact ((continuous_const.mul hlap).add (continuous_finsetSum _ fun j _ => (hb j).mul (hdu j))).sub
    (continuous_finsetSum _ fun j _ => hnl j)

open ClassicalAux in
/-- The classical backward generator of `toFun c` is `toFun (𝓛 c)` once the coefficients are
`ℓ¹`, real, and `toFun c` is `C²`. -/
lemma backwardGenerator_eq_toFun (D : DynData d) (hK : ConvKernelFacts d D.s)
    (hV : Torus.IsCk 1 D.V) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) {c : Coeff d}
    (hreal : IsRealCoeff c) (hc : WS 0 c) (hu : Torus.IsCk 2 (toFun c))
    (hGreal : IsRealCoeff (forwardGen D ρ c)) (hG : WS 0 (forwardGen D ρ c)) :
    backwardGenerator D ρ (toFun c) = toFun (forwardGen D ρ c) := by
  have h1 : coeffOf (toFun c) = c := coeffOf_toFun c hreal ((WS_zero_iff _).1 hc)
  have h2 := coeffOf_backwardGenerator D hK hV hρ hu
  rw [h1] at h2
  refine eq_of_coeffOf_eq (continuous_backwardGenerator D hK hV hρ hu)
    (continuous_toFun _ ((WS_zero_iff _).1 hG)) ?_
  rw [h2, coeffOf_toFun _ hGreal ((WS_zero_iff _).1 hG)]

lemma memSobolev_toFun {m : ℝ} {c : Coeff d} (hs : Summable fun k => ‖c k‖) (hc : MemHs m c)
    (hreal : IsRealCoeff c) : MemSobolev m (toFun c) ∧ sobolevNorm m (toFun c) = hsNorm m c := by
  have hcont : Continuous (toFun c) := continuous_toFun c hs
  have hL2 : MemLp (toFun c) 2 volume :=
    hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcoef : coeffOf (toFun c) = c := coeffOf_toFun c hreal hs
  have hS : MemSobolev m (toFun c) := memSobolev_of_memHs m _ hL2 (by rw [hcoef]; exact hc)
  refine ⟨hS, ?_⟩
  obtain ⟨_, h2⟩ := hsNormSq_coeffOf m (toFun c) hS
  rw [hcoef] at h2
  unfold hsNorm
  rw [h2, Real.sqrt_sq]
  unfold sobolevNorm
  exact Real.sqrt_nonneg _

lemma sobolevNorm_eq_hsNorm {m : ℝ} {φ : Torus d → ℝ} (hφ : MemSobolev m φ) :
    sobolevNorm m φ = hsNorm m (coeffOf φ) := by
  obtain ⟨_, h2⟩ := hsNormSq_coeffOf m φ hφ
  unfold hsNorm
  rw [h2, Real.sqrt_sq]
  unfold sobolevNorm
  exact Real.sqrt_nonneg _

/-! ### Plane waves -/

lemma coeffOf_two_modes (k j : Lattice d) (a b : ℂ) (φ : Torus d → ℝ)
    (hφ : ∀ x, (φ x : ℂ) = a * Torus.mode k x + b * Torus.mode (-k) x) :
    coeffOf φ j = a * (if -j + k = 0 then 1 else 0) + b * (if -j + -k = 0 then 1 else 0) := by
  rw [coeffOf_eq_fcoef]
  unfold Torus.fcoef
  have e : ∀ x, Torus.mode (-j) x * (φ x : ℂ) =
      a * (Torus.mode (-j) x * Torus.mode k x) + b * (Torus.mode (-j) x * Torus.mode (-k) x) := by
    intro x; rw [hφ]; ring
  simp_rw [e]
  rw [integral_add ((Torus.integrable_mode_mul _ _).const_mul a)
    ((Torus.integrable_mode_mul _ _).const_mul b), integral_const_mul, integral_const_mul,
    Torus.integral_mode_mul, Torus.integral_mode_mul]

lemma sobolev_two_modes (n : ℕ) (hn : 1 ≤ n) (k : Lattice d) (a b : ℂ) (ha : ‖a‖ ≤ 1 / 2)
    (hb : ‖b‖ ≤ 1 / 2) (φ : Torus d → ℝ) (hcont : Continuous φ)
    (hφ : ∀ x, (φ x : ℂ) = a * Torus.mode k x + b * Torus.mode (-k) x) :
    MemSobolev (n : ℝ) φ ∧ sobolevNorm (n : ℝ) φ ≤ (2 * Real.pi * Lattice.jp k) ^ n := by
  have hc := fun j => coeffOf_two_modes k j a b φ hφ
  have hzero : ∀ j, j ∉ ({k, -k} : Finset (Lattice d)) → coeffOf φ j = 0 := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    rw [hc j]
    have h1 : ¬ (-j + k = 0) := fun h => hj.1 (neg_add_eq_zero.1 h)
    have h2 : ¬ (-j + -k = 0) := fun h => hj.2 (neg_add_eq_zero.1 h)
    simp [h1, h2]
  have hbd : ∀ j, ‖coeffOf φ j‖ ≤ 1 := by
    intro j
    rw [hc j]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖a * (if -j + k = 0 then (1 : ℂ) else 0)‖ ≤ 1 / 2 := by
      split_ifs <;> simp <;> linarith
    have h2 : ‖b * (if -j + -k = 0 then (1 : ℂ) else 0)‖ ≤ 1 / 2 := by
      split_ifs <;> simp <;> linarith
    linarith
  have hmem : MemHs (n : ℝ) (coeffOf φ) :=
    summable_of_ne_finset_zero (s := ({k, -k} : Finset (Lattice d))) fun j hj => by
      simp [hzero j hj]
  have hL2 : MemLp φ 2 volume :=
    hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hS : MemSobolev (n : ℝ) φ := memSobolev_of_memHs _ φ hL2 hmem
  refine ⟨hS, ?_⟩
  rw [sobolevNorm_eq_hsNorm hS]
  have hsq : hsNormSq (n : ℝ) (coeffOf φ) ≤ 2 * (Lattice.jp k ^ n) ^ 2 := by
    unfold hsNormSq
    rw [tsum_eq_sum (s := ({k, -k} : Finset (Lattice d))) (fun j hj => by simp [hzero j hj])]
    have hw : sobWeight (n : ℝ) k = (Lattice.jp k ^ n) ^ 2 := by
      rw [sobWeight_eq_jp, ← pow_mul, mul_comm, pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (Torus.jp_pos k).le]
      push_cast; ring_nf
    have hw' : sobWeight (n : ℝ) (-k) = (Lattice.jp k ^ n) ^ 2 := by
      rw [sobWeight_neg, hw]
    calc ∑ j ∈ ({k, -k} : Finset (Lattice d)), sobWeight (n : ℝ) j * ‖coeffOf φ j‖ ^ 2
        ≤ ∑ j ∈ ({k, -k} : Finset (Lattice d)), (Lattice.jp k ^ n) ^ 2 := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hwj : sobWeight (n : ℝ) j = (Lattice.jp k ^ n) ^ 2 := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl
            · exact hw
            · exact hw'
          rw [hwj]
          have h0 := norm_nonneg (coeffOf φ j)
          have h1 : ‖coeffOf φ j‖ ^ 2 ≤ 1 := by nlinarith [hbd j]
          exact mul_le_of_le_one_right (sq_nonneg _) h1
      _ ≤ 2 * (Lattice.jp k ^ n) ^ 2 := by
          rw [Finset.sum_const]
          have : ({k, -k} : Finset (Lattice d)).card ≤ 2 := Finset.card_le_two
          have h0 : 0 ≤ (Lattice.jp k ^ n) ^ 2 := sq_nonneg _
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) h0
  unfold hsNorm
  have hjp : 0 ≤ Lattice.jp k ^ n := pow_nonneg (Torus.jp_pos k).le _
  have h2pi : (2 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc Real.sqrt (hsNormSq (n : ℝ) (coeffOf φ)) ≤ Real.sqrt (2 * (Lattice.jp k ^ n) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 2 * Lattice.jp k ^ n := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hjp]
    _ ≤ (2 * Real.pi) ^ n * Lattice.jp k ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ hjp
        have h1 : Real.sqrt 2 ≤ 2 := by
          rw [show (2 : ℝ) = Real.sqrt 4 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by norm_num)
        calc Real.sqrt 2 ≤ 2 * Real.pi := h1.trans h2pi
          _ = (2 * Real.pi) ^ 1 := (pow_one _).symm
          _ ≤ (2 * Real.pi) ^ n := pow_le_pow_right₀ (by linarith) hn
    _ = (2 * Real.pi * Lattice.jp k) ^ n := (mul_pow _ _ _).symm

lemma sobolev_cosMode (n : ℕ) (hn : 1 ≤ n) (k : Lattice d) :
    MemSobolev (n : ℝ) (Torus.cosMode k) ∧
      sobolevNorm (n : ℝ) (Torus.cosMode k) ≤ (2 * Real.pi * Lattice.jp k) ^ n := by
  refine sobolev_two_modes n hn k (1 / 2) (1 / 2) (by simp) (by simp) _ (Torus.continuous_cosMode k) ?_
  intro x
  have := Complex.re_eq_add_conj (Torus.mode k x)
  simp only [Torus.cosMode]
  rw [this, Torus.mode_neg]
  ring

lemma sobolev_sinMode (n : ℕ) (hn : 1 ≤ n) (k : Lattice d) :
    MemSobolev (n : ℝ) (Torus.sinMode k) ∧
      sobolevNorm (n : ℝ) (Torus.sinMode k) ≤ (2 * Real.pi * Lattice.jp k) ^ n := by
  refine sobolev_two_modes n hn k (1 / (2 * Complex.I)) (-(1 / (2 * Complex.I))) (by simp)
    (by simp) _ (Torus.continuous_sinMode k) ?_
  intro x
  have := Complex.im_eq_sub_conj (Torus.mode k x)
  simp only [Torus.sinMode]
  rw [this, Torus.mode_neg]
  ring

lemma tendsto_reflect {t : ℝ} {f : ℝ → ℝ} {x₀ : Set.Icc (0 : ℝ) t}
    (h : Tendsto f (𝓝[Set.Icc 0 t] (t - (x₀ : ℝ))) (𝓝 0)) :
    Tendsto (fun x : Set.Icc (0 : ℝ) t => f (t - (x : ℝ))) (𝓝 x₀) (𝓝 0) :=
  h.comp (tendsto_nhdsWithin_iff.2 ⟨((continuous_const.sub continuous_subtype_val).tendsto x₀),
    Filter.Eventually.of_forall fun x => ⟨by linarith [x.2.2], by linarith [x.2.1]⟩⟩)

lemma exists_mid {m : ℕ} (hm : mStar d ≤ m) :
    ∃ m'' : ℝ, (d : ℝ) / 2 + 2 < m'' ∧ m'' < m := by
  have h1 : (d : ℝ) / 2 + 2 < (mStar d : ℝ) := by
    unfold mStar
    push_cast
    have := Nat.lt_floor_add_one ((d : ℝ) / 2)
    linarith
  have h2 : (mStar d : ℝ) ≤ m := by exact_mod_cast hm
  exact ⟨((d : ℝ) / 2 + 2 + m) / 2, by linarith, by linarith⟩

lemma three_le_mStar (d : ℕ) : 3 ≤ mStar d := by
  unfold mStar; omega

lemma one_le_of_mStar {m : ℕ} (hm : mStar d ≤ m) : 3 ≤ m :=
  (three_le_mStar d).trans hm

end HRS.PDE.ClassicalPart
