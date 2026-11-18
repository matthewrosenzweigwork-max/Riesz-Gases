import HRS.MS.CanThmAux1

/-!
# CAN2 (part 2): the one-step Fubini decomposition and Jensen lower bound for the canonical ensemble

Abstract setting (`Can2Setting`): `g ≥ 0` measurable, `w = exp(-β V)` integrable with `∫ g(x - y) w(x) dx ≤ B Λ`
for all `y` (`Λ = ∫ w`).  For the Hamiltonian `H_c(Y) = ∑ V(Y_i) + c ∑_{i<j} g(Y_i - Y_j)` on `n` particles and
`W_n(c) = ∫⁻ exp(-β H_c)`, we prove

* `can2_lintegral_cons`: Fubini for `(ℝ^d)^{n+1} ≃ ℝ^d × (ℝ^d)^n`,
* `can2_W_succ_ge` : `W_{n+1}(c) ≥ Λ e^{-βB} W_n(c)` when `c n ≤ 1` (Jensen, in the tangent-line form
  `e^{-u} ≥ e^{-m}(1 + m - u)`),
* `can2_one_upper`, `can2_two_upper`: `∫⁻ φ(X_0) e^{-βH} ≤ (∫⁻ φ w) W_n` and the two-particle analogue,
* `W_n ∈ (0, ∞)`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Can2

open HRS.Whole

variable {d : ℕ}

/-- `H_c(Y) = ∑ V(Y_i) + c ∑_{i<j} g(Y_i - Y_j)`; `canonicalHamiltonian` is the case `c = 1/N`. -/
def can2_H (g V : Euc d → ℝ) (c : ℝ) {n : ℕ} (Y : Fin n → Euc d) : ℝ :=
  ∑ i, V (Y i) + c * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (Y i - Y j)

lemma can2_H_eq_canonical (g V : Euc d → ℝ) {N : ℕ} (X : Fin N → Euc d) :
    HRS.Whole.canonicalHamiltonian g V X = can2_H g V (1 / (N : ℝ)) X := rfl

lemma can2_H_succ (g V : Euc d → ℝ) (c : ℝ) {n : ℕ} (X : Fin (n + 1) → Euc d) :
    can2_H g V c X = V (X 0) + c * ∑ j : Fin n, g (X 0 - X j.succ) + can2_H g V c (Fin.tail X) := by
  unfold can2_H
  simp only [Finset.sum_filter, Fin.sum_univ_succ, Fin.tail]
  simp [Fin.succ_lt_succ_iff, Fin.succ_pos]
  ring

/-- `∫⁻` over `(ℝ^d)^{n+1}` split as `ℝ^d × (ℝ^d)^n` (first coordinate and tail). -/
lemma can2_lintegral_cons (n : ℕ) (F : Euc d × (Fin n → Euc d) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X : Fin (n + 1) → Euc d, F (X 0, Fin.tail X)
      = ∫⁻ x : Euc d, ∫⁻ Y : Fin n → Euc d, F (x, Y) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Euc d) 0).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) F
  have e : ∀ X : Fin (n + 1) → Euc d,
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Euc d) 0) X = (X 0, Fin.tail X) := by
    intro X
    simp [MeasurableEquiv.piFinSuccAbove_apply]
  simp only [e] at h
  rw [h, Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable]

/-- Weight `exp(-β H_c)` as an extended nonnegative number. -/
def can2_wgt (g V : Euc d → ℝ) (β c : ℝ) {n : ℕ} (Y : Fin n → Euc d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * can2_H g V c Y))

/-- The interaction factor of a particle at `x` with the configuration `Y`. -/
def can2_E (g : Euc d → ℝ) (β c : ℝ) {n : ℕ} (x : Euc d) (Y : Fin n → Euc d) : ℝ :=
  Real.exp (-β * (c * ∑ j, g (x - Y j)))

/-- Total mass `W_n(c)`. -/
def can2_W (g V : Euc d → ℝ) (β c : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ Y : Fin n → Euc d, can2_wgt g V β c Y

lemma can2_wgt_succ (g V : Euc d → ℝ) (β c : ℝ) {n : ℕ} (X : Fin (n + 1) → Euc d) :
    can2_wgt g V β c X = ENNReal.ofReal (Real.exp (-β * V (X 0)) * can2_E g β c (X 0) (Fin.tail X))
      * can2_wgt g V β c (Fin.tail X) := by
  unfold can2_wgt can2_E
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add, can2_H_succ]
  congr 2
  simp only [Fin.tail]
  ring


/-! ### Setting and measurability -/

/-- Standing hypotheses of the abstract canonical-ensemble estimate. -/
structure Can2Setting (g V : Euc d → ℝ) (β B : ℝ) : Prop where
  β_pos : 0 < β
  g_meas : Measurable g
  g_nonneg : ∀ x, 0 ≤ g x
  V_meas : Measurable V
  w_int : Integrable (fun x : Euc d => Real.exp (-β * V x))
  B_nonneg : 0 ≤ B
  conv : ∀ y : Euc d, Integrable (fun x => g (x - y) * Real.exp (-β * V x)) ∧
    ∫ x, g (x - y) * Real.exp (-β * V x) ≤ B * ∫ x, Real.exp (-β * V x)

/-- `Λ = ∫ exp(-β V)`. -/
def can2_L (V : Euc d → ℝ) (β : ℝ) : ℝ := ∫ x : Euc d, Real.exp (-β * V x)

section Setting

variable {g V : Euc d → ℝ} {β B : ℝ}

lemma can2_L_pos (hS : Can2Setting g V β B) : 0 < can2_L V β := by
  unfold can2_L
  refine (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hS.w_int).2 ?_
  have : Function.support (fun x : Euc d => Real.exp (-β * V x)) = Set.univ := by
    ext x; simp [(Real.exp_pos _).ne']
  rw [this]
  exact Measure.measure_univ_pos.2 (NeZero.ne _)

lemma can2_H_meas (hS : Can2Setting g V β B) (c : ℝ) (n : ℕ) :
    Measurable (fun Y : Fin n → Euc d => can2_H g V c Y) := by
  unfold can2_H
  refine (Finset.measurable_sum _ fun i _ => hS.V_meas.comp (measurable_pi_apply i)).add
    (Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      hS.g_meas.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))) _)

lemma can2_wgt_meas (hS : Can2Setting g V β B) (c : ℝ) (n : ℕ) :
    Measurable (fun Y : Fin n → Euc d => can2_wgt g V β c Y) := by
  unfold can2_wgt
  exact (Real.measurable_exp.comp ((can2_H_meas hS c n).const_mul _)).ennreal_ofReal

lemma can2_E_meas (hS : Can2Setting g V β B) (c : ℝ) (n : ℕ) :
    Measurable (fun p : Euc d × (Fin n → Euc d) => can2_E g β c p.1 p.2) := by
  unfold can2_E
  refine Real.measurable_exp.comp (Measurable.const_mul (Measurable.const_mul
    (Finset.measurable_sum _ fun j _ => hS.g_meas.comp
      (measurable_fst.sub ((measurable_pi_apply j).comp measurable_snd))) _) _)

lemma can2_E_meas_x (hS : Can2Setting g V β B) (c : ℝ) {n : ℕ} (Y : Fin n → Euc d) :
    Measurable (fun x : Euc d => can2_E g β c x Y) := by
  unfold can2_E
  exact Real.measurable_exp.comp (Measurable.const_mul (Measurable.const_mul
    (Finset.measurable_sum _ fun j _ => hS.g_meas.comp (measurable_id.sub measurable_const)) _) _)

lemma can2_E_pos (c : ℝ) {n : ℕ} (x : Euc d) (Y : Fin n → Euc d) : 0 < can2_E g β c x Y :=
  Real.exp_pos _

lemma can2_E_le_one (hS : Can2Setting g V β B) {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (x : Euc d)
    (Y : Fin n → Euc d) : can2_E g β c x Y ≤ 1 := by
  unfold can2_E
  rw [Real.exp_le_one_iff]
  have : 0 ≤ ∑ j, g (x - Y j) := Finset.sum_nonneg fun j _ => hS.g_nonneg _
  have := hS.β_pos
  nlinarith [mul_nonneg hc ‹0 ≤ ∑ j, g (x - Y j)›]

/-- Jensen (tangent line form): `∫ w e^{-u} ≥ Λ e^{-βB}` uniformly in the other particles. -/
lemma can2_jensen (hS : Can2Setting g V β B) {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hcn : c * n ≤ 1)
    (Y : Fin n → Euc d) :
    ENNReal.ofReal (can2_L V β * Real.exp (-(β * B))) ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp (-β * V x) * can2_E g β c x Y) := by
  have hβ := hS.β_pos
  set w : Euc d → ℝ := fun x => Real.exp (-β * V x) with hw
  have hwm : Measurable w := Real.measurable_exp.comp (hS.V_meas.const_mul _)
  set u : Euc d → ℝ := fun x => β * (c * ∑ j, g (x - Y j)) with hu
  have hu0 : ∀ x, 0 ≤ u x := fun x => mul_nonneg hβ.le (mul_nonneg hc
    (Finset.sum_nonneg fun j _ => hS.g_nonneg _))
  have hEu : ∀ x, can2_E g β c x Y = Real.exp (-u x) := fun x => by
    unfold can2_E; rw [hu]; simp only; congr 1; ring
  have hgj : ∀ j, Integrable (fun x => g (x - Y j) * w x) := fun j => (hS.conv (Y j)).1
  have hwu_eq : ∀ x, w x * u x = β * c * ∑ j, (g (x - Y j) * w x) := fun x => by
    rw [hu]; simp only; rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hwu_int : Integrable (fun x => w x * u x) := by
    have := (integrable_finsetSum _ fun j (_ : j ∈ Finset.univ) => hgj j).const_mul (β * c)
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [hwu_eq]
  have hwE_meas : Measurable (fun x => w x * can2_E g β c x Y) := by
    exact hwm.mul (can2_E_meas_x hS c Y)
  have hwE_int : Integrable (fun x => w x * can2_E g β c x Y) := by
    refine Integrable.mono' hS.w_int hwE_meas.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have h1 := can2_E_pos (g := g) (β := β) c x Y
    have h2 := can2_E_le_one hS hc x Y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h1.le)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le h2
  set m : ℝ := β * B with hm
  have hpt : ∀ x, Real.exp (-m) * (w x * (1 + m) - w x * u x) ≤ w x * can2_E g β c x Y := by
    intro x
    have h1 := Real.add_one_le_exp (m - u x)
    have h2 : Real.exp (-u x) = Real.exp (-m) * Real.exp (m - u x) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hEu, h2]
    have hwpos : 0 ≤ w x := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hwpos (Real.exp_pos (-m)).le)
    nlinarith [this]
  have hlow_int : Integrable (fun x => Real.exp (-m) * (w x * (1 + m) - w x * u x)) :=
    ((hS.w_int.mul_const (1 + m)).sub hwu_int).const_mul _
  have hI : ∫ x, Real.exp (-m) * (w x * (1 + m) - w x * u x) ≤ ∫ x, w x * can2_E g β c x Y :=
    integral_mono hlow_int hwE_int hpt
  have hwu_le : ∫ x, w x * u x ≤ m * can2_L V β := by
    have e1 : ∫ x, w x * u x = β * c * ∑ j, ∫ x, g (x - Y j) * w x := by
      simp only [hwu_eq]
      rw [integral_const_mul, integral_finsetSum _ fun j _ => hgj j]
    rw [e1]
    have h3 : ∑ j, ∫ x, g (x - Y j) * w x ≤ ∑ _j : Fin n, B * can2_L V β :=
      Finset.sum_le_sum fun j _ => (hS.conv (Y j)).2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    have hL := can2_L_pos hS
    have hBL : 0 ≤ B * can2_L V β := mul_nonneg hS.B_nonneg hL.le
    have h4 : β * c * ∑ j, ∫ x, g (x - Y j) * w x ≤ β * c * ((n : ℝ) * (B * can2_L V β)) :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hβ.le hc)
    have h5 : β * c * ((n : ℝ) * (B * can2_L V β)) ≤ m * can2_L V β := by
      have : β * c * ((n : ℝ) * (B * can2_L V β)) = (c * n) * (β * (B * can2_L V β)) := by ring
      rw [this, hm]
      have h6 : 0 ≤ β * (B * can2_L V β) := mul_nonneg hβ.le hBL
      nlinarith [mul_le_mul_of_nonneg_right hcn h6]
    exact h4.trans h5
  have hcalc : Real.exp (-m) * can2_L V β ≤ ∫ x, w x * can2_E g β c x Y := by
    refine le_trans ?_ hI
    rw [integral_const_mul, integral_sub (hS.w_int.mul_const (1 + m)) hwu_int,
      integral_mul_const]
    have : can2_L V β = ∫ x, w x := rfl
    rw [← this]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    nlinarith [hwu_le]
  calc ENNReal.ofReal (can2_L V β * Real.exp (-(β * B)))
      ≤ ENNReal.ofReal (∫ x, w x * can2_E g β c x Y) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_comm]; exact hcalc
    _ = ∫⁻ x, ENNReal.ofReal (w x * can2_E g β c x Y) :=
        ofReal_integral_eq_lintegral_ofReal hwE_int
          (ae_of_all _ fun x => mul_nonneg (Real.exp_pos _).le (can2_E_pos c x Y).le)

/-! ### Recursions for the total masses -/

lemma can2_wgt_le (hS : Can2Setting g V β B) {c : ℝ} (hc : 0 ≤ c) {n : ℕ}
    (X : Fin (n + 1) → Euc d) :
    can2_wgt g V β c X ≤ ENNReal.ofReal (Real.exp (-β * V (X 0))) * can2_wgt g V β c (Fin.tail X) := by
  rw [can2_wgt_succ]
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  exact mul_le_of_le_one_right (Real.exp_pos _).le (can2_E_le_one hS hc _ _)

lemma can2_F_meas (hS : Can2Setting g V β B) (c : ℝ) (n : ℕ) :
    Measurable (fun p : Euc d × (Fin n → Euc d) =>
      ENNReal.ofReal (Real.exp (-β * V p.1) * can2_E g β c p.1 p.2) * can2_wgt g V β c p.2) := by
  refine (Measurable.ennreal_ofReal ((Real.measurable_exp.comp
    (hS.V_meas.comp measurable_fst |>.const_mul _)).mul (can2_E_meas hS c n))).mul ?_
  exact (can2_wgt_meas hS c n).comp measurable_snd

/-- One-step lower bound for the total masses. -/
lemma can2_W_succ_ge (hS : Can2Setting g V β B) {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hcn : c * n ≤ 1) :
    ENNReal.ofReal (can2_L V β * Real.exp (-(β * B))) * can2_W g V β c n ≤
      can2_W g V β c (n + 1) := by
  unfold can2_W
  have h1 : ∫⁻ X : Fin (n + 1) → Euc d, can2_wgt g V β c X =
      ∫⁻ X : Fin (n + 1) → Euc d,
        (fun p : Euc d × (Fin n → Euc d) =>
          ENNReal.ofReal (Real.exp (-β * V p.1) * can2_E g β c p.1 p.2) * can2_wgt g V β c p.2)
          (X 0, Fin.tail X) := by
    refine lintegral_congr fun X => ?_
    exact can2_wgt_succ g V β c X
  rw [h1, can2_lintegral_cons n _ (can2_F_meas hS c n)]
  rw [lintegral_lintegral_swap (can2_F_meas hS c n).aemeasurable]
  rw [mul_comm, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun Y => ?_
  simp only
  rw [lintegral_mul_const _ (by
    exact (Measurable.ennreal_ofReal ((Real.measurable_exp.comp
      (hS.V_meas.const_mul _)).mul (can2_E_meas_x hS c Y))))]
  rw [mul_comm]
  exact mul_le_mul_left (can2_jensen hS hc hcn Y) _


/-- `W_0 = 1`. -/
lemma can2_W_zero (g V : Euc d → ℝ) (β c : ℝ) : can2_W g V β c 0 = 1 := by
  unfold can2_W can2_wgt can2_H
  have h : (volume : Measure (Fin 0 → Euc d)) = Measure.dirac default :=
    Measure.pi_of_empty (fun _ : Fin 0 => (volume : Measure (Euc d))) default
  simp [h]

/-- One-particle numerator bound. -/
lemma can2_one_upper (hS : Can2Setting g V β B) {c : ℝ} (hc : 0 ≤ c) (n : ℕ)
    {φ : Euc d → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ X : Fin (n + 1) → Euc d, φ (X 0) * can2_wgt g V β c X ≤
      (∫⁻ x, φ x * ENNReal.ofReal (Real.exp (-β * V x))) * can2_W g V β c n := by
  have hw : Measurable fun x : Euc d => ENNReal.ofReal (Real.exp (-β * V x)) :=
    (Real.measurable_exp.comp (hS.V_meas.const_mul _)).ennreal_ofReal
  have h1 : ∫⁻ X : Fin (n + 1) → Euc d, φ (X 0) * can2_wgt g V β c X ≤
      ∫⁻ X : Fin (n + 1) → Euc d,
        (fun p : Euc d × (Fin n → Euc d) =>
          φ p.1 * ENNReal.ofReal (Real.exp (-β * V p.1)) * can2_wgt g V β c p.2)
          (X 0, Fin.tail X) := by
    refine lintegral_mono fun X => ?_
    simp only
    calc φ (X 0) * can2_wgt g V β c X
        ≤ φ (X 0) * (ENNReal.ofReal (Real.exp (-β * V (X 0))) * can2_wgt g V β c (Fin.tail X)) :=
          mul_le_mul_right (can2_wgt_le hS hc X) _
      _ = _ := by ring
  refine h1.trans (le_of_eq ((can2_lintegral_cons n
    (fun p : Euc d × (Fin n → Euc d) =>
      φ p.1 * ENNReal.ofReal (Real.exp (-β * V p.1)) * can2_wgt g V β c p.2)
    (((hφ.comp measurable_fst).mul (hw.comp measurable_fst)).mul
      ((can2_wgt_meas hS c n).comp measurable_snd))).trans ?_))
  unfold can2_W
  have hm : Measurable fun x : Euc d => φ x * ENNReal.ofReal (Real.exp (-β * V x)) := hφ.mul hw
  rw [← lintegral_mul_const _ hm]
  refine lintegral_congr fun x => ?_
  simp only
  rw [lintegral_const_mul _ (can2_wgt_meas hS c n)]


lemma can2_lintegral_w (hS : Can2Setting g V β B) :
    ∫⁻ x : Euc d, ENNReal.ofReal (Real.exp (-β * V x)) = ENNReal.ofReal (can2_L V β) := by
  unfold can2_L
  rw [ofReal_integral_eq_lintegral_ofReal hS.w_int (ae_of_all _ fun x => (Real.exp_pos _).le)]

lemma can2_W_lt_top (hS : Can2Setting g V β B) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    can2_W g V β c n < ⊤ := by
  induction n with
  | zero => rw [can2_W_zero]; exact ENNReal.one_lt_top
  | succ n ih =>
    have h := can2_one_upper hS hc n (φ := fun _ => 1) measurable_const
    simp only [one_mul] at h
    rw [can2_lintegral_w hS] at h
    exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ih)

lemma can2_W_pos (hS : Can2Setting g V β B) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (hcn : c * n ≤ 1) :
    0 < can2_W g V β c n := by
  induction n with
  | zero => rw [can2_W_zero]; exact one_pos
  | succ n ih =>
    have hcn' : c * (n : ℝ) ≤ 1 := by
      push_cast at hcn; nlinarith
    have h := can2_W_succ_ge hS hc hcn'
    refine lt_of_lt_of_le ?_ h
    refine ENNReal.mul_pos ?_ (ih hcn').ne'
    exact (ENNReal.ofReal_pos.2 (mul_pos (can2_L_pos hS) (Real.exp_pos _))).ne'

/-- Two-particle numerator bound. -/
lemma can2_two_upper (hS : Can2Setting g V β B) {c : ℝ} (hc : 0 ≤ c) (n : ℕ)
    {ψ : Euc d × Euc d → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ X : Fin (n + 2) → Euc d, ψ (X 0, X 1) * can2_wgt g V β c X ≤
      (∫⁻ x, ENNReal.ofReal (Real.exp (-β * V x)) *
        ∫⁻ y, ψ (x, y) * ENNReal.ofReal (Real.exp (-β * V y))) * can2_W g V β c n := by
  have hw : Measurable fun x : Euc d => ENNReal.ofReal (Real.exp (-β * V x)) :=
    (Real.measurable_exp.comp (hS.V_meas.const_mul _)).ennreal_ofReal
  have hψ' : ∀ x : Euc d, Measurable fun y => ψ (x, y) := fun x =>
    hψ.comp (measurable_const.prodMk measurable_id)
  have hF : Measurable (fun p : Euc d × (Fin (n + 1) → Euc d) =>
      ENNReal.ofReal (Real.exp (-β * V p.1)) * (ψ (p.1, p.2 0) * can2_wgt g V β c p.2)) :=
    (hw.comp measurable_fst).mul ((hψ.comp (measurable_fst.prodMk
      ((measurable_pi_apply 0).comp measurable_snd))).mul
      ((can2_wgt_meas hS c (n + 1)).comp measurable_snd))
  have h1 : ∫⁻ X : Fin (n + 2) → Euc d, ψ (X 0, X 1) * can2_wgt g V β c X ≤
      ∫⁻ X : Fin (n + 2) → Euc d,
        (fun p : Euc d × (Fin (n + 1) → Euc d) =>
          ENNReal.ofReal (Real.exp (-β * V p.1)) * (ψ (p.1, p.2 0) * can2_wgt g V β c p.2))
          (X 0, Fin.tail X) := by
    refine lintegral_mono fun X => ?_
    simp only
    have e : Fin.tail X 0 = X 1 := by simp [Fin.tail]
    rw [e]
    calc ψ (X 0, X 1) * can2_wgt g V β c X
        ≤ ψ (X 0, X 1) * (ENNReal.ofReal (Real.exp (-β * V (X 0))) * can2_wgt g V β c (Fin.tail X)) :=
          mul_le_mul_right (can2_wgt_le hS hc X) _
      _ = _ := by ring
  refine h1.trans ((le_of_eq (can2_lintegral_cons (n + 1) _ hF)).trans ?_)
  simp only
  have hmeas2 : Measurable fun x : Euc d => ENNReal.ofReal (Real.exp (-β * V x)) *
      ∫⁻ y, ψ (x, y) * ENNReal.ofReal (Real.exp (-β * V y)) :=
    hw.mul (Measurable.lintegral_prod_right' (f := fun p : Euc d × Euc d =>
      ψ p * ENNReal.ofReal (Real.exp (-β * V p.2))) (hψ.mul (hw.comp measurable_snd)))
  rw [← lintegral_mul_const _ hmeas2]
  refine lintegral_mono fun x => ?_
  have hY : Measurable fun Y : Fin (n + 1) → Euc d => ψ (x, Y 0) * can2_wgt g V β c Y :=
    ((hψ' x).comp (measurable_pi_apply 0)).mul (can2_wgt_meas hS c (n + 1))
  simp only
  rw [lintegral_const_mul _ hY, mul_assoc]
  exact mul_le_mul_right (can2_one_upper hS hc n (hψ' x)) _


/-! ### Marginals of the canonical Gibbs law -/

lemma can2_ennreal (W Wn lam I : ℝ≥0∞) (h : lam * Wn ≤ W) (h0 : Wn ≠ 0) (htop : Wn ≠ ⊤) :
    W⁻¹ * (I * Wn) ≤ lam⁻¹ * I := by
  have h1 : W⁻¹ ≤ (lam * Wn)⁻¹ := ENNReal.inv_le_inv.2 h
  have h2 : (lam * Wn)⁻¹ = lam⁻¹ * Wn⁻¹ := ENNReal.mul_inv (Or.inr htop) (Or.inr h0)
  calc W⁻¹ * (I * Wn) ≤ (lam⁻¹ * Wn⁻¹) * (I * Wn) := by
        rw [← h2]; exact mul_le_mul_left h1 _
    _ = lam⁻¹ * I * (Wn⁻¹ * Wn) := by ring
    _ = lam⁻¹ * I := by rw [ENNReal.inv_mul_cancel h0 htop, mul_one]

lemma can2_partition (hS : Can2Setting g V β B) (N : ℕ) :
    ENNReal.ofReal (HRS.Whole.canonicalPartition g V N β) = can2_W g V β (1 / (N : ℝ)) N := by
  have hc : 0 ≤ 1 / (N : ℝ) := by positivity
  unfold HRS.Whole.canonicalPartition
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun X => (Real.exp_pos _).le) ?_]
  · have h := can2_W_lt_top hS hc N
    have e : ∫⁻ a : EucConfig d N,
        ENNReal.ofReal (Real.exp (-β * HRS.Whole.canonicalHamiltonian g V a)) =
        can2_W g V β (1 / (N : ℝ)) N := rfl
    rw [e, ENNReal.ofReal_toReal h.ne]
  · exact (Real.measurable_exp.comp ((can2_H_meas hS (1 / (N : ℝ)) N).const_mul (-β))).aestronglyMeasurable


lemma can2_canonical_apply (hS : Can2Setting g V β B) (N : ℕ) {A : Set (Fin N → Euc d)}
    (hA : MeasurableSet A) :
    HRS.Whole.canonicalGibbs g V N β A = (can2_W g V β (1 / (N : ℝ)) N)⁻¹ *
      ∫⁻ X, A.indicator (fun _ => (1 : ℝ≥0∞)) X * can2_wgt g V β (1 / (N : ℝ)) X := by
  unfold HRS.Whole.canonicalGibbs
  rw [Measure.smul_apply, withDensity_apply _ hA, ← can2_partition hS N, ← lintegral_indicator hA,
    smul_eq_mul]
  congr 1
  refine lintegral_congr fun X => ?_
  by_cases h : X ∈ A <;> simp [h, can2_wgt, can2_H_eq_canonical]

lemma can2_lam_pos (hS : Can2Setting g V β B) :
    0 < can2_L V β * Real.exp (-(β * B)) := mul_pos (can2_L_pos hS) (Real.exp_pos _)

/-- First marginal of the canonical Gibbs law, `N = n + 1`. -/
lemma can2_first_le (hS : Can2Setting g V β B) (n : ℕ) {A : Set (Euc d)} (hA : MeasurableSet A) :
    ((HRS.Whole.canonicalGibbs g V (n + 1) β).map (fun X : Fin (n + 1) → Euc d => X 0)) A ≤
      (ENNReal.ofReal (can2_L V β * Real.exp (-(β * B))))⁻¹ *
        ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x * ENNReal.ofReal (Real.exp (-β * V x)) := by
  have hc : 0 ≤ 1 / (((n + 1 : ℕ)) : ℝ) := by positivity
  have hcn : 1 / (((n + 1 : ℕ)) : ℝ) * (n : ℝ) ≤ 1 := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]; push_cast; linarith
  have hpre : MeasurableSet ((fun X : Fin (n + 1) → Euc d => X 0) ⁻¹' A) :=
    measurable_pi_apply 0 hA
  rw [Measure.map_apply (measurable_pi_apply 0) hA, can2_canonical_apply hS (n + 1) hpre]
  have hind : ∀ X : Fin (n + 1) → Euc d,
      ((fun X : Fin (n + 1) → Euc d => X 0) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) X =
        A.indicator (fun _ => (1 : ℝ≥0∞)) (X 0) := fun X => by
    by_cases h : X 0 ∈ A <;> simp [h]
  simp only [hind]
  refine le_trans (mul_le_mul_right (can2_one_upper hS hc n (φ :=
    A.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hA)) _) ?_
  exact can2_ennreal _ _ _ _ (can2_W_succ_ge hS hc hcn) (can2_W_pos hS hc n hcn).ne'
    (can2_W_lt_top hS hc n).ne

/-- Second marginal of the canonical Gibbs law, `N = n + 2`. -/
lemma can2_second_le (hS : Can2Setting g V β B) (n : ℕ) {A : Set (Euc d × Euc d)}
    (hA : MeasurableSet A) :
    ((HRS.Whole.canonicalGibbs g V (n + 2) β).map
        (fun X : Fin (n + 2) → Euc d => (X 0, X 1))) A ≤
      (ENNReal.ofReal (can2_L V β * Real.exp (-(β * B))) *
        ENNReal.ofReal (can2_L V β * Real.exp (-(β * B))))⁻¹ *
        ∫⁻ x, ENNReal.ofReal (Real.exp (-β * V x)) *
          ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) * ENNReal.ofReal (Real.exp (-β * V y)) := by
  have hc : 0 ≤ 1 / (((n + 2 : ℕ)) : ℝ) := by positivity
  have hcn : 1 / (((n + 2 : ℕ)) : ℝ) * (n : ℝ) ≤ 1 := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]; push_cast; linarith
  have hcn1 : 1 / (((n + 2 : ℕ)) : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]; push_cast; linarith
  have hm : Measurable (fun X : Fin (n + 2) → Euc d => (X 0, X 1)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hpre : MeasurableSet ((fun X : Fin (n + 2) → Euc d => (X 0, X 1)) ⁻¹' A) := hm hA
  rw [Measure.map_apply hm hA, can2_canonical_apply hS (n + 2) hpre]
  have hind : ∀ X : Fin (n + 2) → Euc d,
      ((fun X : Fin (n + 2) → Euc d => (X 0, X 1)) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) X =
        A.indicator (fun _ => (1 : ℝ≥0∞)) (X 0, X 1) := fun X => by
    by_cases h : (X 0, X 1) ∈ A <;> simp [h]
  simp only [hind]
  refine le_trans (mul_le_mul_right (can2_two_upper hS hc n (ψ :=
    A.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hA)) _) ?_
  refine can2_ennreal _ _ _ _ ?_ (can2_W_pos hS hc n hcn).ne' (can2_W_lt_top hS hc n).ne
  calc ENNReal.ofReal (can2_L V β * Real.exp (-(β * B))) *
        ENNReal.ofReal (can2_L V β * Real.exp (-(β * B))) * can2_W g V β (1 / ((n + 2 : ℕ) : ℝ)) n
      = ENNReal.ofReal (can2_L V β * Real.exp (-(β * B))) *
        (ENNReal.ofReal (can2_L V β * Real.exp (-(β * B))) * can2_W g V β (1 / ((n + 2 : ℕ) : ℝ)) n) := by
        ring
    _ ≤ ENNReal.ofReal (can2_L V β * Real.exp (-(β * B))) *
        can2_W g V β (1 / ((n + 2 : ℕ) : ℝ)) (n + 1) :=
        mul_le_mul_right (can2_W_succ_ge hS hc hcn) _
    _ ≤ can2_W g V β (1 / ((n + 2 : ℕ) : ℝ)) (n + 2) := can2_W_succ_ge hS hc hcn1


lemma can2_withDensityReal_apply {ρ : Euc d → ℝ} {A : Set (Euc d)} (hA : MeasurableSet A) :
    HRS.Whole.withDensityReal ρ A =
      ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x * ENNReal.ofReal (ρ x) := by
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply _ hA, ← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  by_cases h : x ∈ A <;> simp [h]

/-- First marginal domination by `K ρ dx`. -/
lemma can2_first_final (hS : Can2Setting g V β B) (n : ℕ) {ρ : Euc d → ℝ}
    {K : ℝ} (hK : 0 ≤ K)
    (hdom : ∀ x, (can2_L V β * Real.exp (-(β * B)))⁻¹ * Real.exp (-β * V x) ≤ K * ρ x) :
    (HRS.Whole.canonicalGibbs g V (n + 1) β).map (fun X : Fin (n + 1) → Euc d => X 0) ≤
      ENNReal.ofReal K • HRS.Whole.withDensityReal ρ := by
  refine Measure.le_iff.2 fun A hA => ?_
  refine (can2_first_le hS n hA).trans ?_
  rw [← ENNReal.ofReal_inv_of_pos (can2_lam_pos hS), Measure.smul_apply, can2_withDensityReal_apply hA,
    smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  by_cases h : x ∈ A
  · simp only [Set.indicator_of_mem h, one_mul]
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 (can2_lam_pos hS).le), ← ENNReal.ofReal_mul hK]
    exact ENNReal.ofReal_le_ofReal (hdom x)
  · simp [h]

/-- Second marginal domination by `K² ρ ⊗ ρ`. -/
lemma can2_second_final (hS : Can2Setting g V β B) (n : ℕ) {ρ : Euc d → ℝ}
    (hρm : Measurable ρ) {K : ℝ} (hK : 0 ≤ K)
    (hdom : ∀ x, (can2_L V β * Real.exp (-(β * B)))⁻¹ * Real.exp (-β * V x) ≤ K * ρ x) :
    (HRS.Whole.canonicalGibbs g V (n + 2) β).map (fun X : Fin (n + 2) → Euc d => (X 0, X 1)) ≤
      (ENNReal.ofReal K * ENNReal.ofReal K) •
        (HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ) := by
  refine Measure.le_iff.2 fun A hA => (can2_second_le hS n hA).trans ?_
  have hlam := can2_lam_pos hS
  generalize can2_L V β * Real.exp (-(β * B)) = Q at hdom hlam ⊢
  have hQ0 : ENNReal.ofReal Q ≠ 0 := (ENNReal.ofReal_pos.2 hlam).ne'
  have hinv : (ENNReal.ofReal Q * ENNReal.ofReal Q)⁻¹ =
      ENNReal.ofReal Q⁻¹ * ENNReal.ofReal Q⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hQ0) (Or.inl ENNReal.ofReal_ne_top),
      ENNReal.ofReal_inv_of_pos hlam]
  rw [hinv]
  have hw : Measurable fun x : Euc d => ENNReal.ofReal (Real.exp (-β * V x)) :=
    (Real.measurable_exp.comp (hS.V_meas.const_mul _)).ennreal_ofReal
  have hρ' : Measurable fun x : Euc d => ENNReal.ofReal (ρ x) := hρm.ennreal_ofReal
  have hI : Measurable fun p : Euc d × Euc d => A.indicator (fun _ => (1 : ℝ≥0∞)) p :=
    measurable_const.indicator hA
  -- the right-hand side as an iterated integral
  have hrhs : (HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ) A =
      ∫⁻ x, ENNReal.ofReal (ρ x) *
        ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) * ENNReal.ofReal (ρ y) := by
    have : SFinite (HRS.Whole.withDensityReal ρ) := by
      unfold HRS.Whole.withDensityReal; infer_instance
    rw [Measure.prod_apply hA]
    have h1 : ∀ x : Euc d, HRS.Whole.withDensityReal ρ (Prod.mk x ⁻¹' A) =
        ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) * ENNReal.ofReal (ρ y) := fun x => by
      rw [can2_withDensityReal_apply (measurable_prodMk_left hA)]
      refine lintegral_congr fun y => ?_
      by_cases h : (x, y) ∈ A <;> simp [h]
    simp only [h1]
    unfold HRS.Whole.withDensityReal
    rw [lintegral_withDensity_eq_lintegral_mul _ hρ' (Measurable.lintegral_prod_right'
      (f := fun p : Euc d × Euc d => A.indicator (fun _ => (1 : ℝ≥0∞)) p * ENNReal.ofReal (ρ p.2))
      (hI.mul (hρ'.comp measurable_snd)))]
    rfl
  rw [Measure.smul_apply, smul_eq_mul, hrhs]
  have hlhs : ENNReal.ofReal Q⁻¹ * ENNReal.ofReal Q⁻¹ *
      ∫⁻ x, ENNReal.ofReal (Real.exp (-β * V x)) *
        ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) * ENNReal.ofReal (Real.exp (-β * V y)) =
      ∫⁻ x, (ENNReal.ofReal Q⁻¹ * ENNReal.ofReal (Real.exp (-β * V x))) *
        ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) *
          (ENNReal.ofReal Q⁻¹ * ENNReal.ofReal (Real.exp (-β * V y))) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    refine lintegral_congr fun x => ?_
    have : ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) *
          (ENNReal.ofReal Q⁻¹ * ENNReal.ofReal (Real.exp (-β * V y))) =
        ENNReal.ofReal Q⁻¹ * ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) *
          ENNReal.ofReal (Real.exp (-β * V y)) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun y => ?_
      ring
    rw [this]
    ring
  have hrhs2 : ENNReal.ofReal K * ENNReal.ofReal K *
      ∫⁻ x, ENNReal.ofReal (ρ x) *
        ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) * ENNReal.ofReal (ρ y) =
      ∫⁻ x, (ENNReal.ofReal K * ENNReal.ofReal (ρ x)) *
        ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) *
          (ENNReal.ofReal K * ENNReal.ofReal (ρ y)) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    refine lintegral_congr fun x => ?_
    have : ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) *
          (ENNReal.ofReal K * ENNReal.ofReal (ρ y)) =
        ENNReal.ofReal K * ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) *
          ENNReal.ofReal (ρ y) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun y => ?_
      ring
    rw [this]
    ring
  rw [hlhs, hrhs2]
  have hpt : ∀ x, ENNReal.ofReal Q⁻¹ * ENNReal.ofReal (Real.exp (-β * V x)) ≤
      ENNReal.ofReal K * ENNReal.ofReal (ρ x) := fun x => by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le), ← ENNReal.ofReal_mul hK]
    exact ENNReal.ofReal_le_ofReal (hdom x)
  refine lintegral_mono fun x => mul_le_mul (hpt x) (lintegral_mono fun y => ?_) (zero_le) (zero_le)
  exact mul_le_mul_right (hpt y) _

end Setting

end HRS.MS.Can2

end
