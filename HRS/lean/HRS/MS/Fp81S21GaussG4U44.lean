import HRS.MS.Fp81S21GaussG4U43

/-! Linearity of the physical generator on finite oscillator combinations. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

private theorem fp81s21_g4_combo_cb2
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {f : Euc p.d → ℝ}
    (hf : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f) :
    ContDiff ℝ 2 f ∧ ∃ B : ℝ, ∀ i, 1 ≤ i → i ≤ 2 → ∀ x,
      ‖iteratedFDeriv ℝ i f x‖ ≤ B := by
  obtain ⟨u, hu⟩ := fp81s21_adjoint_of_hermite_combo p R hf (t := 0) le_rfl
  have hc := hu.c2 0 ⟨le_rfl, le_rfl⟩
  rw [hu.terminal] at hc
  obtain ⟨B1, hB1⟩ := hu.bdd 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := hu.bdd 2 (by norm_num)
  refine ⟨hc, max B1 B2, ?_⟩
  intro i hi1 hi2 x
  have hcase : i = 1 ∨ i = 2 := by omega
  rcases hcase with rfl | rfl
  · exact (by simpa [hu.terminal] using hB1 0 ⟨le_rfl, le_rfl⟩ x :
      ‖iteratedFDeriv ℝ 1 f x‖ ≤ B1).trans (le_max_left _ _)
  · exact (by simpa [hu.terminal] using hB2 0 ⟨le_rfl, le_rfl⟩ x :
      ‖iteratedFDeriv ℝ 2 f x‖ ≤ B2).trans (le_max_right _ _)

/-- The generator respects linear combinations of finite oscillator sums. -/
theorem fp81s21_g4_generator_linear
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {q : ℝ} (hq : 0 ≤ q)
    {f g : Euc p.d → ℝ}
    (hf : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f)
    (hg : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) g) (a b : ℝ) :
    generatorW (r26t3_coeff R) q (fun x => a * f x + b * g x) =
      fun x => a * generatorW (r26t3_coeff R) q f x +
        b * generatorW (r26t3_coeff R) q g x := by
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  obtain ⟨c, K, hc, hK0, hρ⟩ := HRS.MS.S104e.s104e_gauss_rho
    p.hd p.hs0 hsd p.ha p.hβ δ p.c₁ p.C₁ 1 (by omega)
    R.thermal R.resulting
  obtain ⟨P, hP0, hU⟩ := HRS.MS.S104e.s104e_u2dec_of_gauss
    (d := p.d) hc 1 (p.d + 1)
  obtain ⟨hreg, hbnd⟩ := hρ q hq
  have hdec := hU (R.ρ q) K hK0 hreg (fun k hk x => hbnd k hk x)
  obtain ⟨hf2, Bf, hBf⟩ := fp81s21_g4_combo_cb2 p R hf
  obtain ⟨hg2, Bg, hBg⟩ := fp81s21_g4_combo_cb2 p R hg
  funext x
  have h := s103c_gen_lin (a := p.a) (β := p.β) p.hd p.hs0 hsd
    (show (p.d : ℝ) < ((p.d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self p.d)
    R.ρ q hdec a b hf2
    (fun i hi1 hi2 y => (hBf i hi1 hi2 y).trans (le_max_left _ _)) hg2
    (fun i hi1 hi2 y => (hBg i hi1 hi2 y).trans (le_max_right _ _)) x
  simpa [r26t3_coeff] using h

/-- Classical adjoint existence is closed under finite linear combinations. -/
theorem fp81s21_g4_adjoint_linear
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {t : ℝ} (ht : 0 ≤ t)
    {f g : Euc p.d → ℝ} (a b : ℝ)
    (hf : ∃ u, IsClassicalAdjointW (r26t3_coeff R) t f u)
    (hg : ∃ u, IsClassicalAdjointW (r26t3_coeff R) t g u) :
    ∃ u, IsClassicalAdjointW (r26t3_coeff R) t (fun x => a * f x + b * g x) u := by
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  obtain ⟨c, K, hc, hK0, hρ⟩ := HRS.MS.S104e.s104e_gauss_rho
    p.hd p.hs0 hsd p.ha p.hβ δ p.c₁ p.C₁ 1 (by omega)
    R.thermal R.resulting
  obtain ⟨P, hP0, hU⟩ := HRS.MS.S104e.s104e_u2dec_of_gauss
    (d := p.d) hc 1 (p.d + 1)
  have hA : ∀ τ ∈ Icc (0 : ℝ) t,
      U2Dec 1 ((p.d + 1 : ℕ) : ℝ) (P * K) (R.ρ τ) := by
    intro τ hτ
    obtain ⟨hreg, hbnd⟩ := hρ τ hτ.1
    exact hU (R.ρ τ) K hK0 hreg (fun k hk x => hbnd k hk x)
  obtain ⟨u, hu⟩ := hf
  obtain ⟨v, hv⟩ := hg
  refine ⟨fun r x => a * u r x + b * v r x, ?_⟩
  exact s103c_lincomb p.hd p.hs0 hsd
    (show (p.d : ℝ) < ((p.d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self p.d)
    R.ρ hA a b hu hv

/-- Generator and propagated-generator superposition for a finite sum. -/
theorem fp81s21_g4_generator_combo
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {r q : ℝ} (hr : 0 ≤ r) (hrq : r ≤ q)
    (S : Finset (MultiIndex p.d)) (c : MultiIndex p.d → ℝ) :
    let f := fun x => ∑ α ∈ S, c α * oscTestFun (wholeSpaceIndex p.d : ℝ) α x
    generatorW (r26t3_coeff R) q f =
        (fun x => ∑ α ∈ S, c α * generatorW (r26t3_coeff R) q
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x) ∧
    (∃ u, IsClassicalAdjointW (r26t3_coeff R) q (generatorW (r26t3_coeff R) q f) u) ∧
    r26t3_U R r q (generatorW (r26t3_coeff R) q f) =
        (fun x => ∑ α ∈ S, c α * r26t3_U R r q
          (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x) := by
  classical
  have hq : 0 ≤ q := hr.trans hrq
  have hm : ∀ α : MultiIndex p.d,
      ∃ u, IsClassicalAdjointW (r26t3_coeff R) q
        (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) u := by
    intro α
    have h := (s104b_orbit_of_termRegGen hterm R.admissible R.resulting α q hq).ex1 q ⟨hq, le_rfl⟩
    simpa [r26t3_coeff] using h
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    let z : Euc p.d → ℝ := fun _ => 0
    have hz : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) z := ⟨∅, fun _ => 0, by simp [z]⟩
    have he : generatorW (r26t3_coeff R) q z = z := by
      have h := fp81s21_g4_generator_linear p R hq hz hz 0 0
      simpa [z] using h
    have hex : ∃ u, IsClassicalAdjointW (r26t3_coeff R) q z u := by
      have h := fp81s21_g4_adjoint_linear p R hq 0 0 (hm 0) (hm 0)
      simpa [z] using h
    have hprop : r26t3_U R r q z = z := by
      have h := fp81s21_g4_propagator_linear p R hq ⟨hr, hrq⟩ 0 0 (hm 0) (hm 0)
      simpa [z] using h
    change generatorW (r26t3_coeff R) q z = z ∧
      (∃ u, IsClassicalAdjointW (r26t3_coeff R) q (generatorW (r26t3_coeff R) q z) u) ∧
      r26t3_U R r q (generatorW (r26t3_coeff R) q z) = z
    rw [he]
    exact ⟨rfl, hex, hprop⟩
  | @insert α S hα ih =>
    let f : Euc p.d → ℝ := fun x => ∑ β ∈ S, c β * oscTestFun (wholeSpaceIndex p.d : ℝ) β x
    let g : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
    have hf : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f := ⟨S, c, rfl⟩
    have hg : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) g := ⟨{α}, fun _ => 1, by simp [g]⟩
    have he : (fun x => ∑ β ∈ insert α S, c β * oscTestFun (wholeSpaceIndex p.d : ℝ) β x) =
        (fun x => 1 * f x + c α * g x) := by
      funext x
      simp [f, g, Finset.sum_insert, hα, add_comm]
    have hgen := fp81s21_g4_generator_linear p R hq hf hg 1 (c α)
    have hex := fp81s21_g4_adjoint_linear p R hq 1 (c α) ih.2.1 (hm α)
    have hp := fp81s21_g4_propagator_linear p R hq ⟨hr, hrq⟩ 1 (c α) ih.2.1 (hm α)
    dsimp only at ih ⊢
    rw [he, hgen]
    refine ⟨?_, hex, ?_⟩
    · funext x
      simp [f, g, ih.1, Finset.sum_insert, hα, add_comm]
    · rw [hp]
      funext x
      simp [f, g, ih.2.2, Finset.sum_insert, hα, add_comm]

/-- Propagation commutes with a finite sum of oscillator modes. -/
theorem fp81s21_g4_propagator_combo
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t)
    (S : Finset (MultiIndex p.d)) (c : MultiIndex p.d → ℝ) :
    r26t3_U R r t (fun x => ∑ α ∈ S, c α * oscTestFun (wholeSpaceIndex p.d : ℝ) α x) =
      fun x => ∑ α ∈ S, c α * r26t3_U R r t (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x := by
  classical
  have ht : 0 ≤ t := hr.trans hrt
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    let z : Euc p.d → ℝ := fun _ => 0
    have hz : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) z := ⟨∅, fun _ => 0, by simp [z]⟩
    have hex := fp81s21_adjoint_of_hermite_combo p R hz ht
    have h := fp81s21_g4_propagator_linear p R ht ⟨hr, hrt⟩ 0 0 hex hex
    simpa [z] using h
  | @insert α S hα ih =>
    let f : Euc p.d → ℝ := fun x => ∑ β ∈ S, c β * oscTestFun (wholeSpaceIndex p.d : ℝ) β x
    let g : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
    have hf : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f := ⟨S, c, rfl⟩
    have hg : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) g := ⟨{α}, fun _ => 1, by simp [g]⟩
    have he : (fun x => ∑ β ∈ insert α S, c β * oscTestFun (wholeSpaceIndex p.d : ℝ) β x) =
        (fun x => 1 * f x + c α * g x) := by
      funext x
      simp [f, g, Finset.sum_insert, hα, add_comm]
    rw [he, fp81s21_g4_propagator_linear p R ht ⟨hr, hrt⟩ 1 (c α)
      (fp81s21_adjoint_of_hermite_combo p R hf ht) (fp81s21_adjoint_of_hermite_combo p R hg ht)]
    funext x
    simp [f, g, ih, Finset.sum_insert, hα, add_comm]

/-- Terminal Duhamel formula and genuine time-integrability for every finite
oscillator combination, with the physical radius chosen uniformly. -/
theorem fp81s21_g4_duhamel_combo (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ f, IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f →
      ∀ r v w : ℝ, 0 ≤ r → r ≤ v → v ≤ w → ∀ x : Euc p.d,
        IntegrableOn (fun q => r26t3_U R r q
          (generatorW (r26t3_coeff R) q f) x) (Icc v w) ∧
        r26t3_U R r w f x - r26t3_U R r v f x =
          ∫ q in Icc v w, r26t3_U R r q (generatorW (r26t3_coeff R) q f) x := by
  classical
  obtain ⟨δc, Co, co, hδc, hhalf, hco, hcommon⟩ := fp81s21_common_radius p
  obtain ⟨δm, hδm, hmh, hmode⟩ := fp81s21_g4_duhamel_mode p
  refine ⟨min δc δm, lt_min hδc hδm, (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R f hf r v w hr hrv hvw x
  obtain ⟨_, _, hterm, _⟩ := hcommon δ hδ (hδle.trans (min_le_left _ _)) R.ρβ R.thermal
  rcases hf with ⟨S, c, rfl⟩
  have hm := hmode δ hδ (hδle.trans (min_le_right _ _)) R
  have hi : ∀ α : MultiIndex p.d, IntegrableOn (fun q => r26t3_U R r q
      (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x) (Icc v w) :=
    fun α => (hm α r v w hr hrv hvw x).1
  have he : ∀ q ∈ Icc v w, r26t3_U R r q
      (generatorW (r26t3_coeff R) q
        (fun y => ∑ α ∈ S, c α * oscTestFun (wholeSpaceIndex p.d : ℝ) α y)) x =
      ∑ α ∈ S, c α * r26t3_U R r q
        (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x := by
    intro q hq
    exact congrFun (fp81s21_g4_generator_combo p R hterm hr (hrv.trans hq.1) S c).2.2 x
  have hs : IntegrableOn (fun q => ∑ α ∈ S, c α * r26t3_U R r q
      (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x) (Icc v w) :=
    integrable_finset_sum S (fun α _ => (hi α).const_mul (c α))
  have hae : ∀ᵐ q ∂((volume : Measure ℝ).restrict (Icc v w)), q ∈ Icc v w :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  refine ⟨hs.congr ?_, ?_⟩
  · filter_upwards [hae] with q hq
    exact (he q hq).symm
  · have hw := congrFun (fp81s21_g4_propagator_combo p R hr (hrv.trans hvw) S c) x
    have hv := congrFun (fp81s21_g4_propagator_combo p R hr hrv S c) x
    rw [hw, hv]
    have hint : (∫ q in Icc v w, r26t3_U R r q
        (generatorW (r26t3_coeff R) q
          (fun y => ∑ α ∈ S, c α * oscTestFun (wholeSpaceIndex p.d : ℝ) α y)) x) =
        ∑ α ∈ S, c α * ∫ q in Icc v w, r26t3_U R r q
          (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x := by
      calc
        _ = ∫ q in Icc v w, ∑ α ∈ S, c α * r26t3_U R r q
            (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x := by
              apply integral_congr_ae
              filter_upwards [hae] with q hq
              exact he q hq
        _ = _ := by
          rw [integral_finset_sum S (fun α _ => (hi α).const_mul (c α))]
          simp only [integral_const_mul]
    rw [hint, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro α hα
    rw [← (hm α r v w hr hrv hvw x).2]
    ring

/-- A finite sum of differentiable scalar functions differentiates termwise. -/
theorem fp81s21_g4_gradient_sum {d : ℕ} {ι : Type*}
    (S : Finset ι) (c : ι → ℝ) (F : ι → Euc d → ℝ) (x : Euc d)
    (hF : ∀ i ∈ S, DifferentiableAt ℝ (F i) x) :
    gradient (fun y => ∑ i ∈ S, c i * F i y) x =
      ∑ i ∈ S, c i • gradient (F i) x := by
  classical
  unfold gradient
  rw [fderiv_fun_sum (fun i hi => (hF i hi).const_mul (c i))]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fderiv_const_mul (hF i hi) (c i), map_smul]

/-- Gradient terminal Duhamel formula, including integrability of its
vector-valued integrand. -/
theorem fp81s21_g4_gradient_duhamel_combo (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ f, IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f →
      ∀ r v w : ℝ, 0 ≤ r → r ≤ v → v ≤ w → ∀ x : Euc p.d,
        IntegrableOn (fun q => gradient (r26t3_U R r q
          (generatorW (r26t3_coeff R) q f)) x) (Icc v w) ∧
        gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x =
          ∫ q in Icc v w, gradient (r26t3_U R r q
            (generatorW (r26t3_coeff R) q f)) x := by
  classical
  obtain ⟨δc, Co, co, hδc, hhalf, hco, hcommon⟩ := fp81s21_common_radius p
  obtain ⟨δm, hδm, hmh, hmode⟩ := fp81s21_g4_gradient_duhamel_mode p
  refine ⟨min δc δm, lt_min hδc hδm, (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R f hf r v w hr hrv hvw x
  obtain ⟨_, _, hterm, _⟩ := hcommon δ hδ (hδle.trans (min_le_left _ _)) R.ρβ R.thermal
  rcases hf with ⟨S, c, rfl⟩
  have hm := hmode δ hδ (hδle.trans (min_le_right _ _)) R
  have hreg : ∀ q, r ≤ q → ∀ α : MultiIndex p.d,
      DifferentiableAt ℝ (r26t3_U R r q
        (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x := by
    intro q hrq α
    have hq : 0 ≤ q := hr.trans hrq
    have horb := s104b_orbit_of_termRegGen hterm R.admissible R.resulting α q hq
    have hcb := s104n_memCb_prop (horb.ex1 q ⟨hq, le_rfl⟩) ⟨hr, hrq⟩
    exact (hcb.1.differentiable (by norm_num)) x
  have he : ∀ q ∈ Icc v w, gradient (r26t3_U R r q
      (generatorW (r26t3_coeff R) q
        (fun y => ∑ α ∈ S, c α * oscTestFun (wholeSpaceIndex p.d : ℝ) α y))) x =
      ∑ α ∈ S, c α • gradient (r26t3_U R r q
        (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x := by
    intro q hq
    rw [(fp81s21_g4_generator_combo p R hterm hr (hrv.trans hq.1) S c).2.2]
    exact fp81s21_g4_gradient_sum S c _ x (fun α _ => hreg q (hrv.trans hq.1) α)
  have hi : ∀ α : MultiIndex p.d, IntegrableOn (fun q => gradient (r26t3_U R r q
      (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x) (Icc v w) :=
    fun α => (hm α r v w hr hrv hvw x).1
  have hs : IntegrableOn (fun q => ∑ α ∈ S, c α • gradient (r26t3_U R r q
      (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x) (Icc v w) :=
    integrable_finset_sum S (fun α _ => Integrable.smul (c α) (hi α))
  have hae : ∀ᵐ q ∂((volume : Measure ℝ).restrict (Icc v w)), q ∈ Icc v w :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  refine ⟨hs.congr ?_, ?_⟩
  · filter_upwards [hae] with q hq
    exact (he q hq).symm
  · have hend : ∀ t, r ≤ t → gradient (r26t3_U R r t
        (fun y => ∑ α ∈ S, c α * oscTestFun (wholeSpaceIndex p.d : ℝ) α y)) x =
        ∑ α ∈ S, c α • gradient (r26t3_U R r t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x := by
      intro t hrt
      rw [fp81s21_g4_propagator_combo p R hr hrt S c]
      apply fp81s21_g4_gradient_sum
      intro α hα
      have hex := fp81s21_hermite_adjoint p R α (hr.trans hrt)
      have hcb := s104n_memCb_prop hex ⟨hr, hrt⟩
      exact (hcb.1.differentiable (by norm_num)) x
    rw [hend w (hrv.trans hvw), hend v hrv]
    have hint : (∫ q in Icc v w, gradient (r26t3_U R r q
        (generatorW (r26t3_coeff R) q
          (fun y => ∑ α ∈ S, c α * oscTestFun (wholeSpaceIndex p.d : ℝ) α y))) x) =
        ∑ α ∈ S, c α • ∫ q in Icc v w, gradient (r26t3_U R r q
          (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x := by
      calc
        _ = ∫ q in Icc v w, ∑ α ∈ S, c α • gradient (r26t3_U R r q
            (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x := by
              apply integral_congr_ae
              filter_upwards [hae] with q hq
              exact he q hq
        _ = _ := by
          have hscaled : ∀ α, IntegrableOn (fun q => c α • gradient (r26t3_U R r q
              (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x)
              (Icc v w) := fun α => Integrable.smul (c α) (hi α)
          rw [integral_finset_sum S (fun α _ => hscaled α)]
          simp only [integral_smul]
    rw [hint, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro α hα
    rw [← (hm α r v w hr hrv hvw x).2, smul_sub]

#print axioms fp81s21_g4_gradient_duhamel_combo
#print axioms fp81s21_g4_gradient_sum
#print axioms fp81s21_g4_duhamel_combo
#print axioms fp81s21_g4_propagator_combo
#print axioms fp81s21_g4_generator_combo
#print axioms fp81s21_g4_adjoint_linear
#print axioms fp81s21_g4_generator_linear
end HRS.Fp81.S21
end
