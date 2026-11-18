import HRS.MS.MovLinAux7

/-!
# MOV-2d, part 2: the perturbation `R = ν V_1 + P` on the scale, the hypotheses `Mov2cHyp`, and the global
semigroup on `L²`

Namespace `HRS.MS.MovLin`, helpers `mov2d_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

For the thermal data `(d, s, β, q, ρ)` (`IsThermalEquilibrium d s q β ρ`, `2 ≤ d`, `0 ≤ s < d`, `β, q > 0`) and
`a = movA d s ∈ [1, 2)`:

* `mov2d_R r : OscSpace d r →L OscSpace d (r - a)`: the bounded extension of the function-level operator
  `f ↦ β⁻¹ V_1 f + movP d s ρ f` (`P` acts on finite Hermite sums, which are Schwartz functions;
  `mov_P_bound` for every real `r`; `V_1` by `mo_mult_memCb`).  `mov2d_P_lin`: `P` is linear on Schwartz functions
  (from the adjoint pairing `mov_P_adj_pairing`).
* `mov2d_hyp`: `Mov2cHyp` for the scale `OscSpace d r`, `j = mov2d_j`, `Sm = mov2d_Sm`, `R = mov2d_R`,
  for every `T0 > 0`.
* the Volterra solution at all levels and all times (`mov2d_G`), its Duhamel equation, the semigroup law, strong
  continuity and compatibility with `j`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-! ## A. Schwartz preliminaries -/

lemma mov2d_polyG_schwartz (w : 𝓢R) : PolyG (fun x => w x) := by
  obtain ⟨C, hC⟩ := w.decay 0 0
  refine ⟨C, 0, fun x => ?_⟩
  have := hC.2 x
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at this
  simpa using this

lemma mov2d_integrable_schwartz_mul (u w : 𝓢R) : Integrable (fun x => u x * w x) :=
  int_schwartz_mul u (fun x => w x) w.continuous (mov2d_polyG_schwartz w)

/-- Two Schwartz functions with the same pairings against all Schwartz functions coincide. -/
lemma mov2d_schwartz_ext (φ ψ : 𝓢R) (h : ∀ w : 𝓢R, ∫ x, φ x * w x = ∫ x, ψ x * w x) :
    (⇑φ : Euc d → ℝ) = ⇑ψ := by
  set D : 𝓢R := φ - ψ with hD
  have h1 : ∫ x, D x * D x = 0 := by
    have e : ∀ x, D x * D x = φ x * D x - ψ x * D x := fun x => by
      simp only [hD, sub_apply]; ring
    simp_rw [e]
    rw [integral_sub (mov2d_integrable_schwartz_mul φ D) (mov2d_integrable_schwartz_mul ψ D), h D, sub_self]
  have h2 : (fun x => D x * D x) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (D x))
      (mov2d_integrable_schwartz_mul D D)).1 h1
  have h3 : (fun x => D x * D x) = 0 := by
    have := (Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) (D.continuous.mul D.continuous)
      continuous_const).1 (h2.trans (by rfl))
    exact this
  funext x
  have := congrFun h3 x
  simp only [Pi.zero_apply, mul_self_eq_zero] at this
  simp only [hD, sub_apply] at this
  linarith

lemma mov2d_hs_schwartz (c : MultiIndex d →₀ ℝ) : ∃ φ : 𝓢R, (⇑φ : Euc d → ℝ) = mov2d_hs d c := by
  have : mov2d_hs d c ∈ mo_Hspan d := by
    rw [mov2d_hs_eq]; exact mova3_comb_mem c.support (⇑c)
  exact mova3c_hspan_schwartz this

/-! ## B. The perturbation `R` -/

section Thermal

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

/-- `P` is linear on Schwartz functions. -/
lemma mov2d_P_lin (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (hq : 0 < q)
    (hρ : IsThermalEquilibrium d s q β ρ) (a b : ℝ) (φ1 φ2 : 𝓢R) :
    movP d s ρ (fun z => a * φ1 z + b * φ2 z) = fun z => a * movP d s ρ φ1 z + b * movP d s ρ φ2 z := by
  obtain ⟨ψ, hψ⟩ := mov_P_schwartz hd hs0 hsd β q hβ hq ρ hρ (a • φ1 + b • φ2)
  obtain ⟨ψ1, hψ1⟩ := mov_P_schwartz hd hs0 hsd β q hβ hq ρ hρ φ1
  obtain ⟨ψ2, hψ2⟩ := mov_P_schwartz hd hs0 hsd β q hβ hq ρ hρ φ2
  have hv : (⇑(a • φ1 + b • φ2) : Euc d → ℝ) = fun z => a * φ1 z + b * φ2 z := by
    funext z; simp
  rw [hv] at hψ
  have key : (⇑ψ : Euc d → ℝ) = ⇑(a • ψ1 + b • ψ2) := by
    refine mov2d_schwartz_ext ψ (a • ψ1 + b • ψ2) fun w => ?_
    obtain ⟨χ, hχ⟩ := mov_Padj_schwartz hd hs0 hsd β q hβ hq ρ hρ w
    have p0 := mov_P_adj_pairing hd hs0 hsd β q hβ hq ρ hρ (a • φ1 + b • φ2) w
    have p1 := mov_P_adj_pairing hd hs0 hsd β q hβ hq ρ hρ φ1 w
    have p2 := mov_P_adj_pairing hd hs0 hsd β q hβ hq ρ hρ φ2 w
    have e0 : ∀ x, ψ x = movP d s ρ (⇑(a • φ1 + b • φ2)) x := fun x => by
      rw [hv]; exact congrFun hψ x
    have e1 : ∀ x, ψ1 x = movP d s ρ φ1 x := fun x => congrFun hψ1 x
    have e2 : ∀ x, ψ2 x = movP d s ρ φ2 x := fun x => congrFun hψ2 x
    have hPad : ∀ x, movPadj d s ρ w x = χ x := fun x => (congrFun hχ x).symm
    have hI1 := mov2d_integrable_schwartz_mul φ1 χ
    have hI2 := mov2d_integrable_schwartz_mul φ2 χ
    have hI3 := mov2d_integrable_schwartz_mul ψ1 w
    have hI4 := mov2d_integrable_schwartz_mul ψ2 w
    have hv' : ∀ x, (a • φ1 + b • φ2) x = a * φ1 x + b * φ2 x := fun x => by simp
    calc ∫ x, ψ x * w x = ∫ x, movP d s ρ (⇑(a • φ1 + b • φ2)) x * w x := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [e0 x]
      _ = ∫ x, (a • φ1 + b • φ2) x * movPadj d s ρ w x := p0
      _ = a * (∫ x, φ1 x * χ x) + b * (∫ x, φ2 x * χ x) := by
          simp_rw [hPad, hv', add_mul, mul_assoc]
          rw [integral_add (hI1.const_mul a) (hI2.const_mul b), integral_const_mul, integral_const_mul]
      _ = a * (∫ x, movP d s ρ φ1 x * w x) + b * (∫ x, movP d s ρ φ2 x * w x) := by
          simp_rw [hPad] at p1 p2
          rw [← p1, ← p2]
      _ = ∫ x, (a • ψ1 + b • ψ2) x * w x := by
          have hv'' : ∀ x, (a • ψ1 + b • ψ2) x = a * ψ1 x + b * ψ2 x := fun x => by simp
          simp_rw [hv'', add_mul, mul_assoc, e1, e2]
          rw [integral_add ((hI3.congr (Eventually.of_forall fun x => by simp only [e1 x])).const_mul a)
            ((hI4.congr (Eventually.of_forall fun x => by simp only [e2 x])).const_mul b),
            integral_const_mul, integral_const_mul]
  funext z
  have h1 := congrFun hψ z
  have h2 := congrFun key z
  have h3 := congrFun hψ1 z
  have h4 := congrFun hψ2 z
  simp only [add_apply, smul_apply, smul_eq_mul] at h2
  rw [← h1, h2, h3, h4]

/-- The standing thermal hypotheses of S6.1/S6.2. -/
structure Mov2dTh (d : ℕ) (s β q : ℝ) (ρ : Euc d → ℝ) : Prop where
  hd : 2 ≤ d
  hs0 : 0 ≤ s
  hsd : s < d
  hβ : 0 < β
  hq : 0 < q
  hρ : IsThermalEquilibrium d s q β ρ

lemma mov2d_P_lin' (H : Mov2dTh d s β q ρ) {f1 f2 : Euc d → ℝ} (h1 : ∃ φ : 𝓢R, ⇑φ = f1)
    (h2 : ∃ φ : 𝓢R, ⇑φ = f2) (a b : ℝ) :
    movP d s ρ (fun z => a * f1 z + b * f2 z) = fun z => a * movP d s ρ f1 z + b * movP d s ρ f2 z := by
  obtain ⟨φ1, rfl⟩ := h1
  obtain ⟨φ2, rfl⟩ := h2
  exact mov2d_P_lin H.hd H.hs0 H.hsd H.hβ H.hq H.hρ a b φ1 φ2

/-- The function-level perturbation `f ↦ β⁻¹ V_1 f + P f` (so that `S = S_0 + R` on Schwartz functions,
`mov_S_eq_S0`). -/
def mov2d_AR (d : ℕ) (s β q : ℝ) (ρ : Euc d → ℝ) (f : Euc d → ℝ) : Euc d → ℝ :=
  fun z => β⁻¹ * mov2a_V1 d s β q ρ z * f z + movP d s ρ f z

/-- `V_1` multiplies `Σ^r` boundedly. -/
lemma mov2d_V1_mult (H : Mov2dTh d s β q ρ) (r : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : Euc d → ℝ, MemOsc r f →
      MemOsc r (fun z => β⁻¹ * mov2a_V1 d s β q ρ z * f z) ∧
        oscNorm r (fun z => β⁻¹ * mov2a_V1 d s β q ρ z * f z) ≤ K * oscNorm r f := by
  set N : ℕ := ⌈|r|⌉₊ with hN
  have hrN : |r| ≤ (N : ℝ) := Nat.le_ceil _
  obtain ⟨C, hC, h⟩ := mo_mult_memCb (d := d) r N hrN
  obtain ⟨hcb, C0, hC0, hcb2⟩ := mov2a_V1_memCb H.hd H.hs0 H.hsd H.hβ H.hq H.hρ N
  obtain ⟨hsm, hbd⟩ := mov2a_V1_bound H.hd H.hs0 H.hsd H.hβ H.hq H.hρ
  have htg : (mov2a_V1 d s β q ρ).HasTemperateGrowth := by
    refine ⟨hsm, fun n => ?_⟩
    obtain ⟨Cn, hCn0, hCn⟩ := hbd n
    exact ⟨0, Cn, fun x => by simpa using hCn n le_rfl x⟩
  have hβi : 0 ≤ β⁻¹ := (inv_pos.2 H.hβ).le
  refine ⟨β⁻¹ * (C * ((N + 1) * C0)), by positivity, fun f hf => ?_⟩
  obtain ⟨h1, h2⟩ := h (mov2a_V1 d s β q ρ) htg hcb f hf
  have e : (fun z => β⁻¹ * mov2a_V1 d s β q ρ z * f z) =
      fun z => β⁻¹ * (mov2a_V1 d s β q ρ z * f z) := by funext z; ring
  rw [e]
  obtain ⟨h3, h4⟩ := movc1_osc_smul r β⁻¹ h1
  refine ⟨h3, ?_⟩
  rw [h4, abs_of_nonneg hβi]
  have hn : 0 ≤ oscNorm r f := Real.sqrt_nonneg _
  calc β⁻¹ * oscNorm r (fun x => mov2a_V1 d s β q ρ x * f x)
      ≤ β⁻¹ * (C * cbNorm N (mov2a_V1 d s β q ρ) * oscNorm r f) := mul_le_mul_of_nonneg_left h2 hβi
    _ ≤ β⁻¹ * (C * ((N + 1) * C0) * oscNorm r f) := by
        apply mul_le_mul_of_nonneg_left _ hβi
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcb2 hC) hn
    _ = _ := by ring

lemma mov2d_a_bounds (d : ℕ) (hd : 2 ≤ d) {s : ℝ} (hsd : s < d) : 0 ≤ movA d s ∧ movA d s < 2 := by
  unfold movA
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  constructor
  · exact le_trans zero_le_one (le_max_left _ _)
  · exact max_lt (by norm_num) (by linarith)

/-- Data for the perturbation `R = β⁻¹ V_1 + P` as an operator `Σ^r → Σ^{r-a}`. -/
lemma mov2d_AR_data (H : Mov2dTh d s β q ρ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ Mov2dData (d := d) r (r - movA d s) (mov2d_AR d s β q ρ) C := by
  obtain ⟨K, hK0, hK⟩ := mov2d_V1_mult H r
  obtain ⟨CP, hCP0, hCP⟩ := mov_P_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ r
  have ha0 := (mov2d_a_bounds d H.hd H.hsd).1
  refine ⟨K + CP, by positivity, ?_⟩
  refine mov2d_data_of_ae (fun c => ?_) (fun c c' => ?_) (fun a c => ?_)
  · obtain ⟨φ, hφ⟩ := mov2d_hs_schwartz c
    have hf := mov2d_hs_memOsc r c
    obtain ⟨h1, h2⟩ := hK _ hf
    obtain ⟨h1', h2'⟩ := mo_mono (sub_le_self r ha0) h1
    have hP := hCP φ
    rw [hφ] at hP
    have hn : 0 ≤ oscNorm r (mov2d_hs d c) := Real.sqrt_nonneg _
    obtain ⟨h5, h6⟩ := HRS.MS.MovC1.movc1_osc_add (r - movA d s) h1' hP.1
    refine ⟨h5, h6.trans ?_⟩
    nlinarith [h2, h2', hP.2]
  · obtain ⟨φ1, h1⟩ := mov2d_hs_schwartz c
    obtain ⟨φ2, h2⟩ := mov2d_hs_schwartz c'
    have := mov2d_P_lin' H ⟨φ1, h1⟩ ⟨φ2, h2⟩ 1 1
    refine Eventually.of_forall fun z => ?_
    have e1 : (fun z => mov2d_hs d c z + mov2d_hs d c' z) = fun z => 1 * mov2d_hs d c z + 1 * mov2d_hs d c' z := by
      funext z; ring
    unfold mov2d_AR
    rw [e1, this]
    simp only [one_mul]
    ring
  · obtain ⟨φ1, h1⟩ := mov2d_hs_schwartz c
    have := mov2d_P_lin' H ⟨φ1, h1⟩ ⟨φ1, h1⟩ a 0
    refine Eventually.of_forall fun z => ?_
    have e1 : (fun z => a * mov2d_hs d c z) = fun z => a * mov2d_hs d c z + 0 * mov2d_hs d c z := by
      funext z; ring
    unfold mov2d_AR
    rw [e1, this]
    simp only [zero_mul, add_zero]
    ring

/-- The perturbation `R = β⁻¹ V_1 + P : Σ^r → Σ^{r-a}` as a bounded operator on the scale. -/
def mov2d_R (d : ℕ) (s β q : ℝ) (ρ : Euc d → ℝ) (r : ℝ) : OscSpace d r →L[ℝ] OscSpace d (r - movA d s) :=
  mov2d_op r (r - movA d s) (mov2d_AR d s β q ρ)

lemma mov2d_R_ofFun (H : Mov2dTh d s β q ρ) (r : ℝ) (c : MultiIndex d →₀ ℝ) :
    mov2d_R d s β q ρ r (OscSpace.ofFun r (mov2d_hs d c)) =
      OscSpace.ofFun (r - movA d s) (mov2d_AR d s β q ρ (mov2d_hs d c)) := by
  obtain ⟨C, -, h⟩ := mov2d_AR_data H r
  exact mov2d_op_hs h c

lemma mov2d_R_compat (H : Mov2dTh d s β q ρ) {r r' : ℝ} (h : r' ≤ r) (x : OscSpace d r) :
    mov2d_j (sub_le_sub_right h (movA d s)) (mov2d_R d s β q ρ r x) =
      mov2d_R d s β q ρ r' (mov2d_j h x) := by
  have key : (mov2d_j (sub_le_sub_right h (movA d s))).comp (mov2d_R d s β q ρ r) =
      (mov2d_R d s β q ρ r').comp (mov2d_j (d := d) h) := by
    refine mov2d_ext fun c => ?_
    obtain ⟨C, -, hd⟩ := mov2d_AR_data H r
    have hf := mov2d_hs_memOsc r c
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, mov2d_R_ofFun H r c,
      mov2d_j_ofFun _ (hd.1 c).1, mov2d_j_ofFun h hf, mov2d_R_ofFun H r' c]
  exact congrArg (fun E => E x) key

/-- `Mov2cHyp` for the scale `OscSpace d r`, `j = mov2d_j`, `Sm = mov2d_Sm`, `R = mov2d_R`. -/
theorem mov2d_hyp (H : Mov2dTh d s β q ρ) {T0 : ℝ} (hT0 : 0 < T0) :
    Mov2cHyp (X := fun r => OscSpace d r) (fun {r r'} h => mov2d_j h) (movA d s) T0
      (fun {ρ σ} h t => mov2d_Sm β q h t) (fun r => mov2d_R d s β q ρ r) where
  j_refl r x := by
    show mov2d_j (le_refl r) x = x
    rw [mov2d_j_refl]; rfl
  zero r x := by
    show mov2d_Sm β q (le_refl r) 0 x = x
    rw [mov2d_Sm_zero H.hβ H.hq]; rfl
  cont r x := mov2d_Sm_cont H.hβ H.hq r x
  semi h s τ hs hτ y := mov2d_Sm_semi H.hβ H.hq h hs hτ y
  bound h := mov2d_Sm_bound H.hβ H.hq h hT0
  compS h h' hρ hσ t ht x := mov2d_Sm_compS H.hβ H.hq h h' hρ hσ ht x
  compR h x := mov2d_R_compat H h x

/-! ## C. The Volterra solution at all levels and all times -/

/-- The embeddings `j` as an implicit-binder family (the form used by `Mov2cHyp`). -/
def mov2d_jF (d : ℕ) : ∀ {r r' : ℝ}, r' ≤ r → OscSpace d r →L[ℝ] OscSpace d r' :=
  fun {_ _} h => mov2d_j h

/-- `e^{-tS_0}` as an implicit-binder family. -/
def mov2d_SmF (d : ℕ) (β q : ℝ) : ∀ {ρ σ : ℝ}, ρ ≤ σ → ℝ → OscSpace d ρ →L[ℝ] OscSpace d σ :=
  fun {_ _} h t => mov2d_Sm β q h t

/-- `R` as a family over the levels. -/
def mov2d_RF (d : ℕ) (s β q : ℝ) (ρ : Euc d → ℝ) :
    ∀ r : ℝ, OscSpace d r →L[ℝ] OscSpace d (r - movA d s) :=
  fun r => mov2d_R d s β q ρ r

theorem mov2d_hyp' (H : Mov2dTh d s β q ρ) {T0 : ℝ} (hT0 : 0 < T0) :
    Mov2cHyp (X := fun r => OscSpace d r) (mov2d_jF d) (movA d s) T0 (mov2d_SmF d β q)
      (mov2d_RF d s β q ρ) :=
  mov2d_hyp H hT0

/-- The level structure of `mov2c_scale_volterra` for the thermal data. -/
abbrev mov2d_Lev (H : Mov2dTh d s β q ρ) (T0 r : ℝ) (Tn : ℕ → ℝ → OscSpace d r →L[ℝ] OscSpace d r)
    (T : ℝ → OscSpace d r →L[ℝ] OscSpace d r) : Prop :=
  Mov2cLevel (X := fun r => OscSpace d r) T0 (mov2d_SmF d β q) (mov2d_RF d s β q ρ)
    (mov2d_a_bounds d H.hd H.hsd).1 r Tn T

lemma mov2d_scale_ex (H : Mov2dTh d s β q ρ) (T0 : ℝ) (hT0 : 0 < T0) :
    ∃ T : ∀ r : ℝ, ℝ → OscSpace d r →L[ℝ] OscSpace d r,
      (∀ r, ∃ Tn, mov2d_Lev H T0 r Tn (T r)) ∧
      ∀ (r r' : ℝ) (h : r' ≤ r), ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ x,
        mov2d_j h (T r t x) = T r' t (mov2d_j h x) := by
  obtain ⟨Tn, T, hL, hc, -⟩ := mov2c_scale_volterra (mov2d_hyp' H hT0) (mov2d_a_bounds d H.hd H.hsd).1
    (mov2d_a_bounds d H.hd H.hsd).2 hT0
  exact ⟨T, fun r => ⟨Tn r, hL r⟩, hc⟩

/-- The solution for `T0 = n + 1`. -/
def mov2d_TT (H : Mov2dTh d s β q ρ) (n : ℕ) : ∀ r : ℝ, ℝ → OscSpace d r →L[ℝ] OscSpace d r :=
  (mov2d_scale_ex H ((n : ℝ) + 1) (by positivity)).choose

lemma mov2d_TT_spec (H : Mov2dTh d s β q ρ) (n : ℕ) :
    (∀ r, ∃ Tn, mov2d_Lev H ((n : ℝ) + 1) r Tn (mov2d_TT H n r)) ∧
      ∀ (r r' : ℝ) (h : r' ≤ r), ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), ∀ x,
        mov2d_j h (mov2d_TT H n r t x) = mov2d_TT H n r' t (mov2d_j h x) :=
  (mov2d_scale_ex H ((n : ℝ) + 1) (by positivity)).choose_spec

/-- Consistency of the solutions for different `T0`. -/
lemma mov2d_TT_consistent (H : Mov2dTh d s β q ρ) {m n : ℕ} (hmn : m ≤ n) (r : ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1)) : mov2d_TT H n r t = mov2d_TT H m r t := by
  obtain ⟨Tm, Lm⟩ := (mov2d_TT_spec H m).1 r
  obtain ⟨Tn, Ln⟩ := (mov2d_TT_spec H n).1 r
  have hle : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
  refine Lm.unique (mov2d_TT H n r) (fun x => (Ln.cont x).mono (Set.Icc_subset_Icc le_rfl hle))
    (fun t ht x => Ln.duhamel t ⟨ht.1, ht.2.trans hle⟩ x) t ht

/-- The global solution at level `r`. -/
def mov2d_G (H : Mov2dTh d s β q ρ) (r : ℝ) (t : ℝ) : OscSpace d r →L[ℝ] OscSpace d r :=
  mov2d_TT H ⌈t⌉₊ r t

lemma mov2d_G_eq (H : Mov2dTh d s β q ρ) (r : ℝ) {n : ℕ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1)) :
    mov2d_G H r t = mov2d_TT H n r t := by
  unfold mov2d_G
  have hm : (⌈t⌉₊ : ℝ) + 1 ≥ t := by have := Nat.le_ceil t; linarith
  have h1 : t ∈ Set.Icc (0 : ℝ) ((⌈t⌉₊ : ℝ) + 1) := ⟨ht.1, hm⟩
  rcases le_total ⌈t⌉₊ n with h | h
  · exact (mov2d_TT_consistent H h r h1).symm
  · exact mov2d_TT_consistent H h r ht

/-- Duhamel's equation for the global solution (`t ≥ 0`). -/
lemma mov2d_G_duhamel (H : Mov2dTh d s β q ρ) (r : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : OscSpace d r) :
    mov2d_G H r t x = mov2d_Sm β q (le_refl r) t x - ∫ u in (0 : ℝ)..t,
      mov2d_Sm β q (sub_le_self r (mov2d_a_bounds d H.hd H.hsd).1) (t - u)
        (mov2d_R d s β q ρ r (mov2d_G H r u x)) := by
  obtain ⟨Tn, L⟩ := (mov2d_TT_spec H ⌈t⌉₊).1 r
  have hm : t ≤ (⌈t⌉₊ : ℝ) + 1 := by have := Nat.le_ceil t; linarith
  have h1 : t ∈ Set.Icc (0 : ℝ) ((⌈t⌉₊ : ℝ) + 1) := ⟨ht, hm⟩
  rw [mov2d_G_eq H r h1, L.duhamel t h1 x]
  congr 1
  refine intervalIntegral.integral_congr (fun u hu => ?_)
  rw [Set.uIcc_of_le ht] at hu
  have hu' : u ∈ Set.Icc (0 : ℝ) ((⌈t⌉₊ : ℝ) + 1) := ⟨hu.1, hu.2.trans hm⟩
  simp only [mov2d_G_eq H r hu']
  rfl

lemma mov2d_G_cont (H : Mov2dTh d s β q ρ) (r : ℝ) (x : OscSpace d r) :
    ContinuousOn (fun t => mov2d_G H r t x) (Set.Ici 0) := by
  intro t0 ht0
  have ht0' : (0 : ℝ) ≤ t0 := ht0
  obtain ⟨Tn, L⟩ := (mov2d_TT_spec H ⌈t0⌉₊).1 r
  have hm : t0 < (⌈t0⌉₊ : ℝ) + 1 := by have := Nat.le_ceil t0; linarith
  have hI : Set.Icc (0 : ℝ) ((⌈t0⌉₊ : ℝ) + 1) ∈ 𝓝[Set.Ici (0 : ℝ)] t0 :=
    mem_nhdsWithin.2 ⟨Set.Iio ((⌈t0⌉₊ : ℝ) + 1), isOpen_Iio, hm, fun u hu => ⟨hu.2, hu.1.le⟩⟩
  have hc : ContinuousWithinAt (fun t => mov2d_TT H ⌈t0⌉₊ r t x) (Set.Icc 0 ((⌈t0⌉₊ : ℝ) + 1)) t0 :=
    L.cont x t0 ⟨ht0', hm.le⟩
  refine (hc.mono_of_mem_nhdsWithin hI).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hI] with u hu
    rw [mov2d_G_eq H r hu]
  · rw [mov2d_G_eq H r ⟨ht0', hm.le⟩]

lemma mov2d_G_zero (H : Mov2dTh d s β q ρ) (r : ℝ) (x : OscSpace d r) : mov2d_G H r 0 x = x := by
  rw [mov2d_G_duhamel H r le_rfl x]
  simp [mov2d_Sm_zero H.hβ H.hq]

lemma mov2d_G_bound (H : Mov2dTh d s β q ρ) (r T0 : ℝ) :
    ∃ N : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T0, ‖mov2d_G H r t‖ ≤ N := by
  obtain ⟨Tn, L⟩ := (mov2d_TT_spec H ⌈T0⌉₊).1 r
  obtain ⟨N, hN⟩ := L.norm_le
  have hm : T0 ≤ (⌈T0⌉₊ : ℝ) + 1 := by have := Nat.le_ceil T0; linarith
  refine ⟨N, fun t ht => ?_⟩
  have h1 : t ∈ Set.Icc (0 : ℝ) ((⌈T0⌉₊ : ℝ) + 1) := ⟨ht.1, ht.2.trans hm⟩
  rw [mov2d_G_eq H r h1]
  exact hN t h1

lemma mov2d_G_compat (H : Mov2dTh d s β q ρ) {r r' : ℝ} (h : r' ≤ r) {t : ℝ} (ht : 0 ≤ t)
    (x : OscSpace d r) :
    mov2d_j h (mov2d_G H r t x) = mov2d_G H r' t (mov2d_j h x) := by
  have hm : t ≤ (⌈t⌉₊ : ℝ) + 1 := by have := Nat.le_ceil t; linarith
  have h1 : t ∈ Set.Icc (0 : ℝ) ((⌈t⌉₊ : ℝ) + 1) := ⟨ht, hm⟩
  rw [mov2d_G_eq H r h1, mov2d_G_eq H r' h1]
  exact (mov2d_TT_spec H ⌈t⌉₊).2 r r' h t h1 x

lemma mov2d_K_apply (H : Mov2dTh d s β q ρ) (r τ : ℝ) (z : OscSpace d r) :
    mov2c_K (mov2d_SmF d β q) (mov2d_RF d s β q ρ) (mov2d_a_bounds d H.hd H.hsd).1 r τ z =
      mov2d_Sm β q (sub_le_self r (mov2d_a_bounds d H.hd H.hsd).1) τ (mov2d_R d s β q ρ r z) := rfl

/-- **The semigroup law** `G(s + t) = G(t) G(s)` for the global Volterra solution. -/
lemma mov2d_G_add (H : Mov2dTh d s β q ρ) (r : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (x : OscSpace d r) : mov2d_G H r (a + b) x = mov2d_G H r b (mov2d_G H r a x) := by
  rcases ha.eq_or_lt with h0 | hapos
  · subst h0
    rw [zero_add, mov2d_G_zero]
  set a0 := (mov2d_a_bounds d H.hd H.hsd).1 with ha0
  have ha2 := (mov2d_a_bounds d H.hd H.hsd).2
  set T1 : ℝ := a + b + 1 with hT1
  set T0 : ℝ := b + 1 with hT0
  have hT1p : 0 < T1 := by positivity
  have hyp := mov2d_hyp' H hT1p
  obtain ⟨Kc, hK1⟩ := mov2c_K_ker hyp a0 r
  set K := mov2c_K (mov2d_SmF d β q) (mov2d_RF d s β q ρ) a0 r with hKdef
  have hθ : 0 < 1 - movA d s / 2 := by linarith
  have hθ1 : 1 - movA d s / 2 ≤ 1 := by linarith
  have hK0 : Mov2cKer K T0 Kc (1 - movA d s / 2) :=
    ⟨hK1.Kc_nonneg, fun y => (hK1.cont y).mono (Set.Ioc_subset_Ioc le_rfl (by rw [hT1, hT0]; linarith)),
      fun τ hτ => hK1.bound τ ⟨hτ.1, hτ.2.trans (by rw [hT1, hT0]; linarith)⟩⟩
  set y : OscSpace d r := mov2d_G H r a x with hy
  -- continuity of the two families
  have hc1 : ContinuousOn (fun v => mov2d_G H r (a + v) x) (Set.Icc 0 T0) :=
    ((mov2d_G_cont H r x).comp (continuousOn_const.add continuousOn_id)
      (fun v hv => by simp only [Set.mem_Ici, Pi.add_apply, id]; linarith [hv.1])).mono (fun v hv => hv)
  have hc2 : ContinuousOn (fun v => mov2d_G H r v y) (Set.Icc 0 T0) :=
    (mov2d_G_cont H r y).mono (fun v hv => hv.1)
  have hcT1 : ContinuousOn (fun v => mov2d_G H r v x) (Set.Icc 0 T1) :=
    (mov2d_G_cont H r x).mono (fun v hv => hv.1)
  have hcT1y : ContinuousOn (fun v => mov2d_G H r v y) (Set.Icc 0 T1) :=
    (mov2d_G_cont H r y).mono (fun v hv => hv.1)
  have hSm : ∀ {u : ℝ}, 0 ≤ u → ∀ (z : OscSpace d r) (v : ℝ), 0 < a - v →
      mov2d_Sm β q (le_refl r) u (K (a - v) z) = K (a + u - v) z := by
    intro u hu z v hv
    rw [hKdef, mov2d_K_apply H, mov2d_K_apply H, mov2d_Sm_semi H.hβ H.hq _ hu hv]
    congr 2; ring
  -- Duhamel for `G(a + u) x`
  have hD1 : ∀ u ∈ Set.Icc (0 : ℝ) T0, mov2d_G H r (a + u) x =
      mov2d_Sm β q (le_refl r) u y - ∫ v in (0 : ℝ)..u, K (u - v) (mov2d_G H r (a + v) x) := by
    intro u hu
    have hau : a + u ∈ Set.Icc (0 : ℝ) T1 := ⟨by linarith [hu.1], by rw [hT1]; linarith [hu.2, hT0]⟩
    have haI : a ∈ Set.Icc (0 : ℝ) T1 := ⟨ha, by rw [hT1]; linarith⟩
    rw [mov2d_G_duhamel H r hau.1 x]
    have hfull : IntervalIntegrable (fun v => K (a + u - v) (mov2d_G H r v x)) MeasureTheory.volume 0 (a + u) :=
      mov2c_vol_int hK1 hθ hθ1 hcT1 hau
    have h1 : IntervalIntegrable (fun v => K (a + u - v) (mov2d_G H r v x)) MeasureTheory.volume 0 a :=
      hfull.mono_set (by
        rw [Set.uIcc_of_le ha, Set.uIcc_of_le hau.1]
        exact Set.Icc_subset_Icc le_rfl (by linarith [hu.1]))
    have h2 : IntervalIntegrable (fun v => K (a + u - v) (mov2d_G H r v x)) MeasureTheory.volume a (a + u) :=
      hfull.mono_set (by
        rw [Set.uIcc_of_le (by linarith [hu.1] : a ≤ a + u), Set.uIcc_of_le hau.1]
        exact Set.Icc_subset_Icc ha le_rfl)
    have hg : IntervalIntegrable (fun v => K (a - v) (mov2d_G H r v x)) MeasureTheory.volume 0 a :=
      mov2c_vol_int hK1 hθ hθ1 hcT1 haI
    have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hp1 : ∫ v in (0 : ℝ)..a, K (a + u - v) (mov2d_G H r v x) =
        mov2d_Sm β q (le_refl r) u (∫ v in (0 : ℝ)..a, K (a - v) (mov2d_G H r v x)) := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hg]
      refine intervalIntegral.integral_congr_ae ?_
      have hae : ∀ᵐ v ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), v ∉ ({a} : Set ℝ) :=
        (Set.finite_singleton a).countable.ae_notMem _
      refine hae.mono (fun v hv hvI => ?_)
      rw [Set.uIoc_of_le ha] at hvI
      have hva : v < a := lt_of_le_of_ne hvI.2 hv
      exact (hSm hu.1 _ v (by linarith)).symm
    have hp2 : ∫ v in a..(a + u), K (a + u - v) (mov2d_G H r v x) =
        ∫ v in (0 : ℝ)..u, K (u - v) (mov2d_G H r (a + v) x) := by
      have := intervalIntegral.integral_comp_add_left (a := 0) (b := u)
        (fun v => K (a + u - v) (mov2d_G H r v x)) a
      simp only [add_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      simp only [show a + u - (a + v) = u - v by ring]
    have hGa := mov2d_G_duhamel H r ha x
    have hsem : mov2d_Sm β q (le_refl r) (a + u) x =
        mov2d_Sm β q (le_refl r) u (mov2d_Sm β q (le_refl r) a x) := by
      rw [mov2d_Sm_semi H.hβ H.hq (le_refl r) hu.1 hapos x, add_comm]
    have hint_eq : ∫ v in (0 : ℝ)..(a + u), mov2d_Sm β q (sub_le_self r a0) (a + u - v)
        (mov2d_R d s β q ρ r (mov2d_G H r v x)) =
        ∫ v in (0 : ℝ)..(a + u), K (a + u - v) (mov2d_G H r v x) := rfl
    rw [hint_eq, ← hsplit, hp1, hp2, hsem]
    have hy' : y = mov2d_Sm β q (le_refl r) a x - ∫ v in (0 : ℝ)..a, K (a - v) (mov2d_G H r v x) := hGa
    rw [hy', map_sub]
    abel
  -- Duhamel for `G(v) y`
  have hD2 : ∀ u ∈ Set.Icc (0 : ℝ) T0, mov2d_G H r u y =
      mov2d_Sm β q (le_refl r) u y - ∫ v in (0 : ℝ)..u, K (u - v) (mov2d_G H r v y) := by
    intro u hu
    rw [mov2d_G_duhamel H r hu.1 y]
    rfl
  -- the difference solves the homogeneous Volterra equation
  have hw := mov2c_vol_unique hK0 hθ hθ1 (by rw [hT0]; linarith) (w := fun u => mov2d_G H r (a + u) x - mov2d_G H r u y)
    (hc1.sub hc2) (by
      intro u hu
      have hi1 : IntervalIntegrable (fun v => K (u - v) (mov2d_G H r (a + v) x)) MeasureTheory.volume 0 u :=
        mov2c_vol_int hK0 hθ hθ1 hc1 hu
      have hi2 : IntervalIntegrable (fun v => K (u - v) (mov2d_G H r v y)) MeasureTheory.volume 0 u :=
        mov2c_vol_int hK0 hθ hθ1 hc2 hu
      show mov2d_G H r (a + u) x - mov2d_G H r u y =
        -∫ v in (0 : ℝ)..u, K (u - v) (mov2d_G H r (a + v) x - mov2d_G H r v y)
      simp_rw [map_sub]
      rw [intervalIntegral.integral_sub hi1 hi2, hD1 u hu, hD2 u hu]
      abel)
  have := hw b ⟨hb, by rw [hT0]; linarith⟩
  exact sub_eq_zero.1 this

end Thermal


end HRS.MS.MovLin

end
