import HRS.MS.MovLinAux3

/-!
# MOV-2c, part 2: the Volterra series on a scale of Banach spaces (`Σ^r`)

Infrastructure for S6.2 (`W:lem:r2mov-linear`, TeX L4278-4343), namespace `HRS.MS.MovLin`, helpers `mov2c_`.

## Setting (`Mov2cHyp`)

`X : ℝ → Type` a family of Banach spaces (`X r = Σ^r`; the intended realisation is `OscSpace d r`, or the
`MemOsc r`-functions modulo `L²`-null sets), with continuous linear embeddings `j h : X r → X r'` (`h : r' ≤ r`).
`Sm h t : X ρ → X σ` (`h : ρ ≤ σ`) stands for `e^{-tS_0}` regarded as an operator `Σ^ρ → Σ^σ`, and
`R r : X r → X (r - a)` for the perturbation `R = ν V_1 + P` (`0 ≤ a < 2`).  The hypotheses (`Mov2cHyp`) are
exactly what `MovLinAux2` (`mov_expS0_bound`, `_bounded`, `_continuous`, `_zero`, `_add`) and `MovOpAux` (`mov_P_bound`
for all real `r`) / `MovBridgeAux7` provide: `‖Sm h t‖ ≤ C t^{-(σ-ρ)/2}` (`0 < t ≤ T0`), strong continuity and
`Sm = id` at `t = 0` on each level, the semigroup law, compatibility of `Sm` and `R` with the embeddings
(all operators are restrictions of one operator on functions).  `mov2c_hyp_example` shows the hypotheses are
satisfiable.  The embeddings are assumed to satisfy `j (le_refl r) x = x` (field `j_refl`); injectivity and the
composition law of `j` are not needed.

## What is proved

For each level `r` (`Mov2cLevel`, from `mov2c_volterra` with `K(τ) = Sm(r-a → r)(τ) ∘ R r`,
`F(t) = Sm(r → r)(t)`, `θ = 1 - a/2`): `T_0(t) = e^{-tS_0}`, `T_{n+1}(t) x = -∫_0^t e^{-(t-s)S_0} R T_n(s) x ds`,
`‖T_n(t)‖ ≤ M (C t^{1-a/2})^n / Γ(1 + n(1-a/2))`, operator-norm convergence of `T = ∑ T_n` uniformly on
`[0,T0]`, strong continuity, the Duhamel equation `T(t) = e^{-tS_0} - ∫_0^t e^{-(t-s)S_0} R T(s) ds`, and uniqueness
among strongly continuous solutions (`mov2c_level_exists`).  `mov2c_level_compat`: the levels are
compatible (`j T_r = T_{r'} j`).  `mov2c_smoothing`: `T_ρ(t) : Σ^ρ → Σ^σ`, `‖·‖ ≤ C t^{-(σ-ρ)/2}` for
`0 ≤ σ - ρ < 2 - a`.  `mov2c_scale_volterra` packages the three.

## Scope and adjustments

* The series is constructed on `[0,T0]` only (the plan's "`0 < t ≤ 1`"; `T0 > 0` is a parameter).  Values for `t > T0`
  and the semigroup law are left to the consumer (semigroup law from uniqueness of the Duhamel equation).
* The full smoothing `Σ^{r-a} → Σ^r` (loss exactly `a`, relevant for `a ≥ 1`) follows from the semigroup law by
  splitting `[0,t]` into equal intervals; it is not proved here (only `σ - ρ < 2 - a`).
* `Sm` and `R` are given as bundled continuous linear maps between the Banach spaces.  Transport from the
  function-level `mov_expS0`, `mov_P` (`MemOsc`/`oscNorm`) to such maps is the consumer's step.
-/

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace HRS.MS.MovLin

/-! ## C. The scale layer -/

section Scale

variable {X : ℝ → Type} [∀ r, NormedAddCommGroup (X r)] [∀ r, NormedSpace ℝ (X r)]
  [∀ r, CompleteSpace (X r)]

/-- Hypotheses of the abstract theorem on a scale `X r` (`r ∈ ℝ`) with embeddings `j : X r → X r'`
(`r' ≤ r`).  `Sm h t : X ρ → X σ` (`h : ρ ≤ σ`) is the semigroup `e^{-tS_0}` regarded as an operator
`Σ^ρ → Σ^σ`, `R r : X r → X (r - a)` the perturbation. -/
structure Mov2cHyp (j : ∀ {r r' : ℝ}, r' ≤ r → X r →L[ℝ] X r') (a T0 : ℝ)
    (Sm : ∀ {ρ σ : ℝ}, ρ ≤ σ → ℝ → X ρ →L[ℝ] X σ) (R : ∀ r : ℝ, X r →L[ℝ] X (r - a)) : Prop where
  j_refl : ∀ r (x : X r), j (le_refl r) x = x
  zero : ∀ r (x : X r), Sm (le_refl r) 0 x = x
  cont : ∀ r (x : X r), ContinuousOn (fun t => Sm (le_refl r) t x) (Ici 0)
  semi : ∀ {ρ σ : ℝ} (h : ρ ≤ σ) (s τ : ℝ), 0 ≤ s → 0 < τ → ∀ y : X ρ,
    Sm (le_refl σ) s (Sm h τ y) = Sm h (s + τ) y
  bound : ∀ {ρ σ : ℝ} (h : ρ ≤ σ), ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) T0,
    ‖Sm h t‖ ≤ C * t ^ (-((σ - ρ) / 2))
  compS : ∀ {ρ σ ρ' σ' : ℝ} (h : ρ ≤ σ) (h' : ρ' ≤ σ') (hρ : ρ' ≤ ρ) (hσ : σ' ≤ σ) (t : ℝ),
    0 < t → ∀ x : X ρ, j hσ (Sm h t x) = Sm h' t (j hρ x)
  compR : ∀ {r r' : ℝ} (h : r' ≤ r) (x : X r), j (sub_le_sub_right h a) (R r x) = R r' (j h x)

variable {j : ∀ {r r' : ℝ}, r' ≤ r → X r →L[ℝ] X r'} {a T0 : ℝ}
  {Sm : ∀ {ρ σ : ℝ}, ρ ≤ σ → ℝ → X ρ →L[ℝ] X σ} {R : ∀ r : ℝ, X r →L[ℝ] X (r - a)}

/-- The smoothed semigroup is strongly continuous for `t > 0` (semigroup law + continuity at the level `σ`). -/
lemma mov2c_Sm_cont (H : Mov2cHyp j a T0 Sm R) {ρ σ : ℝ} (h : ρ ≤ σ) (y : X ρ) :
    ContinuousOn (fun τ => Sm h τ y) (Ioi 0) := by
  intro τ0 hτ0
  have hτ0' : (0 : ℝ) < τ0 := hτ0
  set τ1 : ℝ := τ0 / 2 with hτ1
  have hτ1p : 0 < τ1 := by positivity
  have hlt : τ1 < τ0 := by linarith
  set w : X σ := Sm h τ1 y with hw
  have hcont : ContinuousOn (fun τ => Sm (le_refl σ) (τ - τ1) w) (Ici τ1) := by
    have := (H.cont σ w).comp (continuousOn_id.sub continuousOn_const) (s := Ici τ1)
      (t := Ici 0) (fun τ hτ => mem_Ici.2 (sub_nonneg.2 (mem_Ici.1 hτ)))
    exact this
  have heq : ∀ τ ∈ Ici τ1, Sm h τ y = Sm (le_refl σ) (τ - τ1) w := by
    intro τ hτ
    rw [hw, H.semi h (τ - τ1) τ1 (sub_nonneg.2 (mem_Ici.1 hτ)) hτ1p y]
    congr 2; ring
  have hcI : ContinuousOn (fun τ => Sm h τ y) (Ici τ1) := hcont.congr heq
  have hnhds : Ici τ1 ∈ 𝓝 τ0 := Ici_mem_nhds hlt
  exact (hcI.continuousAt hnhds).continuousWithinAt

/-- The Volterra kernel `K(τ) = e^{-τS_0} R : Σ^r → Σ^r` at level `r` (`τ ↦ Sm (r-a → r) τ ∘ R r`). -/
def mov2c_K {a : ℝ} (Sm : ∀ {ρ σ : ℝ}, ρ ≤ σ → ℝ → X ρ →L[ℝ] X σ) (R : ∀ r : ℝ, X r →L[ℝ] X (r - a))
    (ha : 0 ≤ a) (r τ : ℝ) : X r →L[ℝ] X r :=
  (Sm (sub_le_self r ha) τ).comp (R r)

lemma mov2c_K_ker (H : Mov2cHyp j a T0 Sm R) (ha0 : 0 ≤ a) (r : ℝ) :
    ∃ Kc : ℝ, Mov2cKer (mov2c_K Sm R ha0 r) T0 Kc (1 - a / 2) := by
  obtain ⟨C, hC0, hC⟩ := H.bound (sub_le_self r ha0)
  refine ⟨C * ‖R r‖, ⟨mul_nonneg hC0 (norm_nonneg _), ?_, ?_⟩⟩
  · intro y
    exact (mov2c_Sm_cont H (sub_le_self r ha0) (R r y)).mono (fun τ hτ => hτ.1)
  · intro τ hτ
    have e : -((r - (r - a)) / 2) = 1 - a / 2 - 1 := by ring
    calc ‖mov2c_K Sm R ha0 r τ‖ ≤ ‖Sm (sub_le_self r ha0) τ‖ * ‖R r‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * τ ^ (-((r - (r - a)) / 2))) * ‖R r‖ :=
          mul_le_mul_of_nonneg_right (hC τ hτ) (norm_nonneg _)
      _ = C * ‖R r‖ * τ ^ (1 - a / 2 - 1) := by rw [e]; ring

lemma mov2c_F_props (H : Mov2cHyp j a T0 Sm R) (r : ℝ) :
    (∀ x, ContinuousOn (fun t => Sm (le_refl r) t x) (Icc 0 T0)) ∧
      ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) T0, ‖Sm (le_refl r) t‖ ≤ M := by
  refine ⟨fun x => (H.cont r x).mono (fun t ht => ht.1), ?_⟩
  obtain ⟨C, hC0, hC⟩ := H.bound (le_refl r)
  refine ⟨max C 1, fun t ht => ?_⟩
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    have : Sm (le_refl r) 0 = 1 := ContinuousLinearMap.ext (fun x => H.zero r x)
    rw [this]
    exact (ContinuousLinearMap.norm_id_le).trans (le_max_right _ _)
  · have := hC t ⟨hpos, ht.2⟩
    simpa using this.trans (le_max_left _ _)

/-- The Volterra series at a fixed level `r`: `T = ∑ T_n` with `T_0(t) = e^{-tS_0}`,
`T_{n+1}(t) x = -∫_0^t e^{-(t-s)S_0} R T_n(s) x ds`. -/
structure Mov2cLevel {a : ℝ} (T0 : ℝ) (Sm : ∀ {ρ σ : ℝ}, ρ ≤ σ → ℝ → X ρ →L[ℝ] X σ)
    (R : ∀ r : ℝ, X r →L[ℝ] X (r - a)) (ha : 0 ≤ a) (r : ℝ)
    (Tn : ℕ → ℝ → X r →L[ℝ] X r) (T : ℝ → X r →L[ℝ] X r) : Prop where
  zero : ∀ t ∈ Icc (0 : ℝ) T0, Tn 0 t = Sm (le_refl r) t
  succ : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T0, ∀ x,
    Tn (n + 1) t x = -∫ s in (0 : ℝ)..t, Sm (sub_le_self r ha) (t - s) (R r (Tn n s x))
  bound : ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T0,
    ‖Tn n t‖ ≤ M * (C * t ^ (1 - a / 2)) ^ n / Real.Gamma (1 + n * (1 - a / 2))
  cont_n : ∀ n : ℕ, ∀ x, ContinuousOn (fun t => Tn n t x) (Icc 0 T0)
  hasSum : ∀ t ∈ Icc (0 : ℝ) T0, HasSum (fun n => Tn n t) (T t)
  unif : TendstoUniformlyOn (fun (N : Finset ℕ) t => ∑ n ∈ N, Tn n t) T atTop (Icc 0 T0)
  norm_le : ∃ N : ℝ, ∀ t ∈ Icc (0 : ℝ) T0, ‖T t‖ ≤ N
  cont : ∀ x, ContinuousOn (fun t => T t x) (Icc 0 T0)
  duhamel : ∀ t ∈ Icc (0 : ℝ) T0, ∀ x,
    T t x = Sm (le_refl r) t x - ∫ s in (0 : ℝ)..t, Sm (sub_le_self r ha) (t - s) (R r (T s x))
  unique : ∀ U : ℝ → X r →L[ℝ] X r, (∀ x, ContinuousOn (fun t => U t x) (Icc 0 T0)) →
    (∀ t ∈ Icc (0 : ℝ) T0, ∀ x, U t x =
      Sm (le_refl r) t x - ∫ s in (0 : ℝ)..t, Sm (sub_le_self r ha) (t - s) (R r (U s x))) →
    ∀ t ∈ Icc (0 : ℝ) T0, U t = T t

lemma mov2c_level_exists (H : Mov2cHyp j a T0 Sm R) (ha0 : 0 ≤ a) (ha2 : a < 2) (hT0 : 0 < T0)
    (r : ℝ) : ∃ (Tn : ℕ → ℝ → X r →L[ℝ] X r) (T : ℝ → X r →L[ℝ] X r),
      Mov2cLevel T0 Sm R ha0 r Tn T := by
  obtain ⟨Kc, hK⟩ := mov2c_K_ker H ha0 r
  obtain ⟨hFc, M, hM⟩ := mov2c_F_props H r
  have hθ : 0 < 1 - a / 2 := by linarith
  have hθ1 : 1 - a / 2 ≤ 1 := by linarith
  obtain ⟨Tn, T, h0, hsucc, hbd, hcn, hHS, hun, hnb, hc, hd, hu⟩ :=
    mov2c_volterra hK hθ hθ1 hT0.le hFc hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT0.le⟩)
  have hc0 : 0 ≤ Kc * Real.Gamma (1 - a / 2) :=
    mul_nonneg hK.Kc_nonneg (Real.Gamma_pos_of_pos hθ).le
  refine ⟨Tn, T, ⟨h0, hsucc, ⟨M, Kc * Real.Gamma (1 - a / 2), hM0, hc0, ?_⟩, hcn, hHS, hun,
    ⟨_, hnb⟩, hc, hd, hu⟩⟩
  intro n t ht
  refine (hbd n t ht).trans (le_of_eq ?_)
  rw [mul_pow, mov2c_pow_rpow ht.1 n]; ring

lemma mov2c_integrable (H : Mov2cHyp j a T0 Sm R) (ha0 : 0 ≤ a) (ha2 : a < 2) (r : ℝ)
    {y : ℝ → X r} (hy : ContinuousOn y (Icc 0 T0)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T0) :
    IntervalIntegrable (fun s => Sm (sub_le_self r ha0) (t - s) (R r (y s))) volume 0 t := by
  obtain ⟨Kc, hK⟩ := mov2c_K_ker H ha0 r
  exact mov2c_vol_int hK (by linarith) (by linarith) hy ht

theorem mov2c_level_compat (H : Mov2cHyp j a T0 Sm R) (ha0 : 0 ≤ a) (ha2 : a < 2) {r r' : ℝ}
    (h : r' ≤ r) {Tn : ℕ → ℝ → X r →L[ℝ] X r} {T : ℝ → X r →L[ℝ] X r}
    {Tn' : ℕ → ℝ → X r' →L[ℝ] X r'} {T' : ℝ → X r' →L[ℝ] X r'}
    (L : Mov2cLevel T0 Sm R ha0 r Tn T) (L' : Mov2cLevel T0 Sm R ha0 r' Tn' T') :
    ∀ t ∈ Icc (0 : ℝ) T0, ∀ x, j h (T t x) = T' t (j h x) := by
  have hA : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T0, ∀ x, j h (Tn n t x) = Tn' n t (j h x) := by
    intro n
    induction n with
    | zero =>
      intro t ht x
      rw [L.zero t ht, L'.zero t ht]
      rcases ht.1.eq_or_lt with h0 | hpos
      · subst h0
        rw [H.zero, H.zero]
      · exact H.compS (le_refl r) (le_refl r') h h t hpos x
    | succ n ih =>
      intro t ht x
      rw [L.succ n t ht x, L'.succ n t ht (j h x), map_neg,
        ← ContinuousLinearMap.intervalIntegral_comp_comm _
          (mov2c_integrable H ha0 ha2 r (L.cont_n n x) ht)]
      congr 1
      refine intervalIntegral.integral_congr_ae ?_
      have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({t} : Set ℝ) :=
        (Set.finite_singleton t).countable.ae_notMem _
      refine hae.mono (fun s hs hsI => ?_)
      rw [uIoc_of_le ht.1] at hsI
      have hst : s < t := lt_of_le_of_ne hsI.2 hs
      have hsI' : s ∈ Icc (0 : ℝ) T0 := ⟨hsI.1.le, hsI.2.trans ht.2⟩
      rw [H.compS (sub_le_self r ha0) (sub_le_self r' ha0) (sub_le_sub_right h a) h (t - s)
        (by linarith) (R r (Tn n s x)), H.compR h, ih s hsI' x]
  intro t ht x
  have h1 := (L.hasSum t ht).mapL (ContinuousLinearMap.apply ℝ (X r) x)
  have h2 := h1.mapL (j h)
  have h3 := (L'.hasSum t ht).mapL (ContinuousLinearMap.apply ℝ (X r') (j h x))
  refine HasSum.unique h2 ?_
  simp only [ContinuousLinearMap.apply_apply] at h3 ⊢
  simp only [hA _ t ht x]
  exact h3

/-- **Smoothing** `Σ^ρ → Σ^σ` for `0 ≤ σ - ρ < 2 - a`: `T(t) x = j z` with `z ∈ Σ^σ`,
`‖z‖ ≤ C t^{-(σ-ρ)/2} ‖x‖`, `0 < t ≤ T0`. -/
theorem mov2c_smoothing (H : Mov2cHyp j a T0 Sm R) (ha0 : 0 ≤ a) (ha2 : a < 2) (hT0 : 0 < T0)
    {ρ σ : ℝ} (h : ρ ≤ σ) (hb : σ - ρ < 2 - a)
    {Tn : ℕ → ℝ → X ρ →L[ℝ] X ρ} {T : ℝ → X ρ →L[ℝ] X ρ} (L : Mov2cLevel T0 Sm R ha0 ρ Tn T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) T0, ∀ x : X ρ, ∃ z : X σ, j h z = T t x ∧
      ‖z‖ ≤ C * t ^ (-((σ - ρ) / 2)) * ‖x‖ := by
  have hρa : ρ - a ≤ σ := (sub_le_self ρ ha0).trans h
  obtain ⟨C1, hC10, hC1⟩ := H.bound h
  obtain ⟨C2, hC20, hC2⟩ := H.bound hρa
  obtain ⟨N, hN⟩ := L.norm_le
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 ⟨le_rfl, hT0.le⟩)
  set θ' : ℝ := 1 - (σ - ρ + a) / 2 with hθ'
  have hθ'0 : 0 < θ' := by linarith
  have hθ'1 : θ' ≤ 1 := by linarith [sub_nonneg.2 h]
  have hK' : Mov2cKer (fun τ => Sm hρa τ) T0 C2 θ' := by
    refine ⟨hC20, fun y => (mov2c_Sm_cont H hρa y).mono (fun τ hτ => hτ.1), fun τ hτ => ?_⟩
    have e : -((σ - (ρ - a)) / 2) = θ' - 1 := by rw [hθ']; ring
    have := hC2 τ hτ
    rwa [e] at this
  set Cq : ℝ := ‖R ρ‖ * N * C2 * (Real.Gamma θ' / Real.Gamma (1 + θ')) * T0 ^ (1 - a / 2) with hCq
  have hGa : 0 < Real.Gamma θ' := Real.Gamma_pos_of_pos hθ'0
  have hGb : 0 < Real.Gamma (1 + θ') := Real.Gamma_pos_of_pos (by linarith)
  refine ⟨C1 + Cq, add_nonneg hC10 (by positivity), fun t ht x => ?_⟩
  have htI : t ∈ Icc (0 : ℝ) T0 := ⟨ht.1.le, ht.2⟩
  set y : ℝ → X (ρ - a) := fun s => R ρ (T s x) with hy
  have hyc : ContinuousOn y (Icc 0 T0) := (R ρ).continuous.comp_continuousOn (L.cont x)
  have hint : IntervalIntegrable (fun s => Sm hρa (t - s) (y s)) volume 0 t :=
    mov2c_vol_int hK' hθ'0 hθ'1 hyc htI
  refine ⟨Sm h t x - ∫ s in (0 : ℝ)..t, Sm hρa (t - s) (y s), ?_, ?_⟩
  · -- the embedding of `z` is `T t x`
    rw [map_sub, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint, L.duhamel t htI x]
    congr 1
    · rw [H.compS h (le_refl ρ) (le_refl ρ) h t ht.1 x, H.j_refl]
    · refine intervalIntegral.integral_congr_ae ?_
      have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({t} : Set ℝ) :=
        (Set.finite_singleton t).countable.ae_notMem _
      refine hae.mono (fun s hs hsI => ?_)
      rw [uIoc_of_le ht.1.le] at hsI
      have hst : s < t := lt_of_le_of_ne hsI.2 hs
      rw [H.compS hρa (sub_le_self ρ ha0) (le_refl (ρ - a)) h (t - s) (by linarith) (y s),
        H.j_refl]
  · have hA : 0 ≤ ‖R ρ‖ * N * ‖x‖ := by positivity
    have hnorm := mov2c_integral_norm_le (v := fun s => Sm hρa (t - s) (y s)) (t := t) (Kc := C2)
      (A := ‖R ρ‖ * N * ‖x‖) (θ := θ') hθ'0 hC20 hA 0 ht.1.le (by
        intro s hs
        have hτ : t - s ∈ Ioc (0 : ℝ) T0 := ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
        have hsI : s ∈ Icc (0 : ℝ) T0 := ⟨hs.1.le, hs.2.le.trans ht.2⟩
        have e1 : (s ^ (((0 : ℕ) : ℝ) * θ') / Real.Gamma (1 + ((0 : ℕ) : ℝ) * θ')) = 1 := by simp
        simp only [Nat.cast_zero, zero_mul, Real.rpow_zero, add_zero, Real.Gamma_one, div_one,
          mul_one]
        have hb1 := hK'.bound (t - s) hτ
        calc ‖Sm hρa (t - s) (y s)‖ ≤ ‖Sm hρa (t - s)‖ * ‖y s‖ := (Sm hρa (t - s)).le_opNorm _
          _ ≤ (C2 * (t - s) ^ (θ' - 1)) * (‖R ρ‖ * N * ‖x‖) := by
            apply mul_le_mul hb1 _ (norm_nonneg _) (mul_nonneg hC20 (Real.rpow_nonneg (by linarith [hs.2]) _))
            calc ‖y s‖ ≤ ‖R ρ‖ * ‖T s x‖ := (R ρ).le_opNorm _
              _ ≤ ‖R ρ‖ * (N * ‖x‖) := by
                apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                exact ((T s).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hN s hsI) (norm_nonneg _))
              _ = ‖R ρ‖ * N * ‖x‖ := by ring)
    simp only [Nat.cast_zero, zero_add, one_mul] at hnorm
    have hGt : t ^ θ' ≤ T0 ^ (1 - a / 2) * t ^ (-((σ - ρ) / 2)) := by
      have e : θ' = (1 - a / 2) + (-((σ - ρ) / 2)) := by rw [hθ']; ring
      rw [e, Real.rpow_add ht.1]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.1.le _)
      exact Real.rpow_le_rpow ht.1.le ht.2 (by linarith)
    have hSm := hC1 t ht
    calc ‖Sm h t x - ∫ s in (0 : ℝ)..t, Sm hρa (t - s) (y s)‖
        ≤ ‖Sm h t x‖ + ‖∫ s in (0 : ℝ)..t, Sm hρa (t - s) (y s)‖ := norm_sub_le _ _
      _ ≤ (C1 * t ^ (-((σ - ρ) / 2))) * ‖x‖ +
          (‖R ρ‖ * N * ‖x‖ * C2 * Real.Gamma θ' * t ^ θ' / Real.Gamma (1 + θ')) := by
        gcongr
        · exact ((Sm h t).le_opNorm x).trans (mul_le_mul_of_nonneg_right hSm (norm_nonneg _))
      _ ≤ (C1 * t ^ (-((σ - ρ) / 2))) * ‖x‖ +
          (‖R ρ‖ * N * ‖x‖ * C2 * (Real.Gamma θ' / Real.Gamma (1 + θ')) *
            (T0 ^ (1 - a / 2) * t ^ (-((σ - ρ) / 2)))) := by
        have : ‖R ρ‖ * N * ‖x‖ * C2 * Real.Gamma θ' * t ^ θ' / Real.Gamma (1 + θ') =
            ‖R ρ‖ * N * ‖x‖ * C2 * (Real.Gamma θ' / Real.Gamma (1 + θ')) * t ^ θ' := by ring
        rw [this]
        gcongr
      _ = (C1 + Cq) * t ^ (-((σ - ρ) / 2)) * ‖x‖ := by rw [hCq]; ring

lemma Mov2cLevel.at_zero {ha : 0 ≤ a} {r : ℝ} {Tn : ℕ → ℝ → X r →L[ℝ] X r} {T : ℝ → X r →L[ℝ] X r}
    (H : Mov2cHyp j a T0 Sm R) (hT0 : 0 ≤ T0) (L : Mov2cLevel T0 Sm R ha r Tn T) (x : X r) :
    T 0 x = x := by
  rw [L.duhamel 0 ⟨le_rfl, hT0⟩ x, H.zero]
  simp

/-- **The Volterra series on the scale.**  Under `Mov2cHyp` (`0 ≤ a < 2`, `T0 > 0`): for every level `r` the
series `T_r = ∑ T_n` (`Mov2cLevel`: operator-norm convergence uniform on `[0,T0]`, bounds
`M (C t^{1-a/2})^n / Γ(1 + n(1-a/2))`, strong continuity, the Duhamel equation, uniqueness among strongly continuous
solutions); the levels are compatible (`j T_r = T_{r'} j`); and `T_ρ(t) : Σ^ρ → Σ^σ` with
`‖·‖ ≤ C t^{-(σ-ρ)/2}` for `0 ≤ σ - ρ < 2 - a`. -/
theorem mov2c_scale_volterra (H : Mov2cHyp j a T0 Sm R) (ha0 : 0 ≤ a) (ha2 : a < 2) (hT0 : 0 < T0) :
    ∃ (Tn : ∀ r : ℝ, ℕ → ℝ → X r →L[ℝ] X r) (T : ∀ r : ℝ, ℝ → X r →L[ℝ] X r),
      (∀ r, Mov2cLevel T0 Sm R ha0 r (Tn r) (T r)) ∧
      (∀ (r r' : ℝ) (h : r' ≤ r), ∀ t ∈ Icc (0 : ℝ) T0, ∀ x, j h (T r t x) = T r' t (j h x)) ∧
      (∀ (ρ σ : ℝ) (h : ρ ≤ σ), σ - ρ < 2 - a → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) T0,
        ∀ x : X ρ, ∃ z : X σ, j h z = T ρ t x ∧ ‖z‖ ≤ C * t ^ (-((σ - ρ) / 2)) * ‖x‖) := by
  have hex := fun r => mov2c_level_exists H ha0 ha2 hT0 r
  choose Tn T hL using hex
  exact ⟨Tn, T, hL, fun r r' h t ht x => mov2c_level_compat H ha0 ha2 h (hL r) (hL r') t ht x,
    fun ρ σ h hb => mov2c_smoothing H ha0 ha2 hT0 h hb (hL ρ)⟩

end Scale

/-- Non-vacuity of `Mov2cHyp`: the trivial scale `X r = ℝ`, `j = id`, `S(t) = e^{-t}`, `R = 0`, `T0 = 1`. -/
lemma mov2c_hyp_example :
    Mov2cHyp (X := fun _ : ℝ => ℝ) (fun {_ _} _ => ContinuousLinearMap.id ℝ ℝ) 0 1
      (fun {_ _} _ t => Real.exp (-t) • ContinuousLinearMap.id ℝ ℝ) (fun _ => 0) where
  j_refl := fun r x => rfl
  zero := fun r x => by simp
  cont := fun r x => by
    refine Continuous.continuousOn ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    fun_prop
  semi := fun h s τ hs hτ y => by
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  bound := fun {ρ σ} h => by
    refine ⟨1, zero_le_one, fun t ht => ?_⟩
    have h1 : ‖Real.exp (-t) • ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 := by
      refine (norm_smul_le (Real.exp (-t)) (ContinuousLinearMap.id ℝ ℝ)).trans ?_
      have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [ht.1])
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-t) * ‖ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 * 1 :=
            mul_le_mul this ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
        _ = 1 := by ring
    have h2 : (1 : ℝ) ≤ t ^ (-((σ - ρ) / 2)) := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2
      linarith [sub_nonneg.2 h]
    linarith
  compS := fun h h' hρ hσ t ht x => rfl
  compR := fun h x => by simp

end HRS.MS.MovLin
