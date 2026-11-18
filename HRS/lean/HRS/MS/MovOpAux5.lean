import HRS.MS.MovOpAux4

/-!
# MOV-C2 (2): thermal data, Gaussian-class bookkeeping, local profiles of `B`

Namespace `HRS.MS.MovC2`, helper prefix `movc2_`.  Infrastructure for S6.1 (`docs/MOV_PLAN.md`, step 10).

* `MovC2Data d ρ q' B`: the thermal inputs (`ρ > 0`, `√ρ` Gaussian class, `∇log ρ = -q'x + B`, `B ∈ C_b^N` all `N`),
  obtained for a thermal equilibrium by `movc2_data` (`q' = βq`).
* `movc2_prof1`, `movc2_prof2`: weighted profiles `x^w ∂_i(√ρ w)`, `x^w Δ(√ρ w)` in `H^r`, `‖·‖ ≲ ‖w‖_{Σ^{r+1}}`, `Σ^{r+2}`
  (Gaussian multipliers and `movc2_B1`).
* `movc2_force_wt`: `‖Q^K F^loc_i‖`, `‖Q^K x_i F^loc_i‖`, `‖Q^K G^loc‖` in `H^σ`, `σ ≤ m-2+d-s`.
* `movc2_alg` (real-index Sobolev algebra in the `movc2_SB` form), `movc2_decay` (`B2` with `(1+‖x‖²)^{-K}`).
* `movc2_local`: the local part `L` of `B(v,w)` (kernel `θ g`) is bounded `Σ^m × Σ^m → Σ^{m-a}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovC2

open HRS.Whole HRS.MS.MovOsc HRS.MS.Mov0 HRS.MS.MovForce HRS.MS.MovC1 HRS.PDE.ToolboxRd
  HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-! ### Thermal data -/

/-- The thermal inputs for `B`: `ρ > 0` smooth, `ψ = √ρ` of Gaussian class, `∇ log ρ = -q' x + B` with
`B ∈ C_b^N` for all `N`. -/
structure MovC2Data (d : ℕ) (ρ : Euc d → ℝ) (q' : ℝ) (B : Euc d → Euc d) : Prop where
  rho : MovRhoData d ρ
  psiG : MovcG (fun y => Real.sqrt (ρ y))
  grad : ∀ x, gradient (fun y => Real.log (ρ y)) x = -q' • x + B x
  cb : ∀ N : ℕ, ∃ Mb : ℝ, HasCbBound N Mb B

theorem movc2_data (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hb : 0 < β)
    {ρ : Euc d → ℝ} (h : IsThermalEquilibrium d s q β ρ) :
    ∃ B : Euc d → Euc d, MovC2Data d ρ (β * q) B := by
  obtain ⟨B, -, hR, hcb⟩ := mv0_gapref hd hs0 hsd hq hb h
  obtain ⟨hsm, hgrad, c, hc, hψ⟩ := mv0_sqrt_gauss (mul_pos hb hq) hR
  exact ⟨B, ⟨⟨hR.pos, hR.smooth, fun k => by obtain ⟨C, hC⟩ := hψ k; exact ⟨C, c, hc, hC⟩⟩,
    ⟨hsm, c, hc, hψ⟩, hgrad, hcb⟩⟩

/-! ### Gaussian-class bookkeeping -/

lemma movc2_G_bdd {f : Euc d → ℝ} (hf : MovcG f) : Continuous f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B := by
  obtain ⟨hs, c, hc, hk⟩ := hf
  obtain ⟨C, hC⟩ := hk 0
  refine ⟨hs.continuous, |C|, fun x => ?_⟩
  have h1 := hC x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
  have h2 : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖x‖]
  calc |f x| ≤ C * Real.exp (-c * ‖x‖ ^ 2) := h1
    _ ≤ |C| * Real.exp (-c * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |C| := mul_one _

lemma movc2_G_xmul {f : Euc d → ℝ} (hf : MovcG f) (j : Fin d) : MovcG (fun x => x j * f x) := by
  have hb : ContDiff ℝ ∞ (fun x : Euc d => x j) := (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  refine movc1_G_mul hf hb (fun k => ⟨1, zero_le_one, fun x => ?_⟩)
  have hn : ‖(EuclideanSpace.proj (𝕜 := ℝ) j : Euc d →L[ℝ] ℝ)‖ ≤ 1 := movb2_norm_proj_le j
  cases k with
  | zero =>
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have := mova3b2_abs_coord_le j x
    linarith
  | succ k =>
    have := mov0_clm_iter (EuclideanSpace.proj (𝕜 := ℝ) j : Euc d →L[ℝ] ℝ) k x
    have e : (fun x : Euc d => x j) = ⇑(EuclideanSpace.proj (𝕜 := ℝ) j) := rfl
    rw [e]
    nlinarith [norm_nonneg x]

lemma movc2_G_mon {f : Euc d → ℝ} (hf : MovcG f) : ∀ w : List (Fin d),
    MovcG (fun x => movc2_mon w x * f x) := by
  intro w
  induction w with
  | nil => simpa [movc2_mon_nil] using hf
  | cons j w ih =>
    have := movc2_G_xmul ih j
    refine (show (fun x => x j * (movc2_mon w x * f x)) = fun x => movc2_mon (j :: w) x * f x from ?_) ▸ this
    funext x; rw [movc2_mon_cons]; ring

lemma movc2_Q_const (c : ℝ) : ∀ {n m : ℕ} {A : ℝ}, |c| ≤ A → m = 0 →
    mova3b2_Q n m A (fun _ : Euc d => c) := by
  intro n
  induction n with
  | zero => intro m A hA hm x; subst hm; simpa using hA
  | succ n ih =>
    intro m A hA hm
    refine ⟨fun x => ?_, fun j => ?_⟩
    · subst hm; simpa using hA
    · have e : mova3b1_Dj j (fun _ : Euc d => c) = 0 := by
        funext x; simp [mova3b1_Dj]
      rw [e]
      exact mova3b2_Q_zero ((abs_nonneg c).trans hA)

/-- `B1` for a Gaussian-class multiplier, `r ≥ 0`. -/
lemma movc2_B1G {om : Euc d → ℝ} (hom : MovcG om) {r : ℝ} (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : 𝓢R, movc2_SB r (C * oscNorm r v) (fun x => om x * v x) := by
  obtain ⟨C, hC, hB⟩ := movc2_B1 (d := d) hr
  obtain ⟨A, hA⟩ := movc1_G_Q hom ⌈r⌉₊ 0
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (mova3b2_Q_abs hA 0)
  obtain ⟨φ, hφ⟩ := movc1_G_schwartz hom
  have htg : om.HasTemperateGrowth := by rw [← hφ]; exact φ.hasTemperateGrowth
  refine ⟨C * A, mul_nonneg hC hA0, fun v => ?_⟩
  exact hB A hA0 om htg hA v

/-- `B1` without multiplier: `Σ^r ⊂ H^r` on Schwartz functions. -/
lemma movc2_B1_one {r : ℝ} (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : 𝓢R, movc2_SB r (C * oscNorm r v) (⇑v) := by
  obtain ⟨C, hC, hB⟩ := movc2_B1 (d := d) hr
  refine ⟨C * 1, by positivity, fun v => ?_⟩
  have := hB 1 zero_le_one (fun _ => 1) (Function.HasTemperateGrowth.const 1)
    (movc2_Q_const 1 (by simp) rfl) v
  simpa using this

/-! ### Profiles of `B` -/

/-- `h = √ρ w`. -/
def movc2_h (ρ : Euc d → ℝ) (w : 𝓢R) : Euc d → ℝ := fun y => Real.sqrt (ρ y) * w y

/-- Continuous and bounded. -/
def movc2_CB (f : Euc d → ℝ) : Prop := Continuous f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B

lemma movc2_CB_add {f g : Euc d → ℝ} (hf : movc2_CB f) (hg : movc2_CB g) :
    movc2_CB (fun x => f x + g x) := by
  obtain ⟨hf1, B1, hB1⟩ := hf
  obtain ⟨hg1, B2, hB2⟩ := hg
  exact ⟨hf1.add hg1, B1 + B2, fun x => (abs_add_le _ _).trans (add_le_add (hB1 x) (hB2 x))⟩

lemma movc2_CB_smul (c : ℝ) {f : Euc d → ℝ} (hf : movc2_CB f) : movc2_CB (fun x => c * f x) := by
  obtain ⟨hf1, B1, hB1⟩ := hf
  exact ⟨continuous_const.mul hf1, |c| * B1, fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB1 x) (abs_nonneg _)⟩

lemma movc2_CB_G_mul {om : Euc d → ℝ} (hom : MovcG om) (φ : 𝓢R) : movc2_CB (fun x => om x * φ x) := by
  obtain ⟨h1, B1, hB1⟩ := movc2_G_bdd hom
  obtain ⟨M, hM⟩ := mv1_schwartz_bdd φ 0
  refine ⟨h1.mul φ.continuous, B1 * M, fun x => ?_⟩
  have h2 : |φ x| ≤ M := by
    have := hM x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  rw [abs_mul]
  exact mul_le_mul (hB1 x) h2 (abs_nonneg _) ((abs_nonneg _).trans (hB1 x))

/-- Derivative of `√ρ w` in the direction `e_i`. -/
lemma movc2_Dh {ρ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ (fun y => Real.sqrt (ρ y))) (i : Fin d) (w : 𝓢R) :
    mova3b1_Dj i (movc2_h ρ w) = fun y => mova3b1_Dj i (fun z => Real.sqrt (ρ z)) y * w y +
      Real.sqrt (ρ y) * mova3b1_Dj i (⇑w) y := by
  funext y
  exact mova3b1_Dj_mul i ((hψ.differentiable (by simp)) y) (((w.smooth ⊤).differentiable (by simp)) y)

lemma movc2_DDh {ρ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ (fun y => Real.sqrt (ρ y))) (i : Fin d) (w : 𝓢R) :
    mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) = fun y =>
      mova3b1_Dj i (mova3b1_Dj i (fun z => Real.sqrt (ρ z))) y * w y +
      2 * (mova3b1_Dj i (fun z => Real.sqrt (ρ z)) y * mova3b1_Dj i (⇑w) y) +
      Real.sqrt (ρ y) * mova3b1_Dj i (mova3b1_Dj i (⇑w)) y := by
  have hw : ContDiff ℝ ∞ (⇑w) := w.smooth ⊤
  have h1 := mova3b2_contDiff_Dj i hψ
  have h2 := mova3b2_contDiff_Dj i hw
  rw [movc2_Dh hψ i w]
  have hU : ContDiff ℝ ∞ (fun y => mova3b1_Dj i (fun z => Real.sqrt (ρ z)) y * w y) := h1.mul hw
  have hV : ContDiff ℝ ∞ (fun y => Real.sqrt (ρ y) * mova3b1_Dj i (⇑w) y) := hψ.mul h2
  have e : (fun y => mova3b1_Dj i (fun z => Real.sqrt (ρ z)) y * w y +
      Real.sqrt (ρ y) * mova3b1_Dj i (⇑w) y) =
      (fun y => mova3b1_Dj i (fun z => Real.sqrt (ρ z)) y * w y) +
        (fun y => Real.sqrt (ρ y) * mova3b1_Dj i (⇑w) y) := rfl
  rw [e, mova3b2_Dj_add i hU hV]
  funext y
  simp only [Pi.add_apply]
  rw [mova3b1_Dj_mul i ((h1.differentiable (by simp)) y) ((hw.differentiable (by simp)) y),
    mova3b1_Dj_mul i ((hψ.differentiable (by simp)) y) ((h2.differentiable (by simp)) y)]
  ring

/-- Uniform constants over the (finitely many) words of length `≤ n`. -/
lemma movc2_word_const (n : ℕ) (P : List (Fin d) → ℝ → Prop)
    (hmono : ∀ v C C', C ≤ C' → P v C → P v C') (h : ∀ v, ∃ C : ℝ, 0 ≤ C ∧ P v C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : List (Fin d), v.length ≤ n → P v C := by
  classical
  choose Cf hCf0 hCf using h
  have hfin : {l : List (Fin d) | l.length ≤ n}.Finite := List.finite_length_le (Fin d) n
  refine ⟨∑ v ∈ hfin.toFinset, Cf v, Finset.sum_nonneg fun v _ => hCf0 v, fun v hv => ?_⟩
  refine hmono v (Cf v) _ ?_ (hCf v)
  exact Finset.single_le_sum (f := Cf) (fun v _ => hCf0 v) (hfin.mem_toFinset.2 hv)

lemma movc2_coe_D (i : Fin d) (w : 𝓢R) : ⇑(mova1_D i w) = mova3b1_Dj i (⇑w) := by
  funext x; simp [mova3b1_Dj]

lemma movc2_osc_D (r : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (f : 𝓢R),
    oscNorm r (⇑(mova1_D i f)) ≤ C * oscNorm (r + 1) f := by
  obtain ⟨C, hC, h⟩ := mo_partial (d := d) r
  refine ⟨C, hC, fun i f => ?_⟩
  have := (h i f).2
  have e : (⇑(mova1_D i f)) = fun x => fderiv ℝ (⇑f) x (EuclideanSpace.single i (1 : ℝ)) := by
    funext x; simp
  rw [e]; exact this

lemma movc2_osc_mono_r {r : ℝ} (f : 𝓢R) (k : ℝ) (hk : 0 ≤ k) : oscNorm r f ≤ oscNorm (r + k) f :=
  (mo_mono (by linarith) (memOsc_schwartz (r + k) f)).2

/-- **First profile.**  `x^w ∂_i(√ρ w)` has `H^r` norm `≲ ‖w‖_{Σ^{r+1}}`, uniformly in the words `w`, `|w| ≤ n`. -/
lemma movc2_prof1 {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B) (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : 𝓢R, movc2_Reg n (mova3b1_Dj i (movc2_h ρ w)) ∧
      movc2_WB n r (C * oscNorm (r + 1) w) (mova3b1_Dj i (movc2_h ρ w)) := by
  have hψ : MovcG (fun y => Real.sqrt (ρ y)) := D.psiG
  have hψs : ContDiff ℝ ∞ (fun y => Real.sqrt (ρ y)) := hψ.1
  have hDψ : MovcG (mova3b1_Dj i (fun y => Real.sqrt (ρ y))) := movc1_G_Dj hψ i
  obtain ⟨Cd, hCd, hDosc⟩ := movc2_osc_D (d := d) r
  have hword : ∀ v : List (Fin d), ∃ C : ℝ, 0 ≤ C ∧ ∀ w : 𝓢R,
      movc2_SB r (C * oscNorm (r + 1) w) (fun x => movc2_mon v x * mova3b1_Dj i (movc2_h ρ w) x) := by
    intro v
    obtain ⟨C1, hC1, h1⟩ := movc2_B1G (movc2_G_mon hDψ v) hr
    obtain ⟨C2, hC2, h2⟩ := movc2_B1G (movc2_G_mon hψ v) hr
    refine ⟨C1 + C2 * Cd, by positivity, fun w => ?_⟩
    have e : (fun x => movc2_mon v x * mova3b1_Dj i (movc2_h ρ w) x) = fun x =>
        movc2_mon v x * mova3b1_Dj i (fun y => Real.sqrt (ρ y)) x * w x +
          movc2_mon v x * Real.sqrt (ρ x) * (mova1_D i w) x := by
      funext x
      rw [movc2_Dh hψs i w, movc2_coe_D]
      ring
    rw [e]
    have t1 := movc2_SB_mono_E (h1 w) (mul_le_mul_of_nonneg_left
      (movc2_osc_mono_r (r := r) w 1 zero_le_one) hC1)
    have t2 := movc2_SB_mono_E (h2 (mova1_D i w)) (mul_le_mul_of_nonneg_left (hDosc i w) hC2)
    refine movc2_SB_mono_E (movc2_SB_add (u := fun x => movc2_mon v x * mova3b1_Dj i (fun y => Real.sqrt (ρ y)) x * w x)
      (v := fun x => movc2_mon v x * Real.sqrt (ρ x) * (mova1_D i w) x) t1 t2) (le_of_eq ?_)
    ring
  obtain ⟨C, hC, hall⟩ := movc2_word_const n _ (fun v C C' hCC' h w =>
    movc2_SB_mono_E (h w) (mul_le_mul_of_nonneg_right hCC' (Real.sqrt_nonneg _))) hword
  refine ⟨C, hC, fun w => ⟨fun v hv => ?_, fun v hv => hall v hv w⟩⟩
  have e : (fun x => movc2_mon v x * mova3b1_Dj i (movc2_h ρ w) x) = fun x =>
      movc2_mon v x * mova3b1_Dj i (fun y => Real.sqrt (ρ y)) x * w x +
        movc2_mon v x * Real.sqrt (ρ x) * (mova1_D i w) x := by
    funext x
    rw [movc2_Dh hψs i w, movc2_coe_D]
    ring
  have := movc2_CB_add (movc2_CB_G_mul (movc2_G_mon hDψ v) w)
    (movc2_CB_G_mul (movc2_G_mon hψ v) (mova1_D i w))
  rw [← e] at this
  exact this

lemma movc2_CB_zero : movc2_CB (fun _ : Euc d => (0 : ℝ)) :=
  ⟨continuous_const, 0, fun x => by simp⟩

lemma movc2_CB_sum {ι : Type*} (S : Finset ι) {f : ι → Euc d → ℝ} (h : ∀ i ∈ S, movc2_CB (f i)) :
    movc2_CB (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using movc2_CB_zero (d := d)
  | insert a S ha ih =>
    have := movc2_CB_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this

/-- **Second profile.**  `x^w Δ(√ρ w)` has `H^r` norm `≲ ‖w‖_{Σ^{r+2}}`. -/
lemma movc2_prof2 {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B) (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : 𝓢R, movc2_Reg n (fun y => ∑ i, mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) y) ∧
      movc2_WB n r (C * oscNorm (r + 1 + 1) w)
        (fun y => ∑ i, mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) y) := by
  have hψ : MovcG (fun y => Real.sqrt (ρ y)) := D.psiG
  have hψs : ContDiff ℝ ∞ (fun y => Real.sqrt (ρ y)) := hψ.1
  have hDψ : ∀ i : Fin d, MovcG (mova3b1_Dj i (fun y => Real.sqrt (ρ y))) := fun i => movc1_G_Dj hψ i
  have hDDψ : ∀ i : Fin d, MovcG (mova3b1_Dj i (mova3b1_Dj i (fun y => Real.sqrt (ρ y)))) :=
    fun i => movc1_G_Dj (hDψ i) i
  obtain ⟨Cd0, hCd0, hD0⟩ := movc2_osc_D (d := d) r
  obtain ⟨Cd1, hCd1, hD1⟩ := movc2_osc_D (d := d) (r + 1)
  have hterm : ∀ (v : List (Fin d)) (i : Fin d), ∃ C : ℝ, 0 ≤ C ∧ ∀ w : 𝓢R,
      movc2_SB r (C * oscNorm (r + 1 + 1) w)
        (fun x => movc2_mon v x * mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) x) := by
    intro v i
    obtain ⟨C1, hC1, h1⟩ := movc2_B1G (movc2_G_mon (hDDψ i) v) hr
    obtain ⟨C2, hC2, h2⟩ := movc2_B1G (movc2_G_mon (hDψ i) v) hr
    obtain ⟨C3, hC3, h3⟩ := movc2_B1G (movc2_G_mon hψ v) hr
    refine ⟨C1 + 2 * (C2 * (Cd0 * 1)) + C3 * (Cd0 * (Cd1 * 1)) + 0, by positivity, fun w => ?_⟩
    have e : (fun x => movc2_mon v x * mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) x) = fun x =>
        movc2_mon v x * mova3b1_Dj i (mova3b1_Dj i (fun y => Real.sqrt (ρ y))) x * w x +
          2 * (movc2_mon v x * mova3b1_Dj i (fun y => Real.sqrt (ρ y)) x * (mova1_D i w) x) +
          movc2_mon v x * Real.sqrt (ρ x) * (mova1_D i (mova1_D i w)) x := by
      funext x
      rw [movc2_DDh hψs i w]
      simp only [movc2_coe_D]
      ring
    rw [e]
    have o0 : oscNorm r w ≤ oscNorm (r + 1 + 1) w := movc2_osc_mono_r (r := r) w (1 + 1) (by norm_num) |>
      fun h => by simpa [add_assoc] using h
    have o1 : oscNorm r (⇑(mova1_D i w)) ≤ Cd0 * oscNorm (r + 1 + 1) w :=
      (hD0 i w).trans (mul_le_mul_of_nonneg_left (movc2_osc_mono_r (r := r + 1) w 1 zero_le_one) hCd0)
    have o2 : oscNorm r (⇑(mova1_D i (mova1_D i w))) ≤ Cd0 * (Cd1 * oscNorm (r + 1 + 1) w) :=
      (hD0 i (mova1_D i w)).trans (mul_le_mul_of_nonneg_left
        ((hD1 i w)) hCd0)
    have t1 := movc2_SB_mono_E (h1 w) (mul_le_mul_of_nonneg_left o0 hC1)
    have t2 := movc2_SB_smul 2 (movc2_SB_mono_E (h2 (mova1_D i w)) (mul_le_mul_of_nonneg_left o1 hC2))
    have t3 := movc2_SB_mono_E (h3 (mova1_D i (mova1_D i w))) (mul_le_mul_of_nonneg_left o2 hC3)
    have t12 := movc2_SB_add t1 t2
    have t123 := movc2_SB_add t12 t3
    refine movc2_SB_mono_E t123 (le_of_eq ?_)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  have hword : ∀ v : List (Fin d), ∃ C : ℝ, 0 ≤ C ∧ ∀ w : 𝓢R,
      movc2_SB r (C * oscNorm (r + 1 + 1) w)
        (fun x => movc2_mon v x * ∑ i, mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) x) := by
    intro v
    choose Ci hCi0 hCi using hterm v
    refine ⟨∑ i, Ci i, Finset.sum_nonneg fun i _ => hCi0 i, fun w => ?_⟩
    have := movc2_SB_sum r (Finset.univ : Finset (Fin d)) (E := fun i => Ci i * oscNorm (r + 1 + 1) w)
      (fun i _ => hCi i w)
    rw [← Finset.sum_mul] at this
    refine (show (fun x => ∑ i, movc2_mon v x * mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) x) =
      fun x => movc2_mon v x * ∑ i, mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) x from ?_) ▸ this
    funext x; rw [Finset.mul_sum]
  obtain ⟨C, hC, hall⟩ := movc2_word_const n _ (fun v C C' hCC' h w =>
    movc2_SB_mono_E (h w) (mul_le_mul_of_nonneg_right hCC' (Real.sqrt_nonneg _))) hword
  refine ⟨C, hC, fun w => ⟨fun v hv => ?_, fun v hv => hall v hv w⟩⟩
  have e : (fun x => movc2_mon v x * ∑ i, mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) x) = fun x =>
      ∑ i, (movc2_mon v x * mova3b1_Dj i (mova3b1_Dj i (fun y => Real.sqrt (ρ y))) x * w x +
          2 * (movc2_mon v x * mova3b1_Dj i (fun y => Real.sqrt (ρ y)) x * (mova1_D i w) x) +
          movc2_mon v x * Real.sqrt (ρ x) * (mova1_D i (mova1_D i w)) x) := by
    funext x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [movc2_DDh hψs i w]
    simp only [movc2_coe_D]
    ring
  have hcb := movc2_CB_sum (Finset.univ : Finset (Fin d)) (f := fun i x =>
      movc2_mon v x * mova3b1_Dj i (mova3b1_Dj i (fun y => Real.sqrt (ρ y))) x * w x +
          2 * (movc2_mon v x * mova3b1_Dj i (fun y => Real.sqrt (ρ y)) x * (mova1_D i w) x) +
          movc2_mon v x * Real.sqrt (ρ x) * (mova1_D i (mova1_D i w)) x) (fun i _ =>
    movc2_CB_add (movc2_CB_add (movc2_CB_G_mul (movc2_G_mon (hDDψ i) v) w)
      (movc2_CB_smul 2 (movc2_CB_G_mul (movc2_G_mon (hDψ i) v) (mova1_D i w))))
      (movc2_CB_G_mul (movc2_G_mon hψ v) (mova1_D i (mova1_D i w))))
  rw [← e] at hcb
  exact hcb

/-! ### The algebra and the multiplier `B_i` -/

/-- `H^{m_a} × H^σ → H^σ` in the `movc2_SB` bookkeeping. -/
lemma movc2_alg {ma σ : ℝ} (hma : (d : ℝ) / 2 < ma) (hσ0 : 0 ≤ σ) (hσma : σ ≤ ma) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ea E : ℝ) (u f : Euc d → ℝ), movc2_SB ma Ea u → movc2_SB σ E f →
      movc2_SB σ (C * Ea * E) (fun x => u x * f x) := by
  obtain ⟨C, hC, h⟩ := HRS.MS.MovA4.mova4_sobolev_algebra (d := d) hma hσ0 hσma
  refine ⟨C, hC.le, fun Ea E u f hu hf => ?_⟩
  obtain ⟨h1, h2⟩ := h u f hu.1 hf.1
  refine ⟨h1, ?_⟩
  have hnu := mova3b2_sobolevNormSq_nonneg ma u
  have hnf := mova3b2_sobolevNormSq_nonneg σ f
  calc Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq σ fun x => u x * f x)
      ≤ Real.sqrt (C ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq ma u * HRS.PDE.ToolboxRd.sobolevNormSq σ f) :=
        Real.sqrt_le_sqrt h2
    _ = C * (Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq ma u) *
          Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq σ f)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le]
        ring
    _ ≤ C * (Ea * E) := mul_le_mul_of_nonneg_left
        (mul_le_mul hu.2 hf.2 (Real.sqrt_nonneg _) (movc2_SB_nonneg hu)) hC.le
    _ = C * Ea * E := by ring

lemma movc2_B_smooth {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B) :
    ContDiff ℝ ∞ B :=
  contDiff_infty.2 fun n => (D.cb n).choose_spec.1

/-- The coordinates `B_i` of the drift: smooth, of temperate growth, with bounded partial derivatives of
order `≤ N`. -/
lemma movc2_Bi {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B) (i : Fin d)
    (N : ℕ) : ContDiff ℝ ∞ (fun x => B x i) ∧ (fun x => B x i).HasTemperateGrowth ∧
      ∃ A : ℝ, 0 ≤ A ∧ mova3b2_Q N 0 A (fun x => B x i) := by
  have hBs := movc2_B_smooth D
  have hpr : ∀ k : ℕ, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (fun x => B x i) x‖ ≤
      ‖iteratedFDeriv ℝ k B x‖ := fun k x => by
    have hBk : ContDiff ℝ (k : WithTop ℕ∞) B := hBs.of_le (by exact_mod_cast le_top)
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
      (f := B) (x := x) hBk.contDiffAt (n := k) le_rfl
    have h1 : ‖(EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ)‖ ≤ 1 := movb2_norm_proj_le i
    refine (show ‖iteratedFDeriv ℝ k (fun x => B x i) x‖ ≤ _ from h).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  have hs : ContDiff ℝ ∞ (fun x => B x i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hBs
  refine ⟨hs, ⟨hs, fun n => ?_⟩, ?_⟩
  · obtain ⟨Mb, hMb⟩ := D.cb n
    exact ⟨0, Mb, fun x => by simpa using (hpr n x).trans (hMb.2 n le_rfl x)⟩
  · obtain ⟨Mb, hMb⟩ := D.cb N
    refine ⟨Mb, (norm_nonneg _).trans (hMb.2 0 (Nat.zero_le _) 0), ?_⟩
    exact mova3b2_Q_of_iter hs fun k hk x => by
      simpa using (hpr k x).trans (hMb.2 k hk x)

/-! ### The weighted local forces -/

variable {s : ℝ}

/-- The local part `(θ g) * ∂_i h` of the force. -/
def movc2_Fl (s : ℝ) (ρ : Euc d → ℝ) (w : 𝓢R) (i : Fin d) : Euc d → ℝ :=
  HRS.Whole.convFun (fun z => movb2_theta d z * rieszKernel d s z) (mova3b1_Dj i (movc2_h ρ w))

/-- The local part `(θ g) * Δh` of the potential's Laplacian. -/
def movc2_Gl (s : ℝ) (ρ : Euc d → ℝ) (w : 𝓢R) : Euc d → ℝ :=
  HRS.Whole.convFun (fun z => movb2_theta d z * rieszKernel d s z)
    (fun y => ∑ i, mova3b1_Dj i (mova3b1_Dj i (movc2_h ρ w)) y)

lemma movc2_theta_data : ContDiff ℝ ∞ (movb2_theta d) ∧ HasCompactSupport (movb2_theta d) :=
  ⟨(movb2_bump d).contDiff.of_le (by exact_mod_cast le_top), (movb2_bump d).hasCompactSupport⟩

/-- **Weighted local forces.**  `‖Q^K F^loc_i‖_{H^σ}`, `‖Q^K x_i F^loc_i‖_{H^σ}`, `‖Q^K G^loc‖_{H^σ}`
are bounded by `C ‖w‖_{Σ^m}` (`Q = 1+‖x‖²`), provided `σ ≤ m - 2 + d - s`. -/
theorem movc2_force_wt {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B)
    (hs0 : 0 ≤ s) (hsd : s < d) {m σ : ℝ} (hm : 2 ≤ m) (hσ : σ ≤ m - 2 + ((d : ℝ) - s)) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : 𝓢R,
      (∀ i : Fin d, movc2_SB σ (C * oscNorm m w) (fun x => (1 + ‖x‖ ^ 2) ^ K * movc2_Fl s ρ w i x) ∧
        movc2_SB σ (C * oscNorm m w) (fun x => (1 + ‖x‖ ^ 2) ^ K * (x i * movc2_Fl s ρ w i x))) ∧
      movc2_SB σ (C * oscNorm m w) (fun x => (1 + ‖x‖ ^ 2) ^ K * movc2_Gl s ρ w x) := by
  have hds : 0 < (d : ℝ) - s := by linarith
  set n : ℕ := 2 * K + 1 with hn
  have hr1 : 0 ≤ m - 1 := by linarith
  have hr2 : 0 ≤ m - 2 := by linarith
  choose C1 hC1 hprof1 using fun i : Fin d => movc2_prof1 D n hr1 i
  obtain ⟨C2, hC2, hprof2⟩ := movc2_prof2 D n hr2
  obtain ⟨hθ, hc⟩ := movc2_theta_data (d := d)
  obtain ⟨Cl, hCl, hloc⟩ := movc2_loc_wt hs0 hsd n _ hθ hc
  have e1 : m - 1 + 1 = m := by ring
  have e2 : m - 2 + 1 + 1 = m := by ring
  set P1 : ℝ := ∑ i, C1 i with hP1
  have hP10 : 0 ≤ P1 := Finset.sum_nonneg fun i _ => hC1 i
  have hC1P : ∀ i, C1 i ≤ P1 := fun i =>
    Finset.single_le_sum (f := C1) (fun i _ => hC1 i) (Finset.mem_univ i)
  refine ⟨((d : ℝ) + 1) ^ K * Cl * (P1 + C2), by positivity, fun w => ?_⟩
  have ow : 0 ≤ oscNorm m w := Real.sqrt_nonneg _
  -- weighted forces at index `m-1+d-s`, `m-2+d-s`
  have hF : ∀ i : Fin d, movc2_WB n σ (Cl * (P1 * oscNorm m w)) (movc2_Fl s ρ w i) := by
    intro i
    obtain ⟨hr, hw⟩ := hprof1 i w
    rw [e1] at hw
    have := hloc (m - 1) _ _ hr hw
    refine movc2_WB_mono_t (by linarith) (movc2_WB_mono_E ?_ this)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hC1P i) ow) hCl
  have hG : movc2_WB n σ (Cl * (C2 * oscNorm m w)) (movc2_Gl s ρ w) := by
    obtain ⟨hr, hw⟩ := hprof2 w
    rw [e2] at hw
    have := hloc (m - 2) _ _ hr hw
    exact movc2_WB_mono_t hσ this
  have hn2 : 0 + 2 * K ≤ n := by omega
  have key : ∀ {E : ℝ} {u : Euc d → ℝ}, movc2_WB (0 + 2 * K) σ E u →
      movc2_SB σ (((d : ℝ) + 1) ^ K * E) (fun x => (1 + ‖x‖ ^ 2) ^ K * u x) := fun {E u} h =>
    movc2_WB_zero (movc2_WB_Qpow K h)
  have key2 : ∀ {E : ℝ} {u : Euc d → ℝ}, movc2_WB n σ E u → ∀ i : Fin d,
      movc2_SB σ (((d : ℝ) + 1) ^ K * E) (fun x => (1 + ‖x‖ ^ 2) ^ K * (x i * u x)) := fun {E u} h i =>
    key (movc2_WB_mono_n (by omega) (movc2_WB_shift (n := 2 * K) h i))
  have hPC : Cl * (P1 * oscNorm m w) ≤ Cl * ((P1 + C2) * oscNorm m w) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) ow) hCl
  have hPC2 : Cl * (C2 * oscNorm m w) ≤ Cl * ((P1 + C2) * oscNorm m w) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) ow) hCl
  have hd1 : (0 : ℝ) ≤ ((d : ℝ) + 1) ^ K := by positivity
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · refine movc2_SB_mono_E (key (movc2_WB_mono_n hn2 (hF i))) ?_
    calc ((d : ℝ) + 1) ^ K * (Cl * (P1 * oscNorm m w)) ≤ ((d : ℝ) + 1) ^ K * (Cl * ((P1 + C2) * oscNorm m w)) :=
          mul_le_mul_of_nonneg_left hPC hd1
      _ = _ := by ring
  · refine movc2_SB_mono_E (key2 (hF i) i) ?_
    calc ((d : ℝ) + 1) ^ K * (Cl * (P1 * oscNorm m w)) ≤ ((d : ℝ) + 1) ^ K * (Cl * ((P1 + C2) * oscNorm m w)) :=
          mul_le_mul_of_nonneg_left hPC hd1
      _ = _ := by ring
  · refine movc2_SB_mono_E (key (movc2_WB_mono_n hn2 hG)) ?_
    calc ((d : ℝ) + 1) ^ K * (Cl * (C2 * oscNorm m w)) ≤ ((d : ℝ) + 1) ^ K * (Cl * ((P1 + C2) * oscNorm m w)) :=
          mul_le_mul_of_nonneg_left hPC2 hd1
      _ = _ := by ring

/-! ### From weighted `H^σ` bounds to `Σ^σ` -/

lemma movc2_br_mul (K : ℕ) (x : Euc d) : movc2_br (-(K : ℝ)) x * (1 + ‖x‖ ^ 2) ^ K = 1 := by
  unfold movc2_br
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_mul_cancel₀ (by positivity)]

/-- **Decay extraction** (`B2` with the multiplier `(1+‖x‖²)^{-K}`): if `Q^K u ∈ H^σ` then `u ∈ Σ^σ`. -/
lemma movc2_decay {σ : ℝ} (hσ : 0 < σ) (K : ℕ) (hK : σ ≤ 2 * K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : ℝ) (u : Euc d → ℝ), movc2_SB σ E (fun x => (1 + ‖x‖ ^ 2) ^ K * u x) →
      MemOsc σ u ∧ oscNorm σ u ≤ C * E := by
  obtain ⟨C2, hC2, hB⟩ := mo_bridge2 (d := d) σ (2 * K) (by exact_mod_cast hK)
  obtain ⟨A, hA0, hA⟩ := movc2_br_Q (d := d) (2 * K) K (2 * K) le_rfl
  have hceil : ⌈-σ⌉₊ = 0 := Nat.ceil_eq_zero.2 (by linarith)
  have hA' : mova3b2_Q (max (2 * K) ⌈-σ⌉₊) (2 * K) A (movc2_br (-(K : ℝ)) : Euc d → ℝ) := by
    rw [hceil, max_eq_left (Nat.zero_le _)]; exact hA
  refine ⟨C2 * A, mul_nonneg hC2 hA0, fun E u hu => ?_⟩
  obtain ⟨h1, h2⟩ := hB A hA0 (movc2_br (-(K : ℝ))) (movc2_br_tg _) hA' _ hu.1
  have e : (fun x => movc2_br (-(K : ℝ)) x * ((1 + ‖x‖ ^ 2) ^ K * u x)) = u := by
    funext x; rw [← mul_assoc, movc2_br_mul, one_mul]
  rw [e] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  have hE : 0 ≤ C2 * A := mul_nonneg hC2 hA0
  calc C2 * A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq σ fun x => (1 + ‖x‖ ^ 2) ^ K * u x)
      ≤ C2 * A * E := mul_le_mul_of_nonneg_left hu.2 hE
    _ = _ := by ring

/-! ### The local part of `B` -/

/-- The local part of `B(v,w)`: the contribution of the kernel `θ g`. -/
def movc2_Lloc (s : ℝ) (ρ : Euc d → ℝ) (q' : ℝ) (B : Euc d → Euc d) (v w : 𝓢R) (x : Euc d) : ℝ :=
  ((∑ i, mova3b1_Dj i (⇑v) x * movc2_Fl s ρ w i x) + v x * movc2_Gl s ρ w x) +
    ((∑ i, (-q' / 2) * (v x * (x i * movc2_Fl s ρ w i x))) +
      ∑ i, (1 / 2) * ((B x i * v x) * movc2_Fl s ρ w i x))

/-- **The local part of `B` is bounded `Σ^m × Σ^m → Σ^{m-a}`.** -/
theorem movc2_local {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (D : MovC2Data d ρ q' B)
    (hs0 : 0 ≤ s) (hsd : s < d) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v w : 𝓢R, MemOsc (m - movA d s) (movc2_Lloc s ρ q' B v w) ∧
      oscNorm (m - movA d s) (movc2_Lloc s ρ q' B v w) ≤ C * oscNorm m v * oscNorm m w := by
  set σ : ℝ := m - movA d s with hσdef
  have hA1 : 1 ≤ movA d s := le_max_left _ _
  have hA2 : movA d s < 2 := max_lt (by norm_num) (by linarith)
  have hdpos : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hm2 : 2 ≤ m := by linarith
  have hσpos : 0 < σ := by linarith
  have hσ1 : σ ≤ m - 1 := by linarith
  have hσ2 : σ ≤ m - 2 + ((d : ℝ) - s) := by
    have : s + 2 - d ≤ movA d s := le_max_right _ _
    linarith
  set K : ℕ := ⌈σ⌉₊ with hKdef
  have hK : σ ≤ 2 * K := by
    have h1 : σ ≤ (K : ℝ) := Nat.le_ceil σ
    have h2 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    linarith
  obtain ⟨Cw, hCw, hforce⟩ := movc2_force_wt D hs0 hsd hm2 hσ2 K
  obtain ⟨Ca1, hCa1, halg1⟩ := movc2_alg (d := d) (ma := m - 1) (σ := σ) (by linarith) hσpos.le hσ1
  obtain ⟨Ca0, hCa0, halg0⟩ := movc2_alg (d := d) (ma := m) (σ := σ) (by linarith) hσpos.le (by linarith)
  obtain ⟨CB1, hCB1, hB1a⟩ := movc2_B1_one (d := d) (r := m - 1) (by linarith)
  obtain ⟨CB0, hCB0, hB1b⟩ := movc2_B1_one (d := d) (r := m) (by linarith)
  obtain ⟨CBi, hCBi, hB1c⟩ := movc2_B1 (d := d) (r := m) (by linarith)
  obtain ⟨Cd, hCd, hosc⟩ := movc2_osc_D (d := d) (m - 1)
  choose hBs hBtg Ab hAb0 hAbQ using fun i : Fin d => movc2_Bi D i ⌈m⌉₊
  set Asum : ℝ := ∑ i, Ab i with hAsum
  have hAsum0 : 0 ≤ Asum := Finset.sum_nonneg fun i _ => hAb0 i
  have hAbs : ∀ i, Ab i ≤ Asum := fun i =>
    Finset.single_le_sum (f := Ab) (fun i _ => hAb0 i) (Finset.mem_univ i)
  obtain ⟨Cdec, hCdec, hdec⟩ := movc2_decay (d := d) hσpos K hK
  have e1 : m - 1 + 1 = m := by ring
  set C0 : ℝ := (d : ℝ) * (Ca1 * (CB1 * Cd) * Cw) + Ca0 * CB0 * Cw +
    ((d : ℝ) * (|-q' / 2| * (Ca0 * CB0 * Cw)) + (d : ℝ) * (|(1 : ℝ) / 2| * (Ca0 * (CBi * Asum) * Cw))) with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨Cdec * C0, mul_nonneg hCdec hC00, fun v w => ?_⟩
  have ov : 0 ≤ oscNorm m v := Real.sqrt_nonneg _
  have ow : 0 ≤ oscNorm m w := Real.sqrt_nonneg _
  obtain ⟨hFw, hGw⟩ := hforce w
  -- the factors in `H^{m-1}` and `H^m`
  have hu1 : ∀ i : Fin d, movc2_SB (m - 1) (CB1 * (Cd * oscNorm m v)) (mova3b1_Dj i (⇑v)) := by
    intro i
    have h := hB1a (mova1_D i v)
    rw [movc2_coe_D] at h
    refine movc2_SB_mono_E h (mul_le_mul_of_nonneg_left ?_ hCB1)
    have := hosc i v
    rwa [e1] at this
  have hu0 : movc2_SB m (CB0 * oscNorm m v) (⇑v) := hB1b v
  have hu2 : ∀ i : Fin d, movc2_SB m (CBi * Asum * oscNorm m v) (fun x => B x i * v x) := by
    intro i
    have h := hB1c (Ab i) (hAb0 i) (fun x => B x i) (hBtg i) (hAbQ i) v
    refine movc2_SB_mono_E h ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hAbs i) hCBi) ov
  have hCw0 : 0 ≤ Cw * oscNorm m w := mul_nonneg hCw ow
  -- the four families of terms
  have T1 : ∀ i : Fin d, movc2_SB σ (Ca1 * (CB1 * (Cd * oscNorm m v)) * (Cw * oscNorm m w))
      (fun x => mova3b1_Dj i (⇑v) x * ((1 + ‖x‖ ^ 2) ^ K * movc2_Fl s ρ w i x)) := fun i =>
    halg1 _ _ _ _ (hu1 i) (hFw i).1
  have T2 : movc2_SB σ (Ca0 * (CB0 * oscNorm m v) * (Cw * oscNorm m w))
      (fun x => v x * ((1 + ‖x‖ ^ 2) ^ K * movc2_Gl s ρ w x)) := halg0 _ _ _ _ hu0 hGw
  have T3 : ∀ i : Fin d, movc2_SB σ (|-q' / 2| * (Ca0 * (CB0 * oscNorm m v) * (Cw * oscNorm m w)))
      (fun x => (-q' / 2) * (v x * ((1 + ‖x‖ ^ 2) ^ K * (x i * movc2_Fl s ρ w i x)))) := fun i =>
    movc2_SB_smul _ (halg0 _ _ _ _ hu0 (hFw i).2)
  have T4 : ∀ i : Fin d, movc2_SB σ (|(1 : ℝ) / 2| * (Ca0 * (CBi * Asum * oscNorm m v) * (Cw * oscNorm m w)))
      (fun x => (1 / 2) * ((B x i * v x) * ((1 + ‖x‖ ^ 2) ^ K * movc2_Fl s ρ w i x))) := fun i =>
    movc2_SB_smul _ (halg0 _ _ _ _ (hu2 i) (hFw i).1)
  have S1 := movc2_SB_sum σ (Finset.univ : Finset (Fin d)) (fun i _ => T1 i)
  have S3 := movc2_SB_sum σ (Finset.univ : Finset (Fin d)) (fun i _ => T3 i)
  have S4 := movc2_SB_sum σ (Finset.univ : Finset (Fin d)) (fun i _ => T4 i)
  have Stot := movc2_SB_add (movc2_SB_add S1 T2) (movc2_SB_add S3 S4)
  have hW : (fun x => (1 + ‖x‖ ^ 2) ^ K * movc2_Lloc s ρ q' B v w x) = fun x =>
      ((∑ i, mova3b1_Dj i (⇑v) x * ((1 + ‖x‖ ^ 2) ^ K * movc2_Fl s ρ w i x)) +
        v x * ((1 + ‖x‖ ^ 2) ^ K * movc2_Gl s ρ w x)) +
      ((∑ i, (-q' / 2) * (v x * ((1 + ‖x‖ ^ 2) ^ K * (x i * movc2_Fl s ρ w i x)))) +
        ∑ i, (1 / 2) * ((B x i * v x) * ((1 + ‖x‖ ^ 2) ^ K * movc2_Fl s ρ w i x))) := by
    funext x
    unfold movc2_Lloc
    have s1 : (1 + ‖x‖ ^ 2) ^ K * (∑ i, mova3b1_Dj i (⇑v) x * movc2_Fl s ρ w i x) =
        ∑ i, mova3b1_Dj i (⇑v) x * ((1 + ‖x‖ ^ 2) ^ K * movc2_Fl s ρ w i x) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have s3 : (1 + ‖x‖ ^ 2) ^ K * (∑ i, (-q' / 2) * (v x * (x i * movc2_Fl s ρ w i x))) =
        ∑ i, (-q' / 2) * (v x * ((1 + ‖x‖ ^ 2) ^ K * (x i * movc2_Fl s ρ w i x))) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have s4 : (1 + ‖x‖ ^ 2) ^ K * (∑ i, (1 / 2) * ((B x i * v x) * movc2_Fl s ρ w i x)) =
        ∑ i, (1 / 2) * ((B x i * v x) * ((1 + ‖x‖ ^ 2) ^ K * movc2_Fl s ρ w i x)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [mul_add, mul_add, mul_add, s1, s3, s4]
    ring
  rw [← hW] at Stot
  have hE : (∑ i : Fin d, Ca1 * (CB1 * (Cd * oscNorm m v)) * (Cw * oscNorm m w)) +
      Ca0 * (CB0 * oscNorm m v) * (Cw * oscNorm m w) +
      ((∑ i : Fin d, |-q' / 2| * (Ca0 * (CB0 * oscNorm m v) * (Cw * oscNorm m w))) +
        ∑ i : Fin d, |(1 : ℝ) / 2| * (Ca0 * (CBi * Asum * oscNorm m v) * (Cw * oscNorm m w))) =
      C0 * oscNorm m v * oscNorm m w := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hC0]
    ring
  rw [hE] at Stot
  obtain ⟨h1, h2⟩ := hdec _ _ Stot
  exact ⟨h1, by simpa [mul_assoc] using h2⟩

end HRS.MS.MovC2
