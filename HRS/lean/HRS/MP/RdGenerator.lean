/-
Packet MPRGEN, stage 3c: transport, drift and nonlocal terms of the whole-space generator
(`B:eq:path-generator-C1`, S L10770-10776), as weighted `C^k` classes `RgW`.
-/
import HRS.MP.RdGenCalc
import HRS.Whole.AppendixA

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.RdGen
open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

lemma rg_matgrad {k : ℕ} {B MB : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {φ : Euc d → ℝ}
    (hMB : HRS.PDE.MatBound MB M) (hφ : ContDiff ℝ (k + 2 + 1) φ)
    (hB : ∀ n, n ≤ k + 2 + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ B) (j : Fin d) :
    RgW (fun _ => 1) (k + 2) (d * MB * B)
      (fun y => Torus.matVec M.transpose (gradient φ y) j) := by
  have hfun : (fun y => Torus.matVec M.transpose (gradient φ y) j) =
      fun y => ∑ i : Fin d, M i j * gradient φ y i := by
    funext y
    rw [HRS.Whole.Q09B.q09b_matVec_apply]
    simp
  rw [hfun]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)), RgW (fun _ => (1 : ℝ)) (k + 2) (|M i j| * B)
      (fun y => M i j * gradient φ y i) := fun i _ =>
    RgW.const_mul (M i j) (rg_grad_comp hφ hB i)
  have hs := RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := k + 2) Finset.univ hterm
  refine hs.mono (fun _ => zero_le_one) ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by omega) 0)
  calc ∑ i : Fin d, |M i j| * B ≤ ∑ i : Fin d, MB * B :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hMB i j) hB0
    _ = d * MB * B := by simp [Finset.sum_const]; ring

/-- The nonlocal term of the generator. -/
lemma rg_T3 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {k : ℕ} {Aρ Bg : ℝ} (hAρ : 0 ≤ Aρ)
    (hBg : 0 ≤ Bg) {ρ : Euc d → ℝ} (hρ : RgDecay (k + 2) (fun _ => Aρ) ρ)
    {g : Fin d → Euc d → ℝ} (hg : ∀ j, RgW (fun _ => 1) (k + 2) Bg (g j)) :
    RgW (fun _ => 1) k
      (d * (movtr_sigma s * ((2 ^ (k + 2) * Aρ * Bg) * rgNear d s +
        4 ^ (s + 1) * (2 ^ (k + 2) * Aρ * Bg) * rgW d)))
      (fun x => ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s) (fun y => ρ y * g j y) x) j) := by
  have hw0 : ∀ y : Euc d, 0 ≤ (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y =>
    Real.rpow_nonneg (by positivity) _
  have hcf : 0 ≤ 2 ^ (k + 2) * Aρ * Bg := by positivity
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      RgW (fun _ => (1 : ℝ)) k (movtr_sigma s * ((2 ^ (k + 2) * Aρ * Bg) * rgNear d s +
        4 ^ (s + 1) * (2 ^ (k + 2) * Aρ * Bg) * rgW d))
      (fun x => (convGradConvW (rieszKernelGrad d s) (fun y => ρ y * g j y) x) j) := by
    intro j _
    have hmul := RgW.mul (w := fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) (k := k + 2) hw0 hAρ hBg hρ (hg j)
    exact rg_conv_comp hd hs0 hsd hcf hmul j
  have hs := RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := k) Finset.univ hterm
  simpa [Finset.sum_const] using hs

lemma rg_gradV {k : ℕ} (hk : 1 ≤ k) {ΛV G₀ : ℝ} {V : Euc d → ℝ} (hV : VHypRd (k + 1) ΛV G₀ V)
    (j : Fin d) : RgW (fun x => 1 + ‖x‖) k (G₀ + ΛV) (fun x => gradient V x j) := by
  have hG0 : 0 ≤ G₀ := (norm_nonneg _).trans hV.2.2
  have hΛ : 0 ≤ ΛV := (norm_nonneg _).trans (hV.2.1 2 le_rfl (by omega) 0)
  have e : (fun x => gradient V x j) = fun x => fderiv ℝ V x (EuclideanSpace.single j (1 : ℝ)) := by
    funext x; exact movtr_gradient_apply V x j
  have hVk : ContDiff ℝ (k + 1) V := hV.1.of_le (by exact_mod_cast le_top)
  rw [e]
  refine ⟨(hVk.fderiv_right (m := k) (by exact le_rfl)).clm_apply contDiff_const, fun n hn x => ?_⟩
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    rw [norm_iteratedFDeriv_zero]
    have h1 := HRS.Whole.Q09B.q09b_gradV_bound (by omega : 2 ≤ k + 1) hV x
    have h2 : |gradient V x j| ≤ ‖gradient V x‖ := by
      have := PiLp.norm_apply_le (gradient V x) j
      simpa [Real.norm_eq_abs] using this
    have e1 : fderiv ℝ V x (EuclideanSpace.single j (1 : ℝ)) = gradient V x j :=
      (movtr_gradient_apply V x j).symm
    rw [e1, Real.norm_eq_abs]
    nlinarith [norm_nonneg x]
  · have := rg_diruv (n := n) (φ := V) (hVk.of_le (by exact_mod_cast Nat.succ_le_succ hn))
      (EuclideanSpace.single j 1) x
    rw [rg_norm_single, one_mul] at this
    refine this.trans ((hV.2.1 (n + 1) (by omega) (by omega) x).trans ?_)
    nlinarith [norm_nonneg x]

lemma rg_near_nonneg (s : ℝ) : 0 ≤ rgNear d s :=
  setIntegral_nonneg measurableSet_closedBall fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

lemma rg_W_nonneg : 0 ≤ rgW d :=
  integral_nonneg fun y => Real.rpow_nonneg (by positivity) _

lemma RgW.of_one {k : ℕ} {c : ℝ} {u : Euc d → ℝ} (h : RgW (fun _ => 1) k c u) :
    RgW (fun x => 1 + ‖x‖) k c u := by
  have hc : 0 ≤ c := by
    have := h.2 0 (Nat.zero_le _) 0
    have h0 := norm_nonneg (iteratedFDeriv ℝ 0 u 0)
    linarith
  exact ⟨h.1, fun n hn x => (h.2 n hn x).trans (by
    have := norm_nonneg x
    nlinarith)⟩

/-- Drift components. -/
lemma rg_drift (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {k : ℕ} (hk : 1 ≤ k)
    {Aρ MB ΛV G₀ : ℝ} (hAρ : 0 ≤ Aρ) {D : WholeDyn d} (hDs : D.s = s)
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (k + 1) ΛV G₀ D.V)
    {ρ : Euc d → ℝ} (hρ : RgDecay (k + 2) (fun _ => Aρ) ρ) (j : Fin d) :
    RgW (fun x => 1 + ‖x‖) k
      (d * MB * (movtr_sigma s * (Aρ * rgNear d s + 4 ^ (s + 1) * Aρ * rgW d)) + (G₀ + ΛV))
      (fun x => meanFieldDriftW D ρ x j) := by
  have hfun : (fun x => meanFieldDriftW D ρ x j) = fun x =>
      (∑ i : Fin d, D.M j i * (convGradConvW (rieszKernelGrad d s) ρ x) i) - gradient D.V x j := by
    funext x
    unfold meanFieldDriftW
    rw [PiLp.sub_apply, HRS.Whole.Q09B.q09b_matVec_apply, hDs]
  rw [hfun]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      RgW (fun _ => (1 : ℝ)) k (|D.M j i| * (movtr_sigma s * (Aρ * rgNear d s + 4 ^ (s + 1) * Aρ * rgW d)))
        (fun x => D.M j i * (convGradConvW (rieszKernelGrad d s) ρ x) i) := fun i _ =>
    RgW.const_mul _ (rg_conv_comp hd hs0 hsd hAρ hρ i)
  have hs := (RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := k) Finset.univ hterm).of_one
  have hK : 0 ≤ movtr_sigma s * (Aρ * rgNear d s + 4 ^ (s + 1) * Aρ * rgW d) :=
    mul_nonneg (rg_sigma_nonneg hs0)
      (add_nonneg (mul_nonneg hAρ (rg_near_nonneg s))
        (mul_nonneg (mul_nonneg (by positivity) hAρ) rg_W_nonneg))
  have hs' := hs.mono (fun x => by positivity) (c' := d * MB * (movtr_sigma s * (Aρ * rgNear d s + 4 ^ (s + 1) * Aρ * rgW d))) (by
    calc ∑ i : Fin d, |D.M j i| * (movtr_sigma s * (Aρ * rgNear d s + 4 ^ (s + 1) * Aρ * rgW d))
        ≤ ∑ i : Fin d, MB * (movtr_sigma s * (Aρ * rgNear d s + 4 ^ (s + 1) * Aρ * rgW d)) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hMB j i) hK
      _ = _ := by simp [Finset.sum_const]; ring)
  exact hs'.sub (rg_gradV hk hV j)

/-- Transport term. -/
lemma rg_transport {k : ℕ} {B Bb : ℝ} (hB : 0 ≤ B) (hBb : 0 ≤ Bb) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ (k + 1) φ) (hBφ : ∀ n, n ≤ k + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ B)
    {b : Euc d → Euc d} (hb : ∀ j, RgW (fun x => 1 + ‖x‖) k Bb (fun x => b x j)) :
    RgW (fun x => 1 + ‖x‖) k (d * (2 ^ k * Bb * B)) (fun x => inner ℝ (b x) (gradient φ x)) := by
  have hfun : (fun x => inner ℝ (b x) (gradient φ x)) =
      fun x => ∑ j : Fin d, b x j * gradient φ x j := by
    funext x; rw [HRS.Whole.Q09B.q09b_inner_euc]
  rw [hfun]
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      RgW (fun x : Euc d => 1 + ‖x‖) k (2 ^ k * Bb * B) (fun x => b x j * gradient φ x j) := fun j _ =>
    RgW.mul (fun x => by positivity) hBb hB (hb j) (rg_grad_comp hφ hBφ j)
  have hs := RgW.sum (w := fun x : Euc d => 1 + ‖x‖) (k := k) Finset.univ hterm
  simpa [Finset.sum_const] using hs

/-- Weighted `C^k` class to the `weightedSupE k (-1)` seminorm. -/
lemma rg_weighted_of_RgW {k : ℕ} {c : ℝ} {u : Euc d → ℝ} (h : RgW (fun x => 1 + ‖x‖) k c u) :
    weightedSupE k (-1) u ≤ ENNReal.ofReal (2 * c) := by
  unfold weightedSupE derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
  have hj : (j : ℕ) ≤ k := Nat.lt_succ_iff.1 j.2
  have h1 : |partialDeriv i u x| ≤ ‖iteratedFDeriv ℝ j u x‖ := by
    have := (iteratedFDeriv ℝ j u x).le_opNorm (fun l => (EuclideanSpace.single (i l) (1 : ℝ) : Euc d))
    simp only [rg_norm_single, Finset.prod_const_one, mul_one] at this
    unfold partialDeriv
    rwa [← Real.norm_eq_abs]
  have h2 := h.2 j hj x
  have h3 := rg_jb_rpow_le x (p := 1) (by norm_num)
  have hb : 0 < 1 + ‖x‖ := by positivity
  have h4 : (1 + ‖x‖) ^ (-(1 : ℝ)) = (1 + ‖x‖)⁻¹ := Real.rpow_neg_one _
  have hc : 0 ≤ c := by
    have := h.2 0 (Nat.zero_le _) 0
    simp at this
    exact (abs_nonneg _).trans this
  show jbracket x ^ (-1 : ℝ) * |partialDeriv i u x| ≤ 2 * c
  rw [h4, Real.rpow_one] at h3
  calc jbracket x ^ (-1 : ℝ) * |partialDeriv i u x|
      ≤ (2 * (1 + ‖x‖)⁻¹) * (c * (1 + ‖x‖)) :=
        mul_le_mul h3 (h1.trans h2) (abs_nonneg _) (by positivity)
    _ = 2 * c := by field_simp

lemma rg_decay_mono {n n' : ℕ} (hn : n ≤ n') {A : ℝ} {g : Euc d → ℝ}
    (h : RgDecay n' (fun _ => A) g) : RgDecay n (fun _ => A) g :=
  ⟨h.1.of_le (by exact_mod_cast hn), fun l hl y => h.2 l (hl.trans hn) y⟩

lemma rg_VHyp_mono {m m' : ℕ} {ΛV ΛV' G₀ G₀' : ℝ} {V : Euc d → ℝ} (h : VHypRd m ΛV G₀ V)
    (hm : m' ≤ m) (hΛ : ΛV ≤ ΛV') (hG : G₀ ≤ G₀') : VHypRd m' ΛV' G₀' V :=
  ⟨h.1, fun j hj hj' x => (h.2.1 j hj (hj'.trans hm) x).trans hΛ, h.2.2.trans hG⟩

/-- The constant of the generator bound (per unit of `‖φ‖`-derivative sup). -/
def rgK (d : ℕ) (s MB ΛV G₀ ν Aρ : ℝ) (k : ℕ) : ℝ :=
  ν * d + d * (2 ^ k * (d * MB * (movtr_sigma s * (Aρ * rgNear d s + 4 ^ (s + 1) * Aρ * rgW d)) + (G₀ + ΛV))) +
    d * (movtr_sigma s * ((2 ^ (k + 2) * Aρ * (d * MB)) * rgNear d s +
      4 ^ (s + 1) * (2 ^ (k + 2) * Aρ * (d * MB)) * rgW d))

lemma rgK_nonneg {s MB ΛV G₀ ν Aρ : ℝ} (hs0 : 0 ≤ s) (hMB : 0 ≤ MB) (hΛV : 0 ≤ ΛV) (hG : 0 ≤ G₀)
    (hν : 0 ≤ ν) (hA : 0 ≤ Aρ) (k : ℕ) : 0 ≤ rgK d s MB ΛV G₀ ν Aρ k := by
  have := rg_sigma_nonneg hs0
  have := rg_near_nonneg (d := d) s
  have := rg_W_nonneg (d := d)
  unfold rgK
  positivity

/-- The core estimate at fixed time: all constants explicit. -/
lemma rg_gen_core (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {k : ℕ} (hk : 1 ≤ k)
    {MB ΛV G₀ νbar Aρ B : ℝ} (hMB0 : 0 ≤ MB) (hΛV : 0 ≤ ΛV) (hG : 0 ≤ G₀) (hAρ : 0 ≤ Aρ) (hB : 0 ≤ B)
    {D : WholeDyn d} (hDs : D.s = s) (hMB : HRS.PDE.MatBound MB D.M)
    (hV : VHypRd (k + 1) ΛV G₀ D.V) (hν0 : 0 ≤ D.invβ) (hν : D.invβ ≤ νbar)
    {ρ : ℝ → Euc d → ℝ} {τ : ℝ} (hρ : RgDecay (k + 2) (fun _ => Aρ) (ρ τ))
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ (k + 2 + 1) φ)
    (hBφ : ∀ n, n ≤ k + 2 + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ B) :
    RgW (fun x => 1 + ‖x‖) k (B * rgK d s MB ΛV G₀ νbar Aρ k) (generatorW (D.coeff ρ) τ φ) := by
  subst hDs
  have hφ2 : ContDiff ℝ (k + 2) φ := hφ.of_le (by exact_mod_cast Nat.le_succ _)
  have hφ1 : ContDiff ℝ (k + 1) φ := hφ.of_le (by exact_mod_cast (by omega : k + 1 ≤ k + 2 + 1))
  have hLap := rg_laplacian (k := k) hφ2 (fun n hn x => hBφ n (by omega) x)
  have hνt : RgW (fun _ => (1 : ℝ)) k (|D.invβ| * (d * B)) (fun x => D.invβ * Laplacian.laplacian φ x) :=
    hLap.const_mul _
  have hσ := rg_sigma_nonneg hs0
  have hnear := rg_near_nonneg (d := d) D.s
  have hW := rg_W_nonneg (d := d)
  have hK : 0 ≤ movtr_sigma D.s * (Aρ * rgNear d D.s + 4 ^ (D.s + 1) * Aρ * rgW d) :=
    mul_nonneg hσ (add_nonneg (mul_nonneg hAρ hnear) (mul_nonneg (mul_nonneg (by positivity) hAρ) hW))
  have hBb : 0 ≤ d * MB * (movtr_sigma D.s * (Aρ * rgNear d D.s + 4 ^ (D.s + 1) * Aρ * rgW d)) + (G₀ + ΛV) := by
    positivity
  have hT2 := rg_transport (k := k) hB hBb hφ1 (fun n hn x => hBφ n (by omega) x)
    (b := meanFieldDriftW D (ρ τ)) (fun j => rg_drift hd hs0 hsd hk hAρ rfl hMB hV hρ j)
  have hBg : 0 ≤ (d : ℝ) * MB * B := by positivity
  have hT3 := rg_T3 hd hs0 hsd (k := k) hAρ hBg hρ
    (g := fun j y => Torus.matVec D.M.transpose (gradient φ y) j) (fun j => rg_matgrad hMB hφ hBφ j)
  have hmain := (hνt.of_one.add hT2).sub hT3.of_one
  have hfun : generatorW (D.coeff ρ) τ φ = fun x =>
      (D.invβ * Laplacian.laplacian φ x + inner ℝ (meanFieldDriftW D (ρ τ) x) (gradient φ x)) -
        ∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
          (fun y => ρ τ y * (Torus.matVec D.M.transpose (gradient φ y)) j) x) j := rfl
  rw [hfun]
  refine hmain.mono (fun x => by positivity) ?_
  have h1 : |D.invβ| * (d * B) ≤ νbar * (d * B) := by
    rw [abs_of_nonneg hν0]
    exact mul_le_mul_of_nonneg_right hν (by positivity)
  unfold rgK
  nlinarith [h1]

/-- **Generator bound on `ℝ^d`** (`B:eq:path-generator-C1`, S.A.22 whole space), `k = m₀ + 1`,
`q = Γ + 2`.  `Cgen` depends only on `(d, s, Γ, m₀, MB, Λ, ΛV, G₀, νbar)` (and not on `T`, `D`, `ρ`,
`φ`, `τ`).  The hypothesis `hΓ` is the index relation `Γ + 2 > m_* + d/2 + 4` (it is not a field of
`FieldDensityRd`; see `rg_generator_bound_fd`). -/
theorem rg_generator_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (Γ m₀ : ℕ)
    (hm₀ : m₀ ≤ mStar d) (hΓ : (mStar d : ℝ) + d / 2 + 4 < ((Γ : ℝ) + 2))
    (MB Λ ΛV G₀ νbar : ℝ) :
    ∃ Cgen : ℝ, 0 ≤ Cgen ∧ ∀ (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (T : ℝ), D.s = s →
      HRS.PDE.MatBound MB D.M → VHypRd (Γ + 5) ΛV G₀ D.V → IsRegularMFRd s (Γ + 2 + 3) Λ T ρ →
      0 ≤ D.invβ → D.invβ ≤ νbar → ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ φ : Euc d → ℝ,
        IsSobolevTest (((Γ + 2 : ℕ) : ℝ)) φ →
        ContDiff ℝ ((m₀ + 1 : ℕ) : WithTop ℕ∞) (generatorW (D.coeff ρ) τ φ) ∧
        weightedSupE (m₀ + 1) (-1) (generatorW (D.coeff ρ) τ φ) ≤
          ENNReal.ofReal (Cgen * HRS.Whole.sobolevNorm (((Γ + 2 : ℕ) : ℝ)) φ) := by
  have hmS : (m₀ : ℝ) ≤ mStar d := by exact_mod_cast hm₀
  have hq : ((m₀ + 1 + 2 + 1 : ℕ) : ℝ) + d / 2 < (((Γ + 2 : ℕ)) : ℝ) := by
    push_cast at hΓ ⊢; linarith
  obtain ⟨Cs, hCs0, hCs⟩ := rg_phi_bounds (d := d) (m₀ + 1 + 2 + 1) hq
  obtain ⟨MB', hMB'e⟩ : ∃ x : ℝ, x = max MB 0 := ⟨_, rfl⟩
  obtain ⟨Λ', hΛ'e⟩ : ∃ x : ℝ, x = max Λ 0 := ⟨_, rfl⟩
  obtain ⟨ΛV', hΛV'e⟩ : ∃ x : ℝ, x = max ΛV 0 := ⟨_, rfl⟩
  obtain ⟨G₀', hG₀'e⟩ : ∃ x : ℝ, x = max G₀ 0 := ⟨_, rfl⟩
  obtain ⟨ν', hν'e⟩ : ∃ x : ℝ, x = max νbar 0 := ⟨_, rfl⟩
  obtain ⟨Aρ, hAρ⟩ : ∃ x : ℝ, x = (d : ℝ) ^ (Γ + 2 + 3) * Λ' * 2 ^ ((d : ℝ) + 3) := ⟨_, rfl⟩
  have hMB0 : 0 ≤ MB' := hMB'e ▸ le_max_right _ _
  have hΛ0 : 0 ≤ Λ' := hΛ'e ▸ le_max_right _ _
  have hΛV0 : 0 ≤ ΛV' := hΛV'e ▸ le_max_right _ _
  have hG0 : 0 ≤ G₀' := hG₀'e ▸ le_max_right _ _
  have hν0 : 0 ≤ ν' := hν'e ▸ le_max_right _ _
  have hMBle : MB ≤ MB' := hMB'e ▸ le_max_left _ _
  have hΛle : Λ ≤ Λ' := hΛ'e ▸ le_max_left _ _
  have hΛVle : ΛV ≤ ΛV' := hΛV'e ▸ le_max_left _ _
  have hG₀le : G₀ ≤ G₀' := hG₀'e ▸ le_max_left _ _
  have hνle : νbar ≤ ν' := hν'e ▸ le_max_left _ _
  have hA0 : 0 ≤ Aρ := by rw [hAρ]; positivity
  have hK0 := rgK_nonneg (d := d) hs0 hMB0 hΛV0 hG0 hν0 hA0 (m₀ + 1)
  refine ⟨2 * Cs * rgK d s MB' ΛV' G₀' ν' Aρ (m₀ + 1), by positivity, ?_⟩
  intro D ρ T hDs hMB hV hcoef hν0' hν τ hτ φ hφ
  obtain ⟨hφsm, hφmem⟩ := hφ
  have hmΓ : m₀ ≤ Γ := by
    have : (m₀ : ℝ) ≤ Γ := by
      have : (0 : ℝ) ≤ d / 2 := by positivity
      linarith
    exact_mod_cast this
  have hcb := hcoef.1 τ hτ
  have hcb0 : 0 ≤ HRS.cbNorm (Γ + 2 + 3) (ρ τ) :=
    Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hρdec : RgDecay (m₀ + 1 + 2) (fun _ => Aρ) (ρ τ) :=
    rg_decay_mono (by omega) (hAρ ▸ rg_rho_decay hd (r := Γ + 2 + 3) (Λ := Λ') hcb.1 hcb.2.1
      (by linarith [hcb.2.2]))
  have hMB'' : HRS.PDE.MatBound MB' D.M := fun i j => (hMB i j).trans hMBle
  have hV' : VHypRd (m₀ + 1 + 1) ΛV' G₀' D.V :=
    rg_VHyp_mono hV (by omega) hΛVle hG₀le
  have hB0 : 0 ≤ Cs * HRS.Whole.sobolevNorm (((Γ + 2 : ℕ) : ℝ)) φ :=
    mul_nonneg hCs0 (Real.sqrt_nonneg _)
  have hφ' : ContDiff ℝ ((m₀ + 1 : ℕ) + 2 + 1) φ := by exact_mod_cast contDiff_infty.1 hφsm (m₀ + 1 + 2 + 1)
  have hcore := rg_gen_core hd hs0 hsd (k := m₀ + 1) (by omega) hMB0 hΛV0 hG0 hA0 hB0 hDs hMB'' hV'
    hν0' (hν.trans hνle) hρdec hφ'
    (fun n hn x => hCs φ hφsm hφmem n hn x)
  refine ⟨hcore.1, (rg_weighted_of_RgW hcore).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))⟩

/-- The same bound with the field index `Γ` of a selected density `fd : FieldDensityRd d s`. -/
theorem rg_generator_bound_fd (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (fd : FieldDensityRd d s)
    (m₀ : ℕ) (hm₀ : m₀ ≤ mStar d) (hΓ : (mStar d : ℝ) + d / 2 + 4 < ((fd.Gamma : ℝ) + 2))
    (MB Λ ΛV G₀ νbar : ℝ) :
    ∃ Cgen : ℝ, 0 ≤ Cgen ∧ ∀ (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (T : ℝ), D.s = s →
      HRS.PDE.MatBound MB D.M → VHypRd (fd.Gamma + 5) ΛV G₀ D.V → IsRegularMFRd s (fd.Gamma + 2 + 3) Λ T ρ →
      0 ≤ D.invβ → D.invβ ≤ νbar → ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ φ : Euc d → ℝ,
        IsSobolevTest (((fd.Gamma + 2 : ℕ) : ℝ)) φ →
        ContDiff ℝ ((m₀ + 1 : ℕ) : WithTop ℕ∞) (generatorW (D.coeff ρ) τ φ) ∧
        weightedSupE (m₀ + 1) (-1) (generatorW (D.coeff ρ) τ φ) ≤
          ENNReal.ofReal (Cgen * HRS.Whole.sobolevNorm (((fd.Gamma + 2 : ℕ) : ℝ)) φ) :=
  rg_generator_bound hd hs0 hsd fd.Gamma m₀ hm₀ hΓ MB Λ ΛV G₀ νbar

end HRS.MP.RdGen
