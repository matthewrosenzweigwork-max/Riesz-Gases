import HRS.PDE.MeanFieldAdjointSmoothing
import HRS.PDE.MeanFieldAdjointSmoothingLow
import HRS.PDE.MeanFieldAdjointLoss

/-!
# Duhamel formula and abstract adjoint decay (package MF-01, packet P11d)

See `HRS/PDE/MeanFieldAdjointPlan.md`, packet P11d.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFAdjoint

variable {d : ℕ}

/-!
Route for `duhamel_coeff` (coefficientwise, no Hilbert structure, no Fubini).  Write `m = j - 2`,
`U(x)ψ := frozenCoeff D ρβ m ψ x`, `L = forwardGen D ρβ`, `F(σ)` the `μ`-propagator path (level `m+2`),
`G(σ) = forwardGen D (μ (t-σ)) (F σ)`, `E(σ) = G(σ) - L F(σ)`.  Fix `τ` and `k`, and put
`h(σ) = (U(τ-σ) F(σ)) k` on `[0,τ]`.
* `h` is continuous (`F ∈ C([0,t];H^m)` strongly, `U` uniformly bounded and Lipschitz in the datum,
  modes of `U(·)ψ` continuous);
* `h` has right derivative `(U(τ-σ) E(σ)) k` at `σ ∈ (0,τ)`: with `δ = y - σ`,
  `h(y) - h(σ) = U(τ-y)[F(y) - U(δ)F(σ)] k` by the semigroup law `frozenCoeff_shift`, and
  `δ⁻¹[F(y) - U(δ)F(σ)] → G(σ) - L F(σ)` in `H^m` (time regularity of `F` and of the frozen path
  with `H^{m+2}` datum `F(σ)`), `U(τ-y)` being bounded on `H^m` and linear (`frozenCoeff_sub/smul`);
* the derivative is measurable (`measurable_derivWithin_Ici`) and bounded, hence integrable, and
  `integral_eq_sub_of_hasDeriv_right_of_le` gives `h(τ) - h(0) = ∫_0^τ (U(τ-σ)E(σ)) k dσ`.
-/

section DuhamelAux

variable {s : ℝ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ} {ρ : Torus d → ℝ}

theorem hsInner_smul_left' (m : ℝ) (z : ℂ) (a b : Coeff d) :
    hsInner m (z • a) b = z * hsInner m a b := by
  unfold hsInner
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem memHs_smul_coeff {m : ℝ} {c : Coeff d} (hc : MemHs m c) (z : ℂ) : MemHs m (z • c) :=
  MFThermalReg.memHs_smul hc z

/-- Linearity (scalars) of the frozen path in the datum. -/
theorem frozenCoeff_smul (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) {ψc : Coeff d} (hψ : MemHs m ψc) (z : ℂ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    frozenCoeff D ρ m (z • ψc) τ = z • frozenCoeff D ρ m ψc τ := by
  have hzψ : MemHs m (z • ψc) := memHs_smul_coeff hψ z
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [frozenCoeff_zero hm hzψ, frozenCoeff_zero hm hψ]
  · have ht : τ ∈ Set.Ioc 0 T := ⟨hpos, hτ.2⟩
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
    obtain ⟨h1, w1, -⟩ := hspec D ν₀ T (fun _ => ρ) hA τ ht ψc hψ
    have w1' := weakContinuousInHs_mono hm1 w1
    have hsol : IsForwardSolution D (fun _ => ρ) τ (z • ψc)
        (fun σ => z • propagatorCoeff D (fun _ => ρ) m τ ψc σ) := by
      refine ⟨fun σ hσ => memHs_smul_coeff (h1.h1 σ hσ) z, fun k => ?_, fun k σ hσ => ?_⟩
      · have : IntegrableOn (fun σ => z * forwardGen D ρ (propagatorCoeff D (fun _ => ρ) m τ ψc σ) k)
            (Set.Icc 0 τ) := Integrable.const_mul (h1.integrable k) z
        refine this.congr_fun (fun σ _ => ?_) measurableSet_Icc
        simp only [forwardGen_smul, Pi.smul_apply, smul_eq_mul]
      · have hi : IntervalIntegrable (fun x => forwardGen D ρ (propagatorCoeff D (fun _ => ρ) m τ ψc x) k)
            volume 0 σ := by
          rw [intervalIntegrable_iff_integrableOn_Icc_of_le hσ.1]
          exact (h1.integrable k).mono_set (Set.Icc_subset_Icc_right hσ.2)
        have e := h1.eq k σ hσ
        simp only [forwardGen_smul, Pi.smul_apply, smul_eq_mul]
        rw [intervalIntegral.integral_const_mul, e]
        ring
    have hw : WeakContinuousInHs 1 (fun σ => z • propagatorCoeff D (fun _ => ρ) m τ ψc σ) τ := by
      refine ⟨fun σ hσ => memHs_smul_coeff (w1'.1 σ hσ) z, fun G hG => ?_⟩
      refine ((w1'.2 G hG).const_smul z).congr fun σ hσ => ?_
      simp only [hsInner_smul_left', Pi.smul_apply, smul_eq_mul]
    have := propagatorCoeff_eq_of_solution hd hs0 hsd hm hA ht hzψ hsol hw τ ⟨hτ.1.trans le_rfl, le_rfl⟩
    exact this

theorem norm_coeff_le_hsNorm_of_nonneg {m : ℝ} (hm : 0 ≤ m) {c : Coeff d} (hc : MemHs m c)
    (k : Lattice d) : ‖c k‖ ≤ hsNorm m c := by
  have h := MFApriori.norm_coeff_le_hsNorm m hc k
  have h1 : 1 ≤ Real.sqrt (sobWeight m k) := by
    rw [Real.one_le_sqrt]
    exact MFProduct.one_le_sobWeight hm k
  calc ‖c k‖ = ‖c k‖ * 1 := (mul_one _).symm
    _ ≤ ‖c k‖ * Real.sqrt (sobWeight m k) := by gcongr
    _ ≤ _ := h

/-- Uniform bound of the frozen path on `H^m`, also for single coefficients. -/
theorem frozen_coeff_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ψc : Coeff d), MemHs m ψc → ∀ x ∈ Set.Icc (0 : ℝ) T,
      MemHs m (frozenCoeff D ρ m ψc x) ∧ ∀ k, ‖frozenCoeff D ρ m ψc x k‖ ≤ K * hsNorm m ψc := by
  obtain ⟨L, hL, hbd⟩ := exists_frozenCoeff_bound (d := d) (s := s) (m := m) hd hs0 hsd hm R MB Λ VB
  refine ⟨Real.exp (|R.lambdaM L ν₀ (thetaOrder d s)| * T), (Real.exp_pos _).le,
    fun ψc hψ x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hbd D ν₀ T ρ hA ψc hψ x hx
  refine ⟨h1, fun k => ?_⟩
  refine (norm_coeff_le_hsNorm_of_nonneg (Nat.cast_nonneg m) h1 k).trans (h2.trans ?_)
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hsNorm_nonneg' _ _)
  have h3 := le_abs_self (R.lambdaM L ν₀ (thetaOrder d s))
  have h4 := abs_nonneg (R.lambdaM L ν₀ (thetaOrder d s))
  nlinarith [hx.1, hx.2]

/-- Lipschitz dependence of the coefficients of the frozen path on the datum. -/
theorem frozen_coeff_dist (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ψc ψc' : Coeff d), MemHs m ψc → MemHs m ψc' → ∀ x ∈ Set.Icc (0 : ℝ) T,
      ∀ k, ‖frozenCoeff D ρ m ψc x k - frozenCoeff D ρ m ψc' x k‖ ≤ K * hsNorm m (ψc - ψc') := by
  obtain ⟨K, hK, hb⟩ := frozen_coeff_bound hd hs0 hsd hm hA
  refine ⟨K, hK, fun ψc ψc' hψ hψ' x hx k => ?_⟩
  have h := (hb (ψc - ψc') (memHs_sub hψ hψ') x hx).2 k
  rw [frozenCoeff_sub_aux hd hs0 hsd hm hA hψ hψ' hx] at h
  simpa using h

/-- The modes of the frozen path are continuous in time. -/
theorem frozen_mode_continuousOn (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) {ψc : Coeff d} (hψ : MemHs m ψc)
    (k : Lattice d) : ContinuousOn (fun x => frozenCoeff D ρ m ψc x k) (Set.Icc 0 T) := by
  have hT := hA.hT
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  obtain ⟨h1, -, -⟩ := hspec D ν₀ T (fun _ => ρ) hA T ⟨hT, le_rfl⟩ ψc hψ
  refine (mode_continuousOn h1 hT.le k).congr fun x hx => ?_
  exact congrFun (frozenCoeff_eq_propagatorCoeff_aux hd hs0 hsd hm hA hψ ⟨hT, le_rfl⟩ hx).symm k

/-- Right difference quotient of the frozen path at `0` with `H^{m+2}` datum. -/
theorem frozen_quot (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ))
    (hA2 : AdjointData s (m + 2) R MB Λ VB D ν₀ T (fun _ => ρ)) {ψc : Coeff d}
    (hψ : MemHs ((m + 2 : ℕ) : ℝ) ψc) :
    Tendsto (fun δ : ℝ => hsNorm m (fun k =>
      (frozenCoeff D ρ m ψc δ k - ψc k) / ((δ : ℝ) : ℂ) - forwardGen D ρ ψc k))
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  have hT := hA.hT
  obtain ⟨-, htr⟩ := adjoint_torus_time_regularity hd s hs0 hsd (m + 2) (by omega) R MB Λ VB D ν₀
    T (fun _ => ρ) hA2 T ⟨hT, le_rfl⟩ ψc hψ
  have h0 := htr 0 ⟨le_rfl, hT.le⟩
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd (m + 2) (by omega) R MB Λ VB
  obtain ⟨hF, -, -⟩ := hspec D ν₀ T (fun _ => ρ) hA2 T ⟨hT, le_rfl⟩ ψc hψ
  have hP0 : propagatorCoeff D (fun _ => ρ) ((m + 2 : ℕ) : ℝ) T ψc 0 = ψc := by
    funext k
    simpa using hF.eq k 0 ⟨le_rfl, hT.le⟩
  have hcast : (((m + 2 : ℕ) : ℝ) - 2) = m := by push_cast; ring
  rw [hcast] at h0
  have h1 : Set.Ioo 0 T ∈ 𝓝[Set.Ioi 0] (0 : ℝ) := Ioo_mem_nhdsGT hT
  have h2 : Set.Icc 0 T \ {0} ∈ 𝓝[Set.Ioi 0] (0 : ℝ) :=
    Filter.mem_of_superset h1 fun x hx => ⟨⟨hx.1.le, hx.2.le⟩, ne_of_gt hx.1⟩
  refine (h0.mono_left (nhdsWithin_le_of_mem h2)).congr' ?_
  filter_upwards [h1] with δ hδ
  have hδ' : δ ∈ Set.Icc 0 T := ⟨hδ.1.le, hδ.2.le⟩
  have e1 : propagatorCoeff D (fun _ => ρ) ((m + 2 : ℕ) : ℝ) T ψc δ = frozenCoeff D ρ m ψc δ :=
    (frozenCoeff_eq_propagatorCoeff_aux hd hs0 hsd (by omega) hA2 hψ ⟨hT, le_rfl⟩ hδ').trans
      (frozenCoeff_level hd hs0 hsd hm (by omega) hA hA2 hψ hδ').symm
  rw [hP0, e1]
  simp

theorem hsNorm_sub_le_add {m : ℝ} {f g : Coeff d} (hf : MemHs m f) (hg : MemHs m g) :
    hsNorm m (f - g) ≤ hsNorm m f + hsNorm m g := by
  obtain ⟨h1, h2⟩ := hs_neg hg
  have := (hs_add_le m hf h1).2
  have e : (f - g) = fun k => f k + -g k := by
    funext k
    simp [sub_eq_add_neg]
  rw [e]
  linarith

/-- Right derivative of `σ ↦ (U(τ-σ) F(σ)) k`. -/
theorem duhamel_hasDeriv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ))
    (hA2 : AdjointData s (m + 2) R MB Λ VB D ν₀ T (fun _ => ρ))
    {t : ℝ} (htT : t ≤ T) (F G : ℝ → Coeff d)
    (hF1 : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs ((m + 2 : ℕ) : ℝ) (F σ))
    (hFd : ∀ σ ∈ Set.Icc (0 : ℝ) t, Tendsto (fun σ' => hsNorm m (fun k =>
      (F σ' k - F σ k) / ((σ' - σ : ℝ) : ℂ) - G σ k)) (𝓝[Set.Icc 0 t \ {σ}] σ) (𝓝 0))
    (hG : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs m (G σ))
    (hL : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs m (forwardGen D ρ (F σ)))
    {τ : ℝ} (hτ : τ ≤ t) {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 τ) (k : Lattice d) :
    HasDerivWithinAt (fun σ' => frozenCoeff D ρ m (F σ') (τ - σ') k)
      (frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - σ) k) (Set.Ioi σ) σ := by
  obtain ⟨K, hK, hKd⟩ := frozen_coeff_dist hd hs0 hsd hm hA
  have hT := hA.hT
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hσt : σ ∈ Set.Icc (0 : ℝ) t := ⟨hσ.1.le, hσ.2.le.trans hτ⟩
  have hFσm : MemHs (m : ℝ) (F σ) := (hF1 σ hσt).mono hmR
  have hEm : MemHs (m : ℝ) (G σ - forwardGen D ρ (F σ)) := memHs_sub (hG σ hσt) (hL σ hσt)
  have hnhds : Set.Icc 0 τ ∈ 𝓝 σ := Icc_mem_nhds hσ.1 hσ.2
  -- the three limits
  have T1 : Tendsto (fun y => ‖frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - y) k -
      frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - σ) k‖) (𝓝[Set.Ioi σ] σ) (𝓝 0) := by
    have hc : ContinuousOn (fun y => frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - y) k)
        (Set.Icc 0 τ) :=
      (frozen_mode_continuousOn hd hs0 hsd hm hA hEm k).comp (continuous_const.sub continuous_id).continuousOn
        (fun y hy => ⟨by linarith [hy.2], by linarith [hy.1, htT, hτ]⟩)
    have := (hc.continuousAt hnhds).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi σ))
    exact tendsto_iff_norm_sub_tendsto_zero.1 this
  have hnhdsR : Set.Ioo σ t ∈ 𝓝[Set.Ioi σ] σ := Ioo_mem_nhdsGT (lt_of_lt_of_le hσ.2 hτ)
  have T2 : Tendsto (fun y => hsNorm m (fun k' =>
      (F y k' - F σ k') / ((y - σ : ℝ) : ℂ) - G σ k')) (𝓝[Set.Ioi σ] σ) (𝓝 0) := by
    refine (hFd σ hσt).mono_left (nhdsWithin_le_of_mem ?_)
    exact Filter.mem_of_superset hnhdsR fun y hy => ⟨⟨(hσ.1.le.trans hy.1.le), hy.2.le⟩, ne_of_gt hy.1⟩
  have T3 : Tendsto (fun y => hsNorm m (fun k' =>
      (frozenCoeff D ρ m (F σ) (y - σ) k' - F σ k') / ((y - σ : ℝ) : ℂ) - forwardGen D ρ (F σ) k'))
      (𝓝[Set.Ioi σ] σ) (𝓝 0) := by
    have h := frozen_quot hd hs0 hsd hm hA hA2 (hF1 σ hσt)
    refine h.comp ?_
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun y : ℝ => y - σ) (𝓝 σ) (𝓝 (σ - σ)) :=
        (continuous_id.sub continuous_const).tendsto σ
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact Set.mem_Ioi.2 (sub_pos.2 hy)
  have hbound : ∀ᶠ y in 𝓝[Set.Ioi σ] σ,
      ‖slope (fun σ' => frozenCoeff D ρ m (F σ') (τ - σ') k) σ y -
        frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - σ) k‖ ≤
      ‖frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - y) k -
        frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - σ) k‖ +
      K * (hsNorm m (fun k' => (F y k' - F σ k') / ((y - σ : ℝ) : ℂ) - G σ k') +
        hsNorm m (fun k' => (frozenCoeff D ρ m (F σ) (y - σ) k' - F σ k') / ((y - σ : ℝ) : ℂ) -
          forwardGen D ρ (F σ) k')) := by
    have hnhds2 : Set.Ioo σ τ ∈ 𝓝[Set.Ioi σ] σ := Ioo_mem_nhdsGT hσ.2
    filter_upwards [hnhds2] with y hy
    have hδ : 0 < y - σ := sub_pos.2 hy.1
    have hyt : y ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hσ.1, hy.1], by linarith [hy.2]⟩
    have hFym : MemHs (m : ℝ) (F y) := (hF1 y hyt).mono hmR
    have hx : τ - y ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hy.2], by linarith [hσ.1, hy.1, htT, hτ]⟩
    have hδT : y - σ ∈ Set.Icc (0 : ℝ) T := ⟨hδ.le, by linarith [hσ.1, hy.2, htT, hτ]⟩
    obtain ⟨hUδm, hshift⟩ := frozenCoeff_shift hd hs0 hsd hm hA hFσm (τ := y - σ) (v := τ - y)
      hδ.le hx.1 (by linarith [hσ.1, htT, hτ])
    have hsum : y - σ + (τ - y) = τ - σ := by ring
    rw [hsum] at hshift
    set a : Coeff d := F y - frozenCoeff D ρ m (F σ) (y - σ) with ha
    have ham : MemHs (m : ℝ) a := memHs_sub hFym hUδm
    have hdiff : frozenCoeff D ρ m (F y) (τ - y) k - frozenCoeff D ρ m (F σ) (τ - σ) k =
        frozenCoeff D ρ m a (τ - y) k := by
      rw [← hshift]
      have := congrFun (frozenCoeff_sub_aux hd hs0 hsd hm hA hFym hUδm hx) k
      rw [ha, this]
      simp
    set b : Coeff d := (((y - σ : ℝ) : ℂ))⁻¹ • a with hb
    have hbm : MemHs (m : ℝ) b := memHs_smul_coeff ham _
    have hslope : slope (fun σ' => frozenCoeff D ρ m (F σ') (τ - σ') k) σ y =
        frozenCoeff D ρ m b (τ - y) k := by
      rw [slope_def_module, hb, frozenCoeff_smul hd hs0 hsd hm hA ham _ hx, Pi.smul_apply, ← hdiff]
      simp only [Complex.real_smul, smul_eq_mul]
      push_cast
      ring
    set Q1 : Coeff d := fun k' => (F y k' - F σ k') / ((y - σ : ℝ) : ℂ) - G σ k' with hQ1
    set Q2 : Coeff d := fun k' => (frozenCoeff D ρ m (F σ) (y - σ) k' - F σ k') / ((y - σ : ℝ) : ℂ) -
      forwardGen D ρ (F σ) k' with hQ2
    have hQ1e : Q1 = (((y - σ : ℝ) : ℂ))⁻¹ • (F y - F σ) - G σ := by
      funext k'
      simp [hQ1, div_eq_inv_mul]
    have hQ2e : Q2 = (((y - σ : ℝ) : ℂ))⁻¹ • (frozenCoeff D ρ m (F σ) (y - σ) - F σ) -
        forwardGen D ρ (F σ) := by
      funext k'
      simp [hQ2, div_eq_inv_mul]
    have hQ1m : MemHs (m : ℝ) Q1 := by
      rw [hQ1e]; exact memHs_sub (memHs_smul_coeff (memHs_sub hFym hFσm) _) (hG σ hσt)
    have hQ2m : MemHs (m : ℝ) Q2 := by
      rw [hQ2e]; exact memHs_sub (memHs_smul_coeff (memHs_sub hUδm hFσm) _) (hL σ hσt)
    have hbE : b - (G σ - forwardGen D ρ (F σ)) = Q1 - Q2 := by
      funext k'
      simp only [hb, ha, hQ1, hQ2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h1 := hKd b (G σ - forwardGen D ρ (F σ)) hbm hEm (τ - y) hx k
    rw [hbE] at h1
    have h2 := hsNorm_sub_le_add hQ1m hQ2m
    rw [hslope]
    calc ‖frozenCoeff D ρ m b (τ - y) k - frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - σ) k‖
        = ‖(frozenCoeff D ρ m b (τ - y) k - frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - y) k) +
          (frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - y) k -
            frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - σ) k)‖ := by ring_nf
      _ ≤ ‖frozenCoeff D ρ m b (τ - y) k - frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - y) k‖ +
          ‖frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - y) k -
            frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - σ) k‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [add_comm]
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hK)
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.sdiff_singleton_eq_self (by simp)]
  refine tendsto_sub_nhds_zero_iff.1 ?_
  refine squeeze_zero_norm' hbound ?_
  simpa using T1.add ((T2.add T3).const_mul K)

/-- Continuity of `σ ↦ (U(τ-σ) F(σ)) k` on `[0,τ]`. -/
theorem duhamel_continuousOn (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) {t : ℝ} (htT : t ≤ T) (F : ℝ → Coeff d)
    (hFc : ContinuousInHs (m : ℝ) F t) {τ : ℝ} (hτ : τ ≤ t) (k : Lattice d) :
    ContinuousOn (fun σ => frozenCoeff D ρ m (F σ) (τ - σ) k) (Set.Icc 0 τ) := by
  obtain ⟨K, hK, hKd⟩ := frozen_coeff_dist hd hs0 hsd hm hA
  intro σ₀ hσ₀
  have hσ₀t : σ₀ ∈ Set.Icc (0 : ℝ) t := ⟨hσ₀.1, hσ₀.2.trans hτ⟩
  have hsub : Set.Icc (0 : ℝ) τ ⊆ Set.Icc 0 t := Set.Icc_subset_Icc_right hτ
  have T1 : Tendsto (fun σ => hsNorm m (F σ - F σ₀)) (𝓝[Set.Icc 0 τ] σ₀) (𝓝 0) :=
    (hFc.2 σ₀ hσ₀t).mono_left (nhdsWithin_mono σ₀ hsub)
  have hc : ContinuousOn (fun σ => frozenCoeff D ρ m (F σ₀) (τ - σ) k) (Set.Icc 0 τ) :=
    (frozen_mode_continuousOn hd hs0 hsd hm hA (hFc.1 σ₀ hσ₀t) k).comp
      (continuous_const.sub continuous_id).continuousOn
      (fun y hy => ⟨by linarith [hy.2], by linarith [hy.1, htT, hτ]⟩)
  have T2 := tendsto_iff_norm_sub_tendsto_zero.1 (hc σ₀ hσ₀)
  rw [ContinuousWithinAt]
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero_norm' ?_ (by simpa using (T1.const_mul K).add T2)
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hx : τ - σ ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, htT, hτ]⟩
  have h1 := hKd (F σ) (F σ₀) (hFc.1 σ (hsub hσ)) (hFc.1 σ₀ hσ₀t) (τ - σ) hx k
  rw [norm_norm]
  calc ‖frozenCoeff D ρ m (F σ) (τ - σ) k - frozenCoeff D ρ m (F σ₀) (τ - σ₀) k‖
      = ‖(frozenCoeff D ρ m (F σ) (τ - σ) k - frozenCoeff D ρ m (F σ₀) (τ - σ) k) +
        (frozenCoeff D ρ m (F σ₀) (τ - σ) k - frozenCoeff D ρ m (F σ₀) (τ - σ₀) k)‖ := by ring_nf
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 le_rfl)

/-- The integral form: `F(τ) k = (U(τ) F(0)) k + ∫_0^τ (U(τ-σ) E(σ)) k dσ`. -/
theorem duhamel_integral (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ))
    (hA2 : AdjointData s (m + 2) R MB Λ VB D ν₀ T (fun _ => ρ))
    {t : ℝ} (htT : t ≤ T) (F G : ℝ → Coeff d)
    (hF1 : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs ((m + 2 : ℕ) : ℝ) (F σ))
    (hFc : ContinuousInHs (m : ℝ) F t)
    (hFd : ∀ σ ∈ Set.Icc (0 : ℝ) t, Tendsto (fun σ' => hsNorm m (fun k =>
      (F σ' k - F σ k) / ((σ' - σ : ℝ) : ℂ) - G σ k)) (𝓝[Set.Icc 0 t \ {σ}] σ) (𝓝 0))
    (hG : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs m (G σ))
    (hL : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs m (forwardGen D ρ (F σ)))
    (M : ℝ) (hGM : ∀ σ ∈ Set.Icc (0 : ℝ) t, hsNorm m (G σ) ≤ M)
    (hLM : ∀ σ ∈ Set.Icc (0 : ℝ) t, hsNorm m (forwardGen D ρ (F σ)) ≤ M)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ t) (k : Lattice d) :
    F τ k = frozenCoeff D ρ m (F 0) τ k +
      ∫ σ in (0 : ℝ)..τ, frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - σ) k := by
  have hT := hA.hT
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hFm : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs (m : ℝ) (F σ) := fun σ hσ => hFc.1 σ hσ
  have h0t : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, hτ0.trans hτ⟩
  have hτt : τ ∈ Set.Icc (0 : ℝ) t := ⟨hτ0, hτ⟩
  rcases hτ0.eq_or_lt with h0 | hpos
  · subst h0
    simp only [intervalIntegral.integral_same, add_zero]
    rw [frozenCoeff_zero hm (hFm 0 h0t)]
  have hderiv : ∀ x ∈ Set.Ioo 0 τ, HasDerivWithinAt (fun σ' => frozenCoeff D ρ m (F σ') (τ - σ') k)
      (frozenCoeff D ρ m (G x - forwardGen D ρ (F x)) (τ - x) k) (Set.Ioi x) x :=
    fun x hx => duhamel_hasDeriv hd hs0 hsd hm hA hA2 htT F G hF1 hFd hG hL hτ hx k
  have hcont := duhamel_continuousOn hd hs0 hsd hm hA htT F hFc hτ k
  -- integrability of the derivative
  obtain ⟨K, hK, hKb⟩ := frozen_coeff_bound hd hs0 hsd hm hA
  have hint : IntervalIntegrable
      (fun σ => frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - σ) k) volume 0 τ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hpos.le]
    set f : ℝ → ℂ := fun σ' => frozenCoeff D ρ m (F σ') (τ - σ') k with hf
    have hφ : IntegrableOn (fun x => derivWithin f (Set.Ici x) x) (Set.Ioo 0 τ) := by
      refine Measure.integrableOn_of_bounded (M := K * (M + M)) (by simp)
        (measurable_derivWithin_Ici f).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hxt : x ∈ Set.Icc (0 : ℝ) t := ⟨hx.1.le, hx.2.le.trans hτ⟩
      rw [((hasDerivWithinAt_Ioi_iff_Ici.1 (hderiv x hx))).derivWithin (uniqueDiffWithinAt_Ici x)]
      have hEm := memHs_sub (hG x hxt) (hL x hxt)
      have hx' : τ - x ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hx.2], by linarith [hx.1, htT, hτ]⟩
      refine ((hKb _ hEm (τ - x) hx').2 k).trans (mul_le_mul_of_nonneg_left ?_ hK)
      exact (hsNorm_sub_le_add (hG x hxt) (hL x hxt)).trans (add_le_add (hGM x hxt) (hLM x hxt))
    refine hφ.congr_fun (fun x hx => ?_) measurableSet_Ioo
    exact ((hasDerivWithinAt_Ioi_iff_Ici.1 (hderiv x hx))).derivWithin (uniqueDiffWithinAt_Ici x)
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hpos.le hcont hderiv hint
  rw [key]
  simp only [sub_self, sub_zero]
  rw [frozenCoeff_zero hm (hFm τ hτt)]
  ring

/-- The generator maps `H^{m+2}` to `H^m`, with a bound uniform over the admissible densities. -/
theorem forwardGen_hsNorm_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (MB Λ VB : ℝ)
    (D : DynData d) (hDs : D.s = s) (hM : MatBound MB D.M) (hV : VHyp m VB D.V) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk (m + 3) ρ →
      Torus.cbNorm (m + 3) ρ ≤ Λ → ∀ u : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) u →
        MemHs (m : ℝ) (forwardGen D ρ u) ∧
          hsNorm (m : ℝ) (forwardGen D ρ u) ≤ c * hsNorm ((m + 2 : ℕ) : ℝ) u := by
  obtain ⟨c0, hc0, h⟩ := StabAux.forwardGen_bound hd s hs0 hsd m MB Λ VB
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hnn : 0 ≤ 4 * D.invβ ^ 2 + c0 := by positivity
  refine ⟨Real.sqrt (4 * D.invβ ^ 2 + c0), Real.sqrt_nonneg _, fun ρ hρ h1 h2 u hu => ?_⟩
  rw [hcast] at hu ⊢
  obtain ⟨hm1, hm2⟩ := h D hDs hM hV ρ hρ h1 h2 u hu
  refine ⟨hm1, ?_⟩
  unfold hsNorm
  rw [← Real.sqrt_mul hnn]
  exact Real.sqrt_le_sqrt hm2

end DuhamelAux

theorem duhamel_coeff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) (hj : 3 ≤ j) (R R' : Regime)
    (MB Λ VB MB' Λ' VB' : ℝ) (D : DynData d) (ν₀ ν₀' T : ℝ) (μ : ℝ → Torus d → ℝ) (ρβ : Torus d → ℝ)
    (hA : AdjointData s j R MB Λ VB D ν₀ T μ) (hAβ : AdjointData s j R' MB' Λ' VB' D ν₀' T (fun _ => ρβ))
    (hν : 0 < D.invβ) (φc : Coeff d) (hφ : MemHs j φc) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) (k : Lattice d) {τ : ℝ}
    (hτ : τ ∈ Set.Icc 0 t) :
    propagatorCoeff D μ j t φc τ k = frozenCoeff D ρβ (j - 2) φc τ k +
      ∫ σ in (0 : ℝ)..τ, frozenCoeff D ρβ (j - 2)
        (forwardGen D (μ (t - σ)) (propagatorCoeff D μ j t φc σ) - forwardGen D ρβ (propagatorCoeff D μ j t φc σ)) (τ - σ) k := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  have hjm : m + 2 - 2 = m := by omega
  rw [hjm]
  have hAm := StabAux.adjointData_mono (by omega : m ≤ m + 2) hAβ
  have hAμm := StabAux.adjointData_mono (by omega : m ≤ m + 2) hA
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd (m + 2) (by omega) R MB Λ VB
  obtain ⟨hF, hw, hb⟩ := hspec D ν₀ T μ hA t ht φc hφ
  have hcast : ((m + 2 : ℕ) : ℝ) - 2 = m := by push_cast; ring
  have hmR : (m : ℝ) < ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hFc : ContinuousInHs (m : ℝ) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc) t :=
    forward_strong_continuity _ t _ hw _ hmR
  obtain ⟨-, htr⟩ := adjoint_torus_time_regularity hd s hs0 hsd (m + 2) (by omega) R MB Λ VB D ν₀ T
    μ hA t ht φc hφ
  rw [hcast] at htr
  -- bounds
  obtain ⟨c1, hc1, hgen1⟩ := forwardGen_hsNorm_le hd hs0 hsd m MB Λ VB D hA.hs hA.hM
    (hAμm.hV)
  obtain ⟨c2, hc2, hgen2⟩ := forwardGen_hsNorm_le hd hs0 hsd m MB' Λ' VB' D hAβ.hs hAβ.hM
    (hAm.hV)
  have hr0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, ht.1.le.trans ht.2⟩
  set lam := R.lambdaM C ν₀ (thetaOrder d s) with hlam
  set B : ℝ := Real.exp (|lam| * t) * hsNorm ((m + 2 : ℕ) : ℝ) φc with hBdef
  have hB : ∀ σ ∈ Set.Icc (0 : ℝ) t, hsNorm ((m + 2 : ℕ) : ℝ) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc σ) ≤ B := by
    intro σ hσ
    refine (hb σ hσ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hsNorm_nonneg' _ _))
    have h3 := le_abs_self lam
    have h4 := abs_nonneg lam
    nlinarith [hσ.1, hσ.2]
  have hrT : ∀ σ ∈ Set.Icc (0 : ℝ) t, t - σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have hG1 : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      MemHs (m : ℝ) (forwardGen D (μ (t - σ)) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc σ)) ∧
      hsNorm (m : ℝ) (forwardGen D (μ (t - σ)) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc σ)) ≤ c1 * B := by
    intro σ hσ
    have hr := hrT σ hσ
    obtain ⟨h1, h2⟩ := hgen1 (μ (t - σ)) (hAμm.hμ.prob _ hr) (hAμm.hμ.smooth _ hr) (hAμm.hμ.bound _ hr)
      _ (hw.1 σ hσ)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (hB σ hσ) hc1)⟩
  have hG2 : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      MemHs (m : ℝ) (forwardGen D ρβ (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc σ)) ∧
      hsNorm (m : ℝ) (forwardGen D ρβ (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc σ)) ≤ c2 * B := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := hgen2 ρβ (hAm.hμ.prob _ hr0) (hAm.hμ.smooth _ hr0) (hAm.hμ.bound _ hr0)
      _ (hw.1 σ hσ)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (hB σ hσ) hc2)⟩
  have hF0 : propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc 0 = φc := by
    funext k'
    simpa using hF.eq k' 0 ⟨le_rfl, ht.1.le⟩
  have := duhamel_integral hd hs0 hsd hm hAm hAβ (t := t) ht.2
    (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc)
    (fun σ => forwardGen D (μ (t - σ)) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc σ))
    (fun σ hσ => hw.1 σ hσ) hFc htr (fun σ hσ => (hG1 σ hσ).1) (fun σ hσ => (hG2 σ hσ).1)
    (max (c1 * B) (c2 * B)) (fun σ hσ => (hG1 σ hσ).2.trans (le_max_left _ _))
    (fun σ hσ => (hG2 σ hσ).2.trans (le_max_right _ _)) hτ.1 hτ.2 k
  rw [hF0] at this
  exact this

/-! ### Route for `exists_adjoint_decay_abstract`

Fix the level-`j` rate `c₁` of the frozen semigroup (`exists_frozen_hj_decay'`,
`exists_frozen_smoothing'`, in coefficient form `frozen_center_decay_coeff`,
`frozen_center_smooth_coeff`).  Write the time-dependent propagator path `F` through
`duhamel_coeff` as frozen part plus the Duhamel integral of the frozen propagator applied to
`E(σ) = (𝓛_{μ(t-σ)} - 𝓛_{ρβ}) F(σ)`.  Constants (multiples of `δ₀`) are stationary, so `E(σ)`
only sees `Q F(σ)` and is bounded in `H^{j-a}` by the loss estimate `exists_forwardGen_diff`
(`exists_pert_path`, used at the level `min r (j + mStar d + 2)`).  The centered integral is
controlled by Minkowski with a measurable-free majorant
(`hsNorm_intervalIntegral_le_majorant`); the zero mode of `Q I` is determined by the other modes,
so no commutation of `Q` with the integral is needed (`duh_core`).  The estimate
`‖Q F(τ)‖_j ≤ C e^{-cτ}` for `t - τ ≥ R₀` is closed by a sup-over-time Gronwall argument
(`gronwall_close`, `case_i_abstract`), `R₀` large so that the perturbation constant is `≤ 1/2`;
for `t - τ < R₀` the shift property `propagatorCoeff_shift` and the finite-time bound
`propagatorCoeff_center_bound` are used (`main_coeff`).  The function-level statement follows
by the bridges `projMean_toFun`, `S_eq`, `center_frozen_center`. -/

section Decay


/-! ### Generic tools -/

section Generic

open Classical in
/-- Minkowski for coefficientwise interval integrals with a measurable-free majorant: no
measurability of the modes is assumed (a mode that is not integrable has integral `0`). -/
theorem hsNorm_intervalIntegral_le_majorant (m : ℝ) (G : ℝ → Coeff d) (h : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hmem : ∀ σ ∈ Set.Ioo a b, MemHs m (G σ) ∧ hsNorm m (G σ) ≤ h σ)
    (hint : IntegrableOn h (Set.Ioc a b)) :
    MemHs m (fun k => ∫ σ in a..b, G σ k) ∧
      hsNorm m (fun k => ∫ σ in a..b, G σ k) ≤ ∫ σ in a..b, h σ := by
  set G' : ℝ → Coeff d := fun σ k =>
    if IntervalIntegrable (fun x => G x k) volume a b then G σ k else 0 with hG'
  have hmode : ∀ k, ∫ σ in a..b, G' σ k = ∫ σ in a..b, G σ k := by
    intro k
    by_cases hk : IntervalIntegrable (fun x => G x k) volume a b
    · simp only [hG', hk, if_true]
    · simp only [hG', hk, if_false]
      rw [intervalIntegral.integral_undef hk]
      simp
  have hmeas : ∀ k, AEStronglyMeasurable (fun σ => G' σ k) (volume.restrict (Set.Ioc a b)) := by
    intro k
    by_cases hk : IntervalIntegrable (fun x => G x k) volume a b
    · simp only [hG', hk, if_true]
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hk).aestronglyMeasurable
    · simp only [hG', hk, if_false]
      exact aestronglyMeasurable_const
  have hmem' : ∀ σ ∈ Set.Ioo a b, MemHs m (G' σ) ∧ hsNorm m (G' σ) ≤ h σ := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := hmem σ hσ
    have := hs_mult (m := m) (γ := 0) (C := 1) zero_le_one h1 (e := G' σ) (fun k => by
      rw [Real.rpow_zero]
      by_cases hk : IntervalIntegrable (fun x => G x k) volume a b
      · simp [hG', hk]
      · simp [hG', hk])
    simp only [sub_zero, one_mul] at this
    exact ⟨this.1, this.2.trans h2⟩
  have hae : ∀ᵐ σ ∂(volume.restrict (Set.Ioc a b)), σ ∈ Set.Ioo a b := by
    have h1 : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∉ ({b} : Set ℝ) :=
      (Set.countable_singleton b).ae_notMem volume
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h1] with σ hσ hσ'
    exact ⟨hσ'.1, lt_of_le_of_ne hσ'.2 (by simpa using hσ)⟩
  have hnormint : IntegrableOn (fun σ => hsNorm m (G' σ)) (Set.Ioc a b) := by
    refine Integrable.mono' hint (MFApriori.aestronglyMeasurable_hsNorm m G' hmeas) ?_
    filter_upwards [hae] with σ hσ
    rw [Real.norm_of_nonneg (hsNorm_nonneg' _ _)]
    exact (hmem' σ hσ).2
  obtain ⟨hA, hB⟩ := MFApriori.hsNorm_intervalIntegral_le m G' a b hab hmeas
    (fun σ hσ => (hmem' σ hσ).1) hnormint
  have e : (fun k => ∫ σ in a..b, G σ k) = fun k => ∫ σ in a..b, G' σ k :=
    funext fun k => (hmode k).symm
  rw [e]
  refine ⟨hA, hB.trans ?_⟩
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  refine integral_mono_ae hnormint hint ?_
  filter_upwards [hae] with σ hσ
  exact (hmem' σ hσ).2

/-- The real-coefficient bridge to functions. -/
theorem bridge_real {m : ℝ} (hm : (d : ℝ) / 2 < m) {c : Coeff d} (hc : MemHs m c)
    (hre : IsRealCoeff c) :
    Summable (fun k => ‖c k‖) ∧ Continuous (toFun c) ∧ coeffOf (toFun c) = c ∧
      MemSobolev m (toFun c) ∧ sobolevNorm m (toFun c) = hsNorm m c := by
  have hs := summable_norm_of_memHs m hm c hc
  obtain ⟨h1, h2⟩ := ClassicalPart.memSobolev_toFun hs hc hre
  exact ⟨hs, MFProduct.continuous_toFun c hs, coeffOf_toFun c hre hs, h1, h2⟩

end Generic

theorem exists_kernel_bound (γ b : ℝ) (hγ1 : γ < 1) (hb : 0 < b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, 0 ≤ τ →
      IntervalIntegrable (fun σ : ℝ => (1 + (τ - σ) ^ (-γ)) * Real.exp (-(b * (τ - σ)))) volume 0 τ ∧
      ∫ σ in (0:ℝ)..τ, (1 + (τ - σ) ^ (-γ)) * Real.exp (-(b * (τ - σ))) ≤ B := by
  set f : ℝ → ℝ := fun u => (1 + u ^ (-γ)) * Real.exp (-(b * u)) with hf
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (-(b * u))) (Set.Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 hb
  have h2 : IntegrableOn (fun u : ℝ => u ^ (-γ) * Real.exp (-b * u ^ (1:ℝ))) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hb
  have h2' : IntegrableOn (fun u : ℝ => u ^ (-γ) * Real.exp (-(b * u))) (Set.Ioi 0) := by
    refine h2.congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  have hfi : IntegrableOn f (Set.Ioi 0) := by
    refine (h1.add h2').congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only [hf, Pi.add_apply]; ring
  have hf0 : ∀ u ∈ Set.Ioi (0:ℝ), 0 ≤ f u := fun u hu => by
    have : 0 ≤ u ^ (-γ) := Real.rpow_nonneg (le_of_lt hu) _
    simp only [hf]; positivity
  refine ⟨∫ u in Set.Ioi (0:ℝ), f u, setIntegral_nonneg measurableSet_Ioi hf0, fun τ hτ => ?_⟩
  have hI : IntervalIntegrable f volume 0 τ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ]
    exact hfi.mono_set Set.Ioc_subset_Ioi_self
  have hI' : IntervalIntegrable (fun σ => f (τ - σ)) volume 0 τ := by
    have := hI.comp_sub_left τ
    simpa using this.symm
  refine ⟨hI', ?_⟩
  have := intervalIntegral.integral_comp_sub_left f (a := 0) (b := τ) τ
  simp only [sub_self, sub_zero] at this
  show ∫ σ in (0:ℝ)..τ, f (τ - σ) ≤ _
  rw [this, intervalIntegral.integral_of_le hτ]
  refine setIntegral_mono_set hfi ?_ (ae_of_all _ Set.Ioc_subset_Ioi_self)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using hf0 u hu

theorem frozen_center_decay_coeff (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j)
    (νm νp c₀ Λ₀ : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ) (ψc : Coeff d), IsRealCoeff ψc →
      MemHs (j : ℝ) ψc → ∀ τ : ℝ, 0 ≤ τ →
      MemHs (j : ℝ) (centerCoeff ρβ
        (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) ψc τ)) ∧
      hsNorm (j : ℝ) (centerCoeff ρβ
        (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) ψc τ)) ≤
        C * Real.exp (-c * τ) * hsNorm (j : ℝ) (centerCoeff ρβ ψc) := by
  obtain ⟨C, c, hC, hc, hdec⟩ := exists_frozen_hj_decay' hd s j hj νm νp c₀ Λ₀
  refine ⟨C, c, hC, hc, fun β V ρβ H ψc hre hψ τ hτ => ?_⟩
  have hjm := mStar_add_two_le_of_gt hj
  have h3 := ClassicalPart.three_le_mStar d
  have hdj : (d : ℝ) / 2 < j := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨hsum, hcont, hcoef, hmem, -⟩ := bridge_real hdj hψ hre
  have H3 : FrozenHyp d s (j + 3) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  -- level change `j - 2 → j`
  have hlev : frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) ψc τ =
      frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc τ := by
    refine frozenCoeff_level hd H.hs0 H.hsd (by omega) (by omega)
      (adjointData_frozen_level (j - 2) (H.mono (by omega)) 0 (τ + 1) (by linarith))
      (adjointData_frozen_level j H3 0 (τ + 1) (by linarith)) hψ ⟨hτ, by linarith⟩
  rw [hlev]
  obtain ⟨hmemF, -, -⟩ := frozenData hd j hjm H3 hcont hmem hτ
  rw [hcoef] at hmemF
  obtain ⟨hS1, hS2⟩ := hdec β V ρβ H (toFun ψc) hcont hmem τ hτ
  have hSeq := (S_eq hd j hjm H3 hcont hmem hτ).2 j (by positivity) le_rfl
  have hPeq := (proj_data j hjm H3 hcont hmem).2 j (by positivity) le_rfl
  rw [hcoef] at hSeq hPeq
  have hcen := centerCoeff_bound' hprob hρc hΛ (i := (j : ℝ)) (by positivity) hmemF
  refine ⟨hcen.1, ?_⟩
  have := hSeq.2
  rw [this] at hS2
  rw [hPeq.2] at hS2
  exact hS2

theorem frozen_center_smooth_coeff (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j)
    (νm νp c₀ Λ₀ : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ) (ψc : Coeff d), IsRealCoeff ψc →
      MemHs ((j : ℝ) - aExp d s) ψc → ∀ τ : ℝ, 0 < τ →
      MemHs (j : ℝ) (centerCoeff ρβ
        (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) ψc τ)) ∧
      hsNorm (j : ℝ) (centerCoeff ρβ
        (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) ψc τ)) ≤
        C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
          hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ ψc) := by
  obtain ⟨C, c, hC, hc, hsm⟩ := exists_frozen_smoothing' hd s j hj νm νp c₀ Λ₀
  refine ⟨C, c, hC, hc, fun β V ρβ H ψc hre hψa τ hτ => ?_⟩
  have hjm := mStar_add_two_le_of_gt hj
  have h3 := ClassicalPart.three_le_mStar d
  have hst := mStar_gt d
  have ha := aExp_spec (d := d) s H.hsd
  have hA2 : aExp d s < 2 := ha.2.1
  have hA1 : 1 ≤ aExp d s := ha.1
  have hjR : (mStar d : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hjm
  have hdjA : (d : ℝ) / 2 < (j : ℝ) - aExp d s := by linarith
  have hm0A : (mStar d : ℝ) ≤ (j : ℝ) - aExp d s := by linarith
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  obtain ⟨hsum, hcont, hcoef, hmem, -⟩ := bridge_real hdjA hψa hre
  have hmem0 : MemSobolev ((mStar d : ℕ) : ℝ) (toFun ψc) := memSobolev_mono_idx hmem hm0A
  have hS0 := S_eq_low hd (mStar d) le_rfl (H.mono (by omega)) hcont hmem0 hτ
  rw [hcoef] at hS0
  have hψ2 : MemHs (((j - 2 : ℕ)) : ℝ) ψc := hψa.mono (by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith)
  have hlev : frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d) ψc τ =
      frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) ψc τ := by
    refine frozenCoeff_level hd H.hs0 H.hsd (by omega) (by omega)
      (adjointData_frozen_level (mStar d) (H.mono (by omega)) 0 (τ + 1) (by linarith))
      (adjointData_frozen_level (j - 2) (H.mono (by omega)) 0 (τ + 1) (by linarith)) hψ2
      ⟨hτ.le, by linarith⟩
  rw [hlev] at hS0
  set Fz := frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) ψc τ with hFz
  have hFmem : MemHs (((j - 2 : ℕ)) : ℝ) Fz :=
    frozen_memHs hd s H.hs0 H.hsd (j - 2) (by omega) (H.mono (by omega)) hψ2 hτ.le
  have hdj2 : (d : ℝ) / 2 < (((j - 2 : ℕ)) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  have hFsum := summable_norm_of_memHs _ hdj2 _ hFmem
  have hFreal : IsRealCoeff Fz :=
    frozenCoeff_real hd H.hs0 H.hsd (by omega)
      (adjointData_frozen_level (j - 2) (H.mono (by omega)) 0 (τ + 1) (by linarith)) hψ2 hre
      ⟨hτ.le, by linarith⟩
  have hcsum := summable_center (ρ := ρβ) hFsum
  have hcreal := centerCoeff_isReal (ρ := ρβ) hFreal
  obtain ⟨hS1, hS2⟩ := hsm β V ρβ H (toFun ψc) hcont hmem τ hτ
  rw [hS0] at hS1 hS2
  have hco := coeffOf_toFun _ hcreal hcsum
  have hmemc : MemHs (j : ℝ) (centerCoeff ρβ Fz) := by
    have := (hsNormSq_coeffOf _ _ hS1).1
    rwa [hco] at this
  have hnm : sobolevNorm (j : ℝ) (toFun (centerCoeff ρβ Fz)) = hsNorm (j : ℝ) (centerCoeff ρβ Fz) := by
    rw [ClassicalPart.sobolevNorm_eq_hsNorm hS1, hco]
  have hpm := (projMean_toFun hprob hρc hsum hψa hre).2.2
  have hpe := (projMean_toFun hprob hρc hsum hψa hre).1
  rw [hpe, hpm, hnm] at hS2
  exact ⟨hmemc, hS2⟩

theorem exp_ineq {c₁ c κ σ τ t : ℝ} (hcc : c ≤ c₁ / 2) (hκ : 0 ≤ κ) (hστ : σ ≤ τ) :
    Real.exp (-c₁ * (τ - σ)) * Real.exp (-κ * (t - σ)) * Real.exp (-c * σ) ≤
      Real.exp (-κ * (t - τ)) * Real.exp (-c * τ) * Real.exp (-((c₁ / 2) * (τ - σ))) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : 0 ≤ τ - σ := by linarith
  nlinarith [mul_nonneg hκ h1, mul_nonneg (sub_nonneg.mpr hcc) h1]


/-- The Duhamel estimate at the coefficient level (abstract in the frozen propagator `U`). -/
theorem duh_core {ρβ : Torus d → ℝ} (hprob : IsProbDensity ρβ) (hρc : Continuous ρβ) {Λ₀ : ℝ}
    (hΛ : ∀ x, ρβ x ≤ Λ₀) (U : ℝ → Coeff d → Coeff d) (F E : ℝ → Coeff d) (φc : Coeff d)
    {t : ℝ} (j : ℕ) (a K₁ c₁ P κ c B : ℝ) (ha0 : 0 ≤ a) (ha2 : a < 2)
    (hja : 0 ≤ (j : ℝ) - a) (hK₁ : 0 ≤ K₁) (hP : 0 ≤ P) (hκ : 0 ≤ κ) (hcc : c ≤ c₁ / 2)
    (hB : ∀ τ : ℝ, 0 ≤ τ →
      IntervalIntegrable (fun σ : ℝ => (1 + (τ - σ) ^ (-(a / 2))) * Real.exp (-((c₁ / 2) * (τ - σ))))
        volume 0 τ ∧
      ∫ σ in (0:ℝ)..τ, (1 + (τ - σ) ^ (-(a / 2))) * Real.exp (-((c₁ / 2) * (τ - σ))) ≤ B)
    (hduh : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, F τ k = U τ φc k + ∫ σ in (0:ℝ)..τ, U (τ - σ) (E σ) k)
    (hFmem : ∀ σ ∈ Set.Icc (0:ℝ) t, MemHs (j : ℝ) (F σ))
    (hFreal : ∀ σ ∈ Set.Icc (0:ℝ) t, IsRealCoeff (F σ))
    (hUφ : ∀ τ ∈ Set.Icc (0:ℝ) t, IsRealCoeff (U τ φc) ∧ MemHs (j : ℝ) (U τ φc))
    (hsmooth : ∀ ψ : Coeff d, IsRealCoeff ψ → MemHs ((j : ℝ) - a) ψ → ∀ u : ℝ, 0 < u →
      MemHs (j : ℝ) (centerCoeff ρβ (U u ψ)) ∧
      hsNorm (j : ℝ) (centerCoeff ρβ (U u ψ)) ≤
        K₁ * (1 + u ^ (-(a / 2))) * Real.exp (-c₁ * u) * hsNorm ((j : ℝ) - a) (centerCoeff ρβ ψ))
    (hpert : ∀ σ ∈ Set.Icc (0:ℝ) t, IsRealCoeff (E σ) ∧ MemHs ((j : ℝ) - a) (E σ) ∧
      hsNorm ((j : ℝ) - a) (E σ) ≤ P * Real.exp (-κ * (t - σ)) * hsNorm (j : ℝ) (centerCoeff ρβ (F σ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) t) {Y : ℝ} (hY : 0 ≤ Y)
    (hFY : ∀ σ ∈ Set.Icc (0:ℝ) τ, hsNorm (j : ℝ) (centerCoeff ρβ (F σ)) ≤ Y * Real.exp (-c * σ)) :
    MemHs (j : ℝ) (centerCoeff ρβ (F τ) - centerCoeff ρβ (U τ φc)) ∧
      hsNorm (j : ℝ) (centerCoeff ρβ (F τ) - centerCoeff ρβ (U τ φc)) ≤
        (2 * (1 + Λ₀)) * (2 * (1 + Λ₀)) * K₁ * P * B * Y * Real.exp (-κ * (t - τ)) *
          Real.exp (-c * τ) := by
  have hΛ0 : 0 ≤ Λ₀ := (hprob.nonneg 0).trans (hΛ 0)
  set CQ : ℝ := 2 * (1 + Λ₀) with hCQ
  have hCQ0 : 0 ≤ CQ := by rw [hCQ]; positivity
  have hρ0 : MemHs 0 (coeffOf ρβ) := MFApriori.memHs_zero_coeffOf_continuous hρc
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hτ0 : 0 ≤ τ := hτ.1
  have hτt : τ ≤ t := hτ.2
  have hτI : τ ∈ Set.Icc (0:ℝ) t := hτ
  -- the Duhamel integral
  set I : Coeff d := fun k => ∫ σ in (0:ℝ)..τ, U (τ - σ) (E σ) k with hI
  have hFI : F τ = U τ φc + I := by
    funext k
    exact hduh τ hτI k
  have hIeq : I = F τ - U τ φc := by rw [hFI]; funext k; simp
  obtain ⟨hUre, hUmem⟩ := hUφ τ hτI
  have hIreal : IsRealCoeff I := by rw [hIeq]; exact isRealCoeff_sub' (hFreal τ hτI) hUre
  have hImem : MemHs (j : ℝ) I := by rw [hIeq]; exact memHs_sub (hFmem τ hτI) hUmem
  have hI0 : MemHs 0 I := by simpa using (hs_lower (γ := (j : ℝ)) hj0 hImem).1
  -- centered difference
  have hdiff : centerCoeff ρβ (F τ) - centerCoeff ρβ (U τ φc) = centerCoeff ρβ I := by
    rw [hIeq]
    exact (centerCoeff_sub' hρ0 (by simpa using (hs_lower (γ := (j : ℝ)) hj0 (hFmem τ hτI)).1)
      (by simpa using (hs_lower (γ := (j : ℝ)) hj0 hUmem).1)).symm
  rw [hdiff]
  -- kill the zero mode
  set I₀ : Coeff d := fun k => if k = 0 then 0 else I k with hI₀
  have hI00 : I 0 = (((I 0).re : ℝ) : ℂ) := by
    have h := hIreal 0
    simp only [neg_zero] at h
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      have := congrArg Complex.im h
      simp only [Complex.conj_im] at this
      linarith
  have hI₀eq : I₀ = I - (((I 0).re : ℝ) : ℂ) • deltaCoeff (0 : Lattice d) := by
    funext k
    by_cases hk : k = 0
    · subst hk
      simp only [hI₀, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, deltaCoeff, mul_one]
      rw [← hI00]; ring
    · simp [hI₀, hk, deltaCoeff]
  have hQI : centerCoeff ρβ I = centerCoeff ρβ I₀ :=
    (centerCoeff_eq_of_sub_delta hprob hρ0 hI0 _ hI₀eq).symm
  -- the majorant
  set Kc : ℝ := CQ * K₁ * P * Y * Real.exp (-κ * (t - τ)) * Real.exp (-c * τ) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  set h₂ : ℝ → ℝ := fun σ => Kc * ((1 + (τ - σ) ^ (-(a / 2))) * Real.exp (-((c₁ / 2) * (τ - σ))))
    with hh₂
  have hh₂int : IntervalIntegrable h₂ volume 0 τ := (hB τ hτ0).1.const_mul Kc
  set G : ℝ → Coeff d := fun σ => centerCoeff ρβ (U (τ - σ) (E σ)) with hG
  have hGmem : ∀ σ ∈ Set.Ioo (0:ℝ) τ, MemHs (j : ℝ) (G σ) ∧ hsNorm (j : ℝ) (G σ) ≤ h₂ σ := by
    intro σ hσ
    have hσt : σ ∈ Set.Icc (0:ℝ) t := ⟨hσ.1.le, hσ.2.le.trans hτt⟩
    have hσu : 0 < τ - σ := by linarith [hσ.2]
    obtain ⟨hEre, hEmem, hEn⟩ := hpert σ hσt
    obtain ⟨hs1, hs2⟩ := hsmooth (E σ) hEre hEmem (τ - σ) hσu
    refine ⟨hs1, hs2.trans ?_⟩
    have hQE := centerCoeff_bound' hprob hρc hΛ (i := (j : ℝ) - a) hja hEmem
    have hQn : hsNorm ((j : ℝ) - a) (centerCoeff ρβ (E σ)) ≤
        CQ * (P * Real.exp (-κ * (t - σ)) * (Y * Real.exp (-c * σ))) := by
      refine hQE.2.trans ?_
      refine (mul_le_mul_of_nonneg_left (hEn.trans ?_) hCQ0)
      exact mul_le_mul_of_nonneg_left (hFY σ ⟨hσ.1.le, hσ.2.le⟩) (by positivity)
    have hex := exp_ineq (c₁ := c₁) (c := c) (κ := κ) (σ := σ) (τ := τ) (t := t) hcc hκ hσ.2.le
    have hpos : 0 ≤ K₁ * (1 + (τ - σ) ^ (-(a / 2))) * Real.exp (-c₁ * (τ - σ)) := by
      have : 0 ≤ (τ - σ) ^ (-(a / 2)) := Real.rpow_nonneg hσu.le _
      positivity
    calc K₁ * (1 + (τ - σ) ^ (-(a / 2))) * Real.exp (-c₁ * (τ - σ)) *
          hsNorm ((j : ℝ) - a) (centerCoeff ρβ (E σ))
        ≤ K₁ * (1 + (τ - σ) ^ (-(a / 2))) * Real.exp (-c₁ * (τ - σ)) *
          (CQ * (P * Real.exp (-κ * (t - σ)) * (Y * Real.exp (-c * σ)))) :=
          mul_le_mul_of_nonneg_left hQn hpos
      _ = (CQ * K₁ * P * Y) * (1 + (τ - σ) ^ (-(a / 2))) *
          (Real.exp (-c₁ * (τ - σ)) * Real.exp (-κ * (t - σ)) * Real.exp (-c * σ)) := by ring
      _ ≤ (CQ * K₁ * P * Y) * (1 + (τ - σ) ^ (-(a / 2))) *
          (Real.exp (-κ * (t - τ)) * Real.exp (-c * τ) * Real.exp (-((c₁ / 2) * (τ - σ)))) := by
          have : 0 ≤ (1 + (τ - σ) ^ (-(a / 2))) := by
            have : 0 ≤ (τ - σ) ^ (-(a / 2)) := Real.rpow_nonneg hσu.le _
            linarith
          exact mul_le_mul_of_nonneg_left hex (by positivity)
      _ = h₂ σ := by rw [hh₂, hKc]; ring
  obtain ⟨hI'm, hI'n⟩ := hsNorm_intervalIntegral_le_majorant (j : ℝ) G h₂ 0 τ hτ0 hGmem
    (by rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hτ0]; exact hh₂int)
  set I' : Coeff d := fun k => ∫ σ in (0:ℝ)..τ, G σ k with hI'
  -- comparison `I₀ ≤ I'`
  have hI₀I' : ∀ k, ‖I₀ k‖ ≤ 1 * Lattice.jp k ^ (0:ℝ) * ‖I' k‖ := by
    intro k
    rw [Real.rpow_zero]
    by_cases hk : k = 0
    · simp [hI₀, hk]
    · simp only [hI₀, hk, if_false, one_mul, mul_one]
      refine le_of_eq ?_
      congr 1
      simp only [hI, hI', hG, centerCoeff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, deltaCoeff, hk,
        if_false, mul_zero, sub_zero]
  obtain ⟨hI₀m, hI₀n⟩ := hs_mult (m := (j : ℝ)) (γ := 0) (C := 1) zero_le_one hI'm hI₀I'
  simp only [sub_zero, one_mul] at hI₀m hI₀n
  have hQ := centerCoeff_bound' hprob hρc hΛ (i := (j : ℝ)) hj0 hI₀m
  rw [hQI]
  refine ⟨hQ.1, hQ.2.trans ?_⟩
  have hint2 : ∫ σ in (0:ℝ)..τ, h₂ σ ≤ Kc * B := by
    rw [hh₂, intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hB τ hτ0).2 hKc0
  calc 2 * (1 + Λ₀) * hsNorm (j : ℝ) I₀ ≤ CQ * (Kc * B) :=
        mul_le_mul_of_nonneg_left (hI₀n.trans (hI'n.trans hint2)) hCQ0
    _ = _ := by rw [hKc]; ring


theorem forwardGen_isReal (D : DynData d) (ρ : Torus d → ℝ) (hρ : IsRealCoeff (coeffOf ρ))
    (hV : IsRealCoeff (coeffOf D.V)) {F : Coeff d} (hF : IsRealCoeff F) :
    IsRealCoeff (forwardGen D ρ F) := by
  rw [isRealCoeff_iff_reflConj] at hF ⊢
  rw [← forwardGen_reflConj D ρ hρ hV F, hF]

theorem exists_perturbation (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) (hj : 1 ≤ j)
    (r₁ : ℝ) (hr₁ : (d : ℝ) / 2 + j < r₁) :
    ∃ CL : ℝ, 0 ≤ CL ∧ ∀ (D : DynData d), D.s = s → D.M = -1 → ∀ ρ₁ ρ₂ : Torus d → ℝ,
      Continuous ρ₁ → Continuous ρ₂ → MemHs r₁ (coeffOf ρ₁) → MemHs r₁ (coeffOf ρ₂) →
      (∀ i, MemHs 0 (driftCoeff D ρ₁ i)) → (∀ i, MemHs 0 (driftCoeff D ρ₂ i)) →
      ∀ (F : Coeff d) (δ : ℂ), MemHs (j : ℝ) F →
        MemHs ((j : ℝ) - aExp d s) (forwardGen D ρ₁ F - forwardGen D ρ₂ F) ∧
        hsNorm ((j : ℝ) - aExp d s) (forwardGen D ρ₁ F - forwardGen D ρ₂ F) ≤
          CL * hsNorm r₁ (coeffOf ρ₁ - coeffOf ρ₂) * hsNorm (j : ℝ) (F - δ • deltaCoeff 0) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨CL, hCL0, hdiff⟩ := exists_forwardGen_diff hd s hs0 hsd (j : ℝ) r₁ hj1 hr₁
  refine ⟨CL, hCL0, fun D hDs hDM ρ₁ ρ₂ hc1 hc2 h1 h2 hb1 hb2 F δ hF => ?_⟩
  have hF1 : MemHs 1 F := hF.mono hj1
  have hδ1 : MemHs 1 (δ • deltaCoeff (0 : Lattice d)) := memHs_smul_delta 1 δ
  have hρ10 : MemHs 0 (coeffOf ρ₁) := h1.mono (by linarith [show (0:ℝ) ≤ (d:ℝ)/2 + j by positivity])
  have hρ20 : MemHs 0 (coeffOf ρ₂) := h2.mono (by linarith [show (0:ℝ) ≤ (d:ℝ)/2 + j by positivity])
  have e1 := forwardGen_sub_H1 D ρ₁ hρ10 hb1 hF1 hδ1
  have e2 := forwardGen_sub_H1 D ρ₂ hρ20 hb2 hF1 hδ1
  rw [forwardGen_smul_delta, sub_zero] at e1 e2
  have hG : MemHs (j : ℝ) (F - δ • deltaCoeff (0 : Lattice d)) := memHs_sub hF (memHs_smul_delta _ δ)
  have := hdiff D hDs hDM ρ₁ ρ₂ hc1 hc2 h1 h2 _ hG
  rw [e1, e2] at this
  exact this

theorem exists_pert_path (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j) (r : ℝ)
    (hr : (d : ℝ) / 2 + j + 1 < r) (νm νp c₀ Λ₀ Cd κ : ℝ) (R : Regime) (MB Λ VB : ℝ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d + 2) νm νp c₀ Λ₀ β V ρβ) (μ : ℝ → Torus d → ℝ) (T : ℝ) (hT : 0 < T)
      (_ : AdjointData s j R MB Λ VB (mfData d s H.hs0 H.hsd V β H.hβ) νm T μ)
      (_ : ∀ σ, 0 ≤ σ → MemHs r (coeffOf (μ σ) - coeffOf ρβ) ∧
        hsNorm r (coeffOf (μ σ) - coeffOf ρβ) ≤ Cd * Real.exp (-κ * σ))
      (F : Coeff d), IsRealCoeff F → MemHs (j : ℝ) F → ∀ σ ∈ Set.Icc (0 : ℝ) T,
        IsRealCoeff (forwardGen (mfData d s H.hs0 H.hsd V β H.hβ) (μ σ) F -
          forwardGen (mfData d s H.hs0 H.hsd V β H.hβ) ρβ F) ∧
        MemHs ((j : ℝ) - aExp d s) (forwardGen (mfData d s H.hs0 H.hsd V β H.hβ) (μ σ) F -
          forwardGen (mfData d s H.hs0 H.hsd V β H.hβ) ρβ F) ∧
        hsNorm ((j : ℝ) - aExp d s) (forwardGen (mfData d s H.hs0 H.hsd V β H.hβ) (μ σ) F -
          forwardGen (mfData d s H.hs0 H.hsd V β H.hβ) ρβ F) ≤
          P * Real.exp (-κ * σ) * hsNorm (j : ℝ) (centerCoeff ρβ F) := by
  by_cases hsc : 0 ≤ s ∧ s < d
  swap
  · exact ⟨0, le_rfl, fun β V ρβ H => (hsc ⟨H.hs0, H.hsd⟩).elim⟩
  obtain ⟨hs0, hsd⟩ := hsc
  have h3 := ClassicalPart.three_le_mStar d
  have hst := mStar_gt d
  have hjpos : 1 ≤ j := by
    have : (0:ℝ) ≤ (d:ℝ)/2 := by positivity
    have : (1:ℝ) ≤ j := by linarith
    exact_mod_cast this
  set n : ℕ := j + mStar d + 2 with hn
  set r₁ : ℝ := min r (n : ℝ) with hr₁
  have hnR : (d : ℝ) / 2 + j < (n : ℝ) := by
    rw [hn]; push_cast; linarith
  have hr₁lt : (d : ℝ) / 2 + j < r₁ := lt_min (by linarith) hnR
  obtain ⟨CL, hCL0, hpert⟩ := exists_perturbation hd s hs0 hsd j hjpos r₁ hr₁lt
  refine ⟨CL * max Cd 0, mul_nonneg hCL0 (le_max_right _ _), ?_⟩
  intro β V ρβ H μ T hT hA hdec F hFre hF σ hσ
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have hDs : D.s = s := rfl
  have hDM : D.M = -1 := rfl
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hHj : FrozenHyp d s (j + 3) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hAβ := adjointData_frozen_level j hHj νm T hT
  -- multiplier bounds
  obtain ⟨K1, hK10, hK1⟩ := uniform_multBound hd hA
  obtain ⟨K2, hK20, hK2⟩ := uniform_multBound hd hAβ
  have hσ0 : (0:ℝ) ∈ Set.Icc (0:ℝ) T := ⟨le_rfl, hT.le⟩
  have hρ1c : Continuous (μ σ) := continuous_of_isCkU (hA.hμ.smooth σ hσ)
  -- Sobolev memberships at `r₁`
  have hρβn : MemHs (n : ℝ) (coeffOf ρβ) := (ClassicalPart.memHs_coeffOf_cbNorm n ρβ H.hρC).1
  have hρβr : MemHs r₁ (coeffOf ρβ) := hρβn.mono (min_le_right _ _)
  obtain ⟨hdm, hdn⟩ := hdec σ hσ.1
  have hdr : MemHs r₁ (coeffOf (μ σ) - coeffOf ρβ) := hdm.mono (min_le_left _ _)
  have hρ1r : MemHs r₁ (coeffOf (μ σ)) := by
    have := (hs_add_le r₁ hdr hρβr).1
    have e : (fun k => (coeffOf (μ σ) - coeffOf ρβ) k + coeffOf ρβ k) = coeffOf (μ σ) := by
      funext k; simp
    rwa [e] at this
  have hb1 : ∀ i, MemHs 0 (driftCoeff D (μ σ) i) := fun i => ((hK1 σ hσ).2 i).memHs0
  have hb2 : ∀ i, MemHs 0 (driftCoeff D ρβ i) := fun i => ((hK2 0 hσ0).2 i).memHs0
  have hF1 : MemHs (j : ℝ) F := hF
  obtain ⟨hm1, hn1⟩ := hpert D hDs hDM (μ σ) ρβ hρ1c hρc hρ1r hρβr hb1 hb2 F (meanCoeff ρβ F : ℂ) hF1
  -- reality
  have hρ1real : IsRealCoeff (coeffOf (μ σ)) := isRealCoeff_coeffOf_density hA.hμ hσ
  have hρβreal : IsRealCoeff (coeffOf ρβ) := isRealCoeff_coeffOf ρβ (integrable_of_cont hρc)
  have hVreal : IsRealCoeff (coeffOf D.V) := isRealCoeff_coeffOf_V hA.hV
  have hreal := isRealCoeff_sub' (forwardGen_isReal D (μ σ) hρ1real hVreal hFre)
    (forwardGen_isReal D ρβ hρβreal hVreal hFre)
  refine ⟨hreal, hm1, hn1.trans ?_⟩
  -- the norm of the difference
  have hdr_norm : hsNorm r₁ (coeffOf (μ σ) - coeffOf ρβ) ≤ hsNorm r (coeffOf (μ σ) - coeffOf ρβ) := by
    have := (hs_lower (γ := r - r₁) (by have := min_le_left r (n : ℝ); linarith) hdm).2
    rwa [sub_sub_cancel] at this
  have hcen : F - (meanCoeff ρβ F : ℂ) • deltaCoeff (0 : Lattice d) = centerCoeff ρβ F := rfl
  rw [hcen]
  have hN0 : 0 ≤ hsNorm (j : ℝ) (centerCoeff ρβ F) := hsNorm_nonneg' _ _
  have hD1 : hsNorm r₁ (coeffOf (μ σ) - coeffOf ρβ) ≤ max Cd 0 * Real.exp (-κ * σ) := by
    refine hdr_norm.trans (hdn.trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  calc CL * hsNorm r₁ (coeffOf (μ σ) - coeffOf ρβ) * hsNorm (j : ℝ) (centerCoeff ρβ F)
      ≤ CL * (max Cd 0 * Real.exp (-κ * σ)) * hsNorm (j : ℝ) (centerCoeff ρβ F) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD1 hCL0) hN0
    _ = _ := by ring


section TimeDep

variable {s : ℝ} {m : ℕ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ}
  {μ : ℝ → Torus d → ℝ}

/-- Linearity of the propagator path against constants. -/
theorem propagatorCoeff_sub_delta (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {φc : Coeff d}
    (hφ : MemHs (m : ℝ) φc) (c : ℂ) :
    ∀ τ ∈ Set.Icc (0:ℝ) t, propagatorCoeff D μ m t (φc - c • deltaCoeff (0 : Lattice d)) τ =
      propagatorCoeff D μ m t φc τ - c • deltaCoeff (0 : Lattice d) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  obtain ⟨h1, w1, -⟩ := hspec D ν₀ T μ hA t ht φc hφ
  have hsol := isForwardSolution_sub hd hA ht h1 (isForwardSolution_const_delta (D := D) (μ := μ) t c)
  have hw : WeakContinuousInHs 1 (fun _ => c • deltaCoeff (0 : Lattice d)) t :=
    ⟨fun _ _ => memHs_smul_delta 1 c, fun G _ => continuousOn_const⟩
  have hw' := weakContinuousInHs_sub (weakContinuousInHs_mono hm1 w1) hw
  exact propagatorCoeff_eq_of_solution hd hs0 hsd hm hA ht (memHs_sub hφ (memHs_smul_delta _ c))
    hsol hw'


/-- Semigroup (shift) property of the propagator path at the coefficient level. -/
theorem propagatorCoeff_shift (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {φc : Coeff d}
    (hφ : MemHs (m : ℝ) φc) {τ v : ℝ} (hτ : 0 ≤ τ) (hv : 0 < v) (hτv : τ + v = t) :
    MemHs (m : ℝ) (propagatorCoeff D μ m t φc τ) ∧
      ∀ σ ∈ Set.Icc (0:ℝ) v, propagatorCoeff D μ m v (propagatorCoeff D μ m t φc τ) σ =
        propagatorCoeff D μ m t φc (τ + σ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  obtain ⟨hF, hw, -⟩ := hspec D ν₀ T μ hA t ht φc hφ
  set F := propagatorCoeff D μ m t φc with hFdef
  have hτt : τ ∈ Set.Icc (0:ℝ) t := ⟨hτ, by linarith⟩
  have hFτm : MemHs (m : ℝ) (F τ) := hw.1 τ hτt
  refine ⟨hFτm, fun σ hσ => ?_⟩
  have hv' : v ∈ Set.Ioc 0 T := ⟨hv, by linarith [ht.2]⟩
  have hsol : IsForwardSolution D μ v (F τ) (fun σ => F (τ + σ)) := by
    refine ⟨fun σ hσ => hF.h1 (τ + σ) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩, fun k => ?_,
      fun k σ hσ => ?_⟩
    · have h1 : IntervalIntegrable (fun x => forwardGen D (μ (t - x)) (F x) k) volume τ (τ + v) := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
        exact (hF.integrable k).mono_set (Set.Icc_subset_Icc hτ (by linarith))
      have h2 := h1.comp_add_left τ
      simp only [sub_self, add_sub_cancel_left] at h2
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hv.le]
      refine h2.congr fun x _ => ?_
      show forwardGen D (μ (t - (τ + x))) (F (τ + x)) k = forwardGen D (μ (v - x)) (F (τ + x)) k
      rw [show t - (τ + x) = v - x by linarith]
    · have hi : ∀ b, 0 ≤ b → b ≤ t →
          IntervalIntegrable (fun x => forwardGen D (μ (t - x)) (F x) k) volume 0 b := by
        intro b hb0 hb1
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb0]
        exact (hF.integrable k).mono_set (Set.Icc_subset_Icc_right hb1)
      have e1 := hF.eq k (τ + σ) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
      have e2 := hF.eq k τ hτt
      have hI1 := hi τ hτ (by linarith)
      have hI2 : IntervalIntegrable (fun x => forwardGen D (μ (t - x)) (F x) k) volume τ (τ + σ) := by
        refine (hi (τ + σ) (by linarith [hσ.1]) (by linarith [hσ.2])).mono_set ?_
        rw [Set.uIcc_of_le (by linarith [hσ.1]), Set.uIcc_of_le (by linarith [hσ.1])]
        exact Set.Icc_subset_Icc hτ le_rfl
      have e3 := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
      have e4 := intervalIntegral.integral_comp_add_left
        (fun x => forwardGen D (μ (t - x)) (F x) k) (a := 0) (b := σ) τ
      simp only [add_zero] at e4
      show F (τ + σ) k = F τ k + ∫ x in (0:ℝ)..σ, forwardGen D (μ (v - x)) (F (τ + x)) k
      have e5 : ∫ x in (0:ℝ)..σ, forwardGen D (μ (v - x)) (F (τ + x)) k =
          ∫ x in (0:ℝ)..σ, forwardGen D (μ (t - (τ + x))) (F (τ + x)) k := by
        refine intervalIntegral.integral_congr fun x _ => ?_
        show forwardGen D (μ (v - x)) (F (τ + x)) k = forwardGen D (μ (t - (τ + x))) (F (τ + x)) k
        rw [show t - (τ + x) = v - x by linarith]
      rw [e5, e4, e1, e2, ← e3]
      ring
  have hw1 : WeakContinuousInHs 1 (fun σ => F (τ + σ)) v := by
    have hw' := weakContinuousInHs_mono hm1 hw
    refine ⟨fun σ hσ => hw'.1 (τ + σ) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩, fun G hG => ?_⟩
    refine (hw'.2 G hG).comp (continuous_const.add continuous_id).continuousOn fun σ hσ =>
      ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  exact propagatorCoeff_eq_of_solution hd hs0 hsd hm hA hv' hFτm hsol hw1 σ hσ


/-- Finite-time bound of the centered propagator path in terms of the centered datum. -/
theorem propagatorCoeff_center_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (R : Regime) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ} (_ : t ∈ Set.Ioc 0 T)
      {ρβ : Torus d → ℝ} (_ : IsProbDensity ρβ) (_ : Continuous ρβ) {Λ₀ : ℝ}
      (_ : ∀ x, ρβ x ≤ Λ₀) {φc : Coeff d} (_ : MemHs (m : ℝ) φc),
      ∀ τ ∈ Set.Icc (0:ℝ) t,
        MemHs (m : ℝ) (centerCoeff ρβ (propagatorCoeff D μ m t φc τ)) ∧
        hsNorm (m : ℝ) (centerCoeff ρβ (propagatorCoeff D μ m t φc τ)) ≤
          2 * (1 + Λ₀) * Real.exp (R.lambdaM C ν₀ (thetaOrder d s) * τ) *
            hsNorm (m : ℝ) (centerCoeff ρβ φc) := by
  obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  refine ⟨C, hC, fun D ν₀ T μ hA t ht ρβ hprob hρc Λ₀ hΛ φc hφ τ hτ => ?_⟩
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hρ0 : MemHs 0 (coeffOf ρβ) := MFApriori.memHs_zero_coeffOf_continuous hρc
  obtain ⟨h1, w1, b1⟩ := hspec D ν₀ T μ hA t ht φc hφ
  have hQφ : MemHs (m : ℝ) (centerCoeff ρβ φc) := (centerCoeff_bound' hprob hρc hΛ hm0 hφ).1
  obtain ⟨h2, w2, b2⟩ := hspec D ν₀ T μ hA t ht _ hQφ
  have hsub := propagatorCoeff_sub_delta hd hs0 hsd hm hA ht hφ (meanCoeff ρβ φc : ℂ) τ hτ
  have hP : MemHs (m : ℝ) (propagatorCoeff D μ m t φc τ) := w1.1 τ hτ
  have hP0 : MemHs 0 (propagatorCoeff D μ m t φc τ) := by
    simpa using (hs_lower (γ := (m : ℝ)) hm0 hP).1
  have hcc : centerCoeff ρβ (propagatorCoeff D μ m t (centerCoeff ρβ φc) τ) =
      centerCoeff ρβ (propagatorCoeff D μ m t φc τ) := by
    have e : propagatorCoeff D μ m t (centerCoeff ρβ φc) τ =
        propagatorCoeff D μ m t φc τ - (meanCoeff ρβ φc : ℂ) • deltaCoeff (0 : Lattice d) := hsub
    exact centerCoeff_eq_of_sub_delta hprob hρ0 hP0 _ e
  rw [← hcc]
  have hmem := w2.1 τ hτ
  have hc := centerCoeff_bound' hprob hρc hΛ hm0 hmem
  refine ⟨hc.1, hc.2.trans ?_⟩
  have := b2 τ hτ
  calc 2 * (1 + Λ₀) * hsNorm (m : ℝ) (propagatorCoeff D μ m t (centerCoeff ρβ φc) τ)
      ≤ 2 * (1 + Λ₀) * (Real.exp (R.lambdaM C ν₀ (thetaOrder d s) * τ) *
        hsNorm (m : ℝ) (centerCoeff ρβ φc)) := by
        refine mul_le_mul_of_nonneg_left this ?_
        have hΛ0 : 0 ≤ Λ₀ := (hprob.nonneg 0).trans (hΛ 0)
        positivity
    _ = _ := by ring

end TimeDep

/-- The sup-Gronwall closure. -/
theorem gronwall_close (w : ℝ → ℝ) (τb c c₁ κ K A Γ t r' : ℝ) (hc : 0 ≤ c) (hcc : c ≤ c₁)
    (hκ : 0 ≤ κ) (hΓ : 0 ≤ Γ) (hK : 0 ≤ K) (hA : 0 ≤ A) (hτb : 0 ≤ τb) (hr : r' ≤ t - τb)
    (hsmall : Γ * Real.exp (-κ * r') ≤ 1 / 2)
    (hw0 : ∀ τ ∈ Set.Icc (0:ℝ) τb, 0 ≤ w τ) (hwb : ∃ M, ∀ τ ∈ Set.Icc (0:ℝ) τb, w τ ≤ M)
    (hD : ∀ Y : ℝ, 0 ≤ Y → (∀ σ ∈ Set.Icc (0:ℝ) τb, w σ ≤ Y * Real.exp (-c * σ)) →
      ∀ τ ∈ Set.Icc (0:ℝ) τb,
        w τ ≤ K * Real.exp (-c₁ * τ) * A + Γ * Y * Real.exp (-κ * (t - τ)) * Real.exp (-c * τ)) :
    ∃ Y : ℝ, 0 ≤ Y ∧ Y ≤ 2 * K * A ∧ ∀ σ ∈ Set.Icc (0:ℝ) τb, w σ ≤ Y * Real.exp (-c * σ) := by
  obtain ⟨M, hM⟩ := hwb
  set S : Set ℝ := (fun τ => Real.exp (c * τ) * w τ) '' Set.Icc (0:ℝ) τb with hS
  have hne : S.Nonempty := ⟨_, 0, ⟨le_rfl, hτb⟩, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨Real.exp (c * τb) * M, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    have h1 : Real.exp (c * τ) ≤ Real.exp (c * τb) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 hc)
    calc Real.exp (c * τ) * w τ ≤ Real.exp (c * τb) * w τ :=
          mul_le_mul_of_nonneg_right h1 (hw0 τ hτ)
      _ ≤ Real.exp (c * τb) * M := mul_le_mul_of_nonneg_left (hM τ hτ) (Real.exp_pos _).le
  set Y : ℝ := sSup S with hY
  have hyY : ∀ τ ∈ Set.Icc (0:ℝ) τb, Real.exp (c * τ) * w τ ≤ Y := fun τ hτ =>
    le_csSup hbdd ⟨τ, hτ, rfl⟩
  have hY0 : 0 ≤ Y := by
    have := hyY 0 ⟨le_rfl, hτb⟩
    have h0 := hw0 0 ⟨le_rfl, hτb⟩
    simp only [mul_zero, Real.exp_zero, one_mul] at this
    linarith
  have hwY : ∀ σ ∈ Set.Icc (0:ℝ) τb, w σ ≤ Y * Real.exp (-c * σ) := by
    intro σ hσ
    have := hyY σ hσ
    have e : w σ = Real.exp (-c * σ) * (Real.exp (c * σ) * w σ) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [e, mul_comm Y]
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
  have hkey : ∀ τ ∈ Set.Icc (0:ℝ) τb, Real.exp (c * τ) * w τ ≤ K * A + Y / 2 := by
    intro τ hτ
    have h := hD Y hY0 hwY τ hτ
    have h1 : Real.exp (c * τ) * w τ ≤ Real.exp (c * τ) * (K * Real.exp (-c₁ * τ) * A +
        Γ * Y * Real.exp (-κ * (t - τ)) * Real.exp (-c * τ)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    have e1 : Real.exp (c * τ) * (K * Real.exp (-c₁ * τ) * A +
        Γ * Y * Real.exp (-κ * (t - τ)) * Real.exp (-c * τ)) =
        K * A * Real.exp ((c - c₁) * τ) + Γ * Y * Real.exp (-κ * (t - τ)) := by
      have a1 : Real.exp (c * τ) * Real.exp (-c₁ * τ) = Real.exp ((c - c₁) * τ) := by
        rw [← Real.exp_add]; ring_nf
      have a2 : Real.exp (c * τ) * Real.exp (-c * τ) = 1 := by
        rw [← Real.exp_add]; simp
      calc _ = K * A * (Real.exp (c * τ) * Real.exp (-c₁ * τ)) +
            Γ * Y * Real.exp (-κ * (t - τ)) * (Real.exp (c * τ) * Real.exp (-c * τ)) := by ring
        _ = _ := by rw [a1, a2]; ring
    have h2 : Real.exp ((c - c₁) * τ) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [hτ.1]
    have h3 : Real.exp (-κ * (t - τ)) ≤ Real.exp (-κ * r') := by
      apply Real.exp_le_exp.mpr
      nlinarith [hτ.2]
    have hKA : 0 ≤ K * A := mul_nonneg hK hA
    calc Real.exp (c * τ) * w τ ≤ _ := h1
      _ = _ := e1
      _ ≤ K * A * 1 + Γ * Y * Real.exp (-κ * r') := by
          gcongr
      _ ≤ K * A + Y / 2 := by
          have : Γ * Y * Real.exp (-κ * r') = Y * (Γ * Real.exp (-κ * r')) := by ring
          rw [mul_one, this]
          nlinarith
  have hYle : Y ≤ K * A + Y / 2 := by
    refine csSup_le hne ?_
    rintro _ ⟨τ, hτ, rfl⟩
    exact hkey τ hτ
  exact ⟨Y, hY0, by linarith, hwY⟩


/-- Case (i) of the decay estimate, abstract in the frozen propagator `U`. -/
theorem case_i_abstract {ρβ : Torus d → ℝ} (hprob : IsProbDensity ρβ) (hρc : Continuous ρβ) {Λ₀ : ℝ}
    (hΛ : ∀ x, ρβ x ≤ Λ₀) (U : ℝ → Coeff d → Coeff d) (F E : ℝ → Coeff d) (φc : Coeff d)
    {t : ℝ} (j : ℕ) (a K₁ K₂ c₁ P κ B r' : ℝ) (ha0 : 0 ≤ a) (ha2 : a < 2)
    (hja : 0 ≤ (j : ℝ) - a) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hP : 0 ≤ P) (hκ : 0 ≤ κ) (hc₁ : 0 ≤ c₁)
    (hB : ∀ τ : ℝ, 0 ≤ τ →
      IntervalIntegrable (fun σ : ℝ => (1 + (τ - σ) ^ (-(a / 2))) * Real.exp (-((c₁ / 2) * (τ - σ))))
        volume 0 τ ∧
      ∫ σ in (0:ℝ)..τ, (1 + (τ - σ) ^ (-(a / 2))) * Real.exp (-((c₁ / 2) * (τ - σ))) ≤ B)
    (hduh : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, F τ k = U τ φc k + ∫ σ in (0:ℝ)..τ, U (τ - σ) (E σ) k)
    (hFmem : ∀ σ ∈ Set.Icc (0:ℝ) t, MemHs (j : ℝ) (F σ))
    (hFreal : ∀ σ ∈ Set.Icc (0:ℝ) t, IsRealCoeff (F σ))
    (hUφ : ∀ τ ∈ Set.Icc (0:ℝ) t, IsRealCoeff (U τ φc) ∧ MemHs (j : ℝ) (U τ φc))
    (hsmooth : ∀ ψ : Coeff d, IsRealCoeff ψ → MemHs ((j : ℝ) - a) ψ → ∀ u : ℝ, 0 < u →
      MemHs (j : ℝ) (centerCoeff ρβ (U u ψ)) ∧
      hsNorm (j : ℝ) (centerCoeff ρβ (U u ψ)) ≤
        K₁ * (1 + u ^ (-(a / 2))) * Real.exp (-c₁ * u) * hsNorm ((j : ℝ) - a) (centerCoeff ρβ ψ))
    (hdecay : ∀ τ ∈ Set.Icc (0:ℝ) t, hsNorm (j : ℝ) (centerCoeff ρβ (U τ φc)) ≤
      K₂ * Real.exp (-c₁ * τ) * hsNorm (j : ℝ) (centerCoeff ρβ φc))
    (hpert : ∀ σ ∈ Set.Icc (0:ℝ) t, IsRealCoeff (E σ) ∧ MemHs ((j : ℝ) - a) (E σ) ∧
      hsNorm ((j : ℝ) - a) (E σ) ≤ P * Real.exp (-κ * (t - σ)) * hsNorm (j : ℝ) (centerCoeff ρβ (F σ)))
    (hFbdd : ∃ M : ℝ, ∀ σ ∈ Set.Icc (0:ℝ) t, hsNorm (j : ℝ) (F σ) ≤ M)
    {τb : ℝ} (hτb : τb ∈ Set.Icc (0:ℝ) t) (hr : r' ≤ t - τb)
    (hsmall : (2 * (1 + Λ₀)) * (2 * (1 + Λ₀)) * K₁ * P * B * Real.exp (-κ * r') ≤ 1 / 2) :
    hsNorm (j : ℝ) (centerCoeff ρβ (F τb)) ≤
        2 * K₂ * hsNorm (j : ℝ) (centerCoeff ρβ φc) * Real.exp (-(c₁ / 2) * τb) ∧
    MemHs (j : ℝ) (centerCoeff ρβ (F τb) - centerCoeff ρβ (U τb φc)) ∧
    hsNorm (j : ℝ) (centerCoeff ρβ (F τb) - centerCoeff ρβ (U τb φc)) ≤
      (2 * (1 + Λ₀)) * (2 * (1 + Λ₀)) * K₁ * P * B * (2 * K₂ * hsNorm (j : ℝ) (centerCoeff ρβ φc)) *
        Real.exp (-κ * (t - τb)) * Real.exp (-(c₁ / 2) * τb) := by
  have hΛ0 : 0 ≤ Λ₀ := (hprob.nonneg 0).trans (hΛ 0)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set Γ : ℝ := (2 * (1 + Λ₀)) * (2 * (1 + Λ₀)) * K₁ * P * B with hΓ
  have hB0 : 0 ≤ B := by
    have := (hB 0 le_rfl).2
    rwa [intervalIntegral.integral_same] at this
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
  set A : ℝ := hsNorm (j : ℝ) (centerCoeff ρβ φc) with hA
  have hA0 : 0 ≤ A := hsNorm_nonneg' _ _
  set w : ℝ → ℝ := fun τ => hsNorm (j : ℝ) (centerCoeff ρβ (F τ)) with hw
  have hw0 : ∀ τ ∈ Set.Icc (0:ℝ) τb, 0 ≤ w τ := fun τ _ => hsNorm_nonneg' _ _
  have hτb' : τb ∈ Set.Icc (0:ℝ) t := hτb
  have hsub : ∀ τ ∈ Set.Icc (0:ℝ) τb, τ ∈ Set.Icc (0:ℝ) t := fun τ hτ => ⟨hτ.1, hτ.2.trans hτb.2⟩
  have hwb : ∃ M, ∀ τ ∈ Set.Icc (0:ℝ) τb, w τ ≤ M := by
    obtain ⟨M, hM⟩ := hFbdd
    refine ⟨2 * (1 + Λ₀) * M, fun τ hτ => ?_⟩
    have := (centerCoeff_bound' hprob hρc hΛ hj0 (hFmem τ (hsub τ hτ))).2
    exact this.trans (mul_le_mul_of_nonneg_left (hM τ (hsub τ hτ)) (by positivity))
  have hQUmem : ∀ τ ∈ Set.Icc (0:ℝ) t, MemHs (j : ℝ) (centerCoeff ρβ (U τ φc)) := fun τ hτ =>
    (centerCoeff_bound' hprob hρc hΛ hj0 (hUφ τ hτ).2).1
  have hD : ∀ Y : ℝ, 0 ≤ Y → (∀ σ ∈ Set.Icc (0:ℝ) τb, w σ ≤ Y * Real.exp (-(c₁ / 2) * σ)) →
      ∀ τ ∈ Set.Icc (0:ℝ) τb, w τ ≤ K₂ * Real.exp (-c₁ * τ) * A +
        Γ * Y * Real.exp (-κ * (t - τ)) * Real.exp (-(c₁ / 2) * τ) := by
    intro Y hY hwY τ hτ
    have hτt := hsub τ hτ
    obtain ⟨hdm, hdn⟩ := duh_core hprob hρc hΛ U F E φc j a K₁ c₁ P κ (c₁ / 2) B ha0 ha2 hja hK₁ hP hκ
      le_rfl hB hduh hFmem hFreal hUφ hsmooth hpert hτt hY (fun σ hσ => hwY σ ⟨hσ.1, hσ.2.trans hτ.2⟩)
    have hQF : centerCoeff ρβ (F τ) = fun k => (centerCoeff ρβ (F τ) - centerCoeff ρβ (U τ φc)) k +
        centerCoeff ρβ (U τ φc) k := by funext k; simp
    have htri := (hs_add_le (j : ℝ) hdm (hQUmem τ hτt)).2
    show hsNorm (j : ℝ) (centerCoeff ρβ (F τ)) ≤ _
    rw [hQF]
    refine htri.trans ?_
    have := hdecay τ hτt
    linarith
  obtain ⟨Y, hY0, hY2, hwY⟩ := gronwall_close w τb (c₁ / 2) c₁ κ K₂ A Γ t r' (by linarith) (by linarith)
    hκ hΓ0 hK₂ hA0 hτb.1 hr hsmall hw0 hwb hD
  have hwτ := hwY τb ⟨hτb.1, le_rfl⟩
  have hY2' : Y ≤ 2 * K₂ * A := hY2
  refine ⟨hwτ.trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right hY2' (Real.exp_pos _).le
  obtain ⟨hdm, hdn⟩ := duh_core hprob hρc hΛ U F E φc j a K₁ c₁ P κ (c₁ / 2) B ha0 ha2 hja hK₁ hP hκ
      le_rfl hB hduh hFmem hFreal hUφ hsmooth hpert hτb' hY0 hwY
  refine ⟨hdm, hdn.trans ?_⟩
  have hE1 : 0 ≤ Real.exp (-κ * (t - τb)) * Real.exp (-(c₁ / 2) * τb) := by positivity
  calc (2 * (1 + Λ₀)) * (2 * (1 + Λ₀)) * K₁ * P * B * Y * Real.exp (-κ * (t - τb)) *
        Real.exp (-(c₁ / 2) * τb)
      = Γ * Y * (Real.exp (-κ * (t - τb)) * Real.exp (-(c₁ / 2) * τb)) := by rw [hΓ]; ring
    _ ≤ Γ * (2 * K₂ * A) * (Real.exp (-κ * (t - τb)) * Real.exp (-(c₁ / 2) * τb)) := by
        gcongr
    _ = _ := by rw [hΓ]; ring


theorem frozen_lvl_data (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j)
    {νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ) {ψc : Coeff d} (hre : IsRealCoeff ψc)
    (hψ : MemHs (j : ℝ) ψc) {τ : ℝ} (hτ : 0 ≤ τ) :
    frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) ψc τ =
      frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc τ ∧
    IsRealCoeff (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) ψc τ) ∧
    MemHs (j : ℝ) (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) ψc τ) := by
  have hjm := mStar_add_two_le_of_gt hj
  have h3 := ClassicalPart.three_le_mStar d
  have hlev : frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) ψc τ =
      frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc τ := by
    refine frozenCoeff_level hd H.hs0 H.hsd (by omega) (by omega)
      (adjointData_frozen_level (j - 2) (H.mono (by omega)) 0 (τ + 1) (by linarith))
      (adjointData_frozen_level j (H.mono (by omega)) 0 (τ + 1) (by linarith)) hψ ⟨hτ, by linarith⟩
  refine ⟨hlev, ?_, ?_⟩
  · rw [hlev]
    exact frozenCoeff_real hd H.hs0 H.hsd (by omega)
      (adjointData_frozen_level j (H.mono (by omega)) 0 (τ + 1) (by linarith)) hψ hre
      ⟨hτ, by linarith⟩
  · rw [hlev]
    exact frozen_memHs hd s H.hs0 H.hsd j (by omega) H hψ hτ


theorem hsNorm_sub_le' (a : ℝ) {x y : Coeff d} (hx : MemHs a x) (hy : MemHs a y) :
    MemHs a (x - y) ∧ hsNorm a (x - y) ≤ hsNorm a x + hsNorm a y := by
  obtain ⟨h1, h2⟩ := hs_neg hy
  obtain ⟨h3, h4⟩ := hs_add_le a hx h1
  have e : (x - y) = fun k => x k + -y k := by funext k; simp [sub_eq_add_neg]
  rw [e]
  exact ⟨h3, h4.trans (by linarith)⟩

theorem exists_R0 (Γ κ : ℝ) (hΓ : 0 ≤ Γ) (hκ : 0 < κ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ ρ : ℝ, R₀ ≤ ρ → Γ * Real.exp (-κ * ρ) ≤ 1 / 2 := by
  refine ⟨max 1 (2 * Γ / κ), le_max_left _ _, fun ρ hρ => ?_⟩
  have h1 : 2 * Γ / κ ≤ ρ := (le_max_right _ _).trans hρ
  have h2 : 2 * Γ ≤ κ * ρ := by
    rw [div_le_iff₀ hκ] at h1; linarith
  have hρ0 : 0 ≤ ρ := by have := le_max_left (1:ℝ) (2 * Γ / κ); linarith
  have h3 : κ * ρ + 1 ≤ Real.exp (κ * ρ) := by linarith [Real.add_one_le_exp (κ * ρ)]
  have h4 : Real.exp (-κ * ρ) * Real.exp (κ * ρ) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < κ * ρ + 1 := by nlinarith [mul_nonneg hκ.le hρ0]
  have h5 : Real.exp (-κ * ρ) * (κ * ρ + 1) ≤ 1 := by
    calc Real.exp (-κ * ρ) * (κ * ρ + 1) ≤ Real.exp (-κ * ρ) * Real.exp (κ * ρ) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = 1 := h4
  have h6 : Γ * Real.exp (-κ * ρ) * 2 ≤ 1 := by
    have : Γ * Real.exp (-κ * ρ) * 2 ≤ Real.exp (-κ * ρ) * (κ * ρ) := by
      nlinarith [Real.exp_pos (-κ * ρ)]
    nlinarith
  linarith




theorem assemble_bounds {Kd Γ X3 κ R₀ c₁ A t τ C a1 a2 a3 : ℝ} (hKd : 0 ≤ Kd) (hΓ : 0 ≤ Γ)
    (hX3 : 0 ≤ X3) (hκ : 0 ≤ κ) (hR₀ : 0 ≤ R₀) (hA : 0 ≤ A)
    (hC : C = 2 * Kd + Γ * (2 * Kd) + (X3 + Kd) * Real.exp (κ * R₀) + 1)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hc₁ : 0 ≤ c₁) (hτ0 : 0 ≤ τ)
    (hi : R₀ ≤ t - τ → a1 ≤ 2 * Kd * A * Real.exp (-(c₁ / 2) * τ) ∧
      a3 ≤ Γ * (2 * Kd * A) * Real.exp (-κ * (t - τ)) * Real.exp (-(c₁ / 2) * τ))
    (hii : t - τ < R₀ → a1 ≤ X3 * Real.exp (-(c₁ / 2) * τ) * A)
    (hdec : a2 ≤ Kd * Real.exp (-c₁ * τ) * A) (htri : a3 ≤ a1 + a2) :
    a1 ≤ C * Real.exp (-(c₁ / 2) * τ) * A ∧
      a3 ≤ C * Real.exp (-(c₁ / 2) * τ) * Real.exp (-κ * (t - τ)) * A := by
  have hE1 : 0 < Real.exp (-(c₁ / 2) * τ) := Real.exp_pos _
  have hE2 : 0 < Real.exp (-κ * (t - τ)) := Real.exp_pos _
  have hE3 : 1 ≤ Real.exp (κ * R₀) := Real.one_le_exp (by positivity)
  have hP : 0 ≤ A * Real.exp (-(c₁ / 2) * τ) := by positivity
  have hP2 : 0 ≤ A * Real.exp (-(c₁ / 2) * τ) * Real.exp (-κ * (t - τ)) := by positivity
  have hG1 : 0 ≤ Γ * (2 * Kd) := by positivity
  have hG2 : 0 ≤ (X3 + Kd) * Real.exp (κ * R₀) := by positivity
  by_cases hcase : R₀ ≤ t - τ
  · obtain ⟨b1, b3⟩ := hi hcase
    have hCge1 : 2 * Kd ≤ C := by rw [hC]; linarith
    have hCge2 : Γ * (2 * Kd) ≤ C := by rw [hC]; linarith
    refine ⟨b1.trans ?_, b3.trans ?_⟩
    · calc 2 * Kd * A * Real.exp (-(c₁ / 2) * τ) = (2 * Kd) * (A * Real.exp (-(c₁ / 2) * τ)) := by ring
        _ ≤ C * (A * Real.exp (-(c₁ / 2) * τ)) := mul_le_mul_of_nonneg_right hCge1 hP
        _ = _ := by ring
    · calc Γ * (2 * Kd * A) * Real.exp (-κ * (t - τ)) * Real.exp (-(c₁ / 2) * τ)
          = (Γ * (2 * Kd)) * (A * Real.exp (-(c₁ / 2) * τ) * Real.exp (-κ * (t - τ))) := by ring
        _ ≤ C * (A * Real.exp (-(c₁ / 2) * τ) * Real.exp (-κ * (t - τ))) :=
            mul_le_mul_of_nonneg_right hCge2 hP2
        _ = _ := by ring
  · have hlt : t - τ < R₀ := not_le.mp hcase
    have b1 := hii hlt
    have hX4 : X3 + Kd ≤ (X3 + Kd) * Real.exp (κ * R₀) := by
      have : 0 ≤ X3 + Kd := by positivity
      nlinarith
    have hCge : X3 + Kd ≤ C := by rw [hC]; nlinarith
    have hexpd : Real.exp (-c₁ * τ) ≤ Real.exp (-(c₁ / 2) * τ) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have ha2' : a2 ≤ Kd * (A * Real.exp (-(c₁ / 2) * τ)) := by
      calc a2 ≤ Kd * Real.exp (-c₁ * τ) * A := hdec
        _ = Kd * (Real.exp (-c₁ * τ) * A) := by ring
        _ ≤ Kd * (Real.exp (-(c₁ / 2) * τ) * A) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexpd hA) hKd
        _ = _ := by ring
    have ha1' : a1 ≤ X3 * (A * Real.exp (-(c₁ / 2) * τ)) := by
      calc a1 ≤ X3 * Real.exp (-(c₁ / 2) * τ) * A := b1
        _ = _ := by ring
    have hsum : a1 + a2 ≤ (X3 + Kd) * (A * Real.exp (-(c₁ / 2) * τ)) := by nlinarith
    have hKcomp : 1 ≤ Real.exp (κ * R₀) * Real.exp (-κ * (t - τ)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    refine ⟨?_, ?_⟩
    · calc a1 ≤ X3 * (A * Real.exp (-(c₁ / 2) * τ)) := ha1'
        _ ≤ (X3 + Kd) * (A * Real.exp (-(c₁ / 2) * τ)) :=
            mul_le_mul_of_nonneg_right (by linarith) hP
        _ ≤ C * (A * Real.exp (-(c₁ / 2) * τ)) := mul_le_mul_of_nonneg_right hCge hP
        _ = _ := by ring
    · calc a3 ≤ a1 + a2 := htri
        _ ≤ (X3 + Kd) * (A * Real.exp (-(c₁ / 2) * τ)) := hsum
        _ ≤ (X3 + Kd) * Real.exp (κ * R₀) * Real.exp (-κ * (t - τ)) *
              (A * Real.exp (-(c₁ / 2) * τ)) := by
            have h0 : 0 ≤ (X3 + Kd) * (A * Real.exp (-(c₁ / 2) * τ)) := by positivity
            calc (X3 + Kd) * (A * Real.exp (-(c₁ / 2) * τ))
                = (X3 + Kd) * (A * Real.exp (-(c₁ / 2) * τ)) * 1 := by ring
              _ ≤ (X3 + Kd) * (A * Real.exp (-(c₁ / 2) * τ)) *
                  (Real.exp (κ * R₀) * Real.exp (-κ * (t - τ))) := mul_le_mul_of_nonneg_left hKcomp h0
              _ = _ := by ring
        _ ≤ C * Real.exp (-κ * (t - τ)) * (A * Real.exp (-(c₁ / 2) * τ)) := by
            have : (X3 + Kd) * Real.exp (κ * R₀) ≤ C := by rw [hC]; linarith
            calc (X3 + Kd) * Real.exp (κ * R₀) * Real.exp (-κ * (t - τ)) *
                (A * Real.exp (-(c₁ / 2) * τ))
                ≤ C * Real.exp (-κ * (t - τ)) * (A * Real.exp (-(c₁ / 2) * τ)) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hE2.le) hP
              _ = _ := rfl
        _ = _ := by ring


theorem exp_aux (lam c R₀ s' τ₀ : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s') (hsR : s' ≤ R₀) :
    Real.exp (lam * s') * Real.exp (-c * τ₀) ≤
      Real.exp (|lam| * R₀) * Real.exp (c * R₀) * Real.exp (-c * (τ₀ + s')) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : lam * s' ≤ |lam| * R₀ := by
    calc lam * s' ≤ |lam| * s' := mul_le_mul_of_nonneg_right (le_abs_self _) hs
      _ ≤ |lam| * R₀ := mul_le_mul_of_nonneg_left hsR (abs_nonneg _)
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hsR)]


set_option maxHeartbeats 1600000 in
theorem main_coeff (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j) (νm νp c₀ Λ₀ : ℝ)
    (r : ℝ) (hr : (d : ℝ) / 2 + j + 1 < r) (R : Regime) (MB Λ VB : ℝ) (Cd κ : ℝ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d + 2) νm νp c₀ Λ₀ β V ρβ) (μ : ℝ → Torus d → ℝ),
      (∀ T, 0 < T → AdjointData s j R MB Λ VB (mfData d s H.hs0 H.hsd V β H.hβ) νm T μ) →
      (∀ σ, 0 ≤ σ → MemHs r (coeffOf (μ σ) - coeffOf ρβ) ∧
        hsNorm r (coeffOf (μ σ) - coeffOf ρβ) ≤ Cd * Real.exp (-κ * σ)) →
      ∀ φc : Coeff d, IsRealCoeff φc → MemHs (j : ℝ) φc → ∀ t : ℝ, 0 < t → ∀ τ ∈ Set.Icc (0:ℝ) t,
        MemHs (j : ℝ) (centerCoeff ρβ (propagatorCoeff (mfData d s H.hs0 H.hsd V β H.hβ) μ j t φc τ)) ∧
        hsNorm (j : ℝ) (centerCoeff ρβ (propagatorCoeff (mfData d s H.hs0 H.hsd V β H.hβ) μ j t φc τ)) ≤
          C * Real.exp (-c * τ) * hsNorm (j : ℝ) (centerCoeff ρβ φc) ∧
        MemHs (j : ℝ) (centerCoeff ρβ (propagatorCoeff (mfData d s H.hs0 H.hsd V β H.hβ) μ j t φc τ) -
          centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) φc τ)) ∧
        hsNorm (j : ℝ) (centerCoeff ρβ (propagatorCoeff (mfData d s H.hs0 H.hsd V β H.hβ) μ j t φc τ) -
          centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (j - 2) φc τ)) ≤
          C * Real.exp (-c * τ) * Real.exp (-κ * (t - τ)) * hsNorm (j : ℝ) (centerCoeff ρβ φc) := by
  by_cases hsc : 0 ≤ s ∧ s < d
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun β V ρβ H => (hsc ⟨H.hs0, H.hsd⟩).elim⟩
  obtain ⟨hs0, hsd⟩ := hsc
  have hjm := mStar_add_two_le_of_gt hj
  have h3 := ClassicalPart.three_le_mStar d
  have ha := aExp_spec (d := d) s hsd
  have hst := mStar_gt d
  have hj1 : 1 ≤ j := by omega
  have hjR : (mStar d : ℝ) + 2 ≤ j := by exact_mod_cast hjm
  have hja : 0 ≤ (j : ℝ) - aExp d s := by linarith [ha.2.1]
  obtain ⟨Kd, cd, hKd, hcd, hdec⟩ := frozen_center_decay_coeff hd s j hj νm νp c₀ Λ₀
  obtain ⟨Ks, cs, hKs, hcs, hsm⟩ := frozen_center_smooth_coeff hd s j hj νm νp c₀ Λ₀
  obtain ⟨P, hP0, hpert⟩ := exists_pert_path hd s j hj r hr νm νp c₀ Λ₀ Cd κ R MB Λ VB
  obtain ⟨Csp, hCsp, hcen⟩ := propagatorCoeff_center_bound hd hs0 hsd hj1 R MB Λ VB
  obtain ⟨Cspec, hCspec, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd j hj1 R MB Λ VB
  set c₁ : ℝ := min cd cs with hc₁def
  have hc₁ : 0 < c₁ := lt_min hcd hcs
  have hc₁cd : c₁ ≤ cd := min_le_left _ _
  have hc₁cs : c₁ ≤ cs := min_le_right _ _
  obtain ⟨B, hB0, hB⟩ := exists_kernel_bound (aExp d s / 2) (c₁ / 2) (by linarith [ha.2.1])
    (by linarith)
  set Γ : ℝ := (2 * (1 + Λ₀)) * (2 * (1 + Λ₀)) * Ks * P * B with hΓ
  have hΓ0 : 0 ≤ Γ := by
    have : 0 ≤ (2 * (1 + Λ₀)) * (2 * (1 + Λ₀)) := mul_self_nonneg _
    rw [hΓ]
    have := hKs.le
    positivity
  obtain ⟨R₀, hR₀1, hR₀⟩ := exists_R0 Γ κ hΓ0 hκ
  have hR₀pos : 0 < R₀ := by linarith
  set lam : ℝ := R.lambdaM Csp νm (thetaOrder d s) with hlam
  set Λ₁ : ℝ := max Λ₀ 0 with hΛ₁
  have hΛ₁0 : 0 ≤ Λ₁ := le_max_right _ _
  set X3 : ℝ := 2 * (1 + Λ₁) * Real.exp (|lam| * R₀) * Real.exp ((c₁ / 2) * R₀) * (1 + 2 * Kd)
    with hX3
  have hX30 : 0 ≤ X3 := by rw [hX3]; positivity
  set C : ℝ := 2 * Kd + Γ * (2 * Kd) + (X3 + Kd) * Real.exp (κ * R₀) + 1 with hC
  have hC0 : 0 < C := by
    rw [hC]
    have : 0 ≤ Γ * (2 * Kd) := by positivity
    have : 0 ≤ (X3 + Kd) * Real.exp (κ * R₀) := by positivity
    linarith
  have hexpκ : 1 ≤ Real.exp (κ * R₀) := Real.one_le_exp (by positivity)
  refine ⟨C, c₁ / 2, hC0, by linarith, ?_⟩
  intro β V ρβ H μ hA hdecμ φc hre hφ t ht τ hτ
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have hH3 : FrozenHyp d s (j + 3) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hHj : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  have hΛ0 : 0 ≤ Λ₀ := (hprob.nonneg 0).trans (hΛ 0)
  have hΛ1 : 2 * (1 + Λ₀) ≤ 2 * (1 + Λ₁) := by have := le_max_left Λ₀ 0; linarith
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hAt := hA t ht
  have hAβ := adjointData_frozen_level j hH3 νm t ht
  have hν : 0 < D.invβ := inv_pos.mpr H.hβ
  have htI : t ∈ Set.Ioc (0:ℝ) t := ⟨ht, le_rfl⟩
  set F := propagatorCoeff D μ j t φc with hF
  set Uf : ℝ → Coeff d → Coeff d := fun u ψ => frozenCoeff D ρβ (j - 2) ψ u with hUf
  set E : ℝ → Coeff d := fun σ => forwardGen D (μ (t - σ)) (F σ) - forwardGen D ρβ (F σ) with hE
  obtain ⟨hFsol, hFw, hFb⟩ := hspec D νm t μ hAt t htI φc hφ
  have hFmem : ∀ σ ∈ Set.Icc (0:ℝ) t, MemHs (j : ℝ) (F σ) := fun σ hσ => hFw.1 σ hσ
  have hFreal : ∀ σ ∈ Set.Icc (0:ℝ) t, IsRealCoeff (F σ) :=
    ClassicalPart.propagatorCoeff_real hd s hs0 hsd j hj1 R MB Λ VB D νm t μ hAt t htI φc hφ hre
  have hFbdd : ∃ M : ℝ, ∀ σ ∈ Set.Icc (0:ℝ) t, hsNorm (j : ℝ) (F σ) ≤ M := by
    refine ⟨Real.exp (|R.lambdaM Cspec νm (thetaOrder d s)| * t) * hsNorm (j : ℝ) φc, fun σ hσ => ?_⟩
    refine (hFb σ hσ).trans (mul_le_mul_of_nonneg_right ?_ (hsNorm_nonneg' _ _))
    apply Real.exp_le_exp.mpr
    calc R.lambdaM Cspec νm (thetaOrder d s) * σ ≤ |R.lambdaM Cspec νm (thetaOrder d s)| * σ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hσ.1
      _ ≤ _ := mul_le_mul_of_nonneg_left hσ.2 (abs_nonneg _)
  have hUφ : ∀ τ ∈ Set.Icc (0:ℝ) t, IsRealCoeff (Uf τ φc) ∧ MemHs (j : ℝ) (Uf τ φc) :=
    fun τ hτ => let h := frozen_lvl_data hd s j hj hHj hre hφ hτ.1; ⟨h.2.1, h.2.2⟩
  have hsmooth : ∀ ψ : Coeff d, IsRealCoeff ψ → MemHs ((j : ℝ) - aExp d s) ψ → ∀ u : ℝ, 0 < u →
      MemHs (j : ℝ) (centerCoeff ρβ (Uf u ψ)) ∧
      hsNorm (j : ℝ) (centerCoeff ρβ (Uf u ψ)) ≤
        Ks * (1 + u ^ (-(aExp d s / 2))) * Real.exp (-c₁ * u) *
          hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ ψ) := by
    intro ψ hre' hψ u hu
    obtain ⟨h1, h2⟩ := hsm β V ρβ hHj ψ hre' hψ u hu
    refine ⟨h1, h2.trans ?_⟩
    have hexp : Real.exp (-cs * u) ≤ Real.exp (-c₁ * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hrp : 0 ≤ u ^ (-(aExp d s / 2)) := Real.rpow_nonneg hu.le _
    have hpos : 0 ≤ Ks * (1 + u ^ (-(aExp d s / 2))) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hpos) (hsNorm_nonneg' _ _)
  have hdecay : ∀ τ ∈ Set.Icc (0:ℝ) t, hsNorm (j : ℝ) (centerCoeff ρβ (Uf τ φc)) ≤
      Kd * Real.exp (-c₁ * τ) * hsNorm (j : ℝ) (centerCoeff ρβ φc) := by
    intro τ hτ
    obtain ⟨-, h2⟩ := hdec β V ρβ hHj φc hre hφ τ hτ.1
    refine h2.trans ?_
    have hexp : Real.exp (-cd * τ) ≤ Real.exp (-c₁ * τ) :=
      Real.exp_le_exp.mpr (by nlinarith [hτ.1])
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hKd.le) (hsNorm_nonneg' _ _)
  have hpertE : ∀ σ ∈ Set.Icc (0:ℝ) t, IsRealCoeff (E σ) ∧ MemHs ((j : ℝ) - aExp d s) (E σ) ∧
      hsNorm ((j : ℝ) - aExp d s) (E σ) ≤
        P * Real.exp (-κ * (t - σ)) * hsNorm (j : ℝ) (centerCoeff ρβ (F σ)) := fun σ hσ =>
    hpert β V ρβ H μ t ht hAt hdecμ (F σ) (hFreal σ hσ) (hFmem σ hσ) (t - σ)
      ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hduh : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, F τ k = Uf τ φc k +
      ∫ σ in (0:ℝ)..τ, Uf (τ - σ) (E σ) k := fun τ hτ k =>
    duhamel_coeff hd s hs0 hsd j (by omega) R (frozenRegime d s c₀) MB Λ VB 1 Λ₀ Λ₀ D νm νm t μ ρβ hAt hAβ hν φc hφ htI k hτ
  have hcase_i : ∀ τ ∈ Set.Icc (0:ℝ) t, R₀ ≤ t - τ →
      hsNorm (j : ℝ) (centerCoeff ρβ (F τ)) ≤
        2 * Kd * hsNorm (j : ℝ) (centerCoeff ρβ φc) * Real.exp (-(c₁ / 2) * τ) ∧
      MemHs (j : ℝ) (centerCoeff ρβ (F τ) - centerCoeff ρβ (Uf τ φc)) ∧
      hsNorm (j : ℝ) (centerCoeff ρβ (F τ) - centerCoeff ρβ (Uf τ φc)) ≤
        (2 * (1 + Λ₀)) * (2 * (1 + Λ₀)) * Ks * P * B *
          (2 * Kd * hsNorm (j : ℝ) (centerCoeff ρβ φc)) *
          Real.exp (-κ * (t - τ)) * Real.exp (-(c₁ / 2) * τ) := by
    intro τ hτ hR
    exact case_i_abstract hprob hρc hΛ Uf F E φc j (aExp d s) Ks Kd c₁ P κ B (t - τ)
      (by linarith [ha.1]) ha.2.1 hja hKs.le hKd.le hP0 hκ.le hc₁.le hB hduh hFmem hFreal hUφ
      hsmooth hdecay hpertE hFbdd hτ le_rfl (hR₀ (t - τ) hR)
  set A : ℝ := hsNorm (j : ℝ) (centerCoeff ρβ φc) with hAdef
  have hA0 : 0 ≤ A := hsNorm_nonneg' _ _
  have hQFmem : MemHs (j : ℝ) (centerCoeff ρβ (F τ)) :=
    (centerCoeff_bound' hprob hρc hΛ hj0 (hFmem τ hτ)).1
  have hQUmem : MemHs (j : ℝ) (centerCoeff ρβ (Uf τ φc)) :=
    (centerCoeff_bound' hprob hρc hΛ hj0 (hUφ τ hτ).2).1
  have hQUn := hdecay τ hτ
  -- case (ii)
  have hw_ii : t - τ < R₀ → hsNorm (j : ℝ) (centerCoeff ρβ (F τ)) ≤
      X3 * Real.exp (-(c₁ / 2) * τ) * A := by
    intro hlt
    have hexp := Real.exp_pos (-(c₁ / 2) * τ)
    by_cases ht2 : t < R₀
    · obtain ⟨-, hn⟩ := hcen D νm t μ hAt htI hprob hρc hΛ hφ τ hτ
      have := exp_aux lam (c₁ / 2) R₀ τ 0 (by linarith) hτ.1 (by linarith [hτ.2])
      simp only [mul_zero, Real.exp_zero, mul_one, zero_add] at this
      calc hsNorm (j : ℝ) (centerCoeff ρβ (F τ))
          ≤ 2 * (1 + Λ₀) * Real.exp (lam * τ) * A := hn
        _ ≤ 2 * (1 + Λ₁) * (Real.exp (|lam| * R₀) * Real.exp ((c₁ / 2) * R₀) *
              Real.exp (-(c₁ / 2) * τ)) * A := by
            refine mul_le_mul_of_nonneg_right ?_ hA0
            calc 2 * (1 + Λ₀) * Real.exp (lam * τ) ≤ 2 * (1 + Λ₁) * Real.exp (lam * τ) :=
                  mul_le_mul_of_nonneg_right hΛ1 (Real.exp_pos _).le
              _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ X3 * Real.exp (-(c₁ / 2) * τ) * A := by
            rw [hX3]
            have h1 : 1 ≤ 1 + 2 * Kd := by linarith
            have h2 : 0 ≤ 2 * (1 + Λ₁) * (Real.exp (|lam| * R₀) * Real.exp ((c₁ / 2) * R₀) *
              Real.exp (-(c₁ / 2) * τ)) * A := by positivity
            calc 2 * (1 + Λ₁) * (Real.exp (|lam| * R₀) * Real.exp ((c₁ / 2) * R₀) *
                  Real.exp (-(c₁ / 2) * τ)) * A
                = (2 * (1 + Λ₁) * (Real.exp (|lam| * R₀) * Real.exp ((c₁ / 2) * R₀) *
                  Real.exp (-(c₁ / 2) * τ)) * A) * 1 := by ring
              _ ≤ (2 * (1 + Λ₁) * (Real.exp (|lam| * R₀) * Real.exp ((c₁ / 2) * R₀) *
                  Real.exp (-(c₁ / 2) * τ)) * A) * (1 + 2 * Kd) :=
                  mul_le_mul_of_nonneg_left h1 h2
              _ = _ := by ring
    · have hRt : R₀ ≤ t := not_lt.mp ht2
      set τ₀ : ℝ := t - R₀ with hτ₀
      have hτ₀0 : 0 ≤ τ₀ := by rw [hτ₀]; linarith
      have hτ₀mem : τ₀ ∈ Set.Icc (0:ℝ) t := ⟨hτ₀0, by rw [hτ₀]; linarith⟩
      obtain ⟨hb0, -, -⟩ := hcase_i τ₀ hτ₀mem (by rw [hτ₀]; linarith)
      set s' : ℝ := τ - τ₀ with hs'
      have hs'0 : 0 ≤ s' := by rw [hs']; rw [hτ₀]; linarith
      have hs'R : s' ≤ R₀ := by rw [hs']; rw [hτ₀]; linarith [hτ.2]
      obtain ⟨hψm, hshift⟩ := propagatorCoeff_shift hd hs0 hsd hj1 hAt htI hφ hτ₀0 hR₀pos
        (by rw [hτ₀]; ring)
      have e : F τ = propagatorCoeff D μ j R₀ (F τ₀) s' := by
        rw [hshift s' ⟨hs'0, hs'R⟩]
        congr 1
        rw [hs']; ring
      obtain ⟨-, hn2⟩ := hcen D νm R₀ μ (hA R₀ hR₀pos) ⟨hR₀pos, le_rfl⟩ hprob hρc hΛ hψm s'
        ⟨hs'0, hs'R⟩
      have hax := exp_aux lam (c₁ / 2) R₀ s' τ₀ (by linarith) hs'0 hs'R
      have hττ : τ₀ + s' = τ := by rw [hs']; ring
      rw [hττ] at hax
      rw [e]
      have hCQ0 : 0 ≤ 2 * (1 + Λ₀) := by positivity
      calc hsNorm (j : ℝ) (centerCoeff ρβ (propagatorCoeff D μ j R₀ (F τ₀) s'))
          ≤ 2 * (1 + Λ₀) * Real.exp (lam * s') * hsNorm (j : ℝ) (centerCoeff ρβ (F τ₀)) := hn2
        _ ≤ 2 * (1 + Λ₀) * Real.exp (lam * s') *
              (2 * Kd * A * Real.exp (-(c₁ / 2) * τ₀)) :=
            mul_le_mul_of_nonneg_left hb0 (by positivity)
        _ = 2 * (1 + Λ₀) * (Real.exp (lam * s') * Real.exp (-(c₁ / 2) * τ₀)) * (2 * Kd * A) := by ring
        _ ≤ 2 * (1 + Λ₁) * (Real.exp (|lam| * R₀) * Real.exp ((c₁ / 2) * R₀) *
              Real.exp (-(c₁ / 2) * τ)) * (2 * Kd * A) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            calc 2 * (1 + Λ₀) * (Real.exp (lam * s') * Real.exp (-(c₁ / 2) * τ₀))
                ≤ 2 * (1 + Λ₀) * (Real.exp (|lam| * R₀) * Real.exp ((c₁ / 2) * R₀) *
                    Real.exp (-(c₁ / 2) * τ)) := mul_le_mul_of_nonneg_left hax hCQ0
              _ ≤ _ := mul_le_mul_of_nonneg_right hΛ1 (by positivity)
        _ ≤ X3 * Real.exp (-(c₁ / 2) * τ) * A := by
            rw [hX3]
            have h2 : 0 ≤ 2 * (1 + Λ₁) * (Real.exp (|lam| * R₀) * Real.exp ((c₁ / 2) * R₀) *
              Real.exp (-(c₁ / 2) * τ)) * A := by positivity
            calc 2 * (1 + Λ₁) * (Real.exp (|lam| * R₀) * Real.exp ((c₁ / 2) * R₀) *
                  Real.exp (-(c₁ / 2) * τ)) * (2 * Kd * A)
                = (2 * (1 + Λ₁) * (Real.exp (|lam| * R₀) * Real.exp ((c₁ / 2) * R₀) *
                  Real.exp (-(c₁ / 2) * τ)) * A) * (2 * Kd) := by ring
              _ ≤ (2 * (1 + Λ₁) * (Real.exp (|lam| * R₀) * Real.exp ((c₁ / 2) * R₀) *
                  Real.exp (-(c₁ / 2) * τ)) * A) * (1 + 2 * Kd) :=
                  mul_le_mul_of_nonneg_left (by linarith) h2
              _ = _ := by ring
  -- the triangle inequality and the final assembly
  have htri : hsNorm (j : ℝ) (centerCoeff ρβ (F τ) - centerCoeff ρβ (Uf τ φc)) ≤
      hsNorm (j : ℝ) (centerCoeff ρβ (F τ)) + hsNorm (j : ℝ) (centerCoeff ρβ (Uf τ φc)) :=
    (hsNorm_sub_le' (j : ℝ) hQFmem hQUmem).2
  have hsubmem := (hsNorm_sub_le' (j : ℝ) hQFmem hQUmem).1
  have hmain := assemble_bounds (Kd := Kd) (Γ := Γ) (X3 := X3) (κ := κ) (R₀ := R₀) (c₁ := c₁)
    (A := A) (t := t) (τ := τ) (C := C) hKd.le hΓ0 hX30 hκ.le hR₀pos.le hA0 hC (hsNorm_nonneg' _ _)
    (hsNorm_nonneg' _ _) hc₁.le hτ.1
    (fun hR => by
      obtain ⟨b1, -, b3⟩ := hcase_i τ hτ hR
      refine ⟨b1, ?_⟩
      refine b3.trans (le_of_eq ?_)
      rw [hΓ])
    hw_ii hQUn htri
  exact ⟨hQFmem, hmain.1, hsubmem, hmain.2⟩



theorem sobolevNorm_zero_fun {m : ℝ} (hm : (d : ℝ) / 2 < m) :
    sobolevNorm m (fun _ : Torus d => (0 : ℝ)) = 0 := by
  have h0 : MemHs m (0 : Coeff d) := by
    refine summable_of_ne_finset_zero (s := ∅) fun k _ => ?_
    simp
  have hre : IsRealCoeff (0 : Coeff d) := fun k => by simp
  obtain ⟨-, -, -, -, h5⟩ := bridge_real hm h0 hre
  have e : toFun (0 : Coeff d) = fun _ : Torus d => (0 : ℝ) := by
    funext x; simp [toFun, series]
  rw [← e, h5]
  unfold hsNorm hsNormSq
  simp

theorem exists_adjoint_decay_abstract (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j) (νm νp c₀ Λ₀ : ℝ)
    (r : ℝ) (hr : (d : ℝ) / 2 + j + 1 < r) (R : Regime) (MB Λ VB : ℝ) (Cd κ : ℝ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ) (H : FrozenHyp d s (j + mStar d + 2) νm νp c₀ Λ₀ β V ρβ)
      (μ : ℝ → Torus d → ℝ),
      (∀ T, 0 < T → AdjointData s j R MB Λ VB (mfData d s H.hs0 H.hsd V β H.hβ) νm T μ) →
      (∀ σ, 0 ≤ σ → MemHs r (coeffOf (μ σ) - coeffOf ρβ) ∧ hsNorm r (coeffOf (μ σ) - coeffOf ρβ) ≤ Cd * Real.exp (-κ * σ)) →
      ∀ φ : Torus d → ℝ, Continuous φ → MemSobolev j φ → ∀ r' t : ℝ, 0 ≤ r' → r' ≤ t →
        MemSobolev j (projMean (withDensityReal ρβ) (propagator (mfData d s H.hs0 H.hsd V β H.hβ) μ r' t φ)) ∧
        sobolevNorm j (projMean (withDensityReal ρβ) (propagator (mfData d s H.hs0 H.hsd V β H.hβ) μ r' t φ)) ≤
          C * Real.exp (-c * (t - r')) * sobolevNorm j (projMean (withDensityReal ρβ) φ) ∧
        sobolevNorm j (fun x => projMean (withDensityReal ρβ) (propagator (mfData d s H.hs0 H.hsd V β H.hβ) μ r' t φ) x -
          equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (t - r') (projMean (withDensityReal ρβ) φ) x) ≤
          C * Real.exp (-c * (t - r')) * Real.exp (-κ * r') * sobolevNorm j (projMean (withDensityReal ρβ) φ) := by
  by_cases hsc : 0 ≤ s ∧ s < d
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun β V ρβ H => (hsc ⟨H.hs0, H.hsd⟩).elim⟩
  obtain ⟨hs0, hsd⟩ := hsc
  obtain ⟨C₁, c, hC₁, hc, hmain⟩ := main_coeff hd s j hj νm νp c₀ Λ₀ r hr R MB Λ VB Cd κ hκ
  obtain ⟨Cs, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd j (by
    have := mStar_add_two_le_of_gt hj
    have := ClassicalPart.three_le_mStar d
    omega) R MB Λ VB
  refine ⟨max C₁ 1, c, lt_max_of_lt_left hC₁, hc, ?_⟩
  intro β V ρβ H μ hA hdec φ hφc hφ r' t hr' hrt
  have hjm := mStar_add_two_le_of_gt hj
  have h3 := ClassicalPart.three_le_mStar d
  have hj1 : 1 ≤ j := by omega
  have hdj : (d : ℝ) / 2 < j := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have H3 : FrozenHyp d s (j + 3) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  have hcφ : MemHs (j : ℝ) (coeffOf φ) := (hsNormSq_coeffOf _ φ hφ).1
  have hreφ : IsRealCoeff (coeffOf φ) := isRealCoeff_coeffOf φ (integrable_of_cont hφc)
  have hsumφ : Summable fun k => ‖coeffOf φ k‖ := summable_norm_of_memHs _ hdj _ hcφ
  have hP := proj_data j hjm H3 hφc hφ
  have hP' := hP.2 j (by positivity) le_rfl
  have hψ'c : Continuous (projMean (withDensityReal ρβ) φ) := by
    rw [hP.1]; exact continuous_toFun _ (summable_center hsumφ)
  have hmaxC : C₁ ≤ max C₁ 1 := le_max_left _ _
  have hSnn : ∀ (m : ℝ) (g : Torus d → ℝ), 0 ≤ sobolevNorm m g := fun m g => Real.sqrt_nonneg _
  have hsob0 : 0 ≤ sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) φ) := hSnn _ _
  rcases (hr'.trans hrt).eq_or_lt with ht0 | htpos
  · -- the degenerate case `t = 0`
    have ht0' : t = 0 := ht0.symm
    subst ht0'
    have hr0 : r' = 0 := le_antisymm hrt hr'
    subst hr0
    have hA1 := hA 1 one_pos
    have hKf := ClassicalAux.convKernelFacts hd D
    have hV1 : Torus.IsCk 1 D.V := ET.isCk_mono' (a := 1) (b := j + mStar d + 2) (by omega) H.hV
    have hμ1 : Torus.IsCk 1 (μ 0) :=
      ET.isCk_mono' (a := 1) (b := j + 3) (by omega) (hA1.hμ.smooth 0 ⟨le_rfl, zero_le_one⟩)
    have hjR : (mStar d : ℝ) + 2 ≤ j := by exact_mod_cast hjm
    have hφ2 : Torus.IsCk 2 φ := isCk_two_of_memSobolev hφc (memSobolev_mono_idx hφ hjR)
    have hψ'2 : Torus.IsCk 2 (projMean (withDensityReal ρβ) φ) :=
      isCk_two_of_memSobolev hψ'c (memSobolev_mono_idx hP'.1 hjR)
    have hρ1 : Torus.IsCk 1 ρβ := ET.isCk_mono' (a := 1) (b := j + mStar d + 2) (by omega) H.hρC
    have hprop0 : propagator D μ 0 0 φ = φ := MFSemigroup.propagator_zero D hKf hV1 μ hμ1 hφ2
    have hS0 : equilibriumSemigroup D ρβ (0 - 0) (projMean (withDensityReal ρβ) φ) =
        projMean (withDensityReal ρβ) φ := by
      rw [sub_self]
      unfold equilibriumSemigroup
      rw [MFSemigroup.propagator_zero D hKf hV1 (fun _ => ρβ) hρ1 hψ'2]
      have := MFSemigroup.isProb_withDensityReal hprob
      funext x
      have hpp := MFSemigroup.pair_projMean (withDensityReal ρβ) φ
      show projMean (withDensityReal ρβ) φ x -
        pair (withDensityReal ρβ) (projMean (withDensityReal ρβ) φ) = _
      rw [hpp, sub_zero]
    refine ⟨?_, ?_, ?_⟩
    · rw [hprop0]; exact hP'.1
    · rw [hprop0, hP'.2]
      simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
      have := le_max_right C₁ 1
      rw [← hP'.2]
      nlinarith [hSnn (j : ℝ) (projMean (withDensityReal ρβ) φ)]
    · have e : (fun x => projMean (withDensityReal ρβ) (propagator D μ 0 0 φ) x -
          equilibriumSemigroup D ρβ (0 - 0) (projMean (withDensityReal ρβ) φ) x) =
          fun _ : Torus d => (0 : ℝ) := by
        rw [hprop0, hS0]; funext x; simp
      rw [e, sobolevNorm_zero_fun hdj]
      have : 0 ≤ max C₁ 1 * Real.exp (-c * (0 - 0)) * Real.exp (-κ * 0) *
          sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) φ) := by positivity
      exact this
  · -- the main case `t > 0`
    set τ : ℝ := t - r' with hτdef
    have hτ : τ ∈ Set.Icc (0:ℝ) t := ⟨by rw [hτdef]; linarith, by rw [hτdef]; linarith⟩
    obtain ⟨m1, m2, m3, m4⟩ := hmain β V ρβ H μ hA hdec (coeffOf φ) hreφ hcφ t htpos τ hτ
    have hAt := hA t htpos
    have htI : t ∈ Set.Ioc (0:ℝ) t := ⟨htpos, le_rfl⟩
    have hprop := ClassicalPart.propagator_eq_toFun hd s hs0 hsd j (by omega) R MB Λ VB D νm t μ hAt t htI
      φ hφc hφ r' ⟨hr', hrt⟩
    obtain ⟨-, hFw, -⟩ := hspec D νm t μ hAt t htI (coeffOf φ) hcφ
    have hFmem : MemHs (j : ℝ) (propagatorCoeff D μ j t (coeffOf φ) τ) := hFw.1 τ hτ
    have hFreal : IsRealCoeff (propagatorCoeff D μ j t (coeffOf φ) τ) :=
      ClassicalPart.propagatorCoeff_real hd s hs0 hsd j hj1 R MB Λ VB D νm t μ hAt t htI (coeffOf φ)
        hcφ hreφ τ hτ
    have hFsum := summable_norm_of_memHs _ hdj _ hFmem
    obtain ⟨hpm1, hpm2, hpm3⟩ := projMean_toFun hprob hρc hFsum hFmem hFreal
    have hprop' : propagator D μ r' t φ = toFun (propagatorCoeff D μ j t (coeffOf φ) τ) := by
      rw [hprop]
    -- the frozen side
    have hAβ := adjointData_frozen_level j H3 0 (τ + 1) (by linarith [hτ.1])
    have hτ0 : 0 ≤ τ := hτ.1
    have hψ'mem : MemSobolev (j : ℝ) (projMean (withDensityReal ρβ) φ) := hP'.1
    have hcoψ' : coeffOf (projMean (withDensityReal ρβ) φ) = centerCoeff ρβ (coeffOf φ) := by
      rw [hP.1]; exact coeffOf_toFun _ (centerCoeff_isReal hreφ) (summable_center hsumφ)
    have hSeq := (S_eq hd j hjm H3 hψ'c hψ'mem hτ0).1
    rw [hcoψ'] at hSeq
    have hcfc := center_frozen_center hd hs0 hsd hj1 hAβ hprob hρc hcφ (τ := τ) ⟨hτ0, by linarith⟩
    have hlevel := (frozen_lvl_data hd s j hj (H.mono (by omega)) hreφ hcφ hτ0).1
    have hSτ : equilibriumSemigroup D ρβ τ (projMean (withDensityReal ρβ) φ) =
        toFun (centerCoeff ρβ (frozenCoeff D ρβ (j - 2) (coeffOf φ) τ)) := by
      rw [hSeq, ← hcfc, hlevel]
    -- data of the two centered coefficient families
    obtain ⟨hUreal, hUmem⟩ := (frozen_lvl_data hd s j hj (H.mono (by omega)) hreφ hcφ hτ0).2
    have hQFreal := centerCoeff_isReal (ρ := ρβ) hFreal
    have hQUreal := centerCoeff_isReal (ρ := ρβ) hUreal
    have hQFmem := (centerCoeff_bound' hprob hρc hΛ (i := (j : ℝ)) (by positivity) hFmem).1
    have hQUmem := (centerCoeff_bound' hprob hρc hΛ (i := (j : ℝ)) (by positivity) hUmem).1
    have hQFsum := summable_center (ρ := ρβ) hFsum
    have hUsum := summable_norm_of_memHs _ hdj _ hUmem
    have hQUsum := summable_center (ρ := ρβ) hUsum
    have hΔreal := isRealCoeff_sub' hQFreal hQUreal
    have hΔsum : Summable fun k => ‖(centerCoeff ρβ (propagatorCoeff D μ j t (coeffOf φ) τ) -
        centerCoeff ρβ (frozenCoeff D ρβ (j - 2) (coeffOf φ) τ)) k‖ := by
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_sub_le _ _)
        (hQFsum.add hQUsum)
    have hfun : (fun x => projMean (withDensityReal ρβ) (propagator D μ r' t φ) x -
        equilibriumSemigroup D ρβ (t - r') (projMean (withDensityReal ρβ) φ) x) =
        toFun (centerCoeff ρβ (propagatorCoeff D μ j t (coeffOf φ) τ) -
          centerCoeff ρβ (frozenCoeff D ρβ (j - 2) (coeffOf φ) τ)) := by
      funext x
      rw [hprop', hpm1, show t - r' = τ from rfl, hSτ]
      exact (MFApriori.Aux.toFun_sub _ _ hQFsum hQUsum x).symm
    have hbr := (ClassicalPart.memSobolev_toFun hΔsum m3 hΔreal).2
    have htτ : t - τ = r' := by rw [hτdef]; ring
    have hA0 : 0 ≤ hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf φ)) := hsNorm_nonneg' _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [hprop', hpm1]; exact hpm2
    · rw [hprop', hpm1, hpm3, hP'.2]
      refine m2.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.exp_pos _).le) hA0
    · rw [hfun, hbr, hP'.2]
      refine m4.trans ?_
      rw [htτ]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le) (Real.exp_pos _).le) hA0

end Decay

end HRS.PDE.MFAdjoint
