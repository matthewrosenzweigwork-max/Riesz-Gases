import HRS.MS.GoFeatAux3
import HRS.MP.RdGenerator

/-!
# S5.5 features: the uniformly local norm of `𝓛_t φ_α` (infrastructure)

`s55f_gen_ul`: for `b.Valid` there is `Cg` such that for every `S : WholeSetup b`, `N`, `t ∈ [0,T]` and Hermite
index `α`, the function `𝓛_t φ_α` (`generatorW (S.coeff N) t (oscTestFun b.m α)`, `φ_α = λ_α^{-m/2} h_α`) is `C^R` with
`R = b.k + 1 + 1 + ⌈d/2⌉` (the order demanded by `UlAdjointInput` at `j = b.k + 1`) and
`‖𝓛_t φ_α‖_{H^R_ul} ≤ Cg λ_α^{(J-m)/2}`, `J = b.J`.

The proof is for every `0 ≤ s < d` at once (cancellation convention of `convGradConvW`; no split at `d - 2`): the
pieces of the generator are the weighted derivative classes `RgW` of `HRS/MP/RdGenCalc.lean`/`RdGenerator.lean`
(`νΔφ`, the nonlocal part of the drift times `∇φ`, `∇V·∇φ` and the nonlocal term `𝒢_ρ φ`), but with *bounded* (weight
`1`) output: for the linearly growing `∇V·∇φ` the extra factor `1 + |x|` is absorbed by the decay of `∇φ_α`
(`decayNormE 1`).  The `H^R_ul` norm is then bounded by the sup bounds of the derivatives (`s55_ul_of_sup`).

Helper names carry the prefix `s55f_`; namespace `HRS.MS.Go`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.Go
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MP.RdGen HRS.MH.DualityRd

variable {d : ℕ}

/-! ### Elementary weight facts -/

lemma s55f_norm_le_jb (x : Euc d) : ‖x‖ ≤ jbracket x := by
  unfold jbracket
  calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
    _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)

lemma s55f_one_add_le (x : Euc d) : 1 + ‖x‖ ≤ 2 * jbracket x := by
  have := s55f_norm_le_jb x
  have := HRS.MS.Adj.ad1_one_le_jb x
  linarith

/-- The weighted decay norm (`b = 1`) gives plain and `(1+|x|)`-weighted bounds on the derivative norms. -/
lemma s55f_decay_to_norm {k : ℕ} {Λ : ℝ} {f : Euc d → ℝ} (hf : ContDiff ℝ k f)
    (h : decayNormE k 1 f ≤ ENNReal.ofReal Λ) :
    ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ (d : ℝ) ^ n * max Λ 0 ∧
      ‖iteratedFDeriv ℝ n f x‖ * (1 + ‖x‖) ≤ 2 * ((d : ℝ) ^ n * max Λ 0) := by
  intro n hn x
  have hΛ0 : 0 ≤ max Λ 0 := le_max_right _ _
  have hp : ∀ idx : Fin n → Fin d, |partialDeriv idx f x| ≤ max Λ 0 ∧
      (1 + ‖x‖) * |partialDeriv idx f x| ≤ 2 * max Λ 0 := by
    intro idx
    have h1 := s55_dse_bound (w := fun j => 1 + (j : ℝ)) h (j := n) hn idx x
    have hj1 := HRS.MS.Adj.ad1_one_le_jb x
    have he : (1 : ℝ) ≤ 1 + (n : ℝ) := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have h2 : jbracket x ^ (1 : ℝ) ≤ jbracket x ^ (1 + (n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hj1 he
    rw [Real.rpow_one] at h2
    have h3 : jbracket x * |partialDeriv idx f x| ≤ max Λ 0 :=
      (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)).trans h1
    refine ⟨?_, ?_⟩
    · nlinarith [abs_nonneg (partialDeriv idx f x)]
    · have := s55f_one_add_le x
      calc (1 + ‖x‖) * |partialDeriv idx f x| ≤ (2 * jbracket x) * |partialDeriv idx f x| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = 2 * (jbracket x * |partialDeriv idx f x|) := by ring
        _ ≤ 2 * max Λ 0 := by linarith
  have hnorm := HRS.MP.RdInit.mri_norm_iter_le n f x
  have hs1 : ∑ idx : Fin n → Fin d, |partialDeriv idx f x| ≤ (d : ℝ) ^ n * max Λ 0 :=
    s55_card_sum_le n _ fun idx => (hp idx).1
  refine ⟨hnorm.trans hs1, ?_⟩
  have hs2 : ∑ idx : Fin n → Fin d, (1 + ‖x‖) * |partialDeriv idx f x| ≤
      (d : ℝ) ^ n * (2 * max Λ 0) :=
    s55_card_sum_le n _ fun idx => (hp idx).2
  calc ‖iteratedFDeriv ℝ n f x‖ * (1 + ‖x‖) ≤ (∑ idx : Fin n → Fin d, |partialDeriv idx f x|) * (1 + ‖x‖) :=
        mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ = ∑ idx : Fin n → Fin d, (1 + ‖x‖) * |partialDeriv idx f x| := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ ≤ (d : ℝ) ^ n * (2 * max Λ 0) := hs2
    _ = 2 * ((d : ℝ) ^ n * max Λ 0) := by ring

/-- Product of a linearly growing class with a function whose derivatives decay like `(1+|x|)⁻¹`. -/
lemma s55f_mul_lin {R : ℕ} {c c' : ℝ} {u v : Euc d → ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hu : RgW (fun x => 1 + ‖x‖) R c u) (hv : ContDiff ℝ R v)
    (hv' : ∀ n ≤ R, ∀ x, ‖iteratedFDeriv ℝ n v x‖ * (1 + ‖x‖) ≤ c') :
    RgW (fun _ => 1) R (2 ^ R * c * c') (fun x => u x * v x) := by
  refine ⟨hu.1.mul hv, fun n hn x => ?_⟩
  have hn' : (n : WithTop ℕ∞) ≤ R := by exact_mod_cast hn
  refine (norm_iteratedFDeriv_mul_le hu.1 hv x hn').trans ?_
  have hx : 0 < 1 + ‖x‖ := by positivity
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (c * c') := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have h1 := hu.2 i (by omega) x
        have h2 := hv' (n - i) (by omega) x
        have h2' : ‖iteratedFDeriv ℝ (n - i) v x‖ ≤ c' / (1 + ‖x‖) := by
          rw [le_div_iff₀ hx]; exact h2
        have hch : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
        have h3 : ‖iteratedFDeriv ℝ i u x‖ * ‖iteratedFDeriv ℝ (n - i) v x‖ ≤ c * c' := by
          calc _ ≤ (c * (1 + ‖x‖)) * (c' / (1 + ‖x‖)) :=
                mul_le_mul h1 h2' (norm_nonneg _) (by positivity)
            _ = c * c' := by field_simp
        calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i u x‖ * ‖iteratedFDeriv ℝ (n - i) v x‖
            = (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i u x‖ * ‖iteratedFDeriv ℝ (n - i) v x‖) := by ring
          _ ≤ (n.choose i : ℝ) * (c * c') := mul_le_mul_of_nonneg_left h3 hch
    _ = (2 ^ n : ℝ) * (c * c') := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
    _ ≤ 2 ^ R * c * c' * 1 := by
        have h2 : (2 : ℝ) ^ n ≤ 2 ^ R := pow_le_pow_right₀ (by norm_num) hn
        have : 0 ≤ c * c' := mul_nonneg hc hc'
        calc (2 ^ n : ℝ) * (c * c') ≤ 2 ^ R * (c * c') := mul_le_mul_of_nonneg_right h2 this
          _ = 2 ^ R * c * c' * 1 := by ring

/-! ### The bounded generator class -/

/-- The conv-component constant. -/
def s55fCC (d : ℕ) (s Aρ : ℝ) : ℝ :=
  movtr_sigma s * (Aρ * rgNear d s + 4 ^ (s + 1) * Aρ * rgW d)

lemma s55fCC_nonneg {s Aρ : ℝ} (hs0 : 0 ≤ s) (hAρ : 0 ≤ Aρ) : 0 ≤ s55fCC d s Aρ := by
  have := rg_sigma_nonneg hs0
  have := rg_near_nonneg (d := d) s
  have := rg_W_nonneg (d := d)
  unfold s55fCC
  positivity

/-- The coefficient of `B` (the sup of the derivatives of `φ`). -/
def s55fKB (d : ℕ) (s : ℝ) (R : ℕ) (MB νbar Aρ : ℝ) : ℝ :=
  νbar * d + d * (2 ^ R * (d * MB * s55fCC d s Aρ)) +
    d * (movtr_sigma s * ((2 ^ (R + 2) * Aρ * (d * MB)) * rgNear d s +
      4 ^ (s + 1) * (2 ^ (R + 2) * Aρ * (d * MB)) * rgW d))

/-- The coefficient of `B1` (the sup of the `(1+|x|)`-weighted derivatives of `φ`). -/
def s55fK1 (d : ℕ) (R : ℕ) (ΛV G₀ : ℝ) : ℝ := d * (2 ^ R * (G₀ + ΛV))

lemma s55fKB_nonneg {s : ℝ} (hs0 : 0 ≤ s) {R : ℕ} {MB νbar Aρ : ℝ} (hMB : 0 ≤ MB) (hν : 0 ≤ νbar)
    (hAρ : 0 ≤ Aρ) : 0 ≤ s55fKB d s R MB νbar Aρ := by
  have := rg_sigma_nonneg hs0
  have := rg_near_nonneg (d := d) s
  have := rg_W_nonneg (d := d)
  have := s55fCC_nonneg (d := d) hs0 hAρ
  unfold s55fKB
  positivity

lemma s55fK1_nonneg {R : ℕ} {ΛV G₀ : ℝ} (hΛ : 0 ≤ ΛV) (hG : 0 ≤ G₀) : 0 ≤ s55fK1 d R ΛV G₀ := by
  unfold s55fK1; positivity

/-- **Bounded generator estimate**: `𝓛_τ φ` is `C^R` with `‖D^n 𝓛_τ φ‖ ≤ K_B B + K_1 B_1` (`n ≤ R`), where `B`
bounds the derivatives of `φ` up to order `R + 3` and `B_1` the `(1+|x|)`-weighted derivatives up to order `R + 1`. -/
lemma s55f_gen_core (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {R : ℕ} (hR : 1 ≤ R)
    {MB ΛV G₀ νbar Aρ B B1 : ℝ} (hMB0 : 0 ≤ MB) (hΛV : 0 ≤ ΛV) (hG : 0 ≤ G₀) (hAρ : 0 ≤ Aρ)
    (hB : 0 ≤ B) (hB1 : 0 ≤ B1)
    {D : WholeDyn d} (hDs : D.s = s) (hMB : HRS.PDE.MatBound MB D.M)
    (hV : VHypRd (R + 1) ΛV G₀ D.V) (hν0 : 0 ≤ D.invβ) (hν : D.invβ ≤ νbar)
    {ρ : ℝ → Euc d → ℝ} {τ : ℝ} (hρ : RgDecay (R + 2) (fun _ => Aρ) (ρ τ))
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ ((R + 2 + 1 : ℕ) : WithTop ℕ∞) φ)
    (hBφ : ∀ n, n ≤ R + 2 + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ B)
    (hB1φ : ∀ n, n ≤ R + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ * (1 + ‖x‖) ≤ B1) :
    RgW (fun _ => 1) R (s55fKB d s R MB νbar Aρ * B + s55fK1 d R ΛV G₀ * B1)
      (generatorW (D.coeff ρ) τ φ) := by
  subst hDs
  have hφ2 : ContDiff ℝ ((R + 2 : ℕ) : WithTop ℕ∞) φ := hφ.of_le (by exact_mod_cast Nat.le_succ _)
  have hφ1 : ContDiff ℝ ((R + 1 : ℕ) : WithTop ℕ∞) φ :=
    hφ.of_le (by exact_mod_cast (by omega : R + 1 ≤ R + 2 + 1))
  have hcc0 := s55fCC_nonneg (d := d) hs0 hAρ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- g1 : ν Δ φ
  have hLap := rg_laplacian (k := R) hφ2 (fun n hn x => hBφ n (by omega) x)
  have hg1 : RgW (fun _ => (1 : ℝ)) R (|D.invβ| * (d * B)) (fun x => D.invβ * Laplacian.laplacian φ x) :=
    hLap.const_mul _
  -- the nonlocal drift
  have hcomp : ∀ i : Fin d, RgW (fun _ => (1 : ℝ)) R (s55fCC d D.s Aρ)
      (fun x => (convGradConvW (rieszKernelGrad d D.s) (ρ τ) x) i) := fun i =>
    rg_conv_comp hd hs0 hsd hAρ hρ i
  have hdriftA : ∀ j : Fin d, RgW (fun _ => (1 : ℝ)) R (d * MB * s55fCC d D.s Aρ)
      (fun x => ∑ i : Fin d, D.M j i * (convGradConvW (rieszKernelGrad d D.s) (ρ τ) x) i) := by
    intro j
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        RgW (fun _ => (1 : ℝ)) R (|D.M j i| * s55fCC d D.s Aρ)
          (fun x => D.M j i * (convGradConvW (rieszKernelGrad d D.s) (ρ τ) x) i) :=
      fun i _ => RgW.const_mul _ (hcomp i)
    have hs := RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := R) Finset.univ hterm
    refine hs.mono (fun _ => zero_le_one) ?_
    calc ∑ i : Fin d, |D.M j i| * s55fCC d D.s Aρ ≤ ∑ i : Fin d, MB * s55fCC d D.s Aρ :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hMB j i) hcc0
      _ = d * MB * s55fCC d D.s Aρ := by simp [Finset.sum_const]; ring
  have hgrad : ∀ j : Fin d, RgW (fun _ => (1 : ℝ)) R B (fun x => gradient φ x j) := fun j =>
    rg_grad_comp hφ1 (fun n hn x => hBφ n (by omega) x) j
  have hcA : 0 ≤ (d : ℝ) * MB * s55fCC d D.s Aρ := by positivity
  have hg2j : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      RgW (fun _ => (1 : ℝ)) R (2 ^ R * (d * MB * s55fCC d D.s Aρ) * B)
        (fun x => (∑ i : Fin d, D.M j i * (convGradConvW (rieszKernelGrad d D.s) (ρ τ) x) i) *
          gradient φ x j) :=
    fun j _ => RgW.mul (fun _ => zero_le_one) hcA hB (hdriftA j) (hgrad j)
  have hg2 := RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := R) Finset.univ hg2j
  -- the confining term
  have hgV : ∀ j : Fin d, RgW (fun x => 1 + ‖x‖) R (G₀ + ΛV) (fun x => gradient D.V x j) :=
    fun j => rg_gradV hR hV j
  have hg3j : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      RgW (fun _ => (1 : ℝ)) R (2 ^ R * (G₀ + ΛV) * B1)
        (fun x => gradient D.V x j * gradient φ x j) := by
    intro j _
    refine s55f_mul_lin (by positivity) hB1 (hgV j) (hgrad j).1 ?_
    intro n hn x
    have e : (fun x => gradient φ x j) = fun x => fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ)) := by
      funext y; exact movtr_gradient_apply φ y j
    rw [e]
    have h1 := rg_diruv (n := n) (φ := φ) (hφ.of_le (by exact_mod_cast (by omega : n + 1 ≤ R + 2 + 1)))
      (EuclideanSpace.single j 1) x
    rw [rg_norm_single, one_mul] at h1
    exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans (hB1φ (n + 1) (by omega) x)
  have hg3 := RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := R) Finset.univ hg3j
  -- the nonlocal term
  have hBg : 0 ≤ (d : ℝ) * MB * B := by positivity
  have hg4 := rg_T3 hd hs0 hsd (k := R) hAρ hBg hρ
    (g := fun j y => Torus.matVec D.M.transpose (gradient φ y) j)
    (fun j => rg_matgrad hMB hφ hBφ j)
  have hfun : generatorW (D.coeff ρ) τ φ = fun x =>
      (D.invβ * Laplacian.laplacian φ x +
        ((∑ j : Fin d, (∑ i : Fin d, D.M j i * (convGradConvW (rieszKernelGrad d D.s) (ρ τ) x) i) *
            gradient φ x j) -
          ∑ j : Fin d, gradient D.V x j * gradient φ x j)) -
        ∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
          (fun y => ρ τ y * (Torus.matVec D.M.transpose (gradient φ y)) j) x) j := by
    funext x
    rw [generatorW_coeff]
    unfold nlTermRd
    have e1 : inner ℝ (meanFieldDriftW D (ρ τ) x) (gradient φ x) =
        (∑ j : Fin d, (∑ i : Fin d, D.M j i * (convGradConvW (rieszKernelGrad d D.s) (ρ τ) x) i) *
            gradient φ x j) -
          ∑ j : Fin d, gradient D.V x j * gradient φ x j := by
      rw [HRS.Whole.Q09B.q09b_inner_euc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold meanFieldDriftW
      rw [PiLp.sub_apply, HRS.Whole.Q09B.q09b_matVec_apply]
      ring
    rw [e1]
  rw [hfun]
  have hmain := (hg1.add (hg2.sub hg3)).sub hg4
  refine hmain.mono (fun _ => zero_le_one) ?_
  have h1 : |D.invβ| * (d * B) ≤ νbar * (d * B) := by
    rw [abs_of_nonneg hν0]
    exact mul_le_mul_of_nonneg_right hν (by positivity)
  unfold s55fKB s55fK1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith [h1]

lemma s55f_partial_le_norm {j : ℕ} (idx : Fin j → Fin d) (f : Euc d → ℝ) (x : Euc d) :
    |partialDeriv idx f x| ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  have := (iteratedFDeriv ℝ j f x).le_opNorm (fun l => (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d))
  simp only [rg_norm_single, Finset.prod_const_one, mul_one] at this
  unfold partialDeriv
  rwa [← Real.norm_eq_abs]

lemma s55f_ceil_half_le (d : ℕ) : ⌈(d : ℝ) / 2⌉₊ ≤ d := by
  rw [Nat.ceil_le]
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

/-- **`‖𝓛_t φ_α‖_{H^R_ul} ≤ Cg λ_α^{(J-m)/2}`** (`R = b.k + 1 + 1 + ⌈d/2⌉`), uniformly in `S, N, t ∈ [0,T], α`. -/
theorem s55f_gen_ul (b : WholeBounds d) (hb : b.Valid) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (S : WholeSetup b) (N : ℕ), ∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ α : MultiIndex d,
      ContDiff ℝ ((b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞)
        (generatorW (S.coeff N) t (oscTestFun b.m α)) ∧
      ulNormE (b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) b.θ (generatorW (S.coeff N) t (oscTestFun b.m α)) ≤
        ENNReal.ofReal (Cg * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2)) := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hceil := s55f_ceil_half_le d
  set R : ℕ := b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ with hRdef
  have hR1 : 1 ≤ R := by omega
  have hJ : b.J = 4 * b.k + 4 * d + 40 := rfl
  obtain ⟨ΛV, G₀, hV⟩ := s55f_vhyp_quadV hb.hQ b.c (R + 1)
  have hΛV : 0 ≤ ΛV := (norm_nonneg _).trans (hV.2.1 2 le_rfl (by omega) 0)
  have hG : 0 ≤ G₀ := (norm_nonneg _).trans hV.2.2
  have hMB0 : 0 ≤ ∑ i, ∑ j, |b.M i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hceil2 : ⌈(1 + (((R + 3 : ℕ) : ℝ))) / 2⌉₊ ≤ R + 3 := by
    rw [Nat.ceil_le]; push_cast
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  obtain ⟨C0, hC0, hosc⟩ := s55_osc_bounds hb.hθ b.m R (R + 3) 1 (by norm_num) b.J (by omega)
    (by omega)
  obtain ⟨Cu, hCu0, hCu⟩ := s55_ul_of_sup hb.hθ R
  have hdL : (d : ℝ) + 3 ≤ b.L := by
    have := hb.hL; have := hb.hs0; have : (0 : ℝ) ≤ b.k := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  set Λρ : ℝ := (∑ j ∈ Finset.range (R + 2 + 1), (d : ℝ) ^ j + 1) * max b.Λ 0 with hΛρ
  have hΛρ0 : 0 ≤ Λρ := by
    have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (R + 2 + 1), (d : ℝ) ^ j := Finset.sum_nonneg fun _ _ => by positivity
    positivity
  set Aρ : ℝ := (d : ℝ) ^ (R + 2) * Λρ * 2 ^ ((d : ℝ) + 3) with hAρ
  have hAρ0 : 0 ≤ Aρ := by positivity
  set MB : ℝ := ∑ i, ∑ j, |b.M i j| with hMB
  set KB : ℝ := s55fKB d b.s R MB b.νstar Aρ with hKB
  set K1 : ℝ := s55fK1 d R ΛV G₀ with hK1
  have hKB0 : 0 ≤ KB := s55fKB_nonneg hb.hs0 hMB0 hb.hν hAρ0
  have hK10 : 0 ≤ K1 := s55fK1_nonneg hΛV hG
  refine ⟨Cu * (KB * (d : ℝ) ^ (R + 3) + K1 * (2 * (d : ℝ) ^ (R + 3))) * C0, by positivity, ?_⟩
  intro S N t ht α
  obtain ⟨hsm, -, hdec⟩ := hosc α
  set e : ℝ := (((b.J : ℝ) - b.m) / 2) with he
  set Λφ : ℝ := C0 * oscEigenvalue d α ^ e with hΛφ
  have hΛφ0 : 0 ≤ Λφ := mul_nonneg hC0 (Real.rpow_nonneg (oscEigenvalue_pos α).le _)
  have hφR : ContDiff ℝ ((R + 3 : ℕ) : WithTop ℕ∞) (oscTestFun b.m α) :=
    s55_cd_of_inf (R + 3) hsm
  have hnorm := s55f_decay_to_norm hφR hdec
  rw [max_eq_left hΛφ0] at hnorm
  set B : ℝ := (d : ℝ) ^ (R + 3) * Λφ with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hpow : ∀ n ≤ R + 3, (d : ℝ) ^ n ≤ (d : ℝ) ^ (R + 3) := fun n hn =>
    pow_le_pow_right₀ hd1' hn
  have hBφ : ∀ n, n ≤ R + 2 + 1 → ∀ x, ‖iteratedFDeriv ℝ n (oscTestFun b.m α) x‖ ≤ B := by
    intro n hn x
    exact ((hnorm n (by omega) x).1).trans (mul_le_mul_of_nonneg_right (hpow n (by omega)) hΛφ0)
  have hB1φ : ∀ n, n ≤ R + 1 → ∀ x, ‖iteratedFDeriv ℝ n (oscTestFun b.m α) x‖ * (1 + ‖x‖) ≤ 2 * B := by
    intro n hn x
    exact ((hnorm n (by omega) x).2).trans (by
      have := mul_le_mul_of_nonneg_right (hpow n (by omega)) hΛφ0
      linarith)
  -- the density
  have hslice := s55f_regular_slice (n := b.k + 6 + ⌈(d : ℝ) / 2⌉₊) (R + 2) (by omega) hdL
    (S.dens N t ht).1 (S.dens N t ht).2
  have hρdec : RgDecay (R + 2) (fun _ => Aρ) (S.ρ N t) := by
    have hcb0 : 0 ≤ HRS.cbNorm (R + 2) (S.ρ N t) := u4_cbNorm_nonneg _ _
    exact HRS.MP.RdGen.rg_rho_decay hd1 (r := R + 2) (Λ := Λρ) hslice.1 hslice.2.1
      (by linarith [hslice.2.2])
  have hcore := s55f_gen_core hd1 hb.hs0 hb.hsd hR1 hMB0 hΛV hG hAρ0 hB0 (by positivity : (0 : ℝ) ≤ 2 * B)
    (D := S.dyn N) rfl (s55f_matBound b.M) hV (S.hinvβ N).1 (S.hinvβ N).2 hρdec
    (s55_cd_of_inf (R + 2 + 1) hsm) hBφ hB1φ
  have hcore' : RgW (fun _ => (1 : ℝ)) R (KB * B + K1 * (2 * B))
      (generatorW (S.coeff N) t (oscTestFun b.m α)) := hcore
  refine ⟨hcore'.1, ?_⟩
  have hK0 : 0 ≤ KB * B + K1 * (2 * B) := by positivity
  have hul := hCu _ (KB * B + K1 * (2 * B)) hK0 hcore'.1 (fun l hl idx x => by
    have h1 := s55f_partial_le_norm idx (generatorW (S.coeff N) t (oscTestFun b.m α)) x
    have h2 := hcore'.2 l hl x
    simp only [mul_one] at h2
    exact h1.trans h2)
  refine hul.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [hBdef, hΛφ]
  ring

end HRS.MS.Go
