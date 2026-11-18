import HRS.MS.MovBridgeAux8
import HRS.MS.MovForceTie
import HRS.MS.MovThermAux2
import HRS.MS.MovOscAux5
import HRS.MS.ThCorrSob
import HRS.MS.MovOscAux9

/-!
# MOV-C1 (1): Gaussian class, `B1` for Schwartz functions at every real index, the local part of `P`

Namespace `HRS.MS.MovC1`, helper prefix `movc1_`.  Infrastructure for S6.1 (`docs/MOV_PLAN.md`, steps 8, 9); not
manuscript rows.

* `movc1_osc_add`, `movc1_osc_smul`, `movc1_osc_sum`: triangle inequality and finite sums in `Σ^m` for arbitrary
  `MemOsc` functions (the existing triangle inequality `u4_oscNorm_add_le` is for compactly supported functions).
* `MovcG f`: `f ∈ C^∞` with `‖D^k f(x)‖ ≤ C_k exp(-c‖x‖²)` (common rate `c`); closed under multiplication by smooth
  functions with linearly growing derivatives (`movc1_G_mul`), coordinate derivatives (`movc1_G_Dj`); `movc1_G_schwartz`
  packages such a function as a `SchwartzMap`; `movc1_G_Q` gives the `mova3b2_Q` bounds used by `mo_bridge2`, `mo_mult_cb`.
* `movc1_sob_sup`: for a real Schwartz function `F`, `‖F‖_{H^r}` is the supremum of the pairings `|∫ F φ|/‖φ‖_{H^{-r}}`
  (test function `φ = Re W(D)^r F`).
* `movc1_B1`: **B1 for Schwartz functions at every real index** (`mo_bridge1` is only stated for the Hermite span and
  `s ≥ 0`; this replaces it): for `ω` of class `MovcG` and real `r`, `‖ω v‖_{H^r} ≤ C ‖v‖_{Σ^r}` for Schwartz `v`.
  Proof by duality with `mo_bridge2` and `mo_dual_le`.
* `movc1_sob_D`: `∂_j : H^t → H^{t-1}` on Schwartz functions.
* `movc1_B2G`, `movc1_loc_term`: for `f ∈ H^τ` and `σ ≤ τ + d - s`, `b · (g_loc * f) ∈ Σ^σ` with norm `≤ C ‖f‖_{H^τ}`
  (`tc3_riesz_loc_sobolev_gain` then `mo_bridge2`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovC1

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.Mov0

variable {d : ℕ}

/-! ### Triangle inequality and scalar multiples for `Σ^m` -/

lemma movc1_coeff_add {f g : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hg : MemLp g 2 (volume : Measure (Euc d))) (α : MultiIndex d) :
    hermiteCoeff (fun x => f x + g x) α = hermiteCoeff f α + hermiteCoeff g α := by
  unfold hermiteCoeff
  simp_rw [add_mul]
  exact integral_add (mova2_int_mul hf α) (mova2_int_mul hg α)

lemma movc1_coeff_smul (c : ℝ) (f : Euc d → ℝ) (α : MultiIndex d) :
    hermiteCoeff (fun x => c * f x) α = c * hermiteCoeff f α := by
  unfold hermiteCoeff
  simp_rw [mul_assoc]
  exact integral_const_mul c _

lemma movc1_osc_smul (m c : ℝ) {f : Euc d → ℝ} (hf : MemOsc m f) :
    MemOsc m (fun x => c * f x) ∧ oscNorm m (fun x => c * f x) = |c| * oscNorm m f := by
  have hL : MemLp (fun x => c * f x) 2 (volume : Measure (Euc d)) := hf.1.const_mul c
  have hw : ∀ α : MultiIndex d, oscEigenvalue d α ^ m * hermiteCoeff (fun x => c * f x) α ^ 2 =
      c ^ 2 * (oscEigenvalue d α ^ m * hermiteCoeff f α ^ 2) := fun α => by
    rw [movc1_coeff_smul]; ring
  refine ⟨⟨hL, ?_⟩, ?_⟩
  · simp_rw [hw]; exact hf.2.mul_left _
  · unfold oscNorm
    simp_rw [hw]
    rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma movc1_osc_add (m : ℝ) {f g : Euc d → ℝ} (hf : MemOsc m f) (hg : MemOsc m g) :
    MemOsc m (fun x => f x + g x) ∧
      oscNorm m (fun x => f x + g x) ≤ oscNorm m f + oscNorm m g := by
  have hL : MemLp (fun x => f x + g x) 2 (volume : Measure (Euc d)) := hf.1.add hg.1
  have hfg : MemOsc m (fun x => f x + g x) := by
    refine ⟨hL, ?_⟩
    refine Summable.of_nonneg_of_le (fun α => mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _))
      (fun α => ?_) ((hf.2.add hg.2).mul_left 2)
    rw [movc1_coeff_add hf.1 hg.1]
    have h0 := (Real.rpow_nonneg (oscEv_pos (d := d) α).le m)
    nlinarith [mul_nonneg h0 (sq_nonneg (hermiteCoeff f α - hermiteCoeff g α))]
  refine ⟨hfg, ?_⟩
  have hlin : OscSpace.ofFun m (fun x => f x + g x) = OscSpace.ofFun m f + OscSpace.ofFun m g := by
    rw [OscSpace.ofFun_eq hfg, OscSpace.ofFun_eq hf, OscSpace.ofFun_eq hg]
    apply lp.ext
    funext α
    change oscEigenvalue d α ^ (m / 2) * hermiteCoeff (fun x => f x + g x) α =
      oscEigenvalue d α ^ (m / 2) * hermiteCoeff f α + oscEigenvalue d α ^ (m / 2) * hermiteCoeff g α
    rw [movc1_coeff_add hf.1 hg.1]; ring
  calc oscNorm m (fun x => f x + g x) = ‖OscSpace.ofFun m (fun x => f x + g x)‖ :=
        (OscSpace.norm_ofFun _ hfg).symm
    _ = ‖OscSpace.ofFun m f + OscSpace.ofFun m g‖ := by rw [hlin]
    _ ≤ ‖OscSpace.ofFun m f‖ + ‖OscSpace.ofFun m g‖ := norm_add_le _ _
    _ = oscNorm m f + oscNorm m g := by rw [OscSpace.norm_ofFun _ hf, OscSpace.norm_ofFun _ hg]

lemma movc1_osc_zero (m : ℝ) :
    MemOsc m (fun _ : Euc d => (0 : ℝ)) ∧ oscNorm m (fun _ : Euc d => (0 : ℝ)) = 0 := by
  have hc : ∀ α : MultiIndex d, hermiteCoeff (fun _ : Euc d => (0 : ℝ)) α = 0 := fun α => by
    simp [hermiteCoeff]
  refine ⟨⟨MemLp.zero, ?_⟩, ?_⟩
  · simp only [hc]; simp
  · unfold oscNorm; simp [hc]

/-- Finite sums in `Σ^m`: membership and the triangle inequality. -/
lemma movc1_osc_sum (m : ℝ) {ι : Type*} (S : Finset ι) {f : ι → Euc d → ℝ}
    (hf : ∀ i ∈ S, MemOsc m (f i)) :
    MemOsc m (fun x => ∑ i ∈ S, f i x) ∧ oscNorm m (fun x => ∑ i ∈ S, f i x) ≤ ∑ i ∈ S, oscNorm m (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := movc1_osc_zero (d := d) m
    simpa using ⟨h1, h2.le⟩
  | insert a S ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨h3, h4⟩ := movc1_osc_add m (hf a (Finset.mem_insert_self _ _)) h1
    simp only [Finset.sum_insert ha]
    exact ⟨h3, h4.trans (by linarith)⟩

/-! ### Gaussian class -/

/-- `f` is smooth with all derivatives bounded by a Gaussian (common rate). -/
def MovcG (f : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ x : Euc d,
    ‖iteratedFDeriv ℝ k f x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2)

lemma movc1_pow_exp_le {c : ℝ} (hc : 0 < c) (N : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ (N.factorial : ℝ) * Real.exp (1 + 1 / (2 * c)) := by
  have h := mov0_pow_exp_bound (a := 2 * c) (M := 0) (by positivity) N r hr
  have e1 : -(2 * c * r ^ 2 / 2) + 0 * r = -c * r ^ 2 := by ring
  rw [e1] at h
  refine h.trans ?_
  have e2 : (0 + 1 : ℝ) ^ 2 / (2 * c) = 1 / (2 * c) := by ring
  rw [e2]
  have hfac : (0 : ℝ) ≤ N.factorial := Nat.cast_nonneg _
  have h3 : Real.exp (-(2 * c / 4) * r ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg r]
  calc (N.factorial : ℝ) * Real.exp (1 + 1 / (2 * c)) * Real.exp (-(2 * c / 4) * r ^ 2)
      ≤ (N.factorial : ℝ) * Real.exp (1 + 1 / (2 * c)) * 1 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := mul_one _

lemma movc1_G_nonneg {f : Euc d → ℝ} {k : ℕ} {C c : ℝ}
    (h : ∀ x : Euc d, ‖iteratedFDeriv ℝ k f x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2)) : 0 ≤ C := by
  have := h 0
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero, mul_one] at this
  exact (norm_nonneg _).trans this

/-- Leibniz: multiplying a Gaussian-class function by a smooth function with linearly growing derivatives. -/
lemma movc1_G_mul {f b : Euc d → ℝ} (hf : MovcG f) (hb : ContDiff ℝ ∞ b)
    (hbd : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Euc d, ‖iteratedFDeriv ℝ k b x‖ ≤ M * (1 + ‖x‖)) :
    MovcG (fun x => b x * f x) := by
  obtain ⟨hfs, c, hc, hfk⟩ := hf
  choose Cf hCf using hfk
  choose Mb hMb0 hMb using hbd
  refine ⟨hb.mul hfs, c / 2, by positivity, fun k => ?_⟩
  have hc2 : 0 < c / 2 := by positivity
  set K : ℝ := Real.exp (1 + 1 / (2 * (c / 2))) with hK
  have hKpos : 0 < K := Real.exp_pos _
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (Mb i * Cf (k - i) * K), fun x => ?_⟩
  have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (k : WithTop ℕ∞))
    (hb.of_le (by exact_mod_cast le_top)) (hfs.of_le (by exact_mod_cast le_top)) x (n := k) le_rfl
  refine h1.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := by simpa [Nat.lt_succ_iff] using hi
  have hCf0 : 0 ≤ Cf (k - i) := movc1_G_nonneg (hCf (k - i))
  have hr := movc1_pow_exp_le hc2 1 ‖x‖ (norm_nonneg _)
  rw [pow_one, Nat.factorial_one, Nat.cast_one, one_mul, ← hK] at hr
  have hexp : Real.exp (-c * ‖x‖ ^ 2) = Real.exp (-(c / 2) * ‖x‖ ^ 2) * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hch : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i b x‖ * ‖iteratedFDeriv ℝ (k - i) f x‖
      ≤ (k.choose i : ℝ) * (Mb i * (1 + ‖x‖)) * (Cf (k - i) * Real.exp (-c * ‖x‖ ^ 2)) := by
        rw [mul_assoc, mul_assoc]
        refine mul_le_mul_of_nonneg_left (mul_le_mul (hMb i x) (hCf (k - i) x) (norm_nonneg _)
          (mul_nonneg (hMb0 i) (by positivity))) hch
    _ = (k.choose i : ℝ) * (Mb i * Cf (k - i)) *
          ((1 + ‖x‖) * Real.exp (-(c / 2) * ‖x‖ ^ 2) * Real.exp (-(c / 2) * ‖x‖ ^ 2)) := by
        rw [hexp]; ring
    _ ≤ (k.choose i : ℝ) * (Mb i * Cf (k - i)) * (K * Real.exp (-(c / 2) * ‖x‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hch (mul_nonneg (hMb0 i) hCf0))
        exact mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ = _ := by ring

open HRS.MS.MovForce

lemma movc1_G_schwartz {f : Euc d → ℝ} (hf : MovcG f) : ∃ φ : SchwartzMap (Euc d) ℝ, ⇑φ = f := by
  obtain ⟨hs, c, hc, hk⟩ := hf
  refine ⟨⟨f, hs, fun k n => ?_⟩, rfl⟩
  obtain ⟨C, hC⟩ := hk n
  have hC0 : 0 ≤ C := movc1_G_nonneg hC
  refine ⟨C * ((k.factorial : ℝ) * Real.exp (1 + 1 / (2 * c))), fun x => ?_⟩
  have h1 := movc1_pow_exp_le hc k ‖x‖ (norm_nonneg _)
  have h2 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith) k
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ (1 + ‖x‖) ^ k * (C * Real.exp (-c * ‖x‖ ^ 2)) :=
        mul_le_mul h2 (hC x) (norm_nonneg _) (by positivity)
    _ = C * ((1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 hC0

/-- Coordinate derivatives of a Gaussian-class function are Gaussian-class. -/
lemma movc1_G_Dj {f : Euc d → ℝ} (hf : MovcG f) (j : Fin d) : MovcG (mova3b1_Dj j f) := by
  obtain ⟨hs, c, hc, hk⟩ := hf
  refine ⟨mova3b2_contDiff_Dj j hs, c, hc, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hk (k + 1)
  refine ⟨C, fun x => ?_⟩
  have h1 := movb2_norm_iter_partial (hs.of_le (by exact_mod_cast le_top) : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f)
    (EuclideanSpace.single j (1 : ℝ)) x
  have h2 : ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [h2, one_mul] at h1
  exact h1.trans (hC x)

/-- Bounds of `mova3b2_Q` for Gaussian-class functions. -/
lemma movc1_G_Q {f : Euc d → ℝ} (hf : MovcG f) (K m : ℕ) : ∃ A : ℝ, mova3b2_Q K m A f := by
  obtain ⟨hs, c, hc, hk⟩ := hf
  choose C hC using hk
  have hC0 : ∀ k, 0 ≤ C k := fun k => movc1_G_nonneg (hC k)
  refine ⟨∑ k ∈ Finset.range (K + 1), C k * ((m.factorial : ℝ) * Real.exp (1 + 1 / (2 * c))), ?_⟩
  refine mova3b2_Q_of_iter hs (fun k hk x => ?_)
  have hkK : k ∈ Finset.range (K + 1) := Finset.mem_range.2 (by omega)
  have h1 := movc1_pow_exp_le hc m ‖x‖ (norm_nonneg _)
  calc ‖iteratedFDeriv ℝ k f x‖ * (1 + ‖x‖) ^ m
      ≤ (C k * Real.exp (-c * ‖x‖ ^ 2)) * (1 + ‖x‖) ^ m :=
        mul_le_mul_of_nonneg_right (hC k x) (by positivity)
    _ = C k * ((1 + ‖x‖) ^ m * Real.exp (-c * ‖x‖ ^ 2)) := by ring
    _ ≤ C k * ((m.factorial : ℝ) * Real.exp (1 + 1 / (2 * c))) :=
        mul_le_mul_of_nonneg_left h1 (hC0 k)
    _ ≤ _ := Finset.single_le_sum (f := fun k => C k * ((m.factorial : ℝ) * Real.exp (1 + 1 / (2 * c))))
        (fun k _ => mul_nonneg (hC0 k) (by positivity)) hkK

/-! ### Duality: the `H^r` norm of a Schwartz function as a supremum of pairings -/

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux
open scoped FourierTransform ComplexConjugate

local notation "𝓢C" => SchwartzMap (Euc d) ℂ
local notation "𝓢R" => SchwartzMap (Euc d) ℝ

lemma movc1_conj_four (F : 𝓢R) (ξ : Euc d) :
    conj ((𝓕 (mova3b2_cx F) : 𝓢C) (-ξ)) = (𝓕 (mova3b2_cx F) : 𝓢C) ξ := by
  have h1 : conjSchwartz (mova3b2_cx F) = mova3b2_cx F := by
    ext x; simp [conjSchwartz_apply]
  have := fourier_conjSchwartz (mova3b2_cx F) ξ
  rw [h1] at this
  exact this.symm

theorem movc1_sob_sup (F : 𝓢R) (r K : ℝ) (hK : 0 ≤ K)
    (h : ∀ φ : 𝓢R, |∫ x, F x * φ x| ≤ K * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (-r) (⇑φ))) :
    HRS.PDE.ToolboxRd.MemSobolev r (⇑F) ∧ Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r (⇑F)) ≤ K := by
  set Fc : 𝓢C := mova3b2_cx F with hFc
  set φc : 𝓢C := mova3b2_rot (r : ℂ) Fc with hφc
  set φ : 𝓢R := mova3b2_re φc with hφ
  have hW := fun ξ : Euc d => mova3b1_W_pos ξ
  have hfour : ∀ ξ : Euc d, (𝓕 φc : 𝓢C) ξ = ((mova3b1_W ξ ^ r : ℝ) : ℂ) * (𝓕 Fc : 𝓢C) ξ := by
    intro ξ
    rw [hφc, mova3b2_fourier_rot]
    simp only [mova3b2_gm]
    rw [← Complex.ofReal_cpow (hW ξ).le]
  have hI : Integrable (fun ξ : Euc d => mova3b1_W ξ ^ r * ‖fourierL2 (⇑F) ξ‖ ^ 2) volume := by
    refine (mova3b2_int_W (𝓕 Fc : 𝓢C) r).congr ?_
    filter_upwards [mova3b2_fourierL2_eq F] with ξ h
    rw [h]
  have hMem : HRS.PDE.ToolboxRd.MemSobolev r (⇑F) := ⟨F.memLp 2 volume, hI⟩
  set I : ℝ := HRS.PDE.ToolboxRd.sobolevNormSq r (⇑F) with hIdef
  have hIeq : I = ∫ ξ, mova3b1_W ξ ^ r * ‖(𝓕 Fc : 𝓢C) ξ‖ ^ 2 := by
    rw [hIdef, mova3b1_sobolevNormSq_eq]
    refine integral_congr_ae ?_
    filter_upwards [mova3b2_fourierL2_eq F] with ξ h
    rw [h]
  have hI0 : 0 ≤ I := mova3b2_sobolevNormSq_nonneg r _
  -- the norm of the test function
  have hsob := mova3b2_sob φc (-r)
  have hint : ∫ ξ, mova3b1_W ξ ^ (-r) * ‖(𝓕 φc : 𝓢C) ξ‖ ^ 2 = I := by
    rw [hIeq]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    beta_reduce
    rw [hfour, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hW ξ).le _), mul_pow,
      ← mul_assoc]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hW ξ).le, ← Real.rpow_add (hW ξ)]
    congr 1; push_cast; ring
  have hφn : HRS.PDE.ToolboxRd.sobolevNormSq (-r) (⇑φ) ≤ I := by
    rw [← hint, ← hsob.2.2]
    have := mova3b2_sobolevNormSq_nonneg (-r) (⇑(mova3b2_im φc))
    linarith
  -- the pairing
  have hpair : ∫ x, F x * φ x = I := by
    have hFL := F.memLp 2 volume
    have hφL := φ.memLp 2 volume
    rw [integral_mul_eq_re_fourierL2 hFL hφL]
    have hpt : ∀ᵐ ξ : Euc d ∂volume, fourierL2 (⇑F) ξ * conj (fourierL2 (⇑φ) ξ) =
        ((mova3b1_W ξ ^ r * ‖(𝓕 Fc : 𝓢C) ξ‖ ^ 2 : ℝ) : ℂ) := by
      filter_upwards [mova3b2_fourierL2_eq F, mova3b2_fourierL2_eq φ] with ξ h1 h2
      rw [h1, h2, hφ, mova3b2_fourier_re, hfour, hfour]
      have e1 : conj (((mova3b1_W (-ξ) ^ r : ℝ) : ℂ) * (𝓕 Fc : 𝓢C) (-ξ)) =
          ((mova3b1_W ξ ^ r : ℝ) : ℂ) * (𝓕 Fc : 𝓢C) ξ := by
        rw [map_mul, Complex.conj_ofReal, movc1_conj_four, mova3b1_W_neg]
      rw [e1]
      have e2 : (((mova3b1_W ξ ^ r : ℝ) : ℂ) * (𝓕 Fc : 𝓢C) ξ +
          ((mova3b1_W ξ ^ r : ℝ) : ℂ) * (𝓕 Fc : 𝓢C) ξ) / 2 = ((mova3b1_W ξ ^ r : ℝ) : ℂ) * (𝓕 Fc : 𝓢C) ξ := by
        ring
      rw [e2, map_mul, Complex.conj_ofReal]
      have e3 : (𝓕 Fc : 𝓢C) ξ * conj ((𝓕 Fc : 𝓢C) ξ) = ((‖(𝓕 Fc : 𝓢C) ξ‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj]; simp [Complex.normSq_eq_norm_sq]
      rw [show (𝓕 Fc : 𝓢C) ξ * (((mova3b1_W ξ ^ r : ℝ) : ℂ) * conj ((𝓕 Fc : 𝓢C) ξ)) =
          ((mova3b1_W ξ ^ r : ℝ) : ℂ) * ((𝓕 Fc : 𝓢C) ξ * conj ((𝓕 Fc : 𝓢C) ξ)) by ring, e3]
      push_cast; ring
    rw [integral_congr_ae hpt, integral_complex_ofReal, Complex.ofReal_re, hIeq]
  -- conclude
  refine ⟨hMem, ?_⟩
  have h1 := h φ
  rw [hpair, abs_of_nonneg hI0] at h1
  have h2 : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (-r) (⇑φ)) ≤ Real.sqrt I := Real.sqrt_le_sqrt hφn
  have h3 : I ≤ K * Real.sqrt I := h1.trans (mul_le_mul_of_nonneg_left h2 hK)
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero]; exact hK
  · have hs : 0 < Real.sqrt I := Real.sqrt_pos.2 hpos
    have : Real.sqrt I * Real.sqrt I ≤ K * Real.sqrt I := by
      rw [Real.mul_self_sqrt hI0]; exact h3
    exact le_of_mul_le_mul_right this hs

lemma movc1_memSob_schwartz (φ : 𝓢R) (t : ℝ) : HRS.PDE.ToolboxRd.MemSobolev t (⇑φ) := by
  refine ⟨φ.memLp 2 volume, ?_⟩
  show Integrable (fun ξ : Euc d => mova3b1_W ξ ^ t * ‖fourierL2 (⇑φ) ξ‖ ^ 2) volume
  refine (mova3b2_int_W (𝓕 (mova3b2_cx φ) : 𝓢C) t).congr ?_
  filter_upwards [mova3b2_fourierL2_eq φ] with ξ h
  rw [h]

/-- **B1 for Schwartz functions, every real index** (by duality with `mo_bridge2`): for a Gaussian-class
multiplier `om` and every real `r` there is `C` with `‖om v‖_{H^r} ≤ C ‖v‖_{Σ^r}` for all Schwartz `v`. -/
theorem movc1_B1 {om : Euc d → ℝ} (hom : MovcG om) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : 𝓢R, HRS.PDE.ToolboxRd.MemSobolev r (fun x => om x * v x) ∧
      Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r (fun x => om x * v x)) ≤ C * oscNorm r v := by
  obtain ⟨φom, hφom⟩ := movc1_G_schwartz hom
  set N : ℕ := ⌈|r|⌉₊ with hN
  have hrN : -r ≤ (N : ℝ) := by
    have := Nat.le_ceil |r|
    have := neg_le_abs r
    linarith
  obtain ⟨C2, hC2, hB2⟩ := mo_bridge2 (d := d) (-r) N hrN
  obtain ⟨A, hA⟩ := movc1_G_Q hom (max N ⌈-(-r)⌉₊) N
  have hA0 : 0 ≤ A := by
    exact (abs_nonneg _).trans (mova3b2_Q_abs hA 0)
  have htg : Function.HasTemperateGrowth om := by rw [← hφom]; exact φom.hasTemperateGrowth
  refine ⟨C2 * A, mul_nonneg hC2 hA0, fun v => ?_⟩
  -- the profile as a Schwartz function
  have hG : MovcG (fun x => v x * om x) := by
    refine movc1_G_mul hom (v.smooth ⊤) (fun k => ?_)
    obtain ⟨M, hM⟩ := (⟨SchwartzMap.seminorm ℝ 0 k v, fun x => SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ v k x⟩ :
      ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ k v x‖ ≤ M)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    exact ⟨M, hM0, fun x => (hM x).trans (by nlinarith [norm_nonneg x])⟩
  obtain ⟨F, hF⟩ := movc1_G_schwartz hG
  have hFe : (fun x => om x * v x) = ⇑F := by rw [hF]; funext x; ring
  rw [hFe]
  have hv : MemOsc r (⇑v) := memOsc_schwartz r v
  have hK : 0 ≤ C2 * A * oscNorm r v := mul_nonneg (mul_nonneg hC2 hA0) (Real.sqrt_nonneg _)
  refine movc1_sob_sup F r _ hK (fun φ => ?_)
  have hφ := movc1_memSob_schwartz φ (-r)
  obtain ⟨hm, hn⟩ := hB2 A hA0 om htg hA (⇑φ) hφ
  have hv' : MemOsc (-(-r)) (⇑v) := by rw [neg_neg]; exact hv
  have hd := mo_dual_le (-r) hv' hm
  rw [neg_neg] at hd
  have hint : ∫ x, F x * φ x = ∫ x, v x * (om x * φ x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : F x = om x * v x := by rw [← hFe]
    simp only [this]; ring
  rw [hint]
  calc |∫ x, v x * (om x * φ x)| ≤ oscNorm r (⇑v) * oscNorm (-r) (fun x => om x * φ x) := hd
    _ ≤ oscNorm r (⇑v) * (C2 * A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (-r) (⇑φ))) :=
        mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)
    _ = _ := by ring

/-! ### Sobolev bookkeeping on the Fourier side -/

lemma movc1_sob_mono_norm {τ σ : ℝ} {u : Euc d → ℝ} (h : σ ≤ τ) (hu : HRS.PDE.ToolboxRd.MemSobolev τ u) :
    HRS.PDE.ToolboxRd.sobolevNormSq σ u ≤ HRS.PDE.ToolboxRd.sobolevNormSq τ u := by
  have hu' := memSobolev_mono h hu
  rw [sobolevNormSq_eq, sobolevNormSq_eq]
  refine integral_mono hu'.2 hu.2 fun ξ => ?_
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (one_le_wt ξ) h) (by positivity)

lemma movc1_sq_le_wt (ξ : Euc d) (j : Fin d) : (2 * Real.pi * |ξ j|) ^ 2 ≤ wt ξ := by
  have h1 : |ξ j| ^ 2 ≤ ‖ξ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have := Finset.single_le_sum (f := fun i => ‖ξ i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    simpa [Real.norm_eq_abs] using this
  unfold wt
  have : (2 * Real.pi * |ξ j|) ^ 2 = 4 * Real.pi ^ 2 * |ξ j| ^ 2 := by ring
  rw [this]
  nlinarith [sq_nonneg Real.pi, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (sq_nonneg Real.pi))
    (sub_nonneg.2 h1)]

/-- `∂_j : H^t → H^{t-1}` on Schwartz functions, with the norm bound. -/
lemma movc1_sob_D (u : 𝓢R) (j : Fin d) {t : ℝ} (hu : HRS.PDE.ToolboxRd.MemSobolev t (⇑u)) :
    HRS.PDE.ToolboxRd.MemSobolev (t - 1) (⇑(mova1_D j u)) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq (t - 1) (⇑(mova1_D j u)) ≤ HRS.PDE.ToolboxRd.sobolevNormSq t (⇑u) := by
  have hG : MemLp (⇑(mova1_D j u)) 2 volume := (mova1_D j u).memLp 2 volume
  have hae := mova1_norm_fourier_D j u
  have hpt : ∀ᵐ ξ : Euc d ∂volume, wt ξ ^ (t - 1) * ‖fourierL2 (⇑(mova1_D j u)) ξ‖ ^ 2 ≤
      wt ξ ^ t * ‖fourierL2 (⇑u) ξ‖ ^ 2 := by
    filter_upwards [hae] with ξ h
    have hsq : ‖fourierL2 (⇑(mova1_D j u)) ξ‖ ^ 2 =
        (2 * Real.pi * |ξ j|) ^ 2 * ‖fourierL2 (⇑u) ξ‖ ^ 2 := by rw [h]; ring
    have hw := wt_pos (d := d) ξ
    have e : wt ξ ^ t = wt ξ ^ (t - 1) * wt ξ := by
      rw [← Real.rpow_add_one hw.ne']; congr 1; ring
    rw [hsq, e]
    calc wt ξ ^ (t - 1) * ((2 * Real.pi * |ξ j|) ^ 2 * ‖fourierL2 (⇑u) ξ‖ ^ 2)
        ≤ wt ξ ^ (t - 1) * (wt ξ * ‖fourierL2 (⇑u) ξ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (movc1_sq_le_wt ξ j) (sq_nonneg _))
            (Real.rpow_nonneg hw.le _)
      _ = _ := by ring
  have hint : Integrable (fun ξ : Euc d => wt ξ ^ (t - 1) * ‖fourierL2 (⇑(mova1_D j u)) ξ‖ ^ 2) volume := by
    refine Integrable.mono' hu.2 (aesm_wt_mul (aestronglyMeasurable_fourierL2 hG) (t - 1)) ?_
    filter_upwards [hpt] with ξ h
    have h0 : 0 ≤ wt ξ ^ (t - 1) * ‖fourierL2 (⇑(mova1_D j u)) ξ‖ ^ 2 := by
      have := wt_pos (d := d) ξ
      positivity
    rw [Real.norm_of_nonneg h0]
    exact h
  refine ⟨⟨hG, hint⟩, ?_⟩
  rw [sobolevNormSq_eq, sobolevNormSq_eq]
  exact integral_mono_ae hint hu.2 hpt

/-! ### The local part: `H^τ → Σ^σ` -/

/-- `B2` for a Gaussian-class multiplier, packaged. -/
lemma movc1_B2G {b : Euc d → ℝ} (hb : MovcG b) (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev σ w →
      MemOsc σ (fun x => b x * w x) ∧
        oscNorm σ (fun x => b x * w x) ≤ C * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq σ w) := by
  obtain ⟨φ, hφ⟩ := movc1_G_schwartz hb
  set N : ℕ := ⌈|σ|⌉₊ with hN
  have hσN : σ ≤ (N : ℝ) := (le_abs_self σ).trans (Nat.le_ceil _)
  obtain ⟨C2, hC2, hB2⟩ := mo_bridge2 (d := d) σ N hσN
  obtain ⟨A, hA⟩ := movc1_G_Q hb (max N ⌈-σ⌉₊) N
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (mova3b2_Q_abs hA 0)
  have htg : Function.HasTemperateGrowth b := by rw [← hφ]; exact φ.hasTemperateGrowth
  exact ⟨C2 * A, mul_nonneg hC2 hA0, fun w hw => by
    obtain ⟨h1, h2⟩ := hB2 A hA0 b htg hA w hw
    exact ⟨h1, h2⟩⟩

lemma movc1_convFun_eq_T (s : ℝ) (f : Euc d → ℝ) :
    HRS.Whole.convFun (fun x => movb2_theta d x * rieszKernel d s x) f = movb2_T (movb2_gloc d s) f := by
  funext x
  rw [mv1_convFun_eq]
  rfl

/-- Local term: for `f ∈ H^τ` and `σ ≤ τ + d - s`, `b · (g_loc * f) ∈ Σ^σ` with norm `≤ C ‖f‖_{H^τ}`. -/
theorem movc1_loc_term {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {b : Euc d → ℝ} (hb : MovcG b)
    {σ τ : ℝ} (hστ : σ ≤ τ + ((d : ℝ) - s)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev τ f →
      MemOsc σ (fun x => b x * movb2_T (movb2_gloc d s) f x) ∧
        oscNorm σ (fun x => b x * movb2_T (movb2_gloc d s) f x) ≤
          C * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq τ f) := by
  obtain ⟨C1, hC1, hgain⟩ := HRS.MS.Tc3.tc3_riesz_loc_sobolev_gain (θ := movb2_theta d)
    ((movb2_bump d).contDiff.of_le (by exact_mod_cast le_top)) (movb2_bump d).hasCompactSupport hs0 hsd
  obtain ⟨C2, hC2, hB2⟩ := movc1_B2G hb σ
  refine ⟨C2 * C1, mul_nonneg hC2 hC1.le, fun f hf => ?_⟩
  obtain ⟨hm, hn⟩ := hgain τ f hf
  rw [movc1_convFun_eq_T] at hm hn
  have hmσ := memSobolev_mono hστ hm
  obtain ⟨h1, h2⟩ := hB2 _ hmσ
  refine ⟨h1, h2.trans ?_⟩
  have h3 : HRS.PDE.ToolboxRd.sobolevNormSq σ (movb2_T (movb2_gloc d s) f) ≤ C1 ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq τ f :=
    (movc1_sob_mono_norm hστ hm).trans hn
  have h4 : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq σ (movb2_T (movb2_gloc d s) f)) ≤ C1 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq τ f) := by
    calc _ ≤ Real.sqrt (C1 ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq τ f) := Real.sqrt_le_sqrt h3
      _ = C1 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq τ f) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC1.le]
  calc C2 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq σ (movb2_T (movb2_gloc d s) f))
      ≤ C2 * (C1 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq τ f)) := mul_le_mul_of_nonneg_left h4 hC2
    _ = _ := by ring

end HRS.MS.MovC1
