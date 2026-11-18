import HRS.MS.MovOscAux3
import HRS.MP.RdGenSob

/-!
# MOV-A1, part 4: the embedding `Σ^n ⊂ C_b^i` (`i + d/2 < n`)

Namespace `HRS.MS.MovOsc` (helpers `mova1_`, main statement `mo_sobolev_emb`).

`mo_sobolev_emb (i n : ℕ) (hn : i + d/2 < n) : ∃ C, ∀ f : 𝓢, ∀ x, ‖D^i f(x)‖ ≤ C ‖f‖_{Σ^n}`.

Route: `HRS.MP.RdGen.rg_sobolev_embedding` bounds `‖D^i φ(x)‖` by `C ‖φ‖_{H^n}`.  For Schwartz `f` we show
`f ∈ H^n` and `‖f‖_{H^n}² = ∫ (1 + 4π²|ξ|²)^n |f̂|² ≤ (d+1)^n (‖f‖₂² + ∑_j ‖∂_j^n f‖₂²)`, using the
elementary bound `(1 + ∑ t_j)^n ≤ (d+1)^n (1 + ∑ t_j^n)` with `t_j = (2π ξ_j)²` and
`|\\widehat{∂_j^n f}| = (2π|ξ_j|)^n |f̂|` (Plancherel for Schwartz functions).  The norms
`‖f‖₂, ‖∂_j^n f‖₂` are bounded by `‖f‖_{Σ^n}` by the order-loss calculus (`mova1_Bnd`) and `oscNorm_zero`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate

namespace HRS.MS.MovOsc

open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

local notation "𝒮" => SchwartzMap (Euc d) ℝ

/-! ### Fourier transform of `∂_j` -/

theorem mova1_fourier_D (l : Fin d) (v : 𝒮) (ξ : Euc d) :
    𝓕 (fun x : Euc d => ((mova1_D l v x : ℝ) : ℂ)) ξ =
      (2 * Real.pi * Complex.I * (ξ l : ℂ)) * 𝓕 (fun x : Euc d => ((v x : ℝ) : ℂ)) ξ := by
  set V : SchwartzMap (Euc d) ℂ := v.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM with hV
  have h1 := SchwartzMap.fourier_lineDerivOp_eq V (EuclideanSpace.single l 1)
  have h2 : ⇑(LineDeriv.lineDerivOp (EuclideanSpace.single l 1 : Euc d) V : SchwartzMap (Euc d) ℂ) =
      fun x : Euc d => ((mova1_D l v x : ℝ) : ℂ) := by
    ext x
    show fderiv ℝ (⇑V) x _ = _
    have : ⇑V = fun x => ((v x : ℝ) : ℂ) := rfl
    rw [this, mova1_D_apply]
    have hd : DifferentiableAt ℝ (⇑v) x := v.differentiableAt
    rw [show (fun x => ((v x : ℝ) : ℂ)) = Complex.ofRealCLM ∘ ⇑v from rfl,
      (Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt).fderiv]
    rfl
  have h3 : ⇑V = fun x => ((v x : ℝ) : ℂ) := rfl
  have hg : (fun x : Euc d => inner ℝ x (EuclideanSpace.single l 1 : Euc d)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (EuclideanSpace.single l 1 : Euc d)).hasTemperateGrowth
  have e : 𝓕 (fun x : Euc d => ((mova1_D l v x : ℝ) : ℂ)) ξ =
      (𝓕 (LineDeriv.lineDerivOp (EuclideanSpace.single l 1 : Euc d) V : SchwartzMap (Euc d) ℂ)) ξ := by
    rw [SchwartzMap.fourier_coe, h2]
  rw [e, h1]
  simp only [smul_apply, smul_eq_mul]
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.fourier_coe, h3]
  simp [EuclideanSpace.inner_single_right]
  ring

theorem mova1_norm_fourier_D (j : Fin d) (v : 𝒮) :
    ∀ᵐ ξ : Euc d, ‖fourierL2 ⇑(mova1_D j v) ξ‖ = 2 * Real.pi * |ξ j| * ‖fourierL2 ⇑v ξ‖ := by
  filter_upwards [fourierL2_schwartz (mova1_D j v), fourierL2_schwartz v] with ξ h1 h2
  rw [h1, h2, mova1_fourier_D, norm_mul]
  congr 1
  simp [abs_of_pos Real.pi_pos]

theorem mova1_norm_fourier_Diter (j : Fin d) (n : ℕ) (v : 𝒮) :
    ∀ᵐ ξ : Euc d, ‖fourierL2 ⇑((mova1_D j)^[n] v) ξ‖ =
      (2 * Real.pi * |ξ j|) ^ n * ‖fourierL2 ⇑v ξ‖ := by
  induction n with
  | zero => exact Eventually.of_forall fun ξ => by simp
  | succ n ih =>
    filter_upwards [ih, mova1_norm_fourier_D j ((mova1_D j)^[n] v)] with ξ h1 h2
    rw [Function.iterate_succ_apply', h2, h1]
    ring

/-! ### The weight inequality -/

theorem mova1_wt_pow_le (n : ℕ) (ξ : Euc d) :
    wt ξ ^ n ≤ ((d : ℝ) + 1) ^ n * (1 + ∑ j, ((2 * Real.pi * ξ j) ^ 2) ^ n) := by
  have hwt : wt ξ = 1 + ∑ j, (2 * Real.pi * ξ j) ^ 2 := by
    unfold wt
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.norm_eq_abs, sq_abs]; ring
  have hS : 0 ≤ ∑ j, ((2 * Real.pi * ξ j) ^ 2) ^ n :=
    Finset.sum_nonneg fun j _ => by positivity
  have hd1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  cases n with
  | zero => simp
  | succ m =>
    set f : Option (Fin d) → ℝ := fun o => o.elim 1 (fun j => (2 * Real.pi * ξ j) ^ 2) with hf
    have hf0 : ∀ o ∈ (Finset.univ : Finset (Option (Fin d))), 0 ≤ f o := by
      intro o _
      cases o
      · simp [hf]
      · simp only [hf, Option.elim]; positivity
    have h := pow_sum_div_card_le_sum_pow hf0 m
    have hsum : ∑ o, f o = wt ξ := by
      rw [Fintype.sum_option, hwt]; simp [hf]
    have hsum2 : ∑ o, f o ^ (m + 1) = 1 + ∑ j, ((2 * Real.pi * ξ j) ^ 2) ^ (m + 1) := by
      rw [Fintype.sum_option]; simp [hf]
    have hcard : ((Finset.univ : Finset (Option (Fin d))).card : ℝ) = (d : ℝ) + 1 := by
      simp
    rw [hsum, hsum2, hcard] at h
    have hpos : 0 < ((d : ℝ) + 1) ^ m := by positivity
    have h' : wt ξ ^ (m + 1) ≤ ((d : ℝ) + 1) ^ m * (1 + ∑ j, ((2 * Real.pi * ξ j) ^ 2) ^ (m + 1)) := by
      rw [div_le_iff₀ hpos] at h
      linarith
    calc wt ξ ^ (m + 1) ≤ ((d : ℝ) + 1) ^ m * (1 + ∑ j, ((2 * Real.pi * ξ j) ^ 2) ^ (m + 1)) := h'
      _ ≤ ((d : ℝ) + 1) ^ (m + 1) * (1 + ∑ j, ((2 * Real.pi * ξ j) ^ 2) ^ (m + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        exact pow_le_pow_right₀ hd1 (Nat.le_succ m)

/-! ### `f ∈ H^n` and the bound by derivatives -/

theorem mova1_l2_sq (g : 𝒮) : mo_l2 g ^ 2 = ∫ x, g x ^ 2 :=
  Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)

theorem mova1_sobolev_bound (n : ℕ) (f : 𝒮) :
    HRS.PDE.ToolboxRd.MemSobolev (n : ℝ) (⇑f) ∧ HRS.Whole.sobolevNorm (n : ℝ) (⇑f) ≤
      Real.sqrt (((d : ℝ) + 1) ^ n) * (mo_l2 f + ∑ j : Fin d, mo_l2 ((mova1_D j)^[n] f)) := by
  set B : ℝ := ((d : ℝ) + 1) ^ n with hB
  have hB0 : 0 ≤ B := by positivity
  have hmf : MemLp (⇑f) 2 volume := f.memLp 2
  have hmG : ∀ j : Fin d, MemLp (⇑((mova1_D j)^[n] f)) 2 volume := fun j => ((mova1_D j)^[n] f).memLp 2
  have hF := aestronglyMeasurable_fourierL2 hmf
  have hae : ∀ᵐ ξ : Euc d ∂volume, ∀ j : Fin d, ‖fourierL2 ⇑((mova1_D j)^[n] f) ξ‖ =
      (2 * Real.pi * |ξ j|) ^ n * ‖fourierL2 ⇑f ξ‖ :=
    (ae_all_iff).2 fun j => mova1_norm_fourier_Diter j n f
  set bd : Euc d → ℝ := fun ξ => B * (‖fourierL2 ⇑f ξ‖ ^ 2 +
    ∑ j : Fin d, ‖fourierL2 ⇑((mova1_D j)^[n] f) ξ‖ ^ 2) with hbd
  have hbdi : Integrable bd :=
    ((integrable_norm_sq_fourierL2 hmf).add
      (integrable_finsetSum _ fun j _ => integrable_norm_sq_fourierL2 (hmG j))).const_mul _
  have hle : ∀ᵐ ξ : Euc d ∂volume, wt ξ ^ (n : ℝ) * ‖fourierL2 ⇑f ξ‖ ^ 2 ≤ bd ξ := by
    filter_upwards [hae] with ξ hξ
    rw [Real.rpow_natCast]
    have h1 := mova1_wt_pow_le (d := d) n ξ
    have h2 : 0 ≤ ‖fourierL2 ⇑f ξ‖ ^ 2 := sq_nonneg _
    have h3 : ∀ j : Fin d, ‖fourierL2 ⇑((mova1_D j)^[n] f) ξ‖ ^ 2 =
        ((2 * Real.pi * ξ j) ^ 2) ^ n * ‖fourierL2 ⇑f ξ‖ ^ 2 := by
      intro j
      rw [hξ j]
      have e : (2 * Real.pi * |ξ j|) ^ 2 = (2 * Real.pi * ξ j) ^ 2 := by
        rw [mul_pow, sq_abs, ← mul_pow]
      have key : ∀ A N : ℝ, (A ^ n * N) ^ 2 = (A ^ 2) ^ n * N ^ 2 := fun A N => by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
      rw [key, e]
    simp only [hbd, h3]
    calc wt ξ ^ n * ‖fourierL2 ⇑f ξ‖ ^ 2
        ≤ (B * (1 + ∑ j, ((2 * Real.pi * ξ j) ^ 2) ^ n)) * ‖fourierL2 ⇑f ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = B * (‖fourierL2 ⇑f ξ‖ ^ 2 + ∑ j, ((2 * Real.pi * ξ j) ^ 2) ^ n * ‖fourierL2 ⇑f ξ‖ ^ 2) := by
          rw [← Finset.sum_mul]; ring
  have hint : Integrable (fun ξ : Euc d => wt ξ ^ (n : ℝ) * ‖fourierL2 ⇑f ξ‖ ^ 2) := by
    refine Integrable.mono' hbdi (aesm_wt_mul hF (n : ℝ)) ?_
    filter_upwards [hle] with ξ hξ
    have h0 : 0 ≤ wt ξ ^ (n : ℝ) * ‖fourierL2 ⇑f ξ‖ ^ 2 := by
      have := wt_pos (d := d) ξ
      positivity
    rw [Real.norm_of_nonneg h0]
    exact hξ
  refine ⟨⟨hmf, hint⟩, ?_⟩
  have hsq : sobolevNormSq (n : ℝ) (⇑f) ≤
      B * (mo_l2 f ^ 2 + ∑ j : Fin d, mo_l2 ((mova1_D j)^[n] f) ^ 2) := by
    rw [sobolevNormSq_eq]
    calc ∫ ξ, wt ξ ^ (n : ℝ) * ‖fourierL2 ⇑f ξ‖ ^ 2 ≤ ∫ ξ, bd ξ := integral_mono_ae hint hbdi hle
      _ = B * (mo_l2 f ^ 2 + ∑ j : Fin d, mo_l2 ((mova1_D j)^[n] f) ^ 2) := by
          simp only [hbd]
          rw [integral_const_mul, integral_add (integrable_norm_sq_fourierL2 hmf)
            (integrable_finsetSum _ fun j _ => integrable_norm_sq_fourierL2 (hmG j)),
            integral_finsetSum _ fun j _ => integrable_norm_sq_fourierL2 (hmG j),
            integral_norm_sq_fourierL2 hmf, mova1_l2_sq]
          congr 2
          exact Finset.sum_congr rfl fun j _ => by
            rw [integral_norm_sq_fourierL2 (hmG j), mova1_l2_sq]
  unfold HRS.Whole.sobolevNorm
  have ha := mo_l2_nonneg (⇑f)
  have hb : ∀ j : Fin d, 0 ≤ mo_l2 (⇑((mova1_D j)^[n] f)) := fun j => mo_l2_nonneg _
  have hsum2 : ∑ j : Fin d, mo_l2 ((mova1_D j)^[n] f) ^ 2 ≤
      (∑ j : Fin d, mo_l2 ((mova1_D j)^[n] f)) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => hb j
  have hsb : 0 ≤ ∑ j : Fin d, mo_l2 ((mova1_D j)^[n] f) := Finset.sum_nonneg fun j _ => hb j
  calc Real.sqrt (sobolevNormSq (n : ℝ) (⇑f))
      ≤ Real.sqrt (B * (mo_l2 f + ∑ j : Fin d, mo_l2 ((mova1_D j)^[n] f)) ^ 2) := by
        refine Real.sqrt_le_sqrt (hsq.trans ?_)
        refine mul_le_mul_of_nonneg_left ?_ hB0
        nlinarith [mul_nonneg ha hsb]
    _ = Real.sqrt B * (mo_l2 f + ∑ j : Fin d, mo_l2 ((mova1_D j)^[n] f)) := by
        rw [Real.sqrt_mul hB0, Real.sqrt_sq (add_nonneg ha hsb)]

theorem mova1_Bnd_Diter (j : Fin d) : ∀ n : ℕ, mova1_Bnd n (fun f : 𝒮 => (mova1_D j)^[n] f) := by
  intro n
  induction n with
  | zero => exact mova1_Bnd_congr rfl (fun f => by simp) mova1_Bnd_id
  | succ n ih =>
    have h1 := mova1_Bnd_comp (mova1_Bnd_D j) ih
    exact mova1_Bnd_congr (by omega) (fun f => by simp [Function.iterate_succ_apply']) h1

theorem mova1_l2_le {n : ℕ} {T : 𝒮 → 𝒮} (hT : mova1_Bnd n T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝒮, mo_l2 (T f) ≤ C * oscNorm n f := by
  obtain ⟨C, hC, h⟩ := hT 0
  refine ⟨C, hC, fun f => ?_⟩
  have h0 := oscNorm_zero (⇑(T f)) ((T f).memLp 2)
  have := h f
  rw [zero_add] at this
  unfold mo_l2
  rw [← h0]
  exact this

/-- **`mo_sobolev_emb`.**  For `i + d/2 < n`, the `i`-th derivative of a Schwartz function is bounded
pointwise by its `Σ^n` norm. -/
theorem mo_sobolev_emb (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SchwartzMap (Euc d) ℝ) (x : Euc d),
      ‖iteratedFDeriv ℝ i f x‖ ≤ C * oscNorm n f := by
  obtain ⟨C₁, hC₁, h₁⟩ := HRS.MP.RdGen.rg_sobolev_embedding (d := d) i hn
  have hj : ∀ j : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝒮, mo_l2 ((mova1_D j)^[n] f) ≤ C * oscNorm n f :=
    fun j => mova1_l2_le (mova1_Bnd_Diter j n)
  choose Cj hCj0 hCj using hj
  set B : ℝ := ((d : ℝ) + 1) ^ n with hB
  refine ⟨C₁ * Real.sqrt B * (1 + ∑ j, Cj j), by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hCj0 j
    positivity, fun f x => ?_⟩
  have hmem := mova1_sobolev_bound n f
  have h2 := h₁ (⇑f) (f.smooth ⊤) hmem.1 x
  have h0 : mo_l2 f ≤ oscNorm n f := by
    have := oscNorm_zero (⇑f) (f.memLp 2)
    unfold mo_l2
    rw [← this]
    have hm := (mo_mono (r := 0) (r' := (n : ℝ)) (by exact_mod_cast Nat.zero_le n)
      (memOsc_schwartz (n : ℝ) f)).2
    exact hm
  have hsum : ∑ j : Fin d, mo_l2 ((mova1_D j)^[n] f) ≤ (∑ j, Cj j) * oscNorm n f := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hCj j f
  calc ‖iteratedFDeriv ℝ i f x‖ ≤ C₁ * HRS.Whole.sobolevNorm (n : ℝ) (⇑f) := h2
    _ ≤ C₁ * (Real.sqrt B * (mo_l2 f + ∑ j : Fin d, mo_l2 ((mova1_D j)^[n] f))) :=
        mul_le_mul_of_nonneg_left hmem.2 hC₁
    _ ≤ C₁ * (Real.sqrt B * (oscNorm n f + (∑ j, Cj j) * oscNorm n f)) := by
        gcongr
    _ = C₁ * Real.sqrt B * (1 + ∑ j, Cj j) * oscNorm n f := by ring

end HRS.MS.MovOsc
