import HRS.MS.ThCorrSAux1
import HRS.MS.SobMul

/-!
# TC-S, part 3: the real-order multiplier `W^{N,1}` (statement S1)

Namespace `HRS.MS.TcS`.  Fourier convention `û(ξ) = ∫ e^{-2πi⟨x,ξ⟩} u(x) dx`, `wt ξ = 1 + 4π²|ξ|²`.

* `tcs_fourier_pointwise`: for `g ∈ C^N(ℝ^d; ℂ)` with `D^k g ∈ L¹` (`k ≤ N`) and `S = ∑_{k ≤ N} ∫‖D^k g‖`:
  `wt(w)^{t/2} ‖ĝ(w)‖ ≤ √((2(d+1))^N) · S · wt(w)^{-(N-t)/2}`.
* `tcs_sobmul_T`: the estimate of `SobMul.sobmul_bound` with the explicit constant
  `2^{t/2} ∫ wt^{t/2} |T̂|` (any Schwartz `T` equal to a real function `θ`).
* `tcs_mul_schwartz` (S1): `‖ρ u‖²_{H^t} ≤ (C · ∑_{j ≤ N} ∫‖D^jρ‖)² ‖u‖²_{H^t}` for `ρ ∈ C^∞` with
  `D^jρ ∈ L¹`, real `t ≥ 0`, integer `N > t + d`; `C = C(d, t, N)`.  Proof: `ρ_n = ρ · ψ(·/(n+1))` is
  `C_c^∞`; the estimate for `ρ_n` is uniform in `n`; `ρ_n u → ρ u` in `L²` and Fatou on the Fourier side.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.TcS
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MP.RdGen HRS.MS.QMul

variable {d : ℕ}

/-! ### Fourier decay from integrable derivatives -/

theorem tcs_norm_fourier_le (h : Euc d → ℂ) (w : Euc d) : ‖𝓕 h w‖ ≤ ∫ v, ‖h v‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext v
  exact Circle.norm_smul _ _

theorem tcs_fourier_decay {N : ℕ} {g : Euc d → ℂ} (hg : ContDiff ℝ N g)
    (hint : ∀ k ≤ N, Integrable (iteratedFDeriv ℝ k g) volume) (w : Euc d) :
    wt w ^ N * ‖𝓕 g w‖ ^ 2 ≤
      (2 * ((d : ℝ) + 1)) ^ N * (∑ k ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ k g x‖) ^ 2 := by
  set I : ℕ → ℝ := fun k => ∫ x, ‖iteratedFDeriv ℝ k g x‖ with hI
  have hI0 : ∀ k, 0 ≤ I k := fun k => integral_nonneg fun x => norm_nonneg _
  have hn : ∀ n ≤ N, (4 * Real.pi ^ 2 * ‖w‖ ^ 2) ^ n * ‖𝓕 g w‖ ^ 2 ≤ (d : ℝ) ^ n * I n ^ 2 := by
    intro n hn
    have e1 : ∑ i : Fin n → Fin d, ‖𝓕 (qm_pd i g) w‖ ^ 2 =
        (4 * Real.pi ^ 2 * ‖w‖ ^ 2) ^ n * ‖𝓕 g w‖ ^ 2 := by
      calc ∑ i : Fin n → Fin d, ‖𝓕 (qm_pd i g) w‖ ^ 2
          = ∑ i : Fin n → Fin d, ((2 * Real.pi) ^ n * ∏ t, |w (i t)|) ^ 2 * ‖𝓕 g w‖ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [qm_fourier_pd_norm hg hint hn i w]
            ring
        _ = _ := by rw [← Finset.sum_mul, qm_sum_sq]
    rw [← e1]
    have e2 : ∀ i : Fin n → Fin d, ‖𝓕 (qm_pd i g) w‖ ^ 2 ≤ I n ^ 2 := by
      intro i
      refine pow_le_pow_left₀ (norm_nonneg _) ((tcs_norm_fourier_le _ w).trans ?_) 2
      refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
        (hint n hn).norm (Eventually.of_forall fun x => qm_norm_pd_le i g x)
    calc ∑ i : Fin n → Fin d, ‖𝓕 (qm_pd i g) w‖ ^ 2 ≤ ∑ _i : Fin n → Fin d, I n ^ 2 :=
          Finset.sum_le_sum fun i _ => e2 i
      _ = (d : ℝ) ^ n * I n ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have h1 := qm_wt_pow_le (d := d) N w
  calc wt w ^ N * ‖𝓕 g w‖ ^ 2
      ≤ (2 ^ N * ∑ n ∈ Finset.range (N + 1), (4 * Real.pi ^ 2 * ‖w‖ ^ 2) ^ n) * ‖𝓕 g w‖ ^ 2 := by
        gcongr
    _ = 2 ^ N * ∑ n ∈ Finset.range (N + 1), (4 * Real.pi ^ 2 * ‖w‖ ^ 2) ^ n * ‖𝓕 g w‖ ^ 2 := by
        rw [mul_assoc, Finset.sum_mul]
    _ ≤ 2 ^ N * ∑ n ∈ Finset.range (N + 1), ((d : ℝ) + 1) ^ N * I n ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hnr => ?_) (by positivity)
        have hn' : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hnr)
        refine (hn n hn').trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        calc (d : ℝ) ^ n ≤ ((d : ℝ) + 1) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
          _ ≤ ((d : ℝ) + 1) ^ N := pow_le_pow_right₀ (by
              have : (0 : ℝ) ≤ d := by positivity
              linarith) hn'
    _ ≤ 2 ^ N * (((d : ℝ) + 1) ^ N * (∑ n ∈ Finset.range (N + 1), I n) ^ 2) := by
        gcongr
        rw [← Finset.mul_sum]
        gcongr
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun n _ => hI0 n
    _ = _ := by rw [mul_pow]; ring

theorem tcs_wt_rpow_le {a : ℝ} (ha : 0 ≤ a) (ξ : Euc d) :
    wt ξ ^ (-a / 2) ≤ 2 ^ (a / 2) * (1 + ‖ξ‖) ^ (-a) := by
  have hw := wt_pos (d := d) ξ
  have h1 : 0 < 1 + ‖ξ‖ := by positivity
  have h2 := rg_wt_ge (d := d) ξ
  have h3 : 0 < (1 + ‖ξ‖) ^ 2 / 2 := by positivity
  have h4 : (((1 + ‖ξ‖) ^ 2 : ℝ)) ^ (-a / 2) = (1 + ‖ξ‖) ^ (-a) := by
    rw [← Real.rpow_natCast (1 + ‖ξ‖) 2, ← Real.rpow_mul h1.le]
    congr 1
    push_cast; ring
  have h6 : ((2 : ℝ)⁻¹) ^ (-a / 2) = 2 ^ (a / 2) := by
    rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1; ring
  calc wt ξ ^ (-a / 2) ≤ ((1 + ‖ξ‖) ^ 2 / 2) ^ (-a / 2) :=
        Real.rpow_le_rpow_of_nonpos h3 h2 (by linarith)
    _ = _ := by
        rw [div_eq_mul_inv, Real.mul_rpow (sq_nonneg _) (by norm_num), h4, h6, mul_comm]


theorem tcs_integrable_wt_rpow {a : ℝ} (ha : (d : ℝ) < a) :
    Integrable (fun ξ : Euc d => wt ξ ^ (-a / 2)) volume := by
  have ha0 : 0 ≤ a := le_trans (by positivity) ha.le
  have hint : Integrable (fun ξ : Euc d => (1 + ‖ξ‖) ^ (-a)) := by
    apply integrable_one_add_norm
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    exact ha
  refine (hint.const_mul (2 ^ (a / 2))).mono' (continuous_wt_rpow _).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (wt_pos ξ).le _)]
  exact tcs_wt_rpow_le ha0 ξ

theorem tcs_fourier_pointwise {N : ℕ} (t : ℝ) {g : Euc d → ℂ} (hg : ContDiff ℝ N g)
    (hint : ∀ k ≤ N, Integrable (iteratedFDeriv ℝ k g) volume) (w : Euc d) :
    wt w ^ (t / 2) * ‖𝓕 g w‖ ≤ Real.sqrt ((2 * ((d : ℝ) + 1)) ^ N) *
      (∑ k ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ k g x‖) * wt w ^ (-((N : ℝ) - t) / 2) := by
  set S : ℝ := ∑ k ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ k g x‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => integral_nonneg fun x => norm_nonneg _
  have hdec := tcs_fourier_decay hg hint w
  have hw := wt_pos (d := d) w
  set A : ℝ := wt w ^ ((N : ℝ) / 2) * ‖𝓕 g w‖ with hA
  have hA0 : 0 ≤ A := by positivity
  have hA2 : A ^ 2 = wt w ^ N * ‖𝓕 g w‖ ^ 2 := by
    rw [hA, mul_pow, ← Real.rpow_natCast (wt w ^ ((N : ℝ) / 2)) 2, ← Real.rpow_mul hw.le,
      ← Real.rpow_natCast (wt w) N]
    congr 2
    push_cast; ring
  have hK0 : 0 ≤ (2 * ((d : ℝ) + 1)) ^ N := by positivity
  have hAle : A ≤ Real.sqrt ((2 * ((d : ℝ) + 1)) ^ N) * S := by
    refine (pow_le_pow_iff_left₀ hA0 (by positivity) (two_ne_zero)).1 ?_
    rw [hA2, mul_pow, Real.sq_sqrt hK0]
    exact hdec
  have hsplit : wt w ^ (t / 2) * ‖𝓕 g w‖ = wt w ^ (-((N : ℝ) - t) / 2) * A := by
    rw [hA, ← mul_assoc, ← Real.rpow_add hw]
    congr 2
    ring
  rw [hsplit]
  calc wt w ^ (-((N : ℝ) - t) / 2) * A
      ≤ wt w ^ (-((N : ℝ) - t) / 2) * (Real.sqrt ((2 * ((d : ℝ) + 1)) ^ N) * S) :=
        mul_le_mul_of_nonneg_left hAle (by positivity)
    _ = _ := by ring


/-! ### The multiplier estimate with explicit constant -/

theorem tcs_sobmul_T {s : ℝ} (hs : 0 ≤ s) (T : SchwartzMap (Euc d) ℂ) (θ : Euc d → ℝ)
    (hθc : Continuous θ) (hT : ∀ x, T x = ((θ x : ℝ) : ℂ)) (u : Euc d → ℝ)
    (hu : HRS.PDE.ToolboxRd.MemSobolev s u) :
    HRS.PDE.ToolboxRd.MemSobolev s (fun x => θ x * u x) ∧
      sobolevNormSq s (fun x => θ x * u x) ≤
        (2 ^ (s / 2) * ∫ x, wt x ^ (s / 2) * ‖(𝓕 T : SchwartzMap (Euc d) ℂ) x‖) ^ 2 *
          sobolevNormSq s u := by
  set a : SchwartzMap (Euc d) ℂ := 𝓕 T with hadef
  set Ir : ℝ := ∫ x, wt x ^ (s / 2) * ‖a x‖ with hIr
  have hIr0 : 0 ≤ Ir := integral_nonneg fun x =>
    mul_nonneg (Real.rpow_nonneg (wt_pos x).le _) (norm_nonneg _)
  have hIe : ∫⁻ x, ENNReal.ofReal (wt x ^ (s / 2)) * ‖a x‖ₑ = ENNReal.ofReal Ir := by
    rw [hIr, ofReal_integral_eq_lintegral_ofReal (HRS.MS.SobMul.sobmul_integrable_weight hs a)
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (Real.rpow_nonneg (wt_pos x).le _) (norm_nonneg _))]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos x).le _), ofReal_norm]
  have hp := HRS.MS.SobMul.sobmul_memLp_mul hθc hT hu.1
  have hbm := aestronglyMeasurable_fourierL2 hu.1
  have key := HRS.MS.SobMul.sobmul_stepB hs (a := a) (b := fourierL2 u) a.continuous hbm
  rw [hIe] at key
  have hSig : ∫⁻ η, ENNReal.ofReal (wt η ^ s * ‖fourierL2 u η‖ ^ 2) =
      ENNReal.ofReal (sobolevNormSq s u) := by
    have hu2 : Integrable (fun ξ : Euc d => wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2) volume := hu.2
    rw [sobolevNormSq_eq, ofReal_integral_eq_lintegral_ofReal hu2
      (Filter.Eventually.of_forall fun η => by have := wt_pos (d := d) η; positivity)]
  rw [hSig] at key
  have hSig0 : 0 ≤ sobolevNormSq s u := integral_nonneg fun η => by
    have := wt_pos (d := d) η; positivity
  have hF := HRS.MS.SobMul.sobmul_fourierL2_mul hθc hT hu.1
  have hL : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖fourierL2 (fun x => θ x * u x) ξ‖ ^ 2) ≤
      ENNReal.ofReal ((2 ^ (s / 2) * Ir) ^ 2 * sobolevNormSq s u) := by
    have e : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖fourierL2 (fun x => θ x * u x) ξ‖ ^ 2) =
        ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖∫ η, a (ξ - η) * fourierL2 u η‖ ^ 2) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hF] with ξ hξ
      rw [hξ]
    rw [e]
    refine key.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hIr0,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_pow]
    congr 1
    ring
  have hint : Integrable (fun ξ => wt ξ ^ s * ‖fourierL2 (fun x => θ x * u x) ξ‖ ^ 2) volume := by
    refine ⟨aesm_wt_mul (aestronglyMeasurable_fourierL2 hp) s, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hL ENNReal.ofReal_lt_top)
    refine le_of_eq (lintegral_congr fun ξ => ?_)
    rw [Real.enorm_eq_ofReal (by have := wt_pos (d := d) ξ; positivity)]
  refine ⟨⟨hp, hint⟩, ?_⟩
  rw [sobolevNormSq_eq]
  have h2 := hL
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun η => by have := wt_pos (d := d) η; positivity)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2


/-! ### Bounds for a compactly supported smooth multiplier -/

/-- `∑_{k ≤ N} ∫ ‖D^kθ‖`. -/
def tcs_S (N : ℕ) (θ : Euc d → ℝ) : ℝ := ∑ k ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ k θ x‖

theorem tcs_S_nonneg (N : ℕ) (θ : Euc d → ℝ) : 0 ≤ tcs_S N θ :=
  Finset.sum_nonneg fun k _ => integral_nonneg fun x => norm_nonneg _

theorem tcs_norm_iteratedFDeriv_ofReal {θ : Euc d → ℝ} (hθ : ContDiff ℝ ∞ θ) (k : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun y : Euc d => ((θ y : ℝ) : ℂ)) x‖ = ‖iteratedFDeriv ℝ k θ x‖ := by
  have := LinearIsometry.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) Complex.ofRealLI
    (hθ.contDiffAt (x := x)) (i := k) (by exact_mod_cast le_top)
  exact this

theorem tcs_T_bounds {N : ℕ} {t : ℝ} (ht : 0 ≤ t) (hN : t + d < N) {θ : Euc d → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    (∫ x, wt x ^ (t / 2) * ‖(𝓕 (HRS.MS.SobMul.sobmul_T θ hθ hc) : SchwartzMap (Euc d) ℂ) x‖) ≤
        Real.sqrt ((2 * ((d : ℝ) + 1)) ^ N) * tcs_S N θ *
          ∫ ξ : Euc d, wt ξ ^ (-((N : ℝ) - t) / 2) ∧
      ∀ x, |θ x| ≤ Real.sqrt ((2 * ((d : ℝ) + 1)) ^ N) * tcs_S N θ *
          ∫ ξ : Euc d, wt ξ ^ (-((N : ℝ) - 0) / 2) := by
  set T := HRS.MS.SobMul.sobmul_T θ hθ hc with hTdef
  have hTx : ∀ x, T x = ((θ x : ℝ) : ℂ) := fun x => rfl
  have hgC : ContDiff ℝ ∞ (fun y : Euc d => ((θ y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hθ
  have hgN : ContDiff ℝ N (fun y : Euc d => ((θ y : ℝ) : ℂ)) := hgC.of_le (by exact_mod_cast le_top)
  have hint : ∀ k ≤ N, Integrable (iteratedFDeriv ℝ k (fun y : Euc d => ((θ y : ℝ) : ℂ))) volume := by
    intro k hk
    have hcs : HasCompactSupport (fun y : Euc d => ((θ y : ℝ) : ℂ)) :=
      hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    exact (hgC.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
      (hcs.iteratedFDeriv k)
  have hSeq : (∑ k ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ k
      (fun y : Euc d => ((θ y : ℝ) : ℂ)) x‖) = tcs_S N θ := by
    unfold tcs_S
    refine Finset.sum_congr rfl fun k _ => ?_
    exact integral_congr_ae (Eventually.of_forall fun x => tcs_norm_iteratedFDeriv_ofReal hθ k x)
  have hFc : ∀ x, (𝓕 T : SchwartzMap (Euc d) ℂ) x = 𝓕 (fun y : Euc d => ((θ y : ℝ) : ℂ)) x :=
    fun x => rfl
  have hpt : ∀ (s : ℝ) (x : Euc d), wt x ^ (s / 2) * ‖(𝓕 T : SchwartzMap (Euc d) ℂ) x‖ ≤
      Real.sqrt ((2 * ((d : ℝ) + 1)) ^ N) * tcs_S N θ * wt x ^ (-((N : ℝ) - s) / 2) := by
    intro s x
    have := tcs_fourier_pointwise s hgN hint x
    rw [hSeq] at this
    rw [hFc]
    exact this
  have hWint : ∀ s : ℝ, 0 ≤ s → s ≤ t →
      Integrable (fun ξ : Euc d => wt ξ ^ (-((N : ℝ) - s) / 2)) volume := by
    intro s hs hst
    have := tcs_integrable_wt_rpow (d := d) (a := (N : ℝ) - s) (by linarith)
    exact this
  have hK0 : 0 ≤ Real.sqrt ((2 * ((d : ℝ) + 1)) ^ N) * tcs_S N θ :=
    mul_nonneg (Real.sqrt_nonneg _) (tcs_S_nonneg N θ)
  constructor
  · calc (∫ x, wt x ^ (t / 2) * ‖(𝓕 T : SchwartzMap (Euc d) ℂ) x‖)
        ≤ ∫ x, Real.sqrt ((2 * ((d : ℝ) + 1)) ^ N) * tcs_S N θ * wt x ^ (-((N : ℝ) - t) / 2) :=
          integral_mono (HRS.MS.SobMul.sobmul_integrable_weight ht _) ((hWint t ht le_rfl).const_mul _)
            (hpt t)
      _ = _ := integral_const_mul _ _
  · intro x
    have h1 : |θ x| = ‖T x‖ := by
      rw [hTx]; simp
    have h2 : T x = (𝓕 (𝓕 T : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) (-x) := by
      exact (HRS.MS.SobMul.sobmul_fourier_fourier T x).symm
    rw [h1, h2]
    refine (tcs_norm_fourier_le _ _).trans ?_
    calc (∫ v, ‖(𝓕 T : SchwartzMap (Euc d) ℂ) v‖)
        ≤ ∫ v, Real.sqrt ((2 * ((d : ℝ) + 1)) ^ N) * tcs_S N θ * wt v ^ (-((N : ℝ) - 0) / 2) := by
          refine integral_mono (𝓕 T : SchwartzMap (Euc d) ℂ).integrable.norm
            ((hWint 0 le_rfl ht).const_mul _) fun v => ?_
          have := hpt 0 v
          simpa using this
      _ = _ := integral_const_mul _ _


/-! ### The cutoff family -/

/-- a fixed bump: `1` on the unit ball, supported in the ball of radius `2` -/
def tcs_psi (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `θ_n(x) = ψ(x/(n+1))` -/
def tcs_theta (n : ℕ) (x : Euc d) : ℝ := tcs_psi d (((n : ℝ) + 1)⁻¹ • x)

theorem tcs_theta_contDiff (n : ℕ) : ContDiff ℝ ∞ (tcs_theta (d := d) n) :=
  (tcs_psi d).contDiff.comp (contDiff_const_smul _)

theorem tcs_theta_one (n : ℕ) {x : Euc d} (hx : ‖x‖ ≤ (n : ℝ) + 1) : tcs_theta n x = 1 := by
  unfold tcs_theta
  apply ContDiffBump.one_of_mem_closedBall
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
  show _ ≤ (1 : ℝ)
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith

theorem tcs_theta_mem (n : ℕ) (x : Euc d) : 0 ≤ tcs_theta n x ∧ tcs_theta n x ≤ 1 :=
  ⟨(tcs_psi d).nonneg, (tcs_psi d).le_one⟩

theorem tcs_theta_compact (n : ℕ) : HasCompactSupport (tcs_theta (d := d) n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (2 * ((n : ℝ) + 1))) ?_
  intro x hx
  unfold tcs_theta
  apply ContDiffBump.zero_of_le_dist
  rw [mem_closedBall_zero_iff, not_le] at hx
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
  show (2 : ℝ) ≤ _
  rw [le_inv_mul_iff₀ (by positivity)]
  linarith

theorem tcs_theta_deriv (d N : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (i : ℕ), i ≤ N → ∀ x : Euc d,
    ‖iteratedFDeriv ℝ i (tcs_theta n) x‖ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := (tcs_psi d).hasCompactSupport.exists_bound_iteratedFDeriv
    (tcs_psi d).contDiff N
  refine ⟨M, hM0, fun n i hi x => ?_⟩
  set c : ℝ := ((n : ℝ) + 1)⁻¹ with hc
  set g : Euc d →L[ℝ] Euc d := c • ContinuousLinearMap.id ℝ (Euc d) with hg
  have hfun : tcs_theta (d := d) n = (tcs_psi d) ∘ ⇑g := by
    funext y; simp [tcs_theta, hg, hc]
  have hgn : ‖g‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_smul_le c _).trans ?_
    have h1 : ‖c‖ ≤ 1 := by
      rw [hc, norm_inv, Real.norm_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have h2 : ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    calc ‖c‖ * ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [hfun, g.iteratedFDeriv_comp_right (tcs_psi d).contDiff x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _t : Fin i, ‖g‖ ≤ 1 := by
    rw [Finset.prod_const]; exact pow_le_one₀ (norm_nonneg _) hgn
  calc ‖iteratedFDeriv ℝ i (⇑(tcs_psi d)) (g x)‖ * ∏ _t : Fin i, ‖g‖
      ≤ M * 1 := mul_le_mul (hM i hi _) h1 (Finset.prod_nonneg fun _ _ => norm_nonneg _) hM0
    _ = M := mul_one M


theorem tcs_cutoff_S {N : ℕ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ (n i : ℕ), i ≤ N → ∀ x : Euc d, ‖iteratedFDeriv ℝ i (tcs_theta n) x‖ ≤ M)
    {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hint : ∀ j ≤ N, Integrable (fun x => ‖iteratedFDeriv ℝ j ρ x‖) volume) (n : ℕ) :
    tcs_S N (fun x => tcs_theta n x * ρ x) ≤ (((N : ℝ) + 1) ^ 2 * 2 ^ N * M) * tcs_S N ρ := by
  set S : ℝ := tcs_S N ρ with hS
  have hS0 : 0 ≤ S := tcs_S_nonneg N ρ
  have hρn : ContDiff ℝ ∞ (fun x => tcs_theta n x * ρ x) := (tcs_theta_contDiff n).mul hρ
  have hcs : HasCompactSupport (fun x => tcs_theta n x * ρ x) := (tcs_theta_compact n).mul_right
  have hI : ∀ j ≤ N, ∫ x, ‖iteratedFDeriv ℝ j ρ x‖ ≤ S := fun j hj =>
    Finset.single_le_sum (f := fun k => ∫ x, ‖iteratedFDeriv ℝ k ρ x‖)
      (fun k _ => integral_nonneg fun x => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hk : ∀ k ≤ N, ∫ x, ‖iteratedFDeriv ℝ k (fun x => tcs_theta n x * ρ x) x‖ ≤
      ((k : ℝ) + 1) * 2 ^ k * M * S := by
    intro k hk
    have hB : Integrable (fun x => ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * M * ‖iteratedFDeriv ℝ (k - i) ρ x‖) volume :=
      integrable_finset_sum _ fun i hi =>
        (hint (k - i) (le_trans (Nat.sub_le _ _) hk)).const_mul _
    calc ∫ x, ‖iteratedFDeriv ℝ k (fun x => tcs_theta n x * ρ x) x‖
        ≤ ∫ x, ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * M * ‖iteratedFDeriv ℝ (k - i) ρ x‖ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hB
            (Eventually.of_forall fun x => ?_)
          refine (norm_iteratedFDeriv_mul_le (tcs_theta_contDiff n) hρ x
            (by exact_mod_cast le_top)).trans ?_
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          have h1 := hM n i (hi'.trans hk) x
          have h2 : 0 ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
          have h4 : (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (tcs_theta n) x‖ *
                ‖iteratedFDeriv ℝ (k - i) ρ x‖
              ≤ (k.choose i : ℝ) * M * ‖iteratedFDeriv ℝ (k - i) ρ x‖ := by gcongr
          exact h4
      _ = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * M * ∫ x, ‖iteratedFDeriv ℝ (k - i) ρ x‖ := by
          rw [integral_finset_sum _ fun i hi => (hint (k - i) (le_trans (Nat.sub_le _ _) hk)).const_mul _]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      _ ≤ ∑ _i ∈ Finset.range (k + 1), 2 ^ k * M * S := by
          refine Finset.sum_le_sum fun i hi => ?_
          have h1 : (k.choose i : ℝ) ≤ 2 ^ k := by exact_mod_cast Nat.choose_le_two_pow k i
          have h2 := hI (k - i) (le_trans (Nat.sub_le _ _) hk)
          have h3 : 0 ≤ ∫ x, ‖iteratedFDeriv ℝ (k - i) ρ x‖ := integral_nonneg fun x => norm_nonneg _
          have h4 : (k.choose i : ℝ) * M * ∫ x, ‖iteratedFDeriv ℝ (k - i) ρ x‖ ≤ 2 ^ k * M * S := by
            gcongr
          exact h4
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
  unfold tcs_S
  calc ∑ k ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ k (fun x => tcs_theta n x * ρ x) x‖
      ≤ ∑ k ∈ Finset.range (N + 1), ((N : ℝ) + 1) * 2 ^ N * M * S := by
        refine Finset.sum_le_sum fun k hkr => ?_
        have hk' : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hkr)
        refine (hk k hk').trans ?_
        have h1 : ((k : ℝ) + 1) ≤ (N : ℝ) + 1 := by
          have : (k : ℝ) ≤ N := by exact_mod_cast hk'
          linarith
        have h2 : (2 : ℝ) ^ k ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hk'
        have h3 : 0 ≤ M * S := mul_nonneg hM0 hS0
        calc ((k : ℝ) + 1) * 2 ^ k * M * S = (((k : ℝ) + 1) * 2 ^ k) * (M * S) := by ring
          _ ≤ (((N : ℝ) + 1) * 2 ^ N) * (M * S) := by gcongr
          _ = _ := by ring
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring


/-! ### Fatou on the Fourier side, real exponent -/

theorem tcs_fatou (t : ℝ) {G : Euc d → ℂ} {Gn : ℕ → Euc d → ℂ} (hG : MemLp G 2 volume)
    (hGn : ∀ n, MemLp (Gn n) 2 volume)
    (hconv : Tendsto (fun n => ∫⁻ ξ, ‖Gn n ξ - G ξ‖ₑ ^ 2) atTop (𝓝 0))
    {B : ℝ≥0∞} (hB : ∀ n, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ t * ‖Gn n ξ‖ ^ 2) ≤ B) :
    ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ t * ‖G ξ‖ ^ 2) ≤ B := by
  have hconv' : Tendsto (fun n => eLpNorm (Gn n - G) 2 volume) atTop (𝓝 0) := by
    have e : ∀ n, eLpNorm (Gn n - G) 2 volume = (∫⁻ ξ, ‖Gn n ξ - G ξ‖ₑ ^ 2) ^ ((1 : ℝ) / 2) :=
      fun n => qm_eLpNorm_eq _ ((hGn n).sub hG)
    simp_rw [e]
    have := ((ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto 0).comp hconv
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    exact this
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (μ := volume) (f := Gn) (g := G)
    (by norm_num) hconv'
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  set F : ℕ → Euc d → ℝ≥0∞ := fun i ξ => ENNReal.ofReal (wt ξ ^ t * ‖Gn (ns i) ξ‖ ^ 2) with hF
  have hFm : ∀ i, AEMeasurable (F i) volume := by
    intro i
    have : AEStronglyMeasurable (fun ξ => wt ξ ^ t * ‖Gn (ns i) ξ‖ ^ 2) volume :=
      (continuous_wt_rpow t).aestronglyMeasurable.mul (((hGn (ns i)).aestronglyMeasurable.norm).pow 2)
    exact this.aemeasurable.ennreal_ofReal
  have hlim : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      Tendsto (fun i => F i ξ) atTop (𝓝 (ENNReal.ofReal (wt ξ ^ t * ‖G ξ‖ ^ 2))) := by
    filter_upwards [hae] with ξ hξ
    have h1 : Tendsto (fun i => wt ξ ^ t * ‖Gn (ns i) ξ‖ ^ 2) atTop (𝓝 (wt ξ ^ t * ‖G ξ‖ ^ 2)) :=
      (hξ.norm.pow 2).const_mul _
    exact (ENNReal.continuous_ofReal.tendsto _).comp h1
  have h1 : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ t * ‖G ξ‖ ^ 2) =
      ∫⁻ ξ, liminf (fun i => F i ξ) atTop := by
    refine lintegral_congr_ae ?_
    filter_upwards [hlim] with ξ hξ
    exact hξ.liminf_eq.symm
  rw [h1]
  refine (lintegral_liminf_le' hFm).trans ?_
  calc liminf (fun i => ∫⁻ ξ, F i ξ) atTop ≤ liminf (fun _ : ℕ => B) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i => hB (ns i))
    _ = B := by simp


/-! ### The main theorem (S1) -/

theorem tcs_mul_schwartz (d N : ℕ) (t : ℝ) (ht : 0 ≤ t) (hN : t + d < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, ContDiff ℝ ∞ ρ →
      (∀ j ≤ N, Integrable (fun x => ‖iteratedFDeriv ℝ j ρ x‖) volume) →
      ∀ u : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev t u →
        HRS.PDE.ToolboxRd.MemSobolev t (fun x => ρ x * u x) ∧
          sobolevNormSq t (fun x => ρ x * u x) ≤
            (C * ∑ j ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ j ρ x‖) ^ 2 *
              sobolevNormSq t u := by
  obtain ⟨M, hM0, hM⟩ := tcs_theta_deriv d N
  set K0 : ℝ := Real.sqrt ((2 * ((d : ℝ) + 1)) ^ N) with hK0
  set Wt : ℝ := ∫ ξ : Euc d, wt ξ ^ (-((N : ℝ) - t) / 2) with hWt
  set Wt0 : ℝ := ∫ ξ : Euc d, wt ξ ^ (-((N : ℝ) - 0) / 2) with hWt0
  have hWt_nn : 0 ≤ Wt := integral_nonneg fun ξ => Real.rpow_nonneg (wt_pos ξ).le _
  have hWt0_nn : 0 ≤ Wt0 := integral_nonneg fun ξ => Real.rpow_nonneg (wt_pos ξ).le _
  have hK0_nn : 0 ≤ K0 := Real.sqrt_nonneg _
  set c2 : ℝ := ((N : ℝ) + 1) ^ 2 * 2 ^ N * M with hc2
  have hc2_nn : 0 ≤ c2 := by positivity
  set C : ℝ := 2 ^ (t / 2) * K0 * c2 * Wt with hC
  have hC_nn : 0 ≤ C := by positivity
  refine ⟨C, hC_nn, fun ρ hρ hint u hu => ?_⟩
  set S : ℝ := tcs_S N ρ with hS
  have hS0 : 0 ≤ S := tcs_S_nonneg N ρ
  have hSsum : (∑ j ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ j ρ x‖) = S := rfl
  rw [hSsum]
  set ρn : ℕ → Euc d → ℝ := fun n x => tcs_theta n x * ρ x with hρn_def
  have hρn : ∀ n, ContDiff ℝ ∞ (ρn n) := fun n => (tcs_theta_contDiff n).mul hρ
  have hcn : ∀ n, HasCompactSupport (ρn n) := fun n => (tcs_theta_compact n).mul_right
  have hSn : ∀ n, tcs_S N (ρn n) ≤ c2 * S := fun n => tcs_cutoff_S hM0 hM hρ hint n
  have hb := fun n => tcs_T_bounds ht hN (hρn n) (hcn n)
  have hsup : ∀ n x, |ρn n x| ≤ K0 * (c2 * S) * Wt0 := by
    intro n x
    refine ((hb n).2 x).trans ?_
    have : K0 * tcs_S N (ρn n) ≤ K0 * (c2 * S) := mul_le_mul_of_nonneg_left (hSn n) hK0_nn
    exact mul_le_mul_of_nonneg_right this hWt0_nn
  set Mρ : ℝ := K0 * (c2 * S) * Wt0 with hMρ
  have hMρ0 : 0 ≤ Mρ := by positivity
  -- the uniform estimate for the cutoffs
  have hstep : ∀ n, HRS.PDE.ToolboxRd.MemSobolev t (fun x => ρn n x * u x) ∧
      sobolevNormSq t (fun x => ρn n x * u x) ≤ (C * S) ^ 2 * sobolevNormSq t u := by
    intro n
    obtain ⟨h1, h2⟩ := tcs_sobmul_T ht (HRS.MS.SobMul.sobmul_T (ρn n) (hρn n) (hcn n)) (ρn n)
      (hρn n).continuous (fun x => rfl) u hu
    refine ⟨h1, h2.trans ?_⟩
    have hIr0 : 0 ≤ ∫ x, wt x ^ (t / 2) *
        ‖(𝓕 (HRS.MS.SobMul.sobmul_T (ρn n) (hρn n) (hcn n)) : SchwartzMap (Euc d) ℂ) x‖ :=
      integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (wt_pos x).le _) (norm_nonneg _)
    have h3 : 2 ^ (t / 2) * (∫ x, wt x ^ (t / 2) *
        ‖(𝓕 (HRS.MS.SobMul.sobmul_T (ρn n) (hρn n) (hcn n)) : SchwartzMap (Euc d) ℂ) x‖) ≤ C * S := by
      refine (mul_le_mul_of_nonneg_left (hb n).1 (by positivity)).trans ?_
      have : K0 * tcs_S N (ρn n) ≤ K0 * (c2 * S) := mul_le_mul_of_nonneg_left (hSn n) hK0_nn
      calc 2 ^ (t / 2) * (K0 * tcs_S N (ρn n) * Wt)
          ≤ 2 ^ (t / 2) * (K0 * (c2 * S) * Wt) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hWt_nn) (by positivity)
        _ = C * S := by rw [hC]; ring
    have hnn : 0 ≤ sobolevNormSq t u := integral_nonneg fun η => by
      have := wt_pos (d := d) η; positivity
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h3 2) hnn
  -- `ρ` is bounded
  have hρeq : ∀ x, ρ x = ρn ⌈‖x‖⌉₊ x := by
    intro x
    have hx : ‖x‖ ≤ ((⌈‖x‖⌉₊ : ℕ) : ℝ) + 1 := by
      have := Nat.le_ceil ‖x‖
      linarith
    simp only [hρn_def, tcs_theta_one _ hx, one_mul]
  have hρb : ∀ x, |ρ x| ≤ Mρ := fun x => by rw [hρeq x]; exact hsup _ x
  have hρu : MemLp (fun x => ρ x * u x) 2 volume := by
    refine hu.1.of_le_mul (c := Mρ) (hρ.continuous.aestronglyMeasurable.mul
      hu.1.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using hρb x) (norm_nonneg _)
  have hpn : ∀ n, MemLp (fun x => ρn n x * u x) 2 volume := fun n => (hstep n).1.1
  -- `L²` convergence
  have hlim : Tendsto (fun n => ∫ x, (ρn n x * u x - ρ x * u x) ^ 2) atTop (𝓝 0) := by
    have hdom := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (Euc d)))
      (F := fun n x => (ρn n x * u x - ρ x * u x) ^ 2) (f := fun _ => (0 : ℝ))
      (bound := fun x => Mρ ^ 2 * u x ^ 2)
      (fun n => ((hpn n).sub hρu).integrable_sq.aestronglyMeasurable)
      (hu.1.integrable_sq.const_mul _) ?_ ?_
    · simpa using hdom
    · intro n
      refine Eventually.of_forall fun x => ?_
      have h1 : (ρn n x * u x - ρ x * u x) = (tcs_theta n x - 1) * (ρ x * u x) := by
        simp only [hρn_def]; ring
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), h1, mul_pow, mul_pow]
      have h2 : (tcs_theta n x - 1) ^ 2 ≤ 1 := by
        have := tcs_theta_mem n x
        nlinarith [this.1, this.2]
      have h3 : ρ x ^ 2 ≤ Mρ ^ 2 := by
        have := hρb x
        nlinarith [abs_nonneg (ρ x), sq_abs (ρ x)]
      calc (tcs_theta n x - 1) ^ 2 * (ρ x ^ 2 * u x ^ 2) ≤ 1 * (Mρ ^ 2 * u x ^ 2) := by
            gcongr
        _ = _ := one_mul _
    · refine Eventually.of_forall fun x => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
      have hx : ‖x‖ ≤ (n : ℝ) + 1 := by
        have h1 := Nat.le_ceil ‖x‖
        have h2 : ((⌈‖x‖⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp only [hρn_def, tcs_theta_one _ hx, one_mul, sub_self]
      ring
  have hconv : Tendsto (fun n => ∫⁻ ξ, ‖fourierL2 (fun x => ρn n x * u x) ξ -
      fourierL2 (fun x => ρ x * u x) ξ‖ₑ ^ 2) atTop (𝓝 0) := by
    have heq : ∀ n, ∫⁻ ξ, ‖fourierL2 (fun x => ρn n x * u x) ξ -
        fourierL2 (fun x => ρ x * u x) ξ‖ₑ ^ 2 =
        ENNReal.ofReal (∫ x, (ρn n x * u x - ρ x * u x) ^ 2) := by
      intro n
      have hd := fourierL2_sub (hpn n) hρu
      have e1 : ∫⁻ ξ, ‖fourierL2 (fun x => ρn n x * u x) ξ - fourierL2 (fun x => ρ x * u x) ξ‖ₑ ^ 2 =
          ∫⁻ ξ, ‖fourierL2 (fun x => ρn n x * u x - ρ x * u x) ξ‖ₑ ^ 2 := by
        refine lintegral_congr_ae ?_
        filter_upwards [hd] with ξ hξ
        rw [hξ]
      rw [e1]
      have hmp : MemLp (fun x => ρn n x * u x - ρ x * u x) 2 volume := (hpn n).sub hρu
      have e2 : ∫⁻ ξ, ‖fourierL2 (fun x => ρn n x * u x - ρ x * u x) ξ‖ₑ ^ 2 =
          ∫⁻ ξ, ENNReal.ofReal (‖fourierL2 (fun x => ρn n x * u x - ρ x * u x) ξ‖ ^ 2) := by
        refine lintegral_congr fun ξ => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rw [e2, ← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_fourierL2 hmp)
        (Eventually.of_forall fun ξ => sq_nonneg _), integral_norm_sq_fourierL2 hmp]
    simp_rw [heq]
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hlim
    rw [ENNReal.ofReal_zero] at this
    exact this
  -- Fatou on the Fourier side
  have hB : ∀ n, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ t * ‖fourierL2 (fun x => ρn n x * u x) ξ‖ ^ 2) ≤
      ENNReal.ofReal ((C * S) ^ 2 * sobolevNormSq t u) := by
    intro n
    have hI : Integrable (fun ξ : Euc d => wt ξ ^ t * ‖fourierL2 (fun x => ρn n x * u x) ξ‖ ^ 2)
        volume := (hstep n).1.2
    rw [← ofReal_integral_eq_lintegral_ofReal hI
      (Eventually.of_forall fun η => by have := wt_pos (d := d) η; positivity)]
    exact ENNReal.ofReal_le_ofReal ((sobolevNormSq_eq t _).symm ▸ (hstep n).2)
  have hfat := tcs_fatou t (memLp_fourierL2 hρu) (fun n => memLp_fourierL2 (hpn n)) hconv hB
  have hint2 : Integrable (fun ξ => wt ξ ^ t * ‖fourierL2 (fun x => ρ x * u x) ξ‖ ^ 2) volume := by
    refine ⟨aesm_wt_mul (aestronglyMeasurable_fourierL2 hρu) t, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hfat ENNReal.ofReal_lt_top)
    refine le_of_eq (lintegral_congr fun ξ => ?_)
    rw [Real.enorm_eq_ofReal (by have := wt_pos (d := d) ξ; positivity)]
  refine ⟨⟨hρu, hint2⟩, ?_⟩
  rw [sobolevNormSq_eq]
  have hnn : 0 ≤ sobolevNormSq t u := integral_nonneg fun η => by
    have := wt_pos (d := d) η; positivity
  have h2 := hfat
  rw [← ofReal_integral_eq_lintegral_ofReal hint2
    (Eventually.of_forall fun η => by have := wt_pos (d := d) η; positivity)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end HRS.MS.TcS
