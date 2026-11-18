import HRS.Main.MeanPartShift
import HRS.Sections.IIDAux14
import HRS.Sections.Sec5

/-!
# MEANPART (shift, part B): L8 `mp_det_shift`, `mp_delta_early`

(packet `mpshift`, plan `docs/MAIN_A_PLAN_mean_particles.md`, section 4.)

The deterministic shift `Dp_n = √N (μ^{u_n + ·} - dx)` converges in `𝒳_{m,T}`:
* critical case: to `d∞ (t) = A e^{-λ(τ+t)} ψ_k` (as an element of `E_m`),
* late case: to `0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

section OfSeqNorm

variable {m : ℝ}

/-- The norm constant `√2 · (∑_{k≠0} ⟨k⟩^{-2m})^{1/2}` of `E_m`. -/
def mp_Km (d : ℕ) (m : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)))

theorem mp_Km_nonneg (m : ℝ) : 0 ≤ mp_Km d m :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem mp_norm_ofSeq_le (hm2 : (d : ℝ) < 2 * m) (c : NonzeroLattice d → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀ k, |c k| ≤ C) :
    ‖NegSobolev.ofSeq m c‖ ≤
      C * Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) := by
  have hmem := NegSobolev.memℓp_of_bounded hm2 c ⟨C, hc⟩
  have hs := summable_jp_rpow (d := d) m hm2
  obtain ⟨h2, hn⟩ := NegSobolev.coord_sq (NegSobolev.ofSeq m c)
  have hco : ∀ k, NegSobolev.coord (NegSobolev.ofSeq m c) k = Lattice.jp k.1 ^ (-m) * c k :=
    NegSobolev.coord_ofSeq_of_mem c hmem
  have hle : ∑' k, NegSobolev.coord (NegSobolev.ofSeq m c) k ^ 2 ≤
      C ^ 2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) := by
    rw [← tsum_mul_left]
    refine h2.tsum_le_tsum (fun k => ?_) (hs.mul_left _)
    rw [hco, mul_pow, Torus.jp_rpow_sq, show 2 * (-m) = -(2 * m) by ring, mul_comm (C ^ 2)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Torus.jp_pos k.1).le _)
    rw [← sq_abs (c k)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hc k) 2
  calc ‖NegSobolev.ofSeq m c‖ = Real.sqrt (‖NegSobolev.ofSeq m c‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (C ^ 2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) := by
        rw [hn]; exact Real.sqrt_le_sqrt hle
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC]

/-- A bounded function has `E_m`-norm at most `B · K_m`. -/
theorem mp_norm_ofFun_le (hm2 : (d : ℝ) < 2 * m) {g : Torus d → ℝ} {B : ℝ}
    (hB : ∀ x, |g x| ≤ B) : ‖NegSobolev.ofFun m g‖ ≤ B * mp_Km d m := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have h := mp_norm_ofSeq_le hm2 (Torus.funRealCoeff g) (C := Real.sqrt 2 * B)
    (mul_nonneg (Real.sqrt_nonneg _) hB0) (fun k => ?_)
  · unfold NegSobolev.ofFun mp_Km
    calc _ ≤ _ := h
      _ = _ := by ring
  · have h1 := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d)))
      (f := fun x => Torus.realMode k x * g x) (C := Real.sqrt 2 * B)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (Torus.abs_realMode_le k x) (hB x) (abs_nonneg _) (Real.sqrt_nonneg _))
    unfold Torus.funRealCoeff
    rw [Real.norm_eq_abs] at h1
    simpa using h1

theorem mp_integrable_realMode_mul {f : Torus d → ℝ} (hf : Integrable f) (k : NonzeroLattice d) :
    Integrable (fun x => Torus.realMode k x * f x) :=
  hf.bdd_mul (c := Real.sqrt 2) (Torus.continuous_realMode k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa using Torus.abs_realMode_le k x)

/-- Linearity of `ofFun`. -/
theorem mp_ofFun_sub_smul (hm2 : (d : ℝ) < 2 * m) {f ψ : Torus d → ℝ} (hf : Integrable f)
    (hψ : Integrable ψ) (b : ℝ) :
    NegSobolev.ofFun m f - b • NegSobolev.ofFun m ψ =
      NegSobolev.ofFun m (fun x => f x - b * ψ x) := by
  have hg : Integrable (fun x => f x - b * ψ x) := hf.sub (hψ.const_mul b)
  refine lp.ext (funext fun k => ?_)
  show NegSobolev.coord (NegSobolev.ofFun m f - b • NegSobolev.ofFun m ψ) k =
    NegSobolev.coord (NegSobolev.ofFun m fun x => f x - b * ψ x) k
  have e : NegSobolev.coord (NegSobolev.ofFun m f - b • NegSobolev.ofFun m ψ) k =
      NegSobolev.coord (NegSobolev.ofFun m f) k - b * NegSobolev.coord (NegSobolev.ofFun m ψ) k :=
    rfl
  rw [e, IID.coord_ofFun hm2 hf, IID.coord_ofFun hm2 hψ, IID.coord_ofFun hm2 hg]
  unfold Torus.funRealCoeff
  have : ∫ x, Torus.realMode k x * (f x - b * ψ x) =
      (∫ x, Torus.realMode k x * f x) - b * ∫ x, Torus.realMode k x * ψ x := by
    rw [← integral_const_mul, ← integral_sub (mp_integrable_realMode_mul hf k)
      ((mp_integrable_realMode_mul hψ k).const_mul b)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [this]
  ring

end OfSeqNorm

/-! ### The deterministic shift -/

/-- `(Dp_n) t = ofFun m (σ (ρ^{a+t} - 1))`. -/
theorem mp_Dp_apply (S : PreparedData d) {m : ℝ} (hm2 : (d : ℝ) < 2 * m) (T a : ℝ) (ha : 0 ≤ a)
    (σ : ℝ) (t : Set.Icc (0 : ℝ) T) :
    PathSpace.at' (mp_Dp S hm2 T a ha σ) t =
      NegSobolev.ofFun m (fun x => σ * (S.ρ (a + t) x - 1)) := by
  have hq := therm_density S (show 0 ≤ a + (t : ℝ) by linarith [t.2.1])
  have h := IID.sqrtN_ofMeasureDiff (m := m) hm2 (c0 := σ) hq (mp_isProbDensity_one (d := d))
    (f := fun x => σ * (S.ρ (a + t) x - 1))
    (((IID.integrable_of_pd hq).sub (integrable_const (1 : ℝ))).const_mul σ)
    (fun x => rfl)
  exact h

/-- Core estimate: if `σ(ρ^{a+t} - 1) - b(t) ψ` is uniformly bounded by `η` on `[0,T]`, then
`Dp` is `η K_m`-close to the path `t ↦ b(t) ofFun ψ`. -/
theorem mp_Dp_sub_le (S : PreparedData d) {m : ℝ} (hm2 : (d : ℝ) < 2 * m) (T a : ℝ) (ha : 0 ≤ a)
    (σ : ℝ) {ψ : Torus d → ℝ} (hψc : Continuous ψ) (b : ℝ → ℝ) (Φ : PathSpace d m T)
    (hΦ : ∀ t : Set.Icc (0 : ℝ) T, PathSpace.at' Φ t = b t • NegSobolev.ofFun m ψ) {η : ℝ} (hη : 0 ≤ η)
    (hb : ∀ t : Set.Icc (0 : ℝ) T, ∀ x, |σ * (S.ρ (a + t) x - 1) - b t * ψ x| ≤ η) :
    ‖mp_Dp S hm2 T a ha σ - Φ‖ ≤ η * mp_Km d m := by
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine (ContinuousMap.norm_le _ (mul_nonneg hη (mp_Km_nonneg (d := d) m))).2 fun t => ?_
  have hq := therm_density S (show 0 ≤ a + (t : ℝ) by linarith [t.2.1])
  have e : PathSpace.at' (mp_Dp S hm2 T a ha σ - Φ) t = NegSobolev.ofFun m (fun x =>
      σ * (S.ρ (a + t) x - 1) - b t * ψ x) := by
    show PathSpace.at' (mp_Dp S hm2 T a ha σ) t - PathSpace.at' Φ t = _
    rw [hΦ t, mp_Dp_apply]
    exact mp_ofFun_sub_smul hm2 (((IID.integrable_of_pd hq).sub (integrable_const (1 : ℝ))).const_mul σ)
      hψi (b t)
  show ‖PathSpace.at' (mp_Dp S hm2 T a ha σ - Φ) t‖ ≤ _
  rw [e]
  exact mp_norm_ofFun_le hm2 (hb t)

/-- from `f n ≤ η K` for all `η > 0` eventually, to `f n → 0`. -/
theorem mp_tendsto_zero_of_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, f n ≤ η * K) : Tendsto f atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha (hf n), ?_⟩
  intro a ha
  have hη : 0 < a / (2 * (K + 1)) := by positivity
  filter_upwards [h _ hη] with n hn
  refine lt_of_le_of_lt hn ?_
  calc a / (2 * (K + 1)) * K ≤ a / (2 * (K + 1)) * (K + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hη.le
    _ = a / 2 := by field_simp
    _ < a := by linarith

/-- The limit shift `t ↦ A e^{-λ(τ+t)} ψ_k` in `E_m`. -/
def mp_dInfFun (m A lam τ : ℝ) (k : Lattice d) : ℝ → NegSobolev d m :=
  fun t => (A * Real.exp (-lam * (τ + t))) • NegSobolev.ofFun m (PDE.cosTest k)

theorem mp_dInfFun_cont (m A lam τ : ℝ) (k : Lattice d) : Continuous (mp_dInfFun m A lam τ k) := by
  unfold mp_dInfFun
  fun_prop

theorem mp_cosTest_continuous (k : Lattice d) : Continuous (PDE.cosTest k) :=
  Cor516Aux.continuous_of_isCk' (Cor516Aux.isCk_cosTest' k 0)

/-- reindexing helpers -/
theorem mp_reindex_tendsto {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) :
    Tendsto (fun N : ℕ => u (N - 2)) atTop atTop :=
  hu.comp (tendsto_sub_atTop_nat 2)

/-- **L8 (critical case)**: `Dp_n → d∞` in `𝒳_{m,T}` when `u_n - (2λ)⁻¹ log N → τ`. -/
theorem mp_det_shift_critical (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (hkβ : β * rieszCoeff d s k ≤ 1 / 4) (ε A : ℝ) (hε : 0 < ε)
    (ρ : ℝ → Torus d → ℝ) (C : ℝ) (Cj : ℕ → ℝ)
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (S : PreparedData d)
    (hSρ : ∀ t, 0 ≤ t → S.ρ t = ρ t) {m : ℝ} (hm2 : (d : ℝ) < 2 * m) {T : ℝ}
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Tendsto u atTop atTop) (τ : ℝ)
    (hτ : Tendsto (fun n : ℕ => u n - (2 * PDE.transientRate d s β k)⁻¹ * Real.log (n + 2 : ℕ))
      atTop (𝓝 τ)) :
    Tendsto (fun n : ℕ =>
      ‖mp_Dp S hm2 T (u n) (hu0 n) (Real.sqrt ((n + 2 : ℕ) : ℝ)) -
        mp_shiftPath m T (mp_dInfFun m A (PDE.transientRate d s β k) τ k)
          (mp_dInfFun_cont m A (PDE.transientRate d s β k) τ k).continuousOn‖) atTop (𝓝 0) := by
  set u' : ℕ → ℝ := fun N => u (N - 2) with hu'
  have hu'2 : ∀ n : ℕ, u' (n + 2) = u n := fun n => by simp [hu']
  have hu'top : Tendsto u' atTop atTop := mp_reindex_tendsto hu
  have hτ' : Tendsto (fun N : ℕ => u' N -
      (2 * PDE.transientRate d s β k)⁻¹ * Real.log N) atTop (𝓝 τ) := by
    refine (tendsto_add_atTop_iff_nat 2).mp (hτ.congr fun n => ?_)
    simp [hu'2]
  have hcrit := mean_threshold_critical hd hs0 hsd hβ k hk hkβ ε A hε ρ C Cj hρ u' hu'top τ hτ' 0 T
  refine mp_tendsto_zero_of_le (fun n => norm_nonneg _) (mp_Km_nonneg (d := d) m) fun η hη => ?_
  obtain ⟨N₀, hN₀⟩ := hcrit η hη
  filter_upwards [eventually_ge_atTop N₀] with n hn
  have hN := hN₀ (n + 2) (by omega)
  rw [hu'2] at hN
  refine mp_Dp_sub_le S hm2 T (u n) (hu0 n) _ (mp_cosTest_continuous k)
    (fun t => A * Real.exp (-PDE.transientRate d s β k * (τ + t))) _ (fun t => rfl) hη.le ?_
  intro t x
  have ht : (t : ℝ) ∈ Set.Icc (0 : ℝ) T := t.2
  have hpos : 0 ≤ u n + (t : ℝ) := by linarith [hu0 n, t.2.1]
  rw [hSρ _ hpos]
  have hck : Torus.IsCk 0 (fun x => Real.sqrt ((n + 2 : ℕ) : ℝ) * (ρ (u n + t) x - 1) -
      A * Real.exp (-PDE.transientRate d s β k * (τ + t)) * PDE.cosTest k x) :=
    Cor516Aux.isCk_sub'
      (Cor516Aux.isCk_const_mul'
        (Cor516Aux.isCk_sub' (Cor516Aux.isCk_of_isSmooth' (hρ.smooth_pos _ hpos).1 0)
          (Cor516Aux.isCk_const' 0 1)) _)
      (Cor516Aux.isCk_const_mul' (Cor516Aux.isCk_cosTest' k 0) _)
  exact (Cor516Aux.abs_le_cbNorm' hck x).trans (hN t ht)

/-- **L8 (late case)**: `Dp_n → 0` in `𝒳_{m,T}` when `u_n - (2λ)⁻¹ log N → +∞`. -/
theorem mp_det_shift_late (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (hkβ : β * rieszCoeff d s k ≤ 1 / 4) (ε A : ℝ) (hε : 0 < ε)
    (ρ : ℝ → Torus d → ℝ) (C : ℝ) (Cj : ℕ → ℝ)
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (S : PreparedData d)
    (hSρ : ∀ t, 0 ≤ t → S.ρ t = ρ t) {m : ℝ} (hm2 : (d : ℝ) < 2 * m) {T : ℝ}
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Tendsto u atTop atTop)
    (hlate : Tendsto (fun n : ℕ => u n - (2 * PDE.transientRate d s β k)⁻¹ * Real.log (n + 2 : ℕ))
      atTop atTop) :
    Tendsto (fun n : ℕ => ‖mp_Dp S hm2 T (u n) (hu0 n) (Real.sqrt ((n + 2 : ℕ) : ℝ))‖)
      atTop (𝓝 0) := by
  set u' : ℕ → ℝ := fun N => u (N - 2) with hu'
  have hu'2 : ∀ n : ℕ, u' (n + 2) = u n := fun n => by simp [hu']
  have hu'top : Tendsto u' atTop atTop := mp_reindex_tendsto hu
  have hlate' : Tendsto (fun N : ℕ => u' N -
      (2 * PDE.transientRate d s β k)⁻¹ * Real.log N) atTop atTop := by
    refine (tendsto_add_atTop_iff_nat 2).mp (hlate.congr fun n => ?_)
    simp [hu'2]
  have hl := mean_threshold_late hd hs0 hsd hβ k hk hkβ ε A hε ρ C Cj hρ u' hu'top hlate' 0 T
  refine mp_tendsto_zero_of_le (fun n => norm_nonneg _) (mp_Km_nonneg (d := d) m) fun η hη => ?_
  obtain ⟨N₀, hN₀⟩ := hl η hη
  filter_upwards [eventually_ge_atTop N₀] with n hn
  have hN := hN₀ (n + 2) (by omega)
  rw [hu'2] at hN
  have h := mp_Dp_sub_le S hm2 T (u n) (hu0 n) (Real.sqrt ((n + 2 : ℕ) : ℝ))
    (mp_cosTest_continuous k) (fun _ => 0) 0 (fun t => by
      show (0 : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) t = (0 : ℝ) • NegSobolev.ofFun m (PDE.cosTest k)
      rw [zero_smul]; rfl) hη.le (fun t x => ?_)
  · simpa using h
  · have hpos : 0 ≤ u n + (t : ℝ) := by linarith [hu0 n, t.2.1]
    rw [hSρ _ hpos, zero_mul, sub_zero]
    have hck : Torus.IsCk 0 (fun x => Real.sqrt ((n + 2 : ℕ) : ℝ) * (ρ (u n + t) x - 1)) :=
      Cor516Aux.isCk_const_mul'
        (Cor516Aux.isCk_sub' (Cor516Aux.isCk_of_isSmooth' (hρ.smooth_pos _ hpos).1 0)
          (Cor516Aux.isCk_const' 0 1)) _
    exact (Cor516Aux.abs_le_cbNorm' hck x).trans (hN t t.2)

/-- **Part (c)**: `δ_n = √N ∫ψ_k(ρ^{u_n} - 1) → +∞` in the early case, reindexed to `N = n + 2`. -/
theorem mp_delta_early (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (hkβ : β * rieszCoeff d s k ≤ 1 / 4) (ε A : ℝ) (hε : 0 < ε)
    (ρ : ℝ → Torus d → ℝ) (C : ℝ) (Cj : ℕ → ℝ)
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (u : ℕ → ℝ)
    (hu : Tendsto u atTop atTop)
    (hearly : Tendsto (fun n : ℕ => u n - (2 * PDE.transientRate d s β k)⁻¹ * Real.log (n + 2 : ℕ))
      atTop atBot) :
    Tendsto (fun n : ℕ => Real.sqrt ((n + 2 : ℕ) : ℝ) * ∫ x, PDE.cosTest k x * (ρ (u n) x - 1))
      atTop atTop := by
  set u' : ℕ → ℝ := fun N => u (N - 2) with hu'
  have hu'2 : ∀ n : ℕ, u' (n + 2) = u n := fun n => by simp [hu']
  have hu'top : Tendsto u' atTop atTop := mp_reindex_tendsto hu
  have hearly' : Tendsto (fun N : ℕ => u' N -
      (2 * PDE.transientRate d s β k)⁻¹ * Real.log N) atTop atBot := by
    refine (tendsto_add_atTop_iff_nat 2).mp (hearly.congr fun n => ?_)
    simp [hu'2]
  have h := mean_threshold_early hd hs0 hsd hβ k hk hkβ ε A hε ρ C Cj hρ u' hu'top hearly'
  have h2 := (tendsto_add_atTop_iff_nat 2).mpr h
  refine h2.congr fun n => ?_
  simp [hu'2]

end Main

end HRS
