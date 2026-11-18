import HRS.MP.FidiDefs

/-!
# Chunk F (`MP:`), packets F1/F2: the per-`N` coupling `hIdiff` and the transfer lemma

* `fi1_eta_meas`: measurability of `ω ↦ (etaF …).η ω ψ`.
* `fi1_trig_smooth`, `fi1_trig_sob`: trigonometric polynomials are smooth, and their `H^{m'}` norm is bounded by a
  constant times the `H^m` norm for `m ≤ m'`.
* `fi1_hIdiff`: the per-`N` coupling `E|σ_N⟨X_N - μ, U φ⟩ - A_N η(Uφ)| ≤ ε_N^f K ‖φ‖_{H^γ}` from Assumption A.5,
  with `K` independent of `N`.
* `fi2_transfer`: convergence in law transfers along a vanishing smooth-test distance.
-/

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Main HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.FidiDefs
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.MP.FidiF1

variable {d : ℕ}

theorem fi1_eval_meas {γ : ℝ} {ψ : Torus d → ℝ} (h : MemSobolev γ ψ) :
    Measurable fun F : NegSobolev d γ => NegSobolev.eval F ψ := by
  have : (fun F : NegSobolev d γ => NegSobolev.eval F ψ) = fun F => inner ℝ F (HRS.Uniform.Q54.lpOf γ h) := by
    funext F; exact HRS.Uniform.Q54.eval_eq_inner γ F h
  rw [this]
  exact (continuous_id.inner continuous_const).measurable

theorem fi1_eta_meas {S : MainData d} {R : ∀ N, Realization d N} {Cin : ℝ} {εf : ℕ → ℝ}
    {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)} {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin) (N : ℕ) (ψ : Torus d → ℝ) :
    Measurable fun ω => (etaF R (gammaIdx d) ηF N).η ω ψ := by
  classical
  by_cases h : MemSobolev (gammaIdx d : ℝ) ψ
  · have : (fun ω => (etaF R (gammaIdx d) ηF N).η ω ψ) = fun ω => NegSobolev.eval (ηF N ω) ψ := by
      funext ω; show (if MemSobolev (gammaIdx d : ℝ) ψ then _ else _) = _
      rw [if_pos h]
    rw [this]
    exact (fi1_eval_meas h).comp (hfield.ηF_meas N)
  · have : (fun ω => (etaF R (gammaIdx d) ηF N).η ω ψ) = fun _ => 0 := by
      funext ω; show (if MemSobolev (gammaIdx d : ℝ) ψ then _ else _) = _
      rw [if_neg h]
    rw [this]; exact measurable_const

theorem fi1_trig_smooth {φ : Torus d → ℝ} (hφ : IsTrigPolyT φ) : Torus.IsSmooth φ := by
  obtain ⟨F, c, c0, h⟩ := hφ
  have e : φ = fun x => c0 + HRS.FieldSingAux.trigPoly F c x := by
    funext x; rw [h x]; simp [HRS.FieldSingAux.trigPoly]
  have h1 := HRS.FieldSingAux.isSmooth_trigPoly F c
  rw [e]
  unfold Torus.IsSmooth Torus.IsCk at *
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => c0 + HRS.FieldSingAux.trigPoly F c (Torus.mk x))
  exact contDiff_const.add h1


/-- For a smooth test the `H^{m'}` norm is bounded by a constant (depending on the test) times the `H^m` norm,
`m ≤ m'`: if `‖φ‖_{H^m} = 0` all Fourier coefficients vanish. -/
theorem fi1_smooth_sob (m m' : ℝ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ c : ℝ, 0 ≤ c ∧ sobolevNorm m' φ ≤ c * sobolevNorm m φ := by
  by_cases hz : sobolevNorm m φ = 0
  · refine ⟨0, le_rfl, ?_⟩
    have hs : Summable fun k : NonzeroLattice d =>
        Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 := (HRS.A33.a33_memSob m hφ).2
    have hnn : ∀ k : NonzeroLattice d, 0 ≤ Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 :=
      fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
    unfold sobolevNorm at hz ⊢
    have h1 : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 :=
      tsum_nonneg hnn
    have h0 : (Torus.mean φ) ^ 2 +
        ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 = 0 :=
      le_antisymm (Real.sqrt_eq_zero'.1 hz) (add_nonneg (sq_nonneg _) h1)
    have hm0 : (Torus.mean φ) ^ 2 = 0 := by nlinarith [sq_nonneg (Torus.mean φ)]
    have ht0 : ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 = 0 := by
      linarith
    have hk : ∀ k : NonzeroLattice d, Torus.funRealCoeff φ k = 0 := by
      intro k
      have h2 := congrFun ((hasSum_zero_iff_of_nonneg hnn).1 (ht0 ▸ hs.hasSum)) k
      have hj : 0 < Lattice.jp k.1 ^ (2 * m) := Real.rpow_pos_of_pos (Torus.jp_pos _) _
      have h3 : Torus.funRealCoeff φ k ^ 2 = 0 := by
        simpa [hj.ne'] using h2
      exact pow_eq_zero_iff two_ne_zero |>.1 h3
    have hmean : Torus.mean φ = 0 := pow_eq_zero_iff two_ne_zero |>.1 hm0
    simp [hk, hmean]
  · exact ⟨sobolevNorm m' φ / sobolevNorm m φ,
      div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), by rw [div_mul_cancel₀ _ hz]⟩

theorem fi1_trig_sob (m m' : ℝ) (hmm : m ≤ m') {φ : Torus d → ℝ} (hφ : IsTrigPolyT φ) :
    ∃ c : ℝ, 0 ≤ c ∧ sobolevNorm m' φ ≤ c * sobolevNorm m φ := by
  obtain ⟨F, c, c0, h⟩ := hφ
  have e : φ = fun x => c0 + HRS.FieldSingAux.trigPoly F c x := by
    funext x; rw [h x]; simp [HRS.FieldSingAux.trigPoly]
  have hcont : Continuous (HRS.FieldSingAux.trigPoly F c) :=
    continuous_finset_sum _ fun k _ => continuous_const.mul (HRS.FieldSingAux.continuous_realMode k)
  have hint : Integrable (HRS.FieldSingAux.trigPoly F c) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmean : Torus.mean φ = c0 := by
    rw [e]; unfold Torus.mean
    rw [integral_add (integrable_const _) hint]
    have := HRS.FieldSingAux.mean_trigPoly F c
    unfold Torus.mean at this
    rw [this]; simp
  have hcoef : ∀ k, Torus.funRealCoeff φ k = if k ∈ F then c k else 0 := by
    intro k
    rw [← HRS.FieldSingAux.funRealCoeff_trigPoly F c k]
    unfold Torus.funRealCoeff
    rw [e]
    simp only [mul_add]
    have i1 : Integrable fun x => Torus.realMode k x * c0 :=
      ((HRS.FieldSingAux.continuous_realMode k).mul continuous_const).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have i2 : Integrable fun x => Torus.realMode k x * HRS.FieldSingAux.trigPoly F c x :=
      ((HRS.FieldSingAux.continuous_realMode k).mul hcont).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_add i1 i2]
    have : ∫ x, Torus.realMode k x * c0 = 0 := by
      rw [integral_mul_const, Torus.integral_realMode, zero_mul]
    rw [this, zero_add]
  have hnorm : ∀ r : ℝ, sobolevNorm r φ =
      Real.sqrt (c0 ^ 2 + ∑ k ∈ F, Lattice.jp k.1 ^ (2 * r) * c k ^ 2) := by
    intro r
    unfold sobolevNorm
    rw [hmean, tsum_eq_sum (s := F)]
    · congr 1
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hcoef, if_pos hk]
    · intro k hk
      rw [hcoef, if_neg hk]; simp
  set M : ℝ := 1 + ∑ k ∈ F, Lattice.jp k.1 ^ (2 * (m' - m)) with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ∑ k ∈ F, Lattice.jp k.1 ^ (2 * (m' - m)) :=
      Finset.sum_nonneg fun k _ => Real.rpow_nonneg (Torus.jp_pos _).le _
    linarith
  refine ⟨Real.sqrt M, Real.sqrt_nonneg _, ?_⟩
  rw [hnorm, hnorm, ← Real.sqrt_mul (by linarith)]
  refine Real.sqrt_le_sqrt ?_
  have hterm : ∀ k ∈ F, Lattice.jp k.1 ^ (2 * m') * c k ^ 2 ≤
      M * (Lattice.jp k.1 ^ (2 * m) * c k ^ 2) := by
    intro k hk
    have hj := Torus.jp_pos k.1
    have h1 : Lattice.jp k.1 ^ (2 * m') = Lattice.jp k.1 ^ (2 * m) * Lattice.jp k.1 ^ (2 * (m' - m)) := by
      rw [← Real.rpow_add hj]; ring_nf
    have h2 : Lattice.jp k.1 ^ (2 * (m' - m)) ≤ M := by
      have := Finset.single_le_sum (f := fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * (m' - m)))
        (fun k _ => Real.rpow_nonneg (Torus.jp_pos _).le _) hk
      beta_reduce at this
      linarith
    have h3 : 0 ≤ Lattice.jp k.1 ^ (2 * m) * c k ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hj.le _) (sq_nonneg _)
    rw [h1]
    calc Lattice.jp k.1 ^ (2 * m) * Lattice.jp k.1 ^ (2 * (m' - m)) * c k ^ 2
        = Lattice.jp k.1 ^ (2 * (m' - m)) * (Lattice.jp k.1 ^ (2 * m) * c k ^ 2) := by ring
      _ ≤ M * (Lattice.jp k.1 ^ (2 * m) * c k ^ 2) := mul_le_mul_of_nonneg_right h2 h3
  calc c0 ^ 2 + ∑ k ∈ F, Lattice.jp k.1 ^ (2 * m') * c k ^ 2
      ≤ M * c0 ^ 2 + ∑ k ∈ F, M * (Lattice.jp k.1 ^ (2 * m) * c k ^ 2) := by
        exact add_le_add (by nlinarith [sq_nonneg c0]) (Finset.sum_le_sum hterm)
    _ = M * (c0 ^ 2 + ∑ k ∈ F, Lattice.jp k.1 ^ (2 * m) * c k ^ 2) := by
        rw [← Finset.mul_sum, mul_add]

theorem fi1_hIdiff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : PDE.Regime)
    (MB Λ VB ν₀ T : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ) (C₀ Cc : ℝ),
        TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 →
        ∀ (Cin : ℝ) (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
          (νin : Measure (NegSobolev d (gammaIdx d : ℝ))),
          InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin →
        ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
          ∫⁻ ω, ENNReal.ofReal
            |S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0) (propagator (S.dyn N) (S.ρ N) 0 t φ) -
              S.AN N * (etaF R (gammaIdx d) ηF N).η ω (propagator (S.dyn N) (S.ρ N) 0 t φ)|
            ∂(R N).P ≤
          ENNReal.ofReal (εf N * (K * sobolevNorm (gammaIdx d : ℝ) φ)) := by
  have hγm : PDE.mStar d ≤ gammaIdx d := by unfold gammaIdx; omega
  obtain ⟨K, K₂, hK0, hK₂0, hu⟩ := HRS.A34.a34_unif hd s hs0 hsd (gammaIdx d) hγm Rg MB Λ VB ν₀ T
  have h1γ : 1 ≤ gammaIdx d := by have := PDE.ClassicalPart.three_le_mStar d; unfold gammaIdx; omega
  refine ⟨max (K (gammaIdx d)) 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro S hs hT R 𝔈 C₀ Cc hS Cin εf ηF νin hfield N hN t ht φ hφ
  subst hs hT
  have hSm : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 := A9.a9_standing_mono hγm hS
  have hSR' : TorusStanding S (etaF R (gammaIdx d) ηF) Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 :=
    fi1_standing _ ηF hSm
  have hA : PDE.AdjointData S.s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    A9.a9_adjointData hγm hS hN
  have hφc : Continuous φ := A33.a33_cont hφ
  have hφm : MemSobolev (gammaIdx d : ℝ) φ := A33.a33_memSob _ hφ
  -- the propagated test is an `H^γ` continuous test with norm bounded by `K ‖φ‖`
  have hψ : MemSobolev (gammaIdx d : ℝ) (propagator (S.dyn N) (S.ρ N) 0 t φ) ∧
      Continuous (propagator (S.dyn N) (S.ρ N) 0 t φ) ∧
      sobolevNorm (gammaIdx d : ℝ) (propagator (S.dyn N) (S.ρ N) 0 t φ) ≤
        max (K (gammaIdx d)) 1 * sobolevNorm (gammaIdx d : ℝ) φ := by
    have h0 : 0 ≤ sobolevNorm (gammaIdx d : ℝ) φ := Real.sqrt_nonneg _
    rcases ht.1.eq_or_lt with h0t | hpos
    · rw [← h0t, HRS.A34.a34_prop_zero hd (gammaIdx d) hγm Rg S.s MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) hA hφc hφm]
      exact ⟨hφm, hφc, by nlinarith [le_max_right (K (gammaIdx d)) 1]⟩
    · obtain ⟨-, hr⟩ := hu (S.dyn N) (S.ρ N) hA ⟨hpos, ht.2⟩ hφc hφm
      obtain ⟨hm1, hC2, -⟩ := hr 0 ⟨le_rfl, hpos.le⟩
      obtain ⟨hmem, hb⟩ := hm1 (gammaIdx d) h1γ le_rfl
      exact ⟨hmem, HRS.PDE.ClassicalAux.continuous_of_isCk (HRS.PDE.ClassicalAux.isCk_of_le (by norm_num) hC2),
        hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h0)⟩
  obtain ⟨hψm, hψc, hψn⟩ := hψ
  haveI : ∀ ω, IsProbabilityMeasure (empirical ((R N).X₀ ω)) := fun ω =>
    empirical_isProbabilityMeasure hN _
  haveI := S.hμ0
  have hid := A8P.a8p_I_ident (R := etaF R (gammaIdx d) ηF) hSR' hN
    (propagator (S.dyn N) (S.ρ N) 0 t φ)
  have hε := hfield.εf_nonneg N hN
  have hAN := A8P.a8p_A_abs_le S N
  have hfm := hfield.first_moment N hN
  have hnn : 0 ≤ sobolevNorm (gammaIdx d : ℝ) (propagator (S.dyn N) (S.ρ N) 0 t φ) := Real.sqrt_nonneg _
  calc ∫⁻ ω, ENNReal.ofReal
          |S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0) (propagator (S.dyn N) (S.ρ N) 0 t φ) -
            S.AN N * (etaF R (gammaIdx d) ηF N).η ω (propagator (S.dyn N) (S.ρ N) 0 t φ)| ∂(R N).P
      ≤ ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0 -
            ηF N ω‖ₑ * ENNReal.ofReal (sobolevNorm (gammaIdx d : ℝ)
              (propagator (S.dyn N) (S.ρ N) 0 t φ)) ∂(R N).P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hid] with ω hω
        have hω' : S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0) (propagator (S.dyn N) (S.ρ N) 0 t φ) -
            S.AN N * (etaF R (gammaIdx d) ηF N).η ω (propagator (S.dyn N) (S.ρ N) 0 t φ) =
            S.AN N * (S.κ N * (pair (empirical ((R N).X₀ ω)) (propagator (S.dyn N) (S.ρ N) 0 t φ) -
              pair S.μ0 (propagator (S.dyn N) (S.ρ N) 0 t φ)) -
              (etaF R (gammaIdx d) ηF N).η ω (propagator (S.dyn N) (S.ρ N) 0 t φ)) := hω
        rw [hω', abs_mul]
        have hη' : (etaF R (gammaIdx d) ηF N).η ω (propagator (S.dyn N) (S.ρ N) 0 t φ) =
            NegSobolev.eval (ηF N ω) (propagator (S.dyn N) (S.ρ N) 0 t φ) := by
          classical
          show (if MemSobolev (gammaIdx d : ℝ) _ then _ else _) = _
          rw [if_pos hψm]
        have hev : S.κ N * (pair (empirical ((R N).X₀ ω)) (propagator (S.dyn N) (S.ρ N) 0 t φ) -
              pair S.μ0 (propagator (S.dyn N) (S.ρ N) 0 t φ)) -
              (etaF R (gammaIdx d) ηF N).η ω (propagator (S.dyn N) (S.ρ N) 0 t φ) =
            NegSobolev.eval (S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
              (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω) (propagator (S.dyn N) (S.ρ N) 0 t φ) := by
          rw [hη', A9.a9_eval_sub _ _ (A33.a33_ws_of_memSobolev hψm), A9.a9_eval_smul,
            A9.a9_eval_ofMeasureDiff A9.a9_gamma_gt _ _ hψm hψc]
        rw [hev, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hb := A33.a33_abs_eval_le (S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
              (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω) (A33.a33_ws_of_memSobolev hψm)
        calc |S.AN N| * |NegSobolev.eval (S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
              (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω) (propagator (S.dyn N) (S.ρ N) 0 t φ)|
            ≤ 1 * (‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
              (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω‖ *
                sobolevNorm (gammaIdx d : ℝ) (propagator (S.dyn N) (S.ρ N) 0 t φ)) :=
              mul_le_mul hAN hb (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ = (∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0 -
            ηF N ω‖ₑ ∂(R N).P) * ENNReal.ofReal (sobolevNorm (gammaIdx d : ℝ)
              (propagator (S.dyn N) (S.ρ N) 0 t φ)) := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (εf N) * ENNReal.ofReal (max (K (gammaIdx d)) 1 * sobolevNorm (gammaIdx d : ℝ) φ) :=
        mul_le_mul' hfm (ENNReal.ofReal_le_ofReal hψn)
    _ = ENNReal.ofReal (εf N * (max (K (gammaIdx d)) 1 * sobolevNorm (gammaIdx d : ℝ) φ)) :=
        (ENNReal.ofReal_mul hε).symm

/-! ### F2 -/
local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem fi2_transfer {p : ℕ} (μ lam : ℕ → Measure (ℝ^p)) (lam₀ : Measure (ℝ^p))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (lam n)] [IsProbabilityMeasure lam₀]
    (hlc : ConvergesInLaw lam lam₀)
    (hd : Tendsto (fun n => smoothDist 2 (μ n) (lam n)) atTop (𝓝 0)) :
    ConvergesInLaw μ lam₀ := fun f => by
  simpa using HRS.Main.A9.a9_fd_converges (ContinuousLinearMap.id ℝ (ℝ^p)) μ lam lam₀ hlc hd f

end HRS.MP.FidiF1
