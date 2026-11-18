import HRS.MS.WsInitKAux3
import HRS.MS.WsPrepAux14

/-!
# S21T packet 1 (S2.1 (ii), INIT): the window initial path as `Φ(featureVec)` and the orbit input

Setting of the INIT row of `HANDOFF_S21R.md` (section 3, item 3).  For a window start `bw ≥ 0` the particle initial path is
`K_bw = r2InitCouplingPath C m T μ₀ bw id 0` (`s21iK`): `u ↦ (√N (μ_N^0 - μ₀)(U^{0,bw+u} φ_α))_α`, mean-field centring at `μ₀ = ρ⁰ dx`.

* `s21i_series`, `s21i_coord_series`, `s21i_Theta_feature`: the cosine series of the orbit in the enumeration `σ`, for an arbitrary
  orbit `U` with `S11pSeries D T U` (the lemmas `s21g_series`, `s21g_coord_series`, `s21g_Theta_feature` of the stationary packet G
  restated without the coefficient `C`);
* `s21i_path_eq`: `K_bw = Φ_σ (featureVec φ μ₀ ·)` with `φ_j = f_{bw,σ j}` (the window cosine tests `r2WindowTest`) and the fixed
  synthesis map `Φ_σ = s21gPhi σ` (independent of `bw`);
* `S21iOrb`: the output of S10.3 (`r2_window_orbits`) consumed here: `f_{bw,n,α} ∈ C_b^{4d+42}` with
  `‖f_{bw,n,α}‖ ≤ C (1+n)^{-5/4} b_α` uniformly in `bw ≥ 0`, plus continuity of the orbit in the window variable;
* `s21i_orb_data`, `s21i_series_of_orb`, `s21i_family`: the `S11pData`, the pointwise cosine series and the summable feature family.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc cbNorm MemCb smoothDist)

variable {d : ℕ}

/-! ### The cosine series of a general orbit -/

theorem s21i_series {D : S11pData d} {U : MultiIndex d → ℝ → Euc d → ℝ} {T : ℝ} (hT : 0 < T)
    (hU : S11pSeries D T U) (σ : ℕ ≃ ℕ × MultiIndex d) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (α : MultiIndex d) (x : Euc d) :
    HasSum (fun j : ℕ => SeqL2.coord (s21gVec σ hT t α) j * D.f (σ j) x) (U α t x) := by
  classical
  have h := hU α t ht x
  set g : ℕ → ℕ := fun n => σ.symm (n, α) with hg
  have hginj : Function.Injective g := fun a b hab => by
    have := σ.symm.injective hab
    simpa using this
  set F : ℕ → ℝ := fun j => SeqL2.coord (s21gVec σ hT t α) j * D.f (σ j) x with hF
  have hz : ∀ j ∉ Set.range g, F j = 0 := by
    intro j hj
    simp only [hF, s21gVec_coord]
    by_cases hα : (σ j).2 = α
    · exfalso
      apply hj
      refine ⟨(σ j).1, ?_⟩
      simp only [hg]
      have : ((σ j).1, α) = σ j := Prod.ext rfl hα.symm
      rw [this, Equiv.symm_apply_apply]
    · simp [hα]
  rw [← hginj.hasSum_iff hz]
  convert h using 1
  funext n
  simp only [Function.comp_apply, hF, hg, s21gVec_coord, Equiv.apply_symm_apply, ite_true]

theorem s21i_coord_series {D : S11pData d} {U : MultiIndex d → ℝ → Euc d → ℝ} {T : ℝ} (hT : 0 < T)
    (hU : S11pSeries D T U) {N : ℕ} (hN : 1 ≤ N) (ν : Measure (Euc d)) [IsProbabilityMeasure ν]
    (x : EucConfig d N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (U α t) - HRS.Whole.pair ν (U α t)) =
      ∑' n : ℕ, s11p_kap n * r2CosBasis T n t * (Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical x) (D.f (n, α)) - HRS.Whole.pair ν (D.f (n, α)))) := by
  have h1 : HasSum (fun n : ℕ => s11p_kap n * r2CosBasis T n t *
      HRS.Whole.pair (HRS.Whole.empirical x) (D.f (n, α)))
      (HRS.Whole.pair (HRS.Whole.empirical x) (U α t)) := by
    have e : ∀ n : ℕ, s11p_kap n * r2CosBasis T n t * HRS.Whole.pair (HRS.Whole.empirical x) (D.f (n, α)) =
        (N : ℝ)⁻¹ * ∑ i, s11p_kap n * r2CosBasis T n t * D.f (n, α) (x i) := by
      intro n
      rw [HRS.Whole.pair_empirical (by omega), ← Finset.mul_sum]; ring
    simp_rw [e]
    rw [HRS.Whole.pair_empirical (by omega)]
    refine (hasSum_sum (s := Finset.univ) (f := fun (i : Fin N) (n : ℕ) =>
      s11p_kap n * r2CosBasis T n t * D.f (n, α) (x i))
      (a := fun i => U α t (x i)) fun i _ => ?_).mul_left (N : ℝ)⁻¹
    exact hU α t ht (x i)
  have h2 := s11p_mu_series ν hT hU α t ht
  have h3 : HasSum (fun n : ℕ => Real.sqrt N * (s11p_kap n * r2CosBasis T n t *
        HRS.Whole.pair (HRS.Whole.empirical x) (D.f (n, α)) -
        s11p_kap n * r2CosBasis T n t * HRS.Whole.pair ν (D.f (n, α))))
      (Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (U α t) -
        HRS.Whole.pair ν (U α t))) := (h1.sub h2).mul_left (Real.sqrt N)
  refine h3.tsum_eq.symm.trans (tsum_congr fun n => ?_)
  ring

theorem s21i_Theta_feature {J : ℕ} (D : S11pData d) (σ : ℕ ≃ ℕ × MultiIndex d)
    (hφ : IsSummableFeatureFamily J (fun j => D.f (σ j))) {N : ℕ} (hN : 1 ≤ N)
    (ν : Measure (Euc d)) [IsProbabilityMeasure ν] (x : EucConfig d N) (n : ℕ) (α : MultiIndex d) :
    (s21gTheta σ (featureVec (fun j => D.f (σ j)) ν x)).c (n, α) =
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (D.f (n, α)) - HRS.Whole.pair ν (D.f (n, α))) := by
  have h := s21gTheta_c σ (featureVec (fun j => D.f (σ j)) ν x) (σ.symm (n, α))
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  unfold featureVec
  rw [S45.s45_coord_ofSeq (S45.s45_feature_memℓp hN hφ x)]
  simp

/-! ### The window initial path -/

/-- The particle initial path of the window starting at `bw`: `r2InitCouplingPath` with the identity realization and `η₀ = 0`. -/
def s21iK (C : WholeCoeff d) (m T : ℝ) (μ0 : Measure (Euc d)) (bw : ℝ) {N : ℕ} (x : EucConfig d N) :
    OscPath d m T :=
  r2InitCouplingPath C m T μ0 bw (fun y : EucConfig d N => y) (fun _ _ => 0) x

theorem s21i_path_eq {C : WholeCoeff d} {m T : ℝ} (hT : 0 < T) (bw : ℝ) (D : S11pData d)
    (hU : S11pSeries D T (fun α u x => propagatorW C 0 (bw + u) (oscTestFun m α) x))
    (σ : ℕ ≃ ℕ × MultiIndex d) {J : ℕ} (hφ : IsSummableFeatureFamily J (fun j => D.f (σ j)))
    (μ0 : Measure (Euc d)) [IsProbabilityMeasure μ0] {N : ℕ} (hN : 1 ≤ N) (x : EucConfig d N) :
    s21iK C m T μ0 bw x = s21gPhi σ hT m (featureVec (fun j => D.f (σ j)) μ0 x) := by
  unfold s21iK r2InitCouplingPath
  refine s11p_windowPathOf_eq m T _ _ (fun t => ?_)
  unfold r2InitCouplingFun
  rw [← s11p_ellVec_coord (OscPath.at' (s21gPhi σ hT m (featureVec (fun j => D.f (σ j)) μ0 x)) t)]
  congr 1
  funext α
  rw [s21gPhi_coord]
  simp_rw [s21i_Theta_feature D σ hφ hN μ0 x]
  rw [← s21i_coord_series hT hU hN μ0 x t.2 α]
  simp

/-! ### The S10.3 orbit input -/

/-- The weight `b_α = λ_α^{(J'-m)/2}`, `J' = 18d+180`, `m = 24d+240` of S10.3 (`r2_window_orbits`). -/
def s21iB (d : ℕ) (α : MultiIndex d) : ℝ :=
  oscEigenvalue d α ^ ((((18 * d + 180 : ℕ) : ℝ) - ((24 * d + 240 : ℕ) : ℝ)) / 2)

/-- The window-test weights `C (1+n)^{-5/4} b_α`. -/
def s21iW (d : ℕ) (Corb : ℝ) (q : ℕ × MultiIndex d) : ℝ :=
  Corb * (1 + (q.1 : ℝ)) ^ (-(5 : ℝ) / 4) * s21iB d q.2

/-- The conclusions of S10.3 (`r2_window_orbits`, last clause) consumed by INIT, for the coefficients `C` and the horizon `T`:
the window cosine tests are in `C_b^{4d+42}` with `‖f_{bw,n,α}‖ ≤ C (1+n)^{-5/4} b_α`, uniformly in `bw ≥ 0`, and the orbit
`u ↦ U^{0,bw+u}φ_α(x)` is continuous on `[0,T]` (the transported initial paths are well-defined). -/
def S21iOrb (d : ℕ) (T : ℝ) (C : WholeCoeff d) (Corb : ℝ) : Prop :=
  0 ≤ Corb ∧
    (∀ bw : ℝ, 0 ≤ bw → ∀ (n : ℕ) (α : MultiIndex d),
      MemCb (4 * d + 42) (r2WindowTest C ((wholeSpaceIndex d : ℕ) : ℝ) T bw n α) ∧
      cbNorm (4 * d + 42) (r2WindowTest C ((wholeSpaceIndex d : ℕ) : ℝ) T bw n α) ≤
        Corb * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * s21iB d α) ∧
    (∀ bw : ℝ, 0 ≤ bw → ∀ (α : MultiIndex d) (x : Euc d),
      ContinuousOn (fun u => propagatorW C 0 (bw + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x)
        (Set.Icc (0 : ℝ) T))

theorem s21i_B_summable (hd : 1 ≤ d) : Summable (s21iB d) := by
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h := (summable_oscEigenvalue_rpow_iff hd
    ((((24 * d + 240 : ℕ) : ℝ) - ((18 * d + 180 : ℕ) : ℝ)) / 2)).2 (by push_cast; linarith)
  have e : -((((24 * d + 240 : ℕ) : ℝ) - ((18 * d + 180 : ℕ) : ℝ)) / 2) =
      (((18 * d + 180 : ℕ) : ℝ) - ((24 * d + 240 : ℕ) : ℝ)) / 2 := by ring
  rw [e] at h
  exact h

theorem s21i_B_nonneg (α : MultiIndex d) : 0 ≤ s21iB d α :=
  Real.rpow_nonneg (oscEv_pos α).le _

theorem s21i_n_summable : Summable fun n : ℕ => (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show (-(5 : ℝ) / 4) < -1 by norm_num))
  refine h.congr fun n => ?_
  push_cast
  rw [add_comm]

theorem s21i_W_summable (hd : 1 ≤ d) (Corb : ℝ) : Summable (s21iW d Corb) := by
  have h := Summable.mul_of_nonneg s21i_n_summable (s21i_B_summable hd)
    (fun n => Real.rpow_nonneg (by positivity) _) (fun α => s21i_B_nonneg α)
  have h2 := h.mul_left Corb
  refine h2.congr fun q => ?_
  simp only [s21iW]
  ring

theorem s21i_W_nonneg {Corb : ℝ} (hC : 0 ≤ Corb) (q : ℕ × MultiIndex d) : 0 ≤ s21iW d Corb q := by
  unfold s21iW
  have : 0 ≤ (1 + (q.1 : ℝ)) ^ (-(5 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have := s21i_B_nonneg q.2
  positivity

/-- The sum of the weights (uniform in the window start). -/
def s21iS0 (d : ℕ) (Corb : ℝ) : ℝ := ∑' q : ℕ × MultiIndex d, s21iW d Corb q

theorem s21i_orb_data (hd : 1 ≤ d) {T : ℝ} {C : WholeCoeff d} {Corb : ℝ} (h : S21iOrb d T C Corb)
    (bw : ℝ) (hbw : 0 ≤ bw) :
    ∃ D : S11pData d, (∀ q : ℕ × MultiIndex d, D.f q = r2WindowTest C ((wholeSpaceIndex d : ℕ) : ℝ) T bw q.1 q.2) ∧
      (∀ q, D.w q = s21iW d Corb q) := by
  refine ⟨{ f := fun q => r2WindowTest C ((wholeSpaceIndex d : ℕ) : ℝ) T bw q.1 q.2
            w := s21iW d Corb
            hw := s21i_W_summable hd Corb
            hfw := fun q x => ?_
            hfc := fun q => ((h.2.1 bw hbw q.1 q.2).1).1.continuous }, fun q => rfl, fun q => rfl⟩
  exact (s11p_abs_le_cbNorm (h.2.1 bw hbw q.1 q.2).1 x).trans (h.2.1 bw hbw q.1 q.2).2

theorem s21i_series_of_orb {T : ℝ} (hT : 0 < T) {C : WholeCoeff d} {Corb : ℝ}
    (h : S21iOrb d T C Corb) {bw : ℝ} (hbw : 0 ≤ bw) (D : S11pData d)
    (hD : ∀ q : ℕ × MultiIndex d, D.f q = r2WindowTest C ((wholeSpaceIndex d : ℕ) : ℝ) T bw q.1 q.2) :
    S11pSeries D T (fun α u x => propagatorW C 0 (bw + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x) := by
  intro α t ht x
  have hb : Summable fun n : ℕ => D.f (n, α) x :=
    Summable.of_norm_bounded (s11p_series_summable_w D α) (fun n => by
      rw [Real.norm_eq_abs]; exact D.hfw (n, α) x)
  exact s11p_cos_expand hT (fun u => propagatorW C 0 (bw + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x)
    (h.2.2 bw hbw α x) (fun n => D.f (n, α) x) hb (fun n => by rw [hD]; rfl) t ht

/-- The window feature family in the enumeration `σ`: summable in `C_b^{4d+42}` with `featureSum ≤ S₀`. -/
theorem s21i_family (hd : 1 ≤ d) {T : ℝ} {C : WholeCoeff d} {Corb : ℝ} (h : S21iOrb d T C Corb)
    {bw : ℝ} (hbw : 0 ≤ bw) (D : S11pData d)
    (hD : ∀ q : ℕ × MultiIndex d, D.f q = r2WindowTest C ((wholeSpaceIndex d : ℕ) : ℝ) T bw q.1 q.2)
    (hw : ∀ q, D.w q = s21iW d Corb q) (σ : ℕ ≃ ℕ × MultiIndex d) :
    IsSummableFeatureFamily (4 * d + 42) (fun j => D.f (σ j)) ∧
      featureSum (4 * d + 42) (fun j => D.f (σ j)) ≤ s21iS0 d Corb ∧
      ∀ j, cbNorm (4 * d + 42) (D.f (σ j)) ≤ s21iW d Corb (σ j) := by
  have hle : ∀ q, cbNorm (4 * d + 42) (D.f q) ≤ s21iW d Corb q := fun q => by
    rw [hD q]; exact (h.2.1 bw hbw q.1 q.2).2
  have hWs : Summable (s21iW d Corb) := s21i_W_summable hd Corb
  have hWσ : Summable fun j => s21iW d Corb (σ j) := (Equiv.summable_iff σ).2 hWs
  have hsum : Summable fun j => cbNorm (4 * d + 42) (D.f (σ j)) :=
    Summable.of_nonneg_of_le (fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _) (fun j => hle (σ j)) hWσ
  refine ⟨⟨fun j => by show MemCb _ (D.f (σ j)); rw [hD (σ j)]; exact (h.2.1 bw hbw _ _).1, hsum⟩, ?_, fun j => hle (σ j)⟩
  unfold featureSum s21iS0
  calc ∑' j, cbNorm (4 * d + 42) (D.f (σ j)) ≤ ∑' j, s21iW d Corb (σ j) :=
        Summable.tsum_le_tsum (fun j => hle (σ j)) hsum hWσ
    _ = ∑' q, s21iW d Corb q := Equiv.tsum_eq σ (fun q => s21iW d Corb q)

end HRS.MS.S21
