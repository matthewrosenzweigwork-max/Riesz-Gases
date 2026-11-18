import HRS.MC.S7FCH2C
import HRS.MC.S7FCW6G2

/-!
# H2, part D: summing the weights, the tail of the modes, and dominated convergence in `t`

* `S7FCH2_wsum_le`: `∑_k ⟨k⟩^{4-2r-2q} w_k ≤ (mode tail of `C₂ ⟨k⟩^{4-2r}` outside `S`) + ∑_{k ∈ S} ε_k`;
* `S7FCH2_tail_small`: the mode tail is `≤ η` for all `S ⊇ S₀`;
* `S7FCH2_g_aemeasurable`: `t ↦ E |N F^{K - h_k}(X_t, μ_t)|^q` is `AEMeasurable` on `[0,T]` (Carathéodory modification);
* `S7FCH2_dct`: `∫⁻_{[0,T]} sup_N E|N F^{K_L - h_k}|^q dt → 0` as `L → ∞` (FC-G pointwise in `t`, G2 uniform bound).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH2

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan
  HRS.MC.Sec7.S7FCF5F

variable {d : ℕ}

open Classical in
/-- The mode tail `∑_{k ∉ S} C₂ ⟨k⟩^{4-2r}`. -/
def S7FCH2_tail (d : ℕ) (r C2 : ℝ) (S : Finset (NonzeroLattice d)) : ℝ≥0∞ :=
  ∑' k : NonzeroLattice d, if k ∈ S then 0 else ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (4 - 2 * r))

theorem S7FCH2_wsum_le (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (q : ℝ) (hq : 2 ≤ q) (S : Finset (NonzeroLattice d))
    (C2 : ℝ) (hC2 : 0 ≤ C2) (ε : NonzeroLattice d → ℝ≥0∞) :
    ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * S7FCH2_wu S C2 q ε k ≤
      S7FCH2_tail d r C2 S + ∑ k ∈ S, ε k := by
  classical
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have pt : ∀ k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * S7FCH2_wu S C2 q ε k ≤
      (if k ∈ S then 0 else ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (4 - 2 * r))) + (if k ∈ S then ε k else 0) := by
    intro k
    by_cases hk : k ∈ S
    · simp only [S7FCH2_wu, if_pos hk, zero_add]
      have h1 : ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal (Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one k.1) ?_)
        rw [hr]; nlinarith
      calc ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * ε k ≤ 1 * ε k := by gcongr
        _ = ε k := one_mul _
    · simp only [S7FCH2_wu, if_neg hk, add_zero]
      refine le_of_eq ?_
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hjp k).le _), S7FCF5F_exp_id (hjp k) r q C2]
  calc _ ≤ ∑' k : NonzeroLattice d, ((if k ∈ S then 0 else ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (4 - 2 * r))) +
        (if k ∈ S then ε k else 0)) := ENNReal.tsum_le_tsum pt
    _ = S7FCH2_tail d r C2 S + ∑' k : NonzeroLattice d, (if k ∈ S then ε k else 0) := ENNReal.tsum_add
    _ = S7FCH2_tail d r C2 S + ∑ k ∈ S, ε k := by
        congr 1
        rw [tsum_eq_sum (s := S) (fun k hk => if_neg hk)]
        exact Finset.sum_congr rfl fun k hk => if_pos hk

theorem S7FCH2_tail_small (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (C2 : ℝ) (hC2 : 0 ≤ C2) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ S₀ : Finset (NonzeroLattice d), ∀ S : Finset (NonzeroLattice d), S₀ ⊆ S → S7FCH2_tail d r C2 S ≤ η := by
  classical
  have hsum : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (4 - 2 * r) :=
    HRS.MC.Sec7.S7FCF5B.fcf5_D1a_summable_proof r hr
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hne : ∑' k : NonzeroLattice d, ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (4 - 2 * r)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun k : NonzeroLattice d => C2 * Lattice.jp k.1 ^ (4 - 2 * r))
      (fun k => mul_nonneg hC2 (Real.rpow_nonneg (hjp k).le _)) (hsum.mul_left C2)]
    exact ENNReal.ofReal_ne_top
  have ht := ENNReal.tendsto_tsum_compl_atTop_zero hne
  obtain ⟨S₀, hS₀⟩ := Filter.eventually_atTop.1 (ht.eventually (ge_mem_nhds hη))
  refine ⟨S₀, fun S hS => ?_⟩
  have h1 := hS₀ S hS
  have h2 : S7FCH2_tail d r C2 S = ∑' b : { x // x ∉ S }, ENNReal.ofReal (C2 * Lattice.jp (b : NonzeroLattice d).1 ^ (4 - 2 * r)) := by
    have := tsum_subtype ((↑S : Set (NonzeroLattice d))ᶜ)
      (fun k : NonzeroLattice d => ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (4 - 2 * r)))
    unfold S7FCH2_tail
    refine Eq.trans ?_ this.symm
    refine tsum_congr fun k => ?_
    by_cases hk : k ∈ S
    · simp [hk]
    · simp [hk]
  rw [h2]
  exact h1

/-! ### Measurability in `t` and dominated convergence -/

/-- `g_{N,L,k}(t) = E |N F^{K_{k,L} - h_{∇e_k}}(X_t, μ_t)|^q` (as a `lintegral`). -/
def S7FCH2_g (R : Regime d) (q : ℝ) (Kf : FRKernel d) (k : NonzeroLattice d) {N : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy
    (fun x y => Kf.toFun x y - hTransport d R.D.s (Torus.realMode k) x y) (X t.toNNReal ω)
    (withDensityReal (R.ρ t))| ^ q) ∂P

theorem S7FCH2_g_aemeasurable (R : Regime d) (T : ℝ) (hT : 0 < T) (q : ℝ) (Kf : FRKernel d) (k : NonzeroLattice d)
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    AEMeasurable (fun t : ℝ => S7FCH2_g R q Kf k P X t) (volume.restrict (Set.Icc 0 T)) := by
  have hc0 : ∀ᵐ ω ∂P, ContinuousOn (fun t : ℝ => X t.toNNReal ω) (Set.Icc 0 T) :=
    hcont.mono fun ω hω => (continuous_pi fun i => (hω i).comp continuous_real_toNNReal).continuousOn
  obtain ⟨V, hVm, N0, -, hN0, hVN⟩ := HRS.MC.Sec7.S7FCW12.s7fcw12_caratheodory P hT.le
    (fun t ω => X t.toNNReal ω) (fun t => hadapt _) hc0 (fun _ => 0)
  have hsd : R.D.s < d := alltime_hsd R
  have hhm : Measurable fun p : Torus d × Torus d =>
      Kf.toFun p.1 p.2 - hTransport d R.D.s (Torus.realMode k) p.1 p.2 :=
    (S7FCH2_fr_cont Kf).measurable.sub (HRS.MC.Sec7.S7FCW12.s7fcw12_meas_hTransport R.D.s hsd _)
  have hρ : Measurable fun p : ℝ × Torus d => HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos R (p.1, p.2) :=
    (HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos_measurable R).comp measurable_id
  obtain ⟨Psi, hPsi_def⟩ : ∃ Psi : ℝ × Config d N → ℝ≥0∞, Psi = fun p => ENNReal.ofReal (|(N : ℝ) * modulatedEnergy
      (fun x y => Kf.toFun x y - hTransport d R.D.s (Torus.realMode k) x y) p.2
      (withDensityReal fun y => HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos R (p.1, y))| ^ q) := ⟨_, rfl⟩
  have hΨ : Measurable Psi := by
    rw [hPsi_def]
    exact ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp (measurable_const.mul
      (HRS.MC.Sec7.S7FCW12.s7fcw12_meas_modEnergy _ hhm
        (fun t y => HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos R (t, y)) hρ))).pow_const q)
  obtain ⟨F, hF_def⟩ : ∃ F : ℝ × Ω → ℝ≥0∞, F = fun p => Psi (p.1, V p.1 p.2) := ⟨_, rfl⟩
  have hF : Measurable F := by
    rw [hF_def]
    exact hΨ.comp (measurable_fst.prodMk hVm)
  have hG := hF.lintegral_prod_right' (ν := P)
  refine hG.aemeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
  have hμ : withDensityReal (R.ρ t) =
      withDensityReal fun y => HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos R (t, y) := by
    congr 1
    funext y
    rw [HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos_eq R ht.1 y]
  show ∫⁻ ω, F (t, ω) ∂P = S7FCH2_g R q Kf k P X t
  unfold S7FCH2_g
  refine lintegral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  rw [hF_def]
  show Psi (t, V t ω) = _
  rw [hPsi_def]
  show ENNReal.ofReal (|(N : ℝ) * modulatedEnergy
      (fun x y => Kf.toFun x y - hTransport d R.D.s (Torus.realMode k) x y) (V t ω)
      (withDensityReal fun y => HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos R (t, y))| ^ q) = _
  rw [hVN ω hω t ht, ← hμ]

/-- The supremum over `N ≥ 2` of `g_{N,L,k}(t)`. -/
def S7FCH2_phi (R : Regime d) (q : ℝ) (Kf : FRKernel d) (k : NonzeroLattice d) {Ω : ℕ → Type}
    [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N)) (X : ∀ N, ℝ≥0 → Ω N → Config d N) (t : ℝ) : ℝ≥0∞ :=
  ⨆ N : {N : ℕ // 2 ≤ N}, S7FCH2_g R q Kf k (P N) (X N) t

theorem S7FCH2_phi_aemeasurable (R : Regime d) (T : ℝ) (hT : 0 < T) (q : ℝ) (Kf : FRKernel d) (k : NonzeroLattice d)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N)) :
    AEMeasurable (fun t => S7FCH2_phi R q Kf k P X t) (volume.restrict (Set.Icc 0 T)) := by
  refine AEMeasurable.iSup fun N => ?_
  have hS := (hreal N.1 (by omega)).solution T
  exact S7FCH2_g_aemeasurable R T hT q Kf k (P N) (X N) hS.adapted hS.cont

theorem S7FCH2_dct (R : Regime d) (T : ℝ) (hT : 0 < T) {ε₂ c : ℝ} (K : NonzeroLattice d → ℕ → FRKernel d)
    (hK : FCKernelData R ε₂ c K)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    (q : ℝ) (hq : 1 ≤ q) (k : NonzeroLattice d) :
    Tendsto (fun L : ℕ => ∫⁻ t in Set.Icc (0 : ℝ) T, S7FCH2_phi R q (K k L) k P X t) atTop (𝓝 0) := by
  obtain ⟨hc, hε, hεs, hKB, hKc⟩ := hK
  obtain ⟨B, hB⟩ := hKB k
  have hLd : ∀ L, s7_IsFiniteRankSmooth (fun x y => (K k L).toFun x y) := fun L =>
    ⟨(K k L).n, (K k L).f, (K k L).c, (K k L).smooth, (K k L).symm, fun x y => rfl⟩
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7FCW6.s7_FC_G2_unif_proof R T hT k (fun L => (K k L).toFun) hLd B c hc
    (fun L x y hxy => hB L x y hxy) P X₀ W X hreal q hq
  have hmeas : ∀ L : ℕ, AEMeasurable (fun t => S7FCH2_phi R q (K k L) k P X t) (volume.restrict (Set.Icc 0 T)) := by
    intro L
    exact S7FCH2_phi_aemeasurable R T hT q (K k L) k P X₀ W X hreal
  have hbound : ∀ L : ℕ, (fun t => S7FCH2_phi R q (K k L) k P X t) ≤ᵐ[volume.restrict (Set.Icc 0 T)]
      fun _ => ENNReal.ofReal C := by
    intro L
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    exact iSup_le fun N => hC L N.1 N.2 t ht
  have hlim : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun L : ℕ => S7FCH2_phi R q (K k L) k P X t) atTop (𝓝 ((fun _ => (0 : ℝ≥0∞)) t)) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    exact HRS.MC.Sec7.FCG.s7_FC_G_strong_tail_proof R T hT k (fun L => (K k L).toFun) hLd B c hc
      (fun L x y hxy => hB L x y hxy) P X₀ W X hreal ε₂ hε hεs (hKc k) t ht q hq
  have := tendsto_lintegral_of_dominated_convergence' (μ := volume.restrict (Set.Icc (0 : ℝ) T))
    (F := fun L t => S7FCH2_phi R q (K k L) k P X t) (f := fun _ => (0 : ℝ≥0∞)) (fun _ => ENNReal.ofReal C)
    hmeas hbound (by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hlim
  simpa using this

end HRS.MC.Sec7.S7FCH2

end
