import HRS.MS.SA12K9

/-!
# S.A.12 C1, the level hypothesis of `ToriConv` along a diagonal family

For any function `τh : ℝ → [0,T]` with `τh(L) → τs`, the family `g_L = η_{1/L} * perL_L(Z⁻¹ ζ_L ρ(τh L))` satisfies
`tcv_Lvl d j g_L (ρ τs)` for `j ≤ m + 1`: the uniform bounds, local uniform convergence, and uniform tails.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB HRS.MS.ToriConv

variable {d : ℕ}

theorem sa12k_le_infty (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

theorem sa12k_tca_g_le_one (y : Euc d) : tca_g y ≤ 1 := by
  unfold tca_g
  exact Real.rpow_le_one_of_one_le_of_nonpos (tca_one_le_jbracket y)
    (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])

/-- The mollification error of a jet of a regular density. -/
theorem sa12k_jet_moll_err {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ)
    {BG : ℝ} (hBG : ∀ τ ∈ Icc (0 : ℝ) T, ∀ i ≤ m + 3, ∀ w : Euc d, ‖iteratedFDeriv ℝ i (ρ τ) w‖ ≤ BG)
    {δ : ℝ} {η : Euc d → ℝ} (hη : SA12KMoll δ η) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {i : ℕ}
    (hi : i ≤ m + 2) (y : Euc d) :
    ‖sa12k_moll η (iteratedFDeriv ℝ i (ρ τ)) y - iteratedFDeriv ℝ i (ρ τ) y‖ ≤ BG * δ := by
  have hcd : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (ρ τ) := (sa12k_den_facts hρ hτ).1
  have hfc : Continuous (iteratedFDeriv ℝ i (ρ τ)) :=
    hcd.continuous_iteratedFDeriv (by exact_mod_cast (by omega : i ≤ m + 3))
  have hBG0 : 0 ≤ BG := (norm_nonneg _).trans (hBG τ hτ 0 (by omega) 0)
  refine sa12k_moll_err hη hfc y (fun u hu => ?_)
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i (ρ τ)) :=
    hcd.differentiable_iteratedFDeriv (by exact_mod_cast (by omega : i < m + 3))
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := iteratedFDeriv ℝ i (ρ τ))
    (C := BG) (s := univ) (x := y) (y := y - u) (fun z _ => hdiff z)
    (fun z _ => by
      rw [norm_fderiv_iteratedFDeriv]
      exact hBG τ hτ (i + 1) (by omega) z)
    convex_univ (mem_univ _) (mem_univ _)
  calc _ ≤ BG * ‖y - u - y‖ := this
    _ = BG * ‖u‖ := by rw [sub_sub_cancel_left, norm_neg]
    _ ≤ BG * δ := mul_le_mul_of_nonneg_left hu hBG0

set_option maxHeartbeats 4000000 in
theorem sa12k_lvl_diag (s : ℝ) (m : ℕ) (T Λ : ℝ) (ζ : Euc d → ℝ)
    (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ)
    {τh : ℝ → ℝ} (hτh : ∀ L, τh L ∈ Icc (0 : ℝ) T) {τs : ℝ} (hτs : τs ∈ Icc (0 : ℝ) T)
    (htend : Tendsto τh atTop (𝓝 τs)) {j : ℕ} (hj : j ≤ m + 1) :
    tcv_Lvl d j (fun L => sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ (τh L)) L)) (ρ τs) := by
  obtain ⟨Bd, Bc, L₁, hBd0, hBc0, hL₁, hbase⟩ := sa12k_base s m T Λ ζ hζ
  obtain ⟨BG, hBG0, hBGw⟩ := sa12k_den_weight hρ
  have hBGb : ∀ τ ∈ Icc (0 : ℝ) T, ∀ i ≤ m + 3, ∀ w : Euc d, ‖iteratedFDeriv ℝ i (ρ τ) w‖ ≤ BG :=
    fun τ hτ i hi w => (hBGw τ hτ i hi w).trans
      (mul_le_of_le_one_right hBG0 (sa12k_tca_g_le_one w))
  have hρcd : ∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (ρ τ) :=
    fun τ hτ => (sa12k_den_facts hρ hτ).1
  -- base facts at every `(L, τh L)`
  have hb := fun L (hL : L₁ ≤ L) => hbase ρ hρ L hL (τh L) (hτh L)
  refine ⟨L₁, Bd + BG, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L hL
    obtain ⟨-, -, -, hμcd, -⟩ := hb L hL
    exact (sa12k_moll_contDiff (sa12k_etaL_moll L) hμcd.continuous).of_le
      (sa12k_le_infty (j + 2))
  · exact (hρcd τs hτs).of_le (by exact_mod_cast (by omega : j + 2 ≤ m + 3))
  · intro L hL i hi y
    obtain ⟨-, -, -, hμcd, hμbd, -⟩ := hb L hL
    have h1 := sa12k_moll_iter (sa12k_etaL_moll L) hμcd hμbd i (by omega)
    rw [congrFun h1 y]
    have hcont : Continuous (iteratedFDeriv ℝ i (sa12k_mu0 ζ (ρ (τh L)) L)) :=
      hμcd.continuous_iteratedFDeriv (by exact_mod_cast (by omega : i ≤ m + 3))
    exact (sa12k_moll_norm_le (sa12k_etaL_moll L) hcont (fun y' => hμbd i (by omega) y') y).trans
      (by linarith)
  · intro i hi y
    exact (hBGb τs hτs i (by omega) y).trans (by linarith)
  · intro i hi
    have hcont : Continuous fun y : Euc d => ‖iteratedFDeriv ℝ i (ρ τs) y‖ :=
      ((hρcd τs hτs).continuous_iteratedFDeriv (by exact_mod_cast (by omega : i ≤ m + 3))).norm
    refine Integrable.mono' (tca_g_integrable.const_mul BG) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_norm]
    exact hBGw τs hτs i (by omega) y
  · -- local uniform convergence
    intro i hi K hK η hη
    obtain ⟨RK, hRK⟩ := hK.isBounded.exists_norm_le
    obtain ⟨N, hN⟩ := sa12k_Z_close_unif hρ hζ (ε := η / (6 * (BG + 1))) (by positivity)
    obtain ⟨r, hr, hjet⟩ := sa12k_jet_uc hρ hK (i := i) (by omega) hτs (η := η / 3) (by positivity)
    obtain ⟨L₃, hL₃⟩ := Metric.tendsto_atTop.1 htend r hr
    refine ⟨max (max L₁ (4 * (N : ℝ) + 1)) (max (4 * (|RK| + 1) + 1) (max (3 * BG / η + 1) L₃)), ?_⟩
    intro L hL y hy
    have hLa : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
    have hLb : 4 * (N : ℝ) + 1 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
    have hLc : 4 * (|RK| + 1) + 1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
    have hLd : 3 * BG / η + 1 ≤ L :=
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
    have hLe : L₃ ≤ L :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
    have hL1 : 1 ≤ L := by linarith [hL₁]
    have hL0 : 0 < L := by linarith
    set τ := τh L with hτdef
    have hτI : τ ∈ Icc (0 : ℝ) T := hτh L
    obtain ⟨hZ, hvan, hf0cd, hμcd, hμbd, -⟩ := hb L hLa
    have hη₀ := sa12k_etaL_moll (d := d) L
    have hδL : sa12k_rad L ≤ 1 / L := sa12k_rad_le_inv hL1
    have hδ1 : sa12k_rad L ≤ 1 := sa12k_rad_le_one L
    -- the normalising constant
    set Z : ℝ := ∫ y, ζ (L⁻¹ • y) * ρ τ y with hZdef
    have hZc : |Z - 1| ≤ η / (6 * (BG + 1)) := hN L hL0 (by linarith) τ hτI
    have hc := tcv_inv_sub hZ
    have hcl : |Z⁻¹ - 1| ≤ η / (3 * (BG + 1)) := by
      refine hc.trans ?_
      have : 2 * (η / (6 * (BG + 1))) = η / (3 * (BG + 1)) := by field_simp; ring
      rw [← this]; linarith
    -- the jet of `μ0`
    have h1 := sa12k_moll_iter hη₀ hμcd hμbd i (by omega)
    have hcongr : sa12k_moll (sa12k_etaL L) (iteratedFDeriv ℝ i (sa12k_mu0 ζ (ρ τ) L)) y =
        sa12k_moll (sa12k_etaL L) (fun y' => Z⁻¹ • iteratedFDeriv ℝ i (ρ τ) y') y := by
      refine sa12k_moll_congr hη₀ y fun u hu => ?_
      have hy1 : ‖y - u‖ < L / 4 := by
        have h2 := hRK y hy
        have h3 : ‖y - u‖ ≤ ‖y‖ + ‖u‖ := norm_sub_le _ _
        have h4 : ‖u‖ ≤ 1 := hu.trans hδ1
        have : |RK| ≥ RK := le_abs_self RK
        linarith
      exact tcv_mu_near hζ hL0 i (ρ τ) ((hρcd τ hτI).of_le (by exact_mod_cast (by omega : i ≤ m + 3)))
        Z⁻¹ (y - u) hy1
    show ‖iteratedFDeriv ℝ i (sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L)) y -
      iteratedFDeriv ℝ i (ρ τs) y‖ ≤ η
    rw [congrFun h1 y, hcongr, sa12k_moll_smul]
    set Mv := sa12k_moll (sa12k_etaL L) (iteratedFDeriv ℝ i (ρ τ)) y with hMv
    have hfcont : Continuous (iteratedFDeriv ℝ i (ρ τ)) :=
      (hρcd τ hτI).continuous_iteratedFDeriv (by exact_mod_cast (by omega : i ≤ m + 3))
    have hMn : ‖Mv‖ ≤ BG :=
      sa12k_moll_norm_le hη₀ hfcont (fun w => hBGb τ hτI i (by omega) w) y
    have hMerr : ‖Mv - iteratedFDeriv ℝ i (ρ τ) y‖ ≤ BG * sa12k_rad L :=
      sa12k_jet_moll_err hρ hBGb hη₀ hτI (by omega) y
    have hMerr' : BG * sa12k_rad L ≤ η / 3 := by
      have h5 : BG * sa12k_rad L ≤ BG * (1 / L) := mul_le_mul_of_nonneg_left hδL hBG0
      have h6 : BG * (1 / L) ≤ η / 3 := by
        rw [mul_one_div, div_le_iff₀ hL0]
        have : 3 * BG / η + 1 ≤ L := hLd
        have h7 : 3 * BG / η ≤ L := by linarith
        rw [div_le_iff₀ hη] at h7
        nlinarith
      linarith
    have hdt : dist τ τs < r := hL₃ L hLe
    have hP := hjet τ hτI (by rwa [Real.dist_eq] at hdt) y hy
    have hcM : ‖(Z⁻¹ - 1) • Mv‖ ≤ η / 3 := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |Z⁻¹ - 1| * ‖Mv‖ ≤ (η / (3 * (BG + 1))) * BG :=
            mul_le_mul hcl hMn (norm_nonneg _) (by positivity)
        _ ≤ η / 3 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_nonneg hη.le hBG0]
    calc ‖Z⁻¹ • Mv - iteratedFDeriv ℝ i (ρ τs) y‖
        = ‖(Z⁻¹ - 1) • Mv + (Mv - iteratedFDeriv ℝ i (ρ τ) y) +
            (iteratedFDeriv ℝ i (ρ τ) y - iteratedFDeriv ℝ i (ρ τs) y)‖ := by
          congr 1; rw [sub_smul, one_smul]; abel
      _ ≤ ‖(Z⁻¹ - 1) • Mv‖ + ‖Mv - iteratedFDeriv ℝ i (ρ τ) y‖ +
            ‖iteratedFDeriv ℝ i (ρ τ) y - iteratedFDeriv ℝ i (ρ τs) y‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ η := by linarith
  · -- tails
    intro i hi K hK ε hε
    obtain ⟨RK, hRK⟩ := hK.isBounded.exists_norm_le
    have hD2 : (0 : ℝ) < 2 ^ d * (Bd + BG + 1) := by positivity
    have hε' : 0 < ε / (2 ^ d * (Bd + BG + 1)) := div_pos hε hD2
    obtain ⟨N, hN⟩ := tca_tail (d := d) _ hε'
    set ε' : ℝ := ε / (2 ^ d * (Bd + BG + 1)) with hε'def
    have hε'mul : 2 ^ d * (Bd + BG + 1) * ε' = ε := by rw [hε'def]; field_simp
    have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    refine ⟨(N : ℝ) + |RK| + 1, fun R hR => ⟨max L₁ (2 * R), fun L hL x hx => ?_⟩⟩
    have hLa : L₁ ≤ L := (le_max_left _ _).trans hL
    have hLR : 2 * R ≤ L := (le_max_right _ _).trans hL
    have hL0 : 0 < L := by linarith [hL₁]
    have hRL : R ≤ L / 2 := by linarith
    have hRKx : ‖x‖ ≤ |RK| := (hRK x hx).trans (le_abs_self _)
    set τ := τh L with hτdef
    have hτI : τ ∈ Icc (0 : ℝ) T := hτh L
    obtain ⟨hZ, hvan, hf0cd, hμcd, hμbd, hfw, -⟩ := hb L hLa
    have hη₀ := sa12k_etaL_moll (d := d) L
    have h1 := sa12k_moll_iter hη₀ hμcd hμbd i (by omega)
    have hmu_c : Continuous (iteratedFDeriv ℝ i (sa12k_mu0 ζ (ρ τ) L)) :=
      hμcd.continuous_iteratedFDeriv (by exact_mod_cast (by omega : i ≤ m + 3))
    have hBdε : 2 ^ d * Bd * ε' ≤ ε := by
      rw [← hε'mul]
      have : 0 ≤ ε' := hε'.le
      nlinarith [mul_nonneg hBG0 this, mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ d) this]
    constructor
    · have hA : MeasurableSet (tcb_Q d L ∩ {z : Euc d | R < ‖z‖}) :=
        (tcb_measurableSet_Q L).inter (measurableSet_lt measurable_const measurable_norm)
      have hAfin : volume (tcb_Q d L ∩ {z : Euc d | R < ‖z‖}) < ⊤ :=
        lt_of_le_of_lt (measure_mono Set.inter_subset_left) (tcb_measure_Q_lt_top L)
      have key := sa12k_set_moll_le hη₀ hmu_c (B := Bd) (fun y => hμbd i (by omega) y) hA hAfin x
        (E := 2 ^ d * Bd * ε') (fun u hu => by
          have hu1 : ‖u‖ ≤ 1 := hu.trans (sa12k_rad_le_one L)
          have hct := tcv_cube_tail hL0 (sa12k_f0 ζ (ρ τ) L) hvan i Bd
            (fun w => hfw i (by omega) w) (x - u) R hRL
          have hmono := tcv_tail_mono (d := d) (N := N) (r := R - ‖x - u‖) (by
            have : ‖x - u‖ ≤ ‖x‖ + ‖u‖ := norm_sub_le _ _
            linarith)
          refine hct.trans ?_
          exact mul_le_mul_of_nonneg_left (hmono.trans hN) (by positivity))
      have e : (fun z => ‖iteratedFDeriv ℝ i (sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L)) (x - z)‖) =
          fun z => ‖sa12k_moll (sa12k_etaL L) (iteratedFDeriv ℝ i (sa12k_mu0 ζ (ρ τ) L)) (x - z)‖ := by
        funext z; rw [congrFun h1 (x - z)]
      show ∫ z in tcb_Q d L ∩ {z : Euc d | R < ‖z‖},
        ‖iteratedFDeriv ℝ i (sa12k_moll (sa12k_etaL L) (sa12k_mu0 ζ (ρ τ) L)) (x - z)‖ ≤ ε
      rw [e]
      exact key.trans hBdε
    · have hcontg : Continuous fun w : Euc d => ‖iteratedFDeriv ℝ i (ρ τs) w‖ :=
        ((hρcd τs hτs).continuous_iteratedFDeriv (by exact_mod_cast (by omega : i ≤ m + 3))).norm
      have := tcv_euc_tail (fun w => ‖iteratedFDeriv ℝ i (ρ τs) w‖) BG hBG0
        (fun w => hBGw τs hτs i (by omega) w) (fun w => norm_nonneg _) hcontg x R
      refine this.trans ?_
      have hmono := tcv_tail_mono (d := d) (N := N) (r := R - ‖x‖) (by linarith)
      calc BG * ∫ u in {u : Euc d | R - ‖x‖ ≤ ‖u‖}, tca_g u ≤ BG * ε' :=
            mul_le_mul_of_nonneg_left (hmono.trans hN) hBG0
        _ ≤ ε := by
          rw [← hε'mul]
          have : 0 ≤ ε' := hε'.le
          nlinarith [mul_nonneg hBd0 this, mul_nonneg hBG0 this]

end HRS.MH.AdjointRd.Phase2SA12Construction
