import HRS.MS.WadAux12
import HRS.MS.WadAux10
import HRS.MS.WadAux6
import HRS.MS.SpecAux11

/-!
# S8.3, packet D3 (part 2): compactness of the cutoff Mehler operator on `C_M`, transported to `C₀`

The weighted space `C_M` is identified with `C₀(ℝ^d, 𝕜)` through `h ↦ ⟨y⟩^M h` (`s83_wf`).  For a continuous
compactly supported cutoff `χ` the operator `h ↦ χ ⟨x⟩^{-M} P_t(⟨·⟩^M h)` (`s83_cutOp`) is a continuous linear
map `C₀ →L[𝕜] C₀`, and it is compact (`s83_cutOp_isCompact`): the Lipschitz smoothing `s83_G_lip` gives the
uniform equicontinuity on compact sets needed by `HRS.MS.Spec.s8p_isCompactOperator_of_c0`.
This is the compactness of `χ_R P^0_t` of the S8.3 proof (the remainder `(1-χ_R)P^0_1` is controlled by
`s83_P_tail_bound`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ZeroAtInfty

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- `h ↦ ⟨y⟩^M h(y)`. -/
def s83_wf (M : ℝ) (h : Euc d → 𝕜) : Euc d → 𝕜 := fun y => jbracket y ^ M • h y

theorem s83_jb_rpow_cont (M : ℝ) : Continuous fun y : Euc d => jbracket y ^ M := by
  unfold jbracket
  exact Continuous.rpow_const (by fun_prop) fun z => Or.inl (by
    have := (s83_jb_pos z).ne'; unfold jbracket at this; exact this)

theorem s83_wf_cont (M : ℝ) (h : C₀(Euc d, 𝕜)) : Continuous (s83_wf M h) :=
  (s83_jb_rpow_cont M).smul h.continuous

theorem s83_wf_wt (M : ℝ) (h : C₀(Euc d, 𝕜)) : Wt M ‖h‖ (s83_wf M h) := fun y => by
  unfold s83_wf
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (s83_jb_pos y).le _), mul_comm]
  exact mul_le_mul_of_nonneg_right (h.toBCF.norm_coe_le_norm y |>.trans_eq
    (ZeroAtInftyContinuousMap.norm_toBCF_eq_norm)) (Real.rpow_nonneg (s83_jb_pos y).le _)

theorem s83_G_smul_rc (c σ : ℝ) (r : 𝕜) (f : Euc d → 𝕜) :
    s83_G c σ (r • f) = r • s83_G c σ f := by
  funext x
  simp only [s83_G, Pi.smul_apply]
  exact integral_smul r _

theorem s83_wf_add (M : ℝ) (h₁ h₂ : Euc d → 𝕜) : s83_wf M (h₁ + h₂) = s83_wf M h₁ + s83_wf M h₂ := by
  funext y; simp [s83_wf, smul_add]

theorem s83_wf_smul (M : ℝ) (r : 𝕜) (h : Euc d → 𝕜) : s83_wf M (r • h) = r • s83_wf M h := by
  funext y; simp [s83_wf, smul_comm]

section Cut

variable {M : ℝ} {χ : Euc d → ℝ} {a ν t : ℝ}

/-- The transported cutoff Mehler operator as a function of `h ∈ C₀`. -/
def s83_cutFun (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hM : 0 ≤ M) (ha : 0 < a)
    (hν : 0 ≤ ν) (ht : 0 ≤ t) (h : C₀(Euc d, 𝕜)) : C₀(Euc d, 𝕜) where
  toFun x := (χ x * (jbracket x ^ M)⁻¹) • s83_P a ν t (s83_wf M h) x
  continuous_toFun := by
    have hP := s83_G_continuous (s83_wf_cont M h) hM (s83_wf_wt M h)
      (s83_abs_mc_le_one ha.le ht) (s83_abs_ms_le ha hν ht)
    exact (hχ.mul ((s83_jb_rpow_cont M).inv₀ fun y =>
      (Real.rpow_pos_of_pos (s83_jb_pos y) _).ne')).smul hP
  zero_at_infty' := by
    have hev : ∀ᶠ x in cocompact (Euc d), χ x = 0 := by
      have : (tsupport χ)ᶜ ∈ cocompact (Euc d) := hχc.compl_mem_cocompact
      filter_upwards [this] with x hx
      exact image_eq_zero_of_notMem_tsupport hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with x hx
    simp [hx]

theorem s83_cutFun_apply (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hM : 0 ≤ M) (ha : 0 < a)
    (hν : 0 ≤ ν) (ht : 0 ≤ t) (h : C₀(Euc d, 𝕜)) (x : Euc d) :
    s83_cutFun hχ hχc hM ha hν ht h x = (χ x * (jbracket x ^ M)⁻¹) • s83_P a ν t (s83_wf M h) x :=
  rfl

/-- The linear map. -/
def s83_cutLin (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hM : 0 ≤ M) (ha : 0 < a)
    (hν : 0 ≤ ν) (ht : 0 ≤ t) : C₀(Euc d, 𝕜) →ₗ[𝕜] C₀(Euc d, 𝕜) where
  toFun := s83_cutFun hχ hχc hM ha hν ht
  map_add' h₁ h₂ := by
    ext x
    simp only [s83_cutFun_apply, ZeroAtInftyContinuousMap.coe_add, Pi.add_apply]
    rw [s83_wf_add, ← smul_add]
    congr 1
    unfold s83_P
    rw [s83_G_add (s83_wf_cont M h₁) (s83_wf_cont M h₂) hM (s83_wf_wt M h₁) (s83_wf_wt M h₂) _
      (s83_abs_ms_le ha hν ht)]
    rfl
  map_smul' r h := by
    ext x
    simp only [s83_cutFun_apply, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply]
    rw [s83_wf_smul, smul_comm]
    congr 1
    unfold s83_P
    rw [s83_G_smul_rc]
    rfl

/-- Operator norm bound of the cutoff operator. -/
theorem s83_cutFun_norm_le (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hM : 0 ≤ M) (ha : 0 < a)
    (hν : 0 ≤ ν) (ht : 0 ≤ t) {Cχ : ℝ} (hCχ : ∀ x, |χ x| ≤ Cχ) (h : C₀(Euc d, 𝕜)) :
    ‖s83_cutFun hχ hχc hM ha hν ht h‖ ≤
      Cχ * (2 ^ M * mom d M (Real.sqrt (ν / a))) * ‖h‖ := by
  have hCχ0 : 0 ≤ Cχ := (abs_nonneg _).trans (hCχ 0)
  have hK : 0 ≤ 2 ^ M * mom d M (Real.sqrt (ν / a)) :=
    mul_nonneg (by positivity) (s83_mom_nonneg _ _ (Real.sqrt_nonneg _))
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_
  show ‖s83_cutFun hχ hχc hM ha hν ht h x‖ ≤ _
  rw [s83_cutFun_apply, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (inv_nonneg.2 (Real.rpow_nonneg (s83_jb_pos x).le _))]
  have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
  have hP := s83_P_wt (s83_wf_cont M h) hM (s83_wf_wt M h) ha hν ht x
  calc |χ x| * (jbracket x ^ M)⁻¹ * ‖s83_P a ν t (s83_wf M h) x‖
      ≤ Cχ * (jbracket x ^ M)⁻¹ * (‖h‖ * 2 ^ M * mom d M (Real.sqrt (ν / a)) * jbracket x ^ M) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (hCχ x) (inv_nonneg.2 hp.le)) hP
          (norm_nonneg _) (mul_nonneg hCχ0 (inv_nonneg.2 hp.le))
    _ = Cχ * (2 ^ M * mom d M (Real.sqrt (ν / a))) * ‖h‖ := by
        field_simp

/-- The continuous linear map `C₀ →L C₀`. -/
def s83_cutOp (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hM : 0 ≤ M) (ha : 0 < a)
    (hν : 0 ≤ ν) (ht : 0 ≤ t) {Cχ : ℝ} (hCχ : ∀ x, |χ x| ≤ Cχ) :
    C₀(Euc d, 𝕜) →L[𝕜] C₀(Euc d, 𝕜) :=
  LinearMap.mkContinuous (s83_cutLin hχ hχc hM ha hν ht)
    (Cχ * (2 ^ M * mom d M (Real.sqrt (ν / a)))) (s83_cutFun_norm_le hχ hχc hM ha hν ht hCχ)

theorem s83_cutOp_apply (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hM : 0 ≤ M) (ha : 0 < a)
    (hν : 0 ≤ ν) (ht : 0 ≤ t) {Cχ : ℝ} (hCχ : ∀ x, |χ x| ≤ Cχ) (h : C₀(Euc d, 𝕜)) (x : Euc d) :
    s83_cutOp hχ hχc hM ha hν ht hCχ h x =
      (χ x * (jbracket x ^ M)⁻¹) • s83_P a ν t (s83_wf M h) x := rfl

end Cut

section Compact

variable {M : ℝ} {χ : Euc d → ℝ} {a ν t : ℝ}

theorem s83_exp_half_le : Real.exp (1 / 2) ≤ 2 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

set_option maxHeartbeats 1600000 in
/-- **Compactness of `χ P_t` on `C_M`** (transported to `C₀`): for a continuous compactly supported `χ`,
`M ≥ 0`, `a, ν, t > 0`, the operator `h ↦ χ ⟨x⟩^{-M} P_t(⟨·⟩^M h)` is a compact operator on `C₀(ℝ^d, ℝ)`. -/
theorem s83_cutOp_isCompact (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hM : 0 ≤ M)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t) {Cχ : ℝ} (hCχ : ∀ x, |χ x| ≤ Cχ) :
    IsCompactOperator (s83_cutOp (𝕜 := ℝ) hχ hχc hM ha hν.le ht.le hCχ) := by
  have hCχ0 : 0 ≤ Cχ := (abs_nonneg _).trans (hCχ 0)
  set σ₀ := Real.sqrt (ν / a) with hσ₀
  have hmc0 := s83_mc_pos a t
  have hmc1 := s83_mc_le_one ha.le ht.le
  have hms0 := s83_ms_pos ha hν ht
  have hmsb := s83_abs_ms_le ha hν.le ht.le
  set c := s83_mc a t with hc
  set σ := s83_ms a ν t with hσ
  set ρ := c / σ with hρ
  have hρ0 : 0 < ρ := div_pos hmc0 hms0
  have hmom : 0 ≤ mom d M σ₀ := s83_mom_nonneg _ _ (Real.sqrt_nonneg _)
  have hmom2 : 0 ≤ mom d (2 * M) σ₀ := s83_mom_nonneg _ _ (Real.sqrt_nonneg _)
  set K1 : ℝ := 2 ^ M * mom d M σ₀ with hK1
  have hK10 : 0 ≤ K1 := mul_nonneg (by positivity) hmom
  refine HRS.MS.Spec.s8p_isCompactOperator_of_c0 _ (Cχ * K1) ?_ ?_ ?_
  · intro h hh
    have := s83_cutFun_norm_le hχ hχc hM ha hν.le ht.le hCχ h
    calc ‖s83_cutOp (𝕜 := ℝ) hχ hχc hM ha hν.le ht.le hCχ h‖ ≤ Cχ * K1 * ‖h‖ := this
      _ ≤ Cχ * K1 * 1 := mul_le_mul_of_nonneg_left hh (mul_nonneg hCχ0 hK10)
      _ = Cχ * K1 := mul_one _
  · intro ε hε
    refine ⟨tsupport χ, hχc, fun h hh x hx => ?_⟩
    have : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [s83_cutOp_apply, this]
    simp [hε.le]
  · intro K hK ε hε
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (f := fun x : Euc d => ‖x‖) continuous_norm.continuousOn
    set J : ℝ := 1 + |R| with hJ
    have hJ1 : 1 ≤ J := by rw [hJ]; linarith [abs_nonneg R]
    have hJK : ∀ x ∈ K, jbracket x ≤ J := fun x hx => by
      refine (s83_jb_le_one_add x).trans ?_
      have := hR x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] at this
      rw [hJ]; linarith [le_abs_self R]
    have hJM : ∀ x ∈ K, jbracket x ^ M ≤ J ^ M := fun x hx =>
      Real.rpow_le_rpow (s83_jb_pos x).le (hJK x hx) hM
    set A : ℝ := K1 * J ^ M with hA
    have hA0 : 0 ≤ A := mul_nonneg hK10 (Real.rpow_nonneg (by linarith) _)
    set Lc : ℝ := 2 ^ M * J ^ M * Real.sqrt (mom d (2 * M) σ₀) with hLc
    have hLc0 : 0 ≤ Lc :=
      mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)) (Real.sqrt_nonneg _)
    set Bc : ℝ := Cχ * Lc * 2 * ρ with hBc
    have hBc0 : 0 ≤ Bc := by positivity
    -- uniform continuity of `V = χ ⟨x⟩^{-M}`
    set V : Euc d → ℝ := fun x => χ x * (jbracket x ^ M)⁻¹ with hV
    have hVc : Continuous V := hχ.mul ((s83_jb_rpow_cont M).inv₀ fun y =>
      (Real.rpow_pos_of_pos (s83_jb_pos y) _).ne')
    have hVcs : HasCompactSupport V := hχc.mul_right
    have hVuc := hVcs.uniformContinuous_of_continuous hVc
    have hε' : 0 < ε / (2 * (A + 1)) := by positivity
    obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.uniformContinuous_iff.1 hVuc _ hε'
    have hδ₂ : 0 < ε / (2 * (Bc + 1)) := by positivity
    refine ⟨min δ₁ (min (ε / (2 * (Bc + 1))) (1 / ρ)), by positivity, fun h hh x hx y hy hxy => ?_⟩
    have hd1 : dist x y < δ₁ := lt_of_lt_of_le hxy (min_le_left _ _)
    have hd2 : dist x y < ε / (2 * (Bc + 1)) :=
      lt_of_lt_of_le hxy ((min_le_right _ _).trans (min_le_left _ _))
    have hd3 : dist x y < 1 / ρ :=
      lt_of_lt_of_le hxy ((min_le_right _ _).trans (min_le_right _ _))
    -- the data
    set f := s83_wf M h with hf
    have hfc : Continuous f := s83_wf_cont M h
    have hfw : Wt M ‖h‖ f := s83_wf_wt M h
    have hh1 : ‖h‖ ≤ 1 := by simpa using hh
    have hPx : ∀ z ∈ K, |s83_P a ν t f z| ≤ A := fun z hz => by
      have := s83_P_wt hfc hM hfw ha hν.le ht.le z
      rw [Real.norm_eq_abs] at this
      refine this.trans ?_
      have hz0 := Real.rpow_nonneg (s83_jb_pos z).le M
      calc ‖h‖ * 2 ^ M * mom d M σ₀ * jbracket z ^ M ≤ 1 * 2 ^ M * mom d M σ₀ * J ^ M := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh1
              (by positivity)) hmom) (hJM z hz) hz0 (by positivity)
        _ = A := by rw [hA, hK1]; ring
    have hVy : |V y| ≤ Cχ := by
      rw [hV]
      simp only [abs_mul]
      have h1 : 1 ≤ jbracket y ^ M := Real.one_le_rpow (s83_one_le_jb y) hM
      have h2 : |(jbracket y ^ M)⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (inv_nonneg.2 (by linarith))]
        exact inv_le_one_of_one_le₀ h1
      calc |χ y| * |(jbracket y ^ M)⁻¹| ≤ Cχ * 1 :=
            mul_le_mul (hCχ y) h2 (abs_nonneg _) hCχ0
        _ = Cχ := mul_one _
    -- Lipschitz bound for the Mehler average
    have hκ : ρ * ‖x - y‖ < 1 := by
      have := hd3
      rw [dist_eq_norm, lt_div_iff₀ hρ0] at this
      linarith
    have hlip := s83_G_lip hfc hM hfw (c := c) (σ := σ) (σ₀ := σ₀)
      (by rw [abs_of_pos hmc0]; exact hmc1) hmsb hms0.ne' y x
    have hρ' : |c| / |σ| = ρ := by
      rw [abs_of_pos hmc0, abs_of_pos hms0]
    rw [hρ'] at hlip
    have hexp : Real.exp ((ρ * ‖x - y‖) ^ 2 / 2) ≤ 2 := by
      refine (Real.exp_le_exp.2 ?_).trans s83_exp_half_le
      have h0 : 0 ≤ ρ * ‖x - y‖ := by positivity
      nlinarith
    have hLipPf : |s83_P a ν t f x - s83_P a ν t f y| ≤ Lc * 2 * ρ * ‖x - y‖ := by
      have e : s83_P a ν t f = s83_G c σ f := rfl
      rw [e]
      refine hlip.trans ?_
      have hjy : jbracket y ^ M ≤ J ^ M := hJM y hy
      have hnn : 0 ≤ ρ * ‖x - y‖ := by positivity
      calc ‖h‖ * 2 ^ M * jbracket y ^ M * Real.sqrt (mom d (2 * M) σ₀) * (ρ * ‖x - y‖) *
            Real.exp ((ρ * ‖x - y‖) ^ 2 / 2)
          ≤ 1 * 2 ^ M * J ^ M * Real.sqrt (mom d (2 * M) σ₀) * (ρ * ‖x - y‖) * 2 := by
            refine mul_le_mul ?_ hexp (Real.exp_pos _).le (by positivity)
            refine mul_le_mul_of_nonneg_right ?_ hnn
            refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
            exact mul_le_mul (mul_le_mul_of_nonneg_right hh1 (by positivity)) hjy
              (Real.rpow_nonneg (s83_jb_pos y).le _) (by positivity)
        _ = Lc * 2 * ρ * ‖x - y‖ := by rw [hLc]; ring
    -- assemble
    have hTx : s83_cutOp (𝕜 := ℝ) hχ hχc hM ha hν.le ht.le hCχ h x = V x * s83_P a ν t f x := by
      rw [s83_cutOp_apply, smul_eq_mul]
    have hTy : s83_cutOp (𝕜 := ℝ) hχ hχc hM ha hν.le ht.le hCχ h y = V y * s83_P a ν t f y := by
      rw [s83_cutOp_apply, smul_eq_mul]
    rw [Real.dist_eq, hTx, hTy]
    have hdecomp : V x * s83_P a ν t f x - V y * s83_P a ν t f y =
        (V x - V y) * s83_P a ν t f x + V y * (s83_P a ν t f x - s83_P a ν t f y) := by ring
    rw [hdecomp]
    have hVxy : dist (V x) (V y) < ε / (2 * (A + 1)) := hδ₁' hd1
    rw [Real.dist_eq] at hVxy
    have t1 : |(V x - V y) * s83_P a ν t f x| < ε / 2 := by
      rw [abs_mul]
      calc |V x - V y| * |s83_P a ν t f x| ≤ ε / (2 * (A + 1)) * A :=
            mul_le_mul hVxy.le (hPx x hx) (abs_nonneg _) hε'.le
        _ < ε / 2 := by
            rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    have t2 : |V y * (s83_P a ν t f x - s83_P a ν t f y)| < ε / 2 := by
      rw [abs_mul]
      have hd : ‖x - y‖ < ε / (2 * (Bc + 1)) := by rwa [dist_eq_norm] at hd2
      calc |V y| * |s83_P a ν t f x - s83_P a ν t f y| ≤ Cχ * (Lc * 2 * ρ * ‖x - y‖) :=
            mul_le_mul hVy hLipPf (abs_nonneg _) hCχ0
        _ = Bc * ‖x - y‖ := by rw [hBc]; ring
        _ ≤ Bc * (ε / (2 * (Bc + 1))) := mul_le_mul_of_nonneg_left hd.le hBc0
        _ < ε / 2 := by
            rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    calc |(V x - V y) * s83_P a ν t f x + V y * (s83_P a ν t f x - s83_P a ν t f y)|
        ≤ |(V x - V y) * s83_P a ν t f x| + |V y * (s83_P a ν t f x - s83_P a ν t f y)| :=
          abs_add_le _ _
      _ < ε := by linarith

end Compact

end HRS.MS.Wad
