import HRS.Main.EqBiasAux3
import HRS.Equilibrium.CavityMain

/-!
# EQ-BIAS, S4: from the cavity equation to the bias expansion

`eqbias_abstract_step`: if `F = z + βKz - P D` has small `L²` norm and `D ≈ δ c ρ` uniformly then
`‖z/δ - c h‖₂ ≤ η + ε₂`, `h = responseInverse` (coercivity of `I + βK` on `L²_0(μ)`).

`eqbias_expansion_of_D`: the full statement of `equilibrium_bias_expansion`, assuming the asymptotics
`D_N = δ_N c₀β^p ρ (1 + o(1))` of the insertion defect (hypothesis `hD`; proved in S5-S9).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ} {s : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.PDE

/-- `‖f - μ(f)‖₂ ≤ ε` for `|f| ≤ ε`. -/
theorem eqbias_sqrt_proj_le {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f : Torus d → ℝ}
    (hm : Measurable f) {ε : ℝ} (hε : 0 ≤ ε) (hb : ∀ x, |f x| ≤ ε) :
    Real.sqrt (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) ≤ ε := by
  have hfi : Integrable f μ :=
    Integrable.of_bound hm.aestronglyMeasurable ε
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have hf2 : Integrable (fun x => f x ^ 2) μ :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (ε ^ 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg (f x), sq_abs (f x), hb x])
  set m : ℝ := ∫ y, f y ∂μ with hmdef
  have e : ∫ x, (f x - m) ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ - m ^ 2 := by
    have : ∀ x, (f x - m) ^ 2 = f x ^ 2 + (-(2 * m) * f x + m ^ 2) := fun x => by ring
    simp_rw [this]
    have h1 : Integrable (fun x => -(2 * m) * f x + m ^ 2) μ :=
      (hfi.const_mul _).add (integrable_const _)
    rw [integral_add hf2 h1, integral_add (hfi.const_mul _) (integrable_const _),
      integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    rw [← hmdef]; ring
  have hle : ∫ x, f x ^ 2 ∂μ ≤ ε ^ 2 := by
    calc ∫ x, f x ^ 2 ∂μ ≤ ∫ _x, ε ^ 2 ∂μ :=
          integral_mono hf2 (integrable_const _) fun x => by
            nlinarith [abs_nonneg (f x), sq_abs (f x), hb x]
      _ = ε ^ 2 := by simp
  rw [e]
  exact Real.sqrt_le_iff.2 ⟨hε, by nlinarith [sq_nonneg m]⟩

theorem eqbias_memLp_of_bound {μ : Measure (Torus d)} [IsFiniteMeasure μ] {f : Torus d → ℝ}
    (hm : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M) : MemLp f 2 μ :=
  MemLp.of_bound hm.aestronglyMeasurable M
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

set_option maxHeartbeats 1600000 in
theorem eqbias_abstract_step (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {β : ℝ} (hβ : 0 < β)
    {z D : Torus d → ℝ} (hzm : Measurable z) {Mz : ℝ} (hzb : ∀ x, |z x| ≤ Mz)
    (hz0 : ∫ x, z x ∂(withDensityReal ρ) = 0)
    (hDm : Measurable D) {MD : ℝ} (hDb : ∀ x, |D x| ≤ MD)
    {δ : ℝ} (hδ : 0 < δ) (c : ℝ) {η ε₂ : ℝ} (hη : 0 ≤ η) (hε₂ : 0 ≤ ε₂)
    (hFm : MemLp (fun x => z x + β * Kop (periodicRiesz d s) (withDensityReal ρ) z x -
        projMean (withDensityReal ρ) D x) 2 (withDensityReal ρ))
    (hFb : Real.sqrt (∫ x, (z x + β * Kop (periodicRiesz d s) (withDensityReal ρ) z x -
        projMean (withDensityReal ρ) D x) ^ 2 ∂(withDensityReal ρ)) ≤ η * δ)
    (hDc : ∀ x, |D x - δ * c * ρ x| ≤ ε₂ * δ) :
    Real.sqrt (∫ x, (δ⁻¹ * z x - c * responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ x) ^ 2
      ∂(withDensityReal ρ)) ≤ η + ε₂ := by
  have hP := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨Λ, H⟩ := eqbias_KS hd hs0 hsd hρ
  set μ := withDensityReal ρ with hμ
  set h := responseInverse (periodicRiesz d s) μ β ρ with hh
  obtain ⟨hm, hp, he⟩ : MemLp h 2 μ ∧ pair μ h = 0 ∧
      ∀ᵐ x ∂μ, h x + β * Kop (periodicRiesz d s) μ h x = projMean μ ρ x :=
    eqbias_response hd hs0 hsd hρ hβ.le
  have hρm := eqbias_memLp_rho hρ
  have hρmeas : Measurable ρ := hρ.density.measurable
  have hzmem : MemLp z 2 μ := eqbias_memLp_of_bound hzm hzb
  have hzi : Integrable z μ := hzmem.integrable one_le_two
  have hhi : Integrable h μ := hm.integrable one_le_two
  have hDmem : MemLp D 2 μ := eqbias_memLp_of_bound hDm hDb
  have hDi : Integrable D μ := hDmem.integrable one_le_two
  have hρi : Integrable ρ μ := hρm.integrable one_le_two
  -- the test function and its `L²` properties
  set w : Torus d → ℝ := fun x => δ⁻¹ * z x - c * h x with hw
  have hwmem : MemLp w 2 μ := (hzmem.const_mul δ⁻¹).sub (hm.const_mul c)
  have hwp : pair μ w = 0 := by
    unfold pair
    rw [hw]
    simp only
    rw [integral_sub (hzi.const_mul _) (hhi.const_mul _), integral_const_mul, integral_const_mul, hz0]
    have : ∫ x, h x ∂μ = 0 := hp
    rw [this]; ring
  -- linearity of `K`
  have hKw : Kop (periodicRiesz d s) μ w =ᵐ[μ]
      fun x => δ⁻¹ * Kop (periodicRiesz d s) μ z x - c * Kop (periodicRiesz d s) μ h x := by
    have hwe : w = fun y => (fun y => δ⁻¹ * z y) y + (fun y => (-c) * h y) y := by
      funext y; simp only [hw]; ring
    have h1 := MFLinear.Kop_add_ae H (a := fun y => δ⁻¹ * z y) (b := fun y => (-c) * h y)
      (hzi.const_mul _) (hhi.const_mul _)
    rw [MFLinear.Kop_smul, MFLinear.Kop_smul] at h1
    rw [hwe]
    filter_upwards [h1] with x hx
    rw [hx]; ring
  -- the right-hand side
  set F : Torus d → ℝ := fun x => z x + β * Kop (periodicRiesz d s) μ z x - projMean μ D x with hF
  set f : Torus d → ℝ := fun x => δ⁻¹ * D x - c * ρ x with hf
  have hfm : Measurable f := (hDm.const_mul _).sub (hρmeas.const_mul _)
  have hfb : ∀ x, |f x| ≤ ε₂ := by
    intro x
    have : f x = δ⁻¹ * (D x - δ * c * ρ x) := by
      simp only [hf]; field_simp
    rw [this, abs_mul, abs_of_pos (inv_pos.2 hδ), inv_mul_le_iff₀ hδ]
    linarith [hDc x]
  set E : Torus d → ℝ := fun x => δ⁻¹ * F x + (f x - ∫ y, f y ∂μ) with hE
  have hfmem : MemLp (fun x => f x - ∫ y, f y ∂μ) 2 μ :=
    (eqbias_memLp_of_bound hfm hfb).sub (memLp_const _)
  have hEmem : MemLp E 2 μ := (hFm.const_mul δ⁻¹).add hfmem
  have heE : ∀ᵐ x ∂μ, w x + β * Kop (periodicRiesz d s) μ w x = E x := by
    filter_upwards [hKw, he] with x hx1 hx2
    rw [hx1]
    have hfint : ∫ y, f y ∂μ = δ⁻¹ * pair μ D - c * pair μ ρ := by
      simp only [hf]
      rw [integral_sub (hDi.const_mul _) (hρi.const_mul _), integral_const_mul, integral_const_mul]
      rfl
    have hproj : projMean μ ρ x = ρ x - pair μ ρ := rfl
    have hproj2 : projMean μ D x = D x - pair μ D := rfl
    simp only [hE, hF, hw, hf]
    rw [hfint]
    have hx2' : h x + β * Kop (periodicRiesz d s) μ h x = ρ x - pair μ ρ := by rw [hx2, hproj]
    rw [hproj2]
    have hFx : z x + β * Kop (periodicRiesz d s) μ z x = (z x + β * Kop (periodicRiesz d s) μ z x -
        (D x - pair μ D)) + (D x - pair μ D) := by ring
    -- algebra
    have key : δ⁻¹ * z x - c * h x + β * (δ⁻¹ * Kop (periodicRiesz d s) μ z x -
        c * Kop (periodicRiesz d s) μ h x) =
        δ⁻¹ * (z x + β * Kop (periodicRiesz d s) μ z x) -
          c * (h x + β * Kop (periodicRiesz d s) μ h x) := by ring
    rw [key, hx2']
    have : δ⁻¹ * (z x + β * Kop (periodicRiesz d s) μ z x) =
        δ⁻¹ * (z x + β * Kop (periodicRiesz d s) μ z x - (D x - pair μ D)) +
          δ⁻¹ * (D x - pair μ D) := by ring
    rw [this]
    ring
  -- coercivity
  have hcoer := eqbias_coercive hd hs0 hsd hρ hβ.le hwmem hwp
  have hl2 : l2Inner μ w (fun x => w x + β * Kop (periodicRiesz d s) μ w x) = ∫ x, w x * E x ∂μ := by
    unfold l2Inner
    refine integral_congr_ae ?_
    filter_upwards [heE] with x hx
    rw [hx]
  rw [hl2] at hcoer
  have hcs := EF.cs_integral hwmem hEmem
  set W := Real.sqrt (∫ x, w x ^ 2 ∂μ) with hW
  set Q := Real.sqrt (∫ x, E x ^ 2 ∂μ) with hQ
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have hw2 : 0 ≤ ∫ x, w x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hE2 : 0 ≤ ∫ x, E x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hWW : W ^ 2 = ∫ x, w x ^ 2 ∂μ := Real.sq_sqrt hw2
  have hQQ : Q ^ 2 = ∫ x, E x ^ 2 ∂μ := Real.sq_sqrt hE2
  have hWQ : W ≤ Q := by
    by_contra hlt
    push_neg at hlt
    have h1 : W ^ 2 ≤ ∫ x, w x * E x ∂μ := by rw [hWW]; exact hcoer
    have h2 : (∫ x, w x * E x ∂μ) ^ 2 ≤ (W * Q) ^ 2 := by
      rw [mul_pow, hWW, hQQ]; exact hcs
    have h3 : ∫ x, w x * E x ∂μ ≤ W * Q := by
      have := abs_le_of_sq_le_sq' h2 (by positivity)
      exact this.2
    nlinarith [mul_nonneg hW0 hQ0, sq_nonneg (W - Q)]
  refine hWQ.trans ?_
  -- bound `Q`
  have hFmem' : MemLp (fun x => δ⁻¹ * F x) 2 μ := hFm.const_mul δ⁻¹
  have hQ1 : Q ≤ Real.sqrt (∫ x, (δ⁻¹ * F x) ^ 2 ∂μ) +
      Real.sqrt (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) :=
    sqrt_int_add_le hFmem' hfmem
  have hQ2 : Real.sqrt (∫ x, (δ⁻¹ * F x) ^ 2 ∂μ) ≤ η := by
    have e : ∫ x, (δ⁻¹ * F x) ^ 2 ∂μ = (δ⁻¹) ^ 2 * ∫ x, F x ^ 2 ∂μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hδ.le)]
    calc δ⁻¹ * Real.sqrt (∫ x, F x ^ 2 ∂μ) ≤ δ⁻¹ * (η * δ) :=
          mul_le_mul_of_nonneg_left hFb (inv_nonneg.2 hδ.le)
      _ = η := by field_simp
  have hQ3 := eqbias_sqrt_proj_le (μ := μ) hfm hε₂ hfb
  linarith

/-- The constant `c₀ = |𝕊^{d-1}|Γ(2-p)/(s p (p-1))` of `supercriticalBiasDensity`. -/
def eqbias_c0 (d : ℕ) (s : ℝ) : ℝ :=
  sphereArea d * Real.Gamma (2 - d / s) / (s * (d / s) * (d / s - 1))

/-- The `L²` bias expansion, assuming the asymptotics of the insertion defect (`hD`). -/
theorem eqbias_L2_of_D (hd : 2 ≤ d) (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    (hD : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → ∀ x : Torus d,
      |insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x -
          deltaN d s N * (eqbias_c0 d s * β ^ ((d : ℝ) / s)) * ρ x| ≤ ε * deltaN d s N) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
      Real.sqrt (∫ x, ((deltaN d s (n + 1))⁻¹ *
          (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) -
          (eqbias_c0 d s * β ^ ((d : ℝ) / s)) *
            responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ x) ^ 2
        ∂(withDensityReal ρ)) ≤ ε := by
  have hs0 : 0 ≤ s := (eqbias_p_range hs1 hsd hd).1.le
  have hP := PoleCavityAux.isProbabilityMeasure_mu hρ
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := eqbias_response_bound hd hs0 hsd hβ hρ
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  obtain ⟨Cd, hCd⟩ := insDefect_le hd hs0 hsd hβ hρ
  set ε₁ : ℝ := ε / (8 * (C + 1)) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨n₁, hn₁⟩ := sup_dev_small hd hs0 hsd hβ hρ ε₁ hε₁0
  obtain ⟨N₂, hN₂⟩ := eqbias_rates hd hs1 hsd hε₁0
  obtain ⟨N₃, hN₃⟩ := hD (ε / 2) (by positivity)
  refine ⟨max (max n₁ N₂) N₃ + 1, fun n hn hn0 lam hlam => ?_⟩
  have hn1 : n₁ ≤ n := by omega
  have hn2 : N₂ ≤ n + 1 := by omega
  have hn3 : N₃ ≤ n + 1 := by omega
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set δ := deltaN d s (n + 1) with hδ
  have hδ0 : 0 < δ := by
    rw [hδ, eqbias_deltaN hs1]; exact Real.rpow_pos_of_pos hN0 _
  obtain ⟨hFm, hFb0⟩ := hC n hn0 lam hlam ε₁ hε₁0.le (fun y => hn₁ n hn1 hn0 lam hlam y)
  obtain ⟨hr1, hr2⟩ := hN₂ (n + 1) hn2 hN
  have hFb : Real.sqrt (∫ x, ((pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) +
          β * Kop (periodicRiesz d s) (withDensityReal ρ)
            (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1) x -
          projMean (withDensityReal ρ)
            (insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β) x) ^ 2
          ∂(withDensityReal ρ)) ≤ (C * (ε₁ + ε₁ + ε₁)) * δ := by
    refine hFb0.trans ?_
    have : C * (ε₁ * δ + Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + 1 / ((n + 1 : ℕ) : ℝ)) ≤
        C * (ε₁ * δ + ε₁ * δ + ε₁ * δ) := by
      refine mul_le_mul_of_nonneg_left ?_ hC0
      linarith
    refine this.trans (le_of_eq ?_)
    ring
  have hzm : Measurable (fun x => pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) := by
    obtain ⟨hlam0, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn0 hlam
    exact (measurable_pDens hd hs0 hsd hρ hlam0 hln).sub measurable_const
  have hpb : ∀ x, Real.exp (-Mp) ≤ pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x ∧
      pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x ≤ Mp := by
    intro x
    have h1 := (hMp (n + 1) hN x)
    simp only [Nat.add_sub_cancel] at h1
    rw [hlam]
    exact h1
  have hzb : ∀ x, |pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1| ≤ Mp := by
    intro x
    have h1 := hpb x
    have hpos := Real.exp_pos (-Mp)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, hMp1]
  have hz0 : ∫ x, (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1)
      ∂(withDensityReal ρ) = 0 := by
    obtain ⟨hlam0, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn0 hlam
    have h1 := integral_pDens hd hs0 hsd hρ hlam0 hln
    have hpi : Integrable (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β)
        (withDensityReal ρ) :=
      (eqbias_memLp_of_bound (measurable_pDens hd hs0 hsd hρ hlam0 hln) (M := Mp) (fun x => by
        have hp0 := pDens_pos hd hs0 hsd hρ hlam0 hln x
        rw [abs_of_pos hp0]; exact (hpb x).2)).integrable one_le_two
    rw [integral_sub hpi (integrable_const _), h1]; simp
  have hDm : Measurable (insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β) := by
    obtain ⟨hlam0, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn0 hlam
    unfold insDefect
    haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam0
    have hgm := measurable_periodicRiesz hd hs0 hsd
    have hint : Measurable fun x : Torus d => ∫ Y : Config d n, ∑ j, periodicRiesz d s (x - Y j)
        ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) := by
      have : StronglyMeasurable (Function.uncurry fun (x : Torus d) (Y : Config d n) =>
          ∑ j, periodicRiesz d s (x - Y j)) :=
        (Finset.measurable_sum _ fun j _ => hgm.comp (measurable_fst.sub
          ((measurable_pi_apply j).comp measurable_snd))).stronglyMeasurable
      exact (this.integral_prod_right' (ν := cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)).measurable
    exact (Real.measurable_log.comp (measurable_phiIns hd hs0 hsd hρ hlam0 hln)).add
      (hint.const_mul _)
  have hDb : ∀ x, |insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x| ≤ |Cd| * δ := by
    intro x
    obtain ⟨h0, h1, -⟩ := hCd (n + 1) hN x
    simp only [Nat.add_sub_cancel] at h0 h1
    rw [hlam]
    rw [abs_of_nonneg h0]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0.le)
  have hDc : ∀ x, |insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x -
      δ * (eqbias_c0 d s * β ^ ((d : ℝ) / s)) * ρ x| ≤ (ε / 2) * δ := by
    intro x
    have := hN₃ (n + 1) hn3 hN x
    simp only [Nat.add_sub_cancel] at this
    rw [hlam]
    exact this
  have key := eqbias_abstract_step hd hs0 hsd hρ hβ hzm hzb hz0 hDm hDb hδ0
    (eqbias_c0 d s * β ^ ((d : ℝ) / s)) (η := C * (ε₁ + ε₁ + ε₁)) (ε₂ := ε / 2) (by positivity)
    (by positivity) hFm hFb hDc
  refine key.trans ?_
  have : C * (ε₁ + ε₁ + ε₁) ≤ ε / 2 := by
    rw [hε₁]
    have h8 : C * (ε / (8 * (C + 1))) ≤ ε / 8 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_nonneg hC0 hε.le]
    nlinarith
  linarith

/-- `equilibrium_bias_expansion` for the modulated Gibbs law, assuming `hD`. -/
theorem eqbias_tendsto_of_D (hd : 2 ≤ d) (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    (hD : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → ∀ x : Torus d,
      |insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x -
          deltaN d s N * (eqbias_c0 d s * β ^ ((d : ℝ) / s)) * ρ x| ≤ ε * deltaN d s N) :
    (∀ N : ℕ, 2 ≤ N →
      firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
        withDensityReal ρ) ∧
    Tendsto (fun N : ℕ =>
      eLpNorm (fun y =>
        (((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
            (withDensityReal ρ) y).toReal - 1) / (N : ℝ) ^ (1 - (d : ℝ) / s) -
          (eqbias_c0 d s * β ^ ((d : ℝ) / s)) *
            responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ y) 2 (withDensityReal ρ))
      atTop (𝓝 0) := by
  have hs0 : 0 ≤ s := (eqbias_p_range hs1 hsd hd).1.le
  have hP := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨C, hC⟩ := firstMarginal_density_L2 hd hs0 hsd β hβ ρ hρ
  refine ⟨fun N hN => (hC N hN).1, ?_⟩
  have hL2 := eqbias_L2_of_D hd hs1 hsd hβ hρ hD
  obtain ⟨hm, hp, he⟩ : MemLp (responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ) 2
        (withDensityReal ρ) ∧ _ ∧ _ := eqbias_response hd hs0 hsd hρ hβ.le
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun _ => by rw [hεt]; exact le_top
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  obtain ⟨n₀, hn₀⟩ := hL2 ε.toReal hεr
  rw [Filter.eventually_atTop]
  refine ⟨n₀ + 2, fun N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn0 : 0 < n := by omega
  have hN2 : 2 ≤ n + 1 := by omega
  obtain ⟨hlam0, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn0
    (lam := β / ((n + 1 : ℕ) : ℝ)) rfl
  have hae := rnDeriv_pi_eq hd hs0 hsd hρ hlam0 hln
  rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ (n + 1) (Nat.succ_pos n)]
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hzm : Measurable (fun x => pDens (periodicRiesz d s) (withDensityReal ρ) n
      (β / ((n + 1 : ℕ) : ℝ)) β x - 1) :=
    (measurable_pDens hd hs0 hsd hρ hlam0 hln).sub measurable_const
  have hzb : ∀ x, |pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x - 1|
      ≤ Mp := by
    intro x
    have h1 := hMp (n + 1) hN2 x
    simp only [Nat.add_sub_cancel] at h1
    have hpos := Real.exp_pos (-Mp)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, hMp1]
  set δ := deltaN d s (n + 1) with hδ
  have hδ' : ((n + 1 : ℕ) : ℝ) ^ (1 - (d : ℝ) / s) = δ := (eqbias_deltaN hs1 (n + 1)).symm
  set g : Torus d → ℝ := fun x => δ⁻¹ * (pDens (periodicRiesz d s) (withDensityReal ρ) n
      (β / ((n + 1 : ℕ) : ℝ)) β x - 1) -
      (eqbias_c0 d s * β ^ ((d : ℝ) / s)) *
        responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ x with hg
  have hgmem : MemLp g 2 (withDensityReal ρ) :=
    ((eqbias_memLp_of_bound hzm hzb).const_mul δ⁻¹).sub (hm.const_mul _)
  have hcongr : eLpNorm (fun y =>
      (((firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1)
        (β / ((n + 1 : ℕ) : ℝ)) β)).rnDeriv (withDensityReal ρ) y).toReal - 1) /
        ((n + 1 : ℕ) : ℝ) ^ (1 - (d : ℝ) / s) -
        (eqbias_c0 d s * β ^ ((d : ℝ) / s)) *
          responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ y) 2 (withDensityReal ρ) =
      eLpNorm g 2 (withDensityReal ρ) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae] with y hy
    simp only [hg]
    rw [hy, hδ', div_eq_inv_mul]
  rw [hcongr]
  have hb := hn₀ n (by omega) hn0 _ rfl
  have := eLpNorm_two_le hgmem hb
  rwa [ENNReal.ofReal_toReal hεt] at this

end Main

end HRS

end
