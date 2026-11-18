import HRS.MS.SA12C15

/-!
# S.A.12(c), packet E7.03 (part 5): the uniform `L²` bound of the remainder kernel

`ρ_v(z) = D^βγ_L(z) - χ̂(v-z) D^β g(z)` on `z ∈ [-L/2,L/2)^d`: for `L ≥ L₀`, `|v| ≤ 2`, `1 ≤ |β| ≤ m+1`,
`ρ_v² ∈ L¹(cube)` and `∫_{cube} ρ_v² ≤ C` with `C` independent of `L, γ, v, β` (needs `d < 2(s+1)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- The remainder kernel `D^βγ(z) - χ̂(v-z) D^β g(z)`. -/
def sa12cRho (s : ℝ) (χh : Euc d → ℝ) (γ : Euc d → ℝ) {n : ℕ} (β : Fin n → Fin d) (v z : Euc d) : ℝ :=
  partialDeriv β γ z - χh (v - z) * partialDeriv β (rieszKernel d s) z

theorem sa12c_remainder_kernel_l2 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hs1 : (d : ℝ) < 2 * (s + 1)) (m : ℕ) {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, L0 ≤ L → ∀ γ : Euc d → ℝ,
      IsPeriodicRieszKernel d s L γ → ∀ n : ℕ, 1 ≤ n → n ≤ m + 1 → ∀ β : Fin n → Fin d, ∀ v : Euc d,
        ‖v‖ ≤ 2 → IntegrableOn (fun z => (sa12cRho s χh γ β v z) ^ 2) (sa12cCube d L) ∧
          ∫ z in sa12cCube d L, (sa12cRho s χh γ β v z) ^ 2 ≤ C := by
  obtain ⟨δ, q, hδ0, hδ1, hq, hloc0⟩ := sa12c_kernel_local_deriv hd s hs0 hsd
  obtain ⟨Cq, hCq0, hCq⟩ := sa12c_q_bound hq (m + 1)
  obtain ⟨C1, hC10, hC1⟩ := sa12c_far_deriv_bound hd s hs0 hsd m
  have hTail := sa12c_tail_integrable (d := d) hs0 hs1
  set J : ℝ := ∫ z : Euc d, {z : Euc d | 4 ≤ ‖z‖}.indicator (fun z => (‖z‖ ^ (-(s + 1))) ^ 2) z with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun z => Set.indicator_nonneg (fun _ _ => sq_nonneg _) z
  set Vd : ℝ := (d : ℝ) ^ d * (volume (Metric.ball (0 : Euc d) 1)).toReal with hVd
  have hVd0 : 0 ≤ Vd := by positivity
  set V4 : ℝ := (volume (Metric.ball (0 : Euc d) 4)).toReal with hV4
  have hV40 : 0 ≤ V4 := ENNReal.toReal_nonneg
  refine ⟨max 21 (4 / δ), le_trans (by norm_num) (le_max_left _ _),
    Cq ^ 2 * V4 + 2 * C1 ^ 2 * (J + Vd), by positivity, ?_⟩
  intro L hL γ hγ n hn1 hnm β v hv
  have hL21 : 21 ≤ L := (le_max_left _ _).trans hL
  have hL4 : 4 ≤ δ * L := by
    have : 4 / δ ≤ L := (le_max_right _ _).trans hL
    rwa [div_le_iff₀ hδ0, mul_comm] at this
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hcm : MeasurableSet (sa12cCube d L) := sa12c_cube_meas L
  -- bounding function
  set G : Euc d → ℝ := fun z => (Metric.ball (0 : Euc d) 4).indicator (fun _ => Cq ^ 2) z + 2 * C1 ^ 2 *
      ({z : Euc d | 4 ≤ ‖z‖}.indicator (fun z => (‖z‖ ^ (-(s + 1))) ^ 2) z + (L ^ (-(s + 1))) ^ 2) with hG
  have hχ01 : ∀ x, |χh x| ≤ 1 := fun x => by
    have := hχ.2.2.2.2.1 x
    rw [abs_of_nonneg this.1]; exact this.2
  have hpt : ∀ z ∈ sa12cCube d L, z ≠ 0 → (sa12cRho s χh γ β v z) ^ 2 ≤ G z := by
    intro z hz hz0
    have hnn2 : 0 ≤ 2 * C1 ^ 2 *
        ({z : Euc d | 4 ≤ ‖z‖}.indicator (fun z => (‖z‖ ^ (-(s + 1))) ^ 2) z + (L ^ (-(s + 1))) ^ 2) := by
      have := Set.indicator_nonneg (s := {z : Euc d | 4 ≤ ‖z‖}) (f := fun z => (‖z‖ ^ (-(s + 1))) ^ 2)
        (fun _ _ => sq_nonneg _) z
      positivity
    by_cases h4 : ‖z‖ < 4
    · have hzb : z ∈ Metric.ball (0 : Euc d) 4 := by simpa using h4
      have hind : (Metric.ball (0 : Euc d) 4).indicator (fun _ => Cq ^ 2) z = Cq ^ 2 :=
        Set.indicator_of_mem hzb _
      have hχ1 : χh (v - z) = 1 := by
        refine hχ.2.2.2.2.2 (v - z) ?_
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (norm_sub_le _ _).trans (by linarith)
      have hdiff := (hloc0 L hL1 γ hγ).2 n hn1 z hz0 (lt_of_lt_of_le h4 hL4)
      have e1 : partialDeriv β γ z - partialDeriv β (rieszKernel d s) z =
          (L ^ (-s) * (L⁻¹) ^ n) * partialDeriv β q (L⁻¹ • z) := by
        have := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d) ℝ =>
          T (fun l => (EuclideanSpace.single (β l) (1 : ℝ) : Euc d))) hdiff
        simpa [partialDeriv] using this
      have hc0 : 0 ≤ L ^ (-s) * (L⁻¹) ^ n := by positivity
      have hc1 : L ^ (-s) * (L⁻¹) ^ n ≤ 1 := by
        have h1 : L ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
        have h2 : (L⁻¹) ^ n ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hL1)
        calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
          _ = 1 := one_mul 1
      have hw : ‖L⁻¹ • z‖ ≤ 1 / 2 := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL0, inv_mul_le_iff₀ hL0]
        have : ‖z‖ < δ * L := lt_of_lt_of_le h4 hL4
        nlinarith
      have hq1 : |partialDeriv β q (L⁻¹ • z)| ≤ Cq :=
        (HRS.MP.RdInit.mri_abs_partialDeriv_le β q _).trans (hCq n (by omega) _ hw)
      have hρ : |sa12cRho s χh γ β v z| ≤ Cq := by
        unfold sa12cRho
        rw [hχ1, one_mul, e1, abs_mul, abs_of_nonneg hc0]
        calc _ ≤ 1 * Cq := mul_le_mul hc1 hq1 (abs_nonneg _) zero_le_one
          _ = Cq := one_mul _
      have : (sa12cRho s χh γ β v z) ^ 2 ≤ Cq ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hρ 2
      show _ ≤ (Metric.ball (0 : Euc d) 4).indicator (fun _ => Cq ^ 2) z + _
      rw [hind]; linarith
    · push Not at h4
      have hz4 : z ∈ {z : Euc d | 4 ≤ ‖z‖} := h4
      have hind : {z : Euc d | 4 ≤ ‖z‖}.indicator (fun z => (‖z‖ ^ (-(s + 1))) ^ 2) z =
          (‖z‖ ^ (-(s + 1))) ^ 2 := Set.indicator_of_mem hz4 _
      have hcube : ∀ i, |z i| ≤ L / 2 := hz
      have hfar := hC1 L hL1 γ hγ n hn1 (by omega) z hz0 hcube
      have hz1 : 1 ≤ ‖z‖ := by linarith
      have ha : ‖z‖ ^ (-s - n) ≤ ‖z‖ ^ (-(s + 1)) := by
        refine Real.rpow_le_rpow_of_exponent_le hz1 ?_
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        linarith
      have hb : L ^ (-s - n) ≤ L ^ (-(s + 1)) := by
        refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        linarith
      have ha0 : 0 ≤ ‖z‖ ^ (-(s + 1)) := Real.rpow_nonneg (norm_nonneg _) _
      have hb0 : 0 ≤ L ^ (-(s + 1)) := Real.rpow_nonneg hL0.le _
      have hρ : |sa12cRho s χh γ β v z| ≤ C1 * (‖z‖ ^ (-(s + 1)) + L ^ (-(s + 1))) := by
        unfold sa12cRho
        refine (abs_sub _ _).trans ?_
        rw [abs_mul]
        have h1 : |partialDeriv β γ z| ≤ ‖iteratedFDeriv ℝ n γ z‖ :=
          HRS.MP.RdInit.mri_abs_partialDeriv_le β γ z
        have h2 : |partialDeriv β (rieszKernel d s) z| ≤ ‖iteratedFDeriv ℝ n (rieszKernel d s) z‖ :=
          HRS.MP.RdInit.mri_abs_partialDeriv_le β _ z
        have h3 : |χh (v - z)| * |partialDeriv β (rieszKernel d s) z| ≤
            |partialDeriv β (rieszKernel d s) z| := by
          calc _ ≤ 1 * |partialDeriv β (rieszKernel d s) z| :=
                mul_le_mul_of_nonneg_right (hχ01 _) (abs_nonneg _)
            _ = _ := one_mul _
        have h5 : C1 * (‖z‖ ^ (-s - n) + L ^ (-s - n)) ≤ C1 * (‖z‖ ^ (-(s + 1)) + L ^ (-(s + 1))) :=
          mul_le_mul_of_nonneg_left (by linarith) hC10
        linarith
      have : (sa12cRho s χh γ β v z) ^ 2 ≤
          2 * C1 ^ 2 * ((‖z‖ ^ (-(s + 1))) ^ 2 + (L ^ (-(s + 1))) ^ 2) := by
        rw [← sq_abs]
        calc |sa12cRho s χh γ β v z| ^ 2 ≤ (C1 * (‖z‖ ^ (-(s + 1)) + L ^ (-(s + 1)))) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) hρ 2
          _ ≤ _ := by nlinarith [sq_nonneg (‖z‖ ^ (-(s + 1)) - L ^ (-(s + 1))), sq_nonneg C1]
      have hind0 : 0 ≤ (Metric.ball (0 : Euc d) 4).indicator (fun _ => Cq ^ 2) z :=
        Set.indicator_nonneg (fun _ _ => sq_nonneg _) z
      show _ ≤ (Metric.ball (0 : Euc d) 4).indicator (fun _ => Cq ^ 2) z + 2 * C1 ^ 2 *
        ({z : Euc d | 4 ≤ ‖z‖}.indicator (fun z => (‖z‖ ^ (-(s + 1))) ^ 2) z + (L ^ (-(s + 1))) ^ 2)
      rw [hind]; linarith
  -- integrability of G on the cube
  have hcubefin : volume (sa12cCube d L) ≠ ⊤ :=
    ((measure_mono (sa12c_cube_subset (d := d) L hL0.le)).trans_lt measure_closedBall_lt_top).ne
  have hI1 : Integrable (fun z : Euc d => (Metric.ball (0 : Euc d) 4).indicator (fun _ => Cq ^ 2) z) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2 (integrableOn_const measure_ball_lt_top.ne)
  have hI3 : IntegrableOn (fun _ : Euc d => (L ^ (-(s + 1))) ^ 2) (sa12cCube d L) volume :=
    integrableOn_const hcubefin
  have hGi : IntegrableOn G (sa12cCube d L) volume := by
    have h := (hI1.integrableOn (s := sa12cCube d L)).add
      (((hTail.integrableOn (s := sa12cCube d L)).add hI3).const_mul (2 * C1 ^ 2))
    exact h
  -- measurability
  have hUo := HRS.MS.Ker1.ker1_isOpen_offLattice (d := d) hL0
  have hgU : ContDiffOn ℝ ∞ (rieszKernel d s) {x : Euc d | ∀ k : Fin d → ℤ, x ≠ L • latticePt k} :=
    (rieszKernel_contDiffOn (d := d) (s := s)).mono (fun x hx => by
      have := hx 0
      have hz : (L • latticePt (0 : Fin d → ℤ) : Euc d) = 0 := by
        ext i; simp [latticePt]
      simpa [hz] using this)
  have hcontρ : ContinuousOn (fun z => (sa12cRho s χh γ β v z) ^ 2)
      {x : Euc d | ∀ k : Fin d → ℤ, x ≠ L • latticePt k} := by
    refine ContinuousOn.pow ?_ 2
    unfold sa12cRho
    exact (sa12c_pd_contOn hUo hγ.smooth β).sub
      ((hχ.2.1.continuous.comp (continuous_const.sub continuous_id)).continuousOn.mul
        (sa12c_pd_contOn hUo hgU β))
  have hmeas := sa12c_aesm_cube hd hL0 hcontρ
  haveI : NeZero d := ⟨by omega⟩
  have hae0 : ∀ᵐ z ∂(volume : Measure (Euc d)), z ≠ 0 :=
    compl_mem_ae_iff.2 (measure_singleton (0 : Euc d))
  have hae : ∀ᵐ z ∂(volume.restrict (sa12cCube d L)), ‖(sa12cRho s χh γ β v z) ^ 2‖ ≤ G z := by
    refine (ae_restrict_iff' hcm).2 ?_
    filter_upwards [hae0] with z hz0 hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt z hz hz0
  have hint : IntegrableOn (fun z => (sa12cRho s χh γ β v z) ^ 2) (sa12cCube d L) volume :=
    Integrable.mono' hGi hmeas hae
  refine ⟨hint, ?_⟩
  -- the integral bound
  have hnn : 0 ≤ᵐ[volume.restrict (sa12cCube d L)] fun z => (sa12cRho s χh γ β v z) ^ 2 :=
    Eventually.of_forall fun z => sq_nonneg _
  have hle : ∀ᵐ z ∂(volume.restrict (sa12cCube d L)), (sa12cRho s χh γ β v z) ^ 2 ≤ G z := by
    refine (ae_restrict_iff' hcm).2 ?_
    filter_upwards [hae0] with z hz0 hz
    exact hpt z hz hz0
  have h1 : ∫ z in sa12cCube d L, (sa12cRho s χh γ β v z) ^ 2 ≤ ∫ z in sa12cCube d L, G z :=
    integral_mono_ae hint hGi hle
  refine h1.trans ?_
  have hI1' : IntegrableOn (fun z : Euc d => (Metric.ball (0 : Euc d) 4).indicator (fun _ => Cq ^ 2) z)
      (sa12cCube d L) volume := hI1.integrableOn
  have hI2' : IntegrableOn (fun z : Euc d => {z : Euc d | 4 ≤ ‖z‖}.indicator
      (fun z => (‖z‖ ^ (-(s + 1))) ^ 2) z) (sa12cCube d L) volume := hTail.integrableOn
  have hsplit : ∫ z in sa12cCube d L, G z =
      (∫ z in sa12cCube d L, (Metric.ball (0 : Euc d) 4).indicator (fun _ => Cq ^ 2) z) +
      2 * C1 ^ 2 * ((∫ z in sa12cCube d L, {z : Euc d | 4 ≤ ‖z‖}.indicator
        (fun z => (‖z‖ ^ (-(s + 1))) ^ 2) z) + ∫ z in sa12cCube d L, (L ^ (-(s + 1))) ^ 2) := by
    let f : Euc d → ℝ := fun z => (Metric.ball (0 : Euc d) 4).indicator (fun _ => Cq ^ 2) z
    let g : Euc d → ℝ := fun z => {z : Euc d | 4 ≤ ‖z‖}.indicator
      (fun z => (‖z‖ ^ (-(s + 1))) ^ 2) z
    let k : Euc d → ℝ := fun _ => (L ^ (-(s + 1))) ^ 2
    have hfg : G = f + (2 * C1 ^ 2) • (g + k) := by
      funext z; dsimp [G, f, g, k, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
    have hf : IntegrableOn f (sa12cCube d L) volume := hI1'
    have hg : IntegrableOn g (sa12cCube d L) volume := hI2'
    have hk : IntegrableOn k (sa12cCube d L) volume := hI3
    calc
      ∫ z in sa12cCube d L, G z = ∫ z in sa12cCube d L, (f + (2 * C1 ^ 2) • (g + k)) z := by rw [hfg]
      _ = (∫ z in sa12cCube d L, f z) + (2 * C1 ^ 2) * (∫ z in sa12cCube d L, (g + k) z) := by
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, integral_const_mul] using
          (integral_add hf ((hg.add hk).const_mul (2 * C1 ^ 2)))
      _ = _ := by
        have hadd : (∫ z in sa12cCube d L, (g + k) z) =
            (∫ z in sa12cCube d L, g z) + (∫ z in sa12cCube d L, k z) :=
          integral_add hg hk
        simpa only [hadd, f, g, k]
  rw [hsplit]
  have b1 : ∫ z in sa12cCube d L, (Metric.ball (0 : Euc d) 4).indicator (fun _ => Cq ^ 2) z ≤ Cq ^ 2 * V4 := by
    refine (setIntegral_le_integral hI1 (Eventually.of_forall fun z =>
      Set.indicator_nonneg (fun _ _ => sq_nonneg _) z)).trans (le_of_eq ?_)
    rw [integral_indicator_const _ Metric.isOpen_ball.measurableSet]
    simp [hV4, Measure.real, mul_comm]
  have b2 : ∫ z in sa12cCube d L, {z : Euc d | 4 ≤ ‖z‖}.indicator
      (fun z => (‖z‖ ^ (-(s + 1))) ^ 2) z ≤ J :=
    setIntegral_le_integral hTail (Eventually.of_forall fun z =>
      Set.indicator_nonneg (fun _ _ => sq_nonneg _) z)
  have b3 : ∫ z in sa12cCube d L, (L ^ (-(s + 1))) ^ 2 ≤ Vd := by
    rw [setIntegral_const, smul_eq_mul]
    have hvol := sa12c_cube_volume (d := d) L hL0.le
    have hexp : (L : ℝ) ^ d * (L ^ (-(s + 1))) ^ 2 ≤ 1 := by
      have h1 : (L : ℝ) ^ d = L ^ (d : ℝ) := (Real.rpow_natCast L d).symm
      have h2 : (L ^ (-(s + 1))) ^ 2 = L ^ (-(2 * (s + 1))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
        congr 1; push_cast; ring
      rw [h1, h2, ← Real.rpow_add hL0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
    have hq0 : 0 ≤ (L ^ (-(s + 1))) ^ 2 := sq_nonneg _
    calc (volume.real (sa12cCube d L)) * (L ^ (-(s + 1))) ^ 2
        ≤ (Vd * L ^ d) * (L ^ (-(s + 1))) ^ 2 := mul_le_mul_of_nonneg_right hvol hq0
      _ = Vd * (L ^ d * (L ^ (-(s + 1))) ^ 2) := by ring
      _ ≤ Vd * 1 := mul_le_mul_of_nonneg_left hexp hVd0
      _ = Vd := mul_one _
  have hC12 : 0 ≤ 2 * C1 ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add b2 b3) hC12]

end HRS.MH.AdjointRd.Phase2SA12C
