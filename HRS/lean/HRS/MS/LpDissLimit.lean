import HRS.MS.LpDissCut
import HRS.MS.CzPvAux2

/-!
# S.A.16.C5: exact weighted leading fractional energy estimate

`sa16bd_weighted_leading`: the cutoff estimate of C4 passes to the frozen `fracLap` and
`dissipationDensity`.  The signed energy integral converges by dominated convergence (cutoff-uniform
bound from C2), and the cutoff dissipations increase to the frozen dissipation density by monotone
convergence; finiteness of the full weighted dissipation comes out of the uniform C4 bound.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemB

universe u

namespace HRS.Whole.AppendixA.BreakdownSA16

/-- the standard cutoff sequence `1/(n+1)` -/
def sa16bd_eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma sa16bd_eps_pos (n : ℕ) : 0 < sa16bd_eps n := by unfold sa16bd_eps; positivity

lemma sa16bd_eps_anti {m n : ℕ} (h : m ≤ n) : sa16bd_eps n ≤ sa16bd_eps m := by
  unfold sa16bd_eps
  gcongr

lemma sa16bd_eps_tendsto : Tendsto sa16bd_eps atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => sa16bd_eps_pos n⟩
  exact tendsto_one_div_add_atTop_nhds_zero_nat

lemma sa16bd_memCb2_schwartz {d : ℕ} (ψ : SchwartzMap (Euc d) ℝ) : MemCb 2 (⇑ψ) :=
  ⟨ψ.smooth 2, fun j _ => ⟨SchwartzMap.seminorm ℝ 0 j ψ, by
    rintro _ ⟨x, rfl⟩
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ ψ j x⟩⟩

lemma sa16bd_cbNorm_nonneg {d : ℕ} (f : Euc d → ℝ) : 0 ≤ cbNorm 2 f :=
  Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun z => norm_nonneg _

/-- the cutoff differences converge to the frozen `fracLap` -/
lemma sa16bd_lapCut_tendsto {d : ℕ} (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (ψ : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    Tendsto (fun n : ℕ => sa16bd_lapCut d θ (sa16bd_eps n) (fun y => ψ y) x) atTop
      (𝓝 (fracLap d θ (fun y => ψ y) x)) := by
  obtain ⟨B, L, M, hpv⟩ := PvC2.of_schwartz ψ
  have h1 := (fracLap_tendsto hd hθ0 hθ2 hpv x).comp sa16bd_eps_tendsto
  rw [← fracLap_eq_symm hd hθ0 hθ2 hpv x] at h1
  exact h1

/-- measurability of the frozen `fracLap` of a Schwartz function -/
lemma sa16bd_fracLap_aesm {d : ℕ} (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (ψ : SchwartzMap (Euc d) ℝ) :
    AEStronglyMeasurable (fun x : Euc d => fracLap d θ (fun y => ψ y) x) volume :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => sa16bd_lapCut_aesm d θ (sa16bd_eps n) ψ.continuous)
    (Eventually.of_forall fun x => sa16bd_lapCut_tendsto hd hθ0 hθ2 ψ x)

/-- integrability of the energy integrand for an abstract bounded family `ℓ` -/
lemma sa16bd_T_bound {d : ℕ} {ι : Type u} [Fintype ι] {p : ℝ} (hp : 2 ≤ p)
    (W : ι → 𝓢(Euc d, ℝ)) {Bμ Mℓ : ℝ} (μ : Euc d → ℝ) (hBμ : ∀ x, |μ x| ≤ Bμ)
    (ℓ : ι → Euc d → ℝ) (hℓb : ∀ i x, |ℓ i x| ≤ Mℓ) (hMℓ : 0 ≤ Mℓ) (x : Euc d) :
    |μ x * vnorm (fun i => W i x) ^ (p - 2) * (∑ i, W i x * ℓ i x)| ≤
      (Bμ * ((Fintype.card ι : ℝ) * Mℓ)) * vnorm (fun i => W i x) ^ (p - 1) := by
  have h0 : 0 ≤ vnorm (fun i => W i x) := Real.sqrt_nonneg _
  have hsum : |∑ i, W i x * ℓ i x| ≤ (Fintype.card ι : ℝ) * (vnorm (fun i => W i x) * Mℓ) := by
    calc |∑ i, W i x * ℓ i x| ≤ ∑ i, |W i x * ℓ i x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, vnorm (fun i => W i x) * Mℓ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (elemb_abs_le_vnorm (fun i => W i x) i) (hℓb i x) (abs_nonneg _) h0
      _ = _ := by simp
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg h0 _)]
  have e : vnorm (fun i => W i x) ^ (p - 2) * vnorm (fun i => W i x) =
      vnorm (fun i => W i x) ^ (p - 1) := by
    rw [← Real.rpow_add_one' h0 (by linarith)]
    congr 1
    ring
  calc |μ x| * vnorm (fun i => W i x) ^ (p - 2) * |∑ i, W i x * ℓ i x|
      ≤ Bμ * vnorm (fun i => W i x) ^ (p - 2) *
          ((Fintype.card ι : ℝ) * (vnorm (fun i => W i x) * Mℓ)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (hBμ x) (Real.rpow_nonneg h0 _)) hsum
          (abs_nonneg _) ?_
        exact mul_nonneg (le_trans (abs_nonneg _) (hBμ x)) (Real.rpow_nonneg h0 _)
    _ = (Bμ * ((Fintype.card ι : ℝ) * Mℓ)) * vnorm (fun i => W i x) ^ (p - 1) := by
        rw [← e]; ring

lemma sa16bd_T_integrable {d : ℕ} {ι : Type u} [Fintype ι] {p : ℝ} (hp : 2 ≤ p)
    (W : ι → 𝓢(Euc d, ℝ)) {Bμ Mℓ : ℝ} (μ : Euc d → ℝ) (hμc : Continuous μ)
    (hBμ : ∀ x, |μ x| ≤ Bμ)
    (ℓ : ι → Euc d → ℝ) (hℓ : ∀ i, AEStronglyMeasurable (ℓ i) volume)
    (hℓb : ∀ i x, |ℓ i x| ≤ Mℓ) (hMℓ : 0 ≤ Mℓ) :
    Integrable (fun x : Euc d => μ x * vnorm (fun i => W i x) ^ (p - 2) *
      (∑ i, W i x * ℓ i x)) := by
  have hVc : Continuous (fun y : Euc d => vnorm (fun i => W i y)) :=
    elemb_vnorm_continuous (f := fun i y => W i y) fun i => (W i).continuous
  have hg : Integrable (fun x : Euc d =>
      (Bμ * ((Fintype.card ι : ℝ) * Mℓ)) * vnorm (fun i => W i x) ^ (p - 1)) :=
    (sa16bd_Vq_integrable W (by linarith)).const_mul _
  have hmeas : AEStronglyMeasurable (fun x : Euc d => μ x * vnorm (fun i => W i x) ^ (p - 2) *
      (∑ i, W i x * ℓ i x)) volume := by
    refine (hμc.aestronglyMeasurable.mul
      ((hVc.rpow_const (fun _ => Or.inr (by linarith))).aestronglyMeasurable)).mul ?_
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (W i).continuous.aestronglyMeasurable.mul (hℓ i)
  refine hg.mono' hmeas (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact sa16bd_T_bound hp W μ hBμ ℓ hℓb hMℓ x

/-! ### monotone convergence of the cutoff dissipations -/

lemma sa16bd_diss_tendsto {d : ℕ} {ι : Type u} [Fintype ι] (θ p : ℝ) (hp : 2 ≤ p)
    (w : ι → Euc d → ℝ) (hwc : ∀ i, Continuous (w i)) (μ : Euc d → ℝ) (hμc : Continuous μ) :
    Tendsto (fun n : ℕ => ∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
        sa16bd_dissCut d θ p (sa16bd_eps n) (fun y i => w i y) x) atTop
      (𝓝 (∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
        dissipationDensity d θ p (fun y i => w i y) x)) := by
  set F : Euc d × Euc d → ℝ≥0∞ := fun q => ENNReal.ofReal
    ((vnorm (fun i => w i q.1) + vnorm (fun i => w i (q.1 - q.2))) ^ (p - 2) *
      vnorm (fun i => w i q.1 - w i (q.1 - q.2)) ^ 2 / ‖q.2‖ ^ ((d : ℝ) + θ)) with hF
  have hFm : Measurable F := by
    have h1 : Continuous (fun q : Euc d × Euc d => vnorm (fun i => w i q.1)) :=
      elemb_vnorm_continuous (f := fun i (q : Euc d × Euc d) => w i q.1)
        fun i => (hwc i).comp continuous_fst
    have h2 : Continuous (fun q : Euc d × Euc d => vnorm (fun i => w i (q.1 - q.2))) :=
      elemb_vnorm_continuous (f := fun i (q : Euc d × Euc d) => w i (q.1 - q.2))
        fun i => (hwc i).comp (continuous_fst.sub continuous_snd)
    have h3 : Continuous (fun q : Euc d × Euc d => vnorm (fun i => w i q.1 - w i (q.1 - q.2))) :=
      elemb_vnorm_continuous (f := fun i (q : Euc d × Euc d) => w i q.1 - w i (q.1 - q.2))
        fun i => ((hwc i).comp continuous_fst).sub ((hwc i).comp (continuous_fst.sub continuous_snd))
    have h4 : Continuous (fun q : Euc d × Euc d =>
        (vnorm (fun i => w i q.1) + vnorm (fun i => w i (q.1 - q.2))) ^ (p - 2)) :=
      (h1.add h2).rpow_const (fun _ => Or.inr (by linarith))
    have h5 : Measurable (fun q : Euc d × Euc d => ‖q.2‖ ^ ((d : ℝ) + θ)) :=
      (measurable_norm.comp measurable_snd).pow_const _
    exact ((h4.measurable.mul (h3.measurable.pow_const 2)).div h5).ennreal_ofReal
  set S : ℕ → Set (Euc d) := fun n => {z : Euc d | sa16bd_eps n < ‖z‖} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n => measurableSet_lt measurable_const measurable_norm
  have hSmono : Monotone S := fun m n hmn z hz => lt_of_le_of_lt (sa16bd_eps_anti hmn) hz
  have hdiss : ∀ n x, sa16bd_dissCut d θ p (sa16bd_eps n) (fun y i => w i y) x =
      ∫⁻ z in S n, F (x, z) := fun n x => rfl
  have hdens : ∀ x, dissipationDensity d θ p (fun y i => w i y) x = ∫⁻ z, F (x, z) :=
    fun x => rfl
  -- the integrand vanishes at `z = 0`
  have hF0 : ∀ x, F (x, 0) = 0 := by
    intro x
    simp [hF, vnorm]
  -- measurability in `x` of each cutoff dissipation
  have hmeas : ∀ n, Measurable (fun x : Euc d => ENNReal.ofReal (μ x) *
      sa16bd_dissCut d θ p (sa16bd_eps n) (fun y i => w i y) x) := by
    intro n
    have : Measurable (fun x : Euc d => ∫⁻ z in S n, F (x, z)) :=
      Measurable.lintegral_prod_right' (ν := volume.restrict (S n)) hFm
    exact (hμc.measurable.ennreal_ofReal).mul this
  have hmono : Monotone (fun n : ℕ => fun x : Euc d => ENNReal.ofReal (μ x) *
      sa16bd_dissCut d θ p (sa16bd_eps n) (fun y i => w i y) x) := by
    intro m n hmn x
    exact mul_le_mul' le_rfl (lintegral_mono_set (hSmono hmn))
  -- the supremum over `n` of the cutoff dissipation at `x`
  have hsup : ∀ x, (⨆ n, sa16bd_dissCut d θ p (sa16bd_eps n) (fun y i => w i y) x) =
      dissipationDensity d θ p (fun y i => w i y) x := by
    intro x
    rw [hdens]
    simp only [hdiss]
    simp_rw [← lintegral_indicator (hSm _)]
    rw [← lintegral_iSup]
    · congr 1
      funext z
      by_cases hz : z = 0
      · subst hz
        simp [hF0]
      · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
        obtain ⟨n, hn'⟩ := exists_nat_one_div_lt hn
        refine le_antisymm (iSup_le fun m => Set.indicator_le_self' (fun _ _ => bot_le) z)
          (le_iSup_of_le n ?_)
        rw [Set.indicator_of_mem (show z ∈ S n from hn')]
    · exact fun n => hFm.comp (measurable_prodMk_left) |>.indicator (hSm n)
    · intro m n hmn z
      exact Set.indicator_le_indicator_of_subset (hSmono hmn) (fun _ => bot_le) z
  have hmain : (∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
        dissipationDensity d θ p (fun y i => w i y) x) =
      ⨆ n, ∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
        sa16bd_dissCut d θ p (sa16bd_eps n) (fun y i => w i y) x := by
    rw [← lintegral_iSup hmeas hmono]
    congr 1
    funext x
    rw [← hsup x, ENNReal.mul_iSup]
  rw [hmain]
  exact tendsto_atTop_iSup fun m n hmn => lintegral_mono fun x => hmono hmn x


theorem sa16bd_weighted_leading {d : ℕ} (hd : 1 ≤ d) (θ p : ℝ)
    (hθ0 : 0 < θ) (hθ2 : θ < 2) (hp : 2 ≤ p) (ι : Type u) [Fintype ι] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : Euc d → ℝ, MemCb 2 μ → (∀ x, 0 ≤ μ x) →
      ∀ W : ι → SchwartzMap (Euc d) ℝ,
        Integrable (fun x : Euc d => vnorm (fun i => W i x) ^ p) ∧
        Integrable (fun x : Euc d => μ x * vnorm (fun i => W i x) ^ (p - 2) *
          (∑ i, W i x * fracLap d θ (fun y => W i y) x)) ∧
        (∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
          dissipationDensity d θ p (fun y i => W i y) x) < ⊤ ∧
        ∀ lam : ℝ, 0 ≤ lam →
          -lam * (∫ x : Euc d, μ x * vnorm (fun i => W i x) ^ (p - 2) *
            (∑ i, W i x * fracLap d θ (fun y => W i y) x)) ≤
          -lam * sa16bd_convexityConst p *
            (∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
              dissipationDensity d θ p (fun y i => W i y) x).toReal +
          lam * C * cbNorm 2 μ * (∫ x : Euc d, vnorm (fun i => W i x) ^ p) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨C, hC, hCb⟩ := sa16bd_weighted_cutoff hd θ p hθ0 hθ2 hp ι
  obtain ⟨C0, hC0, hC0b⟩ := sa16bd_lapCut_cb2 hd θ hθ0 hθ2
  refine ⟨C, hC, fun μ hμ hμ0 W => ?_⟩
  have hc : 0 < sa16bd_convexityConst p := by unfold sa16bd_convexityConst; positivity
  have hμc : Continuous μ := by
    have : ContDiff ℝ 2 μ := by simpa using hμ.1
    exact this.continuous
  obtain ⟨Bμ, hBμ⟩ : ∃ B : ℝ, ∀ x, |μ x| ≤ B := by
    obtain ⟨B, hB⟩ := hμ.2 0 (by norm_num)
    exact ⟨B, fun x => by simpa [Real.norm_eq_abs] using hB ⟨x, rfl⟩⟩
  have hwc : ∀ i, Continuous (fun y => W i y) := fun i => (W i).continuous
  -- cutoff-uniform bound on the fractional differences
  set Mℓ : ℝ := ∑ i, C0 * cbNorm 2 (⇑(W i)) with hMℓ
  have hMℓ0 : 0 ≤ Mℓ :=
    Finset.sum_nonneg fun i _ => mul_nonneg hC0 (sa16bd_cbNorm_nonneg _)
  have hMℓi : ∀ i, C0 * cbNorm 2 (⇑(W i)) ≤ Mℓ := fun i =>
    Finset.single_le_sum (f := fun i => C0 * cbNorm 2 (⇑(W i)))
      (fun i _ => mul_nonneg hC0 (sa16bd_cbNorm_nonneg _)) (Finset.mem_univ i)
  have hlapb : ∀ i n x, |sa16bd_lapCut d θ (sa16bd_eps n) (fun y => W i y) x| ≤ Mℓ := fun i n x =>
    ((hC0b _ (sa16bd_memCb2_schwartz (W i)) _ (sa16bd_eps_pos n) x).2).trans (hMℓi i)
  have hlap : ∀ i x, Tendsto (fun n : ℕ => sa16bd_lapCut d θ (sa16bd_eps n) (fun y => W i y) x)
      atTop (𝓝 (fracLap d θ (fun y => W i y) x)) :=
    fun i x => sa16bd_lapCut_tendsto hd hθ0 hθ2 (W i) x
  have hfracb : ∀ i x, |fracLap d θ (fun y => W i y) x| ≤ Mℓ := fun i x =>
    le_of_tendsto (hlap i x).abs (Eventually.of_forall fun n => hlapb i n x)
  -- C4 at every cutoff
  have h4 := fun n : ℕ => hCb μ hμ hμ0 W (sa16bd_eps n) (sa16bd_eps_pos n)
  have hVp_int : Integrable (fun x : Euc d => vnorm (fun i => W i x) ^ p) :=
    sa16bd_Vq_integrable W (by linarith)
  have hTi : Integrable (fun x : Euc d => μ x * vnorm (fun i => W i x) ^ (p - 2) *
      (∑ i, W i x * fracLap d θ (fun y => W i y) x)) :=
    sa16bd_T_integrable hp W μ hμc hBμ (fun i => fracLap d θ (fun y => W i y))
      (fun i => sa16bd_fracLap_aesm hd hθ0 hθ2 (W i)) hfracb hMℓ0
  -- dominated convergence for the energy
  have hE : Tendsto (fun n : ℕ => ∫ x : Euc d, μ x * vnorm (fun i => W i x) ^ (p - 2) *
        (∑ i, W i x * sa16bd_lapCut d θ (sa16bd_eps n) (fun y => W i y) x)) atTop
      (𝓝 (∫ x : Euc d, μ x * vnorm (fun i => W i x) ^ (p - 2) *
        (∑ i, W i x * fracLap d θ (fun y => W i y) x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x : Euc d => (Bμ * ((Fintype.card ι : ℝ) * Mℓ)) * vnorm (fun i => W i x) ^ (p - 1))
      (fun n => (h4 n).2.1.aestronglyMeasurable)
      ((sa16bd_Vq_integrable W (by linarith)).const_mul _)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs]
      exact sa16bd_T_bound hp W μ hBμ
        (fun i y => sa16bd_lapCut d θ (sa16bd_eps n) (fun y => W i y) y) (fun i y => hlapb i n y)
        hMℓ0 x
    · exact (tendsto_finset_sum _ fun i _ => (tendsto_const_nhds (x := W i x)).mul (hlap i x)).const_mul _
  -- monotone convergence for the dissipation
  have hL := sa16bd_diss_tendsto θ p hp (fun i y => W i y) hwc μ hμc
  beta_reduce at hL
  set c := sa16bd_convexityConst p with hcdef
  set K : ℝ := C * cbNorm 2 μ * (∫ x : Euc d, vnorm (fun i => W i x) ^ p) with hK
  set L := ∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
    dissipationDensity d θ p (fun y i => W i y) x with hLdef
  have hn : ∀ n : ℕ, ENNReal.ofReal c * (∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
      sa16bd_dissCut d θ p (sa16bd_eps n) (fun y i => W i y) x) ≤
      ENNReal.ofReal ((∫ x : Euc d, μ x * vnorm (fun i => W i x) ^ (p - 2) *
        (∑ i, W i x * sa16bd_lapCut d θ (sa16bd_eps n) (fun y => W i y) x)) + K) := by
    intro n
    obtain ⟨-, -, hfin, hineq⟩ := h4 n
    rw [← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal hineq
  have hnn : 0 ≤ (∫ x : Euc d, μ x * vnorm (fun i => W i x) ^ (p - 2) *
        (∑ i, W i x * fracLap d θ (fun y => W i y) x)) + K := by
    refine ge_of_tendsto (hE.add_const K) (Eventually.of_forall fun n => ?_)
    obtain ⟨-, -, hfin, hineq⟩ := h4 n
    exact le_trans (mul_nonneg hc.le ENNReal.toReal_nonneg) hineq
  have hle : ENNReal.ofReal c * L ≤ ENNReal.ofReal ((∫ x : Euc d, μ x * vnorm (fun i => W i x) ^ (p - 2) *
        (∑ i, W i x * fracLap d θ (fun y => W i y) x)) + K) :=
    le_of_tendsto_of_tendsto' (ENNReal.Tendsto.const_mul hL (Or.inr ENNReal.ofReal_ne_top))
      (ENNReal.tendsto_ofReal (hE.add_const K)) hn
  have hfin : L < ⊤ := by
    by_contra hcon
    have htop : L = ⊤ := not_lt_top_iff.1 hcon
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne'] at hle
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hle)
  refine ⟨hVp_int, hTi, hfin, fun lam hlam => ?_⟩
  have h1 : c * L.toReal ≤ (∫ x : Euc d, μ x * vnorm (fun i => W i x) ^ (p - 2) *
        (∑ i, W i x * fracLap d θ (fun y => W i y) x)) + K := by
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal hnn] at h2
  have h3 := mul_le_mul_of_nonneg_left h1 hlam
  simp only [hK] at h3
  nlinarith [h3]

end HRS.Whole.AppendixA.BreakdownSA16
