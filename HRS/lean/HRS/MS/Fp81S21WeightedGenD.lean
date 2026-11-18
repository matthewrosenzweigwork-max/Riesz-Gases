import HRS.Torus.Basic
import HRS.MS.S104eC3A
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Fp81.S21

open HRS

local notation "J" => iteratedFDeriv ℝ

private theorem fp81s21_b3_jet_equicontinuous {d k : ℕ}
    {gn : ℕ → Euc d → ℝ} {H : Euc d → ℝ}
    (hcn : ∀ n, ContDiff ℝ (k + 1) (gn n))
    (hHc : Continuous H) (hH0 : ∀ x, 0 ≤ H x)
    (hbn : ∀ n m, m ≤ k + 1 → ∀ x, ‖J m (gn n) x‖ ≤ H x)
    (m : ℕ) (hm : m ≤ k) :
    Equicontinuous (fun n x => J m (gn n) x) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall x (1 : ℝ)).exists_bound_of_continuousOn
    (s := closedBall x (1 : ℝ)) (f := H) hHc.continuousOn
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hCbound_all : ∀ n z, z ∈ closedBall x (1 : ℝ) →
      ‖fderiv ℝ (J m (gn n)) z‖ ≤ C := by
    intro n z hz
    rw [norm_fderiv_iteratedFDeriv]
    have hjet := hbn n (m + 1) (by omega) z
    have henv := hC₀ z hz
    have henv' : H z ≤ C := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hH0 z)] at henv
      exact henv.trans (le_max_left _ _)
    exact hjet.trans henv'
  refine ⟨min 1 (ε / (C + 1)), ?_, ?_⟩
  · positivity
  · intro y hy n
    have hxball : x ∈ closedBall x (1 : ℝ) := by simp
    have hydist1 : dist y x < 1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hyball : y ∈ closedBall x (1 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm]
      exact le_of_lt hydist1
    have hdiff : DifferentiableAt ℝ (J m (gn n)) x :=
      (hcn n).differentiable_iteratedFDeriv (m := m)
        (by exact_mod_cast (Nat.lt_succ_of_le hm)) x
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (f := J m (gn n)) (s := closedBall x 1) (x := x) (y := y)
      (fun z hz => (hcn n).differentiable_iteratedFDeriv (m := m)
        (by exact_mod_cast (Nat.lt_succ_of_le hm)) z)
      (fun z hz => hCbound_all n z hz) (convex_closedBall x 1) hxball hyball
    have hdist : dist (J m (gn n) x) (J m (gn n) y) ≤ C * dist y x := by
      simpa [dist_eq_norm, norm_sub_rev] using hmv
    have hydistε : dist y x < ε / (C + 1) := lt_of_lt_of_le hy (min_le_right _ _)
    have hprod : C * dist y x < ε := by
      have hprodle : C * dist y x ≤ C * (ε / (C + 1)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hydistε) hC
      have hfrac : C / (C + 1) < 1 := (div_lt_one (by linarith [hC])).2 (by linarith)
      have hstrict : C * (ε / (C + 1)) < ε := by
        calc
          C * (ε / (C + 1)) = (C / (C + 1)) * ε := by ring
          _ < 1 * ε := mul_lt_mul_of_pos_right hfrac hε
          _ = ε := by ring
      exact hprodle.trans_lt hstrict
    exact lt_of_le_of_lt hdist hprod

private theorem fp81s21_b3_source_jet_local_uniform {d k : ℕ}
    {gn : ℕ → Euc d → ℝ} {g : Euc d → ℝ}
    (hcn : ∀ n, ContDiff ℝ (k + 1) (gn n))
    (hc : ContDiff ℝ (k + 1) g)
    {H : Euc d → ℝ} (hHc : Continuous H)
    (hH0 : ∀ x, 0 ≤ H x)
    (hbn : ∀ n m, m ≤ k + 1 → ∀ x, ‖J m (gn n) x‖ ≤ H x)
    (hb : ∀ m, m ≤ k + 1 → ∀ x, ‖J m g x‖ ≤ H x)
    (heq : ∀ x, ∀ᶠ n in atTop, ∀ m ≤ k,
      J m (gn n) x = J m g x)
    (m : ℕ) (hm : m ≤ k) :
    TendstoLocallyUniformly (fun n => J m (gn n)) (J m g) atTop := by
  let F : ℕ → Euc d → (Euc d [×m]→L[ℝ] ℝ) := fun n => J m (gn n)
  let G : Euc d → (Euc d [×m]→L[ℝ] ℝ) := J m g
  have hcontF : ∀ n, Continuous (F n) := by
    intro n
    exact (hcn n).continuous_iteratedFDeriv (by exact_mod_cast (Nat.le_trans hm (Nat.le_succ k)))
  have hcontG : Continuous G :=
    hc.continuous_iteratedFDeriv (by exact_mod_cast (Nat.le_trans hm (Nat.le_succ k)))
  have hpt : Tendsto F atTop (𝓝 G) := by
    rw [tendsto_pi_nhds]
    intro x
    have he : ∀ᶠ n in atTop, F n x = G x := by
      filter_upwards [heq x] with n hn
      exact hn m hm
    exact tendsto_const_nhds.congr' (he.mono fun n hn => hn.symm)
  have hEqui : Equicontinuous (fun n x => F n x) := by
    simpa [F] using fp81s21_b3_jet_equicontinuous hcn hHc hH0 hbn m hm
  let 𝔖 : Set (Set (Euc d)) := {K | IsCompact K}
  have hcover : ⋃₀ 𝔖 = (Set.univ : Set (Euc d)) := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      refine mem_sUnion.mpr ⟨{x}, ?_, ?_⟩
      · simpa [𝔖]
      · simp
  have hUF : Tendsto (UniformOnFun.ofFun 𝔖 ∘ F) atTop
      (𝓝 (UniformOnFun.ofFun 𝔖 G)) := by
    apply (EquicontinuousOn.tendsto_uniformOnFun_iff_pi
      (𝔖_compact := fun K hK => hK) hcover
      (fun K hK => hEqui.equicontinuousOn K) atTop G).2
    exact hpt
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  have hUniform : ∀ K ∈ 𝔖, TendstoUniformlyOn
      (UniformOnFun.toFun 𝔖 ∘ (UniformOnFun.ofFun 𝔖 ∘ F))
      (UniformOnFun.toFun 𝔖 (UniformOnFun.ofFun 𝔖 G)) atTop K :=
    (UniformOnFun.tendsto_iff_tendstoUniformlyOn (F := UniformOnFun.ofFun 𝔖 ∘ F)
      (f := UniformOnFun.ofFun 𝔖 G)).1 hUF
  simpa [𝔖, F, G, Function.comp_def] using hUniform K hK

 theorem fp81s21_b3_source_jet_limits {d k : ℕ}
    {gn : ℕ → Euc d → ℝ} {g : Euc d → ℝ}
    (hcn : ∀ n, ContDiff ℝ (k + 1) (gn n))
    (hc : ContDiff ℝ (k + 1) g)
    {H : Euc d → ℝ} (hHc : Continuous H)
    (hHi : Integrable H) (hH0 : ∀ x, 0 ≤ H x)
    (hbn : ∀ n m, m ≤ k + 1 → ∀ x,
      ‖J m (gn n) x‖ ≤ H x)
    (hb : ∀ m, m ≤ k + 1 → ∀ x, ‖J m g x‖ ≤ H x)
    (heq : ∀ x, ∀ᶠ n in atTop, ∀ m ≤ k,
      J m (gn n) x = J m g x) :
    ∀ m ≤ k,
      TendstoLocallyUniformly
        (fun n => J m (gn n)) (J m g) atTop ∧
      Tendsto (fun n =>
        eLpNorm (J m (gn n) - J m g) 1 volume)
        atTop (𝓝 0) := by
  intro m hm
  refine ⟨fp81s21_b3_source_jet_local_uniform hcn hc hHc hH0 hbn hb heq m hm, ?_⟩
  let F : ℕ → Euc d → (Euc d [×m]→L[ℝ] ℝ) := fun n => J m (gn n)
  let G : Euc d → (Euc d [×m]→L[ℝ] ℝ) := J m g
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n
    exact ((hcn n).continuous_iteratedFDeriv
      (by exact_mod_cast (Nat.le_trans hm (Nat.le_succ k)))).aestronglyMeasurable
  have hGmeas : AEStronglyMeasurable G volume :=
    (hc.continuous_iteratedFDeriv
      (by exact_mod_cast (Nat.le_trans hm (Nat.le_succ k)))).aestronglyMeasurable
  have hm' : m ≤ k + 1 := Nat.le_trans hm (Nat.le_succ k)
  have hDCT := tendsto_lintegral_norm_of_dominated_convergence
    (μ := volume) (F := F) (f := G) (bound := H) hFmeas hHi.hasFiniteIntegral
    (fun n => ae_of_all volume fun x => hbn n m hm' x)
    (ae_of_all volume fun x => by
      have he : ∀ᶠ n in atTop, F n x = G x := by
        filter_upwards [heq x] with n hn
        exact hn m hm
      exact tendsto_const_nhds.congr' (he.mono fun n hn => hn.symm))
  have hnorm : (fun n => eLpNorm (F n - G) 1 volume) =
      (fun n => ∫⁻ x, ENNReal.ofReal ‖F n x - G x‖ ∂volume) := by
    funext n
    rw [eLpNorm_one_eq_lintegral_enorm ((hFmeas n).sub hGmeas)]
    simp
  change Tendsto (fun n => eLpNorm (F n - G) 1 volume) atTop (𝓝 0)
  rw [hnorm]
  exact hDCT

#print axioms HRS.Fp81.S21.fp81s21_b3_source_jet_limits

end HRS.Fp81.S21
