import HRS.MS.ZeroTempAux12

/-!
# SA11, packet C2d: the dual-norm bound of the particle field minus its linear approximation

`sa11_L_enorm`: for `L ζ = Ξ_t ζ - Ψ_0 ζ ∘ T` we have almost surely `‖L ζ‖ₑ ≤ ofReal (σ_N Kc / 2) · ∫_0^T ofReal(F + oNΛ + c₂ e) dr`,
from the pathwise Duhamel identity (`sa11_L_apply`), the bound `|Comm| ≤ Kc ‖Jφ‖ (F + oNΛ + c₂ e)` and a countable dense family of jets.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.ZeroTemp

variable {d : ℕ} {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

section Bound

variable (hd : 1 ≤ d) (hm : mStar d + ⌊(d : ℝ) / p⌋₊ + 1 ≤ m)

include hd hm

theorem sa11_L_enorm {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {Γ : ℕ}
    (hΓ : 1 ≤ Γ) {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 3) (Γ + 3) C₀ 𝔈)
    {N : ℕ} (hN : 2 ≤ N) (hinv : S.invβ N = 0) {νbar ν₀ : ℝ} (hν : S.invβ N ≤ νbar)
    (hRg : RdRegimeHolds PDE.Regime.R1 d S.s S.M (S.invβ N) ν₀ ∨ HRS.MS.Star.UlocStarRegime d S.s S.M)
    {Kad : ℝ} (hA : AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) (S.coeff N) S.T Kad)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (h : Sa11TransportData m p (S.coeff N) S.T Kad (mStar d) t)
    {Kc c₂ : ℝ} (hKc : 0 ≤ Kc) {e : ℕ → ℝ}
    (hcomm : ∀ X : EucConfig d N, Function.Injective X → ∀ r₀ t' : ℝ, 0 ≤ r₀ → r₀ ≤ t' → t' ≤ S.T →
      ∀ φ : sa11_V d,
        |commN d S.s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r₀ t' φ.1) x)) X
            (HRS.Whole.withDensityReal (S.ρ N r₀))| ≤
          Kc * ‖sa11_J (m := m) (p := p) φ‖ *
            (rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N r₀)) + oNΛ d S.s C₀ Λ N + c₂ * e N)) :
    ∀ᵐ ζ ∂(R N).P,
      ‖(sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X (Real.toNNReal t) ζ) (S.ρ N t)
          (sa11_density_prob hS (by omega) ht)) -
        sa11_precomp (sa11_Top h) (sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X₀ ζ) (S.ρ N 0)
          (sa11_density_prob hS (by omega) ⟨le_rfl, S.hT.le⟩))‖ₑ ≤
      ENNReal.ofReal (S.sigma N / 2 * Kc) *
        ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
          (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
            oNΛ d S.s C₀ Λ N + c₂ * e N) := by
  have hN1 : 1 ≤ N := by omega
  have hT : 0 ≤ S.T := S.hT.le
  have hσ0 : 0 ≤ S.sigma N := HRS.MP.RdRem.mrr_sigma_nonneg S N
  have hflow := sa11_flow_strong hN1 (hS.flow N hN1) hinv
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  haveI := (R N).isProb
  have hXm := HRS.MP.RdRem.mrr_prog_meas ℱ (R N).X hF.progressive hT
  have hcoll : ∀ t' ∈ Set.Icc (0 : ℝ) S.T, ∀ᵐ ζ ∂(R N).P,
      (R N).X (Real.toNNReal t') ζ ∉ eucCollisionSet d N := fun t' ht' =>
    hflow.no_collision.mono fun ζ hζ => hζ (Real.toNNReal t') (by rw [Real.coe_toNNReal _ ht'.1]; exact ht'.2)
  have hinjAE := HRS.MP.RdRem.mrr_coll_ae (R N).P hT (R N).X hXm hcoll
  refine sa11_enorm_le_of_repr (R N).P
    (fun ζ => (sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X (Real.toNNReal t) ζ) (S.ρ N t)
          (sa11_density_prob hS hN1 ht)) -
        sa11_precomp (sa11_Top h) (sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X₀ ζ) (S.ρ N 0)
          (sa11_density_prob hS hN1 ⟨le_rfl, S.hT.le⟩)))
    (fun ζ => ENNReal.ofReal (S.sigma N / 2 * Kc) *
        ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
          (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
            oNΛ d S.s C₀ Λ N + c₂ * e N)) fun φ => ?_
  filter_upwards [sa11_L_apply hd hm hΓ hS hN1 hinv hν hRg hA ht h φ, hinjAE] with ζ hid hinj
  -- the value of `L ζ` on `J φ`
  have hLφ : ((sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X (Real.toNNReal t) ζ) (S.ρ N t)
          (sa11_density_prob hS hN1 ht)) -
        sa11_precomp (sa11_Top h) (sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X₀ ζ) (S.ρ N 0)
          (sa11_density_prob hS hN1 ⟨le_rfl, S.hT.le⟩))) (sa11_J (m := m) (p := p) φ) =
      S.sigma N * ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
        (propagatorW (S.coeff N) r t φ.1) ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) := by
    rw [ContinuousLinearMap.sub_apply, sa11_precomp_apply, sa11_Top_apply]
    exact hid
  rw [hLφ]
  -- `flucInteractionRd = ½ commN`
  have hflucs : ∀ r ∈ Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) r t φ.1)
      ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) =
      (1 / 2 : ℝ) * commN d S.s (fun x => Torus.matVec S.M.transpose
        (gradient (propagatorW (S.coeff N) r t φ.1) x)) ((R N).X (Real.toNNReal r) ζ)
        (HRS.Whole.withDensityReal (S.ρ N r)) := by
    intro r hr
    have hrT : r ∈ Set.Icc (0 : ℝ) S.T := ⟨hr.1, hr.2.trans ht.2⟩
    have hreg := (sa11_regular_mono ((hS.mean_field.regular N hN1)) (by omega : 3 ≤ Γ + 3)).1 r hrT
    have hslice : HRS.MH.DualityRd.RegSliceRd (S.ρ N r) :=
      ⟨sa11_density_prob hS hN1 hrT, hreg.1, hreg.2.1⟩
    obtain ⟨hfc, -, -⟩ := sa11_orbit_facts hA hr.1 hr.2 ht.2 φ
    obtain ⟨-, -, -, hcb, -⟩ := hA r t hr.1 hr.2 ht.2 φ.1 (sa11_cd2 φ.2) (sa11_wClass_mem φ)
    have hmcb2 : MemCb 2 (propagatorW (S.coeff N) r t φ.1) :=
      ⟨hcb.1.of_le (by exact_mod_cast (by unfold mStar; omega : 2 ≤ mStar d)),
        fun j hj => hcb.2 j (by unfold mStar; omega)⟩
    exact HRS.MS.GenPath.s56_fluc_eq_comm (S.dyn N) hd S.hs0 S.hsd hslice hmcb2 _
  have hint : ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) r t φ.1)
      ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) =
      (1 / 2 : ℝ) * ∫ r in Set.Icc (0 : ℝ) t, commN d S.s (fun x => Torus.matVec S.M.transpose
        (gradient (propagatorW (S.coeff N) r t φ.1) x)) ((R N).X (Real.toNNReal r) ζ)
        (HRS.Whole.withDensityReal (S.ρ N r)) := by
    rw [setIntegral_congr_fun measurableSet_Icc hflucs, integral_const_mul]
  rw [hint]
  set nJ : ℝ := ‖sa11_J (m := m) (p := p) φ‖ with hnJ
  set Ic : ℝ := ∫ r in Set.Icc (0 : ℝ) t, commN d S.s (fun x => Torus.matVec S.M.transpose
        (gradient (propagatorW (S.coeff N) r t φ.1) x)) ((R N).X (Real.toNNReal r) ζ)
        (HRS.Whole.withDensityReal (S.ρ N r)) with hIc
  have hE : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      |commN d S.s (fun x => Torus.matVec S.M.transpose
        (gradient (propagatorW (S.coeff N) r t φ.1) x)) ((R N).X (Real.toNNReal r) ζ)
        (HRS.Whole.withDensityReal (S.ρ N r))| ≤ (Kc * nJ) *
        (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
          oNΛ d S.s C₀ Λ N + c₂ * e N) := by
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) S.T := Set.Icc_subset_Icc le_rfl ht.2
    have h1 := ae_restrict_of_ae_restrict_of_subset hsub hinj
    filter_upwards [h1, ae_restrict_mem measurableSet_Icc] with r hr hrm
    exact hcomm _ hr r t hrm.1 hrm.2 ht.2 φ
  have hpb := sa11_path_bound (mul_nonneg hKc (norm_nonneg _)) ht _ _ hE
  have hKnn : 0 ≤ Kc * nJ := mul_nonneg hKc (norm_nonneg _)
  have habs : |S.sigma N * ((1 / 2 : ℝ) * Ic)| = (S.sigma N / 2) * |Ic| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hσ0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    ring
  rw [habs, ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal (S.sigma N / 2) * ENNReal.ofReal |Ic|
      ≤ ENNReal.ofReal (S.sigma N / 2) * (ENNReal.ofReal (Kc * nJ) *
        ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
          (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
            oNΛ d S.s C₀ Λ N + c₂ * e N)) := by gcongr
    _ = (ENNReal.ofReal (S.sigma N / 2 * Kc) *
        ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
          (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
            oNΛ d S.s C₀ Λ N + c₂ * e N)) * ENNReal.ofReal nJ := by
        rw [ENNReal.ofReal_mul hKc, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ S.sigma N / 2)]
        ring

end Bound

end HRS.MS.ZeroTemp
