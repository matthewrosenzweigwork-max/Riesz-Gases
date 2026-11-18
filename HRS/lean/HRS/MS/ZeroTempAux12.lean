import HRS.MS.ZeroTempAux11

/-!
# SA11, packet C2c: the pathwise Duhamel identity for the particle field at zero temperature

`sa11_L_apply`: for `φ ∈ C_c^∞` and almost every `ζ`,
`(Ξ_t ζ)(Jφ) - (Ψ_0 ζ)(T Jφ) = σ_N ∫_0^t flucInteractionRd(U^{r,t}φ; X_r ζ, ρ_r) dr`,
where `Ξ_t = σ(μ_N^t - ρ^t)`, `Ψ_0 = σ(μ_N^0 - ρ^0)` as functionals on `W^{m,p}`.  Inputs: the proved duality identity
(`duality_identity_rd_proof`, the martingale term vanishes at `invβ = 0`), uniqueness of classical solutions, `sa11_Xi_weak`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.ZeroTemp

variable {d : ℕ} {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- At `invβ = 0` the flow is the strong solution. -/
theorem sa11_flow_strong {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {N : ℕ} (hN : 1 ≤ N)
    (hflow : SelectedFlowRd (R N).P (S.dyn N) S.T (R N).X₀ (R N).W (R N).X) (hinv : S.invβ N = 0) :
    IsWholeStrongSolution (R N).P (S.dyn N) S.T (R N).X₀ (R N).W (R N).X := by
  rcases hflow.flow with ⟨hstrong, -⟩ | ⟨-, -, hpos, -⟩ | ⟨-, -, hpos, -⟩
  · exact hstrong
  · exfalso; have : (S.dyn N).invβ = 0 := hinv
    rw [this] at hpos; exact lt_irrefl _ hpos
  · exfalso; have : (S.dyn N).invβ = 0 := hinv
    rw [this] at hpos; exact lt_irrefl _ hpos

section Identity

variable (hd : 1 ≤ d) (hm : mStar d + ⌊(d : ℝ) / p⌋₊ + 1 ≤ m)

include hd hm

theorem sa11_L_apply {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {Γ : ℕ}
    (hΓ : 1 ≤ Γ) {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 3) (Γ + 3) C₀ 𝔈)
    {N : ℕ} (hN : 1 ≤ N) (hinv : S.invβ N = 0) {νbar ν₀ : ℝ} (hν : S.invβ N ≤ νbar)
    (hRg : RdRegimeHolds PDE.Regime.R1 d S.s S.M (S.invβ N) ν₀ ∨ HRS.MS.Star.UlocStarRegime d S.s S.M)
    {Kad : ℝ} (hA : AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) (S.coeff N) S.T Kad)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (h : Sa11TransportData m p (S.coeff N) S.T Kad (mStar d) t)
    (φ : sa11_V d) :
    ∀ᵐ ζ ∂(R N).P,
      (sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X (Real.toNNReal t) ζ) (S.ρ N t)
          (sa11_density_prob hS hN ht)) (sa11_J (m := m) (p := p) φ) -
        (sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X₀ ζ) (S.ρ N 0)
          (sa11_density_prob hS hN ⟨le_rfl, S.hT.le⟩)) (sa11_Phi0 h φ) =
      S.sigma N * ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
        (propagatorW (S.coeff N) r t φ.1) ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) := by
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) S.T := ⟨le_rfl, S.hT.le⟩
  obtain ⟨f, hf⟩ := (hA 0 t le_rfl ht.1 ht.2 φ.1 (sa11_cd2 φ.2) (sa11_wClass_mem φ)).1
  have hU := sa11_uniq hΓ hS hN hν hRg ht hf
  have hmf := hS.mean_field
  have hflow := sa11_flow_strong hN (hS.flow N hN) hinv
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  obtain ⟨ΛV', G₀', hV2⟩ : ∃ ΛV' G₀' : ℝ, VHypRd 2 ΛV' G₀' S.V :=
    ⟨ΛV, G₀, HRS.MP.RdGen.rg_VHyp_mono hS.potential (by omega) le_rfl le_rfl⟩
  haveI := (R N).isProb
  have hD := HRS.MH.DualityRd.duality_identity_rd_proof S.s Λ S.T ΛV' G₀' (S.dyn N) rfl S.hs0 S.hsd (S.hinvβ N)
    hV2 (S.ρ N) (hmf.solution N hN) (sa11_regular_mono (hmf.regular N hN) (by omega))
    (R N).P (R N).X₀ (R N).W (R N).X (hS.flow N hN) ℱ W' hF t ht φ.1 f hf
  -- the zeroth component of the weak jet is the continuous function `U^{0,t}φ`
  have hU0cont : Continuous (propagatorW (S.coeff N) 0 t φ.1) := by
    obtain ⟨hfc, -, -⟩ := sa11_orbit_facts hA le_rfl ht.1 ht.2 φ
    exact hfc.continuous
  have hXi0 := sa11_Xi_weak hd hm hN (S.sigma N) 
  filter_upwards [hD, hflow.init] with ζ hζ hini
  obtain ⟨-, hid⟩ := hζ t ⟨ht.1, le_rfl⟩
  have hsq : Real.sqrt (2 * (S.dyn N).invβ) = 0 := by
    have : (S.dyn N).invβ = 0 := hinv
    rw [this]; simp
  rw [hsq, zero_div, zero_mul, add_zero] at hid
  rw [hf.terminal] at hid
  have hf0 : f 0 = propagatorW (S.coeff N) 0 t φ.1 := (hU 0 ⟨le_rfl, ht.1⟩).symm
  rw [hf0, hini] at hid
  have hint : ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N) (f r) ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) =
      ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) r t φ.1)
        ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) :=
    setIntegral_congr_fun measurableSet_Icc fun r hr => by simp only [hU r hr]
  rw [hint] at hid
  have hN0 : 0 < N := hN
  -- the two values of `Ξ`
  have e1 := sa11_Xi_apply hd hm (S.sigma N) ((R N).X (Real.toNNReal t) ζ) (S.ρ N t) (sa11_density_prob hS hN ht) φ
  have e2 := sa11_Xi_weak hd hm hN0 (S.sigma N) ((R N).X₀ ζ) (S.ρ N 0) (sa11_density_prob hS hN hT0)
    (sa11_Phi0 h φ) hU0cont (sa11_Phi0_spec h φ)
  rw [e1, e2]
  have e3 : (N : ℝ)⁻¹ * ∑ i, φ.1 (((R N).X (Real.toNNReal t) ζ) i) =
      HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ)) φ.1 :=
    (HRS.Whole.pair_empirical hN0 _ _).symm
  have e4 : (N : ℝ)⁻¹ * ∑ i, propagatorW (S.coeff N) 0 t φ.1 (((R N).X₀ ζ) i) =
      HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) (propagatorW (S.coeff N) 0 t φ.1) :=
    (HRS.Whole.pair_empirical hN0 _ _).symm
  rw [e3, e4]
  have e5 : ∫ x, propagatorW (S.coeff N) 0 t φ.1 x ∂(HRS.Whole.withDensityReal (S.ρ N 0)) =
      HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 t φ.1) := rfl
  rw [e5]
  have : HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ)) φ.1 -
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) φ.1 -
      (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) (propagatorW (S.coeff N) 0 t φ.1) -
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 t φ.1)) =
      ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) r t φ.1)
        ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) := by
    rw [sub_eq_iff_eq_add']
    exact hid.trans (by ring)
  rw [← this]
  ring

end Identity

end HRS.MS.ZeroTemp
