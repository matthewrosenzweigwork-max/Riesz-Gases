import HRS.MS.MfeConfAux67

/-!
# S.B.1, packet F6 (part 29): the level-`M` entropy inequality in terms of one-body data

`sb1_level_ineq_onebody`: for the regularised particle system (kernel `k`, static Hamiltonian `sb1Hs`, drift `sb1DriftM`),
a profile `ρ_s` (positive densities with positive normalisers, defined for all `s`, e.g. `ρ ∘ clamp`) and one-body data
`ψ_s = -(θ log ρ_s + G_s + V)`, `κ_s = θ log K_s + (N/2) c_s`, `u_s`, `∂_sψ_s`, `κ'_s`, the entropy inequality
`H(μ_t | ℚ_{N,θ⁻¹}(ρ_t)) ≤ H(μ_0 | ℚ_{N,θ⁻¹}(ρ_0)) + ∫_0^t ∫ S_s dμ_s ds`, with the explicit source of `sb1_S_onebody`.
The remaining obligations are therefore the one-body analytic facts (see `HANDOFF_SB2.md`).
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_level_ineq_onebody {θ T : ℝ} (hθ : 0 < θ) (hN : 1 ≤ N) (D : Whole.WholeDyn d) {k : Euc d → ℝ}
    (hk : Measurable k) {ρ : ℝ → Euc d → ℝ} (hρd : ∀ s, Whole.IsProbDensity (ρ s)) (hρp : ∀ s x, 0 < ρ s x)
    (hKp : ∀ s, 0 < Whole.gibbsNormalizer k N θ⁻¹ (Whole.withDensityReal (ρ s)))
    {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ}
    (hP : P4MolData θ T (fun _ => sb1DriftM D k N) (fun _ => sb1Hs D k N) (fun _ _ => 0) μ Kl B K M CV)
    {ψ wψ1 : ℝ → Euc d → ℝ} {u : ℝ → Euc d → Euc d} {κ κ' : ℝ → ℝ}
    (hψdef : ∀ s x, ψ s x = -(θ * Real.log (ρ s x) + sb1G k (ρ s) x + D.V x))
    (hκdef : ∀ s, κ s = θ * Real.log (Whole.gibbsNormalizer k N θ⁻¹ (Whole.withDensityReal (ρ s))) +
      ((N : ℝ) / 2) * sb1c k (ρ s))
    (hψc : Continuous (Function.uncurry ψ)) (hκc : Continuous κ)
    (hψg : ∀ s x, HasFDerivAt (ψ s) (innerSL ℝ (-(u s x))) x)
    (huc : Continuous (Function.uncurry u)) (hu1 : ∀ s, ContDiff ℝ 1 (u s))
    (hdivc : Continuous (Function.uncurry fun s x => sb1divE (u s) x))
    (hwc : Continuous (Function.uncurry wψ1)) (hκ'c : Continuous κ')
    (hψd : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x, HasDerivAt (fun r => ψ r x) (wψ1 s x) s)
    (hκd : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt κ (κ' s) s)
    {Cψ Ck B1 K1 CS : ℝ → ℝ} (hCψ : ∀ s, 0 ≤ Cψ s) (hCk : ∀ s, 0 ≤ Ck s) (hB1 : ∀ s, 0 ≤ B1 s)
    (hK1 : ∀ s, 0 ≤ K1 s) (hCS : ∀ s, 0 ≤ CS s)
    (hψb : ∀ s x, |ψ s x| ≤ Cψ s * (1 + ‖x‖ ^ 2)) (hκb : ∀ s, |κ s| ≤ Ck s)
    (hub : ∀ s x, ‖u s x‖ ≤ B1 s + K1 s * ‖x‖)
    (hSg : ∀ r (x : EucConfig d N), |sb1S θ (fun _ => sb1DriftM D k N) (fun r => sb1wOne (u r))
      (fun s Z => ∑ i, wψ1 s (Z i) + κ' s) r x| ≤ CS r * (1 + p4m_q x))
    (iCψ : IntegrableOn Cψ (Set.Icc 0 T)) (iCk : IntegrableOn Ck (Set.Icc 0 T))
    (iB1 : IntegrableOn B1 (Set.Icc 0 T)) (iK1 : IntegrableOn K1 (Set.Icc 0 T))
    (iCS : IntegrableOn CS (Set.Icc 0 T)) {DS : ℝ → ℝ} (hDS0 : ∀ s, 0 ≤ DS s)
    (hDSi : IntegrableOn DS (Set.Icc 0 T))
    (hSlip : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x y : EucConfig d N,
      |sb1S θ (fun _ => sb1DriftM D k N) (fun r => sb1wOne (u r)) (fun s Z => ∑ i, wψ1 s (Z i) + κ' s) s x -
        sb1S θ (fun _ => sb1DriftM D k N) (fun r => sb1wOne (u r)) (fun s Z => ∑ i, wψ1 s (Z i) + κ' s) s y|
        ≤ DS s * ‖x - y‖ * (1 + ‖x‖ + ‖y‖))
    {Lw : ℝ≥0} (hLw : LipschitzWith Lw (sb1wOne (u 0) : EucConfig d N → EucConfig d N)) {C0 : ℝ}
    (hC0 : ∀ x : EucConfig d N, 0 ≤ sb1Hs D k N x + (∑ i, ψ 0 (x i) + κ 0) + C0)
    (hfin0 : relEntropy (μ 0) (Whole.modulatedGibbs k N θ⁻¹ (Whole.withDensityReal (ρ 0))) ≠ ⊤)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    relEntropy (μ t) (Whole.modulatedGibbs k N θ⁻¹ (Whole.withDensityReal (ρ t))) ≠ ⊤ ∧
      (relEntropy (μ t) (Whole.modulatedGibbs k N θ⁻¹ (Whole.withDensityReal (ρ t)))).toReal ≤
        (relEntropy (μ 0) (Whole.modulatedGibbs k N θ⁻¹ (Whole.withDensityReal (ρ 0)))).toReal +
          ∫ s in Set.Icc (0 : ℝ) t, ∫ y, sb1S θ (fun _ => sb1DriftM D k N) (fun r => sb1wOne (u r))
            (fun s Z => ∑ i, wψ1 s (Z i) + κ' s) s y ∂(μ s) := by
  have hΨfun : (fun s (Z : EucConfig d N) => ∑ i, ψ s (Z i) + κ s) = sb1Psi θ (sb1Hs D k N) k θ⁻¹ ρ := by
    funext s Z
    rw [sb1_Psi_onebody D k hθ (hρp s) (hKp s) hN Z, hκdef s]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψdef]
  have hT := sb1_tilt_onebody (θ := θ) (T := T) (b := fun _ => sb1DriftM D k N) hN hψc hκc hψg huc hu1 hdivc hwc
    hκ'c hψd hκd hCψ hCk hB1 hK1 hCS hψb hκb hub hSg iCψ iCk iB1 iK1 iCS
  rw [hΨfun] at hT
  have hC0' : ∀ x : EucConfig d N, 0 ≤ sb1Hs D k N x + sb1Psi θ (sb1Hs D k N) k θ⁻¹ ρ 0 x + C0 := by
    intro x
    have := hC0 x
    rw [← congrFun (congrFun hΨfun 0) x] at *
    exact this
  exact sb1_level_ineq_Q hP hθ hk (fun s _ => hρd s) (fun s _ => hρp s) (fun s _ => hKp s) hT hDS0 hDSi hSlip
    hLw hC0' hfin0 ht

end HRS.MS.MfeConf
