import HRS.MC.S7FCH2F
import HRS.MC.S7FCW12F

/-!
# H2, part G: `s7_FC_H2_particle_approx_proof` (the statement of `HRS.MC.Sec7.FCPlan.s7_FC_H2_particle_approx`)

Choose the exponent `Q = max (q+1) 3 > 2, > q`.  By F2 the coefficient moments of order `Q` are `≤ C₂⟨k⟩^{2Q}` uniformly in
`N ≥ 2`, `t ≥ 0`; part D gives a finite `S₀` with mode tail `≤ a` for every `S ⊇ S₀`, and, for each such `S`, an `L₀` with
`∑_{k ∈ S} ∫_0^T φ_{L,k} ≤ b` for `L ≥ L₀` (FC-G + G2 + dominated convergence); part F gives
`E ‖·‖^Q ≤ Δ = δ^{Q/q}` for all `N ≥ 2`; Jensen on the probability space lowers the exponent `Q` to `q`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH2

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan
  HRS.MC.Sec7.S7FCF5F HRS.MC.Sec7.S7FCF5J

variable {d : ℕ}

/-- Jensen on a probability space for an `AEMeasurable` function: `(∫⁻ K)^p ≤ ∫⁻ K^p`, `p > 1`. -/
theorem S7FCH2_jensen_ae {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K : Ω → ℝ≥0∞} (hK : AEMeasurable K P) {p : ℝ} (hp : 1 < p) :
    (∫⁻ ω, K ω ∂P) ^ p ≤ ∫⁻ ω, K ω ^ p ∂P := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  have h1 : ∫⁻ ω, K ω ∂P ≤ (∫⁻ ω, K ω ^ p ∂P) ^ (1 / p) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hK
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simpa using h
  have hp0 : p ≠ 0 := (by linarith : (0 : ℝ) < p).ne'
  calc (∫⁻ ω, K ω ∂P) ^ p ≤ ((∫⁻ ω, K ω ^ p ∂P) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h1 (by linarith)
    _ = ∫⁻ ω, K ω ^ p ∂P := (S7FCF5F_rpow_cancel _ hp0).2

theorem s7_FC_H2_particle_approx_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    (ε₂ c : ℝ) (K : NonzeroLattice d → ℕ → FRKernel d) (hK : FCKernelData R ε₂ c K) (q : ℝ) (hq : 1 ≤ q)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ S₀ : Finset (NonzeroLattice d), ∀ S : Finset (NonzeroLattice d), S₀ ⊆ S →
      ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ N : ℕ, 2 ≤ N →
        Integrable (fun ω => ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2 -
          toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω)‖ ^ q)
          (P N) ∧
        ∫ ω, ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2 -
          toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω)‖ ^ q
          ∂(P N) ≤ δ := by
  classical
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hq0 : 0 < q := by linarith
  set Q : ℝ := max (q + 1) 3 with hQdef
  have hQ3 : 3 ≤ Q := le_max_right _ _
  have hqQ : q + 1 ≤ Q := le_max_left _ _
  have hQ2 : (2 : ℝ) < Q := by linarith
  obtain ⟨C2, hC2⟩ := HRS.MC.Sec7.S7FCW3.s7_FC_F2_B_proof R Q (by linarith)
  have hF2 : ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      Integrable (fun ω => |S7FCF5F_c R (X N) t k ω| ^ Q) (P N) ∧
      ∫ ω, |S7FCF5F_c R (X N) t k ω| ^ Q ∂(P N) ≤ max C2 0 * Lattice.jp k.1 ^ (2 * Q) := by
    intro N hN t ht k
    obtain ⟨hi, hb⟩ := hC2 N hN (P N) (X₀ N) (W N) (X N) (hreal N (by omega)) t ht k
    exact ⟨hi, hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (Torus.jp_pos k.1).le _))⟩
  -- the constants
  have hZ0 : 0 ≤ fcf5Z d r := tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  set Zc : ℝ := fcf5Z d r ^ (Q / 2 - 1) with hZc
  have hZc0 : 0 ≤ Zc := Real.rpow_nonneg hZ0 _
  set m0 : ℝ := T ^ (Q / 2 - 1) * (2 ^ (Q - 1) * (2 * Zc)) with hm0def
  have hm0 : 0 ≤ m0 := by positivity
  set Δ : ℝ := δ ^ (Q / q) with hΔdef
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hδ _
  set m : ℝ := m0 + 1 with hmdef
  have hm : 0 < m := by linarith
  set a : ℝ := Δ / (2 * m * (T + 1)) with hadef
  set b : ℝ := Δ / (2 * m) with hbdef
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  obtain ⟨S₀, hS₀⟩ := S7FCH2_tail_small r hr (max C2 0) (le_max_right _ _) (ENNReal.ofReal a)
    (ENNReal.ofReal_pos.2 ha)
  refine ⟨S₀, fun S hS => ?_⟩
  have hsum : Tendsto (fun L : ℕ => ∑ k ∈ S, ∫⁻ t in Set.Icc (0 : ℝ) T, S7FCH2_phi R Q (K k L) k P X t)
      atTop (𝓝 0) := by
    have := tendsto_finset_sum S (fun k _ => S7FCH2_dct R T hT K hK P X₀ W X hreal Q (by linarith) k)
    simpa using this
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 (hsum.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hb)))
  refine ⟨L₀, fun L hL N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hS' := (hreal N hN1).solution T
  have hmain := S7FCH2_main_est R r hr T hT K hK P X₀ W X hreal Q hQ2 (max C2 0) (le_max_right _ _) hF2 S L N hN
  have hbnd : ∫⁻ ω, ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2 -
      toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω)‖ₑ ^ Q
        ∂(P N) ≤ ENNReal.ofReal Δ := by
    refine hmain.trans ?_
    have htail := hS₀ S hS
    have hs := hL₀ L hL
    have hCq : S7FCH2_Cq d r Q = ENNReal.ofReal (2 ^ (Q - 1) * (2 * Zc)) := by
      unfold S7FCH2_Cq
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        S7FCF5F_two_rpow (Q - 1) (by linarith)]
    have hX : ENNReal.ofReal a * ENNReal.ofReal T + ENNReal.ofReal b = ENNReal.ofReal (a * T + b) := by
      rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_add (mul_nonneg ha.le hT.le) hb.le]
    calc ENNReal.ofReal (T ^ (Q / 2 - 1)) * (S7FCH2_Cq d r Q * (S7FCH2_tail d r (max C2 0) S * ENNReal.ofReal T +
          ∑ k ∈ S, ∫⁻ t in Set.Icc (0 : ℝ) T, S7FCH2_phi R Q (K k L) k P X t))
        ≤ ENNReal.ofReal (T ^ (Q / 2 - 1)) * (S7FCH2_Cq d r Q * (ENNReal.ofReal a * ENNReal.ofReal T +
          ENNReal.ofReal b)) := by gcongr
      _ = ENNReal.ofReal m0 * ENNReal.ofReal (a * T + b) := by
          rw [hX, hCq, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul hm0]
          congr 1
          rw [hm0def]
          ring
      _ ≤ ENNReal.ofReal Δ := by
          rw [← ENNReal.ofReal_mul hm0]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : m0 * (a * T + b) ≤ m * (a * T + b) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          have h2 : m * (a * T + b) = Δ * (T / (T + 1) + 1) / 2 := by
            simp only [hadef, hbdef]
            field_simp
          have h3 : T / (T + 1) ≤ 1 := by
            rw [div_le_one (by linarith)]
            linarith
          rw [h2] at h1
          nlinarith
  -- measurability of the difference
  have hpair := HRS.MC.Sec7.S7FCW12.s7_FC_E_pair_measurable_proof R r hr T hT (P N) hN1 (X₀ N) (W N) (X N)
    (hreal N hN1)
  have hfc := HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_fcPart_aemeasurable R r T hT 0 le_rfl S (fun k => K k L)
    (P N) (X N) hS'.adapted hS'.cont
  have hdiff : AEMeasurable (fun ω => (pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2 -
      toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω))
      (P N) := hpair.snd.sub hfc
  set D : Ω N → L2Path d r T := fun ω => (pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2 -
      toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω)
    with hDdef
  have hhm : AEMeasurable (fun ω => ‖D ω‖ ^ q) (P N) := hdiff.norm.pow_const q
  have hE : ∀ ω, ENNReal.ofReal (‖D ω‖ ^ q) = ‖D ω‖ₑ ^ q := fun ω => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le, ofReal_norm_eq_enorm]
  -- Jensen: from exponent `Q` down to `q`
  have hp : 1 < Q / q := by
    rw [lt_div_iff₀ hq0]
    linarith
  have hJ := S7FCH2_jensen_ae (P N) (K := fun ω => ‖D ω‖ₑ ^ q) (hdiff.enorm.pow_const q) hp
  have hpow : ∀ ω, (‖D ω‖ₑ ^ q) ^ (Q / q) = ‖D ω‖ₑ ^ Q := fun ω => by
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  have hJ' : (∫⁻ ω, ‖D ω‖ₑ ^ q ∂(P N)) ^ (Q / q) ≤ ENNReal.ofReal δ ^ (Q / q) := by
    refine hJ.trans ?_
    simp only [hpow]
    refine hbnd.trans ?_
    rw [hΔdef, ENNReal.ofReal_rpow_of_nonneg hδ.le (by positivity)]
  have hfin : ∫⁻ ω, ‖D ω‖ₑ ^ q ∂(P N) ≤ ENNReal.ofReal δ :=
    (ENNReal.rpow_le_rpow_iff (by positivity : (0 : ℝ) < Q / q)).1 hJ'
  have hlint : ∫⁻ ω, ENNReal.ofReal (‖D ω‖ ^ q) ∂(P N) ≤ ENNReal.ofReal δ := by
    simp only [hE]
    exact hfin
  refine ⟨⟨hhm.aestronglyMeasurable, ?_⟩, ?_⟩
  · show ∫⁻ ω, ‖‖D ω‖ ^ q‖ₑ ∂(P N) < ⊤
    have : ∫⁻ ω, ‖‖D ω‖ ^ q‖ₑ ∂(P N) = ∫⁻ ω, ENNReal.ofReal (‖D ω‖ ^ q) ∂(P N) := by
      refine lintegral_congr fun ω => ?_
      exact Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg _) _)
    rw [this]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _)
      hhm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hδ.le hlint

end HRS.MC.Sec7.S7FCH2

end
