import HRS.MC.S7UCPA
import HRS.MC.S7UCAG

/-!
# S7UCPB: H2 uniformly in the window (part B): `s7_UC_H2_particle_approx_unif_proof`

The proof of `s7_FC_H2_particle_approx_proof` (`S7FCH2G.lean`) at window `a`: the dominated convergence in `t`
(`S7FCH2_dct`) is replaced by `s7_UC_G_strong_tail_unif_proof`, which gives the uniform majorants
`Φ_{L,k} = sup_{t ≥ 0, N ≥ 2} E |N F^{K_{k,L} - h_k}(X_N^t, μ^t)|^Q → 0`, so the time integral is a constant times `T`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCP

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan
  HRS.MC.Sec7.S7FCF5F HRS.MC.Sec7.S7FCF5J HRS.MC.Sec7.S7FCH2

variable {d : ℕ}

/-- The uniform majorant `Φ_{L,k} = ⨆_{t ≥ 0, N ≥ 2} g_{N,L,k}(t)`. -/
def S7UCP_Phi (R : Regime d) (q : ℝ) (K : NonzeroLattice d → ℕ → FRKernel d) {Ω : ℕ → Type}
    [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (L : ℕ) (k : NonzeroLattice d) : ℝ≥0∞ :=
  ⨆ t : {t : ℝ // 0 ≤ t}, ⨆ N : {N : ℕ // 2 ≤ N}, ∫⁻ ω, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy
    (fun x y => (K k L).toFun x y - hTransport d R.D.s (Torus.realMode k) x y)
    (X N t.1.toNNReal ω) (withDensityReal (R.ρ t.1))| ^ q) ∂(P N)

theorem S7UCP_Phi_ge (R : Regime d) (q : ℝ) (K : NonzeroLattice d → ℕ → FRKernel d) {Ω : ℕ → Type}
    [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (L : ℕ) (k : NonzeroLattice d) (N : ℕ) (hN : 2 ≤ N) (t : ℝ) (ht : 0 ≤ t) :
    S7FCH2_g R q (K k L) k (P N) (X N) t ≤ S7UCP_Phi R q K P X L k :=
  le_iSup_of_le ⟨t, ht⟩ (le_iSup (fun N : {N : ℕ // 2 ≤ N} => ∫⁻ ω, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy
    (fun x y => (K k L).toFun x y - hTransport d R.D.s (Torus.realMode k) x y)
    (X N t.toNNReal ω) (withDensityReal (R.ρ t))| ^ q) ∂(P N)) ⟨N, hN⟩)

theorem S7UCP_Phi_tendsto (R : Regime d) {ε₂ c : ℝ} (K : NonzeroLattice d → ℕ → FRKernel d)
    (hK : FCKernelData R ε₂ c K)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    (q : ℝ) (hq : 1 ≤ q) (k : NonzeroLattice d) :
    Tendsto (fun L : ℕ => S7UCP_Phi R q K P X L k) atTop (𝓝 0) := by
  obtain ⟨hc, hε, hεs, hKB, hKc⟩ := hK
  obtain ⟨B, hB⟩ := hKB k
  have hLd : ∀ L, s7_IsFiniteRankSmooth (fun x y => (K k L).toFun x y) := fun L =>
    ⟨(K k L).n, (K k L).f, (K k L).c, (K k L).smooth, (K k L).symm, fun x y => rfl⟩
  exact HRS.MC.Sec7.S7UCA.s7_UC_G_strong_tail_unif_proof R k (fun L => (K k L).toFun) hLd B c hc
    (fun L x y hxy => hB L x y hxy) P X₀ W X hreal ε₂ hε hεs (hKc k) q hq

theorem s7_UC_H2_particle_approx_unif_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    (ε₂ c : ℝ) (K : NonzeroLattice d → ℕ → FRKernel d) (hK : FCKernelData R ε₂ c K) (q : ℝ) (hq : 1 ≤ q)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ S₀ : Finset (NonzeroLattice d), ∀ S : Finset (NonzeroLattice d), S₀ ⊆ S →
      ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, 0 ≤ a →
        Integrable (fun ω => ‖(pairN r T a R.D.s R.ρ (P N) (X N) ω).2 -
          toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (a + t) ω)‖ ^ q)
          (P N) ∧
        ∫ ω, ‖(pairN r T a R.D.s R.ρ (P N) (X N) ω).2 -
          toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (a + t) ω)‖ ^ q
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
  set cq : ℝ := 2 ^ (Q - 1) * (2 * Zc) with hcqdef
  have hcq : 0 ≤ cq := by positivity
  set m0 : ℝ := T ^ (Q / 2 - 1) * cq * T with hm0def
  have hm0 : 0 ≤ m0 := by positivity
  set Δ : ℝ := δ ^ (Q / q) with hΔdef
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hδ _
  set m : ℝ := m0 + 1 with hmdef
  have hm : 0 < m := by linarith
  set e : ℝ := Δ / (2 * m) with hedef
  have he : 0 < e := by positivity
  obtain ⟨S₀, hS₀⟩ := S7FCH2_tail_small r hr (max C2 0) (le_max_right _ _) (ENNReal.ofReal e)
    (ENNReal.ofReal_pos.2 he)
  refine ⟨S₀, fun S hS => ?_⟩
  have hsum : Tendsto (fun L : ℕ => ∑ k ∈ S, S7UCP_Phi R Q K P X L k) atTop (𝓝 0) := by
    have := tendsto_finset_sum S (fun k _ => S7UCP_Phi_tendsto R K hK P X₀ W X hreal Q (by linarith) k)
    simpa using this
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 (hsum.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 he)))
  refine ⟨L₀, fun L hL N hN a ha => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hS' := (hreal N hN1).solution T
  have hmain := S7UCP_main_est R r hr T hT K hK P X₀ W X hreal Q hQ2 (max C2 0) (le_max_right _ _) hF2 S L
    (fun k => S7UCP_Phi R Q K P X L k) (fun k _ N hN t ht => S7UCP_Phi_ge R Q K P X L k N hN t ht) a ha N hN
  have hbnd : ∫⁻ ω, ‖(pairN r T a R.D.s R.ρ (P N) (X N) ω).2 -
      toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (a + t) ω)‖ₑ ^ Q
        ∂(P N) ≤ ENNReal.ofReal Δ := by
    refine hmain.trans ?_
    have htail := hS₀ S hS
    have hs := hL₀ L hL
    have hCq : S7FCH2_Cq d r Q = ENNReal.ofReal cq := by
      unfold S7FCH2_Cq
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        S7FCF5F_two_rpow (Q - 1) (by linarith)]
    have hee : S7FCH2_tail d r (max C2 0) S + ∑ k ∈ S, S7UCP_Phi R Q K P X L k ≤
        ENNReal.ofReal (e + e) := by
      rw [ENNReal.ofReal_add he.le he.le]
      exact add_le_add htail hs
    calc ENNReal.ofReal (T ^ (Q / 2 - 1)) * (S7FCH2_Cq d r Q * (S7FCH2_tail d r (max C2 0) S +
          ∑ k ∈ S, S7UCP_Phi R Q K P X L k) * ENNReal.ofReal T)
        ≤ ENNReal.ofReal (T ^ (Q / 2 - 1)) * (ENNReal.ofReal cq * ENNReal.ofReal (e + e) *
          ENNReal.ofReal T) := by rw [hCq]; gcongr
      _ = ENNReal.ofReal (m0 * (e + e)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hm0def]
          ring
      _ ≤ ENNReal.ofReal Δ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : m0 * (e + e) ≤ m * (e + e) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          have h2 : m * (e + e) = Δ := by
            simp only [hedef]
            field_simp
            norm_num
          linarith
  -- measurability of the difference
  have hdiff := S7UCP_diff_aemeasurable R r T hT a ha S (fun k => K k L) (P N) (X N) hS'.adapted hS'.cont
  set D : Ω N → L2Path d r T := fun ω => (pairN r T a R.D.s R.ρ (P N) (X N) ω).2 -
      toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (a + t) ω)
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

end HRS.MC.Sec7.S7UCP

end
