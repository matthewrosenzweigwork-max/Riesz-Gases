import HRS.MC.S7FCH2B

/-!
# H2, part C: the estimate at a fixed time (prefix `S7FCH2_`)

`S7FCH2_pertime`: for `q ≥ 2` and a fixed time `t ≥ 0`,
`E ‖ℬ_N^t - ℬ_N^{S,K,t}‖^q ≤ 2^{q-1} · 2 · Z^{q/2-1} ∑_k ⟨k⟩^{4-2r-2q} w_k`
with `w_k = ε_k` for `k ∈ S` (a bound for `E |N F^{K_k - h_{∇e_k}}|^q`) and `w_k = C₂ ⟨k⟩^{2q}` (F2) for `k ∉ S`.

The difference of the two centred fields is `U - E U` with `U = ℬ̃ - ℬ̃^{S,K} = ofSeq (u)`, `u_k = -N F^{K_k - h_k}` on `S`
and `u_k = N F^{h_k}` off `S` (linearity of `modulatedEnergy`, part B); `ofSeq` is honest a.e. because
`H'(a) < ⊤` a.e. (part A).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH2

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan
  HRS.MC.Sec7.S7FCF5F

variable {d : ℕ}

open Classical in
/-- The weights: `ε_k` on `S`, the F2 moment bound off `S`. -/
def S7FCH2_wu (S : Finset (NonzeroLattice d)) (C2 q : ℝ) (ε : NonzeroLattice d → ℝ≥0∞)
    (k : NonzeroLattice d) : ℝ≥0∞ :=
  if k ∈ S then ε k else ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (2 * q))

/-- `Z^{q/2-1} ∑_k ⟨k⟩^{4-2r-2q} w_k`. -/
def S7FCH2_Hbd (d : ℕ) (r q : ℝ) (w : NonzeroLattice d → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (fcf5Z d r ^ (q / 2 - 1)) *
    ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * w k

theorem S7FCH2_wsum_C (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (q C2 : ℝ) (hC2 : 0 ≤ C2) :
    ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) *
        ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (2 * q)) = ENNReal.ofReal (C2 * fcf5Z d r) := by
  have hsum : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (4 - 2 * r) :=
    HRS.MC.Sec7.S7FCF5B.fcf5_D1a_summable_proof r hr
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have h1 : ∀ k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) *
      ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (2 * q)) = ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (4 - 2 * r)) := by
    intro k
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hjp k).le _), S7FCF5F_exp_id (hjp k) r q C2]
  rw [tsum_congr h1, ← ENNReal.ofReal_tsum_of_nonneg
    (f := fun k : NonzeroLattice d => C2 * Lattice.jp k.1 ^ (4 - 2 * r))
    (fun k => mul_nonneg hC2 (Real.rpow_nonneg (hjp k).le _)) (hsum.mul_left C2), tsum_mul_left]
  rfl

theorem S7FCH2_memlp_finsupp (m : ℝ) (S : Finset (NonzeroLattice d)) (b : NonzeroLattice d → ℝ)
    (hb : ∀ k, k ∉ S → b k = 0) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * b k) 2 := by
  rw [Torus.memℓp_two_iff]
  refine summable_of_ne_finset_zero (s := S) fun k hk => ?_
  simp [hb k hk]

theorem S7FCH2_pertime (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (q : ℝ) (hq : 2 ≤ q)
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (t : ℝ) (ht : 0 ≤ t) (hXt : Measurable (X t.toNNReal))
    {c : ℝ} (hc : EnvelopeConst (d := d) R.D.s c)
    (S : Finset (NonzeroLattice d)) (Kf : NonzeroLattice d → FRKernel d)
    (C2 : ℝ) (hC2 : 0 ≤ C2)
    (hF2 : ∀ k : NonzeroLattice d, Integrable (fun ω => |S7FCF5F_c R X t k ω| ^ q) P ∧
      ∫ ω, |S7FCF5F_c R X t k ω| ^ q ∂P ≤ C2 * Lattice.jp k.1 ^ (2 * q))
    (ε : NonzeroLattice d → ℝ≥0∞)
    (hε : ∀ k ∈ S, ∫⁻ ω, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy
      (fun x y => (Kf k).toFun x y - hTransport d R.D.s (Torus.realMode k) x y)
      (X t.toNNReal ω) (withDensityReal (R.ρ t))| ^ q) ∂P ≤ ε k) :
    ∫⁻ ω, ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω -
        fcPartAt r S Kf (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ ^ q ∂P ≤
      (2 : ℝ≥0∞) ^ (q - 1) * (S7FCH2_Hbd d r q (S7FCH2_wu S C2 q ε) + S7FCH2_Hbd d r q (S7FCH2_wu S C2 q ε)) := by
  classical
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hq1 : (1 : ℝ) < q := by linarith
  have := S7FCH2_isProb R ht
  have hsd : R.D.s < d := alltime_hsd R
  -- the coefficients
  set a : NonzeroLattice d → Ω → ℝ := fun k ω => S7FCF5F_c R X t k ω with ha_def
  set e : NonzeroLattice d → Ω → ℝ := fun k ω => (N : ℝ) * modulatedEnergy
      (fun x y => (Kf k).toFun x y - hTransport d R.D.s (Torus.realMode k) x y)
      (X t.toNNReal ω) (withDensityReal (R.ρ t)) with he_def
  set u : NonzeroLattice d → Ω → ℝ := fun k ω => if k ∈ S then -(e k ω) else a k ω with hu_def
  have hmeT : ∀ k : NonzeroLattice d, Measurable (fun ω => modulatedEnergy
      (hTransport d R.D.s (Torus.realMode k)) (X t.toNNReal ω) (withDensityReal (R.ρ t))) := by
    intro k
    have hh := (HRS.MC.Sec7.S7FCW3.s7fcw3_hT_meas_symm hsd (HRS.FieldSingAux.isSmooth_realMode k)).1
    exact (HRS.MC.Sec7.S7FCW3.s7fcw3_me_meas (N := N) (hTransport d R.D.s (Torus.realMode k)) hh
      (withDensityReal (R.ρ t))).comp hXt
  have hmeK : ∀ k : NonzeroLattice d, Measurable (fun ω => modulatedEnergy (Kf k).toFun (X t.toNNReal ω)
      (withDensityReal (R.ρ t))) := by
    intro k
    exact (HRS.MC.Sec7.S7FCW3.s7fcw3_me_meas (N := N) (Kf k).toFun (S7FCH2_fr_cont (Kf k)).measurable
      (withDensityReal (R.ρ t))).comp hXt
  have ham : ∀ k, Measurable (a k) := fun k => (hmeT k).const_mul (N : ℝ)
  have hbm : ∀ k, Measurable (fun ω => if k ∈ S then (N : ℝ) * modulatedEnergy (Kf k).toFun (X t.toNNReal ω)
      (withDensityReal (R.ρ t)) else 0) := by
    intro k
    by_cases hk : k ∈ S
    · simp only [if_pos hk]
      exact (hmeK k).const_mul (N : ℝ)
    · simp only [if_neg hk]
      exact measurable_const
  have hem : ∀ k, Measurable (e k) := by
    intro k
    have hlin : ∀ ω, e k ω = (N : ℝ) * modulatedEnergy (Kf k).toFun (X t.toNNReal ω) (withDensityReal (R.ρ t)) -
        a k ω := by
      intro ω
      simp only [he_def, ha_def, S7FCF5F_c]
      rw [S7FCH2_me_sub R ht hc k (Kf k) (X t.toNNReal ω)]
      ring
    have : e k = fun ω => (N : ℝ) * modulatedEnergy (Kf k).toFun (X t.toNNReal ω) (withDensityReal (R.ρ t)) -
        a k ω := funext hlin
    rw [this]
    exact ((hmeK k).const_mul (N : ℝ)).sub (ham k)
  have hum : ∀ k, Measurable (u k) := by
    intro k
    by_cases hk : k ∈ S
    · simp only [hu_def, if_pos hk]
      exact (hem k).neg
    · simp only [hu_def, if_neg hk]
      exact ham k
  -- weights
  have hwu : ∀ k, ∫⁻ ω, ENNReal.ofReal (|u k ω| ^ q) ∂P ≤ S7FCH2_wu S C2 q ε k := by
    intro k
    by_cases hk : k ∈ S
    · simp only [hu_def, S7FCH2_wu, if_pos hk, abs_neg]
      exact hε k hk
    · simp only [hu_def, S7FCH2_wu, if_neg hk]
      obtain ⟨hi, hb⟩ := hF2 k
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)]
      exact ENNReal.ofReal_le_ofReal hb
  -- the fields
  set Atil : Ω → NegSobolev d r := fun ω => quadFieldTilde r R.D.s (withDensityReal (R.ρ t)) (X t.toNNReal ω)
    with hAtil_def
  set Btil : Ω → NegSobolev d r := fun ω => fcPartTilde r S Kf (withDensityReal (R.ρ t)) (X t.toNNReal ω)
    with hBtil_def
  have hAtil : ∀ ω, Atil ω = NegSobolev.ofSeq r (fun k => a k ω) := fun ω => rfl
  have hBtil : ∀ ω, Btil ω = NegSobolev.ofSeq r (fun k => if k ∈ S then (N : ℝ) *
      modulatedEnergy (Kf k).toFun (X t.toNNReal ω) (withDensityReal (R.ρ t)) else 0) := by
    intro ω
    simp only [hBtil_def, fcPartTilde]
  have hAm : Measurable Atil := by
    have := HRS.MC.Sec7.S7FCW12.s7fcw12_measurable_ofSeq (m := r) (fun (ω : Ω) (k : NonzeroLattice d) => a k ω) ham
    exact this
  have hBm : Measurable Btil := by
    have := HRS.MC.Sec7.S7FCW12.s7fcw12_measurable_ofSeq (m := r)
      (fun (ω : Ω) (k : NonzeroLattice d) => if k ∈ S then (N : ℝ) *
        modulatedEnergy (Kf k).toFun (X t.toNNReal ω) (withDensityReal (R.ρ t)) else 0) hbm
    have h2 : Btil = fun ω => NegSobolev.ofSeq r (fun k => if k ∈ S then (N : ℝ) *
        modulatedEnergy (Kf k).toFun (X t.toNNReal ω) (withDensityReal (R.ρ t)) else 0) := funext hBtil
    rw [h2]
    exact this
  -- the a-bounds
  have hHa : ∫⁻ ω, S7FCF5F_H d r q (fun k => a k ω) ∂P ≤ ENNReal.ofReal (S7FCF5F_Ch d r q C2) :=
    S7FCF5F_H_lint P r q C2 hr hq hC2 a ham hF2
  have hH'a : ∫⁻ ω, S7FCH2_H' d r q (fun k => a k ω) ∂P ≤ ENNReal.ofReal (C2 * fcf5Z d r) := by
    refine (S7FCH2_H'_lint P r q hq a ham (fun k => ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (2 * q))) ?_).trans
      (S7FCH2_wsum_C r hr q C2 hC2).le
    intro k
    obtain ⟨hi, hb⟩ := hF2 k
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)]
    exact ENNReal.ofReal_le_ofReal hb
  have hAint : Integrable Atil P := by
    refine ⟨hAm.aestronglyMeasurable, ?_⟩
    have hmain := (S7FCH2_tail_ae P (fun ω => ‖Atil ω‖ₑ)
      (fun ω => S7FCF5F_H d r q (fun k => a k ω)) (fun ω => ‖Atil ω‖ₑ) hq1
      ((S7FCF5F_H_meas r q a ham)) (Filter.Eventually.of_forall fun ω => by
        rw [hAtil]; exact S7FCH2_enorm_le_H r hr q hq _)
      (Filter.Eventually.of_forall fun ω => le_self_add)).1
    have hlt : (∫⁻ ω, ‖Atil ω‖ₑ ∂P) ^ q < ⊤ :=
      lt_of_le_of_lt hmain (lt_of_le_of_lt hHa ENNReal.ofReal_lt_top)
    exact (ENNReal.rpow_lt_top_iff_of_pos (by linarith)).1 hlt
  -- honesty of `ofSeq` for `a`, a.e.
  have hhon : ∀ᵐ ω ∂P, Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) * a k ω) 2 := by
    have hae : ∀ᵐ ω ∂P, S7FCH2_H' d r q (fun k => a k ω) < ⊤ :=
      ae_lt_top (S7FCH2_H'_meas r q a ham)
        (lt_of_le_of_lt hH'a ENNReal.ofReal_lt_top).ne
    filter_upwards [hae] with ω hω
    exact S7FCH2_memlp_of_H_lt_top r hr q hq _ hω
  have hbhon : ∀ ω, Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) * (if k ∈ S then (N : ℝ) *
      modulatedEnergy (Kf k).toFun (X t.toNNReal ω) (withDensityReal (R.ρ t)) else 0)) 2 := by
    intro ω
    exact S7FCH2_memlp_finsupp r S _ fun k hk => by simp [hk]
  -- `U = ofSeq u` a.e.
  set U : Ω → NegSobolev d r := fun ω => Atil ω - Btil ω with hU_def
  have hUu : ∀ᵐ ω ∂P, U ω = NegSobolev.ofSeq r (fun k => u k ω) := by
    filter_upwards [hhon] with ω hω
    simp only [hU_def]
    rw [hAtil, hBtil, ← S7FCH2_ofSeq_sub r _ _ hω (hbhon ω)]
    congr 1
    funext k
    by_cases hk : k ∈ S
    · simp only [hu_def, if_pos hk, he_def, ha_def, S7FCF5F_c]
      rw [S7FCH2_me_sub R ht hc k (Kf k) (X t.toNNReal ω)]
      ring
    · simp only [hu_def, if_neg hk, sub_zero]
  have hUm : Measurable U := hAm.sub hBm
  -- the bound for `u`
  by_cases hfin : S7FCH2_Hbd d r q (S7FCH2_wu S C2 q ε) = ⊤
  · rw [hfin]
    have : (2 : ℝ≥0∞) ^ (q - 1) ≠ 0 := (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
    simp [this]
  have hHu : ∫⁻ ω, S7FCF5F_H d r q (fun k => u k ω) ∂P ≤ S7FCH2_Hbd d r q (S7FCH2_wu S C2 q ε) := by
    show ∫⁻ ω, ENNReal.ofReal (fcf5Z d r ^ (q / 2 - 1)) * S7FCH2_H' d r q (fun k => u k ω) ∂P ≤ _
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (S7FCH2_H'_lint P r q hq u hum _ hwu)
  have hUint : Integrable U P := by
    refine ⟨hUm.aestronglyMeasurable, ?_⟩
    have hmain := (S7FCH2_tail_ae P (fun ω => ‖U ω‖ₑ)
      (fun ω => S7FCF5F_H d r q (fun k => u k ω)) (fun ω => ‖U ω‖ₑ) hq1
      (S7FCF5F_H_meas r q u hum) (by
        filter_upwards [hUu] with ω hω
        rw [hω]; exact S7FCH2_enorm_le_H r hr q hq _)
      (Filter.Eventually.of_forall fun ω => le_self_add)).1
    have hlt : (∫⁻ ω, ‖U ω‖ₑ ∂P) ^ q < ⊤ :=
      lt_of_le_of_lt hmain (lt_of_le_of_lt hHu (lt_top_iff_ne_top.2 hfin))
    exact (ENNReal.rpow_lt_top_iff_of_pos (by linarith)).1 hlt
  have hBint : Integrable Btil P := by
    have : Btil = fun ω => Atil ω - U ω := by
      funext ω
      simp [hU_def]
    rw [this]
    exact hAint.sub hUint
  -- the centred difference
  have hdiff : ∀ ω, quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω -
      fcPartAt r S Kf (fun t => withDensityReal (R.ρ t)) P X t ω = U ω - ∫ ω', U ω' ∂P := by
    intro ω
    have h1 : ∫ ω', U ω' ∂P = ∫ ω', Atil ω' ∂P - ∫ ω', Btil ω' ∂P := integral_sub hAint hBint
    rw [h1]
    simp only [quadFieldAt, fcPartAt, hU_def, hAtil_def, hBtil_def]
    abel
  -- Jensen
  have hBH : ∀ᵐ ω ∂P, ‖U ω‖ₑ ^ q ≤ S7FCF5F_H d r q (fun k => u k ω) := by
    filter_upwards [hUu] with ω hω
    rw [hω]; exact S7FCH2_enorm_le_H r hr q hq _
  have hZ : ∀ᵐ ω ∂P, ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω -
      fcPartAt r S Kf (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ ≤ ‖U ω‖ₑ + ∫⁻ ω', ‖U ω'‖ₑ ∂P :=
    Filter.Eventually.of_forall fun ω => by
      rw [hdiff ω]
      exact enorm_sub_le.trans (add_le_add le_rfl (enorm_integral_le_lintegral_enorm U))
  obtain ⟨hβq, hmain⟩ := S7FCH2_tail_ae P (fun ω => ‖U ω‖ₑ) (fun ω => S7FCF5F_H d r q (fun k => u k ω))
    (fun ω => ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω -
      fcPartAt r S Kf (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ) hq1 (S7FCF5F_H_meas r q u hum) hBH hZ
  refine hmain.trans ?_
  exact mul_le_mul' le_rfl (add_le_add hHu (hβq.trans hHu))

end HRS.MC.Sec7.S7FCH2

end
