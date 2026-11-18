import HRS.Sections.AdjKDAux8
import HRS.Sections.AdjKCFinal

/-!
# ADJK-GLUE, part 1: the `E_m`-valued forcing `R_r` of Lemma 5.8 (`moving_integrated_forcing`)

`adjkgY j r ω = -√N F_N^{h_{∇e_j}}(X_r, ρ^r)` (zero for `r < 0`) are the coordinates of the `E_m`-valued forcing
`adjkgR r ω = R^r_N`; this file shows that the coordinate sequence is pathwise honest (`ℓ²`-summable), that
`R` is jointly measurable, that `⟨V^{t,r} R_r, e_k⟩ = -√N F^{h_{∇U^{r,t}e_k}}`, and gives the `E_m`-second moment of `R_r`
from the per-mode second moments.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The mode forcings `-√N F_N^{h_{∇e_j}}(X_r, ρ^r)` for `r ≥ 0`, `0` for `r < 0`. -/
def adjkgY {Ω : Type u} {N : ℕ} (s : ℝ) (ρ : ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N)
    (j : NonzeroLattice d) (r : ℝ) (ω : Ω) : ℝ :=
  if 0 ≤ r then -(Real.sqrt N * modulatedEnergy
    (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (X r.toNNReal ω)
    (withDensityReal (ρ r))) else 0

/-- The `E_m`-valued forcing `R_r` with coordinates `adjkgY`. -/
def adjkgR {Ω : Type u} {N : ℕ} (m s : ℝ) (ρ : ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N)
    (r : ℝ) (ω : Ω) : NegSobolev d m :=
  NegSobolev.ofSeq m (fun j => adjkgY s ρ X j r ω)

theorem adjkg_memlp {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) (y : NonzeroLattice d → ℝ) {B : ℝ}
    (hy : ∀ j, |y j| ≤ B * Lattice.jp j.1 ^ 2) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * y k) 2 := by
  have hb : ∃ C, ∀ k : NonzeroLattice d, |y k / Lattice.jp k.1 ^ 2| ≤ C := by
    refine ⟨B, fun k => ?_⟩
    have hp : 0 < Lattice.jp k.1 ^ 2 := pow_pos (Torus.jp_pos _) 2
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    exact hy k
  have h := NegSobolev.memℓp_of_bounded (d := d) (m := m - 2) (by linarith) _ hb
  have e : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(m - 2)) * (y k / Lattice.jp k.1 ^ 2)) =
      fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * y k := by
    funext k
    have hjp := Torus.jp_pos k.1
    have h2 : Lattice.jp k.1 ^ (-(m - 2)) = Lattice.jp k.1 ^ (-m) * Lattice.jp k.1 ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hjp]
      congr 1
      push_cast
      ring
    rw [h2]
    field_simp
  rw [e] at h
  exact h

theorem adjkg_fourier_ofSeq {m : ℝ} (c : NonzeroLattice d → ℝ)
    (h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (NegSobolev.ofSeq m c) k = c k := by
  unfold NegSobolev.fourierCoeff
  rw [NegSobolev.coord_ofSeq_of_mem c h, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
  simp

theorem adjkg_rho_bdd (hd : 1 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {r : ℝ}
    (hr : 0 ≤ r) : ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧ ∀ x, ρ r x ≤ Λ₀ := by
  have hjc := Q40b.q40b_jointCont hd htr r
  have hc : Continuous (ρ r) :=
    hjc.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨⟨hr, le_rfl⟩, Set.mem_univ _⟩)
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hc
  exact ⟨M, hM0, fun x => (le_abs_self _).trans (hM x)⟩

/-- Pathwise, the mode forcings grow at most like `⟨j⟩²`. -/
theorem adjkg_Y_bound (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {Ω : Type u} {N : ℕ} (X : ℝ≥0 → Ω → Config d N) (r : ℝ) (ω : Ω) :
    ∃ B : ℝ, ∀ j : NonzeroLattice d, |adjkgY s ρ X j r ω| ≤ B * Lattice.jp j.1 ^ 2 := by
  classical
  have hd1 : 1 ≤ d := by omega
  by_cases hr : 0 ≤ r
  swap
  · exact ⟨0, fun j => by simp [adjkgY, hr]⟩
  obtain ⟨cstar, A, hA, hw, hw0, hdom⟩ := movsx_hdom hd1 htr.hs0 htr.hsd
  obtain ⟨Λ₀, hΛ₀, hρ⟩ := adjkg_rho_bdd hd1 htr hr
  obtain ⟨Θ, hΘ⟩ := adjkd_modEn_bound hd1 htr.hs0 htr.hsd hA hdom (X r.toNNReal ω) hΛ₀ hρ
  obtain ⟨C₀, hC₀⟩ := Torus.cbNorm_realMode_le (d := d) 2
  set C₀' : ℝ := max C₀ 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  refine ⟨Real.sqrt N * (A * ((d : ℝ) * C₀')) * |Θ|, fun j => ?_⟩
  have hek : Torus.IsCk 2 (Torus.realMode j) := adjkd_isCk_of_smooth 2 (adjkd_isSmooth_realMode j)
  have hlip := dyncmp_lip_grad hek
  have hL0 : 0 ≤ (d : ℝ) * Torus.cbNorm 2 (Torus.realMode j) :=
    mul_nonneg (Nat.cast_nonneg d) (adjkd_cbNorm_nonneg 2 _)
  have h1 := hΘ _ _ hL0 hlip
  have hcb : Torus.cbNorm 2 (Torus.realMode j) ≤ C₀' * Lattice.jp j.1 ^ 2 :=
    (hC₀ j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hsq : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  simp only [adjkgY, if_pos hr, abs_neg, abs_mul]
  rw [abs_of_nonneg hsq]
  have h2 : |modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j)))
      (X r.toNNReal ω) (withDensityReal (ρ r))| ≤ A * ((d : ℝ) * (C₀' * Lattice.jp j.1 ^ 2)) * |Θ| := by
    refine h1.trans ?_
    have hΘ0 : Θ ≤ |Θ| := le_abs_self Θ
    calc A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j)) * Θ
        ≤ A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j)) * |Θ| :=
          mul_le_mul_of_nonneg_left hΘ0 (mul_nonneg hA hL0)
      _ ≤ A * ((d : ℝ) * (C₀' * Lattice.jp j.1 ^ 2)) * |Θ| := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hA) (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left hcb (Nat.cast_nonneg d)
  calc Real.sqrt N * |modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j)))
        (X r.toNNReal ω) (withDensityReal (ρ r))|
      ≤ Real.sqrt N * (A * ((d : ℝ) * (C₀' * Lattice.jp j.1 ^ 2)) * |Θ|) :=
        mul_le_mul_of_nonneg_left h2 hsq
    _ = Real.sqrt N * (A * ((d : ℝ) * C₀')) * |Θ| * Lattice.jp j.1 ^ 2 := by ring

theorem adjkg_R_fourier {Ω : Type u} {N : ℕ} (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) (X : ℝ≥0 → Ω → Config d N) (r : ℝ) (ω : Ω)
    (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (adjkgR m s ρ X r ω) k = adjkgY s ρ X k r ω := by
  obtain ⟨B, hB⟩ := adjkg_Y_bound hd htr X r ω
  exact adjkg_fourier_ofSeq _ (adjkg_memlp hm _ hB) k

theorem adjkg_R_coord {Ω : Type u} {N : ℕ} (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) (X : ℝ≥0 → Ω → Config d N) (r : ℝ) (ω : Ω)
    (k : NonzeroLattice d) :
    NegSobolev.coord (adjkgR m s ρ X r ω) k = Lattice.jp k.1 ^ (-m) * adjkgY s ρ X k r ω := by
  obtain ⟨B, hB⟩ := adjkg_Y_bound hd htr X r ω
  exact NegSobolev.coord_ofSeq_of_mem _ (adjkg_memlp hm _ hB) k

/-- The coordinate identity `⟨V^{t,r} R_r, e_k⟩ = -√N F^{h_{∇U^{r,t}e_k}}(X_r, ρ^r)`. -/
theorem adjkg_coord_eq {Ω : Type u} {N : ℕ} (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution htr.dyn ρ m Vev)
    {Vev₂ : ℝ → ℝ → NegSobolev d ((d : ℝ) + 3) →L[ℝ] NegSobolev d ((d : ℝ) + 3)}
    (hdual₂ : IsDualEvolution htr.dyn ρ ((d : ℝ) + 3) Vev₂) {CV₂ : ℝ}
    (hCV₂ : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev₂ t u‖ ≤ CV₂)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (Vev t r (adjkgR m s ρ X r ω)) k =
      -(Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s)
          (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k)))) (X r.toNNReal ω)
        (withDensityReal (ρ r))) := by
  classical
  have hd1 : 1 ≤ d := by omega
  set z := adjkgR m s ρ X r ω with hz
  set ψ := propagator htr.dyn ρ r t (Torus.realMode k) with hψ
  obtain ⟨Λ₀, hΛ₀, hρ⟩ := adjkg_rho_bdd hd1 htr hr
  have hF : ∀ j, NegSobolev.fourierCoeff z j = adjkgY s ρ X j r ω := fun j =>
    adjkg_R_fourier hd htr hm X r ω j
  have hseries := adjkd_forcing_series hd htr (m := (d : ℝ) + 3) (by linarith) hdual₂ hCV₂
    (X r.toNNReal ω) hr hrt hΛ₀ hρ k
  have hseries' : HasSum (fun j : NonzeroLattice d => Torus.funRealCoeff ψ j *
      (Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (X r.toNNReal ω)
        (withDensityReal (ρ r))))
      (Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s) (Torus.grad ψ)) (X r.toNNReal ω)
        (withDensityReal (ρ r))) := by
    convert hseries using 1
    funext j
    rw [adjkd_dual_coeff hdual₂ hr hrt j k]
  have e1 : NegSobolev.fourierCoeff (Vev t r z) k = NegSobolev.eval z ψ := by
    rw [← adjkd_eval_realMode, hdual r t hr hrt z _ (adjkd_isSmooth_realMode k)]
  rw [e1]
  unfold NegSobolev.eval
  have e2 : ∀ j : NonzeroLattice d, NegSobolev.fourierCoeff z j * Torus.funRealCoeff ψ j =
      -(Torus.funRealCoeff ψ j * (Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (X r.toNNReal ω)
        (withDensityReal (ρ r)))) := by
    intro j
    rw [hF j]
    simp only [adjkgY, if_pos hr]
    ring
  simp_rw [e2]
  rw [tsum_neg, hseries'.tsum_eq]

/-! ### Measurability -/

theorem adjkg_Y_measurable (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {N : ℕ} {ℱ : Filtration ℝ mΩ}
    {X : ℝ≥0 → Ω → Config d N} (hX : IsProgressive ℱ (ofNNRealTime X)) (j : NonzeroLattice d) :
    Measurable (fun p : ℝ × Ω => adjkgY s ρ X j p.1 p.2) := by
  have hd1 : 1 ≤ d := by omega
  have hn : ∀ n : ℕ, Measurable (fun p : ℝ × Ω =>
      if 0 ≤ p.1 then -(Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j)))
        (X (clampTI ((n : ℝ) + 1) p.1).toNNReal p.2)
        (withDensityReal (ρ (clampTI ((n : ℝ) + 1) p.1)))) else 0) := by
    intro n
    have hT : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hρP : ∀ r ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), IsProbDensity (ρ r) := fun r hr =>
      (Q40b.q40b_meanField hd1 htr hT).density r hr
    have h := adjkd_y_measurable htr hT.le hd1 hX hρP j
    exact Measurable.ite (measurableSet_le measurable_const measurable_fst) h.neg measurable_const
  refine measurable_of_tendsto_metrizable' (atTop : Filter ℕ) hn (tendsto_pi_nhds.2 fun p => ?_)
  refine Tendsto.congr' ?_ tendsto_const_nhds
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge p.1
  filter_upwards [eventually_ge_atTop n₀] with n hn'
  by_cases hp : 0 ≤ p.1
  · have hmem : p.1 ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1) := by
      refine ⟨hp, ?_⟩
      have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn'
      linarith
    simp only [adjkgY, if_pos hp, clampTI_of_mem hmem]
  · simp [adjkgY, hp]

theorem adjkg_R_measurable (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) {Ω : Type u} [mΩ : MeasurableSpace Ω] {N : ℕ}
    {ℱ : Filtration ℝ mΩ} {X : ℝ≥0 → Ω → Config d N} (hX : IsProgressive ℱ (ofNNRealTime X)) :
    Measurable (Function.uncurry (adjkgR m s ρ X)) := by
  refine adjkd_measurable_of_coord (F := Function.uncurry (adjkgR m s ρ X)) fun k => ?_
  have e : ∀ p : ℝ × Ω, NegSobolev.coord (Function.uncurry (adjkgR m s ρ X) p) k =
      Lattice.jp k.1 ^ (-m) * adjkgY s ρ X k p.1 p.2 := fun p =>
    adjkg_R_coord hd htr hm X p.1 p.2 k
  simp_rw [e]
  exact (adjkg_Y_measurable hd htr hX k).const_mul _

/-! ### The second moment of `R_r` in `E_m` -/

theorem adjkg_coord_sq {m : ℝ} (c : NonzeroLattice d → ℝ)
    (h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2) (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.ofSeq m c) k ^ 2 = Lattice.jp k.1 ^ (-2 * m) * c k ^ 2 := by
  rw [NegSobolev.coord_ofSeq_of_mem c h, mul_pow, Torus.jp_rpow_sq]
  congr 2
  ring

theorem adjkg_enorm_sq_eq {m : ℝ} (F : NegSobolev d m) :
    ‖F‖ₑ ^ 2 = ∑' k : NonzeroLattice d,
      ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) * NegSobolev.fourierCoeff F k ^ 2) := by
  obtain ⟨hs, hn⟩ := NegSobolev.coord_sq F
  have h1 : ‖F‖ₑ ^ 2 = ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [h1, hn, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hs]
  refine tsum_congr fun k => ?_
  congr 1
  have h2 : NegSobolev.coord F k = Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k := by
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
    simp
  rw [h2, mul_pow, Torus.jp_rpow_sq]
  congr 2
  ring

/-- Second moment of `R_r` in `E_m` from the per-mode second moments (`m > d/2 + 2`). -/
theorem adjkg_R_moment (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ}
    (X : ℝ≥0 → Ω → Config d N) (r : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hmeas : ∀ j : NonzeroLattice d, Measurable (fun ω => adjkgY s ρ X j r ω))
    (hL2 : ∀ j : NonzeroLattice d, ∫⁻ ω, ‖adjkgY s ρ X j r ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal ((K * Lattice.jp j.1 ^ 2) ^ 2)) :
    ∫⁻ ω, ‖adjkgR m s ρ X r ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (K ^ 2 * ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (-(2 * (m - 2)))) := by
  have hS : Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-(2 * (m - 2))) :=
    summable_jp_rpow (d := d) (m - 2) (by linarith)
  have hjp0 : ∀ j : NonzeroLattice d, 0 ≤ Lattice.jp j.1 ^ (-2 * m) := fun j =>
    Real.rpow_nonneg (Torus.jp_pos _).le _
  have e1 : ∀ ω, ‖adjkgR m s ρ X r ω‖ₑ ^ 2 = ∑' j : NonzeroLattice d,
      ENNReal.ofReal (Lattice.jp j.1 ^ (-2 * m)) * ‖adjkgY s ρ X j r ω‖ₑ ^ 2 := by
    intro ω
    rw [adjkg_enorm_sq_eq]
    refine tsum_congr fun j => ?_
    rw [adjkg_R_fourier hd htr hm X r ω j, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (hjp0 j), Real.norm_eq_abs, sq_abs]
  have hmj : ∀ j : NonzeroLattice d, Measurable (fun ω =>
      ENNReal.ofReal (Lattice.jp j.1 ^ (-2 * m)) * ‖adjkgY s ρ X j r ω‖ₑ ^ 2) := fun j =>
    ((measurable_enorm.comp (hmeas j)).pow_const 2).const_mul _
  simp_rw [e1]
  rw [lintegral_tsum fun j => (hmj j).aemeasurable]
  have hterm : ∀ j : NonzeroLattice d, ∫⁻ ω, ENNReal.ofReal (Lattice.jp j.1 ^ (-2 * m)) *
      ‖adjkgY s ρ X j r ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (K ^ 2 * Lattice.jp j.1 ^ (-(2 * (m - 2)))) := by
    intro j
    have hm2 : Measurable (fun ω => ‖adjkgY s ρ X j r ω‖ₑ ^ 2) :=
      (measurable_enorm.comp (hmeas j)).pow_const 2
    rw [lintegral_const_mul _ hm2]
    calc ENNReal.ofReal (Lattice.jp j.1 ^ (-2 * m)) * ∫⁻ ω, ‖adjkgY s ρ X j r ω‖ₑ ^ 2 ∂P
        ≤ ENNReal.ofReal (Lattice.jp j.1 ^ (-2 * m)) * ENNReal.ofReal ((K * Lattice.jp j.1 ^ 2) ^ 2) :=
          mul_le_mul' le_rfl (hL2 j)
      _ = ENNReal.ofReal (K ^ 2 * Lattice.jp j.1 ^ (-(2 * (m - 2)))) := by
          rw [← ENNReal.ofReal_mul (hjp0 j)]
          congr 1
          have hjp := Torus.jp_pos j.1
          have h4 : Lattice.jp j.1 ^ (-2 * m) * Lattice.jp j.1 ^ (4 : ℕ) =
              Lattice.jp j.1 ^ (-(2 * (m - 2))) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hjp]
            congr 1
            push_cast
            ring
          calc Lattice.jp j.1 ^ (-2 * m) * (K * Lattice.jp j.1 ^ 2) ^ 2
              = K ^ 2 * (Lattice.jp j.1 ^ (-2 * m) * Lattice.jp j.1 ^ (4 : ℕ)) := by ring
            _ = _ := by rw [h4]
  refine (ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (Torus.jp_pos _).le _)) (hS.mul_left _), tsum_mul_left]

end HRS.AdjK
