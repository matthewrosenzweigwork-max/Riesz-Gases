import HRS.MS.R26T8AP11f4
import HRS.MS.R26T8AP11gm
import HRS.MS.R26T8AP11s

/-!
# S8.2 T8A P11f (part 5): smooth-kernel potential of a pole-singular local source
`r26t8a_f5_pot_sing`: for `Kc` smooth with bounded jets, `ψ` smooth, `|ψ| ≤ 1`, `ψ = 0` for `|v| > 1/2`, and `Sg v y` with
`C^k` off `v = 0` and `‖D^m_y Sg v y‖ ≤ B jb(y)^M |v|^(-s)` (`s < d`): `V(x,y) = ∫ Kc(x-y-v) ψ(v) Sg(v,y) dv` is `C^k` on `E x E`
with `‖D^i V (x,y)‖ ≤ C BK B jb(y)^M`.  Only `y`-jets of the source are needed (centre derivatives).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- The integrand. -/
def r26t8a_f5_G (Kc : Euc d → ℝ) (ψ : Euc d → ℝ) (Sg : Euc d → Euc d → ℝ) (v : Euc d) (p : Euc d × Euc d) : ℝ :=
  Kc (p.1 - p.2 - v) * (ψ v * Sg v p.2)

theorem r26t8a_f5_pot_sing (d : ℕ) (hd : 2 ≤ d) (k : ℕ) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {M : ℝ}
    (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (chi : Euc d → ℝ), NewtonCutoff chi → ∀ (Kc : Euc d → ℝ) (BK : ℝ),
      ContDiff ℝ (k : WithTop ℕ∞) Kc → (∀ j ≤ k, ∀ u, ‖iteratedFDeriv ℝ j Kc u‖ ≤ BK) →
      ∀ (ψ : Euc d → ℝ), ContDiff ℝ (k : WithTop ℕ∞) ψ → (∀ v, |ψ v| ≤ 1) → (∀ v, 1 / 2 < ‖v‖ → ψ v = 0) →
      ∀ (Sg : Euc d → Euc d → ℝ) (B : ℝ), 0 ≤ B →
      ContDiffOn ℝ (k : WithTop ℕ∞) (Function.uncurry Sg) {q : Euc d × Euc d | q.1 ≠ 0} →
      (∀ v y : Euc d, 0 < ‖v‖ → ‖v‖ ≤ 1 / 2 → ∀ m ≤ k,
        ‖iteratedFDeriv ℝ m (fun y' => Sg v y') y‖ ≤ B * jbracket y ^ M * ‖v‖ ^ (-s)) →
      ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => ∫ v, r26t8a_f5_G Kc ψ Sg v p) ∧
      ∀ i ≤ k, ∀ p : Euc d × Euc d,
        ‖iteratedFDeriv ℝ i (fun p : Euc d × Euc d => ∫ v, r26t8a_f5_G Kc ψ Sg v p) p‖ ≤
          C * BK * B * jbracket p.2 ^ M := by
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  obtain ⟨hmI, hmV⟩ := r26t8a_p11a_mass d hd ((d : ℝ) - s) (by linarith) (by linarith) 1 one_pos
  have hexp : (d : ℝ) - s - d = -s := by ring
  rw [hexp] at hmI hmV
  set Ω : ℝ := sphereArea d * ((1 : ℝ) ^ ((d : ℝ) - s) / ((d : ℝ) - s)) with hΩ
  have hΩ0 : 0 ≤ Ω := by
    have : 0 ≤ ∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-s) :=
      setIntegral_nonneg measurableSet_ball fun z _ => Real.rpow_nonneg (norm_nonneg _) _
    rwa [hmV] at this
  refine ⟨4 ^ k * 3 ^ M * Ω, by positivity, ?_⟩
  intro chi hchi Kc BK hKc hBK ψ hψ hψ1 hψ0 Sg B hB hSg hSj
  have hae : ∀ᵐ v : Euc d, v ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : Euc d))
  have hBK0 : 0 ≤ BK := (norm_nonneg _).trans (hBK 0 (Nat.zero_le _) 0)
  -- smoothness of the fibre
  have hSgy : ∀ v : Euc d, v ≠ 0 → ContDiff ℝ (k : WithTop ℕ∞) (fun y => Sg v y) := by
    intro v hv
    have hg : ContDiff ℝ (k : WithTop ℕ∞) (fun y : Euc d => (v, y)) := contDiff_const.prodMk contDiff_id
    have hmaps : Set.MapsTo (fun y : Euc d => (v, y)) Set.univ {q : Euc d × Euc d | q.1 ≠ 0} :=
      fun y _ => by simpa using hv
    have := hSg.comp hg.contDiffOn hmaps
    exact contDiffOn_univ.1 this
  have hGc : ∀ v : Euc d, v ≠ 0 → ContDiff ℝ (k : WithTop ℕ∞) (r26t8a_f5_G Kc ψ Sg v) := by
    intro v hv
    have h1 : ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => Kc (p.1 - p.2 - v)) :=
      hKc.comp ((contDiff_fst.sub contDiff_snd).sub contDiff_const)
    have h2 : ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => ψ v * Sg v p.2) :=
      contDiff_const.mul ((hSgy v hv).comp contDiff_snd)
    exact h1.mul h2
  have hchic : ContDiff ℝ (k : WithTop ℕ∞) chi := hchi.1.of_le (by exact_mod_cast le_top)
  -- the globally smooth truncations
  set Gm : ℕ → (Euc d × Euc d) × (Euc d × Euc d) → ℝ := fun m x =>
    r26t8a_f5_G Kc ψ Sg x.2.1 x.1 * (1 - chi (((m : ℝ) + 1) • x.2.1)) with hGm
  have hGmc : ∀ m : ℕ, ContDiff ℝ (k : WithTop ℕ∞) (Gm m) := by
    intro m
    have hw : ContDiff ℝ (k : WithTop ℕ∞) (fun x : (Euc d × Euc d) × (Euc d × Euc d) => x.2.1) :=
      contDiff_fst.comp contDiff_snd
    have hθ : ContDiff ℝ (k : WithTop ℕ∞) (fun x : (Euc d × Euc d) × (Euc d × Euc d) =>
        1 - chi (((m : ℝ) + 1) • x.2.1)) :=
      contDiff_const.sub (hchic.comp (hw.const_smul ((m : ℝ) + 1)))
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hs : ‖x.2.1‖ < 1 / ((m : ℝ) + 1)
    · have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hev : Gm m =ᶠ[𝓝 x] fun _ => 0 := by
        have hopen : IsOpen {y : (Euc d × Euc d) × (Euc d × Euc d) | ‖y.2.1‖ < 1 / ((m : ℝ) + 1)} :=
          isOpen_lt (continuous_norm.comp (continuous_fst.comp continuous_snd)) continuous_const
        filter_upwards [hopen.mem_nhds hs] with y hy
        have hy' : ‖y.2.1‖ < 1 / ((m : ℝ) + 1) := hy
        have h1' : ‖((m : ℝ) + 1) • y.2.1‖ ≤ 1 := by
          rw [norm_smul, Real.norm_of_nonneg hm.le]
          rw [lt_div_iff₀ hm] at hy'
          nlinarith
        simp only [hGm, hchi.2.2.2.1 _ h1']
        ring
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · push Not at hs
      have hne : x.2.1 ≠ 0 := by
        intro h; rw [h, norm_zero] at hs
        have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        linarith
      have hK1 : ContDiff ℝ (k : WithTop ℕ∞)
          (fun x : (Euc d × Euc d) × (Euc d × Euc d) => Kc (x.1.1 - x.1.2 - x.2.1)) :=
        hKc.comp (((contDiff_fst.comp contDiff_fst).sub (contDiff_snd.comp contDiff_fst)).sub hw)
      have hopen : IsOpen {q : Euc d × Euc d | q.1 ≠ 0} := isOpen_ne_fun continuous_fst continuous_const
      have hmem : (x.2.1, x.1.2) ∈ {q : Euc d × Euc d | q.1 ≠ 0} := hne
      have hlin : ContDiff ℝ (k : WithTop ℕ∞) (fun x : (Euc d × Euc d) × (Euc d × Euc d) => (x.2.1, x.1.2)) :=
        hw.prodMk (contDiff_snd.comp contDiff_fst)
      have h4 : ContDiffAt ℝ (k : WithTop ℕ∞)
          (fun x : (Euc d × Euc d) × (Euc d × Euc d) => Sg x.2.1 x.1.2) x :=
        ContDiffAt.comp (g := Function.uncurry Sg) (f := fun x : (Euc d × Euc d) × (Euc d × Euc d) => (x.2.1, x.1.2)) x
          (hSg.contDiffAt (hopen.mem_nhds hmem)) hlin.contDiffAt
      have hψc : ContDiff ℝ (k : WithTop ℕ∞) (fun x : (Euc d × Euc d) × (Euc d × Euc d) => ψ x.2.1) :=
        hψ.comp hw
      have h5 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun x : (Euc d × Euc d) × (Euc d × Euc d) =>
          Kc (x.1.1 - x.1.2 - x.2.1) * (ψ x.2.1 * Sg x.2.1 x.1.2) * (1 - chi (((m : ℝ) + 1) • x.2.1))) x :=
        (hK1.contDiffAt.mul (hψc.contDiffAt.mul h4)).mul hθ.contDiffAt
      exact h5
  have hmeas : ∀ i ≤ k, ∀ p : Euc d × Euc d,
      AEStronglyMeasurable (fun v : Euc d => iteratedFDeriv ℝ i (r26t8a_f5_G Kc ψ Sg v) p) volume := by
    intro i hi p
    have hcont : ∀ m : ℕ, Continuous (fun v : Euc d =>
        iteratedFDeriv ℝ i (fun Y : Euc d × Euc d => Gm m (Y, (v, 0))) p) := by
      intro m
      have h := r26t8a_partialY_continuous i (E := Euc d × Euc d) (V := ℝ) (Gm m)
        ((hGmc m).of_le (by exact_mod_cast hi))
      exact h.comp (f := fun v : Euc d => (p, ((v, 0) : Euc d × Euc d))) (by fun_prop)
    refine aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
      (f := fun (m : ℕ) (v : Euc d) => iteratedFDeriv ℝ i (fun Y : Euc d × Euc d => Gm m (Y, (v, 0))) p)
      (fun m => (hcont m).aestronglyMeasurable) ?_
    filter_upwards [hae] with v hv
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨m0, hm0⟩ := exists_nat_gt (2 / ‖v‖)
    filter_upwards [eventually_ge_atTop m0] with m hm
    have h1 : 2 ≤ ((m : ℝ) + 1) * ‖v‖ := by
      have h2 : (m0 : ℝ) ≤ m := by exact_mod_cast hm
      rw [div_lt_iff₀ hvpos] at hm0
      nlinarith
    have h : ‖((m : ℝ) + 1) • v‖ ≥ 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]; exact h1
    have hfun : (fun Y : Euc d × Euc d => Gm m (Y, (v, 0))) = r26t8a_f5_G Kc ψ Sg v := by
      funext Y
      simp only [hGm, hchi.2.2.2.2 _ h, sub_zero, mul_one]
    rw [hfun]
  have hmain : ∀ p0 : Euc d × Euc d, ContDiffAt ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => ∫ v, r26t8a_f5_G Kc ψ Sg v p) p0 ∧
      ∀ i ≤ k, ‖iteratedFDeriv ℝ i (fun p : Euc d × Euc d => ∫ v, r26t8a_f5_G Kc ψ Sg v p) p0‖ ≤
        4 ^ k * 3 ^ M * Ω * BK * B * jbracket p0.2 ^ M := by
    intro p0
    set U : Set (Euc d × Euc d) := ball p0 1 with hU
    have hUo : IsOpen U := isOpen_ball
    have hp0U : p0 ∈ U := mem_ball_self one_pos
    have hjb : ∀ p ∈ U, jbracket p.2 ≤ 3 * jbracket p0.2 := by
      intro p hp
      have hp1 : ‖p - p0‖ < 1 := by rw [hU, mem_ball, dist_eq_norm] at hp; exact hp
      have h2 : ‖p.2 - p0.2‖ ≤ ‖p - p0‖ := norm_snd_le (p - p0)
      have := r26t8a_jb_shift' p0.2 (p.2 - p0.2)
      rw [add_sub_cancel] at this
      have hj0 := s83_jb_pos p0.2
      nlinarith
    set c : ℝ := 4 ^ k * BK * B * (3 * jbracket p0.2) ^ M with hc
    have hc0 : 0 ≤ c := by
      have : 0 ≤ (3 * jbracket p0.2) ^ M := Real.rpow_nonneg (by have := s83_jb_pos p0.2; positivity) _
      positivity
    set Φ : Euc d → ℝ := (ball (0 : Euc d) 1).indicator (fun v => c * ‖v‖ ^ (-s)) with hΦd
    have hmI' : IntegrableOn (fun v : Euc d => c * ‖v‖ ^ (-s)) (ball (0 : Euc d) 1) := hmI.const_mul c
    have hΦ : Integrable Φ := (integrable_indicator_iff measurableSet_ball).2 hmI'
    have hΦ0 : ∀ v, 0 ≤ Φ v := fun v => Set.indicator_nonneg (fun w _ => by positivity) v
    have hG : ∀ᵐ v : Euc d, ∀ p ∈ U, ContDiffAt ℝ (k : WithTop ℕ∞) (r26t8a_f5_G Kc ψ Sg v) p := by
      filter_upwards [hae] with v hv p _
      exact (hGc v hv).contDiffAt
    have hbd : ∀ i ≤ k, ∀ᵐ v : Euc d, ∀ p ∈ U, ‖iteratedFDeriv ℝ i (r26t8a_f5_G Kc ψ Sg v) p‖ ≤ Φ v := by
      intro i hi
      filter_upwards [hae] with v hv p hp
      by_cases hv2 : ‖v‖ ≤ 1 / 2
      · have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
        have hgc : ContDiff ℝ (i : WithTop ℕ∞) (fun y => ψ v * Sg v y) :=
          (contDiff_const.mul ((hSgy v hv).of_le (by exact_mod_cast hi)))
        have hKi : ContDiff ℝ (i : WithTop ℕ∞) Kc := hKc.of_le (by exact_mod_cast hi)
        have hBg : ∀ m ≤ i, ‖iteratedFDeriv ℝ m (fun y => ψ v * Sg v y) p.2‖ ≤
            B * (3 * jbracket p0.2) ^ M * ‖v‖ ^ (-s) := by
          intro m hm
          have hSm : ContDiff ℝ (m : WithTop ℕ∞) (fun y => Sg v y) :=
            (hSgy v hv).of_le (by exact_mod_cast (hm.trans hi))
          have e : (fun y => ψ v * Sg v y) = fun y => ψ v • Sg v y := rfl
          rw [e, iteratedFDeriv_const_smul_apply' hSm.contDiffAt, norm_smul, Real.norm_eq_abs]
          have h1 := hSj v p.2 hvpos hv2 m (hm.trans hi)
          have h2 : jbracket p.2 ^ M ≤ (3 * jbracket p0.2) ^ M :=
            Real.rpow_le_rpow (s83_jb_pos _).le (hjb p hp) hM
          calc |ψ v| * ‖iteratedFDeriv ℝ m (fun y => Sg v y) p.2‖ ≤ 1 * (B * jbracket p.2 ^ M * ‖v‖ ^ (-s)) :=
                mul_le_mul (hψ1 v) h1 (norm_nonneg _) zero_le_one
            _ ≤ B * (3 * jbracket p0.2) ^ M * ‖v‖ ^ (-s) := by
                rw [one_mul]
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hB) (Real.rpow_nonneg (norm_nonneg _) _)
        have hjet := r26t8a_f4_jet_G hKi hgc (fun j hj u => hBK j (hj.trans hi) u) v p hBg
        have hvb : v ∈ ball (0 : Euc d) 1 := by simp only [mem_ball_zero_iff]; linarith
        rw [hΦd, Set.indicator_of_mem hvb]
        refine hjet.trans ?_
        have h4 : (4 : ℝ) ^ i ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hi
        have hpos : 0 ≤ BK * (B * (3 * jbracket p0.2) ^ M * ‖v‖ ^ (-s)) := by
          have : 0 ≤ (3 * jbracket p0.2) ^ M := Real.rpow_nonneg (by have := s83_jb_pos p0.2; positivity) _
          positivity
        calc 4 ^ i * (BK * (B * (3 * jbracket p0.2) ^ M * ‖v‖ ^ (-s))) ≤ 4 ^ k * (BK * (B * (3 * jbracket p0.2) ^ M * ‖v‖ ^ (-s))) :=
              mul_le_mul_of_nonneg_right h4 hpos
          _ = c * ‖v‖ ^ (-s) := by rw [hc]; ring
      · have : r26t8a_f5_G Kc ψ Sg v = fun _ => 0 := by
          funext q
          show Kc (q.1 - q.2 - v) * (ψ v * Sg v q.2) = 0
          rw [hψ0 v (not_le.1 hv2)]; simp
        rw [this]
        have h0 : iteratedFDeriv ℝ i (fun _ : Euc d × Euc d => (0 : ℝ)) p = 0 := by
          simp
        rw [h0, norm_zero]
        exact hΦ0 v
    have hmeas' : ∀ i ≤ k, ∀ p ∈ U, AEStronglyMeasurable
        (fun v : Euc d => iteratedFDeriv ℝ i (r26t8a_f5_G Kc ψ Sg v) p) volume := fun i hi p _ => hmeas i hi p
    have hform := r26t8a_iter_integral (μ := volume) hUo (r26t8a_f5_G Kc ψ Sg) k hG hΦ hbd hmeas'
    have hcd := r26t8a_contDiffOn_integral (μ := volume) hUo (r26t8a_f5_G Kc ψ Sg) k hG hΦ hbd hmeas'
    refine ⟨(hcd.contDiffAt (hUo.mem_nhds hp0U)), fun i hi => ?_⟩
    rw [hform i hi p0 hp0U]
    refine (norm_integral_le_of_norm_le hΦ (by filter_upwards [hbd i hi] with v hv using hv p0 hp0U)).trans ?_
    rw [hΦd, integral_indicator measurableSet_ball, integral_const_mul, hmV, hc]
    have h3 : (3 * jbracket p0.2) ^ M = 3 ^ M * jbracket p0.2 ^ M :=
      Real.mul_rpow (by norm_num) (s83_jb_pos _).le
    rw [h3]
    refine le_of_eq ?_
    ring
  exact ⟨contDiff_iff_contDiffAt.2 fun p0 => (hmain p0).1, fun i hi p => by
    have := (hmain p).2 i hi
    simpa [mul_assoc, mul_comm, mul_left_comm] using this⟩

end HRS.MS.R26T8A
