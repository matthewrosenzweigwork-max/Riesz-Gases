import HRS.Sections.AdjKAAux10

/-!
# ADJKA part 11: the `E_j` second/`p`-th moment of stochastic convolutions (Fatou over finite-rank truncations)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjka_abs_le_jp (k : Lattice d) (i : Fin d) : (|(k i : ℝ)|) ≤ Lattice.jp k := by
  have h1 : |(k i : ℝ)| ≤ Lattice.enorm k := by
    unfold Lattice.enorm Lattice.toEuc
    have := PiLp.norm_apply_le (WithLp.toLp 2 fun i : Fin d => (k i : ℝ)) i
    simpa using this
  have h2 : Lattice.enorm k ≤ Lattice.jp k := by
    unfold Lattice.jp
    refine Real.le_sqrt_of_sq_le ?_
    have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_nonneg (sub_nonneg.2 hpi) (sq_nonneg (Lattice.enorm k))]
  exact h1.trans h2

/-- Large `⟨k⟩` outside a finite box. -/
theorem adjka_box (j m : ℝ) (hjm : j < m) :
    ∀ ε : ℝ, 0 < ε → ∃ S : Finset (NonzeroLattice d), ∀ k : NonzeroLattice d, k ∉ S →
      Lattice.jp k.1 ^ (-(2 * (m - j))) ≤ ε := by
  intro ε hε
  have he : 0 < 2 * (m - j) := by linarith
  have ht := (tendsto_rpow_neg_atTop he).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN, hN1⟩ := ((ht.eventually (ge_mem_nhds hε)).and (Filter.eventually_ge_atTop 1)).exists
  classical
  refine ⟨(Fintype.piFinset fun _ : Fin d => Finset.Icc (-(N : ℤ)) N).subtype (fun k : Lattice d => k ≠ 0), ?_⟩
  intro k hk
  have hbox : ¬ ∀ i, k.1 i ∈ Finset.Icc (-(N : ℤ)) N := by
    intro h
    exact hk (by simp [Finset.mem_subtype, Fintype.mem_piFinset, h])
  push_neg at hbox
  obtain ⟨i, hi⟩ := hbox
  have hgt : (N : ℝ) < |(k.1 i : ℝ)| := by
    by_contra hle
    push_neg at hle
    apply hi
    rw [Finset.mem_Icc]
    have := abs_le.1 hle
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  have hjp : (N : ℝ) < Lattice.jp k.1 := hgt.trans_le (adjka_abs_le_jp k.1 i)
  have hjp1 : 1 ≤ Lattice.jp k.1 := Torus.jp_ge_one k.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  refine le_trans ?_ hN
  simp only [Function.comp]
  exact Real.rpow_le_rpow_of_nonpos hNpos hjp.le (by linarith)


theorem adjka_energy_embed' {j m : ℝ} (hjm : j ≤ m) (z : NegSobolev d j) :
    adjkEnergy j m (NegSobolev.embed m z) = ‖z‖ₑ ^ 2 := by
  rw [adjka_energy_embed hjm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]

theorem adjka_lsc_liminf {X : Type*} [TopologicalSpace X] {f : X → ℝ≥0∞} (hf : LowerSemicontinuous f)
    {u : ℕ → X} {x : X} (h : Tendsto u atTop (𝓝 x)) :
    f x ≤ liminf (fun n => f (u n)) atTop := by
  have h1 : f x ≤ liminf f (𝓝 x) := lowerSemicontinuousAt_iff_le_liminf.1 (hf x)
  refine h1.trans ?_
  have : liminf (fun n => f (u n)) atTop = liminf f (map u atTop) := liminf_comp f u atTop
  rw [this]
  exact liminf_le_liminf_of_le h

theorem adjka_energy_moment (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (j : ℕ)
    (hj : (d : ℝ) + 2 ≤ j) (m : ℝ) (hjm : (j : ℝ) + 2 ≤ m) (T : ℝ) (hT : 0 < T) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (μ : ℝ → Ω → Measure (Torus d)) (_ : ∀ r ω, IsProbabilityMeasure (μ r ω))
        (M : ℝ → Ω → NegSobolev d m),
        IsHilbertMartingaleWithCovariation P ℱ T M (fun r ω => covForm m β⁻¹ (μ r ω)) →
        ∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
          IsDualEvolution htr.dyn ρ m Vev →
          ∀ Z : ℝ → Ω → NegSobolev d m,
            (∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M 0 t (Z t)) →
            (∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Z t) P) →
            ∫⁻ ω, (⨆ q ∈ ratIcc 0 T, adjkEnergy (j : ℝ) m (Z q ω)) ^ (p / 2) ∂P ≤ ENNReal.ofReal C := by
  obtain ⟨CB, C2, hCB, hC2, hdec⟩ := adjka_decomp hd htr j hj m hjm T hT p hp
  have hq : 0 ≤ β⁻¹ := (inv_pos.2 htr.hβ).le
  have hS0 : 0 ≤ Q14.q14S d ((j : ℝ) - 1) := Q14.q14S_nonneg d _
  set Bj : ℝ := (d : ℝ) * (2 * β⁻¹ * (2 * Q14.q14S d ((j : ℝ) - 1))) with hBj
  have hBj0 : 0 ≤ Bj := by positivity
  set Kc : ℝ := C2 * (T * ((d : ℝ) * (2 * β⁻¹ * (2 * Q14.q14S d ((j : ℝ) - 1))))) with hKc
  refine ⟨CB * (T * Bj) ^ (p / 2), by positivity, ?_⟩
  intro Ω mΩ P _ ℱ μ hμ M hM Vev hVev Z hZ hZm
  have hjm' : (j : ℝ) ≤ m := by linarith
  have hlt : (j : ℝ) < m := by linarith
  choose S hS using fun n : ℕ => adjka_box (d := d) (j : ℝ) m hlt ((1 / 2 : ℝ) ^ n) (by positivity)
  have hdec' := fun n : ℕ => hdec Ω P ℱ μ hμ M hM Vev hVev Z hZ hZm (S n) ((1 / 2 : ℝ) ^ n)
    (by positivity) (hS n)
  choose ZS Zc hZSm hZcm hid hZSb hZcb using hdec'
  have hratsub : ∀ q ∈ ratIcc 0 T, q ∈ Set.Icc (0 : ℝ) T := fun q hq => hq.1
  have hid' : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ q ∈ ratIcc 0 T,
      Z q ω = NegSobolev.embed m (ZS n q ω) + Zc n q ω := by
    rw [ae_all_iff]; intro n
    rw [ae_ball_iff (ratIcc_countable 0 T)]
    intro q hq; exact hid n q hq.1
  -- the tails
  set aN : ℕ → Ω → ℝ≥0∞ := fun n ω => (⨆ q ∈ ratIcc 0 T, ‖Zc n q ω‖ₑ) ^ (2 : ℝ) with haN
  have haN_meas : ∀ n, AEMeasurable (aN n) P := fun n =>
    (AEMeasurable.biSup (ratIcc 0 T) (ratIcc_countable 0 T)
      (fun q hq => (hZcm n q hq.1).enorm)).pow_const _
  have haN_le : ∀ n ω, aN n ω ≤ (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Zc n t ω‖ₑ) ^ (2 : ℝ) := fun n ω =>
    ENNReal.rpow_le_rpow (iSup₂_le fun q hq => le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => ‖Zc n t ω‖ₑ) q hq.1)
      (by norm_num)
  have haN_int : ∀ n, ∫⁻ ω, aN n ω ∂P ≤ ENNReal.ofReal (Kc * (1 / 2 : ℝ) ^ n) := fun n => by
    refine (lintegral_mono (haN_le n)).trans ((hZcb n).trans (le_of_eq ?_))
    congr 1
    simp only [hKc]; ring
  have hgeo : Summable fun n : ℕ => Kc * (1 / 2 : ℝ) ^ n := summable_geometric_two.mul_left Kc
  have hsum : ∫⁻ ω, ∑' n, aN n ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum haN_meas]
    refine ne_top_of_le_ne_top (b := ∑' n : ℕ, ENNReal.ofReal (Kc * (1 / 2 : ℝ) ^ n)) ?_ (ENNReal.tsum_le_tsum haN_int)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hgeo]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ ω ∂P, ∑' n, aN n ω < ⊤ :=
    ae_lt_top' (AEMeasurable.ennreal_tsum haN_meas) hsum
  set H : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨆ q ∈ ratIcc 0 T, ‖ZS n q ω‖ₑ ^ 2 with hH
  have hH_meas : ∀ n, AEMeasurable (fun ω => H n ω ^ (p / 2)) P := fun n =>
    (AEMeasurable.biSup (ratIcc 0 T) (ratIcc_countable 0 T)
      (fun q hq => ((hZSm n q hq.1).enorm).pow_const 2)).pow_const _
  have hH_le : ∀ n ω, H n ω ^ (p / 2) ≤ (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖ZS n t ω‖ₑ) ^ p := fun n ω => by
    have h1 : H n ω ≤ (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖ZS n t ω‖ₑ) ^ 2 :=
      iSup₂_le fun q hq => pow_le_pow_left' (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => ‖ZS n t ω‖ₑ) q hq.1) 2
    refine (ENNReal.rpow_le_rpow h1 (by linarith)).trans (le_of_eq ?_)
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1; push_cast; ring
  have hH_int : ∀ n, ∫⁻ ω, H n ω ^ (p / 2) ∂P ≤ ENNReal.ofReal (CB * (T * Bj) ^ (p / 2)) := fun n =>
    (lintegral_mono (hH_le n)).trans (hZSb n)
  -- pointwise comparison
  set G : Ω → ℝ≥0∞ := fun ω => ⨆ q ∈ ratIcc 0 T, adjkEnergy (j : ℝ) m (Z q ω) with hG
  have hpt : ∀ᵐ ω ∂P, G ω ^ (p / 2) ≤ liminf (fun n => H n ω ^ (p / 2)) atTop := by
    filter_upwards [hid', hae] with ω hω1 hω2
    have h0 : Tendsto (fun n => aN n ω) atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω2.ne
    have hGl : G ω ≤ liminf (fun n => H n ω) atTop := by
      refine iSup₂_le fun q hq => ?_
      have h1 : ∀ n, ‖Zc n q ω‖ₑ ^ (2 : ℝ) ≤ aN n ω := fun n =>
        ENNReal.rpow_le_rpow (le_iSup₂ (f := fun q (_ : q ∈ ratIcc 0 T) => ‖Zc n q ω‖ₑ) q hq) (by norm_num)
      have h2 : Tendsto (fun n => ‖Zc n q ω‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n => bot_le) h1
      have h3 : Tendsto (fun n => ‖Zc n q ω‖ₑ) atTop (𝓝 0) := by
        have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp h2
        rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
        refine this.congr fun n => ?_
        show (‖Zc n q ω‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = ‖Zc n q ω‖ₑ
        rw [← ENNReal.rpow_mul]; norm_num
      have h4 : Tendsto (fun n => Zc n q ω) atTop (𝓝 0) := by
        refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h3
        refine this.congr fun n => ?_
        simp [Function.comp, toReal_enorm]
      have h5 : Tendsto (fun n => NegSobolev.embed m (ZS n q ω)) atTop (𝓝 (Z q ω)) := by
        have := (tendsto_const_nhds (x := Z q ω)).sub h4
        rw [sub_zero] at this
        refine this.congr fun n => ?_
        rw [hω1 n q hq]; abel
      have h6 := adjka_lsc_liminf (adjkEnergy_lsc (d := d) (j : ℝ) m) h5
      refine h6.trans (liminf_le_liminf (Eventually.of_forall fun n => ?_))
      rw [adjka_energy_embed' hjm']
      exact le_iSup₂ (f := fun q (_ : q ∈ ratIcc 0 T) => ‖ZS n q ω‖ₑ ^ 2) q hq
    have hmono : Monotone fun x : ℝ≥0∞ => x ^ (p / 2) := ENNReal.monotone_rpow_of_nonneg (by linarith)
    have hcont : ContinuousAt (fun x : ℝ≥0∞ => x ^ (p / 2)) (liminf (fun n => H n ω) atTop) :=
      (ENNReal.continuous_rpow_const).continuousAt
    have := hmono.map_liminf_of_continuousAt (fun n => H n ω) hcont (F := atTop)
    calc G ω ^ (p / 2) ≤ (liminf (fun n => H n ω) atTop) ^ (p / 2) := hmono hGl
      _ = liminf (fun n => H n ω ^ (p / 2)) atTop := this
  calc ∫⁻ ω, G ω ^ (p / 2) ∂P ≤ ∫⁻ ω, liminf (fun n => H n ω ^ (p / 2)) atTop ∂P := lintegral_mono_ae hpt
    _ ≤ liminf (fun n => ∫⁻ ω, H n ω ^ (p / 2) ∂P) atTop := lintegral_liminf_le' hH_meas
    _ ≤ ENNReal.ofReal (CB * (T * Bj) ^ (p / 2)) :=
        liminf_le_of_frequently_le' (Frequently.of_forall hH_int)

end HRS.AdjK
