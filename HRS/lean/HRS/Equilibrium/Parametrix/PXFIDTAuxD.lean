import HRS.Equilibrium.Parametrix.PX7AuxE

/-!
# Packet PX-FID-T, file D: the pair inverse with `C^n` output

`px7_spec` gives only a `C²` pair inverse, from the base level `m = ⌊d/2⌋ + 5`.  The tensor argument
of PX7 is parametrised by the level `m` of the one-variable operator (`OV`), and the output
regularity enters only through `px7_ev_C2`, `px7_pair_C2`, `px7_pair_jets`, `px7_inv_C2`.  Here:

* `pxfidt_oneVar`: `px7_oneVar` at every level `m ≥ px7_m d` (the decay `px7_decay` holds at every
  natural `j > d/2 + 4`, not only at even levels);
* `pxfidt_ev_Cn`, `pxfidt_pair_Cn`, `pxfidt_pair_jets`, `pxfidt_inv_Cn`: the same with `C^n`
  output, `d + 2n < 2m`, input `C^{m+m}`.
* `pxfidt_inv_Cn_spec`: the final form for `D = mfData`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.PX7

open HRS.PDE.MFAdjoint

variable {d : ℕ}

section OneVar

theorem pxfidt_oneVar (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρC : Torus.IsSmooth ρ)
    (hpos : ∀ x, 0 < ρ x) (m : ℕ) (hmb : px7_m d ≤ m) :
    OV (mfData d s hs0 hsd V β hβ) ρ m (px7_T (mfData d s hs0 hsd V β hβ) ρ m)
      (px7_Ah (mfData d s hs0 hsd V β hβ) ρ) := by
  have h3 := ClassicalPart.three_le_mStar d
  have hm : mStar d + 2 ≤ m := by have := px7_m_eq d; omega
  set N := m + 2 + mStar d + 3 with hN
  obtain ⟨c₀, Λ₀, H⟩ := MFPair.frozenHyp_of_smooth s hs0 hsd β hβ V hV ρ hρβ hρC hpos N
  have Hm : FrozenHyp d s (m + 3) β⁻¹ β⁻¹ c₀ Λ₀ β V ρ := H.mono (by omega)
  have Hm1 : FrozenHyp d s (m + 1 + 3) β⁻¹ β⁻¹ c₀ Λ₀ β V ρ := H.mono (by omega)
  have Hm2 : FrozenHyp d s (m + 2 + 3) β⁻¹ β⁻¹ c₀ Λ₀ β V ρ := H.mono (by omega)
  have hj0 : (d : ℝ) / 2 + 4 < m := by
    have h1 : (d : ℝ) / 2 < (⌊(d : ℝ) / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : ((⌊(d : ℝ) / 2⌋₊ + 5 : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (show ⌊(d : ℝ) / 2⌋₊ + 5 ≤ m from hmb)
    push_cast at h2
    linarith
  have hj2 : (d : ℝ) / 2 + 4 < ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨M0, c0, hM0, hc0, hdec0⟩ := px7_decay hd s m m hm le_rfl hj0 β⁻¹ β⁻¹ c₀ Λ₀
  obtain ⟨M2, c2, hM2, hc2, hdec2⟩ := px7_decay hd s m (m + 2) hm (by omega) hj2 β⁻¹ β⁻¹ c₀ Λ₀
  have hH0 : FrozenHyp d s (m + mStar d + 3) β⁻¹ β⁻¹ c₀ Λ₀ β V ρ := H.mono (by omega)
  have hH2 : FrozenHyp d s (m + 2 + mStar d + 3) β⁻¹ β⁻¹ c₀ Λ₀ β V ρ := H.mono (by omega)
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  refine ⟨hj0, H.thermal.1, H.cont (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro τ hτ x y hx hy; exact px7_T_add hd m hm Hm hx hy hτ
  · intro τ hτ x hx a; exact px7_T_smul hd m hm Hm hx a hτ
  · exact ⟨M0, c0, hM0, hc0, fun τ hτ x hx => hdec0 β V ρ hH0 x hx τ hτ⟩
  · exact ⟨M2, c2, hM2, hc2, fun τ hτ x hx => hdec2 β V ρ hH2 x hx τ hτ⟩
  · intro τ hτ x hx hre; exact (px7_T_real hd m hm Hm hx hre hτ).2
  · intro τ hτ x hx; exact px7_T_mean hd m hm Hm hx hτ
  · intro τ hτ z; exact px7_T_const hd m hm Hm z hτ
  · intro x hx; exact px7_T_zero hd m hm Hm hx
  · intro σ τ hσ hτ x hx; exact px7_T_semigroup hd m hm Hm hx hσ hτ
  · intro x hx τ₀ hτ₀
    refine px7_T_cont hd m hm Hm1 (M0 * 1) ?_ hx hτ₀
    intro τ hτ y hy
    have := (hdec0 β V ρ hH0 y hy τ hτ).2
    have hE : Real.exp (-c0 * τ) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    calc _ ≤ M0 * Real.exp (-c0 * τ) * hsNorm (m : ℝ) y := this
      _ ≤ M0 * 1 * hsNorm (m : ℝ) y := by
        have := hsNorm_nonneg' (m : ℝ) y
        gcongr
  · intro ψ hψc hψ τ hτ; exact px7_S_eq hd m hm Hm hψc hψ hτ
  · obtain ⟨K, hK, h⟩ := px7_Ah_bound hd m hm Hm
    exact ⟨K, hK, h⟩
  · intro x y hx hy; exact px7_Ah_add hd m hm Hm2 hx hy
  · intro a x; exact px7_Ah_smul m a x _
  · intro x hx hre; exact (px7_Ah_real hd m hm Hm hre).2.2
  · intro x hx; exact px7_T_deriv hd m hm Hm2 hx
  · obtain ⟨Kt, hKt, h⟩ := px7_T_quot_bound hd m hm Hm2
    exact ⟨Kt, hKt, h⟩
  · intro x hx τ hτ
    refine px7_comm hd m hm Hm2 M0 ?_ ?_ hx hτ
    · intro τ' hτ' y hy
      have := (hdec0 β V ρ hH0 y hy τ' hτ').2
      have hE : Real.exp (-c0 * τ') ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      calc _ ≤ M0 * Real.exp (-c0 * τ') * hsNorm (m : ℝ) y := this
        _ ≤ M0 * 1 * hsNorm (m : ℝ) y := by
          have := hsNorm_nonneg' (m : ℝ) y
          gcongr
        _ = _ := by ring
    · intro τ' hτ' y hy; exact (hdec2 β V ρ hH2 y hy τ' hτ').1
  · intro x hr hx; exact px7_bridge hd m hm Hm2 hr hx


end OneVar

section Cn

theorem pxfidt_ev_Cn (n : ℕ) {m : ℕ} (hm : (d : ℝ) + 2 * n < 2 * m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : Arr d, Mem2 (m : ℝ) (m : ℝ) u →
      IsCk2 n (ev u) ∧ cbNorm2 n (ev u) ≤ A * nrm2 (m : ℝ) (m : ℝ) u := by
  have hcs : ∀ k : ℕ, k ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Arr d, Mem2 (m : ℝ) (m : ℝ) u →
      Summable (fun p : Lattice d × Lattice d => Lattice.jp p.1 ^ k * Lattice.jp p.2 ^ k * ‖u p.1 p.2‖) ∧
      ∑' p : Lattice d × Lattice d, Lattice.jp p.1 ^ k * Lattice.jp p.2 ^ k * ‖u p.1 p.2‖ ≤
        C * nrm2 (m : ℝ) (m : ℝ) u := by
    intro k hk
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    exact px7_cs (m : ℝ) (m : ℝ) k k (by linarith) (by linarith)
  choose! C hC0 hC using hcs
  refine ⟨∑ i ∈ Finset.range (n + 1), 2 * 2 ^ i * C i,
    Finset.sum_nonneg fun i hi => mul_nonneg (by positivity)
      (hC0 i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))), fun u hu => ?_⟩
  have hs0 : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖ := by
    simpa using (hC 0 (Nat.zero_le _) u hu).1
  set v : ℕ → Lattice d × Lattice d → ℝ := fun k q =>
    2 * 2 ^ k * (Lattice.jp q.1 ^ k * Lattice.jp q.2 ^ k * ‖u q.1 q.2‖) with hv
  have hvs : ∀ k : ℕ, k ≤ n → Summable (v k) := fun k hk =>
    ((hC k hk u hu).1).mul_left _
  have hcomb : ∀ q : Lattice d × Lattice d, ContDiff ℝ ⊤ (tq u q) := fun q =>
    ((contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)).comp
      (lq q).contDiff
  have hbd : ∀ (k : ℕ) (q : Lattice d × Lattice d) (p : Euc d × Euc d), k ≤ n →
      ‖iteratedFDeriv ℝ k (tq u q) p‖ ≤ v k q := by
    intro k q p hk
    have hb := px7_norm_iter_comp (fun t => (u q.1 q.2).re * Real.cos t + (-(u q.1 q.2).im) * Real.sin t)
      ((contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin))
      (|(u q.1 q.2).re| + |-(u q.1 q.2).im|) (fun i t => norm_iteratedFDeriv_trig_comb _ _ i t)
      (lq q) k p
    refine hb.trans ?_
    have h1' : |(u q.1 q.2).re| + |-(u q.1 q.2).im| ≤ 2 * ‖u q.1 q.2‖ := by
      rw [abs_neg]
      have := Complex.abs_re_le_norm (u q.1 q.2)
      have := Complex.abs_im_le_norm (u q.1 q.2)
      linarith
    have h2' : ‖lq q‖ ^ k ≤ 2 ^ k * (Lattice.jp q.1 ^ k * Lattice.jp q.2 ^ k) := by
      have j1 := Torus.jp_ge_one q.1
      have j2 := Torus.jp_ge_one q.2
      have : Lattice.jp q.1 + Lattice.jp q.2 ≤ 2 * (Lattice.jp q.1 * Lattice.jp q.2) := by nlinarith
      calc ‖lq q‖ ^ k ≤ (Lattice.jp q.1 + Lattice.jp q.2) ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) (px7_norm_lq_le q) k
        _ ≤ (2 * (Lattice.jp q.1 * Lattice.jp q.2)) ^ k :=
            pow_le_pow_left₀ (by positivity) this k
        _ = _ := by rw [mul_pow, mul_pow]
    simp only [hv]
    calc (|(u q.1 q.2).re| + |-(u q.1 q.2).im|) * ‖lq q‖ ^ k
        ≤ (2 * ‖u q.1 q.2‖) * (2 ^ k * (Lattice.jp q.1 ^ k * Lattice.jp q.2 ^ k)) :=
          mul_le_mul h1' h2' (by positivity) (by positivity)
      _ = _ := by ring
  have hlift := px7_lift2_ev hs0
  refine ⟨?_, ?_⟩
  · unfold IsCk2
    rw [hlift]
    exact contDiff_tsum (N := (n : ℕ∞)) (fun q => (hcomb q).of_le le_top)
      (fun k hk => hvs k (by exact_mod_cast hk))
      (fun k q p hk => hbd k q p (by exact_mod_cast hk))
  · have hsupi : ∀ i : ℕ, i ≤ n → ∀ p : Euc d × Euc d,
        ‖iteratedFDeriv ℝ i (lift2 (ev u)) p‖ ≤ ∑' q, v i q := by
      intro i hi p
      rw [hlift]
      have hf : ∀ q, ContDiff ℝ (((n : ℕ∞)) : WithTop ℕ∞) (tq u q) := fun q => (hcomb q).of_le le_top
      rw [iteratedFDeriv_tsum_apply (N := (n : ℕ∞)) hf (fun k hk => hvs k (by exact_mod_cast hk))
        (fun k q p hk => hbd k q p (by exact_mod_cast hk)) (by exact_mod_cast hi) p]
      have hns : Summable fun q => ‖iteratedFDeriv ℝ i (tq u q) p‖ :=
        Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hbd i q p hi) (hvs i hi)
      exact (norm_tsum_le_tsum_norm hns).trans
        (Summable.tsum_le_tsum (fun q => hbd i q p hi) hns (hvs i hi))
    have hvi : ∀ i : ℕ, i ≤ n → ∑' q, v i q ≤ 2 * 2 ^ i * C i * nrm2 (m : ℝ) (m : ℝ) u := by
      intro i hi
      simp only [hv]
      rw [tsum_mul_left]
      calc 2 * 2 ^ i * ∑' q : Lattice d × Lattice d, Lattice.jp q.1 ^ i * Lattice.jp q.2 ^ i * ‖u q.1 q.2‖
          ≤ 2 * 2 ^ i * (C i * nrm2 (m : ℝ) (m : ℝ) u) :=
            mul_le_mul_of_nonneg_left (hC i hi u hu).2 (by positivity)
        _ = _ := by ring
    unfold cbNorm2
    calc ∑ i ∈ Finset.range (n + 1), ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ i (lift2 (ev u)) p‖
        ≤ ∑ i ∈ Finset.range (n + 1), 2 * 2 ^ i * C i * nrm2 (m : ℝ) (m : ℝ) u := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          exact ciSup_le fun p => (hsupi i hi' p).trans (hvi i hi')
      _ = (∑ i ∈ Finset.range (n + 1), 2 * 2 ^ i * C i) * nrm2 (m : ℝ) (m : ℝ) u := by
          rw [Finset.sum_mul]

variable {D : DynData d} {ρ : Torus d → ℝ} {m : ℕ} {T : ℝ → Coeff d → Coeff d} {Ah : Coeff d → Coeff d}

theorem pxfidt_pair_Cn (n : ℕ) (hn : (d : ℝ) + 2 * n < 2 * m) (hOV : OV D ρ m T Ah) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ R : Torus d → Torus d → ℝ, IsCk2 (m + m) R → ∀ τ : ℝ, 0 ≤ τ →
      IsCk2 n (pairSemigroup D ρ τ R) ∧
      cbNorm2 n (pairSemigroup D ρ τ R) ≤ (C * cbNorm2 (m + m) R) * Real.exp (-c * τ) := by
  obtain ⟨M, c, hM, hc, hPP⟩ := px7_PP_bound hOV
  obtain ⟨K, hK, hdata⟩ := px7_arr_data hOV
  obtain ⟨A, hA, hev⟩ := pxfidt_ev_Cn (d := d) n (m := m) hn
  refine ⟨A * (M ^ 2 * K), 2 * c, by positivity, by positivity, fun R hR τ hτ => ?_⟩
  obtain ⟨h1, -, h3⟩ := hdata R hR
  obtain ⟨h4, h5⟩ := hPP τ hτ _ h1
  rw [px7_pair_ev hOV hR hτ]
  obtain ⟨h6, h7⟩ := hev _ h4
  refine ⟨h6, h7.trans ?_⟩
  have hE := (Real.exp_pos (-(2 * c) * τ)).le
  calc A * nrm2 (m : ℝ) (m : ℝ) (PP T τ (arr R))
      ≤ A * (M ^ 2 * Real.exp (-(2 * c) * τ) * nrm2 (m : ℝ) (m : ℝ) (arr R)) :=
        mul_le_mul_of_nonneg_left h5 hA
    _ ≤ A * (M ^ 2 * Real.exp (-(2 * c) * τ) * (K * cbNorm2 (m + m) R)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

theorem pxfidt_pair_jets (n : ℕ) (hn : (d : ℝ) + 2 * n < 2 * m) (hOV : OV D ρ m T Ah)
    {R : Torus d → Torus d → ℝ} (hR : IsCk2 (m + m) R)
    (i : ℕ) (hi : i ≤ n) (p : Euc d × Euc d) :
    ContinuousOn (fun τ => iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ τ R)) p) (Set.Ici 0) := by
  intro σ hσ
  have hσ' : 0 ≤ σ := hσ
  obtain ⟨K, hK, hdata⟩ := px7_arr_data hOV
  obtain ⟨h1, -, -⟩ := hdata R hR
  obtain ⟨A, hA, hev⟩ := pxfidt_ev_Cn (d := d) n (m := m) hn
  obtain ⟨M, c, hM, hc, hPP⟩ := px7_PP_bound hOV
  set u := arr R with hu
  have hmemτ : ∀ τ : ℝ, 0 ≤ τ → Mem2 (m : ℝ) (m : ℝ) (PP T τ u) := fun τ hτ => (hPP τ hτ u h1).1
  have hbound : ∀ᶠ τ in 𝓝[Set.Ici 0] σ,
      ‖iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ τ R)) p -
        iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ σ R)) p‖ ≤
      A * nrm2 (m : ℝ) (m : ℝ) (PP T τ u - PP T σ u) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : 0 ≤ τ := hτ
    have ma := hmemτ τ hτ'
    have mb := hmemτ σ hσ'
    have hsa := px7_summable_of_mem2 hOV.hd ma
    have hsb := px7_summable_of_mem2 hOV.hd mb
    obtain ⟨hc1, hn1⟩ := hev _ ma
    obtain ⟨hc2, hn2⟩ := hev _ mb
    have hsub := (ma.sub mb).1
    obtain ⟨hc3, hn3⟩ := hev _ hsub
    rw [px7_pair_ev hOV hR hτ', px7_pair_ev hOV hR hσ']
    have e : lift2 (ev (PP T τ u)) - lift2 (ev (PP T σ u)) = lift2 (ev (PP T τ u - PP T σ u)) := by
      funext q
      simp only [Pi.sub_apply, lift2]
      rw [px7_ev_sub hsa hsb]
    have hca : ContDiffAt ℝ (i : WithTop ℕ∞) (lift2 (ev (PP T τ u))) p :=
      (hc1.of_le (by exact_mod_cast hi)).contDiffAt
    have hcb : ContDiffAt ℝ (i : WithTop ℕ∞) (lift2 (ev (PP T σ u))) p :=
      (hc2.of_le (by exact_mod_cast hi)).contDiffAt
    rw [← iteratedFDeriv_sub_apply hca hcb, e]
    exact (MFPair.norm_iteratedFDeriv_le_cbNorm2 hc3 hi p).trans hn3
  have hlim : Tendsto (fun τ => A * nrm2 (m : ℝ) (m : ℝ) (PP T τ u - PP T σ u)) (𝓝[Set.Ici 0] σ) (𝓝 0) := by
    simpa using (px7_PP_cont hOV hσ' h1).const_mul A
  have : Tendsto (fun τ => iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ τ R)) p) (𝓝[Set.Ici 0] σ)
      (𝓝 (iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ σ R)) p)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Filter.Eventually.of_forall fun τ => norm_nonneg _) hbound hlim
  exact this

theorem pxfidt_inv_Cn (n : ℕ) (hn : (d : ℝ) + 2 * n < 2 * m) (hOV : OV D ρ m T Ah) :
    ∃ Cinv : ℝ, 0 ≤ Cinv ∧ ∀ R : Torus d → Torus d → ℝ, IsCk2 (m + m) R →
      IsCk2 n (pairInverse D ρ R) ∧ cbNorm2 n (pairInverse D ρ R) ≤ Cinv * cbNorm2 (m + m) R := by
  obtain ⟨C0, c0, hC0, hc0, hC2⟩ := pxfidt_pair_Cn n hn hOV
  refine ⟨((n : ℝ) + 1) * C0 / c0, by positivity, fun R hR => ?_⟩
  have hreg : ∀ t : ℝ, 0 ≤ t → IsCk2 n (pairSemigroup D ρ t R) := fun t ht => (hC2 R hR t ht).1
  have hbd : ∀ t : ℝ, 0 ≤ t → cbNorm2 n (pairSemigroup D ρ t R) ≤
      (C0 * cbNorm2 (m + m) R) * Real.exp (-c0 * t) := fun t ht => (hC2 R hR t ht).2
  have hcont : ∀ i : ℕ, i ≤ n → ∀ p : Euc d × Euc d,
      ContinuousOn (fun t => iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ t R)) p) (Set.Ici 0) :=
    fun i hi p => pxfidt_pair_jets n hn hOV hR i hi p
  obtain ⟨-, hpt, hCk, -⟩ := MFPair.integral_family_isCk2 n (fun t => pairSemigroup D ρ t R)
    (C0 * cbNorm2 (m + m) R) c0 hc0 hreg hbd hcont
  obtain ⟨-, hb⟩ := MFPair.family_tail n (fun t => pairSemigroup D ρ t R) (C0 * cbNorm2 (m + m) R) c0 hc0
    hreg hbd hcont 0 le_rfl
  refine ⟨hCk, ?_⟩
  unfold cbNorm2
  have hn0 : 0 ≤ cbNorm2 (m + m) R := MFPair.cbNorm2_nonneg _ _
  calc ∑ i ∈ Finset.range (n + 1), ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ i (lift2 (pairInverse D ρ R)) p‖
      ≤ ∑ i ∈ Finset.range (n + 1), (C0 * cbNorm2 (m + m) R) * Real.exp (-c0 * 0) / c0 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        refine ciSup_le fun p => ?_
        exact hb i hi' p
    _ = ((n : ℝ) + 1) * C0 / c0 * cbNorm2 (m + m) R := by
        simp only [Finset.sum_const, Finset.card_range, mul_zero, Real.exp_zero, mul_one, nsmul_eq_mul]
        push_cast; field_simp

end Cn

/-- The pair inverse for `D = mfData` is `C^n` with `‖Ψ_R‖_{C^n} ≤ C ‖R‖_{C^{m+m}}` for `R ∈ C^{m+m}`,
`m ≥ px7_m d`, `d + 2n < 2m`. -/
theorem pxfidt_inv_Cn_spec (hd1 : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρC : Torus.IsSmooth ρ)
    (hpos : ∀ x, 0 < ρ x) (m : ℕ) (hmb : px7_m d ≤ m) (n : ℕ) (hn : (d : ℝ) + 2 * n < 2 * m) :
    ∃ Cinv : ℝ, 0 ≤ Cinv ∧ ∀ R : Torus d → Torus d → ℝ, IsCk2 (m + m) R →
      IsCk2 n (pairInverse (mfData d s hs0 hsd V β hβ) ρ R) ∧
      cbNorm2 n (pairInverse (mfData d s hs0 hsd V β hβ) ρ R) ≤ Cinv * cbNorm2 (m + m) R :=
  pxfidt_inv_Cn n hn (pxfidt_oneVar hd1 s hs0 hsd β hβ V hV ρ hρβ hρC hpos m hmb)

end HRS.PDE.PX7

end
