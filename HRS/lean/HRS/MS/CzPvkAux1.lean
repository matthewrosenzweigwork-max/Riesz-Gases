import Mathlib

/-!
# PV-KERNEL, part 1: the approximate identity for mean-zero kernels at Lebesgue points

Packet PVK (CZ development), namespace `HRS.CZ.Pvk`.  Infrastructure (not a manuscript row).

Main result `ae_tendsto_approxid_meanzero`: if `Ψ : ℝ^d → ℝ` is measurable with
`|Ψ z| ≤ C (1+‖z‖)^{-(d+1)}` and `∫ Ψ = 0`, and `g ∈ L^p` (`1 ≤ p`), then for a.e. `x`

`∫ Ψ_ε(z) • g(x-z) dz → 0` as `ε → 0+`, where `Ψ_ε z = ε^{-d} Ψ(z/ε)` (`pvkDil ε Ψ`).

Proof (no dyadic shells, no maximal theorem): `Ψ_ε` has mean zero, so the integral equals
`∫ Ψ_ε(z)(g(x-z)-g(x))`; its norm is bounded by `C J(ε)`, `J(ε) = ∫ ε^{-d}(1+|z|/ε)^{-(d+1)} h(z)`,
`h(z) = ‖g(x-z)-g(x)‖`.  The layer-cake formula `(1+r)^{-a} = ∫_r^∞ a(1+s)^{-(a+1)} ds` and Tonelli give
`J(ε) ≲ ∫_0^∞ w(s) ε^{-d} A(εs) ds` with `A(r) = ∫_{B(0,r)} h`; at a Lebesgue point `A(r)/|B_r| → 0`
(Mathlib's `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div`), and `A(r)/|B_r|` is bounded for all `r`
(Hölder for `r ≥ r₀`, no maximal function needed); dominated convergence in `s` finishes.

Adjustments with respect to the packet sketch (harmless): `g` takes values in an arbitrary real Banach
space `F` (`Ψ` real); `p` is any `1 ≤ p ≤ ∞` (`p < ∞` is not needed); the integrals are Bochner
integrals but the proof shows integrability for small `ε`, so no junk value enters (and if the
integrand were not integrable the integral would be `0`, which is consistent with the conclusion).
The decay hypothesis is stated with the real power `(1+‖z‖)^(-(d+1))`.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.CZ.Pvk

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The `L¹`-normalised dilation `Ψ_ε z = ε^{-d} Ψ(z/ε)`. -/
def pvkDil (ε : ℝ) (Ψ : 𝔼 → ℝ) (z : 𝔼) : ℝ := (ε ^ d)⁻¹ * Ψ (ε⁻¹ • z)

lemma pvk_dil_integral {ε : ℝ} (hε : 0 < ε) (Ψ : 𝔼 → ℝ) :
    ∫ z, pvkDil ε Ψ z = ∫ z, Ψ z := by
  unfold pvkDil
  rw [integral_const_mul, Measure.integral_comp_smul volume Ψ ε⁻¹]
  have : Module.finrank ℝ 𝔼 = d := finrank_euclideanSpace_fin
  rw [this, abs_of_nonneg (by positivity)]
  simp only [inv_pow, inv_inv, smul_eq_mul]
  field_simp

lemma pvk_dil_integrable {ε : ℝ} (hε : 0 < ε) {Ψ : 𝔼 → ℝ} (hΨ : Integrable Ψ) :
    Integrable (pvkDil ε Ψ) := by
  unfold pvkDil
  exact (hΨ.comp_smul (inv_ne_zero hε.ne')).const_mul _

/-- Layer-cake formula for the majorant `(1+r)^{-a}`. -/
lemma pvk_layer {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal ((1 + r) ^ (-a)) =
      ∫⁻ s in Ioi r, ENNReal.ofReal (a * (1 + s) ^ (-(a + 1))) := by
  have hint : IntegrableOn (fun s : ℝ => (s + 1) ^ (-(a + 1))) (Ioi r) :=
    integrableOn_add_rpow_Ioi_of_lt (by linarith) (by linarith)
  have hint' : IntegrableOn (fun s : ℝ => a * (1 + s) ^ (-(a + 1))) (Ioi r) := by
    simp_rw [add_comm (1:ℝ)]
    exact hint.const_mul a
  rw [← ofReal_integral_eq_lintegral_ofReal hint'
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => ?_))]
  · congr 1
    have hd : ∀ t ∈ Ici r, HasDerivAt (fun t : ℝ => -((t + 1) ^ (-a)))
        (a * (t + 1) ^ (-(a + 1))) t := by
      intro t ht
      have h1 : HasDerivAt (fun t : ℝ => t + 1) 1 t := (hasDerivAt_id t).add_const 1
      have h2 := (h1.rpow_const (p := -a) (Or.inl (ne_of_gt (by have := mem_Ici.1 ht; linarith)))).neg
      convert h2 using 1
      have : -a - 1 = -(a + 1) := by ring
      rw [this]; ring
    have hlim : Tendsto (fun t : ℝ => -((t + 1) ^ (-a))) atTop (𝓝 (-0)) :=
      ((tendsto_rpow_neg_atTop ha).comp (tendsto_atTop_add_const_right _ 1 tendsto_id)).neg
    have hint2 : IntegrableOn (fun t : ℝ => a * (t + 1) ^ (-(a + 1))) (Ioi r) := hint.const_mul a
    have := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint2 hlim
    simp_rw [add_comm (1:ℝ)]
    rw [this]; simp
  · have := mem_Ioi.1 hs
    have : 0 ≤ a * (1 + s) ^ (-(a + 1)) := by
      apply mul_nonneg ha.le; apply Real.rpow_nonneg; linarith
    simpa using this


section Lebesgue

variable {F : Type*} [NormedAddCommGroup F]

/-- Lebesgue differentiation along closed balls centred at the point (`ENNReal` form). -/
lemma pvk_leb_ratio {g : 𝔼 → F} (hg : LocallyIntegrable g volume) :
    ∀ᵐ x, Tendsto (fun r : ℝ => (∫⁻ y in closedBall x r, ‖g y - g x‖ₑ) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure 𝔼) 1).ae_tendsto_lintegral_enorm_sub_div hg]
    with x hx
  refine hx.comp (IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt (volume : Measure 𝔼)
    (fun _ => x) (fun r => r) tendsto_id ?_)
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [one_mul]
  exact mem_closedBall_self (le_of_lt hr)

/-- Hölder on a ball: `∫_S |g| ≤ ‖g‖_p |S|^{1-1/p}`. -/
lemma pvk_holder_set {g : 𝔼 → F} {p : ℝ≥0∞} (hp : 1 ≤ p) (hg : AEStronglyMeasurable g volume)
    (S : Set 𝔼) :
    ∫⁻ y in S, ‖g y‖ₑ ≤ eLpNorm g p volume * volume S ^ (1 - 1 / p.toReal) := by
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict S) (f := g)
    (p := 1) (q := p) hp hg.restrict
  rw [eLpNorm_one_eq_lintegral_enorm hg.restrict, Measure.restrict_apply_univ] at h1
  refine h1.trans (mul_le_mul' (eLpNorm_mono_measure g Measure.restrict_le_self) ?_)
  simp

/-- At a Lebesgue point of an `L^p` function, the ball averages of `|g y - g x|` are bounded for
all radii. -/
lemma pvk_leb_bound {g : 𝔼 → F} {p : ℝ≥0∞} (hp : 1 ≤ p) (hgp : MemLp g p volume) {x : 𝔼}
    (hx : Tendsto (fun r : ℝ => (∫⁻ y in closedBall x r, ‖g y - g x‖ₑ) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 0)) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ r > 0,
      ∫⁻ y in closedBall x r, ‖g y - g x‖ₑ ≤ B * volume (closedBall x r) := by
  have hev : ∀ᶠ r in 𝓝[>] (0:ℝ),
      (∫⁻ y in closedBall x r, ‖g y - g x‖ₑ) / volume (closedBall x r) ≤ 1 :=
    hx.eventually (ge_mem_nhds zero_lt_one)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0:ℝ) < u := hu
  set r1 : ℝ := u / 2 with hr1
  have hr1pos : 0 < r1 := by positivity
  have hV0 : ∀ r : ℝ, 0 < r → volume (closedBall x r) ≠ 0 := fun r hr =>
    (measure_closedBall_pos volume x hr).ne'
  have hVt : ∀ r : ℝ, volume (closedBall x r) ≠ ∞ := fun r => measure_closedBall_lt_top.ne
  set N := eLpNorm g p volume with hN
  have hNt : N ≠ ∞ := hgp.eLpNorm_lt_top.ne
  set W := volume (closedBall x r1) ^ (1 / p.toReal) with hW
  have hWpos : W ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 (hV0 r1 hr1pos)) (hVt r1)).ne'
  have hWt : W ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (hVt r1)
  refine ⟨max 1 (N * W⁻¹ + ‖g x‖ₑ), ?_, fun r hr => ?_⟩
  · exact max_ne_top ENNReal.one_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top hNt (ENNReal.inv_ne_top.2 hWpos), enorm_ne_top⟩)
  rcases lt_or_ge r u with hru | hru
  · have h := hsub ⟨hr, hru⟩
    have h' : (∫⁻ y in closedBall x r, ‖g y - g x‖ₑ) ≤ 1 * volume (closedBall x r) :=
      (ENNReal.div_le_iff (hV0 r hr) (hVt r)).1 h
    exact h'.trans (mul_le_mul_left (le_max_left _ _) _)
  · have hrr1 : r1 ≤ r := by rw [hr1]; linarith
    set V := volume (closedBall x r) with hV
    have hV1V : volume (closedBall x r1) ≤ V := measure_mono (closedBall_subset_closedBall hrr1)
    have hA : ∫⁻ y in closedBall x r, ‖g y - g x‖ₑ ≤
        (∫⁻ y in closedBall x r, ‖g y‖ₑ) + ‖g x‖ₑ * V := by
      calc ∫⁻ y in closedBall x r, ‖g y - g x‖ₑ
          ≤ ∫⁻ y in closedBall x r, (‖g y‖ₑ + ‖g x‖ₑ) :=
            lintegral_mono fun y => enorm_sub_le
        _ = (∫⁻ y in closedBall x r, ‖g y‖ₑ) + ‖g x‖ₑ * V := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    have hH := pvk_holder_set hp hgp.aestronglyMeasurable (closedBall x r)
    rw [← hN] at hH
    have hexp : V ^ (1 - 1 / p.toReal) = V * (V ^ (1 / p.toReal))⁻¹ := by
      have : (1 : ℝ) - 1 / p.toReal = 1 + -(1 / p.toReal) := by ring
      rw [this, ENNReal.rpow_add _ _ (hV0 r hr) (hVt r), ENNReal.rpow_one, ENNReal.rpow_neg]
    have hWV : W ≤ V ^ (1 / p.toReal) := ENNReal.rpow_le_rpow hV1V (by positivity)
    have hinv : (V ^ (1 / p.toReal))⁻¹ ≤ W⁻¹ := ENNReal.inv_le_inv.2 hWV
    calc ∫⁻ y in closedBall x r, ‖g y - g x‖ₑ
        ≤ (∫⁻ y in closedBall x r, ‖g y‖ₑ) + ‖g x‖ₑ * V := hA
      _ ≤ N * (V * W⁻¹) + ‖g x‖ₑ * V := by
          gcongr
          calc ∫⁻ y in closedBall x r, ‖g y‖ₑ ≤ N * V ^ (1 - 1 / p.toReal) := hH
            _ = N * (V * (V ^ (1 / p.toReal))⁻¹) := by rw [hexp]
            _ ≤ N * (V * W⁻¹) := by gcongr
      _ = (N * W⁻¹ + ‖g x‖ₑ) * V := by ring
      _ ≤ max 1 (N * W⁻¹ + ‖g x‖ₑ) * V := mul_le_mul_left (le_max_right _ _) _

end Lebesgue


section Layer

/-- The layer-cake weight `w(s) = (d+1) (1+s)^{-(d+2)}` as an extended nonnegative real. -/
def pvkW (d : ℕ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((d:ℝ) + 1) * (1 + s) ^ (-(((d:ℝ) + 1) + 1)))

lemma pvkW_measurable (d : ℕ) : Measurable (pvkW d) := by
  unfold pvkW
  refine ENNReal.measurable_ofReal.comp ?_
  exact (measurable_const.mul (Measurable.pow_const (measurable_const.add measurable_id) _))

/-- Tonelli step: the dilated majorant integrated against `h` is a layer integral of
ball integrals of `h`. -/
lemma pvk_tonelli {h : 𝔼 → ℝ≥0∞} (hm : Measurable h) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ z, ENNReal.ofReal ((ε ^ d)⁻¹ * (1 + ε⁻¹ * ‖z‖) ^ (-((d:ℝ) + 1))) * h z ≤
      ∫⁻ s in Ioi (0:ℝ), pvkW d s *
        (ENNReal.ofReal ((ε ^ d)⁻¹) * ∫⁻ z in closedBall (0:𝔼) (ε * s), h z) := by
  set G : 𝔼 × ℝ → ℝ≥0∞ := Set.indicator {q : 𝔼 × ℝ | ε⁻¹ * ‖q.1‖ < q.2}
    (fun q => ENNReal.ofReal ((ε ^ d)⁻¹) * pvkW d q.2 * h q.1) with hG
  have hSm : MeasurableSet {q : 𝔼 × ℝ | ε⁻¹ * ‖q.1‖ < q.2} :=
    measurableSet_lt (measurable_const.mul measurable_fst.norm) measurable_snd
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ hSm
    exact (measurable_const.mul ((pvkW_measurable d).comp measurable_snd)).mul
      (hm.comp measurable_fst)
  have h1 : ∀ z : 𝔼, ENNReal.ofReal ((ε ^ d)⁻¹ * (1 + ε⁻¹ * ‖z‖) ^ (-((d:ℝ) + 1))) * h z
      = ∫⁻ s, G (z, s) := by
    intro z
    have hr : 0 ≤ ε⁻¹ * ‖z‖ := by positivity
    have hl := pvk_layer (a := (d:ℝ) + 1) (by positivity) hr
    have hGz : ∀ s, G (z, s) = (Ioi (ε⁻¹ * ‖z‖)).indicator
        (fun s => ENNReal.ofReal ((ε ^ d)⁻¹) * pvkW d s * h z) s := by
      intro s
      simp only [hG, Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioi]
    simp_rw [hGz]
    rw [lintegral_indicator measurableSet_Ioi,
      lintegral_mul_const (h z) (f := fun s => ENNReal.ofReal ((ε ^ d)⁻¹) * pvkW d s)
        (measurable_const.mul (pvkW_measurable d)),
      lintegral_const_mul _ (pvkW_measurable d)]
    have : ∫⁻ s in Ioi (ε⁻¹ * ‖z‖), pvkW d s = ENNReal.ofReal ((1 + ε⁻¹ * ‖z‖) ^ (-((d:ℝ) + 1))) :=
      hl.symm
    rw [this, ENNReal.ofReal_mul (by positivity)]
  have h2 : ∀ s : ℝ, ∫⁻ z, G (z, s) ≤ (Ioi (0:ℝ)).indicator (fun s => pvkW d s *
      (ENNReal.ofReal ((ε ^ d)⁻¹) * ∫⁻ z in closedBall (0:𝔼) (ε * s), h z)) s := by
    intro s
    by_cases hs : 0 < s
    · rw [Set.indicator_of_mem (mem_Ioi.2 hs)]
      have hle : ∀ z : 𝔼, G (z, s) ≤ (closedBall (0:𝔼) (ε * s)).indicator
          (fun z => ENNReal.ofReal ((ε ^ d)⁻¹) * pvkW d s * h z) z := by
        intro z
        by_cases hz : ε⁻¹ * ‖z‖ < s
        · have hz' : z ∈ closedBall (0:𝔼) (ε * s) := by
            rw [mem_closedBall_zero_iff]
            have := (inv_mul_lt_iff₀ hε).1 hz
            exact this.le
          rw [Set.indicator_of_mem hz', hG,
            Set.indicator_of_mem (show (z, s) ∈ {q : 𝔼 × ℝ | ε⁻¹ * ‖q.1‖ < q.2} from hz)]
        · simp [hG, Set.indicator, hz]
      calc ∫⁻ z, G (z, s) ≤ ∫⁻ z, (closedBall (0:𝔼) (ε * s)).indicator
            (fun z => ENNReal.ofReal ((ε ^ d)⁻¹) * pvkW d s * h z) z := lintegral_mono hle
        _ = ∫⁻ z in closedBall (0:𝔼) (ε * s),
            ENNReal.ofReal ((ε ^ d)⁻¹) * pvkW d s * h z := by
            rw [lintegral_indicator measurableSet_closedBall]
        _ = pvkW d s * (ENNReal.ofReal ((ε ^ d)⁻¹) * ∫⁻ z in closedBall (0:𝔼) (ε * s), h z) := by
            rw [lintegral_const_mul _ hm]; ring
    · have : ∀ z : 𝔼, G (z, s) = 0 := by
        intro z
        have : ¬ ε⁻¹ * ‖z‖ < s := by
          have : 0 ≤ ε⁻¹ * ‖z‖ := by positivity
          linarith [not_lt.1 hs]
        simp [hG, this]
      simp [this]
  calc ∫⁻ z, ENNReal.ofReal ((ε ^ d)⁻¹ * (1 + ε⁻¹ * ‖z‖) ^ (-((d:ℝ) + 1))) * h z
      = ∫⁻ z, ∫⁻ s, G (z, s) := lintegral_congr h1
    _ = ∫⁻ s, ∫⁻ z, G (z, s) := lintegral_lintegral_swap hGm.aemeasurable
    _ ≤ ∫⁻ s, (Ioi (0:ℝ)).indicator (fun s => pvkW d s *
        (ENNReal.ofReal ((ε ^ d)⁻¹) * ∫⁻ z in closedBall (0:𝔼) (ε * s), h z)) s :=
        lintegral_mono h2
    _ = _ := by
        rw [lintegral_indicator measurableSet_Ioi]


lemma pvkW_integrable_aux (d : ℕ) :
    ∫⁻ s in Ioi (0:ℝ), pvkW d s * ENNReal.ofReal (s ^ d) ≠ ∞ := by
  have hint : IntegrableOn (fun s : ℝ => (s + 1) ^ (-(2:ℝ))) (Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (by norm_num) (by norm_num)
  have hint' : IntegrableOn (fun s : ℝ => ((d:ℝ) + 1) * (1 + s) ^ (-(2:ℝ))) (Ioi 0) := by
    simp_rw [add_comm (1:ℝ)]
    exact hint.const_mul _
  have hle : ∀ s ∈ Ioi (0:ℝ), pvkW d s * ENNReal.ofReal (s ^ d) ≤
      ENNReal.ofReal (((d:ℝ) + 1) * (1 + s) ^ (-(2:ℝ))) := by
    intro s hs
    have hs0 : 0 < s := hs
    unfold pvkW
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : s ^ d ≤ (1 + s) ^ d := pow_le_pow_left₀ hs0.le (by linarith) d
    have h2 : (1 + s) ^ (-(((d:ℝ) + 1) + 1)) * (1 + s) ^ d = (1 + s) ^ (-(2:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
      congr 1; ring
    calc ((d:ℝ) + 1) * (1 + s) ^ (-(((d:ℝ) + 1) + 1)) * s ^ d
        ≤ ((d:ℝ) + 1) * (1 + s) ^ (-(((d:ℝ) + 1) + 1)) * (1 + s) ^ d := by
          gcongr
      _ = ((d:ℝ) + 1) * (1 + s) ^ (-(2:ℝ)) := by rw [mul_assoc, h2]
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' measurableSet_Ioi hle)
  rw [← ofReal_integral_eq_lintegral_ofReal hint' (ae_restrict_of_forall_mem measurableSet_Ioi
    fun s hs => by have : (0:ℝ) < s := hs; positivity)]
  exact ENNReal.ofReal_ne_top


/-- **Shell estimate.**  If the ball integrals of `h ≥ 0` are `o(|B_r|)` as `r → 0` and `O(|B_r|)`
for all `r`, then the integrals of `h` against the dilated majorant `ε^{-d}(1+|z|/ε)^{-(d+1)}`
tend to `0`. -/
lemma pvk_shell_tendsto {h : 𝔼 → ℝ≥0∞} (hm : Measurable h) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hbd : ∀ r > 0, ∫⁻ z in closedBall (0:𝔼) r, h z ≤ B * volume (closedBall (0:𝔼) r))
    (hlim : Tendsto (fun r : ℝ => (∫⁻ z in closedBall (0:𝔼) r, h z) /
      volume (closedBall (0:𝔼) r)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ∫⁻ z, ENNReal.ofReal ((ε ^ d)⁻¹ * (1 + ε⁻¹ * ‖z‖) ^ (-((d:ℝ) + 1))) *
      h z) (𝓝[>] 0) (𝓝 0) := by
  set V1 : ℝ≥0∞ := volume (ball (0:𝔼) 1) with hV1def
  have hV1 : V1 ≠ ∞ := measure_ball_lt_top.ne
  have hvol : ∀ r : ℝ, 0 ≤ r → volume (closedBall (0:𝔼) r) = ENNReal.ofReal (r ^ d) * V1 := by
    intro r hr
    rw [Measure.addHaar_closedBall volume 0 hr, finrank_euclideanSpace_fin]
  set A : ℝ → ℝ≥0∞ := fun r => ∫⁻ z in closedBall (0:𝔼) r, h z with hA
  have hVt : ∀ r : ℝ, volume (closedBall (0:𝔼) r) ≠ ∞ := fun r => measure_closedBall_lt_top.ne
  have hV0 : ∀ r : ℝ, 0 < r → volume (closedBall (0:𝔼) r) ≠ 0 := fun r hr =>
    (measure_closedBall_pos volume _ hr).ne'
  have hscale : ∀ ε s : ℝ, 0 < ε → 0 < s →
      ENNReal.ofReal ((ε ^ d)⁻¹) * volume (closedBall (0:𝔼) (ε * s)) =
        V1 * ENNReal.ofReal (s ^ d) := by
    intro ε s hε hs
    have h1 : ENNReal.ofReal ((ε ^ d)⁻¹) * ENNReal.ofReal ((ε * s) ^ d) =
        ENNReal.ofReal (s ^ d) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [mul_pow]; field_simp
    rw [hvol _ (by positivity), ← mul_assoc, h1, mul_comm]
  have hAeq : ∀ ε s : ℝ, 0 < ε → 0 < s → ENNReal.ofReal ((ε ^ d)⁻¹) * A (ε * s) =
      (A (ε * s) / volume (closedBall (0:𝔼) (ε * s))) * (V1 * ENNReal.ofReal (s ^ d)) := by
    intro ε s hε hs
    have hp : 0 < ε * s := by positivity
    rw [← hscale ε s hε hs]
    calc ENNReal.ofReal ((ε ^ d)⁻¹) * A (ε * s)
        = ENNReal.ofReal ((ε ^ d)⁻¹) * ((A (ε * s) / volume (closedBall (0:𝔼) (ε * s))) *
            volume (closedBall (0:𝔼) (ε * s))) := by
          rw [ENNReal.div_mul_cancel (hV0 _ hp) (hVt _)]
      _ = _ := by ring
  set w : ℝ → ℝ≥0∞ := pvkW d with hw
  set F : ℝ → ℝ → ℝ≥0∞ := fun ε s => (Ioi (0:ℝ)).indicator
    (fun s => w s * (ENNReal.ofReal ((ε ^ d)⁻¹) * A (ε * s))) s with hF
  set bnd : ℝ → ℝ≥0∞ := fun s => (Ioi (0:ℝ)).indicator
    (fun s => (B * V1) * (w s * ENNReal.ofReal (s ^ d))) s with hbnd
  have hFm : ∀ᶠ ε in 𝓝[>] (0:ℝ), Measurable (F ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    refine Measurable.indicator ?_ measurableSet_Ioi
    refine (pvkW_measurable d).mul (measurable_const.mul ?_)
    have hmono : Monotone (fun s : ℝ => A (ε * s)) := by
      intro s t hst
      exact lintegral_mono_set (closedBall_subset_closedBall
        (mul_le_mul_of_nonneg_left hst hε'.le))
    exact hmono.measurable
  have hFb : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᵐ s, F ε s ≤ bnd s := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    refine ae_of_all _ fun s => ?_
    by_cases hs : 0 < s
    · simp only [hF, hbnd, Set.indicator_of_mem (mem_Ioi.2 hs)]
      calc w s * (ENNReal.ofReal ((ε ^ d)⁻¹) * A (ε * s))
          ≤ w s * (ENNReal.ofReal ((ε ^ d)⁻¹) * (B * volume (closedBall (0:𝔼) (ε * s)))) := by
            gcongr
            exact hbd _ (by positivity)
        _ = w s * (B * (ENNReal.ofReal ((ε ^ d)⁻¹) * volume (closedBall (0:𝔼) (ε * s)))) := by
            ring
        _ = (B * V1) * (w s * ENNReal.ofReal (s ^ d)) := by
            rw [hscale ε s hε' hs]; ring
    · simp [hF, hs]
  have hfin : ∫⁻ s, bnd s ≠ ∞ := by
    simp only [hbnd]
    rw [lintegral_indicator measurableSet_Ioi, lintegral_const_mul' _ _
      (ENNReal.mul_ne_top hB hV1)]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hB hV1) (pvkW_integrable_aux d)
  have hlimF : ∀ᵐ s : ℝ, Tendsto (fun ε => F ε s) (𝓝[>] (0:ℝ)) (𝓝 ((fun _ => (0:ℝ≥0∞)) s)) := by
    refine ae_of_all _ fun s => ?_
    by_cases hs : 0 < s
    · simp only [hF, Set.indicator_of_mem (mem_Ioi.2 hs)]
      have hρ : Tendsto (fun ε : ℝ => A (ε * s) / volume (closedBall (0:𝔼) (ε * s)))
          (𝓝[>] 0) (𝓝 0) := by
        refine hlim.comp ?_
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have : Tendsto (fun ε : ℝ => ε * s) (𝓝 0) (𝓝 (0 * s)) :=
            (continuous_id.mul continuous_const).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          exact mul_pos hε hs
      have h2 : Tendsto (fun ε : ℝ => w s * ((A (ε * s) / volume (closedBall (0:𝔼) (ε * s))) *
          (V1 * ENNReal.ofReal (s ^ d)))) (𝓝[>] 0) (𝓝 (w s * (0 * (V1 * ENNReal.ofReal (s ^ d))))) := by
        refine ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const hρ
          (Or.inr (ENNReal.mul_ne_top hV1 ENNReal.ofReal_ne_top))) ?_
        exact Or.inr ENNReal.ofReal_ne_top
      simp only [zero_mul, mul_zero] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [hAeq ε s hε hs]
    · simp [hF, hs]
  have hD := tendsto_lintegral_filter_of_dominated_convergence (l := 𝓝[>] (0:ℝ)) (F := F)
    (f := fun _ => (0:ℝ≥0∞)) bnd hFm hFb hfin hlimF
  simp only [lintegral_zero] at hD
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hD
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  refine (pvk_tonelli hm hε).trans (le_of_eq ?_)
  simp only [hF]
  rw [lintegral_indicator measurableSet_Ioi]

end Layer


section Main

lemma pvk_Psi_integrable {Ψ : 𝔼 → ℝ} (hΨm : Measurable Ψ) {C : ℝ}
    (hΨ : ∀ z, |Ψ z| ≤ C * (1 + ‖z‖) ^ (-((d:ℝ) + 1))) : Integrable Ψ := by
  have h := (integrable_one_add_norm (E := 𝔼) (μ := volume) (r := (d:ℝ) + 1)
    (by rw [finrank_euclideanSpace_fin]; linarith)).const_mul C
  refine h.mono' hΨm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  simpa [Real.norm_eq_abs] using hΨ z

lemma pvk_C_nonneg {Ψ : 𝔼 → ℝ} {C : ℝ}
    (hΨ : ∀ z, |Ψ z| ≤ C * (1 + ‖z‖) ^ (-((d:ℝ) + 1))) : 0 ≤ C := by
  have h := hΨ 0
  simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at h
  exact (abs_nonneg _).trans h

lemma pvk_dil_enorm_le {Ψ : 𝔼 → ℝ} {C : ℝ}
    (hΨ : ∀ z, |Ψ z| ≤ C * (1 + ‖z‖) ^ (-((d:ℝ) + 1))) {ε : ℝ} (hε : 0 < ε) (z : 𝔼) :
    ‖pvkDil ε Ψ z‖ₑ ≤ ENNReal.ofReal C *
      ENNReal.ofReal ((ε ^ d)⁻¹ * (1 + ε⁻¹ * ‖z‖) ^ (-((d:ℝ) + 1))) := by
  rw [← ENNReal.ofReal_mul (pvk_C_nonneg hΨ), ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  unfold pvkDil
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 := hΨ (ε⁻¹ • z)
  have hn : ‖ε⁻¹ • z‖ = ε⁻¹ * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hn] at h1
  calc (ε ^ d)⁻¹ * |Ψ (ε⁻¹ • z)| ≤ (ε ^ d)⁻¹ * (C * (1 + ε⁻¹ * ‖z‖) ^ (-((d:ℝ) + 1))) := by
        gcongr
    _ = _ := by ring


variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma pvk_dil_measurable {Ψ : 𝔼 → ℝ} (hΨm : Measurable Ψ) (ε : ℝ) :
    Measurable (pvkDil ε Ψ) :=
  measurable_const.mul (hΨm.comp (measurable_id.const_smul ε⁻¹))

/-- The approximate identity at a good point `x`. -/
lemma pvk_approxid_at [CompleteSpace F] {Ψ : 𝔼 → ℝ} (hΨm : Measurable Ψ) {C : ℝ}
    (hΨ : ∀ z, |Ψ z| ≤ C * (1 + ‖z‖) ^ (-((d:ℝ) + 1))) (hΨ0 : ∫ z, Ψ z = 0)
    {g : 𝔼 → F} (hgs : StronglyMeasurable g) {p : ℝ≥0∞} (hp : 1 ≤ p) (hgp : MemLp g p volume)
    {x : 𝔼}
    (hx : Tendsto (fun r : ℝ => (∫⁻ y in closedBall x r, ‖g y - g x‖ₑ) /
      volume (closedBall x r)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ∫ z, pvkDil ε Ψ z • g (x - z)) (𝓝[>] 0) (𝓝 0) := by
  set h : 𝔼 → ℝ≥0∞ := fun z => ‖g (x - z) - g x‖ₑ with hh
  have hgm : StronglyMeasurable (fun z : 𝔼 => g (x - z)) :=
    hgs.comp_measurable (measurable_const.sub measurable_id)
  have hhm : Measurable h := (hgm.sub stronglyMeasurable_const).enorm
  have hT : MeasurePreserving (fun z : 𝔼 => x - z) volume volume :=
    Measure.measurePreserving_sub_left volume x
  have hA : ∀ r : ℝ, ∫⁻ z in closedBall (0:𝔼) r, h z =
      ∫⁻ y in closedBall x r, ‖g y - g x‖ₑ := by
    intro r
    have hpre : (fun z : 𝔼 => x - z) ⁻¹' closedBall x r = closedBall 0 r := by
      ext z; simp [mem_closedBall, dist_eq_norm]
    have := hT.setLIntegral_comp_preimage (s := closedBall x r) measurableSet_closedBall
      (f := fun y => ‖g y - g x‖ₑ) (hgs.sub stronglyMeasurable_const).enorm
    rw [hpre] at this; exact this
  have hV : ∀ r : ℝ, 0 < r → volume (closedBall x r) = volume (closedBall (0:𝔼) r) := by
    intro r hr; rw [Measure.addHaar_closedBall _ _ hr.le, Measure.addHaar_closedBall _ _ hr.le]
  obtain ⟨B, hB, hBd⟩ := pvk_leb_bound hp hgp hx
  have hlim0 : Tendsto (fun r : ℝ => (∫⁻ z in closedBall (0:𝔼) r, h z) /
      volume (closedBall (0:𝔼) r)) (𝓝[>] 0) (𝓝 0) := by
    refine hx.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [hA, hV r hr]
  have hJ := pvk_shell_tendsto hhm hB (fun r hr => by rw [hA, ← hV r hr]; exact hBd r hr) hlim0
  set J : ℝ → ℝ≥0∞ := fun ε => ∫⁻ z, ENNReal.ofReal ((ε ^ d)⁻¹ *
    (1 + ε⁻¹ * ‖z‖) ^ (-((d:ℝ) + 1))) * h z with hJdef
  have hΨint := pvk_Psi_integrable hΨm hΨ
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε ∧ J ε < ⊤ := by
    filter_upwards [self_mem_nhdsWithin, hJ.eventually (gt_mem_nhds ENNReal.zero_lt_top)]
      with ε hε hJε
    exact ⟨hε, hJε⟩
  have key : ∀ ε : ℝ, 0 < ε → J ε < ⊤ →
      ‖∫ z, pvkDil ε Ψ z • g (x - z)‖ₑ ≤ ENNReal.ofReal C * J ε := by
    intro ε hε hJε
    have hΨε := pvk_dil_measurable hΨm ε
    set f1 : 𝔼 → F := fun z => pvkDil ε Ψ z • (g (x - z) - g x) with hf1
    have hf1m : AEStronglyMeasurable f1 volume :=
      (hΨε.stronglyMeasurable.smul (hgm.sub stronglyMeasurable_const)).aestronglyMeasurable
    have hbound : ∫⁻ z, ‖f1 z‖ₑ ≤ ENNReal.ofReal C * J ε := by
      calc ∫⁻ z, ‖f1 z‖ₑ ≤ ∫⁻ z, ENNReal.ofReal C * (ENNReal.ofReal ((ε ^ d)⁻¹ *
              (1 + ε⁻¹ * ‖z‖) ^ (-((d:ℝ) + 1))) * h z) := by
            refine lintegral_mono fun z => ?_
            simp only [hf1, enorm_smul]
            calc ‖pvkDil ε Ψ z‖ₑ * ‖g (x - z) - g x‖ₑ
                ≤ (ENNReal.ofReal C * ENNReal.ofReal ((ε ^ d)⁻¹ *
                  (1 + ε⁻¹ * ‖z‖) ^ (-((d:ℝ) + 1)))) * h z :=
                  mul_le_mul_left (pvk_dil_enorm_le hΨ hε z) _
              _ = _ := by rw [mul_assoc]
        _ = ENNReal.ofReal C * J ε := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hf1i : Integrable f1 volume :=
      ⟨hf1m, (hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJε))⟩
    have hf2i : Integrable (fun z => pvkDil ε Ψ z • g x) volume :=
      (pvk_dil_integrable hε hΨint).smul_const (g x)
    have hsplit : (fun z => pvkDil ε Ψ z • g (x - z)) = fun z => f1 z + pvkDil ε Ψ z • g x := by
      funext z; simp [hf1, smul_sub]
    have hzero : ∫ z, pvkDil ε Ψ z • g x = 0 := by
      rw [integral_smul_const, pvk_dil_integral hε, hΨ0, zero_smul]
    rw [hsplit, integral_add hf1i hf2i, hzero, add_zero]
    exact (enorm_integral_le_lintegral_enorm f1).trans hbound
  have hlim : Tendsto (fun ε => ENNReal.ofReal C * J ε) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hJ (Or.inr (ENNReal.ofReal_ne_top (r := C)))
    simpa using this
  rw [tendsto_zero_iff_enorm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hev] with ε hε
  exact key ε hε.1 hε.2


/-- **Approximate identity for mean-zero kernels (a.e. convergence at Lebesgue points).**
For `Ψ` measurable with `|Ψ z| ≤ C (1+|z|)^{-(d+1)}` and `∫ Ψ = 0`, and `g ∈ L^p` (`1 ≤ p`),
for almost every `x`: `∫ Ψ_ε(z) g(x-z) dz → 0` as `ε → 0+`, where `Ψ_ε z = ε^{-d} Ψ(z/ε)`.
(The integrals are genuine Lebesgue integrals: the integrand is integrable for small `ε`.) -/
theorem ae_tendsto_approxid_meanzero [CompleteSpace F] {Ψ : 𝔼 → ℝ} (hΨm : Measurable Ψ)
    {C : ℝ} (hΨ : ∀ z, |Ψ z| ≤ C * (1 + ‖z‖) ^ (-((d:ℝ) + 1))) (hΨ0 : ∫ z, Ψ z = 0)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {g : 𝔼 → F} (hg : MemLp g p volume) :
    ∀ᵐ x ∂(volume : Measure 𝔼),
      Tendsto (fun ε : ℝ => ∫ z, pvkDil ε Ψ z • g (x - z)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨g', hg's, hgg'⟩ := hg.aestronglyMeasurable
  have hg' : MemLp g' p volume := hg.ae_eq hgg'
  filter_upwards [pvk_leb_ratio (hg'.locallyIntegrable hp)] with x hx
  have hae : (fun z : 𝔼 => g (x - z)) =ᵐ[volume] fun z => g' (x - z) :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae_eq_comp hgg'
  have : ∀ ε : ℝ, ∫ z, pvkDil ε Ψ z • g (x - z) = ∫ z, pvkDil ε Ψ z • g' (x - z) := by
    intro ε
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    simp only [hz]
  simp_rw [this]
  exact pvk_approxid_at hΨm hΨ hΨ0 hg's hp hg' hx

end Main

end HRS.CZ.Pvk
