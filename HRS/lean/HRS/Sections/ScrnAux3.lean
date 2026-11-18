import HRS.Sections.ScrnAux2

/-!
# Packet SCRN, part 3: the Riemann sum `ℓ^d ∑_{k≠0} G(ℓk)` against `∫ G` (Proposition 6.1, covariance step)

Cubes `Q_k = ℓ (k + [-1/2,1/2)^d)` partition `ℝ^d`; for `G` with `|G| ≤ A(1+|ξ|)^{-L}` and the local
Lipschitz bound `|G(ξ) - G(η)| ≤ A|ξ-η|(1+|η|)^{-L}/|η|` on `|ξ - η| ≤ |η|/2`, `d ≥ 2`,
`|ℓ^d ∑_{k≠0} G(ℓk) - ∫G| ≤ C A ℓ` (`scrn_riemann`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HRS

variable {d : ℕ}

/-- The cube `ℓ (k + [-1/2, 1/2)^d)` in `ℝ^d`. -/
def scrnCube (d : ℕ) (ℓ : ℝ) (k : Lattice d) : Set (Euc d) :=
  (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹'
    (Set.pi Set.univ fun i => Set.Ico (ℓ * ((k i : ℝ) - 1 / 2)) (ℓ * ((k i : ℝ) + 1 / 2)))

lemma mem_scrnCube {ℓ : ℝ} {k : Lattice d} {ξ : Euc d} :
    ξ ∈ scrnCube d ℓ k ↔ ∀ i, ℓ * ((k i : ℝ) - 1 / 2) ≤ ξ i ∧ ξ i < ℓ * ((k i : ℝ) + 1 / 2) := by
  simp [scrnCube, Set.mem_pi]

lemma measurableSet_scrnCube (ℓ : ℝ) (k : Lattice d) : MeasurableSet (scrnCube d ℓ k) :=
  (MeasurableSet.univ_pi fun i => measurableSet_Ico).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

lemma volume_scrnCube {ℓ : ℝ} (hℓ : 0 < ℓ) (k : Lattice d) :
    volume (scrnCube d ℓ k) = ENNReal.ofReal (ℓ ^ d) := by
  unfold scrnCube
  rw [(PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
  have : ∀ i : Fin d, ℓ * ((k i : ℝ) + 1 / 2) - ℓ * ((k i : ℝ) - 1 / 2) = ℓ := fun i => by ring
  simp_rw [this]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hℓ.le]

lemma scrnCube_disjoint {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Pairwise (Function.onFun Disjoint (scrnCube d ℓ)) := by
  intro k k' hkk'
  rw [Function.onFun, Set.disjoint_left]
  intro ξ h1 h2
  rw [mem_scrnCube] at h1 h2
  apply hkk'
  funext i
  obtain ⟨a1, a2⟩ := h1 i
  obtain ⟨b1, b2⟩ := h2 i
  have c1 : ((k i : ℤ) : ℝ) < (k' i : ℝ) + 1 := by
    by_contra h
    push_neg at h
    nlinarith
  have c2 : ((k' i : ℤ) : ℝ) < (k i : ℝ) + 1 := by
    by_contra h
    push_neg at h
    nlinarith
  have d1 : k i < k' i + 1 := by exact_mod_cast c1
  have d2 : k' i < k i + 1 := by exact_mod_cast c2
  omega

lemma iUnion_scrnCube {ℓ : ℝ} (hℓ : 0 < ℓ) : ⋃ k : Lattice d, scrnCube d ℓ k = univ := by
  refine Set.eq_univ_of_forall fun ξ => ?_
  rw [Set.mem_iUnion]
  refine ⟨fun i => ⌊ξ i / ℓ + 1 / 2⌋, ?_⟩
  rw [mem_scrnCube]
  intro i
  have h1 := Int.floor_le (ξ i / ℓ + 1 / 2)
  have h2 := Int.lt_floor_add_one (ξ i / ℓ + 1 / 2)
  constructor
  · have : ((⌊ξ i / ℓ + 1 / 2⌋ : ℤ) : ℝ) * ℓ ≤ (ξ i / ℓ + 1 / 2) * ℓ :=
      mul_le_mul_of_nonneg_right h1 hℓ.le
    have e : (ξ i / ℓ + 1 / 2) * ℓ = ξ i + ℓ / 2 := by field_simp
    nlinarith
  · have : (ξ i / ℓ + 1 / 2) * ℓ < (((⌊ξ i / ℓ + 1 / 2⌋ : ℤ) : ℝ) + 1) * ℓ :=
      mul_lt_mul_of_pos_right h2 hℓ
    have e : (ξ i / ℓ + 1 / 2) * ℓ = ξ i + ℓ / 2 := by field_simp
    nlinarith

lemma norm_sub_le_of_mem_scrnCube {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Lattice d} {ξ : Euc d}
    (hξ : ξ ∈ scrnCube d ℓ k) : ‖ξ - ℓ • Lattice.toEuc k‖ ≤ ℓ * Real.sqrt d / 2 := by
  rw [mem_scrnCube] at hξ
  rw [EuclideanSpace.norm_eq]
  have hb : ∀ i : Fin d, ‖(ξ - ℓ • Lattice.toEuc k) i‖ ^ 2 ≤ (ℓ / 2) ^ 2 := by
    intro i
    obtain ⟨a, b⟩ := hξ i
    simp only [PiLp.sub_apply, PiLp.smul_apply, Lattice.toEuc, smul_eq_mul, Real.norm_eq_abs]
    rw [sq_abs]
    nlinarith
  calc Real.sqrt (∑ i, ‖(ξ - ℓ • Lattice.toEuc k) i‖ ^ 2)
      ≤ Real.sqrt (∑ _i : Fin d, (ℓ / 2) ^ 2) := Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => hb i)
    _ = ℓ * Real.sqrt d / 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (by positivity)]
        ring


lemma one_le_enorm_of_ne_zero {k : Lattice d} (hk : k ≠ 0) : 1 ≤ Lattice.enorm k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext h)
  have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
    have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|k i| : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h2
  exact h1.trans (abs_le_enorm k i)

lemma norm_smul_toEuc {ℓ : ℝ} (hℓ : 0 < ℓ) (k : Lattice d) :
    ‖ℓ • Lattice.toEuc k‖ = ℓ * Lattice.enorm k := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]; rfl

/-- The Riemann sum of `G` over the lattice `ℓℤ^d` (zero point omitted) against `∫ G`. -/
theorem scrn_riemann (hd : 2 ≤ d) {L : ℝ} (hL : (d : ℝ) < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (G : Euc d → ℂ), Measurable G →
      (∀ ξ, ‖G ξ‖ ≤ A * (1 + ‖ξ‖) ^ (-L)) →
      (∀ ξ η : Euc d, 0 < ‖η‖ → ‖ξ - η‖ ≤ ‖η‖ / 2 →
        ‖G ξ - G η‖ ≤ A * ‖ξ - η‖ * (1 + ‖η‖) ^ (-L) / ‖η‖) →
      ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 →
        ‖(∑' k : Lattice d, if k = 0 then (0 : ℂ) else ((ℓ ^ d : ℝ) : ℂ) * G (ℓ • Lattice.toEuc k))
          - ∫ ξ, G ξ‖ ≤ C * A * ℓ := by
  have hd0 : 0 < d := by omega
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hsd : (1 : ℝ) ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]; exact_mod_cast hd0
  obtain ⟨C₀, hC₀, hlat0⟩ := scrn_latsum hd0 (g := 0) (L := L) le_rfl (by exact_mod_cast hd0) hL
  obtain ⟨C₁, hC₁, hlat1⟩ := scrn_latsum hd0 (g := 1) (L := L) zero_le_one
    (by exact_mod_cast (by omega : 1 < d)) hL
  set cd : ℝ := max (2 * Real.sqrt d * (1 + Real.sqrt d) ^ L) (Real.sqrt d / 2) with hcd
  have hcd0 : 0 ≤ cd := le_max_of_le_right (by positivity)
  refine ⟨3 + cd * C₁, by positivity, ?_⟩
  intro A hA G hGm hG1 hG2 ℓ hℓ hℓ1
  have hLpos : 0 < L := by linarith
  -- integrability
  have hGint : Integrable G := by
    have hi : Integrable (fun ξ : Euc d => (1 + ‖ξ‖) ^ (-L)) := by
      refine integrable_one_add_norm (E := Euc d) ?_
      simpa using hL
    refine Integrable.mono' (hi.const_mul A) hGm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => hG1 ξ)
  have hcube : HasSum (fun k : Lattice d => ∫ ξ in scrnCube d ℓ k, G ξ) (∫ ξ, G ξ) := by
    have := hasSum_integral_iUnion (μ := volume) (f := G) (fun k => measurableSet_scrnCube ℓ k)
      (scrnCube_disjoint hℓ) (by rw [iUnion_scrnCube hℓ]; exact hGint.integrableOn)
    rwa [iUnion_scrnCube hℓ, Measure.restrict_univ] at this
  -- the cube terms
  set t : Lattice d → ℂ := fun k => ((ℓ ^ d : ℝ) : ℂ) * G (ℓ • Lattice.toEuc k) -
    ∫ ξ in scrnCube d ℓ k, G ξ with ht
  have hvolr : ∀ k, volume.real (scrnCube d ℓ k) = ℓ ^ d := fun k => by
    rw [Measure.real, volume_scrnCube hℓ, ENNReal.toReal_ofReal (by positivity)]
  have ht_eq : ∀ k, t k = ∫ ξ in scrnCube d ℓ k, (G (ℓ • Lattice.toEuc k) - G ξ) := by
    intro k
    have hfin : volume (scrnCube d ℓ k) < ∞ := by rw [volume_scrnCube hℓ]; exact ENNReal.ofReal_lt_top
    have hc : IntegrableOn (fun _ : Euc d => G (ℓ • Lattice.toEuc k)) (scrnCube d ℓ k) :=
      integrableOn_const (by exact hfin.ne) (by exact enorm_ne_top)
    rw [integral_sub hc hGint.integrableOn, setIntegral_const, hvolr]
    simp [ht]
  have hbd : ∀ k, ‖t k‖ ≤ (if k = 0 then 2 * A * ℓ ^ d else 0) +
      A * ℓ ^ d * cd * scrnW d 1 L ℓ k := by
    intro k
    have hfin : volume (scrnCube d ℓ k) < ∞ := by rw [volume_scrnCube hℓ]; exact ENNReal.ofReal_lt_top
    have hnn : 0 ≤ A * ℓ ^ d * cd * scrnW d 1 L ℓ k := by
      have := scrnW_nonneg (d := d) 1 L hℓ.le k
      positivity
    have gen : ∀ B : ℝ, (∀ ξ ∈ scrnCube d ℓ k, ‖G (ℓ • Lattice.toEuc k) - G ξ‖ ≤ B) →
        ‖t k‖ ≤ B * ℓ ^ d := by
      intro B hB
      rw [ht_eq k]
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) hfin hB
      rwa [hvolr] at this
    have hpow : (1 + ‖ℓ • Lattice.toEuc k‖) ^ (-L) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (ℓ • Lattice.toEuc k)])
        (by linarith)
    have hcrude : ∀ ξ : Euc d, ‖G (ℓ • Lattice.toEuc k) - G ξ‖ ≤ 2 * A := by
      intro ξ
      refine (norm_sub_le _ _).trans ?_
      have a1 := hG1 (ℓ • Lattice.toEuc k)
      have a2 := hG1 ξ
      have b1 : A * (1 + ‖ℓ • Lattice.toEuc k‖) ^ (-L) ≤ A := by
        calc _ ≤ A * 1 := by gcongr
          _ = A := mul_one A
      have b2 : A * (1 + ‖ξ‖) ^ (-L) ≤ A := by
        have : (1 + ‖ξ‖) ^ (-L) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg ξ]) (by linarith)
        calc _ ≤ A * 1 := by gcongr
          _ = A := mul_one A
      linarith
    by_cases hk : k = 0
    · subst hk
      simp only [if_true]
      have := gen (2 * A) (fun ξ _ => hcrude ξ)
      nlinarith
    · simp only [hk, if_false, zero_add]
      have he1 : 1 ≤ Lattice.enorm k := one_le_enorm_of_ne_zero hk
      have hnk := norm_smul_toEuc hℓ k
      have hwk : scrnW d 1 L ℓ k = (Lattice.enorm k)⁻¹ * (1 + ℓ * Lattice.enorm k) ^ (-L) := by
        unfold scrnW
        rw [max_eq_right he1, Real.rpow_neg_one]
      by_cases hnear : Real.sqrt d ≤ Lattice.enorm k
      · -- far lattice points: local Lipschitz
        have hη : 0 < ‖ℓ • Lattice.toEuc k‖ := by rw [hnk]; positivity
        have key : ∀ ξ ∈ scrnCube d ℓ k, ‖G (ℓ • Lattice.toEuc k) - G ξ‖ ≤
            A * (Real.sqrt d / 2) * ((Lattice.enorm k)⁻¹ * (1 + ℓ * Lattice.enorm k) ^ (-L)) := by
          intro ξ hξ
          have h1 := norm_sub_le_of_mem_scrnCube hℓ hξ
          have h2 : ‖ξ - ℓ • Lattice.toEuc k‖ ≤ ‖ℓ • Lattice.toEuc k‖ / 2 := by
            rw [hnk]
            calc _ ≤ ℓ * Real.sqrt d / 2 := h1
              _ ≤ ℓ * Lattice.enorm k / 2 := by gcongr
          have h3 := hG2 ξ (ℓ • Lattice.toEuc k) hη h2
          rw [norm_sub_rev] at h3
          refine h3.trans ?_
          rw [hnk]
          have he0 : 0 < Lattice.enorm k := by linarith
          calc A * ‖ξ - ℓ • Lattice.toEuc k‖ * (1 + ℓ * Lattice.enorm k) ^ (-L) / (ℓ * Lattice.enorm k)
              ≤ A * (ℓ * Real.sqrt d / 2) * (1 + ℓ * Lattice.enorm k) ^ (-L) /
                  (ℓ * Lattice.enorm k) := by
                gcongr
            _ = _ := by field_simp
        have := gen _ key
        rw [hwk]
        refine this.trans ?_
        have hW : 0 ≤ (Lattice.enorm k)⁻¹ * (1 + ℓ * Lattice.enorm k) ^ (-L) := by
          have he0 : 0 < Lattice.enorm k := by linarith
          exact mul_nonneg (inv_nonneg.2 he0.le) (Real.rpow_nonneg (by positivity) _)
        have hcd2 : Real.sqrt d / 2 ≤ cd := le_max_right _ _
        have hpd : 0 ≤ A * ℓ ^ d * ((Lattice.enorm k)⁻¹ * (1 + ℓ * Lattice.enorm k) ^ (-L)) := by
          positivity
        nlinarith [mul_le_mul_of_nonneg_left hcd2 hpd]
      · push_neg at hnear
        have := gen (2 * A) (fun ξ _ => hcrude ξ)
        rw [hwk]
        refine this.trans ?_
        have he0 : 0 < Lattice.enorm k := by linarith
        have hs0 : 0 < Real.sqrt d := by linarith
        have h1 : (Real.sqrt d)⁻¹ ≤ (Lattice.enorm k)⁻¹ := inv_anti₀ he0 hnear.le
        have h2 : (1 + Real.sqrt d) ^ (-L) ≤ (1 + ℓ * Lattice.enorm k) ^ (-L) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [hnear]) (by linarith)
        have h3 : (Real.sqrt d)⁻¹ * (1 + Real.sqrt d) ^ (-L) ≤
            (Lattice.enorm k)⁻¹ * (1 + ℓ * Lattice.enorm k) ^ (-L) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg (by positivity) _) (inv_nonneg.2 he0.le)
        have h4 : 2 ≤ cd * ((Lattice.enorm k)⁻¹ * (1 + ℓ * Lattice.enorm k) ^ (-L)) := by
          have hc : 2 * Real.sqrt d * (1 + Real.sqrt d) ^ L ≤ cd := le_max_left _ _
          have e1 : (1 + Real.sqrt d) ^ L * (1 + Real.sqrt d) ^ (-L) = 1 := by
            rw [← Real.rpow_add (by positivity)]; simp
          have e2 : Real.sqrt d * (Real.sqrt d)⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
          calc (2 : ℝ) = (2 * Real.sqrt d * (1 + Real.sqrt d) ^ L) *
                ((Real.sqrt d)⁻¹ * (1 + Real.sqrt d) ^ (-L)) := by
                calc (2 : ℝ) = 2 * (Real.sqrt d * (Real.sqrt d)⁻¹) *
                    ((1 + Real.sqrt d) ^ L * (1 + Real.sqrt d) ^ (-L)) := by rw [e2, e1]; ring
                  _ = _ := by ring
            _ ≤ cd * ((Lattice.enorm k)⁻¹ * (1 + ℓ * Lattice.enorm k) ^ (-L)) := by
                have hpos : 0 ≤ (Real.sqrt d)⁻¹ * (1 + Real.sqrt d) ^ (-L) :=
                  mul_nonneg (inv_nonneg.2 hs0.le) (Real.rpow_nonneg (by positivity) _)
                calc _ ≤ cd * ((Real.sqrt d)⁻¹ * (1 + Real.sqrt d) ^ (-L)) :=
                      mul_le_mul_of_nonneg_right hc hpos
                  _ ≤ _ := mul_le_mul_of_nonneg_left h3 hcd0
        have hAl : 0 ≤ A * ℓ ^ d := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h4 hAl]
  -- summability and the final estimate
  set m : Lattice d → ℝ := fun k => (if k = 0 then 2 * A * ℓ ^ d else 0) +
    A * ℓ ^ d * cd * scrnW d 1 L ℓ k with hm
  obtain ⟨hs1, hs1b⟩ := hlat1 ℓ hℓ hℓ1
  obtain ⟨hs0', hs0b⟩ := hlat0 ℓ hℓ hℓ1
  have hmsum : Summable m :=
    (hasSum_ite_eq (0 : Lattice d) (2 * A * ℓ ^ d)).summable.add (hs1.mul_left _)
  have hmtsum : ∑' k, m k = 2 * A * ℓ ^ d + A * ℓ ^ d * cd * ∑' k, scrnW d 1 L ℓ k := by
    rw [hm, Summable.tsum_add (hasSum_ite_eq (0 : Lattice d) (2 * A * ℓ ^ d)).summable
      (hs1.mul_left _), tsum_ite_eq, tsum_mul_left]
  have hts : Summable (fun k => ‖t k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd hmsum
  have hsumf : Summable (fun k : Lattice d => ((ℓ ^ d : ℝ) : ℂ) * G (ℓ • Lattice.toEuc k)) := by
    refine Summable.of_norm_bounded (hs0'.mul_left (A * ℓ ^ d)) (fun k => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := hG1 (ℓ • Lattice.toEuc k)
    rw [norm_smul_toEuc hℓ k] at h1
    have h2 : scrnW d 0 L ℓ k = (1 + ℓ * Lattice.enorm k) ^ (-L) := by
      unfold scrnW; simp
    rw [h2]
    calc ℓ ^ d * ‖G (ℓ • Lattice.toEuc k)‖ ≤ ℓ ^ d * (A * (1 + ℓ * Lattice.enorm k) ^ (-L)) := by
          gcongr
      _ = A * ℓ ^ d * (1 + ℓ * Lattice.enorm k) ^ (-L) := by ring
  have hsplit := hsumf.tsum_eq_add_tsum_ite (0 : Lattice d)
  have hT : ∑' k, t k = (∑' k : Lattice d, ((ℓ ^ d : ℝ) : ℂ) * G (ℓ • Lattice.toEuc k)) - ∫ ξ, G ξ :=
    (hsumf.hasSum.sub hcube).tsum_eq
  have hf0 : ‖((ℓ ^ d : ℝ) : ℂ) * G (ℓ • Lattice.toEuc (0 : Lattice d))‖ ≤ A * ℓ ^ d := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := hG1 (ℓ • Lattice.toEuc (0 : Lattice d))
    have h0 : ℓ • Lattice.toEuc (0 : Lattice d) = 0 := by
      ext i; simp [Lattice.toEuc]
    rw [h0] at h1 ⊢
    simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at h1
    nlinarith [pow_pos hℓ d]
  have hnorm : ‖(∑' k : Lattice d, if k = 0 then (0 : ℂ) else ((ℓ ^ d : ℝ) : ℂ) * G (ℓ • Lattice.toEuc k))
        - ∫ ξ, G ξ‖ ≤ (∑' k, ‖t k‖) + A * ℓ ^ d := by
    have e : (∑' k : Lattice d, if k = 0 then (0 : ℂ) else ((ℓ ^ d : ℝ) : ℂ) * G (ℓ • Lattice.toEuc k))
        - ∫ ξ, G ξ = (∑' k, t k) - ((ℓ ^ d : ℝ) : ℂ) * G (ℓ • Lattice.toEuc (0 : Lattice d)) := by
      rw [hT]
      rw [hsplit]
      ring
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add (norm_tsum_le_tsum_norm hts) hf0)
  have hsum_le : ∑' k, ‖t k‖ ≤ ∑' k, m k := hts.tsum_le_tsum hbd hmsum
  rw [hmtsum] at hsum_le
  have hpow : ℓ ^ d ≤ ℓ := pow_le_of_le_one hℓ.le hℓ1 (by omega)
  have hrp : ℓ ^ d * ℓ ^ (-((d : ℝ) - 1)) = ℓ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hℓ]; simp
  have hS1 : ∑' k, scrnW d 1 L ℓ k ≤ C₁ * ℓ ^ (-((d : ℝ) - 1)) := hs1b
  have hAcd : 0 ≤ A * ℓ ^ d * cd := by positivity
  calc ‖(∑' k : Lattice d, if k = 0 then (0 : ℂ) else ((ℓ ^ d : ℝ) : ℂ) * G (ℓ • Lattice.toEuc k))
        - ∫ ξ, G ξ‖ ≤ (∑' k, ‖t k‖) + A * ℓ ^ d := hnorm
    _ ≤ 2 * A * ℓ ^ d + A * ℓ ^ d * cd * (C₁ * ℓ ^ (-((d : ℝ) - 1))) + A * ℓ ^ d := by
        have := mul_le_mul_of_nonneg_left hS1 hAcd
        linarith
    _ = 3 * A * ℓ ^ d + A * cd * C₁ * (ℓ ^ d * ℓ ^ (-((d : ℝ) - 1))) := by ring
    _ = 3 * A * ℓ ^ d + A * cd * C₁ * ℓ := by rw [hrp]
    _ ≤ (3 + cd * C₁) * A * ℓ := by
        have : 3 * A * ℓ ^ d ≤ 3 * A * ℓ := by gcongr
        nlinarith

end HRS
