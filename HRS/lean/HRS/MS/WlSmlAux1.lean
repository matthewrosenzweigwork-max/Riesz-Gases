import HRS.MS.WlSphAux2
import HRS.MS.WlEnsAux2
import HRS.MS.WrSmlAux2

/-!
# WL-4b (part 1): the band-split lower bound for the energy of the tail kernel `q_M`

Packet WL-4b of `docs/WR_LOG_PLAN.md` (Step 6, S3.5 `r2_log_static`), namespace `HRS.MS.Wl`, helper prefix
`wl4b_`.  Infrastructure lemmas, not manuscript rows.  `K = sphericalLogKernel`, `q_M = wl_qm M`,
`μ = withDensityReal ρ`, `pairEnergy k X μ = 𝖥_n^k(X, μ)` (`HRS.Whole.pairEnergy`).

* `wl4b_band_energy`: `n 𝖥_n^{band(M,L]}(X) ≥ -(1/2) k0(L)` for EVERY configuration `X` (`energy_identity_P`
  for the finite-dimensional tensor feature of the band, `WlSphAux2`);
* `wl4b_energy_ge_neg_row`: `𝖥_n^q ≥ -a` for a weak kernel with row bound `a`;
* `wl_energy_lower`: `-(C log(e n)) ≤ n 𝖥_n^{q_M}(X, μ)` for every injective `X`, uniformly in `ρ` (`C = C(d, A, M)`),
  by the split `q_M = q_L + band(M, L]` (`wl_qm_eq_qm_add_band`) at `L = max (M+1) ⌈n^{2/d}⌉`, the row bound
  `wl_row_qm` for `q_L` (via `wl_qm_weak`) and `k0 L ≤ (1 + log L)/2`.

Documented adjustments: none beyond fixing the signature (`M` is an arbitrary natural number, `C` depends on `M`).
-/

set_option linter.unusedSectionVars false

open MeasureTheory InformationTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

variable {d : ℕ}

/-- A measurable bounded kernel is `Wr8Ok`. -/
lemma wl4b_wr8_of_bdd {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {k : Euc d → Euc d → ℝ}
    (hm : Measurable (fun p : Euc d × Euc d => k p.1 p.2)) {b : ℝ} (hb : ∀ x y, |k x y| ≤ b) :
    Wr8Ok μ k := by
  refine ⟨hm, fun x => ?_, ?_⟩
  · exact Integrable.of_bound (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable b
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hb x y)
  · exact Integrable.of_bound hm.aestronglyMeasurable b
      (Filter.Eventually.of_forall fun p => by
        show ‖k p.1 p.2‖ ≤ b
        rw [Real.norm_eq_abs]; exact hb p.1 p.2)

lemma wl4b_band_le_k0 {M L : ℕ} (hML : M ≤ L) (x y : Euc d) : wl_band M L x y ≤ wl_k0 L := by
  have h1 := wl_km_le_k0 L x y
  have h2 := wl_km_nonneg M x y
  unfold wl_band; linarith

lemma wl4b_band_wr8 {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {M L : ℕ} (hML : M ≤ L) :
    Wr8Ok μ (wl_band M L) :=
  wl4b_wr8_of_bdd (wl_band_measurable M L) (b := wl_k0 L) fun x y => by
    rw [abs_of_nonneg (wl_band_nonneg hML x y)]
    exact wl4b_band_le_k0 hML x y

/-- Energy of the band: `n 𝖥_n^{band} ≥ -(1/2) k0(L)` for every configuration. -/
lemma wl4b_band_energy {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {M L : ℕ} (hML : M ≤ L) {n : ℕ}
    (hn : 1 ≤ n) (X : Fin n → Euc d) :
    -((1 / 2) * wl_k0 L) ≤ (n : ℝ) * HRS.Whole.pairEnergy (wl_band M L) X μ := by
  rw [energy_identity_P (wl_psiBand_hyp hML) μ hn X]
  have h1 : 0 ≤ (1 / 2 : ℝ) * ‖(Real.sqrt n)⁻¹ • ∑ i, (wl_psiBand M L (X i) -
      ∫ y, wl_psiBand M L y ∂μ)‖ ^ 2 := by positivity
  have h2 := wl_k0_nonneg M
  linarith

/-- `𝖥_n^q ≥ -a` for a weak kernel with row bound `a` (every configuration, `n ≥ 1`). -/
lemma wl4b_energy_ge_neg_row {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
    {a : ℝ} {q : E → E → ℝ} (hq : EWeakKernel μ a q) (ha : 0 ≤ a) {n : ℕ} (hn : 1 ≤ n) (X : Fin n → E) :
    -a ≤ modEnergyE q X μ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold modEnergyE
  have hS : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hq.nonneg _ _
  have hR : ∑ i, ∫ y, q (X i) y ∂μ ≤ n * a := by
    calc ∑ i, ∫ y, q (X i) y ∂μ ≤ ∑ _i : Fin n, a :=
          Finset.sum_le_sum fun i _ => hq.wr1_rowInt_le ha (X i)
      _ = n * a := by simp
  have hI : 0 ≤ ∫ x, ∫ y, q x y ∂μ ∂μ := integral_nonneg fun x => hq.wr1_rowInt_nonneg x
  have h1 : 0 ≤ (1 / (2 * (n : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j) :=
    mul_nonneg (by positivity) hS
  have h2 : (1 / (n : ℝ)) * ∑ i, ∫ y, q (X i) y ∂μ ≤ a := by
    calc (1 / (n : ℝ)) * ∑ i, ∫ y, q (X i) y ∂μ ≤ (1 / (n : ℝ)) * (n * a) :=
          mul_le_mul_of_nonneg_left hR (by positivity)
      _ = a := by field_simp
  have h3 : 0 ≤ (1 / 2 : ℝ) * ∫ x, ∫ y, q x y ∂μ ∂μ := by positivity
  linarith

/-- The harmonic-type constant: `k0 L ≤ (1 + log L)/2`. -/
lemma wl4b_k0_le (L : ℕ) : wl_k0 L ≤ (1 / 2) * (1 + Real.log L) := by
  have h := harmonic_le_one_add_log L
  have e : ((harmonic L : ℚ) : ℝ) = ∑ j ∈ Finset.range L, 1 / ((j : ℝ) + 1) := by
    unfold harmonic
    push_cast
    simp
  rw [e] at h
  unfold wl_k0
  linarith

/-- `(L : ℝ) ≥ n^{2/d}` forces `n ≤ L^{d/2}`, so `L^{-(d/2)} ≤ 1/n`. -/
lemma wl4b_rpow_le (hd : 1 ≤ d) {n L : ℕ} (hn : 1 ≤ n) (hL : (n : ℝ) ^ ((2 : ℝ) / d) ≤ L) :
    (L : ℝ) ^ (-((d : ℝ) / 2)) ≤ 1 / (n : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnp : (0 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / d) := Real.rpow_nonneg hn0.le _
  have h1 : (n : ℝ) ≤ (L : ℝ) ^ ((d : ℝ) / 2) := by
    calc (n : ℝ) = ((n : ℝ) ^ ((2 : ℝ) / d)) ^ ((d : ℝ) / 2) := by
          rw [← Real.rpow_mul hn0.le]
          have : (2 : ℝ) / d * (d / 2) = 1 := by field_simp
          rw [this, Real.rpow_one]
      _ ≤ (L : ℝ) ^ ((d : ℝ) / 2) :=
          Real.rpow_le_rpow hnp hL (by positivity)
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hL
  rw [Real.rpow_neg hL0.le]
  rw [← one_div]
  exact one_div_le_one_div_of_le hn0 h1


/-- **`wl_energy_lower`** (weak entropy input).  For the tail kernel `q_M` and every injective configuration
`X` of `n ≥ 1` points, `-(C log(e n)) ≤ n 𝖥_n^{q_M}(X, μ)`, with `C = C(d, A, M)` uniform in `ρ`.
(Split `q_M = q_L + band(M, L]`, `L = max (M+1) ⌈n^{2/d}⌉`.) -/
theorem wl_energy_lower (hd : 2 ≤ d) (A : ℝ) (M : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ n : ℕ, 1 ≤ n → ∀ X : Fin n → Euc d,
      Function.Injective X →
      -(C * Real.log (Real.exp 1 * n)) ≤
        (n : ℝ) * HRS.Whole.pairEnergy (wl_qm M) X (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C1, hC10, hC1⟩ := wl_qm_weak hd A
  set cM : ℝ := Real.log (2 * ((M : ℝ) + 1)) with hcM
  have hcM0 : 0 ≤ cM := Real.log_nonneg (by have : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith)
  refine ⟨(1 / 4) * (1 + cM) + C1 + 1 / 4, by positivity, fun ρ hρ hA n hn X hX => ?_⟩
  haveI := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set L : ℕ := max (M + 1) ⌈(n : ℝ) ^ ((2 : ℝ) / d)⌉₊ with hLdef
  have hML : M ≤ L := le_trans (Nat.le_succ M) (le_max_left _ _)
  have hL1 : 1 ≤ L := le_trans (Nat.succ_le_succ (Nat.zero_le M)) (le_max_left _ _)
  have hLn : (n : ℝ) ^ ((2 : ℝ) / d) ≤ L :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have hq := hC1 ρ hρ hA L hL1
  have hrp : 0 ≤ (L : ℝ) ^ (-((d : ℝ) / 2)) := Real.rpow_nonneg (Nat.cast_nonneg L) _
  have ha : 0 ≤ C1 * (L : ℝ) ^ (-((d : ℝ) / 2)) := mul_nonneg hC10 hrp
  have hrow : C1 * (L : ℝ) ^ (-((d : ℝ) / 2)) ≤ C1 * (1 / (n : ℝ)) :=
    mul_le_mul_of_nonneg_left (wl4b_rpow_le (by omega) hn hLn) hC10
  have hat : ∀ x, μ {x} = 0 := wl_atomless (by omega) ρ
  have hinj : ∀ i j, i ≠ j → X i ≠ X j := fun i j hij h => hij (hX h)
  -- the split of the energy
  have hsplit : HRS.Whole.pairEnergy (wl_qm M) X μ =
      modEnergyE (fun x y => wl_qm L x y + wl_band M L x y) X μ := by
    refine modEnergyE_congr_offdiag hat (fun x y hxy => wl_qm_eq_qm_add_band M L hxy) X hinj
  have hadd := wr8_modEnergyE_add (N := n) (hq.rowOKE ha).wr8_ok (wl4b_band_wr8 (μ := μ) hML) X
  rw [hsplit, hadd]
  have h1 := wl4b_energy_ge_neg_row hq ha hn X
  have h2 := wl4b_band_energy (μ := μ) hML hn X
  have h3 := wl4b_k0_le L
  -- size of `L`
  have hLle : L ≤ 2 * (M + 1) * n := by
    refine max_le ?_ ?_
    · nlinarith [Nat.zero_le M]
    · have hc : ⌈(n : ℝ) ^ ((2 : ℝ) / d)⌉₊ ≤ 2 * n := by
        refine Nat.ceil_le.2 ?_
        have h2d : (2 : ℝ) / d ≤ 1 := by
          rw [div_le_one (by exact_mod_cast (by omega : 0 < d))]
          exact_mod_cast hd
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have := Real.rpow_le_rpow_of_exponent_le hn1 h2d
        rw [Real.rpow_one] at this
        push_cast
        linarith
      exact hc.trans (by nlinarith [Nat.zero_le M])
  have hlogL : Real.log L ≤ cM + Real.log n := by
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
    have : (L : ℝ) ≤ 2 * ((M : ℝ) + 1) * n := by exact_mod_cast hLle
    calc Real.log L ≤ Real.log (2 * ((M : ℝ) + 1) * n) := Real.log_le_log hLpos this
      _ = cM + Real.log n := by
        rw [Real.log_mul (by positivity) hn0.ne']
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hen : Real.log (Real.exp 1 * n) = 1 + Real.log n := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hn0.ne', Real.log_exp]
  rw [hen]
  have h4 : (n : ℝ) * (C1 * (L : ℝ) ^ (-((d : ℝ) / 2))) ≤ C1 := by
    calc (n : ℝ) * (C1 * (L : ℝ) ^ (-((d : ℝ) / 2))) ≤ n * (C1 * (1 / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hrow hn0.le
      _ = C1 := by field_simp
  have h5 : (n : ℝ) * (-(C1 * (L : ℝ) ^ (-((d : ℝ) / 2)))) ≤ (n : ℝ) * modEnergyE (wl_qm L) X μ :=
    mul_le_mul_of_nonneg_left h1 hn0.le
  have e : (n : ℝ) * (modEnergyE (wl_qm L) X μ + modEnergyE (wl_band M L) X μ) =
      (n : ℝ) * modEnergyE (wl_qm L) X μ + (n : ℝ) * modEnergyE (wl_band M L) X μ := by ring
  rw [e]
  have h2' : -((1 / 2) * wl_k0 L) ≤ (n : ℝ) * modEnergyE (wl_band M L) X μ := h2
  nlinarith [mul_nonneg hcM0 hlogn]


/-! ### Entropy of a tilted measure, with a Jensen lower bound for the normaliser -/

section Tilt

variable {α : Type*} [MeasurableSpace α]

/-- Adding a constant to the exponent does not change the tilted measure. -/
lemma wl4b_tilted_add_const (π : Measure α) (f : α → ℝ) (c : ℝ) :
    π.tilted (fun x => f x + c) = π.tilted f := by
  unfold Measure.tilted
  congr 1
  funext x
  have hI : ∫ y, Real.exp (f y + c) ∂π = (∫ y, Real.exp (f y) ∂π) * Real.exp c := by
    simp_rw [Real.exp_add]
    exact integral_mul_const _ _
  rw [hI, Real.exp_add]
  congr 1
  exact mul_div_mul_right _ _ (Real.exp_pos c).ne'

/-- **Entropy of an exponential tilt.**  If `f ≤ B` a.e. and `∫ f dπ ≥ -m` then
`KL(π tilted by f ‖ π) ≤ B + m` (Jensen: `∫ e^f dπ ≥ e^{-m}`; generalisation of `wr12_klDiv_tilted_le`). -/
theorem wl4b_klDiv_tilted_le (π : Measure α) [IsProbabilityMeasure π] {f : α → ℝ} (hf : Measurable f)
    {B m : ℝ} (hB : ∀ᵐ x ∂π, f x ≤ B) (hfi : Integrable f π) (hm : -m ≤ ∫ x, f x ∂π) :
    klDiv (π.tilted f) π ≤ ENNReal.ofReal (B + m) := by
  have hexp : Integrable (fun x => Real.exp (f x)) π :=
    Integrable.of_bound (Real.measurable_exp.comp hf).aestronglyMeasurable (Real.exp B) (by
      filter_upwards [hB] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 hx)
  have hj := ConvexOn.map_integral_le (μ := π) convexOn_exp Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hfi hexp
  have hZ : 1 ≤ ∫ x, Real.exp (f x + m) ∂π := by
    simp_rw [Real.exp_add]
    rw [integral_mul_const]
    have h1 : Real.exp (-m) ≤ ∫ x, Real.exp (f x) ∂π := (Real.exp_le_exp.2 hm).trans hj
    calc (1 : ℝ) = Real.exp (-m) * Real.exp m := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hexp' : Integrable (fun x => Real.exp (f x + m)) π := by
    simp_rw [Real.exp_add]
    exact hexp.mul_const _
  have := wr12_klDiv_tilted_le π (hf.add_const m) (B := B + m)
    (by filter_upwards [hB] with x hx; linarith) hexp' hZ
  rwa [wl4b_tilted_add_const] at this

end Tilt

/-! ### The field ensemble as an exponential tilt of `μ^{⊗n}` -/

section FieldTilt

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- **`fieldLaw` is the exponential tilt** of `μ^{⊗n}` by `y ↦ ∑ ψ (y i) - λ ∑_{i<j} q (y i, y j)`. -/
theorem wl4b_fieldLaw_eq_tilted {V : WeakPotential μ} {ψ : E → ℝ} {M M₁ lam : ℝ}
    (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) :
    fieldLaw V ψ lam n = (Measure.pi fun _ : Fin n => μ).tilted
      (fun y => ∑ i, ψ (y i) - lam * HRS.External.pairEnergy V y) := by
  set π : Measure (Fin n → E) := Measure.pi fun _ : Fin n => μ with hπ
  set f : (Fin n → E) → ℝ := fun y => ∑ i, ψ (y i) - lam * HRS.External.pairEnergy V y with hf
  have hfm : Measurable f :=
    (Finset.measurable_sum _ fun i _ => hψ.measurable.comp (measurable_pi_apply i)).sub
      ((measurable_pairEnergy V).const_mul _)
  have hfle : ∀ y, f y ≤ n * M := by
    intro y
    have h1 : ∑ i, ψ (y i) ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => hψ.le _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have h2 := mul_nonneg hlam (pairEnergy_nonneg V y)
    simp only [hf]
    linarith
  have hint : Integrable (fun y => Real.exp (f y)) π :=
    Integrable.of_bound (Real.measurable_exp.comp hfm).aestronglyMeasurable (Real.exp (n * M))
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (hfle y))
  have hZ : 0 < ∫ y, Real.exp (f y) ∂π := integral_exp_pos hint
  have hnorm : fieldNorm V ψ lam n = ENNReal.ofReal (∫ y, Real.exp (f y) ∂π) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)]
    rfl
  unfold fieldLaw Measure.tilted
  congr 1
  funext y
  unfold fieldDensity
  rw [hnorm, ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv]
  rfl

/-- The exponent of the field ensemble with the field `ψ = (nλ) q*μ + g`:
`∑ ψ(y_i) - λ ∑_{i<j} q = ∑ g(y_i) - λ n² 𝖥_n^q(y) + (λ n²/2) ∫∫ q`. -/
lemma wl4b_exponent_eq {q : E → E → ℝ} (V : WeakPotential μ) (hV : V.q = q) {n : ℕ} (hn : 1 ≤ n)
    (lam : ℝ) (g : E → ℝ) (y : Fin n → E) :
    ∑ i, (((n : ℝ) * lam) * rowIntE q μ (y i) + g (y i)) - lam * HRS.External.pairEnergy V y =
      (∑ i, g (y i) - lam * (n : ℝ) ^ 2 * modEnergyE q y μ) +
        lam * (n : ℝ) ^ 2 / 2 * ∫ x, ∫ z, q x z ∂μ ∂μ := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold HRS.External.pairEnergy modEnergyE rowIntE
  rw [hV, Finset.sum_add_distrib, ← Finset.mul_sum]
  field_simp
  ring

end FieldTilt


/-! ### Abstract entropy bound for the field ensemble -/

section KLField

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {a : ℝ}
  {q : E → E → ℝ}

/-- **Entropy of the weak field ensemble** (abstract form of `wl_klDiv`).  Let `q` be a weak kernel
(`EWeakKernel μ a q`), `V.q = q`, `g` a one-body field with `g ≤ G0`, `∫ g ≥ -m`, `λ ≥ 0`, `n ≥ 1`, and suppose
`n 𝖥_n^q ≥ -Aen` `μ^{⊗n}`-a.e. (`0 ≤ Aen`).  Then the ensemble with field `ψ = (nλ) q*μ + g` satisfies
`KL(fieldLaw V ψ λ n ‖ μ^{⊗n}) ≤ λ n Aen + n (G0 + m)`. -/
theorem wl4b_klDiv_field (hq : EWeakKernel μ a q) (ha : 0 ≤ a) (V : WeakPotential μ) (hV : V.q = q)
    {g : E → ℝ} {G0 m : ℝ} (hg : IsField μ g G0 m) {lam : ℝ} (hlam : 0 ≤ lam) {n : ℕ} (hn : 1 ≤ n)
    {Aen : ℝ} (hA0 : 0 ≤ Aen)
    (hA : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => μ), -Aen ≤ (n : ℝ) * modEnergyE q y μ) :
    klDiv (fieldLaw V (fun x => ((n : ℝ) * lam) * rowIntE q μ x + g x) lam n)
        (Measure.pi fun _ : Fin n => μ) ≤
      ENNReal.ofReal (lam * n * Aen + n * (G0 + m)) := by
  set π : Measure (Fin n → E) := Measure.pi fun _ : Fin n => μ with hπ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnl : 0 ≤ (n : ℝ) * lam := by positivity
  have hψ : IsField μ (fun x => ((n : ℝ) * lam) * rowIntE q μ x + g x)
      (((n : ℝ) * lam) * a + G0) (0 + m) := wl_isField_add (wl_isField_rowInt hq ha hnl) hg
  have hfe : (fun y : Fin n → E => ∑ i, (((n : ℝ) * lam) * rowIntE q μ (y i) + g (y i)) -
        lam * HRS.External.pairEnergy V y) =
      fun y => (∑ i, g (y i) - lam * (n : ℝ) ^ 2 * modEnergyE q y μ) +
        lam * (n : ℝ) ^ 2 / 2 * ∫ x, ∫ z, q x z ∂μ ∂μ :=
    funext (wl4b_exponent_eq V hV hn lam g)
  have hT : fieldLaw V (fun x => ((n : ℝ) * lam) * rowIntE q μ x + g x) lam n =
      π.tilted (fun y => (∑ i, g (y i) - lam * (n : ℝ) ^ 2 * modEnergyE q y μ) +
        lam * (n : ℝ) ^ 2 / 2 * ∫ x, ∫ z, q x z ∂μ ∂μ) :=
    (wl4b_fieldLaw_eq_tilted hψ hlam n).trans (congrArg π.tilted hfe)
  rw [hT, wl4b_tilted_add_const]
  have hokq : Wr8Ok μ q := (hq.rowOKE ha).wr8_ok
  have hEm : Measurable (fun y : Fin n → E => modEnergyE q y μ) := hq.wr12_measurable_energy n
  have hEi : Integrable (fun y : Fin n → E => modEnergyE q y μ) π := wr8_integrable_modEnergyE hokq
  have hgi : ∀ i : Fin n, Integrable (fun y : Fin n → E => g (y i)) π := fun i =>
    integrable_comp_eval (μ := fun _ : Fin n => μ) (i := i) hg.integrable
  have hgm : Measurable (fun y : Fin n → E => ∑ i, g (y i)) :=
    Finset.measurable_sum _ fun i _ => hg.measurable.comp (measurable_pi_apply i)
  have hsum_i : Integrable (fun y : Fin n → E => ∑ i, g (y i)) π := integrable_finsetSum _ fun i _ => hgi i
  have hP : 0 ≤ ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ) := integral_nonneg fun p => hq.nonneg _ _
  have hmean : ∫ y, (∑ i, g (y i) - lam * (n : ℝ) ^ 2 * modEnergyE q y μ) ∂π =
      n * (∫ x, g x ∂μ) + lam * n / 2 * ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ) := by
    rw [integral_sub hsum_i (hEi.const_mul _), integral_const_mul,
      integral_finsetSum _ fun i _ => hgi i, wr8_integral_modEnergyE hokq hn]
    have : ∀ i : Fin n, ∫ y : Fin n → E, g (y i) ∂π = ∫ x, g x ∂μ := fun i =>
      integral_comp_eval (μ := fun _ : Fin n => μ) (i := i) hg.integrable.aestronglyMeasurable
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hlow : -((n : ℝ) * m) ≤ ∫ y, (∑ i, g (y i) - lam * (n : ℝ) ^ 2 * modEnergyE q y μ) ∂π := by
    rw [hmean]
    have h1 : -m ≤ ∫ x, g x ∂μ := hg.ge
    have h2 : 0 ≤ lam * n / 2 * ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ) := by positivity
    nlinarith
  have hup : ∀ᵐ y ∂π, (∑ i, g (y i) - lam * (n : ℝ) ^ 2 * modEnergyE q y μ) ≤
      n * G0 + lam * n * Aen := by
    filter_upwards [hA] with y hy
    have h1 : ∑ i, g (y i) ≤ ∑ _i : Fin n, G0 := Finset.sum_le_sum fun i _ => hg.le _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have h2 : 0 ≤ (lam * n) * ((n : ℝ) * modEnergyE q y μ + Aen) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith
  have := wl4b_klDiv_tilted_le π (hgm.sub (hEm.const_mul _)) hup (hsum_i.sub (hEi.const_mul _)) hlow
  refine this.trans (le_of_eq ?_)
  congr 1
  ring

end KLField

end HRS.MS.Wl
