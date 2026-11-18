import HRS.Equilibrium.Parametrix.PX4aAuxM

/-!
# Packet PX4a auxiliaries N: smooth kernels from chart functions; finite-order smooth kernels are conormal

* `chartKer Q`: the torus kernel `(x, y) ↦ Q(rep y, rep x - rep y)` of a function `Q(Y, z)` that is
  lattice periodic in both variables (`lift2 (chartKer Q) = Q ∘ rightL`);
* `conormal_of_ck2`: a `C^M` doubly periodic kernel with `cbNorm2 ≤ N` is conormal of any order with
  constant `Cs * N` (multiplication of the smooth kernel `1` by `R`, `conormal_mul_smooth_aux`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The linear map `(x, y) ↦ (y, x - y)`. -/
def rightL (d : ℕ) : Euc d × Euc d →L[ℝ] Euc d × Euc d :=
  (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)).prod
    ((ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) - (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)))

lemma rightL_apply (p : Euc d × Euc d) : rightL d p = (p.2, p.1 - p.2) := rfl

lemma norm_rightL_le : ‖rightL d‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun p => ?_
  rw [rightL_apply, Prod.norm_def]
  have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  have := norm_nonneg p
  refine max_le ?_ ?_
  · show ‖p.2‖ ≤ 2 * ‖p‖
    linarith
  · show ‖p.1 - p.2‖ ≤ 2 * ‖p‖
    calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
      _ ≤ _ := by linarith

/-- The torus kernel of a chart function. -/
def chartKer (Q : Euc d × Euc d → ℝ) : Torus d → Torus d → ℝ :=
  fun x y => Q (Torus.rep y, Torus.rep x - Torus.rep y)

lemma isLat_sub {a b : Euc d} (ha : IsLat a) (hb : IsLat b) : IsLat (a - b) := by
  intro i
  obtain ⟨k, hk⟩ := ha i
  obtain ⟨l, hl⟩ := hb i
  exact ⟨k - l, by simp [hk, hl]⟩

lemma lift2_chartKer {Q : Euc d × Euc d → ℝ}
    (hY : ∀ Y z n : Euc d, IsLat n → Q (Y + n, z) = Q (Y, z))
    (hZ : ∀ Y z n : Euc d, IsLat n → Q (Y, z + n) = Q (Y, z)) :
    lift2 (chartKer Q) = fun p => Q (rightL d p) := by
  funext p
  obtain ⟨k1, hk1, e1⟩ := rep_exists_lat p.1
  obtain ⟨k2, hk2, e2⟩ := rep_exists_lat p.2
  show Q (Torus.rep (Torus.mk p.2), Torus.rep (Torus.mk p.1) - Torus.rep (Torus.mk p.2)) = Q (p.2, p.1 - p.2)
  rw [e1, e2]
  have : p.1 + k1 - (p.2 + k2) = (p.1 - p.2) + (k1 - k2) := by abel
  rw [this, hY _ _ _ hk2, hZ _ _ _ (isLat_sub hk1 hk2)]

lemma isCk2_chartKer {Q : Euc d × Euc d → ℝ} {M : ℕ}
    (hQ : ContDiff ℝ (M : WithTop ℕ∞) Q)
    (hY : ∀ Y z n : Euc d, IsLat n → Q (Y + n, z) = Q (Y, z))
    (hZ : ∀ Y z n : Euc d, IsLat n → Q (Y, z + n) = Q (Y, z)) :
    PDE.IsCk2 M (chartKer Q) := by
  unfold PDE.IsCk2
  have : PDE.lift2 (chartKer Q) = fun p => Q (rightL d p) := lift2_chartKer hY hZ
  rw [this]
  exact hQ.comp (rightL d).contDiff

lemma cbNorm2_chartKer_le {Q : Euc d × Euc d → ℝ} {M : ℕ}
    (hQ : ContDiff ℝ (M : WithTop ℕ∞) Q)
    (hY : ∀ Y z n : Euc d, IsLat n → Q (Y + n, z) = Q (Y, z))
    (hZ : ∀ Y z n : Euc d, IsLat n → Q (Y, z + n) = Q (Y, z)) {N : ℕ → ℝ}
    (hN : ∀ j ≤ M, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j Q p‖ ≤ N j) :
    PDE.cbNorm2 M (chartKer Q) ≤ ∑ j ∈ Finset.range (M + 1), 2 ^ j * N j := by
  have hl : PDE.lift2 (chartKer Q) = fun p => Q (rightL d p) := lift2_chartKer hY hZ
  unfold PDE.cbNorm2
  refine Finset.sum_le_sum fun j hj => ?_
  have hjM : j ≤ M := by have := Finset.mem_range.mp hj; omega
  have hN0 : 0 ≤ N j := (norm_nonneg _).trans (hN j hjM 0)
  refine ciSup_le fun p => ?_
  rw [hl]
  have h := (rightL d).iteratedFDeriv_comp_right hQ p (i := j) (by exact_mod_cast hjM)
  change ‖iteratedFDeriv ℝ j (Q ∘ rightL d) p‖ ≤ _
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h2 : ∏ _i : Fin j, ‖rightL d‖ ≤ 2 ^ j := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) norm_rightL_le j
  calc _ ≤ N j * 2 ^ j := mul_le_mul (hN j hjM _) h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) hN0
    _ = _ := by ring

/-- A `C^M` kernel (`IsCk2`) with `cbNorm2 ≤ N` is conormal of any order and log index. -/
theorem conormal_of_ck2 (σ : ℝ) (b : ℕ → ℕ) (M : ℕ) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (R : Torus d → Torus d → ℝ), PDE.IsCk2 M R → ∀ N : ℝ,
      PDE.cbNorm2 M R ≤ N → ConormalL σ b M (Cs * N) R := by
  obtain ⟨Cm, hCm0, hCm⟩ := conormal_mul_smooth_aux (d := d) M σ (fun _ => 0)
  have hone : ConormalL σ (fun _ => 0) M (∑ k ∈ Finset.range (M + 1), (2 : ℝ) ^ k * 1)
      (fun _ _ : Torus d => (1 : ℝ)) :=
    conormal_of_smooth_kernel σ (fun _ => 0) M (a := fun _ _ : Torus d => (1 : ℝ))
      (by exact contDiff_const) (fun _ => 1) (fun k p => by
        have := norm_iteratedFDeriv_const_le (d := d) 1 k p
        have e : lift2 (fun _ _ : Torus d => (1 : ℝ)) = fun _ => (1 : ℝ) := rfl
        rw [e]
        simpa using this)
  set B1 : ℝ := ∑ k ∈ Finset.range (M + 1), (2 : ℝ) ^ k * 1 with hB1
  have hB10 : 0 ≤ B1 := Finset.sum_nonneg fun k _ => by positivity
  refine ⟨Cm * B1, by positivity, fun R hR N hN => ?_⟩
  have hmul := hCm B1 (fun _ _ => 1) R hone hR
  have hsup : (fun c : ℕ => (Finset.range (c + 1)).sup (fun _ : ℕ => (0 : ℕ))) = fun _ => 0 := by
    funext c; simp
  rw [hsup] at hmul
  have hRfun : (fun x y => R x y * (fun _ _ : Torus d => (1 : ℝ)) x y) = R := by
    funext x y; simp
  rw [hRfun] at hmul
  have hcb0 : 0 ≤ PDE.cbNorm2 M R := PDE.MFPair.cbNorm2_nonneg M R
  have h1 : ConormalL σ b M (Cm * PDE.cbNorm2 M R * B1) R :=
    conormalL_mono_b (by positivity) (fun c => Nat.zero_le _) hmul
  refine conormalL_mono_B h1 (by positivity) ?_
  have : Cm * PDE.cbNorm2 M R * B1 ≤ Cm * N * B1 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hCm0) hB10
  calc _ ≤ Cm * N * B1 := this
    _ = Cm * B1 * N := by ring

/-! ### The far convolution `∫_{cube} g(w) S(Y, z - w) dw` -/

/-- The periodic Riesz kernel on `ℝ^d`. -/
def ghat (d : ℕ) (s : ℝ) (w : Euc d) : ℝ := periodicRiesz d s (Torus.mk w)

lemma measurable_ghat (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) : Measurable (ghat d s) :=
  (CoercAux.measurable_periodicRiesz_one (by omega) hs0 hsd).comp
    (by
      have : Measurable (Torus.mk : Euc d → Torus d) := (LocalDivAux.mk_measurePreserving (d := d)).measurable
      exact this)

lemma integrable_ghat_cube (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (ghat d s) (volume.restrict (LocalDivAux.cube d)) := by
  have hmp := LocalDivAux.mk_measurePreserving (d := d)
  have hI : Integrable (periodicRiesz d s) (volume : Measure (Torus d)) :=
    integrable_periodicRiesz_one_le (by omega) hs0 hsd
  exact (hmp.integrable_comp hI.aestronglyMeasurable).mpr hI

/-- The far convolution. -/
def farConv (d : ℕ) (s : ℝ) (S : Euc d × Euc d → ℝ) (p : Euc d × Euc d) : ℝ :=
  ∫ w in LocalDivAux.cube d, ghat d s w * S (p.1, p.2 - w)

lemma iteratedFDeriv_shiftS {S : Euc d × Euc d → ℝ} {M : ℕ} (hS : ContDiff ℝ (M : WithTop ℕ∞) S)
    (c : ℝ) (w : Euc d) {k : ℕ} (hk : k ≤ M) (p0 : Euc d × Euc d) :
    iteratedFDeriv ℝ k (fun p : Euc d × Euc d => c * S (p.1, p.2 - w)) p0 =
      c • iteratedFDeriv ℝ k S (p0.1, p0.2 - w) := by
  have hS' : ContDiff ℝ (M : WithTop ℕ∞) (fun q : Euc d × Euc d => S (q + ((0 : Euc d), -w))) :=
    hS.comp (contDiff_id.add contDiff_const)
  have hat : ContDiffAt ℝ (k : WithTop ℕ∞) (fun q : Euc d × Euc d => S (q + ((0 : Euc d), -w))) p0 :=
    hS'.contDiffAt.of_le (by exact_mod_cast hk)
  have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := c) hat
  have e2 : (fun p : Euc d × Euc d => c * S (p.1, p.2 - w)) =
      fun p => c • (fun q => S (q + ((0 : Euc d), -w))) p := by
    funext p
    show c * S (p.1, p.2 - w) = c * S (p + ((0 : Euc d), -w))
    rw [px3a_add_zero_neg]
  rw [e2, this, iteratedFDeriv_comp_add_right, px3a_add_zero_neg]

theorem farConv_smooth (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M : ℕ} {S : Euc d × Euc d → ℝ}
    (hS : ContDiff ℝ (M : WithTop ℕ∞) S) {N : ℕ → ℝ}
    (hN : ∀ j ≤ M, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j S p‖ ≤ N j) :
    ContDiff ℝ (M : WithTop ℕ∞) (farConv d s S) ∧
    (∀ j ≤ M, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (farConv d s S) p‖ ≤
      (∫ w in LocalDivAux.cube d, |ghat d s w|) * N j) ∧
    (∀ j ≤ M, ∀ p : Euc d × Euc d, iteratedFDeriv ℝ j (farConv d s S) p =
      ∫ w in LocalDivAux.cube d, ghat d s w • iteratedFDeriv ℝ j S (p.1, p.2 - w)) ∧
    (∀ j ≤ M, ∀ p : Euc d × Euc d, Integrable (fun w => ghat d s w • iteratedFDeriv ℝ j S (p.1, p.2 - w))
      (volume.restrict (LocalDivAux.cube d))) := by
  have hgm := measurable_ghat hd hs0 hsd
  have hgi := integrable_ghat_cube hd hs0 hsd
  have hH : ParamHyp (E := Euc d × Euc d) M
      (fun (p : Euc d × Euc d) (w : Euc d) => ghat d s w * S (p.1, p.2 - w))
      (volume.restrict (LocalDivAux.cube d)) := by
    refine ⟨Eventually.of_forall fun w => ?_, fun k hk p0 => ?_, fun k hk => ?_⟩
    · exact contDiff_const.mul (hS.comp (by fun_prop))
    · have e : (fun w => iteratedFDeriv ℝ k (fun p : Euc d × Euc d => ghat d s w * S (p.1, p.2 - w)) p0) =
          fun w => ghat d s w • iteratedFDeriv ℝ k S (p0.1, p0.2 - w) := by
        funext w; exact iteratedFDeriv_shiftS hS _ w hk p0
      rw [e]
      have hc : Continuous fun w : Euc d => iteratedFDeriv ℝ k S (p0.1, p0.2 - w) :=
        (hS.continuous_iteratedFDeriv (by exact_mod_cast hk)).comp (by fun_prop)
      exact hgm.aestronglyMeasurable.smul hc.aestronglyMeasurable
    · refine ⟨fun w => |ghat d s w| * N k, hgi.norm.mul_const _, ?_⟩
      refine Eventually.of_forall fun w p => ?_
      rw [iteratedFDeriv_shiftS hS _ w hk p, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((hN k hk _)) (abs_nonneg _)
  obtain ⟨h1, h2⟩ := contDiff_integral_param_aux M _ hH
  have hform : ∀ j ≤ M, ∀ p : Euc d × Euc d, iteratedFDeriv ℝ j (farConv d s S) p =
      ∫ w in LocalDivAux.cube d, ghat d s w • iteratedFDeriv ℝ j S (p.1, p.2 - w) := by
    intro j hj p
    show iteratedFDeriv ℝ j (fun p' => ∫ w, ghat d s w * S (p'.1, p'.2 - w) ∂(volume.restrict (LocalDivAux.cube d))) p = _
    rw [h2 j hj p]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    exact iteratedFDeriv_shiftS hS _ w hj p
  have hintg : ∀ j ≤ M, ∀ p : Euc d × Euc d, Integrable (fun w => ghat d s w • iteratedFDeriv ℝ j S (p.1, p.2 - w))
      (volume.restrict (LocalDivAux.cube d)) := by
    intro j hj p
    have hc : Continuous fun w : Euc d => iteratedFDeriv ℝ j S (p.1, p.2 - w) :=
      (hS.continuous_iteratedFDeriv (by exact_mod_cast hj)).comp (by fun_prop)
    refine Integrable.mono' (hgi.norm.mul_const (N j))
      (hgm.aestronglyMeasurable.smul hc.aestronglyMeasurable) (Eventually.of_forall fun w => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hN j hj _) (abs_nonneg _)
  refine ⟨h1, fun j hj p => ?_, hform, hintg⟩
  show ‖iteratedFDeriv ℝ j (fun p' => ∫ w, ghat d s w * S (p'.1, p'.2 - w) ∂(volume.restrict (LocalDivAux.cube d))) p‖ ≤ _
  rw [h2 j hj p]
  have hint := hgi.norm.mul_const (N j)
  calc ‖∫ w, iteratedFDeriv ℝ j (fun p' : Euc d × Euc d => ghat d s w * S (p'.1, p'.2 - w)) p
        ∂(volume.restrict (LocalDivAux.cube d))‖
      ≤ ∫ w, |ghat d s w| * N j ∂(volume.restrict (LocalDivAux.cube d)) := by
        refine norm_integral_le_of_norm_le (hint.congr (Eventually.of_forall fun w => by simp)) ?_
        refine Eventually.of_forall fun w => ?_
        rw [iteratedFDeriv_shiftS hS _ w hj p, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hN j hj _) (abs_nonneg _)
    _ = (∫ w in LocalDivAux.cube d, |ghat d s w|) * N j := by
        rw [integral_mul_const]

end HRS.Parx

end
