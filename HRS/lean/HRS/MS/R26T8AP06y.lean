import HRS.MS.R26T8AP06x
import HRS.MS.R26T8AP11lb

/-!
# S8.2 Taylor split (T), step B2d: pure remainder bound for the nested jets of `midPair F - Pfull`
For `F` with `Conormal (k+1+m+1) b M σ A F` (`σ < 0`, `m < -σ <= m+1`): the coefficient functions `c ℓ` of `r26t8a_taylor_coeff` (for `k+1`) satisfy,
for `p + q <= k`, `0 < |z| <= 1/2`:
`‖nest p q (midPair F - Pfull) X z‖ <= C A jb(X)^(2M) |z|^(-σ-q) (1+|log|z||)^b`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem r26t8a_taylor_remainder (hd : 2 ≤ d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ : ℝ)
    (hM : 0 ≤ M) (hσ : σ < 0) (m : ℕ) (hm : (m : ℝ) < -σ) (hm1 : -σ ≤ (m : ℝ) + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, Conormal (k + 1 + m + 1) b M σ A F →
      ∃ c : (ℓ : ℕ) → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ,
        (∀ ℓ ≤ m, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (c ℓ)) ∧
        (∀ ℓ ≤ m, ∀ p ≤ k + 1, ∀ Y : Euc d, ‖iteratedFDeriv ℝ p (c ℓ) Y‖ ≤ C * A * jbracket Y ^ (2 * M)) ∧
        ∀ p q : ℕ, p + q ≤ k → ∀ X z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
          ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2 - r26t8a_Pfull m c Yw.1 Yw.2) X z‖ ≤
            C * A * jbracket X ^ (2 * M) * ‖z‖ ^ (-σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ b := by
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  obtain ⟨C1, hC10, hB1⟩ := r26t8a_taylor_coeff hd hchi (k + 1) b M σ hM m hm
  have hw : ∀ p : ℕ, ∃ Cp : ℝ, 0 ≤ Cp ∧ (p ≤ k → ∀ A' : ℝ, 0 ≤ A' → ∀ (h : Euc d → ℝ)
      (Λ : (ℓ : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ),
      ContDiffOn ℝ ((k + m + 1 - p) + 1 : ℕ) h {z | z ≠ 0} →
      (∀ i ≤ (k + m + 1 - p) + 1, ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 →
        ‖iteratedFDeriv ℝ i h z‖ ≤ A' * r26t8a_jetEnvelope b (σ + i) ‖z‖) →
      (∀ ℓ ≤ m, Tendsto (fun z : Euc d => iteratedFDeriv ℝ ℓ h z) (𝓝[≠] (0 : Euc d)) (𝓝 (Λ ℓ))) →
      ∀ q ≤ (k + m + 1 - p) + 1, ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
        ‖iteratedFDeriv ℝ q (fun w : Euc d => h w - ∑ ℓ ∈ Finset.range (m + 1),
          (1 / (ℓ.factorial : ℝ)) * Λ ℓ (fun _ => w)) z‖ ≤
          Cp * A' * ‖z‖ ^ (-σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ b) := by
    intro p
    by_cases hp : p ≤ k
    · obtain ⟨C, hC0, hC⟩ := r26t8a_word_taylor hd b ((k + m + 1 - p) + 1) m σ hσ hm hm1 (by omega)
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hp⟩
  choose Cw hCw0 hCw using hw
  set Cs : ℝ := ∑ p ∈ Finset.range (k + 1), Cw p with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun p _ => hCw0 p
  have hCwle : ∀ p ≤ k, Cw p ≤ Cs := fun p hp =>
    Finset.single_le_sum (f := Cw) (fun i _ => hCw0 i) (Finset.mem_range.2 (by omega))
  refine ⟨C1 + 3 ^ (2 * M) * Cs, by positivity, ?_⟩
  intro A hA F hF
  obtain ⟨c, hc1, hc2, hc3⟩ := hB1 A hA F hF
  have hjb0 : ∀ X : Euc d, 0 ≤ jbracket X ^ (2 * M) := fun X => Real.rpow_nonneg (s83_jb_pos X).le _
  refine ⟨c, hc1, fun ℓ hℓ p hp Y => ?_, ?_⟩
  · refine (hc2 ℓ hℓ p hp Y).trans ?_
    have : 0 ≤ A * jbracket Y ^ (2 * M) := mul_nonneg hA (hjb0 Y)
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 3 ^ (2 * M)) hCs0) this]
  intro p q hpq X z hz hz1
  have hFK : Conormal ((k + m + 1) + 1) b M σ A F := by
    have e : k + 1 + m + 1 = (k + m + 1) + 1 := by omega
    rw [e] at hF; exact hF
  have hzpos : 0 < ‖z‖ := hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 hz
  have hpk : p ≤ k := by omega
  have hcd : ∀ ℓ ≤ m, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (c ℓ) := hc1
  have hPf : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) :=
    r26t8a_Pfull_contDiff m c hcd
  have hPf' : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) :=
    hPf.of_le (by exact_mod_cast (by omega : p + q ≤ k + 1))
  set R : ℝ := 2 * ‖z‖ with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hΨ : ContDiff ℝ ((k + m + 1 + 1 : ℕ) : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) :=
    r26t8a_gtilde_contDiff hchi hRpos hFK.1
  have hΨ' : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) :=
    hΨ.of_le (by exact_mod_cast (by omega : p + q ≤ k + m + 1 + 1))
  have hρ : 0 < ‖z‖ / 2 := by positivity
  have e1 : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2 - r26t8a_Pfull m c Yw.1 Yw.2) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2 -
        r26t8a_Pfull m c Yw.1 Yw.2) X z := by
    refine r26t8a_nest_congr_ball p q _ _ hρ X z (fun Y w hw => ?_)
    have h1 : ‖z‖ - ‖w‖ ≤ ‖z - w‖ := norm_sub_norm_le z w
    rw [norm_sub_rev] at h1
    have : R / 4 ≤ ‖w‖ := by rw [hR]; linarith
    simp only [r26t8a_psiCut_one hchi hRpos this, one_mul]
  have e2 := r26t8a_nest_sub p q z X hΨ' hPf'
  have e3 : r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) X z =
      mixedJet p q F X z := r26t8a_nest_gtilde hchi hRpos p q X z (by rw [hR]; linarith)
  rw [e1, e2, e3]
  -- the word functions
  set W : ℝ := 3 ^ (2 * M) * jbracket X ^ (2 * M) with hW
  have hW0 : 0 ≤ W := by rw [hW]; exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hjb0 X)
  have hB : 0 ≤ (C1 + 3 ^ (2 * M) * Cs) * A * jbracket X ^ (2 * M) * ‖z‖ ^ (-σ - (q : ℝ)) *
      (1 + |Real.log ‖z‖|) ^ b := by
    have := hjb0 X
    have h2 : 0 ≤ ‖z‖ ^ (-σ - (q : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    positivity
  refine ContinuousMultilinearMap.opNorm_le_bound hB fun u => ?_
  set h : Euc d → ℝ := fun z'' => r26t8a_iterDir ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
    (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (X, z'') with hh
  set Λ : (ℓ : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ :=
    fun ℓ => iteratedFDeriv ℝ p (c ℓ) X u with hΛ
  set Au : ℝ := A * W * ∏ i, ‖u i‖ with hAu
  have hAu0 : 0 ≤ Au := by rw [hAu]; exact mul_nonneg (mul_nonneg hA hW0) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hmid : ∀ i, p + i ≤ k + m + 1 + 1 → ∀ z0 : Euc d, z0 ≠ 0 →
      iteratedFDeriv ℝ i h z0 = (mixedJet p i F X z0) u := fun i hi z0 hz0' => by
    rw [hh]; exact r26t8a_nest_midPair_eq hchi hFK.1 (by omega) hz0' X u
  have hcdh : ContDiffOn ℝ ((k + m + 1 - p) + 1 : ℕ) h {z | z ≠ 0} := fun z0 hz0' => by
    rw [hh]; exact (r26t8a_contDiffAt_h hchi hFK.1 (by omega : p ≤ k + m + 1) hz0' X u).contDiffWithinAt
  have hjet : ∀ i ≤ (k + m + 1 - p) + 1, ∀ z0 : Euc d, 0 < ‖z0‖ → ‖z0‖ ≤ 1 →
      ‖iteratedFDeriv ℝ i h z0‖ ≤ Au * r26t8a_jetEnvelope b (σ + i) ‖z0‖ := by
    intro i hi z0 hz0 hz01
    have hz0' : z0 ≠ 0 := norm_pos_iff.1 hz0
    rw [hmid i (by omega) z0 hz0']
    have hb := hFK.2 p i (by omega) X z0 hz0'
    have hpw : pairWeight M (X + (1 / 2 : ℝ) • z0) (X - (1 / 2 : ℝ) • z0) ≤ W := by
      rw [hW]; exact r26t8a_p01_weight hM (by linarith)
    have henv : 0 ≤ r26t8a_jetEnvelope b (σ + i) ‖z0‖ := by
      unfold r26t8a_jetEnvelope; positivity
    calc ‖(mixedJet p i F X z0) u‖ ≤ ‖mixedJet p i F X z0‖ * ∏ j, ‖u j‖ := (mixedJet p i F X z0).le_opNorm u
      _ ≤ (A * pairWeight M (X + (1 / 2 : ℝ) • z0) (X - (1 / 2 : ℝ) • z0) * r26t8a_jetEnvelope b (σ + i) ‖z0‖) *
            ∏ j, ‖u j‖ := mul_le_mul_of_nonneg_right hb (Finset.prod_nonneg fun j _ => norm_nonneg _)
      _ ≤ (A * W * r26t8a_jetEnvelope b (σ + i) ‖z0‖) * ∏ j, ‖u j‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpw hA) henv)
            (Finset.prod_nonneg fun j _ => norm_nonneg _)
      _ = Au * r26t8a_jetEnvelope b (σ + i) ‖z0‖ := by rw [hAu]; ring
  have hlim : ∀ ℓ ≤ m, Tendsto (fun z' : Euc d => iteratedFDeriv ℝ ℓ h z') (𝓝[≠] (0 : Euc d)) (𝓝 (Λ ℓ)) := by
    intro ℓ hℓ
    refine (hc3 ℓ hℓ p (by omega) X u).congr' ?_
    filter_upwards [(eventually_mem_nhdsWithin : ∀ᶠ w in 𝓝[≠] (0 : Euc d), w ∈ ({0}ᶜ : Set (Euc d)))] with z' hz'
    exact (hmid ℓ (by omega) z' hz').symm
  set hP : Euc d → ℝ := fun w => ∑ ℓ ∈ Finset.range (m + 1), (1 / (ℓ.factorial : ℝ)) * Λ ℓ (fun _ => w) with hhP
  have hPcd : ContDiff ℝ (q : WithTop ℕ∞) hP := by
    refine ContDiff.sum fun ℓ _ => contDiff_const.mul ?_
    exact r26t8a_cmm_diag_contDiff (X := Euc d) ℓ (fun _ => Λ ℓ) (fun w => w) contDiff_const contDiff_id
  have hnestP : (r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) X z) u =
      iteratedFDeriv ℝ q hP z := by
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [r26t8a_nest_swap p q hPf' X z u v]
    have hfun : (fun z' : Euc d => r26t8a_iterDir ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
        (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) (X, z')) = hP := by
      funext z'
      have hlen : ContDiff ℝ (((List.ofFn u).length : ℕ) : WithTop ℕ∞)
          (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) := by
        rw [List.length_ofFn]; exact hPf.of_le (by exact_mod_cast (by omega : p ≤ k + 1))
      rw [r26t8a_iterDir_inl (List.ofFn u) hlen X z']
      have hcdY : ContDiff ℝ (p : WithTop ℕ∞) (fun Y : Euc d => r26t8a_Pfull m c Y z') :=
        (hPf.comp (contDiff_id.prodMk contDiff_const : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
          fun Y : Euc d => (Y, z'))).of_le (by exact_mod_cast (by omega : p ≤ k + 1))
      rw [← r26t8a_iteratedFDeriv_eq_iterDir p _ hcdY X u,
        r26t8a_Pfull_word m c (fun ℓ hℓ => (hcd ℓ hℓ).of_le (by exact_mod_cast (by omega : p ≤ k + 1))) X z' u]
    rw [hfun]
  have hhd : ContDiffAt ℝ (q : WithTop ℕ∞) h z :=
    (hcdh.contDiffAt (isOpen_ne.mem_nhds hz0)).of_le (by exact_mod_cast (by omega : q ≤ (k + m + 1 - p) + 1))
  have hsub : iteratedFDeriv ℝ q (fun w => h w - hP w) z = iteratedFDeriv ℝ q h z - iteratedFDeriv ℝ q hP z :=
    iteratedFDeriv_sub_apply (i := q) hhd hPcd.contDiffAt
  have hval : (mixedJet p q F X z - r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) X z) u =
      iteratedFDeriv ℝ q (fun w => h w - hP w) z := by
    rw [hsub, ContinuousMultilinearMap.sub_apply, ← hmid q (by omega) z hz0, hnestP]
  rw [hval]
  have hq' : q ≤ (k + m + 1 - p) + 1 := by omega
  have hbd := hCw p hpk Au hAu0 h Λ hcdh hjet hlim q hq' z hz hz1
  refine hbd.trans ?_
  have hZ : 0 ≤ ‖z‖ ^ (-σ - (q : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have hL : 0 ≤ (1 + |Real.log ‖z‖|) ^ b := by positivity
  have hprod : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hnn : 0 ≤ A * jbracket X ^ (2 * M) * ‖z‖ ^ (-σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ b * ∏ i, ‖u i‖ := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA (hjb0 X)) hZ) hL) hprod
  have h3 : (3 : ℝ) ^ (2 * M) * Cw p ≤ C1 + 3 ^ (2 * M) * Cs := by
    have : (3 : ℝ) ^ (2 * M) * Cw p ≤ 3 ^ (2 * M) * Cs :=
      mul_le_mul_of_nonneg_left (hCwle p hpk) (by positivity)
    linarith
  calc Cw p * Au * ‖z‖ ^ (-σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ b
      = (3 ^ (2 * M) * Cw p) * (A * jbracket X ^ (2 * M) * ‖z‖ ^ (-σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ b *
          ∏ i, ‖u i‖) := by rw [hAu, hW]; ring
    _ ≤ (C1 + 3 ^ (2 * M) * Cs) * (A * jbracket X ^ (2 * M) * ‖z‖ ^ (-σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ b *
          ∏ i, ‖u i‖) := mul_le_mul_of_nonneg_right h3 hnn
    _ = _ := by ring

end HRS.MS.R26T8A
