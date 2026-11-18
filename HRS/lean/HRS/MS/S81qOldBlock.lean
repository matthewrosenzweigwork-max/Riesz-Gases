import HRS.MS.S81qCoupling
import HRS.MS.FinNoiseAux15
import HRS.MS.S81qOldCost
import HRS.MS.S81pReturn
import HRS.MS.S81pInitial
import HRS.Main.GFB3Aux6

/-!
# S8.1 (worker S81Q): the old block of the burn-in coupling

Namespace `HRS.Whole.S81Q`, prefix `s81q_`.

Generic pieces: measurability of coordinatewise defined `ℓ²`-vectors (`s81q_ofSeq_meas`), coordinate functionals of a path-valued linear map
(`s81q_path_coord_clm`), existence of the Hilbert Itô integral of a Hilbert-Schmidt integrand (`s81q_exists_M`).
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
open HRS HRS.Whole HRS.MS.SuppU11 HRS.MS.Spec HRS.Whole.S81P HRS.Whole.S81W2

namespace HRS.Whole.S81Q

section Generic

/-- A coordinatewise defined `ℓ²`-vector (junk `0` where the series diverges) is measurable. -/
theorem s81q_ofSeq_meas {Ω : Type*} [MeasurableSpace Ω] (c : ℕ → Ω → ℝ) (hc : ∀ l, Measurable (c l)) :
    Measurable fun ω => SeqL2.ofSeq fun l => c l ω := by
  classical
  have hf : ∀ l : ℕ, Measurable (fun ω => (c l ω) ^ 2) := fun l => (hc l).pow_const 2
  have hSm : MeasurableSet {ω | Summable fun l => (c l ω) ^ 2} :=
    HRS.Q41.q41_measurableSet_summable (fun (l : ℕ) (ω : Ω) => (c l ω) ^ 2) hf (fun l ω => sq_nonneg _)
  refine HRS.measurable_of_inner_basis S45.s45_seqBasis fun i => ?_
  have e : (fun ω => inner ℝ (S45.s45_seqBasis i) (SeqL2.ofSeq fun l => c l ω)) =
      fun ω => if Summable (fun l => (c l ω) ^ 2) then c i ω else 0 := by
    funext ω
    rw [S45.s45_inner_seqBasis]
    by_cases hs : Summable fun l => (c l ω) ^ 2
    · rw [if_pos hs]; exact u11_coord_ofSeq (memℓp_two_iff.2 hs) i
    · rw [if_neg hs]
      have : ¬ Memℓp (fun l => c l ω) 2 := fun h => hs (memℓp_two_iff.1 h)
      have h0 : SeqL2.ofSeq (fun l => c l ω) = 0 := by unfold SeqL2.ofSeq; exact dif_neg this
      rw [h0]; rfl
  rw [e]
  exact Measurable.ite hSm (hc i) measurable_const

/-- The coordinate functionals of a path-valued continuous linear map. -/
theorem s81q_path_coord_clm {d : ℕ} {m T : ℝ} (R : SeqL2 →L[ℝ] OscPath d m T) (t : Set.Icc (0 : ℝ) T)
    (α : MultiIndex d) :
    ∃ L : SeqL2 →L[ℝ] ℝ, ∀ z, L z = OscDual.coord (OscPath.at' (R z) t) α := by
  refine ⟨LinearMap.mkContinuous
    { toFun := fun z => OscDual.coord (OscPath.at' (R z) t) α
      map_add' := fun z z' => by
        have : OscPath.at' (R (z + z')) t = OscPath.at' (R z) t + OscPath.at' (R z') t := by
          rw [map_add]; rfl
        simp only [this, OscDual.coord_add]
      map_smul' := fun c z => by
        have : OscPath.at' (R (c • z)) t = c • OscPath.at' (R z) t := by
          rw [map_smul]; rfl
        simp only [this, OscDual.coord_smul, RingHom.id_apply, smul_eq_mul] } ‖R‖ (fun z => ?_),
    fun z => rfl⟩
  show |OscDual.coord (OscPath.at' (R z) t) α| ≤ ‖R‖ * ‖z‖
  have h1 : |OscDual.coord (OscPath.at' (R z) t) α| ≤ ‖OscPath.at' (R z) t‖ := by
    have := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
      (show lp (fun _ : MultiIndex d => ℝ) 2 from OscPath.at' (R z) t) α
    rw [Real.norm_eq_abs] at this
    exact this
  have h2 : ‖OscPath.at' (R z) t‖ ≤ ‖R z‖ := ContinuousMap.norm_coe_le_norm (R z : C(Set.Icc (0 : ℝ) T, OscDual d m)) t
  exact h1.trans (h2.trans (R.le_opNorm z))

end Generic

section Existence

/-- The Hilbert Itô integral of a Hilbert-Schmidt integrand exists (continuous version). -/
theorem s81q_exists_M {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) {κ : Type} [Countable κ] (W : ℝ≥0 → Ω → κ → ℝ)
    (hW : IsCylindricalBrownian P ℱ W) {Φ : ℝ → Ω → κ → SeqL2} (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) :
    ∃ M : ℝ → Ω → SeqL2, IsHilbertItoIntegral P ℱ W Φ M := by
  obtain ⟨Mart, hc, had, hz, hJ⟩ := HRS.GF.gfb3_exists_hilbert_version hW hΦ
  refine ⟨Mart, ⟨hc, had, hz, ?_⟩⟩
  intro τ hτ x
  obtain ⟨J, hIJ, hae⟩ := hJ x
  refine (hIJ.approx τ hτ).congr fun s => ?_
  refine lintegral_congr_ae ?_
  filter_upwards [hae τ hτ] with ω h
  rw [h]
  rfl

end Existence

/-- The spectral empirical noise integrand of the old block. -/
def s81q_Phi {Ω : Type*} (d N : ℕ) (β τ : ℝ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) : ℝ → Ω → (Fin N × Fin d) → SeqL2 := fun r z ia =>
  Real.sqrt (2 / (N * β)) • SeqL2.ofSeq (fun l =>
    Real.exp (-(τ * om l) / 2) * gradient (e l) (X (Real.toNNReal r) z ia.1) ia.2)

theorem s81q_enorm_add_sq_le {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have h1 : ∀ z : E, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [h1, h1, h1, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [norm_add_le x y, norm_nonneg x, norm_nonneg y, norm_nonneg (x + y),
    sq_nonneg (‖x‖ - ‖y‖)]

set_option maxHeartbeats 1600000 in
/-- **The old block.** -/
theorem s81q_old_block {d : ℕ} (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {e : ℕ → Euc d → ℝ} {om : ℕ → ℝ}
    (hdata : IsSpectralData d β ρβ e om) {t₀ : ℝ} (ht₀ : 0 < t₀) {C4 : ℝ}
    (hL4 : ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (withDensityReal ρβ) ≤
      ENNReal.ofReal (C4 * Real.exp (t₀ * om l)))
    {τ : ℝ} (hτ : 4 * t₀ < τ) {b : ℝ} (hb : τ / 2 + 1 < b) {m : ℝ}
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) {T : ℝ} (hT : 0 < T) :
    ∃ (R : SeqL2 →L[ℝ] OscPath d m T) (K : ℝ),
      (∀ (z : SeqL2) (t : Set.Icc (0 : ℝ) T),
        OscPath.at' (R z) t = returnMapW d β ρβ e om m τ b z t) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
        ∀ ℱ : Filtration ℝ mΩ,
          IsCylindricalBrownian P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) →
          (∀ i : Fin N, IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i)) →
          ∀ h : ℝ, 0 ≤ h →
          ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
            (ℱ' : Filtration ℝ mΩ') (B : ℝ≥0 → Ω' → ℕ → ℝ) (Yg Yn : Ω' → SeqL2)
            (Op G1 : ℝ → Ω' → OscDual d m),
            IsProbabilityMeasure P' ∧ MeasurePreserving π P' P ∧ (∀ s, (ℱ s).comap π ≤ ℱ' s) ∧
            IsCylindricalBrownian P' ℱ' B ∧ Indep ((ℱ 0).comap π) (cylindricalPathSigma B) P' ∧
            IsCylindricalBrownian P' ℱ' (fun t w (ia : Fin N × Fin d) => W t (π w) ia.1 ia.2) ∧
            Measurable[ℱ' h] Yg ∧ Measurable[ℱ' h] Yn ∧ IsCenteredGaussian (law P' Yg) ∧
            (∀ x y, covarianceBilin (law P' Yg) x y =
              ∑' l, s81q_sOld β τ h om l * SeqL2.coord x l * SeqL2.coord y l) ∧
            Indep (ℱ' 0) (MeasurableSpace.comap Yg inferInstance) P' ∧
            (∀ t, @Measurable Ω' (OscDual d m) (ℱ' h) _ (G1 t)) ∧
            S81PProc P' T Op ∧ S81PProc P' T G1 ∧
            (∀ ζ, processWindow m T 0 Op ζ = R (Yn ζ)) ∧
            (∀ ζ, processWindow m T 0 G1 ζ = R (Yg ζ)) ∧
            s81p_L2 P' (fun ζ => processWindow m T 0 Op ζ - processWindow m T 0 G1 ζ) ≤
              ENNReal.ofReal (K * ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N)) ∧
            (∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) →
              P'.map (s81p_vec G1 ts αs) = multivariateGaussian 0 (Matrix.of fun i j =>
                s81w2_Q d β ρβ e om m (αs i) (αs j) (2 * b + ts i + ts j) -
                  s81w2_Q d β ρβ e om m (αs i) (αs j) (2 * (b + h) + ts i + ts j))) ∧
            (∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) →
              (Matrix.of fun i j =>
                s81w2_Q d β ρβ e om m (αs i) (αs j) (2 * b + ts i + ts j) -
                  s81w2_Q d β ρβ e om m (αs i) (αs j) (2 * (b + h) + ts i + ts j)).PosSemidef) ∧
            ∫⁻ w, ‖Yn w‖ₑ ^ 2 ∂P' ≠ ⊤ ∧
            (∀ l : ℕ, ∃ JW : ℝ → Ω' → ℝ,
              IsCtbl P' ℱ' (fun r w (ia : Fin N × Fin d) => s81q_fcl om h l r *
                inner ℝ (s81q_Phi d N β τ e om X r (π w) ia) (S45.s45_seqBasis l)) ∧
              IsItoC P' ℱ' (fun t w (ia : Fin N × Fin d) => W t (π w) ia.1 ia.2)
                (fun r w ia => s81q_fcl om h l r *
                  inner ℝ (s81q_Phi d N β τ e om X r (π w) ia) (S45.s45_seqBasis l)) JW ∧
              (fun w => SeqL2.coord (Yn w) l) =ᵐ[P'] JW h) := by
  classical
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hτ0 : 0 < τ := by linarith [ht₀]
  have hom : ∀ l, 0 < om l := hdata.pos
  have hmono : Monotone om := hdata.mono
  obtain ⟨R, hR⟩ := s81p_return_clm hd a β ha hβ ρβ hρ e om hdata t₀ ht₀ C4 hL4 τ hτ b hb m hm T hT
  obtain ⟨C, hC⟩ := s81q_coupling_claim hd ha hβ hρ hdata ht₀ hL4 hτ
  have hdv : Summable (s8p_dv β om τ) := by
    obtain ⟨c, hc, hgrowth⟩ := hdata.growth
    have hmul := s8p_summable_mul_exp_growth (by omega : 1 ≤ d) hc
      (fun l : ℕ => (hgrowth l)) (fun l => (hom l).le) hτ0
    refine (hmul.mul_left (2 * β⁻¹)).congr fun l => ?_
    unfold s8p_dv; ring
  refine ⟨R, ‖R‖ * Real.sqrt (max C 0 / (2 * om 0)), hR, ?_⟩
  intro N hN Ω _ P _ X₀ W X hreal ℱ hW hprog h hh
  obtain ⟨hgood, hΦ, hrest⟩ := hC N hN P X₀ W X hreal ℱ hW hprog
  obtain ⟨M, hM⟩ := s81q_exists_M P ℱ _ hW hΦ
  obtain ⟨Cdet, hCdet, Ω', mΩ', P', π, ℱ', B, S, Sb, G0, hcoup, hbound, hDb, hWb, hprogS, hHSS, hind,
    hSbm⟩ := hrest h hh M hM
  haveI hP' : IsProbabilityMeasure P' := hcoup.prob
  have hπ : MeasurePreserving π P' P := hcoup.preserving
  have hfil := hcoup.filtration
  have hB : IsCylindricalBrownian P' ℱ' B := hcoup.brownian
  have hπm : ∀ s, Measurable[ℱ' s, ℱ s] π := fun s => Measurable.of_comap_le (hfil s)
  have hSb : ∀ r ∈ Set.Icc (0 : ℝ) h, IsSqrtOfForm (Sb r) (s8p_Cdet hβ hom hτ0) := by
    intro r hr
    have h1 := hcoup.sqrtSb r hr
    have e : Cdet r = s8p_Cdet hβ hom hτ0 := by
      refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
      rw [hCdet r hr u v, s8p_Cdet_apply]
    rw [e] at h1; exact h1
  obtain ⟨G, Js, hGad, hGg, hGcov, hGind, hJs, hcost⟩ := s81q_old_cost hβ hom hmono hτ0 hdv hh P' ℱ'
    S45.s45_seqBasis hB (fun r w => S r (π w)) hprogS hHSS Sb hSb ENNReal.ofReal_ne_top hbound
  -- the vectors
  set Z : ℝ≥0∞ := ENNReal.ofReal (C * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2)) with hZ
  set Yg : Ω' → SeqL2 := G h with hYg
  set Δ : Ω' → SeqL2 := fun w => SeqL2.ofSeq fun l => Js l h w - SeqL2.coord (Yg w) l with hΔ
  set Yn : Ω' → SeqL2 := fun w => Yg w + Δ w with hYn
  have hJm : ∀ l, Measurable[ℱ' h] (Js l h) := fun l => (hJs l).adapted h
  have hYgm : Measurable Yg := hGad.mono (ℱ'.le h) le_rfl
  have hΔad : Measurable[ℱ' h] Δ :=
    @s81q_ofSeq_meas Ω' (ℱ' h) (fun l w => Js l h w - SeqL2.coord (Yg w) l) fun l =>
      (hJm l).sub (@s8p_coord_measurable Ω' (ℱ' h) Yg hGad l)
  have hΔm : Measurable Δ := hΔad.mono (ℱ'.le h) le_rfl
  have hYnad : Measurable[ℱ' h] Yn := hGad.add hΔad
  have hYnm : Measurable Yn := hYnad.mono (ℱ'.le h) le_rfl
  -- the coordinates of `Δ`
  have hsq : ∀ᵐ w ∂P', Summable fun l => (Js l h w - SeqL2.coord (Yg w) l) ^ 2 := by
    have h1 : ∫⁻ w, ∑' l, ENNReal.ofReal ((Js l h w - SeqL2.coord (Yg w) l) ^ 2) ∂P' ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := Z * ENNReal.ofReal (1 / (2 * om 0)))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ?_
      refine le_trans (le_of_eq ?_) hcost
      simp_rw [s8p_enorm_sq_eq]
    have h2 : ∀ᵐ w ∂P', ∑' l, ENNReal.ofReal ((Js l h w - SeqL2.coord (Yg w) l) ^ 2) < ⊤ := by
      refine ae_lt_top ?_ h1
      refine Measurable.ennreal_tsum fun l => ENNReal.measurable_ofReal.comp ?_
      exact (((hJm l).mono (ℱ'.le h) le_rfl).sub (s8p_coord_measurable hYgm l)).pow_const 2
    filter_upwards [h2] with w hw
    exact s81p_summable_of_tsum_ne_top (fun l => sq_nonneg _) hw.ne
  have hΔc : ∀ᵐ w ∂P', ∀ l, SeqL2.coord (Δ w) l = Js l h w - SeqL2.coord (Yg w) l := by
    filter_upwards [hsq] with w hw l
    exact u11_coord_ofSeq (memℓp_two_iff.2 hw) l
  have hΔint : ∫⁻ w, ‖Δ w‖ₑ ^ 2 ∂P' ≤ Z * ENNReal.ofReal (1 / (2 * om 0)) := by
    refine le_trans (le_of_eq ?_) hcost
    refine lintegral_congr_ae ?_
    filter_upwards [hΔc, hsq] with w hw hs
    rw [s8p_seq_enorm_sq]
    refine tsum_congr fun l => ?_
    rw [hw l, s8p_enorm_sq_eq]
  -- the processes
  have hRYn : Measurable fun w => R (Yn w) := R.continuous.measurable.comp hYnm
  have hRYg : Measurable fun w => R (Yg w) := R.continuous.measurable.comp hYgm
  set Op : ℝ → Ω' → OscDual d m := fun t w => s81p_pathProc (R (Yn w)) t with hOp
  set G1 : ℝ → Ω' → OscDual d m := fun t w => s81p_pathProc (R (Yg w)) t with hG1
  have hwinO : ∀ w, processWindow m T 0 Op w = R (Yn w) := fun w => s81p_pathProc_win (R (Yn w))
  have hwinG : ∀ w, processWindow m T 0 G1 w = R (Yg w) := fun w => s81p_pathProc_win (R (Yg w))
  -- the cost
  have hcostL2 : s81p_L2 P' (fun w => Yn w - Yg w) ≤
      ENNReal.ofReal (Real.sqrt (max C 0 / (2 * om 0)) *
        ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N)) := by
    rw [s81p_L2_eq]
    have e1 : (fun w => ‖Yn w - Yg w‖ₑ ^ (2 : ℝ)) = fun w => ‖Δ w‖ₑ ^ 2 := by
      funext w
      simp only [hYn, add_sub_cancel_left]
      rw [ENNReal.rpow_two]
    rw [e1]
    refine (ENNReal.rpow_le_rpow hΔint (by norm_num)).trans ?_
    have hδ := HRS.MS.FinNoise.s86_deltaN_nonneg d N (by omega)
    have hq0 : 0 ≤ (N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2 := by positivity
    have hC0 : 0 ≤ max C 0 := le_max_right _ _
    have hom0 : 0 < om 0 := hom 0
    have hle : Z * ENNReal.ofReal (1 / (2 * om 0)) ≤
        ENNReal.ofReal (max C 0 / (2 * om 0) * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2)) := by
      calc Z * ENNReal.ofReal (1 / (2 * om 0)) ≤
          ENNReal.ofReal (max C 0 * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2)) *
            ENNReal.ofReal (1 / (2 * om 0)) := by
            gcongr
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hq0)
        _ = _ := by
            rw [← ENNReal.ofReal_mul (mul_nonneg hC0 hq0)]
            congr 1; ring
    have hsq : Real.sqrt (max C 0 / (2 * om 0) * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2)) ≤
        Real.sqrt (max C 0 / (2 * om 0)) *
          ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N) := by
      rw [Real.sqrt_mul (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      have h2 := HRS.MS.FinNoise.s86_sqrt_le ((N : ℝ)⁻¹) (deltaN d ((d : ℝ) / 2) N)
        (by positivity) hδ
      have h3 : Real.sqrt ((N : ℝ)⁻¹) = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity), Real.inv_rpow (by positivity)]
      rw [h3] at h2
      exact h2
    calc (Z * ENNReal.ofReal (1 / (2 * om 0))) ^ (1 / (2 : ℝ)) ≤
        (ENNReal.ofReal (max C 0 / (2 * om 0) * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2))) ^
          (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hle (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt (max C 0 / (2 * om 0) *
          ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hsq
  -- the coefficients of the return map
  obtain ⟨Cb, hCb⟩ := return_map_bounded_proof hd a β ha hβ ρβ hρ e om hdata t₀ ht₀ C4 hL4 τ hτ b hb m
    hm T hT
  obtain ⟨B0, hB0, hB00, hbes⟩ := u11_coef_bessel hd ha hβ hρ hdata.centered hdata.orth hm
  have hcsum : ∀ α : MultiIndex d, Summable fun l => u11Coef d β ρβ e m α l ^ 2 := fun α =>
    summable_of_sum_le (fun l => sq_nonneg _) (hbes α)
  have hLb : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) (l : ℕ),
      OscDual.coord (OscPath.at' (R (S45.s45_seqBasis l)) ⟨t, ht⟩) α =
        u11Coef d β ρβ e m α l * Real.exp (-(b + t - τ / 2) * om l) := by
    intro t ht α l
    rw [hR]
    obtain ⟨hs, hmem⟩ := (hCb (S45.s45_seqBasis l)).1 t ht
    unfold returnMapW
    rw [HRS.MS.CovMeas.s101_ellVec_coord hmem α, tsum_eq_single l]
    · rw [s8p_coord_basis]; simp [u11Coef]
    · intro k hk
      rw [s8p_coord_basis]; simp [hk]
  have hQsum : ∀ (α α' : MultiIndex d) (x : ℝ), 0 ≤ x → Summable fun l =>
      u11Coef d β ρβ e m α l * u11Coef d β ρβ e m α' l * Real.exp (-x * om l) := by
    intro α α' x hx
    refine Summable.of_norm_bounded (((hcsum α).add (hcsum α')).mul_left (1 / 2 : ℝ)) fun l => ?_
    have h1 : Real.exp (-x * om l) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := hom l; nlinarith
    have h0 := Real.exp_pos (-x * om l)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos h0]
    have : |u11Coef d β ρβ e m α l * u11Coef d β ρβ e m α' l| ≤
        (1 / 2) * (u11Coef d β ρβ e m α l ^ 2 + u11Coef d β ρβ e m α' l ^ 2) := by
      rw [abs_le]; constructor <;>
        nlinarith [sq_nonneg (u11Coef d β ρβ e m α l + u11Coef d β ρβ e m α' l),
          sq_nonneg (u11Coef d β ρβ e m α l - u11Coef d β ρβ e m α' l)]
    nlinarith [abs_nonneg (u11Coef d β ρβ e m α l * u11Coef d β ρβ e m α' l)]
  have hsO0 : ∀ l, 0 ≤ s81q_sOld β τ h om l := fun l => by
    unfold s81q_sOld
    have h1 : Real.exp (-2 * h * om l) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := hom l; nlinarith
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 hβ.le) (Real.exp_pos _).le) (by linarith)
  have hsO1 : ∀ l, s81q_sOld β τ h om l ≤ β⁻¹ := fun l => by
    unfold s81q_sOld
    have h1 : Real.exp (-τ * om l) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := hom l; nlinarith
    have h2 := Real.exp_pos (-2 * h * om l)
    have h3 := Real.exp_pos (-τ * om l)
    have : Real.exp (-τ * om l) * (1 - Real.exp (-2 * h * om l)) ≤ 1 := by nlinarith
    calc β⁻¹ * Real.exp (-τ * om l) * (1 - Real.exp (-2 * h * om l))
        = β⁻¹ * (Real.exp (-τ * om l) * (1 - Real.exp (-2 * h * om l))) := by ring
      _ ≤ β⁻¹ * 1 := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hβ.le)
      _ = β⁻¹ := mul_one _
  have hfdd : ∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) →
      P'.map (s81p_vec G1 ts αs) = multivariateGaussian 0 (Matrix.of fun i j =>
        ∑' l, s81q_sOld β τ h om l *
          (u11Coef d β ρβ e m (αs i) l * Real.exp (-(b + ts i - τ / 2) * om l)) *
          (u11Coef d β ρβ e m (αs j) l * Real.exp (-(b + ts j - τ / 2) * om l))) := by
    intro p ts αs hts
    choose L hL using fun i => s81q_path_coord_clm R ⟨ts i, hts i⟩ (αs i)
    have e1 : s81p_vec G1 ts αs = fun w => (WithLp.toLp 2 fun i => L i (Yg w) :
        EuclideanSpace ℝ (Fin p)) := by
      funext w
      ext i
      simp only [s81p_vec, hG1, s81p_pathProc, dif_pos (hts i), hL]
    rw [e1, s81q_fdd_of_gaussian P' hYgm hGg (fun l => s81q_sOld β τ h om l) hGcov L]
    congr 2
    ext i j
    refine tsum_congr fun l => ?_
    rw [hL i, hL j, hLb (ts i) (hts i) (αs i) l, hLb (ts j) (hts j) (αs j) l]
  have hb0 : 0 < b := by linarith
  have hmat : ∀ (p : ℕ) (ts : Fin p → ℝ), (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) →
      ∀ (αs : Fin p → MultiIndex d) (i j : Fin p),
      ∑' l, s81q_sOld β τ h om l *
          (u11Coef d β ρβ e m (αs i) l * Real.exp (-(b + ts i - τ / 2) * om l)) *
          (u11Coef d β ρβ e m (αs j) l * Real.exp (-(b + ts j - τ / 2) * om l)) =
        s81w2_Q d β ρβ e om m (αs i) (αs j) (2 * b + ts i + ts j) -
          s81w2_Q d β ρβ e om m (αs i) (αs j) (2 * (b + h) + ts i + ts j) := by
    intro p ts hts αs i j
    have hx1 : 0 ≤ 2 * b + ts i + ts j := by linarith [(hts i).1, (hts j).1]
    have hx2 : 0 ≤ 2 * (b + h) + ts i + ts j := by linarith [(hts i).1, (hts j).1]
    unfold s81w2_Q
    rw [← mul_sub, ← (hQsum (αs i) (αs j) _ hx1).tsum_sub (hQsum (αs i) (αs j) _ hx2),
      ← tsum_mul_left]
    refine tsum_congr fun l => ?_
    have e1 : Real.exp (-τ * om l) * Real.exp (-(b + ts i - τ / 2) * om l) *
        Real.exp (-(b + ts j - τ / 2) * om l) = Real.exp (-(2 * b + ts i + ts j) * om l) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(2 * (b + h) + ts i + ts j) * om l) =
        Real.exp (-2 * h * om l) * Real.exp (-(2 * b + ts i + ts j) * om l) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e2]
    unfold s81q_sOld
    calc β⁻¹ * Real.exp (-τ * om l) * (1 - Real.exp (-2 * h * om l)) *
          (u11Coef d β ρβ e m (αs i) l * Real.exp (-(b + ts i - τ / 2) * om l)) *
          (u11Coef d β ρβ e m (αs j) l * Real.exp (-(b + ts j - τ / 2) * om l))
        = β⁻¹ * (u11Coef d β ρβ e m (αs i) l * u11Coef d β ρβ e m (αs j) l) *
          ((1 - Real.exp (-2 * h * om l)) * (Real.exp (-τ * om l) *
            Real.exp (-(b + ts i - τ / 2) * om l) * Real.exp (-(b + ts j - τ / 2) * om l))) := by ring
      _ = _ := by rw [e1]; ring
  have hpsd : ∀ (p : ℕ) (ts : Fin p → ℝ), (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) →
      ∀ (αs : Fin p → MultiIndex d), (Matrix.of fun i j =>
        ∑' l, s81q_sOld β τ h om l *
          (u11Coef d β ρβ e m (αs i) l * Real.exp (-(b + ts i - τ / 2) * om l)) *
          (u11Coef d β ρβ e m (αs j) l * Real.exp (-(b + ts j - τ / 2) * om l))).PosSemidef := by
    intro p ts hts αs
    have hmateq : (Matrix.of fun i j =>
        ∑' l, s81q_sOld β τ h om l *
          (u11Coef d β ρβ e m (αs i) l * Real.exp (-(b + ts i - τ / 2) * om l)) *
          (u11Coef d β ρβ e m (αs j) l * Real.exp (-(b + ts j - τ / 2) * om l))) =
        s81p_seriesCov (fun i l => u11Coef d β ρβ e m (αs i) l * Real.exp (-(b + ts i - τ / 2) * om l))
          (fun l => (s81q_sOld β τ h om l).toNNReal) := by
      ext i j
      simp only [s81p_seriesCov, Matrix.of_apply]
      refine tsum_congr fun l => ?_
      rw [Real.coe_toNNReal _ (hsO0 l)]; ring
    rw [hmateq]
    refine s81p_seriesCov_psd fun i => ?_
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (sq_nonneg _) (NNReal.coe_nonneg _))
      (fun l => ?_) ((hcsum (αs i)).mul_left β⁻¹)
    have h1 : Real.exp (-(b + ts i - τ / 2) * om l) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := hom l
      have : 0 ≤ b + ts i - τ / 2 := by linarith [(hts i).1]
      nlinarith
    have h0 := Real.exp_pos (-(b + ts i - τ / 2) * om l)
    rw [Real.coe_toNNReal _ (hsO0 l), mul_pow]
    have h2 : Real.exp (-(b + ts i - τ / 2) * om l) ^ 2 ≤ 1 := by nlinarith
    have h3 := hsO1 l
    have h4 := hsO0 l
    have h5 := sq_nonneg (u11Coef d β ρβ e m (αs i) l)
    calc u11Coef d β ρβ e m (αs i) l ^ 2 * Real.exp (-(b + ts i - τ / 2) * om l) ^ 2 *
          s81q_sOld β τ h om l
        ≤ u11Coef d β ρβ e m (αs i) l ^ 2 * 1 * β⁻¹ := by gcongr
      _ = β⁻¹ * u11Coef d β ρβ e m (αs i) l ^ 2 := by ring
  -- the physical link: the `W∘π`-integral and the polar `B`-integral of the same martingale
  have hlink : ∀ l : ℕ, ∃ JW : ℝ → Ω' → ℝ,
      IsCtbl P' ℱ' (fun r w (ia : Fin N × Fin d) => s81q_fcl om h l r *
        inner ℝ (s81q_Phi d N β τ e om X r (π w) ia) (S45.s45_seqBasis l)) ∧
      IsItoC P' ℱ' (fun t w (ia : Fin N × Fin d) => W t (π w) ia.1 ia.2)
        (fun r w ia => s81q_fcl om h l r *
          inner ℝ (s81q_Phi d N β τ e om X r (π w) ia) (S45.s45_seqBasis l)) JW ∧
      (fun w => SeqL2.coord (Yn w) l) =ᵐ[P'] JW h := by
    intro l
    have hI1 := s81q_hilbert_isItoC hM (S45.s45_seqBasis l)
    have hξ1 : IsCtbl P ℱ (fun r ω ia => inner ℝ (s81q_Phi d N β τ e om X r ω ia)
        (S45.s45_seqBasis l)) := HRS.Uniform.Q07c.ctbl_coord hΦ (S45.s45_seqBasis l)
    obtain ⟨hξ1', hI1'⟩ := s81q_isItoC_comp hπm hπ hW hWb hξ1 hI1
    have hξW : IsCtbl P' ℱ' (fun r w ia => s81q_fcl om h l r *
        inner ℝ (s81q_Phi d N β τ e om X r (π w) ia) (S45.s45_seqBasis l)) :=
      hξ1'.mul_bdd (w := fun r (_ : Ω') => s81q_fcl om h l r)
        (pc_isProgressive_det (s81q_fcl_cont om h l).measurable) (C := 1)
        (fun r _ => s81q_fcl_abs_le hom h l r)
    obtain ⟨JW, hJW⟩ := exists_isItoC hWb hξW
    refine ⟨JW, hξW, hJW, ?_⟩
    have hI2 := s81q_hilbert_isItoC hcoup.empirical (S45.s45_seqBasis l)
    have hξ2 := HRS.Uniform.Q07c.ctbl_coord hHSS (S45.s45_seqBasis l)
    have hTD := s81q_weighted_eq hWb hξ1' hI1' hB hξ2 hI2 hh
      (fun t ht => Filter.Eventually.of_forall fun w => by simp [min_eq_left ht.2])
      (s81q_fcl_cont om h l) ⟨1, fun r => s81q_fcl_abs_le hom h l r⟩ hJW (hJs l)
    filter_upwards [hTD, hΔc] with w h1 h2
    rw [h1]
    have : SeqL2.coord (Yn w) l = SeqL2.coord (Yg w) l + SeqL2.coord (Δ w) l := rfl
    rw [this, h2 l]
    ring
  have hYg2 : ∫⁻ w, ‖Yg w‖ₑ ^ 2 ∂P' ≠ ⊤ := by
    haveI : IsGaussian (law P' Yg) := hGg.1
    have hint : Integrable (fun x : SeqL2 => ‖x‖ ^ 2) (law P' Yg) :=
      (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).1 IsGaussian.memLp_two_id
    have h1 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(law P' Yg) < ⊤ := hint.lintegral_lt_top
    have h2 : ∫⁻ w, ENNReal.ofReal (‖Yg w‖ ^ 2) ∂P' = ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(law P' Yg) := by
      exact (lintegral_map (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 2)) hYgm).symm
    have h3 : ∀ w, ‖Yg w‖ₑ ^ 2 = ENNReal.ofReal (‖Yg w‖ ^ 2) := fun w => by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    simp_rw [h3, h2]
    exact h1.ne
  have hYn2 : ∫⁻ w, ‖Yn w‖ₑ ^ 2 ∂P' ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := 2 * ∫⁻ w, ‖Yg w‖ₑ ^ 2 ∂P' + 2 * ∫⁻ w, ‖Δ w‖ₑ ^ 2 ∂P') ?_ ?_
    · refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) hYg2, ENNReal.mul_ne_top (by norm_num) ?_⟩
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hΔint
    · calc ∫⁻ w, ‖Yn w‖ₑ ^ 2 ∂P' ≤ ∫⁻ w, (2 * ‖Yg w‖ₑ ^ 2 + 2 * ‖Δ w‖ₑ ^ 2) ∂P' :=
            lintegral_mono fun w => s81q_enorm_add_sq_le _ _
        _ = _ := by
            rw [lintegral_add_left ((hYgm.enorm.pow_const 2).const_mul 2),
              lintegral_const_mul _ (hYgm.enorm.pow_const 2),
              lintegral_const_mul _ (hΔm.enorm.pow_const 2)]
  refine ⟨Ω', mΩ', P', π, ℱ', B, Yg, Yn, Op, G1, hP', hπ, hfil, hB, hcoup.indep, hWb, hGad, hYnad,
    hGg, hGcov, hGind,
    (fun t => @s81p_pathProc_measurable d m T Ω' (ℱ' h) _
      (R.continuous.measurable.comp hGad) t),
    ⟨fun t => s81p_pathProc_measurable hRYn t,
      Filter.Eventually.of_forall fun w => s81p_pathProc_cont (R (Yn w))⟩,
    ⟨fun t => s81p_pathProc_measurable hRYg t,
      Filter.Eventually.of_forall fun w => s81p_pathProc_cont (R (Yg w))⟩, hwinO, hwinG, ?_,
    fun p ts αs hts => ?_, fun p ts αs hts => ?_, hYn2, hlink⟩
  · have e1 : (fun ζ => processWindow m T 0 Op ζ - processWindow m T 0 G1 ζ) =
        fun ζ => R (Yn ζ) - R (Yg ζ) := by
      funext ζ; rw [hwinO, hwinG]
    rw [e1]
    refine (s81p_L2_clm P' R Yn Yg).trans ?_
    refine (mul_le_mul' le_rfl hcostL2).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (norm_nonneg _), ← mul_assoc]
  · rw [hfdd p ts αs hts]
    congr 2
    ext i j
    exact hmat p ts hts αs i j
  · have := hpsd p ts hts αs
    convert this using 1
    ext i j
    exact (hmat p ts hts αs i j).symm

end HRS.Whole.S81Q
