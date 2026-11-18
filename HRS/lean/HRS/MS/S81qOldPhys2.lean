import HRS.MS.S81qOldPhys
import HRS.MS.S88BDTie

/-!
# S8.1 (worker S81Q): physical identification of the old current (assembly)

Namespace `HRS.Whole.S81Q`, prefix `s81q_`.

`s81q_old_phys`: with the old-block data (`s81q_old_block`: `Yn` and, for each `l`, the weighted coordinate integrals `JW_l` against `W ∘ π`), for
`t ∈ [0,T]` and `α`, the series `∑' l a_l (Yn)_l` (`a_l = coef α l e^{-(b+t-τ/2)ω_l}`, i.e. the `α`-coordinate of the return map at time `t` of `Yn`)
is `P'`-a.e. the value at time `h` of the Itô integral wrt `W ∘ π` of the physical old integrand
`√(2/(Nβ)) ∂_a U^{r,b+h+t} φ_α (X_i(r))`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
open HRS HRS.Whole HRS.MS.SuppU11 HRS.MS.Spec HRS.Whole.S81P HRS.Whole.S81W2 HRS.MS.S88Breakdown

namespace HRS.Whole.S81Q

set_option maxHeartbeats 1600000 in
theorem s81q_old_phys {d : ℕ} (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {e : ℕ → Euc d → ℝ} {om : ℕ → ℝ}
    (hdata : IsSpectralData d β ρβ e om) {m : ℝ} (hm : (wholeSpaceIndex d : ℝ) ≤ m)
    (hcoef : S81W2Coef d a β ρβ e om m) {t₀ C4 : ℝ} (ht₀ : 0 < t₀)
    (hL4 : ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (withDensityReal ρβ) ≤
      ENNReal.ofReal (C4 * Real.exp (t₀ * om l)))
    {τ : ℝ} (hτ : 4 * t₀ < τ) {b : ℝ} (hb : τ / 2 + 1 < b)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hreal : IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X) {ℱ : Filtration ℝ mΩ}
    (hW : IsCylindricalBrownian P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2))
    (hprog : ∀ i : Fin N, IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i))
    {Ω' : Type} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {π : Ω' → Ω}
    (hπ : MeasurePreserving π P' P) {ℱ' : Filtration ℝ mΩ'} (hfil : ∀ s, (ℱ s).comap π ≤ ℱ' s)
    (hWb : IsCylindricalBrownian P' ℱ' (fun t w (ia : Fin N × Fin d) => W t (π w) ia.1 ia.2))
    {h : ℝ} (hh : 0 ≤ h) {t : ℝ} (ht : 0 ≤ t) (α : MultiIndex d)
    (Yn : Ω' → SeqL2) (hYn2 : ∫⁻ w, ‖Yn w‖ₑ ^ 2 ∂P' ≠ ⊤)
    (hlink : ∀ l : ℕ, ∃ JW : ℝ → Ω' → ℝ,
      IsCtbl P' ℱ' (fun r w (ia : Fin N × Fin d) => s81q_fcl om h l r *
        inner ℝ (s81q_Phi d N β τ e om X r (π w) ia) (S45.s45_seqBasis l)) ∧
      IsItoC P' ℱ' (fun t w (ia : Fin N × Fin d) => W t (π w) ia.1 ia.2)
        (fun r w ia => s81q_fcl om h l r *
          inner ℝ (s81q_Phi d N β τ e om X r (π w) ia) (S45.s45_seqBasis l)) JW ∧
      (fun w => SeqL2.coord (Yn w) l) =ᵐ[P'] JW h)
    (Ωt : Ω' → ℝ) (hΩm : Measurable Ωt)
    (hΩ : ∀ w, Ωt w = ∑' l, u11Coef d β ρβ e m α l * Real.exp (-(b + t - τ / 2) * om l) *
      SeqL2.coord (Yn w) l) :
    ∃ JO : ℝ → Ω' → ℝ,
      IsItoC P' ℱ' (fun t w (ia : Fin N × Fin d) => W t (π w) ia.1 ia.2)
        (fun r w ia => Real.sqrt (2 / (N * β)) * HRS.MH.DualityRd.truncGradIntegrand (b + h + t)
          (fun r' => propagatorW (critCoeff d a β ρβ) r' (b + h + t) (oscTestFun m α))
          (fun s z => X s (π z)) r w ia) JO ∧ Ωt =ᵐ[P'] JO h := by
  classical
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hb0 : 0 < b := by
    have : 0 < τ := by linarith [ht₀]
    linarith
  have hv0 : 0 ≤ b + h + t := by linarith
  have hom : ∀ l, 0 < om l := hdata.pos
  have hρeq : ρβ = thermalDensity d ((d : ℝ) / 2) a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hμeq : withDensityReal ρβ = thermalMeasure d ((d : ℝ) / 2) a β := by rw [hρeq]; rfl
  obtain ⟨Cs, hCs0, hStat⟩ := S45.s45_static_all hd hs0 hsd ha hβ
  have hSN := hStat N hN
  obtain ⟨cc, bb, hc, hbb, hsumb, hall⟩ := s88_orbit_envelopes hd a β ha hβ m hm
  obtain ⟨hreg, -⟩ := hall ρβ hρ
  have hτ0 : 0 < τ := by linarith [ht₀]
  obtain ⟨C0, hC0⟩ := s81q_coupling_claim hd ha hβ hρ hdata ht₀ hL4 hτ
  obtain ⟨hgood, hΦ, -⟩ := hC0 N hN P X₀ W X hreal ℱ hW hprog
  have hπm : ∀ s, Measurable[ℱ' s, ℱ s] π := fun s => Measurable.of_comap_le (hfil s)
  -- the coefficients
  obtain ⟨B0, hB0, hB00, hbes⟩ := u11_coef_bessel hd ha hβ hρ hdata.centered hdata.orth hm
  have hcs : Summable fun l => u11Coef d β ρβ e m α l ^ 2 :=
    summable_of_sum_le (fun l => sq_nonneg _) (hbes α)
  have hasq : Summable fun l => (u11Coef d β ρβ e m α l * Real.exp (-(b + t - τ / 2) * om l)) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_) hcs
    have h1 : Real.exp (-(b + t - τ / 2) * om l) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := hom l
      have : 0 ≤ b + t - τ / 2 := by linarith
      nlinarith
    have h0 := Real.exp_pos (-(b + t - τ / 2) * om l)
    rw [mul_pow]
    have : Real.exp (-(b + t - τ / 2) * om l) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (u11Coef d β ρβ e m α l)]
  -- time homogeneity
  have hvpos : 0 < b + h + t := by linarith
  obtain ⟨B1, hB1, hfd⟩ := HRS.MS.FinNoise.s86_feat_data hd a β ha hβ m hm (b + h + t) hvpos
  have hfeat := (hfd ρβ hρ).1
  have hshift : ∀ r ∈ Set.Icc (0 : ℝ) (b + h + t),
      propagatorW (critCoeff d a β ρβ) r (b + h + t) (oscTestFun m α) =
        propagatorW (critCoeff d a β ρβ) 0 (b + h + t - r) (oscTestFun m α) := fun r hr =>
    HRS.MS.FinNoise.s86_prop_shift _ hfeat.gen (b + h + t) hfeat.uniq (b + h + t)
      ⟨hv0, le_rfl⟩ _ (hreg.classical α _ hv0) r hr
  -- the closure of the gradient expansion
  have hclos : ∀ s : ℝ, 0 < s →
      (Summable fun l => om l * (Real.exp (-s * om l) * u11Coef d β ρβ e m α l) ^ 2) ∧
      ∀ L : ℕ, ∫⁻ x, ENNReal.ofReal (‖s81q_Gs (critCoeff d a β ρβ) m α e om
          (u11Coef d β ρβ e m α) s L x‖ ^ 2) ∂(thermalMeasure d ((d : ℝ) / 2) a β) =
        ENNReal.ofReal (s81q_tail om (u11Coef d β ρβ e m α) s L) := by
    intro s hs
    obtain ⟨hsm, hL⟩ := s81w2_grad_closure hd ha hβ hρ hm hdata hcoef α hs
    refine ⟨hsm, fun L => ?_⟩
    obtain ⟨hint, hid⟩ := hL L
    have e : ∫⁻ x, ENNReal.ofReal (‖s81q_Gs (critCoeff d a β ρβ) m α e om
        (u11Coef d β ρβ e m α) s L x‖ ^ 2) ∂(withDensityReal ρβ) =
        ENNReal.ofReal (∫ x, ‖gradient (s88Orbit (critCoeff d a β ρβ) m s α) x -
          ∑ l ∈ Finset.range L, (Real.exp (-s * om l) * u11Coef d β ρβ e m α l) •
            gradient (e l) x‖ ^ 2 ∂(withDensityReal ρβ)) :=
      (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
    rw [← hμeq, e, hid]
    rfl
  have hGm : ∀ s : ℝ, 0 < s → ∀ L, Measurable
      (s81q_Gs (critCoeff d a β ρβ) m α e om (u11Coef d β ρβ e m α) s L) := by
    intro s hs L
    unfold s81q_Gs
    refine Measurable.sub ?_ ?_
    · exact (S45.s45_contDiff_gradient (hreg.memCb α s hs.le).1).continuous.measurable
    · exact Finset.measurable_sum _ fun l _ =>
        ((s81w2_gradient_continuous (hdata.smooth l)).const_smul
          (Real.exp (-s * om l) * u11Coef d β ρβ e m α l)).measurable
  -- progressivity
  have hΦprog : ∀ (l : ℕ) (ia : Fin N × Fin d), IsProgressive ℱ' (fun r w =>
      inner ℝ (s81q_PhiAt β τ e om (X (Real.toNNReal r) (π w)) ia) (S45.s45_seqBasis l)) :=
    fun l ia => isProgressive_comp_π hπm (g := fun r z =>
      inner ℝ (s81q_Phi d N β τ e om X r z ia) (S45.s45_seqBasis l))
      (fun i => (((hΦ 0).prog ia) i).inner measurable_const)
  have hXP : IsProgressive ℱ (HRS.ofNNRealTime X) := fun i => by
    letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    exact measurable_pi_iff.2 fun k => hprog k i
  have hXp : IsProgressive ℱ' (HRS.ofNNRealTime (fun s (z : Ω') => X s (π z))) :=
    isProgressive_comp_π hπm hXP
  have hadj : IsClassicalAdjointW (critCoeff d a β ρβ) (b + h + t) (oscTestFun m α)
      (fun r => propagatorW (critCoeff d a β ρβ) r (b + h + t) (oscTestFun m α)) :=
    HRS.MS.Fcau.propagatorW_isClassical (hreg.classical α _ hv0)
  have hphL2 := HRS.MH.DualityRd.isProgressiveL2_truncGrad_proof (P := P') (ℱ := ℱ') (N := N) hv0
    hadj.isC12TestRd hXp
  have hphprog : ∀ ia : Fin N × Fin d, IsProgressive ℱ' (fun r w =>
      HRS.MH.DualityRd.truncGradIntegrand (b + h + t)
        (fun r' => propagatorW (critCoeff d a β ρβ) r' (b + h + t) (oscTestFun m α))
        (fun s z => X s (π z)) r w ia) := fun ia i => (measurable_pi_apply ia).comp (hphL2.prog i)
  have hξph : IsCtbl P' ℱ' (fun r w (ia : Fin N × Fin d) => Real.sqrt (2 / (N * β)) *
      HRS.MH.DualityRd.truncGradIntegrand (b + h + t)
        (fun r' => propagatorW (critCoeff d a β ρβ) r' (b + h + t) (oscTestFun m α))
        (fun s z => X s (π z)) r w ia) := by
    have hsm := hphL2.smul (Real.sqrt (2 / (N * β)))
    refine pc_isCtbl_of (fun ia i => (measurable_const.mul (hphprog ia i))) fun T => ?_
    have := (hsm.sq T).ne
    unfold sqIntegralOn at this
    simp_rw [tsum_fintype]
    exact this
  -- the marginal data
  have hXm : ∀ (s : ℝ≥0) (i : Fin N), Measurable fun w => X s (π w) i := fun s i =>
    (measurable_pi_apply i).comp (((hreal.solution (s : ℝ)).adapted s).comp hπ.measurable)
  have hgoodm := s81q_good_meas τ hdata.smooth om
  have hgoodμ : thermalMeasure d ((d : ℝ) / 2) a β (s81q_good τ e om)ᶜ = 0 := by
    have : ∀ᵐ x ∂(thermalMeasure d ((d : ℝ) / 2) a β), x ∈ s81q_good τ e om := by
      rw [← hμeq]
      filter_upwards [hgood] with x hx i
      exact memℓp_two_iff.1 (hx i)
    exact ae_iff.1 this
  choose JW hJWc hJWi hJWa using hlink
  have hL2 := fun L : ℕ => s81q_phys_L2 hN hβ P' (ℱ' := ℱ') (Cs := Cs)
    (thermalMeasure d ((d : ℝ) / 2) a β) (fun s z => X s (π z)) hXm
    (fun r hr i g hg => s81q_marginal_le hN hπ hreal hSN r hr i g hg) hgoodm hgoodμ
    (critCoeff d a β ρβ) m α (u11Coef d β ρβ e m α) hb0 hh ht hGm
    (fun s hs L => (hclos s hs).2 L) hshift hΦprog hphprog L
  refine s81q_phys_ident P' hWb hh (fun l => u11Coef d β ρβ e m α l * Real.exp (-(b + t - τ / 2) * om l))
    hasq (fun l r w ia => s81q_fcl om h l r *
      inner ℝ (s81q_Phi d N β τ e om X r (π w) ia) (S45.s45_seqBasis l)) hJWc JW hJWi _ hξph Yn hYn2
    hJWa Ωt hΩm hΩ
    (fun L => ENNReal.ofReal (2 * Cs / β) * ∫⁻ r in Set.Icc 0 h,
      ENNReal.ofReal (s81q_tail om (u11Coef d β ρβ e m α) (b + h + t - r) L)) ?_ (fun L => hL2 L)
  have := ENNReal.Tendsto.const_mul (s81q_tail_int_tendsto hom hcs (fun s hs => (hclos s hs).1) hb0 hh ht)
    (Or.inr (ENNReal.ofReal_ne_top (r := 2 * Cs / β)))
  simpa using this

end HRS.Whole.S81Q
