import HRS.MS.S81qAdjoin
import HRS.MS.S88BDTie
import HRS.Main.GFB3Aux9
import HRS.MS.S81qInit

/-!
# S8.1 (worker S81Q): the initial and old blocks on an enlargement, and `S81PBlocks`

Namespace `HRS.Whole.S81Q`, prefix `s81q_`.

`S81QOld` is the interface `HRS.Whole.S81S.S81SOld` with ONE change: the identification of the initial term `Ip` is asserted `Q₁`-almost everywhere
(`∀ᵐ ζ ∂Q₁`) instead of for every `ζ`.  The pointwise version cannot hold in general: `X₀` is only almost everywhere measurable (`IsCanonicalRealization` constrains the
law of `X₀`, and `X₀` is only a.e. equal to the measurable `X 0`), while the measurable process `Ip` is built from a measurable modification of `X₀`.
The glue `s81s_blocks` only uses the identification on a `Q₂`-full set (inside `filter_upwards`), so the a.e. clause is all it needs.

* `s81q_old : S81QOld`.  Enlargement `Ω₁ = Ω' × (ℕ → ℝ)`, `Q₁ = P' ⊗ γ`, `π₁ = π ∘ fst`, `ℱ₁ = ℱ' ⊗ const`; `Ip` from `s81q_initial_term`, the initial Gaussian
  `G0` from `s81p_initial_block` on the second factor (independent of the old block), `Op`, `G1` from `s81q_old_block` on the first factor; the identification of `Op` is
  `s81q_old_phys` + the finite-index bridge `s81q_itoC_eq_ito` + `itoIntegral_comp_π` along `fst`.
* `s81q_blocks : S81QOld → weighted_critical_forcing → S81PBlocks`: the proof of `s81s_blocks` with that one a.e. patch.
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
open HRS HRS.Whole HRS.MS.SuppU11 HRS.MS.Spec HRS.Whole.S81P HRS.Whole.S81W2 HRS.Whole.S81S

namespace HRS.Whole.S81Q

section Lemmas

/-- A filtered solution pulled back along a measure-preserving enlargement. -/
theorem s81q_filtered_comp {d N : ℕ} {Ω Ω₁ : Type*} {mΩ : MeasurableSpace Ω} {mΩ₁ : MeasurableSpace Ω₁}
    {P : Measure Ω} {Q₁ : Measure Ω₁} {ℱ : Filtration ℝ mΩ} {ℱ₁ : Filtration ℝ mΩ₁} {π₁ : Ω₁ → Ω}
    (hfil : ∀ t, (ℱ t).comap π₁ ≤ ℱ₁ t)
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hF : IsWholeFilteredSolution P ℱ W' W X)
    (W₁ : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ) (hW₁ : IsBrownianFiltration Q₁ ℱ₁ W₁)
    (hco : ∀ᵐ ζ ∂Q₁, ∀ t i j, W₁ t ζ (i, j) = W t (π₁ ζ) i j) :
    IsWholeFilteredSolution Q₁ ℱ₁ W₁ (fun t z => W t (π₁ z)) (fun t z => X t (π₁ z)) := by
  have hπm : ∀ t, @Measurable Ω₁ Ω (ℱ₁ t) (ℱ t) π₁ := fun t => (measurable_iff_comap_le).2 (hfil t)
  exact ⟨hW₁, hco, fun t => (hF.adapted t).comp (hπm t), isProgressive_comp_π hπm hF.progressive⟩

/-- The value at time `s` of a countable-index Itô integral on `Ω'` is a.e. the Itô integral on the enlargement `Ω' × Ω₀`
(product measure and product filtration) of the lifted integrand. -/
theorem s81q_ito_lift {Ω' Ω₀ : Type} [mΩ' : MeasurableSpace Ω'] [m₀ : MeasurableSpace Ω₀]
    (P' : Measure Ω') [IsProbabilityMeasure P'] (μ : Measure Ω₀) [IsProbabilityMeasure μ]
    (ℱ' : Filtration ℝ mΩ') {κ : Type} [Fintype κ] [DecidableEq κ] {B : ℝ≥0 → Ω' → κ → ℝ}
    (hB : IsCylindricalBrownian P' ℱ' B) {g : ℝ → Ω' → κ → ℝ} (hg : IsProgressiveL2 P' ℱ' g)
    {J : ℝ → Ω' → ℝ} (hJ : IsItoC P' ℱ' B g J) {s : ℝ} (hs : 0 ≤ s) :
    ∀ᵐ z ∂(P'.prod μ), J s z.1 = itoIntegral (P'.prod μ)
      (prodFiltration P' μ ℱ' (Filtration.const ℝ m₀ le_rfl))
      (fun t (z : Ω' × Ω₀) k => B t z.1 k) (fun r (z : Ω' × Ω₀) k => g r z.1 k) s z := by
  have hBb := s81s_brownian_of_cyl hB
  have h1 := s81q_itoC_eq_ito hBb (HRS.GF.gfb3_isProgressiveL2_restrict_univ hg) hJ hs
  have hB₁ := s81s_brownian_of_cyl (s81q_adjoin_cyl P' μ ℱ' hB)
  have hfst : ∀ t, @Measurable (Ω' × Ω₀) Ω'
      ((prodFiltration P' μ ℱ' (Filtration.const ℝ m₀ le_rfl)) t) (ℱ' t) Prod.fst := fun t =>
    (measurable_iff_comap_le).2 (le_sup_of_le_left le_sup_left)
  have h2 := itoIntegral_comp_π hfst measurePreserving_fst hBb hB₁ hg
  have h3 := (measurePreserving_fst (μ := P') (ν := μ)).quasiMeasurePreserving.ae h1
  filter_upwards [h2, h3] with z hz1 hz2
  rw [hz2]
  exact (hz1 s).symm

/-- The coordinates of the return map applied to an `ℓ²` vector. -/
theorem s81q_ret_coord {d : ℕ} (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {e : ℕ → Euc d → ℝ} {om : ℕ → ℝ}
    (hdata : IsSpectralData d β ρβ e om) {t₀ : ℝ} (ht₀ : 0 < t₀) {C4 : ℝ}
    (hL4 : ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (withDensityReal ρβ) ≤
      ENNReal.ofReal (C4 * Real.exp (t₀ * om l)))
    {τ : ℝ} (hτ : 4 * t₀ < τ) {b : ℝ} (hb : τ / 2 + 1 < b) {m : ℝ}
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) {T : ℝ} (hT : 0 < T) (R : SeqL2 →L[ℝ] OscPath d m T)
    (hR : ∀ (z : SeqL2) (t : Set.Icc (0 : ℝ) T),
      OscPath.at' (R z) t = returnMapW d β ρβ e om m τ b z t)
    (z : SeqL2) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    OscDual.coord (OscPath.at' (R z) ⟨t, ht⟩) α =
      ∑' l, u11Coef d β ρβ e m α l * Real.exp (-(b + t - τ / 2) * om l) * SeqL2.coord z l := by
  obtain ⟨Cb, hCb⟩ := return_map_bounded_proof hd a β ha hβ ρβ hρ e om hdata t₀ ht₀ C4 hL4 τ hτ b hb m
    hm T hT
  obtain ⟨hs, hmem⟩ := (hCb z).1 t ht
  rw [hR]
  unfold returnMapW
  rw [HRS.MS.CovMeas.s101_ellVec_coord hmem α]
  rfl

theorem s81q_deltaN_nonneg {d N : ℕ} (hN : 1 ≤ N) : 0 ≤ deltaN d ((d : ℝ) / 2) N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold HRS.deltaN
  simp only [lt_self_iff_false, ↓reduceIte]
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg N)) (Real.log_nonneg ?_)
  have := Real.add_one_le_exp (1 : ℝ)
  nlinarith

/-- Triangle inequality for `s81p_L2` of a difference. -/
theorem s81q_L2_sub_le {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {P : Measure Ω}
    {f g : Ω → E} (hf : AEMeasurable (fun ω => ‖f ω‖ₑ) P) (hg : AEMeasurable (fun ω => ‖g ω‖ₑ) P) :
    s81p_L2 P (fun ω => f ω - g ω) ≤ s81p_L2 P f + s81p_L2 P g := by
  have h := s81p_L2_add_le (P := P) (f := f) (g := fun ω => -g ω) hf (by simpa using hg)
  rw [s81p_L2_neg] at h
  simpa [sub_eq_add_neg] using h

end Lemmas

section Old

variable {d : ℕ}

/-- The interface `S81SOld` with the identification of the initial term stated `Q₁`-a.e. (the initial configuration `X₀` is only a.e. measurable). -/
def S81QOld : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∀ (a β : ℝ), 0 < a → 0 < β → ∀ (m : ℝ), (wholeSpaceIndex d : ℝ) ≤ m →
    ∀ T : ℝ, 0 < T →
    ∃ (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (b : ℝ),
      IsSpectralData d β (thermalDensity d ((d : ℝ) / 2) a β) e om ∧
      S81W2Coef d a β (thermalDensity d ((d : ℝ) / 2) a β) e om m ∧ 0 ≤ b ∧
      ∃ (C c u0 : ℝ), 0 < c ∧ b ≤ u0 ∧ ∀ N : ℕ, 2 ≤ N →
        ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
          IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
          ∀ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
            IsCylindricalBrownian P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) →
            IsWholeFilteredSolution P ℱ W' W X →
          ∀ u : ℝ, u0 ≤ u →
          ∃ (Ω₁ : Type) (mΩ₁ : MeasurableSpace Ω₁) (Q₁ : Measure Ω₁) (_ : IsProbabilityMeasure Q₁)
            (π₁ : Ω₁ → Ω) (ℱ₁ : Filtration ℝ mΩ₁) (W₁ : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ),
            MeasurePreserving π₁ Q₁ P ∧ (∀ t, (ℱ t).comap π₁ ≤ ℱ₁ t) ∧
            IsCylindricalBrownian Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => W t (π₁ z) ia.1 ia.2) ∧
            IsWholeFilteredSolution Q₁ ℱ₁ W₁ (fun t z => W t (π₁ z)) (fun t z => X t (π₁ z)) ∧
            ∃ (Ip Op G0 G1 : ℝ → Ω₁ → OscDual d m)
              (S0 S1 : ∀ (p : ℕ), (Fin p → ℝ) → (Fin p → MultiIndex d) → Matrix (Fin p) (Fin p) ℝ)
              (ε₀ ε₁ : ℝ≥0∞),
              S81PProc Q₁ T Ip ∧ S81PProc Q₁ T Op ∧ S81PProc Q₁ T G0 ∧ S81PProc Q₁ T G1 ∧
              (∀ t, @Measurable Ω₁ (OscDual d m) (ℱ₁ (u - b)) _ (G0 t)) ∧
              (∀ t, @Measurable Ω₁ (OscDual d m) (ℱ₁ (u - b)) _ (G1 t)) ∧
              IndepFun (fun ζ (t : ℝ) => G0 t ζ) (fun ζ (t : ℝ) => G1 t ζ) Q₁ ∧
              (∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) →
                (S0 p ts αs).PosSemidef ∧ (S1 p ts αs).PosSemidef ∧
                Q₁.map (s81p_vec G0 ts αs) = multivariateGaussian 0 (S0 p ts αs) ∧
                Q₁.map (s81p_vec G1 ts αs) = multivariateGaussian 0 (S1 p ts αs) ∧
                S0 p ts αs + S1 p ts αs = Matrix.of fun i j =>
                  s81w2_Q d β (thermalDensity d ((d : ℝ) / 2) a β) e om m (αs i) (αs j)
                    (2 * b + ts i + ts j)) ∧
              s81p_L2 Q₁ (fun ζ => processWindow m T 0 Ip ζ - processWindow m T 0 G0 ζ) ≤ ε₀ ∧
              s81p_L2 Q₁ (fun ζ => processWindow m T 0 Op ζ - processWindow m T 0 G1 ζ) ≤ ε₁ ∧
              ε₀ + ε₁ ≤ ENNReal.ofReal (C * (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂Q₁,
                OscDual.coord (Ip t ζ) α = Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X₀ (π₁ ζ)))
                    (propagatorW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) 0 (u + t)
                      (oscTestFun m α)) -
                  ∫ x, propagatorW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) 0 (u + t)
                    (oscTestFun m α) x ∂(HRS.Whole.firstMarginal (law P X₀)))) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂Q₁,
                OscDual.coord (Op t ζ) α = itoIntegral Q₁ ℱ₁
                  (fun t z (ia : Fin N × Fin d) => W t (π₁ z) ia.1 ia.2)
                  (HRS.Whole.S81S.s81s_kernel d N a β m (thermalDensity d ((d : ℝ) / 2) a β)
                    (fun t z => X t (π₁ z)) (u + t) α) (u - b) ζ)


set_option maxHeartbeats 3200000 in
/-- **The initial and old blocks on an enlargement** (interface `S81QOld`). -/
theorem s81q_old : S81QOld := by
  classical
  intro d hd a β ha hβ m hm T hT
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Euc d → ℝ, ρ = thermalDensity d ((d : ℝ) / 2) a β := ⟨_, rfl⟩
  rw [← hρdef]
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hρth : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ := by
    rw [hρdef]; exact HRS.Whole.S71.s71_thermal_equilibrium hd hs0 hsd a β ha hβ
  obtain ⟨e, om, hdata, hcoef, t₀, C4, ht₀, hL4, -⟩ :=
    s81w2_spectral_retained hd a β ha hβ m hm ρ hρth
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = 4 * t₀ + 1 := ⟨_, rfl⟩
  have hτ : 4 * t₀ < τ := by linarith
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = τ / 2 + 2 := ⟨_, rfl⟩
  have hb : τ / 2 + 1 < b := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hb1 : 1 ≤ b := by linarith
  obtain ⟨R, K1, hRdef, hBlk⟩ := s81q_old_block hd a β ha hβ hρth hdata ht₀ hL4 hτ hb hm hT
  obtain ⟨Ki, ci, hci, hInit⟩ := s81q_initial_term hd a β ha hβ m hm T hT
  obtain ⟨K0, w0, hw0, hG0blk⟩ := s81p_initial_block hd a β ha hβ ρ
    hρth e om hdata t₀ ht₀ C4 hL4 τ hτ b hb m hm T hT
  refine ⟨e, om, b, hdata, hcoef, hb0, max Ki 0 + max K0 0 + 3 * max K1 0, min ci w0, b,
    lt_min hci hw0, le_rfl, ?_⟩
  intro N hN Ω _ P _ X₀ W X hR ℱ W' hcyl hF u hu
  have hN1 : 1 ≤ N := by omega
  have hu0 : 0 ≤ u := hb0.trans hu
  have hu1 : 1 ≤ u := hb1.trans hu
  have hub : 0 ≤ u - b := by linarith
  have hprog : ∀ i : Fin N, IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i) :=
    fun i => s81s_prog_coord hF.progressive i
  obtain ⟨Ω', mΩ', P', π, ℱ', B, Yg, Yn, Op, G1, hP', hπ, hfil, hBc, hind0, hWb, hYgm, hYnm, hYgG, hYgcov,
    hYgind, hG1m, hOp, hG1, hOpwin, hG1win, hcost, hlawG1, hpsd1, hYn2, hlink⟩ :=
    hBlk N hN P X₀ W X hR ℱ hcyl hprog (u - b) hub
  have := hP'
  -- the initial Gaussian block and the physical initial term
  have hX₀ : AEMeasurable X₀ P := ((hR.solution 0).adapted 0).aemeasurable.congr (hR.solution 0).init
  have hX₀m : Measurable (hX₀.mk X₀) := hX₀.measurable_mk
  have hX₀eq : X₀ =ᵐ[P] hX₀.mk X₀ := hX₀.ae_eq_mk
  have hlaw' : law P (hX₀.mk X₀) = law P X₀ := (Measure.map_congr hX₀eq).symm
  obtain ⟨Ip₀, hIp₀, -, hIp₀id, hIp₀L2⟩ := hInit ρ hρth N hN P
    (hX₀.mk X₀) hX₀m (hlaw'.trans hR.init) u hu1
  obtain ⟨G0₀, hG0₀, hlawG0, hpsdG0, hG0L2⟩ := hG0blk u hu
  -- the enlargement
  have hπ1 : MeasurePreserving (fun z : Ω' × (ℕ → ℝ) => π z.1)
      (P'.prod (s81p_gamma (β⁻¹).toNNReal)) P := hπ.comp measurePreserving_fst
  have hfil1 : ∀ t, (ℱ t).comap (fun z : Ω' × (ℕ → ℝ) => π z.1) ≤
      prodFiltration P' (s81p_gamma (β⁻¹).toNNReal) ℱ'
        (Filtration.const ℝ (inferInstance : MeasurableSpace (ℕ → ℝ)) le_rfl) t := by
    intro t
    rw [show (fun z : Ω' × (ℕ → ℝ) => π z.1) = π ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
    exact (MeasurableSpace.comap_mono (hfil t)).trans (le_sup_of_le_left le_sup_left)
  have hcyl1 := s81q_adjoin_cyl P' (s81p_gamma (β⁻¹).toNNReal) ℱ' hWb
  refine ⟨Ω' × (ℕ → ℝ), inferInstance, P'.prod (s81p_gamma (β⁻¹).toNNReal), inferInstance,
    fun z => π z.1, prodFiltration P' (s81p_gamma (β⁻¹).toNNReal) ℱ'
      (Filtration.const ℝ (inferInstance : MeasurableSpace (ℕ → ℝ)) le_rfl),
    fun t z ia => W t (π z.1) ia.1 ia.2, hπ1, hfil1, hcyl1,
    s81q_filtered_comp hfil1 hF _ (s81s_brownian_of_cyl hcyl1)
      (Filter.Eventually.of_forall fun ζ t i j => rfl), ?_⟩
  have hsnd : MeasurePreserving (Prod.snd : Ω' × (ℕ → ℝ) → ℕ → ℝ)
      (P'.prod (s81p_gamma (β⁻¹).toNNReal)) (s81p_gamma (β⁻¹).toNNReal) := measurePreserving_snd
  have hfst : MeasurePreserving (Prod.fst : Ω' × (ℕ → ℝ) → Ω')
      (P'.prod (s81p_gamma (β⁻¹).toNNReal)) P' := measurePreserving_fst
  have hIp1 : S81PProc (P'.prod (s81p_gamma (β⁻¹).toNNReal)) T
      (fun t (z : Ω' × (ℕ → ℝ)) => Ip₀ t (π z.1)) := s81s_proc_comp hπ1 hIp₀
  have hOp1 : S81PProc (P'.prod (s81p_gamma (β⁻¹).toNNReal)) T
      (fun t (z : Ω' × (ℕ → ℝ)) => Op t z.1) := s81s_proc_comp hfst hOp
  have hG01 : S81PProc (P'.prod (s81p_gamma (β⁻¹).toNNReal)) T
      (fun t (z : Ω' × (ℕ → ℝ)) => G0₀ t z.2) := s81s_proc_comp hsnd hG0₀
  have hG11 : S81PProc (P'.prod (s81p_gamma (β⁻¹).toNNReal)) T
      (fun t (z : Ω' × (ℕ → ℝ)) => G1 t z.1) := s81s_proc_comp hfst hG1
  have hm0 : ∀ t, @Measurable (Ω' × (ℕ → ℝ)) (OscDual d m)
      (prodFiltration P' (s81p_gamma (β⁻¹).toNNReal) ℱ'
        (Filtration.const ℝ (inferInstance : MeasurableSpace (ℕ → ℝ)) le_rfl) (u - b)) _
      (fun z => G0₀ t z.2) := fun t =>
    (@Measurable.comp _ _ _ (MeasurableSpace.comap Prod.snd inferInstance) _ _ (G0₀ t) Prod.snd
      (hG0₀.1 t) (comap_measurable Prod.snd)).mono (le_sup_of_le_left le_sup_right) le_rfl
  have hm1 : ∀ t, @Measurable (Ω' × (ℕ → ℝ)) (OscDual d m)
      (prodFiltration P' (s81p_gamma (β⁻¹).toNNReal) ℱ'
        (Filtration.const ℝ (inferInstance : MeasurableSpace (ℕ → ℝ)) le_rfl) (u - b)) _
      (fun z => G1 t z.1) := fun t =>
    (@Measurable.comp _ _ _ (MeasurableSpace.comap Prod.fst (ℱ' (u - b))) _ _ (G1 t) Prod.fst
      (hG1m t) (comap_measurable Prod.fst)).mono (le_sup_of_le_left le_sup_left) le_rfl
  have hG1p : Measurable (fun (w : Ω') (t : ℝ) => G1 t w) := measurable_pi_iff.2 hG1.1
  have hG0p : Measurable (fun (g : ℕ → ℝ) (t : ℝ) => G0₀ t g) := measurable_pi_iff.2 hG0₀.1
  have hindep : IndepFun (fun (z : Ω' × (ℕ → ℝ)) (t : ℝ) => G0₀ t z.2)
      (fun z (t : ℝ) => G1 t z.1) (P'.prod (s81p_gamma (β⁻¹).toNNReal)) :=
    (indepFun_prod hG1p hG0p).symm
  refine ⟨fun t z => Ip₀ t (π z.1), fun t z => Op t z.1, fun t z => G0₀ t z.2, fun t z => G1 t z.1,
    fun p ts αs => Matrix.of fun i j => s81w2_Q d β ρ e om m (αs i) (αs j) (2 * u + ts i + ts j),
    fun p ts αs => Matrix.of fun i j => s81w2_Q d β ρ e om m (αs i) (αs j) (2 * b + ts i + ts j) -
      s81w2_Q d β ρ e om m (αs i) (αs j) (2 * (b + (u - b)) + ts i + ts j),
    ENNReal.ofReal (Ki * Real.exp (-ci * u)) + ENNReal.ofReal (K0 * Real.exp (-w0 * u)),
    ENNReal.ofReal (K1 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N)),
    hIp1, hOp1, hG01, hG11, hm0, hm1, hindep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- finite-dimensional laws
    intro p ts αs hts
    refine ⟨hpsdG0 p ts αs hts, hpsd1 p ts αs hts, ?_, ?_, ?_⟩
    · have h1 := s81s_map_comp hsnd (s81p_vec_meas hG0₀.1 ts αs)
      exact h1.trans (hlawG0 p ts αs hts)
    · have h1 := s81s_map_comp hfst (s81p_vec_meas hG1.1 ts αs)
      exact h1.trans (hlawG1 p ts αs hts)
    · ext i j
      simp only [Matrix.add_apply, Matrix.of_apply, add_sub_cancel]
  · -- cost of the initial block
    have hA : AEMeasurable (fun ζ : Ω' × (ℕ → ℝ) =>
        ‖processWindow m T 0 (fun t (z : Ω' × (ℕ → ℝ)) => Ip₀ t (π z.1)) ζ‖ₑ)
        (P'.prod (s81p_gamma (β⁻¹).toNNReal)) := (hIp1.aemeasurable hT.le).enorm
    have hB : AEMeasurable (fun ζ : Ω' × (ℕ → ℝ) =>
        ‖processWindow m T 0 (fun t (z : Ω' × (ℕ → ℝ)) => G0₀ t z.2) ζ‖ₑ)
        (P'.prod (s81p_gamma (β⁻¹).toNNReal)) := (hG01.aemeasurable hT.le).enorm
    refine (s81q_L2_sub_le hA hB).trans (add_le_add ?_ ?_)
    · exact (le_of_eq (s81s_L2_comp_fn hπ1 (processWindow m T 0 Ip₀) (hIp₀.aemeasurable hT.le))).trans
        hIp₀L2
    · exact (le_of_eq (s81s_L2_comp_fn hsnd (processWindow m T 0 G0₀) (hG0₀.aemeasurable hT.le))).trans
        hG0L2
  · -- cost of the old block
    have hf1 : AEMeasurable (fun w => processWindow m T 0 Op w - processWindow m T 0 G1 w) P' :=
      (hOp.aemeasurable hT.le).sub (hG1.aemeasurable hT.le)
    exact (le_of_eq (s81s_L2_comp_fn hfst _ hf1)).trans hcost
  · -- total
    have hE0 : 0 ≤ Real.exp (-(min ci w0) * u) := (Real.exp_pos _).le
    have hN0 : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hE : 0 ≤ Real.exp (-(min ci w0) * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)) := add_nonneg hE0 hN0
    have hδ0 : 0 ≤ deltaN d ((d : ℝ) / 2) N := s81q_deltaN_nonneg hN1
    have hδ2 : deltaN d ((d : ℝ) / 2) N ≤ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := s81s_deltaN_le hN1
    have hnE : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Real.exp (-(min ci w0) * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
      le_add_of_nonneg_left hE0
    have hex1 : Real.exp (-ci * u) ≤ Real.exp (-(min ci w0) * u) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left ci w0])
    have hex2 : Real.exp (-w0 * u) ≤ Real.exp (-(min ci w0) * u) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right ci w0])
    have a1 : ENNReal.ofReal (Ki * Real.exp (-ci * u)) ≤ ENNReal.ofReal (max Ki 0 *
        (Real.exp (-(min ci w0) * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) := by
      refine ENNReal.ofReal_le_ofReal ?_
      calc Ki * Real.exp (-ci * u) ≤ max Ki 0 * Real.exp (-ci * u) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
        _ ≤ max Ki 0 * Real.exp (-(min ci w0) * u) :=
            mul_le_mul_of_nonneg_left hex1 (le_max_right _ _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hN0) (le_max_right _ _)
    have a2 : ENNReal.ofReal (K0 * Real.exp (-w0 * u)) ≤ ENNReal.ofReal (max K0 0 *
        (Real.exp (-(min ci w0) * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) := by
      refine ENNReal.ofReal_le_ofReal ?_
      calc K0 * Real.exp (-w0 * u) ≤ max K0 0 * Real.exp (-w0 * u) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
        _ ≤ max K0 0 * Real.exp (-(min ci w0) * u) :=
            mul_le_mul_of_nonneg_left hex2 (le_max_right _ _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hN0) (le_max_right _ _)
    have a3 : ENNReal.ofReal (K1 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N)) ≤
        ENNReal.ofReal (3 * max K1 0 * (Real.exp (-(min ci w0) * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hx : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N := add_nonneg hN0 hδ0
      calc K1 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N) ≤
            max K1 0 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hx
        _ ≤ max K1 0 * (3 * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
        _ ≤ max K1 0 * (3 * (Real.exp (-(min ci w0) * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) :=
            mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
        _ = _ := by ring
    refine (add_le_add (add_le_add a1 a2) a3).trans (le_of_eq ?_)
    have p1 : 0 ≤ max Ki 0 * (Real.exp (-(min ci w0) * u) + (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
      mul_nonneg (le_max_right _ _) hE
    have p2 : 0 ≤ max K0 0 * (Real.exp (-(min ci w0) * u) + (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
      mul_nonneg (le_max_right _ _) hE
    have p3 : 0 ≤ 3 * max K1 0 * (Real.exp (-(min ci w0) * u) + (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) hE
    rw [← ENNReal.ofReal_add p1 p2, ← ENNReal.ofReal_add (add_nonneg p1 p2) p3]
    congr 1
    ring
  · -- identification of the initial term
    intro t ht α
    have f1 := hπ1.quasiMeasurePreserving.ae hX₀eq
    filter_upwards [f1] with ζ hζ
    have hζ' : X₀ (π ζ.1) = hX₀.mk X₀ (π ζ.1) := hζ
    show OscDual.coord (Ip₀ t (π ζ.1)) α = _
    rw [hIp₀id t ht α (π ζ.1), hζ', hlaw']
  · -- identification of the old current
    intro t ht α
    have ht0 : 0 ≤ t := ht.1
    obtain ⟨L, hL⟩ := s81q_path_coord_clm R ⟨t, ht⟩ α
    obtain ⟨Ωt, hΩt⟩ : ∃ Ωt : Ω' → ℝ, ∀ w, Ωt w = L (Yn w) := ⟨fun w => L (Yn w), fun _ => rfl⟩
    have hΩm : Measurable Ωt := by
      have : Ωt = fun w => L (Yn w) := funext hΩt
      rw [this]
      exact L.continuous.measurable.comp (hYnm.mono (ℱ'.le _) le_rfl)
    have hΩ : ∀ w, Ωt w = ∑' l, u11Coef d β ρ e m α l * Real.exp (-(b + t - τ / 2) * om l) *
        SeqL2.coord (Yn w) l := by
      intro w
      rw [hΩt, hL, s81q_ret_coord hd a β ha hβ hρth hdata ht₀ hL4 hτ hb hm hT R hRdef (Yn w) t ht α]
    obtain ⟨JO, hJO, hΩJ⟩ := s81q_old_phys hd ha hβ hρth hdata hm hcoef ht₀ hL4 hτ hb hN hR hcyl hprog
      hπ hfil hWb hub ht0 α Yn hYn2 hlink Ωt hΩm hΩ
    have hπm : ∀ s, @Measurable Ω' Ω (ℱ' s) (ℱ s) π := fun s => (measurable_iff_comap_le).2 (hfil s)
    have hkp := s81s_kernel_prog hd ha hβ m hm hρth hN P W X ℱ W' hF (show 0 ≤ u + t by linarith) α
    have hg : IsProgressiveL2 P' ℱ' (fun r w k => s81s_kernel d N a β m ρ X (u + t) α r (π w) k) :=
      ⟨isProgressive_comp_π hπm hkp.prog, fun T' => by
        rw [sqIntegralOn_comp_π hπm hπ hkp.prog T']; exact hkp.sq T'⟩
    have ek : (fun r w ia => Real.sqrt (2 / (N * β)) * HRS.MH.DualityRd.truncGradIntegrand
        (b + (u - b) + t) (fun r' => propagatorW (critCoeff d a β ρ) r' (b + (u - b) + t)
          (oscTestFun m α)) (fun s z => X s (π z)) r w ia) =
        (fun r w k => s81s_kernel d N a β m ρ X (u + t) α r (π w) k) := by
      funext r w ia
      rw [show b + (u - b) + t = u + t by ring]
      by_cases hr : r ∈ Set.Icc (0 : ℝ) (u + t)
      · simp only [s81s_kernel, HRS.MH.DualityRd.truncGradIntegrand, hr, ↓reduceIte]
      · simp only [s81s_kernel, HRS.MH.DualityRd.truncGradIntegrand, hr, ↓reduceIte, mul_zero]
    rw [ek] at hJO
    have hlift := s81q_ito_lift P' (s81p_gamma (β⁻¹).toNNReal) ℱ' hWb hg hJO hub
    have hO1 : ∀ᵐ w ∂P', OscDual.coord (Op t w) α = Ωt w := by
      filter_upwards [hOp.2] with w hw
      have h1 := s81p_win_apply hw ⟨t, ht⟩
      have h2 : OscPath.at' (processWindow m T 0 Op w) ⟨t, ht⟩ = OscPath.at' (R (Yn w)) ⟨t, ht⟩ := by
        rw [hOpwin w]
      have h3 : Op t w = OscPath.at' (R (Yn w)) ⟨t, ht⟩ := by
        rw [← h2]; exact h1.symm
      rw [h3, hΩt, hL]
    have a1 := hfst.quasiMeasurePreserving.ae hO1
    have a2 := hfst.quasiMeasurePreserving.ae (show ∀ᵐ w ∂P', Ωt w = JO (u - b) w from hΩJ)
    filter_upwards [a1, a2, hlift] with z h1 h2 h3
    show OscDual.coord (Op t z.1) α = _
    rw [h1, h2]
    exact h3

end Old

section Main

variable {d : ℕ}

/-- **The glue (with `S81QOld`).**  `S81PBlocks` follows from the initial/old interface `S81QOld` and `weighted_critical_forcing`; this is the proof of `s81s_blocks`
with the identification of the initial term used `Q₂`-almost everywhere (one `filter_upwards` entry added). -/
theorem s81q_blocks_of (hOld : S81QOld) (hforce : type_of% @HRS.Whole.weighted_critical_forcing) :
    S81PBlocks := by
  classical
  intro d hd a β ha hβ m hm T hT
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hρth : IsThermalEquilibrium d ((d : ℝ) / 2) a β (thermalDensity d ((d : ℝ) / 2) a β) :=
    HRS.Whole.S71.s71_thermal_equilibrium hd hs0 hsd a β ha hβ
  obtain ⟨e, om, b, hdata, hcoef, hb, C, c, u0, hc, hbu0, hOldN⟩ := hOld hd a β ha hβ m hm T hT
  obtain ⟨CR, hCR⟩ := s81s_recent_block hd a β ha hβ m hm T b hT hb
  obtain ⟨CF, hCF⟩ := hforce hd a β ha hβ m hm T hT
  refine ⟨e, om, hdata, hcoef, max C 0 + max CR 0 + max CF 0, c, u0, hc, hb.trans hbu0, ?_⟩
  intro N hN Ω _ P _ X₀ W X hR u hu
  have hN1 : 1 ≤ N := by omega
  have hu0 : 0 ≤ u := (hb.trans hbu0).trans hu
  have hbu : b ≤ u := hbu0.trans hu
  obtain ⟨ℱ, W', hF⟩ := hR.filtered
  obtain ⟨hR0, hF0⟩ := s81s_canonical_W0 hR ℱ W' hF
  have hcyl : IsCylindricalBrownian P ℱ (fun t z (ia : Fin N × Fin d) => s81s_W0 d N W' t z ia.1 ia.2) := by
    rw [s81s_W0_coord]; exact HRS.GF.gfb3_isCylindricalBrownian_of_filtration hF.brownian
  obtain ⟨Ω₁, mΩ₁, Q₁, hQ₁, π₁, ℱ₁, W₁, hπ₁, hfil₁, hcyl₁, hF₁, Ip, Op, G0, G1, S0, S1, ε₀, ε₁, hIp, hOp,
    hG0, hG1, hm0, hm1, hind01, hS01, hb0, hb1, hεs, hIpc, hOpc⟩ :=
    hOldN N hN P X₀ (s81s_W0 d N W') X hR0 ℱ W' hcyl hF0 u hu
  haveI := hQ₁
  have hR1 := s81s_canonical_comp hπ₁ hR0 ℱ₁ W₁ hF₁
  obtain ⟨M, hM, Ω₂, mΩ₂, Q₂, hQ₂, π₂, Rp, G2, hπ₂, hRpdef, hRp, hG2, hind2, hfdd2, hL2R⟩ :=
    hCR (thermalDensity d ((d : ℝ) / 2) a β) hρth N hN Q₁ (fun z => X₀ (π₁ z))
      (fun t z => s81s_W0 d N W' t (π₁ z)) (fun t z => X t (π₁ z)) hR1 ℱ₁ W₁ hcyl₁ hF₁ (u - b).toNNReal
  haveI := hQ₂
  set h : ℝ≥0 := (u - b).toNNReal with hhdef
  have hh : (h : ℝ) = u - b := Real.coe_toNNReal _ (by linarith)
  have hπF : MeasurePreserving (fun ζ => π₁ (π₂ ζ)) Q₂ P := hπ₁.comp hπ₂
  have hmd : (d : ℝ) < m := by
    have : ((wholeSpaceIndex d : ℕ) : ℝ) = 24 * d + 240 := by unfold wholeSpaceIndex; push_cast; ring
    linarith
  -- the processes on the final space
  set Ip' : ℝ → Ω₂ → OscDual d m := fun t ζ => Ip t (π₂ ζ) with hIp'def
  set Op' : ℝ → Ω₂ → OscDual d m := fun t ζ => Op t (π₂ ζ) with hOp'def
  set G0' : ℝ → Ω₂ → OscDual d m := fun t ζ => G0 t (π₂ ζ) with hG0'def
  set G1' : ℝ → Ω₂ → OscDual d m := fun t ζ => G1 t (π₂ ζ) with hG1'def
  set A : ℝ → Ω₂ → OscDual d m := fun t ζ => zetaB m (P.map (X (Real.toNNReal (u + t))))
    (X (Real.toNNReal (u + t)) (π₁ (π₂ ζ))) with hAdef
  set Fp : ℝ → Ω₂ → OscDual d m := fun t ζ => Ip' t ζ + Op' t ζ + Rp t ζ - A t ζ with hFpdef
  have hIp' : S81PProc Q₂ T Ip' := s81s_proc_comp hπ₂ hIp
  have hOp' : S81PProc Q₂ T Op' := s81s_proc_comp hπ₂ hOp
  have hG0' : S81PProc Q₂ T G0' := s81s_proc_comp hπ₂ hG0
  have hG1' : S81PProc Q₂ T G1' := s81s_proc_comp hπ₂ hG1
  have hA : S81PProc Q₂ T A := s81s_proc_comp hπF (s81s_zeta_proc hd m hmd hN1 T u hu0 hR)
  have hFp : S81PProc Q₂ T Fp := ((hIp'.add hOp').add hRp).sub hA
  -- the Duhamel decomposition of the window
  have hduh : ∀ᵐ ζ ∂Q₂, zetaPathW m T u P X (π₁ (π₂ ζ)) = processWindow m T 0 Ip' ζ +
      processWindow m T 0 Op' ζ + processWindow m T 0 Rp ζ - processWindow m T 0 Fp ζ := by
    filter_upwards [hIp'.2, hOp'.2, hRp.2, hA.2] with ζ h1 h2 h3 h4
    have e1 : zetaPathW m T u P X (π₁ (π₂ ζ)) = processWindow m T 0 A ζ := by
      unfold zetaPathW processWindow
      refine HRS.Whole.S79.s79p_windowPathOf_congr T u 0 _ _ (fun t ht => ?_)
      simp only [hAdef, zero_add]
    have e2 : processWindow m T 0 Fp ζ = processWindow m T 0 Ip' ζ + processWindow m T 0 Op' ζ +
        processWindow m T 0 Rp ζ - processWindow m T 0 A ζ := by
      unfold processWindow
      simp only [hFpdef]
      rw [s81p_win_sub (f := fun t => Ip' t ζ + Op' t ζ + Rp t ζ) (g := fun t => A t ζ)
        ((h1.add h2).add h3) h4, s81p_win_add (f := fun t => Ip' t ζ + Op' t ζ) (g := fun t => Rp t ζ)
        (h1.add h2) h3, s81p_win_add (f := fun t => Ip' t ζ) (g := fun t => Op' t ζ) h1 h2]
    rw [e1, e2]
    abel
  -- independence of the three blocks
  set G2' : ℝ → Ω₂ → OscDual d m := G2 with hG2'
  set Gs : Fin 3 → ℝ → Ω₂ → OscDual d m := ![G0', G1', G2] with hGsdef
  have hGs : ∀ i, S81PProc Q₂ T (Gs i) := by
    intro i; fin_cases i
    · exact hG0'
    · exact hG1'
    · exact hG2
  have h𝒢 : (ℱ₁ (h : ℝ)).comap π₂ ≤ mΩ₂ :=
    (MeasurableSpace.comap_mono (ℱ₁.le _)).trans hπ₂.measurable.comap_le
  have hG0m : Measurable (fun ζ (t : ℝ) => G0 t ζ) := measurable_pi_iff.2 hG0.1
  have hG1m : Measurable (fun ζ (t : ℝ) => G1 t ζ) := measurable_pi_iff.2 hG1.1
  have hindep : iIndepFun (fun (i : Fin 3) (ζ : Ω₂) (t : ℝ) => Gs i t ζ) Q₂ := by
    refine s81s_iIndep3 ((ℱ₁ (h : ℝ)).comap π₂) (fun (i : Fin 3) (ζ : Ω₂) (t : ℝ) => Gs i t ζ) h𝒢 ?_ ?_
      (measurable_pi_iff.2 hG2.1) ?_ ?_
    · have := s81s_meas_comap_proc (ℱ₁ (h : ℝ)) π₂ G0 (by rw [hh]; exact hm0)
      exact this
    · have := s81s_meas_comap_proc (ℱ₁ (h : ℝ)) π₂ G1 (by rw [hh]; exact hm1)
      exact this
    · exact s81s_indepFun_comp hπ₂ hG0m hG1m hind01
    · have e := s81s_comap_proc G2
      show Indep _ (MeasurableSpace.comap (fun ζ (t : ℝ) => G2 t ζ) inferInstance) Q₂
      rw [e]; exact hind2
  -- finite-dimensional laws and covariances
  set S2 : ∀ (p : ℕ), (Fin p → ℝ) → (Fin p → MultiIndex d) → Matrix (Fin p) (Fin p) ℝ :=
    fun p ts αs => Matrix.of fun i j => noiseCovW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β))
      β⁻¹ (b + ts i) (b + ts j) (oscTestFun m (αs i)) (oscTestFun m (αs j)) with hS2
  set Ss : Fin 3 → ∀ (p : ℕ), (Fin p → ℝ) → (Fin p → MultiIndex d) → Matrix (Fin p) (Fin p) ℝ :=
    ![S0, S1, S2] with hSs
  have hpsd : ∀ (i : Fin 3) (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d),
      (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) → (Ss i p ts αs).PosSemidef := by
    intro i p ts αs hts
    fin_cases i
    · exact (hS01 p ts αs hts).1
    · exact (hS01 p ts αs hts).2.1
    · exact (hfdd2 p ts αs hts).1
  have hlaw : ∀ (i : Fin 3) (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d),
      (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) →
      Q₂.map (s81p_vec (Gs i) ts αs) = multivariateGaussian 0 (Ss i p ts αs) := by
    intro i p ts αs hts
    fin_cases i
    · have h1 := (hS01 p ts αs hts).2.2.1
      have h2 := s81s_map_comp hπ₂ (s81p_vec_meas hG0.1 ts αs)
      exact h2.trans h1
    · have h1 := (hS01 p ts αs hts).2.2.2.1
      have h2 := s81s_map_comp hπ₂ (s81p_vec_meas hG1.1 ts αs)
      exact h2.trans h1
    · exact (hfdd2 p ts αs hts).2
  have hsum : ∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) →
      Ss 0 p ts αs + Ss 1 p ts αs + Ss 2 p ts αs =
        s81p_Qmat d β (thermalDensity d ((d : ℝ) / 2) a β) e om m ts αs := by
    intro p ts αs hts
    ext i j
    have h01 := congrFun (congrFun (hS01 p ts αs hts).2.2.2.2 i) j
    have hn := s81w2_noiseCov_spectral hd ha hβ hρth hm hdata hcoef (αs i) (αs j)
      (t := b + ts i) (t' := b + ts j) (by linarith [(hts i).1]) (by linarith [(hts j).1])
    have e1 : |(b + ts i) - (b + ts j)| = |ts i - ts j| := by congr 1; ring
    have e2 : (b + ts i) + (b + ts j) = 2 * b + ts i + ts j := by ring
    rw [e1, e2] at hn
    have g : (Ss 0 p ts αs + Ss 1 p ts αs + Ss 2 p ts αs) i j = S0 p ts αs i j + S1 p ts αs i j +
        noiseCovW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) β⁻¹ (b + ts i) (b + ts j)
          (oscTestFun m (αs i)) (oscTestFun m (αs j)) := rfl
    rw [g]
    have h01' : S0 p ts αs i j + S1 p ts αs i j =
        s81w2_Q d β (thermalDensity d ((d : ℝ) / 2) a β) e om m (αs i) (αs j) (2 * b + ts i + ts j) := by
      simpa only [Matrix.add_apply, Matrix.of_apply] using h01
    show _ = s81w2_Q d β (thermalDensity d ((d : ℝ) / 2) a β) e om m (αs i) (αs j) |ts i - ts j|
    linarith
  -- the recent block: Hilbert-Schmidt integrand and physical identification
  obtain ⟨Cin, hCin⟩ := s81s_linear_input hd ha hβ
  obtain ⟨Crec, hCrec⟩ := s81s_finite_noise hd a β ha hβ m hm (b + T) (by linarith) Cin
  have hR1h := HRS.Whole.BreakdownS81.s81b_isCanonical_shift hR1 h
  have hWh := s81s_cyl_shift_vec hcyl₁ h
  have hFh := HRS.Whole.BreakdownS81.s81b_filtered_shift hF₁ h
  have hprog : ∀ i : Fin N, IsProgressive (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ₁ h)
      (fun r z => HRS.Whole.S79.s79p_shiftX h (fun t z => X t (π₁ z)) (Real.toNNReal r) z i) :=
    fun i => s81s_prog_coord hFh.progressive i
  have hlin : ∀ t ∈ Set.Icc (0 : ℝ) (b + T), LinearInputBounds d ((d : ℝ) / 2) N
      (HRS.Whole.withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)) Cin Q₁
      (HRS.Whole.S79.s79p_shiftX h (fun t z => X t (π₁ z)) (Real.toNNReal t)) :=
    fun t _ => hCin _ hρth N hN Q₁ _ _ _ hR1h (Real.toNNReal t)
  obtain ⟨hHS, -⟩ := hCrec _ hρth N hN Q₁ (fun z => X h (π₁ z))
    (HRS.Whole.S79.s79p_shiftW h (fun t z => s81s_W0 d N W' t (π₁ z)))
    (HRS.Whole.S79.s79p_shiftX h (fun t z => X t (π₁ z))) hR1h
    (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ₁ h) hWh hprog hlin
  have hphys := fun t (ht : t ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) =>
    s81s_recent_phys hd ha hβ m hm T b hT hb hρth hN Q₁ (fun t z => s81s_W0 d N W' t (π₁ z))
      (fun t z => X t (π₁ z)) ℱ₁ W₁ hcyl₁ hF₁ h M hHS hM t ht α
  -- transport of the Itô integrals to the original space
  have hπ₁m : ∀ t, @Measurable Ω₁ Ω (ℱ₁ t) (ℱ t) π₁ := fun t => (measurable_iff_comap_le).2 (hfil₁ t)
  have hWbQ : IsBrownianFiltration Q₁ ℱ₁ (fun t z (k : Fin N × Fin d) => W' t (π₁ z) k) :=
    s81s_brownian_of_cyl hcyl₁
  have hcomp : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ' ∂Q₁, ∀ s : ℝ,
      itoIntegral Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => s81s_W0 d N W' t (π₁ z) ia.1 ia.2)
        (s81s_kernel d N a β m (thermalDensity d ((d : ℝ) / 2) a β) (fun t z => X t (π₁ z)) (u + t) α) s ζ' =
      itoIntegral P ℱ W' (s81s_kernel d N a β m (thermalDensity d ((d : ℝ) / 2) a β) X (u + t) α) s (π₁ ζ') :=
    fun t ht α => itoIntegral_comp_π hπ₁m hπ₁ hF.brownian hWbQ
      (s81s_kernel_prog hd ha hβ m hm hρth hN P W X ℱ W' hF (show 0 ≤ u + t by linarith [ht.1]) α)
  -- the forcing
  obtain ⟨-, -, -, hCFb⟩ := hCF _ hρth N hN P X₀ W X hR
  obtain ⟨Fz, hFzm, hFzid, hFzL2⟩ := s81s_forcing_P hd ha hβ m hm T hT hρth hN P X₀ (s81s_W0 d N W') X hR0
    ℱ W' hF0 hu0 (hCFb u hu0)
  have hX0 : ∀ᵐ ζ ∂P, X 0 ζ = X₀ ζ := (hR.solution 0).init
  have hlaw0 : law P (X 0) = law P X₀ := Measure.map_congr hX0
  have hneg : ∀ (x : OscDual d m) (α' : MultiIndex d), OscDual.coord (-x) α' = - OscDual.coord x α' := fun x α' => by
    rw [← neg_one_smul ℝ x, OscDual.coord_smul]; ring
  have hFid : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂Q₂,
      OscDual.coord (Fp t ζ) α = OscDual.coord (Fz t (π₁ (π₂ ζ))) α := by
    intro t ht α
    have ht0 : min t T = t := min_eq_left ht.2
    have ht1 : max 0 t = t := max_eq_right ht.1
    have hhe : (h : ℝ) + (b + t) = u + t := by rw [hh]; ring
    have f2 := hπ₂.quasiMeasurePreserving.ae (hOpc t ht α)
    have f3 := hπ₂.quasiMeasurePreserving.ae (hphys t ht α)
    have f5 := hπ₂.quasiMeasurePreserving.ae (hcomp t ht α)
    have f6 := hπF.quasiMeasurePreserving.ae (hFzid t ht α)
    have f7 := hπF.quasiMeasurePreserving.ae hX0
    have f1 := hπ₂.quasiMeasurePreserving.ae (hIpc t ht α)
    filter_upwards [f1, f2, f3, f5, f6, f7] with ζ g1 g2 g3 g5 g6 g7
    have gR : OscDual.coord (Rp t ζ) α = OscDual.coord (reconstructPath m (b + T) M (π₂ ζ) (b + t)) α := by
      rw [hRpdef t ζ, ht0, ht1]; rfl
    have g3' : OscDual.coord (reconstructPath m (b + T) M (π₂ ζ) (b + t)) α =
        itoIntegral Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => s81s_W0 d N W' t (π₁ z) ia.1 ia.2)
          (s81s_kernel d N a β m (thermalDensity d ((d : ℝ) / 2) a β) (fun t z => X t (π₁ z)) (u + t) α)
          (u + t) (π₂ ζ) -
        itoIntegral Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => s81s_W0 d N W' t (π₁ z) ia.1 ia.2)
          (s81s_kernel d N a β m (thermalDensity d ((d : ℝ) / 2) a β) (fun t z => X t (π₁ z)) (u + t) α)
          (u - b) (π₂ ζ) := by
      rw [← hh, ← hhe]; exact g3
    have gF : OscDual.coord (Fp t ζ) α = OscDual.coord (Ip t (π₂ ζ)) α + OscDual.coord (Op t (π₂ ζ)) α +
        OscDual.coord (Rp t ζ) α - OscDual.coord (A t ζ) α := by
      show OscDual.coord (Ip' t ζ + Op' t ζ + Rp t ζ - A t ζ) α = _
      rw [sub_eq_add_neg, OscDual.coord_add, OscDual.coord_add, OscDual.coord_add, hneg]
      ring
    have gA : OscDual.coord (A t ζ) α = _ := g6
    rw [hlaw0, g7] at gA
    have g5' := g5 (u + t)
    rw [gF, gR, g3', g1, g2, gA, ← g5']
    ring
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  obtain ⟨s, hs⟩ := TopologicalSpace.exists_dense_seq (Set.Icc (0 : ℝ) T)
  have hFseq : ∀ᵐ ζ ∂Q₂, ∀ n : ℕ, ‖Fp (s n) ζ‖ₑ = ‖Fz (s n) (π₁ (π₂ ζ))‖ₑ := by
    refine ae_all_iff.2 fun n => ?_
    filter_upwards [ae_all_iff.2 (hFid (s n) (s n).2)] with ζ hζ
    rw [HRS.MS.GenPath.s56_enorm_eq_l2NormE, HRS.MS.GenPath.s56_enorm_eq_l2NormE]
    congr 1
    funext α
    exact hζ α
  have hbF : s81p_L2 Q₂ (fun ζ => processWindow m T 0 Fp ζ) ≤
      ENNReal.ofReal (CF * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
    refine le_trans ?_ (hFzL2 s)
    rw [s81p_L2_eq]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    have hg : Measurable (fun ζ => (⨆ n : ℕ, ‖Fz (s n) ζ‖ₑ) ^ 2) :=
      (Measurable.iSup fun n => (hFzm _).enorm).pow_const 2
    rw [← hπF.lintegral_comp hg]
    refine lintegral_mono_ae ?_
    filter_upwards [hFp.2, hFseq] with ζ hc hq
    have h1 := s81s_sup_dense hT Fp ζ hc s hs
    rw [show (⨆ n : ℕ, ‖Fp (s n) ζ‖ₑ) = ⨆ n : ℕ, ‖Fz (s n) (π₁ (π₂ ζ))‖ₑ from iSup_congr hq] at h1
    calc ‖processWindow m T 0 Fp ζ‖ₑ ^ (2 : ℝ) ≤ (⨆ n : ℕ, ‖Fz (s n) (π₁ (π₂ ζ))‖ₑ) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = (⨆ n : ℕ, ‖Fz (s n) (π₁ (π₂ ζ))‖ₑ) ^ 2 := ENNReal.rpow_two _
  -- the L² bounds
  have hf0 : AEMeasurable (fun ζ => processWindow m T 0 Ip ζ - processWindow m T 0 G0 ζ) Q₁ :=
    (hIp.aemeasurable hT.le).sub (hG0.aemeasurable hT.le)
  have hf1 : AEMeasurable (fun ζ => processWindow m T 0 Op ζ - processWindow m T 0 G1 ζ) Q₁ :=
    (hOp.aemeasurable hT.le).sub (hG1.aemeasurable hT.le)
  have hb0' : s81p_L2 Q₂ (fun ζ => processWindow m T 0 Ip' ζ - processWindow m T 0 G0' ζ) ≤ ε₀ :=
    le_trans (le_of_eq (s81s_L2_comp_fn hπ₂ _ hf0)) hb0
  have hb1' : s81p_L2 Q₂ (fun ζ => processWindow m T 0 Op' ζ - processWindow m T 0 G1' ζ) ≤ ε₁ :=
    le_trans (le_of_eq (s81s_L2_comp_fn hπ₂ _ hf1)) hb1
  have hE0 : 0 ≤ Real.exp (-c * u) := (Real.exp_pos _).le
  have hN0 : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have htot : ε₀ + ε₁ + ENNReal.ofReal (CR * (N : ℝ) ^ (-(1 / 2 : ℝ))) +
      ENNReal.ofReal (CF * (N : ℝ) ^ (-(1 / 2 : ℝ))) ≤ ENNReal.ofReal ((max C 0 + max CR 0 + max CF 0) *
        (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) := by
    have hE : 0 ≤ Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)) := add_nonneg hE0 hN0
    have hnE : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
      le_add_of_nonneg_left hE0
    have a1 : ε₀ + ε₁ ≤ ENNReal.ofReal (max C 0 * (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) :=
      hεs.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hE))
    have a2 : ENNReal.ofReal (CR * (N : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        ENNReal.ofReal (max CR 0 * (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) :=
      ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_max_left _ _) hN0).trans
        (mul_le_mul_of_nonneg_left hnE (le_max_right _ _)))
    have a3 : ENNReal.ofReal (CF * (N : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        ENNReal.ofReal (max CF 0 * (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) :=
      ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_max_left _ _) hN0).trans
        (mul_le_mul_of_nonneg_left hnE (le_max_right _ _)))
    refine (add_le_add (add_le_add a1 a2) a3).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) hE) (mul_nonneg (le_max_right _ _) hE),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (le_max_right _ _) hE) (mul_nonneg (le_max_right _ _) hE))
        (mul_nonneg (le_max_right _ _) hE)]
    congr 1
    ring
  refine ⟨Ω₂, mΩ₂, Q₂, hQ₂, fun ζ => π₁ (π₂ ζ), hπF, Ip', Op', Rp, Fp, Gs, Ss, ε₀, ε₁,
    ENNReal.ofReal (CR * (N : ℝ) ^ (-(1 / 2 : ℝ))), ENNReal.ofReal (CF * (N : ℝ) ^ (-(1 / 2 : ℝ))),
    hIp', hOp', hRp, hFp, hGs, hduh, hindep, hpsd, hlaw, hsum, hb0', hb1', hL2R, hbF, htot⟩

end Main

/-- **`S81PBlocks` from `weighted_critical_forcing` alone**: the initial, old and recent blocks plus the forcing bound. -/
theorem s81q_blocks (hforce : type_of% @HRS.Whole.weighted_critical_forcing) : S81PBlocks :=
  s81q_blocks_of s81q_old hforce

end HRS.Whole.S81Q
