import HRS.Equilibrium.Parametrix.Packets
import HRS.Equilibrium.Parametrix.PX5AuxI
import HRS.Equilibrium.Parametrix.PXSAuxGen
import HRS.Equilibrium.Parametrix.PXSAuxGlue

/-!
# Packet PXS: the smoothness bootstrap `parx_psi_smooth`

Route (docs/external/parametrix-plan.md, section 8.2): enlarge the number of defect steps
`L = parxL d J` to `L₁ = parxL d J'`; `Δ = ∑_{L ≤ j < L₁} 𝒩R_j` is a doubly centred `C^{J+2}`
kernel with `(𝒜_x + 𝒜_y)Δ = R_{L₁} - R_L`, so the left-inverse clause of `PairInverseSpec` gives
`Ψ_{R_{L₁}} - Ψ_{R_L} = -Δ`, i.e. `ψ_{L₁} = ψ_L` off the diagonal.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem pxS_isCk2_mono {R : Torus d → Torus d → ℝ} {J J' : ℕ} (h : J ≤ J') (hR : PDE.IsCk2 J' R) :
    PDE.IsCk2 J R := by
  unfold PDE.IsCk2 at hR ⊢
  exact hR.of_le (by exact_mod_cast h)

theorem pxS_isCk2_sum {m : ℕ} (n : ℕ) (G : ℕ → Torus d → Torus d → ℝ)
    (h : ∀ j < n, PDE.IsCk2 m (G j)) : PDE.IsCk2 m (fun x y => ∑ j ∈ Finset.range n, G j x y) := by
  unfold PDE.IsCk2
  have : PDE.lift2 (fun x y => ∑ j ∈ Finset.range n, G j x y) =
      fun p => ∑ j ∈ Finset.range n, PDE.lift2 (G j) p := rfl
  rw [this]
  exact ContDiff.sum fun j hj => h j (Finset.mem_range.mp hj)

theorem pxS_cont_slice1 {R : Torus d → Torus d → ℝ} {m : ℕ} (hR : PDE.IsCk2 m R) (y : Torus d) :
    Continuous (fun x => R x y) :=
  Torus.continuous_of_continuous_lift (PDE.MFPair.isCk_slice m R hR y).continuous

theorem pxS_cont_slice2 {R : Torus d → Torus d → ℝ} {m : ℕ} (hR : PDE.IsCk2 m R) (x : Torus d) :
    Continuous (fun y => R x y) :=
  Torus.continuous_of_continuous_lift (PDE.MFPair.isCk_slice2 m R hR x).continuous

/-- `diagExt` does not change double centring. -/
theorem pxS_dc_diagExt (hd : 0 < d) {F : Torus d → Torus d → ℝ}
    (hF : PDE.DoublyCentered (withDensityReal ρ) F) :
    PDE.DoublyCentered (withDensityReal ρ) (diagExt F) := by
  have hae : ∀ y : Torus d, ∀ᵐ w ∂(withDensityReal ρ), w ≠ y := by
    intro y
    have h0 : (withDensityReal ρ) {y} = 0 :=
      withDensity_absolutelyContinuous _ _ (volume_singleton_torus hd y)
    have := (measure_eq_zero_iff_ae_notMem (μ := withDensityReal ρ) (s := {y})).1 h0
    filter_upwards [this] with w hw using hw
  refine ⟨fun y => ?_, fun x => ?_⟩
  · have := hF.1 y
    unfold pair at this ⊢
    rw [← this]
    refine integral_congr_ae ?_
    filter_upwards [hae y] with w hw
    simp [diagExt, hw]
  · have := hF.2 x
    unfold pair at this ⊢
    rw [← this]
    refine integral_congr_ae ?_
    filter_upwards [hae x] with w hw
    simp [diagExt, Ne.symm hw]

theorem pxS_dc_comb (H : ParxHyp d s V β ρ) {A B : Torus d → Torus d → ℝ} {m : ℕ}
    (hA : PDE.IsCk2 m A) (hB : PDE.IsCk2 m B) (a b : ℝ)
    (hAc : PDE.DoublyCentered (withDensityReal ρ) A) (hBc : PDE.DoublyCentered (withDensityReal ρ) B) :
    PDE.DoublyCentered (withDensityReal ρ) (fun x y => a * A x y + b * B x y) := by
  have hρ := H.rho_smooth
  have hρc : Continuous ρ := PDE.MFAux.continuous_of_isCk (PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1)
  have key : ∀ (u v : Torus d → ℝ), Continuous u → Continuous v →
      pair (withDensityReal ρ) u = 0 → pair (withDensityReal ρ) v = 0 →
      pair (withDensityReal ρ) (fun z => a * u z + b * v z) = 0 := by
    intro u v hu hv hu0 hv0
    rw [PDE.MFAdjoint.pair_mu hρ.density] at hu0 hv0 ⊢
    have e : (fun z => ρ z * (a * u z + b * v z)) = fun z => a * (ρ z * u z) + b * (ρ z * v z) := by
      funext z; ring
    rw [e]
    have h1 : Integrable (fun z => a * (ρ z * u z)) :=
      (PDE.MFAdjoint.integrable_of_cont (hρc.mul hu)).const_mul a
    have h2 : Integrable (fun z => b * (ρ z * v z)) :=
      (PDE.MFAdjoint.integrable_of_cont (hρc.mul hv)).const_mul b
    rw [integral_add h1 h2, integral_const_mul, integral_const_mul, hu0, hv0]
    ring
  exact ⟨fun y => key _ _ (pxS_cont_slice1 hA y) (pxS_cont_slice1 hB y) (hAc.1 y) (hBc.1 y),
    fun x => key _ _ (pxS_cont_slice2 hA x) (pxS_cont_slice2 hB x) (hAc.2 x) (hBc.2 x)⟩

theorem pxS_dc_sum (H : ParxHyp d s V β ρ) {m : ℕ} (n : ℕ) (G : ℕ → Torus d → Torus d → ℝ)
    (hG : ∀ j < n, PDE.IsCk2 m (G j))
    (hc : ∀ j < n, PDE.DoublyCentered (withDensityReal ρ) (G j)) :
    PDE.DoublyCentered (withDensityReal ρ) (fun x y => ∑ j ∈ Finset.range n, G j x y) := by
  induction n with
  | zero =>
    refine ⟨fun y => ?_, fun x => ?_⟩ <;> simp [pair]
  | succ n ih =>
    have h1 := ih (fun j hj => hG j (by omega)) (fun j hj => hc j (by omega))
    have h2 := pxS_dc_comb H (pxS_isCk2_sum n G fun j hj => hG j (by omega)) (hG n (by omega))
      1 1 h1 (hc n (by omega))
    convert h2 using 2 with x y
    simp [Finset.sum_range_succ]

theorem pxS_parxL_cast (J : ℕ) : (parxL d J : ℝ) = 2 * J + d + 6 := by
  unfold parxL; push_cast; ring

/-- Common conormal class of `𝒩R_k`, `L ≤ k < L₁`: order `s - L/2 - 2`, log power `1`, `J + 3` derivatives. -/
theorem pxS_N_class (H : ParxHyp d s V β ρ) (J L₁ : ℕ) (f : Torus d → ℝ) (hf : Torus.IsSmooth f)
    (k : ℕ) (hk1 : parxL d J ≤ k) (hk2 : k < L₁) :
    ∃ B : ℝ, 0 ≤ B ∧ Conormal (s - (parxL d J : ℝ) / 2 - 2) 1 (J + 3) B
      (newtonOp d β ρ (parxR d s V β ρ f k)) := by
  obtain ⟨C, hC0, hC⟩ := parxN_conormal H (2 * L₁ + J + 3) k (by omega)
  have h := hC f hf
  have hB0 : 0 ≤ C * posSeminorm (2 * L₁ + J + 3 + 2) f := mul_nonneg hC0 (posSeminorm_nonneg' _ _)
  refine ⟨C * posSeminorm (2 * L₁ + J + 3 + 2) f, hB0, ?_⟩
  refine ConormalL.mono h hB0 ?_ ?_ (by omega) le_rfl
  · have : (parxL d J : ℝ) ≤ k := by exact_mod_cast hk1
    linarith
  · intro c
    show (0 + if s - (k : ℝ) / 2 - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) ≤ 1
    split_ifs <;> simp

theorem pxS_key (H : ParxHyp d s V β ρ) (J J' : ℕ) (hJJ' : J ≤ J') (hspec : PairInverseSpec H J)
    (f : Torus d → ℝ) (hf : Torus.IsSmooth f) (x y : Torus d) (hxy : x ≠ y) :
    parxPsi d s V β ρ f (parxL d J) x y +
        PDE.pairInverse H.dyn ρ (diagExt (parxR d s V β ρ f (parxL d J))) x y =
      parxPsi d s V β ρ f (parxL d J') x y +
        PDE.pairInverse H.dyn ρ (diagExt (parxR d s V β ρ f (parxL d J'))) x y := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) H.two_le
  obtain ⟨Cinv, hCinv, -, hlin, -, hleft⟩ := hspec
  set L := parxL d J with hL
  set L₁ := parxL d J' with hL₁
  have hLL : L ≤ L₁ := by rw [hL, hL₁]; unfold parxL; omega
  obtain ⟨n, hn⟩ : ∃ n, L₁ = L + n := ⟨L₁ - L, by omega⟩
  obtain ⟨C₁, G₁⟩ := parx_gap_proof H J'
  obtain ⟨C₀, G₀⟩ := parx_gap_proof H J
  obtain ⟨hA, hAdc, -, -⟩ := G₁.remainder_ck f hf
  obtain ⟨hB, hBdc, -, -⟩ := G₀.remainder_ck f hf
  have hA' := pxS_isCk2_mono hJJ' hA
  -- the common conormal class of `𝒩R_{L+j}`
  have hN : ∀ j < n, ∃ Bj : ℝ, 0 ≤ Bj ∧ Conormal (s - (L : ℝ) / 2 - 2) 1 (J + 3) Bj
      (newtonOp d β ρ (parxR d s V β ρ f (L + j))) :=
    fun j hj => pxS_N_class H J L₁ f hf (L + j) (by omega) (by omega)
  set F : ℕ → Torus d → Torus d → ℝ := fun j => newtonOp d β ρ (parxR d s V β ρ f (L + j)) with hF
  have hσ : s - (L : ℝ) / 2 - 2 + (((J + 2 : ℕ) : ℝ) + 1) < 0 := by
    rw [hL, pxS_parxL_cast, H.crit]; push_cast; linarith
  obtain ⟨Ce, -, hCe⟩ := conormal_extend H.two_le (J + 2) (s - (L : ℝ) / 2 - 2) 1 hσ
  have hFc : ∀ j < n, PDE.IsCk2 (J + 2) (diagExt (F j)) := by
    intro j hj
    obtain ⟨Bj, hBj0, hBj⟩ := hN j hj
    exact (hCe Bj (F j) hBj0 hBj).1
  have hFdc : ∀ j < n, PDE.DoublyCentered (withDensityReal ρ) (diagExt (F j)) := by
    intro j hj
    obtain ⟨C, hC0, hC⟩ := parxR_conormal H (2 * L₁ + J + 3) (L + j) (by omega)
    obtain ⟨h1, -, -⟩ := hC f hf
    have hσ' : s - ((L + j : ℕ) : ℝ) / 2 < d := by
      have : (0 : ℝ) ≤ ((L + j : ℕ) : ℝ) / 2 := by positivity
      linarith [H.s_lt]
    exact pxS_dc_diagExt hd0 (newton_doublyCentered H hσ' h1)
  set Δ' : Torus d → Torus d → ℝ := fun x y => ∑ j ∈ Finset.range n, diagExt (F j) x y with hΔ'
  have hΔc : PDE.IsCk2 (J + 2) Δ' := pxS_isCk2_sum n _ hFc
  have hΔdc : PDE.DoublyCentered (withDensityReal ρ) Δ' := pxS_dc_sum H n _ hFc hFdc
  set A := diagExt (parxR d s V β ρ f L₁) with hAdef
  set B := diagExt (parxR d s V β ρ f L) with hBdef
  set R' : Torus d → Torus d → ℝ := fun x y => 1 * A x y + (-1) * B x y with hR'
  have hR'c : PDE.IsCk2 J R' := by
    unfold PDE.IsCk2 at hA' hB ⊢
    have : PDE.lift2 R' = fun p => 1 * PDE.lift2 A p + (-1) * PDE.lift2 B p := rfl
    rw [this]
    exact (contDiff_const.mul hA').add (contDiff_const.mul hB)
  have hR'dc : PDE.DoublyCentered (withDensityReal ρ) R' := pxS_dc_comb H hA' hB 1 (-1) hAdc hBdc
  have hΔ2 : PDE.IsCk2 2 Δ' := pxS_isCk2_mono (by omega) hΔc
  have hRcont : Continuous (fun p : Torus d × Torus d => R' p.1 p.2) :=
    PDE.MFPair.continuous_pair_of_continuous_lift2 hR'c.continuous
  -- off the diagonal: `(𝒜_x + 𝒜_y)Δ = R_{L₁} - R_L`
  have hσ2 : s - (L : ℝ) / 2 - 2 + 2 < d := by
    have : (0 : ℝ) ≤ (L : ℝ) / 2 := by positivity
    linarith [H.s_lt]
  have hoff : ∀ x y : Torus d, x ≠ y →
      projGen d s V β ρ (fun x' => Δ' x' y) x + projGen d s V β ρ (fun y' => Δ' x y') y = R' x y := by
    intro x y hxy
    have e1 : projGen d s V β ρ (fun x' => Δ' x' y) x =
        genFst d s V β ρ (fun x y => ∑ j ∈ Finset.range n, F j x y) x y :=
      pxS_projGen_congr hd0 (y := y) (fun z hz => by simp [hΔ', diagExt, hz]) x hxy
    have e2 : projGen d s V β ρ (fun y' => Δ' x y') y =
        genSnd d s V β ρ (fun x y => ∑ j ∈ Finset.range n, F j x y) x y :=
      pxS_projGen_congr hd0 (y := x) (fun z hz => by simp [hΔ', diagExt, Ne.symm hz]) y hxy.symm
    obtain ⟨g1, g2⟩ := gen_sum H hσ2 (b := 1) (m := J + 3) (by omega) n F (fun j hj => (hN j hj).imp fun B hB => hB.2) x y hxy
    rw [e1, e2, g1, g2, ← Finset.sum_add_distrib]
    have hstep : ∀ k, parxR d s V β ρ f (k + 1) x y = parxR d s V β ρ f k x y +
        genFst d s V β ρ (newtonOp d β ρ (parxR d s V β ρ f k)) x y +
        genSnd d s V β ρ (newtonOp d β ρ (parxR d s V β ρ f k)) x y := by
      intro k
      simp [parxR, defectOp, hxy]
    have hs : ∑ j ∈ Finset.range n, (genFst d s V β ρ (F j) x y + genSnd d s V β ρ (F j) x y) =
        parxR d s V β ρ f (L + n) x y - parxR d s V β ρ f L x y := by
      have := Finset.sum_range_sub (fun j => parxR d s V β ρ f (L + j) x y) n
      simp only [add_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show L + (j + 1) = (L + j) + 1 from by omega, hstep]
      simp only [hF]
      ring
    rw [hs]
    simp [hR', hAdef, hBdef, diagExt, hxy, hn]
    ring
  -- hence the equation everywhere (continuity), and the generator bridge
  have hall := pxS_pairGen_diag hd0 H hΔ2 hRcont hoff
  have heq : ∀ x y, PDE.centeredGen H.dyn ρ (fun x' => Δ' x' y) x +
      PDE.centeredGen H.dyn ρ (fun y' => Δ' x y') y = R' x y := by
    intro x y
    have c1 : Torus.IsCk 2 (fun x' => Δ' x' y) :=
      (PDE.MFPair.isCk_slice (J + 2) Δ' hΔc y).of_le (by exact_mod_cast (by omega : 2 ≤ J + 2))
    have c2 : Torus.IsCk 2 (fun y' => Δ' x y') :=
      (PDE.MFPair.isCk_slice2 (J + 2) Δ' hΔc x).of_le (by exact_mod_cast (by omega : 2 ≤ J + 2))
    rw [← congrFun (pxS_projGen_eq_centeredGen H _ c1) x,
      ← congrFun (pxS_projGen_eq_centeredGen H _ c2) y]
    exact hall x y
  have hinv := hleft Δ' R' hΔc hR'c hΔdc hR'dc heq
  have hlin' := hlin A B 1 (-1) hA' hB
  have h1 := congrFun (congrFun hinv x) y
  have h2 := congrFun (congrFun hlin' x) y
  have h3 : PDE.pairInverse H.dyn ρ R' x y = 1 * PDE.pairInverse H.dyn ρ A x y +
      (-1) * PDE.pairInverse H.dyn ρ B x y := h2
  have hΔxy : Δ' x y = ∑ j ∈ Finset.range n, F j x y := by
    simp [hΔ', diagExt, hxy]
  have hψ : parxPsi d s V β ρ f L₁ x y = parxPsi d s V β ρ f L x y + ∑ j ∈ Finset.range n, F j x y := by
    unfold parxPsi
    rw [hn, Finset.sum_range_add]
  have h4 : PDE.pairInverse H.dyn ρ B x y = PDE.pairInverse H.dyn ρ A x y + Δ' x y := by
    linarith
  rw [hψ, h4, hΔxy]
  ring

/-- **Smoothness bootstrap** (proof of `parx_psi_smooth`; the packet statement lives in `Packets.lean`,
which cannot import this file). -/
theorem parx_psi_smooth_proof (H : ParxHyp d s V β ρ) (J : ℕ) (hspec : PairInverseSpec H J)
    (f : Torus d → ℝ) (hf : Torus.IsSmooth f) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (lift2 (fun x y => parxPsi d s V β ρ f (parxL d J) x y +
        PDE.pairInverse H.dyn ρ (diagExt (parxR d s V β ρ f (parxL d J))) x y)) (offDiag d) := by
  rw [contDiffOn_infty]
  intro n
  obtain ⟨J₀, hJ₀⟩ := PDE.periodic_pair_inverse H.two_le s H.s_nonneg H.s_lt β H.beta_pos V
    H.V_smooth ρ H.thermal H.rho_smooth.smooth H.rho_smooth.pos (max n 2) (le_max_right _ _)
  set J' := max J J₀ with hJ'
  obtain ⟨C₁, G₁⟩ := parx_gap_proof H J'
  obtain ⟨hA, hAdc, -, -⟩ := G₁.remainder_ck f hf
  have hA₀ := pxS_isCk2_mono (le_max_right J J₀) hA
  obtain ⟨-, -, -, -, hΨA, -, -⟩ := hJ₀ _ hA₀ hAdc
  have hΨA' : ContDiff ℝ ((max n 2 : ℕ) : WithTop ℕ∞)
      (lift2 (fun x y => PDE.pairInverse H.dyn ρ (diagExt (parxR d s V β ρ f (parxL d J'))) x y)) := hΨA
  have h1 := parxPsi_smooth_offDiag H f hf (parxL d J')
  have h2 : ContDiffOn ℝ (n : WithTop ℕ∞) (lift2 (fun x y => parxPsi d s V β ρ f (parxL d J') x y +
      PDE.pairInverse H.dyn ρ (diagExt (parxR d s V β ρ f (parxL d J'))) x y)) (offDiag d) := by
    have h1' : ContDiffOn ℝ (n : WithTop ℕ∞) (lift2 (parxPsi d s V β ρ f (parxL d J'))) (offDiag d) :=
      h1.of_le (by exact_mod_cast le_top)
    have h3 : ContDiffOn ℝ (n : WithTop ℕ∞)
        (lift2 (fun x y => PDE.pairInverse H.dyn ρ (diagExt (parxR d s V β ρ f (parxL d J'))) x y))
        (offDiag d) :=
      (hΨA'.of_le (by exact_mod_cast le_max_left n 2)).contDiffOn
    exact h1'.add h3
  refine h2.congr fun p hp => ?_
  have hne : Torus.mk p.1 ≠ Torus.mk p.2 := hp
  exact pxS_key H J J' (le_max_left J J₀) hspec f hf _ _ hne

/-- The statement agrees verbatim with the packet `parx_psi_smooth`. -/
example := (@parx_psi_smooth_proof : type_of% @parx_psi_smooth)

end HRS.Parx

end
