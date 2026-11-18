import HRS.Equilibrium.LocalDivCenter
import HRS.Equilibrium.LocalDivTorus
open MeasureTheory Set Metric
noncomputable section
namespace HRS.LocalDivAux
variable {d : ℕ}

theorem eucDist_symm (x y : Torus d) : Torus.eucDist x y = Torus.eucDist y x := by
  unfold Torus.eucDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_sub_rev]

theorem hTransport_symm {s : ℝ} (hsd : s < d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (x y : Torus d) : hTransport d s f x y = hTransport d s f y x := by
  rw [hTransport_eq s f hf, hTransport_eq s f hf]
  have e : y - x = -(x - y) := by abel
  rw [e, HRS.PDE.periodicRieszGrad_neg hsd]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.neg_apply]; ring

theorem eucDist_mk_zero' {w : Euc d} (hw : ∀ i, |w i| ≤ 1 / 2) :
    Torus.eucDist (Torus.mk w) 0 = ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold Torus.eucDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ‖((Torus.mk w : Torus d) i - (0 : Torus d) i)‖ = |w i| := by
    have : ((Torus.mk w : Torus d) i - (0 : Torus d) i) = ((w i : ℝ) : UnitAddCircle) := by
      simp [Torus.mk]
    rw [this]
    refine (AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) one_ne_zero).2 ?_
    rw [abs_one]
    have := hw i
    linarith
  rw [h2, Real.norm_eq_abs]

theorem abs_le_half_of_cube {w : Euc d} (hw : w ∈ cube d) (i : Fin d) : |w i| ≤ 1 / 2 := by
  have := hw i
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

theorem rep_mem (z : Torus d) (i : Fin d) : 0 ≤ Torus.rep z i ∧ Torus.rep z i < 1 := by
  have := (AddCircle.equivIco (1 : ℝ) 0 (z i)).2
  simpa [Torus.rep] using this

theorem exists_small_rep (z : Torus d) : ∃ w : Euc d, (∀ i, |w i| ≤ 1 / 2) ∧ Torus.mk w = z := by
  refine ⟨WithLp.toLp 2 fun i => if Torus.rep z i ≤ 1 / 2 then Torus.rep z i else Torus.rep z i - 1,
    fun i => ?_, ?_⟩
  · have := rep_mem z i
    simp only
    split_ifs with hh
    · rw [abs_le]; constructor <;> linarith [this.1]
    · rw [abs_le]; constructor <;> linarith [this.2]
  · funext i
    have h := congrFun (Torus.mk_rep z) i
    simp only [Torus.mk] at h ⊢
    split_ifs with hh
    · exact h
    · rw [← h]
      simp [sub_eq_add_neg]

theorem h_bound_torus {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : Torus d, 0 < Torus.eucDist x y →
      |hTransport d s f x y| ≤ B * Torus.eucDist x y ^ (-s) := by
  obtain ⟨B, hB0, hB⟩ := h_bound hd hs0 hsd hf
  refine ⟨B, hB0, fun x y hxy => ?_⟩
  obtain ⟨w, hwi, hmk⟩ := exists_small_rep (y - x)
  have hy : y = x + Torus.mk w := by rw [hmk]; abel
  have hnorm : ‖w‖ = Torus.eucDist x y := by
    rw [← eucDist_mk_zero' hwi, hy, eucDist_shift]
  have hy' : hTransport d s f x y = hTransport d s f x (x + Torus.mk w) := by rw [← hy]
  rw [hy', ← hnorm]
  rw [← hnorm] at hxy
  exact hB x w hxy hwi


theorem integrableOn_cube_rpow (hd : 1 ≤ d) {a : ℝ} (ha : a < d) :
    IntegrableOn (fun w : Euc d => ‖w‖ ^ (-a)) (cube d) := by
  have hfin : 1 ≤ Module.finrank ℝ (Euc d) := by
    rw [finrank_euclideanSpace_fin]; exact hd
  have hball : IntegrableOn (fun w : Euc d => ‖w‖ ^ (-a)) (ball 0 ((d : ℝ) + 1)) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := a) hfin
      (by rw [finrank_euclideanSpace_fin]; exact ha) ?_
      ((measurable_norm.pow_const _).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
  refine hball.mono_set fun w hw => ?_
  have := cube_norm_le hw
  rw [mem_ball_zero_iff]
  linarith

/-- the truncated kernel -/
def hC (d : ℕ) (s : ℝ) (f : Torus d → ℝ) (ε : ℝ) (x y : Torus d) : ℝ :=
  if ε < Torus.eucDist x y then hTransport d s f x y else 0

theorem measurable_hC {s : ℝ} (hsd : s < d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (ε : ℝ) :
    Measurable (fun p : Torus d × Torus d => hC d s f ε p.1 p.2) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_eucDist)
    (measurable_hTransport hsd hf) measurable_const

theorem hC_symm {s : ℝ} (hsd : s < d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (ε : ℝ)
    (x y : Torus d) : hC d s f ε x y = hC d s f ε y x := by
  unfold hC
  rw [eucDist_symm x y, hTransport_symm hsd hf x y]

theorem hC_bound {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ε : ℝ), 0 < ε → ∀ x y : Torus d, |hC d s f ε x y| ≤ B * ε ^ (-s) := by
  obtain ⟨B, hB0, hB⟩ := h_bound_torus hd hs0 hsd hf
  refine ⟨B, hB0, fun ε hε x y => ?_⟩
  unfold hC
  split_ifs with h
  · exact (hB x y (hε.trans h)).trans
      (mul_le_mul_of_nonneg_left (rpow_neg_mono hε h.le hs0) hB0)
  · simp only [abs_zero]
    positivity

theorem hC_cube {s : ℝ} (ε : ℝ) (f : Torus d → ℝ) (x : Torus d) {w : Euc d} (hw : w ∈ cube d) :
    hC d s f ε x (x + Torus.mk w) =
      if ε < ‖w‖ then hTransport d s f x (x + Torus.mk w) else 0 := by
  unfold hC
  rw [eucDist_shift, eucDist_mk_zero hw]


theorem hC_cube_bound {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ε : ℝ), 0 < ε → ∀ (x : Torus d) (w : Euc d), w ∈ cube d →
      |hC d s f ε x (x + Torus.mk w)| ≤ B * ‖w‖ ^ (-s) := by
  obtain ⟨B, hB0, hB⟩ := h_bound_torus hd hs0 hsd hf
  refine ⟨B, hB0, fun ε hε x w hw => ?_⟩
  rw [hC_cube ε f x hw]
  split_ifs with h
  · have e : Torus.eucDist x (x + Torus.mk w) = ‖w‖ := by rw [eucDist_shift, eucDist_mk_zero hw]
    have := hB x (x + Torus.mk w) (by rw [e]; exact hε.trans h)
    rwa [e] at this
  · simp only [abs_zero]; positivity

theorem measurable_shift_mk (x : Torus d) : Measurable fun w : Euc d => x + Torus.mk w :=
  (measurable_const_add x).comp Torus.continuous_mk.measurable

section Main
variable {s : ℝ} {ρ φ : Torus d → ℝ}

theorem measurable_hx (hsd : s < d) (hφ : Torus.IsSmooth φ) (x : Torus d) :
    Measurable fun w : Euc d => hTransport d s φ x (x + Torus.mk w) := by
  have hp : Measurable fun w : Euc d => ((x, x + Torus.mk w) : Torus d × Torus d) :=
    Measurable.prodMk measurable_const (measurable_shift_mk x)
  have e : (fun w : Euc d => hTransport d s φ x (x + Torus.mk w)) =
      (fun p : Torus d × Torus d => hTransport d s φ p.1 p.2) ∘
        (fun w : Euc d => ((x, x + Torus.mk w) : Torus d × Torus d)) := rfl
  rw [e]
  exact (measurable_hTransport hsd hφ).comp hp

theorem measurable_ρx (hρ : SmoothPosDensity ρ) (x : Torus d) :
    Measurable fun w : Euc d => ρ (x + Torus.mk w) :=
  hρ.density.measurable.comp (measurable_shift_mk x)

theorem measurable_hC_slice (hsd : s < d) (hφ : Torus.IsSmooth φ) (ε : ℝ) (x : Torus d) :
    Measurable fun y => hC d s φ ε x y := by
  have e : (fun y => hC d s φ ε x y) =
      (fun p : Torus d × Torus d => hC d s φ ε p.1 p.2) ∘ (fun y : Torus d => (x, y)) := rfl
  rw [e]
  exact (measurable_hC hsd hφ ε).comp (Measurable.prodMk measurable_const measurable_id)

theorem inner_eq (hsd : s < d) (hρ : SmoothPosDensity ρ) (hφ : Torus.IsSmooth φ) {ε : ℝ}
    (x : Torus d) :
    ∫ y, hC d s φ ε x y ^ 2 ∂(withDensityReal ρ) =
      ∫ w in cube d, (if ε < ‖w‖ then ρ (x + Torus.mk w) *
        hTransport d s φ x (x + Torus.mk w) ^ 2 else 0) := by
  rw [integral_withDensityReal_eq ρ hρ.density.measurable hρ.density.nonneg]
  have hm : Measurable fun y => ρ y * hC d s φ ε x y ^ 2 :=
    hρ.density.measurable.mul
      (((measurable_hC hsd hφ ε).comp (measurable_const.prodMk measurable_id)).pow_const 2)
  rw [integral_shift_cube x _ hm]
  refine setIntegral_congr_fun measurableSet_cube fun w hw => ?_
  show ρ (x + Torus.mk w) * hC d s φ ε x (x + Torus.mk w) ^ 2 = _
  rw [hC_cube ε φ x hw]
  split_ifs <;> simp

theorem Q_formula (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : SmoothPosDensity ρ)
    (hφ : Torus.IsSmooth φ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : Torus d × Torus d, hC d s φ ε p.1 p.2 ^ 2
        ∂((withDensityReal ρ).prod (withDensityReal ρ)) =
      ∫ x, ρ x * ∫ w in cube d, (if ε < ‖w‖ then ρ (x + Torus.mk w) *
        hTransport d s φ x (x + Torus.mk w) ^ 2 else 0) := by
  have := isProb_withDensityReal hρ.density
  obtain ⟨B, hB0, hB⟩ := hC_bound hd hs0 hsd hφ
  have hint : Integrable (fun p : Torus d × Torus d => hC d s φ ε p.1 p.2 ^ 2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
    refine integrable_of_bdd_prod ((measurable_hC hsd hφ ε).pow_const 2)
      (C := (B * ε ^ (-s)) ^ 2) fun p => ?_
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hB ε hε p.1 p.2) 2
  rw [integral_prod _ hint,
    integral_withDensityReal_eq ρ hρ.density.measurable hρ.density.nonneg
      (fun x => ∫ y, hC d s φ ε x y ^ 2 ∂(withDensityReal ρ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ρ x * ∫ y, hC d s φ ε x y ^ 2 ∂(withDensityReal ρ) = _
  rw [inner_eq hsd hρ hφ x]


theorem uniform_estimate (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : SmoothPosDensity ρ)
    (hφ : Torus.IsSmooth φ) :
    ∃ δ K1 K2 : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ (x : Torus d) (ε : ℝ), 0 < ε → ε ≤ δ →
      |ρ x * (∫ w in cube d, (if ε < ‖w‖ then ρ (x + Torus.mk w) *
          hTransport d s φ x (x + Torus.mk w) ^ 2 else 0)) -
        ρ x ^ 2 * s ^ 2 * (HRS.sphereArea d / (d * (d + 2)) *
          ((hess φ x).trace ^ 2 + 2 * ∑ i, ∑ j, hess φ x i j ^ 2)) *
          ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - 2 * s)| ≤
        K1 + K2 * ∫ r in ε..δ, r ^ ((d : ℝ) - 2 * s) := by
  obtain ⟨C, δ0, hδ0, hδ01, hexp⟩ := h_expand hd hs0.le hsd hφ
  obtain ⟨Bh, hBh0, hBh⟩ := h_bound hd hs0.le hsd hφ
  obtain ⟨BH, hBH0, hBH⟩ := hess_bound hφ
  have hρc : Continuous ρ := PoleCavityAux.continuous_of_smoothPos hρ
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hρc.continuousOn
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR (Classical.arbitrary _) (mem_univ _))
  have hρle : ∀ x, ρ x ≤ R := fun x => by
    have := hR x (mem_univ x)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  obtain ⟨Lρ, hLρ0, hLρ⟩ := lip_shift hρ.smooth
  set δ : ℝ := min (δ0 / 2) (1 / 4) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hδδ0 : δ < δ0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨K1, K2, hK1, hK2, hmain⟩ := local_estimate (d := d) (by omega) hs0 (BH := BH)
    (C1 := |C|) (B := Bh) (Lρ := Lρ) (ρmax := R) hBH0 (abs_nonneg _) hBh0 hLρ0 hR0 hδpos hδ4
  refine ⟨δ, K1, K2, hδpos, hδ4, hK1, hK2, fun x ε hε hεδ => ?_⟩
  have hxm := measurable_hx hsd hφ x
  have hρm := measurable_ρx hρ x
  have key := hmain (hess φ x) (hess_isHermitian hφ x) (fun i j => hBH x i j) _ _ hxm hρm (ρ x)
    ?_ ?_ ?_ ⟨(hρ.pos x).le, hρle x⟩ ?_ ε hε hεδ
  · have e : ρ x * (∫ w in cube d, (if ε < ‖w‖ then ρ (x + Torus.mk w) *
          hTransport d s φ x (x + Torus.mk w) ^ 2 else 0)) =
        ∫ w in cube d, (if ε < ‖w‖ then ρ x * ρ (x + Torus.mk w) *
          hTransport d s φ x (x + Torus.mk w) ^ 2 else 0) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      show ρ x * (if ε < ‖w‖ then _ else 0) = if ε < ‖w‖ then _ else 0
      split_ifs <;> ring
    rw [e]
    exact key
  · intro w hw0 hwδ
    have hwδ0 : ‖w‖ < δ0 := lt_of_le_of_lt hwδ hδδ0
    have := hexp x w hw0 hwδ0
    have e : rieszRadial s w = s * ‖w‖ ^ (-s - 2) := by
      unfold rieszRadial; rw [if_neg hs0.ne']
    rw [e] at this
    refine this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (norm_nonneg _) _))
  · intro w hw hw0
    exact hBh x w hw0 (abs_le_half_of_cube hw)
  · intro w _
    exact ⟨hρ.density.nonneg _, hρle _⟩
  · intro w hw
    have := hLρ x w
    exact this


/-- `J_{φ,ρ}` as in `localDivCoeff`. -/
def Jcoef (d : ℕ) (s : ℝ) (ρ φ : Torus d → ℝ) : ℝ :=
  s ^ 2 * HRS.sphereArea d / (d * (d + 2)) *
    ∫ x, ρ x ^ 2 * (Torus.laplacian φ x ^ 2 +
      2 * ∑ i : Fin d, ∑ j : Fin d, Torus.partialDeriv i (Torus.partialDeriv j φ) x ^ 2)

theorem model_pointwise (hφ : Torus.IsSmooth φ) (x : Torus d) :
    ρ x ^ 2 * s ^ 2 * (HRS.sphereArea d / (d * (d + 2)) *
          ((hess φ x).trace ^ 2 + 2 * ∑ i, ∑ j, hess φ x i j ^ 2)) =
      s ^ 2 * HRS.sphereArea d / (d * (d + 2)) * (ρ x ^ 2 * (Torus.laplacian φ x ^ 2 +
      2 * ∑ i : Fin d, ∑ j : Fin d, Torus.partialDeriv i (Torus.partialDeriv j φ) x ^ 2)) := by
  have htr : (hess φ x).trace = Torus.laplacian φ x := by
    rw [HRS.PDE.laplacian_eq_sum φ (StaticLimitsAux.isCk_two_of_smooth hφ) x]
    simp [Matrix.trace, hess]
  have hsw : ∑ i, ∑ j, hess φ x i j ^ 2 =
      ∑ i : Fin d, ∑ j : Fin d, Torus.partialDeriv i (Torus.partialDeriv j φ) x ^ 2 := by
    simp only [hess]
    exact Finset.sum_comm
  rw [htr, hsw]
  ring

theorem integral_model (hφ : Torus.IsSmooth φ) (hρ : SmoothPosDensity ρ) :
    ∫ x, ρ x ^ 2 * s ^ 2 * (HRS.sphereArea d / (d * (d + 2)) *
          ((hess φ x).trace ^ 2 + 2 * ∑ i, ∑ j, hess φ x i j ^ 2)) = Jcoef d s ρ φ := by
  unfold Jcoef
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => model_pointwise hφ x)

theorem Q_estimate (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : SmoothPosDensity ρ)
    (hφ : Torus.IsSmooth φ) :
    ∃ δ K1 K2 : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      |(∫ p : Torus d × Torus d, hC d s φ ε p.1 p.2 ^ 2
          ∂((withDensityReal ρ).prod (withDensityReal ρ))) -
        Jcoef d s ρ φ * ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - 2 * s)| ≤
        K1 + K2 * ∫ r in ε..δ, r ^ ((d : ℝ) - 2 * s) := by
  obtain ⟨δ, K1, K2, hδ, hδ4, hK1, hK2, hunif⟩ := uniform_estimate hd hs0 hsd hρ hφ
  refine ⟨δ, K1, K2, hδ, hδ4, hK1, hK2, fun ε hε hεδ => ?_⟩
  have := isProb_withDensityReal hρ.density
  rw [Q_formula hd hs0.le hsd hρ hφ hε]
  set R : ℝ := ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - 2 * s) with hR
  set Inn : Torus d → ℝ := fun x => ρ x * ∫ w in cube d, (if ε < ‖w‖ then ρ (x + Torus.mk w) *
        hTransport d s φ x (x + Torus.mk w) ^ 2 else 0) with hInn
  set mdl : Torus d → ℝ := fun x => ρ x ^ 2 * s ^ 2 * (HRS.sphereArea d / (d * (d + 2)) *
          ((hess φ x).trace ^ 2 + 2 * ∑ i, ∑ j, hess φ x i j ^ 2)) with hmdl
  -- integrability of Inn
  obtain ⟨B, hB0, hB⟩ := hC_bound hd hs0.le hsd hφ
  obtain ⟨Rm, hRm⟩ := isCompact_univ.exists_bound_of_continuousOn
    (PoleCavityAux.continuous_of_smoothPos hρ).continuousOn
  have hRm0 : 0 ≤ Rm := (norm_nonneg _).trans (hRm (Classical.arbitrary _) (mem_univ _))
  have hInnI : Integrable Inn := by
    have hg : ∀ x, ∫ w in cube d, (if ε < ‖w‖ then ρ (x + Torus.mk w) *
        hTransport d s φ x (x + Torus.mk w) ^ 2 else 0) =
        ∫ y, hC d s φ ε x y ^ 2 ∂(withDensityReal ρ) := fun x => (inner_eq hsd hρ hφ x).symm
    have hgm : Measurable fun x => ∫ y, hC d s φ ε x y ^ 2 ∂(withDensityReal ρ) :=
      (((measurable_hC hsd hφ ε).pow_const 2).stronglyMeasurable.integral_prod_right'
        (ν := withDensityReal ρ)).measurable
    have hgb : ∀ x, |∫ y, hC d s φ ε x y ^ 2 ∂(withDensityReal ρ)| ≤ (B * ε ^ (-s)) ^ 2 := by
      intro x
      have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ)
        (f := fun y => hC d s φ ε x y ^ 2) (C := (B * ε ^ (-s)) ^ 2)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hB ε hε x y) 2)
      simpa [Real.norm_eq_abs] using this
    have hInn_eq : Inn = fun x => ρ x * ∫ y, hC d s φ ε x y ^ 2 ∂(withDensityReal ρ) := by
      funext x; simp only [hInn]; rw [hg x]
    rw [hInn_eq]
    refine Integrable.of_bound (C := Rm * (B * ε ^ (-s)) ^ 2)
      ((hρ.density.measurable.mul hgm).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ?_ (hgb x) (abs_nonneg _) hRm0
    have := hRm x (mem_univ x)
    rwa [Real.norm_eq_abs] at this
  have hρc := PoleCavityAux.continuous_of_smoothPos hρ
  have hmdlc : Continuous mdl := by
    have e : mdl = fun x => s ^ 2 * HRS.sphereArea d / (d * (d + 2)) * (ρ x ^ 2 *
        (Torus.laplacian φ x ^ 2 +
          2 * ∑ i : Fin d, ∑ j : Fin d, Torus.partialDeriv i (Torus.partialDeriv j φ) x ^ 2)) := by
      funext x; exact model_pointwise hφ x
    rw [e]
    refine continuous_const.mul ((hρc.pow 2).mul ((( StaticLimitsAux.continuous_laplacian hφ).pow 2).add
      (continuous_const.mul (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_))))
    exact (StaticLimitsAux.continuous_second hφ i j).pow 2
  have hmdlI : Integrable fun x => mdl x * R :=
    (hmdlc.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmdlI' : Integrable mdl :=
    hmdlc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e1 : Jcoef d s ρ φ * R = ∫ x, mdl x * R := by
    rw [integral_mul_const, hmdl, integral_model hφ hρ]
  rw [e1, ← integral_sub hInnI hmdlI, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d)))
    (f := fun x => Inn x - mdl x * R) (C := K1 + K2 * ∫ r in ε..δ, r ^ ((d : ℝ) - 2 * s))
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hunif x ε hε hεδ)
  simpa [Measure.real] using this


theorem A_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : SmoothPosDensity ρ)
    (hφ : Torus.IsSmooth φ) :
    ∃ Amax : ℝ, 0 ≤ Amax ∧ ∀ ε : ℝ, 0 < ε → ∀ x : Torus d,
      |∫ y, hC d s φ ε x y ∂(withDensityReal ρ)| ≤ Amax := by
  obtain ⟨B, hB0, hB⟩ := hC_cube_bound hd hs0 hsd hφ
  obtain ⟨Rm, hRm⟩ := isCompact_univ.exists_bound_of_continuousOn
    (PoleCavityAux.continuous_of_smoothPos hρ).continuousOn
  have hRm0 : 0 ≤ Rm := (norm_nonneg _).trans (hRm (Classical.arbitrary _) (mem_univ _))
  have hint := (integrableOn_cube_rpow (d := d) (by omega) hsd).const_mul (Rm * B)
  refine ⟨∫ w in cube d, Rm * B * ‖w‖ ^ (-s), ?_, fun ε hε x => ?_⟩
  · exact setIntegral_nonneg measurableSet_cube fun w _ =>
      mul_nonneg (mul_nonneg hRm0 hB0) (Real.rpow_nonneg (norm_nonneg _) _)
  rw [integral_withDensityReal_eq ρ hρ.density.measurable hρ.density.nonneg]
  have hm : Measurable fun y => ρ y * hC d s φ ε x y :=
    hρ.density.measurable.mul (measurable_hC_slice hsd hφ ε x)
  rw [integral_shift_cube x _ hm, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_cube).2
    (Filter.Eventually.of_forall fun w hw => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |ρ (x + Torus.mk w)| ≤ Rm := by
    have := hRm (x + Torus.mk w) (mem_univ _)
    rwa [Real.norm_eq_abs] at this
  calc |ρ (x + Torus.mk w)| * |hC d s φ ε x (x + Torus.mk w)| ≤ Rm * (B * ‖w‖ ^ (-s)) :=
        mul_le_mul h1 (hB ε hε x w hw) (abs_nonneg _) hRm0
    _ = _ := by ring

theorem center_estimate (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : SmoothPosDensity ρ)
    (hφ : Torus.IsSmooth φ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ ε : ℝ, 0 < ε →
      |(∫ p : Torus d × Torus d, canonicalCenter (withDensityReal ρ) (hC d s φ ε) p.1 p.2 ^ 2
          ∂((withDensityReal ρ).prod (withDensityReal ρ))) -
        ∫ p : Torus d × Torus d, hC d s φ ε p.1 p.2 ^ 2
          ∂((withDensityReal ρ).prod (withDensityReal ρ))| ≤ Cc := by
  have := isProb_withDensityReal hρ.density
  obtain ⟨Amax, hA0, hA⟩ := A_bound hd hs0 hsd hρ hφ
  obtain ⟨B, hB0, hB⟩ := hC_bound hd hs0 hsd hφ
  refine ⟨3 * Amax ^ 2, by positivity, fun ε hε => ?_⟩
  rw [center_sq (μ := withDensityReal ρ) (measurable_hC hsd hφ ε) (M := B * ε ^ (-s))
    (fun x y => hB ε hε x y) (hC_symm hsd hφ ε)]
  set a2 : ℝ := ∫ x, (∫ y, hC d s φ ε x y ∂(withDensityReal ρ)) ^ 2 ∂(withDensityReal ρ) with ha2
  set c : ℝ := ∫ x, ∫ y, hC d s φ ε x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hc
  have ha2b : 0 ≤ a2 ∧ a2 ≤ Amax ^ 2 := by
    refine ⟨integral_nonneg fun x => sq_nonneg _, ?_⟩
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ)
      (f := fun x => (∫ y, hC d s φ ε x y ∂(withDensityReal ρ)) ^ 2) (C := Amax ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hA ε hε x) 2)
    simpa [Real.norm_eq_abs] using (le_abs_self _).trans this
  have hcb : c ^ 2 ≤ Amax ^ 2 := by
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ)
      (f := fun x => ∫ y, hC d s φ ε x y ∂(withDensityReal ρ)) (C := Amax)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hA ε hε x)
    have h2 : |c| ≤ Amax := by simpa [Real.norm_eq_abs, hc] using this
    calc c ^ 2 = |c| ^ 2 := (sq_abs c).symm
      _ ≤ Amax ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  have e : (∫ p : Torus d × Torus d, hC d s φ ε p.1 p.2 ^ 2
          ∂((withDensityReal ρ).prod (withDensityReal ρ))) - 2 * a2 + c ^ 2 -
        ∫ p : Torus d × Torus d, hC d s φ ε p.1 p.2 ^ 2
          ∂((withDensityReal ρ).prod (withDensityReal ρ)) = -2 * a2 + c ^ 2 := by ring
  rw [e, abs_le]
  constructor <;> nlinarith [ha2b.1, ha2b.2, sq_nonneg c]

end Main
end HRS.LocalDivAux
