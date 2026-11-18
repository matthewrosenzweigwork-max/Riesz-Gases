import HRS.Energy.KIDAux4

/-!
# KID helper file 5: measurability and bounds for the Fubini step (part E of the plan)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.Uniform.Q54c

namespace HRS.KID

variable {d N : ℕ}

section Meas

variable {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem MFctx.measurable_Gmu (c : MFctx D T Λ ρ) :
    Measurable fun p : ℝ × Torus d => convGradConv (periodicRieszGrad d D.s) (ρ (clampT T p.1)) p.2 := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (r : ℝ) (x : Torus d) => convGradConv (periodicRieszGrad d D.s) (ρ (clampT T r)) x)
    (fun x => c.Gcont_pt x)
    (fun r => (c.Gcont (clampT_mem c.hT r)).measurable)
  exact h

theorem measurable_Pvec {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (i : Fin N) :
    Measurable fun X : Config d N => Pvec h X i := by
  have hgh : Continuous (Torus.grad h) := HRS.PDE.MFLinear.continuous_grad (isCk1_of_smooth hsm)
  have hs : Measurable fun X : Config d N => ∑ j ∈ Finset.univ.erase i, Torus.grad h (X i - X j) :=
    Finset.measurable_sum _ fun j _ =>
      hgh.measurable.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  unfold Pvec
  exact hs.const_smul ((1 : ℝ) / (N : ℝ))

theorem measurable_particleDrift {D : DynData d} (hV : Torus.IsCk 2 D.V) (i : Fin N) :
    Measurable fun X : Config d N => particleDrift D X i :=
  (measurable_pi_apply i).comp (measurable_driftVec hV)

theorem measurable_ppDrift {D : DynData d} (hV : Torus.IsCk 2 D.V) {h : Torus d → ℝ}
    (hsm : Torus.IsSmooth h) : Measurable (ppDrift D h : Config d N → ℝ) := by
  have hlap : Continuous (Torus.laplacian h) :=
    HRS.PDE.MFApriori.continuous_laplacian_of_isCk (isCk2_of_smooth hsm)
  have hA : Measurable fun X : Config d N =>
      ∑ i, inner ℝ (Pvec h X i) (particleDrift D X i) :=
    Finset.measurable_sum _ fun i _ => (measurable_Pvec hsm i).inner (measurable_particleDrift hV i)
  have hB : Measurable fun X : Config d N =>
      ∑ i, ∑ j ∈ Finset.univ.erase i, Torus.laplacian h (X i - X j) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      hlap.measurable.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  unfold ppDrift
  exact (hA.const_mul _).add ((hB.const_mul _).const_mul _)

theorem MFctx.measurable_fDrift (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) :
    Measurable fun p : ℝ × Config d N => fDrift D h ρ (clampT T p.1) p.2 := by
  have hh := isCk2_of_smooth hsm
  have hft : Continuous fun q : ℝ × Torus d => ftK D h ρ (clampT T q.1) q.2 :=
    c.continuous_ft_clamp hh
  have hlap := c.continuous_lap_fK hsm hev
  have hgr := c.continuous_grad_fK hsm hev
  have hxi : ∀ i : Fin N, Measurable fun p : ℝ × Config d N => ((p.1, p.2 i) : ℝ × Torus d) :=
    fun i => measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  have m1 : ∀ i : Fin N, Measurable fun p : ℝ × Config d N => ftK D h ρ (clampT T p.1) (p.2 i) :=
    fun i => by
      have := hft.measurable.comp (hxi i)
      simpa only [Function.comp_def] using this
  have m2 : ∀ i : Fin N, Measurable fun p : ℝ × Config d N =>
      Torus.laplacian (fK h ρ (clampT T p.1)) (p.2 i) := fun i => by
    have := hlap.measurable.comp (hxi i)
    simpa only [Function.comp_def] using this
  have m3 : ∀ i : Fin N, Measurable fun p : ℝ × Config d N =>
      Torus.grad (fK h ρ (clampT T p.1)) (p.2 i) := fun i => by
    have := hgr.measurable.comp (hxi i)
    simpa only [Function.comp_def] using this
  have m4 : ∀ i : Fin N, Measurable fun p : ℝ × Config d N => particleDrift D p.2 i :=
    fun i => (measurable_particleDrift c.hV i).comp measurable_snd
  have m5 : ∀ i : Fin N, Measurable fun p : ℝ × Config d N =>
      inner ℝ (Torus.grad (fK h ρ (clampT T p.1)) (p.2 i)) (particleDrift D p.2 i) :=
    fun i => (m3 i).inner (m4 i)
  unfold fDrift
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    ((m1 i).add ((m2 i).const_mul _)).add (m5 i))

theorem MFctx.measurable_micro (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) :
    Measurable fun p : ℝ × Config d N => microTerm D h (ρ (clampT T p.1)) p.2 := by
  have hgr := c.continuous_grad_fK hsm hev
  have hmat : Continuous (fun v : Euc d => Torus.matVec D.M v) :=
    LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)
  have hxi : ∀ i : Fin N, Measurable fun p : ℝ × Config d N => ((p.1, p.2 i) : ℝ × Torus d) :=
    fun i => measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  have e : (fun p : ℝ × Config d N => microTerm D h (ρ (clampT T p.1)) p.2) = fun p =>
      (1 / (N : ℝ)) * ∑ i, inner ℝ (Pvec h p.2 i - Torus.grad (fK h ρ (clampT T p.1)) (p.2 i))
        (Torus.matVec D.M (selfForce (periodicRieszGrad d D.s) (ρ (clampT T p.1)) p.2 i)) := by
    funext p
    unfold microTerm
    simp only [c.selfForce_grad hsm hev (clampT_mem c.hT p.1)]
  rw [e]
  have m3 : ∀ i : Fin N, Measurable fun p : ℝ × Config d N =>
      Torus.grad (fK h ρ (clampT T p.1)) (p.2 i) := fun i => by
    have := hgr.measurable.comp (hxi i)
    simpa only [Function.comp_def] using this
  have mG : ∀ i : Fin N, Measurable fun p : ℝ × Config d N =>
      convGradConv (periodicRieszGrad d D.s) (ρ (clampT T p.1)) (p.2 i) := fun i => by
    have := c.measurable_Gmu.comp (hxi i)
    simpa only [Function.comp_def] using this
  have mS : ∀ i : Fin N, Measurable fun p : ℝ × Config d N =>
      selfForce (periodicRieszGrad d D.s) (ρ (clampT T p.1)) p.2 i := fun i => by
    have hs : Measurable fun p : ℝ × Config d N =>
        ∑ j ∈ Finset.univ.erase i, periodicRieszGrad d D.s (p.2 i - p.2 j) :=
      Finset.measurable_sum _ fun j _ =>
        (KernelGrad.measurable_periodicRieszGrad D.hsd).comp
          (((measurable_pi_apply i).comp measurable_snd).sub ((measurable_pi_apply j).comp measurable_snd))
    unfold selfForce
    exact (hs.const_smul ((1 : ℝ) / (N : ℝ))).sub (mG i)
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  have mP : Measurable fun p : ℝ × Config d N => Pvec h p.2 i := (measurable_Pvec hsm i).comp measurable_snd
  exact (mP.sub (m3 i)).inner (hmat.measurable.comp (mS i))

end Meas

section Bounds

variable {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem MFctx.abs_int_rho_le (c : MFctx D T Λ ρ) {r : ℝ} (hr : r ∈ Icc 0 T) {g : Torus d → ℝ}
    (hg : Continuous g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) : |∫ y, ρ r y * g y| ≤ B := by
  have hp := c.dens hr
  have hρc := c.cont hr
  have hi : Integrable (fun y => ρ r y * g y) := integrable_of_cont (hρc.mul hg)
  have hρi : Integrable (ρ r) := integrable_of_cont hρc
  calc |∫ y, ρ r y * g y| ≤ ∫ y, |ρ r y * g y| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => ρ r y * g y)
    _ ≤ ∫ y, B * ρ r y := by
        refine integral_mono hi.abs (hρi.const_mul B) fun y => ?_
        simp only
        rw [abs_mul, abs_of_nonneg (hp.nonneg y), mul_comm]
        exact mul_le_mul_of_nonneg_right (hB y) (hp.nonneg y)
    _ = B := by rw [integral_const_mul, hp.integral_one, mul_one]

theorem MFctx.u_bound (c : MFctx D T Λ ρ) :
    ∃ Bu : ℝ, 0 ≤ Bu ∧ ∀ r ∈ Icc 0 T, ∀ y, ‖meanFieldDrift D (ρ r) y‖ ≤ Bu := by
  have hV1 : Torus.IsCk 1 D.V := c.hV.of_le (by norm_num)
  obtain ⟨B3, hB30, hB3⟩ := exists_norm_bound (Torus.grad D.V) (HRS.PDE.MFLinear.continuous_grad hV1)
  obtain ⟨Kg, hKg⟩ := c.Gbound
  obtain ⟨cM, hcM0, hcM⟩ := exists_matVec_bound D.M
  have hKg0 : 0 ≤ Kg := (norm_nonneg _).trans (hKg 0 ⟨le_rfl, c.hT⟩ 0)
  refine ⟨cM * Kg + B3, by positivity, fun r hr y => ?_⟩
  unfold meanFieldDrift
  refine (norm_sub_le _ _).trans (add_le_add ?_ (hB3 y))
  exact (hcM _).trans (mul_le_mul_of_nonneg_left (hKg r hr y) hcM0)

theorem norm_Pvec_le {h : Torus d → ℝ} {Bg : ℝ} (hBg : ∀ x, ‖Torus.grad h x‖ ≤ Bg) (hBg0 : 0 ≤ Bg)
    (hN : 0 < N) (X : Config d N) (i : Fin N) : ‖Pvec h X i‖ ≤ Bg := by
  unfold Pvec
  rw [norm_smul]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ‖∑ j ∈ Finset.univ.erase i, Torus.grad h (X i - X j)‖ ≤ (N : ℝ) * Bg := by
    calc _ ≤ ∑ j ∈ Finset.univ.erase i, ‖Torus.grad h (X i - X j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.univ.erase i, Bg := Finset.sum_le_sum fun j _ => hBg _
      _ = ((Finset.univ.erase i).card : ℝ) * Bg := by simp
      _ ≤ (N : ℝ) * Bg := by
          refine mul_le_mul_of_nonneg_right ?_ hBg0
          have : (Finset.univ.erase i).card ≤ N := by
            simpa using Finset.card_erase_le (s := (Finset.univ : Finset (Fin N))) (a := i)
          exact_mod_cast this
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / (N : ℝ) * ‖∑ j ∈ Finset.univ.erase i, Torus.grad h (X i - X j)‖ ≤ 1 / (N : ℝ) * ((N : ℝ) * Bg) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Bg := by field_simp

theorem abs_sum_le_card {ι : Type*} (s : Finset ι) (f : ι → ℝ) {B : ℝ} (hB : ∀ i, |f i| ≤ B) :
    |∑ i ∈ s, f i| ≤ (s.card : ℝ) * B := by
  calc |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum fun i _ => hB i
    _ = (s.card : ℝ) * B := by simp

theorem MFctx.Cb_bound (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hsm : Torus.IsSmooth h)
    (hev : ∀ x, h (-x) = h x) (hN : 0 < N) :
    ∃ C₁ C₂ : ℝ, ∀ r ∈ Icc 0 T, ∀ X : Config d N, X ∉ collisionSet d N →
      |commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r)) X (withDensityReal (ρ r))| ≤ C₁ ∧
      |offDiagDiffPairing (Torus.laplacian h) X (withDensityReal (ρ r))| ≤ C₂ := by
  have h1 := isCk1_of_smooth hsm
  have hh := isCk2_of_smooth hsm
  have hgh : Continuous (Torus.grad h) := HRS.PDE.MFLinear.continuous_grad h1
  have hlap : Continuous (Torus.laplacian h) := HRS.PDE.MFApriori.continuous_laplacian_of_isCk hh
  obtain ⟨Bg, hBg0, hBg⟩ := exists_norm_bound (Torus.grad h) hgh
  obtain ⟨Bl, hBl0, hBl⟩ := exists_norm_bound (Torus.laplacian h) hlap
  obtain ⟨Bu, hBu0, hBu⟩ := c.u_bound
  have hβ := D.hβ
  refine ⟨8 * (Bu * Bg), 4 * Bl, fun r hr X hX => ?_⟩
  have hBl' : ∀ x, |Torus.laplacian h x| ≤ Bl := fun x => by simpa [Real.norm_eq_abs] using hBl x
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hρc := c.cont hr
  have hu := c.ucont hr
  have hφ : Torus.IsCk 2 (fK h ρ r) := ContDiff.of_le (c.contDiff_fK hsm hev hr) two_le_top
  have hgφ : Continuous (Torus.grad (fK h ρ r)) :=
    HRS.PDE.MFLinear.continuous_grad (hφ.of_le (by norm_num))
  have hlφ : Continuous (Torus.laplacian (fK h ρ r)) :=
    HRS.PDE.MFApriori.continuous_laplacian_of_isCk hφ
  have hBf : ∀ x, ‖Torus.grad (fK h ρ r) x‖ ≤ Bg := fun x => c.grad_fK_le hsm hev hBg hr x
  have hBlf : ∀ x, |Torus.laplacian (fK h ρ r) x| ≤ Bl := fun x => c.lap_fK_le hsm hev hBl' hr x
  have hUG : ∀ (x : Torus d) (v : Euc d), ‖v‖ ≤ Bg →
      |inner ℝ (meanFieldDrift D (ρ r) x) v| ≤ Bu * Bg := fun x v hv =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hBu r hr x) hv (norm_nonneg _) hBu0)
  -- the pieces
  have hS1 : |∑ i, inner ℝ (meanFieldDrift D (ρ r) (X i)) (Pvec h X i)| ≤ (N : ℝ) * (Bu * Bg) := by
    have := abs_sum_le_card (Finset.univ : Finset (Fin N))
      (fun i => inner ℝ (meanFieldDrift D (ρ r) (X i)) (Pvec h X i)) (B := Bu * Bg)
      (fun i => hUG _ _ (norm_Pvec_le (fun x => hBg x) hBg0 hN X i))
    simpa using this
  have hJ : ∀ x, |Jx D h ρ r x| ≤ Bu * Bg := by
    intro x
    unfold Jx
    exact c.abs_int_rho_le hr (hu.inner (hgh.comp (continuous_const.sub continuous_id)))
      (fun y => hUG y _ (hBg _))
  have hS2 : |∑ i, (inner ℝ (meanFieldDrift D (ρ r) (X i)) (Torus.grad (fK h ρ r) (X i)) -
      Jx D h ρ r (X i))| ≤ (N : ℝ) * (2 * (Bu * Bg)) := by
    have := abs_sum_le_card (Finset.univ : Finset (Fin N))
      (fun i => inner ℝ (meanFieldDrift D (ρ r) (X i)) (Torus.grad (fK h ρ r) (X i)) - Jx D h ρ r (X i))
      (B := 2 * (Bu * Bg)) (fun i => by
        refine (abs_sub _ _).trans ?_
        have := hUG (X i) _ (hBf (X i))
        have := hJ (X i)
        linarith)
    simpa using this
  have hI : |∫ x, ρ r x * inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (fK h ρ r) x)| ≤ Bu * Bg :=
    c.abs_int_rho_le hr (hu.inner hgφ) (fun y => hUG y _ (hBf y))
  have hL1 : |∑ i, ∑ j ∈ Finset.univ.erase i, Torus.laplacian h (X i - X j)| ≤ (N : ℝ) * ((N : ℝ) * Bl) := by
    have := abs_sum_le_card (Finset.univ : Finset (Fin N))
      (fun i => ∑ j ∈ Finset.univ.erase i, Torus.laplacian h (X i - X j)) (B := (N : ℝ) * Bl)
      (fun i => by
        refine (abs_sum_le_card _ _ (fun j => hBl' _)).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hBl0
        have : (Finset.univ.erase i).card ≤ N := by
          simpa using Finset.card_erase_le (s := (Finset.univ : Finset (Fin N))) (a := i)
        exact_mod_cast this)
    simpa using this
  have hL2 : |∑ i, Torus.laplacian (fK h ρ r) (X i)| ≤ (N : ℝ) * Bl := by
    have := abs_sum_le_card (Finset.univ : Finset (Fin N))
      (fun i => Torus.laplacian (fK h ρ r) (X i)) (B := Bl) (fun i => hBlf _)
    simpa using this
  have hL3 : |∫ x, ρ r x * Torus.laplacian (fK h ρ r) x| ≤ Bl :=
    c.abs_int_rho_le hr hlφ hBlf
  rw [c.comm_eval hsm hev hr hN X hX, c.offDiag_eval hsm hev hr hN X hX]
  set K := Bu * Bg with hK
  have hK0 : 0 ≤ K := by positivity
  have t1 : |(2 / (N : ℝ)) * ∑ i, inner ℝ (meanFieldDrift D (ρ r) (X i)) (Pvec h X i)| ≤ 2 * K := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc (2 / (N : ℝ)) * |∑ i, inner ℝ (meanFieldDrift D (ρ r) (X i)) (Pvec h X i)|
        ≤ (2 / (N : ℝ)) * ((N : ℝ) * K) := mul_le_mul_of_nonneg_left hS1 (by positivity)
      _ = 2 * K := by field_simp
  have t2 : |(2 / (N : ℝ)) * ∑ i, (inner ℝ (meanFieldDrift D (ρ r) (X i)) (Torus.grad (fK h ρ r) (X i)) -
      Jx D h ρ r (X i))| ≤ 4 * K := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc (2 / (N : ℝ)) * |∑ i, (inner ℝ (meanFieldDrift D (ρ r) (X i)) (Torus.grad (fK h ρ r) (X i)) -
          Jx D h ρ r (X i))| ≤ (2 / (N : ℝ)) * ((N : ℝ) * (2 * K)) :=
          mul_le_mul_of_nonneg_left hS2 (by positivity)
      _ = 4 * K := by field_simp; ring
  have t3 : |2 * ∫ x, ρ r x * inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (fK h ρ r) x)| ≤ 2 * K := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hI (by norm_num)
  have u1 : |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, Torus.laplacian h (X i - X j)| ≤ Bl := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc (1 / (N : ℝ) ^ 2) * |∑ i, ∑ j ∈ Finset.univ.erase i, Torus.laplacian h (X i - X j)|
        ≤ (1 / (N : ℝ) ^ 2) * ((N : ℝ) * ((N : ℝ) * Bl)) := mul_le_mul_of_nonneg_left hL1 (by positivity)
      _ = Bl := by field_simp
  have u2 : |(2 / (N : ℝ)) * ∑ i, Torus.laplacian (fK h ρ r) (X i)| ≤ 2 * Bl := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc (2 / (N : ℝ)) * |∑ i, Torus.laplacian (fK h ρ r) (X i)| ≤ (2 / (N : ℝ)) * ((N : ℝ) * Bl) :=
          mul_le_mul_of_nonneg_left hL2 (by positivity)
      _ = 2 * Bl := by field_simp
  have hc : |(2 / (N : ℝ)) * ∑ i, inner ℝ (meanFieldDrift D (ρ r) (X i)) (Pvec h X i)
      - (2 / (N : ℝ)) * ∑ i, (inner ℝ (meanFieldDrift D (ρ r) (X i)) (Torus.grad (fK h ρ r) (X i)) -
          Jx D h ρ r (X i))
      + 2 * ∫ x, ρ r x * inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (fK h ρ r) x)| ≤ 8 * K := by
    refine (abs_add_le _ _).trans ?_
    have := abs_sub (2 / (N : ℝ) * ∑ i, inner ℝ (meanFieldDrift D (ρ r) (X i)) (Pvec h X i))
      (2 / (N : ℝ) * ∑ i, (inner ℝ (meanFieldDrift D (ρ r) (X i)) (Torus.grad (fK h ρ r) (X i)) -
        Jx D h ρ r (X i)))
    linarith
  have ho : |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, Torus.laplacian h (X i - X j)
      - (2 / (N : ℝ)) * ∑ i, Torus.laplacian (fK h ρ r) (X i)
      + ∫ x, ρ r x * Torus.laplacian (fK h ρ r) x| ≤ 4 * Bl := by
    refine (abs_add_le _ _).trans ?_
    have := abs_sub ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, Torus.laplacian h (X i - X j))
      ((2 / (N : ℝ)) * ∑ i, Torus.laplacian (fK h ρ r) (X i))
    linarith
  exact ⟨hc, ho⟩

end Bounds

end HRS.KID
