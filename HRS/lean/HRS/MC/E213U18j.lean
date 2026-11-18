import HRS.MC.E213U18i
import HRS.MC.S7PIF1Brk

/-!
# Packet e213u18 (part j): the covariance-tensor term `E[ℓ_k(Z_a) J_a(ℓ_i ⊗ ℓ_j)]`

`E[ℓ_k(Z_a) J_a(ℓ_i⊗ℓ_j)] = 2β⁻¹ ∫_0^{t_i∧t_j} ∫ ∇f_i^u·∇f_j^u χ_k^u dx du`.  Since `J_a = Λ(w)` is a continuous linear functional of
the Gaussian path `w = procWin η`, the expectation against the first-chaos variable `ζ_k` is `Λ(E[ζ_k w])` (Bochner integral in the path space),
and `E[ζ_k w]` is the path `u ↦ χ_k^u`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U11
  HRS.MC.E213U10 HRS.MC.E213U1 HRS.MC.E213U13

variable {d : ℕ}

section JTerm

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- The evaluation formula for the window covariance tensor of a continuous path on the products of evaluation functionals. -/
theorem u18_winJ_eval (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {L : ℝ} (hL0 : 0 ≤ L)
    (w : PathSpace d (rLvl d) L) {ta tb : ℝ} (hta : ta ∈ Set.Icc a (a + T)) (htb : tb ∈ Set.Icc a (a + T))
    {φa φb : Torus d → ℝ} (hφa : Torus.IsSmooth φa) (hφb : Torus.IsSmooth φb)
    (l₁ l₂ : PathSpace d m T →L[ℝ] ℝ) (hl₁ : ∀ w', l₁ w' = NegSobolev.eval (pathEval w' (ta - a)) φa)
    (hl₂ : ∀ w', l₂ w' = NegSobolev.eval (pathEval w' (tb - a)) φb) :
    winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (u11_cp hL0 w v)) (Set.Ioc 0 (a + T))
        (mk2 l₁ l₂) =
      2 * S.β⁻¹ * ∫ u in Set.Ioc 0 (a + T) ∩ Set.Icc 0 (min ta tb),
        NegSobolev.eval (u11_cp hL0 w u)
          (fun x => inner ℝ (Torus.grad (propagator S.dyn S.ρ u ta φa) x)
            (Torus.grad (propagator S.dyn S.ρ u tb φb) x)) := by
  obtain ⟨K₁, K₂, c, -, -, -, hb⟩ := u11_winJ_bound (S := S) (β₀ := β₀) hE T hT
  obtain ⟨⟨J, hJ⟩, -⟩ := hb a ha (u11_cp hL0 w)
    (u11_measurable_nearCoef_of_continuous (u11_cp_continuous hL0 w)) ‖w‖ ‖w‖
    (u11_cp_bounds hL0 w _ _) (u11_cp_bounds hL0 w _ _)
  unfold winJ
  rw [HRS.MC.E213U2.e213u2_jTensor_eq _ _ _ _ _ _ hJ, tensorPow'_apply]
  have hta' : ta ∈ Set.Icc (0 : ℝ) (a + T) := ⟨ha.trans hta.1, hta.2⟩
  have htb' : tb ∈ Set.Icc (0 : ℝ) (a + T) := ⟨ha.trans htb.1, htb.2⟩
  have hτa : ta - a ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hta.1], by linarith [hta.2]⟩
  have hτb : tb - a ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [htb.1], by linarith [htb.2]⟩
  have hl₁' : ∀ w' : PathSpace d m (a + T), (l₁.comp (winRestr a ha)) w' =
      NegSobolev.eval (pathAt w' ta) φa := fun w' => by
    simp only [ContinuousLinearMap.comp_apply]
    rw [hl₁, u18_pathEval_eq, winRestr_pathAt a ha w' hτa]
    simp only [add_sub_cancel]
  have hl₂' : ∀ w' : PathSpace d m (a + T), (l₂.comp (winRestr a ha)) w' =
      NegSobolev.eval (pathAt w' tb) φb := fun w' => by
    simp only [ContinuousLinearMap.comp_apply]
    rw [hl₂, u18_pathEval_eq, winRestr_pathAt a ha w' hτb]
    simp only [add_sub_cancel]
  have hM : (mk2 l₁ l₂).compContinuousLinearMap (fun _ => winRestr a ha) =
      mk2 (l₁.comp (winRestr a ha)) (l₂.comp (winRestr a ha)) := by
    ext x
    simp [mk2, Fin.prod_univ_two]
  rw [hM]
  refine (hJ.2 ta tb φa φb _ _ hφa hφb hta' htb' hl₁' hl₂').trans ?_
  have hinv : (regime S β₀ hE).D.invβ = S.β⁻¹ := (regime S β₀ hE).hDβ
  rw [hinv]
  congr 1
  refine setIntegral_congr_fun (measurableSet_Ioc.inter measurableSet_Icc) fun u _ => ?_
  exact HRS.AdjK.adjka_eval_embed (rLvl_le hE) _ _

theorem u18_Jterm (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {t : Fin 3 → ℝ} {φ : Fin 3 → Torus d → ℝ}
    {χ : Fin 3 → ℝ → Torus d → ℝ} (h : U18Cov gd (a + T) t φ χ) (hta : ∀ i, t i ∈ Set.Icc a (a + T))
    (ℓ : Fin 3 → PathSpace d m T →L[ℝ] ℝ)
    (hℓ : ∀ i w, ℓ i w = NegSobolev.eval (pathEval w (t i - a)) (φ i)) (i j k : Fin 3) :
    ∫ ω, ℓ k (gd.Zwin T a ω) * gd.Jwin T a ω (mk2 (ℓ i) (ℓ j)) ∂gd.P₀ =
      2 * S.β⁻¹ * ∫ r in Set.Icc 0 (min (t i) (t j)), ∫ x,
        inner ℝ (Torus.grad (propagator S.dyn S.ρ r (t i) (φ i)) x)
          (Torus.grad (propagator S.dyn S.ρ r (t j) (φ j)) x) * χ k r x := by
  have hH : 0 < a + T := h.hH
  have hL0 : (0 : ℝ) ≤ a + T + 1 := by linarith
  obtain ⟨Λ, hΛ⟩ := u11_exists_Lambda (S := S) (β₀ := β₀) hE T hT a ha hL0 (by linarith : a + T ≤ a + T + 1)
  have heq := u11_Jwin_eq gd T hT a ha Λ hΛ
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : PathSpace d (rLvl d) (a + T + 1) →L[ℝ] ℝ,
      ∀ x, Θ x = Λ x (mk2 (ℓ i) (ℓ j)) :=
    ⟨(ContinuousLinearMap.apply ℝ ℝ (mk2 (ℓ i) (ℓ j))).comp Λ, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : gd.Ω₀ → PathSpace d (rLvl d) (a + T + 1),
      w = procWin (rLvl d) (a + T + 1) 0 gd.η := ⟨_, rfl⟩
  rw [← hw] at heq
  obtain ⟨C₁, -, hC₁⟩ := u11_eta_moment gd (a + T + 1) (by linarith) 1 le_rfl
  obtain ⟨C₂, -, hC₂⟩ := u11_eta_moment gd (a + T + 1) (by linarith) 2 (by norm_num)
  have hwm : AEStronglyMeasurable w gd.P₀ := by
    rw [hw]; exact (hC₁ 0 le_rfl).1.aestronglyMeasurable
  have hw2 : MemLp (fun ω => ‖w ω‖) 2 gd.P₀ := by
    have hI : Integrable (fun ω => ‖w ω‖ ^ 2) gd.P₀ := by
      have := (hC₂ 0 le_rfl).2.1
      rw [← hw] at this
      simpa only [Real.rpow_two] using this
    exact (memLp_two_iff_integrable_sq hwm.norm).2 hI
  have hζ : MemLp (u18_zeta gd t φ k) 2 gd.P₀ :=
    (u18_zeta_memLp gd h k).mono_exponent (by norm_num)
  have hint : Integrable (fun ω => u18_zeta gd t φ k ω • w ω) gd.P₀ := by
    refine (hζ.norm.integrable_mul hw2).mono' (hζ.aestronglyMeasurable.smul hwm)
      (Eventually.of_forall fun ω => ?_)
    simp only [norm_smul]
    exact le_rfl
  have hZ : ∀ᵐ ω ∂gd.P₀, ℓ k (gd.Zwin T a ω) = u18_zeta gd t φ k ω := by
    filter_upwards [u18_Zwin_eval gd T hT a ha (ψ := φ k)] with ω hω
    have hτ : t k - a ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [(hta k).1], by linarith [(hta k).2]⟩
    rw [hℓ, hω _ hτ]
    simp only [u18_zeta, add_sub_cancel]
  have step1 : ∫ ω, ℓ k (gd.Zwin T a ω) * gd.Jwin T a ω (mk2 (ℓ i) (ℓ j)) ∂gd.P₀ =
      ∫ ω, Θ (u18_zeta gd t φ k ω • w ω) ∂gd.P₀ := by
    refine integral_congr_ae ?_
    filter_upwards [hZ, heq] with ω h1 h2
    rw [h1, h2, map_smul, smul_eq_mul, hΘ]
  have step2 : ∫ ω, Θ (u18_zeta gd t φ k ω • w ω) ∂gd.P₀ = Θ (∫ ω, u18_zeta gd t φ k ω • w ω ∂gd.P₀) :=
    ContinuousLinearMap.integral_comp_comm Θ hint
  obtain ⟨hh, hhdef⟩ : ∃ hh : PathSpace d (rLvl d) (a + T + 1),
      hh = ∫ ω, u18_zeta gd t φ k ω • w ω ∂gd.P₀ := ⟨_, rfl⟩
  rw [← hhdef] at step2
  have step3 : Θ hh = 2 * S.β⁻¹ * ∫ u in Set.Ioc 0 (a + T) ∩ Set.Icc 0 (min (t i) (t j)),
      NegSobolev.eval (u11_cp hL0 hh u)
        (fun x => inner ℝ (Torus.grad (propagator S.dyn S.ρ u (t i) (φ i)) x)
          (Torus.grad (propagator S.dyn S.ρ u (t j) (φ j)) x)) := by
    rw [hΘ, hΛ hh]
    exact u18_winJ_eval T hT a ha hL0 hh (hta i) (hta j) (h.hφ i) (h.hφ j) (ℓ i) (ℓ j) (hℓ i) (hℓ j)
  have hcp : ∀ u ∈ Set.Icc (0 : ℝ) (a + T), ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      NegSobolev.eval (u11_cp hL0 hh u) ψ = ∫ x, ψ x * χ k u x := by
    intro u hu ψ hψ
    have huL : u ∈ Set.Icc (0 : ℝ) (a + T + 1) := ⟨hu.1, by linarith [hu.2]⟩
    rw [u11_cp_of_mem hL0 hh huL]
    have e1 : NegSobolev.eval (PathSpace.at' hh ⟨u, huL⟩) ψ =
        u18_pathCLF (rLvl d) (a + T + 1) u huL hψ hh := by
      rw [u18_pathCLF_apply, u18_pathEval_eq,
        show pathAt hh u = hh.at' ⟨u, huL⟩ from u10_pathAt_eq hh ⟨u, huL⟩]
    rw [e1, hhdef, ← ContinuousLinearMap.integral_comp_comm _ hint, h.cov k u hu ψ hψ]
    refine integral_congr_ae ?_
    filter_upwards [u11_eta_cont gd (a + T + 1)] with ω hc
    have hc' : ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 (0 + (a + T + 1))) := by simpa using hc
    rw [map_smul, smul_eq_mul, u18_pathCLF_apply, u18_pathEval_eq,
      show pathAt (w ω) u = (w ω).at' ⟨u, huL⟩ from u10_pathAt_eq (w ω) ⟨u, huL⟩, hw,
      u11_procWin_at gd.η (a + T + 1) 0 ω hc' (by linarith) ⟨u, huL⟩, zero_add, mul_comm]
  have hset : Set.Ioc (0 : ℝ) (a + T) ∩ Set.Icc 0 (min (t i) (t j)) = Set.Ioc 0 (min (t i) (t j)) := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h1, -⟩, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3.trans ((min_le_left _ _).trans (hta i).2)⟩, h1.le, h3⟩
  rw [step1, step2, step3, hset, integral_Icc_eq_integral_Ioc]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have hui : u ≤ t i := hu.2.trans (min_le_left _ _)
  have huj : u ≤ t j := hu.2.trans (min_le_right _ _)
  have hfi : Torus.IsSmooth (propagator S.dyn S.ρ u (t i) (φ i)) :=
    (HRS.MC.L2C0.l2c0_proof (regime S β₀ hE) (φ i) (h.hφ i) u (t i) hu.1.le hui).1
  have hfj : Torus.IsSmooth (propagator S.dyn S.ρ u (t j) (φ j)) :=
    (HRS.MC.L2C0.l2c0_proof (regime S β₀ hE) (φ j) (h.hφ j) u (t j) hu.1.le huj).1
  exact hcp u ⟨hu.1.le, hui.trans (hta i).2⟩ _ (HRS.MC.Sec7.S7PIF1.S7PIF1_isSmooth_inner_grad hfi hfj)


end JTerm

end HRS.MC.E213U18

end
