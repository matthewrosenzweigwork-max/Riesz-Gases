import HRS.MS.MfeConfAux10

/-!
# S.B.1, packet F1 (part 6): joint continuity of the trajectory, its derivatives, the force and `A(ρ_r)(x)`

On `X = [0,T] × ℝ^d`:

* `sb1_joint_cont_of_unif`: continuity in `x` for each `r` plus uniform-in-`x` continuity in `r` gives joint continuity;
* `sb1_rgT_joint_cont`: `(r,x) ↦ rgT κ (g_r) (x)` is jointly continuous for a jointly continuous family `g` with uniform
  bounds (dominated convergence with the majorant `rgMaj` and the Peetre inequality);
* `sb1_A_joint_cont`: `(r,x) ↦ A(ρ_r)(x)` is jointly continuous.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

open HRS.MP.RdGen HRS.MH.DualityRd

variable {d : ℕ}

theorem sb1_joint_cont_of_unif {G : Type*} [NormedAddCommGroup G] {T : ℝ} {g : ℝ → Euc d → G}
    (hcont : ∀ r ∈ Set.Icc (0 : ℝ) T, Continuous (g r))
    (hunif : ∀ r₀ ∈ Set.Icc (0 : ℝ) T, ∀ ε > 0, ∃ δ > 0, ∀ r ∈ Set.Icc (0 : ℝ) T, |r - r₀| < δ →
      ∀ x, ‖g r x - g r₀ x‖ ≤ ε) :
    Continuous (fun p : Set.Icc (0 : ℝ) T × Euc d => g p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨⟨r₀, hr₀⟩, x₀⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := hunif r₀ hr₀ (ε / 2) (half_pos hε)
  have e1 : ∀ᶠ p : Set.Icc (0 : ℝ) T × Euc d in 𝓝 (⟨r₀, hr₀⟩, x₀), |(p.1 : ℝ) - r₀| < δ := by
    have h : ContinuousAt (fun p : Set.Icc (0 : ℝ) T × Euc d => (p.1 : ℝ)) (⟨r₀, hr₀⟩, x₀) :=
      (continuous_subtype_val.comp continuous_fst).continuousAt
    have h2 := Metric.tendsto_nhds.1 h.tendsto δ hδ
    filter_upwards [h2] with p hp
    simpa [Real.dist_eq] using hp
  have e2 : ∀ᶠ p : Set.Icc (0 : ℝ) T × Euc d in 𝓝 (⟨r₀, hr₀⟩, x₀), dist (g r₀ p.2) (g r₀ x₀) < ε / 2 := by
    have h : ContinuousAt (fun p : Set.Icc (0 : ℝ) T × Euc d => g r₀ p.2) (⟨r₀, hr₀⟩, x₀) :=
      ((hcont r₀ hr₀).comp continuous_snd).continuousAt
    exact (Metric.tendsto_nhds.1 h (ε / 2) (half_pos hε))
  filter_upwards [e1, e2] with p hp1 hp2
  rw [dist_eq_norm] at hp2 ⊢
  calc ‖g p.1 p.2 - g r₀ x₀‖ = ‖(g p.1 p.2 - g r₀ p.2) + (g r₀ p.2 - g r₀ x₀)‖ := by congr 1; abel
    _ ≤ ‖g p.1 p.2 - g r₀ p.2‖ + ‖g r₀ p.2 - g r₀ x₀‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hu p.1 p.1.2 hp1 p.2) hp2
    _ = ε := by ring

theorem sb1_rgT_joint_cont (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ}
    (hκ : RgKer d s σ κ) {Fb : Type*} [NormedAddCommGroup Fb] [NormedSpace ℝ Fb] [CompleteSpace Fb]
    {T : ℝ} {g : ℝ → Euc d → Fb} {b0 b1 : ℝ} (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hdiff : ∀ r ∈ Set.Icc (0 : ℝ) T, Differentiable ℝ (g r))
    (hcont : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => g p.1 p.2)
    (h0 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ y, ‖g r y‖ ≤ b0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (h1 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ y, ‖fderiv ℝ (g r) y‖ ≤ b1) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => rgT κ (g p.1) p.2 := by
  rw [continuous_iff_continuousAt]
  intro p₀
  unfold rgT
  refine continuousAt_of_dominated (F := fun (p : Set.Icc (0 : ℝ) T × Euc d) z =>
    κ z • rgR (g p.1) p.2 z) (bound := rgMaj d s σ (b0 * 2 ^ ((d : ℝ) + 1)) b1 p₀.2)
    (Eventually.of_forall fun p => rg_aesm hκ.meas (hdiff _ p.1.2).continuous p.2) ?_
    (rg_maj_integrable hd hsd σ _ b1 p₀.2) ?_
  · have hball : ∀ᶠ p : Set.Icc (0 : ℝ) T × Euc d in 𝓝 p₀, ‖p.2 - p₀.2‖ < 1 := by
      have h : ContinuousAt (fun p : Set.Icc (0 : ℝ) T × Euc d => p.2) p₀ := continuous_snd.continuousAt
      have h2 := Metric.tendsto_nhds.1 h.tendsto 1 one_pos
      filter_upwards [h2] with p hp
      simpa [dist_eq_norm] using hp
    filter_upwards [hball] with p hp
    filter_upwards [Whole.movtr_ae_ne_zero (d := d) hd] with z hz
    have := rg_norm_le hs0 hκ (hdiff _ p.1.2) hb0 hb1 (h0 _ p.1.2) (h1 _ p.1.2) p.2 z hz
    refine this.trans ?_
    unfold rgMaj
    apply mul_le_mul_of_nonneg_left _ hκ.sigma_nonneg
    refine add_le_add_right ?_ _
    have hpe := rg_peetre (d := d) z hp
    have h4 : (0 : ℝ) ≤ 4 ^ (s + 1) * b0 := by positivity
    calc 4 ^ (s + 1) * b0 * (1 + ‖p.2 - z‖) ^ (-((d : ℝ) + 1))
        ≤ 4 ^ (s + 1) * b0 * (2 ^ ((d : ℝ) + 1) * (1 + ‖p₀.2 - z‖) ^ (-((d : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hpe h4
      _ = 4 ^ (s + 1) * (b0 * 2 ^ ((d : ℝ) + 1)) * (1 + ‖p₀.2 - z‖) ^ (-((d : ℝ) + 1)) := by ring
  · refine Eventually.of_forall fun z => ?_
    have c1 : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => g p.1 (p.2 - z) :=
      hcont.comp (continuous_fst.prodMk (continuous_snd.sub continuous_const))
    have : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => κ z • rgR (g p.1) p.2 z := by
      unfold rgR
      by_cases hz : ‖z‖ ≤ 1 / 4
      · simp only [hz, ite_true]
        exact continuous_const.smul (c1.sub hcont)
      · simp only [hz, ite_false]
        exact continuous_const.smul c1
    exact this.continuousAt


/-! ### Joint continuity of the jets of `ρ` -/

variable {D : Whole.WholeDyn d} {T C B : ℝ} {ρ : ℝ → Euc d → ℝ}

theorem sb1_rho_cont (H : Sb1Traj D T C B ρ) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => ρ p.1 p.2 := by
  refine sb1_joint_cont_of_unif (g := ρ) (fun r hr => H.cont hr) (fun r₀ hr₀ ε hε => ?_)
  have hK := H.KA_nonneg
  refine ⟨ε / (H.KA + 1), by positivity, fun r hr hrr x => ?_⟩
  rw [Real.norm_eq_abs]
  refine (sb1_rho_lip_time H x hr₀ hr).trans ?_
  rw [abs_sub_comm] at hrr
  calc H.KA * |r - r₀| ≤ H.KA * (ε / (H.KA + 1)) := mul_le_mul_of_nonneg_left (by
        rw [abs_sub_comm]; exact hrr.le) hK
    _ ≤ ε := by
        rw [mul_div_assoc']
        exact (div_le_iff₀ (by positivity)).2 (by nlinarith)

theorem sb1_jet_cont (H : Sb1Traj D T C B ρ) (j : ℕ) (hj : j ≤ 2) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => iteratedFDeriv ℝ j (ρ p.1) p.2 := by
  refine sb1_joint_cont_of_unif (g := fun r x => iteratedFDeriv ℝ j (ρ r) x) (fun r hr => ?_) (fun r₀ hr₀ ε hε => ?_)
  · exact (H.slice r hr).decay.1.continuous_iteratedFDeriv (by exact_mod_cast hj.trans (by norm_num))
  · obtain ⟨δ, hδ, h⟩ := sb1_rho_C2_time H hε
    exact ⟨δ, hδ, fun r hr hrr x => h r₀ hr₀ r hr hrr x j hj⟩

theorem sb1_fderiv_cont (H : Sb1Traj D T C B ρ) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => fderiv ℝ (ρ p.1) p.2 := by
  refine sb1_joint_cont_of_unif (g := fun r x => fderiv ℝ (ρ r) x) (fun r hr => ?_) (fun r₀ hr₀ ε hε => ?_)
  · exact (H.slice r hr).decay.1.continuous_fderiv (by norm_num)
  · obtain ⟨δ, hδ, h⟩ := sb1_rho_C1_time H hε
    exact ⟨δ, hδ, fun r hr hrr x => h r₀ hr₀ r hr hrr x⟩

theorem sb1_dd_eq {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (x : Euc d) (k : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ f y (sb1e k)) x (sb1e k) = iteratedFDeriv ℝ 2 f x ![sb1e k, sb1e k] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem sb1_dd_cont (H : Sb1Traj D T C B ρ) (k : Fin d) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
      fderiv ℝ (fun y => fderiv ℝ (ρ p.1) y (sb1e k)) p.2 (sb1e k) := by
  have : (fun p : Set.Icc (0 : ℝ) T × Euc d => fderiv ℝ (fun y => fderiv ℝ (ρ p.1) y (sb1e k)) p.2 (sb1e k)) =
      fun p => iteratedFDeriv ℝ 2 (ρ p.1) p.2 ![sb1e k, sb1e k] := by
    funext p
    exact sb1_dd_eq ((H.slice p.1.1 p.1.2).decay.1.of_le (by norm_num)) p.2 k
  rw [this]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ ![sb1e k, sb1e k]).continuous.comp
    (sb1_jet_cont H 2 le_rfl)

theorem sb1_d_cont (H : Sb1Traj D T C B ρ) (k : Fin d) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => fderiv ℝ (ρ p.1) p.2 (sb1e k) :=
  (ContinuousLinearMap.apply ℝ ℝ (sb1e k)).continuous.comp (sb1_fderiv_cont H)

/-! ### The force and its divergence -/

theorem sb1_F_cont (H : Sb1Traj D T C B ρ) (k : Fin d) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => sb1F d D.s (ρ p.1) k p.2 := by
  have e : (fun p : Set.Icc (0 : ℝ) T × Euc d => sb1F d D.s (ρ p.1) k p.2) =
      fun p => rgT (fun z => (Whole.rieszKernelGrad d D.s z) k) (ρ p.1) p.2 := by
    funext p
    rw [sb1F_eq_rgT H.hd H.hs0 H.hsd (H.slice p.1.1 p.1.2) k]
  rw [e]
  refine sb1_rgT_joint_cont (g := ρ) H.hd H.hs0 H.hsd (rgKerComp_ok H.hs0 k) H.hC H.hC
    (fun r hr => (H.slice r hr).decay.1.differentiable (by norm_num)) (sb1_rho_cont H)
    (fun r hr y => (sb1_slice_facts (H.slice r hr)).2.1 y)
    (fun r hr y => (sb1_slice_facts (H.slice r hr)).2.2.2.1 y)

theorem sb1_dF_eq (H : Sb1Traj D T C B ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (k : Fin d) (x : Euc d) :
    fderiv ℝ (sb1F d D.s (ρ r) k) x = rgT (fun z => (Whole.rieszKernelGrad d D.s z) k) (fderiv ℝ (ρ r)) x :=
  (sb1F_fderiv H.hd H.hs0 H.hsd (H.slice r hr) k x).fderiv

theorem sb1_dF_cont (H : Sb1Traj D T C B ρ) (k : Fin d) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => fderiv ℝ (sb1F d D.s (ρ p.1) k) p.2 (sb1e k) := by
  have e : (fun p : Set.Icc (0 : ℝ) T × Euc d => fderiv ℝ (sb1F d D.s (ρ p.1) k) p.2 (sb1e k)) =
      fun p => (ContinuousLinearMap.apply ℝ ℝ (sb1e k))
        (rgT (fun z => (Whole.rieszKernelGrad d D.s z) k) (fderiv ℝ (ρ p.1)) p.2) := by
    funext p
    rw [sb1_dF_eq H p.1.2 k]
    rfl
  rw [e]
  refine (ContinuousLinearMap.apply ℝ ℝ (sb1e k)).continuous.comp ?_
  refine sb1_rgT_joint_cont (g := fun r => fderiv ℝ (ρ r)) H.hd H.hs0 H.hsd (rgKerComp_ok H.hs0 k) H.hC H.hC
    (fun r hr => ((H.slice r hr).decay.1.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)) (sb1_fderiv_cont H)
    (fun r hr y => (sb1_slice_facts (H.slice r hr)).2.2.1 y)
    (fun r hr y => (sb1_slice_facts (H.slice r hr)).2.2.2.2.1 y)

/-! ### Joint continuity of `A(ρ_r)(x)` -/

theorem sb1A_expand (D : Whole.WholeDyn d) {B : ℝ} (P : Sb1Pot D.V B) (hd : 1 ≤ d)
    (hs0 : 0 ≤ D.s) (hsd : D.s < d) {C : ℝ} {h : Euc d → ℝ} (S : Sb1Slice d C h) (x : Euc d) :
    sb1A D h x = D.invβ * ∑ k, fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x (sb1e k) +
      ∑ k, (fderiv ℝ h x (sb1e k) * (fderiv ℝ D.V x (sb1e k) + sb1F d D.s h k x) +
        h x * (fderiv ℝ (fun y => fderiv ℝ D.V y (sb1e k)) x (sb1e k) +
          fderiv ℝ (sb1F d D.s h k) x (sb1e k))) := by
  unfold sb1A
  congr 1
  exact Finset.sum_congr rfl fun k _ => sb1_flux_deriv D P hd hs0 hsd S k x

theorem sb1_A_joint_cont (H : Sb1Traj D T C B ρ) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => sb1A D (ρ p.1) p.2 := by
  have e : (fun p : Set.Icc (0 : ℝ) T × Euc d => sb1A D (ρ p.1) p.2) = fun p =>
      D.invβ * ∑ k, fderiv ℝ (fun y => fderiv ℝ (ρ p.1) y (sb1e k)) p.2 (sb1e k) +
      ∑ k, (fderiv ℝ (ρ p.1) p.2 (sb1e k) * (fderiv ℝ D.V p.2 (sb1e k) + sb1F d D.s (ρ p.1) k p.2) +
        ρ p.1 p.2 * (fderiv ℝ (fun y => fderiv ℝ D.V y (sb1e k)) p.2 (sb1e k) +
          fderiv ℝ (sb1F d D.s (ρ p.1) k) p.2 (sb1e k))) := by
    funext p
    exact sb1A_expand D H.V H.hd H.hs0 H.hsd (H.slice p.1.1 p.1.2) p.2
  rw [e]
  refine (continuous_const.mul (continuous_finset_sum _ fun k _ => sb1_dd_cont H k)).add
    (continuous_finset_sum _ fun k _ => ?_)
  have hdV : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => fderiv ℝ D.V p.2 (sb1e k) :=
    (sb1_dV_k_contDiff H.V k).continuous.comp continuous_snd
  have hddV : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
      fderiv ℝ (fun y => fderiv ℝ D.V y (sb1e k)) p.2 (sb1e k) :=
    ((((sb1_dV_k_contDiff H.V k).continuous_fderiv (by norm_num)).clm_apply continuous_const)).comp
      continuous_snd
  exact ((sb1_d_cont H k).mul (hdV.add (sb1_F_cont H k))).add
    ((sb1_rho_cont H).mul (hddV.add (sb1_dF_cont H k)))

end HRS.MS.MfeConf
