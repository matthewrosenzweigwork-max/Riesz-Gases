import HRS.Whole.Headline

/-!
# S21: S2.1 part (i) `HRS.Whole.whole_space_stationary` (Headline.lean:334): plan and status, worker S21, 2026-10-23

Frozen statements read: Headline.lean:334 (i), :403 (ii), `IsResultingSolution` :327; TeX supplement L322-336 (class), L348-396
(theorem), proofs L5143-5160 (stationary comparison), L5223-5245 (nonlinear), L3395-3730 (the S5 machinery), L8112 (iii).
No frozen file is edited.  Row S2.1 in coverage.tsv stays `stated` (only clause 1 of (i) is proved, see section 3).

## 0. Verdict

**(i) is TRUE and non-vacuous as frozen, and it does NOT depend on S6.3, S6.7, S9.x, S10.x or S11.x.**  Those rows are prerequisites of
(ii)/(iii): (i) has no `IsResultingSolution`, no window start `a0 > 0` (the window is `a = 0`), no nonlinear trajectory.  Everything
(i) consumes is merged: S3.1/S3.3/S3.4 (thermal data, pressure, static commutator), S4.5 (`quadratic_static_field`), S5.1
(`ul_adjoint_*`, `UlW`/`S85` witnesses), S5.3 (`field_remainder_centered`), S5.6 (`general_paths` internals `s56_*`), F-CAU, CoercLower
(`completionNonnegRd_exists`).  What was missing was new infrastructure (no manuscript row, no frozen change): packets D-F, J (done),
G, H, I, K (open).  `OscAdjointInput` (a hypothesis of `general_paths`) is DERIVED for the stationary coefficients (packet E).

Junk-value audit of the frozen statement (checked against the current Lean text):
* `localizationRate d s C0 N = (N^{-1/d} + sqrt(oN))^{4/(d+4)}`: `Real.sqrt` of a negative number would be junk; avoided by choosing
  `C0 >= 0` (then `oN > 0`, also at `s = 0`: `C0/N + log N/(2dN)`).  `deltaN > 0` in all cases.
* `responseInverse` is `0` when no response exists, so `susceptibilityCov` could be junk; it is not on the arguments that occur
  (`propagatorW 0 t phi_alpha`, bounded smooth): `exists_gaussian_feature` (S4.5) gives the response for every `C_b^J` datum.
* `multivariateGaussian 0 Sigma` takes no psd proof: `Sigma` is psd here, so the `gaussian` field of `IsLinearGaussianEvolutionW`
  is the genuine law.  Non-vacuity of `IsLinearGaussianEvolutionW` is the law identification of packet I (open).
* `Measure.map` of a non-a.e.-measurable map is a Dirac mass: the first two conjuncts (`AEMeasurable`) are part of the claim and are
  PROVED (packet J: the centring `meanEmpirical (P.map (X t))` is the constant probability measure `meanEmpirical P_{N,beta}` on `[0,T]`).
* `GibbsInvariant d s a beta N` is used only to read `law (X t) = canonicalGibbs`, `t <= T`.
* **Normalisation trap (not visible in the statement):** the S5 scales are `sigma_N = min{kappa_N, sqrt(N/invbeta)}`,
  `q_N = sigma_N^2 invbeta/N`.  The frozen theorem uses `sigma = sqrt N`, noise level `q = beta^{-1}`.  In a `WholeSetup` with
  `invbeta = beta^{-1}` one has `sigma <= sqrt(N beta)`: `sigma = sqrt N` only for `beta >= 1`.  The stationary setup (packet D) therefore
  uses `kappa_N = sqrt(N beta)`: `sigma = sqrt(N beta)`, `A = 1`, `q = 1`, i.e. the field `sqrt(beta) zeta_N`; the frozen conclusion
  follows by exact scaling (`smoothDist_map_clm_le`: factor `max(1,c^2)`, `W_1`: factor `c`, `c = beta^{-1/2}`) and the scaling of
  the Gaussian comparator (packet K).
* The completion clause quantifies over ALL `rho_beta` with `IsThermalEquilibrium`: one function (pointwise uniqueness `Mov0.mv0_rho_eq`).
  At `s = 0` the log moment hypothesis of `CompletionNonnegRd` holds (Gaussian decay).

## 1. Clauses of (i) and dependencies

Frozen shape: `exists C0 C, (1: completion) /\ forall rho_beta N, GibbsInvariant -> realizations -> (2) AEMeasurable zeta /\
(3) AEMeasurable Z-window /\ (4) smoothDist 2 <= C (sqrt deltaN + w_N) /\ (5) W_1 <= C (deltaN^{3/20} + sqrt w_N)`.
`C0` is chosen first (>= completion constant, >= the `C0min` of the S5.6-type constants); `C` may depend on `C0`.

| clause | status | where |
|---|---|---|
| 1 completion `0 <= F_N + oN C0 N` | **PROVED** (all `C0 >=` a threshold) | packet A: `s21_clause1_stationary` (WsStatAux2) |
| 2 `AEMeasurable (zetaPathW ..)` | **PROVED** | packet J: `s21_zeta_aemeas` (WsStatAux12) |
| 3 `AEMeasurable (processWindow ..)` | **PROVED** | packet J: `s21_Z_aemeas` |
| 4 `d_2` bound, 5 `W_1` bound | open | `S21Main` (WsStatTie): packets F3, I, G, H, K |

Terms of (4)/(5) (TeX L5143-5160 via L3395-3730):
(a) initial path: `d_2(zeta^0-path, Gaussian path) <= C sqrt deltaN`, `W_1 <= C deltaN^{3/20}`.  Needs the cosine-orbit families
    `f_{n,alpha}`, the static theorem S4.5 (feature form, summable families, proved) and a bounded linear map `l2 -> C([0,T];B_m)`; for `W_1` the
    projection/smoothing argument and `Prob.Metrics.wassersteinE_one_le_of_dual` (finite-dim KR upper bound, proved).  **Open: G (smooth), H (W_1).**
(b) martingale part: `s56_smooth_abstract`, `s56_wasserstein_abstract`, `s56_compare'`, `s56_particle_martingale`, `gff_adapted_coupling_trace`
    (GenPath, proved) with the centred initial `K`-state; convolution lemmas `T25.t25_smoothDist_conv_le`, `t25_smoothDist_affine_le`,
    `wassersteinE_add_indep_le` (proved).  **Open: I (master).**
(c) trace term `E int ||C_r - Cbar_r||_1 <= C q w_N`: `s56_trace_moment` (`S56TraceHyp`), now with the inputs: energy `E|F_N| <= K deltaN`
    and second moments (packet C, proved), rate algebra (packet B, proved: `deltaN <= (3/C0) oN`, `generalLocalizationRate <= C localizationRate`).
(d) centred remainder `E sup ||R~||^2 <= C deltaN`: **PROVED in coordinates** (packet F1/F2: `s21_var_hyp`, `s21_centered_remainder`,
    from `field_remainder_centered_proof`, `S45Static.comm`).  Open: F3 = the centred mild identity linking `R~` (residual of
    `zeta~ = A(k0 - kappa) + T M + R~`) to the coordinates of (d): expectation facts (mean of the Ito integral is 0, `E coord Xi_t = sigma (m_N - rho)(phi_alpha)`,
    Fubini `E int = int E`) and the dense-time argument of `s56_R_bound`.
(e) Gaussian side: law of `Z` is `law(c~) * law(T G)` with `c~` the Gaussian initial path of (a) independent of the Gaussian martingale.  **Open: I.**

## 2. Dependency DAG ([P] proved here, [M] merged earlier, [O] open)

```
completionNonnegRd_exists[M], thermal data[M] ---> A[P] ---------------------------------------> WsStatTie (clause 1)
euclidean_pair_entropy_self[M], S45.s45_static_all[M] ---> C[P] ---> B[P] ---> (c) in I
UlW/S85 witnesses[M], F-CAU[M], s85_thermal_schwartz[M] ---> D[P] ---> E[P] ---> {F3, I}
ul_adjoint_orbit_bounds[M] ---> E[P], G[O]
quadratic_static_field[M] ---> G[O] ---> H[O] ---> I
field_remainder_centered[M], euc_static_commutator[M] ---> F1/F2[P] ---> F3[O] ---> I
s56_* (GenPath)[M], T25 convolution lemmas[M] ---> I[O]
J[P], K[O], I[O] ---> WsStatTie : whole_space_stationary_proof
(S6.3, S6.7, S9-S11: NOT used by (i))
```

## 3. Files (all new, `HRS/MS/WsStat*.lean`, helpers `s21_`, namespace `HRS.MS.S21`; 2409 lines, all compile)

| file | lines | content |
|---|---:|---|
| WsStatAux1 | 169 | this plan (docstring) |
| WsStatAux2 | 149 | A: `s21_completion_of_bounded`, `s21_thermal_bounded`, `s21_clause1_stationary` (clause 1 of (i)), `s21_clause1_resulting` (clause 1 of (ii)) |
| WsStatAux3 | 281 | B: `s21_deltaN_pos/le_one/le_rpow/le_oN`, `s21_oN_pos/le`, `s21_sqrt_le_rpow`, `s21_glr_le_loc` |
| WsStatAux4 | 223 | C: `s21_canonical_eq`, `s21_lintegral_energy_le`, `s21_energy_integral_stationary`, `s21_second_moment_stationary` |
| WsStatAux5-6 | 342 | D1/D2: Schwartz thermal, `s21_gradU_eq`, bounds, `s21_gauss_dom`, `s21_mf_stationary` (thermal density is a stationary `IsWholeMeanFieldSolution`) |
| WsStatAux7 | 134 | D3: `s21Bounds`, `s21Bounds_valid`, `s21_stationary_setup` (stationary `WholeSetup`, `kappa_N = sqrt(N beta)`) |
| WsStatAux8-10 | 432 | E: `s21_stat_deriv`, `s21_isOrbitFeatureK`, `s21_feature_bounds`, `s21_duhamel`, `s21_oscAdjointInput` |
| WsStatAux11 | 68 | D4: `s21_setup_family` (setup + `OscAdjointInput` for every `N`) |
| WsStatAux12 | 73 | J: `s21_Z_aemeas`, `s21_zeta_aemeas` |
| WsStatAux13 | 126 | F1/F2: `s21_evariance_map`, `s21_var_hyp`, `s21_centered_remainder` |
| WsStatAux14 | 140 | F3a: `s21_integral_meanEmpirical`, `s21_E_pair_emp`, `s21_k0_eval_gen` (coordinates of the centring `kappa`, no Bochner expectation), `s21_E_recon` (mean zero of the reconstructed martingale) |
| WsStatAux15 | 147 | F3b: `s21_fubini_comm` (`E int_0^t c_alpha dr = int_0^t E c_alpha dr` with integrability) |
| WsStatAux16 | 63 | F3c (partial): `s21_orbit_data` (`S53Orbit` for the stationary quadratic coefficient); the identity `s21_centered_coord` is NOT written |
| WsStatTie | 62 | `S21Main`, `whole_space_stationary_of_main` (conditional reduction: clause 1 proved, `S21Main` hypothesis) |

## 4. Remaining packets (revised with the observed ratios: D/E/F took 0.25-0.4 of the first estimate)

| id | content | est. lines |
|---|---|---:|
| F3 | (ingredients a/b done: Aux14-16) remaining: `s21_centered_coord` (coord of `R~` = `-(sigma/2) int (c_alpha - E c_alpha)` a.s., via `s56_mild_coord`, `s56_coord_ofMeasureDiff`, `s21_k0_eval_gen`, `s56_fluc_eq_comm`), then the dense-time argument (`R~` continuous, `||R~|| <= sup_t' l2`) | 500-800 |
| I | master: Gaussian coupling space, `s56_smooth_abstract` + `t25_smoothDist_conv_le` (smooth), `s56_wasserstein_abstract` + `wassersteinE_add_indep_le` (W_1), trace term via `s56_trace_moment`, law of `Z` as `c~ * T G` (analogue of `s56_Y_array_law`), constants | 1500-2200 |
| K | scaling `beta < 1` (`c = beta^{-1/2}`), scaled comparator, final constants/quantifier assembly | 400-600 |
| G | initial path static theorem, smooth rate: cosine orbit tests `f_{n,alpha}` (two integrations by parts in `t` with `d_t U = U L`, `a <= 3`), `sum ||f|| < inf`, cosine series, `l2 -> C([0,T];B_m)` bounded linear map, Gaussian path `c~` and its covariance | 2000-3000 |
| H | initial `W_1 <= C deltaN^{3/20}` (rank `R^2` projection, dimension-free smoothing, `wassersteinE_one_le_of_dual`, `wassersteinE_triangle`) | 1500-2500 |
Total remaining for (i): about 6000-9000 lines.  Suggested interface for G+H (a clean `Prop`): there is a probability measure `gamma0` on
`OscPath d (wholeSpaceIndex d) T` with the Gaussian finite-dimensional laws of covariance `C0(U^{0,t}phi_alpha, U^{0,t'}phi_beta)` such that
`smoothDist 2 (law P_{N,beta} initPath) gamma0 <= C sqrt deltaN` and `wassersteinE 1 (...) <= C deltaN^{3/20}`; then I+F3+K close `S21Main`.

## 5. What S7.9 consumes

Exactly the frozen statement `type_of% @HRS.Whole.whole_space_stationary` (hypothesis `h21` of `critical_path_limit_of_S21`,
`shifted_field_path_of_S21`).  No other facet of S2.1.  `whole_space_stationary_of_main` (WsStatTie) is the form in which the remaining gap
is exactly `S21Main` for the constants `C0 >=` a threshold.

## 6. Part (ii) (coarse, not started)

`IsResultingSolution` is a hypothesis of (ii); its clause 1 (completion for `rho t <= C1 rho_beta`) is PROVED (`s21_clause1_resulting`, no S6.3).
The proof of the particle estimates needs a time-dependent `WholeSetup` for `rho_t` (`UlAdjointInput`/`OscAdjointInput` for non-stationary
coefficients: S6.7 `mov_global_adjoint_nonlinear` [O], S.A.12-type theory), pressure along the flow (S6.6/S6.4 [O] or S3.2 stationary pressure),
the tilt static theorem S4.7 (merged), the iid orbit bound (new), and `general_paths_proof` (merged; not the centred version: mean-field
centring costs `sqrt N deltaN`).  Estimate 6-10k lines plus S6.3 N8/N9, S6.4, S6.6, S6.7.  S2.1(iii) needs S9.9-S11.x (about 55k, decision M6: later).

## 7. Decisions / risks

1. Size of (i): 6-9k lines still to do (about 8-11k in total; NEXT_WAVE_PLAN said ~5k).  The two analytic inputs G, H are the only genuinely new mathematics.
2. No frozen statement changes.  `OscAdjointInput` is derived (packet E), not assumed.
3. The `beta < 1` scaling (packet K) is forced by `sigmaScale`; alternatively `kappa_N = sqrt N` works unchanged for `beta >= 1`.
4. The `W_1` initial rate (H) is the least routine piece.


## 8. Status after the continuation (second session)

Proved (all complete, depending only on the three standard foundational principles; new files `HRS/MS/WsStatAux17..39.lean`, about 2.9k lines):
FS (`s21f_filtered`: filtered everywhere-continuous modification of a collision-free strong solution of the quadratic gradient
dynamics; needed because the frozen statement carries no filtration), F3 (`s21_centered_coord`: coordinates of the centred remainder,
`s21_Rt_bound`: dense-time bound), I (`s21_master`: Gaussian coupling space, independence of the initial state, convolution
contractions for the smooth metric and W_1), L (`s21_noiseCov_psd`, `s21_Zlaw`: law of a Gaussian process with covariance
Cc+Cn as a convolution), K (`s21_sigma_eq`, scaling lemmas, `s21_master_Z`, `s21_main_of_init`), and
`whole_space_stationary_of_init`: the frozen statement of S2.1 (i) follows from `S21Init` (WsStatAux34), a clean Prop.

Remaining for S2.1 (i): `S21Init d s a beta T hT` for all data = packets G and H:
* G (smooth rate) + the Gaussian path measure `gamma0` (fdd covariance C_{beta,rho}(U phi_a, U phi_c), PSD), via the cosine (or Schauder)
  time basis `f_{n,alpha}`, the static theorem `quadratic_static_field_proof` for the summable family, `exists_gaussian_feature`,
  and a bounded linear map l2 -> C([0,T];B_m);
* H (W_1 rate delta_N^{3/20}): rank-R projection, Gaussian smoothing, `wassersteinE_one_le_of_dual`, `wassersteinE_triangle`.
Estimate 3000-5000 lines.

Decision for the next workers: G and H are independent and can run in parallel (both consume only `S21Init`'s statement as the
target; G needs orbit data in `C_b^J`, `J > d/2 + 2`, with two time derivatives, i.e. a re-run of `s53_orbit_of_uniq` with a larger `K0`,
then the time basis (cosine or Schauder) and the static theorem; H adds the projection/smoothing argument for `W_1`).
-/

noncomputable section

namespace HRS.MS.S21

end HRS.MS.S21
