/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.LatticeFiberDirac
public import NRS3Hopf.KogutSusskindSpectrum

/-!
# Transverse lower bound for Dirac-type spatial operators with fiber mass and bridge to pure gauge Kogut-Susskind

The lower bound on the fiber term `M_w`, `‖M_w χ‖² ≥ ‖χ‖²/4` (`LatticeFiberDirac.norm_sq_fiber_ge`),
transfers to the rest operator `A + M_w` whenever `A` is symmetric and anticommutes with `M_w`.

This file provides:
1. Abstract bounds: `norm_sq_rest_ge_of_anticomm` and `abs_energy_ge_of_anticomm`.
2. Free case recovery: `dirac_gap_free_instance` recovering the uncoupled Dirac bound.
3. Real symmetric weights / ℤ₂ sector: `SymmetricHopWeight` (real weights `|u| ≤ 1`, symmetric).
4. U(1) phase gauge links: complex link variables `u : Site → ℂ` with `‖u p‖ ≤ 1`,
   hermitian hop `hopC` with complex conjugation on the reverse hop, and formal proof that
   `{A_u1 U, M_w} = 0` and `‖(A_u1 U + M_w) χ‖² ≥ ‖χ‖²/4` for ANY fiber-independent U(1) gauge field.
5. Bridge to the pure gauge Kogut-Susskind spectrum: `pure_gauge_joint_spectral_bridge` and
   `pure_gauge_kogut_susskind_dirac_eigenvalue_bridge` proving that the joint excitation spectrum
   of pure gauge Kogut-Susskind and transverse Dirac fields is strictly bounded from below by
   `min λE (1/2) > 0` (and `≥ 1/2` when `λE ≥ 1/2`), protecting against massless mode collapse.
-/

@[expose] public noncomputable section

open Complex Finset SiteHopL2 LatticeFiberDirac KogutSusskind KogutSusskindGap KogutSusskindSpectrum

namespace DiracGapGaugeInvariant

/-! ## 1. Abstract anticommutation lemmas -/

/-- For ANY symmetric operator `A` on `H` that anticommutes with the fiber term `M_w`,
the rest `A + M_w` satisfies `‖(A + M_w) χ‖² ≥ ‖χ‖²/4`. -/
theorem norm_sq_rest_ge_of_anticomm {A : H →ₗ[ℂ] H} (hA : A.IsSymmetric)
    (h_anticomm : ∀ χ : H, A (Mw χ) = -Mw (A χ)) (χ : H) :
    (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖(A + Mw) χ‖ ^ 2 := by
  have h := DiracSpeed.norm_sq_add_of_anticomm hA Mw_isSymmetric h_anticomm χ
  have hM : ‖Mw χ‖ ^ 2 = ‖Tw χ‖ ^ 2 := by
    rw [norm_sq_eq_re_inner Mw_isSymmetric, norm_sq_eq_re_inner Tw_isSymmetric, Mw_sq]
  have hr : (A + Mw) χ = A χ + Mw χ := rfl
  rw [hr, h, hM]
  nlinarith only [norm_sq_fiber_ge χ, sq_nonneg ‖A χ‖]

/-- If `T_x` is symmetric and anticommutes with `A + M_w`, any eigenvalue of `T_x + A + M_w`
has `|E| ≥ 1/2`. -/
theorem abs_energy_ge_of_anticomm {A : H →ₗ[ℂ] H} (hA : A.IsSymmetric)
    (h_anticomm : ∀ χ : H, A (Mw χ) = -Mw (A χ))
    (hTx_rest : ∀ χ : H, Tx ((A + Mw) χ) = -(A + Mw) (Tx χ))
    {E : ℝ} {χ : H} (hχ : χ ≠ 0)
    (hE : (Tx + (A + Mw)) χ = (E : ℂ) • χ) :
    1 / 2 ≤ |E| := by
  have h_rest_symm : (A + Mw).IsSymmetric := hA.add Mw_isSymmetric
  have h := DiracSpeed.abs_energy_ge Tx_isSymmetric h_rest_symm hTx_rest
    (m := 1 / 2) (norm_sq_rest_ge_of_anticomm hA h_anticomm) hχ hE
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h

/-! ## 2. Free lattice Dirac instance -/

/-- Recovery of the uncoupled free lattice Dirac bound (`LatticeFiberDirac.abs_energy_ge`)
as a direct instance of `abs_energy_ge_of_anticomm`. -/
theorem dirac_gap_free_instance {E : ℝ} {χ : H} (hχ : χ ≠ 0)
    (hE : dirac χ = (E : ℂ) • χ) : 1 / 2 ≤ |E| :=
  abs_energy_ge_of_anticomm AyAz_isSymmetric AyAz_Mw Tx_rest hχ hE

/-! ## 3. Real symmetric hopping weights / ℤ₂ sector -/

/-- A real hopping weight along direction `τ_dir` with `|u| ≤ 1`, symmetric along the link
and independent of the fiber `w`. This models real background modulations or ℤ₂ gauge fields. -/
structure SymmetricHopWeight (τ_dir : Site ≃ Site) where
  u : Site → ℝ
  hu : ∀ p, |u p| ≤ 1
  h_symm : ∀ p, u (τ_dir p) = u p
  h_w : ∀ p, u (τw p) = u p
  h_ws : ∀ p, u (τw.symm p) = u p

theorem sx_τy (p : Site) : sx (τy p) = sx p := rfl
theorem sx_τw (p : Site) : sx (τw p) = sx p := rfl
theorem sx_τws (p : Site) : sx (τw.symm p) = sx p := rfl

theorem sxy_τz (p : Site) : sxy (τz p) = sxy p := rfl
theorem sxy_τw (p : Site) : sxy (τw p) = sxy p := rfl
theorem sxy_τws (p : Site) : sxy (τw.symm p) = sxy p := rfl

/-- The hopping weight for direction `y`: `c_y(p) = sx(p) * u_y(p)`. -/
def cy (Uy : SymmetricHopWeight τy) (p : Site) : ℝ := sx p * Uy.u p

theorem abs_cy (Uy : SymmetricHopWeight τy) (p : Site) : |cy Uy p| ≤ 1 := by
  simp only [cy, abs_mul]
  have h1 := abs_sx p
  have h2 := Uy.hu p
  have n1 := abs_nonneg (sx p)
  have n2 := abs_nonneg (Uy.u p)
  nlinarith

theorem cy_τy (Uy : SymmetricHopWeight τy) (p : Site) : cy Uy (τy p) = cy Uy p := by
  simp only [cy, sx_τy, Uy.h_symm]

theorem cy_τw (Uy : SymmetricHopWeight τy) (p : Site) : cy Uy (τw p) = cy Uy p := by
  simp only [cy, sx_τw, Uy.h_w]

theorem cy_τws (Uy : SymmetricHopWeight τy) (p : Site) : cy Uy (τw.symm p) = cy Uy p := by
  simp only [cy, sx_τws, Uy.h_ws]

/-- The real spatial hop along `y`. -/
def Ay_real (Uy : SymmetricHopWeight τy) : H →ₗ[ℂ] H :=
  hop τy (abs_cy Uy)

theorem Ay_real_isSymmetric (Uy : SymmetricHopWeight τy) : (Ay_real Uy).IsSymmetric :=
  hop_isSymmetric _ _ (cy_τy Uy)

/-- The hopping weight for direction `z`: `c_z(p) = sxy(p) * u_z(p)`. -/
def cz (Uz : SymmetricHopWeight τz) (p : Site) : ℝ := sxy p * Uz.u p

theorem abs_cz (Uz : SymmetricHopWeight τz) (p : Site) : |cz Uz p| ≤ 1 := by
  simp only [cz, abs_mul]
  have h1 := abs_sxy p
  have h2 := Uz.hu p
  have n1 := abs_nonneg (sxy p)
  have n2 := abs_nonneg (Uz.u p)
  nlinarith

theorem cz_τz (Uz : SymmetricHopWeight τz) (p : Site) : cz Uz (τz p) = cz Uz p := by
  simp only [cz, sxy_τz, Uz.h_symm]

theorem cz_τw (Uz : SymmetricHopWeight τz) (p : Site) : cz Uz (τw p) = cz Uz p := by
  simp only [cz, sxy_τw, Uz.h_w]

theorem cz_τws (Uz : SymmetricHopWeight τz) (p : Site) : cz Uz (τw.symm p) = cz Uz p := by
  simp only [cz, sxy_τws, Uz.h_ws]

/-- The real spatial hop along `z`. -/
def Az_real (Uz : SymmetricHopWeight τz) : H →ₗ[ℂ] H :=
  hop τz (abs_cz Uz)

theorem Az_real_isSymmetric (Uz : SymmetricHopWeight τz) : (Az_real Uz).IsSymmetric :=
  hop_isSymmetric _ _ (cz_τz Uz)

/-- The real transverse operator `A_real = A_y + A_z`. -/
def A_real (Uy : SymmetricHopWeight τy) (Uz : SymmetricHopWeight τz) : H →ₗ[ℂ] H :=
  Ay_real Uy + Az_real Uz

theorem A_real_isSymmetric (Uy : SymmetricHopWeight τy) (Uz : SymmetricHopWeight τz) :
    (A_real Uy Uz).IsSymmetric :=
  (Ay_real_isSymmetric Uy).add (Az_real_isSymmetric Uz)

theorem τy_τw (p : Site) : τw (τy p) = τy (τw p) := rfl
theorem τy_τws (p : Site) : τw.symm (τy p) = τy (τw.symm p) := rfl
theorem τys_τw (p : Site) : τw (τy.symm p) = τy.symm (τw p) := rfl
theorem τys_τws (p : Site) : τw.symm (τy.symm p) = τy.symm (τw.symm p) := rfl

theorem τz_τw (p : Site) : τw (τz p) = τz (τw p) := rfl
theorem τz_τws (p : Site) : τw.symm (τz p) = τz (τw.symm p) := rfl
theorem τzs_τw (p : Site) : τw (τz.symm p) = τz.symm (τw p) := rfl
theorem τzs_τws (p : Site) : τw.symm (τz.symm p) = τz.symm (τw.symm p) := rfl

theorem Ay_real_Mw (Uy : SymmetricHopWeight τy) (χ : H) :
    Ay_real Uy (Mw χ) = -Mw (Ay_real Uy χ) := by
  simp only [Ay_real, Mw]
  exact hop_hop_anticomm (abs_cy Uy) abs_sxyz τy_τw τy_τws τys_τw τys_τws
    (cy_τw Uy) (cy_τws Uy) sxyz_τy sxyz_τy_symm χ

theorem Az_real_Mw (Uz : SymmetricHopWeight τz) (χ : H) :
    Az_real Uz (Mw χ) = -Mw (Az_real Uz χ) := by
  simp only [Az_real, Mw]
  exact hop_hop_anticomm (abs_cz Uz) abs_sxyz τz_τw τz_τws τzs_τw τzs_τws
    (cz_τw Uz) (cz_τws Uz) sxyz_τz sxyz_τz_symm χ

theorem A_real_Mw (Uy : SymmetricHopWeight τy) (Uz : SymmetricHopWeight τz) (χ : H) :
    A_real Uy Uz (Mw χ) = -Mw (A_real Uy Uz χ) := by
  simp only [A_real, LinearMap.add_apply, map_add, neg_add]
  rw [Ay_real_Mw Uy χ, Az_real_Mw Uz χ]

theorem norm_sq_rest_ge_real (Uy : SymmetricHopWeight τy) (Uz : SymmetricHopWeight τz) (χ : H) :
    (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖(A_real Uy Uz + Mw) χ‖ ^ 2 :=
  norm_sq_rest_ge_of_anticomm (A_real_isSymmetric Uy Uz) (A_real_Mw Uy Uz) χ

/-! ## 4. U(1) phase gauge links -/

theorem memℓp_shiftC {u : Site → ℂ} (hu : ∀ p, ‖u p‖ ≤ 1) (χ : H) (τ : Site ≃ Site) :
    Memℓp (fun p => u p * χ (τ p)) 2 := by
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have hχ := (memℓp_gen_iff h2).mp (lp.memℓp χ)
  refine (memℓp_gen_iff h2).mpr ((τ.summable_iff.mpr hχ).of_nonneg_of_le
    (fun _ => by positivity) fun p => ?_)
  rw [norm_mul]
  exact Real.rpow_le_rpow (by positivity) (mul_le_of_le_one_left (norm_nonneg _) (hu p))
    (by positivity)

/-- Complex weighted shift on `H = L2 Site`. -/
def shiftC (τ : Site ≃ Site) {u : Site → ℂ} (hu : ∀ p, ‖u p‖ ≤ 1) : H →ₗ[ℂ] H where
  toFun χ := ⟨fun p => u p * χ (τ p), memℓp_shiftC hu χ τ⟩
  map_add' χ η := lp.ext <| funext fun p => by
    simp only [lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' s χ := lp.ext <| funext fun p => by
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem shiftC_apply (τ : Site ≃ Site) {u : Site → ℂ} (hu : ∀ p, ‖u p‖ ≤ 1) (χ : H) (p : Site) :
    shiftC τ hu χ p = u p * χ (τ p) := rfl

/-- The Hermitian adjoint link variable: `u*(p) = conj(u(τ⁻¹ p))`. -/
def u_adj (u : Site → ℂ) (τ : Site ≃ Site) : Site → ℂ :=
  fun p => starRingEnd ℂ (u (τ.symm p))

theorem norm_u_adj (τ : Site ≃ Site) {u : Site → ℂ} (hu : ∀ p, ‖u p‖ ≤ 1) (p : Site) :
    ‖u_adj u τ p‖ ≤ 1 := by
  simp only [u_adj, RCLike.norm_conj]
  exact hu _

theorem inner_shiftC (τ : Site ≃ Site) {u : Site → ℂ} (hu : ∀ p, ‖u p‖ ≤ 1) (φ χ : H) :
    inner ℂ (shiftC τ hu φ) χ = inner ℂ φ (shiftC τ.symm (norm_u_adj τ hu) χ) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, ← τ.symm.tsum_eq]
  refine tsum_congr fun q => ?_
  simp only [shiftC_apply, Equiv.apply_symm_apply, RCLike.inner_apply', map_mul, u_adj]
  ring

theorem u_adj_adj (τ : Site ≃ Site) (u : Site → ℂ) (p : Site) :
    u_adj (u_adj u τ) τ.symm p = u p := by
  simp only [u_adj, Equiv.symm_symm, Equiv.symm_apply_apply, starRingEnd_apply, star_star]

theorem shiftC_adj_adj (τ : Site ≃ Site) {u : Site → ℂ} (hu : ∀ p, ‖u p‖ ≤ 1) :
    shiftC τ.symm.symm (norm_u_adj τ.symm (norm_u_adj τ hu)) = shiftC τ hu := by
  ext ψ p
  simp only [shiftC_apply, Equiv.symm_symm, u_adj_adj]

/-- The gauge-covariant Hermitian hop operator: `(1/2)(T_u + T_u†)`. -/
def hopC (τ : Site ≃ Site) {u : Site → ℂ} (hu : ∀ p, ‖u p‖ ≤ 1) : H →ₗ[ℂ] H :=
  (1 / 2 : ℂ) • (shiftC τ hu + shiftC τ.symm (norm_u_adj τ hu))

theorem hopC_apply (τ : Site ≃ Site) {u : Site → ℂ} (hu : ∀ p, ‖u p‖ ≤ 1) (χ : H) (p : Site) :
    hopC τ hu χ p = (1 / 2 : ℂ) * (u p * χ (τ p) + starRingEnd ℂ (u (τ.symm p)) * χ (τ.symm p)) := by
  simp only [hopC, LinearMap.smul_apply, LinearMap.add_apply, lp.coeFn_smul, lp.coeFn_add,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, shiftC_apply, u_adj]

/-- `hopC` is symmetric (Hermitian) for ANY bounded complex link variable `u`. -/
theorem hopC_isSymmetric (τ : Site ≃ Site) {u : Site → ℂ} (hu : ∀ p, ‖u p‖ ≤ 1) :
    (hopC τ hu).IsSymmetric := by
  intro φ χ
  have e1 := inner_shiftC τ hu φ χ
  have e2 := inner_shiftC τ.symm (norm_u_adj τ hu) φ χ
  have h_adj := shiftC_adj_adj τ hu
  rw [h_adj] at e2
  simp only [hopC, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, e1, e2]
  simp only [map_div₀, map_one, map_ofNat]
  ring

/-- A spatial U(1) gauge link variable along direction `τ_dir` that is independent of `w`. -/
structure U1GaugeLink (τ_dir : Site ≃ Site) where
  u : Site → ℂ
  hu : ∀ p, ‖u p‖ ≤ 1
  h_w : ∀ p, u (τw p) = u p
  h_ws : ∀ p, u (τw.symm p) = u p

/-- The U(1) gauge hopping weight for direction `y`: `c_y(p) = sx(p) * u_y(p)`. -/
def cy_u1 (Uy : U1GaugeLink τy) (p : Site) : ℂ := (sx p : ℂ) * Uy.u p

theorem abs_cy_u1 (Uy : U1GaugeLink τy) (p : Site) : ‖cy_u1 Uy p‖ ≤ 1 := by
  simp only [cy_u1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := abs_sx p
  have h2 := Uy.hu p
  have n1 := abs_nonneg (sx p)
  have n2 := norm_nonneg (Uy.u p)
  nlinarith

/-- The U(1) gauge spatial hop along `y`. -/
def Ay_u1 (Uy : U1GaugeLink τy) : H →ₗ[ℂ] H :=
  hopC τy (abs_cy_u1 Uy)

theorem Ay_u1_isSymmetric (Uy : U1GaugeLink τy) : (Ay_u1 Uy).IsSymmetric :=
  hopC_isSymmetric τy (abs_cy_u1 Uy)

/-- The U(1) gauge hopping weight for direction `z`: `c_z(p) = sxy(p) * u_z(p)`. -/
def cz_u1 (Uz : U1GaugeLink τz) (p : Site) : ℂ := (sxy p : ℂ) * Uz.u p

theorem abs_cz_u1 (Uz : U1GaugeLink τz) (p : Site) : ‖cz_u1 Uz p‖ ≤ 1 := by
  simp only [cz_u1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := abs_sxy p
  have h2 := Uz.hu p
  have n1 := abs_nonneg (sxy p)
  have n2 := norm_nonneg (Uz.u p)
  nlinarith

/-- The U(1) gauge spatial hop along `z`. -/
def Az_u1 (Uz : U1GaugeLink τz) : H →ₗ[ℂ] H :=
  hopC τz (abs_cz_u1 Uz)

theorem Az_u1_isSymmetric (Uz : U1GaugeLink τz) : (Az_u1 Uz).IsSymmetric :=
  hopC_isSymmetric τz (abs_cz_u1 Uz)

/-- The transverse U(1) gauge operator `A_u1 = A_y[U] + A_z[U]`. -/
def A_u1 (Uy : U1GaugeLink τy) (Uz : U1GaugeLink τz) : H →ₗ[ℂ] H :=
  Ay_u1 Uy + Az_u1 Uz

theorem A_u1_isSymmetric (Uy : U1GaugeLink τy) (Uz : U1GaugeLink τz) :
    (A_u1 Uy Uz).IsSymmetric :=
  (Ay_u1_isSymmetric Uy).add (Az_u1_isSymmetric Uz)

theorem sx_τys (p : Site) : sx (τy.symm p) = sx p := rfl
theorem sxy_τzs (p : Site) : sxy (τz.symm p) = sxy p := rfl

/-- **Anticommutation with the fiber term**:
`A_y[U]` anticommutes with `M_w` because `sxyz` flips sign under `τy`, while `U` is independent of `w`. -/
theorem Ay_u1_Mw (Uy : U1GaugeLink τy) (χ : H) :
    Ay_u1 Uy (Mw χ) = -Mw (Ay_u1 Uy χ) := by
  refine lp.ext <| funext fun p => ?_
  have h1 : sxyz (τy p) = -sxyz p := sxyz_τy p
  have h2 : sxyz (τy.symm p) = -sxyz p := sxyz_τy_symm p
  have hU1 : Uy.u (τy.symm (τw p)) = Uy.u (τy.symm p) := by
    rw [← τys_τw, Uy.h_w]
  have hU2 : Uy.u (τy.symm (τw.symm p)) = Uy.u (τy.symm p) := by
    rw [← τys_τws, Uy.h_ws]
  simp only [Ay_u1, Mw, hopC_apply, hop_apply, lp.coeFn_neg, Pi.neg_apply,
    cy_u1, sx_τw, sx_τws, sx_τys,
    τy_τw, τy_τws, τys_τw, τys_τws, hU1, hU2,
    Uy.h_w, Uy.h_ws, starRingEnd_apply]
  rw [h1, h2]
  push_cast
  ring

/-- **Anticommutation with the fiber term**:
`A_z[U]` anticommutes with `M_w` because `sxyz` flips sign under `τz`, while `U` is independent of `w`. -/
theorem Az_u1_Mw (Uz : U1GaugeLink τz) (χ : H) :
    Az_u1 Uz (Mw χ) = -Mw (Az_u1 Uz χ) := by
  refine lp.ext <| funext fun p => ?_
  have h1 : sxyz (τz p) = -sxyz p := sxyz_τz p
  have h2 : sxyz (τz.symm p) = -sxyz p := sxyz_τz_symm p
  have hU1 : Uz.u (τz.symm (τw p)) = Uz.u (τz.symm p) := by
    rw [← τzs_τw, Uz.h_w]
  have hU2 : Uz.u (τz.symm (τw.symm p)) = Uz.u (τz.symm p) := by
    rw [← τzs_τws, Uz.h_ws]
  simp only [Az_u1, Mw, hopC_apply, hop_apply, lp.coeFn_neg, Pi.neg_apply,
    cz_u1, sxy_τw, sxy_τws, sxy_τzs,
    τz_τw, τz_τws, τzs_τw, τzs_τws, hU1, hU2,
    Uz.h_w, Uz.h_ws, starRingEnd_apply]
  rw [h1, h2]
  push_cast
  ring

/-- **PROVED**: For any fiber-independent U(1) gauge configuration `(U_y, U_z)`,
the transverse gauge operator `A_u1 = A_y[U] + A_z[U]` anticommutes with the fiber mass `M_w`. -/
theorem A_u1_Mw (Uy : U1GaugeLink τy) (Uz : U1GaugeLink τz) (χ : H) :
    A_u1 Uy Uz (Mw χ) = -Mw (A_u1 Uy Uz χ) := by
  simp only [A_u1, LinearMap.add_apply, map_add, neg_add]
  rw [Ay_u1_Mw Uy χ, Az_u1_Mw Uz χ]

/-- **Transverse bound in the presence of U(1) gauge field `U`**:
For ANY spatial U(1) gauge configuration `(U_y, U_z)` decoupled from the fiber `w`,
the rest operator satisfies `‖(A_u1[U] + M_w) χ‖² ≥ ‖χ‖²/4`. -/
theorem norm_sq_rest_ge_u1 (Uy : U1GaugeLink τy) (Uz : U1GaugeLink τz) (χ : H) :
    (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖(A_u1 Uy Uz + Mw) χ‖ ^ 2 :=
  norm_sq_rest_ge_of_anticomm (A_u1_isSymmetric Uy Uz) (A_u1_Mw Uy Uz) χ

/-- A pure U(1) gauge link variable with `‖u p‖ = 1` (exact unitary phase `exp(i θ)`),
independent of the fiber `w`. This is the exact unitary U(1) gauge subcase of `U1GaugeLink`. -/
structure PureU1GaugeLink (τ_dir : Site ≃ Site) extends U1GaugeLink τ_dir where
  hu_unit : ∀ p, ‖u p‖ = 1

/-- **Transverse bound for pure U(1) gauge fields**:
For ANY spatial configuration of unitary U(1) phase links `(U_y, U_z)` decoupled from `w`,
`‖(A_u1[U] + M_w) χ‖² ≥ ‖χ‖²/4`. -/
theorem norm_sq_rest_ge_pure_u1 (Uy : PureU1GaugeLink τy) (Uz : PureU1GaugeLink τz) (χ : H) :
    (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖(A_u1 Uy.toU1GaugeLink Uz.toU1GaugeLink + Mw) χ‖ ^ 2 :=
  norm_sq_rest_ge_u1 Uy.toU1GaugeLink Uz.toU1GaugeLink χ

/-! ## 5. Bridge to the pure gauge Kogut-Susskind spectrum -/

/-- Under ANY pure gauge configuration `(Uy, Uz)`, the transverse Dirac rest operator
satisfies `‖(A_u1[U] + M_w) χ‖ ≥ (1/2) * ‖χ‖`. -/
theorem pure_gauge_dirac_norm_ge (Uy : PureU1GaugeLink τy) (Uz : PureU1GaugeLink τz) (χ : H) :
    (1 / 2 : ℝ) * ‖χ‖ ≤ ‖(A_u1 Uy.toU1GaugeLink Uz.toU1GaugeLink + Mw) χ‖ := by
  have hsq := norm_sq_rest_ge_pure_u1 Uy Uz χ
  have hpos : 0 ≤ (1 / 2 : ℝ) * ‖χ‖ := mul_nonneg (by norm_num) (norm_nonneg χ)
  have hpos2 : 0 ≤ ‖(A_u1 Uy.toU1GaugeLink Uz.toU1GaugeLink + Mw) χ‖ := norm_nonneg _
  have h2 : ((1 / 2 : ℝ) * ‖χ‖) ^ 2 = (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 := mul_pow (1 / 2 : ℝ) ‖χ‖ 2
  rw [← h2] at hsq
  nlinarith

/-- The joint spectral gap floor `min lE (1/2)` is strictly positive for any positive electric coupling. -/
theorem pure_gauge_joint_gap_pos {lE : ℝ} (hlE : 0 < lE) :
    0 < min lE (1 / 2 : ℝ) :=
  lt_min hlE (by norm_num)

/-- **The Bridge between the pure gauge Kogut-Susskind spectrum and the gauge-invariant Dirac spectrum**:
For any positive electric coupling `0 < lE` and any magnetic coupling `0 ≤ lB`,
and for ANY pure gauge configuration `(Uy, Uz)`:
1. Every excited pure gauge Kogut-Susskind state `ψ` (orthogonal to constants) has energy at least
   `min lE (1/2) * ‖ψ‖²`.
2. Every fermionic state `χ` in the pure gauge background has transverse Dirac energy norm squared at least
   `(min lE (1/2))² * ‖χ‖²`.
Thus, neither the pure gauge excitations nor the fermionic excitations can collapse to zero gap. -/
theorem pure_gauge_joint_spectral_bridge
    {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Group G] [Fintype G] [DecidableEq G] {n : ℕ}
    (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι) (R : Finset (ι × δ × δ))
    {lE lB : ℝ} (hE : 0 < lE) (hB : 0 ≤ lB)
    (Uy : PureU1GaugeLink τy) (Uz : PureU1GaugeLink τz) :
    let Δ := min lE (1 / 2 : ℝ)
    0 < Δ ∧
    (∀ ψ : State ι δ G, (∑ U, ψ U = 0) → Δ * nsq ψ ≤ (ip ψ (ham ρ τ R lE lB ψ)).re) ∧
    (∀ χ : H, Δ ^ 2 * ‖χ‖ ^ 2 ≤ ‖(A_u1 Uy.toU1GaugeLink Uz.toU1GaugeLink + Mw) χ‖ ^ 2) := by
  intro Δ
  have hΔpos : 0 < Δ := lt_min hE (by norm_num)
  refine ⟨hΔpos, fun ψ h0 => ?_, fun χ => ?_⟩
  · have h_ks := gap_ham ρ τ R (le_of_lt hE) hB ψ h0
    have h_le : Δ ≤ lE := min_le_left lE (1 / 2)
    have hnsq : 0 ≤ nsq ψ := nsq_nonneg ψ
    nlinarith
  · have h_dirac := norm_sq_rest_ge_pure_u1 Uy Uz χ
    have hΔ_sq : Δ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      nlinarith [min_le_right lE (1 / 2 : ℝ)]
    have hχ : 0 ≤ ‖χ‖ ^ 2 := sq_nonneg ‖χ‖
    nlinarith

/-- **Eigenvalue form of the bridge**:
In the pure gauge Kogut-Susskind spectrum with `lB * 2n|R| < lE`, all non-vacuum eigenvalues
satisfy `1/2 ≤ μ_i`, and every fermionic eigenvalue of `Tx + A_u1[U] + Mw` in the pure gauge background
satisfies `1/2 ≤ |E|` when `lE ≥ 1/2`. -/
theorem pure_gauge_kogut_susskind_dirac_eigenvalue_bridge
    {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Group G] [Fintype G] [DecidableEq G] {n : ℕ}
    (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι) (R : Finset (ι × δ × δ))
    {lE lB : ℝ} (hE : 1 / 2 ≤ lE) (hB : 0 ≤ lB) (hsmall : lB * (2 * n * R.card) < lE)
    {m : ℕ} (hm : Module.finrank ℂ (EH ι δ G) = m)
    (Uy : PureU1GaugeLink τy) (Uz : PureU1GaugeLink τz)
    (hTx_rest : ∀ χ : H, Tx ((A_u1 Uy.toU1GaugeLink Uz.toU1GaugeLink + Mw) χ)
      = -(A_u1 Uy.toU1GaugeLink Uz.toU1GaugeLink + Mw) (Tx χ))
    {E : ℝ} {χ : H} (hχ : χ ≠ 0)
    (hE_dirac : (Tx + (A_u1 Uy.toU1GaugeLink Uz.toU1GaugeLink + Mw)) χ = (E : ℂ) • χ) :
    (∃ i0 : Fin m, ∀ i, i ≠ i0 → 1 / 2 ≤ (HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB)).eigenvalues hm i) ∧
    1 / 2 ≤ |E| := by
  have hE_nonneg : 0 ≤ lE := by linarith
  obtain ⟨i0, -, hall⟩ := spectral_gap hE_nonneg hB hsmall hm
  refine ⟨⟨i0, fun i hi => le_trans hE (hall i hi)⟩, ?_⟩
  exact abs_energy_ge_of_anticomm
    (A_u1_isSymmetric Uy.toU1GaugeLink Uz.toU1GaugeLink)
    (A_u1_Mw Uy.toU1GaugeLink Uz.toU1GaugeLink)
    hTx_rest hχ hE_dirac

end DiracGapGaugeInvariant
