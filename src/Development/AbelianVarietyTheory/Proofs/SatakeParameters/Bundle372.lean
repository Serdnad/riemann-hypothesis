module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle188
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle360
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle368
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle192
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle354
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle176
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle332
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle165
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle004
public import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle369
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle370
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle212
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle373
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle355
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.TwoUnits

theorem embLL_mem (D : D7) (z : D.what₂.LL) : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral z).map D.what₂.embLL.toRatAlgHom

theorem lamC_zpow {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (n : ℤ) :
    TaylorLogMetric.lamC lam (x ^ n) = TaylorLogMetric.lamC lam x ^ n := by
  rw [Formalism.L2.Ker.lamC_of_mem lam (zpow_mem hx n), Formalism.L2.Ker.lamC_of_mem lam hx, ← map_zpow₀]
  congr 1

theorem lamC_inv {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x⁻¹ = (TaylorLogMetric.lamC lam x)⁻¹ := by
  rw [Formalism.L2.Ker.lamC_of_mem lam (inv_mem hx), Formalism.L2.Ker.lamC_of_mem lam hx, ← map_inv₀]
  rfl

end GlobalTheory.TwV.Xc.TwoUnits


open GlobalTheory.TwV.Xc.TwoUnits in

theorem GlobalTheory.TwV.Xc.two_units : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => KIn t → S.Pos → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, (sysS H X std).Lv.comp j → (sysS H X std).Lv.comp (j + 1) → ∃ a b : (sysS H X std).G.Kf, (sysS H X std).vEqK a 0 ∧ (sysS H X std).vEqK b 0 ∧ S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) ∧ S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hKIn hPos v π hπ j hj hcj hcj1
  have hπU : π ∈ U1 (sigD D) := hπ.1
  obtain ⟨rm, hrm⟩ := GlobalTheory.T.stepCharacter_uniformizingIdele_mem_coeffField S hD hS hKIn v π hπ j hj
  obtain ⟨ra, hra⟩ := GlobalTheory.T.kernelSite_normalisingCharPow_values_in_coeffField S hD hS j hj.le hcj π hπU
  obtain ⟨rb, hrb⟩ := GlobalTheory.T.kernelSite_normalisingCharPow_values_in_coeffField S hD hS (j + 1) hj hcj1 π hπU
  have hfill := GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hS j hj hcj1
  have hnorm := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj hfill π hπU
  have hord : ∀ v' : (sysS H X std).Pl, ordA (A0 J) v' π = if v' = v then 1 else 0 := by
    intro v'
    split_ifs with h
    · subst h; exact hπ.2.2
    · exact ((GlobalTheory.TwV.Xc.OrdA.ordA_props _ _ _ _ _ (A0 J) (GlobalTheory.TwV.LbB.locInt_locAt _) hS.1 v').2.2.2 v (Ne.symm h) π hπ.2.1)
  have hsum : (∑ v' : (sysS H X std).Pl, (sysS H X std).vm v' (j + 1) * ordA (A0 J) v' π) = (sysS H X std).vm v (j + 1) := by
    rw [Finset.sum_eq_single v]
    · rw [hord v, if_pos rfl, mul_one]
    · intro b _ hb; rw [hord b, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ v) h
  rw [hsum] at hnorm
  obtain ⟨𝔞, h𝔞, hχ⟩ := (GlobalTheory.T.charOnNormOneIdeles_mul_unramified_classValue S hD hS).2.2.2 π hπU
  have hcur := S.curve
  have hp2 : D.what₂.places.resChar w ≠ 2 := by have := hcur.1; omega
  obtain ⟨hQ, -, hone⟩ := GlobalTheory.TwV.Xc.chi_alg_unit_inert D _ S.lam t.χ hcur.2.2.2.2.2.2.1 hp2 hcur.2.2.1 𝔞 h𝔞
  rw [← hχ] at hQ hone
  have hpK : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero)
  have hmQ : S.muT (j + 1) π ∈ TaylorLogMetric.Qbar := hrm ▸ embLL_mem D rm
  have hK : ∀ r : D.what₂.LL, S.E.iK (ex.cmp.embW u w hg r) = TaylorLogMetric.lamC S.lam (D.what₂.embLL r) := fun r =>
    (S.hK r (embLL_mem D r)).trans (Formalism.L2.Ker.lamC_of_mem S.lam (embLL_mem D r)).symm
  refine ⟨((D.what₂.places.resChar w : ℕ) : (sysS H X std).G.Kf) ^ (-((sysS H X std).vm v (j + 1))) * ex.cmp.embW u w hg (rm * ra),
    ((D.what₂.places.resChar w : ℕ) : (sysS H X std).G.Kf) ^ ((sysS H X std).vm v (j + 1)) * ex.cmp.embW u w hg (rm⁻¹ * rb⁻¹), ?_, ?_, ?_, ?_⟩
  · apply GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb
    show ‖S.E.iK _‖ = 1
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, hrm, hra, Formalism.L2.Ker.lamC_mul S.lam hmQ (zpow_mem hQ _), lamC_zpow S.lam hQ,
      norm_mul, norm_mul, norm_zpow, norm_zpow, hnorm, hone, one_zpow, mul_one, ← zpow_add₀ hpK, neg_add_cancel, zpow_zero]
  · apply GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb
    show ‖S.E.iK _‖ = 1
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, map_inv₀, map_inv₀, hrm, hrb, Formalism.L2.Ker.lamC_mul S.lam (inv_mem hmQ) (inv_mem (zpow_mem hQ _)),
      lamC_inv S.lam hmQ, lamC_inv S.lam (zpow_mem hQ _), lamC_zpow S.lam hQ,
      norm_mul, norm_mul, norm_inv, norm_inv, norm_zpow, norm_zpow, hnorm, hone, one_zpow, inv_one, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ hpK)]
  · show S.E.iK _ = _
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, hrm, hra]
  · show S.E.iK _ = _
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, map_inv₀, map_inv₀, hrm, hrb, zpow_neg (chiI J π)]

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc.DetIdChi

open Matrix

theorem heq_transport (D : D7) {n N : ℕ} (h : n = N) (K : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (K' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (hK : HEq K K') :
    (IsSDLat D.host.E n K → IsSDLat D.host.E N K') ∧ TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) K = TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) K' := by
  subst h
  cases eq_of_heq hK
  exact ⟨id, rfl⟩

def coGL {E : Type} [Field E] {N : ℕ} (f : (Fin N → E) ≃ₗ[E] (Fin N → E)) : GL (Fin N) E :=
  ⟨LinearMap.toMatrix' (f : (Fin N → E) →ₗ[E] (Fin N → E)), LinearMap.toMatrix' ((f.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)),
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]⟩

theorem toLE_coGL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (f : (Fin N → E) ≃ₗ[E] (Fin N → E)) : toLE (coGL f) = f := by
  refine LinearEquiv.ext fun x => ?_
  rw [toLE_apply]
  show LinearMap.toMatrix' (f : (Fin N → E) →ₗ[E] (Fin N → E)) *ᵥ x = f x
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem inv_mul_mem_UJ {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ} (G : Matrix (Fin N) (Fin N) E)
    (crd co : GL (Fin N) E) (h1 : cT σ crd.1 * crd.1 = G) (h2 : star co.1 * co.1 = G) : crd⁻¹ * co ∈ UJ σ G := by
  show cT σ ((crd⁻¹ * co : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * G * ((crd⁻¹ * co : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = G
  rw [← Emat.star_eq_cT σ hσ] at h1 ⊢
  rw [Units.val_mul, star_mul, ← h1]
  have e : star ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * star (crd : Matrix (Fin N) (Fin N) E) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  have e' : (crd : Matrix (Fin N) (Fin N) E) * ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 := Units.mul_inv crd
  calc star (co : Matrix (Fin N) (Fin N) E) * star ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * (star (crd : Matrix (Fin N) (Fin N) E) * crd) *
        (((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * co)
      = star (co : Matrix (Fin N) (Fin N) E) * (star ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * star (crd : Matrix (Fin N) (Fin N) E)) *
        ((crd : Matrix (Fin N) (Fin N) E) * ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)) * co := by
          simp only [Matrix.mul_assoc]
    _ = star (co : Matrix (Fin N) (Fin N) E) * co := by rw [e, e', Matrix.mul_one, Matrix.mul_one]
    _ = star (crd : Matrix (Fin N) (Fin N) E) * crd := by rw [h2, h1]

end GlobalTheory.TwV.Xc.DetIdChi

open GlobalTheory.TwV.Xc.DetIdChi in

theorem GlobalTheory.TwV.Xc.chi_detId_kerN_eq : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), ∃ c0 : ℂ, ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → IsSDLat D.host.E _ ((J.fd std).kerN j La) → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = c0 * chiI J ((J.fd std).dt j La)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hSpl j hj
  have hσ : ∀ x : D.host.E, (sigD D : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  set G := gramN D j hj with hG
  set crd := J.A.crd j hj with hcrd
  have hco := (GlobalTheory.TwV.Xc.eMat_unitary_det D.host.E (sigD D : D.host.E →+* D.host.E) hσ (D.R.N j) (D.R.N j) rfl G crd
    (J.pins.crd_orth j hj)).1
  set co : GL (Fin (D.R.N j)) D.host.E := coGL (stdCo (sigD D : D.host.E →+* D.host.E) G) with hcoDef
  have hco2 : star co.1 * co.1 = G := Emat.gram_of_orth _ hσ G _ hco
  set γ₀ := crd⁻¹ * co with hγ₀
  have hγ : γ₀ ∈ UJ (sigD D : D.host.E →+* D.host.E) G := inv_mul_mem_UJ _ hσ G crd co (J.pins.crd_orth j hj) hco2
  have hr : GlobalTheory.TwU.ratA D.host.F γ₀ ∈ UPts (sigD D) G (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ₀, hγ, rfl⟩
  have hch := GlobalTheory.T.charOnNormOneIdeles_mul_unramified_classValue S hDict hSpl
  refine ⟨chiI J (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀)), ?_⟩

  have key : ∀ (β : (J.St j hj).Ch) (x : UA D j hj), IsSDLat D.host.E _ (latK D.sp G J.a x.1 ((J.St j hj).K β).lev.Lb) →
      t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (latK D.sp G J.a x.1 ((J.St j hj).K β).lev.Lb)) =
        chiI J (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀)) * chiI J (Matrix.GeneralLinearGroup.det x.1) := by
    intro β x hsd
    let y : UA D j hj := ⟨GlobalTheory.TwU.ratA D.host.F γ₀ * x.1, mul_mem hr x.2⟩
    have hlat : latK D.sp G J.a x.1 ((J.St j hj).K β).lev.Lb = GlobalTheory.TwU.latCo D.sp G crd J.a y.1 ((J.St j hj).K β).lev.Lb := by
      rw [← GlobalTheory.TwU.latCo_eq_latK G co (toLE_coGL _), show co = crd * γ₀ by rw [hγ₀, mul_inv_cancel_left]]
      exact GlobalTheory.TwU.latCo_mul G crd γ₀ hγ J.a x.1 _
    obtain ⟨hg, hcar, d, hdd, hdet⟩ := GlobalTheory.T.stepCoords_conj_unitary_and_carries_companion J.A J.dtU J.a J.pins J.tie j hj β y
    rw [J.base j hj β] at hcar
    have hstd : IsSDLat D.host.E (D.R.N j) (StandardLatticesGL3.stdL D (D.R.N j)) := by
      have := ((t.O u μ).L0 j).2
      rwa [Formalism.L2.Ker.initial_lattice_eq_standard] at this
    rw [hlat] at hsd ⊢
    have hrel := J.rel (D.R.N j) ⟨_, hstd⟩ ⟨_, hsd⟩ _ hg hcar d hdet
    have hid := t.idl_ok.2.2.2.2 (D.R.N j) ⟨_, hstd⟩ ⟨_, hsd⟩
    rw [hrel] at hid
    have hx1 := GlobalTheory.TwV.det_unitary_adelic_point_gram_step_norm_one D j hj x
    have hy1 := GlobalTheory.TwV.det_unitary_adelic_point_gram_step_norm_one D j hj y
    have hr1 : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) ∈ U1 (sigD D) := by
      have e : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) =
          Matrix.GeneralLinearGroup.det y.1 * (Matrix.GeneralLinearGroup.det x.1)⁻¹ := by
        show _ = Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀ * x.1) * _
        rw [MonoidHom.map_mul Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) x.1, mul_inv_cancel_right]
      rw [e]
      exact mul_mem hy1 (inv_mem hx1)
    rw [← hch.1 _ hr1 _ hx1, show Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) * Matrix.GeneralLinearGroup.det x.1 =
      Matrix.GeneralLinearGroup.det d.1 by rw [hdd]; exact (map_mul _ _ _).symm, hch.2.2.1 d]
    show t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D (D.R.N j)) (⟨_, hsd⟩ : SDLat D.host.E (D.R.N j)).1) = _
    rw [← hid, t.χ_rec, TaylorLogMetric.chiRec_idl D t.idl t.idl_ok.1]
    rfl
  intro La hLa hsd
  obtain ⟨⟨hr', -⟩, -, hheq, hdt⟩ := hDict j hj La hLa
  obtain ⟨h1, h2⟩ := heq_transport D hr' _ _ hheq
  rw [h2, hdt]
  exact key _ _ (h1 hsd)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeTupleMove_scalar_power_of_p : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; GlobalTheory.TwU.pPow (sysS H X std) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹)) = (kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ)⁻¹ * (GlobalTheory.TwU.pPow (sysS H X std) j (c, La) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹))) := by
  first | exact @GlobalTheory.TwV.Xc.moveBy_scal | exact GlobalTheory.TwV.Xc.moveBy_scal | (intros; apply GlobalTheory.TwV.Xc.moveBy_scal <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelScalar_of_sourceTarget_parts_product : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]), ∀ j < D.R.m, ∀ (cB : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (cK : ℂ_[D.what₂.places.resChar w]), (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * cB j La * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → TieChiH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι sc (d.sH S ι) cB j cK) := by
  first | exact @GlobalTheory.TwV.DelB.tieChiH_of_parts | exact GlobalTheory.TwV.DelB.tieChiH_of_parts | (intros; apply GlobalTheory.TwV.DelB.tieChiH_of_parts <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.comparedForm_normalisedValues_latticeTuple : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat (j + 1)).V, ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp (j + 1) x La.1 La.2) = MvPolynomial.map ι V ∧ RealAt d (j + 1) hj h La ((ex.tw.fm u μ).emb (j + 1) x) V) := by
  first | exact @GlobalTheory.TwV.DelA.cmp_valsAt | exact GlobalTheory.TwV.DelA.cmp_valsAt | (intros; apply GlobalTheory.TwV.DelA.cmp_valsAt <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orthonormalChartBasis_det_norm_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j) τ, ‖ι (embT D τ (uB J j hj a).1.det)‖ = 1) := by
  first | exact @GlobalTheory.TwV.DelA.uB_det_unit | exact GlobalTheory.TwV.DelA.uB_det_unit | (intros; apply GlobalTheory.TwV.DelA.uB_det_unit <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.changedFrame_rational_unitary : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j), StdU D (mM d j hj La) ∧ FrIs d.fd2 (J.rho std) j La h (mM d j hj La) ∧ (mM d j hj La).1.det * (d.gam j hj La).1.det = (uB J j hj La.1).1.det) := by
  first | exact @GlobalTheory.TwV.DelA.changed_frame_unitary | exact GlobalTheory.TwV.DelA.changed_frame_unitary | (intros; apply GlobalTheory.TwV.DelA.changed_frame_unitary <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeTupleReading_eq_of_realising_polynomial : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (V : XR ((sysS H X std).Pj (j + 1)) ℂ), (∀ d : Dec J std, RealAt d (j + 1) hj h La φ V) → rdJ I X.onCh ι j La.1 La.2 φ = MvPolynomial.map ι V) := by
  first | exact @GlobalTheory.TwV.DelA.rdJ_eq_of_realAt | exact GlobalTheory.TwV.DelA.rdJ_eq_of_realAt | (intros; apply GlobalTheory.TwV.DelA.rdJ_eq_of_realAt <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.targetStep_scalar_eq : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (La' : (sysS H X std).Lt (j + 1)), dPow (mM d (j + 1) hj La').1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d (j + 1) hj La' = d.uT S j La' * kT J j hj La'.1) := by
  first | exact @GlobalTheory.TwV.DelA.target_scalar | exact GlobalTheory.TwV.DelA.target_scalar | (intros; apply GlobalTheory.TwV.DelA.target_scalar <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

section Trace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem zc_eq_sum_Eop : zc E a = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := GlobalTheory.T.splitCentreDerivative_eq_sum_diagonalMatrixUnits E a

theorem sum_Eop_apply {π : CuspSub E a} {τ : E →+* ℂ} {m : Multiset ℂ} (h : π.HasInfChar τ m) {φ : Sm E a}
    (hφ : φ ∈ π.V) : (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := GlobalTheory.T.cuspidal_traceMatrixUnits_acts_by_sum_infinitesimalCharacter E a π τ m h φ hφ

theorem cex_eq (π : CuspSub E a) : cex (⟨a, π⟩ : Letter E) = ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum := by
  refine (letter_centralExponent E ⟨a, π⟩).2.2.2.2 _ ?_
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine ⟨φ, hφ, h0, ?_⟩
  change zc E a φ = _
  rw [zc_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun τ _ => sum_Eop_apply (ParLaws.hasInfChar_infChar (CG.mk π) τ) hφ

end Trace

end GlobalTheory.UnitLocWeight

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem sum_infChar_of_isWeight {π : CuspSub E a} {wt : ℤ} (h : IsWeight π wt) :
    ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum =
      (Module.finrank ℚ E : ℂ) * ((a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ))) / 2 := by
  set c : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hc : Function.Bijective fun τ : E →+* ℂ => τ.comp c := by
    refine Finite.injective_iff_bijective.1 fun τ τ' e => RingHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := (IsCMField.complexConj E).surjective x
    exact RingHom.congr_fun e y
  have h1 : ∑ τ : E →+* ℂ, ((CG.mk π).infChar (τ.comp c)).sum = ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum :=
    Function.Bijective.sum_comp hc (fun τ => ((CG.mk π).infChar τ).sum)
  have h2 : ∀ τ : E →+* ℂ, ((CG.mk π).infChar (τ.comp c)).sum =
      (a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ)) - ((CG.mk π).infChar τ).sum := fun τ => by
    rw [h τ, Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, CG.card_infChar, Multiset.map_id',
      nsmul_eq_mul]
  have h3 := Embeddings.card E ℂ
  simp only [h2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, h3, nsmul_eq_mul] at h1
  linear_combination -h1 / 2

end GlobalTheory.UnitLocWeight

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

theorem rexp_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} {wt : ℤ}
    (h : IsWeight π wt) : rexp (⟨a, π⟩ : Letter E) = ((a : ℝ) - 1 - wt) / 2 := by
  have e := (cex_eq π).trans (sum_infChar_of_isWeight h)
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have e2 : (cex (⟨a, π⟩ : Letter E)).re = (Module.finrank ℚ E : ℝ) * ((a : ℝ) * ((a : ℝ) - 1 - wt)) / 2 := by
    rw [e]
    have : (Module.finrank ℚ E : ℂ) * ((a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ))) / 2 =
        (((Module.finrank ℚ E : ℝ) * ((a : ℝ) * ((a : ℝ) - 1 - wt)) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  unfold rexp
  change (cex (⟨a, π⟩ : Letter E)).re / ((a : ℝ) * Module.finrank ℚ E) = _
  rw [e2]
  field_simp

end GlobalTheory.UnitLocWeight
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel

namespace GlobalTheory.LocMod.Place

theorem heisO_mem_iSup_range_of_fixed : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ (c : k), c ≠ 0 → ∀ g, Formalism.IndefR.Datum.IsThetaFunO ψ S T g → (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → Formalism.IndefR.Datum.heisO ψ S T (p.up FS FT (c • x)) g = g) → (∀ y : Formalism.IndefR.Datum.WO S T, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → ψ (Formalism.IndefR.Datum.symplO S T (p.up FS FT (c • x)) y) = 1) → Formalism.IndefR.Datum.heisO ψ S T y g = g) → ∀ r : Formalism.IndefR.Datum.WO S T, Formalism.IndefR.Datum.IsHalf p.e r → Formalism.IndefR.Datum.heisO ψ S T r g ∈ ⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) →ₗ[ℂ] (Formalism.IndefR.Datum.WO S T → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ c hc g hg hfix hhalf r hr
  classical
  obtain ⟨FT', hFT'⟩ := GlobalTheory.LocMod.Witness.exists_scaled FT (Equiv.refl Y) (fun _ => c) (fun _ => hc)
  have hβ : FT'.β = c • FT.β := by
    ext i j
    simp [hFT']
  have hup : ∀ x, p.up FS FT' x = p.up FS FT (c • x) := by
    intro x
    unfold GlobalTheory.LocMod.Place.up
    rw [hβ, Matrix.smul_mul, Matrix.mul_smul]
  obtain ⟨T₁, hT₁, hT₁Φ⟩ := (GlobalTheory.LocModU.localModel_uniq_transport_exist D k p Y Y' S T FS FT' ψ hψ).2.2 g hg
    (fun x hx => by rw [hup]; exact hfix x hx)
    (fun y hy h => hhalf y hy (fun x hx => by rw [← hup]; exact h x hx))
  let Φ : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) := ⟨_, GlobalTheory.LocMod.Place.intInd_mem_SB k Y Y'⟩
  have hΦ : T₁ Φ = g := hT₁Φ Φ rfl
  have hr' : p.up FS FT' (p.down FS FT' r) = r := GlobalTheory.LocMod.Witness.up_down p FS FT' hr
  let Φ₁ : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) := ⟨fun t => Φ.1 (t + p.down FS FT' r),
    Φ.2.1.comp_continuous (continuous_add_const _), Φ.2.2.comp_homeomorph (Homeomorph.addRight _)⟩
  have h1 : T₁ Φ₁ = heisO ψ S T r g := by
    rw [hT₁.trans (p.down FS FT' r) Φ Φ₁ (fun t => rfl), hr', hΦ]
  obtain ⟨Tm', hTm', hchg⟩ := GlobalTheory.LocMod.Place.exists_isModel_chg D k p Y Y' S T FS FT' Y Y' FS FT ψ T₁ hT₁
  let e : Matrix Y Y' k ≃ₜ Matrix Y Y' k := Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hc)
  let Φ' : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) := ⟨fun t => Φ₁.1 (c⁻¹ • t), Φ₁.2.1.comp_continuous e.continuous, Φ₁.2.2.comp_homeomorph e⟩
  have h2 : Tm' Φ' = T₁ Φ₁ := hchg Φ₁ Φ' (fun x => by
    show Φ₁.1 x = Φ₁.1 (c⁻¹ • (FT.γ * FT'.β * x * (FS.γ * FS.β)))
    rw [hβ, FS.γβ, Matrix.mul_one, Matrix.mul_smul, FT.γβ, Matrix.smul_mul, Matrix.one_mul,
      smul_smul, inv_mul_cancel₀ hc, one_smul])
  rw [← h1, ← h2]
  exact Submodule.mem_iSup_of_mem Tm' (Submodule.mem_iSup_of_mem hTm' (LinearMap.mem_range_self Tm' Φ'))

end GlobalTheory.LocMod.Place
end
