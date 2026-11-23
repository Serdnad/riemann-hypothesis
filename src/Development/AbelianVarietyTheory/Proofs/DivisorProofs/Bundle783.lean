module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle745
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle746
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle734
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarJacLeExp
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle747
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

section Res

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def resI (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) : Formalism.L2.Herm.intAf F E →+* 𝓞 E ⧸ I :=
  ((RingEquiv.ofBijective (cmpS F I) (cmpS_bij (F := F) I hI)).symm : _ →+* 𝓞 E ⧸ I).comp
    (Ideal.Quotient.mk (idS F I))

variable {F}

theorem resI_oToS (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (a : 𝓞 E) :
    resI F I hI (oToS F E a) = Ideal.Quotient.mk I a := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _
  rw [RingEquiv.symm_apply_eq]
  rfl

theorem resI_eq_zero_iff (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (s : Formalism.L2.Herm.intAf F E) :
    resI F I hI s = 0 ↔ s ∈ idS F I := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _ ↔ _
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

theorem resS_eq_resI (w : Pl E) : resS F w = resI F w.asIdeal w.ne_bot := rfl

end Res

section CRT

variable {E : Type} [Field E] [NumberField E] {I : Ideal (𝓞 E)} {Pg : Finset (Pl E)}

end CRT

end GlobalTheory.GeoActCompare
end
end

section

open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.FrameCong

theorem coord_mem_idS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : IsFrame β Λ)
    (I : Ideal (𝓞 E)) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hw : w ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) :
    ∀ i, ∃ s ∈ idS F I, (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) i =
      (s : E ⊗[F] Formalism.L2.Herm.Af F) := by
  refine Submodule.span_induction (p := fun w _ => ∀ i, ∃ s ∈ idS F I,
    (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) i =
      (s : E ⊗[F] Formalism.L2.Herm.Af F)) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨m, hm, rfl⟩
    refine Submodule.smul_induction_on (p := fun m => ∀ i, ∃ s ∈ idS F I,
      (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m k))) i = (s : E ⊗[F] Formalism.L2.Herm.Af F)) hm ?_ ?_
    · intro a ha u hu i
      have hu' : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        Submodule.subset_span ⟨u, hu, rfl⟩
      have t := (hβ _).1 hu' i
      refine ⟨oToS F E a * ⟨_, t⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha), ?_⟩
      have e : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a • u) k)) =
          (oToS F E a : E ⊗[F] Formalism.L2.Herm.Af F) • (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)) := by
        funext k
        show Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a • u) k) =
          (oToS F E a : E ⊗[F] Formalism.L2.Herm.Af F) * Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)
        rw [Pi.smul_apply, Algebra.smul_def, map_mul]
        rfl
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      rfl
    · intro m1 m2 h1 h2 i
      obtain ⟨s1, hs1, e1⟩ := h1 i
      obtain ⟨s2, hs2, e2⟩ := h2 i
      refine ⟨s1 + s2, add_mem hs1 hs2, ?_⟩
      have : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((m1 + m2) k)) =
          (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m1 k)) +
            (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m2 k)) := by
        funext k; simp [map_add (f := _)]
      rw [this, Matrix.mulVec_add, Pi.add_apply, e1, e2]
      rfl
  · intro i
    exact ⟨0, zero_mem _, by simp⟩
  · intro a b _ _ ha hb i
    obtain ⟨s1, hs1, e1⟩ := ha i
    obtain ⟨s2, hs2, e2⟩ := hb i
    refine ⟨s1 + s2, add_mem hs1 hs2, ?_⟩
    rw [Matrix.mulVec_add, Pi.add_apply, e1, e2]
    rfl
  · intro c a _ ha i
    obtain ⟨s, hs, e⟩ := ha i
    refine ⟨c * s, Ideal.mul_mem_left _ _ hs, ?_⟩
    rw [show c • a = (c : E ⊗[F] Formalism.L2.Herm.Af F) • a from rfl, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, e]
    rfl

theorem redFn_eq_one_of_congr : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), Formalism.L2.DIV.IsFrame β Λ →
    x ∈ Formalism.L2.DIV.St β → ∀ (I : Ideal (𝓞 E)), (∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ z - z ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) →
    ∀ (PP : Formalism.L2.DIV.Pl E), I ≤ PP.asIdeal → Formalism.L2.DIV.redFn β PP x = 1 := by
  intro F E _ _ _ _ _ n β x Λ hβ hx I hcong PP hPP
  classical
  obtain ⟨y, rfl⟩ := hx
  rw [redFn_frGL]
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (intGL F E n y).1 with hY
  have e1 : ((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = β.1 * Y * (β⁻¹).1 := rfl
  apply Units.ext
  ext i j
  have hv : β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
    refine (hβ _).2 fun k => ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hkj : k = j
    · subst hkj; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne hkj]; exact Subring.zero_mem _
  obtain ⟨s, hs, es⟩ := coord_mem_idS β Λ hβ I _ (hcong _ hv) i
  have hcomp : ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      (((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
        (β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) -
        β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) = (Y - 1) *ᵥ Pi.single j 1 := by
    have hm1 : (β⁻¹).1 * (β.1 * Y * (β⁻¹).1) * β.1 = Y := by
      simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [e1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm1, Units.inv_mul,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hcomp, Matrix.mulVec_single_one, Matrix.col_apply] at es
  have e5 : (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (Y - 1) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  have hs' : (y.1 - 1) i j = s := Subtype.ext (e5.trans es)
  have hmem : (y.1 - 1) i j ∈ idS F PP.asIdeal := hs' ▸ Ideal.map_mono hPP hs
  have e6 : resS F PP ((y.1 - 1) i j) = 0 := by
    unfold resS
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_zero]
  show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at e6
  rw [e6, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.FrameCong
end
end

section

noncomputable section

namespace GlobalTheory.HcIrr

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def natBlocks (b : Fin r → Fin s) : Fin r → ℕ := fun i => (b i : ℕ)

theorem blockTri_le_parab (b : Fin r → Fin s) : blockTri (κ := K) (natBlocks b) ≤ parab K b := by
  intro p hp
  refine ⟨fun i j hij => hp hij, fun i j hij => ?_⟩
  exact (inv_mem hp : p⁻¹ ∈ blockTri (κ := K) (natBlocks b)) hij

theorem parab_le_blockTri (b : Fin r → Fin s) : parab K b ≤ blockTri (κ := K) (natBlocks b) := by
  intro p hp i j hij
  exact hp.1 i j hij

theorem levi_one (b : Fin r → Fin s) (c : Fin s) : levi K b c 1 = 1 := by
  apply Units.ext
  exact Matrix.submatrix_one _ Subtype.val_injective

theorem levi_mul (b : Fin r → Fin s) (c : Fin s) (p q : parab K b) :
    levi K b c (p * q) = levi K b c p * levi K b c q := by
  apply Units.ext
  exact blk_mul b c p.2.1 q.2.1

variable (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

def leviTensor : Representation ℂ (blockTri (κ := K) (natBlocks b))
    (PiTensorProduct ℂ (fun c => (lam c : Type))) where
  toFun p := infl K b lam (Subgroup.inclusion (blockTri_le_parab b) p)
  map_one' := by
    have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) 1)) = LinearMap.id := by
      intro c
      rw [map_one, levi_one, map_one]
      rfl
    simp only [infl, this]
    exact PiTensorProduct.map_id
  map_mul' p q := by
    have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) (p * q))) =
        (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p)) ∘ₗ
          (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) q)) := by
      intro c
      rw [map_mul, levi_mul, map_mul]
      rfl
    simp only [infl, this]
    exact PiTensorProduct.map_comp _ _

theorem leviTensor_apply (p : blockTri (κ := K) (natBlocks b)) :
    leviTensor b lam p = PiTensorProduct.map (fun c =>
      (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p))) := rfl

instance finiteTensor : FiniteDimensional ℂ (PiTensorProduct ℂ (fun c => (lam c : Type))) :=
  Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.finBasis ℂ (lam c : Type))

end GlobalTheory.HcIrr
end
end

section

open Formalism.L2.DIV NumberField Module

noncomputable section

namespace GlobalTheory.multiplicity_linearCharacter_eq_characterSum

theorem nOf_eq_charSum : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G) [Fintype H] (ψ : H →* Kˣ), (Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨H, ψ⟩ : K) = (Nat.card H : K)⁻¹ * ∑ h : H, Formalism.IndefR.TransferLatticeStatement.charOf τ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  intro K _ _ G _ _ W _ _ _ τ H _ ψ
  classical
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  set T : Module.End K W := ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) with hT
  have hep : Formalism.IndefR.IndefiniteEpsilonOperator.epOp τ ⟨H, ψ⟩ = (Nat.card H : K)⁻¹ • T := by
    unfold Formalism.IndefR.IndefiniteEpsilonOperator.epOp
    congr 1
    rw [hT]
    simp only [map_inv]
    congr!
  have h1 : ∀ a : H, ((((ψ a)⁻¹ : Kˣ) : K) • τ (a : G)) * T = T := by
    intro a
    rw [hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun h => ?_
    simp [smul_smul, mul_comm]
  have h2 : T * T = (Nat.card H : K) • T := by
    conv_lhs => rw [hT, Finset.sum_mul, ← hT]
    rw [Finset.sum_congr rfl fun a _ => h1 a]
    simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  have hid : IsIdempotentElem (Formalism.IndefR.IndefiniteEpsilonOperator.epOp τ ⟨H, ψ⟩) := by
    rw [IsIdempotentElem, hep, smul_mul_smul_comm, h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.IndefiniteEpsilonOperator.epSp

  rw [← htr, hep, map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory.multiplicity_linearCharacter_eq_characterSum
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VertSpanZero

theorem le_preimage_of_closedPoint {Z : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Z)
    (V : Z.Opens) (h : y.base (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ y ⁻¹ᵁ V := by
  intro p _
  exact ((IsLocalRing.specializes_closedPoint p).map y.continuous).mem_open V.isOpen h

theorem snd_valR_epsMul {Z : Scheme.{0}} {S : Type} [CommRing S] (T : Sp (DualNumber S) ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ T ⁻¹ᵁ O) (a : S) (f : Γ(Z, O)) :
    (valR (spMap (epsMul a) ≫ T) O f).snd = a * (valR T O f).snd := by
  rw [GlobalTheory.Points.valR_spMap_comp (epsMul a) T O h f]
  simp [epsMul]

theorem epsMul_comp_algebraMap {S : Type} [CommRing S] (a : S) :
    (epsMul a).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
  ext x <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_epsMul {S : Type} [CommRing S] (a : S) :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (epsMul a) = (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext x <;> simp [epsMul]

theorem epsMul_zero' {S : Type} [CommRing S] :
    epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext x <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.VertSpanZero

namespace GlobalTheory.VertSpanZero

theorem spMap_fst_algebraMap (S : Type) [CommRing S] :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

def redOver {X : Scheme.{0}} {S : Type} [CommRing S] (x : Sp S ⟶ X) : Over.mk x ⟶ tEpsG x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
    change _ ≫ spMap (algebraMap S (DualNumber S)) ≫ x = x
    rw [← Category.assoc, spMap_fst_algebraMap, Category.id_comp])

theorem redOver_comp_prod {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [CommRing S] (x : Sp S ⟶ X)
    (l : List (tEpsG x ⟶ G)) (hl : ∀ u ∈ l, redOver x ≫ u = 1) : redOver x ≫ l.prod = 1 := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons u l ih =>
    rw [List.prod_cons, MonObj.comp_mul, hl u List.mem_cons_self,
      ih fun u' h => hl u' (List.mem_cons_of_mem _ h), _root_.mul_one]

theorem red_mul_prod {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [CommRing S] (g : Sp S ⟶ G.left)
    (g' : tEpsG (g ≫ G.hom) ⟶ G) (hg' : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g) {n : ℕ}
    (u : Fin n → (tEpsG (g ≫ G.hom) ⟶ G))
    (hu : ∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left = (1 : Over.mk (g ≫ G.hom) ⟶ G).left) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (g' * (List.ofFn u).prod).left = g := by
  have h1 : redOver (g ≫ G.hom) ≫ (List.ofFn u).prod = 1 := by
    refine redOver_comp_prod _ _ fun w hw => ?_
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' u w).1 hw
    exact Over.OverMorphism.ext (hu a)
  change (redOver (g ≫ G.hom) ≫ (g' * (List.ofFn u).prod)).left = g
  rw [MonObj.comp_mul, h1, _root_.mul_one]
  change spMap _ ≫ g'.left = g
  rw [hg', ← Category.assoc, spMap_fst_algebraMap, Category.id_comp]

end GlobalTheory.VertSpanZero
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.imagQuadIntegerLattice_mulStable_I_sqrt : ∀ (d : ℕ) (Λ : PeriodPair), 0 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → MulStable Λ (Complex.I * (Real.sqrt d : ℝ)) ∧ (Complex.I * (Real.sqrt d : ℝ)).im ≠ 0 := by
  first | exact @GlobalTheory.IntLatMul.main | exact GlobalTheory.IntLatMul.main | (intros; apply GlobalTheory.IntLatMul.main <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.isUniformiserAt_iff_adicCompletion_isUnifAt : ∀ {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ), IsUniformiserAt K v (x : v.adicCompletion K) ↔ Formalism.L2.Host.IsUnifAt v x := by
  first | exact @GlobalTheory.UnifVal.isUniformiserAt_iff_isUnifAt | exact GlobalTheory.UnifVal.isUniformiserAt_iff_isUnifAt | (intros; apply GlobalTheory.UnifVal.isUniformiserAt_iff_isUnifAt <;> assumption)
end

section


theorem _root_.GlobalTheory.T.unitarySatake_weylInvariant : Formalism.UG.SatWeyl := by
  first | exact @GlobalTheory.SatakeWeyl.satWeyl | exact GlobalTheory.SatakeWeyl.satWeyl | (intros; apply GlobalTheory.SatakeWeyl.satWeyl <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.polarJac_le_exp_hsNorm : ∀ (p q : ℕ) (h : ℕ → ℝ), (∏ i ∈ Finset.range (min p q), shc (2 * h i) * shc (h i) ^ (2 * (max p q - min p q))) * (∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1) ≤ Real.exp (((p + q : ℕ) : ℝ) * Real.sqrt (2 * (min p q : ℕ)) * hsNorm (aOf p q h)) := by
  first | exact @GlobalTheory.PolarJacBound.polarJac_le_exp | exact GlobalTheory.PolarJacBound.polarJac_le_exp | (intros; apply GlobalTheory.PolarJacBound.polarJac_le_exp <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.semilinear_short_exact_compatible : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (W' M' H' : Type) [AddCommGroup W'] [Module R' W'] [AddCommGroup M'] [Module R' M'] [AddCommGroup H'] [Module R' H'] (i : W →ₗ[R] M) (p : M →ₗ[R] H) (i' : W' →ₗ[R'] M') (p' : M' →ₗ[R'] H') (a : W →ₛₗ[algebraMap R R'] W') (b : M →ₛₗ[algebraMap R R'] M') (c : H →ₛₗ[algebraMap R R'] H'), Function.Surjective p → Function.Exact i p → Function.Injective i' → Function.Exact i' p' → (∀ x, b (i x) = i' (a x)) → (∀ x, p' (b x) = c (p x)) → (∃ e : R' ⊗[R] W ≃ₗ[R'] W', ∀ x, e (1 ⊗ₜ x) = a x) → (∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ x, e (1 ⊗ₜ x) = c x) → ∃ e : R' ⊗[R] M ≃ₗ[R'] M', ∀ x, e (1 ⊗ₜ x) = b x := by
  first | exact @GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact | exact GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact | (intros; apply GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.partialFreeResolutions_homotopyEquivalent : ∀ (O : Type) [CommRing O] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → ∃ (a₀ : F₀ →ₗ[O] G₀) (a₁ : F₁ →ₗ[O] G₁) (a₂ : F₂ →ₗ[O] G₂) (b₀ : G₀ →ₗ[O] F₀) (b₁ : G₁ →ₗ[O] F₁) (b₂ : G₂ →ₗ[O] F₂) (h₀ : F₀ →ₗ[O] F₁) (h₁ : F₁ →ₗ[O] F₂) (h₂ : F₂ →ₗ[O] F₃) (k₀ : G₀ →ₗ[O] G₁) (k₁ : G₁ →ₗ[O] G₂), e₁ ∘ₗ a₁ = a₀ ∘ₗ d₁ ∧ e₂ ∘ₗ a₂ = a₁ ∘ₗ d₂ ∧ d₁ ∘ₗ b₁ = b₀ ∘ₗ e₁ ∧ d₂ ∘ₗ b₂ = b₁ ∘ₗ e₂ ∧ LinearMap.id - b₁ ∘ₗ a₁ = d₂ ∘ₗ h₁ + h₀ ∘ₗ d₁ ∧ LinearMap.id - b₂ ∘ₗ a₂ = d₃ ∘ₗ h₂ + h₁ ∘ₗ d₂ ∧ LinearMap.id - a₁ ∘ₗ b₁ = e₂ ∘ₗ k₁ + k₀ ∘ₗ e₁ := by
  first | exact @GlobalTheory.resolutions_homotopy_equivalent | exact GlobalTheory.resolutions_homotopy_equivalent | (intros; apply GlobalTheory.resolutions_homotopy_equivalent <;> assumption)
end
