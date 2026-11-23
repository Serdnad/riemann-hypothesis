module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTraitDescentFiniteExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle540
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.LabConst

theorem mk_eq_of_forall_char {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ) (β₁ β₂ : X)
    (h : ∀ lam : X →+ ZMod k, lam β₁ = lam β₂) :
    (QuotientAddGroup.mk β₁ : X ⧸ (nsmulAddMonoidHom k : X →+ X).range) = QuotientAddGroup.mk β₂ := by
  let b := Module.Free.chooseBasis ℤ X
  rw [QuotientAddGroup.eq]
  have hc : ∀ i, (k : ℤ) ∣ b.repr (-β₁ + β₂) i := by
    intro i
    have h1 := h ((Int.castAddHom (ZMod k)).comp (b.coord i).toAddMonoidHom)
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply, Int.coe_castAddHom] at h1
    simp only [map_add (f := _), map_neg, Finsupp.add_apply, Finsupp.neg_apply, Int.cast_add, Int.cast_neg, h1, neg_add_cancel]
  choose c hc using hc
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [nsmulAddMonoidHom_apply]
  conv_rhs => rw [← b.sum_repr (-β₁ + β₂)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i, mul_smul, natCast_zsmul]

def qmap {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) :
    X ⧸ (nsmulAddMonoidHom k : X →+ X).range →+ Y ⧸ (nsmulAddMonoidHom k : Y →+ Y).range :=
  QuotientAddGroup.map _ _ e.toAddMonoidHom (by
    rintro _ ⟨z, rfl⟩
    exact ⟨e z, by simp⟩)

theorem qmap_mk {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) (β : X) :
    qmap k e (QuotientAddGroup.mk β) = QuotientAddGroup.mk (e β) := rfl

theorem mk_symm_eq_iff {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) (β : Y) (α : X) :
    (QuotientAddGroup.mk (e.symm β) : X ⧸ (nsmulAddMonoidHom k : X →+ X).range) = QuotientAddGroup.mk α ↔
      (QuotientAddGroup.mk β : Y ⧸ (nsmulAddMonoidHom k : Y →+ Y).range) = QuotientAddGroup.mk (e α) := by
  rw [QuotientAddGroup.eq, QuotientAddGroup.eq]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨e z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← map_nsmul, hz, map_add (f := _), map_neg, AddEquiv.apply_symm_apply]
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← map_nsmul, hz, map_add (f := _), map_neg, AddEquiv.symm_apply_apply]

end GlobalTheory.Poinc.LabConst

namespace GlobalTheory.Poinc.LabConst

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∃ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (l : u.Lab) a α, yy a = QuotientAddGroup.mk α ↔ l.yy a = QuotientAddGroup.mk (ε α) := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi
  obtain ⟨sg, hread⟩ := GlobalTheory.T.torsionLabel_eq_weilPairing_toricTorsionPoint o' Ω S ρ
  have hglob := GlobalTheory.T.exists_toricTorsion_label_closed_point o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
  choose bOf hbOf using hglob
  have hk0 : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have hζk : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (by positivity) (by ring)
  have key : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y →
      spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ →
      ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε →
      ∀ (l : u.Lab) (a : S.Gam) (β : u.D.toPre.X), l.yy a = QuotientAddGroup.mk β →
      ∀ lam : D.toPre.X →+ ZMod (S.r * S.N), lam (ε.symm β) = ((sg : ℤ) • eStd S.g _ (bOf lam) a) := by
    intro p _ y ev hCen hev y₀ hAt u ε hbc l a β hβ lam
    haveI : IsDomain o' := (ArithBase.ded (o := o') (Ω := Ω)).toIsDomain
    set f : o' →+* PadicAlgCl p := y₀.comp (algebraMap o' S.R) with hf
    have hω : IsPrimitiveRoot (f (S.ζ ^ (S.r * S.N))) (S.r * S.N) := by
      have h1 := hζk.isRoot_cyclotomic hk0
      have h2 := h1.map (f := f)
      rw [Polynomial.map_cyclotomic] at h2
      exact (Polynomial.isRoot_cyclotomic_iff_charZero hk0).1 h2
    set ω : (PadicAlgCl p)ˣ := (hω.isUnit hk0.ne').unit with hωdef
    have hωk : ω ^ (S.r * S.N) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hωdef, IsUnit.unit_spec, hω.pow_eq_one, Units.val_one])
    let ψ : ZMod (S.r * S.N) →+ Additive (PadicAlgCl p)ˣ :=
      ZMod.lift (S.r * S.N) ⟨zmultiplesHom (Additive (PadicAlgCl p)ˣ) (Additive.ofMul ω), by
        rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hωk, ofMul_one]⟩
    have hψ : ∀ z : ZMod (S.r * S.N), ((Additive.toMul (ψ z) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = f (S.ζ ^ (S.r * S.N)) ^ z.val := by
      intro z
      haveI : NeZero (S.r * S.N) := NeZero.of_pos hk0
      conv_lhs => rw [← ZMod.intCast_zmod_cast z]
      rw [ZMod.lift_coe]
      simp only [Subtype.coe_mk, zmultiplesHom_apply, toMul_zsmul, toMul_ofMul, ZMod.cast_eq_val, zpow_natCast]
      rw [Units.val_pow_eq_pow_val, hωdef, IsUnit.unit_spec]
    let τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ :=
      AddMonoidHom.toMultiplicativeLeft (ψ.comp (lam.comp ε.symm.toAddMonoidHom))
    have hτ : ∀ χ' : u.D.toPre.X, ((τ' (Multiplicative.ofAdd χ') : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
        f (S.ζ ^ (S.r * S.N)) ^ (lam (ε.symm χ')).val := fun χ' => hψ _
    have hτk : τ' ^ (S.r * S.N) = 1 := by
      refine MonoidHom.ext fun χ' => Units.ext ?_
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply, Units.val_one]
      obtain ⟨χ, rfl⟩ : ∃ χ, Multiplicative.ofAdd χ = χ' := ⟨Multiplicative.toAdd χ', rfl⟩
      rw [hτ, ← pow_mul, Nat.mul_comm _ (S.r * S.N), pow_mul, hω.pow_eq_one, one_pow]
    have hglobτ : ∀ χ, ((τ' (Multiplicative.ofAdd (ε χ)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
        y₀ (algebraMap o' S.R S.ζ) ^ (S.r * S.N * (lam χ).val) := by
      intro χ
      rw [hτ, AddEquiv.symm_apply_apply]
      simp only [hf, RingHom.comp_apply, map_pow, pow_mul]
    have hpt := hbOf lam p y ev hCen hev y₀ hAt u ε hbc τ' hglobτ
    have hv := hread p y₀ u l τ' (bOf lam) hτk hpt a β hβ
    have hv' : f (S.ζ ^ (S.r * S.N)) ^ (lam (ε.symm β)).val =
        f (S.ζ ^ (S.r * S.N)) ^ (((sg : ℤ) • eStd S.g _ (bOf lam) a).val) := by
      rw [← hτ, hv]
      simp only [hf, RingHom.comp_apply, map_pow, pow_mul]
    exact ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hv')
  have hconst : ∀ (p₁ : ℕ) [Fact p₁.Prime] (y₁ : Sp (OO p₁) ⟶ M.Z) (ev₁ : R →+* OO p₁), M.Cen U₀ x y₁ →
      spMap ev₁ ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y₁ → ∀ y₀₁ : S.R →+* PadicAlgCl p₁, S.At M y₁ y₀₁ →
      ∀ (u₁ : ρ.UTest p₁ y₀₁) (ε₁ : D.toPre.X ≃+ u₁.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev₁ u₁ ε₁ →
      ∀ (l₁ : u₁.Lab) (p₂ : ℕ) [Fact p₂.Prime] (y₂ : Sp (OO p₂) ⟶ M.Z) (ev₂ : R →+* OO p₂), M.Cen U₀ x y₂ →
      spMap ev₂ ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y₂ → ∀ y₀₂ : S.R →+* PadicAlgCl p₂, S.At M y₂ y₀₂ →
      ∀ (u₂ : ρ.UTest p₂ y₀₂) (ε₂ : D.toPre.X ≃+ u₂.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev₂ u₂ ε₂ →
      ∀ (l₂ : u₂.Lab) (a : S.Gam), qmap (S.r * S.N) ε₁.symm (l₁.yy a) = qmap (S.r * S.N) ε₂.symm (l₂.yy a) := by
    intro p₁ _ y₁ ev₁ hCen₁ hev₁ y₀₁ hAt₁ u₁ ε₁ hbc₁ l₁ p₂ _ y₂ ev₂ hCen₂ hev₂ y₀₂ hAt₂ u₂ ε₂ hbc₂ l₂ a
    obtain ⟨β₁, hβ₁⟩ := QuotientAddGroup.mk_surjective (l₁.yy a)
    obtain ⟨β₂, hβ₂⟩ := QuotientAddGroup.mk_surjective (l₂.yy a)
    rw [← hβ₁, ← hβ₂, qmap_mk, qmap_mk]
    refine mk_eq_of_forall_char _ _ _ fun lam => ?_
    rw [key p₁ y₁ ev₁ hCen₁ hev₁ y₀₁ hAt₁ u₁ ε₁ hbc₁ l₁ a β₁ hβ₁.symm lam,
      key p₂ y₂ ev₂ hCen₂ hev₂ y₀₂ hAt₂ u₂ ε₂ hbc₂ l₂ a β₂ hβ₂.symm lam]
  by_cases hex : ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p) (_ : M.Cen U₀ x y)
      (_ : spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y) (y₀ : S.R →+* PadicAlgCl p) (_ : S.At M y y₀)
      (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X) (_ : GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε), Nonempty u.Lab
  · obtain ⟨p₁, hp₁, y₁, ev₁, hCen₁, hev₁, y₀₁, hAt₁, u₁, ε₁, hbc₁, ⟨l₁⟩⟩ := hex
    refine ⟨(qmap (S.r * S.N) ε₁.symm).comp l₁.yy, ?_⟩
    intro p _ y ev hCen hev y₀ hAt u ε hbc l a α
    rw [AddMonoidHom.comp_apply, hconst p₁ y₁ ev₁ hCen₁ hev₁ y₀₁ hAt₁ u₁ ε₁ hbc₁ l₁ p y ev hCen hev y₀ hAt u ε hbc l a]
    obtain ⟨β, hβ⟩ := QuotientAddGroup.mk_surjective (l.yy a)
    rw [← hβ, qmap_mk]
    exact mk_symm_eq_iff _ ε β α
  · refine ⟨0, ?_⟩
    intro p _ y ev hCen hev y₀ hAt u ε hbc l
    exact absurd ⟨p, inferInstance, y, ev, hCen, hev, y₀, hAt, u, ε, hbc, ⟨l⟩⟩ hex

end GlobalTheory.Poinc.LabConst

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_uniformisedTrait_descent_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∀ (A₀ : PolAV (Sp (Kb R))) (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) → (letI := A₀.isAb.comm; GlobalTheory.ZH.HypS A₀.A A₀.L) → GeomIso A₀ A' e₀ (algebraMap (FractionRing W) (Kb W)) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ UniTrait D₁.toPre A := by
  first | exact @GlobalTheory.Mum.ClosureDescent.exists_uniTrait | exact GlobalTheory.Mum.ClosureDescent.exists_uniTrait | (intros; apply GlobalTheory.Mum.ClosureDescent.exists_uniTrait <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UniEnlarge

open GlobalTheory.Mum.ClosureDescent GlobalTheory.ThetaDescent

theorem uniTrait_of_finExt : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂), FinExt i₁₂ → IsLocalHom i₁₂ → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → UniTrait D₂.toPre A₂ := by
  intro R₁ _ _ _ _ D₁ A hU R₂ _ _ _ i₁₂ hi₁₂ hl₁₂ D₂ ⟨hD₂⟩ A₂ a₂ hA₂
  classical
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD', a, hW, hφ, hφl, hG', ga, hga, g₁, l₁⟩ := hU
  obtain ⟨ga₂, hga₂, g₂, l₂⟩ := hA₂
  have hfin : i₁₂.Finite := hi₁₂.2.2
  let β : FractionRing W →+* AlgebraicClosure (FractionRing W) := algebraMap _ _
  have hβ : β.IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := FractionRing W) x
  obtain ⟨j₁, hj₁⟩ := exists_extend hfin (algebraMap R₁ (FractionRing R₁)) ga₂ (RingHom.ext fun r => hga₂ r)
    (β.comp ga)
  have hjρ : ∀ r, j₁ (algebraMap R₂ _ (i₁₂ r)) = β (((algebraMap W (FractionRing W)).comp φ) r) := fun r => by
    rw [← hga₂, ← RingHom.comp_apply j₁ ga₂, hj₁, RingHom.comp_apply, hga, RingHom.comp_apply]
  obtain ⟨s₀, hs₀⟩ := exists_range_le_gen hfin β ((algebraMap W _).comp φ) j₁ hjρ
  let i := β.codRestrict _ (mem_gen β s₀)
  let k := j₁.codRestrict _ hs₀
  have hi : i.Finite := finite_gen β hβ s₀
  have := hW.1
  have hWb : Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩, hW.2.2⟩
  obtain ⟨W₁, _, _, _, io, σ, hio, hiol, hσ⟩ := GlobalTheory.CommonCover.exists_cover_field W hWb _ i hi
  obtain ⟨D₃, hD₃, A₃, U₃, a₃, hA₃⟩ := exists_unif_fib hWb.1 hio.1 io hio.2.1 (map_maximalIdeal_le io) hG' U'
    (σ.comp i) ((RingHom.comp_assoc _ _ _).trans hσ)
  have f₁ : Fib A₃ A ((σ.comp i).comp ga) (a₃ ≫ a) := hA₃.comp ⟨g₁, l₁⟩ rfl
  have e : (σ.comp k).comp ga₂ = (σ.comp i).comp ga := RingHom.ext fun x =>
    congrArg σ (Subtype.ext (DFunLike.congr_fun hj₁ x))
  obtain ⟨d, -, hd⟩ := Fib.cancel (σ.comp k) (⟨g₂, l₂⟩ : Fib A₂ A ga₂ a₂) f₁ e
  haveI := hio.1.2.2.1
  obtain ⟨φ₂, hφ₂, hcomp, hinj, hl⟩ := exists_restrict hfin (io.comp φ) (σ.comp k) fun r => by
    have e₁ : k (algebraMap R₂ _ (i₁₂ r)) = i (algebraMap W _ (φ r)) := Subtype.ext (hjρ r)
    exact (congrArg σ e₁).trans (DFunLike.congr_fun hσ (φ r))
  obtain ⟨q⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hφ hio.2.1 hD' hD₃
  rw [← hcomp] at q
  obtain ⟨q₁⟩ := GlobalTheory.PullDegUniq.nonempty_isPullDeg_cancel hi₁₂.2.1 hinj hD₂ q
  exact ⟨W₁, _, _, _, φ₂, _, inferInstance, inferInstance, D₃, A₃, U₃, q₁, d, _root_.GlobalTheory.Mum.ClosureDescent.cDvr_of_finExt hW hio, hinj, hl,
    IsSemiAbelian.pullback _ G' hG', σ.comp k, hφ₂, hd.1, hd.2⟩

end GlobalTheory.Mum.UniEnlarge
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem lamPts_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (hB : IsGrpPullback B' B f φ) {T' : Over S'} {T : Over S} (h : Over.mk (T'.hom ≫ f) ⟶ T)
    (x' y' : T' ⟶ B') (x y : T ⟶ B) (hx : x'.left ≫ φ = h.left ≫ x.left) (hy : y'.left ≫ φ = h.left ≫ y.left)
    (k : Fin 4) : lamPts x' y' k ≫ φ = h.left ≫ lamPts x y k := by
  fin_cases k
  · have e := hB.2 T' x' y' (h ≫ x) (h ≫ y) (by rw [Over.comp_left, hx]) (by rw [Over.comp_left, hy])
    show (x' * y').left ≫ φ = h.left ≫ (x * y).left
    rw [← e, ← MonObj.comp_mul, Over.comp_left]
  · exact hx
  · exact hy
  · show (1 : T' ⟶ B').left ≫ φ = h.left ≫ (1 : T ⟶ B).left
    have e := hB.2 T' 1 1 (pushPt hB.1.w 1) (pushPt hB.1.w 1) rfl rfl
    rw [_root_.mul_one] at e
    have e1 : pushPt hB.1.w (1 : T' ⟶ B') = 1 := by
      have : pushPt hB.1.w (1 : T' ⟶ B') * pushPt hB.1.w 1 = pushPt hB.1.w 1 := Over.OverMorphism.ext e
      exact mul_eq_left.1 this
    have e2 : (pushPt hB.1.w (1 : T' ⟶ B')).left = (1 : T' ⟶ B').left ≫ φ := rfl
    rw [← e2, e1, ← Over.comp_left, MonObj.comp_one]

theorem fibre_exists : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (gQ : ℕ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]
  (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (K : Type) [Field K] (ev : V₁ →+* K),
  ∃ (P' : PolAV (Sp K)) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ P'.A.left) (B : Over (Sp K)) (_ : GrpObj B)
    (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
    P'.g = 8 * gQ ∧ IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) P'.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (P'.L.pull ψ) ∧
    E8Fibration.IsPPFib B gQ M ∧ E8Fibration.IsProd pr ∧ E8Fibration.IsE8WeightedBundle W pr P'.L M.L ∧
    ∀ (n : ℕ) (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ n = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ y' : Out.baseOver (Sp K) ⟶ P'.A, y'.left = q ≫ ψ ∧ y' ^ n = 1 := by
  intro W gQ V V₁ _ _ _ _ Q hQ ρ hρ D e hS K _ ev
  have hS' := hS
  obtain ⟨pr₀, w, hmon, huniv, hw, -, -⟩ := hS'
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap ev) D.P
  have hgp : IsGrpPullback P'.A D.P.A (spMap ev) φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
    rfl⟩
  obtain ⟨i, hi, hiφ⟩ := grpPullback_iso (isGrpPullback_pullback D.P.A (spMap ev)) hgp
  haveI := hi
  have hinv : i.inv.left ≫ pullback.fst D.P.A.hom (spMap ev) = φ := by
    rw [← hiφ, ← Category.assoc, ← Over.comp_left, i.inv_hom_id, Over.id_left, Category.id_comp]

  have hQP : IsPPFib Q.B Q.g Q.M := ⟨Q.isAb, Q.smoothDim, ⟨Q.cub⟩, Q.ample, Q.ktriv⟩
  obtain ⟨M₁, hM₁, hP₁⟩ := GlobalTheory.T.principallyPolarisedFibre_baseChange (spMap ρ) Q.B Q.g Q.M hQP
  obtain ⟨M, hM, hP⟩ := GlobalTheory.T.principallyPolarisedFibre_baseChange (spMap ev) _ Q.g M₁ hP₁
  let B₁ := (Over.pullback (spMap ρ)).obj Q.B
  let pr : Fin 8 → (P'.A ⟶ (Over.pullback (spMap ev)).obj B₁) :=
    fun a => i.inv ≫ (Over.pullback (spMap ev)).map (pr₀ a)
  have hpr : IsProd pr := GlobalTheory.T.eighthPowerProjections_baseChange_iso (spMap ev) pr₀ ⟨hmon, huniv⟩ P'.A i hi
  refine ⟨P', i.hom.left, (Over.pullback (spMap ev)).obj B₁, inferInstance, M, pr, ?_, isGrpPullback_of_iso i, ?_,
    hQ ▸ hP, hpr, ?_, ?_⟩
  · rw [hg, GlobalTheory.T.sharpEighthPower_relative_dimension_eq_eight_mul W V V₁ Q ρ D e hS, hQ]
  · have ht' : LBIso (D.P.L.pull φ) P'.L := ⟨t, ht⟩
    exact LBIso.trans (LB.isLB_pull D.P.isLB _) (LB.isLB_pull (LB.isLB_pull D.P.isLB _) _) (LB.isLB_pull P'.isLB _)
      (GlobalTheory.GenSpread.lbIso_pull_pull D.P.isLB i.hom.left hiφ.symm) (GlobalTheory.GenSpread.lbIso_pullback ht' i.hom.left)
  · have ht' : LBIso (D.P.L.pull φ) P'.L := ⟨t, ht⟩
    have H : LBIso M.L (Q.M.L.pull (pullback.fst B₁.hom (spMap ev) ≫ pullback.fst Q.B.hom (spMap ρ))) := by
      rw [hM, hM₁]
      exact LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull Q.M.isLB _ rfl)
    have hx : ∀ a, (pr a).left ≫ pullback.fst B₁.hom (spMap ev) = φ ≫ (pr₀ a).left := fun a => by
      show (i.inv ≫ (Over.pullback (spMap ev)).map (pr₀ a)).left ≫ _ = _
      rw [Over.comp_left, Category.assoc]
      have hp : ((Over.pullback (spMap ev)).map (pr₀ a)).left ≫ pullback.fst B₁.hom (spMap ev) =
          pullback.fst D.P.A.hom (spMap ev) ≫ (pr₀ a).left := pullback.lift_fst _ _ _
      rw [hp, ← Category.assoc, hinv]
    have ha := GlobalTheory.ShapePull.iso_linComb_pull H (fun k : (Fin 8 × Fin 8) × Fin 4 => lamPts (pr k.1.1) (pr k.1.2) k.2)
      (fun k => lamPts (pr₀ k.1.1) (pr₀ k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)) φ
      (fun k => by
        rw [← Category.assoc, lamPts_pull (isGrpPullback_pullback B₁ (spMap ev)) (Over.homMk φ hφ.w) (pr k.1.1) (pr k.1.2)
          (pr₀ k.1.1) (pr₀ k.1.2) (hx _) (hx _) k.2, Category.assoc]
        rfl)
    have hb := GlobalTheory.GenSpread.lbIso_pullback (⟨w, hw⟩ : LBIso D.P.L _) φ
    exact LBIso.trans P'.isLB (LB.isLB_pull D.P.isLB _) (LB.isLB_linComb M.isLB _ _) (LBIso.symm ht')
      (LBIso.trans (LB.isLB_pull D.P.isLB _) (LB.isLB_pull (LB.isLB_linComb Q.M.isLB _ _) _) (LB.isLB_linComb M.isLB _ _)
        hb (LBIso.symm ha))
  · intro n y hy q hq1 hq2
    have hw' : (q ≫ i.hom.left) ≫ P'.A.hom = (baseOver (Sp K)).hom := by
      rw [Category.assoc, Over.w i.hom]
      exact hq2
    refine ⟨Over.homMk (q ≫ i.hom.left) hw', rfl, ?_⟩
    rw [← GlobalTheory.Raynaud.pow_eq_one_iff_of_isGrpPullback hgp]
    let c : Over.mk (spMap ev) ⟶ Over.mk ((baseOver (Sp K)).hom ≫ spMap ev) := Over.homMk (𝟙 _) (by simp)
    let c' : Over.mk ((baseOver (Sp K)).hom ≫ spMap ev) ⟶ Over.mk (spMap ev) := Over.homMk (𝟙 _) (by simp)
    have hcc : c' ≫ c = 𝟙 _ := by ext; simp [c, c']
    have hy' : c ≫ pushPt hgp.1.w (Over.homMk (q ≫ i.hom.left) hw' : baseOver (Sp K) ⟶ P'.A) = y := by
      ext
      show 𝟙 _ ≫ (q ≫ i.hom.left) ≫ φ = y.left
      rw [Category.id_comp, Category.assoc, hiφ, hq1]
    have h1 : c ≫ pushPt hgp.1.w (Over.homMk (q ≫ i.hom.left) hw' : baseOver (Sp K) ⟶ P'.A) ^ n = 1 := by
      rw [MonObj.comp_pow, hy', hy]
    have h2 := congrArg (c' ≫ ·) h1
    simp only [← Category.assoc, hcc, Category.id_comp, MonObj.comp_one] at h2
    exact h2

end GlobalTheory.Poinc.Sep.E8Fibration
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntEval

theorem eval_at_integral : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))) (g' : GtPtF D.toPre (FractionRing V)) (l : FractionRing V), l ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g → IntTerm.Ext U.toUnifPre x h → GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → IntTerm.FrRel U.toUnifPre w₀ x e h l → ∃ w : Frm D.toPre (FractionRing V) 1 g'.b, w.IsGen ∧ IntTerm.IntFrm D.toPre g.b w l ∧ IntTerm.Lies U.toUnifPre w₀ g' w x e := by
  intro V _ _ _ hV D A G _ _ hG U w₀ hw₀ x e h g g' l hl hF hExt hP hR
  obtain ⟨f, hf, hfv⟩ := hR
  obtain ⟨t, ht, htl⟩ := GlobalTheory.T.exists_integral_generator_rigidification_all_levels V hV D A G U.toUnifPre h g hF f hf
  have hφ : DegPre.lineφ D.toPre (FractionRing V) g'.b = fun i =>
      (toUnit (TF (R := V) (FractionRing V))).left ≫ (![(η[D.toPre.P.A]).left, g.b.left] : Fin 2 → _) i := by
    funext i
    fin_cases i
    · exact Over.comp_left (f := toUnit (TF (R := V) (FractionRing V))) (g := η[D.toPre.P.A])
    · exact hP.1
  obtain ⟨w₁, hw₁, hv₁⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre (FractionRing V) g'.b)
    (ε' := DegPre.lineε 1) (by rw [hφ]; exact fun _ _ _ => rfl)
    (LB.pullGen D.toPre.P.L _ _ t (toUnit (TF (R := V) (FractionRing V))).left) (pullGen_isGen _ _ _ _ ht _)
  obtain ⟨w, hw, hwv⟩ := TorsionValue.exists_frm_scale w₁ hw₁ (inv_ne_zero hl)
  have hwt : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z l * (val w (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
    intro z J hJ
    rw [hwv z J hJ, hv₁ _ _ z J hJ, val_pull hJ, Category.id_comp, ← _root_.mul_assoc, GlobalTheory.UT.CoefBasic.cst_eq,
      GlobalTheory.UT.CoefBasic.cst_eq, ← map_mul, mul_inv_cancel₀ hl, map_one, _root_.one_mul]
  refine ⟨w, hw, ⟨t, ht, hwt⟩, ?_⟩
  intro k hk wk hwk hwkg s s' v hExp hVal
  obtain ⟨σ', hIso, n, c, σ, fs, hE, hσ, hs⟩ := hExp
  choose xs hxs using fun i => GlobalTheory.ExpansionValueZero.exists_coeff (A := V) U.LG.isLB (σ i) h.left
    (GeneratorPullback.powGen U.LG.L _ _ f k) (powGen_isGen _ _ _ _ hf k) (fun W _ q => by simp)
  have hxs' : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp V) z J, Good U.LG.L z J →
      sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val :=
    fun i Z r z J hJ => (hxs i Z r z J hJ).trans (by rw [val_pow])
  choose a ha using fun i α => GlobalTheory.T.exists_integral_coefficient_section_coordinate_rig V D.toPre g t ht k α (fs i α)
  have hv := GlobalTheory.T.section_value_generic_point_integral_section V (maximalIdeal V) D A G U.toUnifPre w₀ x e h l f hExt hfv k s σ' hIso n c σ hσ xs hxs' v hVal
  have hwk' : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z (l ^ k) * (val wk (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ k).val := by
    intro z J hJ
    rw [hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hwt z J hJ, mul_pow,
      GlobalTheory.UT.CoefBasic.cst_eq, GlobalTheory.UT.CoefBasic.cst_eq, map_pow]
  have hc := GlobalTheory.T.integral_combination_terms_rational_point_frame V D.toPre g g' hP t l hl k wk hwkg hwk' s' n c fs hs a ha
  have hI := admissibleBase_of_completeNormalLocalCharZero hV
  have key := EvalZero.sumF_comb hI (FractionRing V) Finset.univ (fun i => c i * (l ^ k)⁻¹) _ _ fun i =>
    EvalZero.sumF_map (maximalIdeal V) (FractionRing V) (a i) (xs i) fun e' =>
      GlobalTheory.T.section_value_integral_point_congruent_term_sum V (maximalIdeal V) D A G U.toUnifPre h g hF f t e' k (htl e') (σ i) (fs i) (hE i e') (xs i) (hxs' i)
        (a i) (ha i)
  have hlk : l ^ k ≠ 0 := pow_ne_zero _ hl
  convert (preTransparency := .reducible) key using 1
  · funext α
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (a i α)) =
        (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (a i α) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      ← hc α, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]
  · simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (xs i)) =
        (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (xs i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      ← hv, mul_comm v, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]

end GlobalTheory.Poinc.IntEval
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.sum_mul_pulledBack_functions_genericFibre_eq : ∀ {X Y S S' T X' : Scheme.{0}} (g : X ⟶ S) (h : S' ⟶ S) (gp : T ⟶ S) (gp' : T ⟶ S') (hgp : gp' ≫ h = gp) (fst : X' ⟶ X) (snd : X' ⟶ S'), fst ≫ g = snd ≫ h → ∀ (α : Y ⟶ X) (t : Y ⟶ T) (hpb : α ≫ g = t ≫ gp) (l : Y ⟶ X') (h1 : l ≫ fst = α), l ≫ snd = t ≫ gp' → ∀ (W : X.Opens) (U : S.Opens) (hWU : W ≤ g ⁻¹ᵁ U) (n : ℕ) (c : Fin n → Γ(X, W)) (b : Fin n → Γ(T, gp ⁻¹ᵁ U)) (b' : Fin n → Γ(S', h ⁻¹ᵁ U)), (∀ m, (gp'.appLE (h ⁻¹ᵁ U) (gp ⁻¹ᵁ U) (le_preimage_of_comp_eq gp gp' h hgp U)).hom (b' m) = b m) → ∃ y : Γ(X', fst ⁻¹ᵁ W), (l.app (fst ⁻¹ᵁ W)).hom y = (Y.presheaf.map (homOfLE (extLI_preimage_le l fst α h1 W)).op).hom (∑ m, (α.app W).hom (c m) * (t.appLE (gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen g α t gp hpb W U hWU)).hom (b m)) := by
  first | exact @GlobalTheory.Mum.exists_app_eq_sum_mul_of_comm | exact GlobalTheory.Mum.exists_app_eq_sum_mul_of_comm | (intros; apply GlobalTheory.Mum.exists_app_eq_sum_mul_of_comm <;> assumption)
end
