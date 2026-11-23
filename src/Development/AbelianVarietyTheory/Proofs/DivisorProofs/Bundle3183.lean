module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierEqOfPrimitiveAdjointBundle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3057
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

theorem _root_.GlobalTheory.T.thetaMultiplier_eq_of_primitive_adjoint_bundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (f f' : G ⟶ G), IsMonHom f → IsMonHom f' → f * f' = 𝟙 G → AdjCls (cls U.LG.L U.LG.isLB) (cls U.LG.L U.LG.isLB) f f' → cls U.LG.L U.LG.isLB = lam (cls U.LG.L U.LG.isLB) (𝟙 G) f → ∀ (fB : D.toPre.P.A ⟶ D.toPre.P.A) (m : D.toPre.X → D.toPre.X), Over₀ U.toUnifPre U.toUnifPre f fB → OnTorus U.toUnifPre U.toUnifPre f' m → PrimVal D.toPre fB m := by
  first | exact @GlobalTheory.PrimAdj.primVal_of_adj | exact GlobalTheory.PrimAdj.primVal_of_adj | (intros; apply GlobalTheory.PrimAdj.primVal_of_adj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.equivariant_linearExtension_to_algClosedField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (E₀ : Fam D.toPre (Kb R) N → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), Eqv D.toPre A (Kb R) N lab E₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (Kb R) F] [IsScalarTower (FractionRing R) (Kb R) F] (lab' : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A)), LabExt (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) lab lab' → ∀ (E' : Fam D.toPre F N →ₗ[F] SecF A F N), (∀ s, E' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s) = secPull A (Kb R) F N (E₀ s)) → ∀ (p : QkPt D.toPre F N) w (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (s s' : Fam D.toPre F N), GlobalTheory.UT.TXFrame N p w → SymLift A.A A.L N N (lab' p) θ → PhiRel D.toPre F N p w s s' → IsActOf A.A A.L N θ (E' s) (E' s') := by
  first | exact @GlobalTheory.Mum.UpAct.act_extension | exact GlobalTheory.Mum.UpAct.act_extension | (intros; apply GlobalTheory.Mum.UpAct.act_extension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

theorem _root_.GlobalTheory.T.toricTorsionSection_of_spread_through_latticeMap : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (o : Type) [CommRing o] (s : B ⟶ Sp o) (o₁ : o →+* V₁) (o₂ : o →+* V₂), ξ₁ ≫ s = spMap o₁ → ξ₂ ≫ s = spMap o₂ → ∀ (k : ℕ) (ζ : o), 1 ≤ k → IsUnit (k : o) → ζ ^ k = 1 → ∀ (Wo : B.Opens) (h : Wo.toScheme ⟶ H.left) (ξ₁' : Sp V₁ ⟶ Wo.toScheme) (ξ₂' : Sp V₂ ⟶ Wo.toScheme), h ≫ H.hom = Wo.ι → ξ₁' ≫ Wo.ι = ξ₁ → ξ₂' ≫ Wo.ι = ξ₂ → ∀ (F₁ : Type) [Field F₁] [IsAlgClosed F₁] [Algebra (FractionRing V₁) F₁] (F₂ : Type) [Field F₂] [IsAlgClosed F₂] [Algebra (FractionRing V₂) F₂] (c : D₁.toPre.X →+ ℤ) (x₁ : TFK (R := V₁) F₁ ⟶ A₁.A) (x₂ : TFK (R := V₂) F₂ ⟶ A₂.A), TorAt U₁ F₁ k (algebraMap (FractionRing V₁) F₁ (algebraMap V₁ (FractionRing V₁) (o₁ ζ))) c x₁ → x₁.left ≫ genMap U₁ ≫ β₁ = spMap (algebraMap (FractionRing V₁) F₁) ≫ jK V₁ ≫ ξ₁' ≫ h → x₂ ^ k = 1 → x₂.left ≫ genMap U₂ ≫ β₂ = spMap (algebraMap (FractionRing V₂) F₂) ≫ jK V₂ ≫ ξ₂' ≫ h → TorAt U₂ F₂ k (algebraMap (FractionRing V₂) F₂ (algebraMap V₂ (FractionRing V₂) (o₂ ζ))) (c.comp ρ) x₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.torAt_of_spread₂ | exact GlobalTheory.Poinc.Sep.Spz.torAt_of_spread₂ | (intros; apply GlobalTheory.Poinc.Sep.Spz.torAt_of_spread₂ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

theorem _root_.GlobalTheory.T.toricTorsionPoint_character_eq_weilPairing_label : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (c : 𝔪.D.toPre.X →+ ℤ) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), TorAt 𝔪.U (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) c x → x.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt τ).left → ∀ a mu, 𝔪.YY a mu → ((c (𝔪.e₈ mu) : ℤ) : ZMod (X₁.S.r * X₁.S.N)) = ((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.torAt_char_eq_weil | exact GlobalTheory.Poinc.Sep.Spz.torAt_char_eq_weil | (intros; apply GlobalTheory.Poinc.Sep.Spz.torAt_char_eq_weil <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OffClosed

theorem nonempty_preimage {S : Scheme.{0}} {G X : Over S} (O : G.left.Opens) (w w' : G ⊗ X ⟶ G)
    (h : lift w' (snd G X) ≫ w = fst G X) (z : (G ⊗ X).left) (hz : (fst G X).left z ∈ O) :
    ((w.left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left).Nonempty := by
  refine ⟨(lift w' (snd G X)).left z, ?_⟩
  rw [← h] at hz
  simpa using hz

theorem exists_section (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G)
    (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R) (hx : closedPoint R ∉ Set.range x) (O : G.left.Opens) (pt : Sp Ω)
    (hO : ∃ g ∈ O, G.hom g = x pt) {J : Type} [Finite J] (k : J → (Over.mk x ⟶ G)) :
    ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, ∀ i, (k i * (toUnit (Over.mk x) ≫ a)).left pt ∈ O ∧
      (k i * (toUnit (Over.mk x) ≫ a)⁻¹).left pt ∈ O := by
  have hirr : IrreducibleSpace (pullback G.hom x : Scheme.{0}) := GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint _ G hG Ω x
  obtain ⟨g, hg, hgx⟩ := hO
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := x) g pt hgx
  let X : Over (Sp R) := Over.mk x
  have hz' : (fst G X).left z ∈ O := by
    change pullback.fst G.hom x z ∈ O
    rw [hz]; exact hg
  let w : J × Bool → (G ⊗ X ⟶ G) := fun j =>
    match j.2 with
    | true => (snd G X ≫ k j.1) * fst G X
    | false => (snd G X ≫ k j.1) * (fst G X)⁻¹
  have hw : ∀ j, (((w j).left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left).Nonempty := by
    rintro ⟨i, _ | _⟩
    · refine nonempty_preimage O _ ((fst G X)⁻¹ * (snd G X ≫ k i)) ?_ z hz'
      simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst]
      group
    · refine nonempty_preimage O _ ((snd G X ≫ k i)⁻¹ * fst G X) ?_ z hz'
      simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst]
      group
  have hirr' : IrreducibleSpace (G ⊗ X).left := hirr
  let U : (G ⊗ X).left.Opens :=
    ⟨⋂ j, (((w j).left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left),
      isOpen_iInter_of_finite fun j => ((w j).left ⁻¹ᵁ O).isOpen⟩
  have hU : (U : Set (G ⊗ X).left).Nonempty := by
    refine ⟨genericPoint (G ⊗ X).left, Set.mem_iInter.2 fun j => ?_⟩
    exact ((genericPoint_spec (G ⊗ X).left).mem_open_set_iff ((w j).left ⁻¹ᵁ O).isOpen).2 (by simpa using hw j)
  obtain ⟨a, aΩ, ha, h1, h2, h3⟩ := GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hR G hG.smooth (η[G]).left (Over.w η[G]) Ω x hx hirr U hU
  let a' : 𝟙_ (Over (Sp R)) ⟶ G := Over.homMk a ha
  let u : X ⟶ G := toUnit X ≫ a'
  have hu : (lift u (𝟙 X)).left = aΩ := by
    apply pullback.hom_ext
    · refine Eq.trans ?_ h1.symm
      have : (lift u (𝟙 X)).left ≫ (fst G X).left = u.left := by rw [← Over.comp_left, lift_fst]
      exact this
    · refine Eq.trans ?_ h2.symm
      have : (lift u (𝟙 X)).left ≫ (snd G X).left = (𝟙 X : X ⟶ X).left := by rw [← Over.comp_left, lift_snd]
      exact this
  have key : ∀ j, (lift u (𝟙 X) ≫ w j).left pt ∈ O := by
    intro j
    have := Set.mem_iInter.1 (h3 ⟨pt, rfl⟩) j
    rw [← hu] at this
    exact this
  refine ⟨a', fun i => ⟨?_, ?_⟩⟩
  · have := key (i, true)
    simp only [w, MonObj.comp_mul, lift_snd_assoc, lift_fst, Category.id_comp] at this
    exact this
  · have := key (i, false)
    simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst, Category.id_comp] at this
    exact this

theorem exists_ten (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (O : G.left.Opens) (hO : ∃ g ∈ O, G.hom g = closedPoint R) (y : G.left) (hy : G.hom y ≠ closedPoint R) :
    ∃ a b c : G ⟶ G, ∀ f ∈ cubeTen (𝟙 G) a b c, f.left y ∈ O := by
  have := hG.smooth
  let Ω : Type := G.left.residueField y
  let yy : Sp Ω ⟶ G.left := G.left.fromSpecResidueField y
  let x : Sp Ω ⟶ Sp R := yy ≫ G.hom
  have hyy : ∀ p, yy p = y := fun p => by
    have : yy p ∈ Set.range (G.left.fromSpecResidueField y) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at this
    exact this
  have hx : ∀ p, x p = G.hom y := fun p => congrArg G.hom (hyy p)
  have hx' : closedPoint R ∉ Set.range x := by
    rintro ⟨p, hp⟩
    exact hy ((hx p).symm.trans hp)
  let pt : Sp Ω := closedPoint Ω
  have hO' : ∃ g ∈ O, G.hom g = x pt := by
    obtain ⟨g, hg, hgc⟩ := hO
    have hs : x pt ⤳ G.hom g := by rw [hgc]; exact specializes_closedPoint _
    obtain ⟨g', h1, h2⟩ := Flat.generalizingMap G.hom hs
    exact ⟨g', h1.mem_open O.isOpen hg, h2⟩
  let X : Over (Sp R) := Over.mk x
  let yh : X ⟶ G := Over.homMk yy rfl
  obtain ⟨a, ha⟩ := exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh]
  obtain ⟨b, hb⟩ := exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh]
  obtain ⟨c, hc⟩ := exists_section R hR G hG Ω x hx' O pt hO'
    ![(1 : Over.mk x ⟶ G), yh, (toUnit X ≫ b)⁻¹, yh * (toUnit X ≫ b)⁻¹]
  refine ⟨toUnit G ≫ a, toUnit G ≫ b, toUnit G ≫ c, fun f hf => ?_⟩
  have e : f.left y = (yh ≫ f).left pt := (congrArg f.left (hyy pt)).symm
  rw [e]
  have ht : ∀ d : 𝟙_ (Over (Sp R)) ⟶ G, yh ≫ toUnit G ≫ d = toUnit X ≫ d := fun d => by
    rw [← Category.assoc, comp_toUnit]
  have a0 := ha 0
  have a1 := ha 1
  have b0 := hb 0
  have b1 := hb 1
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at a0 a1 b0 b1 c0 c1 c2 c3
  rw [_root_.one_mul, _root_.one_mul] at a0 b0 c0
  simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ht, mul_inv, ← _root_.mul_assoc]
  exacts [a1.1, a1.2, a0.1, a0.2, b1.1, c1.1, c3.2, b0.1, c0.1, c2.2]

theorem exists_gen_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
  intro R _ _ _ hR M G' _ _ _ P' G _ _ β hG hpb θ O hO hθ y hy
  have := hR.1
  have hβ : IsProper β := MorphismProperty.of_isPullback (P := @IsProper) hpb.1.flip M.proper
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  have hO' : ∃ g ∈ O', G.hom g = closedPoint R := by
    obtain ⟨g, hg, hgc⟩ := hO
    refine ⟨g, fun g' hg' => ?_, hgc⟩
    subst hg'
    exact TopologicalSpace.Opens.mem_iSup.2 (hθ g' hg hgc)
  obtain ⟨a, b, c, h⟩ := exists_ten R hR.2.2.2 G hG O' hO' y hy
  let V : G.left.Opens := ⟨⋂ f ∈ {f | f ∈ cubeTen (𝟙 G) a b c}, ((f.left ⁻¹ᵁ O' : G.left.Opens) : Set G.left),
    (List.finite_toSet _).isOpen_biInter fun f _ => (f.left ⁻¹ᵁ O').isOpen⟩
  refine ⟨V, Set.mem_iInter₂.2 h, ?_⟩
  obtain ⟨hl, hm⟩ := GlobalTheory.T.grpPullback_points_lift_and_compat_mul_inv _ _ M.π G G' β hpb G' G β hpb.1.w
  obtain ⟨a', ha⟩ := hl a
  obtain ⟨b', hb⟩ := hl b
  obtain ⟨c', hc⟩ := hl c
  have h1 : (𝟙 G' : G' ⟶ G').left ≫ β = β ≫ (𝟙 G : G ⟶ G).left := by simp
  have mul := fun u v u' v' hu hv => (hm u v u' v' hu hv).1
  have inv := fun u u' hu => (hm u u u' u' hu hu).2
  have hten : ∀ f' ∈ cubeTen (𝟙 G') a' b' c', ∃ f ∈ cubeTen (𝟙 G) a b c, f'.left ≫ β = β ≫ f.left := by
    intro f' hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ ha)⟩
    · exact ⟨_, by simp [cubeTen], ha⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hb⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hc⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ (mul _ _ _ _ hb hc))⟩
    · exact ⟨_, by simp [cubeTen], hb⟩
    · exact ⟨_, by simp [cubeTen], hc⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ (mul _ _ _ _ hb hc)⟩
  have := GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points M.S G' P' θ G' (𝟙 G') a' b' c' (β ⁻¹ᵁ V) (by
    intro f' hf' g hg
    obtain ⟨f, hf, e⟩ := hten f' hf'
    have h2 : f.left (β g) ∈ farSet β θ := Set.mem_iInter₂.1 hg f hf
    refine h2 (f'.left g) ?_
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply])
  have e : (β ⁻¹ᵁ V).ι ≫ (𝟙 G' : G' ⟶ G').left = (β ⁻¹ᵁ V).ι := by simp
  rw [e] at this
  exact this

end GlobalTheory.Mum.OffClosed
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_finite_normalization_integral_sections : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsIntegral S] [IsDominant gp]
    (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)), IsFinSub gp F →
    ∃ (S' : Scheme.{0}) (h : S' ⟶ S) (gp' : Sp K ⟶ S') (hgp : gp' ≫ h = gp),
      IsFinite h ∧ IsIntegral S' ∧ IsDominant gp' ∧
      ∀ V : S.Opens, IsAffineOpen V → ∀ x ∈ F V, ∃ c : Γ(S', h ⁻¹ᵁ V),
        (gp'.appLE (h ⁻¹ᵁ V) (gp ⁻¹ᵁ V) (le_preimage_of_comp_eq gp gp' h hgp V)).hom c = x := by
  first | exact @GlobalTheory.Mum.exists_finite_of_isFinSub | exact GlobalTheory.Mum.exists_finite_of_isFinSub | (intros; apply GlobalTheory.Mum.exists_finite_of_isFinSub <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_pulledBackPowerSection_of_local_lifts : ∀ {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α) (k : ℕ), (∀ U : X'.Opens, Function.Injective (a.app U).hom) → ∀ (s : SecK L α k) (n : ℕ) (j : Fin n → L.ι) (W : Fin n → X'.Opens), (⨆ b, W b = ⊤) → ∀ (hW : ∀ b, W b ≤ f ⁻¹ᵁ L.U (j b)), (∀ b, ∃ y : Γ(X', W b), (a.app (W b)).hom y = (Y.presheaf.map (homOfLE (extLI_le_chart L f a α e (W b) (j b) (hW b))).op).hom (s.f (fun _ => j b))) → ∃ σ : SecK L f k, ∀ j' : Fin 1 → L.ι, (a.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j') = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a α e j')).op).hom (s.f j') := by
  first | exact @GlobalTheory.Mum.secK_lift_of_local_lift | exact GlobalTheory.Mum.secK_lift_of_local_lift | (intros; apply GlobalTheory.Mum.secK_lift_of_local_lift <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_levelIsometry_genericFibre_boundaryChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I := by
  first | exact @GlobalTheory.LowDat.exists_xfLevel | exact GlobalTheory.LowDat.exists_xfLevel | (intros; apply GlobalTheory.LowDat.exists_xfLevel <;> assumption)
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_levelIsometry_extension_algClosed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (I₀ : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD (AlgebraicClosure (FractionRing R))),
    GlobalTheory.LowDat.XFLevel C tK m1 m2 (AlgebraicClosure (FractionRing R)) I₀ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧
      ∀ n a, (I.ev n a).y = (I₀.ev n a).y := by
  first | exact @GlobalTheory.LowDat.exists_xfLevel_ext | exact GlobalTheory.LowDat.exists_xfLevel_ext | (intros; apply GlobalTheory.LowDat.exists_xfLevel_ext <;> assumption)
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.exists_isotropicSaturatedSubmodule_of_finrank_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (r : ℕ), r ≤ min D.p D.q →
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = r := by
  first | exact @GlobalTheory.LowFilt.exists_isIsoSat_finrank | exact GlobalTheory.LowFilt.exists_isIsoSat_finrank | (intros; apply GlobalTheory.LowFilt.exists_isIsoSat_finrank <;> assumption)
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensPair

theorem pair_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), (∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb D.toPre.P.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j)) → ∀ (i₀ : Fin r), letI := T.mod (symUnitOf W h); ∃ w : LB.Iso (abelian₂ D.toPre.P.A D.toPre.P.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good D.toPre.P.L z J' → val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b)).left z J J' * val (D'.toPre.tau (T.xi i₀ a) (TensO.binv (symUnitOf W h) • T.xi i₀ b)) (𝟙 _) z J := by
  intro R _ _ _ _ D D' r W h _ T hw i₀
  obtain ⟨w₁, hw₁, hv₁⟩ := hw
  have hsum : ∑ j, (W + W.transpose) i₀ j * TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ = 1 := by
    have hb : (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose :=
      IsUnit.unit_spec _
    have key := congrFun (congrFun (Units.mul_inv (symUnitOf W h).1) i₀) i₀
    rw [hb, Matrix.mul_apply, Matrix.one_apply_eq] at key
    exact key
  obtain ⟨u₀, hu₀, hv₀⟩ := GlobalTheory.T.exists_biextension_generator_bezout_combination D.toPre D.tau_bimult (fun j => (W + W.transpose) i₀ j)
    (fun j => TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀) hsum
  obtain ⟨u, hu, hvu⟩ := exists_gen D.toPre.P.isLB
    (φ' := Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun I : ULift (Finset (Fin 2)) => (psum D.toPre.P.A (x2 D.toPre.P.A) I.down).left))
    (ε' := Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun I : ULift (Finset (Fin 2)) => -((-1) ^ (2 - I.down.card))))
    (fun U _ hh => by
      clear hv₀ hv₁ hu₀ u₀ hw₁ w₁
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      refine congrArg (· * _) ?_
      simp only [Sum.elim_inl, GlobalTheory.TensPair.lamPts_pull, Fintype.prod_prod_type]
      symm
      rw [Finset.prod_eq_single i₀ ?_ (by simp)]
      · exact Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun l _ => by rw [if_pos rfl]
      · intro i _ hi
        refine Finset.prod_eq_one fun j _ => ?_
        rw [Fin.prod_univ_four, if_neg hi]
        simp only [GlobalTheory.PolDeg.lamPts, Oε, _root_.one_mul]
        simp [zpow_mul, zpow_neg]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        module)
    u₀ hu₀
  obtain ⟨w, hw, hvw⟩ := GlobalTheory.T.exists_iso_glued_from_linComb_pullback D.toPre.P.isLB (LB.isLB_linComb D'.toPre.P.isLB _ _) _ _ _ _ _ w₁ hw₁ u hu
  refine ⟨w, hw, fun a b z J J' hJ hJ' => ?_⟩

  suffices key : ∀ b' : D'.toPre.X, (∀ j, T.xe b' j = TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ • b) →
      val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J J' *
        val (D'.toPre.tau (T.xi i₀ a) b') (𝟙 _) z J by
    exact key _ (fun j => (Tens.xe_smul T (symUnitOf W h) (TensO.binv _) (T.xi i₀ b) j).trans (by
      rw [Finset.sum_eq_single i₀ (fun k _ hk => by rw [GlobalTheory.TensPair.xe_xi, if_neg hk, smul_zero]) (by simp),
        GlobalTheory.TensPair.xe_xi, if_pos rfl]))
  intro b' hb'
  have hPl : (lift (toUnit (TK R) ≫ D'.toPre.c (T.xi i₀ a)) (toUnit (TK R) ≫ D'.toPre.c b') : TK R ⟶ G2 D'.toPre.P.A).left =
      (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫
        (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left := by
    rw [GlobalTheory.TensPair.pt_pull T i₀ _ a b _ b' (GlobalTheory.TensPair.xe_xi T i₀ · a) hb']; rfl
  have t0 : ∀ x, val (D.toPre.tau 0 x) (𝟙 _) z J' = 1 := fun x => by
    have e := GlobalTheory.TauTwist.val_tau_nsmul (𝟙 (TK R)) hJ' D.tau_bimult 0 x x
    rw [zero_smul] at e
    simpa [cubN] using e
  have hPi : ∏ i, ∏ j, val (D.toPre.tau (T.xe (T.xi i₀ a) i) (T.xe b' j)) (𝟙 _) z J' ^ ((W + W.transpose) i j) =
      ∏ j, val (D.toPre.tau a (TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ • b)) (𝟙 _) z J' ^ ((W + W.transpose) i₀ j) := by
    rw [Finset.prod_eq_single i₀ (fun i _ hi => Finset.prod_eq_one fun j _ => by
      rw [GlobalTheory.TensPair.xe_xi, if_neg hi, t0, one_zpow]) (by simp)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [GlobalTheory.TensPair.xe_xi, if_pos rfl, hb']
  have e1 := hv₁ (T.xi i₀ a) b' z J' J hJ' hJ
  rw [hPi, hPl] at e1
  have e2 := hvw _ (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J' hJ'
    (fun I => J (((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫
        (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left) ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))
    (hJ.mem _ _)
  have e3 := hv₀ a b z J' hJ'
  have e4 := hvu _ (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J' hJ'
  clear hv₀ hvu hvw hv₁ hPi
  change val _ _ z J = gv w₁ _ z _ _ * _ at e1
  have hj : (fun I : ULift (Finset (Fin 2)) => J ((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left)) =
      (fun I => J (((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left) ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left)) :=
    funext fun I => by rw [Category.assoc]
  have e5 : GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J J' = gw w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z (fun I : ULift (Finset (Fin 2)) => J ((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))
      (fun I => J' ((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (psum D.toPre.P.A (x2 D.toPre.P.A) I.down).left)) := rfl
  rw [e5, hj, e2, e1, e3, e4]
  have key : ∀ {G : Type} [CommGroup G] (A P X : G), A * P = X⁻¹ * A * (X * P) := fun A P X => by
    rw [_root_.mul_comm X⁻¹ A, _root_.mul_assoc, inv_mul_cancel_left]
  exact key (G := ((TK R).left.presheaf.stalk z)ˣ) _ _ _

end GlobalTheory.TensPair
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam


theorem _root_.GlobalTheory.T.exists_degenerationFactor_pairing_iso_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), ∃ w : LB.Iso (cubeLB (pol D).B ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B] (pol D).M.L) (cubeLB (pol D').B ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f] (pol D').M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good (pol D').M.L z J₁ → Good (pol D).M.L z J₂ → val ((pol D).tau (F.xp y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left z J₁ J₂ * val ((pol D').tau ((DistribSMul.toAddMonoidHom D'.toPre.X F.e) y) (((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) y')) (𝟙 _) z J₁ := by
  first | exact @GlobalTheory.MumFam.FactorAdj.exists_pull | exact GlobalTheory.MumFam.FactorAdj.exists_pull | (intros; apply GlobalTheory.MumFam.FactorAdj.exists_pull <;> assumption)
end
