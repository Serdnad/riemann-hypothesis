module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2922
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectAbelianPartTateIsometry
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3180
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInverseNatCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Enlarge

theorem exists_rational_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → UniTrait D₁.toPre A → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ UniTrait D₂.toPre A₂ ∧ ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, (∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p') ∧ ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hR D n hn hodd hnu R₁ _ _ _ ρ D₁ A hρ hP hS hU
  have hn1 : 1 ≤ n := hn.one_lt.le
  have hR₁ : Base R₁ := ⟨hρ.1, by haveI := hR.2; exact charZero_of_injective_ringHom hρ.2.1⟩
  obtain ⟨EQ, fQ, hQ⟩ := GlobalTheory.T.degenerationQuotientPoints_rational_finiteExtension R₁ hR₁ D₁ n hn1
  obtain ⟨EA, fA, hA⟩ := GlobalTheory.T.exists_finite_extension_fraction_field_uniform R₁ hR₁ A n hn1
  haveI := fQ
  haveI := fA
  obtain ⟨R₂, _, _, _, i₁₂, e, hi₁₂, hi₁₂ρ, hloc, he⟩ := GlobalTheory.T.exists_finiteExtension_realising_subextension R hR R₁ ρ hρ (EQ ⊔ EA) inferInstance
  obtain ⟨D₂, hD₂⟩ := GlobalTheory.MumPull.exists_pull R₁ R₂ i₁₂ hi₁₂.2.1 hloc D₁
  have hP₂ := nonempty_isPullDeg_comp_of_injective R R₁ R₂ ρ i₁₂ D.toPre D₁.toPre D₂.toPre hi₁₂.2.1 hP hD₂
  have hle : nonZeroDivisors R₁ ≤ (nonZeroDivisors R₂).comap i₁₂ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective i₁₂ hi₁₂.2.1
  let ga : FractionRing R₁ →+* FractionRing R₂ := IsLocalization.map (FractionRing R₂) i₁₂ hle
  obtain ⟨A₂, g, hg, -, hm, t, ht⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap ga) A
  have gp : IsGrpPullback A₂.A A.A (spMap ga) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    exact congrArg (·.left) (hm T x y).symm⟩
  have hlb : LBIso A₂.L (A.L.pull g) := LBIso.symm ⟨t, ht⟩
  have hfib : IsFib i₁₂ A A₂ g := ⟨ga, fun r => IsLocalization.map_eq hle r, gp, hlb⟩
  have hS₂ : (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) := by
    letI := A.isAb.comm
    letI := A₂.isAb.comm
    exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ A.A A₂.A (spMap ga) g A.L A₂.L A.isLB A₂.isLB gp hlb hS
  let eQ : EQ →+* FractionRing R₂ := e.comp (IntermediateField.inclusion (le_sup_left : EQ ≤ EQ ⊔ EA)).toRingHom
  let eA : EA →+* FractionRing R₂ := e.comp (IntermediateField.inclusion (le_sup_right : EA ≤ EQ ⊔ EA)).toRingHom
  have hrat := hQ R₂ i₁₂ eQ hi₁₂ hloc (fun r => he r) D₂ hD₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, i₁₂.comp ρ, D₂, A₂, hi₁₂ρ, hP₂, hS₂,
    GlobalTheory.T.uniformisedTrait_moves_to_finite_extension R₁ hR₁ D₁ A hU R₂ i₁₂ hi₁₂ hloc D₂ hD₂ A₂ g hfib, fun σ => ⟨GlobalTheory.T.galois_fixes_quotientPoints_of_rational R₂ D₂ n hrat σ, fun x hx => ?_⟩⟩
  obtain ⟨x₀, hx₀⟩ := hA R₂ i₁₂ eA hi₁₂.2.1 (fun r => he r) A₂ g hfib x hx
  rw [hx₀, ← Category.assoc, ← spMap_comp]
  exact congrArg (fun f => spMap f ≫ x₀) (RingHom.ext fun a => σ.commutes a)

end GlobalTheory.Mum.Enlarge
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ k : ℕ, 1 ≤ k → LabTors D.toPre A k (lab k) := by
  first | exact @GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait | exact GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait | (intros; apply GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_cubical_e8LB_evenOn : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ Pc : GlobalTheory.UU.CP (powObj G₀ 8), Pc.L.L = GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W ∧ GlobalTheory.Mum.EvenOn Pc := by
  first | exact @GlobalTheory.PowE8.exists_cp_evenOn | exact GlobalTheory.PowE8.exists_cp_evenOn | (intros; apply GlobalTheory.PowE8.exists_cp_evenOn <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_lowerObject_abelianPart_tateIsometry : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La),
  GlobalTheory.LowDat.IsIsoSat Dw Z → GlobalTheory.LowDat.IsLower Dw D' Z f →
  Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X →
  D'.p = Dw.p - Module.finrank (𝓞 E) Z → D'.q = Dw.q - Module.finrank (𝓞 E) Z →
  ∀ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
  (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F),
      GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I) →
  ∃ (o' : Obj D' (GlobalTheory.LowDat.lowLevel l) (baseKA (GlobalTheory.LowDat.lowLevel l)) (GlobalTheory.LowDat.lowS C))
    (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left),
    IsGrpPullback o'.t.G C.P.D.toPre.P.A (𝟙 _) φB ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (o'.t.act.act x).left ≫ φB = φB ≫ (C.P.oD.onB.act x).left) ∧
    (∃ w : LB.Iso o'.t.PP.L (C.P.D.toPre.P.L.pull φB), w.IsGen) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
      (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)),
      GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.FiltGraded C Z F I →
      ∃ I' : GlobalTheory.LowDat.LowTate C D' o' F, GlobalTheory.LowDat.LowGraded C Z D' f o' φB F I I' := by
  first | exact @GlobalTheory.LowDat.LowObj.exists_lowObj | exact GlobalTheory.LowDat.LowObj.exists_lowObj | (intros; apply GlobalTheory.LowDat.LowObj.exists_lowObj <;> assumption)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.FactorAdj

theorem factor_adj : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), Adj (pol D') (pol D) F.pr (F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) F.xp ((DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi) := by
  intro R _ _ I D D' F
  haveI := F.inc_hom
  haveI := F.o.onB.hom F.f
  have hm : IsMonHom (F.inc ≫ F.o.onB.act F.f) := inferInstance
  have H := GlobalTheory.T.of_twisted_adjoint_comp R (pol D') (pol D) F.pr (F.o.onB.act F.e) (F.o.onB.act (Star.star F.e))
    (F.inc ≫ F.o.onB.act F.f) F.xp
    (DistribSMul.toAddMonoidHom D'.toPre.X F.e) (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e))
    ((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) F.pr_hom hm
    (fun y => c_xp F y) (fun z => c_fxi F z) (GlobalTheory.T.ringInvolutionAction_gives_polarisedAdjointPair R I D' F.O F.o F.e) (GlobalTheory.T.exists_degenerationFactor_pairing_iso_pullback R I D D' F)
  have e1 : (F.inc ≫ F.o.onB.act F.f) ≫ F.o.onB.act (Star.star F.e) = F.inc ≫ F.o.onB.act (Star.star F.e * F.f) := by
    rw [F.o.onB.map_mul, Category.assoc]
  have e2 : (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e)).comp
      ((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) =
      (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi := by
    ext y
    simp [mul_smul]
  exact e1 ▸ e2 ▸ H

end GlobalTheory.MumFam.FactorAdj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

theorem _root_.GlobalTheory.T.polarisedDegeneration_tensorPower_monomial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsTens Q D' W pr xe → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ β' : Fin m → LinearMap.BilinForm ℤ D'.X, IsMonomial D' t β' ∧ (∀ i y z, β' i y z = β' i z y) ∧ ∀ y, y ≠ 0 → ∃ i, 0 < β' i y y := by
  first | exact @GlobalTheory.TensMono.main | exact GlobalTheory.TensMono.main | (intros; apply GlobalTheory.TensMono.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.tensorData_values_facts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), TensFacts W (cmp T ν ν') (chi T ν ν') (wv T ν ν') := by
  first | exact @GlobalTheory.Mum.TensTor.tensFacts_holds | exact GlobalTheory.Mum.TensTor.tensFacts_holds | (intros; apply GlobalTheory.Mum.TensTor.tensFacts_holds <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumSide

open GlobalTheory.TensAct

section Main

theorem mside : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A), f = GlobalTheory.TensAct.matAct T A → W = (W + W.transpose) * A → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) (fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2)), t.IsGen ∧ ∀ (y : D'.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val t (D'.xK y) z J = ∏ a : Fin 4, (∏ i, ∏ j, val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) j)) (𝟙 _) z J ^ W i j) ^ (-(![1, -2, -1, 2] : Fin 4 → ℤ) a) := by
  intro R _ _ I D D' r W T A f hf hW
  classical
  let M : Fin 4 → Matrix (Fin r) (Fin r) ℤ := ![1 + A, 1, A, 0]
  let e : Fin 4 → ℤ := ![1, -2, -1, 2]
  let E : Fin 4 × (Fin r × Fin r) → ℤ := fun q => e q.1 * W q.2.1 q.2.2
  have hB := fun q : Fin 4 × (Fin r × Fin r) => GlobalTheory.T.mumfordLambda_bilinear_integral_combinations R I D D'.P.A T.pr (M q.1 q.2.1) (M q.1 q.2.2)
  choose t ht hv using hB
  have hP := fun q : Fin 4 × (Fin r × Fin r) => exists_zpow D.toPre.P.isLB (t q) (ht q) (E q)
  choose s hs hsv using hP
  have hpr : ∀ (a : Fin 4) (i : Fin r), GlobalTheory.TensAct.matAct T (M a) ≫ T.pr i = ∏ k, T.pr k ^ M a i k :=
    fun a i => GlobalTheory.TensAct.matAct_pr T (M a) i
  obtain ⟨t', ht', hv'⟩ := exists_gen D.toPre.P.isLB
    (φ' := fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left,
      (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2)
    (ε' := fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2) (by
      intro U _ h
      let Lh : (D'.P.A ⟶ D.toPre.P.A) → (D'.P.A ⟶ D.toPre.P.A) → U :=
        fun x x' => ∏ l : Fin 4, h (GlobalTheory.PolDeg.lamPts x x' l) ^ Oε l
      let P : Fin 4 → Fin r → (D'.P.A ⟶ D.toPre.P.A) := fun a i => ∏ k, T.pr k ^ M a i k
      have lamS : ∀ k l, Lh (T.pr k) (T.pr l) = Lh (T.pr l) (T.pr k) := by
        intro k l
        simp only [Lh, Fin.prod_univ_four]
        show h (T.pr k * T.pr l).left ^ (1 : ℤ) * h (T.pr k).left ^ (-1 : ℤ) * h (T.pr l).left ^ (-1 : ℤ) *
            h (1 : D'.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ) =
          h (T.pr l * T.pr k).left ^ (1 : ℤ) * h (T.pr l).left ^ (-1 : ℤ) * h (T.pr k).left ^ (-1 : ℤ) *
            h (1 : D'.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ)
        rw [mul_comm (T.pr k) (T.pr l)]
        ac_rfl
      have H1 := GlobalTheory.T.prod_four_maps_lam_pow_eq_one U W A (fun k l => Lh (T.pr k) (T.pr l)) lamS hW
      have H2 : ∏ q : Fin 4 × (Fin r × Fin r), (∏ k, ∏ l, Lh (T.pr k) (T.pr l) ^
          (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q = 1 := by
        rw [Fintype.prod_prod_type]
        exact Eq.trans (Finset.prod_congr rfl fun a _ => Fintype.prod_prod_type _) H1
      have hR : ∏ p : Fin 4 × ((Fin r × Fin r) × Fin 4), h ((![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left,
          (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) ^
          ((![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2) =
          ∏ q : Fin 4 × (Fin r × Fin r), Lh (P q.1 q.2.1) (P q.1 q.2.2) ^ E q := by
        rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun ij _ => ?_
        rw [← Finset.prod_zpow]
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [four_eq T A f hf a, comp_tensφ', hpr, hpr, ← zpow_mul]
        congr 1
        simp only [tensε, E, e]
        ring
      have hL : ∀ q : Fin 4 × (Fin r × Fin r), ∏ κ : Fin 4 ⊕ ((Fin r × Fin r) × Fin 4),
          h (Sum.elim (GlobalTheory.PolDeg.lamPts (P q.1 q.2.1) (P q.1 q.2.2))
            (fun m : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (T.pr m.1.1) (T.pr m.1.2) m.2) κ) ^
          (E q * Sum.elim Oε (fun m : (Fin r × Fin r) × Fin 4 => -(M q.1 q.2.1 m.1.1 * M q.1 q.2.2 m.1.2 * Oε m.2)) κ) =
          Lh (P q.1 q.2.1) (P q.1 q.2.2) ^ E q * ((∏ k, ∏ l, Lh (T.pr k) (T.pr l) ^
            (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q)⁻¹ := by
        intro q
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        congr 1
        · rw [← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l _ => ?_
          rw [← zpow_mul, mul_comm]
        · rw [← zpow_neg, ← Finset.prod_zpow, Fintype.prod_prod_type, Fintype.prod_prod_type]
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l _ => ?_
          rw [← zpow_mul, ← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l' _ => ?_
          rw [← zpow_mul]
          congr 1
          ring
      rw [hR, Fintype.prod_prod_type]
      refine (Finset.prod_congr rfl fun q _ => hL q).trans ?_
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, H2, inv_one, _root_.mul_one]) (GeneratorPullback.finProdGen D.toPre.P.L _ _ s)
    (finProd_isGen _ _ s hs)
  refine ⟨t', ht', fun y z J hJ => ?_⟩
  let ρ : TK R ⟶ D'.P.A := toUnit (TK R) ≫ D'.c y
  have hρ : ∀ k, ρ ≫ T.pr k = toUnit (TK R) ≫ D.toPre.c (T.xe y k) := fun k => by
    rw [Category.assoc, T.c_pr]
  have lamS : ∀ k l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J =
      val (D.toPre.tau (T.xe y l) (T.xe y k)) (𝟙 _) z J := fun k l => DVR.tauK_symm hJ _ _
  have H1 := GlobalTheory.T.prod_four_maps_lam_pow_eq_one _ W A _ lamS hW
  have H2 : ∏ q : Fin 4 × (Fin r × Fin r), (∏ k, ∏ l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J ^
      (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q = 1 := by
    rw [Fintype.prod_prod_type]
    refine Eq.trans (Finset.prod_congr rfl fun a _ => Fintype.prod_prod_type _) H1
  have hq : ∀ q : Fin 4 × (Fin r × Fin r), val (s q) (D'.xK y) z J =
      ((val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) q.1) q.2.1) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) q.1) q.2.2)) (𝟙 _) z J)⁻¹ *
        ∏ k, ∏ l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J ^ (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q := fun q => by
    rw [hsv q _ _ z J hJ, show D'.xK y = ρ.left from rfl, hv q ρ (fun k => T.xe y k) hρ z J hJ, xe_four, xe_four]
  rw [hv' _ _ z J hJ, val_finProd _ _ _ _ _ hJ, Finset.prod_congr rfl fun q _ => hq q]
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [H2, _root_.mul_one, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [inv_zpow', ← zpow_mul]
  congr 1
  simp only [E, e]
  ring

end Main

end GlobalTheory.MumSide
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.USum

theorem uSame_self {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    USame ρ ρ (fun b => b) (RingHom.id Ω) := by
  let f := spMap S.R.val.toRingHom
  let P := ρ.P
  let P₀ : PolAV (Sp Ω) := {
    A := (Over.pullback f).obj P.A
    isAb := TLinPf.isAb_pullback f P.A P.isAb
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (isGrpPullback_pullback P.A f).1 P.smoothDim
    L := P.L.pull (pullback.fst P.A.hom f)
    isLB := pull_isLB P.isLB _
    rigid := GlobalTheory.PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
    sym := GlobalTheory.PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
    ample := by
      letI := P.isAb.proper
      exact GlobalTheory.AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
    ktriv := by
      obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
      exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv }
  refine ⟨P₀, pullback.fst ρ.P.A.hom (spMap S.R.val.toRingHom), pullback.fst ρ.P.A.hom (spMap S.R.val.toRingHom),
    isGrpPullback_pullback _ _, isGrpPullback_pullback _ _, GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB,
    GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB, fun b => ?_⟩
  refine ⟨pullback.lift (spMap S.R.val.toRingHom ≫ (ρ.pt b).left) (𝟙 _) ?_, pullback.lift_fst _ _ _,
    pullback.lift_fst _ _ _⟩
  rw [Category.assoc, Over.w]; simp [f]

theorem sum_ev_shift : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω}
    (ρ : S.Real) (H : AddSubgroup S.Gam) (m : ℕ), S.N = m ^ 2 → ∀ h h' : S.Gam, m • h = m • h' → h' - h ∈ H →
    ∃ ξ : Ω, (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ t ∈ S.perp H,
      ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j := by
  intro o Ω _ _ _ _ S ρ H m hm h h' e hH
  obtain ⟨P₀, a, a', x, hx, hadd⟩ := exists_isGenLab (uSame_self ρ)
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨ξ₁, ⟨k₁, hk₁, hξ₁⟩, hc₁⟩ :=
    GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue ρ ρ (fun b => b) (RingHom.id Ω) P₀ a a' x hx m hm (m • h) x₀ h rfl
  obtain ⟨ξ₂, ⟨k₂, hk₂, hξ₂⟩, hc₂⟩ :=
    GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue ρ ρ (fun b => b) (RingHom.id Ω) P₀ a a' x hx m hm (m • h) x₀ h' e.symm
  have hξ₂0 : ξ₂ ≠ 0 := by
    rintro rfl
    rw [zero_pow hk₂.ne'] at hξ₂
    exact zero_ne_one hξ₂
  refine ⟨ξ₁ * ξ₂⁻¹, ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, ?_⟩, fun t ht => ?_⟩
  · rw [mul_pow, inv_pow, pow_mul, hξ₁, one_pow, mul_comm k₁, pow_mul, hξ₂, one_pow, inv_one, mul_one]
  obtain ⟨v, hv⟩ := TV.ex hx hadd hm t (h := h) (κ := m • h) rfl
  have hv' := hv.transl hx hadd hm (k := h' - h) (by rw [smul_sub, e, sub_self]) (ht _ hH)
  rw [add_sub_cancel] at hv'
  have E₁ := hc₁ t v hv
  have E₂ := hc₂ t v hv'
  simp only [RingHom.id_apply] at E₁ E₂
  have E := E₂.symm.trans E₁
  have hinv : ξ₂ * ξ₂⁻¹ = 1 := mul_inv_cancel₀ hξ₂0
  rw [← sub_eq_zero]
  refine (mul_eq_zero.1 ?_).resolve_left (mul_ne_zero hξ₂0 hx₀)
  linear_combination E - ξ₁ * S.th x₀ * (∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j) * hinv

end GlobalTheory.UPoinc.USum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pulled_back_period_constants_diag_mem_maximal : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V₁, w ≠ 0 ∧ (q a a : FractionRing V₁) = algebraMap V₁ _ w := by
  first | exact @GlobalTheory.PeriodPos.periods_pos_diag | exact GlobalTheory.PeriodPos.periods_pos_diag | (intros; apply GlobalTheory.PeriodPos.periods_pos_diag <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exp_mulPull_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)) (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)), MulFam m F₁ G → MulSecK C m θ₀ S → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → T.Exp a b θ₀ F₁ → ∃ v : Wˣ, T.Exp a (b * v) S G := by
  intro R _ _ _ hR D C m hm F₁ G θ₀ S hMF hMS W _ _ _ T a b ha hE
  obtain ⟨σ, ⟨σ', f', hcar, hpull, hexp⟩, hgen⟩ := hE
  obtain ⟨u, hu, hS⟩ := hMS
  obtain ⟨σ₂, hσ₂⟩ := GlobalTheory.T.exists_section_pullback_commuting_endomorphism_generator C.P.L.L C.P.L.isLB T.β (mulA T.G m).left (mulA C.G m).left
    (GlobalTheory.ZH.TorsFrame.mulA_comm T.cart m) 1 (m ^ 2) u hu σ
  have hgen₂ := GlobalTheory.T.multiplicationPullback_trait_genericCondition R D C W T m a u θ₀ S hS σ σ₂ hgen hσ₂
  obtain ⟨G', hG'⟩ := GlobalTheory.Mum.exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc (m ^ 2) G
  obtain ⟨uG, σ'', huG, hσ'', hexp''⟩ := GlobalTheory.T.expansion_multiplicationPullback_trait_degreeOne R hR D C W T m hm F₁ G hMF σ' f' hpull hexp G'.f hG'
  obtain ⟨v, hv⟩ := GlobalTheory.T.multiplicationPullbacks_differ_by_unit R hR D C W T m u hu uG huG b σ' σ hcar σ₂ σ'' hσ₂ hσ''
  exact ⟨v, σ₂, ⟨σ'', G'.f, hv, hG', hexp''⟩, hgen₂⟩

end GlobalTheory.Mum
end
