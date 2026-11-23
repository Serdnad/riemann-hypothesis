module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTranslatedMembersLeadingTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierMonomialMemRadicalExtendedMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimStalkLeTautologicalChartRing
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.sectionValues_identity_descends_to_fibreProduct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (w : W), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s p' z J := by
  first | exact @GlobalTheory.Mum.ValDescent.desc | exact GlobalTheory.Mum.ValDescent.desc | (intros; apply GlobalTheory.Mum.ValDescent.desc <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fourierTermSystem_four_of_galois_class_sums : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.ClassSums N₁ → Φ.Four N₁ := by
  first | exact @GlobalTheory.Poinc.SFour.four_of_classSums | exact GlobalTheory.Poinc.SFour.four_of_classSums | (intros; apply GlobalTheory.Poinc.SFour.four_of_classSums <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.secK_ratio_trait_descends_to_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s₁ s₂ : SecK C.P.L.L C.α k) (c d : W), c ≠ 0 → d ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom c) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom d) * sval s₂ p' z J) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J := by
  first | exact @GlobalTheory.Mum.secK_ratio_descends | exact GlobalTheory.Mum.secK_ratio_descends | (intros; apply GlobalTheory.Mum.secK_ratio_descends <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fourierTermSystem_lam_of_exact_class_sums : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 1 ≤ s → 3 ≤ N₁ → Φ.Exact N₁ → Φ.abelian₂ := by
  first | exact @GlobalTheory.Poinc.SepLam.lam_of_exact | exact GlobalTheory.Poinc.SepLam.lam_of_exact | (intros; apply GlobalTheory.Poinc.SepLam.lam_of_exact <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torusExtension_smooth_affine_surjective_fourierTerms : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D), Smooth Y.H.hom ∧ IsAffineHom Y.q.left ∧ Surjective Y.q.left ∧ IsMonHom Y.q ∧ ∀ (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ τ : SecK D.P.L Y.q.left k, IsTermOf Y b τ := by
  first | exact @GlobalTheory.Mum.ext_smooth_affine_surj_terms | exact GlobalTheory.Mum.ext_smooth_affine_surj_terms | (intros; apply GlobalTheory.Mum.ext_smooth_affine_surj_terms <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.trait_expansionScalar_rescale_degreeOne : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1) (r t : R) (x : FractionRing R), r ≠ 0 → x * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) t → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W) (v : Wˣ), a ≠ 0 → b ≠ 0 → T.Exp a b θ₀ F₁ → b * T.φ t = a * T.φ r * v → T.Exp 1 (v : W) (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal C.A.A.hom x) θ₀) F₁ := by
  first | exact @GlobalTheory.Mum.Rescale.rescale | exact GlobalTheory.Mum.Rescale.rescale | (intros; apply GlobalTheory.Mum.Rescale.rescale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaFamily_translatedMembers_leading_times_integral : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (κ : D.toPre.X → (FractionRing R)ˣ), GlobalTheory.ThFam.Reads D.toPre κ → ∀ (k : ℕ), 1 ≤ k → ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (F : Fam D.toPre (FractionRing R) k), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) b (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) → ∀ (mu : D.toPre.X) (r : R), algebraMap R (FractionRing R) r = ((GlobalTheory.ThFam.lead κ k α mu : (FractionRing R)ˣ) : FractionRing R) → ∃ f : D.toPre.SecB k (α + k • mu), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) (α + k • mu)) (DegPre.famε k) (F.s (α + k • mu)) (D.toPre.famφB (α + k • mu)) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) ∧ ∀ e : ℕ, r ∈ maximalIdeal R ^ (e + 1) → VanMod (maximalIdeal R) f e := by
  first | exact @GlobalTheory.ThFam.member_integral | exact GlobalTheory.ThFam.member_integral | (intros; apply GlobalTheory.ThFam.member_integral <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isGrpPullback_thickening_of_carries_torusCoordinates : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → IsGrpPullback (thickObj R' I e G') Y.H (thick R' I e ≫ spMap ρ) φ := by
  first | exact @GlobalTheory.FormalModel.isGrpPullback_of_carries | exact GlobalTheory.FormalModel.isGrpPullback_of_carries | (intros; apply GlobalTheory.FormalModel.isGrpPullback_of_carries <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fourierMonomial_mem_radical_extended_maximalIdeal : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 3 ≤ N₁ → Φ.Exact N₁ → ∀ (y : Φ.Y) (nu : Fin s → Φ.X y), nu ≠ 0 → mono W (Φ.t y) (Φ.δ y) nu ∈ ((maximalIdeal A).map (Φ.ev y)).radical := by
  first | exact @GlobalTheory.Poinc.RadQ.mono_mem_radical | exact GlobalTheory.Poinc.RadQ.mono_mem_radical | (intros; apply GlobalTheory.Poinc.RadQ.mono_mem_radical <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.ringKrullDim_stalk_le_tautologicalChartRing : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite → ringKrullDim (S.presheaf.stalk (ξ (closedPoint C.R))) ≤ ringKrullDim C.R := by
  first | exact @GlobalTheory.TChart.ChartDim.ringKrullDim_stalk_le_chart | exact GlobalTheory.TChart.ChartDim.ringKrullDim_stalk_le_chart | (intros; apply GlobalTheory.TChart.ChartDim.ringKrullDim_stalk_le_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.grpPullback_of_sameFibreWithSquareBundle : ∀ (S T : Scheme.{0}) (A₀ : Over T) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (f : T ⟶ S), P₀.IsLB → P.IsLB → SameFib A₀ P₀ (𝟙 _) A P f → ∃ (φ : A₀.left ⟶ A.left) (φ₂ : (G2 A₀).left ⟶ (G2 A).left), IsGrpPullback A₀ A f φ ∧ IsSquare φ φ₂ ∧ LBIso P₀ (P.pull φ₂) ∧ LBIso (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  first | exact @GlobalTheory.FibrePull.fibre_isPull | exact GlobalTheory.FibrePull.fibre_isPull | (intros; apply GlobalTheory.FibrePull.fibre_isPull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.uniformiserOrder_eq_of_associated_stalkImage : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) (x : M.Z) (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∀ (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : T.V →+* V') (g' : R →+* V'), Function.Injective h → Irreducible (h T.ϖ) → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → ∀ (a : M.Z.presheaf.stalk x) (k : ℕ), Associated (g' (j a)) (h T.ϖ ^ k) → UOrdEq M T ξ (M.stalkHom x a) k := by
  first | exact @GlobalTheory.UPoinc.uOrdEq_stalkHom_of_associated | exact GlobalTheory.UPoinc.uOrdEq_stalkHom_of_associated | (intros; apply GlobalTheory.UPoinc.uOrdEq_stalkHom_of_associated <;> assumption)
end
