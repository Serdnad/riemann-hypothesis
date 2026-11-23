module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle036
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionPointOfIntegralModelPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS

theorem exists_neutral_group_model : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = (a ^ c).left ≫ G.j := by
  intro R K _ _ _ _ _ hS A _ _ hA hP
  have h1 := hS.1
  have h3 := hS.2.2.1
  have h4 := hS.2.2.2
  obtain ⟨n, M, hI, hW⟩ := GlobalTheory.T.exists_weak_neron_model R K inferInstance A hA.smooth hA.proper hP
  obtain ⟨N, hN, c, hc, hT⟩ := GlobalTheory.T.exists_weakNeronModel_birational_groupLaw R K hS A hA n M hI hW
  obtain ⟨N', hN', hle⟩ := GlobalTheory.T.exists_strict_model_of_birational R K hS A hA N hN
  obtain ⟨G, inst, hG, he, hs⟩ := GlobalTheory.T.exists_grpObj_of_strictBirationalLaw R K hS A hA N' hN'
  obtain ⟨b1, b2, b3, -, -⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hS
  refine ⟨G, inst, hG, he, c, hc, fun a => hs (a ^ c) ?_⟩
  have e1 : GenIso N' N (𝟙 A) := b1 A N' N hN'.1.1 hle
  have e2 : GenIso N N' (𝟙 A) := (b3 A A N' N (Iso.refl A)).1 e1
  have e3 := b2 A A A N' N N _ _ hN.1 e1 (hT a)
  have e4 := b2 A A A N' N N' _ _ hN.1 e3 e2
  simpa only [Category.id_comp, Category.comp_id] using e4

end GlobalTheory.SS
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.isAbelianScheme_of_abelian_thickenings : Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsAbelianScheme (Y e)) → (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), GlobalTheory.AbLaw.IsProjBy B.hom → Smooth B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ _ : GrpObj B, IsAbelianScheme B ∧ ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e) := by
  first | exact @GlobalTheory.AlgGroup.isAbelianScheme_of_thickenings | exact GlobalTheory.AlgGroup.isAbelianScheme_of_thickenings | (intros; apply GlobalTheory.AlgGroup.isAbelianScheme_of_thickenings <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.GoodTrait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_of_point {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ)
    {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = x ≫ χ) : PolAt t x := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull x t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t' : SAB H (Sp K)) (p : Sp K ⟶ Y.X) (_ : p = y ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t y) := by
    intro t' p hp n
    subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ hy.symm n
  have h₂ : LBIso PP'.L (t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper,
    amplePt _ _ y _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃) Y.oF.ample Y.oF.ktriv⟩

theorem splitOver_of_abLocus {W : Type} [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) (h : ∀ x, x ∈ abLocus G) : GlobalTheory.LN.SplitOver G (maximalIdeal W) := by
  letI := Ideal.Quotient.field (maximalIdeal W)
  have p : Spec (CommRingCat.of (W ⧸ maximalIdeal W)) := (default : PrimeSpectrum _)
  have hp := ArcNotAbelian.isProper_fibre G hG (W ⧸ maximalIdeal W) (spMap (Ideal.Quotient.mk (maximalIdeal W))) p (h _)
  have := hG.comm
  have := hG.smooth
  have := hG.geomConnected
  have hab : IsAbelianScheme ((Over.pullback (spMap (Ideal.Quotient.mk (maximalIdeal W)))).obj G) :=
    ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd _ _)), hp,
      inferInstanceAs (GeometricallyConnected (pullback.snd _ _))⟩
  unfold GlobalTheory.LN.SplitOver
  exact ⟨_, ZJ.isGt_splitExtOfAbelian _ hab⟩

theorem exists_pelUnif_subsingleton : LL → UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ Y.j = jK W ≫ χ → Set.range χ ⊆ abLocus Y.t.G → ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t), Subsingleton P.D.toPre.X := by
  intro _ hU E _ _ _ H D l Xo c O _ β Y W _ _ _ hW χ y hy hab
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp W), Nonempty (SABMap t Y.t χ) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull χ Y.t
    exact ⟨_, ⟨m⟩⟩
  have ht : ∀ x, x ∈ abLocus t.G := fun x => (abLocus_pullback abLocusOne Y.t.semi m.cart.1 x).1 (hab ⟨x, rfl⟩)
  obtain ⟨P, -⟩ := hU E H W hW t (polAt_of_point Y m _ y hy) (splitOver_of_abLocus t.G t.semi ht)
  refine ⟨t, m, P, ?_⟩
  have hmax : (maximalIdeal W ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (W ⧸ maximalIdeal W ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (W ⧸ maximalIdeal W ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (W ⧸ maximalIdeal W ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick W (maximalIdeal W) 0) p (ht _)
    P.D.toPre.X g.i g.i_hom

end GlobalTheory.GoodTrait
end

section


theorem _root_.GlobalTheory.T.exists_valuationSubring_integral_closure_completeDVR : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (ϖ : O), GlobalTheory.LN.ArcBase O ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F], ∃ S : ValuationSubring F, ∀ x, x ∈ S ↔ IsIntegral O x := by
  first | exact @GlobalTheory.LN.exists_valuationSubring_isIntegral | exact GlobalTheory.LN.exists_valuationSubring_isIntegral | (intros; apply GlobalTheory.LN.exists_valuationSubring_isIntegral <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
theorem _root_.GlobalTheory.T.fibrewise_nonvanishing_of_invertible_pushforward : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t₀ : SAB H S), PushInvertible t₀.G t₀.PP.L → ∀ (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S) (t : SAB H (Sp R)) (_ : SABMap t t₀ ξ), ThetaNZ t.G t.PP.L := by
  first | exact @GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible | exact GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible | (intros; apply GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.exists_completeDVR_residue_galois_automorphisms : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V → CDvr V' → (∀ n : ℕ, n ≠ 0 → IsUnit (n : V)) → ∀ g : V →+* V', Function.Injective g → g.Finite → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (j : V' →+* W), CDvr W ∧ Function.Injective j ∧ (IsLocalRing.maximalIdeal V').map j ≤ IsLocalRing.maximalIdeal W ∧ (IsLocalRing.maximalIdeal V).map (j.comp g) ≤ IsLocalRing.maximalIdeal W ∧ ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (p : V →+* k) (q : W →+* K), Function.Surjective p → Function.Surjective q → (∀ x, algebraMap k K (p x) = q (j (g x))) → FiniteDimensional k K ∧ IsGalois k K ∧ ∀ τ : K ≃ₐ[k] K, ∃ σ : W ≃+* W, (∀ x, σ (j (g x)) = j (g x)) ∧ ∀ x, q (σ x) = τ (q x) := by
  first | exact @GlobalTheory.exists_cDvr_residue_galois | exact GlobalTheory.exists_cDvr_residue_galois | (intros; apply GlobalTheory.exists_cDvr_residue_galois <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.arc_abelianLocus_and_moduli_of_traitData : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b ∧ (∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧ ∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j := by
  first | exact @GlobalTheory.arc_abLocus_of_traitData | exact GlobalTheory.arc_abLocus_of_traitData | (intros; apply GlobalTheory.arc_abLocus_of_traitData <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.generic_point_mem_moduli_of_meets_abelian_locus : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty → (∃ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ) ∧ PolAt t (jK R) ∧ ξ ⁻¹' abLocus Y.t.G = abLocus t.G := by
  first | exact @GlobalTheory.LN.generic_point_of_meets_abLocus | exact GlobalTheory.LN.generic_point_of_meets_abLocus | (intros; apply GlobalTheory.LN.generic_point_of_meets_abLocus <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
theorem _root_.GlobalTheory.T.exists_polAV_generic_fibre_of_triple : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (t : SAB H (Sp R)), PolAt t (jK R) → letI := H.starRing; ∃ (A : PolAV (Sp (FractionRing R))) (oA : A.OAct (𝓞 E)) (gen : (Over.pullback (jK R)).obj t.G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) ∧ ∀ x, (Over.pullback (jK R)).map (t.act.act x) ≫ gen.hom = gen.hom ≫ oA.act x := by
  first | exact @GlobalTheory.LN.exists_polAV_of_polAt | exact GlobalTheory.LN.exists_polAV_of_polAt | (intros; apply GlobalTheory.LN.exists_polAV_of_polAt <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.sectionFrames_move_to_cover_and_ringExtension : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S Z : Scheme.{0}) (t₀ : SAB H S) (t : SAB H Z) (π : Z ⟶ S) (_ : SABMap t t₀ π) (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [CommRing R] [IsDomain R] [CharZero R] (g : R₁ →+* R) (gam : FractionRing R₁ →+* FractionRing R), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R _ (g r)) → ∀ (x₁ : Sp (FractionRing R₁) ⟶ S) (x : Sp (FractionRing R) ⟶ Z), x ≫ π = spMap gam ≫ x₁ → PolAt t₀ x₁ → ∀ (N n : ℕ) (f₁ : Fin n → LB.Sec (LPow t₀.G t₀.PP.L (N : ℤ) (Over.mk x₁))), IsFrame t₀.G t₀.PP.L N x₁ f₁ → ∃ f : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk x)), IsFrame t.G t.PP.L N x f ∧ BasisAlong t.G t.PP.L N (𝟙 _) f := by
  first | exact @GlobalTheory.FramePull.frame_pull | exact GlobalTheory.FramePull.frame_pull | (intros; apply GlobalTheory.FramePull.frame_pull <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.SplitChartsField

open GlobalTheory.UU GlobalTheory.AffineThickening GlobalTheory.TorusQuotientLift GlobalTheory.LocalWeightUnits

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {B : Scheme.{0}}
  {i : splitTorus S X ⟶ G} {q : G.left ⟶ B} [IsAffineHom q] {V : B.Opens} (hi : IsMonHom i) (hV : IsAffineOpen V)
  (h₀ : ∀ a : Γ(G.left, q ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.app V).hom c = a)
  (hinj : Function.Injective (q.app V).hom) (hS : Stable i (q ⁻¹ᵁ V))
include hi hV h₀ hS


include hinj in
theorem exists_mem_basicOpen (P : Γ(G.left, q ⁻¹ᵁ V) → Prop)
    (hP : ∀ x ∈ q ⁻¹ᵁ V, ∃ b, IsWt i _ b 0 ∧ x ∈ G.left.basicOpen b ∧ P b) {y : B} (hy : y ∈ V) :
    ∃ c : Γ(B, V), y ∈ B.basicOpen c ∧ P ((q.app V).hom c) := by
  have hG : Graded i (q ⁻¹ᵁ V) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ (hV.preimage q) (preimage_le_of_stable hS)
  let s : Set Γ(B, V) := {c | P ((q.app V).hom c)}
  let α : Γ(B, V) →+* wtZero i (q ⁻¹ᵁ V) := (q.app V).hom.codRestrict _ fun c => (h₀ _).2 ⟨c, rfl⟩
  have hα : Function.Bijective α := ⟨fun a b h => hinj (congrArg Subtype.val h), fun a => by
    obtain ⟨c, hc⟩ := (h₀ a.1).1 a.2
    exact ⟨c, Subtype.ext hc⟩⟩
  have h1 : Ideal.span ((q.app V).hom '' s) = ⊤ := by
    rw [← (hV.preimage q).self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨b, hb, hxb, hPb⟩ := hP x hx
    obtain ⟨c, rfl⟩ := (h₀ b).1 hb
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, c, hPb, rfl⟩, hxb⟩
  have h2 : (1 : wtZero i (q ⁻¹ᵁ V)) ∈ (Ideal.span s).map α := hG.mem_map _ α 1 (by
    rw [Ideal.map_span]
    exact h1.ge trivial)
  have h3 : Ideal.span s = ⊤ := by
    obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective α hα.2).1 h2
    rw [Ideal.eq_top_iff_one, ← hα.1 (e.trans (map_one α).symm)]
    exact hc
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV.self_le_iSup_basicOpen_iff.2 h3 hy)
  exact ⟨c.1, hc, c.2⟩

theorem isWt_basicOpen_iff (c : Γ(B, V)) (a : Γ(G.left, q ⁻¹ᵁ B.basicOpen c)) :
    IsWt i _ a 0 ↔ ∃ c', (q.app (B.basicOpen c)).hom c' = a := by
  have e : q ⁻¹ᵁ B.basicOpen c = G.left.basicOpen ((q.app V).hom c) := Scheme.preimage_basicOpen _ _
  have hle := B.basicOpen_le c
  have hG : Graded i (q ⁻¹ᵁ V) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ (hV.preimage q) (preimage_le_of_stable hS)
  have hS' : Stable i (q ⁻¹ᵁ B.basicOpen c) := e ▸ stable_basicOpen hS (hasWt_iff.2 ((h₀ _).2 ⟨c, rfl⟩))
  have hG' : Graded i (q ⁻¹ᵁ B.basicOpen c) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ ((hV.basicOpen c).preimage q) (preimage_le_of_stable hS')
  have hw : ∀ x, IsWt i _ ((q.app (B.basicOpen c)).hom (rs hle x)) 0 := fun x => by
    rw [app_rs]
    exact ((h₀ _).2 ⟨x, rfl⟩).res _
  obtain ⟨v, hv⟩ : IsUnit (rs hle c) := B.toRingedSpace.isUnit_res_basicOpen c
  constructor
  · intro ha
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul (hV.preimage q) (q.preimage_mono hle) _ a e
    rw [← app_rs q hle] at hy
    obtain ⟨x, hx, hx'⟩ := hG.exists_lift hG' (rs (q.preimage_mono hle)) (fun _ _ hx => hx.res _) y (χ := 0)
      (hy ▸ mul_mem (pow_mem (S := wtZero i _) (hw c) n) ha)
    obtain ⟨x, rfl⟩ := (h₀ x).1 hx
    refine ⟨(v⁻¹).val ^ n * rs hle x, ?_⟩
    rw [map_mul, app_rs, hx', hy, ← hv, ← map_pow _ v.val, ← _root_.mul_assoc, ← map_mul, ← mul_pow,
      Units.inv_mul, one_pow, map_one, _root_.one_mul]
  · rintro ⟨c', rfl⟩
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul hV hle c c' rfl
    have e' : c' = (v⁻¹).val ^ n * rs hle y := by
      rw [hy, ← hv, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul]
    have h1 : IsWt i _ (Units.map (q.app (B.basicOpen c)).hom.toMonoidHom v).val 0 := by
      have := hw c
      rwa [← hv] at this
    have h2 := h1.inv
    rw [neg_zero] at h2
    rw [e', map_mul, map_pow]
    exact mul_mem (pow_mem (S := wtZero i _) h2 n) (hw y)


omit hi h₀ hS in
include hinj in
theorem injective_basicOpen (c : Γ(B, V)) : Function.Injective (q.app (B.basicOpen c)).hom := by
  have hle := B.basicOpen_le c
  obtain ⟨v, hv⟩ : IsUnit (rs hle c) := B.toRingedSpace.isUnit_res_basicOpen c
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul hV hle c a rfl
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero (hV.preimage q) (q.preimage_mono hle) ((q.app V).hom c)
    ((q.app V).hom y) (Scheme.preimage_basicOpen _ _) (by rw [← app_rs q hle, hy, map_mul, ha, mul_zero])
  rw [← map_pow, ← map_mul, map_eq_zero_iff _ hinj] at hm
  have := congrArg (rs hle) hm
  rwa [map_mul, map_pow, map_zero, hy, ← hv, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
    Units.mul_right_eq_zero, Units.mul_right_eq_zero] at this


omit hi hV h₀ hS in
theorem main : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), GeometricallyConnected H.hom → C.Torus c i → ∃ (B : Over (Sp K)) (_ : GrpObj B) (q : H ⟶ B), IsAbelianScheme B ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsPullback i (toUnit _) q (η[B]) ∧ ∀ a, ∃ (V : B.left.Opens) (h : C.W a = q.left ⁻¹ᵁ V), IsAffineOpen V ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE V (C.W a) h.le).hom := by
  intro K _ H _ _ _ _ _ C d c i hc hT
  obtain ⟨B, q, hp, ha, V, hcov, hV⟩ := Charts.Torus.exists_proper_quotient K H C d c i hT
  obtain ⟨hm, hf, hs, hsm, hfib⟩ := GlobalTheory.LocTriv.main (Sp K) (Fin d → ℤ) H B i q hT.hom ha fun y => by
    obtain ⟨a, hy⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ y))
    obtain ⟨haff, h, hinj, h₀⟩ := hV a
    have hS := hT.stable a
    have hl := GlobalTheory.LocalWeightUnits.main K H C d c i hT a
    generalize C.W a = W at h hinj h₀ hS hl
    subst h
    rw [Scheme.Hom.appLE_eq_app] at hinj h₀
    have h₀' := fun u => hasWt_iff.symm.trans (h₀ u)
    obtain ⟨b, hb, hb₁, u, hu⟩ := exists_mem_basicOpen hT.hom haff h₀' hinj hS
      (fun b => Stable i (H.left.basicOpen b) ∧ ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, H.left.basicOpen b)ˣ,
        ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ)
      (fun x hx => (hl x hx).imp fun b hb => ⟨hasWt_iff.1 hb.1, hb.2⟩) hy
    refine ⟨B.left.basicOpen b, hb, haff.basicOpen b, isWt_basicOpen_iff hT.hom haff h₀' hS b,
      injective_basicOpen haff hinj b, ?_⟩
    rw [Scheme.preimage_basicOpen]
    exact ⟨preimage_le_of_stable hb₁, u, fun χ => hasWt_iff.1 (hu χ)⟩
  obtain ⟨g, hcomm, hq, hker⟩ :=
    GlobalTheory.grpObj_of_flat_coset_quotient (Sp K) H _ B i q hT.hom hm hf hs inferInstance hfib
  have : GeometricallyConnected (q.left ≫ B.hom) := by rwa [Over.w]
  refine ⟨B, g, q, ⟨hcomm, hsm inferInstance, hp, geometricallyConnected_of_surjective q.left B.hom⟩, hq, hf, hs, ha,
    hker, fun a => ?_⟩
  obtain ⟨haff, h, -, h₀⟩ := hV a
  exact ⟨V a, h, haff, h₀⟩

end GlobalTheory.SplitChartsField
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_torusExtensionPoint_of_integralModelPoint : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (c : Sp (OO p) ⟶ u.G.left), c ≫ u.G.hom = spMap u.j → ∃ g, u.Lev c g := by
  first | exact @GlobalTheory.IntegralGt.exists_lev | exact GlobalTheory.IntegralGt.exists_lev | (intros; apply GlobalTheory.IntegralGt.exists_lev <;> assumption)
end
