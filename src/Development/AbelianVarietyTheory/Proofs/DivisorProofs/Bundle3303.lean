module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle554
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle553
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle123
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3218
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle540
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle678
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle695
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle690
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqSpanMonomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3160
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3078
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3292
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.Principal

theorem of_isEmpty {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Type} [CommRing S]
    [IsEmpty (Sp S)] (t : SAB H (Sp S)) :
    IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  refine ⟨inferInstance, ?_, fun T _ s x _ => ?_⟩
  · have := t.semi.quasiCompact
    have := t.semi.separated
    exact GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S) t.G t.PP.L t.PP.isLB inferInstance inferInstance
      fun q => isEmptyElim q
  · have : IsEmpty (Over.mk s).left := ⟨fun p => isEmptyElim (s p)⟩
    exact Over.OverMorphism.ext ((isInitialOfIsEmpty (X := (Over.mk s).left)).hom_ext _ _)

theorem isProper_relAmple_kTriv_of_psiUnitOn : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (f : R), (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∀ tO : SAB H (Sp (Localization.Away f)), SABMap tO t (spMap (algebraMap R (Localization.Away f))) → IsProper tO.G.hom ∧ Out.RelAmple tO.G tO.PP.L ∧ Out.KTriv tO.G tO.PP.L := by
  intro E _ _ _ H R _ _ _ hR t P f hψ tf mf
  let Rf := Localization.Away f
  have hrange : Set.range (spMap (algebraMap R Rf)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range Rf f
  by_cases hf : f = 0
  · have : IsEmpty (Sp Rf) := ⟨fun z => by
      have hz : f ∉ (spMap (algebraMap R Rf) z).asIdeal := hrange.le ⟨z, rfl⟩
      exact hz ((congrArg (· ∈ (spMap (algebraMap R Rf) z).asIdeal) hf).mpr (Ideal.zero_mem _))⟩
    exact of_isEmpty tf
  obtain ⟨hab, -⟩ := GlobalTheory.Mum.abelian_and_proper_of_psiUnitOn R hR P.D P.A t.G t.semi P.U
    (PrimeSpectrum.basicOpen f) hψ
  have : IsNoetherianRing R := hR.1.1
  have : CharZero R := hR.2
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hi : Function.Injective (algebraMap R Rf) := IsLocalization.injective Rf hle
  have : IsDomain Rf := IsLocalization.isDomain_localization hle
  have : CharZero Rf := charZero_of_injective_algebraMap hi
  have habf : abLocus tf.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi mf.cart.1 z).1 (hab (hrange.le ⟨z, rfl⟩))
  have hg : GlobalTheory.LN.PolAt tf (Out.jK Rf) := GlobalTheory.PolNormal.polAt_generic_pull _ hi mf (GlobalTheory.DatUniq.polAt_of_unif P)
  have hpf : IsProper tf.G.hom := GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus E H Rf tf hg habf
  exact ⟨hpf, GlobalTheory.AbLocusPol.relAmple_kTriv_of_generic tf hpf hg⟩

end GlobalTheory.UCanon.Principal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.fibre_thetaConstants_algebraic_over_completeAlgClosed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (n : ℕ), n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → ∀ (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) → ∀ (B : PolAV (Sp (Kb W))) (b : B.A.left ⟶ A'.A.left), IsGrpPullback B.A A'.A (spMap (algebraMap (FractionRing W) (Kb W))) b → LBIso B.L (A'.L.pull b) → ∀ j : ℕ, 1 ≤ j → ∃ (C : Type) (_ : Field C) (jC : Kb W →+* C) (Ix : Type) (x : Ix → (baseOver (Sp (Kb W)) ⟶ B.A)) (v : Ix → Kb R), (∀ z : baseOver (Sp (Kb W)) ⟶ B.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧ (∀ i, x i ^ ((n ^ j) ^ 2) = 1) ∧ IsThetaPt B (n ^ j) (fun i => (Over.homMk (spMap jC) (Category.comp_id _) : Over.mk (spMap jC) ⟶ baseOver (Sp (Kb W))) ≫ x i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (jC (e₀ (v i)))) := by
  first | exact @GlobalTheory.Mum.FibreTheta.theta_consts_algebraic | exact GlobalTheory.Mum.FibreTheta.theta_consts_algebraic | (intros; apply GlobalTheory.Mum.FibreTheta.theta_consts_algebraic <;> assumption)
end

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

namespace GlobalTheory.Poinc.TraitPow

theorem exists_equiv : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (h : T.V →+* R) (hK : FractionRing T.V →+* FractionRing R), IsLocalHom h → (∀ a, hK (algebraMap T.V _ a) = algebraMap R _ (h a)) → ∀ c pr, SharpBy F W A' (spMap hK ≫ T.y) c pr → ∃ e : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W T.β (e y) ∧ Associated r (h T.ϖ ^ (qW W T.β (e y)).toNat)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ y, MatRel W a b (e y) (e (m y)) := by
  intro g n o _ ζ F W hW T R _ _ _ hB hdvr G' _ _ hG' D' A' U' h hK hl hhK c pr hS
  obtain ⟨G, _, _, D, A, U, α, α₂, ε, hG, hα, hαsq, ⟨w', hw'⟩, hτ⟩ :=
    GlobalTheory.Poinc.TraitPull.exists_pull_unif g n o ζ F T R hB hdvr h hK hl hhK
  obtain ⟨⟨φc, φ₂, hc, hsq, ⟨w, hw⟩, -⟩, hpr, huniv, hL⟩ := hS
  obtain ⟨i, hi, hii⟩ := grpPullback_iso hc hα
  have hpt : ∀ a, (pr a).left ≫ φc = (pr a ≫ i.hom).left ≫ α := fun a => by
    rw [Over.comp_left, Category.assoc (pr a).left, hii]
  have hΛ : (abelian₂ A.A A.L).IsLB := LB.isLB_linComb A.isLB _ _
  have i₁ := iso_linComb ((isGen_iff w).1 hw) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have i₂ := iso_linComb ((isGen_iff w').1 hw') (K := Fin 8 × Fin 8)
    (fun ab => (lift (pr ab.1 ≫ i.hom) (pr ab.2 ≫ i.hom)).left) (fun ab => W ab.1 ab.2)
  have hm : (fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left ≫ φ₂) =
      fun ab => (lift (pr ab.1 ≫ i.hom) (pr ab.2 ≫ i.hom)).left ≫ α₂ :=
    funext fun ab => GlobalTheory.Poinc.SharpIdent.lift_comp_square hsq hαsq _ _ _ _ (hpt ab.1) (hpt ab.2)
  rw [hm] at i₁
  have hL' := LBIso.trans A'.isLB (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb hΛ _ _) hL
    (LBIso.trans (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb F.univ.isLB _ _) (LB.isLB_linComb hΛ _ _) i₁ i₂.symm)
  have hu' : ∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)),
      ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a ≫ i.hom = y a := by
    intro T' y
    obtain ⟨z, hz, hz'⟩ := huniv T' fun a => y a ≫ i.inv
    refine ⟨z, fun a => ?_, fun z' h' => hz' z' fun a => ?_⟩
    · rw [← Category.assoc, hz a, Category.assoc, i.inv_hom_id, Category.comp_id]
    · rw [← h' a, Category.assoc z', Category.assoc (pr a), i.hom_inv_id, Category.comp_id]
  have hnn : ∀ a, 0 ≤ T.β a a := fun a => by
    by_cases ha : a = 0
    · simp [ha]
    · exact (GlobalTheory.Poinc.Trait.beta_pos g n o ζ F T a ha).le
  obtain ⟨e, he₁, he₂⟩ := GlobalTheory.T.eighthPower_uniformised_monomialPeriods_latticeIso R hB hdvr G hG D A U G' hG' D' A' U' W hW (fun a => pr a ≫ i.hom)
    (fun a => by have := hpr a; infer_instance) hu' hL' (h T.ϖ)
    (T.β.compl₁₂ (ε : D.toPre.X →+ T.D.toPre.X).toIntLinearMap (ε : D.toPre.X →+ T.D.toPre.X).toIntLinearMap)
    (fun a b => T.symm (ε a) (ε b)) (fun a => hnn (ε a)) hτ
  refine ⟨e.trans (AddEquiv.piCongrRight fun _ => ε), he₁, ?_⟩
  intro a b f f₁ m hf hM hgen hE y v
  have hM' : MatEnd (fun a => pr a ≫ i.hom) a b f₁ := by
    refine ⟨hM.1, fun u => ?_⟩
    rw [← Category.assoc, hM.2 u]
    split_ifs
    · rfl
    · exact MonObj.one_comp _
  have key := congrArg ε (he₂ a b f f₁ m hf hM' hgen hE y v)

  rw [apply_ite ε, map_sum, map_sum, map_zero] at key
  simp only [map_zsmul] at key
  exact key

end GlobalTheory.Poinc.TraitPow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.abelian_proper_uniformised_where_trivialisations_generate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → (W : Set (Sp R)) ⊆ abLocus G ∧ IsProper (G.hom ∣_ W) := by
  first | exact @GlobalTheory.Mum.abelian_and_proper_of_psiUnitOn | exact GlobalTheory.Mum.abelian_and_proper_of_psiUnitOn | (intros; apply GlobalTheory.Mum.abelian_and_proper_of_psiUnitOn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_even_translate_order_two_torus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) ∧ EvenOn P₁ := by
  first | exact @GlobalTheory.Mum.exists_even_translate | exact GlobalTheory.Mum.exists_even_translate | (intros; apply GlobalTheory.Mum.exists_even_translate <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finiteExtension_uniformisation_of_trait_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'), IsGrpPullback G' G (spMap φ) β → LBIso U'.LG.L (P.L.L.pull β) → Nonempty (IsPullDeg φ D.toPre D'.toPre) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β₁ : G₁.left ⟶ G.left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β₁ ∧ LBIso U₁.LG.L (P.L.L.pull β₁) := by
  first | exact @GlobalTheory.Mum.Ident.exists_finExt_unif | exact GlobalTheory.Mum.Ident.exists_finExt_unif | (intros; apply GlobalTheory.Mum.Ident.exists_finExt_unif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisedGroup_closedFibre_finset_in_affineOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R) → ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  first | exact @GlobalTheory.Mum.finite_closedFibre_subset_isAffineOpen | exact GlobalTheory.Mum.finite_closedFibre_subset_isAffineOpen | (intros; apply GlobalTheory.Mum.finite_closedFibre_subset_isAffineOpen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_section_ratios_generate_mod_maximal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  first | exact @GlobalTheory.Mum.exists_ratio_gen_mod | exact GlobalTheory.Mum.exists_ratio_gen_mod | (intros; apply GlobalTheory.Mum.exists_ratio_gen_mod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.MonoAb

theorem exists_pos_of_ne_zero {X : Type} [AddCommGroup X] (d : LinearMap.BilinForm ℤ X)
    (hs : ∀ a b, d a b = d b a) (hn : ∀ a, 0 ≤ d a a) (h : d ≠ 0) : ∃ y, 0 < d y y := by
  by_contra hc
  push_neg at hc
  apply h
  ext a b
  have h1 := hc (a + b)
  have h2 : d a a = 0 := le_antisymm (hc a) (hn a)
  have h3 : d b b = 0 := le_antisymm (hc b) (hn b)
  have h4 := hn (a + b)
  have h5 : d (a + b) (a + b) = 0 := le_antisymm h1 h4
  simp only [map_add (f := _), LinearMap.add_apply, h2, h3, hs b a] at h5
  simp only [LinearMap.zero_apply]
  omega

end GlobalTheory.Mum.MonoAb

theorem GlobalTheory.Mum.abLocus_iff_of_monomialTau : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsMumPol Q G P → ∀ (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k, t k ∈ maximalIdeal R ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → (∀ k, δ k ≠ 0) → Q.IsMonomialTau t δ → ∀ p : Sp R, p ∈ abLocus G ↔ ∏ k, t k ∉ p.asIdeal := by
  intro R _ _ _ hR Q _ G _ _ P hM m t δ ht hsymm hnn hdef hne hmono p
  obtain ⟨R', _, _, _, ρ, r, D, e, hR', hinj, hfin, -, hr, href, hmon⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised R Q m t δ hR hmono (fun k => (ht k).1) (fun k => (ht k).2)
      (fun k a b => hsymm k a b) hnn hdef
  obtain ⟨-, -, hG, -, hU⟩ := hM
  obtain ⟨G', _, _, π, -, A, U, hpb, -, -⟩ := hU R' ρ hR' hinj hfin D e href
  have hG' : IsSemiAbelian G' := GlobalTheory.SiegLoc.TraitOrd.isSemiAbelian_of_isGrpPullback hpb hG
  haveI : IsNoetherianRing R' := hR'.1

  obtain ⟨q, hq⟩ : ∃ q : Sp R', spMap ρ q = p := by
    letI := ρ.toAlgebra
    haveI : p.asIdeal.IsPrime := p.isPrime
    haveI : Module.Finite R R' := hfin
    obtain ⟨Q', -, hQ', hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal R') (by
      intro x hx
      have : ρ x = 0 := hx
      rw [show x = 0 from hinj (this.trans (map_zero ρ).symm)]
      exact p.asIdeal.zero_mem)
    exact ⟨⟨Q', hQ'⟩, PrimeSpectrum.ext hc⟩
  subst hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  rw [abLocus_pullback abLocusOne hG hpb.1 q]
  have key : ∏ k, t k ∈ (spMap ρ q).asIdeal ↔ ∏ k, r k ∈ q.asIdeal := by
    show ρ (∏ k, t k) ∈ q.asIdeal ↔ _
    rw [map_prod, show (∏ k, ρ (t k)) = (∏ k, r k) ^ 2 by rw [← Finset.prod_pow]; simp only [hr]]
    exact ⟨fun h => q.isPrime.mem_of_pow_mem 2 h, fun h => Ideal.pow_mem_of_mem _ h 2 (by norm_num)⟩
  rw [key]
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have ho : IsOpen (abLocus G') := GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian G' hG'
  constructor
  · intro hab hmem
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    obtain ⟨y, hy⟩ := GlobalTheory.Mum.MonoAb.exists_pos_of_ne_zero (δ k) (hsymm k) (hnn k) (hne k)
    obtain ⟨u, n, hn, hc⟩ := hmon (e.symm y)
    have hnk : 0 < n k := by
      have := hn k
      simp [pull] at this
      omega
    have hUo := GlobalTheory.PsiAbelian.psiUnitOn_abLocus h1 h2 h3 h4 h5 R' _ (GlobalTheory.SiegChart.isAdmissibleBase_of_completeNormalLocalCharZero hR') D A G' hG' U ho
      (e.symm y)
    refine GlobalTheory.PsiCoordLocal.not_mem_of_coord ho hab hUo hc ?_
    refine Ideal.mul_mem_left _ _ ?_
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
      (Ideal.pow_mem_of_mem _ hk _ hnk)
  · intro hnot
    let W : (Sp R').Opens := ⟨{x | ∏ k, r k ∉ x.asIdeal}, (PrimeSpectrum.basicOpen (∏ k, r k)).isOpen⟩
    exact GlobalTheory.Mum.UnifFibre.fibres_abelian_of_psiUnitOn R' ⟨admissibleBase_of_completeNormalLocalCharZero hR', hR'.2.2.2⟩ D A G' hG' U W
      (fun y => hmon.psiUnitOn y fun x hx => hx) hnot
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem Taut.exists_ext_normBl : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∃ ξ : Sp C.R ⟶ S, y ≫ j = jK C.R ≫ ξ := by
  intro g _ φ hφ _ n hn _ F Z z i OZ d S π j _ BD hM hB C G₁ _ y α₁ hC
  obtain ⟨hsa, hab, hgen, hmum, hy⟩ := hC
  obtain ⟨J, -, -, hval, hbl, -, -, hji, hpre, -, -⟩ := hB
  obtain ⟨hreg, hchar, -, -, hpar, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, hrk, hcone, hdef, ht⟩ := Taut.monomial_chart g n φ (by omega) C
  haveI : IsOpenImmersion i := hM.isThetaCompact.1.2.2.1
  haveI : IsCommMonObj G₁ := hsa.comm
  haveI : IsNoetherianRing C.R := C.compl.1
  haveI : IsIntegrallyClosed C.R := hmum.1.2.1
  obtain ⟨a, ha⟩ := GlobalTheory.MinExt.exists_ext_of_minAt5 g n F Z z i OZ hM C.R G₁ hsa y α₁ hgen C.b hy
  have hon : IsPolFanOn id φ C.Q.X := hφ C.Q.X hrk
  have he : ∀ k, ∃ e : ℕ, (e : ℝ) = d * φ.evalZ ((n : ℤ) • C.δ k) := by
    intro k
    have hmem : (n : ℤ) • C.δ k ∈ balForms (id : ℤ → ℤ) C.Q.X := Submodule.smul_mem _ _ (hcone.mem k)
    have hnn : ∀ w, 0 ≤ ((n : ℤ) • C.δ k) w w := fun w => by
      simpa using mul_nonneg (Int.natCast_nonneg n) (hcone.nonneg k w)
    obtain ⟨c, hc⟩ := hon.integral _ hmem hnn
    have hc0 : 0 ≤ c := by
      have hne : (n : ℤ) • C.δ k ≠ 0 := by
        refine fun h => hcone.basis.linearIndependent.ne_zero k (Subtype.ext ?_)
        exact (smul_eq_zero.1 h).resolve_left (by omega)
      have := hon.pos _ hmem hnn hne
      rw [hc] at this
      exact_mod_cast this.le
    lift c to ℕ using hc0
    exact ⟨d * c, by rw [hc]; push_cast; rfl⟩
  choose e he using he
  have hJ := GlobalTheory.ChartIdeal.idlAlong_eq_span_monomial g n F Z i φ hφ d J hval C.R C.compl.2.1 C.b a C.Q G₁ y α₁ hsa hgen ha
    hmum C.m C.t C.δ e hpar hab hcone hdef hmono he
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.NormBlLift.lift_normBl g n F Z S i π j J hbl hji hpre C.R a y ha _
    (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)) hJ
  refine ⟨ξ, ?_⟩
  have hπ : (jK C.R ≫ ξ) ≫ π = y ≫ i := by rw [Category.assoc, hξ, ha]
  have hr : Set.range (jK C.R ≫ ξ) ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    rw [← hpre]
    exact ⟨y p, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hπ]⟩
  have hl := IsOpenImmersion.lift_fac j (jK C.R ≫ ξ) hr
  have : IsOpenImmersion.lift j (jK C.R ≫ ξ) hr = y := by
    rw [← cancel_mono i, ← hπ, ← hji, ← Category.assoc, hl]
  rw [← this, hl]

end GlobalTheory.TChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem canon_isBiRig : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → IsBiRig G P := by
  intro R _ _ _ hCN Q G _ _ P hC
  obtain ⟨hP, D', F, A', G', i1, i2, U', oA, oG, inc, pr, hsemi, hlin, hinc, hpr, hip, hpi, hiso⟩ := hC
  have hL : U'.LG.L.IsLB := U'.LG.isLB
  have hros := GlobalTheory.T.linearUniformisation_rosatiAdjoint_star R hCN D' F.O F.o A' G' U' oA oG hsemi hlin
  have hie : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have hf : IsMonHom (inc ≫ oG.act F.f) := by have := oG.hom F.f; infer_instance
  obtain ⟨h1, h2⟩ := GlobalTheory.T.mumfordBundle_pullback_homPair_trivial_axes (Sp R) G G' U'.LG.L hL inc (inc ≫ oG.act F.f) hinc hf P hP hiso
  exact ⟨hP, h1, h2, GlobalTheory.T.mumfordBundle_pullback_inclusion_factor_symmetric (Sp R) G G' U'.LG.L hL F.O oG hros F.e F.f inc hinc hie F.alg.2.1 P hP hiso⟩

end GlobalTheory.Mum
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim : ∀ (K : Type) [Field K] (A B : AbVar K), Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧ Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  first | (exact @GlobalTheory.AV.AbVar.hom_finite_free_rank_le) | (exact GlobalTheory.AV.AbVar.hom_finite_free_rank_le) | (intros; apply GlobalTheory.AV.AbVar.hom_finite_free_rank_le  <;> assumption)
end
