module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle633
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle716
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3297
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3068
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3298
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.translate_integral_thetaExpansion_by_twoTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ (σ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), (∀ e : ℕ, U.ExpandsAt e 1 σ f) → ∃ (σ₂ : H0 U₂.LG.L 1) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen ∧ (∀ e : ℕ, U₂.ExpandsAt e 1 σ₂ f₂) ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) ∧ ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  first | exact @GlobalTheory.MumCmp.translate_expansion_twist | exact GlobalTheory.MumCmp.translate_expansion_twist | (intros; apply GlobalTheory.MumCmp.translate_expansion_twist <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

theorem weilIs_heckeSub_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) 1 := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_commutatorPairing_value_heckePoints p D R b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂
  have hQ : (lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hA2 : IsAbelianScheme (G2 o.A) :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have h1 : u = 1 := by
    refine GlobalTheory.T.scheme_rootOfUnity_eq_one_of_geometric_points R S s k u (b.unit k hk)
      (GlobalTheory.T.commutatorPairing_heckePoints_pow_eq_one p D R b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂ u hu) ?_
    intro K _ _ x β hx
    have hp := GlobalTheory.CommPairing.weilIs_pull (A := G2 o.A) GlobalTheory.globalFns_holds hA2 hQ (toUnit (Over.mk x)) hu
    exact GlobalTheory.T.weilPairing_heckePoints_geometric_eq_one p D R b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂ K x β hx _ hp
  subst h1
  exact hu

end GlobalTheory.UPel.HT.Hecke
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

theorem _root_.GlobalTheory.T.heckeSections_isotropic_commutatorPairing_power : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 g₂) 1 := by
  first | (exact @GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_one) | (exact GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_one) | (intros; apply GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.rosatiAdjoint_genericFibre_of_acts_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g → ActsAs U.toUnifPre (o.onB.act (star a)) (fun χ => star (star a) • χ) g' → RosatiAdj A.A A.L (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom) (U.gen.inv ≫ (Over.pullback (jK R)).map g' ≫ U.gen.hom) := by
  first | exact @GlobalTheory.Mum.RosGeneric.rosatiAdj_generic_of_actsAs | exact GlobalTheory.Mum.RosGeneric.rosatiAdj_generic_of_actsAs | (intros; apply GlobalTheory.Mum.RosGeneric.rosatiAdj_generic_of_actsAs <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_oAct_oLinear_of_actsAs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oG : RingAct G O), (∀ a, ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) (oG.act a)) → ∃ oA : A.OAct O, U.toUnifPre.OLinear O o oA oG := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oG hgA
  have hgen : IsMonHom U.gen.hom := U.gen_hom
  have hgeni : IsMonHom U.gen.inv := by infer_instance
  have hg := oG.hom
  have one := oG.map_one
  have mul := oG.map_mul
  have add := oG.map_add
  let F := Over.pullback (jK R)
  let fA : O → (A.A ⟶ A.A) := fun a => U.gen.inv ≫ F.map (oG.act a) ≫ U.gen.hom
  let oA : A.OAct O :=
    { act := fA
      hom := fun a => by haveI := hg a; dsimp [fA]; infer_instance
      map_one := by simp [fA, F, one]
      map_mul := fun a b => by simp [fA, F, mul]
      map_add := fun a b => by
        haveI := hg a; haveI := hg b
        simp only [fA, F, add, pull_padd]
        rw [padd_comp_hom, padd, padd, comp_lift_assoc]
      rosati := fun a => GlobalTheory.Mum.RosGeneric.rosatiAdj_generic_of_actsAs R hR D A G hG U O o a (oG.act a)
        (oG.act (star a)) (hg a) (hg (star a)) (hgA a) (hgA (star a)) }
  refine ⟨oA, ⟨fun a => ?_, fun e a => (hgA a e).1, fun e a => (hgA a e).2⟩⟩
  simp [oA, fA, F]
end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

theorem exists_geomPt_closedPoint (V : Type) [CommRing V] [IsLocalRing V] (X : Scheme.{0}) (y : Sp V ⟶ X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : X.residueField (y (IsLocalRing.closedPoint V)) →+* k)
      (π : Sp k ⟶ Sp V), π ≫ y = spMap σ ≫ X.fromSpecResidueField (y (IsLocalRing.closedPoint V)) ∧
      ∀ q, π q = IsLocalRing.closedPoint V := by
  let k := AlgebraicClosure (IsLocalRing.ResidueField V)
  let g₀ : V →+* k := (algebraMap (IsLocalRing.ResidueField V) k).comp (IsLocalRing.residue V)
  haveI : IsLocalHom g₀ := RingHom.isLocalHom_comp _ _
  have hπ : ∀ q, spMap g₀ q = IsLocalRing.closedPoint V := by
    intro q
    have hq : q = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [hq]
    exact IsLocalRing.comap_closedPoint g₀
  obtain ⟨⟨x, σ⟩, h⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective (spMap g₀ ≫ y)
  rw [Scheme.SpecToEquivOfField_symm_apply] at h
  have hx : x = y (IsLocalRing.closedPoint V) := by
    let q : Sp k := IsLocalRing.closedPoint k
    have e : (Spec.map σ ≫ X.fromSpecResidueField x) q = (spMap g₀ ≫ y) q := congrArg (fun g : Sp k ⟶ X => g q) h
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hπ, Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hx
  exact ⟨k, inferInstance, inferInstance, σ.hom, spMap g₀, h.symm, hπ⟩

theorem exists_isogTarget_of_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ u : M.X, ∀ z ∈ {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}, ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : M.X.residueField u →+* k) (ζ : Sp k ⟶ M.X), (∀ q, ζ q = z) ∧ CorrQF.IsogTarget M c (spMap σ ≫ M.X.fromSpecResidueField u) ζ := by
  rintro p _ D R _ b N hN hNp c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ u z ⟨V, K, _, _, _, _, _, _, y, z', x, hxy, hxz, rfl, rfl⟩
  let eK : K →+* FractionRing V := (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).toRingEquiv.toRingHom
  have heK : eK.comp (algebraMap V K) = algebraMap V (FractionRing V) := by
    ext a; exact (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).commutes a
  let kF : Sp (FractionRing V) ⟶ Sp V := spMap (algebraMap V (FractionRing V))
  let x' : Sp (FractionRing V) ⟶ Y₀ := spMap eK ≫ x
  have hk : kF = spMap eK ≫ spMap (algebraMap V K) := by
    simp only [kF, spMap, ← heK, CommRingCat.ofHom_comp, Spec.map_comp]
  have hxy' : kF ≫ y = x' ≫ s₀ := by rw [hk, Category.assoc, hxy]; rfl
  have hxz' : kF ≫ z' = x' ≫ t₀ := by rw [hk, Category.assoc, hxz]; rfl
  obtain ⟨o, ⟨my⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp V) M.s y M.univ
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp (FractionRing V)) (y ≫ M.s) kF o
  have m1 : ObjMap oK M.univ (x' ≫ s₀) := hxy' ▸ GlobalTheory.UPel.HT.ObjMapComp.comp mK my
  obtain ⟨n₀, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m1 ms₀
  have key : ∀ σ : Sp (FractionRing V) ⟶ Sp R, x' ≫ (s₀ ≫ M.s) = σ →
      ∃ o' : Obj b N σ, Nonempty (ObjMap o' o₀' x') := by
    rintro σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) x' o₀'
  obtain ⟨oK', ⟨n₀'⟩⟩ := key (kF ≫ (y ≫ M.s)) (by rw [← Category.assoc, ← hxy', Category.assoc])
  obtain ⟨ψK, hψK, -⟩ := ValExt.isPIsog_pull p D R b N c Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) (kF ≫ (y ≫ M.s)) x'
    o₀ o₀' oK oK' n₀ n₀' ψ₀ hψ
  obtain ⟨o', m', ψ, hψV, -⟩ := IsogDVR.exists_isPIsog_extend_dvr p D R b N hN hNp c V (y ≫ M.s) o oK oK' mK ψK hψK
  obtain ⟨z, ⟨hz, ⟨mz⟩⟩, -⟩ := M.rep (Sp V) (y ≫ M.s) o'
  obtain ⟨f, -, huniq⟩ := M.rep (Sp (FractionRing V)) (kF ≫ (y ≫ M.s)) oK'
  have e1 := huniq (kF ≫ z) ⟨by rw [Category.assoc, hz], ⟨GlobalTheory.UPel.HT.ObjMapComp.comp m' mz⟩⟩
  have e2 := huniq (x' ≫ t₀) ⟨by rw [Category.assoc, ← hst, ← Category.assoc, ← hxy', Category.assoc],
    ⟨GlobalTheory.UPel.HT.ObjMapComp.comp n₀' mt₀⟩⟩
  haveI : IsSeparated M.s := by
    obtain ⟨n, i, hi, -, e⟩ := M.qproj
    have : IsSeparated (PSpace.str R n) := by
      unfold PSpace.str
      infer_instance
    rw [← e]
    infer_instance
  haveI : M.X.IsSeparated := ⟨by rw [← terminal.comp_from M.s]; infer_instance⟩
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsDominant kF := inferInstanceAs (IsDominant (spMap (algebraMap V (FractionRing V))))
  have hzz : z = z' := ext_of_isDominant kF (by rw [e1, ← e2, hxz'])
  subst hzz
  obtain ⟨k, _, _, σ, π, hπ, hπc⟩ := exists_geomPt_closedPoint V M.X y
  refine ⟨k, inferInstance, inferInstance, σ, π ≫ z, fun q => by rw [Scheme.Hom.comp_apply, hπc], ?_⟩
  rw [← hπ]
  obtain ⟨o₁, ⟨n⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp k) (y ≫ M.s) π o
  obtain ⟨o₁', ⟨n'⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp k) (y ≫ M.s) π o'
  obtain ⟨ψ₁, hψ₁, -⟩ := ValExt.isPIsog_pull p D R b N c (Sp V) (Sp k) (y ≫ M.s) (π ≫ (y ≫ M.s)) π
    o o' o₁ o₁' n n' ψ hψV
  refine ⟨by rw [Category.assoc, Category.assoc, hz], ?_⟩
  rw [Category.assoc]
  exact ⟨o₁, o₁', ψ₁, ⟨GlobalTheory.UPel.HT.ObjMapComp.comp n my⟩, ⟨GlobalTheory.UPel.HT.ObjMapComp.comp n' mz⟩, hψ₁⟩

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem nsmul_eq_nsmul_of_dvd {M : Type} [AddCommGroup M] {n m : ℕ} (h : n ∣ m) (e : M) : ∃ e', m • e = n • e' := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k • e, mul_smul n k e⟩

theorem Cois.comp_isometry {y : D.La →ₗ[𝓞 E] X} {n : ℕ} (hy : Cois D y n) (G : D.La ≃ₗ[𝓞 E] D.La)
    (hG : ∀ a b, D.EF (G a) (G b) = D.EF a b) : Cois D (y.comp G.toLinearMap) n := by
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · obtain ⟨a, e, he⟩ := hy.1 x
    exact ⟨G.symm a, e, by simpa using he⟩
  · have := hy.2 (G a) fun b hb => by
      have h1 := ha (G.symm b) (by simpa using hb)
      rwa [← hG a (G.symm b), G.apply_symm_apply] at h1
    exact this

theorem ker_iff_of_congr {f f' : D.La →ₗ[𝓞 E] X} {n : ℕ} (h : ∀ a, ∃ e, f' a = f a + n • e) (a : D.La) :
    (∃ e, f a = n • e) ↔ ∃ e, f' a = n • e := by
  obtain ⟨e₀, he₀⟩ := h a
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e + e₀, by rw [he₀, he, smul_add]⟩
  · rintro ⟨e, he⟩
    exact ⟨e - e₀, by rw [smul_sub, ← he, he₀]; abel⟩

theorem KerIs.of_dvd {f : D.La →ₗ[𝓞 E] X} {Z : Submodule (𝓞 E) D.La} {n n' : ℕ} (hk : KerIs D f Z n')
    (hon : ∀ x, ∃ a e, f a = x + n' • e) (hd : n ∣ n') : KerIs D f Z n := by
  intro a
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨c, e', hc⟩ := hon x
    have h1 : ∃ e, f (a - n • c) = n' • e := ⟨-(n • e'), by
      rw [map_sub, map_nsmul, hx, hc, smul_add, smul_neg, smul_comm n' n e']; abel⟩
    obtain ⟨b, hb, e, he⟩ := (hk _).1 h1
    obtain ⟨e'', he''⟩ := nsmul_eq_nsmul_of_dvd hd e
    refine ⟨b, hb, c + e'', ?_⟩
    rw [sub_eq_iff_eq_add] at he
    rw [he, smul_add, ← he'']; abel
  · rintro ⟨b, hb, e, rfl⟩
    obtain ⟨e', he'⟩ := (hk b).2 ⟨b, hb, 0, by simp⟩
    obtain ⟨e'', he''⟩ := nsmul_eq_nsmul_of_dvd hd e'
    exact ⟨e'' + f e, by rw [map_add (f := _), map_nsmul, he', he'', smul_add]⟩

theorem exists_step [Module.Free ℤ X] [Module.Finite ℤ X] {Z FinalForm : Submodule (𝓞 E) D.La} (hop : IsOpp D Z FinalForm)
    (hrk : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (f : D.La →ₗ[𝓞 E] X) {n N' : ℕ} (hn : 0 < n)
    (hd : N' ∣ n) (hc : Cois D f n) (hk : KerIs D f Z N') :
    ∃ h : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (h a) (h b) = D.EF a b) ∧ (∀ a, ∃ e, h a = a + N' • e) ∧
      KerIs D (f.comp h.toLinearMap) Z n := by
  obtain ⟨Z'', hop'', hon⟩ := GlobalTheory.T.exists_opposite_transversal_isotropic D f n hn hc Z FinalForm hop hrk
  obtain ⟨h, hi, hN, hk'⟩ := GlobalTheory.T.exists_isometry_kernel_coisotropic_mod D f n N' hn hd hc Z Z'' hop'' hrk hk hon
  exact ⟨h, hi, hN, hk'⟩

def levelSeq (N j : ℕ) : ℕ := N * (j + 1).factorial

theorem levelSeq_pos {N : ℕ} (hN : 0 < N) (j : ℕ) : 0 < levelSeq N j := Nat.mul_pos hN (Nat.factorial_pos _)

theorem levelSeq_succ (N j : ℕ) : levelSeq N (j + 1) = levelSeq N j * (j + 2) := by
  unfold levelSeq; rw [Nat.factorial_succ (j + 1)]; ring

theorem levelSeq_dvd (N : ℕ) {i j : ℕ} (h : i ≤ j) : levelSeq N i ∣ levelSeq N j :=
  Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial (by omega))

theorem dvd_levelSeq (N : ℕ) {n : ℕ} (hn : 0 < n) : n ∣ levelSeq N n :=
  Dvd.dvd.mul_left (Nat.dvd_factorial hn (Nat.le_succ n)) N

theorem levelSeq_zero (N : ℕ) : levelSeq N 0 = N := by simp [levelSeq]

def GoodAt (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (Z : Submodule (𝓞 E) D.La) (N n : ℕ) (G : D.La ≃ₗ[𝓞 E] D.La) : Prop :=
  (∀ a b, D.EF (G a) (G b) = D.EF a b) ∧ (∀ a, ∃ e, G a = a + N • e) ∧ KerIs D (y.comp G.toLinearMap) Z n

def iterSeq {α : Type} (x₀ : α) (f : ℕ → α → α) (j : ℕ) : α := Nat.rec (motive := fun _ => α) x₀ f j

theorem exists_compatible_isometries : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : ℕ → D.La →ₗ[𝓞 E] X), (∀ n, 0 < n → Cois D (y n) n) →
    (∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, y (n * m) a = y n a + n • e) →
    Module.finrank (𝓞 E) X ≤ min D.p D.q → ∀ N, 0 < N →
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X ∧
      ∃ g : ℕ → D.La ≃ₗ[𝓞 E] D.La, (∀ n a b, D.EF (g n a) (g n b) = D.EF a b) ∧
        (∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, g (n * m) a = g n a + n • e) ∧ (∀ n a, ∃ e, g n a = a + N • e) ∧
        ∀ n, 0 < n → ∀ a, (∃ e, y n (g n a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ _ _ y hc hy hr N hN
  classical
  obtain ⟨Z₀, hZ₀, hrk₀⟩ := GlobalTheory.T.exists_isotropicSaturatedSubmodule_of_finrank_le D _ hr
  obtain ⟨Z₀', hop₀⟩ := GlobalTheory.T.exists_oppositeIsotropicPair D Z₀ hZ₀
  obtain ⟨Z₁', hop₁, hon₁⟩ := GlobalTheory.T.exists_opposite_transversal_isotropic D (y N) N hN (hc N hN) Z₀ Z₀' hop₀ hrk₀
  obtain ⟨g₀, hg₀, -, hk₀⟩ := GlobalTheory.T.exists_isometry_kernel_coisotropic_mod D (y N) N 1 hN (one_dvd N) (hc N hN) Z₀ Z₁' hop₁ hrk₀
    (fun a => ⟨fun _ => ⟨0, zero_mem _, a, by simp⟩, fun _ => ⟨y N a, by simp⟩⟩) hon₁
  set Z := Z₀.map (g₀ : D.La →ₗ[𝓞 E] D.La) with hZdef
  have memZ : ∀ x, x ∈ Z ↔ g₀.symm x ∈ Z₀ := fun x => Submodule.mem_map_equiv Z₀
  have memP : ∀ x, x ∈ perp D Z ↔ g₀.symm x ∈ perp D Z₀ := by
    intro x
    rw [mem_perp, mem_perp]
    constructor
    · intro hx z hz
      have := hx (g₀ z) ((memZ _).2 (by simpa using hz))
      rwa [← hg₀ (g₀.symm x) z, g₀.apply_symm_apply]
    · intro hx z hz
      have := hx _ ((memZ z).1 hz)
      rwa [← hg₀ (g₀.symm x) (g₀.symm z), g₀.apply_symm_apply, g₀.apply_symm_apply] at this
  have hZ : IsIsoSat D Z := by
    refine ⟨fun z hz => (memP z).2 (hZ₀.1 ((memZ z).1 hz)), fun n x hn hx => (memZ x).2 ?_⟩
    have := (memZ _).1 hx
    rw [map_nsmul] at this
    exact hZ₀.2 n _ hn this
  have hrk : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X := by
    rw [← hrk₀]; exact (g₀.submoduleMap Z₀).finrank_eq.symm
  obtain ⟨FinalForm, hop⟩ := GlobalTheory.T.exists_oppositeIsotropicPair D Z hZ
  have hbase : KerIs D (y N) Z N := by
    intro a
    have h1 := hk₀ (g₀.symm a)
    rw [g₀.apply_symm_apply] at h1
    rw [h1]
    constructor
    · rintro ⟨b, hb, e, he⟩
      refine ⟨g₀ b, (memP _).2 (by rwa [g₀.symm_apply_apply]), g₀ e, ?_⟩
      conv_lhs => rw [← g₀.apply_symm_apply a, he]
      rw [map_add (f := _), map_nsmul]
    · rintro ⟨b, hb, e, rfl⟩
      exact ⟨g₀.symm b, (memP b).1 hb, g₀.symm e, by rw [map_add (f := _), map_nsmul]⟩
  have hstep : ∀ j (G : D.La ≃ₗ[𝓞 E] D.La), GoodAt D (y (levelSeq N j)) Z N (levelSeq N j) G →
      ∃ G' : D.La ≃ₗ[𝓞 E] D.La, GoodAt D (y (levelSeq N (j + 1))) Z N (levelSeq N (j + 1)) G' ∧
        ∀ a, ∃ e, G' a = G a + levelSeq N j • e := by
    rintro j G ⟨hGi, hGN, hGk⟩
    have hcong : ∀ a, ∃ e, ((y (levelSeq N (j + 1))).comp G.toLinearMap) a =
        ((y (levelSeq N j)).comp G.toLinearMap) a + levelSeq N j • e := by
      intro a
      rw [levelSeq_succ]
      exact hy (levelSeq N j) (j + 2) (levelSeq_pos hN j) (by omega) (G a)
    have hk : KerIs D ((y (levelSeq N (j + 1))).comp G.toLinearMap) Z (levelSeq N j) := fun a =>
      (ker_iff_of_congr hcong a).symm.trans (hGk a)
    obtain ⟨h, hi, hN', hk'⟩ := exists_step hop hrk ((y (levelSeq N (j + 1))).comp G.toLinearMap)
      (levelSeq_pos hN (j + 1)) (levelSeq_dvd N (Nat.le_succ j)) ((hc _ (levelSeq_pos hN _)).comp_isometry G hGi) hk
    refine ⟨h.trans G, ⟨fun a b => ?_, fun a => ?_, fun a => hk' a⟩, fun a => ?_⟩
    · simp only [LinearEquiv.trans_apply]; rw [hGi, hi]
    · obtain ⟨e, he⟩ := hN' a
      obtain ⟨e₁, he₁⟩ := hGN a
      obtain ⟨e₂, he₂⟩ := nsmul_eq_nsmul_of_dvd (Dvd.intro _ rfl : N ∣ levelSeq N j) (G e)
      exact ⟨e₁ + e₂, by rw [LinearEquiv.trans_apply, he, map_add (f := _), map_nsmul, he₁, he₂, smul_add, add_assoc]⟩
    · obtain ⟨e, he⟩ := hN' a
      exact ⟨G e, by rw [LinearEquiv.trans_apply, he, map_add (f := _), map_nsmul]⟩
  choose! F hF hFc using hstep
  obtain ⟨S, hS0, hSs⟩ : ∃ S : ℕ → D.La ≃ₗ[𝓞 E] D.La, S 0 = LinearEquiv.refl _ _ ∧ ∀ j, S (j + 1) = F j (S j) :=
    ⟨iterSeq (LinearEquiv.refl _ _) F, rfl, fun _ => rfl⟩
  have hgood : ∀ j, GoodAt D (y (levelSeq N j)) Z N (levelSeq N j) (S j) := by
    intro j
    induction j with
    | zero =>
      rw [hS0, levelSeq_zero]
      exact ⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩, fun a => hbase a⟩
    | succ j ih => rw [hSs]; exact hF j (S j) ih
  have hc1 : ∀ j a, ∃ e, S (j + 1) a = S j a + levelSeq N j • e := fun j a => by
    rw [hSs]; exact hFc j (S j) (hgood j) a
  have hck : ∀ i k a, ∃ e, S (i + k) a = S i a + levelSeq N i • e := by
    intro i k
    induction k with
    | zero => intro a; exact ⟨0, by simp⟩
    | succ k ih =>
      intro a
      obtain ⟨e, he⟩ := ih a
      obtain ⟨e₁, he₁⟩ := hc1 (i + k) a
      obtain ⟨e₂, he₂⟩ := nsmul_eq_nsmul_of_dvd (levelSeq_dvd N (Nat.le_add_right i k)) e₁
      exact ⟨e + e₂, by rw [← Nat.add_assoc, he₁, he, he₂, smul_add, add_assoc]⟩
  refine ⟨Z, hZ, hrk, S, fun n => (hgood n).1, fun n m hn hm a => ?_, fun n => (hgood n).2.1, fun n hn a => ?_⟩
  · have hle : n ≤ n * m := Nat.le_mul_of_pos_right n hm
    rw [← Nat.add_sub_of_le hle]
    obtain ⟨e, he⟩ := hck n (n * m - n) a
    obtain ⟨e', he'⟩ := nsmul_eq_nsmul_of_dvd (dvd_levelSeq N hn) e
    exact ⟨e', by rw [he, he']⟩
  · have hg := hgood n
    have hon := ((hc _ (levelSeq_pos hN n)).comp_isometry (S n) hg.1).1
    have hkn := hg.2.2.of_dvd hon (dvd_levelSeq N hn)
    obtain ⟨k, hk⟩ := dvd_levelSeq N hn
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hk; exact absurd hk (levelSeq_pos hN n).ne'
      · exact h0
    have hcong : ∀ a, ∃ e, ((y (levelSeq N n)).comp (S n).toLinearMap) a =
        ((y n).comp (S n).toLinearMap) a + n • e := by
      intro a
      rw [hk]
      exact hy n k hn hkpos (S n a)
    exact (ker_iff_of_congr hcong a).trans (hkn a)

end GlobalTheory.LowFilt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_siegelFamily_cyclotomicAway_odd_level : ∀ g n : ℕ, 1 ≤ g → 3 ≤ n → Odd n → Nonempty (SFam g n (zetaAway n)) := by
  first | exact @GlobalTheory.SiegelTor.exists_sFam_cycAway | exact GlobalTheory.SiegelTor.exists_sFam_cycAway | (intros; apply GlobalTheory.SiegelTor.exists_sFam_cycAway <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.de_rham_polarization_perfect_pairing : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[k] HdR B →ₗ[k] k, AbDual.IsCorrForm (dp0 k) (𝟙 _) A B P φ → φ.IsPerfPair := by
  first | exact @GlobalTheory.FieldPerf.isPerfPair | exact GlobalTheory.FieldPerf.isPerfPair | (intros; apply GlobalTheory.FieldPerf.isPerfPair <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_closedSubscheme_pullback_adjoint_endomorphism_pair : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (f f' : A ⟶ A), IsMonHom f → IsMonHom f' → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (g g' : A' ⟶ A'), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → g.left ≫ φ' = φ' ≫ f.left → g'.left ≫ φ' = φ' ≫ f'.left → (LBIso ((Q.pull φ₂').pull (lift (fst A' A' ≫ g) (snd A' A')).left) ((Q.pull φ₂').pull (lift (fst A' A') (snd A' A' ≫ g')).left) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  first | exact @GlobalTheory.EndLoc.exists_closed_adj | exact GlobalTheory.EndLoc.exists_closed_adj | (intros; apply GlobalTheory.EndLoc.exists_closed_adj <;> assumption)
end
