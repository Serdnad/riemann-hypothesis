module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniversalObjectAtModelStalk
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2994
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullFib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2890
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle175
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

theorem _root_.GlobalTheory.T.characterMap_of_integral_matrix_action : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : G ⟶ G) (m : D.toPre.X →+ D.toPre.X), IsMonHom f → EndChar U f m → (∀ u, f ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ u χ, m (c u χ) = ∑ v, a u v • c v χ := by
  first | exact @GlobalTheory.Poinc.MatChar.charMap_matrix | exact GlobalTheory.Poinc.MatChar.charMap_matrix | (intros; apply GlobalTheory.Poinc.MatChar.charMap_matrix <;> assumption)
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

namespace GlobalTheory.Poinc.TorCoord

theorem coordMap_of_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → IsGrpPullback G' G (spMap g) β → LBIso U'.LG.L (U.LG.L.pull β) → ∀ ρ, TorMatch U U' g β ρ → CoordMap D.toPre D'.toPre g ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hVb hV G' _ _ hG' D' A' U' g β hg hβ hL ρ hT
  haveI := hV
  let gK : FractionRing R →+* FractionRing V := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V (FractionRing V)).comp hg)
  have hgK : ∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r) := IsFractionRing.lift_algebraMap _
  refine GlobalTheory.PsiFromTauEven.main R V hV g gK hgK D.toPre D'.toPre D.tau_bimult D.psi_even D'.tau_bimult D'.psi_even ρ ?_
  intro a b x x' hx hx'
  obtain ⟨⟨-, -, -, hVc⟩, hV0⟩ := id hVb
  haveI := hVc
  haveI := hV0
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing V) F).comp gK).toAlgebra
  have hF : ∀ y, algebraMap (FractionRing R) F y = algebraMap (FractionRing V) F (gK y) := fun _ => rfl
  have hFr : ∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r)) :=
    fun r => (hF _).trans (congrArg _ (hgK r))
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.exists_genericPoints_uniformisations_weilPairing_galois R hR G hG D A U V hVb hV g hg G' β hβ hG' D' A' U' hL F hFr
  have hm : ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative D.toPre.X →* Fˣ) (τ' : Multiplicative D'.toPre.X →* Fˣ)
      (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := V) F ⟶ A'.A),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
      q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g → QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a = e a' := by
    intro k hk τ τ' q q' a a' h1 h2 h3 h4 h5 h6 h7 h8
    have h := (hT F hFr k hk τ τ' q q' a a' h1 h2 h3 h4 h5 h6 h7 h8).trans (he3 a').symm
    simp only [genMap] at h
    have hs : ∀ z : TFK (R := R) F ⟶ A.A, z.left ≫ U.gen.inv.left ≫ pullback.snd G.hom (jK R) = (TFK (R := R) F).hom := by
      intro z
      have := Over.w U.gen.inv
      rw [← Over.w z, ← this]
      rfl
    have h' : a.left ≫ U.gen.inv.left = (e a').left ≫ U.gen.inv.left :=
      pullback.hom_ext (by simpa only [Category.assoc] using h) (by simpa only [Category.assoc] using (hs a).trans (hs (e a')).symm)
    ext1
    have hi : Mono U.gen.inv.left := inferInstance
    exact (cancel_mono _).1 h'
  have key : ∀ k : ℕ, IsUnit (k : R) →
      (k : ℤ) ∣ (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun (Units.map gK.toMonoidHom x) - (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun x' :=
    fun k hk => by
      obtain ⟨O, φ, σ, π, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_inertia_moves_tame_root V F ϖ hϖ k (by simpa using hk.map g)
      exact GlobalTheory.TauFormGen.dvd_ord_sub R hR G hG D A U V hVb G' hG' D' A' U' g gK hgK F hF k hk ϖ hϖ O φ σ π h₁ h₂ h₃ h₄ h₅ ρ e
        (he1 k) (he2 σ) (hm k hk) a b x x' hx hx'
  obtain ⟨u, hu⟩ := GlobalTheory.TauForm.exists_unit_of_ord_eq (W := V) (x := Units.map gK.toMonoidHom x) (y := x') (by
    rw [← sub_eq_zero]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key (l ^ Int.natAbs
      ((GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun (Units.map gK.toMonoidHom x) - (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun x'))
      (by simpa using hl.pow _)) ?_
    rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega))
  exact ⟨u, hu⟩

end GlobalTheory.Poinc.TorCoord
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

theorem _root_.GlobalTheory.T.characters_eighthPower_elementaryMatrices_alt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → (Function.Bijective fun y : Fin 8 → D.toPre.X => ∑ v, c v (y v)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ w x, m (c w x) = if w = a then c b x else 0 := by
  first | exact @GlobalTheory.Poinc.Eq8.characters_eighthPower_elementaryMatrices | exact GlobalTheory.Poinc.Eq8.characters_eighthPower_elementaryMatrices | (intros; apply GlobalTheory.Poinc.Eq8.characters_eighthPower_elementaryMatrices <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.eighth_power_universal_object_at_model_stalk : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ z : V.toScheme, ∃ (cO : SiegPre g n ζ ((V.toScheme.fromSpecStalk z ≫ v) ≫ F.s)) (prO : Fin 8 → ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G ⟶ cO.A)), SiegPB cO F.univ (V.toScheme.fromSpecStalk z ≫ v) ∧ (∀ a, IsMonHom (prO a)) ∧ (∀ (T' : Over (Spec (V.toScheme.presheaf.stalk z))) (y : Fin 8 → (T' ⟶ cO.A)), ∃! x : T' ⟶ (Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G, ∀ a, x ≫ prO a = y a) ∧ LBIso (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (V.toScheme.fromSpecStalk z ≫ V.ι))) (LB.LinComb cO.P (K := Fin 8 × Fin 8) (fun ab => (lift (prO ab.1) (prO ab.2)).left) (fun ab => W ab.1 ab.2)) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G), MatOn FinalForm pr a b f → MatEnd prO a b ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).map f) := by
  first | exact @GlobalTheory.Poinc.Eq8.StalkPow.eighth_power_at_stalk | exact GlobalTheory.Poinc.Eq8.StalkPow.eighth_power_at_stalk | (intros; apply GlobalTheory.Poinc.Eq8.StalkPow.eighth_power_at_stalk <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SiegFactor.firstFactor : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZHOut ρ M U₀ EE) (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), S.Over₀ M U₀ → OpenAt F β u M U c → ∃ (G : Over M.Z) (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left) (_ : IsCommMonObj G), IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e ∧ LBIso (hodge Zh.G S.g) (lbPow (hodge G g) 8) := by
  intro g n hg hn hodd F W hW o Ω _ _ _ _ β S ρ u hsys M U₀ EE Zh U c hO hOpen
  obtain ⟨-, -, hSg, ⟨c', hc'pb, pr, hpr, huniv, -⟩, -⟩ := hsys
  haveI : IsCommMonObj ρ.P.A := ρ.P.isAb.comm
  obtain ⟨inj, hinj, hinjpr, hsum⟩ := GlobalTheory.T.exists_injections_eighthPower_grpObj ρ.P.A c'.A pr hpr huniv
  let E' : Fin 8 → Fin 8 → (ρ.P.A ⟶ ρ.P.A) := fun a b => pr a ≫ inj b
  have hE' : ∀ a b, IsMonHom (E' a b) := fun a b => by
    haveI := hpr a; haveI := hinj b; exact inferInstanceAs (IsMonHom (pr a ≫ inj b))
  have hrel' : ∀ a b c d, E' a b ≫ E' c d = if b = c then E' a d else 1 := by
    intro a b c d
    show (pr a ≫ inj b) ≫ pr c ≫ inj d = if b = c then pr a ≫ inj d else 1
    rw [Category.assoc, ← Category.assoc (inj b), hinjpr]
    split_ifs
    · rw [Category.id_comp]
    · haveI := hinj d; rw [MonObj.one_comp, MonObj.comp_one]
  haveI : AlgebraicGeometry.IsNoetherian M.Z := GlobalTheory.T.isNoetherian_functionFieldModel_arithBase M
  have hdense : Dense (U₀ : Set M.Z) := U₀.isOpen.dense hO.ne
  obtain ⟨E, hE, hrel, hsumE, hcompat⟩ := GlobalTheory.T.exists_matrixUnits_extend_normal_noetherian hO.normal U₀ hdense Zh.G Zh.semi
    ((Over.pullback Zh.u₀).obj ρ.P.A) ρ.P.A Zh.u₀ Zh.φ (pullback.fst _ _) Zh.cart (isGrpPullback_pullback _ _)
    E' hE' hrel' hsum
  have hidem : E 0 0 ≫ E 0 0 = E 0 0 := by rw [hrel]; simp
  obtain ⟨H, _, i, r, hi, hr, hir, hri, hH⟩ := GlobalTheory.T.semiAbelian_direct_factor_of_idempotent M.Z Zh.G Zh.semi (E 0 0) (hE 0 0) hidem
  haveI : IsCommMonObj H := hH.comm
  have huniv8 := GlobalTheory.T.eighthPower_of_matrixUnits_idempotent_split Zh.G H E hE hrel hsumE i r hi hr hir hri
  have hpr8 : ∀ a, IsMonHom (E a 0 ≫ r) := fun a => by
    haveI := hE a 0; haveI := hr; exact inferInstanceAs (IsMonHom (E a 0 ≫ r))
  have hdimG : SmoothOfRelativeDimension (8 * g) Zh.G.hom := hSg ▸ Zh.dim
  have hdim : SmoothOfRelativeDimension g H.hom := GlobalTheory.T.smoothOfRelativeDimension_of_eighth_power H Zh.G g (fun a => E a 0 ≫ r) huniv8 hH hdimG
  have hhodge := GlobalTheory.T.hodgeLineBundle_eighthPower_iso_pow M.Z H Zh.G g (fun a => E a 0 ≫ r) hpr8 huniv8 hH hdim
  obtain ⟨e', he'm, h1, h2⟩ := hcompat 0 0
  obtain ⟨C', _, a, b, ha, hb⟩ := GlobalTheory.T.exists_isGrpPullback_of_compatible_retracts U₀.ι Zh.u₀ Zh.G ((Over.pullback Zh.u₀).obj ρ.P.A) ρ.P.A Zh.φ
    (pullback.fst _ _) Zh.cart (isGrpPullback_pullback _ _) (E 0 0) (E' 0 0) e' he'm h1 h2 H i r hi hr hir hri
    c'.A (inj 0) (pr 0) (hinj 0) (hpr 0) (by simpa using hinjpr 0 0) rfl
  obtain ⟨φ', φ₂, hφ', -, -, -⟩ := hc'pb
  obtain ⟨e, he⟩ := GlobalTheory.T.semiAbelian_pullback_abelian_over_open hO.normal (GlobalTheory.T.isSeparated_siegelModuli_over_integers F) F.univ.A F.univ.ab H hH U₀ U hO.ne hOpen.1
    (Zh.u₀ ≫ u) c C' a (b ≫ φ') ha (hb.comp hφ') Ω M.pt M.gen (fun x y hx hy => by
      rw [hOpen.2.2.2.2 x hx, ← Category.assoc, Zh.u₀_gen y hy])
  refine ⟨H, inferInstance, e, inferInstance, hH, hdim, he, ?_⟩
  rw [hSg]
  exact hhodge
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.level_cover_image_open_finite_over_moduli : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (fM : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → MinorAt S X M U₀ EE fM Xab → (abLocus Zh.G : Set M.Z) = fM ⁻¹' (Xab : Set X.Z) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ abLocus Zh.G := by
  first | exact @GlobalTheory.OpenLev.exists_open_finite | exact GlobalTheory.OpenLev.exists_open_finite | (intros; apply GlobalTheory.OpenLev.exists_open_finite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_symplectic_level_eighth_power_galois_ext : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (K : ℕ), 0 < K → IsUnit (K : X₁.o₁) → ∃ (o₂ Ω₂ : Type) (_ : CommRing o₂) (_ : Field Ω₂) (_ : Algebra o₂ Ω₂) (_ : ArithBase o₂ Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (κ : X₁.o₁ →+* o₂), FiniteDimensional X₁.Ω₁ Ω₂ ∧ IsGalois X₁.Ω₁ Ω₂ ∧ κ.Finite ∧ (algebraMap o₂ Ω₂).comp κ = (algebraMap X₁.Ω₁ Ω₂).comp (algebraMap X₁.o₁ X₁.Ω₁) ∧ ∃ (R : Subalgebra o₂ Ω₂) (h : X₁.S.R →+* R) (P : PolAV (Sp R)) (ψ : P.A.left ⟶ X₁.ρ.P.A.left) (ze : o₂ˣ), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a) ∧ P.g = X₁.ρ.P.g ∧ IsGrpPullback P.A X₁.ρ.P.A (spMap h) ψ ∧ LBIso P.L (X₁.ρ.P.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ((Units.map (algebraMap o₂ R : o₂ →* R)) ze))) := by
  first | exact @GlobalTheory.Poinc.exists_deep_level | exact GlobalTheory.Poinc.exists_deep_level | (intros; apply GlobalTheory.Poinc.exists_deep_level <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem exists_labels_finExt_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (hD : IsPullDeg ρ D.toPre D₁.toPre) (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left), IsFib ρ A A₁ a → ∃ (_ : Algebra (FractionRing R) (Kb R₁)) (em : Kb R →ₐ[FractionRing R] Kb R₁) (lab₁ : Labels D₁.toPre A₁), (∀ r, algebraMap (FractionRing R) (Kb R₁) (algebraMap R _ r) = algebraMap (FractionRing R₁) (Kb R₁) (algebraMap R₁ _ (ρ r))) ∧ OneTrait D₁.toPre A₁ lab₁ ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre (Kb R) k) (p₁ : QkPt D.toPre (Kb R₁) k) (p' : QkPt D₁.toPre (Kb R₁) k), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF ρ hD (Kb R₁) p₁.g p'.g → (lab₁ k p').left ≫ a = spMap em.toRingHom ≫ (lab k p).left := by
  intro R _ _ _ hR D A lab hT R₁ _ _ _ ρ hρ D₁ hD A₁ a ⟨ga, hga, gpa, la⟩
  obtain ⟨W₀, _, _, _, φ₀, G, _, _, D₀, A₀, U₀, h₀, a₀, _, em₀, hW₀, i₀, l₀, hG, ⟨g₀, hg₀, gp₀, lb₀⟩, c₀, H₀⟩ := hT
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have hGF := hL.globalFns
  have := hR.2
  have hB := D.tau_bimult
  obtain rfl := eq_fracMap hρ.2.1 hga
  obtain rfl := eq_fracMap i₀ hg₀
  letI : Algebra (FractionRing R) (Kb R₁) := ((algebraMap (FractionRing R₁) (Kb R₁)).comp (fracMap hρ.2.1)).toAlgebra
  have c' : Compat ρ (Kb R₁) := fun r => congrArg (algebraMap (FractionRing R₁) (Kb R₁)) (hga r)

  obtain ⟨W, _, _, _, io, φ, hW, iio, lio, lφ, hc⟩ :=
    GlobalTheory.LocExt.exists_cDvr_ext_of_finite R R₁ ρ hρ.2.1 hρ.2.2 W₀ hW₀ φ₀ l₀
  have iφ : Function.Injective φ := by
    letI := ρ.toAlgebra
    haveI : Module.Finite R R₁ := hρ.2.2
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := R) ?_
    change Ideal.comap ρ (RingHom.ker φ) = ⊥
    rw [RingHom.comap_ker, hc, ← RingHom.injective_iff_ker_eq_bot]
    exact iio.comp i₀
  have := hW₀.1
  have := hW₀.2.2
  have := hW.1
  have b₀ : AdmBase W₀ (maximalIdeal W₀) := ⟨inferInstance, inferInstance, inferInstance, hW₀.2.1⟩
  have b₁ : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨D₂, h₁, A₂, U₂, b, hP, gpb, lb, hb⟩ := exists_pull_fib hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    b₀ b₁ io iio (map_maximalIdeal_le io) hG U₀
  obtain ⟨hc₀, T₀⟩ := exists_comp i₀ iio h₀ h₁
  obtain ⟨h', T'⟩ : ∃ h' : IsPullDeg φ D₁.toPre D₂.toPre, Tower hD h' hc₀ := by
    revert hc₀
    rw [← hc]
    exact fun hc₀ _ => exists_cancel hρ.2.1 iφ hD hc₀
  have fr : (fracMap iφ).comp (fracMap hρ.2.1) = (fracMap iio).comp (fracMap i₀) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
      simp only [RingHom.comp_apply, fracMap_algebraMap]
      exact congrArg _ (RingHom.congr_fun hc r))
  obtain ⟨a₁, e₁, gp₁, lb₁⟩ := exists_fib_cancel (g' := spMap (fracMap iφ))
    ((Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap fr).trans (Geo.Tor.spMap_comp _ _))) gpa la gp₀ lb₀ gpb lb
  letI : Algebra (FractionRing R₁) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap iφ)).toAlgebra
  letI : Algebra (FractionRing W₀) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap iio)).toAlgebra
  letI : Algebra (FractionRing R) (Kb W) :=
    ((algebraMap (FractionRing W) (Kb W)).comp ((fracMap iφ).comp (fracMap hρ.2.1))).toAlgebra
  have cφ : Compat φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap iφ r)
  have cio : Compat io (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap iio r)
  have cρ : Compat ρ (Kb W) := fun r =>
    congrArg (fun t => algebraMap (FractionRing W) (Kb W) (fracMap iφ t)) (fracMap_algebraMap hρ.2.1 r)
  have cc : Compat (io.comp φ₀) (Kb W) := fun r => (cρ r).trans ((cφ _).trans
    (congrArg (fun t => algebraMap (FractionRing W) (Kb W) (algebraMap W _ t)) (RingHom.congr_fun hc r)))
  have cφ₀ : Compat φ₀ (Kb W) := fun r => (cc r).trans (cio _).symm
  obtain ⟨em⟩ := nonempty_lift (FractionRing R₁) (Kb W)
  obtain ⟨j⟩ := nonempty_lift (FractionRing W₀) (Kb W)
  let emR : Kb R₁ →ₐ[FractionRing R] Kb W := ⟨em.toRingHom, fun t => em.commutes (fracMap hρ.2.1 t)⟩
  have a₀K : algebraMap (FractionRing R) (Kb W₀) = (algebraMap (FractionRing W₀) (Kb W₀)).comp (fracMap i₀) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c₀ r).trans
      (congrArg (algebraMap (FractionRing W₀) (Kb W₀)) (fracMap_algebraMap i₀ r).symm))
  let jR : Kb W₀ →ₐ[FractionRing R] Kb W := ⟨j.toRingHom, fun t => by
    rw [a₀K]
    exact (j.commutes (fracMap i₀ t)).trans
      (congrArg (algebraMap (FractionRing W) (Kb W)) (RingHom.congr_fun fr t).symm)⟩

  obtain ⟨em'⟩ := nonempty_lift (FractionRing R) (Kb R₁)
  letI : Algebra (Kb R) (Kb W) := (emR.comp em').toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) (Kb W) :=
    IsScalarTower.of_algebraMap_eq fun x => ((emR.comp em').commutes x).symm
  let emK : Kb R →ₐ[FractionRing R] Kb R₁ := em'.comp ((jR.comp em₀).restrictNormal (Kb R))
  have hK : (emR.comp emK).toRingHom = (jR.comp em₀).toRingHom :=
    RingHom.ext fun x => (jR.comp em₀).restrictNormal_commutes (Kb R) x

  have ex : ∀ (k : ℕ) (p' : QkPt D₁.toPre (Kb R₁) k), ∃ x : TFK (R := R₁) (Kb R₁) ⟶ A₁.A, 1 ≤ k →
      ∃ (p : QkPt D.toPre (Kb R) k) (p₁ : QkPt D.toPre (Kb R₁) k), QkExt emK.toRingHom p p₁ ∧ p'.y = hD.xe.symm p₁.y ∧
        IsPullGtF ρ hD (Kb R₁) p₁.g p'.g ∧ x.left ≫ a = spMap emK.toRingHom ≫ (lab k p).left := by
    intro k p'
    by_cases hk : 1 ≤ k
    · obtain ⟨p₁, hy, hg⟩ := qkPullExists hGF R R₁ ρ D.toPre D₁.toPre hD (Kb R₁) c' k p'
      obtain ⟨p, hp⟩ := exists_of_ext hB emK hk p₁
      obtain ⟨x, hx⟩ := exists_lift_pt gpa.1 emK.toRingHom emK.comp_algebraMap (lab k p)
      exact ⟨x, fun _ => ⟨p, p₁, hp, hy, hg, hx⟩⟩
    · exact ⟨η[A₁.A] |> fun e => toUnit _ ≫ e, fun h => absurd h hk⟩
  choose lab₁ hlab₁ using ex
  refine ⟨inferInstance, emK, lab₁, c', ?_, ?_⟩
  ·
    refine ⟨W, _, inferInstance, inferInstance, φ, (Over.pullback (specOf io)).obj G, inferInstance, inferInstance, D₂, A₂,
      U₂, h', a₁, inferInstance, em, hW, iφ, lφ, IsSemiAbelian.pullback _ G hG,
      ⟨fracMap iφ, fracMap_algebraMap iφ, gp₁, lb₁⟩, cφ, ?_⟩
    intro k hk p' p₁' p'' x₁ y₁ y₂ y₃ y₄
    obtain ⟨p, p₁, z₁, z₂, z₃, z₄⟩ := hlab₁ k p' hk
    obtain ⟨r, hr⟩ := exists_ext hB emR p₁
    have r₁ : IsPullGtF ρ hD (Kb W) r.g p₁'.g := isPullGtF_ext hD cρ em.toRingHom em.comp_algebraMap z₃ hr y₁
    have r₂ := T'.isPullGtF cc r₁ y₃
    have hq : QkExt (jR.comp em₀).toRingHom p r := by
      rw [← hK]
      exact qkExt_trans z₁ hr
    have key : spMap (emR.comp emK).toRingHom ≫ (lab k p).left = spMap (jR.comp em₀).toRingHom ≫ (lab k p).left := by
      rw [hK]
    obtain ⟨q₁, hq₁⟩ := exists_ext hB em₀ p
    obtain ⟨r', hr'⟩ := exists_ext hB jR q₁
    obtain rfl : r = r' := ext_unique hB (jR.comp em₀) hq (qkExt_trans hq₁ hr')
    let q₀ := pullQk h₀ hGF c₀ hB D₀.tau_bimult q₁
    obtain ⟨x₀, hx₀⟩ := exists_lift_pt gp₀.1 em₀.toRingHom (em₀.comp_algebraMap.trans a₀K) (lab k p)
    have t₀ := H₀ k hk p q₁ q₀ x₀ hq₁ rfl (isPullGtF_pullGt h₀ hGF c₀ _) hx₀
    obtain ⟨⟨q₀', hq₀'⟩, hx, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W₀ _ b₀ D₀ A₀ G hG U₀ _ (Kb W) j k hk q₀
    obtain ⟨x₀', hx₀'⟩ := hx x₀
    have t₁ := (hgal q₀' x₀ x₀' hq₀' hx₀').1 t₀
    have s₁ : IsPullGtF φ₀ h₀ (Kb W) r.g q₀'.g :=
      isPullGtF_ext h₀ cφ₀ j.toRingHom j.comp_algebraMap (isPullGtF_pullGt h₀ hGF c₀ _) hr' hq₀'
    have s₂ := isPullGtF_pullGt h₁ hGF cio q₀'.g
    rw [← pullGt_unique hc₀ cc r₂ (T₀.isPullGtF cc s₁ s₂)] at s₂
    have ey : p''.y = h₁.xe.symm q₀'.y := by
      apply hc₀.xe.injective
      have u₁ : hc₀.xe p''.y = r.y := by
        rw [← T'.xe_eq, y₂, AddEquiv.apply_symm_apply, y₁.1, z₂, AddEquiv.apply_symm_apply, hr.1]
      rw [u₁, ← T₀.xe_eq, AddEquiv.apply_symm_apply, hq₀'.1, hr'.1]
      exact (h₀.xe.apply_symm_apply _).symm
    have ex₁ : x₁.left ≫ b = x₀'.left := by
      apply gp₀.1.hom_ext
      · rw [Category.assoc, ← e₁, ← Category.assoc, y₄, Category.assoc, z₄, hx₀', Category.assoc, hx₀, ← Category.assoc,
          ← Category.assoc, ← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp]
        exact key
      · rw [Category.assoc, gpb.1.w, ← Category.assoc, Over.w x₁, Over.w x₀']
        exact (Geo.Tor.spMap_comp _ _).symm
    refine h5.qkBaseChange W₀ W _ _ b₀ b₁ io D₀ A₀ G U₀ _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) A₂ D₂ h₁
      U₂ hP (Kb W) cio k hk q₀' x₀' p'' x₁ ey s₂ ?_ t₁
    rw [hb, ← Category.assoc, ex₁]
  ·
    intro k hk p p₁ p' e₁' e₂' e₃'
    obtain ⟨q, q₁, z₁, z₂, z₃, z₄⟩ := hlab₁ k p' hk
    obtain rfl : q₁ = p₁ := qk_ext (hD.xe.symm.injective (by rw [← z₂]; exact e₂')) (pullGt_unique' hD z₃ e₃')
    obtain rfl := qkExt_inj hB emK z₁ e₁'
    exact z₄

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FixedTorsionTrait

theorem abLocus_of_retract {S : Scheme.{0}} (G H : Over S) (i : G ⟶ H) (r : H ⟶ G) (h : i ≫ r = 𝟙 G) :
    ∀ x ∈ abLocus H, x ∈ abLocus G := by
  intro x hx K _ _ t ht
  have hp : IsProper ((Over.pullback t).obj H).hom := hx K t ht
  exact GlobalTheory.Mum.RetractGeneric.isProper_of_retract ((Over.pullback t).map i) ((Over.pullback t).map r)
    (by rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]) hp

theorem closedPoint_mem_abLocus_of_fixedTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → (∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → closedPoint V ∈ abLocus ((Over.pullback (spMap φ)).obj G) := by
  intro R _ _ _ hR D A G _ _ hG U V _ _ _ φ hV hφ n hn hu H
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback (spMap φ) G hG
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj G) := Functor.isCommMonObj_obj
  obtain ⟨A', ψ, hψ⟩ := GlobalTheory.UnifProperOpen.exists_polGeneric_pullback R A G U.gen U.gen_hom V φ hφ
  obtain ⟨W, _, _, _, io, em, D₈, Q, H₈, _, _, U₈, i, r, hW, hfin, hinj, hem, hc, hH₈, htot, hr, hir, hmono⟩ :=
    GlobalTheory.T.degeneration_extension_local_domain V hV A' _ hG' ψ hψ
  have hem' : ∀ w : W, w ≠ 0 → IsUnit (em w) := fun w hw =>
    IsUnit.mk0 _ ((map_ne_zero_iff em hem).2 hw)
  letI : Algebra (FractionRing W) (AlgebraicClosure (FractionRing V)) :=
    (IsFractionRing.lift (A := W) (K := FractionRing W) (g := em) hem).toAlgebra
  have hlift : ∀ w : W, algebraMap (FractionRing W) (AlgebraicClosure (FractionRing V)) (algebraMap W _ w) = em w :=
    fun w => IsFractionRing.lift_algebraMap _ _
  have hcompat : ∀ v, algebraMap (FractionRing W) (AlgebraicClosure (FractionRing V)) (algebraMap W _ (io v)) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v) := fun v => (hlift _).trans (hc v)
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_dvr_algClosure_over_finite_dvr_extension V W hV hW io hfin hinj (AlgebraicClosure (FractionRing V)) hcompat
  have hsub : Subsingleton D₈.toPre.X := by
    refine GlobalTheory.T.characterGroup_subsingleton_of_bounded_ramification W hW D₈ Q H₈ hH₈ U₈ htot (AlgebraicClosure (FractionRing V)) n N hn fun j => ?_
    obtain ⟨T', hT', f, hf, hirr, hfix⟩ := H j
    obtain ⟨T'', hT'', g, e, hle, hg, he1, heN, hπ⟩ := hN T' hT' f hf hirr
    refine ⟨T'', hT'', g, e, hg, he1, heN, hπ, fun σ hσ x hx => ?_⟩
    exact GlobalTheory.T.fixedTorsion_transfer_jointlyMonic_homs V W io _ hcompat _ H₈ r hr hmono σ (fun w => hσ _ (by rw [← hg w]; exact (g w).2)) (n ^ j)
      (fun y hy => hfix σ (fun z hz => hσ z (hle hz)) y hy) x hx
  have := hW.1
  have := hW.2.2
  have hab : IsAbelianScheme H₈ := GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ W hW.2.1 D₈ Q H₈ hH₈ U₈ hsub
  have h₈ : closedPoint W ∈ abLocus H₈ := fun K _ _ t _ => by
    have := hab.proper
    infer_instance
  have h₁ : closedPoint W ∈ abLocus ((Over.pullback (spMap io)).obj ((Over.pullback (spMap φ)).obj G)) :=
    abLocus_of_retract _ H₈ i (r 0) hir _ h₈
  have h₂ := (abLocus_pullback (G' := (Over.pullback (spMap io)).obj ((Over.pullback (spMap φ)).obj G)) abLocusOne hG'
    (IsPullback.of_hasPullback ((Over.pullback (spMap φ)).obj G).hom (spMap io)) (closedPoint W)).2 h₁
  letI : Algebra V W := io.toAlgebra
  have : Algebra.IsIntegral V W := ⟨fun w => hfin.to_isIntegral w⟩
  have hm : (maximalIdeal W).comap io = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := V) (algebraMap _ _) hfin.to_isIntegral (maximalIdeal W))
  have : IsLocalHom io := ((IsLocalRing.local_hom_tfae io).out 5 1).1 hm
  have e : spMap io (closedPoint W) = closedPoint V := by
    have h : ⇑(spMap io) = PrimeSpectrum.comap io := by
      ext x : 1
      simp [spMap, Spec.map_base]
      rfl
    rw [h]
    exact IsLocalRing.comap_closedPoint io
  rw [← e]
  exact h₂

end GlobalTheory.FixedTorsionTrait

end
end
