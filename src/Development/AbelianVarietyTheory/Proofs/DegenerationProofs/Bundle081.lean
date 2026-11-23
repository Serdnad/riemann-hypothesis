module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfNormOneGenerators
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle074
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.GeoHalf

theorem sec_of_iso {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀)
    (he : ∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a)
    (hs : ∀ z, ∀ a ∈ S.HH M z, ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.toScheme), z ∈ W ∧
      h ≫ Q.G.ι ≫ Q.P.hom = W.ι ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme)
        (x' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι →
        x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀) :
    Z.Sec := by
  obtain ⟨e, he1, he2, he3⟩ := he
  intro z a ha
  obtain ⟨W, h, hz, hh, hx⟩ := hs z a ha
  refine ⟨W, h ≫ e.inv, hz, ?_, ?_⟩
  · rw [← he1, Category.assoc, e.inv_hom_id_assoc]; exact hh
  · obtain ⟨u₀, hu, G, semi, dim, qproj, φ, cart, L, cub, sym, w, w_gen, w_rig, split⟩ := Z
    dsimp only at e he1 he2 he3 ⊢
    subst he2
    have he4 : φ ≫ e.hom = ex.a := eq_of_heq he3
    intro x x' h1 h2 h3
    have ha0 : φ ≫ e.hom ≫ Q.G.ι = Q.a₀ := by rw [← Category.assoc, he4, ex.a_eq]
    have h4 : x' ≫ pullback.snd _ _ ≫ U₀.ι = M.pt := by
      rw [← Q.cart.w, ← ha0, ← h2, ← he1]; simp only [Category.assoc]
    have h5 : (x' ≫ pullback.snd _ _) ≫ Q.u₀ = spMap S.R.val.toRingHom :=
      Q.u₀_pt _ (by rw [Category.assoc]; exact h4)
    have h6 := hx Ω x x' (h1.trans h4.symm) (by
      rw [h3, ← h5]; simp only [Category.assoc])
    rw [← cancel_mono (e.hom ≫ Q.G.ι)]
    simp only [Category.assoc, e.inv_hom_id_assoc]
    rw [h6, ha0]

theorem zhGeo_of
    (hhastests : GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.HasTests ∧ ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀), l.Match τ ∧ ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)))
    (hprex : Laws → Laws2 → ThmUSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ex.core.HasTests → ex.core.Indep → ex.core.HasCharts → ex.core.TorsSec (S.r * S.N) → (∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀))) → ∃ Z : ZHPre ρ M U₀, (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) ∧ Z.LocTheta ∧ Nonempty ex.core.Law)
    (hab : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀), (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) → Nonempty ex.core.Law → ex.core.HasTests → ex.core.HasCharts → IsOpen {z : M.Z | S.TT M z = ⊥} → (∀ w : Q.P.left, IsClosed ({w} : Set Q.P.left) → S.TT M (Q.P.hom w) = ⊥ → w ∈ Q.G) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.TT M z ≠ ⊥ → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (τ : ex.core.Test y), y (GlobalTheory.ZJ.cPt p) = z ∧ ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j))) → Z.Ab)
    (hseco : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀), (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) → BaseFacts S M U₀ EE → Z.Ab → (∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0) → Z.SecO EE)
    (hunifr : Laws → Laws2 → Laws3 → Laws4 → Laws5 → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W))
    (htop : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Big → ρ.HasU → S.Over₀ M U₀ → S.IsEE M U₀ EE → BaseFacts S M U₀ EE ∧ ρ.HasGeo ∧ ∃ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), ex.core.HasTests ∧ ex.core.Indep ∧ ex.core.Fib ∧ ex.core.HasCharts)
    (htheta : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)))
    (htorssec : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → ex.core.TorsSec (S.r * S.N))
    (hhsec : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), ∀ z, ∀ a ∈ S.HH M z, ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.toScheme), z ∈ W ∧ h ≫ Q.G.ι ≫ Q.P.hom = W.ι ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (x' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι → x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀)
    (hindepfib : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0)
    (hzab : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → IsOpen {z : M.Z | S.TT M z = ⊥} ∧ (∀ w : Q.P.left, IsClosed ({w} : Set Q.P.left) → S.TT M (Q.P.hom w) = ⊥ → w ∈ Q.G) ∧ ∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.TT M z ≠ ⊥ → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (τ : ex.core.Test y), y (GlobalTheory.ZJ.cPt p) = z ∧ ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)))
    (hout : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀) (C : Clos ρ M U₀ EE) (ex : C.Ext), (∃ e : Q.G.left ≅ C.G.toScheme, e.hom ≫ C.G.ι ≫ C.P.hom = Q.G.hom ∧ Q.u₀ = C.u₀ ∧ HEq (Q.φ ≫ e.hom) ex.a) → S.Big → S.Over₀ M U₀ → S.IsEE M U₀ EE → Q.Sec → Q.LocTheta → Q.SecO EE → Q.Ab → Nonempty (ZHOut ρ M U₀ EE)) :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → Laws3 → Laws4 → Laws5 → UTorsSt → ZHGeoSt := by
  intro hx hN hU l1 l2 l3 l4 l5 hT o Ω _ _ _ _ S ρ hB M U₀ EE hov hee _
  have ll : GlobalTheory.UT.LL := ⟨l1, l2, l3, l4, l5⟩
  have hasU : ρ.HasU := fun p _ y₀ hy Fs => (hhastests hN hU l1 l2 hT o Ω S ρ).2 p y₀ Fs hy
  obtain ⟨bf, hg, Q, ex, ht, hi, hf, hc⟩ := htop ll hT o Ω S ρ M U₀ EE hB hasU hov hee
  obtain ⟨Z, he, hth, hlaw⟩ := hprex l1 l2 hU o Ω S ρ M U₀ EE Q ex hB ht hi hc
    (htorssec ll o Ω S ρ M U₀ EE bf Q ex hB hg hf) (htheta ll o Ω S ρ M U₀ EE bf Q ex hB hg)
  obtain ⟨z1, z2, z3⟩ := hzab ll o Ω S ρ M U₀ EE bf Q ex hB hg hf
  have hab : Z.Ab := hab o Ω S ρ M U₀ EE Q ex Z he hlaw ht hc z1 z2 z3
  have hso : Z.SecO EE := hseco o Ω S ρ M U₀ EE Q ex Z he bf hab
    (hindepfib ll o Ω S ρ M U₀ EE bf Q hB hg)
  exact hout hx (hunifr l1 l2 l3 l4 l5) hN hU l1 l2 hT o Ω S ρ M U₀ EE Z Q ex he hB hov hee
    (sec_of_iso Q ex Z he (hhsec ll o Ω S ρ M U₀ EE bf Q)) hth hso hab
end GlobalTheory.ZH.GeoHalf
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_finset_closure_eq_top {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {X : Scheme.{0}}
    (s : X ⟶ Sp o) [LocallyOfFiniteType s] {W : X.Opens} (hW : IsAffineOpen W) :
    ∃ t : Finset Γ(X, W), Subring.closure (t : Set Γ(X, W)) = ⊤ := by
  have h1 : (s.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  have h3 : (algebraMap ℤ o).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h4 := (h1.comp h2).comp h3
  have h5 : (algebraMap ℤ Γ(X, W)).FiniteType := by
    convert h4 using 1
    exact RingHom.ext_int _ _
  obtain ⟨t, ht⟩ := (RingHom.finiteType_algebraMap.1 h5).out
  refine ⟨t, ?_⟩
  rw [Algebra.adjoin_int] at ht
  exact top_unique fun x _ => (show x ∈ subalgebraOfSubring (Subring.closure (t : Set Γ(X, W))) from
    ht ▸ Algebra.mem_top)

theorem exists_factor_of_closure {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* C) (j : B →+* C)
    (hj : Function.Injective j) {t : Set A} (ht : Subring.closure t = ⊤) (h : ∀ a ∈ t, φ a ∈ j.range) :
    ∃ ψ : A →+* B, j.comp ψ = φ := by
  have h1 : ∀ a, φ a ∈ j.range := fun a =>
    (Subring.closure_le.2 (show t ⊆ (j.range.comap φ : Subring A) from h)) (ht ▸ Subring.mem_top a)
  let e : B ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun _ _ hx => hj (congrArg Subtype.val hx), j.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (φ.codRestrict j.range h1), RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ a, h1 a⟩)

theorem preimage_comp_eq_val {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens)
    (hne : (U₀ : Set M.Z).Nonempty) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R)
    (hu : ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom)
    {K : Type} [Field K] (t : Sp K ⟶ U₀.toScheme) (a : R) :
    (Spec.preimage (t ≫ u₀)).hom a = M.val (t ≫ U₀.ι) a := by
  have hle : (⊤ : U₀.toScheme.Opens) ≤ U₀.ι ⁻¹ᵁ U₀ := fun x _ => x.2
  have hs : Function.Surjective (U₀.ι.appLE U₀ ⊤ hle).hom := by
    have : IsIso (U₀.ι.appLE U₀ ⊤ hle) := inferInstance
    exact (asIso (U₀.ι.appLE U₀ ⊤ hle)).commRingCatIsoToRingEquiv.surjective
  obtain ⟨f, hf⟩ := hs ((u₀.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  have key : ∀ (L : Type) [Field L] (x : Sp L ⟶ U₀.toScheme),
      (Spec.preimage (x ≫ u₀)).hom a = valF (x ≫ U₀.ι) U₀ f := by
    intro L _ x
    rw [preimage_apply, ← valR_appLE x u₀ (U := ⊤) (V := ⊤) le_top (le_preimage_top _), ← hf,
      valR_appLE x U₀.ι hle (le_preimage_top _)]
    rfl
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hne)
  have h1 := key Ω (IsOpenImmersion.lift U₀.ι M.pt hr)
  rw [hu _ (IsOpenImmersion.lift_fac _ _ _), IsOpenImmersion.lift_fac, Spec.preimage_map] at h1
  rw [key K t]
  refine (RatModel.val_eq ?_ h1.symm).symm
  rintro _ ⟨w, rfl⟩
  exact (t w).2

theorem exists_fac_of_large_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), Set.range (gPt p ≫ y) ⊆ U₀ → ∃ (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ ∀ u : ρ.UTest p y₀, (∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))) → Nonempty (Q.Fac y u) := by
  intro o Ω _ _ _ hA S ρ M U₀ EE hB Q p _ y hy
  have hO := hB.ov
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hy ⟨w, rfl⟩
  have hle : S.R ≤ M.O ((gPt p ≫ y) w) := hO.le.trans (RatModel.ringOn_le_O hw)
  let y₀ : S.R →+* PadicAlgCl p :=
    (RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
  have hn : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a =>
    RatModel.norm_val_le_one (y := y) rfl (x := algebraMap o Ω a) ((M.O _).algebraMap_mem a)
  have hat : S.At M y y₀ := fun _ => rfl
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y (le_preimage_top y)
  haveI := hA.ft
  haveI := M.lft
  obtain ⟨t, ht⟩ := exists_finset_closure_eq_top M.s hW
  refine ⟨y₀, t.image (fun f => (((valMap y W hyW).hom f : OO p) : PadicAlgCl p)), hn, fun u hu => ?_⟩
  have hj : Function.Injective u.j := fun a b h =>
    IsFractionRing.injective u.V (FractionRing u.V)
      ((algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (congrArg Subtype.val h))
  obtain ⟨ψ, hψ⟩ := exists_factor_of_closure (valMap y W hyW).hom u.j hj ht (by
    intro a ha
    obtain ⟨x, hx⟩ := hu _ (Finset.mem_image_of_mem _ ha)
    obtain ⟨v, hv⟩ := (u.norm_le x).1 (by rw [hx]; exact (mem_OO_iff _).1 (Subtype.prop _))
    exact ⟨v, Subtype.ext (by rw [← hx, ← hv]; rfl)⟩)
  let yV : Sp u.V ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec
  have hfac : spMap u.j ≫ yV = y := by
    rw [← specMap_valMap_fromSpec hW y hyW, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
    rfl
  have hg : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V ≫ yV = gPt p ≫ y := by
    have e : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V = gPt p ≫ spMap u.j := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    rw [← hfac, ← Category.assoc, e, Category.assoc]
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) w)]
    rw [← hg] at hw
    exact hw
  refine ⟨⟨hat, yV, hfac, IsOpenImmersion.lift U₀.ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩⟩
  rw [← Spec.map_preimage (IsOpenImmersion.lift U₀.ι _ hr ≫ Q.u₀)]
  congr 1
  ext a
  apply (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective
  have h1 := preimage_comp_eq_val M U₀ hO.ne S.R Q.u₀ Q.u₀_pt
    (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ IsOpenImmersion.lift U₀.ι _ hr) a
  rw [Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, hg, ← hat a, Spec.preimage_comp,
    Spec.preimage_map] at h1
  exact h1.trans (DFunLike.congr_fun u.fac a).symm

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.PowSec
open GlobalTheory.Points

variable {X Y : Scheme.{0}} {K : Type} [Field K]

theorem le_inf' {g : Sp K ⟶ X} {U V : X.Opens} (hU : ⊤ ≤ g ⁻¹ᵁ U) (hV : ⊤ ≤ g ⁻¹ᵁ V) :
    ⊤ ≤ g ⁻¹ᵁ (U ⊓ V) := fun _ hz => ⟨hU hz, hV hz⟩

theorem le_wchart {I : Type} [Fintype I] (L : LB X) (φ : Y ⟶ X) (j : I → L.ι) {g : Sp K ⟶ Y}
    (h : ∀ i, ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U (j i)) : ⊤ ≤ g ⁻¹ᵁ LB.wchart L (fun _ => φ) j :=
  fun _ hz => Set.mem_iInter.2 fun i => h i hz

theorem of_le_wchart {I : Type} [Fintype I] {L : LB X} {φ : Y ⟶ X} {j : I → L.ι} {g : Sp K ⟶ Y}
    (h : ⊤ ≤ g ⁻¹ᵁ LB.wchart L (fun _ => φ) j) (i : I) : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U (j i) :=
  fun _ hz => Set.mem_iInter.1 (h hz) i

noncomputable def vU (g : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) : Γ(X, U)ˣ →* Kˣ :=
  Units.map (valMap g U h).hom.toMonoidHom

theorem vU_val (g : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    valF g U u.val = (vU g U h u).val := valR_eq g U h _

theorem val_unit_ne (g : Sp K ⟶ X) {U : X.Opens} (h : ⊤ ≤ g ⁻¹ᵁ U) (u : Γ(X, U)ˣ) : valF g U u.val ≠ 0 := by
  rw [vU_val g U h]; exact Units.ne_zero _

theorem val_junk (g : Sp K ⟶ X) {U : X.Opens} (h : ¬ ⊤ ≤ g ⁻¹ᵁ U) (f : Γ(X, U)) : valF g U f = 0 := dif_neg h

theorem val_linComb_g {I : Type} [Fintype I] [Unique I] (L : LB X) (φ : Y ⟶ X) (n : ℤ) (a b : L.ι) (g : Sp K ⟶ Y)
    (ha : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U a) (hb : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U b) :
    valF g _ ((LB.LinComb L (K := I) (fun _ => φ) (fun _ => n)).g (fun _ => a) (fun _ => b)).val =
      valF (g ≫ φ) _ (L.g a b).val ^ n := by
  have h := le_inf' (le_wchart L φ (fun _ : I => a) fun _ => ha) (le_wchart L φ (fun _ : I => b) fun _ => hb)
  have key : ∀ (W : Y.Opens) (_ : ⊤ ≤ g ⁻¹ᵁ W) (e : W ≤ φ ⁻¹ᵁ (L.U a ⊓ L.U b)),
      valF g W (∏ _k : I, res e (pullU φ _ (L.g a b)) ^ n).val = valF (g ≫ φ) _ (L.g a b).val ^ n := fun W h e => by
    rw [vU_val g _ h, Fintype.prod_unique, map_zpow, Units.val_zpow_eq_zpow_val, ← vU_val]
    rw [GlobalTheory.NormGlue.val_res_pullU]
    exact congrArg (· ^ n) (valR_appLE g φ e h _)
  exact key (LB.wchart L (fun _ : I => φ) (fun _ => a) ⊓ LB.wchart L (fun _ : I => φ) (fun _ => b)) h
    (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : I => φ) (fun _ => a) default))
      (inf_le_right.trans (LB.wchart_le L (fun _ : I => φ) (fun _ => b) default)))

theorem val_div_g (M L : LB X) (a b : (LB.div M L).ι) (g : Sp K ⟶ X)
    (ha : ⊤ ≤ g ⁻¹ᵁ (LB.div M L).U a) (hb : ⊤ ≤ g ⁻¹ᵁ (LB.div M L).U b) :
    valF g _ ((LB.div M L).g a b).val = valF g _ (M.g a.1 b.1).val * (valF g _ (L.g a.2 b.2).val)⁻¹ := by
  have h := le_inf' ha hb
  have key : ∀ (W A B : X.Opens) (_ : ⊤ ≤ g ⁻¹ᵁ W) (e : W ≤ A) (e' : W ≤ B) (u : Γ(X, A)ˣ) (v : Γ(X, B)ˣ),
      valF g W (res e u * (res e' v)⁻¹).val = valF g A u.val * (valF g B v.val)⁻¹ := fun W A B h e e' u v => by
    rw [vU_val g _ h, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, ← vU_val, ← vU_val]
    exact congrArg₂ (fun x y => x * y⁻¹) (valR_res g e h _) (valR_res g e' h _)
  exact key _ _ _ h _ _ _ _

theorem val_sec {H : LB X} (s : LB.Sec H) (x : Sp K ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valF x (H.U j) (s.f j) = valF x (H.U j ⊓ H.U k) (H.g j k).val * valF x (H.U k) (s.f k) := by
  have h := le_inf' hj hk
  have e := congrArg (valR x (H.U j ⊓ H.U k)) (s.compat j k)
  rwa [valR_mul x _ h, valR_res x _ h, valR_res x _ h] at e

theorem val_gen {H : LB X} {s : LB.Gen H} (hs : s.IsGen) (x : Sp K ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valF x (H.U j) (s.s j).val = valF x (H.U j ⊓ H.U k) (H.g j k).val * valF x (H.U k) (s.s k).val :=
  val_sec ⟨fun i => (s.s i).val, fun i j => congrArg Units.val (hs i j)⟩ x hj hk

theorem val_g_self {L : LB X} (hL : L.IsLB) (x : Sp K ⟶ X) {k : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valF x _ (L.g k k).val = 1 :=
  (valR_res x _ h _).symm.trans ((congrArg (fun u : Γ(X, L.U k)ˣ => valR x _ u.val) (hL.g_self k)).trans
    (valR_one x _ h))

theorem isUnit_of_val {U : X.Opens} (f : Γ(X, U))
    (h : ∀ (K : Type) [Field K] (g : Sp K ⟶ X), ⊤ ≤ g ⁻¹ᵁ U → valF g U f ≠ 0) : IsUnit f := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => (X.mem_basicOpen f x hx).1 ?_
  let g : Sp (X.residueField x) ⟶ X := X.fromSpecResidueField x
  have hg : ∀ w, g w = x := fun w => Scheme.fromSpecResidueField_apply _ _
  have h1 : ⊤ ≤ g ⁻¹ᵁ U := fun w _ => show g w ∈ U by rw [hg]; exact hx
  have := (le_preimage_basicOpen_iff g h1 f).2 (h _ g h1).isUnit (x := IsLocalRing.closedPoint _) trivial
  exact Set.mem_of_eq_of_mem (hg _).symm this

def Reg (y : Y) (F : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K) : Prop :=
  ∃ (V : Y.Opens) (f : Γ(Y, V)), y ∈ V ∧ ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ V → valF g V f = F K g

section
variable {y : Y} {F F' : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K}

theorem Reg.val (m : Y ⟶ X) {U : X.Opens} (s : Γ(X, U)) (h : m y ∈ U) : Reg y fun _ _ g => valF (g ≫ m) U s :=
  ⟨m ⁻¹ᵁ U, (m.app U).hom s, h, fun _ _ g _ => (valR_comp g m U s).symm⟩

theorem Reg.inv (m : Y ⟶ X) {U : X.Opens} (s : Γ(X, U)) (h : m y ∈ X.basicOpen s) :
    Reg y fun _ _ g => (valF (g ≫ m) U s)⁻¹ := by
  obtain ⟨u, hu⟩ : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
  refine ⟨m ⁻¹ᵁ X.basicOpen s, (m.app _).hom (u⁻¹).val, h, fun _ _ g hg => (valR_comp g m _ _).symm.trans ?_⟩
  replace hg : ⊤ ≤ (g ≫ m) ⁻¹ᵁ X.basicOpen s := hg
  refine (vU_val (g ≫ m) _ hg _).trans ?_
  rw [map_inv, Units.val_inv_eq_inv_val, ← vU_val, hu]
  exact congrArg (·⁻¹) (valR_res _ _ hg _)

theorem Reg.mul (h : Reg y F) (h' : Reg y F') : Reg y fun K _ g => F K g * F' K g := by
  obtain ⟨V, f, hy, hf⟩ := h
  obtain ⟨V', f', hy', hf'⟩ := h'
  refine ⟨V ⊓ V', resG Y inf_le_left f * resG Y inf_le_right f', ⟨hy, hy'⟩, fun K _ g hg => ?_⟩
  exact (valR_mul g _ hg _ _).trans (congrArg₂ (· * ·)
    ((valR_res g _ hg _).trans (hf K g (le_preimage_mono g inf_le_left hg)))
    ((valR_res g _ hg _).trans (hf' K g (le_preimage_mono g inf_le_right hg))))

theorem Reg.add (h : Reg y F) (h' : Reg y F') : Reg y fun K _ g => F K g + F' K g := by
  obtain ⟨V, f, hy, hf⟩ := h
  obtain ⟨V', f', hy', hf'⟩ := h'
  refine ⟨V ⊓ V', resG Y inf_le_left f + resG Y inf_le_right f', ⟨hy, hy'⟩, fun K _ g hg => ?_⟩
  exact (valR_add g _ hg _ _).trans (congrArg₂ (· + ·)
    ((valR_res g _ hg _).trans (hf K g (le_preimage_mono g inf_le_left hg)))
    ((valR_res g _ hg _).trans (hf' K g (le_preimage_mono g inf_le_right hg))))

theorem Reg.pow (h : Reg y F) (n : ℕ) : Reg y fun K _ g => F K g ^ n := by
  obtain ⟨V, f, hy, hf⟩ := h
  exact ⟨V, f ^ n, hy, fun K _ g hg => (valR_pow g _ hg _ _).trans (congrArg (· ^ n) (hf K g hg))⟩

theorem Reg.sum {I : Type} (s : Finset I) {F : I → ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K}
    (h : ∀ i, Reg y (F i)) : Reg y fun K _ g => ∑ i ∈ s, F i K g := by
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, 0, trivial, fun K _ g hg => valR_zero g _ hg⟩
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

end

theorem exists_glue [IsIntegral Y] (V : Y.Opens) (R : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K → Prop)
    {F : Type} [Field F] (ξ : Sp F ⟶ Y) (hξ : ∀ w, ξ w = genericPoint Y)
    (hu : ⊤ ≤ ξ ⁻¹ᵁ V → ∀ v v', R F ξ v → R F ξ v' → v = v')
    (hl : ∀ y ∈ V, ∃ (W : Y.Opens) (f : Γ(Y, W)), y ∈ W ∧
      ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ W → ⊤ ≤ g ⁻¹ᵁ V → R K g (valF g W f)) :
    ∃ f : Γ(Y, V), ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ V → R K g (valF g V f) := by
  choose W f hy hf using fun y : V => hl y.1 y.2
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun y : V => V ⊓ W y) V (fun y => homOfLE inf_le_left)
    (fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hz, hy _⟩) (fun y => resG Y inf_le_right (f y))
    (fun a b => eq_of_valF_generic ξ hξ (U := (V ⊓ W a) ⊓ (V ⊓ W b)) fun h => by
      have h1 := le_preimage_mono ξ inf_le_left h
      have h2 := le_preimage_mono ξ inf_le_right h
      have h3 := le_preimage_mono ξ inf_le_left h1
      exact ((valR_res ξ inf_le_left h _).trans (valR_res ξ _ h1 _)).trans ((hu h3 _ _
        (hf a F ξ (le_preimage_mono ξ inf_le_right h1) h3) (hf b F ξ (le_preimage_mono ξ inf_le_right h2) h3)).trans
        ((valR_res ξ inf_le_right h _).trans (valR_res ξ _ h2 _)).symm))
  refine ⟨s, fun K _ g hg => ?_⟩
  let y : V := ⟨g (IsLocalRing.closedPoint K), hg trivial⟩
  have h1 : ⊤ ≤ g ⁻¹ᵁ W y := (le_preimage_iff g _).2 (hy y)
  have h2 := le_inf' hg h1
  have e : valF g V s = valF g (W y) (f y) := (valR_res g inf_le_left h2 s).symm.trans
    ((congrArg (valR g _) (hs y)).trans (valR_res g _ h2 _))
  exact e ▸ hf y K g h1 hg

theorem exists_generic (Y : Scheme.{0}) [IsIntegral Y] :
    ∃ (F : Type) (_ : Field F) (ξ : Sp F ⟶ Y), ∀ w, ξ w = genericPoint Y :=
  ⟨Y.residueField (genericPoint Y), inferInstance, Y.fromSpecResidueField _,
    fun _ => Scheme.fromSpecResidueField_apply _ _⟩

end GlobalTheory.ZH.PowSec
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory.ThetaReal

open GlobalTheory.VVRank

theorem span_translates_mulPull : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsAffine S] (P : PolAV S) (m N : ℕ), N = m ^ 2 → 1 ≤ m → IsUnit (m : Γ(S, ⊤)) → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ (κ : Type) [Fintype κ] (b : κ → SecM P.A P.L N (baseOver S)), UnivBasis P N b → ∀ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left] ![(N : ℤ), -1])), α.IsGen → ∀ s₀ : LB.Sec (LPow P.A P.L N (baseOver S)), IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀ → ∀ (I : Type) (U : I → ThetaGrp P.A P.L N (baseOver S)) (t : I → LB.Sec (LPow P.A P.L N (baseOver S))), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ N = 1 → ∃ i, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ (U i).pt = z) → (∀ i, IsActOf P.A P.L N (U i) s₀ (t i)) → Submodule.span Γ((baseOver S).left, ⊤) (Set.range fun i => (SecM.ofSec P.A (t i) : SecM P.A P.L N (baseOver S))) = ⊤ := by
  intro hL S _ _ P m N hN hm hunit th hth κ _ b₀ hb₀ α hα s₁ hs₁ I U t hU ht
  subst hN
  have hm0 : m ≠ 0 := by omega
  have hk : m ^ 2 = 1 ∨ 4 ≤ m ^ 2 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · left; rw [show m = 1 by omega]; rfl
    · right; nlinarith
  have hsurj : Surjective (mulA P.A m).left := (hL.mulN S P m hm).2.2.1
  have haff : IsAffine (baseOver S).left := ‹IsAffine S›
  obtain ⟨b, hb⟩ := hb₀ (baseOver S) (𝟙 _)
  refine span_eq_top_of_functionals b _ fun 𝔪 h𝔪 l hl y => ?_
  obtain ⟨K, _, _, u, hu⟩ := exists_geomPoint (baseOver S).left 𝔪 h𝔪
  let w : Spec (CommRingCat.of K) ⟶ S := u
  let h : Over.mk w ⟶ baseOver S := Over.homMk w (Category.comp_id _)
  have haffK : IsAffine (Over.mk w).left := inferInstanceAs (IsAffine (Spec _))
  have hntK : Nontrivial Γ((Over.mk w).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
  obtain ⟨b', hb'⟩ := hb₀ (Over.mk w) h
  obtain ⟨b₁', hb₁'⟩ := hth (Over.mk w) h
  refine (hu _).1 (functional_mem_of_span h.left.appTop.hom (pullM P.A P.L (m ^ 2 : ℕ) h) b b'
    (fun i => by rw [hb, hb', pullM_id P.A P.isLB]) _ ?_ l (fun c => (hu _).2 (hl c)) y)
  obtain ⟨ρ', k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hL.globalFns S P (m ^ 2 : ℕ) (Over.mk w)
  choose U' hU' using fun c => exists_theta_pull P.A P.isLB h (U c)
  have e : ∀ c, pullM P.A P.L (m ^ 2 : ℕ) h (SecM.ofSec P.A (t c)) =
      ρ' (U' c) (SecM.ofSec P.A (pullS P.A _ h s₁)) := fun c =>
    ((k₁ _ _ _).1 ((hU' c).2 _ _ (ht c))).symm
  simp only [e]
  have hI : Nonempty I := ⟨(hU K w 1 (by have := P.isAb.comm; exact one_pow _)).choose⟩
  refine span_translates_eq_top P.A
    ((secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).2 hL.irred S P K w (m ^ 2) hk
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ (natCast_ne_zero w hunit))) ρ' k₁ k₃ k₄ U'
    (fun θ => ?_) _ fun h0 => ?_
  · obtain ⟨c, hc'⟩ := hU K w θ.pt ((hL.kerPow S P (m ^ 2) (Nat.one_le_pow _ _ hm) (Over.mk w) θ.pt).1 fun _ =>
      ⟨⊤, trivial, _, LB.isGen_genPull _ θ.φ θ.isGen _⟩)
    exact ⟨c, (hU' c).1.trans hc'⟩
  · obtain ⟨α', -, k₂⟩ := exists_twist_pull P.A (ψ := mulT P.A (baseOver S) m) (hm := lift_snd _ _)
      (b := 1) P.isLB hα h (ψ' := mulT P.A (Over.mk w) m) (lift_snd _ _) (mulT_comm P.A h m)
    have hint : IsIntegral (Over.mk w ⊗ P.A).left :=
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth
        P.isAb.geomConnected).geometrically_isIntegral w _ _
        (IsPullback.of_hasPullback w P.A.hom).flip
    have hz := ofSec_eq_zero_of_twist P.A P.isLB (surjective_mulT P.A m hsurj _) (k₂ _ _ hs₁) h0
    exact b₁'.ne_zero 0 ((hb₁' 0).trans hz)

end GlobalTheory.ThetaReal
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_label_of_pow_eq_one' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (m : ℕ), m ∣ S.r * S.N → ∀ h : baseOver (Sp u.V) ⟶ u.G, h ^ m = 1 → ∃ b : S.Gam, m • b = 0 ∧ GlobalTheory.UnitTheta.Extends u b h := by
  first | exact @GlobalTheory.UnitTheta.exists_label_of_pow_eq_one | exact GlobalTheory.UnitTheta.exists_label_of_pow_eq_one | (intros; apply GlobalTheory.UnitTheta.exists_label_of_pow_eq_one <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.modelPointExtendsTorsionPoint_mul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a b : S.Gam) (h h' : baseOver (Sp u.V) ⟶ u.G), GlobalTheory.UnitTheta.Extends u a h → GlobalTheory.UnitTheta.Extends u b h' → GlobalTheory.UnitTheta.Extends u (a + b) (h * h') := by
  first | exact @GlobalTheory.UnitTheta.extends_mul | exact GlobalTheory.UnitTheta.extends_mul | (intros; apply GlobalTheory.UnitTheta.extends_mul <;> assumption)
end
