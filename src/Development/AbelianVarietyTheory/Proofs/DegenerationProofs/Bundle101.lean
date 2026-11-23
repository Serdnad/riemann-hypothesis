module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionPullbackPowerLocusLe
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoordReducedFibreClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVectorFieldFrameSmoothCommGrpScheme
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseChangeTestOfSurjectiveMulAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalSectionNeZeroOnFibres
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.card_torsion_pullbackPowerLocus_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G →  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → IsAbelianScheme B → ∀ (L : LB G.left), AmpleCub G L → ∀ (F : G ⟶ G) (Q : ℕ), 2 ≤ Q → IsMonHom F → PullPow F.left L Q → i ≫ F = i ^ Q → ∃ C : ℕ, ∀ n, 1 ≤ n → Finite {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ≫ F = x ^ Q ∧ x ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ≫ F = x ^ Q ∧ x ^ n = 1} ≤ C * n ^ Module.finrank ℤ X := by
  first | exact @GlobalTheory.SS.PowLocus.card_torsion_powLocus_le | exact GlobalTheory.SS.PowLocus.card_torsion_powLocus_le | (intros; apply GlobalTheory.SS.PowLocus.card_torsion_powLocus_le <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.fib_of_indep : ∀ C : Core, C.Indep → C.Fib := by
  intro C hI p _ y τ x hx
  obtain ⟨-, hlft, -, hint, hflat, -, -, -, -, -, -, hdom, htest⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  have := C.lft
  have hne : ((C.GG.hom ⁻¹ᵁ C.U : C.G.toScheme.Opens) : Set C.G.toScheme).Nonempty := by
    obtain ⟨w, hw⟩ := hdom.denseRange.exists_mem_open C.U.isOpen C.ne
    exact ⟨w, hw⟩
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  obtain ⟨b', hb'x, hb'U⟩ :=
    (@GlobalTheory.T.exists_classical_point_lifting_residue_point C.G.toScheme hint (C.GG.hom ≫ C.π) hflat hlft' (C.GG.hom ⁻¹ᵁ C.U) hne p _).1 x
  have hcl : C.Cl (b' ≫ C.GG.hom) := by
    rintro _ ⟨s, rfl⟩
    have := hb'U ⟨s, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact this
  obtain ⟨b, hby, hbx⟩ := hI p (b' ≫ C.GG.hom) y hcl (htest p y τ).1
    (by rw [← Category.assoc, hb'x, hx]) b' rfl
  obtain ⟨c, hc, hcb⟩ := τ.lift b hby
  refine ⟨rPt p ≫ c, by rw [Category.assoc, hc], ?_⟩
  rw [Category.assoc, hcb, hbx, hb'x]

end GlobalTheory.ZJ
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_coord_reducedFibre_closedPoint : ∀ C : Core, C.HasTests → C.Fib → ∀ w : C.G.toScheme, IsClosed ({w} : Set C.G.toScheme) → ∃ (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsAffineOpen W ∧ C.Coord w W hw u := by
  first | exact @GlobalTheory.ZJ.Core.exists_coord | exact GlobalTheory.ZJ.Core.exists_coord | (intros; apply GlobalTheory.ZJ.Core.exists_coord <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_vectorFieldFrame_smooth_commGrpScheme : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∃ D : Fin g → VF A, IsFrame D := by
  first | exact @GlobalTheory.SS.exists_isFrame | exact GlobalTheory.SS.exists_isFrame | (intros; apply GlobalTheory.SS.exists_isFrame <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

theorem _root_.GlobalTheory.T.baseChangeTest_of_surjective_mul_abelianVariety : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) → ∀ (C : Core) (L : C.Law) (T : C.Theta), T.BTest L := by
  first | exact @GlobalTheory.ZJ.bTest_of_surjective_mulN | exact GlobalTheory.ZJ.bTest_of_surjective_mulN | (intros; apply GlobalTheory.ZJ.bTest_of_surjective_mulN <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_local_section_ne_zero_on_fibres' : ∀ (C : Core) (L : C.Law) (T : C.Theta) (Om : Set C.G.toScheme) (ν), IsOpen Om → T.Norms Om ν → L.CompanionTheory Om → (∃ (M : LB C.G.toScheme) (w : LB.Iso (M.pull C.a) T.L.L) (D : M.ι → C.A.left.Opens), M.IsLB ∧ w.IsGen ∧ (∀ i, (D i : Set C.A.left).Nonempty) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ C.A.left) (i : M.ι) (j : T.L.L.ι), IntAt C.a (M.U i) x → Set.range x ⊆ T.L.L.U j → Set.range x ⊆ D i → ‖valF x _ (w.s (j, fun _ => i)).val‖ * ν p x j = 1) → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  first | exact @GlobalTheory.exists_local_section_ne_zero_on_fibres | exact GlobalTheory.exists_local_section_ne_zero_on_fibres | (intros; apply GlobalTheory.exists_local_section_ne_zero_on_fibres <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.symmetryHyp_extends_semiAbelian_dvr : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∀ L : RigLB G, LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V))) → HypS G L.L := by
  first | exact @GlobalTheory.SymExtendDvr.hypS_of_generic | exact GlobalTheory.SymExtendDvr.hypS_of_generic | (intros; apply GlobalTheory.SymExtendDvr.hypS_of_generic <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH

theorem exists_sec_pull_of_comp {X Y Z : Scheme.{0}} (L : LB X) (j : Y ⟶ X) (n : Z ⟶ Y) (φ : Z ⟶ X) (e : n ≫ j = φ)
    (σ : LB.Sec (L.pull j)) : ∃ θ : LB.Sec (L.pull φ), ∀ y, n y ∈ nonzeroLocus σ → y ∈ nonzeroLocus θ := by
  subst e
  refine ⟨DVR.pullSec L (fun _ : PUnit => j) (fun _ => 1) σ n, fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  have h₁ : y ∈ Z.basicOpen ((n.app _).hom (σ.f k)) := by
    rw [← Scheme.preimage_basicOpen]; exact hk
  have h₂ : y ∈ (L.pull (n ≫ j)).U k := mem_pull.2 ((mem_pull (F := j)).1 (Y.basicOpen_le _ hk))
  exact (Z.basicOpen_res _ _).ge ⟨h₂, h₁⟩

local instance (priority := high) grpObjPullback {S T : Scheme.{0}} (f : T ⟶ S)
    (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  Functor.grpObjObj (F := Over.pullback f)

theorem unif_pullback_of_unif_ring : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → IsOpen (abLocus Q.G) → Q.Ab → Q.LocTheta → HypS Q.G Q.L.L → (∀ W : M.Z.Opens, (W : Set M.Z) ⊆ abLocus Q.G → RelAmple ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι))) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (ξ : Sp R ⟶ M.Z), (ξ ⁻¹' abLocus Q.G).Nonempty → ∀ [IsCommMonObj ((Over.pullback ξ).obj Q.G)], ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A ((Over.pullback ξ).obj Q.G)), LBIso U.LG.L (Q.L.L.pull (pullback.fst Q.G.hom ξ)) ∧ ∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus Q.G) := by
  intro H o Ω _ _ _ _ S ρ M U₀ Q _ hop hab hth hS hpol R _ _ _ _ hN hI hC ξ hne _
  have semiPull : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G],
      IsSemiAbelian G → IsSemiAbelian ((Over.pullback f).obj G) := by
    intro S S' f G _ hG
    refine
      { comm := ?_
        smooth := ?_
        separated := ?_
        quasiCompact := ?_
        geomConnected := ?_
        fibres := ?_ }
    · have := hG.comm; infer_instance
    · have := hG.smooth; change Smooth (pullback.snd G.hom f); infer_instance
    · have := hG.separated; change IsSeparated (pullback.snd G.hom f); infer_instance
    · have := hG.quasiCompact; change QuasiCompact (pullback.snd G.hom f); infer_instance
    · have := hG.geomConnected; change GeometricallyConnected (pullback.snd G.hom f); infer_instance
    · intro K _ _ q
      obtain ⟨E⟩ := hG.fibres K (q ≫ f)
      let eM := (Functor.mapMonNatIso (Over.pullbackComp q f) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
      let e : (Over.pullback (q ≫ f)).obj G ≅ (Over.pullback q).obj ((Over.pullback f).obj G) :=
        (Mon.forget _).mapIso eM
      haveI : IsMonHom e.hom := by
        change IsMonHom eM.hom.hom
        infer_instance
      letI := E.grpB
      haveI := E.q_hom
      haveI := E.i_hom
      haveI : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv
      exact ⟨{
        X := E.X
        addCommGroup := E.addCommGroup
        free := E.free
        finite := E.finite
        B := E.B
        grpB := E.grpB
        isAbelian := E.isAbelian
        q := e.inv ≫ E.q
        q_hom := inferInstance
        q_flat := by rw [Over.comp_left]; have := E.q_flat; infer_instance
        q_surjective := by rw [Over.comp_left]; have := E.q_surjective; infer_instance
        q_quasiCompact := by rw [Over.comp_left]; have := E.q_quasiCompact; infer_instance
        i := E.i ≫ e.hom
        i_hom := inferInstance
        isKernel := by
          refine IsPullback.of_iso E.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp }⟩
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB :=
    fun hL F => ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL F
  have h := isGrpPullback_pullback Q.G ξ
  obtain ⟨hL, hr, ⟨c', -⟩, hs⟩ := CubePf.cubePull _ _ Q.G _ (cubeMapOf h) Q.L Q.cub
  have hrefl : LBIso (Q.L.L.pull (pullback.fst Q.G.hom ξ)) (Q.L.L.pull (pullback.fst Q.G.hom ξ)) :=
    ⟨_, CubePf.idIsoL_isGen hL⟩
  let W₀ : M.Z.Opens := ⟨abLocus Q.G, hop⟩
  let W : (Sp R).Opens := ξ ⁻¹ᵁ W₀
  let G' := (Over.pullback ξ).obj Q.G
  have h₀ := isGrpPullback_pullback Q.G W₀.ι
  have h₁ := isGrpPullback_pullback G' W.ι
  have sq : (ξ ∣_ W₀) ≫ W₀.ι = W.ι ≫ ξ := morphismRestrict_ι ξ W₀
  have h₂ := (h₁.comp h).congr sq.symm rfl
  let ψ : ((Over.pullback W.ι).obj G').left ⟶ ((Over.pullback W₀.ι).obj Q.G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst Q.G.hom W₀.ι = pullback.fst G'.hom W.ι ≫ pullback.fst Q.G.hom ξ := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback ((Over.pullback W.ι).obj G') ((Over.pullback W₀.ι).obj Q.G) (ξ ∣_ W₀) ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hsa := semiPull W₀.ι Q.G Q.semi
  have hA : IsAbelianScheme ((Over.pullback W₀.ι).obj Q.G) :=
    { comm := hsa.comm, smooth := hsa.smooth, proper := hab.2 W₀ subset_rfl, geomConnected := hsa.geomConnected }
  have hiso : LBIso ((Q.L.L.pull (pullback.fst Q.G.hom ξ)).pull (pullback.fst G'.hom W.ι))
      ((Q.L.L.pull (pullback.fst Q.G.hom W₀.ι)).pull ψ) :=
    LBIso.chartPull
      (chartPullLinComb Q.L.L _ (fun _ : PUnit => pullback.fst G'.hom W.ι) (fun _ => 𝟙 _) (fun _ => 1) _
        fun _ => (Category.comp_id _).symm)
      (chartPullLinComb Q.L.L _ (fun _ : PUnit => ψ) (fun _ => 𝟙 _) (fun _ => 1) _
        fun _ => hψ.trans (Category.comp_id _).symm)
      ⟨_, CubePf.idIsoL_isGen (pull_isLB Q.L.isLB (𝟙 _))⟩
  obtain ⟨hA', ha, hk⟩ := GlobalTheory.pol_pull _ _ _ _ _ ψ _ _ (pull_isLB Q.L.isLB _) (pull_isLB hL _) hA h₃ hiso
  obtain ⟨ha₀, hk₀⟩ := hpol W₀ subset_rfl
  have hsp : ∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)),
      E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G') := by
    obtain ⟨E, hE⟩ := GlobalTheory.ZJ.SplitAll.fieldPoint (G := Q.G) Q.split _ (spMap (IsLocalRing.residue R) ≫ ξ)
    exact ⟨E, isGt_of_iso (pullCompIso _ ξ Q.G) hE⟩
  have hθ' : ∃ θ : LB.Sec (Q.L.L.pull (pullback.fst Q.G.hom ξ)), ∃ x ∈ nonzeroLocus θ,
      G'.hom x = IsLocalRing.closedPoint R := by
    obtain ⟨N, σ, hz, hσ⟩ := hth (ξ (IsLocalRing.closedPoint R))
    have hξ : ξ ⁻¹ᵁ N = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem ξ hz
    obtain ⟨n, hn⟩ : ∃ n : G'.left ⟶ (Q.G.hom ⁻¹ᵁ N).toScheme, n ≫ (Q.G.hom ⁻¹ᵁ N).ι = pullback.fst Q.G.hom ξ :=
      ⟨IsOpenImmersion.lift _ (pullback.fst Q.G.hom ξ) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ N) h.1.w).mpr (hξ.ge (Set.mem_univ (G'.hom y)))),
        IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨θ, hθ⟩ := exists_sec_pull_of_comp Q.L.L _ n _ hn σ
    obtain ⟨x, hx, hx'⟩ := hσ _ hz
    obtain ⟨y, hy, hy'⟩ := Scheme.exists_preimage_of_isPullback h.1 _ _ hx'
    refine ⟨θ, y, hθ y ?_, hy'⟩
    have e : n y = x := (Q.G.hom ⁻¹ᵁ N).ι.isOpenEmbedding.injective
      ((congrArg (fun q => q y) hn).trans hy)
    rwa [e]
  obtain ⟨D, A, U, hU, hP⟩ := H R hN hI hC G' ((cubeMapOf h).rigLB Q.L hL hr) c' W
    (semiPull ξ Q.G Q.semi) (hs Q.sym)
    (GlobalTheory.SymBaseChange.hypS_baseChange _ _ Q.G G' ξ _ Q.L.L _ Q.L.isLB hL h hrefl hS) hsp hθ' hne
    (Set.ext fun x => abLocus_pullback abLocusOne Q.semi h.1 x) hA'.proper
    (ha ha₀) (hk hk₀)
  exact ⟨D, A, U, by rw [hU]; exact hrefl, hP⟩

end GlobalTheory.ZH

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.RedGood

theorem wt_lin {k : Type} [Field k] (Φ : FibPre k) {d : ℕ} {J : Type} [Fintype J]
    {F : J → (Φ.H d).Sec} {a : J → k} {φ : (Φ.H d).Sec} (h : IsLin Φ.G.hom F a φ) (α : Φ.E.X)
    (l : Φ.N₀.ι) : Φ.wt φ α l = ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l := by
  rw [← WtLin.weight_sum Φ F a α l, ← h l]
  rfl

theorem constFn_zero {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) :
    constFn f U 0 = 0 := by
  simp only [constFn, map_zero]

theorem good_of_parts {k : Type} [Field k] (Φ : FibPre k) (N : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ)
    {J : Type} [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (R : J → Φ.E.X → (Φ.H 1).Sec)
    (pos : Filter.Tendsto q Filter.cofinite Filter.atTop) (short : ∀ i, Short q N (cls i))
    (uniq : ∀ i i', (∃ m, cls i = cls i' + N • m) → cls i = cls i')
    (cover : ∀ α, ∃ i m, α = cls i + N • m)
    (part : ∀ i α, Φ.IsPart α (F i) (R i α))
    (zero : ∀ i α, ¬ (Short q N α ∧ ∃ m, α = cls i + N • m) → ∀ l, Φ.wt (R i α) α l = 0)
    (basis : ∀ i₀ α, Short q N α → (∃ m, α = cls i₀ + N • m) → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ →
      ∃! a : {i // cls i = cls i₀} → k, IsLin Φ.G.hom (fun i : {i // cls i = cls i₀} => R i α) a φ) :
    Φ.Good N q cls F := by
  have hcls : ∀ i₀ i α, (∃ m, α = cls i₀ + N • m) → (∃ m, α = cls i + N • m) → cls i = cls i₀ := by
    rintro i₀ i α ⟨m, hm⟩ ⟨m', hm'⟩
    refine uniq i i₀ ⟨m - m', ?_⟩
    rw [smul_sub, ← add_sub_assoc, ← hm, hm', add_sub_cancel_right]
  have hsum : ∀ (i₀ : J) (α : Φ.E.X) (a : J → k), (∀ i, a i ≠ 0 → cls i = cls i₀) → ∀ l,
      ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l =
        ∑ i : {i // cls i = cls i₀}, constFn Φ.E.B.hom _ (a i) * Φ.wt (R i α) α l := by
    intro i₀ α a ha l
    rw [← Finset.sum_subtype (Finset.univ.filter fun i => cls i = cls i₀) (by simp)
      (fun i => constFn Φ.E.B.hom _ (a i) * Φ.wt (R i α) α l), Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [(part i α).2 l]
    · have : a i = 0 := by
        by_contra h
        exact hi (ha i h)
      rw [this, constFn_zero, zero_mul]
  refine ⟨pos, short, ?_, ?_, ?_⟩
  · rintro i β ⟨l, hl⟩
    by_contra h
    exact hl (((part i β).2 l).symm.trans (zero i β h l))
  · intro α hα φ hφ
    obtain ⟨i₀, hm⟩ := cover α
    obtain ⟨a, ha, -⟩ := basis i₀ α hα hm φ hφ
    have key : ∀ i, (if h : cls i = cls i₀ then a ⟨i, h⟩ else 0) ≠ 0 → cls i = cls i₀ := by
      intro i hi
      by_contra h
      exact hi (dif_neg h)
    refine ⟨fun i => if h : cls i = cls i₀ then a ⟨i, h⟩ else 0, fun i hi => ?_, fun l => ?_⟩
    · rw [key i hi]
      exact hm
    · rw [hsum i₀ α _ key l, wt_lin Φ ha α l]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dite_eq_left i.2]
  · intro α hα a ha h0
    obtain ⟨i₀, hm⟩ := cover α
    have key : ∀ i, a i ≠ 0 → cls i = cls i₀ := fun i hi => hcls i₀ i α hm (ha i hi)
    have hl := (GlobalTheory.SecRatio.ratio_and_lin _ _ (Φ.H_isLB 1)).2 k Φ.G.hom {i // cls i = cls i₀}
      (fun i => R i α)
    obtain ⟨φ, hφ, -⟩ := hl (fun i => a i)
    obtain ⟨φ₀, hφ₀, -⟩ := hl 0
    have hz₀ : ∀ β l, Φ.wt φ₀ β l = 0 := fun β l => by
      rw [wt_lin Φ hφ₀ β l]
      exact Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, constFn_zero, zero_mul]
    have hz : ∀ β l, Φ.wt φ β l = 0 := fun β l => by
      rw [wt_lin Φ hφ β l]
      by_cases hβ : β = α
      · subst hβ
        rw [← hsum i₀ β a key l, h0 l]
      · refine Finset.sum_eq_zero fun i _ => ?_
        have : Φ.wt (R i α) β l = 0 := by
          by_contra h
          exact hβ ((part i α).1 ⟨l, h⟩)
        rw [this, mul_zero]
    have e : φ = φ₀ := WtPart.sec_ext Φ φ φ₀ fun β l => (hz β l).trans (hz₀ β l).symm
    subst e
    have hu := (basis i₀ α hα hm φ (by rintro β ⟨l, hl⟩; exact absurd (hz β l) hl)).unique hφ hφ₀
    funext i
    by_contra h
    exact h (congrFun hu ⟨i, key i h⟩)

theorem residue_j_eq_zero {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) {a : u.V}
    (ha : a ∈ IsLocalRing.maximalIdeal u.V) : IsLocalRing.residue (OO p) (u.j a) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) a) *
      (b : PadicAlgCl p) = 1 := congrArg Subtype.val hb
  have h0 : algebraMap u.V (FractionRing u.V) a ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at hb'
    exact zero_ne_one hb'
  have hn : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) a)⁻¹‖ ≤ 1 := by
    rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hb']
    exact (mem_OO_iff _).1 b.2
  obtain ⟨c, hc⟩ := (u.norm_le _).1 hn
  refine ha (IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_))
  rw [map_mul, hc, map_one, mul_inv_cancel₀ h0]

theorem good_reduction : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N : ℕ) (fb : u.FibOf N), 1 ≤ N → ∀ (J : Type) [Fintype J] (σ : J → (u.H N).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB N α), u.Basis l N σ cls f → ∀ F : J → (fb.Φ.H 1).Sec, (∀ i α, fb.Φ.IsPart (fb.xe.symm α) (F i) (fb.red α (f i α))) → fb.Φ.Good N (l.q.comp fb.xe.toIntLinearEquiv.toLinearMap) (fun i => fb.xe.symm (cls i)) F := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l N fb hN J _ σ cls f hB F hF
  have hsh := GlobalTheory.T.adaptedBasis_terms_at_other_class_members hL o Ω S ρ p y₀ u l N hN J σ cls f hB
  obtain ⟨hshort, huniq, hcover, -, -, hzero, -⟩ := hB
  have hS : ∀ α : fb.Φ.E.X, Short (l.q.comp fb.xe.toIntLinearEquiv.toLinearMap) N α ↔ Short l.q N (fb.xe α) := by
    intro α
    constructor
    · intro h m
      simpa using h (fb.xe.symm m)
    · intro h m
      simpa using h (fb.xe m)
  have hC : ∀ (α : fb.Φ.E.X) (c : u.D.toPre.X),
      (∃ m, α = fb.xe.symm c + N • m) ↔ ∃ m, fb.xe α = c + N • m := by
    intro α c
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨fb.xe m, by simp⟩
    · rintro ⟨m, hm⟩
      exact ⟨fb.xe.symm m, fb.xe.injective (by simp [hm])⟩
  refine good_of_parts fb.Φ N _ _ F (fun i α => fb.red (fb.xe α) (f i (fb.xe α))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact l.pos.comp fb.xe.injective.tendsto_cofinite
  · intro i
    rw [hS, fb.xe.apply_symm_apply]
    exact hshort i
  · intro i i' h
    rw [hC, fb.xe.apply_symm_apply] at h
    rw [huniq i i' h]
  · intro α
    obtain ⟨i, h⟩ := hcover (fb.xe α)
    exact ⟨i, (hC _ _).2 h⟩
  · intro i α
    have := hF i (fb.xe α)
    rwa [fb.xe.symm_apply_apply] at this
  · intro i α h j
    rw [hS, hC] at h
    by_cases hc : ∃ m, fb.xe α = cls i + N • m
    · obtain ⟨a, β, ha, hβ⟩ := (hsh i _ hc).2 fun hs => h ⟨hs, hc⟩
      have := fb.lin _ Unit (fun _ => β) (fun _ => a) (f i (fb.xe α)) (fun j => by
        rw [hβ j, Fintype.sum_unique])
      rw [wt_lin fb.Φ this α j, Fintype.sum_unique, residue_j_eq_zero u ha, constFn_zero, zero_mul]
    · have := fb.lin _ Empty Empty.elim Empty.elim (f i (fb.xe α)) (fun j => by
        rw [hzero i _ (fun m e => hc ⟨m, e⟩) j, Fintype.sum_empty])
      rw [wt_lin fb.Φ this α j, Fintype.sum_empty]
  · intro i₀ α hα hc φ hφ
    rw [hS] at hα
    rw [hC] at hc
    have hb := fb.basis _ _ _ ((hsh i₀ _ hc).1 hα) φ (by rwa [fb.xe.symm_apply_apply])
    let e : {i // cls i = cls i₀} ≃ {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} :=
      Equiv.subtypeEquivRight fun i => fb.xe.symm.injective.eq_iff.symm
    have hlin : ∀ a : {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} → kb p,
        IsLin fb.Φ.G.hom (fun i : {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} =>
          fb.red (fb.xe α) (f i (fb.xe α))) a φ ↔
        IsLin fb.Φ.G.hom (fun i : {i // cls i = cls i₀} => fb.red (fb.xe α) (f i (fb.xe α))) (a ∘ e) φ := by
      intro a
      refine forall_congr' fun j => ?_
      rw [← e.sum_comp]
      rfl
    obtain ⟨a, ha, hu⟩ := hb
    refine ⟨a ∘ e.symm, (hlin _).2 ?_, fun b hb => ?_⟩
    · have : (a ∘ e.symm) ∘ e = a := by
        funext i
        simp
      rw [this]
      exact ha
    · rw [← hu _ ((hlin b).1 hb)]
      funext i
      simp

end GlobalTheory.ZH.RedGood
end
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.div_iff_mem_nonzeroLocus_and_crd_ratio : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (N : RatModel o Ω) (X : Scheme.{0}) (a : N.Z ⟶ X) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω), H.IsLB → ⨆ j, nonzeroLocus (s j) = ⊤ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ N.Z) (v : J → K) (k : J), Crd H s (x ≫ a) v → N.Div t k (x (IsLocalRing.closedPoint K)) → v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k := by
  first | exact @GlobalTheory.ZH.DivCrd.div_iff_mem_nonzeroLocus | exact GlobalTheory.ZH.DivCrd.div_iff_mem_nonzeroLocus | (intros; apply GlobalTheory.ZH.DivCrd.div_iff_mem_nonzeroLocus <;> assumption)
end
