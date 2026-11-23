module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle078
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle108
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.Bundle001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle106
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClosLift

theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (OO p).subtype)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).1 (OO p).subtype_injective]
  exact bot_le

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}

theorem big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  rw [ρ.N_eq]
  have h1 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  nlinarith

theorem gPt_j {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) :
    gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V :=
  (spMap_comp' _ _).trans (spMap_comp' (algebraMap u.V (FractionRing u.V)) (algebraMap (FractionRing u.V) (PadicAlgCl p))).symm

theorem exists_generic {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} {p : ℕ}
    [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u}
    (tm : Q.TMap t c) (x : Sp (PadicAlgCl p) ⟶ Q.P.left) (hx : x ≫ Q.P.hom = gPt p ≫ y) :
    ∃ a : Sp (PadicAlgCl p) ⟶ t.u.G.left, a ≫ t.u.G.hom = gPt p ≫ spMap t.u.j ∧
      a ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x := by
  set κ := spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) with hκ
  have h1 : x ≫ Q.P.hom = (κ ≫ c.yK) ≫ U₀.ι := by
    rw [hx, Category.assoc, c.yK_fac, ← Category.assoc, ← gPt_j, Category.assoc, c.fac]
  let a1 := Q.cart.lift x (κ ≫ c.yK) h1
  have e1 : a1 ≫ Q.a₀ = x := Q.cart.lift_fst _ _ _
  have e2 : a1 ≫ pullback.snd _ _ = κ ≫ c.yK := Q.cart.lift_snd _ _ _
  have h2 : (a1 ≫ pullback.fst _ _) ≫ ρ.P.A.hom = κ ≫ spMap t.u.yK := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, e2, Category.assoc, c.yK_u]
  let a2 := t.u.cart.1.lift (a1 ≫ pullback.fst _ _) κ h2
  have e3 : a2 ≫ t.u.φ = a1 ≫ pullback.fst _ _ := t.u.cart.1.lift_fst _ _ _
  have e4 : a2 ≫ t.u.A.A.hom = κ := t.u.cart.1.lift_snd _ _ _
  let a3 : Sp (PadicAlgCl p) ⟶ pullback t.u.G.hom (jK t.u.V) := a2 ≫ t.u.U.gen.inv.left
  have e5 : a3 ≫ pullback.snd _ _ = κ := by
    rw [← e4]
    exact (Category.assoc _ _ _).trans (congrArg (a2 ≫ ·) (Over.w t.u.U.gen.inv))
  have e6 : a3 ≫ t.u.U.gen.hom.left = a2 := by
    refine (Category.assoc _ _ _).trans ((congrArg (a2 ≫ ·) ?_).trans (Category.comp_id _))
    exact congrArg CommaMorphism.left t.u.U.gen.inv_hom_id
  have e7 : a3 ≫ tm.φ = a1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, tm.φ_fst, ← e3, ← e6]
      exact (Category.assoc _ _ _).symm
    · rw [Category.assoc, tm.φ_snd, ← Category.assoc, e5, e2]
  refine ⟨a3 ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, e5, gPt_j]
  · rw [Category.assoc, ← tm.φ_f, ← Category.assoc, e7, e1]

theorem exists_lift : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ b : Sp (OO p) ⟶ Q.P.left, b ≫ Q.P.hom = y → ⊤ ≤ b ⁻¹ᵁ Q.G → ∃ c' : Sp (OO p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = b := by
  intro _ o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hbig b hb hG
  have hW : ⊤ ≤ b ⁻¹ᵁ (Q.P.hom ⁻¹ᵁ Q.W tm.l) := by
    rw [← Scheme.Hom.comp_preimage, hb]
    exact (CrdCalc.top_le_iff y _).2 tm.mem
  obtain ⟨b', hb'⟩ : ∃ b' : Sp (OO p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme, b' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = b :=
    ⟨IsOpenImmersion.lift _ b (by
      rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff _ _).1 hW), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨w', hw'⟩ := CrdCalc.crd_exists (pull_isLB Q.isLB (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) b'
  have hdet : ∀ {R : Type} [CommRing R] (ψ : t.u.V →+* R), IsUnit (tm.m.map ψ).det := fun ψ => by
    have := tm.unit.map ψ
    rwa [RingHom.map_det] at this
  obtain ⟨w, rfl⟩ : ∃ w, w' = (tm.m.map t.u.j).mulVec w :=
    ⟨(tm.m.map t.u.j)⁻¹.mulVec w', by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet _), Matrix.one_mulVec]⟩
  have hmap : ∀ {R : Type} [CommRing R] (ψ : OO p →+* R), Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l)
      (spMap ψ ≫ b') ((tm.m.map (ψ.comp t.u.j)).mulVec fun i => ψ (w i)) := fun ψ => by
    have := CrdCalc.crd_map ψ hw'
    refine (congrArg _ (funext fun i => ?_)).mp this
    exact RingHom.map_mulVec ψ _ _ i
  obtain ⟨i₀, hi₀, hne⟩ := (GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig (rPt p ≫ b')
    (fun i => IsLocalRing.residue (OO p) (w i))
    (by rw [Category.assoc, ← Category.assoc b', hb', hb]) (hmap _)).1 (by
      rw [Category.assoc, hb']
      exact fun z _ => hG (Set.mem_univ (rPt p z)))
  have hu : IsUnit (w i₀) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hne
  have hn : 1 ≤ ‖(w i₀ : PadicAlgCl p)‖ := not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hu
  obtain ⟨a, ha, haf⟩ := exists_generic tm (gPt p ≫ b) (by rw [Category.assoc, hb])
  have haf' : a ≫ tm.f = gPt p ≫ b' := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι, Category.assoc, haf, Category.assoc, hb']
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists t.mod.isLB t.σ a
  have h1 := tm.crd _ ((OO p).subtype.comp t.u.j) a v (ha.trans (spMap_comp' _ _)) hv
  rw [haf'] at h1
  obtain ⟨κ, hκ⟩ := CrdCalc.crd_unique h1 (hmap (OO p).subtype)
  have h2 : (fun i => (OO p).subtype (w i)) = fun i => (κ : PadicAlgCl p) * v i := by
    refine Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (hdet ((OO p).subtype.comp t.u.j))) ?_
    have : (fun i => (κ : PadicAlgCl p) * v i) = (κ : PadicAlgCl p) • v := rfl
    rw [this, Matrix.mulVec_smul]
    exact funext hκ
  have h3 := CrdCalc.crd_smul κ hv
  rw [← h2] at h3
  obtain ⟨c', hc', hc''⟩ := GlobalTheory.T.isIntegral_of_weightZeroCoordinate_dominates p t.u.V t.u.j t.u.G S.g S.N (S.r * S.N) _ t.l.q _ S.J t.σ t.cls t.mod
    (big ρ hbig) a _ ha h3 ⟨i₀, hi₀, fun i => ((mem_OO_iff _).1 (w i).2).trans hn⟩
  refine ⟨c', hc', ?_⟩
  have := isDominant_gPt p
  have := Q.proper
  refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ (gPt p) ?_
  · rw [Category.assoc, Category.assoc, tm.f_over, ← Category.assoc, hc', c.fac, hb]
  · rw [← Category.assoc, hc'', haf]

end GlobalTheory.ZH.ClosLift
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem relAmple_of_finite_etale_isogeny : ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ ψ : A ⟶ B, IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → ∀ (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB → LBIso L (M.pull ψ.left) → Out.RelAmple A L → Out.RelAmple B M := by
  intro k _ _ A B _ _ hA hB ψ _ hf he hs L M hL hM hiso hamp
  have hN : IsLocallyNoetherian (Sp k) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of k)))
  have h₁ := (GlobalTheory.relAmple_finite_pow_iso (Sp k) A A (𝟙 A) L 1 one_pos hA hA hL
    (by simpa using (inferInstance : IsFinite (𝟙 A.left)))).2.2.2 (M.pull ψ.left) (LB.isLB_pull hM ψ.left) hiso hamp
  exact (GlobalTheory.relAmple_finite_pow_iso (Sp k) A B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs h₁

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.isProper_of_powerSeries_arcs_over_algClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Over (Sp k)) [IsIntegral X.left], IsSeparated X.hom → LocallyOfFiniteType X.hom → QuasiCompact X.hom → (∀ a : Sp (FractionRing (PowerSeries k)) ⟶ X.left, a ≫ X.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) → ∃ b : Sp (PowerSeries k) ⟶ X.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a) → IsProper X.hom := by
  first | exact @GlobalTheory.ArcProper.isProper_of_arcs | exact GlobalTheory.ArcProper.isProper_of_arcs | (intros; apply GlobalTheory.ArcProper.isProper_of_arcs <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenSpread

set_option backward.isDefEq.respectTransparency false

theorem map_linComb_pts {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S}
    {T' : Over S'} (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G')) (a : Fin n → ℕ) :
    ρ (linComb x a) = linComb (fun i => ρ (x i)) a := by
  unfold linComb
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact map_pow ρ _ _

theorem linComb_left_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T' : Over S'} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (baseOver S ⟶ G)) (hx : ∀ i, (x' i).left ≫ φ = (T'.hom ≫ f) ≫ (x i).left) (a : Fin n → ℕ) :
    (linComb x' a).left ≫ φ = (T'.hom ≫ f) ≫ (linComb x a).left := by
  let U : Over.mk (T'.hom ≫ f) ⟶ baseOver S := Over.homMk (T'.hom ≫ f) (Category.comp_id _)
  have hx' : ∀ i, pushPt h.1.w (x' i) = U ≫ x i := fun i => Over.OverMorphism.ext (hx i)
  have e : pushPt h.1.w (linComb x' a) = U ≫ linComb x a :=
    (map_linComb_pts (pushHom h T') x' a).trans ((congrArg (fun z => linComb z a) (funext hx')).trans
      (map_linComb_pts (preHom U) x a).symm)
  exact congrArg (fun z => z.left) e

theorem exists_forall_sections_ne {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} [IsSeparated G.hom]
    {z z' : baseOver (Sp R) ⟶ G} (hz : z ≠ z') :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X : Scheme.{0}) [Nonempty X] (s : X ⟶ Sp R'), (s ≫ spMap g) ≫ z.left ≠ (s ≫ spMap g) ≫ z'.left := by
  let j : (equalizer z z').left ⟶ Sp R := (equalizer.ι z z').left
  have hj : IsClosedImmersion j := isClosedImmersion_equalizer_ι_left z z'
  have hC : IsClosed (Set.range j) := j.isClosedEmbedding.isClosed_range
  have hg : genericPoint (Sp R) ∉ Set.range j := by
    intro hg
    have hd : IsDominant j := by
      refine ⟨?_⟩
      rw [DenseRange, dense_iff_closure_eq, hC.closure_eq]
      exact Set.eq_univ_of_univ_subset (((genericPoint_spec (Sp R)).mem_closed_set_iff hC).1 hg)
    refine hz (Over.OverMorphism.ext ?_)
    have hr : IsReduced (baseOver (Sp R)).left := inferInstanceAs (IsReduced (Sp R))
    refine ext_of_isDominant_of_isSeparated G.hom ((Over.w z).trans (Over.w z').symm) j ?_
    exact congrArg (fun u => u.left) (equalizer.condition z z')
  obtain ⟨a, ha, H⟩ := exists_forall_mem (V := ⟨(Set.range j)ᶜ, hC.isOpen_compl⟩) hg
  refine ⟨a, ha, fun R' _ g hga X hX s e => ?_⟩
  obtain ⟨x⟩ := hX
  let U : Over.mk (s ≫ spMap g) ⟶ baseOver (Sp R) := Over.homMk (s ≫ spMap g) (Category.comp_id _)
  have hU : U ≫ z = U ≫ z' := Over.OverMorphism.ext e
  have hl : (equalizer.lift U hU).left ≫ j = s ≫ spMap g := congrArg (fun u => u.left) (equalizer.lift_ι U hU)
  refine H R' g hga (s x) ⟨(equalizer.lift U hU).left x, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hl]
  rfl

theorem exists_forall_linComb_injective : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSeparated G.hom → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∀ (n k : ℕ) (y : Fin n → (baseOver (Sp R) ⟶ G)) (y₀ : Fin n → (baseOver (Sp K) ⟶ A)), (∀ i, (y₀ i).left ≫ φ = spMap (algebraMap R K) ≫ (y i).left) → (∀ c c' : Fin n → Fin k, linComb y₀ (fun i => (c i : ℕ)) = linComb y₀ (fun i => (c' i : ℕ)) → c = c') → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] (π : G'.left ⟶ G.left) (y' : Fin n → (baseOver (Sp R') ⟶ G')), IsGrpPullback G' G (spMap g) π → (∀ i, (y' i).left ≫ π = spMap g ≫ (y i).left) → ∀ (F : Type) [Field F] [IsAlgClosed F] (s : Spec (CommRingCat.of F) ⟶ Sp R') (c c' : Fin n → Fin k), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i) (fun i => (c' i : ℕ)) → c = c' := by
  intro R K _ _ _ _ _ _ G _ A _ φ hsep hA n k y y₀ hy hind
  have key : ∀ p : (Fin n → Fin k) × (Fin n → Fin k), ∃ a : R, a ≠ 0 ∧
      ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
        ∀ (X : Scheme.{0}) [Nonempty X] (s : X ⟶ Sp R'),
          (s ≫ spMap g) ≫ (linComb y (fun i => (p.1 i : ℕ))).left =
            (s ≫ spMap g) ≫ (linComb y (fun i => (p.2 i : ℕ))).left → p.1 = p.2 := by
    rintro ⟨c, c'⟩
    by_cases hc : c = c'
    · exact ⟨1, one_ne_zero, fun _ _ _ _ _ _ _ _ => hc⟩
    have hne : linComb y (fun i => (c i : ℕ)) ≠ linComb y (fun i => (c' i : ℕ)) := by
      intro e
      refine hc (hind c c' (Over.OverMorphism.ext (hA.1.hom_ext ?_ ?_)))
      · have hy' : ∀ i, (y₀ i).left ≫ φ =
            ((baseOver (Sp K)).hom ≫ spMap (algebraMap R K)) ≫ (y i).left := fun i =>
          (hy i).trans (congrArg (· ≫ (y i).left) (Category.id_comp _).symm)
        rw [linComb_left_push hA y₀ y hy', linComb_left_push hA y₀ y hy', e]
      · exact (Over.w _).trans (Over.w _).symm
    obtain ⟨a, ha, H⟩ := exists_forall_sections_ne hne
    exact ⟨a, ha, fun R' _ g hg X _ s e => (H R' g hg X s e).elim⟩
  choose a ha H using key
  refine ⟨∏ p, a p, Finset.prod_ne_zero_iff.2 fun p _ => ha p, ?_⟩
  intro R' _ g hg G' _ π y' hπ hy' F _ _ s c c' e
  have hu : IsUnit (g (a (c, c'))) :=
    isUnit_of_dvd_unit (map_dvd g (Finset.dvd_prod_of_mem a (Finset.mem_univ _))) hg
  refine H (c, c') R' g hu _ s ?_
  have hx : ∀ i, ((Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i).left ≫ π =
      ((Over.mk s).hom ≫ spMap g) ≫ (y i).left := fun i => by
    show (s ≫ (y' i).left) ≫ π = (s ≫ spMap g) ≫ (y i).left
    rw [Category.assoc, hy' i, Category.assoc]
  have e₁ := linComb_left_push hπ _ y hx (fun i => (c i : ℕ))
  have e₂ := linComb_left_push hπ _ y hx (fun i => (c' i : ℕ))
  rw [e] at e₁
  exact e₁.symm.trans e₂

end GlobalTheory.GenSpread
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem exists_rigidified : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Rigidified A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Rigidified G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ _ _ hL _ _ _
  obtain ⟨i, hi⟩ := exists_chart hL (eSec G (genericPoint (Sp R)))
  obtain ⟨a, ha, H⟩ := exists_forall_mem (R := R) (V := eSec G ⁻¹ᵁ L.U i) hi
  refine ⟨a, ha, fun R' _ g hg G' _ _ π L' h hL' ⟨w, hw⟩ => ?_⟩
  obtain ⟨t, ht⟩ := AbSquare.exists_gen_of_mem_chart hL (K := PUnit) (fun _ => eSec G' ≫ π) (fun _ => 1)
    (fun _ => i) (fun _ y => (congrArg (fun q => q y ∈ L.U i) (PolBaseChange.eSec_comm h)).mpr (H R' g hg y))
  exact exists_down ((isGen_iff w).1 hw) hL hL' t ht

end GlobalTheory.GenSpread
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.relAmple_lift_squareZero_thickening : ∀ (A A' : Type) [CommRing A] [CommRing A'] (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X : Over (Spec (CommRingCat.of A))) (X' : Over (Spec (CommRingCat.of A'))) (β : X'.left ⟶ X.left), IsPullback β X'.hom X.hom (Spec.map (CommRingCat.ofHom g)) → LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L' : LB X'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull β) → RelAmple X' L' → RelAmple X L := by
  first | exact @GlobalTheory.AmpleThickening.relAmple_of_sq_zero | exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero | (intros; apply GlobalTheory.AmpleThickening.relAmple_of_sq_zero <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

theorem _root_.GlobalTheory.T.companionTheory_om_of_tests_torsionSections : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), C.HasTests → T.BTest L → C.TorsSec n → T.Few n → L.CompanionTheory (T.Om L) := by
  first | exact @GlobalTheory.ZJ.Core.Law.six_of_few | exact GlobalTheory.ZJ.Core.Law.six_of_few | (intros; apply GlobalTheory.ZJ.Core.Law.six_of_few <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.semistable_of_potential_semiAbelian_model : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G)) → SemistableReductionZero ∧ SemistableCompleteSplit := by
  first | exact @GlobalTheory.SS.semistable_of_potModel_semiAbelian | exact GlobalTheory.SS.semistable_of_potModel_semiAbelian | (intros; apply GlobalTheory.SS.semistable_of_potModel_semiAbelian <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_finite_splitTorusExtension_of_torusExtension : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExt G) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k'), Nonempty (TorusExtension (fieldBaseChange k k' G)) := by
  first | exact @GlobalTheory.SS.exists_finite_torusExtension_of_torusExt | exact GlobalTheory.SS.exists_finite_torusExtension_of_torusExt | (intros; apply GlobalTheory.SS.exists_finite_torusExtension_of_torusExt <;> assumption)
end
