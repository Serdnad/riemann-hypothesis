module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfInd
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle023
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpairAlg
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpairGeo
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem PositivityTheory.HtPt.Htat.SubgroupHopfOrder.btOrder_isHopfOrder_of_finOpenSub :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) := by
  intro R _ _ _ T _ _ Γ U hU
  obtain ⟨H, A, hH, hA, hAf⟩ := PositivityTheory.HtPt.Twhopf.sub_order R T Γ U hU
  have key : Γ.btOrder U = indOrder H.subtype A := by
    ext f
    rw [PositivityTheory.HtPt.Twhopf.mem_order R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Twhopf.reg_iff R T Γ U _).1 (hf t)
      exact (hAf _).2 ⟨s, fun t' h => hs t' h⟩
    · intro hf t
      refine (PositivityTheory.HtPt.Twhopf.reg_iff R T Γ U _).2 ?_
      obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
      exact ⟨s, fun t' h => hs ⟨t', (hH t').2 h⟩ h⟩
  rw [key]
  exact PositivityTheory.HtPt.Twhopf.ind_hopf R T H H.subtype H.subtype_injective A hA

theorem PositivityTheory.HtPt.Htat.bt_sub_hopf : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) :=
  @PositivityTheory.HtPt.Htat.SubgroupHopfOrder.btOrder_isHopfOrder_of_finOpenSub
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Htat.HTBaseChange

theorem valAt_comp_top {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (x ≫ f) ⊤ le_top s = valAt x ⊤ le_top (f.appTop.hom s) := by
  unfold valAt
  congr 1

theorem valAt_spec_map {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (ψ : B →+* C)
    (y : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom ψ) ≫ y) ⊤ le_top s = ψ (valAt y ⊤ le_top s) := by
  rw [valAt_comp_top]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have := congrArg (fun φ => φ.hom (y.appTop.hom s)) h
  simp only [CommRingCat.comp_apply] at this
  exact this

abbrev qmap {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (N : ℕ) :
    R ⧸ Ideal.span {(N : R)} →+* R' ⧸ Ideal.span {(N : R')} :=
  Ideal.quotientMap (Ideal.span {(N : R')}) (algebraMap R R')
    (Ideal.span_le.2 (by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp only [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.subset_span rfl))

end PositivityTheory.HtPt.Htat.HTBaseChange


open PositivityTheory.HtPt.Htat.HTBaseChange in
theorem PositivityTheory.HtPt.Htat.ht_bc : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) → ∀ (L' : Type) [AddCommGroup L'] [Module R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →+ L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → Submodule.span R' (Set.range β) = ⊤ → ∀ (χ : T →* Rˣ) (w : Module.Dual R L) (w' : Module.Dual R' L'), (∀ e, w' (β e) = algebraMap R R' (w e)) → Γ.IsHT i M N χ w → Γ'.IsHT (F ≫ i) M' N ((Units.map (algebraMap R R' : R →* R')).comp χ) w' := by
  intro R _ _ T _ _ Γ S G _ _ x N i hi L _ _ M R' _ _ _ Γ' F hF hi' L' _ _ M' β hβ hspan χ w w' hw hHT
  obtain ⟨s, hs, hv⟩ := hHT
  have hs' : Γ'.HasValues (F.appTop.hom s)
      (fun t => (((Units.map (algebraMap R R' : R →* R')).comp χ t : R'ˣ) : R')) := by
    obtain ⟨B, instB, ib, j, j', σ, hj, hji, hj'i, -, hσj, hσj'⟩ := hF.pts
    intro t
    have hb : valAt (σ t) ⊤ le_top s = ib (χ t) := by
      apply hj
      rw [← PositivityTheory.HtPt.Htat.HTBaseChange.valAt_spec_map, hσj, hs t, ← RingHom.comp_apply, hji]
    show valAt (Γ'.pt t).left ⊤ le_top (F.appTop.hom s) = _
    rw [← PositivityTheory.HtPt.Htat.HTBaseChange.valAt_comp_top, ← hσj', PositivityTheory.HtPt.Htat.HTBaseChange.valAt_spec_map, hb, ← RingHom.comp_apply, hj'i]
    simp
  obtain ⟨l', hl'⟩ := PositivityTheory.HtPt.Htat.ht_linear R' T Γ' S G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) hi'
    L' M' ((Units.map (algebraMap R R' : R →* R')).comp χ) (F.appTop.hom s) hs'
  have key : ∀ e, l' (β e) = Ideal.Quotient.mk (Ideal.span {(N : R')}) (w' (β e)) := by
    intro e
    obtain ⟨v, hv1, hv2, hv3⟩ := hv e
    have hc : (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (PositivityTheory.HtPt.Htat.HTBaseChange.qmap (R := R) (R' := R') N))) ≫ v) ≫ Γ.G.hom =
        Spec.map (CommRingCat.ofHom ((algebraMap (R' ⧸ Ideal.span {(N : R')})
          (DualNumber (R' ⧸ Ideal.span {(N : R')}))).comp (Ideal.Quotient.mk _))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
      rw [Category.assoc, hv1, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      all_goals simp [GlobalTheory.CompanionTheory.Ar.dualMap, PositivityTheory.HtPt.Htat.HTBaseChange.qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
    set v'' := hF.cart.lift _ _ hc with hv''
    have h1 := hF.cart.lift_fst _ _ hc
    have h2 := hF.cart.lift_snd _ _ hc
    rw [← hv''] at h1 h2
    have h3 : v'' ≫ F ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R')})))) ≫
        (M'.pt (β e)).left := by
      rw [← Category.assoc, h1, Category.assoc, hv2, hβ e, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp]
      congr 2
      ext a
      all_goals simp [GlobalTheory.CompanionTheory.Ar.dualMap, PositivityTheory.HtPt.Htat.HTBaseChange.qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
    have h4 := hl' (β e) v'' ⟨h2, h3⟩
    rw [← PositivityTheory.HtPt.Htat.HTBaseChange.valAt_comp_top, h1, PositivityTheory.HtPt.Htat.HTBaseChange.valAt_spec_map, hv3] at h4
    have h5 := congrArg TrivSqZeroExt.snd h4
    simp only [GlobalTheory.CompanionTheory.Ar.dualMap, PositivityTheory.HtPt.Htat.HTBaseChange.qmap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, zero_add, add_zero, Ideal.quotientMap_mk] at h5
    rw [← h5, hw]
  have heq : l' = (Ideal.Quotient.mkₐ R' (Ideal.span {(N : R')})).toLinearMap.comp w' :=
    LinearMap.ext_on_range hspan (fun e => by simpa using key e)
  refine ⟨F.appTop.hom s, hs', fun e' => ?_⟩
  obtain ⟨v', ⟨hv'1, hv'2⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_dual_number R' T Γ' S G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N
    (F ≫ i) hi' L' M' e'
  refine ⟨v', hv'1, hv'2, ?_⟩
  rw [hl' e' v' ⟨hv'1, hv'2⟩, heq]
  simp
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Mg

abbrev extPt {X : Scheme.{0}} {k K : Type} [Field k] [Field K] (i : k →+* K) (x : Sp k ⟶ X) :
    Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl

theorem epi_spMap {k K : Type} [Field k] [Field K] (i : k →+* K) : Epi (spMap i) := by
  have : Surjective (spMap i) :=
    ⟨fun z => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem extPt_inj {X : Scheme.{0}} {k K : Type} [Field k] [Field K] (i : k →+* K) (x : Sp k ⟶ X) {G : Over X}
    {a b : Over.mk x ⟶ G} (h : extPt i x ≫ a = extPt i x ≫ b) : a = b := by
  have := epi_spMap i
  have h' : spMap i ≫ a.left = spMap i ≫ b.left := congrArg (fun q => q.left) h
  exact Over.OverMorphism.ext ((cancel_epi (spMap i)).1 h')

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {X : Scheme.{0}}
  {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ} {z : Ωˣ} {ev : D.La → (Over.mk ξ ⟶ t.G)}

theorem full_iso (h : IsFullLevelAt D t ξ N z ev) (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) :
    ∃ I : TateIsoAt D t (spMap i ≫ ξ), I.ζ N = Units.map i.toMonoidHom z ∧ ∀ a, I.ev N a = extPt i ξ ≫ ev a := by
  obtain ⟨I, h1, h2⟩ := h k i
  exact ⟨I, Units.ext h1, fun a => Over.OverMorphism.ext (h2 a)⟩

theorem full_desc (hN : 0 < N) (h : IsFullLevelAt D t ξ N z ev) (k : Type) [Field k] (i : Ω →+* k)
    (g : Over.mk (spMap i ≫ ξ) ⟶ t.G) (hg : g ^ N = 1) : ∃ a, g.left = spMap i ≫ (ev a).left := by
  let j : k →+* AlgebraicClosure k := algebraMap _ _
  obtain ⟨I, -, h2⟩ := h (AlgebraicClosure k) (j.comp i)
  let u : Over.mk (spMap (j.comp i) ≫ ξ) ⟶ Over.mk (spMap i ≫ ξ) :=
    Over.homMk (spMap j) (by simp [spMap_comp])
  obtain ⟨a, ha⟩ := (I.onto N hN (u ≫ g)).1 (by rw [← MonObj.comp_pow, hg, MonObj.comp_one])
  refine ⟨a, ?_⟩
  have := epi_spMap j
  have e : spMap j ≫ g.left = (I.ev N a).left := by rw [ha]; rfl
  rw [← cancel_epi (spMap j), e, h2, spMap_comp, Category.assoc]

theorem level_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ), 0 < N → ∀ (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → IsPrimitiveRoot z N ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (r : 𝓞 E) a, ev (r • a) = ev a ≫ t.act.act r) ∧ (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ g : Over.mk ξ ⟶ t.G, g ^ N = 1 ↔ ∃ a, ev a = g) ∧ FullTorsion t.G ξ N ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (a b : D.La) (g g' : Over.mk (spMap i ≫ ξ) ⟶ t.G), g.left = spMap i ≫ (ev a).left → g'.left = spMap i ≫ (ev b).left → Out.WeilIs t.G t.PP.L N g g' (unitOn (Units.map i.toMonoidHom z ^ D.EF a b)) := by
  intro E _ _ _ H D X t Ω _ ξ N hN z ev h
  let j : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  obtain ⟨I, h1, h2⟩ := full_iso h (AlgebraicClosure Ω) j
  refine ⟨?_, fun a b => ?_, fun r a => ?_, fun a => ?_, fun g => ?_, fun k _ i g hg => ?_,
    fun k _ _ i a b g g' hg hg' => ?_⟩
  · refine IsPrimitiveRoot.of_map_of_injective (f := Units.map j.toMonoidHom) ?_ (Units.map_injective j.injective)
    rw [← h1]
    exact I.ζ_prim N hN
  · apply extPt_inj j
    rw [MonObj.comp_mul, ← h2, ← h2, ← h2, I.add]
  · apply extPt_inj j
    rw [← h2, I.lin, h2, Category.assoc]
  · rw [← I.ker N hN a, h2]
    exact ⟨fun e => by rw [e, MonObj.comp_one], fun e => extPt_inj j ξ (by rw [e, MonObj.comp_one])⟩
  · constructor
    · intro hg
      obtain ⟨a, ha⟩ := (I.onto N hN (extPt j ξ ≫ g)).1 (by rw [← MonObj.comp_pow, hg, MonObj.comp_one])
      exact ⟨a, extPt_inj j ξ (by rw [← h2, ha])⟩
    · rintro ⟨a, rfl⟩
      apply extPt_inj j
      rw [MonObj.comp_pow, ← h2, MonObj.comp_one]
      exact (I.onto N hN _).2 ⟨a, rfl⟩
  · obtain ⟨a, ha⟩ := full_desc hN h k i g hg
    exact ⟨ev a, ha⟩
  · obtain ⟨J, e1, e2⟩ := full_iso h k i
    have hg1 : g = J.ev N a := by rw [e2]; exact Over.OverMorphism.ext hg
    have hg2 : g' = J.ev N b := by rw [e2]; exact Over.OverMorphism.ext hg'
    rw [hg1, hg2, ← e1]
    exact J.isom N hN a b

theorem finrank_La (D : Datum H) : Module.Free ℤ D.La ∧ Module.Finite ℤ D.La ∧
    Module.finrank ℤ D.La = Module.finrank ℚ E * (D.p + D.q) := by
  have := D.fin
  refine ⟨GlobalTheory.datum_free_int D, Module.Finite.trans (𝓞 E) D.La, ?_⟩
  rw [GlobalTheory.finrank_int_eq_mul_of_finite (O := 𝓞 E), D.rank, RingOfIntegers.rank]

end PositivityTheory.HtPt.Mg
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Twpair

theorem tw_pair : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, ζ n ^ p ^ n = 1) → X.PairingRegular B ζ → ∀ n, ∃ s ∈ prodSpan ((X.Γ n).btOrder ⊤), ∀ a b, s (lev p n a, lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p hpp C _ _ _ v O _ _ _ hv _ _ S _ G _ _ _ y La _ _ _ X B ζ hζ hreg n
  have : ValuationRing O := ValuationRing.of_integers v hv
  have := finite_levGrp (La := La) hpp.out.ne_zero n
  obtain ⟨β, hβ⟩ := exists_bichar p n B (ζ n) (hζ n)
  obtain ⟨s, hs⟩ := hreg n
  refine ⟨_, bichar_mem_prodSpan (henselian hv) (fun P => ?_) (X.Γ n) β s fun a b => ?_, fun a b => ?_⟩
  · exact (prime_eq_bot_or_maximal hv P.asIdeal).imp id fun h => PrimeSpectrum.ext h
  · obtain ⟨a, rfl⟩ := lev_surjective p n a
    obtain ⟨b, rfl⟩ := lev_surjective p n b
    rw [hβ]
    exact hs a b
  · exact congrArg Units.val (hβ a b)

end PositivityTheory.HtPt.Twpair
end

section

noncomputable section

namespace PositivityTheory.HtPt.Htat

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT

theorem inj_mod_of_surj_mod {M : Type} [AddCommGroup M] [Module.Finite ℤ M] (f : M →ₗ[ℤ] M) (q : ℕ)
    (hs : ∀ a, ∃ z b, a = f z + q • b) (z b : M) (h : f z = q • b) : ∃ z', z = q • z' := by
  let K : Submodule ℤ M := LinearMap.range (q • (LinearMap.id : M →ₗ[ℤ] M))
  have hK : ∀ a, a ∈ K ↔ ∃ b, a = q • b := fun a =>
    ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hle : K ≤ K.comap f := by
    intro a ha
    obtain ⟨b, rfl⟩ := (hK a).1 ha
    exact (hK _).2 ⟨f b, map_nsmul f q b⟩
  let g := K.mapQ K f hle
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨a, rfl⟩ := K.mkQ_surjective a
    obtain ⟨z, b, rfl⟩ := hs a
    refine ⟨K.mkQ z, ?_⟩
    show K.mkQ (f z) = _
    rw [map_add (f := _), show K.mkQ (q • b) = 0 from (Submodule.Quotient.mk_eq_zero K).2 ((hK _).2 ⟨b, rfl⟩), add_zero]
  have hi := OrzechProperty.injective_of_surjective_endomorphism g hg
  have h0 : g (K.mkQ z) = g 0 := by
    rw [map_zero]
    exact (Submodule.Quotient.mk_eq_zero K).2 ((hK _).2 ⟨b, h⟩)
  exact (hK z).1 ((Submodule.Quotient.mk_eq_zero K).1 (hi h0))

theorem surj_mod_pow {M L : Type} [AddCommGroup M] [AddCommGroup L] (σ : M →+ L) (p : ℕ)
    (h : ∀ a, ∃ z b, a = σ z + p • b) (n : ℕ) (a : L) : ∃ z b, a = σ z + (p ^ n) • b := by
  induction n with
  | zero => exact ⟨0, a, by simp⟩
  | succ n ih =>
    obtain ⟨z, b, rfl⟩ := ih
    obtain ⟨z', b', rfl⟩ := h b
    exact ⟨z + (p ^ n) • z', b', by rw [map_add (f := _), map_nsmul, smul_add, pow_succ, mul_smul, add_assoc]⟩

theorem perfect_mod {M L : Type} [AddCommGroup M] [AddCommGroup L] [Module.Free ℤ L] (σ : M →ₗ[ℤ] L) (q : ℕ)
    (EF : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) (hE : Function.Bijective EF) (hs : ∀ a, ∃ z b, a = σ z + q • b)
    (hk : ∀ z b, σ z = q • b → ∃ z', z = q • z') :
    (∀ φ : M →+ ZMod q, ∃ y, ∀ z, ((EF (σ y) (σ z) : ℤ) : ZMod q) = φ z) ∧
      ∀ y, (∀ z, ((EF (σ y) (σ z) : ℤ) : ZMod q) = 0) → ∃ y', y = q • y' := by
  let B := Module.Free.chooseBasis ℤ L
  constructor
  · intro φ
    choose zz cc hzc using hs
    let s : L →ₗ[ℤ] M := B.constr ℤ fun i => zz (B i)
    let t : L →ₗ[ℤ] L := B.constr ℤ fun i => cc (B i)
    have hst : ∀ a, a = σ (s a) + q • t a := by
      have : (LinearMap.id : L →ₗ[ℤ] L) = σ ∘ₗ s + q • t := B.ext fun i => by
        simpa [s, t] using hzc (B i)
      intro a
      simpa using LinearMap.congr_fun this a
    let ψ : L →ₗ[ℤ] ℤ := B.constr ℤ fun i => ((φ (zz (B i))).cast : ℤ)
    have hψ : ∀ a, ((ψ a : ℤ) : ZMod q) = φ (s a) := by
      have : (Int.castAddHom (ZMod q)).toIntLinearMap ∘ₗ ψ = φ.toIntLinearMap ∘ₗ s := B.ext fun i => by
        simp [ψ, s]
      intro a
      simpa using LinearMap.congr_fun this a
    obtain ⟨a₀, ha₀⟩ := hE.2 ψ
    refine ⟨zz a₀, fun z => ?_⟩
    obtain ⟨z', hz'⟩ := hk (z - s (σ z)) (t (σ z)) (by
      rw [map_sub, sub_eq_iff_eq_add']
      exact hst (σ z))
    have h1 : φ z = φ (s (σ z)) := by
      rw [sub_eq_iff_eq_add.1 hz', map_add (f := _), map_nsmul]
      simp [← sub_eq_iff_eq_add.1 hz']
    have h2 : σ (zz a₀) = a₀ - q • cc a₀ := eq_sub_iff_add_eq.2 (hzc a₀).symm
    rw [h1, ← hψ, ← ha₀, h2]
    simp
  · intro y hy
    have hd : ∀ a, (q : ℤ) ∣ EF (σ y) a := by
      intro a
      obtain ⟨z, b, rfl⟩ := hs a
      rw [map_add (f := _), map_nsmul, nsmul_eq_mul]
      exact dvd_add ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (hy z)) (dvd_mul_right _ _)
    choose d hd using hd
    let ψ : L →ₗ[ℤ] ℤ := B.constr ℤ fun i => d (B i)
    obtain ⟨a₀, ha₀⟩ := hE.2 ψ
    refine hk y a₀ (hE.1 (B.ext fun i => ?_))
    rw [map_nsmul, ha₀, hd]
    simp [ψ]

theorem exists_levPairing {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (p : ℕ) [Fact p.Prime] (n : ℕ)
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) {N : ℕ} (u : Fin N → La)
    (hu : IsPolLattice c p EF u) :
    ∃ (π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n)
      (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n)),
      (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) ∧
      (∀ z z', e z z' = ((EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) ∧
      (∀ a : La, ∃ (z : Fin N → 𝓞 E) (b : La), a = ∑ k, z k • u k + (p ^ n) • b) ∧
      Function.Surjective π ∧
      (∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = (p ^ n) • y') ∧
      (∀ y, e y y = 0) ∧
      (∀ (a : 𝓞 E) (y z : Fin N → 𝓞 E), e (a • y) z = e y (RingOfIntegers.mapRingEquiv c a • z)) ∧
      (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ n), ∃ y, e y = φ) ∧
      (∀ y, e y = 0 → ∃ y', y = (p ^ n) • y') := by
  have := hu.free
  have := hu.finite
  let σ₀ : (Fin N → 𝓞 E) →ₗ[𝓞 E] La := Fintype.linearCombination (𝓞 E) u
  let σ : (Fin N → 𝓞 E) →ₗ[ℤ] La := σ₀.toAddMonoidHom.toIntLinearMap
  have hσ : ∀ z, σ z = ∑ k, z k • u k := fun z => Fintype.linearCombination_apply _ _ _
  have hσa : ∀ (a : 𝓞 E) z, σ (a • z) = a • σ z := fun a z => map_smul σ₀ a z
  have hs : ∀ a, ∃ z b, a = σ z + (p ^ n) • b :=
    surj_mod_pow σ.toAddMonoidHom p (fun a => by
      obtain ⟨z, b, h⟩ := hu.span a
      exact ⟨z, b, h.trans (by rw [← hσ]; rfl)⟩) n
  have hrk : Module.finrank ℤ La = Module.finrank ℤ (Fin N → 𝓞 E) := by
    rw [hu.rank, Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  let φ := LinearEquiv.ofFinrankEq La (Fin N → 𝓞 E) hrk
  have hk : ∀ z b, σ z = (p ^ n) • b → ∃ z', z = (p ^ n) • z' := fun z b h =>
    inj_mod_of_surj_mod (φ.toLinearMap ∘ₗ σ) (p ^ n) (fun a => by
      obtain ⟨z, b, h⟩ := hs (φ.symm a)
      refine ⟨z, φ b, ?_⟩
      have := congrArg φ h
      rwa [φ.apply_symm_apply, map_add, map_nsmul] at this) z (φ b) (by
      show φ (σ z) = _
      rw [h, map_nsmul])
  obtain ⟨hsu, hin⟩ := perfect_mod σ (p ^ n) EF hu.unimod hs hk
  let K : Submodule ℤ La := LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))
  let π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n :=
    AddMonoidHom.toMultiplicative (K.mkQ ∘ₗ σ).toAddMonoidHom
  have hπ : ∀ z, π (Multiplicative.ofAdd z) = lev p n (σ z) := fun z => rfl
  let e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n) :=
    { toFun := fun y => (Int.castAddHom (ZMod (p ^ n))).comp (EF (σ y) ∘ₗ σ).toAddMonoidHom
      map_zero' := by ext z; simp
      map_add' := fun y y' => by ext z; simp }
  have he : ∀ y z, e y z = ((EF (σ y) (σ z) : ℤ) : ZMod (p ^ n)) := fun y z => rfl
  have hone : ∀ a : La, lev p n a = 1 ↔ ∃ b, a = (p ^ n) • b := fun a => by
    show (Submodule.Quotient.mk a : La ⧸ K) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  refine ⟨π, e, fun z => by rw [hπ, hσ], fun z z' => by rw [he, hσ, hσ], fun a => ?_, fun t => ?_, fun y => ?_,
    fun y => ?_, fun a y z => ?_, fun ψ => ?_, fun y hy => ?_⟩
  · simpa only [hσ] using hs a
  · obtain ⟨a, ha⟩ := K.mkQ_surjective (Multiplicative.toAdd t)
    obtain ⟨z, b, rfl⟩ := hs a
    refine ⟨Multiplicative.ofAdd z, ?_⟩
    have h0 : K.mkQ ((p ^ n) • b) = 0 := (hone _).2 ⟨b, rfl⟩
    rw [map_add (f := _), h0, add_zero] at ha
    exact ha
  · rw [hπ, hone]
    exact ⟨fun ⟨b, hb⟩ => hk y b hb, fun ⟨y', hy'⟩ => ⟨σ y', by rw [hy', map_nsmul]⟩⟩
  · rw [he, hu.alt, Int.cast_zero]
  · rw [he, he, hσa, hσa, hu.adj]
  · obtain ⟨y, hy⟩ := hsu ψ
    exact ⟨y, AddMonoidHom.ext hy⟩
  · exact hin y fun z => (he y z).symm.trans (by rw [hy]; rfl)

end PositivityTheory.HtPt.Htat
end
end
