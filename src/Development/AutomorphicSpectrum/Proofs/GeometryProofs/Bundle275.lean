module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle528
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle108
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle015
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle147
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle166
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle272
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle095
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle268
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle132
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle189
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PpicDvr
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle258
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle134
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle270
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle274
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle271
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle140
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle139
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle120
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem chart_comp_eq {h : GenFrEx Xo c} {Z : Comp Xo c} (C : GlobalTheory.Reg.FChart h) (ψ : C.R →ₐ[c.F] Om Z)
    (z : FrPt Xo c (Om Z)) (t : Ix Dw → (Om Z)ˣ) (hz : FrMap ψ C.y z) (ht : FrBor t z (genFr h Z)) :
    C.Z = Z := by
  by_contra hne
  let s₀ : Sp (Om Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om Z))
  refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c C.Z Z hne) ?_ (GlobalTheory.AllWt.liesOn_genFr h Z s₀)
  rw [GlobalTheory.UnifComp.ptF_frBor ht, GlobalTheory.UnifComp.ptF_frMap hz, Scheme.Hom.comp_apply]
  let η : Sp C.R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.R)
  let sC : Sp (Om C.Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om C.Z))
  have he : spMap C.R.val.toRingHom sC = η :=
    PrimeSpectrum.ext (Ideal.comap_bot_of_injective C.R.val.toRingHom Subtype.val_injective)
  have hη : GlobalTheory.AllWt.ptF C.y η ∈ (C.Z : Set (Xo.XF c)) := by
    have hgen := GlobalTheory.AllWt.liesOn_genFr h C.Z sC
    rw [← GlobalTheory.UnifComp.ptF_frBor C.bor, GlobalTheory.UnifComp.ptF_frMap C.gen,
      Scheme.Hom.comp_apply, he] at hgen
    exact hgen
  have hspec : η ⤳ spMap ψ.toRingHom s₀ :=
    (PrimeSpectrum.le_iff_specializes (R := C.R) _ _).1 bot_le
  exact (hspec.map (GlobalTheory.AllWt.ptF C.y).continuous).mem_closed
    (isClosed_of_mem_irreducibleComponents _ C.Z.2) hη

attribute [local instance 1100] Subalgebra.algebra in
theorem comp_eq_of_algClosedAt (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (h : GenFrEx Xo c)
    (Z : Comp Xo c) (hac : ∀ a : Om Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om Z)).range)
    (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom)
    (hk : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
      FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y')
    (hk' : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
      FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k' x') y') : k = k' := by
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  obtain ⟨C, ψ, z, t, hz, ht⟩ := hA h (Om Z) (genFr h Z)
  have hCZ : C.Z = Z := chart_comp_eq C ψ z t hz ht
  have : Algebra.Smooth c.F C.R := C.sm
  have hread : ∀ (k : U.Comp) (x : (U.X k).dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ))
      (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y') →
      ∃ f : C.R → ℂ, GlobalTheory.GeomConn.ReadOn (Formalism.L2.PjFree.Unf.ofPj U) C.y f k := by
    rintro k x ⟨φ, y', t', hy', ht'⟩
    obtain ⟨w, hw⟩ := hL.bc _ _ φ z
    exact ⟨_, φ.comp ψ, w, x, _, fun _ => rfl, PullbackSections.frMap_trans _ _ hz hw,
      hmul _ _ _ _ _ ht' (hinv _ _ _ (GlobalTheory.SupGeneric.frBor_of_frMap φ ht hw hy'))⟩
  obtain ⟨f, hf⟩ := hread k x hk
  obtain ⟨f', hf'⟩ := hread k' x' hk'
  refine GlobalTheory.GeomConn.ReadOn.eq_of_isPreconnected (U := Formalism.L2.PjFree.Unf.ofPj U) hσ hU ?_ hf hf'
  have hac' : ∀ a : Om C.Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om C.Z)).range := by
    rw [hCZ]; exact hac
  exact GlobalTheory.GeomConn.isPreconnected_points_over C.R.val Subtype.val_injective hac' σ

end GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp

theorem GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp.comp_iff_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Comp Xo c) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), 1 ≤ r → IsUnf U → (∀ b : Om Z, IsAlgebraic c.F b → b ∈ (algebraMap c.F (Om Z)).range) → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → (Set.range y ⊆ (Z : Set (Xo.XF c)) ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) := by
  intro E _ _ _ H D l Xo c Z r U h1 hU hac
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨-, -, hcov, -, -, g, e, F, ik, φ, hEF, hP⟩ := id hU
  have hty : IsTypeFn H D.p D.q (fun j => relab c c.F.val.toRingHom (e j).1) :=
    (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 D g e
  have hinj := (GlobalTheory.CompBij.ik_bijective E H D l Xo c _ r U h1 hσ hU g e F ik φ hEF
    fun k x => (hP k x).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩).1
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c
  choose q hq using GlobalTheory.UnifComp.exists_liesOn (Formalism.L2.PjFree.Unf.ofPj U) hU
  obtain ⟨k, hk⟩ := GlobalTheory.CompModel.exists_model (Formalism.L2.PjFree.Unf.ofPj U) hU hG Z
  have hqk : q k = Z := GlobalTheory.UnifComp.eq_of_carries hk (hq k)
  have huniq : ∀ k', q k' = Z → k' = k := by
    intro k' hk'
    obtain ⟨Z', hZ'⟩ := GlobalTheory.CompModel.exists_comp (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hG k'
    obtain rfl : Z' = Z := (GlobalTheory.UnifComp.eq_of_carries hZ' (hq k')).symm.trans hk'
    obtain ⟨P, w, x, t, hw, ht⟩ := hk
    obtain ⟨P', w', x', t', hw', ht'⟩ := hZ'
    exact GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp.comp_eq_of_algClosedAt U hσ hU hG Z' hac k' k x' x
      ⟨P', w', t', hw', ht'⟩ ⟨P, w, t, hw, ht⟩
  have hfr : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      ∃ (k' : U.Comp) (x : (U.X k').dom) (t : Ix D → (CAt c.F.val.toRingHom)ˣ)
        (z : FrPt Xo c (CAt c.F.val.toRingHom)),
        FrBor t (U.un k' x) z ∧ z.x = under y ∧ GlobalTheory.AllWt.ptF z = y := by
    intro y hy
    have hover : under y ≫ Xo.s = sOf c ℂ := by
      show (y ≫ pullback.fst _ _) ≫ Xo.s = _
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy, sOf, ← Spec.map_comp]
      rfl
    obtain ⟨z, hz⟩ := Formalism.L2.Pj.exists_frPt_local (Xo := Xo) (c := c) (L := ℂ)
      GlobalTheory.firstFiveLaws.2.1.secTwist (under y) hover
    obtain ⟨k', x, t, hb⟩ := hcov z
    refine ⟨k', x, t, z, hb, hz, ?_⟩
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hz
    · exact (pullback.lift_snd _ _ _).trans hy.symm
  refine ⟨g, _, F, ik k, hty, fun y hy => ⟨fun hZ => ?_, fun ⟨P, hP', hPy⟩ => ?_⟩⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    have hk' : q k' = Z := by
      by_contra hne
      let s₀ : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) ?_ (hZ ⟨s₀, rfl⟩)
      have := hq k' x s₀
      change GlobalTheory.AllWt.ptF (U.un k' x) s₀ ∈ _ at this
      rwa [← GlobalTheory.UnifComp.ptF_frBor hb, hzy] at this
    obtain rfl := huniq k' hk'
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    exact ⟨Pm, hPm, hzx.symm.trans (hb.1.trans hx)⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    have e1 : ik k' = ik k := F.disj _ _ Pm P hPm hP' (hx.symm.trans (hb.1.symm.trans (hzx.trans hPy)))
    obtain rfl := hinj e1
    rintro _ ⟨s, rfl⟩
    rw [← hqk, ← hzy, GlobalTheory.UnifComp.ptF_frBor hb]
    exact hq k' x s
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree

attribute [-instance] GlobalTheory.CompHt.fintypePsi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem}
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem mem_Vgen (𝔐 : HodgeCpt Y S₀ Dc.y) (t : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ) {x : 𝔐.Li}
    (hx : x ∈ 𝔐.V t p) : x ∈ 𝔐.Vgen t := by
  obtain ⟨U, hU, b, hs, hf⟩ := 𝔐.vb t p trivial
  have e : 𝔐.V t p = Submodule.span (regAt 𝔐.ξ p) (Set.range b) := (hf p trivial hU).2
  have hx' : x ∈ Submodule.span (regAt 𝔐.ξ p) (Set.range b) := e ▸ hx
  clear hx
  show x ∈ 𝔐.Vgen t
  have hs' : Submodule.span Ω (Set.range b) = 𝔐.Vgen t := hs
  rw [← hs']
  induction hx' using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span h
  | zero => exact zero_mem _
  | add _ _ _ _ h h' => exact add_mem h h'
  | smul a x _ h => exact Submodule.smul_mem _ (a : Ω) h

theorem disjoint_blocks (Or : CptOrigin Y S₀ Dc Hd) (τ : CMType H) :
    Disjoint (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) := by
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S₀ Ω K J Dc.y Or.𝔐
    (FaithfulSMul.algebraMap_injective _ _)
  exact hind.pairwiseDisjoint (Or.bg_ne_sm τ τ)

theorem exists_smallPart (Or : CptOrigin Y S₀ Dc Hd) {w : (Σ k, J k) → ℂ} (d : MuFrameAt Hd w) :
    ∃ s, Or.IsSmallPart d s := by
  have h : ∀ τ k, ∃ x, x ∈ Or.𝔐.Vgen (Or.sm τ) ∧
      Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) - x ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    have hm : Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := by
      rw [← Or.i_range τ]
      exact ⟨_, rfl⟩
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 hm
    exact ⟨e, he, by rw [← hae]; simpa using ha⟩
  choose s hs using h
  exact ⟨s, hs⟩

theorem frames (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (d : MuFrameAt Hd w) {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li}
    (hs : Or.IsSmallPart d s) (τ : CMType H) (h : genPt Or.𝔐.ξ ⤳ centre z) :
    (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt (d.b τ) ⟨centre z, h⟩ ∧
    (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩ ∧
    ∀ k, Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.V (Or.bg τ) ⟨centre z, h⟩ := by
  have hfr := GlobalTheory.T.component_data_hodge_second E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ d.c d.f (d.b τ) h hw (d.adapted τ).1 d.inDom
  have hb := GlobalTheory.T.is_frame_at_tail_of_is_frame_at_comap_sup_lattice Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (W τ) (Or.i τ) (Or.𝔐.V (Or.bg τ)) (Or.𝔐.V (Or.sm τ))
    (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) Dc.N Dc.j Dc.j_le_N (d.b τ) (s τ) ⟨centre z, h⟩ (Or.i_inj τ)
    (Or.i_range τ) (disjoint_blocks Or τ) (fun _ hx => mem_Vgen _ _ _ hx) (fun _ hx => mem_Vgen _ _ _ hx) hfr
    (by rw [(d.adapted τ).2.2, Or.F_eq τ]) (hs τ)
  exact ⟨hfr, hb.1, hb.2.1⟩

theorem norm_eq (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (hi : Or.𝔐.Interior z) (d : MuFrameAt Hd w)
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s) :
    ∃ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ,
      (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) ∧ (∀ τ, (Γ τ).PosDef) ∧
      d.norm = ‖valAt Dc.y d.u w‖ * (∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ τ).det.re := by
  have h : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  have key : ∀ τ, ∃ Γ : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ,
      Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) Γ ∧ Γ.PosDef ∧
        quotNormSq Dc.j_le_N (gramAt (Dc.h τ) (d.b τ) w) = Γ.det.re := fun τ => by
    obtain ⟨h1, h2, h3⟩ := frames Or hw d hs τ h
    obtain ⟨G, hG, hGp⟩ := GlobalTheory.T.component_data_hodge_third E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z τ (d.b τ) h hi h1
    rw [GlobalTheory.T.intersection_system_hodge_data E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ (d.b τ) h G hw hi h1 hG]
    exact GlobalTheory.T.intersection_system_hodge_bound E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z τ (d.b τ) (s τ) h G hi h1
      ((d.adapted τ).2.2) (fun k => (hs τ k).1) h3 h2 hG hGp
  choose Γ h1 h2 h3 using key
  refine ⟨Γ, h1, h2, ?_⟩
  unfold MuFrameAt.norm
  simp_rw [h3]

theorem det_re_pos {n : ℕ} {Γ : Matrix (Fin n) (Fin n) ℂ} (h : Γ.PosDef) : 0 < Γ.det.re :=
  (Complex.pos_iff.1 h.det_pos).1

theorem phMu_eq (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (hi : Or.𝔐.Interior z) (d : MuFrameAt Hd w)
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s)
    {Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ}
    (hΓ : ∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) :
    phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) +
      (∑ τ, Real.log (Γ τ).det.re) / 2 := by
  have h : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  haveI : CharZero Ω := algebraRat.charZero Ω
  have htie : CoordTie ℤ Or.𝔐.ξ (fun c' : (k : K) → J k => ∏ k, Dc.y ⟨k, c' k⟩) := Or.𝔐.tie
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hi
  obtain ⟨cv, hcv, hwc⟩ := exists_eq_smul_orbitRep w
  obtain ⟨w₀, hw₀def⟩ : ∃ w₀, w₀ = orbitRep w := ⟨_, rfl⟩
  rw [← hw₀def] at hwc
  have hwk : ∀ p, w p = cv p.1 * w₀ p := fun p => congrFun hwc p
  have hw₀ : CoordsAt Or.𝔐.ξ Dc.y z w₀ := by
    have := RootHt.ArchB.coordsAt_smul (fun k => (cv k)⁻¹) (fun k => inv_ne_zero (hcv k)) hw
    convert this using 1
    funext p
    rw [hwc]
    simp [torusSmul, inv_mul_cancel_left₀ (hcv p.1)]
  have hval : ∀ (a : Ω) (v : ℂ), IsValueAt Dc.y a w v ↔ IsValueAt Dc.y a w₀ v := fun a v =>
    ((GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w h hw a v).symm).trans
      (GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w₀ h hw₀ a v)
  have hne₀ : ∀ k, w₀ ⟨k, d.c k⟩ ≠ 0 := fun k h0 => d.inDom.1 k (by rw [hwk ⟨k, d.c k⟩]; simp [h0])
  let d₁ : MuFrameAt Hd w₀ :=
    { c := d.c, f := d.f
      inDom := ⟨hne₀, d.inDom.2.imp fun v hv => ⟨(hval _ _).1 hv.1, hv.2⟩⟩
      b := d.b, adapted := d.adapted, u := d.u, unit := d.unit, eq := d.eq }
  have hs₁ : Or.IsSmallPart d₁ s := hs
  have hu := GlobalTheory.T.unit_value_frame_domain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d.c d.f d.u htie h hw d.inDom d.unit
  have hmc₀ : w₀ ∈ mcPts (mCoordIdeal Dc.y) :=
    (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie w₀).2 ⟨z, h, hw₀⟩
  have hu₀ : valAt Dc.y d.u w₀ = valAt Dc.y d.u w :=
    valAt_eq hmc₀ ((hval _ _).1 ((GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w h hw _ _).1 hu.2))

  have hne := GlobalTheory.T.component_data_hodge_first E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w₀ hw₀
  obtain ⟨s₀, hs₀⟩ := exists_smallPart Or hne.some
  obtain ⟨Γ₀, g₀, p₀, n₀⟩ := norm_eq Or hw₀ hi hne.some hs₀
  obtain ⟨Γ₁, g₁, p₁, -⟩ := norm_eq Or hw₀ hi d₁ hs₁
  have e₁ : Γ₁ = Γ := funext fun τ =>
    GlobalTheory.T.gram_matrix_change_frame E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z _ (s τ) _ _ hpol (g₁ τ) (hΓ τ)
  subst e₁
  have hind := GlobalTheory.T.intersection_system_hodge_degree E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w₀ hne.some d₁ s₀ s Γ₀ Γ₁ hw₀ hi hs₀ hs₁ g₀ g₁ p₀
  have hF : muMetric Hd w₀ = ‖valAt Dc.y d.u w‖ * (∏ k, ‖w₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k) *
      ∏ τ, Real.sqrt (Γ₁ τ).det.re := by
    unfold muMetric
    rw [dite_eq_left hne, n₀, hind]
    show ‖valAt Dc.y d.u w₀‖ * _ * _ = _
    rw [hu₀]
  have hA : 0 < ‖valAt Dc.y d.u w‖ := norm_pos_iff.2 hu.1
  have hsq : 0 < ∏ τ, Real.sqrt (Γ₁ τ).det.re :=
    Finset.prod_pos fun τ _ => Real.sqrt_pos.2 (det_re_pos (p₁ τ))
  have hprod₀ : 0 < ∏ k, ‖w₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hne₀ k)) _
  have hprod : 0 < ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (d.inDom.1 k)) _
  have hpos : 0 < muMetric Hd w₀ := by
    rw [hF]
    positivity
  have hnz : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => ⟨d.c k, d.inDom.1 k⟩
  have hh : (muLine Hd).h w = (∏ k, ‖cv k‖ ^ Hd.aMu k) * muMetric Hd w₀ := by
    subst hw₀def
    exact TopNPoly.hermOfFun_h_smul hcv hwc hnz hpos
  have hcw : (∏ k, ‖cv k‖ ^ Hd.aMu k) * ∏ k, ‖w₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k = ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow, ← norm_mul]
    rw [hwk ⟨k, d.c k⟩]
  have hfin : (muLine Hd).h w = (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) *
      ∏ τ, Real.sqrt (Γ₁ τ).det.re := by
    rw [hh, hF, ← hcw]
    ring
  show Real.log ((muLine Hd).h w) = _
  rw [hfin, Real.log_mul (by positivity) hsq.ne', Real.log_prod (fun τ _ => (Real.sqrt_pos.2 (det_re_pos (p₁ τ))).ne')]
  congr 1
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun τ _ => Real.log_sqrt (det_re_pos (p₁ τ)).le

theorem phMu_small : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) ∧ ∀ d : MuFrameAt Hd w, (∃ s, Or.IsSmallPart d s) ∧ ∀ s, Or.IsSmallPart d s → (∀ τ (h : genPt Or.𝔐.ξ ⤳ centre z), (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩) ∧ valAt Dc.y d.u w ≠ 0 ∧ (Or.𝔐.Interior z → ∀ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) + (∑ τ, Real.log (Γ τ).det.re) / 2) := by
  intro _ E _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w hw
  have htie : CoordTie ℤ Or.𝔐.ξ (segreCoord Dc.y) := Or.𝔐.tie
  refine ⟨GlobalTheory.T.component_data_hodge_first E H D l (Xo l) c Y II K J Ω W Dc Hd S₀ Or z w hw, fun d => ⟨exists_smallPart Or d, fun s hs => ⟨
    fun τ h => (frames Or hw d hs τ h).2.1, ?_, fun hi Γ hΓ => phMu_eq Or hw hi d hs hΓ⟩⟩⟩
  exact (GlobalTheory.T.unit_value_frame_domain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d.c d.f d.u htie (Or.𝔐.all _) hw d.inDom d.unit).1

end GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.CompanionTheory.Relay.polarized_abelian_part_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), GlobalTheory.LN.CDvr V → Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → GlobalTheory.LN.PolAt tV (Out.jK V) → ∀ P : AbPart tV (spMap r), IsPrincipal P.tB := by
  first | exact @PositivityTheory.HtPt.Ppic.dvr | exact PositivityTheory.HtPt.Ppic.dvr
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyGen

theorem section_and_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), 1 ≤ D.g → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (D' : PPData H L') (_ : D.Ext D') (s : Out.H0 D'.t.PP.L 1) (e : Fin D'.g → D'.B.carrier), KeyDeg.NonVan D'.t.G.hom s ∧ LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  intro E _ _ _ H L _ _ D _
  have : Smooth D.t.G.hom := D.t.semi.smooth
  have : GeometricallyConnected D.t.G.hom := D.t.semi.geomConnected
  have : QuasiCompact D.t.G.hom := D.t.semi.quasiCompact
  have hN : (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))).IsLB :=
    LB.isLB_linComb D.t.PP.isLB _ _
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_nonzero_section_pp_data E H L D
  obtain ⟨d₀, hd₀, hb⟩ := GlobalTheory.T.section_module_bounded_denominator (𝓞 L) D.t.G _ hN t ht
  let I : Ideal (𝓞 L) :=
    { carrier := {x | ∃ u : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), d₀ • u = x • t}
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨u, hu⟩
        exact ⟨c • u, by rw [smul_comm, hu, smul_eq_mul, mul_smul]⟩ }
  have hI : I ≠ ⊥ := fun h0 => hd₀ (by
    have : d₀ ∈ I := ⟨t, rfl⟩
    rw [h0] at this
    simpa using this)
  obtain ⟨L', _, _, _, y, hy, hB⟩ := GlobalTheory.T.principal_extension_projective_module L D.B.carrier I hI
  obtain ⟨⟨D', m⟩⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').1
  obtain ⟨hgg, -, io, -, hspan, -⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').2 D' m
  obtain ⟨e, he1, he2⟩ := hB D'.B.carrier io hspan hgg
  obtain ⟨P, hP1, hP2⟩ := GlobalTheory.T.section_module_field_ext_map E H L D L' D' m
  have : Smooth D'.t.G.hom := D'.t.semi.smooth
  let φ := algebraMap (𝓞 L) (𝓞 L')
  let W : Ideal (𝓞 L') :=
    { carrier := {z | ∃ v : SecMod D'.t.G.hom (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), φ d₀ • v = z • P t}
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨u, hu⟩
        exact ⟨c • u, by rw [smul_comm, hu, smul_eq_mul, mul_smul]⟩ }
  have hIW : I.map φ ≤ W := Ideal.map_le_iff_le_comap.2 fun x ⟨u, hu⟩ =>
    ⟨P u, by rw [← hP1, hu, hP1]⟩
  obtain ⟨s, hs⟩ : y ∈ W := hIW (hy ▸ Ideal.mem_span_singleton_self y)
  refine ⟨L', inferInstance, inferInstance, inferInstance, D', m, s, e, ?_, he1, he2⟩
  intro b'
  let b : Sp (𝓞 L) := spMap φ b'

  obtain ⟨x, u, hu, yy, hyy, hmem⟩ : ∃ (x : 𝓞 L) (u : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))),
      d₀ • u = x • t ∧ ∃ yy : D.t.G.left, D.t.G.hom yy = b ∧ yy ∈ Out.nonzeroLocus (M := LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) u := by
    by_cases hb0 : b.asIdeal = ⊥
    · exact ⟨d₀, t, rfl, GlobalTheory.T.nonzero_section_generic_fibre (𝓞 L) D.t.G _ hN t ht b hb0⟩
    · have hmax : b.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hb0 b.isPrime
      obtain ⟨x, u, hu, hV⟩ := GlobalTheory.T.exists_section_not_in_set (𝓞 L) _ (fun a m ha h => eq_zero_of_smul_eq_zero ha h) t ht d₀ hd₀ hb
        {u | ∀ yy : D.t.G.left, D.t.G.hom yy = b → yy ∉ Out.nonzeroLocus (M := LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) u}
        b.asIdeal hmax hb0 (fun u hu c e he h => GlobalTheory.T.section_module_divisible_at_prime (𝓞 L) _ D.t.G.hom _ b hmax u hu c e he h)
      simp only [Set.mem_setOf_eq, not_forall, not_not] at hV
      obtain ⟨yy, hyy, hmem⟩ := hV
      exact ⟨x, u, hu, yy, hyy, hmem⟩
  obtain ⟨y', hy', hm'⟩ := hP2 u b' yy hyy hmem
  refine ⟨y', hy', ?_⟩
  have hxI : φ x ∈ I.map φ := Ideal.mem_map_of_mem φ (show x ∈ I from ⟨u, hu⟩)
  rw [hy, Ideal.mem_span_singleton'] at hxI
  obtain ⟨w, hw⟩ := hxI
  have hφ : φ d₀ ≠ 0 := fun h0 => hd₀ (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 L') (h0.trans (map_zero _).symm))
  have hPu : P u = w • s := by
    have : φ d₀ • (P u - w • s) = 0 := by
      rw [smul_sub, ← hP1, hu, hP1, smul_comm, hs, smul_smul, ← hw, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_smul_eq_zero hφ this)
  rw [hPu] at hm'
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm'
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  have : y' ∈ D'.t.G.left.basicOpen (constFn D'.t.G.hom _ w * LB.Sec.f (show SecMod D'.t.G.hom _ from s) k) := hk
  rw [Scheme.basicOpen_mul] at this
  exact this.2

end GlobalTheory.CompanionTheory.Ar.Sl.KeyGen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_reference_geometry_same_generic : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∃ G : RefGeo Y, genPt G.𝔐.ξ₀ = genPt ξ₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_refGeo | exact GlobalTheory.CompanionTheory.Ar.exists_refGeo | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_refGeo <;> assumption)
end
