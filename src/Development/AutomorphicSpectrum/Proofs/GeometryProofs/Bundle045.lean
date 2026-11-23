module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.PullReg

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {Ω' : Type} [Field Ω']

theorem germ_stalkClosedPointTo_baseChange (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* Ω')
    (ζ : Spec (CommRingCat.of Ω') ⟶ X) (hζ : ζ = Spec.map (CommRingCat.ofHom i) ≫ ξ) (U : X.Opens)
    (hU : ζ (IsLocalRing.closedPoint (CommRingCat.of Ω')) ∈ U) (hU' : genPt ξ ∈ U) :
    X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo ζ =
      X.presheaf.germ U (genPt ξ) hU' ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
  have e : ζ = Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
      X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) := by
    rw [hζ, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hl : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom := by
    refine ⟨fun a ha => ?_⟩
    have h1 : IsUnit (i ((Scheme.stalkClosedPointTo ξ).hom a)) := ha
    have h2 : IsUnit ((Scheme.stalkClosedPointTo ξ).hom a : Ω) :=
      isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at h1
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom a h2
  subst e
  exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk _ U hU

theorem stalkMap_comp_genMap {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} (hD : Dominates ξ' ξ f i)
    (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1) (s : X.presheaf.stalk (f p'.1)) :
    genMap ξ' p' ((f.stalkMap p'.1).hom s) = i (genMap ξ ⟨f p'.1, h⟩ s) := by
  have key : f.stalkMap p'.1 ≫ X'.presheaf.stalkSpecializes p'.2 ≫ Scheme.stalkClosedPointTo ξ' =
      X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
    have hg : genPt ξ ∈ U := h.mem_open U.2 hU
    have hg' : (ξ' ≫ f) (IsLocalRing.closedPoint (CommRingCat.of Ω')) ∈ U := by
      have : (ξ' ≫ f) (IsLocalRing.closedPoint (CommRingCat.of Ω')) = genPt ξ :=
        (Scheme.Hom.comp_apply ξ' f _).trans hD.map_genPt
      rw [this]; exact hg
    have e := germ_stalkClosedPointTo_baseChange ξ i (ξ' ≫ f) hD U hg' hg
    rw [Scheme.stalkClosedPointTo_comp] at e
    have e3 : f.stalkMap p'.1 ≫ X'.presheaf.stalkSpecializes p'.2 ≫ Scheme.stalkClosedPointTo ξ' =
        X.presheaf.stalkSpecializes (p'.2.map f.continuous) ≫ f.stalkMap (genPt ξ') ≫
          Scheme.stalkClosedPointTo ξ' :=
      (Scheme.Hom.stalkSpecializes_stalkMap_assoc f _ _ p'.2 _).symm
    rw [e3, TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
    exact e
  exact congrArg (fun φ => φ.hom s) key

end GlobalTheory.CompanionTheory.Ar.Flat.PullReg

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem pull_reg_and_gen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0})
    (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'),
    Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1,
      (∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧
        ∀ (L : Lat ξ Ω) (t : Ω), L.IsGenAt ⟨f p'.1, h⟩ t →
          (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t) := by
  intro X Ω _ ξ X' Ω' _ ξ' f i hD p'
  have h := hD.specializes p'
  have hreg : ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, PullReg.stalkMap_comp_genMap hD p' h s⟩
  refine ⟨h, hreg, fun L t ht => ⟨(map_ne_zero i).2 ht.1, ?_⟩⟩
  rw [Lat.pull_apply L hD]
  have hL : L ⟨f p'.1, hD.specializes p'⟩ = Submodule.span (regAt ξ ⟨f p'.1, h⟩) {t} := ht.2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨f p'.1, h⟩) {t} := by
      rw [← hL]; exact he
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 he'
    refine Submodule.mem_span_singleton.2 ⟨⟨i r, hreg _ r.2⟩, ?_⟩
    show i (r : Ω) * i t = i ((r : Ω) * t)
    rw [map_mul]
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.subset_span ⟨t, ?_, rfl⟩
    show t ∈ (L ⟨f p'.1, hD.specializes p'⟩ : Set Ω)
    rw [hL]
    exact Submodule.mem_span_singleton_self t

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem lat_stable : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End Ω V), M.IsActOf act.act ρ → ∀ (p : Cpt ξ) (a : O), ∀ e ∈ M.lat p, ρ a e ∈ M.lat p := by
  intro X Ω _ ξ G _ V _ _ M O _ act ρ hact p a e he
  change e ∈ Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v} at he
  change ρ a e ∈ Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v}
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv⟩ := hx
    unfold LieModel.Extends at hv
    obtain ⟨hv1, hv2⟩ := hv
    refine Submodule.subset_span ⟨v ≫ act.act a, ?_⟩
    unfold LieModel.Extends
    refine ⟨?_, ?_⟩
    · unfold IsTanAt at hv1 ⊢
      have := act.hom a
      rw [Over.comp_left, ← Category.assoc, hv1, ← Over.comp_left]
      congr 1
      simp
    · have h := hact a x
      rw [h, Over.comp_left, hv2, Over.comp_left]
      exact Category.assoc _ _ _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Subring.smul_def, map_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ r hx

end GlobalTheory.CompanionTheory.Ar.LieStable
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Frames

open GlobalTheory.CompanionTheory.Ar

variable {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {i : Ω₀ →+* Ω} {Li Li₀ : Type} [AddCommGroup Li] [Module Ω Li]
  [AddCommGroup Li₀] [Module Ω₀ Li₀] {ι : Li₀ →+ Li}

theorem linearIndependent_comp_basis (h : IsExtOver i ι) {K : Type} (B : Module.Basis K Ω₀ Li₀) :
    LinearIndependent Ω fun k => ι (B k) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have e : s ≃ Fin s.card := s.equivFin
  have hb : LinearIndependent Ω₀ (fun k : Fin s.card => B (e.symm k : K)) :=
    B.linearIndependent.comp (fun k => (e.symm k : K)) (Subtype.val_injective.comp e.symm.injective)
  have h3 := (h.2 s.card _ hb).comp e e.injective
  convert h3 using 1
  funext k
  simp

theorem exists_dual_ext (h : IsExtOver i ι) (hs : Submodule.span Ω (Set.range ι) = ⊤)
    (φ : Module.Dual Ω₀ Li₀) : ∃ φ' : Module.Dual Ω Li, ∀ e, φ' (ι e) = i (φ e) := by
  classical
  let B := Module.Basis.ofVectorSpace Ω₀ Li₀
  have hli : LinearIndependent Ω fun k => ι (B k) := linearIndependent_comp_basis h B
  have hmem : ∀ e : Li₀, ι e ∈ Submodule.span Ω (Set.range fun k => ι (B k)) := by
    intro e
    have he : e ∈ Submodule.span Ω₀ (Set.range B) := by rw [B.span_eq]; exact Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [h.1]; exact Submodule.smul_mem _ _ hx
  have hsp : ⊤ ≤ Submodule.span Ω (Set.range fun k => ι (B k)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    exact hmem e
  let B' := Module.Basis.mk hli hsp
  refine ⟨B'.constr Ω (fun k => i (φ (B k))), fun e => ?_⟩
  have he : e ∈ Submodule.span Ω₀ (Set.range B) := by rw [B.span_eq]; exact Submodule.mem_top
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    have hk : ι (B k) = B' k := (Module.Basis.mk_apply hli hsp k).symm
    rw [hk, Module.Basis.constr_basis]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
  | smul a x _ hx =>
    rw [h.1]
    simp only [map_smul, hx, smul_eq_mul, map_mul]

theorem two_frames (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (i : Ω₀ →+* Ω) (Li Li₀ : Type) [AddCommGroup Li] [Module Ω Li]
    [AddCommGroup Li₀] [Module Ω₀ Li₀] (ι : Li₀ →+ Li) (hext : IsExtOver i ι)
    (hs : Submodule.span Ω (Set.range ι) = ⊤) (W : Subring Ω) (L₀ : Set Li₀) (L : Set Li) (r : ℕ)
    (b : Fin r → Li) (b₀ : Fin r → Li₀) (π₀ : Fin r → Module.Dual Ω₀ Li₀) (T : Module.End Ω Li) (Dn κ : Ω)
    (m : Ω₀) (hL : Submodule.span W L = Submodule.span W (ι '' L₀))
    (hT : ∀ e ∈ L, T e ∈ Submodule.span W (Set.range b)) (hTb : ∀ j, T (ι (b₀ j)) = Dn • ι (b₀ j))
    (hm : ∀ j, m • b₀ j ∈ L₀) (hπ : ∀ a j, π₀ a (b₀ j) = if a = j then 1 else 0)
    (hint : ∀ a, ∀ e ∈ L₀, i (m * π₀ a e) ∈ W) (hκ : ∀ j, κ • b j ∈ L)
    (hb : ∀ j, b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a))) :
    (∀ j, (Dn * i m) • ι (b₀ j) ∈ Submodule.span W (Set.range b)) ∧
      ∀ j, (i m * κ) • b j ∈ Submodule.span W (Set.range fun a => ι (b₀ a)) := by
  classical
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have hin : ι (m • b₀ j) ∈ Submodule.span W L := by
      rw [hL]; exact Submodule.subset_span ⟨_, hm j, rfl⟩
    have key : ∀ x ∈ Submodule.span W L, T x ∈ Submodule.span W (Set.range b) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hT y hy
      | zero => simp
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
      | smul w y _ hy =>
        rw [Subring.smul_def, map_smul]
        have hw := Submodule.smul_mem _ w hy
        rwa [Subring.smul_def] at hw
    have hj := key _ hin
    rwa [hext.1, map_smul, hTb, smul_smul, mul_comm] at hj
  · have hv : κ • b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a)) :=
      Submodule.smul_mem _ κ (hb j)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hv
    have hcW : ∀ a, i m * c a ∈ W := by
      intro a
      obtain ⟨ψ, hψ⟩ := exists_dual_ext hext hs (π₀ a)
      have hψv : ψ (κ • b j) = c a := by

        rw [← hc, map_sum, Finset.sum_eq_single a]
        · rw [map_smul, hψ, hπ, if_pos rfl, map_one, smul_eq_mul, mul_one]
        · intro x _ hx
          rw [map_smul, hψ, hπ, if_neg (Ne.symm hx), map_zero, smul_zero]
        · intro ha; exact absurd (Finset.mem_univ a) ha
      have hspan : κ • b j ∈ Submodule.span W (ι '' L₀) := by
        rw [← hL]; exact Submodule.subset_span (hκ j)
      have key : ∀ x ∈ Submodule.span W (ι '' L₀), i m * ψ x ∈ W := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨e, he, rfl⟩ := hy
          rw [hψ, ← map_mul]; exact hint a e he
        | zero => simp
        | add y z _ _ hy hz => rw [map_add (f := _), mul_add]; exact W.add_mem hy hz
        | smul w y _ hy =>
          rw [Subring.smul_def, map_smul, smul_eq_mul, mul_left_comm]
          exact W.mul_mem w.2 hy
      rw [← hψv]; exact key _ hspan
    rw [mul_smul, ← hc, Finset.smul_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [smul_smul]
    have ha := Submodule.smul_mem (Submodule.span W (Set.range fun a => ι (b₀ a))) (⟨_, hcW a⟩ : W)
      (Submodule.subset_span ⟨a, rfl⟩)
    rwa [Subring.smul_def] at ha

end GlobalTheory.CompanionTheory.Ar.Frames
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DualExt

theorem dual_ext : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V'), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → ∃ jd : Module.Dual Ω V →+ Module.Dual Ω' V', ∀ w e, jd w (j e) = i (w e) := by
  intro Ω Ω' _ _ i V V' _ _ _ _ j hext hspan
  let b := Module.Basis.ofVectorSpace Ω V
  have hj : ∀ e : V, j e = (b.repr e).sum fun k a => i a • j (b k) := by
    intro e
    conv_lhs => rw [← b.linearCombination_repr e]

    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
    exact Finset.sum_congr rfl fun k _ => hext.1 _ _
  have hli : LinearIndependent Ω' fun k => j (b k) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    have h := hext.2 s.card (fun m => b (s.equivFin.symm m))
      (b.linearIndependent.comp (fun m => (s.equivFin.symm m : _))
        (Subtype.val_injective.comp s.equivFin.symm.injective))
    have h2 := h.comp s.equivFin s.equivFin.injective
    convert h2 using 1
    funext k
    simp
  have hsp : ⊤ ≤ Submodule.span Ω' (Set.range fun k => j (b k)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    rw [hj e, Finsupp.sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  refine ⟨AddMonoidHom.mk' (fun w => b'.constr Ω' fun k => i (w (b k))) fun w₁ w₂ => ?_, fun w e => ?_⟩
  · rw [← map_add (f := _)]
    congr 1
    funext k
    simp
  · show b'.constr Ω' (fun k => i (w (b k))) (j e) = i (w e)

    rw [hj e, Finsupp.sum, map_sum]

    conv_rhs => rw [← b.linearCombination_repr e, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, show j (b k) = b' k from (Module.Basis.mk_apply hli hsp k).symm, Module.Basis.constr_basis,
      map_smul, smul_eq_mul, smul_eq_mul, map_mul]

end GlobalTheory.CompanionTheory.Ar.DualExt
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem NormAt.isoAt_of_integrallyClosed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (p : Cpt ξ),
    NormAt ξ' f (RingHom.id Ω) p → (∀ a : Ω, IsIntegral (regAt ξ p) a → a ∈ regAt ξ p) →
      IsoAt ξ' f (RingHom.id Ω) p := by
  intro X Ω _ ξ X' ξ' f p hN hp
  have e : (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring = regAt ξ p := by
    rw [Subring.map_id]
    ext a
    exact ⟨hp a, fun ha => isIntegral_algebraMap (x := (⟨a, ha⟩ : regAt ξ p))⟩
  have loc : IsLocalRing (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := by
    rw [e]
    exact NormAt.isLocalRing_regAt p
  have hr : ∀ q : Cpt ξ', f q.1 = p.1 →
      regAt ξ' q = (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := fun q hq => by
    obtain ⟨P, hP, h⟩ := hN.exists_max q hq
    exact h.trans (NormAt.ofPrime_of_isLocalRing _ P hP)
  refine ⟨?_, fun q hq => ?_, hN.dom⟩
  · obtain ⟨q, hq, hu⟩ := hN.existsUnique _ (IsLocalRing.maximalIdeal.isMaximal _)
    exact ⟨q, hq.1, fun q' hq' => hu q' ⟨hq', (hr q' hq').trans
      (NormAt.ofPrime_of_isLocalRing _ _ (IsLocalRing.maximalIdeal.isMaximal _)).symm⟩⟩
  · rw [hr q hq, e, Subring.map_id]

end GlobalTheory.CompanionTheory.Ar
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.Regular
open scoped Matrix ComplexOrder

def basePoint (n a : ℕ) : Fin n → ℂ := fun k => if k.val < a then -1 else 0

theorem basePoint_mem {n a : ℕ} (h : a ≤ n) : basePoint n a ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have : (Fin.castLE h i).val < a := i.isLt
    simp [basePoint, this]
  · have : ¬ k.val < a := by omega
    simp [basePoint, this]

theorem shift_mem {n a : ℕ} (h : a ≤ n) (i : Fin a) :
    basePoint n a + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · have hj : (Fin.castLE h j).val < a := j.isLt
    by_cases hji : Fin.castLE h j = Fin.castLE h i
    · simp [basePoint, hj, hji, Pi.single_apply]
    · simp [basePoint, hj, Pi.single_apply, hji]
  · have hk' : ¬ k.val < a := by omega
    have hne : k ≠ Fin.castLE h i := by
      intro e
      apply hk'
      rw [e]
      exact i.isLt
    simp [basePoint, hk', Pi.single_apply, hne]

theorem expCover_shift {n a : ℕ} (h : a ≤ n) (i : Fin a) (w : Fin n → ℂ) :
    expCover a (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = expCover a w := by
  funext k
  by_cases hk : k = Fin.castLE h i
  · subst hk
    have : (Fin.castLE h i).val < a := i.isLt
    simp [expCover, this, Complex.exp_add, Complex.exp_two_pi_mul_I]
  · simp [expCover, Pi.single_apply, hk]

theorem monodromy_preserves_form {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (i : Fin a) (x y : Λ) :
    L.E (L.T i x) (L.T i y) = L.E x y := by
  have hw := basePoint_mem L.a_le
  have h1 := L.im _ (shift_mem L.a_le i) x y
  rw [expCover_shift, L.mono i _ hw x, L.mono i _ hw y] at h1
  have h2 := L.im _ hw (L.T i x) (L.T i y)
  exact_mod_cast h2.symm.trans h1

theorem T_bijective : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (i : Fin a),
    Function.Bijective (L.T i) := by
  intro n a g Λ _ L i
  haveI := L.fin
  let e : Λ ≃ₗ[ℤ] Module.Dual ℤ Λ := LinearEquiv.ofBijective L.E L.unimod
  let S : Λ →ₗ[ℤ] Λ := e.symm.toLinearMap ∘ₗ (L.T i).dualMap ∘ₗ e.toLinearMap
  have hS : ∀ x, S (L.T i x) = x := by
    intro x
    apply e.injective
    simp only [S, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    ext y
    simpa [e, LinearMap.dualMap_apply] using monodromy_preserves_form L i x y
  have hSsurj : Function.Surjective S := fun x => ⟨_, hS x⟩
  have hSinj : Function.Injective S := OrzechProperty.injective_of_surjective_endomorphism S hSsurj
  refine ⟨Function.LeftInverse.injective hS, fun y => ⟨S y, hSinj (hS (S y))⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

theorem _root_.GlobalTheory.T.complex_coords_added : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, addJ J N k) → ℂ),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → IsCptGen ξ' →
    (∀ q : X', genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordsAt ξ' (addY y x') z w → CoordsAt ξ y (z ≫ f) (fun p => w (addV J N p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict.coordsAt_restrict | exact GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict.coordsAt_restrict | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict.coordsAt_restrict <;> assumption)
end

section

open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

theorem _root_.GlobalTheory.T.glued_lattice_localization : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (T : FinitePlace L → Matrix (Fin n) (Fin n) L), (∀ v, (T v).det ≠ 0) → {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite → ∀ v, locAt v (glued T) = locAt v (frame (T v)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued <;> assumption)
end
