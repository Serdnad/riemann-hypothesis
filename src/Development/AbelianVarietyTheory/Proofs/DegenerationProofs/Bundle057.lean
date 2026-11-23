module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedGenericFibreOfDense
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle045
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Mathlib.RingTheory.Nullstellensatz
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VanishingIdealConePrimeHomogeneous
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.Weights

def eLeft (g n : ℕ) (x : Fin g ⊕ Fin g → ZMod n) : (Fin g ⊕ Fin g → ZMod n) →+ ZMod n :=
  AddMonoidHom.mk' (fun a => eStd g n a x) (by
    intro a b
    simp only [eStd, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring)

theorem eLeft_apply (g n : ℕ) (x a : Fin g ⊕ Fin g → ZMod n) : eLeft g n x a = eStd g n a x := rfl

theorem eStd_swap (g n : ℕ) (x a : Fin g ⊕ Fin g → ZMod n) : eStd g n a x = -eStd g n x a := by
  simp only [eStd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem addHom_ext_single {d n : ℕ} [NeZero n] {A : Type*} [AddCommGroup A] (f f' : (Fin d → ZMod n) →+ A)
    (h : ∀ i, f (Pi.single i 1) = f' (Pi.single i 1)) : f = f' := by
  refine AddMonoidHom.functions_ext _ _ _ fun i z => ?_
  have : (Pi.single i z : Fin d → ZMod n) = z.val • (Pi.single i 1 : Fin d → ZMod n) := by
    rw [← Pi.single_nsmul]
    simp
  rw [this, map_nsmul, map_nsmul, h]

theorem exists_eStd_eq {g d n : ℕ} [NeZero n]
    (φ : (Fin d → ZMod n) →+ (Fin g ⊕ Fin g → ZMod n)) (hφ : Function.Injective φ)
    (a : Fin d → ZMod n) : ∃ x, ∀ i, eStd g n (φ (Pi.single i 1)) x = a i := by
  obtain ⟨F, hF⟩ := (GlobalTheory.ZModPerp.baer_zmod n).extension_property (φ.toZModLinearMap n) hφ
    (Fintype.linearCombination (ZMod n) a)
  refine ⟨Sum.elim (fun i => -F (Pi.single (.inr i) 1)) (fun i => F (Pi.single (.inl i) 1)),
    fun i => ?_⟩
  have h1 : F (φ (Pi.single i 1)) = a i := by
    have := LinearMap.congr_fun hF (Pi.single i 1)
    simpa using this
  rw [← h1, LinearMap.pi_apply_eq_sum_univ F, Fintype.sum_sum_type, eStd, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∀ k : Fin g ⊕ Fin g, (fun j => if k = j then (1 : ZMod n) else 0) = Pi.single k 1 := by
    intro k
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [Sum.elim_inl, Sum.elim_inr, smul_eq_mul, e]
  ring

theorem exists_min {X : Type} [AddCommGroup X] (q : X → ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (N : ℕ) (β : X) :
    ∃ v : X, ∀ v₀ : X, q (β + N • v) ≤ q (β + N • v + N • v₀) := by
  let s : Set X := Set.range fun v : X => β + N • v
  have : Nonempty s := ⟨⟨_, 0, rfl⟩⟩
  obtain ⟨⟨_, v, rfl⟩, hv⟩ := Filter.Tendsto.exists_forall_le (f := fun a : s => q a)
    (hq.comp Subtype.val_injective.tendsto_cofinite)
  refine ⟨v, fun v₀ => ?_⟩
  have := hv ⟨_, v + v₀, rfl⟩
  simpa [add_assoc] using this

end GlobalTheory.ZH.Weights

namespace GlobalTheory.ZH

open Weights

theorem test_weights : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω), (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) := by
  intro o Ω _ _ _ _ S p _ y₀ τ
  have hN : S.N ≠ 0 := by have := S.N_ge; omega
  have hr : S.r ≠ 0 := by have := S.r_pos; omega
  have : NeZero (S.r * S.N) := ⟨mul_ne_zero hr hN⟩
  have : NeZero S.N := ⟨hN⟩
  have hwt : ∀ v : τ.X, τ.wt (S.N • v) = 0 := fun v => by
    ext t
    rw [map_nsmul, AddMonoidHom.nsmul_apply]
    simp
  refine ⟨fun c => ?_, fun T hT hle w hw I hI α => ⟨fun h => ?_, fun h t h₂ ht => ?_⟩⟩
  · obtain ⟨-, d, ⟨E⟩⟩ := τ.isoFree
    obtain ⟨x, hx⟩ := exists_eStd_eq ((S.perp τ.yy.ker).subtype.comp E.symm.toAddMonoidHom)
      (Subtype.val_injective.comp E.symm.injective)
      (fun i => ((c (E.symm (Pi.single i 1))).val : ZMod (S.r * S.N)))
    obtain ⟨β, hβ⟩ := QuotientAddGroup.mk_surjective (τ.yy x)
    obtain ⟨v, hv⟩ := exists_min τ.q τ.pos S.N β
    refine ⟨_, hv, ?_⟩
    rw [map_add (f := _), hwt, add_zero]
    have := addHom_ext_single ((τ.wt β).comp E.symm.toAddMonoidHom) (c.comp E.symm.toAddMonoidHom) fun i => by
      have h1 := τ.wt_eq x β hβ.symm (E.symm (Pi.single i 1))
      have h2 : eStd S.g _ (E.symm (Pi.single i 1) : S.Gam) x = _ := hx i
      rw [h2, map_natCast, ZMod.natCast_zmod_val] at h1
      exact h1
    ext t
    simpa using DFunLike.congr_fun this (E t)
  · obtain ⟨-, d, ⟨E⟩⟩ := hT
    obtain ⟨x, hx⟩ := τ.yy_onto (QuotientAddGroup.mk α)
    have key : ∀ t : T, ∃ a : ZMod (S.r * S.N), eStd S.g _ (t : S.Gam) x = S.N • a := fun t => by
      have h1 := τ.wt_eq x α hx ⟨t, hle t.2⟩
      rw [h t _ t.2, ZMod.castHom_apply, ZMod.cast_eq_val, eq_comm,
        ZMod.natCast_eq_zero_iff] at h1
      obtain ⟨k, hk⟩ := h1
      refine ⟨k, ?_⟩
      rw [← ZMod.natCast_zmod_val (eStd S.g _ (t : S.Gam) x), hk]
      simp
    choose a ha using key
    obtain ⟨b, hb⟩ := exists_eStd_eq (T.subtype.comp E.symm.toAddMonoidHom)
      (Subtype.val_injective.comp E.symm.injective) (fun i => a (E.symm (Pi.single i 1)))
    have h3 := addHom_ext_single ((eLeft S.g _ x).comp (T.subtype.comp E.symm.toAddMonoidHom))
      (S.N • (eLeft S.g _ b).comp (T.subtype.comp E.symm.toAddMonoidHom)) fun i => by
        exact (ha _).trans (congrArg (S.N • ·) (hb i).symm)
    have h4 : x - S.N • b ∈ S.perp T := fun t ht => by
      have h5 : eStd S.g _ t x = S.N • eStd S.g _ t b := by
        simpa [eLeft_apply] using DFunLike.congr_fun h3 (E ⟨t, ht⟩)
      rw [← eLeft_apply, map_sub, map_nsmul, eLeft_apply, eLeft_apply, eStd_swap, h5,
        eStd_swap _ _ t b]
      simp
    set L := AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀) with hL
    have hNL : ∀ v : τ.X, S.N • v ∈ L := fun v => AddSubgroup.subset_closure (Or.inr ⟨v, rfl⟩)
    have h6 : S.perp T ≤ (L.map (QuotientAddGroup.mk' _)).comap τ.yy := by
      rw [← hI, AddSubgroup.closure_le]
      intro i hi
      exact ⟨w i, AddSubgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩), (hw i).symm⟩
    obtain ⟨l, hl, hl'⟩ := h6 h4
    rw [map_sub, map_nsmul, hx, hw, QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk_nsmul,
      ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq] at hl'
    obtain ⟨u, hu⟩ := hl'
    have h7 : α = l + S.N • w b + S.N • (S.r • u) := by
      rw [← mul_nsmul, show (S.r * S.N) • u = _ from hu]
      abel
    rw [h7]
    exact L.add_mem (L.add_mem hl (hNL _)) (hNL _)
  · induction h using AddSubgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨i, hi, rfl⟩ | ⟨v, rfl⟩
      · have hi' : i ∈ S.perp T := hI ▸ AddSubgroup.subset_closure hi
        rw [τ.wt_eq i _ (hw i), eStd_swap, hi' t ht]
        simp
      · rw [hwt]
        rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), AddMonoidHom.add_apply, hx, hy, add_zero]
    | neg x _ hx => rw [map_neg, AddMonoidHom.neg_apply, hx, neg_zero]

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

namespace ModHilb

theorem finrank_span_reduction_le {O K I A B : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite I] (f : I → A → K) (g : I → B → IsLocalRing.ResidueField O)
    (h : ∀ b : B, ∃ (a : A) (w : I → O), ∀ i, f i a = algebraMap O K (w i) ∧ g i b = IsLocalRing.residue O (w i)) :
    Module.finrank (IsLocalRing.ResidueField O) (Submodule.span (IsLocalRing.ResidueField O) (Set.range g)) ≤
      Module.finrank K (Submodule.span K (Set.range f)) := by
  first
  | exact @_root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le
  | exact _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le
  | (apply _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le ..)

theorem hilb_eq_finrank_span {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    hilb C d = Module.finrank k (Submodule.span k (Set.range
      fun (m : {m : J →₀ ℕ // m.degree = d}) (v : C) => m.1.prod fun j n => v.1 j ^ n)) := by
  unfold hilb
  have : (MvPolynomial.homogeneousSubmodule J k d).map
      (LinearMap.pi fun v : C => (MvPolynomial.aeval (R := k) v.1).toLinearMap) =
      Submodule.span k (Set.range
      fun (m : {m : J →₀ ℕ // m.degree = d}) (v : C) => m.1.prod fun j n => v.1 j ^ n) := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    rw [AddMonoidAlgebra.supported_eq_span_single, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      refine ⟨⟨m, hm⟩, ?_⟩
      funext v
      change _ = MvPolynomial.aeval v.1 (MvPolynomial.monomial m (1 : k))
      simp [MvPolynomial.aeval_monomial]
    · rintro ⟨⟨m, hm⟩, rfl⟩
      refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
      funext v
      change MvPolynomial.aeval v.1 (MvPolynomial.monomial m (1 : k)) = _
      simp [MvPolynomial.aeval_monomial]
  rw [this]

theorem hilb_reduction_le : (∀ (O K J : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Fintype J] (C : Set (J → K)) (C' : Set (J → IsLocalRing.ResidueField O)), (∀ v' ∈ C', ∃ w : J → O, (fun j => algebraMap O K (w j)) ∈ C ∧ v' = fun j => IsLocalRing.residue O (w j)) → ∀ d, hilb C' d ≤ hilb C d) := by
  intro O K J _ _ _ _ _ _ _ C C' h d
  rw [hilb_eq_finrank_span, hilb_eq_finrank_span]
  haveI : Finite {m : J →₀ ℕ // m.degree = d} :=
    (Finsupp.finite_of_degree_eq d).to_subtype
  apply finrank_span_reduction_le
  rintro ⟨v', hv'⟩
  obtain ⟨w, hw, rfl⟩ := h v' hv'
  refine ⟨⟨_, hw⟩, fun m => m.1.prod fun j n => w j ^ n, fun m => ⟨?_, ?_⟩⟩
  · simp [Finsupp.prod]
  · simp [Finsupp.prod]

end ModHilb

theorem Mod.hilb_special_le_generic : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls) (d : ℕ), hilb (cone m.Φ.G.hom (m.Φ.H 1) m.F) d ≤ hilb {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ G.left, a ≫ G.hom = gPt p ≫ spMap j ∧ Crd H σ a w} d := by
  intro p _ V _ j G _ g N _ X _ q H J _ σ cls m d
  refine ModHilb.hilb_reduction_le (OO p) (PadicAlgCl p) J _ _ ?_ d
  rintro v ⟨x, hx, hv⟩
  have hred : Crd H σ (x ≫ m.r) v := m.red (Over.homMk x hx) v hv
  haveI := m.smooth
  haveI : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  obtain ⟨c, hc, hcx⟩ := GlobalTheory.ZJ.exists_classical_lift_of_smooth p G.left (Sp V) G.hom (spMap j)
    (x ≫ m.r) (by
      rw [Category.assoc, m.cart.1.w, ← Category.assoc, hx]
      exact Category.id_comp _)
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists m.isLB σ c
  have hw' : Crd H σ (x ≫ m.r) (fun i => IsLocalRing.residue (OO p) (w i)) := by
    rw [← hcx]
    exact CrdCalc.crd_map _ hw
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique hw' hred
  obtain ⟨u₀, hu₀⟩ := IsLocalRing.residue_surjective (u : kb p)
  have hunit : IsUnit u₀ := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hu₀]
    exact u.ne_zero
  obtain ⟨u₁, rfl⟩ := hunit
  refine ⟨fun i => (u₁ : OO p) * w i, ⟨gPt p ≫ c, by rw [Category.assoc, hc], ?_⟩, ?_⟩
  · exact CrdCalc.crd_map (OO p).subtype (CrdCalc.crd_smul u₁ hw)
  · funext i
    rw [hu, map_mul, hu₀]

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.GenericSplit

theorem geometricallyConnected_snd_of_range_subset {X S T T' : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (t' : T' ⟶ S)
    (hr : Set.range t' ⊆ Set.range t) (h : GeometricallyConnected (pullback.snd f t)) :
    GeometricallyConnected (pullback.snd f t') := by
  refine ⟨fun L _ y Z fst snd H ↦ ?_⟩
  have H' : IsPullback (fst ≫ pullback.fst f t') snd f (y ≫ t') :=
    H.paste_horiz (.of_hasPullback f t')
  obtain ⟨s, hs⟩ := hr ⟨y (default : PrimeSpectrum L), rfl⟩
  obtain ⟨w, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback (y ≫ t') t)
    (default : PrimeSpectrum L) s ((Scheme.Hom.comp_apply _ _ _).trans hs.symm)
  let m := (pullback (y ≫ t') t).fromSpecResidueField w
  let m₁ := m ≫ pullback.fst (y ≫ t') t
  let m₂ := m ≫ pullback.snd (y ≫ t') t
  have hm : m₁ ≫ y ≫ t' = m₂ ≫ t := by
    simp only [m₁, m₂, Category.assoc, pullback.condition]
  have H1 : IsPullback (pullback.fst snd m₁ ≫ fst ≫ pullback.fst f t') (pullback.snd snd m₁) f (m₂ ≫ t) := by
    rw [← hm]
    exact (IsPullback.of_hasPullback snd m₁).paste_horiz H'
  have H2 : IsPullback (pullback.lift _ _ (H1.w.trans (Category.assoc _ _ _).symm)) (pullback.snd snd m₁)
      (pullback.snd f t) m₂ := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f t) (v₁₃ := f) (h₂₂ := t) ?_
      (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
    rw [pullback.lift_fst]
    exact H1
  have hc : ConnectedSpace ↥(pullback snd m₁) := h.geometrically_connectedSpace _ _ _ H2
  have : Surjective m₁ := ⟨fun z ↦ ⟨(default : PrimeSpectrum _), Subsingleton.elim (α := PrimeSpectrum L) _ _⟩⟩
  have hsurj : Function.Surjective (pullback.fst snd m₁) := (pullback.fst snd m₁).surjective
  exact hsurj.connectedSpace (pullback.fst snd m₁).continuous

theorem jK_asIdeal (R : Type) [CommRing R] [IsDomain R] (z : Sp (FractionRing R)) :
    (Out.jK R z).asIdeal = ⊥ := by
  have hz : z.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal
    (Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z ⟨⊥, Ideal.isPrime_bot⟩)
  change Ideal.comap (algebraMap R (FractionRing R)) z.asIdeal = ⊥
  rw [hz]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)

theorem geometricallyConnected_and_basePointFree_generic :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → GeometricallyConnected ((Over.pullback (Out.jK R)).obj G).hom ∧ ∀ (n : Fin d) (x : ((Over.pullback (Out.jK R)).obj G).left), ∃ a j, C.wt j = c n ∧ x ∈ ((Over.pullback (Out.jK R)).obj G).left.basicOpen ((C.pull (pullback.fst G.hom (Out.jK R))).r a j) := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS
  constructor
  · have h := geometricallyConnected_genericFibre_of_dense G.left (Sp R) G.hom Sg hD fun x hx ↦ by
      obtain ⟨K, _, t, _, ht, hc, -⟩ := hS x hx
      exact geometricallyConnected_snd_of_range_subset G.hom t _
        (by rw [Scheme.range_fromSpecResidueField, ht]) hc
    refine geometricallyConnected_snd_of_range_subset G.hom _ _ ?_ h
    rw [Scheme.range_fromSpecResidueField]
    rintro _ ⟨z, rfl⟩
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (jK_asIdeal R z)
  · intro n x
    let V : G.left.Opens := ⨆ (a) (j) (_ : C.wt j = c n), G.left.basicOpen (C.r a j)
    obtain ⟨b, hb0, hb⟩ := GenericEq.exists_mem_of_not_mem R G Sg hD V fun y hy ↦ by
      obtain ⟨K, _, t, _, ht, -, i, hi⟩ := hS _ hy
      obtain ⟨s, hs⟩ : G.hom y ∈ Set.range t := ht ▸ rfl
      obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback G.hom t) y s hs.symm
      obtain ⟨a, j, hj, hz'⟩ := hi.bpf n z
      have : z ∈ pullback.fst G.hom t ⁻¹ᵁ G.left.basicOpen (C.r a j) := by
        rw [Scheme.preimage_basicOpen]
        exact hz'
      simp only [V, TopologicalSpace.Opens.mem_iSup]
      exact ⟨a, j, hj, hz ▸ this⟩
    have hx := hb (pullback.fst G.hom (Out.jK R) x) (by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, jK_asIdeal]
      exact hb0)
    simp only [V, TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨a, j, hj, hx⟩ := hx
    refine ⟨a, j, hj, ?_⟩
    have : x ∈ pullback.fst G.hom (Out.jK R) ⁻¹ᵁ G.left.basicOpen (C.r a j) := hx
    rw [Scheme.preimage_basicOpen] at this
    exact this

end GlobalTheory.GenericSplit
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem ThetaSys.FF_div_FF_mem_O_of_valuationRing :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → ∀ x₀ ∈ S.supI M z, ∀ j : ℕ, 1 ≤ j → ∃ C : ℕ, (S.FF _ c' k' / S.th x₀) ^ (j + 1) * (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) ^ C / (S.FF _ c k / S.th x₀) ^ j ∈ M.O z) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → IsDomain (M.O ξ) → ValuationRing (M.O ξ) → IsNoetherianRing (M.O ξ) → S.FF _ c' k' / S.FF _ c k ∈ M.O ξ) := by
  intro o Ω _ _ _ _ S M U₀ hO _ H z ξ c c' k k' hz hs hc hk hk' _ hv hn
  obtain ⟨x₀, hx₀⟩ := hO.div z
  have hx₀' : M.Div S.th x₀ ξ := hx₀.of_specializes hs
  have h0 : S.th x₀ ≠ 0 := hx₀.1
  have hP : (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) ≠ 0 ∧ (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀)⁻¹ ∈ M.O ξ := by
    refine finprod_mem_induction (fun u : Ω => u ≠ 0 ∧ u⁻¹ ∈ M.O ξ) ⟨one_ne_zero, by simp⟩ ?_ ?_
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨mul_ne_zero ha hb, by rw [mul_inv]; exact mul_mem ha' hb'⟩
    · intro x hx
      have hx' : M.Div S.th x ξ := hx
      exact ⟨div_ne_zero hx'.1 h0, by rw [inv_div]; exact hx'.2 x₀⟩
  have hval : ∀ x : Ω, x ∈ (M.O ξ).toSubring ∨ x⁻¹ ∈ (M.O ξ).toSubring := by
    intro x
    rcases ValuationRing.isInteger_or_isInteger (M.O ξ) x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact Or.inl (hy ▸ y.2)
    · exact Or.inr (hy ▸ y.2)
  haveI : ValuationRing (M.O ξ).toSubring := hv
  haveI : IsNoetherianRing (M.O ξ).toSubring := hn
  have key := div_mem_of_forall_pow_succ_div_pow_mem Ω (M.O ξ).toSubring hval
    (S.FF _ c k / S.th x₀) (S.FF _ c' k' / S.th x₀) (div_ne_zero hk.1 h0) (div_ne_zero hk'.1 h0) (by
      intro j hj
      obtain ⟨C, hC⟩ := H z ξ c c' k k' hz hs hc hk hk' x₀ hx₀ j hj
      have h1 := mul_mem (RatModel.O_le_of_specializes hs hC) (pow_mem hP.2 C)
      have hP1 := hP.1
      generalize (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) = P at h1 hP1
      rw [div_mul_eq_mul_div, _root_.mul_assoc, ← _root_.mul_pow, mul_inv_cancel₀ hP1, _root_.one_pow, _root_.mul_one] at h1
      exact h1)
  rw [div_div_div_cancel_right₀ h0] at key
  exact key

end GlobalTheory.ZH
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.exists_invertible_matrix_change_of_span_eq : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) [Fintype J] [DecidableEq J] (W W' : M.Z.Opens) (b B : Matrix J J Ω) (c : Matrix J J Γ(M.Z, W')), (∀ z ∈ W ⊓ W', Submodule.span (M.O z) (Set.range b) = Submodule.span (M.O z) (Set.range B)) → c.map (valF M.pt W') * B = 1 → ∃ m m' : Matrix J J Γ(M.Z, W ⊓ W'), m * m' = 1 ∧ (((W ⊓ W' : M.Z.Opens) : Set M.Z).Nonempty → m.map (valF M.pt (W ⊓ W')) = b * c.map (valF M.pt W')) := by
  first | exact @GlobalTheory.ZH.exists_matrix_mul_eq_one_of_span_eq | exact GlobalTheory.ZH.exists_matrix_mul_eq_one_of_span_eq | (intros; apply GlobalTheory.ZH.exists_matrix_mul_eq_one_of_span_eq <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.exists_hom_spec_of_le_ringOn' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω), (U₀ : Set M.Z).Nonempty → R ≤ M.ringOn U₀ → ∃ u₀ : U₀.toScheme ⟶ Sp R, ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom := by
  first | exact @GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn | exact GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn | (intros; apply GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
theorem _root_.GlobalTheory.T.exists_projectiveClosure_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (n : ℕ) (t : Fin (n + 1) → Ω), (∃ i, t i ≠ 0) → Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤ → ∃ M : RatModel o Ω, M.IsCl t ∧ IsProjOver M.s := by
  first | exact @GlobalTheory.ZH.exists_isCl_isProjOver | exact GlobalTheory.ZH.exists_isCl_isProjOver | (intros; apply GlobalTheory.ZH.exists_isCl_isProjOver <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.torsionClasses_descend_finite_algebra : ∀ (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (S : ValuationSubring F), (∀ x, x ∈ S ↔ IsIntegral O x) → ∀ (N : NumD F) (K₁ : IntermediateField (FractionRing O) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing O) K₁ → (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) → (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) → (∀ x ∈ A₀, N.th x ∈ K₁) → (∀ χ, (N.ψ χ : F) ∈ K₁) → (∀ x y u, S.valuation (N.θ x y u : F) = 1) → (∀ x, S.valuation (N.σ x : F) = 1) → (∀ x, N.th x ∈ S) → (∀ χ, S.valuation (N.ψ χ : F) = 1) → ∀ (Ix : Type) [Finite Ix] (k : Ix → ℕ) (p : ∀ i, N.QT (k i)), (∀ i, 0 < k i) → (∀ i, (p i).1.2.b ∈ A₀) → ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∃ (N₀ : NumD O₁) (I : NumD.Hom O₁.val.toRingHom N₀ N), I.lam = 1 ∧ ∀ i (p' : N.QT (k i)), N.QEq (p i) p' → ∃ p₀ : N₀.QT (k i), p'.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p'.1.2 := by
  first | exact @GlobalTheory.Ex.TorsDesc.descend | exact GlobalTheory.Ex.TorsDesc.descend | (intros; apply GlobalTheory.Ex.TorsDesc.descend <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_positiveDefinite_quadraticForm_endomorphisms : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∃ Q : (B ⟶ B) → ℤ, (∀ f g, Q (f * g) + Q (f * g⁻¹) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ (∀ f, IsMonHom f → Q f = 0 → f = 1) ∧ ∀ (F : B ⟶ B) (q : ℤ), PullPow F.left L q → ∀ f, Q (f ≫ F) = q * Q f := by
  first | exact @GlobalTheory.SS.exists_quadraticForm_end | exact GlobalTheory.SS.exists_quadraticForm_end | (intros; apply GlobalTheory.SS.exists_quadraticForm_end <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
theorem _root_.GlobalTheory.T.vanishing_ideal_cone_prime_homogeneous : (∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) [Fintype J] (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → IsIntegral X → ∀ g : ℕ, SmoothOfRelativeDimension g p → (MvPolynomial.vanishingIdeal k (cone p H s)).IsPrime ∧ (MvPolynomial.vanishingIdeal k (cone p H s)).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) ∧ (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k (cone p H s)) ∧ ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k (cone p H s)) = (g + 1 : ℕ)) := by
  first | exact @GlobalTheory.ZH.ConePrime.isPrime_vanishingIdeal_cone | exact GlobalTheory.ZH.ConePrime.isPrime_vanishingIdeal_cone | (intros; apply GlobalTheory.ZH.ConePrime.isPrime_vanishingIdeal_cone <;> assumption)
end
