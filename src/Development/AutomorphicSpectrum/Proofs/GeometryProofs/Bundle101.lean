module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Mathlib.LinearAlgebra.Dual.Basis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwTan
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeCptCompare
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FlagDataMatchUnderTwist
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationRingCentreInChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle088
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeEigenDecompositionLocal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagRead

open GlobalTheory.CompanionTheory.Ar.FlagPull

theorem fieldRange_finite {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (i : Ω₁ →+* Ω)
    (hfin : letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) :
    FiniteDimensional i.fieldRange Ω ∧
      Module.finrank i.fieldRange Ω = (letI := i.toAlgebra; Module.finrank Ω₁ Ω) := by
  letI := i.toAlgebra
  haveI := hfin
  let e : Ω₁ ≃+* i.fieldRange := RingEquiv.ofBijective i.rangeRestrictField
    ⟨fun x y h => i.injective (congrArg Subtype.val h), fun x => by
      obtain ⟨a, ha⟩ := x.2
      exact ⟨a, Subtype.ext ha⟩⟩
  have he : (algebraMap i.fieldRange Ω).comp (e : Ω₁ →+* i.fieldRange) =
      ((RingEquiv.refl Ω : Ω ≃+* Ω) : Ω →+* Ω).comp (algebraMap Ω₁ Ω) := by
    ext x
    rfl
  exact ⟨Module.Finite.of_equiv_equiv e (RingEquiv.refl Ω) he,
    (Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl Ω) he).symm⟩

theorem span_eq_of_indep {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b b' : Fin r → V}
    {W : Submodule Ω V} (hb : LinearIndependent Ω b) (hle : ∀ k, b k ∈ W) (hb' : LinearIndependent Ω b')
    (hs : Submodule.span Ω (Set.range b') = W) : Submodule.span Ω (Set.range b) = W := by
  subst hs
  haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range b')) :=
    FiniteDimensional.span_of_finite Ω (Set.finite_range _)
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨k, rfl⟩
    exact hle k
  · rw [finrank_span_eq_card hb, finrank_span_eq_card hb']

theorem generic_read : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module B.Ω₀ Li₀) (M₀ : LieModel Y.t.G B.ξ₀ Li₀) (j : Li₀ →+ B.Li) (V₀ : CMType H ⊕ CMType H → Submodule B.Ω₀ Li₀), (∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s) ∧ (∀ e, (B.M.pt (j e)).left ≫ B.m.φ = spMap (dualMap B.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ B.Vgen s) ∧ (letI := B.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ (fun s a => jA (Fl.b s a)) ((letI := i.toAlgebra; Module.finrank Ω₁ Ω) * Fl.deg)) := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A Fl B i h jA hfin hd hf hcst hj hpt hρ
  obtain ⟨hfd, hfr⟩ := fieldRange_finite i hfin
  haveI := hfd
  have hgen : genPt A.ξ₀ = genPt B.ξ₀ := by
    have h1 := RegAtDom.map_genPt hd
    have h2 := RegAtDom.map_genPt A.fn_over
    have h3 := RegAtDom.map_genPt B.fn_over
    rw [← h2, ← h3, ← h1, hf]
    rfl
  obtain ⟨ψ, hψ⟩ := exists_iso A.gen₀ B.gen₀ hgen
  have hfn : B.fn.comp ψ.toRingHom = i.comp A.fn := by
    haveI := mono_of_isCptGen A.gen₀
    have e1 : spMap B.fn ≫ B.ξ₀ = B.ξ ≫ B.f := B.fn_over.symm
    have e2 : spMap A.fn ≫ A.ξ₀ = A.ξ ≫ A.f := A.fn_over.symm
    have e3 : B.ξ ≫ h = spMap i ≫ A.ξ := hd
    have e4 : spMap (B.fn.comp ψ.toRingHom) = spMap (i.comp A.fn) := by
      refine (cancel_mono A.ξ₀).1 ?_
      rw [FlagPull.spMap_comp, FlagPull.spMap_comp, Category.assoc, Category.assoc, hψ, e1, e2, hf, ← Category.assoc, e3,
        Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e4)
  letI mod' : Module B.Ω₀ Fl.Li₀ := Module.compHom _ ψ.symm.toRingHom
  have hs : ∀ (a : A.Ω₀) (e : Fl.Li₀), ψ a • e = a • e := fun a e => by
    show ψ.symm (ψ a) • e = a • e
    rw [ψ.symm_apply_apply]
  have hemb : ∀ s, B.emb s = i.comp (A.emb s) := fun s => by
    simp only [HodgeCpt.emb]
    rw [hcst]
    rfl
  have hVgen : ∀ s w, jA w ∈ B.Vgen s ↔ w ∈ A.Vgen s := fun s w => by
    show jA w ∈ eigSp B.ρ (B.emb s) ↔ w ∈ eigSp A.ρ (A.emb s)
    rw [hemb]
    exact mem_eigSp_iff hj _ _ _ hρ w
  let V₀' : CMType H ⊕ CMType H → Submodule B.Ω₀ Fl.Li₀ := fun s =>
    { carrier := (Fl.V₀ s : Set Fl.Li₀)
      add_mem' := fun ha hb => (Fl.V₀ s).add_mem ha hb
      zero_mem' := (Fl.V₀ s).zero_mem
      smul_mem' := fun c x hx => (Fl.V₀ s).smul_mem (ψ.symm c) hx }
  have hsq : spMap (dualMap i) ≫ spMap (dualMap A.fn) = spMap (dualMap B.fn) ≫ spMap (dualMap ψ.toRingHom) := by
    rw [← FlagPull.spMap_comp, ← FlagPull.spMap_comp, ← dualMap_comp, ← dualMap_comp, hfn]
  have hspan : ∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s := by
    intro s
    letI := A.fn.toAlgebra
    obtain ⟨cc, u, hcV, -, -, hb, -, -, hfl, -⟩ := Fl.generic
    have hmemc : ∀ k, Fl.j (cc s k) ∈ A.Vgen s := fun k => (Fl.V₀_mem s _).1 (by
      rw [← (hcV s).2]
      exact Submodule.subset_span ⟨k, rfl⟩)
    have hbk : ∀ a, Fl.b s a ∈ A.Vgen s := by
      intro a
      have h1 : Fl.b s a ∈ flagStep Ω₁ (Fl.b s) (labelRk D s) := Submodule.subset_span ⟨a, a.2, rfl⟩
      rw [hfl s] at h1
      refine (Submodule.span_le (p := A.Vgen s).2 ?_) h1
      rintro _ ⟨k, -, rfl⟩
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmemc l)
    obtain ⟨U, hU, b', hb', hfr'⟩ := B.vb s ⟨genPt B.ξ, specializes_rfl⟩ (Set.mem_univ _)
    exact span_eq_of_indep (hj.2 _ _ (hb s)) (fun k => (hVgen s _).2 (hbk k))
      (hfr' _ (Set.mem_univ _) hU).1 hb'
  refine ⟨Fl.Li₀, Fl.acg, mod', transport ψ hψ hs Fl.M₀, jA.comp Fl.j, V₀', hspan, fun e => ?_,
    fun s e => (Fl.V₀_mem s e).trans (hVgen s _).symm, ?_⟩
  · show (B.M.pt (jA (Fl.j e))).left ≫ B.m.φ =
      spMap (dualMap B.fn) ≫ spMap (dualMap ψ.toRingHom) ≫ (Fl.M₀.pt e).left
    rw [hpt, Fl.j_pt, ← Category.assoc, hsq, Category.assoc]
  · have := genericFlag_pull A.fn B.fn ψ i hfn hs Fl.j jA hj Fl.V₀ V₀' (fun _ _ => Iff.rfl) Fl.b Fl.deg Fl.generic
    rw [hfr] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.FlagRead
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

def preDualBasis {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] {r : ℕ}
    (B : Module.Basis (Fin r) Ω (Module.Dual Ω V)) : Module.Basis (Fin r) Ω V :=
  B.dualBasis.map (Module.evalEquiv Ω V).symm

theorem apply_preDualBasis {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V]
    {r : ℕ} (B : Module.Basis (Fin r) Ω (Module.Dual Ω V)) (i j : Fin r) :
    B i (preDualBasis B j) = if i = j then 1 else 0 := by
  have h : ∀ x : Module.Dual Ω (Module.Dual Ω V), B i ((Module.evalEquiv Ω V).symm x) = x (B i) := by
    intro x
    obtain ⟨y, rfl⟩ := (Module.evalEquiv Ω V).surjective x
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [preDualBasis, Module.Basis.map_apply, h, Module.Basis.dualBasis_apply_self]

theorem sum_apply_smul_preDualBasis {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    [FiniteDimensional Ω V] {r : ℕ} (B : Module.Basis (Fin r) Ω (Module.Dual Ω V)) (v : V) :
    ∑ i, B i v • preDualBasis B i = v := by
  have hc : ∀ i, (preDualBasis B).coord i = B i := by
    intro i
    refine (preDualBasis B).ext (fun j => ?_)
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, apply_preDualBasis, Finsupp.single_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  conv_rhs => rw [← (preDualBasis B).sum_repr v]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Module.Basis.coord_apply, hc]

theorem Lat.predualIn_isFrameAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {Li : Type} [AddCommGroup Li]
    [Module Ω Li] {L : Lat ξ (Module.Dual Ω Li)} {V : Submodule Ω Li} [FiniteDimensional Ω V] {r : ℕ}
    (B : Module.Basis (Fin r) Ω (Module.Dual Ω V)) {q : Cpt ξ}
    (h : (L.map V.dualRestrict) q = Submodule.span (regAt ξ q) (Set.range B)) :
    (L.predualIn V).IsFrameAt (fun j => (preDualBasis B j : Li)) q := by
  have hB : ∀ i, ∃ w ∈ L q, V.dualRestrict w = B i := by
    intro i
    have hi : B i ∈ (L.map V.dualRestrict) q := by
      rw [h]
      exact Submodule.subset_span (Set.mem_range_self i)
    obtain ⟨w, hw, hwe⟩ := (Submodule.mem_map).mp hi
    exact ⟨w, hw, hwe⟩
  have hw : ∀ w ∈ L q, ∀ j, w (preDualBasis B j : Li) ∈ regAt ξ q := by
    intro w hwL j
    have hm : V.dualRestrict w ∈ (L.map V.dualRestrict) q := Submodule.mem_map_of_mem hwL
    rw [h] at hm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hm
    have hj : (∑ i, c i • B i) (preDualBasis B j) = w (preDualBasis B j : Li) := by
      rw [hc]
      rfl
    have hj' : (∑ i, c i • B i) (preDualBasis B j) = (c j : Ω) := by
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, apply_preDualBasis]
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl, Subring.smul_def, smul_eq_mul, _root_.mul_one]
      · intro b _ hb
        rw [if_neg hb, smul_zero]
      · intro hj0
        exact absurd (Finset.mem_univ j) hj0
    rw [← hj, hj']
    exact (c j).2
  refine ⟨(preDualBasis B).linearIndependent.map' V.subtype (Submodule.ker_subtype V), ?_⟩
  apply le_antisymm
  · intro v hv
    obtain ⟨hvV, hvw⟩ := hv
    have hcoef : ∀ i, B i ⟨v, hvV⟩ ∈ regAt ξ q := by
      intro i
      obtain ⟨w, hwL, hwe⟩ := hB i
      rw [← hwe, Submodule.dualRestrict_apply]
      exact hvw w hwL
    have hv' : v = ∑ i, B i ⟨v, hvV⟩ • (preDualBasis B i : Li) := by
      have hs := congrArg Subtype.val (sum_apply_smul_preDualBasis B ⟨v, hvV⟩)
      rw [Submodule.coe_sum] at hs
      simpa only [Submodule.coe_smul] using hs.symm
    rw [hv']
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have he : B i ⟨v, hvV⟩ • (preDualBasis B i : Li) =
        (⟨B i ⟨v, hvV⟩, hcoef i⟩ : regAt ξ q) • (preDualBasis B i : Li) := rfl
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show (preDualBasis B j : Li) ∈ V ∧ ∀ w ∈ L q, w (preDualBasis B j : Li) ∈ regAt ξ q
    exact ⟨(preDualBasis B j).2, fun w hwL => hw w hwL j⟩

theorem Lat.predualIn_isVBOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li]
    [Module Ω Li] (L : Lat ξ (Module.Dual Ω Li)) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω Li)
    [FiniteDimensional Ω V],
    (L.map V.dualRestrict).IsVBOn T r ⊤ → (L.predualIn V).IsVBOn T r V := by
  intro X Ω _ ξ Li _ _ L T r V _ hL p hp
  obtain ⟨U, hpU, b, hbspan, hfr⟩ := hL p hp
  have hli : LinearIndependent Ω b := (hfr p hp hpU).1
  refine ⟨U, hpU, fun j => (preDualBasis (Module.Basis.mk hli hbspan.ge) j : Li), ?_, ?_⟩
  · have he : (fun j => (preDualBasis (Module.Basis.mk hli hbspan.ge) j : Li)) =
        V.subtype ∘ preDualBasis (Module.Basis.mk hli hbspan.ge) := rfl
    rw [he, Set.range_comp, Submodule.span_image, (preDualBasis (Module.Basis.mk hli hbspan.ge)).span_eq,
      Submodule.map_subtype_top]
  · intro q hq hqU
    apply Lat.predualIn_isFrameAt (Module.Basis.mk hli hbspan.ge)
    rw [(hfr q hq hqU).2, Module.Basis.coe_mk]

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.twisted_hodge_cpt_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y') (Fl : A.Flag) (Fl' : A'.Flag) (ψ : A'.Ω₀ ≃+* A.Ω₀) (x₀ : Sp A.Ω₀ ⟶ Xo.XF c) (x₀' : Sp A'.Ω₀ ⟶ Xo.XF c), Mono (spMap β) → Mono (spMap β') → A.ξ₀ = x₀ ≫ Y.j → A'.ξ₀ = x₀' ≫ Y'.j → spMap ψ.toRingHom ≫ x₀' ≫ pullback.fst _ _ = x₀ ≫ pullback.fst _ _ ≫ Φ.hom → spMap ψ.toRingHom ≫ x₀' ≫ pullback.snd _ _ = x₀ ≫ pullback.snd _ _ → ∃ θ : Fl.Li₀ ≃+ Fl'.Li₀, (∀ (a : A'.Ω₀) e, θ (ψ a • e) = a • θ e) ∧ (∀ e, TwTan n Y Y' (Fl.M₀.pt e).left (spMap (dualMap ψ.toRingHom) ≫ (Fl'.M₀.pt (θ e)).left)) ∧ ∀ s s', labelEmb c s' = (labelEmb c s).comp g.s.toRingHom → ∀ e, e ∈ Fl.V₀ s ↔ θ e ∈ Fl'.V₀ s' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieTw.main | exact GlobalTheory.CompanionTheory.Ar.LieTw.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LieTw.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagMatch

theorem matched_generic_flags_carried : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y) (Fl : A.Flag) (Fl' : A'.Flag) (ψ : A'.Ω₀ ≃+* A.Ω₀) (θ : Fl.Li₀ ≃+ Fl'.Li₀) (φ : A.Li ≃ₗ[Ω] A'.Li), Mono (spMap β) → Mono (spMap β') → A.fn.comp ψ.toRingHom = A'.fn → (∀ w, TwTan n Y Y' ((A.M.pt w).left ≫ A.m.φ) ((A'.M.pt (φ w)).left ≫ A'.m.φ)) → (∀ e, TwTan n Y Y' (Fl.M₀.pt e).left (spMap (dualMap ψ.toRingHom) ≫ (Fl'.M₀.pt (θ e)).left)) → (∀ e, φ (Fl.j e) = Fl'.j (θ e)) ∧ ∀ s s' (r : ℕ) (b : Fin r → Fl.Li₀) (u : Matrix (Fin r) (Fin r) Ω), (∀ k, flagStep Ω (Fl.b s) k = flagStep Ω (fun a => ∑ q, u q a • Fl.j (b q)) k) → (∀ k, flagStep Ω (Fl'.b s') k = flagStep Ω (fun a => ∑ q, u q a • Fl'.j (θ (b q))) k) → ∀ k, (flagStep Ω (Fl.b s) k).map φ.toLinearMap = flagStep Ω (Fl'.b s') k :=
  @PositivityTheory.UnitarySelfGeneration.flag_data_match_under_twist

end GlobalTheory.CompanionTheory.Ar.FlagMatch
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

theorem _root_.GlobalTheory.T.valuation_ring_centre_in_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω Ω' : Type) [Field Ω] [Field Ω'] (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (i : Ω →+* Ω') (W : ValuationSubring Ω') (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k j, i (y ⟨k, j⟩ / y ⟨k, c k⟩) ∈ W) → ∃ q : Cpt ξ, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c q ∧ DomBy W.toSubring i ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.exists_domBy_chart | exact GlobalTheory.CompanionTheory.Ar.OrVert.exists_domBy_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.exists_domBy_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

theorem _root_.GlobalTheory.T.hodge_comp_compare_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → ∀ (W : ValuationSubring Ω) (q : Cpt 𝔐.ξ) (q₀ : Cpt 𝔐₀.ξ), DomBy W.toSubring (RingHom.id Ω) 𝔐.ξ q → DomBy W.toSubring i 𝔐₀.ξ q₀ → 𝔐.f q.1 = 𝔐₀.f q₀.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.image_eq_of_domBy | exact GlobalTheory.CompanionTheory.Ar.OrVert.image_eq_of_domBy | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.image_eq_of_domBy <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

private theorem isUnit_det_of_linearIndependent_frame {C W : Type} [Field C] [AddCommGroup W] [Module C W] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (a b : Fin n → W) (h : ∀ i, a i = ∑ k, M i k • b k)
    (ha : LinearIndependent C a) : IsUnit M.det := by
  by_contra hM
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr (by simpa [isUnit_iff_ne_zero] using hM)
  apply hc0
  have hsum : ∑ i, c i • a i = 0 := by
    simp_rw [h, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.sum_smul]
    have hk := congrFun hc k
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hk
    rw [hk, zero_smul]
  exact funext (Fintype.linearIndependent_iff.mp ha c hsum)

private theorem eq_sum_inv_smul_of_eq_sum_smul {C W : Type} [Field C] [AddCommGroup W] [Module C W] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (hM : IsUnit M.det) (a b : Fin n → W) (h : ∀ i, a i = ∑ k, M i k • b k) :
    ∀ i, b i = ∑ k, M⁻¹ i k • a k := by
  intro i
  simp_rw [h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul M hM, Matrix.one_apply, ite_smul,
    one_smul, zero_smul]
  simp

private theorem eq_sum_mul_smul_of_eq_sum_smul_of_eq_sum_smul {C W : Type} [Field C] [AddCommGroup W] [Module C W] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) C) (N : Matrix (Fin m) (Fin m) C) (x : Fin n → W) (y z : Fin m → W)
    (hx : ∀ i, x i = ∑ k, M i k • y k) (hy : ∀ i, y i = ∑ k, N i k • z k) :
    ∀ i, x i = ∑ k, (M * N) i k • z k := by
  intro i
  rw [hx]
  simp_rw [hy, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem det_evaluated_frame : ∀ (E : Type) [Field E] [NumberField E] (C A : Type) [Field C] [CharZero C] [CommRing A] [Algebra A C]
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (g p q : ℕ) (ρC : 𝓞 E →+* Module.End C (Fin g → C))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C)))
    (tC : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (b₁ v : Fin p → Fin g → C) (b₂ w : Fin q → Fin g → C)
    (u : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (Ap : Matrix (Fin (p + q)) (Fin (p + q)) C)
    (P : Matrix (Fin p) (Fin p) C) (Q : Matrix (Fin q) (Fin q) C) (gm : C),
    (∀ a y, (ρHC a y).1 = ρC a y.1) → (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) →
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) →
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A C).range) → HT.IsFreeOn ρHC HV tC →
    IsAdapted ρHC σ b₁ b₂ u → (∀ i, v i = ∑ k, P i k • b₁ k) → (∀ i, w i = ∑ k, Q i k • b₂ k) →
    LinearIndependent C b₁ → (∀ i, HT.eigProj ρHC σ (tC i) = ∑ k, Ap i k • u k) →
    (∀ (v' : Fin p → Fin g → C) (w' : Fin q → Fin g → C)
      (u' : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (B : Matrix (Fin (p + q)) (Fin (p + q)) C),
      LinearIndependent C v' → Submodule.span A (Set.range v') = HT.eigSub ρC σ (stdLat A C g) →
      LinearIndependent C w' → Submodule.span A (Set.range w') = HT.eigSub ρC σ' (stdLat A C g) →
      IsAdapted ρHC σ v' w' u' → LinearIndependent C (fun i => ∑ k, B i k • u' k) →
      Submodule.span A (Set.range fun i => ∑ k, B i k • u' k) = HT.eigQuot ρHC σ HV →
      ∃ ε : Aˣ, B.det = algebraMap A C ε * gm) →
    LinearIndependent C v → Submodule.span C (Set.range v) = HT.eigSp ρC σ →
    Submodule.span A (Set.range v) = HT.eigSub ρC σ (stdLat A C g) →
    LinearIndependent C w → Submodule.span C (Set.range w) = HT.eigSp ρC σ' →
    Submodule.span A (Set.range w) = HT.eigSub ρC σ' (stdLat A C g) →
    ∃ ε : Aˣ, Ap.det * Q.det = algebraMap A C ε * gm * P.det := by
  intro E _ _ C A _ _ _ _ bar σ σ' g p q ρC ρHC HV tC b₁ v b₂ w u Ap P Q gm h1 h2 h3 h4 hA hfree had hvP hwQ hb₁
    hAp H hv hvspan hvA hw hwspan hwA
  obtain ⟨u', hu'ad, -, hu'span⟩ :=
    GlobalTheory.T.hermitian_signature_basis E C (Fin g → C) ρC ρHC bar σ σ' p q v w h1 h2 h3 h4 hv hvspan hw hwspan
  have hP := isUnit_det_of_linearIndependent_frame P v b₁ hvP hv
  have hQ := isUnit_det_of_linearIndependent_frame Q w b₂ hwQ hw
  obtain ⟨B0, hB0, hB0det⟩ := GlobalTheory.T.adapted_bases_change_by_block_matrices E C (Fin g → C) ρHC σ p q v b₁ w b₂ u' u P⁻¹ Q⁻¹ hu'ad had hv
    hu'span (eq_sum_inv_smul_of_eq_sum_smul P hP v b₁ hvP) (eq_sum_inv_smul_of_eq_sum_smul Q hQ w b₂ hwQ)
  have hcomb := eq_sum_mul_smul_of_eq_sum_smul_of_eq_sum_smul Ap B0 (fun i => HT.eigProj ρHC σ (tC i)) u u' hAp hB0
  have hfam : (fun i => ∑ k, (Ap * B0) i k • u' k) = fun i => HT.eigProj ρHC σ (tC i) :=
    funext fun i => (hcomb i).symm
  have hli : LinearIndependent C (fun i => HT.eigProj ρHC σ (tC i)) :=
    GlobalTheory.CompanionTheory.Ar.Flat.HodgeDeterminantLattice.linearIndependent_eigProj σ hfree
  have hsp : Submodule.span A (Set.range fun i => HT.eigProj ρHC σ (tC i)) = HT.eigQuot ρHC σ HV :=
    (GlobalTheory.CompanionTheory.Ar.Flat.HodgeDeterminantLattice.eigQuot_eq_span σ hfree hA).symm
  obtain ⟨ε, hε⟩ := H v w u' (Ap * B0) hv hvA hw hwA hu'ad (by rw [hfam]; exact hli) (by rw [hfam]; exact hsp)
  refine ⟨ε, ?_⟩
  rw [Matrix.det_mul] at hε
  rw [Matrix.det_nonsing_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Ring.inverse_eq_inv] at hB0det
  have hPd : P.det ≠ 0 := hP.ne_zero
  have hQd : Q.det ≠ 0 := hQ.ne_zero
  have hB : B0.det = Q.det * (P.det)⁻¹ := by
    rw [← hB0det, _root_.mul_comm Q.det, _root_.mul_assoc, inv_mul_cancel₀ hQd, _root_.mul_one]
  calc Ap.det * Q.det = Ap.det * B0.det * P.det := by
        rw [hB, _root_.mul_assoc, _root_.mul_assoc, inv_mul_cancel₀ hPd, _root_.mul_one]
    _ = algebraMap A C ε * gm * P.det := by rw [hε]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.hodge_lattice_eigen_decomposition_local : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [CharZero Ω] [AddCommGroup Vs] [Module Ω Vs]
    [FiniteDimensional Ω Vs] (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (bar : 𝓞 E ≃+* 𝓞 E) (R' : Subring Ω) [IsLocalRing R'] (g p q : ℕ) (ℓ : Fin g → Vs)
    (t : Fin (p + q) → Vs × Module.Dual Ω Vs) (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (σ σ' : E →+* Ω),
    (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) →
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) →
    (∀ e, σ e ∈ R') → (∀ e, σ' e ∈ R') →
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ → HodgeAt ρH HL ℓ t →
    Module.finrank Ω (HT.eigSp ρ σ) = p → Module.finrank Ω (HT.eigSp ρ σ') = q →
    ∃ (b₁ : Fin p → Vs) (b₂ : Fin q → Vs) (u : Fin (p + q) → Vs × Module.Dual Ω Vs)
      (A : Matrix (Fin (p + q)) (Fin (p + q)) R'),
      LinearIndependent Ω b₁ ∧ Submodule.span R' (Set.range b₁) = HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ)) ∧
      LinearIndependent Ω b₂ ∧ Submodule.span R' (Set.range b₂) = HT.eigSub ρ σ' (Submodule.span R' (Set.range ℓ)) ∧
      IsAdapted ρH σ b₁ b₂ u ∧ (∀ i, u i ∈ HL) ∧ IsUnit A.det ∧
      ∀ i, HT.eigProj ρH σ (t i) = ∑ j, (A i j : Ω) • u j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.Frames.adapted_frames | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.Frames.adapted_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.Frames.adapted_frames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem isFlatOn_corr : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P Jd : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P Jd D) (Ψ : Type) (N : ℕ) (T : Ψ × Fin N → HermLine J), (∀ r, IsFlatOn R (T r)) → ∀ a, IsFlatOn R (corr T a) := by
  intro K _ J _ P Jd D R Ψ N T hT a x _
  cases a with
  | none =>
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, fun j => analyticOnNhd_const, fun y _ => ?_⟩
    simp [potOf, corr, Top.trivLine, LocPot.ofFun]
  | some r =>
    choose V hVo hxV G hG hE using fun k : Fin N => hT (r.1, k) x (Set.mem_univ x)
    refine ⟨R.U x ∩ ⋂ k, V k, (R.isOpen_U x).inter (isOpen_iInter_of_finite hVo),
      ⟨R.mem_U x, Set.mem_iInter.2 hxV⟩, fun y => -∑ k ∈ Finset.Iic r.2, G k y, fun j w hw => ?_, fun y hy => ?_⟩
    · have hs : ∀ k ∈ Finset.Iic r.2, AnalyticAt ℂ (G k ∘ (R.A.chart j).symm) w := fun k _ =>
        hG k j w ⟨hw.1, Set.mem_iInter.1 hw.2.2 k⟩
      exact (Finset.analyticAt_fun_sum _ hs).neg
    · have hm := (R.mem x y hy.1).1
      have e : (potOf R (corr T (some r))).φ x y = -∑ k ∈ Finset.Iic r.2, Real.log ((T (r.1, k)).h (R.lift x y)) :=
        log_stepLine (fun k => T (r.1, k)) r.2 hm
      have e' : ∀ k, Real.log ((T (r.1, k)).h (R.lift x y)) = (G k y).re := fun k => by
        simpa [potOf, LocPot.ofFun] using hE k y (Set.mem_iInter.1 hy.2 k)
      simp [e, e', LocPot.ofFun]

end GlobalTheory.CompanionTheory.Ar.Chg
end
