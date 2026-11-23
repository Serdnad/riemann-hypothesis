module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ComapSurjOfLift
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
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
import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.SheafSectionLemmas

open GlobalTheory.EtC

variable {R : Type} [CommRing R]

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hSP⟩ := h
  exact ⟨S, hS, fun V g hg => hP V g (hSP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hSP⟩ := h
  refine ⟨Sieve.bind S.arrows (fun V g hg => (h' V g (hSP V g hg)).choose),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => (h' V g (hSP V g hg)).choose_spec.1), ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact (h' V g (hSP V g hg)).choose_spec.2 W k hk

theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

theorem isSheaf_types (G : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (G.obj ⋙ forget _) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 G.property)

theorem sec_eq_of_loc {F : Shv R} {U : Scheme.{0}} (x y : Sec F U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hSP⟩ := h
  exact ((isSheaf_types F) S hS).isSeparatedFor.ext fun _ g hg => hSP _ g hg

theorem sec_subsingleton_of_isEmpty (F : Shv R) (U : Scheme.{0}) [IsEmpty U] : Subsingleton (Sec F U) :=
  ⟨fun a b => ((isSheaf_types F).isSheafFor (⊥ : Presieve U)
    (by rw [Sieve.generate_bot]; exact Scheme.bot_mem_grothendieckTopology U)).isSeparatedFor.ext (fun _ _ h => h.elim)⟩

theorem epi_of_loc {F G : Shv R} (φ : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec G U), Loc U fun V g => ∃ x : Sec F V, Sec.map φ x = Sec.res g y) : Epi φ := by
  have : Sheaf.IsLocallySurjective φ := by
    constructor
    intro U y
    obtain ⟨S, hS, hSP⟩ := h U y
    refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) hS
    obtain ⟨x, hx⟩ := hSP V g hg
    exact ⟨x, hx⟩
  infer_instance

theorem sec_map_comp {X Y Z : Shv R} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem sec_map_injective_of_mono {X Y : Shv R} (f : X ⟶ Y) [Mono f] (U : Scheme.{0}) :
    Function.Injective (Sec.map f (U := U)) := by
  have h1 : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  have h2 : Mono (f.hom.app (op U)) := (NatTrans.mono_iff_mono_app f.hom).1 h1 (op U)
  exact (ModuleCat.mono_iff_injective _).1 h2

theorem epi_lift_of_loc {X Y Z : Shv R} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : ∀ (U : Scheme.{0}) (y : Sec Y U), Sec.map g y = 0 →
      Loc U fun V k => ∃ x : Sec X V, Sec.map f x = Sec.res k y) :
    Epi (kernel.lift g f w) := by
  apply epi_of_loc
  intro U y
  have hy : Sec.map g (Sec.map (kernel.ι g) y) = 0 := by
    rw [← sec_map_comp, kernel.condition]; rfl
  refine loc_mono (h U _ hy) fun V k ⟨x, hx⟩ => ⟨x, ?_⟩
  apply sec_map_injective_of_mono (kernel.ι g)
  rw [← sec_map_comp, kernel.lift_ι, hx, GlobalTheory.EtC.CupSpec.map_res]

theorem ker_comp_zero {X Y Z : Shv R} (f : X ⟶ Y) (g : X ⟶ Z)
    (h : ∀ (U : Scheme.{0}) (y : Sec X U), Sec.map f y = 0 → Sec.map g y = 0) : kernel.ι f ≫ g = 0 := by
  apply Sheaf.hom_ext
  ext U y
  refine (h U.unop (Sec.map (kernel.ι f) y) ?_).trans rfl
  rw [← sec_map_comp, kernel.condition]; rfl

end CrystallineSemistableComparison.SheafSectionLemmas
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial

namespace CrystallineSemistableComparison.KummerTwistLemmas

open GlobalTheory.EtC

theorem cyc_pow (p b : ℕ) (hp : p.Prime) (hb : 0 < b) :
    ∀ a : ℕ, expand ℤ (p ^ a) (cyclotomic (p ^ b) ℤ) = cyclotomic (p ^ (a + b)) ℤ
  | 0 => by simp
  | a + 1 => by
    rw [pow_succ', expand_mul, cyc_pow p b hp hb a,
      cyclotomic_expand_eq_cyclotomic hp (dvd_pow_self p (by omega : a + b ≠ 0))]
    congr 1
    rw [← pow_succ]
    congr 1
    omega

theorem rootLoc (p a b : ℕ) [Fact p.Prime] (hb : 0 < b) (U : Scheme.{0}) (ξ : Prim (p ^ b) Γ(U, ⊤)) :
    Loc U fun V g => ∃ ζ : Prim (p ^ (a + b)) Γ(V, ⊤), ζ.1 ^ (p ^ a) = g.appTop.hom ξ.1 := by
  have hp : p.Prime := Fact.out
  have hpU : IsUnit (p : Γ(U, ⊤)) := by
    have h := ξ.2.1
    rw [Nat.cast_pow] at h
    exact (isUnit_pow_iff hb.ne').1 h
  have hξ1 : ξ.1 ^ (p ^ b) = 1 := by
    obtain ⟨h, hh⟩ := cyclotomic.dvd_X_pow_sub_one (p ^ b) ℤ
    have := congrArg (aeval ξ.1) hh
    rw [map_mul, ξ.2.2, zero_mul, map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at this
    exact this
  have hξu : IsUnit ξ.1 := by
    refine isUnit_iff_exists_inv.2 ⟨ξ.1 ^ (p ^ b - 1), ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.ne_zero)), hξ1]
  obtain ⟨S, hS, hP⟩ := kumLoc U (p ^ a) hξu.unit (by rw [Nat.cast_pow]; exact hpU.pow _)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨v, hv⟩ := hP V g hg
  rw [IsUnit.unit_spec] at hv
  have hpV : IsUnit (p : Γ(V, ⊤)) := by simpa using hpU.map g.appTop.hom
  refine ⟨⟨v, by rw [Nat.cast_pow]; exact hpV.pow _, ?_⟩, hv⟩
  rw [← cyc_pow p b hp hb a, expand_aeval, hv]
  exact (Prim.map g.appTop.hom ξ).2.2

end CrystallineSemistableComparison.KummerTwistLemmas
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSec

open GlobalTheory.EtC

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  change (F.obj.map (k ≫ g).op).hom y = (F.obj.map k.op).hom ((F.obj.map g.op).hom y)
  rw [op_comp, Functor.map_comp]
  rfl

theorem loc_bind' {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hT' using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => h' V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hT' V g hg W k hk

theorem tw_loc (hG : E.InGen) (Q : ℕ) [NeZero Q] (i : ℤ) (U : Scheme.{0}) (y : Sec (tw Q i) U) :
    Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ := by
  have hsurj : Presheaf.imageSieve (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF Q i)) y ∈ Scheme.etaleTopology U :=
    Presheaf.imageSieve_mem Scheme.etaleTopology _ (U := op U) y
  refine loc_bind' ⟨_, hsurj, fun V g hg => hg⟩ ?_
  rintro V g ⟨t, ht⟩
  by_cases hP : Nonempty (Prim Q Γ(V, ⊤))
  · obtain ⟨ζ₀⟩ := hP
    obtain ⟨S, hS, hS'⟩ := (hG Q i).1 V ζ₀ (Sec.res g y)
    refine ⟨S, hS, fun W k hk => Or.inr ?_⟩
    obtain ⟨c, hc⟩ := hS' W k hk
    exact ⟨ζ₀.map k.appTop.hom, c, (res_comp k g y).trans hc⟩
  · have : IsEmpty (Prim Q Γ(V, ⊤)) := not_nonempty_iff.mp hP
    have ht0 : t = 0 := by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel Q i Γ(V, ⊤))
        (show (Prim Q Γ(V, ⊤) →₀ ULift.{1} (ZMod Q)) ⧸ twRel Q i Γ(V, ⊤) from t)
      have hf : f = 0 := Finsupp.ext fun a => (IsEmpty.false a).elim
      rw [hf]
      exact Submodule.Quotient.mk_zero _
    have hy : Sec.res g y = 0 := by
      refine ht.symm.trans ?_
      rw [ht0]
      exact map_zero _
    refine ⟨⊤, Scheme.etaleTopology.top_mem V, fun W k _ => Or.inl ?_⟩
    rw [res_comp, hy]
    exact map_zero _

end CrystallineSemistableComparison.TwSec
end
end
