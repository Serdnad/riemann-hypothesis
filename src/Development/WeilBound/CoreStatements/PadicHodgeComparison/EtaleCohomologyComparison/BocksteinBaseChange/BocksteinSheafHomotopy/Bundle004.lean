module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bundle001
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Data.ZMod.Units

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace CyclicComplexMaps

def semiComp {T S R : Type} [CommRing T] [CommRing S] [CommRing R] {I : GlobalTheory.EtC.Cx T} {J : GlobalTheory.EtC.Cx S} {L : GlobalTheory.EtC.Cx R}
    (τ : SemiMap I J) (ρ : SemiMap J L) : SemiMap I L where
  app U s := (ρ.app U s).comp (τ.app U s)
  nat g s a := by simp only [AddMonoidHom.comp_apply]; rw [ρ.nat, τ.nat]
  comm U s t a := by simp only [AddMonoidHom.comp_apply]; rw [ρ.comm, τ.comm]

theorem pick_neg' {α : Type*} [Zero α] {P : α → Prop} (h : ¬ ∃ a, P a) : pick P = 0 := by
  unfold pick
  exact dif_neg h

theorem op_zero {S R : Type} [CommRing S] [CommRing R] {I : GlobalTheory.EtC.Cx S} {J : GlobalTheory.EtC.Cx R} (E : Spc) (n : ℤ)
    (x : CohomologyClass ((chains S).obj E) I n) : (0 : SemiMap I J).op.app E n x = 0 := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [SemiMap.op_spec (0 : SemiMap I J) E n α 0 (fun p s h U x => ?_)]
  · rfl
  · rw [Cocycle.coe_zero, CupSpec.ev_zero]
    rfl

end CyclicComplexMaps

theorem redSh (hF : FormalIn) : InRedSh := by
  intro Q q _ _ h i π hπ E n z
  by_cases hρ : ∃ ρ : SemiMap (res (ZMod q) (tw q i)) (res (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))),
      ∀ (U : Scheme.{0}) (a : Sec (tw q i) U), ρ.app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) =
        Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)))
          (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a)
  · have hρ' : ∀ (U : Scheme.{0}) (a : Sec (tw q i) U),
        (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) =
          Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)))
            (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a) := pick_spec hρ
    have hτ := hF.et.red Q q h i
    let σ := CyclicComplexMaps.semiComp (redMap Q q i) (restrMap (ZMod.castHom h (ZMod q)) (tw q i))
    have hg : resι (ZMod Q) (tw Q i) ≫ (CyclicComplexMaps.cxHom σ).f 0 =
        π ≫ resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) := by
      refine CyclicComplexMaps.tw_ext _ _ (fun U ζ => ?_)
      obtain ⟨ξ, hξ⟩ := CyclicComplexMaps.prim_pow h ζ
      change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) =
        Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))) (Sec.map π (twGen i ζ))
      rw [hτ U ζ ξ hξ, hπ U ζ ξ hξ]
      exact hρ' U (twGen i ξ)
    obtain ⟨α, rfl⟩ := z.mk_surjective
    obtain ⟨β, hβ⟩ := SemiMap.image_exists (redMap Q q i) E n α
    obtain ⟨γ, hγ⟩ := SemiMap.image_exists (restrMap (ZMod.castHom h (ZMod q)) (tw q i)) E n β
    change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n ((redMap Q q i).op.app E n (CohomologyClass.mk α)) = _
    rw [SemiMap.op_spec _ E n α β hβ, SemiMap.op_spec _ E n β γ hγ,
      ← CyclicComplexMaps.cpost_of_aug _ π (CyclicComplexMaps.cxHom σ) hg n (CohomologyClass.mk α), cpost_mk]
    congr 1
    apply Cocycle.ext
    apply CupSpec.ev_ext
    intro p s hs U x
    rw [hγ, hβ]
    exact (CyclicComplexMaps.ev_comp α.1 (CyclicComplexMaps.cxHom σ) p s hs U x).symm
  · have h0 : restrMap (ZMod.castHom h (ZMod q)) (tw q i) = 0 := CyclicComplexMaps.pick_neg' hρ
    obtain ⟨y, hy⟩ := (hF.a8 (ZMod Q) (ZMod q) (ZMod.castHom h (ZMod q)) E (tw q i) n).2
      (HK.post _ ((chains _).obj E) π n z)
    rw [← hy]
    change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _ = (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _
    rw [h0, CyclicComplexMaps.op_zero, CyclicComplexMaps.op_zero]

theorem bock_tw (hS : InTwSeq) : BocksteinInputFromFormal := fun hF => bock_of hS (redSh hF) hF

end CrystallineSemistableComparison
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSeq

open GlobalTheory.EtC

theorem pow_self {Q : ℕ} {A : Type} [CommRing A] (ζ : Prim Q A) : ζ.1 ^ Q = 1 := by
  obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one Q ℤ
  have := congrArg (Polynomial.aeval ζ.1) hc
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] at this
  exact this

def pw {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), isUnit_of_dvd_unit (Nat.cast_dvd_cast h) ζ.2.1, by
    obtain ⟨c, hc⟩ := CyclicComplexMaps.cyc_dvd Q q (NeZero.ne Q) h
    have := congrArg (Polynomial.aeval ζ.1) hc
    rw [Polynomial.aeval_comp, map_mul, ζ.2.2, zero_mul] at this
    simpa using this⟩

theorem pw_val {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : (pw h ζ).1 = ζ.1 ^ (Q / q) := rfl

theorem pw_map {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (ζ : Prim Q A) :
    (pw h ζ).map f = pw h (ζ.map f) := Subtype.ext (map_pow f _ _)

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  have h := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤))
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1))) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem redSheaf (hG : E.InGen) {Q q : ℕ} [NeZero Q] [NeZero q] (h : q ∣ Q) (i : ℤ) :
    ∃ π : tw Q i ⟶ (restr (ZMod.castHom h (ZMod q))).obj (tw q i), IsRedSh h i π ∧
      ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map π (twGen i ζ) =
        (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i (pw h ζ)) := by
  obtain ⟨π, hπ⟩ := KummerTwistLemmas.twLift i ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))
    (fun U ζ => (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i (pw h ζ)))
    (fun g ζ => by
      change Sec.res g (twGen i (pw h ζ)) = twGen i (pw h (ζ.map g.appTop.hom))
      rw [twGen_res, pw_map])
    (fun U ζ ξ a ha => by
      let a' : (ZMod q)ˣ := ZMod.unitsMap h a
      have hξ : (pw h ξ).1 = (pw h ζ).1 ^ (a' : ZMod q).val := by
        rw [pw_val, pw_val, ha, ← pow_mul, mul_comm, pow_mul]
        have h1 : ((pw h ζ).1) ^ q = 1 := pow_self (pw h ζ)
        rw [← pw_val h ζ, pow_eq_pow_mod _ h1, pow_eq_pow_mod ((a' : ZMod q).val) h1]
        have hv : (a' : ZMod q).val = (a : ZMod Q).val % q := by
          change (ZMod.castHom h (ZMod q) (a : ZMod Q)).val = _
          rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
        rw [hv, Nat.mod_mod]
      have := ((hG q i).2.2 U (pw h ζ) (pw h ξ) a' hξ)
      change twGen i (pw h ξ) = (ULift.up (ZMod.castHom h (ZMod q) ((a ^ i : (ZMod Q)ˣ) : ZMod Q)) : ULift.{1} (ZMod q)) • twGen i (pw h ζ)
      rw [this, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
      congr 1
      apply ULift.ext
      rw [ULift.down_natCast, ZMod.natCast_zmod_val]
      simp only [a', ZMod.unitsMap]
      rw [← map_zpow]
      rfl)
  refine ⟨π, fun U ζ ξ hξ => ?_, hπ⟩
  rw [hπ U ζ, show pw h ζ = ξ from Subtype.ext (show (pw h ζ).1 = ξ.1 from hξ.symm)]

end CrystallineSemistableComparison.TwSeq
end
end
