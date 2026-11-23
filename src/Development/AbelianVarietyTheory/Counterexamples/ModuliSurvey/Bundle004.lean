module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoHeckeQuotient
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
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
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ArcInTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem mem_of_pow_eq_int {F : Type} [Field F] (V : ValuationSubring F) (x : F) (n : ℕ) (hn : 0 < n) (m : ℤ)
    (h : x ^ n = m) : x ∈ V := by
  have hi : IsIntegral V x := by
    refine IsIntegral.of_pow hn ?_
    rw [h]
    simpa using isIntegral_algebraMap (R := V) (A := F) (x := (m : V))
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).1 hi
  exact hy ▸ y.2

theorem exists_values (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  refine ⟨⟨⟨_, GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField c⟩, mem_of_pow_eq_int _ _ 2 two_pos (-(H.d : ℤ)) ?_⟩,
    ⟨⟨_, GlobalTheory.HostModel.zeta_A_mem_coeff c⟩, mem_of_pow_eq_int _ _ l.A l.A_pos 1 ?_⟩, rfl, rfl⟩
  · apply Subtype.ext
    simpa using H.sqrt_neg_disc_sq
  · apply Subtype.ext
    simpa [zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one


end GlobalTheory.ArcInTest
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeKerModel

open GlobalTheory.HeckeTate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

theorem comp_act_natCast (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
  induction n with
  | zero =>
    have h := t.act.add 0 0
    rw [add_zero] at h
    have h1 : t.act.act 0 = 1 := by simpa using h
    simp [h1]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

theorem mem_tors_span (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ∈ t.tors T (Ideal.span {(n : 𝓞 E)}) ↔ x ^ n = 1 := by
  constructor
  · intro h
    rw [← comp_act_natCast]
    exact h _ (Ideal.mem_span_singleton_self _)
  · intro h a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    have := t.act.hom c
    rw [t.act.mul, ← Category.assoc, comp_act_natCast, h]
    simp

noncomputable def torsSub (t : SAB H S) (T : Over S) (n : ℕ) : Subgroup (T ⟶ t.G) :=
  { carrier := t.tors T (Ideal.span {(n : 𝓞 E)})
    one_mem' := (mem_tors_span t 1 n).2 (one_pow _)
    mul_mem' := fun {x y} hx hy a ha => by
      have := t.act.hom a
      rw [MonObj.mul_comp, hx a ha, hy a ha, _root_.one_mul]
    inv_mem' := fun {x} hx => (mem_tors_span t _ n).2 (by rw [inv_pow, (mem_tors_span t x n).1 hx, inv_one]) }

theorem heckeKer_zero {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {s : S ⟶ Sp B}
    (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (hx : x ≫ s = spMap β)
    (P : Ideal (𝓞 E)) (p : ℕ) (hp : 0 < p) :
    o.t.HeckeKer (Over.mk x) D P p 0 (torsSub o.t (Over.mk x) p) := by
  obtain ⟨-, I, -⟩ := o.geom k x β hx
  have hmem : ∀ z, z ∈ torsSub o.t (Over.mk x) p ↔ z ^ p = 1 := fun z => mem_tors_span o.t z p
  have hset : (torsSub o.t (Over.mk x) p : Set _) = o.t.tors (Over.mk x) (Ideal.span {(p : 𝓞 E)}) :=
    rfl
  have hq : 0 < p * p := Nat.mul_pos hp hp
  refine ⟨fun z hz a => ?_, fun J hJ z hz => ?_, fun z hz a ha => ?_, fun z hz w hw => ?_, ?_, ?_⟩
  · have := o.t.act.hom a
    rw [hmem] at hz ⊢
    rw [← comp_act_natCast, Category.assoc, ← o.t.act.mul, _root_.mul_comm, o.t.act.mul, ← Category.assoc,
      comp_act_natCast, hz]
    simp
  · rw [hset]
    exact fun a ha => hz a (Ideal.mul_le_left (I := J) (J := P) (by rw [hJ]; exact ha))
  · rw [hset] at hz
    exact hz a (Ideal.mul_le_left ha)
  · obtain ⟨a, rfl⟩ := (I.onto p hp z).1 ((hmem z).1 hz)
    obtain ⟨c, rfl⟩ := (I.onto p hp w).1 ((hmem w).1 hw)
    have h := I.isom (p * p) hq (p • a) (p • c)
    rw [ev_nsmul, ev_nsmul, I.tower p p hp hp, I.tower p p hp hp] at h
    have h2 : I.ζ (p * p) ^ D.EF (p • a) (p • c) = 1 := by
      rw [((I.ζ_prim _ hq).zpow_eq_one_iff_dvd _)]
      refine ⟨D.EF a c, ?_⟩
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      push_cast
      ring
    rw [h2] at h
    have h3 : unitOn (1 : kˣ) = 1 := map_one _
    rw [h3] at h
    rw [sq]
    exact_mod_cast h
  · have := D.fin
    have := D.proj
    have := datum_free_int D
    have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    rw [← datum_finrank_int, ← AddSubgroup.index_range_nsmul]
    have hker : (evHom I p).ker = (nsmulAddMonoidHom (α := D.La) p).range := by
      ext a
      exact (I.ker p hp a).trans ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
    rw [← hker, AddSubgroup.index_ker]
    refine Nat.card_congr ⟨fun z => ⟨Additive.ofMul z.1, ?_⟩, fun z => ⟨z.1.toMul, ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · obtain ⟨a, ha⟩ := (I.onto p hp z.1).1 ((hmem _).1 z.2)
      exact ⟨a, congrArg Additive.ofMul ha⟩
    · obtain ⟨a, ha⟩ := z.2
      exact (hmem _).2 ((I.onto p hp _).2 ⟨a, congrArg Additive.toMul ha⟩)
  · rw [hset, Set.inter_self, pow_zero, _root_.mul_one]

end GlobalTheory.HeckeKerModel
end
