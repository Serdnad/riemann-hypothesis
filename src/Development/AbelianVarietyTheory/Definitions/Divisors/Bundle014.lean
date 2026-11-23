module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.InhTate

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UPel.Sm.Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

section Univ
variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : Datum F} {p N : ℕ}

end Univ

section KS
variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]
  {ρ : O →+* Module.End k H} {φ : LinearMap.BilinForm k H} {Fil Z : Submodule k H}

def ksSub (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) :
    Submodule k (H →ₗ[k] H) where
  carrier := {f | IsKS ρ φ Fil Z f}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' {f g} hf hg := ⟨fun a x hx => by
      convert add_mem (hf.1 a x hx) (hg.1 a x hx) using 1
      simp only [LinearMap.add_apply, map_add (f := _)]; abel,
    fun x hx => add_mem (hf.2.1 x hx) (hg.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      have h2 := hg.2.2 x hx y hy
      simp only [LinearMap.add_apply, map_add (f := _)]
      linear_combination h1 + h2⟩
  smul_mem' c f hf := ⟨fun a x hx => by
      convert Fil.smul_mem c (hf.1 a x hx) using 1
      simp only [LinearMap.smul_apply, map_smul, smul_sub],
    fun x hx => Fil.smul_mem c (hf.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
      linear_combination c * h1⟩

def cls (Fil : Submodule k H) : (H →ₗ[k] H) →ₗ[k] (Fil →ₗ[k] H ⧸ Fil) where
  toFun f := Fil.mkQ ∘ₗ f ∘ₗ Fil.subtype
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

theorem cls_eq_iff (f g : H →ₗ[k] H) : cls Fil f = cls Fil g ↔ ∀ x ∈ Fil, f x - g x ∈ Fil := by
  simp [cls, LinearMap.ext_iff, Submodule.Quotient.eq]

theorem KSDim.rank_eq {d : ℕ} (h : KSDim ρ φ Fil Z d) :
    Module.rank k ((ksSub ρ φ Fil Z).map (cls Fil)) = d := by
  obtain ⟨f, hf, hu⟩ := h
  have key : ∀ (g : H →ₗ[k] H) (c : Fin d → k), (∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil) ↔
      cls Fil g = ∑ i, c i • cls Fil (f i) := fun g c => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum, cls_eq_iff, LinearMap.sum_apply, LinearMap.smul_apply]
  have li : LinearIndependent k fun i => cls Fil (f i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨c₀, -, h₀⟩ := hu 0 (ksSub ρ φ Fil Z).zero_mem
    have := (h₀ c ((key 0 c).2 (by rw [hc, map_zero]))).trans (h₀ 0 ((key 0 0).2 (by simp))).symm
    exact congrFun this
  have : (ksSub ρ φ Fil Z).map (cls Fil) = Submodule.span k (Set.range fun i => cls Fil (f i)) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, hc, -⟩ := hu g hg
      rw [(key g c).1 hc]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨f i, hf i, rfl⟩
  rw [this, rank_span li, ← Cardinal.lift_inj.{_, 0}, Cardinal.mk_range_eq_of_injective li.injective]
  simp

theorem KSDim.unique {d e : ℕ} (h : KSDim ρ φ Fil Z d) (h' : KSDim ρ φ Fil Z e) : d = e := by
  exact_mod_cast (KSDim.rank_eq h).symm.trans (KSDim.rank_eq h')

end KS

section Examples
variable (k : Type) [Field k]

end Examples

end GlobalTheory.UPel.Sm.Model
end
end

section

noncomputable section
open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal.ObjModel
variable {E : Type} [Field E] [NumberField E]

theorem coord_ne (y : (Af E)ˣ) (v : HeightOneSpectrum (𝓞 E)) : Valued.v ((y : Af E) v) ≠ 0 := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).1 v
  simpa using this

theorem modF_finite (y : (Af E)ˣ) : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v ((y : Af E) v)))).Finite := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).2
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv h1 => hv ?_
  simp [h1]

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  positivity

theorem modF_mul (y y' : (Af E)ˣ) : modF (y * y') = modF y * modF y' := by
  unfold modF
  rw [← finprod_mul_distrib (modF_finite y) (modF_finite y')]
  refine finprod_congr fun v => ?_
  have : ((y * y' : (Af E)ˣ) : Af E) v = (y : Af E) v * (y' : Af E) v := rfl
  rw [this, map_mul, WithZero.log_mul (coord_ne y v) (coord_ne y' v), zpow_add₀ (absNorm_pos v).ne']

theorem modF_pos (y : (Af E)ˣ) : 0 < modF y :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (absNorm_pos v) _

theorem modF_princ (k : Eˣ) :
    modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|((Algebra.norm ℚ (k : E) : ℚ) : ℝ)|)⁻¹ := by
  apply _root_.GlobalTheory.CMVal.IdeleModule.modF_princ <;> assumption

theorem hatO_integral {c : Ideal (OF E)} {y : Af E} (hy : y ∈ hatO c) (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v (y v) ≤ 1 := by
  have hc : IsClosed {y : Af E | y v ∈ v.adicCompletionIntegers E} :=
    (Valued.isClosed_valuationSubring (v.adicCompletion E)).preimage (RestrictedProduct.continuous_eval v)
  have : y ∈ {y : Af E | y v ∈ v.adicCompletionIntegers E} := by
    refine closure_minimal ?_ hc hy
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
    have : algebraMap (OF E) E a + algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by
      rw [map_add (f := _)]; rfl
    rw [this]
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one _)
  exact this

theorem modF_unit {c : Ideal (OF E)} {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) : modF u = 1 := by
  unfold modF
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  have h1 : Valued.v ((u : Af E) v) ≤ 1 := hatO_integral hu.1 v
  have h2 : Valued.v ((↑u⁻¹ : Af E) v) ≤ 1 := hatO_integral hu.2 v
  have h3 : Valued.v ((u : Af E) v) * Valued.v ((↑u⁻¹ : Af E) v) = 1 := by
    rw [← map_mul]
    have : (u : Af E) v * (↑u⁻¹ : Af E) v = 1 := (coord v u).val_inv
    rw [this, map_one]
  have h4 : Valued.v ((u : Af E) v) = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ Valued.v ((u : Af E) v) * 1 := by gcongr
      _ = _ := mul_one _
  simp [h4]

variable {I : Type}

theorem prod_normSq [Fintype I] [_root_.NumberField.IsTotallyComplex E] {φ : I → E →+* ℂ}
    (h : IsCMType φ) (x : E) :
    ∏ i, ‖φ i x‖ ^ 2 = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h1 := InfinitePlace.prod_eq_abs_norm x
  push_cast at h1
  rw [← h1]
  refine Fintype.prod_bijective (fun i => InfinitePlace.mk (φ i)) ⟨fun i j hij => ?_, fun w => ?_⟩ _ _ fun i => ?_
  · obtain ⟨l, -, hl⟩ := h (φ i)
    have h2 := InfinitePlace.mk_eq_iff.1 hij.symm
    rw [hl i (Or.inl rfl), hl j (h2.imp Eq.symm Eq.symm)]
  · obtain ⟨l, hl, -⟩ := h w.embedding
    refine ⟨l, ?_⟩
    rw [← w.mk_embedding]
    exact InfinitePlace.mk_eq_iff.2 (hl.imp Eq.symm Eq.symm)
  · rw [IsTotallyComplex.mult_eq, InfinitePlace.apply]

theorem prod_cpow (t : Finset I) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i) (z : ℂ) :
    ∏ i ∈ t, ((r i : ℝ) : ℂ) ^ z = ((∏ i ∈ t, r i : ℝ) : ℂ) ^ z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hr a) (Finset.prod_nonneg fun i _ => hr i)]

end GlobalTheory.CMVal.ObjModel
end
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal.Model

section General

variable {E : Type} [Field E] [NumberField E]

theorem IsCMType.bijective {I : Type} {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  refine ⟨fun i j hij => ?_, fun w => ?_⟩
  · obtain ⟨k, -, hk⟩ := h (φ j)
    have h1 : j = k := hk j (Or.inl rfl)
    have h2 : i = k := hk i (by
      rcases InfinitePlace.mk_eq_iff.1 hij with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm)
    rw [h1, h2]
  · obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    rcases hi with e | e
    · simp only [← e, InfinitePlace.mk_embedding]
    · have := congrArg InfinitePlace.mk e
      rw [InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq] at this
      exact this.symm

end General

section Integrality

end Integrality

section Symmetry

variable {E : Type} [Field E] [NumberField E]

end Symmetry

section Twist

variable {E : Type} [Field E] [NumberField E]

end Twist

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end CM

section Cyclotomic


end Cyclotomic

end GlobalTheory.CMVal.Model
end
end

section

noncomputable section

open NumberField Matrix Polynomial

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.skewFun (x y : D.La) : Module.Dual ℚ D.F :=
  (integralBasis D.F).constr ℚ fun k =>
    ((D.EF (algebraMap (𝓞 D.F) D.O (RingOfIntegers.basis D.F k) • x) y : ℤ) : ℚ)

theorem Datum.EF_swap (x y : D.La) : D.EF y x = - D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt, zero_add, add_zero] at h
  linarith

def Datum.Kq : Subfield D.F := (IntermediateField.adjoin ℚ {(D.ω : D.F)}).toSubfield

section Places

variable {F : Type} [Field F] [NumberField F] (Kq : Subfield F) (u : Kq →+* ℚ_[p])

end Places

section Examples

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

end Examples

end GlobalTheory.UPel.HT
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

def Datum.CompactB (D : Datum p) : Prop := 2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)

end GlobalTheory.UPel.HT
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

structure Pre (b : Base D R) (s : S ⟶ Sp R) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  act : OActN D.O A
  P : LB (G2 A).left
  isLB : P.IsLB
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
  ample : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)
  kerP : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A),
    (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1
  rosati : ∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)

attribute [instance] Pre.grp Pre.comm

end GlobalTheory.UPel.HT
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

structure RepFam (b : Base D R) (N : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  univ : Obj b N s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s'), ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o univ f)

def Model.toRepFam {b : Base D R} {N : ℕ} (M : Model b N) : RepFam b N := ⟨M.X, M.s, M.univ, M.rep⟩

end GlobalTheory.UPel.HT
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.EndModel
open ReciprocityTheory.ChartRestriction.G.Out.InhTate

theorem endData_of_oAct {R : Type} [CommRing R] [IsDomain R] (O : Type) [Ring O] [StarRing O] (D : DegPre R)
    [Module O D.X] (io : D.OAct O) (a : O) :
    EndData D (io.onB.act a) (io.onB.act (star a)) (DistribSMul.toAddMonoidHom D.X a)
      (DistribSMul.toAddMonoidHom D.X (star a)) :=
  ⟨io.onB.hom a, io.onB.hom (star a), io.onB.rosati a, io.c_lin a, io.c_lin (star a), io.tau_bal a⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem thickMap_map {G H : Over (Sp R)} (b : G ⟶ H) (e : ℕ) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map b).left =
      ((Over.pullback (thick R I e)).map b).left ≫ thickMap R I e H := by
  apply pullback.hom_ext
  · simp only [thickMap, pullback.map, Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
    rfl
  · simp only [thickMap, pullback.map, Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    simp

end GlobalTheory.Mum.EndModel
end
end
