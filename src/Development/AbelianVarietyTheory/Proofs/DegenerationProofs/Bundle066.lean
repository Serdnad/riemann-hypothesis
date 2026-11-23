module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoOnG
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle061
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
import Mathlib.RingTheory.PiTensorProduct
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.TestBasis

open FreeNear

theorem exists_eStd_eq_linear (g n : ℕ) (f : (Fin g ⊕ Fin g → ZMod n) →ₗ[ZMod n] ZMod n) :
    ∃ b, ∀ y, eStd g n b y = f y := by
  refine ⟨Sum.elim (fun i => f (Pi.single (.inr i) 1)) (fun i => -f (Pi.single (.inl i) 1)),
    fun y => ?_⟩

  conv_rhs => rw [← Finset.univ_sum_single y, map_sum, Fintype.sum_sum_type,
  ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j, f (Pi.single j (y j)) = y j * f (Pi.single j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [h, h]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem perp_perp (H : AddSubgroup S.Gam) : S.perp (S.perp H) = H := by
  refine le_antisymm (fun x hx => ?_) fun x hx y hy => ?_
  · by_contra hxH
    let H' : Submodule (ZMod (S.r * S.N)) S.Gam := AddSubgroup.toZModSubmodule _ H
    obtain ⟨f, hf⟩ := ZModPerp.exists_dual_ne_zero (n := S.r * S.N) (q := H'.mkQ x)
      (fun h0 => hxH ((Submodule.Quotient.mk_eq_zero H').mp h0))
    obtain ⟨b, hb⟩ := exists_eStd_eq_linear _ _ (f ∘ₗ H'.mkQ)
    have hb' : b ∈ S.perp H := fun y hy => by
      rw [hb, LinearMap.comp_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero H').mpr hy, map_zero]
    have h1 : eStd S.g _ x b = 0 := hx b hb'
    rw [Weights.eStd_swap, neg_eq_zero, hb] at h1
    exact hf h1
  · rw [Weights.eStd_swap, hy x hx, neg_zero]

variable {S} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)

theorem exists_nsmul_of_wt_eq_zero [ArithBase o Ω] (α : τ.X) (h : τ.wt α = 0) : ∃ v, α = S.N • v := by
  choose w hw using fun x => QuotientAddGroup.mk_surjective (τ.yy x)
  have h1 := ((test_weights o Ω S p y₀ τ).2 _ τ.isoFree le_rfl w (fun x => (hw x).symm) τ.yy.ker
    (by rw [perp_perp, AddSubgroup.closure_eq]) α).1 (fun t h₂ _ => by rw [h]; rfl)
  have h2 : AddSubgroup.closure (w '' τ.yy.ker ∪ Set.range fun v₀ : τ.X => S.N • v₀) ≤
      (nsmulAddMonoidHom S.N : τ.X →+ τ.X).range := by
    rw [AddSubgroup.closure_le]
    rintro _ (⟨x, hx, rfl⟩ | ⟨v, rfl⟩)
    · have h3 := hw x
      rw [AddMonoidHom.mem_ker.1 hx, QuotientAddGroup.eq_zero_iff] at h3
      obtain ⟨u, hu⟩ := h3
      exact ⟨S.r • u, by rw [← hu]; exact (mul_nsmul u S.r S.N).symm⟩
    · exact ⟨v, rfl⟩
  obtain ⟨v, hv⟩ := h2 h1
  exact ⟨v, hv.symm⟩

theorem q_le_of_wt_eq [ArithBase o Ω] {α β : τ.X} (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀))
    (h : τ.wt β = τ.wt α) : τ.q α ≤ τ.q β := by
  obtain ⟨v, hv⟩ := exists_nsmul_of_wt_eq_zero τ (β - α) (by rw [map_sub, h, sub_self])
  have := hα v
  rwa [← hv, add_sub_cancel] at this

theorem exists_norm_eq_exp {α : τ.X} (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) :
    ∃ l : PadicAlgCl p, ‖l‖ = Real.exp (τ.q α / S.N) := by
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  obtain ⟨x, hx⟩ := τ.δ_max.1
  refine ⟨y₀ ⟨S.th x, S.th_mem x⟩ / y₀ ⟨_, hk⟩, ?_⟩
  have hx' : ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = τ.δ := hx
  rw [norm_div, hx', h, Real.exp_neg]
  have := τ.δ_pos.ne'
  have := (Real.exp_pos (τ.q α / S.N)).ne'
  field_simp

theorem exists_proj_ne_zero {α : τ.X} (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) :
    ∃ j i, y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i)) ≠ 0 := by
  by_contra! h0
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  have := Fintype.ofFinite (S.perp τ.yy.ker)
  have h1 : (⟨_, hk⟩ : S.R) = ∑ t : S.perp τ.yy.ker, algebraMap o S.R (S.ζ ^ (k.2 t).val) *
      ∑ j, algebraMap o S.R (S.proj _ (τ.wt α) j k.1) * ⟨S.ev t j, S.ev_mem t j⟩ := by
    apply Subtype.ext
    simp only [ThetaSys.FF, finsum_eq_sum_of_fintype, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    rfl
  rw [h1] at h

  simp only [map_sum, map_mul, h0, zero_mul, Finset.sum_const_zero, mul_zero, norm_zero] at h
  exact (mul_pos τ.δ_pos (Real.exp_pos _)).ne h

end GlobalTheory.ZH.TestBasis

namespace GlobalTheory.ZH


open FreeNear TestBasis in
theorem exists_adapted_basis_testLattice : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (B : Matrix S.J S.J (PadicAlgCl p)) (l : S.J → PadicAlgCl p) (α : S.J → τ.X), (∀ i j, ‖B i j‖ ≤ 1) ∧ ‖B.det‖ = 1 ∧ (∀ i v₀, τ.q (α i) ≤ τ.q (α i + S.N • v₀)) ∧ (∀ i, ‖l i‖ = Real.exp (τ.q (α i) / S.N)) ∧ (∀ c, ∃ i, τ.wt (α i) = c) ∧ (∀ i, ((S.proj _ (τ.wt (α i))).map fun a => y₀ (algebraMap o S.R a)).mulVec (B i) = B i) ∧ τ.E = Submodule.span (OO p) (Set.range fun i j => l i * B i j) := by
  intro o Ω _ _ _ hA S p _ y₀ τ hint
  have : IsDomain o := hA.inj.isDomain
  have := finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, hsum⟩ := proj_orthogonal S _ τ.isoFree
  let φ : o →+* OO p := (y₀.comp (algebraMap o S.R)).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hint a)
  obtain ⟨κ, col, hdet, hspan⟩ := exists_basis_adapted_to_idempotents (OO p) S.J
    (S.perp τ.yy.ker →+ ZMod S.N) (fun c => φ.mapMatrix (S.proj _ c))
    (fun c c' => by
      rw [← map_mul, hmul]
      split_ifs <;> simp)
    (by rw [← map_sum, hsum, map_one])
  choose a ha hwa using (test_weights o Ω S p y₀ τ).1
  choose f hf using fun c => exists_norm_eq_exp τ (ha c)
  refine ⟨Matrix.of fun i j => y₀ (algebraMap o S.R (S.proj _ (κ i) j (col i))), fun i => f (κ i),
    fun i => a (κ i), fun i j => hint _, ?_, fun i => ha _, fun i => hf _, fun c => ?_, fun i => ?_, ?_⟩
  · have h1 : (((Matrix.of fun i j => φ.mapMatrix (S.proj _ (κ i)) j (col i)).det : OO p) : PadicAlgCl p) =
        (Matrix.of fun i j => y₀ (algebraMap o S.R (S.proj _ (κ i) j (col i)))).det :=
      RingHom.map_det (OO p).subtype _
    rw [← h1]
    exact le_antisymm ((mem_OO_iff _).1 (Subtype.prop _))
      (not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hdet)
  · by_contra! h
    obtain ⟨j, i, hji⟩ := exists_proj_ne_zero τ (ha c)
    rw [hwa] at hji
    have h1 := (hspan c).le (Submodule.subset_span ⟨i, rfl⟩)
    have h2 : {v : S.J → OO p | ∃ i, κ i = c ∧ v = fun j => φ.mapMatrix (S.proj _ c) j (col i)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ ⟨i, hi, _⟩ => h i ((hwa _).trans hi)
    rw [h2, Submodule.span_empty, Submodule.mem_bot] at h1
    exact hji (congrArg Subtype.val (congrFun h1 j))
  · rw [hwa]
    funext j
    have h1 := congrArg (fun a => y₀ (algebraMap o S.R a)) (congrFun (congrFun (hmul (κ i) (κ i)) j) (col i))

    simp only [if_true, Matrix.mul_apply, map_sum, map_mul] at h1
    exact h1
  · refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨α, l, i, hα, hl, rfl⟩
      generalize hc : τ.wt α = c
      have h1 : ∀ w ∈ Submodule.span (OO p) {v : S.J → OO p | ∃ i, κ i = c ∧
          v = fun j => φ.mapMatrix (S.proj _ c) j (col i)},
          (fun j => f c * (w j : PadicAlgCl p)) ∈ Submodule.span (OO p) (Set.range fun i j =>
            f (κ i) * y₀ (algebraMap o S.R (S.proj _ (κ i) j (col i)))) := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem _ h' =>
          obtain ⟨i', rfl, rfl⟩ := h'
          exact Submodule.subset_span ⟨i', rfl⟩
        | zero =>
          have : (fun j => f c * (((0 : S.J → OO p) j : OO p) : PadicAlgCl p)) = 0 := funext fun j => by simp
          rw [this]
          exact Submodule.zero_mem _
        | add a a' _ _ ha ha' =>
          convert Submodule.add_mem _ ha ha' using 1
          funext j
          simp [mul_add]
        | smul s a _ ha =>
          convert Submodule.smul_mem _ s ha using 1
          funext j
          change f c * ((s : PadicAlgCl p) * a j) = (s : PadicAlgCl p) * (f c * a j)
          ring
      have h2 := h1 _ ((hspan c).le (Submodule.subset_span ⟨i, rfl⟩))
      have hpos : 0 < ‖f c‖ := hf c ▸ Real.exp_pos _
      have h0 : f c ≠ 0 := norm_pos_iff.1 hpos
      have hq : l / f c ∈ OO p := by
        rw [mem_OO_iff, norm_div, div_le_one hpos, hf]
        refine hl.trans (Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)))
        exact q_le_of_wt_eq τ hα ((hwa c).trans hc.symm)
      have h3 : (fun j => l * y₀ (algebraMap o S.R (S.proj _ c j i))) =
          (⟨_, hq⟩ : OO p) • fun j => f c * y₀ (algebraMap o S.R (S.proj _ c j i)) := by
        funext j
        change _ = l / f c * (f c * y₀ (algebraMap o S.R (S.proj _ c j i)))
        rw [← _root_.mul_assoc, div_mul_cancel₀ _ h0]
      rw [h3]
      exact Submodule.smul_mem _ _ h2
    · rintro _ ⟨i, rfl⟩
      exact ⟨a (κ i), f (κ i), col i, ha _, (hf _).le, by rw [hwa]; rfl⟩

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH

theorem labelled_torsion_pull {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G']
    {f : B' ⟶ B} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over B') {E : Over B}
    (U : Over.mk (T.hom ≫ f) ⟶ E) {Γ : Type} [Add Γ] (pt : Γ → (E ⟶ G)) (m : ℕ)
    (hadd : ∀ a b, pt (a + b) = pt a * pt b) (htors : ∀ a, pt a ^ m = 1)
    (hbij : ∀ z : Over.mk (T.hom ≫ f) ⟶ G, z ^ m = 1 → ∃! a, U ≫ pt a = z) :
    ∃ x : Γ → (T ⟶ G'), (∀ a, (x a).left ≫ φ = U.left ≫ (pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧
      Function.Injective x ∧ ∀ z : T ⟶ G', z ^ m = 1 → ∃ a, z = x a := by
  have hinj : Function.Injective (pushHom h T) := fun x y e => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) e
    · rw [Over.w, Over.w]
  have hsurj : Function.Surjective (pushHom h T) := fun z =>
    ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  choose x hx using fun a => hsurj (U ≫ pt a)
  refine ⟨x, fun a => congrArg (fun z => z.left) (hx a), fun a b => hinj ?_, fun a b e => ?_, fun z hz => ?_⟩
  · rw [map_mul, hx, hx, hx, hadd, MonObj.comp_mul]
  · have ht : (U ≫ pt a) ^ m = 1 := by
      have := map_pow (preHom U) (pt a) m
      rw [htors, map_one] at this
      exact this.symm
    exact (hbij _ ht).unique rfl (by rw [← hx, ← hx, e])
  · obtain ⟨a, ha, -⟩ := hbij (pushHom h T z) (by rw [← map_pow, hz, map_one])
    exact ⟨a, hinj (by rw [hx, ha])⟩

theorem utest_torsion_points : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧ ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  intro o Ω _ _ _ S ρ p _ y₀ u
  have e : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap u.fac)
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  obtain ⟨x, h₁, h₂⟩ := labelled_torsion_pull u.cart (TFK (R := u.V) (PadicAlgCl p))
    (E := baseOver (Sp S.R))
    (Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK :) (by simp)) ρ.pt (S.r * S.N) ρ.pt_add
    (fun a => (ρ.fr_tors a).1) (fun z hz => ρ.pt_bij (PadicAlgCl p) _ z hz)
  exact ⟨x, fun a => (h₁ a).trans (by rw [← e]; rfl), h₂⟩

end GlobalTheory.ZH
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ZH

theorem exists_test_match : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ x, y₀ ⟨S.th x, S.th_mem x⟩ ≠ 0 → ∃ w : u.D.toPre.X, l.yy x = QuotientAddGroup.mk w ∧ ‖y₀ ⟨S.th x, S.th_mem x⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) → (0 < S.delta y₀ ∧ AddSubgroup.closure {x | ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = S.delta y₀} = l.yy.ker) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∀ h ∈ l.yy.ker, ∀ i, ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt α) j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q α / S.N))) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∃ (k : _) (hk : S.FF _ (l.wt α) k ∈ S.R), ‖y₀ ⟨S.FF _ (l.wt α) k, hk⟩‖ = S.delta y₀ * Real.exp (-(l.q α / S.N))) → (∀ h ∈ l.yy.ker, ∃ i, ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt 0) j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ = S.delta y₀) → ∃ τ : S.Test p y₀, l.Match τ := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u l h1 h2 h3 h4 h5
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have hmax : IsGreatest (Set.range fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (S.delta y₀) := by
    obtain ⟨x, hx⟩ := exists_eq_ciSup_of_finite (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖)
    refine ⟨⟨x, hx⟩, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact le_ciSup (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (Set.finite_range _).bddAbove z
  let τ : S.Test p y₀ :=
    { X := u.D.toPre.X
      q := l.q
      pos := l.pos
      yy := l.yy
      yy_onto := l.yy_onto
      isoFree := l.isoFree
      wt := l.wt
      wt_eq := l.wt_eq
      δ := S.delta y₀
      δ_max := hmax
      δ_pos := h2.1
      supp := h2.2
      tx := h1
      le := h3
      eq := h4
      unit0 := h5 }
  exact ⟨τ, AddEquiv.refl _, fun _ => rfl, fun _ _ => Iff.rfl⟩
end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

def Extends (u : ρ.UTest p y₀) (a : S.Gam) (h : baseOver (Sp u.V) ⟶ u.G) : Prop :=
  ∃ x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V), x ≫ pullback.fst _ _ = jK u.V ≫ h.left ∧
    x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left

theorem integral_iff (u : ρ.UTest p y₀) (a : S.Gam) : u.Integral a ↔ ∃ h, Extends u a h :=
  ⟨fun ⟨h, x, e, H⟩ => ⟨Over.homMk h e, x, H⟩, fun ⟨h, x, H⟩ => ⟨h.left, x, Over.w h, H⟩⟩

end GlobalTheory.UnitTheta
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem torsion_descends {B V K L : Scheme.{0}} {A : Over B} {G : Over V} {H : Over K} [GrpObj A] [GrpObj G] [GrpObj H]
    {f : K ⟶ B} {j : K ⟶ V} {ψ : H.left ⟶ A.left} {π : H.left ⟶ G.left}
    (hA : IsGrpPullback H A f ψ) (hG : IsGrpPullback H G j π) (i : L ⟶ K) (n : ℕ)
    (hs : ∀ z : Over.mk (i ≫ f) ⟶ A, z ^ n = 1 → ∃ s : B ⟶ A.left, s ≫ A.hom = 𝟙 B ∧ (i ≫ f) ≫ s = z.left)
    (y : Over.mk (i ≫ j) ⟶ G) (hy : y ^ n = 1) : ∃ x : K ⟶ G.left, i ≫ x = y.left := by
  let y' : Over.mk i ⟶ H := Over.homMk (hG.1.lift y.left i (Over.w y)) (hG.1.lift_snd _ _ _)
  have e₁ : y'.left ≫ π = y.left := hG.1.lift_fst _ _ _
  have e₂ : pushHom hG (Over.mk i) y' = y := Over.OverMorphism.ext e₁
  have inj : Function.Injective (pushHom hG (Over.mk i)) := fun a b h => by
    apply Over.OverMorphism.ext
    apply hG.1.hom_ext
    · exact congrArg (fun z => z.left) h
    · rw [Over.w, Over.w]
  have e₃ : y' ^ n = 1 := inj (by rw [map_pow, e₂, map_one]; exact hy)
  obtain ⟨s, hs₁, hs₂⟩ := hs (pushHom hA (Over.mk i) y') (by rw [← map_pow, e₃, map_one])
  have w : (f ≫ s) ≫ A.hom = 𝟙 K ≫ f := by rw [Category.assoc, hs₁, Category.comp_id, Category.id_comp]
  refine ⟨hA.1.lift (f ≫ s) (𝟙 K) w ≫ π, ?_⟩
  rw [← e₁, ← Category.assoc]
  congr 1
  apply hA.1.hom_ext
  · rw [Category.assoc, hA.1.lift_fst, ← Category.assoc, hs₂]
    rfl
  · rw [Category.assoc, hA.1.lift_snd, Category.comp_id]
    exact (Over.w y').symm

theorem torsion_rational : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (m : ℕ), m ∣ S.r * S.N → ∀ y : Over.mk (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V) ⟶ u.G, y ^ m = 1 → ∃ x : Sp (FractionRing u.V) ⟶ u.G.left, spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ x = y.left := by
  intro o Ω _ _ _ S ρ p _ y₀ u m hm y hy
  have := u.U.gen_hom
  have hA := ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  refine torsion_descends hA (isGrpPullback_pullback u.G (jK u.V)) _ (S.r * S.N) (fun z hz => ?_) y ?_
  · obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) _ z hz
    exact ⟨(ρ.pt a).left, Over.w (ρ.pt a), congrArg (fun t => t.left) ha⟩
  · obtain ⟨c, hc⟩ := hm
    rw [hc, pow_mul, hy, one_pow]

end GlobalTheory.UnitTheta
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH

theorem weilIs_uTest : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u x hx a b c hc
  have hpos : (S.r * S.N) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega))
  have hζ : IsUnit S.ζ := S.prim.isUnit hpos
  obtain ⟨c₀, hc₀⟩ := (hζ.pow (S.r * S.N * (eStd S.g _ a b).val)).map (algebraMap o S.R)
  have H := ρ.weil a b c₀ hc₀
  have hf : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap u.fac)
    exact (Spec.map_comp (CommRingCat.ofHom u.yK)
      (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p)))).symm
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk (spMap y₀) ((Category.comp_id _).trans hf.symm)
  have H' := CommPairing.weilIs_pull hL.globalFns ρ.P.isAb ρ.P.isLB h H
  have e : Units.map h.left.appTop.hom.toMonoidHom (unitOn c₀) = unitOn c := by
    refine Units.ext ?_
    refine (congrArg (fun q => q.hom c₀.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y₀))).symm.trans ?_
    show (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom (y₀ c₀.val) =
      (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom c.val
    rw [hc, hc₀]
  rw [e] at H'
  exact (weilIs_grpPullback_of_comm' _ _ ρ.P.A u.A.A (spMap u.yK) u.φ ρ.P.L u.A.L ρ.P.isLB u.A.isLB u.cart u.lb
    (TFK (R := u.V) (PadicAlgCl p)) _ (x a) (x b) (h ≫ ρ.pt a) (h ≫ ρ.pt b) (unitOn c) (hx a).symm (hx b).symm).2 H'

end GlobalTheory.ZH
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_projective_lattice_twist_generated : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (M : RatModel o Ω), IsProjOver M.s → ∀ (J : Type) [Fintype J] (EE : M.Lat J), ∃ (n : ℕ) (t : Fin (n + 1) → Ω) (e m : ℕ) (v : Fin m → J → Ω), M.IsCl t ∧ ∀ z i, M.Div t i z → EE.E z = Submodule.span (M.O z) (Set.range fun k j => v k j / t i ^ e) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isCl_lat_eq_span | exact GlobalTheory.ZH.RatModel.exists_isCl_lat_eq_span | (intros; apply GlobalTheory.ZH.RatModel.exists_isCl_lat_eq_span <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.twist_tx_ev_eq_map_arc_alt : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (u : Cˣ), (u : C) = φ PowerSeries.X → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (β₀ : N₀.Form k) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = β₀.be y z) → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p₀ : N₀.QT (m ^ 2)) (p : N.QT (m ^ 2)), p.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p.1.2 → (N.twist β u).tx m (N.twQ β u hm p) = I.lam * φ (N₀.arcTx β₀.be m p₀) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q₀ : N₀.QT j) (q : N.QT j), j ≠ 0 → q.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q.1.2 → ∀ s : ℕ, (m : ℤ) ^ 2 * β₀.be q₀.1.1.toAdd q₀.1.1.toAdd ≤ s → (u : C) ^ s * (N.twist β u).ev m (N.twQ β u hm p) (N.twQ β u hj q).1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv β₀.be m p₀ q₀ s) := by
  first | exact @GlobalTheory.Ex.twist_tx_ev_eq_map_arc | exact GlobalTheory.Ex.twist_tx_ev_eq_map_arc | (intros; apply GlobalTheory.Ex.twist_tx_ev_eq_map_arc <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_numD_iso_onG_of_allMatch : AllMatch fun {_} _ {N} {N'} {_} μ _ _ => μ.A → ∀ e, μ.B e → μ.Term e → ∀ I : NumB.Iso N.toNumB N'.toNumB, μ.OnB I → ∃ J : NumD.Iso N N', J.toIso = I ∧ J.e = e ∧ μ.OnG J := by
  first | exact @GlobalTheory.Ex.RecPeriods.exists_iso_onG | exact GlobalTheory.Ex.RecPeriods.exists_iso_onG | (intros; apply GlobalTheory.Ex.RecPeriods.exists_iso_onG <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.wQ_characterization_and_mul_relation : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ), Odd k → ∀ p p' : N.QT k, (∀ w : Oˣ, w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧ w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b)) ∧ N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') ∧ N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p := by
  first | exact @GlobalTheory.Ex.SymLift.normalising_factor | exact GlobalTheory.Ex.SymLift.normalising_factor | (intros; apply GlobalTheory.Ex.SymLift.normalising_factor <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.closedImmersionBaseChange_projChart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (U₀ : M.Z.Opens) (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (u₀ : U₀.toScheme ⟶ Sp R) (a : N.Z ⟶ X) (b : N.Z ⟶ U₀.toScheme) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω'), IsPullback a b p u₀ → M.IsHom N φ (b ≫ U₀.ι) → ImmBy p H s Set.univ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) → ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t := by
  first | exact @GlobalTheory.ZH.RatModel.projChart_of_isPullback | exact GlobalTheory.ZH.RatModel.projChart_of_isPullback | (intros; apply GlobalTheory.ZH.RatModel.projChart_of_isPullback <;> assumption)
end
