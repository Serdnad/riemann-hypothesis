module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open Coalgebra

namespace GlobalTheory.HTPair

open _root_.GlobalTheory.PDiv

structure QuotTower {p : ℕ} {O : Type} [CommRing O] (G : _root_.GlobalTheory.PDivGroup p O) : Type 1 where

  B : ℕ → Type
  [commRing : ∀ m, CommRing (B m)]
  [hopf : ∀ m, HopfAlgebra O (B m)]
  [cocomm : ∀ m, IsCocomm O (B m)]
  [finite : ∀ m, Module.Finite O (B m)]
  [projective : ∀ m, Module.Projective O (B m)]

  j : ∀ m, B m →ₐc[O] G.A (m + 1)

  ρ : ∀ m, G.A (m + 1) →ₗ[O] B m

  r : ∀ m, B (m + 1) →ₐc[O] B m

  s : ∀ m, G.A m →ₐc[O] B m

  ρ_j : ∀ m b, ρ m (j m b) = b

  r_surjective : ∀ m, Function.Surjective (r m)

  j_r : ∀ m b, j m (r m b) = G.res (m + 1) (j (m + 1) b)

  j_s : ∀ m a, j m (s m a) = G.mulP m a

  tors_le : ∀ m, torsionIdeal (R := O) (A := G.A (m + 1)) p ≤ kerIdeal (j m)

attribute [instance] QuotTower.commRing QuotTower.hopf QuotTower.cocomm QuotTower.finite
  QuotTower.projective

def QuotTower.trivial {p : ℕ} {O : Type} [CommRing O] (G : _root_.GlobalTheory.PDivGroup p O) : QuotTower G where
  B m := G.A (m + 1)
  j _ := BialgHom.id O _
  ρ _ := LinearMap.id
  r m := G.res (m + 1)
  s m := G.mulP m
  ρ_j _ _ := rfl
  r_surjective m := G.res_surjective (m + 1)
  j_r _ _ := rfl
  j_s _ _ := rfl
  tors_le m := by
    rw [kerIdeal_of_surjective (f := BialgHom.id O (G.A (m + 1))) Function.surjective_id]
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    have ha' : counit (R := O) a = 0 := ha
    change counit (R := O) (mulBy (R := O) (A := G.A (m + 1)) p a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha']

theorem exists_retraction_mulP {p : ℕ} {O : Type} [CommRing O] (G : _root_.GlobalTheory.PDivGroup p O) (m : ℕ) :
    ∃ ρ : G.A (m + 1) →ₗ[O] G.A m, ∀ a, ρ (G.mulP m a) = a := by
  let f : G.A m →ₗ[O] G.A (m + 1) := (G.mulP m : G.A m →ₐ[O] G.A (m + 1)).toLinearMap
  have hs : Function.Surjective f.dualMap := fun φ => by
    obtain ⟨ψ, hψ⟩ := G.dual_mulP_surjective m (WithConv.toConv φ)
    exact ⟨ψ.ofConv, congrArg WithConv.ofConv hψ⟩
  obtain ⟨σ, hσ⟩ := f.dualMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)
  refine ⟨(Module.evalEquiv O (G.A m)).symm.toLinearMap ∘ₗ σ.dualMap ∘ₗ
    (Module.evalEquiv O (G.A (m + 1))).toLinearMap, fun a => ?_⟩
  change (Module.evalEquiv O (G.A m)).symm _ = a
  rw [LinearEquiv.symm_apply_eq]
  ext φ
  exact LinearMap.congr_fun (LinearMap.congr_fun hσ φ) a

def QuotTower.full {p : ℕ} {O : Type} [CommRing O] (G : _root_.GlobalTheory.PDivGroup p O) : QuotTower G where
  B m := G.A m
  j m := G.mulP m
  ρ m := (exists_retraction_mulP G m).choose
  r m := G.res m
  s _ := BialgHom.id O _
  ρ_j m := (exists_retraction_mulP G m).choose_spec
  r_surjective := G.res_surjective
  j_r m b := by rw [G.mulP_res, G.res_mulP]
  j_s _ _ := rfl
  tors_le m := by
    rw [← kerIdeal_comp_of_surjective _ (G.res_surjective m), G.mulP_comp_res]

theorem QuotTower.map_res_kerIdeal {p : ℕ} {O : Type} [CommRing O] {G : _root_.GlobalTheory.PDivGroup p O}
    (T : QuotTower G) (m : ℕ) :
    Ideal.map (G.res (m + 1) : G.A (m + 2) →ₐ[O] G.A (m + 1)) (kerIdeal (T.j (m + 1))) =
      kerIdeal (T.j m) := by
  have h : (G.res (m + 1)).comp (T.j (m + 1)) = (T.j m).comp (T.r m) :=
    BialgHom.ext fun b => (T.j_r m b).symm
  rw [← kerIdeal_comp, h, kerIdeal_comp_of_surjective (T.j m) (T.r_surjective m)]

end GlobalTheory.HTPair
end
end

section

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory

namespace GlobalTheory.PDivGroup.Test

open PDiv

variable {p : ℕ} {O : Type} [CommRing O]


open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory in
variable {p : ℕ} {O : Type} [CommRing O] in
theorem _root_.GlobalTheory.PDivGroup.Test.mulP_injective (G : _root_.GlobalTheory.PDivGroup p O) (n : ℕ) :
    Function.Injective (G.mulP n) := by
  intro x y hxy
  have hinj := _root_.GlobalTheory.CartierDual.map_injective_of_surjective (G.dual_mulP_surjective n)
  have hx := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) x
  have hy := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) y
  rw [hxy, ← hy] at hx
  exact (_root_.GlobalTheory.CartierDual.bidual O (G.A n)).injective (hinj hx)

theorem hodgeTate_values [Fact p.Prime] (hp : ¬ IsUnit (p : O)) :
    (∀ t, hodgeTate (mu p O) t = 0) ∧ hodgeTate (const p O) (constGen p O) ≠ 0 := by
  refine ⟨fun t => Subsingleton.elim _ _, fun h => dlogT_ne_zero p O hp ?_⟩
  rw [hodgeTate_eq_omegaMap, ← dualHom_constHom, show constHom _ (constGen p O) = 𝟙 _ by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], dualHom_id,
    Category.id_comp] at h
  have h2 := LinearMap.congr_fun (omegaMap_comp (mu p O).bidual.hom (mu p O).bidual.inv) (dlogT p O)
  rw [Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply, LinearMap.comp_apply] at h2
  rw [h2]
  exact (congrArg _ h).trans (map_zero _)

section Prod

variable (A B : Type) [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]

def inl : A →ₐc[O] A ⊗[O] B :=
  (Bialgebra.TensorProduct.map (BialgHom.id O A) (Bialgebra.unitBialgHom O B)).comp
    (Bialgebra.TensorProduct.rid O O A).symm.toBialgHom

def inr : B →ₐc[O] A ⊗[O] B :=
  (Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom O A) (BialgHom.id O B)).comp
    (Bialgebra.TensorProduct.lid O B).symm.toBialgHom

variable {A B}

theorem inl_apply (a : A) : inl (O := O) A B a = a ⊗ₜ 1 :=
  congrArg (fun y : B => a ⊗ₜ[O] y) (map_one (Bialgebra.unitBialgHom O B))

theorem inr_apply (b : B) : inr (O := O) A B b = 1 ⊗ₜ b :=
  congrArg (fun y : A => y ⊗ₜ[O] b) (map_one (Bialgebra.unitBialgHom O A))

theorem pts_ext {E : Type} [CommRing E] [Algebra O E] {x y : WithConv (A ⊗[O] B →ₐ[O] E)}
    (h1 : pointsMap E (inl A B) x = pointsMap E (inl A B) y)
    (h2 : pointsMap E (inr A B) x = pointsMap E (inr A B) y) : x = y := by
  refine ofConv_injective (Algebra.TensorProduct.ext' fun a b => ?_)
  have e1 : x.ofConv (inl A B a) = y.ofConv (inl A B a) := DFunLike.congr_fun (congrArg ofConv h1) a
  have e2 : x.ofConv (inr A B b) = y.ofConv (inr A B b) := DFunLike.congr_fun (congrArg ofConv h2) b
  have e : a ⊗ₜ[O] b = inl A B a * inr A B b := by simp [inl_apply, inr_apply]
  rw [e, map_mul, map_mul, e1, e2]

end Prod

@[reducible] def prod (G H : PDivGroup p O) : PDivGroup p O where
  height := G.height + H.height
  A n := G.A n ⊗[O] H.A n
  rank_eq n q := by
    rw [rankAtStalk_tensorProduct, Pi.mul_apply, G.rank_eq, H.rank_eq, mul_add, pow_add]
  res n := Bialgebra.TensorProduct.map (G.res n) (H.res n)
  res_surjective n := TensorProduct.map_surjective (g := (G.res n).toLinearMap) (g' := (H.res n).toLinearMap) (G.res_surjective n) (H.res_surjective n)
  ker_res n := by
    refine le_antisymm (fun a ha => ?_) ?_
    · let π := Ideal.Quotient.mkₐ O
        (torsionIdeal (R := O) (A := G.A (n + 1) ⊗[O] H.A (n + 1)) (p ^ n))
      have h1 := (torsionIdeal_le_ker_iff (p ^ n) π).1
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
      obtain ⟨y, hy⟩ := (G.exists_comp_res_iff n (pointsMap _ (inl _ _) (toConv π)).ofConv).2
        (by rw [toConv_ofConv, ← map_pow, h1, map_one])
      obtain ⟨z, hz⟩ := (H.exists_comp_res_iff n (pointsMap _ (inr _ _) (toConv π)).ofConv).2
        (by rw [toConv_ofConv, ← map_pow, h1, map_one])
      have h2 : (Algebra.TensorProduct.lift y z fun _ _ => .all _ _).comp
          (Bialgebra.TensorProduct.map (G.res n) (H.res n) :
            G.A (n + 1) ⊗[O] H.A (n + 1) →ₐ[O] G.A n ⊗[O] H.A n) = π :=
        Algebra.TensorProduct.ext' fun a b => by
          have e1 : y (G.res n a) = π (inl _ _ a) := DFunLike.congr_fun hy a
          have e2 : z (H.res n b) = π (inr _ _ b) := DFunLike.congr_fun hz b
          change y (G.res n a) * z (H.res n b) = _
          rw [e1, e2, ← map_mul, inl_apply, inr_apply]
          simp
      have h3 := (DFunLike.congr_fun h2 a).symm
      rw [AlgHom.comp_apply] at h3
      erw [show Bialgebra.TensorProduct.map (G.res n) (H.res n) a = 0 from ha, map_zero] at h3
      exact Ideal.Quotient.eq_zero_iff_mem.1 h3
    · refine (torsionIdeal_le_ker_iff (p ^ n) (Bialgebra.TensorProduct.map (G.res n) (H.res n) :
          G.A (n + 1) ⊗[O] H.A (n + 1) →ₐ[O] G.A n ⊗[O] H.A n)).2 (pts_ext ?_ ?_)
      · rw [map_pow, map_one]
        refine (G.exists_comp_res_iff n _).1 ⟨(inl (O := O) (G.A n) (H.A n)).toAlgHom, AlgHom.ext fun a => ?_⟩
        change inl _ _ (G.res n a) = Bialgebra.TensorProduct.map (G.res n) (H.res n) (inl _ _ a)
        simp [inl_apply]
      · rw [map_pow, map_one]
        refine (H.exists_comp_res_iff n _).1 ⟨(inr (O := O) (G.A n) (H.A n)).toAlgHom, AlgHom.ext fun a => ?_⟩
        change inr _ _ (H.res n a) = Bialgebra.TensorProduct.map (G.res n) (H.res n) (inr _ _ a)
        simp [inr_apply]

end GlobalTheory.PDivGroup.Test
end
end

section

open MeasureTheory Matrix

noncomputable section
namespace GlobalTheory.LGrp

section Rational
open Polynomial

def IsLaurentPoly (R : RatFunc ℂ) : Prop :=
  ∃ (m : ℕ) (p : ℂ[X]), R * RatFunc.X ^ m = algebraMap _ _ p

def lFactor (S : Multiset ℂˣ) : RatFunc ℂ := (S.map fun a : ℂˣ => (1 - RatFunc.C (a : ℂ) * RatFunc.X)⁻¹).prod

end Rational

section ZetaNonvanishing₂
open ValuativeRel GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

variable [MeasurableSpace (GL n k)]

variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ}

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in
private theorem valuation_det_le_one_of_entries_integer {y : GL n k}
    (h : ∀ i j, (y : Matrix n n k) i j ∈ (valuation k).integer) :
    valuation k (GeneralLinearGroup.det y : k) ≤ 1 := by
  set A : Matrix n n (valuation k).integer := Matrix.of fun i j => ⟨(y : Matrix n n k) i j, h i j⟩
  have e : (y : Matrix n n k) = ((valuation k).integer.subtype).mapMatrix A := by
    ext i j
    rfl
  have hd : (GeneralLinearGroup.det y : k) = (valuation k).integer.subtype A.det := by
    rw [GeneralLinearGroup.val_det_apply, RingHom.map_det, ← e]
  rw [hd]
  exact (Valuation.mem_integer_iff _ _).mp (SetLike.coe_mem _)


open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in
theorem _root_.GlobalTheory.LGrp.nabs_det_of_mem_KO {x : GL n k}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det x) = 1 := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hx
  apply _root_.GlobalTheory.SmGL.nabs_eq_one
  have h1 := valuation_det_le_one_of_entries_integer hx.1
  have h2 := valuation_det_le_one_of_entries_integer hx.2
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at h2
  have hpos : 0 < valuation k (GeneralLinearGroup.det x : k) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
private theorem smGL_ord_pow_eq_mul (x : kˣ) (m : ℕ) :
    _root_.GlobalTheory.SmGL.ord k (x ^ m) = m * _root_.GlobalTheory.SmGL.ord k x := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
  | succ m ih =>
    rw [pow_succ, _root_.GlobalTheory.SmGL.ord_mul, ih]
    push_cast
    ring

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
private theorem exists_unit_ord_eq_one_and_nabs_eq_inv_resCard :
    ∃ ϖ : kˣ, _root_.GlobalTheory.SmGL.ord k ϖ = 1 ∧
      _root_.GlobalTheory.SplitWeil.nabs k ϖ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ)⁻¹ := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (valuation k).integer
  have hp0 : (p : k) ≠ 0 := by
    intro h
    exact hp.ne_zero (Subtype.ext h)
  obtain ⟨y, hy⟩ : ∃ y : k, valuation k y = uniformizer k := valuation_surjective _
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact (uniformizer_pos (R := k)).ne hy
  have hyint : y ∈ (valuation k).integer := by
    rw [Valuation.mem_integer_iff, hy]
    exact uniformizer_lt_one.le
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨y, hyint⟩ : (valuation k).integer)) (fun h => hy0 (congrArg Subtype.val h)) hp
  have hu0 : ((u : (valuation k).integer) : k) ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  refine ⟨Units.mk0 (p : k) hp0, ?_, _root_.GlobalTheory.SplitWeil.nabs_uniformiser hp rfl⟩
  have hyo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 y hy0) = 1 :=
    _root_.GlobalTheory.SmGL.ord_eq_one hy
  have huo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 _ hu0) = 0 := by
    apply _root_.GlobalTheory.SmGL.ord_eq_zero
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
  have hsplit : Units.mk0 y hy0 = Units.mk0 _ hu0 * Units.mk0 (p : k) hp0 ^ m := by
    ext
    have := congrArg Subtype.val hu
    simpa using this
  rw [hsplit, _root_.GlobalTheory.SmGL.ord_mul, huo, smGL_ord_pow_eq_mul,
    zero_add] at hyo
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hyo with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2
  · omega


open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in
theorem _root_.GlobalTheory.LGrp.nabs_eq_zpow (x : kˣ) :
    _root_.GlobalTheory.SplitWeil.nabs k x =
      (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-_root_.GlobalTheory.SmGL.ord k x) := by
  obtain ⟨ϖ, hord, habs⟩ := exists_unit_ord_eq_one_and_nabs_eq_inv_resCard (k := k)
  have hq : (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ≠ 0 := by
    have := _root_.GlobalTheory.SplitWeil.one_lt_resCard k
    positivity
  have hinv : _root_.GlobalTheory.SplitWeil.nabs k ϖ⁻¹ = _root_.GlobalTheory.SplitWeil.resCard k := by
    have h := _root_.GlobalTheory.SplitWeil.nabs_mul k ϖ ϖ⁻¹
    rw [mul_inv_cancel, _root_.GlobalTheory.SplitWeil.nabs_one, habs] at h
    exact ((inv_mul_eq_one₀ hq).mp h.symm).symm
  have oinv : _root_.GlobalTheory.SmGL.ord k ϖ⁻¹ = -1 := by
    have h := _root_.GlobalTheory.SmGL.ord_mul k ϖ ϖ⁻¹
    rw [mul_inv_cancel, hord,
      _root_.GlobalTheory.SmGL.ord_eq_zero (x := (1 : kˣ)) (by simp only [Units.val_one, map_one])] at h
    omega
  have key : ∀ m : ℤ, _root_.GlobalTheory.SplitWeil.nabs k (ϖ ^ m) =
      (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) ∧ _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
    intro m
    refine Int.induction_on m ?_ ?_ ?_
    · refine ⟨by simp [_root_.GlobalTheory.SplitWeil.nabs_one], ?_⟩
      rw [zpow_zero]
      exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
    · intro i ih
      rw [_root_.zpow_add_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
        ih.1, ih.2, habs, hord]
      refine ⟨?_, rfl⟩
      rw [neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
    · intro i ih
      rw [_root_.zpow_sub_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
        ih.1, ih.2, hinv, oinv]
      refine ⟨?_, by ring⟩
      rw [show -(-(i : ℤ) - 1) = -(-(i : ℤ)) + 1 by ring, zpow_add₀ hq, _root_.zpow_one]
  set o := _root_.GlobalTheory.SmGL.ord k x
  have hy : _root_.GlobalTheory.SmGL.ord k (x * ϖ ^ (-o)) = 0 := by
    rw [_root_.GlobalTheory.SmGL.ord_mul, (key _).2]
    ring
  have hy1 : _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o)) = 1 :=
    _root_.GlobalTheory.SmGL.nabs_eq_one k
      (_root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp hy)
  have hx : x * ϖ ^ (-o) * ϖ ^ o = x := by
    rw [mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
  calc _root_.GlobalTheory.SplitWeil.nabs k x
      = _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o) * ϖ ^ o) := by rw [hx]
    _ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-o) := by
      rw [_root_.GlobalTheory.SplitWeil.nabs_mul, hy1, (key o).1, one_mul]


end ZetaNonvanishing₂

end GlobalTheory.LGrp
end
end
