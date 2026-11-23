module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

namespace UpperTheory.Gal.W2.Seed.TypeIdempotent

variable {X M : Type} [Group X] [Group M]

private theorem psi_inv (T : TyLev X M) (k : X) (hk : k ∈ T.K) (hk' : k⁻¹ ∈ T.K) :
    (((T.ψ ⟨T.L.pr k⁻¹, T.fact.2 _ hk'⟩)⁻¹ : ℂˣ) : ℂ) = ((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩ : ℂˣ) : ℂ) := by
  have e : (⟨T.L.pr k⁻¹, T.fact.2 _ hk'⟩ : T.J) = (⟨T.L.pr k, T.fact.2 k hk⟩ : T.J)⁻¹ := by
    ext
    simp
  rw [e, map_inv, inv_inv]

private theorem tf_right (hA : TfAdm) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1) (y : X) (c : T.K₀) :
    T.tf h (y * c) = T.tf h y := by
  have hk : (c : X) ∈ T.K := T.le c.2
  rw [((hA X M T h hh).2 c hk y).2, T.ker c c.2]
  simp

private theorem tf_left (hA : TfAdm) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1) (y : X) (c : T.K₀) :
    T.tf h ((c : X) * y) = T.tf h y := by
  have hk : (c : X) ∈ T.K := T.le c.2
  rw [((hA X M T h hh).2 c hk y).1, T.ker c c.2]
  simp

private theorem ty_act (hA : TfAdm) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1)
    {V : Type} [AddCommGroup V] [Module ℂ V] (Φ : X → V) (hΦ : ∀ k ∈ T.K₀, ∀ g, Φ (g * k) = Φ g) :
    T.IsTy (hAct T.K₀ (T.tf h) Φ) := by
  intro k hk g
  have hF : ∀ (y : X) (c : T.K₀), (fun y => T.tf h (k⁻¹ * y) • Φ (g * y)) (y * c) =
      (fun y => T.tf h (k⁻¹ * y) • Φ (g * y)) y := by
    intro y c
    simp only
    rw [← mul_assoc, tf_right hA T h hh _ c, ← mul_assoc, hΦ c c.2]
  have hs := P.finsum_out_mul T.K₀ k (fun y => T.tf h (k⁻¹ * y) • Φ (g * y)) hF
  simp only [inv_mul_cancel_left] at hs
  simp only [hAct, mul_assoc]
  rw [hs, smul_finsum]
  congr 1
  funext x
  rw [((hA X M T h hh).2 k⁻¹ (T.K.inv_mem hk) _).1, mul_smul, psi_inv T k hk (T.K.inv_mem hk)]

private theorem conv_left (hA : TfAdm) (hC : TfCen) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1) :
    conv T.K₀ (T.tf 1) (T.tf h) = T.tf h := by
  funext g
  set Φ : X → ℂ := fun y => T.tf h (y⁻¹ * g) with hΦdef
  have hTy : T.IsTy Φ := by
    intro k hk y
    simp only [hΦdef, smul_eq_mul, mul_inv_rev, mul_assoc]
    rw [((hA X M T h hh).2 k⁻¹ (T.K.inv_mem hk) (y⁻¹ * g)).1, psi_inv T k hk (T.K.inv_mem hk)]
  have hc := hC X M T 1 (by simp [TyLev.Cen]) ℂ Φ hTy 1
  simp only [hAct, conv, one_mul, mul_one, inv_one, smul_eq_mul, hΦdef] at hc ⊢
  exact hc

private theorem tf_one_not_mem (T : TyLev X M) (y : X) (hy : y ∉ T.K) : T.tf 1 y = 0 := by
  have hn : y ∉ DoubleCoset.doubleCoset (1 : X) (T.K : Set X) T.K := by
    rw [DoubleCoset.mem_doubleCoset]
    rintro ⟨a, ha, b, hb, rfl⟩
    exact hy (by simpa using T.K.mul_mem ha hb)
  simp [TyLev.tf, dosetInd, Set.indicator_apply, hn]

private theorem tf_one_one (T : TyLev X M) : T.tf 1 1 = ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ := by
  have h1 : (1 : X) ∈ DoubleCoset.doubleCoset (1 : X) (T.K : Set X) T.K :=
    DoubleCoset.mem_doubleCoset.2 ⟨1, T.K.one_mem, 1, T.K.one_mem, by simp⟩
  have h2 : T.ψ ⟨1, T.J.one_mem⟩ = 1 := map_one T.ψ
  simp [TyLev.tf, tyFn, dosetInd, Set.indicator_apply, h1, T.J.one_mem, h2]

private theorem finsum_cosets (K K₀ : Subgroup X) (hle : K₀ ≤ K) (hi : K₀.relIndex K ≠ 0) (c : ℂ)
    (G : X ⧸ K₀ → ℂ) (h1 : ∀ z : X ⧸ K₀, z.out ∈ K → G z = c)
    (h0 : ∀ z : X ⧸ K₀, z.out ∉ K → G z = 0) :
    ∑ᶠ z, G z = ((K₀.relIndex K : ℕ) : ℂ) * c := by
  let φ : K ⧸ K₀.subgroupOf K → X ⧸ K₀ :=
    Quotient.map' (fun k : K => (k : X)) (fun a b hab => QuotientGroup.leftRel_apply.mpr (by
      have hab' := QuotientGroup.leftRel_apply.mp hab
      simpa [Subgroup.mem_subgroupOf] using hab'))
  have hφ : ∀ k : K, φ (k : K ⧸ K₀.subgroupOf K) = ((k : X) : X ⧸ K₀) := fun k => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [hφ, hφ, QuotientGroup.eq] at hab
    rw [QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using hab
  have hrange : ∀ z : X ⧸ K₀, z ∈ Set.range φ ↔ z.out ∈ K := by
    intro z
    constructor
    · rintro ⟨w, rfl⟩
      induction w using QuotientGroup.induction_on with | H k => ?_
      rw [hφ]
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K₀ (k : X)
      rw [hc]
      exact K.mul_mem k.2 (hle c.2)
    · intro hz
      refine ⟨((⟨z.out, hz⟩ : K) : K ⧸ K₀.subgroupOf K), ?_⟩
      rw [hφ]
      exact QuotientGroup.out_eq' z
  have hG : G = (Set.range φ).indicator (fun _ => c) := by
    funext z
    by_cases hz : z.out ∈ K
    · rw [Set.indicator_of_mem ((hrange z).2 hz), h1 z hz]
    · rw [Set.indicator_of_notMem (fun h => hz ((hrange z).1 h)), h0 z hz]
  rw [hG, ← finsum_mem_def, finsum_mem_range hinj]
  have hfin : Finite (K ⧸ K₀.subgroupOf K) := Nat.finite_of_card_ne_zero (by exact hi)
  haveI := Fintype.ofFinite (K ⧸ K₀.subgroupOf K)
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [← Nat.card_eq_fintype_card]
  rfl

private theorem conv_right (hA : TfAdm) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1) :
    conv T.K₀ (T.tf h) (T.tf 1) = T.tf h := by
  funext g
  have hF : ∀ (y : X) (c : T.K₀), (fun y => T.tf h y * T.tf 1 (y⁻¹ * g)) (y * c) =
      (fun y => T.tf h y * T.tf 1 (y⁻¹ * g)) y := by
    intro y c
    simp only
    rw [tf_right hA T h hh y c, mul_inv_rev, mul_assoc,
      show ((c : X)⁻¹) = ((c⁻¹ : T.K₀) : X) from rfl, tf_left hA T 1 (map_one _) (y⁻¹ * g) c⁻¹]
  have hs := P.finsum_out_mul T.K₀ g (fun y => T.tf h y * T.tf 1 (y⁻¹ * g)) hF
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] at hs
  simp only [conv]
  rw [← hs]
  rw [finsum_cosets T.K T.K₀ T.le T.idx (((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ * T.tf h g) _ ?_ ?_]
  · have hne : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 T.idx
    field_simp
  · intro z hz
    have hz' : (z.out)⁻¹ ∈ T.K := T.K.inv_mem hz
    rw [((hA X M T h hh).2 _ hz g).2]
    have e := ((hA X M T 1 (map_one _)).2 _ hz' 1).1
    rw [mul_one] at e
    rw [e, tf_one_one, psi_inv T _ hz hz']
    have hu := Units.inv_mul (T.ψ ⟨T.L.pr z.out, T.fact.2 _ hz⟩)
    linear_combination (T.tf h g * ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹) * hu
  · intro z hz
    rw [tf_one_not_mem T _ (fun h' => hz (by simpa using T.K.inv_mem h')), mul_zero]

end UpperTheory.Gal.W2.Seed.TypeIdempotent

open UpperTheory.Gal.W2.Seed.TypeIdempotent in
theorem UpperTheory.Gal.W2.Seed.pTfIdem : TfAdm → TfCen → TfIdem := by
  intro hA hC X M _ _ T h hh
  exact ⟨fun V _ _ Φ hΦ => ty_act hA T h hh Φ hΦ, conv_right hA T h hh, conv_left hA hC T h hh⟩
end

section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem typeFunction_mul_mem {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) (a b : M) (hb : b ∈ J) :
    tyFn J ψ (a * b) = tyFn J ψ a * (((ψ ⟨b, hb⟩)⁻¹ : ℂˣ) : ℂ) := by
  unfold tyFn
  by_cases ha : a ∈ J
  · have hab : a * b ∈ J := J.mul_mem ha hb
    rw [dite_eq_left ha, dite_eq_left hab]
    have : (⟨a * b, hab⟩ : J) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, mul_inv, Units.val_mul]
  · have hab : a * b ∉ J := fun h => ha (by simpa using J.mul_mem h (J.inv_mem hb))
    rw [dite_eq_right ha, dite_eq_right hab, zero_mul]

private theorem typeFunction_one {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) : tyFn J ψ 1 = 1 := by
  unfold tyFn
  rw [dite_eq_left J.one_mem]
  have : (⟨1, J.one_mem⟩ : J) = 1 := rfl
  rw [this, map_one, inv_one, Units.val_one]

private theorem doubleCosetIndicator_central {X : Type} [Group X] (K : Subgroup X) (a z w : X) (hz : ∀ g, z * g = g * z) :
    dosetInd ℂ K (a * z) (z * w) = dosetInd ℂ K a w := by
  have key : z * w ∈ DoubleCoset.doubleCoset (a * z) (K : Set X) (K : Set X) ↔
      w ∈ DoubleCoset.doubleCoset a (K : Set X) (K : Set X) := by
    simp only [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨x, hx, y, hy, ?_⟩
      have e' : z * w = z * (x * a * y) := by
        rw [e, hz (x * a * y)]
        have h1 : x * (a * z) * y = x * a * (z * y) := by group
        rw [h1, hz y]
        group
      exact mul_left_cancel e'
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨x, hx, y, hy, ?_⟩
      rw [e, hz (x * a * y)]
      have h1 : x * (a * z) * y = x * a * (z * y) := by group
      rw [h1, hz y]
      group
  unfold dosetInd
  by_cases hw : w ∈ DoubleCoset.doubleCoset a (K : Set X) (K : Set X)
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (key.mpr hw)]; rfl
  · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (fun h => hw (key.mp h))]

theorem UpperTheory.Gal.W2.Seed.pTfAct :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (V : Type) [AddCommGroup V] [Module ℂ V] (Ψ : X → V), (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Ψ y.out = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out)) → TfAdm → TfAct := by
  intro hidx hfac hadm X M M' _ _ _ T L' Kw hF hAp t z hz V _ _ Φ hΦ g
  have hh : T.L.pr (L'.loc t * z) = 1 := by rw [map_mul, hAp.1 t, hz.2, one_mul]
  obtain ⟨-, hinv⟩ := hadm X M T _ hh
  have hc0 : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr T.idx
  have h0 : ∀ k ∈ T.K, ∀ x, T.tf (L'.loc t * z) (x * k) • Φ (g * (x * k)) =
      T.tf (L'.loc t * z) x • Φ (g * x) := by
    intro k hk x
    rw [(hinv k hk x).2, ← mul_assoc, hΦ k hk, smul_smul, mul_right_comm, Units.inv_mul, one_mul]
  let F : X → V := fun y =>
    (tyFn T.J T.ψ (T.L.pr y) * dosetInd ℂ T.K (L'.loc t * z) y) • Φ (g * y)
  have hF1 : ∀ y, ((T.K₀.relIndex T.K : ℕ) : ℂ) • (T.tf (L'.loc t * z) y • Φ (g * y)) = F y := by
    intro y
    simp only [F, TyLev.tf]
    rw [smul_smul, mul_assoc, mul_inv_cancel_left₀ hc0]
  have hFinv : ∀ (y : X) (k : T.K), F (y * k) = F y := by
    intro y k
    rw [← hF1, ← hF1, h0 k k.2 y]
  let Ψ : X → V := fun y => tyFn T.J T.ψ (T.L.pr y) • Φ (g * z * y)
  have hΨ : ∀ k ∈ T.K, ∀ y, Ψ (y * k) = Ψ y := by
    intro k hk y
    simp only [Ψ]
    rw [map_mul, typeFunction_mul_mem T.J T.ψ _ _ (T.fact.2 k hk), ← mul_assoc, hΦ k hk, smul_smul,
      mul_assoc, Units.inv_mul, mul_one]
  have e1 := hidx X V T.K T.K₀ T.le T.idx (fun x => T.tf (L'.loc t * z) x • Φ (g * x)) h0
  have e2 := hfac X M' L' T.K Kw hF t V Ψ hΨ
  calc hAct T.K₀ (T.tf (L'.loc t * z)) Φ g
      = ((T.K₀.relIndex T.K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ T.K, T.tf (L'.loc t * z) y.out • Φ (g * y.out) := e1
    _ = ∑ᶠ y : X ⧸ T.K, F y.out := by
        rw [smul_finsum]
        exact finsum_congr fun y => hF1 _
    _ = ∑ᶠ y : X ⧸ T.K, F (z * y.out) := (Formalism.UG.P.finsum_out_mul T.K z F hFinv).symm
    _ = ∑ᶠ y : X ⧸ T.K, dosetInd ℂ T.K (L'.loc t) y.out • Ψ y.out := by
        refine finsum_congr fun y => ?_
        simp only [F, Ψ]
        rw [doubleCosetIndicator_central T.K _ z _ hz.1, map_mul, hz.2, one_mul, smul_smul, ← mul_assoc g z,
          mul_comm]
    _ = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out) := e2
    _ = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Φ (g * z * L'.loc x.out) := by
        refine finsum_congr fun x => ?_
        simp only [Ψ]
        rw [hAp.1, typeFunction_one, one_smul]
end

section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pConvRing :
    ConvRing := by
  intro X _ K hK f hf f' hf'
  refine ⟨Formalism.UG.Final.HeckeConvMem X K ℂ hK f hf f' hf', fun f'' hf'' => ?_⟩
  exact Formalism.UG.Final.HeckeAssoc X K ℂ hK f hf f' hf' f'' hf''
end

section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem tyFn_mul_of_mem {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) (a b : M)
    (ha : a ∈ J) : tyFn J ψ a * tyFn J ψ b = tyFn J ψ (a * b) := by
  unfold tyFn
  by_cases hb : b ∈ J
  · have hab : a * b ∈ J := J.mul_mem ha hb
    rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left hab]
    have e : (⟨a * b, hab⟩ : J) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, mul_inv, Units.val_mul, mul_comm]
  · have hab : a * b ∉ J := fun h => hb (by simpa using J.mul_mem (J.inv_mem ha) h)
    rw [dite_eq_right hb, dite_eq_right hab, mul_zero]

private theorem mem_doubleCoset_loc_mul_of_mem_of_pr_eq_one {X M' : Type} [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X)
    (Kw : Subgroup M') (hF : L'.Fact K Kw)
    (hC : ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔
      L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧
        (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K)
    (t : M') (r g y : X) (hr : L'.pr r = 1) (hy : y ∈ DoubleCoset.doubleCoset r (K : Set X) K)
    (hz : y⁻¹ * g ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K) :
    g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ∧
      y⁻¹ * ((L'.loc (L'.pr g))⁻¹ * g) ∈ K := by
  obtain ⟨hn, hk⟩ := (hC t 1 (map_one _) (y⁻¹ * g)).1 (by rw [mul_one]; exact hz)
  obtain ⟨ha, hy'⟩ := (hC 1 r hr y).1 (by rw [map_one, one_mul]; exact hy)
  have haK : L'.pr y ∈ Kw := by
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 ha
    rw [e, mul_one]
    exact Kw.mul_mem hu hv
  have hkK : (L'.loc (L'.pr (y⁻¹ * g)))⁻¹ * (y⁻¹ * g) ∈ K := by
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hk
    rw [e, mul_one]
    exact K.mul_mem hu hv
  generalize hkd : (L'.loc (L'.pr (y⁻¹ * g)))⁻¹ * (y⁻¹ * g) = k at hkK
  generalize hyd : (L'.loc (L'.pr y))⁻¹ * y = y' at hy'
  have hm : L'.pr g = L'.pr y * L'.pr (y⁻¹ * g) := by simp
  generalize had : L'.pr y = a at haK hm hyd
  generalize hnd : L'.pr (y⁻¹ * g) = n at hn hm hkd
  have hpy' : L'.pr y' = 1 := by
    rw [← hyd, map_mul, map_inv, L'.pr_loc, had, inv_mul_cancel]
  have hcomm : ∀ x, L'.loc x * y' = y' * L'.loc x := fun x => L'.comm x y' hpy'
  have hy1 : y = L'.loc a * y' := by rw [← hyd]; group
  have hg : g = L'.loc a * y' * (L'.loc n * k) := by
    rw [← hkd, ← hy1]; group
  have hy0 : (L'.loc (L'.pr g))⁻¹ * g = y' * k := by
    rw [hm, map_mul, hg, mul_assoc (L'.loc a), ← mul_assoc y', ← hcomm n]
    group
  refine ⟨(hC t r hr g).2 ⟨?_, ?_⟩, ?_⟩
  · rw [hm]
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hn
    exact DoubleCoset.mem_doubleCoset.2 ⟨a * u, Kw.mul_mem haK hu, v, hv, by rw [e]; group⟩
  · rw [hy0]
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hy'
    exact DoubleCoset.mem_doubleCoset.2 ⟨u, hu, v * k, K.mul_mem hv hkK, by rw [e]; group⟩
  · rw [hy0]
    have e : y⁻¹ * (y' * k) = (L'.loc a)⁻¹ * k := by
      calc y⁻¹ * (y' * k) = y'⁻¹ * ((L'.loc a)⁻¹ * y') * k := by rw [hy1]; group
        _ = y'⁻¹ * (y' * (L'.loc a)⁻¹) * k := by rw [← map_inv, hcomm]
        _ = (L'.loc a)⁻¹ * k := by group
    rw [e]
    exact K.mul_mem (K.inv_mem (hF.1 a haK)) hkK

private theorem mem_doubleCosets_of_dosetInd_mul_ne_zero {X : Type} [Group X] (K : Subgroup X) (a b : ℂ) (r s x g : X)
    (h : a * dosetInd ℂ K r x * (b * dosetInd ℂ K s (x⁻¹ * g)) ≠ 0) :
    x ∈ DoubleCoset.doubleCoset r (K : Set X) K ∧
      x⁻¹ * g ∈ DoubleCoset.doubleCoset s (K : Set X) K := by
  constructor
  · by_contra hn
    apply h
    simp [dosetInd, Set.indicator_apply, hn]
  · by_contra hn
    apply h
    simp [dosetInd, Set.indicator_apply, hn]

theorem UpperTheory.Gal.W2.Seed.pTfMulR :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → TfAdm → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K) → TfMulR := by
  intro hA hAdm hC X M M' _ _ _ T L' Kw hF hAp t r hr hr'
  funext g
  have hloc : T.L.pr (L'.loc t) = 1 := hAp.1 t
  have hinv : ∀ k ∈ T.K, ∀ x : X,
      T.tf r (x * k) * T.tf (L'.loc t) ((x * k)⁻¹ * g) = T.tf r x * T.tf (L'.loc t) (x⁻¹ * g) := by
    intro k hk x
    have h1 := ((hAdm X M T r hr).2 k hk x).2
    have h2 := ((hAdm X M T (L'.loc t) hloc).2 k⁻¹ (T.K.inv_mem hk) (x⁻¹ * g)).1
    rw [show (x * k)⁻¹ * g = k⁻¹ * (x⁻¹ * g) by group, h1, h2]
    have p1 : T.L.pr k ∈ T.J := T.fact.2 k hk
    have p2 : T.L.pr k⁻¹ ∈ T.J := T.fact.2 k⁻¹ (T.K.inv_mem hk)
    have e : (⟨T.L.pr k⁻¹, p2⟩ : T.J) = (⟨T.L.pr k, p1⟩ : T.J)⁻¹ := Subtype.ext (map_inv _ _)
    rw [e, map_inv, inv_inv]
    have hu := Units.inv_mul (T.ψ ⟨T.L.pr k, p1⟩)
    linear_combination (T.tf r x * T.tf (L'.loc t) (x⁻¹ * g)) * hu
  have hsum := hA X ℂ T.K T.K₀ T.le T.idx (fun x => T.tf r x * T.tf (L'.loc t) (x⁻¹ * g)) hinv
  beta_reduce at hsum
  unfold conv
  rw [hsum]
  have hc : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := by exact_mod_cast T.idx
  by_cases hg : g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (T.K : Set X) T.K
  · obtain ⟨hm, hy0⟩ := (hC X M' L' T.K Kw hF t r hr' g).1 hg
    obtain ⟨y₀, hy0d⟩ : ∃ y₀, y₀ = (L'.loc (L'.pr g))⁻¹ * g := ⟨_, rfl⟩
    rw [← hy0d] at hy0
    have hp0 : L'.pr y₀ = 1 := by rw [hy0d, map_mul, map_inv, L'.pr_loc, inv_mul_cancel]
    have hcomm : L'.loc (L'.pr g) * y₀ = y₀ * L'.loc (L'.pr g) := L'.comm _ _ hp0
    have hg0 : g = L'.loc (L'.pr g) * y₀ := by rw [hy0d]; group
    have hz0 : y₀⁻¹ * g = L'.loc (L'.pr g) := by
      calc y₀⁻¹ * g = y₀⁻¹ * (L'.loc (L'.pr g) * y₀) := by rw [← hg0]
        _ = L'.loc (L'.pr g) := by rw [hcomm]; group
    have hzK : y₀⁻¹ * g ∈ DoubleCoset.doubleCoset (L'.loc t) (T.K : Set X) T.K := by
      rw [hz0]
      obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hm
      exact DoubleCoset.mem_doubleCoset.2
        ⟨L'.loc u, hF.1 u hu, L'.loc v, hF.1 v hv, by rw [e, map_mul, map_mul]⟩
    have hJ : T.L.pr y₀ ∈ T.J := by
      obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hy0
      rw [e, map_mul, map_mul, hr, mul_one]
      exact T.J.mul_mem (T.fact.2 u hu) (T.fact.2 v hv)
    rw [finsum_eq_single _ (QuotientGroup.mk y₀ : X ⧸ T.K)]
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul T.K y₀
      rw [hk, hinv k k.2 y₀]
      have hτ := tyFn_mul_of_mem T.J T.ψ _ (T.L.pr (y₀⁻¹ * g)) hJ
      rw [← map_mul, mul_inv_cancel_left] at hτ
      simp only [TyLev.tf, dosetInd, Set.indicator_of_mem hy0, Set.indicator_of_mem hzK,
        Set.indicator_of_mem hg, Pi.one_apply]
      rw [smul_eq_mul, ← hτ]
      field_simp
    · intro q hq
      by_contra hne
      apply hq
      simp only [TyLev.tf] at hne
      have hm1 := mem_doubleCosets_of_dosetInd_mul_ne_zero T.K _ _ r (L'.loc t) q.out g hne
      have hK := (mem_doubleCoset_loc_mul_of_mem_of_pr_eq_one L' T.K Kw hF (hC X M' L' T.K Kw hF) t r g q.out hr' hm1.1 hm1.2).2
      rw [← hy0d] at hK
      have h := (QuotientGroup.eq (s := T.K)).2 hK
      rwa [QuotientGroup.out_eq'] at h
  · rw [finsum_eq_zero_of_forall_eq_zero]
    · simp [TyLev.tf, dosetInd, hg]
    · intro q
      by_contra hne
      apply hg
      simp only [TyLev.tf] at hne
      have hm1 := mem_doubleCosets_of_dosetInd_mul_ne_zero T.K _ _ r (L'.loc t) q.out g hne
      exact (mem_doubleCoset_loc_mul_of_mem_of_pr_eq_one L' T.K Kw hF (hC X M' L' T.K Kw hF) t r g q.out hr' hm1.1 hm1.2).1
end

section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms
open scoped Classical

namespace UpperTheory.Gal.W2.Seed

theorem pConvSupp : ConvSupp := by
  intro X _ K f f' g h
  by_contra hne
  push_neg at hne
  apply h
  unfold conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  by_contra hq
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hq
  exact hne _ _ h1 h2 (mul_inv_cancel_left _ _).symm

end UpperTheory.Gal.W2.Seed
end
