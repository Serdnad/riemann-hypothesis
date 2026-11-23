module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.InertChar

open ValuativeRel

variable {F : Type} [Field F] [NumberField F]

theorem valued_eq_exp_ordL (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    Valued.v (x : v.adicCompletion F) = WithZero.exp (-Formalism.UG.ordL (x : v.adicCompletion F)) := by
  have h0 : Valued.v (x : v.adicCompletion F) ≠ 0 := (_root_.map_ne_zero _).2 x.ne_zero
  rw [← WithZero.exp_log h0]
  congr 1
  unfold Formalism.UG.ordL
  rw [dite_eq_right h0, neg_neg]
  have key : ∀ (z : WithZero (Multiplicative ℤ)) (h : z ≠ 0), WithZero.log z = Multiplicative.toAdd (WithZero.unzero h) := by
    intro z h
    cases z with
    | zero => exact absurd rfl h
    | coe a => rfl
  exact key _ h0

theorem ord_eq_ordL (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    GlobalTheory.SmGL.ord (v.adicCompletion F) x = Formalism.UG.ordL (x : v.adicCompletion F) := by
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hE := ValuativeRel.isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (uniformizer (v.adicCompletion F))
  have hpu : valuation (v.adicCompletion F) p = uniformizer (v.adicCompletion F) := by
    refine le_antisymm (le_uniformizer_iff.2 (hE.lt_one_iff_lt_one.2 ?_)) ?_
    · rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    · have h1 : Valued.v y < 1 := hE.lt_one_iff_lt_one.1 (hy ▸ uniformizer_lt_one)
      rw [← hy, hE.le_iff_le, hp]
      rcases eq_or_ne (Valued.v y) 0 with h0 | h0
      · rw [h0]; exact zero_le
      · rw [← WithZero.exp_log h0] at h1 ⊢
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
        rw [WithZero.exp_le_exp]; omega
  set P : (v.adicCompletion F)ˣ := Units.mk0 p hp0
  have hP1 : GlobalTheory.SmGL.ord (v.adicCompletion F) P = 1 := GlobalTheory.SmGL.ord_eq_one hpu
  set m := Formalism.UG.ordL (x : v.adicCompletion F)
  set U : (v.adicCompletion F)ˣ := x * P ^ (-m)
  have hU : Valued.v (U : v.adicCompletion F) = 1 := by
    simp only [U, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, P, Units.val_mk0, hp]
    rw [valued_eq_exp_ordL v x, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [m]
  have hU' : valuation (v.adicCompletion F) (U : v.adicCompletion F) = 1 := by
    apply le_antisymm
    · rw [← map_one (valuation (v.adicCompletion F)), hE.le_iff_le, hU, map_one]
    · rw [← map_one (valuation (v.adicCompletion F)), hE.le_iff_le, hU, map_one]
  have hU0 : GlobalTheory.SmGL.ord (v.adicCompletion F) U = 0 := GlobalTheory.SmGL.ord_eq_zero hU'
  let o : (v.adicCompletion F)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun z => .ofAdd (GlobalTheory.SmGL.ord (v.adicCompletion F) z)) fun a b => by
      rw [GlobalTheory.SmGL.ord_mul, ofAdd_add]
  have hx : x = U * P ^ m := by simp [U]
  have : o x = o U * o P ^ m := by rw [hx, map_mul, map_zpow]
  have e2 : GlobalTheory.SmGL.ord (v.adicCompletion F) x = GlobalTheory.SmGL.ord (v.adicCompletion F) U +
      m * GlobalTheory.SmGL.ord (v.adicCompletion F) P := by
    have := congrArg Multiplicative.toAdd this
    simpa [o, mul_comm] using this
  rw [e2, hU0, hP1]; ring

end GlobalTheory.BCT.InertChar

open GlobalTheory.BCT.InertChar in
theorem GlobalTheory.BCT.inertChar_muLocK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w : Pl E, ¬ IsSplitAt w → ∀ k : Eˣ, ((μ.locK w k : ℂˣ) : ℂ) = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (k : E)) := by
  intro E _ _ _ μ e hμ w hw k
  have h := hμ.2.2.1 w hw
  show ((μ.loc w (atFin w k) : ℂˣ) : ℂ) = _
  rw [h, GlobalTheory.SmGL.unrChar_apply, ord_eq_ordL]
  push_cast
  rfl
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GoodInt

variable {E : Type} [Field E] [NumberField E]

theorem eventually_int (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E := by
  filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 E) x).compl_mem_cofinite] with w hw
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  rw [h2]
  exact not_lt.mp hw

theorem mem_GLint {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_mem_KGL {n : ℕ} (g : GL (Fin n) E) : ∀ᶠ w : Pl E in cofinite,
    GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have h : ∀ g : GL (Fin n) E, ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (g.val i j) ∈ w.adicCompletionIntegers E := fun g => by
    simp only [Filter.eventually_all]; exact fun i j => eventually_int _
  filter_upwards [h g, h g⁻¹] with w a b
  exact mem_GLint _ _ a (by rw [← map_inv]; exact b)

theorem locPt_mem_KL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n,
    γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, locPt w γ ∈ KL n w := by
  intro E _ _ _ _ n γ _
  filter_upwards [eventually_mem_KGL (E := E) γ.1] with w hw
  unfold locPt toSub
  split_ifs with h
  · exact hw
  · exact one_mem _

end GlobalTheory.BCT.GoodInt
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.LocAE

theorem mem_GLint_of_entries_inv {L : Type} [Field L] {k : ℕ} (O : Subring L) (g : GL (Fin k) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin k) O := by
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_mem_KL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ x : finU (E := E) (n := n),
    ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  intro E _ _ _ _ n x
  have h : ∀ y : FiniteAdeleRing (𝓞 E) E, ∀ᶠ w in cofinite, pLoc E w y ∈ Formalism.UG.Ov E w := fun y => y.2
  have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E (((x : UA E n) : GA E n).val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E ((((x : UA E n) : GA E n))⁻¹.val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  filter_upwards [h1, h2] with w a b
  have hK : cLoc w (x : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    refine mem_GLint_of_entries_inv _ _ (fun i j => a i j) (fun i j => ?_)
    rw [← map_inv]
    exact b i j
  unfold toSub
  split_ifs with hU
  · exact Subgroup.mem_subgroupOf.2 hK
  · exact one_mem _

end GlobalTheory.BCT.LocAE
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def kernSum (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) : ℂ :=
  (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))),
      ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) :
        ℂ))⁻¹ *
      ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * chW lam γ.1.val.charpoly

def clsSum (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (γ : UE E n) : ℂ :=
  (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt γ) : Subgroup (finU (E := E) (n := n))) : Set (finU (E := E) (n := n)))
        (globLev S K' : Set (finU (E := E) (n := n))),
      ((Nat.card ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt γ)) ⊓
          (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) : ℂ))⁻¹ *
        globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q)

end GlobalTheory.BCT
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SuppFin

theorem norm_emb_entry_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n)
    (τ : E →+* ℂ) (i j : Fin n) : ‖τ (γ.1.val i j)‖ ≤ 1 := by
  have h : (γ.1.val.map (IsCMField.complexConj E).toRingEquiv.toRingHom)ᵀ * 1 * γ.1.val = 1 := γ.2
  have hjj := congrFun (congrFun h j) j
  simp only [Matrix.mul_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.one_apply_eq] at hjj
  have h2 : ∑ k, ((‖τ (γ.1.val k j)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    have := congrArg τ hjj

    rw [map_sum, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    change _ = τ ((IsCMField.complexConj E) (γ.1.val k j)) * _
    rw [IsCMField.complexEmbedding_complexConj, Complex.conj_mul']
    push_cast; rfl
  have h3 : ∑ k, ‖τ (γ.1.val k j)‖ ^ 2 = 1 := by exact_mod_cast h2
  have h4 : ‖τ (γ.1.val i j)‖ ^ 2 ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum (f := fun k => ‖τ (γ.1.val k j)‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (τ (γ.1.val i j))]

end GlobalTheory.BCT.SuppFin
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPart

theorem norm_emb_entry_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n)
    (τ : E →+* ℂ) (i j : Fin n) : ‖τ ((γ : GL (Fin n) E).val i j)‖ ≤ 1 := by
  set M : Matrix (Fin n) (Fin n) E := (γ : GL (Fin n) E).val with hM
  have h : Formalism.UG.cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * 1 * M = 1 := γ.2
  rw [Matrix.mul_one] at h
  have hjj : ∑ k, IsCMField.complexConj E (M k j) * M k j = 1 := by
    have := congrFun₂ h j j
    simpa [Formalism.UG.cT, Matrix.mul_apply] using this
  have hτ : ∑ k, ((Complex.normSq (τ (M k j)) : ℝ) : ℂ) = 1 := by
    have := congrArg τ hjj

    rw [map_sum, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, IsCMField.complexEmbedding_complexConj, Complex.normSq_eq_conj_mul_self]
  have hR : ∑ k, Complex.normSq (τ (M k j)) = 1 := by exact_mod_cast hτ
  have hle : Complex.normSq (τ (M i j)) ≤ 1 := by
    rw [← hR]
    exact Finset.single_le_sum (f := fun k => Complex.normSq (τ (M k j))) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i)
  have hsq : ‖τ (M i j)‖ ^ 2 ≤ 1 := by rw [Complex.sq_norm]; exact hle
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

end GlobalTheory.BCT.FinPart
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

def cavg {G : Type} [Group G] (K : Subgroup G) (f : G → ℂ) (x : G) : ℂ :=
  avg fun k : K => f ((k : G)⁻¹ * x * k)

def adL {k : Type} [Field k] {a b : ℕ} (A : GL (Fin a) k) (B : Matrix (Fin b) (Fin b) k) :
    Matrix (Fin a) (Fin b) k →ₗ[k] Matrix (Fin a) (Fin b) k where
  toFun X := X - (A⁻¹ : GL (Fin a) k).val * X * B
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

variable {E : Type} [Field E] [NumberField E]

def parP (a n : ℕ) (w : Pl E) : Subgroup (GLw n w) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular fun i : Fin n => decide (a ≤ (i : ℕ))}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    exact hg.mul hh
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one]
    exact Matrix.blockTriangular_one
  inv_mem' {g} hg := by
    let := g.invertible
    simp only [Set.mem_ofPred_eq, Matrix.coe_units_inv] at *
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def orbN {n a b : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  hint (intMat a b w) fun X => cavg (GlobalTheory.LFun.KGL w (n := n)) f
    ((blk h w 1 (Multiplicative.toAdd X))⁻¹ * blk h w m 0 * blk h w 1 (Multiplicative.toAdd X))

end GlobalTheory.LeviDesc
end
end

section

namespace GlobalTheory.TraceOnInjectiveMap

theorem trOn_map_of_injective {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (j : X →ₗ[ℂ] V) (hj : Function.Injective j) (M : Submodule ℂ X) (L' : X →ₗ[ℂ] X) (L : V →ₗ[ℂ] V)
    (hL : ∀ x ∈ M, L (j x) = j (L' x)) :
    GlobalTheory.BCT.trOn (Submodule.map j M) L = GlobalTheory.BCT.trOn M L' := by
  have hpres : (∀ v ∈ Submodule.map j M, L v ∈ Submodule.map j M) ↔ ∀ x ∈ M, L' x ∈ M := by
    constructor
    · intro h x hx
      obtain ⟨y, hy, hyx⟩ := h (j x) ⟨x, hx, rfl⟩
      rw [hL x hx] at hyx
      exact hj hyx ▸ hy
    · rintro h _ ⟨x, hx, rfl⟩
      exact ⟨L' x, h x hx, (hL x hx).symm⟩
  unfold GlobalTheory.BCT.trOn
  by_cases h' : ∀ x ∈ M, L' x ∈ M
  · rw [dite_eq_left (hpres.2 h'), dite_eq_left h']
    let e : M ≃ₗ[ℂ] Submodule.map j M := Submodule.equivMapOfInjective j hj M
    have hc : L.restrict (hpres.2 h') = e.conj (L'.restrict h') := by
      apply LinearMap.ext
      intro w
      obtain ⟨x, rfl⟩ := e.surjective w
      apply Subtype.ext
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.coe_restrict_apply, e,
        Submodule.coe_equivMapOfInjective_apply]
      exact hL x x.2
    rw [hc, LinearMap.trace_conj']
  · rw [dite_eq_right (mt hpres.1 h'), dite_eq_right h']

end GlobalTheory.TraceOnInjectiveMap
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
  Formalism.L2.Host GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev blkEq {a b n : ℕ} (h : a + b = n) : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)

def dgMat {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) (A : Matrix (Fin a) (Fin a) R)
    (D : Matrix (Fin b) (Fin b) R) : Matrix (Fin n) (Fin n) R :=
  reindex (blkEq h) (blkEq h) (fromBlocks A 0 0 D)

theorem dgMat_mul {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) (A A' : Matrix (Fin a) (Fin a) R)
    (D D' : Matrix (Fin b) (Fin b) R) : dgMat h A D * dgMat h A' D' = dgMat h (A * A') (D * D') := by
  simp only [dgMat, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem dgMat_one {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) :
    dgMat h (1 : Matrix (Fin a) (Fin a) R) (1 : Matrix (Fin b) (Fin b) R) = 1 := by
  rw [dgMat, fromBlocks_one, reindex_apply, submatrix_one_equiv]

def dgM {a b n : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* GLw n w where
  toFun k := ⟨dgMat h k.1.val k.2.val, dgMat h (k.1⁻¹).val (k.2⁻¹).val,
    by rw [dgMat_mul, Units.mul_inv, Units.mul_inv, dgMat_one],
    by rw [dgMat_mul, Units.inv_mul, Units.inv_mul, dgMat_one]⟩
  map_one' := Units.ext (by simp [dgMat_one])
  map_mul' x y := Units.ext (by simp [dgMat_mul])

theorem dgM_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w) :
    (dgM h w k).val = dgMat h k.1.val k.2.val := rfl

def lev₁ {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) :
    Subgroup (GLw a w) :=
  GlobalTheory.LFun.KGL w (n := a) ⊓ N.comap ((dgM h w).comp (MonoidHom.inl _ _)) ⊓ μ.ker.comap GeneralLinearGroup.det

def lev₂ {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) :
    Subgroup (GLw b w) :=
  GlobalTheory.LFun.KGL w (n := b) ⊓ N.comap ((dgM h w).comp (MonoidHom.inr _ _)) ⊓ μ.ker.comap GeneralLinearGroup.det

theorem blk_val {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = reindex (blkEq h) (blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  have hu : IsUnit (reindex (blkEq h) (blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
    rw [isUnit_iff_isUnit_det, det_reindex_self, det_fromBlocks_zero₂₁]
    exact (m.1.isUnit.map detMonoidHom).mul (m.2.isUnit.map detMonoidHom)
  unfold blk
  simp only
  rw [dite_eq_left hu]
  rfl

end GlobalTheory.BCT.CtLevel
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem cLoc_fin_continuous {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) :
    Continuous (fun x : finU (E := E) (n := n) => cLoc w (x : UA E n)) := by
  have hf : Continuous ((pLoc E w).comp (pFin E)) := by
    show Continuous (fun x => pLoc E w (pFin E x))
    exact (RestrictedProduct.continuous_eval w).comp continuous_snd
  have hm : Continuous (((pLoc E w).comp (pFin E)).mapMatrix : Matrix (Fin n) (Fin n) (Ad E) →+* _) :=
    continuous_id.matrix_map hf
  exact (Continuous.units_map _ hm).comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_toSub {X G : Type} [TopologicalSpace X] [Group G] [TopologicalSpace G] (H : Subgroup G) {f : X → G}
    (hf : Continuous f) (hH : ∀ x, f x ∈ H) : Continuous (fun x => toSub H (f x)) := by
  have : (fun x => toSub H (f x)) = fun x => (⟨f x, hH x⟩ : H) := by
    funext x; simp [toSub, hH x]
  rw [this]
  exact hf.subtype_mk _

theorem toSub_cLoc_continuous_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E)
    (hmem : ∀ x : finU (E := E) (n := n), cLoc w (x : UA E n) ∈ UL n w) :
    Continuous (fun x : finU (E := E) (n := n) => toSub (UL n w) (cLoc w (x : UA E n))) :=
  continuous_toSub _ (cLoc_fin_continuous w) hmem

theorem toSub_cLoc_fin_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ w : Pl E, Continuous (fun x : finU (E := E) (n := n) => toSub (UL n w) (cLoc w (x : UA E n))) := by
  intro E _ _ _ hE n w
  exact toSub_cLoc_continuous_of_mem w (GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hE n w)

end GlobalTheory.BCT
end
end
