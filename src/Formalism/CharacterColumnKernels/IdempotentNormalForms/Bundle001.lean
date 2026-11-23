module

public import Formalism.CharacterColumnKernels.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

open Module

noncomputable section

namespace Formalism.NG

theorem burnside : StatBurnside := by
  intro k A V _ _ _ _ _ _ _ _ hS hsc f
  classical
  have := hS
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := hsc φ
        simp only [Module.End.smul_def, hc, RingHom.id_apply, f.map_smul] }
  obtain ⟨a, ha⟩ := jacobson_density F (Finset.univ.image (Module.finBasis k V))
  refine ⟨a, (Module.finBasis k V).ext fun i => ?_⟩
  have := ha (Module.finBasis k V i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  simpa [F] using this.symm

section RankMod

variable {O : Type*} [CommRing O] {r : Type} [Fintype r] [DecidableEq r]

private theorem free_of_isCompl [IsLocalRing O] (p q : Submodule O (r → O)) (h : IsCompl p q) :
    Module.Free O p ∧ Module.Finite O p := by
  have hproj : Module.Projective O p :=
    Module.Projective.of_split p.subtype (Submodule.linearProjOfIsCompl p q h)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left h x)
  have hfin : Module.Finite O p :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl p q h) (fun x => ⟨x, Submodule.linearProjOfIsCompl_apply_left h x⟩)
  exact ⟨Module.free_of_flat_of_isLocalRing, hfin⟩

private theorem idem_normal_form [IsLocalRing O] (e : Matrix r r O) (he : IsIdempotentElem e) :
    ∃ (P Q : Matrix r r O) (d : r → O), (∀ j, d j = 0 ∨ d j = 1) ∧ P * Q = 1 ∧ Q * P = 1 ∧
      e = P * Matrix.diagonal d * Q := by
  classical
  let f : (r → O) →ₗ[O] (r → O) := Matrix.toLin' e
  have hf : f * f = f := by
    show (Matrix.toLin' e).comp (Matrix.toLin' e) = Matrix.toLin' e
    rw [← Matrix.toLin'_mul, he.eq]
  have hc : IsCompl (LinearMap.range f) (LinearMap.ker f) :=
    LinearMap.IsIdempotentElem.isCompl hf
  obtain ⟨hpF, hpFin⟩ := free_of_isCompl _ _ hc
  obtain ⟨hqF, hqFin⟩ := free_of_isCompl _ _ hc.symm
  let bp := Module.Free.chooseBasis O (LinearMap.range f)
  let bq := Module.Free.chooseBasis O (LinearMap.ker f)
  let b0 := (bp.prod bq).map (Submodule.prodEquivOfIsCompl _ _ hc)
  let σ := b0.indexEquiv (Pi.basisFun O r)
  let b := b0.reindex σ
  have hfb : ∀ j, f (b j) = (if (σ.symm j).isLeft then (1 : O) else 0) • b j := by
    intro j
    rw [Basis.reindex_apply]
    rcases σ.symm j with k | k
    · have hk : (b0 (Sum.inl k) : r → O) = (bp k : r → O) := by
        simp [b0, Basis.map_apply, Basis.prod_apply]
      simp only [Sum.isLeft_inl, if_true, one_smul, hk]
      obtain ⟨y, hy⟩ := (bp k).2
      rw [← hy]
      show (f * f) y = f y
      rw [hf]
    · have hk : (b0 (Sum.inr k) : r → O) = (bq k : r → O) := by
        simp [b0, Basis.map_apply, Basis.prod_apply]
      simp only [Sum.isLeft_inr, Bool.false_eq_true, if_false, zero_smul, hk]
      exact LinearMap.mem_ker.mp (bq k).2
  have hdiag : LinearMap.toMatrix b b f =
      Matrix.diagonal fun i => if (σ.symm i).isLeft then (1 : O) else 0 := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply, hfb, map_smul, Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  refine ⟨(Pi.basisFun O r).toMatrix b, b.toMatrix (Pi.basisFun O r),
    fun i => if (σ.symm i).isLeft then (1 : O) else 0,
    fun j => by by_cases h : (σ.symm j).isLeft <;> simp [h],
    Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩
  rw [← hdiag, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix,
    LinearMap.toMatrix_eq_toMatrix']
  exact (LinearMap.toMatrix'_toLin' e).symm

private theorem rank_map_conj {F : Type*} [Field F] (f : O →+* F) (P Q : Matrix r r O) (d : r → O)
    (hd : ∀ j, d j = 0 ∨ d j = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ((P * Matrix.diagonal d * Q).map f).rank = Nat.card {j // d j = 1} := by
  classical
  have hm1 : P.map f * Q.map f = 1 := by
    rw [← Matrix.map_mul, hPQ]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  have hm2 : Q.map f * P.map f = 1 := by
    rw [← Matrix.map_mul, hQP]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  rw [Matrix.map_mul, Matrix.map_mul,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hm2),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hm1),
    Matrix.diagonal_map (map_zero f), Matrix.rank_diagonal, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro j
  constructor
  · intro h
    rcases hd j with h0 | h1
    · exact (h (by rw [h0, map_zero])).elim
    · exact h1
  · intro h1
    rw [h1, map_one]
    exact one_ne_zero

end RankMod

end Formalism.NG
end
end

section

open Finset

noncomputable section

namespace Formalism.NG

section HomAux

variable {R O M : Type*} [Ring R] [CommRing O] [AddCommGroup M] [Module R M] [Module O M]
  [SMulCommClass R O M] {m g : Type} [Fintype m] [Fintype g] [DecidableEq g]

theorem relMap_apply' (Θ : Matrix m g R) (v : g → M) (i : m) :
    relMap O M Θ v i = ∑ j, Θ i j • v j := rfl

def combo (v : g → M) : (g → R) →ₗ[R] M where
  toFun w := ∑ j, w j • v j
  map_add' w w' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r w := by simp [mul_smul, Finset.smul_sum]

theorem combo_apply (v : g → M) (w : g → R) : combo v w = ∑ j, w j • v j := rfl

theorem combo_single (v : g → M) (j : g) (x : R) : combo v (Pi.single j x) = x • v j := by
  rw [combo_apply]
  simp [Pi.single_apply, ite_smul]

theorem single_eq_smul (j : g) (x : R) : (Pi.single j x : g → R) = x • Pi.single j 1 := by
  ext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem sum_row (Θ : Matrix m g R) (i : m) :
    ∑ j, Θ i j • (Pi.single j (1 : R) : g → R) = Θ i := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

def toVec (Θ : Matrix m g R) (φ : Coker Θ →ₗ[R] M) : g → M :=
  fun j => φ ((relSpan Θ).mkQ (Pi.single j (1 : R)))

theorem toVec_mem (Θ : Matrix m g R) (φ : Coker Θ →ₗ[R] M) :
    toVec Θ φ ∈ LinearMap.ker (relMap O M Θ) := by
  rw [LinearMap.mem_ker]
  funext i
  rw [relMap_apply', Pi.zero_apply]
  simp only [toVec]
  have h : ∑ j, Θ i j • φ ((relSpan Θ).mkQ (Pi.single j (1 : R))) =
      φ ((relSpan Θ).mkQ (∑ j, Θ i j • (Pi.single j (1 : R) : g → R))) := by

    simp [map_sum, map_smul]
  rw [h, sum_row]
  have hmem : Θ i ∈ relSpan Θ := Submodule.subset_span ⟨i, rfl⟩
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hmem, map_zero]

def ofVec (Θ : Matrix m g R) (v : LinearMap.ker (relMap O M Θ)) : Coker Θ →ₗ[R] M :=
  (relSpan Θ).liftQ (combo (v : g → M)) (by
    rw [relSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, combo_apply]
    have h := congrFun (LinearMap.mem_ker.mp v.2) i
    rw [relMap_apply'] at h
    exact h)

theorem ofVec_mk (Θ : Matrix m g R) (v : LinearMap.ker (relMap O M Θ)) (w : g → R) :
    ofVec Θ v (Submodule.Quotient.mk w) = combo (v : g → M) w := rfl

def homEquiv (Θ : Matrix m g R) : (Coker Θ →ₗ[R] M) ≃ₗ[O] LinearMap.ker (relMap O M Θ) where
  toFun φ := ⟨toVec Θ φ, toVec_mem Θ φ⟩
  invFun v := ofVec Θ v
  map_add' φ ψ := by
    apply Subtype.ext; funext j; simp [toVec]
  map_smul' c φ := by
    apply Subtype.ext; funext j; simp [toVec]
  left_inv φ := by
    apply Submodule.linearMap_qext
    apply LinearMap.pi_ext
    intro j x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, ofVec_mk, combo_single,
      single_eq_smul j x, Submodule.Quotient.mk_smul, map_smul]
    rfl
  right_inv v := by
    apply Subtype.ext; funext j
    show ofVec Θ v (Submodule.Quotient.mk (Pi.single j (1 : R))) = (v : g → M) j
    rw [ofVec_mk, combo_single, one_smul]

end HomAux

end Formalism.NG
end
end

section

open Finset

namespace Formalism.NG

private lemma padicValInt_eq_emultiplicity (l : ℕ) [hl : Fact l.Prime] {z : ℤ} (hz : z ≠ 0) :
    (padicValInt l z : ℕ∞) = emultiplicity (l : ℤ) z := by
  have hz' : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  change (multiplicity l z.natAbs : ℕ∞) = emultiplicity (l : ℤ) z
  rw [multiplicity_eq_emultiplicity hz',
    ← Int.natCast_emultiplicity, Int.natCast_natAbs]
  rcases abs_choice z with h | h
  · rw [h]
  · rw [h, emultiplicity_neg]

private lemma padicValInt_pow_sub_one_eq_add (l : ℕ) [hl : Fact l.Prime] (s₀ : ℕ) (hs : 1 ≤ s₀) (hs2 : l = 2 → 2 ≤ s₀)
    (x : ℤ) (hx1 : (l : ℤ) ^ s₀ ∣ x - 1) (hx2 : ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1)
    (n : ℕ) (hn0 : n ≠ 0) :
    x ^ n - 1 ≠ 0 ∧ padicValInt l (x ^ n - 1) = s₀ + padicValNat l n := by
  have hlp := hl.out
  have hE1 : emultiplicity (l : ℤ) (x - 1) = s₀ := emultiplicity_eq_coe.mpr ⟨hx1, hx2⟩
  have hdvd : (l : ℤ) ∣ x - 1 := (dvd_pow_self (l : ℤ) (by omega)).trans hx1
  have hlx : ¬ (l : ℤ) ∣ x := by
    intro h
    have h1 : (l : ℤ) ∣ 1 := by have := dvd_sub h hdvd; simpa using this
    exact (Nat.prime_iff_prime_int.mp hlp).not_dvd_one h1
  have hE : emultiplicity (l : ℤ) (x ^ n - 1) = (s₀ : ℕ∞) + emultiplicity l n := by
    rcases hlp.eq_two_or_odd' with h2 | hodd
    · subst h2
      have h4 : (4 : ℤ) ∣ x - 1 := by
        have := (pow_dvd_pow ((2 : ℕ) : ℤ) (hs2 rfl)).trans hx1
        norm_num at this
        exact this
      push_cast at hlx hE1 ⊢
      have := Int.two_pow_sub_pow' n h4 hlx
      rw [one_pow] at this
      have hc := Int.natCast_emultiplicity 2 n
      push_cast at hc
      rw [this, hE1, hc]
    · have := Int.emultiplicity_pow_sub_pow hlp hodd (y := 1) hdvd hlx n
      rw [one_pow] at this
      rw [this, hE1]
  have hfin : emultiplicity (l : ℤ) (x ^ n - 1) = ((s₀ + padicValNat l n : ℕ) : ℕ∞) := by
    rw [hE, ← multiplicity_eq_emultiplicity hn0, Nat.padicValNat_def]
    norm_cast
  have hne : x ^ n - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at hfin
    exact ENat.top_ne_coe _ hfin
  refine ⟨hne, ?_⟩
  have := padicValInt_eq_emultiplicity l hne
  rw [hfin] at this
  exact_mod_cast this

theorem character_column_kernel_length_bound : characterColumnKernelLengthBound := by
  intro l hl s₀ hs hs2 x hx1 hx2 a b hab
  have hlp := Nat.prime_iff_prime_int.mp hl.out
  obtain ⟨hne, hv⟩ := padicValInt_pow_sub_one_eq_add l s₀ hs hs2 x hx1 hx2 (b - a) (by omega)
  have hdvd : (l : ℤ) ∣ x - 1 := (dvd_pow_self (l : ℤ) (by omega)).trans hx1
  have hlx : ¬ (l : ℤ) ∣ x ^ a := by
    intro h
    have h' : (l : ℤ) ∣ x := hlp.dvd_of_dvd_pow h
    have h1 : (l : ℤ) ∣ 1 := by have := dvd_sub h' hdvd; simpa using this
    exact hlp.not_dvd_one h1
  have hxa : x ^ a ≠ 0 := fun h ↦ hlx (h ▸ dvd_zero _)
  have e : x ^ b - x ^ a = x ^ a * (x ^ (b - a) - 1) := by
    rw [mul_sub, ← pow_add, Nat.add_sub_of_le hab.le, mul_one]
  rw [e, padicValInt.mul hxa hne, padicValInt.eq_zero_of_not_dvd hlx, zero_add, hv]

end Formalism.NG
end
