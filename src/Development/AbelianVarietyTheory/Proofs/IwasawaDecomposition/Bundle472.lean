module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfNormal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle460
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem ptOf_std_entries_intAtA : ∀ {B : Base} (n : ℕ) (g : GA B n) (p : DecoF B.fields.E n ∅ ∅ ∅), PtOf g p → p.deco.1.N = stdLat B.fields.E n → ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin n), IntAtA (F := B.host.F) P ((g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) ∧ IntAtA (F := B.host.F) P (((g⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) := by
  intro B n g p hp hN P r s
  have hlat := hp.lat
  rw [hN] at hlat
  have hint : ∀ x : Fin n → AfE B.host.F B.host.E, x ∈ Formalism.L2.Herm.hatL (Formalism.L2.Col.stdLat B.host.E n) ↔ ∀ i, x i ∈ Formalism.L2.Herm.intAf B.host.F B.host.E := by
    intro x
    exact mem_latS_std x
  have hone : ∀ a : AfE B.host.F B.host.E, a ∈ Formalism.L2.Herm.intAf B.host.F B.host.E → IntAtA (F := B.host.F) P a := by
    intro a ha
    refine ⟨1, ?_, ?_⟩
    · exact P.asIdeal.ne_top_iff_one.mp P.isPrime.ne_top
    · simpa using ha
  have he : ∀ j : Fin n, (Pi.single j 1 : Fin n → AfE B.host.F B.host.E) ∈ Formalism.L2.Herm.hatL (Formalism.L2.Col.stdLat B.host.E n) := by
    intro j
    rw [hint]
    intro i
    by_cases h : i = j
    · subst h; simp [one_mem]
    · simp [Pi.single_apply, h, zero_mem]
  constructor
  · apply hone
    have hx : (g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) *ᵥ Pi.single s 1 ∈ Formalism.L2.Herm.hatL (Formalism.L2.Col.stdLat B.host.E n) := by
      rw [hlat]
      rw [Matrix.mulVec_mulVec]
      have h1 : ((g⁻¹ : GL (Fin n) (AfE B.host.F B.host.E)) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) * (g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [h1, Matrix.one_mulVec]
      exact he s
    have := (hint _).1 hx r
    simpa [Matrix.mulVec_single] using this
  · apply hone
    have hx := (hlat (Pi.single s 1)).1 (he s)
    have := (hint _).1 hx r
    simpa [Matrix.mulVec_single] using this

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdSupport

theorem adAt_entry_eq_one_of_not_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
    (hz : ∀ v', v' ≠ v → bc (prV (E := E) v') z = 1) (P : HeightOneSpectrum (𝓞 E)) (hP : ¬ Formalism.L2.Col.IsOver v P)
    (r s : Fin n) :
    adAt F P ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) =
      (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
  have hne : P.under (𝓞 F) ≠ v := by
    intro h
    apply hP
    rw [← h]
    rfl
  have h2 := congrArg (fun g : GL (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F) =>
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F)) r s) (hz _ hne)
  have h3 : prV (E := E) (P.under (𝓞 F)) ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) =
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F)) r s := h2
  have h4 : prV (E := E) (P.under (𝓞 F)) ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) = 0 := by
    rw [map_sub, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h5 := ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E (P.under (𝓞 F)) _).1.1 h4) P rfl
  rw [map_sub, sub_eq_zero] at h5
  rw [h5, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.Mem.Col2.AdSupport
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isAdIso_eq_afIso (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) (hι : GlobalTheory.TwU.IsAdIso ι) (x : AfE F E) : ι x = afIso F E x := by
  have key : ∀ P : HeightOneSpectrum (𝓞 E), ι x P = afIso F E x P := by
    intro P
    have ev : ∀ a b : FiniteAdeleRing (𝓞 E) E, (a + b) P = a P + b P := fun _ _ => rfl
    have evm : ∀ a b : FiniteAdeleRing (𝓞 E) E, (a * b) P = a P * b P := fun _ _ => rfl
    have evn : ∀ n : ℕ, ((n : FiniteAdeleRing (𝓞 E) E)) P = (n : P.adicCompletion E) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Nat.cast_succ, ev, ih, Nat.cast_succ]; rfl
    rw [← sub_eq_zero]
    by_contra hne
    set d := ι x P - afIso F E x P with hd
    have hv : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).2 hne
    obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := F) (E := E) x {P} hv
    have hNP := hN P (Finset.mem_singleton_self P)
    have h1 : ι (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y) = afIso F E (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y) := by
      show ι (y ⊗ₜ[F] 1) = afIso F E (y ⊗ₜ[F] 1)
      rw [hι.1, afIso_tmul_one]
    have hd2 : d = (N : P.adicCompletion E) * (ι r P - afIso F E r P) := by
      rw [hd, e, map_add (f := _), map_add (f := _), h1, map_mul, map_mul, map_natCast, map_natCast]
      rw [ev, ev, evm, evm, evn]
      ring
    have hr1 : Valued.v (ι r P) ≤ 1 := (hι.2 r).1 hr P
    have hr2 : Valued.v (afIso F E r P) ≤ 1 := (mem_rInt_iff F E r).1 hr P
    have hsub : Valued.v (ι r P - afIso F E r P) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le hr1 hr2)
    have hle : Valued.v d ≤ Valued.v (N : P.adicCompletion E) := by
      rw [hd2, map_mul]
      exact mul_le_of_le_one_right' hsub
    exact lt_irrefl _ (hle.trans_lt hNP)
  exact Subtype.ext (funext key)

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongMove

open GlobalTheory.TwU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

theorem intAtA_sum {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (h : ∀ i ∈ s, IntAtA (F := F) P (f i)) : IntAtA (F := F) P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAtA_int (F := F) (P := P) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAtA_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intAtA_one_apply (a b : Fin N) :
    IntAtA (F := F) P ((1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b) := by
  rw [Matrix.one_apply]
  split_ifs
  · simpa using intAtA_int (F := F) (P := P) 1
  · simpa using intAtA_int (F := F) (P := P) 0

theorem qpow_facts (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    iA F E (((qOf P : ℕ) : E) ^ n) * iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ = 1 ∧
      IntAtA (F := F) P (iA F E (((qOf P : ℕ) : E) ^ n)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  refine ⟨by rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one], ?_⟩
  have := intAtA_int (F := F) (P := P) (((qOf P : ℕ) : 𝓞 E) ^ n)
  simpa using this

theorem intAtA_of_congAt (n : ℕ) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P n k) (a b : Fin N) :
    IntAtA (F := F) P ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b) := by
  obtain ⟨hdc, hd⟩ := qpow_facts (F := F) P n
  have e : (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b =
      (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b +
        iA F E (((qOf P : ℕ) : E) ^ n) * (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ *
          ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) := by
    rw [← mul_assoc, hdc, one_mul, Matrix.sub_apply]; ring
  rw [e]
  exact intAtA_add (intAtA_one_apply a b) (intAtA_mul hd (h a b))

theorem congAt_mul (n : ℕ) {k k' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P n k) (h' : CongAt P n k') :
    CongAt P n (k * k') := by
  intro a b
  have hk' := intAtA_of_congAt n h'
  set K := (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  set K' := (k' : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  have e : ((k * k' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
      (K - 1) * K' + (K' - 1) := by
    rw [Units.val_mul, Matrix.sub_mul, Matrix.one_mul]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum]
  refine intAtA_add (intAtA_sum _ _ fun j _ => ?_) (h' a b)
  rw [← mul_assoc]
  exact intAtA_mul (h a j) (hk' j b)

theorem congAt_conj (n : ℕ) {A B : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hA : CongAt P n A)
    (hB : ∀ r s, IntAtA (F := F) P ((B : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s))
    (hBi : ∀ r s, IntAtA (F := F) P (((B⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s)) :
    CongAt P n (B⁻¹ * A * B) := by
  intro a b
  set Bm := (B : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  set Bi := ((B⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  set Am := (A : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  have hBB : Bi * Bm = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e : ((B⁻¹ * A * B : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
      Bi * ((Am - 1) * Bm) := by
    rw [Units.val_mul, Units.val_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, ← hBB, Matrix.mul_assoc]
  rw [e, Matrix.mul_apply, Finset.mul_sum]
  refine intAtA_sum _ _ fun j _ => ?_
  rw [Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
  refine intAtA_sum _ _ fun l _ => ?_
  have e2 : iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * (Bi a j * ((Am - 1) j l * Bm l b)) =
      Bi a j * (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * (Am - 1) j l) * Bm l b := by ring
  rw [e2]
  exact intAtA_mul (intAtA_mul (hBi a j) (hA j l)) (hB l b)

end GlobalTheory.CongMove

namespace GlobalTheory.CongMove

open GlobalTheory.TwU

theorem nearAt_conj_ratA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (κ x k : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (f g : GL (Fin N) E)
    (hk : ∀ r s, IntAtA (F := F) P ((k : Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s))
    (hki : ∀ r s, IntAtA (F := F) P (((k⁻¹ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) :
      Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s))
    (hm : ∀ r s, IntAtA (F := F) P (((k⁻¹ * x * k : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) :
      Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s))
    (hmi : ∀ r s, IntAtA (F := F) P ((((k⁻¹ * x * k)⁻¹ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) :
      Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s))
    (hκ : GlobalTheory.TwU.CongAt P n (κ⁻¹ * x)) (hg : GlobalTheory.TwU.NearAt P n (k⁻¹ * x * k) g)
    (he : GlobalTheory.TwU.CongAt P n (k⁻¹ * GlobalTheory.TwU.ratA F f)) (hei : GlobalTheory.TwU.CongAt P n ((GlobalTheory.TwU.ratA F f)⁻¹ * k)) :
    GlobalTheory.TwU.NearAt P n ((GlobalTheory.TwU.ratA F f)⁻¹ * κ * GlobalTheory.TwU.ratA F f) g := by
  unfold NearAt at hg ⊢
  set Fr := ratA F f
  set G := ratA F g
  set m := k⁻¹ * x * k
  have key : (Fr⁻¹ * κ * Fr)⁻¹ * G =
      (Fr⁻¹ * k) * (k⁻¹ * (κ⁻¹ * x) * k) * (m⁻¹ * (k⁻¹ * Fr) * m) * (m⁻¹ * G) := by
    simp only [m]
    group
  rw [key]
  refine congAt_mul n (congAt_mul n (congAt_mul n hei ?_) ?_) hg
  · have h := congAt_conj n hκ (B := k) hk hki
    simpa only [inv_inv] using h
  · have h := congAt_conj n he (B := m) hm hmi
    exact h

end GlobalTheory.CongMove
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift.GenZero

theorem exists_hasDerivAt_char (s : ℝ → ℂ) (hs : ∀ t t', s (t + t') = s t * s t') (h0 : s 0 = 1)
    (hc : ContinuousAt s 0) : ∃ m : ℂ, HasDerivAt s m 0 := by
  have hcont : Continuous s := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have e : s = fun t => s (t - t₀) * s t₀ := funext fun t => by rw [← hs, sub_add_cancel]
    rw [e]
    refine ContinuousAt.mul ?_ continuousAt_const
    exact ContinuousAt.comp (g := s) (f := fun t => t - t₀) (by simpa using hc) (by fun_prop)
  let g : ℝ → ℂ := fun x => ∫ y in (0 : ℝ)..x, s y
  have hg : ∀ x, HasDerivAt g (s x) x := fun x => (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  obtain ⟨ε, hε⟩ : ∃ ε, g ε ≠ 0 := by
    by_contra hn
    push Not at hn
    have h1 : HasDerivAt g 0 0 := by
      rw [show g = fun _ => 0 from funext hn]
      exact hasDerivAt_const _ _
    have := (hg 0).unique h1
    rw [h0] at this
    exact one_ne_zero this
  have e : s = fun t => (g (t + ε) - g t) / g ε := by
    funext t
    rw [eq_div_iff hε]
    have h1 : g (t + ε) - g t = ∫ y in t..(t + ε), s y :=
      intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    rw [h1]
    have h2 := intervalIntegral.integral_comp_add_left (a := 0) (b := ε) s t
    rw [add_zero] at h2
    rw [← h2]
    simp only [hs, g]
    exact (intervalIntegral.integral_const_mul _ _).symm
  have h3 : HasDerivAt (fun t => g (t + ε)) (s (0 + ε)) 0 := HasDerivAt.comp_add_const 0 ε (hg _)
  exact ⟨_, ((h3.sub (hg 0)).div_const (g ε)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun e t)⟩

theorem lie_of_path {ι : Type} [Fintype ι] [DecidableEq ι] (H X : Matrix ι ι ℂ) (m : ℝ → Matrix ι ι ℂ) (h0 : m 0 = 1)
    (hm : ∀ t, (m t)ᴴ * H * m t = H) (hX : ∀ k l, HasDerivAt (fun t => m t k l) (X k l) 0) :
    Xᴴ * H + H * X = 0 := by
  ext i j
  have h1 : HasDerivAt (fun t => ∑ l, (∑ k, star (m t k i) * H k l) * m t l j)
      (∑ l, ((∑ k, star (X k i) * H k l) * m 0 l j + (∑ k, star (m 0 k i) * H k l) * X l j)) 0 :=
    HasDerivAt.fun_sum fun l _ =>
      (HasDerivAt.fun_sum fun k _ => (hX k i).star.mul_const (H k l)).mul (hX l j)
  have e : (fun t => ∑ l, (∑ k, star (m t k i) * H k l) * m t l j) = fun _ => H i j := by
    funext t
    rw [← congrFun (congrFun (hm t) i) j]
    simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [e] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  have h3 : (Xᴴ * H * m 0 + (m 0)ᴴ * H * X) i j = 0 := by
    rw [← h2]
    simp only [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, Finset.sum_add_distrib]
  rwa [h0, conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at h3

open scoped Classical



open GlobalTheory.RealWeil in
theorem exists_generator : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∃ u : ℝ → GlobalTheory.RealWeil.BB ψ S T, (∀ t, ((u t).1 : WO S T → ℂ) = om (γ t) F.1) ∧ HasDerivAt u (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F) 0 := by
  intro D θ σ h ψ hψ S T om hw hc γ hγ hadd hinf X hX
  have hγ0 : γ 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_left_cancel (a := γ 0) (by rw [← this, mul_one])
  have hH := isHeis_rhoB (S := S) (T := T) h hψ
  have hL := lie_of_path (HM S T) X (fun t => mM θ S T (γ t)) (by simp only [hγ0, map_one])
    (fun t => mM_unitary h.inf _) hX
  obtain ⟨κ, _, c, p, q, hq, hn⟩ := GlobalTheory.Mem.Lift.Normal.normal_quad (Ix S T) (HM S T) X HM_herm HM_det hL
  obtain ⟨Ω, hΩ, -, hd⟩ := GlobalTheory.T.hasDerivAt_oscillatorAction_unitaryPath_quadratic (Ix S T) (HM S T) HM_herm HM_det (BB ψ S T) (rhoV hψ σ S T) hH
    (GA D S × GA D T) (mM θ S T) (mM_unitary h.inf)
  obtain ⟨lam, hlam⟩ := hd γ X hγ0 hX κ c p q hq
  have sm := sm_of_theta (S := S) (T := T) h hψ
  choose s hs1 hs using fun t => GlobalTheory.T.weakWeilRep_eq_unit_smul_oscillator_real_points D θ σ h ψ hψ S T om hw Ω hΩ (γ t).1 (hinf t).1 (γ t).2 (hinf t).2
  replace hs : ∀ t (F : BB ψ S T), IsThetaFunO ψ S T F.1 → om (γ t) F.1 = s t • ((Ω (γ t) F).1 : WO S T → ℂ) := hs
  obtain ⟨-, hsmul, hsm, hone, hmul, -⟩ := hΩ
  have cs : ∀ (a : ℂ) (G : BB ψ S T), ((a • G).1 : WO S T → ℂ) = a • (G.1 : WO S T → ℂ) := fun _ _ => rfl
  have hne : ∀ t, s t ≠ 0 := fun t e => by simpa [e] using hs1 t
  have hD : ∀ F : BB ψ S T, IsThetaFunO ψ S T F.1 →
      HasDerivAt (fun t => Ω (γ t) F) (nOp (rhoV hψ σ S T) (HM S T) X F + lam • F) 0 := fun F hF =>
    hn _ _ hH F (sm F hF) ▸ hlam F (sm F hF)
  by_cases hex : ∃ F₀ : BB ψ S T, IsThetaFunO ψ S T F₀.1 ∧ F₀ ≠ 0
  swap
  · push Not at hex
    refine ⟨lam, fun F hF => ⟨fun t => Ω (γ t) F, fun t => ?_, hD F hF⟩⟩
    have e : Ω (γ t) F = 0 := by
      have := hsmul (γ t) 0 F (sm F hF)
      rw [zero_smul, zero_smul] at this
      exact (congrArg (Ω (γ t)) (hex F hF)).trans this
    rw [hs t F hF]
    beta_reduce
    rw [e]
    exact (smul_zero _).symm
  obtain ⟨F₀, hF₀, hne₀⟩ := hex
  have hΩne : ∀ g, Ω g F₀ ≠ 0 := by
    intro g e
    have h1 := hmul g⁻¹ g F₀ (sm _ hF₀)
    have h2 := hsmul g⁻¹ 0 F₀ (sm _ hF₀)
    rw [zero_smul, zero_smul] at h2
    rw [inv_mul_cancel, hone _ (sm _ hF₀), e, h2] at h1
    exact hne₀ h1
  have hth : ∀ t, IsThetaFunO ψ S T (Ω (γ t) F₀).1 := by
    intro t
    have h1 := (thetaSub ψ S T).smul_mem (s t)⁻¹ (hw.om_pres (γ t) _ hF₀)
    rw [hs t F₀ hF₀, smul_smul, inv_mul_cancel₀ (hne t), one_smul] at h1
    exact h1
  have hms : ∀ t t', s (t + t') = s t * s t' := by
    intro t t'
    have h1 := hs (t + t') F₀ hF₀
    rw [hadd, map_mul, Module.End.mul_apply, hs t' F₀ hF₀, map_smul, hs t _ (hth t'), ← hmul _ _ _ (sm _ hF₀),
      smul_smul] at h1
    have h2 : (s t' * s t) • Ω (γ t * γ t') F₀ = s (t + t') • Ω (γ t * γ t') F₀ := QB_ext fun x => by
      rw [cs, cs, h1]
    rw [← smul_left_injective ℂ (hΩne _) h2, mul_comm]
  have hs0 : s 0 = 1 := by
    have := hms 0 0
    rw [add_zero] at this
    exact mul_left_cancel₀ (hne 0) (by rw [← this, mul_one])
  obtain ⟨w, hw₀⟩ : ∃ w, (F₀.1 : WO S T → ℂ) w ≠ 0 := by
    by_contra hn'
    push Not at hn'
    exact hne₀ (QB_ext hn')
  have hcs : ContinuousAt s 0 := by
    have h1 : ContinuousAt (fun t => ev _ _ w (Ω (γ t) F₀)) 0 :=
      (ev _ _ w).continuous.continuousAt.comp (hD F₀ hF₀).continuousAt
    have h2 : ev _ _ w (Ω (γ 0) F₀) ≠ 0 := by
      rw [hγ0, hone _ (sm _ hF₀), ev_apply]
      exact hw₀
    have h3 : ContinuousAt (fun t => om (γ t) F₀.1 w) 0 := ((hc _ hF₀ w).comp hγ).continuousAt
    refine (h3.div h1 h2).congr ?_
    filter_upwards [h1.eventually_ne h2] with t ht
    rw [Pi.div_apply, div_eq_iff ht, hs t F₀ hF₀, ev_apply]
    rfl
  obtain ⟨m, hm⟩ := exists_hasDerivAt_char s hms hs0 hcs
  refine ⟨lam + m, fun F hF => ⟨fun t => s t • Ω (γ t) F, fun t => (cs _ _).trans (hs t F hF).symm, ?_⟩⟩
  have h1 := hm.smul (hD F hF)
  rw [hs0, one_smul, hγ0, hone _ (sm _ hF)] at h1
  rw [add_smul, ← add_assoc]
  exact h1

end GlobalTheory.Mem.Lift.GenZero

end
end
