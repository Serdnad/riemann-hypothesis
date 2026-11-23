module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle004
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

def EvEx : Prop := ∀ (p : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] (T : AdT p E) (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal →
  ∃ ev : AfP p ⊗[ℚ] E →+* w.adicCompletion E, ∀ x, ev (T.Φ x) = pLoc E w x

def VecCoord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S), ∃ vec : ∀ w : Plc E, AfP p ⊗[ℚ] VQ S.D →+ (Fin n → w.adicCompletion E),
  (∀ v, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → vec w v = 0) → v = 0) ∧
  (∀ v, v ∈ LaHat S.D ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i, vec w v i ∈ w.adicCompletionIntegers E) ∧
  (∀ y : ∀ w : Plc E, Fin n → w.adicCompletion E, (∀ w i, y w i ∈ w.adicCompletionIntegers E) →
    ∃ v, ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → vec w v = y w) ∧
  (∀ (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∀ (y : Fin n → 𝓞 E) i, vec w (inAf S.D y) i = algebraMap (𝓞 E) _ (y i)) ∧
  (∀ (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∀ g v, vec w (S.L.actG (T.j g) v) =
    (GeneralLinearGroup.map (pLoc E w) T.a * comp w g * (GeneralLinearGroup.map (pLoc E w) T.a)⁻¹).val *ᵥ vec w v) ∧
  ∀ (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∀ (c : 𝓞 E) v,
    vec w (UpperTheory.Gal.Int.Geo.mulF S.D c v) = algebraMap (𝓞 E) (w.adicCompletion E) c • vec w v

def StdForm2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S), ∃ (B : DForm S.G) (x : (AfP p ⊗[ℚ] S.G.C)ˣ) (hx : Triv S.G (AfP p) B.β x 1),
    (∀ y : GL (Fin n) E × ℚˣ, y ∈ GlobalTheory.LKCx.grp S.G B.β ↔ y ∈ Gam0 E n) ∧
    ∀ (y : GL (Fin n) E × ℚˣ) (h : y ∈ GlobalTheory.LKCx.grp S.G B.β) (h' : y ∈ Gam0 E n), (B.embAt x 1 hx ⟨y, h⟩).1 = T.j (rat ⟨y, h'⟩)

def PIntRev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (y : Gam0 E n), (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ KGL w (n := n)) →
    inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G

def IntCof : Prop := ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (a : GL (Fin n) (Af E)),
  ∀ᶠ w in Filter.cofinite, GeneralLinearGroup.map (pLoc E w) a ∈ KGL w (n := n)

end UpperTheory.Gal.W2.Seed
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.W2.Seed

open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below)
open GroundTheory.Global.SemiLocal (completionMap)

private theorem eq_zero_of_small {E : Type} [Field E] [NumberField E] {w : Plc E}
    (z : w.adicCompletion E) (h : ∀ n : ℕ, Valued.v z ≤ WithZero.exp (-(n : ℤ))) : z = 0 := by
  by_contra hz
  have h0 : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v z = WithZero.exp m :=
    ⟨WithZero.log _, (WithZero.exp_log h0).symm⟩
  have := h (1 - m).toNat
  rw [hm, WithZero.exp_le_exp] at this
  omega

private theorem valued_completionMap_le {E : Type} [Field E] [NumberField E] (P : Plc E)
    (t : (below ℚ P).adicCompletion ℚ) (n : ℕ) (ht : Valued.v t ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (completionMap (below ℚ P) P t) ≤ WithZero.exp (-(n : ℤ)) := by
  have he : P.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 0 := by
    intro h0
    have h := GroundTheory.Global.SemiLocal.valued_completionMap (below ℚ P) P
      (0 : (below ℚ P).adicCompletion ℚ)
    rw [map_zero, map_zero, map_zero, h0, pow_zero] at h
    exact zero_ne_one h
  rw [GroundTheory.Global.SemiLocal.valued_completionMap]
  refine le_trans ?_ ht
  refine pow_le_of_le_one zero_le (ht.trans ?_) he
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

private theorem ringHom_eq {E : Type} [Field E] [NumberField E] (P : Plc E) (v : Plc ℚ)
    (φ ψ : v.adicCompletion ℚ →+* P.adicCompletion E)
    (hφ : ∀ (n : ℕ) (a : v.adicCompletion ℚ), Valued.v a ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (φ a) ≤ WithZero.exp (-(n : ℤ)))
    (hψ : ∀ (n : ℕ) (a : v.adicCompletion ℚ), Valued.v a ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (ψ a) ≤ WithZero.exp (-(n : ℤ))) (x : v.adicCompletion ℚ) : φ x = ψ x := by
  have aux : ∀ q : ℚ →+* v.adicCompletion ℚ, DenseRange q → φ x = ψ x := by
    intro q hd
    rw [← sub_eq_zero]
    refine eq_zero_of_small _ fun n => ?_
    have hopen : IsOpen {y : v.adicCompletion ℚ | Valued.v (y - x) ≤ WithZero.exp (-(n : ℤ))} :=
      (GlobalTheory.Idele.isOpen_valued_le (K := ℚ) v (-(n : ℤ))).preimage
        (continuous_id.sub continuous_const)
    obtain ⟨k, hk⟩ := hd.exists_mem_open hopen ⟨x, by simp⟩
    have hk' : Valued.v (q k - x) ≤ WithZero.exp (-(n : ℤ)) := by
      simpa only [Set.mem_ofPred_eq] using hk
    have h : φ (q k) = ψ (q k) := RingHom.congr_fun (Subsingleton.elim (φ.comp q) (ψ.comp q)) k
    have e : φ x - ψ x = ψ (q k - x) - φ (q k - x) := by
      rw [map_sub φ, map_sub ψ, h]
      abel
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le (hψ n _ hk') (hφ n _ hk'))
  exact aux _ (HeightOneSpectrum.denseRange_algebraMap (K := ℚ) v)

private theorem locMap_eq {E : Type} [Field E] [NumberField E] (P : Plc E)
    (x : (below ℚ P).adicCompletion ℚ) :
    GlobalTheory.AdeleBaseChange.locMap ℚ P x = completionMap (below ℚ P) P x :=
  ringHom_eq P (below ℚ P) (GlobalTheory.AdeleBaseChange.locMap ℚ P) (completionMap (below ℚ P) P)
    (fun n a ha => GlobalTheory.AdeleBaseChange.locMap_valued P n a ha)
    (fun n a ha => valued_completionMap_le P a n ha) x

private theorem ringHom_eq_of_continuous {R : Type} [Ring R] [TopologicalSpace R] [T2Space R]
    (v : Plc ℚ) (φ ψ : v.adicCompletion ℚ →+* R) (hφ : Continuous φ) (hψ : Continuous ψ)
    (x : v.adicCompletion ℚ) : φ x = ψ x := by
  have aux : ∀ q : ℚ →+* v.adicCompletion ℚ, DenseRange q → φ x = ψ x := fun q hd =>
    congrFun (hd.equalizer hφ hψ (funext fun k =>
      RingHom.congr_fun (Subsingleton.elim (φ.comp q) (ψ.comp q)) k)) x
  exact aux _ (HeightOneSpectrum.denseRange_algebraMap (K := ℚ) v)

private theorem adMap_eq {E : Type} [Field E] [NumberField E] (a : AfQ) :
    GlobalTheory.AdeleBaseChange.adMap ℚ E a = finiteAdeleMap ℚ E a :=
  FiniteAdeleRing.ext _ fun P => locMap_eq P _

private theorem below_conjSrc {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Plc E) :
    below ℚ (conjSrc (conjE E) w) = below ℚ w := by
  have h := conjPl_conjSrc (conjE E) w
  refine HeightOneSpectrum.ext (Ideal.ext fun y => ?_)
  change algebraMap (𝓞 ℚ) (𝓞 E) y ∈ (conjSrc (conjE E) w).asIdeal ↔ algebraMap (𝓞 ℚ) (𝓞 E) y ∈ w.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← h]
  have : conjE E ((algebraMap (𝓞 ℚ) (𝓞 E) y : 𝓞 E) : E) = ((algebraMap (𝓞 ℚ) (𝓞 E) y : 𝓞 E) : E) := by
    change conjE E (algebraMap ℚ E (y : ℚ)) = algebraMap ℚ E (y : ℚ)
    simp [eq_ratCast]
  rw [this]

private theorem conj_finiteAdeleMap {E : Type} [Field E] [NumberField E] [IsCMField E] (a : AfQ) :
    conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a := by
  refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
  rw [pLoc_conjFin]
  have hb := below_conjSrc w
  have key : ∀ (u : Plc E) (_ : below ℚ u = below ℚ w) (f : u.adicCompletion E →+* w.adicCompletion E),
      Continuous f → f (pLoc E u (finiteAdeleMap ℚ E a)) = pLoc E w (finiteAdeleMap ℚ E a) := by
    intro u hu f hf
    haveI : w.asIdeal.LiesOver (below ℚ u).asIdeal := (GroundTheory.Global.AdeleBaseChange.below_eq_iff w _).1 hu.symm
    change f (completionMap (below ℚ u) u (a (below ℚ u))) = completionMap (below ℚ w) w (a (below ℚ w))
    rw [← GroundTheory.Global.AdeleBaseChange.completionMap_congr hu w a]
    exact ringHom_eq_of_continuous (below ℚ u) (f.comp (completionMap (below ℚ u) u)) (completionMap (below ℚ u) w)
      (hf.comp (GroundTheory.Global.SemiLocal.continuous_completionMap _ _))
      (GroundTheory.Global.SemiLocal.continuous_completionMap _ _) _
  exact key _ hb _ (conjLoc_spec (conjE E) w).1

end UpperTheory.Gal.W2.Seed

open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)

theorem UpperTheory.Gal.W2.Seed.pAdTensor :
    AdTensor := by
  intro E _ _ _
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd ℚ E
  let c : AfQ ⊗[ℚ] E ≃+* Formalism.L2.DIV.AfE ℚ E :=
    (Algebra.TensorProduct.comm ℚ AfQ E).toRingEquiv
  have hc : ∀ a x, c (a ⊗ₜ[ℚ] x) = x ⊗ₜ[ℚ] a := fun a x => rfl
  have hc' : ∀ a x, c.symm (x ⊗ₜ[ℚ] a) = a ⊗ₜ[ℚ] x := fun a x => rfl
  let j := c.trans (RingEquiv.ofBijective ι
    ⟨GlobalTheory.AdeleBaseChange.map_injective hι, GlobalTheory.AdeleBaseChange.map_surjective hι⟩)
  have hj : ∀ y, j y = ι (c y) := fun y => rfl
  refine ⟨j, fun a x => ?_, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, conj_finiteAdeleMap⟩
  · rw [hj, hc, hι, adMap_eq, mul_comm]
  · have : j y ∈ Formalism.UG.intAd E := by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, x, ha, rfl⟩ := hy
        rw [hj, hc]
        exact GlobalTheory.AdeleBaseChange.map_mem_int hι (Formalism.UG.P.levelaf_tmul_mem x ha)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | neg x _ hx => rw [map_neg]; exact neg_mem hx
    exact this
  · have h : c y ∈ Formalism.L2.DIV.RInt ℚ E := GlobalTheory.AdeleBaseChange.mem_int_of_map hι hy
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
    obtain ⟨r, hr, e⟩ := Formalism.UG.P.levelaf_decomp g hg h
    have e' : y = c.symm (c y) := (c.symm_apply_apply y).symm

    rw [e', e, map_sum]
    refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨r i, g i, hr i, ?_⟩
    rw [hc']
end
end

section

noncomputable section

open NumberField nonZeroDivisors

namespace UpperTheory.Gal.W2.Seed

private theorem exists_ideal (E : Type) [Field E] [NumberField E] :
    ∃ (a : 𝓞 E) (J : Ideal (𝓞 E)), a ≠ 0 ∧ J ≠ ⊥ ∧
      ∀ z : E, InCodiff z ↔ ∃ j ∈ J, z = (a : E)⁻¹ * (j : E) := by
  classical
  have h1ne : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  set D : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.dual ℤ ℚ 1 with hDdef
  have hD : D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ h1ne
  have hmem : ∀ z : E, InCodiff z ↔ z ∈ D := by
    intro z
    unfold InCodiff
    rw [hDdef, FractionalIdeal.mem_dual h1ne]
    constructor
    · rintro h b hb
      obtain ⟨x, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
      obtain ⟨m, hm⟩ := h x
      exact ⟨m, by simpa [Algebra.traceForm_apply] using hm.symm⟩
    · intro h x
      obtain ⟨m, hm⟩ := h (x : E) ((FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩)
      exact ⟨m, by simpa [Algebra.traceForm_apply] using hm.symm⟩
  set d : E := algebraMap (𝓞 E) E (D.den : 𝓞 E) with hddef
  have hd0 : d ≠ 0 := by
    rw [hddef]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.coe_ne_zero _)
  have key := FractionalIdeal.den_mul_self_eq_num' (𝓞 E)⁰ E D
  have key2 : D = FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ * (D.num : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← key, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hd0,
      FractionalIdeal.spanSingleton_one, one_mul]
  refine ⟨(D.den : 𝓞 E), D.num, nonZeroDivisors.coe_ne_zero _, ?_, ?_⟩
  · intro h
    apply hD
    rw [← FractionalIdeal.num_eq_zero_iff]
    exact h
  · intro z
    rw [hmem]
    constructor
    · intro hz
      have h1 : d * z ∈ (D.num : FractionalIdeal (𝓞 E)⁰ E) := by
        rw [← key]
        exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hz
      obtain ⟨j, hj, hjeq⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
      refine ⟨j, hj, ?_⟩
      have h2 : (j : E) = d * z := hjeq
      have h3 : ((D.den : 𝓞 E) : E) = d := rfl
      rw [h3, h2, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
    · rintro ⟨j, hj, hz⟩
      have h4 : d⁻¹ * (j : E) ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ * (D.num : FractionalIdeal (𝓞 E)⁰ E) :=
        FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
          ((FractionalIdeal.mem_coeIdeal _).2 ⟨j, hj, rfl⟩)
      rw [← key2] at h4
      rw [hz]
      exact h4

theorem pCodiffGen : CodiffGen := by
  unfold CodiffGen
  intro E _ _ M hM
  classical
  obtain ⟨a, J, ha, hJ, hcod⟩ := exists_ideal E
  have hM0 : ((M : 𝓞 E)) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hI0 : J * Ideal.span {(M : 𝓞 E)} ≠ 0 := by
    refine mul_ne_zero (show J ≠ 0 from hJ) ?_
    intro h
    exact hM0 (Ideal.span_singleton_eq_bot.1 h)
  have hle : J * Ideal.span {(M : 𝓞 E)} ≤ J := Ideal.mul_le.2 fun r hr s _ => J.mul_mem_right s hr
  obtain ⟨j, hj⟩ := IsDedekindDomain.exists_sup_span_eq hle hI0
  have hjJ : j ∈ J := by
    rw [← hj]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self j)
  obtain ⟨K, hK⟩ : J ∣ Ideal.span {j} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hjJ)
  have hKM : K ⊔ Ideal.span {(M : 𝓞 E)} = ⊤ := by
    have h1 : J * (Ideal.span {(M : 𝓞 E)} ⊔ K) = J * ⊤ := by
      rw [Ideal.mul_sup, ← hK, hj, Ideal.mul_top]
    rw [sup_comm]
    exact mul_left_cancel₀ (show J ≠ 0 from hJ) h1
  set e := Ideal.absNorm K with hedef
  have heK : (e : 𝓞 E) ∈ K := Ideal.absNorm_mem K
  refine ⟨(a : E)⁻¹ * (j : E), (hcod _).2 ⟨j, hjJ, rfl⟩, e, ?_, ?_⟩
  · refine Nat.coprime_of_dvd fun q hq hqe hqM => ?_
    have hMq : (M : 𝓞 E) ∈ Ideal.span {(q : 𝓞 E)} :=
      Ideal.mem_span_singleton.2 (Nat.cast_dvd_cast hqM)
    have hKq : K ⊔ Ideal.span {(q : 𝓞 E)} = ⊤ := by
      rw [eq_top_iff, ← hKM]
      exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 hMq) K
    have h1 : (1 : 𝓞 E) ∈ K ⊔ Ideal.span {(q : 𝓞 E)} := by rw [hKq]; trivial
    obtain ⟨k, hk, m, hm, hkm⟩ := Submodule.mem_sup.1 h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hm
    by_cases hK0 : K = ⊥
    · subst hK0
      have hk0 : k = 0 := (Submodule.mem_bot _).1 hk
      rw [hk0, zero_add] at hkm
      have hunit : IsUnit (q : 𝓞 E) := isUnit_iff_exists_inv.2 ⟨t, by rw [mul_comm]; exact hkm⟩
      have htop : Ideal.span {(q : 𝓞 E)} = ⊤ := Ideal.span_singleton_eq_top.2 hunit
      have hn := Ideal.absNorm_span_natCast (S := 𝓞 E) q
      rw [htop, Ideal.absNorm_top] at hn
      have hpos : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
      rcases (Nat.pow_eq_one.1 hn.symm) with h | h
      · exact hq.ne_one h
      · omega
    · haveI : Finite (𝓞 E ⧸ K) := Ideal.finiteQuotientOfFreeOfNeBot K hK0
      haveI : Fact q.Prime := ⟨hq⟩
      have hcard : q ∣ Nat.card (𝓞 E ⧸ K) := by
        rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
        exact hqe
      obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hcard
      have hqx : (q : 𝓞 E ⧸ K) * x = 0 := by
        rw [← nsmul_eq_mul, ← hx]
        exact addOrderOf_nsmul_eq_zero x
      have hu : (q : 𝓞 E ⧸ K) * Ideal.Quotient.mk K t = 1 := by
        have := congrArg (Ideal.Quotient.mk K) hkm
        rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hk, zero_add, map_mul, map_one, map_natCast] at this
        rw [mul_comm]
        exact this
      have hx0 : x = 0 := by
        linear_combination (-x) * hu + (Ideal.Quotient.mk K t) * hqx
      rw [hx0, addOrderOf_zero] at hx
      exact hq.one_lt.ne hx
  · intro z hz
    obtain ⟨j', hj', rfl⟩ := (hcod z).1 hz
    have hmem : j' * (e : 𝓞 E) ∈ Ideal.span {j} := by
      rw [hK]
      exact Ideal.mul_mem_mul hj' heK
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨x, ?_⟩
    have hcast : ((x : E) * (j : E)) = (j' : E) * (e : E) := by
      have := congrArg (fun w : 𝓞 E => (w : E)) hx
      simpa using this
    linear_combination (-(a : E)⁻¹) * hcast

end UpperTheory.Gal.W2.Seed
end
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pCodiffUnit :
    UnitMod → CodiffUnit := by
  intro hU E _ _ M hMpos y t hy ht hloc
  obtain ⟨_, e, he, hye⟩ := hy
  by_cases hM1 : M = 1
  · refine ⟨ht, 0, by simp [hM1], fun z _ => ⟨0, by simp⟩⟩
  let A : Ideal (𝓞 E) :=
    { carrier := {a | ∀ z : E, InCodiff z → ∃ x : 𝓞 E, (a : E) * z = t * x}
      add_mem' := by
        intro a b ha hb z hz
        obtain ⟨x1, h1⟩ := ha z hz
        obtain ⟨x2, h2⟩ := hb z hz
        exact ⟨x1 + x2, by push_cast; rw [add_mul, h1, h2, mul_add]⟩
      zero_mem' := by
        intro z _
        exact ⟨0, by simp⟩
      smul_mem' := by
        intro c a ha z hz
        obtain ⟨x, hx⟩ := ha z hz
        refine ⟨c * x, ?_⟩
        simp only [smul_eq_mul]
        push_cast
        rw [mul_assoc, hx]
        ring }
  have hA : ∀ a : 𝓞 E, a ∈ A → ∀ z : E, InCodiff z → ∃ x : 𝓞 E, (a : E) * z = t * x :=
    fun a ha => ha
  have htop : A ⊔ Ideal.span {((M : ℕ) : 𝓞 E)} = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
    have hMP : ((M : ℕ) : 𝓞 E) ∈ P :=
      hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    obtain ⟨s, u, _, huP, hsu⟩ := hloc P hPmax hMP
    have heP : ((e : ℕ) : 𝓞 E) ∉ P := by
      intro heP
      obtain ⟨p, q, hpq⟩ := Nat.isCoprime_iff_coprime.mpr he
      have h1 : ((p : 𝓞 E) * ((e : ℕ) : 𝓞 E) + (q : 𝓞 E) * ((M : ℕ) : 𝓞 E)) = 1 := by
        have := congrArg (fun n : ℤ => (n : 𝓞 E)) hpq
        push_cast at this
        exact this
      apply hPmax.ne_top
      rw [Ideal.eq_top_iff_one, ← h1]
      exact P.add_mem (P.mul_mem_left _ heP) (P.mul_mem_left _ hMP)
    have hue : u * ((e : ℕ) : 𝓞 E) ∉ P := by
      intro hmem
      rcases hPmax.isPrime.mem_or_mem hmem with h | h
      · exact huP h
      · exact heP h
    apply hue
    apply hle
    apply Ideal.mem_sup_left
    intro z hz
    obtain ⟨x, hx⟩ := hye z hz
    refine ⟨s * x, ?_⟩
    push_cast
    rw [mul_assoc, hx, ← mul_assoc, ← hsu]
    ring
  have hone : (1 : 𝓞 E) ∈ A ⊔ Ideal.span {((M : ℕ) : 𝓞 E)} := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨a, haA, m, hm, ham⟩ := Submodule.mem_sup.mp hone
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hm
  by_cases ha0 : a = 0
  · exfalso
    apply hM1
    have hunit : IsUnit ((M : ℕ) : 𝓞 E) :=
      isUnit_iff_exists_inv.mpr ⟨b, by rw [ha0, zero_add] at ham; rw [mul_comm]; exact ham⟩
    have hspan : Ideal.span {((M : ℕ) : 𝓞 E)} = ⊤ := Ideal.span_singleton_eq_top.mpr hunit
    have hn := Ideal.absNorm_span_natCast (S := 𝓞 E) M
    rw [hspan, Ideal.absNorm_top] at hn
    have hpos : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
    rcases Nat.pow_eq_one.mp hn.symm with h | h
    · exact h
    · exact absurd h hpos
  obtain ⟨e', he', c', hc'⟩ := hU E M a (-b) ha0 (by linear_combination ham)
  refine ⟨ht, e', he', fun z hz => ?_⟩
  obtain ⟨x, hx⟩ := hA a haA z hz
  refine ⟨c' * x, ?_⟩
  have hcoe : ((e' : ℕ) : E) = (a : E) * (c' : E) := by
    have := congrArg (fun w : 𝓞 E => (w : E)) hc'
    push_cast at this
    exact this.symm
  rw [hcoe, mul_comm (a : E), mul_assoc, hx]
  push_cast
  ring
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pSetupBasic :
    SetupBasic := by
  intro E _ _ _ A n p _ S
  have key : ∀ v : InfinitePlace E, sigPosH (S.G.gram_herm v) = 1 ↔ v = InfinitePlace.mk A.τ₀ := by
    intro v
    show sigPos (A.herm n) v.embedding = 1 ↔ _
    have h := S.sig v.embedding
    rw [InfinitePlace.mk_embedding] at h
    constructor
    · intro h1
      by_contra hne
      have h0 := (h.2 hne).1
      omega
    · intro hv
      exact (h.1 hv).1
  refine ⟨?_, (key _).2 rfl, fun h => ?_⟩
  · exact Fintype.card_eq_one_iff.2 ⟨⟨InfinitePlace.mk A.τ₀, (key _).2 rfl⟩,
      fun w => Subtype.ext ((key w.1).1 w.2)⟩
  · have h2 : 2 * 1 < Module.finrank ℚ E := by simpa using h
    exact ⟨Or.inl h2, Or.inl h2⟩
end
