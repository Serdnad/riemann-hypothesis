module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegLTGrowth
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiltrationHilbSum
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertPrime
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulesFromPrimes
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedFiltration
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace HilbertPositive

theorem hilbertPrime : HilbertSamuel.HilbertPrime.Statement.{u} :=
  HilbertSamuel.HilbertPrime.proof HilbertSamuel.HilbertDimZero.proof
    (HilbertSamuel.HilbertIncrement.proof HilbertSamuel.IntersectionRecursion.proof)
    (HilbertSamuel.MixedNumberPolynomial.proof
      (HilbertSamuel.MultigradedHilbertPolynomial.proof HilbertSamuel.EventualPolynomial.proof))
    (HilbertSamuel.ModulesFromPrimes.proof HilbertSamuel.MultigradedFiltration.proof
      HilbertSamuel.FiltrationHilbSum.proof HilbertSamuel.DegLTGrowth.proof)

theorem mixedNumber : HilbertSamuel.MixedNumberPolynomial.Statement.{u} :=
  HilbertSamuel.MixedNumberPolynomial.proof
    (HilbertSamuel.MultigradedHilbertPolynomial.proof HilbertSamuel.EventualPolynomial.proof)

def blockEquiv (N : ℕ) : (Σ _ : Unit, Fin (N + 1)) ≃ Fin (N + 1) where
  toFun v := v.2
  invFun i := ⟨(), i⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

theorem weight_blockWeight_one (d : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) d = fun _ => d.degree := by
  funext u
  rw [Finsupp.weight_apply, Finsupp.degree, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [NumbersDVR.blockWeight]

theorem isWeightedHomogeneous_iff (p : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) p (fun _ => n) ↔
      p.IsHomogeneous n := by
  constructor
  · intro h d hd
    have h1 : d.degree = n := congrFun ((weight_blockWeight_one d).symm.trans (h hd)) ()
    rw [← h1, Finsupp.degree_eq_weight_one]
    rfl
  · intro h d hd
    rw [weight_blockWeight_one]
    funext _
    rw [Finsupp.degree_eq_weight_one]
    exact h hd

theorem ringKrullDim_primeOfOne (y : Fin (N + 1) → Ω) :
    ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ringKrullDim (Poly k N ⧸ primeOf (S := k) y) := by
  let f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N :=
    (renameEquiv k (blockEquiv N)).toRingEquiv
  have hc : primeOfOne (S := k) y = (primeOf (S := k) y).comap f.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  have h : primeOf (S := k) y = (primeOfOne (S := k) y).map f.toRingHom := by
    rw [hc, Ideal.map_comap_of_surjective f.toRingHom f.surjective]
  exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ f h)

theorem ne_zero_of_isSubvar {y : Fin (N + 1) → Ω} {e : ℕ} (h : IsSubvar y (primeOf (S := k) y) e) :
    y ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  intro hy
  apply hi
  rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k i), aeval_X, hy, Pi.zero_apply]

theorem finrank_piece_eq_hilbFn (y : Fin (N + 1) → Ω) (n : ℕ) :
    (Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℤ) =
      NumbersDVR.hilbFn (primeOfOne (S := k) y) (fun _ => (n : ℤ)) := by
  classical
  rw [NumbersDVR.hilbFn, if_pos (fun _ => Int.natCast_nonneg n)]
  simp only [Int.toNat_natCast]
  congr 1
  set V := weightedHomogeneousSubmodule k (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1)))
    (fun _ : Unit => n) with hV
  let f₁ : V →ₗ[k] NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y :=
    (Ideal.Quotient.mkₐ k (primeOfOne (S := k) y)).toLinearMap ∘ₗ V.subtype
  let f₂ : V →ₗ[k] Ω :=
    (aeval (fun v : Σ _ : Unit, Fin (N + 1) => y v.2)).toLinearMap ∘ₗ V.subtype
  have hhom : ∀ v ∈ V, (oneBlock (S := k) (N := N) v).IsHomogeneous n := fun v hv =>
    ((isWeightedHomogeneous_iff v n).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hv)).rename_isHomogeneous
  have heval : ∀ v, aeval y (oneBlock (S := k) (N := N) v) = aeval (fun w : Σ _ : Unit, Fin (N + 1) => y w.2) v :=
    fun v => by rw [oneBlock, aeval_rename]; rfl
  have hr₁ : LinearMap.range f₁ = NumbersDVR.gradedPiece (primeOfOne (S := k) y) (fun _ => n) := by
    rw [NumbersDVR.gradedPiece, LinearMap.range_comp, Submodule.range_subtype]
  have hr₂ : LinearMap.range f₂ = (coordGraded k y).piece (n : ℤ) := by
    apply le_antisymm
    · rintro _ ⟨⟨v, hv⟩, rfl⟩
      refine Submodule.subset_span ⟨oneBlock (S := k) (N := N) v, n, hhom v hv, rfl, ?_⟩
      exact (heval v).symm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, e, hg, he, rfl⟩
      have he' : e = n := by exact_mod_cast he
      subst he'
      refine ⟨⟨rename (blockEquiv N).symm g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        ((isWeightedHomogeneous_iff _ e).mpr (hg.rename_isHomogeneous))⟩, ?_⟩
      change aeval (fun v : Σ _ : Unit, Fin (N + 1) => y v.2) (rename (blockEquiv N).symm g) = aeval y g
      rw [aeval_rename]
      rfl
  have hker : LinearMap.ker f₁ = LinearMap.ker f₂ := by
    ext ⟨v, hv⟩
    simp only [LinearMap.mem_ker, f₁, f₂, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    change oneBlock (S := k) (N := N) v ∈ primeOf (S := k) y ↔ _
    rw [mem_primeOf_of_isHomogeneous y (hhom v hv), heval]
  have e₁ := ((f₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
    f₂.quotKerEquivRange).finrank_eq
  rw [hr₁, hr₂] at e₁
  exact e₁.symm

end HilbertPositive


open HilbertPositive in
theorem HilbertPositive.proof (hPos : ProjDegreePositive.Statement.{u})
    (hSec : TwistSections.Statement.{u, w}) : HilbertPositive.Statement.{u, w} := by
  intro k _ Ω _ _ N y e he hW
  have hy : y ≠ 0 := ne_zero_of_isSubvar hW
  have hq : NumbersDVR.IsMultiProjPrime (primeOfOne (S := k) y) := isMultiProjPrime_primeOfOne y hy
  have hdim : ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim_primeOfOne]
    exact hW.dim
  refine ⟨?_, hPos k (Fin (N + 1)) _ e hq hdim, hSec k Ω N y hy⟩
  have hdim' : ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ((e + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
    simpa using hdim
  obtain ⟨a₀, C, hC⟩ := hilbertPrime e k Unit (fun _ => Fin (N + 1)) _ hq hdim'
  have hadd := (mixedNumber k Unit (fun _ => Fin (N + 1)) _ e hq hdim').2
  have hhom : ∀ n : ℕ, NumbersDVR.intNum k (primeOfOne (S := k) y)
      (fun _ : Fin e => fun _ : Unit => (n : ℤ)) = (n : ℤ) ^ e *
        NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) := by
    intro n
    have := HilbertSamuel.RankOfSections.const_nsmul
      (fun bs => NumbersDVR.intNum k (primeOfOne (S := k) y) bs) hadd n (fun _ : Unit => (1 : ℤ))
    have e' : (n • fun _ : Unit => (1 : ℤ)) = fun _ : Unit => (n : ℤ) := by
      funext u
      simp
    rw [e'] at this
    exact this
  refine ⟨|C| * 2 ^ (e - 1), ?_⟩
  filter_upwards [eventually_ge_atTop (max a₀ 1)] with n hn
  have h := hC (fun _ => n) (fun _ => le_of_max_le_left hn)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  rw [hhom n, ← finrank_piece_eq_hilbFn] at h
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hpow : ((n : ℝ) + 1) ^ ((e : ℝ) - 1) ≤ 2 ^ (e - 1) * (n : ℝ) ^ (e - 1) := by
    rw [show (e : ℝ) - 1 = ((e - 1 : ℕ) : ℝ) by rw [Nat.cast_sub he]; simp, Real.rpow_natCast,
      ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc |(Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℝ) -
        (NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℝ) *
          (n : ℝ) ^ e / (e.factorial : ℝ)|
      = |(((Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℤ)) : ℝ) -
          (((n : ℤ) ^ e * NumbersDVR.intNum k (primeOfOne (S := k) y)
            (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℤ) : ℝ) / (e.factorial : ℝ)| := by
        push_cast
        ring_nf
    _ ≤ C * ((n : ℝ) + 1) ^ ((e : ℝ) - 1) := h
    _ ≤ |C| * ((n : ℝ) + 1) ^ ((e : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 ^ (e - 1) * (n : ℝ) ^ (e - 1)) := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    _ = |C| * 2 ^ (e - 1) * (n : ℝ) ^ (e - 1) := by ring

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn)

noncomputable section

section ResidueMap

variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω] {K : Type} {ι : K → Type}
  (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [hp : p.IsPrime]

open IndefiniteRowSideFullHecke.Kleiman2 (ResField)

instance resField.isFractionRing : IsFractionRing (chartRingOver S y c ⧸ p) (ResField S y c p) :=
  inferInstanceAs (IsFractionRing (chartRingOver S y c ⧸ p) (FractionRing (chartRingOver S y c ⧸ p)))

omit hp in
theorem coe_ne_zero_of_notMem {b : (chartRingOver S y c)} (hb : b ∉ p) : (b : Ω) ≠ 0 := by
  intro h
  apply hb
  have : b = 0 := Subtype.ext h
  rw [this]
  exact p.zero_mem

theorem mem_locIn_chart_iff {u : Ω} : u ∈ locIn (chartRingOver S y c) p ↔ ∃ a b : (chartRingOver S y c), b ∉ p ∧ u = (a : Ω) / b := by
  constructor
  · intro hu
    induction hu using Subring.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, 1, Ideal.one_notMem p, by simp⟩
    | one => exact ⟨1, 1, Ideal.one_notMem p, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, b, hb, rfl⟩ := hx
      obtain ⟨a', b', hb', rfl⟩ := hy
      refine ⟨a * b' + b * a', b * b', hp.mul_notMem hb hb', ?_⟩
      rw [div_add_div _ _ (coe_ne_zero_of_notMem y c p hb) (coe_ne_zero_of_notMem y c p hb')]
      simp
    | neg x _ hx =>
      obtain ⟨a, b, hb, rfl⟩ := hx
      exact ⟨-a, b, hb, by simp [neg_div]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, hb, rfl⟩ := hx
      obtain ⟨a', b', hb', rfl⟩ := hy
      exact ⟨a * a', b * b', hp.mul_notMem hb hb', by simp [div_mul_div_comm]⟩
  · intro h
    exact Subring.subset_closure h

def resq (a : (chartRingOver S y c)) : ResField S y c p :=
  algebraMap (chartRingOver S y c ⧸ p) (ResField S y c p) (Ideal.Quotient.mk p a)

theorem resq_eq_zero_iff (a : (chartRingOver S y c)) : resq y c p a = 0 ↔ a ∈ p := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, resq]
  constructor
  · intro h
    exact IsFractionRing.injective (chartRingOver S y c ⧸ p) (ResField S y c p) (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

theorem resq_ne_zero {b : (chartRingOver S y c)} (hb : b ∉ p) : resq y c p b ≠ 0 :=
  fun h => hb ((resq_eq_zero_iff y c p b).mp h)

theorem resq_mul (a b : (chartRingOver S y c)) : resq y c p (a * b) = resq y c p a * resq y c p b := by
  simp [resq, map_mul]

theorem resq_add (a b : (chartRingOver S y c)) : resq y c p (a + b) = resq y c p a + resq y c p b := by
  simp only [resq, RingHom.map_add]

theorem resq_div_eq {a b a' b' : (chartRingOver S y c)} (hb : b ∉ p) (hb' : b' ∉ p) (h : (a : Ω) / b = (a' : Ω) / b') :
    resq y c p a / resq y c p b = resq y c p a' / resq y c p b' := by
  rw [div_eq_div_iff (coe_ne_zero_of_notMem y c p hb) (coe_ne_zero_of_notMem y c p hb')] at h
  have h' : a * b' = a' * b := Subtype.ext (by simpa using h)
  rw [div_eq_div_iff (resq_ne_zero y c p hb) (resq_ne_zero y c p hb'), ← resq_mul, ← resq_mul, h']

theorem exists_rep (u : locIn (chartRingOver S y c) p) : ∃ a b : (chartRingOver S y c), b ∉ p ∧ (u : Ω) = (a : Ω) / b :=
  (mem_locIn_chart_iff y c p).mp u.2

def resFun (u : locIn (chartRingOver S y c) p) : ResField S y c p :=
  resq y c p (exists_rep y c p u).choose / resq y c p (exists_rep y c p u).choose_spec.choose

theorem resFun_eq (u : locIn (chartRingOver S y c) p) {a b : (chartRingOver S y c)} (hb : b ∉ p) (hu : (u : Ω) = a / b) :
    resFun y c p u = resq y c p a / resq y c p b := by
  obtain ⟨hb0, hu0⟩ := (exists_rep y c p u).choose_spec.choose_spec
  exact resq_div_eq y c p hb0 hb (hu0.symm.trans hu)

def resMap : locIn (chartRingOver S y c) p →+* ResField S y c p where
  toFun := resFun y c p
  map_one' := by
    rw [resFun_eq y c p 1 (a := 1) (b := 1) (Ideal.one_notMem p) (by simp)]
    simp [resq]
  map_mul' u v := by
    obtain ⟨a, b, hb, hu⟩ := exists_rep y c p u
    obtain ⟨a', b', hb', hv⟩ := exists_rep y c p v
    rw [resFun_eq y c p u hb hu, resFun_eq y c p v hb' hv,
      resFun_eq y c p (u * v) (a := a * a') (b := b * b') (hp.mul_notMem hb hb')
        (by simp [hu, hv, div_mul_div_comm]), resq_mul, resq_mul, div_mul_div_comm]
  map_zero' := by
    rw [resFun_eq y c p 0 (a := 0) (b := 1) (Ideal.one_notMem p) (by simp)]
    simp [resq]
  map_add' u v := by
    obtain ⟨a, b, hb, hu⟩ := exists_rep y c p u
    obtain ⟨a', b', hb', hv⟩ := exists_rep y c p v
    rw [resFun_eq y c p u hb hu, resFun_eq y c p v hb' hv,
      resFun_eq y c p (u + v) (a := a * b' + b * a') (b := b * b') (hp.mul_notMem hb hb') (by
        rw [Subring.coe_add, hu, hv,
          div_add_div _ _ (coe_ne_zero_of_notMem y c p hb) (coe_ne_zero_of_notMem y c p hb')]
        simp),
      div_add_div _ _ (resq_ne_zero y c p hb) (resq_ne_zero y c p hb'), resq_add, resq_mul, resq_mul, resq_mul]

theorem resMap_eq (u : locIn (chartRingOver S y c) p) {a b : (chartRingOver S y c)} (hb : b ∉ p) (hu : (u : Ω) = a / b) :
    resMap y c p u = resq y c p a / resq y c p b :=
  resFun_eq y c p u hb hu

theorem resMap_of_mem (a : (chartRingOver S y c)) (h : (a : Ω) ∈ locIn (chartRingOver S y c) p) : resMap y c p ⟨a, h⟩ = resq y c p a := by
  rw [resMap_eq y c p _ (a := a) (b := 1) (Ideal.one_notMem p) (by simp)]
  simp [resq]

end ResidueMap

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

instance segreIdx.fintype {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    ∀ k, Fintype (Sum.elim (fun _ : Unit => ∀ k, ι k) ι k) := fun k => by
  cases k <;> infer_instance

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ModelPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
    ∀ (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
      (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → mIdealOver F y ≤ mIdealOver F y' →
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelTwistGenerated.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IsNoetherianRing S → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ β : K → ℤ,
      ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → IndefiniteRowSideFullHecke.Kleiman2.IsGenerated S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def ModelChangeNef.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
    IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
    ∀ (β : K → ℤ) (β' : K' → ℤ),
      (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
          secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
      (IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y' β')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelGenerated.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ β : K → ℤ,
      ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def ModelChangeVeryAmple.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
    IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
    ∀ (β : K → ℤ) (β' : K' → ℤ),
      (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
          secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
      (IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y β ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y' β')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def RayVanish.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ β : K → ℤ, ∀ᶠ c : ℕ in Filter.atTop, ∀ i : ℕ, 1 ≤ i →
      Subsingleton (cechHc ι (quotPart F (mIdealOver F y)) (β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) i)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
