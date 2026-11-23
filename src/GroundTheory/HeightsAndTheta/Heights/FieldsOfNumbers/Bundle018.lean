module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle010
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle015
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.Localization

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

set_option synthInstance.maxHeartbeats 400000

namespace DegZeroLocResidue

variable {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}

local notation "fr" Q:max h:max =>
  algebraMap (_ ⧸ Q) (FractionRing (_ ⧸ Q)) (Ideal.Quotient.mk Q h)

omit [DecidableEq K] in
theorem fr_ne_zero (Q : Ideal (MRing ι F)) [Q.IsPrime] {h : MRing ι F} (hh : h ∉ Q) :
    fr Q h ≠ 0 := by
  rwa [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

variable {P W : Ideal (MRing ι F)} [P.IsPrime] [W.IsPrime]


omit [DecidableEq K] in
theorem residue_eq (hPW : P ≤ W) {f g f' g' : MRing ι F} (hg : g ∉ W) (hg' : g' ∉ W)
    (h : fr P f / fr P g = fr P f' / fr P g') : fr W f / fr W g = fr W f' / fr W g' := by
  rw [div_eq_div_iff (fr_ne_zero P fun h => hg (hPW h)) (fr_ne_zero P fun h => hg' (hPW h)),
    ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h
  rw [div_eq_div_iff (fr_ne_zero W hg) (fr_ne_zero W hg'), ← map_mul, ← map_mul, ← map_mul,
    ← map_mul, Ideal.Quotient.eq.mpr (hPW (Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ h)))]


variable (P W) in
open Classical in
def res (x : FractionRing (MRing ι F ⧸ P)) : FractionRing (MRing ι F ⧸ W) :=
  if h : ∃ fg : MRing ι F × MRing ι F, fg.2 ∉ W ∧ x = fr P fg.1 / fr P fg.2 then
    fr W h.choose.1 / fr W h.choose.2 else 0


omit [DecidableEq K] in
theorem res_eq (hPW : P ≤ W) {x : FractionRing (MRing ι F ⧸ P)} {f g : MRing ι F} (hg : g ∉ W)
    (hx : x = fr P f / fr P g) : res P W x = fr W f / fr W g := by
  have h : ∃ fg : MRing ι F × MRing ι F, fg.2 ∉ W ∧ x = fr P fg.1 / fr P fg.2 := ⟨(f, g), hg, hx⟩
  rw [res, dite_eq_left h]
  exact residue_eq hPW h.choose_spec.1 hg (h.choose_spec.2.symm.trans hx)

theorem exists_rep (x : degZeroLoc P {W}) : ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧
    IsMultiHomog g b ∧ g ∉ W ∧ (x : FractionRing (MRing ι F ⧸ P)) = fr P f / fr P g := by
  obtain ⟨b, f, g, hf, hg, -, hgW, hx⟩ := DegZeroLocQuot.proof F K ι P {W}
    (by rintro _ rfl; infer_instance) x x.2
  exact ⟨b, f, g, hf, hg, hgW W rfl, hx⟩

def ρ (hPW : P ≤ W) : degZeroLoc P {W} →+* FractionRing (MRing ι F ⧸ W) where
  toFun x := res P W x
  map_one' := by
    have h1 : (1 : MRing ι F) ∉ W := (Ideal.ne_top_iff_one W).mp Ideal.IsPrime.ne_top'
    rw [res_eq hPW (f := 1) (g := 1) h1 (by simp)]; simp
  map_mul' x y := by
    obtain ⟨-, f, g, -, -, hg, hx⟩ := exists_rep x
    obtain ⟨-, f', g', -, -, hg', hy⟩ := exists_rep y
    have hgg : g * g' ∉ W := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hg hg'
    rw [res_eq hPW hg hx, res_eq hPW hg' hy, res_eq (f := f * f') hPW hgg
      (by rw [Subalgebra.coe_mul, hx, hy, div_mul_div_comm, map_mul, map_mul, map_mul, map_mul]),
      div_mul_div_comm, map_mul, map_mul, map_mul, map_mul]
  map_zero' := by
    rw [res_eq hPW (f := 0) (g := 1) ((Ideal.ne_top_iff_one W).mp Ideal.IsPrime.ne_top') (by simp)]
    simp
  map_add' x y := by
    obtain ⟨-, f, g, -, -, hg, hx⟩ := exists_rep x
    obtain ⟨-, f', g', -, -, hg', hy⟩ := exists_rep y
    have hgg : g * g' ∉ W := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hg hg'
    rw [res_eq hPW hg hx, res_eq hPW hg' hy, res_eq (f := f * g' + g * f') hPW hgg
      (by rw [Subalgebra.coe_add, hx, hy, div_add_div _ _ (fr_ne_zero P fun h => hg (hPW h))
        (fr_ne_zero P fun h => hg' (hPW h))]; simp only [map_add (f := _), map_mul]),
      div_add_div _ _ (fr_ne_zero W hg) (fr_ne_zero W hg')]
    simp only [map_add (f := _), map_mul]

theorem ρ_apply (hPW : P ≤ W) (x : degZeroLoc P {W}) : ρ hPW x = res P W x := rfl

theorem inv_mem (hPW : P ≤ W) {b : K → ℕ} {f g : MRing ι F} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g b) (hfW : f ∉ W) : fr P g / fr P f ∈ degZeroLoc P {W} :=
  div_mem_degZeroLoc P {W} hg hf (fun h => hfW (hPW h)) (by rintro _ rfl; exact hfW)

theorem proof : DegZeroLocResidue.Statement := by
  intro F _ K _ ι P _ W _ hPW
  refine ⟨ρ hPW, fun x b f g _ _ hg hx => res_eq hPW hg hx, fun x => ⟨?_, ?_⟩, fun z => ⟨?_, ?_⟩⟩
  · rintro h0 ⟨y, hy, hxy⟩
    have h1 : ρ hPW (x * ⟨y, hy⟩) = 1 := by rw [show x * ⟨y, hy⟩ = 1 from Subtype.ext hxy, map_one]
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro hn
    by_contra h0
    obtain ⟨b, f, g, hf, hg, hgW, hx⟩ := exists_rep x
    rw [ρ_apply, res_eq hPW hgW hx] at h0
    have hfW : f ∉ W := fun h => h0 (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero, zero_div])
    refine hn ⟨_, inv_mem hPW hf hg hfW, ?_⟩
    rw [hx, div_mul_div_comm, mul_comm (fr P f), div_self (mul_ne_zero
      (fr_ne_zero P fun h => hgW (hPW h)) (fr_ne_zero P fun h => hfW (hPW h)))]
  · intro hz
    let E : IntermediateField F (FractionRing (MRing ι F ⧸ W)) :=
      { carrier := Set.range (ρ hPW)
        mul_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩
        add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add _ _ _⟩
        one_mem' := ⟨1, map_one _⟩
        zero_mem' := ⟨0, map_zero _⟩
        algebraMap_mem' := fun c => ⟨algebraMap F _ c, by
          rw [ρ_apply, res_eq hPW (f := C c) (g := 1) ((Ideal.ne_top_iff_one W).mp
            Ideal.IsPrime.ne_top') (by
              show algebraMap F (FractionRing (MRing ι F ⧸ P)) c = _
              rw [map_one, map_one, div_one, IsScalarTower.algebraMap_apply F (MRing ι F ⧸ P),
                ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq])]
          rw [map_one, map_one, div_one, IsScalarTower.algebraMap_apply F (MRing ι F ⧸ W),
            ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]⟩
        inv_mem' := by
          rintro _ ⟨x, rfl⟩
          by_cases h0 : ρ hPW x = 0
          · rw [h0, inv_zero]; exact ⟨0, map_zero _⟩
          obtain ⟨b, f, g, hf, hg, hgW, hx⟩ := exists_rep x
          rw [ρ_apply, res_eq hPW hgW hx] at h0 ⊢
          have hfW : f ∉ W := fun h => h0 (by
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero, zero_div])
          exact ⟨⟨_, inv_mem hPW hf hg hfW⟩, by rw [ρ_apply, res_eq hPW hfW rfl, inv_div]⟩ }
    have hle : homFracDegZero W ≤ E := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨b, f, g, hf, hg, hgW, rfl⟩
      exact ⟨⟨_, div_mem_degZeroLoc P {W} hf hg (fun h => hgW (hPW h)) (by rintro _ rfl; exact hgW)⟩,
        res_eq hPW hgW rfl⟩
    exact hle hz
  · rintro ⟨x, rfl⟩
    obtain ⟨b, f, g, hf, hg, hgW, hx⟩ := exists_rep x
    rw [ρ_apply, res_eq hPW hgW hx]
    exact IntermediateField.subset_adjoin _ _ ⟨b, f, g, hf, hg, hgW, rfl⟩

end DegZeroLocResidue

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem module_finite_of_forall_mem_span {A A' B L : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing A'] [CommRing B] [Algebra A B] [CommRing L] [Algebra A' L] (φ : A →+* A')
    (hφ : Function.Surjective φ) (ψ : B →+* L) (hψ : Function.Injective ψ)
    (hcomm : ∀ a b, ψ (algebraMap A B a * b) = algebraMap A' L (φ a) * ψ b) (s : Finset L)
    (h : ∀ b, ψ b ∈ Submodule.span A' (s : Set L)) : Module.Finite A B := by
  let _ : Algebra A L := ((algebraMap A' L).comp φ).toAlgebra
  have hspan : ∀ x ∈ Submodule.span A' (s : Set L), x ∈ Submodule.span A (s : Set L) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add _ _ _ _ hy hz => exact add_mem hy hz
    | smul a' y _ hy =>
      obtain ⟨a, rfl⟩ := hφ a'
      have e : φ a • y = a • y := by rw [Algebra.smul_def, Algebra.smul_def]; rfl
      rw [e]
      exact Submodule.smul_mem _ a hy
  let f : B →ₗ[A] L :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := fun a b => by rw [Algebra.smul_def, hcomm]; rfl }
  have : IsNoetherian A (Submodule.span A (s : Set L)) :=
    isNoetherian_span_of_finite A s.finite_toSet
  exact Module.Finite.of_injective (f.codRestrict _ fun b => hspan _ (h b))
    fun b c hbc => hψ (congrArg Subtype.val hbc)

theorem SemilocalFinite.proof (h1 : SemilocalIntegral.Statement.{u})
    (h2 : LocalIntegralClosureFinite.Statement.{u}) (h3 : DegZeroLocNoetherian.Statement.{u}) :
    SemilocalFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hd' hd W hW hdW hle
  have := hP'.isPrime
  set A := degZeroLoc (contractPrime j P') {W}
  set B := degZeroLoc P' (fibrePrimes j P' W)
  set A' := A.map (contractFracMap j P')
  have : IsNoetherianRing A :=
    h3 F K (fun k => ι' (j k)) _ (isMultiProjPrime_contractPrime _ _ hP') W hW hle
  have hint : Algebra.IsIntegral A B := h1 F K K' j ι' P' hP' n hd' hd W hW hdW hle
  obtain ⟨s, -, hs⟩ := h2 F K K' j ι' P' hP' (hd.trans hd'.symm) W hW hle
  let φA : A →+* A' := (((contractFracMap j P').comp A.val).codRestrict A'
    (fun a => Subalgebra.mem_map.mpr ⟨a, a.2, rfl⟩)).toRingHom
  have hφA : Function.Surjective φA := fun a' => by
    obtain ⟨a, ha, hae⟩ := Subalgebra.mem_map.mp a'.2
    exact ⟨⟨a, ha⟩, Subtype.ext hae⟩
  refine module_finite_of_forall_mem_span φA hφA B.val.toRingHom Subtype.val_injective
    (fun _ _ => rfl) s fun b => ?_
  exact hs _ (mem_homFracDegZero_of_mem_degZeroLoc P' _ _ b.2)
    (IsIntegral.map_of_comp_eq φA B.val.toRingHom (RingHom.ext fun _ => rfl) (hint.isIntegral b))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarInj.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    Function.Injective (coneVarMap P W hPW v)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarNumerator.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ p : MvPolynomial K (degZeroLoc P {W}),
      ∃ (b : K → ℕ) (g : MRing ι F) (h : (K →₀ ℕ) → MRing ι F),
        IsMultiHomog g b ∧ g ∉ W ∧ (∀ d, IsMultiHomog (h d) b) ∧
        (∀ d, ((p.coeff d : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (h d)) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)) ∧
        ((coneVarMap P W hPW v p : coneLocal P W hPW) : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
              (Ideal.Quotient.mk P (∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k)) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarSurj.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ z : coneLocal P W hPW, ∃ (p q : MvPolynomial K (degZeroLoc P {W})) (e : K →₀ ℕ),
      IsUnit (q.coeff e) ∧ z * coneVarMap P W hPW v q = coneVarMap P W hPW v p

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarUnit.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ (p : MvPolynomial K (degZeroLoc P {W})) (e : K →₀ ℕ), IsUnit (p.coeff e) →
      IsUnit (coneVarMap P W hPW v p)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u


set_option maxHeartbeats 400000 in
theorem ConeLocalFlat.proof (h : ConePolyLocalization.Statement.{u}) : ConeLocalFlat.Statement.{u} := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  choose v hv using hW.relevant
  obtain ⟨hA, hloc⟩ := h F K ι P hP W hW hPW v hv
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
  have : IsScalarTower (degZeroLoc P {W}) (MvPolynomial K (degZeroLoc P {W})) (coneLocal P W hPW) :=
    IsScalarTower.of_algebraMap_eq fun x => ((coneVarMap P W hPW v).commutes x).symm
  have hR : IsLocalRing (coneLocal P W hPW) :=
    IsLocalization.AtPrime.isLocalRing (coneLocal P W hPW)
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))
  refine ⟨hA, hR, ?_, ?_⟩
  · have := IsLocalization.flat (coneLocal P W hPW)
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _)).primeCompl
    exact Module.Flat.trans _ (MvPolynomial K (degZeroLoc P {W})) _
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))
      (coneLocal P W hPW), Ideal.map_map, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
