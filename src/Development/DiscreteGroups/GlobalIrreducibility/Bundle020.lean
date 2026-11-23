module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Formalism.ConjugateSelfDual.Bundle001
public import Development.DiscreteGroups.GlobalIrreducibility.DzApprox
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle006
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import GroundTheory.LocalFields.LocalFourierHaar
public import GroundTheory.LocalFields.PadicLogHom
public import GroundTheory.LocalFields.PrincipalUnitsModule
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
import Mathlib.GroupTheory.Nilpotent
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalB
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.StepData

namespace DiscreteGroups.sglob.DzIso

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

theorem exists_int_lift {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ_[g]) (h : ∀ a b, ‖M a b‖ ≤ 1) :
    ∃ A : Matrix (Fin n) (Fin n) ℤ_[g], (algebraMap ℤ_[g] ℚ_[g]).mapMatrix A = M :=
  ⟨fun a b => ⟨M a b, h a b⟩, by ext a b; rfl⟩

theorem mapMatrix_int_injective {n : ℕ} :
    Function.Injective ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix : Matrix (Fin n) (Fin n) ℤ_[g] → _) :=
  fun _ _ h => Matrix.ext fun a b => PadicInt.ext (congrFun (congrFun h a) b)

include hi

theorem mem_integer_iff (x : ℚ_[g]) : i x ∈ 𝒪[w.adicCompletion E] ↔ ‖x‖ ≤ 1 :=
  (Valuation.mem_integer_iff _ _).trans (valuation_le_iff i hi x)

theorem map_inc_mem_KO {n : ℕ} (k : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) ∈ KO (w.adicCompletion E) (Fin n) := by
  rw [mem_KO]
  refine ⟨fun a b => (mem_integer_iff i hi _).2 (k.val a b).2, fun a b => ?_⟩
  rw [← map_inv, ← map_inv]
  exact (mem_integer_iff i hi _).2 ((k⁻¹).val a b).2

theorem exists_of_mem_KO {n : ℕ} {m : GL (Fin n) (w.adicCompletion E)} (hm : m ∈ KO (w.adicCompletion E) (Fin n)) :
    ∃ k : GL (Fin n) ℤ_[g], Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) = m := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hm
  have hint : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), IntM M →
      ∀ a b, ‖i.symm.toRingHom.mapMatrix M a b‖ ≤ 1 := by
    intro M hM a b
    rw [← norm_le_iff i hi]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    exact (val_le_iff _).1 ((Valuation.mem_integer_iff _ _).1 (hM a b))
  obtain ⟨A, hA⟩ := exists_int_lift _ (hint _ h1)
  obtain ⟨B, hB⟩ := exists_int_lift _ (hint _ h2)
  have hAB : A * B = 1 := mapMatrix_int_injective (by rw [map_mul, hA, hB, ← map_mul, Units.mul_inv, map_one, map_one])
  have hBA : B * A = 1 := mapMatrix_int_injective (by rw [map_mul, hA, hB, ← map_mul, Units.inv_mul, map_one, map_one])
  refine ⟨⟨A, B, hAB, hBA⟩, Units.ext (Matrix.ext fun a b => ?_)⟩
  change i ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix A a b) = m.val a b
  rw [hA]
  simp

def toKO (n : ℕ) : GL (Fin n) ℤ_[g] →* KO (w.adicCompletion E) (Fin n) :=
  ((Matrix.GeneralLinearGroup.map i.toRingHom).comp (inc g n)).codRestrict _ fun k => map_inc_mem_KO i hi k

theorem coe_toKO (n : ℕ) (k : GL (Fin n) ℤ_[g]) :
    ((toKO i hi n k : KO (w.adicCompletion E) (Fin n)) : GL (Fin n) (w.adicCompletion E)) =
      Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) := rfl

theorem toKO_injective (n : ℕ) : Function.Injective (toKO i hi n) := by
  intro k k' h
  have h' := congrArg (fun x : KO (w.adicCompletion E) (Fin n) =>
    ((x : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) h
  refine Units.ext (Matrix.ext fun a b => PadicInt.ext (i.injective ?_))
  exact congrFun (congrFun h' a) b

theorem toKO_surjective (n : ℕ) : Function.Surjective (toKO i hi n) := by
  intro m
  obtain ⟨k, hk⟩ := exists_of_mem_KO i hi m.2
  exact ⟨k, Subtype.ext hk⟩

def equivKO (n : ℕ) : GL (Fin n) ℤ_[g] ≃* KO (w.adicCompletion E) (Fin n) :=
  MulEquiv.ofBijective (toKO i hi n) ⟨toKO_injective i hi n, toKO_surjective i hi n⟩

def redKO (n : ℕ) : KO (w.adicCompletion E) (Fin n) →* Gn g n :=
  (red g n).comp (equivKO i hi n).symm.toMonoidHom

theorem redKO_toKO (n : ℕ) (k : GL (Fin n) ℤ_[g]) : redKO i hi n (toKO i hi n k) = red g n k := by
  show red g n ((equivKO i hi n).symm (equivKO i hi n k)) = red g n k
  rw [MulEquiv.symm_apply_apply]

theorem redKO_surjective (n : ℕ) : Function.Surjective (redKO i hi n) :=
  (GlobalTheory.GLp.Model.red_surjective n).comp (equivKO i hi n).symm.surjective

theorem ker_redKO (n : ℕ) :
    (redKO i hi n).ker = (KOne (w.adicCompletion E) (Fin n)).subgroupOf (KO (w.adicCompletion E) (Fin n)) := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨k, rfl⟩ := toKO_surjective i hi n m
  rw [redKO_toKO, coe_toKO]
  constructor
  · intro hk
    exact map_mem_KOne i hi k hk
  · intro hm
    obtain ⟨k', hk', he⟩ := exists_of_mem_KOne i hi hm
    have : k' = k := toKO_injective i hi n (Subtype.ext he)
    rw [← this]
    exact hk'

end DiscreteGroups.sglob.DzIso
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal ValuativeRel GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


section Ring

variable {Ω : Type} [Field Ω]

def kappaToA {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω) : 𝓞 F →+* A :=
  ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A fun x =>
    mem_of_isIntegral_int A (NumberField.RingOfIntegers.isIntegral_coe x).algebraMap

def kappaQ {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω) :
    𝓞 F →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp (kappaToA A)

theorem kappa_ker_A {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (hv : IsPlaceOver A v) :
    RingHom.ker (kappaQ A : 𝓞 F →+* IsLocalRing.ResidueField A) = v.asIdeal := by
  ext y
  rw [RingHom.mem_ker, kappaQ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff, ← hv y]
  rfl

end Ring

section Compl

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem kappa_val_le_iff (y : v.adicCompletion L) :
    valuation (v.adicCompletion L) y ≤ 1 ↔ Valued.v y ≤ 1 :=
  (DiscreteGroups.sglob.DzIso.val_le_iff y).trans Valued.toNormedField.norm_le_one_iff

theorem kappa_val_lt_iff (y : v.adicCompletion L) :
    valuation (v.adicCompletion L) y < 1 ↔ Valued.v y < 1 :=
  (DiscreteGroups.sglob.DzIso.val_lt_iff y).trans Valued.toNormedField.norm_lt_one_iff

theorem kappa_v_int (y : 𝓞 L) :
    Valued.v (algebraMap L (v.adicCompletion L) (y : L)) = v.valuation L (y : L) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) v (y : L)

def kappaToO : 𝓞 L →+* 𝒪[v.adicCompletion L] :=
  ((algebraMap L (v.adicCompletion L)).comp (algebraMap (𝓞 L) L)).codRestrict 𝒪[v.adicCompletion L] fun y =>
    (Valuation.mem_integer_iff _ _).2 ((kappa_val_le_iff v _).2
      ((kappa_v_int v y).trans_le (v.valuation_le_one y)))

def kappaP : 𝓞 L →+* 𝓀[v.adicCompletion L] := (IsLocalRing.residue 𝒪[v.adicCompletion L]).comp (kappaToO v)

theorem kappa_ker_O : RingHom.ker (kappaP v) = v.asIdeal := by
  ext y
  rw [RingHom.mem_ker, kappaP, RingHom.comp_apply, ← map_zero (IsLocalRing.residue 𝒪[v.adicCompletion L]),
    residue_eq_iff_valuation_lt]
  have e1 : ((kappaToO v y : 𝒪[v.adicCompletion L]) : v.adicCompletion L) -
      ((0 : 𝒪[v.adicCompletion L]) : v.adicCompletion L) = algebraMap L (v.adicCompletion L) (y : L) := by
    rw [ZeroMemClass.coe_zero, sub_zero]
    rfl
  rw [e1, kappa_val_lt_iff v, kappa_v_int v y]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem v y

theorem kappa_surj_O : Function.Surjective (kappaP v) := by
  intro z
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective z
  have hu : Valued.v (u : v.adicCompletion L) ≤ 1 :=
    (kappa_val_le_iff v _).1 ((Valuation.mem_integer_iff _ _).1 u.2)
  obtain ⟨x, hx⟩ := exists_int_approx_compl v (u : v.adicCompletion L) hu
  refine ⟨x, ?_⟩
  rw [kappaP, RingHom.comp_apply, residue_eq_iff_valuation_lt, Valuation.map_sub_swap]
  exact (kappa_val_lt_iff v _).2 hx

end Compl

end DiscreteGroups.sglob.DzType
end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace DiscreteGroups.sglob.DzIso

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

theorem norm_symm_le (y : 𝒪[w.adicCompletion E]) : ‖i.symm (y : w.adicCompletion E)‖ ≤ 1 := by
  rw [← norm_le_iff i hi, RingEquiv.apply_symm_apply]
  exact (val_le_iff _).1 ((Valuation.mem_integer_iff _ _).1 y.2)

def toIntFun (y : 𝒪[w.adicCompletion E]) : ℤ_[g] := ⟨i.symm y, norm_symm_le i hi y⟩

theorem coe_toIntFun (y : 𝒪[w.adicCompletion E]) : ((toIntFun i hi y : ℤ_[g]) : ℚ_[g]) = i.symm y := rfl

def toInt : 𝒪[w.adicCompletion E] →+* ℤ_[g] where
  toFun := toIntFun i hi
  map_one' := PadicInt.ext (by rw [coe_toIntFun, PadicInt.coe_one]; simp)
  map_mul' a b := PadicInt.ext (by rw [PadicInt.coe_mul, coe_toIntFun, coe_toIntFun, coe_toIntFun]; simp)
  map_zero' := PadicInt.ext (by rw [coe_toIntFun, PadicInt.coe_zero]; simp)
  map_add' a b := PadicInt.ext (by rw [PadicInt.coe_add, coe_toIntFun, coe_toIntFun, coe_toIntFun]; simp)

theorem coe_toInt (y : 𝒪[w.adicCompletion E]) : ((toInt i hi y : ℤ_[g]) : ℚ_[g]) = i.symm y := rfl

def redO : 𝒪[w.adicCompletion E] →+* ZMod g := (PadicInt.toZMod (p := g)).comp (toInt i hi)

theorem redO_surjective : Function.Surjective (redO i hi) := by
  intro a
  refine ⟨(a.val : 𝒪[w.adicCompletion E]), ?_⟩
  show PadicInt.toZMod (toInt i hi (a.val : 𝒪[w.adicCompletion E])) = a
  rw [map_natCast, map_natCast, ZMod.natCast_zmod_val]

theorem ker_redO : RingHom.ker (redO i hi) = IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E] := by
  ext y
  rw [← IsLocalRing.residue_eq_zero_iff, residue_eq_zero_iff_lt, RingHom.mem_ker]
  show PadicInt.toZMod (toInt i hi y) = 0 ↔ _
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def,
    coe_toInt, ← valuation_lt_iff i hi, RingEquiv.apply_symm_apply]

end DiscreteGroups.sglob.DzIso
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Art

variable {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A w'}

theorem val_eq_one_iff (y : w'.adicCompletion E') :
    valuation (w'.adicCompletion E') y = 1 ↔ Valued.v y = 1 := by
  have e1 := DiscreteGroups.sglob.DzIso.val_lt_iff y
  have e2 := DiscreteGroups.sglob.DzIso.val_le_iff y
  rw [Valued.toNormedField.norm_lt_one_iff] at e1
  rw [Valued.toNormedField.norm_le_one_iff] at e2
  constructor
  · intro h
    exact le_antisymm (e2.1 h.le) (not_lt.1 fun hl => (e1.2 hl).ne h)
  · intro h
    exact le_antisymm (e2.2 h.le) (not_lt.1 fun hl => (e1.1 hl).ne h)

theorem exists_ine_of_v_eq_one {a' : Weil h' →* (w'.adicCompletion E')ˣ} (ha' : IsLocalArtin h' a')
    (u : (w'.adicCompletion E')ˣ) (hu : Valued.v (u : w'.adicCompletion E') = 1) :
    ∃ t : Ine (F := E') A, a' (ineIncl h' t) = u := by
  obtain ⟨σ, hσ⟩ := ha'.surj u
  have h1 := ha'.ord_eq σ
  rw [hσ, GlobalTheory.SmGL.SphCompletion.ord_completion, hu] at h1
  have h2 : deg σ = 0 := by simpa using h1
  exact ⟨⟨σ, deg_eq_zero_iff.1 h2⟩, by rw [← hσ]; rfl⟩

end Art

set_option linter.unusedVariables false in
theorem exists_ine_of_res {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (A : ValuationSubring Ω) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w') (n : ℕ)
    (hn : 0 < n) (hN : normV w' = g ^ n) (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (K : Type) [Field K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red) (hk : RingHom.ker red = w'.asIdeal) :
    ∀ z : Kˣ, ∃ (t : Ine (F := E') A) (x : 𝓞 E'), red x = z ∧
      Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
  intro z
  obtain ⟨x, hx⟩ := hr z
  have hnm : x ∉ w'.asIdeal := fun hm => z.ne_zero (by rw [← hx, ← RingHom.mem_ker, hk]; exact hm)
  have hv : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = 1 := by
    have e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E') :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')
    rw [e]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w') (K := E')).2 hnm
  have h0 : algebraMap E' (w'.adicCompletion E') (x : E') ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv; exact zero_ne_one hv
  obtain ⟨t, ht⟩ := exists_ine_of_v_eq_one ha' (Units.mk0 _ h0) (by simpa using hv)
  refine ⟨t, x, hx, ?_⟩
  rw [ht, Units.val_mk0, sub_self, map_zero]
  exact zero_lt_one

theorem exists_resChar {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (A : ValuationSubring Ω) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w') (n : ℕ)
    (hn : 0 < n) (hN : normV w' = g ^ n) (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (K : Type) [Field K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red) (hk : RingHom.ker red = w'.asIdeal)
    (η : Weil h' →* ℂˣ) (hη : IsSmooth η) (hηN : ∀ t : Ine (F := E') A, η (ineIncl h' t) ^ (g ^ n - 1) = 1) :
    ∃ ξ : Kˣ →* ℂˣ, ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
      Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        ξ z = η (ineIncl h' t) := by
  obtain ⟨χ, -, hχ⟩ := ha'.factor η hη
  have hgp : g.Prime := Fact.out
  have hvF : ∀ e : E', Valued.v (algebraMap E' (w'.adicCompletion E') e) = w'.valuation E' e :=
    fun e => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' e

  have hpow : ∀ u : (w'.adicCompletion E')ˣ, Valued.v (u : w'.adicCompletion E') = 1 → χ u ^ (g ^ n - 1) = 1 := by
    intro u hu
    obtain ⟨t, ht⟩ := exists_ine_of_v_eq_one ha' u hu
    rw [← ht, ← MonoidHom.comp_apply, ← hχ]
    exact hηN t

  have hgw : ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal := by
    have : Finite (𝓞 E' ⧸ w'.asIdeal) := w'.asIdeal.finiteQuotientOfFreeOfNeBot w'.ne_bot
    let := Fintype.ofFinite (𝓞 E' ⧸ w'.asIdeal)
    have hc : ((Fintype.card (𝓞 E' ⧸ w'.asIdeal) : ℕ) : 𝓞 E' ⧸ w'.asIdeal) = 0 := Nat.cast_card_eq_zero _
    rw [← Nat.card_eq_fintype_card, show Nat.card (𝓞 E' ⧸ w'.asIdeal) = g ^ n from hN, Nat.cast_pow] at hc
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact (pow_eq_zero_iff hn.ne').1 hc
  have hgv : Valued.v ((g : ℕ) : w'.adicCompletion E') < 1 := by
    have h1 := (w'.valuation_lt_one_iff_mem (K := E') ((g : ℕ) : 𝓞 E')).2 hgw
    have h2 := hvF ((g : ℕ) : E')
    rw [map_natCast] at h2
    rw [h2]
    simpa using h1
  have : CharP 𝓀[w'.adicCompletion E'] g := by
    rw [CharP.charP_iff_prime_eq_zero hgp, ← map_natCast (IsLocalRing.residue 𝒪[w'.adicCompletion E']) g,
      GlobalTheory.StepData.residue_eq_zero_iff_lt]
    have e : (((g : ℕ) : 𝒪[w'.adicCompletion E']) : w'.adicCompletion E') = ((g : ℕ) : w'.adicCompletion E') := by
      simp
    rw [e]
    exact (DiscreteGroups.sglob.DzIso.val_lt_iff _).2 (Valued.toNormedField.norm_lt_one_iff.2 hgv)

  have hmU : IsUnit (((g ^ n - 1 : ℕ) : ℤ_[g])) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast]
    have : Fact (1 < g) := ⟨hgp.one_lt⟩
    have h1 : 1 ≤ g ^ n := Nat.one_le_pow _ _ hgp.pos
    rw [Nat.cast_sub h1, Nat.cast_pow, ZMod.natCast_self, zero_pow hn.ne', Nat.cast_one, zero_sub, neg_eq_zero]
    exact one_ne_zero
  have hU1 : ∀ u : (w'.adicCompletion E')ˣ,
      valuation (w'.adicCompletion E') ((u : w'.adicCompletion E') - 1) < 1 → χ u = 1 := by
    intro u hu
    have hmem : u ∈ GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1 :=
      (GroundTheory.LocalField.mem_unitFiltrationUnits_iff_valBall le_rfl).2 (GroundTheory.LocalField.mem_valBall_one_iff.2 hu)
    let U : Additive (GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) := Additive.ofMul ⟨u, hmem⟩
    let y := ((hmU.unit⁻¹ : ℤ_[g]ˣ) : ℤ_[g]) • U
    have hy : (((g ^ n - 1 : ℕ) : ℤ_[g])) • y = U := by
      rw [smul_smul, IsUnit.mul_val_inv, one_smul]
    rw [GroundTheory.LocalField.natCast_smul g (g ^ n - 1) y] at hy
    have hy' : ((Additive.toMul y : GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) :
        (w'.adicCompletion E')ˣ) ^ (g ^ n - 1) = u := by
      have := congrArg (fun z : Additive (GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) =>
        ((Additive.toMul z : GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) :
          (w'.adicCompletion E')ˣ)) hy
      simpa [U] using this
    have hy0 : ((Additive.toMul y : GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) :
        (w'.adicCompletion E')ˣ) ∈ GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 0 :=
      GroundTheory.LocalField.unitFiltrationUnits_antitone (Nat.zero_le 1) (Additive.toMul y).2
    have hyv := (val_eq_one_iff _).1 (GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff.1 hy0)
    rw [← hy', map_pow]
    exact hpow _ hyv

  have hcong : ∀ u1 u2 : (w'.adicCompletion E')ˣ, Valued.v (u1 : w'.adicCompletion E') = 1 →
      Valued.v ((u1 : w'.adicCompletion E') - u2) < 1 → χ u1 = χ u2 := by
    intro u1 u2 h1 h2
    have hinv : Valued.v (((u1⁻¹ : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]
    have : χ (u1⁻¹ * u2) = 1 := hU1 _ (by
      rw [DiscreteGroups.sglob.DzIso.val_lt_iff, Valued.toNormedField.norm_lt_one_iff]
      have e : (((u1⁻¹ * u2 : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') - 1 =
          ((u1⁻¹ : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') * ((u2 : w'.adicCompletion E') - u1) := by
        rw [Units.val_mul, mul_sub, Units.inv_mul]
      rw [e, map_mul, hinv, one_mul, Valuation.map_sub_swap]
      exact h2)
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this
  have hv1 : ∀ x : 𝓞 E', red x ≠ 0 → Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = 1 := by
    intro x hx
    have hnm : x ∉ w'.asIdeal := fun hm => hx (by rw [← RingHom.mem_ker, hk]; exact hm)
    rw [hvF]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w') (K := E')).2 hnm
  choose xz hxz using hr
  have hne : ∀ z : Kˣ, algebraMap E' (w'.adicCompletion E') (xz z : E') ≠ 0 := fun z h0 => by
    have := hv1 (xz z) (by rw [hxz]; exact z.ne_zero)
    rw [h0, map_zero] at this
    exact zero_ne_one this
  let Uz : Kˣ → (w'.adicCompletion E')ˣ := fun z => Units.mk0 _ (hne z)
  have hUv : ∀ z : Kˣ, Valued.v ((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1 :=
    fun z => hv1 (xz z) (by rw [hxz]; exact z.ne_zero)
  have hUc : ∀ (z : Kˣ) (x : 𝓞 E'), red x = z →
      Valued.v (((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') -
        algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
    intro z x hx
    have hm : xz z - x ∈ w'.asIdeal := by rw [← hk, RingHom.mem_ker, map_sub, hxz, hx, sub_self]
    have := (w'.valuation_lt_one_iff_mem (K := E') (xz z - x)).2 hm
    show Valued.v (algebraMap E' (w'.adicCompletion E') (xz z : E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1
    rw [← map_sub, hvF]
    exact this
  let ξ : Kˣ →* ℂˣ :=
    { toFun := fun z => χ (Uz z)
      map_one' := by
        have h := hUc 1 1 (by rw [map_one, Units.val_one])
        rw [show algebraMap E' (w'.adicCompletion E') ((1 : 𝓞 E') : E') = (((1 : (w'.adicCompletion E')ˣ)) :
          w'.adicCompletion E') by simp] at h
        show χ (Uz 1) = 1
        rw [hcong _ 1 (hUv 1) h, map_one]
      map_mul' := fun z1 z2 => by
        show χ (Uz (z1 * z2)) = χ (Uz z1) * χ (Uz z2)
        rw [← map_mul]
        refine hcong _ _ (hUv _) ?_
        have h := hUc (z1 * z2) (xz z1 * xz z2) (by rw [map_mul, hxz, hxz, Units.val_mul])
        have e : (((Uz z1 * Uz z2 : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') =
            algebraMap E' (w'.adicCompletion E') ((xz z1 * xz z2 : 𝓞 E') : E') := by
          simp [Uz]
        rw [e]
        exact h }
  refine ⟨ξ, fun t x z hxz' hv => ?_⟩
  show χ (Uz z) = η (ineIncl h' t)
  rw [hχ, MonoidHom.comp_apply]
  refine hcong _ _ (hUv z) ?_
  have h1 := hUc z x hxz'
  have e : ((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') - (a' (ineIncl h' t) : w'.adicCompletion E') =
      (((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) -
        ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) := by
    ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 hv)

end DiscreteGroups.sglob.DzType
end
end
