module

public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle001
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Mathlib.Order.CompletePartialOrder
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle002
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.TameInertiaTowers.CentralOrderTwo.OddEqOneOfSubOneMem
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle010
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section

open IntermediateField NumberField

namespace Formalism.HC.HostRaw

open Formalism.FrobeniusOrbits Formalism.L2.Host

variable {φ : Frame} (H : HostRaw φ)

def EQ : Fld := ⨆ j : H.E →ₐ[ℚ] Qb, j.fieldRange

def FI : IntermediateField ℚ H.E := H.F.toIntermediateField fun x => by
  simpa using SubfieldClass.ratCast_mem H.F x

def FQ : Fld := ⨆ j : H.E →ₐ[ℚ] Qb, H.FI.map j

theorem mem_EQ (j : H.E →ₐ[ℚ] Qb) (x : H.E) : j x ∈ H.EQ :=
  (le_iSup (fun j : H.E →ₐ[ℚ] Qb => j.fieldRange) j) ⟨x, rfl⟩

def ActsAs (s : H.EQ →ₐ[ℚ] Qb) (g : φ.GG) : Prop :=
  ∀ (j : H.E →ₐ[ℚ] Qb) (x : H.E), s ⟨j x, H.mem_EQ j x⟩ = j (H.gal.symm g x)

def CondEQ : Prop := IsCond H.EQ H.condN

theorem nonempty_emb : Nonempty (H.E →ₐ[ℚ] Qb) := ⟨IsAlgClosed.lift⟩

theorem exists_aut (j j' : H.E →ₐ[ℚ] Qb) : ∃ σ : H.E ≃ₐ[ℚ] H.E, ∀ x, j' x = j (σ x) := by
  have := H.galois
  have inj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => j.comp (σ : H.E →ₐ[ℚ] H.E)) := by
    intro σ τ hst
    exact AlgEquiv.ext fun x => j.toRingHom.injective (DFunLike.congr_fun hst x)
  have hb := (Fintype.bijective_iff_injective_and_card _).mpr ⟨inj, by
    rw [AlgHom.card, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]⟩
  obtain ⟨σ, hσ⟩ := hb.2 j'
  exact ⟨σ, fun x => (DFunLike.congr_fun hσ x).symm⟩

theorem range_eq (j : H.E →ₐ[ℚ] Qb) : j.fieldRange = H.EQ := by
  refine le_antisymm (le_iSup (fun j : H.E →ₐ[ℚ] Qb => j.fieldRange) j) (iSup_le fun j' => ?_)
  obtain ⟨σ, hσ⟩ := H.exists_aut j j'
  rintro _ ⟨x, rfl⟩
  exact ⟨σ x, (hσ x).symm⟩

theorem map_K (j : H.E →ₐ[ℚ] Qb) : H.K.map j = KQ H.d := by
  have hb : j H.sqd ^ 2 = ((-(H.d : ℤ) : ℤ) : Qb) := by rw [← map_pow, H.sqd_sq]; simp
  rw [K, adjoin_map, Set.image_singleton, KQ, sqQ_eq hb]

theorem FQ_le_EQ : H.FQ ≤ H.EQ := iSup_le fun j => by
  rintro _ ⟨x, -, rfl⟩
  exact H.mem_EQ j x

theorem KQ_le_EQ : KQ H.d ≤ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  rw [← H.map_K j]
  rintro _ ⟨x, -, rfl⟩
  exact H.mem_EQ j x

def jOf (j : H.E →ₐ[ℚ] Qb) : H.E ≃ₐ[ℚ] H.EQ :=
  AlgEquiv.ofBijective (j.codRestrict H.EQ.toSubalgebra (H.mem_EQ j))
    ⟨fun x y hxy => j.toRingHom.injective (congrArg Subtype.val hxy), fun y => by
      have hy : (y : Qb) ∈ j.fieldRange := by rw [H.range_eq j]; exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

instance fin_EQ : FiniteDimensional ℚ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  exact (H.jOf j).toLinearEquiv.finiteDimensional

instance normal_EQ : Normal ℚ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  have := H.galois
  exact Normal.of_algEquiv (H.jOf j)

instance fin_FQ : FiniteDimensional ℚ H.FQ :=
  FiniteDimensional.of_injective (inclusion H.FQ_le_EQ).toLinearMap (inclusion H.FQ_le_EQ).toRingHom.injective

variable {H}

theorem actsAs_of_one {s : H.EQ →ₐ[ℚ] Qb} {g : φ.GG} (j : H.E →ₐ[ℚ] Qb)
    (h : ∀ x : H.E, s ⟨j x, H.mem_EQ j x⟩ = j (H.gal.symm g x)) : H.ActsAs s g := by
  intro j' x
  obtain ⟨σ, hσ⟩ := H.exists_aut j j'
  have h1 : (⟨j' x, H.mem_EQ j' x⟩ : H.EQ) = ⟨j (σ x), H.mem_EQ j _⟩ := Subtype.ext (hσ x)
  rw [h1, h, hσ, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, H.gal_comm]

variable (H)

theorem adjoin_cycZeta : IntermediateField.adjoin ℚ ({H.cycZeta} : Set (Cond.Cyc H.condN)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : x ∈ Algebra.adjoin ℚ ({H.cycZeta} : Set (Cond.Cyc H.condN)) := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top H.cycZeta_prim]; trivial
  exact algebra_adjoin_le_adjoin ℚ _ h1

theorem EQ_le_cycQ : H.EQ ≤ cycQ H.condN := by
  let κ : Cond.Cyc H.condN →ₐ[ℚ] Qb := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hz : IsPrimitiveRoot (κ H.cycZeta) H.condN := H.cycZeta_prim.map_of_injective κ.toRingHom.injective
  have hκ : κ.fieldRange = cycQ H.condN := by
    rw [AlgHom.fieldRange_eq_map, ← H.adjoin_cycZeta, adjoin_map, Set.image_singleton, cycQ_eq hz]
  rw [← H.range_eq (κ.comp H.cycEmb), ← hκ]
  rintro _ ⟨x, rfl⟩
  exact ⟨H.cycEmb x, rfl⟩

theorem artin (s : Qb ≃ₐ[ℚ] Qb) (u : (ZMod H.condN)ˣ) (hs : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val) :
    H.ActsAs (restr H.EQ s) (H.art u) := by
  let κ : Cond.Cyc H.condN →ₐ[ℚ] Qb := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨τ, hτ⟩ := Cond.aut H.condN (u : ZMod H.condN).val (ZMod.val_coe_unit_coprime u)
  have hτz := hτ H.cycZeta H.cycZeta_prim.pow_eq_one
  have hcomm : (s : Qb →ₐ[ℚ] Qb).comp κ = κ.comp (τ : Cond.Cyc H.condN →ₐ[ℚ] Cond.Cyc H.condN) := by
    refine AlgHom.ext_of_adjoin_eq_top (s := {H.cycZeta})
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top H.cycZeta_prim) ?_
    rintro _ rfl
    show s (κ H.cycZeta) = κ (τ H.cycZeta)
    rw [hτz, map_pow]
    refine hs _ ?_
    show κ H.cycZeta ^ H.condN = 1
    rw [← map_pow, H.cycZeta_prim.pow_eq_one, map_one]
  refine actsAs_of_one (κ.comp H.cycEmb) fun x => ?_
  show s (κ (H.cycEmb x)) = κ (H.cycEmb (H.gal.symm (H.art u) x))
  rw [H.art_spec u τ hτz x]
  exact DFunLike.congr_fun hcomm (H.cycEmb x)

theorem artin_apply (s : Qb ≃ₐ[ℚ] Qb) (u : (ZMod H.condN)ˣ) (hs : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val)
    (j : H.E →ₐ[ℚ] Qb) (x : H.E) : s (j x) = j (H.gal.symm (H.art u) x) := H.artin s u hs j x

end Formalism.HC.HostRaw

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem emb_conj {R : Ranks} (H : Formalism.BasicNotions.Host R) (g : R.GG) (x : H.E) :
    H.emb g (H.conj x) = starRingEnd ℂ (H.emb g x) := by
  exact H.conjE_apply (H.emb g) x

end Formalism.L2.Host
end
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def OverPF (p : ℕ) (v : HeightOneSpectrum (𝓞 H.F)) : Prop := ((p : ℕ) : 𝓞 H.F) ∈ v.asIdeal

def PvSet (𝔭 : HeightOneSpectrum (𝓞 H.K)) (v : HeightOneSpectrum (𝓞 H.F)) : Set (HeightOneSpectrum (𝓞 H.E)) :=
  {w | w ∈ aboveF (L := H.E) H.F v ∧ w.under (𝓞 H.K) = 𝔭}

structure PlacesOverCommonPrime where

  pK : HeightOneSpectrum (𝓞 H.K)

  pK' : HeightOneSpectrum (𝓞 H.K)
  pK_over : ((H.pde : ℕ) : 𝓞 H.K) ∈ pK.asIdeal
  pK'_over : ((H.pde' : ℕ) : 𝓞 H.K) ∈ pK'.asIdeal

  P : ∀ v : HeightOneSpectrum (𝓞 H.F), OverPF H H.pde v → HeightOneSpectrum (𝓞 H.E)

  P' : ∀ v : HeightOneSpectrum (𝓞 H.F), OverPF H H.pde' v → HeightOneSpectrum (𝓞 H.E)

  P_mem : ∀ v hv, P v hv ∈ PvSet H pK v
  P'_mem : ∀ v hv, P' v hv ∈ PvSet H pK' v

structure ClsRepK where
  rep : ClassGroup (𝓞 H.K) → (nonZeroDivisors (Ideal (𝓞 H.K)))
  rep_cls : ∀ c, ClassGroup.mk0 (rep c) = c

variable {H}

def idK (p : ℕ) : Ideal (𝓞 H.K) := Ideal.span {((p : ℕ) : 𝓞 H.K)}

def PrimeToPl (𝔞 : Ideal (𝓞 H.K)) (v : HeightOneSpectrum (𝓞 H.E)) : Prop := ¬ 𝔞 ≤ (v.under (𝓞 H.K)).asIdeal

end Formalism.L2.Host
end
end

section

noncomputable section

open NumberField Ideal

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem span_isPrime (p : ℕ) [hp : Fact p.Prime] : (span {(p : ℤ)}).IsPrime := by
  exact (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp.out)

theorem inertia_trivial (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) :
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 :=
  (H.der.frob p hnd P).2.2.2 σ

theorem ramificationIdx_eq_one (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] : P.ramificationIdx ℤ = 1 := by
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  have hbot : P.inertia (H.E ≃ₐ[ℚ] H.E) = ⊥ := by
    ext σ
    rw [Subgroup.mem_bot]
    exact AddSubgroup.mem_inertia.trans (inertia_trivial H p hnd P σ)
  rw [← Formalism.TwoAdicCyclotomicDecomposition.odd_card H.E p P, hbot, Subgroup.card_bot]

theorem ramificationIdx'_eq_one (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    (span {(p : ℤ)}).ramificationIdx' P = 1 := by
  have hne : (span {(p : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (span {(p : ℤ)}) P hne]
  exact ramificationIdx_eq_one H p hnd P

theorem map_eq_mul_coprime (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [hP : P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    ∃ I : Ideal (𝓞 H.E), (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) = P * I ∧ ¬ I ≤ P := by
  have hle : (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (Ideal.LiesOver.over)
  obtain ⟨I, hI⟩ := (Ideal.dvd_iff_le).2 hle
  refine ⟨I, hI, fun hIP => ?_⟩
  have h1 := ramificationIdx'_eq_one H p hnd P
  have h2 : (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) ≤ P ^ 2 := by
    rw [hI, pow_two]
    exact Ideal.mul_mono_right hIP
  exact (Ideal.ramificationIdx'_ne_one_iff hle).2 h2 h1

end Formalism.L2.Host
end
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Host.HChar

variable {L : Type} [Field L] [NumberField L] (χ : HChar L)

theorem productRule : χ.ProductRule := hecke_product_rule L χ

theorem val_principal (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : ∀ v, v ∉ S → χ.UnrAt v) (k : Lˣ) :
    (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), χ.val v ^ ordF v k) = (χ.inf k * ∏ v ∈ S, χ.locK v k)⁻¹ :=
  eq_inv_of_mul_eq_one_right (χ.productRule S hS k)

end Formalism.L2.Host.HChar
end
end
