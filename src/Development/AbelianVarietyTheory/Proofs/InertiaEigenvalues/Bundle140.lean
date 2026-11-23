module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle105
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle126
import Mathlib.Algebra.Module.StablyFree.Basic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle122
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle128
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle099
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle119
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Trace.Basic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Mathlib.Algebra.CharP.Algebra
import ReciprocityTheory.GaloisValuations.GlobalB
import ReciprocityTheory.GaloisValuations.GlobalA
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

noncomputable section
namespace GlobalTheory.PhiGam.Count
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

section
variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

theorem exists_le_sup (P Q : Submodule k U) [FiniteDimensional k (P.map Q.mkQ)] :
    ∃ F : Submodule k U, FiniteDimensional k F ∧ P ≤ F ⊔ Q := by
  obtain ⟨σ, hσ⟩ := Q.mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ Q)
  refine ⟨(P.map Q.mkQ).map σ, inferInstance, fun p hp => ?_⟩
  refine Submodule.mem_sup.2 ⟨σ (Q.mkQ p), ⟨_, ⟨p, hp, rfl⟩, rfl⟩, p - σ (Q.mkQ p), ?_, by abel⟩
  have h : Q.mkQ (σ (Q.mkQ p)) = Q.mkQ p := LinearMap.congr_fun hσ _
  exact (Submodule.Quotient.eq _).mp h.symm

theorem finite_of_le_sup {P Q F : Submodule k U} [FiniteDimensional k F] (h : P ≤ F ⊔ Q) :
    FiniteDimensional k (↥P ⧸ Q.submoduleOf P) := by
  have hker : LinearMap.ker (Q.mkQ ∘ₗ P.subtype) = Q.submoduleOf P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
  have hle : LinearMap.range (Q.mkQ ∘ₗ P.subtype) ≤ F.map Q.mkQ := by
    rintro _ ⟨⟨p, hp⟩, rfl⟩
    obtain ⟨f, hf, q, hq, rfl⟩ := Submodule.mem_sup.1 (h hp)
    refine ⟨f, hf, ?_⟩
    change Q.mkQ f = Q.mkQ (f + q)
    rw [map_add (f := _), show Q.mkQ q = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hq, add_zero]
  haveI : FiniteDimensional k (LinearMap.range (Q.mkQ ∘ₗ P.subtype)) :=
    Submodule.finiteDimensional_of_le hle
  rw [← hker]
  exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm

theorem gmult_eq_zero (T : Module.End k U) {P Q M : Submodule k U} (hPM : P ≤ M) (hM : ∀ p ∈ M, T p ∈ M)
    (x : k) (h : ∀ p ∈ M, T p - x • p ∈ Q → p ∈ Q) (hQ : ∀ p ∈ Q, T p ∈ Q) : gmult T P Q x = 0 := by
  set S : Module.End k U := T - algebraMap k (Module.End k U) x with hS
  have hSa : ∀ p, S p = T p - x • p := fun p => by simp [hS, Module.algebraMap_end_apply]
  have key : ∀ m : ℕ, ∀ p ∈ M, (S ^ m) p ∈ Q → p ∈ Q := by
    intro m
    induction m with
    | zero => intro p _ hp; simpa using hp
    | succ m ih =>
      intro p hp hq
      rw [pow_succ, Module.End.mul_apply] at hq
      have h1 : S p ∈ M := by rw [hSa]; exact M.sub_mem (hM p hp) (M.smul_mem _ hp)
      exact h p hp (hSa p ▸ ih _ h1 hq)
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply, hSa]
    exact Q.sub_mem (hQ _ hp) (Q.smul_mem _ hp)
  have hle : P ⊓ ⨆ m : ℕ, Q.comap (S ^ m) ≤ Q := by
    rintro p ⟨hp, hq⟩
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 hq
    exact key m p (hPM hp) hm
  unfold gmult
  rw [← hS, Submodule.submoduleOf_eq_top.2 hle]
  exact Module.finrank_zero_of_subsingleton

end

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem exists_le_sup_sh {N : Submodule k⟦X⟧ V} (hN : IsLat N) (m : ℕ) :
    ∃ F : Submodule k V, FiniteDimensional k F ∧
      N.restrictScalars k ≤ F ⊔ (sh m N).restrictScalars k := by
  induction m with
  | zero => exact ⟨⊥, inferInstance, by simp [sh_zero_eq]⟩
  | succ m ih =>
    obtain ⟨F, hF, h⟩ := ih
    haveI := Window.finite_quot (hN.shift m).1
    obtain ⟨F', hF', h'⟩ := exists_le_sup ((sh m N).restrictScalars k) ((sh 1 (sh m N)).restrictScalars k)
    rw [sh_sh_eq, add_comm] at h'
    refine ⟨F ⊔ F', inferInstance, h.trans ?_⟩
    rw [sup_assoc, Nat.cast_succ]
    exact sup_le_sup_left h' _

theorem graded_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (x : k) (h : sen g N (x + b) = 0) :
    ∀ y ∈ sh b N, nab g y - x • y ∈ sh (b + 1) N → y ∈ sh (b + 1) N := by
  apply GlobalTheory.PhiGam.Compare.graded_inj <;> assumption

theorem window_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (x : k) (s : ℕ) (h : ∀ j : ℕ, 1 ≤ j → j ≤ s → sen g N (x - j) = 0) :
    ∀ y ∈ sh (-s) N, nab g y - x • y ∈ N → y ∈ N := by
  induction s with
  | zero => intro y hy _; simpa [sh_zero_eq] using hy
  | succ s ih =>
    intro y hy hy'
    refine ih (fun j h1 h2 => h j h1 (Nat.le_succ_of_le h2)) y ?_ hy'
    have e : (-((s + 1 : ℕ) : ℤ)) + 1 = -(s : ℤ) := by push_cast; ring
    have := graded_inj R hg hN hC (-((s + 1 : ℕ) : ℤ)) x (by
      rw [Int.cast_neg, Int.cast_natCast, ← sub_eq_add_neg]; exact h _ (Nat.succ_pos s) le_rfl) y hy
    rw [e] at this
    refine this (sh_le_sh_of_le (a := 0) (by omega) N ?_)
    rwa [sh_zero_eq]

theorem sen_count : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ s : ℕ, P ≤ sh (-s) Q → ∀ x : k, sen g P x + qmult g P Q (x + 1) = sen g Q x + qmult g P Q x ∧ (qmult g P Q x ≠ 0 → ∃ j : ℕ, 1 ≤ j ∧ j ≤ s ∧ sen g Q (x - j) ≠ 0) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg P Q hP hQ hQP cP cQ s hs x
  constructor
  · have h1 : ∀ N : Submodule k⟦X⟧ V, sh 1 N ≤ N := fun N => by
      have := sh_le_sh_of_le (a := 1) (b := 0) (by norm_num) N
      rwa [sh_zero_eq] at this
    obtain ⟨F, hF, hle⟩ := exists_le_sup_sh hP (s + 1)
    have h2 : sh ((s + 1 : ℕ) : ℤ) P ≤ sh 1 Q := by
      have := sh_le_sh ((s + 1 : ℕ) : ℤ) hs
      rwa [sh_sh_eq, show ((s + 1 : ℕ) : ℤ) + -(s : ℤ) = 1 by push_cast; ring] at this
    have hfin : FiniteDimensional k (↥(P.restrictScalars k) ⧸
        ((sh 1 Q).restrictScalars k).submoduleOf (P.restrictScalars k)) :=
      finite_of_le_sup (F := F) (hle.trans (sup_le_sup_left (fun _ hy => h2 hy) _))
    have a1 := GlobalTheory.PhiGam.GmultAdd.main (nab g) (P.restrictScalars k) ((sh 1 P).restrictScalars k)
      ((sh 1 Q).restrictScalars k) (fun _ hy => sh_le_sh 1 hQP hy) (fun _ hy => h1 P hy)
      (fun _ hy => Window.nab_mem cP hy) (fun _ hy => Window.nab_mem_sh R hg cP 1 hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ 1 hy) hfin x
    have a2 := GlobalTheory.PhiGam.GmultAdd.main (nab g) (P.restrictScalars k) (Q.restrictScalars k)
      ((sh 1 Q).restrictScalars k) (fun _ hy => h1 Q hy) (fun _ hy => hQP hy)
      (fun _ hy => Window.nab_mem cP hy) (fun _ hy => Window.nab_mem cQ hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ 1 hy) hfin x
    rw [← GlobalTheory.T.quotientMultiplicity_shift_lattice_quotient R g hg P Q hP hQ hQP cP cQ x]
    unfold sen qmult
    omega
  · intro hne
    by_contra hno
    push Not at hno
    exact hne (gmult_eq_zero (nab g) (M := (sh (-s) Q).restrictScalars k) (fun _ hy => hs hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ _ hy) x (window_inj R hg hQ.1 cQ x s hno)
      (fun _ hy => Window.nab_mem cQ hy))

end GlobalTheory.PhiGam.Count
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem trace_eq_add_star : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E], ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y := by
  apply GlobalTheory.JR.NormInt.traceE <;> assumption

end GlobalTheory
end

section

open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.JR

theorem Unram.mem_range_of_star_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (y : E), star y = y → ∃ x : F, algebraMap F E x = y := by
  apply GlobalTheory.JR.Step.UNormal.exists_algebraMap_of_star_eq <;> assumption

end GlobalTheory.JR
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open Pointwise

namespace GlobalTheory.GaloisLift

theorem cong_pow_of_cong_pow_int (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) {σ : G E Ω} (hdec : σ ∈ Dec (F := E) A) {q : ℕ}
    (hcong : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b ^ q) < 1) :
    ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 := by
  have hdec' : σ • A = A := hdec
  intro x hx
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den E A hx
  have hcs := hcong s hs
  have hct := hcong t ht
  have hvt : A.valuation t ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ht)
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (hs.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)))) ?_
    have h3 : ¬ (σ • A).valuation (σ s) < 1 := by
      rw [smul_valuation_lt_one_iff]
      have : (σ⁻¹ : Ω ≃ₐ[E] Ω) (σ s) = s := by
        show (σ⁻¹ * σ) s = s
        simp
      rw [this, hs1]
      exact lt_irrefl 1
    rw [hdec'] at h3
    exact not_lt.mp h3
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s ^ q * σ s * (σ x - x ^ q) = s ^ q * (σ t - t ^ q) + t ^ q * (s ^ q - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s ^ q * σ s * (σ x - x ^ q)) < 1 := by
    rw [key]
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul, Valuation.map_pow, hs1, one_pow, one_mul]
      exact hct
    · rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation (t ^ q) * A.valuation (σ s - s ^ q) ≤ 1 * A.valuation (σ s - s ^ q) :=
            mul_le_mul_left (by rw [Valuation.map_pow]; exact pow_le_one' hvt q) _
        _ < 1 := by rw [one_mul]; exact hcs
  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hs1, hσs, one_pow, one_mul,
    one_mul] at hv
  exact hv

theorem lift_resAut_of_fixes (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (K : IntermediateField E Ω) [FiniteDimensional E K]
    (σ₀ : G E Ω) (hσ₀ : σ₀ ∈ Dec (F := E) A)
    (hK : ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (σ₀ z - z) < 1) :
    ∃ ρ : G E Ω, (∀ z ∈ K, ρ z = z) ∧ ρ ∈ Dec (F := E) A ∧
      ∀ b : Ω, IsIntegral ℤ b → A.valuation (ρ b - σ₀ b) < 1 := by
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  letI : TopologicalSpace (IntCl K Ω) := ⊥
  haveI : DiscreteTopology (IntCl K Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl K Ω
  haveI := isInvariant_intCl K Ω
  set Q := primeBelow (F := K) A with hQ
  set P := Q.under (𝓞 K) with hP
  haveI : Q.LiesOver P := ⟨rfl⟩

  have hint : ∀ (g : G E Ω) (b : IntCl K Ω), IsIntegral (𝓞 K) (g (b : Ω)) := fun g b =>
    ((isIntegral_int_of_isIntegral b.2).map (g.toAlgHom.restrictScalars ℤ)).tower_top
  let e : IntCl K Ω ≃+* IntCl K Ω :=
    { toFun := fun b => ⟨σ₀ b, hint σ₀ b⟩
      invFun := fun b => ⟨σ₀⁻¹ b, hint σ₀⁻¹ b⟩
      left_inv := fun b => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (mul_inv_apply (b : Ω))
      map_mul' := fun a b => Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have he : ∀ b : IntCl K Ω, ((e b : IntCl K Ω) : Ω) = σ₀ b := fun _ => rfl
  have hQe : Q = Q.map (e : IntCl K Ω →+* IntCl K Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap]
    show A.valuation (b : Ω) < 1 ↔ A.valuation (σ₀⁻¹ (b : Ω)) < 1
    exact (valuation_apply_lt_one_iff ((Dec (F := E) A).inv_mem hσ₀) _).symm
  let ψ₀ : (IntCl K Ω ⧸ Q) ≃+* (IntCl K Ω ⧸ Q) := Ideal.quotientEquiv Q Q e hQe
  have hψ₀ : ∀ b, ψ₀ (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (e b) := fun _ => rfl
  have hlin : ∀ x : 𝓞 K ⧸ P, ψ₀ (algebraMap (𝓞 K ⧸ P) (IntCl K Ω ⧸ Q) x) =
      algebraMap (𝓞 K ⧸ P) (IntCl K Ω ⧸ Q) x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, hψ₀, Ideal.Quotient.eq]
    have hz : ((algebraMap (𝓞 K) (IntCl K Ω) a : IntCl K Ω) : Ω) ∈ K := ((a : K)).2
    have := hK _ hz (valuation_le_one_intCl A _)
    exact this
  let ψ : (IntCl K Ω ⧸ Q) ≃ₐ[𝓞 K ⧸ P] (IntCl K Ω ⧸ Q) := AlgEquiv.ofRingEquiv (f := ψ₀) hlin
  obtain ⟨⟨ρ₀, hρ₀Q⟩, hρ₀⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[K] Ω) P Q ψ
  have hρ₀Q' : ρ₀ • Q = Q := hρ₀Q
  have hcong : ∀ b : IntCl K Ω, A.valuation (ρ₀ (b : Ω) - σ₀ b) < 1 := by
    intro b
    have h1 : Ideal.Quotient.mk Q (ρ₀ • b) = Ideal.Quotient.mk Q (e b) :=
      DFunLike.congr_fun hρ₀ (Ideal.Quotient.mk Q b)
    have h2 : ρ₀ • b - e b ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, sub_self]
    exact h2
  have hdec : ρ₀ • A = A := by
    refine eq_of_valuation_lt_one_iff K fun b hb => ?_
    let b' : IntCl K Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := K) (ρ₀ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hρ₀Q']
  refine ⟨ρ₀.restrictScalars E, fun z hz => ρ₀.commutes ⟨z, hz⟩, ?_, fun b hb => hcong ⟨b, hb.tower_top⟩⟩
  show (ρ₀.restrictScalars E) • A = A
  conv_rhs => rw [← hdec]
  ext x
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem exists_fixing_actsAs : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w)
    (K : IntermediateField E Ω) [FiniteDimensional E K], ∀ d ∈ Dec (F := E) A, ∀ j : ℕ,
      (∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1) →
      ∃ ρ : G E Ω, (∀ z ∈ K, ρ z = z) ∧ ActsAs A (normV w) (d * ρ) j 0 := by
  intro E Ω _ _ _ _ _ A w h K _ d hd j hdK
  obtain ⟨φ, hφ⟩ := exists_isFrob h
  have hφ1 : ActsAs A (normV w) φ 1 0 := actsAs_one_iff.mpr hφ
  have hpow : ∀ n : ℕ, ActsAs A (normV w) (φ ^ n) n 0 := by
    intro n
    induction n with
    | zero => exact ⟨(Dec (F := E) A).one_mem, fun x _ => by simp⟩
    | succ n ih => simpa [pow_succ] using ih.mul hφ1
  have hφj := hpow j
  set σ₀ : G E Ω := d⁻¹ * φ ^ j with hσ₀def
  have hσ₀ : σ₀ ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hd) hφj.1
  have hK : ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (σ₀ z - z) < 1 := by
    intro z hz hz1
    rw [← valuation_apply_lt_one_iff hd, map_sub]
    have e1 : d (σ₀ z) = (φ ^ j) z := by
      rw [hσ₀def, AlgEquiv.mul_apply, mul_inv_apply]
    rw [e1]
    have h1 := hφj.2 z hz1
    simp only [pow_zero, pow_one] at h1
    exact cong_trans h1 (cong_symm (hdK z hz hz1))
  obtain ⟨ρ, hρK, hρA, hρc⟩ := lift_resAut_of_fixes E Ω A K σ₀ hσ₀ hK
  set τ : G E Ω := σ₀⁻¹ * ρ with hτdef
  have hτ : τ ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hσ₀) hρA
  have hτc : ∀ b : Ω, IsIntegral ℤ b → A.valuation (τ b - b ^ 1) < 1 := by
    intro b hb
    rw [pow_one, ← valuation_apply_lt_one_iff hσ₀, map_sub]
    have e3 : σ₀ (τ b) = ρ b := mul_inv_apply (ρ b)
    rw [e3]
    exact hρc b hb
  have hτI : ActsAs A (normV w) τ 0 0 :=
    ⟨hτ, fun x hx => by simpa using cong_pow_of_cong_pow_int E Ω A hτ hτc x hx⟩
  refine ⟨ρ, hρK, ?_⟩
  have e2 : d * ρ = φ ^ j * τ := by
    rw [hτdef, hσ₀def]; group
  rw [e2]
  simpa using hφj.mul hτI

end GlobalTheory.GaloisLift
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

open NumberField IsDedekindDomain Polynomial in
private theorem dvd_of_primitiveRoot_pow_pow_eq_self {Ω : Type} [Field Ω] {q k m : ℕ} (hq : 1 < q)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ (q ^ k - 1)) (hpos : 0 < q ^ k - 1) (hm : ζ ^ q ^ m = ζ) :
    k ∣ m := by
  have hz : ζ ≠ 0 := hζ.ne_zero hpos.ne'
  have h1 : q ^ k - 1 ∣ q ^ m - 1 := by
    apply hζ.dvd_of_pow_eq_one
    have h0 : ζ ^ (q ^ m - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega)), one_mul]
      exact hm
    exact mul_right_cancel₀ hz h0
  have h2 := Nat.pow_sub_one_gcd_pow_sub_one q k m
  rw [Nat.gcd_eq_left h1] at h2
  have h3 : q ^ k = q ^ Nat.gcd k m := by
    have := Nat.one_le_pow (Nat.gcd k m) q (by omega)
    have := Nat.one_le_pow k q (by omega)
    omega
  have h4 := Nat.pow_right_injective hq h3
  rw [h4]
  exact Nat.gcd_dvd_right k m


open NumberField IsDedekindDomain Polynomial in
theorem _root_.GlobalTheory.exists_fixed_dvd_deg : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (k : ℕ), 0 < k →
    ∃ ζ : Ω, ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) ζ = ζ → (k : ℤ) ∣ _root_.GlobalTheory.WeilDeligne.deg σ := by
  intro E Ω _ _ _ _ _ A w h k hk
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hq1 : 1 < _root_.Formalism.ConjugateSelfDual.normV w := _root_.GlobalTheory.WeilDeligne.one_lt_normV w
  have hpos : 0 < _root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hk.ne' hq1)
  haveI : NeZero ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : Ω) := ⟨by
    rw [← map_natCast (algebraMap E Ω)]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hpos.ne')⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1)
  have hvN : ¬ A.valuation ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : Ω) < 1 := by
    have hmem : ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : 𝓞 E) ∉ w.asIdeal := by
      intro hN
      have h1 : ((_root_.Formalism.ConjugateSelfDual.normV w : ℕ) : 𝓞 E) ∈ w.asIdeal := by
        simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using Ideal.absNorm_mem w.asIdeal
      have h2 : ((_root_.Formalism.ConjugateSelfDual.normV w : ℕ) : 𝓞 E) ^ k ∈ w.asIdeal := Ideal.pow_mem_of_mem _ h1 _ hk
      have h3 : ((_root_.Formalism.ConjugateSelfDual.normV w : ℕ) : 𝓞 E) ^ k - ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : 𝓞 E) = 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
        ring
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h3 ▸ sub_mem h2 hN))
    simpa using _root_.ReciprocityTheory.Gal.not_valuation_lt_one_of_isPlaceOver hmem h 1
  have hζv : A.valuation ζ ≤ 1 := le_of_eq (_root_.ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hpos.ne' hζ.pow_eq_one)
  have hroot : ∀ m : ℕ, (ζ ^ _root_.Formalism.ConjugateSelfDual.normV w ^ m) ^ (_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1) = 1 := by
    intro m
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨ζ, fun σ hσ => ?_⟩
  rcases le_or_gt 0 (_root_.GlobalTheory.WeilDeligne.deg σ) with hd | hd
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hd
    have hact := _root_.GlobalTheory.WeilDeligne.actsAs_of_deg (σ := σ) (a := m) (b := 0)
      (by rw [hm]; simp)
    have hv := hact.2 ζ hζv
    rw [pow_zero, pow_one, hσ] at hv
    have heq := _root_.ReciprocityTheory.Gal.eq_of_pow_eq_one A hvN hζ.pow_eq_one (hroot m) hv
    rw [hm]
    exact Int.natCast_dvd_natCast.2 (dvd_of_primitiveRoot_pow_pow_eq_self hq1 hζ hpos heq.symm)
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hd.le)
    have hact := _root_.GlobalTheory.WeilDeligne.actsAs_of_deg (σ := σ) (a := 0) (b := m)
      (by rw [← hm]; simp)
    have hv := hact.2 ζ hζv
    rw [pow_zero, pow_one, hσ] at hv
    have heq := _root_.ReciprocityTheory.Gal.eq_of_pow_eq_one A hvN (hroot m) hζ.pow_eq_one hv
    rw [← neg_neg (_root_.GlobalTheory.WeilDeligne.deg σ), hm, dvd_neg]
    exact Int.natCast_dvd_natCast.2 (dvd_of_primitiveRoot_pow_pow_eq_self hq1 hζ hpos heq)

end GlobalTheory
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.isUnramifiedAt_of_isUnramifiedInGaloisExtension : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)}, GlobalTheory.NT.UnramIn L 𝔭 → ∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver 𝔭.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) P := by
  first | exact @GlobalTheory.NT.isUnramifiedAt_of_unramIn | exact GlobalTheory.NT.isUnramifiedAt_of_unramIn | (intros; apply GlobalTheory.NT.isUnramifiedAt_of_unramIn <;> assumption)
end

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.additiveSystem_generalLemma_orderOne : GLOnto 1 ∧ GLCount 1 := by
  first | exact @GlobalTheory.PMonE.gl1 | exact GlobalTheory.PMonE.gl1 | (intros; apply GlobalTheory.PMonE.gl1 <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.generalLinear_haar_isMulRightInvariant_unramified : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (letI := M.mG; M.μG.IsMulRightInvariant) := by
  first | exact @GlobalTheory.JR.gl_unimodular | exact GlobalTheory.JR.gl_unimodular | (intros; apply GlobalTheory.JR.gl_unimodular <;> assumption)
end
