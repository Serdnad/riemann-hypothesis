module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraFrobeniusQuadraticModPrimePow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle380
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesEqOfCongruentValuesAtPrimitiveRoots
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle322
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle365
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle379
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle376
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle309
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle337
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle275
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertPrimeOrderParitySignRadicalIntegralForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle375
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle338
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle343
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveCharacterTwist
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Int
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.eichlerShimura_frobenius_quadratic_mod_prime_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ n : ℕ, ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s → ∀ b ∈ X.B N l w, ∀ u, (X.galB l s (X.galB l s b) - X.heckeT N l q (X.galB l s b) + ((q : ℤ_[l]) ^ (w + 1)) • X.diam N l q b) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  first | exact @GlobalTheory.KZ.eichlerShimura_B_mod | exact GlobalTheory.KZ.eichlerShimura_B_mod | (intros; apply GlobalTheory.KZ.eichlerShimura_B_mod <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.ImZ

variable {l : ℕ} [Fact l.Prime]

theorem norm_coe_unit (u : ℤ_[l]ˣ) : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := by
  exact PadicInt.norm_def.symm.trans (PadicInt.isUnit_iff.mp u.isUnit)

def logU (u : ℤ_[l]ˣ) : ℤ_[l] :=
  ⟨Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l]), (GlobalTheory.PadicLogUnits.logZl_hom l).2.2.1 _ (norm_coe_unit u)⟩

theorem coe_logU (u : ℤ_[l]ˣ) : ((logU u : ℤ_[l]) : ℚ_[l]) = Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l]) := rfl

theorem logU_mul (u w : ℤ_[l]ˣ) : logU (u * w) = logU u + logU w := by
  apply Subtype.ext
  show Formalism.MainNotions.LocalSituation.logZl l (((u * w : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l]) + Formalism.MainNotions.LocalSituation.logZl l ((w : ℤ_[l]) : ℚ_[l])
  rw [Units.val_mul, PadicInt.coe_mul]
  exact (GlobalTheory.PadicLogUnits.logZl_hom l).1 _ _ (norm_coe_unit u) (norm_coe_unit w)

theorem logU_one : logU (1 : ℤ_[l]ˣ) = 0 := by
  have h := logU_mul (l := l) 1 1
  rw [mul_one] at h
  linear_combination -h

def logHom : ℤ_[l]ˣ →* Multiplicative ℤ_[l] where
  toFun u := Multiplicative.ofAdd (logU u)
  map_one' := by rw [logU_one]; rfl
  map_mul' u w := by rw [logU_mul]; rfl

theorem continuous_logHom : Continuous (logHom (l := l)) := by
  have h1 : Continuous fun u : ℤ_[l]ˣ => ((u : ℤ_[l]) : ℚ_[l]) :=
    (continuous_subtype_val : Continuous (fun x : ℤ_[l] => (x : ℚ_[l]))).comp (Units.continuous_val (M := ℤ_[l]))
  have h2 : Continuous fun u : ℤ_[l]ˣ => Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l]) :=
    (GlobalTheory.PadicLogUnits.logZl_hom l).2.1.comp_continuous h1 (fun u => norm_coe_unit u)
  exact continuous_ofAdd.comp (h2.subtype_mk _)

theorem cycZ_eq_one_of_eps {Ω : Type} [Field Ω] [Algebra ℚ Ω] {z : G ℚ Ω} (h : eps l z = 1) :
    cycZ ℚ Ω l z = 1 := by
  have h' : ((cycZ ℚ Ω l z : ℤ_[l]) : ℚ_[l]) = 1 := by
    have h2 := h
    simp [eps, cycBar] at h2
    exact h2
  apply Units.ext
  exact PadicInt.ext (h'.trans PadicInt.coe_one.symm)

theorem isIrr_of_comp {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (H : Subgroup Γ)
    (h : IsIrr (r.comp H.subtype)) : IsIrr r := by
  obtain ⟨h1, _, h3⟩ := h
  exact ⟨h1, fun _ _ _ => Submodule.mem_top, fun W' hW' hinv => h3 W' hW' fun g v hv => hinv g v hv⟩

theorem exists_cycZ_nat (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (hl : l ≠ 2) :
    ∃ (σ : G ℚ Ω) (n : ℕ), 2 ≤ n ∧ ((cycZ ℚ Ω l σ : ℤ_[l]) = n) := by
  haveI : (Ideal.span {((2 : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 ℚ) (Ideal.span {((2 : ℕ) : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 ℚ)).injective_int]; exact bot_le)
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField ℚ)⟩
  have hlv : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro h
    have h2 : ((l : ℕ) : ℤ) ∈ M.comap (algebraMap ℤ (𝓞 ℚ)) := by
      rw [Ideal.mem_comap, map_natCast]; exact h
    change ((l : ℕ) : ℤ) ∈ Ideal.under ℤ M at h2
    rw [hc, Ideal.mem_span_singleton] at h2
    have h3 : (2 : ℕ) ∣ l := by exact_mod_cast h2
    exact hl ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out)).mp h3).symm
  have hσ := cycZ_of_isFrob (l := l) hlv (isPlaceOver_placeOf Ω v) (isFrob_frobOf Ω v)
  refine ⟨frobOf Ω v, normV v, ?_, hσ⟩
  have h0 : normV v ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hσ
    exact (cycZ ℚ Ω l (frobOf Ω v)).ne_zero hσ
  have h1 : normV v ≠ 1 := by
    intro h1
    have : Nat.card (𝓞 ℚ ⧸ v.asIdeal) = 1 := h1
    obtain ⟨hs, _⟩ := Nat.card_eq_one_iff_unique.mp this
    haveI : v.asIdeal.IsMaximal := hM
    haveI : Nontrivial (𝓞 ℚ ⧸ v.asIdeal) := inferInstance
    exact not_subsingleton _ hs
  omega

theorem logHom_ne_one (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (hl : l ≠ 2) :
    ∃ σ : G ℚ Ω, logHom (cycZ ℚ Ω l σ) ≠ 1 := by
  obtain ⟨σ, n, hn, hσ⟩ := exists_cycZ_nat (l := l) Ω hl
  refine ⟨σ ^ (l - 1), fun h => ?_⟩
  have hl1 : 1 ≤ l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have hval : ((cycZ ℚ Ω l (σ ^ (l - 1)) : ℤ_[l]) : ℚ_[l]) = ((n ^ (l - 1) : ℕ) : ℚ_[l]) := by
    rw [map_pow, Units.val_pow_eq_pow_val, hσ]; push_cast; rfl
  have h0 : logU (cycZ ℚ Ω l (σ ^ (l - 1))) = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa [logHom] using this
  have h0' : Formalism.MainNotions.LocalSituation.logZl l ((n ^ (l - 1) : ℕ) : ℚ_[l]) = 0 := by
    rw [← hval, ← coe_logU, h0]; rfl

  have hnd : ¬ l ∣ n := by
    rintro ⟨k, rfl⟩
    have hu : IsUnit ((l * k : ℕ) : ℤ_[l]) := by rw [← hσ]; exact Units.isUnit _
    rw [Nat.cast_mul] at hu
    have hlu := PadicInt.isUnit_iff.mp (isUnit_of_mul_isUnit_left hu)
    rw [PadicInt.norm_p] at hlu
    have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    linarith

  have hdvd : ((l : ℤ)) ^ 1 ∣ ((n : ℤ) ^ (l - 1) - 1) := by
    rw [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hz : ((n : ℤ) : ZMod l) ≠ 0 := by
      rw [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff]; exact hnd
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one (by simpa using hz), sub_self]
  have hnorm := (Padic.norm_int_le_pow_iff_dvd (p := l) _ 1).mpr hdvd
  have hle : ‖((n ^ (l - 1) : ℕ) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
    have : ((((n : ℤ) ^ (l - 1) - 1 : ℤ)) : ℚ_[l]) = ((n ^ (l - 1) : ℕ) : ℚ_[l]) - 1 := by push_cast; ring
    rw [← this]; exact hnorm
  have heq := (GlobalTheory.PadicLogUnits.logZl_hom l).2.2.2 1 le_rfl (fun h2 => absurd h2 hl) _ hle
  rw [h0', norm_zero] at heq
  have hne : ((n ^ (l - 1) : ℕ) : ℚ_[l]) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    have : 2 ≤ n ^ (l - 1) := le_trans hn (Nat.le_self_pow (by omega) n)
    intro he
    have : n ^ (l - 1) = 1 := by exact_mod_cast he
    omega
  exact hne (norm_eq_zero.mp heq.symm)

end GlobalTheory.Ord2.ImZ

namespace GlobalTheory.Ord2


open GlobalTheory.Ord2.ImZ in
theorem exists_ker_eps_ne_one : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ z ∈ W.ker, eps l z ≠ 1 := by
  intro l _ Ω _ _ _ e S A W h
  by_contra hne
  push_neg at hne
  obtain ⟨c, hc⟩ := h.int
  let lam : G ℚ Ω →* Multiplicative ℤ_[l] := logHom.comp (cycZ ℚ Ω l)
  have hlamc : Continuous lam := continuous_logHom.comp (continuous_cycZ ℚ Ω l)
  have hdet : ∀ g, ((W g : Matrix (Fin 2) (Fin 2) (Qbar l))).det ^ 2 = 1 := by
    intro g
    have := congrArg (fun u : (Qbar l)ˣ => (u : Qbar l)) (DFunLike.congr_fun h.det2 g)
    simpa [dt] using this
  have hker : W.ker ≤ lam.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    show logHom (cycZ ℚ Ω l z) = 1
    rw [cycZ_eq_one_of_eps (hne z hz), map_one]
  have hlam := GlobalTheory.T.hom_padicInt_trivial_of_irreducible_compact_rep l c (G ℚ Ω) W lam h.cont hc hdet (isIrr_of_comp W _ h.irr) hlamc hker
  obtain ⟨σ, hσ⟩ := logHom_ne_one (l := l) Ω h.l_odd
  exact hσ (DFunLike.congr_fun hlam σ)

end GlobalTheory.Ord2
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.BrTame

variable {l : ℕ} [Fact l.Prime]

def ballSub (r : ℝ) (hr : 0 ≤ r) : AddSubgroup (PadicAlgCl l) where
  carrier := {x | ‖x‖ ≤ r}
  zero_mem' := by simpa using hr
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  neg_mem' := fun {a} ha => by simpa [Set.mem_setOf_eq, norm_neg] using ha

theorem mem_ballSub {r : ℝ} {hr : 0 ≤ r} {x : PadicAlgCl l} : x ∈ ballSub r hr ↔ ‖x‖ ≤ r := Iff.rfl

theorem cg_iff {n : ℕ} {a b : Qbar l} : Cg n a b ↔ a - b ∈ ballSub (l := l) ‖((l : ℕ) : Qbar l) ^ n‖ (norm_nonneg _) := Iff.rfl

theorem mul_mem_ballSub {r : ℝ} {hr : 0 ≤ r} {k x : PadicAlgCl l} (hk : ‖k‖ ≤ 1) (hx : x ∈ ballSub r hr) :
    k * x ∈ ballSub r hr := by
  rw [mem_ballSub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hk).trans hx

theorem norm_le_one_of_int (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  norm_le_one_of_int x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

end GlobalTheory.BrTame


open GlobalTheory.BrTame in
theorem GlobalTheory.br_tame : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (h : G ℚ Ω → Qbar l) (σ : G ℚ Ω), 1 ≤ n → IsPlaceOver B w → l ^ n ∣ normV w - 1 → (∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) → (∀ s, h s ∈ c.O) → (∀ s ∈ Dec (F := ℚ) B, ∀ t ∈ Dec (F := ℚ) B, Cg n (h (s * t)) (h s + h t)) → (∀ s ∈ Ine (F := ℚ) B, Cg n (h s) 0) → Cob2 c n (Dec (F := ℚ) B) (fun s t => (((ψ s).toAdd.val : ℕ) : Qbar l) * h t) → σ ∈ Dec (F := ℚ) B → Cg n (h σ) 0 := by
  intro l _ Ω _ _ _ c n w B ψ h σ hn hB hdiv ⟨τ, hτ, hψτ⟩ hO _ hIne ⟨u, hucont, huO, hu⟩ hσ
  set S := ballSub (l := l) ‖((l : ℕ) : Qbar l) ^ n‖ (norm_nonneg _) with hS
  have hu1 : ∀ s, ‖u s‖ ≤ 1 := fun s => norm_le_one_of_mem c (huO s)
  have heps : ∀ s ∈ Dec (F := ℚ) B, eps l s - 1 ∈ S := fun s hs => GlobalTheory.T.cyclotomicChar_congruent_one_on_decompositionGroup l Ω n w B hB hdiv hn s hs
  have hnat : ∀ k : ℕ, ‖((k : ℕ) : Qbar l)‖ ≤ 1 := fun k => IsUltrametricDist.norm_natCast_le_one _ k
  have hmul : ∀ k x : Qbar l, ‖k‖ ≤ 1 → x ∈ S → k * x ∈ S := fun k x hk hx => mul_mem_ballSub hk hx
  have hIne' : ∀ s ∈ Ine (F := ℚ) B, h s ∈ S := fun s hs => by
    have := cg_iff.1 (hIne s hs)
    rwa [sub_zero] at this
  have hIneDec : ∀ s ∈ Ine (F := ℚ) B, s ∈ Dec (F := ℚ) B := fun s hs => Ine_le_Dec B hs

  set T := ballSub (l := l) 1 zero_le_one with hT
  let M := T ⧸ S.comap T.subtype
  let f : G ℚ Ω → M := fun s => QuotientAddGroup.mk ⟨u s, hu1 s⟩
  have hf : ∀ s t, f s = f t ↔ u s - u t ∈ S := fun s t => by
    show (QuotientAddGroup.mk _ : M) = QuotientAddGroup.mk _ ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_comap]
    change -u s + u t ∈ S ↔ _
    have e : -u s + u t = -(u s - u t) := by ring
    rw [e, S.neg_mem_iff]
  have hlpos : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have htors : ∀ x : M, l ^ n • x = 0 := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H y =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap, AddSubgroup.coe_subtype,
        AddSubgroup.coe_nsmul, nsmul_eq_mul, mem_ballSub, norm_mul, Nat.cast_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) y.2
  have hloc : IsLocallyConstant (fun s : Ine (F := ℚ) B => f s) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    have hc : Continuous (fun s : Ine (F := ℚ) B => u s) :=
      (hucont.mono (fun s hs => hIneDec s hs)).comp_continuous continuous_subtype_val (fun s => s.2)
    refine ⟨(fun s : Ine (F := ℚ) B => u s) ⁻¹' Metric.ball (u x) ‖((l : ℕ) : Qbar l) ^ n‖,
      Metric.isOpen_ball.preimage hc, Metric.mem_ball_self hlpos, fun y hy => ?_⟩
    rw [hf, mem_ballSub]
    have := Metric.mem_ball.1 hy
    rw [dist_eq_norm] at this
    exact this.le
  have hadd : ∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, f (s * t) = f s + f t := by
    intro s hs t ht
    have e : f s + f t = QuotientAddGroup.mk (⟨u s, hu1 s⟩ + ⟨u t, hu1 t⟩ : T) := rfl
    rw [e]
    show (QuotientAddGroup.mk _ : M) = QuotientAddGroup.mk _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_comap]
    change -u (s * t) + (u s + u t) ∈ S
    have h1 := hu s (hIneDec s hs) t (hIneDec t ht)
    have h2 := hmul _ _ (hnat ((ψ s).toAdd.val)) (hIne' t ht)
    have h3 := hmul _ _ (hu1 t) (heps s (hIneDec s hs))
    rw [cg_iff] at h1
    have e2 : -u (s * t) + (u s + u t) =
        -((((ψ s).toAdd.val : ℕ) : Qbar l) * h t - (eps l s * u t - u (s * t) + u s))
          + (((ψ s).toAdd.val : ℕ) : Qbar l) * h t - u t * (eps l s - 1) := by ring
    rw [e2]
    exact S.sub_mem (S.add_mem (S.neg_mem h1) h2) h3
  have hconj := GlobalTheory.T.inertiaTorsionQuotient_conj_invariant_decomposition l Ω n w B M f hB hdiv hn htors hloc hadd σ hσ τ hτ
  rw [hf] at hconj
  set τ' := σ * τ * σ⁻¹ with hτ'
  have hτ'I : τ' ∈ Ine (F := ℚ) B := conj_mem_Ine hσ hτ
  have hprod : τ' * σ = σ * τ := by rw [hτ']; group
  have hψ' : ((ψ τ').toAdd.val : Qbar l) = 1 := by
    have e : ψ τ' = ψ τ := by rw [hτ', map_mul, map_mul, mul_comm (ψ σ), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    have hl1 : 1 < l ^ n := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
    rw [e, hψτ, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hl1, Nat.cast_one]
  have hA := hu τ' (hIneDec τ' hτ'I) σ hσ
  have hB' := hu σ hσ τ (hIneDec τ hτ)
  dsimp only at hA hB'
  rw [cg_iff, hprod, hψ', one_mul] at hA
  rw [cg_iff] at hB'
  have hC := hmul _ _ (hnat ((ψ σ).toAdd.val)) (hIne' τ hτ)
  have hD := hmul _ _ (hu1 σ) (heps τ' (hIneDec τ' hτ'I))
  have hF := hmul _ _ (hu1 τ) (heps σ hσ)
  rw [cg_iff, sub_zero]
  have e : h σ = (h σ - (eps l τ' * u σ - u (σ * τ) + u τ')) + u σ * (eps l τ' - 1) + (u τ' - u τ)
      - ((((ψ σ).toAdd.val : ℕ) : Qbar l) * h τ - (eps l σ * u τ - u (σ * τ) + u σ))
      + (((ψ σ).toAdd.val : ℕ) : Qbar l) * h τ - u τ * (eps l σ - 1) := by ring
  rw [e]
  exact S.sub_mem (S.add_mem (S.sub_mem (S.add_mem (S.add_mem hA hD) hconj) hB') hC) hF
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4
open scoped TensorProduct MatrixGroups Matrix
open GlobalTheory.LambdaValuationPowers

theorem _root_.GlobalTheory.T.exists_admissible_hecke_projection_nonvanishing : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ)
  [Fact l.Prime] (e : ℕ) (S : Finset Pl) (W : R2 Ω l) (ψ : ZMod l → Qbar l) (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1))
  (j : Ω →+* Qbar l),
  Nf e S A W → 1 ≤ e →
  (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
  (∀ x ∈ A, ‖j x‖ ≤ 1) →
  ∀ (ev : Letter → Qbar l) (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l)) (F : Finset Ω),
  (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) →
  (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) →
  (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
    (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e - 1 + 1)) →
  (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ev (Letter.T q) = ι.symm (gN.a q)) →
  ∀ (χ : ℕ → ℤ_[l]), (∀ d : ℕ, Nat.Coprime d N → ev (Letter.D d) = ((χ d : ℤ_[l]) : Qbar l)) →
  ∀ (m : ℕ) (π : Fin m → (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (Fin 2 → Qbar l))
    (σ : Fin m → (Fin 2 → Qbar l) →ₗ[Qbar l] (Qbar l ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra (Qbar l) Letter),
  P ∈ admissibleLettersSubalgebra (Qbar l) N l → FreeAlgebra.lift (Qbar l) ev P = 1 → (∀ i v, σ i v ∈ X.VB N l (2 * e - 1) (Qbar l)) →
  (∀ i s, ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.galV l (Qbar l) s x) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ π i x) →
  (∀ i s v, X.galV l (Qbar l) s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v)) →
  (∀ i (T : Letter) v, GlobalTheory.KZ.admitted N l T → X.opV N l (Qbar l) T (σ i v) = ev T • σ i v) →
  (∀ i (T : Letter), GlobalTheory.KZ.admitted N l T → ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.opV N l (Qbar l) T x) = ev T • π i x) →
  (∀ i i' v, π i (σ i' v) = if i = i' then v else 0) →
  (∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P x = ∑ i, σ i (π i x)) →
  ∀ (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), FinSupp lam → (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) →
  (∃ c₂ : ℕ, ∀ (n : ℕ), c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N (2 * e - 1) χ b →
    Cg (n - c₂) (lam (seqN 1 j (thN X A N l n 1 (X.op N l T b)))) (ev T * lam (seqN 1 j (thN X A N l n 1 b)))) →
  ∃ (pr : X.Fn l → Fin 2 → Qbar l) (a : ℕ) (cf : Coef l),
    c.O ≤ cf.O ∧ (∀ s i k, mat W s i k ∈ cf.O) ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
    (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b) ∧
    (∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b) ∧
    IsLamFR2 X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam) := by
  first | (exact @GlobalTheory.AdmProj.exists_admissible_hecke_projection_nonvanishing_alt) | (exact GlobalTheory.AdmProj.exists_admissible_hecke_projection_nonvanishing_alt) | (intros; apply GlobalTheory.AdmProj.exists_admissible_hecke_projection_nonvanishing_alt  <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

theorem _root_.GlobalTheory.T.powerSeries_eq_of_congruent_values_at_primitiveRoots : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (A B : PowerSeries (Qbar l)) (u : Qbar l) (w : ℕ → Qbar l) (c₀ m₀ : ℕ), (∀ n, A.coeff n ∈ c.O) → (∀ n, B.coeff n ∈ c.O) → B ≠ 0 → ‖u‖ = 1 → (∀ m, ‖w m‖ = 1 ∧ Cg m (w (m + 1)) (w m)) → (∀ m, m₀ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg (m / 2 - c₀) (tval A (l ^ (3 * m)) z) (w m * u ^ m * tval B (l ^ (3 * m)) z)) → u = 1 ∧ ∀ k : ℕ, ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → ∀ n, Cg k (A.coeff n) (w m * B.coeff n) := by
  first | exact @GlobalTheory.KZ.autoPin_congr | exact GlobalTheory.KZ.autoPin_congr | (intros; apply GlobalTheory.KZ.autoPin_congr <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem inp_all : ∀ D, Inp D := fun D =>
  { g1 := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
    perm := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).2
    uni := GlobalTheory.T.intertwinerUnitary_all D
    mu := GlobalTheory.T.admissible_characters_exist D
    curve := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D
    gal := GlobalTheory.T.thetaTranslate_galoisRationality_cmPoints D
    galEx := GlobalTheory.T.galois_data_exists D
    t0Ex := GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D
    use1 := GlobalTheory.T.forall_use1 D
    alg := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D
    conj := GlobalTheory.T.thetaVacua_conjugates_cmPoints D
    nrm := GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings D
    bar := GlobalTheory.T.cmTheta_complexConjugation_compatible D
    odd3 := GlobalTheory.T.weilRepresentation_vacuum_sign_inert_places D
    odd4 := GlobalTheory.T.oddness_condition_holds D
    rep := GlobalTheory.T.exists_unitaryClass_rep_trivial_at_cm D
    model := GlobalTheory.T.datum_curve_integral_unitDisc_model D
    transl := GlobalTheory.T.cm_theta_torsion_translate_integral_series D
    two := GlobalTheory.T.cm_theta_functions_over_two_unit_and_integral D
    jets := GlobalTheory.T.cm_normalized_theta_jets_integral D
    split := GlobalTheory.T.cm_theta_values_vanish_at_odd_split_prime D
    eqv := GlobalTheory.OddRank.exact_equivariance D }

end GlobalTheory.NormSum
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

theorem _root_.GlobalTheory.T.amiceRiemannSum_congr_dirac_coefficients : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e : ℕ) (F : PowerSeries (Qbar l)) (a : ℕ → Qbar l) (N r : ℕ) (ξ : Qbar l), 1 ≤ r → l ^ (3 * r) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ j, ‖a j‖ ≤ 1) → (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot ξ (l ^ r) → Cg (2 * r) (rSum φ e F r ξ) ((l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a j * (φ (j : ZMod l) * (j : Qbar l) ^ e)) := by
  first | exact @GlobalTheory.KZ.Cmp.RiemannDirac.rSum_cg | exact GlobalTheory.KZ.Cmp.RiemannDirac.rSum_cg | (intros; apply GlobalTheory.KZ.Cmp.RiemannDirac.rSum_cg <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

theorem _root_.GlobalTheory.T.characterTwistedSum_congr_gaussSum_dirac : ∀ (l : ℕ) [Fact l.Prime] (F : PowerSeries (Qbar l)) (a : ℕ → Qbar l) (N m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), 1 ≤ m → l ^ (3 * m) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive → Cg (2 * m) (chSum F m z ψ) (gSum m z ψ * ∑ j ∈ Finset.range N, a j * ψ⁻¹ (j : ZMod (l ^ m))) := by
  first | exact @GlobalTheory.KZ.Cmp.ChD.chSum_gauss | exact GlobalTheory.KZ.Cmp.ChD.chSum_gauss | (intros; apply GlobalTheory.KZ.Cmp.ChD.chSum_gauss; all_goals assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

theorem _root_.GlobalTheory.T.exists_primitive_character_twist : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e k : ℕ) (ζ : Qbar l), l ≠ 2 → 1 ≤ k → IsPrimitiveRoot ζ (l ^ k) → ∃ ψ : DirichletCharacter (Qbar l) (l ^ (k + 1)), ψ.IsPrimitive ∧ InComp φ e ψ ∧ ψ⁻¹ (1 + (l : ZMod (l ^ (k + 1)))) = ζ := by
  first | (exact @GlobalTheory.KZ.Cmp.PrimChar.exists_primitive_inComp) | (exact GlobalTheory.KZ.Cmp.PrimChar.exists_primitive_inComp) | (intros; apply GlobalTheory.KZ.Cmp.PrimChar.exists_primitive_inComp  <;> assumption)
end
