module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.RingTheory.HahnSeries.Summable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle158
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformHeckeRelations
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle152
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle160
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.isCuspExpansionAtInfinity_properties : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (f f' : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f' h' → IsExp ε (f + f') (h + h') ∧ IsExp ε (f - f') (h - h') ∧ IsExp ε (f * f') (h * h')) ∧ (∀ (f : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f h' → h = h') ∧ (∀ c : Ω, IsExp ε (fun _ => ε c) (HahnSeries.C c)) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → IsExp ε f (0 : HahnSeries ℚ Ω) → f = 0) ∧ ∀ (f : ℍ → ℂ) (h : HahnSeries ℚ Ω), h ≠ 0 → IsExp ε f h → IsExp ε f⁻¹ h⁻¹ := by
  first | exact @GlobalTheory.FNExp.exp_props | exact GlobalTheory.FNExp.exp_props | (intros; apply GlobalTheory.FNExp.exp_props <;> assumption)
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.AlmostEt

section DerLemmas

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

theorem IsDerOn.mono' {B C : Subalgebra A S} {D : S → M} (h : IsDerOn C D) (hBC : B ≤ C) :
    IsDerOn B D :=
  ⟨fun x hx y hy => h.add x (hBC hx) y (hBC hy), fun x hx y hy => h.mul x (hBC hx) y (hBC hy), h.alg⟩

theorem IsDerOn.pow_succ_der {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B)
    (k : ℕ) : D (x ^ (k + 1)) = (((k + 1 : ℕ) : S) * x ^ k) • D x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ' x (k + 1), h.mul x hx _ (pow_mem hx _), ih, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

theorem IsDerOn.eq_on_adjoin {s : Set S} {D₁ D₂ : S → M} (h₁ : IsDerOn (Algebra.adjoin A s) D₁)
    (h₂ : IsDerOn (Algebra.adjoin A s) D₂) (hs : ∀ x ∈ s, D₁ x = D₂ x) :
    ∀ x ∈ Algebra.adjoin A s, D₁ x = D₂ x := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap a => rw [h₁.alg, h₂.alg]
  | add x y hx hy ihx ihy => rw [h₁.add x hx y hy, h₂.add x hx y hy, ihx, ihy]
  | mul x y hx hy ihx ihy => rw [h₁.mul x hx y hy, h₂.mul x hx y hy, ihx, ihy]

end DerLemmas

section TowerDer

open GlobalTheory.K5 Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_succ_pow_p (T : Tower p Ω) (m : ℕ) : zS T (m + 1) ^ p = zS T m :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact T.ζpow m)

theorem qS_succ_pow_p (T : Tower p Ω) (m : ℕ) : qS T (m + 1) ^ p = qS T m :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact T.qpow m)

theorem zS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert (zS T m) {qS T m})

theorem qS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton (qS T m)))

theorem zS_mem_levelAlg_succ (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T (m + 1) := by
  rw [← zS_succ_pow_p]; exact pow_mem (zS_mem_levelAlg T (m + 1)) _

theorem qS_mem_levelAlg_succ (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T (m + 1) := by
  rw [← qS_succ_pow_p]; exact pow_mem (qS_mem_levelAlg T (m + 1)) _

theorem levelAlg_le_succ (T : Tower p Ω) (m : ℕ) : levelAlg T m ≤ levelAlg T (m + 1) :=
  Algebra.adjoin_le (Set.insert_subset_iff.2 ⟨zS_mem_levelAlg_succ T m,
    Set.singleton_subset_iff.2 (qS_mem_levelAlg_succ T m)⟩)

theorem frac_smul_mk (s : integralClosure (O0 p) Ω) (x : Ω) :
    s • (Submodule.Quotient.mk x : Frac p Ω) = Submodule.Quotient.mk ((s : Ω) * x) := by
  rw [← Submodule.Quotient.mk_smul]; rfl

theorem frac_mk_eq_zero (s : integralClosure (O0 p) Ω) :
    (Submodule.Quotient.mk (s : Ω) : Frac p Ω) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨s, rfl⟩

theorem cyc_relation (hc : CharZero Ω) (T : Tower p Ω) (m : ℕ) :
    (Polynomial.aeval (zS T (m + 1)) (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)))) •
      (Submodule.Quotient.mk (T.ζ (m + 1) * p / (p : Ω) ^ (m + 1)) : Frac p Ω) = 0 := by
  set z := zS T (m + 1)
  set ζ := T.ζ (m + 1)
  have hp1 : 1 < p := hp.out.one_lt
  have hpos : 0 < p ^ (m + 1) := pow_pos hp.out.pos _
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero

  have hξ : IsPrimitiveRoot (ζ ^ p ^ m) p := by
    have := (T.prim (m + 1)).pow_of_dvd (pow_ne_zero m hp.out.ne_zero) (pow_dvd_pow p (Nat.le_succ m))
    simpa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)] using this

  set gS : integralClosure (O0 p) Ω := ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (z ^ p ^ m) ^ j
  have hgval : (gS : Ω) = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (ζ ^ p ^ m) ^ j := by
    simp [gS, z, ζ, zS]
  have hg : (gS : Ω) * (ζ ^ p ^ m - 1) = - p := by
    rw [hgval, Finset.sum_mul]
    simp_rw [geom_sum_mul]
    rw [Finset.sum_sub_distrib, hξ.geom_sum_eq_zero hp1]
    simp

  have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (T.prim (m + 1)).isRoot_cyclotomic hpos
  have hid := congrArg (fun f => Polynomial.aeval ζ (Polynomial.derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, map_add (f := _), map_mul,
    map_sub, hroot, zero_mul, add_zero, sub_zero] at hid
  have hzval : (Polynomial.aeval z (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p))) : Ω)
      = Polynomial.aeval ζ (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p))) := by
    exact (Polynomial.aeval_algHom_apply (integralClosure (O0 p) Ω).val z _).symm
  rw [frac_smul_mk, hzval]
  set F := Polynomial.aeval ζ (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)))
  have hζ1 : ζ ^ p ^ (m + 1) = 1 := (T.prim (m + 1)).pow_eq_one
  have hF : F * (ζ ^ p ^ m - 1) * ζ = (p : Ω) ^ (m + 1) := by
    have h2 : F * (ζ ^ p ^ m - 1) = (p : Ω) ^ (m + 1) * ζ ^ (p ^ (m + 1) - 1) := by
      simpa [map_natCast] using hid
    rw [h2, mul_assoc, pow_sub_one_mul (pow_ne_zero _ hp.out.ne_zero), hζ1, mul_one]
  have hξ1 : ζ ^ p ^ m - 1 ≠ 0 := sub_ne_zero.2 (hξ.ne_one hp1)
  have key : F * (ζ * p / (p : Ω) ^ (m + 1)) = ((-gS : integralClosure (O0 p) Ω) : Ω) := by
    apply mul_right_cancel₀ hξ1
    push_cast
    rw [neg_mul, hg, neg_neg]
    have hpm : (p : Ω) ^ (m + 1) ≠ 0 := pow_ne_zero _ hp0
    rw [div_eq_mul_inv]
    linear_combination ((p : Ω) * ((p : Ω) ^ (m + 1))⁻¹) * hF + (p : Ω) * mul_inv_cancel₀ hpm
  rw [key, frac_mk_eq_zero]

end TowerDer

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

open GlobalTheory.K5

theorem IsDerOn.pow_der {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B) {n : ℕ}
    (hn : 0 < n) : D (x ^ n) = ((n : S) * x ^ (n - 1)) • D x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa using h.pow_succ_der hx k

theorem zeta_derivation : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    IsClo p Ω → ∀ (T : Tower p Ω), ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω,
      IsDerOn (towerAlg T) D ∧ ∀ m : ℕ, D (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧
        D (qS T m) = 0 := by
  intro p hp Ω _ _ hc T
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hlev : ∀ m : ℕ, ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω,
      IsDerOn (levelAlg T (m + 1)) D ∧
        D (zS T (m + 1)) = Submodule.Quotient.mk (T.ζ (m + 1) * p / (p : Ω) ^ (m + 1)) ∧
        D (qS T (m + 1)) = 0 := fun m =>
    GlobalTheory.T.exists_derivation_towerLevelAlgebra_prescribed p Ω hc T (m + 1) (Nat.succ_pos m) (Frac p Ω) _ 0
      (cyc_relation inferInstance T m) (smul_zero _)
  choose D hD hDz hDq using hlev
  have hval : ∀ m, D m (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧
      D m (qS T m) = 0 := by
    intro m
    constructor
    · rw [← zS_succ_pow_p, (hD m).pow_der (zS_mem_levelAlg T (m + 1)) hp.out.pos, hDz m, frac_smul_mk]
      congr 1
      have hc1 : ((zS T (m + 1) : integralClosure (O0 p) Ω) : Ω) = T.ζ (m + 1) := rfl
      push_cast
      rw [hc1, ← T.ζpow m, ← pow_sub_one_mul hp.out.ne_zero (T.ζ (m + 1))]
      field_simp
      ring
    · rw [← qS_succ_pow_p, (hD m).pow_der (qS_mem_levelAlg T (m + 1)) hp.out.pos, hDq m, smul_zero]
  have hcompat : ∀ m, ∀ x ∈ levelAlg T (m + 1), D (m + 1) x = D m x := by
    intro m
    refine IsDerOn.eq_on_adjoin (s := {zS T (m + 1), qS T (m + 1)})
      ((hD (m + 1)).mono' (levelAlg_le_succ T (m + 1))) (hD m) ?_
    rintro x (rfl | hx)
    · rw [(hval (m + 1)).1, hDz m]
    · rw [Set.mem_singleton_iff.1 hx, (hval (m + 1)).2, hDq m]
  have hmono : Monotone (fun m => levelAlg T (m + 1)) :=
    monotone_nat_of_le_succ fun m => levelAlg_le_succ T (m + 1)
  obtain ⟨D', hD', hD'eq⟩ := isDerOn_iSup_glue (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
    (fun m => levelAlg T (m + 1)) hmono D hD hcompat
  have hle : towerAlg T ≤ ⨆ m, levelAlg T (m + 1) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨m, rfl⟩ | ⟨m, rfl⟩)
    · exact (le_iSup (fun m => levelAlg T (m + 1)) m) (zS_mem_levelAlg_succ T m)
    · exact (le_iSup (fun m => levelAlg T (m + 1)) m) (qS_mem_levelAlg_succ T m)
  refine ⟨D', hD'.mono' hle, fun m => ⟨?_, ?_⟩⟩
  · rw [hD'eq m _ (zS_mem_levelAlg_succ T m), (hval m).1]
  · rw [hD'eq m _ (qS_mem_levelAlg_succ T m), (hval m).2]

end GlobalTheory.AlmostEt
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.isCuspFormCoeffSeq_dirichletTwist_level_mul_sq : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ), 0 < M → CF k N (ch χ) g → CF k (N * M ^ 2) (fun d => ch χ d * ch φ d ^ 2) (fun n => φ n * g n) := by
  first | exact @GlobalTheory.EisM.CharTwist.cf_twist | exact GlobalTheory.EisM.CharTwist.cf_twist | (intros; apply GlobalTheory.EisM.CharTwist.cf_twist <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

noncomputable section

namespace GlobalTheory.EisM

theorem hat_mix_twist : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (ω : DirichletCharacter ℂ l) (φ : ZMod l → ℂ) (a c : ℤ),
    0 < N → 0 < l → N.Coprime l → (∀ x : ℤ, hat φ x = ch ω x) →
    (∀ d u : ZMod l, IsUnit d → φ u = ω d * φ (d * u)) → IsUnit (c : ZMod N) → IsUnit (a : ZMod l) →
    (∃ C : ℂ, C ≠ 0 ∧ ∀ x : ℤ, hat (fun z : ZMod (N * l) => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) x = C * (ch ω x * hat ν x)) ∧
    ∀ d : ℤ, IsCoprime d (N * l : ℕ) → ∀ y : ZMod (N * l),
      ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) y) * φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) y) =
      ch ω d * ch ν⁻¹ d * (ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) (y * d)) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) (y * d))) := by
  intro N l ν ω φ a c hN hl hc hφ htw hcu hau
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : NeZero (N * l) := ⟨(Nat.mul_pos hN hl).ne'⟩
  have hlu : IsUnit (l : ZMod N) := (ZMod.unitOfCoprime l hc.symm).isUnit
  have hNu : IsUnit (N : ZMod l) := (ZMod.unitOfCoprime N hc).isUnit
  refine ⟨?_, ?_⟩
  · have haN : IsUnit ((a : ZMod l) * N) := hau.mul hNu
    have hωaN : ω ((a : ZMod l) * N) ≠ 0 := (haN.map ω).ne_zero
    have hνcl : ν (-(c : ZMod N) * l) ≠ 0 := ((hcu.neg.mul hlu).map ν).ne_zero
    refine ⟨ν (-(c : ZMod N) * l) * (ω ((a : ZMod l) * N))⁻¹, mul_ne_zero hνcl (inv_ne_zero hωaN), fun x => ?_⟩
    rw [← hφ x, mul_comm (hat φ x)]
    let f : ZMod N × ZMod l → ZMod (N * l) := fun p => ((p.1.val * l + p.2.val * N : ℕ) : ZMod (N * l))
    have hcN : ∀ k : ℕ, ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (k : ZMod (N * l)) = (k : ZMod N) :=
      fun k => map_natCast _ k
    have hcl : ∀ k : ℕ, ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (k : ZMod (N * l)) = (k : ZMod l) :=
      fun k => map_natCast _ k
    have hinj : Function.Injective f := by
      intro p q hpq
      have h1 := congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hpq
      have h2 := congrArg (ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l)) hpq
      simp only [f, hcN, hcl] at h1 h2
      push_cast at h1 h2
      simp only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val] at h1 h2
      exact Prod.ext (hlu.mul_right_cancel h1) (hNu.mul_right_cancel h2)
    have hbij : Function.Bijective f := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hinj, by simp [ZMod.card]⟩
    rw [hat_eq_sum_std, hat_eq_sum_std, hat_eq_sum_std, ← Fintype.sum_bijective f hbij _ _ (fun _ => rfl),
      Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]
    refine Fintype.sum_congr _ _ (fun p => ?_)
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ (fun q => ?_)
    have hN1 : ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (f (p, q)) = p * l := by
      simp only [f, hcN]; push_cast; simp [ZMod.natCast_self]
    have hl1 : ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (f (p, q)) = q * N := by
      simp only [f, hcl]; push_cast; simp [ZMod.natCast_self]
    have htq := htw ((a : ZMod l) * N) q haN
    have hval : ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (f (p, q))) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (f (p, q)))
        = ν (-(c : ZMod N) * l) * (ω ((a : ZMod l) * N))⁻¹ * (ν p * φ q) := by
      rw [hN1, hl1, htq]
      have e1 : -(c : ZMod N) * (p * l) = (-(c : ZMod N) * l) * p := by ring
      have e2 : (a : ZMod l) * (q * N) = (a : ZMod l) * N * q := by ring
      rw [e1, e2, map_mul]
      field_simp
    have he : (ZMod.stdAddChar (f (p, q) * (x : ZMod (N * l))) : ℂ)
        = ZMod.stdAddChar (p * (x : ZMod N)) * ZMod.stdAddChar (q * (x : ZMod l)) := by
      have : f (p, q) * (x : ZMod (N * l)) = ((((p.val * l + q.val * N : ℕ) : ℤ) * x : ℤ) : ZMod (N * l)) := by
        simp only [f]; push_cast; rfl
      rw [this, ZMod.stdAddChar_coe, stdAddChar_nat_mul_int p x, stdAddChar_nat_mul_int q x, ← Complex.exp_add]
      congr 1
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      have hl' : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
      push_cast
      field_simp
    rw [hval, he]
    ring
  · intro d hd y
    have hdN : IsUnit (d : ZMod N) := isUnit_of_isCoprime d (by
      have := hd; push_cast at this; exact this.of_mul_right_left)
    have hdl : IsUnit (d : ZMod l) := isUnit_of_isCoprime d (by
      have := hd; push_cast at this; exact this.of_mul_right_right)
    have h1 : ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (y * d)
        = ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) y * (d : ZMod N) := by
      rw [map_mul, map_intCast]
    have h2 : ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (y * d)
        = ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) y * (d : ZMod l) := by
      rw [map_mul, map_intCast]
    rw [h1, h2]
    set u := ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) y
    set v := ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) y
    have hν0 : ν (d : ZMod N) ≠ 0 := (hdN.map ν).ne_zero
    have htv := htw (d : ZMod l) ((a : ZMod l) * v) hdl
    have e1 : -(c : ZMod N) * (u * d) = (-(c : ZMod N) * u) * d := by ring
    have e2 : (a : ZMod l) * (v * d) = (d : ZMod l) * ((a : ZMod l) * v) := by ring
    rw [e1, e2, map_mul ν (-(c : ZMod N) * u) (d : ZMod N)]
    unfold ch
    rw [MulChar.inv_apply_eq_inv', htv]
    field_simp

end GlobalTheory.EisM

end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.dirichletCharFiniteFourierTransform_properties : (∀ (N : ℕ) (θ : DirichletCharacter ℂ N), 0 < N → (∀ x : ℤ, hat θ (x + N) = hat θ x) ∧ (∀ d x : ℤ, IsCoprime d N → hat θ (x * d) = ch θ⁻¹ d * hat θ x) ∧ (θ ≠ 1 → hat θ 0 = 0)) ∧ (∀ (N l : ℕ) (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)), 0 < N → 0 < l → N.Coprime l → (∀ d : ℤ, ch φ d = ch θ d * ch ψ d) → ∀ x, hat φ x = ch θ l * ch ψ N * (hat θ x * hat ψ x)) ∧ ∀ (l : ℕ) (ψ : DirichletCharacter ℂ l), l.Prime → (ψ ≠ 1 → hat ψ 1 ≠ 0 ∧ ∀ x, hat ψ x = hat ψ 1 * ch ψ⁻¹ x) ∧ (ψ = 1 → ∀ x : ℤ, hat ψ x = (if (l : ℤ) ∣ x then (l : ℂ) else 0) - 1) := by
  first | exact @GlobalTheory.EisM.hat_char_props | exact GlobalTheory.EisM.hat_char_props | (intros; apply GlobalTheory.EisM.hat_char_props <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.depletedCuspEigenform_heckeRelations : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g → (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) ∧ (∀ p r : ℕ, p.Prime → ¬ p ∣ N → g (p ^ (r + 2)) = g p * g (p ^ (r + 1)) - χ p * (p : ℂ) ^ (k - 1) * g (p ^ r)) ∧ ∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (k - 1) * g (m * n / δ ^ 2) := by
  first | exact @GlobalTheory.EisM.hecke_relations | exact GlobalTheory.EisM.hecke_relations | (intros; apply GlobalTheory.EisM.hecke_relations <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.mdifferentiable_qExpansion_of_coeffPolynomialGrowth : ∀ a : ℕ → ℂ, PolyB a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a) := by
  first | exact @GlobalTheory.EisM.qs_mdifferentiable | exact GlobalTheory.EisM.qs_mdifferentiable | (intros; apply GlobalTheory.EisM.qs_mdifferentiable <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ

theorem vs_mem_of_isIntegral {K : Type} [Field K] (W : ValuationSubring K) {x : K} (h : IsIntegral W x) : x ∈ W := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [← hy]; exact y.2

theorem hs_coeff_algebraMap {Ω : Type} [Field Ω] (c : Ω) (r : ℚ) :
    (algebraMap Ω (HahnSeries ℚ Ω) c).coeff r = if r = 0 then c else 0 := by
  rw [HahnSeries.algebraMap_apply']
  have : algebraMap Ω (PowerSeries Ω) c = PowerSeries.C c := rfl
  rw [this, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
  simp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  change (X.exp (X.gal s (algebraMap Ω X.K c))).coeff r = (X.exp (algebraMap Ω X.K (s c))).coeff r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes, hs_coeff_algebraMap, hs_coeff_algebraMap]
  split_ifs <;> simp

theorem Tower.gal_jK (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  change (X.exp (X.gal s X.jK)).coeff r = (X.exp X.jK).coeff r
  rw [X.gal_exp]
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [hn, map_intCast]

theorem Tower.adjoin_le_of_overY (X : Tower Ω ε) (W : ValuationSubring X.K) (hW : X.OverY W) :
    ∀ x ∈ Algebra.adjoin Ω {X.jK}, x ∈ W := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.mp hy]; exact hW.2
  | algebraMap c => exact hW.1 c
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem Tower.overY_comap_sl_gal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ W : ValuationSubring X.K, X.OverY W →
      (∀ g : GQ, X.OverY (W.comap (X.sl g).toRingEquiv.toRingHom)) ∧
        ∀ s : Ω ≃ₐ[ℚ] Ω, X.OverY (W.comap (X.gal s).toRingHom) := by
  intro Ω _ _ _ ε X hε hj W hW
  refine ⟨fun g => ⟨fun c => ?_, ?_⟩, fun s => ⟨fun c => ?_, ?_⟩⟩
  · rw [ValuationSubring.mem_comap]
    change X.sl g (algebraMap Ω X.K c) ∈ W
    rw [AlgEquiv.commutes]; exact hW.1 c
  · rw [ValuationSubring.mem_comap]
    change X.sl g X.jK ∈ W
    have hint := GlobalTheory.T.isIntegral_modularTower_j_comp_glTwoPosRat ε X hε hj g
    let A := Algebra.adjoin Ω {X.jK}
    have hle : A.toSubring ≤ W.toSubring := fun x hx => X.adjoin_le_of_overY W hW x hx
    let ι : A →+* W := Subring.inclusion hle
    let _ : Algebra A W := ι.toAlgebra
    have : IsScalarTower A W X.K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact vs_mem_of_isIntegral W (hint.tower_top)
  · rw [ValuationSubring.mem_comap]
    change X.gal s (algebraMap Ω X.K c) ∈ W
    rw [X.gal_algebraMap]; exact hW.1 (s c)
  · rw [ValuationSubring.mem_comap]
    change X.gal s X.jK ∈ W
    rw [X.gal_jK]; exact hW.2

end GlobalTheory.KZ
end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.heckeSum_potentials_cocycle_eq : ∀ (N l w : ℕ) (α : Matrix (Fin 2) (Fin 2) ℤ) (ι : Type) [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < N → 0 < l → 0 < α.det → GlobalTheory.HeckeFamilyMatrices.IsDCReps (GlobalTheory.HeckeFamilyMatrices.Lev N l) α δ → ∀ F ∈ Pot ℂ w (Gam N l), (∑ i, opP ℂ (δ i) F) ∈ Pot ℂ w (Gam N l) ∧ cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (∑ i, opP ℂ (δ i) F) = GlobalTheory.HeckeFamilyMatrices.hk (GlobalTheory.HeckeFamilyMatrices.Lev N l) w δ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  first | exact @GlobalTheory.KZ.DictHk.dict_hk | exact GlobalTheory.KZ.DictHk.dict_hk | (intros; apply GlobalTheory.KZ.DictHk.dict_hk <;> assumption)
end
