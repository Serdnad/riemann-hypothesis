module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.Blo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.BloAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.LevProj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.SliceRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.ZeroLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW
open PositivityTheory.Rg.Tf.Core

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (BW.Pl E)}

private noncomputable def bV {r : ℕ} (b : Blo S r) : Submodule ℂ (LL (mu1 E r)) := b.summand.choose

private theorem bV_summand {r : ℕ} (b : Blo S r) : IsSummand (mu1 E r) (bV b) := b.summand.choose_spec.1

private theorem bV_mem {r : ℕ} (b : Blo S r) :
    ((cuspToL2 (mu1 E r) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 E r)) : LL (mu1 E r)) ∈ bV b :=
  b.summand.choose_spec.2

private theorem sum_blo {n : ℕ} (d : Dat S n) : ∑ i, (d.blo i).1 = n := by
  induction d with
  | nil =>
    change ∑ i : Fin 0, _ = 0
    simp
  | @cons r s b d ih =>
    change ∑ i : Fin (d.len + 1), _ = r + s
    rw [Fin.sum_univ_succ]
    exact congrArg (r + ·) ih

private noncomputable def datOf {n : ℕ} (d : Dat S n) (h : 2 ≤ d.len) : Datum E n where
  r := d.len
  two := h
  d := fun i => (d.blo i).1
  pos := fun i => (d.blo i).2.pos
  sum := sum_blo d
  μ := fun i => mu1 E (d.blo i).1
  V := fun i => bV (d.blo i).2
  summand := fun i => bV_summand _

private theorem map_split {r s : ℕ} (f : Fin (r + s) → ℂ) :
    (Finset.univ.val.map f) = (Finset.univ.val.map fun i : Fin r => f (Fin.castAdd s i)) +
      (Finset.univ.val.map fun i : Fin s => f (Fin.natAdd r i)) := by
  simp only [Fin.univ_val_map, List.ofFn_add, Multiset.coe_add]
  rfl

private theorem lam_ms {n : ℕ} (d : Dat S n) (τ : E →+* ℂ) : ∀ z : Fin d.len → ℂ,
    (Finset.univ.val.map fun i : Fin n => d.lam τ i + z (d.idx i)) =
      ∑ j, (Finset.univ.val.map ((d.blo j).2.Λ τ)).map (· + z j) := by
  induction d with
  | nil =>
    intro z
    change _ = ∑ j : Fin 0, _
    simp
  | @cons r s b d ih =>
    intro (z : Fin (d.len + 1) → ℂ)
    change _ = ∑ j : Fin (d.len + 1), (Finset.univ.val.map (((Dat.cons b d).blo j).2.Λ τ)).map (· + z j)
    rw [map_split, Fin.sum_univ_succ]
    have h1 : (fun i : Fin r => (Dat.cons b d).lam τ (Fin.castAdd s i) + z ((Dat.cons b d).idx (Fin.castAdd s i))) =
        fun i => b.Λ τ i + z 0 := by
      funext i
      simp [Dat.lam, Dat.idx]
      exact congrArg z (Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) _)
    have h2 : (fun i : Fin s => (Dat.cons b d).lam τ (Fin.natAdd r i) + z ((Dat.cons b d).idx (Fin.natAdd r i))) =
        fun i => d.lam τ i + z (d.idx i).succ := by
      funext i
      simp [Dat.lam, Dat.idx]
      exact congrArg z (Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) _)
    rw [h1, h2, ih fun j => z j.succ, Multiset.map_map]
    rfl

private theorem sat_blo {n : ℕ} (d : Dat S n) (j : Fin d.len) : d.sat j = (d.blo j).2.sat := by
  induction d with
  | nil => exact (j : Fin 0).elim0
  | @cons r s b d ih =>
    revert j
    change ∀ j : Fin (d.len + 1), _
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · exact ih i

private theorem pt_on {n : ℕ} (d : Dat S n) (h : 2 ≤ d.len) {Λ : (E →+* ℂ) → Multiset ℂ} {t : BW.Pl E → Multiset ℂ}
    (ho : d.On Λ t) : (datOf d h).Pt S Λ t := by
  obtain ⟨z, hΛ, ht⟩ := ho
  refine ⟨z, fun i τ => Finset.univ.val.map ((d.blo i).2.Λ τ), fun i w => ((d.blo i).2.sat w).map fun x : ℂˣ => (x : ℂ),
    fun i => UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.bloAt E S _ _ _ (bV_summand _) (bV_mem _), fun τ => ?_, fun w hw => ?_⟩
  · rw [hΛ]
    exact lam_ms d τ z
  · rw [ht w hw]
    unfold Dat.ptS
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sat_blo, Multiset.map_map]
    rfl

private theorem two_blocks {n : ℕ} (d : Dat S n) (h : d.len = 2) (hs : ∀ i, (d.blo i).1 = 2) :
    ∃ b₁ b₂ : Blo S 2, HEq d (Dat.cons b₁ (Dat.cons b₂ (Dat.nil : Dat S 0))) := by
  cases d with
  | nil => exact absurd h (by simp [Dat.len])
  | @cons r s b d =>
    cases d with
    | nil => exact absurd h (by simp [Dat.len])
    | @cons r' s' b' d =>
      cases d with
      | nil =>
        obtain rfl : r = 2 := hs (0 : Fin 2)
        obtain rfl : r' = 2 := hs (1 : Fin 2)
        exact ⟨b, b', HEq.rfl⟩
      | cons _ _ => exact absurd h (by simp [Dat.len])

private theorem form_mem {m : (E →+* ℂ) → Multiset ℂ} {B : BW.Pl E → Multiset ℂ} {τ : Submodule ℂ (LL (mu1 E 2))}
    (b : Blo S 2) (hA : At (mu1 E 2) S (bV b) m B)
    (hs : ∀ V, IsSummand (mu1 E 2) V → At (mu1 E 2) S V m B → V = τ) :
    ((cuspToL2 (mu1 E 2) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ := by
  rw [← hs _ (bV_summand b) hA]
  exact bV_mem b

private theorem fin_two_ne : ∀ i j : Fin 2, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by decide


private theorem core (τ₁ τ₂ : Submodule ℂ (LL (mu1 E 2))) (m₁ m₂ : (E →+* ℂ) → Multiset ℂ) (B₁ B₂ : BW.Pl E → Multiset ℂ)
    (smo₁ : ∀ V, IsSummand (mu1 E 2) V → At (mu1 E 2) S V m₁ B₁ → V = τ₁)
    (smo₂ : ∀ V, IsSummand (mu1 E 2) V → At (mu1 E 2) S V m₂ B₂ → V = τ₂)
    (rigid : ∀ b : Datum E (2 + 2), b.Pt S (fun τ => m₁ τ + m₂ τ) (fun w => B₁ w + B₂ w) →
      b.r = 2 ∧ (∀ i, b.d i = 2) ∧ ∃ i j, i ≠ j ∧ At (b.μ i) S (b.V i) m₁ B₁ ∧ At (b.μ j) S (b.V j) m₂ B₂)
    (d : Dat S (2 + 2)) (h : 2 ≤ d.len) (ho : d.On (fun τ => m₁ τ + m₂ τ) (fun w => B₁ w + B₂ w)) :
    ∃ b₁ b₂ : Blo S 2, d = Dat.cons b₁ (Dat.cons b₂ Dat.nil) ∧
      ((((cuspToL2 (mu1 E 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ₁ ∧
          ((cuspToL2 (mu1 E 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ₂) ∨
        (((cuspToL2 (mu1 E 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ₂ ∧
          ((cuspToL2 (mu1 E 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ₁)) := by
  have hP := pt_on d h ho
  have key := rigid (datOf d h) hP
  have hr := key.1
  have hd := key.2.1
  obtain ⟨b₁, b₂, he⟩ := two_blocks d hr hd
  obtain ⟨i, j, hij, hi, hj⟩ := key.2.2
  have he' : d = Dat.cons b₁ (Dat.cons b₂ Dat.nil) := eq_of_heq he
  subst he'
  refine ⟨b₁, b₂, rfl, ?_⟩
  revert i j
  change ∀ i j : Fin 2, _
  intro i j hij hi hj
  rcases fin_two_ne i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨form_mem b₁ hi smo₁, form_mem b₂ hj smo₂⟩
  · exact Or.inr ⟨form_mem b₁ hj smo₂, form_mem b₂ hi smo₁⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.exempt :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (μ : Measure (normOneGL (K := E) (n := (2 + 2)))) [μ.IsHaarMeasure] (θ : Twist μ)
      (𝔢 : Side θ 2) (𝔵 : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam 𝔢) (d : Dat 𝔢.S (2 + 2)), 2 ≤ d.len → d.On 𝔵.Λ 𝔵.t →
      ∃ b₁ b₂ : Blo 𝔢.S 2, d = Dat.cons b₁ (Dat.cons b₂ Dat.nil) ∧
        ((((cuspToL2 (mu1 E 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ 𝔵.τ₁ ∧ ((cuspToL2 (mu1 E 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ 𝔵.τ₂) ∨
          (((cuspToL2 (mu1 E 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ 𝔵.τ₂ ∧ ((cuspToL2 (mu1 E 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ 𝔵.τ₁)) := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 d h ho
  exact core 𝔵.τ₁ 𝔵.τ₂ 𝔵.m₁ 𝔵.m₂ 𝔵.B₁ 𝔵.B₂ 𝔵.smo₁ 𝔵.smo₂ 𝔵.rigid d h ho
end

section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (BW.Pl E)}

noncomputable def bloV {r : ℕ} (b : Blo S r) : Submodule ℂ (LL (mu1 E r)) := b.summand.choose

theorem bloV_summand {r : ℕ} (b : Blo S r) : IsSummand (mu1 E r) (bloV b) := b.summand.choose_spec.1

theorem bloV_mem {r : ℕ} (b : Blo S r) :
    ((cuspToL2 (mu1 E r) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 E r)) : LL (mu1 E r)) ∈ bloV b := b.summand.choose_spec.2

private theorem blo_sum : ∀ {n : ℕ} (d : Dat S n), ∑ j, (d.blo j).1 = n
  | _, .nil => rfl
  | _, .cons b d => by
    have := blo_sum d
    exact (Fin.sum_univ_succ (n := d.len) _).trans (congrArg (_ + ·) this)

theorem blo_sat : ∀ {n : ℕ} (d : Dat S n) (j : Fin d.len), d.sat j = (d.blo j).2.sat
  | _, .nil, j => j.elim0
  | _, .cons b d, j => by
    refine Fin.cases (motive := fun j : Fin (d.len + 1) => (Dat.cons b d).sat j = (Dat.blo (.cons b d) j).2.sat) rfl
      (fun i => blo_sat d i) j

private theorem map_addCases {r s : ℕ} (f : Fin (r + s) → ℂ) :
    Finset.univ.val.map f = (Finset.univ.val.map fun i => f (Fin.castAdd s i)) + Finset.univ.val.map fun i => f (Fin.natAdd r i) := by
  simp only [Fin.univ_val_map, List.ofFn_add, Multiset.coe_add]
  rfl

theorem blo_ms (τ : E →+* ℂ) : ∀ {n : ℕ} (d : Dat S n) (z : Fin d.len → ℂ),
    msOf (d.ptL z) τ = ∑ j, (Finset.univ.val.map ((d.blo j).2.Λ τ)).map (· + z j)
  | _, .nil, _ => rfl
  | _, .cons b d, z => by
    have ih := blo_ms τ d fun j => z (j.succ : Fin (d.len + 1))
    refine Eq.trans ?_ (Fin.sum_univ_succ (n := d.len) _).symm
    unfold msOf at ih ⊢
    rw [map_addCases]
    congr 1
    · rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      have h1 : (Dat.cons b d).idx (Fin.castAdd _ i) = (0 : Fin (d.len + 1)) :=
        Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      have h2 : (Dat.cons b d).lam τ (Fin.castAdd _ i) = b.Λ τ i :=
        Fin.addCases_left (motive := fun _ => ℂ) (left := b.Λ τ) (right := d.lam τ) i
      exact congrArg₂ (· + ·) h2 (congrArg z h1)
    · refine Eq.trans ?_ ih
      refine Multiset.map_congr rfl fun i _ => ?_
      have h1 : (Dat.cons b d).idx (Fin.natAdd _ i) = ((d.idx i).succ : Fin (d.len + 1)) :=
        Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      have h2 : (Dat.cons b d).lam τ (Fin.natAdd _ i) = d.lam τ i :=
        Fin.addCases_right (motive := fun _ => ℂ) (left := b.Λ τ) (right := d.lam τ) i
      exact congrArg₂ (· + ·) h2 (congrArg z h1)

noncomputable def datB {n : ℕ} (d : Dat S n) (h2 : 2 ≤ d.len) : Datum E n where
  r := d.len
  two := h2
  d := fun j => (d.blo j).1
  pos := fun j => (d.blo j).2.pos
  sum := by exact blo_sum d
  μ := fun j => mu1 E (d.blo j).1
  haar := fun _ => inferInstance
  V := fun j => bloV (d.blo j).2
  summand := fun j => bloV_summand (d.blo j).2

theorem datB_at {n : ℕ} (d : Dat S n) (h2 : 2 ≤ d.len) (j : Fin d.len) :
    At (mu1 E (d.blo j).1) S (bloV (d.blo j).2) (fun τ => Finset.univ.val.map ((d.blo j).2.Λ τ))
      fun w => ((d.blo j).2.sat w).map fun x : ℂˣ => (x : ℂ) :=
  bloAt E S _ _ _ (bloV_summand _) (bloV_mem _)

theorem bloV_unique {r : ℕ} (b : Blo S r) {m : (E →+* ℂ) → Multiset ℂ} {B : BW.Pl E → Multiset ℂ}
    (h : At (mu1 E r) S (bloV b) m B) :
    (∀ τ, m τ = Finset.univ.val.map (b.Λ τ)) ∧ ∀ w ∉ S, B w = (b.sat w).map fun x : ℂˣ => (x : ℂ) := by
  have hb := bloAt E S r b (bloV b) (bloV_summand b) (bloV_mem b)
  have hp := Dp.parEx E r b.pos (mu1 E r) (bloV b) (bloV_summand b)
  exact ⟨fun τ => (hp.1 τ).unique (h.1 τ) (hb.1 τ), fun w hw => (hp.2.1 w (h.2 w hw).2.1).unique (h.2 w hw) (hb.2 w hw)⟩

private theorem on_of {n : ℕ} (d : Dat S n) {Λ : (E →+* ℂ) → Multiset ℂ} {t : BW.Pl E → Multiset ℂ} (lam : Fin d.len → ℂ)
    (m : Fin d.len → (E →+* ℂ) → Multiset ℂ) (B : Fin d.len → BW.Pl E → Multiset ℂ)
    (hA : ∀ j, At (mu1 E (d.blo j).1) S (bloV (d.blo j).2) (m j) (B j))
    (hΛ : ∀ τ, Λ τ = ∑ j, (m j τ).map (· + lam j))
    (ht : ∀ w ∉ S, t w = ∑ j, (B j w).map (· * (Ideal.absNorm w.asIdeal : ℂ) ^ (-lam j))) : d.On Λ t := by
  have hu := fun j => bloV_unique (d.blo j).2 (hA j)
  refine ⟨lam, funext fun τ => ?_, fun w hw => ?_⟩
  · rw [hΛ τ, blo_ms]
    exact Finset.sum_congr rfl fun j _ => by rw [(hu j).1 τ]
  · rw [ht w hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hu j).2 w hw, blo_sat, Multiset.map_map]
    rfl

theorem datB_pt {n : ℕ} (d : Dat S n) (h2 : 2 ≤ d.len) (Λ : (E →+* ℂ) → Multiset ℂ) (t : BW.Pl E → Multiset ℂ) :
    (datB d h2).Pt S Λ t ↔ d.On Λ t := by
  constructor
  · rintro ⟨lam, m, B, hA, hΛ, ht⟩
    exact on_of d lam m B hA hΛ ht
  · rintro ⟨z, rfl, ht⟩
    refine ⟨z, _, _, fun j => datB_at d h2 j, fun τ => blo_ms τ d z, fun w hw => ?_⟩
    rw [ht w hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [blo_sat, Multiset.map_map]
    rfl

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.datOn :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Set (BW.Pl E)) (n : ℕ) (d : Dat S n), 2 ≤ d.len →
      ∃ b : Datum E n, ∀ Λ t, b.Pt S Λ t ↔ d.On Λ t := by
  intro E _ _ _ S n d h2
  exact ⟨UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.datB d h2, UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.datB_pt d h2⟩
end

section

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

variable {K : Type} [Field K] [NumberField K]

theorem lv_nn (a b : G1 K 2) (t : ℝ) (X : UPos (2 + 2) 2 → 𝔸[K]) : ∃ Y, lv a b t * nn X = nn Y * lv a b t := by
  obtain ⟨e, he, -⟩ := adMeas a b t
  exact ⟨e.symm X, by rw [he, e.apply_symm_apply]⟩

theorem rd_bdd {μ₂ : Measure (G1 K 2)} {τ : Submodule ℂ (L2 μ₂)} {φ : G1 K 2 → ℂ} (h : Rd τ φ) : ∃ C : ℝ, ∀ m, ‖φ m‖ ≤ C := by
  obtain ⟨C, hC⟩ := h.decay 0
  exact ⟨C, fun m => by simpa using hC m⟩

theorem ex_prob {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (U : Subgroup G)
    [CompactSpace U] : ∃ lam : Measure U, IsProbabilityMeasure lam ∧ lam.IsHaarMeasure :=
  ⟨Measure.haarMeasure ⊤, ⟨by simpa using Measure.haarMeasure_self (G := U) (K₀ := ⊤)⟩, inferInstance⟩


theorem secEx [_root_.NumberField.IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2))
    (h₁ : CuspIrr μ₂ τ₁) (h₂ : CuspIrr μ₂ τ₂) (φ₁ φ₂ : G1 K 2 → ℂ) (r₁ : Rd τ₁ φ₁) (r₂ : Rd τ₂ φ₂)
    (ψ : G1 K (2 + 2) → ℂ) (hψ : Continuous ψ) (hfix : D.Fix ψ) :
    ∃ (U : Subgroup (G1 K (2 + 2))) (_ : CompactSpace U) (lam : Measure U) (_ : IsProbabilityMeasure lam)
      (x : U → G1 K 2 × G1 K 2) (f : G1 K (2 + 2) → ℂ), U ≤ KG K (2 + 2) ∧ Continuous x ∧
      (∀ u : U, ∃ X, (u : G1 K (2 + 2)) = nn X * lv (x u).1 (x u).2 0) ∧ IsSec τ₁ τ₂ f ∧ D.Fix f ∧
      ∀ X a b t, ∀ k ∈ KG K (2 + 2),
        f (nn X * lv a b t * k) = ∫ u : U, φ₁ (a * (x u).1) * φ₂ (b * (x u).2) * ψ ((u : G1 K (2 + 2))⁻¹ * k) ∂lam := by
  obtain ⟨S, π, hS, hπ, hmem, hval⟩ := levProj (K := K)
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) := ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 _).1
  have hmul := (blkLaws (K := K)).2.1
  haveI hc : CompactSpace (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2))) := isCompact_iff_compactSpace.1 (hK.inter_left hS)
  haveI : SecondCountableTopology (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2))) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨lam, hp, hl⟩ := ex_prob (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2)))
  have c₁ := r₁.cont
  have c₂ := r₂.cont
  obtain ⟨f, hf, hv⟩ := indSec S (KG K (2 + 2)) hS hK (fun g => by
    obtain ⟨X, a, b, t, k, hk, rfl⟩ := iwa g
    exact ⟨_, (hmem _).2 ⟨X, a, b, t, rfl⟩, k, hk, rfl⟩) π hπ (fun m => φ₁ m.1 * φ₂ m.2) (by fun_prop) ψ hψ lam
  set x : (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2))) → G1 K 2 × G1 K 2 := fun u => π ⟨u, u.2.1⟩ with hx
  have hxc : Continuous x := hπ.comp (continuous_subtype_val.subtype_mk _)
  have hv' : ∀ X a b t, ∀ k ∈ KG K (2 + 2), f (nn X * lv a b t * k) =
      ∫ u, φ₁ (a * (x u).1) * φ₂ (b * (x u).2) * ψ ((u : G1 K (2 + 2))⁻¹ * k) ∂lam := by
    intro X a b t k hk
    have := hv ⟨_, (hmem _).2 ⟨X, a, b, t, rfl⟩⟩ k hk
    rw [hval X a b t _ rfl] at this
    exact this
  have hF : D.Fix f := by
    intro g
    obtain ⟨X, a, b, t, k, hk, rfl⟩ := iwa g
    obtain ⟨hU, hle, -⟩ := typeFin D
    haveI := D.prob
    have hH : Continuous fun z : G1 K (2 + 2) × (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2))) =>
        φ₁ (a * (x z.2).1) * φ₂ (b * (x z.2).2) * ψ ((z.2 : G1 K (2 + 2))⁻¹ * z.1) :=
      ((c₁.comp (continuous_const.mul (hxc.comp continuous_snd).fst)).mul (c₂.comp (continuous_const.mul (hxc.comp continuous_snd).snd))).mul
        (hψ.comp ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst))
    have := fix_swap D.ν _ hU D.supp D.e D.cont lam _ hH (fun C hC => by
      obtain ⟨B, hB⟩ := (hC.prod isCompact_univ).exists_bound_of_continuousOn hH.continuousOn
      exact ⟨B, ae_of_all _ fun y z hz => hB (z, y) ⟨hz, trivial⟩⟩) k fun u => by
        simp only [← hfix ((u : G1 K (2 + 2))⁻¹ * k), ← integral_const_mul, mul_assoc]
        exact integral_congr_ae (ae_of_all _ fun h => by ring)
    rw [hv' X a b t k hk, ← this]
    refine integral_congr_ae ?_
    filter_upwards [D.supp] with h hh
    rw [mul_assoc, hv' X a b t _ (mul_mem hk (hle hh))]
  obtain ⟨C₁, b₁⟩ := rd_bdd r₁
  obtain ⟨C₂, b₂⟩ := rd_bdd r₂
  have hsl : ∀ m₁ m₂ X a b t, ∀ k ∈ KG K (2 + 2), f (lv m₁ m₂ 0 * (nn X * lv a b t * k)) =
      ∫ u, φ₁ (m₁ * a * (x u).1) * φ₂ (m₂ * b * (x u).2) * ψ ((u : G1 K (2 + 2))⁻¹ * k) ∂lam := by
    intro m₁ m₂ X a b t k hk
    obtain ⟨Y, hY⟩ := lv_nn m₁ m₂ 0 X
    rw [← mul_assoc, ← mul_assoc, hY, mul_assoc (nn Y), hmul, hv' _ _ _ _ k hk]
  refine ⟨_, hc, lam, hp, x, f, inf_le_right, hxc, fun u => ?_,
    (secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hF).2 ⟨hf, ?_, fun Y g => ?_, fun s g => ?_, fun g => ?_⟩, hF, hv'⟩
  · obtain ⟨X, a, b, t, e⟩ := (hmem _).1 u.2.1
    have h0 := (hpSpec (K := K)).1 X a b t 1
    rw [mul_one, ← e, ((hpSpec (K := K)).2.1 _ u.2.2).1, ((hpSpec (K := K)).2.1 _ (one_mem _)).1, add_zero] at h0
    subst h0
    have e2 : x u = (a, b) := hval X a b 0 _ e
    exact ⟨X, by rw [e2]; exact e⟩
  · obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hψ.continuousOn
    refine ⟨C₁ * C₂ * B * lam.real univ, fun g => ?_⟩
    obtain ⟨X, a, b, t, k, hk, rfl⟩ := iwa g
    rw [hv' X a b t k hk]
    refine norm_integral_le_of_norm_le_const (ae_of_all _ fun u => ?_)
    rw [norm_mul, norm_mul]
    have h1 := (norm_nonneg _).trans (b₁ 1)
    exact mul_le_mul (mul_le_mul (b₁ _) (b₂ _) (norm_nonneg _) h1) (hB _ (mul_mem (inv_mem u.2.2) hk)) (norm_nonneg _)
      (mul_nonneg h1 ((norm_nonneg _).trans (b₂ 1)))
  · obtain ⟨X, a, b, t, k, hk, rfl⟩ := iwa g
    rw [← mul_assoc, ← mul_assoc, ← unipOne_add, hv' _ a b t k hk, hv' _ a b t k hk]
  · obtain ⟨X, a, b, t, k, hk, rfl⟩ := iwa g
    obtain ⟨Y, hY⟩ := lv_nn 1 1 s X
    rw [← mul_assoc, ← mul_assoc, hY, mul_assoc (nn Y), hmul, one_mul, one_mul, hv' _ _ _ _ k hk, hv' _ _ _ _ k hk]
  · obtain ⟨X, a, b, t, k, hk, rfl⟩ := iwa g
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨v, hv, hr⟩ := sliceRep μ₂ τ₁ h₁ φ₁ c₁ ⟨C₁, b₁⟩ r₁.rat r₁.rep _ lam
        (fun u => φ₂ (m₂ * b * (x u).2) * ψ ((u : G1 K (2 + 2))⁻¹ * k)) (fun u => a * (x u).1)
        ((c₂.comp (continuous_const.mul hxc.snd)).mul (hψ.comp (continuous_subtype_val.inv.mul continuous_const)))
        (continuous_const.mul hxc.fst)
      refine ⟨v, hv, ?_⟩
      simp only [hsl _ _ X a b t k hk]
      exact hr.mono fun y hy => hy.trans (integral_congr_ae (ae_of_all _ fun u => by simp only [mul_assoc]; ring))
    · obtain ⟨v, hv, hr⟩ := sliceRep μ₂ τ₂ h₂ φ₂ c₂ ⟨C₂, b₂⟩ r₂.rat r₂.rep _ lam
        (fun u => φ₁ (m₁ * a * (x u).1) * ψ ((u : G1 K (2 + 2))⁻¹ * k)) (fun u => b * (x u).2)
        ((c₁.comp (continuous_const.mul hxc.fst)).mul (hψ.comp (continuous_subtype_val.inv.mul continuous_const)))
        (continuous_const.mul hxc.snd)
      refine ⟨v, hv, ?_⟩
      simp only [hsl _ _ X a b t k hk]
      exact hr.mono fun y hy => hy.trans (integral_congr_ae (ae_of_all _ fun u => by simp only [mul_assoc]; ring))

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX
end
