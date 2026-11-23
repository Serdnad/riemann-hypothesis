module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle031
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle362
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle022
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle381
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle389
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.Tactic.Basify
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle390
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.EigTorus

theorem exists_common_eigenvector : ∀ (d : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    {I : Type} (T : I → Module.End ℂ E), (∀ a b, Commute (T a) (T b)) → Module.finrank ℂ E = d → 0 < d →
    ∃ w : E, w ≠ 0 ∧ ∃ c : I → ℂ, ∀ i, T i w = c i • w :=
  _root_.UpperTheory.Reformulated.B.Ygb8.main

theorem diag_commute {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {g h : GL (Fin n) L}
    (hg : IsDiagM g) (hh : IsDiagM h) : g * h = h * g := by
  have key : ∀ a : GL (Fin n) L, IsDiagM a →
      (a : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => (a : Matrix (Fin n) (Fin n) L) i i) := by
    intro a ha
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij, ha i j hij]
  apply Units.ext
  simp only [Units.val_mul]
  rw [key g hg, key h hh, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

theorem mem_latK_iff {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (a : GL (Fin n) L)
    (ha : IsDiagM a) (hv : ∀ i, Valued.v ((a : Matrix (Fin n) (Fin n) L) i i) = 1) (k : ℕ) (x : Fin n → L) :
    (a : Matrix (Fin n) (Fin n) L).mulVec x ∈ latK L n k ↔ x ∈ latK L n k := by
  have hc : ∀ i, (a : Matrix (Fin n) (Fin n) L).mulVec x i = (a : Matrix (Fin n) (Fin n) L) i i * x i := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      rw [ha i j (Ne.symm hj), zero_mul]
    · simp
  have hvv : ∀ i, Valued.v ((a : Matrix (Fin n) (Fin n) L).mulVec x i) = Valued.v (x i) := by
    intro i
    rw [hc, map_mul, hv, one_mul]
  simp only [latK, Set.mem_setOf_eq, hvv]

theorem mem_iwGL_of_diag {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (a : GL (Fin n) L)
    (ha : IsDiagM a) (hv : ∀ i, Valued.v ((a : Matrix (Fin n) (Fin n) L) i i) = 1) : a ∈ IwGL L n := by
  unfold IwGL
  rw [Subgroup.mem_iInf]
  intro k
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_latK_iff a ha hv k y).2 hy
  · intro hx
    refine ⟨((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec x, ?_, ?_⟩
    · rw [← mem_latK_iff a ha hv k, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
      simpa using hx
    · show (a : Matrix (Fin n) (Fin n) L).mulVec (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
      simp

theorem mem_iwU_of_diag {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
    (k : GU σ n) (hk : k ∈ KU σ n) (hd : IsDiagM (k : GL (Fin n) L)) : k ∈ IwU σ n := by
  refine Subgroup.mem_subgroupOf.2 (mem_iwGL_of_diag _ hd fun i => ?_)
  obtain ⟨-, r, hr⟩ := Subgroup.mem_subgroupOf.1 hk
  have hint : ∀ (s : GL (Fin n) (intL L)) (i j : Fin n),
      Valued.v (((Formalism.UG.bc (n := Fin n) (intL L).subtype s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 := by
    intro s i j
    exact ((s : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have h1 := hint r i i
  have h2 := hint r⁻¹ i i
  rw [map_inv, hr] at h2
  rw [hr] at h1
  have hmul : ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      ((((k : GL (Fin n) L))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) L => M i i) (Units.mul_inv (k : GL (Fin n) L))
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
    rw [Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hj
      rw [hd i j (Ne.symm hj), zero_mul]
    · simp
  have hm := congrArg Valued.v hmul
  rw [map_mul, map_one] at hm
  refine le_antisymm h1 ?_
  by_contra hlt
  push_neg at hlt
  have : Valued.v (((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      Valued.v (((((k : GL (Fin n) L))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  exact absurd hm (ne_of_lt this)

theorem eigU_of (hIw : IwahoriU) (hDom : DomU) (hKU : KUFacts)
    (hA4 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], A4 G) :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ∀ y : V, y ∉ jacU ρ →
    (∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ρ k y - y ∈ jacU ρ) →
    ∃ (y' : V) (ξ : GU σ n → ℂ), y' ∉ jacU ρ ∧ (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y' - ξ t • y' ∈ jacU ρ) ∧
      ∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ξ k = 1 := by
  intro L _ _ _ ϖ σ q n V _ _ ρ hu hadm y hy hfix
  obtain ⟨D, hJ, hN, hNm, hT⟩ := hIw L ϖ σ q hu n
  obtain ⟨-, -, hIK, t₀, ht₀d, ht₀s⟩ := hKU L ϖ σ q n hu
  have hstr : D.IsStrDom ⟨t₀, (hT _).2 ht₀d⟩ :=
    (hDom L ϖ σ q hu n D hJ hN hNm hT ⟨t₀, (hT _).2 ht₀d⟩).2 ht₀s
  obtain ⟨-, honto⟩ := hA4 (GU σ n) D V ρ hadm ⟨_, hstr⟩
  have hker : twKer ρ D.N 1 = jacU ρ := twKer_eq_jacSub D _ hN ρ
  have hpi : ∀ (t : D.T) (v : V), D.piN ρ t (D.proj ρ v) = D.proj ρ (ρ (t : GU σ n) v) := fun _ _ => rfl
  have hproj0 : ∀ v : V, D.proj ρ v = 0 ↔ v ∈ jacU ρ := by
    intro v
    rw [← hker]
    exact Submodule.Quotient.mk_eq_zero _
  have hprojeq : ∀ v v' : V, D.proj ρ v = D.proj ρ v' ↔ v - v' ∈ jacU ρ := by
    intro v v'
    rw [← hker]
    exact Submodule.Quotient.eq _
  have hfd : FiniteDimensional ℂ (fixed ρ D.J) := hadm.2 D.J D.isOpen_J D.isCompact_J
  let S : Submodule ℂ (Jacquet ρ D.N) := fixed (D.piN ρ) D.JT
  let p : fixed ρ D.J →ₗ[ℂ] Jacquet ρ D.N := (twKer ρ D.N 1).mkQ ∘ₗ (fixed ρ D.J).subtype
  have hSle : S ≤ LinearMap.range p := by
    intro w hw
    obtain ⟨v, hv⟩ := honto w hw
    exact ⟨v, hv⟩
  have hSfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSle
  have hmemS : ∀ w : Jacquet ρ D.N, w ∈ S ↔ ∀ s : D.JT, D.piN ρ (s : D.T) w = w := by
    intro w
    refine ⟨fun h s => by simpa using h s, fun h s => by simpa using h s⟩
  have hw₀ : D.proj ρ y ∈ S := by
    refine (hmemS _).2 fun s => ?_
    rw [hpi, hprojeq]
    have hsJ : ((s : D.T) : GU σ n) ∈ D.J := s.2
    exact hfix _ (hIK (hJ ▸ hsJ)) ((hT _).1 (s : D.T).2)
  have hw₀0 : D.proj ρ y ≠ 0 := fun h => hy ((hproj0 y).1 h)
  have hcomm : ∀ a b : D.T, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact diag_commute ((hT _).1 a.2) ((hT _).1 b.2)
  have hst : ∀ t : D.T, ∀ w ∈ S, D.piN ρ t w ∈ S := by
    intro t w hw
    refine (hmemS _).2 fun s => ?_
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, (hmemS w).1 hw s]
  have hpos : 0 < Module.finrank ℂ S := by
    have : Nontrivial S := ⟨⟨⟨_, hw₀⟩, 0, fun h => hw₀0 (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  obtain ⟨w, hw0, c, hc⟩ := exists_common_eigenvector _ S (fun t : D.T => (D.piN ρ t).restrict (hst t))
    (fun a b => by
      ext x
      have h : D.piN ρ a (D.piN ρ b x) = D.piN ρ b (D.piN ρ a x) := by
        rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
      simpa [Module.End.mul_apply, LinearMap.restrict_apply] using h) rfl hpos
  have hc' : ∀ t : D.T, D.piN ρ t (w : Jacquet ρ D.N) = c t • (w : Jacquet ρ D.N) := fun t => by
    simpa [LinearMap.restrict_apply] using congrArg Subtype.val (hc t)
  have hwne : (w : Jacquet ρ D.N) ≠ 0 := fun h => hw0 (Subtype.ext h)
  obtain ⟨y', hy'⟩ : ∃ y' : V, D.proj ρ y' = (w : Jacquet ρ D.N) := Submodule.Quotient.mk_surjective _ _
  classical
  refine ⟨y', fun g => if h : g ∈ D.T then c ⟨g, h⟩ else 1, fun h => hwne (hy' ▸ (hproj0 y').2 h), ?_, ?_⟩
  · intro t ht
    have htT : t ∈ D.T := (hT t).2 ht
    beta_reduce
    rw [dite_eq_left htT, ← hproj0]
    have h1 := hc' ⟨t, htT⟩
    rw [← hy', hpi] at h1
    show D.proj ρ (ρ t y' - c ⟨t, htT⟩ • y') = 0
    have hsub : D.proj ρ (ρ t y' - c ⟨t, htT⟩ • y') = D.proj ρ (ρ t y') - c ⟨t, htT⟩ • D.proj ρ y' := rfl
    rw [hsub, h1, sub_self]
  · intro k hk hkd
    have hkT : k ∈ D.T := (hT k).2 hkd
    beta_reduce
    rw [dite_eq_left hkT]
    have hkJ : k ∈ D.J := hJ ▸ mem_iwU_of_diag k hk hkd
    have h1 := hc' ⟨k, hkT⟩
    have h2 := (hmemS _).1 w.2 ⟨⟨k, hkT⟩, hkJ⟩
    have h3 : c ⟨k, hkT⟩ • (w : Jacquet ρ D.N) = (1 : ℂ) • (w : Jacquet ρ D.N) := by
      rw [← h1, one_smul]
      exact h2
    exact smul_left_injective ℂ hwne h3

end GlobalTheory.CompanionTheory.EigTorus
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
open GlobalTheory.CompanionTheory.LbElem.ConjMonomial GlobalTheory.CompanionTheory.LbElem.MonomialInJ GlobalTheory.CompanionTheory.LbElem.IwahoriLDU

namespace GlobalTheory.CompanionTheory.LbElem.JPredDom

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entry_diag_mul {N : ℕ} {a b : GL (Fin N) k} (n : GL (Fin N) k) {α β : Fin N → k}
    (ha : (a : Matrix (Fin N) (Fin N) k) = Matrix.diagonal α)
    (hb : (b : Matrix (Fin N) (Fin N) k) = Matrix.diagonal β) (i j : Fin N) :
    ((a * n * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      α i * (n : Matrix (Fin N) (Fin N) k) i j * β j := by
  rw [Units.val_mul, Units.val_mul, ha, hb, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem diag_ne_zero {N : ℕ} {x : GL (Fin N) k} {d : Fin N → k}
    (hx : (x : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d) (i : Fin N) : d i ≠ 0 := by
  have h := diag_ne_zero_of_offDiag x (fun i j hij => by rw [hx, Matrix.diagonal_apply_ne _ hij]) i
  rwa [hx, Matrix.diagonal_apply_eq] at h

theorem val_inv_diag {N : ℕ} {x : GL (Fin N) k} {d : Fin N → k}
    (hx : (x : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d) :
    ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => (d i)⁻¹ := by
  have h1 : (x : Matrix (Fin N) (Fin N) k) * Matrix.diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [hx, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (diag_ne_zero hx i)
  calc ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
      = ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *
          ((x : Matrix (Fin N) (Fin N) k) * Matrix.diagonal (fun i => (d i)⁻¹)) := by rw [h1, mul_one]
    _ = Matrix.diagonal fun i => (d i)⁻¹ := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem val_pow_diag {N : ℕ} {x : GL (Fin N) k} {d : Fin N → k}
    (hx : (x : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d) (r : ℕ) :
    ((x ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => d i ^ r := by
  rw [Units.val_pow_eq_pow_val, hx, Matrix.diagonal_pow]
  rfl

theorem val_conj_up (a b c : k) (r : ℕ) :
    valuation k (a ^ r * c * (b ^ r)⁻¹) = (valuation k a / valuation k b) ^ r * valuation k c := by
  rw [map_mul, map_mul, map_inv₀, map_pow, map_pow, div_pow, div_eq_mul_inv, mul_right_comm]

theorem val_conj_lo (a b c : k) (r : ℕ) :
    valuation k ((b ^ r)⁻¹ * c * a ^ r) = (valuation k a / valuation k b) ^ r * valuation k c := by
  rw [← val_conj_up]
  congr 1
  ring

theorem up_entries {N : ℕ} {t n : GL (Fin N) k} {d : Fin N → k}
    (ht : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d)
    (h0 : ∀ i j : Fin N, j < i → (n : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i : Fin N, (n : Matrix (Fin N) (Fin N) k) i i = 1) (r : ℕ) :
    (∀ i j : Fin N, j < i → ((t ^ r * n * (t ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0) ∧
    (∀ i : Fin N, ((t ^ r * n * (t ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i = 1) ∧
    ∀ i j : Fin N, valuation k (((t ^ r * n * (t ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) =
      (valuation k (d i) / valuation k (d j)) ^ r * valuation k ((n : Matrix (Fin N) (Fin N) k) i j) := by
  have hp := val_pow_diag ht r
  have hq := val_inv_diag hp
  have he := entry_diag_mul n hp hq
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
  · rw [he, h0 i j hij, mul_zero, zero_mul]
  · rw [he, h1, mul_one]
    exact mul_inv_cancel₀ (pow_ne_zero _ (diag_ne_zero ht i))
  · rw [he]
    exact val_conj_up _ _ _ r

theorem lo_entries {N : ℕ} {t n : GL (Fin N) k} {d : Fin N → k}
    (ht : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d)
    (h0 : ∀ i j : Fin N, i < j → (n : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i : Fin N, (n : Matrix (Fin N) (Fin N) k) i i = 1) (r : ℕ) :
    (∀ i j : Fin N, i < j → (((t ^ r)⁻¹ * n * t ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0) ∧
    (∀ i : Fin N, (((t ^ r)⁻¹ * n * t ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i = 1) ∧
    ∀ i j : Fin N, valuation k ((((t ^ r)⁻¹ * n * t ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) =
      (valuation k (d j) / valuation k (d i)) ^ r * valuation k ((n : Matrix (Fin N) (Fin N) k) i j) := by
  have hp := val_pow_diag ht r
  have hq := val_inv_diag hp
  have he := entry_diag_mul n hq hp
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
  · rw [he, h0 i j hij, mul_zero, zero_mul]
  · rw [he, h1, mul_one]
    exact inv_mul_cancel₀ (pow_ne_zero _ (diag_ne_zero ht i))
  · rw [he]
    exact val_conj_lo _ _ _ r

theorem ratio_lt_one {a b : ValueGroupWithZero k} (h : a < b) : a / b < 1 :=
  (div_lt_one₀ (lt_of_le_of_lt zero_le' h)).2 h

theorem exists_contract {N : ℕ} {d : Fin N → k} (hd : ∀ i, d i ≠ 0)
    (hinc : ∀ i j : Fin N, i < j → valuation k (d i) < valuation k (d j))
    {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    ∃ r : ℕ, ∀ i j : Fin N, i < j → (valuation k (d i) / valuation k (d j)) ^ r < γ := by
  classical
  have h : ∀ p : Fin N × Fin N, ∃ r : ℕ, p.1 < p.2 → ∀ r' : ℕ, r ≤ r' →
      (valuation k (d p.1) / valuation k (d p.2)) ^ r' < γ := by
    intro p
    by_cases hp : p.1 < p.2
    · have h1 := ratio_lt_one (hinc _ _ hp)
      have h2 : valuation k (d p.1) / valuation k (d p.2) ≠ 0 :=
        div_ne_zero ((Valuation.ne_zero_iff _).2 (hd _)) ((Valuation.ne_zero_iff _).2 (hd _))
      obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.CongruenceBasis.exists_pow_succ_lt h2 h1 hγ
      exact ⟨m + 1, fun _ r' hr' => lt_of_le_of_lt (pow_le_pow_of_le_one zero_le' h1.le hr') hm⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose f hf using h
  exact ⟨Finset.univ.sup f, fun i j hij => hf (i, j) hij _ (Finset.le_sup (Finset.mem_univ _))⟩

theorem levi_comm {N : ℕ} (s x : Levi k (Bl (ones N))) : s * x = x * s := by
  funext a
  haveI : Subsingleton (Fin (ones N a)) := by
    show Subsingleton (Fin 1)
    infer_instance
  apply Units.ext
  ext i j
  obtain rfl : i = j := Subsingleton.elim i j
  simp only [Units.val_mul, Matrix.mul_apply, Pi.mul_apply]
  rw [Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i, mul_comm]

theorem torEmb_diag {N : ℕ} (s : Levi k (Bl (ones N))) :
    ((torEmb k N s : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((torEmb k N s : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ h]
    exact tor_offDiag (⟨s, rfl⟩ : torEmb k N s ∈ Tor k N) h

theorem sub_one_le {N : ℕ} {x : GL (Fin N) k} {γ : ValueGroupWithZero k}
    (h1 : ∀ i, (x : Matrix (Fin N) (Fin N) k) i i = 1)
    (h2 : ∀ i j, i ≠ j → valuation k ((x : Matrix (Fin N) (Fin N) k) i j) ≤ γ) (i j : Fin N) :
    valuation k ((x : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ γ := by
  by_cases h : i = j
  · subst h
    rw [h1, Matrix.one_apply_eq, sub_self, map_zero]
    exact zero_le'
  · rw [Matrix.one_apply_ne h, sub_zero]
    exact h2 i j h

theorem exists_value_subset {N : ℕ} {U : Set (GL (Fin N) k)} (hU : IsOpen U) (h1 : (1 : GL (Fin N) k) ∈ U) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ g : GL (Fin N) k, (∀ i j,
      valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ γ) → g ∈ U := by
  have hne : algebraMap 𝒪[k] k (Zls.unif k) ≠ 0 :=
    (map_ne_zero_iff (algebraMap 𝒪[k] k) (IsFractionRing.injective 𝒪[k] k)).2 Zls.irreducible_unif.ne_zero
  obtain ⟨M, -, hsub⟩ := GlobalTheory.CompanionTheory.CongruenceBasis.exists_congruence_subset k N _ hne
    GlobalTheory.CompanionTheory.CongruenceBasis.val_unif_lt_one GlobalTheory.CompanionTheory.CongruenceBasis.val_le_val_unif U (hU.mem_nhds h1)
  exact ⟨_, (Valuation.ne_zero_iff _).2 (pow_ne_zero M hne), fun g hg => hsub hg⟩

end GlobalTheory.CompanionTheory.LbElem.JPredDom

end
end

section

open GlobalTheory.BCT
open scoped Classical Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitConvHecke

theorem relIndex_ne_zero_of_isOpen {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (K L : Subgroup H) (hL : IsOpen (L : Set H)) (hK : IsCompact (K : Set H)) :
    L.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hop : IsOpen ((L.subgroupOf K : Subgroup K) : Set K) :=
    hL.preimage continuous_subtype_val
  haveI : Finite (K ⧸ L.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hop
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.SplitConvHecke
end
end
