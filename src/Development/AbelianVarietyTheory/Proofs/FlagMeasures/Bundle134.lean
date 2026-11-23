module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle121
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KMapInto

section
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ : Fin n → ℝ} {S : Submodule ℂ H}

theorem comap_bot_or_top (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s))
    (W : Submodule ℂ H) (hW : IsKStableOn ε σ W) :
    (∀ s : S, T s ∈ W → s = 0) ∨ (∀ s : S, T s ∈ W) := by
  obtain ⟨_, hSst, hSirr, _, _⟩ := hS
  have hle : (W.comap T).map S.subtype ≤ S := by
    rintro _ ⟨s, _, rfl⟩
    exact s.2
  have hst : IsKStableOn ε σ ((W.comap T).map S.subtype) := by
    rintro g hg _ ⟨s, hs, rfl⟩
    refine ⟨⟨σ g s, hSst g hg s s.2⟩, ?_, rfl⟩
    show T _ ∈ W
    rw [hT g hg s _ rfl]
    exact hW g hg _ hs
  rcases hSirr _ hle hst with h | h
  · left
    intro s hs
    have hmem : (s : H) ∈ (W.comap T).map S.subtype := ⟨s, hs, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  · right
    intro s
    have hmem : (s : H) ∈ (W.comap T).map S.subtype := by
      rw [h]
      exact s.2
    obtain ⟨t, ht, hts⟩ := hmem
    obtain rfl : t = s := Subtype.ext hts
    exact ht

theorem inj_or_zero (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s)) :
    (∀ s : S, T s = 0 → s = 0) ∨ (∀ s : S, T s = 0) := by
  have hbot : IsKStableOn ε σ (⊥ : Submodule ℂ H) := by
    intro g _ v hv
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  simpa only [Submodule.mem_bot] using comap_bot_or_top hS T hT ⊥ hbot

theorem range_isKType (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s))
    (hinj : ∀ s : S, T s = 0 → s = 0) : IsKTypeOf ε σ Λ (LinearMap.range T) := by
  have hS' := hS
  obtain ⟨hfin, hSst, _, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS'
  have key : ∀ s : S, ∀ t ∈ Kset ε, ∀ c : ℂ, σ t (T s) = c • T s → σ t s = c • (s : H) := by
    intro s t ht c h
    have h2 : T (⟨σ t s, hSst t ht s s.2⟩ - c • s) = 0 := by
      rw [map_sub, map_smul, hT t ht s _ rfl, h, sub_self]
    exact congrArg Subtype.val (sub_eq_zero.mp (hinj _ h2))
  refine ⟨inferInstance, ?_, ?_, ⟨T ⟨v, hvS⟩, ⟨⟨v, hvS⟩, rfl⟩, ?_, ?_⟩, ?_⟩
  · rintro g hg _ ⟨s, rfl⟩
    exact ⟨⟨σ g s, hSst g hg s s.2⟩, hT g hg s _ rfl⟩
  · intro S' hle hst
    rcases comap_bot_or_top hS T hT S' hst with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨s, rfl⟩ := hle hx
      rw [h s hx, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨s, rfl⟩
      exact h s
  · intro h
    exact hv0 (congrArg Subtype.val (hinj _ h))
  · intro θ hθ
    rw [← hT _ hθ ⟨v, hvS⟩ ⟨_, hSst _ hθ v hvS⟩ rfl, ← map_smul]
    exact congrArg T (Subtype.ext (hvw θ hθ))
  · intro μ w hw hw0 hww
    obtain ⟨s, rfl⟩ := hw
    refine hdom μ s s.2 ?_ ?_
    · intro h
      apply hw0
      obtain rfl : s = 0 := Subtype.ext h
      exact map_zero T
    · intro θ hθ
      exact key s _ hθ _ (hww θ hθ)

theorem scalar_of_range_le (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s))
    (hle : ∀ s, T s ∈ S) : ∃ c : ℂ, ∀ s, T s = c • (s : H) := by
  have hS' := hS
  obtain ⟨hfin, _, _, ⟨v, hvS, hv0, _⟩, _⟩ := hS'
  haveI : Nontrivial S := ⟨⟨⟨v, hvS⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (LinearMap.codRestrict S T hle)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hK : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s →
      (T - c • S.subtype) s' = σ k ((T - c • S.subtype) s) := by
    intro k hk s s' hs'
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, map_sub, map_smul,
      hT k hk s s' hs', hs']
  rcases inj_or_zero hS (T - c • S.subtype) hK with h | h
  · exfalso
    have e : T w = c • (w : H) := congrArg Subtype.val hw.apply_eq_smul
    refine hw.2 (h w ?_)
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, e, sub_self]
  · intro s
    have hs := h s
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, sub_eq_zero] at hs
    exact hs

end

theorem kMap_lowKSub_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∀ T : lowKSub ε lam σ →ₗ[ℂ] H, (∀ k ∈ Kset ε, ∀ s s' : lowKSub ε lam σ, (s' : H) = σ k s → T s' = σ k (T s)) → ∃ c : ℂ, ∀ s, T s = c • (s : H) := by
  intro n ε lam H _ _ _ σ _ hK T hT
  rcases inj_or_zero hK T hT with h | h
  · refine scalar_of_range_le hK T hT ?_
    intro s
    have hle : LinearMap.range T ≤ lowKSub ε lam σ := le_sSup (range_isKType hK T hT h)
    exact hle ⟨s, rfl⟩
  · exact ⟨0, fun s => by rw [h s, zero_smul]⟩

end GlobalTheory.KMapInto
end

section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

namespace GlobalTheory.RowLev.LevelIdem

open GlobalTheory.BadShare GlobalTheory.BadShare.Basic

theorem unitri_sub_one_pow {k : Type} [Field k] {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (h1 : ∀ a, M a a = 1) (h2 : ∀ a b, b < a → M a b = 0) : (M - 1) ^ N = 0 := by
  have ht : (M - 1).BlockTriangular id := by
    intro a b hab
    have hab' : b < a := hab
    rw [Matrix.sub_apply, h2 a b hab', Matrix.one_apply_ne hab'.ne', sub_zero]
  have h := Matrix.aeval_self_charpoly (M - 1)
  rw [Matrix.charpoly_of_isUpperTriangular _ ht] at h
  simpa [h1] using h

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

theorem spec_of_eps (L : Lev g N) (χ : GG g N → ℂ) (hp : IsProj (eps L.Mem χ)) (a : MonoidAlgebra ℂ (GG g N))
    (ha : ∀ x, a.coeff x = eps L.Mem χ x) :
    a * a = a ∧ IsSA a ∧ ∀ q, a.coeff q ≠ 0 → ((q : Matrix (Fin N) (Fin N) (ZMod g)) - 1) ^ N = 0 := by
  have e : a = alg (eps L.Mem χ) := by
    ext x
    rw [coeff_alg, ha]
  refine ⟨by rw [e, ← alg_conv, hp.1], fun q => ?_, fun q hq => ?_⟩
  · rw [ha, ha, hp.2]
    rfl
  · rw [ha] at hq
    have hm : L.Mem q := by
      by_contra hc
      exact hq (if_neg hc)
    exact unitri_sub_one_pow _ hm.1.1 hm.1.2

theorem spec_eDat (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop) (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g)
    (b : Bool) (s k : ℕ) (h : s + k < N)
    (H : ∀ (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) x,
      (eDat g N P φ ψ).coeff x = (levOfChar ψ hψ N b s k h).e x) (ψ : AddChar (ZMod g) ℂ) :
    eDat g N P φ ψ * eDat g N P φ ψ = eDat g N P φ ψ ∧ IsSA (eDat g N P φ ψ) ∧
      ∀ q, (eDat g N P φ ψ).coeff q ≠ 0 → ((q : Matrix (Fin N) (Fin N) (ZMod g)) - 1) ^ N = 0 := by
  by_cases hψ : ψ = 1
  swap
  · exact spec_of_eps _ _ (isProj_e _) _ (H ψ hψ)
  subst hψ
  have h0 : (ZMod.stdAddChar (N := g)) ≠ 1 := (levStandard g N b s k h).hψ
  set L := levOfChar ZMod.stdAddChar h0 N b s k h with hL
  haveI : Nonempty {u // L.Mem u} := ⟨⟨1, mem_one L⟩⟩
  have hc : (Nat.card {u // L.Mem u} : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hP : (fun u : GG g N => P u.val) = L.Mem := by
    funext x
    have hx := H _ h0 x
    rw [coeff_eDat, Lev.e] at hx
    unfold eps at hx
    refine propext ⟨fun h1 => ?_, fun h1 => ?_⟩
    · by_contra h2
      haveI : Nonempty {u : GG g N // P u.val} := ⟨⟨x, h1⟩⟩
      have hc' : (Nat.card {u : GG g N // P u.val} : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
      rw [if_pos h1, if_neg h2] at hx
      refine div_ne_zero (inv_ne_zero fun h3 => ?_) hc' hx
      have := AddChar.norm_apply (ZMod.stdAddChar (N := g)) (φ x.val)
      beta_reduce at h3
      rw [h3] at this
      simp at this
    · by_contra h2
      rw [if_neg h2, if_pos h1] at hx
      exact div_ne_zero (inv_ne_zero (chi_ne L x)) hc hx.symm
  refine spec_of_eps L (fun _ => 1) (GlobalTheory.BadShare.EpsProj.isProj_eps (mem_one L) (fun _ _ => mem_mul L) rfl (fun _ _ _ _ => by simp)) _
    fun x => ?_
  rw [coeff_eDat, hP]
  rfl

theorem eUk_eJk_spec : ∀ (D : D7) (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))), a = eUk D k ψ₀ ∨ a = eJk D k ψ₀ → a * a = a ∧ IsSA a ∧ ∀ q, a.coeff q ≠ 0 → ((q : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) - 1) ^ D.R.r = 0 := by
  intro D k ψ a ha
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hN : D.R.r = D.R.k + 2 * (D.R.m / 2 - 1) + 1 := by
    have := dimS_eq D.R
    unfold Ranks.rS at this
    omega
  have h : (D.R.m / 2 - 1) + D.R.k < D.R.r := by omega
  rcases ha with rfl | rfl
  · exact spec_eDat _ _ false _ _ h (fun ψ hψ x => coeff_eU ψ hψ _ _ h x) ψ
  · exact spec_eDat _ _ true _ _ h (fun ψ hψ x => coeff_eJ ψ hψ _ _ hN h x) ψ

end GlobalTheory.RowLev.LevelIdem
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.TwoSidedJac

open Kronecker

noncomputable def twoSided {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    Matrix (Fin a) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin b) ℂ where
  toFun T := A * T * B
  map_add' S T := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c T := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem twoSided_apply {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (T : Matrix (Fin a) (Fin b) ℂ) : twoSided A B T = A * T * B := rfl

theorem det_twoSided {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    LinearMap.det (twoSided A B) = A.det ^ b * B.det ^ a := by
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin a) (Fin b))]
  have h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin a) (Fin b))
      (Matrix.stdBasis ℂ (Fin a) (Fin b)) (twoSided A B) = A ⊗ₖ Bᵀ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, twoSided_apply]
    have hr : ∀ M : Matrix (Fin a) (Fin b) ℂ,
        (Matrix.stdBasis ℂ (Fin a) (Fin b)).repr M (i, j) = M i j := by
      intro M
      simp [Matrix.stdBasis]
    rw [hr]
    simp [Matrix.mul_apply, Matrix.single, Finset.sum_mul, ite_and]
  rw [h, Matrix.det_kronecker, Matrix.det_transpose]
  simp

section Skew

variable {a : ℕ} {ι : Type} [Fintype ι]

theorem star_coe (T : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ)) :
    star (T : Matrix (Fin a) (Fin a) ℂ) = -(T : Matrix (Fin a) (Fin a) ℂ) :=
  skewAdjoint.mem_iff.mp T.2

theorem linearIndependent_skew
    (e : Module.Basis ι ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))) :
    LinearIndependent ℂ (fun i => (e i : Matrix (Fin a) (Fin a) ℂ)) := by
  have hR : ∀ g : ι → ℝ, ∑ i, (g i : ℂ) • (e i : Matrix (Fin a) (Fin a) ℂ) = 0 → ∀ i, g i = 0 := by
    intro g hg
    apply Fintype.linearIndependent_iff.mp e.linearIndependent g
    apply Subtype.ext
    simpa using hg
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h2 : ∑ i, (starRingEnd ℂ (g i)) • (e i : Matrix (Fin a) (Fin a) ℂ) = 0 := by
    have := congrArg star hg
    simp only [star_sum, star_smul, star_coe, smul_neg, Finset.sum_neg_distrib, star_zero,
      neg_eq_zero] at this
    exact this
  have hre : ∀ i, 2 * (g i).re = 0 := by
    apply hR
    have : ∀ i, ((2 * (g i).re : ℝ) : ℂ) = g i + starRingEnd ℂ (g i) := fun i =>
      (Complex.add_conj _).symm
    simp only [this, add_smul, Finset.sum_add_distrib, hg, h2, add_zero]
  have him : ∀ i, 2 * (g i).im = 0 := by
    apply hR
    have : ∀ i, ((2 * (g i).im : ℝ) : ℂ) = (-Complex.I) * (g i - starRingEnd ℂ (g i)) := by
      intro i
      rw [Complex.sub_conj]
      have := Complex.I_mul_I
      linear_combination ((2 * (g i).im : ℝ) : ℂ) * this
    simp only [this, mul_smul, ← Finset.smul_sum, sub_smul, Finset.sum_sub_distrib, hg, h2,
      sub_zero, smul_zero]
  intro i
  apply Complex.ext
  · have := hre i
    simpa using this
  · have := him i
    simpa using this

theorem span_skew
    (e : Module.Basis ι ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun i => (e i : Matrix (Fin a) (Fin a) ℂ)) := by
  have hS : ∀ T : Matrix (Fin a) (Fin a) ℂ, star T = -T →
      T ∈ Submodule.span ℂ (Set.range fun i => (e i : Matrix (Fin a) (Fin a) ℂ)) := by
    intro T hT
    have h := congrArg Subtype.val (e.sum_repr ⟨T, skewAdjoint.mem_iff.mpr hT⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    rw [← h]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro T _
  have h1 := hS (T - star T) (by simp)
  have h2 := hS (Complex.I • (T + star T)) (by simp [star_smul, add_comm])
  have : T = (1 / 2 : ℂ) • ((T - star T) + (-Complex.I) • (Complex.I • (T + star T))) := by
    rw [smul_smul]
    simp only [neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    module
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2))

theorem det_skew_eq
    (L : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ) →ₗ[ℝ]
      skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))
    (F : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (h : ∀ T, (L T : Matrix (Fin a) (Fin a) ℂ) = F T) :
    ((LinearMap.det L : ℝ) : ℂ) = LinearMap.det F := by
  classical
  let e := Module.finBasis ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))
  let e' := Module.Basis.mk (linearIndependent_skew e) (span_skew e)
  have he : ∀ i, e' i = (e i : Matrix (Fin a) (Fin a) ℂ) := fun i => Module.Basis.mk_apply _ _ i
  rw [← LinearMap.det_toMatrix e, ← LinearMap.det_toMatrix e']
  have hm : LinearMap.toMatrix e' e' F = (LinearMap.toMatrix e e L).map Complex.ofRealHom := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, he, ← h]
    have h1 : (L (e j) : Matrix (Fin a) (Fin a) ℂ) =
        ∑ k, ((e.repr (L (e j)) k : ℝ) : ℂ) • e' k := by
      have h := congrArg Subtype.val (e.sum_repr (L (e j)))
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
      rw [← h]
      simp only [he, Complex.coe_smul]
    rw [h1, e'.repr_sum_self]
    rfl
  rw [hm]
  exact RingHom.map_det Complex.ofRealHom _

end Skew

theorem real_jacobians :
    (∀ (a b : ℕ) (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) (L : Matrix (Fin a) (Fin b) ℂ →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ), (∀ T, L T = A * T * B) → LinearMap.det L = ‖A.det‖ ^ (2 * b) * ‖B.det‖ ^ (2 * a)) ∧ ∀ (a : ℕ) (A : Matrix (Fin a) (Fin a) ℂ) (L : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ) →ₗ[ℝ] skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ)), (∀ T, ((L T : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ)) : Matrix (Fin a) (Fin a) ℂ) = A * (T : Matrix (Fin a) (Fin a) ℂ) * Aᴴ) → LinearMap.det L = ‖A.det‖ ^ (2 * a) := by
  refine ⟨fun a b A B L hL => ?_, fun a A L hL => ?_⟩
  · have : L = (twoSided A B).restrictScalars ℝ := LinearMap.ext hL
    rw [this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, det_twoSided,
      Complex.normSq_eq_norm_sq, norm_mul, norm_pow, norm_pow]
    ring
  · have h := det_skew_eq L (twoSided A Aᴴ) hL
    rw [det_twoSided, Matrix.det_conjTranspose, ← mul_pow] at h
    apply Complex.ofReal_injective
    rw [h, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
    push_cast
    rfl

end GlobalTheory.TwoSidedJac
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

noncomputable def matrixEntriesEuclideanReal (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] PiLp 2 (fun _ : Fin n × Fin n => ℂ) where
  toFun X := WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun v := Matrix.of fun i j => v.ofLp (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem inner_matrixEntriesEuclideanReal (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    inner ℝ (matrixEntriesEuclideanReal n Y) (matrixEntriesEuclideanReal n X)
      = ((X * Yᴴ).trace).re := by
  change inner ℝ (WithLp.toLp 2 (fun p : Fin n × Fin n => Y p.1 p.2))
      (WithLp.toLp 2 (fun p : Fin n × Fin n => X p.1 p.2)) = _
  rw [PiLp.inner_apply]
  simp only [WithLp.ofLp_toLp, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.inner, mul_comm]

theorem exists_orthonormal_basis_re_trace_mul_conjTranspose (n : ℕ)
    (U : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ),
      (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ LinearIndependent ℝ E ∧
        U = Submodule.span ℝ (Set.range E) := by
  classical
  set e := matrixEntriesEuclideanReal n
  set V : Submodule ℝ (PiLp 2 (fun _ : Fin n × Fin n => ℂ)) := U.map e.toLinearMap
  let b := stdOrthonormalBasis ℝ V
  refine ⟨Module.finrank ℝ V, fun i => e.symm (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ)), ?_, ?_, ?_⟩
  · intro i k
    have h := inner_matrixEntriesEuclideanReal n (e.symm (b i)) (e.symm (b k))
    simp only [e, LinearEquiv.apply_symm_apply] at h
    rw [← h, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal k i]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik, Ne.symm hik]
  · have hb : LinearIndependent ℝ (fun i => (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ))) :=
      b.orthonormal.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    exact hb.map' e.symm.toLinearMap e.symm.ker
  · symm
    have hrange : Set.range (fun i => e.symm (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ)))
        = e.symm.toLinearMap '' (V.subtype '' Set.range b) := by
      ext x; simp [Set.mem_image, Set.mem_range]
    have hspan : Submodule.span ℝ (Set.range b) = ⊤ := by
      simpa [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
    rw [hrange, Submodule.span_image, Submodule.span_image, hspan, Submodule.map_subtype_top]
    ext x
    simp [V]

end GlobalTheory
end
