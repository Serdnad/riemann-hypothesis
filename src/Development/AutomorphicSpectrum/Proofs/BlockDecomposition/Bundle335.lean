module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.OpenOrbit

section Perm

variable {k : Type} [Field k]

def permGL {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) k where
  val := (1 : Matrix _ _ k).submatrix σ id
  inv := (1 : Matrix _ _ k).submatrix id σ
  val_inv := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, mul_one]
    exact Matrix.submatrix_one_equiv σ
  inv_val := by
    rw [← Matrix.submatrix_mul _ _ _ σ _ σ.bijective, mul_one]
    exact Matrix.submatrix_one_equiv (Equiv.refl _)

theorem permGL_mul_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (B : Matrix (Fin N) (Fin N) k) (a c : Fin N) :
    (((permGL σ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) * B) a c = B (σ a) c := by
  show (((1 : Matrix (Fin N) (Fin N) k).submatrix σ id) * B) a c = _
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem vecMul_single_one {N : ℕ} (M : Matrix (Fin N) (Fin N) k) (a : Fin N) :
    vecMul (Pi.single a 1) M = M a := by
  ext c
  simp [vecMul, dotProduct, Pi.single_apply]

end Perm

section Orbit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdSum_inr_ne_inl {r t N : ℕ} (h : r + t = N) (j : Fin t) (l : Fin r) :
    stdSum h (Sum.inr j) ≠ stdSum h (Sum.inl l) := fun e => by
  simpa using (stdSum h).injective e

theorem wPerm_first {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    wPerm h (stdSum h (Sum.inl (Fin.last i))) = Fin.last (i + t) := by
  have e : (two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  show ePG i t ((two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i)))) = _
  rw [e]
  exact ePG_false_last i t

theorem lastRow_wInv {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (eLast k (i + t)) (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) =
      Pi.single (stdSum h (Sum.inl (Fin.last i))) 1 := by
  rw [show eLast k (i + t) = Pi.single (Fin.last (i + t)) 1 from rfl, vecMul_single_one]
  ext c
  show (1 : Matrix _ _ k).submatrix id (wPerm h) (Fin.last (i + t)) c = _
  rw [← wPerm_first h]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem lastRow_inv {i t : ℕ} (h : (i + 1) + t = i + t + 1) (q p : GL (Fin (i + t + 1)) k)
    (hp : p ∈ Mir k (i + t)) :
    vecMul (eLast k (i + t)) (((q * wGL k h * p)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) =
      ((q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (stdSum h (Sum.inl (Fin.last i))) := by
  have hp' : vecMul (eLast k (i + t)) ((p⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) = eLast k (i + t) :=
    (Mir k (i + t)).inv_mem hp
  rw [show (q * wGL k h * p)⁻¹ = p⁻¹ * (wGL k h)⁻¹ * q⁻¹ by simp [mul_assoc], Units.val_mul, Units.val_mul,
    ← vecMul_vecMul, ← vecMul_vecMul, hp', lastRow_wInv, vecMul_single_one]

theorem exists_ne_of_mem {i t : ℕ} (h : (i + 1) + t = i + t + 1) (q p : GL (Fin (i + t + 1)) k)
    (hq : q ∈ parab k (two (stdSum h))) (hp : p ∈ Mir k (i + t)) :
    ∃ a : Fin (i + 1), (((q * wGL k h * p)⁻¹ : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0 := by
  by_contra hc
  push_neg at hc
  let r : parab k (two (stdSum h)) := ⟨q⁻¹, inv_mem hq⟩
  let M : GL (Fin (i + 1)) k := leviProj k (two (stdSum h)) r false
  have hrow : ∀ a, (M : Matrix (Fin (i + 1)) (Fin (i + 1)) k) (Fin.last i) a = 0 := fun a => by
    have e := congrFun (lastRow_inv h q p hp) (stdSum h (Sum.inl a))
    rw [show eLast k (i + t) = Pi.single (Fin.last (i + t)) 1 from rfl, vecMul_single_one, hc a] at e
    exact e.symm
  have h1 : ((M : Matrix (Fin (i + 1)) (Fin (i + 1)) k) *
      ((M⁻¹ : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k)) (Fin.last i) (Fin.last i) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel]
    simp
  rw [Matrix.mul_apply] at h1
  simp [hrow] at h1

theorem exists_parab_row {i t : ℕ} (h : (i + 1) + t = i + t + 1) (y : Fin (i + t + 1) → k) (a : Fin (i + 1))
    (ha : y (stdSum h (Sum.inl a)) ≠ 0) :
    ∃ b ∈ parab k (two (stdSum h)),
      (b : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (stdSum h (Sum.inl (Fin.last i))) = y := by
  obtain ⟨b, -, -, hb⟩ := exists_rowSec (k := k) (stdSum h (Sum.inl a))
  have hb0 := hb y ha
  have hbQ : b y ∈ parab k (two (stdSum h)) := by
    refine mem_parab_iff.2 ?_
    rintro (_ | _) (_ | _) l j hlt
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · rw [hb0, two_true, two_false, Matrix.updateRow_ne (stdSum_inr_ne_inl h l a),
        Matrix.one_apply_ne (stdSum_inr_ne_inl h l j)]
    · exact absurd hlt (by decide)
  have hmQ : (permGL (Equiv.swap (stdSum h (Sum.inl a)) (stdSum h (Sum.inl (Fin.last i)))) : GL (Fin (i + t + 1)) k) ∈
      parab k (two (stdSum h)) := by
    refine mem_parab_iff.2 ?_
    rintro (_ | _) (_ | _) l j hlt
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · show (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Equiv.swap (stdSum h (Sum.inl a)) (stdSum h (Sum.inl (Fin.last i))) (stdSum h (Sum.inr l)))
        (stdSum h (Sum.inl j)) = 0
      rw [Equiv.swap_apply_of_ne_of_ne (stdSum_inr_ne_inl h l a) (stdSum_inr_ne_inl h l _),
        Matrix.one_apply_ne (stdSum_inr_ne_inl h l j)]
    · exact absurd hlt (by decide)
  refine ⟨_, mul_mem hmQ hbQ, ?_⟩
  funext c
  rw [Units.val_mul, permGL_mul_apply, Equiv.swap_apply_right, hb0, Matrix.updateRow_self]

theorem mem_of_ne {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k) (a : Fin (i + 1))
    (ha : ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0) :
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  obtain ⟨b, hbQ, hrow⟩ := exists_parab_row h _ a ha
  refine ⟨b⁻¹, inv_mem hbQ, (wGL k h)⁻¹ * b * g, ?_, by group⟩
  show vecMul (eLast k (i + t)) (((wGL k h)⁻¹ * b * g : GL (Fin (i + t + 1)) k) : Matrix _ _ k) = eLast k (i + t)
  have e : ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) =
      vecMul (eLast k (i + t)) ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) := by
    rw [show eLast k (i + t) = Pi.single (Fin.last (i + t)) 1 from rfl, vecMul_single_one]
  rw [Units.val_mul, Units.val_mul, ← vecMul_vecMul, ← vecMul_vecMul, lastRow_wInv, vecMul_single_one, hrow, e,
    vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]

end Orbit

end GlobalTheory.CompanionTheory.BZRes.OpenOrbit

namespace GlobalTheory.CompanionTheory.BZRes

theorem mem_dcos_wGL_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k,
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) ↔
      ∃ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0 := by
  intro k _ _ _ _ i t h _ g
  constructor
  · rintro ⟨q, hq, p, hp, rfl⟩
    exact OpenOrbit.exists_ne_of_mem h q p hq hp
  · rintro ⟨a, ha⟩
    exact OpenOrbit.mem_of_ne h g a ha

end GlobalTheory.CompanionTheory.BZRes

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem exists_nhds_one_tube {G : Type} [Group G] [TopologicalSpace G] {C : Set G} (hC : IsCompact C)
    {n : Set (G × G)} (hn : IsOpen n) (h : ∀ c ∈ C, (c, (1 : G)) ∈ n) :
    ∃ O ∈ 𝓝 (1 : G), ∀ c ∈ C, ∀ u ∈ O, (c, u) ∈ n :=
  _root_.UpperTheory.Reformulated.B.Ylb7.main hC hn h

theorem finite_image_of_rightInvariant {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] {W : Type}
    (φ : P → W) (K' : Subgroup P) (hK' : IsOpen (K' : Set P)) (hinv : ∀ (p : P), ∀ κ ∈ K', φ (p * κ) = φ p)
    {C : Set P} (hC : IsCompact C) : (φ '' C).Finite := by
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => {p : P | c⁻¹ * p ∈ K'}) (fun c _ => by
    have ho : IsOpen {p : P | c⁻¹ * p ∈ K'} := hK'.preimage (continuous_const.mul continuous_id)
    exact ho.mem_nhds (by simp [K'.one_mem]))
  refine (t.finite_toSet.image φ).subset ?_
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨c, hc, hcp⟩ := Set.mem_iUnion₂.1 (ht hp)
  refine ⟨c, hc, ?_⟩
  have := hinv c _ hcp
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem exists_openSubgroup_consistent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NonarchimedeanGroup G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G} :
    LocSec Q P x → ∀ (σ : Representation ℂ Q W₁), IsSmooth σ → ∀ (φ : P → W₁),
    (∀ (q : Q) (p p' : P), (q : G) * x * (p : G) = x * (p' : G) → φ p' = σ q (φ p)) →
    ∀ (K' : Subgroup P), IsOpen (K' : Set P) → (∀ (p : P), ∀ κ ∈ K', φ (p * κ) = φ p) →
    ∀ (C : Set P), IsCompact C → ∀ (Y : Set G), IsOpen Y → (∀ c ∈ C, x * (c : G) ∈ Y) →
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (∀ c ∈ C, ∀ κ ∈ K, x * (c : G) * κ ∈ Y) ∧
      ∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c) := by
  intro hL σ hσ φ hφ K' hK' hinv C hC Y hY hCY
  have hfin : (φ '' C).Finite := finite_image_of_rightInvariant φ K' hK' hinv hC

  have hopenQ : IsOpen {q : Q | ∀ v ∈ φ '' C, σ q v = v} := by
    have e : {q : Q | ∀ v ∈ φ '' C, σ q v = v} = ⋂ v ∈ φ '' C, {q : Q | σ q v = v} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [e]
    exact hfin.isOpen_biInter fun v _ => hσ v
  obtain ⟨UQ, hUQ, hUQe⟩ := isOpen_induced_iff.1 hopenQ
  have h1UQ : (1 : G) ∈ UQ := by
    have : (1 : Q) ∈ (Subtype.val : Q → G) ⁻¹' UQ := by
      rw [hUQe]
      intro v _
      simp
    exact this
  have hfix : ∀ s : Q, (s : G) ∈ UQ → ∀ c ∈ C, σ s (φ c) = φ c := by
    intro s hs c hc
    have : s ∈ (Subtype.val : Q → G) ⁻¹' UQ := hs
    rw [hUQe] at this
    exact this _ ⟨c, hc, rfl⟩

  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hK'
  have h1U : (1 : G) ∈ U := by
    have : (1 : P) ∈ (Subtype.val : P → G) ⁻¹' U := by
      rw [hUe]
      exact K'.one_mem
    exact this
  have hC' : IsCompact ((Subtype.val : P → G) '' C) := hC.image continuous_subtype_val
  obtain ⟨OP, hOP, hOPc⟩ := exists_nhds_one_tube hC' (n := {z : G × G | z.1⁻¹ * z.2 * z.1 ∈ U})
    (hU.preimage (by fun_prop)) (by
      rintro _ ⟨c, -, rfl⟩
      simpa using h1U)
  obtain ⟨O, hO, hOs⟩ := hL UQ (hUQ.mem_nhds h1UQ) OP hOP
  obtain ⟨O₁, hO₁, hO₁c⟩ := exists_nhds_one_tube hC'
    (n := {z : G × G | z.1 * z.2 * z.1⁻¹ ∈ interior O ∧ x * z.1 * z.2 ∈ Y})
    ((isOpen_interior.preimage (by fun_prop)).inter (hY.preimage (by fun_prop))) (by
      rintro _ ⟨c, hc, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa using mem_interior_iff_mem_nhds.2 hO
      · simpa using hCY c hc)
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean O₁ hO₁
  have hVc : ∀ c ∈ C, ∀ κ ∈ (V : Subgroup G),
      (c : G) * κ * (c : G)⁻¹ ∈ interior O ∧ x * (c : G) * κ ∈ Y := fun c hc κ hκ =>
    hO₁c _ ⟨c, hc, rfl⟩ κ (hV hκ)
  refine ⟨(V : Subgroup G), V.isOpen, fun c hc κ hκ => (hVc c hc κ hκ).2, ?_⟩
  intro c hc κ hκ q p' hq
  have huO : (c : G) * κ * (c : G)⁻¹ ∈ O := interior_subset (hVc c hc κ hκ).1

  have hmem : x * ((c : G) * κ * (c : G)⁻¹) ∈ dcos Q P x := by
    refine ⟨(q : G)⁻¹, Q.inv_mem q.2, (p' : G) * (c : G)⁻¹, P.mul_mem p'.2 (P.inv_mem c.2), ?_⟩
    calc x * ((c : G) * κ * (c : G)⁻¹) = (q : G)⁻¹ * ((q : G) * x * (c : G) * κ) * (c : G)⁻¹ := by group
      _ = (q : G)⁻¹ * x * ((p' : G) * (c : G)⁻¹) := by rw [hq]; group
  obtain ⟨s, hsQ, hsU, p₂, hp₂, hp₂O, he⟩ := hOs _ huO hmem

  have hconj : (c : G)⁻¹ * p₂ * (c : G) ∈ U := hOPc _ ⟨c, hc, rfl⟩ p₂ hp₂O
  have hκ' : (c⁻¹ * ⟨p₂, hp₂⟩ * c : P) ∈ K' := by
    have : (c⁻¹ * ⟨p₂, hp₂⟩ * c : P) ∈ (Subtype.val : P → G) ⁻¹' U := hconj
    rw [hUe] at this
    exact this
  have hval : φ (⟨p₂, hp₂⟩ * c) = φ c := by
    have := hinv c _ hκ'
    rwa [show c * (c⁻¹ * ⟨p₂, hp₂⟩ * c) = ⟨p₂, hp₂⟩ * c by group] at this
  have hrel : (((⟨(q : G) * s, Q.mul_mem q.2 hsQ⟩ : Q)) : G) * x * ((⟨p₂, hp₂⟩ * c : P) : G) = x * (p' : G) := by
    have : (q : G) * s * x * (p₂ * (c : G)) = (q : G) * (s * x * p₂) * (c : G) := by group
    show (q : G) * s * x * (p₂ * (c : G)) = x * (p' : G)
    rw [this, ← he, ← hq]
    group
  have hsplit : (⟨(q : G) * s, Q.mul_mem q.2 hsQ⟩ : Q) = q * ⟨s, hsQ⟩ := rfl
  rw [hφ _ _ _ hrel, hval, hsplit, map_mul, Module.End.mul_apply, hfix ⟨s, hsQ⟩ hsU c hc]

end GlobalTheory.CompanionTheory.BZRes
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.TopCol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entry (n : ℕ) (w : Fin n → k) (a b : Fin (n + 1)) :
    ((uM k n w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b + colMat k n w a b := rfl

theorem ePG_true_eq (i t : ℕ) (b : Fin t) :
    ePG i t ⟨true, b⟩ = Fin.castSucc (Fin.natAdd i b) := by
  first
  | rfl
  | (ext; simp [GlobalTheory.BZMir.Leib.ePG])

theorem ePG_false_eq (i t : ℕ) (a : Fin i) :
    ePG i t ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd t a) := by
  have h : GlobalTheory.BZMir.Leib.ePG i t ⟨false, Fin.castSucc a⟩ =
      ((Equiv.sumCongr (finSumFinEquiv.symm : Fin (i + 1) ≃ Fin i ⊕ Fin 1) (Equiv.refl (Fin t))).trans
        ((Equiv.sumAssoc (Fin i) (Fin 1) (Fin t)).trans
          ((Equiv.sumCongr (Equiv.refl (Fin i)) (Equiv.sumComm (Fin 1) (Fin t))).trans
            ((Equiv.sumAssoc (Fin i) (Fin t) (Fin 1)).symm.trans
              ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv)))))
        (Sum.inl (Fin.castSucc a)) := rfl
  rw [h]
  ext
  simp [finSumFinEquiv_symm_apply_castSucc]

theorem ePG_true_ne_last (i t : ℕ) (b : Fin t) : ePG i t ⟨true, b⟩ ≠ Fin.last (i + t) := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_eq]
  exact Fin.castSucc_ne_last _

theorem mem (i t : ℕ) (x : Fin i → k) : uM k (i + t) (topV k i t x) ∈ HPG k i t := by
  show ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k)) ∈
    GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG i t)
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro a b p q hba
  cases a <;> cases b
  all_goals first
    | exact absurd hba (by decide)
    | (simp at hba; done)
    | skip
  have hne : GlobalTheory.BZMir.Leib.ePG i t ⟨true, p⟩ ≠ GlobalTheory.BZMir.Leib.ePG i t ⟨false, q⟩ := by
    intro h
    have h' : true = false := congrArg Sigma.fst ((GlobalTheory.BZMir.Leib.ePG i t).injective h)
    cases h'
  have hr := GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_eq i t p
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry, Matrix.one_apply_ne hne, zero_add, hr]
  simp only [GlobalTheory.BZMir.colMat]
  split_ifs
  · rw [Fin.lastCases_castSucc]
    simp [GlobalTheory.CompanionTheory.BZPsiPG.topV]
  · rfl

theorem fst (i t : ℕ) (x : Fin i → k) :
    (pgProj k i t ⟨uM k (i + t) (topV k i t x), mem i t x⟩).1 = uM k i x := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  change ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) = _
  have h1 : (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) =
      (1 : Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b := by
    simp [Matrix.one_apply]
  have h2 : GlobalTheory.BZMir.colMat k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) =
      GlobalTheory.BZMir.colMat k i x a b := by
    simp only [GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.Leib.ePG_false_eq_last_iff]
    split_ifs with hb
    · induction a using Fin.lastCases with
      | last => rw [GlobalTheory.BZMir.Leib.ePG_false_last, Fin.lastCases_last, Fin.lastCases_last]
      | cast c =>
        rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_false_eq, Fin.lastCases_castSucc,
          Fin.lastCases_castSucc]
        simp [GlobalTheory.CompanionTheory.BZPsiPG.topV]
    · rfl
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry,
    GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry, h1, h2]

theorem snd (i t : ℕ) (x : Fin i → k) :
    (pgProj k i t ⟨uM k (i + t) (topV k i t x), mem i t x⟩).2 = 1 := by
  apply Units.ext
  ext a b
  change ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨true, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨true, b⟩) =
      (1 : Matrix (Fin t) (Fin t) k) a b
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry]
  simp only [GlobalTheory.BZMir.colMat, if_neg (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_ne_last i t b), add_zero]
  simp [Matrix.one_apply]

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ)
    (x : Fin i → k), ∃ h : uM k (i + t) (topV k i t x) ∈ HPG k i t, pgProj k i t ⟨_, h⟩ = (uM k i x, 1) := by
  intro k _ _ _ _ i t x
  exact ⟨GlobalTheory.CompanionTheory.BZPsiPG.TopCol.mem i t x,
    Prod.ext (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.fst i t x)
      (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.snd i t x)⟩

end GlobalTheory.CompanionTheory.BZPsiPG.TopCol

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem qp_mulVec_midV_exists_top (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (q : Qp k i t) (v : Fin t → k) :
    ∃ x : Fin i → k, ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec (midV k i t v) =
      topV k i t x + midV k i t ((((qBlocks k i t q).2 : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v) := by
  refine ⟨fun r => ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec
    (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) (Fin.castAdd t r), ?_⟩
  rw [GlobalTheory.CompanionTheory.BZPsiPG.topV_add_midV]
  funext r
  refine Fin.addCases (fun a => ?_) (fun b => ?_) r
  · rw [Fin.append_left]
  · rw [Fin.append_right]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, GlobalTheory.CompanionTheory.BZPsiPG.midV, Fin.append_left,
      Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
    rfl

end GlobalTheory.CompanionTheory.BZPsiPG
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

section Abs
variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

def IsBump (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (c : G) (v : W) (B : cIndSpace H ρ) : Prop :=
  (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * c * x) = ρ a v) ∧
    ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * c * x) → B.1.1.1 g = 0

end Abs

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option synthInstance.maxHeartbeats 100000 in
def sO (i t : ℕ) : Mir k (i + (t + 1)) →* Mir k ((i + 1) + t + 1) :=
  (sEmb k ((i + 1) + t)).comp (castM k (by omega : i + (t + 1) = (i + 1) + t)).toMonoidHom

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

theorem _root_.GlobalTheory.T.derivative_twisted_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (j n : ℕ) (π : GRep k (n + j)), GIso (derivB ψ j π) ((dG ψ j π).tw ((j : ℝ) / 2)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.DerivTw.derivB_iso_tw | exact GlobalTheory.CompanionTheory.LeibOrd.DerivTw.derivB_iso_tw | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.DerivTw.derivB_iso_tw <;> assumption)
end
