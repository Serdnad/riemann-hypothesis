module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle099
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.SelfDualLattice

section Forms

variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
  {h : V → V → K.E}

def formL (hadd : ∀ x y z, h (x + y) z = h x z + h y z) (hsmul : ∀ (c : K.E) x z, h (c • x) z = c * h x z)
    (z : V) : V →ₗ[K.E] K.E where
  toFun x := h x z
  map_add' x y := hadd x y z
  map_smul' c x := hsmul c x z

end Forms

end GlobalTheory.SelfDualLattice

namespace GlobalTheory.SelfDualLattice

variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
  {h : V → V → K.E}

end GlobalTheory.SelfDualLattice

namespace GlobalTheory.SelfDualLattice

theorem exists_orthonormal_family (K : UQ)
    (hN : ∀ u : K.Oˣ, K.c (algebraMap K.O K.E u) = algebraMap K.O K.E u →
      ∃ z : K.Oˣ, algebraMap K.O K.E u = algebraMap K.O K.E z * K.c (algebraMap K.O K.E z))
    (hT : ∃ z : K.O, algebraMap K.O K.E z + K.c (algebraMap K.O K.E z) = 1) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
      [Module.Finite K.E V] (h : V → V → K.E), Module.finrank K.E V = n →
      (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) →
      (∀ x y, h y x = K.c (h x y)) → ∀ L : Submodule K.O V, L.FG →
      Submodule.span K.E (L : Set V) = ⊤ →
      (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
      ∃ m, ∃ v : Fin m → V, (∀ i j, h (v i) (v j) = if i = j then 1 else 0) ∧
        Submodule.span K.O (Set.range v) = L := by
  first
  | exact @_root_.GlobalTheory.UnitPairNorm.main
  | exact _root_.GlobalTheory.UnitPairNorm.main
  | (apply _root_.GlobalTheory.UnitPairNorm.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitPairNorm.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitPairNorm.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitPairNorm.main ..)

end GlobalTheory.SelfDualLattice

namespace GlobalTheory.SelfDualLattice

theorem exists_orthonormal_basis : ∀ (K : UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (h : V → V → K.E),
    (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) →
    (∀ x y, h y x = K.c (h x y)) → ∀ L : Submodule K.O V, L.FG →
    Submodule.span K.E (L : Set V) = ⊤ →
    (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, Submodule.span K.O (Set.range b) = L ∧
      ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  intro K V _ _ _ _ _ h hadd hsmul hsym L hfg hspan hdual
  obtain ⟨hN, hT, -, -⟩ := GlobalTheory.T.unramifiedQuadratic_norms_trace_uniformizer_facts K
  obtain ⟨m, v, hvo, hvs⟩ := exists_orthonormal_family K hN hT _ V h rfl hadd hsmul hsym L hfg hspan hdual
  have hli : LinearIndependent K.E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (formL hadd hsmul (v i)) hg

    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    change ∑ j, g j * h (v j) (v i) = 0 at this
    simpa [hvo] using this
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range v) := by
    rw [← hspan, ← hvs, Submodule.span_span_of_tower]
  set b0 := Module.Basis.mk hli hsp with hb0
  have hm : m = Module.finrank K.E V := by
    rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
  refine ⟨b0.reindex (finCongr hm), ?_, ?_⟩
  · rw [Module.Basis.range_reindex, hb0, Module.Basis.coe_mk, hvs]
  · intro i j
    simp only [Module.Basis.reindex_apply, hb0, Module.Basis.coe_mk, hvo]
    simp

end GlobalTheory.SelfDualLattice
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.EtInv

section Gen
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] [Module.Finite F K]

theorem eq_zero_of_trace_mul [CharZero F] [IsReduced K] (a : K)
    (h : ∀ x : K, Algebra.trace F K (x * a) = 0) : a = 0 := by
  classical
  let b := Module.finBasis F K
  have hn : IsNilpotent (Algebra.leftMulMatrix b a) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]
    exact h _
  obtain ⟨m, hm⟩ := hn
  rw [← map_pow, ← map_zero (Algebra.leftMulMatrix b)] at hm
  exact (IsNilpotent.eq_zero ⟨m, Algebra.leftMulMatrix_injective b hm⟩)

variable {r : ℕ} {τ : K}

theorem trace_mul_eq_sum (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ)) (x a : K) :
    Algebra.trace F K (x * a) = ∑ j, bb.repr x j * Algebra.trace F K (τ ^ (j : ℕ) * a) := by
  conv_lhs => rw [← bb.sum_repr x]

  simp [Finset.sum_mul, smul_mul_assoc, map_sum, hb]

end Gen

section Comp
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] {r : ℕ} {τ : K} {p : Fin r → F}

theorem leftMulMatrix_eq_companion (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ))
    (hr : τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0) : Algebra.leftMulMatrix bb τ = companion p := by
  classical
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, hb, ← pow_succ']
  simp only [companion, Matrix.of_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · rw [if_pos hj, hj, eq_neg_of_add_eq_zero_left hr]
    have : ∑ k, p k • τ ^ (k : ℕ) = ∑ k, p k • bb k := by simp [hb]
    rw [this, map_neg, Finsupp.neg_apply, bb.repr_sum_self]
  · rw [if_neg hj]
    have hlt : (j : ℕ) + 1 < r := by omega
    have : τ ^ ((j : ℕ) + 1) = bb ⟨(j : ℕ) + 1, hlt⟩ := by rw [hb]
    rw [this, bb.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = (j : ℕ) + 1
    · rw [if_pos (Fin.ext hi.symm), if_pos hi]
    · rw [if_neg (fun h => hi (by rw [← h])), if_neg hi]

theorem companion_pow_mulVec (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ))
    (hr : τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0) (n : ℕ) :
    (companion p ^ n) *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : F) else 0) = ⇑(bb.repr (τ ^ n)) := by
  classical
  induction n with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec, pow_zero]
    funext i
    have hr0 : 0 < r := lt_of_le_of_lt (Nat.zero_le _) i.2
    have h1 : (1 : K) = bb ⟨0, hr0⟩ := by rw [hb]; simp
    rw [h1, bb.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
    · rw [if_neg hi, if_neg (fun h => hi (by rw [← h]))]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, ← leftMulMatrix_eq_companion bb hb hr,
      Algebra.leftMulMatrix_apply, LinearMap.toMatrix_mulVec_repr, pow_succ']
    rfl

end Comp

theorem invK_regular_iff_isUnit :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p →
      Function.Bijective (fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a)) ∧
      ∀ a : A.K, (∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a)) ∧
        (Delta (A.invK τ p lam a) ≠ 0 ↔ IsUnit a) := by
  intro F E _ _ _ _ hU A r τ p lam hg
  classical
  haveI : CharZero F := hU.charZero
  obtain ⟨hli, hfr, hr⟩ := hg
  let bb : Module.Basis (Fin r) F A.K :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [hfr, Fintype.card_fin])
  have hb : ∀ i, bb i = τ ^ (i : ℕ) := fun i => by
    simp [bb]
  let Ψ : A.K →ₗ[F] (Fin r → F) :=
    { toFun := fun a i => Algebra.trace F A.K (τ ^ (i : ℕ) * a)
      map_add' := fun a a' => by funext i; simp [mul_add]
      map_smul' := fun c a => by funext i; simp [mul_smul_comm] }
  have hΨ : ∀ a, Ψ a = fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * a) := fun _ => rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    apply eq_zero_of_trace_mul (F := F) a
    intro x
    rw [trace_mul_eq_sum bb hb x a]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun ha j
    simp only [hΨ, Pi.zero_apply] at this
    rw [this, mul_zero]
  have hbij : Function.Bijective Ψ := by
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hfr])).1 hinj
  have hmom : ∀ a : A.K, ∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a) := by
    intro a i
    simp only [mom, sec, Et.invK]
    rw [companion_pow_mulVec bb hb hr i, trace_mul_eq_sum bb hb (τ ^ i) a, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨hbij, fun a => ⟨hmom a, ?_⟩⟩

  have hH : ∀ v : Fin r → F, hankel (A.invK τ p lam a) *ᵥ v = Ψ (a * bb.equivFun.symm v) := by
    intro v
    funext i

    simp only [hankel, Matrix.mulVec, dotProduct, Matrix.of_apply, hmom, hΨ,
    Module.Basis.equivFun_symm_apply, hb, Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]; ring_nf
  have hcomp : Function.Injective (hankel (A.invK τ p lam a)).mulVec ↔ Function.Injective (fun y : A.K => a * y) := by
    constructor
    · intro h y y' hyy
      have := h (a₁ := bb.equivFun y) (a₂ := bb.equivFun y') (by rw [hH, hH]; simp [hyy])
      exact bb.equivFun.injective this
    · intro h v v' hvv
      rw [hH, hH] at hvv
      exact bb.equivFun.symm.injective (h (hinj hvv))
  rw [Delta, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit, hcomp]
  constructor
  · intro h
    have hs : Function.Surjective (Algebra.lmul F A.K a) :=
      LinearMap.injective_iff_surjective.1 h
    obtain ⟨y, hy⟩ := hs 1
    exact ⟨⟨a, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  · intro h
    exact h.mul_right_injective

end GlobalTheory.JR.EtInv
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.RhoProd

theorem out_iff {G : Type} [Group G] (H : Subgroup G) (P : G → Prop)
    (hP : ∀ g h, h ∈ H → (P (g * h) ↔ P g)) (g : G) :
    P (Quotient.out (QuotientGroup.mk g : G ⧸ H)) ↔ P g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh]; exact hP g h h.2

theorem card_prod {G G₁ G₂ : Type} [Group G] [Group G₁] [Group G₂]
    (H : Subgroup G) (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) (e : G ≃* G₁ × G₂)
    (he : ∀ g, g ∈ H ↔ (e g).1 ∈ H₁ ∧ (e g).2 ∈ H₂)
    (P : G → Prop) (P₁ : G₁ → Prop) (P₂ : G₂ → Prop)
    (hP : ∀ g, P g ↔ P₁ (e g).1 ∧ P₂ (e g).2)
    (h₁ : ∀ g h, h ∈ H₁ → (P₁ (g * h) ↔ P₁ g)) (h₂ : ∀ g h, h ∈ H₂ → (P₂ (g * h) ↔ P₂ g)) :
    Nat.card {k : G ⧸ H // P (Quotient.out k)} =
      Nat.card {k : G₁ ⧸ H₁ // P₁ (Quotient.out k)} * Nat.card {k : G₂ ⧸ H₂ // P₂ (Quotient.out k)} := by
  let E : G ⧸ H ≃ (G₁ ⧸ H₁) × (G₂ ⧸ H₂) :=
    (Quotient.congr e.toEquiv (by
      intro a b
      show QuotientGroup.leftRel H a b ↔ (QuotientGroup.leftRel H₁).prod (QuotientGroup.leftRel H₂) (e a) (e b)
      rw [Setoid.prod_apply, QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, he]
      simp [map_mul, map_inv])).trans (Setoid.prodQuotientEquiv _ _).symm
  have hE : ∀ g : G, E (QuotientGroup.mk g) = (QuotientGroup.mk (e g).1, QuotientGroup.mk (e g).2) := by
    intro g; rfl
  have hPi : ∀ g h, h ∈ H → (P (g * h) ↔ P g) := by
    intro g h hh
    rw [hP, hP, map_mul, Prod.fst_mul, Prod.snd_mul]
    exact and_congr (h₁ _ _ ((he h).1 hh).1) (h₂ _ _ ((he h).1 hh).2)
  rw [← Nat.card_prod]
  refine Nat.card_congr ((E.subtypeEquiv ?_).trans (Equiv.subtypeProdEquivProd))
  intro k
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
  rw [hE, out_iff H₁ P₁ h₁, out_iff H₂ P₂ h₂, ← hP]
  exact out_iff H P hPi g

variable {K : UQ}

def torusEquiv (B₁ B₂ : InvAlg K) : (B₁.prod B₂).T ≃* B₁.T × B₂.T where
  toFun t := (⟨Units.map (RingHom.fst B₁.A B₂.A).toMonoidHom (show (B₁.A × B₂.A)ˣ from t.1),
      congrArg Prod.fst t.2⟩,
    ⟨Units.map (RingHom.snd B₁.A B₂.A).toMonoidHom (show (B₁.A × B₂.A)ˣ from t.1),
      congrArg Prod.snd t.2⟩)
  invFun s := ⟨show (B₁.A × B₂.A)ˣ from MulEquiv.prodUnits.symm ((s.1 : B₁.Aˣ), (s.2 : B₂.Aˣ)),
      Prod.ext s.1.2 s.2.2⟩
  left_inv t := by
    apply Subtype.ext; apply Units.ext; rfl
  right_inv s := by
    ext <;> rfl
  map_mul' a b := by
    ext <;> rfl

theorem inv_mul_int (B : InvAlg K) (w : B.A) (g h : B.T)
    (hh : h ∈ (intUnits K.O B.A).subgroupOf B.T) :
    IsIntegral K.O ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) ↔
      IsIntegral K.O ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) := by
  rw [Subgroup.mem_subgroupOf] at hh
  obtain ⟨hi, hi'⟩ := hh
  have e1 : ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) =
      ((((h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w) := by
    simp [mul_inv_rev, Units.val_mul, mul_assoc]
  have e2 : ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) =
      (((h : B.T) : B.Aˣ) : B.A) * ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w) := by
    rw [e1, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  constructor
  · intro H; rw [e2]; exact hi.mul H
  · intro H; rw [e1]; exact hi'.mul H

theorem rho_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (w₁ : B₁.A) (w₂ : B₂.A),
    (B₁.prod B₂).rho ((w₁, w₂) : B₁.A × B₂.A) = B₁.rho w₁ * B₂.rho w₂ := by
  intro K B₁ B₂ w₁ w₂
  unfold InvAlg.rho
  refine card_prod ((intUnits K.O (B₁.prod B₂).A).subgroupOf (B₁.prod B₂).T) _ _ (torusEquiv B₁ B₂) ?_
    (fun g : (B₁.prod B₂).T => IsIntegral K.O ((((g : (B₁.prod B₂).Aˣ)⁻¹ : (B₁.prod B₂).Aˣ) * (show (B₁.prod B₂).A from (w₁, w₂)) : (B₁.prod B₂).A)))
    (fun g : B₁.T => IsIntegral K.O ((((g : B₁.Aˣ)⁻¹ : B₁.Aˣ) * w₁ : B₁.A)))
    (fun g : B₂.T => IsIntegral K.O ((((g : B₂.Aˣ)⁻¹ : B₂.Aˣ) * w₂ : B₂.A)))
    ?_ (inv_mul_int B₁ w₁) (inv_mul_int B₂ w₂)
  · intro g
    simp only [Subgroup.mem_subgroupOf]
    show (IsIntegral K.O (show B₁.A × B₂.A from ((g : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) ∧ IsIntegral K.O (show B₁.A × B₂.A from (((g : (B₁.prod B₂).Aˣ)⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A))) ↔ _
    rw [IsIntegral.pair_iff, IsIntegral.pair_iff]
    exact ⟨fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => ⟨⟨a, c⟩, ⟨b, d⟩⟩, fun ⟨⟨a, c⟩, ⟨b, d⟩⟩ => ⟨⟨a, b⟩, ⟨c, d⟩⟩⟩
  · intro g
    show IsIntegral K.O (show B₁.A × B₂.A from ((((g : (B₁.prod B₂).Aˣ)⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A) * (show (B₁.prod B₂).A from (w₁, w₂)))) ↔ _
    rw [IsIntegral.pair_iff]
    exact Iff.rfl

end GlobalTheory.RhoProd
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.NormInt

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem traceE [U : Unram F E] (z : E) : algebraMap F E (Algebra.trace F E z) = z + star z := by
  have := U.charZero
  obtain ⟨b, d, hb0, hs, hd, hd0⟩ := Unram.exists_basis_antifixed F E
  have h2 := (IsUnit.mk0 (2 : F) two_ne_zero)
  exact (quadratic_star_structure b d hb0 hs hd U.star_fix (IsUnit.mk0 d hd0) h2).2.2.1 z

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y : A.L, (∀ i, ‖j y i‖ ≤ 1) → A.psiK ψ (x * A.NL y) = 1 := by
  intro F E _ _ _ _ U A ψ hψ x r j hj y hy
  have := U.charZero
  have := U.ultraE
  have hE2 : Module.Finite F E := Module.finite_of_finrank_pos (by rw [U.finrank_eq]; norm_num)
  obtain ⟨⟨c⟩, hinj, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have : Module.Free A.K A.L := Module.Free.of_basis c
  have : Module.Finite A.K A.L := Module.Finite.of_basis c
  have : Module.Free E A.L := Module.Free.of_basis (A.push.out.basis (Module.Free.chooseBasis F A.K))
  have : Module.Finite E A.L := Module.Finite.of_basis (A.push.out.basis (Module.Free.chooseBasis F A.K))
  set s : E := star (j y) ⬝ᵥ j y with hs_def

  have hs1 : ‖s‖ ≤ 1 := by
    rw [hs_def, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [Pi.star_apply, norm_mul, U.norm_star]
    exact mul_le_one₀ (hy i) (norm_nonneg _) (hy i)

  have hss : star s = s := by
    rw [hs_def, dotProduct, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, star_mul', star_star, mul_comm]
  have hsL : s = Algebra.trace E A.L (algebraMap A.K A.L x * star y * y) := hj y y
  set T : F := Algebra.trace F A.K (x * A.NL y) with hT
  have hz : algebraMap A.K A.L (x * A.NL y) = algebraMap A.K A.L x * star y * y := by
    rw [map_mul, hN, mul_assoc, mul_comm y]
  have htK : ∀ k : A.K, Algebra.trace A.K A.L (algebraMap A.K A.L k) = 2 • k := by
    intro k
    apply hinj
    rw [htr, A.star_K, map_nsmul, two_nsmul]
  have h1 : Algebra.trace F A.L (algebraMap A.K A.L (x * A.NL y)) = 2 • T := by
    rw [← Algebra.trace_trace (S := A.K), htK, map_nsmul]
  have h2 : Algebra.trace F A.L (algebraMap A.K A.L (x * A.NL y)) = Algebra.trace F E s := by
    rw [← Algebra.trace_trace (S := E), hz, hsL]
  have h3 : algebraMap F E T = s := by
    have e := congrArg (algebraMap F E) (h1.symm.trans h2)
    rw [traceE, hss, map_nsmul, two_nsmul, ← two_mul, ← two_mul] at e
    have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
    have h20 : (2 : E) ≠ 0 := two_ne_zero
    exact mul_left_cancel₀ h20 e
  have hT1 : ‖T‖ ≤ 1 := by rw [← norm_algebraMap' E T, h3]; exact hs1
  exact hψ.1 T hT1

end GlobalTheory.JR.NormInt
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem exists_idempotent_of_not_isField : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by
  intro F E _ _ _ _ _ A hK hL
  obtain ⟨-, hinj, hN, hT, hnd⟩ := Et.quadratic_structure F E A
  have hnt : ∃ x y : A.L, x ≠ y := by
    obtain ⟨x, y, hxy⟩ := hK.exists_pair_ne
    exact ⟨_, _, hinj.ne hxy⟩
  have hy : ∃ y : A.L, y ≠ 0 ∧ ∀ b, y * b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hL ⟨hnt, mul_comm, fun {a} ha => hcon a ha⟩
  obtain ⟨y, hy0, hyu⟩ := hy
  have hz : ∃ z, Algebra.trace A.K A.L (star y * z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (hnd y hcon)
  obtain ⟨z, hz⟩ := hz
  obtain ⟨s, hs⟩ := hK.mul_inv_cancel hz
  have hn : y * star y = 0 := by
    by_contra hne
    have h1 : A.NL y ≠ 0 := by
      intro h0
      apply hne
      rw [← hN, h0, map_zero]
    obtain ⟨n, hn⟩ := hK.mul_inv_cancel h1
    apply hyu (star y * algebraMap A.K A.L n)
    rw [← mul_assoc, ← hN, ← map_mul, hn, map_one]
  have hs' := congrArg (algebraMap A.K A.L) hs
  rw [map_mul, hT, map_one, star_mul', star_star] at hs'
  have hst : star (star y * z * algebraMap A.K A.L s) = y * star z * algebraMap A.K A.L s := by
    rw [star_mul', star_mul', star_star, A.star_K]
  refine ⟨star y * z * algebraMap A.K A.L s, ?_, ?_⟩
  · linear_combination (star y * z * algebraMap A.K A.L s) * hs'
      - (z * star z * algebraMap A.K A.L s ^ 2) * hn
  · rw [hst]
    linear_combination hs'

end GlobalTheory.JR.Hyp
end
