module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.GroupTheory.Commensurable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index
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
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Flat.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Polynomial IsLocalRing

namespace GlobalTheory.UnitPowerExistence

theorem exists_unit_pow_eq (O : Type) [CommRing O] [HenselianLocalRing O]
    [IsSepClosed (IsLocalRing.ResidueField O)] (q : ℕ) (hq : IsUnit (q : O)) (hpos : 0 < q)
    (w : Oˣ) : ∃ v : Oˣ, v ^ q = w := by
  have hq0 : (q : ResidueField O) ≠ 0 := by
    have h := hq.map (residue O)
    rw [map_natCast] at h
    exact h.ne_zero
  have hw : residue O (w : O) ≠ 0 := (w.isUnit.map (residue O)).ne_zero
  obtain ⟨a₀, ha₀⟩ := IsSepClosed.exists_root (X ^ q - C (residue O (w : O)))
    (by rw [degree_X_pow_sub_C hpos]; exact_mod_cast hpos.ne') (separable_X_pow_sub_C _ hq0 hw)
  obtain ⟨b, rfl⟩ := residue_surjective a₀
  have hb : b ^ q - (w : O) ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff, map_sub, map_pow]
    simpa [IsRoot] using ha₀
  have hbu : IsUnit b := by
    by_contra hb'
    have h2 : b ^ q ∈ maximalIdeal O := Ideal.pow_mem_of_mem _ ((mem_maximalIdeal b).2 hb') q hpos
    have h3 : (w : O) ∈ maximalIdeal O := by simpa using sub_mem h2 hb
    exact (mem_maximalIdeal _).1 h3 w.isUnit
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ q - C (w : O)) (monic_X_pow_sub_C _ hpos.ne') b
    (by simpa using hb) (by
      rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul, eval_C, eval_pow, eval_X]
      exact hq.mul (hbu.pow (q - 1)))
  have hapow : a ^ q = w := by simpa [IsRoot, sub_eq_zero] using ha
  have hau : IsUnit a := (isUnit_pow_iff hpos.ne').1 (hapow ▸ w.isUnit)
  exact ⟨hau.unit, Units.ext (by simpa using hapow)⟩

end GlobalTheory.UnitPowerExistence
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem frobSubalgebra_counit : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ B : Subalgebra k A, (∀ a, a ∈ B ↔ ∃ c : A, c ^ p = a) ∧ ∃ Δ' : B →ₐ[k] B ⊗[k] B, ((∀ a : B, TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a) ∧ (∀ a : B, TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a)) := by
  intro p _ k A _ _ _ _ _ ε Δ ⟨hl, hr⟩
  have injA : Function.Injective (algebraMap k A) := fun x y h => by
    simpa using congrArg ε h
  haveI : CharP A p := charP_of_injective_algebraMap injA p
  let εε : A ⊗[k] A →ₐ[k] k := Algebra.TensorProduct.lift ε ε (fun _ _ => Commute.all _ _)
  have injAA : Function.Injective (algebraMap k (A ⊗[k] A)) := fun x y h => by
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using congrArg εε h
  haveI : CharP (A ⊗[k] A) p := charP_of_injective_algebraMap injAA p
  let B : Subalgebra k A :=
    { carrier := {a | ∃ c : A, c ^ p = a}
      mul_mem' := by rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c * d, mul_pow c d p⟩
      add_mem' := by rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c + d, add_pow_char c d p⟩
      algebraMap_mem' := by
        intro r
        obtain ⟨s, hs⟩ := surjective_frobenius k p r
        exact ⟨algebraMap k A s, by rw [← map_pow, ← hs, frobenius_def]⟩ }
  refine ⟨B, fun a => Iff.rfl, ?_⟩
  let j : B ⊗[k] B →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.map B.val B.val
  have hj : Function.Injective j :=
    TensorProduct.map_injective_of_flat_flat B.val.toLinearMap B.val.toLinearMap
      Subtype.val_injective Subtype.val_injective
  have hpow : ∀ t : A ⊗[k] A, t ^ p ∈ j.range := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [zero_pow (Fact.out : p.Prime).ne_zero]⟩
    | tmul a b =>
      exact ⟨(⟨a ^ p, a, rfl⟩ : B) ⊗ₜ (⟨b ^ p, b, rfl⟩ : B), by
        simp [j, Algebra.TensorProduct.tmul_pow]⟩
    | add x y hx hy => rw [add_pow_char]; exact add_mem hx hy
  have hΔ : ∀ b : B, Δ (B.val b) ∈ j.range := by
    rintro ⟨_, c, rfl⟩
    simpa [map_pow] using hpow (Δ c)
  let e := AlgEquiv.ofInjective j hj
  let Δ' : B →ₐ[k] B ⊗[k] B := e.symm.toAlgHom.comp ((Δ.comp B.val).codRestrict j.range hΔ)
  have hjΔ : ∀ b : B, j (Δ' b) = Δ (B.val b) := by
    intro b
    have h1 := e.apply_symm_apply ⟨Δ (B.val b), hΔ b⟩
    exact congrArg Subtype.val h1
  have kl : ∀ x : B ⊗[k] B, ((TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap x) : B) : A)
      = TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (j x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [j]
    | add x y hx hy => simp only [map_add (f := _), Subalgebra.coe_add, hx, hy]
  have kr : ∀ x : B ⊗[k] B, ((TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap x) : B) : A)
      = TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (j x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [j]
    | add x y hx hy => simp only [map_add (f := _), Subalgebra.coe_add, hx, hy]
  refine ⟨Δ', fun b => ?_, fun b => ?_⟩
  · apply Subtype.ext
    rw [kl, hjΔ]; exact hl _
  · apply Subtype.ext
    rw [kr, hjΔ]; exact hr _

end GlobalTheory
end

section

namespace GlobalTheory.PowerInRangeTensorRight

open TensorProduct

theorem exists_pow_pow_mem_range_includeRight (k K B : Type) [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B] (q : ℕ) [ExpChar k q]
    (z : TensorProduct k K B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      AlgHom.range (Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k K B) := by
  rcases subsingleton_or_nontrivial (TensorProduct k K B) with hs | hnt
  · exact ⟨0, by rw [Subsingleton.elim (z ^ q ^ 0) 0]; exact zero_mem _⟩
  have : ExpChar (TensorProduct k K B) q :=
    expChar_of_injective_algebraMap (algebraMap k (TensorProduct k K B)).injective q
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x b =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem k q x
    refine ⟨n, (AlgHom.mem_range _).mpr ⟨c • b ^ q ^ n, ?_⟩⟩
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_pow, ← hc,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨n1, h1⟩ := hx
    obtain ⟨n2, h2⟩ := hy
    refine ⟨n1 + n2, ?_⟩
    have e1 : x ^ q ^ (n1 + n2) = (x ^ q ^ n1) ^ q ^ n2 := by rw [pow_add, pow_mul]
    have e2 : y ^ q ^ (n1 + n2) = (y ^ q ^ n2) ^ q ^ n1 := by rw [pow_add, mul_comm, pow_mul]
    rw [add_pow_expChar_pow, e1, e2]
    exact add_mem (pow_mem h1 _) (pow_mem h2 _)

end GlobalTheory.PowerInRangeTensorRight
end

section

open Matrix

namespace GlobalTheory

theorem relIndex_iInf_fin_ne_zero {G : Type} [Group G] {m : ℕ} (K : Fin m → Subgroup G)
    (L : Subgroup G) (h : ∀ i, (K i).relIndex L ≠ 0) : (⨅ i, K i).relIndex L ≠ 0 := by
  have key : ∀ s : Finset (Fin m), (⨅ i ∈ s, K i).relIndex L ≠ 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iInf_insert]
      exact Subgroup.relIndex_inf_ne_zero (h a) ih
  simpa using key Finset.univ

theorem prod_pi_eq_inf_iInf {A : Type} [Group A] {m : ℕ} {B : Fin m → Type} [∀ i, Group (B i)]
    (H : Subgroup A) (K : ∀ i, Subgroup (B i)) :
    H.prod (Subgroup.pi Set.univ K) =
      H.comap (MonoidHom.fst A ((i : Fin m) → B i)) ⊓
        ⨅ i, (K i).comap ((Pi.evalMonoidHom B i).comp (MonoidHom.snd A ((i : Fin m) → B i))) := by
  ext x
  simp [Subgroup.mem_prod, Subgroup.mem_pi, Subgroup.mem_iInf]

theorem relIndex_prod_pi_ne_zero {A : Type} [Group A] {m : ℕ} {B : Fin m → Type}
    [∀ i, Group (B i)] (H H' : Subgroup A) (K K' : ∀ i, Subgroup (B i))
    (hH : H.relIndex H' ≠ 0) (hK : ∀ i, (K i).relIndex (K' i) ≠ 0) :
    (H.prod (Subgroup.pi Set.univ K)).relIndex (H'.prod (Subgroup.pi Set.univ K')) ≠ 0 := by
  rw [prod_pi_eq_inf_iInf H K]
  apply Subgroup.relIndex_inf_ne_zero
  · rw [Subgroup.relIndex_comap]
    refine mt (Subgroup.relIndex_eq_zero_of_le_right ?_) hH
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_prod.mp hx).1
  · apply relIndex_iInf_fin_ne_zero
    intro i
    rw [Subgroup.relIndex_comap]
    refine mt (Subgroup.relIndex_eq_zero_of_le_right ?_) (hK i)
    rintro _ ⟨x, hx, rfl⟩
    exact ((Subgroup.mem_pi Set.univ).mp (Subgroup.mem_prod.mp hx).2) i (Set.mem_univ i)

theorem map_conj_prod_pi {A : Type} [Group A] {m : ℕ} {B : Fin m → Type} [∀ i, Group (B i)]
    (H : Subgroup A) (K : ∀ i, Subgroup (B i)) (g : A × ((i : Fin m) → B i)) :
    (H.prod (Subgroup.pi Set.univ K)).map (MulAut.conj g).toMonoidHom =
      (H.map (MulAut.conj g.1).toMonoidHom).prod
        (Subgroup.pi Set.univ fun i => (K i).map (MulAut.conj (g.2 i)).toMonoidHom) := by
  ext x
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_prod, Subgroup.mem_pi, Set.mem_univ,
    true_implies, MulAut.conj_symm_apply, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv,
    Prod.snd_inv, Pi.mul_apply, Pi.inv_apply]

theorem commensurable_map_conj_prod_pi : ∀ {A : Type} [Group A] {m : ℕ} {B : Fin m → Type} [∀ i, Group (B i)] (H : Subgroup A) (K : ∀ i, Subgroup (B i)) (g : A × ((i : Fin m) → B i)), Subgroup.Commensurable (H.map (MulAut.conj g.1).toMonoidHom) H → (∀ i, Subgroup.Commensurable ((K i).map (MulAut.conj (g.2 i)).toMonoidHom) (K i)) → Subgroup.Commensurable ((H.prod (Subgroup.pi Set.univ K)).map (MulAut.conj g).toMonoidHom) (H.prod (Subgroup.pi Set.univ K)) := by
  intro A _ m B _ H K g hH hK
  rw [map_conj_prod_pi]
  exact ⟨⟨relIndex_prod_pi_ne_zero _ _ _ _ hH.1.relIndex_ne_zero
      fun i => (hK i).1.relIndex_ne_zero⟩,
    ⟨relIndex_prod_pi_ne_zero _ _ _ _ hH.2.relIndex_ne_zero
      fun i => (hK i).2.relIndex_ne_zero⟩⟩

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

section GLCong

variable {B : Type} [CommRing B] (R : Subring B) {n : ℕ}

theorem glcong_mem_range (A : GL (Fin n) B) (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) B) i j ∈ R)
    (hA' : ∀ i j, ((A⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R) :
    A ∈ (GeneralLinearGroup.map (n := Fin n) R.subtype).range := by
  let M : Matrix (Fin n) (Fin n) R := fun i j => ⟨_, hA i j⟩
  let N : Matrix (Fin n) (Fin n) R := fun i j => ⟨_, hA' i j⟩
  have hM : R.subtype.mapMatrix M = (A : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
  have hN : R.subtype.mapMatrix N = ((A⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
  have hinj : Function.Injective (R.subtype.mapMatrix : Matrix (Fin n) (Fin n) R →+* _) := by
    intro X Y h; ext i j; exact congrFun (congrFun h i) j
  have h1 : M * N = 1 := hinj (by rw [map_mul, map_one, hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h2 : N * M = 1 := hinj (by rw [map_mul, map_one, hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨M, N, h1, h2⟩, ?_⟩
  ext i j
  rfl

theorem glcong_entries (c : R) (h : GL (Fin n) R)
    (hh : GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (Ideal.span {c * c})) h = 1)
    (P Q : Matrix (Fin n) (Fin n) B) (hP : ∀ i j, (c : B) * P i j ∈ R) (hQ : ∀ i j, (c : B) * Q i j ∈ R)
    (hPQ : P * Q = 1) :
    ∀ i j, (P * R.subtype.mapMatrix (h : Matrix (Fin n) (Fin n) R) * Q) i j ∈ R := by
  have hX : ∀ i j, ∃ x : R, x * (c * c) = (h : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j := by
    intro i j
    rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq]
    have := congrArg (fun u : GL (Fin n) (R ⧸ Ideal.span {c * c}) => (u : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {c * c})) i j) hh
    simp only [GeneralLinearGroup.map_apply, Units.val_one] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  choose X hXe using hX
  let P' : Matrix (Fin n) (Fin n) R := fun i j => ⟨_, hP i j⟩
  let Q' : Matrix (Fin n) (Fin n) R := fun i j => ⟨_, hQ i j⟩
  let X' : Matrix (Fin n) (Fin n) R := fun i j => X i j
  have hP' : R.subtype.mapMatrix P' = (c : B) • P := by ext i j; rfl
  have hQ' : R.subtype.mapMatrix Q' = (c : B) • Q := by ext i j; rfl
  have hh' : (h : Matrix (Fin n) (Fin n) R) = 1 + (c * c) • X' := by
    refine Matrix.ext fun i j => ?_
    show _ = (1 : Matrix (Fin n) (Fin n) R) i j + (c * c) * X i j
    rw [mul_comm, hXe i j]; ring
  have key : P * R.subtype.mapMatrix (h : Matrix (Fin n) (Fin n) R) * Q
      = R.subtype.mapMatrix (1 + P' * X' * Q') := by
    have hs : R.subtype.mapMatrix ((c * c) • X') = ((c : B) * (c : B)) • R.subtype.mapMatrix X' := by
      ext i j
      change ((c * c * X i j : R) : B) = (c : B) * c * (X i j : B)
      push_cast; ring
    rw [map_add (f := _), map_one, map_mul, map_mul, hP', hQ', hh', map_add (f := _), map_one, hs]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPQ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  intro i j
  rw [key]
  exact ((1 + P' * X' * Q' : Matrix (Fin n) (Fin n) R) i j).2

theorem glcong_relIndex_ne_zero (c : R) (hfin : Finite (R ⧸ Ideal.span {c * c})) (g : GL (Fin n) B)
    (hg : ∀ i j, (c : B) * (g : Matrix (Fin n) (Fin n) B) i j ∈ R)
    (hg' : ∀ i j, (c : B) * ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R) :
    (((GeneralLinearGroup.map (n := Fin n) R.subtype).range).map (MulAut.conj g).toMonoidHom).relIndex
      (GeneralLinearGroup.map (n := Fin n) R.subtype).range ≠ 0 := by
  set φ := GeneralLinearGroup.map (n := Fin n) R.subtype
  set ψ := GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (Ideal.span {c * c}))
  have hΓ : ψ.ker.index ≠ 0 := by
    rw [Subgroup.index_ker]
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    ext i j
    exact congrArg (fun u : GL (Fin n) B => (u : Matrix (Fin n) (Fin n) B) i j) hab
  have h1 : (ψ.ker.map φ).relIndex φ.range ≠ 0 := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj,
      Subgroup.relIndex_top_right]
    exact hΓ
  have hval : ∀ h : GL (Fin n) R, ((φ h : GL (Fin n) B) : Matrix (Fin n) (Fin n) B)
      = R.subtype.mapMatrix (h : Matrix (Fin n) (Fin n) R) := fun h => rfl
  have hgg : ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) * (g : Matrix (Fin n) (Fin n) B) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : ψ.ker.map φ ≤ φ.range.map (MulAut.conj g).toMonoidHom := by
    rintro x ⟨h, hh, rfl⟩
    replace hh : ψ h = 1 := hh
    have hh' : ψ h⁻¹ = 1 := by rw [map_inv, hh, inv_one]
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ * φ h * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    apply glcong_mem_range
    · intro i j
      have := glcong_entries R c h hh _ _ hg' hg hgg i j
      rwa [Units.val_mul, Units.val_mul, hval]
    · intro i j
      have := glcong_entries R c h⁻¹ hh' _ _ hg' hg hgg i j
      rwa [show (g⁻¹ * φ h * g)⁻¹ = g⁻¹ * φ h⁻¹ * g by rw [map_inv]; group, Units.val_mul, Units.val_mul, hval]
  exact fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_left h2 h0)

end GLCong

theorem commensurable_conj_range_GL_subring {B : Type} [CommRing B] (R : Subring B) (n : ℕ) (c : R)
    (hfin : Finite (R ⧸ Ideal.span {c * c})) (g : GL (Fin n) B)
    (hg : ∀ i j, (c : B) * (g : Matrix (Fin n) (Fin n) B) i j ∈ R)
    (hg' : ∀ i j, (c : B) * ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R) :
    Subgroup.Commensurable ((GeneralLinearGroup.map R.subtype).range.map (MulAut.conj g).toMonoidHom)
      (GeneralLinearGroup.map R.subtype).range := by
  set K := (GeneralLinearGroup.map (n := Fin n) R.subtype).range
  refine ⟨⟨glcong_relIndex_ne_zero R c hfin g hg hg'⟩, ?_⟩
  rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
  have e := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (K.map (MulAut.conj g⁻¹).toMonoidHom) K (MulEquiv.injective _)
  have hK : (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id K]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hK] at e
  rw [e]
  exact glcong_relIndex_ne_zero R c hfin g⁻¹ hg' (by simpa using hg)

end GlobalTheory
end

section

namespace GlobalTheory

theorem doubleCoset_semidirect_surj :
    ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P),
      (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) →
      ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N),
        (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) →
        ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM →
          (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) →
          (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) →
          ∀ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P), ∃ X : N,
            DoubleCoset.mk TP KP (s (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) * u X)
              = d := by
  intro P M N _ _ _ s π u hs _ hker KP KM L hKs _ _ TM CM TP CP _ hTP _ _ d
  obtain ⟨t, ht, k, hk, hm⟩ := (@DoubleCoset.eq _ _ TM KM
    (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) (π (Quotient.out d))).1
    (DoubleCoset.out_eq' _)
  generalize Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d))) = q at hm ⊢
  obtain ⟨X, hX⟩ := (hker ((s q)⁻¹ * (s t)⁻¹ * Quotient.out d * (s k)⁻¹)).1 (by
    simp only [map_mul, map_inv, hs]
    rw [hm]; group)
  refine ⟨X, ?_⟩
  rw [hX]
  conv_rhs => rw [← DoubleCoset.out_eq' d]
  rw [DoubleCoset.eq]
  exact ⟨s t, (hTP _).2 ⟨t, ht, rfl⟩, s k, hKs k hk, by group⟩

end GlobalTheory
end

section

namespace GlobalTheory

theorem orbit_count_parabolic_unfold : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), Nat.card {x : N ⧸ L // DoubleCoset.mk TP KP (s q * u (Quotient.out x)) = DoubleCoset.mk TP KP (s q * u X)} = (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by
  intro P M N _ _ _ s π u hπs hu hker KP KM L hsK hπK huK TM CM TP CP _ hTP _ _ q X
  set S : Subgroup M := TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM with hS
  set C : Subgroup M := KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s) with hC
  letI : MulAction M (P ⧸ KP) := MulAction.compHom (P ⧸ KP) s
  have hsmul : ∀ (r : M) (p : P), r • (QuotientGroup.mk p : P ⧸ KP) = QuotientGroup.mk (s r * p) := by
    intro r p; rfl
  have memS : ∀ r : M, r ∈ S ↔ (∃ t ∈ TM, q⁻¹ * t * q = r) ∧ r ∈ KM := by
    intro r
    simp only [hS, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hπu : ∀ Y, π (u Y) = 1 := fun Y => (hker _).2 ⟨Y, rfl⟩
  set x0 : P ⧸ KP := QuotientGroup.mk (u X) with hx0
  have key : ∀ Y : N, DoubleCoset.mk TP KP (s q * u Y) = DoubleCoset.mk TP KP (s q * u X) ↔
      (QuotientGroup.mk (u Y) : P ⧸ KP) ∈ MulAction.orbit S x0 := by
    intro Y
    rw [eq_comm, DoubleCoset.eq]
    constructor
    · rintro ⟨h, hh, k, hk, e⟩
      obtain ⟨t, ht, rfl⟩ := (hTP h).1 hh
      have e2 : u Y = s (q⁻¹ * t * q) * u X * k := by
        apply mul_left_cancel (a := s q)
        rw [e, map_mul, map_mul, map_inv]
        group
      have e3 := congrArg π e2
      simp only [map_mul, hπs, hπu, mul_one] at e3
      have e4 : q⁻¹ * t * q = (π k)⁻¹ := eq_inv_of_mul_eq_one_left e3.symm
      have hr : q⁻¹ * t * q ∈ S := (memS _).2 ⟨⟨t, ht, rfl⟩, e4 ▸ KM.inv_mem (hπK k hk)⟩
      refine ⟨⟨_, hr⟩, ?_⟩
      show (q⁻¹ * t * q) • x0 = _
      rw [hx0, hsmul, QuotientGroup.eq, e2]
      convert hk using 1
      group
    · rintro ⟨⟨r, hr⟩, e⟩
      change r • x0 = _ at e
      rw [hx0, hsmul, QuotientGroup.eq] at e
      obtain ⟨⟨t, ht, rfl⟩, -⟩ := (memS r).1 hr
      refine ⟨s t, (hTP _).2 ⟨t, ht, rfl⟩, _, e, ?_⟩
      simp only [map_mul, map_inv]
      group
  have hinj : ∀ x y : N ⧸ L, (QuotientGroup.mk (u (Quotient.out x)) : P ⧸ KP) = QuotientGroup.mk (u (Quotient.out y)) → x = y := by
    intro x y h
    rw [QuotientGroup.eq, ← map_inv, ← map_mul, huK] at h
    rw [← Quotient.out_eq' x, ← Quotient.out_eq' y]
    exact (QuotientGroup.eq (s := L)).2 h
  have hcard : Nat.card {x : N ⧸ L // DoubleCoset.mk TP KP (s q * u (Quotient.out x)) = DoubleCoset.mk TP KP (s q * u X)} = Nat.card (MulAction.orbit S x0) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨QuotientGroup.mk (u (Quotient.out x.1)), (key _).1 x.2⟩) ⟨?_, ?_⟩)
    · intro x y h
      exact Subtype.ext (hinj _ _ (congrArg Subtype.val h))
    · rintro ⟨y, ⟨⟨r, hr⟩, rfl⟩⟩
      have hk : π (s r * u X * (s r)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, hπs, hπu]; group
      obtain ⟨Z, hZ⟩ := (hker _).1 hk
      have hrK : (r : M) ∈ KM := ((memS r).1 hr).2
      have hyo : (QuotientGroup.mk (u (Quotient.out (QuotientGroup.mk Z : N ⧸ L))) : P ⧸ KP) = r • x0 := by
        obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L Z
        change _ = r • x0
        rw [hx0, hsmul, hl, QuotientGroup.eq, map_mul, hZ]
        have h1 : s (r : M) ∈ KP := hsK _ hrK
        have h2 : u (l : N) ∈ KP := (huK _).2 l.2
        convert KP.mul_mem (KP.inv_mem h2) h1 using 1
        group
      refine ⟨⟨QuotientGroup.mk Z, (key _).2 ?_⟩, ?_⟩
      · rw [hyo]; exact ⟨⟨r, hr⟩, rfl⟩
      · exact Subtype.ext hyo
  have hstab : MulAction.stabilizer S x0 = (S ⊓ C).subgroupOf S := by
    ext ⟨r, hr⟩
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hC, Subgroup.mem_comap]
    change (r • x0 = x0) ↔ _
    rw [hx0, hsmul, QuotientGroup.eq]
    simp only [hr, true_and, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply, inv_inv]
    rw [← KP.inv_mem_iff]
    constructor <;> intro h <;> convert h using 1 <;> group
  rw [hcard, Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, Nat.card_coe_set_eq]

end GlobalTheory
end
