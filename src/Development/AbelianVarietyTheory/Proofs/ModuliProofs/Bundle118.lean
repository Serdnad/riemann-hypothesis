module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.TensorProduct.Nontrivial
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.TUniq

namespace GlobalTheory.TUniq

private theorem exists_algClosed_compositum {k K K₀ : Type} [Field k] [Field K] [Field K₀]
    (φ : k →+* K) (ψ : k →+* K₀) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (j : K₀ →+* Ω),
      i.comp φ = j.comp ψ := by
  letI : Algebra k K := φ.toAlgebra
  letI : Algebra k K₀ := ψ.toAlgebra
  haveI : Nontrivial (K ⊗[k] K₀) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k K K₀
      φ.injective ψ.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[k] K₀)
  letI : Field (K ⊗[k] K₀ ⧸ m) := Ideal.Quotient.field m
  let emb : K ⊗[k] K₀ →+* AlgebraicClosure (K ⊗[k] K₀ ⧸ m) :=
    (algebraMap (K ⊗[k] K₀ ⧸ m) (AlgebraicClosure (K ⊗[k] K₀ ⧸ m))).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure (K ⊗[k] K₀ ⧸ m), inferInstance, inferInstance,
    emb.comp Algebra.TensorProduct.includeLeftRingHom,
    emb.comp (Algebra.TensorProduct.includeRight : K₀ →ₐ[k] K ⊗[k] K₀).toRingHom, ?_⟩
  ext a
  simp only [RingHom.comp_apply]
  congr 1
  show (algebraMap k K a) ⊗ₜ[k] (1 : K₀) = (1 : K) ⊗ₜ[k] (algebraMap k K₀ a)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

private theorem pt_eq_lemma_2 {K : Type} [Field K] (q r : PrimeSpectrum K) : q = r :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime q.asIdeal).trans (Ideal.eq_bot_of_prime r.asIdeal).symm)

theorem exists_algClosed_join_of_mem_range {S : Scheme.{0}} {K K₀ : Type} [Field K] [Field K₀]
    (x : Sp K ⟶ S) (x₀ : Sp K₀ ⟶ S) (p : Sp K) (p₀ : Sp K₀) (h : x p = x₀ p₀) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (j : K₀ →+* Ω),
      spMap i ≫ x = spMap j ≫ x₀ := by
  have e : p = IsLocalRing.closedPoint K := pt_eq_lemma_2 _ _
  have e₀ : p₀ = IsLocalRing.closedPoint K₀ := pt_eq_lemma_2 _ _
  subst e e₀
  have hx := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S x
  have hx₀ := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K₀ S x₀
  generalize S.descResidueField (Scheme.stalkClosedPointTo x) = φ at hx
  generalize S.descResidueField (Scheme.stalkClosedPointTo x₀) = φ₀ at hx₀
  obtain ⟨Ω, hΩ, hΩc, i, j, hij⟩ := exists_algClosed_compositum φ.hom ((S.residueFieldCongr h).hom ≫ φ₀).hom
  refine ⟨Ω, hΩ, hΩc, i, j, ?_⟩
  have hx₀' : Spec.map ((S.residueFieldCongr h).hom ≫ φ₀) ≫
      S.fromSpecResidueField (x (IsLocalRing.closedPoint K)) = x₀ := by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField, hx₀]
  have hc : φ ≫ CommRingCat.ofHom i = ((S.residueFieldCongr h).hom ≫ φ₀) ≫ CommRingCat.ofHom j := by
    ext a
    exact RingHom.congr_fun hij a
  show Spec.map (CommRingCat.ofHom i) ≫ x = Spec.map (CommRingCat.ofHom j) ≫ x₀
  conv_lhs => rw [← hx]
  conv_rhs => rw [← hx₀']
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hc]

theorem geoGood_commonFibres : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (t t' : TObj g k J b s), GeoGood t t' {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (u : TObj g k J b (x ≫ s)), p ∈ Set.range x ∧ TMap u t x ∧ TMap u t' x} := by
  intro o _ g k J b S s t t' K _ x hx
  obtain ⟨K₁, hK₁, x₁, u₁, ⟨p₁, hp₁⟩, hu, hu'⟩ := hx ⟨IsLocalRing.closedPoint K, rfl⟩
  obtain ⟨Ω, hΩ, hΩc, i, j, hij⟩ :=
    exists_algClosed_join_of_mem_range x x₁ (IsLocalRing.closedPoint K) p₁ hp₁.symm
  obtain ⟨u, hu₀⟩ := GlobalTheory.tObj_pull o g k J b (Sp K₁) (Sp Ω) (x₁ ≫ s) (spMap i ≫ x ≫ s) (spMap j) u₁
    (by rw [← Category.assoc, ← hij, Category.assoc])
  have hT := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b S (Sp K₁) (Sp Ω) s (x₁ ≫ s) (spMap i ≫ x ≫ s) t u₁ u).2
    x₁ (spMap j) hu).1 hu₀
  have hT' := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b S (Sp K₁) (Sp Ω) s (x₁ ≫ s) (spMap i ≫ x ≫ s) t' u₁ u).2
    x₁ (spMap j) hu').1 hu₀
  rw [← hij] at hT hT'
  obtain ⟨ψ, hψ⟩ := (tMap_iff u t _).1 hT
  obtain ⟨ψ', hψ'⟩ := (tMap_iff u t' _).1 hT'
  exact ⟨Ω, hΩ, hΩc, i, spMap i ≫ x ≫ s, u, ψ, ψ', hψ, hψ'⟩

end GlobalTheory.TUniq
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PowerAdjoint

open GlobalTheory.CechPic

section Algebra

variable {M : Type} {V : Type 1} [AddCommGroup M] [AddCommGroup V] {n : Type} [Fintype n]

def form (B : M →+ M →+ V) (W : Matrix n n ℤ) (x y : n → M) : V := ∑ u, ∑ v, W u v • B (x u) (y v)

theorem form_left (B : M →+ M →+ V) (W m : Matrix n n ℤ) (x y : n → M) :
    form B W (fun u => ∑ v, m u v • x v) y = form B (m.transpose * W) x y := by
  have hL : form B W (fun u => ∑ v, m u v • x v) y = ∑ u, ∑ v, ∑ w, (W u v * m u w) • B (x w) (y v) := by

    simp [form, Finset.smul_sum, smul_smul, map_sum]
  have hR : form B (m.transpose * W) x y = ∑ w, ∑ v, ∑ u, (m u w * W u v) • B (x w) (y v) := by
    simp [form, Matrix.mul_apply, Finset.sum_smul]
  rw [hL, hR]
  calc ∑ u, ∑ v, ∑ w, (W u v * m u w) • B (x w) (y v)
      = ∑ u, ∑ w, ∑ v, (W u v * m u w) • B (x w) (y v) := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ w, ∑ u, ∑ v, (W u v * m u w) • B (x w) (y v) := Finset.sum_comm
    _ = ∑ w, ∑ v, ∑ u, (m u w * W u v) • B (x w) (y v) := Finset.sum_congr rfl fun _ _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem form_right (B : M →+ M →+ V) (W m : Matrix n n ℤ) (x y : n → M) :
    form B W x (fun u => ∑ v, m u v • y v) = form B (W * m) x y := by
  have hL : form B W x (fun u => ∑ v, m u v • y v) = ∑ u, ∑ v, ∑ w, (W u v * m v w) • B (x u) (y w) := by

    simp [form, Finset.smul_sum, smul_smul, map_sum]
  have hR : form B (W * m) x y = ∑ u, ∑ w, ∑ v, (W u v * m v w) • B (x u) (y w) := by
    simp [form, Matrix.mul_apply, Finset.sum_smul]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem form_polar (B : M →+ M →+ V) (hB : ∀ a b, B a b = B b a) (W : Matrix n n ℤ) (x y : n → M) :
    form B W (x + y) (x + y) - form B W x x - form B W y y + form B W 0 0 = form B (W + W.transpose) x y := by
  have hyx : ∑ u, ∑ v, W u v • B (y u) (x v) = ∑ u, ∑ v, W v u • B (x u) (y v) := by
    rw [Finset.sum_comm]
    simp only [hB (y _) (x _)]
  simp only [form, Pi.add_apply, Pi.zero_apply, map_add (f := _), map_zero, AddMonoidHom.add_apply,
    smul_add, smul_zero, Finset.sum_add_distrib, Finset.sum_const_zero, Matrix.add_apply, Matrix.transpose_apply, add_smul]
  rw [hyx]
  abel

end Algebra

section Square

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]


omit [IsCommMonObj B] in
theorem exists_biadditive {P : LB (G2 B).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd B B) (fst B B)).left))
    (T : Over S) (hb : ∀ x x' y : T ⟶ B, ∃ t : LB.Gen (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen) :
    ∃ β : Additive (T ⟶ B) →+ Additive (T ⟶ B) →+ Pic T.left, (∀ a b, β a b = β b a) ∧
      ∀ x y : T ⟶ B, β (.ofMul x) (.ofMul y) = pull (lift x y).left (cls P hP) := by
  have add1 : ∀ x x' y : T ⟶ B, pull (lift (x * x') y).left (cls P hP) =
      pull (lift x y).left (cls P hP) + pull (lift x' y).left (cls P hP) := by
    intro x x' y
    have h0 := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hb x x' y)
    rw [cls_linComb hP] at h0
    simp [Fin.sum_univ_three] at h0
    rw [← sub_eq_zero, ← h0]
    abel
  have e1 : cls P hP = pull (lift (snd B B) (fst B B)).left (cls P hP) := by
    rw [← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_iff hP _).2 hs
  have hsym : ∀ x y : T ⟶ B, pull (lift y x).left (cls P hP) = pull (lift x y).left (cls P hP) := by
    intro x y
    have e2 : (lift y x).left ≫ (lift (snd B B) (fst B B)).left = (lift x y).left := by
      rw [← Over.comp_left]
      congr 1
      ext <;> simp
    calc pull (lift y x).left (cls P hP)
        = pull (lift y x).left (pull (lift (snd B B) (fst B B)).left (cls P hP)) := by rw [← e1]
      _ = pull (lift x y).left (cls P hP) := by rw [← pull_comp, e2]
  have add2 : ∀ x y y' : T ⟶ B, pull (lift x (y * y')).left (cls P hP) =
      pull (lift x y).left (cls P hP) + pull (lift x y').left (cls P hP) := by
    intro x y y'
    rw [hsym (y * y') x, add1, ← hsym y x, ← hsym y' x]
  refine ⟨AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => pull (lift a.toMul b.toMul).left (cls P hP))
    fun b b' => ?_) fun a a' => ?_, fun a b => ?_, fun x y => rfl⟩
  · rw [toMul_add]
    exact add2 _ _ _
  · ext b
    simp only [toMul_add]
    exact add1 _ _ _
  · exact (hsym a.toMul b.toMul).symm

theorem comp_prod_zpow {T T' : Over S} (ρ : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ B)) (k : Fin n → ℤ) :
    ρ ≫ (List.ofFn fun v => x v ^ k v).prod = (List.ofFn fun v => (ρ ≫ x v) ^ k v).prod := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => simp [List.ofFn_succ, MonObj.comp_mul, GrpObj.comp_zpow, ih]

theorem ofMul_comp_matrix {Q T : Over S} {n : ℕ} (pr : Fin n → (Q ⟶ B)) (m : Matrix (Fin n) (Fin n) ℤ) (α : Q ⟶ Q)
    (hα : ∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) (x : T ⟶ Q) :
    (fun u => Additive.ofMul ((x ≫ α) ≫ pr u)) = fun u => ∑ v, m u v • Additive.ofMul (x ≫ pr v) := by
  funext u
  rw [Category.assoc, hα u, comp_prod_zpow]
  simp [ofMul_list_prod, List.sum_ofFn, ofMul_zpow]

theorem exists_form {P : LB (G2 B).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd B B) (fst B B)).left))
    (T : Over S) (hb : ∀ x x' y : T ⟶ B, ∃ t : LB.Gen (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen)
    {Q : Over S} [GrpObj Q] [IsCommMonObj Q] {n : Type} [Fintype n] (pr : n → (Q ⟶ B)) (hpr : ∀ u, IsMonHom (pr u))
    {L : LB Q.left} (hL : L.IsLB) (W : Matrix n n ℤ)
    (hW : LBIso L (LB.LinComb P (K := n × n) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2))) :
    ∃ β : Additive (T ⟶ B) →+ Additive (T ⟶ B) →+ Pic T.left,
      (∀ x : T ⟶ Q, pull x.left (cls L hL) =
        form β W (fun u => .ofMul (x ≫ pr u)) (fun u => .ofMul (x ≫ pr u))) ∧
      ∀ (x y : T ⟶ Q) hh, cls (cubeLB Q ![x, y] L) hh =
        form β (W + W.transpose) (fun u => .ofMul (x ≫ pr u)) (fun u => .ofMul (y ≫ pr u)) := by
  obtain ⟨β, hβs, hβ⟩ := exists_biadditive hP hs T hb
  have hpt : ∀ x : T ⟶ Q, pull x.left (cls L hL) =
      form β W (fun u => .ofMul (x ≫ pr u)) (fun u => .ofMul (x ≫ pr u)) := by
    intro x

    rw [(cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hW, cls_linComb hP, map_sum, Fintype.sum_prod_type]
    simp only [form]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hβ]
  refine ⟨β, hpt, fun x y hh => ?_⟩
  have hxy : (fun u => Additive.ofMul ((x * y) ≫ pr u)) =
      (fun u => Additive.ofMul (x ≫ pr u)) + fun u => Additive.ofMul (y ≫ pr u) := by
    funext u
    have := hpr u
    simp [MonObj.mul_comp]
  have h1 : (fun u => Additive.ofMul ((1 : T ⟶ Q) ≫ pr u)) = 0 := by
    funext u
    have := hpr u
    simp [MonObj.one_comp]
  rw [cls_cube_two hL x y hh, lam, hpt, hpt, hpt, hpt, hxy, h1]
  exact form_polar β hβs W _ _

theorem primitive_adjoint {P : LB (G2 B).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd B B) (fst B B)).left))
    (hb : ∀ (T : Over S) (x x' y : T ⟶ B), ∃ t : LB.Gen (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen)
    {Q : Over S} [GrpObj Q] [IsCommMonObj Q] {n : ℕ} (pr : Fin n → (Q ⟶ B)) (hpr : ∀ u, IsMonHom (pr u))
    {L : LB Q.left} (hL : L.IsLB) (W : Matrix (Fin n) (Fin n) ℤ)
    (hW : LBIso L (LB.LinComb P (K := Fin n × Fin n) (fun uv => (lift (pr uv.1) (pr uv.2)).left)
      (fun uv => W uv.1 uv.2)))
    (m : Matrix (Fin n) (Fin n) ℤ) (α : Q ⟶ Q) (hα : ∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) :
    ((W + W.transpose) * m = W → LBIso L (cubeLB Q ![𝟙 Q, α] L)) ∧
      ∀ (m' : Matrix (Fin n) (Fin n) ℤ) (α' : Q ⟶ Q), (∀ u, α' ≫ pr u = (List.ofFn fun v => pr v ^ m' u v).prod) →
        m.transpose * (W + W.transpose) = (W + W.transpose) * m' →
        LBIso (cubeLB Q ![fst Q Q ≫ α, snd Q Q] L) (cubeLB Q ![fst Q Q, snd Q Q ≫ α'] L) := by
  refine ⟨fun hm => ?_, fun m' α' hα' hm' => ?_⟩
  · obtain ⟨β, hpt, hcube⟩ := exists_form hP hs Q (hb Q) pr hpr hL W hW
    have hc : (cubeLB Q ![𝟙 Q, α] L).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff hL hc).1 ?_
    have e0 := hpt (𝟙 Q)
    rw [Over.id_left, pull_id] at e0
    have hY := ofMul_comp_matrix pr m α hα (𝟙 Q)
    have hR := form_right β (W + W.transpose) m (fun u => Additive.ofMul (pr u)) (fun u => Additive.ofMul (pr u))
    simp only [Category.id_comp] at e0 hY
    rw [e0, hcube (𝟙 Q) α hc]
    simp only [Category.id_comp]
    rw [hY, hR, hm]
  · obtain ⟨β, -, hcube⟩ := exists_form hP hs (Q ⊗ Q) (hb (Q ⊗ Q)) pr hpr hL W hW
    have h1 : (cubeLB Q ![fst Q Q ≫ α, snd Q Q] L).IsLB := LB.isLB_linComb hL _ _
    have h2 : (cubeLB Q ![fst Q Q, snd Q Q ≫ α'] L).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff h1 h2).1 ?_
    have hl := form_left β (W + W.transpose) m (fun u => Additive.ofMul (fst Q Q ≫ pr u))
      (fun u => Additive.ofMul (snd Q Q ≫ pr u))
    have hr := form_right β (W + W.transpose) m' (fun u => Additive.ofMul (fst Q Q ≫ pr u))
      (fun u => Additive.ofMul (snd Q Q ≫ pr u))
    rw [hcube _ _ h1, hcube _ _ h2, ofMul_comp_matrix pr m α hα (fst Q Q), ofMul_comp_matrix pr m' α' hα' (snd Q Q), hl, hr, hm']

end Square

theorem matrix_primitive_adjoint : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (K : Type) [Field K] (o : Type) [CommRing o] (s : Sp K ⟶ Sp o) (h k : ℕ) (ζ : o) (c : SiegPre h k ζ s) (P : Out.PolAV (Sp K)) (pr : Fin 8 → (P.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ P.A, ∀ u, x ≫ pr u = y u) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → ∀ (m : Matrix (Fin 8) (Fin 8) ℤ) (α : P.A ⟶ P.A), (∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → ((W + W.transpose) * m = W → LBIso P.L (cubeLB P.A ![𝟙 P.A, α] P.L)) ∧ ∀ (m' : Matrix (Fin 8) (Fin 8) ℤ) (α' : P.A ⟶ P.A), (∀ u, α' ≫ pr u = (List.ofFn fun v => pr v ^ m' u v).prod) → m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB P.A ![fst P.A P.A ≫ α, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ α'] P.L) := by
  intro hΘ W K _ o _ s h k ζ c P pr hpr huniv hW m α hα
  have : IsCommMonObj P.A := P.isAb.comm
  exact primitive_adjoint c.isLB c.symm
    (fun T x x' y => siegPre_bundle_mul_left hΘ K o s h k ζ c P pr hpr huniv T x x' y) pr hpr P.isLB W hW m α hα

end GlobalTheory.PowerAdjoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelOfTheta

open GlobalTheory.CechPic

section Algebra

variable {G U : Type} [CommGroup G] [CommGroup U]

end Algebra

section Classes

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

theorem pull_one (hL : L.IsLB) (hr : Out.Rigidified A L) (T : Over S) :
    pull (1 : T ⟶ A).left (cls L hL) = 0 := by
  have e : pull (eSec A) (cls L hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 hr
  have e' : (1 : T ⟶ A).left = (toUnit T).left ≫ eSec A := rfl
  rw [e', pull_comp, e, map_zero]

omit [GrpObj A] in
theorem pull_pull {T T' : Over S} (f : T' ⟶ T) (a : T ⟶ A) (c : Pic A.left) :
    pull f.left (pull a.left c) = pull (f ≫ a).left c := (pull_comp _ _ _).symm

variable [IsCommMonObj A]

theorem isLB_lam (hL : L.IsLB) : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _

theorem cls_lam (hL : L.IsLB) :
    cls _ (isLB_lam hL) = pull (fst A A * snd A A).left (cls L hL) - pull (fst A A).left (cls L hL) -
      pull (snd A A).left (cls L hL) + pull (1 : A ⊗ A ⟶ A).left (cls L hL) := by
  refine (cls_linComb hL _ _ (isLB_lam hL)).trans ?_
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum A (x2 A) I).left (cls L hL)) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have p₀ : psum A (x2 A) ∅ = 1 := rfl
  have p₁ : psum A (x2 A) {0} = fst A A := _root_.mul_one (fst A A)
  have p₂ : psum A (x2 A) {1} = snd A A := _root_.mul_one (snd A A)
  have p₃ : psum A (x2 A) {0, 1} = fst A A * snd A A := congrArg (fst A A * ·) (_root_.mul_one (snd A A))
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [neg_smul, one_smul]
  abel

theorem pull_lam (hL : L.IsLB) (hr : Out.Rigidified A L) {T : Over S} (a b : T ⟶ A) :
    pull (lift a b).left (cls _ (isLB_lam hL)) =
      pull (a * b).left (cls L hL) - pull a.left (cls L hL) - pull b.left (cls L hL) := by
  rw [cls_lam hL, pull_one hL hr, add_zero, map_sub, map_sub, pull_pull, pull_pull, pull_pull, MonObj.comp_mul,
    lift_fst, lift_snd]

end Classes

section Pairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L M : LB A.left}

theorem exists_theta_iff (hL : L.IsLB) (k : ℤ) {T : Over S} (x : T ⟶ A) :
    (∃ θ : Out.ThetaGrp A L k T, θ.pt = x) ↔
      k • pull (snd T A).left (cls L hL) - k • pull (Out.translPt A x).left (cls L hL) = 0 := by
  have e := cls_linComb hL (K := Fin 2) ![(snd T A).left, (Out.translPt A x).left] ![k, -k] (LB.isLB_linComb hL _ _)
  rw [Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, ← sub_eq_add_neg] at e
  rw [← e, cls_eq_zero_iff]
  exact ⟨fun ⟨θ, h⟩ => h ▸ ⟨θ.φ, θ.isGen⟩, fun ⟨t, ht⟩ => ⟨⟨x, t, ht⟩, rfl⟩⟩

theorem weilIs_of_pow (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (hM : M.IsLB) (d : ℕ)
    (e : cls M hM = d • cls L hL) {k : ℤ} {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A L k x y c) : Out.WeilIs A M k x y (c ^ d) := by
  have up : ∀ (T' : Over S) (u : T' ⟶ A), (∃ θ : Out.ThetaGrp A L k T', θ.pt = u) →
      ∃ θ : Out.ThetaGrp A M k T', θ.pt = u := fun T' u H => by
    rw [exists_theta_iff hL] at H
    rw [exists_theta_iff hM, e, map_nsmul, map_nsmul, smul_comm k d, smul_comm k d, ← smul_sub, H, smul_zero]
  obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs (k := k) (x := x) (y := y) hG hA hM
    (fun p => by
      obtain ⟨V, hV, ⟨θ, -, H, -⟩, -⟩ := h p
      exact ⟨V, hV, up _ _ ⟨θ, H⟩⟩)
    (fun p => by
      obtain ⟨V, hV, ⟨-, θ, -, H⟩, -⟩ := h p
      exact ⟨V, hV, up _ _ ⟨θ, H⟩⟩)
  have iso : LBIso (lbPow L d) (M.pull (𝟙 A : A ⟶ A).left) :=
    (cls_eq_iff (isLB_lbPow hL d) (pull_isLB hM _)).1 (by
      rw [cls_lbPow hL, cls_pull hM, Over.id_left, pull_id, e])
  have := (weilIs_along_hom hG S A A (𝟙 A) L M d k T x y c c' hA hA hL hM inferInstance iso
    (by simpa using hc')).2 h
  exact this ▸ hc'

end Pairing

section Principal

variable {S : Scheme.{0}}

theorem cls_diag (hG : Out.GlobalFnsSt)
    (hc : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    (P : Out.PolAV S) [IsCommMonObj P.A] :
    cls _ (pull_isLB (isLB_lam P.isLB) (lift (𝟙 P.A) (𝟙 P.A)).left) = 2 • cls P.L P.isLB := by
  have h := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2
    ((MulPull.mulPull_of_cube_of_symm hc (exists_gen_negLB hG)).1 S P 2)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id] at h
  have e : Out.mulA P.A 2 = 𝟙 P.A * 𝟙 P.A := pow_two _
  rw [e] at h
  rw [cls_pull (isLB_lam P.isLB), pull_lam P.isLB P.rigid, Over.id_left, pull_id]
  rw [← sub_eq_zero, ← neg_eq_zero, ← h]
  push_cast
  module

theorem relAmple_of_pow {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) (h : Out.RelAmple A L) : Out.RelAmple A M := by
  have := hA.proper
  rw [relAmple_iff_isAmpleLB A hL] at h
  refine relAmple_of_isAmpleLB A hM fun U hU => ?_
  refine (isAmpleLB_congr (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _) ((cls_eq_iff (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)).1 ?_)).1
    ((isAmpleLB_pow_iff (pull_isLB hL _) hd).2 (h U hU))
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

end Principal

section Level

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

end Level

end GlobalTheory.SiegelOfTheta
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isProjOver_comp_of_finite :
    ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Sp R), IsFinite f → IsProjOver s → IsProjOver (f ≫ s) := by
  intro R _ X Y f s hf hs
  exact GlobalTheory.isProjOver_comp_of_isFinite f hs

end GlobalTheory
end
