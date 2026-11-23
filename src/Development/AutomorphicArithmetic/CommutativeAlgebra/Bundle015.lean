module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MapZeroS
public import Development.EtaleCohomology.EtaleSheaves.Bundle012
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle064
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.EtaleCohomology.EtaleSheaves.Bundle009
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.TypeStar
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.tensor_fractionRing_exists_mul_eq_of_denominator :
    ∀ (k L K : Type) [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] (B : Subalgebra k K), IsFractionRing B K → ∀ t : L ⊗[k] K, ∃ (s : L ⊗[k] B) (β : B), β ≠ 0 ∧ t * ((1 : L) ⊗ₜ[k] (β : K)) = inc L B s := by
  intro k L K _ _ _ _ _ B hB t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul l κ =>
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) κ
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (b : K) ≠ 0 := fun h0 => hb0 (Subtype.ext h0)
    refine ⟨l ⊗ₜ[k] a, b, hb0, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp only [inc, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
    congr 1
    rw [← hab]
    change (a : K) / (b : K) * b = a
    field_simp
  | add x y hx hy =>
    obtain ⟨s1, β1, h1, e1⟩ := hx
    obtain ⟨s2, β2, h2, e2⟩ := hy
    refine ⟨s1 * ((1 : L) ⊗ₜ[k] β2) + s2 * ((1 : L) ⊗ₜ[k] β1), β1 * β2, mul_ne_zero h1 h2, ?_⟩
    have i1 : inc L B ((1 : L) ⊗ₜ[k] β2) = (1 : L) ⊗ₜ[k] (β2 : K) := by simp [inc]
    have i2 : inc L B ((1 : L) ⊗ₜ[k] β1) = (1 : L) ⊗ₜ[k] (β1 : K) := by simp [inc]
    have split : (1 : L) ⊗ₜ[k] ((β1 * β2 : B) : K) =
        ((1 : L) ⊗ₜ[k] (β1 : K)) * ((1 : L) ⊗ₜ[k] (β2 : K)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Subalgebra.coe_mul]
    rw [map_add (f := _), map_mul, map_mul, i1, i2, ← e1, ← e2, split]
    ring
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

private theorem map_units {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (ε : ℤˣ) (x : Sec F U) :
    Sec.map φ (ε • x) = ε • Sec.map φ x := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

private theorem map_add' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y :=
  map_add _ _ _

private theorem mul_mid {R : Type} [CommRing R] {I Q P : Cx R} (μ : Pair Q P I) (U : Scheme.{0}) (k m m' w : ℤ) (e : m = m')
    (h : m + 1 = w) (h' : m' + 1 = w) (A : Sec (Q.X k) U) (B : Sec (P.X 1) U) :
    μ.mul U m 1 w h (Sec.map (Q.d k m) A) B = μ.mul U m' 1 w h' (Sec.map (Q.d k m') A) B := by
  subst e
  rfl

theorem UpperTheory.psi_comm_differential_of_cocycle :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W), Sec.map (P.d 1 2) z = 0 →
        ∀ (T : Scheme.{0}) (s t : ℤ) (a : Sec ((LL I Q).X s) T),
          Sec.map (I.d s t) (psi W μ z T s a) = psi W μ z T t (Sec.map ((LL I Q).d s t) a) := by
  intro R _ W I Q P μ z hz T s t a
  by_cases hst : s + 1 = t
  · subst hst
    have hB : Sec.map (P.d 1 (1 + 1)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z) = 0 := by
      rw [← res_map]
      have h2 : Sec.map (P.d 1 (1 + 1)) z = 0 := hz
      rw [h2]
      exact map_zero _
    have hL := μ.leibniz (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a))
      (Sec.res (prod.fst : W ⨯ T ⟶ W) z)
    rw [hB, map_zero, smul_zero, add_zero,
      mul_mid μ (W ⨯ T) (s + -1) (s + -1 + 1) (s + 1 + -1) (s + 1) (by omega) (by omega) (by omega)] at hL
    change Sec.map (I.d s (s + 1)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ a) +
        s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)) =
      Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ (Sec.map ((LL I Q).d s (s + 1)) a)) +
        (s + 1).negOnePow • μ.mul (W ⨯ T) (s + 1 + -1) 1 (s + 1) (by omega)
          (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ (Sec.map ((LL I Q).d s (s + 1)) a))) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)
    rw [map_add', map_units, hL, c₁_d, c₂_d, res_map, Int.negOnePow_succ]
    congr 1
    have hn : Sec.res (prod.snd : W ⨯ T ⟶ T) (- Sec.map (Q.d (s + -1) (s + 1 + -1)) (c₂ a)) =
        - Sec.map (Q.d (s + -1) (s + 1 + -1)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) := by
      rw [← res_map]
      exact map_neg _ _
    rw [hn, map_neg, LinearMap.neg_apply, smul_neg, Units.neg_smul, neg_neg]
  · have h1 : I.d s t = 0 := I.shape _ _ hst
    have h2 : (LL I Q).d s t = 0 := (LL I Q).shape _ _ hst
    rw [h1, h2, map_zeroS, map_zeroS, map_zero]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

namespace UpperTheory.Kun.InL

variable {R : Type} [CommRing R]

private theorem sgn {A : Type*} [AddCommGroup A] (a b : ℤˣ) (x : A) : b • a • a • b • x = x := by
  rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;> simp

private theorem inL_coe {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) :
    (inL h α₁ α₂).1 = α₁.1.comp (Cochain.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
      n.negOnePow • (α₂.1.rightShift (-1) n (by omega)).comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n) := rfl

private theorem inL_fst {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) :
    (inL h α₁ α₂).1.comp (Cochain.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero n) = α₁.1 := by
  rw [inL_coe, Cochain.add_comp, Cochain.units_smul_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
    Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    biprod.inl_fst, biprod.inr_fst, Cochain.comp_id]
  simp

private theorem inL_snd {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) :
    (inL h α₁ α₂).1.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n) =
      n.negOnePow • α₂.1.rightShift (-1) n (by omega) := by
  rw [inL_coe, Cochain.add_comp, Cochain.units_smul_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
    Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    biprod.inl_snd, biprod.inr_snd, Cochain.comp_id]
  simp

private theorem decomp {K I Q : Cx R} {n : ℤ} (x : Cochain K (LL I Q) n) :
    (x.comp (Cochain.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero n)).comp (Cochain.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
      (x.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n)).comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n) = x := by
  rw [Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_assoc_of_second_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, ← Cochain.comp_add, ← Cochain.ofHom_add, biprod.total, Cochain.comp_id]

private theorem unsh {K Q : Cx R} {m n : ℤ} (h : m + 1 = n) (ε : ℤˣ) (y : Cocycle K (sh Q) n) :
    ∃ a : Cocycle K Q m, ε • a.1.rightShift (-1) n (by omega) = y.1 := by
  have hy : n + -1 = m := by omega
  refine ⟨Cocycle.mk (ε • y.1.rightUnshift m hy) (m + 1) rfl ?_, ?_⟩
  · rw [δ_units_smul, Cochain.δ_rightUnshift _ m hy (m + 1) (n + 1) (by omega), Cocycle.δ_eq_zero]
    simp
  · change ε • (ε • y.1.rightUnshift m hy).rightShift (-1) n hy = y.1
    rw [Cochain.rightShift_units_smul, Cochain.rightShift_rightUnshift, smul_smul, Int.units_mul_self, one_smul]

end UpperTheory.Kun.InL

open UpperTheory.Kun.InL in
theorem UpperTheory.cohomologyClass_inL_surjective_and_injective :
    ∀ (R : Type) [CommRing R] {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n),
        (∀ x : Cocycle K (LL I Q) n, ∃ (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m), CohomologyClass.mk x = CohomologyClass.mk (inL h α₁ α₂)) ∧
        ∀ (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m), CohomologyClass.mk (inL h α₁ α₂) = 0 → CohomologyClass.mk α₁ = 0 ∧ CohomologyClass.mk α₂ = 0 := by
  intro R _ K I Q m n h
  refine ⟨fun x => ?_, fun α₁ α₂ h0 => ?_⟩
  · obtain ⟨a, ha⟩ := unsh (K := K) (Q := Q) h n.negOnePow (zcomp x (Cocycle.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n))
    refine ⟨zcomp x (Cocycle.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero n), a, ?_⟩
    congr 1
    apply Cocycle.ext
    rw [inL_coe]
    have e : n.negOnePow • a.1.rightShift (-1) n (by omega) = x.1.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n) := ha
    rw [← Cochain.units_smul_comp, e]
    exact (decomp x.1).symm
  · obtain ⟨p, hp, y, hy⟩ := (CohomologyClass.mk_eq_zero_iff _).1 h0
    have hy' : δ p n y = (inL h α₁ α₂).1 := hy
    constructor
    · rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨p, hp, y.comp (Cochain.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero p), ?_⟩
      rw [δ_comp_ofHom, hy', inL_fst]
    · rw [CohomologyClass.mk_eq_zero_iff]
      have hs : δ p n (y.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero p)) =
          n.negOnePow • α₂.1.rightShift (-1) n (by omega) := by
        rw [δ_comp_ofHom, hy', inL_snd]
      have hn : n + -1 = m := by omega
      have e : δ (p + -1) m ((y.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero p)).rightUnshift (p + -1) rfl) =
          (-1 : ℤ).negOnePow • n.negOnePow • α₂.1 := by
        rw [Cochain.δ_rightUnshift _ (p + -1) rfl m n hn, hs, Cochain.rightUnshift_units_smul, Cochain.rightUnshift_rightShift]
      refine ⟨p + -1, by omega, n.negOnePow • (-1 : ℤ).negOnePow •
        (y.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero p)).rightUnshift (p + -1) rfl, ?_⟩
      rw [δ_units_smul, δ_units_smul, e, sgn]
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace UpperTheory.DirectSumIndependence

private abbrev P (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    Ht q (sch.obj (Spec A)) n i →+ Ht q (sch.obj (Spec B)) n i :=
  pull _ (sch.map (Spec.map f)) (tw q i) n

private theorem pullback_comp₂ (q : ℕ) (i n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (x : Ht q (sch.obj (Spec A)) n i) : P q i n (f ≫ g) x = P q i n g (P q i n f x) := by
  show pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n x = _
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

private theorem isUnit_of_hom {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (h : IsUnit (q : A)) :
    IsUnit (q : B) := by
  simpa using h.map f.hom

private theorem chase (b1 : B1) (q : ℕ) (i : ℤ) {J : Type} [SmallCategory J] [IsFiltered J]
    (D D' : J ⥤ CommRingCat.{0}) (α : D ⟶ D') (c : Cocone D) (hc : IsColimit c)
    (c' : Cocone D') (hc' : IsColimit c') (g : c.pt ⟶ c'.pt)
    (hg : ∀ j, c.ι.app j ≫ g = α.app j ≫ c'.ι.app j)
    (hα : ∀ j, RE q i (α.app j)) (hq : ∀ j, IsUnit (q : D.obj j)) : RE q i g := by
  intro n
  change Function.Bijective (P q i n g)
  have hqc : IsUnit (q : c.pt) := by
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    exact isUnit_of_hom (c.ι.app j) (hq j)
  have hqc' : IsUnit (q : c'.pt) := isUnit_of_hom g hqc
  have hqD' : ∀ j, IsUnit (q : D'.obj j) := fun j => isUnit_of_hom (α.app j) (hq j)
  have comm : ∀ j y, P q i n g (P q i n (c.ι.app j) y) =
      P q i n (c'.ι.app j) (P q i n (α.app j) y) := by
    intro j y
    rw [← pullback_comp₂, ← pullback_comp₂, hg]
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, hy⟩ := (b1 q D c hc n i).1 x hqc
    change P q i n (c.ι.app j) y = x at hy
    subst hy
    rw [comm] at hx
    obtain ⟨k, f, hf⟩ := (b1 q D' c' hc' n i).2 j (P q i n (α.app j) y) (hqD' j) hx
    change P q i n (D'.map f) (P q i n (α.app j) y) = 0 at hf
    rw [← pullback_comp₂, ← α.naturality f, pullback_comp₂] at hf
    have h0 : P q i n (D.map f) y = 0 := by
      apply (hα k n).1
      show P q i n (α.app k) (P q i n (D.map f) y) = P q i n (α.app k) 0
      rw [hf, map_zero]
    rw [← c.w f, pullback_comp₂, h0, map_zero]
  · intro z
    obtain ⟨j, y', hy'⟩ := (b1 q D' c' hc' n i).1 z hqc'
    change P q i n (c'.ι.app j) y' = z at hy'
    obtain ⟨y, rfl⟩ := (hα j n).2 y'
    refine ⟨P q i n (c.ι.app j) y, ?_⟩
    rw [← hy']
    exact comm j y

variable {J : Type} [SmallCategory J] {A Y : CommRingCat.{0}} (φ : A ⟶ Y) (D : J ⥤ CommRingCat.{0})
  (t : ∀ j, A ⟶ D.obj j) (ht : ∀ {j k : J} (f : j ⟶ k), t j ≫ D.map f = t k)

private def Dp : J ⥤ CommRingCat.{0} where
  obj j := pushout φ (t j)
  map {j k} f := pushout.desc (pushout.inl φ (t k)) (D.map f ≫ pushout.inr φ (t k)) (by
    rw [← Category.assoc, ht f, pushout.condition])
  map_id j := by
    apply pushout.hom_ext <;> simp
  map_comp {j k l} f g := by
    apply pushout.hom_ext
    · erw [pushout.inl_desc, ← Category.assoc, pushout.inl_desc, pushout.inl_desc]
    · erw [pushout.inr_desc, ← Category.assoc, pushout.inr_desc, Category.assoc, pushout.inr_desc,
        D.map_comp, Category.assoc]

private theorem inl_Dp {j k : J} (f : j ⟶ k) :
    pushout.inl φ (t j) ≫ (Dp φ D t ht).map f = pushout.inl φ (t k) :=
  pushout.inl_desc _ _ _

private theorem inr_Dp {j k : J} (f : j ⟶ k) :
    pushout.inr φ (t j) ≫ (Dp φ D t ht).map f = D.map f ≫ pushout.inr φ (t k) :=
  pushout.inr_desc _ _ _

private def toDp : D ⟶ Dp φ D t ht where
  app j := pushout.inr φ (t j)
  naturality j k f := (inr_Dp φ D t ht f).symm

variable (c : Cocone D) (hc : IsColimit c) {Y' : CommRingCat.{0}} (w : Y ⟶ Y') (φ' : c.pt ⟶ Y')
  (cc : A ⟶ c.pt) (hcc : ∀ j, t j ≫ c.ι.app j = cc) (hp : IsPushout φ cc w φ')

private def cocDp : Cocone (Dp φ D t ht) where
  pt := Y'
  ι :=
    { app j := pushout.desc w (c.ι.app j ≫ φ') (by
        rw [← Category.assoc, hcc, hp.w])
      naturality j k f := by
        refine pushout.hom_ext ?_ ?_
        · erw [← Category.assoc, inl_Dp, pushout.inl_desc, ← Category.assoc, pushout.inl_desc,
            Category.comp_id]
        · erw [← Category.assoc, inr_Dp, Category.assoc, pushout.inr_desc, ← Category.assoc, c.w f,
            ← Category.assoc, pushout.inr_desc, Category.comp_id] }

private theorem inl_coc (j : J) :
    pushout.inl φ (t j) ≫ (cocDp φ D t ht c w φ' cc hcc hp).ι.app j = w :=
  pushout.inl_desc _ _ _

private theorem inr_coc (j : J) :
    pushout.inr φ (t j) ≫ (cocDp φ D t ht c w φ' cc hcc hp).ι.app j = c.ι.app j ≫ φ' :=
  pushout.inr_desc _ _ _

private theorem inl_indep [IsFiltered J] (e : Cocone (Dp φ D t ht)) (j k : J) :
    pushout.inl φ (t j) ≫ e.ι.app j = pushout.inl φ (t k) ≫ e.ι.app k := by
  rw [← e.w (IsFiltered.leftToMax j k), ← e.w (IsFiltered.rightToMax j k)]
  erw [← Category.assoc, inl_Dp, ← Category.assoc, inl_Dp]

private def resCoc (e : Cocone (Dp φ D t ht)) : Cocone D where
  pt := e.pt
  ι :=
    { app j := pushout.inr φ (t j) ≫ e.ι.app j
      naturality j k f := by
        erw [Category.comp_id, ← e.w f, ← Category.assoc, ← Category.assoc, inr_Dp]
        simp
        rfl }

private def isColDp [IsFiltered J] : IsColimit (cocDp φ D t ht c w φ' cc hcc hp) :=
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  { desc := fun e => hp.desc (pushout.inl φ (t j0) ≫ e.ι.app j0)
      (hc.desc (resCoc φ D t ht e)) (by
        erw [← hcc j0, Category.assoc, hc.fac, ← Category.assoc, pushout.condition, Category.assoc])
    fac := fun e j => by
      refine pushout.hom_ext ?_ ?_
      · erw [← Category.assoc, inl_coc, hp.inl_desc]
        exact inl_indep φ D t ht e j0 j
      · erw [← Category.assoc, inr_coc, Category.assoc, hp.inr_desc, hc.fac]
        rfl
    uniq := fun e m hm => by
      refine hp.hom_ext ?_ ?_
      · erw [hp.inl_desc, ← hm j0, ← Category.assoc, inl_coc]
        rfl
      · erw [hp.inr_desc]
        refine hc.hom_ext fun j => ?_
        erw [hc.fac, ← Category.assoc, ← inr_coc φ D t ht c w φ' cc hcc hp j, Category.assoc, hm j]
        rfl }

end UpperTheory.DirectSumIndependence

theorem UpperTheory.cohomology_continuity_filtered_colimit_rings :
    LateralTheory.E.t_E3Cut.Limit := by
  intro hyp q _ i A Y φ hq hEt C c hc Y' w φ' hp
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hc
  have ht : ∀ {j k : J} (f : j ⟶ k), t.app j ≫ D.map f = t.app k := by
    intro j k f
    rw [← t.naturality f]
    simp
  exact UpperTheory.DirectSumIndependence.chase hyp.2.2.2.2.2.2.1 q i D
    (UpperTheory.DirectSumIndependence.Dp φ D (fun j => t.app j) ht)
    (UpperTheory.DirectSumIndependence.toDp φ D (fun j => t.app j) ht) (Cocone.mk C s) hs
    (UpperTheory.DirectSumIndependence.cocDp φ D (fun j => t.app j) ht (Cocone.mk C s) w φ' c
      (fun j => (hts j).2) hp)
    (UpperTheory.DirectSumIndependence.isColDp φ D (fun j => t.app j) ht (Cocone.mk C s) hs w φ' c
      (fun j => (hts j).2) hp)
    φ'
    (fun j => (UpperTheory.DirectSumIndependence.inr_coc φ D (fun j => t.app j) ht (Cocone.mk C s) w φ' c
      (fun j => (hts j).2) hp j).symm)
    (fun j => hEt _ _ (hts j).1 _ _ _ (IsPushout.of_hasPushout _ _))
    (fun j => UpperTheory.DirectSumIndependence.isUnit_of_hom (t.app j) hq)
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

private lemma exists_local_generator {B : Type} [CommRing B] [IsDedekindDomain B]
    (I : Ideal B) (p : Ideal B) [hp : p.IsPrime] :
    ∃ π ∈ I, ∃ s, s ∉ p ∧ ∀ x ∈ I, s * x ∈ Ideal.span {π} :=
  _root_.UpperTheory.Reformulated.B.ExistsLocalGenerator.exists_local_generator I p

theorem UpperTheory.dedekind_spec_open_isAffine :
    ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (W : (Spec (CommRingCat.of B)).Opens), IsAffineOpen W := by
  intro B _ _ W
  let S : Set (PrimeSpectrum B) := ((W : Set (Spec (CommRingCat.of B)))ᶜ : Set (Spec (CommRingCat.of B)))
  have hS : IsClosed S := W.isOpen.isClosed_compl
  let I : Ideal B := PrimeSpectrum.vanishingIdeal S
  have hWc : PrimeSpectrum.zeroLocus (I : Set B) = S := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hS.closure_eq
  let D : B → (Spec (CommRingCat.of B)).Opens := fun r =>
    PrimeSpectrum.basicOpen (R := CommRingCat.of B) r
  have hbasic : ∀ r : B, IsAffineOpen (D r) := by
    intro r
    have h := (isAffineOpen_top (Spec (CommRingCat.of B))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv r)
    rwa [basicOpen_eq_of_affine] at h
  have hmain : IsAffineHom W.ι := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
    obtain ⟨π, hπ, s, hs, hsI⟩ := @exists_local_generator B _ _ I x.asIdeal x.isPrime
    refine ⟨D s, hs, hbasic s, ?_⟩
    have hEq : W ⊓ D s = D (s * π) := by
      ext q
      have hq : q ∈ W ↔ ¬ (I : Set B) ⊆ q.asIdeal := by
        have h1 : (I : Set B) ⊆ q.asIdeal ↔ q ∉ W := Set.ext_iff.1 hWc q
        rw [h1, not_not]
      have hDm : ∀ r : B, q ∈ D r ↔ r ∉ q.asIdeal := fun r => Iff.rfl
      change q ∈ W ∧ q ∈ D s ↔ q ∈ D (s * π)
      rw [hDm, hDm, hq]
      have hqp : q.asIdeal.IsPrime := q.isPrime
      constructor
      · rintro ⟨hIq, hsq⟩ hm
        rcases hqp.mem_or_mem hm with h | h
        · exact hsq h
        · refine hIq fun y hy => ?_
          have h2 : s * y ∈ q.asIdeal :=
            (Ideal.span_singleton_le_iff_mem q.asIdeal).2 h (hsI y hy)
          exact (hqp.mem_or_mem h2).resolve_left hsq
      · intro hm
        refine ⟨fun hsub => hm (Ideal.mul_mem_left _ _ (hsub hπ)),
          fun h => hm (Ideal.mul_mem_right _ _ h)⟩
    have h := hbasic (s * π)
    rw [← hEq] at h
    have h2 := h.preimage_of_isOpenImmersion W.ι (by simp)
    have e : W.ι ⁻¹ᵁ (W ⊓ D s) = W.ι ⁻¹ᵁ D s := by
      ext y
      exact ⟨fun hy => hy.2, fun hy => ⟨y.2, hy⟩⟩
    rwa [e] at h2
  have : IsAffine W.toScheme := isAffine_of_isAffineHom W.ι
  exact this
end
