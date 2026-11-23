module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.chi :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] (q n m : ℕ) (a : Fin q → ℕ), (∀ j, m ≤ a j) → ∀ p : Fin q × Fin n, ∃ χ : Del l n a →* Multiplicative (Om O m), ∀ p', χ (Pi.mulSingle p' (Multiplicative.ofAdd 1)) = Multiplicative.ofAdd (if p = p' then 1 else 0) := by
  intro l _ O _ _ _ _ q n m a ha p
  have hl : (l : O) ∈ maximalIdeal O := by
    haveI : CharP (ResidueField O) l := IsCoef.char
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have h0 : (zmultiplesHom (Om O m) 1) ((l ^ a p.1 : ℕ) : ℤ) = 0 := by
    have : ((l : O) ^ a p.1) ∈ maximalIdeal O ^ m :=
      Ideal.pow_le_pow_right (ha _) (Ideal.pow_mem_pow hl _)
    have h2 := Ideal.Quotient.eq_zero_iff_mem.mpr this
    simpa using h2
  let f : ZMod (l ^ a p.1) →+ Om O m := ZMod.lift _ ⟨zmultiplesHom (Om O m) 1, h0⟩
  have f1 : f 1 = 1 := by
    have := ZMod.lift_coe (l ^ a p.1) ⟨zmultiplesHom (Om O m) 1, h0⟩ 1
    simpa [f] using this
  refine ⟨(AddMonoidHom.toMultiplicative f).comp
    (Pi.evalMonoidHom (fun p : Fin q × Fin n => Multiplicative (ZMod (l ^ a p.1))) p), fun p' => ?_⟩
  by_cases h : p = p'
  · subst h
    simp [f1]
  · simp [h, Pi.mulSingle_eq_of_ne h]
end

section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem core_ex {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K P : Subgroup Γ) [P.Normal] (hK : IsOpen (K : Set Γ)) (hP : P ≤ K) :
    ∃ U : OpenNormalSubgroup Γ, P ≤ U.toSubgroup ∧ U.toSubgroup ≤ K := by
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hK
  haveI : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : IsClosed (K.normalCore : Set Γ) := Subgroup.normalCore_isClosed K (K.isClosed_of_isOpen hK)
  have ho : IsOpen (K.normalCore : Set Γ) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hc
  exact ⟨{ toSubgroup := K.normalCore, isOpen' := ho, isNormal' := inferInstance },
    Subgroup.normal_le_normalCore.2 hP, K.normalCore_le⟩

private theorem pl_normal (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ) :
    (PL l H).Normal := by
  refine ⟨fun a ha g => ?_⟩
  simp only [PL, Subgroup.mem_iInf] at ha ⊢
  intro U hU
  exact U.isNormal'.conj_mem a (ha U hU) g

private theorem pl_le (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : OpenNormalSubgroup Γ) :
    PL l H.toSubgroup ≤ H.toSubgroup := by
  intro a ha
  simp only [PL, Subgroup.mem_iInf] at ha
  exact ha H fun h hh => ⟨0, by rw [pow_zero, pow_one]; exact hh⟩

theorem UpperTheory.V.Th.Sp.close :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (y : Pt G0.frame O n), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → ∀ K : ℕ, ∀ᶠ N in atTop, ∀ j a b, mat y.ρ ((T.h N).p₀ (T.ph N j)) a b - mat y.ρ (T.sg j) a b ∈ maximalIdeal O ^ K := by
  intro l _ L G0 T n O _ _ _ y hPL K
  haveI := pl_normal l T.H.toSubgroup
  have hle := pl_le l T.H
  let R : G0.G₀ →* Matrix (Fin n) (Fin n) (O ⧸ maximalIdeal O ^ K) :=
    (Ideal.Quotient.mk (maximalIdeal O ^ K)).mapMatrix.toMonoidHom.comp (mat y.ρ)
  have hR : ∀ g i j, R g i j = Ideal.Quotient.mk (maximalIdeal O ^ K) (mat y.ρ g i j) := fun _ _ _ => rfl
  have h0 : IsLocallyConstant fun g : G0.G₀ => R g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have : ∀ᶠ g in nhds g0, ∀ i j, R g i j = R g0 i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        (y.cont i j K).eventually_eq g0
    filter_upwards [this] with g hg
    exact Matrix.ext hg
  have ho : IsOpen ((R.ker.map G0.η.ker.subtype : Subgroup G0.Γ) : Set G0.Γ) :=
    G0.η_open.isOpenMap_subtype_val _ (h0.isOpen_fiber 1)
  have h1R : ∀ g, y.ρ g = 1 → R g = 1 := fun g h => by
    show (Ideal.Quotient.mk (maximalIdeal O ^ K)).mapMatrix (Units.coeHom _ (y.ρ g)) = 1
    rw [h, map_one, map_one]
  obtain ⟨V, h1, h2⟩ := core_ex _ (PL l T.H.toSubgroup) ho fun g hg =>
    ⟨⟨g, T.H_η g (hle hg)⟩, h1R _ (hPL _ hg), rfl⟩
  filter_upwards [Filter.eventually_all.2 fun j => T.ph_lim V j h1] with N hN j a b
  obtain ⟨u, hu, e1⟩ := h2 (hN j)
  have e2 : (T.h N).p₀ (T.ph N j) = u * T.sg j := Subtype.ext (by
    show (T.h N).p (T.ph N j) = (u : G0.Γ) * T.sg j
    rw [show (u : G0.Γ) = _ from e1, inv_mul_cancel_right])
  have e3 : R ((T.h N).p₀ (T.ph N j)) = R (T.sg j) := by
    rw [e2, map_mul, show R u = 1 from hu, one_mul]
  rw [← Ideal.Quotient.eq, ← hR, ← hR, e3]
end

section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem UpperTheory.V.Th.Sp.trace_partial_charpoly_single {T G : Type} [CommRing T] [Group G] (t : MonoidAlgebra T G →ₗ[T] T)
    (g ta : G) (a y : T) :
    t (MonoidAlgebra.single g a * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y)) =
      a * (t (MonoidAlgebra.single (g * ta) 1) - t (MonoidAlgebra.single g 1)) -
        y * (a * t (MonoidAlgebra.single g 1)) := by
  have h : ∀ (k : G) (b : T), t (MonoidAlgebra.single k b) = b * t (MonoidAlgebra.single k 1) := fun k b => by
    rw [← smul_eq_mul, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [mul_sub, mul_sub, mul_one, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one,
    map_sub, map_sub, h (g * ta) a, h g a, h g (a * y)]
  ring

theorem UpperTheory.V.Th.Sp.q2 :
    ∀ (O T G X : Type) [CommRing O] [CommRing T] [Algebra O T] [Group G] [AddCommGroup X] [Module O X] (n : ℕ) (D : GDet n T G) (x : T →ₐ[O] O) (del : T →ₗ[O] X) (ta : G) (y : T) (Q : MonoidAlgebra T G), 1 ≤ n → IsDer x del → x y = 0 → (∀ g, x (D.tr (MonoidAlgebra.single (g * ta) 1)) = x (D.tr (MonoidAlgebra.single g 1))) → x (D.tr (Q * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y))) = 0 ∧ del (D.tr (Q * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y))) = del (D.tr (MonoidAlgebra.mapRingHom G ((algebraMap O T).comp (x : T →+* O)) Q * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 0))) - x (D.tr Q) • del y := by
  intro O T G X _ _ _ _ _ _ n D x del ta y Q hn hd hy hta
  obtain ⟨t, ht⟩ := (UpperTheory.V.CA.d_tr D.toDet).1 hn
  have ht' : ∀ z, D.tr z = t z := fun z => by rw [ht, (UpperTheory.V.CA.d_toDet D z).2.2.1]
  simp only [ht'] at hta ⊢
  induction Q using MonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ =>
    simp only [map_add (f := _), add_mul, hP.1, hQ.1, hP.2, hQ.2, add_zero, true_and, add_smul]
    abel
  | single g a =>
    have h : t (MonoidAlgebra.single g a) = a * t (MonoidAlgebra.single g 1) := by
      rw [← smul_eq_mul, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [MonoidAlgebra.mapRingHom_single, UpperTheory.V.Th.Sp.trace_partial_charpoly_single, UpperTheory.V.Th.Sp.trace_partial_charpoly_single, h]
    have h0 : x (t (MonoidAlgebra.single (g * ta) 1) - t (MonoidAlgebra.single g 1)) = 0 := by
      rw [map_sub, hta, sub_self]
    refine ⟨by rw [map_sub, map_mul, map_mul, h0, hy, mul_zero, zero_mul, sub_zero], ?_⟩
    rw [map_sub, hd, hd, h0, hy, zero_smul, zero_smul, add_zero, zero_add, zero_mul, sub_zero, RingHom.comp_apply,
      ← Algebra.smul_def, map_smul]
    rfl
end
