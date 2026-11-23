module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle009
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial Cardinal

noncomputable section

namespace FreeParAlgIndep

theorem genPar_algIndep (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k)
      (GenParField k e n)) :=
    IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)
  have h := (MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj
  have hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) =
      genPar k e n := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]
  rwa [hc] at h

theorem algebraicIndependent_of_trdeg {k L : Type} [Field k] [Field L] [Algebra k L]
    (A₀ : Subalgebra k L) {ι : Type} [Finite ι] (w : ι → L)
    [Algebra.IsAlgebraic (Algebra.adjoin A₀ (Set.range w)) L] {e : ℕ}
    (htr : Algebra.trdeg k A₀ ≤ e) (hle : (e : Cardinal) + #ι ≤ Algebra.trdeg k L) :
    AlgebraicIndependent A₀ w := by
  have : FaithfulSMul k A₀ :=
    (faithfulSMul_iff_algebraMap_injective k A₀).2 (algebraMap k A₀).injective
  have : FaithfulSMul A₀ L :=
    (faithfulSMul_iff_algebraMap_injective A₀ L).2 Subtype.val_injective
  have hadd := trdeg_add_eq k A₀ (A := L)
  refine (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite A₀ w ?_).1
  have h3 : #ι + (e : Cardinal) ≤ Algebra.trdeg A₀ L + e := by
    rw [add_comm, add_comm _ (e : Cardinal)]
    refine hle.trans ?_
    rw [← hadd]
    gcongr
  exact (Cardinal.add_le_add_iff_of_lt_aleph0 (Cardinal.natCast_lt_aleph0)).1 h3

theorem proof : FreeParAlgIndep.Statement := by
  intro k _ _ n e L _ _ _ _ _ x hgen hU hT j₀ hx0 htr
  generalize hz : (fun m => x m * (x j₀)⁻¹) = z at htr ⊢
  have hzm : ∀ m, z m = x m * (x j₀)⁻¹ := fun m => by rw [← hz]
  have hz0 : z j₀ = 1 := by rw [hzm, mul_inv_cancel₀ hx0]
  rw [IntermediateField.algebraicIndependent_adjoin_iff]

  let w : (Fin e × {j : Fin n // j ≠ j₀}) ⊕ Fin n → L :=
    Sum.elim (fun p => algebraMap (GenParField k e n) L (genPar k e n (.inl (p.1, p.2.1))))
      (fun j => algebraMap (GenParField k e n) L (genPar k e n (.inr j)))
  have halg : Algebra.IsAlgebraic
      (Algebra.adjoin (Algebra.adjoin k (Set.range z)) (Set.range w)) L := by
    set A₀ := Algebra.adjoin k (Set.range z) with hA₀
    set B := Algebra.adjoin A₀ (Set.range w) with hB
    have hzB : ∀ m, z m ∈ B := fun m =>
      Subalgebra.algebraMap_mem B (⟨z m, Algebra.subset_adjoin ⟨m, rfl⟩⟩ : A₀)
    have hwB : ∀ i, w i ∈ B := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
    have hkB : ∀ c : k, algebraMap k L c ∈ B := fun c => by
      rw [IsScalarTower.algebraMap_apply k A₀ L]
      exact Subalgebra.algebraMap_mem B _
    have hparB : ∀ p, algebraMap (GenParField k e n) L (genPar k e n p) ∈ B := by
      rintro (⟨i, j⟩ | j)
      · by_cases hj : j = j₀
        · rw [hj]
          have hsum : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j = 0 := by
            simp only [hzm, ← mul_assoc, ← Finset.sum_mul, hU i, zero_mul]
          have h1 := Finset.add_sum_erase Finset.univ
            (fun j => algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j)
            (Finset.mem_univ j₀)
          simp only [hz0, mul_one] at h1
          rw [hsum, ← eq_neg_iff_add_eq_zero] at h1
          rw [h1]
          refine neg_mem (Subalgebra.sum_mem _ fun j' hj' => Subalgebra.mul_mem _ ?_ (hzB j'))
          exact hwB (.inl (i, ⟨j', Finset.ne_of_mem_erase hj'⟩))
        · exact hwB (.inl (i, ⟨j, hj⟩))
      · exact hwB (.inr j)
    have hmem : ∀ b ∈ B, IsAlgebraic B b := fun b hb => isAlgebraic_algebraMap (⟨b, hb⟩ : B)
    have hx0alg : IsAlgebraic B (x j₀) := by
      have hs : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j = (x j₀)⁻¹ := by
        simp only [hzm, ← mul_assoc, ← Finset.sum_mul, hT, one_mul]
      have h2 : IsAlgebraic B
          (∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j) :=
        hmem _ (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (hwB (.inr j)) (hzB j))
      have := h2.inv
      rwa [hs, inv_inv] at this
    have hxalg : ∀ m, IsAlgebraic B (x m) := fun m => by
      have hm : x m = z m * x j₀ := by rw [hzm, inv_mul_cancel_right₀ hx0]
      rw [hm]
      exact (hmem _ (hzB m)).mul hx0alg
    have hpoly : ∀ a : MvPolynomial (Par e n) k, algebraMap (GenParField k e n) L
        (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n) a) ∈ B := by
      intro a
      induction a using MvPolynomial.induction_on with
      | C c =>
        rw [← MvPolynomial.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k) (GenParField k e n),
          ← IsScalarTower.algebraMap_apply k (GenParField k e n) L]
        exact hkB c
      | add a b ha hb =>
        rw [map_add (f := _), map_add (f := _)]
        exact Subalgebra.add_mem _ ha hb
      | mul_X a p ha =>
        rw [map_mul, map_mul]
        exact Subalgebra.mul_mem _ ha (hparB p)
    have hK : ∀ f, IsAlgebraic B (algebraMap (GenParField k e n) L f) := fun f => by
      obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Par e n) k) f
      rw [map_div₀, div_eq_mul_inv]
      exact (hmem _ (hpoly a)).mul (hmem _ (hpoly b)).inv
    refine ⟨fun y => ?_⟩
    have hy : y ∈ (MvPolynomial.aeval (R := GenParField k e n) x).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval, hgen]
      trivial
    obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
    clear hy
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.aeval_C]
      exact hK c
    | add a b ha hb =>
      rw [map_add (f := _)]
      exact ha.add hb
    | mul_X a j ha =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact ha.mul (hxalg j)

  have hcard : (e : Cardinal) + #((Fin e × {j : Fin n // j ≠ j₀}) ⊕ Fin n) ≤
      Algebra.trdeg k L := by
    have hind : AlgebraicIndependent k
        (fun p => algebraMap (GenParField k e n) L (genPar k e n p)) :=
      (genPar_algIndep k e n).map' (f := IsScalarTower.toAlgHom k (GenParField k e n) L)
        (algebraMap (GenParField k e n) L).injective
    have hinj : Function.Injective (Sum.elim (fun i : Fin e => (Sum.inl (i, j₀) : Par e n))
        (Sum.elim (fun p : Fin e × {j : Fin n // j ≠ j₀} => (Sum.inl (p.1, p.2.1) : Par e n))
          Sum.inr)) := by
      rintro (i | ⟨i, j, hj⟩ | j) (i' | ⟨i', j', hj'⟩ | j') h <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
          reduceCtorEq, Subtype.mk.injEq, and_true] at h ⊢ <;>
        first | exact h | exact absurd h.2.symm hj' | exact absurd h.2 hj
    calc (e : Cardinal) + #((Fin e × {j : Fin n // j ≠ j₀}) ⊕ Fin n)
        = #(Fin e ⊕ ((Fin e × {j : Fin n // j ≠ j₀}) ⊕ Fin n)) := by simp
      _ ≤ #(Par e n) := Cardinal.mk_le_of_injective hinj
      _ ≤ Algebra.trdeg k L := hind.cardinalMk_le_trdeg
  exact (algebraicIndependent_of_trdeg (Algebra.adjoin k (Set.range z)) w htr hcard).comp
    Sum.inl Sum.inl_injective

end FreeParAlgIndep

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace SecPointSeparable

theorem isSeparable_of_derivation_eq_zero {K L : Type} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] (h : ∀ D : Derivation K L L, D = 0) : Algebra.IsSeparable K L := by
  rw [← Algebra.FormallyUnramified.iff_isSeparable]
  refine ⟨⟨fun a b => ?_⟩⟩
  have key : ∀ ω : Ω[L⁄K], ω = 0 := by
    intro ω
    refine (Module.forall_dual_apply_eq_zero_iff L ω).1 fun φ => ?_
    have : φ = 0 := by
      apply (KaehlerDifferential.linearMapEquivDerivation K L).injective
      rw [map_zero]
      exact h _
    rw [this, LinearMap.zero_apply]
  rw [key a, key b]

end SecPointSeparable

open SecPointSeparable in
theorem SecPointSeparable.proof (h₁ : GenericFormsKer.Statement) (h₂ : DerivSpanTrdeg.Statement)
    (h₃ : FreeParAlgIndep.Statement) : SecPointSeparable.Statement := by
  intro k _ _ n e L _ _ _ _ _ x hx hU hT htr
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, x j₀ ≠ 0 := by
    by_contra! h
    simp [h] at hT
  set z : Fin n → L := fun m => x m * (x j₀)⁻¹ with hz
  obtain ⟨r, hre, b, hb⟩ := h₂ k L (Fin n) z e (htr j₀ hj₀)
  have hind := h₃ k n e L x hx hU hT j₀ hj₀ (htr j₀ hj₀)
  apply isSeparable_of_derivation_eq_zero
  intro D
  obtain ⟨c, hc⟩ := hb (D.restrictScalars k)
  have hc' : ∀ j, D (z j) = ∑ m, c m * (b m j : L) := hc
  have hDK : ∀ a : GenParField k e n, D (algebraMap (GenParField k e n) L a) = 0 :=
    fun a => D.map_algebraMap a
  have hlin : ∀ (a : GenParField k e n) (y : L),
      D (algebraMap (GenParField k e n) L a * y) = algebraMap (GenParField k e n) L a * D y := by
    intro a y
    rw [D.leibniz, hDK, smul_zero, add_zero, smul_eq_mul]
  have hDz₀ : D (z j₀) = 0 := by
    simp only [z, mul_inv_cancel₀ hj₀, Derivation.map_one_eq_zero]
  have hUDz : ∀ i : Fin e,
      ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * D (z j) = 0 := by
    intro i
    have h0 : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j = 0 := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hU i, zero_mul]
    have := congrArg D h0

    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => (hlin _ _).symm
  have hDz : ∀ j, D (z j) = 0 := by
    have key := h₁ (IntermediateField.adjoin k (Set.range z)) L {j : Fin n // j ≠ j₀} e r hre
      (fun p => algebraMap (GenParField k e n) L (genPar k e n (.inl (p.1, p.2.1)))) hind
      (fun m j => b m j.1) c (fun i => ?_)
    · intro j
      by_cases hj : j = j₀
      · rw [hj, hDz₀]
      · rw [hc' j]
        exact key ⟨j, hj⟩
    · have := hUDz i
      rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, hDz₀, mul_zero, zero_add] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc' j.1]
      rfl
  have hx₀ : D (x j₀) = 0 := by
    have hs : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j = (x j₀)⁻¹ := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hT, one_mul]
    have h1 := congrArg D hs

    rw [map_sum, Finset.sum_eq_zero fun j _ => by rw [hlin, hDz, mul_zero], Derivation.leibniz_inv,
    eq_comm, smul_eq_mul, neg_mul, neg_eq_zero, mul_eq_zero] at h1
    exact h1.resolve_left (pow_ne_zero _ (inv_ne_zero hj₀))
  have hxj : ∀ j, D (x j) = 0 := by
    intro j
    have hxz : x j = z j * x j₀ := by simp only [z, mul_assoc, inv_mul_cancel₀ hj₀, mul_one]
    rw [hxz, D.leibniz, hx₀, hDz, smul_zero, smul_zero, add_zero]
  exact Derivation.ext_of_adjoin_eq_top (Set.range x) hx (by rintro _ ⟨j, rfl⟩; simpa using hxj j)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

attribute [local simp] MvPolynomial.bind₁

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

section Lemmas

variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}

def chartVar (e n : ℕ) (ij : Fin (e + 1) × Fin n) : Par e n :=
  Fin.cases (motive := fun _ => Par e n) (.inr ij.2) (fun i => .inl (i, ij.2)) ij.1

theorem chartVar_injective (e n : ℕ) : Function.Injective (chartVar e n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  induction i using Fin.cases <;> induction i' using Fin.cases <;>
    simp_all [chartVar, Fin.cases_zero, Fin.cases_succ]

theorem parToFrac_algebraMap' (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (x : MvPolynomial (Par e n) (𝓞 K)) :
    parToFrac e n v (algebraMap _ (ParDVR e n v) x) = algebraMap _ (ParFrac K e n) x := by
  rw [parToFrac, IsLocalization.lift_eq]

theorem kToFrac_algebraMap (e n : ℕ) (a : 𝓞 K) :
    kToFrac K e n (algebraMap (𝓞 K) K a) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (C a) := by
  rw [kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

theorem eval_specRest_chart (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) :
    eval (fun j => parYF K e n (.inr j))
        (specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (rename (chartVar e n) g) := by
  have h : ((eval fun j => parYF K e n (.inr j)).comp
      ((eval₂Hom (C.comp (kToFrac K e n)) (fun ij => Fin.cases
        (motive := fun _ => MvPolynomial (Fin n) (ParFrac K e n)) (X ij.2)
        (fun i => C (parYF K e n (.inl (i, ij.2)))) ij.1)).comp (map (algebraMap (𝓞 K) K)))) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n)).comp (rename (chartVar e n)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun ij => ?_)
    · simp [kToFrac_algebraMap]
    · rcases ij with ⟨i, j⟩
      induction i using Fin.cases <;> simp [chartVar, parYF]
  exact congrArg (fun φ => φ g) h

theorem eval_specRest_lin (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) :
    eval (fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j)))
        (specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (rename Sum.inl (specFirst g u)) := by
  have h : ((eval fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))).comp
      ((eval₂Hom (C.comp (kToFrac K e n)) (fun ij => Fin.cases
        (motive := fun _ => MvPolynomial (Fin n) (ParFrac K e n)) (X ij.2)
        (fun i => C (parYF K e n (.inl (i, ij.2)))) ij.1)).comp (map (algebraMap (𝓞 K) K)))) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n)).comp
        ((rename (Sum.inl : Fin e × Fin n → Par e n)).toRingHom.comp (bind₁ (specFirstVar u)).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun ij => ?_)
    · simp [kToFrac_algebraMap]
    · rcases ij with ⟨i, j⟩
      induction i using Fin.cases <;> simp [specFirstVar, parYF, kToFrac_algebraMap]
  exact congrArg (fun φ => φ g) h

theorem secLin_eq_sum {R : Type*} [CommRing R] {Q : Ideal (MvPolynomial (Fin n) R)} {y : Par e n → R}
    (w : Fin n → R) : secLin Q y w = ∑ j, algebraMap R (SecAlg Q y) (w j) * secCoord Q y j := by

  simp only [secLin, linForm, map_sum, map_mul]
  rfl

theorem chart_sum_eq_one {R : Type*} [CommRing R] {Q : Ideal (MvPolynomial (Fin n) R)}
    {y : Par e n → R} : ∑ j, algebraMap R (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by
  rw [← secLin_eq_sum]
  have hmem : chartForm y - 1 ∈ secIdeal Q y := Ideal.mem_sup_right (Ideal.subset_span rfl)
  have h := Ideal.Quotient.eq.mpr hmem
  rw [map_one] at h
  exact h

end Lemmas

theorem NormIdentity.proof (hcn : ChowNormForm.Statement) (hfin : SecBFinite.Statement)
    (htf : SecBTorsionFree.Statement) (hgen : SecBGeneric.Statement)
    (hloc : NormFormLocalization.Statement) (hev : NormFormEval.Statement)
    (hai : ParAlgIndep.Statement) (hfr : ParFracIsFractionRing.Statement)
    (hdvr : ParDVRIsDVR.Statement) : NormIdentity.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := hdvr K e n v
  obtain ⟨φ, hφc, hφr, hφloc⟩ := hgen K n e I v hI
  have hfinB : Module.Finite (ParDVR e n v) (SecB e I v) := hfin K n e I _ v hI hf
  have htfB : Module.IsTorsionFree (ParDVR e n v) (SecB e I v) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r b h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · exact Or.inr (htf K n e I v hI r b hr h)
  have hfreeB : Module.Free (ParDVR e n v) (SecB e I v) := Module.free_of_finite_type_torsion_free'
  let _iRF : Algebra (ParDVR e n v) (ParFrac K e n) := (parToFrac e n v).toAlgebra
  have hFR : IsFractionRing (ParDVR e n v) (ParFrac K e n) := hfr K e n v
  let _iKF : Algebra K (ParFrac K e n) := (kToFrac K e n).toAlgebra
  let _iBL : Algebra (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) := φ.toAlgebra
  have _t1 : IsScalarTower (ParDVR e n v) (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) :=
    IsScalarTower.of_algebraMap_eq (R := ParDVR e n v) (S := SecB e I v)
      (A := SecAlg (idealF e I) (parYF K e n)) fun r => (hφr r).symm
  have hNL := hloc (ParDVR e n v) (ParFrac K e n) (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) n
    (secCoord (modelR e I v) (parY e n v))
  have hxs : (fun j => algebraMap (SecB e I v) (SecAlg (idealF e I) (parYF K e n))
      (secCoord (modelR e I v) (parY e n v) j)) = secCoord (idealF e I) (parYF K e n) := funext hφc
  rw [hxs] at hNL
  obtain ⟨-, c, -, hcn'⟩ := hcn K (ParFrac K e n) n e I (g.map (algebraMap (𝓞 K) K)) (parYF K e n)
    (hai K e n) hI hf
  set P := normForm (R := ParDVR e n v) (SecB e I v) (secCoord (modelR e I v) (parY e n v)) with hP
  replace hcn' : specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n) =
      C c * P.map (algebraMap (ParDVR e n v) (ParFrac K e n)) := by
    rw [hNL]
    exact hcn'

  have hevP : ∀ z : Fin n → ParDVR e n v,
      eval (fun j => parToFrac e n v (z j)) (P.map (algebraMap (ParDVR e n v) (ParFrac K e n))) =
        parToFrac e n v (Algebra.norm (ParDVR e n v)
          (∑ j, algebraMap (ParDVR e n v) (SecB e I v) (z j) * secCoord (modelR e I v) (parY e n v) j)) := by
    intro z
    rw [eval_map, ← hev (ParDVR e n v) (SecB e I v) n _ z, ← hP]
    show eval₂ _ _ P = parToFrac e n v (eval₂ (RingHom.id _) z P)
    rw [hom_eval₂]
    rfl

  have hT := congrArg (eval fun j => parYF K e n (.inr j)) hcn'
  rw [eval_specRest_chart, map_mul, eval_C] at hT
  have hTpt : (fun j => parYF K e n (.inr j)) = fun j => parToFrac e n v (parY e n v (.inr j)) := by
    funext j
    rw [parY, parToFrac_algebraMap']
    rfl
  rw [hTpt, hevP, chart_sum_eq_one, map_one, map_one, mul_one] at hT

  have hU := congrArg (eval fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))) hcn'
  rw [eval_specRest_lin, map_mul, eval_C] at hU
  have hUpt : (fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))) =
      fun j => parToFrac e n v (algebraMap (𝓞 K) (ParDVR e n v) (u j)) := by
    funext j
    rw [kToFrac_algebraMap, IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K))
      (ParDVR e n v), parToFrac_algebraMap']
    rfl
  rw [hUpt, hevP, ← secLin_eq_sum, ← hT, ← parToFrac_algebraMap', ← parToFrac_algebraMap', ← map_mul] at hU
  have hinj : Function.Injective (parToFrac e n v) := IsFractionRing.injective (ParDVR e n v) (ParFrac K e n)
  have hUR := hinj hU

  obtain ⟨m, hm⟩ := hprim
  have hnot : rename (chartVar e n) g ∈ (parPrime e n v).primeCompl := by
    intro hmem
    have hmem' : rename (chartVar e n) g ∈ Ideal.map C v.asIdeal := hmem
    rw [MvPolynomial.mem_map_C_iff] at hmem'
    have hmem := hmem'
    have := hmem (Finsupp.mapDomain (chartVar e n) m)
    rw [coeff_rename_mapDomain _ (chartVar_injective e n)] at this
    exact hm this
  have hunit : IsUnit (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename (chartVar e n) g)) :=
    IsLocalization.map_units (ParDVR e n v) (⟨_, hnot⟩ : (parPrime e n v).primeCompl)
  exact ⟨hunit.unit, hUR⟩

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem ParFracIsFractionRing.proof : ParFracIsFractionRing.Statement := by
  intro K _ _ e n v
  let := (parToFrac e n v).toAlgebra
  have : IsScalarTower (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (ParFrac K e n) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = parToFrac e n v (algebraMap _ _ x)
      unfold parToFrac
      rw [IsLocalization.lift_eq]
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (parPrime e n v).primeCompl
    (ParDVR e n v) (ParFrac K e n)

end

end GroundTheory.Heights₂.Heights.Vertical
end
