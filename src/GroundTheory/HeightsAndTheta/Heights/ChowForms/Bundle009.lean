module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormSection
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

private def firstGroupVars (e n : ℕ) : Fin (e + 1) × Fin n ≃ Fin n ⊕ Fin e × Fin n where
  toFun ij := Fin.cases (motive := fun _ => Fin n ⊕ Fin e × Fin n) (Sum.inl ij.2)
    (fun i => Sum.inr (i, ij.2)) ij.1
  invFun := Sum.elim (fun m => (0, m)) (fun im => (im.1.succ, im.2))
  left_inv := by
    rintro ⟨i, m⟩
    cases i using Fin.cases <;> rfl
  right_inv := by
    rintro (m | ⟨i, m⟩) <;> rfl

private theorem firstGroup_eq {F : Type*} [Field F] {n e : ℕ} (g : MvPolynomial (Fin (e + 1) × Fin n) F) :
    firstGroup g = ((renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n))) g := by
  have h : (aeval (fun ij : Fin (e + 1) × Fin n =>
      Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
        (X ij.2) (fun i => C (X (i, ij.2))) ij.1) :
        MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] _) =
      ((renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n))).toAlgHom := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, m⟩
    cases i using Fin.cases <;> simp [firstGroupVars]
  exact DFunLike.congr_fun h g

theorem ChartFirstGroupPrime.proof (h₁ : IncIdealPrime.Statement) (h₂ : IncIdealBelow.Statement) :
    ChartFirstGroupPrime.Statement := by
  intro F _ n e I f p _ hI hf
  obtain ⟨hf0, hspan⟩ := isChowForm_iff.mp hf
  have hfp : Prime f := by
    have := h₁ F n (e + 1) I hI.isPrime hI.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hf0).mp this
  set Φ := (renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n)) with hΦ
  have hg : Prime (firstGroup f) := by
    rw [firstGroup_eq]
    exact (MulEquiv.prime_iff Φ).mpr hfp

  have hC : ∀ s : MvPolynomial (Fin e × Fin n) F,
      (C s : MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)) =
        Φ (rename (fun im : Fin e × Fin n => ((im.1.succ, im.2) : Fin (e + 1) × Fin n)) s) := by
    intro s
    have hcomp : (firstGroupVars e n) ∘ (fun im : Fin e × Fin n => ((im.1.succ, im.2) : Fin (e + 1) × Fin n)) =
        Sum.inr := by
      funext im
      rfl
    rw [hΦ, AlgEquiv.trans_apply, renameEquiv_apply, rename_rename, hcomp]
    have := DFunLike.congr_fun (sumAlgEquiv_comp_rename_inr F (Fin n) (Fin e × Fin n)) s
    simp only [AlgHom.coe_comp, Function.comp_apply] at this
    exact (this.trans (by rw [IsScalarTower.coe_toAlgHom', algebraMap_eq])).symm
  have hdisj : Disjoint ((p.primeCompl.map (C : MvPolynomial (Fin e × Fin n) F →+*
      MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)) : Submonoid _) : Set _)
      ((Ideal.span {firstGroup f} : Ideal (MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))) :
        Set (MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))) := by
    rw [Set.disjoint_left]
    intro y hy hmem
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hy
    rw [SetLike.mem_coe, Ideal.mem_span_singleton, hC, firstGroup_eq, map_dvd_iff] at hmem
    have hvan := (hf.2 _).mpr hmem
    have hsI : s ∈ incIdeal I e := by
      rw [mem_incIdeal_iff]
      rintro v ⟨x, hx0, hxI, hxv⟩
      have := hvan (fun ij => Fin.cases (motive := fun _ => AlgebraicClosure F) 0 (fun i => v (i, ij.2)) ij.1)
        ⟨x, hx0, hxI, fun i => by
          cases i using Fin.cases with
          | zero => simp
          | succ i => simpa using hxv i⟩
      rwa [aeval_rename] at this
    rw [h₂ F n e I f hI hf, Ideal.mem_bot] at hsI
    exact hs (hsI ▸ p.zero_mem)
  letI := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := MvPolynomial (Fin e × Fin n) F)
    (S := Localization.AtPrime p)
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint
    (p.primeCompl.map (C : MvPolynomial (Fin e × Fin n) F →+*
      MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)))
    (MvPolynomial (Fin n) (Localization.AtPrime p)) _
    ((Ideal.span_singleton_prime hg.ne_zero).mpr hg) hdisj
  rw [Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def] at hprime
  refine (Ideal.span_singleton_prime fun h => hg.ne_zero ?_).mp hprime
  exact map_injective _ (IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors)
    (h.trans (map_zero _).symm)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartChoice

variable {F : Type} [Field F] {n e : ℕ}

def shiftVar (e n : ℕ) : Fin e × Fin n → Fin (e + 1) × Fin n := fun jm => (jm.1.succ, jm.2)

def splitFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) :=
  aeval fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
    (X ij.2) (fun j => C (X (j, ij.2))) ij.1

def joinFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) →+* MvPolynomial (Fin (e + 1) × Fin n) F :=
  eval₂Hom (rename (shiftVar e n)).toRingHom (fun m => X (0, m))

theorem joinFirst_splitFirst (p : MvPolynomial (Fin (e + 1) × Fin n) F) :
    joinFirst F e n (splitFirst F e n p) = p := by
  have h : (joinFirst F e n).comp (splitFirst F e n).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [joinFirst, splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [joinFirst, splitFirst, shiftVar]
  exact RingHom.congr_fun h p

theorem joinFirst_C (a : MvPolynomial (Fin e × Fin n) F) :
    joinFirst F e n (C a) = rename (shiftVar e n) a := by
  simp [joinFirst]

theorem specFirst_rename_shiftVar (q : MvPolynomial (Fin e × Fin n) F) :
    specFirst (rename (shiftVar e n) q) 0 = q := by
  unfold specFirst
  rw [bind₁_rename]
  have : (specFirstVar (0 : Fin n → F) ∘ shiftVar e n) = X := by
    funext jm
    simp [specFirstVar, shiftVar]
  rw [this, bind₁_X_left]
  rfl

theorem specFirst_zero_of_isMultiHomog {δ : ℕ} (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) F}
    (hf : IsMultiHomog δ f) : specFirst f 0 = 0 := by
  classical
  unfold specFirst
  conv_lhs => rw [f.as_sum]

  rw [map_sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [bind₁_monomial]
  obtain ⟨i, hi, h0⟩ : ∃ i ∈ s.support, i.1 = 0 := by
    by_contra hno
    push Not at hno
    have hw := congrFun (hf (mem_support_iff.mp hs)) 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at hw
    have : ∑ c ∈ s.support, (s c • groupWeight (e + 1) n c) 0 = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      simp [groupWeight, Ne.symm (hno c hc)]
    omega
  rw [Finset.prod_eq_zero hi, mul_zero]
  obtain ⟨a, m⟩ := i
  simp only at h0
  subst h0
  simp [specFirstVar, zero_pow (Finsupp.mem_support_iff.mp hi)]

theorem eval_map_splitFirst (J : Ideal (MvPolynomial (Fin e × Fin n) F)) (t : Fin n → F)
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    eval (fun m => Ideal.Quotient.mk J (C (t m))) (map (Ideal.Quotient.mk J) (splitFirst F e n f)) =
      Ideal.Quotient.mk J (specFirst f t) := by
  rw [eval_map]
  have h : (eval₂Hom (Ideal.Quotient.mk J) (fun m => Ideal.Quotient.mk J (C (t m)))).comp
      (splitFirst F e n).toRingHom = (Ideal.Quotient.mk J).comp (bind₁ (specFirstVar t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [splitFirst, specFirstVar, bind₁_X_right]
  exact RingHom.congr_fun h f

end ChartChoice


open ChartChoice in
theorem ChartChoice.proof (h₁ : IncIdealPrime.Statement) (h₂ : ChowFormMultiHomog.Statement) :
    ChartChoice.Statement := by
  intro F _ _ n e I f q hI hf hq
  classical
  obtain ⟨hf0, hspan⟩ := isChowForm_iff.mp hf
  have hfp : Prime f := by
    have := h₁ F n (e + 1) I hI.isPrime hI.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hf0).mp this
  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (e + 1) I f hI hf

  have hndvd : ¬ rename (shiftVar e n) q ∣ f := by
    rintro ⟨g, hg⟩
    rcases hfp.2.2 (rename (shiftVar e n) q) g (hg ▸ dvd_refl f) with ⟨h, hh⟩ | ⟨h, hh⟩
    · have := congrArg (fun p => specFirst p 0) hh
      rw [specFirst_rename_shiftVar] at this
      unfold specFirst at this
      rw [map_mul] at this
      have h0 : specFirst f 0 = 0 := specFirst_zero_of_isMultiHomog hδ hhom
      unfold specFirst at h0
      rw [h0, zero_mul] at this
      exact hq.ne_zero this
    · have hunit : IsUnit (rename (shiftVar e n) q) := by
        refine isUnit_iff_exists_inv.mpr ⟨h, ?_⟩
        apply mul_left_cancel₀ hf0
        calc f * (rename (shiftVar e n) q * h) = rename (shiftVar e n) q * (f * h) := by ring
          _ = f * 1 := by rw [← hh, ← hg, mul_one]
      have := hunit.map (bind₁ (specFirstVar (0 : Fin n → F)))
      have h' : bind₁ (specFirstVar (0 : Fin n → F)) (rename (shiftVar e n) q) = q :=
        specFirst_rename_shiftVar q
      rw [h'] at this
      exact hq.not_isUnit this
  set J : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q} with hJ
  have : J.IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  set P := map (Ideal.Quotient.mk J) (splitFirst F e n f) with hP
  have hP0 : P ≠ 0 := by
    intro h0
    have hmem : splitFirst F e n f ∈ RingHom.ker (map (σ := Fin n) (Ideal.Quotient.mk J)) := by
      rw [RingHom.mem_ker]; exact h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, hJ, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at hmem
    apply hndvd
    have := map_dvd (joinFirst F e n) hmem
    rwa [joinFirst_splitFirst, joinFirst_C] at this
  have : CharZero (MvPolynomial (Fin e × Fin n) F ⧸ J) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  by_contra hall
  push Not at hall
  apply hP0
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun _ => (Finset.range (P.totalDegree + 1)).image (fun k : ℕ => (k : MvPolynomial (Fin e × Fin n) F ⧸ J)))
    (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact Nat.lt_succ_of_le (degreeOf_le_totalDegree P i)
  · choose k _ hk using fun i => Finset.mem_image.mp (hx i)
    have hx' : x = fun m => Ideal.Quotient.mk J (C ((k m : ℕ) : F)) := by
      funext m
      rw [← hk m]
      simp
    rw [hx', hP, eval_map_splitFirst]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hall _))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

private def shiftGroup {e n : ℕ} (ij : Fin e × Fin n) : Fin (e + 1) × Fin n := (ij.1.succ, ij.2)

private theorem shiftGroup_injective {e n : ℕ} : Function.Injective (shiftGroup (e := e) (n := n)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [shiftGroup, Prod.mk.injEq, Fin.succ_inj] at h
  rw [h.1, h.2]

private def killFirst {F : Type*} [Field F] {e n : ℕ} (ij : Fin (e + 1) × Fin n) :
    MvPolynomial (Fin (e + 1) × Fin n) F :=
  if ij.1 = 0 then 0 else X ij

private theorem aeval_killFirst_eq_zero {F : Type*} [Field F] {e n δ : ℕ} (hδ : 1 ≤ δ)
    {f : MvPolynomial (Fin (e + 1) × Fin n) F} (hf : IsMultiHomog δ f) :
    aeval (killFirst (F := F)) f = 0 := by
  classical
  rw [aeval_def, eval₂_eq]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := congrFun (hf (mem_support_iff.mp hd)) 0
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at hw
  have hne : (∑ c ∈ d.support, (d c • groupWeight (e + 1) n c) 0) ≠ 0 := by rw [hw]; omega
  obtain ⟨ij, hij, hij0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have h1 : ij.1 = 0 := by
    by_contra h
    apply hij0
    simp [groupWeight, Ne.symm h]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hij ?_)
  rw [killFirst, if_pos h1]
  exact zero_pow (Finsupp.mem_support_iff.mp hij)

theorem IncIdealBelow.proof (h₁ : ChowFormMultiHomog.Statement) : IncIdealBelow.Statement := by
  intro F _ n e I f hI hf
  classical
  obtain ⟨δ, hδ, hmh⟩ := h₁ F n (e + 1) I f hI hf
  rw [eq_bot_iff]
  intro g hg
  rw [Ideal.mem_bot]
  set g' : MvPolynomial (Fin (e + 1) × Fin n) F := rename shiftGroup g with hg'
  have hvan : ∀ v ∈ incidence I (e + 1), aeval v g' = 0 := by
    rintro v ⟨x, hx0, hxI, hxv⟩
    rw [hg', aeval_rename]
    exact (mem_incIdeal_iff.mp hg) (v ∘ shiftGroup) ⟨x, hx0, hxI, fun i => hxv i.succ⟩
  obtain ⟨h, hh⟩ := (hf.2 g').mp hvan
  have hfix : aeval (killFirst (F := F)) g' = g' := by
    rw [hg', aeval_rename]
    conv_rhs => rw [← aeval_X_left_apply (rename shiftGroup g), aeval_rename]
    congr 1
  have hzero : g' = 0 := by
    rw [← hfix, hh, map_mul, aeval_killFirst_eq_zero hδ hmh, zero_mul]
  exact rename_injective _ shiftGroup_injective (by rw [← hg', hzero, map_zero])

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem SpecFirstMemIncIdeal.proof : SpecFirstMemIncIdeal.Statement := by
  intro F _ n e I W f t hf hIW ht
  rw [mem_incIdeal_iff]
  rintro v ⟨x, hx0, hxW, hv⟩
  let w : Fin (e + 1) × Fin n → AlgebraicClosure F := fun ij =>
    Fin.cases (motive := fun _ => AlgebraicClosure F) (algebraMap F (AlgebraicClosure F) (t ij.2))
      (fun i => v (i, ij.2)) ij.1
  have hw : w ∈ incidence I (e + 1) := by
    refine ⟨x, hx0, fun g hg => hxW g (hIW hg), fun i => ?_⟩
    induction i using Fin.cases with
    | zero =>
      have h := hxW _ ht

      simpa [w, linForm, map_sum, aeval_X, aeval_C] using h
    | succ i => simpa [w] using hv i
  have hfw : aeval w f = 0 := (hf.2 f).mpr dvd_rfl w hw
  have hev : aeval v (specFirst f t) = aeval w f := by
    rw [specFirst, aeval_bind₁]
    congr 2
    funext ij
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases with
    | zero => simp [specFirstVar, w]
    | succ i => simp [specFirstVar, w]
  rw [hev, hfw]

end GroundTheory.Heights₂.Heights
end
