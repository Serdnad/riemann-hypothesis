module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle003
public import Mathlib.Algebra.MvPolynomial.Funext
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle004
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartIncDomain.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime I → linForm t ∉ I →
      IsDomain (ChartInc I t e) ∧ RingHom.ker (chartX I t e) = I ⊔ Ideal.span {linForm t - 1}

def ChartKernel.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime I → linForm t ∉ I →
      RingHom.ker (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) = incIdeal I e

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem LocalizationPrimeDVR.proof : LocalizationPrimeDVR.Statement := by
  intro R _ _ _ _ q p _ hq hp
  set O := Localization.AtPrime p
  have hmax : maximalIdeal O = Ideal.span {algebraMap R O q} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p O,
      congrArg (Ideal.map (algebraMap R O)) hp, Ideal.map_span, Set.image_singleton]
  have hprin : (maximalIdeal O).IsPrincipal := ⟨⟨algebraMap R O q, hmax⟩⟩
  have hPID : IsPrincipalIdealRing O :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain O).out 5 1).mp hprin
  have hq0 : algebraMap R O q ≠ 0 := by
    intro h
    have hinj : Function.Injective (algebraMap R O) :=
      IsLocalization.injective O (p.primeCompl_le_nonZeroDivisors)
    exact hq.ne_zero (hinj (by rw [h, map_zero]))
  have hne : maximalIdeal O ≠ ⊥ := by
    rw [hmax, Ne, Ideal.span_singleton_eq_bot]
    exact hq0
  exact { hPID with not_a_field' := hne }

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Choice

variable {F : Type} [Field F] {k n : ℕ}

def specFirstSplit (ij : Fin (k + 1) × Fin n) : (Fin k × Fin n) ⊕ Fin n :=
  Fin.cases (motive := fun _ => (Fin k × Fin n) ⊕ Fin n) (Sum.inr ij.2) (fun i => Sum.inl (i, ij.2)) ij.1

theorem specFirstSplit_injective : Function.Injective (specFirstSplit (k := k) (n := n)) := by
  rintro ⟨i, m⟩ ⟨j, m'⟩ h
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp_all [specFirstSplit]

theorem specFirst_eq_map_eval (g : MvPolynomial (Fin (k + 1) × Fin n) F) (t : Fin n → F) :
    specFirst g t = map (eval t) (sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit g)) := by
  have h : (bind₁ (specFirstVar t) : MvPolynomial (Fin (k + 1) × Fin n) F →ₐ[F] _).toRingHom =
      (map (eval t)).comp ((sumAlgEquiv F (Fin k × Fin n) (Fin n)).toRingHom.comp
        (rename specFirstSplit).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change bind₁ (specFirstVar t) (C a) =
        map (eval t) (sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit (C a)))
      rw [bind₁_C_right, rename_C, sumAlgEquiv_C_inl, map_C, eval_C]
    · rintro ⟨i, m⟩
      cases i using Fin.cases <;>
        simp [specFirstVar, specFirstSplit, sumAlgEquiv_X_inl, sumAlgEquiv_X_inr, bind₁_X_right]
  exact RingHom.congr_fun h g

theorem exists_specFirst_ne_zero [Infinite F] {f : MvPolynomial (Fin (k + 1) × Fin n) F} (hf : f ≠ 0) :
    ∃ t : Fin n → F, specFirst f t ≠ 0 := by
  set g := sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit f) with hg_def
  have hg : g ≠ 0 :=
    (map_ne_zero_iff _ (sumAlgEquiv F (Fin k × Fin n) (Fin n)).injective).mpr
      ((map_ne_zero_iff _ (rename_injective _ specFirstSplit_injective)).mpr hf)
  obtain ⟨β, hβ⟩ := ne_zero_iff.mp hg
  have ht : ∃ t : Fin n → F, eval t (AddMonoidAlgebra.coeff g β) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hβ (MvPolynomial.funext fun x => by simp [h x])
  obtain ⟨t, ht⟩ := ht
  refine ⟨t, fun h0 => ht ?_⟩
  have := congr_arg (AddMonoidAlgebra.coeff · β) h0
  simpa only [specFirst_eq_map_eval, ← hg_def, coeff_map, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] using this

end Choice

theorem det_mulLeft_ne_zero {O B : Type*} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [Algebra O B]
    {θ : B} (hθ : θ ≠ 0) : LinearMap.det (LinearMap.mulLeft O θ) ≠ 0 := by
  classical
  intro h
  by_cases H : ∃ s : Finset B, Nonempty (Module.Basis s O B)
  · obtain ⟨s, ⟨b⟩⟩ := H
    have : Module.Free O B := Module.Free.of_basis b
    have hker := LinearMap.bot_lt_ker_of_det_eq_zero h
    rw [bot_lt_iff_ne_bot, Ne, LinearMap.ker_eq_bot] at hker
    exact hker fun x y hxy => mul_left_cancel₀ hθ (by simpa using hxy)
  · simp [LinearMap.coe_det, H] at h

theorem SpecFirstNe.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₄ : ChartLocDomain.Statement) (h₅ : ChartNorm.Statement) : SpecFirstNe.Statement := by
  intro F _ _ n e I f u hI hf hu
  obtain ⟨t, ht⟩ := exists_specFirst_ne_zero hf.1
  have hlt : linForm t ∉ I := fun hmem => ht (by
    have hmem' := h₂ F n e I I f t hf le_rfl hmem
    rwa [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem')
  have htp : specFirst f t ∉ (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)) := by
    rwa [Ideal.mem_bot]
  obtain ⟨hdom, -, hθ⟩ := h₄ F n e I f t ⊥ hI hf hlt
  have hnorm := h₅ F n e I f t ⊥ hI hf (Or.inl rfl) htp u
  have ha : algebraMap _ (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
      (specFirst f t) ≠ 0 := fun h => ht
    (IsLocalization.injective (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
      (Ideal.primeCompl_le_nonZeroDivisors ⊥) (h.trans (map_zero _).symm))
  have hdet := det_mulLeft_ne_zero (O := Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
    (hθ u hu)
  intro h0
  rw [h0, map_zero] at hnorm
  exact mul_ne_zero ha hdet hnorm.symm

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem pderiv_aeval_eq_sum {F K : Type*} [CommRing F] [CommRing K] [Algebra F K]
    {σ τ : Type*} [Fintype σ] (ψ : σ → MvPolynomial τ K) (i : τ) (g : MvPolynomial σ F) :
    pderiv i (aeval ψ g) = ∑ j, aeval ψ (pderiv j g) * pderiv i (ψ j) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, map_add (f := _), add_mul,
      Finset.sum_add_distrib, pderiv_X, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    · refine Finset.sum_congr rfl fun b _ => by ring

theorem pderiv_genSubst {K : Type*} [CommRing K] {n k : ℕ} (ζ c : Fin n → K) (i : Fin k) (m : Fin n)
    (j : Fin k × Fin n) :
    pderiv (i, m) (genSubst ζ c j) =
      (if j = (i, m) then 1 else 0) - (if j.1 = i then C (ζ m) * C (c j.2) else 0) := by
  classical
  obtain ⟨j₁, j₂⟩ := j

  simp only [genSubst, map_sub, Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, zero_add,
  map_sum, pderiv_X, Pi.single_apply, mul_zero]
  by_cases h : j₁ = i
  · subst h
    simp [Prod.ext_iff, eq_comm, mul_comm]
  · simp [Prod.ext_iff, h]

theorem not_dvd_pderiv_of_degreeOf_pos {F σ : Type*} [Field F] [CharZero F] {g : MvPolynomial σ F}
    (hg : g ≠ 0) {i : σ} (hi : 0 < degreeOf i g) : ¬ g ∣ pderiv i g := by
  classical
  rintro ⟨q, hq⟩
  have hlt : degreeOf i (pderiv i g) < degreeOf i g := by
    rw [degreeOf_lt_iff hi]
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  have hne : pderiv i g ≠ 0 := by
    obtain ⟨s, hs, hsd⟩ := Finset.exists_mem_eq_sup g.support (support_nonempty.2 hg) (fun m => m i)
    rw [← degreeOf_eq_sup] at hsd
    have hle : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.2 (by omega)
    intro h0
    have := congrArg (AddMonoidAlgebra.coeff · (s - Finsupp.single i 1)) h0
    simp only [coeff_pderiv, AddMonoidAlgebra.coeff_zero, tsub_add_cancel_of_le hle] at this
    have hcs : AddMonoidAlgebra.coeff g s ≠ 0 := mem_support_iff.1 hs
    have hsi : (((s - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : F) + 1 ≠ 0 := by
      exact Nat.cast_add_one_ne_zero _
    exact mul_ne_zero hcs hsi this
  rw [hq, degreeOf_mul_eq hg (right_ne_zero_of_mul (hq ▸ hne))] at hlt
  omega

theorem ChowFormBirational.proof (h₁ : IncidenceGeneric.Statement)
    (h₂ : ChowFormMultiHomog.Statement) : ChowFormBirational.Statement := by
  intro F _ _ n k P g c hP hg hc
  have := hP.isPrime
  classical

  have hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h := by
    intro h
    rw [← hg.2 h, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hg0 : aeval (genSubst (genPt P) c) g = 0 :=
    (h₁ F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)

  have hA : ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) =
      C (genPt P m) * ∑ l, aeval (genSubst (genPt P) c) (pderiv (0, l) g) * C (c l) := by
    intro m
    have h := pderiv_aeval_eq_sum (genSubst (genPt P) c) (0, m) g
    rw [hg0, map_zero] at h
    simp only [pderiv_genSubst, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero] at h
    rw [eq_comm, sub_eq_zero] at h
    rw [h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (k + 1) P g hP hg
  obtain ⟨s, hs⟩ := support_nonempty.2 hg.1
  obtain ⟨l, hl⟩ : ∃ l, 0 < s (0, l) := by
    by_contra hcon
    push Not at hcon
    have hw := congrFun (hhom (mem_support_iff.1 hs)) 0
    have : (Finsupp.weight (groupWeight (k + 1) n) s) 0 = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      obtain ⟨x₁, x₂⟩ := x
      by_cases hx : x₁ = 0
      · subst hx; simp [Nat.le_zero.1 (hcon x₂)]
      · simp [groupWeight, hx]
    omega
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ :=
    ⟨_, hA⟩
  have hdeg : 0 < degreeOf (0, l) g := lt_of_lt_of_le hl (monomial_le_degreeOf _ hs)
  refine ⟨Pi.single l 1, ?_, fun m => ?_⟩
  · have hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) =
        pderiv (0, l) g := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hsum, hmem]
    exact not_dvd_pderiv_of_degreeOf_pos hg.1 hdeg

  · simp only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace ComponentOfIncIdeal

theorem ringKrullDim_quot_add_one_le {A : Type} [CommRing A] {P Q : Ideal A} [P.IsPrime]
    (hPQ : P ≤ Q) (hne : P ≠ Q) : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ P) := by
  obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hPQ hne)
  have hne' : Q.map (Ideal.Quotient.mk P) ≠ ⊥ := by
    intro h0
    have hx : Ideal.Quotient.mk P x ∈ Q.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ hxQ
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact hxP hx
  have h := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le _ hne'
  rwa [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ)] at h

theorem one_le_ringKrullDim_quot {F : Type} [Field F] {n : ℕ} {W : Ideal (MvPolynomial (Fin n) F)}
    (hW : IsProjPrime W) : (1 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ W) := by
  have hWp := hW.isPrime
  set m : Ideal (MvPolynomial (Fin n) F) := RingHom.ker (constantCoeff : MvPolynomial (Fin n) F →+* F)
  have hmp : m.IsPrime := RingHom.ker_isPrime _
  have hle : W ≤ m := by
    intro f hf
    rw [RingHom.mem_ker]
    by_contra h
    have h0 := hW.isHomog f hf 0
    rw [homogeneousComponent_zero] at h0
    have hc : AddMonoidAlgebra.coeff f 0 ≠ 0 := by rwa [← constantCoeff_eq]
    exact hWp.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit hc).map C))
  have hne : W ≠ m := by
    obtain ⟨j, hj⟩ := hW.isRelevant
    intro h
    exact hj (h ▸ (by simp [m] : (X j : MvPolynomial (Fin n) F) ∈ m))
  have h := ringKrullDim_quot_add_one_le hle hne
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ m) :=
    ringKrullDim_nonneg_of_nontrivial
  exact (le_add_of_nonneg_left h0).trans h

theorem exists_nat_of_bounds {x : WithBot ℕ∞} {e : ℕ} (h1 : 1 ≤ x) (h2 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ k : ℕ, x = (k : WithBot ℕ∞) ∧ 1 ≤ k ∧ k ≤ e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h1 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
        le_trans (le_add_of_nonneg_right zero_le_one) h2
      have h4 : (⊤ : ℕ∞) ≤ ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast h3
      exact absurd h4 (by simp)
    | coe k =>
      refine ⟨k, rfl, ?_, ?_⟩
      · exact_mod_cast h1
      · have : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h2
        have : k + 1 ≤ e + 1 := by exact_mod_cast this
        omega

end ComponentOfIncIdeal


open ComponentOfIncIdeal in
theorem ComponentOfIncIdeal.proof (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement)
    (h₃ : ConeDimComponent.Statement) : ComponentOfIncIdeal.Statement := by
  intro F _ n e I W u q hI hdim hu hW hle hq hinc
  have hWp := hW.isPrime
  have := hI.isPrime

  have hIW : I ≤ W := le_sup_left.trans hle
  have huW : linForm u ∈ W := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hIneW : I ≠ W := fun h => hu (h ▸ huW)
  have hup := ringKrullDim_quot_add_one_le hIW hIneW
  rw [hdim] at hup
  obtain ⟨k, hk, hk1, hke⟩ := exists_nat_of_bounds (one_le_ringKrullDim_quot hW) hup

  have hdimInc := h₁ F n e (k - 1) W hW (by rw [hk]; congr 2; omega)
  have hincp : (incIdeal W e).IsPrime := h₂ F n e W hWp hW.isRelevant
  have hS : ringKrullDim (MvPolynomial (Fin e × Fin n) F) = ((e * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_isField (Field.toIsField F)]
    simp [Nat.card_eq_fintype_card]
  have hsum := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F) (incIdeal W e)
  rw [hdimInc, hS] at hsum
  have hqle : (Ideal.span {q}).height ≤ 1 := Ideal.height_span_singleton_le_one hq.not_isUnit
  have hht : (incIdeal W e).height ≤ 1 := (Ideal.height_mono hinc).trans hqle
  obtain ⟨h, hh⟩ : ∃ h : ℕ, (incIdeal W e).height = h :=
    ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hht) |>.imp fun _ h => h.symm
  rw [hh] at hsum hht
  have hh1 : h ≤ 1 := by exact_mod_cast hht
  have hnat : h + (e * n - e + min e (k - 1)) = e * n := by
    have h5 : (((h + (e * n - e + min e (k - 1)) : ℕ) : ℕ∞) : WithBot ℕ∞) = (((e * n : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [Nat.cast_add, WithBot.coe_add]
      exact hsum
    exact_mod_cast WithBot.coe_inj.mp h5
  have hn : 1 ≤ n := by
    obtain ⟨j, _⟩ := hW.isRelevant
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => (h0 ▸ j).elim0
  have hen : e ≤ e * n := Nat.le_mul_of_pos_right e hn
  have hmin : min e (k - 1) = k - 1 := min_eq_right (by omega)
  rw [hmin] at hnat
  generalize e * n = N at hnat hen
  have hke' : k = e := by omega
  have hh' : h = 1 := by omega
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨W'', hmin'', hW''⟩ := Ideal.exists_minimalPrimes_le hle
    have hrel : IsRelevant W'' := by
      obtain ⟨j, hj⟩ := hW.isRelevant
      exact ⟨j, fun hj'' => hj (hW'' hj'')⟩
    have hdim'' := (h₃ F n e I W'' u hI hdim hu ⟨hmin'', hrel⟩).2
    by_cases heq : W'' = W
    · exact heq ▸ ⟨hmin'', hrel⟩
    · have := hmin''.1.1
      have hlt := ringKrullDim_quot_add_one_le hW'' heq
      rw [hdim'', hk, hke'] at hlt
      have : e + 1 ≤ e := by exact_mod_cast hlt
      omega
  ·
    by_contra hne
    have : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
    have : (Ideal.span {q}).FiniteHeight :=
      (Ideal.span {q}).finiteHeight_iff.mpr (Or.inr (ne_top_of_le_ne_top (by simp) hqle))
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hinc hne)
    rw [hh, hh'] at hlt
    exact absurd (hlt.trans_le hqle) (lt_irrefl _)

end GroundTheory.Heights₂.Heights
end
