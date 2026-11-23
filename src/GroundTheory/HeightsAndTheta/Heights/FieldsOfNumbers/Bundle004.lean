module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherReduction
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Order.Filter.AtTopBot.Map
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

theorem NoetherIntegralClosureFinite.proof : NoetherIntegralClosureFinite.Statement := by
  intro k A _ _ _ _ _ K _ _ _ L _ _ _ _ _
  refine finite_integralClosure_of_forall_mvPolynomial k A K L fun s L' _ _ _ _ _ => ?_
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hp' | rfl
  · have : Fact p.Prime := ⟨hp'⟩
    exact finite_integralClosure_mvPolynomial_of_charP k p s L'
  · have : CharZero k := CharP.charP_to_charZero k
    exact finite_integralClosure_mvPolynomial_of_charZero k s L'

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def extendAddHom {K K' : Type} (j : K ↪ K') : (K → ℕ) →+ (K' → ℕ) where
  toFun x := Function.extend j x 0
  map_zero' := by
    funext k'
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      simp [j.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  map_add' x y := by
    funext k'
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      simp [j.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]

theorem weight_mapDomain_blockWeight {K K' : Type} [DecidableEq K] [DecidableEq K'] (j : K ↪ K')
    (ι : K → Type) (ι' : K' → Type) (g : (Σ k, ι k) → (Σ k', ι' k'))
    (hg : ∀ v, (g v).1 = j v.1) (u : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain g u) =
      Function.extend j (Finsupp.weight (blockWeight ι) u) 0 := by
  have key : (Finsupp.weight (R := ℕ) (blockWeight ι')).comp
        (Finsupp.mapDomain.addMonoidHom (M := ℕ) g) =
      (extendAddHom j).comp (Finsupp.weight (R := ℕ) (blockWeight ι)) := by
    ext v
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.singleAddHom_apply,
      Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, Finsupp.weight_single,
      one_smul]
    show blockWeight ι' (g v) _ = Function.extend j (blockWeight ι v) 0 _
    rename_i k'
    simp only [blockWeight, hg v]
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      rw [j.injective.extend_apply]
      by_cases hav : a = v.1
      · subst hav; simp
      · rw [Pi.single_eq_of_ne (fun e => hav (j.injective e)), Pi.single_eq_of_ne hav]
    · rw [Function.extend_apply' _ _ _ h, Pi.single_eq_of_ne (fun e => h ⟨v.1, e.symm⟩)]
      rfl
  exact DFunLike.congr_fun key u

theorem RenameMultiHomog.proof : RenameMultiHomog.Statement.{u} := by
  intro R _ K K' _ _ j ι ι' g hg f d hf e he
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero g f e he
  rw [weight_mapDomain_blockWeight j ι ι' g hg u, hf hu]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

namespace RenameIntNum

variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)

def precompIso : (K₂ → ℤ) ≃o (K₁ → ℤ) where
  toFun m := m ∘ e
  invFun m := m ∘ e.symm
  left_inv m := by funext k; simp
  right_inv m := by funext k; simp
  map_rel_iff' := by
    intro a b
    constructor
    · intro h k
      simpa using h (e.symm k)
    · intro h k
      exact h (e k)

theorem eventualValue_comp (g : (K₁ → ℤ) → ℤ) :
    eventualValue (fun m : K₂ → ℤ => g (m ∘ e)) = eventualValue g := by
  have key : ∀ c, (∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c) ↔
      ∀ᶠ m in atTop, g m = c := by
    intro c
    rw [← (precompIso e).map_atTop, Filter.eventually_map]
    rfl
  unfold eventualValue
  by_cases hg : ∃ c, ∀ᶠ m in atTop, g m = c
  · have hf : ∃ c, ∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c :=
      hg.imp fun c hc => (key c).2 hc
    rw [dite_eq_left hf, dite_eq_left hg]
    obtain ⟨m, h1, h2⟩ := (((key _).1 hf.choose_spec).and hg.choose_spec).exists
    exact h1.symm.trans h2
  · have hf : ¬ ∃ c, ∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c :=
      fun ⟨c, hc⟩ => hg ⟨c, (key c).1 hc⟩
    rw [dite_eq_right hf, dite_eq_right hg]

theorem mixedDiff_comp {n : ℕ} (bs : Fin n → K₂ → ℤ) (h : (K₁ → ℤ) → ℤ) :
    mixedDiff bs (fun m => h (m ∘ e)) = fun m => mixedDiff (fun i => bs i ∘ e) h (m ∘ e) := by
  unfold mixedDiff
  have hl : List.ofFn (fun i => bs i ∘ e) = (List.ofFn bs).map (fun b => b ∘ e) := by
    rw [List.map_ofFn]
    rfl
  rw [hl]
  generalize List.ofFn bs = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldr_cons, List.map_cons, List.foldr_cons, ih]
    rfl

theorem proof (h : RenameHilbFn.Statement.{u}) : RenameIntNum.Statement.{u} := by
  intro F _ S K' _ _ κ ι' E σ hσ P n bs
  have hH : hilbFn (P.comap (rename σ)) = fun m => hilbFn P (m ∘ E.symm) :=
    funext fun m => h F S K' κ ι' E σ hσ P m
  unfold intNum
  rw [hH, mixedDiff_comp E.symm bs (hilbFn P),
    eventualValue_comp E.symm (mixedDiff (fun i => bs i ∘ E.symm) (hilbFn P))]

end RenameIntNum

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace RenameMultiProjPrime

variable {S K' : Type} [DecidableEq S] [DecidableEq K'] {κ : S → Type} {ι' : K' → Type} (E : S ≃ K')
  (σ : (Σ s, κ s) ≃ (Σ k', ι' k'))

theorem weight_mapDomain (hσ : ∀ v, (σ v).1 = E v.1) (d : (Σ s, κ s) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain σ d) =
      Finsupp.weight (blockWeight κ) d ∘ E.symm := by
  induction d using Finsupp.induction_linear with
  | zero => funext k; simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), hf, hg]
    rfl
  | single v n =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
    funext k
    simp only [blockWeight, hσ, Function.comp_apply, Pi.smul_apply, Pi.single_apply,
      Equiv.symm_apply_eq, smul_eq_mul]

theorem rename_weightedHomogeneousComponent {R : Type u} [CommRing R]
    (hσ : ∀ v, (σ v).1 = E v.1) (b : S → ℕ) (f : MRing κ R) :
    rename σ (weightedHomogeneousComponent (blockWeight κ) b f) =
      weightedHomogeneousComponent (blockWeight ι') (b ∘ E.symm) (rename σ f) := by
  classical
  ext m
  have hm : m = Finsupp.mapDomain σ (Finsupp.mapDomain σ.symm m) := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  rw [hm, coeff_weightedHomogeneousComponent, coeff_rename_mapDomain _ σ.injective,
    coeff_rename_mapDomain _ σ.injective, coeff_weightedHomogeneousComponent,
    weight_mapDomain E σ hσ]
  have hiff : Finsupp.weight (blockWeight κ) (Finsupp.mapDomain σ.symm m) ∘ E.symm = b ∘ E.symm ↔
      Finsupp.weight (blockWeight κ) (Finsupp.mapDomain σ.symm m) = b :=
    E.symm.surjective.injective_comp_right.eq_iff
  simp only [hiff]

end RenameMultiProjPrime

theorem RenameMultiProjPrime.proof : RenameMultiProjPrime.Statement.{u} := by
  intro R _ S K' _ _ κ ι' E σ hσ P hP
  refine ⟨?_, ?_, ?_⟩
  · have := hP.isPrime
    exact Ideal.comap_isPrime _ _
  · intro f hf b
    rw [Ideal.mem_comap] at hf ⊢
    rw [RenameMultiProjPrime.rename_weightedHomogeneousComponent (R := R) E σ hσ b f]
    exact hP.multiHomog _ hf _
  · intro s
    obtain ⟨i', hi'⟩ := hP.relevant (E s)
    obtain ⟨⟨s', i⟩, hv⟩ : ∃ v, σ v = ⟨E s, i'⟩ := σ.surjective _
    have hs : s' = s := E.injective (by simpa [hv] using (hσ ⟨s', i⟩).symm)
    subst hs
    refine ⟨i, ?_⟩
    rw [Ideal.mem_comap, rename_X, hv]
    exact hi'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem divCycle_support_finite {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (f : MRing ι F) :
    (Function.support (divCycle P f)).Finite := by
  apply (Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι F)
    (P ⊔ Ideal.span {f})).subset
  intro W hW
  by_contra h
  apply hW
  simp only [divCycle]
  rw [dite_eq_right (fun h' => h h'.1)]

theorem cycEval_ratDiv {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (N : Ideal (MRing ι F) → ℤ) (P : Ideal (MRing ι F))
    (f g : MRing ι F) :
    cycEval N (ratDiv P f g) = cycEval N (divCycle P f) - cycEval N (divCycle P g) := by
  simp only [cycEval, ratDiv, sub_mul]
  apply finsum_sub_distrib
  · exact (divCycle_support_finite P f).subset (Function.support_mul_subset_left _ _)
  · exact (divCycle_support_finite P g).subset (Function.support_mul_subset_left _ _)

theorem CutRational.proof (h1 : CutRegular.Statement.{u}) (h2 : IntNumAdd.Statement.{u}) :
    CutRational.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hn bf bg f g hf hg hfP hgP bs
  have hadd := h2 F K ι P hP.multiHomog hP.relevant (n + 1) hn
    (Fin.snoc (α := fun _ => K → ℤ) bs 0) (Fin.last n)
    (fun k => (bf k : ℤ) - bg k) (fun k => (bg k : ℤ))
  simp only [Fin.update_snoc_last] at hadd
  have hsum : ((fun k => (bf k : ℤ) - bg k) + fun k => (bg k : ℤ)) = fun k => (bf k : ℤ) := by
    funext k; simp
  rw [hsum, h1 F K ι P hP n hn bf f hf hfP bs, h1 F K ι P hP n hn bg g hg hgP bs] at hadd
  rw [cycEval_ratDiv]
  linarith

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section SplitRelDeg

variable {F : Type u} [Field F] {K K' : Type} (j : K ↪ K') {ι' : K' → Type}
  (P' : Ideal (MRing ι' F)) [P'.IsPrime]

theorem contractFracMap_mk (f : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') f)) =
      algebraMap _ _ (Ideal.Quotient.mk P' (rename (blockIncl j ι') f)) := by
  simp [contractFracMap, contractQuot]
  rfl


end SplitRelDeg

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

theorem isMultiHomog_prod_pow {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*}
    [CommRing R] (i : ∀ k, ι k) (n : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι R) ^ n k) n := by
  have h := IsWeightedHomogeneous.prod (R := R) Finset.univ
    (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ n k) (fun k => n k • blockWeight ι ⟨k, i k⟩)
    (w := blockWeight ι) (fun k _ => (isWeightedHomogeneous_X R _ _).pow _)
  have hs : (∑ k, n k • blockWeight ι ⟨k, i k⟩) = n := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [hs] at h
  exact h

theorem prod_pow_not_mem {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) [hP : P.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι R) ∉ P) (n : K → ℕ) :
    (∏ k, (X ⟨k, i k⟩ : MRing ι R) ^ n k) ∉ P := by
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hi k (hP.mem_of_pow_mem _ hk)

theorem ExistsForm.proof : ExistsForm.Statement := by
  intro F _ K _ _ ι _ P hP b
  have := hP.isPrime
  choose i hi using hP.relevant
  refine ⟨fun k => (b k).toNat, fun k => (-b k).toNat,
    ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ (b k).toNat, ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ (-b k).toNat,
    isMultiHomog_prod_pow i _, isMultiHomog_prod_pow i _, prod_pow_not_mem P i hi _,
    prod_pow_not_mem P i hi _, ?_⟩
  funext k
  simp only
  omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem PFContracted.natCast_lt_withBotWithTop {a b : ℕ} (h : a < b) :
    ((a : ℕ) : WithBot (WithTop ℤ)) < ((b : ℕ) : WithBot (WithTop ℤ)) := by
  show (((a : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < (((b : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by exact_mod_cast h))

theorem PFContracted.blockIncl_injective_of_embedding {K K' : Type} (j : K ↪ K') (ι' : K' → Type) :
    Function.Injective (blockIncl j ι') := by
  rintro ⟨k₁, x₁⟩ ⟨k₂, x₂⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  cases j.injective h1
  cases eq_of_heq h2
  rfl

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

section

variable {K : Type*}

theorem diffStep_comm (a b : K → ℤ) (h : (K → ℤ) → ℤ) :
    diffStep a (diffStep b h) = diffStep b (diffStep a h) := by
  funext m
  simp only [diffStep, sub_sub, add_comm a b]
  ring

instance diffStep_leftCommutative :
    LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ) :=
  ⟨diffStep_comm⟩

theorem mixedDiff_comp_perm {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n))
    (h : (K → ℤ) → ℤ) : mixedDiff (bs ∘ σ) h = mixedDiff bs h := by
  unfold mixedDiff
  exact (σ.ofFn_comp_perm bs).foldr_eq h

end

theorem IntNumSymm.proof : IntNumSymm.Statement := by
  intro F _ K _ _ ι _ I n bs σ
  unfold intNum
  rw [mixedDiff_comp_perm]

end GroundTheory.Heights₂.Heights.FieldNumbers
end
