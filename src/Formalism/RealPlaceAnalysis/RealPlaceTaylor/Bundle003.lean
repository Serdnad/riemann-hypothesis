module

public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle070
public import Formalism.RealPlaceAnalysis.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

section

open scoped TensorProduct
open Finset

noncomputable section

namespace Formalism.REAL

theorem casComm_casK_comm {A : Type} [Ring A] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → A) (hE : GlRel E) (c d : Fin n) (hcd : ε c = ε d) :
    CasK ε E * E c d = E c d * CasK ε E :=
  _root_.UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm ε E hE c d hcd

theorem casimir_central_holds : CasCentral := by
  intro A _ n ε E hE
  refine ⟨fun c d => ?_, fun c d h => casComm_casK_comm ε E hE c d h⟩
  have h := casComm_casK_comm (fun _ => true) E hE c d rfl
  have hC : CasK (fun _ : Fin n => true) E = Cas E := by simp [CasK, Cas]
  rwa [hC] at h

end Formalism.REAL
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.REAL

section general

variable {σ : Type*}

lemma fischerInner_eq_sum_of_subset (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockF f g = ∑ m ∈ s, f.coeff m * star (g.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset h
  intro m _ hm
  simp [MvPolynomial.notMem_support_iff.mp hm]

lemma fischerInner_add_left (f1 f2 g : MvPolynomial σ ℂ) :
    fockF (f1 + f2) g = fockF f1 g + fockF f2 g := by
  classical
  rw [fischerInner_eq_sum_of_subset _ _ (f1.support ∪ f2.support) MvPolynomial.support_add,
    fischerInner_eq_sum_of_subset f1 g (f1.support ∪ f2.support) Finset.subset_union_left,
    fischerInner_eq_sum_of_subset f2 g (f1.support ∪ f2.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [MvPolynomial.coeff_add]; ring

lemma fischerInner_add_right (f g1 g2 : MvPolynomial σ ℂ) :
    fockF f (g1 + g2) = fockF f g1 + fockF f g2 := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [MvPolynomial.coeff_add, star_add]; ring

def fischerInnerLeftHom (g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →+ ℂ :=
  AddMonoidHom.mk' (fun f => fockF f g) (fun a b => fischerInner_add_left a b g)

def fischerInnerRightHom (f : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →+ ℂ :=
  AddMonoidHom.mk' (fun g => fockF f g) (fun a b => fischerInner_add_right f a b)

lemma fischerInner_sum_left {ι : Type*} (s : Finset ι) (h : ι → MvPolynomial σ ℂ) (g : MvPolynomial σ ℂ) :
    fockF (∑ a ∈ s, h a) g = ∑ a ∈ s, fockF (h a) g :=
  map_sum (fischerInnerLeftHom g) h s

lemma fischerInner_sum_right {ι : Type*} (s : Finset ι) (f : MvPolynomial σ ℂ) (h : ι → MvPolynomial σ ℂ) :
    fockF f (∑ a ∈ s, h a) = ∑ a ∈ s, fockF f (h a) :=
  map_sum (fischerInnerRightHom f) h s

lemma fischerInner_eq_star (f g : MvPolynomial σ ℂ) : fockF f g = star (fockF g f) := by
  classical
  rw [fischerInner_eq_sum_of_subset f g (f.support ∪ g.support) Finset.subset_union_left,
    fischerInner_eq_sum_of_subset g f (f.support ∪ g.support) Finset.subset_union_right, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', star_star, star_natCast]; ring

lemma fischerInner_monomial_left (u : σ →₀ ℕ) (c : ℂ) (g : MvPolynomial σ ℂ) :
    fockF (monomial u c) g = c * star (g.coeff u) * ((∏ k ∈ u.support, (u k).factorial : ℕ) : ℂ) := by
  classical
  rw [fischerInner_eq_sum_of_subset _ _ {u} support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    if_pos rfl]

lemma prod_factorial_support_sub_single [DecidableEq σ] (u : σ →₀ ℕ) (v : σ) (hv : u v ≠ 0) :
    (∏ k ∈ u.support, (u k).factorial) =
      u v * ∏ k ∈ (u - Finsupp.single v 1 : σ →₀ ℕ).support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial := by
  have hsub : (u - Finsupp.single v 1 : σ →₀ ℕ).support ⊆ u.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro h0; apply hk; simp [Finsupp.tsub_apply, h0]
  have e : ∏ k ∈ (u - Finsupp.single v 1 : σ →₀ ℕ).support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial =
      ∏ k ∈ u.support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial :=
    Finset.prod_subset hsub (fun k _ hk => by rw [Finsupp.notMem_support_iff.mp hk]; rfl)
  rw [e]
  have hmem : v ∈ u.support := Finsupp.mem_support_iff.mpr hv
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem]
  have h2 : ∏ k ∈ u.support.erase v, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial =
      ∏ k ∈ u.support.erase v, (u k).factorial := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k ≠ v := Finset.ne_of_mem_erase hk
    simp [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm hk']
  rw [h2, ← mul_assoc]
  congr 1
  simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
  exact (Nat.mul_factorial_pred hv).symm

lemma fischerInner_pderiv_left [DecidableEq σ] (v : σ) (f g : MvPolynomial σ ℂ) :
    fockF (pderiv v f) g = fockF f (X v * g) := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [pderiv_monomial, fischerInner_monomial_left, fischerInner_monomial_left, coeff_X_mul']
    by_cases hv : u v = 0
    · have : v ∉ u.support := Finsupp.notMem_support_iff.mpr hv
      simp [hv, this]
    · have : v ∈ u.support := Finsupp.mem_support_iff.mpr hv
      rw [if_pos this, prod_factorial_support_sub_single u v hv]
      push_cast; ring
  | add p q hp hq => rw [map_add (f := _), fischerInner_add_left, fischerInner_add_left, hp, hq]

lemma fischerInner_X_mul_left [DecidableEq σ] (v : σ) (f g : MvPolynomial σ ℂ) :
    fockF (X v * f) g = fockF f (pderiv v g) := by
  rw [fischerInner_eq_star, ← fischerInner_pderiv_left, ← fischerInner_eq_star]

end general

variable {M n' : ℕ}

end Formalism.REAL
end
end

section

open Finset

noncomputable section

namespace Formalism.REAL

def TrPow_m {n : ℕ} (l : Fin n → ℂ) : ℕ → Fin n → ℂ
  | 0 => fun _ => 1
  | k + 1 => fun a => l a * TrPow_m l k a - ∑ b ∈ univ.filter (fun b => a < b), TrPow_m l k b

lemma TrPow_m_zero {n : ℕ} (l : Fin n → ℂ) (a : Fin n) : TrPow_m l 0 a = 1 := rfl

lemma TrPow_m_succ {n : ℕ} (l : Fin n → ℂ) (k : ℕ) (a : Fin n) :
    TrPow_m l (k + 1) a = l a * TrPow_m l k a - ∑ b ∈ univ.filter (fun b => a < b), TrPow_m l k b :=
  rfl

lemma TrPow_diag (h : HWDiag) {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) (hE : GlRel E)
    (hv : IsHW E ν v) : ∀ (k : ℕ) (a : Fin n), epow E k a a v = TrPow_m (lsh ν) k a • v := by
  intro k
  induction k with
  | zero => intro a; simp [epow, TrPow_m_zero]
  | succ k ih =>
    intro a
    rw [h V n E ν v hE hv k a, TrPow_m_succ, ih a]
    simp only [ih]
    rw [← Finset.sum_smul, sub_smul, mul_smul]

end Formalism.REAL
end
end

section

open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

section KT2Gen
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}

theorem mem_compactSpan (x : V) : x ∈ kSpan ε F x := by
  exact Submodule.mem_sInf.2 fun S hS => hS.1

theorem compactSpan_le {x : V} {S : Submodule ℂ V} (hx : x ∈ S) (hS : KStable ε F S) :
    kSpan ε F x ≤ S := sInf_le ⟨hx, hS⟩

theorem isCompactInvariant_compactSpan (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  rw [kSpan, Submodule.mem_sInf] at hy ⊢
  intro S hS
  exact hS.2 a b hab y (hy S hS)

theorem isWeightVector_apply (hrel : KRel ε F) {ν : Fin n → ℝ} {v : V}
    (hv : IsWeight F ν v) (a b : Fin n) (hab : ε a = ε b) :
    IsWeight F (ν + root a b) (F a b v) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ V => T v) (hrel c c a b rfl hab)
  have e1 : (if c = a then F c b else 0) v = (if c = a then (1 : ℂ) else 0) • F a b v := by
    split_ifs with h1
    · subst h1
      simp
    · simp
  have e2 : (if b = c then F a c else 0) v = (if c = b then (1 : ℂ) else 0) • F a b v := by
    by_cases h2 : c = b
    · subst h2
      simp
    · simp [h2, Ne.symm h2]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv c, map_smul, e1, e2] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, ← sub_smul, ← add_smul]
  congr 1
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> push_cast <;> ring

end KT2Gen

theorem eigenvalue_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {F : Fin n → Fin n → Module.End ℂ V} (hunit : KUnit ε F)
    {v : V} (hv : v ≠ 0) (a : Fin n) {c : ℂ} (hc : F a a v = c • v) : ((c.re : ℝ) : ℂ) = c := by
  have h := hunit a a rfl v v
  rw [hc, inner_smul_left, inner_smul_right] at h
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv
  exact Complex.conj_eq_iff_re.1 (mul_right_cancel₀ hvv h)

theorem kHiUniq_of (hl : KLow) (_hw : KWtOrth) (ho : KOrth) : KHiUniq := by
  intro V _ _ n ε F μ ν x y hrel hunit hx hyx hy
  by_cases hμν : ν = μ
  · right
    refine ⟨hμν, ?_⟩
    obtain ⟨hspan, huniq⟩ := hl V n ε F μ x hrel hx
    exact huniq y (hspan ▸ hyx) (hμν ▸ hy.1)
  · left
    have h0 := ho V n ε F μ ν x y hrel hunit hx hy (Ne.symm hμν) y hyx y (mem_compactSpan y)
    exact inner_self_eq_zero.1 h0

theorem kIrr_of (he : KHiExist) (hu : KHiUniq) : KIrr := by
  intro V _ _ n ε F μ x hfd hrel hunit hx S hS hSst
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  right
  haveI := hfd
  have hfdS : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hS
  obtain ⟨y, hyS, hy0, ν, hy⟩ := he V n ε F S hfdS hrel hunit hSst h0
  rcases hu V n ε F μ ν x y hrel hunit hx (hS hyS) hy with h | ⟨-, c, hc⟩
  · exact absurd h hy0
  · have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hy0 hc
    have hxS : x ∈ S := by
      have h1 : c⁻¹ • y ∈ S := S.smul_mem _ hyS
      rwa [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h1
    exact le_antisymm hS (compactSpan_le hxS hSst)

theorem weighted_sum_rootVector_shift {n : ℕ} (ν : Fin n → ℝ) (a b : Fin n) :
    (∑ i : Fin n, -((i : ℕ) : ℝ) * (ν + root a b) i) =
      (∑ i : Fin n, -((i : ℕ) : ℝ) * ν i) + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  simp only [root, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

theorem highestWeightExists_holds : KHiExist := by
  intro V _ _ n ε F S hfd hrel hunit hst hne
  haveI := hfd
  have hcomm : ∀ a b : Fin n, F a a * F b b = F b b * F a a := by
    intro a b
    have h := hrel a a b b rfl rfl
    by_cases hab : a = b
    · subst hab
      rfl
    · simpa [hab, Ne.symm hab, sub_eq_zero] using h
  have main : ∀ s : Finset (Fin n), ∃ W : Submodule ℂ V, W ≤ S ∧ W ≠ ⊥ ∧
      (∀ a, ∀ w ∈ W, F a a w ∈ W) ∧ ∃ lam : Fin n → ℂ, ∀ a ∈ s, ∀ w ∈ W, F a a w = lam a • w := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨S, le_rfl, hne, fun a w hw => hst a a rfl w hw, 0, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨W, hWS, hW0, hWst, lam, hlam⟩ := ih
      haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW0
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((F a a).restrict (hWst a))
      obtain ⟨⟨v, hvW⟩, hv⟩ := hc.exists_hasEigenvector
      have hker : ∀ y, y ∈ LinearMap.ker (F a a - c • 1) ↔ F a a y = c • y := by
        intro y
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          sub_eq_zero]
      have hvker : F a a v = c • v := by
        have h1 := congrArg Subtype.val hv.apply_eq_smul
        simpa using h1
      refine ⟨W ⊓ LinearMap.ker (F a a - c • 1), inf_le_left.trans hWS, ?_, ?_, Function.update lam a c, ?_⟩
      · intro h
        have hvmem : v ∈ W ⊓ LinearMap.ker (F a a - c • 1) := ⟨hvW, (hker v).2 hvker⟩
        rw [h] at hvmem
        exact hv.2 (Subtype.ext (by simpa using (Submodule.mem_bot ℂ).1 hvmem))
      · intro b w hw
        refine ⟨hWst b w hw.1, (hker _).2 ?_⟩
        have h1 : F a a w = c • w := (hker w).1 hw.2
        have h2 := congrArg (fun T : Module.End ℂ V => T w) (hcomm a b)
        simp only [Module.End.mul_apply] at h2
        rw [h2, h1, map_smul]
      · intro b hb w hw
        rcases Finset.mem_insert.1 hb with rfl | hb'
        · rw [Function.update_self]
          exact (hker w).1 hw.2
        · rw [Function.update_of_ne (by rintro rfl; exact ha hb')]
          exact hlam b hb' w hw.1
  obtain ⟨W, hWS, hW0, -, lam, hlam⟩ := main Finset.univ
  obtain ⟨v0, hv0W, hv00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hw0 : IsWeight F (fun a => (lam a).re) v0 := fun a => by
    rw [eigenvalue_real hunit hv00 a (hlam a (Finset.mem_univ a) v0 hv0W)]
    exact hlam a (Finset.mem_univ a) v0 hv0W
  have hstab : ∀ a, ∀ y ∈ S, F a a y ∈ S := fun a => hst a a rfl
  have hfinW : {ν : Fin n → ℝ | ∃ v ∈ S, v ≠ 0 ∧ IsWeight F ν v}.Finite := by
    refine (Set.Finite.pi (t := fun a => {r : ℝ | Module.End.HasEigenvalue ((F a a).restrict (hstab a)) (r : ℂ)})
      (fun a => ?_)).subset ?_
    · exact (Module.End.finite_hasEigenvalue _).preimage (fun _ _ _ _ h => Complex.ofReal_injective h)
    · rintro ν ⟨v, hvS, hv0, hvw⟩
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
      intro a
      apply Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvS⟩)
      refine ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        apply Subtype.ext
        simp [hvw a]
      · intro h
        apply hv0
        simpa using congrArg Subtype.val h
  obtain ⟨ν, ⟨v, hvS, hv0, hvw⟩, hmax⟩ := Set.exists_max_image _
    (fun ν : Fin n → ℝ => ∑ i : Fin n, -((i : ℕ) : ℝ) * ν i) hfinW ⟨_, v0, hWS hv0W, hv00, hw0⟩
  refine ⟨v, hvS, hv0, ν, hvw, fun a b hab hεab => ?_⟩
  by_contra hne'
  have hmem : ν + root a b ∈ {ν : Fin n → ℝ | ∃ v ∈ S, v ≠ 0 ∧ IsWeight F ν v} :=
    ⟨F a b v, hst a b hεab v hvS, hne', isWeightVector_apply hrel hvw a b hεab⟩
  have h1 := hmax _ hmem
  rw [weighted_sum_rootVector_shift] at h1
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

end Formalism.REAL
end
end
