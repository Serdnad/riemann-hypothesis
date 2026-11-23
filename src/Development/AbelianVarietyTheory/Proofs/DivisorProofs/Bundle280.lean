module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Mathlib.RingTheory.Ideal.Height
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.GenFibMap

variable {A A' A'' X X' X'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [CommRing X]
  [CommRing X'] [CommRing X''] [Algebra A X] [Algebra A' X'] [Algebra A'' X'']

theorem submonoid_le (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) :
    Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors A) ≤
      (Algebra.algebraMapSubmonoid (Localization.AtPrime P') (nonZeroDivisors A')).comap
        (Localization.localRingHom P P' χ hP) := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨φ a, hφ a ha, ?_⟩
  simp only [IsScalarTower.algebraMap_apply A X (Localization.AtPrime P),
    IsScalarTower.algebraMap_apply A' X' (Localization.AtPrime P'),
    Localization.localRingHom_to_map, hc]

def genFibMap (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) :
    GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P') :=
  IsLocalization.map (S := GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P))
    (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P')) (Localization.localRingHom P P' χ hP)
    (submonoid_le φ χ hc hφ P P' hP)

theorem genFibMap_comp_algebraMap (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) :
    (genFibMap φ χ hc hφ P P' hP).comp
        (algebraMap (Localization.AtPrime P) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P))) =
      (algebraMap (Localization.AtPrime P') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P'))).comp
        (Localization.localRingHom P P' χ hP) :=
  IsLocalization.map_comp _

theorem genFibMap_apply (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) (y : X) :
    genFibMap φ χ hc hφ P P' hP
        (algebraMap (Localization.AtPrime P) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P))
          (algebraMap X (Localization.AtPrime P) y)) =
      algebraMap (Localization.AtPrime P') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P'))
          (algebraMap X' (Localization.AtPrime P') (χ y)) := by
  rw [genFibMap, IsLocalization.map_eq, Localization.localRingHom_to_map]

theorem ext {C : Type} [CommRing C] (P : Ideal X) [P.IsPrime]
    {u v : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P) →+* C}
    (h : ∀ y : X, u (algebraMap (Localization.AtPrime P) _ (algebraMap X (Localization.AtPrime P) y)) =
      v (algebraMap (Localization.AtPrime P) _ (algebraMap X (Localization.AtPrime P) y))) : u = v := by
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors A))
  apply IsLocalization.ringHom_ext P.primeCompl
  exact RingHom.ext h

theorem genFibMap_comp (φ₁ : A →+* A') (χ₁ : X →+* X')
    (hc₁ : ∀ a, χ₁ (algebraMap A X a) = algebraMap A' X' (φ₁ a))
    (hφ₁ : ∀ a ∈ nonZeroDivisors A, φ₁ a ∈ nonZeroDivisors A')
    (φ₂ : A' →+* A'') (χ₂ : X' →+* X'')
    (hc₂ : ∀ a, χ₂ (algebraMap A' X' a) = algebraMap A'' X'' (φ₂ a))
    (hφ₂ : ∀ a ∈ nonZeroDivisors A', φ₂ a ∈ nonZeroDivisors A'')
    (φ₃ : A →+* A'') (χ₃ : X →+* X'')
    (hc₃ : ∀ a, χ₃ (algebraMap A X a) = algebraMap A'' X'' (φ₃ a))
    (hφ₃ : ∀ a ∈ nonZeroDivisors A, φ₃ a ∈ nonZeroDivisors A'')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (P'' : Ideal X'') [P''.IsPrime]
    (h₁ : P = P'.comap χ₁) (h₂ : P' = P''.comap χ₂) (h₃ : P = P''.comap χ₃)
    (hχ : ∀ y, χ₃ y = χ₂ (χ₁ y)) :
    (genFibMap φ₂ χ₂ hc₂ hφ₂ P' P'' h₂).comp (genFibMap φ₁ χ₁ hc₁ hφ₁ P P' h₁) =
      genFibMap φ₃ χ₃ hc₃ hφ₃ P P'' h₃ := by
  refine ext P (fun y => ?_)
  simp only [RingHom.comp_apply, genFibMap_apply, hχ]

theorem genFibMap_id (φ : A →+* A) (χ : X →+* X)
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A X (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A)
    (P : Ideal X) [P.IsPrime] (hP : P = P.comap χ) (hχ : ∀ y, χ y = y) :
    genFibMap φ χ hc hφ P P hP = RingHom.id _ := by
  refine ext P (fun y => ?_)
  simp only [RingHom.id_apply, genFibMap_apply, hχ]

end GlobalTheory.GenFibMap
end
end

section

open IsLocalRing Polynomial

namespace GlobalTheory

theorem genFib_colim_surj : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ b : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q), ∃ k x, g k x = b := by
  intro T _ _ ι _ _ 𝒜 hmono hunion E _ _ Q _ Ek _ _ e h he hh hsurj g hg b
  classical
  obtain ⟨⟨z, ⟨m, hm⟩⟩, hb0⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)) b
  obtain ⟨c, hc, hcm⟩ := hm
  subst hcm
  obtain ⟨⟨x, ⟨s, hs⟩⟩, hz0⟩ := IsLocalization.mk'_surjective Q.primeCompl z
  simp only at hb0 hz0
  subst hz0
  obtain ⟨k₁, y₁, hy₁⟩ := hsurj x
  obtain ⟨k₂, t₂, ht₂⟩ := hsurj s
  obtain ⟨k₃, hc₃⟩ := hunion c
  obtain ⟨k₁₂, h1, h2⟩ := directed_of (· ≤ ·) k₁ k₂
  obtain ⟨k, h12, h3⟩ := directed_of (· ≤ ·) k₁₂ k₃
  have hk1 : k₁ ≤ k := h1.trans h12
  have hk2 : k₂ ≤ k := h2.trans h12
  set y := h k₁ k hk1 y₁
  set t := h k₂ k hk2 t₂
  have hy : e k y = x := by rw [hh, hy₁]
  have ht : e k t = s := by rw [hh, ht₂]
  have htQ : t ∈ (Q.comap (e k)).primeCompl := by
    show t ∉ Q.comap (e k)
    rw [Ideal.mem_comap, ht]; exact hs
  set c' : 𝒜 k := ⟨c, hmono h3 hc₃⟩
  have hc' : c' ∈ nonZeroDivisors (𝒜 k) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    apply nonZeroDivisors.ne_zero hc
    have := congrArg (fun a : 𝒜 k => (a : T)) h0
    simpa [c'] using this
  set z' : (Localization.AtPrime (Q.comap (e k))) := IsLocalization.mk' (Localization.AtPrime (Q.comap (e k))) y ⟨t, htQ⟩
  set m' : (Localization.AtPrime (Q.comap (e k))) := algebraMap (𝒜 k) (Localization.AtPrime (Q.comap (e k))) c'
  have hm' : m' ∈ Algebra.algebraMapSubmonoid (Localization.AtPrime (Q.comap (e k))) (nonZeroDivisors (𝒜 k)) := ⟨c', hc', rfl⟩
  refine ⟨k, IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩, ?_⟩
  have hu1 : IsUnit (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c)) :=
    IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
      (⟨algebraMap T (Localization.AtPrime Q) c, c, hc, rfl⟩ : Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T))
  have hu2 : IsUnit (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s)) :=
    (IsLocalization.map_units (Localization.AtPrime Q) (⟨s, hs⟩ : Q.primeCompl)).map _
  have hgm : g k (algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) m') = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) := by
    have hm'e : m' = algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) (algebraMap (𝒜 k) (Ek k) c') :=
      IsScalarTower.algebraMap_apply (𝒜 k) (Ek k) (Localization.AtPrime (Q.comap (e k))) c'
    rw [hm'e, hg, he, ← IsScalarTower.algebraMap_apply]
    rfl
  have hgt : g k (algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) t)) =
      algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s) := by rw [hg, ht]
  have hgy : g k (algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
      algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) x) := by rw [hg, hy]
  have hz' : z' * algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) t = algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y :=
    IsLocalization.mk'_spec (Localization.AtPrime (Q.comap (e k))) y ⟨t, htQ⟩
  have hX : IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩ * algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) m' = algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' :=
    IsLocalization.mk'_spec (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩
  have hz : IsLocalization.mk' (Localization.AtPrime Q) x ⟨s, hs⟩ * algebraMap E (Localization.AtPrime Q) s = algebraMap E (Localization.AtPrime Q) x :=
    IsLocalization.mk'_spec (Localization.AtPrime Q) x ⟨s, hs⟩
  have hb : IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) x ⟨s, hs⟩)
      (⟨algebraMap T (Localization.AtPrime Q) c, c, hc, rfl⟩ : Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)) *
      algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) x ⟨s, hs⟩) :=
    IsLocalization.mk'_spec (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) _ _
  have e1 : b * (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) * algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s)) = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) x) := by
    rw [← hb0, ← mul_assoc, hb, ← map_mul, hz]
  have e2 : g k (IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩) * (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) * algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s)) = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) x) := by
    rw [← hgm, ← hgt, ← mul_assoc, ← map_mul, hX, ← map_mul, ← map_mul, hz', hgy]
  exact (hu1.mul hu2).mul_left_inj.mp (e2.trans e1.symm)

end GlobalTheory
end

section

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocAcyc

def genFibMap {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E] [Algebra T O]
    (ψ : E →ₐ[T] O) : GenFib T E →+* GenFib T O :=
  IsLocalization.map (M := Algebra.algebraMapSubmonoid E (nonZeroDivisors T))
    (T := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (GenFib T O) ψ.toRingHom (by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (ψ.commutes t).symm⟩)

theorem genFibMap_algebraMap {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E]
    [Algebra T O] (ψ : E →ₐ[T] O) (e : E) :
    genFibMap ψ (algebraMap E (GenFib T E) e) = algebraMap O (GenFib T O) (ψ e) := by
  simp [genFibMap, IsLocalization.map_eq]

theorem genFib_ringHom_ext {T E C : Type} [CommRing T] [CommRing E] [CommRing C] [Algebra T E]
    {f g : GenFib T E →+* C} (h : ∀ e : E, f (algebraMap E _ e) = g (algebraMap E _ e)) : f = g :=
  IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid E (nonZeroDivisors T))
    (RingHom.ext h)

end GlobalTheory.LocAcyc
end
end

section

open IsLocalRing Polynomial

namespace GlobalTheory

theorem genFib_colim_ker : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ k, Function.Injective (e k)) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ (f : ∀ k l, k ≤ l → GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l)))),
      (∀ k l (hkl : k ≤ l) (y : Ek k), f k l hkl (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime (Q.comap (e l)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l))))
          (algebraMap (Ek l) (Localization.AtPrime (Q.comap (e l))) (h k l hkl y))) →
    ∀ k (x : GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))), g k x = 0 →
      ∃ l, ∃ hkl : k ≤ l, f k l hkl x = 0 := by
  intro T _ _ ι _ _ 𝒜 hA hcov E _ _ Q _ Ek _ _ e h he hh heh hinj hsurj g hg f hf k x hx
  classical

  set L := Localization.AtPrime (Q.comap (e k)) with hL
  obtain ⟨⟨z, a'⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid L (nonZeroDivisors (𝒜 k))) x
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Q.comap (e k)).primeCompl z
  dsimp only at hx ⊢
  set G := GlobalTheory.LocAcyc.GenFib (𝒜 k) L
  set X := IsLocalization.mk' G (IsLocalization.mk' L y s) a' with hX
  set v : G := algebraMap L G (a' : L) * algebraMap L G (algebraMap (Ek k) L (s : Ek k)) with hv
  have hvu : IsUnit v := by
    refine (IsLocalization.map_units G a').mul ?_
    exact (IsLocalization.map_units L s).map _
  have hXv : X * v = algebraMap L G (algebraMap (Ek k) L y) := by
    rw [hv, ← mul_assoc, hX, IsLocalization.mk'_spec, ← map_mul, IsLocalization.mk'_spec]

  have hgy : g k (algebraMap L G (algebraMap (Ek k) L y)) = 0 := by
    rw [← hXv, map_mul, hx, zero_mul]
  rw [hg] at hgy

  obtain ⟨⟨m0, hm0⟩, hm0y⟩ := (IsLocalization.map_eq_zero_iff
    (Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)) _ _).1 hgy
  obtain ⟨t, ht, rfl⟩ := Submonoid.mem_map.1 hm0
  simp only at hm0y
  rw [IsScalarTower.algebraMap_apply T E (Localization.AtPrime Q), ← map_mul] at hm0y
  obtain ⟨⟨u, hu⟩, huy⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ _).1 hm0y
  simp only at huy
  obtain ⟨m, u', rfl⟩ := hsurj u
  obtain ⟨m', htm'⟩ := hcov t
  obtain ⟨l1, hkl1, hml1⟩ := directed_of (· ≤ ·) k m
  obtain ⟨l, hl1, hm'l⟩ := directed_of (· ≤ ·) l1 m'
  have hkl : k ≤ l := hkl1.trans hl1
  have hml : m ≤ l := hml1.trans hl1
  let c : 𝒜 l := ⟨t, hA hm'l htm'⟩
  have hc0 : c ∈ nonZeroDivisors (𝒜 l) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    have : (t : T) = 0 := congrArg Subtype.val h0
    exact nonZeroDivisors.ne_zero ht this
  have hprod : h m l hml u' * (algebraMap (𝒜 l) (Ek l) c * h k l hkl y) = 0 := by
    apply hinj l
    rw [map_mul, map_mul, heh, heh, he, map_zero]
    simpa [mul_assoc] using huy
  have hu'' : h m l hml u' ∈ (Q.comap (e l)).primeCompl := by
    change e l (h m l hml u') ∉ Q
    rw [heh]; exact hu
  set Ll := Localization.AtPrime (Q.comap (e l))
  have h1 : algebraMap (Ek l) Ll (algebraMap (𝒜 l) (Ek l) c * h k l hkl y) = 0 := by
    have := congrArg (algebraMap (Ek l) Ll) hprod
    rw [map_mul, map_zero] at this
    exact ((IsLocalization.map_units Ll ⟨_, hu''⟩).mul_right_eq_zero).1 this
  have h2 : algebraMap Ll (GlobalTheory.LocAcyc.GenFib (𝒜 l) Ll) (algebraMap (Ek l) Ll (h k l hkl y)) = 0 := by
    have hcm : algebraMap (𝒜 l) Ll c ∈ Algebra.algebraMapSubmonoid Ll (nonZeroDivisors (𝒜 l)) :=
      Submonoid.mem_map.2 ⟨c, hc0, rfl⟩
    have := congrArg (algebraMap Ll (GlobalTheory.LocAcyc.GenFib (𝒜 l) Ll)) h1
    rw [map_mul, map_zero, ← IsScalarTower.algebraMap_apply, map_mul] at this
    exact ((IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib (𝒜 l) Ll) ⟨_, hcm⟩).mul_right_eq_zero).1 this
  refine ⟨l, hkl, ?_⟩
  have hfy : f k l hkl (algebraMap L G (algebraMap (Ek k) L y)) = 0 := by
    rw [hf]; exact h2
  have := congrArg (f k l hkl) hXv
  rw [map_mul, hfy] at this
  exact ((hvu.map (f k l hkl)).mul_left_eq_zero).1 this

end GlobalTheory
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.GenFibBaseChange

theorem exists_genFib_maps : ∀ (T O A A₁ R R₁ : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R] [CommRing R₁] [Algebra A₁ R₁]
    (j : A →+* A₁) (i₁ : A₁ →+* T), Function.Injective j → Function.Injective i₁ →
    ∀ (jA : R →+* O) (jA₁ : R₁ →+* O) (γ : R →+* R₁)
      (ψA : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib T O),
    jA₁.comp (algebraMap A₁ R₁) = (algebraMap T O).comp i₁ →
    γ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp j →
    jA₁.comp γ = jA →
    ψA.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∃ (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O)
      (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
      ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ ∧
      ψA₁.comp β = ψA ∧
      β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := by
  intro T O A A₁ R R₁ _ _ _ _ _ _ _ _ _ _ _ _ j i₁ hj hi₁ jA jA₁ γ ψA h1 h2 h3 h4
  have hu1 : ∀ y : Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁),
      IsUnit (((algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁) y) := by
    rintro ⟨y, a, ha, rfl⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hi : i₁ a ∈ nonZeroDivisors T := mem_nonZeroDivisors_of_ne_zero (fun h => ha0 (hi₁ (by simpa using h)))
    have e : jA₁ (algebraMap A₁ R₁ a) = algebraMap T O (i₁ a) := by
      simpa using congrArg (fun f => f a) h1
    simp only [RingHom.coe_comp, Function.comp_apply, e]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib T O)
      (⟨algebraMap T O (i₁ a), ⟨i₁ a, hi, rfl⟩⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  have hu2 : ∀ y : Algebra.algebraMapSubmonoid R (nonZeroDivisors A),
      IsUnit (((algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ) y) := by
    rintro ⟨y, a, ha, rfl⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hi : j a ∈ nonZeroDivisors A₁ := mem_nonZeroDivisors_of_ne_zero (fun h => ha0 (hj (by simpa using h)))
    have e : γ (algebraMap A R a) = algebraMap A₁ R₁ (j a) := by
      simpa using congrArg (fun f => f a) h2
    simp only [RingHom.coe_comp, Function.comp_apply, e]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A₁ R₁)
      (⟨algebraMap A₁ R₁ (j a), ⟨j a, hi, rfl⟩⟩ : Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
  let ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)) hu1
  let β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁ :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) hu2
  have k1 : ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
      (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ := IsLocalization.lift_comp hu1
  have k3 : β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := IsLocalization.lift_comp hu2
  refine ⟨ψA₁, β, k1, ?_, k3⟩
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  rw [RingHom.comp_assoc, k3, ← RingHom.comp_assoc, k1, RingHom.comp_assoc, h3, h4]

end GlobalTheory.GenFibBaseChange
end

section

open IsLocalRing

noncomputable section

namespace GlobalTheory.LocAcyc

def IsZModTorsor (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) : Prop :=
  Module.Finite B D ∧ Module.Projective B D ∧ Module.FaithfullyFlat B D ∧
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)))

theorem torsorsTrivial_iff (B : Type) [CommRing B] (q : ℕ) :
    TorsorsTrivial B q ↔ ∀ (D : Type) [CommRing D] [Algebra B D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)), IsZModTorsor B D q act →
        Nonempty (D →ₐ[B] B) := by
  constructor
  · intro h D _ _ act hD
    exact h D hD.1 hD.2.1 hD.2.2.1 act hD.2.2.2
  · intro h D _ _ h1 h2 h3 act h4
    exact h D act ⟨h1, h2, h3, h4⟩

def LocPiecesEtale (R S : Type) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
    (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧
    ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A)
      (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)

end GlobalTheory.LocAcyc
end
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginNoeth

def baseHom (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : R →+* D :=
  (algebraMap (GlobalTheory.LocAcyc.GenFib A R) D).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R))

def closure (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : Subring D :=
  letI := (baseHom A R D).toAlgebra
  (integralClosure R D).toSubring

def closureAlg (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : Algebra R (closure A R D) :=
  ((baseHom A R D).codRestrict (closure A R D) (fun r => by
    letI := (baseHom A R D).toAlgebra
    exact isIntegral_algebraMap (R := R) (A := D) (x := r))).toAlgebra

def ClosureFiniteEtale (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : Prop :=
  letI := closureAlg A R D
  Module.Finite R (closure A R D) ∧ Algebra.Etale R (closure A R D) ∧ Nontrivial (closure A R D)

def Good (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (ρ : R →+* A) : Prop :=
  letI := closureAlg A R D
  (∀ (P : Ideal R) [P.IsPrime], (P.comap (algebraMap A R)).height ≤ 1 →
      Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] closure A R D)) ∧
    ∃ s : closure A R D →+* FractionRing A,
      s.comp (algebraMap R (closure A R D)) = (algebraMap A (FractionRing A)).comp ρ

end GlobalTheory.KeyOriginNoeth
end
end
