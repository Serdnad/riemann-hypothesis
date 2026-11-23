module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001

@[expose] public section

section

open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.HomInj

theorem aeval_mul_hom {σ R A : Type} [CommRing R] [CommRing A] [Algebra R A] {P : MvPolynomial σ R} {q : ℕ} (hP : P.IsHomogeneous q)
    (c : A) (z : σ → A) : aeval (fun i => c * z i) P = c ^ q * aeval z P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd := hP (mem_support_iff.mp hm)
  simp only [aeval_monomial, mul_pow]
  rw [Finsupp.prod_mul, ← hd]
  have : (m.prod fun _ k => c ^ k) = c ^ (Finsupp.weight 1 m) := by
    simp [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum]
  rw [this]; ring

def dehom (D : ℕ) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial (Fin D) ℤ :=
  aeval (Fin.cons 1 X)

theorem aeval_dehom {A : Type} [CommRing A] [Algebra ℤ A] {D : ℕ} (w : Fin D → A) (P : MvPolynomial (Fin (D + 1)) ℤ) :
    aeval w (dehom D P) = aeval (Fin.cons 1 w : Fin (D + 1) → A) P := by
  rw [dehom, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem dehom_eq_zero {D q : ℕ} {P : MvPolynomial (Fin (D + 1)) ℤ} (hP : P.IsHomogeneous q)
    (h : dehom D P = 0) : P = 0 := by
  let R := MvPolynomial (Fin (D + 1)) ℤ
  let F := FractionRing R
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  set c : F := algebraMap R F (X 0) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Ne, ← map_zero (algebraMap R F)]
    exact fun e => X_ne_zero (R := ℤ) (0 : Fin (D + 1)) (hinj e)
  let z : Fin (D + 1) → F := fun i => algebraMap R F (X i) / c
  have hz : (fun i => algebraMap R F (X i)) = fun i => c * z i := by
    funext i; exact (mul_div_cancel₀ _ hc0).symm
  have hz0 : z = Fin.cons 1 (fun j => z j.succ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · show algebraMap R F (X 0) / c = 1
      exact div_self hc0
    · simp
  have key : algebraMap R F P = c ^ q * aeval z P := by
    have e1 : algebraMap R F P = aeval (fun i => algebraMap R F (X i)) P := by
      rw [← Function.comp_def (algebraMap R F) X, aeval_algebraMap_apply, aeval_X_left_apply]
    rw [e1, hz]
    exact aeval_mul_hom hP c z
  have hzP : aeval z P = 0 := by
    have e2 := aeval_dehom (fun j => z j.succ) P
    rw [h, map_zero] at e2
    rw [hz0]; exact e2.symm
  apply hinj
  rw [key, hzP, mul_zero, map_zero]

end GlobalTheory.HSAmp.HomInj

namespace GlobalTheory.HSAmp


open GlobalTheory.HSAmp.HomInj in
theorem homogComb_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) →
    AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K →
    ∀ (ι : Type) [Fintype ι] (g : ι → K), LinearIndependent (ratF x) g → ∀ (q : ℕ)
    (T : ι → MvPolynomial (Fin (D + 1)) ℤ), (∀ i, (T i).IsHomogeneous q) → ∑ i, aeval x (T i) * g i = 0 → T = 0 := by
  intro K _ _ D x hx hind _ ι _ g hg q T hT hsum
  let y : Fin (D + 1) → K := fun j => x j / x 0
  have hy : ∀ j, y j ∈ ratF x := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [y, div_self (hx 0)]; exact (ratF x).one_mem
    · exact Subfield.subset_closure ⟨j, rfl⟩
  let y' : Fin (D + 1) → ratF x := fun j => ⟨y j, hy j⟩
  have hxy : x = fun j => x 0 * y j := by
    funext j; exact (mul_div_cancel₀ _ (hx 0)).symm
  have hval : ∀ i, aeval y (T i) = ((aeval y' (T i) : ratF x) : K) := by
    intro i
    show _ = algebraMap (ratF x) K _
    rw [← aeval_algebraMap_apply]
    rfl
  have h1 : ∀ i, aeval x (T i) = x 0 ^ q * aeval y (T i) := by
    intro i
    rw [← aeval_mul_hom (hT i) (x 0) y]
    exact congrArg (fun v => aeval v (T i)) hxy
  have hsum' : ∑ i, aeval y' (T i) • g i = 0 := by
    have hq : x 0 ^ q ≠ 0 := pow_ne_zero _ (hx 0)
    have : x 0 ^ q * ∑ i, aeval y' (T i) • g i = 0 := by
      rw [Finset.mul_sum, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1, hval, Subfield.smul_def, smul_eq_mul]; ring
    exact (mul_eq_zero.mp this).resolve_left hq
  have h0 : ∀ i, aeval y (T i) = 0 := by
    intro i
    rw [hval, Fintype.linearIndependent_iff.1 hg _ hsum' i]; rfl
  have hy0 : y = Fin.cons 1 (fun j : Fin D => x j.succ / x 0) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [y, div_self (hx 0)]
    · simp [y]
  funext i
  apply dehom_eq_zero (hT i)
  apply (algebraicIndependent_iff_injective_aeval.1 hind)
  rw [aeval_dehom, ← hy0, h0, map_zero]

end GlobalTheory.HSAmp
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem etTower_coords_algebraicIndependent {K L : Type} [Field K] [Field L] (cK : ℂ →+* K)
    (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) :
    IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
    Function.Injective (MvPolynomial.eval₂Hom ι τ) →
    (letI := cL.toAlgebra; AlgebraicIndependent ℂ
      (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  intro h hx hinj
  letI := cL.toAlgebra
  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let φ : MvPolynomial (Fin n) ℂ →+* R := MvPolynomial.eval₂Hom c0 x
  have hφinj : Function.Injective φ := by
    have hxK : Function.Injective (MvPolynomial.eval₂Hom cK (fun i => (x i : K))) := by
      letI := cK.toAlgebra
      have h1 := hx.1
      rw [algebraicIndependent_iff_injective_aeval] at h1
      exact h1
    have hcomp : R.subtype.comp φ = MvPolynomial.eval₂Hom cK (fun i => (x i : K)) := by
      ext <;> simp [φ, c0]
    intro a b e
    apply hxK
    rw [← hcomp, RingHom.comp_apply, RingHom.comp_apply, e]
  have key : (T.subtype.comp ((MvPolynomial.eval₂Hom ι τ).comp ((MvPolynomial.map φ).comp
        (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n)).toRingEquiv.toRingHom)))
        = (MvPolynomial.aeval (Sum.elim (fun i => (τ i : L)) (fun i => (ι (x i) : L)))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have := h.const a
      simp [φ, c0, MvPolynomial.sumAlgEquiv_C_inl]
      exact this
    · rintro (i | j) <;> simp [φ, MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.sumAlgEquiv_X_inr]
  have hy : Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)) ∘ finSumFinEquiv
      = Sum.elim (fun i => (τ i : L)) (fun i => (ι (x i) : L)) := by
    ext (i | j) <;> simp
  rw [← algebraicIndependent_equiv finSumFinEquiv, hy, algebraicIndependent_iff_injective_aeval,
    injective_iff_map_eq_zero]
  intro P hP
  have hP' : T.subtype.comp ((MvPolynomial.eval₂Hom ι τ).comp ((MvPolynomial.map φ).comp
        (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n)).toRingEquiv.toRingHom)) P = 0 := by
    rw [key]; exact hP
  have h1 : MvPolynomial.eval₂Hom ι τ (MvPolynomial.map φ (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n) P)) = 0 :=
    Subtype.ext hP'
  have h2 := (injective_iff_map_eq_zero _).1 hinj _ h1
  have h3 := (injective_iff_map_eq_zero _).1 (MvPolynomial.map_injective φ hφinj) _ h2
  exact (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n)).map_eq_zero_iff.1 h3

end GlobalTheory.FieldPair
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.ValAdd

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem ratVal_add' {σ : k →+* ℂ} {y : CxPts p σ} {f g : X.functionField} (hf : RegAt (under y) f)
    (hg : RegAt (under y) g) : ratVal (f + g) y = ratVal f y + ratVal g y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨W, hW, b, rfl⟩ := hg.exists_fnOf
  have hy : y ∈ ptsIn p σ (U ⊓ W) := mem_ptsIn.2 ⟨hU, hW⟩
  rw [← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)),
    ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_add,
    ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_add]

theorem val_add (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) {f g : X.functionField}
    (hf : f ∈ P.H a b) (hg : g ∈ P.H a b) : val P a b σ y (f + g) = val P a b σ y f + val P a b σ y g := by
  have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
  have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
  have e : P.loc a b (f + g) (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) =
      P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) +
        P.loc a b g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]; ring
  rw [val, val, val, e, ratVal_add' (hf _ _ _ hi hj) (hg _ _ _ hi hj), add_mul]

end GlobalTheory.HSAmp.ValAdd


open GlobalTheory.HSAmp.ValAdd in
theorem GlobalTheory.HSAmp.val_additive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ ℓ : P.H a b →+ ℂ, ∀ f : P.H a b, ℓ f = val P a b σ y f := by
  intro k _ X _ p P a b σ y
  refine ⟨{ toFun := fun f => val P a b σ y f, map_zero' := ?_, map_add' := fun f g => val_add P a b σ y f.2 g.2 }, fun _ => rfl⟩
  have := val_add P a b σ y (zero_mem (P.H a b)) (zero_mem (P.H a b))
  simp only [add_zero] at this
  simpa using this
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem exists_locModel_at_point :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.EssFiniteType ℂ A] (ε : A →ₐ[ℂ] ℂ),
      ∃ T : Subring (FractionRing A), IsLocModel (algebraMap ℂ (FractionRing A)) T ∧
        RatRes (algebraMap ℂ (FractionRing A)) T ∧
        ∀ a : A, algebraMap A (FractionRing A) a ∈ T ∧
          (ε a = 0 → NonUnit T (algebraMap A (FractionRing A) a)) := by
  intro A _ _ _ _ ε
  let K := FractionRing A
  let P : Ideal A := RingHom.ker (ε : A →+* ℂ)
  haveI : P.IsPrime := RingHom.ker_isPrime _
  have hle : P.primeCompl ≤ nonZeroDivisors A := P.primeCompl_le_nonZeroDivisors
  let B : Subalgebra A K := Localization.subalgebra.ofField K P.primeCompl hle
  haveI hB : IsLocalization P.primeCompl B := Localization.subalgebra.isLocalization_ofField K _ hle
  let b : A →+* B := algebraMap A B
  have hu : ∀ y : P.primeCompl, IsUnit ((ε : A →+* ℂ) y) := fun y => by
    refine isUnit_iff_ne_zero.2 fun h => y.2 ?_
    exact RingHom.mem_ker.2 h
  let ψ : B →+* ℂ := IsLocalization.lift hu
  have hψ : ∀ x, ψ (b x) = ε x := IsLocalization.lift_eq hu
  have hcK : ∀ z : ℂ, algebraMap ℂ K z = algebraMap A K (algebraMap ℂ A z) :=
    fun z => IsScalarTower.algebraMap_apply ℂ A K z
  have hc : ∀ z : ℂ, algebraMap ℂ K z ∈ B.toSubring := fun z => by
    rw [hcK]; exact B.algebraMap_mem _
  have hψc : ∀ z : ℂ, ψ ⟨algebraMap ℂ K z, hc z⟩ = z := fun z => by
    have : (⟨algebraMap ℂ K z, hc z⟩ : B) = b (algebraMap ℂ A z) := Subtype.ext (hcK z)
    rw [this, hψ]; exact ε.commutes z
  have key : ∀ x : B, ψ x = 0 → NonUnit B.toSubring (x : K) := fun x hx => by
    refine (nonUnit_iff (R := B.toSubring) x).2 fun h => ?_
    have := h.map ψ
    rw [hx] at this
    exact not_isUnit_zero this
  refine ⟨B.toSubring, ⟨hc, IsLocalization.AtPrime.isLocalRing B P, ?_, ?_⟩, ?_, fun a => ?_⟩
  · have e : (algebraMap ℂ K).codRestrict B.toSubring hc = b.comp (algebraMap ℂ A) := by
      ext z; exact hcK z
    rw [e]
    refine RingHom.EssFiniteType.comp ?_ ?_
    · exact RingHom.essFiniteType_algebraMap.2 (inferInstance : Algebra.EssFiniteType ℂ A)
    · exact (RingHom.essFiniteType_algebraMap (R := A) (S := B)).2
        (Algebra.EssFiniteType.of_isLocalization B P.primeCompl)
  · intro f
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) f
    have hy' : algebraMap A K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    exact ⟨_, B.algebraMap_mem x, _, B.algebraMap_mem y, hy', div_mul_cancel₀ _ hy'⟩
  · intro r hr
    refine ⟨ψ ⟨r, hr⟩, key (⟨r, hr⟩ - ⟨algebraMap ℂ K (ψ ⟨r, hr⟩), hc _⟩) ?_⟩
    rw [ψ.map_sub, hψc, sub_self]
  · refine ⟨B.algebraMap_mem a, fun ha => key (b a) ?_⟩
    rw [hψ, ha]

end GlobalTheory.FieldPair
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.PolyPlaceEt

variable {k K : Type} [Field k] [Field K] {c : k →+* K}

def inclRing {Q : Subring K} {P : Place c} (h : P.Contains Q) : Q →+* P.ring :=
  Q.subtype.codRestrict P.ring fun q => h q q.2

theorem isUnit_of_ord_zero (P : Place c) (b : P.ring) (hb : (b : K) ≠ 0)
    (h : P.ord (b : K) = 0) : IsUnit b := by
  have h1 : (b : K)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hb)).1 (by rw [P.ord_inv, h]; rfl)
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ hb))

theorem isLocalization_ring {Q : Subring K} {P : Place c} (h : P.IsPrimeOf Q) :
    letI := (inclRing h.1).toAlgebra
    IsLocalization ((IsUnit.submonoid P.ring).comap (inclRing h.1)) P.ring := by
  letI := (inclRing h.1).toAlgebra
  rw [isLocalization_iff]
  refine ⟨fun y => y.2, fun f => ?_, fun {a b} e => ⟨1, ?_⟩⟩
  · obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := h.2 f f.2
    exact ⟨⟨⟨a, ha⟩, ⟨⟨b, hb⟩, isUnit_of_ord_zero P ⟨b, h.1 b hb⟩ hb0 hbo⟩⟩, Subtype.ext e⟩
  · have : (a : K) = b := congrArg (fun z : P.ring => (z : K)) e
    rw [Subtype.ext this]

end PolyPlaceEt


open PolyPlaceEt in
theorem formallyEtale_polyPlace : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K)
    (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL) (P0 : Place cK)
    (j : K →+* L), IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T → P0.IsPrimeOf R →
    (∀ g : R, j (g : K) = (ι g : L)) → ∀ (hA : ∀ f ∈ P0.ring, j f ∈ P.ring)
    (hτ : ∀ i, (τ i : L) ∈ P.ring),
    (MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))).FormallyEtale := by
  intro K L _ _ cK cL r R T ι ψ τ P P0 j hE hP hP0 hj hA hτ
  letI : Algebra R P0.ring := (inclRing hP0.1).toAlgebra
  letI : Algebra T P.ring := (inclRing hP.1).toAlgebra
  haveI h0 := isLocalization_ring hP0
  haveI h1 := isLocalization_ring hP
  letI : Algebra (MvPolynomial (Fin r) R) (MvPolynomial (Fin r) P0.ring) :=
    MvPolynomial.algebraMvPolynomial
  haveI := MvPolynomial.isLocalization (σ := Fin r) ((IsUnit.submonoid P0.ring).comap (inclRing hP0.1)) P0.ring
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) (MvPolynomial (Fin r) P0.ring) :=
    Algebra.FormallyEtale.of_isLocalization
      (((IsUnit.submonoid P0.ring).comap (inclRing hP0.1)).map MvPolynomial.C)
  have hc : ((algebraMap T P.ring).comp (MvPolynomial.eval₂Hom ι τ)).FormallyEtale :=
    RingHom.FormallyEtale.comp hE.etale (RingHom.formallyEtale_algebraMap.2
      (Algebra.FormallyEtale.of_isLocalization ((IsUnit.submonoid P.ring).comap (inclRing hP.1))))
  letI : Algebra (MvPolynomial (Fin r) R) P.ring :=
    ((algebraMap T P.ring).comp (MvPolynomial.eval₂Hom ι τ)).toAlgebra
  letI : Algebra (MvPolynomial (Fin r) P0.ring) P.ring :=
    (MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin r) R) (MvPolynomial (Fin r) P0.ring) P.ring := by
    apply IsScalarTower.of_algebraMap_eq'
    apply MvPolynomial.ringHom_ext
    · intro g
      change inclRing hP.1 (MvPolynomial.eval₂Hom ι τ (MvPolynomial.C g)) =
        MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))
          (MvPolynomial.map (inclRing hP0.1) (MvPolynomial.C g))
      rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      apply Subtype.ext
      exact (hj g).symm
    · intro i
      change inclRing hP.1 (MvPolynomial.eval₂Hom ι τ (MvPolynomial.X i)) =
        MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))
          (MvPolynomial.map (inclRing hP0.1) (MvPolynomial.X i))
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      rfl
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) P.ring := hc
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) P0.ring) P.ring :=
    Algebra.FormallyEtale.of_restrictScalars (R := MvPolynomial (Fin r) R)
  exact RingHom.formallyEtale_algebraMap.2 this

end GlobalTheory.FieldPair
end
end

section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem ratRes_locRing_of_isClosed : ∀ (Z : Scheme.{0}) [IsIntegral Z] (q : Z ⟶ Sp ℂ)
    [LocallyOfFiniteType q] (y : Z), IsClosed ({y} : Set Z) →
    RatRes (GlobalTheory.Cartier.constFn q) (locRing y) := by
  intro Z _ q _ y hy r hr
  have hyt : y ∈ (⊤ : Z.Opens) := trivial
  obtain ⟨s, rfl⟩ := hr
  have hsurj : Function.Surjective ((Z.evaluation ⊤ y hyt).hom.comp (algX q ⊤)) := by
    have e : (Z.evaluation ⊤ y hyt).hom.comp (algX q ⊤) = (residueFieldIsoBase q y hy).inv.hom :=
      ReciprocityTheory.AnForm.R.constRes_eq q y hy
    rw [e]
    exact (residueFieldIsoBase q y hy).commRingCatIsoToRingEquiv.symm.surjective
  obtain ⟨α, hα⟩ := hsurj (Z.residue y s)
  set g := Z.presheaf.germ ⊤ y hyt (algX q ⊤ α) with hgdef
  have hg : algebraMap (Z.presheaf.stalk y) Z.functionField g = GlobalTheory.Cartier.constFn q α := by
    rw [hgdef, algebraMap_germ]
    exact RingHom.congr_fun (fnOf_comp_algX q ⊤ _) α
  have hres : Z.residue y (s - g) = 0 := by
    rw [map_sub, sub_eq_zero, ← hα, hgdef, RingHom.comp_apply, ← Scheme.germ_residue, CommRingCat.comp_apply]
  have hnu : ¬ IsUnit (s - g) := by
    intro hu
    have : Z.residue y (s - g) ≠ 0 := by
      have := hu.map (Z.residue y).hom
      exact this.ne_zero
    exact this hres
  refine ⟨α, ?_⟩
  rw [← hg, ← map_sub]
  refine (nonUnit_iff (R := locRing y) ⟨_, s - g, rfl⟩).2 fun hu => hnu ?_
  obtain ⟨u, hu'⟩ := hu.exists_right_inv
  obtain ⟨t, ht⟩ := u.2
  refine isUnit_iff_exists_inv.2 ⟨t, ?_⟩
  refine (IsFractionRing.injective (Z.presheaf.stalk y) Z.functionField ?_)
  rw [map_mul, map_one, ht]
  exact congrArg Subtype.val hu'

end GlobalTheory.FieldPair
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem archIntegrable_of_isAmb : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k),
    IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) →
    ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  intro H k _ Y _ q hq e he M N r hr σ
  rcases isEmpty_or_nonempty (CxPts q σ) with h0 | ⟨⟨y⟩⟩
  · exact ⟨MeasureTheory.Integrable.of_isEmpty, MeasureTheory.Integrable.of_isEmpty⟩
  · have hc : CharZero Γ(Y, ⊤) :=
      RingHom.charZero (S := ℂ) ((Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp y.1.appTop.hom)
    exact H k Y q e ⟨hq.1, hq.2, ‹_›, hq.3, (flat_int_iff_charZero _).2 hc, he⟩ M N r hr σ

end GlobalTheory.MixHt
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.algebraicIndependent_etaleTower_coordinates : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  Function.Injective (MvPolynomial.eval₂Hom ι τ) →
  (letI := cL.toAlgebra; AlgebraicIndependent ℂ (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  first | exact @GlobalTheory.FieldPair.etTower_coords_algebraicIndependent | exact GlobalTheory.FieldPair.etTower_coords_algebraicIndependent | (intros; apply GlobalTheory.FieldPair.etTower_coords_algebraicIndependent <;> assumption)

end
end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_additive_sectionValueUnitFrame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ ℓ : P.H a b →+ ℂ, ∀ f : P.H a b, ℓ f = val P a b σ y f := by
  first | exact @GlobalTheory.HSAmp.val_additive | exact GlobalTheory.HSAmp.val_additive | (intros; apply GlobalTheory.HSAmp.val_additive <;> assumption)

end
end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_localModel_at_complexPoint : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.EssFiniteType ℂ A] (ε : A →ₐ[ℂ] ℂ),
  ∃ T : Subring (FractionRing A), IsLocModel (algebraMap ℂ (FractionRing A)) T ∧
    RatRes (algebraMap ℂ (FractionRing A)) T ∧
    ∀ a : A, algebraMap A (FractionRing A) a ∈ T ∧ (ε a = 0 → NonUnit T (algebraMap A (FractionRing A) a)) := by
  first | exact @GlobalTheory.FieldPair.exists_locModel_at_point | exact GlobalTheory.FieldPair.exists_locModel_at_point | (intros; apply GlobalTheory.FieldPair.exists_locModel_at_point <;> assumption)

end
end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.formallyEtale_polynomialPlace_to_place : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K)
    (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL) (P0 : Place cK)
    (j : K →+* L), IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T → P0.IsPrimeOf R →
    (∀ g : R, j (g : K) = (ι g : L)) → ∀ (hA : ∀ f ∈ P0.ring, j f ∈ P.ring)
    (hτ : ∀ i, (τ i : L) ∈ P.ring),
    (MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))).FormallyEtale := by
  first | exact @GlobalTheory.FieldPair.formallyEtale_polyPlace | exact GlobalTheory.FieldPair.formallyEtale_polyPlace | (intros; apply GlobalTheory.FieldPair.formallyEtale_polyPlace <;> assumption)

end
end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.hasRationalResidueField_pointLocalRing_closedPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (q : Z ⟶ Sp ℂ) [LocallyOfFiniteType q] (y : Z), IsClosed ({y} : Set Z) → RatRes (GlobalTheory.Cartier.constFn q) (locRing y) := by
  first | exact @GlobalTheory.FieldPair.ratRes_locRing_of_isClosed | exact GlobalTheory.FieldPair.ratRes_locRing_of_isClosed | (intros; apply GlobalTheory.FieldPair.ratRes_locRing_of_isClosed <;> assumption)

end
end

section

@[expose] public section

open Filter Topology MvPolynomial GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.homogeneousFormCombination_eq_zero_independent : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) → AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K → ∀ (ι : Type) [Fintype ι] (g : ι → K), LinearIndependent (ratF x) g → ∀ (q : ℕ) (T : ι → MvPolynomial (Fin (D + 1)) ℤ), (∀ i, (T i).IsHomogeneous q) → ∑ i, aeval x (T i) * g i = 0 → T = 0 := by
  first | exact @GlobalTheory.HSAmp.homogComb_eq_zero | exact GlobalTheory.HSAmp.homogComb_eq_zero | (intros; apply GlobalTheory.HSAmp.homogComb_eq_zero <;> assumption)

end
end
