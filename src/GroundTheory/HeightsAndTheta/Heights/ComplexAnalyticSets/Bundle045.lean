module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem CurveProperClosedFinite.no_chain_two {R : Type*} [CommRing R] {W P Q : Ideal R}
    (hW : W.IsPrime) (hP : P.IsPrime) (hQ : Q.IsPrime) (hdim : ringKrullDim (R ⧸ W) = 1)
    (hWP : W < P) (hPQ : P < Q) : False := by
  let a : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨W, hW⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 le_rfl⟩
  let b : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨P, hP⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 hWP.le⟩
  let c : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨Q, hQ⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 (hWP.trans hPQ).le⟩
  have hab : a < b := hWP
  have hbc : b < c := hPQ
  let p0 : LTSeries (PrimeSpectrum.zeroLocus (R := R) (W : Set R)) := RelSeries.singleton _ a
  have h2 := Order.LTSeries.length_le_krullDim ((p0.snoc b hab).snoc c hbc)
  rw [← ringKrullDim_quotient, hdim] at h2
  have hl : ((p0.snoc b hab).snoc c hbc).length = 2 := by
    rfl
  rw [hl] at h2
  norm_num at h2

theorem CurveProperClosedFinite.proof : CurveProperClosedFinite.Statement := by
  intro n W K hW hdim hK
  let m : (Fin n → ℂ) → Ideal (MvPolynomial (Fin n) ℂ) := fun x => RingHom.ker (eval x)
  have hinj : Function.Injective m := by
    intro x y hxy
    funext i
    have hx : X i - C (x i) ∈ m x := by simp [m, RingHom.mem_ker]
    have hy : X i - C (x i) ∈ m y := hxy ▸ hx
    have hy' : y i - x i = 0 := by simpa [m, RingHom.mem_ker] using hy
    exact (sub_eq_zero.1 hy').symm
  have hsub : m '' (zeroSet W ∩ zeroSet K) ⊆ (W ⊔ K).minimalPrimes := by
    rintro _ ⟨x, ⟨hxW, hxK⟩, rfl⟩
    have hmax : (m x).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective (eval x) (fun c => ⟨C c, by simp⟩)
    have hle : W ⊔ K ≤ m x := sup_le (fun q hq => hxW q hq) (fun q hq => hxK q hq)
    refine ⟨⟨hmax.isPrime, hle⟩, fun Q ⟨hQ, hJQ⟩ hQm => ?_⟩
    by_contra hmQ
    have hWQ : W < Q := by
      refine lt_of_le_of_ne (le_sup_left.trans hJQ) ?_
      rintro rfl
      exact hK (le_sup_right.trans hJQ)
    exact CurveProperClosedFinite.no_chain_two hW hQ hmax.isPrime hdim hWQ (lt_of_le_of_ne hQm
      (fun h => hmQ (h ▸ le_rfl)))
  exact Set.Finite.of_finite_image
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset hsub) hinj.injOn

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreSFlatAscent.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], IsNoetherianRing A → IsNoetherianRing B →
    Module.Flat A B → ∀ k : ℕ, SerreS A k →
      (∀ (P : Ideal B) [P.IsPrime], SerreSAt (primeFibreLocalRing A P) k) → SerreS B k

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

def IsolatedPointsCountPrime.Statement : Prop :=
  ∀ (n m : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)), P.IsPrime → ∀ (Q : Fin m → MvPolynomial (Fin n) ℂ),
    ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts P Q z).encard ≤ N

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric

open MvPolynomial Matrix

noncomputable section

def entries {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : Fin a × Fin b → ℂ := fun ij => A ij.1 ij.2

def rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  bind₁ (fun ij : Fin d × Fin n => ∑ l, C (F (s ij.1) l) * X (l, ij.2)) p

theorem eval_rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
    eval (entries U) (rowsPoly F s p) = eval (entries ((F * U).submatrix s id)) p := by
  change eval₂Hom (RingHom.id ℂ) (entries U) (bind₁ _ p) = eval₂Hom (RingHom.id ℂ) _ p
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  simp [entries, Matrix.mul_apply]

theorem exists_rows_eq {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) (A : Matrix (Fin d) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, (F * U).submatrix s id = A := by
  refine ⟨star F * Matrix.of (Function.extend s (fun i => A i) 0), ?_⟩
  rw [← Matrix.mul_assoc, mem_unitaryGroup_iff.mp hF, Matrix.one_mul]
  ext i j
  simp [hs.extend_apply]

theorem rowsPoly_ne_zero {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) {p : MvPolynomial (Fin d × Fin n) ℂ}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : eval (entries A) p ≠ 0) : rowsPoly F s p ≠ 0 := by
  obtain ⟨U, hU⟩ := exists_rows_eq hF hs A
  intro h
  apply hA
  rw [← hU, ← eval_rowsPoly, h, map_zero]

theorem proof (hO : FiniteProjectionsContainOpen.Statement) (hU : UnitaryZariskiDense.Statement) :
    FiniteProjectionsGeneric.Statement := by
  classical
  intro n d J hJ hd
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hsub⟩ := hO n d J hJ hd
  have hA₀' := hA₀
  rw [hS] at hA₀'
  obtain ⟨p, hpS, hp⟩ := hA₀'
  have good : ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (entries A) p ≠ 0 → IsFiniteProjection J A :=
    fun A hA => hsub (by rw [hS]; exact ⟨p, hpS, hA⟩)
  have hdn : d ≤ n := by
    have h := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
    exact_mod_cast h
  refine ⟨⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hsub⟩, fun D hD hcl => ?_, fun m F => ?_⟩
  · obtain ⟨U, hUu, hUp⟩ := hU n (rowsPoly 1 (Fin.castLE hdn) p)
      (rowsPoly_ne_zero (one_mem _) (Fin.castLE_injective hdn) hp)
    have hUp' : eval (entries (U.submatrix (Fin.castLE hdn) id)) p ≠ 0 := by
      have := eval_rowsPoly 1 (Fin.castLE hdn) p U
      rw [Matrix.one_mul] at this
      exact this ▸ hUp
    have hAo : U.submatrix (Fin.castLE hdn) id ∈ orthoRows d n := by
      show _ * _ = _
      rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
        ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hUu,
        submatrix_one _ (Fin.castLE_injective hdn)]
    have hopen : IsOpen {B : Matrix (Fin d) (Fin n) ℂ | eval (entries B) p ≠ 0} :=
      isOpen_ne_fun ((MvPolynomial.continuous_eval p).comp
        (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)) continuous_const
    obtain ⟨B, hBp, hBD⟩ := mem_closure_iff.mp (hcl hAo) _ hopen hUp'
    exact ⟨B, hBD, good B hBp⟩
  · have hQ : (∏ ks : Fin m × (Fin d ↪ Fin n), rowsPoly (F ks.1 : Matrix (Fin n) (Fin n) ℂ) ks.2 p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ks _ => rowsPoly_ne_zero (F ks.1).2 ks.2.injective hp
    obtain ⟨U, hUu, hUQ⟩ := hU n _ hQ
    refine ⟨U, hUu, fun k s => good _ ?_⟩
    rw [map_prod] at hUQ
    have := Finset.prod_ne_zero_iff.mp hUQ (k, s) (Finset.mem_univ _)
    change eval (entries U) (rowsPoly _ _ p) ≠ 0 at this
    rwa [eval_rowsPoly] at this

end

end GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Matrix

noncomputable section

def entries {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : Fin a × Fin b → ℂ := fun ij => A ij.1 ij.2

def rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  bind₁ (fun ij : Fin d × Fin n => ∑ l, C (F (s ij.1) l) * X (l, ij.2)) p

theorem eval_rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
    eval (entries U) (rowsPoly F s p) = eval (entries ((F * U).submatrix s id)) p := by
  change eval₂Hom (RingHom.id ℂ) (entries U) (bind₁ _ p) = eval₂Hom (RingHom.id ℂ) _ p
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  simp [entries, Matrix.mul_apply]

theorem exists_rows_eq {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) (A : Matrix (Fin d) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, (F * U).submatrix s id = A := by
  refine ⟨star F * Matrix.of (Function.extend s (fun i => A i) 0), ?_⟩
  rw [← Matrix.mul_assoc, mem_unitaryGroup_iff.mp hF, Matrix.one_mul]
  ext i j
  simp [hs.extend_apply]

theorem rowsPoly_ne_zero {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) {p : MvPolynomial (Fin d × Fin n) ℂ}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : eval (entries A) p ≠ 0) : rowsPoly F s p ≠ 0 := by
  obtain ⟨U, hU⟩ := exists_rows_eq hF hs A
  intro h
  apply hA
  rw [← hU, ← eval_rowsPoly, h, map_zero]

theorem GenericProjectionFinite.proof (hO : FiniteProjectionsContainOpen.Statement)
    (hU : UnitaryZariskiDense.Statement) :
    GenericProjectionFinite.Statement := by
  classical
  intro n d J hJ hd
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hW⟩ := hO n d J hJ hd
  have good : ∀ A : Matrix (Fin d) (Fin n) ℂ, (∃ p ∈ S, eval (entries A) p ≠ 0) →
      IsFiniteProjection J A := fun A hA => hW (by rw [hS]; exact hA)
  have hA₀' := hA₀
  rw [hS] at hA₀'
  obtain ⟨p, hpS, hp⟩ := hA₀'
  have hdn : d ≤ n := by
    have h := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
    exact_mod_cast h
  refine ⟨⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, fun A hA => hW hA⟩, ⟨A₀, hW hA₀⟩, fun D hD hcl => ?_, fun m F => ?_⟩
  · obtain ⟨U, hUu, hUp⟩ := hU n (rowsPoly 1 (Fin.castLE hdn) p)
      (rowsPoly_ne_zero (one_mem _) (Fin.castLE_injective hdn) hp)
    have hUp' : eval (entries (U.submatrix (Fin.castLE hdn) id)) p ≠ 0 := by
      have := eval_rowsPoly 1 (Fin.castLE hdn) p U
      rw [Matrix.one_mul] at this
      exact this ▸ hUp
    have hAo : U.submatrix (Fin.castLE hdn) id ∈ orthoRows d n := by
      show _ * _ = _
      rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
        ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hUu,
        submatrix_one _ (Fin.castLE_injective hdn)]
    have hopen : IsOpen {B : Matrix (Fin d) (Fin n) ℂ | eval (entries B) p ≠ 0} :=
      isOpen_ne_fun ((MvPolynomial.continuous_eval p).comp
        (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)) continuous_const
    obtain ⟨B, hBp, hBD⟩ := mem_closure_iff.mp (hcl hAo) _ hopen hUp'
    exact ⟨B, hBD, good B ⟨p, hpS, hBp⟩⟩
  · have hQ : (∏ ks : Fin m × (Fin d ↪ Fin n), rowsPoly (F ks.1 : Matrix (Fin n) (Fin n) ℂ) ks.2 p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ks _ => rowsPoly_ne_zero (F ks.1).2 ks.2.injective hp
    obtain ⟨U, hUu, hUQ⟩ := hU n _ hQ
    refine ⟨U, hUu, fun k s => good _ ⟨p, hpS, ?_⟩⟩
    rw [map_prod] at hUQ
    have := Finset.prod_ne_zero_iff.mp hUQ (k, s) (Finset.mem_univ _)
    change eval (entries U) (rowsPoly _ _ p) ≠ 0 at this
    rwa [eval_rowsPoly] at this

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem DominantFibreBound.trdeg_le {n d : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection P A) :
    Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) ≤ Cardinal.mk (Fin d) := by
  set a : Fin d → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (linPoly A i) with ha_def
  have hproj : projHom P A = aeval a := by
    rw [projHom, pullback, comp_aeval]
    rfl
  have hind : AlgebraicIndependent ℂ a := by
    rw [algebraicIndependent_iff_injective_aeval, ← hproj]
    exact hA.injective
  have hint : Algebra.IsIntegral (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P) := by
    constructor
    intro b
    obtain ⟨f, hfm, hfb⟩ := hA.finite.to_isIntegral b
    refine ⟨f.map (hind.aevalEquiv : MvPolynomial (Fin d) ℂ →+* Algebra.adjoin ℂ (Set.range a)),
      hfm.map _, ?_⟩
    have hcomp : (algebraMap (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P)).comp
        (hind.aevalEquiv : MvPolynomial (Fin d) ℂ →+* Algebra.adjoin ℂ (Set.range a)) =
        (projHom P A).toRingHom := by
      apply RingHom.ext
      intro y
      rw [RingHom.comp_apply]
      change ((hind.aevalEquiv y : Algebra.adjoin ℂ (Set.range a)) : MvPolynomial (Fin n) ℂ ⧸ P) = projHom P A y
      rw [hproj]
      exact hind.algebraMap_aevalEquiv y
    rw [Polynomial.eval₂_map, hcomp]
    exact hfb
  have : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P) :=
    Algebra.IsIntegral.isAlgebraic
  exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk (R := ℂ) (s := Set.range a)).trans Cardinal.mk_range_le

theorem DominantFibreBound.exists_poly (hG : ComplexSets.GenericProjectionFinite.Statement) {n d : ℕ}
    (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) (hP : P.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ))
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval p)))
    (b : MvPolynomial (Fin n) ℂ ⧸ P) :
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g ≠ 0 ∧
      (g.map (aeval (fun i => Ideal.Quotient.mk P (p i))).toRingHom).eval b = 0 := by
  obtain ⟨A, hA⟩ := (hG n d P hP hdim).2.1
  set q : Fin d → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (p i) with hq_def
  have hind : AlgebraicIndependent ℂ q := by
    rw [algebraicIndependent_iff_injective_aeval]
    rw [comp_aeval] at hinj
    exact hinj
  have hbasis : IsTranscendenceBasis ℂ q :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (DominantFibreBound.trdeg_le P A hA)
  obtain ⟨f, hf0, hfb⟩ := hbasis.isAlgebraic.isAlgebraic b
  refine ⟨f.map (hind.aevalEquiv.symm : Algebra.adjoin ℂ (Set.range q) →+* MvPolynomial (Fin d) ℂ),
    (Polynomial.map_ne_zero_iff hind.aevalEquiv.symm.injective).2 hf0, ?_⟩
  rw [Polynomial.map_map, ← hfb, Polynomial.aeval_def, Polynomial.eval_map]
  congr 1
  ext y
  simp [← hind.algebraMap_aevalEquiv]

theorem DominantFibreBound.proof (hG : ComplexSets.GenericProjectionFinite.Statement) :
    DominantFibreBound.Statement := by
  intro n d P p hP hdim hinj
  choose g hg0 hgb using fun j : Fin n =>
    DominantFibreBound.exists_poly hG P p hP hdim hinj (Ideal.Quotient.mk P (X j))
  refine ⟨∏ j, (g j).natDegree, ∏ j, (g j).leadingCoeff, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun j _ => Polynomial.leadingCoeff_ne_zero.2 (hg0 j)
  intro w hw
  rw [map_prod] at hw
  have hlc : ∀ j, eval w (g j).leadingCoeff ≠ 0 := fun j =>
    (Finset.prod_ne_zero_iff.1 hw) j (Finset.mem_univ j)
  have hne : ∀ j, (g j).map (eval w) ≠ 0 := fun j h => by
    have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (eval w) (hlc j)
    rw [h, Polynomial.leadingCoeff_zero] at this
    exact hlc j this.symm
  let R : Fin n → Finset ℂ := fun j => ((g j).map (eval w)).roots.toFinset
  have hsub : {x | x ∈ zeroSet P ∧ ∀ i, eval x (p i) = w i} ⊆
      (Fintype.piFinset R : Set (Fin n → ℂ)) := by
    rintro x ⟨hx, hxw⟩
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    let ψ : MvPolynomial (Fin n) ℂ ⧸ P →+* ℂ := Ideal.Quotient.lift P (eval x) hx
    have hψx : ∀ q, ψ (Ideal.Quotient.mk P q) = eval x q := fun q => Ideal.Quotient.lift_mk P _ _
    have hψ : ψ.comp (aeval (fun i => Ideal.Quotient.mk P (p i))).toRingHom = eval w := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, algHom_C]
        rw [← Ideal.Quotient.mk_algebraMap, hψx, MvPolynomial.algebraMap_eq, eval_C, eval_C]
      · intro i
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        rw [hψx, hxw i, eval_X]
    have h0 := congrArg ψ (hgb j)
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, hψ, map_zero, ← Polynomial.eval_map] at h0
    have hxj : ψ (Ideal.Quotient.mk P (X j)) = x j := by
      rw [hψx, eval_X]
    rw [hxj] at h0
    exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hne j)).2 h0)
  calc _ ≤ (Fintype.piFinset R : Set (Fin n → ℂ)).encard := Set.encard_le_encard hsub
    _ = ((Fintype.piFinset R).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ _ := by
      rw [Fintype.card_piFinset]
      exact_mod_cast Finset.prod_le_prod' fun j _ => (Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans Polynomial.natDegree_map_le)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

def SliceReducedAway.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical →
    ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
      ∀ L ∈ O, ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → sliceIdeal J L q ≤ P →
        P ≠ RingHom.ker (eval q) →
          ∀ g ∈ (sliceIdeal J L q).radical, ∃ s ∉ P, s * g ∈ sliceIdeal J L q

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

def SliceReducedAwayZariski.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical →
    ∃ F : MvPolynomial (Fin d × Fin n) ℂ, F ≠ 0 ∧
      ∀ L : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F ≠ 0 →
        ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → sliceIdeal J L q ≤ P →
          P ≠ RingHom.ker (eval q) →
            ∀ g ∈ (sliceIdeal J L q).radical, ∃ s ∉ P, s * g ∈ sliceIdeal J L q

end

end GroundTheory.Heights₂.Heights
end
