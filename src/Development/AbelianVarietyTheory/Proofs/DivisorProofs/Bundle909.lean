module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertHomCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle141
public import Mathlib.NumberTheory.NumberField.Basic
import Development.EtaleCohomology.CohomologicalPurity.WeightedVectorLaurentEvalHomTOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieAction
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle881
public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle879
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM

theorem ahFactor_im_int_chart {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  apply _root_.GlobalTheory.LamPullFrame.exists_chart_pt' <;> assumption

theorem ahFactor_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (v w : Fin g → ℂ) : w ⬝ᵥ Hm.mulVec (star v) = star (v ⬝ᵥ Hm.mulVec (star w)) := by
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← hH.apply a b, star_star]
  ring

theorem ahFactor_im_int : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → IsFactorAH u Hm χ →
    ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n := by
  intro g A _ L u Hm χ hL hF l hl l' hl'
  obtain ⟨hH, hχ, hfac⟩ := hF
  obtain ⟨i, hi⟩ := ahFactor_im_int_chart L hL (u.ex 0).left
  have hex : ∀ z ∈ u.Λ, u.ex z = u.ex 0 := fun z hz => by
    rw [(u.ker z).mpr hz, (u.ker 0).mpr (zero_mem _)]
  have hc : ∀ z ∈ u.Λ, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := fun z hz => by rw [hex z hz]; exact hi
  have e1 := hfac ⟨l, hl⟩ i 0 (hc 0 (zero_mem _))
  have e2 := hfac ⟨l', hl'⟩ i l (hc l hl)
  have e3 := hfac ⟨l', hl'⟩ i 0 (hc 0 (zero_mem _))
  have e4 := hfac ⟨l, hl⟩ i l' (hc l' hl')
  have hne := u.fr_ne i (l + l') (hc _ (add_mem hl hl'))
  have hχ1 : χ ⟨l, hl⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l, hl⟩
  have hχ2 : χ ⟨l', hl'⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l', hl'⟩
  have hsw := ahFactor_herm_swap hH l l'
  simp only [zero_add, zero_dotProduct, mul_zero] at e1 e3
  rw [e2] at e1
  rw [e4, add_comm l' l] at e3
  have key := e1.symm.trans e3
  set F := u.fr i (l + l')
  set H := l ⬝ᵥ Hm.mulVec (star l')
  set H' := l' ⬝ᵥ Hm.mulVec (star l')
  set H0 := l ⬝ᵥ Hm.mulVec (star l)
  set Hs := l' ⬝ᵥ Hm.mulVec (star l)
  set c1 := χ ⟨l, hl⟩
  set c2 := χ ⟨l', hl'⟩
  have key2 : (c1 * c2 * F) * Complex.exp (Real.pi / 2 * H0 + (Real.pi * H + Real.pi / 2 * H')) =
      (c1 * c2 * F) * Complex.exp (Real.pi / 2 * H' + (Real.pi * Hs + Real.pi / 2 * H0)) := by
    simp only [Complex.exp_add] at key ⊢
    linear_combination key
  have hnz : c1 * c2 * F ≠ 0 := mul_ne_zero (mul_ne_zero hχ1 hχ2) hne
  have key3 := mul_left_cancel₀ hnz key2
  have key4 : Complex.exp ((Real.pi / 2 * H0 + (Real.pi * H + Real.pi / 2 * H')) -
      (Real.pi / 2 * H' + (Real.pi * Hs + Real.pi / 2 * H0))) = 1 := by
    rw [Complex.exp_sub, key3, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp key4
  refine ⟨n, ?_⟩
  have hsc : H - Hs = 2 * (H.im : ℂ) * Complex.I := by
    rw [hsw]
    have h7 := Complex.sub_conj H
    push_cast at h7
    exact h7
  have h5 : ((H.im : ℂ) - n) * (2 * Real.pi * Complex.I) = 0 := by
    linear_combination hn - (Real.pi : ℂ) * hsc
  have h6 := sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right Complex.two_pi_I_ne_zero)
  exact_mod_cast h6

end GlobalTheory.TorusRM
end
end

section

namespace GlobalTheory.NatMultipleIntegralSmulBound

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : RingOfIntegers E, (b : E) = (m : E) * a := by
  have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos (Int.natAbs_pos.2 hy) (Int.natAbs_pos.2 hy),
    ⟨y • (y • a), (mem_integralClosure_iff ℤ E).2 (hint.smul y)⟩, ?_⟩
  show y • (y • a) = ((y.natAbs * y.natAbs : ℕ) : E) * a
  rw [smul_smul, zsmul_eq_mul, ← Int.cast_natCast, Int.natAbs_mul_self]

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L' : Submodule (RingOfIntegers E) (Fin n → E))
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ c : ℕ, 0 < c ∧ (c : E) • x ∈ L' := by
  apply GlobalTheory.PrincLat.exists_nat_smul_mem <;> assumption

theorem exists_nat_smul_le {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L L' : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.FG L)
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) :
    ∃ (c : ℕ), (0 : ℕ) < c ∧ ∀ x ∈ L, (↑c : E) • x ∈ L' := by
  classical
  obtain ⟨s, rfl⟩ := hL
  have hs : ∃ c : ℕ, 0 < c ∧ ∀ x ∈ s, (c : E) • x ∈ L' := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | @insert a s _ ih =>
      obtain ⟨c, hc, hcs⟩ := ih
      obtain ⟨d, hd, hda⟩ := exists_nat_smul_mem L' h a
      refine ⟨c * d, Nat.mul_pos hc hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · have e : ((c * d : ℕ) : E) • x = c • ((d : E) • x) := by
          rw [← Nat.cast_smul_eq_nsmul E c, smul_smul, Nat.cast_mul]
        rw [e]
        exact L'.nsmul_mem hda c
      · have e : ((c * d : ℕ) : E) • x = d • ((c : E) • x) := by
          rw [← Nat.cast_smul_eq_nsmul E d, smul_smul, Nat.cast_mul, mul_comm]
        rw [e]
        exact L'.nsmul_mem (hcs x hx) d
  obtain ⟨c, hc, hcs⟩ := hs
  refine ⟨c, hc, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hcs x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact L'.add_mem hx hy
  | smul b x _ hx =>
    rw [Nat.cast_smul_eq_nsmul] at hx ⊢
    rw [smul_comm]
    exact L'.smul_mem b hx

end GlobalTheory.NatMultipleIntegralSmulBound
end

section

namespace GlobalTheory.CoordinateBasisBounds

open NumberField

theorem nat_mul_integral {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ o : 𝓞 E, (m : E) * x = algebraMap (𝓞 E) E o := by
  have hx : IsAlgebraic ℤ x := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ x)
  obtain ⟨m, s, hm, h⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 E) hx
  exact ⟨m, Nat.pos_of_ne_zero hm, s, by rw [← h, nsmul_eq_mul]⟩

theorem coord_bound {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, ∀ i : Fin n, ∃ o : 𝓞 E, (N : E) * x i = algebraMap (𝓞 E) E o := by
  obtain ⟨S, hS⟩ := hL
  have key : ∀ v ∈ S, ∃ m : ℕ, 0 < m ∧ ∀ i : Fin n, ∃ o : 𝓞 E, (m : E) * v i = algebraMap (𝓞 E) E o := by
    intro v _
    choose m hm o ho using fun i : Fin n => nat_mul_integral (v i)
    refine ⟨∏ i, m i, Finset.prod_pos (fun i _ => hm i), fun i => ?_⟩
    have hd : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := hd
    refine ⟨(k : 𝓞 E) * o i, ?_⟩
    rw [hk, map_mul, ← ho i, map_natCast]; push_cast; ring
  classical
  choose! m hm hv using key
  refine ⟨∏ v ∈ S, m v, Finset.prod_pos (fun v hv' => hm v hv'), ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem v hvS =>
    intro i
    obtain ⟨o, ho⟩ := hv v hvS i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hvS
    refine ⟨(k : 𝓞 E) * o, ?_⟩
    rw [hk, map_mul, ← ho, map_natCast]; push_cast; ring
  | zero => intro i; exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨a, ha⟩ := hx i
    obtain ⟨b, hb⟩ := hy i
    exact ⟨a + b, by rw [map_add (f := _), ← ha, ← hb, Pi.add_apply]; ring⟩
  | smul c x _ hx =>
    intro i
    obtain ⟨a, ha⟩ := hx i
    refine ⟨c * a, ?_⟩
    rw [map_mul, ← ha, Pi.smul_apply, Algebra.smul_def]; ring

theorem basis_bound {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  apply GlobalTheory.PrincLat.exists_nat_smul_mem <;> assumption

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.FG L → Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∃ (N : ℕ), (0 : ℕ) < N ∧ (∀ (j : Fin n), (↑N : E) • Pi.single j (1 : E) ∈ L) ∧ ∀ x ∈ L, ∀ (i : Fin n), ∃ (o : NumberField.RingOfIntegers E), (↑N : E) * x i = (Algebra.algebraMap (NumberField.RingOfIntegers E) E : NumberField.RingOfIntegers E → E) o := by
  intro E _ _ n L hL hspan
  obtain ⟨M, hM, hcoord⟩ := GlobalTheory.CoordinateBasisBounds.coord_bound L hL
  choose d hd hdL using fun j : Fin n => GlobalTheory.CoordinateBasisBounds.basis_bound L hspan (Pi.single j (1 : E))
  refine ⟨M * ∏ j, d j, Nat.mul_pos hM (Finset.prod_pos fun j _ => hd j), ?_, ?_⟩
  · intro j
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ j)
    have e : ((M * ∏ j, d j : ℕ) : E) • Pi.single j (1 : E) = (M * k) • ((d j : E) • Pi.single j (1 : E)) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, hk]; push_cast; ring_nf
    rw [e]
    exact nsmul_mem (hdL j) _
  · intro x hx i
    obtain ⟨o, ho⟩ := hcoord x hx i
    refine ⟨((∏ j, d j : ℕ) : 𝓞 E) * o, ?_⟩
    rw [map_mul, ← ho, map_natCast]; push_cast; ring

end GlobalTheory.CoordinateBasisBounds
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.MultiplicativeGroupGlobalSections


open LaurentPolynomial in
theorem laurent_ringHom_ext {R S : Type} [CommRing R] [CommRing S] {f g : LaurentPolynomial R →+* S}
    (hC : f.comp C = g.comp C) (hT : f (T 1) = g (T 1)) : f = g := by
  apply LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.ExcisionChartRatio.laurent_ext <;> assumption

theorem pull_spMap_id (q : ℕ) (A : Type) [CommRing A] (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (RingHom.id A)) _ n x = x := by
  have h : spMap (RingHom.id A) = 𝟙 (sp A) := by
    simp only [spMap]
    rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]
  rw [h, pull_id]


open LaurentPolynomial GmPhiNat in
theorem exists_ht_zero_pull_laurent_eq (q : ℕ) [NeZero q] (R : Type) [CommRing R] (hq : IsUnit (q : R)) (i : ℤ)
    (y : Ht q (sp (LaurentPolynomial R)) 0 i) :
    ∃ z : Ht q (sp R) 0 i, pull _ (spMap (LaurentPolynomial.C : R →+* LaurentPolynomial R)) _ 0 z = y := by
  let ev₁ : LaurentPolynomial R →+* R := eval₂ (RingHom.id R) 1
  have hev : ev₁.comp C = RingHom.id R := RingHom.ext fun a => eval₂_C _ _ a
  refine ⟨pull _ (spMap ev₁) _ 0 y, ?_⟩
  symm
  rw [← sub_eq_zero]
  have hqL : IsUnit (q : LaurentPolynomial R) := by simpa using hq.map (C : R →+* LaurentPolynomial R)
  apply GlobalTheory.EtC.GeomZero.eq_zero_of_geom q (LaurentPolynomial R) hqL i
  intro K _ _ f
  set y' := y - pull _ (spMap (C : R →+* LaurentPolynomial R)) _ 0 (pull _ (spMap ev₁) _ 0 y) with hy'

  have h0 : pull _ (spMap ev₁) _ 0 y' = 0 := by
    rw [hy', map_sub, ← pull_spMap_comp, hev, pull_spMap_id, sub_self]
  let f₀ : R →+* K := f.comp C
  have hT1 : IsUnit (f (T 1)) := by
    refine isUnit_iff_exists_inv.2 ⟨f (T (-1)), ?_⟩
    rw [← map_mul, ← T_add]; simp
  let u : Kˣ := hT1.unit
  let evu : LaurentPolynomial K →+* K := eval₂ (RingHom.id K) u
  have hf : f = evu.comp (laurentMap f₀) := by
    apply laurent_ringHom_ext
    · rw [RingHom.comp_assoc, laurentMap_C, ← RingHom.comp_assoc]
      ext a
      simp [evu, f₀, eval₂_C]
    · simp [evu, laurentMap_T, eval₂_T, u]
  let ev₁K : LaurentPolynomial K →+* K := eval₂ (RingHom.id K) 1
  have hevK : ev₁K.comp C = RingHom.id K := RingHom.ext fun a => eval₂_C _ _ a
  have hcomm : ev₁K.comp (laurentMap f₀) = f₀.comp ev₁ := by
    apply laurent_ringHom_ext
    · rw [RingHom.comp_assoc, laurentMap_C, ← RingHom.comp_assoc, hevK, RingHom.comp_assoc, hev]
      rfl
    · simp [ev₁K, ev₁, laurentMap_T, eval₂_T]
  have hqK : IsUnit (q : K) := by simpa using hq.map f₀
  have hζ : ∃ ζ : K, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    have hdeg : (Polynomial.cyclotomic q K).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨ζ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ
  have hbij := GlobalTheory.EtC.h_zero_pull_bijective q K (LaurentPolynomial K) (C : K →+* LaurentPolynomial K) hqK hζ
    inferInstance (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) i
  have hw : pull _ (spMap (laurentMap f₀)) _ 0 y' = 0 := by
    obtain ⟨v, hv⟩ := hbij.2 (pull _ (spMap (laurentMap f₀)) _ 0 y')
    have hv0 : v = 0 := by
      have e1 : pull _ (spMap ev₁K) _ 0 (pull _ (spMap (C : K →+* LaurentPolynomial K)) _ 0 v) = v := by
        rw [← pull_spMap_comp, hevK, pull_spMap_id]
      rw [← e1, hv, ← pull_spMap_comp, hcomm, pull_spMap_comp, h0, map_zero]
    rw [← hv, hv0, map_zero]
  rw [hf, pull_spMap_comp, hw, map_zero]

end GlobalTheory.EtC.MultiplicativeGroupGlobalSections

end
end

section

open Matrix Finset Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.LowHW

theorem height_root {n : ℕ} (a b : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * Formalism.REAL.root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem height_sum {n : ℕ} (c : Fin n → Fin n → ℕ) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) i
      = ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
  simp only [← height_root, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

theorem cdom_antisymm {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h1 : CDom ε μ Λ) (h2 : CDom ε Λ μ) :
    μ = Λ := by
  apply Formalism.MainNotions.BridgeLemma.cdom_antisymm <;> assumption

end GlobalTheory.LowHW
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

theorem _root_.GlobalTheory.T.exists_coprime_mul_prime_pow_mem_conductor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), l.Prime → IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∃ M : ℕ, ¬ l ∣ M ∧ ((M * l ^ a0 𝔣 l : ℕ) : OF E) ∈ condQ 𝔣 Q := by
  first | exact @GlobalTheory.HilbFam.CondNumber.exists_mem_condQ | exact GlobalTheory.HilbFam.CondNumber.exists_mem_condQ | (intros; apply GlobalTheory.HilbFam.CondNumber.exists_mem_condQ <;> assumption)
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory

theorem exists_perm_of_block_bijection : ∀ (r : ℕ) (b b' : Fin r → ℕ) (R : ℕ → ℕ → Prop), (∀ c ∈ Set.range b, ∃! c', c' ∈ Set.range b' ∧ R c c') → (∀ c' ∈ Set.range b', ∃! c, c ∈ Set.range b ∧ R c c') → (∀ c ∈ Set.range b, ∀ c' ∈ Set.range b', R c c' → (block b c).card = (block b' c').card) → ∃ w : Equiv.Perm (Fin r), (∀ i, R (b i) (b' (w i))) ∧ ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  classical
  intro r b b' R h1 h2 h3
  have h1' : ∀ i : Fin r, ∃ c', c' ∈ Set.range b' ∧ R (b i) c' :=
    fun i => (h1 (b i) ⟨i, rfl⟩).exists
  choose f hf1 hf2 using h1'
  have hiff : ∀ i c c', c ∈ Set.range b → c' ∈ Set.range b' → R c c' → (f i = c' ↔ b i = c) := by
    intro i c c' hc hc' hR
    constructor
    · intro h
      exact (h2 c' hc').unique ⟨⟨i, rfl⟩, h ▸ hf2 i⟩ ⟨hc, hR⟩
    · intro h
      subst h
      exact (h1 (b i) hc).unique ⟨hf1 i, hf2 i⟩ ⟨hc', hR⟩
  have hcard : ∀ c' : ℕ, Fintype.card {i // f i = c'} = Fintype.card {i // b' i = c'} := by
    intro c'
    rw [Fintype.card_subtype, Fintype.card_subtype]
    by_cases hc' : c' ∈ Set.range b'
    · obtain ⟨c, hc, hR⟩ := (h2 c' hc').exists
      have h := h3 c hc c' hc' hR
      unfold block at h
      rw [← h]
      congr 1
      ext i
      simp [hiff i c c' hc hc' hR]
    · rw [Finset.filter_eq_empty_iff.2, Finset.filter_eq_empty_iff.2]
      · intro i _ h
        exact hc' ⟨i, h⟩
      · intro i _ h
        exact hc' (h ▸ hf1 i)
  let e : ∀ c' : ℕ, {i // f i = c'} ≃ {i // b' i = c'} := fun c' => Fintype.equivOfCardEq (hcard c')
  have hw : ∀ i, b' (Equiv.ofFiberEquiv e i) = f i := fun i => Equiv.ofFiberEquiv_map e i
  refine ⟨Equiv.ofFiberEquiv e, fun i => ?_, fun i j => ?_⟩
  · rw [hw]; exact hf2 i
  · rw [hw, hw]
    exact (hiff i (b j) (f j) ⟨j, rfl⟩ (hf1 j) (hf2 j)).symm

end GlobalTheory
end

section

open NumberField GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.mem_zalg_commute_lie_action : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a → z * GlobalTheory.CuspRep.lie E a X = GlobalTheory.CuspRep.lie E a X * z := by
  first | exact @GlobalTheory.CuspRep.Zalg_mul_lie | exact GlobalTheory.CuspRep.Zalg_mul_lie | (intros; apply GlobalTheory.CuspRep.Zalg_mul_lie <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_units_comparing_lifted_transitions_factor : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X), M.IsLB → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ (fr : ∀ k, Hol (K.W k)) (a : Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) → (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) → ∀ (i : K.Obj → M.ι), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) → ∀ (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C), (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) → ∃ e : ∀ T : K.Obj, (T.C)ˣ, (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) := by
  first | exact @GlobalTheory.LiftUnits.exists_units | exact GlobalTheory.LiftUnits.exists_units | (intros; apply GlobalTheory.LiftUnits.exists_units <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_analyticChartsRealization_of_affine : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ K : Charts F, (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K.W k, ⊤ ≤ u.E p ⁻¹ᵁ U) → ∃ r : Real K s σ, r.IsFor u ∧ ∀ k (U : X.Opens), IsAffineOpen U → (∀ p ∈ K.W k, ⊤ ≤ u.E p ⁻¹ᵁ U) → ⊤ ≤ r.x k ⁻¹ᵁ U := by
  first | exact @GlobalTheory.AnPer.exists_real_isFor | exact GlobalTheory.AnPer.exists_real_isFor | (intros; apply GlobalTheory.AnPer.exists_real_isFor <;> assumption)
end
