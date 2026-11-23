module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle015
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ChartRankAdjoin

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] (z : (Σ k, ι k) → Φ') (j : ∀ k, ι k)

def affCoord : (Σ k, ι k) → Φ' := fun q => z q / z ⟨q.1, j q.1⟩

variable {z j}

theorem aeval_monomial_mul (hz : ∀ k, z ⟨k, j k⟩ ≠ 0) (m : (Σ k, ι k) →₀ ℕ) :
    aeval (affCoord z j) (monomial m (1 : Φ)) *
        ∏ k, z ⟨k, j k⟩ ^ (Finsupp.weight (NumbersDVR.blockWeight ι) m k) =
      aeval z (monomial m (1 : Φ)) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' =>
    rw [← mul_one (1 : Φ), ← monomial_mul, map_mul, map_mul, map_add (f := _), ← hm, ← hm']
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  | single p n =>
    rw [← X_pow_eq_monomial, map_pow, map_pow, Finsupp.weight_single,
      Fintype.prod_eq_single p.1 (fun k hk => by simp [NumbersDVR.blockWeight, hk])]
    simp only [affCoord, aeval_X, NumbersDVR.blockWeight, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, div_pow]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ (hz p.1))]

theorem aeval_mul_of_isMultiHomog [∀ k, Fintype (ι k)] (hz : ∀ k, z ⟨k, j k⟩ ≠ 0) {h : MRingOver Φ ι} {a : K → ℕ}
    (hh : IsMultiHomog h a) : aeval (affCoord z j) h * ∏ k, z ⟨k, j k⟩ ^ a k = aeval z h := by
  have hw := (Bridge.isMultiHomog_iff h a).mpr hh
  conv_rhs => rw [h.as_sum]
  conv_lhs => rw [h.as_sum]

  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw' : Finsupp.weight (NumbersDVR.blockWeight ι) m = a := hw (mem_support_iff.mp hm)
  have hmon : monomial m (AddMonoidAlgebra.coeff h m) = AddMonoidAlgebra.coeff h m • monomial m (1 : Φ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul, map_smul, smul_mul_assoc, ← hw', aeval_monomial_mul hz]

theorem chartIdeal_eq_ker [∀ k, Fintype (ι k)] (hz : ∀ k, z ⟨k, j k⟩ ≠ 0)
    (hP : IsMultiHomogIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ'))) :
    chartIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) j =
      RingHom.ker (aeval (affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ') := by
  have hprod : ∀ a : K → ℕ, ∏ k, z ⟨k, j k⟩ ^ a k ≠ 0 :=
    fun a => Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
  have hunit : Ideal.span (Set.range fun k => (X ⟨k, j k⟩ : MRingOver Φ ι) - 1) ≤
      RingHom.ker (aeval (affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ') := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, aeval_X, affCoord]
    rw [div_self (hz k), sub_self]
  refine le_antisymm (sup_le ?_ hunit) fun f hf => ?_
  · obtain ⟨S, hS, hPS⟩ := hP
    rw [hPS, Ideal.span_le]
    intro s hs
    obtain ⟨a, ha⟩ := hS s hs
    have hsP : s ∈ RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ') := by
      rw [hPS]; exact Ideal.subset_span hs
    have h1 := aeval_mul_of_isMultiHomog hz ha
    rw [RingHom.mem_ker.mp hsP] at h1
    exact RingHom.mem_ker.mpr ((mul_eq_zero.mp h1).resolve_right (hprod a))
  · obtain ⟨N, hN⟩ := NumbersDVR.IntNumPoint.exists_homog_congr j f
    obtain ⟨h, hh, hc⟩ := hN N le_rfl
    have hfh : f - h ∈ NumbersDVR.IntNumPoint.chartUnitIdeal (F := Φ) j := Ideal.Quotient.eq.mp hc
    have h0 : aeval (affCoord z j) h = 0 := by
      have := RingHom.mem_ker.mp (hunit hfh)
      rwa [map_sub, RingHom.mem_ker.mp hf, zero_sub, neg_eq_zero] at this
    have hhP : h ∈ RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ') := by
      rw [RingHom.mem_ker, ← aeval_mul_of_isMultiHomog hz ((Bridge.isMultiHomog_iff h N).mp hh), h0,
        zero_mul]
    have : f = (f - h) + h := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_right hfh) (Ideal.mem_sup_left hhP)

end ChartRankAdjoin

theorem ChartRankAdjoin.proof : ChartRankAdjoin.Statement := by
  classical
  intro K _ ι _ Φ Φ' _ _ _ z j hz hP
  have hker := ChartRankAdjoin.chartIdeal_eq_ker hz hP
  have e : (fun q : Σ k, ι k => z q / z ⟨q.1, j q.1⟩) = ChartRankAdjoin.affCoord z j := rfl
  rw [e, ptDeg, hker,
    (Ideal.quotientKerEquivRange (aeval (ChartRankAdjoin.affCoord z j) :
      MRingOver Φ ι →ₐ[Φ] Φ')).toLinearEquiv.finrank_eq, aeval_range,
    ← IntermediateField.finrank_eq_finrank_subalgebra]
  by_cases halg : ∀ q, IsAlgebraic Φ (ChartRankAdjoin.affCoord z j q)
  · rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (by rintro _ ⟨q, rfl⟩; exact halg q)]
  · push Not at halg
    obtain ⟨q, hq⟩ := halg
    have hinf : ∀ B : Subalgebra Φ Φ', ChartRankAdjoin.affCoord z j q ∈ B → ¬ Module.Finite Φ B :=
      fun B hB hfin => hq ((IsAlgebraic.of_finite Φ (⟨_, hB⟩ : B)).algHom B.val)
    have h1 : ChartRankAdjoin.affCoord z j q ∈ Algebra.adjoin Φ (Set.range (ChartRankAdjoin.affCoord z j)) :=
      Algebra.subset_adjoin ⟨q, rfl⟩
    have h2 : ChartRankAdjoin.affCoord z j q ∈
        (IntermediateField.adjoin Φ (Set.range (ChartRankAdjoin.affCoord z j))).toSubalgebra :=
      IntermediateField.subset_adjoin Φ _ ⟨q, rfl⟩
    rw [Module.finrank_of_not_finite (hinf _ h1), Module.finrank_of_not_finite (hinf _ h2)]

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

abbrev ProjectiveLineBundle.Diag {D : ℕ} (S : ProjectiveLineBundle D) : Ideal (MRing S.WIdx) :=
  T.wwIdeal S.x S.δ S.e S.φ (S.a 0) (S.a 0)

section Statements

def ZeroSetNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (s : MRing ι)
    (a : K → ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsMultiHomog s a → s ∉ P →
    (∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) s) ≠ 0 → g₁ z = g₂ z) →
    ptsIntegral P φ g₁ = ptsIntegral P φ g₂

end Statements

section Inhabit

end Inhabit

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Gen

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_comp_X {σ A B : Type} [CommRing A] [CommRing B] {_ : Algebra ℤ B}
    (φ : MvPolynomial σ ℤ →+* A) (e : A →+* B) (f : MvPolynomial σ ℤ) :
    aeval (fun q => e (φ (X q))) f = e (φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact (eq_intCast (algebraMap ℤ B) a).trans (eq_intCast ((e.comp φ).comp C) a).symm
  | add p q hp hq => rw [map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p q hp => rw [map_mul, hp, aeval_X, map_mul, map_mul]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_genPt (P : Ideal (MRing ι)) {_ : Algebra ℤ (FnField P)} (f : MRing ι) :
    aeval (genPt P) f = algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f) :=
  aeval_comp_X (Ideal.Quotient.mk P) (algebraMap (MRing ι ⧸ P) (FnField P)) f


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ker_algebraMap_comp_mk (P : Ideal (MRing ι)) :
    RingHom.ker ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) = P := by
  rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective (MRing ι ⧸ P) (FnField P)), Ideal.mk_ker]

end Gen

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

def pivotCols {n : ℕ} (a : Fin (n - 1)) (b : Fin n) : Fin (a + 1) → Fin n :=
  fun c => if h : (c : ℕ) < a then ⟨c, by have := a.2; omega⟩ else b

def pivotMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n) : R :=
  (M.submatrix (Fin.castLE (by have := a.2; omega)) (pivotCols a b)).det

def leadMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) : R :=
  pivotMinor M a (Fin.castLE (Nat.sub_le n 1) a)

def pivotMatrix {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun r b => if h : (r : ℕ) < n - 1 then pivotMinor M ⟨r, h⟩ b else 0

theorem pivotCols_strictMono {n : ℕ} (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    StrictMono (pivotCols a b) := by
  intro c d hcd
  have hcd' : (c : ℕ) < d := hcd
  simp only [pivotCols]
  split_ifs with h1 h2 h2
  · exact Fin.mk_lt_mk.mpr hcd'
  · exact Fin.mk_lt_mk.mpr (by omega)
  · omega
  · omega

theorem card_image_pivotCols {n : ℕ} (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    (Finset.univ.image (pivotCols a b)).card = a + 1 := by
  rw [Finset.card_image_of_injective _ (pivotCols_strictMono a b hab).injective, Finset.card_univ, Fintype.card_fin]

theorem pivotMinor_eq_flagMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hab : (a : ℕ) ≤ b) :
    pivotMinor M a b = flagMinor M a ⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab⟩ := by
  unfold pivotMinor flagMinor
  congr 2
  exact (Finset.orderEmbOfFin_unique (card_image_pivotCols a b hab) (fun c => Finset.mem_image_of_mem _ (Finset.mem_univ c))
    (pivotCols_strictMono a b hab))

theorem pivotMinor_eq_zero {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hba : (b : ℕ) < a) : pivotMinor M a b = 0 := by
  unfold pivotMinor
  refine Matrix.det_zero_of_column_eq (i := ⟨b, by omega⟩) (j := Fin.last a) (fun h => by
    have := congrArg Fin.val h; simp at this; omega) fun k => ?_
  simp [pivotCols, hba]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]



def genMap (P : Ideal (MRing ι)) {N1 : ℕ} {S : Type} [Fintype S] (v : S → Fin N1 → FnField P) :
    MRing (PBlk ι N1) →+* MvPolynomial S (FnField P) :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (genPt P ⟨k, i⟩)
    | ⟨.inr _, j⟩ => ∑ s, C (v s j) * X s



end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ChartNormCount.proof (hSC : ChartSpecCount.Statement) (hNP : ChartNormPts.Statement) :
    ChartNormCount.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G j hv hP' hZ hj hfin
  classical
  have hchar : CharZero G.Φ := by
    refine charZero_of_inj_zero fun N hN => ?_
    have hmem : (C (N : ℤ) : MRing ι) ∈ imageZ v P' := by
      rw [← G.ker_x, RingHom.mem_ker]
      simpa using hN
    have h2 : (N : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := hmem
    rw [hZ.2.2.1] at h2
    exact_mod_cast (Ideal.mem_bot.mp h2)
  obtain ⟨E, hE, hcount⟩ := hSC (MRing ι) G.Φ G.Φ' (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom _
    (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) G.gen hfin
  refine ⟨E, fun hm => hE ?_, fun w hw hEw => ?_⟩
  · rw [← G.ker_x] at hm
    exact hm
  have hker : RingHom.ker (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom ≤
      RingHom.ker (eval₂Hom (Int.castRingHom ℂ) w) := by
    intro f hf
    have hf' : f ∈ imageZ v P' := by
      rw [← G.ker_x]
      exact hf
    have h0 := hw.2 f hf'
    rw [RingHom.mem_ker, coe_eval₂Hom]
    rwa [eval_map] at h0
  have hψE : eval₂Hom (Int.castRingHom ℂ) w E ≠ 0 := by
    rwa [coe_eval₂Hom, ← eval_map]
  obtain ⟨hZfin, hZcard, hZne⟩ := hcount _ hker hψE
  have hmh : IsMultiHomogIdeal P' := hP'.2.1.2.1
  have hiff : ∀ z' : (Σ k', ι' k') → ℂ, (∀ p, z' (v p) = w p) → (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1) →
      (z' ∈ mcPts P' ↔ ∀ F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι),
        eval₂ ((algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom)
          (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) F = 0 →
        eval₂ (eval₂Hom (Int.castRingHom ℂ) w) (fun q => z' ⟨q.1.1, q.2⟩) F = 0) := by
    intro z' hzw hz1
    have hw' : (fun p => z' (v p)) = w := funext hzw
    have hwz : (fun p => z' (v p)) ∈ mcPts (imageZ v P') := by
      rw [hw']
      exact hw
    have h := hNP K ι K' ι' κ v P' G j hv hmh hj z' hwz hz1
    rw [hw'] at h
    exact h
  set Z := {y : (Σ k : FibreBlock κ, ι' k.1) → ℂ | ∀ F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι),
        eval₂ ((algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom)
          (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) F = 0 →
        eval₂ (eval₂Hom (Int.castRingHom ℂ) w) y F = 0} with hZdef
  set N := {z' | z' ∈ mcPts P' ∧ (∀ p, z' (v p) = w p) ∧ ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1} with hNdef
  let res : ((Σ k', ι' k') → ℂ) → (Σ k : FibreBlock κ, ι' k.1) → ℂ := fun z' q => z' ⟨q.1.1, q.2⟩
  have hinj : Set.InjOn res N := by
    intro a ha b hb hab
    funext q'
    obtain ⟨k', i⟩ := q'
    by_cases h : k' ∈ Set.range κ
    · obtain ⟨p, hp⟩ := hv.2.2.2 ⟨k', i⟩ h
      rw [← hp, ha.2.1 p, hb.2.1 p]
    · exact congrFun hab ⟨⟨k', h⟩, i⟩
  have himg : res '' N = Z := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z', hz', rfl⟩
      exact (hiff z' hz'.2.1 hz'.2.2).1 hz'.1
    · intro y hy
      have hy1 : ∀ k : FibreBlock κ, y ⟨k, j k⟩ = 1 := by
        intro k
        have h := hy (X ⟨k, j k⟩ - 1) (by simp [div_self (hj k)])
        simpa [sub_eq_zero] using h
      let z' : (Σ k', ι' k') → ℂ := fun q' =>
        if h : q'.1 ∈ Set.range κ then w (hv.2.2.2 q' h).choose else y ⟨⟨q'.1, h⟩, q'.2⟩
      have hzw : ∀ p, z' (v p) = w p := by
        intro p
        have h : (v p).1 ∈ Set.range κ := ⟨p.1, (hv.2.2.1 p).symm⟩
        have hc : (hv.2.2.2 (v p) h).choose = p := hv.2.1 (hv.2.2.2 (v p) h).choose_spec
        simp only [z', dif_pos h, hc]
      have hz1 : ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1 := by
        intro k
        simp only [z', dif_neg k.2]
        exact hy1 k
      have hres : res z' = y := by
        funext q
        simp only [res, z', dif_neg q.1.2]
      refine ⟨z', ⟨(hiff z' hzw hz1).2 ?_, hzw, hz1⟩, hres⟩
      have : (fun q : Σ k : FibreBlock κ, ι' k.1 => z' ⟨q.1.1, q.2⟩) = y := hres
      rw [this]
      exact hy
  refine ⟨Set.Finite.of_finite_image (himg ▸ hZfin) hinj, ?_, ?_⟩
  · rw [← hinj.ncard_image, himg]
    exact hZcard
  · intro z' hz' hzw hz1 q hq
    have hy := (hiff z' hzw hz1).1 hz'
    exact hZne _ hy q (div_ne_zero hq (hj q.1))

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Fibre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


open Classical in
def baseSubst (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P') :
    MRing ι' →+* MRingOver G.Φ (fibreIdx ι' κ) :=
  eval₂Hom (algebraMap ℤ _) fun q =>
    if h : q.1 ∈ Set.range κ then
      (if h' : q ∈ Set.range v then C (G.x h'.choose) else 0)
    else X ⟨⟨q.1, h⟩, q.2⟩

def fibreOf (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P')
    (W : Ideal (MRing ι')) : Ideal (MRingOver G.Φ (fibreIdx ι' κ)) :=
  Ideal.map (baseSubst κ G) W

end Fibre

def PFHoriz.Statement : Prop :=
  ∀ (I : AllFam) (r : ℕ), PFAt I r →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' W : Ideal (MRing ι')) (d : ℕ)
      (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
      (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
      IsBlockMap κ v → IsArithVar W (d + r) → imageZ v W = imageZ v P' → IsArithVar (imageZ v P') d →
      IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      (∀ j, IsSmoothHerm (N j)) →
      I K' ι' W (d + r) (Fin.append L' N) =
        (J (fibreOf κ G W) r (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L

end

end GroundTheory.Heights₂.Heights.Inter
end
