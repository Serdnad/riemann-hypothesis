module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle611
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Formalism.LocalToGlobal.NumberFieldFamilies.IdTransSM
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.UnitLemma.ShiftRes

def shiftPoly {F : Type} [Field F] (t s : F) (p : F[X]) : F[X] :=
  C (t ^ p.natDegree)⁻¹ * p.comp (C t * X + C s)

theorem natDegree_lin {F : Type} [Field F] (t s : F) (ht : t ≠ 0) : (C t * X + C s).natDegree = 1 := by
  rw [natDegree_add_C, natDegree_C_mul_X t ht]

theorem natDegree_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p : F[X]) :
    (shiftPoly t s p).natDegree = p.natDegree := by
  unfold shiftPoly
  rw [natDegree_C_mul (inv_ne_zero (pow_ne_zero _ ht)), natDegree_comp, natDegree_lin t s ht, mul_one]

theorem monic_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p : F[X]) (hp : p.Monic) :
    (shiftPoly t s p).Monic := by
  unfold shiftPoly Monic
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp (by rw [natDegree_lin t s ht]; exact one_ne_zero),
    hp.leadingCoeff, one_mul]
  have : (C t * X + C s).leadingCoeff = t := by
    rw [leadingCoeff, natDegree_lin t s ht]; simp
  rw [this, inv_mul_cancel₀ (pow_ne_zero _ ht)]

theorem map_shiftPoly {F L : Type} [Field F] [Field L] (φ : F →+* L) (t s : F) (p : F[X]) :
    (shiftPoly t s p).map φ = shiftPoly (φ t) (φ s) (p.map φ) := by
  unfold shiftPoly
  rw [Polynomial.map_mul, map_C, Polynomial.map_comp, natDegree_map]
  simp

theorem shiftPoly_mul {F : Type} [Field F] (t s : F) (p q : F[X]) (hp : p.Monic) (hq : q.Monic) :
    shiftPoly t s (p * q) = shiftPoly t s p * shiftPoly t s q := by
  unfold shiftPoly
  rw [hp.natDegree_mul hq, mul_comp, pow_add, mul_inv, C_mul]
  ring

theorem shiftPoly_eq_prod {L : Type} [Field L] [IsAlgClosed L] (t s : L) (ht : t ≠ 0) (p : L[X]) (hp : p.Monic) :
    shiftPoly t s p = ((p.roots.map fun α => (α - s) / t).map fun a => X - C a).prod := by
  have hsp := IsAlgClosed.splits p
  have hcard : Multiset.card p.roots = p.natDegree := hsp.natDegree_eq_card_roots.symm
  unfold shiftPoly
  conv_lhs => arg 2; rw [hsp.eq_prod_roots_of_monic hp]
  rw [multiset_prod_comp, Multiset.map_map, Multiset.map_map]
  have key : ∀ α : L, (X - C α).comp (C t * X + C s) = C t * (X - C ((α - s) / t)) := by
    intro α
    rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, mul_div_cancel₀ _ ht, C_sub]
    ring
  simp only [Function.comp_def, key]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard, ← C_pow, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ (pow_ne_zero _ ht), C_1, one_mul]

theorem resultant_shiftPoly_alg {L : Type} [Field L] [IsAlgClosed L] (t s : L) (ht : t ≠ 0) (p q : L[X])
    (hp : p.Monic) (hq : q.Monic) :
    resultant (shiftPoly t s p) (shiftPoly t s q) = (t ^ (p.natDegree * q.natDegree))⁻¹ * resultant p q := by
  have hcp : Multiset.card p.roots = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hcq : Multiset.card q.roots = q.natDegree := (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  rw [resultant_eq_prod_roots_sub _ _ (monic_shiftPoly t s ht p hp) (monic_shiftPoly t s ht q hq)
    (IsAlgClosed.splits _) (IsAlgClosed.splits _), resultant_eq_prod_roots_sub p q hp hq (IsAlgClosed.splits p)
    (IsAlgClosed.splits q), shiftPoly_eq_prod t s ht p hp, shiftPoly_eq_prod t s ht q hq,
    roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C, Multiset.prod_map_product_eq_prod_prod,
    Multiset.prod_map_product_eq_prod_prod]
  simp only [Multiset.map_map, Function.comp_def]
  have key : ∀ α β : L, (α - s) / t - (β - s) / t = t⁻¹ * (α - β) := by
    intro α β; field_simp; ring
  simp only [key]
  simp only [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcq]
  rw [hcp, ← pow_mul, inv_pow, mul_comm q.natDegree p.natDegree]

theorem resultant_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p q : F[X]) (hp : p.Monic) (hq : q.Monic) :
    resultant (shiftPoly t s p) (shiftPoly t s q) = (t ^ (p.natDegree * q.natDegree))⁻¹ * resultant p q := by
  let φ := algebraMap F (AlgebraicClosure F)
  apply φ.injective
  have e1 : φ (resultant (shiftPoly t s p) (shiftPoly t s q)) =
      resultant ((shiftPoly t s p).map φ) ((shiftPoly t s q).map φ) := by
    rw [resultant_map_map, natDegree_map, natDegree_map]
  have e2 : φ (resultant p q) = resultant (p.map φ) (q.map φ) := by
    rw [resultant_map_map, natDegree_map, natDegree_map]
  rw [e1, map_mul, e2, map_shiftPoly, map_shiftPoly,
    resultant_shiftPoly_alg _ _ ((_root_.map_ne_zero φ).2 ht) _ _ (hp.map φ) (hq.map φ), natDegree_map, natDegree_map,
    map_inv₀, map_pow]

theorem separable_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p : F[X]) (hp : p.Separable) :
    (shiftPoly t s p).Separable := by
  have h1 := IsCoprime.map hp (Polynomial.compRingHom (C t * X + C s))
  rw [Polynomial.coe_compRingHom_apply, Polynomial.coe_compRingHom_apply] at h1
  have h2 : IsCoprime (p.comp (C t * X + C s)) (C t) :=
    ⟨0, C t⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ ht, C_1]⟩
  have h3 : derivative (p.comp (C t * X + C s)) = (derivative p).comp (C t * X + C s) * C t := by
    rw [derivative_comp, derivative_add, derivative_C_mul_X, derivative_C, add_zero, mul_comm]
  have hc : (p.comp (C t * X + C s)).Separable := by
    show IsCoprime _ _
    rw [h3]
    exact h1.mul_right h2
  unfold shiftPoly
  have hu : IsUnit (C (t ^ p.natDegree)⁻¹ : F[X]) := isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ht)))
  show IsCoprime _ _
  rw [derivative_mul, derivative_C, zero_mul, zero_add]
  exact (isCoprime_mul_unit_left hu _ _).2 hc

theorem charpoly_eq_of_adjoin {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A] (x : A)
    (hx : Algebra.adjoin F ({x} : Set A) = ⊤) (p : F[X]) (hp : p.Monic) (hpx : aeval x p = 0)
    (hd : p.natDegree = Module.finrank F A) : (LinearMap.mulLeft F x).charpoly = p := by
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hmon := minpoly.monic hint
  have hCH : aeval x (LinearMap.mulLeft F x).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft F x)
    have h2 := Polynomial.aeval_algHom_apply (Algebra.lmul F A) x (LinearMap.mulLeft F x).charpoly
    have h3 : (Algebra.lmul F A) (aeval x (LinearMap.mulLeft F x).charpoly) = 0 := by rw [← h2]; exact h
    simpa using congrArg (fun f => f 1) h3
  have hcd : (LinearMap.mulLeft F x).charpoly.natDegree = Module.finrank F A := LinearMap.charpoly_natDegree _
  have hle : Module.finrank F A ≤ (minpoly F x).natDegree := by
    let pb := AdjoinRoot.powerBasis' hmon
    haveI : Module.Finite F (AdjoinRoot (minpoly F x)) := pb.finite
    let f := AdjoinRoot.liftAlgHom (minpoly F x) (Algebra.ofId F A) x
      (by rw [← minpoly.aeval F x, aeval_def]; rfl)
    have hs : Function.Surjective f := by
      intro y
      have hy : y ∈ Algebra.adjoin F ({x} : Set A) := hx ▸ Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨r, rfl⟩ := hy
      exact ⟨AdjoinRoot.mk _ r, by rw [AdjoinRoot.liftAlgHom_mk]; rfl⟩
    have h1 := LinearMap.finrank_range_le f.toLinearMap
    rw [LinearMap.range_eq_top.2 hs, finrank_top, pb.finrank, AdjoinRoot.powerBasis'_dim] at h1
    exact h1
  have h1 : p = minpoly F x :=
    eq_of_monic_of_dvd_of_natDegree_le hmon hp (minpoly.dvd F x hpx) (by omega)
  have h2 : (LinearMap.mulLeft F x).charpoly = minpoly F x :=
    eq_of_monic_of_dvd_of_natDegree_le hmon (LinearMap.charpoly_monic _) (minpoly.dvd F x hCH) (by omega)
  rw [h2, h1]

theorem val_inv_pow_mul {K : UQ} {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    val K.O ((x ^ n)⁻¹ * y) = val K.O y - n * val K.O x := by
  unfold val
  have h1 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E ((x ^ n)⁻¹) ≠ 0 := by simp [hx]
  have h2 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E y ≠ 0 := by simp [hy]
  rw [map_mul, WithZero.log_mul h1 h2, map_inv₀, map_pow, WithZero.log_inv, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem val_resultant_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (k : ℕ) (t : K.O), t ≠ 0 → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (B₁.P * B₂.P).Separable ∧ GlobalTheory.UnitLemma.val K.O (resultant B₁.P B₂.P) = ordL (resultant Q₁ Q₂) - ((k * a * b : ℕ) : ℤ) := by
  intro E _ _ _ w K e hval k t ht hk a b Q₁ Q₂ B₁ B₂ hm₁ hm₂ ha hb hsep hadj₁ hQ₁ hf₁ hadj₂ hQ₂ hf₂
  set t' : K.E := algebraMap K.O K.E t with ht'def
  have ht' : t' ≠ 0 := by
    rw [ht'def]; exact (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ht
  have hP : ∀ (B : InvAlg K) (Q : (w.adicCompletion E)[X]), Q.Monic →
      Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ →
      aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 →
      Module.finrank K.E B.A = Q.natDegree → B.P = shiftPoly t' 1 (Q.map e.symm.toRingHom) := by
    intro B Q hQm hadj hQ hfin
    have hd : (Q.map e.symm.toRingHom).natDegree = Q.natDegree := natDegree_map _
    have hu : aeval B.g (C t' * X + C 1) = 1 + algebraMap K.O B.A t * B.g := by
      rw [map_add (f := _), map_mul, aeval_C, aeval_X, aeval_C, map_one, ht'def, ← IsScalarTower.algebraMap_apply]
      ring
    unfold InvAlg.P
    apply charpoly_eq_of_adjoin
    · rw [eq_top_iff, ← hadj]
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff, ← hu]
      exact aeval_mem_adjoin_singleton _ _
    · exact monic_shiftPoly t' 1 ht' _ (hQm.map _)
    · unfold shiftPoly
      rw [map_mul, aeval_C, aeval_comp, hu, hQ, mul_zero]
    · rw [natDegree_shiftPoly t' 1 ht', hd, hfin]
  have e₁ := hP B₁ Q₁ hm₁ hadj₁ hQ₁ hf₁
  have e₂ := hP B₂ Q₂ hm₂ hadj₂ hQ₂ hf₂
  have hm₁' : (Q₁.map e.symm.toRingHom).Monic := hm₁.map _
  have hm₂' : (Q₂.map e.symm.toRingHom).Monic := hm₂.map _
  refine ⟨?_, ?_⟩
  · rw [e₁, e₂, ← shiftPoly_mul t' 1 _ _ hm₁' hm₂', ← Polynomial.map_mul]
    exact separable_shiftPoly t' 1 ht' _ hsep.map
  · rw [e₁, e₂, resultant_shiftPoly t' 1 ht' _ _ hm₁' hm₂']
    have hR : resultant (Q₁.map e.symm.toRingHom) (Q₂.map e.symm.toRingHom) = e.symm (resultant Q₁ Q₂) := by
      rw [resultant_map_map, natDegree_map, natDegree_map]; rfl
    have hR0 : resultant Q₁ Q₂ ≠ 0 := resultant_ne_zero _ _ hsep.isCoprime
    rw [hR, natDegree_map, natDegree_map, val_inv_pow_mul ht' ((_root_.map_ne_zero _).2 hR0), hval, RingEquiv.apply_symm_apply, hk, ha, hb]
    push_cast; ring

end GlobalTheory.UnitLemma.ShiftRes
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.InvAlgConstr

theorem exists_invAlg_adjoinRoot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (t : K.O), t ≠ 0 → ∀ Q : (w.adicCompletion E)[X], Q.Monic → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ ∧ aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 ∧ Module.finrank K.E B.A = Q.natDegree ∧ (1 + algebraMap K.O B.A t * B.g) * B.σ (1 + algebraMap K.O B.A t * B.g) = 1 := by
  intro E _ _ _ w hw K e he t ht Q hQ hcsr
  set Q' : K.E[X] := Q.map e.symm.toRingHom with hQ'
  have hinj : Function.Injective (e.symm.toRingHom) := e.symm.injective
  have hQ'm : Q'.Monic := hQ.map _
  have hdeg : Q'.natDegree = Q.natDegree := natDegree_map_eq_of_injective hinj _
  have hc := hcsr.resolve_left hw
  have hQ0 : Q.coeff 0 ≠ 0 := by
    intro h0
    rw [h0, map_zero, C_0, zero_mul] at hc
    exact (hQ.map (cj w)).ne_zero (reverse_eq_zero.mp hc.symm)
  have hQ'0 : Q'.coeff 0 ≠ 0 := by
    rw [hQ', coeff_map]
    exact fun h => hQ0 (hinj (by rw [h, map_zero]))
  let A := AdjoinRoot Q'
  let r : A := AdjoinRoot.root Q'
  let pb := AdjoinRoot.powerBasis' hQ'm
  haveI : Module.Finite K.E A := pb.finite
  have hr0 : aeval r Q' = 0 := by
    rw [aeval_def, AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.eval₂_root Q'
  set v : A := -(aeval r (divX Q')) * algebraMap K.E A (Q'.coeff 0)⁻¹ with hv
  have hrv : r * v = 1 := by
    have h1 := congrArg (aeval r) (X_mul_divX_add Q')
    rw [map_add (f := _), map_mul, aeval_X, aeval_C, hr0] at h1
    have h2 : algebraMap K.E A (Q'.coeff 0) * algebraMap K.E A (Q'.coeff 0)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hQ'0, map_one]
    linear_combination (-(algebraMap K.E A (Q'.coeff 0)⁻¹)) * h1 + h2
  letI : Invertible v := ⟨r, hrv, by rw [mul_comm]; exact hrv⟩
  have hce : ∀ y, K.c (e.symm y) = e.symm (cj w y) := by
    intro y; apply e.injective; rw [he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hmapc : Q'.map K.c.toRingHom = (Q.map (cj w)).map e.symm.toRingHom := by
    rw [hQ', Polynomial.map_map, Polynomial.map_map]; congr 1; ext y; exact hce y
  have hrev : (Q'.map K.c.toRingHom).reverse = C (e.symm (cj w (Q.coeff 0))) * Q' := by
    rw [hmapc]
    unfold reverse
    rw [natDegree_map_eq_of_injective hinj, reflect_map, ← reverse, ← hc, Polynomial.map_mul, map_C]
    rfl
  have hev : eval₂ ((algebraMap K.E A).comp K.c.toRingHom) v Q' = 0 := by
    rw [← eval₂_map, ← eval₂_reverse_mul_pow (algebraMap K.E A) v, hrev]
    show eval₂ (algebraMap K.E A) r (C (e.symm (cj w (Q.coeff 0))) * Q') * _ = 0
    have hev0 : eval₂ (algebraMap K.E A) r Q' = 0 := by rw [← aeval_def]; exact hr0
    rw [eval₂_mul, hev0, mul_zero, zero_mul]
  let σ0 : A →+* A := AdjoinRoot.lift ((algebraMap K.E A).comp K.c.toRingHom) v hev
  have hσr : σ0 r = v := AdjoinRoot.lift_root hev
  have hσof : ∀ a, σ0 (algebraMap K.E A a) = algebraMap K.E A (K.c a) := fun a => AdjoinRoot.lift_of hev
  have hσv : σ0 v = r := by
    calc σ0 v = σ0 v * (r * v) := by rw [hrv, mul_one]
      _ = σ0 (r * v) * r := by rw [map_mul σ0 r v, hσr]; ring
      _ = r := by rw [hrv, map_one, one_mul]
  have hcomp : σ0.comp σ0 = RingHom.id A := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro a
      show σ0 (σ0 (algebraMap K.E A a)) = algebraMap K.E A a
      rw [hσof, hσof]; simp [K.c_c]
    · show σ0 (σ0 r) = r
      rw [hσr, hσv]
  have hσσ : ∀ y, σ0 (σ0 y) = y := fun y => RingHom.congr_fun hcomp y
  let σ : A ≃+* A :=
    { toFun := σ0, invFun := σ0, left_inv := hσσ, right_inv := hσσ, map_mul' := map_mul σ0, map_add' := map_add σ0 }
  set tE : K.E := algebraMap K.O K.E t
  have htE : tE ≠ 0 := fun h => ht ((IsFractionRing.injective K.O K.E) (by rw [map_zero]; exact h))
  let B : GlobalTheory.UnitLemma.InvAlg K :=
    { A := A, σ := σ, σ_σ := hσσ, σ_alg := hσof, g := (r - 1) * algebraMap K.E A tE⁻¹ }
  have hu : (1 + algebraMap K.O B.A t * B.g) = r := by
    show (1 + algebraMap K.O A t * ((r - 1) * algebraMap K.E A tE⁻¹)) = r
    rw [IsScalarTower.algebraMap_apply K.O K.E A t]
    have h3 : algebraMap K.E A tE * algebraMap K.E A tE⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ htE, map_one]
    linear_combination (r - 1) * h3
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · rw [hu]; exact AdjoinRoot.adjoinRoot_eq_top
  · rw [hu]; exact hr0
  · show Module.finrank K.E A = Q.natDegree
    rw [pb.finrank, AdjoinRoot.powerBasis'_dim, hdeg]
  · rw [hu]
    show r * σ0 r = 1
    rw [hσr, hrv]

end GlobalTheory.InvAlgConstr
end

section

noncomputable section

open NumberField GlobalTheory.BCT GlobalTheory.CuspRep Matrix
open scoped Classical

namespace GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def mulMat (a : B.A) : Matrix (Fin m) (Fin m) (w.adicCompletion E) :=
  (LinearMap.toMatrix b b (LinearMap.mulLeft K.E a)).map e

def gram (β : B.A) : Matrix (Fin m) (Fin m) (w.adicCompletion E) :=
  Matrix.of fun i j => e (B.herm β (b i) (b j))

def dlt (β : B.A) : GLw m w :=
  if h : IsUnit (gram e b β) then invT m _ h.unit * (PhiU m _)⁻¹ else 1

def lat (g : GLw m w) : Submodule K.O B.A :=
  Submodule.span K.O (Set.range fun j => ∑ i, e.symm (g.val i j) • b i)

end GlobalTheory.TwLat
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AbsHalfLevi

theorem absHalf_det_div_eq_deltaHalf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m : GLw a w × GLw b w), absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) : ℂ) := by
  intro E _ _ _ a b w m
  rw [GlobalTheory.SmGL.deltaHalf_two, Units.val_mul]
  have e1 : m.1.val.det = ((GeneralLinearGroup.det m.1 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    simp [GeneralLinearGroup.val_det_apply]
  have e2 : m.2.val.det = ((GeneralLinearGroup.det m.2 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    simp [GeneralLinearGroup.val_det_apply]
  rw [e1, e2]
  generalize GeneralLinearGroup.det m.1 = d1
  generalize GeneralLinearGroup.det m.2 = d2
  have n1 := GlobalTheory.LGrp.BorelCompletion.nabs_completion w d1
  have n2 := GlobalTheory.LGrp.BorelCompletion.nabs_completion w d2
  have hb : ((Fintype.card (Fin b) : ℂ) / 2) = (((b : ℝ) / 2 : ℝ) : ℂ) := by simp
  have ha : (-(Fintype.card (Fin a) : ℂ) / 2) = ((-(a : ℝ) / 2 : ℝ) : ℂ) := by simp
  rw [hb, ha, GlobalTheory.SmGL.val_absPow_ofReal, GlobalTheory.SmGL.val_absPow_ofReal, n1, n2, ← Complex.ofReal_mul]
  unfold absHalf
  congr 1
  have hd1 : ((d1 : w.adicCompletion E)) ≠ 0 := d1.ne_zero
  have hd2 : ((d2 : w.adicCompletion E)) ≠ 0 := d2.ne_zero
  have hx : ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) ≠ 0 := by
    exact div_ne_zero (pow_ne_zero _ hd1) (pow_ne_zero _ hd2)
  have hv1 : Valued.v (d1 : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd1
  have hv2 : Valued.v (d2 : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd2
  have hord : ordL ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) =
      -((b : ℤ) * WithZero.log (Valued.v (d1 : w.adicCompletion E)) - (a : ℤ) * WithZero.log (Valued.v (d2 : w.adicCompletion E))) := by
    have hv : Valued.v ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    unfold ordL
    rw [dite_eq_right hv, WithZero.toAdd_unzero_eq_log, map_div₀, map_pow, map_pow,
      WithZero.log_div (pow_ne_zero _ hv1) (pow_ne_zero _ hv2), WithZero.log_pow, WithZero.log_pow]
    simp
  rw [hord, neg_neg]
  have hq : (0 : ℝ) < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV; exact (Ideal.absNorm_eq_zero_iff).not.mpr w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  generalize WithZero.log (Valued.v (d1 : w.adicCompletion E)) = l1
  generalize WithZero.log (Valued.v (d2 : w.adicCompletion E)) = l2
  generalize (qV E w : ℝ) = q at hq ⊢
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

end GlobalTheory.AbsHalfLevi
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.OrbitCptW

theorem orbit_cpt_w : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (N : GLw n w), N.val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ x : GLw n w, x⁻¹ * N * x ∈ C → ∃ z : GLw n w, z * N = N * z ∧ ∃ d ∈ D, x = z * d := by
  intro E _ _ _ _ n w N hN C hC
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  obtain ⟨C', hC', hC'g⟩ := GlobalTheory.OrbCpt.gl_orbit_cpt (k := w.adicCompletion E) N.val hN
    ((fun y : GLw n w => (y : Matrix (Fin n) (Fin n) (w.adicCompletion E))) '' C)
    (hC.image Units.continuous_val)
  refine ⟨(fun y => y⁻¹) '' C', hC'.image continuous_inv, fun x hx => ?_⟩
  obtain ⟨c, hc, t, ht, hxt⟩ := hC'g x⁻¹ ⟨_, hx, by simp [mul_assoc]⟩
  refine ⟨t⁻¹, ?_, c⁻¹, ⟨c, hc, rfl⟩, ?_⟩
  · have h1 : t * N = N * t := Units.ext ht
    calc t⁻¹ * N = t⁻¹ * (N * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * N) * t⁻¹ := by rw [h1]
      _ = N * t⁻¹ := by group
  · rw [← _root_.mul_inv_rev, ← hxt, inv_inv]

end GlobalTheory.OrbitCptW
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HCharUnit

theorem locK_eq_one {E : Type} [Field E] [NumberField E] (χ : HChar E) (k : Eˣ) (v : HeightOneSpectrum (𝓞 E))
    (hu : χ.UnrAt v) (ho : ordF v k = 0) : χ.locK v k = 1 := by
  apply hu
  show Valued.v (((k : E) : v.adicCompletion E)) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have h0 : v.valuation E (k : E) ≠ 0 := by simp
  have hl : WithZero.log (v.valuation E (k : E)) = 0 := by
    unfold ordF at ho; omega
  rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]

theorem finprod_locK_mul_inf : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (k : Eˣ),
    (Function.mulSupport fun w : Pl E => χ.locK w k).Finite ∧ (∏ᶠ w : Pl E, χ.locK w k) * χ.inf k = 1 := by
  intro E _ _ χ k
  have hT : ({v | ¬ χ.UnrAt v} ∪ {v : HeightOneSpectrum (𝓞 E) | ordF v k ≠ 0}).Finite :=
    Set.Finite.union (Filter.eventually_cofinite.mp (Formalism.L2.Fam.IdTrans.unrAe χ)) (GlobalTheory.HeckeProduct.finite_ordF k)
  set S := hT.toFinset with hSdef
  have hsub : (Function.mulSupport fun w : Pl E => χ.locK w k) ⊆ (S : Set (HeightOneSpectrum (𝓞 E))) := by
    intro v hv
    rw [hSdef, Set.Finite.coe_toFinset]
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hv (locK_eq_one χ k v h.1 h.2)
  refine ⟨S.finite_toSet.subset hsub, ?_⟩
  have hS : ∀ v, v ∉ S → χ.UnrAt v := by
    intro v hv
    by_contra h
    exact hv (by rw [hSdef, Set.Finite.mem_toFinset]; exact Or.inl h)
  have hpr := Formalism.L2.Host.HChar.productRule χ S hS k
  have hrest : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [finprod_eq_if]
    split_ifs with hv
    · rfl
    have : ordF v k = 0 := by
      by_contra h
      exact hv (by rw [hSdef, Set.Finite.mem_toFinset]; exact Or.inr h)
    rw [this, zpow_zero]
  rw [hrest, mul_one] at hpr
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, mul_comm]
  exact hpr

end GlobalTheory.HCharUnit
end
end
