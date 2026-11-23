module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormPoly
import GroundTheory.LocalFields.Uniqueness
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle006
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.Bundle001
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.DZA GlobalTheory.LBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section Alg

variable {n : ℕ}

private theorem map_aeval_matrix {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) (p : R[X]) :
    (aeval A p).map f = aeval (A.map f) (p.map f) := by
  have h := Polynomial.hom_eval₂ p (algebraMap R (Matrix (Fin n) (Fin n) R))
    (f.mapMatrix (m := Fin n)) A
  have hc : (f.mapMatrix (m := Fin n)).comp (algebraMap R (Matrix (Fin n) (Fin n) R)) =
      (algebraMap S (Matrix (Fin n) (Fin n) S)).comp f := by
    ext x i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply, apply_ite f]
  rw [hc] at h
  rw [aeval_def, aeval_def, eval₂_map]
  exact h

private theorem commute_aeval {R : Type} [CommRing R] {x A : Matrix (Fin n) (Fin n) R}
    (h : Commute x A) (p : R[X]) : Commute x (aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial m a =>
    rw [aeval_monomial]
    exact Commute.mul_right (Algebra.commutes a x).symm (h.pow_right m)

private theorem conj_aeval {R : Type} [CommRing R] (g : GL (Fin n) R)
    (A : Matrix (Fin n) (Fin n) R) (p : R[X]) :
    ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * aeval A p * (g : Matrix (Fin n) (Fin n) R) =
      aeval (((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * A * (g : Matrix (Fin n) (Fin n) R)) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), ← hp, ← hq, mul_add, add_mul]
  | monomial m a =>
    rw [aeval_monomial, aeval_monomial, Units.conj_pow']
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]

end Alg

section Int

variable {K : Type} [Field K] [ValuativeRel K]

private theorem lifts_of_int (q : K[X]) (h : ∀ i, valuation K (q.coeff i) ≤ 1) :
    q ∈ Polynomial.lifts (algebraMap 𝒪[K] K) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro i
  exact ⟨⟨_, (Valuation.mem_integer_iff _ _).2 (h i)⟩, rfl⟩

private theorem lift_aeval {n : ℕ} (Y : Matrix (Fin n) (Fin n) 𝒪[K]) {q : K[X]}
    (h : q ∈ Polynomial.lifts (algebraMap 𝒪[K] K)) :
    ∃ C : Matrix (Fin n) (Fin n) 𝒪[K], C.map (algebraMap 𝒪[K] K) = aeval (Y.map (algebraMap 𝒪[K] K)) q := by
  obtain ⟨q', rfl⟩ := (Polynomial.mem_lifts _).1 h
  exact ⟨aeval Y q', map_aeval_matrix _ Y q'⟩

end Int

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.goodDelta :
    UpperTheory.Gal.InertialTypesAlt.L.GoodDelta := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ _ F₀ F₁ _ _ _ _ _ rk rK s sb h n γ hγ
  set G : Matrix (Fin n) (Fin n) k := (γ : Matrix (Fin n) (Fin n) k) with hG
  have hmon : G.charpoly.Monic := Matrix.charpoly_monic G
  have h0 : valuation k (G.charpoly.coeff 0) = 1 := by
    have e := Matrix.det_eq_sign_charpoly_coeff G
    have hv := hγ.2
    rw [← hG, e, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul] at hv
    exact hv
  obtain ⟨p, hp, hdvd⟩ := UpperTheory.Gal.InertialTypesAlt.L.normPoly k K F₀ F₁ rk rK s sb h G.charpoly hmon hγ.1 h0
  set A : Matrix (Fin n) (Fin n) K := (incl K n γ : Matrix (Fin n) (Fin n) K) with hA
  have hAG : A = G.map (algebraMap k K) := rfl
  let ps : ℕ → K[X] := fun i => p.map ((s ^ i : K ≃ₐ[k] K) : K →+* K)
  have hprod : aeval A (∏ i ∈ Finset.range (Module.finrank k K), ps i) = A := by
    obtain ⟨q, hq⟩ := hdvd
    have hz : aeval A (G.charpoly.map (algebraMap k K)) = 0 := by
      rw [← Matrix.charpoly_map, ← hAG]
      exact Matrix.aeval_self_charpoly A
    have e := congrArg (aeval A) hq
    rw [map_sub, aeval_X, map_mul, hz, zero_mul, sub_eq_zero] at e
    exact e
  have hAs : ∀ i, A.map ((s ^ i : K ≃ₐ[k] K) : K →+* K) = A := by
    intro i
    ext a b
    exact (s ^ i : K ≃ₐ[k] K).commutes ((γ : Matrix (Fin n) (Fin n) k) a b)
  have hmapps : ∀ i, (aeval A p).map ((s ^ i : K ≃ₐ[k] K) : K →+* K) = aeval A (ps i) := fun i => by
    have e := map_aeval_matrix ((s ^ i : K ≃ₐ[k] K) : K →+* K) A p
    rwa [hAs] at e
  obtain ⟨e, he⟩ : ∃ e, Module.finrank k K = e + 1 :=
    Nat.exists_eq_succ_of_ne_zero Module.finrank_pos.ne'
  let r : K[X] := ∏ i ∈ Finset.range e, ps (i + 1)
  have hps0 : ps 0 = p := by
    show p.map ((s ^ 0 : K ≃ₐ[k] K) : K →+* K) = p
    rw [pow_zero]
    exact Polynomial.map_id
  have hpr : aeval A (p * r) = A := by
    have e' := hprod
    rw [he, Finset.prod_range_succ', hps0, mul_comm] at e'
    exact e'
  have hδ1 : aeval A p * (aeval A r * (((incl K n γ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
    rw [← mul_assoc, ← map_mul (aeval A), hpr]
    exact Units.mul_inv _
  let δ : GL (Fin n) K := ⟨aeval A p, aeval A r * (((incl K n γ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
    hδ1, mul_eq_one_comm.1 hδ1⟩
  refine ⟨δ, ?_, ?_, ?_⟩
  · apply Units.ext
    have hj : ∀ j : Fin (Module.finrank k K),
        ((galAct (s ^ (j : ℕ)) n δ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = aeval A (ps j) :=
      fun j => hmapps j
    have e1 : ((List.ofFn fun j : Fin (Module.finrank k K) => galAct (s ^ (j : ℕ)) n δ).prod : GL (Fin n) K).val =
        (List.ofFn fun j : Fin (Module.finrank k K) => ((galAct (s ^ (j : ℕ)) n δ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).prod := by
      have e' := map_list_prod (Units.coeHom (Matrix (Fin n) (Fin n) K))
        (List.ofFn fun j : Fin (Module.finrank k K) => galAct (s ^ (j : ℕ)) n δ)
      rw [List.map_ofFn] at e'
      exact e'
    have e2 : (List.ofFn fun j : Fin (Module.finrank k K) => aeval A (ps j)).prod =
        aeval A (List.ofFn fun j : Fin (Module.finrank k K) => ps j).prod := by
      have e' := map_list_prod (aeval A) (List.ofFn fun j : Fin (Module.finrank k K) => ps j)
      rw [List.map_ofFn] at e'
      exact e'.symm
    have e3 : (List.ofFn fun j : Fin (Module.finrank k K) => ps j).prod =
        ∏ i ∈ Finset.range (Module.finrank k K), ps i := by
      rw [List.prod_ofFn, Fin.prod_univ_eq_prod_range ps]
    show ((List.ofFn fun j : Fin (Module.finrank k K) => galAct (s ^ (j : ℕ)) n δ).prod : GL (Fin n) K).val = A
    rw [e1]
    simp only [hj]
    rw [e2, e3, hprod]
  · intro x hx
    exact Commute.units_val_iff.1 (commute_aeval (Commute.units_val_iff.2 hx) p)
  · rintro g ⟨y, hy⟩
    have hB : (y : Matrix (Fin n) (Fin n) 𝒪[K]).map (algebraMap 𝒪[K] K) =
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A * (g : Matrix (Fin n) (Fin n) K) :=
      congrArg Units.val hy
    have hlp : p ∈ Polynomial.lifts (algebraMap 𝒪[K] K) := lifts_of_int p hp
    have hlr : r ∈ Polynomial.lifts (algebraMap 𝒪[K] K) :=
      Subsemiring.prod_mem _ fun i _ => lifts_of_int _ fun j => by
        rw [Polynomial.coeff_map]
        show valuation K ((s ^ (i + 1) : K ≃ₐ[k] K) (p.coeff j)) ≤ 1
        rw [GroundTheory.LocalField.valuation_algEquiv_apply k K]
        exact hp j
    obtain ⟨Cp, hCp⟩ := lift_aeval (y : Matrix (Fin n) (Fin n) 𝒪[K]) hlp
    obtain ⟨Cr, hCr⟩ := lift_aeval (y : Matrix (Fin n) (Fin n) 𝒪[K]) hlr
    have inj : Function.Injective fun M : Matrix (Fin n) (Fin n) 𝒪[K] => M.map (algebraMap 𝒪[K] K) :=
      Matrix.map_injective Subtype.val_injective
    have h1 : Cp * (Cr * ((y⁻¹ : GL (Fin n) 𝒪[K]) : Matrix (Fin n) (Fin n) 𝒪[K])) = 1 := by
      apply inj
      show (Cp * (Cr * ((y⁻¹ : GL (Fin n) 𝒪[K]) : Matrix (Fin n) (Fin n) 𝒪[K]))).map (algebraMap 𝒪[K] K) =
        (1 : Matrix (Fin n) (Fin n) 𝒪[K]).map (algebraMap 𝒪[K] K)
      rw [Matrix.map_mul, Matrix.map_mul, hCp, hCr, ← mul_assoc,
        ← map_mul (aeval ((y : Matrix (Fin n) (Fin n) 𝒪[K]).map (algebraMap 𝒪[K] K))), hB, ← conj_aeval, hpr,
        ← hB, ← Matrix.map_mul, Units.mul_inv]
    refine ⟨⟨Cp, Cr * ((y⁻¹ : GL (Fin n) 𝒪[K]) : Matrix (Fin n) (Fin n) 𝒪[K]), h1, mul_eq_one_comm.1 h1⟩, ?_⟩
    apply Units.ext
    show Cp.map (algebraMap 𝒪[K] K) =
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * aeval A p * (g : Matrix (Fin n) (Fin n) K)
    rw [hCp, hB, conj_aeval]
end
end

section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem sg_cont {σ : E ≃+* E} (hσ : Isom σ) : Continuous (sg σ : GL (Fin n) E → GL (Fin n) E) := by
  have hc : Continuous (σ : E → E) := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, (IsValuativeTopology.hasBasis_nhds x).tendsto_iff
      (IsValuativeTopology.hasBasis_nhds (σ x))]
    intro γ _
    refine ⟨γ, trivial, fun z hz => ?_⟩
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [← map_sub, hσ]
    exact hz
  exact Continuous.units_map _ (continuous_id.matrix_map hc)

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem map_diag {F : Type} [Field F] (f : E →+* F) (u : Fin n → Eˣ) :
    Matrix.GeneralLinearGroup.map f (diagT E (Fin n) u) = diagT F (Fin n) fun i => Units.map (f : E →* F) (u i) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, val_diagT, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.diagonal_apply]
  split_ifs <;> simp

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem diag_comm (u v : Fin n → Eˣ) :
    diagT E (Fin n) u * diagT E (Fin n) v = diagT E (Fin n) v * diagT E (Fin n) u := by
  rw [← map_mul, ← map_mul, mul_comm]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem diag_inj {u v : Fin n → Eˣ} (h : diagT E (Fin n) u = diagT E (Fin n) v) : u = v := by
  funext i
  have h1 := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) h
  simp only [val_diagT, Matrix.diagonal_apply_eq] at h1
  exact Units.ext h1

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem sg_diag (σ : E ≃+* E) (p : Fin n → Eˣ) :
    sg σ (diagT E (Fin n) p) = diagT E (Fin n) (sgT σ p) := by
  exact map_diag (σ : E →+* E) p

private theorem cent_diag {σ : E ≃+* E} {q : ℕ} (hσ : Cyc σ q) {d : Fin n → Eˣ} (hd : Strict d) {δ y c : GL (Fin n) E}
    (hy : y⁻¹ * δ * sg σ y = diagT E (Fin n) d) (hc : c⁻¹ * δ * sg σ c = δ) : ∃ u, y⁻¹ * c * y = diagT E (Fin n) u := by
  have hc2 : δ * sg σ c = c * δ := by
    calc δ * sg σ c = c * (c⁻¹ * δ * sg σ c) := by group
      _ = c * δ := by rw [hc]
  have key : (y⁻¹ * c * y)⁻¹ * diagT E (Fin n) d * sg σ (y⁻¹ * c * y) = diagT E (Fin n) d := by
    rw [← hy]
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
    rw [← mul_assoc δ, hc2]
    simp only [mul_assoc, inv_mul_cancel_left]
  exact strictNormal E n σ q hσ d d hd hd _ key

private theorem diag_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (h : Near r s) : diagT E (Fin n) s ∈ ball n r := by
  intro i j
  rw [val_diagT]
  by_cases hij : i = j
  · subst hij
    simpa using h i
  · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]

private theorem near_of_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (h : diagT E (Fin n) s ∈ ball n r) : Near r s := by
  intro i
  have h1 := h i i
  simpa [val_diagT, Matrix.diagonal_apply_eq] using h1

end

theorem UpperTheory.Gal.InertialTypesAlt.L.oneField :
    UpperTheory.Gal.InertialTypesAlt.L.OneField := by
  intro E _ _ _ _ n σ q hσ r hr0 hr1 _ _ μ hμ A hA δ y d hd hy H hH ν hν R hR hRd
  obtain ⟨K, hK, hKo, hKc⟩ := ballSub E n r hr0 hr1
  have hsupp := (suppE E n σ q hσ r hr0 hr1 A hA).2 δ y d hd hy
  have hδ : δ = y * diagT E (Fin n) d * (sg σ y)⁻¹ := by
    rw [← hy]
    group
  have hfix : ∀ w, (y * diagT E (Fin n) w * y⁻¹)⁻¹ * δ * sg σ (y * diagT E (Fin n) w * y⁻¹) = δ ↔
      sgT σ w = w := by
    intro w
    have e : (y * diagT E (Fin n) w * y⁻¹)⁻¹ * δ * sg σ (y * diagT E (Fin n) w * y⁻¹) =
        y * ((diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)) * (sg σ y)⁻¹ := by
      rw [hδ, map_mul, map_mul, map_inv, sg_diag]
      group
    rw [e]
    constructor
    · intro h
      conv_rhs at h => rw [hδ]
      have h2 : (diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w) = diagT E (Fin n) d :=
        mul_left_cancel (mul_right_cancel h)
      have h3 : diagT E (Fin n) d * diagT E (Fin n) (sgT σ w) = diagT E (Fin n) d * diagT E (Fin n) w := by
        calc diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)
            = diagT E (Fin n) w * ((diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)) := by
              group
          _ = diagT E (Fin n) w * diagT E (Fin n) d := by rw [h2]
          _ = diagT E (Fin n) d * diagT E (Fin n) w := diag_comm w d
      exact diag_inj (mul_left_cancel h3)
    · intro h
      rw [h, hδ, mul_assoc (diagT E (Fin n) w)⁻¹, diag_comm d w]
      group
  have hcen : ∀ c ∈ H, ∃ u, y⁻¹ * c * y = diagT E (Fin n) u :=
    fun c hc => cent_diag hσ hd hy ((hH c).1 hc)
  have hback : ∀ c u, y⁻¹ * c * y = diagT E (Fin n) u → c = y * diagT E (Fin n) u * y⁻¹ := by
    intro c u hu
    rw [← hu]
    group
  have hfixH : ∀ c ∈ H, ∀ u, y⁻¹ * c * y = diagT E (Fin n) u → sgT σ u = u := by
    intro c hc u hu
    apply (hfix u).1
    rw [← hback c u hu]
    exact (hH c).1 hc
  have hclosed : IsClosed (H : Set (GL (Fin n) E)) := by
    have hset : (H : Set (GL (Fin n) E)) = {c | c⁻¹ * δ * sg σ c = δ} := Set.ext hH
    rw [hset]
    exact isClosed_eq ((continuous_inv.mul continuous_const).mul (sg_cont hσ.isom)) continuous_const
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, Commute a b := by
    intro a ha b hb
    obtain ⟨u, hu⟩ := hcen a ha
    obtain ⟨v, hv⟩ := hcen b hb
    rw [hback a u hu, hback b v hv]
    show y * diagT E (Fin n) u * y⁻¹ * (y * diagT E (Fin n) v * y⁻¹) =
      y * diagT E (Fin n) v * y⁻¹ * (y * diagT E (Fin n) u * y⁻¹)
    calc y * diagT E (Fin n) u * y⁻¹ * (y * diagT E (Fin n) v * y⁻¹)
        = y * (diagT E (Fin n) u * diagT E (Fin n) v) * y⁻¹ := by group
      _ = y * (diagT E (Fin n) v * diagT E (Fin n) u) * y⁻¹ := by rw [diag_comm u v]
      _ = y * diagT E (Fin n) v * y⁻¹ * (y * diagT E (Fin n) u * y⁻¹) := by group
  have hV : ∀ ρ ∈ R, ∀ h : H, h ∈ {h : H | y⁻¹ * ↑h * y ∈ ball n r} ↔
      (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ) ∈ K := by
    intro ρ _ h
    obtain ⟨u, hu⟩ := hcen h h.2
    have e : (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ) = y⁻¹ * ↑h * y := by
      calc (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ)
          = (diagT E (Fin n) ρ)⁻¹ * (y⁻¹ * ↑h * y) * diagT E (Fin n) ρ := by group
        _ = y⁻¹ * ↑h * y := by
          rw [hu, mul_assoc, diag_comm u ρ, inv_mul_cancel_left]
    rw [Set.mem_setOf_eq, e, ← SetLike.mem_coe, hK]
  have hS : ∀ g, g ∈ {g : GL (Fin n) E | g⁻¹ * δ * sg σ g ∈ elemSet r A} ↔
      ∃ ρ ∈ R, ∃ h ∈ H, ∃ κ ∈ K, g = h * (y * diagT E (Fin n) ρ) * κ := by
    intro g
    rw [Set.mem_setOf_eq, hsupp g]
    constructor
    · rintro ⟨u, hu, κ, hκ, rfl⟩
      obtain ⟨ρ, hρR, p, s, hp, hs, rfl⟩ := (hR u).1 hu
      refine ⟨ρ, hρR, y * diagT E (Fin n) p * y⁻¹, (hH _).2 ((hfix p).2 hp), diagT E (Fin n) s * κ, ?_, ?_⟩
      · refine K.mul_mem ?_ ?_
        · rw [← SetLike.mem_coe, hK]
          exact diag_ball hs
        · rw [← SetLike.mem_coe, hK]
          exact hκ
      · rw [map_mul, map_mul, diag_comm ρ p]
        group
    · rintro ⟨ρ, hρR, h, hh, κ, hκ, rfl⟩
      obtain ⟨w, hw⟩ := hcen h hh
      have hw' := hfixH h hh w hw
      refine ⟨w * ρ, (hR _).2 ⟨ρ, hρR, w, 1, hw', fun i => by simp, by rw [mul_one, mul_comm]⟩, κ, ?_, ?_⟩
      · rw [← hK]
        exact hκ
      · rw [map_mul, hback h w hw]
        group
  have hD : ∀ i ∈ R, ∀ j ∈ R, (∃ h ∈ H, ∃ κ ∈ K, y * diagT E (Fin n) i = h * (y * diagT E (Fin n) j) * κ) →
      i = j := by
    rintro i hi j hj ⟨h, hh, κ, hκ, he⟩
    obtain ⟨w, hw⟩ := hcen h hh
    have hw' := hfixH h hh w hw
    have hk : κ = diagT E (Fin n) (w⁻¹ * j⁻¹ * i) := by
      calc κ = (h * (y * diagT E (Fin n) j))⁻¹ * (y * diagT E (Fin n) i) := by
            rw [he]
            group
        _ = diagT E (Fin n) (w⁻¹ * j⁻¹ * i) := by
          rw [hback h w hw, mul_comm w⁻¹ j⁻¹]
          simp only [map_mul, map_inv]
          group
    refine hRd i hi j hj ⟨w, w⁻¹ * j⁻¹ * i, hw', near_of_ball ?_, by group⟩
    rw [← hk, ← hK]
    exact hκ
  have key := cosetSum (GL (Fin n) E) μ hμ K H hKo hKc hclosed hcomm ν hν (Fin n → Eˣ) R
    (fun ρ => y * diagT E (Fin n) ρ) {h : H | y⁻¹ * ↑h * y ∈ ball n r}
    {g : GL (Fin n) E | g⁻¹ * δ * sg σ g ∈ elemSet r A} hV hS hD
  rw [hK] at key
  exact key
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

open GroundTheory.Global.AdeleBaseChange in
theorem UpperTheory.Gal.InertialTypesAlt.L.normLoc :
    UpperTheory.Gal.InertialTypesAlt.L.NormLoc := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp v w hw i1 i2 i3 i4 hmap η hη u
  obtain ⟨w0, hw0⟩ := w
  obtain rfl : below F w0 = v := (below_eq_iff w0 v).2 hw0
  have h2 := ideleNorm_finiteEmbedding (K := F) w0 u
  have h3 := UpperTheory.Gal.InertialTypesAlt.G.normTriv F E η hη (IdeleGroup.finiteEmbedding w0 u)
  rw [h2] at h3
  have hi : i1 = GroundTheory.Global.SemiLocal.algebraCompletion (below F w0) w0 := by
    apply Algebra.algebra_ext
    intro r
    exact (hmap r).symm
  subst hi
  exact h3
end
end
