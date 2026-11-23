module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNumeratorOfInvolution
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle108
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Mathlib.Algebra.Polynomial.Div
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Meromorphic.Divisor
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.StatementLoc
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.GenEigIdem

open Polynomial Module

section SlopeTestRemainingChoices

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def stabAlg (Z B : Submodule K V) : Subalgebra K (Module.End K V) where
  carrier := {f | (∀ z ∈ Z, f z ∈ Z) ∧ ∀ z ∈ B, f z ∈ B}
  mul_mem' := fun {f g} hf hg =>
    ⟨fun z hz => hf.1 _ (hg.1 z hz), fun z hz => hf.2 _ (hg.2 z hz)⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun z hz => Z.add_mem (hf.1 z hz) (hg.1 z hz),
     fun z hz => B.add_mem (hf.2 z hz) (hg.2 z hz)⟩
  algebraMap_mem' := fun c =>
    ⟨fun z hz => by simpa [Module.algebraMap_end_apply] using Z.smul_mem c hz,
     fun z hz => by simpa [Module.algebraMap_end_apply] using B.smul_mem c hz⟩

def quotAlgHom (Z B : Submodule K V) :
    stabAlg Z B →ₐ[K] Module.End K (Z ⧸ B.comap Z.subtype) where
  toFun f := (B.comap Z.subtype).mapQ (B.comap Z.subtype)
    ((f : Module.End K V).restrict f.2.1) (fun z hz => f.2.2 _ hz)
  map_one' := by ext z; rfl
  map_mul' f g := by ext z; rfl
  map_zero' := by ext z; rfl
  map_add' f g := by ext z; rfl
  commutes' c := by ext z; rfl

theorem quotAlgHom_mk (Z B : Submodule K V) (f : stabAlg Z B) (z : Z) :
    quotAlgHom Z B f (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨(f : Module.End K V) z, f.2.1 z z.2⟩ := rfl

theorem quotAlgHom_mk_eq_zero (Z B : Submodule K V) (f : stabAlg Z B) (z : Z) :
    quotAlgHom Z B f (Submodule.Quotient.mk z) = 0 ↔ (f : Module.End K V) z ∈ B := by
  rw [quotAlgHom_mk, Submodule.Quotient.mk_eq_zero]; rfl

theorem exists_poly_genEig (M : Type) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (A : Module.End K M) (c : K) :
    ∃ p : K[X], p.eval c = 1 ∧
      ∀ w, aeval A ((X - C c) ^ finrank K M) (aeval A p w) = 0 := by
  set χ := A.charpoly with hχdef
  have hχ : χ ≠ 0 := (LinearMap.charpoly_monic A).ne_zero
  set a := χ.rootMultiplicity c
  set r := χ /ₘ (X - C c) ^ a
  have hr : r.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hχ
  have hfac : (X - C c) ^ a * r = χ := pow_mul_divByMonic_rootMultiplicity_eq χ c
  have ha : a ≤ finrank K M := by
    have h1 : (X - C c) ^ a ∣ χ := ⟨r, hfac.symm⟩
    have h2 := natDegree_le_of_dvd h1 hχ
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one, hχdef, LinearMap.charpoly_natDegree] at h2
  refine ⟨C (r.eval c)⁻¹ * r, by simp [hr], fun w => ?_⟩
  rw [← Module.End.mul_apply, ← map_mul]
  have : (X - C c) ^ finrank K M * (C (r.eval c)⁻¹ * r) =
      C (r.eval c)⁻¹ * (X - C c) ^ (finrank K M - a) * χ := by
    rw [← hfac]
    conv_lhs => rw [← Nat.sub_add_cancel ha, pow_add]
    ring
  rw [this, map_mul, LinearMap.aeval_self_charpoly, mul_zero, LinearMap.zero_apply]

end SlopeTestRemainingChoices

end GlobalTheory.GenEigIdem

namespace GlobalTheory

open Polynomial Module GlobalTheory.GenEigIdem

theorem exists_genEig_idem_poly : ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (Z B : Submodule K V) (ι : Type) (S : ι → Prop) (T : ι → Module.End K V) (lam : ι → K), B ≤ Z → FiniteDimensional K Z → (∀ t, S t → ∀ z ∈ Z, T t z ∈ Z) → (∀ t, S t → ∀ z ∈ B, T t z ∈ B) → (∀ t t', S t → S t' → ∀ z ∈ Z, T t (T t' z) - T t' (T t z) ∈ B) → (∀ z ∈ Z, ∀ n : ℕ, (∀ t, S t → ((T t - lam t • 1) ^ n) z ∈ B) → ∀ t, S t → (T t - lam t • 1) z ∈ B) → ∃ P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}), FreeAlgebra.lift K lam P = 1 ∧ ∀ z ∈ Z, ∀ t, S t → (T t - lam t • 1) (FreeAlgebra.lift K T P z) ∈ B := by
  intro K _ V _ _ Z B ι S T lam _hBZ hfd hZ hB hcomm hgen
  let Tg : {t // S t} → stabAlg Z B := fun t => ⟨T t.1, hZ t.1 t.2, hB t.1 t.2⟩
  let φ := quotAlgHom Z B
  let d := finrank K (Z ⧸ B.comap Z.subtype)
  have hex : ∀ t : {t // S t}, ∃ p : K[X], p.eval (lam t.1) = 1 ∧
      ∀ w, aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d) (aeval (φ (Tg t)) p w) = 0 :=
    fun t => exists_poly_genEig _ _ _
  choose p hp1 hp2 using hex
  let N : {t // S t} → Submodule K (Z ⧸ B.comap Z.subtype) := fun t =>
    LinearMap.ker (aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d))
  let Ninf : Finset {t // S t} → Submodule K (Z ⧸ B.comap Z.subtype) := fun F => ⨅ t ∈ F, N t
  obtain ⟨F, -, hF⟩ := (measure fun F : Finset {t // S t} => finrank K (Ninf F)).wf.has_min
    Set.univ ⟨∅, trivial⟩
  classical
  have hFle : ∀ s, Ninf F ≤ N s := by
    intro s
    have hins : Ninf (insert s F) = N s ⊓ Ninf F := Finset.iInf_insert _ _ _
    have hmin : ¬ finrank K (Ninf (insert s F)) < finrank K (Ninf F) := hF (insert s F) trivial
    have heq : Ninf (insert s F) = Ninf F := by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [hins]; exact inf_le_right
      · exact not_lt.mp hmin
    rw [← heq, hins]; exact inf_le_left
  have hinv : ∀ (s t : {t // S t}) (q : K[X]) (w : Z ⧸ B.comap Z.subtype), w ∈ N t →
      aeval (φ (Tg s)) q w ∈ N t := by
    intro s t q w hw
    have hc : Commute (φ (Tg s)) (φ (Tg t)) := by
      refine LinearMap.ext fun w => Submodule.Quotient.induction_on _ w fun z => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, quotAlgHom_mk, quotAlgHom_mk, quotAlgHom_mk,
        quotAlgHom_mk, Submodule.Quotient.eq]
      exact hcomm s.1 t.1 s.2 t.2 z z.2
    have hc2 : Commute (aeval (φ (Tg s)) q) (aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d)) :=
      Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K _)
        (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K _)
          hc.symm).symm
    have hw' := LinearMap.mem_ker.mp hw
    refine LinearMap.mem_ker.mpr ?_
    rw [← Module.End.mul_apply, ← hc2.eq, Module.End.mul_apply, hw', map_zero]
  have hprod : ∀ (l : List {t // S t}) (w : Z ⧸ B.comap Z.subtype) (t : {t // S t}), t ∈ l →
      φ (l.map fun s => aeval (Tg s) (p s)).prod w ∈ N t := by
    intro l
    induction l with
    | nil => intro w t ht; simp at ht
    | cons a l ih =>
      intro w t ht
      rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ← aeval_algHom_apply]
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact LinearMap.mem_ker.mpr (hp2 _ _)
      · exact hinv _ _ _ _ (ih _ _ ht')
  let P : FreeAlgebra K ι := (F.toList.map fun t => aeval (FreeAlgebra.ι K t.1) (p t)).prod
  let Q : stabAlg Z B := (F.toList.map fun t => aeval (Tg t) (p t)).prod
  have hPQ : FreeAlgebra.lift K T P = (Q : Module.End K V) := by
    rw [show (Q : Module.End K V) = (stabAlg Z B).val Q from rfl]
    simp only [P, Q, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    rw [← aeval_algHom_apply, ← aeval_algHom_apply, FreeAlgebra.lift_ι_apply]
    rfl
  have hPmem : P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}) := by
    refine Subalgebra.list_prod_mem _ fun x hx => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_image_of_mem (FreeAlgebra.ι K) (show t.1 ∈ {t | S t} from t.2)))
      (aeval_mem_adjoin_singleton K _)
  have hPlam : FreeAlgebra.lift K lam P = 1 := by
    simp only [P, map_list_prod, List.map_map]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    simp only [Function.comp_apply]
    rw [← aeval_algHom_apply, FreeAlgebra.lift_ι_apply, coe_aeval_eq_eval, hp1]
  refine ⟨P, hPmem, hPlam, fun z hz s hs => ?_⟩
  rw [hPQ]
  have hQz : (Q : Module.End K V) z ∈ Z := Q.2.1 z hz
  refine hgen _ hQz d (fun t ht => ?_) s hs
  let U : stabAlg Z B := (Tg ⟨t, ht⟩ - algebraMap K (stabAlg Z B) (lam t)) ^ d
  have hU : (U : Module.End K V) = (T t - lam t • 1) ^ d := by
    simp [U, Tg, Algebra.algebraMap_eq_smul_one]
  rw [← hU]
  have key : φ U (Submodule.Quotient.mk ⟨(Q : Module.End K V) z, hQz⟩) = 0 := by
    have h1 : φ Q (Submodule.Quotient.mk ⟨z, hz⟩) =
        Submodule.Quotient.mk ⟨(Q : Module.End K V) z, hQz⟩ := quotAlgHom_mk _ _ _ _
    rw [← h1]
    have hφU : φ U = aeval (φ (Tg ⟨t, ht⟩)) ((X - C (lam t)) ^ d) := by
      simp [U]
    rw [hφU]
    refine LinearMap.mem_ker.mp (hFle ⟨t, ht⟩ ?_)
    simp only [Ninf, Submodule.mem_iInf]
    intro s' hs'
    exact hprod _ _ _ (Finset.mem_toList.mpr hs')
  exact (quotAlgHom_mk_eq_zero Z B U _).mp key

end GlobalTheory
end

section

open Polynomial PeriodPair

namespace GlobalTheory

lemma exists_monic_sq_eq_of_mul_eq_sq {D G P : ℂ[X]} (hD : D.Monic) (hc : IsCoprime D G)
    (h : D * G = P ^ 2) : ∃ h : ℂ[X], h.Monic ∧ D = h ^ 2 := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hc h
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hD.ne_zero (by simpa using hd.symm)
  refine ⟨normalize d, monic_normalize hd0, ?_⟩
  refine eq_of_monic_of_associated hD ((monic_normalize hd0).pow 2) ?_
  exact hd.symm.trans ((associated_normalize d).pow_pow)

theorem exists_mul_sqrt_neg_odd_polynomial_identity (L : PeriodPair) (α : ℂ) (m : ℕ)
    (k : Subfield ℂ) (hα2 : α ^ 2 = -(2 * (m : ℂ) + 1))
    (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice)
    (hind : (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
      L.lattice.toAddSubgroup = 2 * m + 1)
    (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L.lattice → L.weierstrassP t ∈ k) :
    ∃ n h : ℂ[X], n.Monic ∧ h.Monic ∧ n.natDegree = 2 * m + 1 ∧ h.natDegree = m ∧
      IsCoprime n h ∧ (∀ i, n.coeff i ∈ k) ∧
      (∀ x, h.IsRoot x → ∃ t ∉ L.lattice, α * t ∈ L.lattice ∧ L.weierstrassP t = x) ∧
      (X ^ 3 + C (-L.g₂ / 4) * X + C (-L.g₃ / 4)) * (derivative n * h - 2 * n * derivative h) ^ 2 =
        n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * h ^ 4 + C (α ^ 6 * (-L.g₃ / 4)) * h ^ 6 := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h0 : ((2 * m + 1 : ℕ) : ℂ) = 0 := by
      push_cast
      linear_combination hα2
    exact absurd (Nat.cast_eq_zero.mp h0) (by omega)
  obtain ⟨A, D, c1, -, c3, c4, c5, c6, c7, c8, c9⟩ :=
    exists_weierstrassP_mul_eq_div hα0 hα k h₂ h₃ hαk hk
  set F : ℂ[X] := X ^ 3 + C (-L.g₂ / 4) * X + C (-L.g₃ / 4) with hF
  set n : ℂ[X] := C (α ^ 2) * A with hn
  have hα20 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα0
  have hFe : ∀ z ∉ L.lattice, F.eval (℘[L] z) = ℘'[L] z ^ 2 / 4 := by
    intro z hz
    rw [L.derivWeierstrassP_sq z hz]
    simp only [hF, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring
  have hnD : IsCoprime n D := by
    rw [hn]
    exact (isCoprime_mul_unit_left_left (isUnit_C.mpr (IsUnit.mk0 _ hα20)) A D).mpr c5
  have key : F * (derivative n * D - n * derivative D) ^ 2 =
      D * (n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3) := by
    refine mul_left_cancel₀ c3.ne_zero (Polynomial.funext fun x ↦ ?_)
    obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    by_cases h0 : D.eval (℘[L] z) = 0
    · simp [h0]
    have hz' := (c8 z hz).not.mp h0
    have e1 := derivWeierstrassP_mul_eq hα c9 hz' h0
    have e2 := L.derivWeierstrassP_sq _ hz'
    rw [c9 z hz'] at e2
    rw [eval_mul, eval_mul, eval_mul (p := D), hFe z hz]
    congr 1
    simp only [hn, derivative_mul, derivative_C, eval_add, eval_mul, eval_pow, eval_sub, eval_C,
      zero_mul, zero_add] at e1 ⊢
    have e3 := congrArg (· ^ 2) e1
    simp only [mul_pow] at e3
    rw [e2] at e3
    field_simp at e3
    field_simp
    linear_combination (-1 : ℂ) * e3
  have hDF : IsCoprime D F := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
    intro x
    obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    by_contra! hc
    simp only [coe_aeval_eq_eval] at hc
    have h1 := (c8 z hz).mp hc.1
    have h2 : ℘'[L] z = 0 := by
      have := hc.2
      rw [hFe z hz] at this
      simpa using this
    rw [derivWeierstrassP_eq_zero_iff L hz] at h2
    refine hz ?_
    have h3 := sub_mem (neg_mem (hα _ h1)) (nsmul_mem h2 m)
    convert h3 using 1
    rw [nsmul_eq_mul]
    linear_combination z * hα2
  have hDG : IsCoprime D
      (n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3) := by
    have : n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3 =
        n ^ 3 + D * (C (α ^ 4 * (-L.g₂ / 4)) * n * D + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 2) := by ring
    rw [this]
    exact (hnD.symm.pow_right).add_mul_left_right _
  obtain ⟨h, hm, hD⟩ := exists_monic_sq_eq_of_mul_eq_sq c3 (hDG.mul_right hDF)
    (P := F * (derivative n * D - n * derivative D)) (by linear_combination (-F) * key)
  have hdn : n.natDegree = 2 * m + 1 := by rw [hn, natDegree_C_mul hα20, c6, hind]
  refine ⟨n, h, ?_, hm, hdn, ?_, ?_, fun i ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · rw [Monic, hn, leadingCoeff_mul, leadingCoeff_C, c4, mul_inv_cancel₀ hα20]
  · rw [c6, hind, hD, natDegree_pow] at c7
    omega
  · rw [hD] at hnD
    exact (IsCoprime.pow_right_iff (by norm_num)).mp hnD
  · rw [hn, coeff_C_mul]
    exact mul_mem (pow_mem hαk 2) (c1 i)
  · obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    refine ⟨z, hz, (c8 z hz).mp ?_, rfl⟩
    rw [hD, eval_pow, hx.eq_zero]
    norm_num
  · refine mul_left_cancel₀ (pow_ne_zero 2 hm.ne_zero) ?_
    rw [hD, derivative_sq] at key
    have h2 : (C 2 : ℂ[X]) = 2 := rfl
    rw [h2] at key
    linear_combination key

end GlobalTheory
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section
namespace GlobalTheory.KZ.RootDisc

open Metric Filter Topology

theorem exists_root_of_ne_zero (g : ℂ → ℂ) (m : ℕ) (c : ℂ) (R : ℝ) (hm : 0 < m)
    (hg : DifferentiableOn ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0) (hR : 0 < R) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s (ball c R) ∧ ∀ z ∈ ball c R, s z ^ m = g z := by
  have hd : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c R) :=
    (hg.deriv isOpen_ball).div hg hne
  obtain ⟨L, hL0, hL⟩ := hd.isExactOn_ball.with_val_at c (Complex.log (g c))
  have hc : c ∈ ball c R := mem_ball_self hR
  have hgd : ∀ z ∈ ball c R, HasDerivAt g (deriv g z) z := fun z hz =>
    ((hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hh : ∀ z ∈ ball c R, HasDerivAt (fun w => g w * Complex.exp (-L w)) 0 z := by
    intro z hz
    have h1 : HasDerivAt (fun w => g w * Complex.exp (-L w))
        (deriv g z * Complex.exp (-L z) + g z * (Complex.exp (-L z) * -(deriv g z / g z))) z :=
      (hgd z hz).mul ((hL z hz).neg.cexp)
    refine h1.congr_deriv ?_
    have e : g z * (deriv g z / g z) = deriv g z := mul_div_cancel₀ _ (hne z hz)
    linear_combination (-Complex.exp (-L z)) * e
  have hexp : ∀ z ∈ ball c R, g z = Complex.exp (L z) := by
    intro z hz
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
      (fun z hz => (hh z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => by simpa using (hh z hz).deriv) hz hc
    simp only [hL0, Complex.exp_neg, Complex.exp_log (hne c hc)] at hconst
    rw [mul_inv_cancel₀ (hne c hc)] at hconst
    have := Complex.exp_ne_zero (L z)
    field_simp at hconst
    exact hconst
  refine ⟨fun z => Complex.exp (L z / m), ?_, ?_⟩
  · intro z hz
    exact (((hL z hz).differentiableAt.div_const (m : ℂ)).cexp).differentiableWithinAt
  · intro z hz
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hm', hexp z hz]

end GlobalTheory.KZ.RootDisc

namespace GlobalTheory.KZ.RootDisc
open Metric Filter Topology

theorem exists_root_disc : ∀ (h : ℂ → ℂ) (m : ℕ) (c : ℂ) (R : ℝ), 0 < m → 0 < R →
    AnalyticOnNhd ℂ h (Metric.closedBall c R) →
    (∀ τ ∈ Metric.closedBall c R, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) →
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (Metric.ball c R) ∧ ∀ z ∈ Metric.ball c R, r z ^ m = h z := by
  intro h m c R hm hR hh hord
  set U := closedBall c R with hU
  have hmer : MeromorphicOn h U := hh.meromorphicOn
  have htop : ∀ u : U, meromorphicOrderAt h u ≠ ⊤ := by
    rintro ⟨u, hu⟩
    obtain ⟨k, hk⟩ := hord u hu
    rw [(hh u hu).meromorphicOrderAt_eq, hk, ENat.map_coe]
    exact WithTop.coe_ne_top
  have hfin : (MeromorphicOn.divisor h U).support.Finite := (MeromorphicOn.divisor h U).finiteSupport (isCompact_closedBall c R)
  obtain ⟨g, hg, hgne, hgeq⟩ := hmer.extract_zeros_poles htop hfin
  set d := MeromorphicOn.divisor h U with hd
  set S := hfin.toFinset with hS
  have hdU : ∀ u ∈ U, ∃ k : ℕ, d u = ((m * k : ℕ) : ℤ) := by
    intro u hu
    obtain ⟨k, hk⟩ := hord u hu
    refine ⟨k, ?_⟩
    rw [hd, MeromorphicOn.divisor_apply hmer hu, (hh u hu).meromorphicOrderAt_eq, hk, ENat.map_coe, WithTop.untop₀_coe]
  let kk : ℂ → ℕ := fun u => (d u).toNat / m
  have hkk : ∀ u ∈ U, d u = ((m * kk u : ℕ) : ℤ) := by
    intro u hu
    obtain ⟨k, hk⟩ := hdU u hu
    have : kk u = k := by
      simp only [kk, hk, Int.toNat_natCast]
      exact Nat.mul_div_cancel_left k hm
    rw [this, hk]
  have hSU : ∀ u ∈ S, u ∈ U := by
    intro u hu
    rw [hS, Set.Finite.mem_toFinset] at hu
    exact d.supportWithinDomain hu
  let q : ℂ → ℂ := fun z => ∏ u ∈ S, (z - u) ^ kk u
  have hP : ∀ z, (∏ᶠ u, (· - u) ^ d u : ℂ → ℂ) z = q z ^ m := by
    intro z
    rw [finprod_eq_prod_of_mulSupport_subset (s := S), Finset.prod_apply, ← Finset.prod_pow]
    · refine Finset.prod_congr rfl fun u hu => ?_
      rw [hkk u (hSU u hu), zpow_natCast, mul_comm, pow_mul]
      rfl
    · intro u hu
      rw [Set.Finite.coe_toFinset]
      rw [Function.mem_mulSupport] at hu
      rw [Function.mem_support]
      intro h0
      apply hu
      rw [h0, zpow_zero]
  have hqd : Differentiable ℂ q := by
    intro z
    simp only [q]
    fun_prop
  have hgball : DifferentiableOn ℂ g (ball c R) :=
    (hg.mono ball_subset_closedBall).differentiableOn
  obtain ⟨s, hs, hsm⟩ := exists_root_of_ne_zero g m c R hm hgball
    (fun z hz => hgne ⟨z, ball_subset_closedBall hz⟩) hR
  refine ⟨fun z => q z * s z, hqd.differentiableOn.mul hs, ?_⟩
  intro z hz
  rw [mul_pow, hsm z hz]
  have hzU : z ∈ U := ball_subset_closedBall hz
  have hA := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hgeq) z hzU
  have hUn : U ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds
    (mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)
  have hev : h =ᶠ[𝓝[≠] z] fun w => q w ^ m * g w := by
    filter_upwards [hA, hUn] with w hw hwU
    rcases hw with hw | hw
    · have hw' : h w = (∏ᶠ u, (· - u) ^ d u : ℂ → ℂ) w * g w := hw
      rw [hw', hP]
    · exact absurd hwU hw
  have t1 : Tendsto h (𝓝[≠] z) (𝓝 (h z)) :=
    (hh z hzU).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun w => q w ^ m * g w) (𝓝[≠] z) (𝓝 (q z ^ m * g z)) :=
    (((hqd z).continuousAt.pow m).mul (hg z hzU).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  exact (tendsto_nhds_unique_of_eventuallyEq t2 t1 hev.symm)

end GlobalTheory.KZ.RootDisc
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.padicInt_eq_zero_of_pow_smul_of_card_quotient : ∀ (l : ℕ) [Fact l.Prime] (C : Type) [AddCommGroup C] [Module ℤ_[l] C] [Module.Finite ℤ_[l] C], (∀ r : ℕ, 0 < r → Nat.card (C ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] C ((l : ℤ_[l]) ^ r))) = l ^ r) → ∀ (r : ℕ) (c : C), (l : ℤ_[l]) ^ r • c = 0 → c = 0 := by
  first | exact @GlobalTheory.padicInt_torsionFree_of_card_quotient_pow | exact GlobalTheory.padicInt_torsionFree_of_card_quotient_pow | (intros; apply GlobalTheory.padicInt_torsionFree_of_card_quotient_pow <;> assumption)
end
