module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle208
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle204
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle206
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle207
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle196
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle225
public import GroundTheory.LocalFields.Different
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle226
public import GroundTheory.PAdicHodge.TiltValuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.RootFactorProduct

private lemma map_sub_smul_E_mulVec_eq {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c))
    (a : ℕ) (v : Fin n → FractionRing O) :
    e (((X₀ - ρ a • E).map (toFr O)).mulVec v) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1) - ρ a) * (e v).2 c) := by
  have hm : (X₀ - ρ a • E).map (toFr O) = X₀.map (toFr O) - toFr O (ρ a) • E.map (toFr O) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul]
  have hs : ((toFr O (ρ a)) • E.map (toFr O)).mulVec v = toFr O (ρ a) • (E.map (toFr O)).mulVec v := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum,
      mul_assoc]
  rw [hm, Matrix.sub_mulVec, hs, map_sub, map_smul, hX, hE]
  refine Prod.ext (by simp) ?_
  funext c
  simp only [Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub]
  ring

theorem prod_cons_action {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c))
    (s : List ℕ) : ∀ (a : ℕ) (u : Fin n → FractionRing O),
      e (((((a :: s).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) =
        (0, fun c : Fin t =>
          toFr O (((a :: s).map fun c' => ρ ((c : ℕ) + 1) - ρ c').prod) * (e u).2 c) := by
  induction s with
  | nil =>
    intro a u
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact map_sub_smul_E_mulVec_eq e E X₀ ρ hE hX a u
  | cons b s ih =>
    intro a u
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, ← Matrix.mulVec_mulVec,
      map_sub_smul_E_mulVec_eq e E X₀ ρ hE hX a, ih b u]
    refine Prod.ext rfl ?_
    funext c
    simp only [List.map_cons, List.prod_cons, map_mul, mul_assoc]

private lemma list_prod_range'_eq_prod_Ico {M : Type} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∀ m : ℕ, ((List.range' m n).map g).prod = ∏ k ∈ Finset.Ico m (m + n), g k := by
  induction n with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    rw [List.range'_succ, List.map_cons, List.prod_cons, ih, show m + (n + 1) = m + 1 + n by omega,
      Finset.prod_eq_prod_Ico_succ_bot (show m < m + 1 + n by omega)]

theorem prod_other_factors_action {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O) (ht : 2 ≤ t)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c)) (u : Fin n → FractionRing O) :
    e (((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) =
      (0, fun c : Fin t => if (c : ℕ) = 0 then
        toFr O (∏ c' ∈ Finset.Ioc 1 t, (ρ 1 - ρ c')) * (e u).2 c else 0) := by
  have hl : List.range' 2 (t - 1) = 2 :: List.range' 3 (t - 2) := by
    rw [show t - 1 = (t - 2) + 1 by omega, List.range'_succ]
  rw [hl, prod_cons_action e E X₀ ρ hE hX, ← hl]
  refine Prod.ext rfl ?_
  funext c
  dsimp only
  split_ifs with h0
  · simp only [h0, zero_add]
    congr 2
    all_goals
      rw [list_prod_range'_eq_prod_Ico]
      apply Finset.prod_congr _ (fun _ _ => rfl)
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
  · have hc := c.isLt
    rw [List.prod_eq_zero, map_zero, zero_mul]
    exact List.mem_map.2 ⟨(c : ℕ) + 1, List.mem_range'_1.2 ⟨by omega, by omega⟩, sub_self _⟩

end GlobalTheory.RootFactorProduct
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

open Polynomial

theorem isLocalRing_of_domain_finite_padicInt (l : ℕ) [Fact l.Prime] (B : Type) [CommRing B]
    [IsDomain B] [Algebra ℤ_[l] B] [Module.Finite ℤ_[l] B] : IsLocalRing B := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun b => ?_
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h0, h1⟩ := hcon
  obtain ⟨E, hE, hM⟩ := GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem l b
  have e0 : E - 0 ∈ (Ideal.span {b}).restrictScalars ℤ_[l] := hM _ 0 fun n => by
    simp only [sub_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
    exact dvd_pow_self b (Nat.succ_ne_zero n)
  have e1 : E - 1 ∈ (Ideal.span {1 - b}).restrictScalars ℤ_[l] := hM _ 1 fun n => by
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
    have := one_sub_dvd_one_sub_pow b (n + 1)
    rw [← neg_sub 1 (b ^ (n + 1))]
    exact this.neg_right
  simp only [sub_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at e0 e1
  rcases (IsIdempotentElem.iff_eq_zero_or_one (p := E)).1 hE with h | h
  · rw [h, zero_sub] at e1
    exact h1 (isUnit_of_dvd_one (dvd_neg.1 e1))
  · rw [h] at e0
    exact h0 (isUnit_of_dvd_one e0)

theorem exists_fin_prod_of_splits {L : Type} [Field L] (t : ℕ) (f : L[X]) (hs : f.Splits)
    (hm : f.Monic) (ht : f.natDegree = t) : ∃ α : Fin t → L, f = ∏ c, (X - C (α c)) := by
  have hc : f.roots.toList.length = t := by
    rw [Multiset.length_toList, ← hs.natDegree_eq_card_roots, ht]
  subst hc
  refine ⟨f.roots.toList.get, ?_⟩
  conv_lhs => rw [hs.eq_prod_roots_of_monic hm, ← Multiset.coe_toList f.roots]
  rw [Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
  congr 1
  conv_lhs => rw [← List.ofFn_get f.roots.toList]
  rw [List.map_ofFn]
  rfl

theorem exists_finite_dvr_splitting : ∀ (l : ℕ) [Fact l.Prime] {A ι : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] [Finite ι] (t : ℕ) (P : ι → Polynomial A), (∀ i, ((P i).map (toFr A)).Monic ∧ ((P i).map (toFr A)).natDegree = t) → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B), Module.Finite A B ∧ Function.Injective (algebraMap A B) ∧ ∀ i, ∃ α : Fin t → FractionRing B, (P i).map ((toFr B).comp (algebraMap A B)) = ∏ c, (Polynomial.X - Polynomial.C (α c)) := by
  intro l _ A ι _ _ _ _ _ _ _ t P hP
  classical
  haveI := Fintype.ofFinite ι
  let K := FractionRing A
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing A
  let F : K[X] := ∏ i, (P i).map (toFr A)
  have hF : F.Monic := monic_prod_of_monic _ _ fun i _ => (hP i).1
  let L := F.SplittingField
  haveI : IsScalarTower A K L := inferInstance
  let S := integralClosure A L
  haveI : Module.Finite A S := IsIntegralClosure.finite A K L S
  haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain A K L S
  haveI : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension A K L S
  haveI : IsLocalRing S := by
    letI : Algebra ℤ_[l] S := ((algebraMap A S).comp (algebraMap ℤ_[l] A)).toAlgebra
    haveI : IsScalarTower ℤ_[l] A S := .of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℤ_[l] S := Module.Finite.trans A S
    exact isLocalRing_of_domain_finite_padicInt l S
  have hinj : Function.Injective (algebraMap A S) :=
    algebraMap_injective_of_field_isFractionRing A S K L
  have hnf : ¬ IsField S := fun h =>
    IsDiscreteValuationRing.not_isField A (isField_of_isIntegral_of_isField hinj h)
  haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 3 1).1
    (inferInstance : IsDedekindDomain S)
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hinj,
    fun i => ?_⟩
  let e : L ≃ₐ[S] FractionRing S := (FractionRing.algEquiv S L).symm
  have hsF : (F.map (algebraMap K L)).Splits := SplittingField.splits F
  have hsi : (((P i).map (toFr A)).map (algebraMap K L)).Splits :=
    hsF.of_dvd (hF.map _).ne_zero
      (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
  have hcomp : (toFr S).comp (algebraMap A S) =
      ((e : L →+* FractionRing S).comp (algebraMap K L)).comp (toFr A) := by
    ext a
    have : algebraMap K L (toFr A a) = algebraMap S L (algebraMap A S a) := by
      rw [← IsScalarTower.algebraMap_apply A S L]
      exact (IsScalarTower.algebraMap_apply A K L a).symm
    simp only [RingHom.comp_apply, this]
    exact (e.commutes _).symm
  rw [hcomp, ← Polynomial.map_map, ← Polynomial.map_map]
  refine exists_fin_prod_of_splits t _ (hsi.map _) (((hP i).1.map _).map _) ?_
  rw [natDegree_map, natDegree_map, (hP i).2]

end GlobalTheory
end

section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.IdeleLogNormCompare

open GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.Mem.Chr.CharModel

variable (E : Type) [Field E] [NumberField E]

theorem ord_eq_ord_vw (d : (AdeleRing (𝓞 E) E)ˣ) (v : HeightOneSpectrum (𝓞 E)) :
    GroundTheory.Global.IdeleGroup.ord v d = GlobalTheory.Idele.ord_vw (finPart E d) v := rfl

theorem logInf_eq (d : (AdeleRing (𝓞 E) E)ˣ) :
    logInf E (infPart E d) = Real.log (infiniteModule d) := by
  rw [infiniteModule, Real.log_prod]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
    rfl
  · intro w _
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (infinite_ne_zero d w))

theorem logFin_eq (d : (AdeleRing (𝓞 E) E)ˣ) :
    logFin E (finPart E d) = -Real.log (finiteModule d) := by
  classical
  have hfin := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (finPart E d))
  let S := hfin.toFinset
  have hS : ∀ v, v ∉ S → GlobalTheory.Idele.ord_vw (finPart E d) v = 0 := by
    intro v hv
    by_contra h
    exact hv (hfin.mem_toFinset.2 h)
  have hI : GlobalTheory.Idele.idealOf (finPart E d) =
      ∏ v ∈ S, (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ GlobalTheory.Idele.ord_vw (finPart E d) v := by
    unfold GlobalTheory.Idele.idealOf
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    exact hv (by show (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ GlobalTheory.Idele.ord_vw (finPart E d) v = 1
                 rw [hS v h, zpow_zero])
  have hM : finiteModule d = ∏ v ∈ S, ‖(d : AdeleRing (𝓞 E) E).2 v‖ := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    refine hv ?_
    change ‖(d : AdeleRing (𝓞 E) E).2 v‖ = 1
    rw [norm_finite_eq_rpow, ord_eq_ord_vw, hS v h, Int.cast_zero, neg_zero, Real.rpow_zero]
  have hN : ∀ v : HeightOneSpectrum (𝓞 E), (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    fun v => (absNorm_asIdeal_pos v).ne'
  rw [logFin, hI, hM, map_prod, Rat.cast_prod, Real.log_prod, Real.log_prod, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast, Real.log_zpow,
      norm_finite_eq_rpow, Real.log_rpow (absNorm_asIdeal_pos v), ord_eq_ord_vw]
    ring
  · intro v _
    exact norm_ne_zero_iff.2 (finite_ne_zero d v)
  · intro v _
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    exact zpow_ne_zero _ (hN v)

theorem logNorm_eq_log_ideleModule (d : (AdeleRing (𝓞 E) E)ˣ) :
    logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) := by
  rw [logNorm, logInf_eq, logFin_eq, ideleModule_apply,
    Real.log_mul (infiniteModule_pos d).ne' (finiteModule_pos d).ne']
  ring

end GlobalTheory.IdeleLogNormCompare
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.SerreTateIndep

variable {l : ℕ} [Fact l.Prime] {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
  {χ : GQ l →* ℚ_[l]ˣ} {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)}

theorem chiC_add (i j : ℤ) (g : GQ l) : chiC χ (i + j) g = chiC χ i g * chiC χ j g := by
  simp [chiC, zpow_add]

theorem twAct_twist (i j : ℤ) (g : GQ l) (y : Fin r → PadicComplex l) :
    twAct act χ (i + j) U g y = chiC χ i g • twAct act χ j U g y := by
  unfold twAct
  rw [chiC_add, mul_smul]

theorem twAct_comb {n : ℕ} (i : ℤ) (g : GQ l) (c : Fin n → PadicComplex l)
    (x : Fin n → Fin r → PadicComplex l) :
    twAct act χ i U g (∑ k, c k • x k) = ∑ k, act g (c k) • twAct act χ i U g (x k) := by
  unfold twAct
  have : (fun b => act g ((∑ k, c k • x k) b)) = ∑ k, act g (c k) • fun b => act g (x k b) := by
    funext b; simp [Finset.sum_apply]
  rw [this, Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_smul, smul_comm]

theorem twAct_zero (i : ℤ) (g : GQ l) : twAct act χ i U g 0 = 0 := by
  unfold twAct
  have : (fun b => act g ((0 : Fin r → PadicComplex l) b)) = 0 := by
    funext b; simp
  rw [this, Matrix.mulVec_zero, smul_zero]

theorem linearIndependent_of_weightwise (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (G : Subgroup (GQ l)) (E : IntermediateField ℚ_[l] (Om l))
    (hinv : ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ G, chiC χ i g * act g y = y) →
      (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC E))
    (r n : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (e : Fin n → Fin r → PadicComplex l) (u : Fin n → ℤ)
    (he : ∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k)
    (hE : ∀ (a : ℤ) (c : Fin n → ↥E), (∀ k, u k ≠ a → c k = 0) →
      ∑ k, (((c k : ↥E) : Om l) : PadicComplex l) • e k = 0 → ∀ k, c k = 0) :
    LinearIndependent (PadicComplex l) e := by
  classical
  have key : ∀ (s : Finset (Fin n)) (c : Fin n → PadicComplex l), (∀ k, k ∉ s → c k = 0) →
      ∑ k, c k • e k = 0 → ∀ k, c k = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro c hc _ k; exact hc k (by simp)
    | insert k0 s hk0 ih =>
      intro c hc hsum
      by_cases h0 : c k0 = 0
      · refine ih c (fun k hk => ?_) hsum
        by_cases hkk : k = k0
        · rw [hkk]; exact h0
        · exact hc k (by simp [hkk, hk])
      exfalso
      set d : Fin n → PadicComplex l := fun k => (c k0)⁻¹ * c k with hd
      have hd0 : d k0 = 1 := inv_mul_cancel₀ h0
      have hds : ∑ k, d k • e k = 0 := by
        simp only [hd, mul_smul]
        rw [← Finset.smul_sum, hsum, smul_zero]
      have hfix : ∀ k, ∀ g ∈ G, chiC χ (u k0 - u k) g * act g (d k) = d k := by
        intro k g hg
        have h1 : ∑ k, (chiC χ (u k0 - u k) g * act g (d k)) • e k = 0 := by
          have h := twAct_comb (act := act) (χ := χ) (U := U) (u k0) g d e
          rw [hds, twAct_zero] at h
          rw [h]
          refine Finset.sum_congr rfl fun k _ => ?_
          conv_rhs => rw [← sub_add_cancel (u k0) (u k), twAct_twist, he g hg k]
          rw [smul_smul, mul_comm]
        have h2 := ih (fun k => chiC χ (u k0 - u k) g * act g (d k) - d k) (fun k hk => ?_) ?_ k
        · exact sub_eq_zero.1 h2
        · by_cases hkk : k = k0
          · subst hkk
            simp [hd0, chiC]
          · have : c k = 0 := hc k (by simp [hkk, hk])
            simp [hd, this]
        · simp only [sub_smul, Finset.sum_sub_distrib, h1, hds, sub_self]
      have hex : ∀ k, ∃ x : ↥E, (((x : ↥E) : Om l) : PadicComplex l) = d k ∧ (u k ≠ u k0 → x = 0) := by
        intro k
        by_cases hu : u k = u k0
        · obtain ⟨x, hx, hxd⟩ := (hinv _ _ (hfix k)).2 (by rw [hu, sub_self])
          exact ⟨⟨x, hx⟩, hxd, fun h => (h hu).elim⟩
        · refine ⟨0, ?_, fun _ => rfl⟩
          rw [(hinv _ _ (hfix k)).1 (sub_ne_zero.2 (Ne.symm hu))]
          simp
      choose x hx hx0 using hex
      have h3 := hE (u k0) x hx0 (by simp only [hx, hds]) k0
      have h4 := hx k0
      rw [h3, hd0] at h4
      simp at h4
  exact Fintype.linearIndependent_iff.2 fun c hc => key Finset.univ c (by simp) hc

end GlobalTheory.SerreTateIndep
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem exists_limit_rep : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ), DenseRange x → ∀ (θ : J → PadicAlgCl l) (L : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] L → (∀ j, θ j ∈ L) → ∀ (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∃ r : Γ →* GL (Fin a) (PadicAlgCl l), Continuous r ∧ IsSSRep r ∧ (∀ j, trc r (x j) = θ j) ∧ PolyApprox (trc r) (trc '' C) := by
  intro l _ Γ _ _ _ _ a J x hx θ L hL hθL C hC hA
  have hU := GlobalTheory.T.approximatedTraceSystem_locally_cauchy l Γ a J x θ C hC hA
  obtain ⟨T, hTc, hTx⟩ := GlobalTheory.Cong.extend_of_locallyCauchy l Γ J x hx θ L hL hθL hU
  have hA' : PolyApprox (fun j => T (x j)) ((fun ρ j => trc ρ (x j)) '' C) := by
    have : (fun j => T (x j)) = θ := funext hTx
    rw [this]; exact hA
  have hT : PolyApprox T (trc '' C) := GlobalTheory.Cong.polyApprox_of_denseRange l Γ a J x hx T hTc C hC hA'
  have hP : IsPsChar a T := GlobalTheory.T.isPseudoCharacter_of_approximatedByTraces l Γ a T C hT
  obtain ⟨r, hr, htr⟩ := GlobalTheory.PsChar.exists_ssRep Γ (PadicAlgCl l) a T hP
  have htrc : trc r = T := funext fun g => htr g
  refine ⟨r, ?_, hr, fun j => by rw [htrc]; exact hTx j, by rw [htrc]; exact hT⟩
  refine GlobalTheory.SSCont.continuous_of_continuous_trace Γ (PadicAlgCl l) a r hr ?_
  have : (fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)).trace) = T := htrc
  rw [this]; exact hTc

end GlobalTheory.Cong
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.commutator_mem_of_coboundary_detects_quotient : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → Detects p r A B → ∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B := by
  first | exact @GlobalTheory.PMon.Ram.commutator_mem_of_detects | exact GlobalTheory.PMon.Ram.commutator_mem_of_detects | (intros; apply GlobalTheory.PMon.Ram.commutator_mem_of_detects <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem untilt_injective_zero_and_dvd_of_norm_sh_le :
    ∀ (l : ℕ) [Fact l.Prime], (∀ x : Fl l, sh x = 0 → x = 0) ∧
      ∀ x y : Fl l, ‖sh x‖ ≤ ‖sh y‖ → y ∣ x := by
  intro l _
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_tiltIntegersCpEquiv_compatible_untilt l
  refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
  · have h0 : e x = 0 := GroundTheory.PAdicHodge.untilt_eq_zero_iff.1 (by rw [he]; exact hx)
    exact e.injective (by rw [h0, map_zero])
  · have hd : e y ∣ e x := by
      rw [GroundTheory.PAdicHodge.preTilt_dvd_iff_norm_le, GroundTheory.PAdicHodge.preTilt_norm_def,
        GroundTheory.PAdicHodge.preTilt_norm_def, he, he]
      exact hxy
    obtain ⟨c, hc⟩ := hd
    exact ⟨e.symm c, e.injective (by rw [map_mul, e.apply_symm_apply, hc])⟩

end GlobalTheory.PSer
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.ramificationJumpSum_add_two_mul_differentExponent_le : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (J : Subgroup (L ≃ₐ[F] L)), jumpSum (wild F L) ⊤ J + 2 * differentExponent ↥(IntermediateField.fixedField J) L ≤ 2 * differentExponent F L := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_add_two_mul_differentExponent_fixedField_le | exact GlobalTheory.PMon.Ram.jumpSum_add_two_mul_differentExponent_fixedField_le | (intros; apply GlobalTheory.PMon.Ram.jumpSum_add_two_mul_differentExponent_fixedField_le <;> assumption)
end
