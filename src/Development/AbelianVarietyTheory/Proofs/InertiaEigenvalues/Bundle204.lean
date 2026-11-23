module

public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

noncomputable section

namespace GlobalTheory.LatLenExt

open Formalism.L2.Col TensorProduct

section Int

variable {K : Type} [Field K] [NumberField K] {O : Type} [CommRing O] [IsDomain O]
  (e : K →+* FractionRing O) (he : ∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range)

def intMap : 𝓞 K →+* O :=
  (RingEquiv.ofBijective (algebraMap O (FractionRing O)).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective O (FractionRing O) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).symm.toRingHom.comp
    ((e.comp (algebraMap (𝓞 K) K)).codRestrict _ he)

theorem algebraMap_intMap (a : 𝓞 K) :
    algebraMap O (FractionRing O) (intMap e he a) = e (a : K) := by
  have h := (RingEquiv.ofBijective (algebraMap O (FractionRing O)).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective O (FractionRing O) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).apply_symm_apply
      ((e.comp (algebraMap (𝓞 K) K)).codRestrict _ he a)
  exact congrArg Subtype.val h

variable [IsDiscreteValuationRing O] (w : HeightOneSpectrum (𝓞 K))
  (hw : ∀ a : 𝓞 K, ∀ z : O, algebraMap O (FractionRing O) z = e (a : K) →
    (a ∈ w.asIdeal ↔ ¬ IsUnit z))

include hw in
theorem isUnit_intMap {a : 𝓞 K} (ha : a ∉ w.asIdeal) : IsUnit (intMap e he a) := by
  by_contra h
  exact ha ((hw a _ (algebraMap_intMap e he a)).2 h)

def owHom : Ow w →+* O :=
  IsLocalization.lift (M := w.asIdeal.primeCompl) (g := intMap e he)
    (fun s => isUnit_intMap e he w hw s.2)

theorem owHom_algebraMap (a : 𝓞 K) :
    owHom e he w hw (algebraMap (𝓞 K) (Ow w) a) = intMap e he a :=
  IsLocalization.lift_eq _ _

theorem algebraMap_owHom (x : Ow w) :
    algebraMap O (FractionRing O) (owHom e he w hw x) = e (algebraMap (Ow w) K x) := by
  have : (algebraMap O (FractionRing O)).comp (owHom e he w hw) = e.comp (algebraMap (Ow w) K) :=
    IsLocalization.ringHom_ext w.asIdeal.primeCompl (RingHom.ext fun a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
        owHom_algebraMap, algebraMap_intMap, ← IsScalarTower.algebraMap_apply])
  exact RingHom.congr_fun this x

theorem owHom_injective : Function.Injective (owHom e he w hw) := by
  intro x y h
  have := congrArg (algebraMap O (FractionRing O)) h
  rw [algebraMap_owHom, algebraMap_owHom] at this
  exact algebraMap_ow_injective w (e.injective this)

theorem owHom_isLocalHom : IsLocalHom (owHom e he w hw) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl x
  rw [owHom, IsLocalization.lift_mk'] at hx
  have ha : IsUnit (intMap e he a) := (IsUnit.mul_iff.1 hx).1
  have : a ∉ w.asIdeal := fun h => ((hw a _ (algebraMap_intMap e he a)).1 h) ha
  exact (IsLocalization.AtPrime.isUnit_mk'_iff (Ow w) w.asIdeal a s).2 this

end Int

theorem nonempty_quot_map_equiv {S M N : Type*} [Ring S] [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (f : M →ₗ[S] N) (hf : Function.Injective f)
    (P Q : Submodule S M) (P' Q' : Submodule S N) (hP : P.map f = P') (hQ : Q.map f = Q') :
    Nonempty ((P ⧸ Q.submoduleOf P) ≃ₗ[S] (P' ⧸ Q'.comap P'.subtype)) := by
  subst hP hQ
  refine ⟨Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf P) ?_⟩
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.submoduleOf, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    have := congrArg Subtype.val hxy
    simpa using this
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hpq⟩ := hy
    obtain rfl := hf hpq
    exact ⟨⟨p, hp⟩, hq, rfl⟩

end GlobalTheory.LatLenExt

namespace GlobalTheory.LatLenExt

open Formalism.L2.Col TensorProduct

theorem lenUnit_span_eq_lenUW : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V), LinearIndependent (FractionRing O) (fun a => iV (b a)) → (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → (l : 𝓞 K) ∈ w.asIdeal → (∀ a : 𝓞 K, ∀ z : O, algebraMap O (FractionRing O) z = e (a : K) → (a ∈ w.asIdeal ↔ ¬ IsUnit z)) → ∀ (A B : Submodule (𝓞 K) V), A.FG → B ≤ A → lenUnit (O := O) l (↥(Submodule.span O (iV '' (A : Set V))) ⧸ (Submodule.span O (iV '' (B : Set V))).comap (Submodule.span O (iV '' (A : Set V))).subtype) = Formalism.L2.Col.lenUW w A B := by
  intro K _ _ O _ _ _ e V V' _ _ _ _ _ _ _ _ _ iV ι b hli he w l hl hlw hw A B _ _
  letI : Algebra (Ow w) O := (owHom e he w hw).toAlgebra
  letI : Algebra K (FractionRing O) := e.toAlgebra
  haveI : IsScalarTower (Ow w) K (FractionRing O) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (Ow w) O (FractionRing O)]
    exact algebraMap_owHom e he w hw x
  haveI : FaithfulSMul (Ow w) O :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (owHom_injective e he w hw)
  haveI : IsLocalHom (algebraMap (Ow w) O) := owHom_isLocalHom e he w hw
  letI : Module K V' := Module.compHom V' e
  haveI : IsScalarTower K (FractionRing O) V' := ⟨fun c x y => by
    show (c • x) • y = e c • (x • y)
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let iVK : V →ₗ[K] V' :=
    { toFun := iV, map_add' := iV.map_add, map_smul' := fun c x => iV.map_smulₛₗ c x }
  let Φ : FractionRing O ⊗[K] V →ₗ[FractionRing O] V' := iVK.liftBaseChange (FractionRing O)
  have hΦ : ∀ v, Φ ((1 : FractionRing O) ⊗ₜ[K] v) = iV v := fun v => by
    simp [Φ, iVK]
  have hinj : Function.Injective Φ := by
    refine LinearMap.injective_of_linearIndependent (Algebra.TensorProduct.basis (FractionRing O) b).span_eq ?_
    have hc : (Φ ∘ ⇑(Algebra.TensorProduct.basis (FractionRing O) b)) = fun a => iV (b a) :=
      funext fun i => by simp [hΦ]
    rw [hc]
    exact hli
  let Φs := Φ.restrictScalars O
  have key : ∀ A' : Submodule (𝓞 K) V,
      (GlobalTheory.spanBaseChange K O (FractionRing O) (atW w A')).map Φs =
        Submodule.span O (iV '' (A' : Set V)) := by
    intro A'
    rw [GlobalTheory.spanBaseChange, Submodule.map_span, Set.image_image]
    have h1 : (fun m => Φs ((1 : FractionRing O) ⊗ₜ[K] m)) = iV := funext fun m => hΦ m
    rw [h1]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hsx⟩ := mem_atW_iff.1 hx
      obtain ⟨u, hu⟩ := isUnit_intMap e he w hw hs
      have h2 : iV (s • x) = intMap e he s • iV x := by
        rw [← algebraMap_smul K s x, iV.map_smulₛₗ, ← algebraMap_smul (FractionRing O) (intMap e he s),
          algebraMap_intMap]
      have h3 : iV x = ((u⁻¹ : Oˣ) : O) • iV (s • x) := by
        rw [h2, ← hu, smul_smul, Units.inv_mul, one_smul]
      rw [SetLike.mem_coe, h3]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsx, rfl⟩)
    · exact Submodule.span_mono (Set.image_mono fun x hx => Submodule.subset_span hx)
  obtain ⟨E2⟩ := nonempty_quot_map_equiv Φs hinj _ _ _ _ (key A) (key B)
  let E := GlobalTheory.spanBaseChangeSubquotEquiv K O (FractionRing O) (atW w A) (atW w B) ≪≫ₗ E2
  have hlen : Module.length O (↥(Submodule.span O (iV '' (A : Set V))) ⧸
      (Submodule.span O (iV '' (B : Set V))).comap (Submodule.span O (iV '' (A : Set V))).subtype) =
      lenW w A B * ((IsLocalRing.maximalIdeal O).ramificationIdx (Ow w) : ℕ) := by
    rw [← E.length_eq, GlobalTheory.length_baseChange_dvr]
    rfl
  have hden : Module.length O (O ⧸ Ideal.span {(l : O)}) =
      (eW w : ℕ∞) * ((IsLocalRing.maximalIdeal O).ramificationIdx (Ow w) : ℕ) := by
    obtain rfl := eq_prW_of_mem w hl hlw
    rw [GlobalTheory.length_quotient_span_singleton_eq_addVal, ← map_natCast (algebraMap (Ow w) O),
      GlobalTheory.addVal_algebraMap, ← GlobalTheory.length_quotient_span_singleton_eq_addVal, length_ow_quot_prW]
  have hpos := GlobalTheory.ramificationIdx_maximalIdeal_pos (Ow w) O
  unfold lenUnit lenUW
  rw [hlen, hden]
  simp only [ENat.toNat_mul, ENat.toNat_coe]
  push_cast
  exact mul_div_mul_right _ _ (by exact_mod_cast hpos.ne')

end GlobalTheory.LatLenExt
end
end

section

namespace GlobalTheory.RetractionComplement

open Formalism.MainNotions.N Matrix

section SlopeTestRemainingChoices

variable {k k' : Type} [Field k] [Field k'] [Algebra k k'] {n : ℕ}

theorem exists_retraction : ∃ l : k' →ₗ[k] k, ∀ c : k, l (algebraMap k k' c) = c := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k k')
    (LinearMap.ker_eq_bot.mpr (algebraMap k k').injective)
  exact ⟨g, fun c => by simpa using LinearMap.congr_fun hg c⟩

theorem form_mulVec (l : k' →ₗ[k] k) (A : Matrix (Fin n) (Fin n) k) (x : Fin n → k') :
    (fun i => l ((A.map (algebraMap k k')).mulVec x i)) = A.mulVec (fun i => l (x i)) := by
  funext i

  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem ext_mulVec (A : Matrix (Fin n) (Fin n) k) (v : Fin n → k) :
    (A.map (algebraMap k k')).mulVec (fun i => algebraMap k k' (v i))
      = fun i => algebraMap k k' (A.mulVec v i) := by
  funext i

  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

def extSub (k' : Type) [Field k'] [Algebra k k'] (W : Submodule k (Fin n → k)) :
    Submodule k' (Fin n → k') :=
  Submodule.span k' ((fun (v : Fin n → k) (i : Fin n) => algebraMap k k' (v i)) '' W)

theorem form_mem (l : k' →ₗ[k] k) (W : Submodule k (Fin n → k)) (x : Fin n → k')
    (hx : x ∈ extSub k' W) : (fun i => l (x i)) ∈ W := by
  have key : ∀ c : k', (fun i => l (c * x i)) ∈ W := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      intro c
      convert W.smul_mem (l c) hw using 1
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    | zero =>
      intro c
      convert W.zero_mem using 1
      funext i
      simp
    | add y z _ _ hy hz =>
      intro c
      convert W.add_mem (hy c) (hz c) using 1
      funext i
      simp [mul_add]
    | smul a y _ hy =>
      intro c
      convert hy (c * a) using 1
      funext i
      simp [mul_assoc]
  simpa using key 1

theorem extSub_stable (A : Matrix (Fin n) (Fin n) k) (W : Submodule k (Fin n → k))
    (hA : ∀ v ∈ W, A.mulVec v ∈ W) (x : Fin n → k') (hx : x ∈ extSub k' W) :
    (A.map (algebraMap k k')).mulVec x ∈ extSub k' W := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [ext_mulVec]
    exact Submodule.subset_span ⟨_, hA w hw, rfl⟩
  | zero =>
    rw [Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ a hy

def descCompl (l : k' →ₗ[k] k) (W : Submodule k (Fin n → k)) (U : Submodule k' (Fin n → k')) :
    Submodule k (Fin n → k) where
  carrier := {v | ∃ x ∈ extSub k' W, ∃ u ∈ U, x + u = (fun i => algebraMap k k' (v i)) ∧
    (fun i => l (x i)) = 0}
  zero_mem' := ⟨0, Submodule.zero_mem _, 0, U.zero_mem, by funext i; simp, by funext i; simp⟩
  add_mem' := by
    rintro v w ⟨x, hx, u, hu, h1, h2⟩ ⟨x', hx', u', hu', h1', h2'⟩
    refine ⟨x + x', Submodule.add_mem _ hx hx', u + u', U.add_mem hu hu', ?_, ?_⟩
    · funext i
      have a := congrFun h1 i
      have b := congrFun h1' i
      simp only [Pi.add_apply, map_add (f := _)] at a b ⊢
      rw [← a, ← b]; ring
    · funext i
      have a := congrFun h2 i
      have b := congrFun h2' i
      simp only [Pi.add_apply, map_add (f := _), Pi.zero_apply] at a b ⊢
      rw [a, b, add_zero]
  smul_mem' := by
    rintro c v ⟨x, hx, u, hu, h1, h2⟩
    refine ⟨algebraMap k k' c • x, Submodule.smul_mem _ _ hx, algebraMap k k' c • u,
      U.smul_mem _ hu, ?_, ?_⟩
    · funext i
      have a := congrFun h1 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul] at a ⊢
      rw [← a]; ring
    · funext i
      have a := congrFun h2 i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a ⊢
      rw [← Algebra.smul_def, map_smul, a, smul_zero]

theorem isCompl_descCompl (l : k' →ₗ[k] k) (hl : ∀ c : k, l (algebraMap k k' c) = c)
    (W : Submodule k (Fin n → k)) (U : Submodule k' (Fin n → k'))
    (h : IsCompl (extSub k' W) U) : IsCompl W (descCompl l W U) := by
  have hmem : ∀ v ∈ W, (fun i => algebraMap k k' (v i)) ∈ extSub k' W :=
    fun v hv => Submodule.subset_span ⟨v, hv, rfl⟩
  have hback : ∀ v : Fin n → k, (fun i => l (algebraMap k k' (v i))) = v :=
    fun v => funext fun i => hl (v i)
  constructor
  · rw [Submodule.disjoint_def]
    rintro v hv ⟨x, hx, u, hu, h1, h2⟩
    have hu' : u ∈ extSub k' W := by
      have e : u = (fun i => algebraMap k k' (v i)) - x := by rw [← h1]; abel
      rw [e]
      exact Submodule.sub_mem _ (hmem v hv) hx
    have hu0 : u = 0 := (Submodule.disjoint_def.mp h.disjoint) u hu' hu
    rw [hu0, add_zero] at h1
    rw [h1, hback] at h2
    exact h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : (fun i => algebraMap k k' (v i)) ∈ extSub k' W ⊔ U := by
      rw [h.sup_eq_top]
      trivial
    obtain ⟨x, hx, u, hu, hxu⟩ := Submodule.mem_sup.mp hv
    obtain ⟨w, hw⟩ : ∃ w : Fin n → k, w = fun i => l (x i) := ⟨_, rfl⟩
    have hwW : w ∈ W := hw ▸ form_mem l W x hx
    have hd : v - w ∈ descCompl l W U := by
      refine ⟨x - fun i => algebraMap k k' (w i), Submodule.sub_mem _ hx (hmem w hwW), u, hu, ?_, ?_⟩
      · funext i
        have e := congrFun hxu i
        simp only [Pi.add_apply, Pi.sub_apply, map_sub] at e ⊢
        rw [← e]
        ring
      · funext i
        simp [hw, hl]
    simpa using Submodule.add_mem_sup hwW hd

theorem descCompl_stable (l : k' →ₗ[k] k) (A : Matrix (Fin n) (Fin n) k)
    (W : Submodule k (Fin n → k)) (U : Submodule k' (Fin n → k'))
    (hA : ∀ v ∈ W, A.mulVec v ∈ W)
    (hU : ∀ u ∈ U, (A.map (algebraMap k k')).mulVec u ∈ U) :
    ∀ v ∈ descCompl l W U, A.mulVec v ∈ descCompl l W U := by
  rintro v ⟨x, hx, u, hu, h1, h2⟩
  refine ⟨(A.map (algebraMap k k')).mulVec x, extSub_stable A W hA x hx,
    (A.map (algebraMap k k')).mulVec u, hU u hu, ?_, ?_⟩
  · rw [← Matrix.mulVec_add, h1, ext_mulVec]
  · rw [form_mulVec, h2, Matrix.mulVec_zero]

end SlopeTestRemainingChoices

theorem isSSRep_of_mapRep {Γ k k' : Type} [Group Γ] [Field k] [Field k'] {n : ℕ}
    (ι : k →+* k') (ρ : Γ →* GL (Fin n) k) (h : IsSSRep (mapRep ι ρ)) : IsSSRep ρ := by
  let _ : Algebra k k' := ι.toAlgebra
  have hcoe : ∀ g, ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k') =
      (ρ g : Matrix (Fin n) (Fin n) k).map (algebraMap k k') := fun _ => rfl
  obtain ⟨l, hl⟩ := exists_retraction (k := k) (k' := k')
  intro W hW
  have hWe : IsInv (mapRep ι ρ) (extSub k' W) := fun g x hx => by
    rw [hcoe]
    exact extSub_stable _ W (hW g) x hx
  obtain ⟨U, hU, hc⟩ := h _ hWe
  refine ⟨descCompl l W U, fun g => ?_, isCompl_descCompl l hl W U hc⟩
  exact descCompl_stable l _ W U (hW g) fun u hu => by
    rw [← hcoe]
    exact hU g u hu

end GlobalTheory.RetractionComplement
end

section

open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.SSCont

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

theorem mem_imAlg_iff (r : Γ →* GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) :
    x ∈ PI.SSAscent.UnitaryGroupMassFormula.imAlg r ↔
      x ∈ Submodule.span k (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) := by
  have h : (Submonoid.closure (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) :
      Set (Matrix (Fin n) (Fin n) k)) = Set.range fun g => (r g : Matrix (Fin n) (Fin n) k) := by
    have e : (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) =
        (MonoidHom.mrange ((Units.coeHom _).comp r) : Set (Matrix (Fin n) (Fin n) k)) := by
      ext y
      simp
    rw [e, Submonoid.closure_eq]
  rw [PI.SSAscent.UnitaryGroupMassFormula.imAlg, ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span, h]

theorem exists_linear_of_trace [CharZero k] (r : Γ →* GL (Fin n) k) (hr : IsSSRep r) :
    ∃ (m : ℕ) (c : Fin m → Γ) (ψ : (Fin m → k) →ₗ[k] Matrix (Fin n) (Fin n) k),
      ∀ g, (r g : Matrix (Fin n) (Fin n) k) =
        ψ fun i => ((r (g * c i) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  have hnd : PI.SSAscent.UnitaryGroupMassFormula.TrNondeg (PI.SSAscent.UnitaryGroupMassFormula.imAlg r) :=
    PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent k Γ n r hr
  set S : Set (Matrix (Fin n) (Fin n) k) := Set.range fun g => (r g : Matrix (Fin n) (Fin n) k) with hS
  obtain ⟨f, hf, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq k S
  choose c hc using hf
  let φ : Submodule.span k S →ₗ[k] (Fin (Module.finrank k (Submodule.span k S)) → k) :=
    LinearMap.pi fun i => (Matrix.traceLinearMap (Fin n) k k) ∘ₗ (LinearMap.mulRight k (f i)) ∘ₗ
      (Submodule.span k S).subtype
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    refine hnd x.1 ((mem_imAlg_iff r _).2 x.2) fun y hy => ?_
    have hy' := (mem_imAlg_iff r _).1 hy
    rw [← hS, ← hspan] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      simpa [φ] using congrFun hx i
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
    | smul a y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ hφ
  refine ⟨_, c, (Submodule.span k S).subtype ∘ₗ ψ, fun g => ?_⟩
  let x : Submodule.span k S := ⟨r g, Submodule.subset_span ⟨g, rfl⟩⟩
  have h1 : (fun i => ((r (g * c i) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) = φ x := by
    funext i
    simp [φ, x, ← hc i]
  have h2 : ψ (φ x) = x := LinearMap.congr_fun hψ x
  rw [h1, LinearMap.comp_apply, h2]
  rfl

theorem continuous_of_continuous_trace : ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) (r : Γ →* GL (Fin n) k), IsSSRep r → Continuous (fun g => ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → Continuous r := by
  intro Γ k _ _ _ _ _ _ _ n r hr ht
  obtain ⟨m, c, ψ, h⟩ := exists_linear_of_trace r hr
  have hc : Continuous fun g => ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [funext h]
    exact ψ.continuous_on_pi.comp (continuous_pi fun i => ht.comp (continuous_mul_const (c i)))
  rw [Units.continuous_iff]
  refine ⟨hc, ?_⟩
  simp only [← map_inv]
  exact hc.comp continuous_inv

end GlobalTheory.SSCont
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_cyclotomic_integral_lattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) := by
  first | exact @GlobalTheory.CycIntegral.cyc_lattice | exact GlobalTheory.CycIntegral.cyc_lattice | (intros; apply GlobalTheory.CycIntegral.cyc_lattice <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

theorem _root_.GlobalTheory.T.exists_tateTwistDual_perfectPairing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → ∃ (ρ' : Representation ℚ_[l] ↥(GK K) (Fin (finrank ℚ_[l] V) → ℚ_[l])) (m : V →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l]), (∀ y, Continuous fun g => ρ' g y) ∧ IsDual1 (P.PD K) ρ ρ' m := by
  first | exact @GlobalTheory.DualTwist.exists_dual1 | exact GlobalTheory.DualTwist.exists_dual1 | (intros; apply GlobalTheory.DualTwist.exists_dual1 <;> assumption)
end
