module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MulVecMemLatS
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle301
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParsevalContinuousPeriodicAdelicRationalQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc.DescBD

section Abstract

theorem exists_retr_abs {Z O O' K K' : Type} [CommRing Z] [CommRing O] [CommRing O'] [IsDedekindDomain O]
    [Field K] [Field K'] [Algebra O K] [IsFractionRing O K] [Algebra Z O] [Algebra Z O'] [Module.Finite Z O']
    (f : O →+* O') (hf : ∀ c, algebraMap Z O' c = f (algebraMap Z O c)) (j : O' →+* K') (φ : K →+* K')
    (hc : ∀ a, φ (algebraMap O K a) = j (f a)) (hs : ∀ x : K', ∃ a : K, a ≠ 0 ∧ ∃ y, j y = φ a * x) :
    ∃ R : K' →+ K, (∀ a x, R (φ a * x) = a * R x) ∧ (∀ a, R (φ a) = a) ∧ ∀ x, ∃ y, j y = φ (R (j x)) := by
  letI : Algebra K K' := φ.toAlgebra
  letI : Algebra O K' := (φ.comp (algebraMap O K)).toAlgebra
  letI : Algebra O O' := f.toAlgebra
  letI : Algebra O' K' := j.toAlgebra
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower O O' K' := IsScalarTower.of_algebraMap_eq hc
  haveI : IsScalarTower Z O O' := IsScalarTower.of_algebraMap_eq hf
  haveI : Module.Finite O O' := Module.Finite.of_restrictScalars_finite Z _ _
  let L : Submodule O K' := LinearMap.range (IsScalarTower.toAlgHom O O' K').toLinearMap
  haveI : Module.Finite O L := inferInstance
  have hsp : Submodule.span K (L : Set K') = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, y, hy⟩ := hs x
    have e : x = a⁻¹ • j y := by
      rw [hy]
      change x = φ a⁻¹ * (φ a * x)
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  obtain ⟨T, hT, hT'⟩ := GlobalTheory.St.G.Inter.exists_retraction (O := O) (K := K)
    (Algebra.linearMap K K') φ.injective L hsp
  exact ⟨T.toAddMonoidHom, fun a x => T.map_smul a x, hT, fun x => hT' (j x) ⟨x, rfl⟩⟩

theorem mem_BD_iff {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) {Γ : Type} [Group Γ] {k : ℕ}
    (N : Γ →* Matrix (Fin k) (Fin k) O) (z : Γ → (Fin k → K) ⧸ stdG O K k) :
    z ∈ BD (stdLatG hinj N) ↔ ∃ m : Fin k → K, ∀ g v, Submodule.Quotient.mk v = z g →
      ∃ u : Fin k → O, ∀ j, algebraMap O K (u j) = ∑ t, algebraMap O K (N g j t) * m t - m j - v j := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    refine ⟨m, fun g v hv => ?_⟩
    have hg := (congrFun hm g).trans hv.symm
    have hg' : matRep (mapM (algebraMap O K) N) g m - m - v ∈ stdG O K k := (Submodule.Quotient.eq _).1 hg
    obtain ⟨u, hu⟩ := hg'
    exact ⟨u, fun j => congrFun hu j⟩
  · rintro ⟨m, hm⟩
    refine ⟨Submodule.Quotient.mk m, funext fun g => ?_⟩
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (z g)
    obtain ⟨u, hu⟩ := hm g v hv
    have key : matRep (mapM (algebraMap O K) N) g m - m - v ∈ stdG O K k := ⟨u, funext hu⟩
    exact ((Submodule.Quotient.eq _).2 key).trans hv

theorem desc_abs {O K O' K' : Type} [CommRing O] [Field K] [Algebra O K] [CommRing O'] [Field K'] [Algebra O' K']
    (hinj : Function.Injective (algebraMap O K)) (hinj' : Function.Injective (algebraMap O' K'))
    (f : O →+* O') (φ : K →+* K') (hc : ∀ a, algebraMap O' K' (f a) = φ (algebraMap O K a))
    (R : K' →+ K) (hR : ∀ a x, R (φ a * x) = a * R x) (hR1 : ∀ a, R (φ a) = a)
    (hRO : ∀ x, ∃ y, algebraMap O K y = R (algebraMap O' K' x))
    {Γ : Type} [Group Γ] {k : ℕ} (N : Γ →* Matrix (Fin k) (Fin k) O)
    (q : (Fin k → K) ⧸ stdG O K k → (Fin k → K') ⧸ stdG O' K' k)
    (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk (fun j => φ (v j)))
    (z : Γ → (Fin k → K) ⧸ stdG O K k) (hz : (fun g => q (z g)) ∈ BD (stdLatG hinj' (mapM f N))) :
    z ∈ BD (stdLatG hinj N) := by
  obtain ⟨m, hm⟩ := (mem_BD_iff hinj' (mapM f N) (fun g => q (z g))).1 hz
  refine (mem_BD_iff hinj N z).2 ⟨fun j => R (m j), fun g v hv => ?_⟩
  obtain ⟨u, hu⟩ := hm g (fun j => φ (v j)) (by rw [← hv, hq])
  choose r hr using hRO
  refine ⟨fun j => r (u j), fun j => ?_⟩
  have hj : algebraMap O' K' (u j) = ∑ t, algebraMap O' K' (f (N g j t)) * m t - m j - φ (v j) := hu j

  rw [hr, hj, map_sub, map_sub, map_sum, hR1]
  simp only [hc, hR]

end Abstract

section Gen
variable {l : ℕ} [Fact l.Prime]

theorem exists_retr {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    ∃ R : ↥LL'.1 →+ ↥LL.1, (∀ a x, R (IntermediateField.inclusion h a * x) = a * R x) ∧
      (∀ a, R (IntermediateField.inclusion h a) = a) ∧ ∀ x ∈ OL LL', R x ∈ OL LL := by
  haveI := LL.2
  haveI := LL'.2
  haveI : IsDedekindDomain ↥(OL LL) := integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL') :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL'.1 (integralClosure ℤ_[l] ↥LL'.1)
  obtain ⟨R, h1, h2, h3⟩ := exists_retr_abs (Z := ℤ_[l]) (O := ↥(OL LL)) (O' := ↥(OL LL')) (K := ↥LL.1)
    (K' := ↥LL'.1) (incO h) (fun _ => rfl) (OL LL').val.toRingHom (IntermediateField.inclusion h).toRingHom
    (fun _ => rfl) (fun x => by
      have hx : IsAlgebraic ℤ_[l] x :=
        (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL'.1).2 (Algebra.IsAlgebraic.isAlgebraic x)
      obtain ⟨y, hy, hi⟩ := hx.exists_integral_multiple
      refine ⟨algebraMap ℤ_[l] ↥LL.1 y, ?_, ⟨y • x, hi⟩, Algebra.smul_def y x⟩
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
      simpa using hy)
  refine ⟨R, h1, h2, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h3 ⟨x, hx⟩
  have hy' : (y : ↥LL'.1) = ((IntermediateField.inclusion h).restrictScalars ℤ_[l]) (R x) := hy
  have : IsIntegral ℤ_[l] (((IntermediateField.inclusion h).restrictScalars ℤ_[l]) (R x)) := hy' ▸ y.2
  exact (isIntegral_algHom_iff ((IntermediateField.inclusion h).restrictScalars ℤ_[l])
    (IntermediateField.inclusion h).injective).1 this

theorem desc {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {Γ : Type} [Group Γ] {k : ℕ}
    (N : Γ →* Matrix (Fin k) (Fin k) ↥(OL LL))
    (z : Γ → (Fin k → ↥LL.1) ⧸ stdG ↥(OL LL) ↥LL.1 k)
    (hz : (fun g => liftQ h k (z g)) ∈
      BD (stdLatG (O := ↥(OL LL')) (LL := ↥LL'.1) Subtype.val_injective (mapM (incO h) N))) :
    z ∈ BD (stdLatG (O := ↥(OL LL)) (LL := ↥LL.1) Subtype.val_injective N) := by
  obtain ⟨R, hR, hR1, hRO⟩ := exists_retr h
  exact desc_abs (O := ↥(OL LL)) (K := ↥LL.1) (O' := ↥(OL LL')) (K' := ↥LL'.1) Subtype.val_injective
    Subtype.val_injective (incO h) (IntermediateField.inclusion h).toRingHom (fun _ => rfl) R hR hR1
    (fun x => ⟨⟨R x, hRO _ x.2⟩, rfl⟩) N (liftQ h k) (liftQ_mk h k) z hz

end Gen

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ BD (latC C (locOC C M)) → z ∈ BD (Br.locLat D.nbr i w hw M) :=
  fun D i w hw C _ M z hz => desc C.le (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w))) z hz

end GlobalTheory.UseLoc.DescBD
end

section

open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

theorem exists_linRetraction_of_isTorsionFree {R S : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] (hinj : Function.Injective (algebraMap R S))
    [Module.IsTorsionFree R (S ⧸ LinearMap.range (Algebra.linearMap R S))] :
    ∃ r : S →ₗ[R] R, r 1 = 1 := by
  set N := LinearMap.range (Algebra.linearMap R S) with hN
  haveI : Module.Free R (S ⧸ N) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let φ : S →ₗ[R] S := LinearMap.id - s ∘ₗ N.mkQ
  have hφ : ∀ x, φ x ∈ N := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hs (N.mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    have this' : (Submodule.Quotient.mk (s (Submodule.Quotient.mk x)) : S ⧸ N) = Submodule.Quotient.mk x := this
    simp [φ, Submodule.Quotient.mk_sub, this']
  have hinj' : Function.Injective (Algebra.linearMap R S) := hinj
  let e := LinearEquiv.ofInjective (Algebra.linearMap R S) hinj'
  refine ⟨e.symm.toLinearMap ∘ₗ φ.codRestrict N hφ, ?_⟩
  have h1 : (1 : S) ∈ N := ⟨1, map_one (algebraMap R S)⟩
  have hφ1 : φ 1 = 1 := by
    have : N.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero N).2 h1
    simp [φ, this]
  apply hinj'
  have := congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict N hφ 1))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.ofInjective_apply] at this
  rw [this, LinearMap.codRestrict_apply, hφ1, Algebra.linearMap_apply, map_one]

theorem isTorsionFree_quot_range {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (H : ∀ a : R, a ≠ 0 → ∀ (b : R) (z : S), algebraMap R S b = algebraMap R S a * z → ∃ c, algebraMap R S c = z) :
    Module.IsTorsionFree R (S ⧸ LinearMap.range (Algebra.linearMap R S)) := by
  refine ⟨fun a ha => ?_⟩
  intro x y hxy
  induction x using Submodule.Quotient.induction_on with | _ x => ?_
  induction y using Submodule.Quotient.induction_on with | _ y => ?_
  have hxy' : (Submodule.Quotient.mk (a • x) : S ⧸ LinearMap.range (Algebra.linearMap R S)) =
      Submodule.Quotient.mk (a • y) := hxy
  rw [Submodule.Quotient.eq] at hxy' ⊢
  obtain ⟨b, hb⟩ := hxy'
  rw [← smul_sub, Algebra.smul_def] at hb
  obtain ⟨c, hc⟩ := H a ha.ne_zero b (x - y) hb
  exact ⟨c, hc⟩

end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

theorem incO_injective {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    Function.Injective (incO h) := by
  intro a b hab
  have := congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) hab
  exact Subtype.ext (Subtype.ext this)

theorem incO_div {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {a b : ↥(OL LL)} (ha0 : a ≠ 0)
    {z : ↥(OL LL')} (hb : incO h b = incO h a * z) : ∃ c, incO h c = z := by
  have haL : ((a : ↥LL.1) : Om l) ≠ 0 := fun e => ha0 (Subtype.ext (Subtype.ext e))
  have hb' : ((b : ↥LL.1) : Om l) = ((a : ↥LL.1) : Om l) * ((z : ↥LL'.1) : Om l) :=
    congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) hb
  have hz : ((z : ↥LL'.1) : Om l) = ((b : ↥LL.1) : Om l) / ((a : ↥LL.1) : Om l) := by
    rw [eq_div_iff haL, mul_comm]
    exact hb'.symm
  have hc : (b : ↥LL.1) / (a : ↥LL.1) ∈ OL LL := by
    rw [Formalism.BasicNotions.Examples₂.LB.mem_OL]
    have hz1 := (Formalism.BasicNotions.Examples₂.LB.mem_OL LL' (z : ↥LL'.1)).1 z.2
    rw [hz] at hz1
    simpa using hz1
  refine ⟨⟨_, hc⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  change ((b : ↥LL.1) : Om l) / ((a : ↥LL.1) : Om l) = ((z : ↥LL'.1) : Om l)
  rw [hz]


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_intRetraction : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1),
    ∃ r : ↥(OL LL') →+ ↥(OL LL), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) ∧ r 1 = 1 := by
  intro l _ LL LL' h
  letI A : Algebra ↥(OL LL) ↥(OL LL') := (incO h).toAlgebra
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  haveI T : IsScalarTower ℤ_[l] ↥(OL LL) ↥(OL LL') := IsScalarTower.of_algebraMap_eq (fun x => by
    apply Subtype.ext; apply Subtype.ext; rfl)
  haveI : Module.Finite ℤ_[l] ↥(OL LL') := Formalism.BasicNotions.Examples₂.LB.OL_finite LL'
  haveI : Module.Finite ↥(OL LL) ↥(OL LL') := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI := isTorsionFree_quot_range (R := ↥(OL LL)) (S := ↥(OL LL')) (fun a ha b z hb => incO_div h ha hb)
  obtain ⟨r, hr⟩ := exists_linRetraction_of_isTorsionFree (R := ↥(OL LL)) (S := ↥(OL LL')) (incO_injective h)
  refine ⟨r.toAddMonoidHom, fun a x => ?_, hr⟩
  show r (incO h a * x) = a * r x
  have e1 : incO h a * x = a • x := (Algebra.smul_def a x).symm
  rw [e1, map_smul, smul_eq_mul]

end GlobalTheory.UseLoc
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DecomplPerf

section Generic

variable {U E R : Type} [CommRing U] [CommRing E] [CommRing R] (p : ℕ) (τ : U →* R)
  (φ : R →+* R) (io : E →+* R) (ψ : E → E)

theorem persist (hψ : ∀ e, io (ψ e) = φ (io e)) {x : R} {n : ℕ}
    (h : ∃ e r, φ^[n] x = io e + (p : R) * r) (k : ℕ) :
    ∃ e r, φ^[n + k] x = io e + (p : R) * r := by
  induction k with
  | zero => exact h
  | succ k ih =>
    obtain ⟨e, r, h⟩ := ih
    refine ⟨ψ e, φ r, ?_⟩
    rw [← add_assoc, Function.iterate_succ_apply', h, map_add (f := _), map_mul, map_natCast, hψ]

theorem closure_perf (hψ : ∀ e, io (ψ e) = φ (io e)) (h0 : τ 0 = 0)
    (hadd : ∀ x y, ∃ r, τ (x + y) = τ x + τ y + (p : R) * r)
    (hneg : ∀ x, ∃ r, τ (-x) = -τ x + (p : R) * r) (S : Set U)
    (hS : ∀ u ∈ S, ∃ n e r, φ^[n] (τ u) = io e + (p : R) * r) :
    ∀ u ∈ Subring.closure S, ∃ n e r, φ^[n] (τ u) = io e + (p : R) * r := by
  intro u hu
  induction hu using Subring.closure_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨0, 0, 0, by simp [h0]⟩
  | one => exact ⟨0, 1, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    obtain ⟨e, r, h⟩ := persist p φ io ψ hψ hn m
    obtain ⟨e', r', h'⟩ := persist p φ io ψ hψ hm n
    obtain ⟨c, hc⟩ := hadd x y
    rw [add_comm m n] at h'
    rw [← RingHom.coe_pow] at h h'
    refine ⟨n + m, e + e', r + r' + (φ ^ (n + m)) c, ?_⟩
    rw [← RingHom.coe_pow, hc, map_add (f := _), map_add (f := _), map_mul, map_natCast, h, h', map_add (f := _)]
    ring
  | neg x _ hx =>
    obtain ⟨n, e, r, h⟩ := hx
    obtain ⟨c, hc⟩ := hneg x
    rw [← RingHom.coe_pow] at h
    refine ⟨n, -e, -r + (φ ^ n) c, ?_⟩
    rw [← RingHom.coe_pow, hc, map_add (f := _), map_neg, map_mul, map_natCast, h, map_neg]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    obtain ⟨e, r, h⟩ := persist p φ io ψ hψ hn m
    obtain ⟨e', r', h'⟩ := persist p φ io ψ hψ hm n
    rw [add_comm m n] at h'
    rw [← RingHom.coe_pow] at h h'
    refine ⟨n + m, e * e', io e * r' + r * (io e' + p * r'), ?_⟩
    rw [← RingHom.coe_pow, map_mul, map_mul, h, h', map_mul]
    ring

theorem iterate_τ (hφ : ∀ u, φ (τ u) = τ (u ^ p)) (n : ℕ) (u : U) :
    φ^[n] (τ u) = τ (u ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, hφ, ← pow_mul, pow_succ]

end Generic

variable {l : ℕ} [Fact l.Prime]

def teichW (l : ℕ) [Fact l.Prime] : OCb l →* WCb l :=
  (inclW l : Ainf l →* WCb l).comp (WittVector.teichmuller l)

theorem teichW_apply (u : OCb l) : teichW l u = inclW l (WittVector.teichmuller l u) := rfl

theorem teichW_coeff (u : OCb l) : (teichW l u).coeff 0 = algebraMap (OCb l) (Cb l) u := by
  rw [teichW_apply, coeff_inclW, WittVector.teichmuller_coeff_zero]

theorem teichW_add (x y : OCb l) :
    ∃ r, teichW l (x + y) = teichW l x + teichW l y + (l : WCb l) * r := by
  obtain ⟨r, hr⟩ := (coeff_zero_eq_zero_iff (teichW l (x + y) - teichW l x - teichW l y)).1 (by
    rw [sub_coeff_zero, sub_coeff_zero, teichW_coeff, teichW_coeff, teichW_coeff, map_add (f := _)]
    ring)
  exact ⟨r, by linear_combination hr⟩

theorem teichW_zero : teichW l 0 = 0 := by
  rw [teichW_apply, WittVector.teichmuller_zero, map_zero]

theorem teichW_neg (x : OCb l) : ∃ r, teichW l (-x) = -teichW l x + (l : WCb l) * r := by
  obtain ⟨r, hr⟩ := teichW_add x (-x)
  rw [add_neg_cancel, teichW_zero] at hr
  exact ⟨-r, by linear_combination -hr⟩

theorem frobW_teichW (u : OCb l) : frobW l (teichW l u) = teichW l (u ^ l) := by
  change WittVector.map (frobenius (Cb l) l) (teichW l u) = _
  rw [teichW_apply, teichW_apply, inclW, WittVector.map_teichmuller, WittVector.map_teichmuller,
    WittVector.map_teichmuller, frobenius_def, ← map_pow]

theorem εroot_pow {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) : AI.εroot k ^ l ^ k = AI.ε := by
  induction k with
  | zero => simp [LocAinf.εroot]
  | succ k ih =>
    rw [LocAinf.εroot, Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p]
    exact ih

def rightW (LL : FinExt l) : WCb l →+* RW LL :=
  (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] RW LL).toRingHom

def teichR (LL : FinExt l) : OCb l →* RW LL := (rightW LL : WCb l →* RW LL).comp (teichW l)

theorem teichR_apply (LL : FinExt l) (u : OCb l) : teichR LL u = rightW LL (teichW l u) := rfl

theorem φRW_teichR (LL : FinExt l) (u : OCb l) :
    (φRW LL : RW LL →+* RW LL) (teichR LL u) = teichR LL (u ^ l) :=
  congrArg (rightW LL) (frobW_teichW u)

theorem teichR_εroot {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) :
    teichR LL (AI.εroot s) = piR AI LL s + 1 := by
  have h : teichW l (AI.εroot s) = inclW l (piW AI s) + 1 := by
    rw [piW, map_sub, map_one, sub_add_cancel, teichW_apply]
  rw [teichR_apply, h, map_add (f := _), map_one]
  rfl

theorem isIntegral_of_pow_eq_one {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {x : B}
    {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : IsIntegral A x :=
  IsIntegral.of_pow hm (hx ▸ isIntegral_one)

theorem add_one_pow_eq_ringHom_image_add_prime_mul_zero {E R : Type} [CommRing E] [CommRing R] (io : E →+* R) (p : ℕ) (a : E) (t : R)
    (ha : io a = t) (k : ℕ) : (t + 1) ^ k = io ((a + 1) ^ k) + (p : R) * 0 := by
  rw [map_pow, map_add (f := _), map_one, ha, mul_zero, add_zero]

theorem gen_aux₀ {E R : Type} [CommRing E] [CommRing R] (φ : R →+* R) (io : E →+* R) (p : ℕ)
    (a : E) (t : R) (ha : io a = t) : ∃ n e r, φ^[n] t = io e + (p : R) * r :=
  ⟨0, a, 0, by simp [ha]⟩



theorem teich_mem_perfection : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), ∀ u ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), ∃ (n : ℕ) (e : W.EE) (r : RW LL), (φRW LL)^[n] ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l u)) = E.tie.ioE e + (l : RW LL) * r := by
  intro l _ P AI K s LL h W E
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Decompl.ioE_compat l P AI K s LL h W E
  refine closure_perf l (teichR LL) (φRW LL : RW LL →+* RW LL) (E.tie.ioE : W.EE →+* RW LL)
    W.φE h1 ?_ ?_ ?_ _ ?_
  · rw [teichR_apply, teichW_zero]; exact (rightW LL).map_zero
  · intro x y
    obtain ⟨r, hr⟩ := teichW_add x y
    refine ⟨rightW LL r, ?_⟩
    rw [teichR_apply, teichR_apply, teichR_apply, hr, map_add (f := _), map_add (f := _),
      (rightW LL).map_mul, map_natCast (rightW LL)]
  · intro x
    obtain ⟨r, hr⟩ := teichW_neg x
    refine ⟨rightW LL r, ?_⟩
    rw [teichR_apply, teichR_apply, hr, map_add (f := _), (rightW LL).map_neg,
      (rightW LL).map_mul, map_natCast (rightW LL)]
  · rintro u (⟨k, rfl⟩ | ⟨c, hc, m, hm, hlm, hcm, hxb⟩)
    · refine ⟨k, (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ + 1) ^ l ^ s,
        0, ?_⟩
      have e1 := iterate_τ l (teichR LL) (φRW LL : RW LL →+* RW LL) (φRW_teichR LL) k (AI.εroot k)
      have e2 : teichR LL (AI.εroot k ^ l ^ k) = teichR LL (AI.εroot s) ^ l ^ s := by
        rw [εroot_pow, ← εroot_pow AI s]
        exact (teichR LL).map_pow _ _
      rw [teichR_εroot] at e2
      exact (e1.trans e2).trans (add_one_pow_eq_ringHom_image_add_prime_mul_zero (E.tie.ioE : W.EE →+* RW LL) l _ _ h3 _)
    · have hc' : (⟨c, hc⟩ : ↥(K0 K)) ^ m = 1 := Subtype.ext hcm
      have hint : ∀ i, IsIntegral ℤ_[l] (W.emb i ⟨c, hc⟩) := fun i =>
        isIntegral_of_pow_eq_one hm (by rw [← map_pow, hc', map_one])
      have e1 := E.inertia_action_on_roots ⟨c, hc⟩ m hm hlm hcm u hxb (fun i => ⟨W.emb i ⟨c, hc⟩, hint i⟩)
        (fun i => rfl)
      have e2 := (E.tie.ioE_ext _).trans (congrArg (inclR LL) e1)
      exact gen_aux₀ (φRW LL : RW LL →+* RW LL) (E.tie.ioE : W.EE →+* RW LL) l _ _ e2

end GlobalTheory.DecomplPerf
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem continuous_colT_good : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → Continuous (colT ψ (m + 1) f) := by
  intro E _ _ a ψ hψ m f hf
  have hl : ∀ (c : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) g, f (ratGL E a (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g
  have key := GlobalTheory.T.continuous_quotientAverage_periodic_family (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) (GA E a)
    (fun p => ψ (-dot (eLast a (m + 1)) p.2) * f (blkU p.2 * p.1)) ?_ ?_
  · exact key
  · refine (hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul
      (hf.cont.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))
  · intro g γ hγ y
    exact (per_coef hψ (eLast a (m + 1)) hf.cont hl g).2 γ hγ y

end GlobalTheory.CuspGeneric
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.parseval_continuous_periodic_adelicRationalQuotient : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ → ∀ [MeasurableSpace (ι → Ad E)] [BorelSpace (ι → Ad E)] (ν : Measure (ι → Ad E)) (D : Set (ι → Ad E)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratV E ι) D ν → ν D = 1 → ∑' ξ : ι → E, ‖avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x)‖ₑ ^ 2 = ∫⁻ x in D, ‖Φ x‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.AdelicParseval.tsum_enorm_avg_sq | exact GlobalTheory.AdelicParseval.tsum_enorm_avg_sq | (intros; apply GlobalTheory.AdelicParseval.tsum_enorm_avg_sq <;> assumption)
end
