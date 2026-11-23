module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Norm.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.DedekindDomain.Instances
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.GoingUp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumLift

theorem ker_factor_sq {R : Type} [CommRing R] (J : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R ⧸ J ^ (e + 1 + 1) →+* R ⧸ J ^ (e + 1)) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx hy
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have h := Ideal.mul_mem_mul hx hy
  rw [← pow_add] at h
  exact Ideal.pow_le_pow_right (by omega) h

end GlobalTheory.MumLift
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_maximalIdeal_pow_le_map_maximalIdeal (R : Type) [CommRing R] [IsLocalRing R]
    (R' : Type) [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R']
    [Module.Finite R R'] :
    ∃ N : ℕ, maximalIdeal R' ^ N ≤ (maximalIdeal R).map (algebraMap R R') := by
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hIP, hP⟩
    haveI := hP
    have hc : P.comap (algebraMap R R') = maximalIdeal R := by
      apply le_antisymm
      · exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap (algebraMap R R')).ne_top
      · exact Ideal.map_le_iff_le_comap.1 hIP
    have hmax : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) P (by
        change (P.comap (algebraMap R R')).IsMaximal
        rw [hc]; infer_instance)
    exact (IsLocalRing.eq_maximalIdeal hmax).ge
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg _
    (IsNoetherian.noetherian ((maximalIdeal R).map (algebraMap R R')).radical)
  exact ⟨n, (Ideal.pow_right_mono hrad n).trans hn⟩

theorem exists_compatible_maps_mod_pow_maximalIdeal_base : ∀ (R : Type) [CommRing R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R'] [Module.Finite R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (Γ : Type) (actC : Γ → (C' ≃ₐ[R] C')) (O : Type) [CommRing O] [Algebra R O] (i' : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')), (∀ e x y, Ideal.Quotient.mk _ y = i' (e + 1) x → Ideal.Quotient.mk _ y = i' e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i' e x → Ideal.Quotient.mk _ (actC σ y) = i' e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i' e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i' e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R' ^ (e + 1)).map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R')) → ∃ i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C'), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) ∧ (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (actC σ y) = i e x) ∧ (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) := by
  intro R _ _ R' _ _ _ _ _ C' _ _ _ _ Γ actC O _ _ i' hcomp hinv hsk
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_map_maximalIdeal R R'
  have hR' : ∀ e : ℕ, maximalIdeal R' ^ (N * (e + 1) + 1) ≤
      (maximalIdeal R ^ (e + 1)).map (algebraMap R R') := by
    intro e
    calc maximalIdeal R' ^ (N * (e + 1) + 1) ≤ maximalIdeal R' ^ (N * (e + 1)) :=
          Ideal.pow_le_pow_right (Nat.le_succ _)
      _ = (maximalIdeal R' ^ N) ^ (e + 1) := pow_mul _ _ _
      _ ≤ ((maximalIdeal R).map (algebraMap R R')) ^ (e + 1) := Ideal.pow_right_mono hN _
      _ = _ := (Ideal.map_pow _ _ _).symm
  have hle : ∀ e : ℕ, (maximalIdeal R' ^ (N * (e + 1) + 1)).map (algebraMap R' C') ≤
      (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
    intro e
    rw [Ideal.map_le_iff_le_comap]
    refine (hR' e).trans ?_
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp only [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact Ideal.mem_map_of_mem _ hr
  have hJ : ∀ e : ℕ, (maximalIdeal R ^ (e + 1 + 1)).map (algebraMap R C') ≤
      (maximalIdeal R ^ (e + 1)).map (algebraMap R C') :=
    fun e => Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))
  have hiter : ∀ a b : ℕ, a ≤ b → ∀ x y,
      Ideal.Quotient.mk ((maximalIdeal R' ^ (b + 1)).map (algebraMap R' C')) y = i' b x →
      Ideal.Quotient.mk ((maximalIdeal R' ^ (a + 1)).map (algebraMap R' C')) y = i' a x := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact fun x y h => h
    | succ b _ ih => exact fun x y h => ih x y (hcomp b x y h)
  let i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') :=
    fun e => (Ideal.Quotient.factorₐ R (hle e)).comp (i' (N * (e + 1)))
  have hi : ∀ e x, i e x = Ideal.Quotient.factorₐ R (hle e) (i' (N * (e + 1)) x) :=
    fun _ _ => rfl
  have hlift : ∀ e x y, Ideal.Quotient.mk ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')) y
      = i e x → ∃ y', Ideal.Quotient.mk ((maximalIdeal R' ^ (N * (e + 1) + 1)).map
        (algebraMap R' C')) y' = i' (N * (e + 1)) x ∧
        y - y' ∈ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
    intro e x y h
    obtain ⟨y', hy'⟩ := Ideal.Quotient.mk_surjective (i' (N * (e + 1)) x)
    refine ⟨y', hy', ?_⟩
    rw [← Ideal.Quotient.eq, h, hi, ← hy', Ideal.Quotient.factorₐ_apply_mk]
  refine ⟨i, ?_, ?_, ?_⟩
  · intro e x y h
    obtain ⟨y', hy', hd⟩ := hlift (e + 1) x y h
    have h2 := hiter (N * (e + 1)) (N * (e + 1 + 1)) (Nat.mul_le_mul_left _ (Nat.le_succ _)) x y' hy'
    rw [Ideal.Quotient.eq.2 (hJ e hd), hi, ← h2, Ideal.Quotient.factorₐ_apply_mk]
  · intro e σ x y h
    obtain ⟨y', hy', hd⟩ := hlift e x y h
    have hst : (maximalIdeal R ^ (e + 1)).map (algebraMap R C') ≤
        ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')).comap (actC σ) := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, AlgEquiv.commutes]
      exact Ideal.mem_map_of_mem _ hr
    have hσ : actC σ y - actC σ y' ∈ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
      rw [← map_sub]; exact hst hd
    rw [Ideal.Quotient.eq.2 hσ, hi, ← hinv (N * (e + 1)) σ x y' hy', Ideal.Quotient.factorₐ_apply_mk]
  · intro e
    obtain ⟨hsur, hker⟩ := hsk (N * (e + 1))
    set L' := Algebra.TensorProduct.lift (i' (N * (e + 1)))
      ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _
      with hL'
    have hfac : Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _)
        = (Ideal.Quotient.factorₐ R (hle e)).comp L' := by
      apply Algebra.TensorProduct.ext'
      intro a b
      rw [AlgHom.comp_apply, hL', Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
        map_mul, hi]
      congr 1
    rw [hfac]
    refine ⟨?_, ?_⟩
    · intro z
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨t, ht⟩ := hsur (Ideal.Quotient.mk _ c)
      exact ⟨t, by simp [ht, Ideal.Quotient.factorₐ_apply_mk]⟩
    apply le_antisymm
    · intro t ht
      rw [RingHom.mem_ker, AlgHom.comp_apply] at ht
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (L' t)
      have hcJ : c ∈ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.factorₐ_apply_mk R (hle e), hc]
        exact ht
      have hsub : (maximalIdeal R ^ (e + 1)).map (algebraMap R C') ≤
          (((maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))).map L').comap
            (Ideal.Quotient.mk ((maximalIdeal R' ^ (N * (e + 1) + 1)).map (algebraMap R' C'))) := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        simp only [Ideal.mem_comap, Ideal.Quotient.mk_algebraMap]
        rw [← AlgHom.commutes L' r]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr)
      have hmem := hsub hcJ
      rw [Ideal.mem_comap, hc] at hmem
      obtain ⟨t', ht'K, ht'⟩ := (Ideal.mem_map_iff_of_surjective L' hsur).1 hmem
      have hdiff : t - t' ∈ RingHom.ker L' := by
        rw [RingHom.mem_ker, map_sub, ht', sub_self]
      rw [hker] at hdiff
      have hKK : (maximalIdeal R' ^ (N * (e + 1) + 1)).map
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R') ≤
          (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R')) := by
        rw [Ideal.map_le_iff_le_comap]
        refine (hR' e).trans ?_
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        simp only [Ideal.mem_comap, AlgHom.commutes]
        exact Ideal.mem_map_of_mem _ hr
      simpa using Ideal.add_mem _ (hKK hdiff) ht'K
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
      rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hr

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open scoped Pointwise

namespace GlobalTheory.LocalNormalExt

theorem exists_eq_of_mul_mem_integralClosure
    (R K K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra R K'] [IsScalarTower R K K']
    (P : Ideal (integralClosure R K')) [P.IsMaximal]
    (x : K) (s : integralClosure R K') (hs : s ∉ P)
    (hx : algebraMap K K' x * (s : K') ∈ integralClosure R K') :
    ∃ r : R, algebraMap R K r = x := by
  classical
  let L := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R K' L := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R K K', ← IsScalarTower.algebraMap_apply K K' L]; rfl)
  haveI : FiniteDimensional K L := inferInstance
  haveI : IsGalois K L := inferInstance
  haveI : IsScalarTower R R L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S := integralClosure R L
  let C := integralClosure R K'
  haveI : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  let f : C →ₐ[R] S := ((IsScalarTower.toAlgHom R K' L).comp C.val).codRestrict S
    (fun c => (c.2 : IsIntegral R (c : K')).map (IsScalarTower.toAlgHom R K' L))
  have hfv : ∀ c : C, ((f c : S) : L) = algebraMap K' L (c : K') := fun _ => rfl
  have hfinj : Function.Injective f := by
    intro c d h
    have := congrArg (fun u : S => (u : L)) h
    simp only [hfv] at this
    exact Subtype.ext ((algebraMap K' L).injective this)
  letI : Algebra C S := f.toRingHom.toAlgebra
  haveI : IsScalarTower R C S := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : Algebra.IsIntegral C S := ⟨fun u => (Algebra.IsIntegral.isIntegral (R := R) u).tower_top⟩
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) P
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap C S)).mp hfinj]; exact bot_le)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  let J : Ideal S :=
    { carrier := {u | ∃ v : S, u * algebraMap R S a = algebraMap R S b * v}
      add_mem' := by
        rintro u₁ u₂ ⟨v₁, h₁⟩ ⟨v₂, h₂⟩
        exact ⟨v₁ + v₂, by rw [add_mul, h₁, h₂, mul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c u ⟨v, h⟩
        exact ⟨c * v, by rw [smul_eq_mul, _root_.mul_assoc, h, mul_left_comm]⟩ }
  have hJg : ∀ (g : S ≃ₐ[R] S) (u : S), u ∈ J → g u ∈ J := by
    rintro g u ⟨v, h⟩
    exact ⟨g v, by rw [← g.commutes a, ← g.commutes b, ← map_mul, h, map_mul]⟩

  have e1 : ∀ r : R, ((algebraMap R S r : S) : L) = algebraMap K L (algebraMap R K r) :=
    fun _ => rfl
  have hbL : algebraMap K L (algebraMap R K b) ≠ 0 := (map_ne_zero _).mpr hb0
  have htJ : f s ∈ J := by
    refine ⟨f ⟨_, hx⟩, ?_⟩
    apply Subtype.ext
    show (f s : L) * ((algebraMap R S a : S) : L) = ((algebraMap R S b : S) : L) * (f ⟨_, hx⟩ : L)
    rw [hfv, hfv, e1, e1]
    simp only [map_mul]
    rw [← IsScalarTower.algebraMap_apply K K' L, ← hab, map_div₀]
    field_simp
  have hmax : ∀ (I : Ideal S) [I.IsMaximal], I.under R = IsLocalRing.maximalIdeal R :=
    fun I _ => IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) I)
  have hJtop : J = ⊤ := by
    by_contra hne
    obtain ⟨N, hNmax, hJN⟩ := Ideal.exists_le_maximal J hne
    haveI : Finite (S ≃ₐ[R] S) := Finite.of_equiv _ (galRestrict R K L S).toEquiv
    haveI : Algebra.IsInvariant R S (S ≃ₐ[R] S) := Algebra.isInvariant_of_isGalois' R K L S
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := R) (B := S) (G := S ≃ₐ[R] S) Q N
      ((hmax Q).trans (hmax N).symm)
    set_option synthInstance.maxHeartbeats 200000 in
    have h1 : g • f s ∈ g • Q := by
      rw [← hg]; exact hJN (hJg g _ htJ)
    have h2 : f s ∈ Q := (Ideal.smul_mem_pointwise_smul_iff).mp h1
    exact hs (by rw [← hQ]; exact h2)
  obtain ⟨v, hv⟩ : (1 : S) ∈ J := hJtop ▸ Submodule.mem_top
  have hvL : (v : L) = algebraMap K L x := by
    have := congrArg (fun u : S => (u : L)) hv
    simp only [_root_.one_mul, Subalgebra.coe_mul, e1] at this
    rw [← hab, map_div₀, this]
    field_simp
  have hint : IsIntegral R (algebraMap K L x) := hvL ▸ v.2
  have hxint : IsIntegral R x :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).mp hint
  exact IsIntegrallyClosed.isIntegral_iff.mp hxint

theorem exists_local_normal_domain_of_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (ρ : R →+* R') (e : FractionRing R' ≃+* K'), IsLocalHom ρ ∧ Function.Injective ρ ∧ (∀ r, e (algebraMap R' _ (ρ r)) = algebraMap (FractionRing R) K' (algebraMap R _ r)) ∧ ∀ (x : FractionRing R) (w : R'), e (algebraMap R' _ w) = algebraMap (FractionRing R) K' x → ∃ r : R, algebraMap R _ r = x := by
  intro R _ _ _ _ _ _ K' _ _ _
  classical
  let K := FractionRing R
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  letI : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let C := integralClosure R K'
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension K K'
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  haveI : IsNoetherianRing C := IsIntegralClosure.isNoetherianRing R K K' C
  haveI : IsDomain C := inferInstance
  obtain ⟨m', hm'⟩ := Ideal.exists_maximal C
  obtain ⟨R', _, _, _⟩ : ∃ (R' : Type) (_ : CommRing R') (_ : Algebra C R'),
      IsLocalization.AtPrime R' m' :=
    ⟨Localization.AtPrime m', inferInstance, inferInstance, inferInstance⟩
  haveI : IsLocalRing R' := IsLocalization.AtPrime.isLocalRing R' m'
  haveI : IsDomain R' :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := m'.primeCompl) (S := R') m'.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing R' := IsLocalization.isNoetherianRing m'.primeCompl R' inferInstance
  haveI : IsIntegrallyClosed R' :=
    isIntegrallyClosed_of_isLocalization R' m'.primeCompl m'.primeCompl_le_nonZeroDivisors
  letI : Algebra R' K' := (IsLocalization.lift (M := m'.primeCompl) (S := R') (g := algebraMap C K')
    (fun y => IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C K')).mpr
      (fun h => y.2 (h ▸ m'.zero_mem))))).toAlgebra
  haveI : IsScalarTower C R' K' :=
    IsScalarTower.of_algebraMap_eq (fun c => (IsLocalization.lift_eq _ c).symm)
  haveI : IsFractionRing R' K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m'.primeCompl R' K'
  let e : FractionRing R' ≃+* K' :=
    (FractionRing.algEquiv R' K').toRingEquiv
  have he : ∀ w : R', e (algebraMap R' _ w) = algebraMap R' K' w := fun w =>
    (FractionRing.algEquiv R' K').commutes w
  have hRC : ∀ r : R, algebraMap C K' (algebraMap R C r) = algebraMap K K' (algebraMap R K r) :=
    fun _ => rfl
  have hinjRC : Function.Injective (algebraMap R C) := by
    intro a b h
    have := congrArg (algebraMap C K') h
    rw [hRC, hRC] at this
    exact IsFractionRing.injective R K ((algebraMap K K').injective this)
  have hinjCR' : Function.Injective (algebraMap C R') :=
    IsLocalization.injective R' m'.primeCompl_le_nonZeroDivisors
  have hcomap : m'.comap (algebraMap R C) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) m')
  refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap C R').comp (algebraMap R C), e, ?_, hinjCR'.comp hinjRC, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    by_contra hnu
    have h1 : algebraMap R C r ∈ m' := by
      rw [← Ideal.mem_comap, hcomap]; exact hnu
    have h2 : algebraMap C R' (algebraMap R C r) ∈ IsLocalRing.maximalIdeal R' := by
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff R' m']; exact h1
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 hr
  · intro r
    rw [he]
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply C R' K', hRC]
  · intro x w hw
    rw [he] at hw
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective m'.primeCompl w
    have hmul : algebraMap K K' x * (s : C) = (c : K') := by
      rw [← hw]
      have := congrArg (algebraMap R' K') (IsLocalization.mk'_spec R' c s)
      rw [map_mul, ← IsScalarTower.algebraMap_apply C R' K', ← IsScalarTower.algebraMap_apply C R' K'] at this
      exact this
    exact exists_eq_of_mul_mem_integralClosure R K K' m' x (s : C) s.2 (hmul ▸ c.2)

end GlobalTheory.LocalNormalExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem algebraMap_norm_mem_span_singleton (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] (f : B) :
    algebraMap A B (Algebra.norm A f) ∈ Ideal.span {f} := by
  set g : B →ₗ[A] B := Algebra.lmul A B f with hg
  set p := g.charpoly
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p)
  have h0 : Polynomial.aeval f p = 0 := by
    have h1 : Polynomial.aeval g p = 0 := LinearMap.aeval_self_charpoly g
    rw [hg, Polynomial.aeval_algHom_apply] at h1
    have h2 := congrArg (fun u : B →ₗ[A] B => u 1) h1
    simpa using h2
  have h3 := congrArg (Polynomial.aeval f) hq
  simp only [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, h0, zero_sub] at h3
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul,
    show algebraMap A B (g.charpoly.coeff 0) = -(f * Polynomial.aeval f q) by
      rw [← h3, neg_neg]]
  exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))

theorem norm_not_mem_iff (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] (f : B) (P : PrimeSpectrum A) :
    Algebra.norm A f ∉ P.asIdeal ↔
      ∀ Q : PrimeSpectrum B, Q.asIdeal.comap (algebraMap A B) = P.asIdeal → f ∉ Q.asIdeal := by
  constructor
  · intro hN Q hQ hf
    apply hN
    rw [← hQ, Ideal.mem_comap]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hf (algebraMap_norm_mem_span_singleton A B f)
  · intro h hN
    let Rₘ := Localization.AtPrime P.asIdeal
    let Sₘ := Localization (Algebra.algebraMapSubmonoid B P.asIdeal.primeCompl)
    have hnu : ¬ IsUnit (algebraMap B Sₘ f) := by
      intro hu
      have h1 := hu.map (Algebra.norm Rₘ (S := Sₘ))
      rw [Algebra.norm_localization A P.asIdeal.primeCompl] at h1
      exact (IsLocalization.AtPrime.isUnit_to_map_iff Rₘ P.asIdeal _).mp h1 hN
    obtain ⟨M, hM, hfM⟩ := exists_max_ideal_of_mem_nonunits hnu
    haveI : Module.Finite Rₘ Sₘ := Module.Finite.of_basis
      ((Module.Free.chooseBasis A B).localizationLocalization Rₘ P.asIdeal.primeCompl Sₘ)
    have hMc : M.comap (algebraMap Rₘ Sₘ) = IsLocalRing.maximalIdeal Rₘ :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Rₘ) M)
    refine h ⟨M.comap (algebraMap B Sₘ), hM.isPrime.comap _⟩ ?_ hfM
    show (M.comap (algebraMap B Sₘ)).comap (algebraMap A B) = P.asIdeal
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A Rₘ Sₘ,
      ← Ideal.comap_comap, hMc]
    exact Localization.AtPrime.under_maximalIdeal

end GlobalTheory.Mum
end
