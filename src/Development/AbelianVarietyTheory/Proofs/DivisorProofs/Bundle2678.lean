module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle113
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle383
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LocRegDesc

theorem exists_unit_mul_eq_of_flat {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R]
    (ρ : A →+* R) (hρ : ρ.Flat) (s b : A) (r : R) (hs : ρ s = ρ b * r) :
    ∃ g a : A, IsUnit (ρ g) ∧ g * s = b * a := by
  letI := ρ.toAlgebra
  haveI : Module.Flat A R := hρ
  have hrel : ∑ i, (![s, -b] : Fin 2 → A) i • (![1, r] : Fin 2 → R) i = 0 := by
    simp [Fin.sum_univ_two, Algebra.smul_def, RingHom.algebraMap_toAlgebra, hs]
  have ht : Module.IsTrivialRelation (![s, -b] : Fin 2 → A) (![1, r] : Fin 2 → R) :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨k, a, y, hx, hf⟩ := ht
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (ρ (a 0 j)) := by
    by_contra hne
    push_neg at hne
    have h1 : (1 : R) ∈ maximalIdeal R := by
      have := hx 0
      simp only [Matrix.cons_val_zero] at this
      rw [this]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      exact Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).2 (hne j))
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  refine ⟨a 0 j, a 1 j, hj, ?_⟩
  have := hf j
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  linear_combination this

end LocRegDesc

namespace LocRegDesc

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_kill_on_basicOpen (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (δ : Γ(X, W)) (hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0)
    (f : Γ(X, U.1)) (hf : X.basicOpen f ≤ W) :
    ∃ g, IsUnit (ρ g) ∧
      (X.presheaf.map (homOfLE hf).op).hom ((X.presheaf.map (homOfLE hWU).op).hom g * δ) = 0 := by
  haveI hloc := U.2.isLocalization_basicOpen f
  set δV := (X.presheaf.map (homOfLE hf).op).hom δ with hδV
  set hV := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom h with hhV
  have key : X.basicOpen hV = X.basicOpen f ⊓ X.basicOpen h := Scheme.basicOpen_res _ _ _
  have hB : X.basicOpen hV ≤ X.basicOpen h := key ▸ inf_le_right
  have hzero : (X.presheaf.map (homOfLE (X.basicOpen_le hV)).op).hom δV = 0 := by
    rw [hδV, res_res, ← res_res hh hB, hδ, map_zero]
  obtain ⟨n, hn⟩ :=
    exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X (U.2.basicOpen f).isCompact δV hV hzero
  obtain ⟨⟨e, m⟩, hem⟩ := IsLocalization.surj (Submonoid.powers f) δV
  simp only at hem
  have h0 : algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (h ^ n * e) = 0 := by
    rw [map_mul, ← hem, map_pow]
    change hV ^ n * (δV * _) = 0
    rw [← _root_.mul_assoc, hn, zero_mul]
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ _).1 h0
  simp only at hj
  have hc : ρ (f ^ j * e) = 0 := by
    have : ρ h ^ n * ρ (f ^ j * e) = 0 := by
      rw [← map_pow, ← map_mul, show h ^ n * (f ^ j * e) = f ^ j * (h ^ n * e) by ring, hj, map_zero]
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hρh)
  obtain ⟨g, a, hu, hg⟩ := exists_unit_mul_eq_of_flat ρ hρ (f ^ j * e) 0 0 (by simp [hc])
  refine ⟨g, hu, ?_⟩
  rw [map_mul, res_res]
  change algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) g * δV = 0
  have u1 : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (m : Γ(X, U.1))) :=
    IsLocalization.map_units _ m
  have u2 : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (f ^ j)) :=
    IsLocalization.map_units _ (⟨f ^ j, j, rfl⟩ : Submonoid.powers f)
  rw [← u1.mul_left_eq_zero, ← u2.mul_left_eq_zero, _root_.mul_assoc _ δV, hem, ← map_mul, ← map_mul,
    show g * e * f ^ j = g * (f ^ j * e) by ring, hg, zero_mul, map_zero]

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_kill (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (hW : IsCompact (W : Set X)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (δ : Γ(X, W)) (hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0) :
    ∃ g, IsUnit (ρ g) ∧ (X.presheaf.map (homOfLE hWU).op).hom g * δ = 0 := by
  let p : Set X → Prop := fun t => ∃ g, IsUnit (ρ g) ∧ ∀ y (hy : y ∈ W), y ∈ t →
    (X.presheaf.germ W y hy).hom ((X.presheaf.map (homOfLE hWU).op).hom g * δ) = 0
  have hp : p (W : Set X) := by
    refine hW.induction_on ?_ ?_ ?_ ?_
    · exact ⟨1, by simp, fun y _ hy => hy.elim⟩
    · rintro s t hst ⟨g, hg, H⟩
      exact ⟨g, hg, fun y hy hs => H y hy (hst hs)⟩
    · rintro s t ⟨g₁, hg₁, H₁⟩ ⟨g₂, hg₂, H₂⟩
      refine ⟨g₁ * g₂, by rw [map_mul]; exact hg₁.mul hg₂, fun y hy hyst => ?_⟩
      rw [map_mul (X.presheaf.map (homOfLE hWU).op).hom g₁ g₂]
      rcases hyst with hs | ht
      · rw [mul_right_comm, map_mul (X.presheaf.germ W y hy).hom, H₁ y hy hs, zero_mul]
      · rw [_root_.mul_assoc, map_mul (X.presheaf.germ W y hy).hom, H₂ y hy ht, mul_zero]
    · intro x hx
      obtain ⟨f, hf, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ (hWU hx)
      obtain ⟨g, hg, H⟩ := exists_unit_kill_on_basicOpen X U W hWU R ρ hρ h hh hρh δ hδ f hf
      refine ⟨X.basicOpen f, mem_nhdsWithin_of_mem_nhds ((X.basicOpen f).isOpen.mem_nhds hxf),
        g, hg, fun y hy hyf => ?_⟩
      rw [← X.presheaf.germ_res_apply (homOfLE hf) y hyf, H, map_zero]
  obtain ⟨g, hg, H⟩ := hp
  refine ⟨g, hg, ?_⟩
  refine TopCat.Presheaf.section_ext X.sheaf W _ 0 fun y hy => ?_
  exact (H y hy hy).trans (map_zero (X.presheaf.germ W y hy).hom).symm

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_one (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (hW : IsCompact (W : Set X)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (θ : Γ(X, W))
    (H : ∀ (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s =
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) *
        (X.presheaf.map (homOfLE hh).op).hom θ → ρ h ^ N ∣ ρ s) :
    ∃ g, IsUnit (ρ g) ∧ ∃ s : Γ(X, U.1),
      (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ := by
  haveI hloc := U.2.isLocalization_basicOpen h
  obtain ⟨⟨s, ⟨_, N, rfl⟩⟩, hsm⟩ :=
    IsLocalization.surj (Submonoid.powers h) ((X.presheaf.map (homOfLE hh).op).hom θ)
  simp only at hsm
  obtain ⟨r, hr⟩ := H s N (by
    change algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) s =
      algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N) * _
    rw [← hsm, mul_comm])
  obtain ⟨g₁, a, hu₁, hga⟩ := exists_unit_mul_eq_of_flat ρ hρ s (h ^ N) r (by rw [map_pow, hr])
  set δ := (X.presheaf.map (homOfLE hWU).op).hom a - (X.presheaf.map (homOfLE hWU).op).hom g₁ * θ
    with hδdef
  have hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0 := by
    have u : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N)) :=
      IsLocalization.map_units _ (⟨h ^ N, N, rfl⟩ : Submonoid.powers h)
    rw [← u.mul_left_eq_zero, hδdef, map_sub, map_mul, res_res, res_res]
    change (algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) a - algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) g₁ *
      (X.presheaf.map (homOfLE hh).op).hom θ) * algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N) = 0
    rw [sub_mul, _root_.mul_assoc, hsm, ← map_mul, ← map_mul, hga, mul_comm a, sub_self]
  obtain ⟨g₂, hu₂, hk⟩ := exists_unit_kill X U W hWU hW R ρ hρ h hh hρh δ hδ
  refine ⟨g₂ * g₁, by rw [map_mul]; exact hu₂.mul hu₁, g₂ * a, ?_⟩
  rw [map_mul, map_mul]
  rw [hδdef] at hk
  linear_combination hk

end LocRegDesc

theorem LocRegDesc.descent : ∀ (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens) (hWU : W ≤ U.1), IsCompact (W : Set X) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ρ : Γ(X, U.1) →+* R), ρ.Flat → ∀ mm : Ideal Γ(X, U.1), (maximalIdeal R).comap ρ = mm → ∀ (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W), ρ h ≠ 0 → ∀ (J : Type) [Finite J] (θ : J → Γ(X, W)), (∀ i (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s = (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) * (X.presheaf.map (homOfLE hh).op).hom (θ i) → ρ h ^ N ∣ ρ s) → ∃ g ∉ mm, ∀ i, ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ i := by
  intro X U W hWU hW R _ _ _ ρ hρ mm hmm h hh hρh J _ θ H
  choose g hg s hs using fun i => LocRegDesc.exists_unit_one X U W hWU hW R ρ hρ h hh hρh (θ i) (H i)
  haveI := Fintype.ofFinite J
  classical
  refine ⟨∏ i, g i, ?_, fun i => ⟨s i * ∏ j ∈ Finset.univ.erase i, g j, ?_⟩⟩
  · rw [← hmm, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_not, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hg i)
  · rw [map_mul, hs i, ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i), map_mul]
    ring

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ValExt

theorem exists_ext_centred : ∀ (p : ℕ) [Fact p.Prime] (A B : Type) [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)] (𝔷 : Ideal B), Function.Injective (algebraMap A B) → (∀ b : B, (∀ σ : B ≃ₐ[A] B, σ b = b) → b ∈ Set.range (algebraMap A B)) → 𝔷.IsMaximal → ∀ ev : A →+* PadicAlgCl p, (∀ a, ‖ev a‖ ≤ 1) → (∀ a ∈ IsLocalRing.maximalIdeal A, ‖ev a‖ < 1) → ∃ ev' : B →+* PadicAlgCl p, (∀ a, ev' (algebraMap A B a) = ev a) ∧ (∀ b, ‖ev' b‖ ≤ 1) ∧ ∀ b ∈ 𝔷, ‖ev' b‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.NormExtensionBound.main
  | exact _root_.GlobalTheory.NormExtensionBound.main
  | (apply _root_.GlobalTheory.NormExtensionBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormExtensionBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormExtensionBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormExtensionBound.main ..)

end GlobalTheory.ValExt
end

section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.chevalley_exists_le_sup_maximalIdeal_pow_of_antitone : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A) (J : Ideal A), Antitone K → (∀ e, maximalIdeal A ^ e ≤ K e) → (∀ (F : AdicCompletion (maximalIdeal A) A) (a : ℕ → A), (∀ n, F - algebraMap A (AdicCompletion (maximalIdeal A) A) (a n) ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) → (∀ n, a n ∈ K n) → F ∈ J.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) → ∀ k : ℕ, ∃ e : ℕ, K e ≤ J ⊔ maximalIdeal A ^ k := by
  first | exact @GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone | exact GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone | (intros; apply GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocReg

theorem exists_derivation_away {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (f : A)
    (hloc : letI := φ.toAlgebra; IsLocalization.Away f B) (d : A → A)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = x * d y + y * d x) :
    ∃ D : Derivation ℤ B B, ∀ a, D (φ a) = φ (d a) := by
  letI := φ.toAlgebra
  have h0 : d 0 = 0 := by
    have e := hadd 0 0
    rw [add_zero] at e
    linear_combination -e
  have h1 : d 1 = 0 := by
    have e := hmul 1 1
    rw [_root_.mul_one, _root_.one_mul] at e
    linear_combination -e
  let ψ : A →+* TrivSqZeroExt B B :=
    { toFun := fun a => TrivSqZeroExt.inl (φ a) + TrivSqZeroExt.inr (φ (d a))
      map_one' := by ext <;> simp [h1]
      map_mul' := fun x y => by
        ext
        · simp
        · simp [hmul]
          ring
      map_zero' := by ext <;> simp [h0]
      map_add' := fun x y => by ext <;> simp [hadd] }
  have hu : IsUnit (ψ f) := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    simpa [ψ, RingHom.algebraMap_toAlgebra] using IsLocalization.Away.algebraMap_isUnit (S := B) f)
  let Λ : B →+* TrivSqZeroExt B B := IsLocalization.Away.lift f hu
  have hΛ : ∀ a, Λ (φ a) = ψ a := fun a => IsLocalization.lift_eq (M := Submonoid.powers f) (S := B) _ a
  have hfst : ∀ x, (Λ x).fst = x := by
    have : (TrivSqZeroExt.fstHom ℤ B B).toRingHom.comp Λ = RingHom.id B := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun r => ?_)
      simp [RingHom.algebraMap_toAlgebra, hΛ, ψ]
    intro x
    exact congr($this x)
  let L : B →+ B :=
    { toFun := fun x => (Λ x).snd
      map_zero' := by simp
      map_add' := fun x y => by simp }
  refine ⟨Derivation.mk' L.toIntLinearMap (fun x y => ?_), fun a => ?_⟩
  · show (Λ (x * y)).snd = x • (Λ y).snd + y • (Λ x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [mul_comm]
  · show (Λ (φ a)).snd = φ (d a)
    rw [hΛ]
    simp [ψ]

theorem deriv_ext_basicOpen : ∀ (X : Scheme.{0}) (U W : X.affineOpens) (hWU : W.1 ≤ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)), (∀ r, DW ((X.presheaf.map (homOfLE hWU).op).hom r) = (X.presheaf.map (homOfLE hWU).op).hom (D r)) → ∀ (h : Γ(X, U.1)), X.basicOpen h ≤ W.1 → ∀ (R : Type) [CommRing R] [Algebra ℤ R] (g : Sp R ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U.1) (D' : Derivation ℤ R R), (∀ r, D' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U.1 ⊤ hg).hom r)) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U.1 ⊤ hg).hom (D r))) → ∃ (hUW : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ g ⁻¹ᵁ W.1) (D'' : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1)), (∀ r, D'' (((Sp R).presheaf.map (homOfLE (le_top : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ ⊤)).op).hom r) = ((Sp R).presheaf.map (homOfLE (le_top : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ ⊤)).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)))) ∧ (∀ θ, D'' ((g.appLE W.1 _ hUW).hom θ) = (g.appLE W.1 _ hUW).hom (DW θ)) := by

  intro X U W hWU D DW hDW h hhW R _ _ g hg D' hD'
  set e := Scheme.ΓSpecIso (CommRingCat.of R) with he
  set f := (g.appLE U.1 ⊤ hg).hom h with hf
  have hUW : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) f).1 ≤ g ⁻¹ᵁ W.1 := by
    show (Sp R).basicOpen f ≤ _
    rw [hf, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact fun x hx => hhW hx.2
  refine ⟨hUW, ?_⟩
  set U' := ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) f) with hU'
  let φ := ((Sp R).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom
  have hloc : letI := φ.toAlgebra; IsLocalization.Away f Γ(Sp R, U'.1) :=
    (isAffineOpen_top (Sp R)).isLocalization_basicOpen f
  obtain ⟨D'', hD''⟩ := exists_derivation_away φ f hloc (fun r => e.inv.hom (D' (e.hom.hom r)))
    (fun x y => by simp only [map_add (f := _)]) (fun x y => by
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _)]
      simp)
  refine ⟨D'', hD'', ?_⟩

  set resUW := (X.presheaf.map (homOfLE hWU).op).hom with hresUW
  set ψW := (g.appLE W.1 U'.1 hUW).hom with hψW
  have hUU : U'.1 ≤ g ⁻¹ᵁ U.1 := hUW.trans (fun x hx => hWU hx)
  set ψU := (g.appLE U.1 U'.1 hUU).hom with hψU
  have hψ : ∀ y, ψW (resUW y) = ψU y := fun y => by
    rw [hψW, hresUW, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have hψU' : ∀ y, ψU y = φ ((g.appLE U.1 ⊤ hg).hom y) := fun y => by
    rw [hψU, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hDU : ∀ y, D'' (ψU y) = ψU (D y) := fun y => by
    rw [hψU', hD'', hψU', hD']
    simp
  have hres : ∀ y, D'' (ψW (resUW y)) = ψW (DW (resUW y)) := fun y => by
    rw [hψ, hDU, hDW, hψ]
  have hunit : IsUnit (ψU h) := by
    rw [hψU']
    letI := φ.toAlgebra
    exact IsLocalization.Away.algebraMap_isUnit (S := Γ(Sp R, U'.1)) f
  have key : ∀ θ : Γ(X, W.1), ∃ (a : Γ(X, U.1)) (M : ℕ), resUW (h ^ M) * θ = resUW a := by
    intro θ
    set V := X.basicOpen (resUW h) with hVdef
    have hV : V = X.basicOpen h := by
      rw [hVdef, hresUW, Scheme.basicOpen_res]
      exact inf_eq_right.2 hhW
    have hVW : V ≤ W.1 := X.basicOpen_le _
    have hVU : V ≤ U.1 := hVW.trans hWU
    let resUV := (X.presheaf.map (homOfLE hVU).op).hom
    let resWV := (X.presheaf.map (homOfLE hVW).op).hom
    have hcomp : ∀ y, resWV (resUW y) = resUV y := fun y => by
      rw [hresUW, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have hlocU : letI := resUV.toAlgebra; IsLocalization.Away h Γ(X, V) :=
      U.2.isLocalization_of_eq_basicOpen h (homOfLE hVU) hV
    have hlocW : letI := resWV.toAlgebra; IsLocalization.Away (resUW h) Γ(X, V) :=
      W.2.isLocalization_basicOpen (resUW h)
    obtain ⟨⟨a, _, N, rfl⟩, hN⟩ := (letI := resUV.toAlgebra; IsLocalization.surj (Submonoid.powers h) (resWV θ))
    simp only [RingHom.algebraMap_toAlgebra] at hN
    rw [← hcomp, ← hcomp, ← map_mul] at hN
    letI := resWV.toAlgebra
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (resUW h)) (S := Γ(X, V))
      (x := θ * resUW (h ^ N)) (y := resUW a) (by simpa only [RingHom.algebraMap_toAlgebra] using hN)
    refine ⟨h ^ k * a, k + N, ?_⟩
    simp only [map_mul, map_pow] at hc ⊢
    linear_combination hc
  intro θ
  obtain ⟨a, M, hM⟩ := key θ
  have e2 := congrArg (fun x => D'' (ψW x)) hM
  have e3 := congrArg (fun x => ψW (DW x)) hM
  simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _)] at e2 e3
  rw [hres, hres] at e2
  have hu : IsUnit (ψW (resUW (h ^ M))) := by rw [hψ, map_pow]; exact hunit.pow M
  exact hu.mul_left_cancel (by linear_combination e2 - e3)

end GlobalTheory.LocReg
end
end

section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem dvd_of_map_dvd_of_valuationRing {V T : Type} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing T] [IsDomain T] (ψ : V →+* T) (hψ : Function.Injective ψ) [IsLocalHom ψ] {a b : V}
    (ha : a ≠ 0) (h : ψ a ∣ ψ b) : a ∣ b := by
  rcases ValuationRing.dvd_total a b with hab | hba
  · exact hab
  · obtain ⟨c, hc⟩ := hba
    obtain ⟨d, hd⟩ := h
    have hb : b ≠ 0 := by rintro rfl; exact ha (by simpa using hc)
    have hψb : ψ b ≠ 0 := fun e => hb (hψ (e.trans (map_zero ψ).symm))
    have h1 : ψ b * (ψ c * d) = ψ b * 1 := by
      rw [mul_one]; nth_rewrite 2 [hd]; rw [hc, map_mul]; ring
    have hcu : IsUnit (ψ c) := IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hψb h1)
    have hc' : IsUnit c := isUnit_of_map_unit ψ c hcu
    exact (Units.dvd_mul_right (u := hc'.unit)).mp (by rw [IsUnit.unit_spec, ← hc])

theorem dvd_of_forall_complete_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CharZero R] (f g : R), g ≠ 0 →
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V →
      ∀ ρ : R →+* V, Function.Injective ρ → IsLocalHom ρ → ρ g ∣ ρ f) → g ∣ f := by
  intro R _ _ _ _ _ _ f g hg H
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hg' : algebraMap R K g ≠ 0 := fun e => hg (hinj (e.trans (map_zero _).symm))
  by_contra hnd
  have hx : ¬ ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ r, algebraMap R K r ∈ V) →
      (∀ r ∈ maximalIdeal R, algebraMap R K r ∈ V.nonunits) →
      algebraMap R K f / algebraMap R K g ∈ V := by
    intro hall
    obtain ⟨r, hr⟩ := GlobalTheory.exists_algebraMap_eq_of_forall_discreteValuationSubring (R := R) (K := K) hall
    apply hnd
    refine ⟨r, hinj ?_⟩
    rw [map_mul, hr, mul_div_cancel₀ _ hg']
  push_neg at hx
  obtain ⟨V, hV, h1, h2, hxV⟩ := hx
  have hdom : LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring :=
    (GlobalTheory.localSubring_range_le_valuationSubring_iff _ _).mpr ⟨h1, h2⟩
  obtain ⟨-, hc, -, h, hρi, hρl⟩ :=
    (GlobalTheory.discreteValuationRing_dominating_noetherian_local R K K).2.2 V hdom
  have hd := H (AdicCompletion (maximalIdeal V) V) hc _ hρi hρl
  let a : V := ⟨algebraMap R K g, h g⟩
  let b : V := ⟨algebraMap R K f, h f⟩
  have ha : a ≠ 0 := fun e => hg' (congrArg Subtype.val e)
  obtain ⟨c, hcab⟩ := dvd_of_map_dvd_of_valuationRing (algebraMap V (AdicCompletion (maximalIdeal V) V))
    (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V) ha hd
  apply hxV
  have : algebraMap R K f = algebraMap R K g * (c : K) := congrArg Subtype.val hcab
  rw [this, mul_div_cancel_left₀ _ hg']
  exact c.2

end GlobalTheory.Poinc
end
