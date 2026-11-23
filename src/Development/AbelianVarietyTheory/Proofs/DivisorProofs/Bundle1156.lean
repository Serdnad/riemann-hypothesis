module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle007
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Mathlib.Algebra.WithConv
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle990
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerfPairField

open Module

theorem eq_zero_of_mem_of_flip_ker {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (φ : V →ₗ[K] W →ₗ[K] K) (A : Submodule K V) (B : Submodule K W)
    (hdim : finrank K A + finrank K B ≤ finrank K W)
    (h : ∀ y, (∀ x ∈ A, φ x y = 0) → y ∈ B) :
    ∀ x ∈ A, φ x = 0 → x = 0 := by
  intro x hx hφx
  set T : W →ₗ[K] Module.Dual K A := (φ.domRestrict A).flip with hT
  have hker : LinearMap.ker T ≤ B := by
    intro y hy
    apply h y
    intro a ha
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp hy) ⟨a, ha⟩
    simpa [hT] using this
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  have hkb := Submodule.finrank_mono hker
  have hdA : finrank K (Module.Dual K A) = finrank K A := Subspace.dual_finrank_eq
  have htop : LinearMap.range T = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (LinearMap.range T)
    omega
  have hx0 : (⟨x, hx⟩ : A) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro f
    obtain ⟨y, rfl⟩ : f ∈ LinearMap.range T := htop ▸ Submodule.mem_top
    simp [hT, hφx]
  simpa using congrArg Subtype.val hx0

end GlobalTheory.PerfPairField

open Module in
theorem GlobalTheory.PerfPairField.isPerfPair_of_kernel_conditions : ∀ (k : Type) [Field k] (M N : Type 1) [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [FiniteDimensional k M] [FiniteDimensional k N] (F : Submodule k M) (F' : Submodule k N) (g : ℕ), Module.finrank k M = 2 * g → Module.finrank k N = 2 * g → Module.finrank k F = g → Module.finrank k F' = g → ∀ φ : Module.Dual k M →ₗ[k] Module.Dual k N →ₗ[k] k, (∀ x, (∀ y ∈ F'.dualAnnihilator, φ x y = 0) → x ∈ F.dualAnnihilator) → (∀ y, (∀ x ∈ F.dualAnnihilator, φ x y = 0) → y ∈ F'.dualAnnihilator) → φ.IsPerfPair := by
  intro k _ M N _ _ _ _ _ _ F F' g hM hN hF hF' φ h1 h2
  have eM := Subspace.finrank_add_finrank_dualAnnihilator_eq F
  have eN := Subspace.finrank_add_finrank_dualAnnihilator_eq F'
  have dM : finrank k (Module.Dual k M) = 2 * g := by rw [Subspace.dual_finrank_eq, hM]
  have dN : finrank k (Module.Dual k N) = 2 * g := by rw [Subspace.dual_finrank_eq, hN]
  apply LinearMap.IsPerfPair.of_injective
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hA : x ∈ F.dualAnnihilator := h1 x (fun y _ => by simp [hx])
    exact GlobalTheory.PerfPairField.eq_zero_of_mem_of_flip_ker φ F.dualAnnihilator F'.dualAnnihilator
      (by omega) h2 x hA hx
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hB : y ∈ F'.dualAnnihilator := h2 y (fun x _ => by
      have := LinearMap.congr_fun hy x
      simpa using this)
    exact GlobalTheory.PerfPairField.eq_zero_of_mem_of_flip_ker φ.flip F'.dualAnnihilator F.dualAnnihilator
      (by omega) (fun x hx => h1 x (fun y hy => by simpa using hx y hy)) y hB hy
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem span_natCast_pow_eq_bot_of_isNilpotent (p : ℕ) (R : Type) [CommRing R]
    (h : IsNilpotent (p : R)) : ∃ N : ℕ, Ideal.span {(p : R)} ^ N • (⊤ : Submodule R R) = ⊥ := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  rw [Ideal.span_singleton_pow, hN, smul_eq_mul, Ideal.mul_top]
  simp

theorem isAdicComplete_span_natCast_of_isNilpotent :
    ∀ (p : ℕ) (R : Type) [CommRing R], IsNilpotent (p : R) →
      IsAdicComplete (Ideal.span {(p : R)}) R := by
  intro p R _ h
  obtain ⟨N, hN⟩ := span_natCast_pow_eq_bot_of_isNilpotent p R h
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have := hx N
    rwa [hN, SModEq.bot] at this
  · intro f hf
    refine ⟨f N, fun n => ?_⟩
    rcases le_total n N with hn | hn
    · exact hf hn
    · have h1 := hf hn
      rw [hN, SModEq.bot] at h1
      rw [h1]
end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmitsurCohomologyH1

noncomputable def d0 (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D'] :
    D' →ₗ[D] D' ⊗[D] D' :=
  TensorProduct.mk D D' D' 1 - (TensorProduct.mk D D' D').flip 1

theorem amitsur_d0_apply (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D'] (a : D') :
    d0 D D' a = (1 : D') ⊗ₜ[D] a - a ⊗ₜ[D] (1 : D') := by
  simp [d0]

theorem cocycle_is_coboundary : ∀ (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D']
    [Module.FaithfullyFlat D D'] (c : D' ⊗[D] D'),
    (∀ (E : Type) [CommRing E] [Algebra D E] (f₁ f₂ f₃ : D' →ₐ[D] E),
      Algebra.TensorProduct.lift f₁ f₃ (fun _ _ ↦ Commute.all _ _) c =
        Algebra.TensorProduct.lift f₁ f₂ (fun _ _ ↦ Commute.all _ _) c +
          Algebra.TensorProduct.lift f₂ f₃ (fun _ _ ↦ Commute.all _ _) c) →
    ∃ a : D', c = (1 : D') ⊗ₜ[D] a - a ⊗ₜ[D] (1 : D') := by
  intro D D' _ _ _ _ c hc
  let i1 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') := Algebra.TensorProduct.includeLeft
  let i2 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') :=
    (Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeLeft
  let i3 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') :=
    (Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeRight
  have h := hc (D' ⊗[D] (D' ⊗[D] D')) i1 i2 i3
  have k1 : ∀ x : D' ⊗[D] D',
      Algebra.TensorProduct.lift i1 i3 (fun _ _ ↦ Commute.all _ _) x -
        Algebra.TensorProduct.lift i1 i2 (fun _ _ ↦ Commute.all _ _) x =
        LinearMap.lTensor D' (d0 D D') x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      simp [i1, i2, i3, amitsur_d0_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), ← hx, ← hy]; abel
  have k2 : ∀ x : D' ⊗[D] D',
      Algebra.TensorProduct.lift i2 i3 (fun _ _ ↦ Commute.all _ _) x = (1 : D') ⊗ₜ[D] x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      simp [i2, i3, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      rw [map_add (f := _), hx, hy, TensorProduct.tmul_add]
  have key : (1 : D') ⊗ₜ[D] c = LinearMap.lTensor D' (d0 D D') c := by
    rw [← k1, ← k2, h]; abel
  let q := (LinearMap.range (d0 D D')).mkQ
  have hq : (1 : D') ⊗ₜ[D] q c = 0 := by
    have : (1 : D') ⊗ₜ[D] q c = LinearMap.lTensor D' q ((1 : D') ⊗ₜ[D] c) := by simp
    rw [this, key, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have hz : q ∘ₗ d0 D D' = 0 := by
      ext a; simp [q]
    rw [hz]; simp
  have hq0 : q c = 0 := (Module.FaithfullyFlat.one_tmul_eq_zero_iff D _ (A := D') _).1 hq
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hq0
  exact ⟨a, by rw [← ha, amitsur_d0_apply]⟩

end GlobalTheory.AmitsurCohomologyH1
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ff_descent_elem : ∀ (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D']
    [Module.FaithfullyFlat D D'] (a : D'), a ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] a →
      ∃ e : D, algebraMap D D' e = a := by
  intro D D' _ _ _ _ a h
  have hx : FlatDescent.amitsurDiff (A := D) D' D (a ⊗ₜ[D] (1 : D)) = 0 := by
    apply (LinearEquiv.lTensor D' (TensorProduct.rid D D')).injective
    simp [FlatDescent.amitsurDiff_tmul, h]
  obtain ⟨m, hm⟩ := ((FlatDescent.amitsur_exact (A := D) (B := D') (M := D)).2 _).1 hx
  refine ⟨m, ?_⟩
  have := congrArg (TensorProduct.rid D D') hm
  simpa [Algebra.algebraMap_eq_smul_one] using this

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_pushout_faithfullyFlat : ∀ (R : Type) [CommRing R] (D D' E : Type) [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E] [Algebra R E] (ψ : D →ₐ[R] D') (φ : D →ₐ[R] E), (ψ : D →+* D').FaithfullyFlat → ∃ (E' : Type) (_ : CommRing E') (_ : Algebra R E') (ψ' : E →ₐ[R] E') (φ' : D' →ₐ[R] E'), (ψ' : E →+* E').FaithfullyFlat ∧ ψ'.comp φ = φ'.comp ψ := by
  intro R _ D D' E _ _ _ _ _ _ ψ φ hψ
  letI : Algebra D E := φ.toRingHom.toAlgebra
  letI : Algebra D D' := ψ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  let f : E →+* TensorProduct D E D' := Algebra.TensorProduct.includeLeftRingHom
  let g : D' →+* TensorProduct D E D' := (Algebra.TensorProduct.includeRight : D' →ₐ[D] _).toRingHom
  have hfg : f.comp (algebraMap D E) = g.comp (algebraMap D D') :=
    RingHom.ext fun d => by
      change (algebraMap D E d) ⊗ₜ[D] (1 : D') = (1 : E) ⊗ₜ[D] algebraMap D D' d
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  letI iR : Algebra R (TensorProduct D E D') := (f.comp (algebraMap R E)).toAlgebra
  have hf : f.FaithfullyFlat := by
    have : Module.FaithfullyFlat E (TensorProduct D E D') := inferInstance
    exact (RingHom.faithfullyFlat_algebraMap_iff).2 this
  refine ⟨TensorProduct D E D', inferInstance, iR,
    { f with commutes' := fun r => rfl },
    { g with commutes' := fun r => ?_ }, hf, ?_⟩
  · change g (algebraMap R D' r) = f (algebraMap R E r)
    rw [← ψ.commutes r, ← φ.commutes r]
    exact (congrArg (fun h => h (algebraMap R D r)) hfg).symm
  · ext d
    exact congrArg (fun h => h d) hfg

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GlobalVerticalUnit
open GlobalTheory.VerticalUnit

theorem exists_const_mul_eq_gen : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K) (M : LB X.left) (c : LB.Gen (M.pull φ)), Smooth X.hom → QuasiCompact X.hom → GeometricallyConnected X.hom → IsPullback φ p X.hom (spMap (algebraMap R K)) → M.IsLB → c.IsGen → ∃ (a : Kˣ) (u : LB.Gen M), u.IsGen ∧ ∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val := by
  intro R K _ _ _ _ _ _ _ X Y φ p M c hsm hqc hgc H hM hc
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ X.hom hsm hgc
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian X.hom
  have : IsIntegral Y := DvrModel.isIntegral_of_geometricallyIntegral H
  have := isNormalScheme_of_smooth X.hom
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : AlgebraicGeometry.IsNoetherian X.left := {}
  have hinj := IsFractionRing.injective R K
  have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) H.flip
    (Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance))
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip
    (IsPreimmersion.of_isLocalization (nonZeroDivisors R))
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks φ
  have lift : ∀ x : X.left, (X.hom x).asIdeal = ⊥ → ∃ y, φ y = x := fun x hx => by
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H x (⊥ : PrimeSpectrum K)
      (PrimeSpectrum.ext (hx.trans (Ideal.comap_bot_of_injective _ hinj).symm))
    exact ⟨y, hy⟩
  have hφ : φ (genericPoint Y) ⤳ genericPoint X.left := by
    obtain ⟨y, hy⟩ := (Flat.generalizingMap φ).stableUnderGeneralization_range
      (genericPoint_specializes (φ (genericPoint Y))) ⟨_, rfl⟩
    exact hy ▸ (genericPoint_specializes y).map φ.continuous
  have hne : ∀ (V : X.left.Opens) [Nonempty V], Nonempty (φ ⁻¹ᵁ V) := fun V _ =>
    ⟨⟨_, hφ.mem_open V.isOpen (genericPoint_mem_opens V)⟩⟩
  have hne' : ∀ i [Nonempty (M.U i)], Nonempty ((M.pull φ).U fun _ => i) := fun i _ => by
    rw [DvrModel.pull_U]; exact hne _
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  have hb := ffMap_bijective φ hφ
  obtain ⟨r, hr⟩ : ∃ r : M.ι → X.left.functionField, ∀ i [Nonempty ((M.pull φ).U fun _ => i)],
      ffMap φ hφ (r i) = Y.germToFunctionField _ (c.s fun _ => i).val := by
    have : ∀ i, ∃ t : X.left.functionField, ∀ [Nonempty ((M.pull φ).U fun _ => i)],
        ffMap φ hφ t = Y.germToFunctionField _ (c.s fun _ => i).val := fun i => by
      by_cases h : Nonempty ((M.pull φ).U fun _ => i)
      · exact (hb.2 (Y.germToFunctionField _ (c.s fun _ => i).val)).imp fun _ h => h
      · exact ⟨0, @fun h' => (h h').elim⟩
    exact ⟨fun i => (this i).choose, fun i => (this i).choose_spec⟩
  let k : K →+* Γ(Y, ⊤) := (p.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let κ : K →+* X.left.functionField := (RingEquiv.ofBijective (ffMap φ hφ).hom hb).symm.toRingHom.comp
    ((Y.germToFunctionField ⊤).hom.comp k)
  have hκ : ∀ a, ffMap φ hφ (κ a) = Y.germToFunctionField ⊤ (constFn p ⊤ a) := fun a =>
    (RingEquiv.ofBijective (ffMap φ hφ).hom hb).apply_symm_apply _
  have hr0 : ∀ i x, x ∈ M.U i → r i ≠ 0 := fun i x hx h => by
    have : Nonempty (M.U i) := ⟨⟨x, hx⟩⟩
    have := hne' i
    have e := hr i
    rw [h, map_zero] at e
    exact ((Units.isUnit _).map _).ne_zero e.symm
  have hg : ∀ i j (x : X.left) (hi : x ∈ M.U i) (hj : x ∈ M.U j),
      haveI : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
      r i = X.left.germToFunctionField (M.U i ⊓ M.U j) (M.g i j).val * r j := by
    intro i j x hi hj
    have : Nonempty (M.U i) := ⟨⟨x, hi⟩⟩
    have : Nonempty (M.U j) := ⟨⟨x, hj⟩⟩
    have : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
    have := hne' i
    have := hne' j
    have := nonempty_inf_of_isIntegral ((M.pull φ).U fun _ => i) ((M.pull φ).U fun _ => j)
    refine hb.1 ?_
    have e := congrArg (Y.germToFunctionField _) (congrArg Units.val (hc (fun _ => i) fun _ => j))
    rw [Units.val_mul, map_mul, DvrModel.coe_pull_g, ← ffMap_germ φ hφ] at e
    rw [map_mul, hr, hr]
    exact (germToFunctionField_res _ _).symm.trans (e.trans (congrArg _ (germToFunctionField_res _ _)))
  have htr : ∀ i j x t, x ∈ M.U i → x ∈ M.U j → VerticalUnit.UnitAt x (t * r j) → VerticalUnit.UnitAt x (t * r i) := by
    intro i j x t hi hj h
    rw [hg i j x hi hj, mul_left_comm]
    exact VerticalUnit.UnitAt.mul ⟨Units.map (X.left.presheaf.germ (M.U i ⊓ M.U j) x ⟨hi, hj⟩).hom (M.g i j),
      X.left.presheaf.germ_stalkSpecializes_apply _ _ _⟩ h
  have hκR : ∀ b : R, κ (algebraMap R K b) = X.left.presheaf.germ ⊤ (genericPoint X.left) trivial (constFn X.hom ⊤ b) := fun b => hb.1 (by
    rw [hκ, ← app_constFn H.w, ← φ.appLE_eq_app]
    exact (ffMap_germ φ hφ ⊤ ⊤ le_top _).symm)
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_const_mul_unitAt_codimOne_of_factorialBase R K X.left X.hom κ hκR M.ι M.U r (LB.mem_of_cover hM) (fun i x hx => hr0 i x hx) htr (fun x hx => by
    obtain ⟨y, rfl⟩ := lift x hx
    obtain ⟨i, hi⟩ := LB.mem_of_cover hM (φ y)
    have : Nonempty (M.U i) := ⟨⟨_, hi⟩⟩
    have := hne' i
    exact ⟨i, hi, unitAt_of_isUnit φ hφ (Units.isUnit _) ((DvrModel.pull_U M φ _).ge hi) (hr i)⟩)
  have hu : ∀ i, ∃ v : Γ(X.left, M.U i)ˣ, ∀ [Nonempty (M.U i)],
      X.left.germToFunctionField (M.U i) v.val = κ a * r i := fun i => by
    by_cases h : Nonempty (M.U i)
    · obtain ⟨v, hv⟩ := exists_unit_eq (M.U i) (κ a * r i)
        (mul_ne_zero ((map_ne_zero κ).2 a.ne_zero) (hr0 i _ h.some.2)) (ha i)
      exact ⟨v, @fun _ => hv⟩
    · exact ⟨1, @fun h' => (h h').elim⟩
  choose u hu using hu
  refine ⟨a, ⟨u⟩, fun i j => ?_, fun i Z rr z hz => ?_⟩
  · by_cases h : Nonempty (M.U i ⊓ M.U j : X.left.Opens)
    · obtain ⟨⟨x, hi, hj⟩⟩ := h
      have : Nonempty (M.U i) := ⟨⟨x, hi⟩⟩
      have : Nonempty (M.U j) := ⟨⟨x, hj⟩⟩
      have : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
      refine Units.ext (X.left.germToFunctionField_injective (M.U i ⊓ M.U j) ?_)
      show X.left.germToFunctionField _ (X.left.presheaf.map (homOfLE _).op (u i).val) =
        X.left.germToFunctionField _ ((M.g i j).val * X.left.presheaf.map (homOfLE _).op (u j).val)
      rw [map_mul, germToFunctionField_res, germToFunctionField_res, hu, hu, hg i j x hi hj]
      ring
    · exact unit_ext fun x hx => (h ⟨⟨x, hx⟩⟩).elim
  · have hm : rr z ∈ (M.pull φ).U fun _ => i := mem_pull.2 hz
    have h₂ : ((M.pull φ).U fun _ => i) ≤ φ ⁻¹ᵁ M.U i := fun y hy => mem_pull.1 hy
    have : Nonempty ((M.pull φ).U fun _ => i) := ⟨⟨_, hm⟩⟩
    have : Nonempty (M.U i) := ⟨⟨_, hz⟩⟩
    have hW : (φ.appLE (M.U i) _ h₂).hom (u i).val = constFn p _ (a : K) * (c.s fun _ => i).val := by
      refine Y.germToFunctionField_injective _ ((ffMap_germ φ hφ _ _ h₂ _).symm.trans ?_)
      rw [hu, map_mul, map_mul, hκ, hr]
      refine congrArg₂ (· * ·) ?_ rfl
      exact (germToFunctionField_res (le_top : ((M.pull φ).U fun _ => i) ≤ ⊤) _).symm.trans
        (congrArg _ (res_appLE_apply p _ _ _))
    show (gm (rr ≫ φ) z (M.U i) (u i)).val = _
    rw [← gs_unit (rr ≫ φ) z _ hz, ← gs_unit rr z _ hm, ← GlobalTheory.OpenPartUnit.gs_appLE rr φ z _ _ h₂ hm, hW,
      gs_mul rr z _ hm]
    refine congrArg (· * _) ?_
    exact GlobalTheory.OpenPartUnit.gs_appLE rr p z ⊤ _ _ hm _

end GlobalTheory.GlobalVerticalUnit
end
