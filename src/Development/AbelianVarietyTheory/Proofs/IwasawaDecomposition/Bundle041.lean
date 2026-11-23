module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle031
import Mathlib.Algebra.AffineMonoid.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.RingTheory.Discriminant
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory.QFNN

theorem integralClosure_of_fractions (P A : Type) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [CharZero P] [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Algebra P A] [Algebra.EssFiniteType P A]
    (hinj : Function.Injective (algebraMap P A))
    (hloc : ∀ a : A, ∃ b t : A, IsIntegral P b ∧ IsIntegral P t ∧ IsUnit t ∧ a * t = b) :
    Module.Finite P (integralClosure P A) ∧ IsIntegrallyClosed (integralClosure P A) ∧
      Function.Injective (algebraMap P (integralClosure P A)) ∧
      IsLocalization.AtPrime A
        ((maximalIdeal A).comap (algebraMap (integralClosure P A) A)) := by
  let K := FractionRing A
  let F := FractionRing P
  let B := integralClosure P A
  have hιinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hPK : Function.Injective (algebraMap P K) := by
    rw [IsScalarTower.algebraMap_eq P A K]
    exact hιinj.comp hinj
  haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr hPK
  letI : Algebra F K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P F K := FractionRing.isScalarTower_liftAlgebra P K

  have halgA : ∀ a : A, IsAlgebraic P (algebraMap A K a) := by
    intro a
    obtain ⟨b, t, hb, ht, hu, hab⟩ := hloc a
    have ht0 : algebraMap A K t ≠ 0 := by
      simpa using (map_ne_zero_iff _ hιinj).mpr hu.ne_zero
    have : algebraMap A K a = algebraMap A K b * (algebraMap A K t)⁻¹ := by
      rw [← hab, map_mul, mul_assoc, mul_inv_cancel₀ ht0, mul_one]
    rw [this]
    exact (hb.algebraMap (B := K)).isAlgebraic.mul (ht.algebraMap (B := K)).isAlgebraic.inv
  haveI hPKalg : Algebra.IsAlgebraic P K := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, s, _, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    rw [div_eq_mul_inv]
    exact (halgA a).mul (halgA s).inv
  haveI : Algebra.IsAlgebraic F K := (IsFractionRing.comap_isAlgebraic_iff (A := P) (K := F)).mp hPKalg
  haveI : Algebra.EssFiniteType A K := .of_isLocalization K (nonZeroDivisors A)
  haveI : Algebra.EssFiniteType P K := .comp P A K
  haveI : Algebra.EssFiniteType F K := .of_comp P F K
  haveI : FiniteDimensional F K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective P F)
  haveI hic : IsIntegralClosure B P K :=
    { algebraMap_injective := hιinj.comp Subtype.val_injective
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := A))
          have ha : IsIntegral P a := (isIntegral_algebraMap_iff (A := A) (B := K)).mp hx
          exact ⟨⟨a, ha⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact (y.2.algebraMap (B := K)) }
  haveI hfrac : IsFractionRing B K := IsIntegralClosure.isFractionRing_of_finite_extension P F K B
  refine ⟨IsIntegralClosure.finite P F K B, ?_, ?_, ?_⟩
  · refine (isIntegrallyClosed_iff K).mpr ?_
    intro x hx
    have hxP : IsIntegral P x := isIntegral_trans x hx
    exact (IsIntegralClosure.isIntegral_iff (A := B)).mp hxP
  · intro x y h
    exact hinj (congrArg Subtype.val h)
  · have hne : ∀ b : B, b ∈ ((maximalIdeal A).comap (algebraMap B A)).primeCompl →
        IsUnit (algebraMap B A b) := by
      intro b hb
      by_contra hu
      exact hb ((mem_maximalIdeal _).mpr hu)
    refine ⟨fun y => hne y.1 y.2, fun a => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · obtain ⟨b, t, hb, ht, hu, hab⟩ := hloc a
      refine ⟨(⟨b, hb⟩, ⟨⟨t, ht⟩, ?_⟩), hab⟩
      intro hmem
      exact (mem_maximalIdeal _).mp hmem hu
    · have : x = y := Subtype.val_injective h
      rw [this]

end GlobalTheory.QFNN

theorem GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], ∃ (r : ℕ) (B : Type) (_ : CommRing B) (_ : IsDomain B)
      (_ : IsIntegrallyClosed B) (_ : Algebra (MvPolynomial (Fin r) ℤ) B)
      (_ : Module.Finite (MvPolynomial (Fin r) ℤ) B) (_ : Algebra B A) (𝔫 : Ideal B) (_ : 𝔫.IsPrime),
      Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) B) ∧ IsLocalization.AtPrime A 𝔫 := by
  intro A _ _ _ _ _ hess
  obtain ⟨S₀, M, hft, hlocM⟩ := (Algebra.essFiniteType_iff_exists_subalgebra ℤ A).mp hess
  let 𝔮 : Ideal S₀ := (maximalIdeal A).comap (algebraMap S₀ A)
  haveI h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  have hunit : ∀ s : S₀, s ∉ 𝔮 → IsUnit (algebraMap S₀ A s) := by
    intro s hs
    by_contra hu
    exact hs ((mem_maximalIdeal _).mpr hu)
  have hM : M ≤ 𝔮.primeCompl := by
    intro m hm hmem
    exact (mem_maximalIdeal _).mp hmem (IsLocalization.map_units A ⟨m, hm⟩)
  haveI hat : IsLocalization 𝔮.primeCompl A :=
    IsLocalization.of_le M _ hM (fun s hs => hunit s hs)
  haveI : CharZero S₀ := (algebraMap S₀ A).charZero
  obtain ⟨r, y, hy, hqf⟩ := GlobalTheory.T.exists_quasi_finite_polynomial_map S₀ 𝔮
  let P := MvPolynomial (Fin r) ℤ
  letI algPS : Algebra P S₀ := (MvPolynomial.aeval y : P →ₐ[ℤ] S₀).toRingHom.toAlgebra
  letI algPA : Algebra P A := ((algebraMap S₀ A).comp (algebraMap P S₀)).toAlgebra
  haveI : IsScalarTower P S₀ A := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℤ P S₀ := .of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsScalarTower ℤ P A := .of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : Algebra.FiniteType P S₀ := .of_restrictScalars_finiteType ℤ P S₀
  haveI : Algebra.EssFiniteType P A := .of_comp ℤ P A
  have hinj : Function.Injective (algebraMap P A) :=
    (Subtype.val_injective : Function.Injective (algebraMap S₀ A)).comp
      ((algebraicIndependent_iff_injective_aeval).mp hy)
  have hzmp : Algebra.ZariskisMainProperty P 𝔮 := Algebra.ZariskisMainProperty.of_finiteType 𝔮
  obtain ⟨ρ, hρq, hρ, H⟩ := Algebra.zariskisMainProperty_iff.mp hzmp
  have hloc : ∀ a : A, ∃ b t : A, IsIntegral P b ∧ IsIntegral P t ∧ IsUnit t ∧ a * t = b := by
    intro a
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj 𝔮.primeCompl a
    obtain ⟨m₁, h₁⟩ := H x
    obtain ⟨m₂, h₂⟩ := H s
    have hb : IsIntegral P (ρ ^ (m₁ + m₂) * x) := by
      have : ρ ^ (m₁ + m₂) * x = ρ ^ m₂ * (ρ ^ m₁ * x) := by ring
      rw [this]
      exact (hρ.pow _).mul h₁
    have ht : IsIntegral P (ρ ^ (m₁ + m₂) * (s : S₀)) := by
      have : ρ ^ (m₁ + m₂) * (s : S₀) = ρ ^ m₁ * (ρ ^ m₂ * (s : S₀)) := by ring
      rw [this]
      exact (hρ.pow _).mul h₂
    refine ⟨_, _, hb.algebraMap (B := A), ht.algebraMap (B := A), hunit _ ?_, ?_⟩
    · exact h𝔮.mul_notMem (fun h => hρq (h𝔮.mem_of_pow_mem _ h)) s.2
    · simp only [map_mul, map_pow]
      rw [← hxs]
      ring
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.QFNN.integralClosure_of_fractions P A hinj hloc
  exact ⟨r, integralClosure P A, inferInstance, inferInstance, h2, inferInstance, h1, inferInstance,
    _, Ideal.comap_isPrime _ _, h3, h4⟩
end

section

open TensorProduct Polynomial

namespace GlobalTheory.DiscConductor

theorem isIntegral_trace_of_isIntegral
    (U L Ω : Type) [CommRing U] [Field L] [CommRing Ω] [Algebra U L] [Algebra L Ω] [Algebra U Ω]
    [IsScalarTower U L Ω] [Module.Finite L Ω] (ω : Ω) (h : IsIntegral U ω) :
    IsIntegral U (Algebra.trace L Ω ω) := by
  classical
  let b := Module.finBasis L Ω
  let A := AlgebraicClosure L
  let f : Ω →ₐ[U] Matrix (Fin (Module.finrank L Ω)) (Fin (Module.finrank L Ω)) A :=
    (((Algebra.ofId L A).mapMatrix).comp (Algebra.leftMulMatrix b)).restrictScalars U
  have hM : IsIntegral U (f ω) := h.map f
  have htr : algebraMap L A (Algebra.trace L Ω ω) = (f ω).trace := by
    rw [Algebra.trace_eq_matrix_trace b]

    simp only [Matrix.trace, Matrix.diag, map_sum]
    rfl
  rw [← isIntegral_algebraMap_iff (A := L) (B := A) , htr,
    Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : IsRoot (f ω).charpoly μ := (mem_roots'.1 hμ).2
  have hspec : μ ∈ spectrum A (f ω) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  obtain ⟨p, hp, hp0⟩ := hM
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (f ω) (p.map (algebraMap U A)) ⟨μ, hspec, rfl⟩
  have h2 : aeval (f ω) (p.map (algebraMap U A)) = 0 := by
    rw [aeval_map_algebraMap]; simpa [aeval_def] using hp0
  have : Nontrivial (Matrix (Fin (Module.finrank L Ω)) (Fin (Module.finrank L Ω)) A) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [spectrum.of_subsingleton] at hspec
    exact hspec
  rw [h2, spectrum.zero_eq, Set.mem_singleton_iff] at h1
  simpa [eval_map] using h1

theorem det_smul_eq_sum
    (U L Ω ι : Type) [CommRing U] [Field L] [CommRing Ω] [Algebra U L] [Algebra L Ω]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι L Ω) (ω : Ω)
    (hG : ∀ i j, ∃ u : U, algebraMap U L u = Algebra.trace L Ω (b i * b j))
    (hω : ∀ i, ∃ u : U, algebraMap U L u = Algebra.trace L Ω (ω * b i)) :
    ∃ v : ι → U, (Algebra.traceMatrix L b).det • ω = ∑ j, algebraMap U L (v j) • b j := by
  choose g hg using hG
  choose w hw using hω
  have hG : (algebraMap U L).mapMatrix (Matrix.of g) = Algebra.traceMatrix L b := by
    ext i j
    simp [hg, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have h1 : (Algebra.traceMatrix L b).mulVec (b.equivFun ω) = fun i => algebraMap U L (w i) := by
    rw [Algebra.traceMatrix_of_basis_mulVec]
    ext i
    rw [hw]
  have h2 : (Algebra.traceMatrix L b).det • b.equivFun ω =
      fun j => algebraMap U L ((Matrix.of g).adjugate.mulVec w j) := by
    have h3 := congrArg ((Algebra.traceMatrix L b).adjugate.mulVec) h1
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h3
    rw [h3, ← hG, ← RingHom.map_adjugate]
    ext j
    simp [Matrix.mulVec, dotProduct]
  refine ⟨(Matrix.of g).adjugate.mulVec w, ?_⟩
  conv_lhs => rw [← b.sum_equivFun ω, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, ← congrFun h2 j]
  rfl

theorem exists_conductor_of_fractionFields
    (T U C F K L : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CharZero T]
    [CommRing U] [IsDomain U] [IsIntegrallyClosed U]
    [CommRing C] [IsDomain C] [Field F] [Field K] [Field L]
    [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F]
    [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L]
    [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K]
    [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L]
    [Module.Flat T U] [Module.Finite T C] :
    ∃ d : T, d ≠ 0 ∧ ∀ c : FractionRing (U ⊗[T] C), IsIntegral (U ⊗[T] C) c →
      ∃ s : (U ⊗[T] C), algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) s =
        algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) (algebraMap T (U ⊗[T] C) d) * c := by
  classical
  obtain ⟨n, b, hbC, hbT⟩ := GlobalTheory.T.exists_basis_of_integral_with_trace_in_base T C F K
  obtain ⟨φ, hφi, hφ⟩ := GlobalTheory.T.exists_injective_tensor_into_tensor_fractionFields T U C F K L
  have hφu := GlobalTheory.T.isUnit_map_of_mem_nonZeroDivisors_tensor' T U C F K L φ hφi hφ
  choose t ht using hbT
  choose e he using hbC
  let Gt : Matrix (Fin n) (Fin n) T := Matrix.of t
  have hG : (algebraMap T F).mapMatrix Gt = Algebra.traceMatrix F b := by
    ext i j
    simp [Gt, ht, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  haveI : FiniteDimensional F K := Module.Finite.of_basis b
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective T F)
  have hd : algebraMap T F Gt.det = (Algebra.traceMatrix F b).det := by
    rw [RingHom.map_det, hG]
  refine ⟨Gt.det, ?_, ?_⟩
  · intro h0
    apply Algebra.discr_not_zero_of_basis F b
    rw [Algebra.discr_def, ← hd, h0, map_zero]
  intro c hc
  let B : Module.Basis (Fin n) L (L ⊗[F] K) := b.baseChange L
  have hB : ∀ i, B i = 1 ⊗ₜ b i := fun i => Module.Basis.baseChange_apply L b i
  haveI : Module.Finite L (L ⊗[F] K) := Module.Finite.of_basis B
  have htr : ∀ x : K, Algebra.trace L (L ⊗[F] K) (1 ⊗ₜ x) = algebraMap F L (Algebra.trace F K x) := by
    intro x
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
      LinearMap.trace_baseChange]
  have htow : ∀ x : T, algebraMap F L (algebraMap T F x) = algebraMap U L (algebraMap T U x) := by
    intro x
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hBB : ∀ i j, algebraMap U L (algebraMap T U (t i j)) =
      Algebra.trace L (L ⊗[F] K) (B i * B j) := by
    intro i j
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, one_mul, htr, ← ht, htow]
  let ψ : FractionRing (U ⊗[T] C) →+* L ⊗[F] K :=
    IsLocalization.lift (M := nonZeroDivisors (U ⊗[T] C)) (g := φ) (fun s => hφu s.1 s.2)
  have hψ : ∀ s, ψ (algebraMap (U ⊗[T] C) _ s) = φ s := fun s => IsLocalization.lift_eq _ s
  have hψi : Function.Injective ψ := by
    refine (RingHom.injective_iff_ker_eq_bot ψ).2 ((RingHom.ker_eq_bot_iff_eq_zero ψ).2 ?_)
    intro x hx
    obtain ⟨⟨s, r⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (U ⊗[T] C)) x
    have h1 := congrArg ψ h
    rw [map_mul, hx, zero_mul, hψ] at h1
    have h2 : s = 0 := hφi (by rw [map_zero]; exact h1.symm)
    rw [h2, map_zero] at h
    exact (IsLocalization.map_units (FractionRing (U ⊗[T] C)) r).mul_left_eq_zero.1 h
  have hω : IsIntegral U (ψ c) := by
    obtain ⟨p, hp, hpc⟩ := hc
    refine GlobalTheory.T.isIntegral_of_monic_eval_tmul_map_eq_zero T U C F K L φ hφ (ψ c) p hp ?_
    have h1 := congrArg ψ hpc
    rw [hom_eval₂, map_zero] at h1
    have h2 : ψ.comp (algebraMap (U ⊗[T] C) _) = φ := RingHom.ext hψ
    rwa [h2] at h1
  have hBi : ∀ i, IsIntegral U (B i) := by
    intro i
    refine GlobalTheory.T.isIntegral_of_monic_eval_tmul_map_eq_zero T U C F K L φ hφ (B i) (X - Polynomial.C (1 ⊗ₜ e i))
      (monic_X_sub_C _) ?_
    rw [eval₂_sub, eval₂_X, eval₂_C, hφ, map_one, he, hB, sub_self]
  obtain ⟨v, hv⟩ := det_smul_eq_sum U L (L ⊗[F] K) (Fin n) B (ψ c)
    (fun i j => ⟨_, hBB i j⟩) (fun i => IsIntegrallyClosed.isIntegral_iff.1
      (isIntegral_trace_of_isIntegral U L (L ⊗[F] K) _ (hω.mul (hBi i))))
  have hdet : (Algebra.traceMatrix L B).det = algebraMap U L (algebraMap T U Gt.det) := by
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp [Gt, hBB, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  refine ⟨∑ j, v j ⊗ₜ e j, hψi ?_⟩

  rw [map_mul, hψ, hψ, map_sum, Algebra.TensorProduct.algebraMap_apply, hφ, map_one, ← hdet]
  have h1 : ((Algebra.traceMatrix L B).det ⊗ₜ[F] (1 : K)) * ψ c =
      (Algebra.traceMatrix L B).det • ψ c := by
    rw [Algebra.smul_def]; rfl
  rw [h1, hv]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hφ, he, hB, smul_tmul', smul_eq_mul, mul_one]


attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
theorem discr_mul_mem_of_isIntegral : ∀ (T U C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CharZero T] [CommRing U] [IsDomain U] [IsIntegrallyClosed U] [Algebra T U] [Module.Flat T U] [CommRing C] [IsDomain C] [Algebra T C] [Module.Finite T C], Function.Injective (algebraMap T U) → Function.Injective (algebraMap T C) → ∃ d : T, d ≠ 0 ∧ ∀ c : FractionRing (U ⊗[T] C), IsIntegral (U ⊗[T] C) c → ∃ s : (U ⊗[T] C), algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) s = algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) (algebraMap T (U ⊗[T] C) d) * c := by
  intro T U C _ _ _ _ _ _ _ _ _ _ _ _ _ hU hC
  haveI : FaithfulSMul T U := (faithfulSMul_iff_algebraMap_injective _ _).2 hU
  haveI : FaithfulSMul T C := (faithfulSMul_iff_algebraMap_injective _ _).2 hC
  exact exists_conductor_of_fractionFields T U C (FractionRing T) (FractionRing C) (FractionRing U)

end GlobalTheory.DiscConductor
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory

theorem fromSpec_appLE_self_top {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (e : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W) :
    hW.fromSpec.appLE W ⊤ e = (Scheme.ΓSpecIso Γ(Y, W)).inv := by
  rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  rw [show (eqToHom hW.fromSpec_preimage_self).op ≫ (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, Category.comp_id]

theorem appLE_SpecMap_comp_fromSpec_hom {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {S : CommRingCat.{0}}
    (φ : Γ(Y, W) ⟶ S) (h : ⊤ ≤ (Spec.map φ ≫ hW.fromSpec) ⁻¹ᵁ W) :
    (Spec.map φ ≫ hW.fromSpec).appLE W ⊤ h ≫ (Scheme.ΓSpecIso S).hom = φ := by
  have e1 : (⊤ : (Spec Γ(Y, W)).Opens) ≤ hW.fromSpec ⁻¹ᵁ W := by simp
  have e2 : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤ := by simp
  have e3 : (Spec.map φ).appLE ⊤ ⊤ e2 = (Spec.map φ).appTop := (Spec.map φ).appLE_eq_app
  have e4 := Scheme.Hom.appLE_comp_appLE (Spec.map φ) hW.fromSpec W ⊤ ⊤ e1 e2
  rw [← e4, fromSpec_appLE_self_top, e3, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem appLE_SpecMap_comp_fromSpec {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {S : CommRingCat.{0}}
    (φ : Γ(Y, W) ⟶ S) (h : ⊤ ≤ (Spec.map φ ≫ hW.fromSpec) ⁻¹ᵁ W) (c : Γ(Y, W)) :
    (Scheme.ΓSpecIso S).hom.hom (((Spec.map φ ≫ hW.fromSpec).appLE W ⊤ h).hom c) = φ.hom c := by
  rw [← CommRingCat.comp_apply, appLE_SpecMap_comp_fromSpec_hom]

theorem specTensor_to_pullback : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) {R : Type} [CommRing R] (ξ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (W : Y'.affineOpens) (hW : (W : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), letI := (ρ.appLE U W hW).hom.toAlgebra; letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra; ∃ (κ : Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R)) ⟶ pullback ξ ρ) (hκ : ⊤ ≤ (κ ≫ pullback.snd ξ ρ) ⁻¹ᵁ (W : Y'.Opens)), (∀ c : Γ(Y', W), (Scheme.ΓSpecIso _).hom.hom (((κ ≫ pullback.snd ξ ρ).appLE W ⊤ hκ).hom c) = c ⊗ₜ[Γ(X, U)] (1 : R)) ∧ ∀ r : R, (Scheme.ΓSpecIso _).hom.hom (κ.appTop.hom ((pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] r := by
  intro X Y' ρ R _ ξ U hle W hW
  letI := (ρ.appLE U W hW).hom.toAlgebra
  letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
  let incL : Γ(Y', W) →+* Γ(Y', W) ⊗[Γ(X, U)] R := Algebra.TensorProduct.includeLeftRingHom
  let incR : R →ₐ[Γ(X, U)] Γ(Y', W) ⊗[Γ(X, U)] R := Algebra.TensorProduct.includeRight
  have hξ : Spec.map (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫ U.2.fromSpec = ξ := by
    rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec ξ U.2 (isAffineOpen_top _) hle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have hρ : W.2.fromSpec ≫ ρ = Spec.map (ρ.appLE U W hW) ≫ U.2.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec ρ U.2 W.2 hW).symm
  have hring : (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫ CommRingCat.ofHom incR.toRingHom =
      ρ.appLE U W hW ≫ CommRingCat.ofHom incL := by
    ext b
    exact (incR.commutes b).trans ((Algebra.TensorProduct.includeLeft (R := Γ(X, U)) (S := Γ(X, U))
      (A := Γ(Y', W)) (B := R)).commutes b).symm
  have hw : Spec.map (CommRingCat.ofHom incR.toRingHom) ≫ ξ =
      (Spec.map (CommRingCat.ofHom incL) ≫ W.2.fromSpec) ≫ ρ := by
    refine (congrArg (Spec.map (CommRingCat.ofHom incR.toRingHom) ≫ ·) hξ.symm).trans ?_
    rw [Category.assoc, hρ, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hring]
  let κ := pullback.lift _ _ hw
  have hsnd : κ ≫ pullback.snd ξ ρ = Spec.map (CommRingCat.ofHom incL) ≫ W.2.fromSpec := pullback.lift_snd _ _ _
  have hfst : κ ≫ pullback.fst ξ ρ = Spec.map (CommRingCat.ofHom incR.toRingHom) := pullback.lift_fst _ _ _
  have hκ : ⊤ ≤ (κ ≫ pullback.snd ξ ρ) ⁻¹ᵁ (W : Y'.Opens) := by
    rw [hsnd]
    intro x _
    show (Spec.map (CommRingCat.ofHom incL) ≫ W.2.fromSpec) x ∈ (W : Set Y')
    rw [Scheme.Hom.comp_apply, ← W.2.range_fromSpec]
    exact ⟨_, rfl⟩
  refine ⟨κ, hκ, fun c => ?_, fun r => ?_⟩
  · have key : ∀ (f : Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R)) ⟶ Y')
        (_ : f = Spec.map (CommRingCat.ofHom incL) ≫ W.2.fromSpec) (h' : ⊤ ≤ f ⁻¹ᵁ (W : Y'.Opens)),
        (Scheme.ΓSpecIso _).hom.hom ((f.appLE W ⊤ h').hom c) = c ⊗ₜ[Γ(X, U)] (1 : R) := by
      rintro f rfl h'
      exact appLE_SpecMap_comp_fromSpec W.2 (CommRingCat.ofHom incL) h' c
    exact key _ hsnd hκ
  · rw [← CommRingCat.comp_apply (pullback.fst ξ ρ).appTop κ.appTop, ← Scheme.Hom.comp_appTop, hfst,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rfl

end GlobalTheory
end
