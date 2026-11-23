module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KTypesBoundedFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle031
public import Mathlib.Algebra.Field.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import ReciprocityTheory.Hypotheses.GalCohDefs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.smoothDual_exact :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n), ∀ p ∈ S.BB, ∃ (K : Type) (_ : Field K) (_ : Algebra (ResidueField O) K) (ξ : S.A →+* K), RingHom.ker ξ = p.asIdeal ∧ S.FPt ξ ∧ S.u.triM ≤ RingHom.ker ξ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S p hp
  haveI : IsLocalRing S.R := S.co.toIsLocalRing
  haveI : IsLocalHom (algebraMap O S.R) := S.co.isLocalHom
  obtain ⟨h1, h2⟩ := hp
  let ξ : S.A →+* p.asIdeal.ResidueField := algebraMap S.A p.asIdeal.ResidueField
  have hk : RingHom.ker ξ = p.asIdeal := Ideal.ker_algebraMap_residueField _
  have hz : ∀ c ∈ maximalIdeal O, ξ.comp (algebraMap O S.A) c = 0 := by
    intro c hc
    have hm : algebraMap O S.B c ∈ S.mB := by
      show algebraMap O S.R c ∈ maximalIdeal S.R
      exact map_nonunit (algebraMap O S.R) c hc
    have : algebraMap O S.A c ∈ p.asIdeal := h1 hm
    rw [← hk] at this
    exact this
  let φ : ResidueField O →+* p.asIdeal.ResidueField :=
    Ideal.Quotient.lift (maximalIdeal O) (ξ.comp (algebraMap O S.A)) hz
  refine ⟨p.asIdeal.ResidueField, inferInstance, φ.toAlgebra, ξ, hk, ?_, ?_⟩
  · letI := φ.toAlgebra
    refine ⟨?_, fun c => rfl⟩
    rw [hk]
    exact Ideal.map_le_iff_le_comap.2 h1
  · rcases (types hF hn S _ ξ).2 (by rw [hk]; exact h1) with h | h
    · rw [hk] at h
      exact absurd h h2
    · exact h
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem td_fin {B A D : Type} [CommRing B] [CommRing A] [CommRing D] [Algebra B A] [Algebra A D]
    [Algebra B D] [IsScalarTower B A D] [Algebra.IsIntegral A D] (p : Ideal D) [p.IsPrime] (η : Ideal A)
    (hη : p.comap (algebraMap A D) = η) :
    p.comap (algebraMap B D) = η.comap (algebraMap B A) ∧
    Algebra.trdeg (B ⧸ p.comap (algebraMap B D)) (D ⧸ p) = Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) := by
  subst hη
  rename_i iBD iT iI hp
  have hI : iBD = ((algebraMap A D).comp (algebraMap B A)).toAlgebra := by
    apply Algebra.algebra_ext
    intro r
    exact IsScalarTower.algebraMap_apply B A D r
  subst hI
  refine ⟨(Ideal.comap_comap _ _).symm, ?_⟩
  letI iBD' : Algebra B D := ((algebraMap A D).comp (algebraMap B A)).toAlgebra
  letI : Algebra (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p)) (D ⧸ p) :=
    (Ideal.quotientAlgebra : Algebra (B ⧸ Ideal.comap (algebraMap B D) p) (D ⧸ p))
  haveI : IsScalarTower (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p))
      (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  haveI : FaithfulSMul (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p))
      (A ⧸ Ideal.comap (algebraMap A D) p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  haveI : FaithfulSMul (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  haveI : Nontrivial (D ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  haveI : Nontrivial (A ⧸ Ideal.comap (algebraMap A D) p) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.comap_ne_top _ hp.ne_top)
  haveI : Nontrivial (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p)) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.comap_ne_top _ (Ideal.comap_ne_top _ hp.ne_top))
  haveI : Algebra.IsAlgebraic (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) :=
    Algebra.IsIntegral.isAlgebraic
  have key := trdeg_add_eq (B ⧸ Ideal.comap (algebraMap B A) (Ideal.comap (algebraMap A D) p))
    (A ⧸ Ideal.comap (algebraMap A D) p) (A := D ⧸ p)
  have h0 : Algebra.trdeg (A ⧸ Ideal.comap (algebraMap A D) p) (D ⧸ p) = 0 := trdeg_eq_zero
  rw [h0, add_zero] at key
  exact key.symm

set_option linter.overlappingInstances false in
private theorem dim_gen (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {B A D R : Type} [CommRing B] [Algebra O B] [IsLocalRing B] [CommRing A]
    [CommRing D] [Algebra B A] [Algebra A D] [Algebra.FiniteType B A] [Module.Finite A D] [Module.Flat A D]
    [CommRing R] [IsLocalRing R] [Algebra D R] (hB : UpperTheory.V.CA.IsCL O B) (x : Ideal A) (hx : x.IsMaximal)
    (hxB : x.comap (algebraMap B A) = maximalIdeal B) (y : Ideal D) (hy : y.comap (algebraMap A D) = x)
    (hR : UpperTheory.V.CA.IsCplAt y R) :
    (∀ P : Ideal R, P.IsPrime → ∀ η : Ideal A, (P.comap (algebraMap D R)).comap (algebraMap A D) = η → ∀ t : ℕ,
      Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) ≤ t →
        ringKrullDim (R ⧸ P) ≤ ringKrullDim (B ⧸ η.comap (algebraMap B A)) + t) ∧
    ∀ η : Ideal A, η.IsPrime → η ≤ x → ∀ t : ℕ, Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) = t →
      ∃ P : Ideal R, P.IsPrime ∧ (P.comap (algebraMap D R)).comap (algebraMap A D) = η ∧
        ringKrullDim (R ⧸ P) = ringKrullDim (B ⧸ η.comap (algebraMap B A)) + t := by
  haveI : IsNoetherianRing B := hB.noeth
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing B A
  haveI : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A D
  haveI : IsNoetherianRing R := hR.noeth
  letI : Algebra B D := ((algebraMap A D).comp (algebraMap B A)).toAlgebra
  haveI : IsScalarTower B A D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType B D := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI := hx
  have hyc : Ideal.comap (algebraMap D R) (maximalIdeal R) = y := by
    simpa using hR.comap_pow 1
  haveI hyP : y.IsPrime := by
    rw [← hyc]
    infer_instance
  haveI hyM : y.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) y (by
    change (y.comap (algebraMap A D)).IsMaximal
    rw [hy]
    exact hx)
  have hyB : Ideal.comap (algebraMap B D) y = maximalIdeal B := by
    rw [IsScalarTower.algebraMap_eq B A D, ← Ideal.comap_comap, hy, hxB]
  constructor
  · intro P hP η hη t ht
    haveI := hP
    haveI hpDP : (P.comap (algebraMap D R)).IsPrime := Ideal.comap_isPrime _ _
    have hpDy : P.comap (algebraMap D R) ≤ y := by
      rw [← hyc]
      exact Ideal.comap_mono (le_maximalIdeal hP.ne_top)
    obtain ⟨t', ht'tr, ht'dim⟩ := UpperTheory.V.CA.c3b O y hB hyB (P.comap (algebraMap D R)) hpDy
    have htd := td_fin (B := B) (P.comap (algebraMap D R)) η hη
    have h1 := (UpperTheory.V.CA.c3c y hR).2 (P.comap (algebraMap D R)) P le_rfl
    rw [ht'dim, htd.1] at h1
    rw [htd.2] at ht'tr
    have hc : (t' : Cardinal) ≤ t := ht'tr ▸ ht
    have htt : t' ≤ t := by exact_mod_cast hc
    have hcast : ((t' : ℕ∞) : WithBot ℕ∞) ≤ ((t : ℕ∞) : WithBot ℕ∞) := by
      exact_mod_cast htt
    exact h1.trans (add_le_add le_rfl hcast)
  · intro η hη hηx t ht
    haveI := hη
    haveI : y.LiesOver x := ⟨hy.symm⟩
    haveI : Algebra.HasGoingDown A D := Algebra.HasGoingDown.of_flat (R := A) (S := D)
    obtain ⟨pD, hpDy, hpD, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := η) (q := x) y hηx
    have hηD : pD.comap (algebraMap A D) = η := (Ideal.over_def pD η).symm
    have hmap : Ideal.map (algebraMap D R) pD ≤ maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap, hyc]
      exact hpDy
    obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hmap
    obtain ⟨hqdim, hqc⟩ := UpperTheory.V.CA.c3d O y hB hyB hR pD hpDy q hq
    obtain ⟨t', ht'tr, ht'dim⟩ := UpperTheory.V.CA.c3b O y hB hyB pD hpDy
    have htd := td_fin (B := B) pD η hηD
    refine ⟨q, hq.1.1, by rw [hqc, hηD], ?_⟩
    rw [hqdim, ht'dim, htd.1]
    rw [htd.2, ht] at ht'tr
    have htt : t' = t := by exact_mod_cast ht'tr.symm
    rw [htt]

theorem UpperTheory.V.Fr.loc_dim :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (∀ P : Ideal L.R, P.IsPrime → ∀ t : ℕ, S.td (L.im P) ≤ t → ringKrullDim (L.R ⧸ P) ≤ ringKrullDim (S.B ⧸ L.π P) + t) ∧ ∀ η : Ideal S.A, η.IsPrime → η ≤ x → ∀ t : ℕ, S.td η = t → ∃ P : Ideal L.R, P.IsPrime ∧ L.im P = η ∧ ringKrullDim (L.R ⧸ P) = ringKrullDim (S.B ⧸ S.π η) + t := by
  intro l _ O _ _ _ _ F C₀ n hOk hn S x L
  obtain ⟨hco, hmB⟩ := co_B hOk hn S
  haveI := hco
  haveI : IsLocalRing S.B := hco.toIsLocalRing
  haveI : IsLocalRing L.R := L.co.toIsLocalRing
  haveI : IsAdicComplete (maximalIdeal O) O := UpperTheory.V.Fr.IsCoef.complete (l := l)
  have hB : UpperTheory.V.CA.IsCL O S.B := UpperTheory.V.CA.IsCL.of_isCO O S.B
  obtain ⟨-, -, -, -, hFT, -, -⟩ := gr_A hOk hn S
  haveI := hFT
  obtain ⟨-, hxM, hmx⟩ := loc_flat hOk hn S x L
  have hxB : x.comap (algebraMap S.B S.A) = maximalIdeal S.B := by
    refine le_antisymm (le_maximalIdeal (Ideal.comap_ne_top _ hxM.ne_top)) ?_
    rw [hmB]
    exact hmx
  have hinj : Function.Injective (algebraMap O L.O') := by
    by_cases hK : RingHom.ker (algebraMap O L.O') = ⊥
    · exact (RingHom.injective_iff_ker_eq_bot _).mpr hK
    · exfalso
      have hKm : (RingHom.ker (algebraMap O L.O')).IsMaximal :=
        Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) hK
      have hKeq := IsLocalRing.eq_maximalIdeal hKm
      have hmap : Ideal.map (algebraMap O L.O') (maximalIdeal O) = ⊥ :=
        (Ideal.map_eq_bot_iff_le_ker _).mpr hKeq.ge
      rw [L.unr] at hmap
      exact IsDiscreteValuationRing.not_a_field L.O' hmap
  have htor : Submodule.torsion O L.O' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨⟨r, hr⟩, hrz⟩ := (Submodule.mem_torsion_iff z).mp hz
    rw [Submodule.mem_bot]
    have hr0 : algebraMap O L.O' r ≠ 0 := by
      intro h
      apply nonZeroDivisors.ne_zero hr
      exact hinj (by rw [h, map_zero])
    change r • z = 0 at hrz
    rw [Algebra.smul_def] at hrz
    exact (mul_eq_zero.mp hrz).resolve_left hr0
  haveI : Module.Flat O L.O' := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr htor
  letI : Algebra S.A (TensorProduct O L.O' S.A) := Algebra.TensorProduct.rightAlgebra
  let e : (TensorProduct O S.A L.O') ≃ₐ[S.A] (TensorProduct O L.O' S.A) :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv) (fun a => by
      simp [Algebra.TensorProduct.algebraMap_apply]
      rfl)
  haveI : Module.Finite S.A (TensorProduct O L.O' S.A) := Module.Finite.equiv e.toLinearEquiv
  haveI : Module.Flat S.A (TensorProduct O L.O' S.A) := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  let ι' : TensorProduct O L.O' S.A →ₐ[L.O'] L.R :=
    Algebra.TensorProduct.lift (Algebra.ofId L.O' L.R) L.ι (fun _ _ => Commute.all _ _)
  have hι' : ∀ a : S.A, ι' (TensorProduct.tmul O (1 : L.O') a) = L.ι a := by
    intro a
    simp [ι']
  have hR := loc_cpl hOk hn S x L ι' hι'
  letI : Algebra (TensorProduct O L.O' S.A) L.R := ι'.toRingHom.toAlgebra
  have hcm : ∀ Q : Ideal L.R, (Q.comap (algebraMap (TensorProduct O L.O' S.A) L.R)).comap
      (algebraMap S.A (TensorProduct O L.O' S.A)) = L.im Q := by
    intro Q
    ext a
    change ι' (TensorProduct.tmul O (1 : L.O') a) ∈ Q ↔ L.ι a ∈ Q
    rw [hι']
  have hy : (Ideal.comap ι'.toRingHom (maximalIdeal L.R)).comap (algebraMap S.A (TensorProduct O L.O' S.A)) = x := by
    exact (hcm (maximalIdeal L.R)).trans L.lies
  have key := dim_gen O hB x hxM hxB _ hy hR
  constructor
  · intro P hP t ht
    exact key.1 P hP (L.im P) (hcm P) t ht
  · intro η hη hηx t ht
    obtain ⟨P, hP, hPη, hdim⟩ := key.2 η hη hηx t ht
    refine ⟨P, hP, ?_, hdim⟩
    rw [← hcm P]
    exact hPη
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_res :
    ∀ (Γ k : Type) [Group Γ] [Field k] (κ : Γ →* kˣ) (U : Subgroup Γ), commutator Γ ≤ U → (∃ u ∈ U, κ u ≠ 1) → ∀ y : Γ → k, (∀ s t, y (s * t) = y s + κ s * y t) → (∃ b, ∀ s ∈ U, y s = κ s * b - b) → ∃ b, ∀ s, y s = κ s * b - b := by
  intro Γ k _ _ κ U hU hu y hy hb
  obtain ⟨u, huU, hu1⟩ := hu
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, fun s => ?_⟩
  have hc : s * u * s⁻¹ * u⁻¹ ∈ U := by
    apply hU
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top s) (Subgroup.mem_top u)
    rw [commutatorElement_def] at this
    exact this
  have hv : s * u * s⁻¹ ∈ U := by
    have := U.mul_mem hc huU
    simpa using this
  have hκ : κ (s * u * s⁻¹) = κ u := by
    rw [map_mul, map_mul, map_inv, mul_comm (κ s) (κ u), mul_inv_cancel_right]
  have h1 := hy s u
  have h2 := hy (s * u * s⁻¹) s
  rw [inv_mul_cancel_right, hb _ hv, hκ] at h2
  rw [hb u huU] at h1
  have hne : ((κ u : k) - 1) ≠ 0 := by
    intro h
    apply hu1
    ext
    simpa using sub_eq_zero.mp h
  apply mul_left_cancel₀ hne
  linear_combination h1 - h2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_dual :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [Module (ZMod (l ^ 1)) k] (Γ : Type) [Group Γ] (μ : Γ →* (ZMod (l ^ 1))ˣ) (ρ : Representation (ZMod (l ^ 1)) Γ k) (g : Γ) (c : k), (∀ m, ρ g m = c * m) → c ≠ ZMod.castHom (dvd_pow_self l one_ne_zero) k (μ g) → H0 (twDual μ ρ) = ⊥ := by
  intro l _ k _ _ _ Γ _ μ ρ g c hc hne
  set a : k := ZMod.castHom (dvd_pow_self l one_ne_zero) k (μ g) with ha
  rw [eq_bot_iff]
  intro φ hφ
  rw [Submodule.mem_bot]
  have h : twDual μ ρ g φ = φ := hφ g
  have hne' : c - a ≠ 0 := sub_ne_zero.mpr hne
  have hsmul : ∀ m : k, a * m = ((μ g : ZMod (l ^ 1))) • m := by
    intro m
    rw [ha, ZMod.castHom_apply, ZMod.cast_eq_val, ← nsmul_eq_mul,
      ← Nat.cast_smul_eq_nsmul (ZMod (l ^ 1)), ZMod.natCast_zmod_val]
  have hinv : ∀ m : k, ρ g⁻¹ (ρ g m) = m := by
    intro m
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let ψ : k →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1) := φ
  have key : ∀ m : k, ψ ((c - a) * m) = 0 := by
    intro m
    have h1 : (twDual μ ρ g φ) (ρ g m) = φ (ρ g m) := by rw [h]
    rw [twDual_apply, hinv, hc] at h1
    change (μ g : ZMod (l ^ 1)) * ψ m = ψ (c * m) at h1
    rw [sub_mul, map_sub, hsmul, map_smul, ← h1, smul_eq_mul, sub_self]
  apply LinearMap.ext
  intro x
  have hx : x = (c - a) * ((c - a)⁻¹ * x) := by
    rw [← mul_assoc, mul_inv_cancel₀ hne', one_mul]
  change ψ x = 0
  rw [hx, key]
end
