module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle012
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.MatrixIrreducibility.IrrOfMatIrr
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem place_under {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {p : ℕ}
    (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 F), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w ∧ (p : 𝓞 F) ∈ w.asIdeal := by
  have hA : ∀ x : 𝓞 F, algebraMap F Ω (x : F) ∈ A := fun x => by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
      ((x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom).tower_top : IsIntegral A (algebraMap F Ω (x : F)))
    exact hy ▸ y.2
  let f : 𝓞 F →+* A := ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A hA
  have hf : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap f := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hm : (p : 𝓞 F) ∈ (IsLocalRing.maximalIdeal A).comap f := (hf _).1 (by simpa only [map_natCast] using hp)
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h => ?_⟩, hf, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hp0 (Nat.cast_eq_zero.1 hm)

private theorem pow_eq_one_of_kills {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    {M : ℕ} (hM : 1 ≤ M) : ∃ k : ℕ, 0 < k ∧ ∀ (C : Type) [Monoid C] (χ : _root_.Formalism.ConjugateSelfDual.G F Ω →* C), KillsMu M χ → ∀ s, χ s ^ k = 1 := by
  let S : SubMulAction (_root_.Formalism.ConjugateSelfDual.G F Ω) Ω :=
    { carrier := {ζ | ζ ^ M = 1}
      smul_mem' := fun s ζ (h : ζ ^ M = 1) => by
        show (s ζ) ^ M = 1
        rw [← map_pow, h, map_one] }
  haveI : Finite S := by
    classical
    refine Set.Finite.subset (s := ((nthRoots M (1 : Ω)).toFinset : Set Ω)) (Finset.finite_toSet _) fun ζ h => ?_
    exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 ((mem_nthRoots hM).2 h))
  refine ⟨Nat.card (Equiv.Perm S), Nat.card_pos, fun C _ χ h s => ?_⟩
  rw [← map_pow]
  refine h _ fun ζ hζ => ?_
  have e : MulAction.toPermHom (_root_.Formalism.ConjugateSelfDual.G F Ω) S (s ^ Nat.card (Equiv.Perm S)) = 1 := by
    rw [map_pow, pow_card_eq_one']
  exact congrArg Subtype.val (DFunLike.congr_fun e ⟨ζ, hζ⟩)

private theorem charpoly_of_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} {r : H →* GL (Fin n) k}
    {κ : Fin n → H →* kˣ} (h : W.HasFlag r κ) (s : H) (b : GL (Fin n) k) :
    ((b * r s * b⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = ∏ i, (X - C ((κ i s : kˣ) : k)) := by
  obtain ⟨a, ha⟩ := h
  have h1 := Matrix.charpoly_of_upperTriangular ((a * r s * a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
    fun i j hij => (ha s).1 i j hij
  simp only [(ha s).2] at h1
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem conj_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (g : GL (Fin n) k) (s : Γ) :
    ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (χ s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]

private theorem flag_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (H : Subgroup Γ)
    (κ : Fin n → ↥H →* kˣ) (g : GL (Fin n) k)
    (hg : ∀ s : ↥H, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) k) i j = 0) ∧
      ∀ i, (g * r s * g⁻¹ : GL (Fin n) k) i i = (κ i s : k)) :
    W.HasFlag ((tw r χ).comp H.subtype) fun i => κ i * χ.comp H.subtype := by
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have := (hg s).1 i j hij
    show ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0
    rw [conj_tw, Matrix.smul_apply]
    exact smul_eq_zero_of_right _ this
  · have := (hg s).2 i
    show ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = _
    rw [conj_tw, Matrix.smul_apply, smul_eq_mul, this]
    exact mul_comm _ _

private theorem pow_fixes (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] {M : ℕ} (hM : 1 ≤ M) :
    ∃ k : ℕ, 0 < k ∧ ∀ (s : _root_.Formalism.ConjugateSelfDual.G F Ω) (ζ : Ω), ζ ^ M = 1 → (s ^ k) ζ = ζ := by
  classical
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine ((Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet).subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots (show 0 < M by omega)] using hζ
  haveI : Finite {ζ : Ω // ζ ^ M = 1} := hfin
  let f : _root_.Formalism.ConjugateSelfDual.G F Ω →* Equiv.Perm {ζ : Ω // ζ ^ M = 1} :=
    { toFun := fun s => Equiv.Perm.subtypePerm (s : Ω ≃ₐ[F] Ω).toEquiv fun x => by
        change s x ^ M = 1 ↔ x ^ M = 1
        rw [← map_pow, map_eq_one_iff _ (s : Ω ≃ₐ[F] Ω).injective]
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨Nat.card (Equiv.Perm {ζ : Ω // ζ ^ M = 1}), Nat.card_pos, fun s ζ hζ => ?_⟩
  have h1 : f (s ^ Nat.card (Equiv.Perm {ζ : Ω // ζ ^ M = 1})) = 1 := by
    rw [map_pow, pow_card_eq_one']
  exact congrArg (fun p : Equiv.Perm {ζ : Ω // ζ ^ M = 1} => (p ⟨ζ, hζ⟩ : Ω)) h1
end

section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

section SlopeTestRemainingChoices

open IsLocalRing UpperTheory.V UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

private theorem int_of_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
  exact ⟨q, hqm, by
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem loc_of_int {O R A : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A]
    [Nontrivial A] [Algebra O A] [Algebra.IsIntegral O A] (f : R →ₐ[O] A) : IsLocalHom f := by
  let g : R →+* f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' g hg
  have hl : IsLocalHom g := IsLocalHom.of_surjective _ hg
  haveI : Algebra.IsIntegral f.range A := Algebra.IsIntegral.tower_top (R := O)
  have h2 : IsLocalHom (algebraMap f.range A) := Algebra.IsIntegral.isLocalHom _ _
  exact ⟨fun x hx => hl.map_nonunit x (h2.map_nonunit (g x) hx)⟩

private theorem norm_le {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f) (x : R) : ‖f x‖ ≤ 1 := by
  obtain ⟨-, -, hl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  have hz : (l : R) ∈ maximalIdeal R := fun h => by
    have h1 : IsUnit (algebraMap c.O R (l : c.O)) := by rwa [map_natCast]
    exact hl (IsLocalHom.map_nonunit _ h1)
  have hp : 0 < ‖((l : ℕ) : PadicAlgCl l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  by_contra hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖((l : ℕ) : PadicAlgCl l)‖⁻¹) (not_le.1 hx)
  have h1 := hf (x ^ n * l) (Ideal.mul_mem_left _ _ hz)
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h1
  have h2 := mul_lt_mul_of_pos_right hn hp
  rw [inv_mul_cancel₀ hp.ne'] at h2
  exact lt_asymm h1 h2

private theorem factor {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    (f : R →ₐ[c.O] PadicAlgCl l) (hf : IsLocPt f) :
    ∃ (A : Subalgebra c.O (PadicAlgCl l)) (h : IsDiscreteValuationRing A) (_ : Module.Finite c.O A) (f' : R →ₐ[c.O] A),
      IsAdicComplete (@maximalIdeal A _ h.toIsLocalRing) A ∧ ∀ x, (f' x : PadicAlgCl l) = f x := by
  haveI := (UpperTheory.V.abelian₂.dvr_finite l c.O).1
  obtain ⟨E, hE⟩ := Loc.ptFin (l := l) R ((TrivSqZeroExt.inlAlgHom c.O _ _).comp f) hf
  have hE' : ∀ a, f a ∈ E.1 := fun a => (hE a).1
  haveI := E.2
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l E.1
  let j : E.1 →ₐ[ℤ_[l]] PadicAlgCl l := E.1.val.restrictScalars ℤ_[l]
  have hj : Function.Injective j := Subtype.val_injective
  let e := (integralClosure ℤ_[l] E.1).equivMapOfInjective j hj
  let B := (integralClosure ℤ_[l] E.1).map j
  have hB : ∀ x, f x ∈ B := fun x =>
    ⟨⟨f x, hE' x⟩, (isIntegral_algHom_iff j hj).1 (int_of_norm _ (norm_le hf x)), rfl⟩
  let A : Subalgebra c.O (PadicAlgCl l) := { B.toSubsemiring with algebraMap_mem' := fun a => f.commutes a ▸ hB _ }
  have d1 : IsDiscreteValuationRing B := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have d2 : Module.Finite ℤ_[l] B := Module.Finite.equiv e.toLinearEquiv
  haveI : Module.Finite ℤ_[l] A := d2
  haveI d3 : IsDiscreteValuationRing A := d1
  exact ⟨A, d3, Module.Finite.of_restrictScalars_finite ℤ_[l] c.O A, f.codRestrict A hB, (UpperTheory.V.abelian₂.dvr_finite l A).1,
    fun _ => rfl⟩

end SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
open UpperTheory.V.Af.Bc
open scoped Pointwise

private theorem move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A (w.under (𝓞 F))) :
    ∃ (B : ValuationSubring Ω) (g : _root_.Formalism.ConjugateSelfDual.G F Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver B w ∧
      (∀ s ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A, g⁻¹ * s * g ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) B) ∧
      (∀ s ∈ _root_.ReciprocityTheory.Gal.Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  obtain ⟨B, hB⟩ := (exists_isPlaceOver Ω w : ∃ B : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver B w)
  have hB' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hm : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hv : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hm, ← hm, map_eq_zero_iff _ g.injective]
  have hD : ∀ s ∈ _root_.ReciprocityTheory.Gal.Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  have hD' : ∀ s ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) (g • B), g⁻¹ * s * g ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) B := fun s hs => by
    have h1 : s • g • B = g • B := hs
    show (g⁻¹ * s * g) • B = B
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  refine ⟨B, g, hB, hD', hD, fun s hs => ⟨hD s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hv]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hm y).2 (((g • B).valuation_le_one_iff _).1 hx)))

private theorem nat_mem_under {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (χ : Γ →* C) (g s : Γ) : χ (g * s * g⁻¹) = χ s := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

private theorem rep_conj {Γ C : Type} [Group Γ] [Group C] (r : Γ →* C) (P : C) (g s : Γ) :
    P * r g * r s * (P * r g)⁻¹ = P * r (g * s * g⁻¹) * P⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group

private theorem flag_move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n M : ℕ} {m : Fin n → ℤ} {r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)}
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A (w.under (𝓞 F)))
    {κ : Fin n → ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A) →* (Qbar l)ˣ} (hκ : FlagAt M m r A κ) :
    ∃ (B : ValuationSubring Ω) (d : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) B) →* ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A)), _root_.Formalism.ConjugateSelfDual.IsPlaceOver B w ∧
      FlagAt M m (r.comp (res F Ω K)) B (fun i => (κ i).comp d) ∧
      (∀ s, cycBar F Ω l (d s) = cycBar K Ω l s) ∧
      (_root_.ReciprocityTheory.Gal.Dec (F := F) B ≤ (res F Ω K).range → Function.Surjective d) := by
  obtain ⟨χ, hχ, ⟨P, hP⟩, hκ⟩ := hκ
  obtain ⟨B, g, hB, hD', hD, hI⟩ := move w hA
  let d : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) B) →* ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A) :=
    (((MulAut.conj g).toMonoidHom.comp (res F Ω K)).comp (_root_.ReciprocityTheory.Gal.Dec (F := K) B).subtype).codRestrict _
      fun s => hD s s.2
  have hd : ∀ s, (d s : _root_.Formalism.ConjugateSelfDual.G F Ω) = g * res F Ω K s * g⁻¹ := fun _ => rfl
  refine ⟨B, d, hB, ⟨fun i => (χ i).comp (res F Ω K), fun i s hs => hχ i _ hs,
    ⟨P * r g, fun s => ?_⟩, fun i s hs => ?_⟩, fun s => ?_, fun H s => ?_⟩
  · rw [MonoidHom.comp_apply, rep_conj]
    exact hP (d s)
  · have h := hκ i (d s) (hI s hs)
    rw [hd, char_conj, char_conj] at h
    exact h
  · rw [hd, char_conj]
    rfl
  · obtain ⟨t, ht⟩ := H (hD' s s.2)
    have htD : t ∈ _root_.ReciprocityTheory.Gal.Dec (F := K) B := by
      have h1 : res F Ω K t • B = B := by
        rw [ht]
        exact hD' s s.2
      exact h1
    refine ⟨⟨t, htD⟩, Subtype.ext ?_⟩
    rw [hd]
    show g * res F Ω K t * g⁻¹ = s
    rw [ht]
    group

end

theorem UpperTheory.V.Th.unlRes :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ) (r : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin n) (Qbar l)), 1 ≤ M → ((∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → _root_.ReciprocityTheory.Gal.Dec (F := ℚ) A ≤ (AlgEquiv.restrictScalarsHom ℚ : _root_.Formalism.ConjugateSelfDual.G K Ω →* _root_.Formalism.ConjugateSelfDual.G ℚ Ω).range) → Unl l M m r → Unl l M m (r.comp (AlgEquiv.restrictScalarsHom ℚ : _root_.Formalism.ConjugateSelfDual.G K Ω →* _root_.Formalism.ConjugateSelfDual.G ℚ Ω))) ∧ ((∀ i j, m i ≠ m j + 1) → Af.Level l M m r → Unl l M m (r.comp (AlgEquiv.restrictScalarsHom ℚ : _root_.Formalism.ConjugateSelfDual.G K Ω →* _root_.Formalism.ConjugateSelfDual.G ℚ Ω))) := by
  intro K Ω _ _ _ _ _ _ _ l _ n M m r hM
  refine ⟨fun hdec H w hw => ?_, fun hm H w hw => ?_⟩
  · obtain ⟨A, hA, κ, hκ, hu⟩ := H (w.under (𝓞 ℚ)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, d, hB, hF, hc, hs⟩ := flag_move w hA hκ
    have hv : B.valuation (l : Ω) < 1 := by
      simpa only [map_natCast] using (hB (l : 𝓞 K)).2 hw
    refine ⟨B, hB, _, hF, fun i j e => hu i j (MonoidHom.ext fun s => ?_)⟩
    obtain ⟨t, rfl⟩ := hs (hdec B hv) s
    have h1 := DFunLike.congr_fun e t
    change κ i (d t) = κ j (d t) * cycBar K Ω l t at h1
    change κ i (d t) = κ j (d t) * cycBar ℚ Ω l (d t)
    rw [hc, h1]
  · obtain ⟨A, hA, κ, hκ⟩ := (Lev.LevelF.of_level H).above (w.under (𝓞 ℚ)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, d, hB, hF, -, -⟩ := flag_move w hA hκ
    exact ⟨B, hB, _, hF, Lev.unlGap K Ω l n M hM m _ w hw B hB _ hF hm⟩
end
