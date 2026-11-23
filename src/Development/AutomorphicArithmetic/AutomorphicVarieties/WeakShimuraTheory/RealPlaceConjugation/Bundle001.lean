module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import ReciprocityTheory.Hypotheses.GalCoh
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RamificationInertia.Basic
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Module.ZMod
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem emb_twist {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (i j : Ω →+* ℂ) :
    ∃ g : Ω ≃ₐ[ℚ] Ω, ∀ x, j (g x) = i x := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let jA : Ω →ₐ[ℚ] ℂ := j.toRatAlgHom
  let iA : Ω →ₐ[ℚ] ℂ := i.toRatAlgHom
  let K : IntermediateField ℚ ℂ := jA.fieldRange
  let r : Ω →+* K :=
    { toFun := fun x => ⟨jA x, jA.mem_fieldRange.2 ⟨x, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hr : Function.Bijective r := by
    constructor
    · intro x y hxy
      have : jA x = jA y := congrArg Subtype.val hxy
      exact jA.toRingHom.injective this
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := jA.mem_fieldRange.1 hz
      exact ⟨x, rfl⟩
  haveI : IsAlgClosed K := IsAlgClosed.of_ringEquiv Ω K (RingEquiv.ofBijective r hr)
  have hi : ∀ x, ∃ y, j y = i x := by
    intro x
    have h1 : IsIntegral ℚ (iA x) := (Algebra.IsIntegral.isIntegral x).map iA
    have h2 : IsIntegral K (iA x) := h1.tower_top
    have h3 := minpoly.mem_range_of_degree_eq_one K (iA x)
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible h2))
    obtain ⟨k, hk⟩ := h3
    obtain ⟨y, hy⟩ := jA.mem_fieldRange.1 k.2
    refine ⟨y, ?_⟩
    have : jA y = iA x := by rw [hy]; exact hk
    exact this
  choose φ hφ using hi
  let h0 : Ω →+* Ω :=
    { toFun := φ
      map_one' := j.injective (by rw [hφ, map_one, map_one])
      map_mul' := fun x y => j.injective (by rw [hφ, map_mul, map_mul, hφ, hφ])
      map_zero' := j.injective (by rw [hφ, map_zero, map_zero])
      map_add' := fun x y => j.injective (by rw [hφ, map_add (f := _), map_add (f := _), hφ, hφ]) }
  let hA : Ω →ₐ[ℚ] Ω := h0.toRatAlgHom
  have hb : Function.Bijective hA := Algebra.IsAlgebraic.algHom_bijective hA
  exact ⟨AlgEquiv.ofBijective hA hb, fun x => hφ x⟩

theorem UpperTheory.V.Ws.isConj_of_isComplexConjugation :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (σ τ : G ℚ Ω), IsCC σ → IsCC τ → IsConj σ τ := by
  intro Ω _ _ _ σ τ hσ hτ
  obtain ⟨jσ, hjσ⟩ := hσ
  obtain ⟨jτ, hjτ⟩ := hτ
  obtain ⟨g, hg⟩ := emb_twist jσ jτ
  rw [isConj_iff]
  refine ⟨g, AlgEquiv.ext fun y => jτ.injective ?_⟩
  have e1 : jσ (g⁻¹ y) = jτ y := by
    rw [← hg]
    congr 1
    exact AlgEquiv.apply_symm_apply g y
  show jτ (g (σ (g⁻¹ y))) = jτ (τ y)
  rw [hg, hjσ, e1, hjτ]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem natCard_dual_eq_natCard_of_finite (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [Finite V] :
    Nat.card (Module.Dual K V) = Nat.card V := by
  haveI : Module.Finite K V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := K) (V := Module.Dual K V),
    Module.natCard_eq_pow_finrank (K := K) (V := V), Subspace.dual_finrank_eq]

theorem UpperTheory.V.Ws.local_h1_finite_mod_l :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), IsPlaceOver A v → ContAction ρ → Finite (H1 ρ) ∧ Nat.card (H1 ρ) ≤ Nat.card (H0 ρ) * Nat.card M ^ (1 + if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0) := by
  intro hF hT hE F Ω _ _ _ _ _ l _ M _ _ _ _ _ A v ρ hv hρ
  haveI : Fact (Nat.Prime (l ^ 1)) := ⟨by rw [pow_one]; exact Fact.out⟩
  obtain ⟨_, hf1, _, _⟩ := hF F Ω l 1 M A ρ v one_pos hv hρ
  obtain ⟨⟨e2⟩, _, _, _, hbij⟩ := hT F Ω l 1 M A ρ v one_pos hv hρ
  obtain ⟨hEram, hEun⟩ := hE F Ω l 1 M A ρ v one_pos hv hρ
  obtain ⟨e2'⟩ : Nonempty (H2 ((charRep ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype)).comp
      (MonoidHom.id _)) ≃ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) := by
    rw [MonoidHom.comp_id]
    exact ⟨e2⟩
  haveI hfinD : Finite (Module.Dual (ZMod (l ^ 1)) M) :=
    Finite.of_injective (fun f : Module.Dual (ZMod (l ^ 1)) M => (f : M → ZMod (l ^ 1))) DFunLike.coe_injective
  haveI hfinT : Finite (TDual (ZMod (l ^ 1)) M) := hfinD
  have hH2 : Nat.card (H2 ρ) ≤ Nat.card M := by
    calc Nat.card (H2 ρ) = Nat.card (H2 (ρ.comp (MonoidHom.id _))) := by rw [MonoidHom.comp_id]
      _ = _ := Nat.card_eq_of_bijective _ hbij
      _ = Nat.card (Module.Dual (ZMod (l ^ 1)) ↥(H0 ((twDual ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) ρ).comp
            (MonoidHom.id _)))) := Nat.card_congr (LinearEquiv.congrRight e2').toEquiv
      _ = Nat.card ↥(H0 ((twDual ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) ρ).comp
            (MonoidHom.id _))) := natCard_dual_eq_natCard_of_finite _ _
      _ ≤ Nat.card (TDual (ZMod (l ^ 1)) M) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = Nat.card M := natCard_dual_eq_natCard_of_finite _ _
  refine ⟨hf1, ?_⟩
  by_cases hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  · rw [if_pos hl, hEram hl, pow_add, pow_one (Nat.card M), ← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hH2)
  · rw [if_neg hl, hEun hl, add_zero, pow_one (Nat.card M)]
    exact Nat.mul_le_mul_left _ hH2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem cup_product_injective_comp {R Γ D M : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    [Group Γ] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (φ : D →* Γ)
    (hρ : ContAction (ρ.comp φ)) (χ' : D →* Rˣ) (e : χ' = χ.comp φ)
    (h : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) (hρ.comp' continuous_id))) :
    Function.Injective (cupH1H1TwistedDual χ ρ φ hρ) := by
  subst e
  have e1 : (twDual χ ρ).comp φ = (twDual (χ.comp φ) (ρ.comp φ)).comp (MonoidHom.id D) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun y => LinearMap.ext fun m => ?_
    change ((χ (φ g) : Rˣ) : R) * y (ρ ((φ g)⁻¹) m) =
      ((χ (φ g) : Rˣ) : R) * y (ρ (φ g⁻¹) m)
    rw [map_inv φ g]
  have gen : ∀ (σ σ' : Representation R D (TDual R M)) (_ : σ = σ') h1 h2,
      Function.Injective (cupProductH1H1 σ' (ρ.comp φ) ((charRep χ).comp φ) evalPair.flip
        continuous_of_discreteTopology h2 hρ) →
      Function.Injective (cupProductH1H1 σ (ρ.comp φ) ((charRep χ).comp φ) evalPair.flip
        continuous_of_discreteTopology h1 hρ) := by
    intro σ σ' e h1 h2 h
    subst e
    exact h
  exact gen _ _ e1 _ (fun g y x => evalPair_equiv (χ.comp φ) (ρ.comp φ) g x y) h

theorem UpperTheory.V.Ws.dualSelmer_orthogonalComplement_conditions :
    LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ 1))ˣ) (Av : S → ValuationSubring Ω), μ.comp (toGS Ω _) = cycMod F Ω l 1 → (∀ v, IsPlaceOver (Av v) v.1) → Sel (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) fun _ => ⊤) = Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) := by
  intro hT F Ω _ _ _ _ _ l _ M _ _ _ _ _ S ρ hρ μ Av hμ hA
  have key : ∀ v : S, Function.Injective
      (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))) := fun v => by
    have h := (hT F Ω l 1 M (Av v) (ρ.comp (locFam S Av v)) v.1 one_pos (hA v)
      (hρ.comp' (continuous_locFam S Av v))).2.2.1.1
    exact cup_product_injective_comp μ ρ _ _ _ (by rw [← hμ]; rfl) h
  ext y
  rw [mem_Sel, Sha1, Submodule.mem_iInf]
  refine forall_congr' fun v => ?_
  rw [mem_perpCond, LinearMap.mem_ker]
  constructor
  · intro h
    apply key v
    rw [map_zero]
    exact LinearMap.ext fun x => h x trivial
  · intro h x _
    rw [h, map_zero, LinearMap.zero_apply]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.exists_complexConjugation_at_realPlace :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : InfinitePlace F), w.IsReal → ∃ c : G F Ω, IsCCAt w c := by
  intro F Ω _ _ _ _ _ w hw
  let φ : F →+* ℂ := w.embedding
  have hreal : ∀ x : F, starRingEnd ℂ (φ x) = φ x := by
    intro x
    have h := congrArg (fun ψ : F →+* ℂ => ψ x)
      (NumberField.ComplexEmbedding.isReal_iff.mp (NumberField.InfinitePlace.isReal_iff.mp hw))
    simpa using h
  letI : Algebra F ℂ := φ.toAlgebra
  have halg : ∀ x : F, algebraMap F ℂ x = φ x := fun x => rfl
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  let j : Ω →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let E : IntermediateField F ℂ := j.fieldRange
  let e : Ω ≃ₐ[F] E := AlgEquiv.ofInjectiveField j
  haveI : Normal F E := Normal.of_algEquiv e
  let cj : ℂ →ₐ[F] ℂ :=
    { (starRingEnd ℂ : ℂ →+* ℂ) with
      commutes' := fun x => by
        show starRingEnd ℂ (algebraMap F ℂ x) = algebraMap F ℂ x
        rw [halg]; exact hreal x }
  have hrange : (cj.comp E.val).fieldRange = E := AlgHom.fieldRange_of_normal _
  have hmem : ∀ y : Ω, starRingEnd ℂ (j y) ∈ E := by
    intro y
    have h1 : (cj.comp E.val) (e y) ∈ (cj.comp E.val).fieldRange := AlgHom.mem_fieldRange.mpr ⟨e y, rfl⟩
    rw [hrange] at h1
    have h2 : ((e y : E) : ℂ) = j y := rfl
    simpa [cj, h2] using h1
  let f' : Ω →ₐ[F] E := (cj.comp j).codRestrict E.toSubalgebra (fun y => hmem y)
  let σ0 : Ω →ₐ[F] Ω := e.symm.toAlgHom.comp f'
  have hbij : Function.Bijective σ0 := Algebra.IsAlgebraic.algHom_bijective σ0
  let c : Ω ≃ₐ[F] Ω := AlgEquiv.ofBijective σ0 hbij
  refine ⟨c, (j : Ω →+* ℂ), ?_, ?_⟩
  · intro x
    have h3 : ((e (e.symm (f' x)) : E) : ℂ) = j (e.symm (f' x)) := rfl
    rw [AlgEquiv.apply_symm_apply] at h3
    show j (e.symm (f' x)) = starRingEnd ℂ (j x)
    rw [← h3]
    rfl
  · have h4 : (j : Ω →+* ℂ).comp (algebraMap F Ω) = φ := by
      ext x
      simp [halg]
    rw [h4]
    exact NumberField.InfinitePlace.mk_embedding w
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem addClosed_index (l : ℕ) [Fact l.Prime] (A : AddSubgroup ℤ_[l])
    (hA : IsClosed (A : Set ℤ_[l])) (a : ℤ_[l]) (ha : a ∈ A) (h0 : a ≠ 0) : A.index ≠ 0 := by
  have key : ∀ x : ℤ_[l], a * x ∈ A := by
    intro x
    refine PadicInt.denseRange_intCast.induction_on x ?_ ?_
    · exact hA.preimage (continuous_const.mul continuous_id)
    · intro m
      have hm : a * (m : ℤ_[l]) = m • a := by rw [zsmul_eq_mul, mul_comm]
      rw [hm]
      exact A.zsmul_mem ha m
  have hspec := PadicInt.unitCoeff_spec h0
  set w := PadicInt.unitCoeff h0
  set n := a.valuation
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let f := (PadicInt.toZModPow (p := l) n).toAddMonoidHom
  have hle : f.ker ≤ A := by
    intro x hx
    have hx' : x ∈ RingHom.ker (PadicInt.toZModPow (p := l) n) := hx
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hx'
    obtain ⟨y, rfl⟩ := hx'
    have hw : (w : ℤ_[l]) * ↑w⁻¹ = 1 := Units.mul_inv w
    have heq : (l : ℤ_[l]) ^ n * y = a * (↑w⁻¹ * y) := by
      conv_rhs => rw [hspec]
      linear_combination (-((l : ℤ_[l]) ^ n * y)) * hw
    rw [heq]
    exact key _
  have hfin : f.ker.index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  intro hA0
  apply hfin
  exact Nat.eq_zero_of_zero_dvd (hA0 ▸ AddSubgroup.index_dvd_of_le hle)

open GroundTheory.Global.Cyclotomic in
theorem UpperTheory.V.Ws.index_ne_zero_of_isClosed_of_not_isOfFinOrder :
    ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup ℤ_[l]ˣ), IsClosed (H : Set ℤ_[l]ˣ) → (∃ u ∈ H, ¬ IsOfFinOrder u) → H.index ≠ 0 := by
  intro l _ H hH hu
  obtain ⟨u, huH, hu⟩ := hu
  set L := padicUnitsLog l with hL
  have hB : IsClosed ((H.map L : Subgroup (Multiplicative ℤ_[l])) : Set (Multiplicative ℤ_[l])) := by
    rw [Subgroup.coe_map]
    exact ((hH.isCompact).image (continuous_padicUnitsLog l)).isClosed
  let A : AddSubgroup ℤ_[l] := Subgroup.toAddSubgroup' (H.map L)
  have hAc : IsClosed (A : Set ℤ_[l]) := hB
  have haA : Multiplicative.toAdd (L u) ∈ A := by
    rw [Subgroup.mem_toAddSubgroup']
    exact ⟨u, huH, rfl⟩
  have ha0 : Multiplicative.toAdd (L u) ≠ 0 := by
    intro h
    apply hu
    have h1 : L u = 1 := by
      rw [← ofAdd_toAdd (L u), h]
      rfl
    rw [hL, padicUnitsLog_eq_one_iff] at h1
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨_, torsionExponent_pos l, h1⟩
  have hAi : A.index ≠ 0 := addClosed_index l A hAc _ haA ha0
  have hMi : (H.map L).index ≠ 0 := hAi
  have hK : (H ⊔ L.ker).index ≠ 0 := by
    rw [← Subgroup.comap_map_eq, Subgroup.index_comap_of_surjective _ (padicUnitsLog_surjective l)]
    exact hMi
  have hker : L.ker ≤ rootsOfUnity (torsionExponent l) ℤ_[l] := by
    intro x hx
    rw [mem_rootsOfUnity]
    rw [MonoidHom.mem_ker, hL, padicUnitsLog_eq_one_iff] at hx
    exact hx
  have hcard : Nat.card L.ker ≠ 0 := by
    haveI : NeZero (torsionExponent l) := ⟨(torsionExponent_pos l).ne'⟩
    haveI : Finite L.ker := Finite.of_injective (Subgroup.inclusion hker) (Subgroup.inclusion_injective hker)
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  have hrel : H.relIndex (H ⊔ L.ker) ≠ 0 := by
    rw [sup_comm, Subgroup.relIndex_sup_right]
    intro h0
    apply hcard
    exact Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_card H L.ker)
  rw [← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ L.ker)]
  exact mul_ne_zero hrel hK
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem UpperTheory.V.Ws.exists_zmod_representation (n : ℕ) (Γ : Type) [Group Γ] (R M : Type) [CommRing R]
    [AddCommGroup M] [Module R M] [Module (ZMod n) M] (ρ : Representation R Γ M) :
    ∃ ρ' : Representation (ZMod n) Γ M, ∀ g m, ρ' g m = ρ g m := by
  refine ⟨{ toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap n
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · ext m
    simp
  · intro g h
    ext m
    simp
  · intro g m
    rfl

theorem UpperTheory.V.Ws.exists_zmod_prime_representation_of_torsion :
    ∀ (l : ℕ) (Γ : Type) [Group Γ] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], (∀ m : M, l • m = 0) → ∀ ρ : Representation R Γ M, ∃ (_ : Module (ZMod (l ^ 1)) M) (ρ' : Representation (ZMod (l ^ 1)) Γ M), ∀ g m, ρ' g m = ρ g m := by
  intro l Γ _ R M _ _ _ hl ρ
  letI : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule (fun m => by simpa using hl m)
  obtain ⟨ρ', hρ'⟩ := UpperTheory.V.Ws.exists_zmod_representation (l ^ 1) Γ R M ρ
  exact ⟨this, ρ', hρ'⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.sum_local_degree_above_l_le_finrank :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))), (∑ v ∈ S, if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0) ≤ Module.finrank ℚ F := by
  intro F _ _ l hl S
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  set p : Ideal ℤ := Ideal.span {(l : ℤ)} with hpdef
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hl0).2 (Nat.prime_iff_prime_int.mp hl.out)
  have hpb : p ≠ ⊥ := by
    rw [hpdef, Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  haveI hpm : p.IsMaximal := hpp.isMaximal hpb
  have key := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)
  rw [NumberField.RingOfIntegers.rank] at key
  rw [← key, ← Finset.sum_filter]
  set g : Ideal (𝓞 F) → ℕ := fun I => I.ramificationIdx ℤ * I.inertiaDeg ℤ with hg
  have h1 : ∑ v ∈ S.filter (fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal), locDeg v
      = ∑ I ∈ (S.filter (fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)).image (fun v => v.asIdeal), g I := by
    rw [Finset.sum_image]
    · rfl
    · intro a _ b _ hab
      exact HeightOneSpectrum.ext hab
  have h2 : ∑ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ
      = ∑ I ∈ (Finset.univ : Finset (p.primesOver (𝓞 F))).image Subtype.val, g I := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Subtype.ext hab
  rw [h1, h2]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    simp only [Finset.mem_image, Finset.mem_filter] at hI
    obtain ⟨v, ⟨_, hv⟩, rfl⟩ := hI
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    have hle : p ≤ Ideal.under ℤ v.asIdeal := by
      rw [hpdef, Ideal.span_le, Set.singleton_subset_iff]
      simpa [Ideal.under, Ideal.mem_comap] using hv
    have hne : Ideal.under ℤ v.asIdeal ≠ ⊤ := (Ideal.IsPrime.under ℤ v.asIdeal).ne_top
    have heq : p = Ideal.under ℤ v.asIdeal := hpm.eq_of_le hne hle
    exact ⟨⟨v.asIdeal, ⟨v.isPrime, ⟨heq⟩⟩⟩, rfl⟩
  · intro _ _ _
    exact Nat.zero_le _
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.cocycle_card_euler_formula :
    ∀ (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M), ContAction ρ → Finite (H1 ρ) → Finite (Z1 ρ) ∧ Nat.card (Z1 ρ) * Nat.card (H0 ρ) = Nat.card (H1 ρ) * Nat.card M := by
  intro R Γ M _ _ _ _ _ _ _ _ ρ hρ hH1
  have hB1Z1 : B1 ρ ≤ Z1 ρ := by
    intro f hf
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.1 hf
    rw [mem_Z1_iff_cocycle]
    have hfun : (d0 ρ m) = fun g => ρ g m - m := funext fun g => amitsur_d0_apply ρ m g
    refine ⟨?_, fun g h => ?_⟩
    · rw [hfun]
      exact (hρ.comp (Continuous.prodMk continuous_id continuous_const)).sub continuous_const
    · simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have hker : LinearMap.ker (d0 ρ) = H0 ρ := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro h g
      have := congrFun h g
      rw [amitsur_d0_apply, Pi.zero_apply, sub_eq_zero] at this
      exact this
    · intro h
      funext g
      rw [amitsur_d0_apply, h g, sub_self, Pi.zero_apply]
  have hq : Nat.card (M ⧸ LinearMap.ker (d0 ρ)) = Nat.card (B1 ρ) :=
    Nat.card_congr (d0 ρ).quotKerEquivRange.toEquiv
  have hM := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (d0 ρ))
  rw [hq, hker] at hM
  have hB : Nat.card (Submodule.comap (Z1 ρ).subtype (B1 ρ)) = Nat.card (B1 ρ) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe hB1Z1).toEquiv
  have hZ := Submodule.card_eq_card_quotient_mul_card (Submodule.comap (Z1 ρ).subtype (B1 ρ))
  rw [hB] at hZ
  have hMpos : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hB1pos : Nat.card (B1 ρ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hM
    exact hMpos hM
  have hH1pos : Nat.card (H1 ρ) ≠ 0 := Nat.card_pos.ne'
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [hZ]
    exact mul_ne_zero hB1pos hH1pos
  · rw [hZ, hM]
    change Nat.card (B1 ρ) * Nat.card (H1 ρ) * Nat.card (H0 ρ) =
      Nat.card (H1 ρ) * (Nat.card (H0 ρ) * Nat.card (B1 ρ))
    ring
end
