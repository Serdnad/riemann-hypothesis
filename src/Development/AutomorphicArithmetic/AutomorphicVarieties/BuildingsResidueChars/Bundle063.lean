module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.RamificationInertia.Inertia
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

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem ext_two {Γ H A : Type} [Group Γ] [Group H] [CommGroup A] (i : H →* Γ) (hi : Function.Injective i)
    (δ : H →* A) (c : Γ) (hcc : c * c = 1) (hc : ∀ s, i s ≠ c) (hall : ∀ g, ∃ s, i s = g ∨ i s = g * c)
    (hinv : ∀ s, ∃ t, i t = c * i s * c ∧ δ t = δ s) :
    ∃ δ' : Γ →* A, δ'.comp i = δ ∧ δ' c = 1 := by
  choose p hp using hall
  have huniq : ∀ g s, (i s = g ∨ i s = g * c) → p g = s := by
    intro g s hs
    rcases hp g with h | h <;> rcases hs with h' | h'
    · exact hi (h.trans h'.symm)
    · exact absurd (by rw [map_mul, map_inv, h, h', inv_mul_cancel_left]) (hc ((p g)⁻¹ * s))
    · exact absurd (by rw [map_mul, map_inv, h, h', inv_mul_cancel_left]) (hc (s⁻¹ * p g))
    · exact hi (h.trans h'.symm)
  refine ⟨MonoidHom.mk' (fun g => δ (p g)) fun g g' => ?_, MonoidHom.ext fun s => ?_, ?_⟩
  · rcases hp g with h | h
    · rw [huniq (g * g') (p g * p g') (by
        rw [map_mul, h]
        rcases hp g' with h' | h'
        · exact Or.inl (by rw [h'])
        · exact Or.inr (by rw [h', mul_assoc])), map_mul]
    · obtain ⟨t, ht, hδ⟩ := hinv (p g')
      rw [huniq (g * g') (p g * t) (by
        rw [map_mul, h, ht, mul_assoc g c, mul_assoc c (i _), ← mul_assoc c c, hcc, one_mul]
        rcases hp g' with h' | h'
        · exact Or.inr (by rw [h', mul_assoc])
        · exact Or.inl (by rw [h', mul_assoc g', hcc, mul_one])), map_mul, hδ]
  · change δ (p (i s)) = δ s
    rw [huniq _ s (Or.inl rfl)]
  · change δ (p c) = 1
    rw [huniq c 1 (Or.inr (by rw [map_one, hcc])), map_one]

private theorem conj_on {F M Ω : Type} [Field F] [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra F Ω]
    [Algebra M Ω] {c : _root_.Formalism.ConjugateSelfDual.G F Ω} (hc : IsConjEl c) (x : M) :
    c (algebraMap M Ω x) = algebraMap M Ω (IsCMField.complexConj M x) := by
  obtain ⟨j, hj⟩ := hc
  refine j.injective ?_
  rw [hj]
  exact (IsCMField.complexEmbedding_complexConj M (j.comp (algebraMap M Ω)) x).symm

private theorem conj_comm {K M : Type} [Field K] [Field M] [NumberField M] [IsCMField M] [Algebra K M]
    (σ : M ≃ₐ[K] M) (x : M) : IsCMField.complexConj M (σ x) = σ (IsCMField.complexConj M x) := by
  let φ : M →+* ℂ := Classical.choice inferInstance
  refine φ.injective ?_
  rw [IsCMField.complexEmbedding_complexConj]
  exact (IsCMField.complexEmbedding_complexConj M (φ.comp (σ : M →+* M)) x).symm

private theorem lift_fix {F M Ω : Type} [Field F] [Field M] [Field Ω] [Algebra F M] [Algebra F Ω] [Algebra M Ω]
    [IsScalarTower F M Ω] (g : _root_.Formalism.ConjugateSelfDual.G F Ω) (hg : ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) :
    ∃ s : _root_.Formalism.ConjugateSelfDual.G M Ω, resG F M Ω s = g :=
  ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hg, AlgEquiv.ext fun _ => rfl⟩

private theorem ex_conj (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    ∃ c : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield K) Ω, IsConjEl c := by
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  let φ : K →+* ℂ := Classical.choice inferInstance
  letI : Algebra K ℂ := φ.toAlgebra
  let j : Ω →+* ℂ := (IsAlgClosed.lift (R := K) (S := Ω) (M := ℂ)).toRingHom
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := maximalRealSubfield K) j
    (ComplexEmbedding.conjugate j) (RingHom.ext fun x =>
      ((mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))).symm)
  exact ⟨σ.symm, j, fun x => DFunLike.congr_fun hσ x⟩

theorem UpperTheory.character_extends_to_galois_group :
    UpperTheory.V.Af.Sol.ExtChar := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ l _ δ hδ
  have kill : ∀ t : _root_.Formalism.ConjugateSelfDual.G K Ω, (∀ x : M, t (algebraMap M Ω x) = algebraMap M Ω x) → δ t = 1 := fun t ht => by
    obtain ⟨s, rfl⟩ := lift_fix t ht
    exact DFunLike.congr_fun hδ s
  obtain ⟨c, hc⟩ := ex_conj K Ω
  have hcc : c * c = 1 := by
    obtain ⟨j, hj⟩ := hc
    exact AlgEquiv.ext fun x => j.injective (by
      rw [AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply])
  have hKM : ∀ (g : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield K) Ω), (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) →
      ∃ s : _root_.Formalism.ConjugateSelfDual.G K Ω, resG (maximalRealSubfield K) K Ω s = g ∧ δ s = 1 := fun g hg => by
    obtain ⟨s, rfl⟩ := lift_fix (M := K) g fun x => by
      rw [IsScalarTower.algebraMap_apply K M Ω, hg]
    exact ⟨s, rfl, kill s hg⟩
  obtain ⟨δ', h1, h2⟩ := ext_two (resG (maximalRealSubfield K) K Ω) (AlgEquiv.restrictScalars_injective _) δ c hcc
    (fun s hs => IsCMField.complexConj_ne_one K (AlgEquiv.ext fun x => (algebraMap K Ω).injective (by
      rw [← conj_on hc, ← hs]
      exact s.commutes x)))
    (fun g => by
      have h2 : Nat.card (K ≃ₐ[maximalRealSubfield K] K) = 2 :=
        (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K) ▸
          IsGalois.card_aut_eq_finrank (maximalRealSubfield K) K
      rw [Nat.card_eq_two_iff' 1] at h2
      by_cases hg : g.restrictNormal K = 1
      · obtain ⟨s, hs⟩ := lift_fix (M := K) g fun x => by
          rw [← AlgEquiv.restrictNormal_commutes, hg, AlgEquiv.one_apply]
        exact ⟨s, Or.inl hs⟩
      · have hg' := h2.unique hg (IsCMField.complexConj_ne_one K)
        obtain ⟨s, hs⟩ := lift_fix (M := K) (g * c) fun x => by
          rw [AlgEquiv.mul_apply, conj_on hc, ← AlgEquiv.restrictNormal_commutes, hg',
            IsCMField.complexConj_apply_apply]
        exact ⟨s, Or.inr hs⟩)
    (fun s => by
      obtain ⟨t, ht, hδt⟩ := hKM (c * resG _ K Ω s * c * (resG _ K Ω s)⁻¹) fun x => by
        obtain ⟨y, rfl⟩ := (s.restrictNormal M).surjective x
        change c (s (c (s.symm _))) = _
        rw [AlgEquiv.restrictNormal_commutes, s.symm_apply_apply, conj_on hc, ← AlgEquiv.restrictNormal_commutes,
          conj_on hc, conj_comm, IsCMField.complexConj_apply_apply, AlgEquiv.restrictNormal_commutes]
      exact ⟨t * s, by rw [map_mul, ht, inv_mul_cancel_right], by rw [map_mul, hδt, one_mul]⟩)
  have h3 : ∀ g : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield K) Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → δ' g = 1 :=
    fun g hg => by
      obtain ⟨s, rfl, hs⟩ := hKM g hg
      exact (DFunLike.congr_fun h1 s).trans hs
  refine ⟨δ', h1, fun d hd => ?_, ?_⟩
  · have h4 := h3 (d * c) fun x => by
      rw [AlgEquiv.mul_apply, conj_on hc, conj_on hd, IsCMField.complexConj_apply_apply]
    rwa [map_mul, h2, mul_one] at h4
  · let f : M →ₐ[maximalRealSubfield K] Ω := IsScalarTower.toAlgHom (maximalRealSubfield K) M Ω
    haveI : FiniteDimensional (maximalRealSubfield K) f.fieldRange :=
      (AlgEquiv.ofInjectiveField f).toLinearEquiv.finiteDimensional
    refine Subgroup.isOpen_mono (fun g hg => ?_) (IntermediateField.fixingSubgroup_isOpen f.fieldRange)
    exact h3 g fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ⟨x, rfl⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_auxiliary_galois_extension :
    UpperTheory.V.Af.Sol.ExistsCompositumWithPrimeDegreeGalois := by
  intro M Ω _ _ _ _ _ L _ _ _ hp hlt
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed M
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap M Ω).injective
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  have hαi : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  set P := minpoly ℚ α with hPdef
  have hPdeg : P.natDegree = Module.finrank ℚ L := by
    rw [← IntermediateField.adjoin.finrank hαi, hα, IntermediateField.finrank_top']
  let φ : L →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  set β := φ α with hβdef
  have hβP : minpoly ℚ β = P := minpoly.algHom_eq φ φ.injective α
  set Q : Polynomial M := P.map (algebraMap ℚ M) with hQdef
  have hQ0 : Q ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hαi)
  have hsplit : (Q.map (algebraMap M Ω)).Splits := IsAlgClosed.splits _
  have hSF := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hsep : Q.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ α)
  have hroot : ∀ y : Ω, y ∈ Q.rootSet Ω ↔ y ∈ P.rootSet Ω := by
    intro y
    rw [Polynomial.mem_rootSet, Polynomial.mem_rootSet, hQdef, Polynomial.aeval_map_algebraMap]
    exact and_congr_left fun _ => ⟨fun _ => minpoly.ne_zero hαi, fun _ => hQ0⟩
  have hβroot : β ∈ P.rootSet Ω := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hαi, hβP ▸ minpoly.aeval ℚ β⟩
  have hrange : ∀ x : L, φ x ∈ IntermediateField.adjoin M {β} := by
    intro x
    have h1 : φ x ∈ (⊤ : IntermediateField ℚ L).map φ := ⟨x, trivial, rfl⟩
    rw [← hα, IntermediateField.adjoin_map, Set.image_singleton] at h1
    have h2 : IntermediateField.adjoin ℚ {φ α} ≤ (IntermediateField.adjoin M {β}).restrictScalars ℚ :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self M β)
    exact h2 h1
  have hPs : (P.map (algebraMap ℚ L)).Splits := Normal.splits inferInstance α
  have hroots : ∀ y ∈ P.rootSet Ω, y ∈ Set.range φ := by
    intro y hy
    rw [← hPs.image_rootSet φ] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have heq : IntermediateField.adjoin M (Q.rootSet Ω) = IntermediateField.adjoin M {β} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := hroots y ((hroot y).1 hy)
      exact hrange x
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin M _ ((hroot β).2 hβroot)
  have hgal0 : IsGalois M (IntermediateField.adjoin M (Q.rootSet Ω)) := by
    haveI := hSF
    exact IsGalois.of_separable_splitting_field hsep
  have hgal : IsGalois M (IntermediateField.adjoin M {β}) := heq ▸ hgal0
  have hβQ : IsIntegral ℚ β := hαi.map φ
  have hβM : IsIntegral M β := hβQ.tower_top
  haveI hfdM : FiniteDimensional M (IntermediateField.adjoin M {β}) :=
    IntermediateField.adjoin.finiteDimensional hβM
  haveI hfdQ : FiniteDimensional ℚ (IntermediateField.adjoin M {β}) :=
    Module.Finite.trans M (IntermediateField.adjoin M {β})
  haveI hnf : NumberField (IntermediateField.adjoin M {β}) := {}
  let f : L →+* IntermediateField.adjoin M {β} := (φ : L →+* Ω).codRestrict _ hrange
  have hfin : Module.finrank M (IntermediateField.adjoin M {β}) = (minpoly M β).natDegree :=
    IntermediateField.adjoin.finrank hβM
  have hle : (minpoly M β).natDegree ≤ Module.finrank ℚ L := by
    rw [← hPdeg, ← Polynomial.natDegree_map (algebraMap ℚ M) (p := P)]
    refine Polynomial.natDegree_le_of_dvd ?_ hQ0
    have h4 := minpoly.dvd_map_of_isScalarTower ℚ M β
    rwa [hβP] at h4
  have hx : minpoly ℚ (⟨β, IntermediateField.mem_adjoin_simple_self M β⟩ : IntermediateField.adjoin M {β}) = P := by
    rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ (IntermediateField.adjoin M {β}) Ω)
      (algebraMap (IntermediateField.adjoin M {β}) Ω).injective]
    exact hβP
  have hdvd : Module.finrank ℚ L ∣ Module.finrank ℚ (IntermediateField.adjoin M {β}) := by
    have h5 := minpoly.degree_dvd (Algebra.IsIntegral.isIntegral (R := ℚ)
      (⟨β, IntermediateField.mem_adjoin_simple_self M β⟩ : IntermediateField.adjoin M {β}))
    rwa [hx, hPdeg] at h5
  have hMpos : 0 < Module.finrank ℚ M := Module.finrank_pos
  have hEpos : 0 < Module.finrank M (IntermediateField.adjoin M {β}) := Module.finrank_pos
  have hdeg : Module.finrank M (IntermediateField.adjoin M {β}) = Module.finrank ℚ L := by
    rw [← Module.finrank_mul_finrank ℚ M (IntermediateField.adjoin M {β})] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h3
    · exact absurd h3 (Nat.not_dvd_of_pos_of_lt hMpos hlt)
    · exact le_antisymm (hfin ▸ hle) (Nat.le_of_dvd hEpos h3)
  have htop : Algebra.adjoin M (Set.range f) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hz : (z : Ω) ∈ Algebra.adjoin M {β} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβM.isAlgebraic]
      exact z.2
    have hsub : Algebra.adjoin M {β} ≤
        (Algebra.adjoin M (Set.range f)).map (IntermediateField.adjoin M {β}).val := by
      rw [AlgHom.map_adjoin]
      apply Algebra.adjoin_mono
      rintro _ rfl
      exact ⟨f α, ⟨α, rfl⟩, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hsub hz
    have hwz' : w = z := Subtype.ext hwz
    exact hwz' ▸ hw
  exact ⟨IntermediateField.adjoin M {β}, inferInstance, hnf, inferInstance, inferInstance,
    inferInstance, f, hgal, hdeg, htop⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_polarized_restriction :
    UpperTheory.V.Af.Sol.PolRes := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι n r h
  obtain ⟨F₀, i1, i2, i3, i4, i5, i6, hF, μ, c, P, hμ, hs, hc, hp⟩ := h
  letI : Algebra F₀ M := ((algebraMap K M).comp (algebraMap F₀ K)).toAlgebra
  haveI : IsScalarTower F₀ K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower F₀ M Ω := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply F₀ K Ω,
      IsScalarTower.algebraMap_apply K M Ω]
  refine ⟨F₀, i1, i2, inferInstance, inferInstance, this, i6, hF, μ, c, P, hμ, hs, hc, ?_⟩
  unfold IsPairing at hp ⊢
  intro t t' ht
  have e1 : ∀ u : _root_.Formalism.ConjugateSelfDual.G M Ω,
      AlgEquiv.restrictScalars F₀ (resG K M Ω u) = AlgEquiv.restrictScalars F₀ u := by
    intro u; ext x; rfl
  have e2 : ∀ u : _root_.Formalism.ConjugateSelfDual.G M Ω, resG F₀ M Ω u = resG F₀ K Ω (resG K M Ω u) := by
    intro u; ext x; rfl
  have key := hp (resG K M Ω t) (resG K M Ω t') (by rw [e1, e1]; exact ht)
  simpa [e2] using key
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol
open scoped Matrix

private theorem eig_dual {K : Type} [Field K] (φ : K →+* ℂ) {n : ℕ} (M M' P : GL (Fin n) K) (t : K)
    (hP : (M : Matrix (Fin n) (Fin n) K)ᵀ * (P : Matrix (Fin n) (Fin n) K) * (M' : Matrix (Fin n) (Fin n) K) =
      t • (P : Matrix (Fin n) (Fin n) K)) (S S' : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S.map fun b => X - C b).prod)
    (h' : (M' : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S'.map fun b => X - C b).prod) :
    S = S'.map fun a => φ t * a⁻¹ := by
  have h0 : (M : Matrix (Fin n) (Fin n) K)ᵀ = (P : Matrix (Fin n) (Fin n) K) *
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, ← hP, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have h1 : (M : Matrix (Fin n) (Fin n) K).charpoly =
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).charpoly := by
    rw [← Matrix.charpoly_transpose, h0, Matrix.coe_units_inv P, Matrix.charpoly_units_conj]
  rw [← Matrix.charpoly_map] at h'
  have h3 := GlobalTheory.charpoly_smul_inv_of_charpoly_eq_prod n (Matrix.GeneralLinearGroup.map φ M') (φ t) _ h'
  have h4 : (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map φ =
      φ t • (((Matrix.GeneralLinearGroup.map φ M')⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← map_inv]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [h1, ← Matrix.charpoly_map, h4, h3] at h
  have h5 := congrArg roots h
  rw [roots_multiset_prod_X_sub_C] at h5
  rw [← roots_multiset_prod_X_sub_C (S'.map fun a => φ t * a⁻¹), Multiset.map_map]
  exact h5.symm

private theorem cPl_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    cPl w = preplace (IsCMField.complexConj E).toRingEquiv w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))

private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm

private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : _root_.Formalism.ConjugateSelfDual.G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield F) Ω} (hc : IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)

private theorem frob_dual {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)} {θ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ}
    {c : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield F) Ω} {P : GL (Fin n) (Qbar l)} (hc : IsConjEl c)
    (hP : IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ)) * θ) P) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {B B' : Multiset ℂˣ} {z : ℂˣ} (hB : FrobEig ι r w (algSat n (normV w) B))
    (hB' : FrobEig ι r (cPl w) (algSat n (normV (cPl w)) B')) (hz : CharEig ι θ w z) :
    B'.map (·⁻¹) = B.map (· * z⁻¹) := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have hL := isLift_conj hc
  have hAA : ∀ y, c.symm.toRingEquiv y ∈ A ↔ y ∈ A.comap c.symm.toRingEquiv.toRingHom := fun _ => Iff.rfl
  rw [cPl_eq] at hB'
  have e := (hB' _ (isPlaceOver_preplace hL hAA hA)).2 (conjGal hL σ)
    (by rw [normV_preplace]; exact isFrob_conjGal hL hAA hσ)
  rw [normV_preplace] at e
  have h1 := eig_dual ι.toRingHom (r σ⁻¹) (r (conjGal hL σ)⁻¹) P _
    (hP σ⁻¹ (conjGal hL σ)⁻¹ (by rw [← map_inv]; exact AlgEquiv.ext fun _ => rfl)) _ _ ((hB A hA).2 σ hσ) e
  have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
  have hq0 : normV w ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at h2
    exact Units.ne_zero _ h2
  have hqR : (0 : ℝ) < normV w := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have h3 := (hz A hA).2 σ hσ
  set d : ℂ := ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact_mod_cast (Real.rpow_pos_of_pos hqR _).ne'
  have hdd : d * d = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hd, ← Complex.ofReal_mul, ← Real.rpow_add hqR, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
    push_cast
    rfl
  have h4 : ι.toRingHom (((cycBar F Ω l ^ (1 - (n : ℤ)) * θ) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = d * d * z := by
    change ι _ = _
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, map_mul, map_inv (cycBar F Ω l),
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast, h3, hdd, inv_zpow',
      neg_sub]
  have hS : ∀ B : Multiset ℂˣ, algSat n (normV w) B = B.map fun α : ℂˣ => d * (α : ℂ) := fun B => by
    simp only [algSat, ← hd, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def]
  rw [h4, hS, hS] at h1
  have h5 := congrArg (Multiset.map fun a : ℂ => d⁻¹ * a * (z : ℂ)⁻¹) h1
  simp only [Multiset.map_map, Function.comp_def] at h5
  apply Multiset.map_injective (f := (Units.val : ℂˣ → ℂ)) Units.val_injective
  simp only [Multiset.map_map, Function.comp_def]
  have := z.ne_zero
  refine (Multiset.map_congr rfl fun a _ => ?_).trans (h5.symm.trans (Multiset.map_congr rfl fun a _ => ?_))
  · rw [Units.val_inv_eq_inv_val]
    have := a.ne_zero
    field_simp
  · rw [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp

theorem UpperTheory.frobeniusDuality_complexConj :
    UpperTheory.V.Af.Sol.FrobDualC := by
  intro F Ω _ _ _ _ _ _ l _ ι n r θ c P hc hP w hw B B' z hB hB' hz
  exact frob_dual hc hP hw hB hB' hz
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.galois_character_frobenius_compatibility :
    UpperTheory.V.Af.Sol.CharFrob := by
  intro F Ω _ _ _ _ _ l _ ι χ μ hχ
  obtain ⟨_, art, a, hart, _, hL⟩ := hχ
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (l : 𝓞 F) ∉ v.asIdeal := by
    have hne : Ideal.span {(l : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hne).subset ?_)
    intro v hv
    simp only [Set.mem_setOf_eq, not_not] at hv ⊢
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv
  filter_upwards [GlobalTheory.GalChar.unr_ae χ, hl] with v hu hv
  refine ⟨hu, fun A hA => ⟨(GlobalTheory.HeckeGal.IsLAdicOf.unr_iff hart hL (Or.inl hv) hA).2 hu, fun σ hσ => ?_⟩⟩
  have h := GlobalTheory.HeckeGal.IsLAdicOf.frob_unr hart hL (Or.inl hv) hu hA hσ
  rw [map_inv, Units.val_inv_eq_inv_val, h, inv_inv, RingEquiv.apply_symm_apply]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem exists_not_mem_asIdeal_pow_of_ne_zero (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)) : ∃ f : ℕ, normV w = normV (HeightOneSpectrum.under (𝓞 K) w) ^ f := by
  refine ⟨(w.asIdeal.under (𝓞 K)).inertiaDeg' w.asIdeal, ?_⟩
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.asIdeal.under (𝓞 K)) (Ideal.IsPrime.under _ _) (HeightOneSpectrum.under (𝓞 K) w).ne_bot
  simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

private theorem tendsto_under_cofinite' (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] : Filter.Tendsto (HeightOneSpectrum.under (𝓞 K) : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have hfin := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)
  refine Set.Finite.to_subtype (Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) (hfin.subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h))
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨x.isPrime, ⟨rfl⟩⟩

private theorem algSat_pow_map_pow (n q f : ℕ) (B : Multiset ℂˣ) : algSat n (q ^ f) (Multiset.map (fun x => x ^ f) B) = Multiset.map (fun x => x ^ f) (algSat n q B) := by
  unfold algSat
  simp only [Multiset.bind_map, Multiset.map_map, Function.comp_def, Multiset.bind_singleton, Multiset.pure_def, Multiset.bind_def]
  refine Multiset.map_congr rfl fun b _ => ?_
  rw [mul_pow]
  congr 1
  push_cast
  rw [← Complex.ofReal_pow, Real.rpow_pow_comm (by positivity)]

theorem UpperTheory.satake_base_change_attached :
    UpperTheory.V.Af.Sol.AttBc := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι n r sat sat' huniq hbc hatt hss
  refine ⟨hss, ?_⟩
  have hT := UpperTheory.frobenius_power_compatibility K M Ω l ι
  filter_upwards [hbc, (tendsto_under_cofinite' K M).eventually hatt.2] with w hw hv
  obtain ⟨f, hf⟩ := exists_not_mem_asIdeal_pow_of_ne_zero K M w
  obtain ⟨B, hB, hE⟩ := hv
  obtain ⟨B0, hB0, hB0'⟩ := hw f hf
  obtain rfl := huniq _ _ _ hB hB0
  refine ⟨_, hB0', ?_⟩
  have h2 := (hT w f hf).1 n r _ hE
  rw [hf, algSat_pow_map_pow]
  exact h2
end
