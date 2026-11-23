module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LeNuIffPowMemPrinc
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.EmultiplicityPowSubOneOdd
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle001
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.shaAbsRes :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 F'))) (φ : G F' Ω' →* G F Ω) (hφ : Continuous φ),
      (∀ (v' : HeightOneSpectrum (𝓞 F')) (A' : ValuationSubring Ω'), IsPlaceOver A' v' → ∃ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v ∧ (v ∈ S ↔ v' ∈ S') ∧
        (∀ g ∈ Dec (F := F') A', φ g ∈ Dec (F := F) A) ∧ ∀ g ∈ Ine (F := F') A', φ g ∈ Ine (F := F) A) →
      ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R (G F Ω) M), (∀ x ∈ ShaAbs ρ S, resH1 ρ φ hφ x ∈ ShaAbs (ρ.comp φ) S') ∧
        (Function.Surjective φ → Module.length R (ShaAbs ρ S) ≤ Module.length R (ShaAbs (ρ.comp φ) S')) := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ S S' φ hφ h R _ M _ _ _ _ _ ρ
  have h1 : ∀ x ∈ ShaAbs ρ S, resH1 ρ φ hφ x ∈ ShaAbs (ρ.comp φ) S' := by
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨ha, hb⟩ := (mk_mem_ShaAbs ρ S z).1 hx
    refine (mk_mem_ShaAbs (ρ.comp φ) S' (restrictCocycles1 ρ φ hφ z)).2 ⟨?_, ?_⟩
    · intro v' hv' A' hA'
      obtain ⟨v, A, hA, hS, hD, -⟩ := h v' A' hA'
      obtain ⟨m, hm⟩ := ha v (hS.2 hv') A hA
      exact ⟨m, fun g hg => hm (φ g) (hD g hg)⟩
    · intro v' hv' A' hA'
      obtain ⟨v, A, hA, hS, -, hI⟩ := h v' A' hA'
      obtain ⟨m, hm⟩ := hb v (fun hv => hv' (hS.1 hv)) A hA
      exact ⟨m, fun g hg => hm (φ g) (hI g hg)⟩
  refine ⟨h1, fun hs => ?_⟩
  have hinj : Function.Injective (resH1 ρ φ hφ) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : (Submodule.Quotient.mk (restrictCocycles1 ρ φ hφ z) : H1 (ρ.comp φ)) = 0 := hx
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx')
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩)
    obtain ⟨g', rfl⟩ := hs g
    exact hm g'
  refine Module.length_le_of_injective ((resH1 ρ φ hφ).restrict h1) ?_
  intro x y hxy
  exact Subtype.ext (hinj (congrArg Subtype.val hxy))
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.ineOpen :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω),
    v ∈ Above (F := F) l → IsPlaceOver A v →
    IsOpen (ineImage F l A : Set ℤ_[l]ˣ) ∧ (ineImage F l A).index ≠ 0 ∧
    (ineImage F l A).index ≤ Module.finrank ℚ F := by
  intro F Ω _ _ _ _ _ l _ v A hl hA
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hl' : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := hl
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl'
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have hK : Module.finrank ℚ F = K.fixingSubgroup.index := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finrank_eq
  have hK0 : K.fixingSubgroup.index ≠ 0 := by
    rw [← hK]; exact Module.finrank_pos.ne'
  let I : Subgroup (G ℚ Ω) := Ine (F := ℚ) A
  let f : I →* ℤ_[l]ˣ := (cycZ (F := ℚ) (Ω := Ω) l).comp I.subtype
  have hf : Function.Surjective f := fun u => by
    obtain ⟨σ, hσ, h⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u
    exact ⟨⟨σ, hσ⟩, h⟩
  have hle : (K.fixingSubgroup.subgroupOf I).map f ≤ ineImage F l A := by
    rintro _ ⟨σ, hσ, rfl⟩
    have hmem : σ.1 ∈ K.fixingSubgroup := hσ
    let g : G F Ω := { σ.1.toRingEquiv with
      commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
    exact ⟨g, σ.2, rfl⟩
  have hrel0 : K.fixingSubgroup.relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  have hrel : K.fixingSubgroup.relIndex I ≤ K.fixingSubgroup.index := by
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top hrel0
  have hrelI : K.fixingSubgroup.relIndex I ≠ 0 := fun h =>
    hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h)
  have hdvd : (ineImage F l A).index ∣ K.fixingSubgroup.relIndex I :=
    (Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hf)
  have h0 : (ineImage F l A).index ≠ 0 := ne_zero_of_dvd_ne_zero hrelI hdvd
  refine ⟨?_, h0, ?_⟩
  · have : (ineImage F l A).FiniteIndex := ⟨h0⟩
    refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
    exact ((isClosed_Ine (F := F) A).isCompact.image (continuous_cycZ F Ω l)).isClosed
  · rw [hK]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hrelI) hdvd).trans hrel
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem cyclotomicCharacter_conj_ringEquiv {L M : Type} [Field L] [Field M] (p : ℕ) [Fact p.Prime]
    (φ : L ≃+* M) (g : L ≃+* L) :
    cyclotomicCharacter L p g = cyclotomicCharacter M p (φ.symm.trans (g.trans φ)) := by
  by_cases H : ∀ i : ℕ, ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i)
  · have hL (i : ℕ) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
    have hM (i : ℕ) : HasEnoughRootsOfUnity M (p ^ i) := by
      obtain ⟨ζ, hζ⟩ := H i
      exact ⟨⟨φ ζ, hζ.map_of_injective φ.injective⟩, rootsOfUnity.isCyclic _ _⟩
    ext1
    refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
    rw [cyclotomicCharacter.toZModPow, cyclotomicCharacter.toZModPow]
    refine modularCyclotomicCharacter.unique M
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity M (p ^ n)) _ fun t ht ↦ ?_
    have hs : Units.map φ.symm.toMonoidHom t ∈ rootsOfUnity (p ^ n) L := by
      rw [mem_rootsOfUnity] at ht ⊢
      rw [← map_pow, ht, map_one]
    have key := modularCyclotomicCharacter.spec L
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ n)) g hs
    simp only [Units.coe_map, Units.val_pow_eq_pow_val] at key
    change g (φ.symm (t : M)) = (φ.symm (t : M)) ^ _ at key
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, key, map_pow, RingEquiv.apply_symm_apply]
  · have H' : ¬ ∀ i : ℕ, ∃ ζ : M, IsPrimitiveRoot ζ (p ^ i) := by
      intro hM
      apply H
      intro i
      obtain ⟨ζ, hζ⟩ := hM i
      exact ⟨φ.symm ζ, hζ.map_of_injective φ.symm.injective⟩
    ext1
    simp [cyclotomicCharacter, cyclotomicCharacter.toFun, H, H']

theorem UpperTheory.V.LDataCardLeFinrank.ranges :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l), (cycZ F Ω l).range = KStar.TotallyRealRoots.galImage l F ∧ D.chi.range = KStar.TotallyRealRoots.galImage l F ∧ ∀ v : D.S, (D.chi.comp (locFam D.S D.A v)).range = decImage F l (D.A v) := by
  intro F Ω _ _ _ _ _ l _ D
  have hcyc : (cycZ F Ω l).range = KStar.TotallyRealRoots.galImage l F := by
    let e : Ω ≃ₐ[F] AlgebraicClosure F := IsAlgClosure.equiv F Ω (AlgebraicClosure F)
    have hpt : ∀ σ : Gal(Ω/F), cycZ F Ω l σ = KStar.TotallyRealRoots.eps l F (AlgEquiv.autCongr e σ) := by
      intro σ
      simp only [cycZ, KStar.TotallyRealRoots.eps, MonoidHom.comp_apply]
      exact cyclotomicCharacter_conj_ringEquiv l e.toRingEquiv _
    ext x
    simp only [MonoidHom.mem_range, KStar.TotallyRealRoots.galImage]
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨_, (hpt σ).symm⟩
    · rintro ⟨τ, rfl⟩
      exact ⟨(AlgEquiv.autCongr e).symm τ, by rw [hpt, MulEquiv.apply_symm_apply]⟩
  have hchi : D.chi.range = (cycZ F Ω l).range := by
    have htop : (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    rw [← D.hchi, MonoidHom.range_comp, htop, ← MonoidHom.range_eq_map]
  refine ⟨hcyc, hchi.trans hcyc, fun v ↦ ?_⟩
  have hcomp : D.chi.comp (locFam D.S D.A v) = (cycZ F Ω l).comp (Dec (D.A v)).subtype := by
    rw [← D.hchi]
    rfl
  rw [hcomp, MonoidHom.range_comp, Subgroup.range_subtype]
  rfl
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

section

open KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem nlb_nu_le {U : Subgroup ℤ_[l]ˣ} {u : ℤ_[l]ˣ} (hu : u ∈ U) (tr : ℕ) :
    nu l U tr ≤ emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ tr - 1) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_nu_iff] at hn
  exact le_emultiplicity_of_pow_dvd (hn u hu)

private theorem nlb_exists_unit {a : ℕ} (ha : 1 ≤ a) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a := by
  have h : IsUnit (1 + (l : ℤ_[l]) ^ a) := by
    by_contra hn
    have h1 : ‖1 + (l : ℤ_[l]) ^ a‖ < 1 := PadicInt.not_isUnit_iff.mp hn
    rw [PadicInt.norm_lt_one_iff_dvd] at h1
    have h2 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ a := dvd_pow_self _ (by omega)
    exact PadicInt.prime_p.not_dvd_one ((dvd_add_left h2).mp h1)
  exact ⟨h.unit, by simp⟩

private theorem nlb_main {U : Subgroup ℤ_[l]ˣ} {s e : ℕ} (h : princ l s ≤ U) (he : e ≠ 0) :
    nu l U e ≤ ((max s (if l = 2 then 2 else 1) + e.factorization l : ℕ) : ℕ∞) := by
  have hp : l.Prime := Fact.out
  set a := max s (if l = 2 then 2 else 1) with ha
  have ha1 : 1 ≤ a := le_trans (by split_ifs <;> omega) (le_max_right _ _)
  obtain ⟨u, hu⟩ := nlb_exists_unit (l := l) ha1
  have hm : u ∈ U := h (by
    rw [mem_princ, hu]
    exact pow_dvd_pow _ (le_max_left _ _))
  have hem : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a := by
    rw [hu, emultiplicity_pow_self_of_prime PadicInt.prime_p]
  have key : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ e - 1) =
      emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) + emultiplicity l e := by
    by_cases hl : l = 2
    · refine emultiplicity_pow_sub_one_sq ?_ e
      rw [hu]
      refine pow_dvd_pow _ ?_
      rw [ha, if_pos hl]
      exact le_max_right _ _
    · refine emultiplicity_pow_sub_one_odd hl ?_ e
      rw [hu]
      exact dvd_pow_self _ (by omega)
  have := nlb_nu_le hm e
  rw [key, hem, ← padicValNat_eq_emultiplicity he] at this
  rw [Nat.cast_add, Nat.factorization_def _ hp]
  exact this

end

theorem UpperTheory.V.LDataCardLeFinrank.nuLeBound :
    ∀ (l : ℕ) [Fact l.Prime] (N e : ℕ) (U : Subgroup ℤ_[l]ˣ), KStar.TotallyRealRoots.princ l (N.factorization l) ≤ U → e ≠ 0 → KStar.TotallyRealRoots.nu l U e ≤ (nuBound l N e : ℕ∞) := by
  intro l _ N e U h he
  unfold nuBound
  by_cases hc : l ∣ N ∨ l - 1 ∣ e
  · rw [if_pos hc]
    exact nlb_main h he
  · rw [if_neg hc]
    rw [not_or] at hc
    obtain ⟨h1, h2⟩ := KStar.TotallyRealRoots.levelGroup_eq_top (l := l) hc.1 ⊤
    rw [h1] at h2
    have hU : U = ⊤ := by
      rw [eq_top_iff]
      intro u _
      apply h
      rw [KStar.TotallyRealRoots.mem_princ, Nat.factorization_eq_zero_of_not_dvd hc.1, pow_zero]
      exact one_dvd _
    subst hU
    have h3 := hc.2
    rw [← h2, ← KStar.TotallyRealRoots.nu_pos_iff] at h3
    simpa using not_lt.mp h3
end
