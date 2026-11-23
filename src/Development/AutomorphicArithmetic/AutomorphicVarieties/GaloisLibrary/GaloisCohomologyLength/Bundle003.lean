module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LeNuIffPowMemPrinc
public import Formalism.GaloisCohomology.Statement
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle002
import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Int
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem units_zpow_neg_smul_eq_self_iff (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Module ℤ_[l] A]
    (v : ℤ_[l]ˣ) (e : ℤ) (x : A) :
    ((v ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • x = x ↔ ((v : ℤ_[l]) ^ e.natAbs) • x = x := by
  have key : ∀ n : ℕ, ((v ^ (-(n:ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) • x = x ↔ ((v : ℤ_[l]) ^ n) • x = x := by
    intro n
    rw [← Units.val_pow_eq_pow_val, ← Units.smul_def, ← Units.smul_def, zpow_neg, zpow_natCast]
    constructor
    · intro h
      conv_lhs => rw [← h]
      simp
    · intro h
      conv_lhs => rw [← h]
      simp
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · simpa using key n
  · simp [← Units.val_pow_eq_pow_val]

theorem UpperTheory.V.LDataCardLeFinrank.H0_scalRep_inv_pow_eq_twistInv :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (ψ : Γ →* ℤ_[l]ˣ) (e : ℤ), H0 (scalRep (QZ l) (ψ ^ (-e))) = KStar.TotallyRealRoots.twistInv l (QZ l) ψ.range e.natAbs := by
  intro l _ Γ _ ψ e
  ext x
  rw [KStar.TotallyRealRoots.mem_twistInv]
  change (∀ g : Γ, (scalRep (QZ l) (ψ ^ (-e))) g x = x) ↔ _
  simp only [scalRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply,
    MonoidHom.zpow_apply]
  constructor
  · rintro h u ⟨g, rfl⟩
    exact (units_zpow_neg_smul_eq_self_iff l (QZ l) (ψ g) e x).mp (h g)
  · intro h g
    exact (units_zpow_neg_smul_eq_self_iff l (QZ l) (ψ g) e x).mpr (h _ ⟨g, rfl⟩)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.lenTwist :
    ∀ (l : ℕ) [Fact l.Prime] (U : Subgroup ℤ_[l]ˣ) (tr : ℕ), Module.length ℤ_[l] (KStar.TotallyRealRoots.twistInv l (QZ l) U tr) = KStar.TotallyRealRoots.nu l U tr ∧ Nonempty (KStar.TotallyRealRoots.twistInv l (QZ l) U tr ≃ₗ[ℤ_[l]] KStar.TotallyRealRoots.H0 l U tr) := by
  intro l _ U tr
  have e : ZlSub l = (1 : Submodule ℤ_[l] ℚ_[l]) := Submodule.one_eq_range.symm
  let f : QZ l ≃ₗ[ℤ_[l]] KStar.TotallyRealRoots.QmodZ l := Submodule.quotEquivOfEq _ _ e
  have hmap : (KStar.TotallyRealRoots.twistInv l (QZ l) U tr).map (f : QZ l →ₗ[ℤ_[l]] KStar.TotallyRealRoots.QmodZ l) =
      KStar.TotallyRealRoots.twistInv l (KStar.TotallyRealRoots.QmodZ l) U tr := by
    ext y
    simp only [Submodule.mem_map, KStar.TotallyRealRoots.mem_twistInv]
    constructor
    · rintro ⟨x, hx, rfl⟩ u hu
      rw [LinearEquiv.coe_coe, ← f.map_smul, hx u hu]
    · intro hy
      refine ⟨f.symm y, fun u hu => ?_, by simp⟩
      rw [← f.symm.map_smul, hy u hu]
  let g : KStar.TotallyRealRoots.twistInv l (QZ l) U tr ≃ₗ[ℤ_[l]] KStar.TotallyRealRoots.H0 l U tr :=
    (f.submoduleMap _).trans (LinearEquiv.ofEq _ _ hmap)
  have hnu : ¬IsUnit ((l : ℕ) : ℤ_[l]) := PadicInt.irreducible_p.not_isUnit
  have h := KStar.TotallyRealRoots.length_twistInvOver (O := ℤ_[l]) ℚ_[l] hnu U tr
  have hv : IsDiscreteValuationRing.addVal ℤ_[l] (l : ℤ_[l]) = 1 :=
    IsDiscreteValuationRing.addVal_uniformizer PadicInt.irreducible_p
  rw [hv, mul_one] at h
  have hsame : KStar.TotallyRealRoots.twistInvOver l ℤ_[l] (KStar.Selmer.FracMod ℤ_[l] ℚ_[l]) U tr =
      KStar.TotallyRealRoots.twistInv l (KStar.TotallyRealRoots.QmodZ l) U tr := by
    ext x
    rw [KStar.TotallyRealRoots.mem_twistInv]
    rfl
  rw [hsame] at h
  refine ⟨?_, ⟨g⟩⟩
  rw [g.length_eq]
  exact h
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.cardAbove :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l), D.S.card ≤ Module.finrank ℚ F := by
  intro F Ω _ _ _ _ _ l hl D
  classical
  have hn : l.Prime := hl.out
  have hp0 : (Ideal.span {(l : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne_zero
  have hmax : (Ideal.span {(l : ℤ)} : Ideal ℤ).IsMaximal := inferInstance
  refine le_trans (Finset.card_le_card_of_injOn
    (t := IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 F))
    (fun p => p.asIdeal) ?_ ?_) (Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hp0)
  · intro p hp
    rw [D.hS] at hp
    have hp' : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal := hp
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0]
    have := p.isPrime
    refine ⟨p.isPrime, ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hp'
  · intro p _ p' _ h
    exact HeightOneSpectrum.ext h
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.contScal :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ψ : Γ →* ℤ_[l]ˣ), (Continuous fun g => ((ψ g : ℤ_[l]ˣ) : ℤ_[l])) → ContAction (scalRep (QZ l) ψ) := by
  intro l _ Γ _ _ ψ hψ
  haveI hd : DiscreteTopology (QZ l) := ⟨rfl⟩
  unfold ReciprocityTheory.Gal.ContAction
  apply continuous_prod_of_discrete_right.mpr
  intro a
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
  let q : ℚ_[l] → QZ l := fun z => Submodule.Quotient.mk z
  have hmk : Continuous q := by
    refine (continuous_discrete_rng (β := QZ l)).mpr ?_
    intro b
    obtain ⟨y, rfl⟩ : ∃ y, q y = b := Submodule.Quotient.mk_surjective (ZlSub l) b
    have e : q ⁻¹' {q y} = Metric.closedBall y 1 := by
      ext z
      have h1 : q z = q y ↔ z - y ∈ ZlSub l := Submodule.Quotient.eq (ZlSub l)
      rw [Set.mem_preimage, Set.mem_singleton_iff, h1, LinearMap.mem_range,
        Metric.mem_closedBall, dist_eq_norm]
      constructor
      · rintro ⟨w, hw⟩
        rw [← hw]
        exact w.norm_le_one
      · intro h
        exact ⟨⟨z - y, h⟩, rfl⟩
    rw [e]
    exact IsUltrametricDist.isOpen_closedBall y one_ne_zero
  have hc : Continuous fun g : Γ => ((ψ g : ℤ_[l]) : ℚ_[l]) * x :=
    (continuous_subtype_val.comp hψ).mul continuous_const
  refine (hmk.comp hc).congr ?_
  intro g
  rfl
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem pt_val_lt_one {Ω Ω' : Type} [Field Ω] [Field Ω'] {σ : Ω ≃+* Ω'} {A : ValuationSubring Ω}
    {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A') (x : Ω) :
    A.valuation x < 1 ↔ A'.valuation (σ x) < 1 := by
  rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω'), ← hA, ← map_inv₀, ← hA,
    map_eq_zero_iff _ σ.injective]

theorem UpperTheory.V.LDataCardLeFinrank.placeTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (f : F →+* F') (σ : Ω ≃+* Ω'), (∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) →
      ∀ φ : G F' Ω' →* G F Ω, (∀ g x, σ (φ g x) = g (σ x)) → ∀ (v' : HeightOneSpectrum (𝓞 F')) (A' : ValuationSubring Ω'), IsPlaceOver A' v' →
      ∃ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v ∧ (∀ l : ℕ, v ∈ Above (F := F) l ↔ v' ∈ Above (F := F') l) ∧ (∀ x, x ∈ A ↔ σ x ∈ A') ∧
        (∀ g, φ g ∈ Dec (F := F) A ↔ g ∈ Dec (F := F') A') ∧ ∀ g, φ g ∈ Ine (F := F) A ↔ g ∈ Ine (F := F') A' := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ f σ h φ hφ v' A' hv'
  have hne : v'.asIdeal.comap (RingOfIntegers.mapRingHom f) ≠ ⊥ := by
    intro hb
    have h1 : ((Ideal.absNorm v'.asIdeal : ℕ) : 𝓞 F) ∈ v'.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [hb, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h1
    exact v'.ne_bot h1
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨v'.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, hne⟩
  have hA : ∀ x, x ∈ A'.comap σ.toRingHom ↔ σ x ∈ A' := fun x => Iff.rfl
  generalize A'.comap σ.toRingHom = A at hA
  have hD : ∀ g, φ g ∈ Dec (F := F) A ↔ g ∈ Dec (F := F') A' := by
    intro g
    constructor
    · intro hg
      rw [mem_Dec]
      ext y
      obtain ⟨x, rfl⟩ := σ.surjective y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hφ, ← hA, ← hA, map_inv]
      exact apply_mem_iff_of_mem_Dec ((Dec (F := F) A).inv_mem hg) _
    · intro hg
      rw [mem_Dec]
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def, hA, hA, hφ]
      exact apply_mem_iff_of_mem_Dec ((Dec (F := F') A').inv_mem hg) _
  refine ⟨v, A, ?_, ?_, hA, hD, ?_⟩
  · intro x
    have e : x ∈ v.asIdeal ↔ RingOfIntegers.mapRingHom f x ∈ v'.asIdeal := Iff.rfl
    rw [e, ← hv', pt_val_lt_one hA, h]
    rfl
  · intro l
    show RingOfIntegers.mapRingHom f ((l : ℕ) : 𝓞 F) ∈ v'.asIdeal ↔ ((l : ℕ) : 𝓞 F') ∈ v'.asIdeal
    rw [map_natCast]
  · intro g
    constructor
    · intro hg
      refine ⟨(hD g).1 hg.1, fun y hy => ?_⟩
      obtain ⟨x, rfl⟩ := σ.surjective y
      rw [← hφ, ← map_sub, ← pt_val_lt_one hA]
      exact hg.2 _ ((A.valuation_le_one_iff _).2 ((hA x).2 ((A'.valuation_le_one_iff _).1 hy)))
    · intro hg
      refine ⟨(hD g).2 hg.1, fun x hx => ?_⟩
      rw [pt_val_lt_one hA, map_sub, hφ]
      exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).1 ((A.valuation_le_one_iff _).1 hx)))
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem length_add_coker {R X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) :
    Module.length R X + Module.length R (Y ⧸ LinearMap.range f) =
      Module.length R (LinearMap.ker f) + Module.length R Y := by
  have hX := Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hY := Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [hX, hY, (f.quotKerEquivRange).length_eq, add_assoc]

theorem UpperTheory.V.LDataCardLeFinrank.vFormula :
    Formalism.GaloisCohomology.VFormula := by
  intro F Ω _ _ _ _ _ l _ D e hcase hcoker hsha hloc
  have hker : LinearMap.ker (localH2 D e) = Sha2Zl D e := by
    unfold localH2
    rw [LinearMap.ker_pi]
    rfl
  have key := length_add_coker (localH2 D e)
  rw [hcoker hcase, hker, hsha hcase, Module.length_pi_of_fintype] at key
  unfold VLen sumLocalH0TwistLength
  rw [key]
  congr 1
  exact Finset.sum_congr rfl (fun v _ => hloc v)
end
