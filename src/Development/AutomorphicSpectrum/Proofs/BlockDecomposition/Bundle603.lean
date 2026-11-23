module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle597
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS.HeckeSum

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem heckeVec_finset_sum {ι : Type} (ρ : Representation ℂ G V) (K : Subgroup G) (s : Finset ι) (f : ι → ℂ)
    (h : ι → G → ℂ) (x : V) (hf : ∀ p ∈ s, {c : G ⧸ K | h p c.out ≠ 0}.Finite) :
    heckeVec ρ K (fun g => ∑ p ∈ s, f p * h p g) x = ∑ p ∈ s, f p • heckeVec ρ K (h p) x := by
  have e : ∀ c : G ⧸ K, (∑ p ∈ s, f p * h p c.out) • ρ c.out x =
      ∑ p ∈ s, f p • (h p c.out • ρ c.out x) := fun c => by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun p _ => mul_smul _ _ _
  unfold heckeVec
  rw [finsum_congr e, finsum_sum_comm]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_finsum]
  · intro p hp
    exact (hf p hp).subset fun c hc h0 => hc (by simp [h0])

theorem biInv_out {K : Subgroup G} {h : G → ℂ} (hh : IsBiInv K h) (g : G) :
    h ((g : G ⧸ K).out) = h g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  have e := hh 1 k g
  simp only [OneMemClass.coe_one, one_mul] at e
  rw [hk, e]

variable {A B : Type} [Group A] [Group B]

theorem finite_pair {KA : Subgroup A} {KB : Subgroup B} {fA : A → ℂ} {fB : B → ℂ}
    (hA : IsBiInv KA fA) (hB : IsBiInv KB fB) (fa : {c : A ⧸ KA | fA c.out ≠ 0}.Finite)
    (fb : {c : B ⧸ KB | fB c.out ≠ 0}.Finite) :
    {c : (A × B) ⧸ KA.prod KB | fA c.out.1 * fB c.out.2 ≠ 0}.Finite := by
  refine Set.Finite.of_finite_image
    (f := fun c : (A × B) ⧸ KA.prod KB => (((c.out.1 : A ⧸ KA)), ((c.out.2 : B ⧸ KB))))
    ((fa.prod fb).subset ?_) ?_
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : fA c.out.1 * fB c.out.2 ≠ 0 := hc
    refine ⟨?_, ?_⟩
    · change fA ((c.out.1 : A ⧸ KA).out) ≠ 0
      rw [biInv_out hA]
      exact left_ne_zero_of_mul hc'
    · change fB ((c.out.2 : B ⧸ KB).out) ≠ 0
      rw [biInv_out hB]
      exact right_ne_zero_of_mul hc'
  · intro c _ d _ e
    have e1 := QuotientGroup.eq.1 (congrArg Prod.fst e)
    have e2 := QuotientGroup.eq.1 (congrArg Prod.snd e)
    rw [← c.out_eq', ← d.out_eq']
    exact QuotientGroup.eq.2 (Subgroup.mem_prod.2 ⟨by simpa using e1, by simpa using e2⟩)

end Abstract

theorem heckeVec_Tj_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℂ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GLw a w × GLw b w) V) (x : V),
    heckeVec ρ (K2 a b w) (fun g => ∑ p ∈ s, f p * (Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2)) x =
      ∑ p ∈ s, f p • heckeVec ρ (K2 a b w) (fun g => Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2) x := by
  intro E _ _ _ a b w ϖ hϖ s f V _ _ ρ x
  refine heckeVec_finset_sum ρ (K2 a b w) s f
    (fun p g => Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2) x fun p _ => ?_
  have ha := Tj_mem_hecke (n := a) hϖ p.1
  have hb := Tj_mem_hecke (n := b) hϖ p.2
  exact finite_pair ha.1 hb.1 (Formalism.UG.P.finite_support_cosets (Final.GLintComm E w a) ha.2)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm E w b) hb.2)

end GlobalTheory.CompanionTheory.CtS.HeckeSum
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen

theorem lip_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : PI.VolStabS.TensAllW.LIP S) : PI.VolStabS.TensAllW.LIP R := by
  intro m n _ _ _ _ W hW
  obtain ⟨P, hP⟩ := h m n (W.map e) (by
    intro c hc
    have hc' : W *ᵥ (fun j => e.symm (c j)) = 0 := by
      funext i
      apply e.injective
      have := congrFun hc i

      simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum] using this
    have h0 := hW _ hc'
    funext j
    have := congrFun h0 j
    simpa using this)
  refine ⟨P.map e.symm, ?_⟩
  ext i j
  apply e.injective
  have := congrFun (congrFun hP i) j
  simp only [Matrix.mul_apply, Matrix.map_apply] at this

  rw [Matrix.mul_apply, map_sum]
  simp only [map_mul, Matrix.map_apply, RingEquiv.apply_symm_apply]
  rw [this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem lip_of_artinian_reduced (R : Type) [CommRing R] [IsArtinianRing R] [IsReduced R] :
    PI.VolStabS.TensAllW.LIP R := by
  classical
  letI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  letI : ∀ m : MaximalSpectrum R, Field (R ⧸ m.asIdeal) := fun m =>
    Ideal.Quotient.field m.asIdeal
  exact lip_of_ringEquiv (IsArtinianRing.equivPi R)
    (PI.VolStabS.TensAllW.lip_pi (fun m : MaximalSpectrum R => R ⧸ m.asIdeal)
      (fun m => PI.VolStabS.TensAllW.lip_field _))

theorem isOpen_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ), IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  intro F E _ _ _ _ _ σ _ R _ _ _ _ _ hR n M
  obtain ⟨hT, -, -, -, hA, hRed, hU, -⟩ := hR
  haveI := hT
  haveI := hA
  haveI := hRed
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hUo : IsOpen {r : R | IsUnit r} := by
    have := hU.isOpen_range
    convert this using 1
    ext r
    simp [IsUnit]
  exact PI.VolStabS.TensAllW.isOpen_linIndep (Module.finBasis F E) R hUo
    (lip_of_artinian_reduced R)

end GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen
end
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.decomposition_group_frobenius_factor : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ g : Dec (F := F) A, ∃ a < N, ∃ t i : Dec (F := F) A, (i : G F Ω) ∈ Ine (F := F) A ∧ g = φ ^ a * t ^ N * i := by
  first | exact @GlobalTheory.CompanionTheory.TameDecomp.exists_frob_pow_mul_pow_mul_inertia | exact GlobalTheory.CompanionTheory.TameDecomp.exists_frob_pow_mul_pow_mul_inertia | (intros; apply GlobalTheory.CompanionTheory.TameDecomp.exists_frob_pow_mul_pow_mul_inertia <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.frobenius_power_fixes_root_unique : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ ξ : Ω, IsPrimitiveRoot ξ (normV v ^ N - 1) → ∀ (a : ℕ) (t i : Dec (F := F) A), a < N → (i : G F Ω) ∈ Ine (F := F) A → ((φ ^ a * t ^ N * i : Dec (F := F) A) : G F Ω) ξ = ξ → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TameAction.eq_zero_of_fixes_primitiveRoot | exact GlobalTheory.CompanionTheory.TameAction.eq_zero_of_fixes_primitiveRoot | (intros; apply GlobalTheory.CompanionTheory.TameAction.eq_zero_of_fixes_primitiveRoot <;> assumption)
end
