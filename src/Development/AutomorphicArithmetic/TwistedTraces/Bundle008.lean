module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle001
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.inf_fixed_le_spanFix_of_dense_spanAll :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (_ : GroundTheory.Automorphic.IsSmooth τ) (π : UnitaryRep G H) (U : Subgroup G) (_ : IsCompact (U : Set G)) (_ : IsOpen (U : Set G)) (V D : Submodule ℂ H), IsClosed (D : Set H) → π.IsInvariant D → D ≤ V → V ≤ (spanAll τ π V).topologicalClosure → FiniteDimensional ℂ ↥(D ⊓ fixU π U) → D ⊓ fixU π U ≤ spanFix τ π D U := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ π U hUc hUo V D hD hinv hDV hV hfin y hy
  have hQX : spanFix τ π D U ≤ D ⊓ fixU π U := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, x, hx, rfl⟩
    exact ⟨hf.mem x, fun u hu => by rw [← hf.map, hx u hu]⟩
  haveI : FiniteDimensional ℂ ↥(spanFix τ π D U) := Submodule.finiteDimensional_of_le hQX
  have hQc : IsClosed (spanFix τ π D U : Set H) := Submodule.closed_of_finiteDimensional _
  have hc : D.topologicalClosure = D := hD.submodule_topologicalClosure_eq
  have hpm : ∀ v, prj D v ∈ D := fun v => by
    have h : prj D v ∈ D.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hc] at h
  have hpc : ∀ g v, π g (prj D v) = prj D (π g v) := fun g v => by
    have hi : π.IsInvariant D.topologicalClosure := by rw [hc]; exact hinv
    exact congrArg (fun T : H →L[ℂ] H => T v)
      ((UnitaryRep.isInvariant_iff_commute_starProjection D.topologicalClosure).1 hi g).eq
  let Φ : H →L[ℂ] H := prj (fixU π U) ∘L prj D
  have hspan : spanAll τ π V ≤ (spanFix τ π D U).comap (Φ : H →ₗ[ℂ] H) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, x, rfl⟩
    let f' : S →ₗ[ℂ] H := (prj D : H →ₗ[ℂ] H) ∘ₗ f
    have hmap : ∀ g x, f' (τ g x) = π g (f' x) := fun g x => by
      show prj D (f (τ g x)) = π g (prj D (f x))
      rw [hf.map, hpc]
    have hf1 : Eqv τ π D f' := ⟨fun x => hpm _, hmap⟩
    have hf2 : Eqv τ π ⊤ f' := ⟨fun _ => trivial, hmap⟩
    have h := UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π U hUc hUo f' hf2 x
    show prj (fixU π U) (prj D (f x)) ∈ spanFix τ π D U
    have h' : prj (fixU π U) (prj D (f x)) = f' (fixedProj τ hτ hUc hUo x) := h
    rw [h']
    exact Submodule.subset_span ⟨f', hf1, _, (fixedProj τ hτ hUc hUo x).2, rfl⟩
  have hcl : (spanAll τ π V).topologicalClosure ≤ (spanFix τ π D U).comap (Φ : H →ₗ[ℂ] H) :=
    Submodule.topologicalClosure_minimal _ hspan (hQc.preimage Φ.continuous)
  have hy' : Φ y ∈ spanFix τ π D U := hcl (hV (hDV hy.1))
  have hp : prj D y = y := Submodule.starProjection_eq_self_iff.2 (D.le_topologicalClosure hy.1)
  have he : prj (fixU π U) y = y := (UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π U U).2.1 y hy.2
  have hΦ : Φ y = y := by
    show prj (fixU π U) (prj D y) = y
    rw [hp, he]
  rwa [hΦ] at hy'
end

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.finiteDimensional_fixedVectors_isotypic_of_irreducible :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (_ : GroundTheory.Automorphic.IsSmooth τ) (_ : τ.IsIrreducible) (π : UnitaryRep G H) (K : Subgroup G), IsCompact (K : Set G) → IsOpen (K : Set G) → FiniteDimensional ℂ (fixedVectors τ K) → fixedVectors τ K ≠ ⊥ → ∀ t : Module.End ℂ (fixedVectors τ K), ∃ (T : H →L[ℂ] H) (A : S →ₗ[ℂ] S), ((∀ v, T v ∈ fixU π K) ∧ (∀ x, A x ∈ fixedVectors τ K) ∧ (∀ D : Submodule ℂ H, IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, T v ∈ D) ∧ (∀ (G' : Type) [Group G'] [TopologicalSpace G'] (π' : UnitaryRep G' H), (∀ g h v, π g (π' h v) = π' h (π g v)) → ∀ h v, T (π' h v) = π' h (T v)) ∧ (∀ f, Eqv τ π ⊤ f → ∀ x, T (f x) = f (A x))) ∧ ∀ x : fixedVectors τ K, A x = t x := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ hirr π K hKc hKo hfd hne t
  haveI := hfd
  haveI : Nontrivial (fixedVectors τ K) := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨p1, -, p3, -⟩ := UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π K K
  let e : S →ₗ[ℂ] fixedVectors τ K := fixedProj τ hτ hKc hKo
  let b : G → Module.End ℂ (fixedVectors τ K) := fun g => e ∘ₗ τ g ∘ₗ (fixedVectors τ K).subtype
  have he : ∀ y : fixedVectors τ K, e y = y := fun y =>
    Subtype.ext (fixedProj_apply_of_mem hτ hKc hKo y.2)
  have hq : ∀ f, Eqv τ π ⊤ f → ∀ x, prj (fixU π K) (f x) = f (e x) := fun f hf x =>
    UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π K hKc hKo f hf x
  have hcomm : ∀ (G' : Type) [Group G'] [TopologicalSpace G'] (π' : UnitaryRep G' H),
      (∀ g h v, π g (π' h v) = π' h (π g v)) →
        ∀ h v, prj (fixU π K) (π' h v) = π' h (prj (fixU π K) v) := by
    intro G' _ _ π' hc
    exact ((UpperTheory.fixedProjection_invariant_and_commuting_reps G G' H π π' K ⊥).2.2.2 hc).1
  have htop : Algebra.adjoin ℂ (Set.range b) = ⊤ := by
    obtain ⟨c, h1, h2⟩ := UpperTheory.exists_algHom_end_intertwining_mem_adjoin (fixedVectors τ K) (fixedVectors τ K) {LinearMap.id}
      (Set.range fun g => (b g, b g)) (by simp) (by
        rintro _ ⟨g, rfl⟩ _ rfl
        rfl) (by
        intro x hx
        let W : Subrepresentation τ := ⟨Submodule.span ℂ (Set.range fun g => τ g x), fun g v hv => by
          refine (Submodule.map_span_le (τ g) _ _).2 ?_ (Submodule.mem_map_of_mem hv)
          rintro _ ⟨h, rfl⟩
          exact Submodule.subset_span ⟨g * h, by simp⟩⟩
        have hW : Submodule.span ℂ (Set.range fun g => τ g x) = ⊤ := by
          rcases eq_bot_or_eq_top W with h | h
          · have h' : Submodule.span ℂ (Set.range fun g => τ g x) = ⊥ := congrArg Subrepresentation.toSubmodule h
            have : τ 1 x ∈ Submodule.span ℂ (Set.range fun g => τ g x) := Submodule.subset_span ⟨1, rfl⟩
            rw [h', map_one] at this
            exact (hx (Subtype.ext this)).elim
          · exact congrArg Subrepresentation.toSubmodule h
        rw [eq_top_iff]
        rintro y -
        rw [← he y]
        refine (Submodule.map_span_le e (Set.range fun g => τ g x) _).2 ?_ (Submodule.mem_map_of_mem (hW ▸ Submodule.mem_top))
        rintro _ ⟨g, rfl⟩
        exact Submodule.subset_span ⟨_, ⟨g, rfl⟩, rfl⟩)
    rw [eq_top_iff]
    intro s _
    have hcs : c s = s := by simpa using h1 s LinearMap.id rfl
    rw [← hcs]
    refine Algebra.adjoin_mono ?_ (h2 s)
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  have ht : t ∈ Algebra.adjoin ℂ (Set.range b) := by rw [htop]; trivial
  induction ht using Algebra.adjoin_induction with
  | mem s hs =>
    obtain ⟨g, rfl⟩ := hs
    refine ⟨prj (fixU π K) ∘L π g ∘L prj (fixU π K),
      (fixedVectors τ K).subtype ∘ₗ e ∘ₗ τ g ∘ₗ (fixedVectors τ K).subtype ∘ₗ e,
      ⟨fun v => p1 _, fun x => (e _).2, ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact p3 D hD hinv _ (hinv g _ (p3 D hD hinv _ hv))
    · intro G' _ _ π' hc h v
      show prj (fixU π K) (π g (prj (fixU π K) (π' h v))) = π' h (prj (fixU π K) (π g (prj (fixU π K) v)))
      rw [hcomm G' π' hc h v, hc, hcomm G' π' hc]
    · intro f hf x
      show prj (fixU π K) (π g (prj (fixU π K) (f x))) = f (e (τ g (e x)))
      rw [hq f hf x, ← hf.map, hq f hf]
    · intro x
      show ((e (τ g ((e (x : S) : fixedVectors τ K) : S)) : fixedVectors τ K) : S) = _
      rw [he x]
      rfl
  | algebraMap z =>
    refine ⟨z • prj (fixU π K), z • ((fixedVectors τ K).subtype ∘ₗ e),
      ⟨fun v => (fixU π K).smul_mem z (p1 v), fun x => (fixedVectors τ K).smul_mem z (e x).2, ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact D.smul_mem z (p3 D hD hinv _ hv)
    · intro G' _ _ π' hc h v
      show z • prj (fixU π K) (π' h v) = π' h (z • prj (fixU π K) v)
      rw [hcomm G' π' hc h v, map_smul]
    · intro f hf x
      show z • prj (fixU π K) (f x) = f (z • ((e x : fixedVectors τ K) : S))
      rw [hq f hf x, map_smul]
    · intro x
      show z • ((e (x : S) : fixedVectors τ K) : S) = _
      rw [he x]
      simp [Module.algebraMap_end_apply]
  | add s u _ _ hs hu =>
    obtain ⟨T₁, A₁, ⟨a1, a2, a3, a4, a5⟩, a6⟩ := hs
    obtain ⟨T₂, A₂, ⟨b1, b2, b3, b4, b5⟩, b6⟩ := hu
    refine ⟨T₁ + T₂, A₁ + A₂, ⟨fun v => (fixU π K).add_mem (a1 v) (b1 v),
      fun x => (fixedVectors τ K).add_mem (a2 x) (b2 x), ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact D.add_mem (a3 D hD hinv v hv) (b3 D hD hinv v hv)
    · intro G' _ _ π' hc h v
      show T₁ (π' h v) + T₂ (π' h v) = π' h (T₁ v + T₂ v)
      rw [a4 G' π' hc, b4 G' π' hc, map_add (f := _)]
    · intro f hf x
      show T₁ (f x) + T₂ (f x) = f (A₁ x + A₂ x)
      rw [a5 f hf, b5 f hf, map_add (f := _)]
    · intro x
      show A₁ x + A₂ x = _
      rw [a6 x, b6 x]
      rfl
  | mul s u _ _ hs hu =>
    obtain ⟨T₁, A₁, ⟨a1, a2, a3, a4, a5⟩, a6⟩ := hs
    obtain ⟨T₂, A₂, ⟨b1, b2, b3, b4, b5⟩, b6⟩ := hu
    refine ⟨T₁ ∘L T₂, A₁ ∘ₗ A₂, ⟨fun v => a1 _, fun x => a2 _, ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact a3 D hD hinv _ (b3 D hD hinv v hv)
    · intro G' _ _ π' hc h v
      show T₁ (T₂ (π' h v)) = π' h (T₁ (T₂ v))
      rw [b4 G' π' hc, a4 G' π' hc]
    · intro f hf x
      show T₁ (T₂ (f x)) = f (A₁ (A₂ x))
      rw [b5 f hf, a5 f hf]
    · intro x
      show A₁ (A₂ x) = _
      rw [b6 x, a6 (u x)]
      rfl
end
