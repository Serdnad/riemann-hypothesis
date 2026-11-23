module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle095
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle007
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
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
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle002
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

@[expose] public section

section

open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Factor

open CompanionTheory.D.gk.admitted.FinOfPIAux

variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Diag

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem diag_mem_of_bicomm (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (C : Submodule ℂ (PiLp 2 (fun _ : ι => H))) (hcl : IsClosed (C : Set (PiLp 2 (fun _ : ι => H))))
    (hC : ∀ g, ∀ z ∈ C, diag (σ g) z ∈ C) (T : H →L[ℂ] H)
    (hT : ∀ S : H →L[ℂ] H, (∀ g, S * σ g = σ g * S) → S * T = T * S)
    (z : PiLp 2 (fun _ : ι => H)) (hz : z ∈ C) :
    diag T z ∈ C := by
  haveI : CompleteSpace C := hcl.completeSpace_coe
  have hPg := proj_comm (ι := ι) σ hσ C hC
  let Q : ι → ι → H →L[ℂ] H := fun k l =>
    (PiLp.proj 2 (fun _ : ι => H) k).comp (C.starProjection.comp (incl l))
  have hQ : ∀ k l, Q k l * T = T * Q k l := by
    intro k l
    apply hT
    intro g
    ext v
    simp only [Q, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    rw [← diag_incl, hPg, diag_apply]
  have hsum : ∀ w : PiLp 2 (fun _ : ι => H), ∀ k,
      (C.starProjection w).ofLp k = ∑ l, Q k l (w.ofLp l) := by
    intro w k
    conv_lhs => rw [← sum_incl w]

    simp [Q, map_sum]
  have key : C.starProjection (diag T z) = diag T (C.starProjection z) := by
    ext k

    rw [hsum, diag_apply, hsum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [diag_apply]
    exact congrArg (fun S : H →L[ℂ] H => S (z.ofLp l)) (hQ k l)
  have hz' : C.starProjection z = z := (Submodule.starProjection_eq_self_iff).2 hz
  rw [← hz', ← key]
  exact C.starProjection_apply_mem _

theorem sum_eq_zero_of_bicomm (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (L : ι → H →L[ℂ] H) (y : ι → H) (h : ∀ g, ∑ k, L k (σ g (y k)) = 0) (T : H →L[ℂ] H)
    (hT : ∀ S : H →L[ℂ] H, (∀ g, S * σ g = σ g * S) → S * T = T * S) :
    ∑ k, L k (T (y k)) = 0 := by
  let y' : PiLp 2 (fun _ : ι => H) := WithLp.toLp 2 y
  let V : Submodule ℂ (PiLp 2 (fun _ : ι => H)) :=
    Submodule.span ℂ (Set.range fun g : G => diag (σ g) y')
  have hdiag_mul : ∀ a b : G, ∀ w : PiLp 2 (fun _ : ι => H),
      diag (σ a) (diag (σ b) w) = diag (σ (a * b)) w := by
    intro a b w
    ext k
    simp only [diag_apply, map_mul, ContinuousLinearMap.mul_apply]
  have hCinv : ∀ g, ∀ z ∈ V.topologicalClosure, diag (σ g) z ∈ V.topologicalClosure := by
    intro g
    have hle : V ≤ V.topologicalClosure.comap
        ((diag (σ g) : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H))) :
          (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] (PiLp 2 (fun _ : ι => H))) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      show diag (σ g) (diag (σ b) y') ∈ V.topologicalClosure
      rw [hdiag_mul]
      exact V.le_topologicalClosure (Submodule.subset_span ⟨g * b, rfl⟩)
    have hcl' : IsClosed ((V.topologicalClosure.comap
        ((diag (σ g) : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H))) :
          (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] (PiLp 2 (fun _ : ι => H))) :
          Submodule ℂ (PiLp 2 (fun _ : ι => H))) : Set (PiLp 2 (fun _ : ι => H))) :=
      V.isClosed_topologicalClosure.preimage (diag (σ g)).continuous
    intro z hz
    exact Submodule.topologicalClosure_minimal V hle hcl' hz
  have hy' : y' ∈ V.topologicalClosure := by
    apply V.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    ext k
    simp [diag_apply]
  have hT' := diag_mem_of_bicomm σ hσ V.topologicalClosure V.isClosed_topologicalClosure
    hCinv T hT y' hy'
  let Λ : (PiLp 2 (fun _ : ι => H)) →L[ℂ] H := ∑ k, (L k).comp (PiLp.proj 2 (fun _ : ι => H) k)
  have hΛ : ∀ w : PiLp 2 (fun _ : ι => H), Λ w = ∑ k, L k (w.ofLp k) := by
    intro w
    simp [Λ]
  have hker : V.topologicalClosure ≤ LinearMap.ker (Λ : (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] H) := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΛ, diag_apply]
      simpa [y'] using h g
    · exact Λ.isClosed_ker
  have hfin := hker hT'
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΛ, diag_apply] at hfin
  simpa [y'] using hfin

end Diag

theorem standard_polynomial_vanishes_on_bicommutant (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (E : H →L[ℂ] H) (M : ℕ) (h : ∀ g : Fin M → G, stdPoly E (fun i => σ (g i)) = 0)
    (a : Fin M → H →L[ℂ] H)
    (ha : ∀ i, ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * a i = a i * T) :
    stdPoly E a = 0 := by
  classical
  have step : ∀ j : ℕ, ∀ g : Fin M → G,
      stdPoly E (fun i : Fin M => if (i : ℕ) < j then a i else σ (g i)) = 0 := by
    intro j
    induction j with
    | zero => intro g; simpa using h g
    | succ j ih =>
      intro g
      by_cases hj : j < M
      · let k : Fin M := ⟨j, hj⟩
        let b : Fin M → H →L[ℂ] H := fun i => if (i : ℕ) < j then a i else σ (g i)
        have hb : (fun i : Fin M => if (i : ℕ) < j + 1 then a i else σ (g i)) =
            Function.update b k (a k) := by
          funext i
          by_cases hik : i = k
          · subst hik
            simp [b, k]
          · rw [Function.update_of_ne hik]
            have hne : (i : ℕ) ≠ j := fun e => hik (Fin.ext e)
            by_cases hlt : (i : ℕ) < j
            · have h2 : (i : ℕ) < j + 1 := by omega
              simp [b, hlt, h2]
            · have h2 : ¬ (i : ℕ) < j + 1 := by omega
              simp [b, hlt, h2]
        obtain ⟨A, B, hAB⟩ := CompanionTheory.D.gk.admitted.FinOfPIAux.stdPoly_update E b k
        have hσk : ∀ x : G, stdPoly E (Function.update b k (σ x)) = 0 := by
          intro x
          have hx := ih (Function.update g k x)
          convert hx using 2
          funext i
          by_cases hik : i = k
          · subst hik
            simp [b, k]
          · rw [Function.update_of_ne hik]
            simp [b, Function.update_of_ne hik]
        rw [hb, hAB]
        ext v
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply,
          ContinuousLinearMap.zero_apply]
        refine sum_eq_zero_of_bicomm σ hσ A (fun π => B π v) ?_ (a k) (ha k)
        intro x
        have hv := congrArg (fun S : H →L[ℂ] H => S v) ((hAB (σ x)).symm.trans (hσk x))
        simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply] using hv
      · have hiff : ∀ i : Fin M, ((i : ℕ) < j + 1 ↔ (i : ℕ) < j) := fun i => by
          have := i.isLt
          omega
        simpa [hiff] using ih g
  simpa using step M (fun _ => 1)

theorem stdPoly_bicomm : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (E : H →L[ℂ] H) (m : ℕ), (∀ g : Fin m → G, stdPoly E (fun i => σ (g i)) = 0) →
    ∀ a : Fin m → (H →L[ℂ] H), (∀ i, ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * a i = a i * T) → stdPoly E a = 0 := by
  intro G H _ _ _ _ σ hσ E m h a ha
  exact standard_polynomial_vanishes_on_bicommutant σ hσ E m h a ha

end GlobalTheory.CompanionTheory.Factor
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjFlat

theorem acyclic_extendScalars_of_bounded_flat : ∀ (R K : Type) [CommRing R] [CommRing K] (χ : R →+* K) (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (hn : ∀ p, n < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p)) (hac : C.Acyclic), (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj C).Acyclic :=
  fun _ _ _ _ χ C n hn hflat hac => GlobalTheory.AbLaw.acyclic_extendScalars_of_flat χ C n hn hflat hac

end GlobalTheory.CompanionTheory.PointSurjFlat
end

section

open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Factor

theorem schur_on_minimal_subspace :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (N : Set (H →L[ℂ] H))
    (Q : Submodule ℂ H), (∀ T ∈ N, star T ∈ N) → IsClosed (Q : Set H) → (∀ T ∈ N, ∀ v ∈ Q, T v ∈ Q) →
    (∀ U : Submodule ℂ H, IsClosed (U : Set H) → U ≤ Q → (∀ T ∈ N, ∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = Q) →
    ∀ A : H →L[ℂ] H, (∀ T ∈ N, T * A = A * T) → ∃ c : ℂ, ∀ v ∈ Q, A v - c • v ∈ Qᗮ := by
  intro H _ _ _ N Q hstar hQc hQinv hmin A hcomm
  haveI : CompleteSpace Q := hQc.completeSpace_coe

  let σ : N → (Q →L[ℂ] Q) := fun T =>
    (T.1.comp Q.subtypeL).codRestrict Q (fun v => hQinv T.1 T.2 v v.2)

  have hperp : ∀ T ∈ N, ∀ w ∈ Qᗮ, T w ∈ Qᗮ := by
    intro T hT w hw
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro u hu
    have h1 : ⟪u, T w⟫_ℂ = ⟪(star T) u, w⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hw _ (hQinv _ (hstar T hT) u hu)

  have hproj : ∀ T ∈ N, ∀ w : H, Q.starProjection (T w) = T (Q.starProjection w) := by
    intro T hT w
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · exact hQinv T hT _ (Submodule.starProjection_apply_mem Q w)
    · rw [← map_sub]
      exact hperp T hT _ (Submodule.sub_starProjection_mem_orthogonal w)
  let B : Q →L[ℂ] Q := (Q.orthogonalProjection).comp (A.comp Q.subtypeL)
  have hB : ∀ v : Q, ((B v : Q) : H) = Q.starProjection (A v) := fun _ => rfl
  obtain ⟨c, hc⟩ := GlobalTheory.hilbert_schur_of_adjoint_closed N Q σ
    (by
      intro g
      refine ⟨⟨star g.1, hstar g.1 g.2⟩, ?_⟩
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      change ⟪(star g.1) (x : H), (y : H)⟫_ℂ = ⟪(x : H), g.1 (y : H)⟫_ℂ
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left])
    (by
      intro S hS hSinv
      have hclosed : IsClosed ((S.map Q.subtype : Submodule ℂ H) : Set H) := by
        exact hQc.isClosedEmbedding_subtypeVal.isClosedMap _ hS
      have hle : S.map Q.subtype ≤ Q := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hinv : ∀ T ∈ N, ∀ v ∈ S.map Q.subtype, T v ∈ S.map Q.subtype := by
        rintro T hT _ ⟨x, hx, rfl⟩
        exact ⟨σ ⟨T, hT⟩ x, hSinv ⟨T, hT⟩ x hx, rfl⟩
      rcases hmin _ hclosed hle hinv with h | h
      · left
        rw [eq_bot_iff]
        intro x hx
        have hx' : (x : H) ∈ S.map Q.subtype := ⟨x, hx, rfl⟩
        rw [h, Submodule.mem_bot] at hx'
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext hx')
      · right
        rw [eq_top_iff]
        intro x _
        have hx : (x : H) ∈ S.map Q.subtype := by
          rw [h]
          exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        have : y = x := Subtype.ext hyx
        exact this ▸ hy)
    B
    (by
      intro g
      ext v
      change Q.starProjection (A (g.1 v)) = g.1 (Q.starProjection (A v))
      have h := congrArg (fun X : H →L[ℂ] H => X (v : H)) (hcomm g.1 g.2)
      have h' : g.1 (A v) = A (g.1 v) := h
      rw [← h', hproj g.1 g.2])
  refine ⟨c, fun v hv => ?_⟩
  have h1 : Q.starProjection (A v) = c • v := by
    have := hB ⟨v, hv⟩
    rw [hc] at this
    simpa using this.symm
  rw [← h1]
  exact Submodule.sub_starProjection_mem_orthogonal _

end GlobalTheory.CompanionTheory.Factor
end

section

open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.OrthoFamily

theorem exists_minimal_of_no_family_below
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : Set (Submodule ℂ H))
    (hcl : ∀ S ∈ L, IsClosed (S : Set H))
    (hinf : ∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) (n : ℕ) :
    ∀ S ∈ L, S ≠ ⊥ →
      (∀ f : Fin n → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → (∀ i, f i ≤ S) →
        ¬ Pairwise fun i k => f i ⟂ f k) →
      ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q := by
  induction n with
  | zero =>
    intro S _ _ hS
    exact (hS (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
      (fun i => i.elim0)).elim
  | succ n ih =>
    intro S hSL hS0 hS
    by_cases hmin : ∀ T ∈ L, T ≤ S → T = ⊥ ∨ T = S
    · exact ⟨S, hSL, hS0, hmin⟩
    · push_neg at hmin
      obtain ⟨T, hTL, hTS, hT0, hTne⟩ := hmin
      refine ih T hTL hT0 ?_
      intro f hfL hf0 hfT hpw
      haveI : CompleteSpace T := (hcl T hTL).completeSpace_coe
      have hR0 : S ⊓ Tᗮ ≠ ⊥ := by
        intro h
        apply hTne
        have hsup := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hTS
        rw [inf_comm, h, sup_bot_eq] at hsup
        exact hsup
      have ho : ∀ j, (S ⊓ Tᗮ) ⟂ f j := fun j => inf_le_right.trans (Submodule.orthogonal_le (hfT j))
      apply hS (Fin.cons (S ⊓ Tᗮ) f)
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact hinf S hSL T hTL
        | succ j => rw [Fin.cons_succ]; exact hfL j
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact hR0
        | succ j => rw [Fin.cons_succ]; exact hf0 j
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact inf_le_left
        | succ j => rw [Fin.cons_succ]; exact (hfT j).trans hTS
      · intro i k hik
        induction i using Fin.cases with
        | zero =>
          induction k using Fin.cases with
          | zero => exact absurd rfl hik
          | succ j =>
            rw [Fin.cons_zero, Fin.cons_succ]
            exact ho j
        | succ j =>
          induction k using Fin.cases with
          | zero =>
            rw [Fin.cons_zero, Fin.cons_succ]
            exact (ho j).symm
          | succ j' =>
            rw [Fin.cons_succ, Fin.cons_succ]
            exact hpw (fun h => hik (congrArg Fin.succ h))

theorem exists_minimal_of_orthogonal_bound :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (L : Set (Submodule ℂ H)) (m : ℕ)
    (S₀ : Submodule ℂ H), (∀ S ∈ L, IsClosed (S : Set H)) → (∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) → S₀ ∈ L → S₀ ≠ ⊥ →
    (∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → ¬ Pairwise fun i k => f i ⟂ f k) →
    ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q := by
  intro H _ _ _ L m S₀ hcl hinf hS₀ hS₀0 hfam
  exact exists_minimal_of_no_family_below L hcl hinf (m + 1) S₀ hS₀ hS₀0
    (fun f hfL hf0 _ => hfam f hfL hf0)

end GlobalTheory.CompanionTheory.OrthoFamily
end
