module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.ArchVanish

open GlobalTheory.AdelicU

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

variable {σ J}

theorem isMulCommutative_cent_projArch_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (w : InfinitePlace F) :
    IsMulCommutative (Orb.cent (projArch σ J w (ratEmb σ J γ))) :=
  Orb.isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)


end General

end GlobalTheory.ArchVanish

end

namespace GlobalTheory.ArchVanish


end GlobalTheory.ArchVanish
end

section

noncomputable section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory.TrFinDense

theorem span_values_dense : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ hU : IsSubrep π ⊤, ∀ N : Subrepresentation (finPartDSSm M hU), N ≠ ⊥ → (Submodule.span ℂ {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}).topologicalClosure = ⊤ := by
  intro D V S M H _ _ _ π hπ hU N hN
  classical
  set Sv : Set H := {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}
    with hSv
  set W : Submodule ℂ H := Submodule.span ℂ Sv with hW

  let Mon : Submonoid (GA D V) :=
    { carrier := {g | Sv ⊆ W.comap (π g : H →ₗ[ℂ] H)}
      mul_mem' := by
        intro a b ha hb z hz
        have hbz : π b z ∈ W := hb hz
        have : W ≤ W.comap (π a : H →ₗ[ℂ] H) := Submodule.span_le.2 ha
        show π (a * b) z ∈ W
        rw [map_mul]
        exact this hbz
      one_mem' := by
        intro z hz
        show π 1 z ∈ W
        rw [map_one]
        exact Submodule.subset_span hz }
  have hfin : ∀ g : GfC V, (g : GA D V) ∈ Mon := by
    rintro g _ ⟨Φ, hΦ, y, rfl⟩
    refine Submodule.subset_span ⟨finPartDSSm M hU g Φ, N.apply_mem_toSubmodule g hΦ, y, rfl⟩
  have hinf : ∀ w x, embW V w x ∈ Mon := by
    intro w x
    obtain ⟨τ, rfl⟩ := (placeOf_bijective D).2 w
    rintro _ ⟨Φ, hΦ, y, rfl⟩
    refine Submodule.subset_span ⟨Φ, hΦ, Function.update y τ (dsRep M τ x (y τ)), ?_⟩
    exact (((Φ : homDS M π ⊤).2).2 τ x y).symm
  haveI : Submodule.IsFullLattice D.host.E (stdLattice D.host.E V.rank) := isLattice_stdLattice
  have htop : Mon = ⊤ := GlobalTheory.PlaceGen.eq_top_of_local D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) Mon ∅
    (fun v x => hfin (locFin V v x)) hinf (fun k hk => hfin ⟨k, (mem_levelOff.1 hk).1⟩)
  have hinvW : ∀ g, ∀ v ∈ W, π g v ∈ W := fun g v hv =>
    (Submodule.span_le.2 (show g ∈ Mon from htop ▸ trivial)) hv
  have hsub := isSubrep_topologicalClosure (π := π) hinvW
  rcases hπ.irred.2 _ hsub with h | h
  · exfalso
    obtain ⟨Φ, hΦ, hΦ0⟩ : ∃ Φ ∈ N.toSubmodule, Φ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hN (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun Φ hΦ => (Submodule.mem_bot ℂ).2 (hc Φ hΦ)))
    have : ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) ≠ 0 := by
      intro e
      exact hΦ0 (Subtype.ext (Subtype.ext e))
    obtain ⟨y, hy⟩ : ∃ y, ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact this (ContinuousMultilinearMap.ext hc)
    have hmem : ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y ∈ W.topologicalClosure :=
      W.le_topologicalClosure (Submodule.subset_span ⟨Φ, hΦ, y, rfl⟩)
    rw [h] at hmem
    exact hy ((Submodule.mem_bot ℂ).1 hmem)
  · exact h

end GlobalTheory.TrFinDense
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory.FixedSpan

section General

variable {ι G H : Type} {Γ Hs : ι → Type} [Group G] [∀ i, Group (Γ i)] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
  {p : ∀ i, G →* Γ i} {δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i)} {ξ : ∀ i, Hs i} {π : G →* (H →L[ℂ] H)}
  {B : (∀ i, Hs i) → H}

theorem mem_closure_span_of_orthogonal [DecidableEq ι] [CompleteSpace H] (h : IsRestrTensor p δ ξ π B)
    (U : ∀ i, Submodule ℂ (Hs i)) [∀ i, (U i).HasOrthogonalProjection] (hξ : ∀ᶠ i in cofinite, ξ i ∈ U i) (x : H)
    (hx : ∀ z, Restr ξ z → ∀ i, ∀ w ∈ (U i)ᗮ, ⟪x, B (Function.update z i w)⟫_ℂ = 0) :
    x ∈ (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ i, y i ∈ U i) ∧ z = B y}).topologicalClosure := by
  set Y := (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ i, y i ∈ U i) ∧ z = B y}).topologicalClosure with hY
  haveI : CompleteSpace Y := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨a, ha, u, hu, rfl⟩ := Y.exists_add_mem_mem_orthogonal x
  have h1 : ∀ z, Restr ξ z → ∀ i, ∀ w ∈ (U i)ᗮ, ⟪a, B (Function.update z i w)⟫_ℂ = 0 := fun z hz i w hw => by
    have : Y ≤ (ℂ ∙ B (Function.update z i w))ᗮ :=
      Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 (by
        rintro _ ⟨y, hy, hyU, rfl⟩
        refine Submodule.mem_orthogonal_singleton_iff_inner_left.2 ?_
        rw [h.inner_update hz hy, Submodule.inner_right_of_mem_orthogonal (hyU i) hw, zero_mul]))
        (Submodule.isClosed_orthogonal _)
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (this ha)
  have h2 : ∀ z, Restr ξ z → ∀ i, ∀ w ∈ (U i)ᗮ, ⟪u, B (Function.update z i w)⟫_ℂ = 0 := fun z hz i w hw => by
    have := hx z hz i w hw
    rwa [inner_add_left, h1 z hz i w hw, zero_add] at this
  have h3 : ∀ s : Finset ι, ∀ y, Restr ξ y → (∀ i ∉ s, y i ∈ U i) → ⟪u, B y⟫_ℂ = 0 := fun s => by
    induction s using Finset.induction_on with
    | empty =>
      intro y hy hyU
      exact Submodule.inner_left_of_mem_orthogonal (K := Y)
        (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, hy, fun i => hyU i (by simp), rfl⟩)) hu
    | insert i s hi ih =>
      intro y hy hyU
      obtain ⟨b, hb, c, hc, e⟩ := (U i).exists_add_mem_mem_orthogonal (y i)
      have e1 : B y = B (Function.update y i b) + B (Function.update y i c) := by
        have := h.pure_update hy i 1 b c
        rwa [one_smul, one_smul, ← e, Function.update_eq_self] at this
      rw [e1, inner_add_right, h2 y hy i c hc, add_zero]
      refine ih _ (SmallThetaModules.restr_update hy i b) fun j hj => ?_
      by_cases hji : j = i
      · subst hji; rwa [Function.update_self]
      · rw [Function.update_of_ne hji]
        exact hyU j (by simp [hji, hj])
  have h4 : u = 0 := h.ext fun y hy => by
    have hf : ({i | y i ≠ ξ i} ∪ {i | ξ i ∈ U i}ᶜ).Finite := Set.Finite.union hy hξ
    rw [inner_zero_right, inner_eq_zero_symm]
    refine h3 hf.toFinset y hy fun i hi => ?_
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff, not_or, not_not] at hi
    exact hi.1 ▸ hi.2
  rwa [h4, add_zero]

theorem exists_update_clm [DecidableEq ι] (h : IsRestrTensor p δ ξ π B) {y : ∀ i, Hs i} (hy : Restr ξ y) (v : ι) :
    ∃ T : Hs v →L[ℂ] H, ∀ w, T w = B (Function.update y v w) := by
  have hr := SmallThetaModules.restr_update hy v
  have h0 : B (Function.update y v 0) = 0 := h.ext fun z hz => by simp [h.inner_update hy hz]
  let T : Hs v →ₗ[ℂ] H :=
    { toFun := fun x => B (Function.update y v x)
      map_add' := fun a b => by simpa using h.pure_update hy v 1 a b
      map_smul' := fun c a => by simpa [h0] using h.pure_update hy v c a 0 }
  have hT : ∀ x, ‖T x‖ ≤ √‖∏ᶠ (u) (_ : u ≠ v), ⟪y u, y u⟫_ℂ‖ * ‖x‖ := fun x => by
    have e := h.inner_update hy (hr x) v x
    rw [Function.update_self, finprod_congr fun u => finprod_congr fun hu : u ≠ v => by
      rw [Function.update_of_ne hu]] at e
    have e' := congrArg norm e
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e'
    refine le_of_sq_le_sq (le_of_eq ?_) (by positivity)
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _), mul_comm]
    simpa [T] using e'
  exact ⟨T.mkContinuous _ hT, fun _ => rfl⟩

end General

def fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X] (ρ : G →* (X →L[ℂ] X))
    (K : Subgroup G) : Submodule ℂ X := ⨅ k ∈ K, LinearMap.ker ((ρ k - 1 : X →L[ℂ] X) : X →ₗ[ℂ] X)

theorem mem_fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ρ : G →* (X →L[ℂ] X)}
    {K : Subgroup G} {x : X} : x ∈ fixedSub ρ K ↔ ∀ k ∈ K, ρ k x = x := by
  simp [fixedSub, sub_eq_zero]

theorem isClosed_fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (ρ : G →* (X →L[ℂ] X)) (K : Subgroup G) : IsClosed (fixedSub ρ K : Set X) := by
  have : (fixedSub ρ K : Set X) = ⋂ k ∈ K, {x | ρ k x = x} := by
    ext x; simp [mem_fixedSub]
  rw [this]
  exact isClosed_biInter fun k _ => isClosed_eq (ρ k).continuous continuous_id

theorem inner_eq_zero_of_fixed {Γ X H : Type} [Group Γ] [TopologicalSpace Γ] [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : Γ →* (X →L[ℂ] X)} (hρ : IsUnitaryRep ρ) {τ : Γ → (H →L[ℂ] H)}
    (hτ : ∀ g a b, ⟪τ g a, τ g b⟫_ℂ = ⟪a, b⟫_ℂ) (T : X →L[ℂ] H) (hT : ∀ g w, T (ρ g w) = τ g (T w))
    {K : Subgroup Γ} {x : H} (hx : ∀ k ∈ K, τ k x = x) {w : X} (hw : w ∈ (fixedSub ρ K)ᗮ) : ⟪x, T w⟫_ℂ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left]
  refine Submodule.inner_right_of_mem_orthogonal (mem_fixedSub.2 fun k hk => ext_inner_right ℂ fun z => ?_) hw
  obtain ⟨z, rfl⟩ : ∃ z', z = ρ k z' := ⟨ρ k⁻¹ z, by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]⟩
  rw [inner_map_map hρ, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hT]
  conv_rhs => rw [← hx k hk, hτ]

theorem mem_closure_span_fixed : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GAd σ J →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (R : ∀ v, IrrU (GPl σ J v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H), IsFactorisation σ J (fun v => (R v).π) ξ π B → ∀ (Kp : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GLoc σ J v)), (∀ᶠ v in cofinite, ∀ k ∈ Kp v, (R (.inr v)).π k (ξ (.inr v)) = ξ (.inr v)) → ∀ x : H, (∀ v, ∀ k ∈ Kp v, π (emb σ J v k) x = x) → x ∈ (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ v, ∀ k ∈ Kp v, (R (.inr v)).π k (y (.inr v)) = y (.inr v)) ∧ z = B y}).topologicalClosure := by
  intro F E _ _ _ _ _ σ n J H _ _ π hπ R ξ B h Kp hξ x hx
  classical
  haveI := hπ.complete
  haveI := fun v => (R v).isIrr.complete
  let K : ∀ v, Subgroup (GPl σ J v) := fun v => match v with
    | .inl _ => ⊥
    | .inr v => Kp v
  haveI : ∀ v, CompleteSpace (fixedSub (R v).π (K v)) := fun v => (isClosed_fixedSub _ _).completeSpace_coe
  have hK : ∀ y : ∀ v, (R v).H, ∀ w, y (.inl w) ∈ fixedSub (R (.inl w)).π (K (.inl w)) := fun y w =>
    mem_fixedSub.2 fun k hk => by
      rw [Subgroup.mem_bot.1 hk, map_one, ContinuousLinearMap.one_apply]
  have key := mem_closure_span_of_orthogonal h (fun v => fixedSub (R v).π (K v)) ?_ x ?_
  · refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_) key
    rintro _ ⟨y, hy, hyU, rfl⟩
    exact ⟨y, hy, fun v => mem_fixedSub.1 (hyU (.inr v)), rfl⟩
  · refine (Set.Finite.image Sum.inr hξ).subset ?_
    rintro (w | v) hv
    · exact absurd (hK ξ w) hv
    · exact ⟨v, fun e => hv (mem_fixedSub.2 e), rfl⟩
  · intro z hz v w hw
    obtain ⟨T, hT⟩ := exists_update_clm h hz v
    rw [← hT]
    refine inner_eq_zero_of_fixed (R v).isIrr.unitary (τ := fun g => π (embPl σ J v g))
      (fun g a b => inner_map_map hπ.unitary _ a b) T (fun g a => ?_) (K := K v) ?_ hw
    · rw [hT, hT, h.apply_embPl (SmallThetaModules.restr_update hz v a), Function.update_self, Function.update_idem]
    · rcases v with v | v
      · intro k hk
        rw [Subgroup.mem_bot.1 hk, map_one, map_one, ContinuousLinearMap.one_apply]
      · exact hx v

end GlobalTheory.FixedSpan
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrAct


open Classical in
noncomputable def partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) : GA D V :=
  ofInf D.sp.cm.sig V.gram (embArchPi D.sp.cm.sig V.gram fun w =>
    if w ∈ s.image (placeOf D) then projArch D.sp.cm.sig V.gram w g else 1)

open Classical in
theorem projArch_partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) (w : InfinitePlace D.host.F) :
    projArch D.sp.cm.sig V.gram w (partAt V g s) =
      if w ∈ s.image (placeOf D) then projArch D.sp.cm.sig V.gram w g else 1 := by
  rw [partAt, projArch_ofInf, projInfArch_embArchPi]

theorem proj_partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    proj D.sp.cm.sig V.gram v (partAt V g s) = 1 := by
  rw [partAt, proj_ofInf]

open Classical in
theorem partAt_insert {D : D7} (V : HSp D) (g : GA D V) {s : Finset D.what₂.Tau} {τ : D.what₂.Tau} (hτ : τ ∉ s) :
    partAt V g (insert τ s) =
      embW V (placeOf D τ) (projArch D.sp.cm.sig V.gram (placeOf D τ) g) * partAt V g s := by
  refine GAd_ext D.sp.cm.sig V.gram (fun w => ?_) (fun v => ?_)
  · rw [map_mul, projArch_partAt, projArch_partAt]
    by_cases hw : w = placeOf D τ
    · subst hw
      have h1 : placeOf D τ ∈ (insert τ s).image (placeOf D) := Finset.mem_image_of_mem _ (Finset.mem_insert_self τ s)
      have h2 : placeOf D τ ∉ s.image (placeOf D) := fun h => by
        obtain ⟨ρ, hρ, e⟩ := Finset.mem_image.1 h
        exact hτ ((placeOf_bijective D).1 e ▸ hρ)
      rw [if_pos h1, if_neg h2, mul_one]
      exact (projArch_embArch_self _ _ _ _).symm
    · rw [projArch_embArch_ne _ _ hw, one_mul]
      congr 1
      simp only [Finset.image_insert, Finset.mem_insert, hw, false_or]
  · rw [map_mul, proj_partAt, proj_partAt, proj_embArch, one_mul]

theorem partAt_univ {D : D7} (V : HSp D) (g : GA D V) [Fintype D.what₂.Tau] :
    partAt V g Finset.univ = (toInf V g : GA D V) := by
  classical
  refine GAd_ext D.sp.cm.sig V.gram (fun w => ?_) (fun v => ?_)
  · rw [projArch_partAt, if_pos]
    · show _ = projArch D.sp.cm.sig V.gram w (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g))
      rw [projArch_ofInf, projInfArch_projInf]
    · obtain ⟨τ, rfl⟩ := (placeOf_bijective D).2 w
      exact Finset.mem_image_of_mem _ (Finset.mem_univ τ)
  · rw [proj_partAt]
    show _ = proj D.sp.cm.sig V.gram v (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g))
    rw [proj_ofInf]

end GlobalTheory.TrAct


open GlobalTheory.TrAct in
theorem GlobalTheory.TrAct.toInf_apply_homDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H), ∀ Φ ∈ homDS M ρ U, ∀ (g : GA D V) y, ρ (toInf V g : GA D V) (Φ y) = Φ fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) := by
  intro D V S M H _ _ _ ρ U Φ hΦ g y
  classical
  haveI : Finite D.what₂.Tau := Finite.of_injective _ (placeOf_bijective D).1
  haveI : Fintype D.what₂.Tau := Fintype.ofFinite _
  have key : ∀ s : Finset D.what₂.Tau, ρ (partAt V g s) (Φ y) = Φ fun τ =>
      if τ ∈ s then dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) else y τ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : partAt V g ∅ = 1 := by
        rw [partAt]
        have : (fun w => if w ∈ (∅ : Finset D.what₂.Tau).image (placeOf D) then
            projArch D.sp.cm.sig V.gram w g else (1 : GArch D.sp.cm.sig V.gram w)) = 1 := by
          funext w; simp
        rw [this, map_one, map_one]
      simp [this]
    | insert τ s hτ ih =>
      rw [partAt_insert V g hτ, map_mul, ContinuousLinearMap.mul_apply, ih, ← (mem_homPi.1 hΦ).2 τ]
      congr 1
      funext τ'
      by_cases e : τ' = τ
      · subst e
        simp [hτ]
      · rw [Function.update_of_ne e]
        simp [e]
  have := key Finset.univ
  rw [partAt_univ] at this
  simpa using this
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.TrIdem

def normInd {G : Type} [MeasurableSpace G] (μ : Measure G) (H : Set G) : G → ℂ :=
  (μ.real H : ℂ)⁻¹ • H.indicator 1

variable {D : D7} {V : HSp D}

def kerSub (T : TypeDataG V) (v : T.S) : Subgroup (GLoc D.sp.cm.sig V.gram v) :=
  ((T.frame v).red.ker).map (Kv V v).subtype

def levelFam (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v) :=
  Function.update (fun v => if hv : v ∈ T.S then kerSub T ⟨v, hv⟩ else Kv V v) U.u U.frame.iwahori

def fam (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ :=
  fun v => if hv : v ∈ T.S ∧ v ∈ A then T.idem μf ⟨v, hv.1⟩ else normInd (μf v) (levelFam T U v : Set _)

variable (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
  (A : Finset (HeightOneSpectrum (𝓞 D.host.F)))

theorem levelFam_u : levelFam T U U.u = U.frame.iwahori := Function.update_self ..

theorem levelFam_of_mem (hu : U.u ∉ T.S) (v : T.S) : levelFam T U v = kerSub T v := by
  have : (v : HeightOneSpectrum (𝓞 D.host.F)) ≠ U.u := fun e => hu (e ▸ v.2)
  rw [levelFam, Function.update_of_ne this, dif_pos v.2]

theorem levelFam_of_notMem {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ T.S) (hu : v ≠ U.u) :
    levelFam T U v = Kv V v := by
  rw [levelFam, Function.update_of_ne hu, dif_neg hv]

theorem fam_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ T.S) (hA : v ∈ A) :
    fam T U μf A v = T.idem μf ⟨v, hv⟩ := dif_pos ⟨hv, hA⟩

theorem fam_of_not {v : HeightOneSpectrum (𝓞 D.host.F)} (h : ¬ (v ∈ T.S ∧ v ∈ A)) :
    fam T U μf A v = normInd (μf v) (levelFam T U v : Set _) := dif_neg h

end GlobalTheory.TrIdem
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PlaceAwayRed

theorem redFn_conj_locFin_eq_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (a : GfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) (PP : Pl D.host.E), (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v → ∀ k : Gv V v, finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β → redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = 1 := by
  intro D V β a v PP hPP k hS
  refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
  rw [Finset.mem_singleton] at hu
  subst hu
  have e : proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (embV V v k) = 1 := proj_emb_ne _ _ hPP k
  show proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ((a : GA D V) * (locFin V v k : GA D V) * ((a⁻¹ : GfC V) : GA D V)) = 1
  rw [coe_locFin, MonoidHom.map_mul, MonoidHom.map_mul, e, mul_one, ← MonoidHom.map_mul, ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, MonoidHom.map_one]

end GlobalTheory.PlaceAwayRed

end
end
