module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle068
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle066
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle474
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ConjTorusSubApply
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle001
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem fd_fixed {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) : FiniteDimensional ℂ (fixed π (KOne k (Fin N))) := by
  refine (UpperTheory.Zero.LLC.Pr.adm k N V π hs hi).2 (KOne k (Fin N)) ?_ ?_
  · rw [← levelPre_bot]
    exact isOpen_levelPre _
  · rw [← levelPre_bot]
    exact isCompact_levelPre _

private theorem isCl_trace {G : Type} [Group G] {r : ℕ} (η : Representation ℂ G (Fin r → ℂ)) :
    IsCl (fun g => LinearMap.trace ℂ (Fin r → ℂ) (η g)) := by
  intro x y
  show LinearMap.trace ℂ _ (η (y⁻¹ * x * y)) = LinearMap.trace ℂ _ (η x)
  rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem frob_step (hF : FrobL) {F : Type} [Field F] [Finite F] {s : ℕ} {d : Fin s → ℕ} {N : ℕ}
    (hd : ∑ i, d i = N) (Y : ∀ i, GL (Fin (d i)) F → ℂ) {r : ℕ}
    (η : Representation ℂ (GL (Fin N) F) (Fin r → ℂ))
    (h : ∑ᶠ g, star (hcL (List.ofFn fun i => ⟨d i, Y i⟩) N g) * LinearMap.trace ℂ (Fin r → ℂ) (η g) ≠ 0) :
    ∑ᶠ p : parab F (stdBlocks d hd), star (∏ i, Y i (leviProj F (stdBlocks d hd) p i)) *
      LinearMap.trace ℂ (Fin r → ℂ) (η p) ≠ 0 := by
  obtain ⟨c, hc, hcY⟩ := hF F s d N hd
  intro h0
  apply h
  rw [hcY Y (fun g => LinearMap.trace ℂ (Fin r → ℂ) (η g)) (isCl_trace η), h0, mul_zero]

private theorem meets_parab (hT : TensTr) {F : Type} [Field F] {s : ℕ} {d : Fin s → ℕ} {N : ℕ}
    (hd : ∑ i, d i = N) {W : Fin s → Type} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]
    [∀ a, FiniteDimensional ℂ (W a)] (σ : ∀ a, Representation ℂ (GL (Fin (d a)) F) (W a))
    (Y : ∀ i, GL (Fin (d i)) F → ℂ) (hY : ∀ a γ, LinearMap.trace ℂ (W a) (σ a γ) = Y a γ) {r : ℕ}
    (η : Representation ℂ (GL (Fin N) F) (Fin r → ℂ))
    (h : ∑ᶠ p : parab F (stdBlocks d hd), star (∏ i, Y i (leviProj F (stdBlocks d hd) p i)) *
      LinearMap.trace ℂ (Fin r → ℂ) (η p) ≠ 0) :
    Meets (η.comp (parab F (stdBlocks d hd)).subtype)
      (fun p => LinearMap.trace ℂ _ (((piTensor σ).comp (leviProj F (stdBlocks d hd))) p)) := by
  have key : ∀ p : parab F (stdBlocks d hd),
      LinearMap.trace ℂ (PiTensorProduct ℂ fun a => W a) (piTensor σ (leviProj F (stdBlocks d hd) p)) =
        ∏ i, Y i (leviProj F (stdBlocks d hd) p i) := by
    intro p
    rw [(hT s _ W σ).2]
    exact Finset.prod_congr rfl fun a _ => hY a _
  unfold Meets
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, key]
  exact h

private theorem compose_map {G X U U' : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] {ρ : Representation ℂ G U} {ρ' : Representation ℂ G U'}
    {η : Representation ℂ G X} (Ψ : X →ₗ[ℂ] U) (f : ρ.IntertwiningMap ρ') (hf : Function.Injective f)
    (hΨ0 : Ψ ≠ 0) (hΨ : ∀ g x, Ψ (η g x) = ρ g (Ψ x)) :
    ∃ F : X →ₗ[ℂ] U', F ≠ 0 ∧ ∀ g x, F (η g x) = ρ' g (F x) := by
  refine ⟨f.toLinearMap ∘ₗ Ψ, ?_, ?_⟩
  · intro h0
    apply hΨ0
    refine LinearMap.ext fun x => hf ?_
    have := LinearMap.congr_fun h0 x
    simpa using this
  · intro g x
    have := LinearMap.congr_fun (f.isIntertwining' g) (Ψ x)
    simpa [hΨ] using this

theorem UpperTheory.Gal.InertialTypesAlt.lblFull :
    MeetsIff → FrobL → JDEq → TensTr → AvgMap → IndMap → TensInc → UpperTheory.Gal.InertialTypesAlt.LblFull := by
  intro hMI hF hJD hTT hAvg hInd hTI
  intro k _ _ _ _ _ θ N V _ _ π hs hi s x c hd hE hx T hT hP
  obtain ⟨e⟩ := hE
  obtain ⟨r, η, hη⟩ := hT
  have hTη : T = fun g => LinearMap.trace ℂ (Fin r → ℂ) (η g) := by
    funext g
    rw [hη g]
    rfl
  subst hTη
  have hJ : J θ (List.ofFn fun a => ((x a).fst, c a)) N =
      hcL (List.ofFn fun i => (⟨(x i).fst, cusp θ (x i).fst (c i)⟩ : (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N := by
    rw [← JD_nil, (hJD 𝓀[k] θ).1]
    simp [List.map_ofFn, Function.comp_def]
  have h1 : ∑ᶠ g, star (hcL (List.ofFn fun i => (⟨(x i).fst, cusp θ (x i).fst (c i)⟩ :
      (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N g) * LinearMap.trace ℂ (Fin r → ℂ) (η g) ≠ 0 := by
    rw [← hJ]
    exact hP
  have h2 := frob_step hF (d := fun a => (x a).fst) hd (fun i => cusp θ (x i).fst (c i)) η h1
  haveI hfd : ∀ a, FiniteDimensional ℂ (fixed (x a).rep (KOne k (Fin (x a).fst))) :=
    fun a => fd_fixed _ (x a).snd.rep.smooth (x a).snd.rep.irr
  have h3 := meets_parab hTT hd (fun a => levelZero (x a).rep) (fun i => cusp θ (x i).fst (c i)) hx η h2
  haveI := (hTT s _ _ (fun a => levelZero (x a).rep)).1
  obtain ⟨ψ, hψ0, hψ⟩ := ((hMI _ _ _ _ _).1).1 h3
  obtain ⟨j, hj, hjx⟩ := hTI k s (fun a => (x a).fst) _ (fun a => (x a).rep)
  obtain ⟨Φ, ev, hΦ1, hΦ2, hΦ3⟩ := hInd k N s (fun a => (x a).fst) hd _ _ _ _ j hj hjx
  obtain ⟨Ψ, hΨ0, hΨ⟩ := hAvg _ (parab 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)) _ _ _ _ _ _ η Φ ev ψ
    hΦ1 hΦ2 hΦ3 hψ hψ0
  have hinj : Function.Injective (levelZeroMap e.symm.toIntertwiningMap) := by
    apply levelZeroMap_injective
    intro a b hab
    have := congrArg e hab
    simpa using this
  obtain ⟨F', hF0, hF'⟩ := compose_map Ψ (levelZeroMap e.symm.toIntertwiningMap) hinj hΨ0 hΨ
  haveI := fd_fixed π hs hi
  exact ((hMI _ _ _ (levelZero π) η).2).2 ⟨F', hF0, hF'⟩
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.unlFull :
    UnlFull := by
  intro k _ _ _ _ _ N V _ _ π s x hd hs hu
  have hmem : ∀ a, x a ∈ Finset.univ.val.map x := fun a =>
    Multiset.mem_map_of_mem x (Finset.mem_univ_val a)
  have hx : ∀ a, (x a).IsCusp := fun a => hs.isCusp (hmem a)
  have hP : (prodIrr x hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k s N (fun a => Segment.single (x a) (hx a)) x hd
      (fun a b => GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx a) (hx b) (hu _ (hmem b) _ (hmem a))
        (hu _ (hmem a) _ (hmem b)))
      (fun a => (single_spec (hx a)).2.1)
  have h1 := GlobalTheory.LocGL.SupportPerm.isSubquotient_prodIrr_of_hasSupport
    UpperTheory.Zero.LLC.Pr.zel UpperTheory.Zero.LLC.Pr.bz k N s ⟨V, π, hs.isSmooth, hs.isIrreducible⟩ x hd hs
  haveI := GlobalTheory.ReducedFactor.nontrivial_of_irr hs.isIrreducible
  have equiv_of_sub {G A B : Type} [Group G] [AddCommGroup A] [Module ℂ A]
      [AddCommGroup B] [Module ℂ B] {σ : Representation ℂ G B}
      {ρ : Representation ℂ G A} (h : IsSubquotient σ ρ) [Nontrivial B]
      (hirr : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
    obtain ⟨S, f, hf⟩ := h
    obtain ⟨y, hy⟩ := exists_ne (0 : B)
    obtain ⟨v, rfl⟩ := hf y
    haveI : IsSimpleOrder (Subrepresentation ρ) := hirr
    rcases eq_bot_or_eq_top S with rfl | rfl
    · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
    let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
    refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
    rcases eq_bot_or_eq_top F.ker with h | h
    · have : x ∈ F.ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ F.ker := by rw [h]; trivial
      exact absurd this hy
  obtain ⟨E⟩ := equiv_of_sub h1 hP
  exact ⟨E.symm⟩
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem redK_mem_unipRad {s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {g : GL (Fin n) k}
    (hu : g ∈ unipRad k e) (hK : g ∈ KO k (Fin n)) : redK k (Fin n) ⟨g, hK⟩ ∈ unipRad 𝓀[k] e := by
  refine CuspMax.mem_unipRad_iff_entries.2 fun i j hij => ?_
  have h := CuspMax.mem_unipRad_iff_entries.1 hu i j hij
  by_cases hh : i = j
  · subst hh
    have h1 := (redK_eq_iff ⟨g, hK⟩ i i 1).2 (by simp [h])
    simpa using h1
  · rw [Matrix.one_apply_ne hh]
    exact (redK_eq_zero_iff ⟨g, hK⟩ i j).2 (by simp [h, Matrix.one_apply_ne hh])

private theorem finCusp_levelZero {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (hc : IsCuspidal π) : PositivityTheory.Rg.DzCount.FinCusp (levelZero π) := by
  intro s d e hne v hv
  have hV : (v : V) ∈ fixed π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) := by
    refine GlobalTheory.DepthZeroJac.mem_fixed_sup v.2 (GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_)
    have h1 := congrArg Subtype.val (hv _ (redK_mem_unipRad e hg.1 hg.2))
    rwa [levelZero_apply] at h1
  have hne' : unipRad k e ≠ ⊥ := CuspMax.unipRad_ne_bot_iff.2 (CuspMax.unipRad_ne_bot_iff.1 hne)
  haveI := hc.2 s d e hne'
  exact Subtype.ext (GlobalTheory.DepthZeroJac.depthZeroJacquetInjective k n s d e ⟨V, π, hs, hi⟩ (v : V) hV (Subsingleton.elim _ _))

private theorem irreducible_levelZero (π : IrrRep (GL (Fin n) k)) (ω : kˣ →* ℂˣ) (hω : HasCentralChar π.ρ ω)
    (hF : PositivityTheory.Rg.DzCount.FinCusp (levelZero π.ρ)) (hD : fixed π.ρ (KOne k (Fin n)) ≠ ⊥) :
    (levelZero π.ρ).IsIrreducible := by
  have key : ∀ W : Subrepresentation (levelZero π.ρ), W ≠ ⊥ → W = ⊤ := by
    intro W hW
    haveI : Nontrivial W.toSubmodule := by
      rw [Submodule.nontrivial_iff_ne_bot]
      intro h
      exact hW (Subrepresentation.toSubmodule_injective h)
    let j : W.toSubmodule →ₗ[ℂ] π.V := (fixed π.ρ (KOne k (Fin n))).subtype ∘ₗ W.toSubmodule.subtype
    have hFτ : PositivityTheory.Rg.DzCount.FinCusp W.toRepresentation := by
      intro s d e hne w hw
      exact Subtype.ext (hF s d e hne w (fun u hu => congrArg Subtype.val (hw u hu)))
    have hj : PositivityTheory.Rg.DzCount.IsTypeMap W.toRepresentation π.ρ j := by
      refine ⟨?_, ?_⟩
      · intro a c hac
        exact Subtype.ext (Subtype.ext hac)
      · intro g w
        exact levelZero_apply π.ρ g w
    have hfix := PositivityTheory.Rg.DzCount.B.st6 k W.toSubmodule n W.toRepresentation hFτ π ω hω j hj
    apply Subrepresentation.toSubmodule_injective
    show W.toSubmodule = ⊤
    rw [eq_top_iff]
    intro v _
    have hv : (v : π.V) ∈ LinearMap.range j := hfix ▸ v.2
    obtain ⟨w, hw⟩ := hv
    have hwv : (w : fixed π.ρ (KOne k (Fin n))) = v := Subtype.ext hw
    rw [← hwv]
    exact w.2
  haveI : Nontrivial (Subrepresentation (levelZero π.ρ)) := by
    refine ⟨⟨⊥, ⊤, fun h => hD ?_⟩⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hm : (⟨v, hv⟩ : fixed π.ρ (KOne k (Fin n))) ∈ (⊤ : Subrepresentation (levelZero π.ρ)).toSubmodule :=
      Submodule.mem_top
    rw [← h'] at hm
    exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 hm)
  constructor
  intro W
  by_cases h : W = ⊥
  · exact Or.inl h
  · exact Or.inr (key W h)

end

theorem UpperTheory.Gal.InertialTypesAlt.cuspIrr :
    CuspIrr := by
  intro k _ _ _ _ _ y hc hD
  have hadm := (UpperTheory.Zero.LLC.Pr.adm k y.1 y.2.rep.V y.rep y.2.rep.smooth y.2.rep.irr).2 (levelPre ⊥)
    (isOpen_levelPre ⊥) (isCompact_levelPre ⊥)
  rw [levelPre_bot] at hadm
  obtain ⟨ω, hω⟩ := (GlobalTheory.T.centralCharacter_subquotient_productIrreducibles k).1 y
  have hF := finCusp_levelZero y.rep y.2.rep.smooth y.2.rep.irr hc.2
  exact ⟨hadm, irreducible_levelZero y.2.rep ω hω hF hD, hF⟩
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.suppStd :
    SuppStd := by
  intro k _ _ _ _ _ N V _ _ π S hS
  obtain ⟨t, x, hx, -⟩ := id hS
  have hsum := hS.sum_fst
  have hd : ∑ a, (x a).fst = N := by
    rw [← hx, Multiset.map_map] at hsum
    simpa [Finset.sum_eq_multiset_sum] using hsum
  let τ : IrrRep (GL (Fin N) k) := ⟨V, π, hS.isSmooth, hS.isIrreducible⟩
  refine ⟨t, x, hd, hx, ?_⟩
  exact SupportPerm.isSubquotient_prodIrr_of_hasSupport UpperTheory.Zero.LLC.Pr.zel UpperTheory.Zero.LLC.Pr.bz k N t τ x hd
    (hx ▸ hS)
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_block (hBC : UpperTheory.Gal.TypesAndIwahori.BlockCount) {s N : ℕ} (d c : Fin s → ℕ) (hd : ∑ a, d a = N) (y : ℂ) :
    ∏ j : Fin N, (X - C (y ^ c (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j)) : ℂ[X]) =
      ∏ a, (X - C (y ^ c a)) ^ d a := by
  show (Finset.univ.val.map fun j => (fun a => (X - C (y ^ c a) : ℂ[X])) (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j)).prod = _
  rw [hBC ℂ[X] N s d hd (fun a => X - C (y ^ c a)), Multiset.prod_sum]
  simp [Multiset.prod_replicate]

private theorem pol_top (hBC : UpperTheory.Gal.TypesAndIwahori.BlockCount) (hPT : PolTop) (b : Lbl) {s N : ℕ} (d c : Fin s → ℕ)
    (hd : ∑ a, d a = N) (hl : List.ofFn (fun a => (d a, c a)) = b.D ++ b.L) (y : ℂ) (h2 : 2 ≤ b.q)
    (h1 : ∀ p ∈ b.L, p.1 = 1) (hy : y ^ (b.q - 1) = 1) :
    ∏ j : Fin N, (X - C (y ^ c (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j)) : ℂ[X]) = b.pol b.q y := by
  rw [prod_block hBC, (hPT b y h2 h1 hy).2, ← hl, List.map_ofFn, List.prod_ofFn]
  rfl

private theorem pol_bot (hPB : PolBot) (q Q : ℕ) {s : ℕ} (m c : Fin s → ℕ) (y : ℂ) (h2 : 2 ≤ Q) (hy : y ^ (Q - 1) = 1) :
    (⟨q, [], List.ofFn fun a => (m a, c a)⟩ : Lbl).pol Q y =
      ∏ a, ∏ j ∈ Finset.range (m a), (X - C (y ^ (c a * q ^ j * ((Q - 1) / (q ^ m a - 1))))) := by
  rw [hPB q Q _ y h2 hy, List.map_ofFn, List.prod_ofFn]
  rfl

theorem UpperTheory.Gal.InertialTypesAlt.suppAny :
    (LblOn fun a => a.D = []) → LblOf → TypeOfLbl → UpperTheory.Gal.TypesAndIwahori.SuppOfType → UpperTheory.Gal.TypesAndIwahori.BlockCount → TameChars → LeTop → PolTop → PolBot → ResEmbEx → UnifTower → BaseQ → CardRes → ArtRead → CuspIne → SuppIne → SuppAny := by
  intro hOn hOf hTy hSO hBC hTC hLT hPT hPB hRE hUT hBQ hCR hAR hCI hSI
  intro E Ω _ _ _ _ _ _ n hn π Y hY A v w h h' g _ i hi hI τ τ' hτ hτ' hD f hf hs
  haveI : CharZero (v.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI : CharZero (w.adicCompletion Y.K) := charZero_of_injective_algebraMap (algebraMap Y.K _).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨⟨e, he⟩, Θ, hΘ⟩ := hRE E Ω A v h
  obtain ⟨⟨e', he'⟩, -⟩ := hRE Y.K Ω A w h'
  have eqv : τ.ρ.Equiv (IrrGL.of τ.ρ τ.smooth τ.irred).rep := IrrGL.equivOf _ _ _
  obtain ⟨𝔪, hm⟩ := UpperTheory.Zero.LLC.Pr.exh (v.adicCompletion E) (IrrGL.of τ.ρ τ.smooth τ.irred)
  have hS₀ : HasSupport (IrrGL.of τ.ρ τ.smooth τ.irred).rep (msupp 𝔪) :=
    hasSupport_msupp_of_isL UpperTheory.Zero.LLC.Pr.zel _ 𝔪 _ hm
  have hS : HasSupport τ.ρ (msupp 𝔪) := hS₀.of_equiv eqv.symm
  have hfix : fixed τ.ρ (KOne (v.adicCompletion E) (Fin n)) ≠ ⊥ := GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv eqv.symm hD
  have hθ : Inj (Θ.comp e.toMonoidHom) := fun a b ha hb hab =>
    e.injective (hΘ _ _ (by simpa using ha) (by simpa using hb) hab)
  obtain ⟨hg2, hcard, -⟩ := hBQ E v g i hi
  obtain ⟨s, x, c, hxS, hx, hlbl⟩ := hOf _ (Θ.comp e.toMonoidHom) hθ n _ τ.ρ _ hS hfix
  rw [hcard] at hlbl hx
  obtain ⟨b, hab, hb⟩ := hOn E Ω n hn (Pt.base Ω π) Y hY A Θ hΘ hI v w h h' e e' he he' τ τ' hτ hτ' _ rfl hlbl
  have hbq : b.q = g ^ f := by rw [hb.2.1, hCR, hf]
  have hb2 : 2 ≤ b.q := hb.1.1
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h0
    · simp [hbq] at hb2
    · exact h0
  have hdiv : ∀ a, (x a).1 ∣ f := fun a =>
    hs _ hS _ (by rw [← hxS]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ a))
  have hsp : (⟨g, [], List.ofFn fun a => ((x a).1, c a)⟩ : Lbl).Splits b.q := by
    refine ⟨f, hf0, hbq, fun p hp => ?_⟩
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 hp
    exact hdiv a
  obtain ⟨-, -, hL1, hblk⟩ := hLT _ b hlbl.1 hab hsp
  obtain ⟨s', d, c', hd, ω, hl, hω, hTV⟩ := hTy _ (Θ.comp e'.toMonoidHom) n _ τ'.ρ b hb hL1
  have hTS := hSO _ n s' d hd _ τ'.ρ τ'.smooth τ'.irred ω hTV
  obtain ⟨ξ, hξ, hξt, hξs, hξu⟩ := hTC _ n _ τ'.ρ _ hTS
  refine ⟨ξ, hξ, hξt, hξs, ?_⟩
  intro rc hrc a' ha' t
  have hQ : 1 ≤ normV w - 1 := by rw [hf, ← hbq]; omega
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : Ω, ϖ ^ (normV w - 1) = (g : Ω) := IsAlgClosed.exists_pow_nat_eq _ hQ
  have hg1 : ((g : ℕ) : 𝓞 Y.K) ∈ w.asIdeal := DiscreteGroups.sglob.DzType.natCast_mem_of_normV w g f hf0 hf
  have hg2' : ((g : ℕ) : 𝓞 Y.K) ∉ w.asIdeal ^ 2 := hUT E Ω n (Pt.base Ω π) Y hY A hI v w h h' g hg2
  obtain ⟨z, u, hz, hu, hres, hpow⟩ := hAR Y.K Ω A w h' g hg1 hg2' a' ha' e' he' t ϖ hϖ
  obtain ⟨y, hyd⟩ : ∃ y : ℂ, y = Θ (IsLocalRing.residue A z) := ⟨_, rfl⟩
  have hy : y ^ (g ^ f - 1) = 1 := by rw [hyd, ← map_pow, ← hf, hpow, map_one]
  have hξ' : ∀ j, ((ξ j (a' (ineIncl h' t)) : ℂˣ) : ℂ) = y ^ c' (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j) := by
    intro j
    rw [← hu, hξu, hω, hyd, ← hres]
    rfl
  let t₀ : Ine (F := E) A := ⟨AlgEquiv.restrictScalars E (t : G Y.K Ω), t.2.1, t.2.2⟩
  have hcu : ∀ a, (rc (x a)).inePol (t₀ : G E Ω) =
      ∏ j ∈ Finset.range (x a).1, (X - C (y ^ (c a * g ^ j * ((g ^ f - 1) / (g ^ (x a).1 - 1))))) := by
    intro a
    rw [hyd]
    exact hCI E Ω A v h g i hi Θ hΘ e (x a) (c a) (hx a).1 (hx a).2.1 (hx a).2.2.1 (hx a).2.2.2 rc hrc f hf0 (hdiv a)
      t₀ ϖ (hf ▸ hϖ) z hz
  have hSx : HasSupport (IrrGL.of τ.ρ τ.smooth τ.irred).rep (msupp 𝔪) := hS₀
  have h1 := hSI E Ω A v h rc hrc _ _ hSx t₀
  rw [← hxS, Multiset.map_map] at h1
  have h2 : (rc (IrrGL.of τ.ρ τ.smooth τ.irred)).inePol (t₀ : G E Ω) =
      ∏ a, ∏ j ∈ Finset.range (x a).1, (X - C (y ^ (c a * g ^ j * ((g ^ f - 1) / (g ^ (x a).1 - 1))))) := by
    rw [h1, ← Finset.prod_congr rfl fun a _ => hcu a]
    rfl
  have h3 := pol_top hBC hPT b d c' hd hl y hb2 hL1 (hbq ▸ hy)
  have h4 := pol_bot hPB g (g ^ f) (fun a => (x a).1) c y (hbq ▸ hb2) hy
  have h5 : b.pol (g ^ f) y = (⟨g, [], List.ofFn fun a => ((x a).1, c a)⟩ : Lbl).pol (g ^ f) y := by
    rw [← hbq]
    unfold Lbl.pol
    rw [hblk]
  rw [hbq, h5, h4] at h3
  simp only [hξ']
  exact h2.trans h3.symm
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem card_eq_pow_finrank {F F' : Type} [Field F] [Field F'] [Finite F'] (m : Module F F') :
    Nat.card F' = Nat.card F ^ @Module.finrank F F' _ _ m := by
  letI := m
  exact Module.natCard_eq_pow_finrank

private theorem finrank_module_unique {F F' : Type} [Field F] [Field F'] [Finite F] [Finite F'] (m₁ m₂ : Module F F') :
    @Module.finrank F F' _ _ m₁ = @Module.finrank F F' _ _ m₂ :=
  Nat.pow_right_injective (Finite.one_lt_card (α := F))
    ((card_eq_pow_finrank m₁).symm.trans (card_eq_pow_finrank m₂))

theorem UpperTheory.Gal.InertialTypesAlt.stepInert :
    FinTrace → StableOf → ResEmbCompat → ResDeg → LiftOk → JDEq → ∀ P₀, KillsOn P₀ → StepAt P₀ Not := by
  intro hFT hSt hRE hRD hLO hJD P₀ hK K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hl n hn π P hW A Θ hΘ v w hs hu e e' he he'
    τ τ' hτ hτ' a hPa hL
  obtain ⟨hOk, hq, hna, hMeets⟩ := hL
  obtain ⟨r, j, hr, hj, hje⟩ := hRE K M Ω A v w e e' he he'
  letI := r.toAlgebra
  obtain ⟨hfr, s, hsf⟩ := hRD K M hl v w hs hu
  have hfr' : @Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] _ _ Algebra.toModule = Module.finrank K M :=
    (finrank_module_unique _ _).trans hfr
  have hl' : (@Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] _ _ Algebra.toModule).Prime := by
    rw [hfr']
    exact hl
  let ι : AlgebraicClosure 𝓀[v.adicCompletion K] →ₐ[𝓀[v.adicCompletion K]] AlgebraicClosure 𝓀[w.1.adicCompletion M] :=
    { j.toRingHom with
      commutes' := fun x => by
        show j (algebraMap _ _ x) = _
        rw [hj x, IsScalarTower.algebraMap_apply 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M]
          (AlgebraicClosure 𝓀[w.1.adicCompletion M]) x]
        rfl }
  let θ' : AlgebraicClosure 𝓀[w.1.adicCompletion M] →* ℂ := Θ.comp e'.toMonoidHom
  have hθ' : Inj θ' := fun x y hx hy h =>
    e'.injective (hΘ _ _ (fun h0 => hx (e'.injective (by simpa using h0)))
      (fun h0 => hy (e'.injective (by simpa using h0))) h)
  have hpull : pullθ ι θ' = Θ.comp e.toMonoidHom := by
    ext x
    show Θ (e' (j x)) = Θ (e x)
    rw [hje]
  rw [← hpull] at hMeets
  subst hna
  have hlift := hLO a _ hl' hOk
  refine ⟨a.lift (@Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] _ _ Algebra.toModule),
    Relation.ReflTransGen.single ⟨_, hl', rfl⟩, hlift.1, ?_, hlift.2.symm, ?_⟩
  · show a.q ^ _ = _
    rw [hq]
    exact (card_eq_pow_finrank _).symm
  · intro hz
    have hf : IsCl fun g => star (JD (pullθ ι θ') a.D a.L a.rk g) := fun x y => by
      show star _ = star _
      rw [(hJD _ (pullθ ι θ')).2.2 a.D a.L a.rk x y]
    have hTr := hFT K M hl a.rk hn π P (hSt K M hl a.rk hn π P hW).1 hW v w hs hu τ τ' hτ hτ' hr s hsf _ hf hMeets
    have hstar : ∀ δ, shLift s (fun g => star (JD (pullθ ι θ') a.D a.L a.rk g)) δ =
        star (shLift s (JD (pullθ ι θ') a.D a.L a.rk) δ) := fun δ => by
      unfold shLift
      split_ifs <;> simp
    haveI : FiniteDimensional ℂ (fixed τ'.ρ (KOne (w.1.adicCompletion M) (Fin a.rk))) :=
      (UpperTheory.Zero.LLC.Pr.adm _ _ _ _ τ'.smooth τ'.irred).2 _ GlobalTheory.StepData.isOpen_KOne
        (levelPre_bot (k := w.1.adicCompletion M) (n := Fin a.rk) ▸ isCompact_levelPre ⊥)
    refine hTr ?_
    simp only [hstar]
    exact hK _ _ s hl' hsf ι θ' hθ' a hPa hOk hq _ (levelZero τ'.ρ) hz
end
