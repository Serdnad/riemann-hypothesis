module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Formalism.AlgebraicWeights.IsAlgWeight
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle798
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSubgroupOfTrivOutsideOfLocalPoints
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle269
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle299
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle792
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocProj

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → Function.Injective T → (∀ a, T a ∈ π.S) → (∀ x : GAf L n, TrivOutside {s.v} (x : GA L n) → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)) → ∀ f ∈ π.S, f ≠ 0 → ∃ p : (GAf L n → ℂ) →ₗ[ℂ] τ.V, p f ≠ 0 ∧ ∀ x : GAf L n, TrivOutside {s.v} (x : GA L n) → ∀ f' ∈ π.S, p (NG.rt L n x f') = τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) (p f') := by
  intro L _ _ _ n π s τ i T hi hic hT hTS hTeq f hf hf0
  classical
  obtain ⟨hdec, hcomm, huniq⟩ := GlobalTheory.SplitAdelic.main L n s
  choose lift hlift using fun A => (huniq A).exists
  have hlu : ∀ A x, TrivOutside {s.v} x → s.loc n x = A → x = lift A := fun A x hx e =>
    (huniq A).unique ⟨hx, e⟩ (hlift A)
  have tmul : ∀ {x y : GAf L n}, TrivOutside {s.v} x → TrivOutside {s.v} y → TrivOutside {s.v} (x * y) := by
    intro x y hx hy v hv
    show ((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
    rw [Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, mul_one]
  have tone : TrivOutside {s.v} (1 : GAf L n) := by
    intro v _
    show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
    rw [Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let lh : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := lift
      map_one' := (hlu _ _ tone (map_one _)).symm
      map_mul' := fun A B => (hlu _ _ (tmul (hlift A).1 (hlift B).1)
        (by rw [map_mul, (hlift A).2, (hlift B).2])).symm }
  have hlh : ∀ x, TrivOutside {s.v} x → lh (s.loc n x) = x := fun x hx => (hlu _ x hx rfl).symm
  let ρ : Representation ℂ (GAf L n) π.S :=
    { toFun := fun g => (NG.rt L n g).restrict (fun f hf => π.stable g f hf)
      map_one' := by
        apply LinearMap.ext; intro f; apply Subtype.ext; funext x
        simp [NG.rt]
      map_mul' := fun a b => by
        apply LinearMap.ext; intro f; apply Subtype.ext; funext x
        simp [NG.rt, mul_assoc] }
  have hρ : ∀ g (f : π.S), ((ρ g f : π.S) : GAf L n → ℂ) = NG.rt L n g f := fun _ _ => rfl
  have hρirr : ρ.IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun P => ?_ }
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne
      have h1 : (⟨g, hg⟩ : π.S) ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
      rw [← h] at h1
      exact hg0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h1))
    · have hle : P.toSubmodule.map π.S.subtype ≤ π.S := by
        rintro _ ⟨p, -, rfl⟩
        exact p.2
      have hst : ∀ h, ∀ g ∈ P.toSubmodule.map π.S.subtype, NG.rt L n h g ∈ P.toSubmodule.map π.S.subtype := by
        rintro h _ ⟨p, hp, rfl⟩
        exact ⟨ρ h p, P.apply_mem_toSubmodule h hp, rfl⟩
      rcases π.irr _ hle hst with h | h
      · left
        apply Subrepresentation.ext
        show P.toSubmodule = ⊥
        rw [eq_bot_iff]
        intro p hp
        have : (p : GAf L n → ℂ) ∈ P.toSubmodule.map π.S.subtype := ⟨p, hp, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
      · right
        apply Subrepresentation.ext
        show P.toSubmodule = ⊤
        rw [eq_top_iff]
        intro p _
        have : (p : GAf L n → ℂ) ∈ P.toSubmodule.map π.S.subtype := by rw [h]; exact p.2
        obtain ⟨q, hq, e'⟩ := this
        rwa [show q = p from Subtype.ext e'] at hq
  let mi : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map i.toRingHom
  have hmi : ∀ B, mi (Matrix.GeneralLinearGroup.map i.symm.toRingHom B) = B := fun B =>
    Units.ext (Matrix.ext fun a b => i.apply_symm_apply _)
  let σ : Representation ℂ (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) τ.V := τ.ρ.comp mi
  have hσirr : σ.IsIrreducible := by
    have hτ := τ.irr
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun P => ?_ }
    · obtain ⟨P1, P2, hne⟩ := hτ.exists_pair_ne
      apply hne
      have e1 : P1 = ⊥ ∨ P1 = ⊤ := hτ.eq_bot_or_eq_top P1
      have e2 : P2 = ⊥ ∨ P2 = ⊤ := hτ.eq_bot_or_eq_top P2
      have htop : (⊥ : Subrepresentation τ.ρ) = ⊤ := by
        apply Subrepresentation.ext
        have h' := congrArg Subrepresentation.toSubmodule h
        exact h'
      rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl <;> simp [htop]
    · let P' : Subrepresentation τ.ρ := ⟨P.toSubmodule, fun g v hv => by
        have := P.apply_mem_toSubmodule (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) hv
        change τ.ρ (mi _) v ∈ P.toSubmodule at this
        rwa [hmi] at this⟩
      rcases hτ.eq_bot_or_eq_top P' with h | h
      · left; apply Subrepresentation.ext; have h' := congrArg Subrepresentation.toSubmodule h; exact h'
      · right; apply Subrepresentation.ext; have h' := congrArg Subrepresentation.toSubmodule h; exact h'
  have hV : ∃ a : τ.V, a ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨P1, P2, hne⟩ := τ.irr.exists_pair_ne
    apply hne
    apply Subrepresentation.ext
    ext a
    simp [hcon a, P1.toSubmodule.zero_mem, P2.toSubmodule.zero_mem]
  let f0 : σ.IntertwiningMap (ρ.comp lh) :=
    { toLinearMap := LinearMap.codRestrict π.S T hTS
      isIntertwining' := fun A => by
        apply LinearMap.ext; intro a; apply Subtype.ext
        show T (τ.ρ (mi A) a) = NG.rt L n (lh A) (T a)
        have := hTeq (lh A) (hlift A).1 a
        rwa [show s.loc n (lh A) = A from (hlift A).2] at this }
  have hf0' : f0 ≠ 0 := by
    obtain ⟨a, ha⟩ := hV
    intro h
    apply ha
    apply hT
    have : (f0 a : GAf L n → ℂ) = 0 := by rw [h]; rfl
    simpa [f0] using this
  have hc : ∀ g, ∃ u, ∀ y, Commute ((lh u)⁻¹ * g) (lh y) := by
    intro g
    obtain ⟨x, y', hx, hy', rfl⟩ := hdec g
    refine ⟨s.loc n x, fun y => ?_⟩
    rw [hlh x hx, inv_mul_cancel_left]
    exact (hcomm _ _ (hlift y).1 hy').symm
  have hU : ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ _ W'), σ'.IsIrreducible →
      ∀ f' : σ'.IntertwiningMap (ρ.comp lh), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
    intro W' _ _ σ' hσ' f' hf'
    exact (GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ W' ρ lh σ σ' hρirr hσirr hσ' hc f0 hf0').2 f' hf'
  have hsum := (GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ τ.V ρ lh σ σ hρirr hσirr hσirr hc f0 hf0').1
  have hfne : (⟨f, hf⟩ : π.S) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  obtain ⟨p0, hp0⟩ := GlobalTheory.T.exists_intertwiningMap_ne_zero_of_isotypic_irreducible _ _ _ (ρ.comp lh) σ hσirr hsum hU ⟨f, hf⟩ hfne
  obtain ⟨p, hp⟩ := LinearMap.exists_extend p0.toLinearMap
  have hpS : ∀ g (hg : g ∈ π.S), p g = p0 ⟨g, hg⟩ := fun g hg => by
    have := LinearMap.congr_fun hp ⟨g, hg⟩
    exact this
  refine ⟨p, by rw [hpS f hf]; exact hp0, fun x hx f' hf' => ?_⟩
  rw [hpS _ (π.stable x f' hf'), hpS f' hf']
  have e1 : (⟨NG.rt L n x f', π.stable x f' hf'⟩ : π.S) = (ρ.comp lh) (s.loc n x) ⟨f', hf'⟩ := by
    apply Subtype.ext
    show NG.rt L n x f' = NG.rt L n (lh (s.loc n x)) f'
    rw [hlh x hx]
  rw [e1]
  exact LinearMap.congr_fun (p0.isIntertwining' (s.loc n x)) ⟨f', hf'⟩

end GlobalTheory.LocProj
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.splitPlace_component_unitaryAdelic_determined : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) (x y : GAf L n), s.loc n x = s.loc n y → (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) := by
  first | exact @GlobalTheory.SplitCompat.compAt_map_eq_of_loc_eq | exact GlobalTheory.SplitCompat.compAt_map_eq_of_loc_eq | (intros; apply GlobalTheory.SplitCompat.compAt_map_eq_of_loc_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.mem_subgroup_of_trivOutside_of_local_points : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (K : Subgroup (GAf L n)) (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) (y : GAf L n), TrivOutside (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) y → (∀ v ∈ T, ∃ p ∈ K, TrivOutside {v} p ∧ (p.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v)) → y ∈ K := by
  first | exact @GlobalTheory.TrivOutsideGen.mem_of_trivOutside_of_local | exact GlobalTheory.TrivOutsideGen.mem_of_trivOutside_of_local | (intros; apply GlobalTheory.TrivOutsideGen.mem_of_trivOutside_of_local <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjPlaceDual

theorem conjPl_symm (D : D7) {w w' : PlE D.host} (h : IsConjPl D.host w w') : IsConjPl D.host w' w := by
  intro x y hy
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := by
    rw [hy, GlobalTheory.SplitPlaceOver.host_conj_eq', GlobalTheory.SplitPlaceOver.host_conj_eq', IsCMField.complexConj_apply_apply]
  exact (h y x hx).symm

end GlobalTheory.ConjPlaceDual
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem isotIn_detect_by_eqv_map : ∀ (D : D7) {n : ℕ} (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (π : NG.FinTyp D.host.E n) (y : A), y ∈ principalLevelFrame.isotIn ρ C π → y ≠ 0 → ∃ q : A →ₗ[ℂ] (GAf D.host.E n → ℂ), q y ≠ 0 ∧ ∀ z ∈ principalLevelFrame.isotIn ρ C π, q z ∈ π.S ∧ ∀ h, q (ρ h z) = NG.rt D.host.E n h (q z) := by
  intro D n A _ _ ρ C π y hy hy0
  let St : Submodule ℂ A → Prop := fun K => ∀ h, ∀ x ∈ K, ρ h x ∈ K
  have rangeSt : ∀ Φ : π.S →ₗ[ℂ] A, principalLevelFrame.IsEqvA ρ π Φ → St (LinearMap.range Φ) := by
    rintro Φ hΦ h _ ⟨f, rfl⟩
    exact ⟨_, hΦ h f⟩
  have rangeLe : ∀ Φ : π.S →ₗ[ℂ] A, principalLevelFrame.IsEqvA ρ π Φ → LinearMap.range Φ ≤ C →
      LinearMap.range Φ ≤ principalLevelFrame.isotIn (D := D) ρ C π := fun Φ hΦ hC =>
    le_iSup₂ (f := fun (Ψ : π.S →ₗ[ℂ] A) (_ : principalLevelFrame.IsEqvA ρ π Ψ ∧ LinearMap.range Ψ ≤ C) => LinearMap.range Ψ) Φ ⟨hΦ, hC⟩
  have supSt : ∀ K1 K2 : Submodule ℂ A, St K1 → St K2 → St (K1 ⊔ K2) := by
    intro K1 K2 h1 h2 h x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]; exact Submodule.add_mem_sup (h1 h a ha) (h2 h b hb)
  have atom : ∀ K : Submodule ℂ A, St K → ∀ Φ : π.S →ₗ[ℂ] A, principalLevelFrame.IsEqvA ρ π Φ →
      LinearMap.range Φ ≤ K ∨ ∀ f, Φ f ∈ K → f = 0 := by
    intro K hK Φ hΦ
    rcases π.irr ((K.comap Φ).map π.S.subtype) (by
        rintro _ ⟨f, -, rfl⟩; exact f.2)
      (by
        rintro h _ ⟨f, hf, rfl⟩
        refine ⟨⟨NG.rt D.host.E n h f, π.stable h f f.2⟩, ?_, rfl⟩
        show Φ _ ∈ K
        rw [hΦ h f]; exact hK h _ hf) with h0 | h1
    · right; intro f hf
      have : (f : GAf D.host.E n → ℂ) ∈ (K.comap Φ).map π.S.subtype := ⟨f, hf, rfl⟩
      rw [h0] at this
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    · left; rintro _ ⟨f, rfl⟩
      have : (f : GAf D.host.E n → ℂ) ∈ (K.comap Φ).map π.S.subtype := by rw [h1]; exact f.2
      obtain ⟨f', hf', he⟩ := this
      have : f' = f := Subtype.ext he
      subst this; exact hf'
  obtain ⟨K, hKmax⟩ := zorn_le₀ {K : Submodule ℂ A | K ≤ principalLevelFrame.isotIn (D := D) ρ C π ∧ St K ∧ y ∉ K} (by
    intro c hc hch
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ⟨bot_le, fun h x hx => ?_, fun h => hy0 ((Submodule.mem_bot ℂ).1 h)⟩, by simp⟩
      rw [(Submodule.mem_bot ℂ).1 hx, map_zero]; exact zero_mem _
    · refine ⟨sSup c, ⟨sSup_le fun K hK => (hc hK).1, ?_, ?_⟩, fun K hK => le_sSup hK⟩
      · intro h x hx
        have : sSup c ≤ (sSup c).comap (ρ h) := sSup_le fun K hK z hz => le_sSup hK ((hc hK).2.1 h z hz)
        exact this hx
      · intro hyc
        obtain ⟨K, hK, hyK⟩ := (Submodule.mem_sSup_of_directed hne hch.directedOn).1 hyc
        exact (hc hK).2.2 hyK)
  obtain ⟨⟨hKN, hKSt, hyK⟩, hKm⟩ := hKmax
  have grow : ∀ K' : Submodule ℂ A, K' ≤ principalLevelFrame.isotIn (D := D) ρ C π → St K' → K ≤ K' → ¬ K' ≤ K → y ∈ K' :=
    fun K' h1 h2 h3 h4 => by
      by_contra hyK'; exact h4 (hKm ⟨h1, h2, hyK'⟩ h3)
  obtain ⟨Φ, ⟨hΦ, hΦC⟩, hΦK⟩ : ∃ Φ : π.S →ₗ[ℂ] A, (principalLevelFrame.IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) ∧
      ¬ LinearMap.range Φ ≤ K := by
    by_contra hcon
    push_neg at hcon
    exact hyK ((iSup₂_le fun Φ hΦ => hcon Φ hΦ : principalLevelFrame.isotIn (D := D) ρ C π ≤ K) hy)
  have hΦK' : ∀ f, Φ f ∈ K → f = 0 := (atom K hKSt Φ hΦ).resolve_left hΦK
  have hyK2 : y ∈ K ⊔ LinearMap.range Φ := grow _ (sup_le hKN (rangeLe Φ hΦ hΦC))
    (supSt _ _ hKSt (rangeSt Φ hΦ)) le_sup_left (fun h => hΦK (le_sup_right.trans h))
  have hN2 : principalLevelFrame.isotIn (D := D) ρ C π ≤ K ⊔ LinearMap.range Φ := by
    refine iSup₂_le fun Φ' hΦ' => ?_
    by_contra hnot
    have h3 := (atom _ (supSt _ _ hKSt (rangeSt Φ hΦ)) Φ' hΦ'.1).resolve_left hnot
    have hyK3 : y ∈ K ⊔ LinearMap.range Φ' := grow _ (sup_le hKN (rangeLe Φ' hΦ'.1 hΦ'.2))
      (supSt _ _ hKSt (rangeSt Φ' hΦ'.1)) le_sup_left
      (fun h => hnot ((le_sup_right.trans h).trans le_sup_left))
    obtain ⟨k, hk, _, ⟨f', rfl⟩, hsum⟩ := Submodule.mem_sup.1 hyK3
    have hf' : f' = 0 := h3 f' (by
      have : Φ' f' = y - k := by rw [← hsum]; abel
      rw [this]; exact Submodule.sub_mem _ hyK2 (Submodule.mem_sup_left hk))
    apply hyK; rw [← hsum, hf', map_zero, add_zero]; exact hk
  let Ψ : (K × π.S) →ₗ[ℂ] A := K.subtype.coprod Φ
  have hΨ : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨k, f⟩ h0
    simp only [Ψ, LinearMap.coprod_apply, Submodule.subtype_apply] at h0
    have hneg : Φ f = -(k : A) := eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h0)
    have hf : f = 0 := hΦK' f (by rw [hneg]; exact K.neg_mem k.2)
    subst hf
    rw [map_zero, add_zero] at h0
    have hk : k = 0 := Subtype.ext h0
    subst hk; rfl
  let E := LinearEquiv.ofInjective Ψ hΨ
  let q0 : LinearMap.range Ψ →ₗ[ℂ] π.S := (LinearMap.snd ℂ K π.S).comp E.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend q0
  have hq0 : ∀ (k : K) (f : π.S), g (k + Φ f) = f := by
    intro k f
    have hmem : (k : A) + Φ f ∈ LinearMap.range Ψ := ⟨(k, f), rfl⟩
    have h1 := LinearMap.congr_fun hg ⟨_, hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    have h2 : (⟨_, hmem⟩ : LinearMap.range Ψ) = E (k, f) := Subtype.ext (by simp only [E, LinearEquiv.ofInjective_apply]; rfl)
    show (E.symm _).2 = f
    rw [h2, LinearEquiv.symm_apply_apply]
  have dec : ∀ z ∈ principalLevelFrame.isotIn (D := D) ρ C π, ∃ (k : K) (f : π.S), z = k + Φ f := by
    intro z hz
    obtain ⟨a, ha, _, ⟨f, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (hN2 hz)
    exact ⟨⟨a, ha⟩, f, rfl⟩
  refine ⟨π.S.subtype ∘ₗ g, ?_, ?_⟩
  · obtain ⟨k, f, rfl⟩ := dec y hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hq0]
    intro hf
    have : f = 0 := Subtype.ext hf
    subst this
    apply hyK; rw [map_zero, add_zero]; exact k.2
  · intro z hz
    obtain ⟨k, f, rfl⟩ := dec z hz
    refine ⟨by simp [hq0], fun h => ?_⟩
    have : ρ h ((k : A) + Φ f) = ((⟨ρ h k, hKSt h k k.2⟩ : K) : A) + Φ ⟨NG.rt D.host.E n h f, π.stable h f f.2⟩ := by
      rw [map_add (f := _), hΦ h f]
    have e1 := hq0 ⟨ρ h k, hKSt h k k.2⟩ ⟨NG.rt D.host.E n h f, π.stable h f f.2⟩
    have e2 := hq0 k f
    rw [this, LinearMap.comp_apply, LinearMap.comp_apply, e1, e2]
    rfl

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp
open GlobalTheory.Grow
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.AdjUnfold



theorem integral_val_thF_eq : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) (u : (R.HV i t).H), ∫ g in R.fdW i, star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g ∂(R.νW i) = ∫ h in R.fdV i t, ⟪upVec R i t v b y h, R.extV i t u h⟫_ℂ ∂(R.νV i t) := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t v n b y u
  have hm := hL.models
  have hθ : IsInfFam R.θ := hm.inf
  have hω := hL.thP.ωP i t
  have hpt := hL.thP.pt_theta i t
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  have hHV : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfdV : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := (hm.νV i t).2
  have hHW : (R.νW i).IsHaarMeasure := (hm.νW i).1.1
  have hfdW : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := (hm.νW i).2
  have hJt : ∀ k, IsThetaFunO R.ψ (Vc D i) (Wc D i) (jointVec R i t v (b k)) := fun k => hpt _
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ u)
  have hFc : Continuous (R.extV i t u) :=
    GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx
  have hFi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t u (γ * h) = R.extV i t u h :=
    GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hGk : ∀ k, RapidDec (Vc D i) (fun h => ⟪R.extV i t u h, b k⟫_ℂ) := fun k =>
    RapidDec.of_isCompact (fun γ hγ h => by simp only [hFi γ hγ h]) (hFc.inner continuous_const) hK
      (fun g => by
        obtain ⟨γ, hγ, c', hc', e⟩ := hKc g
        exact ⟨γ⁻¹, inv_mem hγ, by rw [e, inv_mul_cancel_left]; exact hc'⟩)
  obtain ⟨-, hr, -⟩ := hm.HW i (sg0 D A)
  have hTm : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e y) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ y
      exact this)
  have hF : RapidDec (Wc D i) (fun g => starRingEnd ℂ (val R i v y g)) :=
    (rapidDec_of_cuspForm hP hθ (hTm.aut fun ρ => v ρ) (hTm.cusp fun ρ => v ρ)).conj
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin n → GA D (Wc D i) → GA D (Vc D i) → ℂ, Φ = fun k g h =>
      thetaKO (R.ωP i t) h g (jointVec R i t v (b k)) * starRingEnd ℂ (val R i v y g) *
        starRingEnd ℂ ⟪R.extV i t u h, b k⟫_ℂ := ⟨_, rfl⟩
  have hint : ∀ k, Integrable (Function.uncurry (Φ k))
      (((R.νW i).restrict (R.fdW i)).prod ((R.νV i t).restrict (R.fdV i t))) := fun k => by
    rw [hΦ]
    exact GlobalTheory.ChainOnto.ThetaSwap.integrable_prod hθ hω (hJt k) hHV hfdV hHW hfdW (hGk k) hF
  have hthF : ∀ g, R.thF i t u (fun ρ => v ρ) g = ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) ∂(R.νV i t) :=
    fun g => (hL.thP.thF i t).elim fun _ h => (congrFun (h.2 u v) g).trans
      (h.1.eq ((R.extV i t).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g)
  have hexp : ∀ g h, thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) =
      ∑ k, ⟪b k, R.extV i t u h⟫_ℂ * thetaKO (R.ωP i t) h g (jointVec R i t v (b k)) := by
    intro g h
    have e : (R.cV i).ext ((R.HV i t).e u) h = ∑ k, ⟪b k, R.extV i t u h⟫_ℂ • b k := (b.sum_repr' _).symm

    rw [e, map_sum]
    unfold jointVec RealDat.ptP

    simp only [map_sum, map_smul, thetaKO, LinearMap.sum_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  have hL1 : ∀ᵐ g ∂((R.νW i).restrict (R.fdW i)), star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g =
      ∑ k, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) := by
    have hae : ∀ᵐ g ∂((R.νW i).restrict (R.fdW i)), ∀ k,
        Integrable (fun h => Φ k g h) ((R.νV i t).restrict (R.fdV i t)) :=
      ae_all_iff.2 fun k => (hint k).prod_right_ae
    filter_upwards [hae] with g hg
    rw [hthF g, ← integral_const_mul]
    have e : ∀ h, star (val R i v y g) * thetaKO (R.ωP i t) h g
        (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) = ∑ k, Φ k g h := by
      intro h
      rw [hexp g h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hΦ, inner_conj_symm, Complex.star_def]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact integral_finsetSum _ fun k _ => hg k
  have hR : ∀ h, ⟪upVec R i t v b y h, R.extV i t u h⟫_ℂ = ∑ k, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) := by
    intro h
    simp only [upVec, sum_inner, inner_smul_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hΦ, upLift]
    rw [integral_mul_const, ← integral_conj, inner_conj_symm]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, Complex.star_def, Complex.conj_conj]
  calc ∫ g in R.fdW i, star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g ∂(R.νW i)
      = ∫ g in R.fdW i, ∑ k, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) ∂(R.νW i) := integral_congr_ae hL1
    _ = ∑ k, ∫ g in R.fdW i, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) ∂(R.νW i) :=
        integral_finsetSum _ fun k _ => (hint k).integral_prod_left
    _ = ∑ k, ∫ h in R.fdV i t, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) ∂(R.νV i t) :=
        Finset.sum_congr rfl fun k _ => integral_integral_swap (hint k)
    _ = ∫ h in R.fdV i t, ∑ k, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) ∂(R.νV i t) :=
        (integral_finsetSum _ fun k _ => (hint k).integral_prod_right).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun h => (hR h).symm)

end GlobalTheory.AdjUnfold
end
end
