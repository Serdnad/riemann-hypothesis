module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiAlgUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CLocConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle066
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle069
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuSign
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PairJAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsUnramifiedAtTotallyRealOfInertiaLeRestrictionR
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle070
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway

@[expose] public section

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem sk_hecke {A M ι ι₀ : Type} [CommRing A] [AddCommGroup M] [Module A M] (Y Y₀ : Submodule A M)
    (op : ι → Module.End A M) (op₀ : ι₀ → Module.End A M) [h : Fact (CommOn Y op)] [h₀ : Fact (CommOn Y₀ op₀)] (j : ι → ι₀)
    (hop : ∀ i, op i = op₀ (j i)) (hm : ∀ f, f ∈ Y ↔ f ∈ Y₀) :
    ∃ φ : heckeAlg Y op →ₐ[A] heckeAlg Y₀ op₀, (∀ i, φ (heckeGen Y op i) = heckeGen Y₀ op₀ (j i)) ∧
      ∀ (t : heckeAlg Y op) (y : Y) (y₀ : Y₀), y.1 = y₀.1 →
        ((t : Module.End A Y) y).1 = ((φ t : Module.End A Y₀) y₀).1 := by
  have hle : Y₀ ≤ Y := fun f hf => (hm f).2 hf
  obtain ⟨φ, h1, h2⟩ := levelUR2HeckeMap A M M ι₀ ι Y₀ Y op₀ op (Submodule.inclusion hle) j
    (Submodule.inclusion_injective hle) fun i y => by
      rw [hop]
      rfl
  refine ⟨φ, h1, fun t y y₀ e => ?_⟩
  have e' : y = Submodule.inclusion hle y₀ := Subtype.ext e
  rw [e', ← h2]
  rfl
private theorem sk_bot {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y Y₀ : Submodule A M}
    (hm : ∀ f, f ∈ Y ↔ f ∈ Y₀) : Y = ⊥ ↔ Y₀ = ⊥ := by
  rw [Submodule.ext hm]
private theorem sk_zero {A M R : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y Y₀ : Submodule A M}
    (hY : Y = ⊥) (ν : R → Y → M) (hν : ∀ t, ν t 0 = 0) (μ : Module.End A Y₀) (t : R) (y : Y) (y₀ : Y₀) (e : y.1 = y₀.1) :
    ν t y = (μ y₀).1 := by
  have h : y = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hY _ y.2)
  have h₀ : y₀ = 0 := Subtype.ext (e.symm.trans (congrArg Subtype.val h))
  rw [h, h₀, hν, map_zero]
  rfl
private theorem sk_comp {O : Type} [CommRing O] {R R₀ T T₀ : Type} [CommRing R] [Algebra O R] [CommRing R₀] [Algebra O R₀]
    [CommRing T] [Algebra O T] [CommRing T₀] [Algebra O T₀] (f : R →ₐ[O] T) (f₀ : R₀ →ₐ[O] T₀) (β : R →ₐ[O] R₀)
    (Φ : T →ₐ[O] T₀) (φ : T →+* T₀) (hφ : ∀ x, Φ x = φ x) {n : ℕ} {G G₀ V : Type} {Γ : V → Type} [Group G] [Group G₀]
    [∀ v, Group (Γ v)] (p : G →* G₀) (D : W.GDet n R G) (ψ : ∀ v, Fin n → Γ v →* Rˣ)
    (D₀ : W.GDet n R₀ G₀) (ψ₀ : ∀ v, Fin n → Γ v →* R₀ˣ)
    (hD : D.map β.toRingHom = D₀.comap p) (hψ : ∀ v i, W.pushCh β.toRingHom (ψ v i) = ψ₀ v i)
    (hu : ∀ f g : R →ₐ[O] T₀, D.map f.toRingHom = D.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g)
    (h : (D.map f.toRingHom).map φ = (D₀.map f₀.toRingHom).comap p ∧
      ∀ v i, W.pushCh φ (W.pushCh f.toRingHom (ψ v i)) = W.pushCh f₀.toRingHom (ψ₀ v i)) (t : R) :
    φ (f t) = f₀ (β t) := by
  obtain rfl : φ = Φ.toRingHom := RingHom.ext fun x => (hφ x).symm
  have e : Φ.comp f = f₀.comp β := by
    refine hu _ _ ?_ fun v i => ?_
    · have e1 : D.map (Φ.comp f).toRingHom = (D.map f.toRingHom).map Φ.toRingHom := ((CA.d_gmap D).2.1 _ _).symm
      have e2 : D.map (f₀.comp β).toRingHom = (D.map β.toRingHom).map f₀.toRingHom := ((CA.d_gmap D).2.1 _ _).symm
      rw [e1, e2, h.1, hD]
      rfl
    · have e := h.2 v i
      rw [← hψ] at e
      exact e
  exact DFunLike.congr_fun e t

theorem UpperTheory.V.Hi.levelUR2SmulKey_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q₀ τ₀).X.I.T →* Aˣ), (hset Q₀ τ₀).IsWt θ →  ∀ (a : (hset Q₀ τ₀).Op → c.O) (K₀ : (hset Q₀ τ₀).Lev) (K : (hset Q τ₀).Lev), ∀ (p : V.frame.G₀ →* V₀.frame.G₀), Continuous p → Function.Surjective p → (∀ g, p (V.pr g) = V₀.pr g) → ∀ j : (hset Q τ₀).Op → (hset Q₀ τ₀).Op, (∀ x : Vl l L × Fin n, j (.inr x) = .inr x) → (∀ (w : (hset Q τ₀).Wp) (k : Fin n), ∃ hw, j (.inl (w, k)) = .inl (⟨w.1, hw⟩, k)) → ∀ (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O), (hset Q τ₀).IsWt θ' → @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ → (∀ i, a' i = a (j i)) → (∀ i, (hset Q τ₀).op A i = (hset Q₀ τ₀).op A (j i)) → (∀ f : (hset Q₀ τ₀).X.Fn A m, f ∈ (hset Q τ₀).MK θ' a' K ↔ f ∈ (hset Q₀ τ₀).MK θ a K₀) → ∀ (R₀ R : Type) [CommRing R₀] [Algebra c.O R₀] [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R₀ V₀.frame.G₀) (ψ₀ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* R₀ˣ) (D : W.GDet n R V.frame.G₀) (ψ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* Rˣ) (β : R →ₐ[c.O] R₀), D.map β.toRingHom = D₀.comap p → (∀ v i, W.pushCh β.toRingHom (ψ v i) = ψ₀ v i) → (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D.map f.toRingHom = D.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g) → ∀ μ : R₀ →+* Module.End A ((hset Q₀ τ₀).MK θ a K₀), ((hset Q₀ τ₀).MK θ a K₀ = ⊥ ∨ ∃ (_ : Fact (CommOn ((hset Q₀ τ₀).MK θ a K₀) ((hset Q₀ τ₀).op A))) (_ : Alg.IsCO c.O ((hset Q₀ τ₀).TK θ a K₀)) (f : R₀ →ₐ[c.O] (hset Q₀ τ₀).TK θ a K₀), (hset Q₀ τ₀).IsMap θ a K₀ D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A ((hset Q₀ τ₀).MK θ a K₀))) → ∀ ν : R → (hset Q τ₀).MK θ' a' K → (hset Q₀ τ₀).X.Fn A m, (∀ t, ν t 0 = 0) → (∀ [Fact (CommOn ((hset Q τ₀).MK θ' a' K) ((hset Q τ₀).op A))] [Alg.IsCO c.O ((hset Q τ₀).TK θ' a' K)], ∃ f : R →ₐ[c.O] (hset Q τ₀).TK θ' a' K, (hset Q τ₀).IsMap θ' a' K D ψ f ∧ ∀ t y, ν t y = ((f t : Module.End A ((hset Q τ₀).MK θ' a' K)) y).1) → ∀ t (y : (hset Q τ₀).MK θ' a' K) (y₀ : (hset Q₀ τ₀).MK θ a K₀), y.1 = y₀.1 → ν t y = (μ (β t) y₀).1 := by
  intro hN l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c m τ₀ A _ _ _ θ hθ a K₀ K p hp hps hpr j hj1 hj2 θ' a' hθ' hθθ ha hop hm
    R₀ R _ _ _ _ D₀ ψ₀ D ψ β hD hψ hu μ hμ ν hν0 hν t y y₀ hy
  by_cases hne : (hset Q τ₀).MK θ' a' K = ⊥
  · exact sk_zero hne ν hν0 (μ (β t)) t y y₀ hy
  have hAx := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c m τ₀
  haveI hF : Fact (CommOn ((hset Q τ₀).MK θ' a' K) ((hset Q τ₀).op A)) :=
    ⟨((hiComm L Ω l n c _ hAx A θ' hθ' K).2.2.2 a').1⟩
  obtain ⟨hCO, -⟩ := hiAlg L Ω l n c _ hAx A θ' hθ' a' K hne
  obtain ⟨f, hf, hνf⟩ := hν
  obtain ⟨hF₀, hCO₀, f₀, hf₀, hμf⟩ := hμ.resolve_left fun h => hne ((sk_bot hm).2 h)
  obtain ⟨φ, hg, hφ⟩ : ∃ φ : (hset Q τ₀).TK θ' a' K →ₐ[A] (hset Q₀ τ₀).TK θ a K₀,
      (∀ i, φ ((hset Q τ₀).gen θ' a' K i) = (hset Q₀ τ₀).gen θ a K₀ (j i)) ∧
      ∀ (t : (hset Q τ₀).TK θ' a' K) (y : (hset Q τ₀).MK θ' a' K) (y₀ : (hset Q₀ τ₀).MK θ a K₀), y.1 = y₀.1 →
        ((t : Module.End A ((hset Q τ₀).MK θ' a' K)) y).1 = ((φ t : Module.End A ((hset Q₀ τ₀).MK θ a K₀)) y₀).1 :=
    sk_hecke _ _ _ _ (h := hF) (h₀ := hF₀) j hop hm
  have hB := _root_.UpperTheory.V.Hi.levelUR2BaseEq_alt hN l L Ω s n hn V₀ V Q₀ Q c m τ₀ A θ hθ a K₀ K p hp hps hpr j hj1 hj2 θ' a' hθ' hθθ ha
    _ _ hf₀ _ _ hf φ hg
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (hset Q τ₀).TK θ' a' K →ₐ[c.O] (hset Q₀ τ₀).TK θ a K₀, ∀ x, Φ x = φ x :=
    ⟨φ.restrictScalars c.O, fun _ => rfl⟩
  have e := sk_comp f f₀ β Φ φ.toRingHom hΦ p D ψ D₀ ψ₀ hD hψ (hu _) hB t
  refine (hνf t y).trans ((hφ (f t) y y₀ hy).trans ?_)
  exact congrArg (fun u : Module.End A ((hset Q₀ τ₀).MK θ a K₀) => (u y₀).1)
    ((congrArg Subtype.val e).trans (hμf (β t)).symm)
end
end

section




section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Alg
open Matrix
end Alg
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
theorem automorphic_of_gsp4_rigid_solvable_galois (H : _root_.UpperTheory.V.Af.HypothesesH') (K L : IntermediateField ℚ Ω) [NumberField K] [NumberField L] [IsCMField K] [IsCMField L]
    (hle : K ≤ L) (hK : Module.finrank ℚ K = 2) (hgal : IsGalois ℚ L) (hsol : IsSolvable (L ≃ₐ[ℚ] L)) (ι : Qbar l ≃+* ℂ)
    (r : G ℚ Ω →* M4 (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ) (hr : Continuous r.toHomUnits) (hθ : Af.IsAlgChar ι θ)
    (hm : ∀ g, IsGSp (θ g : Qbar l) (r g)) (cc : G ℚ Ω) (hc : Af.IsConjEl cc) (hirr : Af.IsIrr (r.toHomUnits.comp (resQ L)))
    (haut : Af.IsAut ι (r.toHomUnits.comp (resQ K))) : Af.IsAut ι (r.toHomUnits.comp (resQ L)) := by
  letI : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[ℚ] L) := hsol
  have s2 : IsSolvable (L ≃ₐ[K] L) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom ℚ : (L ≃ₐ[K] L) →* (L ≃ₐ[ℚ] L)))
      (AlgEquiv.restrictScalars_injective ℚ)
  obtain ⟨P, hP⟩ := auPair r θ hm cc
  have hp : Af.IsPairing cc (r.toHomUnits.comp (Af.resG ℚ K Ω)) (θ.comp (Af.resG ℚ K Ω)) P := fun s s' h => by
    have h' : Af.resG ℚ K Ω s' = cc * Af.resG ℚ K Ω s * cc⁻¹ := h
    have h1 := hP (Af.resG ℚ K Ω s)
    rw [← h'] at h1
    exact h1
  exact (Z.Bc.solQ (_root_.UpperTheory.V.Z.Bc.solC_alt H H.cyc) ℚ K L Ω s2 ⟨inferInstance, Or.inr ⟨hK, inferInstance⟩⟩
    inferInstance inferInstance l ι 4 (by norm_num) (r.toHomUnits.comp (Af.resG ℚ K Ω)) θ
    (hr.comp (Af.continuous_restrictScalarsHom ℚ K Ω)) hirr hθ (auSign _) ⟨cc, _, hc, hp⟩).1 haut
end Gal
section Core
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end Core
section Rg
open scoped Matrix TensorProduct
section BK
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
end BK
end Rg
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem au_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)
private theorem au_isTeich {l : ℕ} [hl : Fact l.Prime] {F : W.GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  obtain ⟨τ, hτ⟩ := au_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩⟩
  rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
private theorem au_open {G O : Type} [Group G] [TopologicalSpace G] [CommRing O] {m : ℕ} (f : O →+* ℂ) (hf : Function.Injective f)
    (τ : G →* GL (Fin m) O) (h : IsOpen (((Matrix.GeneralLinearGroup.map f).comp τ).ker : Set G)) : IsOpen (τ.ker : Set G) := by
  have : ((Matrix.GeneralLinearGroup.map f).comp τ).ker = τ.ker := by
    refine MonoidHom.ker_comp_of_injective _ _ fun a b hab => ?_
    ext i j
    exact hf (congrArg (fun x : GL (Fin m) ℂ => (x : Matrix (Fin m) (Fin m) ℂ) i j) hab)
  rwa [this] at h
theorem UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ →
    (hset Q τ₀).AutomorphicHeckeSet ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι) := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  obtain ⟨t, ht⟩ := au_isTeich c r
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) :=
    au_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine SetLike.le_def.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  · obtain ⟨Y, hY, hPU, -⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt hP l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
    rw [← hY]
    exact le_iSup (fun Y : {Y : (hset Q τ₀).PartAltAlt ι lam ξ // _root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι lam Y.r} => Y.1.Y) ⟨Y, hPU⟩
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Hi.nonempty_unitaryHeckeData :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ Λ : LamObj r, Nonempty (_root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) := by
  intro P l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι Λ
  obtain ⟨m, τ₀, hτ⟩ := _root_.UpperTheory.V.Hi.exists_integral_type_for_residual_rep P l L Ω s n hn V Q c r ι
  obtain ⟨θ, hθ, hw⟩ := _root_.UpperTheory.V.Hi.exists_theta_is_weight_of_lam_obj P.litN l L Ω s n hn V Q c m τ₀ r Λ
  obtain ⟨a, ha⟩ := _root_.UpperTheory.V.Hi.exists_is_res_of_residual_rep_and_type P.litN l L Ω s n hn V Q c m τ₀ r
  exact ⟨⟨m, τ₀, hτ, θ, hθ, hw, a, ha⟩⟩
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
namespace UpperTheory.Gal.projectedFormsSystemPart
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : Plc F} {τ : SmIrr (GLw n w)} {B : Multiset ℂˣ}
end
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem part2 (H : _root_.UpperTheory.V.Af.HypothesesH') {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {ι : Qbar l ≃+* ℂ}
    {ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)} (hρ : Continuous ρ) {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ)
    (hLG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      _root_.UpperTheory.V.Z.Win.LocGlobT ι (ρ.comp V.pr) w τ) (hi : Af.IsIrr (ρ.comp V.pr)) :
    ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (ρ.comp V.pr) π ∧
      (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
        π.IsLocComp w τ ↔ IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  have hc : Continuous (ρ.comp V.pr) := hρ.comp (V.pr_cont W.continuous_resP)
  have hoff : ∀ᶠ w : Plc L in Filter.cofinite, ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 L)} ≠ 0 := by
      simp [(Fact.out : l.Prime).ne_zero]
    exact (Ideal.finite_factors h0).subset fun w hw => Ideal.dvd_span_singleton.mpr (not_not.mp hw)
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.link2_alt H L Ω (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) l s.odd ι n hn σ hσ _ hc hi
    (hoff.mono fun w hw hsp τ hτ B hB => _root_.UpperTheory.Gal.projectedFormsSystemPart.frobLG'_alt H.toClassicalTheorems hc hw hB (hLG w hsp τ hτ))
theorem autUO_of_printsH : _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Z.Ord.AutUOAlt := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  have hTeich : ∃ t, r.IsTeich t := by
    obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    have : CharP (ResidueField c.O) l := by
      refine (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 ?_
      rw [← map_natCast (residue c.O), residue_eq_zero_iff]
      exact hlm
    have : CharP (c.O ⧸ maximalIdeal c.O) l := inferInstanceAs (CharP (ResidueField c.O) l)
    have : PerfectRing (ResidueField c.O) l := inferInstance
    let lift := Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)
    let j := lift (RingHom.id (ResidueField c.O))
    let τ := (Perfection.teichmuller l (maximalIdeal c.O)).comp j.toMonoidHom
    have hres (x : ResidueField c.O) : residue c.O (τ x) = x :=
      (Perfection.mk_teichmuller (j x)).trans
        (RingHom.congr_fun (lift.symm_apply_apply (RingHom.id (ResidueField c.O))) x)
    refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hres _, ?_⟩⟩
    rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  obtain ⟨t, ht⟩ := hTeich
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) := by
    let f := ι.toRingHom.comp (algebraMap c.O (Qbar l))
    have hf : Function.Injective f := ι.injective.comp Subtype.val_injective
    have hmap : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin m) f) := by
      intro A B hAB
      apply Units.ext
      apply Matrix.ext
      intro i j
      exact hf (congrArg (fun M : GL (Fin m) ℂ => (M : Matrix (Fin m) (Fin m) ℂ) i j) hAB)
    rw [← MonoidHom.ker_comp_of_injective τ₀ _ hmap]
    exact (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine IsConcreteLE.le_iff.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨Y, hY, -, hcomp, hLG⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt H l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
  rw [← hY]
  refine le_iSup (fun Y : {Y : (hset Q τ₀).PartAltAlt ι lam ξ // Af.IsIrr (Y.r.comp V.pr) → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧
    GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (Y.r.comp V.pr) π ∧ ∀ v, π.IsLocComp ((hset Q τ₀).Sl v) (Y.σl v)} => Y.1.Y) ⟨Y, fun hi => ?_⟩
  obtain ⟨π, p1, p2, p3, -, p5⟩ := part2 H s hn Y.cont σ.2 hLG hi
  refine ⟨π, p1, p2, p3, fun v => ?_⟩
  have hsplit : IsSplitAt (s.w v.1) :=
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v.1) (s.split _ (Or.inl v.2)) _
      (HeightOneSpectrum.ext (Ideal.ext fun x =>
        (show _ ↔ _ from (s.hw v.1) (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v.1 x)))
  exact (p5 _ hsplit _).2 (hcomp v)
end UpperTheory.Gal.projectedFormsSystemPart
end
end
