module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.HeckePolCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamFree
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
import Mathlib.RingTheory.MvPowerSeries.Rename
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem UpperTheory.V.Hi.dense_arithmetic_points {O A B T E : Type} [CommRing O] [CommRing A] [CommRing B] [CommRing T] [CommRing E]
    [Algebra O A] [Algebra O B] [Algebra O T] [Algebra O E] [Algebra A T] (lam : A →ₐ[O] B) (f : B →ₐ[O] T)
    (hf : ∀ a, f (lam a) = algebraMap A T a) (P : (A →+* E) → Prop) (G : (B →ₐ[O] E) → Prop)
    (hG : ∀ x : B →ₐ[O] E, P (x.comp lam).toRingHom → G x)
    (hsep : ∀ t : T, (∀ x : T →ₐ[O] E, P (x.toRingHom.comp (algebraMap A T)) → x t = 0) → t = 0) (b : B)
    (hb : ∀ x : B →ₐ[O] E, RingHom.ker f ≤ RingHom.ker x → G x → x b = 0) : b ∈ RingHom.ker f := by
  rw [RingHom.mem_ker]
  refine hsep (f b) fun x hx => hb (x.comp f) (fun y hy => ?_) (hG _ ?_)
  · rw [RingHom.mem_ker] at hy ⊢
    rw [AlgHom.comp_apply, hy, map_zero]
  · have e : ((x.comp f).comp lam).toRingHom = x.toRingHom.comp (algebraMap A T) :=
      RingHom.ext fun y => congrArg x (hf y)
    rw [e]
    exact hx
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.levelUR2HeckeMap :
    ∀ (A M M' ι ι' : Type) [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] (Y : Submodule A M) (Y' : Submodule A M') (op : ι → Module.End A M) (op' : ι' → Module.End A M') [Fact (CommOn Y op)] [Fact (CommOn Y' op')] (φ : Y →ₗ[A] Y') (j : ι' → ι), Function.Injective φ → (∀ i (y : Y), ((φ ((heckeGen Y op (j i) : Module.End A Y) y) : Y') : M') = op' i (φ y)) → ∃ ψ : heckeAlg Y' op' →ₐ[A] heckeAlg Y op, (∀ i, ψ (heckeGen Y' op' i) = heckeGen Y op (j i)) ∧ ∀ (t : heckeAlg Y' op') (y : Y), φ ((ψ t : Module.End A Y) y) = (t : Module.End A Y') (φ y) := by
  intro A M M' ι ι' _ _ _ _ _ Y Y' op op' _ _ φ j hφ hop
  have uniq : ∀ (t : Module.End A Y') (s s' : heckeAlg Y op),
      (∀ y : Y, φ ((s : Module.End A Y) y) = t (φ y)) → (∀ y : Y, φ ((s' : Module.End A Y) y) = t (φ y)) → s = s' := by
    intro t s s' h h'
    exact Subtype.ext (LinearMap.ext fun y => hφ ((h y).trans (h' y).symm))
  have ex : ∀ t : heckeAlg Y' op', ∃ s : heckeAlg Y op,
      ∀ y : Y, φ ((s : Module.End A Y) y) = (t : Module.End A Y') (φ y) := by
    rintro ⟨t, ht⟩
    change ∃ s : heckeAlg Y op, ∀ y : Y, φ ((s : Module.End A Y) y) = t (φ y)
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, hi⟩ := hx
      exact ⟨heckeGen Y op (j i), fun y => Subtype.ext ((hop i y).trans (hi (φ y)).symm)⟩
    | algebraMap r =>
      refine ⟨algebraMap A _ r, fun y => ?_⟩
      change φ (r • y) = r • φ y
      exact map_smul φ r y
    | add a b _ _ ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s + s', fun y => ?_⟩
      change φ ((s : Module.End A Y) y + (s' : Module.End A Y) y) = a (φ y) + b (φ y)
      rw [map_add (f := _), hs, hs']
    | mul a b _ _ ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s * s', fun y => ?_⟩
      change φ ((s : Module.End A Y) ((s' : Module.End A Y) y)) = a (b (φ y))
      rw [hs, hs']
  choose f hf using ex
  refine ⟨{ toFun := f
            map_one' := uniq _ _ _ (hf 1) fun y => rfl
            map_mul' := fun a b => uniq _ _ _ (hf (a * b)) fun y => ?_
            map_zero' := uniq _ _ _ (hf 0) fun y => map_zero φ
            map_add' := fun a b => uniq _ _ _ (hf (a + b)) fun y => ?_
            commutes' := fun r => uniq _ _ _ (hf (algebraMap A _ r)) fun y => map_smul φ r y }, fun i => ?_, hf⟩
  · change φ ((f a : Module.End A Y) ((f b : Module.End A Y) y)) = (a : Module.End A Y') ((b : Module.End A Y') (φ y))
    rw [hf, hf]
  · change φ ((f a : Module.End A Y) y + (f b : Module.End A Y) y) = (a : Module.End A Y') (φ y) + (b : Module.End A Y') (φ y)
    rw [map_add (f := _), hf, hf]
  · exact uniq _ _ _ (hf (heckeGen Y' op' i)) fun y => Subtype.ext (hop i y)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem integers_isLocalRing : IsLocalRing 𝒪[k] := (inferInstance : IsDiscreteValuationRing 𝒪[k]).toIsLocalRing
attribute [local instance] integers_isLocalRing

private theorem valuation_unif_eq_uniformizer : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  have h0 : x ≠ 0 := by
    rintro rfl
    exact uniformizer_pos.ne (by simpa using hx)
  exact Classical.epsilon_spec (p := fun x : kˣ => valuation k (x : k) = uniformizer k) ⟨Units.mk0 x h0, hx⟩

private theorem mem_maximal_pow_iff_valuation (c : ℕ) (x : 𝒪[k]) :
    x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c ↔ valuation k (x : k) ≤ uniformizer k ^ c := by
  have hI := Valuation.integer.integers (valuation k)
  let p : 𝒪[k] := ⟨unif k, (valuation_unif_eq_uniformizer.trans_lt uniformizer_lt_one).le⟩
  have hp : valuation k (algebraMap 𝒪[k] k p) = uniformizer k := valuation_unif_eq_uniformizer
  have e : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {p} := by
    ext y
    rw [← IsLocalRing.residue_eq_zero_iff, GlobalTheory.StepData.residue_eq_zero_iff_lt, Ideal.mem_span_singleton,
      hI.dvd_iff_le, hp, le_uniformizer_iff]
    rfl
  rw [e, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hI.dvd_iff_le, map_pow, map_pow, hp]
  rfl

private theorem mem_Kc_iff' {c : ℕ} {g : GL (Fin n) k} :
    g ∈ Kc k n c ↔ g ∈ KO k (Fin n) ∧ ∀ i j, valuation k ((g.val - 1) i j) ≤ uniformizer k ^ c := by
  have key : ∀ u : GL (Fin n) 𝒪[k],
      u ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))).ker ↔
      ∀ i j, valuation k (((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u).val - 1) i j) ≤ uniformizer k ^ c := by
    intro u
    rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    have e : ((1 : GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c)).val) i j =
        Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := by
      simp only [Units.val_one, Matrix.one_apply]; split_ifs <;> simp
    rw [e]
    refine (Ideal.Quotient.eq.trans (mem_maximal_pow_iff_valuation c _)).trans (iff_of_eq ?_)
    congr 2
    simp only [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> simp <;> rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, (key u).1 hu⟩
  · rintro ⟨⟨u, rfl⟩, hu⟩
    exact ⟨u, (key u).2 hu, rfl⟩

private theorem congruence_subgroup_isOpen (c : ℕ) : IsOpen (Kc k n c : Set (GL (Fin n) k)) := by
  have e : (Kc k n c : Set (GL (Fin n) k)) = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin n) k => (g.val - 1) i j) ⁻¹' {x | valuation k x ≤ uniformizer k ^ c} := by
    ext g; simp only [SetLike.mem_coe, mem_Kc_iff', Set.mem_iInter, Set.mem_inter_iff]; rfl
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter <|
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.preimage ?_ ?_
  · have := Units.continuous_val (M := Matrix (Fin n) (Fin n) k)
    fun_prop
  · have h0 : (valuation k).restrict ((unif k : k) ^ c) ≠ 0 := by simp
    simpa only [Valuation.restrict_le_iff, map_pow (valuation k), valuation_unif_eq_uniformizer] using Valuation.isOpen_closedBall h0

end SlopeTestRemainingChoices

private theorem eigenspace_one_eq_fixed {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M)
    (K : Subgroup H) : GlobalTheory.PRep.eig ρ K 1 = fixd ρ K := by
  ext v
  constructor
  · intro hv u hu
    have h := hv ⟨u, hu⟩
    simpa using h
  · intro hv u
    have h := hv u u.2
    simpa using h

theorem UpperTheory.V.Hi.partUR2Abs :
    ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GLw n w) M) (Z : Submodule ℂ M) (τ : SmIrr (GLw n w)), IsoSum ρ Z τ →
    (∀ K : Subgroup (GLw n w), IsCompact (K : Set (GLw n w)) → Z ⊓ fixd ρ K ≠ ⊥ → fixd τ.ρ K ≠ ⊥) ∧
    (∀ (j : ℕ) (a : ℂ), (∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v) → ∀ z ∈ Z ⊓ fixd ρ (KO (w.adicCompletion L) (Fin n)), sphOp ρ j z = a • z) ∧
    (∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (ρ' : Representation ℂ (GLw n w) M') (f : M →+ M'), (∀ g v, f (ρ g v) = ρ' g (f v)) → ∀ (j : ℕ) v, f (sphOp ρ j v) = sphOp ρ' j (f v)) ∧
    ∀ c : ℕ, IsCompact (Kc (w.adicCompletion L) n c : Set (GLw n w)) := by
  intro L _ _ n w M _ _ ρ Z τ hZ
  have hnat : ∀ (N N' : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup N'] [Module ℂ N']
      (σ : Representation ℂ (GLw n w) N) (σ' : Representation ℂ (GLw n w) N') (f : N →+ N'),
      (∀ g v, f (σ g v) = σ' g (f v)) → ∀ (j : ℕ) v, f (sphOp σ j v) = sphOp σ' j (f v) := by
    intro N N' _ _ _ _ σ σ' f hf j v
    exact (dcSum ℂ _ N σ _ _ _ ((sphComm _ n ℂ N σ).1 _)).2.2.2 ℂ N' σ' f hf v
  have key := fun (K : Subgroup (GLw n w)) (hK : IsCompact (K : Set (GLw n w))) =>
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repScalar ρ τ.ρ τ.smooth Z hZ K 1 hK (by simp)
  simp only [eigenspace_one_eq_fixed] at key
  refine ⟨fun K hK => (key K hK).1, fun j a ha => ?_, fun M' _ _ ρ' => hnat M M' ρ ρ', fun c => ?_⟩
  · refine (key _ GlobalTheory.SplitFlip.isCompact_KO).2 (sphOp ρ j) (sphOp τ.ρ j) a (fun f v _ => ?_) ha
    exact (hnat _ _ τ.ρ ρ f.1.toAddMonoidHom f.2.1 j v).symm
  · exact GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (congruence_subgroup_isOpen c))
      fun g hg => (mem_Kc_iff'.1 hg).1
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.deformationRing_to_heckeAlgebra_surjective :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A T B : Type) [CommRing A] [CommRing T] [Algebra c.O T] [Algebra A T] [CommRing B] [Algebra c.O B] (gen : H.Op → T) (D₀ : W.GDet n B H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Bˣ) (f : B →ₐ[c.O] T),
    (∀ (w : H.Wp) (P : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver P w.1 → IsFrob P (normV w.1) σ →
      (D₀.map f.toRingHom).chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
    (∀ v (j : Fin n) (x : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)), (g : G L Ω) = (x : G L Ω) → H.art v x = unif _ →
      ((∏ i with i ≤ j, W.pushCh f.toRingHom (ψ₀ v i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
    ∀ j : A → B, (∀ b, f (j b) = algebraMap A T b) → Algebra.adjoin A (Set.range gen) = ⊤ → Function.Surjective f := by
  intro L Ω _ _ _ _ _ l _ n c H hH A T B _ _ _ _ _ _ gen D₀ ψ₀ f h1 h2 j hj htop
  have hgen : ∀ i, gen i ∈ f.range := by
    rintro (⟨w, k⟩ | ⟨v, k⟩)
    · obtain ⟨P, hP⟩ := exists_isPlaceOver Ω w.1
      obtain ⟨σ, hσ⟩ := exists_isFrob hP
      have hq : IsUnit ((normV w.1 : ℕ) : c.O) := by
        have h0 := (cycZ L Ω l σ).isUnit.map (algebraMap ℤ_[l] c.O)
        rwa [cycZ_of_isFrob (hH.Wp_away w.1 w.2) hP hσ, map_natCast] at h0
      obtain ⟨u, hu⟩ := hq.exists_left_inv
      have huT : algebraMap c.O T u * ((normV w.1 : ℕ) : T) = 1 := by
        rw [← map_natCast (algebraMap c.O T), ← map_mul, hu, map_one]
      have e := JEx.heckePol_coeff n (normV w.1)
        (fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) (k + 1) k.2
      rw [← h1 w P σ hP hσ, dite_eq_left ⟨Nat.succ_pos _, k.2⟩] at e
      have e2 : (D₀.map f.toRingHom).chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) =
          (D₀.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1)).map f.toRingHom := by
        let y := MonoidAlgebra.single (H.prj σ⁻¹) (1 : B)
        have he (z : MonoidAlgebra B H.Gq) : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom H.Gq C
            (MonoidAlgebra.mapRingHom H.Gq f.toRingHom z) =
            MonoidAlgebra.mapRingHom H.Gq (Polynomial.mapRingHom f.toRingHom)
              (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom H.Gq C z) := by
          rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
            ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
            ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
        let : Algebra B T[X] := ((algebraMap T T[X]).comp f.toRingHom).toAlgebra
        have hn := D₀.nat B[X] T[X]
          { toRingHom := Polynomial.mapRingHom f.toRingHom
            commutes' := fun a => by change (Polynomial.mapRingHom f.toRingHom) (C a) = C (f a); simp }
          (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom H.Gq C y)
        change (D₀.map f.toRingHom).D T[X] _ = _
        rw [← show MonoidAlgebra.mapRingHom H.Gq f.toRingHom y =
          MonoidAlgebra.single (H.prj σ⁻¹) 1 by simp [y], he y]
        exact hn
      rw [e2, coeff_map] at e
      have e3 : gen (.inl (w, k)) = algebraMap c.O T u ^ ((k + 1) * (k + 1 - 1) / 2 : ℕ) *
          ((-1) ^ ((k : ℕ) + 1) * f ((D₀.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1)).coeff (n - (k + 1)))) := by
        refine Eq.trans ?_ (congrArg _ e.symm)
        rw [← mul_assoc, ← mul_pow, huT, one_pow, one_mul]
        rfl
      rw [e3]
      exact mul_mem (pow_mem (f.range.algebraMap_mem u) _)
        (mul_mem (pow_mem (neg_mem (one_mem _)) _) (f.mem_range_self _))
    · obtain ⟨y, hy⟩ := (hH.art_spec v).surj (unif _)
      rw [← h2 v k y (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) y) rfl hy, Units.coe_prod]
      refine prod_mem fun i _ => ?_
      rw [Units.val_mul, Units.val_pow_eq_pow_val]
      exact mul_mem (f.mem_range_self _) (pow_mem (f.range.algebraMap_mem _) _)
  intro t
  have ht : t ∈ Algebra.adjoin A (Set.range gen) := htop ▸ Algebra.mem_top
  change t ∈ f.range
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hgen i
  | algebraMap r => exact ⟨j r, hj r⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


section Loc
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
  (C : Subgroup 𝓀[k]ˣ)

private theorem iwLev_loc : IsOpen (AlgebraTools.iwC k n C : Set (GL (Fin n) k)) ∧ IsCompact (AlgebraTools.iwC k n C : Set (GL (Fin n) k)) ∧
    AlgebraTools.iwC k n C ≤ AlgebraTools.iwC k n ⊤ := by
  have h1 := (AlgebraTools.memIwC k n C).1
  have h2 := (AlgebraTools.memIwC k n C).2.1
  have hle : AlgebraTools.iwC k n C ≤ AlgebraTools.iwC k n ⊤ := by
    intro g hg
    rw [h2]
    exact ((h1 g).1 hg).1
  have hopen : IsOpen (AlgebraTools.iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (show KOne k (Fin n) ≤ AlgebraTools.iwC k n C from le_sup_left.trans le_sup_left)
      GlobalTheory.StepData.isOpen_KOne
  refine ⟨hopen, ?_, hle⟩
  refine IsCompact.of_isClosed_subset GlobalTheory.SplitFlip.isCompact_KO (Subgroup.isClosed_of_isOpen _ hopen) ?_
  intro g hg
  exact GlobalTheory.SmGL.iwahori_le_KO k (Fin n) ((h1 g).1 hg).1

private theorem iwLev_conj {x g : GL (Fin n) k} (hx : x ∈ AlgebraTools.iwC k n C) (hg : g ∈ AlgebraTools.iwC k n ⊤) :
    g * x * g⁻¹ ∈ AlgebraTools.iwC k n C := by
  have h2 := (AlgebraTools.memIwC k n C).2.1
  have h3 := (AlgebraTools.memIwC k n C).2.2.1
  rw [h2] at hg
  exact h3 g hg x hx

end Loc

theorem UpperTheory.V.Hi.levelUR2IwLev :
    ∀ (l : ℕ) (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L), (∀ j C, IsOpen (AlgebraTools.iwC ((w j).adicCompletion L) n C : Set (GLw n (w j))) ∧ IsCompact (AlgebraTools.iwC ((w j).adicCompletion L) n C : Set (GLw n (w j))) ∧ AlgebraTools.iwC ((w j).adicCompletion L) n C ≤ AlgebraTools.iwC ((w j).adicCompletion L) n ⊤) ∧ ((Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)).Normal := by
  intro l L _ _ n q w
  refine ⟨fun j C => iwLev_loc _ n C, ?_⟩
  have hle : Pa.UIw1 l n w ≤ Pa.UIw n w := by
    intro g hg
    simp only [Pa.UIw, Pa.UIw1, Subgroup.mem_pi] at hg ⊢
    intro j hj
    exact (iwLev_loc _ n _).2.2 (hg j hj)
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h g hh hg
  simp only [Pa.UIw, Pa.UIw1, Subgroup.mem_pi] at hh hg ⊢
  intro j hj
  exact iwLev_conj _ n _ (hh j hj) (hg j hj)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.levelUR2BasePack :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V₀ : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V₀.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (wt : Pa.WtVars (Pa.locOf r) O n D) (A : Type) [CommRing A] [Algebra O A] (e : Pa.abelian₂ O Empty D ≃ₐ[O] A) (lam : A →ₐ[O] B.B), (∀ k, residue O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField O) = 1) → (∀ k, lam (e (MvPowerSeries.X (.inr k))) = algebraMap O B.B (wt.c k) * (B.u.ψ (wt.v k) (wt.i k) (wt.γ k) : B.B) - 1) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M] (μ : B.B →+* Module.End A M), (∀ a y, μ (lam a) y = a • y) → RingHom.ker μ = J → ∃ (b : Pa.TWBase (Pa.pairOf B.u) J Empty D) (eb : M ≃+ b.M), b.wt = wt ∧ ∀ t y, eb (μ t y) = t • eb y := by
  intro l _ L Ω _ _ _ _ _ _ s V₀ O _ _ _ n r B J D wt A _ _ e lam hres hlam M _ _ _ _ μ hμ hker
  letI mB : Module B.B M := Module.compHom M μ
  letI mL : Module (Pa.abelian₂ O Empty D) M := Module.compHom M (e : Pa.abelian₂ O Empty D →+* A)
  have hsm : ∀ (a : Pa.abelian₂ O Empty D) (m : M), a • m = (lam.comp e.toAlgHom) a • m := by
    intro a m
    exact (hμ (e a) m).symm
  haveI : Nontrivial A := e.injective.nontrivial
  let bL := (Module.Free.chooseBasis A M).mapCoeffs e.symm.toRingEquiv (fun c x => by
    show e (e.symm c) • x = c • x
    rw [AlgEquiv.apply_symm_apply])
  haveI : Module.Free (Pa.abelian₂ O Empty D) M := Module.Free.of_basis bL
  haveI : Module.Finite (Pa.abelian₂ O Empty D) M := Module.Finite.of_basis bL
  have hann : Module.annihilator B.B M = J := by
    rw [← hker]
    ext b
    rw [Module.mem_annihilator, RingHom.mem_ker]
    constructor
    · intro hb
      ext m
      exact hb m
    · intro hb m
      show μ b m = 0
      rw [hb]
      rfl
  exact ⟨Pa.TWBase.mk wt hres (lam.comp e.toAlgHom) (fun k => hlam k) M hsm inferInstance inferInstance
    (fun p _ => by rw [hann]), AddEquiv.refl M, rfl, fun t y => rfl⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem weight_variables_exist (l : ℕ) [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (n : ℕ)
    (r : Resid F O n) (d : F.Vl → ℕ) (A : ∀ v, W.LocAb l (F.Gv v) (F.Iv v) (d v)) (Λ : LamObj r) (D : ℕ)
    (hD : ∑ v, d v = D) :
    ∃ (v : Fin (n * D) → F.Vl) (i : Fin (n * D) → Fin n) (γ : ∀ k, F.Gv (v k)) (c : Fin (n * D) → O)
      (e : MvPowerSeries (Empty ⊕ Fin (n * D)) O ≃ₐ[O] Λ.Λ), ∀ k, ∃ hγ : γ k ∈ F.Iv (v k),
      residue O (c k) * (r.psib (v k) (i k) (γ k) : ResidueField O) = 1 ∧
      e (MvPowerSeries.X (.inr k)) = algebraMap O Λ.Λ (c k) * (Λ.κ (v k) (i k) ⟨γ k, hγ⟩ : Λ.Λˣ) - 1 := by
  obtain ⟨e, ψ₀, hψ₀, he⟩ := (W.lam_ex_free l F O n r d A).2 Λ
  have hc : Fintype.card (Σ v : F.Vl, Fin n × Fin (d v)) = n * D := by
    rw [Fintype.card_sigma, ← hD, Finset.mul_sum]
    simp
  let ε : Fin (n * D) ≃ (Σ v : F.Vl, Fin n × Fin (d v)) := (Fintype.equivFinOfCardEq hc).symm
  choose g hgI hg using fun (v : F.Vl) (j : Fin (d v)) => ((A v).inertia (Pi.single j 1, 0)).2 rfl
  let ε' : Empty ⊕ Fin (n * D) ≃ (Σ v : F.Vl, Fin n × Fin (d v)) :=
    (@Equiv.emptySum Empty (Fin (n * D)) ⟨Empty.elim⟩).trans ε
  refine ⟨fun k => (ε k).1, fun k => (ε k).2.1, fun k => g (ε k).1 (ε k).2.2,
    fun k => ((ψ₀ (ε k).1 (ε k).2.1 (g (ε k).1 (ε k).2.2))⁻¹ : Oˣ),
    (MvPowerSeries.renameEquiv O ε').trans e, fun k => ⟨hgI _ _, ?_, ?_⟩⟩
  · have h1 := (hψ₀ (ε k).1 (ε k).2.1).red (g (ε k).1 (ε k).2.2)
    have h2 : ∀ x : O, Alg.res O O x = residue O x := fun x => (Alg.res O O).commutes x
    rw [h2] at h1
    show residue O _ * ((r.psib (ε k).1 (ε k).2.1 (g (ε k).1 (ε k).2.2) : (ResidueField O)ˣ) : ResidueField O) = 1
    rw [← h1, ← map_mul, Units.inv_mul, map_one]
  · have h1 := he (ε k).1 (ε k).2.1 (ε k).2.2 ⟨g (ε k).1 (ε k).2.2, hgI _ _⟩ (hg _ _)
    have h2 : MvPowerSeries.renameEquiv O ε' (MvPowerSeries.X (.inr k)) = MvPowerSeries.X (ε k) := by
      exact MvPowerSeries.rename_X _ _
    show e (MvPowerSeries.renameEquiv O ε' (MvPowerSeries.X (.inr k))) =
      algebraMap O Λ.Λ ((ψ₀ (ε k).1 (ε k).2.1 (g (ε k).1 (ε k).2.2))⁻¹ : Oˣ) *
        ((Λ.κ (ε k).1 (ε k).2.1 ⟨g (ε k).1 (ε k).2.2, hgI _ _⟩ : Λ.Λˣ) : Λ.Λ) - 1
    rw [h1, h2, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul, add_sub_cancel_left]

theorem UpperTheory.V.Hi.levelUR2WtVars :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r), Pa.LocCFT s → ∃ (wt : Pa.WtVars (Pa.locOf r) c.O n (n * Module.finrank ℚ (Lp L))) (e : Pa.abelian₂ c.O Empty (n * Module.finrank ℚ (Lp L)) ≃ₐ[c.O] Λ.Λ), ∀ k, ∃ hγ : wt.γ k ∈ V.frame.Iv (wt.v k), residue c.O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField c.O) = 1 ∧ e (MvPowerSeries.X (.inr k)) = algebraMap c.O Λ.Λ (wt.c k) * (Λ.κ (wt.v k) (wt.i k) ⟨wt.γ k, hγ⟩ : Λ.Λˣ) - 1 := by
  intro l hl L Ω _ _ _ _ _ _ s n V c r _ Λ h
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField ℤ_[l]) l :=
    charP_of_injective_ringHom (f := (PadicInt.residueField (p := l)).symm.toRingHom)
      (PadicInt.residueField (p := l)).symm.injective l
  haveI : CharP (ResidueField c.O) l :=
    charP_of_injective_ringHom (algebraMap (ResidueField ℤ_[l]) (ResidueField c.O)).injective l
  obtain ⟨d₀, hd, hA⟩ := h
  let d : V.frame.Vl → ℕ := d₀
  have hsum : ∑ v : V.frame.Vl, d v = Module.finrank ℚ (Lp L) :=
    (finsum_eq_sum_of_fintype (α := V.frame.Vl) d).symm.trans hd
  obtain ⟨v, i, γ, cc, e, H⟩ := weight_variables_exist l V.frame c.O n r d (fun v => (hA v).some) Λ _ hsum
  exact ⟨⟨v, i, γ, cc⟩, e, H⟩
end
