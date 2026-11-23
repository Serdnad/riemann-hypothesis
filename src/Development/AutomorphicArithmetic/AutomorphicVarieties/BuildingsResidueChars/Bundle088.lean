module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle307
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle272
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle320
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct

private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.under (𝓞 K) = v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (RingOfIntegers.algebraMap.injective K L)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

private theorem ker_pr_le {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) (K : Subgroup (G L Ω))
    (hK : IsClosed (K : Set (G L Ω)))
    (hI : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      Ine (F := L) A ≤ K) : V.pr.ker ≤ K := by
  have hc : IsClosed ((K.map (W.resP L Ω) : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) :=
    (hK.isCompact.image W.continuous_resP).isClosed
  have hN : NS Ω V.S' ≤ (K.map (W.resP L Ω)).normalCore := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
      (Subgroup.normalCore_isClosed _ hc)
    intro g hg b
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, A, hA, hg⟩ := hg
    have hl : IsLift (RingEquiv.refl (W.Lp L)) (b⁻¹).toRingEquiv := fun x => (b⁻¹).commutes x
    have hAA : ∀ x, (b⁻¹).toRingEquiv x ∈ A ↔ x ∈ A.comap (b⁻¹).toRingEquiv.toRingHom := fun x => Iff.rfl
    have h1 : b * g * b⁻¹ ∈ Ine (F := W.Lp L) (A.comap (b⁻¹).toRingEquiv.toRingHom) := conjGal_mem_Ine hl hAA hg
    have hA' : IsPlaceOver (A.comap (b⁻¹).toRingEquiv.toRingHom) v := fun x => by
      rw [← val_lt_one hAA, ← hA x]
      exact Iff.of_eq (congrArg (fun y => A.valuation y < 1) ((b⁻¹).commutes (x : W.Lp L)))
    obtain ⟨t, ht⟩ := s.unr _ _ hA' h1
    obtain ⟨w, hw, hwv⟩ := place_between (L := L) hA'
    refine ⟨t, hI w (by rw [hwv]; exact hv) _ hw ?_, ht⟩
    rw [← ht] at h1
    exact h1
  intro g hg
  have h1 : W.resP L Ω g ∈ NS Ω V.S' := (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hg)
  obtain ⟨t, ht, e⟩ := Subgroup.normalCore_le _ (hN h1)
  have : t = g := AlgEquiv.ext fun x => DFunLike.congr_fun e x
  exact this ▸ ht

private theorem pr_surj {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := fun g => by
  obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
  obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
  exact ⟨σ, Subtype.ext hτ⟩

private theorem ker_closed {H k : Type} [Group H] [TopologicalSpace H] [CommRing k] [TopologicalSpace k] [T2Space k] {n : ℕ}
    (r : H →* GL (Fin n) k) (hr : Continuous r) : IsClosed (r.ker : Set H) := by
  have h : (r.ker : Set H) = {g | ∀ i j, (r g).val i j = (1 : Matrix (Fin n) (Fin n) k) i j} :=
    Set.ext fun g => ⟨fun hg i j => by rw [show r g = 1 from hg]; rfl, fun hg => Units.ext (Matrix.ext hg)⟩
  rw [h, Set.setOf_forall]
  refine isClosed_iInter fun i => ?_
  rw [Set.setOf_forall]
  refine isClosed_iInter fun j => isClosed_eq ?_ continuous_const
  have hv : Continuous fun g => (r g).val := Units.continuous_val.comp hr
  exact hv.matrix_elem i j

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.exists_descent_to_level_group_of_unramified :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (c : Coef l) (r : G L Ω →* GL (Fin n) (Qbar l)), Continuous r → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ g ∈ Ine (F := L) A, r g = 1) → ∃ ρ : V.frame.G₀ →* GL (Fin n) (Qbar l), Continuous ρ ∧ ρ.comp V.pr = r ∧ ∀ P, Af.IsPairing s.c r (cycBar L Ω l ^ (1 - (n : ℤ))) P → V.frame.IsForm c.O n ρ P := by
  intro l _ L Ω _ _ _ _ _ _ s n V c r hcont hI
  have hker : V.pr.ker ≤ r.ker :=
    ker_pr_le V _ (ker_closed r hcont) fun w hw A hA t ht => hI w hw A hA t ht
  let ρ : V.frame.G₀ →* GL (Fin n) (Qbar l) := V.pr.liftOfSurjective (pr_surj V) ⟨r, hker⟩
  have hρ : ∀ g, ρ (V.pr g) = r g := fun g => V.pr.liftOfRightInverse_comp_apply _ _ _ g
  refine ⟨ρ, ?_, MonoidHom.ext hρ, fun P hP g => ?_⟩
  · haveI := isClosed_NS Ω V.S'
    have hq : Topology.IsQuotientMap V.pr :=
      (V.pr_cont W.continuous_resP).isClosedMap.isQuotientMap (V.pr_cont W.continuous_resP) (pr_surj V)
    exact hq.continuous_iff.2 (hcont.congr fun g => (hρ g).symm)
  · obtain ⟨t, rfl⟩ := pr_surj V g
    obtain ⟨t', ht'⟩ : s.c * W.resP L Ω t * s.c⁻¹ ∈ (W.resP L Ω).range := by
      rw [← V.hη, map_mul (toGS Ω V.S'), map_mul (toGS Ω V.S'), map_inv (toGS Ω V.S')]
      exact (V.frame.conj (V.pr t)).2
    have e1 : V.frame.conj (V.pr t) = V.pr t' := Subtype.ext (by
      show toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω t) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω t')
      rw [ht', map_mul, map_mul, map_inv])
    have e2 := hP t t' ht'
    have e3 : V.ε (V.pr t).1 = cycZ L Ω l t := DFunLike.congr_fun V.hε (W.resP L Ω t)
    have e4 : V.frame.eps c.O (Qbar l) (V.pr t) = cycBar L Ω l t := by
      refine Units.ext ?_
      show ((algebraMap ℤ_[l] c.O (V.ε (V.pr t).1 : ℤ_[l]ˣ) : c.O) : Qbar l) = _
      rw [e3]
      rfl
    rw [e1, e4]
    show (ρ (V.pr t)).val.transpose * _ * (ρ (V.pr t')).val = _
    rw [hρ, hρ]
    exact e2
end

section

open UpperTheory.V.Af UpperTheory.V.Af.Gu
open GlobalTheory.DefiniteBC

private theorem spehInf_eq_sum_shifted_map (d : ℕ) (m : Multiset ℂ) :
    spehInf d m = ∑ k : Fin d, Multiset.map (fun x => x + (((d:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) m := by
  unfold spehInf
  rw [Fin.sum_univ_eq_sum_range (fun k => Multiset.map (fun x => x + (((d:ℂ) - 1) / 2 - (k:ℂ))) m) d]
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]

private theorem infOfWeight_nodup' (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n) :
    (GlobalTheory.UnitaryBC.infOfWeight lam).Nodup := by
  unfold GlobalTheory.UnitaryBC.infOfWeight
  refine Multiset.Nodup.map ?_ Finset.univ.nodup
  intro a b h
  have h2 : ((lam.w a - (a:ℕ) : ℤ) : ℂ) = ((lam.w b - (b:ℕ) : ℤ) : ℂ) := by
    push_cast
    linear_combination h
  have h3 : lam.w a - (a:ℕ) = lam.w b - (b:ℕ) := by exact_mod_cast h2
  rcases lt_trichotomy a b with hab | hab | hab
  · have := lam.anti hab.le
    have : (a:ℕ) < (b:ℕ) := hab
    omega
  · exact hab
  · have := lam.anti hab.le
    have : (b:ℕ) < (a:ℕ) := hab
    omega

private theorem multiset_map_finset_sum {ι : Type*} (s : Finset ι) (g : ℂ → ℂ) (f : ι → Multiset ℂ) :
    Multiset.map g (∑ i ∈ s, f i) = ∑ i ∈ s, Multiset.map g (f i) :=
  map_sum (Multiset.mapAddMonoidHom g) f s

theorem UpperTheory.speh_parameter_strings :
    Strings := by
  intro n c d m lam h
  have hnd := infOfWeight_nodup' n lam
  refine ⟨fun i k => ?_, ?_⟩
  · have hle1 : Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i) ≤ spehInf (d i) (m i) := by
      rw [spehInf_eq_sum_shifted_map]
      exact Finset.single_le_sum (f := fun k : Fin (d i) => Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i))
        (fun _ _ => Multiset.zero_le _) (Finset.mem_univ k)
    have hle2 : spehInf (d i) (m i) ≤ ∑ j, spehInf (d j) (m j) :=
      Finset.single_le_sum (f := fun j => spehInf (d j) (m j)) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
    have hle : Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i) ≤ GlobalTheory.UnitaryBC.infOfWeight lam :=
      h ▸ hle1.trans hle2
    refine ⟨(Multiset.nodup_of_le hle hnd).of_map _, fun z hz => ?_⟩
    have hmem := Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz)
    unfold GlobalTheory.UnitaryBC.infOfWeight at hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨j, -, hj⟩ := hmem
    refine ⟨lam.w j - (j:ℕ), ?_⟩
    unfold ex
    push_cast
    linear_combination (-1 : ℂ) * hj
  · rw [← h, multiset_map_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [spehInf_eq_sum_shifted_map, multiset_map_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    unfold ex
    push_cast
    ring
end

section

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
open UpperTheory.V.Af UpperTheory.V.Af.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.building_component_uniqueness :
    CompUnique := by
  intro E _ _ _ n π hπ w hw V W _ _ _ _ ρ₁ ρ₂ h₁ h₂
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨r, -, -, hc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  let s : GL (Fin n) (w.adicCompletion E) →* UA E n :=
    (locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cLoc w (s y) = y := fun y => by
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  let P : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  have key : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (τ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) X),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ →
      ∃ f : τ.IntertwiningMap (P.rep.comp s), f ≠ 0 := by
    rintro X _ _ τ ⟨-, f, h0, hf, h2⟩
    refine ⟨⟨f.codRestrict π hf, fun y => LinearMap.ext fun v => Subtype.ext ?_⟩, fun e0 => h0 ?_⟩
    · have h3 := h2 (e.symm y) v
      have hy : ((cLoc w).comp (locU n w).subtype) (e.symm y) = y := hs y
      rw [hy] at h3
      exact h3
    · exact LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun e0 v)
  obtain ⟨f, hf⟩ := key ρ₁ h₁
  obtain ⟨f', hf'⟩ := key ρ₂ h₂
  have hcomm : ∀ g : UA E n, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      have : s (e (r g)) = (r g : UA E n) := congrArg Subtype.val (e.symm_apply_apply (r g))
      rw [this]
      exact hc g (e.symm y)⟩
  exact (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ P.rep s ρ₁ ρ₂ P.isIrreducible_rep h₁.1 h₂.1 hcomm f hf).2 f' hf'
end

section

open UpperTheory.V.Af UpperTheory.V.Af.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.sum_family_of_reductions :
    SumTwo → SumRed → SumFam := by
  intro h2 hred E Ω _ _ _ _ _ l _ ι c hc
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  clear hc
  induction c with
  | zero =>
    intro N hN n hn r p HT H
    have hn' : N 0 = n := by simpa using hn
    subst hn'
    refine ⟨r 0, ⟨(H 0).cont, (H 0).ss, ?_, fun w => ((H 0).par w).congr fun A h rc _ => ?_⟩, fun hi => ⟨rfl, fun i => ?_⟩⟩
    · have e : (fun τ => ∑ i, HT i τ) = HT 0 := by
        funext τ
        simp
      rw [e]
      exact (H 0).ht
    · simp [sumList, WD.lpSum_zero]
    · obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact hi
  | succ c ih =>
    intro N hN n hn r p HT H
    rw [Fin.sum_univ_succ] at hn
    subst hn
    obtain ⟨R, hR, -⟩ := ih (fun i => N i.succ) (fun i => hN i.succ) _ rfl (fun i => r i.succ) (fun i => p i.succ)
      (fun i => HT i.succ) (fun i => H i.succ)
    have hS := h2 E Ω l ι _ _ (r 0) R _ _ _ _ (H 0) hR
    refine ⟨Formalism.MainNotions.SumRepresentations.At.sumRep (r 0) R, ⟨hS.cont, hS.ss, ?_, fun w => (hS.par w).congr fun A h rc _ => ?_⟩, fun hi => ?_⟩
    · have e : (fun τ => ∑ i, HT i τ) = fun τ => HT 0 τ + ∑ i : Fin (c + 1), HT i.succ τ := by
        funext τ
        rw [Fin.sum_univ_succ]
      rw [e]
      exact hS.ht
    · rw [List.ofFn_succ (f := fun i => p i w A h rc)]
      rfl
    · refine absurd hi (hred _ _ _ _ _ _ (hN 0) ?_)
      exact le_trans (hN (Fin.succ 0)) (Finset.single_le_sum (f := fun i : Fin (c + 1) => N i.succ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
end

section

open UpperTheory.V.Af UpperTheory.V.Af.Gu
open GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.SumParam

theorem UpperTheory.galoisRep_direct_sum_away_from_places :
    SumAway := by
  intro E Ω _ _ _ _ _ l _ ι a b r r' hr hr' w hl A h x x' hx hx'
  have c : Continuous fun g => ((r g : GL (Fin a) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin a) (Fin a) (Formalism.ConjugateSelfDual.Qbar l)) :=
    Units.continuous_val.comp hr
  have c' : Continuous fun g => ((r' g : GL (Fin b) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin b) (Fin b) (Formalism.ConjugateSelfDual.Qbar l)) :=
    Units.continuous_val.comp hr'
  have cs : Continuous fun g => ((Formalism.MainNotions.SumRepresentations.At.sumRep r r' g : GL (Fin (a + b)) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin (a + b)) (Fin (a + b)) (Formalism.ConjugateSelfDual.Qbar l)) := by
    simp only [coe_sumRep]
    exact (c.matrix_fromBlocks continuous_const continuous_const c').matrix_reindex _ _
  rw [← hx.wdOf_eq hl, ← hx'.wdOf_eq hl, ← wdOf_sumRep hl ι r r' c c']
  exact isWDOf_wdOf hl ι cs
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.sum_two_of_hodge_tate :
    HypothesesH → SumAway → SumHT → SumTwo := by
  intro H hA hT E Ω _ _ _ _ _ l _ ι a b r r' p p' HT HT' C C'
  obtain ⟨T⟩ := Loc.tiedP l
  have hv := GlobalTheory.BCGal.cont_sumRep r r' (Units.continuous_val.comp C.cont) (Units.continuous_val.comp C'.cont)
  have hc : Continuous (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    simp only [← map_inv]
    exact hv.comp continuous_inv
  have hht := hT E Ω l a b r r' C.cont C'.cont HT HT' C.ht C'.ht
  refine ⟨hc, GlobalTheory.BCGal.ss_sumRep r r' C.ss C'.ss, hht, fun w A h rc hrc => ?_⟩
  obtain ⟨a1, b1⟩ := C.par w A h rc hrc
  obtain ⟨a2, b2⟩ := C'.par w A h rc hrc
  refine ⟨fun hw => hA E Ω l ι a b r r' C.cont C'.cont w hw A h _ _ (a1 hw) (a2 hw), fun O _ _ _ Bw hj => ?_⟩
  obtain ⟨p1, e1⟩ := b1 O Bw hj
  obtain ⟨p2, e2⟩ := b2 O Bw hj
  have p3 : IsPstAt (Loc.PP l) Bw ((Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    refine H.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hc.comp continuous_subtype_val)) ?_
    exact (hht w A h O Bw hj).1
  refine ⟨p3, ?_⟩
  have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) (r'.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  rw [e] at p3 ⊢
  rw [GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l _ _ ⟨T⟩ ι E Ω A w O Bw h hj a b _ _ p1 p2 p3]
  exact (Lev.ssCalc E Ω A w h).2.1 _ _ _ _ e1 e2
end

section

open UpperTheory.V.Af UpperTheory.V.Af.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.GalOfCusp

private theorem eta_val (L : Type) [Field L] [NumberField L] (k : Lˣ) :
    ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
  classical
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
    ι (fun w => algebraMap L w.Completion k)
  rw [← map_prod, Finset.univ_prod_mulSingle]

private theorem eta_map (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (x : Kˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L (infDiag x) = infDiag (Units.map (algebraMap K L).toMonoidHom x) := by
  apply Units.ext
  change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L ((infDiag x : Ideles K) : AdeleRing (𝓞 K) K) = _
  rw [eta_val, eta_val]
  refine Prod.ext ?_ ?_
  · have h := congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap K L (x : K))
    exact h
  · exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L)

private theorem eta_loc {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (h2 : ∀ x, χ.1 x ^ 2 = 1)
    (v : InfinitePlace F) (hs : χ.locInf v (-1) = -1) (k : Fˣ) :
    ((χ.locInf v (atInf v k) : ℂˣ) : ℂ) * ((‖v.embedding (k : F)‖ : ℝ) : ℂ) = v.embedding (k : F) := by
  have hv : v.IsReal := IsTotallyReal.isReal v
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  have he : e (algebraMap _ v.Completion (k : F)) = InfinitePlace.embedding_of_isReal hv k := by
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply]
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm (k : F))
  have hsq : ∀ x : (v.Completion)ˣ, 0 < e x → χ.locInf v x = 1 := fun x hx => by
    have h0 : e.symm (Real.sqrt (e x)) ≠ 0 := by
      rw [map_ne_zero]
      exact (Real.sqrt_pos.2 hx).ne'
    have e1 : x = Units.mk0 _ h0 ^ 2 := Units.ext (e.injective (by
      rw [Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, e.apply_symm_apply, Real.sq_sqrt hx.le]))
    rw [e1, map_pow]
    exact h2 _
  have h0 : InfinitePlace.embedding_of_isReal hv k ≠ 0 := (map_ne_zero _).2 k.ne_zero
  rw [← InfinitePlace.embedding_of_isReal_apply hv, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne h0 with h | h
  · have e1 : atInf v k = -1 * -atInf v k := by simp
    rw [e1, map_mul, hs, hsq _ (by
      rw [Units.val_neg, map_neg]
      exact neg_pos.2 (he ▸ h)), abs_of_neg h]
    simp
  · rw [hsq _ (he ▸ h), abs_of_pos h]
    simp

private theorem eta_inf {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (h2 : ∀ x, χ.1 x ^ 2 = 1)
    (hs : ∀ v, χ.locInf v (-1) = -1) (k : Fˣ) :
    ((χ.inf k : ℂˣ) : ℂ) * ((‖∏ φ : F →+* ℂ, φ (k : F)‖ : ℝ) : ℂ) = ∏ φ : F →+* ℂ, φ (k : F) := by
  have hb : Function.Bijective fun v : InfinitePlace F => v.embedding :=
    ⟨InfinitePlace.embedding_injective F, fun φ =>
      ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)⟩⟩
  have e1 : χ.inf k = ∏ v : InfinitePlace F, χ.locInf v (atInf v k) := by
    unfold HChar.inf HChar.locInf infDiag
    rw [MonoidHom.comp_apply, MonoidHom.finsetProd_apply, map_prod]
    rfl
  rw [← hb.prod_comp fun φ => φ (k : F), e1, Units.coe_prod, norm_prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => eta_loc χ h2 v (hs v) k

private theorem eta_norm (E : Type) [Field E] [NumberField E] (k : E) :
    ∏ φ : E →+* ℂ, φ k = ((Algebra.norm ℚ k : ℚ) : ℂ) := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ k
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ k)
    (fun σ : E →ₐ[ℚ] ℂ => σ k) (fun _ => rfl)] at h
  rw [← h]; simp

private theorem eta_abs (E : Type) [Field E] [NumberField E] [IsCMField E] (f : ℤ) (k : (maximalRealSubfield E)ˣ) :
    (((GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2))).inf k : ℂˣ) : ℂ) =
      ((‖∏ φ : maximalRealSubfield E →+* ℂ, φ (k : maximalRealSubfield E)‖ : ℝ) : ℂ) ^ f := by
  have e1 : (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2))).inf k =
      (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)).inf (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom k) :=
    congrArg (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)).1 (eta_map _ E k)
  rw [e1, (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E _).2.2]
  simp only [← Complex.ofReal_cpow (norm_nonneg _)]
  rw [← Complex.ofReal_prod, Real.finsetProd_rpow _ _ fun _ _ => norm_nonneg _, ← norm_prod, eta_norm, eta_norm]
  have e2 : Algebra.norm ℚ ((Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom k : Eˣ) : E) =
      Algebra.norm ℚ (k : maximalRealSubfield E) ^ 2 := by
    change Algebra.norm ℚ (algebraMap (maximalRealSubfield E) E k) = _
    rw [← Algebra.norm_norm (S := maximalRealSubfield E), Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two,
      map_pow]
  rw [e2, Rat.cast_pow, norm_pow, ← Complex.ofReal_zpow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
    ← Real.rpow_intCast]
  congr 2
  push_cast
  ring

theorem UpperTheory.eta_condition :
    Eta := by
  intro E _ _ _ f
  have hq : ∀ x, (quadChar E).1 x ^ 2 = 1 := fun x => by
    change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
    rw [← map_pow, Int.units_sq, map_one]
  obtain ⟨ξ, m, hm, hξ⟩ := Cq.extReal E
    (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)) * quadChar E ^ f)⁻¹ (-f) fun k => by
      have e : (quadChar E ^ f).inf k = (quadChar E).inf k ^ f := rfl
      rw [HChar.inf_inv, HChar.inf_mul, Units.val_inv_eq_inv_val, Units.val_mul, eta_abs, e, Units.val_zpow_eq_zpow_val,
        ← mul_zpow, mul_comm, eta_inf _ hq (quadChar_locInf E), Finset.prod_zpow, zpow_neg]
  refine ⟨ξ, m, hm, ?_⟩
  have e : GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2) * ξ) =
      GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)) * GlobalTheory.HeightCounting.Blocks.resReal ξ := rfl
  rw [e, hξ, mul_inv, mul_inv_cancel_left, map_inv, map_zpow, compNorm_quadChar, one_zpow, inv_one]
end
