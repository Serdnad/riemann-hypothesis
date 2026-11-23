module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle041
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.DelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ProjNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.TrOfCommdc
import GroundTheory.LocalFields.UnramifiedHensel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle046
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CoboundaryLemmaNoColumn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle015
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelUpper
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle043
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.AdmissibleUnitaryThreePoint
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem opOf_proj {Λ Γ Q M : Type} [CommRing Λ] [Group Γ] [Group Q] [AddCommGroup M] [Module Λ M]
    (ρ : Representation Λ Q M) (e : Γ ≃* Q) (hP : Module.Projective (MonoidAlgebra Λ Q) ρ.asModule) :
    Module.Projective (MonoidAlgebra Λ Γ) (Representation.asModule (ρ.comp e.toMonoidHom : Representation Λ Γ M)) := by
  let σ : MonoidAlgebra Λ Q ≃+* MonoidAlgebra Λ Γ := (MonoidAlgebra.domCongr Λ Λ e.symm).toRingEquiv
  let ρ' : Representation Λ Γ M := ρ.comp e.toMonoidHom
  have key : ∀ a : MonoidAlgebra Λ Q, ρ'.asAlgebraHom (σ a) = ρ.asAlgebraHom a := fun a => by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | single g c => simp [σ, ρ']
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  let f : ρ.asModule ≃ₛₗ[(σ : MonoidAlgebra Λ Q →+* MonoidAlgebra Λ Γ)] ρ'.asModule :=
    { ρ.asModuleEquiv.toAddEquiv.trans ρ'.asModuleEquiv.symm.toAddEquiv with
      map_smul' := fun a m => by
        apply ρ'.asModuleEquiv.injective
        rw [Representation.asModuleEquiv_map_smul]
        simp [Representation.asModuleEquiv_map_smul, key] }
  exact Module.Projective.of_equiv f
private theorem opOf_dc {R G P : Type} [CommRing R] [Group G] [AddCommGroup P] [Module R P] (ρ : Representation R G P)
    (K K1 : Subgroup G) [Fintype (K ⧸ K1.subgroupOf K)] (m : P) (hm : m ∈ fixd ρ K1) :
    dc ρ K K1 1 m = ∑ g : K ⧸ K1.subgroupOf K, ρ (g.out : K) m := by
  let f : K ⧸ K1.subgroupOf K → MulAction.orbit K ((1 : G) : G ⧸ K1) := fun g =>
    ⟨((g.out : K) : G), g.out, congrArg QuotientGroup.mk (mul_one _)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, ?_⟩
    · have h1 := QuotientGroup.eq.1 (congrArg Subtype.val hab)
      rw [← a.out_eq', ← b.out_eq']
      exact QuotientGroup.eq.2 h1
    · rintro ⟨_, k, rfl⟩
      refine ⟨(k : K ⧸ K1.subgroupOf K), Subtype.ext ?_⟩
      have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' (k : K ⧸ K1.subgroupOf K))
      have h2 : (((k : K ⧸ K1.subgroupOf K).out : K) : G ⧸ K1) = ((k : G) : G ⧸ K1) := QuotientGroup.eq.2 h1
      exact h2.trans (congrArg (QuotientGroup.mk (s := K1)) (mul_one (k : G)).symm)
  unfold dc
  rw [← finsum_comp f hf, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K1 ((g.out : K) : G)
  show ρ (((g.out : K) : G) : G ⧸ K1).out m = _
  rw [hu, map_mul, Module.End.mul_apply, hm u u.2]
private theorem opOf_tr {Λ R G P Γ σ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group G] [AddCommGroup P]
    [Module R P] [Module Λ P] [IsScalarTower Λ R P] [Group Γ] [Finite Γ] (ρ : Representation R G P)
    (K K1 : Subgroup G) (hle : K1 ≤ K) [(K1.subgroupOf K).Normal]
    (ρ' : Representation Λ (K ⧸ K1.subgroupOf K) (fixd ρ K1))
    (hρ' : ∀ (u : K) f, (ρ' (u : K ⧸ K1.subgroupOf K) f : P) = ρ u f)
    (hP : Module.Projective (MonoidAlgebra Λ (K ⧸ K1.subgroupOf K)) ρ'.asModule)
    (e : Γ ≃* K ⧸ K1.subgroupOf K) (γ : σ → Γ) (hγ : Subgroup.closure (Set.range γ) = ⊤)
    (Y : σ → Module.End R (fixd ρ K1)) (hY : ∀ p m, ρ' (e (γ p)) m = m + Y p m)
    (tr : fixd ρ K1 →ₗ[R] fixd ρ K) (htr : ∀ m, (tr m : P) = dc ρ K K1 1 m) :
    Function.Surjective tr ∧ LinearMap.ker tr = ⨆ p, LinearMap.range (Y p) := by
  haveI : Finite (K ⧸ K1.subgroupOf K) := Finite.of_equiv Γ e.toEquiv
  letI := Fintype.ofFinite (K ⧸ K1.subgroupOf K)
  obtain ⟨h1, h2⟩ := projNorm Λ _ _ ρ' hP
  have hs : ∀ m, (tr m : P) = (∑ g, ρ' g m : fixd ρ K1) := fun m => by
    rw [htr, opOf_dc ρ K K1 m m.2, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← hρ', QuotientGroup.out_eq']
  refine ⟨fun v => ?_, le_antisymm (fun m hm => ?_) (iSup_le fun p => ?_)⟩
  · obtain ⟨m, hm⟩ := h1 ⟨v, fixd_anti ρ hle v.2⟩ fun g => by
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
      exact Subtype.ext ((hρ' u _).trans (v.2 u u.2))
    exact ⟨m, Subtype.ext (by rw [hs, hm])⟩
  · have h0 : ∑ g, ρ' g m = 0 := Subtype.ext (by rw [← hs, LinearMap.mem_ker.1 hm]; rfl)
    have hc : Subgroup.closure (Set.range fun p => e (γ p)) = ⊤ := by
      have := congrArg (Subgroup.map e.toMonoidHom) hγ
      rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top_of_surjective _ e.surjective] at this
      exact this
    have h3 : (⨆ g ∈ Set.range fun p => e (γ p), LinearMap.range (ρ' g - 1)) ≤
        (⨆ p, LinearMap.range (Y p)).restrictScalars Λ := by
      refine iSup₂_le ?_
      rintro _ ⟨p, rfl⟩ _ ⟨v, rfl⟩
      refine Submodule.mem_iSup_of_mem (p := fun p => LinearMap.range (Y p)) p ⟨v, ?_⟩
      rw [LinearMap.sub_apply, hY, Module.End.one_apply, add_sub_cancel_left]
    exact h3 (h2 _ hc m h0)
  · rintro _ ⟨m, rfl⟩
    have h4 : tr (ρ' (e (γ p)) m) = tr m := Subtype.ext (by
      rw [hs, hs]
      congr 1
      refine Fintype.sum_equiv (Equiv.mulRight (e (γ p))) _ _ fun g => ?_
      rw [Equiv.coe_mulRight, map_mul, Module.End.mul_apply])
    rw [hY, map_add (f := _)] at h4
    exact add_eq_left.1 h4
private theorem opOf_gen {l q n : ℕ} (hl : l.Prime) (a : Fin q → ℕ) :
    Subgroup.closure (Set.range fun p : Fin q × Fin n => (Pi.mulSingle p (Multiplicative.ofAdd 1) : Del l n a)) = ⊤ := by
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ a p.1) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  refine eq_top_iff.2 fun g _ => ?_
  rw [← Finset.univ_prod_mulSingle g]
  refine Subgroup.prod_mem _ fun s _ => ?_
  have h1 : g s = Multiplicative.ofAdd (1 : ZMod (l ^ a s.1)) ^ (Multiplicative.toAdd (g s)).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [h1, Pi.mulSingle_pow]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self s)) _
private theorem opOf_cop {L : Type} [Field L] [NumberField L] (w : Plc L) {l : ℕ} (hl : l.Prime)
    (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) : l.Coprime (resCard (w.adicCompletion L)) := by
  have h1 : Valued.v (l : w.adicCompletion L) = 1 := by
    have e : (l : w.adicCompletion L) = algebraMap L _ (algebraMap (𝓞 L) L l) := by simp
    rw [e]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans ?_
    exact (HeightOneSpectrum.valuation_of_algebraMap w _).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 hw)
  have h2 : valuation (w.adicCompletion L) (l : w.adicCompletion L) = 1 := by
    haveI : (Valued.v : Valuation (w.adicCompletion L) _).Compatible := Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (valuation (w.adicCompletion L)) Valued.v).eq_one_iff_eq_one.2 h1
  have h3 : IsUnit (l : 𝒪[w.adicCompletion L]) :=
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 (by simpa using h2)
  have h4 : (l : 𝓀[w.adicCompletion L]) ≠ 0 := by
    simpa using (h3.map (residue 𝒪[w.adicCompletion L])).ne_zero
  rw [hl.coprime_iff_not_dvd]
  intro hd
  letI := Fintype.ofFinite 𝓀[w.adicCompletion L]
  haveI := Fact.mk hl
  rw [resCard, Nat.card_eq_fintype_card] at hd
  exact h4 ((ringChar.spec _ _).2 (by
    have h5 := (prime_dvd_char_iff_dvd_card l).2 hd
    have h6 := CharP.char_is_prime 𝓀[w.adicCompletion L] (ringChar 𝓀[w.adicCompletion L])
    rw [(Nat.prime_dvd_prime_iff_eq hl h6).1 h5]))
private theorem opOf_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ iwC k n ⊤ := by
  have h1 : unitsC k C ≤ unitsC k ⊤ := Subgroup.map_mono (Subgroup.comap_mono le_top)
  have h2 : torC k n C ≤ torC k n ⊤ := fun t ht i hi => h1 (ht i hi)
  exact sup_le_sup_left (Subgroup.map_mono h2) _
private theorem opOf_tow {Λ R P : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [AddCommGroup P]
    [Module R P] [Module Λ P] [IsScalarTower Λ R P] (S : Submodule R P) : IsScalarTower Λ R S := inferInstance
theorem UpperTheory.V.Th.opOfX_alt :
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (ph ta : Fin q → (globOf r V).G₀) (N : ℕ), _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ ph ta → (∀ j, qj w j ≡ 1 [MOD l ^ N]) → ∃ A' : OpMod b h q N, OpRelX A' (qj w) ph ta (2 * n.factorial) := by
  intro hP l hl L Ω _ _ _ _ _ _ s V0 O _ _ _ hO _ n r B J D b V h q w A x δ hw hx hδ ph ta N hok hN
  have hq : ∀ j, IsUnit (qj w j : A.R) := fun j => by
    haveI := hO.char
    have h1 : IsUnit (qj w j : ResidueField O) :=
      (CharP.isUnit_natCast_iff hl.out).2 (hl.out.coprime_iff_not_dvd.1 (opOf_cop (w j) hl.out (hw j)))
    have h2 : IsUnit (qj w j : O) := by
      rw [← map_natCast (residue O)] at h1
      exact (isUnit_map_iff _ _).1 h1
    simpa using h2.map (algebraMap O A.R)
  obtain ⟨T⟩ := thEx L n q w l A.R A.P A.ρ x δ hq
  obtain ⟨hn, ρ', hρ', hpr⟩ := A.proj
  obtain ⟨e, he⟩ := delIso L n q w l δ hδ
  obtain ⟨hy, tr, htr, hu⟩ := trOf L n q w l A.R A.P A.ρ x δ T hδ
  have h2 := _root_.UpperTheory.V.Z.Win.T2.level_relation_two_x hP l L Ω s V0 O n r B J D b V h q w A x δ hw hx hδ T ph ta hok
  have h3 := _root_.UpperTheory.V.Pa.Lev.twoOf_alt hP l L Ω s V0 O n r B J D b V h q w A x δ hw hx hδ T ph ta hok
  have hg : ∀ j i m, ρ' (e (Pi.mulSingle (j, i) (Multiplicative.ofAdd 1))) m = T.act1 (1 + yV A.R j i) m := fun j i m => by
    obtain ⟨g, hg1, hg2⟩ := he j i
    exact Subtype.ext (by rw [hg2, hρ', hg1]; exact (hy j i m).symm)
  have hle : UIw1 l n w ≤ UIw n w := fun g hg j hj => opOf_le _ (hg j hj)
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ padicValNat l (qj w p.1 - 1)) := fun s => ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨hs, hk⟩ := opOf_tr A.ρ (UIw n w) (UIw1 l n w) hle ρ' hρ' hpr e
    (fun p : Fin q × Fin n => Pi.mulSingle p (Multiplicative.ofAdd 1)) (opOf_gen hl.out fun j => padicValNat l (qj w j - 1))
    (fun p : Fin q × Fin n => T.act1 (yV A.R p.1 p.2)) (fun p m => (hg p.1 p.2 m).trans (by rw [map_add (f := _), map_one]; rfl)) tr htr
  have ha : ∀ j, N ≤ padicValNat l (qj w j - 1) := fun j => by
    have h4 : 1 < qj w j := Finite.one_lt_card
    exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (by omega)).1 ((Nat.modEq_iff_dvd' h4.le).1 (hN j).symm)
  exact ⟨{ rN := A.rN, compat := A.compat, R := A.R, p := A.p, segmentWeightExponent := A.segmentWeightExponent, β := A.β, β_pair := A.β_pair
           M1 := fixd A.ρ (UC n w fun _ => ellC l _), tow1 := opOf_tow _, fin1 := A.fin, Mw := fixd A.ρ (UC n w fun _ => ⊤)
           act1 := T.act1, actw := T.actw, a := fun j => padicValNat l (qj w j - 1), le_a := ha
           ρ := ρ'.comp e.toMonoidHom, ρ_gen := hg, proj := opOf_proj ρ' e hpr
           tr := tr, tr_surj := hs, tr_ker := hk, tr_u := hu }, h3, h2⟩
end
end

section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Z.J
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
private theorem oneChar_unramU (hC : U3.CohInp) (hLM : LemmaM) (hLM' : LemmaM') (hLP : LemmaP) (hK : _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW)
    (hRI : _root_.UpperTheory.V.Th.RigidityFirstCase) (hRII : _root_.UpperTheory.V.Th.RigiditySecondCase) (hAd : _root_.UpperTheory.V.Z.J.AdmI_s) (hA : _root_.UpperTheory.V.Aut.AutomorphyUnramifiedCoefficientsAlt)
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (he : eO l c.O = 1) (hG : GD Ω K l e ψ) (ι : Qbar l ≃+* ℂ) (σ : G K Ω) (t : Qbar l)
    (ht : t = algebraMap c.O (PadicAlgCl l) ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ) : c.O) + 1 +
      (((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ))⁻¹ : c.Oˣ) : c.O)))
    (hne : ∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ →
      (ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ t) :
    Vlen Ω c e ψ ≠ ⊤ ∧ ∃ X : Finset (G K Ω →* GL (Fin 3) (Qbar l)),
      (∀ ρ ∈ X, _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ) ∧ (∀ ρ ∈ X, ∀ ρ' ∈ X, Af.RepIso ρ ρ' → ρ = ρ') ∧
      Vn Ω c e ψ ≤ 2 * ∑ ρ ∈ X, vl l ((ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t) := by
  classical
  obtain ⟨D⟩ := exists_dat hG
  obtain ⟨g₁, hM, hFin, hB, hW⟩ := hA Ω K l c N e ψ D he ι
  obtain ⟨U⟩ := exists_uLoc hC D
  obtain ⟨S⟩ := exists_ring hC D U g₁ hM
  obtain ⟨M⟩ := exists_model hC hLP D hM S
  have hmult : ∀ f : S.R →ₐ[c.O] PadicAlgCl l, HasMult D.η (push f S.r.hom) := fun f g => S.r.hasMult g
  let ρ : (S.R →ₐ[c.O] PadicAlgCl l) → (G K Ω →* GL (Fin 3) (Qbar l)) := fun f => D.rhoK (push f S.r.hom) (hmult f)
  have hσ : D.η (galEmb ℚ K Ω σ) = 1 := by
    rw [← MonoidHom.mem_ker, D.η_ker]
    exact galEmb_mem ℚ K Ω σ
  have htr : ∀ f, trDiff D.η D.Ψ S.r.hom (galEmb ℚ K Ω σ) f =
      (ρ f σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t := by
    intro f
    let g := galEmb ℚ K Ω σ
    have htrace : (r0 D.η D.Ψ g).mat.trace = (D.Ψ g : c.O) + 1 + ((D.Ψ g)⁻¹ : c.Oˣ).val := by
      simp [GG.mat, tor_val, Matrix.trace_diagonal, Fin.sum_univ_three, wt1]
    rw [trDiff, htrace, ht]
    congr 1
    exact AddMonoidHom.map_trace (f : S.R →+* PadicAlgCl l) _
  have hadm : ∀ f, TwoPt (η := D.η) S.r.hom f → _root_.UpperTheory.V.Z.J.Adm3U_s ι e N (ρ f) ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) (ρ f) := by
    intro f hf
    have hp := isPt_push D hM S f hf.1
    have hpush : IsPush (f.comp (entAlg c.O S.r.hom).val) S.r.hom (push f S.r.hom) :=
      fun g => ⟨rfl, fun a b => ⟨Algebra.subset_adjoin ⟨g, a, b, rfl⟩, rfl⟩⟩
    rcases (twoPt_shape S hG.l_odd hM f hf).1 with h | h
    · exact Or.inl (hAd D hM S f hf.1 (hmult f) ι h (hB U S _ _ _ hpush h))
    · exact Or.inr (_root_.UpperTheory.GalN.V.adm2B_rhoK_of_typeII_of_modular_extensions hC D hM hp ι h
        (hW U S _ _ hpush h (typeII_facts hC D hM hp h).1))
  obtain ⟨hlen, T, hT, hTo, hle⟩ := model_upper S M hG.l_odd hM hLM (hFin U S)
    (_root_.UpperTheory.V.Z.J.ptHyp_of_autB_of_lemW_of_isBase hC hK hRI hRII D hM S ι hB hW M.x₀ M.base) (galEmb ℚ K Ω σ) hσ
    fun f hf => by rw [htr]; exact sub_ne_zero.2 (hne _ (hadm f hf))
  have hV := vlen_le hC hLM' D hM S M
  have hinj : ∀ f ∈ T, ∀ f' ∈ T, Af.RepIso (ρ f) (ρ f') → f = f' := by
    rintro f hf f' hf' ⟨g, hg⟩
    obtain ⟨s, hs⟩ := (twoPt_shape S hG.l_odd hM f (hT.1 f hf)).2 f' (hT.1 f' hf').1 ⟨g, fun x hx => by
      rw [D.η_ker, ← range_galEmb] at hx
      obtain ⟨y, rfl⟩ := hx
      exact (congrArg Units.val (eq_mul_inv_iff_mul_eq.1 (hg y))).symm⟩
    exact hTo f hf f' hf' s hs
  refine ⟨ne_top_of_le_ne_top hlen hV, T.image ρ, fun x hx => ?_, fun x hx x' hx' h => ?_, ?_⟩
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    exact hadm f (hT.1 f hf)
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hx'
    rw [hinj f hf f' hf' h]
  · rw [Finset.sum_image fun f hf f' hf' h => hinj f hf f' hf' ⟨1, fun s => by rw [h, one_mul, inv_one, mul_one]⟩]
    simp only [← htr]
    exact (Chr.nrm_mono l hV hlen).trans hle
theorem UpperTheory.V.Z.J.oneCharU_of_katoTwoW_rig_admI_automorphy :
    U3.CohInp → LemmaM → LemmaM' → LemmaP → _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW → _root_.UpperTheory.V.Th.RigidityFirstCase → _root_.UpperTheory.V.Th.RigiditySecondCase → _root_.UpperTheory.V.Z.J.AdmI_s → _root_.UpperTheory.V.Aut.AutomorphyUnramifiedCoefficientsAlt → _root_.UpperTheory.V.Z.J.OneCharU_s := by
  intro hC hLM hLM' hLP hK hRI hRII hAd hA Ω _ _ _ K _ _ _ _ _ l _ c N _ e ψ hG ι σ t ht hne
  have hunram : ∃ (c' : Coef l) (ψ' : DirichletCharacter c'.O N), eO l c'.O = 1 ∧
      ∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) = ((ψ' a : c'.O) : PadicAlgCl l) := by
    classical
    have : NeZero (orderOf ψ) := ⟨fun h => hG.ord (h ▸ dvd_zero l)⟩
    obtain ⟨c', he, _⟩ := (coefSup l).2.1 (orderOf ψ) hG.ord
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot c'.O (orderOf ψ)
    have hζ' : IsPrimitiveRoot (ζ : PadicAlgCl l) (orderOf ψ) :=
      hζ.map_of_injective (f := c'.O.val) Subtype.val_injective
    have hmem : ∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) ∈ c'.O := by
      intro a
      by_cases ha : IsUnit a
      · obtain ⟨u, rfl⟩ := ha
        have hp : ψ u ^ orderOf ψ = 1 := by
          rw [← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
        have hp' : ((ψ u : c.O) : PadicAlgCl l) ^ orderOf ψ = 1 := by
          rw [← SubmonoidClass.coe_pow, hp]
          rfl
        obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hp'
        rw [← hi]
        exact pow_mem ζ.2 i
      · rw [ψ.map_nonunit ha]
        exact zero_mem _
    refine ⟨c', ⟨⟨⟨fun a => ⟨_, hmem a⟩, Subtype.ext ?_⟩, fun a b => Subtype.ext ?_⟩,
      fun a ha => Subtype.ext ?_⟩, he, fun _ => rfl⟩
    · show ((ψ 1 : c.O) : PadicAlgCl l) = 1
      rw [map_one]
      rfl
    · show ((ψ (a * b) : c.O) : PadicAlgCl l) = _
      rw [map_mul]
      rfl
    · show ((ψ a : c.O) : PadicAlgCl l) = 0
      rw [ψ.map_nonunit ha]
      rfl
  obtain ⟨c', ψ', he, hψ⟩ := hunram
  have hgd {O O' : Type} [CommRing O] [CommRing O'] (f : O →+* O')
      (hf : Function.Injective f) (χ : DirichletCharacter O N) :
      GD Ω K l e (χ.ringHomComp f) ↔ GD Ω K l e χ := by
    let F : DirichletCharacter O N →* DirichletCharacter O' N := MulChar.ringHomCompHom f
    have hF : Function.Injective F := MulChar.injective_ringHomComp hf
    have hord : orderOf (F χ) = orderOf χ := orderOf_injective F hF χ
    have hcomp (r : ℕ) (ξ : DirichletCharacter O N) : F (HV.comp r ξ) = HV.comp r (F ξ) := by
      ext u
      simp [F, HV.comp, MulChar.ringHomComp_apply]
    have hine : HV.comp l (F χ) ^ 2 = 1 ↔ HV.comp l χ ^ 2 = 1 := by
      rw [← hcomp, ← map_pow, map_eq_one_iff F hF]
    have hpar : PsiEven e (F χ) ↔ PsiEven e χ := by
      change f (χ (-1)) = (-1 : O') ^ e ↔ χ (-1) = (-1 : O) ^ e
      rw [show (-1 : O') ^ e = f ((-1) ^ e) by simp, hf.eq_iff]
    have hchi : F (chiP l χ) = chiP l (F χ) := by
      simp only [chiP, th0, lPrime, lPart, map_mul, map_inv, map_pow, hord, hcomp]
    have hker : (Chr.dirG ℚ Ω (chiP l (F χ))).ker = (Chr.dirG ℚ Ω (chiP l χ)).ker := by
      rw [← hchi]
      ext g
      simp only [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply]
      rw [Units.ext_iff, Units.ext_iff]
      simp only [MulChar.coe_toUnitHom, F, MulChar.ringHomCompHom_apply, MulChar.ringHomComp_apply,
        Units.val_one, ← map_one f, hf.eq_iff]
    change GD Ω K l e (F χ) ↔ GD Ω K l e χ
    constructor
    · intro h
      exact ⟨h.l_odd, h.e_pos, h.N_even, by simpa only [hord] using h.ord, hine.1 h.ine,
        hpar.1 h.par, h.quad, h.imag, h.l_cop, h.cop, by simpa only [hker] using h.eta, h.gen⟩
    · intro h
      exact ⟨h.l_odd, h.e_pos, h.N_even, by simpa only [hord] using h.ord, hine.2 h.ine,
        hpar.2 h.par, h.quad, h.imag, h.l_cop, h.cop, by simpa only [hker] using h.eta, h.gen⟩
  have h1 : ψ.ringHomComp c.O.val.toRingHom = ψ'.ringHomComp c'.O.val.toRingHom :=
    MulChar.ext' hψ
  have hG' : GD Ω K l e ψ' :=
    (hgd c'.O.val.toRingHom Subtype.val_injective ψ').1
      (h1 ▸ (hgd c.O.val.toRingHom Subtype.val_injective ψ).2 hG)
  obtain ⟨h2, h3⟩ := coefIndep Ω l c c' N e ψ ψ' hψ
  have h4 : ∀ g, Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g) =
      Units.map (algebraMap c'.O (PadicAlgCl l)).toMonoidHom (Chr.Psi l e (Chr.dirG ℚ Ω ψ') g) := by
    intro g
    simp only [Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow]
    congr 1
    exact Units.ext (hψ _)
  have h5 := congrArg Units.val (h4 (galEmb ℚ K Ω σ))
  have h6 := congrArg (fun u : (PadicAlgCl l)ˣ => (u⁻¹).val) (h4 (galEmb ℚ K Ω σ))
  rw [Ne, h2, h3]
  refine oneChar_unramU hC hLM hLM' hLP hK hRI hRII hAd hA Ω K l c' N e ψ' he hG' ι σ t ?_ hne
  rw [ht, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_one, map_one]
  exact congrArg₂ (· + ·) (congrArg (· + 1) h5) h6
end
end

section




section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp
open UpperTheory.V.Af
open scoped Matrix
namespace UpperTheory.V.Af.NewformAutomorphy
end UpperTheory.V.Af.NewformAutomorphy
theorem UpperTheory.GalN.V.newformAut0_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → NewformAut0 := by
  intro P k hk f l hl Ω _ _ _ ι W j hf hW K _ _ _ _ _ _ hK hirr
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  exact _root_.UpperTheory.V.Sd.up_quad_of_printed_results P ℚ K Ω l ι hK 2 one_le_two W hW (_root_.UpperTheory.V.Af.newformAutR_alt P k hk f l Ω ι W j hf) hirr
end
end
