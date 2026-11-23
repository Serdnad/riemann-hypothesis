module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ProjNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle023
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle088
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
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
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem dom_gen {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (t : Fin n → kˣ) : ∃ a b : Fin n → kˣ, Dom a ∧ Dom b ∧ t = a * b⁻¹ := by
  have key : ∃ c : kˣ, ∀ s : Fin n → kˣ, (s = 1 ∨ s = t) → ∀ i j : Fin n, i ≤ j →
      valuation k ((s i * c ^ (n - i) : kˣ) : k) ≤ valuation k ((s j * c ^ (n - j) : kˣ) : k) := by
    rcases isEmpty_or_nonempty (Fin n) with h | h
    · exact ⟨1, fun _ _ i => h.elim i⟩
    obtain ⟨p, hp⟩ := Finite.exists_min (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
    set c : kˣ := t p.2 * (t p.1)⁻¹ with hc
    have h1 : valuation k (c : k) ≤ 1 := by simpa using hp (p.1, p.1)
    refine ⟨c, fun s hs i j hij => ?_⟩
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    have h2 : valuation k (s i : k) * valuation k (c : k) ≤ valuation k (s j : k) := by
      rcases hs with rfl | rfl
      · simpa using h1
      · have := mul_le_mul_right (hp (i, j)) (valuation k (s i : k))
        refine this.trans (le_of_eq ?_)
        rw [← map_mul, ← Units.val_mul]
        congr 2
        simp
    have hj := j.2
    have hlt' : (i : ℕ) < j := hlt
    have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
    rw [e]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
    rw [← mul_assoc]
    exact mul_le_mul' h2 (mul_le_of_le_one_right' (pow_le_one' h1 _))
  obtain ⟨c, hc⟩ := key
  refine ⟨t * (fun i : Fin n => c ^ (n - (i : ℕ))), (1 : Fin n → kˣ) * (fun i : Fin n => c ^ (n - (i : ℕ))),
    hc t (Or.inr rfl), hc 1 (Or.inl rfl), ?_⟩
  simp

private theorem comm_dc {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H) (φ : Module.End A M) (h : ∀ g, Commute φ (ρ g)) :
    Commute φ (dc ρ K K' x) :=
  finsum_induction (fun e => Commute φ e) (Commute.zero_right φ) (fun _ _ h1 h2 => h1.add_right h2) fun _ => h _

section

variable {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ)

private theorem comm_at {j j' : Fin q} (h : j ≠ j') (g : GLw n (w j)) (g' : GLw n (w j')) :
    Commute (ρ (atJ n w j g)) (ρ (atJ n w j' g')) :=
  (Pi.mulSingle_commute (f := fun j => GLw n (w j)) h g g').map ρ

private theorem mem_UC (m : M) :
    m ∈ fixd ρ (UC n w C) ↔ ∀ j, m ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) :=
  by apply _root_.UpperTheory.Reformulated.B.Gr34.mem_UC <;> assumption

private theorem one_place (j : Fin q) (hq : IsUnit (qj w j : A)) :
    ∃ θ : (Fin n → ((w j).adicCompletion L)ˣ) →* (Module.End A (fixd ρ (UC n w C)))ˣ, ∀ t, Dom t →
      ∀ m : fixd ρ (UC n w C), ((θ t : Module.End A (fixd ρ (UC n w C))) m : M) =
        dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t) m := by
  obtain ⟨hmul, hunit, -⟩ := domMul _ n (C j) A M (ρ.comp (atJ n w j))
  have happ : ∀ x (v : fixd (ρ.comp (atJ n w j)) (iwC _ n (C j))),
      (hk (ρ.comp (atJ n w j)) (iwC _ n (C j)) x v : M) =
        dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) x v := fun x =>
    (hkApply A _ M (ρ.comp (atJ n w j)) _ _ x ((heckePairIwC _ n (C j)).1 x)).1
  have hcomm : ∀ j', j' ≠ j → ∀ g x, Commute (ρ (atJ n w j' g))
      (dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) x) := fun j' h g x =>
    comm_dc _ _ _ _ _ fun g' => comm_at ρ h g g'
  have hpres : ∀ x, ∀ m ∈ fixd ρ (UC n w C),
      dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) x m ∈ fixd ρ (UC n w C) := by
    intro x m hm
    rw [mem_UC] at hm ⊢
    intro j'
    by_cases e : j' = j
    · subst e
      exact happ x ⟨m, hm _⟩ ▸ (hk (ρ.comp (atJ n w j')) (iwC _ n (C j')) x ⟨m, hm _⟩).2
    · intro u hu
      have h1 := LinearMap.congr_fun (hcomm j' e u x).eq m
      rw [Module.End.mul_apply, Module.End.mul_apply, show ρ (atJ n w j' u) m = m from hm j' u hu] at h1
      exact h1
  let f : (Fin n → ((w j).adicCompletion L)ˣ) → Module.End A (fixd ρ (UC n w C)) := fun t =>
    (dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t)).restrict (hpres _)
  have hf : ∀ t m, (f t m : M) =
    dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t) m := fun _ _ => rfl
  have fmul : ∀ a b, Dom a → Dom b → f (a * b) = f a * f b := by
    intro a b ha hb
    ext m
    have h1 := congrArg Subtype.val (LinearMap.congr_fun (hmul a b ha hb) ⟨m, (mem_UC ρ C _).1 m.2 j⟩)
    rw [Module.End.mul_apply, happ, happ, happ] at h1
    exact h1.symm
  have funit : ∀ a, Dom a → IsUnit (f a) := by
    intro a ha
    obtain ⟨hi, hs⟩ := (Module.End.isUnit_iff _).1 (hunit hq a ha)
    refine (Module.End.isUnit_iff _).2 ⟨fun m m' h => ?_, fun m => ?_⟩
    · have := @hi ⟨m, (mem_UC ρ C _).1 m.2 j⟩ ⟨m', (mem_UC ρ C _).1 m'.2 j⟩ (Subtype.ext (by
        rw [happ, happ]; exact congrArg Subtype.val h))
      have h2 := congrArg Subtype.val this
      exact Subtype.ext h2
    · obtain ⟨v, hv⟩ := hs ⟨m, (mem_UC ρ C _).1 m.2 j⟩
      have hv' := congrArg Subtype.val hv
      rw [happ] at hv'
      refine ⟨⟨v, (mem_UC ρ C _).2 fun j' => ?_⟩, Subtype.ext hv'⟩
      by_cases e : j' = j
      · subst e
        exact v.2
      · intro u hu
        have hm : ρ (atJ n w j' u) v ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) := by
          intro g hg
          have h1 := LinearMap.congr_fun (comm_at ρ e u g).eq v
          rw [Module.End.mul_apply, Module.End.mul_apply, show ρ (atJ n w j g) v = v from v.2 g hg] at h1
          exact h1.symm
        have := @hi ⟨_, hm⟩ v (Subtype.ext (by
          rw [happ, happ]
          have h1 := LinearMap.congr_fun (hcomm j' e u (diagT _ (Fin n) a)).eq v
          rw [Module.End.mul_apply, Module.End.mul_apply, hv'] at h1
          rw [hv']
          exact h1.symm.trans ((mem_UC ρ C _).1 m.2 j' u hu)))
        exact congrArg Subtype.val this
  let P : Submonoid (Fin n → ((w j).adicCompletion L)ˣ) :=
    { carrier := {t | Dom t}
      one_mem' := dom_one
      mul_mem' := fun {a b} ha hb i j hij => by
        simp only [Pi.mul_apply, Units.val_mul, map_mul]
        exact mul_le_mul' (ha i j hij) (hb i j hij) }
  obtain ⟨θ, hθ, -⟩ := monoidExt _ _ P f (fun t => by
      obtain ⟨a, b, ha, hb, h⟩ := dom_gen t
      exact ⟨a, ha, b, hb, h⟩)
    (by
      have h := fmul 1 1 dom_one dom_one
      rw [mul_one] at h
      exact (funit 1 dom_one).mul_left_cancel (h.symm.trans (mul_one _).symm))
    (fun a ha b hb => fmul a b ha hb) (fun a ha => funit a ha)
  exact ⟨θ, fun t ht m => by rw [hθ t ht, hf]⟩

end

theorem UpperTheory.V.Pa.Lev.thetaQ :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ), (∀ j, IsUnit (qj w j : A)) → ∃ Θ, IsThetaQ ρ C Θ := by
  intro L _ _ n q w A M _ _ _ ρ C hq
  choose Θ hΘ using fun j => one_place ρ C j (hq j)
  refine ⟨Θ, hΘ, fun j j' t t' => ?_⟩
  by_cases e : j = j'
  · subst e
    exact (Commute.all t t').map _
  have hd : ∀ a b, Dom a → Dom b → Commute (Θ j a) (Θ j' b) := by
    intro a b ha hb
    refine Units.ext (LinearMap.ext fun m => Subtype.ext ?_)
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hΘ j a ha, hΘ j' b hb,
      hΘ j' b hb, hΘ j a ha]
    exact LinearMap.congr_fun (comm_dc _ _ _ _ _ fun g' =>
      (comm_dc _ _ _ _ _ fun g => comm_at ρ (Ne.symm e) g' g).symm).eq (m : M)
  obtain ⟨a, b, ha, hb, rfl⟩ := dom_gen t
  obtain ⟨c, d, hc, hd', rfl⟩ := dom_gen t'
  rw [map_mul, map_mul, map_inv, map_inv]
  exact ((hd a c ha hc).mul_right (hd a d ha hd').inv_right).mul_left
    ((hd b c hb hc).mul_right (hd b d hb hd').inv_right).inv_left
end
