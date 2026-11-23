module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ellC_index (l : ℕ) [hl : Fact l.Prime] (M : Type) [CommGroup M] [Finite M] :
    ∃ n : ℕ, (ellC l M).index = l ^ n := by
  have hp : IsPGroup l (M ⧸ ellC l M) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' l hl.out.ne_one
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have h1 : orderOf (x ^ l ^ e) ∣ m := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, ← he, pow_orderOf_eq_one])
    exact Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm).symm
  exact IsPGroup.iff_card.1 hp

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem isUnit_iff_val (p : 𝒪[k]) : IsUnit p ↔ valuation k (p : k) = 1 :=
  (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one

private theorem unif_of_ord {x : kˣ} (hx : ord k x = 1) : IsUnif x := by
  have hv : valuation k (x : k) = uniformizer k := by
    obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact uniformizer_ne_zero hy.symm
    have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hy
    have h2 := ord_mul k (x * (Units.mk0 y hy0)⁻¹) (Units.mk0 y hy0)
    rw [inv_mul_cancel_right, hx, h1] at h2
    have h3 := ord_eq_zero_iff.1 (show ord k (x * (Units.mk0 y hy0)⁻¹) = 0 by omega)
    have h4 : (x : k) = ((x * (Units.mk0 y hy0)⁻¹ : kˣ) : k) * y := by simp [hy0]
    rw [h4, map_mul, h3, one_mul, hy]
  have hlt : valuation k (x : k) < 1 := hv ▸ uniformizer_lt_one
  refine ⟨⟨x, hlt.le⟩, ⟨fun h => hlt.ne ((isUnit_iff_val _).1 h), fun a b hab => ?_⟩, rfl⟩
  by_contra hn
  rw [not_or, isUnit_iff_val, isUnit_iff_val] at hn
  have ha : valuation k (a : k) < 1 := lt_of_le_of_ne a.2 hn.1
  have hb : valuation k (b : k) ≤ uniformizer k := le_uniformizer_iff.2 (lt_of_le_of_ne b.2 hn.2)
  have h5 : valuation k (x : k) = valuation k (a : k) * valuation k (b : k) := by
    rw [← map_mul]; exact congrArg (fun z : 𝒪[k] => valuation k (z : k)) hab
  have h6 : valuation k (a : k) * valuation k (b : k) < 1 * uniformizer k :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos ha hb zero_le (zero_lt_iff.2 uniformizer_ne_zero)
  rw [← h5, hv, one_mul] at h6
  exact lt_irrefl _ h6

private theorem exists_lift {H : Type} [Group H] [TopologicalSpace H] (f : H →* kˣ) (hf : Continuous f)
    (h1 : ∀ s, valuation k (f s : k) = 1) :
    ∃ g : H →* 𝒪[k]ˣ, (∀ s, Units.map (algebraMap 𝒪[k] k).toMonoidHom (g s) = f s) ∧
      IsOpen (((Units.map (residue 𝒪[k]).toMonoidHom).comp g).ker : Set H) := by
  let g0 : H →* 𝒪[k] :=
    { toFun := fun s => ⟨f s, (h1 s).le⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by simp) }
  refine ⟨g0.toHomUnits, fun s => Units.ext rfl, ?_⟩
  have e : (((Units.map (residue 𝒪[k]).toMonoidHom).comp g0.toHomUnits).ker : Set H) =
      (fun s => (f s : k) - 1) ⁻¹' {x : k | valuation k x < 1} := by
    ext s
    have e1 : (s ∈ ((Units.map (residue 𝒪[k]).toMonoidHom).comp g0.toHomUnits).ker) ↔ residue 𝒪[k] (g0 s - 1) = 0 := by
      rw [MonoidHom.mem_ker, Units.ext_iff, map_sub, map_one, sub_eq_zero]; rfl
    rw [SetLike.mem_coe, e1, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_val]
    exact ⟨fun h => lt_of_le_of_ne (g0 s - 1).2 h, fun h => ne_of_lt h⟩
  rw [e]
  refine IsOpen.preimage ((Units.continuous_val.comp hf).sub continuous_const) ?_
  simpa only [Valuation.restrict_lt_iff_lt_embedding, map_one] using
    (Valuation.isOpen_ball (v := valuation k) 1)

end Loc

theorem UpperTheory.V.Pa.Lev.artinEl :
    GlobalTheory.Published.TameLocal → ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (a : Weil hB →* (w.adicCompletion E)ˣ), IsLocalArtin hB a → ∀ fr τ : G E Ω, fr ∈ Dec (F := E) Bq → IsFrob (F := E) Bq (normV w) fr⁻¹ → GlobalTheory.TameQuot.IsProGen E Bq l τ → resCard (w.adicCompletion E) = normV w ∧ ∃ (h1 : fr ∈ Weil hB) (h2 : τ ∈ Weil hB), IsUnif (a ⟨fr, h1⟩) ∧ IsGenMod _ (ellC l _) (a ⟨τ, h2⟩) ∧ (∀ (σ : G E Ω) (h3 : σ ∈ Weil hB), σ ∈ GlobalTheory.TameQuot.ineKer E Bq l → a ⟨σ, h3⟩ ∈ unitsC _ (ellC l _)) ∧ (τ ^ normV w)⁻¹ * (fr⁻¹ * τ * fr) ∈ GlobalTheory.TameQuot.ineKer E Bq l := by
  intro hT l _ E Ω _ _ _ _ _ Bq w hB hl a ha fr τ hfr hF hτ
  have h0 : fr⁻¹ ∈ Weil hB := mem_Weil_of_isFrob hB hF
  have h1 : fr ∈ Weil hB := (inv_mem_iff (H := Weil hB)).1 h0
  have hval : ∀ s : Ine (F := E) Bq,
      valuation (w.adicCompletion E) ((a.comp (ineIncl hB) s : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := fun s => by
    refine ord_eq_zero_iff.1 ?_
    rw [MonoidHom.comp_apply, ha.ord_eq, deg_eq_zero_iff.2 s.2, neg_zero]
  obtain ⟨g, hg, hop⟩ := exists_lift (a.comp (ineIncl hB)) ha.cont hval
  set r := (Units.map (residue 𝒪[w.adicCompletion E]).toMonoidHom).comp g with hr
  have hrs : Function.Surjective r := fun y => by
    obtain ⟨d, rfl⟩ := surjective_units_map_of_local_ringHom (residue 𝒪[w.adicCompletion E]) residue_surjective
      inferInstance y
    obtain ⟨s, hs⟩ := ha.surj (Units.map (algebraMap 𝒪[w.adicCompletion E] (w.adicCompletion E)).toMonoidHom d)
    have hs0 : deg s = 0 := by
      have := ha.ord_eq s
      rw [hs, ord_eq_zero ((isUnit_iff_val _).1 d.isUnit)] at this
      omega
    refine ⟨⟨s, deg_eq_zero_iff.1 hs0⟩, ?_⟩
    have h5 := (hg ⟨s, deg_eq_zero_iff.1 hs0⟩).trans hs
    have h6 : g ⟨s, deg_eq_zero_iff.1 hs0⟩ = d := Units.ext (Subtype.ext (congrArg Units.val h5))
    rw [hr, MonoidHom.comp_apply, h6]
  have hopen : ∀ C : Subgroup 𝓀[w.adicCompletion E]ˣ, IsOpen ((C.comap r : Subgroup _) : Set (Ine (F := E) Bq)) :=
    fun C => Subgroup.isOpen_mono (fun s hs => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hs]; exact C.one_mem) hop
  have hker : GlobalTheory.TameQuot.proKer l (Ine (F := E) Bq) ≤ (ellC l _).comap r := fun s hs =>
    GlobalTheory.TameQuot.mem_proKer.1 hs _ inferInstance (hopen _) (by
      rw [Subgroup.index_comap_of_surjective _ hrs]; exact ellC_index l _)
  refine ⟨resCard_eq_normV _, h1, Ine_le_Weil hB hτ.1, unif_of_ord ?_, ⟨g ⟨τ, hτ.1⟩, hg _, ?_⟩, fun σ h3 hσ => ?_, ?_⟩
  · have h2 : deg (⟨fr, h1⟩ : Weil hB)⁻¹ = 1 := deg_eq_one_iff.2 hF
    rw [ha.ord_eq, ← deg_inv, h2]
  · refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨s, rfl⟩ := hrs y
    set C := Subgroup.zpowers (r ⟨τ, hτ.1⟩) ⊔ ellC l _ with hC
    have hle : Subgroup.zpowers τ ⊔ GlobalTheory.TameQuot.ineKer E Bq l ≤ (C.comap r).map (Ine (F := E) Bq).subtype := by
      refine sup_le ((Subgroup.zpowers_le).2 ⟨⟨τ, hτ.1⟩, ?_, rfl⟩) (Subgroup.map_mono (hker.trans ?_))
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.comap_mono le_sup_right
    have h4 : (s : G E Ω) ∈ closure (Subtype.val '' ((C.comap r : Subgroup _) : Set (Ine (F := E) Bq))) :=
      closure_mono (fun z hz => hle hz) (hτ.2 s.2)
    have h5 : s ∈ closure ((C.comap r : Subgroup _) : Set (Ine (F := E) Bq)) := closure_subtype.2 h4
    rw [(Subgroup.isClosed_of_isOpen _ (hopen C)).closure_eq] at h5
    exact h5
  · obtain ⟨s, hs, rfl⟩ := hσ
    exact ⟨g s, hker hs, hg s⟩
  · have hτd : τ ∈ Dec (F := E) Bq := Weil_le_Dec hB (Ine_le_Weil hB hτ.1)
    have := ((hT.1 E Ω l Bq w hB hl).2.2.2.2.2 ⟨fr⁻¹, inv_mem hfr⟩ ⟨τ, hτd⟩ hF hτ).2.1
    simpa using this
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Pa.Lev

def homComp {l : ℕ} [Fact l.Prime] {L : Loc} {G G' G'' : Glob l L} (e : G.Hom G') (h : G'.Hom G'') : G.Hom G'' where
  p := h.p.comp e.p
  cont := h.cont.comp e.cont
  surj := h.surj.comp e.surj
  η g := (h.η _).trans (e.η g)
  c := by rw [MonoidHom.comp_apply, e.c, h.c]
  ε g := (h.ε _).trans (e.ε g)
  φ v g := by rw [MonoidHom.comp_apply, e.φ, h.φ]
  φu v g := by rw [MonoidHom.comp_apply, e.φu, h.φu]

def emb (O R : Type) [CommRing O] [CommRing R] [Algebra O R] {q n : ℕ} (j : Fin q) : MvPolynomial (Fin n) O →+* PU R q n :=
  (MvPolynomial.rename fun i => (j, i) : MvPolynomial (Fin n) R →ₐ[R] PU R q n).toRingHom.comp (MvPolynomial.map (algebraMap O R))

structure HkHyp (O : Type) {R V : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup V] [Module R V] {q n : ℕ}
    (Nq : Fin q → ℕ) (act : PU R q n →ₐ[R] Module.End R V) (e : Fin q → Module.End R V) (W : Fin q → Submodule R V) : Prop where
  ee : ∀ j j', Commute (e j) (e j')
  eX : ∀ j j' i, j ≠ j' → Commute (e j) (act (MvPolynomial.X (j', i)))
  esym : ∀ j (z : MvPolynomial (Fin n) O), z.IsSymmetric → Commute (e j) (act (emb O R j z))
  sum : ∀ j (ι : Type) [Fintype ι] (a b : ι → MvPolynomial (Fin n) O), Hk.IsDual a b →
    ∑ i, act (emb O R j (a i)) * e j * act (emb O R j (b i)) = act (emb O R j (Hk.NN n (Nq j : O)))
  WX : ∀ j j' i, j ≠ j' → ∀ v ∈ W j, act (MvPolynomial.X (j', i)) v ∈ W j
  We : ∀ j j', j ≠ j' → ∀ v ∈ W j, e j' v ∈ W j
  tr : ∀ j (x : MvPolynomial (Fin n) O), ∀ v ∈ W j,
    e j (act (emb O R j x) v) = act (emb O R j (Hk.dd (Hk.NN n (Nq j : O) * x))) v

section Th

variable {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

abbrev qj (w : Fin q → Plc L) (j : Fin q) : ℕ := resCard ((w j).adicCompletion L)

structure ThData (l : ℕ) (ρ : Representation A (GV n w) M) (x δ : ∀ j, ((w j).adicCompletion L)ˣ) where
  Θ1 : ∀ j, (Fin n → ((w j).adicCompletion L)ˣ) →* (Module.End A (fixd ρ (UC n w fun _ => ellC l _)))ˣ
  h1 : IsThetaQ ρ (fun _ => ellC l _) Θ1
  Θw : ∀ j, (Fin n → ((w j).adicCompletion L)ˣ) →* (Module.End A (fixd ρ (UC n w fun _ => ⊤)))ˣ
  hw : IsThetaQ ρ (fun _ => ⊤) Θw
  act1 : PUY A q n →ₐ[A] Module.End A (fixd ρ (UC n w fun _ => ellC l _))
  act_uVariable_eq_pow : ∀ j i, act1 (uV A j i) = ((qj w j : A) ^ (i : ℕ)) • (Θ1 j (Pi.mulSingle i (x j)) : Module.End A _)
  act_yVariable : ∀ j i, act1 (1 + yV A j i) = (Θ1 j (Pi.mulSingle i (δ j)) : Module.End A _)
  actw : PU A q n →ₐ[A] Module.End A (fixd ρ (UC n w fun _ => ⊤))
  actw_u : ∀ j i, actw (MvPolynomial.X (j, i)) = ((qj w j : A) ^ (i : ℕ)) • (Θw j (Pi.mulSingle i (x j)) : Module.End A _)

end Th

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r} {J : Ideal B.B} {D : ℕ} {b : TWBase (pairOf B.u) J Empty D}
  {V : s.Lev} {h : (globOf r V).Hom (globOf r V0)} {q : ℕ} {w : Fin q → Plc L}

def LocOk (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ) (ph ta : Fin q → (globOf r V).G₀) : Prop :=
  ∃ ι : Qbar l ≃+* ℂ, (∀ m : A.P, (∀ y : LevPt A ι, y.sp m = 0) → m = 0) ∧ ∀ (y : LevPt A ι) j,
    LocRel l (x j) (δ j) (y.σ j).ρ ((mat y.rep (ph j)).map ι) ((mat y.rep (ta j)).map ι)

end UpperTheory.V.Pa.Lev
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lt_imp_mul_prod_le_of_b_le_one_le_a_mul_le {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a b : Fin n → G) (hb1 : ∀ l, b l ≤ 1) (hba : ∀ l, b l ≤ a l) (hab : ∀ l, a l * b l ≤ 1) :
    ∀ i j : Fin n, i < j → a i * ∏ l, b l ≤ a j := by
  classical
  intro i j hij
  have hne : j ≠ i := ne_of_gt hij
  have hsplit : ∏ l, b l = b i * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩),
      Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  calc a i * ∏ l, b l = (a i * b i) * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
        rw [hsplit, mul_assoc]
    _ ≤ 1 * (b j * 1) := mul_le_mul' (hab i) (mul_le_mul' le_rfl (Finset.prod_le_one' (fun l _ => hb1 l)))
    _ ≤ a j := by rw [one_mul, mul_one]; exact hba j

private theorem le_imp_mul_pow_sub_le_of_c_le_one_mul_le {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a : Fin n → G) (c : G) (hc1 : c ≤ 1) (hc : ∀ i j : Fin n, i < j → a i * c ≤ a j) (i j : Fin n)
    (hij : i ≤ j) : a i * c ^ (n - (i : ℕ)) ≤ a j * c ^ (n - (j : ℕ)) := by
  rcases lt_or_eq_of_le hij with h | h
  · obtain ⟨d, hd⟩ : ∃ d, n - (i : ℕ) = (n - (j : ℕ)) + d + 1 :=
      ⟨(j : ℕ) - i - 1, by have := j.isLt; have := Fin.lt_iff_val_lt_val.mp h; omega⟩
    calc a i * c ^ (n - (i : ℕ)) = (a i * c) * c ^ d * c ^ (n - (j : ℕ)) := by
          rw [hd, pow_add, pow_add, pow_one]; ac_rfl
      _ ≤ a j * 1 * c ^ (n - (j : ℕ)) := mul_le_mul' (mul_le_mul' (hc i j h) (pow_le_one' hc1 d)) le_rfl
      _ = a j * c ^ (n - (j : ℕ)) := by rw [mul_one]
  · rw [h]

private theorem thetaMap_split {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ c : kˣ, ∀ s : Fin n → kˣ, (s = 1 ∨ s = t) → ∀ i j : Fin n, i ≤ j →
      valuation k ((s i * c ^ (n - i) : kˣ) : k) ≤ valuation k ((s j * c ^ (n - j) : kˣ) : k) := by
  classical
  let φ : kˣ →* (ValueGroupWithZero k)ˣ := Units.map (valuation k).toMonoidWithZeroHom.toMonoidHom
  have hφ : ∀ u : kˣ, valuation k (u : k) = ((φ u : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) :=
    fun u => rfl
  let w : Fin n → kˣ := fun l => if φ (t l) ≤ 1 then t l else (t l)⁻¹
  have hw1 : ∀ l, φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact h
    · rw [map_inv]; exact inv_le_one'.mpr (le_of_lt (not_le.mp h))
  have hwa : ∀ l, φ (w l) ≤ φ (t l) := fun l => by
    simp only [w]
    split_ifs with h
    · exact le_rfl
    · rw [map_inv]
      exact (inv_le_one'.mpr (le_of_lt (not_le.mp h))).trans (le_of_lt (not_le.mp h))
  have hwab : ∀ l, φ (t l) * φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact mul_le_one' h h
    · rw [map_inv, mul_inv_cancel]
  refine ⟨∏ l, w l, ?_⟩
  have hC : φ (∏ l, w l) = ∏ l, φ (w l) := map_prod φ _ _
  have hc1 : ∏ l, φ (w l) ≤ 1 := Finset.prod_le_one' (fun l _ => hw1 l)
  intro s hs i j hij
  rw [hφ, hφ, Units.val_le_val, map_mul, map_mul, map_pow, map_pow, hC]
  rcases hs with h | h
  · rw [h]
    simpa using le_imp_mul_pow_sub_le_of_c_le_one_mul_le (fun _ => (1 : (ValueGroupWithZero k)ˣ)) _ hc1
      (fun _ _ _ => by rw [one_mul]; exact hc1) i j hij
  · rw [h]
    exact le_imp_mul_pow_sub_le_of_c_le_one_mul_le (fun l => φ (t l)) _ hc1
      (lt_imp_mul_prod_le_of_b_le_one_le_a_mul_le (fun l => φ (t l)) (fun l => φ (w l)) hw1 hwa hwab) i j hij

private theorem thetaMap_dc {A M A' M' G : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing A'] [AddCommGroup M']
    [Module A' M'] [Group G] (ρ : Representation A G M) (ρ' : Representation A' G M') (K K' : Subgroup G) (x : G)
    (hx : FinOrb K K' x) (f : M →+ M') (hf : ∀ g m, f (ρ g m) = ρ' g (f m)) (m : M) :
    dc ρ' K K' x (f m) = f (dc ρ K K' x m) := by
  haveI := hx.fintype

  simp only [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hf]

private theorem thetaMap_ext {A N A' N' T : Type} [CommRing A] [AddCommGroup N] [Module A N] [CommRing A'] [AddCommGroup N']
    [Module A' N'] [Group T] (θ : T →* (Module.End A N)ˣ) (θ' : T →* (Module.End A' N')ˣ) (g : N → N') (t b : T)
    (hb : ∀ m, (θ' b).val (g m) = g ((θ b).val m)) (ha : ∀ m, (θ' (b * t)).val (g m) = g ((θ (b * t)).val m)) (m : N) :
    (θ' t).val (g m) = g ((θ t).val m) := by
  have key : ∀ y, ((θ' b)⁻¹).val ((θ' b).val y) = y := fun y => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  have h1 := ha m
  simp only [map_mul, Units.val_mul, Module.End.mul_apply] at h1
  rw [← hb] at h1
  rw [← key ((θ' t).val (g m)), h1, key]

theorem UpperTheory.V.Pa.Lev.thetaMap :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (A M A' M' : Type) [CommRing A] [AddCommGroup M] [Module A M] [CommRing A'] [AddCommGroup M'] [Module A' M'] (ρ : Representation A (GV n w) M) (ρ' : Representation A' (GV n w) M') (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (Θ) (Θ'), IsThetaQ ρ C Θ → IsThetaQ ρ' C Θ' → ∀ f : M →+ M', (∀ g m, f (ρ g m) = ρ' g (f m)) → ∀ j t (m : fixd ρ (UC n w C)) (m' : fixd ρ' (UC n w C)), (m' : M') = f m → ((Θ' j t).val m').val = f ((Θ j t).val m).val := by
  intro L _ _ n q w A M A' M' _ _ _ _ _ _ ρ ρ' C Θ Θ' hΘ hΘ' f hf j t m m' hm
  let g : fixd ρ (UC n w C) → fixd ρ' (UC n w C) := fun x =>
    ⟨f x, show ∀ u ∈ UC n w C, ρ' u (f x) = f x from fun u hu => by
      rw [← hf]
      exact congrArg f ((show ∀ u ∈ UC n w C, ρ u x = x from x.2) u hu)⟩
  have hdom : ∀ s, Dom s → ∀ x, (Θ' j s).val (g x) = g ((Θ j s).val x) := by
    intro s hs x
    apply Subtype.ext
    rw [hΘ'.1 j s hs (g x)]
    change _ = f (((Θ j s).val x : M))
    rw [hΘ.1 j s hs x]
    exact thetaMap_dc _ _ _ _ _ ((heckePairIwC _ n (C j)).1 _) f (fun g' y => hf _ y) x
  obtain ⟨c, hc⟩ := thetaMap_split t
  let b : Fin n → (HeightOneSpectrum.adicCompletion L (w j))ˣ := fun i => c ^ (n - (i : ℕ))
  have hb : Dom b := fun i i' h => by simpa [b] using hc 1 (Or.inl rfl) i i' h
  have hbt : Dom (b * t) := fun i i' h => by
    have := hc t (Or.inr rfl) i i' h
    simpa [b, Pi.mul_apply, mul_comm] using this
  have key := thetaMap_ext (Θ j) (Θ' j) g t b (hdom b hb) (hdom (b * t) hbt) m
  have hm' : m' = g m := Subtype.ext hm
  rw [hm', key]
end
