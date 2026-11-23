module

public import Development.EtaleCohomology.EtaleSheaves.Bundle062
public import Development.EtaleCohomology.EtaleSheaves.AlgebraicIntegralClosure.AicLoc
public import Development.EtaleCohomology.EtaleSheaves.Bundle041
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.EtaleCohomology.EtaleSheaves.Bundle063
public import Mathlib.Topology.Instances.ZMod
public import Development.EtaleCohomology.EtaleSheaves.Bundle064
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StalkAICRingPf

theorem aic_loc {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hR : AIC R) : AIC S := by
  intro p hp hn
  rcases subsingleton_or_nontrivial R with hR1 | hR1
  · refine ⟨0, ?_⟩
    have h01 : (0 : S) = 1 := by
      rw [← map_zero (algebraMap R S), ← map_one (algebraMap R S), Subsingleton.elim (0 : R) 1]
    exact @Subsingleton.elim _ (subsingleton_of_zero_eq_one h01) _ _
  set n := p.natDegree with hnd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples M (Finset.univ : Finset (Fin n)) (fun i => p.coeff i)
  choose r hr using fun i : Fin n => hb i (Finset.mem_univ _)
  set β : S := algebraMap R S b with hβ
  have hu : IsUnit β := IsLocalization.map_units S b
  set q : R[X] := X ^ n + ∑ i : Fin n, C (r i * (b : R) ^ (n - 1 - i)) * X ^ (i : ℕ) with hq
  have hqm : q.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hqd : q.natDegree = n := by
    rw [hq, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]; exact degree_sum_fin_lt _
  obtain ⟨c, hc⟩ := hR q hqm (hqd ▸ hn)
  refine ⟨hu.unit⁻¹ * algebraMap R S c, ?_⟩
  have key : β ^ n * p.eval (hu.unit⁻¹ * algebraMap R S c) = algebraMap R S (q.eval c) := by
    conv_lhs => rw [hp.as_sum]
    rw [← hnd, ← Fin.sum_univ_eq_sum_range]

    simp only [hq, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, map_add (f := _), map_pow, map_sum, map_mul, mul_add,
    Finset.mul_sum]
    congr 1
    · rw [← mul_pow, ← mul_assoc, hu.mul_val_inv, one_mul]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr i]
      have hβn : β ^ n = β ^ 1 * β ^ (n - 1 - (i : ℕ)) * β ^ (i : ℕ) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      simp only [Algebra.smul_def, ← hβ]
      rw [hβn, mul_pow]
      have h1 : β ^ (i : ℕ) * (↑hu.unit⁻¹ : S) ^ (i : ℕ) = 1 := by rw [← mul_pow, hu.mul_val_inv, one_pow]
      linear_combination (β ^ 1 * β ^ (n - 1 - (i:ℕ)) * p.coeff i * algebraMap R S c ^ (i:ℕ)) * h1
  rw [hc, map_zero] at key
  exact (hu.pow n).mul_right_eq_zero.1 key

theorem StalkAICRing_of : LateralTheory.E.FibreEqvPf.StalkAICRing := by
  intro S hS x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let _ := TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨x, hxU⟩ : U)
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact aic_loc (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (hS.2 U hU ⟨x, hxU⟩)

end LateralTheory.E.StalkAICRingPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial LateralTheory.E.t_E2Cut LateralTheory.E.AICOpenPf

namespace LateralTheory.E.BaseAICPf

theorem aic_of_local {Z : Scheme.{0}} [IsIntegral Z]
    (hloc : ∀ (W : Z.Opens) (y : Z), y ∈ W → ∃ U : Z.Opens, y ∈ U ∧ U ≤ W ∧ AIC Γ(Z, U))
    (W : Z.Opens) (hW : (W : Set Z).Nonempty) : AIC Γ(Z, W) := by
  intro p hm hd
  have : Nonempty W := ⟨⟨_, hW.some_mem⟩⟩
  have hcov : ∀ x : W, ∃ U : Z.Opens, (x : Z) ∈ U ∧ U ≤ W ∧ AIC Γ(Z, U) := fun x => hloc W x x.2
  choose U hxU hUW hUa using hcov
  have hne : ∀ x : W, Nonempty (U x) := fun x => ⟨⟨_, hxU x⟩⟩
  let ψ := Z.germToFunctionField W
  have hroot : ∀ x : W, ∃ β : Z.functionField, (p.map ψ.hom).eval β = 0 := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hUa x
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    obtain ⟨r, hr⟩ := hA (p.map ρ) (hm.map ρ) (by rw [hm.natDegree_map]; exact hd)
    refine ⟨Z.germToFunctionField (U x) r, ?_⟩
    rw [← gtf_res_hom (homOfLE (hUW x)), ← Polynomial.map_map, Polynomial.eval_map_apply, hr, map_zero]
  obtain ⟨β, hβ⟩ := hroot ⟨_, hW.some_mem⟩
  have hsec : ∀ x : W, ∃ t : Γ(Z, U x), Z.germToFunctionField (U x) t = β := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hUa x
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    exact roots_in (Z.germToFunctionField (U x)).hom hA _ (p.map ρ) rfl (hm.map ρ) β
      (by rw [Polynomial.map_map, gtf_res_hom]; exact hβ)
  choose sf hsf using hsec
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have := hne i; have := hne j
    have hij : ((U i ⊓ U j : Z.Opens) : Set Z).Nonempty :=
      nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨_, hxU i⟩ ⟨_, hxU j⟩
    have : Nonempty (U i ⊓ U j : Z.Opens) := ⟨⟨_, hij.some_mem⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.germToFunctionField _ (Z.presheaf.map _ (sf i)) = Z.germToFunctionField _ (Z.presheaf.map _ (sf j))
    rw [gtf_res, gtf_res, hsf, hsf]
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (U := U) (V := W) (iUV := fun x => homOfLE (hUW x))
    (hcover := fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU _⟩) (sf := sf) (h := hcompat)
  have hsβ : ψ s = β := by
    have h0 := hs ⟨_, hW.some_mem⟩
    have := hne ⟨_, hW.some_mem⟩
    rw [← hsf ⟨_, hW.some_mem⟩, ← gtf_res (homOfLE (hUW ⟨_, hW.some_mem⟩)) s]
    exact congrArg _ h0
  obtain ⟨t, ht⟩ : ∃ t : Γ(Z, W), ψ t = β := ⟨s, hsβ⟩
  refine ⟨t, Z.germToFunctionField_injective W ?_⟩
  rw [map_zero]
  have key : ψ.hom (p.eval t) = (p.map ψ.hom).eval (ψ.hom t) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  change ψ.hom (p.eval t) = 0
  rw [key]; change (p.map ψ.hom).eval (ψ t) = 0
  rw [ht]; exact hβ

def BaseInt : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, IsIntegral (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})

def BaseLoc : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, ∀ (W : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens)
  (y : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})), y ∈ W →
  ∃ U : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens, y ∈ U ∧ U ≤ W ∧
    AIC Γ((Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}), U)

def BaseLocLoc : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, ∀ (W : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens)
  (y : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})), y ∈ W →
  ∃ U : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens, y ∈ U ∧ U ≤ W ∧
    ∃ V : Z.Opens, IsAffineOpen V ∧ (V : Set Z).Nonempty ∧
    ∃ f : Γ(Z, V) →+* Γ((Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}), U), ∃ M : Submonoid Γ(Z, V),
      @IsLocalization _ _ M _ _ f.toAlgebra

theorem BaseLoc_of (h : BaseLocLoc) : BaseLoc := by
  intro Z S c _ _ _ hZ hS x W y hy
  obtain ⟨U, hyU, hUW, V, hV, hne, f, M, hM⟩ := h c hZ hS x W y hy
  letI := f.toAlgebra
  exact ⟨U, hyU, hUW, LateralTheory.E.BaseAICPf.Loc.aic_loc M (hZ.2 V hV hne)⟩

theorem BaseAIC_of (h1 : BaseInt) (h2 : BaseLoc) : LateralTheory.E.FibreEqvPf.BaseAIC := by
  intro Z S c _ _ _ hZ hS x
  have : IsIntegral (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}) := h1 c hZ hS x
  exact ⟨this, fun U _ hne => aic_of_local (h2 c hZ hS x) U hne⟩

end LateralTheory.E.BaseAICPf
end
end

section

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.SpecAICPf

theorem aic_equiv {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A') (h : AIC A) : AIC A' := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _) (by rwa [natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have := congrArg e ha
  rw [eval_map, ← coe_eval₂RingHom, map_zero] at this
  rw [← this]

  simp [eval₂_eq_sum_range, eval_eq_sum_range, map_sum]

theorem card_roots_of_aic {A : Type} [CommRing A] [IsDomain A] (h : AIC A) :
    ∀ (n : ℕ) (p : A[X]), p.Monic → p.natDegree = n → Multiset.card p.roots = n := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    rw [eq_one_of_monic_natDegree_zero hp hn]; simp
  | succ n ih =>
    intro p hp hn
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hdeg : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    have e := mul_divByMonic_eq_iff_isRoot.2 ha
    have hq : (p /ₘ (X - C a)).Monic := Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [e]; exact hp)
    rw [← e, roots_mul (by rw [e]; exact hp.ne_zero), roots_X_sub_C, Multiset.card_add, ih _ hq hdeg]
    simp; omega

theorem aic_localization {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (M : Submonoid B)
    [IsLocalization M S] (h : AIC B) : AIC S := by
  classical
  intro p hp hd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M (Finset.image p.coeff (Finset.range (p.natDegree + 1)))
  set r : S := algebraMap B S b
  have hl : p.scaleRoots r ∈ lifts (algebraMap B S) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · obtain ⟨t, ht⟩ := hb (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      refine ⟨t * b ^ (p.natDegree - (i + 1)), ?_⟩
      rw [map_mul, ht, map_pow, Algebra.smul_def]
      simp only [r]
      have : p.natDegree - i = (p.natDegree - (i + 1)) + 1 := by omega
      rw [this, pow_succ]; ring
    · subst hi; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
    · rw [coeff_eq_zero_of_natDegree_lt hi]; exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff r).2 hp)
  obtain ⟨β, hβ⟩ := h q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)
  have hru : IsUnit r := IsLocalization.map_units S b
  refine ⟨algebraMap B S β * hru.unit⁻¹, ?_⟩
  have h1 := scaleRoots_eval₂_mul (p := p) (RingHom.id S) (algebraMap B S β * hru.unit⁻¹) r
  simp only [eval₂_id, RingHom.id_apply] at h1
  have h2 : r * (algebraMap B S β * hru.unit⁻¹) = algebraMap B S β := by
    rw [mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]
  rw [h2, ← hq, eval_map, eval₂_hom, hβ, map_zero] at h1
  exact (hru.pow _).mul_right_eq_zero.1 h1.symm

end LateralTheory.E.SpecAICPf

namespace LateralTheory.E.SpecAICPf

theorem roots_eq {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] (hK : Function.Injective (algebraMap R K)) (L : Subalgebra R K) (hL : AIC L)
    (p : R[X]) (hp : p.Monic) : (p.map (algebraMap R L)).roots.map L.val.toRingHom = (p.map (algebraMap R K)).roots ∧
      Multiset.card (p.map (algebraMap R L)).roots = p.natDegree := by
  have hinj : Function.Injective (algebraMap R L) := by
    intro a b hab
    exact hK (congrArg Subtype.val hab)
  have hc : Multiset.card (p.map (algebraMap R L)).roots = p.natDegree := by
    rw [card_roots_of_aic hL _ _ (hp.map _) rfl, natDegree_map_eq_of_injective hinj]
  refine ⟨?_, hc⟩
  rw [roots_map_of_injective_of_card_eq_natDegree (f := L.val.toRingHom) Subtype.val_injective
    (by rw [hc, natDegree_map_eq_of_injective hinj]), map_map]
  rfl

theorem aic_of_local {R : Type} [CommRing R] [IsDomain R]
    (h : ∀ v : MaximalSpectrum R, AIC (Localization.AtPrime v.asIdeal)) : AIC R := by
  classical
  intro p hp hd
  let K := FractionRing R
  let L : MaximalSpectrum R → Subalgebra R K := fun v =>
    Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors
  have hL : ∀ v, AIC (L v) := fun v =>
    aic_equiv (IsLocalization.algEquiv v.asIdeal.primeCompl (Localization.AtPrime v.asIdeal) (L v)).toRingEquiv (h v)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  obtain ⟨e0, c0⟩ := roots_eq (IsFractionRing.injective R K) (L ⟨m, hm⟩) (hL _) p hp
  obtain ⟨x, hx⟩ : ∃ x, x ∈ (p.map (algebraMap R K)).roots := by
    rw [← e0]
    apply Multiset.exists_mem_of_ne_zero
    intro h0
    rw [Multiset.map_eq_zero] at h0
    rw [h0] at c0; simp at c0; omega
  have hmem : x ∈ (⊥ : Subalgebra R K) := by
    rw [← MaximalSpectrum.iInf_localization_eq_bot R K, Algebra.mem_iInf]
    intro v
    rw [← (roots_eq (IsFractionRing.injective R K) (L v) (hL v) p hp).1] at hx
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
    exact y.2
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.1 hmem
  refine ⟨a, ?_⟩
  have hr := (mem_roots (hp.map _).ne_zero).1 hx
  rw [IsRoot, eval_map, eval₂_hom] at hr
  exact (IsFractionRing.injective R K) (by rw [hr, map_zero])

end LateralTheory.E.SpecAICPf

namespace LateralTheory.E.SpecAICPf

open CategoryTheory AlgebraicGeometry

theorem stalk_aic (B : CommRingCat.{0}) (hA : AIC B) (x : Spec B) : AIC ((Spec B).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := x.isPrime
  let _ : Algebra B ((Spec B).presheaf.stalk x) := StructureSheaf.stalkAlgebra B x
  have : IsLocalization.AtPrime ((Spec B).presheaf.stalk x) x.asIdeal := StructureSheaf.IsLocalization.to_stalk B x
  exact aic_localization x.asIdeal.primeCompl hA

theorem SpecAIC_of : LateralTheory.E.FibreEqvPf.SpecAIC := by
  intro B hB hA
  refine ⟨inferInstance, ?_⟩
  intro U hU hne
  haveI : Nonempty U := hne.to_subtype
  apply aic_of_local
  intro v
  let y : PrimeSpectrum Γ(Spec B, U) := ⟨v.asIdeal, v.isMaximal.isPrime⟩
  have hy : hU.fromSpec y ∈ U := by
    show hU.fromSpec y ∈ (U : Set (Spec B))
    rw [← hU.range_fromSpec]; exact ⟨y, rfl⟩
  letI := TopCat.Presheaf.algebra_section_stalk (Spec B).presheaf ⟨hU.fromSpec y, hy⟩
  have hloc : IsLocalization.AtPrime ((Spec B).presheaf.stalk (hU.fromSpec y)) y.asIdeal := hU.isLocalization_stalk' y hy
  have hst := stalk_aic B hA (hU.fromSpec y)
  exact aic_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl ((Spec B).presheaf.stalk (hU.fromSpec y))
    (Localization.AtPrime v.asIdeal)).toRingEquiv hst

end LateralTheory.E.SpecAICPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.TateTwistZeroAugmentationSheaf

variable (q : ℕ)

def CP : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj U := ModuleCat.of _ C(U.unop, ULift.{1} (ZMod q))
  map {U V} f := ModuleCat.ofHom
    { toFun := fun g => ContinuousMap.comp g f.unop.base.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem isSheaf_etaleTopology_continuousMaps : Presheaf.IsSheaf Scheme.etaleTopology.{0} (CP q) := by
  apply Presheaf.IsSheaf.of_le (le_trans Scheme.etaleTopology_le_proetaleTopology Scheme.proetaleTopology_le_fpqcTopology)
  haveI : ReflectsLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    reflectsLimitsOfSize_shrink.{1, 1, 0, 1} _
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))
  exact isSheaf_fpqcTopology_continuousMapPresheaf (ULift.{1} (ZMod q))

def augA (U : Scheme.{0}) : (Scheme.Γ ⋙ twF q 0).obj (Opposite.op U) →ₗ[ULift.{1} (ZMod q)] C(U, ULift.{1} (ZMod q)) :=
  (twRel q 0 Γ(U, ⊤)).liftQ (Finsupp.linearCombination _ (fun _ => (1 : C(U, ULift.{1} (ZMod q))))) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, -, rfl⟩
    simp)

def augP : Scheme.Γ ⋙ twF q 0 ⟶ CP q where
  app U := ModuleCat.ofHom (augA q U.unop)
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    apply Finsupp.lhom_ext
    intro ζ c
    apply ContinuousMap.ext; intro t
    erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    change (augA q V.unop) (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.unop.appTop.hom) (Finsupp.single ζ c))) t =
      (augA q U.unop (Submodule.Quotient.mk (Finsupp.single ζ c))) (f.unop.base t)
    simp only [augA]
    erw [Submodule.liftQ_apply, Submodule.liftQ_apply, Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single]
    rfl

def augS : sheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0) ⟶ CP q :=
  sheafifyLift Scheme.etaleTopology.{0} (augP q) (isSheaf_etaleTopology_continuousMaps q)

def augC (T : Scheme.{0}) (x : Sec (tw q 0) T) : C(T, ULift.{1} (ZMod q)) := ((augS q).app (Opposite.op T)).hom x

def aug (T : Scheme.{0}) : Sec (tw q 0) T →+ LocallyConstant T (ZMod q) :=
  AddMonoidHom.mk' (fun x => ⟨fun t => (augC q T x t).down,
      (IsLocallyConstant.iff_continuous _).2 (continuous_uliftDown.comp (ContinuousMap.continuous _))⟩)
    (fun x y => by
      ext t
      simp only [LocallyConstant.coe_add, Pi.add_apply, LocallyConstant.coe_mk, augC]
      erw [LinearMap.map_add]
      rfl)

theorem aug_nat {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U) :
    aug q V (Sec.res g x) = (aug q U x).comap g.base.hom := by
  have h := congrArg (fun h => (ModuleCat.Hom.hom h) x) ((augS q).naturality g.op)
  ext t
  simp only [aug, AddMonoidHom.mk'_apply, LocallyConstant.coe_mk, LocallyConstant.coe_comap, Function.comp_apply]
  exact congrArg (fun k : C(V, ULift.{1} (ZMod q)) => (k t).down) h

theorem aug_gen (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) : aug q U (twGen 0 ζ) = 1 := by
  have h := congrArg (fun h => (ModuleCat.Hom.hom (NatTrans.app h (Opposite.op U))) (Submodule.Quotient.mk (Finsupp.single ζ 1)))
    (toSheafify_sheafifyLift Scheme.etaleTopology.{0} (augP q) (isSheaf_etaleTopology_continuousMaps q))
  ext t
  simp only [aug, AddMonoidHom.mk'_apply, LocallyConstant.coe_mk, LocallyConstant.coe_one, Pi.one_apply]
  have h2 := congrArg (fun k : C(U, ULift.{1} (ZMod q)) => (k t).down) h
  refine h2.trans ?_
  simp only [augP, augA]
  erw [ModuleCat.hom_ofHom, Submodule.liftQ_apply, Finsupp.linearCombination_single]
  simp

theorem Aug_holds : LateralTheory.E.TateTwistZeroAugmentationBijective.Aug := fun q => ⟨aug q, fun g x => aug_nat q g x, aug_gen q⟩

theorem Tw0_of (hB : LateralTheory.E.TateTwistZeroAugmentationBijective.AugBij) : LateralTheory.E.LCIsoPf.Tw0 := LateralTheory.E.TateTwistZeroAugmentationBijective.Tw0_of Aug_holds hB

end LateralTheory.E.TateTwistZeroAugmentationSheaf
end
end

section

noncomputable section
open Polynomial LateralTheory.E.PartDiagCut GlobalTheory.EtC

namespace LateralTheory.E.PartCPfSplit

theorem split_of (hLoc : LateralTheory.E.HensCut.LocAIC) (hMS : LateralTheory.E.HensCut.MonicSplits) : LateralTheory.E.PartCPf.Split := by
  intro B _ _ I hB P p hm
  have key : ∀ e : P.1, ∃ g : Fin p.natDegree → Localization (S I e.1),
      p.map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) = ∏ l, (X - C (g l)) := by
    intro e
    have h0 : (0:B) ∉ S I e.1 := by
      rintro ⟨t, ht⟩
      apply (P.idem e.1 e.2).2
      simpa using ht.symm
    obtain ⟨hdom, haic⟩ := hLoc B (S I e.1) h0 hB
    have hme := hm.map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e)
    obtain ⟨s, hs⟩ := hMS _ haic _ hme
    have hcard : s.toList.length = p.natDegree := by
      have := congrArg natDegree hs
      rw [natDegree_multiset_prod_X_sub_C_eq_card, hm.natDegree_map] at this
      simp [this]
    refine ⟨fun l => s.toList.get (Fin.cast hcard.symm l), ?_⟩
    rw [hs]
    conv_lhs => rw [← Multiset.coe_toList s]
    rw [Multiset.map_coe, Multiset.prod_coe]
    rw [← Fintype.prod_equiv (finCongr hcard) (fun i : Fin s.toList.length => X - C (s.toList.get i)) _ (fun _ => rfl)]
    rw [← List.prod_ofFn]
    congr 1
    apply List.ext_get <;> simp
  choose g hg using key
  refine ⟨p.natDegree, fun l e => g e l, ?_⟩
  refine Polynomial.ext fun k => funext fun e => ?_
  have h2 : (∏ l, (X - C (fun e => g e l))).map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e)
      = ∏ l, (X - C (g e l)) := by simp [Polynomial.map_prod]
  have := congrArg (fun q : (Localization (S I e.1))[X] => q.coeff k) ((hg e).trans h2.symm)
  simpa [coeff_map] using this

theorem PartC_of (hLoc : LateralTheory.E.HensCut.LocAIC) (hMS : LateralTheory.E.HensCut.MonicSplits) (hIP : LateralTheory.E.HensCut.IdemPart)
    (hA : LateralTheory.E.PartDiagCut.PartA) (hl : LateralTheory.E.PartCPf.Lift) : LateralTheory.E.PartDiagCut.PartC :=
  LateralTheory.E.PartCPf.PartC_of' (split_of hLoc hMS) hIP hA hl

end LateralTheory.E.PartCPfSplit
end
end
