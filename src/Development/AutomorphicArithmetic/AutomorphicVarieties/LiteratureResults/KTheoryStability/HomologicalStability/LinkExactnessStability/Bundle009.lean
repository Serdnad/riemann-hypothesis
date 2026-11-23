module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle002
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectiveRepGroupHomologyPosVanishes
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

@[expose] public section

section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCxLow

noncomputable def emb (R : Type) [CommRing R] (m : ℕ) : (Fin m → R) →ₗ[R] (ℕ →₀ R) :=
  Finsupp.lmapDomain R R Fin.val ∘ₗ (Finsupp.linearEquivFunOnFinite R R (Fin m)).symm.toLinearMap

theorem emb_apply_val {R : Type} [CommRing R] {m : ℕ} (v : Fin m → R) (k : Fin m) :
    emb R m v (k : ℕ) = v k := by
  simp [emb, Finsupp.mapDomain_apply_of_injective Fin.val_injective]

theorem emb_apply_of_le {R : Type} [CommRing R] {m : ℕ} (v : Fin m → R) (n : ℕ) (h : m ≤ n) :
    emb R m v n = 0 := by
  simp only [emb, LinearMap.comp_apply, Finsupp.lmapDomain_apply, LinearEquiv.coe_coe]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨k, hk⟩
  have hk2 := k.isLt
  omega

theorem emb_injective (R : Type) [CommRing R] (m : ℕ) : Function.Injective (emb R m) := by
  intro v w hvw
  funext k
  have e := congrArg (fun x => x (k : ℕ)) hvw
  simpa only [emb_apply_val] using e

theorem emb_mem_low {R : Type} [CommRing R] {m : ℕ} (v : Fin m → R) : emb R m v ∈ low R m :=
  fun n h => emb_apply_of_le v n h

theorem emb_restrict {R : Type} [CommRing R] {m : ℕ} (x : ℕ →₀ R) (hx : x ∈ low R m) :
    emb R m (fun k : Fin m => x k) = x := by
  ext n
  by_cases h : n < m
  · have e := emb_apply_val (fun k : Fin m => x k) ⟨n, h⟩
    simpa using e
  · rw [emb_apply_of_le _ n (not_lt.mp h)]
    exact (hx n (not_lt.mp h)).symm

theorem form_emb {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (v : Fin m → R) :
    (∑ k : Fin m, g k • Finsupp.lapply (R := R) (M := R) (k : ℕ)) (emb R m v) = g ⬝ᵥ v := by
  simp [dotProduct, emb_apply_val]

theorem emb_form {R : Type} [CommRing R] {m : ℕ} (f : (ℕ →₀ R) →ₗ[R] R) (v : Fin m → R) :
    (fun k => f (emb R m (Pi.single k 1))) ⬝ᵥ v = f (emb R m v) := by
  have hs : ∀ k, (Pi.single k (v k) : Fin m → R) = v k • (Pi.single k 1 : Fin m → R) := by
    intro k
    ext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [hj]
  conv_rhs => rw [← Finset.univ_sum_single v]

  simp only [map_sum, hs, map_smul, smul_eq_mul, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

theorem link_eq (R : Type) [CommRing R] (m : ℕ) :
    linkIn (uniM R (ℕ →₀ R)) (low R m) [] = List.map (emb R m) '' uniSeq R m := by
  ext w
  simp only [linkIn, Set.mem_ofPred_eq, List.nil_append, Set.mem_image]
  constructor
  · rintro ⟨hw, f, hf⟩
    refine ⟨w.map (fun x (k : Fin m) => x k), ⟨fun i k => f (Fin.cast (by simp) i) (emb R m (Pi.single k 1)), ?_⟩, ?_⟩
    · intro i j
      simp only [List.get_eq_getElem, List.getElem_map]
      rw [emb_form, emb_restrict _ (hw _ (List.getElem_mem _))]
      have e := hf (Fin.cast (by simp) i) (Fin.cast (by simp) j)
      simpa [List.get_eq_getElem, Fin.ext_iff] using e
    · rw [List.map_map]
      refine (List.map_congr_left ?_).trans (List.map_id w)
      intro x hx
      exact emb_restrict x (hw x hx)
  · rintro ⟨u, ⟨g, hg⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact emb_mem_low y
    · refine ⟨fun i => ∑ k : Fin m, g (Fin.cast (by simp) i) k • Finsupp.lapply (R := R) (M := R) (k : ℕ), ?_⟩
      intro i j
      simp only [List.get_eq_getElem, List.getElem_map]
      rw [form_emb]
      have e := hg (Fin.cast (by simp) i) (Fin.cast (by simp) j)
      simpa [List.get_eq_getElem, Fin.ext_iff] using e

end GlobalTheory.SeqCxLow

private theorem exactAt_of_exactAt_image_injective {V U : Type} (e : V → U) (he : Function.Injective e)
    (F : Set (List V)) (q : ℕ) (h : ExactAt (List.map e '' F) q) : ExactAt F q := by
  classical
  have hM : Function.Injective (List.map e) := List.map_injective_iff.mpr he
  have comm : ∀ c, bd U (Finsupp.mapDomain (List.map e) c) = Finsupp.mapDomain (List.map e) (bd V c) := by
    intro c
    have E : (bd U).comp (Finsupp.lmapDomain ℤ ℤ (List.map e)) = (Finsupp.lmapDomain ℤ ℤ (List.map e)).comp (bd V) := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [bd, map_sum, Finsupp.lmapDomain_apply, Finsupp.mapDomain_smul, Finsupp.mapDomain_single, List.eraseIdx_map]
    exact LinearMap.congr_fun E c
  intro c hc hbc
  have hc' : Finsupp.mapDomain (List.map e) c ∈ chains (List.map e '' F) q := by
    rw [chains, Finsupp.mem_supported] at hc ⊢
    intro z hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (Finset.mem_coe.mp hz))
    have hl' := hc (Finset.mem_coe.mpr hl)
    exact ⟨⟨l, hl'.1, rfl⟩, by simp [hl'.2]⟩
  obtain ⟨b', hb', hbb⟩ := h _ hc' (by rw [comm, hbc, Finsupp.mapDomain_zero])
  rw [chains, Finsupp.mem_supported] at hb'
  have hrange : ↑b'.support ⊆ Set.range (List.map e) := by
    intro z hz
    obtain ⟨⟨l, _, rfl⟩, _⟩ := hb' hz
    exact ⟨l, rfl⟩
  refine ⟨Finsupp.comapDomain (List.map e) b' hM.injOn, ?_, ?_⟩
  · rw [chains, Finsupp.mem_supported]
    intro l hl
    rw [Finset.mem_coe, Finsupp.comapDomain_support, Finset.mem_preimage] at hl
    obtain ⟨⟨l', hl'F, hl'e⟩, hlen⟩ := hb' (Finset.mem_coe.mpr hl)
    have hll := hM hl'e
    subst hll
    exact ⟨hl'F, by simpa using hlen⟩
  · apply Finsupp.mapDomain_injective hM
    rw [← comm, Finsupp.mapDomain_comapDomain (List.map e) hM b' hrange, hbb]

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exactAt_unimodularSeqs_of_link_nil_coordSubspace : ∀ (R : Type) [CommRing R] (m q : ℕ), ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R m) []) q → ExactAt (uniSeq R m) q := by
  intro R _ m q h
  rw [GlobalTheory.SeqCxLow.link_eq] at h
  exact exactAt_of_exactAt_image_injective _ (GlobalTheory.SeqCxLow.emb_injective R m) _ _ h
end
end

section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCxLinkEquiv

theorem uniM_map_of_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M)
    (l : List M) (h : l ∈ uniM R M) : l.map ψ ∈ uniM R M := by
  obtain ⟨f, hf⟩ := h
  have hl : (l.map ψ).length = l.length := by simp
  refine ⟨fun i => (f (Fin.cast hl i)).comp ψ.symm.toLinearMap, ?_⟩
  intro i j
  have := hf (Fin.cast hl i) (Fin.cast hl j)
  simpa [Fin.ext_iff] using this

theorem linkIn_map {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M)
    (X : Set M) (hX : ∀ x, ψ x ∈ X ↔ x ∈ X) (τ : List M) :
    linkIn (uniM R M) X (τ.map ψ) = List.map ψ '' linkIn (uniM R M) X τ := by
  ext w
  simp only [linkIn, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hw, hmem⟩
    refine ⟨w.map ψ.symm, ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      rw [← hX]
      simpa using hw y hy
    · have := uniM_map_of_mem ψ.symm _ hmem
      simpa [List.map_append, List.map_map, Function.comp_def] using this
    · simp [List.map_map, Function.comp_def]
  · rintro ⟨w', ⟨hw', hmem⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact (hX y).2 (hw' y hy)
    · have := uniM_map_of_mem ψ _ hmem
      simpa [List.map_append] using this

private theorem bd_mapDomain_listMap_comm {V : Type} (g : V → V) (c : List V →₀ ℤ) :
    bd V (Finsupp.mapDomain (List.map g) c) = Finsupp.mapDomain (List.map g) (bd V c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [Finsupp.mapDomain_add, ha, hb]
  | single l n =>
    simp [bd, Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_smul, List.eraseIdx_map]

private theorem mapDomain_listMap_mem_chains_of_map_mem {V : Type} (g : V → V) (F G : Set (List V))
    (hFG : ∀ l ∈ F, l.map g ∈ G) (p : ℕ) (c : List V →₀ ℤ) (hc : c ∈ chains F p) :
    Finsupp.mapDomain (List.map g) c ∈ chains G p := by
  classical
  rw [chains, Finsupp.mem_supported] at hc ⊢
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
  obtain ⟨hlF, hlen⟩ := hc hl
  exact ⟨hFG l hlF, by simp [hlen]⟩

theorem exactAt_linkIn_of_map : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M) (X : Set M), (∀ x, ψ x ∈ X ↔ x ∈ X) → ∀ (τ : List M) (p : ℕ), ExactAt (linkIn (uniM R M) X (τ.map ψ)) p → ExactAt (linkIn (uniM R M) X τ) p := by
  intro R M _ _ _ ψ X hX τ p h
  rw [linkIn_map ψ X hX τ] at h
  intro c hc hbd
  have hc' := mapDomain_listMap_mem_chains_of_map_mem (⇑ψ) (linkIn (uniM R M) X τ)
    (List.map ψ '' linkIn (uniM R M) X τ) (fun l hl => ⟨l, hl, rfl⟩) p c hc
  obtain ⟨b, hb, hbb⟩ := h _ hc' (by rw [bd_mapDomain_listMap_comm, hbd]; simp)
  refine ⟨Finsupp.mapDomain (List.map ψ.symm) b,
    mapDomain_listMap_mem_chains_of_map_mem (⇑ψ.symm) _ _ ?_ _ b hb, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    simpa [List.map_map, Function.comp_def] using hl
  · have hid : (List.map ψ.symm ∘ List.map ψ) = id := by
      funext l
      simp [List.map_map, Function.comp_def]
    rw [bd_mapDomain_listMap_comm, hbb, ← Finsupp.mapDomain_comp, hid, Finsupp.mapDomain_id]

end GlobalTheory.SeqCxLinkEquiv

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exactAt_linkIn_uniM_of_exactAt_map_linearEquiv : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M) (X : Set M), (∀ x, ψ x ∈ X ↔ x ∈ X) → ∀ (τ : List M) (p : ℕ), ExactAt (linkIn (uniM R M) X (τ.map ψ)) p → ExactAt (linkIn (uniM R M) X τ) p := by
  first
  | exact @GlobalTheory.SeqCxLinkEquiv.exactAt_linkIn_of_map
  | exact @GlobalTheory.SeqCxLinkEquiv.linkIn_map
  | exact @GlobalTheory.SeqCxLinkEquiv.uniM_map_of_mem
end
end

section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

def conjActHom {k G : Type} [CommRing k] [Group G] (g : G) (A : Rep k G) :
    A ⟶ Rep.res (MulAut.conj g).toMonoidHom A :=
  Rep.ofHom ⟨A.ρ g, fun h => LinearMap.ext fun a => by
    change A.ρ g (A.ρ h a) = A.ρ (g * h * g⁻¹) (A.ρ g a)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]⟩

theorem conjActHom_hom_apply {k G : Type} [CommRing k] [Group G] (g : G) (A : Rep k G) (a : A) :
    (conjActHom g A).hom a = A.ρ g a := rfl

theorem conj_map_eq_id_zero (k G : Type) [CommRing k] [Group G] (g : G) (A : Rep k G)
    (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A) (hu : ∀ a, u.hom a = A.ρ g a) :
    groupHomology.map (MulAut.conj g).toMonoidHom u 0 = 𝟙 _ := by
  rw [← cancel_epi (groupHomology.H0π A), groupHomology.H0π_comp_map, Category.comp_id]
  ext a
  have hv : (groupHomology.H0π A).hom (A.ρ g a) = (groupHomology.H0π A).hom a := by
    rw [← groupHomology.coinvariantsMk_comp_H0Iso_inv]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    congr 1
    exact Representation.Coinvariants.mk_self_apply _ _ _
  rw [← hv, ← hu]
  rfl

theorem conj_map_eq_id : ∀ (k G : Type) [CommRing k] [Group G] (g : G) (n : ℕ) (A : Rep k G)
    (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A), (∀ a, u.hom a = A.ρ g a) →
    groupHomology.map (MulAut.conj g).toMonoidHom u n = 𝟙 _ := by
  intro k G _ _ g n
  induction n with
  | zero => exact conj_map_eq_id_zero k G g
  | succ n ih =>
    intro A u hu
    obtain ⟨ι, K, i, e, h, hS⟩ := exists_free_shortExact k G A
    have hP : IsZero (groupHomology (Rep.free k G ι) (n + 1)) :=
      GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k G (Rep.free k G ι) inferInstance n
    have hmono := groupHomology.mono_δ_of_isZero hS n hP
    have hnat := (GlobalTheory.T.groupHomology_longExact_maps_natural_of_res k G G (MulAut.conj g).toMonoidHom _ _ hS hS
      (conjActHom g K) (conjActHom g (Rep.free k G ι)) u
      (fun a => by
        change (Rep.free k G ι).ρ g (i.hom a) = i.hom (K.ρ g a)
        exact (Rep.hom_comm_apply i g a).symm)
      (fun a => by
        change u.hom (e.hom a) = e.hom ((Rep.free k G ι).ρ g a)
        rw [hu]
        exact (Rep.hom_comm_apply e g a).symm) n).1
    rw [ih K (conjActHom g K) (fun _ => rfl), Category.comp_id] at hnat
    rw [← cancel_mono (groupHomology.δ hS (n + 1) n rfl), Category.id_comp]
    exact hnat.symm

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.innerAut_acts_trivially_groupHomology : ∀ (k G : Type) [CommRing k] [Group G] (g : G) (n : ℕ) (A : Rep k G) (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A), (∀ a, u.hom a = A.ρ g a) → groupHomology.map (MulAut.conj g).toMonoidHom u n = 𝟙 _ := by
  first
  | exact @GlobalTheory.HomStab.conj_map_eq_id
  | exact @GlobalTheory.HomStab.conj_map_eq_id_zero
  | exact @GlobalTheory.HomStab.conjActHom_hom_apply
end
end
