module

public import Formalism.HermitianLattices.Bundle003
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVa
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

section Transport

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

def latMap (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V' :=
  M.map ((φ : V →ₗ[K] V').restrictScalars (𝓞 K))

theorem mem_tr (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) (y : V') : y ∈ latMap φ M ↔ φ.symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨φ.symm y, h, by simp⟩

theorem tr_symm_tr (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : latMap φ.symm (latMap φ M) = M := by
  ext x; simp [mem_tr]

theorem tr_tr_symm (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V') : latMap φ (latMap φ.symm M) = M := by
  ext x; simp [mem_tr]

theorem tr_injective (φ : V ≃ₗ[K] V') : Function.Injective (latMap (K := K) φ) := fun a b h => by
  rw [← tr_symm_tr φ a, h, tr_symm_tr]

def cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : V' ≃ₗ[K] V' := (φ.symm.trans g).trans φ

theorem cj_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') : cj φ g y = φ (g (φ.symm y)) := rfl

theorem cj_symm_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') :
    (cj φ g).symm y = φ (g.symm (φ.symm y)) := rfl

theorem cj_symm_cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : cj φ.symm (cj φ g) = g := by
  ext x; simp [cj_apply]

theorem cj_cj_symm (φ : V ≃ₗ[K] V') (g : V' ≃ₗ[K] V') : cj φ (cj φ.symm g) = g := by
  ext x; simp [cj_apply]

theorem mem_gmap (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) (y : V) : y ∈ gmap g M ↔ g.symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨g.symm y, h, by simp⟩

theorem gmap_cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    gmap (cj φ g) (latMap φ M) = latMap φ (gmap g M) := by
  ext y
  simp [mem_gmap, mem_tr, cj_symm_apply]

theorem loc_tr (φ : V ≃ₗ[K] V') (p : Ideal (𝓞 K)) (M : Submodule (𝓞 K) V) :
    loc (K := K) p (latMap φ M) = latMap φ (loc (K := K) p M) := by
  ext y
  rw [mem_tr]
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_tr] at h
    have e : φ.symm (s • y) = s • φ.symm y := by
      rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]
    rwa [e] at h
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_tr]
    have e : φ.symm (s • y) = s • φ.symm y := by
      rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]
    rwa [e]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem isom_symm {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) :
    ∀ x y, h (φ.symm x) (φ.symm y) = h' x y := fun x y => by
  rw [← hφ]; simp

theorem cj_mem_isom {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {g : V ≃ₗ[K] V}
    (hg : g ∈ isom h) : cj φ g ∈ isom h' := by
  intro x y
  rw [cj_apply, cj_apply, hφ, hg, isom_symm hφ]

theorem isLattice_tr (φ : V ≃ₗ[K] V') {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (latMap φ M) :=
  Submodule.IsLattice.of_fg K (hM.fg.map _)

theorem isFullLattice_tr (φ : V ≃ₗ[K] V') {M : Submodule (𝓞 K) V}
    (hM : Submodule.IsFullLattice K M) : Submodule.IsFullLattice K (latMap φ M) := by
  letI : Submodule.IsLattice K (latMap φ M) := isLattice_tr φ hM.toIsLattice
  constructor
  change Submodule.span K ((M.map ((φ : V →ₗ[K] V').restrictScalars (𝓞 K)) :
    Submodule (𝓞 K) V') : Set V') = ⊤
  rw [show Submodule.span K ((M.map ((φ : V →ₗ[K] V').restrictScalars (𝓞 K)) :
      Submodule (𝓞 K) V') : Set V') = (Submodule.span K (M : Set V)).map φ.toLinearMap by
        rw [Submodule.map_span]; rfl,
    hM.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact φ.surjective

theorem genus_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L M : Submodule (𝓞 K) V}
    (hM : M ∈ genus h L) : latMap φ M ∈ genus h' (latMap φ L) := by
  refine ⟨isFullLattice_tr φ hM.1, fun p hp => ?_⟩
  obtain ⟨g, hg, e⟩ := hM.2 p hp
  exact ⟨cj φ g, cj_mem_isom hφ hg, by rw [loc_tr, gmap_cj, e, loc_tr]⟩

theorem classReps_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L : Submodule (𝓞 K) V}
    {s : Finset (Submodule (𝓞 K) V)} (hs : IsClassReps h L s) :
    IsClassReps h' (latMap φ L) (s.map ⟨latMap φ, tr_injective φ⟩) := by
  constructor
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := Finset.mem_map.1 hM
    exact genus_tr hφ (hs.1 N hN)
  · intro M hM
    have hM' : latMap φ.symm M ∈ genus h L := by
      have := genus_tr (isom_symm hφ) hM
      rwa [tr_symm_tr] at this
    obtain ⟨N, ⟨hN, g, hg, e⟩, huniq⟩ := hs.2 _ hM'
    refine ⟨latMap φ N, ⟨Finset.mem_map.2 ⟨N, hN, rfl⟩, cj φ g, cj_mem_isom hφ hg, ?_⟩, ?_⟩
    · rw [gmap_cj, e, tr_tr_symm]
    · rintro N' ⟨hN', g', hg', e'⟩
      obtain ⟨N₀, hN₀, rfl⟩ := Finset.mem_map.1 hN'
      have : N₀ = N := by
        refine huniq N₀ ⟨hN₀, cj φ.symm g', cj_mem_isom (isom_symm hφ) hg', ?_⟩
        have h2 := gmap_cj φ.symm g' (latMap φ N₀)
        rw [tr_symm_tr] at h2
        change gmap g' (latMap φ N₀) = M at e'
        rw [h2, e']
      rw [this]; rfl

theorem card_autL_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) (M : Submodule (𝓞 K) V) :
    Nat.card (autL h' (latMap φ M)) = Nat.card (autL h M) := by
  have a1 : ∀ g : autL h M, gmap (cj φ g.1) (latMap φ M) = latMap φ M := fun g => by
    rw [gmap_cj, g.2.2]
  have a2 : ∀ g : autL h' (latMap φ M), gmap (cj φ.symm g.1) M = M := fun g => by
    have h2 := gmap_cj φ.symm g.1 (latMap φ M)
    rw [tr_symm_tr] at h2
    rw [h2, g.2.2, tr_symm_tr]
  exact (Nat.card_congr ⟨fun g => ⟨cj φ g.1, cj_mem_isom hφ g.2.1, a1 g⟩,
    fun g => ⟨cj φ.symm g.1, cj_mem_isom (isom_symm hφ) g.2.1, a2 g⟩,
    fun g => Subtype.ext (cj_symm_cj φ g.1), fun g => Subtype.ext (cj_cj_symm φ g.1)⟩).symm

theorem mass_eq_sum (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (s : Finset (Submodule (𝓞 K) V)) (hs : IsClassReps h L s) :
    mass h L = ∑ M ∈ s, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ := by
  rw [massBasic_mass_eq h L ⟨s, hs⟩]
  apply Complex.ofReal_injective
  rw [massBasic_sum_cast, massBasic_sum_cast]
  exact latLiftIndep K V h L _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _
    (Exists.choose_spec (⟨s, hs⟩ : ∃ s, IsClassReps h L s)) hs

theorem mass_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) (L : Submodule (𝓞 K) V) :
    mass h' (latMap φ L) = mass h L := by
  by_cases hs : ∃ s, IsClassReps h L s
  · obtain ⟨s, hs⟩ := hs
    rw [mass_eq_sum h L s hs, mass_eq_sum h' _ _ (classReps_tr hφ hs), Finset.sum_map]
    exact Finset.sum_congr rfl fun M _ => by
      rw [Function.Embedding.coeFn_mk, card_autL_tr hφ]
  · have hs' : ¬ ∃ s, IsClassReps h' (latMap φ L) s := by
      rintro ⟨s, hs'⟩
      apply hs
      have := classReps_tr (isom_symm hφ) hs'
      rw [tr_symm_tr] at this
      exact ⟨_, this⟩
    unfold mass
    rw [dite_eq_right hs, dite_eq_right hs']

theorem mass_ortho_eq {n : ℕ} {L : Submodule (𝓞 K) V} {L' : Submodule (𝓞 K) V'}
    (hL : IsOrthoLattice h L n) (hL' : IsOrthoLattice h' L' n) : mass h L = mass h' L' := by
  obtain ⟨e, he1, he2, rfl, he⟩ := hL
  obtain ⟨e', he1', he2', rfl, he'⟩ := hL'
  let b : Module.Basis (Fin n) K V := Module.Basis.mk he1 he2.ge
  let b' : Module.Basis (Fin n) K V' := Module.Basis.mk he1' he2'.ge
  let φ : V ≃ₗ[K] V' := b.equiv b' (Equiv.refl _)
  have hφe : ∀ i, φ (e i) = e' i := fun i => by
    have := b.equiv_apply i b' (Equiv.refl _)
    simpa [b, b', φ] using this
  have hφ : ∀ x y, h' (φ x) (φ y) = h x y := by
    intro x y
    have hx := b.sum_repr x
    have hy := b.sum_repr y
    rw [← hx, ← hy]

    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, b,
    Module.Basis.mk_apply, hφe, he, he']
  rw [← mass_tr hφ]
  congr 1
  unfold latMap
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext i
  exact hφe i

end Transport

end Formalism.MainNotions.J

end
end

section

noncomputable section

namespace Formalism.MainNotions.J

open Finset Matrix

section Pattern

variable {n : ℕ} {F : Type} [Field F]

def Pat (S : Finset (Fin n × Fin n)) (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, (i, j) ∉ S → A i j = if i = j then 1 else 0

theorem pat_det (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) (A : Matrix (Fin n) (Fin n) F)
    (h : Pat S A) : A.det = 1 := by
  have ht : A.BlockTriangular id := by
    intro i j hij
    have hn : (i, j) ∉ S := fun hm => absurd (hS _ hm) (not_lt.mpr (le_of_lt hij))
    have hij' : j < i := hij
    rw [h i j hn, if_neg (ne_of_gt hij')]
  rw [Matrix.det_of_isUpperTriangular ht]
  refine Finset.prod_eq_one fun i _ => ?_
  have hn : (i, i) ∉ S := fun hm => lt_irrefl _ (hS _ hm)
  rw [h i i hn, if_pos rfl]

def patMat (S : Finset (Fin n × Fin n)) (φ : S → F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if h : (i, j) ∈ S then φ ⟨(i, j), h⟩ else if i = j then 1 else 0

theorem patMat_pat (S : Finset (Fin n × Fin n)) (φ : S → F) : Pat S (patMat S φ) := fun i j h => by
  simp [patMat, h]

def patEquiv (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) :
    {A : GL (Fin n) F // Pat S (A : Matrix (Fin n) (Fin n) F)} ≃ (S → F) where
  toFun A := fun p => (A.1 : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2
  invFun φ := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (patMat S φ)
    (by rw [pat_det S hS _ (patMat_pat S φ)]; exact one_ne_zero), patMat_pat S φ⟩
  left_inv A := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    show patMat S (fun p => (A.1 : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2) i j = (A.1 : Matrix (Fin n) (Fin n) F) i j
    by_cases h : (i, j) ∈ S
    · simp [patMat, h]
    · simp [patMat, h, A.2 i j h]
  right_inv φ := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    show patMat S φ i j = _
    simp [patMat, h]

theorem card_pat [Finite F] (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) :
    Nat.card {A : GL (Fin n) F // Pat S (A : Matrix (Fin n) (Fin n) F)} = Nat.card F ^ S.card := by
  rw [Nat.card_congr (patEquiv S hS), Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]

end Pattern

def upS (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

theorem card_upS (n : ℕ) : (upS n).card = n * (n - 1) / 2 := by
  unfold upS
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have : ∀ j : Fin n, (∑ i : Fin n, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have : (univ.filter fun i : Fin n => i < j) = Finset.Iio j := by ext; simp
    rw [this, Fin.card_Iio]
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

def rowS (k rS n : ℕ) : Finset (Fin n × Fin n) :=
  (upS n).filter fun p => ¬ (p.2.val = rS + k ∧ rS ≤ p.1.val)

theorem card_rowS (k rS n : ℕ) (hn : rS + k < n) : (rowS k rS n).card + k = n * (n - 1) / 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := upS n)
    (fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val)
  rw [card_upS] at h
  have hk : ((upS n).filter fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val).card = k := by
    have : ((upS n).filter fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val) =
        (univ : Finset (Fin k)).image fun i => ((⟨rS + i.val, by omega⟩ : Fin n), (⟨rS + k, hn⟩ : Fin n)) := by
      ext ⟨a, b⟩
      simp only [upS, mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨hab, hb, ha⟩
        have hab' : a.val < b.val := hab
        exact ⟨⟨a.val - rS, by omega⟩, Fin.ext (by simp; omega), Fin.ext (by simp [hb])⟩
      · rintro ⟨i, rfl, rfl⟩
        refine ⟨?_, rfl, by simp⟩
        show rS + i.val < rS + k
        omega
    rw [this, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro i j hij
    have := congrArg (fun p : Fin n × Fin n => p.1.val) hij
    simp at this
    exact Fin.ext this
  unfold rowS
  omega

theorem isUnitri_iff {n : ℕ} {F : Type} [Field F] (A : Matrix (Fin n) (Fin n) F) :
    StandardLattice.IsUnitri A ↔ Pat (upS n) A := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    simp only [upS, mem_filter, mem_univ, true_and, not_lt] at hij
    rcases eq_or_lt_of_le hij with h | h
    · subst h; simp [h2]
    · rw [h1 i j h, if_neg (ne_of_gt h)]
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [h i j (by simp [upS, le_of_lt hij]), if_neg (ne_of_gt hij)]
    · rw [h i i (by simp [upS]), if_pos rfl]

theorem isRowLev_iff {n : ℕ} {F : Type} [Field F] (k rS : ℕ) (A : Matrix (Fin n) (Fin n) F) :
    StandardLattice.IsRowLev k rS A ↔ Pat (rowS k rS n) A := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ i j hij
    by_cases e : i = j
    · subst e; simp [h2]
    rw [if_neg e]
    have e' : i.val ≠ j.val := fun h => e (Fin.ext h)
    simp only [rowS, upS, mem_filter, mem_univ, true_and, not_and] at hij
    by_cases hlt : i < j
    · obtain ⟨hj, hi⟩ : j.val = rS + k ∧ rS ≤ i.val := by
        by_contra hc
        exact hij hlt (fun a b => hc ⟨a, b⟩)
      have hlt' : i.val < j.val := hlt
      exact h4 i j hj e (by unfold StandardLattice.blk; split_ifs <;> omega)
    · have hlt' : j.val < i.val := by
        have : ¬ i.val < j.val := hlt
        omega
      by_cases hb : StandardLattice.blk rS k j.val < StandardLattice.blk rS k i.val
      · exact h1 i j hb
      · refine h3 i j ?_ hlt'
        revert hb
        unfold StandardLattice.blk
        split_ifs <;> omega
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hb hij => ?_, fun i j hj hne hb => ?_⟩
    · have hlt : j.val < i.val := by
        revert hij
        unfold StandardLattice.blk
        split_ifs <;> omega
      have hlt2 : ¬ i < j := fun hh => by
        have : i.val < j.val := hh
        omega
      rw [h i j (by simp [rowS, upS, hlt2]), if_neg (fun e => by subst e; omega)]
    · rw [h i i (by simp [rowS, upS]), if_pos rfl]
    · have hlt2 : ¬ i < j := not_lt.mpr (le_of_lt hij)
      rw [h i j (by simp [rowS, upS, hlt2]), if_neg (ne_of_gt hij)]
    · have hi : rS ≤ i.val := by
        revert hb
        unfold StandardLattice.blk
        split_ifs <;> omega
      rw [h i j (by simp [rowS, hj, hi]), if_neg hne]

end Formalism.MainNotions.J

end
end

section

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stdForm_apply (K : Type) [Field K] [StarRing K] (M : ℕ) (x y : Fin M → K) :
    StandardLattice.stdForm K M x y = ∑ i, star (x i) * y i := rfl

theorem std_ortho (K : Type) [Field K] [NumberField K] [StarRing K] (M : ℕ) :
    IsOrthoLattice (StandardLattice.stdForm K M) (StandardLattice.stdLat K M) M := by
  have e : (fun i : Fin M => (Pi.single i 1 : Fin M → K)) = Pi.basisFun K (Fin M) := by
    funext i; simp
  refine ⟨fun i => Pi.single i 1, ?_, ?_, rfl, fun i j => ?_⟩
  · rw [e]; exact (Pi.basisFun K (Fin M)).linearIndependent
  · rw [e]; exact (Pi.basisFun K (Fin M)).span_eq
  · by_cases hij : i = j
    · subst hij; simp [stdForm_apply, Pi.single_apply]
    · simp [stdForm_apply, Pi.single_apply, hij, Ne.symm hij]

theorem zetaR_eq (M : ℕ) (hM : 2 ≤ M) : (riemannZeta (M : ℂ)).re = StandardLattice.zetaR M := by
  have h1 : (1 : ℝ) < ((M : ℂ)).re := by
    simp only [Complex.natCast_re]; exact_mod_cast hM
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1]
  have h2 : (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (M : ℂ)) = ((StandardLattice.zetaR M : ℝ) : ℂ) := by
    unfold StandardLattice.zetaR
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [Complex.cpow_natCast]
    push_cast
    rfl
  rw [h2, Complex.ofReal_re]

end Formalism.MainNotions.J

end
end

section

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem theta_injective_of_scalars (D : D7) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D) (hI : Rows.IsotInternal D.what₂)
    (i : D.nd.Loc) (hj : D.nd.j i ∈ SizeData₂.lifts D) :
    Function.Injective (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
  have hj' := Finset.mem_Icc.mp hj
  exact injective_of_scalars (D.what₂.isot (D.nd.j i)) (hI _ hj'.1 hj'.2) _ (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))
    (fun σ hσ => let ⟨lam, h0, hl⟩ := (h42 i σ hσ).1.1; ⟨(lam : ℂ), by exact_mod_cast h0.ne', hl⟩)

end Formalism.MainNotions.J

end
end
