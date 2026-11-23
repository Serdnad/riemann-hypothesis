module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Mathlib.Tactic.Continuity
public import Mathlib.Algebra.Homology.QuasiIso
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory.CubeTop

variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]


omit [LinearOrder ι] in
theorem univ_subset {n : ℕ} (hn : Fintype.card ι = n) (s : {s : Finset ι // s.card = n}) :
    (Finset.univ : Finset ι) ⊆ s.1 :=
  (Finset.eq_univ_of_card s.1 (s.2.trans hn.symm)).ge

def topTerm (A : Cube.{0} ι R) {n : ℕ} (hn : Fintype.card ι = n) :
    A.obj Finset.univ →ₗ[R] Cube.Term A n :=
  LinearMap.pi fun s => Cube.res A (univ_subset hn s)


omit [LinearOrder ι] in
theorem topTerm_surjective (A : Cube.{0} ι R) {n : ℕ} (hn : Fintype.card ι = n) :
    Function.Surjective (topTerm A hn) := by
  intro x
  refine ⟨x ⟨Finset.univ, hn⟩, funext ?_⟩
  rintro ⟨s, hs⟩
  obtain rfl := Finset.eq_univ_of_card s (hs.trans hn.symm)
  exact Cube.res_self A _ _

theorem topTerm_res_mem (A : Cube.{0} ι R) {p : ℕ} (hn : Fintype.card ι = p + 1) (i : ι)
    (x : A.obj (Finset.univ.erase i)) :
    ∃ y, Cube.d A p y = topTerm A hn (Cube.res A (Finset.erase_subset i _) x) := by
  let y : ∀ s, A.obj s := Pi.single (Finset.univ.erase i) (cubeSign Finset.univ i • x)
  refine ⟨fun s => y s.1, funext ?_⟩
  rintro ⟨s, hs⟩
  obtain rfl := Finset.eq_univ_of_card s (hs.trans hn.symm)
  rw [Cube.d_apply_eq_totalD A _ y (fun _ => rfl), Cube.totalD_apply, Finset.sum_eq_single i]
  · simp only [y, Pi.single_eq_same, map_zsmul, cubeSign_smul_smul]
    exact (Cube.res_self A _ _).symm
  · intro j _ hji
    have : (Finset.univ.erase j : Finset ι) ≠ Finset.univ.erase i := fun h => by
      have : j ∈ (Finset.univ.erase i : Finset ι) := by simp [hji]
      rw [← h] at this
      simp at this
    simp only [y, Pi.single_eq_of_ne this, map_zero, smul_zero]
  · simp

theorem d_top (A : Cube.{0} ι R) :
    (cubeComplex A).d (Fintype.card ι) (Fintype.card ι + 1) = 0 := by
  rw [cubeComplex_d]
  have := Cube.subsingleton_term A (Nat.lt_succ_self (Fintype.card ι))
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

def topClass (A : Cube.{0} ι R) :
    A.obj Finset.univ →ₗ[R] (cubeComplex A).homology (Fintype.card ι) :=
  ((cubeComplex A).pOpcycles (Fintype.card ι) ≫
    ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
      (d_top A)).inv).hom ∘ₗ topTerm A rfl

theorem topClass_surjective (A : Cube.{0} ι R) : Function.Surjective (topClass A) :=
  ((ModuleCat.epi_iff_surjective ((cubeComplex A).pOpcycles (Fintype.card ι) ≫
    ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
      (d_top A)).inv)).1 inferInstance).comp (topTerm_surjective A rfl)

theorem topClass_res (A : Cube.{0} ι R) (i : ι) (x : A.obj (Finset.univ.erase i)) :
    topClass A (Cube.res A (Finset.erase_subset i _) x) = 0 := by
  have key : ∀ (n : ℕ) (hn : Fintype.card ι = n), ((cubeComplex A).pOpcycles n).hom
      (topTerm A hn (Cube.res A (Finset.erase_subset i _) x)) = 0 := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 :=
      Nat.exists_eq_succ_of_ne_zero (hn ▸ (Fintype.card_pos_iff.2 ⟨i⟩).ne')
    obtain ⟨y, hy⟩ := topTerm_res_mem A hn i x
    have := (cubeComplex A).d_pOpcycles p (p + 1)
    rw [cubeComplex_d] at this
    rw [← hy]
    exact congr(($this).hom y)
  have := key _ rfl
  let g := ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
    (d_top A)).inv.hom
  exact (congrArg g this).trans (map_zero g)

theorem span_topClass {κ : Type} (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) :
    Submodule.span R ((fun a : κ => topClass A (b Finset.univ ⟨a, Finset.subset_univ _⟩)) ''
      {a | T a = Finset.univ}) = ⊤ := by
  rw [eq_top_iff, ← LinearMap.range_eq_top.2 (topClass_surjective A), LinearMap.range_eq_map,
    ← (b Finset.univ).span_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  by_cases h : T a.1 = Finset.univ
  · exact Submodule.subset_span ⟨a.1, h, rfl⟩
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ T a.1 := by
      simpa [Finset.eq_univ_iff_forall] using h
    have := topClass_res A i (b _ ⟨a.1, Finset.subset_erase.2 ⟨Finset.subset_univ _, hi⟩⟩)
    rw [hb] at this
    rw [this]
    exact zero_mem _

theorem main : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (κ : Type) (T : κ → Finset ι) (A : Cube.{0} ι R) (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s)), (∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}), Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) → ((∀ a, T a ≠ Finset.univ) → (cubeComplex A).ExactAt (Fintype.card ι)) ∧ ({a | T a = Finset.univ}.Finite → Module.Finite R ((cubeComplex A).homology (Fintype.card ι))) := by
  intro ι _ _ R _ κ T A b hb
  have h := span_topClass T A b hb
  refine ⟨fun hT => ?_, fun hT => ⟨h ▸ Submodule.fg_span (hT.image _)⟩⟩
  · rw [Set.eq_empty_of_forall_notMem (s := {a | T a = Finset.univ}) hT, Set.image_empty,
      Submodule.span_empty] at h
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have := (Submodule.subsingleton_iff R).1 (subsingleton_of_bot_eq_top h)
    exact ModuleCat.isZero_of_subsingleton _

end GlobalTheory.CubeTop
end
end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory

variable {ι : Type} (R : Type) [CommRing R]

def Cube.above (w : Finset ι) : Cube.{0} ι R :=
  Cube.mk (fun s => ModuleCat.of R (PLift (w ⊆ s) →₀ R))
    (fun h => Finsupp.lmapDomain R R fun x => ⟨x.down.trans h⟩)
    (fun _ _ => Finsupp.mapDomain_id)
    (fun _ _ _ => Finsupp.mapDomain_comp.symm)

theorem cubeComplex_above_exactAt [LinearOrder ι] [Fintype ι] (w : Finset ι) {p : ℕ}
    (hp : p ≠ Fintype.card ι) : (cubeComplex (Cube.above R w)).ExactAt p := by
  by_cases hw : w = Finset.univ
  · subst hw
    have : Subsingleton (Cube.Term (Cube.above R (Finset.univ : Finset ι)) p) := by
      refine ⟨fun x y => funext fun s => ?_⟩
      refine Finsupp.ext fun a => absurd ?_ hp
      rw [← s.2, Finset.univ_subset_iff.1 a.down, Finset.card_univ]
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Cube.Term _ p)))
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ w := by
      by_contra! h
      exact hw (Finset.eq_univ_iff_forall.2 h)
    refine cubeComplex_exactAt_of_bijective _ i (fun s _ => ?_) p
    refine ⟨Finsupp.mapDomain_injective fun _ _ _ => Subsingleton.elim _ _,
      Finsupp.mapDomain_surjective fun x => ⟨⟨?_⟩, Subsingleton.elim _ _⟩⟩
    exact (Finset.subset_insert_iff_of_notMem hi).1 x.down

variable {R}

def monomialCoord {κ : Type} (T : κ → Finset ι) {s : Finset ι} {M : Type} [AddCommGroup M]
    [Module R M] (b : Module.Basis {a : κ // T a ⊆ s} R M) :
    M ≃ₗ[R] ⨁ a, (PLift (T a ⊆ s) →₀ R) :=
  b.repr ≪≫ₗ Finsupp.domLCongr (Equiv.sigmaPLiftEquivSubtype fun a => T a ⊆ s).symm ≪≫ₗ
    sigmaFinsuppLequivDFinsupp R

theorem monomialCoord_basis {κ : Type} [DecidableEq κ] (T : κ → Finset ι) {s : Finset ι} {M : Type}
    [AddCommGroup M] [Module R M] (b : Module.Basis {a : κ // T a ⊆ s} R M)
    (a : {a : κ // T a ⊆ s}) :
    monomialCoord T b (b a) =
      DirectSum.lof R κ (fun a => PLift (T a ⊆ s) →₀ R) a.1 (Finsupp.single ⟨a.2⟩ 1) := by
  simp only [monomialCoord, LinearEquiv.trans_apply, Module.Basis.repr_self, Finsupp.domLCongr_single]
  exact sigmaFinsuppEquivDFinsupp_single _ _

theorem cubeComplex_exactAt_of_monomialBasis (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (κ : Type) (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩)
    (p : ℕ) (hp : p ≠ Fintype.card ι) : (cubeComplex A).ExactAt p := by
  classical
  let e : A ≅ Cube.directSum fun a => Cube.above R (T a) :=
    Cube.isoMk (fun s => monomialCoord T (b s)) fun {s t} h x => by
      have : (monomialCoord T (b t)).toLinearMap ∘ₗ Cube.res A h =
          (DirectSum.lmap fun a => Finsupp.lmapDomain R R
            fun x : PLift (T a ⊆ s) => (⟨x.down.trans h⟩ : PLift (T a ⊆ t))) ∘ₗ
            (monomialCoord T (b s)).toLinearMap := by
        refine (b s).ext fun a => ?_
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hb, monomialCoord_basis,
          DirectSum.lmap_lof, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      exact congr($this x)
  exact (exactAt_iff_of_quasiIsoAt ((cubeFunctor ι R).mapIso e).hom p).2
    ((cubeComplex_directSum_exactAt_iff _ p).2 fun a => cubeComplex_above_exactAt R (T a) hp)

end GlobalTheory
end
end

section

namespace GlobalTheory

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

section Chain

theorem relLength_eq_add_of_le {A B C : Submodule R V} (hCB : C ≤ B) (hBA : B ≤ A) :
    relLength A C = relLength A B + relLength B C := by
  have hle : C.submoduleOf A ≤ B.submoduleOf A := Submodule.comap_mono hCB
  have hex := Module.length_eq_add_of_exact (LinearMap.ker (Submodule.factor hle)).subtype
    (Submodule.factor hle) (Submodule.injective_subtype _) (Submodule.factor_surjective hle)
    (LinearMap.exact_subtype_ker_map _)
  have hker : LinearMap.ker (Submodule.factor hle) =
      (B.submoduleOf A).map (C.submoduleOf A).mkQ := by
    rw [Submodule.factor, Submodule.ker_mapQ, Submodule.comap_id]
  rw [hker, ← relLength_eq_length_map_mkQ, relLength_submoduleOf hBA] at hex
  rw [add_comm]
  exact hex

theorem relLength_inf_eq_add (A B C : Submodule R V) :
    relLength A (B ⊓ C) = relLength A B + relLength (A ⊓ B) C := by
  have h := relLength_eq_add_of_le (A := A) (B := A ⊓ B) (C := A ⊓ B ⊓ C) inf_le_left inf_le_left
  rwa [relLength_inf_right, relLength_inf_right, inf_assoc, relLength_inf_right] at h

theorem relLength_le_add (A B C : Submodule R V) :
    relLength A C ≤ relLength A B + relLength B C :=
  calc relLength A C ≤ relLength A (B ⊓ C) := relLength_anti_right A inf_le_right
    _ = relLength A B + relLength (A ⊓ B) C := relLength_inf_eq_add A B C
    _ ≤ relLength A B + relLength B C := by
      gcongr
      exact inf_le_right

theorem relLength_inf_le_add (A B C : Submodule R V) :
    relLength A (B ⊓ C) ≤ relLength A B + relLength A C := by
  rw [relLength_inf_eq_add]
  gcongr
  exact inf_le_left

theorem relLength_ne_top_trans {A B C : Submodule R V} (hAB : relLength A B ≠ ⊤)
    (hBC : relLength B C ≠ ⊤) : relLength A C ≠ ⊤ :=
  ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hAB, hBC⟩) (relLength_le_add A B C)

theorem relLength_inf_ne_top_iff {A B C : Submodule R V} :
    relLength A (B ⊓ C) ≠ ⊤ ↔ relLength A B ≠ ⊤ ∧ relLength A C ≠ ⊤ :=
  ⟨fun h => ⟨ne_top_of_le_ne_top h (relLength_anti_right A inf_le_left),
      ne_top_of_le_ne_top h (relLength_anti_right A inf_le_right)⟩,
    fun h => ne_top_of_le_ne_top (WithTop.add_ne_top.mpr h) (relLength_inf_le_add A B C)⟩

end Chain

section Commensurable

variable {A A' B B' C : Submodule R V}

@[trans] theorem LengthCommensurable.trans (hAB : LengthCommensurable A B)
    (hBC : LengthCommensurable B C) : LengthCommensurable A C :=
  ⟨relLength_ne_top_trans hAB.1 hBC.1, relLength_ne_top_trans hBC.2 hAB.2⟩

theorem lengthCommensurable_iff_of_le_of_le (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable A C ↔ LengthCommensurable A B ∧ LengthCommensurable B C := by
  rw [lengthCommensurable_iff_of_ge hCB, lengthCommensurable_iff_of_ge hBA,
    lengthCommensurable_iff_of_ge (hCB.trans hBA), relLength_eq_add_of_le hCB hBA]
  exact WithTop.add_ne_top

namespace LengthCommensurable

theorem of_between_left (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable A B :=
  ((lengthCommensurable_iff_of_le_of_le hCB hBA).mp h).1

theorem of_between_right (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable B C :=
  ((lengthCommensurable_iff_of_le_of_le hCB hBA).mp h).2

theorem inf_right (hAB : LengthCommensurable A B) (hAC : LengthCommensurable A C) :
    LengthCommensurable A (B ⊓ C) :=
  ⟨relLength_inf_ne_top_iff.mpr ⟨hAB.1, hAC.1⟩,
    ne_top_of_le_ne_top hAB.2 (relLength_mono_left inf_le_left A)⟩

theorem toNat_relLength_eq_add_of_le (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    (relLength A C).toNat = (relLength A B).toNat + (relLength B C).toNat := by
  rw [relLength_eq_add_of_le hCB hBA,
    ENat.toNat_add (h.of_between_left hCB hBA).1 (h.of_between_right hCB hBA).1]

theorem signedLength_eq_toNat_sub_of_le {D : Submodule R V} (h : LengthCommensurable A B)
    (hAD : LengthCommensurable A D) (hDA : D ≤ A) (hDB : D ≤ B) :
    signedLength A B = ((relLength A D).toNat : ℤ) - ((relLength B D).toNat : ℤ) := by
  have hBD : LengthCommensurable B D := h.symm.trans hAD
  have h₁ := hAD.toNat_relLength_eq_add_of_le (B := A ⊓ B) (le_inf hDA hDB) inf_le_left
  have h₂ := hBD.toNat_relLength_eq_add_of_le (B := A ⊓ B) (le_inf hDA hDB) inf_le_right
  rw [relLength_inf_right] at h₁
  rw [relLength_inf_right'] at h₂
  rw [h₁, h₂, signedLength]
  push_cast
  ring

theorem signedLength_eq_add (hAB : LengthCommensurable A B) (hBC : LengthCommensurable B C) :
    signedLength A C = signedLength A B + signedLength B C := by
  have hAC := hAB.trans hBC
  have hAD : LengthCommensurable A (A ⊓ B ⊓ C) := ((refl A).inf_right hAB).inf_right hAC
  have hA : A ⊓ B ⊓ C ≤ A := inf_le_left.trans inf_le_left
  have hB : A ⊓ B ⊓ C ≤ B := inf_le_left.trans inf_le_right
  have hC : A ⊓ B ⊓ C ≤ C := inf_le_right
  rw [hAB.signedLength_eq_toNat_sub_of_le hAD hA hB, hAC.signedLength_eq_toNat_sub_of_le hAD hA hC,
    hBC.signedLength_eq_toNat_sub_of_le (hAB.symm.trans hAD) hB hC]
  ring

end LengthCommensurable

end Commensurable

end GlobalTheory
end

section

open Pointwise

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem nonempty_quotient_smul_top_equiv_pi {ι : Type*} [Finite ι] (b : Module.Basis ι R M)
    (a : R) :
    Nonempty ((M ⧸ (a • ⊤ : Submodule R M)) ≃ₗ[R] (ι → R ⧸ Ideal.span {a})) := by
  let g : M →ₗ[R] (ι → R ⧸ Ideal.span {a}) :=
    LinearMap.pi fun i => (Ideal.span {a} : Ideal R).mkQ ∘ₗ b.coord i
  have hg : ∀ x i, g x i = Ideal.Quotient.mk (Ideal.span {a}) (b.repr x i) := fun _ _ => rfl
  have hs : Function.Surjective g := by
    intro y
    choose c hc using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨b.equivFun.symm c, funext fun i => ?_⟩
    rw [hg, ← hc i, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hk : (a • ⊤ : Submodule R M) = LinearMap.ker g := by
    ext x
    rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker, funext_iff]
    simp only [hg, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, -, rfl⟩ i
      exact ⟨b.repr y i, by simp [mul_comm]⟩
    · intro h
      choose c hc using h
      refine ⟨b.equivFun.symm c, trivial, b.equivFun.injective (funext fun i => ?_)⟩
      rw [map_smul, LinearEquiv.apply_symm_apply, b.equivFun_apply, ← hc i, Pi.smul_apply,
        smul_eq_mul, mul_comm]
  exact ⟨Submodule.quotEquivOfEq _ _ hk ≪≫ₗ g.quotKerEquivOfSurjective hs⟩

theorem length_quotient_smul_top_of_free [Nontrivial R] [Module.Free R M] [Module.Finite R M]
    (a : R) :
    Module.length R (M ⧸ (a • ⊤ : Submodule R M)) =
      Module.length R (R ⧸ Ideal.span {a}) * (Module.finrank R M : ℕ∞) := by
  rw [(nonempty_quotient_smul_top_equiv_pi (Module.finBasis R M) a).some.length_eq,
    Module.length_pi, mul_comm]
  simp

theorem submoduleOf_smul_self (A : Submodule R M) (a : R) :
    (a • A).submoduleOf A = (a • ⊤ : Submodule R A) := by
  ext x
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, trivial, Subtype.ext h⟩
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, y.2, rfl⟩

theorem relLength_smul_self_eq_length (A : Submodule R M) (a : R) :
    relLength A (a • A) = Module.length R (A ⧸ (a • ⊤ : Submodule R A)) := by
  rw [relLength_def, submoduleOf_smul_self]

end General

section DVR

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem length_quotient_span_singleton_dvr (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = addVal R a :=
  Ring.ord_eq_addVal a

theorem addVal_irreducible_pow {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) :
    addVal R (ϖ ^ e) = e := by
  rw [addVal_pow, addVal_uniformizer hϖ, nsmul_one]

section Free

variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

theorem length_quotient_smul_top_dvr (a : R) :
    Module.length R (M ⧸ (a • ⊤ : Submodule R M)) = addVal R a * (Module.finrank R M : ℕ∞) := by
  rw [length_quotient_smul_top_of_free, length_quotient_span_singleton_dvr]

end Free

variable {V : Type*} [AddCommGroup V] [Module R V] [Module.IsTorsionFree R V]
  {A : Submodule R V}

theorem relLength_smul_self (hA : A.FG) (a : R) :
    relLength A (a • A) = addVal R a * (Module.finrank R A : ℕ∞) := by
  have : Module.Finite R A := Module.Finite.iff_fg.mpr hA
  rw [relLength_smul_self_eq_length, length_quotient_smul_top_dvr]

theorem relLength_smul_self_of_addVal_eq (hA : A.FG) {a : R} {n : ℕ} (hn : addVal R a = n) :
    relLength A (a • A) = ((n * Module.finrank R A : ℕ) : ℕ∞) := by
  rw [relLength_smul_self hA, hn, Nat.cast_mul]

theorem relLength_irreducible_pow_smul_self (hA : A.FG) {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) :
    relLength A (ϖ ^ e • A) = ((e * Module.finrank R A : ℕ) : ℕ∞) :=
  relLength_smul_self_of_addVal_eq hA (addVal_irreducible_pow hϖ e)

theorem relLength_smul_self_ne_top (hA : A.FG) {a : R} (ha : a ≠ 0) :
    relLength A (a • A) ≠ ⊤ := by
  rw [relLength_smul_self hA]
  exact WithTop.mul_ne_top (addVal_eq_top_iff.not.mpr ha) (ENat.coe_ne_top _)

theorem lengthCommensurable_smul_self (hA : A.FG) {a : R} (ha : a ≠ 0) :
    LengthCommensurable A (a • A) :=
  (lengthCommensurable_iff_of_ge (Submodule.smul_le_self_of_tower a A)).mpr
    (relLength_smul_self_ne_top hA ha)

theorem signedLength_smul_self_of_addVal_eq (hA : A.FG) {a : R} {n : ℕ} (hn : addVal R a = n) :
    signedLength A (a • A) = (n : ℤ) * (Module.finrank R A : ℤ) := by
  have ha : a ≠ 0 := addVal_eq_top_iff.not.mp (hn ▸ ENat.coe_ne_top n)
  rw [← Nat.cast_mul, (lengthCommensurable_smul_self hA ha).signedLength_eq_natCast_iff_of_ge
    (Submodule.smul_le_self_of_tower a A), relLength_smul_self_of_addVal_eq hA hn]

theorem signedLength_smul_self (hA : A.FG) {a : R} (ha : a ≠ 0) :
    signedLength A (a • A) = ((addVal R a).toNat : ℤ) * (Module.finrank R A : ℤ) :=
  signedLength_smul_self_of_addVal_eq hA (ENat.coe_toNat (addVal_eq_top_iff.not.mpr ha)).symm

end DVR

end GlobalTheory
end
