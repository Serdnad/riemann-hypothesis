module

public import Development.EtaleCohomology.EtaleSheaves.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.EtaleSheaves.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open LateralTheory.E.t_E1Cut

namespace LateralTheory.E.LCGoodPf

theorem closed_empty {C : Type} [CommRing C] {J : Ideal C} (hJ : J ≤ Ideal.jacobson ⊥)
    (Z : Set (PrimeSpectrum C)) (hZ : IsClosed Z)
    (h : ∀ z : PrimeSpectrum (C ⧸ J), PrimeSpectrum.comap (Ideal.Quotient.mk J) z ∉ Z) : Z = ∅ := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).1 hZ
  by_cases hI : I = ⊤
  · subst hI; simp
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  exfalso
  have hJM : J ≤ M := le_trans hJ (sInf_le ⟨bot_le, hM⟩)
  have hp : (⟨M, hM.isPrime⟩ : PrimeSpectrum C) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
    have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ M := by rw [Ideal.mk_ker]; exact hJM
    have := hM.isPrime
    have hpr : (M.map (Ideal.Quotient.mk J)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    refine ⟨⟨M.map (Ideal.Quotient.mk J), hpr⟩, ?_⟩
    ext1
    show Ideal.comap _ (Ideal.map _ M) = M
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    refine sup_eq_left.2 ?_
    rw [← RingHom.ker_eq_comap_bot]; exact hker
  obtain ⟨z, hz⟩ := hp
  apply h z
  rw [hz]
  exact hIM

theorem lcMap_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {Y : Type}
    (φ : LocallyConstant (PrimeSpectrum A) Y) (z : PrimeSpectrum B) :
    lcMap f φ z = φ (PrimeSpectrum.comap f z) := rfl

theorem isClosed_ne {X Y : Type} [TopologicalSpace X] (a b : LocallyConstant X Y) :
    IsClosed {x | a x ≠ b x} := by
  have : IsLocallyConstant (fun x => (a x = b x : Prop)) :=
    IsLocallyConstant.comp₂ a.isLocallyConstant b.isLocallyConstant (fun u v => (u = v : Prop))
  have h2 := this.isClosed_fiber False
  convert h2 using 1
  ext x; simp

theorem LCGood_of : LCGood := by
  intro C _ J hG Y
  obtain ⟨hJ, hlift⟩ := hG
  constructor
  · intro a b hab
    have hZ := closed_empty hJ _ (isClosed_ne a b) (fun z hz => hz (by
      have := congrArg (fun φ => φ z) hab
      simpa [lcMap_apply] using this))
    ext x
    by_contra hx
    have : x ∈ ({x | a x ≠ b x} : Set _) := hx
    rw [hZ] at this; exact this
  · intro ψ

    have hU : ∀ y : Y, ∃ U : Set (PrimeSpectrum C), IsClopen U ∧
        PrimeSpectrum.comap (Ideal.Quotient.mk J) ⁻¹' U = ψ ⁻¹' {y} := by
      intro y
      obtain ⟨e, he, hF⟩ := PrimeSpectrum.isClopen_iff.1 (ψ.isLocallyConstant.isClopen_fiber y)
      obtain ⟨x, hx, hxe⟩ := hlift e he
      refine ⟨PrimeSpectrum.basicOpen x, PrimeSpectrum.isClopen_iff.2 ⟨x, hx, rfl⟩, ?_⟩
      have hF' : ψ ⁻¹' {y} = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum (C ⧸ J))) := hF
      rw [hF', ← hxe]
      ext p
      simp
    choose U hUc hUp using hU
    have hmem : ∀ z y, PrimeSpectrum.comap (Ideal.Quotient.mk J) z ∈ U y ↔ ψ z = y := by
      intro z y
      have := congrArg (fun s => z ∈ s) (hUp y)
      simpa using this
    have hcover : ∀ x, ∃ y, x ∈ U y := by
      have hE := closed_empty hJ (⋃ y, U y)ᶜ
        (isOpen_iUnion (fun y => (hUc y).isOpen)).isClosed_compl
        (fun z hz => hz (Set.mem_iUnion.2 ⟨ψ z, (hmem z _).2 rfl⟩))
      intro x
      by_contra hx
      push Not at hx
      have : x ∈ (⋃ y, U y)ᶜ := by simpa using hx
      rw [hE] at this
      exact this
    have huniq : ∀ x y y', x ∈ U y → x ∈ U y' → y = y' := by
      intro x y y' h1 h2
      by_contra hne
      have := closed_empty hJ (U y ∩ U y') ((hUc y).isClosed.inter (hUc y').isClosed)
        (fun z hz => hne (((hmem z y).1 hz.1).symm.trans ((hmem z y').1 hz.2)))
      have hx : x ∈ U y ∩ U y' := ⟨h1, h2⟩
      rw [this] at hx; exact hx
    classical
    let g : PrimeSpectrum C → Y := fun x => Classical.choose (hcover x)
    have hg : ∀ x y, g x = y ↔ x ∈ U y := by
      intro x y
      constructor
      · rintro rfl; exact Classical.choose_spec (hcover x)
      · intro h; exact huniq x _ _ (Classical.choose_spec (hcover x)) h
    have hgl : IsLocallyConstant g := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro y
      have : g ⁻¹' {y} = U y := by ext x; simp [hg]
      rw [this]; exact (hUc y).isOpen
    refine ⟨⟨g, hgl⟩, ?_⟩
    ext z
    rw [lcMap_apply]
    exact (hg _ _).2 ((hmem z _).2 rfl)

end LateralTheory.E.LCGoodPf
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.EqvQAPf

theorem prim_of_aic (q : ℕ) [NeZero q] (S : Type) [CommRing S] (hS : AIC S) (hq : IsUnit (q : S)) :
    Nonempty (Prim q S) := by
  rcases subsingleton_or_nontrivial S with hs | hs
  · exact ⟨⟨0, hq, Subsingleton.elim _ _⟩⟩
  have hm : ((Polynomial.cyclotomic q ℤ).map (Int.castRingHom S)).Monic :=
    (Polynomial.cyclotomic.monic q ℤ).map _
  have hd : 0 < ((Polynomial.cyclotomic q ℤ).map (Int.castRingHom S)).natDegree := by
    rw [(Polynomial.cyclotomic.monic q ℤ).natDegree_map, Polynomial.natDegree_cyclotomic]
    exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  obtain ⟨a, ha⟩ := hS _ hm hd
  exact ⟨⟨a, hq, by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]; simpa using ha⟩⟩

theorem bij_of_sub {A B : Type*} [AddZeroClass A] [AddZeroClass B] [Subsingleton A] [Subsingleton B] (f : A →+ B) :
    Function.Bijective f :=
  ⟨fun x y _ => Subsingleton.elim x y, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end LateralTheory.E.EqvQAPf

open LateralTheory.E.t_E1Cut in
theorem LateralTheory.E.t_E1Cut.EqvQA_of (hAcyc : AcycQA) (hQA : QAClosed) (hH0 : EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions) (hLC : LCGood) : EqvQA := by
  intro h1 h9 hb1 hb2 q _ S _ J hS hJ hq i n
  have hqJ : IsUnit (q : S ⧸ J) := by simpa using hq.map (Ideal.Quotient.mk J)
  have hSJ : QA (S ⧸ J) := (hQA S hS).2.2 J
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := (h9 (ZMod q) (tw q i)).1 (sp S) n hn
    haveI := (h9 (ZMod q) (tw q i)).1 (sp (S ⧸ J)) n hn
    exact LateralTheory.E.EqvQAPf.bij_of_sub _
  · obtain ⟨ζ⟩ := LateralTheory.E.EqvQAPf.prim_of_aic q S (hQA S hS).1 hq
    obtain ⟨e, he⟩ := hH0 h9 q i
    have key : ∀ φ, pull _ (spMap (Ideal.Quotient.mk J)) (tw q i) 0 (e S ζ φ) =
        e (S ⧸ J) (ζ.map (Ideal.Quotient.mk J)) (lcMap (Ideal.Quotient.mk J) φ) :=
      fun φ => he S (S ⧸ J) (Ideal.Quotient.mk J) ζ φ
    have hcomp : (pull _ (spMap (Ideal.Quotient.mk J)) (tw q i) 0) =
        (e (S ⧸ J) (ζ.map (Ideal.Quotient.mk J))) ∘
          (fun φ => lcMap (Ideal.Quotient.mk J) φ) ∘ (e S ζ).symm := by
      funext x
      obtain ⟨φ, rfl⟩ := (e S ζ).surjective x
      simp only [Function.comp_apply, AddEquiv.symm_apply_apply]
      exact key φ
    rw [hcomp]
    exact (e _ _).bijective.comp ((hLC S J hJ (ZMod q)).comp (e S ζ).symm.bijective)
  · haveI := hAcyc h1 h9 hb1 hb2 q S hS hq n i hn
    haveI := hAcyc h1 h9 hb1 hb2 q (S ⧸ J) hSJ hqJ n i hn
    exact LateralTheory.E.EqvQAPf.bij_of_sub _
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.t_D3Cut

abbrev BX (Γ : Type) [Group Γ] (X : Scheme.{0}) : Spc := cst (SingleObj Γ) ⨯ sch.obj X

def slantHom (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R) :
    (free R).obj (yoneda.obj X) ⟶ (free R).obj ((BX Γ X).obj (op (SimplexCategory.mk m))) :=
  c.sum fun g r => (ULift.up r : ULift.{1} R) • (free R).map (grpPt X g)

def slantV (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R) :
    ((chains R).obj (sch.obj X)).X 0 ⟶ ((chains R).obj (BX Γ X)).X (-(m : ℤ)) :=
  (((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
      (((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj X))).extendXIso
      ComplexShape.embeddingDownNat (i := 0) (i' := 0) (by simp)).hom ≫ slantHom R X c ≫
    (((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
      (((SimplicialObject.whiskering _ _).obj (free R)).obj (BX Γ X))).extendXIso
      ComplexShape.embeddingDownNat (i := m) (i' := -(m : ℤ)) (by simp)).inv

def slantCo (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R) :
    Cochain ((chains R).obj (sch.obj X)) ((chains R).obj (BX Γ X)) (-(m : ℤ)) :=
  Cochain.single (slantV R X c) (-(m : ℤ))

abbrev bd (R : Type) [CommRing R] {Γ : Type} [Group Γ] {m : ℕ} (b : (Fin (m + 1) → Γ) →₀ R) : (Fin m → Γ) →₀ R :=
  groupHomology.inhomogeneousChains.d (Rep.trivial R Γ R) m b

def Faces : Prop := ∀ (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ) (g : Fin (m + 1) → Γ),
  grpPt X g ≫ (BX Γ X).δ 0 = grpPt X (fun i => g i.succ) ∧
  ∀ j : Fin (m + 1), grpPt X g ≫ (BX Γ X).δ j.succ = grpPt X (j.contractNth (· * ·) g)

def HomD : Prop := ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ) (b : (Fin (m + 1) → Γ) →₀ R),
  slantHom R X b ≫ ((chainsN R).obj (BX Γ X)).d (m + 1) m = slantHom R X (bd R b)

def DeltaCo : Prop := ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}),
  (∀ c : (Fin 0 → Γ) →₀ R, δ (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) (slantCo R X c) = 0) ∧
  ∀ (m : ℕ) (b : (Fin (m + 1) → Γ) →₀ R), δ (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ)) (slantCo R X b) = slantCo R X (bd R b)

section
variable (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ}

theorem slantHom_zero : slantHom R X (0 : (Fin m → Γ) →₀ R) = 0 := Finsupp.sum_zero_index

theorem slantHom_single (g : Fin m → Γ) (r : R) :
    slantHom R X (Finsupp.single g r) = (ULift.up r : ULift.{1} R) • (free R).map (grpPt X g) :=
  Finsupp.sum_single_index (zero_smul (ULift.{1} R) _)

theorem slantHom_add (c c' : (Fin m → Γ) →₀ R) : slantHom R X (c + c') = slantHom R X c + slantHom R X c' :=
  Finsupp.sum_add_index' (fun _ => zero_smul (ULift.{1} R) _)
    (fun _ r s => add_smul (ULift.up r : ULift.{1} R) (ULift.up s) _)

theorem slantV_add (c c' : (Fin m → Γ) →₀ R) : slantV R X (c + c') = slantV R X c + slantV R X c' := by
  unfold slantV
  rw [slantHom_add]
  erw [Preadditive.add_comp, Preadditive.comp_add]

theorem slantCo_v (c : (Fin m → Γ) →₀ R) : (slantCo R X c).v 0 (-(m : ℤ)) (zero_add _) = slantV R X c :=
  Cochain.single_v _ _ _

theorem slantCo_v_ne (c : (Fin m → Γ) →₀ R) (p p' : ℤ) (h : p + -(m : ℤ) = p') (hp : p ≠ 0) :
    (slantCo R X c).v p p' h = 0 := Cochain.single_v_eq_zero _ _ _ _ _ hp

theorem slantCo_add (c c' : (Fin m → Γ) →₀ R) : slantCo R X (c + c') = slantCo R X c + slantCo R X c' := by
  ext p p' h : 1
  by_cases hp : p = 0
  · subst hp
    obtain rfl : p' = -(m : ℤ) := by omega
    rw [Cochain.add_v, slantCo_v, slantCo_v, slantCo_v, slantV_add]
  · rw [Cochain.add_v, slantCo_v_ne _ _ _ _ _ _ hp, slantCo_v_ne _ _ _ _ _ _ hp, slantCo_v_ne _ _ _ _ _ _ hp, add_zero]

theorem slantCo_zero : slantCo R X (0 : (Fin m → Γ) →₀ R) = 0 := by
  have h := slantCo_add R X (0 : (Fin m → Γ) →₀ R) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem isSlant_iff (c : (Fin m → Γ) →₀ R) (z) : IsSlant R X c z ↔ z.1 = slantCo R X c := by
  constructor
  · rintro ⟨h1, h2⟩
    ext p p' h : 1
    by_cases hp : p = 0
    · subst hp
      obtain rfl : p' = -(m : ℤ) := by omega
      rw [slantCo_v]; exact h2
    · rw [slantCo_v_ne _ _ _ _ _ _ hp]; exact h1 p p' h hp
  · intro h
    refine ⟨fun p p' hh hp => ?_, ?_⟩
    · rw [h]; exact slantCo_v_ne _ _ _ _ _ _ hp
    · rw [h]; exact slantCo_v _ _ _

end

theorem closed (h : DeltaCo) (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ)
    (c : groupHomology.cycles (Rep.trivial R Γ R) m) :
    δ (-(m : ℤ)) (-(m : ℤ) + 1) (slantCo R X (groupHomology.iCycles (Rep.trivial R Γ R) m c)) = 0 := by
  cases m with
  | zero => exact (h R Γ X).1 _
  | succ m =>
    have h1 := (h R Γ X).2 m (groupHomology.iCycles (Rep.trivial R Γ R) (m + 1) c)
    have h2 : bd R (groupHomology.iCycles (Rep.trivial R Γ R) (m + 1) c) = 0 := by
      have h3 := ConcreteCategory.congr_hom
        ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).iCycles_d (m + 1) m) c
      rw [groupHomology.inhomogeneousChains.d_def] at h3
      exact h3
    rw [h2, slantCo_zero] at h1
    have h4 : ∀ k : ℤ, k = -(m : ℤ) →
        δ (-((m + 1 : ℕ) : ℤ)) k (slantCo R X (groupHomology.iCycles (Rep.trivial R Γ R) (m + 1) c)) = 0 := by
      rintro _ rfl; exact h1
    exact h4 _ (by omega)

theorem exists_bd (R : Type) [CommRing R] (Γ : Type) [Group Γ] (m : ℕ)
    (c : groupHomology.cycles (Rep.trivial R Γ R) m) (hc : groupHomology.π (Rep.trivial R Γ R) m c = 0) :
    ∃ b, bd R b = groupHomology.iCycles (Rep.trivial R Γ R) m c := by
  have e : (ShortComplex.mk _ _ ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).toCycles_comp_homologyπ (m + 1) m)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _
      ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).homologyIsCokernel (m + 1) m (by simp))
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).1 e c hc
  refine ⟨b, ?_⟩
  have h3 := ConcreteCategory.congr_hom
    ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).toCycles_i (m + 1) m) b
  rw [groupHomology.inhomogeneousChains.d_def] at h3
  rw [← hb]
  exact h3.symm

theorem cpre_add {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {m : ℤ} (a a' : Cocycle K L m)
    (M : CochainComplex C ℤ) (n k : ℤ) (h : m + n = k) : cpre (a + a') M n k h = cpre a M n k h + cpre a' M n k h := by
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [AddMonoidHom.add_apply, cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  congr 1
  exact Cocycle.ext (Cochain.add_comp _ _ _ h)

theorem cpre_eq_zero {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {m m' : ℤ} (a : Cocycle K L m)
    (hm : m' + 1 = m) (w : Cochain K L m') (hw : δ m' m w = a.1)
    (M : CochainComplex C ℤ) (n k : ℤ) (h : m + n = k) : cpre a M n k h = 0 := by
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  have h1 : cpost K x m k h (CohomologyClass.mk a) = 0 := by
    rw [(CohomologyClass.mk_eq_zero_iff a).2 ⟨m', hm, w, hw⟩, map_zero]
  exact h1

theorem etale_group_homology_slant_of_delta_cochain (h : DeltaCo) : D3 := by
  intro R _ Γ _ X m
  let z : groupHomology.cycles (Rep.trivial R Γ R) m → Cocycle ((chains R).obj (sch.obj X)) ((chains R).obj (BX Γ X)) (-(m : ℤ)) :=
    fun c => Cocycle.mk _ _ rfl (closed h R Γ X m c)
  refine ⟨fun c => ⟨z c, (isSlant_iff R X _ _).2 rfl⟩, fun F n => ?_⟩
  have hex : ∃ S, IsSlantMap R Γ X F m n S := by
    let T : groupHomology.cycles (Rep.trivial R Γ R) m →+ H R (BX Γ X) F (m + n) →+ H R (sch.obj X) F n :=
      AddMonoidHom.mk' (fun c => HK.pre R (z c) F (m + n) n (by ring)) (fun c c' => by
        have : z (c + c') = z c + z c' := Cocycle.ext (by
          change slantCo R X (groupHomology.iCycles (Rep.trivial R Γ R) m (c + c')) = slantCo R X _ + slantCo R X _
          rw [map_add (f := _)]; exact slantCo_add R X _ _)
        rw [this]; exact cpre_add _ _ _ _ _ _)
    have hs : Function.Surjective (groupHomology.π (Rep.trivial R Γ R) m).hom.toAddMonoidHom :=
      (ModuleCat.epi_iff_surjective (groupHomology.π (Rep.trivial R Γ R) m)).1
        (inferInstanceAs (Epi ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).homologyπ m)))
    have hk : (groupHomology.π (Rep.trivial R Γ R) m).hom.toAddMonoidHom.ker ≤ T.ker := by
      intro c hc
      obtain ⟨b, hb⟩ := exists_bd R Γ m c hc
      refine cpre_eq_zero (z c) (m' := -((m + 1 : ℕ) : ℤ)) (by omega) (slantCo R X b) ?_ _ _ _ _
      rw [(h R Γ X).2 m b, hb]; rfl
    refine ⟨AddMonoidHom.liftOfSurjective _ hs ⟨T, hk⟩, fun c z' hz' => ?_⟩
    have e : z' = z c := Cocycle.ext ((isSlant_iff R X _ _).1 hz')
    rw [e]
    exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨T, hk⟩ c
  unfold slantR
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem goal_of (h : DeltaCo) : LateralTheory.E.EtaleChapterDThree :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => etale_group_homology_slant_of_delta_cochain h

end LateralTheory.E.t_D3Cut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.DescStepPf

def Bounds : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
  ((chains R).obj E).IsStrictlyLE 0 ∧ (res R F).IsStrictlyGE 0 ∧ ∀ m, Injective ((res R F).X m)

def LevelIdent : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') (p : ℕ) (j : ℤ),
  (Function.Bijective (pull R (disc.map (f.app (op (SimplexCategory.mk p)))) F j) ↔
    Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (((chains R).map f).f (-(p : ℤ)))) (res R F) j)) ∧
  (Function.Injective (pull R (disc.map (f.app (op (SimplexCategory.mk p)))) F j) ↔
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (((chains R).map f).f (-(p : ℤ)))) (res R F) j))

def CxDesc : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (n : ℤ),
  (∀ (p : ℕ) (j : ℤ), j < n → Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-(p : ℤ)))) I j)) →
  (∀ p : ℕ, Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-(p : ℤ)))) I n)) →
  (∀ j : ℤ, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j)) →
  (∀ j : ℤ, j < n + 1 → Function.Bijective (cpull g I j)) ∧ Function.Injective (cpull g I (n + 1))

theorem DescStep_of (hB : Bounds) (hL : LevelIdent) (hX : CxDesc) : LateralTheory.E.t_E1Cut.DescStep := by
  intro _ R _ F E E' f n hc he
  obtain ⟨h1, h2, h3⟩ := hB R F E
  obtain ⟨h1', -, -⟩ := hB R F E'
  have := h2
  have := h1
  have := h1'
  exact hX R (res R F) h3 ((chains R).map f) n
    (fun p j hj => ((hL R F f p j).1).1 ((hc (op (SimplexCategory.mk p))).1 j hj))
    (fun p => ((hL R F f p n).2).1 (hc (op (SimplexCategory.mk p))).2)
    (fun j => ((hL R F f 0 j).1).1 (he j))

end LateralTheory.E.DescStepPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitAWPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf

theorem sec_sub {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) (U : Scheme.{0}) :
    Subsingleton (Sec ((res R F).X s) U) := by
  have hz : IsZero ((res R F).X s) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have h2 : IsZero (((res R F).X s).obj.obj (op U)) :=
    Functor.map_isZero ((sheafToPresheaf _ _) ⋙ (evaluation _ _).obj (op U)) hz
  exact ModuleCat.isZero_iff_subsingleton.mp h2

theorem sub_zero_self {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval (n := N) 0 N h = 𝟙 _ := by
    ext i : 3
    simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem main_gen (q : ℕ) [NeZero q] (E : Spc) (i j : ℤ) (hij : i = j)
    (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q j)))
    (hU : ∀ (U : Scheme.{0}) (t w : ℤ) (h : 0 + t = w) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → HEq (μ.mul U 0 t w h a b) b)
    (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) (hα : OneLoc α)
    (n k : ℤ) (hnk : n = k) (β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q i)) n) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q j)) k, μ.IsAW (show 0 + n = k by omega) α.1 β.1 γ.1 ∧
      CohomologyClass.mk γ = Ht.cast hnk hij (CohomologyClass.mk β : Ht q E n i) := by
  subst hij hnk
  refine ⟨β, ?_, rfl⟩
  intro N w h U x
  have hmz : ∀ (s t w : ℤ) (h : s + t = w) (a : Sec ((res _ (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
      s < 0 → μ.mul U s t w h a b = 0 := by
    intro s t w h a b hs
    have := sec_sub (tw q 0) s hs U
    rw [Subsingleton.elim a 0]
    simp
  rw [Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · subst h
    show _ = (n * ((0 : ℕ) : ℤ)).negOnePow • μ.mul U (-((0 : ℕ) : ℤ) + 0) (-((N - 0 : ℕ) : ℤ) + n) (-(N : ℤ) + n) (by omega)
      (ev α.1 0 _ rfl U (x.sub 0 0 (by omega))) (ev β.1 (N - 0) _ rfl U (x.sub 0 (N - 0) (by omega)))
    have h1 : (n * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
    rw [h1, one_smul]
    show _ = μ.mul U 0 (-(N : ℤ) + n) (-(N : ℤ) + n) (by omega)
      (ev α.1 0 0 (by simp) U (x.sub 0 0 (by omega))) (ev β.1 N _ rfl U (x.sub 0 N (by omega)))
    rw [sub_zero_self]
    exact (eq_of_heq (hU U _ _ (by omega) _ (ev β.1 N _ rfl U x) (hα U (x.sub 0 0 (by omega))))).symm
  · intro p _
    rw [hmz, smul_zero]
    simp
    omega

theorem LeafUnitAW_of : LeafUnitAW := by
  intro q _ E i μ hU α hα n β
  exact main_gen q E i (0 + i) (by ring) μ hU α hα n (0 + n) (by ring) β

end LateralTheory.E.LeafUnitAWPf
end
end
