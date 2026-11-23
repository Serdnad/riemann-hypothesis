module

public import Development.EtaleCohomology.EtaleSheaves.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.EtaleCohomology.EtaleSheaves.Bundle023
public import Mathlib.Tactic.ENatToNat
public import Development.EtaleCohomology.EtaleSheaves.Bundle024
public import Development.EtaleCohomology.EtaleSheaves.Bundle025
import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Development.EtaleCohomology.EtaleSheaves.Bundle026
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Comma.LocallySmall
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Unramified.LocalStructure
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ChainsDiscCoprodPf

variable (R : Type) [CommRing R]

theorem chains_disc_f {P Q : PSh} (f : P ⟶ Q) (n : ℕ) :
    ((chains R).map (disc.map f)).f (-(n : ℤ)) =
      (chainsXIso R (disc.obj P) n).hom ≫ (free R).map f ≫ (chainsXIso R (disc.obj Q) n).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := n) rfl]
  rfl

theorem isZero_chains_X (E : Spc) (i : ℤ) (hi : ∀ n : ℕ, -(n : ℤ) ≠ i) :
    IsZero (((chains R).obj E).X i) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat i (fun n => hi n)

theorem cofan_of_isos {C : Type*} [Category C] {ι : Type} {A A' : ι → C} {B B' : C}
    (a : ∀ j, A' j ≅ A j) (b : B' ≅ B) (f : ∀ j, A j ⟶ B) (f' : ∀ j, A' j ⟶ B')
    (hf : ∀ j, f' j = (a j).hom ≫ f j ≫ b.inv) (hc : IsColimit (Cofan.mk B f)) :
    Nonempty (IsColimit (Cofan.mk B' f')) := by
  refine ⟨Cofan.IsColimit.mk _ (fun s => b.hom ≫ hc.desc (Cofan.mk s.pt fun j => (a j).inv ≫ s.inj j)) ?_ ?_⟩
  · intro s j
    have := hc.fac (Cofan.mk s.pt fun j => (a j).inv ≫ s.inj j) ⟨j⟩
    simp only [Cofan.mk_ι_app] at this
    change f' j ≫ _ = _
    simp only [hf, Category.assoc, Iso.inv_hom_id_assoc, this, Iso.hom_inv_id_assoc]
  · intro s m hm
    rw [← Iso.inv_comp_eq]
    refine hc.uniq (Cofan.mk s.pt fun j => (a j).inv ≫ s.inj j) _ ?_
    rintro ⟨j⟩
    change f j ≫ b.inv ≫ m = (a j).inv ≫ s.inj j
    rw [← hm j]
    change f j ≫ b.inv ≫ m = (a j).inv ≫ f' j ≫ m
    simp only [hf, Category.assoc, Iso.inv_hom_id_assoc]

theorem cofan_of_zero {C : Type*} [Category C] [HasZeroMorphisms C] {ι : Type} {A : ι → C} {B : C}
    (hA : ∀ j, IsZero (A j)) (hB : IsZero B) (f : ∀ j, A j ⟶ B) :
    Nonempty (IsColimit (Cofan.mk B f)) :=
  ⟨Cofan.IsColimit.mk _ (fun _ => 0) (fun _ j => (hA j).eq_of_src _ _) (fun _ _ _ => hB.eq_of_src _ _)⟩

theorem degColimit {ι : Type} (P : ι → PSh) (Q : PSh) (p : ∀ j, P j ⟶ Q)
    (hc : IsColimit (Cofan.mk ((free R).obj Q) fun j => (free R).map (p j))) (i : ℤ) :
    Nonempty (IsColimit ((HomologicalComplex.eval _ _ i).mapCocone
      (Cofan.mk ((chains R).obj (disc.obj Q)) fun j => (chains R).map (disc.map (p j))))) := by
  rw [(isColimitMapCoconeCofanMkEquiv _ _ _).nonempty_congr]
  by_cases h : 0 < i
  · have h' : ∀ n : ℕ, -(n : ℤ) ≠ i := fun n => by omega
    exact cofan_of_zero (fun j => isZero_chains_X R _ i h') (isZero_chains_X R _ i h') _
  · have hi : i = -(((-i).toNat : ℕ) : ℤ) := by omega
    rw [hi]
    generalize (-i).toNat = n
    exact cofan_of_isos (fun j => chainsXIso R (disc.obj (P j)) n) (chainsXIso R (disc.obj Q) n)
      (fun j => (free R).map (p j)) _ (fun j => chains_disc_f R (p j) n) hc

theorem ChainsDiscCoprod_of : LateralTheory.E.CoprodPf.ChainsDiscCoprod := by
  intro R _ ι P Q p ⟨hc⟩
  exact ⟨HomologicalComplex.isColimitOfEval _ _ (fun i => (degColimit R P Q p hc i).some)⟩

end LateralTheory.E.ChainsDiscCoprodPf
end
end

section

noncomputable section
open CategoryTheory Limits IsLocalRing

namespace LateralTheory.E.SHAlgSecPf

theorem retract_alg {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)] [Algebra.Etale A R] (Q : Ideal R) [Q.IsPrime]
    (hQ : (Q.comap (algebraMap A R)).IsMaximal) : Nonempty (R →ₐ[A] A) := by
  have hQm : Q.comap (algebraMap A R) = maximalIdeal A := IsLocalRing.eq_maximalIdeal hQ
  have hEt : Algebra.IsEtaleAt A Q := by
    have h := (Algebra.etaleLocus_eq_univ_iff_etale (R := A) (A := R)).mpr inferInstance
    have : (⟨Q, inferInstance⟩ : PrimeSpectrum R) ∈ Algebra.etaleLocus A R := by rw [h]; trivial
    exact this
  obtain ⟨g, hgQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let Rg := Localization.Away g
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid R) : Set R) (Q : Set R) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hgQ
  let Q' : Ideal Rg := Q.map (algebraMap R Rg)
  have hQ'p : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Rg Q ‹_› hdisj
  have hQ'c : Q'.comap (algebraMap R Rg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Rg ‹_› hdisj
  have hcomap : Q'.comap (algebraMap A Rg) = RingHom.ker (algebraMap A (ResidueField A)) := by
    rw [IsScalarTower.algebraMap_eq A R Rg, ← Ideal.comap_comap, hQ'c, hQm,
      ResidueField.algebraMap_eq, ker_residue]
  obtain ⟨φ⟩ := GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed (R := A) (K := ResidueField A) Q' hcomap
  obtain ⟨ψ, -⟩ := GlobalTheory.exists_algHom_lift_of_isStandardEtale (R := A) (A := Rg) (B := A)
    (C := ResidueField A) (maximalIdeal A) (Algebra.ofId A (ResidueField A))
    (residue_surjective) (fun b => by
      simp [Algebra.ofId_apply, ResidueField.algebraMap_eq, residue_eq_zero_iff]) φ
  exact ⟨ψ.comp (IsScalarTower.toAlgHom A R Rg)⟩

theorem SHAlgSec_of : LateralTheory.E.SHSectionPf.SHAlgSec := by
  intro A R f hA hf hQ
  obtain ⟨hH, hS⟩ := hA
  let := f.hom.toAlgebra
  have : Algebra.Etale A R := (RingHom.etale_algebraMap).mp hf
  obtain ⟨Q, hQp, hQm⟩ := hQ
  obtain ⟨σ⟩ := retract_alg (A := A) (R := R) Q hQm
  refine ⟨CommRingCat.ofHom σ.toRingHom, ?_⟩
  ext a
  exact σ.commutes a

end LateralTheory.E.SHAlgSecPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf

namespace LateralTheory.E.LeafGeomPfLoc

theorem projective_bundle_direct_sum_zero_vertex_coordinates_restrict {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X Y : Scheme.{0}}
    (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) (j : Fin (a + b)) :
    vec0 V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) j = Scheme.Γ.map k.op (vec0 V W x j) := by
  set_option synthInstance.maxHeartbeats 200000 in
  have h := ConcreteCategory.congr_hom (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).naturality k.op) x
  unfold vec0
  erw [h]
  rfl

theorem unit_le {X : Scheme.{0}} (f : Γ(X, ⊤)) {V : X.Opens} (h : V ≤ X.basicOpen f) :
    IsUnit ((X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom f) := by
  have hu := X.toRingedSpace.isUnit_res_basicOpen (U := ⊤) f
  have := hu.map (X.presheaf.map (homOfLE h).op).hom
  erw [← CommRingCat.comp_apply, ← Functor.map_comp] at this
  exact this

theorem unit_basicOpen {X : Scheme.{0}} (f : Scheme.Γ.obj (op X)) :
    IsUnit (Scheme.Γ.map (X.basicOpen f).ι.op f) := by
  rw [Scheme.Γ_map_op, Scheme.Opens.ι_appTop]
  exact unit_le f (X.basicOpen f).ι_image_top.le

theorem leafLocal : LeafLocal := by
  intro E a b V W n X x
  have hspan : Ideal.span (Set.range (vec0 V W x)) = ⊤ :=
    ((show Fin (n + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X)) from
      ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x).obj 0).2
  have hcov : TopologicalSpace.IsOpenCover (fun j => X.basicOpen (vec0 V W x j)) := by
    have := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top (X := X) ⊤ (Set.range (vec0 V W x)) hspan
    refine le_antisymm le_top ?_
    rw [← this]
    exact iSup₂_le fun _ ⟨j, hj⟩ => hj ▸ le_iSup (fun j => X.basicOpen (vec0 V W x j)) j
  let 𝒰 := X.openCoverOfIsOpenCover _ hcov
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.zariskiTopology_le_etaleTopology _ 𝒰.mem_grothendieckTopology, ?_⟩
  intro Y k hk
  rw [Sieve.mem_ofArrows_iff] at hk
  obtain ⟨j, g, rfl⟩ := hk
  have hu : IsUnit (Scheme.Γ.map (g ≫ 𝒰.f j).op (vec0 V W x j)) := by
    rw [op_comp, Functor.map_comp]
    exact (unit_basicOpen (vec0 V W x j)).map (Scheme.Γ.map g.op).hom
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ : (∃ i, j = Fin.castAdd b i) ∨ ∃ i, j = Fin.natAdd a i :=
    Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) j
  · left
    simp only [First, projective_bundle_direct_sum_zero_vertex_coordinates_restrict]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hu
  · right
    simp only [Second, projective_bundle_direct_sum_zero_vertex_coordinates_restrict]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hu

theorem LeafGeom_of (h1 : LeafHalf1) (h2 : LeafHalf2) : LateralTheory.E.D2.LeafGeom :=
  LateralTheory.E.LeafGeomPf.LeafGeom_of h1 h2 leafLocal

end LateralTheory.E.LeafGeomPfLoc
end
end

section

noncomputable section
open CategoryTheory

namespace LateralTheory.E.IdemCoverPf

variable (C : Type) [CommRing C]

abbrev P := ∀ p : PrimeSpectrum C, C ⧸ p.asIdeal


open Classical in
def e (c : C) : P C := fun p => if c ∈ p.asIdeal then 1 else 0

abbrev D := Algebra.adjoin C (Set.range (e C))

variable {C}

def Ei (c : C) : D C := ⟨e C c, Algebra.subset_adjoin ⟨c, rfl⟩⟩

theorem coord_alg (c : C) (p : PrimeSpectrum C) :
    ((algebraMap C (D C) c : D C) : P C) p = Ideal.Quotient.mk p.asIdeal c := rfl

theorem E_mul_one_sub (c : C) : Ei c * (1 - Ei c) = 0 := by
  apply Subtype.ext; funext p
  show e C c p * (1 - e C c p) = 0
  unfold e; split_ifs <;> simp

theorem E_mul_alg (c : C) : Ei c * algebraMap C (D C) c = 0 := by
  apply Subtype.ext; funext p
  show e C c p * Ideal.Quotient.mk p.asIdeal c = 0
  unfold e; split_ifs with h
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 h, mul_zero]
  · simp

theorem one_sub_E_mul (a b : C) : 1 - Ei (a * b) = (1 - Ei a) * (1 - Ei b) := by
  apply Subtype.ext; funext p
  show 1 - e C (a * b) p = (1 - e C a p) * (1 - e C b p)
  unfold e
  have := p.isPrime.mul_mem_iff_mem_or_mem (x := a) (y := b)
  split_ifs <;> simp_all

theorem ann_alg (t : D C) (c : C) (h : t * algebraMap C (D C) c = 0) : t * (1 - Ei c) = 0 := by
  apply Subtype.ext; funext p
  have hp := congrArg (fun x : D C => (x : P C) p) h
  simp only [Subalgebra.coe_mul, Pi.mul_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at hp
  show (t : P C) p * (1 - e C c p) = 0
  unfold e; split_ifs with hc
  · simp
  · rw [coord_alg] at hp
    have hne : Ideal.Quotient.mk p.asIdeal c ≠ 0 := fun h0 => hc (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    rw [mul_eq_zero] at hp
    simp [hp.resolve_right hne]

theorem integral : Algebra.IsIntegral C (D C) := by
  apply Algebra.IsIntegral.adjoin
  rintro _ ⟨c, rfl⟩
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1), Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, map_one]
  funext p; simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.zero_apply]; unfold e; split_ifs <;> simp

theorem approx (r : Ideal (D C)) [r.IsPrime] (s : D C) :
    ∃ ε : D C, ε ∉ r ∧ ∃ c : C, ε * s = ε * algebraMap C (D C) c := by
  obtain ⟨x, hx⟩ := s
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c, rfl⟩ := hx
    by_cases hc : Ei c ∈ r
    · refine ⟨1 - Ei c, fun h => r.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance) ?_, 0, ?_⟩
      · have := r.add_mem h hc; simpa using this
      · rw [map_zero, mul_zero, mul_comm]; exact E_mul_one_sub c
    · refine ⟨Ei c, hc, 1, ?_⟩
      rw [map_one, mul_one]
      apply Subtype.ext; funext p
      show e C c p * e C c p = e C c p
      unfold e; split_ifs <;> simp
  | algebraMap c => exact ⟨1, fun h => (Ideal.IsPrime.ne_top inferInstance) (r.eq_top_of_isUnit_mem h isUnit_one), c, rfl⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨ε1, h1, c1, e1⟩ := ihx
    obtain ⟨ε2, h2, c2, e2⟩ := ihy
    refine ⟨ε1 * ε2, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim h1 h2, c1 + c2, ?_⟩
    have : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : D C) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add (f := _)]
    linear_combination ε2 * e1 + ε1 * e2
  | mul x y hx hy ihx ihy =>
    obtain ⟨ε1, h1, c1, e1⟩ := ihx
    obtain ⟨ε2, h2, c2, e2⟩ := ihy
    refine ⟨ε1 * ε2, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim h1 h2, c1 * c2, ?_⟩
    have : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : D C) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul]
    linear_combination (ε2 * ⟨y, hy⟩) * e1 + (ε1 * algebraMap C (D C) c1) * e2

section Loc
variable (r : Ideal (D C)) [r.IsPrime]
local notation "L" => Localization.AtPrime r

theorem unit_of (x : D C) (hx : x ∉ r) : IsUnit (algebraMap (D C) L x) :=
  IsLocalization.map_units L (⟨x, hx⟩ : r.primeCompl)

theorem eq_of_approx (s : D C) : ∃ c : C, algebraMap (D C) L s = algebraMap (D C) L (algebraMap C (D C) c) := by
  obtain ⟨ε, hε, c, h⟩ := approx r s
  refine ⟨c, ?_⟩
  have h' := congrArg (algebraMap (D C) L) h
  rw [map_mul, map_mul] at h'
  exact (unit_of r ε hε).mul_left_cancel h'

theorem frac (z : L) : ∃ a b : C, IsUnit (algebraMap (D C) L (algebraMap C (D C) b)) ∧
    z * algebraMap (D C) L (algebraMap C (D C) b) = algebraMap (D C) L (algebraMap C (D C) a) := by
  obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective r.primeCompl z
  obtain ⟨a, ha⟩ := eq_of_approx r x
  obtain ⟨b, hb⟩ := eq_of_approx r (t : D C)
  refine ⟨a, b, hb ▸ unit_of r t t.2, ?_⟩
  simp only
  rw [← hb, ← ha, IsLocalization.mk'_spec]

theorem zero_of_E (a : C) (h : Ei a ∉ r) : algebraMap (D C) L (algebraMap C (D C) a) = 0 := by
  have h' := congrArg (algebraMap (D C) L) (E_mul_alg a)
  rw [map_mul, map_zero] at h'
  exact (unit_of r _ h).mul_right_eq_zero.1 h'

theorem domain : IsDomain L := by
  have key : ∀ a b : C, algebraMap (D C) L (algebraMap C (D C) (a * b)) = 0 →
      algebraMap (D C) L (algebraMap C (D C) a) = 0 ∨ algebraMap (D C) L (algebraMap C (D C) b) = 0 := by
    intro a b h
    obtain ⟨⟨t, ht⟩, h0⟩ := (IsLocalization.map_eq_zero_iff r.primeCompl L _).1 h
    have h1 := ann_alg t (a * b) h0
    have hm : t * (1 - Ei (a * b)) ∈ r := h1 ▸ r.zero_mem
    have h2 : 1 - Ei (a * b) ∈ r := (Ideal.IsPrime.mem_or_mem inferInstance hm).resolve_left ht
    rw [one_sub_E_mul] at h2
    have hne : ∀ c : C, 1 - Ei c ∈ r → Ei c ∉ r := fun c h3 h4 =>
      (Ideal.IsPrime.ne_top inferInstance) (r.eq_top_iff_one.2 (by simpa using r.add_mem h3 h4))
    rcases Ideal.IsPrime.mem_or_mem inferInstance h2 with h3 | h3
    · exact Or.inl (zero_of_E r a (hne a h3))
    · exact Or.inr (zero_of_E r b (hne b h3))
  haveI : NoZeroDivisors L := ⟨fun {x y} hxy => by
    obtain ⟨a, b, hb, hx⟩ := frac r x
    obtain ⟨a', b', hb', hy⟩ := frac r y
    have : algebraMap (D C) L (algebraMap C (D C) (a * a')) = 0 := by
      rw [map_mul, map_mul, ← hx, ← hy]
      calc x * _ * (y * _) = x * y * (algebraMap (D C) L (algebraMap C (D C) b) *
          algebraMap (D C) L (algebraMap C (D C) b')) := by ring
        _ = 0 := by rw [hxy, zero_mul]
    rcases key a a' this with h | h
    · left; rw [← hx] at h; exact hb.mul_left_eq_zero.1 h
    · right; rw [← hy] at h; exact hb'.mul_left_eq_zero.1 h⟩
  exact NoZeroDivisors.to_isDomain L

end Loc

theorem spS (q : Ideal C) (hq : q.IsPrime) : ∃ Q : Ideal (D C), Q.IsPrime ∧ Q.comap (algebraMap C (D C)) = q := by
  let φ : D C →+* C ⧸ q := (Pi.evalRingHom (fun p : PrimeSpectrum C => C ⧸ p.asIdeal) ⟨q, hq⟩).comp
    (D C).val.toRingHom
  haveI := hq
  refine ⟨RingHom.ker φ, RingHom.ker_isPrime φ, ?_⟩
  rw [RingHom.comap_ker]
  have : φ.comp (algebraMap C (D C)) = Ideal.Quotient.mk q := by ext c; rfl
  rw [this, Ideal.mk_ker]

theorem IdemCover_of : LateralTheory.E.DomCoverPf.IdemCover := by
  intro C0
  haveI : Algebra.IsIntegral C0 (D C0) := integral
  refine ⟨CommRingCat.of (D C0), CommRingCat.ofHom (algebraMap C0 (D C0)), ?_, ?_, ?_⟩
  · intro x; exact Algebra.IsIntegral.isIntegral (R := C0) (x : D C0)
  · intro q hq; exact spS q hq
  · intro r _
    exact ⟨domain r, frac r⟩

end LateralTheory.E.IdemCoverPf
end
end

section

noncomputable section
open CategoryTheory Limits Cardinal

namespace LateralTheory.E.UnderFAPf

def FP (X : CommRingCat.{0}) : ObjectProperty (Under X) := fun S => S.hom.hom.FinitePresentation

def model (X : CommRingCat.{0}) (i : Σ n : ℕ, Ideal (MvPolynomial (Fin n) X)) : Under X :=
  Under.mk (CommRingCat.ofHom (algebraMap X (MvPolynomial (Fin i.1) X ⧸ i.2)))

theorem fpSmall (X : CommRingCat.{0}) : ObjectProperty.EssentiallySmall.{0} (FP X) := by
  refine ⟨⟨.ofObj (model X), inferInstance, fun S hS => ?_⟩⟩
  let _ : Algebra X S.right := S.hom.hom.toAlgebra
  have hS' : Algebra.FinitePresentation X S.right := hS
  obtain ⟨n, f, hf, -⟩ := hS'.out
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  refine ⟨_, ⟨⟨n, RingHom.ker f⟩⟩, ⟨(Under.isoMk e.toRingEquiv.toCommRingCatIso ?_).symm⟩⟩
  ext x
  exact e.commutes x

attribute [local instance] fact_isRegular_aleph0

theorem fp_le (X : CommRingCat.{0}) : FP X ≤ isCardinalPresentable (Under X) (ℵ₀ : Cardinal.{0}) := by
  intro S hS
  have h := CommRingCat.isFinitelyPresentable_under X S hS
  exact h

def FPColim : Prop := ∀ (X : CommRingCat.{0}) (S : Under X),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J), (FP X).colimitsOfShape J S

theorem UnderFA_of (hC : FPColim) : LateralTheory.E.IECompPf.UnderFA := by
  intro X
  have := fpSmall X
  have hg : (FP X).IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{0}) :=
    { le_isCardinalPresentable := fp_le X
      exists_colimitsOfShape := fun S => by
        obtain ⟨J, _, _, h⟩ := hC X S
        refine ⟨J, inferInstance, ?_, h⟩
        rw [isCardinalFiltered_aleph0_iff]; infer_instance }
  exact { toHasCardinalFilteredGenerator := hg.hasCardinalFilteredGenerator }

end LateralTheory.E.UnderFAPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.ContStepPf

def PCS (X0 : Scheme.{0}) : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ j0 : J, Nonempty (D.obj j0 ≅ X0) →
  ∀ n i : ℤ, ∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x

def PCK (X0 : Scheme.{0}) : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ j0 : J, Nonempty (D.obj j0 ≅ X0) →
  ∀ n i : ℤ, ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
    ∃ (k : J) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0

theorem PC_of {X0 : Scheme.{0}} (h1 : PCS X0) (h2 : PCK X0) : PC X0 := by
  intro q J _ _ D c hc ha hcs hqs hu j0 e n i
  exact ⟨h1 q D c hc ha hcs hqs hu j0 e n i, h2 q D c hc ha hcs hqs hu j0 e n i⟩

def StepS : Prop := Hyp → MV → ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) →
  U ⊔ V = ⊤ → PC U.toScheme → PC V.toScheme → PC (U ⊓ V).toScheme → PCS X

def StepK : Prop := Hyp → MV → ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) →
  U ⊔ V = ⊤ → PC U.toScheme → PC V.toScheme → PC (U ⊓ V).toScheme → PCK X

theorem ContStep_of (hS : StepS) (hK : StepK) : ContStep := by
  intro h hmv X U V hU hV hUV pU pV pW
  exact PC_of (hS h hmv X U V hU hV hUV pU pV pW) (hK h hmv X U V hU hV hUV pU pV pW)

end LateralTheory.E.ContStepPf
end
end
