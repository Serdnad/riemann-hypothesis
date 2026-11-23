module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.Integers
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle002
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
public import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

theorem sub_pull : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K := by
  intro p C _ R _ _ N N' _ _ M M' j K hM hG g hg
  rw [← hM] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  have hinv : g' ∈ invFun M' ⊥ := ⟨hg', fun x k hk => by rw [AddSubgroup.mem_bot.1 hk, add_zero]⟩
  have h1 : g' ∈ Algebra.adjoin R ((afFun p (invFun M' ⊥) : Submodule R (N' → C)) : Set (N' → C)) :=
    hG hinv
  change (fun x => g' (j x)) ∈
    Algebra.adjoin R ((afFun p (invFun M K) : Submodule R (N → C)) : Set (N → C))
  clear hg' hinv
  induction h1 using Algebra.adjoin_induction with
  | mem f hf =>
    refine Algebra.subset_adjoin ⟨?_, fun x y => ?_⟩
    · rw [← hM]
      exact ⟨f, hf.1.1, rfl⟩
    · have := hf.2 (j x) (j y)
      simpa only [map_add (f := _)] using this
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add f f' _ _ h h' => exact Subalgebra.add_mem _ h h'
  | mul f f' _ _ h h' => exact Subalgebra.mul_mem _ h h'

end PositivityTheory.HtPt.Rh
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ri

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

lemma mem_pInt (p : ℕ) (z : C) : z ∈ pInt (C := C) R p ↔ ∃ r : R, algebraMap R C (r * p) = z := by
  unfold GlobalTheory.CompanionTheory.Ar.GR.pInt
  rw [Submodule.mem_span_singleton]
  simp only [Algebra.smul_def, map_mul, map_natCast]

lemma alg_mem_pInt (p : ℕ) {r : R} (h : r ∈ Ideal.span {(p : R)}) :
    algebraMap R C r ∈ pInt (C := C) R p := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 h
  exact (PositivityTheory.HtPt.Ri.mem_pInt p _).2 ⟨a, rfl⟩

lemma add_zero_mem {p : ℕ} {N : Type} [AddCommGroup N] {g : N → C}
    (hg : g ∈ addFun (C := C) R p N) : g 0 ∈ pInt (C := C) R p := by
  have h := (show ∀ x y : N, g (x + y) - g x - g y ∈ GlobalTheory.CompanionTheory.Ar.GR.pInt (C := C) R p
    from hg) 0 0
  rw [add_zero, sub_self, zero_sub] at h
  simpa using Submodule.neg_mem _ h

lemma add_nsmul_mem {p : ℕ} {N : Type} [AddCommGroup N] {g : N → C}
    (hg : g ∈ addFun (C := C) R p N) (y : N) (n : ℕ) :
    g (n • y) - n * g y ∈ pInt (C := C) R p := by
  induction n with
  | zero => simpa using PositivityTheory.HtPt.Ri.add_zero_mem hg
  | succ n ih =>
    have h := (show ∀ x y : N, g (x + y) - g x - g y ∈ GlobalTheory.CompanionTheory.Ar.GR.pInt (C := C) R p
      from hg) (n • y) y
    have hsum := Submodule.add_mem _ h ih
    rw [succ_nsmul]
    convert hsum using 1
    push_cast
    ring

lemma val_add_mem (p : ℕ) [NeZero p] (a b : ZMod p) :
    (((a + b).val : R) - (a.val : R) - (b.val : R)) ∈ Ideal.span {(p : R)} := by
  rw [Ideal.mem_span_singleton']
  refine ⟨-(((a.val + b.val) / p : ℕ) : R), ?_⟩
  have h := Nat.mod_add_div (a.val + b.val) p
  have h' : (((a.val + b.val) % p : ℕ) : R) + (p : R) * (((a.val + b.val) / p : ℕ) : R)
      = (a.val : R) + b.val := by
    rw [← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, h]
  rw [ZMod.val_add]
  linear_combination -h'

end

theorem card_addChar (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N : Type)
    [AddCommGroup N] [Fintype N] : Nat.card (AddChar N C) = Fintype.card N := by
  have hne : Monoid.exponent (Multiplicative N) ≠ 0 := Monoid.exponent_ne_zero_of_finite
  haveI : NeZero (Monoid.exponent (Multiplicative N)) := ⟨hne⟩
  haveI : NeZero (Monoid.exponent (Multiplicative N) : C) := ⟨Nat.cast_ne_zero.2 hne⟩
  rw [Nat.card_congr (AddChar.toMonoidHomEquiv.trans MonoidHom.toHomUnitsMulEquiv.toEquiv),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_congr Multiplicative.toAdd,
    Nat.card_eq_fintype_card]

end PositivityTheory.HtPt.Ri
end
end

section

noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem valAt_comp_top {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (x ≫ f) ⊤ le_top s = valAt x ⊤ le_top (f.appTop.hom s) := by
  unfold valAt
  congr 1

theorem tors_ext {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T} {S : Scheme.{0}}
    {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}} {v v' : Y ⟶ Γ.G.left} (h1 : v ≫ Γ.G.hom = v' ≫ Γ.G.hom)
    (h2 : v ≫ i = v' ≫ i) : v = v' :=
  congrArg (·.left) (h.inj (Over.mk (v ≫ Γ.G.hom)) (Over.homMk v rfl) (Over.homMk v' h1.symm) h2)

theorem ht_add : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ χ' : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N χ' w' → Γ.IsHT i M N (χ * χ') (w + w') := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M χ χ' w w' ⟨s, hs, hv⟩ ⟨s', hs', hv'⟩
  have hm : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left),
      valAt y ⊤ le_top (s * s') = valAt y ⊤ le_top s * valAt y ⊤ le_top s' := fun y => by simp [valAt]
  refine ⟨s * s', fun t => ?_, fun e => ?_⟩
  · rw [hm, hs t, hs' t, ← map_mul]; rfl
  · obtain ⟨v, h1, h2, h3⟩ := hv e
    obtain ⟨v', h1', h2', h3'⟩ := hv' e
    obtain rfl : v = v' := tors_ext h (h1.trans h1'.symm) (h2.trans h2'.symm)
    refine ⟨v, h1, h2, ?_⟩
    rw [hm, h3, h3']
    ext <;> simp [add_comm]

theorem ht_olin : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (α : T →* T) (A : L →ₗ[R] L), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → M.IsDiffOf a A → ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N (χ.comp α) (w ∘ₗ A) := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M a _ α A hα hA χ w ⟨s, hs, hv⟩
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, Category.id_comp _⟩
  have hga : (g ≫ a) ^ N = 1 := by
    have : ∀ n : ℕ, (g ≫ a) ^ n = (g ^ n) ≫ a := fun n => by
      induction n with
      | zero => simp [MonObj.one_comp]
      | succ n ih => rw [pow_succ, pow_succ, ih, MonObj.mul_comp]
    rw [this, hg, MonObj.one_comp]
  obtain ⟨a', ha'⟩ := (h.kernel Γ.G (g ≫ a)).1 hga
  replace ha' : a'.left ≫ i = i ≫ a.left := ha'
  refine ⟨a'.left.appTop.hom s, fun t => ?_, fun e => ?_⟩
  · have : (Γ.pt t).left ≫ a'.left = (Γ.pt (α t)).left :=
      tors_ext h (by rw [Category.assoc, Over.w, Over.w, Over.w]) (by rw [Category.assoc, ha', hα])
    rw [← valAt_comp_top, this]
    exact hs (α t)
  · obtain ⟨v, ⟨h1, h2⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i h L M e
    obtain ⟨v', h1', h2', h3'⟩ := hv (A e)
    have : v ≫ a'.left = v' := tors_ext h (by rw [Category.assoc, Over.w, h1, h1']) (by
      rw [Category.assoc, ha', ← Category.assoc, h2, h2', hA e, Over.comp_left, Category.assoc])
    exact ⟨v, h1, h2, by rw [← valAt_comp_top, this, h3']; rfl⟩

end PositivityTheory.HtPt.Htat
end
end

section

noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
open scoped nonZeroDivisors

theorem isFractionRing_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsFractionRing O C := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : FaithfulSMul O C := (faithfulSMul_iff_algebraMap_injective O C).2 hv.hom_inj
  refine IsFractionRing.of_field O C fun z => ?_
  obtain ⟨a, h | h⟩ := hv.eq_algebraMap_or_inv_eq_algebraMap z
  · exact ⟨a, 1, by simp [h]⟩
  · exact ⟨1, a, by simp [← h]⟩

theorem finrank_lattice {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (M : Submodule A Ω) (hM : M.IsFullLattice K) : finrank A M = finrank K Ω := by
  haveI : IsLocalizedModule A⁰ M.subtype :=
    { map_units := fun s => by
        rw [← (Algebra.lsmul A (A := K) A Ω).commutes]
        exact (IsLocalization.map_units K s).map _
      surj := fun y => by
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span A⁰ K (M : Set Ω) y
          (by rw [hM.span_eq_top]; trivial)
        rw [Submodule.span_eq] at ht
        exact ⟨⟨⟨_, ht⟩, t⟩, rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.val_injective h]⟩ }
  rw [← IsLocalizedModule.finrank_eq A⁰ M.subtype le_rfl]
  exact (IsLocalization.finrank_eq K A⁰ le_rfl).symm

theorem rankAtStalk_eq_finrank {A : Type} [CommRing A] [IsDomain A] (M : Type) [AddCommGroup M]
    [Module A M] (p : PrimeSpectrum A) : rankAtStalk M p = finrank A M := by
  have hp : p.asIdeal.primeCompl ≤ A⁰ := p.asIdeal.primeCompl_le_nonZeroDivisors
  rw [rankAtStalk, IsLocalization.finrank_eq _ p.asIdeal.primeCompl hp,
    IsLocalizedModule.finrank_eq p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) hp]

theorem finrank_baseChange_flat {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O]
    [Algebra A O] (M : Type) [AddCommGroup M] [Module A M] [Module.Flat A M] [Module.Finite A M] :
    finrank O (O ⊗[A] M) = finrank A M := by
  rw [← rankAtStalk_eq_finrank (O ⊗[A] M) (⊥ : PrimeSpectrum O), rankAtStalk_baseChange,
    rankAtStalk_eq_finrank]

theorem exists_lift {A O : Type} [CommRing A] [CommRing O] [Algebra A O] {M : Type} [AddCommGroup M]
    [Module A M] {Ω' : Type} [AddCommGroup Ω'] [Module O Ω'] (ι : M →ₛₗ[algebraMap A O] Ω') :
    ∃ j : O ⊗[A] M →ₗ[O] Ω', (∀ x, j (1 ⊗ₜ x) = ι x) ∧
      LinearMap.range j = Submodule.span O (Set.range ι) := by
  letI : Module A Ω' := Module.compHom Ω' (algebraMap A O)
  haveI : IsScalarTower A O Ω' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f : M →ₗ[A] Ω' :=
    { toFun := ι, map_add' := map_add ι, map_smul' := fun a x => ι.map_smulₛₗ a x }
  refine ⟨f.liftBaseChange O, fun x => by simp [f], ?_⟩
  rw [LinearMap.range_liftBaseChange]
  rfl

theorem bc_iso : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (L : Submodule O Ω') (ι : M →ₛₗ[algebraMap A O] Ω'), M.IsFullLattice K → Module.Projective A M → L.IsFullLattice C → Submodule.span O (Set.range ι) = L → Module.finrank K Ω = Module.finrank C Ω' → ∃ j : O ⊗[A] M →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = L ∧ ∀ x, j (1 ⊗ₜ x) = ι x := by
  intro A K _ _ _ _ _ Ω _ _ _ _ M C _ v O _ _ hv _ Ω' _ _ _ _ L ι hM hP hL hspan hrk
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := isFractionRing_of_integers hv
  haveI : Module.Finite A M := Module.Finite.iff_fg.2 hM.fg
  obtain ⟨j, hj, hr⟩ := exists_lift ι
  rw [hspan] at hr
  refine ⟨j, ?_, hr, hj⟩
  have h1 : finrank O (O ⊗[A] M) = finrank O (LinearMap.range j) := by
    rw [finrank_baseChange_flat, finrank_lattice M hM, hr, finrank_lattice L hL, hrk]
  have h2 := j.rank_range_add_rank_ker
  haveI : Module.Finite O (LinearMap.range j) := inferInstance
  rw [← finrank_eq_rank O (O ⊗[A] M), ← finrank_eq_rank O (LinearMap.range j), h1] at h2
  have h3 : Module.rank O (LinearMap.ker j) = 0 := by
    rw [add_comm] at h2
    exact (Cardinal.add_nat_inj _).1 (h2.trans (zero_add _).symm)
  rw [← LinearMap.ker_eq_bot]
  exact (Submodule.rank_eq_zero).1 h3

end PositivityTheory.HtPt.Gb
end
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

private theorem isTorsionFree_of_projective {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    [Module.Projective A P] : Module.IsTorsionFree A P := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective A P›
  have hinj : Function.Injective s :=
    Function.LeftInverse.injective (g := Finsupp.linearCombination A id)
      (fun x => LinearMap.congr_fun hs x)
  refine ⟨fun r hr p p' h => hinj ?_⟩
  have h' : r • s p = r • s p' := by
    rw [← map_smul, ← map_smul]
    exact congrArg s h
  ext x
  have hx := congrArg (fun g => g x) h'
  simp only [Finsupp.smul_apply, smul_eq_mul] at hx
  exact hr.left hx

theorem inj_mod_of_surj_mod {A : Type} [CommRing A] [IsDomain A] {P : Type} [AddCommGroup P]
    [Module A P] [Module.Finite A P] [Module.IsTorsionFree A P] {N : ℕ} (a : A)
    (φ : (Fin N → A) →ₗ[A] P) (hN : (N : Cardinal) ≤ Module.rank A P)
    (hs : ∀ y, ∃ x y', y = φ x + a • y') (x : Fin N → A) (y : P) (hx : φ x = a • y) :
    ∃ x', x = a • x' := by
  haveI : Module.IsTorsionFree A (Fin N → A) := isTorsionFree_of_projective
  obtain ⟨r, hr1, hrP⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := Ideal.span {a}) (N := LinearMap.range φ) (Module.Finite.fg_top (R := A) (M := P)) le_rfl
    (by
      intro z _
      obtain ⟨x₀, z', rfl⟩ := hs z
      exact Submodule.add_mem_sup (LinearMap.mem_range_self φ x₀)
        (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) Submodule.mem_top))
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr1
  by_cases hr : r = 0
  · refine ⟨-(c • x), ?_⟩
    rw [smul_neg, smul_smul, mul_comm, hc, hr]
    simp
  have hrange : ∀ p : P, r • p ∈ LinearMap.range φ := fun p =>
    hrP (Submodule.smul_mem_pointwise_smul p r ⊤ Submodule.mem_top)
  let f : P →ₗ[A] LinearMap.range φ :=
    LinearMap.codRestrict (LinearMap.range φ) (r • LinearMap.id) (fun p => hrange p)
  have hf : Function.Injective f := by
    intro p p' h
    have h' : r • p = r • p' := congrArg Subtype.val h
    exact smul_right_injective P hr h'
  have hrk : (N : Cardinal) ≤ Module.rank A (LinearMap.range φ) :=
    hN.trans (LinearMap.rank_le_of_injective f hf)
  have hsum := LinearMap.rank_range_add_rank_ker φ
  rw [rank_fin_fun] at hsum
  have hker : Module.rank A (LinearMap.ker φ) = 0 := by
    have hle : Module.rank A (LinearMap.range φ) ≤ N := by
      rw [← hsum]
      exact le_self_add
    rw [le_antisymm hle hrk, add_comm] at hsum
    exact (Cardinal.add_right_inj_of_lt_aleph0 Cardinal.natCast_lt_aleph0).mp (by rw [hsum, zero_add])
  have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp (Submodule.rank_eq_zero.mp hker)
  obtain ⟨z, hz⟩ := hrange y
  have hxz : r • x = a • z :=
    hinj (by rw [map_smul, map_smul, hx, hz, smul_smul, smul_smul, mul_comm])
  refine ⟨z - c • x, ?_⟩
  rw [smul_sub, ← hxz, smul_smul, ← sub_smul, mul_comm a c, hc]
  simp

theorem split_exact : ∀ (A : Type) [CommRing A] [IsDomain A] (P₁ P₂ : Type) [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁] [AddCommGroup P₂] [Module A P₂] [Module.Finite A P₂] [Module.Projective A P₂] (N : ℕ) (a : A) (i : P₁ →ₗ[A] (Fin N → A)) (r : (Fin N → A) →ₗ[A] P₁) (q : (Fin N → A) →ₗ[A] P₂), Module.finrank A P₁ + Module.finrank A P₂ = N → (∀ w, ∃ w', r (i w) = w + a • w') → (∀ y, ∃ x y', y = q x + a • y') → (∀ w, ∃ y, q (i w) = a • y) → ∀ x, (∃ y, q x = a • y) → ∃ w x', x = i w + a • x' := by
  intro A _ _ P₁ P₂ _ _ _ _ _ _ _ _ N a i r q hrank hri hq hqi x hx
  haveI : Module.IsTorsionFree A (P₁ × P₂) := isTorsionFree_of_projective
  have hN : (N : Cardinal) ≤ Module.rank A (P₁ × P₂) := by
    rw [← hrank, Nat.cast_add, Module.finrank_eq_rank, Module.finrank_eq_rank]
    exact rank_add_rank_le_rank_prod A P₁
  have hs : ∀ y : P₁ × P₂, ∃ x y', y = (r.prod q) x + a • y' := by
    rintro ⟨w, y⟩
    obtain ⟨x₀, y₀, rfl⟩ := hq y
    obtain ⟨w', hw'⟩ := hri (w - r x₀)
    obtain ⟨y'', hy''⟩ := hqi (w - r x₀)
    refine ⟨x₀ + i (w - r x₀), (-w', y₀ - y''), Prod.ext ?_ ?_⟩
    · show w = r (x₀ + i (w - r x₀)) + a • -w'
      rw [map_add (f := _), hw', smul_neg]
      abel
    · show q x₀ + a • y₀ = q (x₀ + i (w - r x₀)) + a • (y₀ - y'')
      rw [map_add (f := _), hy'', smul_sub]
      abel
  obtain ⟨w', hw'⟩ := hri (r x)
  obtain ⟨y'', hy''⟩ := hqi (r x)
  obtain ⟨y, hy⟩ := hx
  have hφ : (r.prod q) (x - i (r x)) = a • (-w', y - y'') := by
    refine Prod.ext ?_ ?_
    · show r (x - i (r x)) = a • -w'
      rw [map_sub, hw', smul_neg]
      abel
    · show q (x - i (r x)) = a • (y - y'')
      rw [map_sub, hy, hy'', smul_sub]
  obtain ⟨x', hx'⟩ := PositivityTheory.HtPt.Gd.inj_mod_of_surj_mod a (r.prod q) hN hs _ _ hφ
  refine ⟨r x, x', ?_⟩
  rw [← hx']
  abel

end PositivityTheory.HtPt.Gd
end
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

theorem test_descend : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (𝔮 : Ideal A) (M : Type) [AddCommGroup M] [Module A M] (L : Submodule A M) (x : M), 𝔮.IsPrime → 𝔮.height = 1 → Function.Injective (algebraMap A O) → (∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (algebraMap A O a)) < 1) → (1 : O) ⊗ₜ[A] x ∈ Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ L := by
  intro A K _ _ _ _ _ _ _ C _ v O _ _ hv _ q M _ _ L x hq h1 hinj hcen hx
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers _ hv
  haveI := dvr_of_height_one q h1
  have hu : ∀ s : q.primeCompl, IsUnit (algebraMap A O s) := fun s => by
    rw [hv.isUnit_iff_valuation_eq_one]
    exact le_antisymm (hv.map_le_one _) (not_lt.1 fun h => s.2 ((hcen s).2 h))
  let R := Localization.AtPrime q
  letI : Algebra R O := (IsLocalization.lift (M := q.primeCompl) hu).toAlgebra
  have hcomp : ∀ a : A, algebraMap R O (algebraMap A R a) = algebraMap A O a := fun a =>
    IsLocalization.lift_eq hu a
  haveI : IsScalarTower A R O := IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  have hinjR : Function.Injective (algebraMap R O) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    have h2 : algebraMap A O a = 0 := by
      rw [← hcomp, ← IsLocalization.mk'_spec R a s, map_mul]
      simp only at hr
      rw [hr, zero_mul]
    have : a = 0 := hinj (by simpa using h2)
    simp [this]
  haveI : IsLocalHom (algebraMap R O) := ⟨fun r hr => by
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    simp only at hr ⊢
    rw [IsLocalization.AtPrime.isUnit_mk'_iff R q]
    have h2 : IsUnit (algebraMap A O a) := by
      rw [← hcomp, ← IsLocalization.mk'_spec R a s, map_mul, hcomp]
      exact hr.mul (hu s)
    rw [hv.isUnit_iff_valuation_eq_one] at h2
    intro ha
    exact ((hcen a).1 ha).ne h2⟩
  haveI : FaithfulSMul R O := (faithfulSMul_iff_algebraMap_injective R O).2 hinjR
  haveI : Module.Flat R O := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  haveI : Module.FaithfullyFlat R O := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have h0 : (1 : O) ⊗ₜ[A] (L.mkQ x) = 0 := by
    have : Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) ≤
        LinearMap.ker (L.mkQ.baseChange O) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      simp [(Submodule.Quotient.mk_eq_zero L).2 hy]
    simpa using this hx
  have h2 : (1 : O) ⊗ₜ[R] ((1 : R) ⊗ₜ[A] (L.mkQ x)) = 0 := by
    apply (AlgebraTensorModule.cancelBaseChange A R O O (M ⧸ L)).injective
    simpa using h0
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h2
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff q.primeCompl
    (TensorProduct.mk A R (M ⧸ L) 1)).1 h2
  refine ⟨s, s.2, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
  exact hs

end PositivityTheory.HtPt.Gc
end
