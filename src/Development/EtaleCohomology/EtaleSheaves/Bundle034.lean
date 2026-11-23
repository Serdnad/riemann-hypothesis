module

public import Development.EtaleCohomology.EtaleSheaves.Bundle018
public import Development.EtaleCohomology.EtaleSheaves.Bundle020
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.EmptyVan₂

theorem sec_subsingleton {R : Type} [CommRing R] (G : Shv R) (X : Scheme.{0}) [IsEmpty X] :
    Subsingleton (G.obj.obj (op X)) := by
  have h := Sheaf.isTerminalOfBotCover G X (Scheme.bot_mem_grothendieckTopology X)
  constructor
  intro a b
  have e := h.hom_ext (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ a))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ b))
  have := congrArg (fun f => f.hom (1 : ULift.{1} R)) e
  simpa using this

theorem free_isZero {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] :
    IsZero ((free R).obj (yoneda.obj X)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).injective
  ext U x
  rcases isEmpty_or_nonempty U.unop with hU | hU
  · have := sec_subsingleton (R := R) ((free R).obj (yoneda.obj X)) U.unop
    exact @Subsingleton.elim _ this _ _
  · have : IsEmpty ((yoneda.obj X).obj U) := ⟨fun (f : U.unop ⟶ X) => IsEmpty.false (f.base (Classical.arbitrary U.unop))⟩
    have hx : x = 0 := Subsingleton.elim (α := ULift.{1} ((yoneda.obj X).obj U) →₀ ULift.{1} R) x 0
    rw [hx, map_zero, map_zero]

theorem chains_X_isZero {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (m : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X m) := by
  rcases le_or_gt m 0 with h | h
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, m = -(p : ℤ) := ⟨(-m).toNat, by omega⟩
    exact (free_isZero (R := R) X).of_iso (chainsXIso R _ p)
  · exact HomologicalComplex.isZero_extend_X _ _ m (fun i => by
      change -(i : ℤ) ≠ m; omega)

theorem cc_subsingleton {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ}
    (hK : ∀ m, IsZero (K.X m)) (n : ℤ) : Subsingleton (CohomologyClass K L n) := by
  have : Subsingleton (Cochain K L n) :=
    ⟨fun a b => Cochain.ext _ _ fun p q hpq => (hK p).eq_of_src _ _⟩
  have : Subsingleton (Cocycle K L n) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  constructor
  intro a b
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [Subsingleton.elim a b]

theorem EmptyVan_of : LateralTheory.E.CoverPf.EmptyVan := by
  intro _ q _ i n S _ hS x
  have : IsEmpty (Spec (CommRingCat.of S)) :=
    ⟨fun p => (p : PrimeSpectrum S).isPrime.ne_top (Subsingleton.elim _ _)⟩
  have := cc_subsingleton (L := res (ZMod q) (tw q i)) (chains_X_isZero (R := ZMod q) (Spec (CommRingCat.of S))) (n + 1)
  exact Subsingleton.elim _ _

end LateralTheory.E.EmptyVan₂
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafConsPfA
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut

theorem HK_pull_mk (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) (z : Cocycle L (res R F) n) :
    HK.pull R f F n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom f) z (zero_add n)) := rfl

theorem HK_pull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (y : HK R M F n) : HK.pull R (f ≫ g) F n y = HK.pull R f F n (HK.pull R g F n y) := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective y
  rw [HK_pull_mk, HK_pull_mk, HK_pull_mk]
  congr 1
  apply Cocycle.ext
  simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem HK_pull_id (R : Type) [CommRing R] {K : Cx R} (F : Shv R) (n : ℤ)
    (y : HK R K F n) : HK.pull R (𝟙 K) F n y = y := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective y
  rw [HK_pull_mk]
  congr 1
  apply Cocycle.ext
  simp [zcomp]

theorem map_congr {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂} (ha : a = a') (hb : b = b')
    (c : φ₁ ≫ b = a ≫ φ₂) (c' : φ₁ ≫ b' = a' ≫ φ₂) :
    mappingCone.map φ₁ φ₂ a b c = mappingCone.map φ₁ φ₂ a' b' c' := by
  subst ha hb; rfl

theorem rmap_congr (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') {u u2 : U' ⟶ U} {e e2 : E' ⟶ E}
    (hu : u = u2) (he : e = e2) (c : f' ≫ e = u ≫ f) (c2 : f' ≫ e2 = u2 ≫ f) :
    rmap R f f' u e c = rmap R f f' u2 e2 c2 := by
  subst hu he; rfl

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f')
    (c'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f f'' (u' ≫ u) (e' ≫ e) c'' = rmap R f' f'' u' e' c' ≫ rmap R f f' u e c := by
  unfold rmap
  exact (map_congr _ _ ((chains R).map_comp _ _) ((chains R).map_comp _ _) _ _).trans
    (mappingCone.map_comp _ _ _ _ _ _ _ _ _)

theorem rmap_id (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (c : f ≫ 𝟙 E = 𝟙 U ≫ f) :
    rmap R f f (𝟙 U) (𝟙 E) c = 𝟙 _ := by
  unfold rmap
  exact (map_congr _ _ ((chains R).map_id _) ((chains R).map_id _) _ _).trans (mappingCone.map_id _)

theorem rpl_comp (q : ℕ) (i : ℤ) {U E U' E' U'' E'' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f')
    (c'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (n : ℤ) (y) :
    rpl q i f f'' (u' ≫ u) (e' ≫ e) c'' n y = rpl q i f' f'' u' e' c' n (rpl q i f f' u e c n y) := by
  simp only [rpl, rpull]
  rw [← HK_pull_comp, ← rmap_comp _ _ _ _ _ _ _ _ _ _ (by simp only [← Functor.map_comp, c'', Category.assoc])]
  congr 1

theorem rpl_id (q : ℕ) (i : ℤ) {U E : Scheme.{0}} (f : U ⟶ E) (c : f ≫ 𝟙 E = 𝟙 U ≫ f) (n : ℤ) (y) :
    rpl q i f f (𝟙 U) (𝟙 E) c n y = y := by
  simp only [rpl, rpull]
  rw [rmap_congr _ _ _ (sch.map_id _) (sch.map_id _) _ (by simp), rmap_id, HK_pull_id]

theorem rpl_bij (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (c : f' ≫ e = u ≫ f) [IsIso u] [IsIso e] (n : ℤ) : Function.Bijective (rpl q i f f' u e c n) := by
  have c2 : f ≫ inv e = inv u ≫ f' := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← c, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine Function.bijective_iff_has_inverse.2 ⟨rpl q i f' f (inv u) (inv e) c2 n, fun y => ?_, fun y => ?_⟩
  · rw [← rpl_comp q i f f' f u e (inv u) (inv e) c c2 (by simp), ]
    simp only [IsIso.inv_hom_id]
    exact rpl_id q i f _ n y
  · rw [← rpl_comp q i f' f f' (inv u) (inv e) u e c2 c (by simp)]
    simp only [IsIso.hom_inv_id]
    exact rpl_id q i f' _ n y

end LateralTheory.E.LeafConsPfA
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.TwFBijPf

theorem aeval_res {C : Type} [CommRing C] [IsLocalRing C] (q : ℕ) (x : C) :
    aeval (residue C x) (cyclotomic q ℤ) = residue C (aeval x (cyclotomic q ℤ)) :=
  by
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂]; congr 1

theorem isRoot_iff {K : Type} [CommRing K] (q : ℕ) (x : K) :
    IsRoot (cyclotomic q K) x ↔ aeval x (cyclotomic q ℤ) = 0 := by
  rw [← map_cyclotomic_int, IsRoot, Polynomial.eval_map, aeval_def, algebraMap_int_eq]

theorem res_prim {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {ζ : C}
    (h : aeval ζ (cyclotomic q ℤ) = 0) : IsPrimitiveRoot (residue C ζ) q := by
  haveI : NeZero ((q : ℕ) : ResidueField C) := ⟨by
    have := hq.map (residue C); rw [map_natCast] at this; exact this.ne_zero⟩
  rw [← isRoot_cyclotomic_iff, isRoot_iff]
  exact (aeval_res q ζ).trans (by rw [h, map_zero])

theorem pow_q {C : Type} [CommRing C] {q : ℕ} {ζ : C} (h : aeval ζ (cyclotomic q ℤ) = 0) : ζ ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ζ) hg
  simp [h] at this
  exact sub_eq_zero.1 this

theorem prim {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {ζ : C}
    (h : aeval ζ (cyclotomic q ℤ) = 0) : IsPrimitiveRoot ζ q := by
  refine ⟨pow_q h, fun l hl => (res_prim hq h).dvd_of_pow_eq_one l ?_⟩
  rw [← map_pow, hl, map_one]

theorem uniq {C : Type} [CommRing C] [IsLocalRing C] {n : ℕ} (hn : IsUnit (n : C)) {x y : C} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (hr : residue C x = residue C y) : x = y := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have key := (Commute.all x y).geom_sum₂_mul n
  rw [hx, hy, sub_self] at key
  have hS : IsUnit (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) := by

    rw [← residue_ne_zero_iff_isUnit, map_sum]
    have : ∀ i ∈ Finset.range n, residue C (x ^ i * y ^ (n - 1 - i)) = residue C x ^ (n - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, ← hr, ← pow_add]
      congr 1
      have := Finset.mem_range.1 hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 : IsUnit (residue C (n : C)) := hn.map _
    have h2 : IsUnit (residue C x) := (show IsUnit x from ⟨⟨x, x ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), hx],
      by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), hx]⟩, rfl⟩).map _
    rw [map_natCast] at h1
    exact (h1.mul (h2.pow _)).ne_zero
  have := hS.mul_right_eq_zero.1 key
  exact sub_eq_zero.1 this

theorem pow_rep {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {η ξ : C}
    (hη : aeval η (cyclotomic q ℤ) = 0) (hξ : aeval ξ (cyclotomic q ℤ) = 0) :
    ∃ a : (ZMod q)ˣ, ξ = η ^ (a : ZMod q).val := by
  obtain ⟨i, hi, he⟩ := (res_prim hq hη).eq_pow_of_pow_eq_one (ξ := residue C ξ) (by rw [← map_pow, pow_q hξ, map_one])
  have hηi : η ^ i = ξ := uniq hq (by rw [← pow_mul, mul_comm, pow_mul, pow_q hη, one_pow]) (pow_q hξ) (by rw [map_pow, he])
  have hc : i.Coprime q := ((prim hq hη).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hηi ▸ prim hq hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hηi]

theorem pow_inj {C : Type} [CommRing C] {q : ℕ} [NeZero q] {η : C} (hη : IsPrimitiveRoot η q) {a b : (ZMod q)ˣ}
    (h : η ^ (a : ZMod q).val = η ^ (b : ZMod q).val) : a = b :=
  Units.ext (ZMod.val_injective q (hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))

theorem exists_root {A : Type} [CommRing A] {q : ℕ} [NeZero q] (hq : IsUnit (q : A)) (hA : SH A) :
    ∃ ζ : A, aeval ζ (cyclotomic q ℤ) = 0 := by
  obtain ⟨hH, hS⟩ := hA
  haveI : NeZero ((q : ℕ) : ResidueField A) := ⟨by
    have := hq.map (residue A); rw [map_natCast] at this; exact this.ne_zero⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root (cyclotomic q (ResidueField A))
    (ne_of_gt (degree_cyclotomic_pos q _ (Nat.pos_of_ne_zero (NeZero.ne q)))) (separable_cyclotomic q _)
  obtain ⟨a0, rfl⟩ := residue_surjective x
  have hd : IsUnit ((cyclotomic q A).derivative.eval a0) := by
    rw [← residue_ne_zero_iff_isUnit]
    have := (separable_cyclotomic q (ResidueField A)).aeval_derivative_ne_zero (x := residue A a0) (by
      rw [aeval_def, Algebra.algebraMap_self, eval₂_id]; exact hx)
    rw [aeval_def, Algebra.algebraMap_self, eval₂_id, ← map_cyclotomic q (residue A), derivative_map,
      Polynomial.eval_map, Polynomial.eval₂_hom] at this
    exact this
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (cyclotomic q A) (cyclotomic.monic q A) a0 (by
    rw [← residue_eq_zero_iff, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, map_cyclotomic]; exact hx) hd
  exact ⟨a, (isRoot_iff q a).1 ha⟩

section Gen
variable {q : ℕ} [NeZero q] (i : ℤ) {C : Type} [CommRing C] [IsLocalRing C]

theorem pmod {η : C} (hη : IsPrimitiveRoot η q) (n : ℕ) : η ^ (n % q) = η ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]

def ex (η ξ : Prim q C) : (ZMod q)ˣ := Classical.choose (pow_rep η.2.1 η.2.2 ξ.2.2)

theorem ex_spec (η ξ : Prim q C) : ξ.1 = η.1 ^ (ex η ξ : ZMod q).val := Classical.choose_spec (pow_rep η.2.1 η.2.2 ξ.2.2)

theorem ex_pow (η ξ ζ : Prim q C) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : ex η ξ = ex η ζ * a := by
  have hη := prim η.2.1 η.2.2
  apply pow_inj hη
  rw [← ex_spec, h, ex_spec η ζ, ← pow_mul, Units.val_mul, ZMod.val_mul, pmod hη]

theorem ex_self (η : Prim q C) : ex η η = 1 := by
  have hη := prim η.2.1 η.2.2
  apply pow_inj hη
  rw [← ex_spec, Units.val_one, ZMod.val_one_eq_one_mod, pmod hη, pow_one]

def psi (η : Prim q C) : (Prim q C →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (fun ξ => ULift.up (((ex η ξ ^ i : (ZMod q)ˣ) : ZMod q)))

theorem rel_le (η : Prim q C) : twRel q i C ≤ LinearMap.ker (psi i η) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, psi, Finsupp.linearCombination_single, ex_pow η ξ ζ a h,
    mul_zpow, Units.val_mul]
  apply ULift.ext
  simp [mul_comm]

def Psi (η : Prim q C) : ((Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  (twRel q i C).liftQ (psi i η) (rel_le i η)

def gen (η : Prim q C) : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C := Submodule.Quotient.mk (Finsupp.single η 1)

theorem Psi_gen (η : Prim q C) : Psi i η (gen i η) = 1 := by
  simp [Psi, gen, psi, Finsupp.linearCombination_single, ex_self]
  rfl

theorem decomp (η : Prim q C) (z : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) : z = Psi i η z • gen i η := by
  induction z using Submodule.Quotient.induction_on with
  | H x =>
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Submodule.Quotient.mk_add, map_add (f := _), add_smul, ← hx, ← hy]
  | single ξ c =>
    have hrel : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single η (ULift.up (((ex η η * ex η ξ) ^ i : (ZMod q)ˣ) : ZMod q))
        ∈ twRel q i C := by
      refine Submodule.subset_span ⟨η, ξ, ex η ξ, ex_spec η ξ, ?_⟩
      rw [ex_self, one_mul]
    rw [ex_self, one_mul] at hrel
    have h1 : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) =
        ULift.up (((ex η ξ ^ i : (ZMod q)ˣ) : ZMod q)) • gen i η := by
      rw [gen, ← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
      exact (Submodule.Quotient.eq _).2 hrel
    have h2 : (Finsupp.single ξ c : Prim q C →₀ ULift.{1} (ZMod q)) = c • Finsupp.single ξ 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h2, Submodule.Quotient.mk_smul, h1, smul_smul]
    congr 1
    rw [map_smul, Psi_gen, smul_eq_mul, mul_one]

end Gen

theorem bij_ty {q : ℕ} [NeZero q] (i : ℤ) {X Y : Type} [CommRing X] [CommRing Y] [IsLocalRing X] [IsLocalRing Y]
    (g : X →+* Y) (ζ : Prim q X) :
    Function.Bijective (Submodule.mapQ (twRel q i X) (twRel q i Y) (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
      (Prim.map g)) (twRel_le q i g)) := by
  set F := Submodule.mapQ (twRel q i X) (twRel q i Y) (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
      (Prim.map g)) (twRel_le q i g)
  have hF : ∀ z, F z = Psi i ζ z • gen i (Prim.map g ζ) := by
    intro z
    conv_lhs => rw [decomp i ζ z]
    rw [map_smul]
    congr 1
    simp only [F, gen, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  have hP : ∀ z, Psi i (Prim.map g ζ) (F z) = Psi i ζ z := by
    intro z
    rw [hF, map_smul, Psi_gen, smul_eq_mul, mul_one]
  refine ⟨fun z1 z2 h => ?_, fun w => ⟨Psi i (Prim.map g ζ) w • gen i ζ, ?_⟩⟩
  · rw [decomp i ζ z1, decomp i ζ z2, ← hP z1, ← hP z2, h]
  · rw [hF, map_smul, Psi_gen, smul_eq_mul, mul_one]
    exact (decomp i _ w).symm

theorem bij_gen {q : ℕ} [NeZero q] (i : ℤ) {X Y : CommRingCat.{0}} [IsLocalRing X] [IsLocalRing Y] (g : X ⟶ Y)
    (ζ : Prim q X) : Function.Bijective ((twF q i).map g).hom :=
  bij_ty i g.hom ζ

theorem TwFBij_of : LateralTheory.E.SHEqvPf.TwFBij := by
  intro q _ i A B f hq hA hB
  obtain ⟨hHA, hSA⟩ := hA
  obtain ⟨hHB, -⟩ := hB
  have hloc : ∀ (R : CommRingCat.{0}), IsLocalRing R → IsLocalRing Γ(Spec R, ⊤) := by
    intro R _
    let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
    haveI : Nontrivial Γ(Spec R, ⊤) := e.toEquiv.nontrivial
    exact IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  haveI := hloc A inferInstance
  haveI := hloc B inferInstance
  obtain ⟨ζ, hζ⟩ := exists_root hq ⟨hHA, hSA⟩
  exact bij_gen i _ (Prim.map (Scheme.ΓSpecIso A).inv.hom ⟨ζ, hq, hζ⟩)

end LateralTheory.E.TwFBijPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitActPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafUnitPairGPf

def LeafActSheaf : Prop := ∀ (q : ℕ) [NeZero q], ∃ L : ∀ (F : Shv (ZMod q)) (U : Scheme.{0}),
    Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)] Sec F U →ₗ[ULift.{1} (ZMod q)] Sec F U,
  (∀ (F : Shv (ZMod q)) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec (tw q 0) U) (b : Sec F U),
      Sec.res g (L F U a b) = L F V (Sec.res g a) (Sec.res g b)) ∧
  (∀ {F G : Shv (ZMod q)} (φ : F ⟶ G) (U : Scheme.{0}) (a : Sec (tw q 0) U) (b : Sec F U),
      Sec.map φ (L F U a b) = L G U a (Sec.map φ b)) ∧
  ∀ (F : Shv (ZMod q)) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (b : Sec F U), L F U (twGen 0 ζ) b = b

theorem LeafUnitAct_of (h : LeafActSheaf) : LeafUnitAct := by
  intro q _ i
  obtain ⟨L, hU, hF, hζ⟩ := h q
  refine ⟨fun U t => L ((res _ (tw q i)).X t) U, ⟨fun g t a b => hU _ g a b, fun U t a b => hF _ U a b⟩,
    fun U t ζ b => hζ _ U ζ b⟩

end LateralTheory.E.LeafUnitActPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafPairExtPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafUnitPairGPf

def LeafActSgl : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) L, IsAct q i L →
  ∃ lam : Pair (sgl (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      lam.mul U 0 t t (zero_add t) (Sec.map (sglι (tw q 0)) a) b = L U t a b

def LeafExtAlongAug : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (lam : Pair (sgl (tw q 0)) (res _ (tw q i)) (res _ (tw q i))),
  ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (x : Sec ((sgl (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      ν.mul U 0 t t (zero_add t) (Sec.map ((resAug (tw q 0)).f 0) x) b = lam.mul U 0 t t (zero_add t) x b

section Act
variable {q : ℕ} {i : ℤ}

def actPair (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) : Sec ((sgl (tw q 0)).X s) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)]
      Sec ((res _ (tw q i)).X w) U :=
  if hs : s = 0 then
    ((L U t).compl₁₂ (((HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (tw q 0) s hs).hom.hom.app (op U)).hom)
      LinearMap.id).compr₂ ((((res _ (tw q i)).XIsoOfEq (show t = w by omega)).hom.hom.app (op U)).hom)
  else 0

theorem actPair_pos (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) (U : Scheme.{0}) (t : ℤ)
    (a : Sec ((sgl (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U) :
    actPair L U 0 t t (zero_add t) a b =
      L U t (Sec.map (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (tw q 0) 0 rfl).hom a) b := by
  simp [actPair, HomologicalComplex.XIsoOfEq_rfl]

theorem actPair_neg (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) (hs : s ≠ 0) : actPair L U s t w h = 0 := by
  simp [actPair, hs]

end Act

theorem LeafPairExt_of (h1 : LeafActSgl) (h2 : LeafExtAlongAug) : LeafPairExt := by
  intro q _ i L hL
  obtain ⟨lam, hlam⟩ := h1 q i L hL
  obtain ⟨ν, hν⟩ := h2 q i lam
  refine ⟨ν, fun U t a b => ?_⟩
  have e : Sec.map (resι _ (tw q 0)) a = Sec.map ((resAug (tw q 0)).f 0) (Sec.map (sglι (tw q 0)) a) := rfl
  rw [e, hν, hlam]

theorem etale_twist_action_induces_single_complex_pairing_holds : LeafActSgl := by
  intro q _ i L hL
  refine ⟨⟨actPair L, ?_, ?_⟩, ?_⟩
  · intro V U g s t w h a b
    by_cases hs : s = 0
    · subst hs
      obtain rfl : w = t := by omega
      rw [actPair_pos, actPair_pos, hL.1]
      congr 2
    · rw [actPair_neg L U s t w h hs, actPair_neg L V s t w h hs]
      simp
  · intro U s t w h a b
    have hd : (sgl (tw q 0)).d s (s + 1) = 0 := by simp
    rw [hd]
    have h0 : Sec.map (0 : (sgl (tw q 0)).X s ⟶ (sgl (tw q 0)).X (s + 1)) a = 0 := rfl
    rw [h0, map_zero, LinearMap.zero_apply, zero_add]
    by_cases hs : s = 0
    · subst hs
      obtain rfl : w = t := by omega
      rw [actPair_pos, actPair_pos, Int.negOnePow_zero, one_smul]
      exact hL.2 U _ _ b
    · rw [actPair_neg L U s t w h hs, actPair_neg L U s (t + 1) (w + 1) (by omega) hs]
      simp
  · intro U t a b
    change actPair L U 0 t t (zero_add t) _ b = _
    rw [actPair_pos]
    congr 1

theorem LeafPairExt_of' (h2 : LeafExtAlongAug) : LeafPairExt := LeafPairExt_of etale_twist_action_induces_single_complex_pairing_holds h2

end LateralTheory.E.LeafPairExtPf
end
end
