module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfForallMem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3397
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.ES.CorrQF

theorem charP_of_residueField_of_notMem_basicOpen (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (u : X)
    (hu : u ∉ X.basicOpen ((p : ℕ) : Γ(X, ⊤))) (L : Type) [Field L] (h : X.residueField u →+* L) : CharP L p := by
  have h1 : ¬ IsUnit (X.presheaf.germ ⊤ u trivial ((p : ℕ) : Γ(X, ⊤))) :=
    fun hh => hu ((X.mem_basicOpen ((p : ℕ) : Γ(X, ⊤)) u (Set.mem_univ u)).2 hh)
  rw [map_natCast] at h1
  have h2 : IsLocalRing.residue (X.presheaf.stalk u) ((p : ℕ) : X.presheaf.stalk u) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h1)
  rw [map_natCast] at h2
  have h3 : ((p : ℕ) : L) = 0 := by
    rw [← map_natCast h]
    exact (congrArg h h2).trans (map_zero h)
  exact (CharP.charP_iff_prime_eq_zero (Fact.out)).2 h3

theorem finite_isogTarget : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (c : ℕ) (M : Model b N) (u : M.X), u ∉ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → ∀ (L : Type) [Field L] [IsAlgClosed L] (h : M.X.residueField u →+* L), {ζ : Sp L ⟶ M.X | CorrQF.IsogTarget M c (spMap h ≫ M.X.fromSpecResidueField u) ζ}.Finite := by
  intro p _ D R _ b N hN hNp hm c M u hu L _ _ h
  haveI : CharP L p := charP_of_residueField_of_notMem_basicOpen p M.X u hu L h
  set ξ := spMap h ≫ M.X.fromSpecResidueField u with hξ
  obtain ⟨o₀, ⟨m₀⟩⟩ := HTPull.exists_objMap_pull p D R b N M.X (Sp L) M.s ξ M.univ
  have hF := T.finite_kernels_pIsogenies_harrisTaylor_charP p D R b N hN hNp hm c L (ξ ≫ M.s) o₀
  let Rel : (Sp L ⟶ M.X) → ((T : Over (Sp L)) → (T ⟶ o₀.A) → Prop) → Prop := fun ζ P =>
    ∃ (o' : Obj b N (ξ ≫ M.s)) (ψ₀ : o₀.A ⟶ o'.A), IsPIsog c o₀ o' ψ₀ ∧
      (P = fun T x => x ≫ ψ₀ = 1) ∧ Nonempty (ObjMap o' M.univ ζ) ∧ ζ ≫ M.s = ξ ≫ M.s
  have hsub : ∀ P, {ζ | Rel ζ P}.Subsingleton := by
    rintro P ζ₁ ⟨o₁, ψ₁, hψ₁, rfl, ⟨n₁⟩, hs₁⟩ ζ₂ ⟨o₂, ψ₂, hψ₂, he, ⟨n₂⟩, hs₂⟩
    obtain ⟨m, -⟩ := KerDet.exists_objMap_of_ker_eq p D R b N hN hNp c (Sp L) (ξ ≫ M.s) o₀ o₁ o₂ ψ₁ ψ₂
      hψ₁ hψ₂ (fun T x => Iff.of_eq (congrFun (congrFun he T) x))
    have hn : Nonempty (ObjMap o₁ M.univ ζ₂) := by
      simpa only [Category.id_comp] using (show Nonempty (ObjMap o₁ M.univ (𝟙 (Sp L) ≫ ζ₂)) from ⟨m.comp n₂⟩)
    exact (M.rep (Sp L) (ξ ≫ M.s) o₁).unique ⟨hs₁, ⟨n₁⟩⟩ ⟨hs₂, hn⟩
  refine (hF.biUnion fun P _ => (hsub P).finite).subset ?_
  intro ζ hζ
  obtain ⟨hs, o, o', ψ, ⟨mo⟩, ⟨mo'⟩, hψ⟩ := hζ
  obtain ⟨i₀, -⟩ := IwLevel.exists_objMap_cancel (f := 𝟙 (Sp L)) (g := ξ)
    (cast (congrArg (ObjMap o₀ M.univ) (Category.id_comp ξ).symm) m₀) mo
  obtain ⟨i₁, -⟩ := IwLevel.exists_objMap_cancel (f := 𝟙 (Sp L)) (g := ζ)
    (cast (congrArg (ObjMap o' M.univ) (Category.id_comp ζ).symm) mo') mo'
  obtain ⟨ψ₀, hψ₀, -⟩ := ValExt.isPIsog_pull p D R b N c (Sp L) (Sp L) (ξ ≫ M.s) (ξ ≫ M.s) (𝟙 _)
    o o' o₀ o' i₀ i₁ ψ hψ
  exact Set.mem_biUnion (x := fun T x => x ≫ ψ₀ = 1) ⟨o', ψ₀, hψ₀, rfl⟩ ⟨o', ψ₀, hψ₀, rfl, ⟨mo'⟩, hs.symm⟩

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.TjExists

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}} {N : ℕ}

theorem charZero_of_base (b : Base D R) (hp : IsUnit ((p : ℕ) : R)) {k : Type} [Field k] (s : Sp k ⟶ Sp R) :
    CharZero k := by
  let β : R →+* k := (Spec.preimage s).hom
  haveI := ringChar.charP k
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hl | hl
  · exfalso
    have h0 : ((ringChar k : ℕ) : k) = 0 := CharP.cast_eq_zero k _
    have hu : IsUnit ((ringChar k : ℕ) : R) := by
      by_cases h : ringChar k = p
      · rw [h]; exact hp
      · exact b.unit _ ((Nat.coprime_primes hl Fact.out).2 h)
    have := hu.map β
    rw [map_natCast, h0] at this
    exact not_isUnit_zero this
  · haveI : CharP k 0 := hl ▸ ringChar.charP k
    exact CharP.charP_to_charZero k

attribute [local instance] ptModuleWvs

def torsSub {s : S ⟶ Sp R} (o : Obj b N s) (T : Over S) (c : ℕ) : Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) where
  carrier := {g | g.toMul ^ c = 1}
  zero_mem' := one_pow c
  add_mem' {g h} hg hh := by
    show (g.toMul * h.toMul) ^ c = 1
    rw [mul_pow, show g.toMul ^ c = 1 from hg, show h.toMul ^ c = 1 from hh, _root_.mul_one]
  smul_mem' a g hg := by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ^ c = 1
    rw [← MonObj.pow_comp, show g.toMul ^ c = 1 from hg, MonObj.one_comp]

theorem comp_act_natCast {s : S ⟶ Sp R} (o : Obj b N s) {T : Over S} (q : T ⟶ o.A) (n : ℕ) :
    q ≫ o.act.act (n : D.O) = q ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero_eq_one_wvs, pow_zero, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, o.act.add, o.act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

theorem exists_sub (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (hw : w.IsMaximal) (hu : uIdeal D r ≤ w) (hj : j ≤ D.n)
    (hc : ∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) (hm : D.m = 1) {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {s : Sp k ⟶ Sp R} (o : Obj b N s) :
    ∃ H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A), (∀ c' : D.O, ∀ h ∈ H, h ≫ o.act.act c' ∈ H) ∧ (∀ h ∈ H, h ^ c = 1) ∧
      (∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
        (lift h₁ 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h₂) 1) ∧
      (∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
        (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h) 1) → g ∈ H) ∧
      (∀ h ∈ H, (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) h) → KilledBy o w h) ∧
      Nat.card {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h} = Ideal.absNorm w ^ j := by
  obtain ⟨ex, hce, hje⟩ := hc
  have hpk : ((p : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hck : (c : k) ≠ 0 := by rw [hce, Nat.cast_pow]; exact pow_ne_zero _ hpk
  obtain ⟨e, he, hl, hr, hadj, hskew, hnd⟩ : ∃ e : (𝟙_ (Over (Sp k)) ⟶ o.A) → (𝟙_ (Over (Sp k)) ⟶ o.A) → kˣ,
      (∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ,
        Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 g') u ↔
          u = unitOn (e g g')) ∧
      (∀ g₁ g₂ g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 →
        e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧
      (∀ g g₁ g₂ : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 →
        e g (g₁ * g₂) = e g g₁ * e g g₂) ∧
      (∀ (a : D.O) (g g' : 𝟙_ (Over (Sp k)) ⟶ o.A), g ^ c = 1 → g' ^ c = 1 →
        e (g ≫ o.act.act a) g' = e g (g' ≫ o.act.act (D.star a).unop)) ∧
      (∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → e g g' * e g' g = 1) ∧
      (∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g' ^ c = 1 → e g g' = 1) → g = 1) :=
    PQuot.exists_pairing o c ⟨ex, hce⟩ k hpk (𝟙 _)
  have hinj : Function.Injective (unitOn (R := k)) := by
    refine Units.map_injective (f := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) ?_
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.injective
  have hone : unitOn (1 : kˣ) = 1 := map_one (Units.map _)
  have he1 : ∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 →
      (Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 g') 1 ↔
        e g g' = 1) := fun g g' hg hg' => by
    rw [he g g' hg hg']
    exact ⟨fun h => (hinj (hone.trans h)).symm, fun h => by rw [h]; exact hone.symm⟩
  let M := torsSub o (𝟙_ (Over (Sp k))) c
  haveI : Finite M := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hck).1
  have hM0 : ∀ x : M, x = 0 ↔ x.1.toMul = 1 := fun x => ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  have hkill : ∀ (v : Ideal (𝓞 D.F)) (x : M), (∀ a ∈ v, a • x = 0) ↔ KilledBy o v x.1.toMul :=
    fun v x => forall₂_congr fun a _ => hM0 (a • x)
  have hwne : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw (NumberField.RingOfIntegers.not_isField D.F)
  have hq : 0 < Ideal.absNorm w := Nat.pos_of_ne_zero fun h => hwne (Ideal.absNorm_eq_zero_iff.1 h)
  have hle : Ideal.absNorm w ^ j ≤ Nat.card {x : M // ∀ a ∈ w, a • x = 0} := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero]
      haveI : Nonempty {x : M // ∀ a ∈ w, a • x = 0} := ⟨⟨0, fun a _ => smul_zero a⟩⟩
      exact Nat.card_pos
    · have hrk : Nat.card {g : 𝟙_ (Over (Sp k)) ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * D.n) :=
        GlobalTheory.T.card_torsion_killed_by_ideal_char_zero p D R b N (Sp k) s o w hwne k (𝟙 _)
      have htor : ∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, KilledBy o w g → g ^ c = 1 := fun g hg => by
        have h1 := hg _ (hu (p_mem_uIdeal D r))
        rw [map_natCast, comp_act_natCast] at h1
        obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (hje hj0).ne'
        rw [hce, pow_succ', pow_mul, h1, one_pow]
      let φ : {g : 𝟙_ (Over (Sp k)) ⟶ o.A // KilledBy o w g} ≃ {x : M // ∀ a ∈ w, a • x = 0} :=
        { toFun := fun g => ⟨⟨Additive.ofMul g.1, htor g.1 g.2⟩, (hkill w _).2 g.2⟩
          invFun := fun x => ⟨x.1.1.toMul, (hkill w _).1 x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Nat.card_congr φ, hrk, hm, Nat.one_mul]
      exact Nat.pow_le_pow_right hq hj
  obtain ⟨K, Kiso, Kmax, Ku, Kcard⟩ := GlobalTheory.T.perfect_pairing_torsion_module p D r w j c hw hu ⟨ex, hce⟩ M
    (fun x => (hM0 _).2 x.2) k (fun x y => e x.1.toMul y.1.toMul)
    (fun x x' y => hl _ _ _ x.2 x'.2 y.2) (fun x y y' => hr _ _ _ x.2 y.2 y'.2)
    (fun a x y => by
      have := hadj (algebraMap (𝓞 D.F) D.O a) _ _ x.2 y.2
      rw [D.star_F, MulOpposite.unop_op] at this
      exact this)
    (fun x y => hskew _ _ x.2 y.2)
    (fun x h => (hM0 x).2 (hnd _ x.2 fun g' hg' => h ⟨Additive.ofMul g', hg'⟩)) hle
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A) :=
    { carrier := {g | ∃ x ∈ K, x.1.toMul = g}
      one_mem' := ⟨0, K.zero_mem, rfl⟩
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, K.add_mem hx hy, rfl⟩
      inv_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨-x, K.neg_mem hx, rfl⟩ }
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro c' _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := GlobalTheory.T.integers_surjective_of_rank_one p D hm c'
    exact ⟨a • x, K.smul_mem a hx, rfl⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (he1 _ _ x.2 y.2).2 (Kiso x hx y hy)
  · intro g hg h
    exact ⟨⟨Additive.ofMul g, hg⟩, Kmax _ fun y hy => (he1 _ _ hg y.2).1 (h _ ⟨y, hy, rfl⟩), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ ⟨i, hi⟩
    exact (hkill w x).1 (Ku x hx ⟨i, (hkill _ x).2 hi⟩)
  · rw [← Kcard]
    refine (Nat.card_eq_of_bijective (fun x : {x : M // x ∈ K ∧ ∀ a ∈ w, a • x = 0} =>
      (⟨x.1.1.toMul, ⟨x.1, x.2.1, rfl⟩, (hkill w _).1 x.2.2⟩ :
        {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h})) ⟨fun x y h => ?_, ?_⟩).symm
    · exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))
    · rintro ⟨_, ⟨x, hx, rfl⟩, hk⟩
      exact ⟨⟨x, hx, (hkill w x).2 hk⟩, rfl⟩

theorem exists_isPIsog_isTj : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ Sp R) (o : Obj b N s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ IsTj r w j o o' ψ := by
  intro p _ D R _ _ b N _ _ hp r w j c hw hu hj hc hm k _ _ s o
  haveI := charZero_of_base b hp s
  obtain ⟨H, stab, hpow, hiso, hmax, hU, hcard⟩ := exists_sub r w j c hw hu hj hc hm o
  obtain ⟨ex, hce, -⟩ := hc
  have hck : (c : k) ≠ 0 := by
    rw [hce, Nat.cast_pow]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hfin : Finite H := by
    haveI := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hck).1
    exact Finite.of_injective (fun h : H => (⟨h.1, hpow h.1 h.2⟩ : {g : 𝟙_ (Over (Sp k)) ⟶ o.A // g ^ c = 1}))
      fun a a' h => Subtype.ext (Subtype.mk.inj h)
  have hinj : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ Sp k) (h h' : 𝟙_ (Over (Sp k)) ⟶ o.A),
      toUnit (Over.mk x) ≫ h = toUnit (Over.mk x) ≫ h' → h = h' := fun κ _ x h h' e => by
    haveI : Nonempty (Over.mk x).left := inferInstanceAs (Nonempty (PrimeSpectrum κ))
    haveI := GlobalTheory.PointQuot.epi_toUnit (Over.mk x)
    exact (cancel_epi _).1 e
  have hfree : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ Sp k) (h : 𝟙_ (Over (Sp k)) ⟶ o.A),
      toUnit (Over.mk x) ≫ h = 1 ↔ h = 1 := fun κ _ x h =>
    ⟨fun e => hinj κ x h 1 (by rw [e, MonObj.comp_one]), fun e => by rw [e, MonObj.comp_one]⟩
  obtain ⟨o', ψ, hψ, hker⟩ := PQuot.exists_quot o c ⟨ex, hce⟩ hp H hfin (fun κ _ _ x h _ e => (hfree κ x h).1 e)
    stab hpow hiso (fun κ _ _ x g hg ho => PQuot.max_geom o c hck H hpow hmax κ x g hg ho)
  refine ⟨o', ψ, hψ, fun κ _ _ _ x => ?_⟩
  have hkb : ∀ (v : Ideal (𝓞 D.F)) (h : 𝟙_ (Over (Sp k)) ⟶ o.A),
      KilledBy o v (toUnit (Over.mk x) ≫ h) ↔ KilledBy o v h := fun v h =>
    forall₂_congr fun a _ => by rw [Category.assoc, hfree]
  refine ⟨fun g hg ⟨i, hi⟩ => ?_, ?_⟩
  · obtain ⟨h, hh, rfl⟩ := (hker κ x g).1 hg
    exact (hkb w h).2 (hU h hh ⟨i, (hkb _ h).1 hi⟩)
  · rw [hm, Nat.one_mul, ← hcard]
    refine (Nat.card_eq_of_bijective (fun h : {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h} =>
      (⟨toUnit (Over.mk x) ≫ h.1, (hker κ x _).2 ⟨h.1, h.2.1, rfl⟩, (hkb w _).2 h.2.2⟩ :
        {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g})) ⟨fun a a' h => ?_, ?_⟩).symm
    · exact Subtype.ext (hinj κ x _ _ (congrArg Subtype.val h))
    · rintro ⟨g, hg, hk⟩
      obtain ⟨h, hh, rfl⟩ := (hker κ x g).1 hg
      exact ⟨⟨h, hh, (hkb w h).1 hk⟩, rfl⟩

end GlobalTheory.UPel.HT.ES.TjExists
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open GlobalTheory.ZM GlobalTheory.SiegelTor
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open IsLocalRing
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

namespace GlobalTheory.CrysRed


open GlobalTheory.Published.GrothendieckMessing in
theorem exists_crysRed : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] (a : GlobalTheory.UPel.HT.OActN O A₀), ∃ red : Crys (divided₂ hsq) (spMap π) A₀ →ₛₗ[π] HdR A₀, Module.Finite C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Module.Projective C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Function.Surjective red ∧ (∀ x, red x = 0 → x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀))) ∧ (∀ d y, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl A₀).Corr d y ↔ red d = y) ∧ (∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a c d) = GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d)) ∧ ∃ E' M : Submodule C (Crys (divided₂ hsq) (spMap π) A₀), IsCompl E' M ∧ ∀ y, y ∈ Fil A₀ ↔ ∃ d ∈ E', red d = y := by
  intro C C₀ _ _ _ _ π hπ hsq A₀ _ _ hA₀ O _ a
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hI2] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  let κ := divided₂ hsq
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have GD : GlobalTheory.Published.GrothendieckDeformation :=
    GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl A₀ hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A' hA'
  have HC := (GD C (RingHom.ker π) κ hκ C₀ π hπ rfl).1
  obtain ⟨bij, ⟨N0, hN0⟩, hAdm⟩ := HC g A₀ A' i' h' hA' hg
  let e := LinearEquiv.ofBijective (crysToDR κ h') (HC.crysToDR_bijective h' hA' hg)
  have ee : ∀ xA, crysToDR κ h' (e.symm xA) = xA := e.apply_symm_apply
  letI : Algebra C C₀ := π.toAlgebra
  have hBC := (ADR.2.2.1 C A' g hA' hg C₀ A₀ i' h').1
  obtain ⟨hfinA, hprojA, -⟩ := ADR.1.prim hA' hg
  haveI := hfinA
  haveI := hprojA
  have hfin : Module.Finite C (Crys κ (spMap π) A₀) := Module.Finite.equiv e.symm
  have hproj : Module.Projective C (Crys κ (spMap π) A₀) := Module.Projective.of_equiv e.symm
  let red : Crys κ (spMap π) A₀ →ₛₗ[π] HdR A₀ := hBC.bcMap.comp (crysToDR κ h')
  have hm : ∀ x, (crysRedMor κ rfl A₀).Corr x (red x) := fun x ↦
    (corr_crysToDR_iff rfl h' bij.2 x (red x)).1 (by exact hBC.corr_iff.2 rfl)
  have hcorr : ∀ d y, (crysRedMor κ rfl A₀).Corr d y ↔ red d = y := fun d y ↦
    ⟨fun H ↦ by exact hBC.corr_iff.1 ((corr_crysToDR_iff rfl h' bij.2 d y).2 H), fun H ↦ H ▸ hm d⟩
  have hred : Function.Surjective red := by
    intro y
    let l : primDR A' →ₗ[C] C₀ :=
      { toFun c := y ((redMor h').pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨xA, hx⟩ := Module.projective_lifting_property (Algebra.linearMap C C₀) l hπ
    refine ⟨e.symm xA, ?_⟩
    show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
    rw [ee]
    exact hBC.corr_iff.1 fun c ↦ (LinearMap.congr_fun hx c).symm
  have hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule C (Crys κ (spMap π) A₀)) := by
    intro x hx
    have hc := hBC.corr_iff.2 hx
    have hmem := GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (crysToDR κ h' x) fun c ↦
      RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))
    have := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) hmem
    rw [Submodule.map_smul''] at this
    have ex : e.symm.toLinearMap (crysToDR κ h' x) = x := e.symm_apply_apply x
    rw [ex] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hact : ∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct κ (spMap π) a c d) =
      GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d) := by
    intro c d
    haveI := a.hom c
    refine (hcorr _ _).1 ?_
    rw [GlobalTheory.HTSummand.crysAct_apply, GlobalTheory.HTSummand.crysAct_apply]
    exact GrpMor.Corr.push (m := crysRedMor κ rfl A₀) (crysRedMor κ rfl A₀) (a.act c) (a.act c) (by simp) (hm d)
  have hFN : IsCompl (liftFil κ h') (N0.comap (crysToDR κ h')) :=
    (Submodule.orderIsoMapComap e).symm.isCompl hN0
  refine ⟨red, hfin, hproj, hred, hker, hcorr, hact, liftFil κ h', N0.comap (crysToDR κ h'), hFN, fun y ↦ ⟨?_, ?_⟩⟩
  · intro hy
    obtain ⟨xA, hxA, hc⟩ := (hAdm y).1 hy
    refine ⟨e.symm xA, ?_, ?_⟩
    · show crysToDR κ h' (e.symm xA) ∈ Fil A'
      rw [ee]; exact hxA
    · show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
      rw [ee]; exact hBC.corr_iff.1 hc
  · rintro ⟨d, hd, rfl⟩
    exact (hAdm (red d)).2 ⟨crysToDR κ h' d, hd, by exact hBC.corr_iff.2 rfl⟩

end GlobalTheory.CrysRed
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] {d : ℕ}

theorem finite_tsze (k : Type) [Field k] (d : ℕ) : Module.Finite k (TrivSqZeroExt k (Fin d → k)) :=
  Module.Finite.of_surjective
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))).coprod (TrivSqZeroExt.inrHom k (Fin d → k)))
    (fun x => ⟨(x.fst, x.snd), by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]⟩)

theorem isArtinianRing_tsze (k : Type) [Field k] (d : ℕ) : IsArtinianRing (TrivSqZeroExt k (Fin d → k)) :=
  haveI := finite_tsze k d; IsArtinianRing.of_finite k _

theorem exists_coords (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀) (l : primDR A₀ →ₗ[k] TrivSqZeroExt k V) :
    ∃ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀,
      ∀ c, e ((GlobalTheory.FODef.constMorV k V A₀).pull c) = l c := by
  have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V) (GlobalTheory.FODef.constMorV k V A₀)
  let eqv := LinearEquiv.ofBijective _ hm
  refine ⟨(LinearMap.liftBaseChange (TrivSqZeroExt k V) l) ∘ₗ eqv.symm.toLinearMap, fun c => ?_⟩
  have : (GlobalTheory.FODef.constMorV k V A₀).pull c = eqv (1 ⊗ₜ c) :=
    (one_smul (TrivSqZeroExt k V) ((GlobalTheory.FODef.constMorV k V A₀).pull c)).symm
  rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe, eqv.symm_apply_apply,
    LinearMap.liftBaseChange_tmul, one_smul]

def glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) :
    Submodule (TrivSqZeroExt k (Fin d → k))
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) where
  carrier := {e | ∃ x ∈ Fil A₀, ∃ z : Fin d → HdR A₀, (∀ j, z j ∈ Fil A₀) ∧
      ∀ c : primDR A₀, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
        TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (fun j => (f j x + z j) c)}
  add_mem' := by
    rintro e e' ⟨x, hx, z, hz, he⟩ ⟨x', hx', z', hz', he'⟩
    refine ⟨x + x', add_mem hx hx', z + z', fun j => add_mem (hz j) (hz' j), fun c => ?_⟩
    rw [LinearMap.add_apply, he c, he' c]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply, map_add (f := _),
        LinearMap.add_apply, zero_add, Pi.zero_apply, add_zero]
      ring
  zero_mem' := ⟨0, zero_mem _, 0, fun _ => zero_mem _, fun c => by rw [LinearMap.zero_apply]; ext <;> simp⟩
  smul_mem' := by
    rintro r e ⟨x, hx, z, hz, he⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, fun j => r.fst • z j + r.snd j • x,
      fun j => add_mem (Submodule.smul_mem _ _ (hz j)) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, he c, smul_eq_mul]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply, Pi.smul_apply,
        map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_zero, zero_add,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.zero_apply]
      ring

theorem exists_mem_glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) {x : HdR A₀} (hx : x ∈ Fil A₀) :
    ∃ e ∈ glueFil A₀ f, ∀ c, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr ((LinearMap.pi fun j => f j x) c) := by
  obtain ⟨e, he⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ x + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => f j x)
  refine ⟨e, ⟨x, hx, 0, fun _ => zero_mem _, fun c => ?_⟩, fun c => ?_⟩
  · rw [he c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  · rw [he c]; simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.HTGlue
end
end
