module

public import Development.EtaleCohomology.EtaleSheaves.Bundle004
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafOfRingsLocSurjPf

theorem cover_hit {X : Scheme.{0}} (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X) (x : X) :
    ∃ (U : Scheme.{0}) (w : U ⟶ X), Etale w ∧ x ∈ Set.range w ∧ S.arrows w := by
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff).1 hS
  obtain ⟨i, hi⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 x
  exact ⟨𝒰.X i, 𝒰.f i, 𝒰.map_prop i, hi, h𝒰 _ _ (Presieve.ofArrows.mk i)⟩

theorem LeafOfRingsLocSurj_of : LateralTheory.E.E8.TwSec.LeafOfRingsLocSurj := by
  intro R _ M X s x
  have hS := Presheaf.imageSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op X) s
  obtain ⟨U, w, hw, hx, t, ht⟩ := cover_hit _ hS x
  exact ⟨U, w, hw, hx, t, ht.symm⟩

end LateralTheory.E.LeafOfRingsLocSurjPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec.Gen

theorem prim_pow_eq_one {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

theorem prim_isPrimitiveRoot {q : ℕ} [NeZero q] {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (ζ : Prim q A) :
    IsPrimitiveRoot (φ ζ.1) q := by
  have hu : IsUnit (q : K) := by simpa using ζ.2.1.map φ
  have : NeZero (q : K) := ⟨hu.ne_zero⟩
  have h := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
  rw [ζ.2.2, map_zero] at h
  have h2 : Polynomial.aeval (φ ζ.1) (Polynomial.cyclotomic q ℤ) = 0 := by simpa using h
  rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic, ← Polynomial.IsRoot.def,
    Polynomial.isRoot_cyclotomic_iff] at h2

theorem exists_pow {q : ℕ} [NeZero q] {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (ζ ξ : Prim q A) :
    ∃ k < q, k.Coprime q ∧ φ ξ.1 = φ ζ.1 ^ k := by
  have hζ := prim_isPrimitiveRoot φ ζ
  have hξ := prim_isPrimitiveRoot φ ξ
  obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  refine ⟨i, hi, ?_, e.symm⟩
  exact (hζ.pow_iff_coprime (NeZero.pos q) i).mp (by rw [e]; exact hξ)

theorem key_ring {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (x y : A) (q k : ℕ) (hq : (q : K) ≠ 0)
    (hx : x ^ q = 1) (hy : y ^ q = 1) (h : φ x = φ y ^ k) :
    φ (∑ b ∈ Finset.range q, (x * y ^ (k * (q - 1))) ^ b) ≠ 0 ∧
    ∀ (B : Type) [CommRing B] (ψ : A →+* B), IsUnit (ψ (∑ b ∈ Finset.range q, (x * y ^ (k * (q - 1))) ^ b)) →
      ψ x = ψ y ^ k := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hkq : k * (q - 1) + k = k * q := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.mpr hq0); simp [mul_add]; ring
  have hyk : y ^ (k * (q - 1)) * y ^ k = 1 := by rw [← pow_add, hkq, mul_comm, pow_mul, hy, one_pow]
  have hu : (x * y ^ (k * (q - 1))) ^ q = 1 := by
    rw [mul_pow, hx, one_mul, ← pow_mul, mul_comm, pow_mul, hy, one_pow]
  refine ⟨?_, ?_⟩
  · have : φ (x * y ^ (k * (q - 1))) = 1 := by
      rw [map_mul, map_pow, h, ← pow_add, add_comm, hkq, mul_comm, pow_mul, ← map_pow, hy, map_one, one_pow]

    simpa [map_sum, map_pow, this] using hq
  · intro B _ ψ hs
    have h0 : ψ (∑ b ∈ Finset.range q, (x * y ^ (k * (q - 1))) ^ b) * (ψ (x * y ^ (k * (q - 1))) - 1) = 0 := by
      rw [← map_one ψ, ← map_sub, ← map_mul, geom_sum_mul, hu, sub_self, map_zero]
    have h1 : ψ (x * y ^ (k * (q - 1))) = 1 := by
      have := (hs.mul_right_eq_zero).mp h0
      exact sub_eq_zero.mp this
    calc ψ x = ψ x * ψ (y ^ (k * (q - 1)) * y ^ k) := by rw [hyk, map_one, mul_one]
      _ = ψ (x * y ^ (k * (q - 1))) * ψ y ^ k := by simp only [map_mul, map_pow]; ring
      _ = ψ y ^ k := by rw [h1, one_mul]

theorem isUnit_res {W : Scheme.{0}} (s : Γ(W, ⊤)) :
    IsUnit ((Scheme.Γ.map (W.basicOpen s).ι.op).hom s) := by
  set O := W.basicOpen s
  rw [Scheme.Γ_map_op]
  refine RingedSpace.isUnit_of_isUnit_germ O.toScheme.toRingedSpace ⊤ _ (fun y _ => ?_)
  have hy : y ∈ O.toScheme.basicOpen (O.ι.appTop s) := by
    rw [← Scheme.preimage_basicOpen_top]
    show O.ι y ∈ O
    exact y.2
  exact (Scheme.mem_basicOpen_top _ _ _).mp hy

end LateralTheory.E.E8.TwSec.Gen

namespace LateralTheory.E.E8.TwSec.Gen

theorem map_mk {q : ℕ} (j : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ξ : Prim q A) (r : ULift.{1} (ZMod q)) :
    ((twF q j).map f).hom (Submodule.Quotient.mk (p := twRel q j A) (Finsupp.single ξ r)) =
      Submodule.Quotient.mk (p := twRel q j B) (Finsupp.single (ξ.map f.hom) r) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain _ (Finsupp.single ξ r)) = _
  rw [Finsupp.mapDomain_single]

theorem mk_pow {q : ℕ} (j : ℤ) {B : CommRingCat.{0}} (ζ ξ : Prim q B) (k : ℕ) (hk : k < q) (hc : k.Coprime q)
    (h : ξ.1 = ζ.1 ^ k) :
    (Submodule.Quotient.mk (p := twRel q j B) (Finsupp.single ξ 1) : (twF q j).obj B) =
      ULift.up ((((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ)) : ZMod q) • twCls j ζ := by
  unfold twCls
  have h1 : (ULift.up ((((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ)) : ZMod q) : ULift.{1} (ZMod q)) •
      (Submodule.Quotient.mk (p := twRel q j B) (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ)) : ZMod q))) := by
    rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  refine Eq.trans ?_ h1.symm
  rw [Submodule.Quotient.eq]
  refine Submodule.subset_span ⟨ζ, ξ, ZMod.unitOfCoprime k hc, ?_, rfl⟩
  rw [h, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

theorem res_le {q : ℕ} (j : ℤ) {W : Scheme.{0}} {O O' : W.Opens} (h : O' ≤ O) {x y : (twF q j).obj Γ(W, ⊤)}
    (e : ((twF q j).map (Scheme.Γ.map O.ι.op)).hom x = ((twF q j).map (Scheme.Γ.map O.ι.op)).hom y) :
    ((twF q j).map (Scheme.Γ.map O'.ι.op)).hom x = ((twF q j).map (Scheme.Γ.map O'.ι.op)).hom y := by
  rw [← W.homOfLE_ι h, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp]
  exact congrArg (ModuleCat.Hom.hom ((twF q j).map (Scheme.Γ.map (W.homOfLE h).op))) e

theorem core {q : ℕ} [NeZero q] (j : ℤ) {W : Scheme.{0}} (ζ ξ : Prim q Γ(W, ⊤)) (w0 : W) :
    ∃ (O : W.Opens) (c : ZMod q), w0 ∈ O ∧
      ((twF q j).map (Scheme.Γ.map O.ι.op)).hom (Submodule.Quotient.mk (p := twRel q j Γ(W, ⊤)) (Finsupp.single ξ 1)) =
        ((twF q j).map (Scheme.Γ.map O.ι.op)).hom (ULift.up c • twCls j ζ) := by
  obtain ⟨k, hk, hc, e⟩ := exists_pow (W.Γevaluation w0).hom ζ ξ
  have hq : ((q : ℕ) : W.residueField w0) ≠ 0 := by
    have := ζ.2.1.map (W.Γevaluation w0).hom
    simpa using this.ne_zero
  obtain ⟨h1, h2⟩ := key_ring (W.Γevaluation w0).hom ξ.1 ζ.1 q k hq (prim_pow_eq_one ξ) (prim_pow_eq_one ζ) e
  refine ⟨W.basicOpen (∑ b ∈ Finset.range q, (ξ.1 * ζ.1 ^ (k * (q - 1))) ^ b),
    (((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ) : ZMod q),
    (W.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) w0 trivial _).mp h1, ?_⟩
  have hs := h2 _ (Scheme.Γ.map (W.basicOpen (∑ b ∈ Finset.range q, (ξ.1 * ζ.1 ^ (k * (q - 1))) ^ b)).ι.op).hom
    (isUnit_res _)
  refine (map_mk j _ ξ 1).trans ?_
  refine Eq.trans ?_ (LinearMap.map_smul _ _ _).symm
  refine Eq.trans ?_ (congrArg _ (map_mk j _ ζ 1).symm)
  exact mk_pow j _ _ k hk hc hs

end LateralTheory.E.E8.TwSec.Gen

namespace LateralTheory.E.E8.TwSec

open Gen in
theorem LeafTwGen_of : LeafTwGen := by
  intro q _ j W ζ t w0
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel q j Γ(W, ⊤)) t
  induction f using Finsupp.induction_linear with
  | zero =>
    refine ⟨⊤, 0, trivial, ?_⟩
    have hm : (Submodule.Quotient.mk 0 : (twF q j).obj Γ(W, ⊤)) = 0 := Submodule.Quotient.mk_zero _
    have h0 : (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • twCls j ζ = 0 := zero_smul _ _
    rw [hm, h0]
    exact rfl
  | add f g hf hg =>
    obtain ⟨O1, c1, h1, e1⟩ := hf
    obtain ⟨O2, c2, h2, e2⟩ := hg
    refine ⟨O1 ⊓ O2, c1 + c2, ⟨h1, h2⟩, ?_⟩
    have hm : (Submodule.Quotient.mk (f + g) : (twF q j).obj Γ(W, ⊤)) =
        (Submodule.Quotient.mk f : (twF q j).obj Γ(W, ⊤)) + (Submodule.Quotient.mk g : (twF q j).obj Γ(W, ⊤)) :=
      Submodule.Quotient.mk_add _
    rw [hm]
    refine (LinearMap.map_add _ _ _).trans ?_
    rw [res_le j inf_le_left e1, res_le j inf_le_right e2]
    refine (LinearMap.map_add _ _ _).symm.trans ?_
    congr 1
    exact (add_smul _ _ _).symm
  | single ξ r =>
    obtain ⟨O, c, h, e⟩ := core j ζ ξ w0
    refine ⟨O, r.down * c, h, ?_⟩
    have hr : Finsupp.single ξ r = r • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hm : (Submodule.Quotient.mk (r • Finsupp.single ξ (1 : ULift.{1} (ZMod q))) : (twF q j).obj Γ(W, ⊤)) =
        r • (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q j).obj Γ(W, ⊤)) :=
      Submodule.Quotient.mk_smul _ _ _
    rw [hr, hm]
    refine (LinearMap.map_smul _ _ _).trans ?_
    rw [e]
    refine (LinearMap.map_smul _ _ _).symm.trans ?_
    congr 1
    exact smul_smul _ _ _

end LateralTheory.E.E8.TwSec
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

theorem twF_res_comp {q : ℕ} (j : ℤ) {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : (twF q j).obj Γ(Z, ⊤)) :
    ((twF q j).map (Scheme.Γ.map (a ≫ b).op)).hom x =
      ((twF q j).map (Scheme.Γ.map a.op)).hom (((twF q j).map (Scheme.Γ.map b.op)).hom x) := by
  rw [op_comp, Functor.map_comp, Functor.map_comp]; rfl

theorem twF_map_cls {q : ℕ} (j : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) (c : ZMod q) :
    ((twF q j).map f).hom (ULift.up c • twCls j ζ) = ULift.up c • twCls j (ζ.map f.hom) := by
  rw [map_smul]
  congr 1
  unfold twCls
  change Submodule.mapQ _ _ _ (twRel_le q j f.hom) _ = _
  rw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem twF_eq_zero_of_not_unit {q : ℕ} (j : ℤ) {A : CommRingCat.{0}} (hq : ¬ IsUnit (q : A)) (t : (twF q j).obj A) :
    t = 0 := by
  haveI : IsEmpty (Prim q A) := ⟨fun ζ => hq ζ.2.1⟩
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  rw [Subsingleton.elim f 0]
  exact Submodule.Quotient.mk_zero _

theorem LeafTwPt_of (hA : LeafTwAdj) (hG : LeafTwGen) (hF : LeafTwFieldZ) : LeafTwPt := by
  intro q _ j U u t V g v hgv ht
  by_cases hq : IsUnit (q : Γ(U, ⊤))
  swap
  · refine ⟨U, 𝟙 U, inferInstance, ⟨u, rfl⟩, ?_⟩
    rw [twF_eq_zero_of_not_unit j hq t]; exact map_zero _
  obtain ⟨W₁, w₁, hw₁, ⟨w, hw⟩, ⟨ζ⟩⟩ := hA q U u hq
  haveI := hw₁
  obtain ⟨O, c, hwO, hO⟩ := hG q j W₁ ζ (((twF q j).map (Scheme.Γ.map w₁.op)).hom t) w
  have hO' : ((twF q j).map (Scheme.Γ.map (O.ι ≫ w₁).op)).hom t =
      ULift.up c • twCls j (ζ.map (Scheme.Γ.map O.ι.op).hom) := by
    rw [twF_res_comp, hO]; exact twF_map_cls j _ ζ c
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := O.ι ≫ w₁) (g := g)
    (⟨w, hwO⟩ : O.toScheme) v (by rw [hgv]; exact hw)
  have hc : c = 0 := by
    let P := pullback (O.ι ≫ w₁) g
    let φ := P.evaluation ⊤ p trivial
    have e : ((twF q j).map (Scheme.Γ.map (pullback.fst (O.ι ≫ w₁) g ≫ O.ι ≫ w₁).op)).hom t = 0 := by
      rw [pullback.condition, twF_res_comp, ht, map_zero]
    rw [twF_res_comp, hO', twF_map_cls] at e
    have key := twF_map_cls j φ (Prim.map (Scheme.Γ.map (pullback.fst (O.ι ≫ w₁) g).op).hom
      (Prim.map (Scheme.Γ.map O.ι.op).hom ζ)) c
    exact hF q j (P.residueField p) (Field.toIsField _) _ c
      (key.symm.trans ((congrArg (fun x => ((twF q j).map φ).hom x) e).trans (map_zero _)))
  refine ⟨O, O.ι ≫ w₁, inferInstance, ⟨⟨w, hwO⟩, hw⟩, ?_⟩
  rw [hO', hc]
  exact zero_smul (ULift (ZMod q)) _

end LateralTheory.E.E8.TwSec
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleExistenceAndUniqueness

open LateralTheory.E.CupProductRingLaws

section Ext
variable {R : Type} [CommRing R]

theorem free_hom_ext {P : PSh} {F : Shv R} (f g : (free R).obj P ⟶ F)
    (h : ∀ U x, (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) : f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (J := Scheme.etaleTopology) f.hom g.hom F.property
  ext U : 2
  induction U using Opposite.rec with | _ U => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  exact h U x

theorem cochain_ext_ev {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (hev : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev α p s h U x = ev β p s h U x) :
    α = β := by
  apply Cochain.ext
  intro p s hps
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨p.natAbs, by omega⟩
    have : (chainsXIso R E k).inv ≫ α.v _ _ hps = (chainsXIso R E k).inv ≫ β.v _ _ hps :=
      free_hom_ext _ _ (fun U x => hev k s hps U x)
    simpa using this
  · refine (HomologicalComplex.isZero_extend_X _ _ p (fun i => ?_)).eq_of_src _ _
    show -(i : ℤ) ≠ p
    omega

theorem res_isZero (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) :=
  HomologicalComplex.isZero_extend_X _ _ s (fun i => by show (i : ℤ) ≠ s; omega)

end Ext

def EtaleKummerChernCocycleEvaluationsUnique : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ γ γ', IsEtaleFirstChernClassCocycle q L γ → IsEtaleFirstChernClassCocycle q L γ' →
    (∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 1 (by simp) U x = ev γ'.1 1 1 (by simp) U x) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev γ.1 2 0 (by simp) U x = ev γ'.1 2 0 (by simp) U x

def EtaleKummerChernCocycleExists : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ γ, IsEtaleFirstChernClassCocycle q L γ

theorem etale_kummer_chern_cocycle_eq_of_evaluation_uniqueness (hU : EtaleKummerChernCocycleEvaluationsUnique) (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hq : Inv q E)
    (γ γ' : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (h : IsEtaleFirstChernClassCocycle q L γ) (h' : IsEtaleFirstChernClassCocycle q L γ') :
    γ = γ' := by
  obtain ⟨h1, h2⟩ := hU q L hq γ γ' h h'
  apply Subtype.ext
  apply cochain_ext_ev
  intro p s hs U x
  rcases p with _ | _ | _ | p
  · obtain rfl : s = 2 := by omega
    rw [h.1 U x, h'.1 U x]
  · obtain rfl : s = 1 := by omega
    exact h1 U x
  · obtain rfl : s = 0 := by omega
    exact h2 U x
  · unfold ev
    rw [(res_isZero (tw q 1) s (by omega)).eq_of_tgt ((chainsXIso _ E _).inv ≫ γ.1.v _ _ hs)
      ((chainsXIso _ E _).inv ≫ γ'.1.v _ _ hs)]

theorem etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique (hE : EtaleKummerChernCocycleExists) (hU : EtaleKummerChernCocycleEvaluationsUnique) : EtaleFirstChernClassRepresentedByChernCocycle := by
  intro q _ E L hq
  obtain ⟨γ0, h0⟩ := hE q L hq
  refine ⟨⟨γ0, h0⟩, fun γ hγ => ?_⟩
  have hex : ∃ c : Ht q E 2 1, ∃ γ : Cocycle _ _ 2, CohomologyClass.mk γ = c ∧ IsEtaleFirstChernClassCocycle q L γ :=
    ⟨_, γ0, rfl, h0⟩
  obtain ⟨γ1, hc, h1⟩ := pick_spec hex
  have : γ1 = γ := etale_kummer_chern_cocycle_eq_of_evaluation_uniqueness hU q L hq γ1 γ h1 hγ
  subst this
  exact hc.symm

end LateralTheory.E.ChernCocycleExistenceAndUniqueness
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.FirstChernNaturality

variable {R : Type} [CommRing R]

theorem chainsXIso_inv_nat {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  simp [chains, chainsXIso, chainsN, HomologicalComplex.extendMap_f]

theorem freeGen_nat {P P' : PSh} (g : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R P' U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  unfold freeGen
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P')).app (op U)).hom
    ((((freeP R).map g).app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) = _
  congr 1
  simp only [ModuleCat.freeMk, freeP]
  simp [ModuleCat.free]
  erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem ev_zpull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (γ : Cocycle ((chains R).obj E') I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (zcomp (Cocycle.ofHom ((chains R).map f)) γ (zero_add n)).1 p s h U x =
      ev γ.1 p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  have hc : (zcomp (Cocycle.ofHom ((chains R).map f)) γ (zero_add n)).1.v (-(p : ℤ)) s h =
      ((chains R).map f).f (-(p : ℤ)) ≫ γ.1.v (-(p : ℤ)) s h := by
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (by simp) h]
  unfold ev
  rw [hc, ← Category.assoc, chainsXIso_inv_nat, Category.assoc]
  exact congrArg (((chainsXIso R E' p).inv ≫ γ.1.v (-(p : ℤ)) s h).hom.app (op U)).hom
    (freeGen_nat (f.app (op (SimplexCategory.mk p))) U x)

theorem sub_nat {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (f.app (op (SimplexCategory.mk l))).app (op U) (x.sub j l h) =
      Sx.sub (E := E') ((f.app (op (SimplexCategory.mk N))).app (op U) x) j l h := by
  unfold Sx.sub
  exact congrFun (congrArg (fun t => t.app (op U)) (f.naturality (SimplexCategory.subinterval j l h).op)) x

theorem lineUnit_comp {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 1 U) :
    lineUnit (f ≫ L) x = lineUnit L ((f.app (op (SimplexCategory.mk 1))).app (op U) x) := rfl

theorem etale_first_chern_class_natural_of_spec (hC1 : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassRepresentedByChernCocycle) : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassNaturalUnderPullback := by
  intro q _ E E' f L hinv
  have hinvE : Inv q E := fun U ⟨x⟩ => hinv U ⟨(f.app _).app _ x⟩
  obtain ⟨⟨γ, hγ⟩, h2⟩ := hC1 q L hinv
  rw [h2 γ hγ]
  obtain ⟨_, h2'⟩ := hC1 q (f ≫ L) hinvE
  rw [h2' (zcomp (Cocycle.ofHom ((chains _).map f)) γ (zero_add 2)) ?_]
  · rfl
  obtain ⟨g0, g1, g2⟩ := hγ
  refine ⟨?_, ?_, ?_⟩
  · intro U x
    rw [ev_zpull]; exact g0 U _
  · intro U x v hv
    rw [ev_zpull]; exact g1 U _ v (by rw [hv, lineUnit_comp])
  · intro U x v w hv hw
    rw [ev_zpull]
    exact g2 U _ v w (by rw [hv, lineUnit_comp, sub_nat]) (by rw [hw, lineUnit_comp, sub_nat])

end LateralTheory.E.FirstChernNaturality
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRingUnitPf
open LateralTheory.E.CupProductRingLaws

def UnitProp {q : ℕ} {i : ℤ} (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i)))) : Prop :=
  ∀ (U : Scheme.{0}) (t w : ℤ) (h : 0 + t = w) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
    Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → HEq (μ.mul U 0 t w h a b) b

def LeafUnitPair : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ),
  ∃ μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i))), IsTwPair μ ∧ UnitProp μ

def OneLoc {q : ℕ} {E : Spc} (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) : Prop :=
  ∀ (U : Scheme.{0}) (x : Sx E 0 U), Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g (ev (R := ZMod q) α.1 0 0 (by simp) U x) = resGen 0 ζ)

def LeafOneLoc : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E →
  ∀ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, IsOneCocycle q E α → OneLoc α

def LeafUnitAW : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) (i : ℤ)
  (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i)))), UnitProp μ →
  ∀ (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0), OneLoc α →
  ∀ (n : ℤ) (β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q i)) n),
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (0 + i))) (0 + n), μ.IsAW rfl α.1 β.1 γ.1 ∧
      CohomologyClass.mk γ = Ht.cast (by ring) (by ring) (CohomologyClass.mk β : Ht q E n i)

theorem LeafRingUnit_of (hcup : LeafCupSpec) (hex : LeafTwPairExists) (hun : LeafTwPairUnique) (hone : LeafOneSpec)
    (h1 : LeafUnitPair) (h2a : LeafOneLoc) (h2 : LeafUnitAW) : LeafRingUnit := by
  intro q _ E hE n i a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨μ, hμ, hU⟩ := h1 q i
  obtain ⟨⟨α, hα⟩, hαone⟩ := hone q E hE
  obtain ⟨γ, hγ, hγc⟩ := h2 q E i μ hU α (h2a q E hE α hα) n β
  have htw : IsTwPair (twPair q 0 i) := pick_spec (hex q 0 i)
  have hc : cup q (one q E) (CohomologyClass.mk β) = (twPair q 0 i).cup E rfl (one q E) (CohomologyClass.mk β) := rfl
  rw [hc, hun q 0 i _ μ htw hμ E rfl, hαone α hα, (hcup (ZMod q) μ E rfl).2 α β γ hγ, hγc]

end LateralTheory.E.LeafRingUnitPf
end
end
