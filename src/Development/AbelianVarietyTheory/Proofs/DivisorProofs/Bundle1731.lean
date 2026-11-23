module

public import ReciprocityTheory.DualLattices.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle283
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionLiftAbelianPartFiniteExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.LinearFormDegree.InvFun
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009

@[expose] public section

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PowLim

theorem pow_prime_step {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {p : ℕ}
    (hp : p.Prime) (hvp : v (p : C) = 1) {a b : C} (ha : 0 ≤ v a) (hb : 0 ≤ v b) {t ε : ℝ}
    (hεt : ε ≤ t) (hε1 : ε ≤ 1) (ht : (t : WithTop ℝ) ≤ v (a - b)) :
    ((t + ε : ℝ) : WithTop ℝ) ≤ v (a ^ p - b ^ p) := by
  let R : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        have ha' : 0 ≤ v a := ha
        have hb' : 0 ≤ v b := hb
        show 0 ≤ v (a * b)
        rw [v.map_mul]
        exact add_nonneg ha' hb'
      one_mem' := by
        show 0 ≤ v 1
        rw [v.map_one]
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (v.map_add _ _)
      zero_mem' := by
        show 0 ≤ v 0
        rw [v.map_zero]; exact le_top
      neg_mem' := fun {a} ha => by
        show 0 ≤ v (-a)
        rw [v.map_neg]; exact ha }
  have haR : a ∈ R := ha
  have hbR : b ∈ R := hb
  have hdR : a - b ∈ R := R.sub_mem haR hbR
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨a - b, hdR⟩ : R) ⟨b, hbR⟩
  have hr' := congrArg (fun z : R => (z : C)) hr
  simp only [Subring.coe_pow, Subring.coe_add, Subring.coe_mul, Subring.coe_natCast,
    sub_add_cancel] at hr'
  obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have e : a ^ p - b ^ p = (a - b) * (a - b) * (a - b) ^ k + (p : C) * (a - b) * (b * r) := by
    rw [hr']
    have : (a - b) ^ p = (a - b) * (a - b) * (a - b) ^ k := by rw [hk]; ring
    rw [this]; ring
  have h1 : (0 : WithTop ℝ) ≤ v ((a - b) ^ k) := R.pow_mem hdR k
  have h2 : (0 : WithTop ℝ) ≤ v (b * (r : C)) := R.mul_mem hbR r.2
  have hε : (ε : WithTop ℝ) ≤ v (a - b) := le_trans (WithTop.coe_le_coe.2 hεt) ht
  have hε1' : (ε : WithTop ℝ) ≤ 1 := by exact_mod_cast hε1
  rw [e]
  refine le_trans (le_min ?_ ?_) (v.map_add _ _)
  · rw [v.map_mul, v.map_mul, WithTop.coe_add]
    exact le_trans (add_le_add ht hε) (le_add_of_nonneg_right h1)
  · rw [v.map_mul, v.map_mul, WithTop.coe_add, hvp, add_comm (t : WithTop ℝ)]
    exact le_trans (add_le_add hε1' ht) (le_add_of_nonneg_right h2)

theorem pow_prime_pow_close : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ x y : C, IsIntV v x → IsIntV v y → 0 < v (x - y) → ∀ r : ℝ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (r : WithTop ℝ) ≤ v (x ^ p ^ N - y ^ p ^ N) := by
  intro C _ v p hp hvp x y hx hy hxy r
  have hx' : 0 ≤ v x := hx
  have hy' : 0 ≤ v y := hy
  obtain ⟨ε, hε0, hε1, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ (ε : WithTop ℝ) ≤ v (x - y) := by
    generalize v (x - y) = w at hxy
    induction w using WithTop.recTopCoe with
    | top => exact ⟨1, one_pos, le_rfl, le_top⟩
    | coe s =>
      have hs : 0 < s := by exact_mod_cast hxy
      exact ⟨min s 1, lt_min hs one_pos, min_le_right _ _, WithTop.coe_le_coe.2 (min_le_left _ _)⟩
  have hpow : ∀ (z : C) (n : ℕ), 0 ≤ v z → 0 ≤ v (z ^ n) := by
    intro z n hz
    rw [v.map_pow]
    exact nsmul_nonneg hz n
  have key : ∀ N : ℕ, ((((N : ℝ) + 1) * ε : ℝ) : WithTop ℝ) ≤ v (x ^ p ^ N - y ^ p ^ N) := by
    intro N
    induction N with
    | zero => simpa using hε
    | succ N ih =>
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have := pow_prime_step v hp hvp (hpow x (p ^ N) hx') (hpow y (p ^ N) hy')
        (t := ((N : ℝ) + 1) * ε) (ε := ε) (by nlinarith) hε1 ih
      rw [← pow_mul, ← pow_mul, ← pow_succ] at this
      refine le_trans (WithTop.coe_le_coe.2 (le_of_eq ?_)) this
      push_cast; ring
  obtain ⟨M, hM⟩ := exists_nat_gt (r / ε)
  refine ⟨M, fun N hN => le_trans (WithTop.coe_le_coe.2 ?_) (key N)⟩
  have h1 : (M : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_lt_iff₀ hε0] at hM
  nlinarith

end GlobalTheory.PowLim
end

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.IntInv

theorem exists_int_inv : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d : ℕ) (Θ : Fin d → MvPowerSeries (Fin d) C), (∀ a, MvIsInt v (Θ a)) → (∀ a, constantCoeff (Θ a) = 0) → (∀ a b, coeff (Finsupp.single b 1) (Θ a) = if a = b then 1 else 0) → ∃ Ψ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (Ψ a)) ∧ (∀ a, constantCoeff (Ψ a) = 0) ∧ (∀ a, subst Ψ (Θ a) = MvPowerSeries.X a) ∧ ∀ a, subst Θ (Ψ a) = MvPowerSeries.X a := by
  intro C _ _ v d Θ hint h0 h1
  set S := ReciprocityTheory.ChartRestriction.G.Sh.PTb.intRing v
  let Θ' : Fin d → MvPowerSeries (Fin d) S := fun a α => ⟨coeff α (Θ a), hint a α⟩
  have hΘ' : ∀ a, map S.subtype (Θ' a) = Θ a := fun a => by ext α; rfl
  have h0' : ∀ a, constantCoeff (Θ' a) = 0 := fun a => Subtype.ext (by
    change coeff 0 (Θ a) = 0
    rw [coeff_zero_eq_constantCoeff_apply]; exact h0 a)
  have h1' : ∀ a b, coeff (Finsupp.single b 1) (Θ' a) = (1 : Matrix (Fin d) (Fin d) S) a b := by
    intro a b
    apply Subtype.ext
    change coeff (Finsupp.single b 1) (Θ a) = _
    rw [h1 a b, Matrix.one_apply]
    split_ifs <;> rfl
  have hu : IsUnit (1 : Matrix (Fin d) (Fin d) S).det := by rw [Matrix.det_one]; exact isUnit_one
  obtain ⟨ψ, hψ0, hψΘ, hΘψ⟩ := ReciprocityTheory.ChartRestriction.G.LF.InvFun.exists_inv Θ' h0' 1 h1' hu
  have hsψ : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hsΘ : HasSubst Θ' := hasSubst_of_constantCoeff_zero h0'
  refine ⟨fun a => map S.subtype (ψ a), ?_, ?_, ?_, ?_⟩
  · intro a α
    rw [coeff_map]
    exact (coeff α (ψ a)).2
  · intro a
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hψ0 a]
    rfl
  · intro a
    have key := map_subst hsψ (h := S.subtype) (Θ' a)
    rw [hΘ', hψΘ a, map_X] at key
    exact key.symm
  · intro a
    have key := map_subst hsΘ (h := S.subtype) (ψ a)
    have e : (fun s => map S.subtype (Θ' s)) = Θ := funext hΘ'
    rw [e, hΘψ a, map_X] at key
    exact key.symm

end GlobalTheory.IntInv
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SemiAbSurj

theorem surjective_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {X Y : Over (Sp k)}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [Flat f.left]
    [LocallyOfFinitePresentation f.left]
    (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ Y, ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = y) : Surjective f.left := by
  refine ⟨Set.range_eq_univ.1 ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ := RationalPoint.exists_pt_mem (f.left.isOpenMap.isOpen_range).isClosed_compl
    (Set.nonempty_compl.2 hne)
  obtain ⟨x, rfl⟩ := h y
  exact hy ⟨RationalPoint.pt x, rfl⟩

end GlobalTheory.SemiAbSurj

namespace GlobalTheory.SemiAbSurj

theorem exists_root_unit {k : Type} [Field k] [IsAlgClosed k] (m : ℕ) (hm : m ≠ 0)
    (u : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ) : ∃ v : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ, v ^ m = u := by
  let e : Γ((𝟙_ (Over (Sp k))).left, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e u.val) (Nat.pos_of_ne_zero hm)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hz
    exact (u.isUnit.map e).ne_zero hz.symm
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom (Units.mk0 z hz0), Units.ext ?_⟩
  rw [← map_pow, Units.coe_map, Units.val_pow_eq_pow_val, Units.val_mk0, hz]
  exact e.symm_apply_apply u.val

theorem exists_pow_eq_of_torusExtension {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] (E : TorusExtension G) (m : ℕ) (hm : m ≠ 0)
    (x : 𝟙_ (Over (Sp k)) ⟶ G) : ∃ y : 𝟙_ (Over (Sp k)) ⟶ G, y ^ m = x := by
  classical
  letI := E.addCommGroup
  letI := E.free
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  have hB := E.isAbelian
  haveI := hB.smooth
  haveI := hB.comm

  have hsB := GlobalTheory.AbelianLimit.surjective_pow E.B hB m (Nat.one_le_iff_ne_zero.2 hm)
  haveI : LocallyOfFiniteType (((𝟙 E.B) ^ m : E.B ⟶ E.B).left ≫ E.B.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType ((𝟙 E.B) ^ m : E.B ⟶ E.B).left := locallyOfFiniteType_of_comp _ E.B.hom
  obtain ⟨p, hp⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ((𝟙 E.B) ^ m : E.B ⟶ E.B).left (x ≫ E.q).left
  let b' : 𝟙_ (Over (Sp k)) ⟶ E.B := Over.homMk p (by
    have := Over.w (x ≫ E.q)
    rw [hp, Category.assoc, Over.w] at this
    exact this)
  have hb' : b' ^ m = x ≫ E.q := by
    rw [← Category.comp_id b', ← MonObj.comp_pow]
    exact Over.OverMorphism.ext hp.symm

  haveI : LocallyOfFiniteType (E.q.left ≫ E.B.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType E.q.left := locallyOfFiniteType_of_comp _ E.B.hom
  haveI := E.q_surjective
  obtain ⟨p', hp'⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective E.q.left b'.left
  let g' : 𝟙_ (Over (Sp k)) ⟶ G := Over.homMk p' (by
    have := Over.w b'
    rw [hp', Category.assoc, Over.w] at this
    exact this)
  have hg' : g' ≫ E.q = b' := Over.OverMorphism.ext hp'.symm

  let qh := IsMonHom.monoidHom E.q (𝟙_ (Over (Sp k)))
  let ih := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hq : ∀ z, qh z = z ≫ E.q := fun _ => rfl
  have hi : ∀ z, ih z = z ≫ E.i := fun _ => rfl
  let h := x * (g' ^ m)⁻¹
  have hh : h ≫ E.q = 1 := by
    rw [← hq, map_mul, map_inv, map_pow, hq, hq, hg', hb', mul_inv_cancel]
  let s := E.isKernel.lift h (toUnit _) (by rw [hh, Hom.one_def])
  have hs : s ≫ E.i = h := E.isKernel.lift_fst _ _ _
  let e := splitTorusPointsEquiv (Sp k) E.X (𝟙_ (Over (Sp k)))
  obtain ⟨d, hd⟩ := GlobalTheory.TorsionLift.exists_char_root (Module.Free.chooseBasis ℤ E.X) m (e s)
    fun i => exists_root_unit m hm _
  refine ⟨e.symm d ≫ E.i * g', ?_⟩
  rw [mul_pow, ← hi, ← map_pow, ← map_pow, hd, MulEquiv.symm_apply_apply, hi, hs]
  exact inv_mul_cancel_right x (g' ^ m)

end GlobalTheory.SemiAbSurj

namespace GlobalTheory.SemiAbSurj

theorem surjective_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ m : ℕ, m ≠ 0 → Surjective ((𝟙 G) ^ m : G ⟶ G).left := by
  intro S G _ _ hG m hm
  have hfl := (GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow S G hG m hm).1
  haveI := hG.smooth
  refine ⟨fun x => ?_⟩
  let K := AlgebraicClosure (S.residueField (G.hom x))
  let t : Sp K ⟶ S := spMap (algebraMap (S.residueField (G.hom x)) K) ≫ S.fromSpecResidueField (G.hom x)
  have ht : G.hom x = t (IsLocalRing.closedPoint K) := (Scheme.fromSpecResidueField_apply _ _).symm
  let B := (Over.pullback t).obj G
  have hP := GlobalTheory.AbelianLimit.isPullback_pow (isGrpPullback_pullback G t) m
  haveI : LocallyOfFiniteType B.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom t))
  haveI : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  haveI : Flat ((𝟙 B) ^ m : B ⟶ B).left := MorphismProperty.of_isPullback hP hfl
  haveI : LocallyOfFiniteType (((𝟙 B) ^ m : B ⟶ B).left ≫ B.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType ((𝟙 B) ^ m : B ⟶ B).left := locallyOfFiniteType_of_comp _ B.hom
  haveI : LocallyOfFinitePresentation ((𝟙 B) ^ m : B ⟶ B).left := inferInstance
  obtain ⟨E⟩ := hG.fibres K t
  have hs : Surjective ((𝟙 B) ^ m : B ⟶ B).left := by
    refine surjective_of_rationalPoints _ fun y => ?_
    obtain ⟨z, hz⟩ := exists_pow_eq_of_torusExtension B E m hm y
    exact ⟨z, by rw [MonObj.comp_pow, Category.comp_id, hz]⟩
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback G.hom t) x _ ht
  obtain ⟨z, rfl⟩ := ((𝟙 B) ^ m : B ⟶ B).left.surjective y
  exact ⟨pullback.fst G.hom t z,
    (congrArg (fun g => g z) (GlobalTheory.AbelianLimit.pow_comm (isGrpPullback_pullback G t) m)).symm.trans hy⟩

end GlobalTheory.SemiAbSurj
end
end
