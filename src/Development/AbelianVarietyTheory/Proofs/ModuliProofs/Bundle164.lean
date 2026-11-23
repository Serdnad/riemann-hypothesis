module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle073
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelCoverField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle030
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_toric_torsion_cubWeil_one : Out.Laws3 → ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L : RigLB G) (c : CubicalStr G L) (g N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), SmoothOfRelativeDimension g G.hom → (N : k) ≠ 0 → ∃ T : Set (Over.mk x ⟶ G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ y : Over.mk x ⟶ G, y ^ N = 1 → CubWeil c N τ y 1) ∧ Nat.card {p : Over.mk x ⟶ G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  intro h3 X G _ _ hG L c g N k _ _ x dG hN
  let G' : Over (Sp k) := (Over.pullback x).obj G
  have hp : IsGrpPullback G' G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback x G hG
  have := hG'.comm
  have := hG'.smooth
  have := hG'.geomConnected
  have dG' : SmoothOfRelativeDimension g G'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 dG
  obtain ⟨E⟩ := hG.fibres k x
  let := E.addCommGroup
  let := E.grpB
  have := E.free
  have := E.finite
  have := E.i_hom
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := h3.cubePull _ _ G G' (cubeMapOf hp) L c
  obtain ⟨σ⟩ := GlobalTheory.BiextTriv.main k E.X G' _ c' E.i E.i_hom
  have hw : pullback.fst G.hom x ≫ G.hom = G'.hom ≫ x := pullback.condition
  let U : Over (Sp k) := 𝟙_ (Over (Sp k))
  let ρ : Over.mk x ⟶ Over.mk (U.hom ≫ x) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk x ⟶ G) := (preHom ρ).comp (toBaseHom (toBase_mul_pullback G x) U)
  have hφ : ∀ a : U ⟶ G', (φ a).left = a.left ≫ pullback.fst G.hom x := fun a => Category.id_comp _
  have hb : Function.Bijective φ := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hφ, ← hφ, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm))
        (pullback.lift_snd _ _ _), Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  let e := MulEquiv.ofBijective φ hb
  have he : ∀ a : U ⟶ G', e a ^ N = 1 ↔ a ^ N = 1 := fun a => by rw [← map_pow, e.map_eq_one_iff]
  have hcount := GlobalTheory.card_torsion_mul_card_toric_torsion k G' E g N hG' dG' hN
  refine ⟨e '' {y | y ^ N = 1 ∧ ∃ t, y = t ≫ E.i}, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact (he a).2 ha
  · rintro _ ⟨_, ⟨ha, t, rfl⟩, rfl⟩ y hy
    obtain ⟨b, rfl⟩ := e.surjective y
    have ht : t ^ N = 1 := E.isKernel.hom_ext
      (by rw [MonObj.pow_comp, ha, MonObj.one_comp]) (toUnit_unique _ _)
    have h1 := σ.cubWeil ht ((he b).1 hy)
    have h2 := (GlobalTheory.UU.cubWeil_of_isPullCubical _ _ x G G' (cubeMapOf hp) hw (toBase_mul_pullback G x) L _ c c' hc' N U _ _ _ h1).comp ρ
    rw [map_one] at h2
    exact h2
  · rw [← hcount]
    congr 1
    · exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun a => (he a).symm)).symm
    · exact Nat.card_image_of_injective e.injective _

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.MulRoot

open CechPic

theorem pull_pow_pol (h : Out.MulPullSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) (n : ℕ) :
    pull (𝟙 P.A ^ n : P.A ⟶ P.A).left (cls P.L P.isLB) = (n ^ 2) • cls P.L P.isLB := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 (h S P n)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, neg_smul, one_smul] at e
  rw [← natCast_zsmul, Nat.cast_pow]
  exact (add_neg_eq_zero.1 e).symm

theorem pull_inv_pol (h : Out.MulPullSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S)
    (hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen) :
    pull ((𝟙 P.A)⁻¹ : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
  have := P.isAb.comm
  have h₀ := pull_pow_pol h P 0
  have h₂ := pull_pow_pol h P 2
  have e := lam_mul_left P.isLB hΘ (𝟙 P.A) (𝟙 P.A)⁻¹ (𝟙 P.A)
  rw [mul_inv_cancel, lam_one_left] at e
  rw [pow_zero] at h₀
  rw [pow_two (𝟙 P.A)] at h₂
  simp only [lam, inv_mul_cancel, h₀, h₂, Over.id_left, pull_id] at e
  linear_combination (norm := module) e

theorem lam_eq_zero (laws : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K))
    {D : LB P.A.left} (hD : D.IsLB) (hΘ : ∃ t : LB.Gen (Theta P.A D), t.IsGen) {m : ℕ} (hm : 0 < m)
    (h : pull (𝟙 P.A ^ m : P.A ⟶ P.A).left (cls D hD) = 0) {T : Over (Sp K)} (x y : T ⟶ P.A) :
    lam (cls D hD) x y = 0 := by
  have := P.isAb.comm
  have := P.isAb.smooth
  have kill : ∀ {T : Over (Sp K)} (x : T ⟶ P.A), pull (x ^ m).left (cls D hD) = 0 := fun x => by
    have e : x ^ m = x ≫ 𝟙 P.A ^ m := by rw [MonObj.comp_pow, Category.comp_id]
    rw [e, Over.comp_left, pull_comp, h, map_zero]
  have two : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A), lam (cls D hD) (x ^ (m * m)) y = 0 := fun {T} x y => by
    rw [pow_mul, lam_pow_left hD hΘ, ← lam_pow_right hD hΘ]
    have k₁ := kill (1 : T ⟶ P.A)
    rw [one_pow] at k₁
    rw [lam, ← mul_pow, kill, kill, kill, k₁]
    simp
  have hN : (cubeLB P.A ![fst P.A P.A, snd P.A P.A] D).IsLB := LB.isLB_linComb hD _ _
  have val : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A),
      cls _ (pull_isLB hN (lift x y).left) = lam (cls D hD) x y := fun x y => by
    rw [cls_pull hN, cls_cube_two hD, pull_lam, lift_fst, lift_snd]
  have gen : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A), lam (cls D hD) x y = 0 →
      ∃ s : ((cubeLB P.A ![fst P.A P.A, snd P.A P.A] D).pull (lift x y).left).Gen, s.IsGen := fun x y e =>
    (cls_eq_zero_iff _).1 ((val x y).trans e)
  have main := GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian laws.globalFns K P.A P.A _ P.L P.isAb P.isAb P.isLB P.ample hN
    (gen _ _ (lam_one_left _ _)) (by
      have hs : Surjective (𝟙 P.A ^ (m * m)).left := (laws.mulN _ P (m * m) (Nat.mul_pos hm hm)).2.2.1
      refine dense_image_points (𝟙 P.A ^ (m * m)) _ fun u => gen _ _ ?_
      rw [MonObj.comp_pow, MonObj.comp_pow]
      exact two _ _) (gen _ _ (lam_one_right _ _))
  rw [← val, cls_pull hN, (cls_eq_zero_iff hN).2 main, map_zero]

end GlobalTheory.MulRoot

namespace GlobalTheory

open CechPic MulRoot

theorem pol_iso_symmetrised_root : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (m : ℕ), Odd m → N.IsLB → LBIso (lbPow P.L (m ^ 2)) (N.pull ((𝟙 P.A) ^ m).left) → LBIso P.L (LB.LinComb N (K := Fin 2) ![𝟙 P.A.left, (GrpObj.inv : P.A ⟶ P.A).left] ![(1 - (m : ℤ)) / 2, ((m : ℤ) + 1) / 2]) := by
  intro laws cube K _ _ P N m hm hN hiso
  have := P.isAb.comm
  have hL := P.isLB
  have hD : (LB.div N P.L).IsLB := LB.isLB_div hN hL
  have hd : cls _ hD = cls N hN - cls P.L hL := cls_div hN hL hD
  have h₁ : pull (𝟙 P.A ^ m : P.A ⟶ P.A).left (cls _ hD) = 0 := by
    have e := (cls_eq_iff (LB.isLB_linComb hL _ _) (pull_isLB hN _)).2 hiso
    rw [cls_lbPow hL, cls_pull hN] at e
    rw [hd, map_sub, ← e, pull_pow_pol laws.mulPull, sub_self]
  have hlam := fun x y : P.A ⟶ P.A => lam_eq_zero laws P hD (cube _ P _ hD) hm.pos h₁ x y
  have h₀ : pull (1 : P.A ⟶ P.A).left (cls _ hD) = 0 := by
    have e : (1 : P.A ⟶ P.A) = 1 ≫ 𝟙 P.A ^ m := by rw [MonObj.comp_pow, Category.comp_id, one_pow]
    rw [e, Over.comp_left, pull_comp, h₁, map_zero]
  have hadd : ∀ x y : P.A ⟶ P.A, pull (x * y).left (cls _ hD) = pull x.left (cls _ hD) + pull y.left (cls _ hD) :=
    fun x y => by
      have e := hlam x y
      rw [lam, h₀] at e
      linear_combination (norm := module) e
  have hpow : ∀ n : ℕ, pull (𝟙 P.A ^ n : P.A ⟶ P.A).left (cls _ hD) = n • cls _ hD := fun n => by
    induction n with
    | zero => rw [pow_zero, h₀, zero_nsmul]
    | succ n ih => rw [pow_succ, hadd, ih, Over.id_left, pull_id, succ_nsmul]
  have hmd : m • cls _ hD = 0 := (hpow m).symm.trans h₁
  have hinv := hadd (𝟙 P.A) (𝟙 P.A)⁻¹
  rw [mul_inv_cancel, h₀, Over.id_left, pull_id] at hinv
  have hsym := pull_inv_pol laws.mulPull P (cube _ P _ hL)
  have ei : ((𝟙 P.A)⁻¹ : P.A ⟶ P.A) = GrpObj.inv := Category.id_comp _
  rw [ei] at hinv hsym
  rw [hd, map_sub, hsym] at hinv
  rw [hd] at hmd
  obtain ⟨k, rfl⟩ := hm
  have a : (1 - ((2 * k + 1 : ℕ) : ℤ)) / 2 = -k := by push_cast; omega
  have b : (((2 * k + 1 : ℕ) : ℤ) + 1) / 2 = k + 1 := by push_cast; omega
  rw [← cls_eq_iff hL (LB.isLB_linComb hN _ _), cls_linComb hN, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, a, b]
  linear_combination (norm := module) ((k : ℤ) + 1) • hinv + hmd

end GlobalTheory
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open PairingDetermines IsoDescent PrimCocycle

theorem lam_iso_of_weil_pairings : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left)) := by
  intro hL k _ _ P P' α p d hα hp _ hW
  haveI : IsCommMonObj P.A := P.isAb.comm
  have fib : ∀ (x : 𝟙_ (Over (Sp k)) ⟶ P.A) (n : ℕ), 0 < n → n.Coprime p → x ^ n = 1 →
      ∃ t : LB.Gen ((LB.div (abelian₂ P.A (P'.L.pull α.left)) (abelian₂ P.A (lbPow P.L d))).pull
        (lift (toUnit P.A ≫ x) (𝟙 P.A)).left), t.IsGen := by
    intro x n hn hnp hx
    obtain ⟨u, hu, v⟩ := exists_gen_lam hL.globalFns hL.cube P (𝟙 P.A) d n x hx
    obtain ⟨u', hu', v'⟩ := exists_gen_lam hL.globalFns hL.cube P' α 1 n x hx
    refine exists_gen_div_pull P.L P'.L (𝟙 _) α.left d 1 (lamφ P.A) lamε _ ?_
    refine lbIso_of_invariant P.isLB P'.isLB _ _ _ _ (Out.mulA P.A n).left
      (I := {y : 𝟙_ (Over (Sp k)) ⟶ P.A // y ^ n = 1}) (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left) (fun y => ?_)
      (fun U f hf => torsion_invariant_descends (fun S _ P n hn => by
        obtain ⟨a, b, c, e, -⟩ := hL.mulN S P n hn
        exact ⟨a, b, c, e⟩) k P n (Nat.cast_ne_zero.2 hn.ne') U f fun y hy => hf ⟨y, hy⟩) u hu u' hu'
      (fun y z J J' hJ hJ' => ?_)
    · rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, y.2,
        MonObj.comp_one, _root_.one_mul]
    · obtain ⟨c, hc, -⟩ := (hL.weil _ P n _).1 x y.1 hx y.2
      obtain ⟨c, rfl⟩ : ∃ c₀ : kˣ, unitOn c₀ = c :=
        ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c,
          Units.ext ((Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply c.val)⟩
      have e : unitOn (c ^ d) = unitOn c ^ d := map_pow (Units.map _) c d
      have h₁ := v y.1 (unitOn c) y.2 (by rw [Category.comp_id, Category.comp_id]; exact hc) z J hJ
      have h₂ := v' y.1 (unitOn (c ^ d)) y.2 (hW n x y.1 c hn hnp hx y.2 hc) z J' hJ'
      rw [pow_one, e] at h₂
      refine (congrArg₂ (fun a b => a * b⁻¹) h₂ h₁).trans ?_
      exact mul_div_mul_right_eq_div _ _ _ |> fun h => by simpa only [div_eq_mul_inv] using h
  refine T.seesaw_triviality_on_dense_fibres_product_abelian hL.globalFns k P.A P.A (LB.div (abelian₂ P.A (P'.L.pull α.left)) (abelian₂ P.A (lbPow P.L d))) P.L
    P.isAb P.isAb P.isLB P.ample
    (LB.isLB_div (DVR.linComb_isLB _ (LB.isLB_pull P'.isLB _) _ _)
      (DVR.linComb_isLB _ (DVR.linComb_isLB _ P.isLB _ _) _ _)) ?_ ?_ ?_
  · have := fib 1 1 one_pos (Nat.coprime_one_left p) (one_pow _)
    rwa [MonObj.comp_one] at this
  · refine (CoprimeTorsion.dense_torsion hL.ample hL.kerPow hL.irred k P hp).mono ?_
    exact Set.biUnion_subset_biUnion_left fun x ⟨n, hn, hnp, hx⟩ => fib x n hn hnp hx
  · obtain ⟨u, hu⟩ := exists_gen_axis (A := P.A) P.isLB (𝟙 _) d
    obtain ⟨u', hu'⟩ := exists_gen_axis (A := P.A) P'.isLB α.left 1
    exact exists_gen_div_pull P.L P'.L (𝟙 _) α.left d 1 (lamφ P.A) lamε _
      (lbIso_of_gens P.isLB P'.isLB _ _ _ _ u hu u' hu')

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.CharZeroPts

theorem exists_generization {o : Type} [CommRing o] [IsDomain o] [CharZero o] {S : Scheme.{0}} (s : S ⟶ Sp o) [Flat s]
    (p : S) : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K),
      x ≫ s = spMap β ∧ ∀ u, x u ⤳ p := by
  let ξ : Sp o := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum o)
  have hξ : ξ ⤳ s p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨q, hq, hq'⟩ := Flat.generalizingMap s hξ
  obtain ⟨K, _, _, x, hx⟩ := FinEt.exists_algClosed_point S q
  have hx' : ∀ u, x u = q := fun u => by
    have : x u ∈ Set.range x := ⟨u, rfl⟩
    rwa [hx] at this
  let β : o →+* K := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  have hinj : Function.Injective β := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have e : spMap β (default : PrimeSpectrum K) = ξ := by
      rw [← hβ]
      exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg s (hx' _)).trans hq')
    have e' : a ∈ (spMap β (default : PrimeSpectrum K)).asIdeal := by
      show β a ∈ (default : PrimeSpectrum K).asIdeal
      rw [ha]; exact zero_mem _
    rw [e] at e'
    exact e'
  exact ⟨K, inferInstance, inferInstance, charZero_of_injective_ringHom hinj, x, β, hβ, fun u => (hx' u).symm ▸ hq⟩

variable {S : Scheme.{0}}

abbrev toB {T : Scheme.{0}} (x : T ⟶ S) : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)

theorem smoothOfRelativeDimension_of_generization {X : Scheme.{0}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f]
    (g : ℕ) (h : ∀ y : X, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ X), (∀ u, z u ⤳ y) ∧
      ∀ m, SmoothOfRelativeDimension m (pullback.snd f (z ≫ f)) → m = g) : SmoothOfRelativeDimension g f := by
  choose n W hW hd using H1.exists_dim f
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  obtain ⟨k, _, z, hz, hg⟩ := h y
  have : ConnectedSpace ↥(pullback f (z ≫ f)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (z ≫ f) _ _ (IsPullback.of_hasPullback _ _)
  let z' : Sp k ⟶ pullback f (z ≫ f) := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected (pullback.snd f (z ≫ f)) (z' (default : PrimeSpectrum k))
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst f (z ≫ f) = z := pullback.lift_fst _ _ _
    have e' := congrArg (fun q : Sp k ⟶ X => q (default : PrimeSpectrum k)) e
    exact (congrArg (fun u => u ∈ W y) e').mpr ((hz _).mem_open (W y).isOpen (hW y)))
  rw [← hg m hm, ← e₁]
  exact hd y

theorem weilIs_of_generization (hL : Out.Laws) (P : Out.PolAV S) (n : ℕ) (x y : Out.baseOver S ⟶ P.A) (c : Γ(S, ⊤)ˣ)
    (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤))) (hx : x ^ n = 1) (hy : y ^ n = 1) (hc : c ^ n = 1)
    (h : ∀ p : S, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ S), (∀ u, z u ⤳ p) ∧
      Out.WeilIs P.A P.L n (toB z ≫ x) (toB z ≫ y) (Units.map z.appTop.hom.toMonoidHom c)) :
    Out.WeilIs P.A P.L n x y c := by
  obtain ⟨U, hU, H⟩ := exists_clopen_weilIs_iff hL S P n (Out.baseOver S) x y c hn hu hx hy hc
  have := (H _ (𝟙 _)).2 (by
    rintro _ ⟨p, rfl⟩
    obtain ⟨K, _, z, hz, hw⟩ := h p
    exact (hz (default : PrimeSpectrum K)).mem_closed hU ((H _ (toB z)).1 hw ⟨_, rfl⟩))
  rw [Category.id_comp, Category.id_comp] at this
  convert this
  ext
  simp

theorem torsion_basis_of_generization (A : Over S) [GrpObj A] (k r : ℕ) (pt : Fin r → (Out.baseOver S ⟶ A))
    (hA : IsAbelianScheme A) (hk : 0 < k) (hu : IsUnit (k : Γ(S, ⊤))) (hpt : ∀ i, pt i ^ k = 1)
    (h : ∀ p : S, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ S), (∀ u, z u ⤳ p) ∧
      ∀ y : Over.mk z ⟶ A, y ^ k = 1 →
        ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB z ≫ pt i) (fun i => (c i).val) = y)
    (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A) (hy : y ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB x ≫ pt i) (fun i => (c i).val) = y := by
  let Sg : Set S := {p | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ S),
    p ∈ Set.range z ∧ ∀ y : Over.mk z ⟶ A, y ^ k = 1 →
      ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB z ≫ pt i) (fun i => (c i).val) = y}
  refine torsion_basis_of_dense S A k r pt Sg hA hk hu hpt ?_ (fun p hp => hp) K x y hy
  intro p
  obtain ⟨K, _, _, z, hz, H⟩ := h p
  exact (hz (default : PrimeSpectrum K)).mem_closed isClosed_closure
    (subset_closure ⟨K, inferInstance, inferInstance, z, ⟨_, rfl⟩, H⟩)

end GlobalTheory.CharZeroPts
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

private theorem isGrpPullback_pullback_obj {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback _ _, ?_⟩
  intro T x y x₀ y₀ hx hy
  have e : (lift x₀ y₀).left =
      (lift x y).left ≫ (Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫
        pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [Over.μ_pullback_left_fst_fst]
      simp only [Over.lift_left, pullback.lift_fst, pullback.lift_fst_assoc, hx]
    · simp only [Category.assoc]
      rw [Over.μ_pullback_left_fst_snd]
      simp only [Over.lift_left, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst_assoc, hy]
  rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, e, Functor.obj.μ_def, Over.comp_left]
  simp only [Category.assoc]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  first
    | exact (pullback.lift_fst _ _ _).symm
    | (erw [Over.pullback_map_left]; simp)

theorem kTriv_away_of_kTriv_fibre : Out.GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (K : Type) [Field K] (x : R →+* K), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Out.KTriv ((Over.pullback (spMap x)).obj A) (L.pull (pullback.fst A.hom (spMap x))) → ∃ f : R, x f ≠ 0 ∧ Out.KTriv ((Over.pullback (spMap (algebraMap R (Localization.Away f)))).obj A) (L.pull (pullback.fst A.hom (spMap (algebraMap R (Localization.Away f))))) := by
  intro _ R _ _ A _ L K _ x hA hL hR hK
  obtain ⟨f, hf, H⟩ := GlobalTheory.T.exists_basicOpen_kTriv_of_fibre R A L K x ((Over.pullback (spMap x)).obj A)
    (pullback.fst A.hom (spMap x)) hA hL hR (isGrpPullback_pullback_obj A (spMap x)) hK
  exact ⟨f, hf, H (Localization.Away f) (algebraMap R (Localization.Away f)) _ _
    (IsLocalization.Away.algebraMap_isUnit f) (isGrpPullback_pullback_obj A _)⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem finite_torsion_semiAbelian :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G → ∀ n : ℕ, 0 < n → Finite {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1} :=
  TorsionFinite.finite_torsion_semiAbelian_of_abelian AbTorsionFinite.finite_torsion

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

theorem levelCover_closed : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂ : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ :=
  fun hL => GlobalTheory.LevCover.levelCover_field hL GlobalTheory.LiePull.lieMult_pull GlobalTheory.pol_pull
    GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift
    GlobalTheory.tateIso_differ_by_similitude GlobalTheory.exists_finiteEtale_latticeTorsionHom
    (GlobalTheory.exists_clopen_weilIs_iff hL)
    (GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift)

end GlobalTheory.LevCover
end
