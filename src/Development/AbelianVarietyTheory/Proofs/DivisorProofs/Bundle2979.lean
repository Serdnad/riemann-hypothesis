module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle053
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle153
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawCommutativityValue
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.HTWeilLocus

open GlobalTheory.CechPic GlobalTheory.DiagPairing

section Root

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_weilIs_root {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (M : ℕ) (T : Over S) (x y : T ⟶ o.A) (hM : 0 < M)
    (hx : x ^ M = 1) (hy : y ^ M = 1) :
    ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ M = 1 ∧ Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M x y c₀ := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ o.A), pc o.isLB (x * x') y = pc o.isLB x y + pc o.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), pc o.isLB x (y * y') = pc o.isLB x y + pc o.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : T ⟶ o.A, z ^ M = 1 → ∀ q : T.left, ∃ V : T.left.Opens, q ∈ V ∧
      ∃ θ : Out.ThetaGrp o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M (Out.overRes V),
        θ.pt = Out.overResι V ≫ z := fun z hz q => by
    obtain ⟨θ, hθ⟩ := exists_theta_diag o.isLB hB hB' (k := M) (Out.overResι ⊤ ≫ z)
      (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
    exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG o.ab hD (lifts x hx) (lifts y hy)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG o.ab hD (lifts 1 (one_pow M)) (lifts y hy)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG o.ab hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG o.ab hD h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M (x ^ (m + 1)) y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ c₀ (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG o.ab hD ih hc₀
  have hp := pw (M - 1)
  rw [Nat.sub_add_cancel hM, hx] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG o.ab hD hp (e₁' ▸ hc₁), hc₀⟩

end Root

end GlobalTheory.HTWeilLocus

namespace GlobalTheory.HTWeilLocus

open GlobalTheory.LevCover

theorem weil_locus_clopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Z : Over S) (t₁ : Z.left ⟶ Sp (cycAway M)) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) → ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))) := by
  intro p _ D R _ b N h M hM hMp S t o Z t₁ e hadd hpow
  have hG : Out.GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hLB : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hMZ : IsUnit (M : Γ(Z.left, ⊤)) := by
    have := (b.unit M hMp).map (fnOn (Z.hom ≫ t))
    rwa [map_natCast] at this
  let ζu : (cycAway M)ˣ := Units.ofPowEqOne (zetaAway M) M (zetaAway_pow_self M hM.ne') hM.ne'
  have hζv : (ζu : cycAway M) = zetaAway M := Units.val_ofPowEqOne _ _ _ _
  have hζM : ∀ (k : Type) [Field k] (β : cycAway M →+* k), Units.map β.toMonoidHom ζu ^ M = 1 := fun k _ β => by
    rw [← map_pow, Units.pow_ofPowEqOne, map_one]
  let P2 : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ℤ) → HkClopen.GeoCond Z.left := fun a c k _ _ x =>
    ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) →
      Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a)
        ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))
  have locPair : ∀ a c, HkClopen.Loc (P2 a c) := fun a c => by
    obtain ⟨v, hv, hW⟩ := exists_weilIs_root o M Z (e a) (e c) hM (hpow a) (hpow c)
    refine (GlobalTheory.loc_units_eq Z.left M v (Units.map (fnOn t₁).toMonoidHom (ζu ^ (2 * omegaStd a c))) hMZ hv
      fun k _ _ g => ?_).congr fun k _ _ g => ?_
    · obtain ⟨β, hβ⟩ := exists_spMap (g ≫ t₁)
      rw [map_fnOn _ g β hβ, ← GlobalTheory.SiegCover.unitOn_pow', map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hζM, one_zpow]
      exact GlobalTheory.SiegCover.unitOn_one'
    · have hW' := GlobalTheory.CommPairing.weilIs_pull hG o.ab hLB (Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) hW
      obtain ⟨β, hβ⟩ := exists_spMap (g ≫ t₁)
      have hu := map_fnOn _ g β hβ (ζu ^ (2 * omegaStd a c))
      rw [show Units.map β.toMonoidHom (ζu ^ (2 * omegaStd a c)) =
        Units.map β.toMonoidHom ζu ^ (2 * omegaStd a c) from map_zpow _ _ _] at hu
      have hzβ : ((Units.map β.toMonoidHom ζu : kˣ) : k) = β (zetaAway M) := by
        rw [Units.coe_map]; exact congrArg β hζv
      constructor
      · intro E β' z hβ' hz
        obtain rfl : β = β' := spMap_inj' (hβ.symm.trans hβ')
        obtain rfl : z = Units.map β.toMonoidHom ζu := Units.ext (hz.trans hzβ.symm)
        rw [← hu, ← E]
        exact hW'
      · intro H
        exact GlobalTheory.CommutatorPairing.weilIs_unique hG o.ab hLB hW' (hu ▸ H β _ hβ hzβ)
  have e1 : ∀ a c, e (a + M • c) = e a := fun a c => by
    rw [hadd, add_map_nsmul hadd, hpow, _root_.mul_one]
  have inv : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) (a a' c₁ c₂ : Fin h ⊕ Fin h → ℤ),
      P2 a a' k g → P2 (a + M • c₁) (a' + M • c₂) k g := by
    intro k _ _ g a a' c₁ c₂ H β z hβ hz
    rw [e1, e1]
    have hzM : z ^ M = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hz, ← map_pow, zetaAway_pow_self M hM.ne', map_one, Units.val_one])
    obtain ⟨m, hm⟩ : ∃ m : ℤ, omegaStd (a + M • c₁) (a' + M • c₂) = omegaStd a a' + M * m :=
      ⟨_, GlobalTheory.SiegCover.omegaStd_add_nsmul M a a' c₁ c₂⟩
    have hz' : z ^ (2 * omegaStd (a + M • c₁) (a' + M • c₂)) = z ^ (2 * omegaStd a a') := by
      rw [hm, mul_add, zpow_add, show (2 : ℤ) * (M * m) = M * (2 * m) by ring, zpow_mul _ (M : ℤ), zpow_natCast,
        hzM, one_zpow, _root_.mul_one]
    rw [hz']
    exact H β z hβ hz
  obtain ⟨κ, hκ, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) hM
  haveI := hκ
  let r : κ → (Fin h ⊕ Fin h → ℤ) := Function.invFun q
  have localization₂ : HkClopen.Loc (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) => ∀ a a', P2 a a' k g) := by
    refine (HkClopen.Loc.all (I₀ := κ × κ) (P := fun i => P2 (r i.1) (r i.2)) fun i => locPair _ _).congr
      fun k _ _ g => ⟨fun H a a' => ?_, fun H i => H _ _⟩
    obtain ⟨c₁, e₁⟩ := hq (r (q a)) a (Function.invFun_eq ⟨a, rfl⟩)
    obtain ⟨c₂, e₂⟩ := hq (r (q a')) a' (Function.invFun_eq ⟨a', rfl⟩)
    rw [e₁, e₂]
    exact inv k g _ _ c₁ c₂ (H (q a, q a'))
  exact localization₂.congr fun k _ _ x =>
    ⟨fun H β z hβ hz a c => H a c β z hβ hz, fun H a c β z hβ hz => H β z hβ hz a c⟩

end GlobalTheory.HTWeilLocus
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BaseTransl

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
  {g : G'.left ⟶ G.left}

theorem toBase_injective (hg : IsPullback g G'.hom G.hom f) {T : Over S'} {x x' : T ⟶ G'}
    (h : toBase hg.w x = toBase hg.w x') : x = x' := by
  have e : x.left ≫ g = x'.left ≫ g := congrArg (fun z => z.left) h
  ext
  exact hg.hom_ext e (by rw [Over.w x, Over.w x'])

theorem toBase_one (hg : IsPullback g G'.hom G.hom f)
    (hm : ∀ (T : Over S') (x y : T ⟶ G'), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) (T : Over S') :
    toBase hg.w (1 : T ⟶ G') = 1 := by
  have := hm T 1 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

theorem isGrpPullback_of_toBase (hg : IsPullback g G'.hom G.hom f)
    (hm : ∀ (T : Over S') (x y : T ⟶ G'), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) :
    IsGrpPullback G' G f g := by
  refine ⟨hg, fun T x y x₀ y₀ hx hy => ?_⟩
  have ex : x₀ = toBase hg.w x := by ext; exact hx
  have ey : y₀ = toBase hg.w y := by ext; exact hy
  rw [ex, ey, ← hm]
  rfl


open GlobalTheory.RigidTranslate in
theorem exists_baseChange_translate : ∀ (K K' : Type) [Field K] [Field K'] (io : K →+* K') (A : PolAV (Sp K)) (y : Over.mk (spMap io) ⟶ A.A), y * y = 1 → ∃ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (t : 𝟙_ (Over (Sp K')) ⟶ A₁.A), IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ t.left ≫ α₁ = y.left ∧ LBIso A₁.L (GlobalTheory.RigidTranslate.rigTransl (A.L.pull α₁) t) := by
  intro K K' _ _ io A y hy
  obtain ⟨P, g, hg, -, hm, w, hw⟩ := GlobalTheory.polBaseChange_holds (Sp K) (Sp K') (spMap io) A
  have hpb : IsGrpPullback P.A A.A (spMap io) g := isGrpPullback_of_toBase hg hm
  have := P.isAb.comm
  have := P.isAb.proper
  have := A.isAb.comm
  let t₀ : 𝟙_ (Over (Sp K')) ⟶ P.A := Over.homMk (hg.lift y.left (𝟙 _) (by rw [Over.w y, Category.id_comp]; rfl))
    (hg.lift_snd _ _ _)
  have ht₀ : t₀.left ≫ g = y.left := hg.lift_fst _ _ _
  let e : Over.mk ((𝟙_ (Over (Sp K'))).hom ≫ spMap io) ⟶ Over.mk (spMap io) := Over.homMk (𝟙 _) (Category.id_comp _)
  have hte : toBase hg.w t₀ = e ≫ y := by
    ext
    exact ht₀.trans (Category.id_comp _).symm
  have htt : t₀ * t₀ = 1 := by
    refine toBase_injective hg ?_
    rw [hm, hte, toBase_one hg hm, ← MonObj.comp_mul, hy, MonObj.comp_one]
  have hwL : LBIso (A.L.pull g) P.L := ⟨w, hw⟩
  obtain ⟨c, hc⟩ := GlobalTheory.Moduli.cube_of_isLB _ P P.L P.isLB
  let A₁ : PolAV (Sp K') :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := rigTransl P.L t₀
      isLB := DVR.linComb_isLB _ P.isLB _ _
      rigid := rigidified_rigTransl P.isLB
      sym := sym_rigTransl htt P.isLB P.sym
      ample := relAmple_rigTransl htt P.isLB P.ample
      ktriv := kTriv_rigTransl htt P.isLB P.ktriv }
  obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ A.A P.A g hpb
  have hLamA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hLamP : (abelian₂ P.A P.L).IsLB := DVR.linComb_isLB _ P.isLB _ _
  have h3 := hlam A.L P.L _ (abelian₂ A.A A.L) (𝟙 _) A.isLB P.isLB hLamA hwL.symm (GlobalTheory.DescendedPrincipal.lbIso_pull_id hLamA).symm
  rw [Category.comp_id] at h3
  have h1 : LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ P.A P.L).pull (𝟙 _)) := lam_rigTransl P.isLB c hc
  refine ⟨A₁, g, β₂, t₀, hpb, hsq, ?_, ht₀, GlobalTheory.PelPrim.lbIso_linComb hwL.symm _ _⟩
  exact LBIso.trans (DVR.linComb_isLB _ A₁.isLB _ _) (pull_isLB hLamP _) (pull_isLB hLamA _) h1
    (LBIso.trans (pull_isLB hLamP _) hLamP (pull_isLB hLamA _) (GlobalTheory.DescendedPrincipal.lbIso_pull_id hLamP) h3)

end GlobalTheory.BaseTransl
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Conj

variable {R : Type} [CommRing R] [IsDomain R]

theorem spMap_jFK (σ : Kb R →ₐ[FractionRing R] Kb R) :
    spMap σ.toRingHom ≫ jFK (R := R) (Kb R) = jFK (R := R) (Kb R) := by
  rw [spMap, jFK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact σ.comp_algebraMap

def twK (σ : Kb R →ₐ[FractionRing R] Kb R) : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (spMap σ.toRingHom) (spMap_jFK σ)

@[simp] theorem twK_left (σ : Kb R →ₐ[FractionRing R] Kb R) : (twK σ).left = spMap σ.toRingHom := rfl

def mTw (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    TFK (R := R) (Kb R) ⊗ A.A ⟶ TFK (R := R) (Kb R) ⊗ A.A :=
  lift (fst _ _ ≫ twK σ) (snd _ _)

theorem mTw_fst (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    mTw A σ ≫ fst _ _ = fst _ _ ≫ twK σ := lift_fst _ _

theorem mTw_snd (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    mTw A σ ≫ snd _ _ = snd _ _ := lift_snd _ _

theorem mTw_fst_left (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    (mTw A σ).left ≫ (fst (TFK (R := R) (Kb R)) A.A).left =
      (fst (TFK (R := R) (Kb R)) A.A).left ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  rw [← Over.comp_left, mTw_fst, Over.comp_left]; rfl

theorem mTw_snd_left (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    (mTw A σ).left ≫ (snd (TFK (R := R) (Kb R)) A.A).left = (snd (TFK (R := R) (Kb R)) A.A).left := by
  rw [← Over.comp_left, mTw_snd]

def secTw (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N :=
  GlobalTheory.FieldBaseChange.pullOver (π := (fst (TFK (R := R) (Kb R)) A.A).left) (π' := (fst (TFK (R := R) (Kb R)) A.A).left)
    A.L (fun _ : Fin 1 => (N : ℤ)) (mTw_fst_left A σ) (fun _ => (mTw_snd_left A σ).symm) t

def TwF (σ : Kb R →ₐ[FractionRing R] Kb R) : Type := Kb R

instance (σ : Kb R →ₐ[FractionRing R] Kb R) : Field (TwF σ) := inferInstanceAs (Field (Kb R))
instance (σ : Kb R →ₐ[FractionRing R] Kb R) : Algebra (FractionRing R) (TwF σ) :=
  inferInstanceAs (Algebra (FractionRing R) (Kb R))
instance (σ : Kb R →ₐ[FractionRing R] Kb R) : Algebra (Kb R) (TwF σ) := σ.toRingHom.toAlgebra
instance (σ : Kb R →ₐ[FractionRing R] Kb R) : IsScalarTower (FractionRing R) (Kb R) (TwF σ) :=
  IsScalarTower.of_algebraMap_eq fun r => (σ.commutes r).symm

def famTw (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s : Fam D (Kb R) N) : Fam D (Kb R) N :=
  (GlobalTheory.FieldBaseChange.famPull D (Kb R) (TwF σ) GlobalTheory.allSixLaws.1.globalFns N s : Fam D (TwF σ) N)

def genCast {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ} (h : φ = φ')
    (t : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ' ε) :=
  h ▸ t

theorem genCast_isGen {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) : (genCast h t).IsGen := by
  subst h; exact ht

theorem val_genCast {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (genCast h t) r z J = val t r z J := by
  subst h; rfl

theorem thetaφ_mTw (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (x : TFK (R := R) (Kb R) ⟶ A.A) :
    (fun i => (mTw A σ).left ≫ (![(snd (TFK (R := R) (Kb R)) A.A).left, (translPt A.A x).left] : Fin 2 → _) i) =
      ![(snd (TFK (R := R) (Kb R)) A.A).left, (translPt A.A (twK σ ≫ x)).left] := by
  funext i
  fin_cases i
  · exact mTw_snd_left A σ
  · show (mTw A σ).left ≫ (translPt A.A x).left = (translPt A.A (twK σ ≫ x)).left
    rw [← Over.comp_left, translPt, translPt, ← Category.assoc, comp_lift, ← Category.assoc, mTw_fst, mTw_snd,
      Category.assoc]

def thTw (A : PolAV (Sp (FractionRing R))) (k : ℤ) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (θ : ThetaGrp A.A A.L k (TFK (R := R) (Kb R))) : ThetaGrp A.A A.L k (TFK (R := R) (Kb R)) where
  pt := twK σ ≫ θ.pt
  φ := genCast (thetaφ_mTw A σ θ.pt) (LB.pullGen A.L _ _ θ.φ (mTw A σ).left)
  isGen := genCast_isGen _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen A.L _ _ θ.φ θ.isGen _)

theorem spMap_jFKR (σ : Kb R →ₐ[FractionRing R] Kb R) :
    spMap σ.toRingHom ≫ (jFK (R := R) (Kb R) ≫ jK R) = jFK (R := R) (Kb R) ≫ jK R := by
  rw [← Category.assoc, spMap_jFK]

def twF (σ : Kb R →ₐ[FractionRing R] Kb R) : TF (R := R) (Kb R) ⟶ TF (R := R) (Kb R) :=
  Over.homMk (spMap σ.toRingHom) (spMap_jFKR σ)

theorem lineφ_tw (D : DegPre R) {N : ℕ} (τ : Kb R →ₐ[FractionRing R] Kb R) {p p₀ : QkPt D (Kb R) N}
    (h : QkExt τ.toRingHom p p₀) :
    (fun k => spMap τ.toRingHom ≫ DegPre.lineφ D (Kb R) p.g.b k) = DegPre.lineφ D (Kb R) p₀.g.b := by
  funext k
  fin_cases k
  · show (twF τ).left ≫ (toUnit _ ≫ η[D.P.A]).left = (toUnit _ ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  · exact h.2.1.symm

def frTw (D : DegPre R) {N : ℕ} (τ : Kb R →ₐ[FractionRing R] Kb R) {p p₀ : QkPt D (Kb R) N}
    (h : QkExt τ.toRingHom p p₀) (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) : GlobalTheory.UT.Frm D (Kb R) N p₀.g.b :=
  genCast (lineφ_tw D τ h) (LB.pullGen D.P.L _ _ w (spMap τ.toRingHom))

end GlobalTheory.Mum.Conj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : F →+* F) (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F) (g : GtPtF D F), spMap σ ≫ g.b.left = g.b.left → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → GlobalTheory.TorusExt.gtExt D σ hσ g = g := by
  first | exact @GlobalTheory.TorusExt.gtExt_eq_self_of_charVal_fixed | exact GlobalTheory.TorusExt.gtExt_eq_self_of_charVal_fixed | (intros; apply GlobalTheory.TorusExt.gtExt_eq_self_of_charVal_fixed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.FieldBaseChange

def basisOfIsExtension {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) {I : Type}
    (B : Module.Basis I K V) : Module.Basis I F W :=
  Module.Basis.mk (GlobalTheory.ConstFam.linearIndependent_of_isExtension ha B.linearIndependent) (by
    have h : Submodule.span K (Set.range B) ≤
        Submodule.comap a (Submodule.span F (Set.range fun i => a (B i))) :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩)
    rw [← ha.span, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (Set.range B) := B.span_eq ▸ Submodule.mem_top
    exact h hv)

theorem basisOfIsExtension_apply {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) {I : Type}
    (B : Module.Basis I K V) (i : I) : basisOfIsExtension ha B i = a (B i) := by
  simp [basisOfIsExtension]

theorem exists_bijective_extension : ∀ (K F V V' W W' : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W'] (a : V →ₛₗ[algebraMap K F] W) (d : V' →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension a → GlobalTheory.FieldBaseChange.IsExtension d → ∀ e : V →ₗ[K] V', Function.Bijective e → ∃ e' : W →ₗ[F] W', Function.Bijective e' ∧ ∀ v, e' (a v) = d (e v) := by
  intro K F V V' W W' _ _ _ _ _ _ _ _ _ _ _ a d ha hd e he
  let B := Module.Basis.ofVectorSpace K V
  let B' := B.map (LinearEquiv.ofBijective e he)
  let C := basisOfIsExtension ha B
  let C' := basisOfIsExtension hd B'
  let E := C.equiv C' (Equiv.refl _)
  refine ⟨E.toLinearMap, E.bijective, fun v => ?_⟩
  have key : (E.toLinearMap.comp a : V →ₛₗ[algebraMap K F] W') = d.comp e := B.ext fun i => by
    have h1 : a (B i) = C i := (basisOfIsExtension_apply ha B i).symm
    have h2 : d (e (B i)) = C' i := by
      rw [basisOfIsExtension_apply hd B' i]; simp [B']
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, h2, E, Module.Basis.equiv_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun key v

end GlobalTheory.FieldBaseChange
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.quotientPoint_characterValue_pow_isUnit : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → (∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F)) → ∀ (k : ℕ) (p : QkPt D F k) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = p.g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal p.g χ (closedPoint F) J) : F) ^ k = ((u : T) : F) := by
  first | exact @GlobalTheory.UnramCharPow.charVal_pow_unit | exact GlobalTheory.UnramCharPow.charVal_pow_unit | (intros; apply GlobalTheory.UnramCharPow.charVal_pow_unit <;> assumption)
end
