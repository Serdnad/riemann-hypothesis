module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem omegaStd_nsmul_left' {h : ℕ} (M : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    omegaStd (M • a) b = (M : ℤ) * omegaStd a b := by
  unfold omegaStd
  simp only [Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem omegaStd_single_inr {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (Sum.inr i) 1) = a (Sum.inl i) := by
  simp [omegaStd, Pi.single_apply]

theorem omegaStd_single_inl {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (Sum.inl i) 1) = -a (Sum.inr i) := by
  simp [omegaStd, Pi.single_apply]

theorem kappaOK_dvd_iff {h M d : ℕ} {κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)}
    (hκ : KappaOK h M d κ) (a : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    (∀ k, ∃ b, κ k a = M • b) ↔ ∃ b, a = M • b := by
  constructor
  · intro hk
    choose c hc using hk
    have hdiv : ∀ b, (M : ℤ) ∣ omegaStd a b := by
      intro b
      have h2 : (M : ℤ) ∣ formZ d h (fun k => κ k a) (fun k => κ k b) := by
        unfold formZ
        refine Finset.dvd_sum fun k _ => Finset.dvd_sum fun l _ => ?_
        dsimp only
        rw [hc k, omegaStd_nsmul_left']
        exact Dvd.intro (form d (sig k) (sig l) * omegaStd (c k) (κ l b)) (by ring)
      have := dvd_add (hκ.1 a b).dvd h2
      simpa using this
    have hx : ∀ x, (M : ℤ) ∣ a x := by
      rintro (i | i)
      · simpa [omegaStd_single_inr] using hdiv (Pi.single (Sum.inr i) 1)
      · simpa [omegaStd_single_inl] using hdiv (Pi.single (Sum.inl i) 1)
    exact ⟨fun x => a x / M, funext fun x => by simp [Int.mul_ediv_cancel' (hx x)]⟩
  · rintro ⟨b, rfl⟩ k
    exact ⟨κ k b, map_nsmul _ _ _⟩

theorem kappaOK_mod (h M d : ℕ) (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ))
    (hM : 1 ≤ M) (hκ : KappaOK h M d κ) :
    (∀ a, (∀ k, ∃ b, κ k a = M • b) ↔ ∃ b, a = M • b) ∧
      ∀ cc : Fin 8 → (Fin h ⊕ Fin h → ℤ), ∃ a, ∀ k, ∃ b, κ k a = cc k + M • b := by
  refine ⟨kappaOK_dvd_iff hκ, ?_⟩
  haveI : NeZero M := ⟨by omega⟩
  let f : (Fin (8 * h) ⊕ Fin (8 * h) → ZMod M) → (Fin 8 → Fin h ⊕ Fin h → ZMod M) :=
    fun x k j => ((κ k (fun i => ((x i).val : ℤ)) j : ℤ) : ZMod M)
  have hinj : Function.Injective f := by
    intro x y hxy
    let a : Fin (8 * h) ⊕ Fin (8 * h) → ℤ := fun i => ((x i).val : ℤ) - ((y i).val : ℤ)
    have hk : ∀ k, ∃ b, κ k a = M • b := by
      intro k
      have hj : ∀ j, (M : ℤ) ∣ κ k a j := by
        intro j
        have e := congrFun (congrFun hxy k) j
        simp only [f] at e
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have ha : a = (fun i => ((x i).val : ℤ)) - (fun i => ((y i).val : ℤ)) := rfl
        rw [ha, map_sub, Pi.sub_apply, Int.cast_sub, e, sub_self]
      exact ⟨fun j => κ k a j / M, funext fun j => by simp [Int.mul_ediv_cancel' (hj j)]⟩
    obtain ⟨b, hb⟩ := (kappaOK_dvd_iff hκ a).1 hk
    funext i
    have e := congrFun hb i
    have h2 : ((a i : ℤ) : ZMod M) = 0 := by rw [e]; simp
    simp [a] at h2
    exact sub_eq_zero.mp h2
  have hcard : Fintype.card (Fin (8 * h) ⊕ Fin (8 * h) → ZMod M) =
      Fintype.card (Fin 8 → Fin h ⊕ Fin h → ZMod M) := by
    simp only [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin, ZMod.card]
    rw [← pow_mul]
    congr 1
    ring
  have hbij := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  intro cc
  obtain ⟨x, hx⟩ := hbij.2 (fun k j => (cc k j : ZMod M))
  refine ⟨fun i => ((x i).val : ℤ), fun k => ?_⟩
  have hj : ∀ j, (M : ℤ) ∣ κ k (fun i => ((x i).val : ℤ)) j - cc k j := by
    intro j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
    have e := congrFun (congrFun hx k) j
    simp only [f] at e
    rw [e, sub_self]
  refine ⟨fun j => (κ k (fun i => ((x i).val : ℤ)) j - cc k j) / M, funext fun j => ?_⟩
  rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Int.mul_ediv_cancel' (hj j)]
  ring

end GlobalTheory.ZarhinFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam.LevCoord

section Coord

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  simp only [mkZ, pa, lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  simp only [mkZ, pb, lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem zob_hom_ext {T : Over S} (f g : T ⟶ Zob A B) (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · apply (Out.powIsLimit A 4).hom_ext
    rintro ⟨i⟩
    simpa [pa] using ha i
  · apply (Out.powIsLimit B 4).hom_ext
    rintro ⟨j⟩
    simpa [pb] using hb j

instance pa_isMonHom (i : Fin 4) : IsMonHom (pa A B i) := by
  unfold pa; infer_instance

instance pb_isMonHom (j : Fin 4) : IsMonHom (pb A B j) := by
  unfold pb; infer_instance

end Coord

theorem oMat_apply (d : ℕ) (k : Fin 8) (p q : Fin 4 ⊕ Fin 4) :
    ((oMat d k : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) p q =
      if Sum.inl 0 = p ∧ sig k = q then 1 else 0 := by
  simp [oMat, Matrix.single_apply]

theorem sig_eq_inl (k : Fin 8) (i : Fin 4) : sig k = Sum.inl i ↔ Fin.castAdd 4 i = k := by
  fin_cases k <;> fin_cases i <;> simp [sig] <;> decide

theorem sig_eq_inr (k : Fin 8) (j : Fin 4) : sig k = Sum.inr j ↔ Fin.natAdd 4 j = k := by
  fin_cases k <;> fin_cases j <;> simp [sig] <;> decide

section Key

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem incZ_pa (j : Fin 4) : incZ A B ≫ pa A B j = if j = 0 then 𝟙 A else 1 := by
  simp [incZ, mkZ_pa]

theorem incZ_pb (j : Fin 4) : incZ A B ≫ pb A B j = 1 := by
  simp [incZ, mkZ_pb]

theorem inc_act_pa {T : Over S} (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (y : T ⟶ A) (k : Fin 8) (i : Fin 4) :
    y ≫ incZ A B ≫ actZ A B d la mu (oMat d k) ≫ pa A B i = if sig k = Sum.inl i then y else 1 := by
  rw [actZ, mkZ_pa]
  simp only [oMat_apply, Fin.prod_univ_four, comp_mul, GrpObj.comp_zpow, ← Category.assoc, incZ_pa]
  simp only [true_and, if_true, Category.comp_id, reduceCtorEq, false_and, if_false, zero_div, zpow_zero,
    mul_one, Sum.inl.injEq, Fin.reduceEq, comp_one, one_zpow]
  split_ifs <;> simp

theorem inc_act_pb {T : Over S} (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (y : T ⟶ A) (k : Fin 8) (j : Fin 4) :
    y ≫ incZ A B ≫ actZ A B d la mu (oMat d k) ≫ pb A B j = if sig k = Sum.inr j then y ≫ la else 1 := by
  rw [actZ, mkZ_pb]
  simp only [oMat_apply, Fin.prod_univ_four, comp_mul, GrpObj.comp_zpow, ← Category.assoc, incZ_pa, incZ_pb]
  simp only [true_and, if_true, Category.comp_id, reduceCtorEq, false_and, if_false, zero_div, zpow_zero,
    mul_one, one_mul, Sum.inl.injEq, Fin.reduceEq, comp_one, one_comp, one_zpow]
  split_ifs <;> simp

end Key

theorem list_prod_comp {S : Scheme.{0}} {T M N : Over S} [MonObj M] [MonObj N] (g : M ⟶ N) [IsMonHom g]
    (L : List (T ⟶ M)) : L.prod ≫ g = (L.map (· ≫ g)).prod := by
  let φ : (T ⟶ M) →* (T ⟶ N) :=
    { toFun := (· ≫ g), map_one' := one_comp g, map_mul' := fun x y => mul_comp x y g }
  exact map_list_prod φ L

theorem _root_.GlobalTheory.ZarhinFam.levZ_eq_mkZ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    (d h h' : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A))
    (κ : Fin 8 → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (a : Fin h' ⊕ Fin h' → ℤ) :
    levZ lev (incZ A B) (actZ A B d la mu) (oMat d) κ a =
      mkZ A B (fun i => lev (κ (Fin.castAdd 4 i) a)) (fun j => lev (κ (Fin.natAdd 4 j) a) ≫ la) := by
  apply zob_hom_ext
  · intro i
    rw [mkZ_pa, levZ, list_prod_comp, List.map_ofFn]
    simp only [Function.comp_def, Category.assoc, inc_act_pa, List.prod_ofFn, sig_eq_inl]
    exact Fintype.prod_ite_eq _ _
  · intro j
    rw [mkZ_pb, levZ, list_prod_comp, List.map_ofFn]
    simp only [Function.comp_def, Category.assoc, inc_act_pb, List.prod_ofFn, sig_eq_inr]
    exact Fintype.prod_ite_eq (Fin.natAdd 4 j) (fun k => lev (κ k a) ≫ la)

end GlobalTheory.ZarhinFam.LevCoord
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ZarhinFam

section Maps

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

def zpr (mu : B ⟶ A) (k : Fin 8) : Zob A B ⟶ A :=
  Sum.elim (pa A B) (fun j => pb A B j ≫ mu) (sig k)

def zphi (mu : B ⟶ A) : Zob A B ⟶ Out.powObj A 8 :=
  (Out.powIsLimit A 8).lift (Fan.mk _ (zpr A B mu))

theorem zphi_powPr (mu : B ⟶ A) (k : Fin 8) : zphi A B mu ≫ Out.powPr A k = zpr A B mu k :=
  (Out.powIsLimit A 8).fac _ ⟨k⟩

end Maps

def zW (d : ℕ) : Matrix (Fin 8) (Fin 8) ℤ := fun k l =>
  Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 (sig k) (sig l)

end GlobalTheory.ZarhinFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section
open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinKerA

variable {S : Scheme.{0}}

theorem mkZ_pa' {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S}
    (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) : mkZ A B u v ≫ pa A B i = u i := by
  simp only [mkZ, pa, lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb' {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S}
    (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) : mkZ A B u v ≫ pb A B j = v j := by
  simp only [mkZ, pb, lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem pull_zCls {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (w w' : Y ⟶ Zob A B) :
    CechPic.pull (lift w w').left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (w ≫ pa A B i) (w' ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (w ≫ pa A B i) (w' ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (w' ≫ pa A B i) (w ≫ pb A B j)) +
      ∑ j, evc hQ (w' ≫ pb A B j ≫ mu) (w ≫ pb A B j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zCls, map_add (f := _), map_sum, map_zsmul, evc, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc]

theorem zarhinBundle_kernel : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i ≫ la) * ∏ j, (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx i
  have hP := c.isLB
  have hQ : Q.IsLB := hZ.2.1.isLB
  have hQd : IsDual c.A B Q := hZ.2.1
  have hQd' : IsDual B c.A (swap Q) := hZ.2.2.1
  have hs : (swap Q).IsLB := hQd'.isLB
  haveI : IsMonHom mu := hZ.2.2.2.2.1

  have h0 : CechPic.pull (lift (snd (Zob c.A B) T ≫ x) (fst (Zob c.A B) T)).left
      (zCls c.A B c.isLB hQ d mu) = 0 := by
    rw [← cls_zP c.A B c.isLB hQ d mu, ← cls_pull (zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) _
      (pull_isLB (zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) _)]
    exact (cls_eq_zero_iff _).2 hx

  let inc : c.A ⟶ Zob c.A B := mkZ c.A B (fun k => if k = i then 𝟙 c.A else 1) (fun _ => 1)
  have h1 := congrArg (CechPic.pull (lift (fst c.A T ≫ inc) (snd c.A T)).left) h0
  rw [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst, pull_zCls] at h1
  have hpa : ∀ k, (fst c.A T ≫ inc) ≫ pa c.A B k = if k = i then fst c.A T else 1 := by
    intro k
    rw [Category.assoc, mkZ_pa']
    split_ifs <;> simp [MonObj.comp_one]
  have hpb : ∀ j, (fst c.A T ≫ inc) ≫ pb c.A B j = 1 := by
    intro j
    rw [Category.assoc, mkZ_pb', MonObj.comp_one]
  have z1 : ∀ {Y : Over S} (a : Y ⟶ c.A), evc hP a (1 : Y ⟶ c.A) = 0 := fun a => evc_one_right hP c.rig₂ a
  have z2 : ∀ {Y : Over S} (a : Y ⟶ c.A), evc hQ a (1 : Y ⟶ B) = 0 := fun a => evc_one_right hQ hQd.zero a
  have z3 : ∀ {Y : Over S} (b : Y ⟶ B), evc hQ (1 : Y ⟶ c.A) b = 0 := fun b => hQd.additive.evc_one hQ b
  have s1 : (∑ k, evc hP ((snd c.A T ≫ x) ≫ pa c.A B k) ((fst c.A T ≫ inc) ≫ pa c.A B k)) =
      evc hP ((snd c.A T ≫ x) ≫ pa c.A B i) (fst c.A T) := by
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [hpa, if_neg hk, z1]) (fun hi => absurd (Finset.mem_univ i) hi),
      hpa, if_pos rfl]
  have s2 : (∑ k, ∑ j, quat d j k • evc hQ ((snd c.A T ≫ x) ≫ pa c.A B k) ((fst c.A T ≫ inc) ≫ pb c.A B j)) = 0 := by
    simp only [hpb, z2, smul_zero, Finset.sum_const_zero]
  have s3 : (∑ k, ∑ j, quat d j k • evc hQ ((fst c.A T ≫ inc) ≫ pa c.A B k) ((snd c.A T ≫ x) ≫ pb c.A B j)) =
      ∑ j, quat d j i • evc hQ (fst c.A T) ((snd c.A T ≫ x) ≫ pb c.A B j) := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp only [hpa, if_neg hk, z3, smul_zero, Finset.sum_const_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [hpa, if_pos rfl]
  have s4 : (∑ j, evc hQ ((fst c.A T ≫ inc) ≫ pb c.A B j ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j)) = 0 := by
    simp only [← Category.assoc _ (pb c.A B _) mu, hpb, MonObj.one_comp, z3, Finset.sum_const_zero]
  rw [s1, s2, s3, s4, add_zero, add_zero] at h1

  have eS : cls c.P hP = evc hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
  have eL : cls c.P hP = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
    (cls_eq_iff hP (pull_isLB hQ _)).2 hZ.2.2.2.2.2.2.2
  have ePQ : ∀ {Y : Over S} (u a : Y ⟶ c.A), evc hP u a = evc hQ a (u ≫ la) := by
    intro Y u a
    have e1 := congrArg (CechPic.pull (lift u a).left) eS
    have e2 := congrArg (CechPic.pull (lift a u).left) eL
    rw [pull_evc, lift_snd, lift_fst] at e1
    rw [pull_evc, lift_fst, lift_snd_assoc] at e2
    exact e1.trans e2

  have hadd : ∀ {Y : Over S} (a : Y ⟶ c.A) (b b' : Y ⟶ B), evc hQ a (b * b') = evc hQ a b + evc hQ a b' := by
    intro Y a b b'
    rw [← evc_swap hQ hs, ← evc_swap hQ hs, ← evc_swap hQ hs]
    exact (isAdditive_iff hs).1 hQd'.additive Y b b' a
  let φ : (T ⟶ B) →* Multiplicative (Pic (c.A ⊗ T).left) :=
    MonoidHom.mk' (fun b => Multiplicative.ofAdd (evc hQ (fst c.A T) (snd c.A T ≫ b))) fun b b' => by
      simp only [MonObj.comp_mul, hadd, ofAdd_add]
  refine (hQd.isPerfect hQd').ker_right T _ ((triv_ev_iff hQ _ _).2 ?_)
  have key : Multiplicative.toAdd (φ ((x ≫ pa c.A B i ≫ la) * ∏ j, (x ≫ pb c.A B j) ^ quat d j i)) =
      evc hQ (fst c.A T) (snd c.A T ≫ ((x ≫ pa c.A B i ≫ la) * ∏ j, (x ≫ pb c.A B j) ^ quat d j i)) := rfl
  rw [← key, map_mul, map_prod, toAdd_mul, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, φ, MonoidHom.mk'_apply, toAdd_ofAdd]
  rw [← Category.assoc, ← Category.assoc, ← ePQ]
  simpa only [Category.assoc] using h1

end GlobalTheory.ZarhinKerA
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

open GlobalTheory.CechPic GlobalTheory.AbDual

noncomputable section

namespace GlobalTheory.ZarhinFam

section
variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem incZ_pa (i : Fin 4) : incZ A B ≫ pa A B i = if i = 0 then 𝟙 A else 1 := by
  unfold incZ pa mkZ
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk A _) ⟨i⟩

theorem incZ_pb (j : Fin 4) : incZ A B ≫ pb A B j = 1 := by
  unfold incZ pb mkZ
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk A _) ⟨j⟩
end

theorem zarhinBundle_pullback_inclusion : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → LBIso c.P ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (GlobalTheory.ZarhinFam.incZ c.A B ⊗ₘ GlobalTheory.ZarhinFam.incZ c.A B).left) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ _ _ _ _
  have hQ : Q.IsLB := hZ.2.1.isLB
  have hq0 : ∀ {Y : Over S} (a : Y ⟶ c.A), CechPic.pull (lift a (1 : Y ⟶ B)).left (cls Q hZ.2.1.isLB) = 0 :=
    fun a => evc_one_right hZ.2.1.isLB hZ.2.1.zero a
  have hp0 : ∀ {Y : Over S}, CechPic.pull (lift (1 : Y ⟶ c.A) (1 : Y ⟶ c.A)).left (cls c.P c.isLB) = 0 :=
    evc_one_left c.isLB c.rig₁ 1
  have hp1 : CechPic.pull (lift (fst c.A c.A) (snd c.A c.A)).left (cls c.P c.isLB) = cls c.P c.isLB := by
    rw [lift_fst_snd, Over.id_left, pull_id]
  refine (cls_eq_iff c.isLB (pull_isLB (zarhinBundle_isLineBundle _ _ _ _ _ _) _)).1 ?_
  rw [cls_pull (zarhinBundle_isLineBundle _ _ _ _ _ _), cls_zP]
  unfold zCls

  simp only [map_add (f := _), map_sum, map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, tensorHom_fst_assoc,
  tensorHom_snd_assoc, incZ_pa, incZ_pb, Fin.sum_univ_four]
  simp only [MonObj.comp_one, Category.comp_id, ↓reduceIte, Fin.isValue, Fin.reduceEq, one_ne_zero, hq0, hp0, hp1, smul_zero, add_zero, zero_add, Finset.sum_const_zero]

end GlobalTheory.ZarhinFam
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.SympLevLocus

def SympAt {S : Scheme.{0}} {A : Over S} [GrpObj A] (P : LB (G2 A).left) (h M : ℕ)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (k : Type) [Field k] (x : Sp k ⟶ S) (z : kˣ) : Prop :=
  (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b)) ∧
    (∀ g : Over.mk x ⟶ A, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
    ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b)
      (unitOn (z ^ (2 * omegaStd a b)))

theorem isSympLev_iff {S : Scheme.{0}} {A : Over S} [GrpObj A] (P : LB (G2 A).left) (h M : ℕ) {B : Type}
    [CommRing B] (ζ : B) (t₁ : S ⟶ Sp B) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) :
    IsSympLev P h M ζ t₁ lev ↔ (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ M = 1) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ t₁ = spMap β →
        (z : k) = β ζ → SympAt P h M lev k x z :=
  Iff.rfl

end GlobalTheory.SympLevLocus

namespace GlobalTheory.SympLevLocus


open GlobalTheory.SiegelPull in
theorem sympAt_pullback_iff {S T : Scheme.{0}} (g : T ⟶ S) {A : Over S} [GrpObj A] [IsCommMonObj A] {A' : Over T}
    [GrpObj A'] [IsCommMonObj A'] {P : LB (G2 A).left} {P' : LB (G2 A').left} {φ : A'.left ⟶ A.left}
    {φ₂ : (G2 A').left ⟶ (G2 A).left} {h M : ℕ} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)}
    {lev' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ A')} (hP : P.IsLB) (hP' : P'.IsLB)
    (pb : IsGrpPullback A' A g φ) (sq : IsSquare φ φ₂) (iso : LBIso P' (P.pull φ₂))
    (hl : ∀ a, (lev' a).left ≫ φ = g ≫ (lev a).left) (k : Type) [Field k] (x : Sp k ⟶ T) (z : kˣ) :
    SympAt P' h M lev' k x z ↔ SympAt P h M lev k (x ≫ g) z := by
  have push : ∀ a, pushHom pb (Over.mk x) (toUnit (Over.mk x) ≫ lev' a) = toUnit (Over.mk (x ≫ g)) ≫ lev a := by
    intro a
    apply Over.OverMorphism.ext
    show ((toUnit (Over.mk x)).left ≫ (lev' a).left) ≫ φ = (toUnit (Over.mk (x ≫ g))).left ≫ (lev a).left
    rw [Category.assoc, hl, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
    rfl
  have inj := push_injective pb (Over.mk x)
  have surj := push_surjective pb (Over.mk x)
  refine and_congr (forall_congr' fun a => ?_) (and_congr ⟨fun H g₀ hg₀ => ?_, fun H g₀ hg₀ => ?_⟩
    (forall_congr' fun a => forall_congr' fun b => ?_))
  · rw [← inj.eq_iff, push, map_one]
  · obtain ⟨g₁, rfl⟩ := surj g₀
    obtain ⟨a, ha⟩ := H g₁ (inj (by rw [map_pow, map_one]; exact hg₀))
    exact ⟨a, (push a).symm.trans (congrArg _ ha)⟩
  · obtain ⟨a, ha⟩ := H (pushHom pb (Over.mk x) g₀) (by rw [← map_pow, hg₀, map_one])
    exact ⟨a, inj ((push a).trans ha)⟩
  · exact weilIs_grpPullback_of_comm S T A A' g φ _ _ (pull_isLB hP _) (pull_isLB hP' _) pb
      (diag_iso sq iso) (Over.mk x) M _ _ _ _ _
      (congrArg (fun q => q.left) (push a).symm) (congrArg (fun q => q.left) (push b).symm)

end GlobalTheory.SympLevLocus
end
end
