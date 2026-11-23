module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

section RadialKernelIntegrals

variable {S : Scheme.{0}}

def precompHom {Y Y' G : Over S} [GrpObj G] (f : Y' ⟶ Y) : (Y ⟶ G) →* (Y' ⟶ G) :=
  MonoidHom.mk' (fun a => f ≫ a) (fun a b => MonObj.comp_mul f a b)

def postcompHom {Y G H : Over S} [GrpObj G] [GrpObj H] (g : G ⟶ H) [IsMonHom g] : (Y ⟶ G) →* (Y ⟶ H) :=
  MonoidHom.mk' (fun a => a ≫ g) (fun a b => MonObj.mul_comp a b g)

def evcHom {A T Y : Over S} [GrpObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB) (h : IsAdditive M) (t : Y ⟶ T) :
    (Y ⟶ A) →* Multiplicative (Pic Y.left) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (evc hM a t)) (fun a b => by
    rw [(isAdditive_iff hM).1 h Y a b t]; rfl)

theorem evc_prod_zpow_left {A T Y : Over S} [GrpObj A] [IsCommMonObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (h : IsAdditive M) {K : Type} [Fintype K] (a : K → (Y ⟶ A)) (n : K → ℤ) (t : Y ⟶ T) :
    evc hM (∏ k, a k ^ n k) t = ∑ k, n k • evc hM (a k) t := by
  have e := map_prod (evcHom hM h t) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact congrArg Multiplicative.toAdd e

theorem evc_pow_left {A T Y : Over S} [GrpObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (h : IsAdditive M) (a : Y ⟶ A) (n : ℕ) (t : Y ⟶ T) : evc hM (a ^ n) t = n • evc hM a t :=
  congrArg Multiplicative.toAdd (map_pow (evcHom hM h t) a n)

theorem evc_mul_right {A B Y : Over S} [GrpObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) (a : Y ⟶ A) (b b' : Y ⟶ B) : evc hM a (b * b') = evc hM a b + evc hM a b' := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', ← evc_swap hM hs', ← evc_swap hM hs']
  exact (isAdditive_iff hs').1 hs Y b b' a

theorem evc_prod_zpow_right {A B Y : Over S} [GrpObj B] [IsCommMonObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) {K : Type} [Fintype K] (a : Y ⟶ A) (b : K → (Y ⟶ B)) (n : K → ℤ) :
    evc hM a (∏ k, b k ^ n k) = ∑ k, n k • evc hM a (b k) := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', evc_prod_zpow_left hs' hs]
  exact Finset.sum_congr rfl fun k _ => by rw [evc_swap hM hs']

theorem evc_pow_right {A B Y : Over S} [GrpObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) : evc hM a (b ^ n) = n • evc hM a b := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', evc_pow_left hs' hs, evc_swap hM hs']

theorem comp_prod_zpow'' {Y Y' G : Over S} [GrpObj G] [IsCommMonObj G] {K : Type} [Fintype K] (f : Y' ⟶ Y)
    (a : K → (Y ⟶ G)) (n : K → ℤ) : f ≫ ∏ k, a k ^ n k = ∏ k, (f ≫ a k) ^ n k := by
  have e := map_prod (precompHom f) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact e

theorem prod_zpow_comp'' {Y G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj G] [IsCommMonObj H] {K : Type}
    [Fintype K] (a : K → (Y ⟶ G)) (n : K → ℤ) (g : G ⟶ H) [IsMonHom g] :
    (∏ k, a k ^ n k) ≫ g = ∏ k, (a k ≫ g) ^ n k := by
  have e := map_prod (postcompHom (Y := Y) g) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact e

end RadialKernelIntegrals

end GlobalTheory.ZarhinKerB

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

section KerAux2

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa' {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  rw [pa, ← Category.assoc, mkZ, lift_fst]
  exact (Out.powIsLimit A 4).fac _ ⟨i⟩

theorem mkZ_pb' {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  rw [pb, ← Category.assoc, mkZ, lift_snd]
  exact (Out.powIsLimit B 4).fac _ ⟨j⟩

theorem pull_zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (p q : Y ⟶ Zob A B) :
    CechPic.pull (lift p q).left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (p ≫ pa A B i) (q ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (p ≫ pa A B i) (q ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (q ≫ pa A B i) (p ≫ pb A B j)) +
      ∑ j, evc hQ (q ≫ pb A B j ≫ mu) (p ≫ pb A B j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zCls, map_add (f := _), map_sum, map_zsmul, evc, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc]

end KerAux2

end GlobalTheory.ZarhinKerB

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zarhinBundle_kernel : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ j, ((∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i) ≫ la) * (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ d = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx j
  have hQ : IsDual c.A B Q := hZ.2.1
  have hQ' : IsDual B c.A (swap Q) := hZ.2.2.1
  haveI hla : IsMonHom la := hZ.2.2.2.1
  haveI hmu : IsMonHom mu := hZ.2.2.2.2.1
  have hlm : la ≫ mu = 𝟙 c.A ^ d := hZ.2.2.2.2.2.1
  have hPQ := hZ.2.2.2.2.2.2.2
  have hzP := zarhinBundle_isLineBundle c.A B c.isLB hQ.isLB d mu
  have h0 : ∀ (Y : Over S) (s : Y ⟶ T) (z : Y ⟶ Zob c.A B),
      CechPic.pull (lift (s ≫ x) z).left (zCls c.A B c.isLB hQ.isLB d mu) = 0 := by
    intro Y s z
    have e := congrArg (CechPic.pull (lift z s).left) ((cls_eq_zero_iff (pull_isLB hzP _)).2 hx)
    rw [cls_pull hzP, cls_zP, map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst] at e
    exact e

  have e := h0 (c.A ⊗ T) (snd c.A T)
    (mkZ c.A B (fun _ => 1) (fun j' => if j' = j then fst c.A T ≫ la else 1))
  rw [pull_zCls] at e
  simp only [mkZ_pa', mkZ_pb'] at e
  simp only [← Category.assoc, mkZ_pa', mkZ_pb'] at e
  have t2 : ∀ i, ∑ j', quat d j' i • evc hQ.isLB ((snd c.A T ≫ x) ≫ pa c.A B i)
      (if j' = j then fst c.A T ≫ la else 1) = quat d j i • evc hQ.isLB ((snd c.A T ≫ x) ≫ pa c.A B i) (fst c.A T ≫ la) :=
    fun i => by
      rw [Fintype.sum_eq_single j (fun j' hj' => by rw [if_neg hj', evc_one_right hQ.isLB hQ.zero, smul_zero]),
        if_pos rfl]
  have t4 : ∑ j', evc hQ.isLB ((if j' = j then fst c.A T ≫ la else 1) ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j') =
      evc hQ.isLB ((fst c.A T ≫ la) ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j) := by
    rw [Fintype.sum_eq_single j (fun j' hj' => by rw [if_neg hj', MonObj.one_comp, hQ.additive.evc_one hQ.isLB]),
      if_pos rfl]
  simp only [t2, t4, evc_one_right c.isLB c.rig₂, hQ.additive.evc_one hQ.isLB, smul_zero, Finset.sum_const_zero,
    zero_add, add_zero] at e
  have hPev : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc c.isLB p q = evc hQ.isLB p (q ≫ la) := by
    intro Y p q
    have e1 : cls c.P c.isLB = evc hQ.isLB (fst c.A c.A) (snd c.A c.A ≫ la) :=
      (cls_eq_iff c.isLB (pull_isLB hQ.isLB _)).2 hPQ
    rw [evc, e1, pull_evc, lift_fst, lift_snd_assoc]
  have hPsymm : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc c.isLB p q = evc c.isLB q p := by
    intro Y p q
    have e1 : cls c.P c.isLB = evc c.isLB (snd c.A c.A) (fst c.A c.A) :=
      (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
    rw [evc, e1, pull_evc, lift_fst, lift_snd]
  have hQsw : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc hQ.isLB p (q ≫ la) = evc hQ.isLB q (p ≫ la) := by
    intro Y p q
    rw [← hPev, ← hPev, hPsymm]
  refine (hQ.isPerfect hQ').ker_right T _ ((triv_ev_iff hQ.isLB _ _).2 ?_)
  rw [MonObj.comp_mul, ← Category.assoc, comp_prod_zpow'', prod_zpow_comp'', MonObj.comp_pow,
    evc_mul_right hQ.isLB hQ'.additive, evc_prod_zpow_right hQ.isLB hQ'.additive, evc_pow_right hQ.isLB hQ'.additive]
  rw [Category.assoc, hlm, MonObj.comp_pow, Category.comp_id, evc_pow_left hQ.isLB hQ.additive] at e
  rw [← e]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hQsw, Category.assoc]

end GlobalTheory.ZarhinKerB
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.RelAlg

open GlobalTheory.ZarhinFam

section Obj

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  simp only [mkZ, pa]
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  simp only [mkZ, pb]
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem zob_ext {T : Over S} {f g : T ⟶ Zob A B} (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · apply (Out.powIsLimit A 4).hom_ext
    rintro ⟨i⟩
    simpa [pa] using ha i
  · apply (Out.powIsLimit B 4).hom_ext
    rintro ⟨j⟩
    simpa [pb] using hb j

instance isMonHom_pa (i : Fin 4) : IsMonHom (pa A B i) := by
  unfold pa
  infer_instance

instance isMonHom_pb (j : Fin 4) : IsMonHom (pb A B j) := by
  unfold pb
  infer_instance

theorem isMonHom_of_coords {X : Over S} [MonObj X] (f : X ⟶ Zob A B)
    (ha : ∀ i, IsMonHom (f ≫ pa A B i)) (hb : ∀ j, IsMonHom (f ≫ pb A B j)) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · apply zob_ext A B
    · intro i
      have := ha i
      simp only [Category.assoc, IsMonHom.one_hom (f := f ≫ pa A B i),
        IsMonHom.one_hom (f := pa A B i)]
    · intro j
      have := hb j
      simp only [Category.assoc, IsMonHom.one_hom (f := f ≫ pb A B j),
        IsMonHom.one_hom (f := pb A B j)]
  · apply zob_ext A B
    · intro i
      have := ha i
      simp only [Category.assoc, IsMonHom.mul_hom (f := f ≫ pa A B i),
        IsMonHom.mul_hom (f := pa A B i), MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    · intro j
      have := hb j
      simp only [Category.assoc, IsMonHom.mul_hom (f := f ≫ pb A B j),
        IsMonHom.mul_hom (f := pb A B j), MonoidalCategory.tensorHom_comp_tensorHom_assoc]

theorem isMonHom_incZ : IsMonHom (incZ A B) := by
  apply isMonHom_of_coords
  · intro i
    rw [incZ, mkZ_pa]
    split_ifs
    · infer_instance
    · exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  · intro j
    rw [incZ, mkZ_pb]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[B]))

theorem isMonHom_prZ : IsMonHom (prZ A B) := by
  unfold prZ pa
  infer_instance

theorem incZ_prZ : incZ A B ≫ prZ A B = 𝟙 A := by
  rw [incZ, prZ, mkZ_pa]
  simp

theorem prZ_incZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) : prZ A B ≫ incZ A B = actZ A B d la mu (idem d) := by
  apply zob_ext
  · intro i
    rw [Category.assoc, incZ, mkZ_pa, actZ, mkZ_pa]
    fin_cases i <;> simp [prZ, idem, Matrix.single_apply, Fin.prod_univ_four, MonObj.comp_one]
  · intro j
    rw [Category.assoc, incZ, mkZ_pb, actZ, mkZ_pb]
    fin_cases j <;> simp [prZ, idem, Matrix.single_apply, Fin.prod_univ_four, MonObj.comp_one]

end Obj

end GlobalTheory.ZarhinFam.RelAlg

noncomputable section

namespace GlobalTheory.ZarhinFam.RelAlg

open GlobalTheory.ZarhinFam

section Lev

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

def precompHom {X Y M : Over S} [GrpObj M] [IsCommMonObj M] (x : X ⟶ Y) : (Y ⟶ M) →* (X ⟶ M) where
  toFun g := x ≫ g
  map_one' := MonObj.comp_one x
  map_mul' g₁ g₂ := MonObj.comp_mul x g₁ g₂

theorem one_comp_actZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) [IsMonHom la] [IsMonHom mu] (N : ord d) :
    (1 : 𝟙_ (Over S) ⟶ Zob A B) ≫ actZ A B d la mu N = 1 := by
  apply zob_ext
  · intro i
    rw [Category.assoc, actZ, mkZ_pa, MonObj.one_comp (pa A B i)]
    change precompHom (1 : 𝟙_ (Over S) ⟶ Zob A B) _ = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [map_mul, map_zpow, map_zpow]
    change (1 ≫ pa A B j) ^ _ * (1 ≫ pb A B j ≫ mu) ^ _ = 1
    rw [MonObj.one_comp, ← Category.assoc, MonObj.one_comp, MonObj.one_comp]
    simp
  · intro j
    rw [Category.assoc, actZ, mkZ_pb, MonObj.one_comp (pb A B j)]
    change precompHom (1 : 𝟙_ (Over S) ⟶ Zob A B) _ = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [map_mul, map_zpow, map_zpow]
    change (1 ≫ pa A B k ≫ la) ^ _ * (1 ≫ pb A B k) ^ _ = 1
    rw [MonObj.one_comp (pa A B k ≫ la), MonObj.one_comp (pb A B k)]
    simp

theorem oMat_zero (d : ℕ) : oMat d 0 = idem d := rfl

end Lev

end GlobalTheory.ZarhinFam.RelAlg

namespace GlobalTheory.ZarhinFam

open GlobalTheory.ZarhinFam.RelAlg

theorem zRel_alg : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → IsMonHom (GlobalTheory.ZarhinFam.incZ c.A B) ∧ IsMonHom (GlobalTheory.ZarhinFam.prZ c.A B) ∧ GlobalTheory.ZarhinFam.incZ c.A B ≫ GlobalTheory.ZarhinFam.prZ c.A B = 𝟙 c.A ∧ GlobalTheory.ZarhinFam.prZ c.A B ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.idem d) ∧ ∀ a, c.lev a ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (GlobalTheory.ZarhinFam.jlMap h a) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ _ _ _ _ κ hκ
  haveI : IsMonHom la := hZ.2.2.2.1
  haveI : IsMonHom mu := hZ.2.2.2.2.1
  haveI := isMonHom_incZ c.A B
  have hpi := prZ_incZ c.A B d la mu
  refine ⟨isMonHom_incZ c.A B, isMonHom_prZ c.A B, incZ_prZ c.A B, hpi, fun a => ?_⟩
  have hlev0 : c.lev 0 = 1 := by
    have h0 := c.lev_add 0 0
    rw [add_zero] at h0
    exact left_eq_mul.mp h0
  rw [levZ, List.prod_ofFn, Fintype.prod_eq_single 0 (fun k hk => by
    rw [hκ.2.2 k hk a, hlev0, ← Category.assoc, MonObj.one_comp, one_comp_actZ])]
  rw [hκ.2.1 a, oMat_zero, ← hpi, ← Category.assoc (incZ c.A B), incZ_prZ, Category.id_comp]

end GlobalTheory.ZarhinFam
end
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelPull

theorem push_sec_of_left {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hpb : IsGrpPullback A' A f φ) {x : 𝟙_ (Over S) ⟶ A} {x' : 𝟙_ (Over S') ⟶ A'}
    (hx : x'.left ≫ φ = f ≫ x.left) (T : Over S') :
    pushHom hpb T (toUnit T ≫ x') = toUnit (Over.mk (T.hom ≫ f)) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ x'.left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ x.left
  rw [Category.assoc, hx, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem isSympLev_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A]
    [IsCommMonObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left}
    (hpb : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (G2 A).left} {P' : LB (G2 A').left}
    (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) {h M : ℕ} {B : Type} [CommRing B] {ζ : B}
    {s : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)}
    {lev' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A')} (hl : ∀ a, (lev' a).left ≫ φ = f ≫ (lev a).left)
    (hS : IsSympLev P h M ζ s lev) : IsSympLev P' h M ζ (f ≫ s) lev' := by
  have hp' : ∀ a, pushHom hpb _ (lev' a) = toUnit _ ≫ lev a := fun a => by
    have e := push_sec_of_left hpb (hl a) (𝟙_ (Over S'))
    rwa [toUnit_unit, Category.id_comp] at e
  refine ⟨fun a b => push_injective hpb _ ?_, fun a => push_injective hpb _ ?_, ?_⟩
  · rw [map_mul, hp', hp', hp', hS.1, MonObj.comp_mul]
  · rw [map_pow, map_one, hp', ← MonObj.comp_pow, hS.2.1, MonObj.comp_one]
  intro k _ _ x β z hx hz
  obtain ⟨g₁, g₂, g₃⟩ := hS.2.2 k (x ≫ f) β z (by rw [Category.assoc, hx]) hz
  refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
  · rw [← (push_injective hpb (Over.mk x)).eq_iff, push_sec_of_left hpb (hl a), map_one]
    rfl
  · obtain ⟨a, ha⟩ := g₂ (pushHom hpb (Over.mk x) g) (by
      have := congrArg (pushHom hpb (Over.mk x)) hg
      rw [map_pow, map_one] at this
      exact this)
    exact ⟨a, push_injective hpb _ ((push_sec_of_left hpb (hl a) _).trans ha)⟩
  · exact (weilIs_grpPullback_of_comm S S' A A' f φ _ _ (pull_isLB hP _) (pull_isLB hP' _) hpb
      (diag_iso sq H) (Over.mk x) M _ _ _ _ _
      (congrArg (fun q => q.left) (push_sec_of_left hpb (hl a) (Over.mk x)).symm)
      (congrArg (fun q => q.left) (push_sec_of_left hpb (hl b) (Over.mk x)).symm)).2 (g₃ a b)

theorem kerBy_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂)
    {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) (d : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ d = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x ^ d = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine push_injective h T ?_
  rw [map_pow, map_one]
  refine hn _ (pushHom h T x) ?_
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

theorem siegKerBy_pull {S S' : Scheme.{0}} {h M : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c : SiegPre h M ζ s} {c' : SiegPre h M ζ' s'} {f : S' ⟶ S}
    (m : SiegPB c' c f) {d : ℕ} (hc : SiegKerBy c d) : SiegKerBy c' d := by
  obtain ⟨φ, φ₂, pb, sq, iso, -⟩ := m
  exact ⟨(GlobalTheory.pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
    (diag_iso sq iso)).2.1 hc.1, kerBy_pull pb sq c.isLB c'.isLB iso d hc.2⟩

end GlobalTheory.UPel.HT
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.matrixWeightedPairBundle_rigidified_ample : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsAbelianScheme (Out.powObj A r) ∧ (formLB A Q (Out.powPr A (n := r)) W).IsLB ∧ Out.Rigidified (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) ∧ Out.RelAmple (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) := by
  first | (exact @GlobalTheory.PowFormProps.formLB_props) | (exact GlobalTheory.PowFormProps.formLB_props) | (intros; apply GlobalTheory.PowFormProps.formLB_props  <;> assumption)
end
