module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle191
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle147
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle008
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.GtBaseChangeSharp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStdSympZmod
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle007
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.E8LatticePullbackGeneric

open GlobalTheory.CechPic

theorem sum_lamPts {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x y : T ⟶ G) (c : Pic G.left) (w : ℤ) :
    ∑ k : Fin 4, (-(w * GlobalTheory.PolDeg.negε k)) • pull (GlobalTheory.PolDeg.lamPts x y k) c = w • lam c x y := by
  simp only [Fin.sum_univ_four, GlobalTheory.PolDeg.lamPts, GlobalTheory.PolDeg.negε, lam, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [smul_add, smul_sub, mul_neg, mul_one, neg_neg, neg_smul]
  all_goals first
  | (norm_num; done)
  | (norm_num; abel)
  | (push_cast; abel)
  | (rw [sub_eq_add_neg, sub_eq_add_neg]; congr 1 <;> [congr 1; skip] <;> norm_num)

theorem lam_pull_hom {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G'] (φ : G' ⟶ G) [IsMonHom φ]
    (c : Pic G.left) (x y : T ⟶ G') : lam (pull φ.left c) x y = lam c (x ≫ φ) (y ≫ φ) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, MonObj.mul_comp, MonObj.one_comp]

theorem pull_fst_lam {S S' : Scheme.{0}} (f : S' ⟶ S) {X G : Over S} [GrpObj G] (c : Pic G.left) (x x' : X ⟶ G) :
    GlobalTheory.CechPic.pull (pullback.fst X.hom f) (lam c x x') =
      lam (GlobalTheory.CechPic.pull (pullback.fst G.hom f) c) ((Over.pullback f).map x) ((Over.pullback f).map x') := by
  have hfst : ∀ z : X ⟶ G, pullback.fst X.hom f ≫ z.left = ((Over.pullback f).map z).left ≫ pullback.fst G.hom f :=
    fun z => by simp [pullback.lift_fst]
  simp only [lam, map_add (f := _), map_sub, ← pull_comp, hfst, Functor.map_mul, Functor.map_one]


open GlobalTheory.E8LatticePullbackGeneric GlobalTheory.CechPic in
theorem exists_polAV_gen : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ (A : PolAV (Sp (FractionRing V₁))) (gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  intro hL₁ _ _ V₁ _ _ _ _ D₀ G₀ _ _ A₀ U₀ _ W hW
  have := A₀.isAb.comm

  let c := GlobalTheory.EighthPowerFactor.siegOne hL₁.globalFns A₀.isAb A₀.isLB A₀.g
  have hc1 : RelAmple c.A c.diag := GlobalTheory.EighthPowerFactor.relAmple_diag_lam A₀.isAb A₀.isLB
    (GlobalTheory.Moduli.cube_of_isLB _ A₀ A₀.L A₀.isLB) A₀.ample
  have hb := GlobalTheory.EighthPower.isSymBilin hL₁.globalFns c hc1
  have hpw := GlobalTheory.PowGrp.powers _ _ _ 8 (powIsPowGrp A₀.A 8)
  have hu : ∀ (T : Over (Sp (FractionRing V₁))) (y : Fin 8 → (T ⟶ A₀.A)),
      ∃! x : T ⟶ powObj A₀.A 8, ∀ u, x ≫ powPr A₀.A u = y u := fun T y =>
    ⟨(powIsLimit A₀.A 8).lift (Fan.mk T y), fun u => (powIsLimit A₀.A 8).fac _ ⟨u⟩,
      fun x hx => (powIsLimit A₀.A 8).hom_ext fun ⟨u⟩ => by rw [(powIsLimit A₀.A 8).fac]; exact hx u⟩
  let Q : PolAV (Sp (FractionRing V₁)) :=
    { A := powObj A₀.A 8, isAb := hpw.2.2.2.1 A₀.isAb, g := 8 * A₀.g, smoothDim := hpw.2.2.1 _ A₀.smoothDim
      L := GlobalTheory.MatrixBundle.matLB c.P (powPr A₀.A) W, isLB := LB.isLB_linComb c.isLB _ _
      rigid := GlobalTheory.MatrixBundle.rigidified_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u)
      sym := GlobalTheory.MatrixBundle.sym_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u)
      ample := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hL₁.globalFns _ _ 8 _ _ _ _ c _ (powPr A₀.A) W
        (fun u => powPr.isMonHom A₀.A u) hu hc1 hW.1
      ktriv := GlobalTheory.MatrixBundle.kTriv_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u) hu hW.2
        (fun T x hx => GlobalTheory.SiegelOfPolarised.eq_one_of_lam A₀.isLB A₀.ktriv x hx) }

  let F := Over.pullback (jK V₁)
  have hP : IsLimit (Fan.mk (F.obj (powObj G₀ 8)) fun u => F.map (powPr G₀ u)) :=
    isLimitFanMkObjOfIsLimit F _ _ (powIsLimit G₀ 8)
  let y : Fin 8 → (F.obj (powObj G₀ 8) ⟶ A₀.A) := fun u => F.map (powPr G₀ u) ≫ U₀.gen.hom
  let gen : F.obj (powObj G₀ 8) ≅ Q.A :=
    { hom := (powIsLimit A₀.A 8).lift (Fan.mk _ y)
      inv := hP.lift (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv)
      hom_inv_id := hP.hom_ext fun ⟨u⟩ => by
        simp only [Fan.mk_pt, Fan.mk_π_app, Category.assoc, Category.id_comp]
        erw [hP.fac (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv) ⟨u⟩]
        simp only [Fan.mk_π_app]
        erw [(powIsLimit A₀.A 8).fac_assoc (Fan.mk _ y) ⟨u⟩]
        simp [y]
      inv_hom_id := (powIsLimit A₀.A 8).hom_ext fun ⟨u⟩ => by
        simp only [Fan.mk_pt, Fan.mk_π_app, Category.assoc, Category.id_comp]
        erw [(powIsLimit A₀.A 8).fac (Fan.mk _ y) ⟨u⟩]
        simp only [Fan.mk_π_app, y]
        rw [← Category.assoc]
        erw [hP.fac (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv) ⟨u⟩]
        simp }
  have hgen : ∀ u, gen.hom ≫ powPr A₀.A u = y u := fun u => (powIsLimit A₀.A 8).fac _ ⟨u⟩
  have := U₀.gen_hom
  refine ⟨Q, gen, ?_, ?_⟩
  · refine GlobalTheory.EighthPowerFactor.isMonHom_of_coord (fun u => powPr.isMonHom A₀.A u) hu fun u => ?_
    rw [hgen u]
    infer_instance
  · have hA := A₀.isLB
    have hLG := U₀.LG.isLB
    have hQ : Q.L.IsLB := Q.isLB
    have hE : (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).IsLB := LB.isLB_linComb hLG _ _
    have hext : pull (pullback.fst G₀.hom (jK V₁)) (cls _ hLG) = pull U₀.gen.hom.left (cls _ hA) := by
      obtain ⟨w, hw⟩ := U₀.ext
      have e := (cls_eq_iff (pull_isLB hA _) (pull_isLB hLG _)).2 ⟨w, hw⟩
      rw [cls_pull hA, cls_pull hLG] at e
      exact e.symm
    have key : ∀ x x' : powObj G₀ 8 ⟶ G₀, pull (pullback.fst (powObj G₀ 8).hom (jK V₁)) (lam (cls _ hLG) x x') =
        lam (cls _ hA) (F.map x ≫ U₀.gen.hom) (F.map x' ≫ U₀.gen.hom) := by
      intro x x'
      rw [pull_fst_lam, hext, lam_pull_hom]
    have hlam : cls c.P c.isLB = lam (cls _ hA) (fst A₀.A A₀.A) (snd A₀.A A₀.A) := cls_cube_two hA _ _ c.isLB
    have eL : pull gen.hom.left (cls Q.L hQ) =
        ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • lam (cls _ hA) (y uv.1) (y uv.2) := by

      rw [show cls Q.L hQ = _ from cls_linComb c.isLB
      (fun uv : Fin 8 × Fin 8 => (lift (powPr A₀.A uv.1) (powPr A₀.A uv.2)).left) (fun uv => W uv.1 uv.2) hQ, map_sum]
      refine Finset.sum_congr rfl fun uv _ => ?_
      rw [map_zsmul, hlam]
      erw [pull_lam, pull_lam]
      rw [lift_fst, lift_snd]
      erw [hgen, hgen]
    have eR : pull (pullback.fst (powObj G₀ 8).hom (jK V₁)) (cls _ hE) =
        ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • lam (cls _ hA) (y uv.1) (y uv.2) := by
      rw [show cls _ hE = _ from cls_linComb hLG (K := (Fin 8 × Fin 8) × Fin 4)
        (fun k => GlobalTheory.PolDeg.lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
        (fun k => -(W k.1.1 k.1.2 * GlobalTheory.PolDeg.negε k.2)) hE, Fintype.sum_prod_type]

      simp only [sum_lamPts, map_sum, map_zsmul, key, y]
    refine (cls_eq_iff (pull_isLB hQ _) (pull_isLB hE _)).1 ?_
    rw [cls_pull hQ, cls_pull hE, eL, eR]

end GlobalTheory.E8LatticePullbackGeneric

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem isPPFib_baseChange : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] (g : ℕ) (M : RigLB G), E8Fibration.IsPPFib G g M → ∃ M' : RigLB ((Over.pullback f).obj G), M'.L = M.L.pull (pullback.fst G.hom f) ∧ E8Fibration.IsPPFib ((Over.pullback f).obj G) g M' := by
  intro S S' f G _ g M hM
  obtain ⟨hA, hg, ⟨c⟩, ha, hK⟩ := hM
  have hA' : IsAbelianScheme ((Over.pullback f).obj G) := by
    have := hA.comm
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · change Smooth (pullback.snd G.hom f)
      infer_instance
    · change IsProper (pullback.snd G.hom f)
      infer_instance
    · change GeometricallyConnected (pullback.snd G.hom f)
      infer_instance
  have := hA.comm
  have := hA'.comm
  have := hA.proper
  have h := isGrpPullback_pullback G f
  obtain ⟨hL, hr, c', -⟩ := GlobalTheory.PullSharp.cube_pull_sharp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubeMapOf h) M c
  obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl hL
  exact ⟨(ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubeMapOf h).rigLB M hL hr, rfl, hA',
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hg, ⟨c'⟩,
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback M.isLB ha h.1,
    kTriv_pull h M.isLB hL ((isGen_iff w).1 hw) hK⟩

end GlobalTheory.Poinc.Sep.E8Fibration

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration.FactorBasis

theorem omegaStd_eq_sum (g : ℕ) (a b : Fin g ⊕ Fin g → ℤ) :
    omegaStd a b = ∑ c, ∑ d, Out.stdSymp g (((finCongr (two_mul g)).trans finSumFinEquiv.symm).symm c)
      (((finCongr (two_mul g)).trans finSumFinEquiv.symm).symm d) * (a c * b d) := by
  set σ : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm with hσ
  have l : ∀ a, (σ.symm (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (σ.symm (.inr a) : ℕ) = g + a := fun _ => rfl
  have ll : ∀ i j, Out.stdSymp g (σ.symm (.inl i)) (σ.symm (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r]; split_ifs <;> omega
  have rr : ∀ i j, Out.stdSymp g (σ.symm (.inr i)) (σ.symm (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r]; split_ifs <;> omega
  have lr : ∀ i j, Out.stdSymp g (σ.symm (.inl i)) (σ.symm (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]; split_ifs <;> omega
  have rl : ∀ i j, Out.stdSymp g (σ.symm (.inr i)) (σ.symm (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]; split_ifs <;> omega
  simp only [Fintype.sum_sum_type, ll, rr, lr, rl, omegaStd, Finset.sum_sub_distrib]
  simp [sub_eq_add_neg]

theorem exists_family {N g : ℕ} (hN : Odd N) {T R : Type} [CommGroup T] [CommRing R] [IsDomain R] {z : Rˣ}
    (hz : IsPrimitiveRoot z N) (hT : ∀ x : T, x ^ N = 1)
    (hc : ∀ d : ℕ, d ∣ N → Nat.card {x : T // x ^ d = 1} = d ^ (2 * g))
    (E : Matrix (Fin 8) (Fin 8) ℤ) (hE : E.transpose = E) (hdet : E.det = 1)
    (e : (Fin 8 → T) →* (Fin 8 → T) →* Rˣ) (halt : ∀ x, e x x = 1) (hnd : ∀ x, (∀ y, e x y = 1) → x = 1)
    (hrel : ∀ s t s' t' : Fin 8 → ℤ, dotProduct s (E.mulVec t) = dotProduct s' (E.mulVec t') → ∀ p q : T,
      e (fun u => p ^ s u) (fun u => q ^ t u) = e (fun u => p ^ s' u) (fun u => q ^ t' u)) :
    ∃ b : Fin g ⊕ Fin g → T, ∀ x y : Fin 8 → (Fin g ⊕ Fin g → ℤ),
      e (fun u => ∏ c, b c ^ x u c) (fun u => ∏ c, b c ^ y u c) = z ^ ∑ u, ∑ v, E u v * omegaStd (x u) (y v) := by
  let s₀ : Fin 8 → ℤ := Pi.single 0 1
  let t₀ : Fin 8 → ℤ := E.adjugate.mulVec s₀
  have h₀ : dotProduct s₀ (E.mulVec t₀) = 1 := by
    simp only [t₀, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mulVec]
    simp [s₀]
  have h₀' : dotProduct t₀ (E.mulVec s₀) = 1 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hE, dotProduct_comm, h₀]
  let pw : (Fin 8 → ℤ) → T →* (Fin 8 → T) := fun s =>
    MonoidHom.mk' (fun p u => p ^ s u) fun p q => funext fun u => mul_zpow p q _
  let h : T →* T →* Rˣ := ((e.comp (pw s₀)).flip.comp (pw t₀)).flip
  have hh : ∀ p q, h p q = e (fun u => p ^ s₀ u) (fun u => q ^ t₀ u) := fun _ _ => rfl
  have key : ∀ (s t : Fin 8 → ℤ) (p q : T),
      e (fun u => p ^ s u) (fun u => q ^ t u) = h p q ^ dotProduct s (E.mulVec t) := fun s t p q => by
    rw [hrel s t (dotProduct s (E.mulVec t) • s₀) t₀ (by rw [smul_dotProduct, h₀, smul_eq_mul, _root_.mul_one]), hh,
      ← MonoidHom.zpow_apply, ← map_zpow]
    congr 2
    funext u
    change p ^ (dotProduct s (E.mulVec t) * s₀ u) = (p ^ s₀ u) ^ dotProduct s (E.mulVec t)
    rw [← zpow_mul, _root_.mul_comm]
  have eskew : ∀ x y, e x y * e y x = 1 := fun x y => by
    have := halt (x * y)
    simp only [map_mul, MonoidHom.mul_apply, halt, _root_.one_mul, _root_.mul_one] at this
    first | exact this | (rw [_root_.mul_comm]; exact this)
  have halt' : ∀ p, h p p = 1 := fun p => by
    have k₁ : h p p ^ 2 = 1 := by
      have := eskew (fun u => p ^ s₀ u) (fun u => p ^ t₀ u)
      rwa [key, key, h₀, h₀', zpow_one, ← pow_two] at this
    have k₂ : h p p ^ N = 1 := by rw [← map_pow, hT, map_one]
    obtain ⟨m, rfl⟩ := hN
    rwa [pow_succ, pow_mul, k₁, one_pow, _root_.one_mul] at k₂
  have hnd' : ∀ p, (∀ q, h p q = 1) → p = 1 := fun p hp => by
    have := hnd (fun u => p ^ s₀ u) fun y => by
      have hy : y = ∏ v, fun u => y v ^ (Pi.single v 1 : Fin 8 → ℤ) u := by
        funext u
        rw [Finset.prod_apply, Finset.prod_eq_single u (fun v _ hv => by simp [Pi.single_apply, hv.symm]) (by simp)]
        simp
      rw [hy, map_prod]
      exact Finset.prod_eq_one fun v _ => by rw [key, hp, one_zpow]
    simpa [s₀] using congrFun this 0
  obtain ⟨v, hv⟩ := exists_stdSymp_of_alternating_pairing N g T R z hN.pos hz hT hc h halt' hnd'
  let σ : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm
  refine ⟨fun c => v (σ.symm c), fun x y => ?_⟩
  have hp : ∀ x : Fin 8 → (Fin g ⊕ Fin g → ℤ),
      (fun u => ∏ c, v (σ.symm c) ^ x u c) = ∏ c, fun u => v (σ.symm c) ^ x u c := fun x =>
    funext fun u => by rw [Finset.prod_apply]
  rw [hp, hp]
  have heval (f : (Fin g ⊕ Fin g) → ((Fin 8 → T) →* Rˣ)) (a : Fin 8 → T) :
      (∏ c, f c) a = ∏ c, f c a := by
    exact map_prod (MonoidHom.eval a) f Finset.univ
  simp only [map_prod, heval, key, hv, ← zpow_mul]
  rw [Finset.prod_comm]
  have zs : ∀ {α : Type} [Fintype α] (f : α → ℤ), ∏ a, z ^ f a = z ^ ∑ a, f a := fun f =>
    (map_prod (zpowersHom Rˣ z) (fun a => Multiplicative.ofAdd (f a)) Finset.univ).symm
  simp only [zs]
  congr 1
  simp only [omegaStd_eq_sum, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun u _ => ?_))
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun u' _ => ?_))
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [σ]
  ring

theorem exists_basis : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ N : ℕ), Odd N → ∀ (K : Type) [Field K] [IsAlgClosed K], (N : K) ≠ 0 →
  ∀ (z : Kˣ), IsPrimitiveRoot z N → ∀ (P' : PolAV (Sp K)), P'.g = 8 * gQ →
  ∀ (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (P'.A ⟶ B)), E8Fibration.IsProd pr →
  (∀ (s t s' t' : Fin 8 → ℤ), dotProduct s ((E8Fibration.e8 W).mulVec t) = dotProduct s' ((E8Fibration.e8 W).mulVec t') →
    ∀ (p q : Out.baseOver (Sp K) ⟶ B), p ^ N = 1 → q ^ N = 1 →
    ∀ (x y x' y' : Out.baseOver (Sp K) ⟶ P'.A), (∀ u, x ≫ pr u = p ^ s u) → (∀ u, y ≫ pr u = q ^ t u) →
      (∀ u, x' ≫ pr u = p ^ s' u) → (∀ u, y' ≫ pr u = q ^ t' u) →
      ∀ c, Out.WeilIs P'.A P'.L N x y c → Out.WeilIs P'.A P'.L N x' y' c) →
  ∃ b : Fin gQ ⊕ Fin gQ → (Out.baseOver (Sp K) ⟶ B), (∀ c, b c ^ N = 1) ∧
    ∀ (x y : Fin 8 → (Fin gQ ⊕ Fin gQ → ℤ)) (X Y : Out.baseOver (Sp K) ⟶ P'.A),
      (∀ u, X ≫ pr u = ∏ c, b c ^ x u c) → (∀ u, Y ≫ pr u = ∏ c, b c ^ y u c) →
      Out.WeilIs P'.A P'.L N X Y (unitOn z ^ ∑ u, ∑ v, E8Fibration.e8 W u v * omegaStd (x u) (y v)) := by
  intro W hW g N hN K _ _ hK z hz P hg B _ _ pr hpr hrel
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have : IsDomain Γ(Sp K, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have hz' : IsPrimitiveRoot (unitOn z) N :=
    hz.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)
      (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1)
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P N (Out.baseOver _)
  have hmon := hpr.1
  let φ₀ : (Out.baseOver (Sp K) ⟶ P.A) →* (Fin 8 → (Out.baseOver (Sp K) ⟶ B)) :=
    MonoidHom.mk' (fun x u => x ≫ pr u) fun x y => funext fun u => MonObj.mul_comp _ _ _
  have hφ : Function.Bijective φ₀ :=
    ⟨fun x y h => (hpr.2 _ (φ₀ y)).unique (fun u => congrFun h u) fun _ => rfl,
      fun y => (hpr.2 _ y).exists.imp fun x hx => funext hx⟩
  let φ := MulEquiv.ofBijective φ₀ hφ
  have φa : ∀ x u, φ x u = x ≫ pr u := fun _ _ => rfl
  let T : Subgroup (Out.baseOver (Sp K) ⟶ B) := (powMonoidHom N).ker
  let ψ : (Fin 8 → T) →* (Out.baseOver (Sp K) ⟶ P.A) :=
    φ.symm.toMonoidHom.comp (T.subtype.compLeft (Fin 8))
  have ψa : ∀ x u, ψ x ≫ pr u = (x u).1 := fun x u =>
    (φa _ u).symm.trans (congrFun (φ.apply_symm_apply _) u)
  have hT : ∀ x : T, x ^ N = 1 := fun x => Subtype.ext x.2
  have ψt : ∀ x, ψ x ^ N = 1 := fun x => by
    rw [← map_pow, show x ^ N = 1 from funext fun u => hT _, map_one]
  have ψs : ∀ y : Out.baseOver (Sp K) ⟶ P.A, y ^ N = 1 → ∃ x, ψ x = y := fun y hy =>
    ⟨fun u => ⟨φ y u, by
      show φ y u ^ N = 1
      rw [← Pi.pow_apply, ← map_pow, hy, map_one, Pi.one_apply]⟩, φ.symm_apply_apply y⟩
  choose w hw hw' using fun x y : Fin 8 → T => w₁ _ _ (ψt x) (ψt y)
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (by rw [map_mul]; exact w₂ _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (CommPairing.weilIs_symm P.isLB (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  let e : (Fin 8 → T) →* (Fin 8 → T) →* Γ(Sp K, ⊤)ˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x))
    fun x x' => MonoidHom.ext fun y => wl x x' y
  have hc : ∀ d : ℕ, d ∣ N → Nat.card {x : T // x ^ d = 1} = d ^ (2 * g) := fun d hd => by
    have hA : Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} = d ^ (2 * P.g) :=
      (hL.mulN _ P d (Nat.pos_of_dvd_of_pos hd hN.pos)).2.2.2.2 K (𝟙 _) (by
        obtain ⟨e, rfl⟩ := hd
        rw [Nat.cast_mul] at hK
        exact left_ne_zero_of_mul hK)
    let F : (Fin 8 → {x : T // x ^ d = 1}) → {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} := fun x =>
      ⟨ψ fun u => (x u).1, by
        rw [← map_pow, show (fun u => (x u).1) ^ d = 1 from funext fun u => (x u).2, map_one]⟩
    have hF : Function.Bijective F := by
      refine ⟨fun x y h => funext fun u => Subtype.ext (Subtype.ext ?_), fun y => ?_⟩
      · have h' : ψ (fun u => (x u).1) = ψ fun u => (y u).1 := congrArg Subtype.val h
        rw [← ψa (fun u => (x u).1) u, h', ψa]
      · obtain ⟨x, hx⟩ := ψs y.1 (by
          obtain ⟨c, hc⟩ := hd
          rw [hc, pow_mul, y.2, one_pow])
        refine ⟨fun u => ⟨x u, Subtype.ext ?_⟩, Subtype.ext hx⟩
        show (x u).1 ^ d = 1
        rw [← ψa, hx, ← φa, ← Pi.pow_apply, ← map_pow, y.2, map_one, Pi.one_apply]
    have h := Nat.card_eq_of_bijective F hF
    rw [hA, hg, Nat.card_fun, Nat.card_fin, show 2 * (8 * g) = 2 * g * 8 by ring, pow_mul] at h
    exact Nat.pow_left_injective (by norm_num) h
  obtain ⟨b, hb⟩ := exists_family (g := g) hN hz' hT hc (E8Fibration.e8 W)
    (by simp [e8, Matrix.transpose_add, add_comm]) hW.2 e
    (fun x => (hw' _ _ _ (w₃ _ (ψt x))).symm)
    (fun x hx => by
      have h1 : ψ x = 1 := hL.weilNondeg K P N hK _ (ψt x) fun y hy => by
        obtain ⟨y, rfl⟩ := ψs y hy
        have h : w x y = 1 := hx y
        exact h ▸ hw x y
      funext u
      exact Subtype.ext (by rw [← ψa, h1, ← φa, map_one]; rfl))
    (fun s t s' t' h p q => hw' _ _ _ (hrel s t s' t' h p.1 q.1 p.2 q.2 _ _ _ _
      (fun u => ψa _ u) (fun u => ψa _ u) (fun u => ψa _ u) (fun u => ψa _ u) _ (hw _ _)))
  refine ⟨fun c => (b c).1, fun c => (b c).2, fun x y X Y hX hY => ?_⟩
  have hp : ∀ (x : Fin 8 → (Fin g ⊕ Fin g → ℤ)) (X : Out.baseOver (Sp K) ⟶ P.A),
      (∀ u, X ≫ pr u = ∏ c, (b c).1 ^ x u c) → X = ψ fun u => ∏ c, b c ^ x u c := fun x X hX =>
    hφ.1 (funext fun u => (hX u).trans (Eq.symm ((ψa _ u).trans (by simp))))
  rw [hp x X hX, hp y Y hY, ← hb x y]
  exact hw _ _

end GlobalTheory.Poinc.Sep.E8Fibration.FactorBasis
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

def sharpBasis (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) :
    (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
  (sharpReindex h).trans
    { twistSnd (e8 W).adjugate with
      invFun := twistSnd (e8 W)
      left_inv := twistSnd_twistSnd _ _ (by rw [Matrix.mul_adjugate, hW, one_smul])
      right_inv := twistSnd_twistSnd _ _ (by rw [Matrix.adjugate_mul, hW, one_smul]) }

theorem isSharpBasis_sharpBasis (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) :
    IsSharpBasis W (sharpBasis W hW h) := by
  intro i j
  rw [← sum_omegaStd_single h i j]
  exact sum_omegaStd_twistSnd (e8 W) _ (by simp [e8, Matrix.transpose_add, add_comm])
    (by rw [Matrix.mul_adjugate, hW, one_smul]) _ _

def labMat (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) (a : Fin 2) :
    Matrix (Fin (2 * (8 * h))) (Fin (2 * (8 * h))) ℤ :=
  fun i' i => (sharpBasis W hW h).symm
    (fun u c => ∑ v, actMat W a u v * sharpBasis W hW h (Pi.single i 1) v c) i'

variable {S : Scheme.{0}}

def ptOf {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] {pr : Fin 8 → (A ⟶ B)} (hP : IsProd pr)
    {T : Over S} {C : Type} [Fintype C] (b : C → (T ⟶ B)) (x : Fin 8 → C → ℤ) : T ⟶ A :=
  (hP.2 T fun u => ∏ c, b c ^ x u c).exists.choose

theorem ptOf_pr {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] {pr : Fin 8 → (A ⟶ B)} (hP : IsProd pr)
    {T : Over S} {C : Type} [Fintype C] (b : C → (T ⟶ B)) (x : Fin 8 → C → ℤ) (u : Fin 8) :
    ptOf hP b x ≫ pr u = ∏ c, b c ^ x u c :=
  (hP.2 T fun u => ∏ c, b c ^ x u c).exists.choose_spec u

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

namespace GlobalTheory.Mum.Desc

theorem isActOf_secExt : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (x : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → SymLift A.A A.L N N (baseEm em ≫ x) θ' → ∀ t t' : SecF A (Kb R) N, IsActOf A.A A.L N θ t t' → IsActOf A.A A.L N θ' (secExt A em N t) (secExt A em N t') := by
  intro R _ _ A F _ _ em N hN x θ θ' H H' t t' a
  exact GlobalTheory.WeightProbe.act_pull A hN (baseEm em) H H' a

end GlobalTheory.Mum.Desc
end
