module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeviProjectionDenominatorsOfHypotheses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle898
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke

theorem left_comp_of_comp {S : Scheme.{0}} {X Y Z : Over S} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) :
    f.left ≫ g.left = h.left := by
  rw [← Over.comp_left, e]

theorem exists_birigidified_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsMonHom ψ → ∀ (m : ℕ) (P₀ : LB (G2 A').left), P₀.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  intro p _ D R _ b M S s o A' _ _ ψ hψ m P₀ hP₀ H
  let φ : Fin 4 → ((G2 A').left ⟶ (G2 A').left) := ![𝟙 _, (lift (fst A' A') (1 : G2 A' ⟶ A')).left,
    (lift (1 : G2 A' ⟶ A') (snd A' A')).left, (lift (1 : G2 A' ⟶ A') (1 : G2 A' ⟶ A')).left]
  let ε : Fin 4 → ℤ := ![1, -1, -1, 1]
  have hε : ε 0 = 1 ∧ ε 1 = -1 ∧ ε 2 = -1 ∧ ε 3 = 1 := ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨LB.LinComb P₀ φ ε, DVR.linComb_isLB P₀ hP₀ φ ε, ?_, ?_, ?_⟩
  · refine GlobalTheory.PrimNorm.hasGen_nested hP₀ φ ε (fun _ : PUnit => _) (fun _ => 1) ?_
    have e0 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 0 = (lift (1 : A' ⟶ A') (𝟙 A')).left := Category.comp_id _
    have e1 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 1 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e2 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 2 = (lift (1 : A' ⟶ A') (𝟙 A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e3 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 3 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_four, e0, e1, e2, e3]
    rw [hε.1, hε.2.1, hε.2.2.1, hε.2.2.2, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one,
      mul_right_comm _ _ (GlobalTheory.PrimNorm.cls P₀ _)⁻¹, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
  · refine GlobalTheory.PrimNorm.hasGen_nested hP₀ φ ε (fun _ : PUnit => _) (fun _ => 1) ?_
    have e0 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 0 = (lift (𝟙 A') (1 : A' ⟶ A')).left := Category.comp_id _
    have e1 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 1 = (lift (𝟙 A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e2 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 2 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e3 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 3 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_four, e0, e1, e2, e3]
    rw [hε.1, hε.2.1, hε.2.2.1, hε.2.2.2, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one,
      mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
  · haveI := hψ
    let ρ : Fin 4 → ((G2 o.A).left ⟶ (G2 o.A).left) := ![𝟙 _, (lift (fst o.A o.A) (1 : G2 o.A ⟶ o.A)).left,
      (lift (1 : G2 o.A ⟶ o.A) (snd o.A o.A)).left, (lift (1 : G2 o.A ⟶ o.A) (1 : G2 o.A ⟶ o.A)).left]
    have hsq : ∀ k, sq2 ψ ≫ φ k = ρ k ≫ sq2 ψ := by
      intro k
      fin_cases k
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      all_goals
        refine (left_comp_of_comp rfl).trans ((left_comp_of_comp ?_).symm)
        apply CartesianMonoidalCategory.hom_ext <;> simp
    have hP := o.isLB
    have cls1 : ∀ (r : (G2 o.A).left ⟶ (G2 o.A).left),
        GlobalTheory.MulPull.HasGen o.P (fun _ : PUnit => r) (fun _ => 1) → GlobalTheory.PrimNorm.cls o.P r = 1 := by
      intro r h
      have := (GlobalTheory.PrimNorm.hasGen_iff hP _ _).1 h
      rwa [Fintype.prod_unique, zpow_one] at this
    have h1 : GlobalTheory.PrimNorm.cls o.P (ρ 1) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left)
        (ε := fun _ => 1) o.rig₂ (fst o.A o.A).left
      have e : (fst o.A o.A).left ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left = ρ 1 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have h2 : GlobalTheory.PrimNorm.cls o.P (ρ 2) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left)
        (ε := fun _ => 1) o.rig₁ (snd o.A o.A).left
      have e : (snd o.A o.A).left ≫ (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left = ρ 2 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have h3 : GlobalTheory.PrimNorm.cls o.P (ρ 3) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left)
        (ε := fun _ => 1) o.rig₂ (fst o.A o.A ≫ (1 : o.A ⟶ o.A)).left
      have e : (fst o.A o.A ≫ (1 : o.A ⟶ o.A)).left ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left = ρ 3 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have L1 : (lbPow o.P m).IsLB := DVR.linComb_isLB o.P hP _ _
    have L2 : (LB.LinComb (lbPow o.P m) ρ ε).IsLB := DVR.linComb_isLB _ L1 _ _
    have L3 : (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε).IsLB := DVR.linComb_isLB _ hP₀ _ _
    have L4 : ((LB.LinComb P₀ φ ε).pull (sq2 ψ)).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ hP₀ _ _) _ _
    have I1 : LBIso (lbPow o.P m) (LB.LinComb (lbPow o.P m) ρ ε) := by
      refine LBIso.symm (GlobalTheory.PrimNorm.lbIso_nested hP (fun _ : Fin m => 𝟙 _) (fun _ => 1) ρ ε
        (fun _ : Fin m => 𝟙 _) (fun _ => 1) ?_)
      simp only [Category.comp_id, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Fin.prod_univ_four, h1, h2, h3, one_pow, one_zpow, _root_.mul_one, hε.1]
      rfl
    obtain ⟨w, hw⟩ := H
    have I2 : LBIso (LB.LinComb (lbPow o.P m) ρ ε) (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε) :=
      iso_linComb ((isGen_iff w).1 hw) ρ ε
    have I3 : LBIso (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε) ((LB.LinComb P₀ φ ε).pull (sq2 ψ)) := by
      refine LBIso.symm (GlobalTheory.PrimNorm.lbIso_nested hP₀ φ ε (fun _ : PUnit => sq2 ψ) (fun _ => 1)
        (fun k => ρ k ≫ sq2 ψ) ε ?_)
      rw [Fintype.prod_unique, zpow_one]
      exact Finset.prod_congr rfl fun k _ => by rw [hsq k]
    exact LBIso.trans L1 L2 L4 I1 (LBIso.trans L2 L3 L4 I2 I3)
end GlobalTheory.UPel.HT.Hecke
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{0}}

def RosatiFor (D : Datum p) {A : Over S} [GrpObj A] (act : OActN D.O A) (P : LB (G2 A).left) : Prop :=
  ∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)

def EtaOK (D : Datum p) (N : ℕ) {A : Over S} [GrpObj A] (act : OActN D.O A) (eta : D.La → (𝟙_ (Over S) ⟶ A)) :
    Prop :=
  (∀ x y, eta (x + y) = eta x * eta y) ∧ (∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c) ∧ ∀ x, eta (N • x) = 1

def GeomAt (D : Datum p) (N : ℕ) {A : Over S} [GrpObj A] (act : OActN D.O A) (P : LB (G2 A).left)
    (eta : D.La → (𝟙_ (Over S) ⟶ A)) (k : Type) [Field k] (x : Sp k ⟶ S) : Prop :=
  ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
      (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)),
    ∀ y, toUnit _ ≫ eta y = I.ev N y

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {s : S ⟶ Sp R}

theorem Obj.rosatiFor (o : Obj b N s) : RosatiFor D o.act o.P := o.rosati

theorem Obj.etaOK (o : Obj b N s) : EtaOK D N o.act o.eta := ⟨o.eta_add, o.eta_lin, o.eta_ker⟩

theorem Obj.geomAt (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k)
    (hx : x ≫ s = spMap β) : GeomAt D N o.act o.P o.eta k x := o.geom k x β hx

theorem Obj.lieHer (o : Obj b N s) (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S)
    (hx : x ≫ s = spMap β) : LieHer b o.act β x := by
  intro R'' _ g
  have e₁ : (spMap g ≫ x) ≫ s = spMap (g.comp β) := by
    rw [Category.assoc, hx]
    simp [spMap, ← Spec.map_comp]
    try rfl
  refine ⟨o.lie R'' (g.comp β) (spMap g ≫ x) e₁, fun k _ _ g' i => ?_⟩
  refine o.lieRank k (spMap g' ≫ spMap g ≫ x) (g'.comp (g.comp β)) ?_ i
  rw [Category.assoc, Category.assoc, hx]
  simp [spMap, ← Spec.map_comp]
  try rfl

theorem RosatiFor.of_iso {A : Over S} [GrpObj A] {act : OActN D.O A} {P P' : LB (G2 A).left} (hP : P.IsLB)
    (hP' : P'.IsLB) (H : LBIso P P') (h : RosatiFor D act P) : RosatiFor D act P' := fun c =>
  LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB hP' _)
    (GlobalTheory.RigidBundleGlue.LBIso.pull H _).symm
    (LBIso.trans (pull_isLB hP _) (pull_isLB hP _) (pull_isLB hP' _) (h c) (GlobalTheory.RigidBundleGlue.LBIso.pull H _))

end GlobalTheory.UPel.HT
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixMatCond

theorem eq_θ {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) {Y : Scheme.{0}} (φ : Y ⟶ A.left)
    (ψ : Y ⟶ (topS Rg ⊗ A).left) (h : ψ ≫ (snd (topS Rg) A).left = φ) : ψ = φ ≫ θ A := by
  let Y0 : Over (Sp Rg) := Over.mk (φ ≫ A.hom)
  have w1 : ψ ≫ (topS Rg ⊗ A).hom = Y0.hom := by
    show _ = φ ≫ A.hom
    rw [← h, Category.assoc, Over.w (snd (topS Rg) A)]
  have w2 : (φ ≫ θ A) ≫ (topS Rg ⊗ A).hom = Y0.hom := by
    show _ = φ ≫ A.hom
    rw [Category.assoc, ← Over.w (snd (topS Rg) A), ← Category.assoc (θ A), θ_snd, Category.id_comp]
  let u : Y0 ⟶ topS Rg ⊗ A := Over.homMk ψ w1
  let v : Y0 ⟶ topS Rg ⊗ A := Over.homMk (φ ≫ θ A) w2
  have : u = v := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      haveI : Mono (topS Rg).hom := by dsimp [topS, overRes]; infer_instance
      rw [← cancel_mono (topS Rg).hom]
      simp only [Over.comp_left, Category.assoc, Over.w]
      try exact w1.trans w2.symm
    · ext
      simp only [Over.comp_left, u, v, Over.homMk_left, Category.assoc, θ_snd, Category.comp_id, h]
  exact congrArg CommaMorphism.left this

theorem gs_sum' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ}
    (a : Fin n → Γ(X, U)) : gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem gs_pow' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (t : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (t z) ∈ U)
    (f : Γ(X, U)) : gs (t ≫ g) z U f = (t.stalkMap z).hom (gs g (t z) U f) := by
  rw [← gs_pull t g z U h, gs_stalkMap t z _ h, gs_pull (𝟙 _) g (t z) U h, Category.id_comp]

theorem gs_appTop' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (a : Γ(X, ⊤)) :
    gs (𝟙 Y) y ⊤ (f.appTop.hom a) = gs f y ⊤ a :=
  (gs_pull (𝟙 _) f y ⊤ trivial a).trans (by rw [Category.id_comp])

theorem mem_wchart_one {X Y : Scheme.{0}} (L : LB X) (m : Y ⟶ X) (j : Fin 1 → L.ι) (y : Y) :
    y ∈ LB.wchart L (fun _ : Fin 1 => m) j ↔ m y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun i => by rw [Fin.fin_one_eq_zero i]; exact h⟩

theorem mem_wchart_unit {X Y : Scheme.{0}} (L : LB X) (m : Y ⟶ X) (q : L.ι) (y : Y) :
    y ∈ LB.wchart L (fun _ : PUnit => m) (fun _ => q) ↔ m y ∈ L.U q :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem app_of_comp {X Y Z : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (x : X) :
    g (f x) = h x := by
  rw [← e]; rfl

theorem mem_wchart_comp {X Y Z : Scheme.{0}} (L : LB X) (f : Z ⟶ Y) (g : Y ⟶ X) (j : Fin 1 → L.ι) (z : Z)
    (h : f z ∈ LB.wchart L (fun _ : Fin 1 => g) j) : (𝟙 Z) z ∈ LB.wchart L (fun _ : Fin 1 => f ≫ g) j :=
  (mem_wchart_one L (f ≫ g) j ((𝟙 Z) z)).2 ((mem_wchart_one L g j (f z)).1 h)

end GlobalTheory.HomFixMatCond

namespace GlobalTheory.HomFixMatCond

theorem mat_cond : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c ∧ GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c ∧ GlobalTheory.HomFixUniv.Normal t c αA βB := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c hL hM hcov hvA hvB hT hMat
  obtain ⟨hpA, hpB, hΦ, -⟩ := hT
  obtain ⟨ψA, ψB, α, hA, hB, -, hnorm, hmat⟩ := hMat
  obtain rfl := eq_θ A φA' ψA hA
  obtain rfl := eq_θ B φB' ψB hB
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ A'.left) (z : Z) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι))
      (_ : r z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (j : Fin mB),
      gs (r ≫ Φ'.left ≫ φB' ≫ θ B) z ((LPow B M (k : ℤ) (topS Rg)).U p.1) ((bB j).f p.1) =
        gs r z _ (α.s p).val * ∑ i, gs (r ≫ A'.hom) z ⊤ (c i j) *
          gs (r ≫ φA' ≫ θ A) z ((LPow A L (k : ℤ) (topS Rg)).U p.2) ((bA i).f p.2) := by
    intro Z r z p hz j
    have e := congrArg (gs r z _) (hmat j p)
    erw [gs_appLE _ _ _ _ r z hz, gs_mul r z _ hz, gs_sum' r z _ hz] at e
    refine Eq.trans ?_ (e.trans ?_)
    · rfl
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [gs_mul r z _ hz]
      erw [gs_appLE _ _ _ _ r z hz, gs_appLE _ _ _ _ r z hz]
      all_goals rfl
  refine ⟨?_, ?_, ?_⟩
  · intro z q hq
    have hz : (Φ'.left ≫ φB' ≫ θ B) z ∈ ⨆ j, nonzeroLocus (bB j) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    unfold nonzeroLocus at hj
    obtain ⟨kk, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
    have hkU := (topS Rg ⊗ B).left.basicOpen_le _ hk
    have hzU : (𝟙 A'.left) z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U (kk, q) :=
      ⟨mem_wchart_comp _ _ _ _ _ hkU, mem_wchart_comp _ _ _ _ _ hq⟩
    have e := key (𝟙 _) z (kk, q) hzU j
    simp only [Category.id_comp] at e
    refine ⟨j, ?_⟩
    have hu : IsUnit (gs (Φ'.left ≫ φB' ≫ θ B) z _ ((bB j).f kk)) := by
      rw [gs_eq _ _ _ hkU]
      have : z ∈ A'.left.basicOpen (((Φ'.left ≫ φB' ≫ θ B).app _).hom ((bB j).f kk)) := by
        rw [← Scheme.preimage_basicOpen]; exact hk
      exact (Scheme.mem_basicOpen _ _ _ _).1 this
    rw [e] at hu
    exact isUnit_of_mul_isUnit_right hu
  · intro z q kk hq hk j j'
    have hzU : (𝟙 A'.left) z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U (kk, q) :=
      ⟨mem_wchart_comp _ _ _ _ _ hk, mem_wchart_comp _ _ _ _ _ hq⟩
    have e1 := key (𝟙 _) z (kk, q) hzU j
    have e2 := key (𝟙 _) z (kk, q) hzU j'
    simp only [Category.id_comp] at e1 e2
    have hc : ∀ j, comb bA (φA' ≫ θ A) A'.hom c z q j = ∑ i, gs A'.hom z ⊤ (c i j) *
        gs (φA' ≫ θ A) z ((LPow A L (k : ℤ) (topS Rg)).U q) ((bA i).f q) := fun _ => rfl
    rw [hc, hc, e1, e2]
    ring
  · intro j
    apply fn_ext
    intro x _
    obtain ⟨qA, hqA⟩ := exists_chart hL (eSec A (t x))
    obtain ⟨qB, hqB⟩ := exists_chart hM (eSec B (t x))
    have F2 : zeroPt A' ≫ φA' = t ≫ eSec A := GlobalTheory.PolBaseChange.eSec_comm hpA
    have F3 : zeroPt A' ≫ Φ'.left ≫ φB' = t ≫ eSec B := by
      have h0 : zeroPt A' ≫ Φ'.left = zeroPt B' := by
        show η[A'].left ≫ Φ'.left = η[B'].left
        rw [← Over.comp_left, IsMonHom.one_hom]
      rw [← Category.assoc, h0]; exact GlobalTheory.PolBaseChange.eSec_comm hpB
    have F1 : zeroPt A' ≫ A'.hom = 𝟙 _ := Over.w η[A']
    have GA : zeroPt A' ≫ φA' ≫ θ A = t ≫ eSec A ≫ θ A := by rw [reassoc_of% F2]
    have GB : zeroPt A' ≫ Φ'.left ≫ φB' ≫ θ B = t ≫ eSec B ≫ θ B := by rw [reassoc_of% F3]
    let p : (Fin 1 → M.ι) × (Fin 1 → L.ι) := (fun _ => qB, fun _ => qA)
    have hx0 : zeroPt A' x ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p := by
      refine ⟨(mem_wchart_one _ _ _ _).2 ?_, (mem_wchart_one _ _ _ _).2 ?_⟩
      · rw [app_of_comp (f := zeroPt A') (g := (Φ'.left ≫ φB' ≫ θ B) ≫ (snd (topS Rg) B).left)
          (h := t ≫ eSec B) (by simp only [Category.assoc, θ_snd, Category.comp_id]; exact F3)]
        exact hqB
      · rw [app_of_comp (f := zeroPt A') (g := (φA' ≫ θ A) ≫ (snd (topS Rg) A).left)
          (h := t ≫ eSec A) (by simp only [Category.assoc, θ_snd, Category.comp_id]; exact F2)]
        exact hqA
    have hmemA : (eSec A ≫ θ A) (t x) ∈ (LPow A L (k : ℤ) (topS Rg)).U p.2 := by
      refine (mem_wchart_one _ _ _ _).2 ?_
      rw [app_of_comp (f := eSec A ≫ θ A) (g := (snd (topS Rg) A).left) (h := eSec A)
        (by rw [Category.assoc, θ_snd, Category.comp_id])]
      exact hqA
    have hmemB : (eSec B ≫ θ B) (t x) ∈ (LPow B M (k : ℤ) (topS Rg)).U p.1 := by
      refine (mem_wchart_one _ _ _ _).2 ?_
      rw [app_of_comp (f := eSec B ≫ θ B) (g := (snd (topS Rg) B).left) (h := eSec B)
        (by rw [Category.assoc, θ_snd, Category.comp_id])]
      exact hqB
    have hWA : t x ∈ (L.pull (eSec A)).U (fun _ => p.2 0) := (mem_wchart_unit _ _ _ _).2 hqA
    have hWB : t x ∈ (M.pull (eSec B)).U (fun _ => p.1 0) := (mem_wchart_unit _ _ _ _).2 hqB
    have hIA : ∀ i, gs (t ≫ eSec A ≫ θ A) x ((LPow A L (k : ℤ) (topS Rg)).U p.2) ((bA i).f p.2) =
        gs t x ⊤ (αA i) * gs t x _ (eA.s (fun _ => qA)).val ^ k := by
      intro i
      rw [gs_comp_stalk _ _ _ _ hmemA, hvA i (t x) p.2 hmemA, map_mul]
      congr 1
      · exact (gs_stalkMap t x ⊤ trivial _).symm
      · show (t.stalkMap x).hom ((gm (𝟙 _) (t x) _ (eA.s _)) ^ k).val = _
        rw [Units.val_pow_eq_pow_val, map_pow, ← gs_unit (𝟙 _) (t x) _ hWA, ← gs_stalkMap t x _ hWA]
    have hIB : gs (t ≫ eSec B ≫ θ B) x ((LPow B M (k : ℤ) (topS Rg)).U p.1) ((bB j).f p.1) =
        gs t x ⊤ (βB j) * gs t x _ (eB.s (fun _ => qB)).val ^ k := by
      rw [gs_comp_stalk _ _ _ _ hmemB, hvB j (t x) p.1 hmemB, map_mul]
      congr 1
      · exact (gs_stalkMap t x ⊤ trivial _).symm
      · show (t.stalkMap x).hom ((gm (𝟙 _) (t x) _ (eB.s _)) ^ k).val = _
        rw [Units.val_pow_eq_pow_val, map_pow, ← gs_unit (𝟙 _) (t x) _ hWB, ← gs_stalkMap t x _ hWB]
    have hxW : (𝟙 (Sp R)) x ∈ (zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p ⊓
        t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
        t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0) := ⟨⟨hx0, hWA⟩, hWB⟩
    have hN : gs (zeroPt A') x _ (α.s p).val * gs t x _ (eA.s (fun _ => qA)).val ^ k =
        gs t x _ (eB.s (fun _ => qB)).val ^ k := by
      have e := congrArg (gs (𝟙 (Sp R)) x _) (hnorm p)
      rw [gs_mul _ _ _ hxW, gs_pow' _ _ _ hxW, gs_pow' _ _ _ hxW] at e
      erw [gs_appLE _ _ _ _ _ x hxW, gs_appLE _ _ _ _ _ x hxW, gs_appLE _ _ _ _ _ x hxW] at e
      simp only [Category.id_comp] at e
      exact e
    have eK := key (zeroPt A') x p hx0 j
    rw [GA, GB, F1, hIB] at eK
    simp only [hIA] at eK
    have heb : IsUnit (gs t x _ (eB.s (fun _ => qB)).val) := by
      rw [gs_unit t x _ hWB]; exact Units.isUnit _
    rw [gs_appTop', gs_sum' (𝟙 (Sp R)) x ⊤ trivial]
    simp only [gs_mul (𝟙 (Sp R)) x ⊤ trivial, gs_appTop']
    apply (heb.pow k).mul_left_inj.1
    rw [eK, ← hN, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.HomFixMatCond
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem embedsBy_fA_of_isBCBasis (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k mB : ℕ)
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (hB : IsAbelianScheme B) (hM : M.IsLB) (_hk : 1 ≤ k)
    (hVA : VeryAmpleAt B M k) (hb : IsBCBasis B M k bB) : GlobalTheory.AmpleSpan.EmbedsBy (GlobalTheory.HomFixUniv.fA B) bB := by
  have hp : IsProper B.hom := hB.proper
  let t : Spec (CommRingCat.of Rg) ⟶ (topS Rg).left := (Sp Rg).topIso.inv
  choose b' hb' using fun i => GlobalTheory.AbLaw.SecBC.exists_pullSec B M (k : ℤ) (homAt t) (bB i)
  have hspan := (hb Rg t b' hb').2
  have hE := GlobalTheory.AmpleSpan.embedsBy_baseAt B hM hVA (isAffineOpen_top (Sp Rg)) t b' hspan
  have hS := fun i => GlobalTheory.SpanFrame.secScal_of_isPullSec B hM (k : ℤ) (homAt t) (hb' i)
  haveI : IsIso (homAt t) := by
    haveI : IsIso ((Over.forget _).map (homAt t)) := by change IsIso t; infer_instance
    exact isIso_of_reflects_iso (homAt t) (Over.forget _)
  haveI : IsIso (homAt t ▷ B).left := inferInstanceAs (IsIso ((Over.forget _).map (homAt t ▷ B)))
  haveI : IsAffine (baseAt t).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of Rg)))
  have hw : (homAt t ▷ B).left ≫ fA B = (fst (baseAt t) B).left ≫ 𝟙 _ := by
    have e1 := Over.w (homAt t ▷ B)
    have e2 := Over.w (fst (baseAt t) B)
    have e3 : (baseAt t).hom = 𝟙 _ := by simp [baseAt, t, baseOver]
    rw [Category.comp_id, fA, e1, ← e2, e3, Category.comp_id]
  have sq : IsPullback (inv (homAt t ▷ B).left) (fA B) (fst (baseAt t) B).left (𝟙 _) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [IsIso.inv_comp_eq, Category.comp_id, hw, Category.comp_id]
  exact GlobalTheory.AmpleSpan.EmbedsBy.secScal hM sq hE
    fun i => GlobalTheory.AmpleSpan.secScal_symm hM (hS i) (IsIso.inv_hom_id _)

end GlobalTheory.HomFixUniv
end
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.dualWeylWeightSpreadBound_proof : GlobalTheory.LeviCut.NablaBdd := by
  first | exact @GlobalTheory.LeviCut.nablaBdd | exact GlobalTheory.LeviCut.nablaBdd | (intros; apply GlobalTheory.LeviCut.nablaBdd <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.dualWeylModuleStructureGl_proof : GlobalTheory.LeviCut.NablaGl := by
  first | exact @GlobalTheory.LeviCut.nablaGl | exact GlobalTheory.LeviCut.nablaGl | (intros; apply GlobalTheory.LeviCut.nablaGl <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.dualWeylLeviProjectionDenominators_of_hypotheses : GlobalTheory.LeviCut.ResLat → GlobalTheory.LeviCut.ResHw → GlobalTheory.LeviCut.ResDer → GlobalTheory.LeviCut.LeviProj := by
  first | exact @GlobalTheory.LeviCut.leviProj_of | exact GlobalTheory.LeviCut.leviProj_of | (intros; apply GlobalTheory.LeviCut.leviProj_of <;> assumption)
end

section

open Classical

theorem _root_.GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by
  first | exact @GlobalTheory.MinorFrame.inv_le_span_prodMinors | exact GlobalTheory.MinorFrame.inv_le_span_prodMinors | (intros; apply GlobalTheory.MinorFrame.inv_le_span_prodMinors <;> assumption)
end
