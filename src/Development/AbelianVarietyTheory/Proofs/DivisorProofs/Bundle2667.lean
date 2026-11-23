module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle984
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiNormCoord

open Formalism.L2.Pj

variable {R : Type} [CommRing R] [IsDomain R]

theorem valF_eq {D : DegPre R} {χ : D.X} {r : R} (j : PUnit → D.P.L.ι)
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
    (e : ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val) :
    valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) r := by
  unfold valF
  rw [dite_eq_left (by exact h)]
  have e1 : ∀ (h' : ⊤ ≤ 𝟙 (Sp (FractionRing R)) ⁻¹ᵁ (D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j),
      (Scheme.Hom.appLE (𝟙 (Sp (FractionRing R)))
        ((D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j) ⊤ h').hom ((D.psi χ).s j).val
      = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val := by
    intro h'
    rfl
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((e1 h).trans e.symm)).trans ?_
  have e2 : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    have : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := rfl
    simp only [DegPre.toOpen, RingHom.comp_apply, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e2]
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have n' := congrArg (fun f => (f ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r) n
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at n'
  exact n'.symm

theorem exists_unit_valF {D : DegPre R} {χ : D.X} {r : R} (hr : PsiCoord D χ r) (j : PUnit → D.P.L.ι)
    (hj : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit)) :
    ∃ u : Rˣ, valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) (u * r) := by
  obtain ⟨j₀, hj₀, h₀, e₀⟩ := hr
  have h := PsiCoordLocal.generic_le D χ j hj
  obtain ⟨u, hu⟩ := PsiCoordLocal.exists_trans D χ j j₀ hj hj₀ h h₀
  let φ := RingEquiv.ofBijective _ (PsiCoordLocal.toOpen_top_bijective (R := R))
  refine ⟨Units.map φ.symm.toMonoidHom u, valF_eq j h ?_⟩
  have k : DegPre.toOpen (R := R) ⊤ (Units.map φ.symm.toMonoidHom u : Rˣ) = u := φ.apply_symm_apply u.val
  rw [map_mul, map_mul, k, e₀]
  exact (congrArg Units.val hu).symm

theorem norm_unit {S C : Type} [CommRing S] [NormedField C] (f : S →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (u : Sˣ) :
    ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Sˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (hf _) ?_
  calc (1 : ℝ) = ‖f u‖ * ‖f (u⁻¹ : Sˣ)‖ := h.symm
    _ ≤ ‖f u‖ * 1 := mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
    _ = _ := mul_one _

theorem main : ∀ (p : ℕ) [Fact p.Prime] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra (FractionRing W) (PadicAlgCl p)], (∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) → ∀ (D : DegData W (maximalIdeal W)) (y : D.toPre.X), (∃ r, Formalism.L2.Pj.PsiCoord D.toPre y r) ∧ ∀ r, Formalism.L2.Pj.PsiCoord D.toPre y r → ∀ t : ℝ, (GlobalTheory.UnifTorsK.PsiNormAt p D.toPre y t ↔ ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ r)‖ = t) := by
  intro p _ W _ _ _ _ hball D y
  haveI : CharZero W :=
    ((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))).charZero
  have hf : ∀ a : W, ‖((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))) a‖ ≤ 1 :=
    fun a => (hball _).2 ⟨a, rfl⟩
  refine ⟨((GlobalTheory.PsiCoordLocal.main W D inferInstance y).1).imp fun r h => h.1, fun r hr t => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨j₀, hj₀, h₀, e₀⟩ := hr
    have := h j₀ hj₀
    rwa [valF_eq j₀ h₀ e₀] at this
  · intro j hj
    obtain ⟨u, hu⟩ := exists_unit_valF hr j hj
    rw [hu, map_mul, map_mul, norm_mul]
    have := norm_unit _ hf u
    simp only [RingHom.comp_apply] at this
    rw [this, _root_.one_mul, h]

end GlobalTheory.PsiNormCoord
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.RosatiPull

theorem sq_left_ext {H : Scheme.{0}} {G : Over H} {Z : Scheme.{0}} {a b : Z ⟶ (G ⊗ G).left}
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  pullback.hom_ext h1 h2

theorem rosatiFor_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (S H E : Scheme.{0}) (A₀ : Over S) [GrpObj A₀] (P : LB (G2 A₀).left), P.IsLB → ∀ (AH : Over H) [GrpObj AH] (AE : Over E) [GrpObj AE] (f : E ⟶ H) (φ : AE.left ⟶ AH.left) (φ₂ : (G2 AE).left ⟶ (G2 AH).left) (φ₂H : (G2 AH).left ⟶ (G2 A₀).left) (actH : OActN D.O AH) (actE : OActN D.O AE), IsGrpPullback AE AH f φ → IsSquare φ φ₂ → (∀ a : D.O, (actE.act a).left ≫ φ = φ ≫ (actH.act a).left) → RosatiFor D actH (P.pull φ₂H) → RosatiFor D actE (P.pull (φ₂ ≫ φ₂H)) := by
  intro p _ D S H E A₀ _ P hP AH _ AE _ f φ φ₂ φ₂H actH actE _ hsq hact hR c
  have hu : (lift (fst AE AE ≫ actE.act c) (snd AE AE)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst AH AH ≫ actH.act c) (snd AH AH)).left := by
    apply sq_left_ext
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hsq.1]
      simp only [← Category.assoc, ← Over.comp_left, lift_fst]
      simp only [Over.comp_left, Category.assoc, hact]
      rw [← Category.assoc φ₂, hsq.1, Category.assoc]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hsq.2]
      simp only [← Category.assoc, ← Over.comp_left, lift_snd]
  have hv : (lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst AH AH) (snd AH AH ≫ actH.act (D.star c).unop)).left := by
    apply sq_left_ext
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hsq.1]
      simp only [← Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hsq.2]
      simp only [← Category.assoc, ← Over.comp_left, lift_snd]
      simp only [Over.comp_left, Category.assoc, hact]
      rw [← Category.assoc φ₂, hsq.2, Category.assoc]
  have hQ : (P.pull φ₂H).IsLB := pull_isLB hP _
  have hR' : (P.pull (φ₂ ≫ φ₂H)).IsLB := pull_isLB hP _
  have e3 := GlobalTheory.GenSpread.lbIso_pull_comp (L := P.pull φ₂H) (M := P.pull φ₂H) φ₂ hu hv (hR c)
  have e1u := GlobalTheory.GenSpread.lbIso_pull_pull hP
    (lift (fst AE AE ≫ actE.act c) (snd AE AE)).left (a := φ₂ ≫ φ₂H) rfl
  have e2u := GlobalTheory.GenSpread.lbIso_pull_pull hP
    ((lift (fst AE AE ≫ actE.act c) (snd AE AE)).left ≫ φ₂) (a := φ₂H) (Category.assoc _ _ _).symm
  have e1v := GlobalTheory.GenSpread.lbIso_pull_pull hP
    (lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left (a := φ₂ ≫ φ₂H) rfl
  have e2v := GlobalTheory.GenSpread.lbIso_pull_pull hP
    ((lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left ≫ φ₂) (a := φ₂H) (Category.assoc _ _ _).symm
  exact LBIso.trans (pull_isLB hR' _) (pull_isLB hP _) (pull_isLB hR' _) e1u.symm
    (LBIso.trans (pull_isLB hP _) (pull_isLB hQ _) (pull_isLB hR' _) e2u
      (LBIso.trans (pull_isLB hQ _) (pull_isLB hQ _) (pull_isLB hR' _) e3
        (LBIso.trans (pull_isLB hQ _) (pull_isLB hP _) (pull_isLB hR' _) e2v.symm e1v)))

end GlobalTheory.RosatiPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTTransport

open ReciprocityTheory.ChartRestriction.G.Pdiv

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

def tateTransport {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q'] {act : D.O → Q → Q}
    {act' : D.O → Q' → Q'} {E : ℕ → Q → Q → kˣ → Prop} {E' : ℕ → Q' → Q' → kˣ → Prop}
    (I : TateIsoO D k Q act E) (e : Q ≃* Q') (ha : ∀ c g, e (act c g) = act' c (e g))
    (hE : ∀ n g g' u, E n g g' u → E' n (e g) (e g') u) : TateIsoO D k Q' act' E' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n y := e (I.ev n y)
  add n x y := by rw [I.add, map_mul]
  lin n c x := by rw [I.lin, ha]
  ker n hn hp x := by rw [map_eq_one_iff _ e.injective]; exact I.ker n hn hp x
  onto n hn hp q := by
    rw [← map_eq_one_iff e.symm e.symm.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun y => ⟨fun h => by rw [h, e.apply_symm_apply], fun h => by rw [← h, e.symm_apply_apply]⟩
  tower n m hn hm hp x := by rw [← map_pow, I.tower n m hn hm hp]
  isom n hn hp x y := hE _ _ _ _ (I.isom n hn hp x y)

theorem exists_tate_iff {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q'] {act : D.O → Q → Q}
    {act' : D.O → Q' → Q'} {E : ℕ → Q → Q → kˣ → Prop} {E' : ℕ → Q' → Q' → kˣ → Prop}
    (e : Q ≃* Q') (ha : ∀ c g, e (act c g) = act' c (e g))
    (hE : ∀ n g g' u, E n g g' u ↔ E' n (e g) (e g') u) (N : ℕ) (l : D.La → Q) (l' : D.La → Q')
    (hl : ∀ y, e (l y) = l' y) :
    (∃ I : TateIsoO D k Q act E, ∀ y, l y = I.ev N y) ↔ (∃ I : TateIsoO D k Q' act' E', ∀ y, l' y = I.ev N y) := by
  constructor
  · rintro ⟨I, hI⟩
    exact ⟨tateTransport I e ha fun n g g' u => (hE n g g' u).1, fun y => by rw [← hl, hI]; rfl⟩
  · rintro ⟨I, hI⟩
    refine ⟨tateTransport I e.symm (fun c g => e.injective (by rw [e.apply_symm_apply, ha, e.apply_symm_apply]))
      (fun n g g' u h => (hE n _ _ u).2 (by rw [e.apply_symm_apply, e.apply_symm_apply]; exact h)), fun y => ?_⟩
    show l y = e.symm (I.ev N y)
    rw [← hI y, ← hl y, e.symm_apply_apply]

variable {R : Type} [CommRing R] (b : Base D R) {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A]
  [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem lieAt_iff (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S') : LieAt b act' β x ↔ LieAt b act β (x ≫ f) := by
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  have key := fun c r v => GlobalTheory.HTPull.isTanScal_iff pb act act' hact x e he c r v
  constructor
  · intro H v hv
    obtain ⟨w, hw, hvw⟩ := H (e.symm v) ((key _ _ _).2 (by rw [e.apply_symm_apply]; exact hv))
    refine ⟨fun i => e (w i), fun i c => (key _ _ _).1 (hw i c), ?_⟩
    rw [← e.apply_symm_apply v, hvw, map_list_prod, List.map_ofFn]
    rfl
  · intro H v hv
    obtain ⟨w, hw, hvw⟩ := H (e v) ((key _ _ _).1 hv)
    refine ⟨fun i => e.symm (w i), fun i c => (key _ _ _).2 (by rw [e.apply_symm_apply]; exact hw i c),
      e.injective ?_⟩
    rw [hvw, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]

theorem lieRankAt_iff (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S') : LieRankAt b act' β x ↔ LieRankAt b act β (x ≫ f) := by
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun g =>
    forall_congr' fun i => ?_
  have h := GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' A A' f φ (act.toF D) (act'.toF D) pb (fun c => hact _) k
    (spMap g ≫ x) ((g.comp β).comp (b.t i)) D.m
  rwa [Category.assoc] at h

theorem lieHer_iff (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S') : LieHer b act' β x ↔ LieHer b act β (x ≫ f) := by
  refine forall_congr' fun R'' => forall_congr' fun _ => forall_congr' fun g => ?_
  have h1 := lieAt_iff b pb act act' hact (g.comp β) (spMap g ≫ x)
  have h2 := lieRankAt_iff b pb act act' hact (g.comp β) (spMap g ≫ x)
  rw [Category.assoc] at h1 h2
  exact and_congr h1 h2

theorem geomAt_iff [IsCommMonObj A] (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) (P : LB (G2 A).left) (P' : LB (G2 A').left)
    (hP : P.IsLB) (hP' : P'.IsLB) (φ₂ : (G2 A').left ⟶ (G2 A).left) (sq : IsSquare φ φ₂)
    (H : LBIso P' (P.pull φ₂)) (eta : D.La → (𝟙_ (Over S) ⟶ A)) (eta' : D.La → (𝟙_ (Over S') ⟶ A'))
    (heta : ∀ y, (eta' y).left ≫ φ = f ≫ (eta y).left) (N : ℕ) (k : Type) [Field k] (x : Sp k ⟶ S') :
    GeomAt D N act' P' eta' k x ↔ GeomAt D N act P eta k (x ≫ f) := by
  have dg := SiegelPull.diag_iso sq H
  let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ f) ⟶ A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
    ⟨SiegelPull.push_injective pb _, SiegelPull.push_surjective pb _⟩
  have hel : ∀ g, (e g).left = g.left ≫ φ := fun g => rfl
  refine exists_tate_iff e (fun c g => GlobalTheory.HTPull.push_comp pb (hact c) _ g) (fun n g g' u => ?_) N _ _
    (fun y => ?_)
  · exact weilIs_grpPullback_of_comm S S' A A' f φ _ _ (pull_isLB hP _) (pull_isLB hP' _) pb dg (Over.mk x) n
      g g' (e g) (e g') _ (hel g) (hel g')
  · apply Over.OverMorphism.ext
    show ((toUnit (Over.mk x)).left ≫ (eta' y).left) ≫ φ = (toUnit (Over.mk (x ≫ f))).left ≫ (eta y).left
    rw [Category.assoc, heta, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
    rfl

end GlobalTheory.HTTransport

namespace GlobalTheory.HTTransport

open ReciprocityTheory.ChartRestriction.G.Pdiv

theorem lieHer_geomAt_iff : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (X T : Scheme.{0}) (πX : X ⟶ S₀) (z : T ⟶ X) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (AT : Over T) [GrpObj AT] [IsCommMonObj AT] (φX : AX.left ⟶ A₀.left) (φ₂X : (G2 AX).left ⟶ (G2 A₀).left) (φT : AT.left ⟶ A₀.left) (φ₂T : (G2 AT).left ⟶ (G2 A₀).left) (ψ : AT.left ⟶ AX.left) (actX : OActN D.O AX) (actT : OActN D.O AT) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)) (ηT : D.La → (𝟙_ (Over T) ⟶ AT)) (PT : LB (G2 AT).left), PT.IsLB → IsGrpPullback AX A₀ πX φX → IsSquare φX φ₂X → IsGrpPullback AT A₀ (z ≫ πX) φT → IsSquare φT φ₂T → IsGrpPullback AT AX z ψ → ψ ≫ φX = φT → LBIso PT (P₀.pull φ₂T) → (∀ a : D.O, (actT.act a).left ≫ ψ = ψ ≫ (actX.act a).left) → (∀ y, (ηT y).left ≫ ψ = z ≫ (ηX y).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), LieHer b actT β x ↔ LieHer b actX β (x ≫ z)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), GeomAt D N actT PT ηT k x ↔ GeomAt D N actX (P₀.pull φ₂X) ηX k (x ≫ z) := by
  intro p _ D R _ b N S₀ A₀ _ _ P₀ hP₀ X T πX z AX _ _ AT _ _ φX φ₂X φT φ₂T ψ actX actT ηX ηT PT hPT _ sqX _ sqT
    pbψ hψ H hact hη
  have w : ((fst AT AT).left ≫ ψ) ≫ AX.hom = ((snd AT AT).left ≫ ψ) ≫ AX.hom := by
    rw [Category.assoc, Category.assoc, pbψ.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]
  let ψ₂ : (G2 AT).left ⟶ (G2 AX).left := pullback.lift _ _ w
  have sqψ : IsSquare ψ ψ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hcomp : ψ₂ ≫ φ₂X = φ₂T := by
    have h1 : (ψ₂ ≫ φ₂X) ≫ (fst A₀ A₀).left = φ₂T ≫ (fst A₀ A₀).left := by
      rw [Category.assoc, sqX.1, ← Category.assoc, sqψ.1, Category.assoc, hψ, sqT.1]
    have h2 : (ψ₂ ≫ φ₂X) ≫ (snd A₀ A₀).left = φ₂T ≫ (snd A₀ A₀).left := by
      rw [Category.assoc, sqX.2, ← Category.assoc, sqψ.2, Category.assoc, hψ, sqT.2]
    exact Over.tensorObj_ext _ _ h1 h2
  have hB : ((P₀.pull φ₂X).pull ψ₂).IsLB := pull_isLB (pull_isLB hP₀ _) _
  have iso : LBIso PT ((P₀.pull φ₂X).pull ψ₂) :=
    LBIso.trans hPT (pull_isLB hP₀ _) hB H
      (LBIso.chartPull (GlobalTheory.RigidBundleGlue.chartPullComp P₀ φ₂X ψ₂ φ₂T hcomp.symm) (chartPullId _)
        (PullbackComparison.gen_refl _ hB))
  exact ⟨fun R' _ β x => lieHer_iff b pbψ actX actT hact β x,
    fun k _ _ x => geomAt_iff pbψ actX actT hact (P₀.pull φ₂X) PT (pull_isLB hP₀ _) hPT ψ₂ sqψ iso ηX ηT hη N k x⟩

end GlobalTheory.HTTransport
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT

theorem exists_finite_rep_linLevel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH], IsAbelianScheme AH → IsUnit ((N : ℕ) : Γ(H, ⊤)) → ∀ (actH : OActN D.O AH), ∃ (E : Scheme.{0}) (πE : E ⟶ H) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsFinite πE ∧ IsGrpPullback AE AH πE φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  intro p _ D N H AH _ _ hab hN actH
  haveI := D.freeLa
  haveI := D.finLa
  haveI := D.freeO
  haveI := D.finO
  haveI : IsSeparated AH.hom := by haveI := hab.proper; infer_instance
  obtain ⟨Z, et, hZf, -, eadd, epow, huniv⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom H AH N D.La hab hN
  let bO := Module.Free.chooseBasis ℤ D.O
  let bL := Module.Free.chooseBasis ℤ D.La
  obtain ⟨Y, i, hYf, hieq, hiu⟩ := GlobalTheory.T.exists_finite_agreementLocus_separated H Z AH hZf inferInstance
    (Module.Free.ChooseBasisIndex ℤ D.O × Module.Free.ChooseBasisIndex ℤ D.La)
    (fun k => et (bO k.1 • bL k.2)) (fun k => et (bL k.2) ≫ actH.act (bO k.1))
  let u : D.La → (Y ⟶ AH) := fun x => i ≫ et x
  have uadd : ∀ x y, u (x + y) = u x * u y := fun x y => by
    simp only [u, eadd, MonObj.comp_mul]
  have ulin : ∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c :=
    GlobalTheory.T.oLinear_of_basis_products_additive_points p D H Y AH actH u uadd _ _ bO bL fun j k => by
      have := hieq (j, k)
      simp only [u]
      rw [this, Category.assoc]
  have ukill : ∀ x, u (N • x) = 1 := fun x => by
    simp only [u]
    rw [GlobalTheory.LevCover.add_map_nsmul eadd, epow, MonObj.comp_one]
  have uuniv : ∀ (T : Over H) (u' : D.La → (T ⟶ AH)), (∀ x y, u' (x + y) = u' x * u' y) →
      (∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c) → (∀ x, u' (N • x) = 1) →
      ∃! h : T ⟶ Y, ∀ x, h ≫ u x = u' x := by
    intro T u' hadd hlin hkill
    have hpow : ∀ x, u' x ^ N = 1 := fun x => by rw [← GlobalTheory.LevCover.add_map_nsmul hadd, hkill]
    obtain ⟨h₀, hh₀, hu₀⟩ := huniv T u' hadd hpow
    have heq : ∀ k, h₀ ≫ (fun k : _ × _ => et (bO k.1 • bL k.2)) k =
        h₀ ≫ (fun k : _ × _ => et (bL k.2) ≫ actH.act (bO k.1)) k := by
      rintro ⟨j, k⟩
      simp only
      rw [hh₀, hlin, ← Category.assoc, hh₀]
    obtain ⟨h, hh, hu⟩ := hiu T h₀ heq
    refine ⟨h, fun x => by simp only [u]; rw [← Category.assoc, hh, hh₀], fun h' hh' => hu h' ?_⟩
    exact hu₀ _ fun x => by rw [Category.assoc]; exact hh' x
  obtain ⟨AE, _, _, φE, actE, ηE, hE, hact, heta, hηu⟩ := GlobalTheory.T.exists_pullback_group_oLinear_torsion_level p D N H AH actH Y u uadd ulin ukill
  exact ⟨Y.left, Y.hom, AE, inferInstance, inferInstance, φE, actE, ηE, hYf, hE, hact, heta,
    fun T g AT _ φ act eta hT hTact hTeta =>
      GlobalTheory.T.oLinearLevel_pullback_universal_factorisation p D N H AH actH Y u AE φE ηE hE hηu uuniv T g AT φ act eta hT hTact hTeta⟩

end GlobalTheory.UPel.HT
end
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnframePt

open GlobalTheory.RealGeo GlobalTheory.Unframe Formalism.IndefR.FWT

abbrev fullHeckeRealDatMovedReadings {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ) : RealDat3 D A3 Ks :=
  { Rl with toRealDat := moveR Rl.toRealDat w }

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def geoHalf (p : PtAt ex Csz) : GeoHalf p.T p.R.toRealDat (fun _ => 1) :=
  ⟨p.κ, p.v₀, p.fw, p.bar, p.O, p.pins, p.rhoGeo, p.equivAll, p.cTie, fun i hu => by
    have e : phEff p.R = fun _ => (1 : ℂ) := funext p.phEff_one
    rw [← e]
    exact p.phase i hu⟩

end Pt

end GlobalTheory.UnframePt
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem _root_.GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ) (K : (Rul Xo c)ˣ), GoodEmb c σ → IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = x) → Nonempty (KeySec Xo c) → 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∃ C : ℝ, 0 < C ∧ |Real.log C| ≤ 2 * (g : ℝ) * Real.log (2 * Real.pi) ∧ ∀ k, ∀ y ∈ (U.X k).dom, homN U x (wtOf Dw 0 (-4)) (K : Rul Xo c) ⟨k, y⟩ = C := by
  first | exact @GlobalTheory.KeyArchNorm.homN_key_const | exact GlobalTheory.KeyArchNorm.homN_key_const | (intros; apply GlobalTheory.KeyArchNorm.homN_key_const <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.RootDiagAmple

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem relAmple_pull_of_isFinite {A G : Over S} [IsProper A.hom] (χ : A ⟶ G) [IsFinite χ.left]
    {D : LB G.left} (hD : D.IsLB) (h : Out.RelAmple G D) : Out.RelAmple A (D.pull χ.left) := by
  refine relAmple_of_isAmpleLB A (pull_isLB hD _) fun V hV => ?_
  have le : A.hom ⁻¹ᵁ V ≤ χ.left ⁻¹ᵁ (G.hom ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, Over.w]
  have le' : χ.left ⁻¹ᵁ (G.hom ⁻¹ᵁ V) ≤ A.hom ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, Over.w]
  have e : A.hom ⁻¹ᵁ V = χ.left ⁻¹ᵁ (G.hom ⁻¹ᵁ V) := le_antisymm le le'
  rw [e]
  have h₁ := (isAmpleLB_of_relAmple G hD h V hV).pull_of_isFinite (χ.left ∣_ (G.hom ⁻¹ᵁ V))
  refine (isAmpleLB_congr (pull_isLB (pull_isLB hD _) _) (pull_isLB (pull_isLB hD _) _) ?_).1 h₁
  refine (cls_eq_iff (pull_isLB (pull_isLB hD _) _) (pull_isLB (pull_isLB hD _) _)).1 ?_
  rw [cls_pull (pull_isLB hD _), cls_pull (pull_isLB hD _), cls_pull hD, cls_pull hD, ← pull_comp, ← pull_comp,
    morphismRestrict_ι]

theorem relAmple_of_relAmple_pow {A : Over S} [IsProper A.hom] {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) (h : Out.RelAmple A M) : Out.RelAmple A L := by
  rw [relAmple_iff_isAmpleLB A hM] at h
  refine relAmple_of_isAmpleLB A hL fun U hU => (isAmpleLB_pow_iff (pull_isLB hL _) hd).1 ?_
  refine (isAmpleLB_congr (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)
    ((cls_eq_iff (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)).1 ?_)).2 (h U hU)
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

end GlobalTheory.RootDiagAmple
end
end
