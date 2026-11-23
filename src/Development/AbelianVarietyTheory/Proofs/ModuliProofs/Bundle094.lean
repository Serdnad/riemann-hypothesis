module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle089
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle074
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle051
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAnalyticKodairaSpencerClass
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)

noncomputable section

namespace GlobalTheory.InvFieldBasis

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}

def expPt {B : Type} [CommRing B] [Algebra K B] (v : Fin n → (epsR K ⟶ G)) (e : Fin n → B)
    (he : ∀ i, e i * e i = 0) : sp (R₀ := K) B ⟶ G :=
  (List.ofFn fun i => (Chart.spMap (epsTo K (e i) (he i)) ≫ v i : sp (R₀ := K) B ⟶ G)).prod

variable {C : Type} [CommRing C] [Algebra K C]

theorem pushR_prodPts' (v : Fin n → (epsR K ⟶ G)) (c : Fin n → C) :
    pushR G (Chart.prodPts c (bcVec C v)) =
      expPt v (fun i => (inr (c i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  unfold Chart.prodPts expPt
  have key : ∀ i, pushR G (Chart.spMap (Chart.scaleD (c i)) ≫ bcVec C v i) =
      (Chart.spMap (epsTo K (inr (c i) : DualNumber C) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v i :
        sp (R₀ := K) (DualNumber C) ⟶ G) := by
    intro i
    rw [Chart.pushR_spMap, pushR_bcVec, ← Category.assoc, Chart.spMap_comp]
    congr 2
    apply DualNumber.algHom_ext
    change Chart.scaleD (c i) (Chart.dualMapA K C (inr 1)) = epsTo K (inr (c i) : DualNumber C) _ (inr 1)
    rw [Chart.dualMapA_inr, map_one]
    simp only [Chart.scaleD]
    rw [show (inr 1 : DualNumber K) = DualNumber.eps from rfl, epsTo_eps, TrivSqZeroExt.map_inr,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, _root_.mul_one]
  calc pushR G _ = pushRHom G (DualNumber C)
        (List.ofFn fun i => Chart.spMap (Chart.scaleD (c i)) ≫ bcVec C v i).prod := rfl
    _ = _ := by
      rw [map_list_prod, List.map_ofFn]
      exact congrArg List.prod (List.ofFn_inj.mpr (funext key))

theorem existsUnique_expPt [Smooth G.hom] {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    (w : sp (R₀ := K) (DualNumber C) ⟶ G) (hw : Chart.spMap ((fstD C).restrictScalars K) ≫ w = 1) :
    ∃! c : Fin n → C,
      w = expPt v (fun i => (inr (c i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  have hb : IsLieBasis (bcVec C v) :=
    Chart.isLieBasis_baseChange (algebraMap K C) (isGrpPullback_pullback G (fB K C)) hv
      (fun j => bcVec_left_fst v j)
  have hwT : Chart.IsTan (pullR (R' := C) G w) := by
    rw [isTan_iff_mem, Chart.pushR_pullR]
    exact mem_redKer_of_section _ ((Algebra.ofId C (DualNumber C)).restrictScalars K) (fun a => by simp) hw
  have hT : IsTangent (pullR (R' := C) G w) := (Chart.isTan_iff _).1 hwT
  have key : ∀ c : Fin n → C, IsLieComb c (bcVec C v) (pullR (R' := C) G w) ↔
      w = expPt v (fun i => (inr (c i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
    intro c
    rw [Chart.isLieComb_iff, ← pushR_prodPts']
    constructor
    · intro h'
      rw [← h', Chart.pushR_pullR]
    · intro h'
      apply Chart.pushR_inj (G := G)
      rw [Chart.pushR_pullR, h']
  obtain ⟨c, hc, hu⟩ := hb.2 _ hT
  exact ⟨c, (key c).1 hc, fun c' hc' => hu c' ((key c').2 hc')⟩

theorem preimage_translate {v : epsR K ⟶ G} (hv : IsTangent v) (W : G.left.Opens) :
    ((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ W = (snd (epsR K) G).left ⁻¹ᵁ W := by
  apply GlobalTheory.KS.DlogPol.preimage_transl <;> assumption

theorem evalPt_pbT {B : Type} [CommRing B] {Y Z : Scheme.{0}} (x : Sp B ⟶ Z) (f : Z ⟶ Y) {O : Y.Opens}
    {O' : Z.Opens} (h : O' ≤ f ⁻¹ᵁ O) (h' : ⊤ ≤ x ⁻¹ᵁ O') (y : Sp B ⟶ Y) (hy : x ≫ f = y)
    (h'' : ⊤ ≤ y ⁻¹ᵁ O) (s : Γ(Y, O)) : evalPt x O' h' (pbT f s O') = evalPt y O h'' s := by
  subst hy
  simp only [evalPt, pbT, dif_pos h]
  rw [← Scheme.Hom.appLE_comp_appLE (e₁ := h) (e₂ := h')]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]

private lemma evalPt_add {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Sp B ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : evalPt x O h (a + b) = evalPt x O h a + evalPt x O h b := by
  unfold evalPt
  exact map_add _ a b

private lemma evalPt_mul {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Sp B ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : evalPt x O h (a * b) = evalPt x O h a * evalPt x O h b := by
  unfold evalPt
  exact map_mul _ a b

private lemma evalPt_constFn' {B A : Type} [CommRing B] [CommRing A] {Z : Scheme.{0}} (x : Sp B ⟶ Z)
    (q : Z ⟶ Sp A) (φ : A →+* B) (hq : x ≫ q = Spec.map (CommRingCat.ofHom φ)) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a : A) : evalPt x O h (constFn q O a) = φ a := by
  unfold evalPt constFn
  have e1 : ∀ (g : Sp B ⟶ Sp A) (e : ⊤ ≤ g ⁻¹ᵁ ⊤), g.appLE ⊤ ⊤ e = g.appTop := fun g e => by
    simp only [Scheme.Hom.appLE]
    rw [show (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _]
    exact Category.comp_id _
  rw [← CommRingCat.comp_apply, ← Category.assoc]
  erw [Scheme.Hom.appLE_comp_appLE]
  rw [e1, hq, Scheme.ΓSpecIso_naturality]
  simp

variable {B : Type} [CommRing B] [Algebra K B]

theorem evalPt_translate {v : epsR K ⟶ G} (hv : IsTangent v)
    {dd : ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : IsInvDer v dd) (e : B) (he : e * e = 0)
    (z : sp (R₀ := K) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ ((Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + e * evalPt z.left O h (dd O f) := by
  let t : sp (R₀ := K) B ⟶ epsR K ⊗ G := lift (Chart.spMap (epsTo K e he)) z
  have ht1 : t ≫ ((fst (epsR K) G ≫ v) * snd (epsR K) G) =
      (Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z := by
    rw [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd]
  have ht2 : t ≫ snd (epsR K) G = z := lift_snd _ _
  have ht3 : t ≫ fst (epsR K) G = Chart.spMap (epsTo K e he) := lift_fst _ _
  have hP := preimage_translate hv O
  have hc : ∀ {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens), f ⁻¹ᵁ (g ⁻¹ᵁ U) = (f ≫ g) ⁻¹ᵁ U :=
    fun _ _ _ => rfl
  have hO : t.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ O) = z.left ⁻¹ᵁ O := by
    rw [hc, ← Over.comp_left, ht2]
  have hO' : ((Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z).left ⁻¹ᵁ O = z.left ⁻¹ᵁ O := by
    rw [← ht1, Over.comp_left, ← hc, hP, hO]
  have hT : ⊤ ≤ t.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ O) := hO ▸ h
  refine ⟨hO' ▸ h, fun f => ?_⟩
  have e1 : evalPt t.left _ hT (pbT (snd (epsR K) G).left f ((snd (epsR K) G).left ⁻¹ᵁ O)) =
      evalPt z.left O h f :=
    evalPt_pbT t.left _ le_rfl hT z.left (by rw [← Over.comp_left, ht2]) h f
  have e2 : evalPt t.left _ hT (pbT (snd (epsR K) G).left (dd O f) ((snd (epsR K) G).left ⁻¹ᵁ O)) =
      evalPt z.left O h (dd O f) :=
    evalPt_pbT t.left _ le_rfl hT z.left (by rw [← Over.comp_left, ht2]) h (dd O f)
  have e3 : evalPt t.left _ hT (constFn (R := DualNumber K) (fst (epsR K) G).left
      ((snd (epsR K) G).left ⁻¹ᵁ O) DualNumber.eps) = e := by
    rw [evalPt_constFn' t.left (fst (epsR K) G).left (epsTo K e he : DualNumber K →+* B)]
    · simp
    · rw [← Over.comp_left, ht3]
      rfl
  rw [← evalPt_pbT t.left ((fst (epsR K) G ≫ v) * snd (epsR K) G).left hP.ge hT
    ((Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z).left (by rw [← Over.comp_left, ht1]) _ f,
    hd O f, evalPt_add, evalPt_mul, e1, e2, e3]

private lemma evalPt_congr' {B : Type} [CommRing B] {Z : Scheme.{0}} {x y : Sp B ⟶ Z} (hxy : x = y)
    (O : Z.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ O) (hy : ⊤ ≤ y ⁻¹ᵁ O) (s : Γ(Z, O)) : evalPt x O hx s = evalPt y O hy s := by
  subst hxy
  rfl

theorem evalPt_expPt {v : Fin n → (epsR K ⟶ G)} (hv : ∀ i, IsTangent (v i))
    {dd : Fin n → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : ∀ i, IsInvDer (v i) (dd i))
    (e : Fin n → B) (he : ∀ i j, e i * e j = 0)
    (z : sp (R₀ := K) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ (expPt v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f) := by
  induction n with
  | zero =>
    have h1 : expPt v e (fun i => he i i) * z = z := by
      simp only [expPt, List.ofFn_zero, List.prod_nil]
      exact _root_.one_mul z
    refine ⟨by rw [h1]; exact h, fun f => ?_⟩
    have hx : (expPt v e (fun i => he i i) * z).left = z.left := congrArg (fun w => w.left) h1
    exact (evalPt_congr' hx O _ h f).trans (by simp)
  | succ n ih =>
    have hs : expPt v e (fun i => he i i) * z =
        (Chart.spMap (epsTo K (e 0) (he 0 0)) ≫ v 0 : sp (R₀ := K) B ⟶ G) *
          (expPt (fun i => v i.succ) (fun i => e i.succ) (fun i => he i.succ i.succ) * z) := by
      rw [← _root_.mul_assoc]
      congr 1
      simp only [expPt, List.ofFn_succ, List.prod_cons]
    obtain ⟨h1, H1⟩ := ih (v := fun i => v i.succ) (hv := fun i => hv i.succ) (dd := fun i => dd i.succ)
      (hd := fun i => hd i.succ) (e := fun i => e i.succ) (he := fun i j => he i.succ j.succ)
    obtain ⟨h2, H2⟩ := evalPt_translate (hv 0) (hd 0) (e 0) (he 0 0) _ O h1
    refine ⟨by rw [hs]; exact h2, fun f => ?_⟩
    have hx : (expPt v e (fun i => he i i) * z).left =
        ((Chart.spMap (epsTo K (e 0) (he 0 0)) ≫ v 0 : sp (R₀ := K) B ⟶ G) *
          (expPt (fun i => v i.succ) (fun i => e i.succ) (fun i => he i.succ i.succ) * z)).left :=
      congrArg (fun w => w.left) hs
    rw [evalPt_congr' hx O _ h2 f, H2 f, H1 f, H1 (dd 0 O f), Fin.sum_univ_succ]
    have hz : e 0 * ∑ i : Fin n, e i.succ * evalPt z.left O h (dd i.succ O (dd 0 O f)) = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [← _root_.mul_assoc, he 0 i.succ]; simp
    rw [_root_.mul_add, hz]
    ring

end GlobalTheory.InvFieldBasis
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.CubeGen

open GlobalTheory.AbLaw.Cube

theorem surjective_appTop {X : Scheme.{0}} (P : Over X) (e : 𝟙_ (Over X) ⟶ P) (hs : Smooth P.hom)
    (hg : GeometricallyIntegral P.hom) (hr : IsReduced X) (hab : genericPoints X ⊆ abLocus P) :
    Function.Surjective P.hom.appTop.hom := by
  change ∀ u : Γ(P.left, P.hom ⁻¹ᵁ ⊤), ∃ a, (P.hom.app ⊤).hom a = u
  intro u
  have he : e.left ≫ P.hom = 𝟙 X := Over.w e
  have hle : (⊤ : X.Opens) ≤ e.left ⁻¹ᵁ (P.hom ⁻¹ᵁ ⊤) := fun _ _ => trivial
  have key : ∀ (g : X ⟶ X) (hg : g = 𝟙 X) (h' : (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤) (c : Γ(X, ⊤)),
      (g.appLE ⊤ ⊤ h').hom c = c := by
    rintro g rfl h' c
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    change (X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens)))).hom c = c
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hφψ : ∀ c : Γ(X, ⊤), (e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom ((P.hom.app ⊤).hom c) = c := fun c =>
    (congrArg (fun φ => CommRingCat.Hom.hom φ c) (Scheme.Hom.comp_appLE e.left P.hom ⊤ ⊤ hle)).symm.trans
      (key _ he hle c)
  refine ⟨(e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom u, ?_⟩
  have h1 := GlobalTheory.eq_one_of_appLE_section_eq_one X P e.left he hs hg ⟨hr, hab⟩ ⊤
    (1 + u - (P.hom.app ⊤).hom ((e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom u)) hle
    (by rw [map_sub, map_add (f := _), map_one, hφψ]; ring)
  linear_combination -h1

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def cubicalOfNormalised (s₂ : Function.Surjective (A ⊗ A).hom.appTop.hom)
    (s₃ : Function.Surjective (A ⊗ A ⊗ A).hom.appTop.hom) (s₄ : Function.Surjective (A ⊗ A ⊗ A ⊗ A).hom.appTop.hom)
    (M : RigLB A) (t : LB.Gen (Theta A M.L)) (ht : t.IsGen) (hn : IsNormalised t) : CubicalStr A M :=
  { t := t
    isGen := ht
    face := fun i => by
      have key : ∀ a b c : G2 A ⟶ A, lift 1 1 ≫ a = (1 : 𝟙_ (Over S) ⟶ A) → lift 1 1 ≫ b = (1 : 𝟙_ (Over S) ⟶ A) →
          lift 1 1 ≫ c = (1 : 𝟙_ (Over S) ⟶ A) → a = 1 ∨ b = 1 ∨ c = 1 →
          LB.Gen.Corr M.L _ _ (Y := (G2 A).left) _ _
            (LB.pullGen M.L (thφ A (x3 A)) thε t (lift a (lift b c)).left) (LB.oneGen M.L) := by
        intro a b c ha hb hc h
        refine corr_of_val_section M.isLB s₂ (lift 1 1) (fun V _ k => ?_) (DVR.pullGen_isGen _ _ _ _ ht _) oneGen_isGen
          (fun y J hJ => (hn.pull _ ha hb hc hJ).trans (val_one _).symm)
        refine (Fintype.prod_empty _).trans (Eq.trans ?_ (prod_cub a b c k).symm)
        apply Additive.ofMul.injective
        rcases h with rfl | rfl | rfl <;> simp only [_root_.mul_one, _root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one] <;> abel
      fin_cases i
      · exact key 1 (x2 A 0) (x2 A 1) (MonObj.comp_one _) (by simp [x2]) (by simp [x2]) (.inl rfl)
      · exact key (x2 A 0) 1 (x2 A 1) (by simp [x2]) (MonObj.comp_one _) (by simp [x2]) (.inr (.inl rfl))
      · exact key (x2 A 0) (x2 A 1) 1 (by simp [x2]) (by simp [x2]) (MonObj.comp_one _) (.inr (.inr rfl))
    cubeSymmetric_swap_first := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 1) (x3 A 0)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cubeSymmetric_swap_last := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 2) (x3 A 1), mul_right_comm (x3 A 0) (x3 A 2)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cocycle := by
      let e : 𝟙_ (Over S) ⟶ G4 A := lift 1 (lift 1 (lift 1 1))
      have e₀ : e ≫ x4 A 0 = 1 := by simp [e, x4]
      have e₁ : e ≫ x4 A 1 = 1 := by simp [e, x4]
      have e₂ : e ≫ x4 A 2 = 1 := by simp [e, x4]
      have e₃ : e ≫ x4 A 3 = 1 := by simp [e, x4]
      have f₀ : e ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
      have f₁ : e ≫ padd A (x4 A 1) (x4 A 2) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])
      refine corr_of_val_section M.isLB s₄ e (fun V _ k => ?_)
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (fun y J hJ => ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e f₀ e₂ e₃ hJ) (hn.pull e e₀ e₁ e₃ hJ))).trans ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e e₀ f₁ e₃ hJ) (hn.pull e e₁ e₂ e₃ hJ))).symm)
      refine (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0) (x4 A 1 * x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 1) (x4 A 2) (x4 A 3) k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0 * x4 A 1) (x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 0) (x4 A 1) (x4 A 3) k)).symm)
      apply Additive.ofMul.injective
      simp only [_root_.mul_assoc (x4 A 0), ofMul_mul, ofMul_inv]
      abel }

theorem exists_gen_of_lbIso {Z : Scheme.{0}} (L : LB Z) (f : Z ⟶ Z) (h : LBIso L (L.pull f)) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![f, 𝟙 Z] ![1, -1]), s.IsGen := by
  apply GlobalTheory.BiextSym.exists_gen_of_iso <;> assumption

theorem cubical_and_symmetric : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsSemiAbelian G → (IsReduced X ∧ genericPoints X ⊆ abLocus G) → ((∃ t : (Theta G L.L).Gen, t.IsGen) → Nonempty (CubicalStr G L)) ∧ (LBIso L.L (L.L.pull (GrpObj.inv (X := G)).left) → L.IsSymmetric) := by
  intro X G _ _ L hsa hrg
  obtain ⟨hr, hab⟩ := hrg
  have hsm : Smooth G.hom := hsa.smooth
  have hgc : GeometricallyConnected G.hom := hsa.geomConnected
  have hgi : GeometricallyIntegral G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth X G
  refine ⟨fun ⟨t, ht⟩ => ?_, fun hiso => ?_⟩
  · obtain ⟨t', ht', hn⟩ := exists_normalised L.isLB t ht
    obtain ⟨sm2, gi2, ab2⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G G hsm hsm hgi hgi
    obtain ⟨sm3, gi3, ab3⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G (G ⊗ G) hsm sm2 hgi gi2
    obtain ⟨sm4, gi4, ab4⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G (G ⊗ G ⊗ G) hsm sm3 hgi gi3
    have g2 : genericPoints X ⊆ abLocus (G ⊗ G) := fun x hx => ab2 ⟨hab hx, hab hx⟩
    have g3 : genericPoints X ⊆ abLocus (G ⊗ G ⊗ G) := fun x hx => ab3 ⟨hab hx, g2 hx⟩
    have g4 : genericPoints X ⊆ abLocus (G ⊗ G ⊗ G ⊗ G) := fun x hx => ab4 ⟨hab hx, g3 hx⟩
    exact ⟨cubicalOfNormalised (surjective_appTop (G ⊗ G) (lift 1 1) sm2 gi2 hr g2)
      (surjective_appTop (G ⊗ G ⊗ G) (lift 1 (lift 1 1)) sm3 gi3 hr g3)
      (surjective_appTop (G ⊗ G ⊗ G ⊗ G) (lift 1 (lift 1 (lift 1 1))) sm4 gi4 hr g4) L t' ht' hn⟩
  · exact GlobalTheory.PrimNorm.isSymmetric_of_hasGen L (exists_gen_of_lbIso L.L _ hiso)

end GlobalTheory.CubeGen
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

namespace GlobalTheory.AmpleBaseChange

theorem relAmple_of_isPullback {S S' : Scheme.{0}} {B : Over S} [IsProper B.hom] {M : LB B.left}
    (hM : M.IsLB) (hA : Out.RelAmple B M) {t : S' ⟶ S} {X : Scheme.{0}} {π : X ⟶ B.left}
    {f : X ⟶ S'} (h : IsPullback π f B.hom t) : Out.RelAmple (Over.mk f) (M.pull π) := by
  have hp : IsProper (Over.mk f).hom := MorphismProperty.of_isPullback (P := @IsProper) h ‹_›
  refine AmpleLocal.relAmple_of_locally S' (Over.mk f) (M.pull π) (pull_isLB hM π)
    inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := t s) trivial
  exact ⟨t ⁻¹ᵁ V, hs, PolBaseChange.relAmple_restrict (A' := Over.mk f) h hM hA V hV⟩

theorem isProjBy_smooth_isProper_geometricallyIntegral :
    ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ B.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f B.hom t → IsProjBy f ∧ Smooth f ∧ IsProper f ∧ GeometricallyIntegral f := by
  intro S B _ M hB hM hA R _ t X π f h
  have := hB.proper
  have hs : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) h hB.smooth
  refine ⟨?_, hs, MorphismProperty.of_isPullback (P := @IsProper) h hB.proper,
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ f hs
      (MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hB.geomConnected)⟩
  obtain ⟨N, -, m, s, hN, hv⟩ := veryAmpleBy_of_relAmple (A := Over.mk f) (pull_isLB hM π)
    (relAmple_of_isPullback hM hA h) (𝟙 X) (Category.id_comp f) (pull_isLB hM π)
    (LBIso.chartPull (chartPullId _) (chartPullPull (M.pull π) (𝟙 X) (𝟙 X) rfl)
      (PolBaseChange.lbIso_refl (pull_isLB hM π)))
  exact ⟨_, hN, m, s, hv⟩

end GlobalTheory.AmpleBaseChange
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}

theorem lbIso_pull_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X}
    (H : LBIso L' (L.pull φ)) (φ' : X'' ⟶ X') : LBIso (L'.pull φ') (L.pull (φ' ≫ φ)) :=
  LBIso.chartPull (chartPullPull L' φ' φ' rfl) (chartPullSame L _ _ _ φ' fun _ => rfl) H

theorem TMap.refl (t : TObj g k J b s) : TMap t t (𝟙 S) := by
  refine ⟨𝟙 _, ?_, ?_, fun i => by simp, fun j => by simp⟩
  · have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
    exact isGrpPullback_of_iso (Iso.refl t.A)
  · exact LBIso.chartPull (chartPullId t.L) (chartPullPull t.L _ _ rfl) (GlobalTheory.PolBaseChange.lbIso_refl t.isLB)

theorem TMap.comp {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h' : TMap t'' t' f') (h : TMap t' t f) : TMap t'' t (f' ≫ f) := by
  obtain ⟨φ, h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨φ', k₁, k₂, k₃, k₄⟩ := h'
  refine ⟨φ' ≫ φ, k₁.comp h₁, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) k₂ (lbIso_pull_comp h₂ φ')
  · rw [← Category.assoc, k₃, Category.assoc, h₃, Category.assoc]
  · rw [← Category.assoc, k₄, Category.assoc, h₄, Category.assoc]

theorem TMap.cancel {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h : TMap t' t f) (n : TMap t'' t (f' ≫ f)) : TMap t'' t' f' := by
  obtain ⟨φ, h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨ψ, k₁, k₂, k₃, k₄⟩ := n
  have hp := h₁.1
  obtain ⟨F, hF, hw⟩ : ∃ F : t''.A.left ⟶ t'.A.left, F ≫ φ = ψ ∧ F ≫ t'.A.hom = t''.A.hom ≫ f' :=
    ⟨hp.lift ψ (t''.A.hom ≫ f') (by rw [k₁.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  subst hF
  refine ⟨F, h₁.cancel k₁ hw, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t.isLB _) (pull_isLB t'.isLB _) k₂ (lbIso_pull_comp h₂ F).symm
  · apply hp.hom_ext
    · rw [Category.assoc, k₃, Category.assoc, Category.assoc, h₃]
    · have a₁ : (t''.pt i).left ≫ t''.A.hom = 𝟙 S'' := Over.w (t''.pt i)
      have a₂ : (t'.pt i).left ≫ t'.A.hom = 𝟙 S' := Over.w (t'.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  · apply hp.hom_ext
    · rw [Category.assoc, k₄, Category.assoc, Category.assoc, h₄]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

theorem tmap_id_comp_cancel : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (s'' : S'' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (t'' : TObj g k J b s''), TMap t t (𝟙 S) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S'), TMap t' t f → (TMap t'' t' f' ↔ TMap t'' t (f' ≫ f)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ t _ _ => ⟨TMap.refl t, fun _ _ h => ⟨fun h' => h'.comp h, fun n => h.cancel n⟩⟩

end GlobalTheory.ZM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.cohomology_logDerivative_adjoint_endomorphisms : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X) φ (f₀ f₀' : P₀.A ⟶ P₀.A) (F' : Matrix (Fin g) (Fin g) K), L.IsLB → LBIso P₀.L (L.pull m) → IsDlog m L dd φ → IsMonHom f₀ → IsMonHom f₀' → LBIso (cubeLB P₀.A ![fst P₀.A P₀.A ≫ f₀, snd P₀.A P₀.A] P₀.L) (cubeLB P₀.A ![fst P₀.A P₀.A, snd P₀.A P₀.A ≫ f₀'] P₀.L) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ x, Cohom f₀.left _ (lc P₀.A.hom (fun y => F' y x) φ) (φ x) := by
  first | exact @GlobalTheory.KS.AdjDlog.cohom_dlog_of_adjoint | exact GlobalTheory.KS.AdjDlog.cohom_dlog_of_adjoint | (intros; apply GlobalTheory.KS.AdjDlog.cohom_dlog_of_adjoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_analytic_kodairaSpencer_class : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D, IsDer x₀ D → ∃ Θ s, KSRel u p m D Θ s := by
  first | exact @GlobalTheory.KS.Exist.exists_ksRel | exact GlobalTheory.KS.Exist.exists_ksRel | (intros; apply GlobalTheory.KS.Exist.exists_ksRel <;> assumption)
end
