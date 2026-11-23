module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PolKerAtPullbackOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle709
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle950
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
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

noncomputable section
namespace GlobalTheory.ZM.FieldPoint

theorem exists_secCoord_of_subsingleton_pic {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} (σ : I → M.Sec)
    {A : Type} [CommRing A] [Subsingleton (CommRing.Pic A)] (x : Sp A ⟶ X) : ∃ v : I → A, SecCoord M σ x v := by
  have hL := LB.isLB_pull hM x
  obtain ⟨t, ht⟩ := GlobalTheory.LB.exists_isGen_of_subsingleton_pic hL
  let a := ReciprocityTheory.ChartRestriction.G.DVR.genSec t ht
  have ha : ⊤ ≤ nonzeroLocus a := (nonzeroLocus_genSec hL t ht).ge
  choose v hv using fun j => fnOn_top_bijective.2 (resG _ ha (secRatio a (secPull (σ j) x)))
  refine ⟨v, t, ht, fun i j h => ?_⟩
  have h1 := secRatio_on a (secPull (σ i) x) j (le_top.trans ha) le_rfl
  rw [resG_self, resG_self] at h1
  change _ = fnOn _ (v i) * a.f j
  rw [← resG_fnOn (le_top : _ ≤ ⊤), hv, resG_resG]
  exact h1

theorem exists_secCoord : ∀ (o : Type) [CommRing o] (m : ℕ) (K : Type) [Field K] (y : Sp K ⟶ PSpace o m),
    ∃ v : Fin (m + 1) → K, SecCoord (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) y v :=
  fun o _ m _ _ y => exists_secCoord_of_subsingleton_pic (O1_isLB o m) _ y

end GlobalTheory.ZM.FieldPoint
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.LevelZero

variable {R : Type} [CommRing R]

theorem pull_iso_bijective {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem cechC_pull_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (A' : Type) [CommRing A'] [Algebra A A'], Module.Finite A A' → ∀ (k : ℕ) (i : ℤ),
    Function.Bijective (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) := by
  intro q _ A _ hA hq A' _ _ hfin k i
  obtain ⟨e0, e, h1, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI := hfin
  have hT : Module.Finite A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) := inferInstance
  have hr0 := GlobalTheory.T.laurentC_pullback_bijective_finite_strictlyHenselian q A hA hq (PiTensorProduct A (fun _ : Fin (k + 1) => A')) hT i
  have hmap := congrArg (fun f => disc.map f) h1
  simp only [Functor.map_comp] at hmap
  have heq : ∀ x, pull _ (disc.map e.hom) (tw q i) 0 (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0 x) =
      pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q i) 0
        (pull _ (disc.map e0.hom) (tw q i) 0 x) := by
    intro x
    rw [← pull_comp, hmap, pull_comp]
    rfl
  have hcomp : (pull _ (disc.map e.hom) (tw q i) 0) ∘ (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) =
      (pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q i) 0) ∘
        (pull _ (disc.map e0.hom) (tw q i) 0) := funext heq
  have he : Function.Bijective (pull _ (disc.map e.hom) (tw q i) 0) :=
    pull_iso_bijective (disc.mapIso e) (tw q i) 0
  have he0 : Function.Bijective (pull _ (disc.map e0.hom) (tw q i) 0) :=
    pull_iso_bijective (disc.mapIso e0) (tw q i) 0
  rw [← Function.Bijective.of_comp_iff' he, hcomp]
  exact hr0.comp he0

end GlobalTheory.EtC.GmStep.LevelZero
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem cech_level_acyc : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 0 < s → Subsingleton (Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) s i) := by
  intro q _ A _ hA hq A' _ _ hfin k s i hs
  obtain ⟨e0, -, -, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI : Subsingleton (Ht q (sp (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) s i) :=
    GlobalTheory.T.finite_strictlyHenselian_tateTwist_acyclic q A hA hq _ inferInstance s i hs
  let f : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌)) :=
    disc.map e0.hom
  let g : disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌)) ⟶ sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) :=
    disc.map e0.inv
  have hgf : g ≫ f = 𝟙 _ := by
    exact (disc.mapIso e0).inv_hom_id
  have hinj : Function.Injective (pull (ZMod q) f (tw q i) s) := by
    intro x y hxy
    have := congrArg (pull (ZMod q) g (tw q i) s) hxy
    rwa [← pull_comp, ← pull_comp, hgf, pull_id, pull_id] at this
  exact hinj.subsingleton

end GlobalTheory.EtC.GmStep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

theorem _root_.GlobalTheory.T.pullback_sections_group_scheme : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (ψA : A'.left ⟶ (topS Rg ⊗ A).left), IsGrpPullback A' A t φA' → ψA ≫ (snd (topS Rg) A).left = φA' → ∀ (d : Fin mA → Γ(Sp R, ⊤)), (∀ (j : Fin 1 → L.ι) (x : A'.left), x ∈ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j → ∃ (W : A'.left.Opens) (hW : W ≤ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j), x ∈ W ∧ ∑ i, (A'.hom.appLE ⊤ W (by simp)).hom (d i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j) W (hW.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j))).hom ((bA i).f j) = 0) → d = 0 := by
  first | (exact @GlobalTheory.HomFixIndep.pulled_basis_indep) | (exact GlobalTheory.HomFixIndep.pulled_basis_indep) | (intros; apply GlobalTheory.HomFixIndep.pulled_basis_indep  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

theorem _root_.GlobalTheory.T.homomorphisms_same_matrix_isomorphic_test_data : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A₁ B₁ : Over (Sp R)) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) (A₂ B₂ : Over (Sp R)) [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → IsTest A B L M t A₂ B₂ φA₂ φB₂ Φ₂ → IsMat L M k bA bB eA eB t A₁ B₁ φA₁ φB₁ Φ₁ c → IsMat L M k bA bB eA eB t A₂ B₂ φA₂ φB₂ Φ₂ c → IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ (𝟙 (Sp R)) := by
  first | exact @GlobalTheory.HomFixMat.mat_determines | exact GlobalTheory.HomFixMat.mat_determines | (intros; apply GlobalTheory.HomFixMat.mat_determines <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylor_isLevelLift_of_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N' s') (f : S' ⟶ S) (om : ObjMap (o'.forget N hd hc) o f) (T : Over S) (g : T.left ⟶ S') (lv : D.La → (T ⟶ o.A)), g ≫ f = T.hom → (∀ a, (lv a).left = g ≫ (o'.eta a).left ≫ om.φ) → IsLift o N' T lv := by
  first | exact @GlobalTheory.UPel.HT.isLift_of_point | exact GlobalTheory.UPel.HT.isLift_of_point | (intros; apply GlobalTheory.UPel.HT.isLift_of_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.isoNormalisation_at_zeroSection : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)ˣ), (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Normal t c αA βB → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ (φB' ≫ GlobalTheory.HomFixUniv.θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p) (by simp)).hom (c i j) *
          ((φA' ≫ GlobalTheory.HomFixUniv.θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (u p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  first | (exact @GlobalTheory.HomFixNorm.norm_at_zero) | (exact GlobalTheory.HomFixNorm.norm_at_zero) | (intros; apply GlobalTheory.HomFixNorm.norm_at_zero  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.isOpen_generatingCombinationMatrixLocus : ∀ (Rg : Type) [CommRing Rg] (A₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) [UniversallyClosed f] (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N), N.IsLB → ∃ U : (Sp (MvPolynomial (Fin (mA * mB)) Rg)).Opens, ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.Generates a φ p (matOf g) ↔ ∀ τ, g τ ∈ U) := by
  first | (exact @GlobalTheory.HomFixOpen.main) | (exact GlobalTheory.HomFixOpen.main) | (intros; apply GlobalTheory.HomFixOpen.main  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.unitTensorStructureMap_flat_projective_univClosed : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → Flat (GlobalTheory.HomFixUniv.fA A) ∧ GlobalTheory.AbLaw.IsProjBy (GlobalTheory.HomFixUniv.fA A) ∧ UniversallyClosed (GlobalTheory.HomFixUniv.fA A) := by
  first | (exact @GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed) | (exact GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed) | (intros; apply GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.polKerAt_pullback_of_isGrpPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁' : B₁ ⟶ o₁.A) (ψ' : B ⟶ o.A) (c : ℕ), IsGrpPullback B₁ B t θ → θ ≫ ψ'.left = ψ₁'.left ≫ m.φ → (PolKerAt o ψ' c t ↔ PolKerAt o₁ ψ₁' c (𝟙 T)) := by
  first | exact @UpperTheory.Cb.polKerAt_pullback_of_isGrpPullback | exact UpperTheory.Cb.polKerAt_pullback_of_isGrpPullback
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

set_option autoImplicit false

namespace GlobalTheory.CoverDeg

theorem exists_goodCover_of_coords_of_cover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (x : X) (U₁ U₂ : X.Opens), IsAffineOpen U₁ → x ∈ U₁ → (∃ t : Fin D → Γ(X, U₁), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t).Etale) → IsAffineOpen U₂ → x ∈ U₂ → IsAffineOpen (π ⁻¹ᵁ U₂) → (π.app U₂).hom.Etale → (π.app U₂).hom.Finite → (letI := (π.app U₂).hom.toAlgebra; Module.Free Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) ∧ Module.finrank Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) = δ) → ∃ U : X.Opens, x ∈ U ∧ GlobalTheory.CoverDeg.GoodCover p π D δ U := by
  intro k _ X Y p π D δ x U₁ U₂ hU₁ hx₁ ⟨t, ht⟩ hU₂ hx₂ hV₂ he hf hfr
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU₁ hU₂ x ⟨hx₁, hx₂⟩
  have hxU : x ∈ X.basicOpen g := hfg ▸ hxf
  refine ⟨X.basicOpen g, hxU, ?_⟩
  have hUU₁ : X.basicOpen g ≤ U₁ := hfg ▸ X.basicOpen_le f
  have hUU₂ : X.basicOpen g ≤ U₂ := X.basicOpen_le g
  have hUa : IsAffineOpen (X.basicOpen g) := hU₂.basicOpen g
  have hpre : π ⁻¹ᵁ X.basicOpen g = Y.basicOpen (π.app U₂ g) := Scheme.preimage_basicOpen π g
  have hVa : IsAffineOpen (π ⁻¹ᵁ X.basicOpen g) := hpre ▸ hV₂.basicOpen _
  have hVV₂ : π ⁻¹ᵁ X.basicOpen g ≤ π ⁻¹ᵁ U₂ := fun _ h => hUU₂ h
  refine ⟨hUa, hVa, ?_, ?_⟩
  · refine ⟨fun i => resG X hUU₁ (t i), ?_⟩
    have e : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (X.basicOpen g)) (fun i => resG X hUU₁ (t i)) =
        (resG X hUU₁).comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t) := by
      rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]
    rw [e]
    have hR : (resG X hUU₁).Etale := by
      letI : Algebra Γ(X, U₁) Γ(X, X.basicOpen g) := (resG X hUU₁).toAlgebra
      haveI : IsLocalization.Away f Γ(X, X.basicOpen g) :=
        hU₁.isLocalization_of_eq_basicOpen f (homOfLE hUU₁) hfg.symm
      exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)
    exact RingHom.Etale.stableUnderComposition _ _ ht hR
  · letI i1 : Algebra Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) := (π.app U₂).hom.toAlgebra
    letI i2 : Algebra Γ(X, U₂) Γ(X, X.basicOpen g) := (resG X hUU₂).toAlgebra
    letI i3 : Algebra Γ(Y, π ⁻¹ᵁ U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) := (resG Y hVV₂).toAlgebra
    letI i4 : Algebra Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) := (π.app (X.basicOpen g)).hom.toAlgebra
    letI i5 : Algebra Γ(X, U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      ((π.app (X.basicOpen g)).hom.comp (resG X hUU₂)).toAlgebra
    have hnat : (π.app (X.basicOpen g)).hom.comp (resG X hUU₂) = (resG Y hVV₂).comp (π.app U₂).hom := by
      ext a
      exact congr($(π.naturality (homOfLE hUU₂).op) a)
    haveI : IsScalarTower Γ(X, U₂) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq' hnat
    haveI : IsLocalization.Away g Γ(X, X.basicOpen g) :=
      hU₂.isLocalization_of_eq_basicOpen g (homOfLE hUU₂) rfl
    haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ U₂) (Submonoid.powers g))
        Γ(Y, π ⁻¹ᵁ X.basicOpen g) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      exact hV₂.isLocalization_of_eq_basicOpen (π.app U₂ g) (homOfLE hVV₂) hpre
    haveI hpo : Algebra.IsPushout Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      Algebra.isPushout_of_isLocalization (Submonoid.powers g) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ U₂)
        Γ(Y, π ⁻¹ᵁ X.basicOpen g)
    have het : (algebraMap Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g)).Etale :=
      RingHom.Etale.isStableUnderBaseChange _ _ _ _ he
    haveI : Module.Finite Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) := hf
    haveI hfin : Module.Finite Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      Module.Finite.of_isLocalization Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) (Submonoid.powers g)
    refine ⟨het, hfin, ?_⟩
    obtain ⟨hfree, hrk⟩ := hfr
    haveI : Nontrivial Γ(X, X.basicOpen g) := (X.presheaf.germ _ x hxU).hom.domain_nontrivial
    haveI : Nontrivial Γ(X, U₂) := (X.presheaf.germ _ x hx₂).hom.domain_nontrivial
    let b := Module.Free.chooseBasis Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂)
    let b' := hpo.symm.out.basis b
    refine ⟨Module.Free.of_basis b', ?_⟩
    rw [Module.finrank_eq_card_basis b', ← hrk, Module.finrank_eq_card_basis b]

end GlobalTheory.CoverDeg
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.unitaryChartSection_fderiv_below_diagonal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (z : V (nd X)) (τ : X.Ψ) (a b : Fin r), b < a → dY X z τ a b = nmat X z τ a b := by
  first | exact @GlobalTheory.SUChartSection.dY_lower | exact GlobalTheory.SUChartSection.dY_lower | (intros; apply GlobalTheory.SUChartSection.dY_lower <;> assumption)
end
