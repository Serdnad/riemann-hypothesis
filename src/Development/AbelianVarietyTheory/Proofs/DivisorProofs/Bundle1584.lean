module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle286
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.PlaceCoordsF

variable {F : Type} [Field F] [NumberField F]

def placeAt (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : AF F := pairA F 0 (GlobalTheory.AdelicU.singleFin v x)

theorem placeAt_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    placeAt v (x + y) = placeAt v x + placeAt v y := by
  unfold placeAt pairA
  rw [map_add (f := _)]
  exact Prod.ext (add_zero 0).symm rfl

theorem placeAt_injective (v : HeightOneSpectrum (𝓞 F)) : Function.Injective (placeAt v) := by
  intro x y h
  have h2 := congrArg (fun c : AF F => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c.2) h
  simpa only [placeAt, pairA, GlobalTheory.AdelicU.evalV_singleFin_self] using h2

theorem continuous_placeAt (v : HeightOneSpectrum (𝓞 F)) : Continuous (placeAt v) := by
  unfold placeAt pairA
  exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

theorem eq_placeAt_of_mul {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (hα1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α = 1)
    (hα0 : ∀ v', v' ≠ v → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v' α = 0) {c : AF F} (hc : pairA F 0 α * c = c) :
    c = placeAt v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c.2) := by
  have h1 : c.1 = 0 := by
    have := congrArg Prod.fst hc
    rw [← this]
    exact zero_mul _
  have h2 : α * c.2 = c.2 := congrArg Prod.snd hc
  refine Prod.ext h1 ?_
  show c.2 = GlobalTheory.AdelicU.singleFin v _
  refine GlobalTheory.AdelicU.af_ext fun u => ?_
  by_cases hu : u = v
  · subst hu
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hu, ← h2, map_mul, hα0 u hu, zero_mul]

end GlobalTheory.PlaceCoordsF

namespace GlobalTheory.PlaceCoordsF

theorem coords_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlaceIdemF F v ε → ∀ nS nT : ℕ,
      ∃ (N : ℕ) (Φ : (Fin N → v.adicCompletion F) →+ WOF F E nS nT), Continuous Φ ∧ Function.Injective Φ ∧
        ∀ y : WOF F E nS nT, (∀ i j, algebraMap (AF F) (AEF F E) ε * y i j = y i j) → y ∈ Set.range Φ := by
  intro F E _ _ _ _ _ v ε hε nS nT
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AEF F E) :=
    Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  let e := Fintype.equivFin (Fin nT × Fin nS × Fin (Module.finrank F E))
  let f : (Fin (Fintype.card (Fin nT × Fin nS × Fin (Module.finrank F E))) → v.adicCompletion F) → WOF F E nS nT :=
    fun t i j => B.equivFun.symm (fun l => placeAt v (t (e (i, j, l))))
  have hadd : ∀ s t, f (s + t) = f s + f t := by
    intro s t
    funext i j
    show B.equivFun.symm _ = B.equivFun.symm _ + B.equivFun.symm _
    rw [← map_add (f := _)]
    congr 1
    funext l
    exact placeAt_add v _ _
  let Φ := AddMonoidHom.mk' f hadd
  refine ⟨_, Φ, ?_, ?_, ?_⟩
  · have hB : Continuous B.equivFun.symm := IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap
    exact continuous_pi fun i => continuous_pi fun j =>
      hB.comp (continuous_pi fun l => (continuous_placeAt v).comp (continuous_apply _))
  · intro s t hst
    have key : ∀ i j l, s (e (i, j, l)) = t (e (i, j, l)) := by
      intro i j l
      have h1 : f s i j = f t i j := congrFun (congrFun hst i) j
      have h2 := congrFun (B.equivFun.symm.injective h1) l
      exact placeAt_injective v h2
    funext k
    have := key (e.symm k).1 (e.symm k).2.1 (e.symm k).2.2
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using this
  · intro y hy
    have hc : ∀ i j l, B.equivFun (y i j) l =
        placeAt v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (B.equivFun (y i j) l).2) := by
      intro i j l
      refine eq_placeAt_of_mul hα1 hα0 ?_
      have h1 : pairA F 0 α • y i j = y i j := by rw [Algebra.smul_def]; exact hy i j
      have h2 := congrFun (congrArg B.equivFun h1) l
      rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
      exact h2
    refine ⟨fun k => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (B.equivFun (y (e.symm k).1 (e.symm k).2.1) (e.symm k).2.2).2, ?_⟩
    funext i j
    show B.equivFun.symm _ = y i j
    simp only [Equiv.symm_apply_apply]
    rw [← B.equivFun.symm_apply_apply (y i j)]
    congr 1
    funext l
    rw [B.equivFun.symm_apply_apply]
    exact (hc i j l).symm

end GlobalTheory.PlaceCoordsF
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section
namespace GlobalTheory.Poinc.Renorm

theorem alg_renorm {M : Type} [CommGroup M] {q q₀ a p p₀ g g₀ x y : M} (h₀ : q = y * x⁻¹ * q₀)
    (h₁ : a = g₀ * (q₀ * p₀)⁻¹) (h₂ : p = x * p₀) (h₃ : g = y * g₀) : q * (a * p) = g := by
  rw [h₀, h₁, h₂, h₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

section Norm
open GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem exists_unit_normW (w₀ : W0 U) (hw : w₀.IsGen) (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) :
    ∃ a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ, NormW U w₀ (GlobalTheory.UU.scaleGen a ρ) := by
  let z₀ : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  obtain ⟨JA₀, hA₀⟩ := exists_good' A.isLB z₀
  obtain ⟨JG₀, hG₀⟩ := exists_good' U.LG.isLB z₀
  let eK : Spec (CommRingCat.of (FractionRing R)) ⟶ ((Over.pullback (jK R)).obj G).left :=
    eSec ((Over.pullback (jK R)).obj G)
  have h₁ : eK ≫ U.gen.hom.left = eSec A.A := EvalZero.eK_gen U
  have h₂ : eK ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G := EvalZero.eK_fst
  have hsurj : ∀ u : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z₀)ˣ,
      ∃ a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ, gm (𝟙 _) z₀ ⊤ a = u := by
    intro u
    obtain ⟨V, hV, s, hs⟩ := (Spec (CommRingCat.of (FractionRing R))).presheaf.exists_germ_eq u.val
    obtain rfl : V = ⊤ := eq_top_iff.2 fun y _ =>
      (Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ y) ▸ hV
    have hu : IsUnit s := (Spec (CommRingCat.of (FractionRing R))).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain rfl : z₀ = y := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ y
      exact (congrArg IsUnit hs).mpr u.isUnit
    exact ⟨hu.unit, Units.ext ((gm_val _ z₀ ⊤ trivial _).trans hs)⟩
  obtain ⟨a, ha⟩ := hsurj (val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (jK R) z₀ JG₀ *
    (pw w₀ eK z₀ (JA₀ (eSec A.A)) (JG₀ (jK R ≫ eSec G)) *
      val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) (Z := Spec (CommRingCat.of (FractionRing R)))
        ρ (𝟙 _) z₀ JA₀)⁻¹)
  refine ⟨a, hw, GlobalTheory.UU.scaleGen_isGen a hρ, fun z JA JG hA hG => ?_⟩
  obtain rfl : z₀ = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ z
  have mA : ∀ J, Good A.L z₀ J → U.gen.hom.left (eK z₀) ∈ A.L.U (J (eSec A.A)) := fun J hJ =>
    (congrArg (fun q => q z₀ ∈ A.L.U (J (eSec A.A))) h₁).mpr (hJ _)
  have mG : ∀ J, Good U.LG.L z₀ J → pullback.fst G.hom (jK R) (eK z₀) ∈ U.LG.L.U (J (jK R ≫ eSec G)) := fun J hJ =>
    (congrArg (fun q => q z₀ ∈ U.LG.L.U (J (jK R ≫ eSec G))) h₂).mpr (hJ _)
  have b₀ : gw w₀ eK z₀ (JG (jK R ≫ eSec G)) (fun _ => JA (eSec A.A)) =
      pw w₀ eK z₀ (JA (eSec A.A)) (JG (jK R ≫ eSec G)) := rfl
  have b₁ := pw_trans hw eK z₀ (mA _ hA) (mA _ hA₀) (mG _ hG) (mG _ hG₀)
  have b₂ := val_tr (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1)
    (Z := Spec (CommRingCat.of (FractionRing R))) hρ (𝟙 _) hA hA₀
  have b₃ := val_tr (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rigGen (jK R) hG hG₀
  have b₄ := GlobalTheory.UU.val_scaleGen (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) a ρ (𝟙 _) hA
  rw [h₁, h₂] at b₁
  rw [Fintype.prod_unique, zpow_one] at b₂ b₃
  rw [Category.id_comp] at b₂
  rw [b₀, b₄]
  exact alg_renorm b₁ ha b₂ b₃

end Norm

theorem alg_rig {M : Type} [CommGroup M] (g v : M) (k : ℤ) :
    g ^ (k - 1) * (v ^ k * v⁻¹) = (g * v) ^ k * (g * v)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem alg_frame {M : Type} [CommGroup M] {g t α r : M} {k : ℤ} (h : t ^ k = α * r ^ (1 : ℤ)) :
    (g * t) ^ k = g ^ (k - 1) * α * (g * r) ^ (1 : ℤ) := by
  apply Additive.ofMul.injective
  replace h := congrArg Additive.ofMul h
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at h ⊢
  linear_combination (norm := module) h

section Tors
variable {S : Scheme.{0}} {P : PolAV S}

theorem isTorsFrame_scale (rig : LB.Gen (P.L.pull (eSec P.A))) (a : Γ(S, ⊤)ˣ) {n : ℕ} {T : Over S} {x : T ⟶ P.A}
    {τ τ' : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))}
    (H : IsTorsFrame P rig n x τ) (hτ' : τ'.IsGen)
    (ht : ∀ z J, Good P.L z J → val τ' (𝟙 _) z J = gm T.hom z ⊤ a * val τ (𝟙 _) z J) :
    IsTorsFrame P (GlobalTheory.UU.scaleGen a rig) n x τ' := by
  obtain ⟨hn, -, α, hα, hN, hc⟩ := H
  let u : Γ(P.A.left, ⊤)ˣ := pullU P.A.hom ⊤ a ^ ((n : ℤ) ^ 2 - 1)
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z),
      gm r z ⊤ u = gm (r ≫ P.A.hom) z ⊤ a ^ ((n : ℤ) ^ 2 - 1) := fun Z r z =>
    (map_zpow _ _ _).trans (congrArg (· ^ _) (gm_pull r P.A.hom z ⊤ trivial a))
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) J, Good P.L z J →
      FrameMove.rval (GlobalTheory.UU.scaleGen a rig) r z J = gm r z ⊤ a * FrameMove.rval rig r z J := fun Z r z J hJ =>
    GlobalTheory.UU.val_scaleGen (L := P.L) (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) a rig r hJ
  have hα' : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) J, Good P.L z J →
      val (GlobalTheory.UU.scaleGen u α) r z J = gm r z ⊤ u * val α r z J := fun Z r z J hJ =>
    GlobalTheory.UU.val_scaleGen u α r hJ
  have he : eSec P.A ≫ P.A.hom = 𝟙 S := Over.w η[P.A]
  refine ⟨hn, hτ', GlobalTheory.UU.scaleGen u α, GlobalTheory.UU.scaleGen_isGen u hα, corr_of_val P.isLB fun y J hJ => ?_,
    corr_of_val P.isLB fun y J hJ => ?_⟩
  · have e0 : val α (𝟙 _ ≫ eSec P.A) y J =
        FrameMove.rval rig (𝟙 _) y J ^ ((n : ℤ) ^ 2) * (FrameMove.rval rig (𝟙 _) y J)⁻¹ :=
      (val_pull hJ α (eSec P.A) (𝟙 _)).symm.trans ((val_corr hJ hN (𝟙 _)).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (map_zpow _ _ _) (val_inv _ _))))
    have e1 : val (rigPow P.A P.L (GlobalTheory.UU.scaleGen a rig) ((n : ℤ) ^ 2)) (𝟙 _) y J =
        FrameMove.rval (GlobalTheory.UU.scaleGen a rig) (𝟙 _) y J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_pull hJ, hα' _ _ _ _ hJ, hu, e0, val_mul hJ, e1, val_inv, hr _ _ _ _ hJ, Category.assoc, he,
      Category.id_comp]
    rw [show val (L := P.L) (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) (GlobalTheory.UU.scaleGen a rig) (𝟙 (𝟙_ (Over S)).left) y J = _ from hr _ _ _ _ hJ]
    exact alg_rig (M := (S.presheaf.stalk y)ˣ) _ _ _
  · have a1 : val τ (𝟙 _) y J ^ ((n : ℤ) ^ 2) = val α (𝟙 _ ≫ x.left) y J * FrameMove.rval rig (𝟙 _ ≫ T.hom) y J ^ (1 : ℤ) :=
      (map_zpow _ _ _).symm.trans ((val_corr hJ hc (𝟙 _)).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (val_pull hJ _ _ _) (FrameMove.val_rigT _ _ _ hJ))))
    rw [FrameMove.val_powFrame, val_mul hJ, val_pull hJ, FrameMove.val_rigT _ _ _ hJ, hα' _ _ _ _ hJ, hu,
      hr _ _ _ _ hJ, ht y J hJ, Category.assoc, Over.w x]
    simp only [Category.id_comp] at a1 ⊢
    exact alg_frame a1

end Tors

theorem cst_gm {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]
    (a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ) (z : (TFK (R := R) F).left) :
    (gm (jFK (R := R) F) z ⊤ a).val = cst (R := R) F z (algebraMap (FractionRing R) F
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val)) := by
  rw [← gs_unit _ z ⊤ trivial]
  have e : a.val = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val) := by simp
  conv_lhs => rw [e]
  exact FrameMove.gs_spMap (algebraMap (FractionRing R) F) z _

theorem exists_renorm : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen → ∃ (ρ' : LB.Gen (A.L.pull (eSec A.A))) (c : FractionRing R), c ≠ 0 ∧ NormW U w₀ ρ' ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (x : TFK (R := R) F ⟶ A.A) (fr fr' : FrAt x), IsTorsFrame A ρ N x fr → fr'.IsGen → (∀ z J, Good A.L z J → (val fr' (𝟙 _) z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (algebraMap (FractionRing R) F c)) * (val fr (𝟙 _) z J).val) → IsTorsFrame A ρ' N x fr' := by
  intro R _ _ I D A G _ _ U w₀ hw ρ hρ
  obtain ⟨a, ha⟩ := exists_unit_normW U w₀ hw ρ hρ
  refine ⟨GlobalTheory.UU.scaleGen a ρ, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val, ?_, ha,
    fun F _ _ N x fr fr' H hfr' hv => ?_⟩
  · exact (a.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom).ne_zero
  · refine isTorsFrame_scale ρ a H hfr' fun z J hJ => Units.ext ?_
    rw [Units.val_mul, hv z J hJ]
    exact congrArg (· * _) (cst_gm F a z).symm

end GlobalTheory.Poinc.Renorm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_lintegral_sq_eq_mul_setLIntegral_thetaTransform : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ 𝓕 : Set ((κ → AF F) × (κ → AF F)),
      @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
      ∃ c : ENNReal, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
        ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.ThetaParseval.exists_lintegral_sq_eq_mul_setLIntegral_theta | exact GlobalTheory.ThetaParseval.exists_lintegral_sq_eq_mul_setLIntegral_theta | (intros; apply GlobalTheory.ThetaParseval.exists_lintegral_sq_eq_mul_setLIntegral_theta <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.MatrixUnits₂

theorem exists_order (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] :
    ∃ OB : Subring C, Module.Finite ℤ OB ∧ ∀ b : C, ∃ m : ℕ, 0 < m ∧ (m : C) * b ∈ OB := by
  first
  | exact @_root_.GlobalTheory.MultiplierOrders.exists_order
  | exact _root_.GlobalTheory.MultiplierOrders.exists_order
  | (apply _root_.GlobalTheory.MultiplierOrders.exists_order <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultiplierOrders.exists_order <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultiplierOrders.exists_order <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultiplierOrders.exists_order ..)

theorem isIntV_order_eventually (p : ℕ) [Fact p.Prime] (G : HTGroup p) (OB : Subring G.C)
    (hfin : Module.Finite ℤ OB) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ x ∈ OB, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] x) := by
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := OB)
  have H := Filter.eventually_all.2 fun i : Fin k => Filter.eventually_all.2 fun m =>
    ratCast_mem_intV_eventually p ((Module.finBasis ℚ G.C).repr (g i : G.C) m)
  refine H.mono fun v hv x hx => ?_
  have hx' : (⟨x, hx⟩ : OB) ∈ Submodule.span ℤ (Set.range g) := by rw [hg]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx'
  have e : (1 : Qv v) ⊗ₜ[ℚ] x = ∑ i, ((c i : ℤ) : Qv v) ⊗ₜ[ℚ] (g i : G.C) := by
    have hx2 : x = ∑ i, (c i : ℤ) • (g i : G.C) := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    rw [hx2, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    simp
  rw [e]
  exact isIntV_of_eq_sum G v _ _ _ (fun i _ => intCast_mem _ _) (fun i _ m => hv i m)

end GlobalTheory.OrbFinAf.MatrixUnits₂

namespace GlobalTheory.OrbFinAf.MatrixUnits₂

open Rat.HeightOneSpectrum

def theta (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) [Fact (primesEquiv v.1 : ℕ).Prime] :
    ℚ_[(primesEquiv v.1 : ℕ)] ⊗[ℚ] G.C ≃ₐ[ℚ] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.congr (adicCompletion.padicEquiv v.1).symm.toAlgEquiv AlgEquiv.refl

theorem theta_tmul (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) [Fact (primesEquiv v.1 : ℕ).Prime]
    (r : ℚ_[(primesEquiv v.1 : ℕ)]) (c : G.C) :
    theta p G v (r ⊗ₜ c) = (adicCompletion.padicEquiv v.1).symm r ⊗ₜ c := rfl

theorem padicEquiv_symm_coe_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) [Fact (primesEquiv v.1 : ℕ).Prime]
    (r : ℤ_[(primesEquiv v.1 : ℕ)]) :
    (adicCompletion.padicEquiv v.1).symm (r : ℚ_[(primesEquiv v.1 : ℕ)]) ∈ v.1.adicCompletionIntegers ℚ := by
  obtain ⟨x, hx, hxr⟩ := (adicCompletion.padicEquiv_bijOn v.1).surjOn
    (show (r : ℚ_[(primesEquiv v.1 : ℕ)]) ∈ PadicInt.subring _ from r.2)
  rw [← hxr, ContinuousAlgEquiv.symm_apply_apply]
  exact hx

end GlobalTheory.OrbFinAf.MatrixUnits₂

namespace GlobalTheory.OrbFinAf.MatrixUnits₂

open Rat.HeightOneSpectrum GlobalTheory.LKInvGood

theorem isIntV_theta_locOrder (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p)
    [Fact (primesEquiv v.1 : ℕ).Prime] (OB : Subring G.C)
    (hO : ∀ x ∈ OB, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] x)) (h1 : IsIntV G v 1)
    (hmul : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z))
    (y : ℚ_[(primesEquiv v.1 : ℕ)] ⊗[ℚ] G.C) (hy : y ∈ locOrder (primesEquiv v.1 : ℕ) OB) :
    IsIntV G v (theta p G v y) := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [theta_tmul, map_one]
    exact hO c hc
  | algebraMap r =>
    rw [Algebra.TensorProduct.algebraMap_apply, theta_tmul]
    intro k
    rw [basV_repr_tmul]
    have h1k := h1 k
    rw [Algebra.TensorProduct.one_def, basV_repr_tmul, one_mul] at h1k
    exact mul_mem (padicEquiv_symm_coe_mem p G v r) h1k
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact isIntV_add' G v hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact hmul _ _ hx hy

theorem finite_dvd (p : ℕ) (N : ℕ) (hN : 0 < N) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ¬ (primesEquiv v.1 : ℕ) ∣ N := by
  have hfin : {v : AwayP p | (primesEquiv v.1 : ℕ) ∣ N}.Finite := by
    have hinj : Function.Injective fun v : AwayP p => (primesEquiv v.1 : ℕ) :=
      fun a b h => Subtype.ext (primesEquiv.injective (Subtype.ext h))
    refine Set.Finite.of_finite_image ?_ hinj.injOn
    refine (Set.finite_le_nat N).subset ?_
    rintro _ ⟨v, hv, rfl⟩
    exact Nat.le_of_dvd hN hv
  exact hfin.eventually_cofinite_notMem

theorem matrixUnits_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ E : Fin G.n → Fin G.n → Qv v ⊗[ℚ] G.C,
      (∀ i j k l, E i j * E k l = if j = k then E i l else 0) ∧ ∑ i, E i i = 1 ∧
      ∀ i j, IsIntV G v (E i j) := by
  intro p _ G
  obtain ⟨OB, hfin, hspan⟩ := exists_order G.C
  obtain ⟨N, hN, hmat⟩ := GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all G.F G.C G.n G.rankC OB hfin hspan
  filter_upwards [finite_dvd p N hN, isIntV_order_eventually p G OB hfin, intV_order_eventually p G]
    with v hv hO hord
  haveI : Fact (primesEquiv v.1 : ℕ).Prime := ⟨(primesEquiv v.1).2⟩
  obtain ⟨ψ, -⟩ := hmat (primesEquiv v.1 : ℕ) hv
  let E : Fin G.n → Fin G.n → Qv v ⊗[ℚ] G.C := fun i j =>
    theta p G v ((ψ.symm (Matrix.single i j 1) : locOrder (primesEquiv v.1 : ℕ) OB) :
      ℚ_[(primesEquiv v.1 : ℕ)] ⊗[ℚ] G.C)
  refine ⟨E, fun i j k l => ?_, ?_, fun i j =>
    isIntV_theta_locOrder p G v OB hO hord.1 hord.2.1 _ (ψ.symm _).2⟩
  · simp only [E]
    rw [← map_mul, ← Subalgebra.coe_mul, ← map_mul]
    split_ifs with hjk
    · subst hjk
      rw [Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := hjk), map_zero, ZeroMemClass.coe_zero, map_zero]
  · have hs : ∑ i, (Matrix.single i i (1 : cenOrder (primesEquiv v.1 : ℕ) G.F) :
        Matrix (Fin G.n) (Fin G.n) (cenOrder (primesEquiv v.1 : ℕ) G.F)) = 1 := by
      ext a b
      rw [Matrix.sum_apply, Matrix.one_apply, Finset.sum_eq_single a]
      · by_cases h : a = b
        · subst h; simp [Matrix.single_apply]
        · simp [Matrix.single_apply, h]
      · intro c _ hc; simp [Matrix.single_apply, hc]
      · simp
    simp only [E]

    rw [← map_sum (theta p G v), ← AddSubmonoidClass.coe_finsetSum, ← map_sum ψ.symm, hs, map_one,
    OneMemClass.coe_one, map_one]

end GlobalTheory.OrbFinAf.MatrixUnits₂
end
end
