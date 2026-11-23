module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTranslateLiesOverProductTorsionFra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle540
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRootStalk
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2065
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle040
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle090
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle125
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle038
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep.TwistTranslate
open GlobalTheory.UT.CoefBasic GlobalTheory.AdicSum GlobalTheory.Poinc.Tors.AnyField GlobalTheory.Poinc.Tors.ValPair GlobalTheory.Poinc.Tors.Translate

variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

theorem x_add (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A))
    (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) (a τ : X₁.S.Gam)
    (xτ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (hτ : xτ.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) :
    x (a + τ) = x a * xτ := by
  let U : Over.mk ((TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk (spMap 𝔪.yK) (by
      show spMap 𝔪.yK ≫ 𝟙 _ = _
      rw [Category.comp_id]
      change _ = Spec.map (𝟙 _) ≫ _
      rw [Spec.map_id, Category.id_comp])
  have key := 𝔪.cart.2 (TFK (R := V) (FractionRing V)) (x a) xτ (U ≫ X₁.ρ.pt a) (U ≫ X₁.ρ.pt τ)
    (hx a).symm hτ.symm
  rw [← MonObj.comp_mul, ← X₁.ρ.pt_add] at key
  apply Over.OverMorphism.ext
  refine 𝔪.cart.1.hom_ext ?_ ?_
  · rw [hx (a + τ), ← key]; rfl
  · rw [Over.w, Over.w]

theorem eq_yK_zeta_pow (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (u : FractionRing V)
    (hu : u ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1) : ∃ e : ℕ, u = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) := IsFractionRing.charZero V
  set k := (X₁.S.r * X₁.S.N) ^ 2 with hk
  have hkpos : 0 < k := by
    have h1 := X₁.S.r_pos; have h2 := X₁.S.N_ge
    positivity
  have hinj : Function.Injective (algebraMap X₁.o₁ X₁.S.R) := by
    intro a b hab
    apply X₁.ar.inj
    have := congrArg (fun x : X₁.S.R => (x : X₁.Ω₁)) hab
    simpa using this
  have hR : IsPrimitiveRoot (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) k := X₁.S.prim.map_of_injective hinj
  have hroot : (Polynomial.cyclotomic k (FractionRing V)).IsRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) := by
    have h := (hR.isRoot_cyclotomic hkpos).map (f := 𝔪.yK)
    rwa [Polynomial.map_cyclotomic] at h
  haveI : NeZero (k : FractionRing V) := ⟨by exact_mod_cast hkpos.ne'⟩
  have hK : IsPrimitiveRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) k :=
    (Polynomial.isRoot_cyclotomic_iff).1 hroot
  obtain ⟨e, -, he⟩ := hK.eq_pow_of_pow_eq_one hu
  exact ⟨e, by rw [map_pow, map_pow, he]⟩

theorem exists_rig_torsFrame (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ)
    (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a))
    (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left)
    (hfr : ∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) :
    ∃ ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A)), ρA.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  have gp := 𝔪.cart
  have hw := 𝔪.wl_gen
  obtain ⟨rig', hrig', Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) hw X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm gp) X₁.ρ.rig X₁.ρ.rig_gen
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over _)).left) (z : Z) J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      GlobalTheory.FrameMove.rval X₁.ρ.rig (r ≫ spMap 𝔪.yK) z J =
        GlobalTheory.ConstFam.wVal 𝔪.wl z J J' (r ≫ eSec 𝔪.A.A) * GlobalTheory.FrameMove.rval rig' r z J' :=
    fun Z r z J J' hJ hJ' =>
      (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  refine ⟨rig', hrig', fun a => ?_⟩
  exact GlobalTheory.FrameMove.isTorsFrame_move gp hw hr (hx a) (X₁.ρ.fr_tors a) (hfr a).1
    (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)

theorem over_translate (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (w₀ : W0 𝔪.U.toUnifPre) (hw₀ : w₀.IsGen)
    (ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρA.IsGen) (x₁ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)
    (e₁ : FrAt x₁) (he₁ : IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) x₁ e₁)
    (g₁ : GtPtF 𝔪.D.toPre (FractionRing V)) (w₁ : Frm 𝔪.D.toPre (FractionRing V) 1 g₁.b)
    (hg₁ : ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₁ o ∧ o.IsZero) (hw₁ : w₁.IsGen) (H₁ : 𝔪.Over' w₀ g₁ w₁ x₁ e₁)
    (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) (hχ : χ ^ (X₁.S.r * X₁.S.N) = 1)
    (g₀ : GtPtF 𝔪.D.toPre (FractionRing V)) (ht : IsTor χ g₀)
    (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)
    (_ : p.y = 0) (hp : p.g = g₀) (hx : QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x)
    (g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (hadd : g₁.IsAdd g₀ g₂) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b)
    (hww : ∀ z J, Good 𝔪.D.toPre.P.L z J → val w₂ (𝟙 _) z J = val w₁ (𝟙 _) z J)
    (x₂ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (hx₂ : x₂ = x₁ * x) :
    ∃ e₂ : FrAt x₂, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) x₂ e₂ ∧ 𝔪.Over' w₀ g₂ w₂ x₂ e₂ := by
  obtain ⟨o, ho, _⟩ := hg₁
  subst hp
  have hB : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  haveI := 𝔪.cn.2.2.2
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (lt_of_lt_of_le two_pos X₁.S.N_ge)
  obtain ⟨w, hw, vw⟩ := exists_gen 𝔪.D.toPre.P.isLB (φ' := DegPre.lineφ 𝔪.D.toPre _ g₂.b) (ε' := DegPre.lineε 1)
    (fun U _ h => by rw [(ThetaAverage.val_translate ht hadd).1]) w₁ hw₁
  have vw' := fun z J hJ => vw _ (𝟙 _) z J hJ
  obtain ⟨e₂, he₂, H₂⟩ := exists_liesOver hB 𝔪.semi 𝔪.U hw₀ hn hw₁ he₁.2.1 H₁ hχ p ht hx hadd hw vw' hx₂
  refine ⟨e₂, isTorsFrame_of_liesOver hB 𝔪.semi 𝔪.U hw₀ hρ hn ho hw₁ he₁ H₁ hχ ht hadd hw vw' ?_ he₂ H₂,
    fun k hk wk e => H₂ k hk wk fun z J hJ => by rw [e z J hJ, hww z J hJ, vw' z J hJ]⟩
  rw [hx₂, mul_pow, he₁.1, (hx w₀ hw₀).1, _root_.mul_one]


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem twistSum_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → ∃ e : ℕ, SumF (maximalIdeal V) (FractionRing V) (fun mu : X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀ C lab _ T hT c τ _ χ hχ hyp
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hTc⟩ := hT
  obtain ⟨ρA, hρA, htors⟩ := exists_rig_torsFrame 𝔪 x fr hx hfr
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' c) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w'', hw''g, hw''v⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w''.IsGen ∧ ∀ z J, val w'' (𝟙 _) z J = val (w c) (𝟙 _) z J := by
    revert hb
    generalize (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w c, (hc c).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := over_translate 𝔪 w₀ hw₀ ρA hρA (x (lab c)) (fr (lab c)) (htors _)
    (g' c) (w c) (hc c).1 (hc c).2.1 (hc c).2.2 χ hχ _ hg₀ p xτ hpy hpg hq _ hadd w'' (fun z J _ => hw''v z J)
    (x (lab c + τ)) (x_add 𝔪 x hx (lab c) τ xτ hxτ)
  obtain ⟨u, hu, hval⟩ := GlobalTheory.Poinc.TorsRatio.valAt_torsFrame_ratio V 𝔪.A ρA hρA _
    (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) _ _ _
    (htors (lab c + τ)) he₂ th _ (hth (lab c + τ))
  have hsum := hov 1 le_rfl w'' (fun z J _ => (pow_one _).symm) hw''g th s _ hs hval
  obtain ⟨e, he⟩ := eq_yK_zeta_pow 𝔪 u hu
  refine ⟨e, ?_⟩
  rw [← he]
  have hco : ∀ χ', coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w'' χ' =
      ((χ (Multiplicative.ofAdd χ') : (FractionRing V)ˣ) : FractionRing V) * coef s (g' c) (w c) χ' := fun χ' => by
    rw [GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd (hc c).2.1 (c := 1) (fun z J _ => by rw [hw''v, map_one, _root_.one_mul]) s χ',
      _root_.one_mul]
  have hA := admissibleBase_of_completeNormalLocalCharZero 𝔪.cn
  have key := ((GlobalTheory.AdicSum.sumF_calculus V _ hA (FractionRing V) _
    (coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w'') 0 _ 0).2.2 X 𝔪.e₈
    𝔪.e₈.injective (fun j hj => absurd ⟨𝔪.e₈.symm j, 𝔪.e₈.apply_symm_apply j⟩ hj)).2 hsum
  convert key using 2 with mu
  simp only [Function.comp_apply, hco, hTc]

end GlobalTheory.GSep.TwistTranslate
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.DvrScale

open GlobalTheory.TorusExt GlobalTheory.ZH.TestVal GlobalTheory.ThetaDvr.Scale GlobalTheory.Poinc.IntTerm.DvrScale
open Classical


attribute [local instance] gtGroup in
theorem exists_dvd_pow : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ b, ∀ a, ∃ (w : X) (r : V), 𝔪.YY a w ∧ 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) * algebraMap V (FractionRing V) (t w) := by
  intro I X₁ z₁ act V _ _ _ _ ev X _ t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hc : IsAdicComplete (maximalIdeal V) V := 𝔪.cn.2.2.1
  obtain ⟨hL, hL₂⟩ := abelianSchemeLaws_all
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  have hm := odd_level' X₁.ρ
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, hc⟩
  have hB := 𝔪.D.tau_bimult
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using QForm.exists_QVal hϖ 𝔪.D
  obtain ⟨v, hv, -⟩ := GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) := by
    have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨t', ht⟩ := hsec 1 X₁.ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW 𝔪.U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G
    𝔪.semi 𝔪.U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ rig hw₀ th ϑ hE hP
    _ hm hu
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t'
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r
  set Fc := AlgebraicClosure (FractionRing V) with hF
  set y₀ : X₁.S.R →+* Fc := (algebraMap (FractionRing V) Fc).comp 𝔪.yK with hy₀
  have tv : ∀ a z J, Good 𝔪.A.L z J → cst (R := V) Fc z sc *
      @id ((TF (R := V) Fc).left.presheaf.stalk z) (sA th (ptSecT 𝔪.A.A (x a)).left z J) =
      cst (R := V) Fc z (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) * @id ((TF (R := V) Fc).left.presheaf.stalk z)
        (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := X₁.ρ.th_val a
      rw [← powFrame_one' (X₁.ρ.pt a) (X₁.ρ.fr a)] at b
      exact b) z J hJ)
  have ex : ∀ a, ∃ q, QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) := fun a => by
    obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
    exact ⟨q, (f₁ _ _).2 hq.symm⟩
  have yyOf : ∀ a q (χ : 𝔪.D.toPre.X), QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) →
      𝔪.YY a (𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y)) := fun a q χ hq =>
    ⟨qkShift hB q χ, x a, by
      rw [AddEquiv.apply_symm_apply]
      show q.y + (X₁.S.r * X₁.S.N) • χ = _
      rw [add_comm],
      (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB q _))), hx a⟩
  have hM2 : (X₁.S.r * X₁.S.N) ^ 2 ≠ 0 := pow_ne_zero _ hm.pos.ne'
  by_cases h0 : sc = 0
  · have z0 : ∀ a, y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0 := fun a => by
      obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := Fc)
      obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) Fc).left) 𝔪.A.isLB z
      have := tv a z J hJ
      rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
      exact CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    have z1 : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0 := fun a =>
      (map_eq_zero_iff _ (algebraMap (FractionRing V) Fc).injective).1 (z0 a)
    refine ⟨0, fun a => ?_⟩
    obtain ⟨q, hq⟩ := ex a
    refine ⟨_, 0, yyOf a q 0 hq, ?_⟩
    rw [z1 a, zero_pow hM2, map_zero, zero_mul, zero_mul]

  have tv' : ∀ a z J, Good 𝔪.A.L z J → sA th (ptSecT 𝔪.A.A (x a)).left z J =
      @id ((TFK (R := V) Fc).left.presheaf.stalk z)
        (cst (R := V) Fc z (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)) *
        (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have hvs : v sc ≠ ⊤ := v.ne_top_iff.2 h0
  have split : ∀ a, v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) := fun a => by
    rw [← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = 0 → v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc :=
    fun a h => by rw [split a, h, add_zero]
  have h2 : 2 ≤ X₁.S.r * X₁.S.N := X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  obtain ⟨b, hb⟩ : ∃ b, v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) = v sc := by
    obtain ⟨p₀, hp₀⟩ := exists_qkPt (F := Fc) H.1.mulN (Or.inr H.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) hm.pos.ne' 0
    obtain ⟨q', x', -, hx', -, hval⟩ := (key p₀ (f p₀) ((f₁ _ _).2 rfl)).2 (X₁.S.r * X₁.S.N) h2 dvd_rfl hp₀
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    exact ⟨a', nz a' (hval _ _ (he a') (tv' a'))⟩
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hvs
  refine ⟨b, fun a => ?_⟩
  obtain ⟨q, hq₁⟩ := ex a
  obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := Int.exists_least_of_bdd (P := fun k => ∃ χ, Q ((X₁.S.r * X₁.S.N) • χ + q.y) = k)
    ⟨0, by
      rintro _ ⟨χ, rfl⟩
      by_cases c : (X₁.S.r * X₁.S.N) • χ + q.y = 0
      · rw [c, QForm.Q_zero hϖ 𝔪.D hQ]
      · exact zero_le_one.trans (QForm.Q_pos hϖ 𝔪.D hQ c)⟩ ⟨_, 0, rfl⟩
  have hk := ((key q _ hq₁).1 _ _ (he a) (tv' a)).1
    ((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ)) fun χ' =>
      div_le_div_of_nonneg_right (Int.cast_le.2 (hχ _ ⟨χ', rfl⟩)) (Nat.cast_nonneg _)
  set w := 𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y) with hw
  have hew : 𝔪.e₈ w = (X₁.S.r * X₁.S.N) • χ + q.y := AddEquiv.apply_symm_apply _ _
  have hmono : v (algebraMap (FractionRing V) Fc (algebraMap V (FractionRing V) (t w))) =
      (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ) := by
    obtain ⟨u, hpc⟩ := 𝔪.psi w
    rw [hew] at hpc
    exact hv _ _ (hasVal_of_unit_mul u (GlobalTheory.ValForm.hasVal_coord (hQ _) hpc))
  have hb0 : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := fun h => hvs (by
    rw [← hb]; show v (algebraMap (FractionRing V) Fc (𝔪.yK _)) = ⊤; rw [h, map_zero, AddValuation.map_zero])
  have hne : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) *
      algebraMap V (FractionRing V) (t w) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hb0)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2
        (let ⟨_, h⟩ := 𝔪.psi w; right_ne_zero_of_mul (PsiCoordLocal.ne_zero_of_coord h)))
  have hle : v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) *
      algebraMap V (FractionRing V) (t w))) ≤
      v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2))) := by
    rw [map_mul, map_pow, map_pow, v.map_mul, v.map_pow, v.map_pow, hmono]
    change (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) + _ ≤
      (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)
    rw [hb, split a, ← hs]

    have hN : (((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM2
    have e : (((X₁.S.r * X₁.S.N) ^ 2 • (s : WithTop ℚ)) + (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ)) =
        (X₁.S.r * X₁.S.N) ^ 2 • ((s : WithTop ℚ) +
          (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) : WithTop ℚ)) := by
      rw [← WithTop.coe_add, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_eq_coe,
        nsmul_eq_mul, nsmul_eq_mul, mul_add, mul_div_cancel₀ _ hN]
    rw [e]
    exact nsmul_le_nsmul_right (add_le_add le_rfl hk) _
  obtain ⟨r', hr', -⟩ := GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hne hle
  refine ⟨w, r', yyOf a q χ hq₁, ?_⟩
  rw [hr', _root_.mul_assoc]

end GlobalTheory.GSep.DvrScale
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep

theorem GMem.yK_th_ne_zero : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀ hd h0
  obtain ⟨c, -, h⟩ := GlobalTheory.ZH.GoodOut.exists_th_notMem GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 X₁.ρ
    ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime 𝔪.yK⟩ 0
  refine h (RingHom.mem_ker.2 ?_)
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (0 + c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1] at e
  rw [𝔪.yK_eq] at h0 ⊢
  exact e.trans ((congrArg (_ * ·) h0).trans (mul_zero _))

end GlobalTheory.GSep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep

open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

theorem torusChar_eq_weil_gen : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) := by
  intro I X₁ z₁ act
  refine ⟨1, ?_⟩
  intro V _ _ _ ev X _ t δ 𝔪 τ χ hχ hpt a mu hY
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hK : KerPowSt := hL.1.kerPow
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p, x, hpy, hpg, hpx, hxo⟩ := hpt (torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ))
    ((isTor_iff _ _).2 (isTorusPtF_torusPt χ))
  obtain ⟨p', x', hp'y, hp'x, hx'o⟩ := hY
  obtain ⟨p₁, hext, -⟩ := existsUnique_qkExt hB (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) hf p
  set χ₁ : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ :=
    (Units.map (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).toMonoidHom).comp χ with hχ₁
  have hp₁g : p₁.g = torusPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (Additive.ofMul χ₁) := by
    rw [(eq_gtExt_iff _ hf _ _).2 hext.2, hpg]
    exact gtExt_torusPt _ hf χ
  have hp₁y : p₁.y = 0 := hext.1.trans hpy
  have hτ₁ : IsTor χ₁ p₁.g := by rw [hp₁g]; exact (isTor_iff _ _).2 (isTorusPtF_torusPt χ₁)
  have W₁ := weilQkIs_tor hG p₁ p' hp₁y hτ₁
  have hx₁ := (qkToAkU_iff_of_algebra hG hK 𝔪.U hk hext x).1 hpx
  have W₂ := (GlobalTheory.UT.weilQkIs_iff_weilIs hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk p₁ p' _ x' hx₁ hp'x (χ₁ (Multiplicative.ofAdd p'.y))).1 W₁
  have := X₁.ρ.P.isAb.comm
  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := (spMap_comp _ _).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := hy
  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
    X₁.S.prim.pow (pow_pos hk 2) (pow_two _)
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit (by omega)).unit
  have w := GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h
    (X₁.ρ.weil τ a (c₀ ^ (eStd X₁.S.g _ τ a).val) (by rw [pow_mul, map_pow]; rfl))
  have W₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩
    (TFK (R := V) (AlgebraicClosure (FractionRing V))) _
    (fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x) x' (h ≫ X₁.ρ.pt τ) (h ≫ X₁.ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB W₂ W₃)
    rw [hp'y] at e
    have e' := congrArg Units.val e
    simp only [hχ₁, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.coe_comp, Function.comp_apply, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec] at e'
    rw [Units.val_one, one_smul]
    refine (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective ?_
    have hc : (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) ^ (eStd X₁.S.g _ τ a).val =
        algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ a).val)) := by
      simp only [pow_mul, map_pow]
    rw [e']
    exact congrArg (fun z => algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK z)) hc
  · show h.left ≫ (X₁.ρ.pt τ).left = _
    rw [Over.comp_left, Category.assoc, hxo]
    rfl
  · show h.left ≫ (X₁.ρ.pt a).left = _
    rw [hx'o, hh]

end GlobalTheory.GSep
end
end
