module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle633
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

section SlopeTestRemainingChoices

variable {S T : Scheme.{0}} (f : T ⟶ S)

theorem pullback_prod_hom_ext {X Y : Over S} {W : Over T}
    {u v : W ⟶ (Over.pullback f).obj (X ⊗ Y)}
    (h₁ : u ≫ (Over.pullback f).map (fst X Y) = v ≫ (Over.pullback f).map (fst X Y))
    (h₂ : u ≫ (Over.pullback f).map (snd X Y) = v ≫ (Over.pullback f).map (snd X Y)) : u = v :=
  BinaryFan.IsLimit.hom_ext ((isLimitMapConeBinaryFanEquiv (Over.pullback f) _ _)
    (isLimitOfPreserves (Over.pullback f) (tensorProductIsBinaryProduct X Y))) h₁ h₂

theorem pullback_map_one {X G : Over S} [MonObj G] :
    (Over.pullback f).map (1 : X ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, Functor.map_comp]
  change _ = toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map η[G]
  rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (Functor.OplaxMonoidal.η (Over.pullback f))]
  exact toUnit_unique _ _

end SlopeTestRemainingChoices

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

section Torus

variable {S : Scheme.{0}} {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂]

theorem torusHomOf_iff_appTop' (h : X₂ → X₁) (t : splitTorus S X₁ ⟶ splitTorus S X₂) : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X₂ χ).val = (charUnit S X₁ (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X₂ χ)) : Γ((splitTorus S X₁).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X₂ χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem torusHomOf_unique {h : X₂ → X₁} {t t' : splitTorus S X₁ ⟶ splitTorus S X₂}
    (ht : TorusHomOf h t) (ht' : TorusHomOf h t') : t = t' := by
  refine (GlobalTheory.splitTorusPointsEquiv S X₂ _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop' _ _).1 ht,
    (torusHomOf_iff_appTop' _ _).1 ht']

theorem eq_one_of_torusHomOf_zero {t : splitTorus S X₁ ⟶ splitTorus S X₂}
    (ht : TorusHomOf (fun _ => (0 : X₁)) t) : t = 1 := by
  refine (GlobalTheory.splitTorusPointsEquiv S X₂ _).injective ?_
  rw [map_one]
  refine MonoidHom.ext fun χ => Units.ext ?_
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  have k : ∀ χ : X₂, (GlobalTheory.splitTorusPointsEquiv S X₂ _ t (Multiplicative.ofAdd χ)).val =
      (charUnit S X₁ 0).val := fun χ => by
    rw [GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop' _ _).1 ht]
  rw [k χ, ← k 0, ofAdd_zero, map_one]
  rfl

theorem torusHomOf_torusMap (q : X₂ →+ X₁) : TorusHomOf q (GlobalTheory.SplitTorusPow.torusMap S q) :=
  (torusHomOf_iff_appTop' _ _).2 fun χ => GlobalTheory.SplitTorusPow.torusMap_char q χ

end Torus

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem IsProdUnif.linHom_inl : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → LinHom U₁ U i₁ q₁ (lift (𝟙 G₁) 1) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₁ hi₁ hi₂
  have h1 : IsMonHom (1 : G₁ ⟶ G₂) := inferInstanceAs (IsMonHom (toUnit G₁ ≫ η[G₂]))
  have hi₂' : i₁ ≫ p₂ = 1 := hi₂.trans Hom.one_def.symm
  have hlim := hD.lim
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  ·
    have := (U₂.gt e).q_hom
    rw [← cancel_mono ((Over.pullback (thick R I e)).map (lift p₁ p₂))]
    refine pullback_prod_hom_ext _ ?_ ?_
    · simp only [Category.assoc, ← Functor.map_comp, lift_fst]
      rw [hU.q_pr₁ e, ← Category.assoc, ← Functor.map_comp, lift_fst, hi₁, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · simp only [Category.assoc, ← Functor.map_comp, lift_snd]
      rw [hU.q_pr₂ e, ← Category.assoc, ← Functor.map_comp, lift_snd, hi₂', pullback_map_one,
        pullback_map_one, MonObj.one_comp, MonObj.comp_one]
  ·
    have := (U₂.gt e).i_hom
    let E := Equiv.ofBijective _ hD.xsum
    let j₁ : D₁.toPre.X → D.toPre.X := fun y => E.symm (y, 0)
    let j₂ : D₂.toPre.X → D.toPre.X := fun y => E.symm (0, y)
    have hj₁ : ∀ y, q₁ (j₁ y) = y ∧ q₂ (j₁ y) = 0 := fun y => by
      have := E.apply_symm_apply (y, 0)
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    have hj₂ : ∀ y, q₁ (j₂ y) = 0 ∧ q₂ (j₂ y) = y := fun y => by
      have := E.apply_symm_apply (0, y)
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    obtain ⟨t₁, ht₁, hf⟩ := hU.i_pr₁ e j₁ (fun y => (hj₁ y).1) (fun y => (hj₁ y).2)
    obtain ⟨t₂, ht₂, hs⟩ := hU.i_pr₂ e j₂ (fun y => (hj₂ y).1) (fun y => (hj₂ y).2)
    let t := GlobalTheory.SplitTorusPow.torusMap (Sp (R ⧸ I ^ (e + 1))) q₁
    have ht : TorusHomOf q₁ t := torusHomOf_torusMap q₁
    have e₁ : t ≫ t₁ = 𝟙 _ := by
      have k := ht.comp ht₁
      simp only [fun y => (hj₁ y).1] at k
      exact torusHomOf_unique k (TorusHomOf.id _)
    have e₂ : t ≫ t₂ = 1 := by
      have k := ht.comp ht₂
      simp only [fun y => (hj₂ y).1] at k
      exact eq_one_of_torusHomOf_zero k
    refine ⟨t, ht, pullback_prod_hom_ext _ ?_ ?_⟩
    · rw [Category.assoc, Category.assoc, ← Functor.map_comp, lift_fst, CategoryTheory.Functor.map_id, hf,
        ← Category.assoc, e₁, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ← Functor.map_comp, lift_snd, hs, ← Category.assoc, e₂,
        pullback_map_one, MonObj.one_comp, MonObj.comp_one]

end GlobalTheory.MumProd
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.carried_section_of_frame_carried_along_lifts : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X) (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)), φ ≫ f = f → (∀ f' : (pullback f (spMap ρ₁)) ⟶ (pullback f (spMap ρ₁)), f' ≫ (pullback.fst f (spMap ρ₁)) = (pullback.fst f (spMap ρ₁)) ≫ φ → f' ≫ (pullback.snd f (spMap ρ₁)) = (pullback.snd f (spMap ρ₁)) → FrameCarriedAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ φ w f') → ∀ l, SecCarriedOver L O (s l) φ w := by
  first | exact @GlobalTheory.Mum.secCarriedOver_of_frameCarriedAlong | exact GlobalTheory.Mum.secCarriedOver_of_frameCarriedAlong | (intros; apply GlobalTheory.Mum.secCarriedOver_of_frameCarriedAlong <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.AbDual

noncomputable section

namespace GlobalTheory.RigTorsTriv

theorem triv_of_geometricFibres : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over S) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit ((k : Γ(S, ⊤))) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (M.pull (pullback.fst A.hom y)).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
  intro S A _ _ hA M hM hrig k hk hpow hfib
  have key : ∀ {Y : Scheme.{0}} (f : Y ⟶ A.left), (∃ t : (M.pull f).Gen, t.IsGen) ↔ pull f (cls M hM) = 0 :=
    fun f => (cls_eq_zero_iff (pull_isLB hM f)).symm.trans (by rw [cls_pull hM f])
  have hsurj : ∀ V : S.Opens, Function.Surjective (A.hom ∣_ V).appTop.hom := fun V => by
    have hG : Out.GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
    have h1 := hG _ _ (Out.TLinPf.isAb_pullback V.ι A hA)
    let e := IsPullback.isoIsPullback _ _ (isPullback_morphismRestrict A.hom V)
      (IsPullback.of_hasPullback A.hom V.ι).flip
    have he : e.hom ≫ pullback.snd A.hom V.ι = A.hom ∣_ V := IsPullback.isoIsPullback_hom_fst _ _ _ _
    have hi : Function.Surjective e.hom.appTop.hom := by
      have : IsIso (e.hom.app ⊤) := inferInstance
      exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
    rw [← he, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    exact hi.comp h1.2
  have hc0 : pull (1 : 𝟙_ (Over S) ⟶ A).left (cls M hM) = 0 := (key _).1 hrig
  have hkM : k • cls M hM = 0 := by
    have h := (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).2 hpow
    rw [cls_linComb hM] at h
    simpa [pull_id] using h
  refine GlobalTheory.CubeGlue.triv_of_locally_triv hM A.hom (1 : 𝟙_ (Over S) ⟶ A).left
    (by simpa using Over.w (1 : 𝟙_ (Over S) ⟶ A)) hsurj hrig ?_
  intro s
  obtain ⟨R, j, hj, ⟨p, hp⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial
  let j' : Sp R ⟶ S := j
  haveI : IsOpenImmersion j' := hj
  let A' := (Over.pullback j').obj A
  have hA' : IsAbelianScheme A' := Out.TLinPf.isAb_pullback j' A hA
  let φ := pullback.fst A.hom j'
  have hM' : (M.pull φ).IsLB := pull_isLB hM φ
  have key' : ∀ {Y : Scheme.{0}} (f : Y ⟶ A'.left),
      (∃ t : ((M.pull φ).pull f).Gen, t.IsGen) ↔ pull (f ≫ φ) (cls M hM) = 0 := fun f =>
    (cls_eq_zero_iff (pull_isLB hM' f)).symm.trans (by rw [cls_pull hM' f, cls_pull hM φ, pull_comp])
  have hone : (1 : 𝟙_ (Over (Sp R)) ⟶ A').left ≫ φ = j' ≫ (1 : 𝟙_ (Over S) ⟶ A).left := by
    rw [Hom.one_def, Hom.one_def]
    simp [φ]
  have hrig' := (key' _).2 (by rw [hone, pull_comp, hc0, map_zero])
  have hk' : IsUnit (k : R) := by
    have h := hk.map ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp j'.appTop.hom)
    simpa using h
  have hpow' : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (M.pull φ) k).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM' _ _)).1 ?_
    rw [cls_linComb hM']
    simp [pull_id, cls_pull hM φ, ← map_nsmul, hkM]
  let P : PrimeSpectrum R := p
  haveI : P.asIdeal.IsPrime := P.isPrime
  let F := AlgebraicClosure P.asIdeal.ResidueField
  let ψ : R →+* F := (algebraMap P.asIdeal.ResidueField F).comp (algebraMap R P.asIdeal.ResidueField)
  have hfib' : ∃ t : ((M.pull φ).pull (pullback.fst A'.hom (spMap ψ))).Gen, t.IsGen := by
    rw [key']
    have h0 := (key _).1 (hfib F (spMap ψ ≫ j'))
    have e : pullback.fst A'.hom (spMap ψ) ≫ φ =
        pullback.lift (pullback.fst A'.hom (spMap ψ) ≫ φ) (pullback.snd A'.hom (spMap ψ))
          (by
            have hc : pullback.fst A'.hom (spMap ψ) ≫ A'.hom = pullback.snd A'.hom (spMap ψ) ≫ spMap ψ :=
              pullback.condition
            rw [Category.assoc, pullback.condition, ← Category.assoc]
            exact (congrArg (· ≫ j') hc).trans (Category.assoc _ _ _))
          ≫ pullback.fst A.hom (spMap ψ ≫ j') := (pullback.lift_fst _ _ _).symm
    rw [e, pull_comp, h0, map_zero]
  obtain ⟨r, hr, ht⟩ := GlobalTheory.T.localTriviality_of_noetherian_descent (GlobalTheory.T.torsionLineBundle_trivial_basicOpen_of_trivial_fibre GlobalTheory.T.exists_generator_torsion_bundle_abelianScheme_sqZero) R A' hA' (M.pull φ) hM' hrig' k hk' hpow' F ψ hfib'
  have hrp : P ∈ PrimeSpectrum.basicOpen r := by
    intro hm
    apply hr
    show algebraMap _ F (algebraMap R P.asIdeal.ResidueField r) = 0
    rw [(Ideal.algebraMap_residueField_eq_zero).2 hm, map_zero]
  refine ⟨j' ''ᵁ PrimeSpectrum.basicOpen r, ⟨p, hrp, hp⟩, ?_⟩
  refine (key _).2 ?_
  let D : (Sp R).Opens := PrimeSpectrum.basicOpen r
  let W := A.hom ⁻¹ᵁ (j' ''ᵁ D)
  have h1 : Set.range (W.ι ≫ A.hom) ⊆ Set.range j' := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨q, -, hq⟩ := y.2
    exact ⟨q, hq⟩
  let m : W.toScheme ⟶ A'.left :=
    pullback.lift W.ι (IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1) (IsOpenImmersion.lift_fac _ _ _).symm
  have h2 : Set.range m ⊆ Set.range (A'.hom ⁻¹ᵁ D).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have e : m ≫ A'.hom = IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1 := pullback.lift_snd _ _ _
    show (m ≫ A'.hom) y ∈ D
    rw [e]
    obtain ⟨q, hqD, hq⟩ := y.2
    have : IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1 y = q := j'.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]; exact hq.symm)
    rw [this]; exact hqD
  have hfac : W.ι = IsOpenImmersion.lift (A'.hom ⁻¹ᵁ D).ι m h2 ≫ (A'.hom ⁻¹ᵁ D).ι ≫ φ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (pullback.lift_fst _ _ _).symm
  rw [hfac, pull_comp, (key' _).1 ht, map_zero]

end GlobalTheory.RigTorsTriv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.OfLift

theorem exists_objMap_comp {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
    {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

def ObjMap.forget {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N' : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N' s'} {o : Obj b N' s} {f : S' ⟶ S}
    (m : ObjMap o' o f) (N : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) : ObjMap (o'.forget N hd hc) (o.forget N hd hc) f :=
  ⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, fun y => m.eta _⟩

theorem ofLift : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), 3 ≤ N → ∀ (hd : N ∣ N') (hc : N'.Coprime p) (M : Model b N) (M' : Model b N') (π : M'.X ⟶ M.X), π ≫ M.s = M'.s → ∀ (om : ObjMap (M'.univ.forget N hd hc) M.univ π) (T : Over M.X) (lv : D.La → (T ⟶ M.univ.A)), IsLift M.univ N' T lv → ∃ g : T.left ⟶ M'.X, g ≫ π = T.hom ∧ ∀ a, (lv a).left = g ≫ (M'.univ.eta a).left ≫ om.φ := by
  intro p _ D R _ b N N' hN hd hc M M' π hπ om T lv hlv
  obtain ⟨o'', mm, hmm⟩ := GlobalTheory.T.exists_harrisTaylorObject_of_levelLift p D R b N N' hd hc M.X M.s M.univ T lv hlv
  obtain ⟨g, ⟨hg, ⟨m''⟩⟩, -⟩ := M'.rep T.left (T.hom ≫ M.s) o''
  obtain ⟨c, hcφ⟩ := exists_objMap_comp (ObjMap.forget m'' N hd hc) om
  have hNp : N.Coprime p := Nat.Coprime.coprime_dvd_left hd hc
  have hgπ : g ≫ π = T.hom := by
    obtain ⟨f, -, hu⟩ := M.rep T.left (T.hom ≫ M.s) (o''.forget N hd hc)
    have e1 := hu (g ≫ π) ⟨by rw [Category.assoc, hπ, hg], ⟨c⟩⟩
    have e2 := hu T.hom ⟨rfl, ⟨mm⟩⟩
    exact e1.trans e2.symm
  have hφ : c.φ = mm.φ := GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp M.X T.left M.s (T.hom ≫ M.s) M.univ (o''.forget N hd hc) _ _ c mm hgπ
  refine ⟨g, hgπ, fun a => ?_⟩
  rw [← hmm a, ← hφ, hcφ]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ om.φ) (m''.eta a)).trans (Category.assoc _ _ _))

end GlobalTheory.UPel.HT.OfLift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum



theorem GlobalTheory.Mum.FibreGerm.secGerm_eq_secRatio_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (ψ : Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0) ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ _ ψ) → ∀ (k N : ℕ) (α : Fin N → D.toPre.X) (b : ∀ j, D.toPre.SecB k (α j)) (τ : Fin N → SecK D.toPre.P.L Y.q.left k) (F : Fin N → IntFam (maximalIdeal R) D.toPre k) (s : Fin N → H0 U.LG.L k), (∀ j, IsTermOf Y (b j) (τ j)) → (∀ j, (F j).Lead (α j) (b j)) → (∀ j, U.ExpandsAt 0 k (s j) (F j).f) → ∀ (z : (thickObj R (maximalIdeal R) 0 G).left) (j : Fin N) (i : Fin 1 → U.LG.L.ι), ψ.left z ∈ nonzeroLocus (τ j) → (fstG (maximalIdeal R) 0 G).left z ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s l) i = gs (Y := (thickObj R (maximalIdeal R) 0 G).left) ψ.left z (nonzeroLocus (τ j)) (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s j) i := by
  intro R _ _ _ D A G _ _ U Y ψ hP k N α b τ F s hT hL hE z j i hτz hi
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusCoord.exists_good' U.LG.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.TorusCoord.exists_good' D.toPre.P.isLB z
  obtain ⟨c, hc⟩ := GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term R D A G U Y _ (𝟙 _) ψ hP k z J J' hJ hJ'
  have hv : ∀ l, secGerm (fstG (maximalIdeal R) 0 G).left z (s l)
      (fun _ => J ((fstG (maximalIdeal R) 0 G).left ≫ 𝟙 _)) = c.val * sval (τ l) ψ.left z J' := by
    intro l
    have := hc (α l) (b l) (τ l) (F l) (s l) (hT l) (hL l) (hE l)
    rw [Category.id_comp] at this
    exact this
  obtain ⟨a, ha⟩ := exists_unit_secGerm k (fstG (maximalIdeal R) 0 G).left z hi
    (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (fstG (maximalIdeal R) 0 G).left)
  let jt : Fin 1 → D.toPre.P.L.ι := fun _ => J' (ψ.left ≫ Y.q.left)
  have hzt : ψ.left z ∈ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt :=
    hJ'.mem (fun _ : Fin 1 => Y.q.left) ψ.left
  have hzW : ψ.left z ∈ nonzeroLocus (τ j) ⊓ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt := ⟨hτz, hzt⟩
  have hk : nonzeroLocus (τ j) ⊓ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt ≤
      (LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ))).U jt := inf_le_right
  have ha' : nonzeroLocus (τ j) ⊓ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt ≤ nonzeroLocus (τ j) :=
    inf_le_left
  have hu : ∀ l, sval (τ l) ψ.left z J' =
      gs ψ.left z (nonzeroLocus (τ j)) (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) * sval (τ j) ψ.left z J' := by
    intro l
    have e := congrArg (gs ψ.left z _) (GlobalTheory.ProjSpace.secRatio_on (τ j) (τ l) jt ha' hk)
    rw [sval_of (τ l) ψ.left z J' jt (fun _ => rfl), sval_of (τ j) ψ.left z J' jt (fun _ => rfl)]
    exact ((gs_res _ _ hk hzW _).symm.trans e).trans ((gs_mul _ _ _ hzW _ _).trans
      (congrArg₂ (· * ·) (gs_res _ _ ha' hzW _) (gs_res _ _ hk hzW _)))
  have hunit : IsUnit (sval (τ j) ψ.left z J') := by
    obtain ⟨w, hw⟩ := GlobalTheory.ProjSpace.isUnit_resG_sec (τ j) jt ha' hk
    rw [sval_of (τ j) ψ.left z J' jt (fun _ => rfl)]
    have e : gs ψ.left z _ ((τ j).f jt) = (gm ψ.left z _ w).val :=
      (gs_res _ _ hk hzW _).symm.trans ((congrArg (gs ψ.left z _) hw.symm).trans (gs_unit _ _ _ hzW w))
    exact e ▸ Units.isUnit _
  refine ⟨?_, fun l => ?_⟩
  · rw [ha, hv j]
    exact a.isUnit.mul (c.isUnit.mul hunit)
  · rw [ha, ha, hv, hv, hu l]
    ring
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_veryAmple_fourth_power_uniformised_group : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), ∃ (m : ℕ) (σ : Fin (m + 1) → H0 U.LG.L 4), VeryAmpleAlong ((Over.pullback (jK R)).obj G).hom (pullback.fst G.hom (jK R)) U.LG.L σ := by
  first | exact @GlobalTheory.Mum.exists_veryAmpleAlong_unif | exact GlobalTheory.Mum.exists_veryAmpleAlong_unif | (intros; apply GlobalTheory.Mum.exists_veryAmpleAlong_unif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.actsOnThickenings_of_pullback_uniformisation : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (I : Ideal R) (I' : Ideal V) (D : DegData R I) (D' : DegData V I') (hD : IsPullDeg θ D.toPre D'.toPre) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf θ)).obj G) (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif θ hD bc U U' → ∀ (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g : G ⟶ G) (b' : D'.toPre.P.A ⟶ D'.toPre.P.A) (h' : D'.toPre.X → D'.toPre.X) (g' : G' ⟶ G'), IsMonHom b' → ActsAs U.toUnifPre b h g → g' ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf θ)).map g → b' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map b → (∀ y, hD.xe (h' y) = h (hD.xe y)) → ActsAs U'.toUnifPre b' h' g' := by
  first | exact @GlobalTheory.Mum.actsAs_of_isPullUnif | exact GlobalTheory.Mum.actsAs_of_isPullUnif | (intros; apply GlobalTheory.Mum.actsAs_of_isPullUnif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum


theorem _root_.GlobalTheory.T.exists_descended_generator_thickened_abelian_part : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ (v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε)), v.IsGen → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y y' : T ⟶ thickObj R I e G₁, x ≫ (U₁.gt e).q = x' ≫ (U₁.gt e).q → y ≫ (U₁.gt e).q = y' ≫ (U₁.gt e).q → val v (lift x y).left z J = val v (lift x' y').left z J) → ∃ t : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k) mε), t.IsGen := by
  first | exact @GlobalTheory.HomMum.exists_gen_thick_two | exact GlobalTheory.HomMum.exists_gen_thick_two | (intros; apply GlobalTheory.HomMum.exists_gen_thick_two <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum


theorem _root_.GlobalTheory.T.exists_generator_multiplicative_on_quotient_kernel : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ (W : LB.Iso ((join U₁.LG.L U₂.LG.L).pull (coprod.map (fstG I e G₁).left (fstG I e G₂).left)) ((JN D₁.toPre D₂.toPre).pull (coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))), W.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₁.gt e).pG.left (r z) ∈ D₁.toPre.P.L.U j.1 → (fstG I e G₁).left (r z) ∈ U₁.LG.L.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw (U₁.w e) r z j.1 (fun _ => k.1)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U j.2 → (fstG I e G₂).left (r z) ∈ U₂.LG.L.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw (U₂.w e) r z j.2 (fun _ => k.2)) → ∀ (u : LB.Gen (LB.LinComb (join U₁.LG.L U₂.LG.L) (mφ G₁ G₂ f g) mε)), u.IsGen → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ G₁.left ⨿ G₂.left) → (join U₁.LG.L U₂.LG.L).ι), Good (join U₁.LG.L U₂.LG.L) z J → ∀ x x' y : T ⟶ G₁, val u (lift (x * x') y).left z J * cubV U₁.cubG z (rl J) x x' y = cubV U₂.cubG z (rr J) (x ≫ f) (x' ≫ f) (y ≫ g) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV U₁.cubG z (rl J) y x x' = cubV U₂.cubG z (rr J) (y ≫ f) (x ≫ g) (x' ≫ g) * (val u (lift y x).left z J * val u (lift y x').left z J)) → ∃ v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε), v.IsGen ∧ (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y : T ⟶ thickObj R I e G₁, (Over.map (thick R I e)).map x ≫ (U₁.gt e).pG = 1 → val v (lift (x * x') y).left z J = val v (lift x y).left z J * val v (lift x' y).left z J ∧ val v (lift y (x * x')).left z J = val v (lift y x).left z J * val v (lift y x').left z J) := by
  first | exact @GlobalTheory.HomMum.exists_gen_mul_level | exact GlobalTheory.HomMum.exists_gen_mul_level | (intros; apply GlobalTheory.HomMum.exists_gen_mul_level <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum


theorem _root_.GlobalTheory.T.generator_torus_invariant_of_multiplicative : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ [ConnectedSpace (thickObj R I e G₁).left] (v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε)), v.IsGen → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y : T ⟶ thickObj R I e G₁, (Over.map (thick R I e)).map x ≫ (U₁.gt e).pG = 1 → val v (lift (x * x') y).left z J = val v (lift x y).left z J * val v (lift x' y).left z J ∧ val v (lift y (x * x')).left z J = val v (lift y x).left z J * val v (lift y x').left z J) → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y y' : T ⟶ thickObj R I e G₁, x ≫ (U₁.gt e).q = x' ≫ (U₁.gt e).q → y ≫ (U₁.gt e).q = y' ≫ (U₁.gt e).q → val v (lift x y).left z J = val v (lift x' y').left z J) := by
  first | exact @GlobalTheory.HomMum.gen_invariant_of_mul | exact GlobalTheory.HomMum.gen_invariant_of_mul | (intros; apply GlobalTheory.HomMum.gen_invariant_of_mul <;> assumption)
end
