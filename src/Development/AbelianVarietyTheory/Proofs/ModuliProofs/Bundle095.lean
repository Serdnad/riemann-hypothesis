module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle026
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle089
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerCommutesWithEndomorphism
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

noncomputable section

namespace GlobalTheory.SquareGenerated

section
variable {X Y : Scheme.{0}} {H : LB X}

theorem unitAt_of_mem (s : LB.Sec H) (φ : Y ⟶ X) (y : Y) (hy : φ y ∈ Out.nonzeroLocus s) :
    UnitAt H (K := Fin 1) (fun _ => φ) (fun _ => 1) y := by
  have v : ∀ (j : Fin 1 → H.ι) (z : Y), z ∈ LB.wchart H (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z (LB.wchart H (fun _ : Fin 1 => φ) j)
        ((Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) j 0)).op).hom
          ((φ.app _).hom (s.f (j 0)))) = gs (𝟙 Y ≫ φ) z (H.U (j 0)) (s.f (j 0)) := fun j z hz =>
    (gs_res _ z _ hz _).trans (gs_pull _ φ z _ (LB.wchart_le H (fun _ : Fin 1 => φ) j 0 hz) _)
  let s' : LB.Sec (LB.LinComb H (K := Fin 1) (fun _ => φ) (fun _ => 1)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) j 0)).op).hom
          ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            (congrArg Units.val (gm_linComb H _ _ (𝟙 Y) z j j' hz.1 hz.2)))
              ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        have hm : (𝟙 Y ≫ φ) z ∈ H.U (j 0) ⊓ H.U (j' 0) :=
          ⟨LB.wchart_le H (fun _ : Fin 1 => φ) j 0 hz.1, LB.wchart_le H (fun _ : Fin 1 => φ) j' 0 hz.2⟩
        refine (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res _ z _ hm _))))
        rw [gs_unit _ z _ hm, Fin.prod_univ_one, zpow_one] }
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨s', fun J hJ => isUnit_sval s' (𝟙 Y) y hJ (fun _ => k) ?_⟩
  have hm : y ∈ LB.wchart H (fun _ : Fin 1 => φ) (fun _ => k) :=
    Set.mem_iInter.2 fun _ => X.basicOpen_le _ hk
  show y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) (fun _ => k) 0)).op).hom
          ((φ.app _).hom (s.f k)))
  have e := Y.basicOpen_res ((φ.app _).hom (s.f k))
    (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) (fun _ => k) 0)).op
  refine e ▸ ⟨hm, ?_⟩
  exact (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f k)) y).1 hk

theorem exists_sec_pw (hH : H.IsLB) (t : ℤ) (y : X)
    (h : UnitAt H (K := Fin 1) (fun _ => 𝟙 X) (fun _ => t) y) :
    ∃ u : LB.Sec (pw H t), y ∈ Out.nonzeroLocus u := by
  obtain ⟨s, hs⟩ := h
  have le : ∀ i : H.ι, H.U i ≤ LB.wchart H (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
    fun i z hz => Set.mem_iInter.2 fun _ => hz
  let u : LB.Sec (pw H t) :=
    { f := fun i => (X.presheaf.map (homOfLE (le i)).op).hom (s.f fun _ => i)
      compat := fun i j => fn_ext fun z hz => by
        refine ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (le i) hz.1 _)).trans
          (Eq.trans ?_ ((gs_mul (𝟙 X) z _ hz _ _).trans
          (congrArg₂ (· * ·) (gs_unit (𝟙 X) z _ hz _)
              ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (le j) hz.2 _)))).symm)
        refine (sec_trans s (𝟙 X) z (le i hz.1) (le j hz.2)).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
        exact (Fin.prod_univ_one _).trans (map_zpow _ _ _).symm }
  choose I hI using fun χ : X ⟶ X => exists_chart hH (χ y)
  have hm : y ∈ H.U (I (𝟙 X ≫ 𝟙 X)) := hI (𝟙 X ≫ 𝟙 X)
  refine ⟨u, TopologicalSpace.Opens.mem_iSup.2 ⟨I (𝟙 X ≫ 𝟙 X), (X.mem_basicOpen _ _ hm).2 ?_⟩⟩
  exact (congrArg IsUnit ((gs_eq (𝟙 X) y _ hm _).symm.trans (gs_res (𝟙 X) y (le _) hm _))).mpr (hs I hI)

end

theorem exists_sec_sq {O : Type} [CommRing O] [IsLocalRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A]
    {H : LB A.left} (hH : H.IsLB) (hT : Triv (Theta A H)) (s : LB.Sec H) (a : 𝟙_ (Over (Sp O)) ⟶ A)
    (y : A.left) (h₁ : ((toUnit A ≫ a) * 𝟙 A).left y ∈ Out.nonzeroLocus s)
    (h₂ : ((toUnit A ≫ a⁻¹) * 𝟙 A).left y ∈ Out.nonzeroLocus s) :
    ∃ u : LB.Sec (pw H 2), y ∈ Out.nonzeroLocus u := by
  obtain ⟨t, ht⟩ := hT
  let χ : Fin 4 → (Sp O ⟶ A.left) := ![(a * a⁻¹).left, a.left, (a⁻¹).left, (1 : 𝟙_ (Over (Sp O)) ⟶ A).left]
  choose i hi using fun k => exists_chart hH (χ k (IsLocalRing.closedPoint O))
  have e : ∀ k, (![((toUnit A ≫ a) * (toUnit A ≫ a⁻¹)).left, (toUnit A ≫ a).left,
      (toUnit A ≫ a⁻¹).left, (1 : A ⟶ A).left] k) = (toUnit A).left ≫ χ k := by
    intro k
    fin_cases k
    · show _ = (toUnit A ≫ (a * a⁻¹)).left
      rw [MonObj.comp_mul]; rfl
    · rfl
    · rfl
    · show _ = (toUnit A ≫ (1 : 𝟙_ (Over (Sp O)) ⟶ A)).left
      rw [MonObj.comp_one]; rfl
  obtain ⟨u, hu⟩ := GlobalTheory.AbSquare.exists_gen_square hH t ht (toUnit A ≫ a) (toUnit A ≫ a⁻¹) (𝟙 A) i
    (fun k z => by
      rw [e k]
      have h : χ k ⁻¹ᵁ H.U (i k) = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 (hi k)
      show (toUnit A).left z ∈ χ k ⁻¹ᵁ H.U (i k)
      rw [h]; trivial)
  have hu' : UnitAt H _ _ y := ⟨genSec u hu, fun J hJ => by
    rw [sval_genSec u hu _ y hJ]; exact Units.isUnit _⟩
  have e1 : (toUnit A ≫ a) * (toUnit A ≫ a⁻¹) * 𝟙 A = 𝟙 A := by
    rw [← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one, _root_.one_mul]
  refine exists_sec_pw hH 2 y (UnitAt.congr hH (formEq_of_add fun U _ hh => ?_)
    (((unitAt_of_mem s _ y h₁).mul (unitAt_of_mem s _ y h₂)).mul hu'))
  simp only [Fintype.sum_sum_type, Fin.sum_univ_succ, e1, Sum.elim_inl, Sum.elim_inr]
  simp
  module

theorem exists_secs_sq_generate : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ H : LB A.left, H.IsLB → Triv (Theta A H) → ∀ s : LB.Sec H, (∃ x ∈ Out.nonzeroLocus s, A.hom x = IsLocalRing.closedPoint O) → ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw H 2)), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  intro O K _ _ _ _ _ _ _ A _ _ hA H hH hT s hs
  obtain ⟨-, hk, hlift⟩ := GlobalTheory.T.valuationRing_henselian_and_smooth_points_lift O K
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  let t : Sp (IsLocalRing.ResidueField O) ⟶ Sp O := spMap (IsLocalRing.residue O)
  let T : Over (Sp O) := Over.mk t
  have : IsIntegral (T ⊗ A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t A.hom).flip
  let p : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint (IsLocalRing.ResidueField O)
  have htp : t p = IsLocalRing.closedPoint O := IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  have up : ∀ x : A.left, A.hom x = IsLocalRing.closedPoint O → ∃ z : (T ⊗ A).left, (snd T A).left z = x := by
    intro x hx
    have : x ∈ Set.range (pullback.snd t A.hom) := by
      rw [Scheme.Pullback.range_snd]
      exact ⟨p, htp.trans hx.symm⟩
    exact this
  let W : A.left.Opens := ⨆ u : LB.Sec (pw H 2), Out.nonzeroLocus u
  have hW : W = ⊤ := by
    by_contra hne
    have hZ : ((W : Set A.left)ᶜ).Nonempty := by
      rw [Set.nonempty_compl]
      exact fun h => hne (SetLike.coe_injective h)
    have hc : IsClosed (A.hom '' (W : Set A.left)ᶜ) := A.hom.isClosedMap _ W.isOpen.isClosed_compl
    obtain ⟨x₀, hx₀, hx₁⟩ : IsLocalRing.closedPoint O ∈ A.hom '' (W : Set A.left)ᶜ := by
      obtain ⟨q, hq⟩ := hZ.image A.hom
      exact (IsLocalRing.specializes_closedPoint q).mem_closed hc hq
    obtain ⟨z₀, hz₀⟩ := up x₀ hx₁
    have : LocallyOfFiniteType (X := (T ⊗ A).left) (Y := Sp (IsLocalRing.ResidueField O)) (fst T A).left :=
      inferInstanceAs (LocallyOfFiniteType (pullback.fst t A.hom))
    have : JacobsonSpace (T ⊗ A).left :=
      LocallyOfFiniteType.jacobsonSpace (X := (T ⊗ A).left) (Y := Sp (IsLocalRing.ResidueField O)) (fst T A).left
    obtain ⟨c, hcZ, hcc⟩ := nonempty_inter_closedPoints
      (Z := (((snd T A).left ⁻¹ᵁ W : (T ⊗ A).left.Opens) : Set (T ⊗ A).left)ᶜ)
      ⟨z₀, by
        show ¬ (snd T A).left z₀ ∈ W
        rw [hz₀]; exact hx₀⟩ ((snd T A).left ⁻¹ᵁ W).isOpen.isClosed_compl.isLocallyClosed
    let σ := pointOfClosedPoint (X := (T ⊗ A).left) (K := IsLocalRing.ResidueField O) (fst T A).left c hcc
    have hσ : σ ≫ (fst T A).left = 𝟙 _ := pointOfClosedPoint_comp _ c hcc
    have hσp : σ p = c := pointOfClosedPoint_apply _ c hcc p
    let σ' : T ⟶ T ⊗ A := Over.homMk σ (by
      rw [← Over.w (fst T A), ← Category.assoc]
      exact (congrArg (· ≫ T.hom) hσ).trans (Category.id_comp _))
    let x : T ⟶ A := σ' ≫ snd T A
    have hx : x.left p ∉ W := by
      show (snd T A).left (σ p) ∉ W
      rw [hσp]; exact hcZ
    obtain ⟨y₀, hy₀, hy₁⟩ := hs
    obtain ⟨z₁, hz₁⟩ := up y₀ hy₁
    obtain ⟨a, h₁, h₂⟩ := GlobalTheory.NoBasePoint.exists_two_points t ((snd T A).left ⁻¹ᵁ Out.nonzeroLocus s)
      ⟨z₁, by
        show (snd T A).left z₁ ∈ Out.nonzeroLocus s
        rw [hz₁]; exact hy₀⟩ x x
    obtain ⟨b, hb, hba⟩ := hlift A.left A.hom inferInstance a.left (Over.w a)
    let b' : 𝟙_ (Over (Sp O)) ⟶ A := Over.homMk b hb
    have hb' : toUnit T ≫ b' = a := Over.OverMorphism.ext hba
    have key : ∀ (d : 𝟙_ (Over (Sp O)) ⟶ A), (Out.ptSecT A ((toUnit T ≫ d) * x)).left p ∈
        (snd T A).left ⁻¹ᵁ Out.nonzeroLocus s →
        ((toUnit A ≫ d) * 𝟙 A).left (x.left p) ∈ Out.nonzeroLocus s := by
      intro d hd
      have e : x ≫ ((toUnit A ≫ d) * 𝟙 A) = Out.ptSecT A ((toUnit T ≫ d) * x) ≫ snd T A := by
        simp [Out.ptSecT, MonObj.comp_mul]
      have e' : ((toUnit A ≫ d) * 𝟙 A).left (x.left p) =
          (snd T A).left ((Out.ptSecT A ((toUnit T ≫ d) * x)).left p) :=
        congrArg (fun q => q.left p) e
      rw [e']; exact hd
    obtain ⟨u, hu⟩ := exists_sec_sq A hH hT s b' (x.left p) (key b' (by rw [hb']; exact h₁ p))
      (key b'⁻¹ (by rw [GrpObj.comp_inv, hb']; exact h₂ p))
    exact hx (TopologicalSpace.Opens.mem_iSup.2 ⟨u, hu⟩)
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun u : LB.Sec (pw H 2) => (Out.nonzeroLocus u : Set A.left)) (fun u => (Out.nonzeroLocus u).isOpen)
    (fun y _ => by
      have : y ∈ W := by rw [hW]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 this))
  refine ⟨F.card, Fin.cons (secZero _) (fun i => (F.equivFin.symm i : LB.Sec (pw H 2))), top_unique fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(F.equivFin ⟨u, hu⟩).succ, ?_⟩
  rw [Fin.cons_succ, Equiv.symm_apply_apply]
  exact hy

end GlobalTheory.SquareGenerated
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.GlueDer

theorem rsT_eq {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : rsT s O = resG Y h s := dif_pos h

theorem res_res {Y : Scheme.{0}} {U V V' : Y.Opens} (h : V ≤ U) (h' : V' ≤ V) (s : Γ(Y, U)) :
    resG Y h' (resG Y h s) = resG Y (h'.trans h) s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_app {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ U) (f : Γ(X, U)) :
    resG Y h' ((m.app U).hom f) = (m.app V).hom (resG X h f) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, m.naturality]
  rfl

theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    resG X h (constFn p U a) = constFn p V a := by
  simp only [resG, constFn]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem app_const {R K : Type} [CommRing R] [CommRing K] {X Y : Scheme.{0}} (x₀ : R →+* K) (p : X ⟶ Sp R)
    (q : Y ⟶ Sp K) (m : Y ⟶ X) (hm : m ≫ p = q ≫ spMap x₀) (U : X.Opens) (a : R) :
    (m.app U).hom (constFn p U a) = constFn q (m ⁻¹ᵁ U) (x₀ a) := by
  have h1 : (m.app U).hom (constFn p U a) = constFn (m ≫ p) (m ⁻¹ᵁ U) a := by
    simp only [constFn]
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE m p ⊤ U (m ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl)
  rw [h1, hm]
  simp only [constFn]
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (x₀ a) =
      ((spMap x₀).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := by
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom x₀)
    exact congrArg (fun φ => φ.hom a) this
  rw [h2]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.comp_appLE q (spMap x₀) ⊤ (m ⁻¹ᵁ U) (fun _ _ => trivial))

theorem pre_mono {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ U :=
  fun _ hx => h hx

theorem pre_cover {Y X : Scheme.{0}} (m : Y ⟶ X) {I : Type} (W : I → X.Opens) (hW : ⨆ i, W i = ⊤) (O : X.Opens) :
    m ⁻¹ᵁ O ≤ ⨆ i, m ⁻¹ᵁ (O ⊓ W i) := by
  intro y hy
  have : m y ∈ ⨆ i, W i := by rw [hW]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hy, hi⟩

theorem glue {K : Type} [Field K] {R : Type} [CommRing R] {Y X : Scheme.{0}} (q : Y ⟶ Sp K) (p : X ⟶ Sp R)
    (m : Y ⟶ X) (D : R → K) {I : Type} (W : I → X.Opens) (hW : ⨆ i, W i = ⊤)
    (e : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)) (he : ∀ i, LocDerK q p m D (W i) (e i))
    (hc : ∀ i j O, O ≤ W i ⊓ W j → ∀ f, e i O f = e j O f) : ∃ d₁, LocDerK q p m D ⊤ d₁ := by
  have ex : ∀ (O : X.Opens) (f : Γ(X, O)), ∃ s : Γ(Y, m ⁻¹ᵁ O), ∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = e i (O ⊓ W i) (resG X inf_le_left f) := by
    intro O f
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (pre_cover m W hW O)
      (fun i => e i (O ⊓ W i) (resG X inf_le_left f)) (by
        intro i j
        have hi := (he i).res (O ⊓ W i) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_left inf_le_right (resG X inf_le_left f)
        have hj := (he j).res (O ⊓ W j) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_right inf_le_right (resG X inf_le_left f)
        rw [rsT_eq (pre_mono m inf_le_left), res_res] at hi
        rw [rsT_eq (pre_mono m inf_le_right), res_res] at hj
        have := hc i j ((O ⊓ W i) ⊓ (O ⊓ W j)) (inf_le_inf inf_le_right inf_le_right)
          (resG X (inf_le_left.trans inf_le_left) f)
        exact hi.symm.trans (this.trans hj))
    exact ⟨s, hs⟩
  have ext : ∀ (O : X.Opens) (s t : Γ(Y, m ⁻¹ᵁ O)), (∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) t) →
      s = t := fun O s t h =>
    Y.sheaf.eq_of_locally_eq' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (pre_cover m W hW O) s t h
  choose d₁ hd using ex
  refine ⟨d₁, ?_, ?_, ?_, ?_⟩
  · intro O _ f f'
    refine ext O _ _ fun i => ?_
    rw [map_add (f := _), hd, hd, hd, map_add (f := _), (he i).add _ inf_le_right]
  · intro O _ f f'
    refine ext O _ _ fun i => ?_
    rw [map_add (f := _), map_mul, map_mul, hd, hd, hd, map_mul, (he i).mul _ inf_le_right,
      res_app m inf_le_left, res_app m inf_le_left]
  · intro O O' h _ f
    refine ext O' _ _ fun i => ?_
    have h' : O' ⊓ W i ≤ O ⊓ W i := inf_le_inf_right _ h
    have h1 := (he i).res (O ⊓ W i) (O' ⊓ W i) h' inf_le_right (resG X inf_le_left f)
    rw [rsT_eq (pre_mono m h'), res_res, ← hd, res_res] at h1
    rw [hd, rsT_eq (pre_mono m h), res_res, res_res, h1]
  · intro O _ r
    refine ext O _ _ fun i => ?_
    rw [hd, res_const, res_const, (he i).base _ inf_le_right]

end GlobalTheory.KS.GlueDer


open GlobalTheory.KS.GlueDer in
theorem GlobalTheory.KS.exists_global_locDer_of_isCob : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ, ⨆ i, W i = ⊤ → KSCoc A₀.hom p m D W dd d θ → (∀ a, IsCob _ (θ a)) → ∃ d₁, LocDerK A₀.hom p m D ⊤ d₁ := by
  intro K _ A₀ _ g v dd _ hv hdd R _ x₀ X p m hm I W D d θ hW hc hb
  choose b hb using hb
  have H := fun a => (GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₀ (v a) (hv.1 a)).2 (dd a) (hdd a)
  refine glue A₀.hom p m D W hW
    (fun i O f => d i O f - ∑ a, rsT (b a i) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)) (fun i => ?_) ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro O hO f f'
      simp only [(hc.der i).add O hO, map_add (f := _), fun a => (H a).1, mul_add, Finset.sum_add_distrib]
      ring
    · intro O hO f f'
      simp only [(hc.der i).mul O hO, map_mul, fun a => (H a).2.1, mul_add, Finset.sum_add_distrib, mul_sub,
        Finset.mul_sum, mul_left_comm (rsT _ _)]
      ring
    · intro O O' h hO f
      have h' := pre_mono m h

      rw [(hc.der i).res O O' h hO, rsT_eq h', rsT_eq h', map_sub, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 := (H a).2.2.1 _ _ ((m.app O).hom f) h'
      rw [rsT_eq h', rsT_eq h', res_app m h] at h2
      rw [map_mul, h2, rsT_eq (pre_mono m hO), rsT_eq (pre_mono m (h.trans hO)), res_res]
    · intro O hO r
      simp only [(hc.der i).base O hO, app_const x₀ p A₀.hom m hm.w, fun a => (H a).2.2.2.1, mul_zero,
        Finset.sum_const_zero, sub_zero]
  · intro i j O hO f
    have h1 := hc.diff i j O hO f
    have hi : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W i := pre_mono m (hO.trans inf_le_left)
    have hj : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W j := pre_mono m (hO.trans inf_le_right)
    have h2 : ∀ a, rsT (θ a i j) (m ⁻¹ᵁ O) = rsT (b a j) (m ⁻¹ᵁ O) - rsT (b a i) (m ⁻¹ᵁ O) := by
      intro a
      rw [hb, rsT_eq (le_inf hi hj), map_sub, rsT_eq inf_le_right, rsT_eq inf_le_left, res_res, res_res,
        rsT_eq hi, rsT_eq hj]
    simp only [h2, sub_mul, Finset.sum_sub_distrib] at h1
    show _ - _ = _ - _
    linear_combination -h1
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.logDerivative_principalPolarisation_independent : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0 := by
  first | exact @GlobalTheory.KS.DlogPol.dlog_independent | exact GlobalTheory.KS.DlogPol.dlog_independent | (intros; apply GlobalTheory.KS.DlogPol.dlog_independent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.HkFam

theorem lbIso_pow_pull_square {B B' G G' : Scheme.{0}} {β : B' ⟶ B} {π : G' ⟶ G} {φ : B ⟶ G} {φ' : B' ⟶ G'}
    (h : φ' ≫ π = β ≫ φ) {P : LB G} {P' : LB G'} {M : LB B} {M' : LB B'} (hP : P.IsLB) (hP' : P'.IsLB)
    (hM : M.IsLB) (hM' : M'.IsLB) (eP : LBIso P' (P.pull π)) (eM : LBIso M' (M.pull β)) {n : ℕ}
    (hI : LBIso (lbPow M n) (P.pull φ)) : LBIso (lbPow M' n) (P'.pull φ') := by
  obtain ⟨w, hw⟩ := eP
  have e₁ : LBIso (P'.pull φ') (P.pull (φ' ≫ π)) :=
    iso_linComb ((isGen_iff w).1 hw) (fun _ : PUnit => φ') (fun _ => 1)
  have e₂ : LBIso (P.pull (φ' ≫ π)) ((P.pull φ).pull β) :=
    LBIso.chartPull (chartPullSame P _ _ _ β fun _ => h) (chartPullPull _ β) (lbIso_refl (pull_isLB hP φ))
  have e₃ := LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂
  refine LBIso.trans (isLB_lbPow hM' _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP' _) ?_ e₃.symm
  exact LBIso.trans (isLB_lbPow hM' _) (isLB_lbPow (pull_isLB hM _) _) (pull_isLB (pull_isLB hP _) _)
    (lbIso_lbPow eM _) (LBIso.chartPull (chartPullPowPull M β _) (chartPullPull _ β) hI)

theorem KerSet.pull {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'} [GrpObj G] [GrpObj G']
    {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} (hβ : β ≫ B.hom = B'.hom ≫ f) (hπ : IsGrpPullback G' G f π)
    {ψ : B ⟶ G} {ψ' : B' ⟶ G'} (h : ψ'.left ≫ π = β ≫ ψ.left) {K : Set B.left} (hK : KerSet ψ K) :
    KerSet ψ' (β ⁻¹' K) := by
  intro k _ _ x z
  have e : pushHom hπ (Over.mk x) (z ≫ ψ') = pushPt hβ z ≫ ψ := Over.OverMorphism.ext (by
    show (z.left ≫ ψ'.left) ≫ π = (z.left ≫ β) ≫ ψ.left
    rw [Category.assoc, Category.assoc, h])
  have e₁ : z ≫ ψ' = 1 ↔ pushPt hβ z ≫ ψ = 1 := by
    rw [← e]
    refine ⟨fun q => by rw [q, map_one], fun q => PureType.eq_of_comp_eq hπ.1 ?_⟩
    exact congrArg (fun u => u.left) (q.trans (map_one (pushHom hπ (Over.mk x))).symm)
  refine e₁.trans ((hK k (x ≫ f) (pushPt hβ z)).trans ?_)
  show Set.range (z.left ≫ β) ⊆ K ↔ _
  simp only [Set.range_subset_iff, Set.mem_preimage, Scheme.Hom.comp_apply]

theorem isog_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o₁ o₂ : Ob D l s) (o₁' o₂' : Ob D l s') (n₁ : ObjMap o₁' o₁ f) (n₂ : ObjMap o₂' o₂ f) (ψ : o₁.t.G ⟶ o₂.t.G), (∃! ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left) ∧ ∀ ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left → (IsIsog o₁ o₂ p ψ → IsIsog o₁' o₂' p ψ') ∧ ∀ K, IsMonHom ψ → KerSet ψ K → KerSet ψ' (n₁.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l p S S' s s' f o₁ o₂ o₁' o₂' n₁ n₂ ψ
  have c₁ := n₁.toSABMap.cart
  have c₂ := n₂.toSABMap.cart
  refine ⟨?_, fun ψ' h => ⟨?_, fun K _ hK => KerSet.pull c₁.1.w c₂ h hK⟩⟩
  · obtain ⟨ψ', h⟩ := PureType.exists_hom_over c₁.1.w c₂.1 ψ
    exact ⟨ψ', h, fun χ hχ => PureType.eq_of_comp_eq c₂.1 (hχ.trans h.symm)⟩
  rintro ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, h₇⟩
  have sq : IsPullback n₁.toSABMap.φ ψ'.left ψ.left n₂.toSABMap.φ :=
    IsPullback.of_bot (by rw [Over.w, Over.w]; exact c₁.1) h.symm c₂.1
  have lev : ∀ {u : 𝟙_ (Over S) ⟶ o₁.t.G} {v : 𝟙_ (Over S) ⟶ o₂.t.G} {u' : 𝟙_ (Over S') ⟶ o₁'.t.G}
      {v' : 𝟙_ (Over S') ⟶ o₂'.t.G}, u'.left ≫ n₁.toSABMap.φ = f ≫ u.left → v'.left ≫ n₂.toSABMap.φ = f ≫ v.left →
      u ≫ ψ = v → u' ≫ ψ' = v' := fun {u v u' v'} hu hv e => PureType.eq_of_comp_eq c₂.1 (by
    refine Eq.trans ?_ hv.symm
    rw [← e, Over.comp_left, Over.comp_left, Category.assoc]
    exact (congrArg (u'.left ≫ ·) h).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ψ.left) hu).trans (Category.assoc _ _ _))))
  refine ⟨⟨PureType.isMonHom_over c₁ c₂ h, MorphismProperty.of_isPullback (P := @IsFinite) sq h₂,
    MorphismProperty.of_isPullback (P := @Etale) sq h₃, MorphismProperty.of_isPullback (P := @Surjective) sq h₄,
    fun a => PureType.eq_of_comp_eq c₂.1 ?_, ?_⟩, fun p' hp a =>
    ⟨lev (n₁.eta _) (n₂.eta _) (h₇ p' hp a).1, lev (n₁.etaA _) (n₂.etaA _) (h₇ p' hp a).2⟩⟩
  · have e : (o₁.t.act.act a).left ≫ ψ.left = ψ.left ≫ (o₂.t.act.act a).left := congrArg (fun u => u.left) (h₅ a)
    have h' : ψ'.left ≫ n₂.cm.F = n₁.cm.F ≫ ψ.left := h
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, n₂.act, h', reassoc_of% h',
      reassoc_of% (n₁.act a), e]
  · exact lbIso_pow_pull_square h o₂.t.PP.isLB o₂'.t.PP.isLB o₁.t.PP.isLB o₁'.t.PP.isLB
      (n₂.lin.imp fun _ q => q.1) (n₁.lin.imp fun _ q => q.1) h₆

end GlobalTheory.HkFam

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.kodairaSpencer_commutes_with_endomorphism : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ (f : X ⟶ X) (f₀ : P₀.A ⟶ P₀.A) (F : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm Θ F := by
  first | exact @GlobalTheory.KS.Endo.comm_of_endo | exact GlobalTheory.KS.Endo.comm_of_endo | (intros; apply GlobalTheory.KS.Endo.comm_of_endo <;> assumption)
end
