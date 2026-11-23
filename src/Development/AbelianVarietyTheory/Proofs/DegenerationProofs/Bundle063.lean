module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle053
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallPowDvdGerm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.ZH.FrameNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc TopologicalSpace

section Points
variable {K C : Type} [Field K] [Field C] [IsAlgClosed C] {Y : Scheme.{0}} {q : Y ⟶ Sp K} [LocallyOfFiniteType q]
  {σ : K →+* C}


variable (q σ) in
theorem exists_point_mem {Z : Set Y} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Sp C ⟶ Y, x ≫ q = spMap σ ∧ ∀ w, x w ∈ Z := by
  have hs : Surjective (spMap σ) := ⟨fun y ↦ by
    obtain ⟨z⟩ : Nonempty ↥(Sp C) := inferInstance
    exact ⟨z, Subsingleton.elim _ _⟩⟩
  have hJ : JacobsonSpace ↥(pullback q (spMap σ)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd q (spMap σ))
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z₀, rfl⟩ := (pullback.fst q (spMap σ)).surjective y
  obtain ⟨z, hzZ, hz⟩ := nonempty_inter_closedPoints (Z := pullback.fst q (spMap σ) ⁻¹' Z) ⟨z₀, hy⟩
    (hZ.preimage (pullback.fst q (spMap σ)).continuous)
  replace hz : IsClosed {z} := hz
  refine ⟨pointOfClosedPoint (pullback.snd q (spMap σ)) z hz ≫ pullback.fst _ _,
    by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc], fun w => ?_⟩
  rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  exact hzZ

theorem eq_of_val_eq [IsReduced Y] {W : Y.Opens} {r s : Γ(Y, W)}
    (h : ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → valR x W r = valR x W s) : r = s := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  obtain ⟨x, hx, hm⟩ := exists_point_mem q σ (Y.basicOpen (r - s)).isOpen.isLocallyClosed ⟨y, hy⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ W := fun w _ => Y.basicOpen_le _ (hm w)
  have := ((isUnit_valR_iff x W hW (r - s)).2 fun w _ => hm w).ne_zero
  rw [valR_eq x W hW, map_sub, ← valR_eq, ← valR_eq, h x hx hW, sub_self] at this
  exact (this rfl).elim

theorem isUnit_of_val_ne_zero {W : Y.Opens} {r : Γ(Y, W)}
    (h : ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → valR x W r ≠ 0) : IsUnit r := by
  refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun y hy => (Scheme.mem_basicOpen _ _ y hy).1 ?_
  by_contra hn
  obtain ⟨x, hx, hm⟩ := exists_point_mem q σ
    (W.isOpen.isLocallyClosed.inter (Y.basicOpen r).isOpen.isClosed_compl.isLocallyClosed) ⟨y, hy, hn⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ W := fun w _ => (hm w).1
  obtain ⟨w⟩ : Nonempty ↥(Sp C) := inferInstance
  exact (hm w).2 ((isUnit_valR_iff x W hW r).1 (h x hx hW).isUnit (show w ∈ (⊤ : (Sp C).Opens) from trivial))

theorem exists_glue [IsReduced Y] {I : Type} (W : Y.Opens) (T : I → Y.Opens) (F : I → (Sp C ⟶ Y) → C)
    (hT : ∀ z, ∃ m, z ∈ T m) (hF : ∀ m, Reg q σ (W ⊓ T m) (F m))
    (h : ∀ m m' x, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ⊤ ≤ x ⁻¹ᵁ T m → ⊤ ≤ x ⁻¹ᵁ T m' → F m x = F m' x) :
    ∃ r : Γ(Y, W), ∀ m x, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ⊤ ≤ x ⁻¹ᵁ T m → F m x = valR x W r := by
  choose u hu using hF
  obtain ⟨r, hr, -⟩ := Y.sheaf.existsUnique_gluing' (fun m => W ⊓ T m) W (fun _ => homOfLE inf_le_left)
    (fun y hy => Opens.mem_iSup.2 ((hT y).imp fun _ hm => ⟨hy, hm⟩)) u
    (fun m m' => eq_of_val_eq (q := q) (σ := σ) (W := W ⊓ T m ⊓ (W ⊓ T m')) fun x hx hW =>
      (valR_res x inf_le_left hW _).trans ((hu m x hx fun _ hz => (hW hz).1).symm.trans
        ((h m m' x hx (fun _ hz => (hW hz).1.1) (fun _ hz => (hW hz).1.2) fun _ hz => (hW hz).2.2).trans
          ((hu m' x hx fun _ hz => (hW hz).2).trans (valR_res x inf_le_right hW _).symm))))
  refine ⟨r, fun m x hx hW hm => ?_⟩
  have hh : ⊤ ≤ x ⁻¹ᵁ (W ⊓ T m) := fun _ hz => ⟨hW hz, hm hz⟩
  rw [hu m x hx hh, ← hr m]
  exact valR_res x inf_le_left hh r

end Points


open GlobalTheory.PrimeSection in
theorem exists_zpow_mul_isUnit_of_mem {X : Scheme.{0}} {t : Γ(X, ⊤)} {ξ : X}
    (hη : ∀ x : X, x ∉ X.basicOpen t ↔ ξ ⤳ x)
    (hp : ∀ U : X.Opens, IsAffineOpen U → ξ ∈ U → Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
    [IsIntegral X] [IsLocallyNoetherian X] {A : Type} {U : A → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
    {a₀ : A} (h₀ : ξ ∈ U a₀) (hg : ∀ a b, IsUnit (g a b)) (τ : Γ(X, X.basicOpen t)ˣ)
    (hτ : (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t)
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hru : ∀ a, IsUnit (r a)) :
    ∃ n : ℤ, ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a := by
  obtain ⟨hdvr, hirr⟩ := isDiscreteValuationRing_stalk hη hp
  have hD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hx₀ : X.presheaf.germ _ _ (genericPoint_mem_inf hp h₀) (r a₀) ≠ 0 := ((hru a₀).map _).ne_zero
  have hτn : ∀ n : ℤ, X.presheaf.germ _ _ hD (↑(τ ^ n) : Γ(X, X.basicOpen t)) =
      algebraMap _ X.functionField (X.presheaf.germ ⊤ ξ trivial t) ^ n := fun n ↦ by
    rw [algebraMap_germ, ← germ_res (le_top : X.basicOpen t ≤ ⊤) hD, ← hτ]
    let φ : Γ(X, X.basicOpen t) →+* X.functionField := (X.presheaf.germ _ _ hD).hom
    change φ _ = φ _ ^ n
    rw [← MonoidHom.coe_coe, ← Units.coe_map, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  obtain ⟨n, ⟨u, hu, hn⟩, -⟩ :=
    GlobalTheory.PrimeElement.existsUnique_zpow_mul_eq_unit (K := X.functionField) hirr hx₀
  have : ∀ a, ∃ s : Γ(X, U a), X.presheaf.map (homOfLE inf_le_left).op s =
      X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a :=
    fun a ↦ exists_res_eq hη hp _ fun h ↦
      ⟨X.presheaf.germ (U a ⊓ U a₀) ξ ⟨h, h₀⟩ (g a a₀) * u, by
        rw [map_mul, map_mul, hn, germ_res, hτn, algebraMap_germ,
          germ_eq_mul_germ hr (a := a) _ (genericPoint_mem_inf hp h₀)]
        ring⟩
  choose s hs using this
  have hs₀ : ξ ∈ X.basicOpen (s a₀) := by
    rw [X.mem_basicOpen _ ξ h₀]
    convert hu
    apply IsFractionRing.injective _ X.functionField
    have := congrArg (X.presheaf.germ _ _ (genericPoint_mem_inf hp h₀)) (hs a₀)
    rw [map_mul, germ_res, germ_res, hτn] at this
    rw [algebraMap_germ, hn, this]
  refine ⟨n, s, fun b ↦ isUnit_of_isUnit_res hη hp ?_ fun h ↦
    mem_basicOpen_of_compatible hg (compatible_of_res_eq hD hr _ hs) h hs₀, hs⟩
  rw [hs b]
  exact ((Units.isUnit _).map _).mul (hru b)


open GlobalTheory.DvrModel GlobalTheory.PrimeSection in
theorem norm_const : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (A I : Type) (U : A → H.Opens) (T : I → HK.Opens) (F : A → I → (Sp (PadicAlgCl p) ⟶ HK) → PadicAlgCl p), (∀ z, ∃ m, z ∈ T m) → (∀ a m, Reg q σ (j ⁻¹ᵁ U a ⊓ T m) (F a m)) → (∀ a m x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → F a m x ≠ 0) → (∀ a m m' x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → ⊤ ≤ x ⁻¹ᵁ T m' → F a m x = F a m' x) → (∀ a a', ∃ g : Γ(H, U a ⊓ U a')ˣ, ∀ m x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a' → ⊤ ≤ x ⁻¹ᵁ T m → F a m x = valR (x ≫ j) (U a ⊓ U a') g.val * F a' m x) → ∃ κ : ℝ, 0 < κ ∧ ∀ a m (c : Sp (OO p) ⟶ H) x, c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → ‖F a m x‖ = κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hsm hgi hK A I U T F hT hreg hne h₁ h₂
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hK
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hs
  have := isOpenImmersion_generic hK
  have := GlobalTheory.DvrModel.isIntegral hK
  have := GlobalTheory.DvrModel.isLocallyNoetherian f
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hK inferInstance
  have hη := notMem_basicOpen_iff_specializes hϖ hs
  by_cases hA : ∃ a₀, pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))) (genericPoint _) ∈ U a₀
  swap
  · refine ⟨1, one_pos, fun a m c x hc _ _ ha _ => (hA ⟨a, mem_of_notMem_basicOpen hη
      (ha (show IsLocalRing.closedPoint (OO p) ∈ (⊤ : (Sp (OO p)).Opens) from trivial)) ?_⟩).elim⟩
    rw [notMem_basicOpen_iff f hϖ, ← Scheme.Hom.comp_apply, hc]
    exact IsLocalRing.comap_closedPoint jV
  obtain ⟨a₀, h₀⟩ := hA
  choose r hr using fun a => exists_glue (j ⁻¹ᵁ U a) T (F a) hT (hreg a) (h₁ a)
  choose g hg using h₂
  have hpt : ∀ x : Sp (PadicAlgCl p) ⟶ HK, ∃ m, ⊤ ≤ x ⁻¹ᵁ T m := fun x =>
    (hT _).imp fun m hm => (top_le_iff x _).2 hm
  have hru : ∀ a, IsUnit (r a) := fun a => isUnit_of_val_ne_zero (q := q) (σ := σ) fun x hx hW => by
    obtain ⟨m, hm⟩ := hpt x
    rw [← hr a m x hx hW hm]
    exact hne a m x hx hW hm
  have h0 : algebraMap V K ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hϖ.ne_zero
  let φ : K →+* Γ(HK, ⊤) := q.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨r', τ', hτ', hr', -, hu', E⟩ := exists_transport (opensRange_generic hϖ hK)
    (g := fun a b => (g a b).val) (fun a => rfl) r
    (fun a b => eq_of_val_eq (q := q) (σ := σ) fun x hx hW => by
      obtain ⟨m, hm⟩ := hpt x
      have ha : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U a := fun _ hz => (hW hz).1
      have hb : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U b := fun _ hz => (hW hz).2
      refine (valR_res x inf_le_left hW _).trans (((hr a m x hx ha hm).symm.trans (hg a b m x hx ha hb hm)).trans
        (Eq.symm ((valR_mul x _ hW _ _).trans (congrArg₂ (· * ·) (GlobalTheory.Points.valR_appLE x j _ hW _) ?_))))
      exact (valR_res x inf_le_right hW _).trans (hr b m x hx hb hm).symm)
    (Units.map φ.toMonoidHom (Units.mk0 _ h0)) (appTop_cst hK.w ϖ).symm
  obtain ⟨n, s, hsu, hs'⟩ := exists_zpow_mul_isUnit_of_mem hη (prime_res_generic hϖ hs) h₀
    (fun a b => (g a b).isUnit) τ' hτ' hr' fun a => hu' a (hru a)
  have hpos : 0 < ‖σ (algebraMap V K ϖ)‖ ^ n := zpow_pos (norm_pos_iff.2 ((map_ne_zero σ).2 h0)) n
  refine ⟨(‖σ (algebraMap V K ϖ)‖ ^ n)⁻¹, inv_pos.2 hpos, fun a m c x hc hx hq ha hm => ?_⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U a := by
    show ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a
    rw [hx]
    exact fun _ _ => ha trivial
  have e := congrArg (valR x _) ((E n a (s a)).1 (hs' a))
  have e₁ : valR x ⊤ (Units.map φ.toMonoidHom (Units.mk0 _ h0)).val = σ (algebraMap V K ϖ) :=
    (GlobalTheory.Points.valR_comp x q ⊤ _).symm.trans (by
      rw [hq]
      exact GlobalTheory.Points.valR_specMap (CommRingCat.ofHom σ) _)
  have e₂ : ((valR c (U a) (s a) : OO p) : PadicAlgCl p) = σ (algebraMap V K ϖ) ^ n * F a m x := by
    rw [hr a m x hq hW hm, ← e₁, ← val_zpow x (U := ⊤) (fun _ _ => trivial)]
    refine Eq.trans ?_ ((e.trans (valR_mul x _ hW _ _)).trans (congrArg (· * _) (valR_res x le_top hW _)))
    refine Eq.trans ?_ (GlobalTheory.Points.valR_appLE x j _ hW _).symm
    rw [hx]
    exact ((valR_spMap (OO p).subtype c _ ha).2 _).symm
  have e₃ : ‖((valR c (U a) (s a) : OO p) : PadicAlgCl p)‖ = 1 := by
    have hu : IsUnit (valR c (U a) (s a)) := by
      rw [valR_eq c _ ha]
      exact (hsu a).map _
    obtain ⟨d, hd⟩ := hu.exists_right_inv
    have e' := congrArg (fun z : OO p => ‖(z : PadicAlgCl p)‖) hd
    simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at e'
    exact le_antisymm ((mem_OO_iff _).1 (Subtype.prop _))
      (e'.ge.trans (mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 d.2)))
  rw [e₂, norm_mul, norm_zpow] at e₃
  exact eq_inv_of_mul_eq_one_right e₃

end GlobalTheory.ZH.FrameNorm
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_specialFibre_projection_abelianPart : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (g : GtCoord (IsLocalRing.maximalIdeal V) D 0 G) (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∃ π : (Over.mk (spMap f) ⟶ G) →* (Over.mk (spMap f) ⟶ D.P.A), (∀ x, ∃ y : Sp κ ⟶ (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left, y ≫ (fstG (IsLocalRing.maximalIdeal V) 0 G).left = x.left ∧ y ≫ g.pG.left = (π x).left) ∧ ∀ n : ℕ, 1 ≤ n → ∀ b, b ^ n = 1 → ∃ x, x ^ n = 1 ∧ π x = b := by
  first | exact @GlobalTheory.SpecialPoints.exists_projection | exact GlobalTheory.SpecialPoints.exists_projection | (intros; apply GlobalTheory.SpecialPoints.exists_projection <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private theorem surjective_flat_quasiCompact_spMap {k K : Type} [Field k] [Field K] (σ : k →+* K) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show Surjective (Spec.map (CommRingCat.ofHom σ))
    constructor
    intro x
    obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
    exact ⟨y, Subsingleton.elim _ _⟩
  · show Flat (Spec.map (CommRingCat.ofHom σ))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := σ.toAlgebra
    show Module.Flat k K
    infer_instance
  · show QuasiCompact (Spec.map (CommRingCat.ofHom σ))
    infer_instance


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.hom_descends_to_subfield_containing_finset :
    ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (X Y : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (X₀ Y₀ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) (φ : X.left ⟶ X₀.left) (ψ : Y.left ⟶ Y₀.left), IsPullback φ X.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) → IsPullback ψ Y.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) → QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFiniteType Y.hom → ∀ f : X ⟶ Y, ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (X₁ Y₁ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k₁)) (φ₁ : X.left ⟶ X₁.left) (χ : X₁.left ⟶ X₀.left) (ψ₁ : Y.left ⟶ Y₁.left) (ω : Y₁.left ⟶ Y₀.left), IsPullback χ X₁.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap α) → IsPullback ω Y₁.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap α) → φ₁ ≫ χ = φ → ψ₁ ≫ ω = ψ → φ₁ ≫ X₁.hom = X.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β → ψ₁ ≫ Y₁.hom = Y.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β → ∃ f₁ : X₁ ⟶ Y₁, φ₁ ≫ f₁.left = f.left ≫ ψ₁ := by
  intro k K _ _ σ X Y X₀ Y₀ φ ψ hX hY hqc hqs hft f
  letI : Algebra k K := σ.toAlgebra
  have hσ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) :=
    surjective_flat_quasiCompact_spMap σ
  haveI := _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc
  haveI := _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc
  haveI : QuasiCompact X₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hX.flip hσ hqc
  haveI : QuasiSeparated X₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hX.flip hσ hqs
  haveI : LocallyOfFiniteType Y₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hY.flip hσ hft
  haveI : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := by
    show IsLocallyNoetherian (Spec (CommRingCat.of k)); infer_instance
  haveI : LocallyOfFinitePresentation Y₀.hom :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have hX' : IsPullback φ X.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k K)) := hX
  have hΦ : (hX'.isoPullback.inv ≫ f.left ≫ ψ) ≫ Y₀.hom =
      pullback.fst X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k K)) ≫ X₀.hom := by
    simp only [Category.assoc, hY.w, Over.w_assoc]
    rw [hX'.isoPullback_inv_snd_assoc]
    exact pullback.condition.symm
  obtain ⟨R, Ψ, hRfg, hΨ, hRΨ⟩ :=
    _root_.GlobalTheory.Spread.exists_fg_comp_eq X₀.hom Y₀.hom (hX'.isoPullback.inv ≫ f.left ≫ ψ) hΦ
  obtain ⟨s, hs⟩ := hRfg
  refine ⟨s, ?_⟩
  intro k₁ _ α β hβα hsβ X₁ Y₁ φ₁ χ ψ₁ ω hX₁ hY₁ hφ₁ hψ₁ hφ₁s hψ₁s
  letI : Algebra k k₁ := α.toAlgebra
  have hβα' : ∀ r : k, β (α r) = σ r := fun r => by rw [← hβα]; rfl
  let β' : k₁ →ₐ[k] K := { β with commutes' := fun r => hβα' r }
  have hβinj : Function.Injective β' := β.injective
  have hle : R ≤ β'.range := by
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hsβ hx
    exact ⟨y, rfl⟩
  let g : R →ₐ[k] k₁ :=
    (AlgEquiv.ofInjective β' hβinj).symm.toAlgHom.comp (Subalgebra.inclusion hle)
  have hg : ∀ x : R, β' (g x) = R.val x := fun x =>
    congrArg Subtype.val ((AlgEquiv.ofInjective β' hβinj).apply_symm_apply (Subalgebra.inclusion hle x))
  have hX₁' : IsPullback χ X₁.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁)) := hX₁
  have hY₁' : IsPullback ω Y₁.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁)) := hY₁
  have hm : (hX₁'.isoPullback.hom ≫ _root_.GlobalTheory.Spread.bcMap X₀.hom g ≫ Ψ) ≫ Y₀.hom =
      X₁.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁) := by
    simp only [Category.assoc, hΨ, _root_.GlobalTheory.Spread.bcMap_fst_assoc,
      hX₁'.isoPullback_hom_fst_assoc]
    exact hX₁'.w
  have key : φ₁ ≫ hX₁'.isoPullback.hom =
      hX'.isoPullback.hom ≫ _root_.GlobalTheory.Spread.bcMap X₀.hom β' := by
    apply pullback.hom_ext
    · rw [Category.assoc, hX₁'.isoPullback_hom_fst, hφ₁, Category.assoc,
        _root_.GlobalTheory.Spread.bcMap_fst, hX'.isoPullback_hom_fst]
    · rw [Category.assoc, hX₁'.isoPullback_hom_snd, hφ₁s, Category.assoc,
        _root_.GlobalTheory.Spread.bcMap_snd, hX'.isoPullback_hom_snd_assoc]
  refine ⟨Over.homMk (hY₁'.lift _ X₁.hom hm) (hY₁'.lift_snd _ _ _), ?_⟩
  show φ₁ ≫ hY₁'.lift _ X₁.hom hm = f.left ≫ ψ₁
  apply hY₁'.hom_ext
  · rw [Category.assoc, hY₁'.lift_fst, Category.assoc, hψ₁, reassoc_of% key,
      _root_.GlobalTheory.Spread.bcMap_comp_of_eq_assoc X₀.hom g β' R.val hg, hRΨ,
      Iso.hom_inv_id_assoc]
  · rw [Category.assoc, hY₁'.lift_snd, hφ₁s, Category.assoc, hψ₁s, Over.w_assoc]

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ExtensionRigidity

theorem hom_ext_of_rationalPoints {K : Type} [Field K] [IsAlgClosed K] {X Y : Over (Sp K)}
    [Smooth X.hom] [IsProper Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp K)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have := isNormalScheme_of_smooth (S := Spec (.of K)) X.hom
  have : IsReduced X.left := IsNormalScheme.isReduced
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := K) Y.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_) (by rw [Over.w, Over.w]))
  let p : 𝟙_ (Over (Sp K)) ⟶ X :=
    Over.homMk (pointOfClosedPoint (K := K) X.hom x hx) (pointOfClosedPoint_comp (K := K) X.hom x hx)
  have h1 : pointOfClosedPoint (K := K) X.hom x hx ≫ f.left =
      pointOfClosedPoint (K := K) X.hom x hx ≫ g.left := congrArg CommaMorphism.left (h p)
  have h2 : f.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) =
      g.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint K)) h1
  have h3 := pointOfClosedPoint_apply (K := K) X.hom x hx (IsLocalRing.closedPoint K)
  exact (congrArg f.left h3).symm.trans (h2.trans (congrArg g.left h3))

theorem exists_factor {S : Scheme.{0}} {X Y Z : Over S} (p : X ⟶ Y) [Flat p.left]
    [Surjective p.left] [QuasiCompact p.left] (f : X ⟶ Z)
    (h : ∀ (W : Over S) (a b : W ⟶ X), a ≫ p = b ≫ p → a ≫ f = b ≫ f) :
    ∃ β : Y ⟶ Z, p ≫ β = f := by
  have hc : ∀ {W : Scheme.{0}} (g g' : W ⟶ X.left), g ≫ p.left = g' ≫ p.left →
      g ≫ f.left = g' ≫ f.left := by
    intro W g g' hg
    have hw : g' ≫ X.hom = g ≫ X.hom := by
      rw [← Over.w p, ← Category.assoc, ← hg, Category.assoc]
    have := h (Over.mk (g ≫ X.hom)) (Over.homMk g rfl) (Over.homMk g' hw)
      (Over.OverMorphism.ext hg)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac p.left f.left hc
  exact ⟨Over.homMk (EffectiveEpi.desc p.left f.left hc) (by
    rw [← cancel_epi p.left, ← Category.assoc, hfac, Over.w, Over.w]),
    Over.OverMorphism.ext hfac⟩

theorem isMonHom_of_pointed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : G ⟶ B, η[G] ≫ f = η[B] → IsMonHom f := by
  intro K _ _ E G _ hG B _ hB f hf
  have := (UnitRigidity.smooth_geometricallyConnected_of_isGt E G hG).1
  obtain ⟨D⟩ := hG
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have := hB.proper
  obtain ⟨-, -, -, -, h1, -⟩ := (splitTorus_properties (Sp K)).1 E.X
  have : Smooth (splitTorus (Sp K) E.X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ E.X) _
  have : Smooth (splitTorus (Sp K) E.X ⊗ G).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Sp K) E.X).hom G.hom ≫
      (splitTorus (Sp K) E.X).hom))
  have hact : ((fst (splitTorus (Sp K) E.X) G ≫ D.i) * snd _ G) ≫ f = snd _ G ≫ f := by
    refine hom_ext_of_rationalPoints _ _ fun x => ?_
    obtain ⟨b, hb⟩ := GlobalTheory.T.splitTorus_to_abelianVariety_const K E.X B hB ((D.i * (toUnit _ ≫ x ≫ snd _ G)) ≫ f)
    have e : ∀ t : 𝟙_ (Over (Sp K)) ⟶ splitTorus (Sp K) E.X,
        ((t ≫ D.i) * (x ≫ snd _ G)) ≫ f = b := by
      intro t
      have := congrArg (t ≫ ·) hb
      simp only [← Category.assoc, MonObj.comp_mul] at this
      rw [toUnit_unique (t ≫ toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at this
      exact this
    have e1 := e 1
    rw [MonObj.one_comp, _root_.one_mul] at e1
    rw [← Category.assoc, MonObj.comp_mul, ← Category.assoc, e, ← Category.assoc, e1]
  obtain ⟨β, hβ⟩ := exists_factor D.q f fun W a c h => by
    have H := UnitRigidity.isPullback_act D.i D.q D.isKernel
    rw [← H.lift_fst a c h, Category.assoc, hact, ← Category.assoc, H.lift_snd]
  have : IsMonHom β := rigidity_holds _ _ _ E.isAbelian hB β (by
    rw [← IsMonHom.one_hom D.q, Category.assoc, hβ, hf])
  rw [← hβ]
  infer_instance

end GlobalTheory.ExtensionRigidity
end
