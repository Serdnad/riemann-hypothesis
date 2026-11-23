module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle024
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ZJ.exists_torsion_lift_of_residue :
    ∀ (p : ℕ) [Fact p.Prime] (B : Scheme.{0}) (G : Over B) [GrpObj G], IsSemiAbelian G → ∀ (y : Sp (OO p) ⟶ B) (n : ℕ), IsUnit (n : Γ(B, ⊤)) → ∀ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ y) ⟶ G, t ^ n = 1 → ∃ b : Over.mk y ⟶ G, b ^ n = 1 ∧ spMap (IsLocalRing.residue (OO p)) ≫ b.left = t.left := by
  intro p _ B G _ hG y n hn t ht
  have := hG.comm
  have := hG.smooth
  have := GrpTangent.etale_torsion G hn
  have hP := GrpTangent.isPullback_torsion G n
  have e : ∀ {T : Scheme.{0}} (q : T ⟶ B), (1 : Over.mk q ⟶ G).left = q ≫ η[G].left := by
    intro T q
    rw [Hom.one_def, Over.comp_left]; rfl
  have w : t.left ≫ (mulN G n).left =
      (spMap (IsLocalRing.residue (OO p)) ≫ y) ≫ η[G].left := by
    rw [← Over.comp_left, GrpTangent.comp_mulN, ht, e]
  obtain ⟨c, hc₁, hc₂⟩ := ZJ.exists_classical_lift_of_smooth p _ _ (torsion G n).hom y
    (hP.lift _ _ w) (hP.lift_snd _ _ w)
  let b : Over.mk y ⟶ G := Over.homMk (c ≫ (torsion.ι G n).left) (by
    rw [Category.assoc, Over.w]; exact hc₁)
  refine ⟨b, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    rw [← GrpTangent.comp_mulN, Over.comp_left, e]
    change (c ≫ (torsion.ι G n).left) ≫ _ = _
    rw [Category.assoc, hP.w, ← Category.assoc, hc₁]
  · change _ ≫ c ≫ (torsion.ι G n).left = _
    rw [← Category.assoc]
    exact (congrArg (· ≫ (torsion.ι G n).left) hc₂).trans (hP.lift_fst _ _ w)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

def wtDefect {P G T : Scheme.{0}} (a b : P ⟶ G) (c : P ⟶ T) (V : G.Opens) (u : Γ(G, V))
    (e : Γ(T, ⊤)) : Γ(P, a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V) :=
  (a.appLE V _ inf_le_left).hom u - (c.appLE ⊤ _ le_top).hom e * (b.appLE V _ inf_le_right).hom u

theorem appLE_wtDefect {Z P G T : Scheme.{0}} (a b : P ⟶ G) (c : P ⟶ T) (V : G.Opens)
    (u : Γ(G, V)) (e : Γ(T, ⊤)) (p : Z ⟶ P) {a' b' : Z ⟶ G} {c' : Z ⟶ T} (ha : p ≫ a = a')
    (hb : p ≫ b = b') (hc : p ≫ c = c') (h : ⊤ ≤ p ⁻¹ᵁ (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V))
    (h₁ : ⊤ ≤ a' ⁻¹ᵁ V) (h₂ : ⊤ ≤ b' ⁻¹ᵁ V) :
    (p.appLE _ ⊤ h).hom (wtDefect a b c V u e) =
      (a'.appLE V ⊤ h₁).hom u - c'.appTop.hom e * (b'.appLE V ⊤ h₂).hom u := by
  subst ha hb hc
  have e₁ := congrArg (fun q => CommRingCat.Hom.hom q u)
    (Scheme.Hom.appLE_comp_appLE p a V _ ⊤ inf_le_left h)
  have e₂ := congrArg (fun q => CommRingCat.Hom.hom q u)
    (Scheme.Hom.appLE_comp_appLE p b V _ ⊤ inf_le_right h)
  have e₃ := congrArg (fun q => CommRingCat.Hom.hom q e)
    ((Scheme.Hom.appLE_comp_appLE p c ⊤ _ ⊤ le_top h).trans (Scheme.Hom.appLE_eq_app (p ≫ c)))
  rw [wtDefect, map_sub, map_mul]
  exact congrArg₂ (· - ·) e₁ (congrArg₂ (· * ·) e₃ e₂)

theorem eq_zero_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {P : Over (Sp k)}
    [Smooth P.hom] {W : P.left.Opens} (d : Γ(P.left, W))
    (h : ∀ (z : 𝟙_ (Over (Sp k)) ⟶ P) (x : (𝟙_ (Over (Sp k))).left),
      z.left x ∉ P.left.basicOpen d) : d = 0 := by
  have : IsReduced P.left := GlobalTheory.isReduced_of_smooth_of_isReduced (S := Spec (.of k)) P.hom
  have : JacobsonSpace P.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec (.of k)) P.hom
  refine eq_zero_of_basicOpen_eq_bot d ?_
  by_contra hne
  have hne' : ((P.left.basicOpen d : P.left.Opens) : Set P.left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h' => hne (TopologicalSpace.Opens.ext h')
  obtain ⟨x, hxd, hx⟩ := nonempty_inter_closedPoints hne' (P.left.basicOpen d).isOpen.isLocallyClosed
  refine h (Over.homMk (pointOfClosedPoint (K := k) P.hom x hx)
    (pointOfClosedPoint_comp (K := k) P.hom x hx)) (IsLocalRing.closedPoint k) ?_
  have e := pointOfClosedPoint_apply (K := k) P.hom x hx (IsLocalRing.closedPoint k)
  exact e.symm ▸ hxd

theorem wt_of_genericPoint :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], Smooth G.hom → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G) (F : Type) [Field F] (s : Sp F ⟶ Sp k) (g : Over.mk s ⟶ G), (∀ V : G.left.Opens, (V : Set G.left).Nonempty → ⊤ ≤ g.left ⁻¹ᵁ V) → ∀ (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X), (∀ (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) (h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V), WtRat.ev (R := F) (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left V h₁ u = WtRat.ev (R := F) (toUnit (Over.mk s) ≫ t).left ⊤ le_top (charUnit (Sp k) X χ).val * WtRat.ev (R := F) g.left V h₂ u) → Wt i V u χ := by
  intro k _ _ G _ hG X _ _ _ i F _ s g hg V u χ H
  obtain ⟨-, -, -, -, h1, -⟩ := (splitTorus_properties (Sp k)).1 X
  have : Smooth (splitTorus (Sp k) X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ X) _
  have : Smooth (splitTorus (Sp k) X ⊗ G).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Sp k) X).hom G.hom ≫
      (splitTorus (Sp k) X).hom))
  have hact : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left = ((t ≫ i) * y).left := by
    intro Z t y
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have hsnd : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ (snd (splitTorus (Sp k) X) G).left = y.left := by
    intro Z t y
    rw [← Over.comp_left, lift_snd]
  have hfst : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ (fst (splitTorus (Sp k) X) G).left = t.left := by
    intro Z t y
    rw [← Over.comp_left, lift_fst]
  have hd : wtDefect ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left (snd _ G).left
      (fst (splitTorus (Sp k) X) G).left V u (charUnit (Sp k) X χ).val = 0 := by
    refine eq_zero_of_rationalPoints _ fun z x hx => ?_
    set d := wtDefect ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left (snd _ G).left
      (fst (splitTorus (Sp k) X) G).left V u (charUnit (Sp k) X χ).val with hdd
    let t := z ≫ fst _ _
    let m : G ⟶ splitTorus (Sp k) X ⊗ G := lift (toUnit G ≫ t) (𝟙 G)
    have hz : (z ≫ snd _ _) ≫ m = z := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [m, t, Category.assoc, lift_fst]
        rw [← Category.assoc (snd _ _), ← Category.assoc z, toUnit_unique (z ≫ _) (𝟙 _),
          Category.id_comp]
      · simp [m]
    have hgm : g ≫ m = lift (toUnit (Over.mk s) ≫ t) g := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [m, Category.assoc, lift_fst]
        rw [← Category.assoc, toUnit_unique (g ≫ _) (toUnit _)]
      · simp [m]
    have h0 := hg (m.left ⁻¹ᵁ (splitTorus (Sp k) X ⊗ G).left.basicOpen d)
      ⟨(z ≫ snd _ _).left x, by
        have : m.left ((z ≫ snd _ _).left x) = z.left x := congrArg (fun q => q.left x) hz
        show m.left ((z ≫ snd _ _).left x) ∈ (splitTorus (Sp k) X ⊗ G).left.basicOpen d
        rw [this]; exact hx⟩
    have h1 : ⊤ ≤ (lift (toUnit (Over.mk s) ≫ t) g).left ⁻¹ᵁ
        (splitTorus (Sp k) X ⊗ G).left.basicOpen d := by
      rw [← hgm]; exact h0
    have h2 := h1.trans ((lift (toUnit (Over.mk s) ≫ t) g).left.preimage_mono
      ((splitTorus (Sp k) X ⊗ G).left.basicOpen_le d))
    have h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V := by
      rw [← hact]; exact fun y hy => (h2 hy).1
    have h₂ : ⊤ ≤ g.left ⁻¹ᵁ V := by
      rw [← hsnd (toUnit (Over.mk s) ≫ t)]; exact fun y hy => (h2 hy).2
    have hu := isUnit_ev (R := F) _ _ h2 d h1
    have hv := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      (appLE_wtDefect _ _ _ V u (charUnit (Sp k) X χ).val _ (hact _ _) (hsnd _ _) (hfst _ _) h2 h₁ h₂)
    have hH := (H t h₁ h₂).trans (congrArg (· * ev (R := F) g.left V h₂ u)
      (ev_top (R := F) (toUnit (Over.mk s) ≫ t).left le_top (charUnit (Sp k) X χ).val))
    refine hu.ne_zero (hv.trans ?_)
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (hH.trans (map_mul _ _ _).symm))
  intro Z t y h₁ h₂
  have h : ⊤ ≤ (lift t y).left ⁻¹ᵁ (((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left ⁻¹ᵁ V ⊓
      (snd (splitTorus (Sp k) X) G).left ⁻¹ᵁ V) := by
    rw [← hact] at h₁
    rw [← hsnd t] at h₂
    exact fun w hw => ⟨h₁ hw, h₂ hw⟩
  have hv := appLE_wtDefect _ _ _ V u (charUnit (Sp k) X χ).val _ (hact t y) (hsnd t y) (hfst t y)
    h h₁ h₂
  rw [hd, map_zero] at hv
  exact sub_eq_zero.1 hv.symm

end GlobalTheory.SS.WtRat
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LN

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

theorem psi_value_of_match (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (f : O' →+* R) (u : R) (hf : ∀ x, x ≠ 0 → IsUnit (f x)) (P : DegPre R) [Module (𝓞 E) P.X]
    (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ : P.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.X) (hW : Match a f u P oP φ he w e)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F]
    (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
        algebraMap (FractionRing R) F (algebraMap R _ (f x)))
    (z : Sp F) (y : a.D₀.X) (χ : P.X) (hχ : e y = χ) (j : P.P.L.ι)
    (hj : (P.c χ).left (cpt R) ∈ P.P.L.U j) :
    ∃ v : Rˣ,
      (gm (Out.jFK (R := R) F) z
        (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))
        ((P.psi χ).s (fun _ => j))).val =
      toStk z ((algebraMap (FractionRing R) F (algebraMap R _ u)) ^ (a.be y y / 2) *
        algebraMap (FractionRing R) F (algebraMap R _ v.val)) := by
  subst hχ
  obtain ⟨-, -, -, -, -, hG⟩ := hW
  have hG' := (genRel_iff w _ _ _ z).1 (hG F _ hF rfl y)
  obtain ⟨hp, hv⟩ := hG'
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  let x : Sp R ⟶ P.P.A.left := (P.c (e y)).left
  have hx : Out.jFK (R := R) F ≫ Out.ptK (P.c (e y)) = spMap g ≫ x := by
    have : spMap g = Out.jFK (R := R) F ≫ Out.jK R := by
      simp only [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc]
    rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart a.D₀.P.isLB (φ (x (cpt R)))
  have ht : ⊤ ≤ x ⁻¹ᵁ ((a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 hj₀, hj⟩
  have hz : (Out.jFK (R := R) F ≫ Out.ptK (P.c (e y))) z ∈
      (a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j := by
    rw [hx]
    exact ht (show spMap g z ∈ (⊤ : (Sp R).Opens) from trivial)
  have hz₀ := mem_pull.1 hz.1
  have H1 := hv (fun _ => j) (fun _ => j₀) (fun _ => hz₀) (fun _ => hz.2)
  rw [gm_pullGen', gm_pullGen', Category.id_comp, Category.id_comp, Fintype.prod_unique, zpow_neg_one,
    Units.val_mul, Units.inv_mul_eq_iff_eq_mul] at H1
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g x _ ht (w.s (fun _ => j₀, j)) z
  have hz₁ : (Out.jFK (R := O') F ≫ Out.ptK (a.D₀.c y)) z ∈ a.D₀.P.L.U j₀ := by
    rw [← hp PUnit.unit]; exact hz₀
  have ht₀ : ⊤ ≤ (𝟙 (Sp (FractionRing O'))) ⁻¹ᵁ
      (LB.wchart a.D₀.P.L (K := PUnit) (fun _ => Out.ptK (a.D₀.c y)) (fun _ => j₀)) :=
    (top_le_iff_mem _ _ (Out.jFK (R := O') F z)).2 (Set.mem_iInter.2 fun _ => hz₁)
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap (algebraMap (FractionRing O') F) (𝟙 _) _ ht₀
    ((a.D₀.psi y).s (fun _ => j₀)) z
  obtain ⟨r, s, hs, hr⟩ := IsFractionRing.div_surjective (A := O') u₀.val
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := fun h0 => u₀.ne_zero (by rw [← hr, h0, map_zero, zero_div])
  obtain ⟨r', hr'⟩ := hf r hr0
  obtain ⟨s', hs'⟩ := hf s hs0
  have hq : algebraMap (FractionRing O') F u₀.val = g (r' * s'⁻¹).val := by
    rw [← hr, map_div₀, hF, hF, ← hr', ← hs', Units.val_mul, map_mul, map_units_inv, div_eq_mul_inv]
    rfl
  rw [hq, Category.comp_id] at hu₀
  rw [← hx] at hu₁
  refine ⟨u₁ * (r' * s'⁻¹), H1.trans ?_⟩
  refine (congrArg₂ (· * ·) hu₁ (congrArg _ hu₀)).trans ?_
  simp only [Units.val_mul, map_mul]
  rw [mul_left_comm]
  rfl

theorem pow_eq_of_not_isUnit {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {u : R} (hu : ¬ IsUnit u)
    (v v' : Rˣ) (m n : ℕ) (h0 : u ^ m * v ≠ 0) (h : u ^ m * v = u ^ n * v') : m = n := by
  by_cases hz : u = 0
  · subst hz
    have h0' := h ▸ h0
    have hm : m = 0 := by
      by_contra hm; exact h0 (by rw [zero_pow hm, zero_mul])
    have hn : n = 0 := by
      by_contra hn; exact h0' (by rw [zero_pow hn, zero_mul])
    omega
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨k, t, ht⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
    have hk : k ≠ 0 := by
      rintro rfl
      exact hu (by rw [ht, pow_zero, _root_.mul_one]; exact t.isUnit)
    have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (t ^ m * v) (t ^ n * v') (k * m) (k * n) (by
      rw [ht] at h
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, pow_mul]
      linear_combination h)
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) this

theorem be_self_eq_of_match (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (f : O' →+* R) (u : R) (hf : ∀ x, x ≠ 0 → IsUnit (f x)) (hu : ¬ IsUnit u) (P : DegPre R) [Module (𝓞 E) P.X]
    (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X)
    (h₁ : Match a f u P oP φ₁ he₁ w₁ e₁) (h₂ : Match a f u P oP φ₂ he₂ w₂ e₂) (y y' : a.D₀.X) (hy : e₁ y = e₂ y') :
    a.be y y = a.be y' y' := by
  let F := AlgebraicClosure (FractionRing R)
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective _ _)
  have hfi : Function.Injective f := (injective_iff_map_eq_zero f).2 fun x hx => by
    by_contra h0
    exact (hf x h0).ne_zero hx
  have hgf : Function.Injective (g.comp f) := hg.comp hfi
  let alg : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hgf).toAlgebra
  have hF : ∀ x, @algebraMap (FractionRing O') F _ _ alg (algebraMap O' _ x) =
      algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x =>
    IsFractionRing.lift_algebraMap hgf x
  have z : Sp F := (default : PrimeSpectrum F)
  obtain ⟨j, hj⟩ := exists_chart P.P.isLB ((P.c (e₁ y)).left (cpt R))
  obtain ⟨v, hv⟩ := @psi_value_of_match E _ _ _ H D l c O _ β O' _ _ b a R _ _ _ f u hf P _ oP φ₁ he₁ w₁ e₁ h₁
    F _ _ _ alg hF z y _ rfl j hj
  obtain ⟨v', hv'⟩ := @psi_value_of_match E _ _ _ H D l c O _ β O' _ _ b a R _ _ _ f u hf P _ oP φ₂ he₂ w₂ e₂ h₂
    F _ _ _ alg hF z y' _ hy.symm j hj
  have e := (toStk z).injective (hv.symm.trans hv')
  have e0 := fun h => Units.ne_zero _ (hv.trans ((congrArg (toStk z) h).trans (map_zero _)))
  have nn : ∀ y, 0 ≤ a.be y y := fun y => by
    by_cases hy : y = 0
    · subst hy; simp
    · exact (a.be_pos y hy).le
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (nn y) (by norm_num : (0 : ℤ) ≤ 2))
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (nn y') (by norm_num : (0 : ℤ) ≤ 2))
  rw [hm, hn, zpow_natCast, zpow_natCast] at e
  rw [hm, zpow_natCast] at e0
  have e' : u ^ m * v = u ^ n * v' := by
    apply hg
    rw [map_mul, map_mul, map_pow, map_pow]
    exact e
  have e0' : u ^ m * v ≠ 0 := fun h => e0 (by
    have := congrArg g h
    rw [map_mul, map_pow, map_zero] at this
    exact this)
  have hmn : m = n := pow_eq_of_not_isUnit hu v v' m n e0' e'
  have d : (2 : ℤ) ∣ a.be y y := (Dvd.intro _ rfl).trans (a.be_dvd y y)
  have d' : (2 : ℤ) ∣ a.be y' y' := (Dvd.intro _ rfl).trans (a.be_dvd y' y')
  omega

theorem be_symm_eq_of_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : O' →+* R) (u : R), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (P : DegPre R) [Module (𝓞 E) P.X] (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left) (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A) (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X), Match a f u P oP φ₁ he₁ w₁ e₁ → Match a f u P oP φ₂ he₂ w₂ e₂ → ∀ y, a.be (e₁.symm y) (e₁.symm y) = a.be (e₂.symm y) (e₂.symm y) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ f u hf hu P _ oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂ y =>
    be_self_eq_of_match a f u hf hu P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂ _ _ (by simp)

end GlobalTheory.LN

end
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.TorsDesc

theorem s_mem_of_basis {F : Type} [CommRing F] (N : NumD F) (U : Subgroup Fˣ) (g : N.Gt) {ι : Type}
    (e : Module.Basis ι ℤ N.X) (hθ : ∀ χ χ', N.θ (N.c χ) (N.c χ') g.b ∈ U) (he : ∀ l, g.s (e l) ∈ U) (χ : N.X) :
    g.s χ ∈ U := by
  have hχ : χ ∈ Submodule.span ℤ (Set.range e) := by rw [e.span_eq]; trivial
  rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure] at hχ
  induction hχ using AddSubgroup.closure_induction with
  | mem x hx => obtain ⟨l, rfl⟩ := hx; exact he l
  | zero => rw [NumD.Gt.s_zero]; exact U.one_mem
  | add x y _ _ hx hy =>
    rw [eq_div_iff_mul_eq'.2 (g.mult x y)]
    exact U.div_mem (U.mul_mem hx hy) (hθ _ _)
  | neg x _ hx =>
    have := g.mult x (-x)
    rw [add_neg_cancel, NumD.Gt.s_zero, one_mul] at this
    exact (U.mul_mem_cancel_left hx).1 (this ▸ hθ _ _)

theorem s_mem_of_root {F : Type} [CommRing F] (N : NumD F) (U : Subgroup Fˣ)
    (hθ : ∀ x y u, N.θ x y u ∈ U) (hψ : ∀ χ, N.ψ χ ∈ U) {k : ℕ} (hU : ∀ u : Fˣ, u ^ k ∈ U → u ∈ U) (p : N.QT k)
    (χ : N.X) : p.1.2.s χ ∈ U := by
  refine hU _ ?_
  rw [← NumD.Gt.pow_s, N.mem_QT.1 p.2, NumD.io_s]
  exact U.mul_mem (U.div_mem (U.div_mem (hψ _) (hψ _)) (hψ _)) (U.prod_mem fun _ _ => hθ _ _ _)

theorem exists_finite_subalgebra (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F]
    (K : IntermediateField (FractionRing O) F) [FiniteDimensional (FractionRing O) K] :
    ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∀ x ∈ K, IsIntegral O x → x ∈ O₁ := by
  have : CharZero (FractionRing O) := IsFractionRing.charZero_of_isFractionRing O
  have : Module.Finite O (integralClosure O K) := IsIntegralClosure.finite O (FractionRing O) K _
  let v : K →ₐ[O] F := { K.val.toRingHom with commutes' := fun _ => rfl }
  have hv : Function.Injective v := Subtype.val_injective
  refine ⟨(integralClosure O K).map v, Module.Finite.equiv ((integralClosure O K).equivMapOfInjective v hv).toLinearEquiv,
    fun x hx hi => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (isIntegral_algHom_iff v hv).1 hi

theorem descend : ∀ (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (S : ValuationSubring F), (∀ x, x ∈ S ↔ IsIntegral O x) → ∀ (N : NumD F) (K₁ : IntermediateField (FractionRing O) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing O) K₁ → (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) → (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) → (∀ x ∈ A₀, N.th x ∈ K₁) → (∀ χ, (N.ψ χ : F) ∈ K₁) → (∀ x y u, S.valuation (N.θ x y u : F) = 1) → (∀ x, S.valuation (N.σ x : F) = 1) → (∀ x, N.th x ∈ S) → (∀ χ, S.valuation (N.ψ χ : F) = 1) → ∀ (Ix : Type) [Finite Ix] (k : Ix → ℕ) (p : ∀ i, N.QT (k i)), (∀ i, 0 < k i) → (∀ i, (p i).1.2.b ∈ A₀) → ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∃ (N₀ : NumD O₁) (I : NumD.Hom O₁.val.toRingHom N₀ N), I.lam = 1 ∧ ∀ i (p' : N.QT (k i)), N.QEq (p i) p' → ∃ p₀ : N₀.QT (k i), p'.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p'.1.2 := by
  intro O F _ _ _ _ _ _ _ _ _ _ S hS N K₁ A₀ hK hc hθ hσ hth hψ vθ vσ vth vψ Ix _ k p hk hp
  let e := Module.Free.chooseBasis ℤ N.X
  let T : Set F := Set.range fun il : Ix × Module.Free.ChooseBasisIndex ℤ N.X => ((p il.1).1.2.s (e il.2) : F)
  have : Finite T := (Set.finite_range _).to_subtype
  have : FiniteDimensional (FractionRing O) (IntermediateField.adjoin (FractionRing O) T) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let K₂ := K₁ ⊔ IntermediateField.adjoin (FractionRing O) T
  have : FiniteDimensional (FractionRing O) K₂ := IntermediateField.finiteDimensional_sup _ _
  have h12 : K₁ ≤ K₂ := le_sup_left
  obtain ⟨O₁, hfin, hO⟩ := exists_finite_subalgebra O F K₂
  have hunit : ∀ u : Fˣ, (u : F) ∈ K₂ → S.valuation (u : F) = 1 → ∃ a : O₁ˣ, O₁.val.toRingHom a = u := by
    intro u hu hv
    have h1 : (u : F) ∈ O₁ := hO _ hu ((hS _).1 ((S.valuation_le_one_iff _).1 hv.le))
    have h2 : ((u⁻¹ : Fˣ) : F) ∈ O₁ := by
      rw [Units.val_inv_eq_inv_val]
      exact hO _ (K₂.inv_mem hu) ((hS _).1 ((S.valuation_le_one_iff _).1 (by rw [map_inv₀, hv, inv_one])))
    exact ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, rfl⟩
  let U : Subgroup Fˣ :=
    { carrier := {u | (u : F) ∈ K₂}
      mul_mem' := fun ha hb => K₂.mul_mem ha hb
      one_mem' := K₂.one_mem
      inv_mem' := fun {u} hu => by
        change ((u⁻¹ : Fˣ) : F) ∈ K₂
        rw [Units.val_inv_eq_inv_val]
        exact K₂.inv_mem hu }
  let V : Subgroup Fˣ := (S.valuation.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom F)).ker
  obtain ⟨N₀, I, hI, h⟩ := GlobalTheory.Ex.NumD.exists_descent_subring O₁ F O₁.val.toRingHom Subtype.val_injective N A₀ hc
    (fun x hx y hy u hu => hunit _ (h12 (hθ x hx y hy u hu)) (vθ _ _ _))
    (fun x hx => hunit _ (h12 (hσ x hx)) (vσ _))
    (fun x hx => ⟨⟨_, hO _ (h12 (hth x hx)) ((hS _).1 (vth x))⟩, rfl⟩)
    (fun χ => hunit _ (h12 (hψ χ)) (vψ _))
  refine ⟨O₁, hfin, N₀, I, hI, fun i p' ⟨z, _, hz⟩ => h _ p' ?_ fun χ => hunit _ ?_ ?_⟩
  · rw [hz]
    exact A₀.mul_mem (hp i) (hc z)
  · have h1 : (p i).1.2.s χ ∈ U := s_mem_of_basis N U _ e (fun χ χ' => h12 (hθ _ (hc _) _ (hc _) _ (hp i)))
      (fun l => (le_sup_right : _ ≤ K₂) (IntermediateField.subset_adjoin _ _ ⟨(i, l), rfl⟩)) χ
    have hψU : ∀ χ, N.ψ χ ∈ U := fun χ => h12 (hψ χ)
    change p'.1.2.s χ ∈ U
    rw [hz, NumD.Gt.mul_s]
    exact U.div_mem (U.mul_mem h1 (U.div_mem (U.div_mem (hψU _) (hψU _)) (hψU _)))
      (h12 (hθ _ (hc _) _ (hp i) _ (hc z)))
  · refine s_mem_of_root N V vθ vψ (fun u hu => ?_) p' χ
    have : S.valuation (u : F) ^ k i = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val]; exact hu
    exact (pow_eq_one_iff_of_nonneg zero_le (hk i).ne').1 this

end GlobalTheory.Ex.TorsDesc
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
theorem _root_.GlobalTheory.T.twist_terms_alt : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p : N.QT (m ^ 2)) (χ : N.X), (N.twist β u).txT m (N.twQ β u hm p) χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ ∧ (∀ (j : ℕ) (hj : j ∣ k) (q : N.QT j), j ≠ 0 → (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) + β.be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j) : Oˣ) * N.evT m p q.1.2 χ) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q q' : N.QT j), (N.twist β u).wp (N.twQ β u hj q) (N.twQ β u hj q') = N.wp q q' ∧ N.twQ β u hj (q * q') = N.twQ β u hj q * N.twQ β u hj q' ∧ (N.QEq q q' ↔ (N.twist β u).QEq (N.twQ β u hj q) (N.twQ β u hj q')) := by
  first | exact @GlobalTheory.Ex.twist_terms | exact GlobalTheory.Ex.twist_terms | (intros; apply GlobalTheory.Ex.twist_terms <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.hom_transport_alt : ∀ (O O' : Type) [CommRing O] [CommRing O'] (f : O →+* O') (N : NumD O) (N' : NumD O') (I : NumD.Hom f N N'), (∀ g, ∃! g', I.Rel g g') ∧ (∀ g h g' h', I.Rel g g' → I.Rel h h' → I.Rel (g * h) (g' * h')) ∧ (∀ y, I.Rel (N.io y) (N'.io (I.e y))) ∧ (∀ k (p q : N.QT k) (p' q' : N'.QT k), p'.1.1.toAdd = I.e p.1.1.toAdd → I.Rel p.1.2 p'.1.2 → q'.1.1.toAdd = I.e q.1.1.toAdd → I.Rel q.1.2 q'.1.2 → N'.wp p' q' = Units.map f.toMonoidHom (N.wp p q)) ∧ ∀ m, Odd m → ∀ (p : N.QT (m ^ 2)) (p' : N'.QT (m ^ 2)), p'.1.1.toAdd = I.e p.1.1.toAdd → I.Rel p.1.2 p'.1.2 → ∀ χ, N'.txT m p' (I.e χ) = I.lam * f (N.txT m p χ) ∧ ∀ h h', I.Rel h h' → N'.evT m p' h' (I.e χ) = (I.lam * I.h h.b ^ (m ^ 2) : O'ˣ) * f (N.evT m p h χ) := by
  first | exact @GlobalTheory.Ex.NumD.hom_transport | exact GlobalTheory.Ex.NumD.hom_transport | (intros; apply GlobalTheory.Ex.NumD.hom_transport <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.mulq_dbl_cubN_relations : ∀ (O : Type) [CommRing O] (B : NumB O) (a b : ℕ) (x y : B.A), mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) ∧ mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y * (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) ∧ dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) = dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 ∧ mulq B.θ B.σ a x⁻¹ * B.σ x ^ (a ^ 2) = mulq B.θ B.σ a x * B.σ (x ^ a) := by
  first | exact @GlobalTheory.Ex.mulq_laws | exact GlobalTheory.Ex.mulq_laws | (intros; apply GlobalTheory.Ex.mulq_laws <;> assumption)
end
