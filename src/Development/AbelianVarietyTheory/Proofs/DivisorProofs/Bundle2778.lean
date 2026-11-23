module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle155
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle130
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle054
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle079
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLinearLiftAdditiveHolomorphicAbelian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle129
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.commutatorPairing_heckeTranslate_eq_zeta : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k M : ℕ), c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ (I : TateIsoO D κ (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))) (n : ℕ), 0 < n → n.Coprime p → ∀ (u v : D.La) (e : (Γ((Over.mk x).left, ⊤))ˣ), Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) ((n * (k ^ 2 / c) : ℕ) : ℤ) (I.ev (n * k) (g u)) (I.ev (n * k) (g v)) e → e = unitOn (I.ζ n ^ (2 * D.EF u v)) := by
  first | exact @GlobalTheory.UPel.HT.Hecke.weil_value_translate | exact GlobalTheory.UPel.HT.Hecke.weil_value_translate | (intros; apply GlobalTheory.UPel.HT.Hecke.weil_value_translate <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem mem_basicOpen_of_comp {X Y Y' : Scheme.{0}} (c : Y ⟶ Y') (f : Y' ⟶ X) {U : X.Opens} (r : Γ(X, U))
    {y : Y} (h : y ∈ Y.basicOpen ((c ≫ f).app U r)) : c y ∈ Y'.basicOpen (f.app U r) := by
  rw [← Scheme.preimage_basicOpen] at h ⊢
  exact h

theorem secCoNonzero_of_comp {X Y Y' : Scheme.{0}} (L : LB X) {k k' : ℕ} (c : Y ⟶ Y') (u v : Y' ⟶ X)
    (s : H0 L k) (t : H0 L k') (h : SecCoNonzero L (c ≫ u) (c ≫ v) s t) : SecCoNonzero L u v s t := by
  obtain ⟨y, i, i', h1, h2⟩ := h
  exact ⟨c y, i, i', mem_basicOpen_of_comp c u _ h1, mem_basicOpen_of_comp c v _ h2⟩

theorem formalEnd_secCoNonzero_lift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), FormalEnd U.toUnifPre a h' b → ∀ (k k' : ℕ) (s : H0 U.LG.L k) (t : H0 U.LG.L k'), SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s t → ∀ e : ℕ, SecCoNonzero U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s t := by
  intro R _ _ _ _ D A G _ _ _ U a h' b hb k k' s t h0 e
  induction e with
  | zero => exact h0
  | succ e ih =>
    apply secCoNonzero_of_comp U.LG.L (thickMap R (maximalIdeal R) e G)
    have hf : thickMap R (maximalIdeal R) e G ≫ (fstG (maximalIdeal R) (e + 1) G).left =
        (fstG (maximalIdeal R) e G).left := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    rw [hf, ← Category.assoc, hb.2.1 e, Category.assoc, hf]
    exact ih

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Rigid

open GlobalTheory.CechPic GlobalTheory.AmpleRigid GlobalTheory.SiegRigid

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem pull_cls_diag {b : Base D R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R}
    {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S} (m : ObjMap o' o f) :
    pull m.φ (cls _ (pull_isLB o.isLB (lift (𝟙 o.A) (𝟙 o.A)).left)) =
      cls _ (pull_isLB o'.isLB (lift (𝟙 o'.A) (𝟙 o'.A)).left) := by
  have hs := m.sq
  have e : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
    have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 o.A) (𝟙 o.A))
    have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 o.A) (𝟙 o.A))
    have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 o'.A) (𝟙 o'.A))
    have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 o'.A) (𝟙 o'.A))
    simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst o.A o.A).left = (_ ≫ _) ≫ (fst o.A o.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
    · show (_ ≫ _) ≫ (snd o.A o.A).left = (_ ≫ _) ≫ (snd o.A o.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp
  have h1 : pull m.φ₂ (cls o.P o.isLB) = cls o'.P o'.isLB :=
    ((cls_eq_iff o'.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol).symm
  rw [cls_pull o.isLB, cls_pull o'.isLB, ← pull_comp, ← e, pull_comp, h1]

theorem eq_on_torsion {b : Base D R} {N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {S S' : Scheme.{0}}
    {s : S ⟶ Sp R} (o : Obj b N s) {A' : Over S'} [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ o.A.left} (hφ : IsGrpPullback A' o.A f φ)
    (lv : D.La → (𝟙_ (Over S') ⟶ A'))
    (h₁ : ∀ a, (lv a).left ≫ φ = f ≫ (o.eta a).left) (h₂ : ∀ a, (lv a).left ≫ φ' = f ≫ (o.eta a).left)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ A') (hy : y ^ N = 1) :
    y.left ≫ φ = y.left ≫ φ' := by
  let β : R →+* k := (Spec.preimage ((x ≫ f) ≫ s)).hom
  obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (Spec.map_preimage _).symm
  have hy₁ : pushHom hφ (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := (I.onto N hN hNp _).1 hy₁
  have hu : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := (Category.comp_id _).symm.trans (Over.w (toUnit _))
  have e : (x ≫ f) ≫ (o.eta a).left = y.left ≫ φ := by
    rw [← hu]
    exact congrArg (fun q => q.left) ((hI a).trans ha)
  have e₁ : y.left = x ≫ (lv a).left := by
    apply hφ.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h₁ a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h₁ a).trans (h₂ a).symm)

theorem eq_id : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (m : ObjMap o o (𝟙 S)), m.φ = 𝟙 _ := by
  intro p _ D R _ b N hN hNp S s o m
  have hψ := m.cart
  have e₂ : m.φ ≫ o.A.hom = o.A.hom := hψ.1.w.trans (Category.comp_id _)
  haveI : IsIso m.φ := hψ.1.isIso_fst_of_isIso
  let σ : o.A ≅ o.A := Over.isoMk (asIso m.φ) e₂
  have hσ : IsMonHom σ.hom := isMonHom_of_mul_comp σ.hom fun T x y => mul_comp_of_grpPullback_id σ.hom hψ x y
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 o.A o.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S.residueField t)
    let j : Sp K ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField t) K)) ≫ S.fromSpecResidueField t
    have hp := isGrpPullback_pullback o.A j
    have := o.ab.smooth
    have := o.ab.proper
    have := o.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj o.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd o.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd o.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd o.A.hom j); infer_instance }
    have hNK : (N : K) ≠ 0 := by
      have hu := (b.unit N hNp).map (Spec.preimage (j ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have g := hp.comp m.cart
    rw [Category.comp_id] at g
    have e' := eq_of_field (pull_isLB o.isLB _) o.ample hab g hp
      (by rw [pull_comp, pull_cls_diag m]) hN hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion (φ' := 𝟙 _) (by omega) hNp o m.cart o.eta m.eta (fun a => by simp) Ω (x ≫ j) _ hy₁
        rw [← Category.assoc]
        exact e₁.trans (Category.comp_id _)
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · exact e'
  have := congrArg (fun q => q.left) key
  exact this

end GlobalTheory.UPel.HT.Rigid
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
open ReciprocityTheory.ChartRestriction.G GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.SiegLift

theorem exists_level_of_forget : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N), Odd N → 3 ≤ N → c.Principal →
    SmoothOfRelativeDimension g c.A.hom → ∃ C : SiegPre g N (b.ζ : K) (𝟙 (Sp K)), SRel C c 0 0 (𝟙 _) := by
  intro g n N B _ ζ k _ _ s c b ho hN3 hc hg
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hG := hL.globalFns
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hN : ((N : ℕ) : k) ≠ 0 := b.unit.ne_zero
  have hN₀ : N ≠ 0 := fun e => hN (by rw [e, Nat.cast_zero])
  have hz : IsPrimitiveRoot b.ζ N := IsPrimitiveRoot.coe_units_iff.1 (b.prim k (RingHom.id k))
  have hz₂ : IsPrimitiveRoot (b.ζ ^ 2) N := hz.pow_of_coprime 2 (Nat.coprime_two_left.2 ho)
  have card := GlobalTheory.card_torsion_geometricPoint_of_field GlobalTheory.card_torsion_abelianVariety _ c.A c.ab g hg

  obtain ⟨L, hLM, ⟨cu⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta hL _ c.A c.ab c.diag hD
    (DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hD _))
    (GlobalTheory.exists_gen_theta_of_isAbelianScheme k c.A c.ab _ hD)
  have toW : ∀ {m : ℕ} {T : Over (Sp k)} {x y : T ⟶ c.A} {u}, UU.CubWeil cu m x y u →
      Out.WeilIs c.A c.diag m x y u := fun H => hLM ▸ (UU.cubWeil_iff_weilIs hG c.ab H.1 H.2.1 _).1 H
  obtain ⟨f₁, f₂, f₃⟩ := (GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow k c.A c.diag c.P c.ab
    hD hc.1 c.isLB).2 N (Nat.pos_of_ne_zero hN₀)
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ c.A) := (powMonoidHom N).ker
  have hH : ∀ x : H, x.1 ^ N = 1 := fun x => x.2
  have ex : ∀ x y : H, ∃ u : kˣ, UU.CubWeil cu N x.1 y.1 (unitOn u) := fun x y => by
    obtain ⟨u, hu, -⟩ := UU.existsUnique_cubWeil cu (hH x) (hH y)
    obtain ⟨w, rfl⟩ : ∃ w : kˣ, unitOn w = u :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom u,
        Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) u.val)⟩
    exact ⟨w, hu⟩
  choose w hw using ex
  have uq : ∀ x y u, UU.CubWeil cu N x.1 y.1 (unitOn u) → w x y = u := fun x y u H =>
    SiegelOfPolarised.unitOn_inj ((hw x y).unique H)
  have l : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y => uq _ _ _ (by
    have := (hw x y).mul_left (hw x' y)
    unfold unitOn at this ⊢
    rwa [map_mul])
  have sk : ∀ x y, w y x = (w x y)⁻¹ := fun x y => uq _ _ _ (by
    have := (hw x y).symm
    unfold unitOn at this ⊢
    rwa [map_inv])
  have u1 : unitOn (1 : kˣ) = 1 := map_one _
  let e : H →* H →* kˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) fun y y' => by
    rw [sk (y * y'), l, mul_inv, ← sk, ← sk]) fun x x' => MonoidHom.ext fun y => l x x' y
  obtain ⟨l₁, add₁, w₁⟩ := exists_symplectic_hom (g := g) (Nat.pos_of_ne_zero hN₀) hz₂
    (fun x => Subtype.ext (hH x)) (fun m hm => by
      obtain ⟨r, hr⟩ := hm
      have hm : (m : k) ≠ 0 := left_ne_zero_of_mul (by rwa [hr, Nat.cast_mul] at hN)
      refine Eq.trans (Nat.card_congr ?_) (card k (𝟙 _) m hm)
      exact ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩, fun x => ⟨⟨x.1, show x.1 ^ N = 1 by
        rw [hr, pow_mul, x.2, one_pow]⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩)
    e (fun x => uq _ _ _ (u1 ▸ UU.cubWeil_self cu (hH x))) (fun x hx => Subtype.ext (by
      have t := GlobalTheory.CubNondeg.main hL _ c.A c.ab L cu k (𝟙 _) N hN f₁ f₂ f₃ x.1 (hH x) fun y hy => by
        have := hw x ⟨y, hy⟩
        rwa [show w x ⟨y, hy⟩ = 1 from hx ⟨y, hy⟩, u1] at this
      rw [hLM] at t
      have s₂ : x.1 ^ 2 = 1 := sq_eq_one_of_translDiff c hc (𝟙 _) x.1 t
      exact (pow_eq_one_iff_of_coprime (Nat.coprime_two_left.2 ho)).1 ⟨s₂, hH x⟩))
  let l₂ : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp k)) ⟶ c.A) := fun a => (l₁ a).1
  have add₂ : ∀ a a', l₂ (a + a') = l₂ a * l₂ a' := fun a a' => congrArg Subtype.val (add₁ a a')
  have tors₂ : ∀ a, l₂ a ^ N = 1 := fun a => hH _
  have w₂ : ∀ a a', UU.CubWeil cu N (l₂ a) (l₂ a') (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) := fun a a' =>
    (show w (l₁ a) (l₁ a') = _ from w₁ a a') ▸ hw (l₁ a) (l₁ a')

  have mk : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ Sp k) (β : k →+* k') (z : k'ˣ),
        x ≫ 𝟙 _ = spMap β → (z : k') = β b.ζ →
        (∀ a, (toUnit (Over.mk x) ≫ l₂ a = 1 ↔ ∃ v, a = N • v)) ∧
        (∀ y : Over.mk x ⟶ c.A, y ^ N = 1 → ∃ a, toUnit _ ≫ l₂ a = y) ∧
        ∀ a a', Out.WeilIs c.A c.diag (N : ℕ) (toUnit (Over.mk x) ≫ l₂ a) (toUnit _ ≫ l₂ a')
          (unitOn (z ^ (2 * omegaStd a a'))) := by
    intro k' _ _ x β z hx hzz
    obtain rfl : x = spMap β := (Category.comp_id _).symm.trans hx
    obtain rfl : z = Units.map β.toMonoidHom b.ζ := Units.ext hzz
    have hz' : IsPrimitiveRoot (Units.map β.toMonoidHom (b.ζ ^ 2)) N :=
      hz₂.map_of_injective (Units.map_injective β.injective)
    have hk' : ((N : ℕ) : k') ≠ 0 := by rw [← map_natCast β]; exact (map_ne_zero β).2 hN
    have W : ∀ a a', UU.CubWeil cu N (toUnit (Over.mk (spMap β)) ≫ l₂ a) (toUnit _ ≫ l₂ a')
        (unitOn (Units.map β.toMonoidHom (b.ζ ^ 2) ^ omegaStd a a')) := fun a a' => by
      have H := (w₂ a a').comp (toUnit (Over.mk (spMap β)))
      have e : Units.map (toUnit (Over.mk (spMap β))).left.appTop.hom.toMonoidHom
          (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) = unitOn (Units.map β.toMonoidHom ((b.ζ ^ 2) ^ omegaStd a a')) :=
        Units.ext (congrArg (fun q => q.hom ((b.ζ ^ 2) ^ omegaStd a a').val)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
      rw [e, map_zpow] at H
      exact H
    have ker : ∀ a, toUnit (Over.mk (spMap β)) ≫ l₂ a = 1 → ∃ v, a = N • v := fun a ha =>
      SiegelOfPolarised.exists_smul_of_dvd fun a' => by
        have w₁ := W a a'
        rw [ha] at w₁
        have e := SiegelOfPolarised.unitOn_inj
          ((w₁.unique (UU.cubWeil_one_left cu w₁.2.1)).trans (map_one _).symm)
        exact (hz'.zpow_eq_one_iff_dvd _).1 e
    refine ⟨fun a => ⟨ker a, ?_⟩, SiegelOfPolarised.onto_torsion hN₀ _ (fun a b => by rw [add₂, MonObj.comp_mul])
      (fun a => by rw [← MonObj.comp_pow, tors₂, MonObj.comp_one]) ker ?_, fun a a' => ?_⟩
    · rintro ⟨v, rfl⟩
      have pw : ∀ m : ℕ, l₂ (m • v) = l₂ v ^ m := fun m => by
        induction m with
        | zero => rw [zero_smul, pow_zero]; exact mul_eq_left.1 ((add₂ 0 0).symm.trans (by rw [add_zero]))
        | succ m ih => rw [succ_nsmul, add₂, ih, pow_succ]
      rw [pw, tors₂, MonObj.comp_one]
    · rw [card k' _ _ hk']
      simp [two_mul]
    · have H := toW (W a a')
      rwa [map_pow, ← zpow_ofNat, ← zpow_mul] at H
  refine ⟨{ A := c.A
            ab := c.ab
            P := c.P
            isLB := c.isLB
            rig₁ := c.rig₁
            rig₂ := c.rig₂
            symm := c.symm
            lev := l₂
            lev_add := add₂
            lev_tors := tors₂
            geom := mk },
    𝟙 _, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl c.A) (inferInstanceAs (IsMonHom (𝟙 c.A))),
    ⟨𝟙 _, ⟨by simp, by simp⟩, ?_⟩, fun a => ?_⟩
  · exact (CechPic.cls_eq_iff c.isLB (pull_isLB c.isLB _)).1
      ((CechPic.pull_id _).symm.trans (CechPic.cls_pull c.isLB _ _).symm)
  · simp

end GlobalTheory.SiegLift
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.principal_siegel_object_odd_level_rigid : ∀ (h n n' d' : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (c : SiegPre h n (b.ζ : B) s) (c' : SiegPre h n' ζ' s') (f : S' ⟶ S) (φ φ' : c'.A.left ⟶ c.A.left), 3 ≤ n → Odd n → c.Principal → SRelBy c' c d' 1 f φ → SRelBy c' c d' 1 f φ' → φ = φ' := by
  first | exact @GlobalTheory.SiegRigid.eq_of_sRelBy | exact GlobalTheory.SiegRigid.eq_of_sRelBy | (intros; apply GlobalTheory.SiegRigid.eq_of_sRelBy <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
open GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.SharpIso

theorem iso_of_sRel : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N) (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (t : TObj (8 * g) N J b (𝟙 (Sp K))) (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ Q.A, ∀ u, x ≫ pr u = y u) → LBIso Q.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → SRel C c 0 0 (𝟙 _) → IsSharp W a bas t C → ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
  intro g n N B _ ζ K _ s c b C W J a bas t Q pr hpr huniv hQ hrel hsharp
  obtain ⟨φ, hpb, ⟨φ₂, hsq, hP⟩, -⟩ := hrel
  obtain ⟨pr', hpr', huniv', ht, -, -⟩ := hsharp
  have w : φ ≫ c.A.hom = C.A.hom := by simpa using hpb.1.w
  let f : C.A ⟶ c.A := Over.homMk φ w
  haveI : IsIso φ := hpb.1.isIso_fst_of_isIso
  haveI : IsIso f := by
    have : IsIso ((Over.forget _).map f) := by simpa [f] using (inferInstance : IsIso φ)
    exact isIso_of_reflects_iso f (Over.forget _)
  haveI hf : IsMonHom f := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f
    (fun _ x y => GlobalTheory.AbelianLetters.mul_comp_of_isGrpPullback_id f hpb x y)
  obtain ⟨ψ, hψ, -⟩ := huniv t.A (fun u => pr' u ≫ f)
  obtain ⟨χ, hχ, -⟩ := huniv' Q.A (fun u => pr u ≫ inv f)
  have h1 : ψ ≫ χ = 𝟙 _ := (huniv' t.A pr').unique (fun u => by
      rw [Category.assoc, hχ, ← Category.assoc, hψ, Category.assoc, IsIso.hom_inv_id, Category.comp_id])
    (fun u => Category.id_comp _)
  have h2 : χ ≫ ψ = 𝟙 _ := (huniv Q.A pr).unique (fun u => by
      rw [Category.assoc, hψ, ← Category.assoc, hχ, Category.assoc, IsIso.inv_hom_id, Category.comp_id])
    (fun u => Category.id_comp _)
  have hm : ∀ u, IsMonHom (ψ ≫ pr u) := fun u => by
    rw [hψ]; haveI := hpr' u; infer_instance
  have hψm : IsMonHom ψ := by
    refine ⟨(huniv _ fun u => η[Q.A] ≫ pr u).unique (fun u => ?_) fun _ => rfl,
      (huniv _ fun u => μ[t.A] ≫ ψ ≫ pr u).unique (fun u => Category.assoc _ _ _) fun u => ?_⟩
    · have := hm u
      have := hpr u
      rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · have := hm u
      have := hpr u
      rw [Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom]
  refine ⟨⟨ψ, χ, h1, h2⟩, hψm, ?_⟩
  have hsq' : Geo.Tor.IsSquare φ (f ⊗ₘ f).left :=
    ⟨by rw [← Over.comp_left, tensorHom_fst]; rfl, by rw [← Over.comp_left, tensorHom_snd]; rfl⟩
  obtain rfl := GlobalTheory.LamPull.isSquare_unique hsq hsq'
  have key : ∀ uv : Fin 8 × Fin 8, (lift (pr' uv.1) (pr' uv.2)).left ≫ (f ⊗ₘ f).left =
      ψ.left ≫ (lift (pr uv.1) (pr uv.2)).left := fun uv => by
    rw [← Over.comp_left, ← Over.comp_left, lift_map, comp_lift, hψ, hψ]
  rw [← cls_eq_iff t.isLB (pull_isLB Q.isLB _), (cls_eq_iff t.isLB (LB.isLB_linComb C.isLB _ _)).2 ht,
    cls_linComb C.isLB, (cls_eq_iff C.isLB (pull_isLB c.isLB _)).2 hP, cls_pull c.isLB,
    cls_pull Q.isLB, (cls_eq_iff Q.isLB (LB.isLB_linComb c.isLB _ _)).2 hQ, cls_linComb c.isLB]

  simp only [map_sum, map_zsmul, ← pull_comp, key]

end GlobalTheory.SharpIso
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_siegelObject_deeper_level_of_sections : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S V : Scheme.{0}) (s : S ⟶ Sp B) (sV : V ⟶ Sp B') (π : V ⟶ S) (c : SiegPre h n ζ s) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk π ⟶ c.A)), (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a, e a ^ d = toUnit (Over.mk π) ≫ c.lev a) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V) (β : B' →+* k) (z : kˣ), x ≫ sV = spMap β → (z : k) = β ζ' → (∀ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk (x ≫ π) ⟶ c.A, g ^ N = 1 → ∃ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a') (unitOn (z ^ (2 * omegaStd a a')))) → ∃ (C : SiegPre h N ζ' sV) (φ : C.A.left ⟶ c.A.left), SRelBy C c d 1 π φ ∧ (∀ a, (C.lev a).left ≫ φ = (e a).left) ∧ ∀ (T : Scheme.{0}) (t : T ⟶ V) (B'' : Type) [CommRing B''] (ζ'' : B'') (sT : T ⟶ Sp B'') (C' : SiegPre h N ζ'' sT), SiegPB C' C t ↔ ∃ φ' : C'.A.left ⟶ c.A.left, SRelBy C' c d 1 (t ≫ π) φ' ∧ ∀ a, (C'.lev a).left ≫ φ' = t ≫ (e a).left := by
  first | exact @GlobalTheory.siegCover_build | exact GlobalTheory.siegCover_build | (intros; apply GlobalTheory.siegCover_build <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem GlobalTheory.SiegLev.SQuot.eq_of_siegPB : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [CommRing o'] (ζ : o) (ζ' : o') (F : SFam h N ζ') (j : o →+* o') (Q : SQuot F n ζ j) (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ Q.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'), x ≫ Q.s = y ≫ Q.s → SiegPB c Q.univ x → SiegPB c Q.univ y → x = y := by
  intro h n N o o' _ _ ζ ζ' F j Q R _ _ x y s' c hxy hx hy
  haveI := Q.fin; haveI := Q.etale; haveI := Q.onto
  obtain ⟨R1, _, _, φ1, hl1, hφ1, x1, hx1⟩ := GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection R Q.X F.X Q.π x
  obtain ⟨R2, _, _, φ2, hl2, hφ2, y2, hy2⟩ := GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection R1 Q.X F.X Q.π (spMap φ1 ≫ y)
  set g : Sp R2 ⟶ Sp R := spMap φ2 ≫ spMap φ1 with hg
  set x2 : Sp R2 ⟶ F.X := spMap φ2 ≫ x1 with hx2d
  have hx2 : x2 ≫ Q.π = g ≫ x := by simp only [x2, g, Category.assoc, hx1]
  have hy2' : y2 ≫ Q.π = g ≫ y := by simp only [g, Category.assoc, hy2]
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c2, hc2⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n o o ζ ζ (RingHom.id o) (Sp R) (Sp R2) s' (g ≫ s') g rfl (by rw [hid, Category.comp_id])).1 c
  have key : ∀ z : Sp R ⟶ Q.X, ∀ z2 : Sp R2 ⟶ F.X, z2 ≫ Q.π = g ≫ z → SiegPB c Q.univ z → SRel c2 F.univ 1 (N / n) z2 := by
    intro z z2 hz hcz
    have A := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n n o o o ζ ζ ζ Q.X (Sp R) (Sp R2) Q.s s' (g ≫ s') Q.univ c c2 z g 1 1 1 ((sRel_one_one_iff _ _ _).2 hcz)).1
    have B : SRel c2 Q.univ 1 1 (g ≫ z) := A.1 ((sRel_one_one_iff _ _ _).2 hc2)
    have C := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n N n o o' o ζ ζ' ζ Q.X F.X (Sp R2) Q.s F.s (g ≫ s') Q.univ F.univ c2 Q.π z2 1 (N / n) 1 Q.low).1
    rw [hz] at C
    exact C.2 B
  have e := Q.fibre R2 x2 y2 (g ≫ s') c2 (by
      rw [← Q.base, ← Category.assoc, ← Category.assoc y2, hx2, hy2', Category.assoc, Category.assoc, hxy]; simp only [g, Category.assoc])
    (key x x2 hx2 hx) (key y y2 hy2' hy)
  rw [hx2, hy2'] at e
  have hcomp : spMap (φ2.comp φ1) = g := by
    simp only [g, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  exact GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom R R2 (φ2.comp φ1) inferInstance (hφ2.comp hφ1) Q.X x y (by rw [hcomp]; exact e)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.liftedRatios_eval_ideal_mul_eq_zero_succ : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)), a ∈ I → C.ev e i F = 0 → C.ev (e + 1) i (MvPolynomial.C a * F) = 0 := by
  first | exact @GlobalTheory.FormalAlg.JStep.ev_succ_C_mul_eq_zero | exact GlobalTheory.FormalAlg.JStep.ev_succ_C_mul_eq_zero | (intros; apply GlobalTheory.FormalAlg.JStep.ev_succ_C_mul_eq_zero <;> assumption)
end
