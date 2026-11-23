module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle176
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle177
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWitOfPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.SetTheory.ZFC.PSet
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_very_ample_power : ∀ (A : Type) [CommRing A] (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (g₀ : A →+* K) (X₀ : Scheme.{0}) (π : X₀ ⟶ X.left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ X.hom (Spec.map (CommRingCat.ofHom g₀)) → ∃ d : ℕ, 1 ≤ d ∧ FirstCohomologyVanishes ((pw L d).pull π) ∧ ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (pw L d)), VeryAmpleBy X.hom (pw L d) s := by
  first | exact @GlobalTheory.Algebraise.exists_veryAmple_h1Zero_pull | exact GlobalTheory.Algebraise.exists_veryAmple_h1Zero_pull | (intros; apply GlobalTheory.Algebraise.exists_veryAmple_h1Zero_pull <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleLocalBase

theorem relAmple_baseChange {S S' : Scheme.{0}} [IsAffine S] {f : S' ⟶ S} {A : Over S} {A' : Over S'}
    {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left} (h : IsPullback φ A'.hom A.hom f)
    (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hA : RelAmple A L) : RelAmple A' L' := by
  obtain ⟨w, hw⟩ := hw
  exact relAmple_pull h hL hL' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S) (fun _ => trivial) hA

theorem relAmple_of_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) (M : LB B.left), Flat B.hom → IsProjBy B.hom → M.IsLB → ∀ (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀), Function.Surjective g → ∀ (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left), IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)) → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → RelAmple Y₀ N₀ → RelAmple B M := by
  intro R _ _ _ B M hF hP hM R₀ _ _ g hg Y₀ b hb N₀ hN₀ hiso hA
  have hker : RingHom.ker g ≤ RingHom.ker (IsLocalRing.residue R) := by
    rw [IsLocalRing.ker_residue]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)
  let g' : R₀ →+* IsLocalRing.ResidueField R :=
    RingHom.liftOfSurjective g hg ⟨IsLocalRing.residue R, hker⟩
  have hg' : g'.comp g = IsLocalRing.residue R := RingHom.liftOfSurjective_comp g hg _
  let k := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hk : Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom g) = k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  let ψ : pullback B.hom k ⟶ Y₀.left := hb.lift (pullback.fst B.hom k)
    (pullback.snd B.hom k ≫ Spec.map (CommRingCat.ofHom g'))
    (by rw [Category.assoc, hk, pullback.condition])
  have hψ : ψ ≫ b = pullback.fst B.hom k := hb.lift_fst _ _ _
  have hψ' : IsPullback ψ (pullback.snd B.hom k) Y₀.hom (Spec.map (CommRingCat.ofHom g')) := by
    refine IsPullback.of_right ?_ (hb.lift_snd _ _ _) hb
    rw [hψ, hk]
    exact IsPullback.of_hasPullback _ _
  have h₁ : RelAmple ((Over.pullback k).obj B) (M.pull (pullback.fst B.hom k)) :=
    relAmple_baseChange (A' := (Over.pullback k).obj B) hψ' hN₀ (pull_isLB hM _)
      (LBIso.chartPull (Geo.Tor.chartPullPull N₀ ψ ψ rfl)
        (chartPullSame M (fun _ : PUnit => pullback.fst B.hom k) (fun _ => b) (fun _ => 1) ψ
          fun _ => hψ.symm) hiso).symm hA
  obtain ⟨r, hr, h₂⟩ := GlobalTheory.AmpleNear.relAmple_near_fibre R B M hF hP hM _ (IsLocalRing.residue R) (fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨a, 1, by simp, by simp⟩) h₁
  have hu : IsUnit r := (IsLocalRing.residue_ne_zero_iff_isUnit r).1 hr
  have htop : PrimeSpectrum.basicOpen r = ⊤ := by
    exact top_le_iff.1 fun p _ => fun hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
  generalize (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of R)).Opens) = U at htop h₂
  subst htop
  let j := Scheme.Opens.ι (X := Spec (CommRingCat.of R)) ⊤
  have : IsIso j := inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
  have : IsAffine (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme := isAffineOpen_top _
  have h₃ : IsPullback (inv (pullback.fst B.hom j)) B.hom (pullback.snd B.hom j) (inv j) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]⟩
  refine relAmple_baseChange (A := (Over.pullback j).obj B) h₃ (pull_isLB hM _) hM ?_ h₂
  exact (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSec M _ _ (IsIso.inv_hom_id (pullback.fst B.hom j)))
    ⟨_, idIso_isGen (pull_isLB hM _)⟩).symm

end GlobalTheory.AmpleLocalBase
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_form_correction_next_thickening_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k'))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick R I (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0) → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ d, AddMonoidAlgebra.coeff G d ∈ I ^ (e + 1)) ∧ (∀ k : (H (e + 1)).ι, MvPolynomial.eval₂Hom (cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) ((H (e + 1)).U k)) (fun j => (s (e + 1) j).f k) (F - G) = 0) := by
  first | exact @GlobalTheory.Degen.exists_form_correction_local | exact GlobalTheory.Degen.exists_form_correction_local | (intros; apply GlobalTheory.Degen.exists_form_correction_local <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ArcDataDescent



theorem hasArcData_descends : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ : Sp R ⟶ Y.X) (y : Sp (FractionRing R) ⟶ Xo.XF c), y ≫ Y.j = jK R ≫ χ → ∀ (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t), P.TorsionIso → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ g : R →+* V, Function.Injective g → I.map g ≤ IsLocalRing.maximalIdeal V → ¬ IsUnit (g u) → (∀ x, x ≠ 0 → IsUnit (g (f x))) → Y.HasArcData a (IsLocalRing.maximalIdeal V) (g.comp f) (g u) (spMap g ≫ χ) → Y.HasArcData a I f u χ := by
  intro hL h2 h3 h4 h5 h6 hH E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a R _ _ _ _ I f u hR _ hf χ y hy t m P hT V _ _ _ hV g hg hI
    _ _ hA
  letI := H.starRing
  obtain ⟨hV₁, hV₂, -⟩ := hV
  have hV : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV₂⟩
  have := hR.1
  have := hR.2.2.1
  obtain ⟨t', m₀, P', hD, bc, mbc, hPU, hm₀, xl, el⟩ :=
    exists_pelUnif_pull h3.cubePull hL.polBaseChange h4.unifBaseChange h5 hR hV t P g hg hI
  obtain ⟨m', hm'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₀
  obtain ⟨W₁⟩ := (Y.hasArcData_iff a _ _ _ _).1 hA
  obtain ⟨W, rfl, k₁, k₂⟩ := WitnessMove.exists_wit h4.unifBaseChange h5 h6.unifUniq (qkPullExists hL.globalFns) hV W₁
    t' m' P'
  obtain rfl : m' = W.m := (eq_of_heq k₁).symm
  obtain rfl : P' = W.P := (eq_of_heq k₂).symm
  have hm : W.m.φ = (bc.hom.left ≫ pullback.fst t.G.hom (specOf g)) ≫ m.φ := by rw [hm', hm₀]
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  have gD := pull_grp hD
  obtain ⟨φ, gφ, hφ, wφ⟩ := exists_desc_pol hL h2 hH f hg a.D₀.P P.D.toPre.P W.P.D.toPre.P gD s1 ⟨hD.w, hD.w_gen⟩
    ⟨W.w, s2⟩ (fun F _ _ i₁ i₂ => agree hL h2 h5 hR hV hf hg y hy m P hT W hD bc mbc hPU hm xl el F i₁ i₂)
  have he : eSec P.D.toPre.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A := (cubeMapOf gφ).e_comm
  obtain ⟨w, gw, rw'⟩ := Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap f) a.D₀.P.A P.D.toPre.P.A φ he
    ⟨a.D₀.P.L, a.D₀.rig, a.D₀.P.isLB, a.D₀.rig_gen⟩ ⟨P.D.toPre.P.L, P.D.toPre.rig, P.D.toPre.P.isLB, P.D.toPre.rig_gen⟩ wφ
  have pw := (isGen_iff w).1 gw
  have pD := (isGen_iff hD.w).1 hD.w_gen
  obtain ⟨w', T⟩ := exists_comp P.D.toPre.P.isLB w hD.w pw pD a.D₀.P.isLB W.P.D.toPre.P.isLB
  have tr : ∀ {F : Type} [Field F] {K : Type} [Fintype K] {pt : K → (Sp F ⟶ W.P.D.toPre.P.A.left)}
      {pt₀ : K → (Sp F ⟶ a.D₀.P.A.left)} {ε : K → ℤ} (s : LB.Gen (LB.LinComb W.P.D.toPre.P.L pt ε))
      (s₀ : LB.Gen (LB.LinComb a.D₀.P.L pt₀ ε)) (x : F), GenRel w' s s₀ x ↔ GenRel W.w s s₀ x := by
    have r₀ := (maps_iff w _ (fun _ => eSec a.D₀.P.A) _ P.D.toPre.rig a.D₀.rig (spMap f) _
      (rigPull_le φ (spMap f) he a.D₀.P.L) (fun _ => rfl)).1 rw'
    have r₂ := T.pmaps_comp P.D.toPre.P.isLB (fun _ => hD.he) r₀ (pmaps_rig' hD)
    rw [← spMap_comp] at r₂
    have g' := (isGen_iff w').2 (T.pgen_comp P.D.toPre.P.isLB pw pD)
    have key : ∀ (ψ : W.P.D.toPre.P.A.left ⟶ a.D₀.P.A.left) (v : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ψ)), ψ = W.φ →
        v.IsGen → PMaps v (K := PUnit) (fun _ => eSec W.P.D.toPre.P.A) (fun _ => eSec a.D₀.P.A) (fun _ => 1)
          W.P.D.toPre.rig a.D₀.rig (spMap (g.comp f)) →
        ∀ {F : Type} [Field F] {K : Type} [Fintype K] {pt : K → (Sp F ⟶ W.P.D.toPre.P.A.left)}
          {pt₀ : K → (Sp F ⟶ a.D₀.P.A.left)} {ε : K → ℤ} (s : LB.Gen (LB.LinComb W.P.D.toPre.P.L pt ε))
          (s₀ : LB.Gen (LB.LinComb a.D₀.P.L pt₀ ε)) (x : F), GenRel v s s₀ x ↔ GenRel W.w s s₀ x := by
      rintro _ v rfl gv pv F _ K _ pt pt₀ ε s s₀ x
      rw [rigidified_iso_unique hL.globalFns W.P.D.toPre.P a.D₀.P.isLB W.φ v W.w gv s2 _ _
        ((maps_iff v _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig (spMap (g.comp f)) _
          (rigPull_le W.φ (spMap (g.comp f)) W.he a.D₀.P.L) (fun _ => rfl)).2 pv) s3]
    intro F _ K _ pt pt₀ ε s s₀ x
    exact key _ w' hφ g' r₂ s s₀ x
  let xD : W.P.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD.xe with map_smul' := xl }
  have := P.D.toPre.P.isAb.smooth
  have := a.D₀.P.isAb.proper
  let gam : FractionRing R →+* FractionRing V :=
    IsFractionRing.lift (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V _).comp hg)
  have hgam : ∀ r, gam (algebraMap R _ r) = algebraMap V _ (g r) := fun r => IsFractionRing.lift_algebraMap _ r
  refine ⟨t, m, P, φ, he, w, W.e.trans xD, gφ, gw, rw', fun x => ?_, fun z => ?_, fun F _ _ _ _ uF ha hu => ?_⟩
  · refine ext_of_injective hg gD.1 a.D₀.P.A.hom ?_ ?_
    · rw [Category.assoc, gφ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, gφ.1.w]
    · rw [← Category.assoc, ← act_proj hD (el x), Category.assoc, hφ, s4 x, ← Category.assoc, hφ]
  · refine ext_of_injective (p := 𝟙 _) (p' := 𝟙 _) hg (IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans (Category.id_comp _).symm⟩) a.D₀.P.A.hom ?_ ?_
    · rw [Category.assoc, gφ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    · have k := hD.c_pr (W.e z)
      refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) k.symm)).trans ?_
      rw [Category.assoc, hφ, s5 z, spMap_comp, Category.assoc]
  · obtain ⟨F', _, _, σ, ρ, hσρ⟩ := exists_common_field (algebraMap (FractionRing R) F) gam
    letI : Algebra (FractionRing R) F' := (σ.comp (algebraMap (FractionRing R) F)).toAlgebra
    letI : Algebra (FractionRing O') F' := (σ.comp (algebraMap (FractionRing O') F)).toAlgebra
    letI : Algebra (FractionRing V) F' := ρ.toAlgebra
    have hF : ∀ r : R, algebraMap (FractionRing R) F' (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing V) F' (algebraMap V (FractionRing V) (g r)) := fun r =>
      (RingHom.congr_fun hσρ _).trans (congrArg ρ (hgam r))
    have ha' : ∀ x, algebraMap (FractionRing O') F' (algebraMap O' _ x) =
        algebraMap (FractionRing R) F' (algebraMap R _ (f x)) := fun x => congrArg σ (ha x)
    have hu' : σ uF = algebraMap (FractionRing R) F' (algebraMap R _ u) := congrArg σ hu
    have hj := jFK_comm hF
    have jR : jFK (R := R) F' = spMap σ ≫ jFK (R := R) F := spMap_comp _ _
    have jO : jFK (R := O') F' = spMap σ ≫ jFK (R := O') F := spMap_comp _ _
    refine ⟨fun z => ?_, fun yF hyF k p₀ s hs q₀ q x e₁ e₂ e₃ e₄ => ?_⟩
    · have k := (s6 F' (σ uF) (fun x => (ha' x).trans (hF _)) (hu'.trans (hF _))).1 z
      obtain ⟨n₁, n₂⟩ := pmaps_psi' hD hj (χ' := W.e z) rfl
      have k' := (genRel_transfer T P.D.toPre.P.isLB W.P.D.toPre.P.isLB (fun _ => n₁) n₂ _ _).2 ((tr _ _ _).2 k)
      rw [← map_zpow₀] at k'
      refine (genRel_pull_iff σ w _ _ _).1 ((genRel_congr P.D.toPre.P.isLB a.D₀.P.isLB w ?_ ?_
        (DVR.pullGen_isGen _ _ _ _ (P.D.toPre.psi_gen _) _)
        (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (P.D.toPre.psi_gen _) _) _)
        (DVR.pullGen_isGen _ _ _ _ (a.D₀.psi_gen _) _)
        (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (a.D₀.psi_gen _) _) _)
        (fun p J hJ => ?_) (fun p J hJ => ?_) _).1 k')
      · exact funext fun _ => (congrArg (· ≫ _) jR).trans (Category.assoc _ _ _)
      · exact funext fun _ => (congrArg (· ≫ _) jO).trans (Category.assoc _ _ _)
      · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans (val_pull hJ _ _ _)).symm)
        exact congrArg (fun r => val (P.D.toPre.psi (hD.xe (W.e z))) r p J)
          ((congrArg (𝟙 _ ≫ ·) jR).trans (Category.assoc _ _ _).symm)
      · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans (val_pull hJ _ _ _)).symm)
        exact congrArg (fun r => val (a.D₀.psi z) r p J) ((congrArg (𝟙 _ ≫ ·) jO).trans (Category.assoc _ _ _).symm)
    · have hk : 1 ≤ k := by
        rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact l.A_pos
        · exact le_trans (by norm_num) l.three_le
      obtain ⟨q₀', hq₀, -⟩ := TorusExt.existsUnique_qkExt a.bimult σ (F' := F') rfl q₀
      obtain ⟨q', hq, -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult σ (F' := F') rfl q
      let x' : TFK (R := R) F' ⟶ P.A.A := Over.homMk (spMap σ ≫ x.left) (by
        have w₂ : x.left ≫ P.A.A.hom = jFK (R := R) F := Over.w x
        show (spMap σ ≫ x.left) ≫ P.A.A.hom = jFK (R := R) F'
        rw [Category.assoc, w₂, jR])
      let σ' : F →ₐ[FractionRing R] F' := ⟨σ, fun _ => rfl⟩
      refine (TorsionExt.qkToAkU_iff_of_qkExt ⟨hL, h2, h3, h4, h5⟩ R I hR P.D P.A t.G t.semi P.U F F' σ' k hk q q' x x' hq
        rfl).2 ?_
      obtain ⟨τ, hτ, -⟩ := exists_qk_pull_equiv hL h2 R V g P.D.toPre W.P.D.toPre hD P.D.tau_bimult W.P.D.tau_bimult F' hF k
      obtain ⟨k₁, k₂⟩ := (hτ q' _).1 rfl
      refine toA_down hL hR hV m P W hD bc mbc hPU hm F' hF (σ uF) ha' hu' (spMap σ ≫ yF)
        (by rw [Category.assoc, hyF, jR, Category.assoc]) k p₀ s hs q₀' q' (τ q') x' (ArcSpecialise.qkExt_trans e₁ hq₀)
        k₁ k₂ ?_ (fun z => ?_) ?_
      · rw [k₁, AddEquiv.symm_apply_eq, hq.1, hq₀.1]; exact e₂
      · obtain ⟨n₁, n₂⟩ := pmaps_of_isPullGtF k₂ (χ' := W.e z) rfl
        refine (tr _ _ _).1 ((genRel_transfer T P.D.toPre.P.isLB W.P.D.toPre.P.isLB n₁ n₂ _ _).1 ?_)
        rw [← map_zpow₀, hq₀.1]
        exact (genRel_congr P.D.toPre.P.isLB a.D₀.P.isLB w (gtφ_ext rfl hq _) (gtφ_ext rfl hq₀ _) (q'.g.isGen _)
          (DVR.pullGen_isGen _ _ _ _ (q.g.isGen _) _) (q₀'.g.isGen _) (DVR.pullGen_isGen _ _ _ _ (q₀.g.isGen _) _)
          (fun p J hJ => val_corr hJ (hq.2.2 _) _) (fun p J hJ => val_corr hJ (hq₀.2.2 _) _) _).2
          ((genRel_pull_iff σ w _ _ _).2 (e₃ z))
      · show (spMap σ ≫ x.left) ≫ _ = _
        rw [Category.assoc, e₄, Category.assoc]

end GlobalTheory.ArcDataDescent
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.exists_degData_psi_of_section_nonzero_fibres : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ φ : R →+* V, Function.Injective φ → (IsLocalRing.maximalIdeal V).comap φ = I → ∀ (D : DegPre R) (D' : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A' G') (U₀ : Unif (IsLocalRing.maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), Under U' U₀.toUnifPre → ThetaNZ G U.P.L.L → ∃ (psi : _) (h : _) (Dd : DegData R I) (hD : IsPullDeg φ (withPsi D psi h) D'.toPre), Dd.toPre = withPsi D psi h ∧ hD.e.hom.left ≫ pullback.fst _ _ = C.β ∧ HEq hD.w C.v ∧ hD.xe = C.xe := by
  first | exact @GlobalTheory.PsiRing.exists_degData_of_thetaNZ | exact GlobalTheory.PsiRing.exists_degData_of_thetaNZ | (intros; apply GlobalTheory.PsiRing.exists_degData_of_thetaNZ <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.flat_and_surjective_of_surjective_points' : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'], SmConn G → SmConn G' → ∀ i : G ⟶ G', IsMonHom i → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ i = y) → Flat i.left ∧ Surjective i.left := by
  first | exact @GlobalTheory.SS.flat_and_surjective_of_surjective_points | exact GlobalTheory.SS.flat_and_surjective_of_surjective_points | (intros; apply GlobalTheory.SS.flat_and_surjective_of_surjective_points <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_uniformisationTest_of_geometricTest : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∃ (τ : ex.core.Test y) (e : pullback τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j) ≅ t.mod.Φ.G.left), e.hom ≫ t.mod.Φ.G.hom = pullback.snd _ _ ∧ e.hom ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  first | exact @GlobalTheory.ZH.Clos.exists_core_test_of_geoTest | exact GlobalTheory.ZH.Clos.exists_core_test_of_geoTest | (intros; apply GlobalTheory.ZH.Clos.exists_core_test_of_geoTest <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem finite_notMem_coheight_le_one {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : {ξ : X | ξ ∉ U ∧ Order.coheight ξ ≤ 1}.Finite := by
  apply _root_.GlobalTheory.PushFinite.finite_notMem_coheight_le_one <;> assumption

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isNoetherian [IsNoetherianRing o] : IsNoetherian M.Z :=
  have := M.lft
  have := M.qc
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  {}

theorem isNoetherianRing_O [IsNoetherianRing o] (z : M.Z) : IsNoetherianRing (M.O z) :=
  have := M.isNoetherian
  isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

theorem coheight_le_one_of_valuationRing [IsNoetherianRing o] {ξ : M.Z} (h : ValuationRing (M.O ξ)) :
    Order.coheight ξ ≤ 1 := by
  have := M.isNoetherianRing_O ξ
  have : IsPrincipalIdealRing (M.O ξ) := IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
  have h1 : ringKrullDim (M.O ξ) ≤ 1 := Ring.krullDimLE_iff.1 inferInstance
  rw [← ringKrullDim_eq_of_ringEquiv (M.stalkEquiv ξ), ringKrullDim_stalk_eq_coheight] at h1
  exact_mod_cast h1

theorem exists_specializes_isLocalization (z : M.Z) (q : Ideal (M.O z)) [q.IsPrime] :
    ∃ (ξ : M.Z) (h : ξ ⤳ z),
      letI := (Subalgebra.inclusion (O_le_of_specializes h)).toRingHom.toAlgebra
      IsLocalization.AtPrime (M.O ξ) q := by
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  let ψ : ∀ {x : M.Z} (_ : x ∈ V), Γ(M.Z, V) →+* M.O x := fun {x} hx =>
    (M.stalkEquiv x).toRingHom.comp (M.Z.presheaf.germ V x hx).hom
  have hψ : ∀ {x : M.Z} (hx : x ∈ V) (f : Γ(M.Z, V)), ψ hx f = ⟨valF M.pt V f, valF_mem_O hx f⟩ :=
    fun hx f => stalkEquiv_germ hx f
  have hloc : ∀ (p : PrimeSpectrum Γ(M.Z, V)) (hp : hV.fromSpec p ∈ V),
      @IsLocalization.AtPrime _ _ (M.O (hV.fromSpec p)) _ (ψ hp).toAlgebra p.asIdeal _ := fun p hp => by
    let : Algebra Γ(M.Z, V) (M.Z.presheaf.stalk (hV.fromSpec p)) :=
      TopCat.Presheaf.algebra_section_stalk M.Z.presheaf (U := V) ⟨_, hp⟩
    let := (ψ hp).toAlgebra
    have : IsLocalization p.asIdeal.primeCompl (M.Z.presheaf.stalk (hV.fromSpec p)) :=
      hV.isLocalization_stalk' p hp
    exact IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl
      ({ M.stalkEquiv _ with commutes' := fun _ => rfl } :
        M.Z.presheaf.stalk (hV.fromSpec p) ≃ₐ[Γ(M.Z, V)] M.O (hV.fromSpec p))
  have hmem : ∀ p : PrimeSpectrum Γ(M.Z, V), hV.fromSpec p ∈ V := fun p => by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨p₀, rfl⟩ : ∃ p₀ : PrimeSpectrum Γ(M.Z, V), hV.fromSpec p₀ = z :=
    (hV.range_fromSpec ▸ hz : z ∈ Set.range hV.fromSpec)
  let := (ψ hz).toAlgebra
  have h₀ := hloc p₀ hz
  let p : PrimeSpectrum Γ(M.Z, V) := ⟨q.comap (ψ hz), inferInstance⟩
  have hle : p.asIdeal ≤ p₀.asIdeal := fun a ha =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (M.O (hV.fromSpec p₀)) p₀.asIdeal a).1
      (IsLocalRing.le_maximalIdeal_of_isPrime q ha)
  have hs : hV.fromSpec p ⤳ hV.fromSpec p₀ :=
    ((PrimeSpectrum.le_iff_specializes p p₀).1 hle).map hV.fromSpec.continuous
  refine ⟨_, hs, ?_⟩
  let := (Subalgebra.inclusion (O_le_of_specializes hs)).toRingHom.toAlgebra
  let := (ψ (hmem p)).toAlgebra
  have h₁ := hloc p (hmem p)
  have : IsScalarTower Γ(M.Z, V) (M.O (hV.fromSpec p₀)) (M.O (hV.fromSpec p)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hψ (hmem p) a).trans
      (congrArg (Subalgebra.inclusion (O_le_of_specializes hs)) (hψ hz a)).symm
  have h₂ := IsLocalization.isLocalization_of_submonoid_le (M.O (hV.fromSpec p₀)) (M.O (hV.fromSpec p))
    p₀.asIdeal.primeCompl p.asIdeal.primeCompl (fun a ha h => ha (hle h))
  refine IsLocalization.of_le_of_exists_dvd (p.asIdeal.primeCompl.map (algebraMap _ (M.O (hV.fromSpec p₀)))) _
    (by rintro _ ⟨a, ha, rfl⟩; exact ha) fun n hn => ?_
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj p₀.asIdeal.primeCompl n
  refine ⟨_, ⟨a, fun ha => ?_, rfl⟩, _, e.symm⟩
  have ha' : algebraMap _ (M.O (hV.fromSpec p₀)) a ∈ q := ha
  rw [← e] at ha'
  exact hn ((Ideal.mul_unit_mem_iff_mem q (IsLocalization.map_units _ s)).1 ha')

theorem mem_O_of_forall_valuationRing [IsNoetherianRing o] (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    (z : M.Z) (φ : Ω) (h : ∀ ξ : M.Z, ξ ⤳ z → ValuationRing (M.O ξ) → φ ∈ M.O ξ) : φ ∈ M.O z := by
  have := M.isNoetherianRing_O z
  have := isIntegrallyClosed_O hn z
  obtain ⟨y, rfl⟩ : φ ∈ (algebraMap (M.O z) Ω).range := by
    refine (mem_range_algebraMap_iff_forall_height_eq_one φ).mpr fun q _ h1 => ?_
    obtain ⟨ξ, hξ, hloc⟩ := M.exists_specializes_isLocalization z q
    let := (Subalgebra.inclusion (O_le_of_specializes hξ)).toRingHom.toAlgebra
    have : IsScalarTower (M.O z) (M.O ξ) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have := isDiscreteValuationRing_of_height_eq_one q h1 (M.O ξ)
    exact (mem_range_algebraMap_iff_mem_primeLocalSubalgebra q (M.O ξ) φ).mp
      ⟨⟨φ, h ξ hξ inferInstance⟩, rfl⟩
  exact y.2

end RatModel

theorem normalModel_height_le_one :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o],
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (z : M.Z),
      (∀ φ : Ω, (∀ ξ : M.Z, ξ ⤳ z → ValuationRing (M.O ξ) → φ ∈ M.O ξ) → φ ∈ M.O z) ∧
      IsNoetherianRing (M.O z) ∧
      ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → {ξ : M.Z | ξ ∉ U ∧ ValuationRing (M.O ξ)}.Finite := by
  intro o Ω _ _ _ M _ hn z
  have := M.isNoetherian
  exact ⟨M.mem_O_of_forall_valuationRing hn z, M.isNoetherianRing_O z, fun U hU =>
    (finite_notMem_coheight_le_one U hU).subset fun _ h => ⟨h.1, M.coheight_le_one_of_valuationRing h.2⟩⟩

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.form_vanishes_of_torsion_torusExtension : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ v, Crd (Φ.H 1) F x.left v ∧ MvPolynomial.eval v Pf = 0) → ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, MvPolynomial.eval v Pf = 0) := by
  first | exact @GlobalTheory.ZH.TorsionVanish.form_vanishes_of_torsion | exact GlobalTheory.ZH.TorsionVanish.form_vanishes_of_torsion | (intros; apply GlobalTheory.ZH.TorsionVanish.form_vanishes_of_torsion <;> assumption)
end
