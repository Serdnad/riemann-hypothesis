module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle391
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2999
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameTheoremOfCube
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2971
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVHom
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

theorem trivCond_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Out.Rigidified A N → ∀ (T : Scheme.{0}) (t : T ⟶ S), (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ TrivCond A N V (V.ι ≫ t)) → TrivCond A N T t := by
  intro S A _ N hA hN hR T t hloc Y φ y hY
  haveI := hA.comm
  letI : GrpObj ((Over.pullback t).obj A) := Functor.grpObjObj
  let e : Over.mk y ≅ (Over.pullback t).obj A := Over.isoMk hY.isoPullback hY.isoPullback_hom_snd
  letI I : GrpObj (Over.mk y) := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  have hP : IsGrpPullback (Over.mk y) A t φ :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A t)).congr (Category.id_comp _)
      (by simp [e])
  have hA' : IsAbelianScheme (Over.mk y) := by
    refine ⟨?_, MorphismProperty.of_isPullback (P := @Smooth) hP.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hP.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hP.1 hA.geomConnected⟩
    rw [isCommMonObj_iff_isMulCommutative]
    intro U
    refine ⟨⟨fun x z => Over.OverMorphism.ext (hP.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
    rw [← hP.2 U x z (pushPt hP.1.w x) (pushPt hP.1.w z) rfl rfl,
      ← hP.2 U z x (pushPt hP.1.w z) (pushPt hP.1.w x) rfl rfl, _root_.mul_comm]
  haveI := hA'.comm
  obtain ⟨r, hr⟩ := hR
  have he : eSec (Over.mk y) ≫ φ = t ≫ eSec A := (cubeMapOf hP).e_comm
  have g := rigPullOf_isGen (G' := Over.mk y) (G := A) φ t he N r hr
  have hR' : Out.Rigidified (Over.mk y) (N.pull φ) := ⟨_, g⟩
  refine GlobalTheory.T.exists_generator_rigidified_locally_trivial T (Over.mk y) (N.pull φ) hA' (pull_isLB hN φ) hR' (fun τ => ?_)
  obtain ⟨V, hτ, hV⟩ := hloc τ
  refine ⟨V, hτ, ?_⟩
  have H : IsPullback ((y ⁻¹ᵁ V).ι ≫ φ) (y ∣_ V) A.hom (V.ι ≫ t) :=
    (isPullback_morphismRestrict y V).flip.paste_horiz hY
  exact (GlobalTheory.Mum.exists_gen_pull_pull_iff hN φ (y ⁻¹ᵁ V).ι).2 (hV _ _ _ H)

end GlobalTheory.TrivLocus
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ D : DegData R I}
  {A₁ A₂ A : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)}
  [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

structure IsProdUnif (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (U : UnifPre I D A (G₁ ⊗ G₂))
    (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X)
    (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A) : Prop where
  gen_pr₁ : U.gen.hom ≫ a₁ = (Over.pullback (jK R)).map (fst G₁ G₂) ≫ U₁.gen.hom
  gen_pr₂ : U.gen.hom ≫ a₂ = (Over.pullback (jK R)).map (snd G₁ G₂) ≫ U₂.gen.hom
  wL : ∃ w : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left), w.IsGen
  q_pr₁ : ∀ e, (U.gt e).q ≫ (Over.pullback (thick R I e)).map p₁ =
    (Over.pullback (thick R I e)).map (fst G₁ G₂) ≫ (U₁.gt e).q
  q_pr₂ : ∀ e, (U.gt e).q ≫ (Over.pullback (thick R I e)).map p₂ =
    (Over.pullback (thick R I e)).map (snd G₁ G₂) ≫ (U₂.gt e).q
  i_pr₁ : ∀ (e : ℕ) (h : D₁.toPre.X → D.toPre.X), (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) →
    ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X,
      TorusHomOf h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂) = t ≫ (U₁.gt e).i
  i_pr₂ : ∀ (e : ℕ) (h : D₂.toPre.X → D.toPre.X), (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) →
    ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
      TorusHomOf h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂) = t ≫ (U₂.gt e).i

variable {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂} {U : UnifPre I D A (G₁ ⊗ G₂)}
  {p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A} {p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A} {q₁ : D.toPre.X →+ D₁.toPre.X}
  {q₂ : D.toPre.X →+ D₂.toPre.X} {a₁ : A.A ⟶ A₁.A} {a₂ : A.A ⟶ A₂.A}

theorem IsProdUnif.linHom_fst (hU : IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂) (j₁ : D₁.toPre.X →+ D.toPre.X)
    (h₁ : ∀ y, q₁ (j₁ y) = y) (h₂ : ∀ y, q₂ (j₁ y) = 0) : LinHom U U₁ p₁ j₁ (fst G₁ G₂) :=
  ⟨inferInstance, fun e => (hU.q_pr₁ e).symm, fun e => hU.i_pr₁ e j₁ h₁ h₂⟩

theorem IsProdUnif.linHom_snd (hU : IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂) (j₂ : D₂.toPre.X →+ D.toPre.X)
    (h₁ : ∀ y, q₁ (j₂ y) = 0) (h₂ : ∀ y, q₂ (j₂ y) = y) : LinHom U U₂ p₂ j₂ (snd G₁ G₂) :=
  ⟨inferInstance, fun e => (hU.q_pr₂ e).symm, fun e => hU.i_pr₂ e j₂ h₁ h₂⟩

end GlobalTheory.MumProd
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isGtPointInvolutionAction_sub_of_idempotent : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O), a * a = a → ∀ g₀ g h t : GtPtF D F, GtPtAct oa a g₀ g → GtPtAct oa a h h → GtPtF.IsAdd t h g → GtPtAct oa a t t := by
  first | exact @GlobalTheory.Mum.IdemDiff.gtPtAct_of_isAdd | exact GlobalTheory.Mum.IdemDiff.gtPtAct_of_isAdd | (intros; apply GlobalTheory.Mum.IdemDiff.gtPtAct_of_isAdd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem gs_sub' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_comp_map {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (V : X.Opens) (hz : h (g z) ∈ V)
    (a : Γ(X, V)) : gs (g ≫ h) z V a = (g.stalkMap z).hom (gs h (g z) V a) := by
  rw [← gs_pull g h z V hz a, gs_eq_map_gs g z (h ⁻¹ᵁ V) hz, gs_pull (𝟙 Y) h (g z) V hz a, Category.id_comp]

theorem secCarriedOver_of_lift {X Z P : Scheme.{0}} (q : Z ⟶ X) (p₁ : Z ⟶ P) (L : LB X) (W O : X.Opens) (hOW : O ≤ W)
    (τ : ∀ k : L.ι, Γ(Z, q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k)ˣ) (d : ℕ) (B : Fin d → Γ(P, ⊤))
    (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k))
    (hdec : ∀ (z : Z) (k : L.ι), q z ∈ O → q z ∈ L.U k →
      gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs p₁ z ⊤ (B l) * gs q z (O ⊓ L.U k) (s l k))
    (huniq : ∀ (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U →
      (∀ z : Z, q z = x → ∑ l, gs p₁ z ⊤ (B l) * gs q z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0)
    (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)) (f' : Z ⟶ Z) (hf'q : f' ≫ q = q ≫ φ) (hf'p : f' ≫ p₁ = p₁)
    (hcar : FrameCarriedAlong L q (q ⁻¹ᵁ W) τ φ w f') (l : Fin d) : SecCarriedOver L O (s l) φ w := by
  have hpt : ∀ z, q (f' z) = φ (q z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hf'q, Scheme.Hom.comp_apply]
  intro x j k hxO hφxO hxk hφxj
  let U' : X.Opens := O ⊓ L.U k ⊓ φ ⁻¹ᵁ (O ⊓ L.U j) ⊓ ((L.pull φ).U (fun _ => j) ⊓ L.U k)
  have h1 : U' ≤ φ ⁻¹ᵁ (O ⊓ L.U j) := fun _ h => h.1.2
  have h2 : U' ≤ (L.pull φ).U (fun _ => j) ⊓ L.U k := fun _ h => h.2
  have h3 : U' ≤ O ⊓ L.U k := fun _ h => h.1.1
  let a : Fin d → Γ(X, U') := fun l' =>
    (X.presheaf.map (homOfLE h1).op).hom ((φ.app (O ⊓ L.U j)).hom (s l' j)) -
      (X.presheaf.map (homOfLE h2).op).hom (w.s (fun _ => j, k)).val * (X.presheaf.map (homOfLE h3).op).hom (s l' k)
  have ha : ∀ {Y : Scheme.{0}} (g : Y ⟶ X) (y : Y) (hy : g y ∈ U') (l' : Fin d),
      gs g y U' (a l') = gs (g ≫ φ) y (O ⊓ L.U j) (s l' j) -
        (gm g y ((L.pull φ).U (fun _ => j) ⊓ L.U k) (w.s (fun _ => j, k))).val * gs g y (O ⊓ L.U k) (s l' k) := by
    intro Y g y hy l'
    have e1 : gs g y U' ((X.presheaf.map (homOfLE h1).op).hom ((φ.app (O ⊓ L.U j)).hom (s l' j))) =
        gs (g ≫ φ) y (O ⊓ L.U j) (s l' j) :=
      (gs_res g y h1 hy _).trans (gs_pull g φ y (O ⊓ L.U j) (h1 hy) _)
    have e2 : gs g y U' ((X.presheaf.map (homOfLE h2).op).hom (w.s (fun _ => j, k)).val) =
        (gm g y ((L.pull φ).U (fun _ => j) ⊓ L.U k) (w.s (fun _ => j, k))).val :=
      (gs_res g y h2 hy _).trans (gs_unit g y _ (h2 hy) _)
    have e3 : gs g y U' ((X.presheaf.map (homOfLE h3).op).hom (s l' k)) = gs g y (O ⊓ L.U k) (s l' k) :=
      gs_res g y h3 hy _
    rw [gs_sub' g y U' hy, gs_mul g y U' hy, e1, e2, e3]
  have hxU : x ∈ U' := ⟨⟨⟨hxO, hxk⟩, hφxO, hφxj⟩, mem_pull.2 hφxj, hxk⟩
  have key := huniq U' a x hxU (by
    intro z hz
    have hzU : q z ∈ U' := hz ▸ hxU
    have hzO : q z ∈ O := hz ▸ hxO
    have hzk : q z ∈ L.U k := hz ▸ hxk
    have hzW : z ∈ q ⁻¹ᵁ W := hOW hzO
    have hf'zO : q (f' z) ∈ O := by rw [hpt, hz]; exact hφxO
    have hf'zj : q (f' z) ∈ L.U j := by rw [hpt, hz]; exact hφxj
    have hmj : q (f' z) ∈ O ⊓ L.U j := ⟨hf'zO, hf'zj⟩
    have hmWj : f' z ∈ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U j := ⟨hOW hf'zO, hf'zj⟩
    have hmWk : (𝟙 Z) z ∈ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k := ⟨hzW, hzk⟩
    have hcz := hcar z j k hzW (hOW hf'zO) hzk hf'zj
    have S1 : ∑ l', gs p₁ z ⊤ (B l') * gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) =
        (gm f' z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U j) (τ j)).val := by
      have e1 : ∀ l', gs p₁ z ⊤ (B l') = (f'.stalkMap z).hom (gs p₁ (f' z) ⊤ (B l')) := fun l' => by
        conv_lhs => rw [← hf'p]
        exact gs_comp_map f' p₁ z ⊤ trivial _
      have e2 : ∀ l', gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) = (f'.stalkMap z).hom (gs q (f' z) (O ⊓ L.U j) (s l' j)) :=
        fun l' => by rw [← hf'q]; exact gs_comp_map f' q z _ hmj _

      simp only [e1, e2, ← map_mul, ← map_sum]
      rw [← hdec (f' z) j hf'zO hf'zj, ← gs_eq_map_gs f' z _ hmWj, gs_unit f' z _ hmWj]
    have S3 := hdec z k hzO hzk
    rw [gs_unit (𝟙 Z) z _ hmWk] at S3
    have e4 : ∀ l', gs p₁ z ⊤ (B l') * gs q z U' (a l') =
        gs p₁ z ⊤ (B l') * gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) -
          (gw w q z j k).val * (gs p₁ z ⊤ (B l') * gs q z (O ⊓ L.U k) (s l' k)) := fun l' => by
      rw [ha q z hzU l', gw]; ring
    rw [Finset.sum_congr rfl (fun l' _ => e4 l'), Finset.sum_sub_distrib, ← Finset.mul_sum, S1, ← S3, hcz,
      Units.val_mul, sub_self])
  have e := key l
  rw [ha (𝟙 X) x hxU l, Category.id_comp, sub_eq_zero] at e
  exact e

theorem secCarriedOver_of_frameCarriedAlong : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X) (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)), φ ≫ f = f → (∀ f' : (pullback f (spMap ρ₁)) ⟶ (pullback f (spMap ρ₁)), f' ≫ (pullback.fst f (spMap ρ₁)) = (pullback.fst f (spMap ρ₁)) ≫ φ → f' ≫ (pullback.snd f (spMap ρ₁)) = (pullback.snd f (spMap ρ₁)) → FrameCarriedAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ φ w f') → ∀ l, SecCarriedOver L O (s l) φ w := by
  intro R R₁ _ _ ρ₁ d b hb X f L W O hOW τ s hdec φ w hφ hcar l
  have hcond : (pullback.fst f (spMap ρ₁) ≫ φ) ≫ f = pullback.snd f (spMap ρ₁) ≫ spMap ρ₁ := by
    rw [Category.assoc, hφ, pullback.condition]
  have hf'q : pullback.lift _ _ hcond ≫ pullback.fst f (spMap ρ₁) = pullback.fst f (spMap ρ₁) ≫ φ :=
    pullback.lift_fst _ _ _
  have hf'p : pullback.lift _ _ hcond ≫ pullback.snd f (spMap ρ₁) = pullback.snd f (spMap ρ₁) :=
    pullback.lift_snd _ _ _
  exact secCarriedOver_of_lift (pullback.fst f (spMap ρ₁)) (pullback.snd f (spMap ρ₁)) L W O hOW τ d
    (fun l => (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) s hdec
    (fun U a x hx hz => GlobalTheory.T.coefficient_germs_zero_finiteFree_baseChange R R₁ ρ₁ d b hb X f U a x hx hz) φ w _ hf'q hf'p (hcar _ hf'q hf'p) l

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_generator_corrected_torusCoordinate_ratio : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)), w.IsGen → ∀ (χ₂ : D₂.X) (χ : D.X), D₂.c χ₂ ≫ β = D.c χ → ∀ h : (thickObj R I e G).left ⟶ (thickObj R I e G).left, h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ g.pG.left = g₂.pG.left ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b 0 → ∃ u : LB.Gen (LB.LinComb D.P.L (fun k => g.q.left ≫ GlobalTheory.CoordCompare.diffφ (D.prBe I e) (D.c χ) (D.c χ) k) ![1, -1, 1, -1]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → val u r z J = val (g.t χ) (r ≫ h) z J * ((∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' * val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ := by
  first | exact @GlobalTheory.MumCmp.TranslRatio.exists_ratio_gen | exact GlobalTheory.MumCmp.TranslRatio.exists_ratio_gen | (intros; apply GlobalTheory.MumCmp.TranslRatio.exists_ratio_gen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_carriedFrame_theoremOfCube : ∀ {S : Scheme.{0}} (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (L : RigLB G') (c : CubicalStr G' L) (θ : L.L.Sec) (T : Over S) (x a b c' : T ⟶ G') (W : T.left.Opens), (∀ g ∈ cubeTen x a b c', W ≤ g.left ⁻¹ᵁ secNz θ) → ∃ τ : ∀ k : L.L.ι, Γ(T.left, W ⊓ x.left ⁻¹ᵁ L.L.U k)ˣ, FrameAlong L.L x.left W τ ∧ ∀ (f : G'.left ⟶ G'.left) (fS : S ⟶ S) (hc : IsGrpPullback G' G' fS f) (w : LB.Iso L.L (L.L.pull f)), w.IsGen → PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) L.rig L.rig fS → PMaps w (thφ G' (x3 G')) (thφ G' (x3 G')) thε c.t c.t (cubeMapOf hc).F3 → SecCarried L.L θ f w → ∀ hT : T.left ⟶ T.left, hT ≫ T.hom = T.hom ≫ fS → x.left ≫ f = hT ≫ x.left → a.left ≫ f = hT ≫ a.left → b.left ≫ f = hT ≫ b.left → c'.left ≫ f = hT ≫ c'.left → FrameCarriedAlong L.L x.left W τ f w hT := by
  first | exact @GlobalTheory.Mum.exists_carried_frame_of_cubeTen | exact GlobalTheory.Mum.exists_carried_frame_of_cubeTen | (intros; apply GlobalTheory.Mum.exists_carried_frame_of_cubeTen <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke.TateTransl

section Ev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {κ : Type} [Field κ] {Q : Type} [Group Q] {act : D.O → Q → Q}
  {e : ℕ → Q → Q → κˣ → Prop} (I : TateIsoO D κ Q act e)

theorem ev_zero (n : ℕ) : I.ev n 0 = 1 := by
  have h := I.add n 0 0
  rw [add_zero] at h
  simpa using h

theorem ev_nsmul (n j : ℕ) (w : D.La) : I.ev n (j • w) = I.ev n w ^ j := by
  induction j with
  | zero => rw [zero_smul, ev_zero, pow_zero]
  | succ j ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem ev_neg (n : ℕ) (w : D.La) : I.ev n (-w) = (I.ev n w)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← I.add, neg_add_cancel, ev_zero])

theorem ev_eq_iff (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (w w' : D.La) :
    I.ev n w = I.ev n w' ↔ ∃ y, w - w' = n • y := by
  rw [← I.ker n hn hnp, sub_eq_add_neg, I.add, ev_neg, mul_inv_eq_one]

theorem ev_mul_nsmul (n j : ℕ) (hn : 0 < n) (hj : 0 < j) (hc : (j * n).Coprime p) (w : D.La) :
    I.ev (n * j) (n • w) = I.ev j w := by
  rw [ev_nsmul, mul_comm n j, I.tower j n hj hn hc]

end Ev

theorem one_comp_transl_pt {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (h : 𝟙_ (Over S) ⟶ A) :
    (1 : T ⟶ A) ≫ transl h = toUnit T ≫ h := by
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique ((1 : T ⟶ A) ≫ toUnit A) (toUnit T),
    _root_.one_mul]

theorem exists_tateIsoO_transl : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c) (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta (g y) ≫ ψ) = I.ev N y := by
  intro p _ D R _ b g c k N hcp hkp hN hNp hEF hg hck S s o A' _ _ act' ψ hA' hψ hGal hact P' hP' r₁ r₂ hiso κ _ _ x β hx
  obtain ⟨I, hI⟩ := o.geom κ x β hx
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have kpos : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; rw [Nat.coprime_zero_left] at hkp; omega
  have cpos : 0 < c := Nat.pos_of_ne_zero fun h => by subst h; rw [Nat.coprime_zero_left] at hcp; omega
  have Npos : 0 < N := by omega
  haveI := D.freeLa
  let Ψ : (Over.mk x ⟶ o.A) →* (Over.mk x ⟶ A') :=
    MonoidHom.mk' (fun t => t ≫ ψ) (fun a a' => MonObj.mul_comp a a' ψ)
  have hΨ : ∀ t, Ψ t = t ≫ ψ := fun _ => rfl
  have ginj : Function.Injective g := by
    intro u v huv
    have h0 : D.EF (u - v) = 0 := by
      ext w
      have e := hEF (u - v) w
      rw [map_sub, huv, sub_self, map_zero, LinearMap.zero_apply] at e
      rw [LinearMap.zero_apply]
      exact (mul_eq_zero.1 e.symm).resolve_left (by exact_mod_cast cpos.ne')
    have := D.nondeg (h0.trans (map_zero D.EF).symm)
    exact sub_eq_zero.1 this
  have hlev : ∀ n, 0 < n → n.Coprime p → ∀ w, I.ev (n * k) (n • w) = I.ev k w := fun n hn hnp w =>
    ev_mul_nsmul I n k hn kpos (Nat.Coprime.mul_left hkp hnp) w
  have hker : ∀ t : Over.mk x ⟶ o.A, t ≫ ψ = 1 ↔ ∃ z, t = I.ev (N * k) (N • g z) := by
    intro t
    constructor
    · intro ht
      have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
        rw [← Over.comp_left, ← Over.comp_left, ht, MonObj.one_comp]
      obtain ⟨h, hh, -⟩ := hGal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
      obtain ⟨z, hz⟩ := h.2
      refine ⟨z, ?_⟩
      have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl h.1 := Over.OverMorphism.ext (by rw [Over.comp_left]; exact hh.symm)
      rw [e2, one_comp_transl_pt, hz, hI]
    · rintro ⟨z, rfl⟩
      rw [← hI, Category.assoc, comp_eq_one_of_transl ψ (o.eta (N • g z)) (hGal.inv ⟨_, mem_heckeSub o g N z⟩),
        MonObj.comp_one]
  have ker' : ∀ n, 0 < n → n.Coprime p → ∀ y, I.ev (n * k) (g y) ≫ ψ = 1 ↔ ∃ z, y = n • z := by
    intro n hn hnp y
    rw [hker]
    constructor
    · rintro ⟨z, hz⟩
      rw [hlev N Npos hNp, ← hlev n hn hnp] at hz
      obtain ⟨w, hw⟩ := (ev_eq_iff I (n * k) (Nat.mul_pos hn kpos) (Nat.Coprime.mul_left hnp hkp) _ _).1 hz
      obtain ⟨w', hw'⟩ := hg w
      refine ⟨z + w', ginj ?_⟩
      rw [map_nsmul, map_add (f := _), hw', smul_add, smul_smul, ← sub_eq_iff_eq_add', hw]
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [map_nsmul, hlev n hn hnp, hlev N Npos hNp]⟩

  have htor : ∀ n, 0 < n → n.Coprime p → ∀ y, (I.ev (n * k) (g y) ≫ ψ) ^ n = 1 := by
    intro n hn hnp y
    rw [← hΨ, ← map_pow, hΨ, ← ev_nsmul, ← map_nsmul]
    exact (ker' n hn hnp (n • y)).2 ⟨y, rfl⟩
  have onto' : ∀ n, 0 < n → n.Coprime p → ∀ q : Over.mk x ⟶ A', q ^ n = 1 ↔ ∃ y, I.ev (n * k) (g y) ≫ ψ = q := by
    intro n hn hnp q
    constructor
    · intro hq
      haveI := hGal.fin
      haveI := hGal.onto
      obtain ⟨a₀, ha₀⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left q.left
      let a : Over.mk x ⟶ o.A := Over.homMk a₀ (by
        show a₀ ≫ o.A.hom = x
        rw [← Over.w ψ, ← Category.assoc, ← ha₀, Over.w q]; rfl)
      have ha : a ≫ ψ = q := Over.OverMorphism.ext (by rw [Over.comp_left]; exact ha₀.symm)
      have han : (a ^ n) ≫ ψ = 1 := by rw [← hΨ, map_pow, hΨ, ha, hq]
      obtain ⟨z, hz⟩ := (hker _).1 han
      rw [hlev N Npos hNp, ← hlev n hn hnp] at hz
      have hnk : 0 < n * k := Nat.mul_pos hn kpos
      have hnkp : (n * k).Coprime p := Nat.Coprime.mul_left hnp hkp
      have hak : a ^ (n * k) = 1 := by
        rw [pow_mul, hz, ← ev_nsmul, I.ker _ hnk hnkp]
        exact ⟨g z, by rw [smul_smul, mul_comm]⟩
      obtain ⟨w, hw⟩ := (I.onto _ hnk hnkp a).1 hak
      rw [← hw, ← ev_nsmul, ev_eq_iff I _ hnk hnkp] at hz
      obtain ⟨v, hv⟩ := hz
      have e1 : n • (w - g z - k • v) = 0 := by rw [smul_sub, smul_sub, smul_smul, ← hv, sub_self]
      have e2 : w - g z - k • v = 0 := by
        have e3 : ((n : ℤ)) • (w - g z - k • v) = 0 := by rw [natCast_zsmul]; exact e1
        exact (smul_eq_zero.1 e3).resolve_left (by exact_mod_cast hn.ne')
      have e4 : w = g z + k • v := by rw [sub_sub, sub_eq_zero] at e2; exact e2
      obtain ⟨v', hv'⟩ := hg v
      refine ⟨z + v', ?_⟩
      rw [map_add (f := _), hv', ← e4, hw, ha]
    · rintro ⟨y, rfl⟩
      exact htor n hn hnp y

  have hnκ : ∀ n : ℕ, n.Coprime p → (n : κ) ≠ 0 := fun n hnp => by
    have h := (b.unit n hnp).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have hiso2 : LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (k ^ 2 / c))
      ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb (pull_isLB o.isLB _) _ _) (pull_isLB (pull_isLB hP' _) _)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow (pull_isLB o.isLB _), GlobalTheory.CechPic.cls_pull o.isLB, GlobalTheory.CechPic.cls_pull (pull_isLB hP' _),
      GlobalTheory.CechPic.cls_pull hP', ← GlobalTheory.CechPic.pull_comp]
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB hP' _)).2 hiso
    rw [GlobalTheory.CechPic.cls_linComb o.isLB, GlobalTheory.CechPic.cls_pull hP'] at h1
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift (𝟙 o.A) (𝟙 o.A)).left) h1
    rw [map_nsmul, ← GlobalTheory.CechPic.pull_comp] at h2
    rw [h2]
    congr 1
    simp only [sq2, ← Over.comp_left, comp_lift, Category.id_comp, lift_fst_assoc, lift_snd_assoc, Category.comp_id]
  refine ⟨⟨I.ζ, I.ζ_prim, I.ζ_pow, fun n y => I.ev (n * k) (g y) ≫ ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun y => ?_⟩
  · intro n y y'
    rw [map_add (f := _), I.add, MonObj.mul_comp]
  · intro n b' y
    rw [map_smul, I.lin, Category.assoc, hact, ← Category.assoc]
  · exact fun n hn hnp y => ker' n hn hnp y
  · exact fun n hn hnp q => onto' n hn hnp q
  · intro n m hn hm hnm y
    rw [← hΨ, ← map_pow, hΨ, Nat.mul_right_comm n m k, I.tower (n * k) m (Nat.mul_pos hn kpos) hm
      (by rw [Nat.mul_right_comm]; exact Nat.Coprime.mul_left hnm hkp)]
  · intro n hn hnp u v
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_weilCommutatorPairing_torsion_geometricPoint S A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) hA' (pull_isLB hP' _) κ x n hn (hnκ n hnp) _ _
      (htor n hn hnp u) (htor n hn hnp v)
    have h2 := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds o.ab (pull_isLB o.isLB _) (pull_isLB hP' _) ψ hiso2 he
    have h3 := GlobalTheory.T.commutatorPairing_heckeTranslate_eq_zeta p D R b g c k (N * k) hcp hkp hEF hg hck S s o κ x β hx I n hn hnp u v e
      (by rw [Nat.cast_mul]; exact h2)
    rw [h3] at he
    exact he
  · show toUnit _ ≫ (o.eta (g y) ≫ ψ) = I.ev (N * k) (g y) ≫ ψ
    rw [← Category.assoc, hI]

end GlobalTheory.UPel.HT.Hecke.TateTransl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.exists_bimultiplicative_weilPairing_torsion_axes : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (c : ℕ), (c : κ) ≠ 0 → ∃ e : (Over.mk x ⟶ A) → (Over.mk x ⟶ A) → κˣ, (∀ g g' : Over.mk x ⟶ A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') u ↔ u = unitOn (e g g')) ∧ (∀ g₁ g₂ g' : Over.mk x ⟶ A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 → e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧ (∀ g g₁ g₂ : Over.mk x ⟶ A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 → e g (g₁ * g₂) = e g g₁ * e g g₂) := by
  first | (exact @GlobalTheory.TorsionCommPairing.exists_pairing) | (exact GlobalTheory.TorsionCommPairing.exists_pairing) | (intros; apply GlobalTheory.TorsionCommPairing.exists_pairing  <;> assumption)
end
