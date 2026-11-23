module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramesRespectCubicalStructures
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2996
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle196
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
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

open GlobalTheory.Poinc.Tors

theorem _root_.GlobalTheory.T.integral_frames_respect_cubical_structures : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (h : Finset (Fin 3) → ((𝟙_ (Over (Sp V))) ⟶ G)) (g : Finset (Fin 3) → GtPt D.toPre (𝟙_ (Over (Sp V)))) (f : ∀ S, LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => (h S).left) (fun _ => 1))) (t : ∀ S, LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, ((g S).b).left] (DegPre.lineε 1))), h ∅ = 1 → h {0, 1} = h {0} * h {1} → h {0, 2} = h {0} * h {2} → h {1, 2} = h {1} * h {2} → h {0, 1, 2} = h {0} * h {1} * h {2} → (g ∅).b = 1 → (g {0, 1}).b = (g {0}).b * (g {1}).b → (g {0, 2}).b = (g {0}).b * (g {2}).b → (g {1, 2}).b = (g {1}).b * (g {2}).b → (g {0, 1, 2}).b = (g {0}).b * (g {1}).b * (g {2}).b → (∀ S, GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre (h S) (g S)) → (∀ S, (f S).IsGen) → (∀ S, (t S).IsGen) → (∀ S (e : ℕ), GlobalTheory.Poinc.IntEval.TRel U.toUnifPre (h S) (g S).b (f S) (t S) e) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good U.LG.L z JG → Good D.toPre.P.L z JB → (val (f {0, 1, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {0}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {1}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {2}) (toUnit (TF (R := V) (FractionRing V))).left z JG) * (val (t {0, 1, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {0}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {1}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {2}) (toUnit (TF (R := V) (FractionRing V))).left z JB) * cubV D.toPre.cub z JB ((toUnit (TF (R := V) (FractionRing V))) ≫ (g {0}).b) ((toUnit (TF (R := V) (FractionRing V))) ≫ (g {1}).b) ((toUnit (TF (R := V) (FractionRing V))) ≫ (g {2}).b) = cubV U.cubG z JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}) * (val (f {0, 1}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {0, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {1, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f ∅) (toUnit (TF (R := V) (FractionRing V))).left z JG) * (val (t {0, 1}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {0, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {1, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t ∅) (toUnit (TF (R := V) (FractionRing V))).left z JB) := by
  first | exact @GlobalTheory.Poinc.IntCube.integral_cube | exact GlobalTheory.Poinc.IntCube.integral_cube | (intros; apply GlobalTheory.Poinc.IntCube.integral_cube <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SecDiv

theorem resTop_map {Y : Scheme.{0}} {V W : Y.Opens} (h : W ≤ V) (c : Γ(Y, ⊤)) :
    (Y.presheaf.map (homOfLE h).op).hom (ReciprocityTheory.ChartRestriction.G.Out.resTop V c) = ReciprocityTheory.ChartRestriction.G.Out.resTop W c := by
  unfold ReciprocityTheory.ChartRestriction.G.Out.resTop
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_secIsMul {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {L : LB Y}
    (a : R) (τ : LB.Sec L) : ∃ σ : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p a σ τ := by
  unfold ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul
  refine ⟨⟨fun j => ReciprocityTheory.ChartRestriction.G.Out.resTop (L.U j) (scal p a) * τ.f j, fun i j => ?_⟩, fun j => rfl⟩
  simp only [map_mul, resTop_map]
  rw [τ.2 i j]
  ring

theorem exists_expT_of_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 → U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∃ τ : U.SecGT (𝟙_ _) 1, U.ExpT (𝟙_ _) 1 τ g := by
  intro R _ _ _ hB D A G _ _ U σ f g q hq hσ hfg
  have hB' : AdmBase R (maximalIdeal R) ∧ CharZero R := hB
  have h1 : IsNoetherianRing R ∧ IsDomain R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R := hB'.1
  obtain ⟨hN, -, hIC, hC⟩ := h1
  haveI := hN
  haveI := hIC
  have hs := U.semi
  haveI := hs.smooth
  haveI := hs.geomConnected
  haveI : IsIso (λ_ G).hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso (λ_ G)).hom)
  have hSm : Smooth (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    rw [← Over.w (λ_ G).hom]
    infer_instance
  have hGC : GeometricallyConnected (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    have hsq : IsPullback (λ_ G).hom.left (𝟙_ (Over (Sp R)) ⊗ G).hom G.hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq inferInstance
  have he : (η[G].left ≫ (λ_ G).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ G).hom = 𝟙 _ := by
    simp only [Category.assoc, Over.w]
    rfl
  have hLB : (LB.LinComb U.P.L.L (K := Fin 1) (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left)
      (fun _ => ((1 : ℕ) : ℤ))).IsLB := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U.P.L.isLB _ _
    | exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ _ _
  have hloc := GlobalTheory.T.germ_dvd_of_sectionExpansion_dvd_closedFibre R hB D A G U σ f g q hσ hfg
  have hall := GlobalTheory.T.lineBundle_section_dvd_everywhere_smooth_connected_fibres R _ (𝟙_ (Over (Sp R)) ⊗ G).hom hSm hGC _ he _ hLB σ q hq hloc
  have hflat : Flat (𝟙_ (Over (Sp R)) ⊗ G).hom := inferInstance
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_baseMul_section_of_germ_dvd_flat_domain R _ (𝟙_ (Over (Sp R)) ⊗ G).hom hflat _ σ q hq hall
  have hEga : GlobalTheory.LN.AlgSt ∧ GlobalTheory.LN.MorAlgSt ∧ GlobalTheory.LN.SecAlgSt ∧ GlobalTheory.LN.PicardZeroDegenerationCondition := GlobalTheory.LN.ega_holds
  obtain ⟨h, hh⟩ := GlobalTheory.CompleteBaseExpansion.exists_expT hEga.2.2.1 hC U 1 τ
  choose f' hf' using fun α => exists_secIsMul (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom q (h α)
  have hσf' : U.ExpT (𝟙_ _) 1 σ f' := GlobalTheory.T.sectionExpansion_scale_base_element R (maximalIdeal R) D A G U 1 q σ τ f' h hτ hf' hh
  have hjac : maximalIdeal R ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hff' : f' = f := GlobalTheory.CompleteBaseExpansion.expT_unique hjac U 1 σ f' f hσf' hσ
  have hflatD : Flat (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom := by
    haveI : IsIso (λ_ D.P.A).hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso (λ_ D.P.A)).hom)
    haveI : Smooth D.P.A.hom := D.P.isAb.smooth
    rw [← Over.w (λ_ D.P.A).hom]
    infer_instance
  have hhg : h = g := by
    funext α
    have hfa := hf' α
    rw [hff'] at hfa
    exact GlobalTheory.T.lineBundleSection_baseMul_cancel_flat_domain R _ _ hflatD _ q hq (f α) (h α) (g α) hfa (hfg α)
  refine ⟨τ, ?_⟩
  rw [← hhg]
  exact hh

end GlobalTheory.SecDiv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegUniqAny

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.PullDegUniq
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nonempty_isPullDeg_id {φ : R →+* R'} {D : DegPre R} {D₁ D₂ : DegPre R'} (h₁ : IsPullDeg φ D D₁)
    (h₂ : IsPullDeg φ D D₂) : Nonempty (IsPullDeg (RingHom.id R') D₁ D₂) := by
  have hβ : Function.Injective (RingHom.id R') := Function.injective_id
  have h : IsPullDeg ((RingHom.id R').comp φ) D D₂ := (RingHom.id_comp φ).symm ▸ h₂
  have p₁ : IsGrpPullback D₁.P.A D.P.A (spMap φ) (proj h₁) := pull_grp h₁
  have sc : spMap (RingHom.id R') ≫ spMap φ = spMap ((RingHom.id R').comp φ) := (spMap_comp φ _).symm
  have p : IsGrpPullback D₂.P.A D.P.A (spMap (RingHom.id R') ≫ spMap φ) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D₂.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧
      Φ ≫ D₁.P.A.hom = D₂.P.A.hom ≫ spMap (RingHom.id R') :=
    ⟨p₁.1.lift (proj h) (D₂.P.A.hom ≫ spMap (RingHom.id R')) (p.1.w.trans (Category.assoc _ _ _).symm),
      p₁.1.lift_fst _ _ _, p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D₂.P.A D₁.P.A (spMap (RingHom.id R')) Φ :=
    IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D.P.isLB D₁.P.isLB D₂.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D₂.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D₂.c x).left ≫ Φ = spMap (RingHom.id R') ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW⟩ := nonempty_psiOn_pull h₁
  obtain ⟨s, hs⟩ := exists_generic_section h₁
  obtain ⟨hD, -⟩ := DvrDeg.exists_isPullDeg_of_val hβ D₁ D₂ ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D.P.isLB z
    have sβ : jK R' ≫ spMap (RingHom.id R') = genMap hβ ≫ jK R' :=
      (Category.id_comp _).symm.trans (fracMap_sq hβ)
    have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ₀ hJ
    have v₁ := PsiEvenPull.psi_pull h₁ (xe x) (genMap hβ) z hJ₀ hJ₁
    have ag : val (h₁.psiW.psi (h.xe x)) (genMap hβ ≫ h₁.g) z J₀ = val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J₀ :=
      ArcSpecialise.psiOn_agree h₁.psiW h.psiW _ _ _ (by
        rw [Category.assoc, h₁.g_comm, Category.assoc, h.g_comm, Category.id_comp, ← Category.assoc, ← sβ,
          Category.assoc]
        exact congrArg (jK R' ≫ ·) sc) hJ₀
    have hx : D₂.xK x ≫ Φ = genMap hβ ≫ D₁.xK (xe x) := by
      show (jK R' ≫ (D₂.c x).left) ≫ Φ = genMap hβ ≫ jK R' ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    change _ = (om h₁.w z J₀ J₁ (genMap hβ ≫ D₁.xK (xe x)))⁻¹ * _ at v₁
    change _ = (om h.w z J₀ J (𝟙 _ ≫ D₂.xK x))⁻¹ * _ at v
    rw [hxe, ag, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD⟩

end GlobalTheory.PullDegUniqAny

namespace GlobalTheory.Mum

theorem isPullDeg_unique_any : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D₁ D₂ : DegPre R'), Nonempty (IsPullDeg φ D D₁) → Nonempty (IsPullDeg φ D D₂) → Nonempty (IsPullDeg (RingHom.id R') D₁ D₂) :=
  fun _ _ _ _ _ _ _ _ _ _ ⟨h₁⟩ ⟨h₂⟩ => GlobalTheory.PullDegUniqAny.nonempty_isPullDeg_id h₁ h₂

end GlobalTheory.Mum
end
end
