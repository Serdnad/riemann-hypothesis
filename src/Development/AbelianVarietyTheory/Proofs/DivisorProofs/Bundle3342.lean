module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle043
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3228
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

theorem exists_lb_of_generated_system_proper : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → (∀ e, ⨆ i, nonzeroLocus (s e i) = ⊤) → ∃ (M : LB X.left) (s' : Fin (n + 1) → LB.Sec M) (w : ∀ e, LB.Iso (H e) (M.pull (b e))), M.IsLB ∧ ∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j) := by
  intro R _ _ I hcI X hX Y β b hb hbb H v hH n s hs hgen
  obtain ⟨P, f, O, t, hO, hva, hP⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal R n ⊥ (fun F hF d => by
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  choose c w hc' hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy R P f O n t hO hva _
    ((Y e).hom ≫ thick R I e) (H e) (s e) (hH e).1 (hgen e) (fun d F hF h k => by
      obtain ⟨m, hm⟩ := (hP d F hF).1 h 0
      have : F = 0 := by
        rw [Ideal.mem_bot] at hm
        exact ((MvPolynomial.isRegular_X (n := (0 : Fin (n + 1)))).pow m).left (by simpa using hm)
      rw [this, map_zero])
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := fun e => by
    rw [← (hb (e + 1)).w, ← Category.assoc, hbb, (hb e).w]
  have hcc : ∀ e, β e ≫ c (e + 1) = c e := fun e => by
    have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hO (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections R P f O n t hO hva _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hc', hc', c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
  haveI hPp : IsProper f := GlobalTheory.AbLaw.isProper_of_isProjBy R P f ⟨O, hO, n, t, hva⟩
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.formalAlgebraisation_morphisms' R I hcI X (Over.mk f) hX (inferInstanceAs (IsSeparated f))
    (inferInstanceAs (LocallyOfFiniteType f)) (inferInstanceAs (QuasiCompact f)) Y β b hb hbb
    c hc' hcc
  have hM : (O.pull g.left).IsLB := LB.isLB_pull hO _
  obtain ⟨s', hs'⟩ := GlobalTheory.MorAlg.exists_isPull g.left hO t
  have key : ∀ e, GlobalTheory.MorAlg.IsPull (b e) s' (s e) := fun e =>
    GlobalTheory.MorAlg.IsPull.cancel hO hM (hH e).1 hs' (by rw [hg e]; exact ⟨w e, hw e, hr e⟩)
  choose w' hw' cw using key
  exact ⟨O.pull g.left, s', w', hM, fun e => ⟨hw' e, fun j => cw e j⟩⟩

end GlobalTheory.FormalAlg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

theorem resG_resG' {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (f : Γ(X, U)) :
    resG X h₂ (resG X h₁ f) = resG X (h₂.trans h₁) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem chart_sec (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G))
    (hn : Geo.Tor.IsNormalScheme M.Z) (ho : Odd m) (h3 : 3 ≤ m) (hu : IsUnit (m : k)) (hp : PolFib t.G t.PP.L g M.pt)
    (hg : IsGenSec t.G t.PP.L _ θ) (hl : ThList t.G t.PP.L t.PP.rig m M.pt θ pt c) (hc : PCrd (M.pt ≫ h) c)
    (a : Fin (n + 1)) : ∃ s : LocSec t.G t.PP.L (h ⁻¹ᵁ chart k n a), IsLocSec s ∧
      ((((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ)) ∧
      FibNz s (h ⁻¹ᵁ chart k n a)) := by
  by_cases hne : ((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty
  · have hloc := GlobalTheory.T.exists_localSection_thetaQuotient_projChart E H k Ω M t g m n c h θ pt hn ho h3 hu hp hg hl hc a
    choose N hzN hNle s hs hgs hfs using hloc
    let κ := {z : M.Z // z ∈ h ⁻¹ᵁ chart k n a}
    have hsup : (⨆ z : κ, N z.1 z.2) = h ⁻¹ᵁ chart k n a :=
      le_antisymm (iSup_le fun z => hNle z.1 z.2) fun z hz =>
        TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzN z hz⟩
    obtain ⟨s', hs', hres⟩ := GlobalTheory.T.exists_glued_lineBundleSection_over_cover M.Z t.G t.PP.L (h ⁻¹ᵁ chart k n a) κ (fun z => N z.1 z.2) (fun z => s z.1 z.2)
      (fun z => hNle z.1 z.2) hsup (fun z => hs z.1 z.2) (fun z z' i =>
        GlobalTheory.T.lineBundleLocalSection_eq_of_generic_fibre M.Z t.G t.semi t.PP.L Ω M.pt M.gen _ _ _ _ _ (hgs z.1 z.2) (hgs z'.1 z'.2) i)
    obtain ⟨h1, h2⟩ := GlobalTheory.T.glued_section_generic_value_nonvanishing M.Z t.G t.PP.L Ω M.pt _ κ (fun z => N z.1 z.2) (fun z => s z.1 z.2) s' _
      (fun z => hNle z.1 z.2) hsup hres (fun z => hgs z.1 z.2) (fun z => hfs z.1 z.2)
    exact ⟨s', hs', fun _ => h1 ⟨⟨hne.some, hne.some_mem⟩⟩, h2⟩
  · refine ⟨0, isLocSec_zero, fun h' => absurd h' hne, fun K _ _ x hx => absurd ?_ hne⟩
    exact ⟨_, hx ⟨IsLocalRing.closedPoint K, rfl⟩⟩

end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

theorem app_resG {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (e : V ≤ U) (x : Γ(X, U)) :
    (f.app V).hom (resG X e x) = resG Y (fun _ hy => e hy : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) ((f.app U).hom x) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, f.naturality]
  rfl

theorem valF_resG {F : Type} [Field F] {X : Scheme.{0}} (y : Sp F ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (hV : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(X, U)) : valF y V (resG X e f) = valF y U f := by
  unfold valF
  rw [dite_eq_left hV, dite_eq_left (hV.trans fun x hx => show y x ∈ U from e (show y x ∈ V from hx))]
  congr 1
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl

theorem val_res' {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res e u : Γ(X, V)ˣ) : Γ(X, V)) = resG X e (u : Γ(X, U)) := rfl

theorem val_pullU' {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (u : Γ(X, U)ˣ) :
    ((pullU f U u : Γ(Y, f ⁻¹ᵁ U)ˣ) : Γ(Y, f ⁻¹ᵁ U)) = (f.app U).hom (u : Γ(X, U)) := rfl
end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl
open ProjSpace



theorem pull_theta_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n), Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt → HasTh t.G t.PP.L t.PP.rig m M.pt c → PCrd (M.pt ≫ h) c → ∃ σ : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).Sec, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), ∃ (y : Sp K ⟶ t.G.left) (j : _), y ≫ t.G.hom = x ∧ Set.range y ⊆ (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U j ∧ valF y _ (σ.f j) ≠ 0 := by
  intro E _ _ _ H k Ω _ _ _ _ _ M t g m n c h hn ho h3 hu hp hth hc
  obtain ⟨θ, pt, hg, hl⟩ := hth
  choose s hs hgs hfs using chart_sec E H k Ω M t g m n c h θ pt hn ho h3 hu hp hg hl hc
  have hcross := GlobalTheory.T.localThetaSections_ratio_coordinates_overlap k Ω M t.G t.PP.L n c h (SecM.ofSec t.G θ) hc (GlobalTheory.T.lineBundleLocalSection_eq_of_generic_fibre M.Z t.G t.semi t.PP.L Ω M.pt M.gen)
  have hle : ∀ p : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).ι,
      (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U p ≤
        t.PP.L.U p.1 ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n (p.2 PUnit.unit PUnit.unit)) := fun p y hy =>
    ⟨hy.1, Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩
  refine ⟨⟨fun p => resG _ (hle p) (s _ p.1), fun p q => ?_⟩, fun K _ _ x => ?_⟩
  · obtain ⟨i, pj⟩ := p
    obtain ⟨i', qj⟩ := q
    have eB : ∀ (Y : Scheme.{0}) (φ : Y ⟶ M.Z) (u v : PUnit → PUnit → Fin (n + 1)),
        ((((ProjSpace.O1 k n).pull h).pull φ).g u v : Γ(Y, _)) =
          resG Y (fun y hy => ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 PUnit.unit) PUnit.unit,
              Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩ :
            (((ProjSpace.O1 k n).pull h).pull φ).U u ⊓ (((ProjSpace.O1 k n).pull h).pull φ).U v ≤
              φ ⁻¹ᵁ (h ⁻¹ᵁ (chart k n (u PUnit.unit PUnit.unit) ⊓ chart k n (v PUnit.unit PUnit.unit))))
            ((φ.app _).hom ((h.app _).hom (ratioOn (chart k n (u PUnit.unit PUnit.unit) ⊓
              chart k n (v PUnit.unit PUnit.unit)) _ inf_le_left (v PUnit.unit PUnit.unit)))) := by
      intro Y φ u v
      have e1 := ProjSpace.linComb_punit_g ((ProjSpace.O1 k n).pull h) φ 1 u v
      have e2 := ProjSpace.linComb_punit_g (ProjSpace.O1 k n) h 1 (u PUnit.unit) (v PUnit.unit)
      rw [zpow_one] at e1 e2
      erw [e1]
      erw [e2]
      erw [val_res', val_pullU', val_res', val_pullU']
      rw [O1_g_eq_ratioUnit_chart_inf, val_ratioUnit]
      erw [app_resG, resG_resG']
      rfl
    have hW1 : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i, pj) ⊓
        (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i', qj) ≤
        t.PP.L.U i ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n (pj PUnit.unit PUnit.unit) ⊓ chart k n (qj PUnit.unit PUnit.unit))) :=
      fun y hy => ⟨hy.1.1, (hle _ hy.1).2, (hle _ hy.2).2⟩
    have hW2 : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i, pj) ⊓
        (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i', qj) ≤
        t.PP.L.U i ⊓ t.PP.L.U i' ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n (qj PUnit.unit PUnit.unit)) :=
      fun y hy => ⟨⟨hy.1.1, hy.2.1⟩, (hle _ hy.2).2⟩
    have e1 := congrArg (resG t.G.left hW1) (hcross _ _ (s _) (s _) (hgs _) (hgs _) i)
    have e2 := congrArg (resG t.G.left hW2) (hs (qj PUnit.unit PUnit.unit) i i')
    rw [map_mul] at e1 e2
    erw [resG_resG', resG_resG', resG_resG'] at e1
    erw [resG_resG', resG_resG', resG_resG'] at e2
    show resG _ _ (resG _ (hle (i, pj)) (s (pj PUnit.unit PUnit.unit) i)) = _ *
      resG _ _ (resG _ (hle (i', qj)) (s (qj PUnit.unit PUnit.unit) i'))
    rw [resG_resG', resG_resG']
    erw [Units.val_mul, val_res', val_res', eB, resG_resG']
    rw [e1, e2, mul_left_comm, ← _root_.mul_assoc]
    rfl
  · obtain ⟨a, ha⟩ := _root_.GlobalTheory.ProjSpace.exists_mem_chart k n (h (x (IsLocalRing.closedPoint K)))
    have hx : Set.range x ⊆ h ⁻¹ᵁ chart k n a := by
      rintro _ ⟨w, rfl⟩
      rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
      exact ha
    obtain ⟨y, i, hyx, hyr, hv⟩ := hfs a K x hx
    have hyr' : Set.range y ⊆ (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U
        (i, fun _ _ => a) := fun _ hw =>
      ⟨(hyr hw).1, Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => (hyr hw).2⟩
    refine ⟨y, (i, fun _ _ => a), hyx, hyr', ?_⟩
    show valF y _ (resG _ (hle (i, fun _ _ => a)) (s a i)) ≠ 0
    rwa [valF_resG y _ ((GlobalTheory.ZH.top_le_preimage_iff y _).2 hyr')]

end GlobalTheory.UMin.ThBdl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData

theorem cls_lam_proj {S : Scheme.{0}} {H : Over S} [GrpObj H] {L : LB H.left} (hL : L.IsLB) (h : (abelian₂ H L).IsLB) :
    cls (abelian₂ H L) h = lam (cls L hL) (fst H H) (snd H H) :=
  cls_cube_two hL (fst H H) (snd H H) h

theorem lbIso_iff_lam {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [GrpObj H₂] {L₁ : LB H₁.left} {L₂ : LB H₂.left}
    (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) (f g : H₁ ⟶ H₂) :
    LBIso (abelian₂ H₁ L₁) ((abelian₂ H₂ L₂).pull (lift (fst H₁ H₁ ≫ f) (snd H₁ H₁ ≫ g) : G2 H₁ ⟶ G2 H₂).left) ↔
      ∀ (T : Over S) (x z : T ⟶ H₁), lam (cls L₁ h₁) x z = lam (cls L₂ h₂) (x ≫ f) (z ≫ g) := by
  have hA : (abelian₂ H₁ L₁).IsLB := LB.isLB_linComb h₁ _ _
  have hB : (abelian₂ H₂ L₂).IsLB := LB.isLB_linComb h₂ _ _
  rw [← cls_eq_iff hA (pull_isLB hB _), cls_pull hB, cls_lam_proj h₁, cls_lam_proj h₂, pull_lam, lift_fst, lift_snd]
  constructor
  · intro h T x z
    have e := congrArg (pull (lift x z).left) h
    simpa only [pull_lam, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using e
  · intro h
    exact h _ _ _

theorem lam_of_rosatiGen {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {a b : B ⟶ B} (u : LB.Gen (LB.LinComb M (rosatiφ B a b) rosatiε)) (hu : u.IsGen) {T : Over S} (x y : T ⟶ B) :
    lam (cls M hM) (x ≫ a) y = lam (cls M hM) x (y ≫ b) := by
  unfold lam
  rw [GlobalTheory.EndRosati.cls_of_rosati hM u hu x y]

end GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData



theorem adjCls_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q r : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom q → IsMonHom r → IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → j ≫ r = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) r inc → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (jB : D₀.toPre.P.A ⟶ D.toPre.P.A), IsMonHom qB → IsMonHom jB → Over₀ U.toUnifPre U₀.toUnifPre q qB → Over₀ U₀.toUnifPre U.toUnifPre j jB → AdjCls (cls D.toPre.P.L D.toPre.P.isLB) (cls D₀.toPre.P.L D₀.toPre.P.isLB) qB jB := by
  intro R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG hG₀ U U₀ q r inc j hq hr hinc hj hiq hjr hqj hri qB jB hqB hjB hOq hOj
  obtain ⟨hAdm, hCZ⟩ := hR
  obtain ⟨incB, hincB, hOinc⟩ := exists_abelian_hom R _ hAdm D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre inc hinc
  obtain ⟨rB, hrB, hOr⟩ := exists_abelian_hom R _ hAdm D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre r hr
  have hjrB : jB ≫ rB = 𝟙 _ :=
    (over₀_onTorus_unique R _ hAdm D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre (j ≫ r)).1 _ _
      (FactorPol.over_comp hOj hOr) (by rw [hjr]; exact FactorPol.over_id)

  have h1 : ∀ (T : Over (Sp R)) (x z : T ⟶ G₀),
      lam (cls U₀.LG.L U₀.LG.isLB) x z = lam (cls U.LG.L U.LG.isLB) (x ≫ inc) (z ≫ j) := by
    intro T x z
    rw [hqj T (x ≫ inc) z, Category.assoc, hiq, Category.comp_id]
  have hI := GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart R hAdm D₀ D A₀ A G₀ G hG₀ hG U₀ U inc j incB jB hinc hj hincB hjB hOinc hOj
    ((lbIso_iff_lam U₀.LG.isLB U.LG.isLB inc j).2 h1)
  have h1B := (lbIso_iff_lam D₀.toPre.P.isLB D.toPre.P.isLB incB jB).1 hI

  have hadj : ∀ (T : Over (Sp R)) (x z : T ⟶ G),
      lam (cls U.LG.L U.LG.isLB) (x ≫ q ≫ inc) z = lam (cls U.LG.L U.LG.isLB) x (z ≫ r ≫ j) := by
    intro T x z
    rw [lam_comm, ← Category.assoc x, hri T z (x ≫ q), lam_comm, ← hqj T x (z ≫ r), Category.assoc]
  have hiso : LBIso (cubeLB G ![fst G G ≫ (q ≫ inc), snd G G] U.LG.L)
      (cubeLB G ![fst G G, snd G G ≫ (r ≫ j)] U.LG.L) := by
    have ha : (cubeLB G ![fst G G ≫ (q ≫ inc), snd G G] U.LG.L).IsLB := LB.isLB_linComb U.LG.isLB _ _
    have hb : (cubeLB G ![fst G G, snd G G ≫ (r ≫ j)] U.LG.L).IsLB := LB.isLB_linComb U.LG.isLB _ _
    refine (cls_eq_iff ha hb).1 ?_
    rw [cls_cube_two U.LG.isLB _ _ ha, cls_cube_two U.LG.isLB _ _ hb]
    exact hadj _ _ _

  haveI : IsMonHom U.gen.hom := U.gen_hom
  have hext : ∀ a : G ⟶ G, (Over.pullback (jK R)).map a ≫ U.gen.hom =
      U.gen.hom ≫ (U.gen.inv ≫ (Over.pullback (jK R)).map a ≫ U.gen.hom) := fun a => by simp
  obtain ⟨E, hE, -⟩ := exists_degenerationEndomorphism_of_admissibleBase R _ hAdm D A G hG U (q ≫ inc) _ inferInstance inferInstance (hext _)
  obtain ⟨E', hE', -⟩ := exists_degenerationEndomorphism_of_admissibleBase R _ hAdm D A G hG U (r ≫ j) _ inferInstance inferInstance (hext _)
  have hros := (rosatiAdjoint_and_linear_of_admissibleBase R _ hAdm D A G hG U E E' (by rw [hE, hE']; exact hiso)).2.1
  have hEB : E.aB = qB ≫ incB :=
    (over₀_onTorus_unique R _ hAdm D D A A G G U.toUnifPre U.toUnifPre E.aG).1 _ _ (lin_of_endU E).1.2.2.1
      (by rw [hE]; exact FactorPol.over_comp hOq hOinc)
  have hE'B : E'.aB = rB ≫ jB :=
    (over₀_onTorus_unique R _ hAdm D D A A G G U.toUnifPre U.toUnifPre E'.aG).1 _ _ (lin_of_endU E').1.2.2.1
      (by rw [hE']; exact FactorPol.over_comp hOr hOj)
  haveI := E.homB
  haveI := E'.homB
  obtain ⟨u, hu, -⟩ := exists_ros GlobalTheory.firstFiveLaws.1.globalFns D.toPre.P.isAb D.toPre.P.isLB E.aB E'.aB hros
  intro T x z
  rw [h1B T (x ≫ qB) z, Category.assoc, ← hEB, lam_of_rosatiGen D.toPre.P.isLB u hu, hE'B, Category.assoc,
    reassoc_of% hjrB]

end GlobalTheory.Mum.PowData
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
noncomputable section

namespace GlobalTheory.Mum.PowData

open GlobalTheory.Mum.FactorPol



theorem periodRel_of_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (h : D₀.toPre.X →+ D.toPre.X) (k : D.toPre.X →+ D₀.toPre.X), Lin U.toUnifPre U₀.toUnifPre q qB h → OnTorus U₀.toUnifPre U.toUnifPre j k → (∀ y, D₀.toPre.c (k y) = D.toPre.c y ≫ qB) ∧ PeriodRel D.toPre D₀.toPre qB h k := by
  intro R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG hG₀ U U₀ q inc j hinc hj iq adj qB h k L T
  have hA := hR.1
  have := hR.2
  have := U.gen_hom
  have := U₀.gen_hom
  haveI := hinc
  haveI := hj
  haveI : IsMonHom q := L.1
  obtain ⟨k', tk'⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre inc hinc
  have un₀ := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre
  have un := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre
  have kh : ∀ χ, k' (h χ) = χ := congrFun ((un₀ _).2 _ _ (iq ▸ onTorus_comp tk' L.2.2.2) onTorus_id)
  have hinj : Function.Injective h := Function.LeftInverse.injective kh
  have C := GlobalTheory.Mum.Two.coord_of_lin R _ hA D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre q qB h L
  obtain ⟨c, hc, gc⟩ : ∃ c : A.A ⟶ A₀.A, IsMonHom c ∧ Gen₀ U.toUnifPre U₀.toUnifPre q c :=
    ⟨U.gen.inv ≫ (Over.pullback (jK R)).map q ≫ U₀.gen.hom, inferInstance, by simp [Gen₀]⟩
  obtain ⟨c', hc', gc'⟩ : ∃ c' : A₀.A ⟶ A.A, IsMonHom c' ∧ Gen₀ U₀.toUnifPre U.toUnifPre j c' :=
    ⟨U₀.gen.inv ≫ (Over.pullback (jK R)).map j ≫ U.gen.hom, inferInstance, by simp [Gen₀]⟩
  haveI := hc
  haveI := hc'
  obtain ⟨E, eG, eA⟩ := (GlobalTheory.UT.functorial_of_unif R _ hA D A G hG U).1 (q ≫ j) (c ≫ c') inferInstance inferInstance
    (by
      unfold Gen₀ at gc gc'
      rw [Functor.map_comp, Category.assoc, gc', ← Category.assoc, gc, Category.assoc])
  have hL := U.LG.isLB
  have hL₀ := U₀.LG.isLB

  have lamE : ∀ (T' : Over (Sp R)) (x y : T' ⟶ G),
      lam (cls U.LG.L hL) (x ≫ q ≫ j) y = lam (cls U₀.LG.L hL₀) (x ≫ q) (y ≫ q) := fun T' x y => by
    rw [lam_comm, ← Category.assoc, adj, lam_comm]
  have lamE' : ∀ (T' : Over (Sp R)) (x y : T' ⟶ G),
      lam (cls U.LG.L hL) x (y ≫ q ≫ j) = lam (cls U₀.LG.L hL₀) (x ≫ q) (y ≫ q) := fun T' x y => by
    rw [← Category.assoc, adj]
  have adjE : LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E.aG] U.LG.L) :=
    (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cube_two hL _ _ _).trans (Eq.trans (by rw [eG, lamE, lamE']) (cls_cube_two hL _ _ _).symm))
  have H₂ : LBIso (cubeLB G₀ ![fst G G ≫ q, snd G G ≫ q] U₀.LG.L)
      (cubeLB G ![fst G G ≫ E.aG, snd G G ≫ 𝟙 G] U.LG.L) :=
    (cls_eq_iff (LB.isLB_linComb hL₀ _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cube_two hL₀ _ _ _).trans (Eq.trans (by rw [eG, Category.comp_id, lamE]) (cls_cube_two hL _ _ _).symm))
  have H₃ := GlobalTheory.Mum.Two.lbIso_cubeLB_generic R _ D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre q q E.aG (𝟙 _) c c E.aA (𝟙 _)
    gc gc E.ext (by simp [Gen₀]) H₂
  obtain ⟨Ω, _, _, _, K⟩ := GlobalTheory.Mum.Two.exists_key R _ hA D D₀ A A₀ G G₀ hG hG₀ U U₀ q c qB h hc gc L C hinj
  obtain ⟨φ, hφ, hhφ⟩ := GlobalTheory.Mum.Two.periods_of_key R _ hA D D₀ A A₀ G G₀ hG hG₀ U U₀ q c qB h hc gc L C E E adjE H₃
    Ω K

  have eh : (⇑E.h : D.toPre.X → D.toPre.X) = ⇑h ∘ ⇑k :=
    (un _).2 _ _ (eG ▸ (lin_of_endU E).1.2.2.2) (onTorus_comp L.2.2.2 T)
  have hφk : ∀ y, φ y = k y := fun y => hinj ((hhφ y).trans (congrFun eh y))
  have hB := D.tau_bimult
  refine ⟨fun y => ?_, fun χ => ?_⟩
  · obtain ⟨g', ha, hg'⟩ := hφ y _ (GlobalTheory.TorusExt.isIota_iota hB y)
    have h1 := ha.1
    rw [hg'.1, (GlobalTheory.TorusExt.isIota_iota hB y).1] at h1
    rw [← hφk y]
    refine GlobalTheory.Mum.Two.Fac.pt_ext R D₀.toPre Ω _ _ ?_
    simpa only [Category.assoc] using h1
  · obtain ⟨u, hu, -⟩ := C χ
    refine ⟨u, hu, fun y z J hJ => ?_⟩
    obtain ⟨g', ha, hg'⟩ := hφ y _ (GlobalTheory.TorusExt.isIota_iota hB y)
    have e := GlobalTheory.Mum.Two.act_val_frac R D₀.toPre D.toPre qB h Ω y (φ y) _ g' (GlobalTheory.TorusExt.isIota_iota hB y) hg' ha χ u hu
      z J hJ
    rwa [hφk] at e

end GlobalTheory.Mum.PowData
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LowDat.exists_lower : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R],
  GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R, 1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X →
  ∃ (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La)
    (o' : Obj D' (GlobalTheory.LowDat.lowLevel l) (baseKA (GlobalTheory.LowDat.lowLevel l)) (GlobalTheory.LowDat.lowS C))
    (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left),
    GlobalTheory.LowDat.IsIsoSat Dw Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    GlobalTheory.LowDat.IsLower Dw D' Z f ∧ D'.p = Dw.p - Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    D'.q = Dw.q - Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    IsGrpPullback o'.t.G C.P.D.toPre.P.A (𝟙 _) φB ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (o'.t.act.act x).left ≫ φB = φB ≫ (C.P.oD.onB.act x).left) ∧
    (∃ w : LB.Iso o'.t.PP.L (C.P.D.toPre.P.L.pull φB), w.IsGen) ∧
    ∃ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
        ∃ (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)) (I' : GlobalTheory.LowDat.LowTate C D' o' F),
          GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I ∧
          GlobalTheory.LowDat.LowGraded C Z D' f o' φB F I I' := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C hr
  obtain ⟨Z, hZ, hrk, tK, m1, m2, hI⟩ := GlobalTheory.T.exists_isotropic_saturated_weight_filtration Xo c R hR C hr
  obtain ⟨D', f, hf, hp, hq⟩ := GlobalTheory.T.exists_lower_datum_of_isotropic_saturated Dw Z hZ
  obtain ⟨o', φB, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_lowerObject_abelianPart_tateIsometry Xo c R hR C Z D' f hZ hf hrk hp hq tK m1 m2 hI
  refine ⟨Z, D', f, o', φB, hZ, hrk, hf, hrk ▸ hp, hrk ▸ hq, h1, h2, h3, tK, m1, m2, ?_⟩
  intro F _ _ _
  obtain ⟨I, hI1, hI2⟩ := hI F
  obtain ⟨I', hI'⟩ := h4 F I hI1 hI2
  exact ⟨I, I', hI1, hI2, hI'⟩
end
end

section


theorem _root_.GlobalTheory.T.goodMetric_topChernForm_integral_eq_smooth : GlobalTheory.Published.GoodTopChernForm := by
  first | exact @GlobalTheory.GoodTop.goodTopChernForm | exact GlobalTheory.GoodTop.goodTopChernForm | (intros; apply GlobalTheory.GoodTop.goodTopChernForm <;> assumption)
end
