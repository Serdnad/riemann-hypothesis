module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawCommutativityValue
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.AlgebraLevelSetting
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedCubicalBundleClosedFibreUniformisation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle751
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.quotientPoints_finite_representatives : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), k ≠ 0 → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → ∃ Rep : Set (QkPt D F k), Rep.Finite ∧ ∀ p : QkPt D F k, ∃ p' ∈ Rep, ∃ (z : D.X) (t : GtPtF D F), t.b = 1 ∧ (letI := GlobalTheory.TorusExt.gtGroup D F; k • t = 0 ∧ p.g = p'.g + GlobalTheory.TorusExt.iota hB F z + t) := by
  first | exact @GlobalTheory.Mum.qkPt_finite_reps | exact GlobalTheory.Mum.qkPt_finite_reps | (intros; apply GlobalTheory.Mum.qkPt_finite_reps <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torusExtensionPoint_characterValues_fixed_local : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∀ (σ : F →+* F), (∀ t ∈ T, σ t = t) → ∀ (g : GtPtF D F) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ (S : Set D.X), AddSubgroup.closure S = ⊤ → (∀ χ ∈ S, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → ∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) := by
  first | exact @GlobalTheory.CharValsFixed.main | exact GlobalTheory.CharValsFixed.main | (intros; apply GlobalTheory.CharValsFixed.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullDegTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem psi_val_on {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') {W : (Sp R).Opens}
    (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ) (x : D'.X) (z : (TK R').left)
    {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val (ψW.psi (h.xe x)) g z J = (om h.w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J' := by
  have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
  have ag : val (ψW.psi (h.xe x)) g z J = val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J :=
    ArcSpecialise.psiOn_agree ψW h.psiW _ _ _ (by rw [hg, Category.id_comp, h.g_comm]) hJ
  change _ = (om h.w z J J' (𝟙 _ ≫ D'.xK x))⁻¹ * _ at v
  rw [ag, v, Category.id_comp]

def reopen {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') {W : (Sp R).Opens}
    (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ) : IsPullDeg φ D D' :=
  { h with
    W := W
    psiW := ψW
    g := g
    g_comm := hg
    psi_pr := fun x => by
      obtain ⟨b, hb, hc⟩ := h.psi_pr x
      refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (val_corr hJ hc (𝟙 _)).trans ?_⟩
      rw [val_pull hJ, val_pull hJ]
      exact ArcSpecialise.psiOn_agree h.psiW ψW _ _ _ (by
        rw [Category.id_comp, Category.id_comp, hg, h.g_comm]) hJ }

theorem exists_top {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D')
    (hU : ∀ y, PsiUnitOn D y Set.univ) : ∃ h' : IsPullDeg φ D D', h'.W = ⊤ ∧ proj h' = proj h ∧ h'.xe = h.xe := by
  obtain ⟨ψ⟩ := nonempty_psiOn_top D hU
  exact ⟨reopen h ψ ((jK R' ≫ specOf φ) ≫ (Sp R).topIso.inv) (by
    rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]), rfl, rfl, rfl⟩

theorem psiUnitOn_univ {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D')
    (hU : ∀ y, PsiUnitOn D y Set.univ) (x : D'.X) : PsiUnitOn D' x Set.univ := by
  obtain ⟨h', hW, -, -⟩ := exists_top h hU
  obtain ⟨ψ, -⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull h'
  have := GlobalTheory.PsiUnitOfPsiOn.psiUnitOn_of_psiOn _ _ _ ψ x
  rw [hW] at this
  exact this

theorem act_iff {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') (f : D.P.A ⟶ D.P.A)
    (f' : D'.P.A ⟶ D'.P.A) :
    f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf φ)).map f ↔ f'.left ≫ proj h = proj h ≫ f.left := by
  have a : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst D.P.A.hom (specOf φ) =
      pullback.fst D.P.A.hom (specOf φ) ≫ f.left := by
    simp [Over.pullback_map_left, pullback.lift_fst]
  constructor
  · intro H
    have := congrArg (fun q => q.left ≫ pullback.fst D.P.A.hom (specOf φ)) H
    simp only [Over.comp_left, Category.assoc] at this
    rw [a] at this
    exact this.trans (Category.assoc _ _ _).symm
  · intro H
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      rw [a]
      exact H.trans (Category.assoc _ _ _)
    · exact (Over.w (f' ≫ h.e.hom)).trans (Over.w (h.e.hom ≫ (Over.pullback (specOf φ)).map f)).symm

theorem exists_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p₀ : IsPullDeg i D D') (q : IsPullDeg j D' D'')
    (hU : ∀ y, PsiUnitOn D y Set.univ) :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p₀ ∧ ∀ x, r.xe x = p₀.xe (q.xe x) := by
  obtain ⟨p, hW, e₁, e₂⟩ := exists_top p₀ hU
  rw [← e₁, ← e₂]
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨ψ, hv⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull p
  obtain ⟨g, hg⟩ : ∃ g : (TK R'').left ⟶ (specOf i ⁻¹ᵁ p.W).toScheme,
      g ≫ (specOf i ⁻¹ᵁ p.W).ι = jK R'' ≫ specOf j :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hg' : (g ≫ (specOf i ∣_ p.W)) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, hr₁, hr₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW D D'' p.psiW (g ≫ (specOf i ∣_ p.W)) hg' gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := hv (q.xe x) _ g z J J' hJ hJ'
      have v₂ := psi_val_on q ψ g hg x z hJ' hJ''
      have hx : D''.xK x ≫ proj q = g ≫ (specOf i ⁻¹ᵁ p.W).ι ≫ (D'.c (q.xe x)).left := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = _
        rw [Category.assoc, q.c_pr, ← Category.assoc g, hg, Category.assoc]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      rw [v₂, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, hr₁, hr₂⟩

theorem exists_cancel {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} {θ : R₀ →+* R₂} (hθ : β.comp α = θ)
    {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂}
    (h₀ : IsPullDeg α D₀ D₁) (h : IsPullDeg θ D₀ D) (hU : ∀ y, PsiUnitOn D₀ y Set.univ) :
    ∃ h' : IsPullDeg β D₁ D, proj h' ≫ proj h₀ = proj h ∧ ∀ x, h₀.xe (h'.xe x) = h.xe x := by
  subst hθ
  obtain ⟨h₁, hW₁, e₁', e₂'⟩ := exists_top h₀ hU
  rw [← e₁', ← e₂']
  have hW : specOf α ⁻¹ᵁ h₁.W = ⊤ := by rw [hW₁]; rfl
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW, hv⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull h₁
  obtain ⟨g, hg⟩ : ∃ g : (TK R₂).left ⟶ (specOf α ⁻¹ᵁ h₁.W).toScheme,
      g ≫ (specOf α ⁻¹ᵁ h₁.W).ι = jK R₂ ≫ specOf β :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨hD, k₁, k₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW D₁ D ψW g hg gp w hw hr xe hc
    (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ₀ hJ
    have v₁ := hv (xe x) _ g z J₀ J₁ hJ₀ hJ₁
    have ag : val (h₁.psiW.psi (h.xe x)) (g ≫ (specOf α ∣_ h₁.W)) z J₀ =
        val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J₀ :=
      ArcSpecialise.psiOn_agree h₁.psiW h.psiW _ _ _ (by
        rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg, Category.id_comp, h.g_comm, Category.assoc]
        exact congrArg (jK R₂ ≫ ·) sc) hJ₀
    have hx : D.xK x ≫ Φ = g ≫ (specOf α ⁻¹ᵁ h₁.W).ι ≫ (D₁.c (xe x)).left := by
      show (jK R₂ ≫ (D.c x).left) ≫ Φ = _
      rw [Category.assoc, hc, ← Category.assoc g, hg, Category.assoc]
    change _ = (om h.w z J₀ J (𝟙 _ ≫ D.xK x))⁻¹ * _ at v
    rw [hxe, ag, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD, by rw [k₁, e₁], fun x => by rw [k₂, hxe]⟩

theorem main : (∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (_ : IsPullDeg φ D D'), (∀ y, PsiUnitOn D y Set.univ) → ∀ x, PsiUnitOn D' x Set.univ) ∧ (∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') (f : D.P.A ⟶ D.P.A) (f' : D'.P.A ⟶ D'.P.A), f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf φ)).map f ↔ f'.left ≫ h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = (h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ f.left) ∧ (∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), (∀ y, PsiUnitOn D y Set.univ) → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x)) ∧ (∀ {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} {θ : R₀ →+* R₂}, β.comp α = θ → ∀ {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂} (h₀ : IsPullDeg α D₀ D₁) (h : IsPullDeg θ D₀ D), (∀ y, PsiUnitOn D₀ y Set.univ) → ∃ h' : IsPullDeg β D₁ D, (h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf β)) ≫ h₀.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf α) = h.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ) ∧ ∀ x, h₀.xe (h'.xe x) = h.xe x) :=
  ⟨fun h hU x => psiUnitOn_univ h hU x, fun h f f' => act_iff h f f', fun p q hU => exists_comp p q hU,
    fun e _ _ _ h₀ h hU => exists_cancel e h₀ h hU⟩

end GlobalTheory.PullDegTop
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.cubicalStructure_of_pushed_point_values_cube_function : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (t : LB.Gen (Theta G L.L)), t.IsGen → (∀ U, Function.Injective ((lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G2 G).left ⟶ X), (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ a = (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ b → a = b) → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ U, Function.Injective ((lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G4 G).left ⟶ X), (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ a = (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → IsCub (fun a b d : T ⟶ G' => GlobalTheory.CubTransport.thV t z I (pushHom h T a) (pushHom h T b) (pushHom h T d))) → ∃ c : CubicalStr G L, c.t = t := by
  first | exact @GlobalTheory.Mum.cubicalStr_of_push_val | exact GlobalTheory.Mum.cubicalStr_of_push_val | (intros; apply GlobalTheory.Mum.cubicalStr_of_push_val <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.translatedCubicalBundle_closedFibre_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G), a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
    ∀ P₁ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G),
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₁ (GlobalTheory.ValueForm.modelCP U.toUnifPre GlobalTheory.firstFiveLaws.1.globalFns) →
    ∃ (a₀ : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) ⟶ thickObj R (maximalIdeal R) 0 G)
      (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)),
      a₀.left ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0) = thick R (maximalIdeal R) 0 ≫ a.left ∧ a₀ ^ 2 = 1 ∧
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P ∧
      P₀.L.L = P₁.L.L.pull ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        val P₀.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a₀) * x).left z J * (val P₁.sym (toUnit T ≫ a₀).left z J)⁻¹) ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x y u : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        cubV P₀.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a₀) * u) * (cubV P₁.c z J x y (toUnit T ≫ a₀))⁻¹) := by
  first | exact @GlobalTheory.Mum.TranslateLevel.exists_level_translate | exact GlobalTheory.Mum.TranslateLevel.exists_level_translate | (intros; apply GlobalTheory.Mum.TranslateLevel.exists_level_translate <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GenBundle

variable {X Y Z : Scheme.{0}}

theorem lbIso_self {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_comp' {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso (L.pull (g ≫ f)) ((L.pull f).pull g) :=
  LBIso.chartPull (chartPullSame L (fun _ : PUnit => g ≫ f) (fun _ => f) (fun _ => 1) g fun _ => rfl)
    (chartPullPull _ g) (lbIso_self (pull_isLB hL f))

end GlobalTheory.Mum.GenBundle


open GlobalTheory.Mum.GenBundle in
theorem GlobalTheory.Mum.genBundle_extends : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w := by
  intro R R' _ _ _ _ _ ρ hA _ D₁ D₂ D₃ E p q₁ q₂ Φ κ _ hκ h1 h2
  obtain ⟨hN, -, hI, -⟩ := hA
  haveI := D₃.P.isAb
  haveI : Smooth D₃.P.A.hom := D₃.P.isAb.smooth
  haveI : GeometricallyIntegral D₃.P.A.hom := geometricallyIntegral_of_isAbelianScheme D₃.P.A
  have hL₁ := D₁.P.isLB
  have hL₂ := D₂.P.isLB
  have hL₃ := D₃.P.isLB
  have hLE := E.P.isLB
  have a₁ : LBIso (D₃.P.L.pull κ) (D₁.P.L.pull (GlobalTheory.PsiEvenPull.proj q₁)) :=
    LBIso.chartPull (chartPullPull D₃.P.L κ)
      (chartPullSame D₁.P.L (fun _ : PUnit => GlobalTheory.PsiEvenPull.proj q₁) (fun _ => GlobalTheory.PsiEvenPull.proj p)
        (fun _ => 1) κ fun _ => h1.symm) ⟨p.w, p.w_gen⟩
  have a : LBIso (D₃.P.L.pull κ) E.P.L :=
    LBIso.trans (pull_isLB hL₃ κ) (pull_isLB hL₁ _) hLE a₁ (LBIso.symm ⟨q₁.w, q₁.w_gen⟩)
  have b₀ : LBIso E.P.L (D₂.P.L.pull (κ ≫ Φ)) := h2 ▸ ⟨q₂.w, q₂.w_gen⟩
  have b : LBIso (D₃.P.L.pull κ) ((D₂.P.L.pull Φ).pull κ) :=
    LBIso.trans (pull_isLB hL₃ κ) (pull_isLB hL₂ _) (pull_isLB (pull_isLB hL₂ Φ) κ)
      (LBIso.trans (pull_isLB hL₃ κ) hLE (pull_isLB hL₂ _) a b₀) (lbIso_pull_comp' hL₂ Φ κ)
  have hj : pullback.fst D₃.P.A.hom (jK R') = hκ.1.isoPullback.inv ≫ κ := by
    exact (Iso.inv_hom_id_assoc hκ.1.isoPullback _).symm.trans
      (congrArg (hκ.1.isoPullback.inv ≫ ·) hκ.1.isoPullback_hom_fst)
  have c : LBIso (D₃.P.L.pull (pullback.fst D₃.P.A.hom (jK R')))
      ((D₂.P.L.pull Φ).pull (pullback.fst D₃.P.A.hom (jK R'))) :=
    LBIso.chartPull
      (chartPullSame D₃.P.L (fun _ : PUnit => pullback.fst D₃.P.A.hom (jK R')) (fun _ => κ) (fun _ => 1)
        hκ.1.isoPullback.inv fun _ => hj)
      (chartPullSame (D₂.P.L.pull Φ) (fun _ : PUnit => pullback.fst D₃.P.A.hom (jK R')) (fun _ => κ) (fun _ => 1)
        hκ.1.isoPullback.inv fun _ => hj) b
  obtain ⟨w, hw⟩ := GlobalTheory.Mum.lbIso_of_generic_local R' D₃.P.A (eSec D₃.P.A) (Over.w η[D₃.P.A]) D₃.P.L
    (D₂.P.L.pull Φ) hL₃ (pull_isLB hL₂ Φ) c
  exact ⟨w, (isGen_iff w).1 hw⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCompTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_isPullDeg_comp_of_preimage {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'')
    (hW : specOf i ⁻¹ᵁ p.W = ⊤) :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨ψ', hv⟩ := PullDegCancelTop.exists_psiOn_pull p
  obtain ⟨g, hg'⟩ : ∃ g : (TK R'').left ⟶ (specOf i ⁻¹ᵁ p.W).toScheme,
      g ≫ (specOf i ⁻¹ᵁ p.W).ι = jK R'' ≫ specOf j :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hg : (g ≫ (specOf i ∣_ p.W)) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg', Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, hr₁, hr₂, -⟩ := PullDegCompData.exists_isPullDeg_of_valW D D'' p.psiW (g ≫ (specOf i ∣_ p.W)) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := hv (q.xe x) _ g z J J' hJ hJ'
      have v₂ := PsiEvenPull.psi_pull q x (𝟙 _) z hJ' hJ''
      have ag : val (ψ'.psi (q.xe x)) g z J' = val (q.psiW.psi (q.xe x)) (𝟙 _ ≫ q.g) z J' :=
        ArcSpecialise.psiOn_agree ψ' q.psiW _ _ _ (by rw [hg', Category.id_comp, q.g_comm]) hJ'
      have hx : D''.xK x ≫ proj q = g ≫ (specOf i ⁻¹ᵁ p.W).ι ≫ (D'.c (q.xe x)).left := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = _
        rw [Category.assoc, q.c_pr, ← Category.assoc g, hg', Category.assoc]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om q.w z J' J'' (𝟙 _ ≫ D''.xK x))⁻¹ * _ at v₂
      rw [ag, v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, hr₁, hr₂⟩

theorem exists_isPullDeg_comp_top : ∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), p.W = ⊤ → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  intro R R' R'' _ _ _ _ _ _ i j D D' D'' p q e
  exact exists_isPullDeg_comp_of_preimage p q (by rw [e]; rfl)

end GlobalTheory.PullDegCompTop
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.rigidified_identifications_generic_fibre_agree : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w → PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) → ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  first | exact @GlobalTheory.GenEqual.genequal | exact GlobalTheory.GenEqual.genequal | (intros; apply GlobalTheory.GenEqual.genequal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), IsIntegral F.X ∧ Geo.Tor.IsNormalScheme F.X ∧ IsLocallyNoetherian F.X := by
  first | exact @GlobalTheory.SiegelIntegral.integral_normal_noetherian | exact GlobalTheory.SiegelIntegral.integral_normal_noetherian | (intros; apply GlobalTheory.SiegelIntegral.integral_normal_noetherian <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.siegelObject_rigidity_identifications_eq : ∀ (h M : ℕ), 3 ≤ M → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp (cycAway M)) (s' : S' ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s) (o : SiegPre h M (zetaAway M) s') (f : S' ⟶ S), Out.RelAmple c.A c.diag → ∀ (φ ψ : o.A.left ⟶ c.A.left) (φ₂ ψ₂ : (G2 o.A).left ⟶ (G2 c.A).left), IsGrpPullback o.A c.A f φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → (∀ a, (o.lev a).left ≫ φ = f ≫ (c.lev a).left) → IsGrpPullback o.A c.A f ψ → IsSquare ψ ψ₂ → LBIso o.P (c.P.pull ψ₂) → (∀ a, (o.lev a).left ≫ ψ = f ≫ (c.lev a).left) → φ = ψ := by
  first | (exact @GlobalTheory.SiegRigidCyc.eq_of_pullback) | (exact GlobalTheory.SiegRigidCyc.eq_of_pullback) | (intros; apply GlobalTheory.SiegRigidCyc.eq_of_pullback  <;> assumption)
end
