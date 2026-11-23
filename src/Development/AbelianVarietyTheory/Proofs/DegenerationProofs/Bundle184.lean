module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle168
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle131
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle183
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle180
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreTorsionEqReductions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSeriesAtPointIntegralOfPeriodValuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.IsogRed

variable {S T : Scheme.{0}} (f : T ⟶ S)

noncomputable def sec {G : Over S} (s : 𝟙_ (Over S) ⟶ G) : 𝟙_ (Over T) ⟶ (Over.pullback f).obj G :=
  Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map s

theorem sec_comp {G G' : Over S} (s : 𝟙_ (Over S) ⟶ G) (I : G ⟶ G') :
    sec f (s ≫ I) = sec f s ≫ (Over.pullback f).map I := by
  simp only [sec, Functor.map_comp, Category.assoc]

theorem sec_pow {G : Over S} [GrpObj G] (s : 𝟙_ (Over S) ⟶ G) (n : ℕ) : sec f (s ^ n) = sec f s ^ n := by
  simp only [sec, ← MonObj.comp_pow]
  congr 1
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih]

theorem sec_left {G : Over S} (s : 𝟙_ (Over S) ⟶ G) :
    (sec f s).left ≫ pullback.fst G.hom f = f ≫ s.left := by
  have hw := Over.w (Functor.LaxMonoidal.ε (Over.pullback f))
  have hc := pullback.condition (f := (𝟙_ (Over S)).hom) (g := f)
  simp only [sec, Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
  simp at hw hc ⊢

theorem sec_eq {G : Over S} (s : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over T) ⟶ (Over.pullback f).obj G)
    (h : f ≫ s.left = x.left ≫ pullback.fst G.hom f) : sec f s = x := by
  ext1
  apply pullback.hom_ext
  · rw [sec_left, h]
  · have h1 := Over.w (sec f s)
    have h2 := Over.w x
    simp only [Over.pullback_obj_hom] at h1 h2
    rw [h1, h2]

theorem sec_injective [IsSchemeTheoreticallyDominant f] {G : Over S} [IsSeparated G.hom]
    {s t : 𝟙_ (Over S) ⟶ G} (h : sec f s = sec f t) : s = t := by
  refine GlobalTheory.over_ext_of_schemeTheoreticallyDominant (Y := 𝟙_ (Over S)) f ?_
  rw [← sec_left, ← sec_left, h]

theorem smConn_baseChange (G : Over S) [GrpObj G] (h : SmConn G) : SmConn ((Over.pullback f).obj G) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩ <;> (try simp only [Over.pullback_obj_hom]) <;> infer_instance

theorem sec_residue_surjective {R : Type} [CommRing R] [HenselianLocalRing R] (G : Over (Sp R)) [Smooth G.hom]
    (x : 𝟙_ _ ⟶ spFibre G) : ∃ s : 𝟙_ _ ⟶ G, sec (spMap (IsLocalRing.residue R)) s = x := by
  have hx : (x.left ≫ pullback.fst G.hom (spMap (IsLocalRing.residue R))) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ 𝟙 _ := by
    have hw := Over.w x
    simp only [Over.pullback_obj_hom] at hw
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    simp
  obtain ⟨⟨y, hy⟩, hyx⟩ := GlobalTheory.reducePoint_residue_surjective G.hom R (𝟙 _) ⟨_, hx⟩
  refine ⟨Over.homMk y (by simpa using hy), sec_eq _ _ _ ?_⟩
  simpa [GlobalTheory.reducePoint] using congrArg Subtype.val hyx

theorem relDim_spFibre {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (hG : SmConn G) (g : ℕ)
    (h : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G).hom) :
    SmoothOfRelativeDimension g (spFibre G).hom := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{0} g) :=
    smoothOfRelativeDimension_isStableUnderBaseChange g
  have hG0 : SmoothOfRelativeDimension g G.hom := by
    apply GlobalTheory.GenericDim.smoothOfRelativeDimension_of_generic R G g
    unfold ReciprocityTheory.ChartRestriction.G.Out.jK
    obtain ⟨ψ, hψ⟩ : ∃ ψ : K →+* FractionRing R, ψ.comp (algebraMap R K) = algebraMap R (FractionRing R) :=
      ⟨_, (IsLocalization.algEquiv (nonZeroDivisors R) K (FractionRing R)).toAlgHom.comp_algebraMap⟩
    have hK : SmoothOfRelativeDimension g
        (pullback.snd G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := h
    rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp]
    have key : pullback.snd G.hom (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) =
        (pullbackLeftPullbackSndIso G.hom _ _).inv ≫
          pullback.snd (pullback.snd G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (Spec.map (CommRingCat.ofHom ψ)) := by
      rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
    rw [key]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension.{0} g)
      (hP := @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
        (smoothOfRelativeDimension_isStableUnderBaseChange g)) _ _).mpr
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (self := smoothOfRelativeDimension_isStableUnderBaseChange g) (IsPullback.of_hasPullback _ _) hK)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (self := smoothOfRelativeDimension_isStableUnderBaseChange g) (IsPullback.of_hasPullback _ _) hG0

theorem pow_comp_isogeny {Z A B : Over T} [GrpObj A] [GrpObj B] (i : A ⟶ B) (r : B ⟶ A) [IsMonHom i] {m : ℕ}
    (hri : r ≫ i = 𝟙 _ ^ m) (c : ℕ) (x : Z ⟶ B) : ((x ≫ r) ^ c) ≫ i = x ^ (m * c) := by
  rw [MonObj.pow_comp, Category.assoc, hri, MonObj.comp_pow, Category.comp_id, pow_mul]

theorem sec_eq_comp {G : Over S} {A : Over T} (e : (Over.pullback f).obj G ≅ A) (s : 𝟙_ (Over S) ⟶ G)
    (a : 𝟙_ (Over T) ⟶ A) (h : f ≫ s.left = a.left ≫ e.inv.left ≫ pullback.fst G.hom f) : sec f s = a ≫ e.inv := by
  apply sec_eq
  rw [h, Over.comp_left, Category.assoc]

theorem exists_section {G G' : Over S} [GrpObj G] [GrpObj G'] [IsSchemeTheoreticallyDominant f] [IsSeparated G'.hom]
    {A : Over T} [GrpObj A] (e : (Over.pullback f).obj G ≅ A) (i : A ⟶ (Over.pullback f).obj G')
    (r : (Over.pullback f).obj G' ⟶ A) [IsMonHom i] {m c : ℕ} (hri : r ≫ i = 𝟙 _ ^ m) (I : G ⟶ G')
    (hI : (Over.pullback f).map I = e.hom ≫ i)
    (hext : ∀ a : 𝟙_ _ ⟶ A, ∃ s : 𝟙_ _ ⟶ G, f ≫ s.left = (a ^ c).left ≫ e.inv.left ≫ pullback.fst G.hom f)
    (z : 𝟙_ _ ⟶ G') : ∃ s : 𝟙_ _ ⟶ G, s ≫ I = z ^ (m * c) := by
  obtain ⟨s, hs⟩ := hext (sec f z ≫ r)
  refine ⟨s, sec_injective f ?_⟩
  rw [sec_comp, sec_eq_comp f e s _ hs, hI, sec_pow, Category.assoc, e.inv_hom_id_assoc,
    pow_comp_isogeny i r hri]

theorem semiAbelian_reduction_of_isogeny : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] (G' : Over (Sp R)) [GrpObj G'] (g m : ℕ), IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → IsSemiAbelian G' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G').hom → ∀ (i : A ⟶ (Over.pullback (spMap (algebraMap R K))).obj G') (r : (Over.pullback (spMap (algebraMap R K))).obj G' ⟶ A), IsMonHom i → IsMonHom r → 1 ≤ m → r ≫ i = 𝟙 _ ^ m → ∃ (G : Over (Sp R)) (_ : GrpObj G) (e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ A), SmConn G ∧ IsMonHom e.hom ∧ Nonempty (TorusExtension (spFibre G)) := by
  intro R K _ _ _ _ _ hSH A _ G' _ g m hA hP hG' hgA hgG' i r hi hr hm hri
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := id hG'
  have hSG' : SmConn G' := ⟨a1, a2, a3, a4, a5⟩
  have : IsCommMonObj A := hA.1
  obtain ⟨M, hMg, hM, he, c, hc, hext⟩ := GlobalTheory.T.exists_neutral_group_model' R K hSH A hA hP
  obtain ⟨hdvr, hhens, hac, hfr⟩ := hSH
  refine ⟨M.Y, hMg, M.e, hM, he, ?_⟩
  obtain ⟨F, ⟨hF, hFe⟩, -⟩ := GlobalTheory.T.existsUnique_hom_extension_smoothConn_semiAbelian_dvr R K M.Y G' hM hG' (M.e.hom ≫ i) inferInstance
  have hgM : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj M.Y).hom := by
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{0} g) :=
      smoothOfRelativeDimension_isStableUnderBaseChange g
    rw [← Over.w M.e.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension.{0} g)
      (hP := @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
        (smoothOfRelativeDimension_isStableUnderBaseChange g)) ((Over.forget _).mapIso M.e).hom A.hom).mpr hgA
  refine GlobalTheory.T.torusExtension_of_surjective_of_dim_eq' (IsLocalRing.ResidueField R) (spFibre M.Y) (spFibre G') g
    (smConn_baseChange _ _ hM) (smConn_baseChange _ _ hSG')
    (relDim_spFibre M.Y hM g hgM) (relDim_spFibre G' hSG' g hgG')
    (a6 _ _) ((Over.pullback (spMap (IsLocalRing.residue R))).map F) inferInstance ?_
  intro y
  obtain ⟨w, hw⟩ := GlobalTheory.T.torusExtension_points_divisible' (IsLocalRing.ResidueField R) (spFibre G') (a6 _ _) (m * c)
    (by simpa using Nat.mul_le_mul hm hc) y
  obtain ⟨z, hz⟩ := sec_residue_surjective G' w
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  obtain ⟨s, hs⟩ := exists_section (spMap (algebraMap R K)) M.e i r hri F hFe (fun a => hext a) z
  refine ⟨sec (spMap (IsLocalRing.residue R)) s, ?_⟩
  rw [← sec_comp, hs, sec_pow, hz, hw]

end GlobalTheory.IsogRed
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_hom_algebraising_thickenings_projective : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y Z : Over (Spec (CommRingCat.of R))), IsProjBy Y.hom → IsProjBy Z.hom → Flat Y.hom → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom) → (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ g : Y ⟶ Z, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  first | exact @GlobalTheory.MorAlgIdeal.exists_hom_of_thickenings | exact GlobalTheory.MorAlgIdeal.exists_hom_of_thickenings | (intros; apply GlobalTheory.MorAlgIdeal.exists_hom_of_thickenings <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN.UnifPrime

theorem hypW_of_triple {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S) :
    HypW t.G t.PP.L :=
  ⟨t.act.act H.w0, t.act.act (H.bar H.w0), t.act.hom _, t.act.hom _,
    by rw [← t.act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, t.act.one], t.prim, t.adj _⟩

theorem exists_pelUnif : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (t : SAB H (Sp R)), PolAt t (jK R) → SplitOver t.G I → ThetaNZ t.G t.PP.L → ∃ P : PELUnif I t, P.TorsionIso := by
  intro h1 h2 h3 _ _ hE hU hP E _ _ _ H R _ _ _ I hA hpi t hpol hs hth
  obtain ⟨A, -, gen, hgen, hL, -⟩ := GlobalTheory.T.exists_polAV_generic_fibre_of_triple h1 h2 E H R t hpol
  have := hA.1.1
  have := hA.2.2.1
  obtain ⟨P, hPL, -⟩ := GlobalTheory.T.exists_cubical_bundle_of_symmetric_semiAbelian h1 R A t.G t.semi gen hgen t.PP t.cub t.sym
  obtain ⟨D, U, hUL, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocalDomain_prime h1 h2 h3 hE hU R I hA hpi t.G P t.semi (hPL ▸ hypW_of_triple t) hs
    (hPL ▸ hth) A gen hgen (hPL ▸ hL)
  obtain ⟨Q, -, -, -, hQ⟩ := hP E H R I hA.1 t D A U (hUL.trans hPL)
  exact ⟨Q, hQ⟩

end GlobalTheory.LN.UnifPrime
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem exists_isEE_of_adm : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.HasTests → S.admitted M U₀ → ∃ EE : M.Lat S.J, S.IsEE M U₀ EE ∧ (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) := by
  intro o Ω _ _ _ hb S M U₀ hT hA
  have hO : S.Over₀ M U₀ := hA.1
  haveI := hb.ft
  haveI := hb.char
  have hll := @GlobalTheory.ZH.classical_points_and_local_regularity o Ω _ _ _ _ _ M U₀ hO.normal
  have hte := @GlobalTheory.ZH.exists_at_test_of_cen o Ω _ _ _ _ S M U₀ hT hO
  have hwt := @GlobalTheory.ZH.test_weights o Ω _ _ _ _ S
  have h0a := @GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω _ _ _ _ S M U₀ hO
  have h0b := @GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a
  have h11 := @GlobalTheory.thetaSys_norm_FF_le_exp o Ω _ _ _ _ S hwt
  have h12 := @GlobalTheory.norm_val_FF_eq_of_div o Ω _ _ _ _ S M U₀ hO h0a h11 hte
  have hne := @GlobalTheory.ZH.FF_TT_ne_zero o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt
  have h2g := @GlobalTheory.ZH.comparison_function_regular o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt h11 h12
  have h2ge := @GlobalTheory.ZH.FirstIneq.ff_div_ff_mem_of_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt h11 h12
  have h2le := @GlobalTheory.ZH.ThetaSys.FF_div_FF_mem_O_of_valuationRing o Ω _ _ _ _ S M U₀ hO h0b h2g
  have h3h := @GlobalTheory.ZH.span_lattice_eq_of_valuationRing o Ω _ _ _ _ S M U₀ hA h0b hne h2ge h2le
  have h3b := @GlobalTheory.ZH.exists_basis_lattice_near o Ω _ _ _ _ S M U₀ hA h0b hne
  obtain ⟨EE, hE₁, hE₂⟩ := @GlobalTheory.ZH.WeightBundle.exists_lat o Ω _ _ _ _ S M U₀ hA hll.2 h0b hne h3h h3b
  exact ⟨EE, @GlobalTheory.ZH.isEE_of_span_weightSpaces o Ω _ _ _ _ S M U₀ EE hA h0a h0b hne hwt h12 hE₁ hE₂, hE₁⟩

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.testLattice_eq_span_model_sections : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → l.Match τ → u.Link σ b → b.det ≠ 0 → ∃ c : FractionRing u.V, c ≠ 0 ∧ τ.E = Submodule.span (OO p) (Set.range ((c • b).map (algebraMap _ (PadicAlgCl p)))) := by
  first | exact @GlobalTheory.ZH.testLattice_eq_span_sections | exact GlobalTheory.ZH.testLattice_eq_span_sections | (intros; apply GlobalTheory.ZH.testLattice_eq_span_sections <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorsionValue

local instance (priority := high) grpObjTorsionValuePullback {S T : Scheme.{0}} (f : T ⟶ S)
    (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

local instance (priority := high) torsionValueOverHomOfNatOne {S : Scheme.{0}} {Y G : Over S} [MonObj G] :
    OfNat (Y ⟶ G) 1 := ⟨toUnit Y ≫ η⟩

theorem exists_torsion_pullback {B B' : Scheme.{0}} (H : Over B) [GrpObj H] (r : B' ⟶ B) (c : Over.mk r ⟶ H) (n : ℕ)
    (hc : c ^ n = 1) : ∃ c' : baseOver B' ⟶ (Over.pullback r).obj H, c' ^ n = 1 ∧
      c'.left ≫ pullback.fst H.hom r = c.left := by
  have h := isGrpPullback_pullback H r
  let c' : baseOver B' ⟶ (Over.pullback r).obj H :=
    Over.homMk (pullback.lift c.left (𝟙 B') ((Over.w c).trans (Category.id_comp r).symm)) (pullback.lift_snd _ _ _)
  have e : c'.left ≫ pullback.fst H.hom r = c.left := pullback.lift_fst _ _ _
  let U : Over.mk ((baseOver B').hom ≫ r) ⟶ Over.mk r := Over.homMk (𝟙 B') rfl
  have e₁ : pushHom h _ c' = preHom U c := Over.OverMorphism.ext (e.trans (Category.id_comp _).symm)
  have e₂ : pushHom h _ (c' ^ n) = pushHom h _ 1 := by
    rw [map_pow, e₁, ← map_pow, hc, map_one, map_one]
  refine ⟨c', ?_, e⟩
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · exact congrArg (fun z => z.left) e₂
  · rw [Over.w, Over.w]

theorem cl_of_test {C : GlobalTheory.ZJ.Core} {p : ℕ} [Fact p.Prime] {y : Sp (GlobalTheory.ZJ.OO p) ⟶ C.Z} (τ : C.Test y) : C.Cl y := by
  let k : τ.V →+* PadicAlgCl p := (GlobalTheory.ZJ.OO p).subtype.comp τ.j
  have hk : Function.Injective k := Subtype.val_injective.comp τ.j_inj
  have e : GlobalTheory.ZJ.gPt p ≫ spMap τ.j = spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ jK τ.V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (IsFractionRing.lift_algebraMap (K := FractionRing τ.V) hk x).symm
  have e2 : GlobalTheory.ZJ.gPt p ≫ y = (spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ τ.yK) ≫ C.U.ι := by
    rw [Category.assoc, τ.yK_fac, ← Category.assoc, ← e, Category.assoc, τ.fac]
  unfold GlobalTheory.ZJ.Core.Cl
  rw [e2]
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact ((spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ τ.yK) w).2

theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  constructor
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (OO p).subtype).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (OO p).subtype_injective]; exact bot_le)

theorem exists_lift {Z : Scheme.{0}} {N W : Z.Opens} (hN : N ≤ W) {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ Z)
    (hy : y (cPt p) ∈ W) (x : Sp (kb p) ⟶ N.toScheme) (hx : x ≫ N.ι = rPt p ≫ y) :
    ∃ y' : Sp (OO p) ⟶ W.toScheme, y' ≫ W.ι = y ∧ x ≫ Z.homOfLE hN = rPt p ≫ y' := by
  have hr : Set.range y ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint w).map y.continuous).mem_open W.isOpen hy
  have hy' : IsOpenImmersion.lift W.ι y hr ≫ W.ι = y := IsOpenImmersion.lift_fac _ _ _
  refine ⟨_, hy', ?_⟩
  rw [← cancel_mono W.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, hy', hx]

theorem chase {k O N W G P H H' Φ X V : Scheme.{0}} {x : k ⟶ N} {i : N ⟶ W} {h : W ⟶ G} {j : G ⟶ P} [Mono j]
    {r : k ⟶ O} {y' : O ⟶ W} {c₁ : O ⟶ X} {f : X ⟶ V} {κ : V ⟶ P} {c' : k ⟶ H'} {e : H' ⟶ Φ} {s : Φ ⟶ X}
    {q : H' ⟶ H} {g : H ⟶ G} {c : k ⟶ H} (h₁ : x ≫ i = r ≫ y') (h₂ : y' ≫ h ≫ j = c₁ ≫ f ≫ κ)
    (h₃ : r ≫ c₁ = (c' ≫ e) ≫ s) (h₄ : e ≫ s ≫ f ≫ κ = q ≫ g ≫ j) (h₅ : c' ≫ q = c) : x ≫ i ≫ h = c ≫ g := by
  rw [← cancel_mono j]
  simp only [Category.assoc] at h₃ ⊢
  rw [reassoc_of% h₁, h₂, reassoc_of% h₃, h₄, reassoc_of% h₅]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}

theorem mem_ker (t : ρ.GeoTest p y₀) {a : S.Gam} (ha : a ∈ t.l.yy.ker) : a ∈ t.τ.yy.ker := by
  obtain ⟨e, -, he⟩ := t.mt
  have := (he a 0).2 (by rw [map_zero]; exact ha)
  exact this

theorem integral_eq_section {Q : Clos ρ M U₀ EE} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u} (tm : Q.TMap t c)
    {a : S.Gam} {W : M.Z.Opens} {h : W.toScheme ⟶ Q.G.toScheme} (hh : h ≫ Q.G.ι ≫ Q.P.hom = W.ι)
    (hgen : ∀ (x : Sp (PadicAlgCl p) ⟶ W.toScheme) (x' : Sp (PadicAlgCl p) ⟶ pullback ρ.P.A.hom Q.u₀),
      x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι →
      x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀)
    {y' : Sp (OO p) ⟶ W.toScheme} (hy : y' ≫ W.ι = y) {c₁ : Sp (OO p) ⟶ t.u.G.left} {a' : t.u.PtC}
    (h₁ : c₁ ≫ t.u.G.hom = spMap t.u.j) (h₂ : gPt p ≫ c₁ = t.u.toG a')
    (h₃ : t.u.toA a' = spMap y₀ ≫ (ρ.pt a).left) :
    y' ≫ h ≫ Q.G.ι = c₁ ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
  have := Q.proper
  have := isDominant_gPt p
  have e : gPt p ≫ spMap t.u.j = jFK (R := t.u.V) (PadicAlgCl p) ≫ jK t.u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have e₀ : jFK (R := t.u.V) (PadicAlgCl p) ≫ spMap t.u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap t.u.fac)
    rw [← Spec.map_comp]
    rfl
  let α : Sp (PadicAlgCl p) ⟶ pullback t.u.G.hom (jK t.u.V) := a'.left
  have ha : α ≫ pullback.snd _ _ = jFK (R := t.u.V) (PadicAlgCl p) := Over.w a'
  have hs : (α ≫ tm.φ) ≫ pullback.snd _ _ = jFK (R := t.u.V) (PadicAlgCl p) ≫ c.yK := by
    rw [Category.assoc, tm.φ_snd, ← Category.assoc, ha]
  refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ (gPt p) ?_
  · simp only [Category.assoc]
    rw [hh, hy, tm.f_over, ← Category.assoc, h₁, c.fac]
  · have k := hgen (gPt p ≫ y') (α ≫ tm.φ) ?_ ?_
    · rw [Category.assoc, Category.assoc, tm.φ_f] at k
      rw [k, ← Category.assoc (gPt p), h₂]
      exact (Category.assoc _ _ _).symm
    · rw [← Category.assoc (α ≫ tm.φ), hs, Category.assoc, Category.assoc, hy, c.yK_fac, ← Category.assoc, ← e,
        Category.assoc, c.fac]
    · rw [← Category.assoc (α ≫ tm.φ), hs, Category.assoc, Category.assoc, tm.φ_fst, ← Category.assoc c.yK, c.yK_u,
        ← Category.assoc (jFK _), e₀]
      exact h₃

theorem torsSec : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → ex.core.TorsSec (S.r * S.N) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG hF z _
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  choose W h hz hh hgen using fun a : S.HH M z => GlobalTheory.T.exists_section_extending_torsionPoints_support hL o Ω S ρ M U₀ EE hB Q z a.1 a.2
  let N : M.Z.Opens := ⟨⋂ a, (W a : Set M.Z), isOpen_iInter_of_finite fun a => (W a).isOpen⟩
  have hN : ∀ a, N ≤ W a := fun a w hw => Set.mem_iInter.1 hw a
  refine ⟨N, Set.mem_iInter.2 hz, ?_⟩
  intro p _ y τ x c hy hx hc
  have hcl := cl_of_test τ
  obtain ⟨y₀, t, cf, ⟨tm⟩⟩ := (GlobalTheory.T.exists_geometricTest_map_classicalPoint hL o Ω S ρ M U₀ EE hB Q hS hG).1 p y hcl
  obtain ⟨e, he, hef⟩ := GlobalTheory.T.exists_iso_special_fibre_test_geometric_test hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t cf tm τ hS hF
  obtain ⟨c', hc', hcl'⟩ := exists_torsion_pullback τ.H _ c _ hc
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => by
    rw [cf.at_]
    exact RatModel.norm_val_le_one rfl ((M.O _).algebraMap_mem a)
  have hX : (c' ≫ e.hom) ^ (S.r * S.N) = 1 := by
    rw [← MonObj.pow_comp, hc', MonObj.one_comp]
  obtain ⟨a, ha, c₁, a', h₁, h₂, h₃, h₄⟩ :=
    (special_torsion_eq_reduction hL o Ω S ρ p y₀ t.u t.l t.σ t.cls t.mod hint).2.1 (c' ≫ e.hom) hX
  have haH : a ∈ S.HH M z := by
    rw [hB.atTest z p y y₀ t.τ ⟨hy, hcl⟩ cf.at_]
    exact mem_ker t ha
  let b : S.HH M z := ⟨a, haH⟩
  obtain ⟨y', hy', hxy⟩ := exists_lift (Z := M.Z) (hN b) y ((congrArg (· ∈ W b) hy).mpr (hz b)) x hx
  have key := integral_eq_section tm (hh b) (hgen b _) hy' h₁ h₂ h₃
  refine ⟨M.Z.homOfLE (hN b) ≫ h b, ?_, chase (j := Q.G.ι) hxy key h₄ hef hcl'⟩
  show (M.Z.homOfLE (hN b) ≫ h b) ≫ Q.G.ι ≫ Q.P.hom = N.ι
  rw [Category.assoc, hh, Scheme.homOfLE_ι]

end GlobalTheory.ZH.TorsionValue
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.theta_series_at_point_integral_of_period_valuation : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∀ w, Crd (u.H S.N) σ a w → ∃ ν : u.D.toPre.X →+ ℝ, Ser l.q S.N cls w ν ∧ ((∃ m, ∀ α, ν α = QuadraticMap.polar l.q m α) → ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = a) := by
  first | exact @GlobalTheory.ZH.SeriesAtPoint.main | exact GlobalTheory.ZH.SeriesAtPoint.main | (intros; apply GlobalTheory.ZH.SeriesAtPoint.main <;> assumption)
end
