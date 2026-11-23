module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductDegenerationDataSum
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle021
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCanonicalDivisor
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section
namespace GlobalTheory.Mum.MixTwo

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))}
  {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

abbrev homF (a : G₁ ⟶ G₂) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (UnifPre.GF (G := G₁) F).left ⟶ (UnifPre.GF (G := G₂) F).left :=
  (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left

theorem homF_str (a : G₁ ⟶ G₂) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    homF a F ≫ MixedConv.strF G₂ F = MixedConv.strF G₁ F :=
  congrArg (fun q => q.left) (whiskerLeft_fst (TFK (R := R) F) ((Over.pullback (jK R)).map a))

theorem homF_gFK (a : G₁ ⟶ G₂) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    homF a F ≫ UnifPre.gFK (G := G₂) F = UnifPre.gFK (G := G₁) F ≫ a.left := by
  have h₁ := congrArg (fun q => q.left) (whiskerLeft_snd (TFK (R := R) F) ((Over.pullback (jK R)).map a))
  have h₂ : ((Over.pullback (jK R)).map a).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ a.left :=
    pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G₂.hom (jK R)) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

theorem val_secLin' {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {U : UnifPre I D A G} {F : Type} [Field F] [Algebra (FractionRing R) F] {k n : ℕ} {σ₀ : U.SecGF F k}
    {σ : Fin n → H0 U.LG.L k} {c : Fin n → F}
    (h : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)) σ₀
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i)))
    {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of F)) (r : Y ⟶ (UnifPre.GF (G := G) F).left)
    (hr : r ≫ MixedConv.strF G F = q) (y : Y) {J} (hJ : Good U.LG.L y J) :
    sval σ₀ r y J = ∑ i, GlobalTheory.BoxExpansion.constHomVal q y (c i) *
      sval (σ i) (r ≫ UnifPre.gFK (G := G) F) y J :=
  (GlobalTheory.BoxExpansion.secLin_val h r y hJ).trans (Finset.sum_congr rfl fun i _ => congrArg (· * _)
    ((gs_scal (MixedConv.strF G F) r y _).trans ((congrArg (fun q => constVal q y (c i)) hr).trans
      (GlobalTheory.BoxExpansion.constVal_eq _ _ _))))

theorem coreF₂ [CharZero R] (hL : LL) (hR : AdmBase R I) {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}
    {a : G₁ ⟶ G₂} {b : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {h : D₂.toPre.X →+ D₁.toPre.X} (hLin : Lin U₁ U₂ a b h)
    (hCo : Coord U₁ U₂ a b h) {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (j j' : ℕ)
    {N : Type} [Fintype N] (c : N → F) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j')
    (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α)
    (hE : ∀ ν e, U₂.ExpandsAt e j (σ ν) (f ν)) (hE' : ∀ ν e, U₁.ExpandsAt e j' (σ' ν) (f' ν))
    (hrel : ∀ (y : (UnifPre.GF (G := G₁) F).left) (J₁ J₂), Good U₁.LG.L y J₁ → Good U₂.LG.L y J₂ →
      ∑ ν, GlobalTheory.BoxExpansion.constHomVal (MixedConv.strF G₁ F) y (c ν) *
        (sval (σ ν) (UnifPre.gFK (G := G₁) F ≫ a.left) y J₂ * sval (σ' ν) (UnifPre.gFK (G := G₁) F) y J₁) = 0)
    (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F) (hg : Act D₁.toPre D₂.toPre b h g g')
    (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b) (hw : w.IsGen) (hw' : w'.IsGen)
    (x : N → D₂.toPre.X → F) (x' : N → D₁.toPre.X → F)
    (hx : ∀ ν χ, MixedConv.IsCoefB j g' w χ (f ν χ) (x ν χ)) (hx' : ∀ ν χ, MixedConv.IsCoefB j' g w' χ (f' ν χ) (x' ν χ))
    (α : D₁.toPre.X) :
    SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} =>
      ∑ ν, c ν * (x ν p.1.1 * x' ν p.1.2)) 0 := by
  obtain ⟨n, β, ρ, hβ, hc⟩ := MixedConv.exists_indep (R := R) c
  haveI : Nonempty G₁.left := ⟨eSec G₁ (⊥ : PrimeSpectrum R)⟩
  haveI : Nonempty G₂.left := ⟨eSec G₂ (⊥ : PrimeSpectrum R)⟩
  have P₁ := isPart_inl U₁.LG.L U₂.LG.L
  have P₂ := isPart_inr U₁.LG.L U₂.LG.L
  let d : Fin n → SecOver G₁.hom (LB.LinComb (join U₁.LG.L U₂.LG.L)
      (Sum.elim (fun _ : Fin 1 => (a.left ≫ 𝟙 G₂.left) ≫ coprod.inr) (fun _ : Fin 1 => 𝟙 G₁.left ≫ coprod.inl))
      (Sum.elim (fun _ => (j : ℤ)) (fun _ => (j' : ℤ)))) := fun m =>
    ∑ ν, ρ m ν • (show SecOver G₁.hom _ from
      H1.SectionArithmetic.mulSec (P₂.sec (H1.SectionArithmetic.pullSec (σ ν) a.left)) (P₁.sec (σ' ν)))
  have hd : ∀ m (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J), Good (join U₁.LG.L U₂.LG.L) z J →
      sval (d m) r z J = ∑ ν, constVal (r ≫ G₁.hom) z (ρ m ν) *
        (sval (σ ν) (r ≫ a.left) z (rr J) * sval (σ' ν) r z (rl J)) :=
    fun m Z r z J hJ => (sval_sum' (π := G₁.hom) hJ _ _ _).trans (Finset.sum_congr rfl fun ν _ =>
      (sval_smul' (π := G₁.hom) hJ _ _ _).trans (congrArg _ ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans
        (congrArg₂ (· * ·) ((P₂.sval_sec _ r z hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ z (P₂.good hJ)))
          (P₁.sval_sec _ r z hJ)))))
  have := U₁.smooth
  have h₀ := GlobalTheory.T.sval_eq_zero_of_linearIndependent_comb R F _ _ _ _ G₁.hom (MixedConv.strF G₁ F) _ MixedConv.isPullback_GF
    (join U₁.LG.L U₂.LG.L) (join_isLB U₁.LG.isLB U₂.LG.isLB) _ _ _ _ β hβ d
    (fun y J hJ => by
      refine Eq.trans ?_ (hrel y (rl J) (rr J) (P₁.good hJ) (P₂.good hJ))

      simp only [hd _ _ _ y J hJ, hc, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun m _ => ?_
      rw [(MixedConv.isPullback_GF (G := G₁) (F := F)).w, constVal_specMap, GlobalTheory.BoxExpansion.constVal_eq,
        GlobalTheory.BoxExpansion.constVal_eq, _root_.mul_assoc]
      rfl)
  have h₁ := MixedConv.sumF_comb hR Finset.univ β _ fun m => GlobalTheory.T.integralRelation_uniformisedHom_convolution_expansionTerms hL R I hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a b h hLin hCo F
    j j' N (ρ m) σ σ' f f' hE hE' (fun Z r z J₁ J₂ hJ₁ hJ₂ => by
      obtain ⟨J, hJ, rfl, rfl⟩ := exists_good_join U₁.LG.isLB U₂.LG.isLB hJ₁ hJ₂
      exact (hd m Z r z J hJ).symm.trans (h₀ m Z r z J hJ)) g g' hg w w' hw hw' x x' hx hx' α
  refine (congrArg (fun q => SumF I F q 0) (funext fun p => ?_)).mp h₁
  simp only [hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun m _ => (_root_.mul_assoc _ _ _).symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₁ : W0 U₁.toUnifPre) (w₂ : W0 U₂.toUnifPre), w₁.IsGen → w₂.IsGen → ∀ (j j' : ℕ), 1 ≤ j → 1 ≤ j' → ∀ (t₁ t₂ : SecA A₂ F j) (t₁' t₂' : SecA A₁ F j') s₁ s₂ s₁' s₂', U₂.ExpandsF F j w₂ t₁ s₁ → U₂.ExpandsF F j w₂ t₂ s₂ → U₁.ExpandsF F j' w₁ t₁' s₁' → U₁.ExpandsF F j' w₁ t₂' s₂' → CrossH c t₁ t₂ t₁' t₂' → ∀ (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F), Act D₁.toPre D₂.toPre b h g g' → ∀ (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ α, SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} => coef s₁ g' w p.1.1 * coef s₂' g w' p.1.2 - coef s₂ g' w p.1.1 * coef s₁' g w' p.1.2) 0 := by
  intro R _ _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ _ _ U₁ U₂ a c b h _ hG hLin hCo F _ _ _ w₁ w₂ hw₁ hw₂ j j' _ _
    t₁ t₂ t₁' t₂' s₁ s₂ s₁' s₂' H₁ H₂ H₁' H₂' hC g g' hg w w' hw hw' α
  obtain ⟨τ₁, r₁, n₁, c₁, σ₁, f₁, e₁, l₁, b₁⟩ := H₁
  obtain ⟨τ₂, r₂, n₂, c₂, σ₂, f₂, e₂, l₂, b₂⟩ := H₂
  obtain ⟨τ₁', r₁', n₁', c₁', σ₁', f₁', e₁', l₁', b₁'⟩ := H₁'
  obtain ⟨τ₂', r₂', n₂', c₂', σ₂', f₂', e₂', l₂', b₂'⟩ := H₂'
  choose x₁ hx₁ using fun i χ => MixedConv.exists_isCoefB g' hw χ (f₁ i χ)
  choose x₂ hx₂ using fun i χ => MixedConv.exists_isCoefB g' hw χ (f₂ i χ)
  choose x₁' hx₁' using fun i χ => MixedConv.exists_isCoefB g hw' χ (f₁' i χ)
  choose x₂' hx₂' using fun i χ => MixedConv.exists_isCoefB g hw' χ (f₂' i χ)
  have key := coreF₂ GlobalTheory.firstFiveLaws hR hLin hCo j j' (N := (Fin n₁ × Fin n₂') ⊕ (Fin n₂ × Fin n₁'))
    (Sum.elim (fun p => c₁ p.1 * c₂' p.2) (fun p => -(c₂ p.1 * c₁' p.2)))
    (Sum.elim (fun p => σ₁ p.1) (fun p => σ₂ p.1)) (Sum.elim (fun p => σ₂' p.2) (fun p => σ₁' p.2))
    (Sum.elim (fun p => f₁ p.1) (fun p => f₂ p.1)) (Sum.elim (fun p => f₂' p.2) (fun p => f₁' p.2))
    (by rintro (p | p); exacts [e₁ p.1, e₂ p.1]) (by rintro (p | p); exacts [e₂' p.2, e₁' p.2])
    (fun y J₁ J₂ hJ₁ hJ₂ => by
      have hh := GlobalTheory.T.carriedSections_crossRelation_of_hom R I D₁ D₂ A₁ A₂ G₁ G₂ U₁.toUnifPre U₂.toUnifPre a c hG F w₁ w₂ hw₁ hw₂ j j'
        t₁ t₂ t₁' t₂' τ₁ τ₂ τ₁' τ₂' r₁ r₂ r₁' r₂' hC y J₁ J₂ hJ₁ hJ₂
      rw [val_secLin' l₁ _ _ (homF_str a F) y hJ₂, val_secLin' l₂ _ _ (homF_str a F) y hJ₂,
        val_secLin' l₁' _ _ (Category.id_comp _) y hJ₁, val_secLin' l₂' _ _ (Category.id_comp _) y hJ₁, homF_gFK,
        Category.id_comp, Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_eq_zero] at hh
      refine Eq.trans ?_ hh
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, map_neg, map_mul,
        neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
      exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)
        (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _))
    g g' hg w w' hw hw' (Sum.elim (fun p => x₁ p.1) (fun p => x₂ p.1))
    (Sum.elim (fun p => x₂' p.2) (fun p => x₁' p.2))
    (by rintro (p | p); exacts [hx₁ p.1, hx₂ p.1]) (by rintro (p | p); exacts [hx₂' p.2, hx₁' p.2]) α
  refine (congrArg (fun q => SumF I F q 0) (funext fun p => ?_)).mp key
  rw [MixedConv.coef_of_secLin (b₁ _) (fun i => hx₁ i _), MixedConv.coef_of_secLin (b₂ _) (fun i => hx₂ i _),
    MixedConv.coef_of_secLin (b₁' _) (fun i => hx₁' i _), MixedConv.coef_of_secLin (b₂' _) (fun i => hx₂' i _),
    Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)
    (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)

end GlobalTheory.Mum.MixTwo
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.SumDeg

theorem tMul_of_box : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), IsBoxGen (φ := thφ D.P.A (x3 D.P.A)) (φ₁ := thφ D₁.P.A (x3 D₁.P.A)) (φ₂ := thφ D₂.P.A (x3 D₂.P.A)) (ε := thε) w (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.cub.t D₁.cub.t D₂.cub.t → ∀ (T T₁ T₂ : Over (Sp R)) (P : T ⟶ D.P.A) (P₁ : T₁ ⟶ D₁.P.A) (P₂ : T₂ ⟶ D₂.P.A) (ρ₁ : T ⟶ T₁) (ρ₂ : T ⟶ T₂), P ≫ p₁ = ρ₁ ≫ P₁ → P ≫ p₂ = ρ₂ ≫ P₂ → ∀ (t : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : ∀ χ : D₁.X, LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ χ) Oinvε)) (t₂ : ∀ χ : D₂.X, LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ χ) Oinvε)), (∀ x, IsBoxGen w ρ₁.left ρ₂.left (t x) (t₁ (q₁ x)) (t₂ (q₂ x))) → TMul D₁ P₁ t₁ → TMul D₂ P₂ t₂ → TMul D P t := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w hc T T₁ T₂ P P₁ P₂ ρ₁ ρ₂ e₁ e₂ t t₁ t₂ hb h₁ h₂ χ χ'
  haveI := hS.hom₁
  haveI := hS.hom₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.P.isLB y
  have B : ∀ x, (om w y J₁ J₂ J (P * cP D T x).left)⁻¹ * om w y J₁ J₂ J (cP D T x).left * om w y J₁ J₂ J P.left *
      (om w y J₁ J₂ J (1 : T ⟶ D.P.A).left)⁻¹ * val (t x) (𝟙 T.left) y J =
      val (t₁ (q₁ x)) ρ₁.left y J₁ * val (t₂ (q₂ x)) ρ₂.left y J₂ := fun x => by
    have := hb x T.left (𝟙 T.left) y J₁ J₂ J hJ₁ hJ₂ hJ
    simp only [Category.id_comp] at this
    rwa [GlobalTheory.TorusCoordPull.prod_O D P x (om w y J₁ J₂ J)] at this
  have K₁ : (lift (cP D T χ) (lift (cP D T χ') P)).left ≫ (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left =
      ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left := by
    rw [groupObj_lift3_comp_tensorCube_monHom, cPoint_pr hS.c_pr₁, cPoint_pr hS.c_pr₁, e₁, ← comp_cP D₁ ρ₁ (q₁ χ), ← comp_cP D₁ ρ₁ (q₁ χ'),
      ← comp_lift, ← comp_lift, Over.comp_left]
  have K₂ : (lift (cP D T χ) (lift (cP D T χ') P)).left ≫ (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left =
      ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left := by
    rw [groupObj_lift3_comp_tensorCube_monHom, cPoint_pr hS.c_pr₂, cPoint_pr hS.c_pr₂, e₂, ← comp_cP D₂ ρ₂ (q₂ χ), ← comp_cP D₂ ρ₂ (q₂ χ'),
      ← comp_lift, ← comp_lift, Over.comp_left]
  have C0 := hc T.left (lift (cP D T χ) (lift (cP D T χ') P)).left y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [K₁, K₂] at C0
  have pc := prod_cub (cP D T χ) (cP D T χ') P (om w y J₁ J₂ J)
  have C : (om w y J₁ J₂ J (cP D T χ * cP D T χ' * P).left * (om w y J₁ J₂ J (cP D T χ * cP D T χ').left)⁻¹ *
      (om w y J₁ J₂ J (cP D T χ * P).left)⁻¹ * (om w y J₁ J₂ J (cP D T χ' * P).left)⁻¹ *
      om w y J₁ J₂ J (cP D T χ).left * om w y J₁ J₂ J (cP D T χ').left * om w y J₁ J₂ J P.left *
      (om w y J₁ J₂ J (1 : T ⟶ D.P.A).left)⁻¹) * val D.cub.t (lift (cP D T χ) (lift (cP D T χ') P)).left y J =
      val D₁.cub.t (ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left) y J₁ *
      val D₂.cub.t (ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left) y J₂ := by
    rw [← pc]; exact C0
  have M₁ : val (t₁ (q₁ χ + q₁ χ')) ρ₁.left y J₁ *
      val D₁.cub.t (ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left) y J₁ =
      val (t₁ (q₁ χ)) ρ₁.left y J₁ * val (t₁ (q₁ χ')) ρ₁.left y J₁ := by
    have := (val_mul hJ₁ _ _ _).symm.trans ((val_corr hJ₁ (h₁ (q₁ χ) (q₁ χ')) ρ₁.left).trans (val_mul hJ₁ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_pull hJ₁ _ _ _).symm
  have M₂ : val (t₂ (q₂ χ + q₂ χ')) ρ₂.left y J₂ *
      val D₂.cub.t (ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left) y J₂ =
      val (t₂ (q₂ χ)) ρ₂.left y J₂ * val (t₂ (q₂ χ')) ρ₂.left y J₂ := by
    have := (val_mul hJ₂ _ _ _).symm.trans ((val_corr hJ₂ (h₂ (q₂ χ) (q₂ χ')) ρ₂.left).trans (val_mul hJ₂ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_pull hJ₂ _ _ _).symm
  have B0 := B (χ + χ')
  have Ba := B χ
  have Bb := B χ'
  rw [map_add (f := _), map_add (f := _), cPoint_add,
    show P * (cP D T χ * cP D T χ') = cP D T χ * cP D T χ' * P from mul_comm _ _] at B0
  rw [show P * cP D T χ = cP D T χ * P from mul_comm _ _] at Ba
  rw [show P * cP D T χ' = cP D T χ' * P from mul_comm _ _] at Bb
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans
    (congrArg (fun r => val D.cub.t r y J) (Category.id_comp _))))).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  show val (t (χ + χ')) (𝟙 T.left) y J * val D.cub.t (lift (cP D T χ) (lift (cP D T χ') P)).left y J =
    val (t χ) (𝟙 T.left) y J * val (t χ') (𝟙 T.left) y J
  apply Additive.ofMul.injective
  have a0 := congrArg Additive.ofMul B0
  have a1 := congrArg Additive.ofMul Ba
  have a2 := congrArg Additive.ofMul Bb
  have a3 := congrArg Additive.ofMul C
  have a4 := congrArg Additive.ofMul M₁
  have a5 := congrArg Additive.ofMul M₂
  simp only [ofMul_mul, ofMul_inv] at a0 a1 a2 a3 a4 a5 ⊢
  linear_combination (norm := abel) a0 + a3 - a1 - a2 + a4 + a5

end GlobalTheory.ProdUnif
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.SumDeg

variable {R : Type} [CommRing R] [IsDomain R] {D D₁ D₂ : DegPre R} (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A)
  [IsMonHom p₁] [IsMonHom p₂] (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left))

theorem isBoxGen_cub (hw : w.IsGen) :
    IsBoxGen w (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.cub.t D₁.cub.t D₂.cub.t := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D.P.A (D.P.A ⊗ D.P.A)).left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D.P.isAb _) (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2)
  have he : e.left ≫ (snd D.P.A (D.P.A ⊗ D.P.A)).left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (ε := thε)
    (fun a => (CubeMap.ofHom p₁).psum_comm a.down) (fun a => (CubeMap.ofHom p₂).psum_comm a.down)
    D.cub.isGen D₁.cub.isGen D₂.cub.isGen _ e.left he sj fun s I₁ I₂ I hI₁ hI₂ hI => ?_
  have C : IsCub (cubV D.cub s I) := isCub_cubV D.cub hI
  have C₁ : IsCub (cubV D₁.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I₁) := isCub_cubV D₁.cub hI₁
  have C₂ : IsCub (cubV D₂.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I₂) := isCub_cubV D₂.cub hI₂
  have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) 1 1 (om w s I₁ I₂ I)
  rw [_root_.mul_one, _root_.mul_one] at p
  have o₁ : e.left ≫ (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left =
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D₁.P.A) (lift 1 1)).left := by
    refine (groupObj_lift3_comp_tensorCube_monHom p₁ 1 1 1).trans ?_
    rw [MonObj.one_comp]
  have o₂ : e.left ≫ (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left =
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D₂.P.A) (lift 1 1)).left := by
    refine (groupObj_lift3_comp_tensorCube_monHom p₂ 1 1 1).trans ?_
    rw [MonObj.one_comp]
  have v₁ := (congrArg (fun m => val D₁.cub.t m s I₁) o₁).trans (C₁.face 1 1)
  have v₂ := (congrArg (fun m => val D₂.cub.t m s I₂) o₂).trans (C₂.face 1 1)
  exact (congrArg₂ (· * ·) p (C.face 1 1)).trans (Eq.trans (by simp) (congrArg₂ (· * ·) v₁ v₂).symm)

theorem isBoxGen_sym (hw : w.IsGen) : IsBoxGen w p₁.left p₂.left D.sym D₁.sym D₂.sym := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (inv_comp p₁) (inv_comp p₂)
    D.sym_gen D₁.sym_gen D₂.sym_gen D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2
    fun s I₁ I₂ I hI₁ hI₂ hI => ?_
  have q := prod_sym (eSec D.P.A) (om w s I₁ I₂ I)
  have o : eSec D.P.A ≫ (ι[D.P.A]).left = eSec D.P.A :=
    congrArg (fun m => m.left) (GrpObj.one_inv : η[D.P.A] ≫ ι[D.P.A] = η[D.P.A])
  rw [o, mul_inv_cancel] at q
  rw [eSec_comp, eSec_comp, val_sym_zero D₁ hI₁, val_sym_zero D₂ hI₂]
  exact congrArg₂ (· * ·) q (val_sym_zero D hI)

theorem exists_strBox_of_isSumDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), StrBox p₁ p₂ w D.rig D₁.rig D₂.rig D.cub.t D₁.cub.t D₂.cub.t D.sym D₁.sym D₂.sym ∧ ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x)) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ h
  have := h.hom₁
  have := h.hom₂
  obtain ⟨w, hw, hr, hψ⟩ := h.w
  exact ⟨w, ⟨hw, isBoxGen_of_mapsAt w _ _ hr, isBoxGen_cub p₁ p₂ w hw, isBoxGen_sym p₁ p₂ w hw⟩,
    fun x => isBoxGen_of_mapsAt w _ _ (hψ x)⟩

end GlobalTheory.ProdUnif
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

theorem even_box₂ : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ (iT : T ⟶ T) (iT₁ : T₁ ⟶ T₁) (iT₂ : T₂ ⟶ T₂) {iG : G ⟶ G} {iG₁ : G₁ ⟶ G₁} {iG₂ : G₂ ⟶ G₂} {iB : B ⟶ B} {iB₁ : B₁ ⟶ B₁} {iB₂ : B₂ ⟶ B₂} (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])) (s₁ : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![iG₁, 𝟙 G₁] ![1, -1])) (s₂ : LB.Gen (LB.LinComb L₂ (K := Fin 2) ![iG₂, 𝟙 G₂] ![1, -1])) (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) (σ₁ : LB.Gen (LB.LinComb M₁ (K := Fin 2) ![iB₁, 𝟙 B₁] ![1, -1])) (σ₂ : LB.Gen (LB.LinComb M₂ (K := Fin 2) ![iB₂, 𝟙 B₂] ![1, -1])), iT ≫ h₁ = h₁ ≫ iT₁ → iT ≫ h₂ = h₂ ≫ iT₂ → iT ≫ f = f ≫ iG → iT ≫ p = p ≫ iB → iT₁ ≫ f₁ = f₁ ≫ iG₁ → iT₁ ≫ p₁ = p₁ ≫ iB₁ → iT₂ ≫ f₂ = f₂ ≫ iG₂ → iT₂ ≫ p₂ = p₂ ≫ iB₂ → IsBoxGen wL g₁ g₂ s s₁ s₂ → IsBoxGen wM b₁ b₂ σ σ₁ σ₂ → GlobalTheory.PowUnif.EvenAlong we₁ iT₁ s₁ σ₁ → GlobalTheory.PowUnif.EvenAlong we₂ iT₂ s₂ σ₂ → GlobalTheory.PowUnif.EvenAlong we iT s σ := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂
    hM hM₁ hM₂ hL hL₁ hL₂ e₁ e₂ e₃ e₄ we Q iT iT₁ iT₂ iG iG₁ iG₂ iB iB₁ iB₂ s s₁ s₂ σ σ₁ σ₂
    ih₁ ih₂ iF iP iF₁ iP₁ iF₂ iP₂ Hs Hσ ev₁ ev₂
  intro jS jT cS cT V k₁ k₂ k₃ k₄
  refine unit_ext fun z hz => ?_
  obtain ⟨n₁, n₂⟩ := GlobalTheory.EvenPull.even_stalk we s σ jS jT V k₁ k₂ k₃ k₄ (𝟙 T) z hz
  refine n₁.trans (Eq.trans ?_ n₂.symm)
  clear n₁ n₂
  obtain ⟨J, hJ, hJj⟩ := exists_good M hM z (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT cT
    (fun k => Set.mem_iInter.1 (k₁ hz) k)
  obtain ⟨N, hN, hNj⟩ := exists_good L hL z (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS cS
    (fun k => Set.mem_iInter.1 (k₄ hz) k)
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at hM₁ z
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at hM₂ z
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.BoxFamily.exists_good_at hL₁ z
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.BoxFamily.exists_good_at hL₂ z

  have hb₁ : (p ≫ iB) ≫ b₁ = (h₁ ≫ p₁) ≫ iB₁ := by
    rw [← iP, Category.assoc, e₁, ← Category.assoc, ih₁, Category.assoc, iP₁, Category.assoc]
  have hb₂ : (p ≫ iB) ≫ b₂ = (h₂ ≫ p₂) ≫ iB₂ := by
    rw [← iP, Category.assoc, e₂, ← Category.assoc, ih₂, Category.assoc, iP₂, Category.assoc]
  have hg₁ : (f ≫ iG) ≫ g₁ = (h₁ ≫ f₁) ≫ iG₁ := by
    rw [← iF, Category.assoc, e₃, ← Category.assoc, ih₁, Category.assoc, iF₁, Category.assoc]
  have hg₂ : (f ≫ iG) ≫ g₂ = (h₂ ≫ f₂) ≫ iG₂ := by
    rw [← iF, Category.assoc, e₄, ← Category.assoc, ih₂, Category.assoc, iF₂, Category.assoc]
  have QQ : ∀ k, om wM z J₁ J₂ J (p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) *
        gw we ((![iT, 𝟙 T] : Fin 2 → _) k) z (J (p ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
          (fun _ => N (f ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) =
      gw we₁ ((![h₁ ≫ iT₁, h₁] : Fin 2 → _) k) z (J₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
          (fun _ => N₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k)) *
        gw we₂ ((![h₂ ≫ iT₂, h₂] : Fin 2 → _) k) z (J₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
          (fun _ => N₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k)) *
        om wL z N₁ N₂ N (f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · have q := Q T iT z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      rw [iP, iF, ih₁, ih₂, hb₁, hb₂, hg₁, hg₂] at q
      simpa only [Matrix.cons_val_zero] using q
    · have q := Q T (𝟙 T) z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      simp only [Category.id_comp] at q
      rw [e₁, e₂, e₃, e₄] at q
      simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Category.comp_id] using q
  have HM := Hσ T p z J₁ J₂ J hJ₁ hJ₂ hJ
  rw [e₁, e₂] at HM
  have HL := Hs T f z N₁ N₂ N hN₁ hN₂ hN
  rw [e₃, e₄] at HL
  have H₁ : val σ₁ (h₁ ≫ p₁) z J₁ = (∏ k, gw we₁ ((![h₁ ≫ iT₁, h₁] : Fin 2 → _) k) z
      (J₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
      (fun _ => N₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
      val s₁ (h₁ ≫ f₁) z N₁ :=
    ev₁.stalk iF₁ iP₁ h₁ z _ _
      (fun a b e => congrArg N₁ ((Category.assoc _ _ _).trans ((congrArg (h₁ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun a b e => congrArg J₁ ((Category.assoc _ _ _).trans ((congrArg (h₁ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun k => hN₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k))
      (fun k => hJ₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
  have H₂ : val σ₂ (h₂ ≫ p₂) z J₂ = (∏ k, gw we₂ ((![h₂ ≫ iT₂, h₂] : Fin 2 → _) k) z
      (J₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
      (fun _ => N₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
      val s₂ (h₂ ≫ f₂) z N₂ :=
    ev₂.stalk iF₂ iP₂ h₂ z _ _
      (fun a b e => congrArg N₂ ((Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun a b e => congrArg J₂ ((Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun k => hN₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k))
      (fun k => hJ₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
  have R := rel_alg (![1, -1] : Fin 2 → ℤ) _ _ _ _ _ QQ HM HL H₁ H₂
  rw [val_of σ p z J jT hJj, val_of s f z N jS hNj, Fin.prod_univ_two] at R
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg] at R
  have a₀ : J (p ≫ iB) = jT 0 := hJj 0
  have a₁ : J (p ≫ 𝟙 B) = jT 1 := hJj 1
  have c₀ : N (f ≫ iG) = jS 0 := hNj 0
  have c₁ : N (f ≫ 𝟙 G) = jS 1 := hNj 1
  rw [a₀, a₁, c₀, c₁] at R
  simp only [Category.id_comp]
  rw [R, mul_right_comm, inv_mul_cancel_right]

end GlobalTheory.ProdUnif
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PoincareKer.mem_fil_left : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [Nontrivial R]
    (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left,
    AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
    ∀ x : HdR A, (∀ y ∈ Fil B, φ x y = 0) → x ∈ Fil A := by
  intro hHdR R _ _ A B _ _ g hA hB hgA hgB P hP φ hφ x hx
  have hφ' := GlobalTheory.T.poincareCrystalPairing_swap_eq_neg_flip R A B P hP.isLB φ hφ
  refine GlobalTheory.T.mem_hodgeFiltration_of_orthogonal_perfectPairing hHdR R B A g hB hA hgB hgA (AbDual.swap P) hP.swap (-φ.flip) hφ' x ?_
  intro y hy
  simp [hx y hy]
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.kodaira_spencer_canonical_divisor : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z), y ∉ U₀ TF.X Z → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∀ (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) → (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) → ∃ (V' : (Y₀ TF.X Z).Opens) (_ : y ∈ V') (hle : V' ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι) (j : (common₀ TF.X Z).J) (u : Γ(Y₀ TF.X Z, V')), V' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ V' ≤ (common₀ TF.X Z).U j ∧ (∀ z (hz : z ∈ V'), IsUnit (ger z hz u)) ∧ ∀ z (hz : z ∈ V') (ho : z ∈ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off) (hc : z ∈ (LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)).U (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j)), ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z (hle hz) t * H0.germ (p := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str) (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j) z ho hc ω₀.ω = ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z hz u := by
  first | exact @GlobalTheory.LogPole.simple_pole | exact GlobalTheory.LogPole.simple_pole | (intros; apply GlobalTheory.LogPole.simple_pole <;> assumption)
end
