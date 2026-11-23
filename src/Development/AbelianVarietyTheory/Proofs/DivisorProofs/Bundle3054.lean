module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2961
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2965
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2969
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
open MeasureTheory GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchPull

open Set

theorem setIntegral_pull {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {p : X ⟶ Sp k} {e : ℕ} (hX : IsArithVar p e) (g : Y ⟶ X) (hY : IsArithVar (g ≫ p) e)
    (hη : g (genericPoint Y) = genericPoint X) (hδ : g.residueDegree (genericPoint Y) ≠ 0)
    (N : HermLB p) (σ : k →+* ℂ) (U : X.Opens) (hU : genericPoint X ∈ U)
    (f : CxPts p σ → ℝ) (hf : ContinuousOn f (ptsIn p σ U))
    (S' : Set (CxPts (g ≫ p) σ)) (hsub : ptsIn (g ≫ p) σ (g ⁻¹ᵁ U) ⊆ S')
    (f' : CxPts (g ≫ p) σ → ℝ)
    (hf' : EqOn f' (fun y => f (PtsOver.map g rfl _ y)) (ptsIn (g ≫ p) σ (g ⁻¹ᵁ U)))
    (ε : ℤˣ) :
    ∫ y in S', f' y ∂((N.restr g).φ σ).chernPart e ε =
      (g.residueDegree (genericPoint Y) : ℝ) * ∫ x in ptsIn p σ U, f x ∂(N.φ σ).chernPart e ε := by
  obtain ⟨V, hVη, hV⟩ := GlobalTheory.CoverDeg.exists_open_covering_charts hX hY g rfl hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hV σ
  set F := PtsOver.map g (rfl : g ≫ p = g ≫ p) (spMap σ) with hFdef
  have hFm : Measurable F := (PtsOver.continuous_map _ _ _).measurable
  have hpre : ∀ W : X.Opens, F ⁻¹' ptsIn p σ W = ptsIn (g ≫ p) σ (g ⁻¹ᵁ W) := by
    intro W
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hUm : MeasurableSet (ptsIn p σ U) := (isOpen_ptsIn U).measurableSet
  have hVm : MeasurableSet (ptsIn p σ V) := (isOpen_ptsIn V).measurableSet
  have h0 : (N.φ σ).chernPart e ε (ptsIn p σ V)ᶜ = 0 := by
    have h := GlobalTheory.ChernNull.chernPart_over_closed hX ((V : X.Opens) : Set X)ᶜ
      V.isOpen.isClosed_compl (by simp [hVη]) σ (N.φ σ) ε
    convert h using 2
    ext y
    simp [mem_ptsIn]
  have hmeas : (g.residueDegree (genericPoint Y) : ℝ≥0∞) •
      ((N.φ σ).chernPart e ε).restrict (ptsIn p σ U) =
      Measure.map F ((((N.φ σ).pull g rfl).chernPart e ε).restrict
        (F ⁻¹' (ptsIn p σ U ∩ ptsIn p σ V))) := by
    ext A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA, Measure.map_apply hFm hA,
      Measure.restrict_apply (hFm hA), ← Set.preimage_inter,
      GlobalTheory.CoverChern.chernPart_preimage_of_cover hX hY g rfl (N.φ σ) (N.cInf σ) ε (ptsIn p σ V)
        (isOpen_ptsIn V) _ hcard hchart hlift
        (fun c c' hc w hw => GlobalTheory.PullChartDens.chernDens_pull_of_chart g rfl (N.φ σ) (N.cInf σ)
          c c' hc w hw) _
        (hA.inter (hUm.inter hVm)) (fun x hx => hx.2.2), smul_eq_mul, ← Set.inter_assoc,
      measure_inter_conull h0]
  set T' := F ⁻¹' (ptsIn p σ U ∩ ptsIn p σ V) with hT'
  have hT'eq : T' = ptsIn (g ≫ p) σ (g ⁻¹ᵁ U) ∩ ptsIn (g ≫ p) σ (g ⁻¹ᵁ V) := by
    rw [hT', Set.preimage_inter, hpre, hpre]
  have hT'm : MeasurableSet T' := hFm (hUm.inter hVm)
  have hT'U : T' ⊆ ptsIn (g ≫ p) σ (g ⁻¹ᵁ U) := by
    rw [hT'eq]; exact Set.inter_subset_left
  have h0' : ((N.φ σ).pull g rfl).chernPart e ε T'ᶜ = 0 := by
    have h := GlobalTheory.ChernNull.chernPart_over_closed hY (g ⁻¹' ((U ⊓ V : X.Opens) : Set X)ᶜ)
      ((U ⊓ V).isOpen.isClosed_compl.preimage g.continuous) (by simp [hη, hU, hVη]) σ
      ((N.φ σ).pull g rfl) ε
    convert h using 2
    rw [hT'eq]
    ext y
    simp [mem_ptsIn]

  have hae : S' =ᵐ[((N.φ σ).pull g rfl).chernPart e ε] T' := by
    refine ae_eq_set.2 ⟨measure_mono_null (fun x hx => hx.2) h0', ?_⟩
    rw [Set.diff_eq_empty.2 (hT'U.trans hsub)]
    exact measure_empty
  have hfm : AEStronglyMeasurable f (Measure.map F ((((N.φ σ).pull g rfl).chernPart e ε).restrict T')) := by
    rw [← hmeas]
    exact (hf.aestronglyMeasurable hUm).smul_measure _
  calc ∫ y in S', f' y ∂((N.restr g).φ σ).chernPart e ε
      = ∫ y in T', f' y ∂((N.φ σ).pull g rfl).chernPart e ε := setIntegral_congr_set hae
    _ = ∫ y in T', f (F y) ∂((N.φ σ).pull g rfl).chernPart e ε :=
        setIntegral_congr_fun hT'm (hf'.mono hT'U)
    _ = ∫ x, f x ∂Measure.map F ((((N.φ σ).pull g rfl).chernPart e ε).restrict T') :=
        (integral_map hFm.aemeasurable hfm).symm
    _ = _ := by
        rw [← hmeas, integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul]

theorem archInt_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (e : ℕ), IsArithVar p e → IsArithVar q e → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), g.residueDegree (genericPoint Y) ≠ 0 → ∀ (M N : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (N.pull g hg).archInt (M.pull g hg) e (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = (g.residueDegree (genericPoint Y) : ℝ) * N.archInt M e hr := by
  intro k _ X Y _ _ p q e hX hY g hg hη hδ M N r hr
  subst hg
  have hη' : g (genericPoint Y) ⤳ genericPoint X := hη ▸ specializes_rfl
  have hU : genericPoint X ∈ (M.div hr).supp.compl := (M.div hr).genericPoint_notMem_supp
  have key : ∀ σ : k →+* ℂ,
      ((N.restr g).φ σ).chernInt e
        (offSupp (g ≫ p) σ ((M.restr g).div (MultPull.isRatSec_pull_map g hη' hr)))
        (logNorm ((M.restr g).φ σ) (fun c => Units.map (TrueGeo.SmallSec.fnMap g hη').toMonoidHom
          (r (c PUnit.unit)))) =
      (g.residueDegree (genericPoint Y) : ℝ) *
        (N.φ σ).chernInt e (offSupp p σ (M.div hr)) (logNorm (M.φ σ) r) := by
    intro σ
    have hsub := fun (y : CxPts (g ≫ p) σ) (hy : y ∈ ptsIn (g ≫ p) σ (g ⁻¹ᵁ (M.div hr).supp.compl)) =>
      ArchIntAlter.mem_offSupp_pull M g hη' hr hy
    have hf' := fun (y : CxPts (g ≫ p) σ) (hy : y ∈ ptsIn (g ≫ p) σ (g ⁻¹ᵁ (M.div hr).supp.compl)) =>
      ArchIntAlter.logNorm_pull M g hη' hr hy
    have hc := ArchIntAlter.continuousOn_logNorm (M.φ σ) hr (M.cInf σ)
    unfold Weight.chernInt
    rw [setIntegral_pull hX g hY hη hδ N σ _ hU _ hc _ hsub _ hf' 1,
      setIntegral_pull hX g hY hη hδ N σ _ hU _ hc _ hsub _ hf' (-1), mul_sub]
    rfl
  unfold HermLB.archInt
  refine (finsum_congr key).trans ?_
  exact (mul_finsum _ _).symm

end GlobalTheory.ArchPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem _root_.GlobalTheory.T.torsionPointOperator_symmetricFrame_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (p : QkPt D.toPre (Kb R) N) (w : GlobalTheory.UT.Frm D.toPre (Kb R) N p.g.b) (p' : QkPt D.toPre F N) (w' : GlobalTheory.UT.Frm D.toPre F N p'.g.b), GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p' w' → QkExt em.toRingHom p p' → ∀ s s₁, PhiRel D.toPre (Kb R) N p w s s₁ → PhiRel D.toPre F N p' w' (famExt D.toPre em N s) (famExt D.toPre em N s₁) := by
  first | exact @GlobalTheory.Mum.Desc.phiRel_famExt | exact GlobalTheory.Mum.Desc.phiRel_famExt | (intros; apply GlobalTheory.Mum.Desc.phiRel_famExt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem _root_.GlobalTheory.T.thetaGroup_symmetricLift_action_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (x : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → SymLift A.A A.L N N (baseEm em ≫ x) θ' → ∀ t t' : SecF A (Kb R) N, IsActOf A.A A.L N θ t t' → IsActOf A.A A.L N θ' (secExt A em N t) (secExt A em N t') := by
  first | exact @GlobalTheory.Mum.Desc.isActOf_secExt | exact GlobalTheory.Mum.Desc.isActOf_secExt | (intros; apply GlobalTheory.Mum.Desc.isActOf_secExt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem _root_.GlobalTheory.T.exists_linearMap_thetaGroup_action_sections : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), ∃ b : SecF A F N →ₗ[F] SecF A F N, ∀ t t' : SecF A F N, IsActOf A.A A.L N θ t t' ↔ t' = b t := by
  first | exact @GlobalTheory.Mum.Desc.exists_linear_isActOf | exact GlobalTheory.Mum.Desc.exists_linear_isActOf | (intros; apply GlobalTheory.Mum.Desc.exists_linear_isActOf <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem _root_.GlobalTheory.T.lineBundlePowSections_algClosure_fieldBaseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), letI : Algebra (Kb R) F := em.toRingHom.toAlgebra; GlobalTheory.FieldBaseChange.IsExtension (secExt A em N) := by
  first | exact @GlobalTheory.Mum.Desc.isExtension_secExt | exact GlobalTheory.Mum.Desc.isExtension_secExt | (intros; apply GlobalTheory.Mum.Desc.isExtension_secExt <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)


theorem _root_.GlobalTheory.T.hodgeBundlePullbackGenOfFrame_isGen : ∀ {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a), (gen h ha).IsGen := by
  first | exact @GlobalTheory.HodgeFrameGen.gen_isGen | exact GlobalTheory.HodgeFrameGen.gen_isGen | (intros; apply GlobalTheory.HodgeFrameGen.gen_isGen <;> assumption)
end
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)


theorem _root_.GlobalTheory.T.hodge_frame_generator_value_pullback : ∀ {S' T Z : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) (r : Z ⟶ T) {B : Over Z} [GrpObj B] {ρ : B.left ⟶ H.left}
    (q : IsGrpPullback B H r ρ) (x' : Z ⟶ S') (ψ' : B.left ⟶ G.left) (h' : IsGrpPullback B G x' ψ'),
    r ≫ x = x' → ρ ≫ ψ = ψ' → ∀ {b : Fin g → Γ(omega B, ⊤)} (hb : IsFrame b),
    (∀ i, b i = (omegaBase q).app ⊤ (pullbackSections r _ le_top (a i))) → ∀ (z : Z)
    (J : (Z ⟶ S') → (hodge G g).ι), Good (hodge G g) z J →
    val (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J =
      val (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J := by
  first | exact @GlobalTheory.HodgeFrameGen.val_gen_pull | exact GlobalTheory.HodgeFrameGen.val_gen_pull | (intros; apply GlobalTheory.HodgeFrameGen.val_gen_pull <;> assumption)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

theorem _root_.GlobalTheory.T.torusPointSection_along_spreadingTrait : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁] (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂] (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left) (ρ : D₂.toPre.X →+ D₁.toPre.X), Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (o : Type) [CommRing o] (s : B ⟶ Sp o) (o₁ : o →+* V₁) (o₂ : o →+* V₂), ξ₁ ≫ s = spMap o₁ → ξ₂ ≫ s = spMap o₂ → ∀ (k : ℕ) (ζ : o), 1 ≤ k → ζ ^ k = 1 → ∀ (Wo : B.Opens) (h : Wo.toScheme ⟶ H.left) (ξ₁' : Sp V₁ ⟶ Wo.toScheme) (ξ₂' : Sp V₂ ⟶ Wo.toScheme), h ≫ H.hom = Wo.ι → ξ₁' ≫ Wo.ι = ξ₁ → ξ₂' ≫ Wo.ι = ξ₂ → ∀ (c : D₁.toPre.X →+ ℤ), (∀ (κ : Type) [Field κ] (b : V₁ →+* κ) (hb : ∀ y ∈ maximalIdeal V₁ ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G₁.left) (hm : IsGrpPullback Gκ G₁ (spMap b) m) (τ : Multiplicative D₁.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b (o₁ ζ) ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D₁.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ ξ₁' ≫ h = (z ≫ GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb hm).left ≫ m ≫ β₁) → ∃ (κ : Type) (_ : Field κ) (b : V₂ →+* κ) (hb : ∀ y ∈ maximalIdeal V₂ ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) (_ : GrpObj Gκ) (m : Gκ.left ⟶ G₂.left) (hm : IsGrpPullback Gκ G₂ (spMap b) m) (τ : Multiplicative D₂.toPre.X →* κˣ) (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D₂.toPre.X), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b (o₂ ζ) ^ (c.comp ρ) χ) ∧ (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) ∧ spMap b ≫ ξ₂' ≫ h = (z ≫ GlobalTheory.TorusPart.gtTorus (U₂.gt 0) hb hm).left ≫ m ≫ β₂ := by
  first | exact @GlobalTheory.SpreadTorSection.trait_section | exact GlobalTheory.SpreadTorSection.trait_section | (intros; apply GlobalTheory.SpreadTorSection.trait_section <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

theorem _root_.GlobalTheory.T.exists_semiAbelianEnd_extending_abelianSchemeEnd : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ f : ρ.P.A ⟶ ρ.P.A, IsMonHom f → ∃ Fm : FinalForm.G ⟶ FinalForm.G, EndOn FinalForm f Fm := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.endOn_exists | exact GlobalTheory.Poinc.Sep.Spz.endOn_exists | (intros; apply GlobalTheory.Poinc.Sep.Spz.endOn_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

theorem _root_.GlobalTheory.T.abelianScheme_pullback_semiAbelian_over_normalDomain : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Algebra O Ω] [IsFractionRing O Ω] (x : Sp O ⟶ M.Z) (u : S.R →+* O), spMap (algebraMap O Ω) ≫ x = M.pt → (algebraMap O Ω).comp u = S.R.val.toRingHom → ∃ gm : ((Over.pullback (spMap u)).obj ρ.P.A).left ⟶ FinalForm.G.left, Link FinalForm x (spMap u) ((Over.pullback (spMap u)).obj ρ.P.A) (pullback.fst ρ.P.A.hom (spMap u)) gm := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.link_of_normal | exact GlobalTheory.Poinc.Sep.Spz.link_of_normal | (intros; apply GlobalTheory.Poinc.Sep.Spz.link_of_normal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) (θ : P.L.L.Sec) (T : Over S) (x a b c : T ⟶ G) (W : T.left.Opens), (∀ f ∈ cubeTen x a b c, W ≤ f.left ⁻¹ᵁ secNz θ) → ∃ t : LB.Gen (P.L.L.pull (W.ι ≫ x.left)), t.IsGen := by
  first | exact @GlobalTheory.Mum.exists_gen_of_cubeTen | exact GlobalTheory.Mum.exists_gen_of_cubeTen | (intros; apply GlobalTheory.Mum.exists_gen_of_cubeTen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.mem_subringClosure_of_isIntegralElem_affineOpen_le : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) (V W : S.Opens) (hWV : W ≤ V),
    IsAffineOpen V → IsAffineOpen W → ∀ b : Γ(Sp K, gp ⁻¹ᵁ W), (gp.app W).hom.IsIntegralElem b →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ s, (gp.app V).hom.IsIntegralElem y) ∧
      b ∈ Subring.closure (Set.range (gp.app W).hom ∪ resK gp hWV '' (s : Set _)) := by
  first | exact @GlobalTheory.Mum.mem_closure_of_isIntegralElem_affine_le | exact GlobalTheory.Mum.mem_closure_of_isIntegralElem_affine_le | (intros; apply GlobalTheory.Mum.mem_closure_of_isIntegralElem_affine_le <;> assumption)
end
