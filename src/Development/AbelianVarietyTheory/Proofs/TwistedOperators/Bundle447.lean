module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusCompactQuotientFiniteVolume
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle274
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle404
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle262
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1992
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle179
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle413
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle414
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv

@[expose] public section

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrClassTerm

theorem integrable_descend_of_stdDom {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} {φ : G → ℂ} (hi : LeftInv Γ φ) (h : IntegrableOn φ (stdDom Γ) μ) :
    Integrable (descend Γ φ) (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ∧
      ∫ q, descend Γ φ q ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ = ∫ x in stdDom Γ, φ x ∂μ := by
  have e : descend Γ φ = φ ∘ sec Γ := funext fun q => by
    rw [Function.comp_apply, ← hi.descend_mk, mk_sec]
  rw [e]
  exact ⟨(measurePreserving_sec.integrable_comp_emb measurableEmbedding_sec).2 h,
    measurePreserving_sec.integral_comp measurableEmbedding_sec φ⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem continuous_tensor {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L]
    {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}
    (ha : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) (hf : IsFinFamily σ J L ff) :
    Continuous (tensor σ J fa ff) ∧ HasCompactSupport (tensor σ J fa ff) := by
  have hb := hf.tensorFin_mem
  have h1 : Continuous (tensorInf σ J fa) :=
    continuous_finsetProd _ fun w _ => (ha w).1.comp (continuous_projInfArch σ J w)
  have h2 : HasCompactSupport (tensorInf σ J fa) := by
    refine .intro ((infContEquivPi σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_univ_pi fun w => (ha w).2)) fun g hg => ?_
    by_contra hne
    exact hg fun w _ => subset_tsupport _ (Finset.prod_ne_zero_iff.1 hne w (Finset.mem_univ w))
  rw [tensor_eq_infFin]
  refine ⟨(h1.comp (continuous_projInf σ J)).mul (hb.1.continuous.comp (continuous_projFin σ J)), .intro
    ((infFinEquiv σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (IsCompact.prod h2 hb.2)) fun g hg => ?_⟩
  by_contra hne
  exact hg ⟨subset_tsupport _ (left_ne_zero_of_mul hne), subset_tsupport _ (right_ne_zero_of_mul hne)⟩

theorem isMulCommutative_cent_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) : IsMulCommutative (cent (ratEmb σ J γ)) :=
  ⟨⟨fun a b => Subtype.ext (GAd_ext σ J
    (fun w => by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val
        ((isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)).1.1
          (centMap (projArch σ J w) _ a) (centMap (projArch σ J w) _ b)))
    fun v => by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val
        ((isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)).1.1
          (centMap (proj σ J v) _ a) (centMap (proj σ J v) _ b)))⟩⟩

theorem class_term : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), XSet P (Fv F v) J) (qa : ∀ w : InfinitePlace F, XSet P w.Completion J), (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v).1) → (∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w).1) → Integrable (descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff))) (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff)) q ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * ((∏ᶠ v, orbCls (μf v) (dtf v) (ff v) (qf v)) * ∏ w, orbCls (μa w) (dta w) (fa w) (qa w)) := by
  intro F E _ _ _ _ _ σ hcm r P J hJ L _ μa μf μ hμ fa ff hfa hff dta dtf dt hdt γ hγ qf qa hqf hqa
  have hreg : IsRegSS γ.1.1 := by
    rw [IsRegSS, hγ]; exact P.2.2.1.separable
  obtain ⟨ea, ef, e, hc, ⟨𝓣, h𝓣, hvol⟩, hf, ha⟩ := GlobalTheory.T.exists_centralizer_measures_from_unitaryTorus F E σ hcm r P J hJ L γ hγ dta dtf dt hdt
  obtain ⟨pf, pa⟩ := GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ
  have := hμ.haar
  have := hc.1
  have := hc.2.1
  have := hc.2.2.1
  have : ∀ w, (ea w).IsMulRightInvariant := fun w =>
    isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hreg w)) _
  have : ∀ v, (ef v).IsMulRightInvariant := fun v =>
    isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_proj_ratEmb hreg v)) _
  have hf' : ∀ v, HasOrbInt (μf v) (proj σ J v (ratEmb σ J γ)) (ef v) (ff v) (orbCls (μf v) (dtf v) (ff v) (qf v)) :=
    fun v => by
      obtain ⟨x, φ, h, e1, e2⟩ := hqf v
      have := (pf v (μf v) (dtf v) (ff v) (hμ.haar_loc v) (IsRestrictedProd.haar_loc hdt v) (hff.1 v).1.continuous
        (hff.1 v).2).2 x φ h
      rw [show qf v = ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ from Subtype.ext e1.symm]
      exact (hf v x φ h e2 _ _ _).1 this
  have ha' : ∀ w, HasOrbInt (μa w) (projArch σ J w (ratEmb σ J γ)) (ea w) (fa w)
      (orbCls (μa w) (dta w) (fa w) (qa w)) := fun w => by
    obtain ⟨x, φ, h, e1, e2⟩ := hqa w
    have := (pa w (μa w) (dta w) (fa w) (hμ.haar_arch w) (IsRestrictedProd.haar_arch hdt w) (hfa w).1
      (hfa w).2).2 x φ h
    rw [show qa w = ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ from Subtype.ext e1.symm]
    exact (ha w x φ h e2 _ _ _).1 this
  have hO := (hasOrbInt_tensor_of_hasOrbInt hμ hc hff.2 (eventually_conj_mem_stabLoc hcm hJ L hreg) ha' hf').2
  have hfin := (GlobalTheory.T.unitaryTorus_compact_quotient_finite_volume F E σ hcm r P).2 dt (IsRestrictedProd.haar hdt)
  have ht := continuous_tensor hfa hff
  obtain ⟨-, h1, h2⟩ := GlobalTheory.T.classTerm_eq_volume_mul_orbitalIntegral (GAd σ J) (ratPts σ J) (ratEmb σ J γ) (range_ratEmb σ J ▸ ⟨γ, rfl⟩)
    (isMulCommutative_cent_ratEmb hreg) μ e 𝓣 h𝓣 (hvol ▸ hfin.lt_top) _ _ ht.1 ht.2 hO _
    (isFundamentalDomain_stdDom _ μ)
  obtain ⟨h3, h4⟩ := integrable_descend_of_stdDom
    (fun g hg x => GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel_mul (ratEmb σ J γ) (tensor σ J fa ff) hg x) h1
  refine ⟨h3, ?_⟩
  rw [h4, h2, Measure.real, hvol, mul_comm (∏ w, _)]

end GlobalTheory.TrClassTerm
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.GoodStableGiven

theorem goodStable_of_given : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), Given R F → Formalism.L2.DIV.GoodStable A.X := by
  intro hGC D G _ _ Pl0 T A Ks _ _ _ R F h
  obtain ⟨om, hT⟩ := GlobalTheory.T.exists_tameCharacters_seriesIdempotentsTameLabelled R F h
  exact GlobalTheory.GoodStableDual.goodStable_of_irr R F h.irr h.core.grp om
    (GlobalTheory.GoodIdemTie.idemTie_of_tameTie hGC D om hT)

end GlobalTheory.GoodStableGiven

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.good_forms_le_range_theta_adjoint_base_tuple : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ j, U2.goodW A3 (R.toCx3 F) j ≤ LinearMap.range ((R.toCx3 F).θ' j A3.A.fam.μ0) := by
  exact @GlobalTheory.LiftOntoGood.goodW_le_range
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDualStep

variable {D : D7}

theorem actO_one_left (S T : HSp D) (h : GA D T) (Z : WO S T) :
    actO S T 1 h Z = HMul.hMul (Formalism.L2.Theta.mt T h) (Z : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
  unfold actO
  simp [Formalism.L2.Theta.mt]

theorem infPart_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : infPart D e = 0 := by
  classical
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  subst hsum
  induction P using Finset.induction_on with
  | empty => rw [Finset.sum_empty, RingHom.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem (hes a (Finset.mem_insert_self a s)).1,
      ih fun PP hPP => hes PP (Finset.mem_insert_of_mem hPP), add_zero]

def finLift {m n : ℕ} (c : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  Matrix.of fun a b => pairA D.host.F 0 1 ⊗ₜ[D.host.F] c a b

theorem smul_map_incA {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {m n : ℕ}
    (c : Matrix (Fin m) (Fin n) D.host.E) :
    e • c.map (incA D) = e • finLift c := by
  ext a b
  simp only [finLift, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [map_mul, map_mul, infPart_idemSum he, zero_mul, zero_mul]
  · rw [map_mul, map_mul, GlobalTheory.LatVac.finPart_pair, GlobalTheory.LatVac.finPart_incA]

theorem homLat_mul {a b c : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin c → D.host.E)}
    {x : Matrix (Fin c) (Fin b) D.host.E} {y : Matrix (Fin b) (Fin a) D.host.E}
    (hx : x ∈ homLat Λ' Λ'') (hy : y ∈ homLat Λ Λ') : x * y ∈ homLat Λ Λ'' := by
  show ∀ v ∈ Λ, (x * y) *ᵥ v ∈ Λ''
  intro v hv
  rw [← Matrix.mulVec_mulVec]
  exact hx _ (hy v hv)

theorem smul_homLat_mul {a b c : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin c → D.host.E)}
    {x : Matrix (Fin c) (Fin b) D.host.E} {y : Matrix (Fin b) (Fin a) D.host.E}
    (hx : x ∈ 𝔪 • homLat Λ' Λ'') (hy : y ∈ homLat Λ Λ') : x * y ∈ 𝔪 • homLat Λ Λ'' := by
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun p q hp hq => ?_)
  · rw [Matrix.smul_mul]
    exact Submodule.smul_mem_smul hr (homLat_mul hn hy)
  · rw [Matrix.add_mul]
    exact Submodule.add_mem _ hp hq

theorem hatMx_mul {a b c : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin c) (Fin b) D.host.E)}
    {N : Submodule (𝓞 D.host.E) (Matrix (Fin c) (Fin a) D.host.E)} (y : Matrix (Fin b) (Fin a) D.host.E)
    (hMN : ∀ x ∈ M, x * y ∈ N) {u : Mx D c b} (hu : u ∈ hatMx M) : u * y.map (incA D) ∈ hatMx N := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, x * y, hMN x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show _ * (Algebra.TensorProduct.includeRight (y k j)) = _
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add p q _ _ hp hq => rw [Matrix.add_mul]; exact add_mem hp hq
  | neg p _ hp => rw [Matrix.neg_mul]; exact neg_mem hp

theorem smul_one_sub {n : ℕ} (e : AE D) (A A' C : Matrix (Fin n) (Fin n) (AE D)) (h : e • A = e • C) :
    e • (1 - (A' - C)) = e • (1 + A - A') := by
  rw [smul_sub, smul_sub, smul_sub, smul_add, h]
  abel

theorem core_step {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n n' : ℕ}
    (x₀ : Matrix (Fin n) (Fin n') D.host.E) (y₀ : Matrix (Fin n') (Fin n) D.host.E)
    (mg : Matrix (Fin n) (Fin n) (AE D)) (u u' : Matrix (Fin n) (Fin n') (AE D))
    (heq : e • (x₀.map (incA D) - u) = HMul.hMul mg (e • (x₀.map (incA D) - u'))) :
    e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul u (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1))) =
      HMul.hMul mg (e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul u' (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1)))) := by
  have hxy : x₀ * y₀ = 1 + (x₀ * y₀ - 1) := by abel
  have hXY : HMul.hMul (x₀.map (incA D)) (y₀.map (incA D)) = (1 : Matrix (Fin n) (Fin n) (AE D)) + (x₀ * y₀ - 1).map (incA D) := by
    rw [← Matrix.map_mul]
    conv_lhs => rw [hxy]
    rw [Matrix.map_add (incA D) (fun a b => RingHom.map_add _ a b),
      Matrix.map_one (incA D) (RingHom.map_zero _) (RingHom.map_one _)]
  have hce := smul_map_incA he (x₀ * y₀ - 1)
  have key : ∀ v : Matrix (Fin n) (Fin n') (AE D),
      e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul v (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1))) =
        HMul.hMul (e • (x₀.map (incA D) - v)) (y₀.map (incA D)) := by
    intro v
    rw [Matrix.smul_mul, Matrix.sub_mul, hXY]
    exact smul_one_sub e _ _ _ hce
  rw [key u, key u', heq, Matrix.mul_assoc]

theorem coset_equation_mul_right_congruent_one_mod_depthIdeal : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ u ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∀ u' ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))),
    e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u')) →
    ∃ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∃ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
      e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) := by
  intro D _ T L μ0 _ sc G W M _ i _ x₀ hx₀ e he g u hu u' hu' heq
  obtain ⟨-, y₀, hy₀, hc⟩ := hx₀
  have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by simp
  have hcf : finLift (x₀ * y₀ - 1) ∈
      hatMx (G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i))) :=
    AddSubgroup.subset_closure ⟨1, h1, x₀ * y₀ - 1, hc, rfl⟩
  have hmul : ∀ x ∈ G.modul • homLat (G.latS (.core i)) (G.latT (.core i)),
      x * y₀ ∈ G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i)) := fun x hx => smul_homLat_mul hx hy₀
  refine ⟨_, sub_mem (hatMx_mul y₀ hmul hu) hcf, _, sub_mem (hatMx_mul y₀ hmul hu') hcf, ?_⟩
  rw [actO_one_left] at heq ⊢
  exact core_step he x₀ y₀ _ u u' heq

end GlobalTheory.CosDualStep
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows

theorem rowTower_of_step : RowModels → RowStep → RowTower := by
  intro hmod hstep D q hs T L μ0 hL sc hc G W M hM M₀ h₀ n
  induction n with
  | zero =>
    intro h
    refine ⟨parB (Ptw D) 0, M₀, (parRow_zero D sc.cGap).symm, h₀, fun _ w => w, fun t ht Φ => ⟨t, ht, fun ρ w => ⟨trivial, rfl⟩⟩⟩
  | succ n ih =>
    intro h
    obtain ⟨S, MA, hS, hA, vec, hvec⟩ := ih (Nat.le_of_succ_le h)
    obtain ⟨MB, hB⟩ := hmod D q hs T L μ0 hL sc hc G W M hM (n + 1) h
    obtain ⟨It, hIt⟩ := hstep D q hs T L μ0 hL sc hc G W M hM n h S _ MA MB hS rfl hA hB
    refine ⟨_, MB, rfl, hB, fun ρ w => It (ρ ⟨n, h⟩) (vec ρ w), fun t ht Φ => ?_⟩
    obtain ⟨F, hF, hF'⟩ := hvec t ht Φ
    obtain ⟨F', hF1, hF2⟩ := hIt F hF (Φ ⟨n, h⟩)
    refine ⟨F', hF1, fun ρ w => ?_⟩
    obtain ⟨h1, h2⟩ := hF' ρ w
    obtain ⟨h3, h4⟩ := hF2 (ρ ⟨n, h⟩) (vec ρ w)
    rw [← h2] at h3 h4
    exact ⟨⟨h1, h3⟩, h4⟩

end GlobalTheory.SepRows
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct nonZeroDivisors ComplexConjugate

namespace GlobalTheory.ReLatPf

variable {D : D7}

theorem theta_relat (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (r : ReLat A) (r' : ReLat B) (f : WO A B → ℂ) :
    IsThetaFunO ψ r.sp r'.sp f ↔ IsThetaFunO ψ A B f := ⟨fun h => ⟨h.1,h.2,h.3,h.4⟩, fun h => ⟨h.1,h.2,h.3,h.4⟩⟩

theorem aut_relat (V : HSp D) (r : ReLat V) (θ : InfFam D) (φ : GA D V → ℂ) : IsAutFunSm θ r.sp φ ↔ IsAutFunSm θ V φ :=
  ⟨fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩,
   fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩⟩

theorem reLatLaw_holds : ∀ D : D7, ReLatLaw D := by
  intro D
  refine ⟨fun V Λ h => ⟨⟨_, GlobalTheory.Core.Rk.DownCompare.latIn_lat h, GlobalTheory.Core.Rk.DownCompare.latIn_unimod h⟩,
      GlobalTheory.Core.Rk.DownCompare.frameLat_reset V Λ h V.sig⟩,
    fun V r θ S M J => ⟨?_, rfl, rfl, rfl, fun _ => Iff.rfl⟩, fun ψ A B r r' => ⟨theta_relat ψ A B r r', fun χS χT ω => ?_⟩⟩
  · have e : (Mult θ (r.mod M) J 1 : Submodule ℂ (MMap M)) = Mult θ M J 1 := by
      unfold Mult
      congr 1
      ext T
      exact ⟨fun h => ⟨fun v => (aut_relat V r θ _).1 (h.1 v), h.2, h.3, h.4, h.5⟩,
        fun h => ⟨fun v => (aut_relat V r θ _).2 (h.1 v), h.2, h.3, h.4, h.5⟩⟩
    exact congrArg (Submodule.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] _).toLinearMap) e
  · have t := theta_relat ψ A B r r'
    exact ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, fun p f hf => (t _).1 (h.6 p f ((t _).2 hf)),
        fun g k w f hf => h.7 g k w f ((t _).2 hf), fun γ a γ' b f hf => h.8 γ a γ' b f ((t _).2 hf),
        fun f hf => h.9 f ((t _).2 hf), fun μ X a b p f hf => h.10 μ X a b p f ((t _).2 hf),
        fun e he g k a b x y c d => (h.11 e he g k a b x y c d).imp fun _ hr => ⟨hr.1, fun l hl f hf =>
          hr.2 l (fun u hu f hf => hl u hu f ((t _).1 hf)) f ((t _).2 hf)⟩⟩,
      fun h => ⟨h.1, h.2, h.3, h.4, h.5, fun p f hf => (t _).2 (h.6 p f ((t _).1 hf)),
        fun g k w f hf => h.7 g k w f ((t _).1 hf), fun γ a γ' b f hf => h.8 γ a γ' b f ((t _).1 hf),
        fun f hf => h.9 f ((t _).1 hf), fun μ X a b p f hf => h.10 μ X a b p f ((t _).1 hf),
        fun e he g k a b x y c d => (h.11 e he g k a b x y c d).imp fun _ hr => ⟨hr.1, fun l hl f hf =>
          hr.2 l (fun u hu f hf => hl u hu f ((t _).2 hf)) f ((t _).1 hf)⟩⟩⟩

end GlobalTheory.ReLatPf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.PairLift (adjO)
noncomputable section
namespace GlobalTheory.ExchLatPf

theorem exchLat : All fun {D} _ _ _ {G} W _ => ExchLaw D → LatExch → ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' → ∀ g : WO r.sp r'.sp → ℂ, IsLatVac (heisO W.ψ r.sp r'.sp) (latO r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) fun _ => True) g → IsLatVac (heisO W.ψ (G.pS (.core i)) (G.pT (.core i))) (latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
  intro D hOff T L μ0 hLi sc G W M hM hEx hLat i hi r r' hr hr' g hg
  have hAdj := GlobalTheory.AdjLawPf.adjLaw D W.ψ W.ψ_std (G.V (.core i)) (G.V (.core (i+1)))
  have hE := (hEx W.ψ (G.V (.core i)) (G.V (.core (i+1))) W.ψ_std).2.1
  have hL := hLat D hOff T L μ0 hLi sc G W M hM i hi r r' hr hr' (fun _ => True)
  refine ⟨fun u hu => ?_, fun e he u hu hue => ?_⟩
  · refine (hE _ _).trans (congrArg _ ?_)
    have h2 : adjO (G.V (.core i)) (G.V (.core (i+1))) (2 • u) = 2 • adjO (G.V (.core i)) (G.V (.core (i+1))) u := by
      rw [two_smul, two_smul, hAdj.add]
    rw [h2]
    exact hg.1 _ ((hL u).1 hu)
  · refine (hE _ _).trans (congrArg _ ?_)
    exact hg.2 (cA D e) (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isSplitIdem_cA he) _ ((hL u).1 hu) (hAdj.half e u hue)

end GlobalTheory.ExchLatPf
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.quotient_char_partial_L_entire_nonvanishing_integers : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, i < j → j < c.m → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ j)⁻¹) w}) z) ∧ ∀ n : ℕ, 1 ≤ n → Λ n ≠ 0 := by
  first | exact @GlobalTheory.EvenOnto.QuotL.quotL_entire_ne_zero | exact GlobalTheory.EvenOnto.QuotL.quotL_entire_ne_zero | (intros; apply GlobalTheory.EvenOnto.QuotL.quotL_entire_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.measurable_level_indicator_coefficient_test_function : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v a : ∀ τ, M.H τ), Measurable (coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v a) := by
  first | exact @GlobalTheory.SepPer.CoefMeas.measurable_coef | exact GlobalTheory.SepPer.CoefMeas.measurable_coef | (intros; apply GlobalTheory.SepPer.CoefMeas.measurable_coef <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.doubleMixedModelSupportedClass_subset_splitLatticeVacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Γ : AddSubgroup (WO V W)), p.Is dV dW x ψ → Splits dV dW p x y ψ Γ → ∀ Φ ∈ cls dV dW p x y ψ, VacG ψ V W Γ Φ := by
  first | exact @GlobalTheory.AscFin.SplitVac.cls_vac | exact GlobalTheory.AscFin.SplitVac.cls_vac | (intros; apply GlobalTheory.AscFin.SplitVac.cls_vac <;> assumption)
end
