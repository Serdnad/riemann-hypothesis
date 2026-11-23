module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle472
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletionStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle307
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle238
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.PrimesOverExistence.Places
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle164
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle186
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle319
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftInertEigenvaluesIffThetaImageEigensystem
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertTypeEigenvaluesIffLabelEigensystemsRows
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle308
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle309
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

namespace GlobalTheory.AfIsoPrV

theorem prV_eq_one_iff_afIso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), Formalism.UG.prV (E := E) v z = 1 ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → GlobalTheory.Mem.Col2.afIso F E z P = 1 := by
  intro F E _ _ _ _ _ v z
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd F E
  let ι' : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E :=
    RingEquiv.ofBijective ι ⟨GlobalTheory.AdeleBaseChange.map_injective hι, GlobalTheory.AdeleBaseChange.map_surjective hι⟩
  have hiso : GlobalTheory.TwU.IsAdIso ι' :=
    ⟨GlobalTheory.AdeleBaseChange.map_tmul_one hι,
      fun y => ⟨fun hy => GlobalTheory.AdeleBaseChange.map_mem_int hι hy,
        fun hy => GlobalTheory.AdeleBaseChange.mem_int_of_map hι hy⟩⟩
  have he : ι z = GlobalTheory.Mem.Col2.afIso F E z := GlobalTheory.isAdIso_eq_afIso F E ι' hiso z
  rw [GlobalTheory.AdeleBaseChange.prV_eq_one_iff hι, he]

end GlobalTheory.AfIsoPrV
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.AboveL.DecRes

variable {Ω F E : Type} [Field Ω] [Field F] [Field E] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]
  (A : ValuationSubring Ω)

def lift (h : _root_.Formalism.ConjugateSelfDual.G F Ω) (hh : ∀ x : E, h (algebraMap E Ω x) = algebraMap E Ω x) : _root_.Formalism.ConjugateSelfDual.G E Ω :=
  { (h : Ω ≃+* Ω) with commutes' := hh }

def resHom : _root_.ReciprocityTheory.Gal.Dec (F := E) A →* _root_.ReciprocityTheory.Gal.Dec (F := F) A where
  toFun g := ⟨AlgEquiv.restrictScalarsHom F (g : _root_.Formalism.ConjugateSelfDual.G E Ω), g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem resHom_injective : Function.Injective (resHom (F := F) (E := E) A) := by
  intro g g' hgg
  apply Subtype.ext
  ext z
  have := congrArg (fun k : _root_.ReciprocityTheory.Gal.Dec (F := F) A => (k : _root_.Formalism.ConjugateSelfDual.G F Ω) z) hgg
  exact this

theorem mem_map_iff (V : Subgroup (_root_.ReciprocityTheory.Gal.Dec (F := E) A)) (g : _root_.ReciprocityTheory.Gal.Dec (F := E) A) :
    resHom (F := F) A g ∈ V.map (resHom (F := F) (E := E) A) ↔ g ∈ V :=
  (Subgroup.mem_map_iff_mem (resHom_injective (E := E) A))

variable (hfix : ∀ g ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A, ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x)
include hfix

theorem resHom_surjective : Function.Surjective (resHom (F := F) (E := E) A) := by
  intro k
  exact ⟨⟨lift (k : _root_.Formalism.ConjugateSelfDual.G F Ω) (hfix _ k.2), k.2⟩, Subtype.ext (by ext z; rfl)⟩

theorem isOpen_map [FiniteDimensional F E] (V : Subgroup (_root_.ReciprocityTheory.Gal.Dec (F := E) A)) (hV : IsOpen (V : Set (_root_.ReciprocityTheory.Gal.Dec (F := E) A))) :
    IsOpen ((V.map (resHom (F := F) (E := E) A)) : Set (_root_.ReciprocityTheory.Gal.Dec (F := F) A)) := by
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp hV
  have h1 : (1 : _root_.ReciprocityTheory.Gal.Dec (F := E) A) ∈ V := V.one_mem
  have hU1 : (1 : _root_.Formalism.ConjugateSelfDual.G E Ω) ∈ U := by
    have : (1 : _root_.ReciprocityTheory.Gal.Dec (F := E) A) ∈ Subtype.val ⁻¹' U := by rw [hUV]; exact h1
    exact this
  obtain ⟨K, hK, hKU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp (hU.mem_nhds hU1)
  haveI := hK
  haveI : FiniteDimensional F (K.restrictScalars F) :=
    (Module.Finite.trans E K : Module.Finite F K)
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  have hO : IsOpen (Subtype.val ⁻¹' ((K.restrictScalars F).fixingSubgroup : Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) : Set (_root_.ReciprocityTheory.Gal.Dec (F := F) A)) :=
    (IntermediateField.fixingSubgroup_isOpen (K.restrictScalars F)).preimage continuous_subtype_val
  refine Filter.mem_of_superset (hO.mem_nhds ((K.restrictScalars F).fixingSubgroup.one_mem)) ?_
  intro k hk
  obtain ⟨g, rfl⟩ := resHom_surjective (E := E) A hfix k
  refine ⟨g, ?_, rfl⟩
  have hgU : (g : _root_.Formalism.ConjugateSelfDual.G E Ω) ∈ U := by
    apply hKU
    intro z
    exact hk ⟨z.1, z.2⟩
  have : g ∈ Subtype.val ⁻¹' U := hgU
  rw [hUV] at this
  exact this

theorem commutator_le_map (V : Subgroup (_root_.ReciprocityTheory.Gal.Dec (F := E) A)) (hc : commutator (_root_.ReciprocityTheory.Gal.Dec (F := E) A) ≤ V) :
    commutator (_root_.ReciprocityTheory.Gal.Dec (F := F) A) ≤ V.map (resHom (F := F) (E := E) A) := by
  have hs := resHom_surjective (E := E) A hfix
  rw [commutator_def, ← Subgroup.map_top_of_surjective _ hs, ← Subgroup.map_commutator]
  exact Subgroup.map_mono (by rw [← commutator_def]; exact hc)

end GlobalTheory.AboveL.DecRes

namespace GlobalTheory.AboveL


open GlobalTheory.AboveL.DecRes in
theorem exists_cm_solvDisj_dec_eq : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w), (∀ g ∈ _root_.ReciprocityTheory.Gal.Dec (F := maximalRealSubfield E) A, ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x) → ∀ V : Subgroup (_root_.ReciprocityTheory.Gal.Dec (F := E) A), IsOpen (V : Set (_root_.ReciprocityTheory.Gal.Dec (F := E) A)) → commutator (_root_.ReciprocityTheory.Gal.Dec (F := E) A) ≤ V → ∀ N : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω), IsOpen (N : Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ ∀ g : _root_.ReciprocityTheory.Gal.Dec (F := E) A, (∀ x : M, (g : _root_.Formalism.ConjugateSelfDual.G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ↔ g ∈ V := by
  intro Ω _ E _ _ _ _ _ A w h hfix V hVo hVc N hNo
  haveI : IsAlgClosure (maximalRealSubfield E) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩
  obtain ⟨n, hn, hnv⟩ := (Formalism.MainNotions.V.Pf.ShaCmp.exists_over_iff (K := E) A).mp ⟨w, h⟩
  obtain ⟨v, hv⟩ := (Formalism.MainNotions.V.Pf.ShaCmp.exists_over_iff (K := maximalRealSubfield E) A).mpr ⟨n, hn, hnv⟩
  obtain ⟨T, hvT, hT⟩ := GlobalTheory.T.exists_cmField_lift_disjoint_of_real_solvable Ω E v N hNo
  obtain ⟨F₁, hfin, hab, hreal, hdecF, hsplit⟩ := GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion Ω (maximalRealSubfield E) A v hv
    (V.map (resHom (F := maximalRealSubfield E) (E := E) A)) (isOpen_map A hfix V hVo)
    (commutator_le_map A hfix V hVc) T hvT
  have hsolv : IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) :=
    isSolvable_of_comm fun a b => hab.toIsMulCommutative.is_comm.comm a b
  obtain ⟨M, i1, i2, i3, i4, i5, i6, i7, hSD, hM, -⟩ :=
    hT F₁ hfin hab.toIsGalois hsolv hreal hsplit
  refine ⟨M, i1, i2, i3, i4, i5, i6, i7, hSD, fun g => ?_⟩
  rw [hM (g : _root_.Formalism.ConjugateSelfDual.G E Ω), ← mem_map_iff (F := maximalRealSubfield E) A V g, ← hdecF, IntermediateField.mem_fixingSubgroup_iff]
  rfl

end GlobalTheory.AboveL
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.LabDet

theorem adjoin_common {M : Type} [AddCommGroup M] [Module ℂ M] (s : Set (Module.End ℂ M)) (u u' : M)
    (h : ∀ x ∈ s, ∃ l : ℂ, x u = l • u ∧ x u' = l • u') :
    ∀ a ∈ Algebra.adjoin ℂ s, ∃ l : ℂ, a u = l • u ∧ a u' = l • u' := by
  first
  | exact @_root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin
  | exact _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin
  | (apply _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin ..)

variable {D : D7}

theorem opOf_single {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (d : List ℤ) : opOf π P (Finsupp.single d 1) = ∑ γ ∈ rep V P d, π γ := by
  unfold opOf
  rw [Finsupp.sum_single_index (by simp), one_smul]

theorem opOf_single_of_not {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (d : List ℤ) (h : ¬ IsLab V P d) : opOf π P (Finsupp.single d 1) = 0 := by
  rw [opOf_single]
  unfold rep
  rw [dite_eq_right h, Finset.sum_empty]

theorem sphOp_rep {V : HSp D} {P : Pl D.host.E} {d : List ℤ} (h : IsLab V P d) : SphOp V P d (rep V P d) := by
  unfold rep
  rw [dite_eq_left h]
  exact h.choose_spec

theorem eq_of_split {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (hP : _root_.Formalism.DivisionValues.conjPl P ≠ P) (u u' : M) (hu : u ≠ 0) (hu' : u' ≠ 0) (fu : ∀ k ∈ hyp V P, π k u = u) (fu' : ∀ k ∈ hyp V P, π k u' = u')
    (a a' b b' : List ℤ → ℂ)
    (ha : ∀ d, IsLab V P d → opOf π P (Finsupp.single d 1) u = a d • u)
    (ha' : ∀ d, IsLab V P d → opOf π P (Finsupp.single d 1) u' = a' d • u')
    (hb : ∀ d, IsLab V (_root_.Formalism.DivisionValues.conjPl P) d → opOf π (_root_.Formalism.DivisionValues.conjPl P) (Finsupp.single d 1) u = b d • u)
    (hb' : ∀ d, IsLab V (_root_.Formalism.DivisionValues.conjPl P) d → opOf π (_root_.Formalism.DivisionValues.conjPl P) (Finsupp.single d 1) u' = b' d • u')
    (ea : ∀ k, k ≤ V.rank → a (splitLab V.rank k) = a' (splitLab V.rank k))
    (eb : ∀ k, k ≤ V.rank → b (splitLab V.rank k) = b' (splitLab V.rank k)) :
    ∀ d, IsLab V P d → a d = a' d := by
  intro d hd
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical V P hP M π d
  obtain ⟨l, h1, h2⟩ := adjoin_common _ u u' (by
    rintro y ⟨k, hk, rfl | rfl⟩
    · by_cases hl : IsLab V P (splitLab V.rank k)
      · exact ⟨_, ha _ hl, by rw [ha' _ hl, ea k hk]⟩
      · exact ⟨0, by simp [opOf_single_of_not π P _ hl], by simp [opOf_single_of_not π P _ hl]⟩
    · have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 (Finsupp.single (splitLab V.rank k) 1) M π
      have hd : dualC (Finsupp.single (splitLab V.rank k) 1) = Finsupp.single (dualLab (splitLab V.rank k)) 1 := by
        unfold dualC
        rw [Finsupp.mapDomain_single]
      rw [hd] at hc
      rw [← hc u fu, ← hc u' fu']
      by_cases hl : IsLab V (_root_.Formalism.DivisionValues.conjPl P) (splitLab V.rank k)
      · exact ⟨_, hb _ hl, by rw [hb' _ hl, eb k hk]⟩
      · exact ⟨0, by simp [opOf_single_of_not π _ _ hl], by simp [opOf_single_of_not π _ _ hl]⟩) x hx
  rw [hxe u fu, ha d hd] at h1
  rw [hxe u' fu', ha' d hd] at h2
  rw [smul_left_injective ℂ hu h1, smul_left_injective ℂ hu' h2]

def rLin (V : HSp D) (g : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun F := fun h => F (h * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rRep {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : GA D V →* Module.End ℂ (MMap M) where
  toFun g := postOn M (rLin V g)
  map_one' := by
    ext U v h
    show U v (h * 1) = U v h
    rw [mul_one]
  map_mul' g g' := by
    ext U v h
    show U v (h * (g * g')) = U v (h * g * g')
    rw [mul_assoc]

theorem rRep_apply {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GA D V) (U : MMap M) (v : M.Vec) (h : GA D V) :
    rRep M g U v h = U v (h * g) := rfl

theorem sum_rRep {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (B : Finset (GA D V)) :
    ∑ γ ∈ B, rRep M γ = heckeOn M B := by
  ext U v h
  rw [LinearMap.sum_apply, MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem mult_lev {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (U : MMap M) (hU : U ∈ Mult θ M J χ) (k : GA D V) (hk : k ∈ J)
    (h1 : χ k = 1) : rRep M k U = U := by
  induction hU using Submodule.span_induction with
  | mem x hx =>
    ext v h
    rw [rRep_apply, hx.lev v k hk h, h1, one_mul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

theorem mem_partFull {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : Pl D.host.E → List ℤ → ℂ) (U : MMap M) :
    U ∈ partFull θ M J χ Sb c ↔ U ∈ Mult θ M J χ ∧ ∀ P d B, Hecke₂ V J χ Sb P d B → heckeOn M B U = c P d • U := by
  unfold partFull
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem part_eq_of_labels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ SF, IsSF R SF → ∀ i (c c' : Pl D.host.E → List ℤ → ℂ), Wcc R SF i c ≠ ⊥ → Wcc R SF i c' ≠ ⊥ → (∀ P, Good R A.μ0 P → _root_.Formalism.DivisionValues.conjPl P ≠ P → ∀ k, k ≤ (Wc D i).rank → c P (splitLab (Wc D i).rank k) = c' P (splitLab (Wc D i).rank k)) → (∀ P d, Good R A.μ0 P → _root_.Formalism.DivisionValues.conjPl P = P → IsLab (Wc D i) P d → c P d = c' P d) → Wcc R SF i c = Wcc R SF i c' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF i c c' hc hc' hs hi
  obtain ⟨hQ, hgood, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
    GlobalTheory.T.level_operators_at_prime_off_level_datum (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P
      (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
      (by
        intro PP hPP
        refine hP PP (hPP.imp id ?_)
        intro h
        exact absurd h (Finset.notMem_empty _))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  obtain ⟨x', hx', hx0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc'
  have inj : Function.Injective (R.HW i (sg0 D A)).e := (hC.models.HW i (sg0 D A)).1
  have hu : (R.HW i (sg0 D A)).e x ≠ 0 := fun h => hx0 (inj (by rw [h, map_zero]))
  have hu' : (R.HW i (sg0 D A)).e x' ≠ 0 := fun h => hx0' (inj (by rw [h, map_zero]))
  have hp := (mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx)).2
  have hp' := (mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx')).2
  have key : ∀ P, Good R A.μ0 P → ∀ d, IsLab (Wc D i) P d → c P d = c' P d := by
    intro P hP
    by_cases hcP : _root_.Formalism.DivisionValues.conjPl P = P
    · exact fun d hd => hi P d hP hcP hd
    · have hP' : Good R A.μ0 (_root_.Formalism.DivisionValues.conjPl P) := (hgood _ P hP).2.1
      have hcc : _root_.Formalism.DivisionValues.conjPl (_root_.Formalism.DivisionValues.conjPl P) = P := ValuationRepresentative.conjPl_conjPl P
      refine eq_of_split (rRep (R.MW i (sg0 D A))) P hcP _ _ hu hu' ?_ ?_ (c P) (c' P) (c (_root_.Formalism.DivisionValues.conjPl P)) (c' (_root_.Formalism.DivisionValues.conjPl P)) ?_ ?_ ?_ ?_
        (hs P hP hcP) (hs _ hP' (by rw [hcc]; exact fun h => hcP h.symm))
      · exact fun k hk => mult_lev _ _ _ _ _ hp.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2
      · exact fun k hk => mult_lev _ _ _ _ _ hp'.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩)
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp'.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩)
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩)
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp'.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩)
  have key2 : ∀ P d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF P d B →
      c P d = c' P d := by
    intro P d B hB
    have hP : Good R A.μ0 P := by
      obtain ⟨_, _, _, _, ho, _⟩ := hB
      exact (hoff SF hSF P).1 ho
    exact key P hP d ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩
  unfold Wcc
  congr 2
  ext U
  rw [mem_partFull, mem_partFull]
  refine and_congr_right fun _ => forall_congr' fun P => forall_congr' fun d => forall_congr' fun B => imp_congr_right fun hB => ?_
  rw [key2 P d B hB]

end GlobalTheory.Hk3.LabDet

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem latAdLoc_of : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)), SplAlg A → LocInt A → Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin n → E)) = ⊤ → LatAdLoc A Lb := by
  intro F E _ _ _ _ _ n p G A Lb hS hI hfin hspan y v
  letI : StarRing E := starRingOfComm
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F) :=
    Units.val (bc (prV (E := E) (A.pl v).1) y : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) with hY
  set f : E ⊗[F] (A.pl v).1.adicCompletion F →+* G.P.Qq v :=
    ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v).comp (A.ph v) with hf
  have hfac : ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) = Y.map f := by
    rw [hY]; ext i j; rfl
  have hmv : ∀ u : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F,
      (fun k => (A.eQ v).symm (A.ph v ((Y *ᵥ u) k))) =
        ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ
          (fun k => (A.eQ v).symm (A.ph v (u k))) := by
    intro u
    rw [hfac]
    funext k
    exact RingHom.map_mulVec f Y u k
  ext z'
  rw [locSp_eq_image A hS hI v, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzz⟩
    rw [GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan] at hz
    set u := Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ z with hu
    refine ⟨fun k => (A.eQ v).symm (A.ph v (u k)), (locSp_eq_image A hS hI v Lb _).2 ⟨u, hz, fun k => rfl⟩, ?_⟩
    have hzu : z = Y *ᵥ u := by
      rw [hu, hY, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    show (facQ A v y : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ _ = z'
    rw [← hmv, ← hzu]
    funext k
    exact hzz k
  · rintro ⟨w, hw, hwz⟩
    obtain ⟨u, hu, huw⟩ := (locSp_eq_image A hS hI v Lb w).1 hw
    refine ⟨Y *ᵥ u, ?_, ?_⟩
    · have hback : Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ
          (Y *ᵥ u) = u := by
        rw [hY, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan]
      rw [hback]
      exact hu
    · intro k
      have hw' : w = fun k => (A.eQ v).symm (A.ph v (u k)) := funext fun k => (huw k).symm
      subst hwz
      subst hw'
      exact congrFun (hmv u) k

end GlobalTheory.TwV
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.every_rowOperator_is_labelOperator_with_partner : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ t, ∃ pl cX c0, RowDict R t pl cX c0 := by
  first | exact @GlobalTheory.RowDictR.rowDict_exists | exact GlobalTheory.RowDictR.rowDict_exists | (intros; apply GlobalTheory.RowDictR.rowDict_exists <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.every_liftOperator_is_labelOperator_with_partner : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ j t, ∃ pl cV cW, LiftDict R j t pl cV cW := by
  first | exact @GlobalTheory.LiftDictionary.every_op_label | exact GlobalTheory.LiftDictionary.every_op_label | (intros; apply GlobalTheory.LiftDictionary.every_op_label <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.liftInertEigenvalues_iff_thetaImageEigensystem : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → (∀ χ ∈ A3.A.X, IsAbsIrrChar χ) → ∀ (j : Fin D.R.m) (c c' : Pl D.host.E → List ℤ → ℂ) (s s' : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x x' : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ i, (A3.liftI j A3.A.μ0).opAll i x = s i • x) → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0 → (∀ i, (A3.liftI j A3.A.μ0).opAll i x' = s' i • x') → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ∈ R.Wc' j c' → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ≠ 0 → ∀ Q : A3.okI A3.A.μ0, ((∀ y : List ℕ, s (Sum.inr (Q, y)) = s' (Sum.inr (Q, y))) ↔ ∀ d, IsLab (Wc D j) (R.plI Q.1) d → c (R.plI Q.1) d = c' (R.plI Q.1) d) := by
  first | exact @GlobalTheory.Hk3.lift_inert_iff | exact GlobalTheory.Hk3.lift_inert_iff | (intros; apply GlobalTheory.Hk3.lift_inert_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inertTypeEigenvalues_iff_labelEigensystems_rows : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∀ (p p' : A3.fam3.base3.Ix) (c c' : Pl D.host.E → List ℤ → ℂ), R.Carries p c → R.Carries p' c' → ∀ Q : A3.okI A3.A.μ0, ((∀ y : List ℕ, p.1.2 (Q.1, y) = p'.1.2 (Q.1, y)) ↔ ∀ d, IsLab (Yc D 0) (R.plI Q.1) d → c (R.plI Q.1) d = c' (R.plI Q.1) d) := by
  first | exact @GlobalTheory.InertRowsEig.inert_types_iff_labels | exact GlobalTheory.InertRowsEig.inert_types_iff_labels | (intros; apply GlobalTheory.InertRowsEig.inert_types_iff_labels <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.detTwistedFrame_operatorIdentity_denominator : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → subD X Kc j G * numD X Kc j = denD X Kc j * (cD X Kc j (ι (cOp X D pos j s)) * trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) := by
  first | exact @GlobalTheory.TwV.DelA.opId_denom | exact GlobalTheory.TwV.DelA.opId_denom | (intros; apply GlobalTheory.TwV.DelA.opId_denom <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteDatum_level_pos_badPrimes_no_conjugate_pair : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => 0 < (t.rd u μ).lev ∧ ∀ Q ∈ ssRec t u μ, conjPrime₂ Q ∉ ssRec t u μ) := by
  first | exact @GlobalTheory.BadPrimes.lev_pos_and_noConj | exact GlobalTheory.BadPrimes.lev_pos_and_noConj | (intros; apply GlobalTheory.BadPrimes.lev_pos_and_noConj <;> assumption)
end
