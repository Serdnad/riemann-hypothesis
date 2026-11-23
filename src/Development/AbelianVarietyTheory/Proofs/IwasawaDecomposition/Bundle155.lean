module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle147
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle148
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolUnique

theorem haar_eq_of_eq_on_set {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure] (S : Set G) (h : μ S = μ' S)
    (h0 : μ' S ≠ 0) (ht : μ' S ≠ ⊤) : μ = μ' := by
  have hμ := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hc : ((Measure.haarScalarFactor μ μ' : NNReal) : ENNReal) = 1 := by
    have h1 : μ S = (Measure.haarScalarFactor μ μ' : ENNReal) * μ' S := by
      conv_lhs => rw [hμ]
      simp
    rw [h] at h1
    exact ((ENNReal.mul_left_inj h0 ht).1 (by rw [one_mul]; exact h1)).symm
  have hc' : Measure.haarScalarFactor μ μ' = 1 := by exact_mod_cast hc
  rw [hμ, hc', one_smul]

theorem exists_set_pos_finite (cd : CDHaar) (P Q : ℕ) :
    ∃ B : Set (UpqT P Q), MeasurableSet B ∧ cd.cd P Q B ≠ 0 ∧ cd.cd P Q B ≠ ⊤ := by
  obtain ⟨_, _, _, _, _, _⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  haveI := cd.haar P Q
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : UpqT P Q)
  exact ⟨K, hK.measurableSet, (Measure.measure_pos_of_mem_nhds _ hK1).ne', hK.measure_lt_top.ne⟩

theorem volMeas_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∀ μ μ', IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ → IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ' → μ = μ' := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W _ _ μ μ' hμ hμ'
  obtain ⟨hH, ⟨θ, hθ⟩, hall⟩ := hμ
  obtain ⟨hH', -, hall'⟩ := hμ'
  obtain ⟨⟨A, hA⟩, hB⟩ := hall θ hθ
  have hB' := (hall' θ hθ).2 A hA
  have hB := hB A hA
  choose B hBm hB0 hBt using fun ρ : I => exists_set_pos_finite cd (W.sig (τ ρ)).1 (W.sig (τ ρ)).2
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E cm.sig W.rank W.gram
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) cm.sig W.gram) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF F) cm.sig W.gram))
  haveI : BorelSpace (HA (AF F) cm.sig W.gram) := ⟨rfl⟩
  refine haar_eq_of_eq_on_set μ μ' _ ((hB B hBm).trans (hB' B hBm).symm) ?_ ?_
  · rw [hB' B hBm]
    exact Finset.prod_ne_zero_iff.2 fun ρ _ => hB0 ρ
  · rw [hB' B hBm]
    exact ENNReal.prod_ne_top fun ρ _ => hBt ρ

end GlobalTheory.Mem.VolUnique
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_iwasawa_decomposition_upperUnitriangular_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (g : GL (Fin m) k), ∃ u ∈ unipB k (Fin m), ∃ t : Fin m → kˣ, ∃ κ ∈ KO k (Fin m), g = u * diagT k (Fin m) t * κ := by
  first | exact @GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO | exact GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO | (intros; apply GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.algWt_exists_invForm' : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n), ∃ β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ, GlobalTheory.CoefDuty.IsInvForm a β := by
  first | exact @GlobalTheory.algWt_exists_invForm | exact GlobalTheory.algWt_exists_invForm | (intros; apply GlobalTheory.algWt_exists_invForm <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory

namespace GroundFieldChange

theorem finsum_const_mul_int (c : ℤ) (f : ℕ → ℤ) : ∑ᶠ n, c * f n = c * ∑ᶠ n, f n :=
  (mul_finsum f c).symm

theorem hdim_fieldChange (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0})
    [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (F : Z.Modules)
    (n : ℕ) : hdim κ F n = Module.finrank κ κ' * hdim κ' F n := by
  rw [hdim_def, hdim_def, Module.finrank_mul_finrank]

theorem chi_fieldChange (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0})
    [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (F : Z.Modules) :
    chi κ F = (Module.finrank κ κ' : ℤ) * chi κ' F := by
  rw [chi_def, chi_def, ← finsum_const_mul_int]
  refine finsum_congr fun n ↦ ?_
  rw [hdim_fieldChange κ κ' Z F n, Nat.cast_mul]
  ring

theorem interNum_fieldChange : ∀ (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0})
    [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (G : Z.Modules)
    {ι : Type} [Fintype ι] (L : ι → LB Z),
    interNum κ G L = (Module.finrank κ κ' : ℤ) * interNum κ' G L := by
  intro κ κ' _ _ _ Z _ _ _ G ι _ L
  rw [interNum_def, interNum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [chi_fieldChange κ κ' Z]
  ring

end GroundFieldChange

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.support_pushforward_subset_image : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsClosedImmersion g] (E : Y.Modules), support ((Scheme.Modules.pushforward g).obj E) ⊆ g '' support E := by
  first | exact @GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion | exact GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion | (intros; apply GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CoefSpace

section Poly

open Formalism.BasicNotions Formalism.L2.DIV MvPolynomial Matrix
open scoped ComplexOrder InnerProductSpace

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem fockL_eq {σ : Type} (f g : MvPolynomial σ ℂ) : fockL f g = Formalism.REAL.fockF g f := by
  have h := Formalism.L2.Col.map_fockS (RingHom.id ℂ) f g (fun _ => rfl)
  simp only [RingHom.id_apply, MvPolynomial.map_id] at h
  exact h

theorem map_fockL {K σ : Type} [Field K] [StarRing K] (φ : K →+* ℂ) (hφ : ∀ x, φ (star x) = star (φ x))
    (f g : MvPolynomial σ K) : φ (fockL f g) = fockL (map φ f) (map φ g) := by
  rw [fockL_eq]
  exact Formalism.L2.Col.map_fockS φ f g fun _ => hφ _

theorem map_pairP {K : Type} [Field K] [StarRing K] (φ : K →+* ℂ) (hφ : ∀ x, φ (star x) = star (φ x))
    (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n) :
    φ (pairP lam G F F') = pairP lam (fun τ => (G τ).map φ) (map φ F) (map φ F') := by
  have h1 : φ (gramTw lam G) = gramTw lam (fun τ => (G τ).map φ) := by
    simp only [gramTw, map_prod, map_zpow₀, RingHom.map_det]
    rfl
  have h2 : φ (extNorm K lam) = extNorm ℂ lam := by
    simp only [extNorm, map_prod, ← fockL_apply, map_fockL φ hφ, map_extremal]
  rw [pairP_apply, pairP_apply, map_mul, map_div₀, h1, h2, map_fockL φ hφ, Formalism.L2.Col.map_blockAct]
  rfl

theorem map_actP {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n)
    (B : ι → GL (Fin n) K) (F : Pol K ι n) :
    map φ (actP lam B F) = actP lam (fun τ => Formalism.UG.bc φ (B τ)) (map φ F) := by
  have h3 : φ (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc φ (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h3, trAct,
    Formalism.L2.Col.map_blockAct]
  rfl

def bcVV {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) : VV K lam →ₛₗ[φ] VV ℂ lam where
  toFun x := ⟨map φ x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' a x := Subtype.ext (by simp [smul_eq_C_mul])

theorem bcVV_span {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) :
    Submodule.span ℂ (Set.range fun i => bcVV φ lam (bVV K lam i)) = ⊤ := by
  rw [eq_top_iff, ← (bVV ℂ lam).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨F, hF, e⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc φ lam i
  have : bVV ℂ lam i = bcVV φ lam ⟨F, hF⟩ := Subtype.ext ((bVV_coe ℂ lam i).trans e)

  rw [this, ← (bVV K lam).sum_repr ⟨F, hF⟩, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem bcVV_indep {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) :
    LinearIndependent ℂ fun i => bcVV φ lam (bVV K lam i) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (bcVV_span φ lam).ge
    (Module.finrank_eq_card_basis (bVV ℂ lam)).symm

theorem continuous_actP {X : Type} [TopologicalSpace X] (lam : ι → DomWeight n) (g : X → ι → GL (Fin n) ℂ)
    (hg : ∀ τ, Continuous fun x => (g x τ : Matrix (Fin n) (Fin n) ℂ)) (l : Pol ℂ ι n →ₗ[ℂ] ℂ) (F : Pol ℂ ι n) :
    Continuous fun x => l (actP lam (g x) F) := by
  let G : ι → Matrix (Fin n) (Fin n) C(X, ℂ) := fun τ a b => ⟨fun x => (g x τ : Matrix (Fin n) (Fin n) ℂ) b a,
    (continuous_apply_apply b a).comp (hg τ)⟩
  let P := Formalism.GradedWeylDivisibility.blockAct C(X, ℂ) G (map (algebraMap ℂ C(X, ℂ)) F)
  have key : ∀ x, trAct (g x) F = map (ContinuousMap.evalAlgHom ℂ ℂ x : C(X, ℂ) →+* ℂ) P := by
    intro x
    have : ((trAct (g x) : Pol ℂ ι n →ₐ[ℂ] Pol ℂ ι n) : Pol ℂ ι n →+* Pol ℂ ι n) =
        (map (ContinuousMap.evalAlgHom ℂ ℂ x : C(X, ℂ) →+* ℂ)).comp
          ((Formalism.GradedWeylDivisibility.blockAct C(X, ℂ) (n := n) G).toRingHom.comp (map (algebraMap ℂ C(X, ℂ)))) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [trAct]
      · intro v
        simp [trAct, Formalism.GradedWeylDivisibility.blockAct, G]
    exact DFunLike.congr_fun this F
  have h2 : ∀ x, l (trAct (g x) F) = ∑ m ∈ P.support, (P.coeff m) x * l (monomial m 1) := by
    intro x
    rw [key]
    conv_lhs => rw [P.as_sum]

    simp only [map_sum, map_monomial]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul, h2, detTw_eq]
  refine Continuous.mul (continuous_finsetProd _ fun τ _ => (hg τ).matrix_det.zpow₀ _ fun x => Or.inl ?_)
    (continuous_finsetSum _ fun m _ => (P.coeff m).continuous.mul continuous_const)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (g x τ).isUnit).ne_zero

def gramOf (B : ι → GL (Fin n) ℂ) : ι → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => (B τ : Matrix (Fin n) (Fin n) ℂ)ᴴ * (B τ : Matrix (Fin n) (Fin n) ℂ)

theorem pairK_pos (lam : ι → DomWeight n) (B : ι → GL (Fin n) ℂ) (x : VV ℂ lam) (hx : x ≠ 0) :
    0 < pairK lam (gramOf B) x x := by
  have h := pairTransport ℂ ι n lam (fun _ => 1) B B x.1 x.1
  simp only [Matrix.mul_one] at h
  have hne : actP lam B x.1 ≠ 0 := fun h0 => hx (Subtype.ext (by
    have := congrArg (fun φ : Module.End ℂ (Pol ℂ ι n) => φ x.1) ((rhoP lam).map_mul B⁻¹ B)
    rw [inv_mul_cancel, map_one] at this
    refine this.trans ?_
    show actP lam B⁻¹ (actP lam B x.1) = 0
    rw [h0, map_zero]))
  obtain ⟨q, hq, e⟩ := extNormPos ℂ ι n lam
  rw [pairK_apply]
  unfold gramOf
  rw [← h, pairP_apply, pb_gramTw_one, pb_blockAct_one_tr, fockL_eq, e]
  refine mul_pos (one_div_pos.2 ?_) (ps_fockF_pos _ hne)
  rw [eq_ratCast, ← Complex.ofReal_ratCast]
  exact Complex.zero_lt_real.2 (by exact_mod_cast hq)

def HV (lam : ι → DomWeight n) (_B : ι → GL (Fin n) ℂ) : Type := VV ℂ lam

variable (lam : ι → DomWeight n) (B : ι → GL (Fin n) ℂ)

instance : AddCommGroup (HV lam B) := inferInstanceAs (AddCommGroup (VV ℂ lam))

instance : Module ℂ (HV lam B) := inferInstanceAs (Module ℂ (VV ℂ lam))

@[reducible] def core : InnerProductSpace.Core ℂ (HV lam B) where
  inner x y := pairK lam (gramOf B) x y
  conj_inner_symm x y := (pairSymm ℂ ι n lam (gramOf B) fun τ => by simp [gramOf]).eq _ _
  re_inner_nonneg x := by
    by_cases hx : x = 0
    · subst hx
      exact le_of_eq (congrArg Complex.re (map_zero (pairK lam (gramOf B) 0))).symm
    · exact (Complex.lt_def.1 (pairK_pos lam B x hx)).1.le
  add_left x y z := LinearMap.map_add₂ (pairK lam (gramOf B)) x y z
  smul_left x y r := LinearMap.map_smulₛₗ₂ (pairK lam (gramOf B)) r x y
  definite x hx := by
    by_contra h
    exact (pairK_pos lam B x h).ne' hx

instance : NormedAddCommGroup (HV lam B) := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (core lam B)

instance : InnerProductSpace ℂ (HV lam B) := InnerProductSpace.ofCore (core lam B).toCore

instance : FiniteDimensional ℂ (HV lam B) := (bVV ℂ lam).finiteDimensional_of_finite

theorem inner_HV (x y : HV lam B) : inner ℂ x y = pairK lam (gramOf B) x y := rfl

instance : Nontrivial (HV lam B) :=
  ⟨⟨_, (0 : VV ℂ lam), fun h => GlobalTheory.Proof.TensorMapDescent.ten_ne_zero (fun τ => extremal ℂ n (lam τ))
    (fun τ => Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _) (congrArg Subtype.val (h : (⟨_, GlobalTheory.Proof.TensorMapDescent.ten_mem lam _
      fun τ => Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (natW_antitone _)⟩ : VV ℂ lam) = 0))⟩⟩

theorem continuous_HV {X : Type} [TopologicalSpace X] (g : X → ι → GL (Fin n) ℂ)
    (hg : ∀ τ, Continuous fun x => (g x τ : Matrix (Fin n) (Fin n) ℂ)) (v : HV lam B) :
    Continuous (X := X) (Y := HV lam B) fun x => rhoK lam (g x) v := by
  have : (fun x => (rhoK lam (g x) v : HV lam B)) = fun x => ∑ i,
      pairP lam (gramOf B) (Subtype.val (stdOrthonormalBasis ℂ (HV lam B) i)) (actP lam (g x) (Subtype.val v)) •
        stdOrthonormalBasis ℂ (HV lam B) i := by
    funext x
    exact ((stdOrthonormalBasis ℂ (HV lam B)).sum_repr' _).symm
  rw [this]
  exact continuous_finsetSum _ fun i _ => (continuous_actP lam g hg _ _).smul continuous_const

end Poly

end GlobalTheory.CoefSpace
end
end

section

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.normAt_standardFrame_eq_norm_complexForm : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ), (∀ a, σ (star a) = starRingEnd ℂ (σ a)) → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W), Formalism.L2.DIV.FormsTie σ j H E op → ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x = ‖j x‖ := by
  first | exact @GlobalTheory.AmbNormTie.normAt_frm_mk | exact GlobalTheory.AmbNormTie.normAt_frm_mk | (intros; apply GlobalTheory.AmbNormTie.normAt_frm_mk <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false
noncomputable section

namespace GlobalTheory

theorem subsingleton_coh_twist_pushforward_iff {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g]
    {A N : LB X} (hA : A.IsLB) (hN : N.IsLB) (G : Y.Modules) [G.IsQuasicoherent] (j m p : ℕ) :
    Subsingleton (coh (twist G (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))) p) ↔
      Subsingleton (coh (twist ((Scheme.Modules.pushforward g).obj G)
        (tens (lbPow A j) (lbPow N m))) p) := by
  have hT : (tens (lbPow A j) (lbPow N m)).IsLB := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
  have hA' := LB.isLB_pull hA g
  have hN' := LB.isLB_pull hN g
  have hT' : (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m)).IsLB :=
    isLB_tens (isLB_lbPow hA' j) (isLB_lbPow hN' m)
  have hTp := LB.isLB_pull hT g
  have e : cls _ hT' = cls _ hTp := by
    apply (cls_eq_iff hT' hTp).2
    let a := chartPullPowPull A g j
    let b := chartPullPowPull N g m
    have c : ChartPull (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))
        (tens (lbPow A j) (lbPow N m)) g := by
      refine ⟨fun t => (a.idx t.1, b.idx t.2), fun t _ hz => ⟨a.le _ hz.1, b.le _ hz.2⟩, ?_⟩
      intro z i k hi hk
      exact (gm_tens _ _ (𝟙 Y) z i k hi hk).trans ((congrArg₂ (· * ·)
        (a.g z _ _ hi.1 hk.1) (b.g z _ _ hi.2 hk.2)).trans
          (gm_tens _ _ g z (a.idx i.1, b.idx i.2) (a.idx k.1, b.idx k.2)
            ⟨a.le _ hi.1, b.le _ hi.2⟩ ⟨a.le _ hk.1, b.le _ hk.2⟩).symm)
    exact LBIso.chartPull c (chartPullPull _ g) (PolBaseChange.lbIso_refl hT)
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq G hT' hTp e
  have := Twist.isQuasicoherent_twist (F := G) hTp
  have e₁ : coh (twist ((Scheme.Modules.pushforward g).obj G) (tens (lbPow A j) (lbPow N m))) p ≃ₗ[ℤ]
      coh (twist G (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))) p :=
    (cohOn.mapIso ℤ ⊤ p (Twist.projIso _ g G).symm).trans
      ((LinearEquiv.ofBijective (cohPushMap ℤ g (fun r => by simp) (twist G _) ⊤ p)
        (cohPushMap_bijective_of_isAffineHom ℤ g (fun r => by simp) (twist G _) ⊤ p)).trans (cohOn.mapIso ℤ ⊤ p i.symm))
  exact e₁.toEquiv.subsingleton_congr.symm

theorem twistConeVanishing_pull_iff_pushforward : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g]
    (A N : LB X), A.IsLB → N.IsLB → ∀ (G : Y.Modules) [G.IsQuasicoherent],
    (TwistConeVanishing (A.pull g) (N.pull g) G ↔
      TwistConeVanishing A N ((Scheme.Modules.pushforward g).obj G)) := by
  intro X Y g _ A N hA hN G _
  unfold TwistConeVanishing
  simp only [subsingleton_coh_twist_pushforward_iff g hA hN G]

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.adelicTwoStepMeasure_orthogonalBases_plane_compare : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b), ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x₁ : Fin 1 → Fin (M + 1) → E) (a₁ : F) (B₁ : Matrix (Fin (M + 1)) (Fin M) E) (J₁' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (a₂ : F) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (y₁ y₂ : Fin 1 → Fin M → E) (b₁ b₂ : F) (γ : GL (Fin 2) E), StepData σ J x₁ a₁ B₁ J₁' → StepData σ J x₂ a₂ B₂ J₂' → b₁ ≠ 0 → b₂ ≠ 0 → hE σ J₁' (y₁ 0) (y₁ 0) = algebraMap F E b₁ → hE σ J₂' (y₂ 0) (y₂ 0) = algebraMap F E b₂ → ![x₂ 0, B₂.mulVec (y₂ 0)] = lrAct 1 (γ : Matrix (Fin 2) (Fin 2) E) ![x₁ 0, B₁.mulVec (y₁ 0)] → ∀ (ν₁ ν₂ : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (ν₁' ν₂' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (N₁ N₂ : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E)), IsStdX s σ J a₁ ν₁ → IsStdX s σ J₁' b₁ ν₁' → IsStdX s σ J a₂ ν₂ → IsStdX s σ J₂' b₂ ν₂' → TwoStep (AF F) σ J x₁ B₁ ν₁ ν₁' N₁ → TwoStep (AF F) σ J x₂ B₂ ν₂ ν₂' N₂ → N₂ = N₁.map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F)))) := by
  first | exact @GlobalTheory.GaugeEx.twoStep_adelic_swap | exact GlobalTheory.GaugeEx.twoStep_adelic_swap | (intros; apply GlobalTheory.GaugeEx.twoStep_adelic_swap <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobenius_period_ring_injective : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (Per.φB l) := by
  first | exact @GlobalTheory.MemLoc.phiB_injective | exact GlobalTheory.MemLoc.phiB_injective | (intros; apply GlobalTheory.MemLoc.phiB_injective <;> assumption)
end

section

open Formalism.IndefR Formalism.L2.DIV

namespace GlobalTheory

theorem classPres_extMem_extBij_isom : ∀ (G Γ : Type) [Group G] [Group Γ] (ι : Γ →* G) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ), P.ExtMem ∧ P.ExtBij ∧ P.Isom := by
  intro G Γ _ _ ι W _ _ K _ _ _ S σ ρ J χ P
  obtain ⟨h1, h2, h3, -⟩ := classPres_basic ι S σ ρ J χ P
  exact ⟨h1, h3, h2⟩

end GlobalTheory
end
