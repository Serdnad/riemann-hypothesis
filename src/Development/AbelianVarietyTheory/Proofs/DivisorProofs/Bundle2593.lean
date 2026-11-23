module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle014
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle629
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRepresentingSchemePinchedBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035

@[expose] public section

section

open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem idlAlong_eq_top_of_notMem_support (X : Scheme.{0}) (I : X.IdealSheafData) (R : Type) [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ X) (h : ξ (closedPoint R) ∉ I.support) : idlAlong I ξ = ⊤ := by
  have e : FinalTheorems.stalkId I (ξ (closedPoint R)) = ⊤ :=
    not_not.1 fun h' => h ((mem_support_iff_stalkId I _).2 h')
  rw [idlAlong, e, Ideal.map_top]

end GlobalTheory.LocM
end

section

open NumberField

theorem _root_.GlobalTheory.T.complexUniformisation_components_covolume_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k k' : U.Comp, GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol (U.X k') := by
  first | exact @GlobalTheory.EqCovol.covol_eq_of_isUnf | exact GlobalTheory.EqCovol.covol_eq_of_isUnf | (intros; apply GlobalTheory.EqCovol.covol_eq_of_isUnf <;> assumption)
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
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ChartEigFrame

open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.FlagMod GlobalTheory.Reg
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem tanPull_injective_of_chart {V K : Type} [CommRing V] [CommRing K] (ρ : V →+* K) (hρ : Function.Injective ρ)
    (M : MChart Y) {x : Sp V ⟶ Y.X} {x' : Sp K ⟶ Y.X} (e : spMap ρ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ M.U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ M.U) : Function.Injective (tanPull (G := Y.t.G) ρ e) := by
  intro u u' huu
  obtain ⟨cv, rfl⟩ := (vec M x h).surjective u
  obtain ⟨cv', rfl⟩ := (vec M x h).surjective u'
  rw [tanPull_vec M ρ e h h', tanPull_vec M ρ e h h'] at huu
  have := (vec M x' h').injective huu
  congr 1
  funext j
  exact hρ (congrFun this j)

theorem exists_eigFrame_of_top {X : FlagCover Y} {V K : Type} [CommRing V] [CommRing K] [Algebra c.F K]
    (ρ : V →+* K) (hρ : Function.Injective ρ) (φ : c.F →+* V) (hφ : ρ.comp φ = algebraMap c.F K)
    (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (hz' : ⊤ ≤ (spMap ρ ≫ q) ⁻¹ᵁ X.F.U k)
    (htop : ∀ σ, initSpan K (X.F.vecAt k (spMap ρ ≫ q) hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap ρ ≫ q) ≫ X.π) σ) :
    ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (tv (X.F.vecAt k q hz rfl τ i)).left := by
  have hx : ⊤ ≤ (q ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hz rfl
  have hx' : ⊤ ≤ ((spMap ρ ≫ q) ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hz' rfl
  have e : spMap ρ ≫ (q ≫ X.π) = (spMap ρ ≫ q) ≫ X.π := (Category.assoc _ _ _).symm
  have hinj := tanPull_injective_of_chart ρ hρ (X.F.M k).toMChart e hx hx'
  have hpull : ∀ τ i, tanPull ρ e (X.F.vecAt k q hz rfl τ i) = X.F.vecAt k (spMap ρ ≫ q) hz' rfl τ i :=
    fun τ i => X.F.tanPull_vecAt k ρ q hz hz' rfl rfl e τ i
  have hmem : ∀ τ i, X.F.vecAt k (spMap ρ ≫ q) hz' rfl τ i ∈ eigLie c ((spMap ρ ≫ q) ≫ X.π) τ := fun τ i => by
    rw [← htop τ]
    exact Submodule.subset_span ⟨i, i.2, rfl⟩
  have hsmul : ∀ (τ : E →+* ℂ) (a : 𝓞 E) (w : TanM (q ≫ X.π) Y.t.G),
      tanPull ρ e (φ (embK c τ a) • w) = algebraMap c.F K (embK c τ a) • tanPull ρ e w := fun τ a w => by
    rw [map_smulₛₗ, ← hφ]
    rfl
  refine ⟨GlobalTheory.ShFam.EigFrame.ofVec (fun τ i => X.F.vecAt k q hz rfl τ i) (fun τ i a => ?_) (fun τ w hw => ?_),
    fun τ i => rfl⟩
  · apply hinj
    rw [tanPull_actR, hsmul, hpull]
    exact hmem τ i a
  · have hw' : tanPull ρ e w ∈ eigLie c ((spMap ρ ≫ q) ≫ X.π) τ := fun a => by
      rw [← tanPull_actR, hw a, hsmul]
    rw [← htop τ] at hw'
    obtain ⟨a, -, ha⟩ := mem_initSpan.1 hw'
    obtain ⟨W, hW⟩ := X.F.uAt_split k q hz τ
    obtain ⟨cv, rfl⟩ := (vec (X.F.M k).toMChart (q ≫ X.π) hx).surjective w
    rw [X.F.sum_vecAt, tanPull_vec (X.F.M k).toMChart ρ e hx hx'] at ha
    have hc := (vec (X.F.M k).toMChart _ hx').injective ha
    rw [X.F.uAt_spMap k ρ q hz hz'] at hc
    have hWρ : W.map ρ * (X.F.uAt k q hz τ).map ρ = 1 := by
      rw [← Matrix.map_mul, hW, Matrix.map_one _ (map_zero _) (map_one _)]
    have ha2 : (W.map ρ).mulVec (fun j => ρ (cv j)) = a := by
      rw [← hc, Matrix.mulVec_mulVec, hWρ, Matrix.one_mulVec]
    refine ⟨W.mulVec cv, ?_, fun b hb => ?_⟩
    · show _ = ∑ i, _ • X.F.vecAt k q hz rfl τ i
      rw [X.F.sum_vecAt]
      congr 1
      funext j
      apply hρ
      rw [RingHom.map_mulVec]
      have : (ρ ∘ W.mulVec cv) = a := by
        rw [← ha2]
        funext i
        exact RingHom.map_mulVec ρ W cv i
      rw [this, hc]
    · have hb' : vec (X.F.M k).toMChart (q ≫ X.π) hx cv =
          vec (X.F.M k).toMChart (q ≫ X.π) hx ((X.F.uAt k q hz τ).mulVec b) := by
        rw [← X.F.sum_vecAt]
        exact hb
      have := (vec (X.F.M k).toMChart _ hx).injective hb'
      rw [this, Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]

theorem exists_eigFrame_vecAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : FlagCover Y) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V), (algebraMap V K).comp φ = algebraMap c.F K → ∀ (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (yF : Sp K ⟶ Xo.XF c), yF ≫ pullback.snd _ _ = spMap (algebraMap c.F K) → (spMap (algebraMap V K) ≫ q) ≫ X.π = yF ≫ Y.j → ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (X.F.vecAt k q hz rfl τ i)).left := by
  intro E _ _ _ H Dw l Xo c O _ β Y X V K _ _ _ _ _ _ φ hφ q k hz yF hyF hpt
  have hz' : ⊤ ≤ (spMap (algebraMap V K) ≫ q) ⁻¹ᵁ X.F.U k := le_preimage_comp _ hz
  have key : ∀ (x'' : Sp K ⟶ Y.X) (hx : (spMap (algebraMap V K) ≫ q) ≫ X.π = x''),
      (∀ σ, initSpan K (X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap (algebraMap V K) ≫ q) ≫ X.π) σ := by
    rintro x'' rfl h
    exact h
  exact exists_eigFrame_of_top (algebraMap V K) (IsFractionRing.injective V K) φ hφ q k hz hz'
    (key _ hpt fun σ => X.top K yF hyF _ hpt k hz' σ)

end GlobalTheory.ChartEigFrame
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdealPull

theorem germ_appLE {X Y : Scheme.{0}} (t : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (hV : V ≤ t ⁻¹ᵁ U)
    (y : Y) (hy : y ∈ V) (a : Γ(X, U)) :
    (Y.presheaf.germ V y hy).hom ((t.appLE U V hV).hom a) =
      (t.stalkMap y).hom ((X.presheaf.germ U (t y) (show t y ∈ U from hV hy)).hom a) := by
  show (Y.presheaf.germ V y hy).hom (resG Y hV ((t.app U).hom a)) = _
  rw [germ_resG]
  exact (Scheme.Hom.germ_stalkMap_apply t U y _ a).symm

theorem regAt_and_unitAt_div_gen : ∀ (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData) (y : Y₁) (U : Y₀.Opens) (hx : t y ∈ U) (n : ℕ) (b : Fin n → Γ(Y₀, U)), (∀ (k : Fin n) (W : Y₀.affineOpens) (h : W.1 ≤ U), resG Y₀ h (b k) ∈ I.ideal W) → (∀ (W : Y₀.affineOpens) (hxW : t y ∈ W.1) (a : Γ(Y₀, W.1)), a ∈ I.ideal W → Y₀.presheaf.germ W.1 (t y) hxW a ∈ Ideal.span (Set.range fun k => Y₀.presheaf.germ U (t y) hx (b k))) → ∀ (U' : Y₁.affineOpens) (f : Γ(Y₁, U'.1)) (hyU' : y ∈ U'.1), fnOf U'.1 (gen_mem hyU') f ≠ 0 → (I.comap t).ideal U' = Ideal.span {f} → ∀ (V : Y₁.Opens) (hV : V ≤ t ⁻¹ᵁ U) (hyV : y ∈ V), (∀ k, RegAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f)) ∧ ∃ k, UnitAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f) := by
  intro Y₀ Y₁ _ t I y U hx n b hb hgerm U' f hyU' hf0 hU' V hV hyV
  obtain ⟨_, ⟨W, hWa, rfl⟩, hxW, hWU⟩ := Y₀.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hWU' : W ≤ U := hWU
  obtain ⟨_, ⟨V₀, hV₀a, rfl⟩, hyV₀, hV₀le⟩ := Y₁.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ U'.1 ⊓ t ⁻¹ᵁ W from ⟨hyU', hxW⟩) (U'.1 ⊓ t ⁻¹ᵁ W).isOpen
  have hV₀U' : V₀ ≤ U'.1 := fun z hz => (hV₀le hz).1
  have hV₀W : V₀ ≤ t ⁻¹ᵁ W := fun z hz => (hV₀le hz).2
  let R := Y₁.presheaf.stalk y
  let g : R := (Y₁.presheaf.germ U'.1 y hyU').hom f
  let β : Fin n → R := fun k => (t.stalkMap y).hom ((Y₀.presheaf.germ U (t y) hx).hom (b k))
  have hI1 : (I.comap t).ideal ⟨V₀, hV₀a⟩ = Ideal.span {resG Y₁ hV₀U' f} := by
    rw [← (I.comap t).map_ideal (U := ⟨V₀, hV₀a⟩) (V := U') hV₀U', hU', Ideal.map_span,
      Set.image_singleton]
    rfl
  have hI2 := GlobalTheory.Principalise.comapIdealAffine I t ⟨W, hWa⟩ ⟨V₀, hV₀a⟩ hV₀W
  have hgf : (Y₁.presheaf.germ V₀ y hyV₀).hom (resG Y₁ hV₀U' f) = g := germ_resG _ _ _ _
  have hc : ∀ k, ∃ c : R, β k = c * g := by
    intro k
    have hmem : (t.appLE W V₀ hV₀W).hom (resG Y₀ hWU' (b k)) ∈ (I.comap t).ideal ⟨V₀, hV₀a⟩ := by
      rw [hI2]; exact Ideal.mem_map_of_mem _ (hb k ⟨W, hWa⟩ hWU')
    rw [hI1, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨(Y₁.presheaf.germ V₀ y hyV₀).hom c, ?_⟩
    have := congrArg (Y₁.presheaf.germ V₀ y hyV₀).hom hc
    rw [map_mul, hgf, germ_appLE, germ_resG] at this
    exact this.symm
  choose c hcβ using hc
  have hgmem : g ∈ Ideal.span (Set.range β) := by
    have hmem : resG Y₁ hV₀U' f ∈ (I.comap t).ideal ⟨V₀, hV₀a⟩ := by
      rw [hI1]; exact Ideal.mem_span_singleton_self _
    rw [hI2] at hmem
    have h2 := Ideal.mem_map_of_mem (Y₁.presheaf.germ V₀ y hyV₀).hom hmem
    rw [hgf, Ideal.map_map] at h2
    refine (Ideal.map_le_iff_le_comap.2 ?_) h2
    intro a ha
    rw [Ideal.mem_comap, RingHom.comp_apply, germ_appLE]
    have h3 := Ideal.mem_map_of_mem (t.stalkMap y).hom (hgerm ⟨W, hWa⟩ hxW a ha)
    rw [Ideal.map_span, ← Set.range_comp] at h3
    exact h3
  have hfK : algebraMap R Y₁.functionField g = fnOf U'.1 (gen_mem hyU') f := algebraMap_germ hyU' f
  have hg0 : g ≠ 0 := fun h => hf0 (by rw [← hfK, h, map_zero])
  have hFk : ∀ k, fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f =
      algebraMap R Y₁.functionField (c k) := by
    intro k
    rw [← algebraMap_germ hyV, ← hfK, germ_appLE]
    change algebraMap R _ (β k) / _ = _
    rw [hcβ k, map_mul, mul_div_assoc, div_self (hfK ▸ hf0), mul_one]
  refine ⟨fun k => hFk k ▸ ⟨c k, rfl⟩, ?_⟩
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hgmem
  have hsum : ∑ k, e k * c k = 1 := by
    have : (∑ k, e k * c k) * g = 1 * g := by
      rw [one_mul, Finset.sum_mul]
      conv_rhs => rw [← he]
      exact Finset.sum_congr rfl fun k _ => by rw [hcβ k, smul_eq_mul, mul_assoc]
    exact mul_right_cancel₀ hg0 this
  obtain ⟨k, hk⟩ : ∃ k, IsUnit (c k) := by
    by_contra hcon
    push_neg at hcon
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R := hsum ▸ Ideal.sum_mem _ fun k _ =>
      Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hcon k))
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top this
  exact ⟨k, c k, hk, (hFk k).symm⟩

end GlobalTheory.IdealPull
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

namespace GlobalTheory.CompHS.ChartBd

theorem mem_iff_not_mem_basicOpen {X : Scheme.{0}} (C : Closeds X) (U : X.affineOpens) (g : Γ(X, U.1))
    (hD : (Scheme.IdealSheafData.vanishingIdeal C).ideal U = Ideal.span {g}) (x : X) (hx : x ∈ U.1) :
    x ∈ C ↔ x ∉ X.basicOpen g := by
  obtain ⟨s, rfl⟩ : x ∈ Set.range U.2.fromSpec := by rw [U.2.range_fromSpec]; exact hx
  have hcl : IsClosed (U.2.fromSpec ⁻¹' (C : Set X)) := C.isClosed.preimage U.2.fromSpec.continuous
  have hz : PrimeSpectrum.zeroLocus ((Scheme.IdealSheafData.vanishingIdeal C).ideal U : Set Γ(X, U.1)) =
      U.2.fromSpec ⁻¹' (C : Set X) := by
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hcl.closure_eq
  have h1 : U.2.fromSpec s ∈ X.basicOpen g ↔ s ∈ PrimeSpectrum.basicOpen g := by
    rw [← U.2.fromSpec_preimage_basicOpen]; rfl
  have h2 : U.2.fromSpec s ∈ C ↔ s ∈ U.2.fromSpec ⁻¹' (C : Set X) := Iff.rfl
  have h3 : s ∈ PrimeSpectrum.basicOpen g ↔ g ∉ (s : PrimeSpectrum Γ(X, U.1)).asIdeal :=
    PrimeSpectrum.mem_basicOpen g s
  have h4 : s ∈ U.2.fromSpec ⁻¹' (C : Set X) ↔ g ∈ (s : PrimeSpectrum Γ(X, U.1)).asIdeal := by
    rw [← hz, hD, PrimeSpectrum.zeroLocus_span]
    exact (PrimeSpectrum.mem_zeroLocus (s : PrimeSpectrum Γ(X, U.1)) {g}).trans Set.singleton_subset_iff
  exact h2.trans (h4.trans (not_not.symm.trans (h1.trans h3).not.symm))

end GlobalTheory.CompHS.ChartBd

namespace GlobalTheory.CompHS.ChartBd

theorem exists_chart_bd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw), IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, ∃ (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (p : Γ(Y₀ TF.X Z, W)), y ∈ W ∧ W ≤ (L₀ TF.X Z la).U i ∧ IsDomain Γ(Y₀ TF.X Z, W) ∧ RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)).hom ∧ p ≠ 0 ∧ ∀ y' ∈ W, (y' ∈ bd₀ TF.X Z ↔ y' ∉ (Y₀ TF.X Z).basicOpen p) := by
  intro E _ _ _ H Dw l Xo c TF Z la hV y

  let q : Y₀ TF.X Z ⟶ TF.Y.X := inc₀ TF.X Z ≫ TF.X.π
  obtain ⟨-, U', hxU', n, f, J, -, hD⟩ := TF.snc (q y)
  let g : Γ(TF.Y.X, U'.1) := ∏ i ∈ J, f i
  have hZ : ∀ x ∈ U'.1, x ∈ (LogKS.interior TF.Y).compl ↔ x ∉ TF.Y.X.basicOpen g :=
    mem_iff_not_mem_basicOpen _ U' g hD

  have hs : Smooth (str₀ TF.X Z) := by
    haveI := hV.1
    exact SmoothOfRelativeDimension.smooth (GlobalTheory.FlagTan.dimFlag Dw) (str₀ TF.X Z)
  obtain ⟨-, hn, hl⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ _ hs
  have := GlobalTheory.IsNormalScheme.of_pred hn
  obtain ⟨W₁, hyW₁, hW₁⟩ := GlobalTheory.ModelChart.exists_open_isDomain (Y₀ TF.X Z) y
  obtain ⟨i, hi⟩ := exists_chart (isLB_L₀ TF.X Z la) y
  let O : (Y₀ TF.X Z).Opens := W₁ ⊓ (L₀ TF.X Z la).U i ⊓ q ⁻¹ᵁ U'.1
  have hyO : y ∈ O := ⟨⟨hyW₁, hi⟩, hxU'⟩
  obtain ⟨W, hW, hyW, hWO⟩ := exists_isAffineOpen_mem_and_subset (U := O) (x := y) hyO
  have hWO' : W ≤ O := hWO
  have hWq : W ≤ q ⁻¹ᵁ U'.1 := hWO'.trans inf_le_right
  let p : Γ(Y₀ TF.X Z, W) := (Y₀ TF.X Z).presheaf.map (homOfLE hWq).op (q.app U'.1 g)
  have hbo : (Y₀ TF.X Z).basicOpen p = W ⊓ q ⁻¹ᵁ TF.Y.X.basicOpen g := by
    rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
  have key : ∀ y' ∈ W, (y' ∈ bd₀ TF.X Z ↔ y' ∉ (Y₀ TF.X Z).basicOpen p) := by
    intro y' hy'
    have e1 : y' ∈ bd₀ TF.X Z ↔ q y' ∈ (LogKS.interior TF.Y).compl := Iff.rfl
    have e2 : y' ∈ (Y₀ TF.X Z).basicOpen p ↔ q y' ∈ TF.Y.X.basicOpen g := by
      rw [hbo]; exact ⟨fun h => h.2, fun h => ⟨hy', h⟩⟩
    rw [e1, e2]
    exact hZ _ (hWq hy')
  refine ⟨W, hW, i, p, hyW, hWO'.trans (inf_le_left.trans inf_le_right), hW₁ W hyW (hWO'.trans (inf_le_left.trans inf_le_left)), ?_, ?_, key⟩
  · have hφ : Spec.map (Spec.preimage ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)) =
        (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z := Spec.map_preimage _
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp (by rw [hφ]; infer_instance)
  · intro hp0
    obtain ⟨y', hy'W, hy'U⟩ := (dense_U₀ TF.X Z).inter_open_nonempty W W.isOpen ⟨y, hyW⟩
    have h := (key y' hy'W).not.mp (not_not.mpr hy'U)
    rw [hp0, Scheme.basicOpen_zero] at h
    exact h (by simp)

end GlobalTheory.CompHS.ChartBd
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

theorem baseIdeal_sup {R : Type} [CommRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (a b : Ideal R) : baseIdeal f (a ⊔ b) = baseIdeal f a ⊔ baseIdeal f b := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, baseIdeal_ideal, baseIdeal_ideal, baseIdeal_ideal,
    Ideal.map_sup]

theorem idealSheaf_ext_top {X : Scheme.{0}} [IsAffine X] {I J : X.IdealSheafData}
    (h : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J.ideal ⟨⊤, isAffineOpen_top X⟩) : I = J :=
  Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := Unit) (fun _ => ⟨⊤, isAffineOpen_top X⟩) iSup_const fun _ => h

theorem appLE_specMap_fromSpec {W : Scheme.{0}} (U : W.Opens) (hU : IsAffineOpen U) (C : Type) [CommRing C]
    (φ : Γ(W, U) →+* C) (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤
      (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U) :
    ((Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h).hom =
      (cst (𝟙 (Spec (CommRingCat.of C))) ⊤).comp φ := by
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have m1 : (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h =
      hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(W, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(W, U)).presheaf.map_id _
  have m3 : (Scheme.ΓSpecIso Γ(W, U)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  rw [m1, m2, m3]
  ext x
  simp only [cst, RingHom.comp_apply, rs_self]
  rfl

theorem specIdeal :
    (∀ (C : Type) [CommRing C], Function.Bijective (fun a : Ideal C => baseIdeal (𝟙 (Spec (CommRingCat.of C))) a) ∧ (∀ a b : Ideal C, baseIdeal (𝟙 (Spec (CommRingCat.of C))) (a ⊔ b) = baseIdeal (𝟙 _) a ⊔ baseIdeal (𝟙 _) b)) ∧ (∀ (W : Scheme.{0}) (V : W.affineOpens) (C : Type) [CommRing C] (φ : Γ(W, V.1) →+* C) (J : W.IdealSheafData), J.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) = baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((J.ideal V).map φ)) := by
  refine ⟨fun C _ => ⟨⟨fun a b hab => ?_, fun J => ?_⟩, fun a b => baseIdeal_sup _ a b⟩, fun W V C _ φ J => ?_⟩
  · have hb := cst_bijective (𝟙 (Spec (CommRingCat.of C))) (W := ⊤) rfl
    have e := congrArg (fun I : (Spec (CommRingCat.of C)).IdealSheafData => I.ideal ⟨⊤, isAffineOpen_top _⟩) hab
    simp only [baseIdeal_ideal] at e
    rw [← Ideal.comap_map_of_bijective _ hb (I := a), e, Ideal.comap_map_of_bijective _ hb]
  · have hb := cst_bijective (𝟙 (Spec (CommRingCat.of C))) (W := ⊤) rfl
    refine ⟨(J.ideal ⟨⊤, isAffineOpen_top _⟩).comap (cst (𝟙 (Spec (CommRingCat.of C))) ⊤), idealSheaf_ext_top ?_⟩
    simp only [baseIdeal_ideal]
    exact Ideal.map_comap_of_surjective _ hb.2 _
  · have h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ V.1 :=
      fun x _ => V.2.range_fromSpec.subset ⟨_, rfl⟩
    refine idealSheaf_ext_top ?_
    rw [GlobalTheory.Principalise.comapIdealAffine J _ V ⟨⊤, isAffineOpen_top _⟩ h, baseIdeal_ideal, Ideal.map_map,
      appLE_specMap_fromSpec V.1 V.2 C φ h]

end GlobalTheory.FormalAlg
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem surj_mod_baseIdeal_of_isClosedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → ∀ (V : Z.Opens) (hV : IsAffineOpen V), IsAffineOpen (φ ⁻¹ᵁ V) → Function.Surjective ((Ideal.Quotient.mk (((baseIdeal p I).ideal ⟨V, hV⟩).map (φ.app V).hom)).comp (φ.app V).hom) := by
  intro R _ I X Z φ p hg V hV hW
  set K := (baseIdeal p I).comap φ with hK
  have hKid : K.ideal ⟨φ ⁻¹ᵁ V, hW⟩ = ((baseIdeal p I).ideal ⟨V, hV⟩).map (φ.app V).hom := by
    rw [hK, GlobalTheory.Principalise.comapIdealAffine (baseIdeal p I) φ ⟨V, hV⟩ ⟨φ ⁻¹ᵁ V, hW⟩ le_rfl,
      Scheme.Hom.app_eq_appLE]
  intro q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨b, hb⟩ := Scheme.Hom.app_surjective (K.subschemeι ≫ φ) V hV
    ((K.subschemeι.app (φ ⁻¹ᵁ V)).hom c)
  refine ⟨b, ?_⟩
  simp only [RingHom.comp_apply]
  rw [Ideal.Quotient.eq, ← hKid, ← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker, map_sub]
  rw [Scheme.Hom.comp_app] at hb
  rw [sub_eq_zero]
  exact hb

end GlobalTheory.FormalAlg
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_of_sqZero : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ J : Ideal R, J ^ 2 = ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J))) → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.LBLift.hasRep_of_sqZero | exact GlobalTheory.LBLift.hasRep_of_sqZero | (intros; apply GlobalTheory.LBLift.hasRep_of_sqZero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasRepresentingScheme_pinchedBase : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → HasRepAF A g (Over.mk (spMap (algebraMap R R'))) → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk c))) → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.Pinch.hasRep_pinched | exact GlobalTheory.Pinch.hasRep_pinched | (intros; apply GlobalTheory.Pinch.hasRep_pinched <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

theorem _root_.GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    (∀ α : A.Fld, A.IsForm α → ∀ ε : ℤˣ, IsFiniteMeasure (A.part α ε)) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), A.IsForm α → A.IsForm β → (∀ ε : ℤˣ, Integrable g (A.part α ε)) → (∀ ε : ℤˣ, Integrable g (A.part β ε)) →
      (∀ ε : ℤˣ, Integrable g (A.part (α + β) ε)) ∧ wInt A g (α + β) = wInt A g α + wInt A g β) ∧
    (∀ (g : M → ℝ) (t : ℝ) (α : A.Fld), A.IsForm α → wInt A g ((t : ℂ) • α) = t * wInt A g α) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), (∀ x, dens (α x) = dens (β x)) → wInt A g α = wInt A g β) := by
  exact @GlobalTheory.LineForm.wInt_props
end
