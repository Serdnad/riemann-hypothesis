module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.LocalToGlobal.LocalInduction.BridgeInd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle006
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle003
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle005
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.WittCoreInclusionMulVecMemLatticeCompletionAtPla
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle400
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle743
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle785
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle383
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle223

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.ChiExtend
end GlobalTheory.ChiExtend
namespace GlobalTheory.ChiExtend
end GlobalTheory.ChiExtend
open GlobalTheory.ChiExtend in
theorem GlobalTheory.ChiExtend.chi_eq_of_ext_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ → ∀ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) → (∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z') → ∀ c, 1 ≤ c → c ≤ D.R.t → ∀ σ : GE L₁.lay.fixZ.nd, ((L₁.lay.fixZ.nd.chi i₁ c σ : (L₁.lay.fixZ.nd.O i₁)ˣ) : L₁.lay.fixZ.nd.O i₁) = φ ((L₀.lay.fixZ.nd.chi i₀ c σ : (L₀.lay.fixZ.nd.O i₀)ˣ) : L₀.lay.fixZ.nd.O i₀) := by
  intro _ D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ hCheb big₀ big₁ L₀ L₁ hB₀ hB₁ i₀ i₁ hw hj φ hφ hφalg c hc1 hct σ
  obtain ⟨Sp₀, ⟨AS₀⟩, -⟩ := hB₀
  obtain ⟨Sp₁, ⟨AS₁⟩, -⟩ := hB₁
  have hw' : L₀.X.nd.w i₀ = L₁.X.nd.w i₁ := hw
  have hj' : L₀.X.nd.j i₀ = L₁.X.nd.j i₁ := hj
  have hl : L₀.lay.fixZ.nd.l i₀ = L₁.lay.fixZ.nd.l i₁ := by
    rw [← L₀.lay.fixZ.nd.w_l i₀, ← L₁.lay.fixZ.nd.w_l i₁, hw]
  have hmu : L₀.Y.muC i₀ = L₁.Y.muC i₁ := by
    have hr := L₀.X.nd.j_range i₀
    let jj : Fin D.R.m := ⟨L₀.X.nd.j i₀ - 1, by omega⟩
    have e₀ := AS₀.muC i₀ jj (by show L₀.X.nd.j i₀ - 1 + 1 = L₀.X.nd.j i₀; omega)
    have e₁ := AS₁.muC i₁ jj (by show L₀.X.nd.j i₀ - 1 + 1 = L₁.X.nd.j i₁; omega)
    apply A.chr.e1.injective
    apply Subtype.ext
    have hm : L₀.X.nd.mu i₀ = L₁.X.nd.mu i₁ := by
      exact (L₀.X.mu_w i₀).trans ((congrArg D.what₂.muTw hw').trans (L₁.X.mu_w i₁).symm)
    exact e₀.trans ((congrArg (fun m => tp.tup m jj) hm).trans e₁.symm)
  have hl₀ := (L₀.lay.fixZ.nd.lPrime i₀).out.ne_zero
  have hfin : (placesOver D.host.E (L₀.lay.fixZ.nd.l i₀) ∪ ((L₀.lay.fixZ.nd.S i₀ : Set (PlE D.host)) ∪
      (L₀.lay.fixZ.nd.Q i₀ : Set (PlE D.host))) ∪ ((L₁.lay.fixZ.nd.S i₁ : Set (PlE D.host)) ∪
      (L₁.lay.fixZ.nd.Q i₁ : Set (PlE D.host)))).Finite :=
    ((placesOver_finite' _ _ hl₀).union ((Finset.finite_toSet _).union (Finset.finite_toSet _))).union
      ((Finset.finite_toSet _).union (Finset.finite_toSet _))
  have hout : ∀ w ∉ hfin.toFinset, IsSplitPl D.host w →
      SplitOut L₀.lay.fixZ.nd i₀ w ∧ SplitOut L₁.lay.fixZ.nd i₁ w := by
    intro w hwF hsp
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Finset.mem_coe, not_or] at hwF
    obtain ⟨⟨hpl, hS₀, hQ₀⟩, hS₁, hQ₁⟩ := hwF
    exact ⟨⟨hsp, hpl, hS₀, hQ₀⟩, ⟨hsp, hl ▸ hpl, hS₁, hQ₁⟩⟩
  have hone : (fun σ : GE L₁.lay.fixZ.nd => ((L₁.lay.fixZ.nd.chi i₁ 1 σ : (L₁.lay.fixZ.nd.O i₁)ˣ) :
      L₁.lay.fixZ.nd.O i₁)) = fun σ => φ ((L₀.lay.fixZ.nd.chi i₀ 1 σ : (L₀.lay.fixZ.nd.O i₀)ˣ) :
      L₀.lay.fixZ.nd.O i₀) := by
    haveI := L₁.lay.fixZ.nd.O_complete i₁
    refine eq_of_dense (L₁.lay.fixZ.nd.O_adic i₁) inferInstance (L₁.lay.fixZ.nd.chi_cont i₁ 1)
      ((continuous_of_le_comap (L₀.lay.fixZ.nd.O_adic i₀) (L₁.lay.fixZ.nd.O_adic i₁) φ
        (maximalIdeal_le_comap hl φ hφalg)).comp (L₀.lay.fixZ.nd.chi_cont i₀ 1)) (hCheb hfin.toFinset) ?_
    rintro σ ⟨w, hwF, hsp, B, hB, hσ⟩
    obtain ⟨ho₀, ho₁⟩ := hout w hwF hsp
    have e₀ := (L₀.lay.fixZ.naut.chi_mu i₀ w ho₀).2 B σ hB hσ
    have e₁ := (L₁.lay.fixZ.naut.chi_mu i₁ w ho₁).2 B σ hB hσ
    have em := congrArg (fun m => D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw m D.naut.etaTinv) w)
      (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2))) hmu
    have e := Multiset.singleton_inj.1 (e₀.symm.trans (em.trans e₁))
    apply iotaO_injective L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁
    rw [hφ]
    exact e.symm
  have hu1 : L₁.lay.fixZ.nd.chi i₁ 1 σ = Units.map (φ : L₀.lay.fixZ.nd.O i₀ →* L₁.lay.fixZ.nd.O i₁)
      (L₀.lay.fixZ.nd.chi i₀ 1 σ) := Units.ext (congrFun hone σ)
  have key : L₁.lay.fixZ.nd.chi i₁ c σ = Units.map (φ : L₀.lay.fixZ.nd.O i₀ →* L₁.lay.fixZ.nd.O i₁)
      (L₀.lay.fixZ.nd.chi i₀ c σ) := by
    rw [L₁.lay.fixZ.nd.chi_def i₁ c hc1 hct, L₀.lay.fixZ.nd.chi_def i₀ c hc1 hct]
    simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, map_mul, map_zpow]
    erw [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, map_mul, map_zpow]
    rw [hu1]
    refine congrArg _ (congrArg (· ^ _) ?_)
    apply Units.ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    exact (hφalg _ _ (cyc_heq _ _ hl σ)).symm
  exact congrArg Units.val key
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.CoefDuty.ExtRing
end GlobalTheory.CoefDuty.ExtRing
end
open GlobalTheory.CoefDuty.ExtRing in

theorem GlobalTheory.CoefDuty.ExtRing.ext_ring_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ) (L₀ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → ∃ big₁ : D.what₂.places.Pl → Finset ℂ, ∀ L₁ : LocAll (lay0 D), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → ∃ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) ∧ ∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z' := by
  classical
  intro _ D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big₀ L₀ hB₀
  obtain ⟨Sp₀, ⟨Au₀⟩, -⟩ := hB₀
  have hg := fun i => exists_gens (Sp₀.iq i) (Sp₀.iq_alg i)
  let gens : ∀ i : L₀.X.nd.Loc, Finset (Qbar (L₀.X.nd.l i)) := fun i => Classical.choose (hg i)
  have hgens : ∀ i x, Sp₀.iq i x ∈ Submodule.span ℚ_[L₀.X.nd.l i] (gens i : Set (Qbar (L₀.X.nd.l i))) :=
    fun i => Classical.choose_spec (hg i)
  let big₁ : D.what₂.places.Pl → Finset ℂ := fun w => (Finset.Icc 1 D.R.m).biUnion fun j =>
    (L₀.X.nd.locs j w).biUnion fun i => (gens i).image fun y => qCast (L₀.X.nd.w_l i) (A.pl.ι (L₀.X.nd.w i)) y
  have hbig : ∀ i y, y ∈ gens i → qCast (L₀.X.nd.w_l i) (A.pl.ι (L₀.X.nd.w i)) y ∈ big₁ (L₀.X.nd.w i) := by
    intro i y hy
    refine Finset.mem_biUnion.2 ⟨L₀.X.nd.j i, Finset.mem_Icc.2 (L₀.X.nd.j_range i), ?_⟩
    exact Finset.mem_biUnion.2 ⟨i, (L₀.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩, Finset.mem_image_of_mem _ hy⟩
  refine ⟨big₁, fun L₁ hB₁ i₀ i₁ hw => ?_⟩
  obtain ⟨Sp₁, ⟨Au₁⟩, -⟩ := hB₁
  change L₀.X.nd.w i₀ = L₁.X.nd.w i₁ at hw
  have hl : L₀.X.nd.l i₀ = L₁.X.nd.l i₁ := by
    exact (L₀.X.nd.w_l i₀).symm.trans ((congrArg _ hw).trans (L₁.X.nd.w_l i₁))
  haveI := L₀.X.nd.lPrime i₀
  haveI := L₁.X.nd.lPrime i₁
  have key : ∀ w (_ : L₀.X.nd.w i₀ = w) (h₁ : D.what₂.places.resChar w = L₁.X.nd.l i₁),
      qCast h₁ (A.pl.ι w) = qCast hl (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) := by
    intro w hw' h₁
    subst hw'
    exact qCast_trans _ _ _ _
  obtain ⟨φ, h1, h2⟩ := exists_ringHom (O₀ := L₀.X.nd.O i₀) (O₁ := L₁.X.nd.O i₁)
    (cr₀ := L₀.X.nd.instO i₀) (dm₀ := L₀.X.nd.domO i₀) (dv₀ := L₀.X.nd.dvrO i₀) (al₀ := L₀.X.nd.algO i₀) (fi₀ := L₀.X.nd.finO i₀)
    (cr₁ := L₁.X.nd.instO i₁) (dm₁ := L₁.X.nd.domO i₁) (dv₁ := L₁.X.nd.dvrO i₁) (al₁ := L₁.X.nd.algO i₁) (fi₁ := L₁.X.nd.finO i₁) hl (Sp₀.iq i₀) (Sp₀.iq_alg i₀) (Sp₁.iq i₁) (Sp₁.iq_alg i₁)
    (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) (qCast (L₁.X.nd.w_l i₁) (A.pl.ι (L₁.X.nd.w i₁)))
    (key _ hw _) _ (hgens i₀) (fun y hy => Sp₁.iq_big i₁ _ (hw ▸ hbig i₀ y hy))
  refine ⟨φ, fun z => ?_, h2⟩
  have e₀ := fun x => (congrArg (fun g : Qbar (L₀.X.nd.l i₀) ≃+* ℂ => g (L₀.Y.naut.iotaQ i₀ x)) (Au₀.iotaQC i₀)).trans
    (congrArg (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) (DFunLike.congr_fun (Au₀.iotaQ i₀) x))
  have e₁ := fun x => (congrArg (fun g : Qbar (L₁.X.nd.l i₁) ≃+* ℂ => g (L₁.Y.naut.iotaQ i₁ x)) (Au₁.iotaQC i₁)).trans
    (congrArg (qCast (L₁.X.nd.w_l i₁) (A.pl.ι (L₁.X.nd.w i₁))) (DFunLike.congr_fun (Au₁.iotaQ i₁) x))
  exact (e₁ _).trans ((h1 z).trans (e₀ _).symm)
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.ExtTheta
variable {D : D7}
theorem transport_alt (U : _root_.GlobalTheory.HeightCounting.AUSideAlt D) (M : MtFam D) {μ₀ μ₁ : D.what₂.Tup} {j₀ j₁ : ℕ} (hμ : μ₀ = μ₁) (hj : j₀ = j₁)
    (a₀ : 1 ≤ j₀) (b₀ : j₀ ≤ D.R.m) (a₁ : 1 ≤ j₁) (b₁ : j₁ ≤ D.R.m) {ι : Type}
    (S₀ : ι → Submodule ℂ (GAf D.host.E D.R.nV → (M μ₀ j₀ a₀ b₀).wt.W))
    (irr₀ : ∀ P, NG.IsIrrRep (M μ₀ j₀ a₀ b₀).wt.ρ (S₀ P))
    (surj : ∀ S', NG.IsIrrRep (M μ₀ j₀ a₀ b₀).wt.ρ S' →
      (NG.isoTyp (M μ₀ j₀ a₀ b₀).wt.ρ S').comap (M μ₀ j₀ a₀ b₀).real ≠ ⊥ → ∃ P, NG.IsoRep (S₀ P) S')
    (S₁ : Submodule ℂ (GAf D.host.E D.R.nV → (M μ₁ j₁ a₁ b₁).wt.W))
    (irr₁ : NG.IsIrrRep (M μ₁ j₁ a₁ b₁).wt.ρ S₁)
    (ne : (NG.isoTyp (M μ₁ j₁ a₁ b₁).wt.ρ S₁).comap (M μ₁ j₁ a₁ b₁).real ≠ ⊥) :
    ∃ P, (∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ) (c : ℂ),
      (∀ y ∈ (NG.isoTyp (M μ₁ j₁ a₁ b₁).wt.ρ S₁).comap (M μ₁ j₁ a₁ b₁).real,
        NG.tN (M μ₁ j₁ a₁ b₁).J s ϖ k ((M μ₁ j₁ a₁ b₁).real y) = c • (M μ₁ j₁ a₁ b₁).real y) →
      ∀ y ∈ (NG.isoTyp (M μ₀ j₀ a₀ b₀).wt.ρ (S₀ P)).comap (M μ₀ j₀ a₀ b₀).real,
        NG.tN (M μ₀ j₀ a₀ b₀).J s ϖ k ((M μ₀ j₀ a₀ b₀).real y) = c • (M μ₀ j₀ a₀ b₀).real y) ∧
      (∀ w, D.nbc.locAU j₀ (U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₀ P, irrS := irr₀ P }) w =
        D.nbc.locAU j₁ (U.cls j₁ a₁ b₁ { (M μ₁ j₁ a₁ b₁).wt with S := S₁, irrS := irr₁ }) w) ∧
      (∀ w, D.nbc.satAU j₀ (U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₀ P, irrS := irr₀ P }) w =
        D.nbc.satAU j₁ (U.cls j₁ a₁ b₁ { (M μ₁ j₁ a₁ b₁).wt with S := S₁, irrS := irr₁ }) w) ∧
      D.nbc.infW j₀ (D.nbc.wtAU j₀ (U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₀ P, irrS := irr₀ P })) =
        D.nbc.infW j₁ (D.nbc.wtAU j₁ (U.cls j₁ a₁ b₁ { (M μ₁ j₁ a₁ b₁).wt with S := S₁, irrS := irr₁ })) := by
  subst hμ; subst hj
  obtain ⟨P, hP⟩ := surj S₁ irr₁ ne
  have e := isoTyp_congr (M μ₀ j₀ a₀ b₀).wt.ρ (irr₀ P).1.stable hP
  have hc : U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₀ P, irrS := irr₀ P } =
      U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₁, irrS := irr₁ } :=
    (U.iso j₀ a₀ b₀ _ _).2 ⟨NG.AlgWt.Iso.refl _, hP⟩
  refine ⟨P, fun s ϖ k c h => ?_, fun w => ?_, fun w => ?_, ?_⟩
  · rw [e]; exact h
  · rw [hc]
  · rw [hc]
  · rw [hc]
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}
theorem split_out_of_w_eq {big₀ big₁ : D.what₂.places.Pl → Finset ℂ} {X₀ X₁ : LocNd (lay0 D)} {T₀ : LocTw X₀} {T₁ : LocTw X₁}
    (Sp₀ : NdSpec A.pl M C big₀ X₀ T₀) (Sp₁ : NdSpec A.pl M C big₁ X₁ T₁) (i₀ : X₀.nd.Loc) (i₁ : X₁.nd.Loc)
    (hw : X₀.nd.w i₀ = X₁.nd.w i₁) (v : PlE D.host) (h : SplitOut X₀.nd i₀ v) : SplitOut X₁.nd i₁ v := by
  have hl : X₀.nd.l i₀ = X₁.nd.l i₁ := by rw [← X₀.nd.w_l, ← X₁.nd.w_l, hw]
  have q₀ : X₀.nd.Q i₀ = C.Q (X₀.nd.w i₀) :=
    (Sp₀.Q_eq _ _ i₀ ((X₀.nd.locs_mem _ _ _).2 ⟨rfl, rfl⟩)).trans (Sp₀.Qc_eq _ _)
  have q₁ : X₁.nd.Q i₁ = C.Q (X₁.nd.w i₁) :=
    (Sp₁.Q_eq _ _ i₁ ((X₁.nd.locs_mem _ _ _).2 ⟨rfl, rfl⟩)).trans (Sp₁.Qc_eq _ _)
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, hl ▸ h2, fun hs => h3 ?_, ?_⟩
  · have := (X₁.S_def i₁ v).1 hs
    refine (X₀.S_def i₀ v).2 ?_
    have hl' : X₀.l i₀ = X₁.l i₁ := hl
    rw [hl']; exact this
  · rw [q₁, ← hw, ← q₀]; exact h4
theorem mu_c_eq_of_mu_eq_of_j_eq {X₀ X₁ : LocNd (lay0 D)} {iq₀ : ∀ i : X₀.nd.Loc, FractionRing (X₀.nd.O i) →+* Qbar (X₀.nd.l i)}
    {iq₁ : ∀ i : X₁.nd.Loc, FractionRing (X₁.nd.O i) →+* Qbar (X₁.nd.l i)} {Y₀ : LocAut X₀} {Y₁ : LocAut X₁}
    {C₀ : LocBC Y₀} {C₁ : LocBC Y₁} (U₀ : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq₀ Y₀ C₀) (U₁ : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq₁ Y₁ C₁)
    (i₀ : X₀.nd.Loc) (i₁ : X₁.nd.Loc) (hμ : X₀.nd.mu i₀ = X₁.nd.mu i₁) (hj : X₀.nd.j i₀ = X₁.nd.j i₁) :
    (Y₀.muC i₀ : D.naut.CG 1) = Y₁.muC i₁ := by
  have hr := X₀.nd.j_range i₀
  let j : Fin D.R.m := ⟨X₀.nd.j i₀ - 1, by omega⟩
  have e₀ : j.1 + 1 = X₀.nd.j i₀ := by simp only [j]; omega
  have h₀ := U₀.muC i₀ j e₀
  have h₁ := U₁.muC i₁ j (e₀.trans hj)
  apply A.chr.e1.injective
  apply Subtype.ext
  rw [h₀, h₁, hμ]

theorem zn_of_alt {X₀ X₁ : LocNd (lay0 D)} {iq₀ : ∀ i : X₀.nd.Loc, FractionRing (X₀.nd.O i) →+* Qbar (X₀.nd.l i)}
    {iq₁ : ∀ i : X₁.nd.Loc, FractionRing (X₁.nd.O i) →+* Qbar (X₁.nd.l i)} {Y₀ : LocAut X₀} {Y₁ : LocAut X₁}
    {C₀ : LocBC Y₀} {C₁ : LocBC Y₁} (U₀ : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq₀ Y₀ C₀) (U₁ : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq₁ Y₁ C₁)
    (i₀ : X₀.nd.Loc) (i₁ : X₁.nd.Loc) (hw : X₀.nd.w i₀ = X₁.nd.w i₁) (hj : X₀.nd.j i₀ = X₁.nd.j i₁)
    (hs : ∀ v, SplitOut X₀.nd i₀ v → SplitOut X₁.nd i₁ v) (x₀ : X₀.nd.X i₀) (x₁ : X₁.nd.X i₁)
    (he : ∀ v k, SplitOut X₀.nd i₀ v → 1 ≤ k → k ≤ D.R.nV →
      iotaO X₁.nd Y₁.naut i₁ ((X₁.nd.hT i₁ v k : X₁.nd.X i₁ → X₁.nd.O i₁) x₁) =
        iotaO X₀.nd Y₀.naut i₀ ((X₀.nd.hT i₀ v k : X₀.nd.X i₀ → X₀.nd.O i₀) x₀))
    (h : x₁ ∈ ZN X₁.nd Y₁.naut i₁) : x₀ ∈ ZN X₀.nd Y₀.naut i₀ := by
  have hμ : X₀.nd.mu i₀ = X₁.nd.mu i₁ := by rw [X₀.nd.mu_w, X₁.nd.mu_w, hw]
  have hm := _root_.GlobalTheory.ExtTheta.mu_c_eq_of_mu_eq_of_j_eq U₀ U₁ i₀ i₁ hμ hj
  obtain ⟨P₁, hP₁, Pa, ⟨c1, c2, c3, c4, c5, c6⟩, hmem⟩ := h
  have ne := Y₁.naut.typeV_ne i₁ P₁
  rw [U₁.typeV] at ne
  obtain ⟨P₀, t1, t2, t3, t4⟩ := _root_.GlobalTheory.ExtTheta.transport_alt A.au M hμ hj (X₀.nd.j_range i₀).1 (X₀.nd.j_range i₀).2 (X₁.nd.j_range i₁).1
    (X₁.nd.j_range i₁).2 (U₀.S i₀) (U₀.irr i₀) (U₀.surj i₀) (U₁.S i₁ P₁) (U₁.irr i₁ P₁) ne
  have l1 : ∀ w, (Y₀.naut.locV i₀ P₀ w : D.naut.LP w) = Y₁.naut.locV i₁ P₁ w := fun w => by
    rw [C₀.embAV_loc, C₁.embAV_loc, U₀.emb, U₁.emb]; exact t2 w
  have l2 : ∀ w, Y₀.naut.satV i₀ P₀ w = Y₁.naut.satV i₁ P₁ w := fun w => by
    rw [C₀.embAV_sat, C₁.embAV_sat, U₀.emb, U₁.emb]; exact t3 w
  have l3 : Y₀.naut.infWt i₀ = Y₁.naut.infWt i₁ := by
    rw [C₀.embAV_inf i₀ P₀, C₁.embAV_inf i₁ P₁, U₀.emb, U₁.emb]; exact t4
  refine ⟨P₀, (U₀.ptV i₀ P₀ x₀).2 fun w k s ϖ h1 h2 h3 h4 h5 => ?_, Pa, ⟨c1, c2, c3, fun w hw => ?_, fun w hw => ?_, fun τ => ?_⟩, ?_⟩
  · have h6 := (U₁.ptV i₁ P₁ x₁).1 hP₁ w k s ϖ (hs w h1) h2 h3 h4 h5
    rw [U₁.typeV, he w k h1 h4 h5] at h6
    rw [U₀.typeV]
    exact t1 s ϖ k _ h6
  · exact (c4 w hw).trans (l1 w).symm
  · rw [l2]; exact c5 w hw
  · rw [l3]; exact c6 τ
  · have : (Y₀.naut.muC i₀ : D.naut.CG 1) = Y₁.naut.muC i₁ := hm
    rw [this]; exact hmem

theorem theta_loci_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ → ∀ e : L₁.lay.fixZ.nd.X i₁ ≃ L₀.lay.fixZ.nd.X i₀, (∀ (v : PlE D.host) (k : ℕ) (x : L₁.lay.fixZ.nd.X i₁), SplitOut L₁.lay.fixZ.nd i₁ v → 1 ≤ k → k ≤ D.R.nV → iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ((L₁.lay.fixZ.nd.hT i₁ v k : L₁.lay.fixZ.nd.X i₁ → L₁.lay.fixZ.nd.O i₁) x) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ ((L₀.lay.fixZ.nd.hT i₀ v k : L₀.lay.fixZ.nd.X i₀ → L₀.lay.fixZ.nd.O i₀) (e x))) → ∀ x, x ∈ L₁.lay.fixZ.nd.Z i₁ ↔ e x ∈ L₀.lay.fixZ.nd.Z i₀ := by
  intro _ D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big₀ big₁ L₀ L₁ ⟨Sp₀, ⟨U₀⟩, _⟩ ⟨Sp₁, ⟨U₁⟩, _⟩ i₀ i₁ hw hj e he x
  have s01 := _root_.GlobalTheory.ExtTheta.split_out_of_w_eq Sp₀ Sp₁ i₀ i₁ hw
  have s10 := _root_.GlobalTheory.ExtTheta.split_out_of_w_eq Sp₁ Sp₀ i₁ i₀ hw.symm
  refine (L₁.lay.zOk_fixZ.1 i₁ x).trans (Iff.trans ⟨fun h => ?_, fun h => ?_⟩ (L₀.lay.zOk_fixZ.1 i₀ (e x)).symm)
  · exact _root_.GlobalTheory.ExtTheta.zn_of_alt U₀ U₁ i₀ i₁ hw hj s01 (e x) x (fun v k h1 h2 h3 => he v k x (s01 v h1) h2 h3) h
  · exact _root_.GlobalTheory.ExtTheta.zn_of_alt U₁ U₀ i₁ i₀ hw.symm hj.symm s10 x (e x) (fun v k h1 h2 h3 => (he v k x h1 h2 h3).symm) h
end GlobalTheory.ExtTheta
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain
open Formalism.L2.NT
namespace Formalism.L2

structure NTiedAllAlt (D : D7) (C : NChoice D) (I : TwIn D) where
  gal : _root_.Formalism.L2.NGalTiedAlt D
  n : _root_.GlobalTheory.HeightCounting.NTiedGPlaceholder D
  loc : LocTied D
  data : NormalizedDataCompatibility D
  cover : NormalizedLocalCompatibility D gal.mt
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  rho : NR.NRhoTied D
  types : NormalizedTypesCompatibility D gal.fr.jE
  twF : TwFrame D
  tw : NTwTied D twF
  nct : NChTie D C
  exp : NExpTied D
  choice : NChoiceTied D C I (avDesign D)
  eMt_level : ∀ (w : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : TwistedAt D w) (hA : NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)))),
    ∃ ι : FractionRing (C.Oe w) →+* ℂ, (∀ x : D.what₂.LL, ι (C.embW w x) = D.what₂.embLL x) ∧
      (gal.mt (D.what₂.muTw w) j h1 h2).J =
        (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J ∧
      ∀ (κ : Formalism.AUTREP.GAf D.host.E D.R.nV) (h : κ ∈ (gal.mt (D.what₂.muTw w) j h1 h2).J)
        (h' : κ ∈ (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
          ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J),
        (((gal.mt (D.what₂.muTw w) j h1 h2).χ ⟨κ, h⟩ : ℂˣ) : ℂ) =
          ι (C.kMapE w (((exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
            ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).χ ⟨κ, h'⟩ : (NX.Kk D (C.twI w) (C.k' w))ˣ) :
              NX.Kk D (C.twI w) (C.k' w)))
  cf : Host.CharFrame D
  tp : Host.TupTied D cf C
  tupLink : gal.TupLink tp
  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  psi_eq : ∀ a x, (chiD.psi a).χ x = (tp.psi (D.nd.w a)).1 x
  plB : D.what₂.places.Pl → ValuationSubring ℂ
  plκ : ∀ w, haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    IsLocalRing.ResidueField (plB w) ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w)
  plB_loc : ∀ (i : D.nd.Loc) (y : D.nd.O i),
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ h : iotaOC D i y ∈ plB (D.nd.w i),
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (plκ (D.nd.w i) (IsLocalRing.residue (plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)
  plB_iota : ∀ (i : D.nd.Loc) k v x,
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    D.ntypes.iota k v (D.nd.w i) x = redThrough (plB (D.nd.w i)) (plκ (D.nd.w i)) (D.ntypes.teichC k x)
  etaT_link : ∀ (w : PlE D.host) (α : ℂ), chiD.etaT.At w α →
    D.naut.frobEig (D.naut.locG D.naut.etaT w) = {α⁻¹}
  muC_link : ∀ i : D.nd.Loc, ∀ᶠ w in Filter.cofinite, ∀ α : ℂ,
    (chiD.mu0 (D.nd.j i) * chiD.del (D.ntw.twOf i) * chiD.psi i).At w α →
    D.naut.frobEig (D.naut.locG (D.naut.muC i) w) = {α⁻¹}
  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y
end Formalism.L2
end
end
end

section



section
noncomputable section
namespace GlobalTheory.TieLabAt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    Formalism.MainNotions.SumRepresentations.tieLab D ∧ _root_.UpperTheory.GalS.LabTameS D.nd D.naut ∧ IotaRed D ∧ GlobalTheory.RowCopy.RbarTie D := by
  intro hL D P
  let γ : Fin 2 → PlE D.host → Formalism.ConjugateSelfDual.G D.host.E D.nd.Om := fun k => Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1)
  have hγ : ∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v := fun k v => (D.naut.plGw_inj k).extend_apply _ _ v
  have hT : GlobalTheory.LabLaws.LabTie P.T D.ntypes.teichC γ := by
    intro k v
    rw [hγ k v]
    exact ⟨D.ntypes.teichC_inj k, D.ntypes.tg_gen k v, P.lab k v⟩
  refine ⟨GlobalTheory.LabLaws.tieLab_of_labTie hT, _root_.GlobalTheory.LabLaws.labTameS_of_labTie hT, ?_, ⟨P.ty.rbarSS, P.ty.rbar⟩⟩
  intro i
  refine ⟨P.ty.plB (D.nd.w i), P.ty.plκ (D.nd.w i), fun y => P.ty.plB_loc i y, fun k v x => ?_⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hm := GlobalTheory.ParRay.mem_of_monoidHom (P.ty.plB (D.nd.w i)) (D.ntypes.teichC k) x
  refine ⟨hm, ?_⟩
  rw [P.ty.plB_iota i k v x]
  unfold redThrough
  exact dif_pos hm
end GlobalTheory.TieLabAt
end
end
end

end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.side_eigen_level_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ) (L₀ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → ∃ big₁ : D.what₂.places.Pl → Finset ℂ, ∀ L₁ : LocAll (lay0 D), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → ∃ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) ∧ ∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z' := by
  first | exact @_root_.GlobalTheory.CoefDuty.ExtRing.ext_ring_alt | exact _root_.GlobalTheory.CoefDuty.ExtRing.ext_ring_alt | (intros; apply _root_.GlobalTheory.CoefDuty.ExtRing.ext_ring_alt <;> assumption)
end

end
end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.side_eigen_conductor_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ → ∀ e : L₁.lay.fixZ.nd.X i₁ ≃ L₀.lay.fixZ.nd.X i₀, (∀ (v : PlE D.host) (k : ℕ) (x : L₁.lay.fixZ.nd.X i₁), SplitOut L₁.lay.fixZ.nd i₁ v → 1 ≤ k → k ≤ D.R.nV → iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ((L₁.lay.fixZ.nd.hT i₁ v k : L₁.lay.fixZ.nd.X i₁ → L₁.lay.fixZ.nd.O i₁) x) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ ((L₀.lay.fixZ.nd.hT i₀ v k : L₀.lay.fixZ.nd.X i₀ → L₀.lay.fixZ.nd.O i₀) (e x))) → ∀ x, x ∈ L₁.lay.fixZ.nd.Z i₁ ↔ e x ∈ L₀.lay.fixZ.nd.Z i₀ := by
  first | exact @_root_.GlobalTheory.ExtTheta.theta_loci_alt | exact _root_.GlobalTheory.ExtTheta.theta_loci_alt | (intros; apply _root_.GlobalTheory.ExtTheta.theta_loci_alt <;> assumption)
end

end
end
