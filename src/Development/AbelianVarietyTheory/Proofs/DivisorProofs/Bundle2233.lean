module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTorsionMemClosureGenerators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle211
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceThetaFunctionVacuumConjugatePlace
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle240
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.TorsGen

theorem exists_linear_pow_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    GlobalTheory.Serre.IsLinearHom A.t.act B.t.act G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∃ F : A.t.G ⟶ B.t.G, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act F ∧ F ^ m = G := by
  intro E _ _ _ H K _ _ σ A B G hG m hm hker
  have hGm := hG.isMonHom
  obtain ⟨_, hfl, hsu, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp (𝓞 K)) A.pol m hm
  have : Flat (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m).left := hfl
  have : Surjective (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m).left := hsu
  have hc : IsCommMonObj A.t.G := A.ab.comm
  have hcB : IsCommMonObj B.t.G := B.ab.comm
  have hall := GlobalTheory.T.hom_kills_torsion_of_complexPoints_oneEmbedding E H K σ A B G hGm m hm hker
  obtain ⟨F, hF⟩ := GlobalTheory.DivisibleHom.exists_factor (A := A.t.G) m G hall
  have hFm : IsMonHom (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m ≫ F) := hF ▸ hGm
  have : IsMonHom F := GlobalTheory.DivisibleHom.isMonHom_of_factor m F
  refine ⟨F, ⟨this, fun c => ?_⟩, by rw [← hF, GlobalTheory.DivisibleHom.mulA_comp]⟩
  have := A.t.act.hom c
  have := B.t.act.hom c
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m)
  rw [← Category.assoc, GlobalTheory.DivisibleHom.mulA_comp, ← GlobalTheory.DivisibleHom.comp_mulA, Category.assoc, hF, hG.comm,
    ← Category.assoc, hF]

theorem gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (n : ℕ), 0 < n →
    ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
    y ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
      ∃ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (f : (X.A true).t.G ⟶ X.B.t.G),
        x ^ n = 1 ∧ GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
        (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) ∧
        w = x ≫ f} := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X n hn y hy
  refine Submonoid.closure_mono ?_ (GlobalTheory.T.cm_torsion_mem_closure_generators E H hH K ρ σ₁ p X n hn y hy)
  rintro w ⟨m, x, z, hm, hx, hG, rfl⟩
  obtain ⟨F, hF, hFm⟩ := exists_linear_pow_eq E H K σ₁ (X.A true) X.B _
    (GlobalTheory.FlatCM.HomLat.isLinearHom_prod X z) m hm hG
  have := hF.isMonHom
  refine ⟨x ^ m, F, ?_, hF, ⟨m, hm, z, hFm⟩, ?_⟩
  · rw [← pow_mul, mul_comm, hx]
  · rw [← hFm, MonObj.comp_pow, MonObj.pow_comp]

end GlobalTheory.FlatCM.TorsGen

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.squareModel_negSpace_goodSchroedinger : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW₁ G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (-1 : D.host.E) • (spW₁ G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid (i : ℕ) (j : ℕ))).map (conjU _ (-1) hJ)) dom) B.ψ := by
  first | exact @GlobalTheory.FunObj.squareModelW₁_good | exact GlobalTheory.FunObj.squareModelW₁_good | (intros; apply GlobalTheory.FunObj.squareModelW₁_good <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SquareExps

open GlobalTheory.Chain.StepVac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasInfExp_one_of (τ : D.what₂.Tau) (h : ∃ θ, IsInfFam (D := D) θ) : HasInfExp D (1 : (AE D)ˣ →* Circle) τ 0 :=
  ⟨0, by simp, h, fun θ _ x _ _ => by simp⟩

theorem hasInfExp_pow {η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {b : ℚ} (h : HasInfExp D η τ b) (n : ℕ) :
    HasInfExp D (η ^ n) τ (n * b) := by
  induction n with
  | zero =>
    obtain ⟨_, _, hθ, _⟩ := h
    simpa using hasInfExp_one_of τ hθ
  | succ n ih =>
    rw [pow_succ]
    have := hasInfExp_mul ih h
    convert this using 1
    push_cast; ring

theorem eta_exp {μ₀ : T} (hL : L.Is μ₀) (τ : D.what₂.Tau) : HasInfExp D L.eta τ (1 / 2) :=
  GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
    (hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ

theorem alpha_exp {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (alpha G t i j) τ (-(D.hc τ).e ⟨j, hj⟩ + (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j : ℚ) * (1 / 2)) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 ⟨j, hj⟩) (hasInfQ_tau (L.C.isMu0 ⟨j, hj⟩).inf) τ
  obtain ⟨θ, hθ⟩ : ∃ θ, IsInfFam (D := D) θ := by
    obtain ⟨_, _, hθ, _⟩ := h0
    exact hθ
  have h1 : HasInfExp D (L.mu t (j + 1)) τ (-(D.hc τ).e ⟨j, hj⟩) := by
    have := hasInfExp_mul h0 (hasInfExp_of_order hθ (hL.xi t) hn ho τ)
    rw [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
    exact this
  exact hasInfExp_mul h1 (hasInfExp_pow (eta_exp hL τ) _)

theorem beta_exp {μ₀ : T} (hL : L.Is μ₀) (i j : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (beta G i j) τ ((cen D sc.cGap τ (D.R.m - i) : ℚ) + (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j : ℚ) * (1 / 2)) := by
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  exact hasInfExp_mul h0 (hasInfExp_pow (eta_exp hL τ) _)

theorem exps : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ mα mβ : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (alpha G t i j) mα ∧
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (beta G i j) mβ ∧
      ∀ w, (((spW G i j).rank + (spW₁ G i j).rank : ℕ) : ℤ) < mα w - mβ w := by
  intro D T L sc G μ₀ hL t i j _ τf hτf
  obtain ⟨mα, hα, eα⟩ := GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => alpha_exp (G := G) hL t i j j.2 τ) τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => beta_exp (G := G) hL i j i.2 τ) τf hτf
  refine ⟨mα, mβ, hα, hβ, fun w => ?_⟩
  have hr : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have key := GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre sc.cGap (τf w) i j i.2 j.2
  have e1 : (spW G i j).rank = rankV D (i + 1) (j + 1) := hr _ _ (by omega) (by omega)
  have e2 : (spW₁ G i j).rank = rankV D i j := hr _ _ (by omega) (by omega)
  rw [e1, e2]
  have h1 := eα w
  have h2 := eβ w
  have : (((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ) := by
    push_cast at h1 h2 key ⊢
    rw [h1, h2]
    linarith
  exact_mod_cast this

end GlobalTheory.SquareExps

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.WeilThetaRat

theorem dbl_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    {κ : Type} [Fintype κ] (hκ : Fintype.card κ = a * b)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ)
    (hd : ∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ))
    (hdd : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (χ : Chr F E) (hχ : IsHecke F E χ)
    (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (hS : IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (hR : SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (g : UG (cA σ) (dbl (incM F JB))) (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) (hg : ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F g₀) :
    ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd g φ) = thetaSum F φ := by
  intro φ hφ
  obtain ⟨p, q, p', p₀, q₀, p₀', t, s, t', hp, hq, hp', ht, hs, ht', rfl⟩ :=
    GlobalTheory.T.doubledUnitary_rational_eq_diagonalFixers_product F E σ hσ b JB ε hJ hdet g g₀ hg
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  calc
    _ = thetaSum F (omd q (omd p' φ)) :=
      GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR p p₀ hp t ht (omd q (omd p' φ)) (hS.pres q _ (hS.pres p' _ hφ))
    _ = thetaSum F (omd p' φ) :=
      GlobalTheory.T.adelicThetaSum_doubledWeil_antidiagonal_invariant F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR q q₀ hq s hs (omd p' φ) (hS.pres p' _ hφ)
    _ = thetaSum F φ :=
      GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR p' p₀' hp' t' ht' φ hφ

theorem member_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    {κ : Type} [Fintype κ] (hκ : Fintype.card κ = a * b)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ)
    (hd : ∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (χ : Chr F E) (hχ : IsHecke F E χ) (om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (γ : UG (cA σ) (incM F JB)) (γ₀ : Matrix (Fin b) (Fin b) E)
    (hγ : ((γ : GL (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F γ₀) :
    ∀ Φ ∈ schA F κ, thetaSum F (om γ Φ) = thetaSum F Φ := by
  intro Φ hΦ
  obtain ⟨hom, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (cA σ) (Fin b) (incM F JB) γ
  have hgd0 : ((gd : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F (Matrix.fromBlocks γ₀ 0 0 1) := by
    rw [hgd, hγ]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨φ₂, hφ₂, hθ⟩ := GlobalTheory.T.exists_adelicSchwartz_thetaDistributionSum_ne_zero F κ
  have hb := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ Φ hΦ φ₂ hφ₂
  have e1 := dbl_rat σ hσ ψ hψ JA JB ε hJ hdet hκ d hd dd hdd χ hχ omd hS.toIsSplitting hR gd _ hgd0 _ hb
  rw [hres γ gd hgd Φ hΦ φ₂ hφ₂, GlobalTheory.T.adelicThetaDistributionSum_productFunction F κ κ _ (hom.pres γ Φ hΦ) φ₂ hφ₂, GlobalTheory.T.adelicThetaDistributionSum_productFunction F κ κ Φ hΦ φ₂ hφ₂] at e1
  exact mul_right_cancel₀ hθ e1

theorem rat_mat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {γ : UA σ J} (hγ : γ ∈ ratU σ J) :
    ∃ γ₀ : Matrix (Fin n) (Fin n) E, ((γ.1 : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F γ₀ := by
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
  refine ⟨(g₀ : Matrix (Fin n) (Fin n) E), ?_⟩
  rw [← hg₀]
  ext i j
  rfl

theorem thetaSum_om_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 → ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW → ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JW) co χX χW om → ∀ γ ∈ ratU σ JX, ∀ γ' ∈ ratU σ JW, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ :=
  PositivityTheory.ThKF0.darboux_coordinates_rational_exist

end GlobalTheory.WeilThetaRat
end
end

section

namespace ThetaInjectivity
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThetaInj

theorem schr_reindex {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (σ : κ ≃ κ') (w : (κ' → R) × (κ' → R)) (φ : (κ → R) → ℂ) (x : κ' → R) :
    GlobalTheory.WeilM.schr ψ w (fun u : κ' → R => φ (u ∘ σ)) x =
      GlobalTheory.WeilM.schr ψ (w.1 ∘ σ, w.2 ∘ σ) φ (x ∘ σ) := by
  have hd : ∀ u v : κ' → R, (u ∘ σ) ⬝ᵥ (v ∘ σ) = u ⬝ᵥ v := fun u v =>
    Equiv.sum_comp σ fun i => u i * v i
  simp only [GlobalTheory.WeilM.schr, hd]
  rfl

theorem thetaSum_reindex (F : Type) [Field F] [NumberField F] {κ κ' : Type} (σ : κ ≃ κ')
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (fun u : κ' → AdeleRing (𝓞 F) F => Φ (u ∘ σ)) = GlobalTheory.WeilM.thetaSum F Φ := by
  unfold GlobalTheory.WeilM.thetaSum
  exact (Equiv.arrowCongr σ.symm (Equiv.refl F)).tsum_eq
    (fun ξ : κ → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))

theorem theta_transform_injOn : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w, GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ) = GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ')) →
      Φ = Φ' := by
  intro D ψ hψ κ _ Φ hΦ Φ' hΦ' h
  classical
  have hR : IsTotallyReal D.host.F := inferInstance
  let σ := Fintype.equivFin κ
  have key : ∀ (Ψ : (κ → AF D.host.F) → ℂ) (w : GlobalTheory.ThetaTransform.VA D.host.F (Fintype.card κ)),
      GlobalTheory.ThetaTransform.thV ψ (fun u : Fin (Fintype.card κ) → AF D.host.F => Ψ (u ∘ σ)) w =
        GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (w.1 ∘ σ, w.2 ∘ σ) Ψ) := by
    intro Ψ w
    rw [← thetaSum_reindex D.host.F σ (GlobalTheory.WeilM.schr ψ (w.1 ∘ σ, w.2 ∘ σ) Ψ)]
    unfold GlobalTheory.ThetaTransform.thV
    congr 1
    funext x
    exact schr_reindex ψ σ w Ψ x
  have e := GlobalTheory.ThetaTransform.thV_injOn hR hψ.1 (GlobalTheory.ThetaTransform.comp_mem_schA σ hΦ)
    (GlobalTheory.ThetaTransform.comp_mem_schA σ hΦ') (funext fun w => by rw [key, key]; exact h _)
  funext x
  have := congrFun e (x ∘ σ.symm)
  simpa [Function.comp_assoc] using this

end GlobalTheory.CompanionTheory.ThetaInj

end

end ThetaInjectivity
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.thetaTransform_injOn_adelicSchwartzSpace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w, GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ) = GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ')) →
      Φ = Φ' := by
  first | exact @ThetaInjectivity.GlobalTheory.CompanionTheory.ThetaInj.theta_transform_injOn | exact ThetaInjectivity.GlobalTheory.CompanionTheory.ThetaInj.theta_transform_injOn | (intros; apply ThetaInjectivity.GlobalTheory.CompanionTheory.ThetaInj.theta_transform_injOn <;> assumption)

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

theorem _root_.GlobalTheory.T.splitPlace_thetaFunction_vacuum_conjugatePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ φ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ φ ∧ φ ≠ 0 ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            heisOF σ JS JT ξ₀ B.ψ y φ = φ ∨
            ∃ u : WOF F E nS nT, heisOF σ JS JT ξ₀ B.ψ u φ = φ ∧
              B.ψ (symplOHF σ JS JT ξ₀ u y - symplOHF σ JS JT ξ₀ y u) ≠ 1 := by
  exact @PositivityTheory.ThKW.SplitVacuumEigenvectors.exists_vac_split
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.exists_thetaZeroMeanLogLeConstMul : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D := by
  first | exact @GlobalTheory.Theta0MeanLeC.theta0MeanLeC | exact GlobalTheory.Theta0MeanLeC.theta0MeanLeC | (intros; apply GlobalTheory.Theta0MeanLeC.theta0MeanLeC <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StageDict

theorem fst_isFinF_frames : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW), (∀ τ, (GlobalTheory.SquareComm.frSgn true FA).cart τ = -X.rA.s τ) →
    (∀ τ, FW.cart τ = X.rW.s τ) → X.Is ψ θ α β νH S → ∀ t, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t) := by
  intro D T A A' WW X ψ θ α β νH S FA FW hcA hcW hX t
  have hv := hX.isVac
  have hν : Formalism.L2.Theta.IsHeckeChar D (α t / β t) := by
    have h := (hX.weil t).hecT
    rw [← inv_div]
    refine ⟨?_, fun x => ?_⟩
    · exact continuous_inv.comp h.1
    · show ((β t / α t) _)⁻¹ = 1
      rw [h.2 x, inv_one]
  have hI : X.ideal S t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_
    rw [Ideal.zero_eq_bot]
    exact w.ne_bot
  obtain ⟨f₁, h1, h1t⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW (α t / β t) (X.e t) (S t) (X.ideal S t) X.vac
    hX.rigA hX.rigW hν (hX.idem t) hI hv
  have heq : X.f t = f₁ := by
    obtain ⟨⟨Tm, hT⟩, hall⟩ := hX.fst t
    rw [hall Tm hT, h1.2 Tm hT]
  have hft : IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (X.f t) := heq ▸ h1t
  refine ⟨hft, fun τ => ?_⟩
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.idem t)
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hv.1.1.1 hv.2.inf ho.infPart_eq ho.conj.infPart_eq
    (hX.fst t) hv.2.theta hft (hv.2.fock τ)
  rw [hcA τ, hcW τ]
  exact hF

end GlobalTheory.StageDict
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.ray_q_surjective_and_quasiCompact : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X] {oa : D.OAct O} (Y : Ray oa), Surjective Y.q.left ∧ QuasiCompact Y.q.left := by
  first | exact @GlobalTheory.RayEv.Ray.surjective_quasiCompact_q | exact GlobalTheory.RayEv.Ray.surjective_quasiCompact_q | (intros; apply GlobalTheory.RayEv.Ray.surjective_quasiCompact_q <;> assumption)
end
