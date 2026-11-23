module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle157
public import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalVectorValueUnitaryRankOneGindikinKarpel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory


theorem _root_.GlobalTheory.T.darbouxCoords_transport_covolumeOne_haar : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) →
    ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
    letI : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
    ∃ (lam : MeasureTheory.Measure ((κ → AF D.host.F) × (κ → AF D.host.F)))
      (𝓖 : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
      lam.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) 𝓖 lam ∧
      lam 𝓖 = 1 ∧ ∀ g : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
        ∫ w in 𝓕, g (e w) ∂ν = ∫ p in 𝓖, g p ∂lam := by
  first | exact @GlobalTheory.DarbouxMeasure.transport_covol_one | exact GlobalTheory.DarbouxMeasure.transport_covol_one | (intros; apply GlobalTheory.DarbouxMeasure.transport_covol_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.rationalDarboux_transfers_haar_fundamentalDomain : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ (ν : Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), ν.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratL T S) 𝓕 ν →
          ∃ (ν' : @Measure ((κ → AF D.host.F) × (κ → AF D.host.F)) (borel _)) (𝓕' : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
            @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
            @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) _ _ _ (borel _) 𝓕' ν' ∧
            ∀ f : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
              ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  first | exact @GlobalTheory.RatDarbouxTransfer.haar_fundDomain_transfer | exact GlobalTheory.RatDarbouxTransfer.haar_fundDomain_transfer | (intros; apply GlobalTheory.RatDarbouxTransfer.haar_fundDomain_transfer <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLower

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {M W' ι : Type} [AddCommGroup M] [Module K M]
  [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [Fintype ι]


omit [NumberField K] in
theorem inner_coef_of_rat (b : Module.Basis ι K M) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W') (pr : M →ₗ⋆[K] M →ₗ[K] K)
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a'))) (u v : M) (hu : ∀ a, b.repr u a ∈ cmMax K) :
    inner ℂ (c₁ u) (c₁ v) = σ (pr u v) := by
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr u, ← b.sum_repr v]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul,
  RingHom.id_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [starRingEnd_apply (b.repr u a'), hu a' σ]

theorem inner_eq_csumAt (S : CSD K) (hb : S.HasRatBasis) (b : Module.Basis ι K M) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W')
    (pr : M →ₗ⋆[K] M →ₗ[K] K) (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a')))
    (e : S.V ≃ₗ[K] M) (hr : ∀ i a, b.repr (e (S.bV i)) a ∈ cmMax K) (he : ∀ x x', pr (e x) (e x') = S.pair x x')
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : S.Forms →ₛₗ[σ] H)
    (hj : ∀ x y : S.Forms, inner ℂ (j x) (j y) =
      ∑ c, ((S.wt c : ℂ))⁻¹ * inner ℂ (c₁ (e ((x : S.Cl → S.V) c))) (c₁ (e ((y : S.Cl → S.V) c)))) (x y : S.Forms) :
    inner ℂ (j x) (j y) = csumAt S σ x y := by
  have hrat : ∀ k c a, b.repr (e ((S.basis k : S.Cl → S.V) c)) a ∈ cmMax K := by
    intro k c a
    rw [← S.bV.sum_repr ((S.basis k : S.Cl → S.V) c)]

    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (S.basis_rat hb k c i) (hr i a)
  have hH : ∀ k l, inner ℂ (j (S.basis k)) (j (S.basis l)) = σ (S.H k l) := by
    intro k l
    rw [hj]
    unfold CSD.H CSD.csum

    rw [Matrix.of_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_coef_of_rat b σ c₁ pr hp _ _ (hrat k c), he, map_mul, map_inv₀, map_natCast]
  conv_lhs => rw [← S.basis.sum_repr x, ← S.basis.sum_repr y]
  unfold csumAt

  simp only [map_sum, LinearMap.map_smulₛₗ, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hH,
  dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [starRingEnd_apply]
  ring

theorem inner_eq_csumAt_of_pres {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ι₀ : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι₀ S σ₀ ρ J χ) (b : Module.Basis ι K M) (c₀ : M →ₛₗ[σ₀] W) (pr : M →ₗ⋆[K] M →ₗ[K] K)
    {Q : (S.V ≃ₗ[K] M) → Prop}
    (hP : ∃ e : S.V ≃ₗ[K] M, (∀ i a, b.repr (e (S.bV i)) a ∈ cmMax K) ∧ (∀ x, P.coef x = c₀ (e x)) ∧
      (∀ x x', pr (e x) (e x') = S.pair x x') ∧ Q e)
    (hb : S.HasRatBasis) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W')
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a')))
    (H : HMod (G → W')) (j : S.Forms →ₛₗ[σ] H.H)
    (hH : ∀ x y : H.H, inner ℂ x y = Bridge.adInner ι₀ J P.y (H.e x) (H.e y))
    (hj : ∀ (x : S.Forms) h, ∃ v, P.ext (x : S.Cl → S.V) h = c₀ v ∧ H.e (j x) h = c₁ v) (x y : S.Forms) :
    inner ℂ (j x) (j y) = csumAt S σ x y := by
  obtain ⟨e, hr, he, hpair, -⟩ := hP
  have hval : ∀ (z : S.Forms) cl, H.e (j z) (P.y cl) = c₁ (e (z.1 cl)) := by
    intro z cl
    obtain ⟨v, h0, h1⟩ := hj z (P.y cl)
    have h3 : P.coef (z.1 cl) = P.coef (e.symm v) := by
      rw [← GlobalTheory.PresBasic.ext_y P z cl, h0, he, e.apply_symm_apply]
    rw [h1, GlobalTheory.PresBasic.coef_injective _ h3, e.apply_symm_apply]
  refine inner_eq_csumAt S hb _ σ c₁ _ hp e hr hpair j (fun z w => ?_) x y
  rw [hH]
  unfold Bridge.adInner
  refine Finset.sum_congr rfl fun cl _ => ?_
  rw [hval, hval, CSD.wt, ← Nat.card_eq_fintype_card, Nat.card_congr (P.stabI cl).toEquiv]

end Generic

theorem inner_conjForms_eq_csumAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) c c₁ H j, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ x y, ⟪j x, j y⟫_ℂ = csumAt (A.MtCSD i A.μ0) σ x y := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hjV gramR c0R c0L hT i σ c c₁ H j hC x y
  have hb : (A.MtCSD i A.μ0).HasRatBasis :=
    (GlobalTheory.HeckeRational.dcOp_matrix_mem_cmMax (Vc D i) (R.cV i).coef (R.βV i) (R.datVt i A.μ0) (R.B.L i A.μ0).pres
      (hT.coefL i A.μ0) (hT.mapL i)
      (fun g a k => (coefAction_repr_mem_subfield (labLL D) _ _ GlobalTheory.HeckeRational.labLL_mem_cmMax g a k).2) {1} 1
      (fun f => by funext h; simp [Bridge.dcOp])).1
  have h1 := hC.model.choose_spec.2.2.2
  have h2 : ∀ (z : A.fam.amb.FL i A.μ0) h, ∃ v, (R.B.L i A.μ0).pres.ext z.1 h = c0L i v ∧ H.e (j z) h = c₁ v :=
    fun z h => (hC.base z h).imp fun v hv => ⟨(congrFun (hjV i A.μ0 z) h).symm.trans hv.1, hv.2⟩
  exact inner_eq_csumAt_of_pres (R.B.L i A.μ0).pres _ (c0L i) _ (hT.coefL i A.μ0) hb σ c₁ hC.pair H j h1 h2 x y

end GlobalTheory.LiftLower

end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.det_valuations_sum_zero_same_local_lattice : ∀ (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (g n : ℕ) (L : Submodule (𝓞 K) (Fin g → K)) (b : Fin n → Fin g → K), GlobalTheory.PtDeg.LocBasis 𝔓 L b → ∀ (M : Matrix (Fin n) (Fin n) K) (u : Fin n → Fin g → K), (∀ i, u i = ∑ j, M i j • b j) → ∀ (C : Matrix (Fin n) (Fin n) T.Fr), (∀ i, (∑ j, C i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin g → K) k => iK (v k)) '' (L : Set (Fin g → K)))) → (∀ v ∈ L, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C i j • fun k => iK (u j k))) → M.det ≠ 0 ∧ C.det ≠ 0 ∧ vV T.V C.det + vV T.V (iK M.det) = 0 := by
  first | exact @GlobalTheory.TwoBasesDet.det_vV_add_eq_zero | exact GlobalTheory.TwoBasesDet.det_vV_add_eq_zero | (intros; apply GlobalTheory.TwoBasesDet.det_vV_add_eq_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteUnitary_localPoints_transfer_iff : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU (E := D.host.E) (n := V.rank) ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e f, IsPrimeIdem P e f) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ SuppF V f (cj j h₀ x)) := by
  first | exact @GlobalTheory.DefTransfer.Loc.locU_iff | exact GlobalTheory.DefTransfer.Loc.locU_iff | (intros; apply GlobalTheory.DefTransfer.Loc.locU_iff <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

theorem _root_.GlobalTheory.T.mem_weylCellUnitaryGroup_longSimpleReflection_iff : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n → ∀ (y : GU σ n),
    IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (u : GU σ n),
    u ∈ cellU y ↔ ∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  first | exact @GlobalTheory.cellU_rankOne_shape | exact GlobalTheory.cellU_rankOne_shape | (intros; apply GlobalTheory.cellU_rankOne_shape <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

theorem _root_.GlobalTheory.T.unitaryWeylSimpleReflection_rev_comm_sq_eq_one : ∀ (n : ℕ) (k : Fin (n / 2)), (∀ i, simpleU k i.rev = (simpleU k i).rev) ∧ simpleU k * simpleU k = 1 := by
  first | exact @GlobalTheory.simpleU_rev_and_sq | exact GlobalTheory.simpleU_rev_and_sq | (intros; apply GlobalTheory.simpleU_rev_and_sq <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

theorem _root_.GlobalTheory.T.chiDeltaU_conj_longSimpleReflection_unitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (y : GU σ n), IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (α : Fin (n / 2) → ℂˣ) (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) *
        (q : ℂ) ^ (-2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
  first | exact @GlobalTheory.GKUnitary.chiDeltaU_conj_simpleU_long | exact GlobalTheory.GKUnitary.chiDeltaU_conj_simpleU_long | (intros; apply GlobalTheory.GKUnitary.chiDeltaU_conj_simpleU_long <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

theorem _root_.GlobalTheory.T.unitaryRankOne_sphericalIntegrand_diagonal_torus_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂˣ) (φ : GU σ n → ℂ), IsSphericalU q (fun i => (α i : ℂ)) φ →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → ∀ w x : GU σ n,
      φ (y⁻¹ * t * w * x) * (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
        chiDeltaU q (fun i => (actU k α i : ℂ)) t * φ (y⁻¹ * w * x) := by
  first | exact @GlobalTheory.WeylCell.U21TorusFactor.torus_factor | exact GlobalTheory.WeylCell.U21TorusFactor.torus_factor | (intros; apply GlobalTheory.WeylCell.U21TorusFactor.torus_factor <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

theorem _root_.GlobalTheory.T.sphericalVector_value_unitaryRankOne_gindikinKarpelevich : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (α : Fin (n / 2) → ℂ) (φ : GU σ n → ℂ), IsSphericalU q α φ → φ 1 = 1 →
    ∀ (y : GU σ n), y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (u : GU σ n), (∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j) →
    φ (y⁻¹ * u) = if Valued.v (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ 1 then 1
      else α k ^ (-ordL (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)) *
        (q : ℂ) ^ (ordL (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)) := by
  first | exact @GlobalTheory.GKUnitaryRankOne.value_rankOne | exact GlobalTheory.GKUnitaryRankOne.value_rankOne | (intros; apply GlobalTheory.GKUnitaryRankOne.value_rankOne <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.holomorphicRestrictionSubalgebraFrameDomain_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.dom.Nonempty → IsDomain (GlobalTheory.FlatPair.holAlg X) := by
  first | exact @GlobalTheory.FlatPair.holAlg_isDomain | exact GlobalTheory.FlatPair.holAlg_isDomain | (intros; apply GlobalTheory.FlatPair.holAlg_isDomain <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJReg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def chiS (ν : kˣ →* ℂˣ) (s : ℂ) (g : GL (Fin n) k) : ℂ := (ν (gdet g) : ℂ) * apow (gdet g) s

theorem chiS_mul (ν : kˣ →* ℂˣ) (s : ℂ) (g h : GL (Fin n) k) : chiS ν s (g * h) = chiS ν s g * chiS ν s h := by
  simp only [chiS, gdet_mul, map_mul, Units.val_mul, apow_mul]; ring

@[simp] theorem chiS_one (ν : kˣ →* ℂˣ) (s : ℂ) : chiS ν s (1 : GL (Fin n) k) = 1 := by
  simp [chiS, gdet]

theorem chiS_inv_mul (ν : kˣ →* ℂˣ) (s : ℂ) (g : GL (Fin n) k) : chiS ν s g⁻¹ * chiS ν s g = 1 := by
  rw [← chiS_mul, inv_mul_cancel, chiS_one]

theorem chiS_of_mem_KO {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (s : ℂ) {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    chiS ν s g = 1 := by
  have hv := valuation_gdet_of_mem_KO hg
  simp [chiS, hν _ hv, apow_of_valuation_eq_one hv]

def latInd (g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k → ℂ := fun X =>
  (intM k (Fin n) (Fin n)).indicator 1 (X * (g⁻¹ : GL (Fin n) k).val)

theorem latInd_mem_SB (g : GL (Fin n) k) : latInd g ∈ SB (Matrix (Fin n) (Fin n) k) :=
  restrict_mem_SB (P' := g.val) (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    indicator_intM_mem_SB

theorem mul_left_mem_SB (g : GL (Fin n) k) {φ : Matrix (Fin n) (Fin n) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin n) (Fin n) k)) : (fun X => φ (g.val * X)) ∈ SB (Matrix (Fin n) (Fin n) k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have c1 : Continuous fun X : Matrix (Fin n) (Fin n) k => g.val * X := continuous_const.matrix_mul continuous_id
  have c2 : Continuous fun X : Matrix (Fin n) (Fin n) k => (g⁻¹).val * X := continuous_const.matrix_mul continuous_id
  have e : Topology.IsClosedEmbedding fun X : Matrix (Fin n) (Fin n) k => g.val * X :=
    Function.LeftInverse.isClosedEmbedding (f := fun X => (g⁻¹).val * X)
      (fun X => by simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul])
      c2 c1
  exact ⟨hφ.1.comp_continuous c1, hφ.2.comp_isClosedEmbedding e⟩

theorem mul_right_mem_SB (g : GL (Fin n) k) {φ : Matrix (Fin n) (Fin n) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin n) (Fin n) k)) : (fun X => φ (X * g.val)) ∈ SB (Matrix (Fin n) (Fin n) k) :=
  restrict_mem_SB (P' := (g⁻¹).val) (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hφ


variable (k n) in
def kInd : Matrix (Fin n) (Fin n) k → ℂ := {X | ∃ g ∈ KO k (Fin n), g.val = X}.indicator 1

def gjZ [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (s : ℂ) (φ : Matrix (Fin n) (Fin n) k → ℂ) : ℂ :=
  ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) s ∂(haarVol (KO k (Fin n)))

end GlobalTheory.GJReg
end
end
