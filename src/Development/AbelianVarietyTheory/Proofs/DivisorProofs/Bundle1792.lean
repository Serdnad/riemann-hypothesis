module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupOperatorDepthMulDisjointColumns
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle249
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1762
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChgPfTP
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

namespace GlobalTheory.FinLatF

theorem latRepF_cont : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ f (w : WOF F E nS nT), Continuous fun p : GAF σ JS × GAF σ JT => (Om p f : WOF F E nS nT → ℂ) w := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om h f u
  have hσ : ∀ x, σ (σ x) = x := fun x => GlobalTheory.AdelicU.cm_conj_conj hB.cm x
  have H := isHeis_opFF hσ hS hT hξ hc h.hw
  have hfix : ∀ p : GAF σ JS × GAF σ JT, (∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ) →
      ∀ e, Fixes (opFF hc w) (latF F E nS nT Λ) e → Om p e = e := by
    intro p hp e he
    rw [h.vac p e he]
    exact GlobalTheory.FinWeilO.normOp_of_le H lam (h.sd' p) (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he
  have hev : ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), Om p f = f := by
    intro f
    have hf : f ∈ Submodule.span ℂ {m | ∃ x e, Fixes (opFF hc w) (latF F E nS nT Λ) e ∧ m = opFF hc w x e} := by
      rw [h.span]; trivial
    induction hf using Submodule.span_induction with
    | mem _ hm =>
      obtain ⟨x, e, he, rfl⟩ := hm
      obtain ⟨N, hN, hNl⟩ := h.lev (w • x)
      filter_upwards [h.near, h.near' x N hN] with p hp hp'
      obtain ⟨l, hl, hl'⟩ := hp'
      have e2 : gamFF σ JS JT ξ₀ B.ψ (w • x) (N • l) = 1 := by
        rw [gamFF, ← symplOHF_add_self, AddChar.map_add_eq_mul, XFF.coe_nsmul, hNl l hl, one_mul]
      have e4 := H.comp x (N • l) e
      rw [he _ (nsmul_mem hl N), e2, one_smul] at e4
      rw [h.op, hfix p hp e he, hl', ← e4]
    | zero => exact Filter.Eventually.of_forall fun p => map_zero _
    | add u v _ _ hu hv => filter_upwards [hu, hv] with p h3 h4 using by rw [map_add (f := _), h3, h4]
    | smul c u _ hu => filter_upwards [hu] with p h3 using by rw [map_smul, h3]
  haveI : IsTopologicalGroup (GAF σ JS) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsTopologicalGroup (GAF σ JT) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h1 : Filter.Tendsto (fun p => q⁻¹ * p) (𝓝 q) (𝓝 1) :=
    (continuous_const.mul continuous_id).tendsto' q 1 (inv_mul_cancel q)
  refine continuousAt_const.congr (f := fun _ => (Om q f : WOF F E nS nT → ℂ) u) ?_
  filter_upwards [h1.eventually (hev f)] with p hp
  conv_rhs => rw [← mul_inv_cancel_left q p, map_mul, Module.End.mul_apply, hp]

end GlobalTheory.FinLatF
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.LinChange

open MvPowerSeries GlobalTheory.FGDepth

section Rules

variable {K : Type} [Field K] {σ : Type}

private theorem mfact_eq_prod_factorial [Fintype σ] (α : σ →₀ ℕ) :
    (mfact α : K) = ∏ x, ((α x).factorial : K) := by
  unfold mfact
  exact Finsupp.prod_fintype _ _ (fun _ => by simp)

theorem mfact_add_single [Fintype σ] [DecidableEq σ] (α : σ →₀ ℕ) (l : σ) :
    (mfact (α + Finsupp.single l 1) : K) = mfact α * ((α l : K) + 1) := by
  rw [mfact_eq_prod_factorial, mfact_eq_prod_factorial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ l),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ l)]
  have hrest : ∏ x ∈ Finset.univ.erase l, (((α + Finsupp.single l 1 : σ →₀ ℕ) x).factorial : K) =
      ∏ x ∈ Finset.univ.erase l, ((α x).factorial : K) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hx)), add_zero]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

theorem derivAt0_add' (P Q : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (P + Q) g = derivAt0 P g + derivAt0 Q g := by
  classical
  rw [derivAt0_eq_sum_of_subset (P + Q) g MvPolynomial.support_add,
    derivAt0_eq_sum_of_subset P g (Finset.subset_union_left (s₂ := Q.support)),
    derivAt0_eq_sum_of_subset Q g (Finset.subset_union_right (s₁ := P.support)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem derivAt0_smulP (b : K) (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (b • P) g = b * derivAt0 P g := by
  classical
  rw [derivAt0_eq_sum_of_subset (b • P) g MvPolynomial.support_smul, derivAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem derivAt0_smulG (b : K) (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 P (b • g) = b * derivAt0 P g := by
  unfold derivAt0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPowerSeries.coeff_smul]
  ring

theorem derivAt0_sumG {κ : Type} (s : Finset κ) (P : MvPolynomial σ K) (f : κ → MvPowerSeries σ K) :
    derivAt0 P (∑ i ∈ s, f i) = ∑ i ∈ s, derivAt0 P (f i) := by
  unfold derivAt0

  simp_rw [map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem derivAt0_C' (a : K) (g : MvPowerSeries σ K) :
    derivAt0 (MvPolynomial.C a) g = a * constantCoeff g := by
  rw [MvPolynomial.C_apply, DepthAdd.derivAt0_monomial, DepthAdd.mfact_zero',
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, mul_one]

theorem derivAt0_mul_X [Fintype σ] (P : MvPolynomial σ K) (l : σ) (g : MvPowerSeries σ K) :
    derivAt0 (P * MvPolynomial.X l) g = derivAt0 P (pderiv l g) := by
  classical
  have hP : P * MvPolynomial.X l =
      ∑ α ∈ P.support, MvPolynomial.monomial (α + Finsupp.single l 1) (P.coeff α) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [show (MvPolynomial.X l : MvPolynomial σ K) = MvPolynomial.monomial (Finsupp.single l 1) 1 from rfl,
      MvPolynomial.monomial_mul, mul_one]
  rw [hP, DepthAdd.derivAt0_sum]
  conv_rhs => unfold derivAt0
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [DepthAdd.derivAt0_monomial, MvPowerSeries.coeff_pderiv, mfact_add_single]
  ring

private theorem constantCoeff_subst_of_constantCoeff_zero' {K ι Λ : Type} [Field K] [Finite ι] (A : ι → MvPowerSeries Λ K)
    (hA : ∀ l, constantCoeff (A l) = 0) (Ψ : MvPowerSeries ι K) :
    constantCoeff (subst A Ψ) = constantCoeff Ψ := by
  have hs : HasSubst A := hasSubst_of_constantCoeff_zero hA
  have h := constantCoeff_subst_eq_zero hs hA (f := Ψ - C (constantCoeff Ψ)) (by simp)
  rw [subst_sub hs, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

private theorem pderiv_sum_smul_X_eq_C {K ι Λ : Type} [Field K] [Fintype Λ] [DecidableEq Λ] (β : Λ → ι → K)
    (lam : Λ) (l : ι) :
    pderiv lam (∑ lam', β lam' l • (X lam' : MvPowerSeries Λ K)) = C (β lam l) := by

  rw [map_sum, Finset.sum_eq_single lam]
  · rw [Derivation.map_smul, pderiv_X_self, MvPowerSeries.smul_eq_C_mul, mul_one]
  · intro b _ hb
    rw [Derivation.map_smul, pderiv_X_of_ne hb, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ lam) h

end Rules

end GlobalTheory.IsoTriv.LinChange

namespace GlobalTheory.IsoTriv

open MvPowerSeries GlobalTheory.FGDepth GlobalTheory.IsoTriv.LinChange

theorem linSt_holds : LinSt := by
  unfold LinSt
  intro K _ _ ι Λ _ _ β P
  classical
  have hA0 : ∀ l : ι, constantCoeff (∑ lam, β lam l • (X lam : MvPowerSeries Λ K)) = 0 := by
    intro l
    simp [MvPowerSeries.smul_eq_C_mul]
  induction P using MvPolynomial.induction_on
  · rename_i a
    intro Ψ
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, derivAt0_C', derivAt0_C',
      constantCoeff_subst_of_constantCoeff_zero' _ hA0]
  · rename_i p q hp hq
    intro Ψ
    rw [map_add (f := _), derivAt0_add', derivAt0_add', hp, hq]
  · rename_i p lam hp
    intro Ψ
    have hterm : ∀ l : ι, MvPolynomial.aeval
        (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι K)) p *
          (MvPolynomial.C (β lam l) * MvPolynomial.X l) =
        β lam l • (MvPolynomial.aeval
          (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι K)) p *
            MvPolynomial.X l) := by
      intro l
      rw [MvPolynomial.smul_eq_C_mul]
      ring
    rw [map_mul]
    simp only [MvPolynomial.aeval_X]
    rw [Finset.mul_sum]
    simp_rw [hterm]
    rw [DepthAdd.derivAt0_sum, derivAt0_mul_X,
      ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hA0, derivAt0_sumG]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [derivAt0_smulP, derivAt0_mul_X, hp, pderiv_sum_smul_X_eq_C, mul_comm _ (C (β lam l)), ← MvPowerSeries.smul_eq_C_mul,
      derivAt0_smulG]

end GlobalTheory.IsoTriv
end
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)
open scoped ComplexOrder

namespace GlobalTheory.ColumnFamilyMetric

open GlobalTheory.PeriodClassSum GlobalTheory.TestLat.Compare

theorem chF_gramV (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg)
    (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (j : ℕ) (b : (chF W sel mu I u j).β) :
    ((chF W sel mu I u j).mem b).gramV = GlobalTheory.TestLat.Compare.gramB X.K (W.lamTrue u j) := by
  ext i k
  have e : gramKd X.emb (1 : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) = fun _ => 1 := by
    funext τ
    rw [gramKd, Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]
  show pairK (W.lamTrue u j) (gramKd X.emb 1) (bVV _ _ i) (bVV _ _ k) = _
  rw [e]
  exact pairK_one_basis (W.lamTrue u j) i k

theorem famIpAt_nonneg : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (j : ℕ) (h : (chF W sel mu I u j).Ok) (v : InfinitePlace X.K) (φ : (chF W sel mu I u j).Forms), 0 ≤ (famIpAt (chF W sel mu I u j) h v φ φ).re := by
  intro X Pr R W sel Sg mu I u j h v φ
  refine (Complex.nonneg_iff.1 ?_).1
  unfold famIpAt
  refine Finset.sum_nonneg fun b _ => ?_
  have hG : ((((chF W sel mu I u j).mem b).gramV).map v.embedding).PosSemidef := by
    rw [chF_gramV]
    exact (gramB_posDef (W.lamTrue u j) v.embedding).posSemidef
  letI := (h b).fintypeCl
  exact (ipAt_eq _ (h b) v _ _).symm ▸ wForm_nonneg _ hG _

end GlobalTheory.ColumnFamilyMetric
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] (y : FrPt Xo c K) {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, IsTangent (ub σ k)) ∧ (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ ub σ k) ∧ ∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w := by
  first | exact @GlobalTheory.KSExist.exists_frame_of_isGrpPullback | exact GlobalTheory.KSExist.exists_frame_of_isGrpPullback | (intros; apply GlobalTheory.KSExist.exists_frame_of_isGrpPullback <;> assumption)
end

section

set_option autoImplicit false


noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

open FrameLift

theorem exists_frame_of_isGrpPullback_ring {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}
    (hπ : IsGrpPullback A Xo.univ.t.G y.x π)
    (a : OAct (𝓞 E) A) (ha : ∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) :
    ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧
      (∀ σ k, IsTangent (ub σ k)) ∧
      (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ ub σ k) ∧
      ∀ σ (w : epsR S ⟶ A), IsTangent w →
        (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ w) →
        ∃ cf, IsLieComb cf (ub σ) w := by
  choose ub hub using fun σ k => exists_lift hπ (T := epsR S) (y.u σ k) (y.tan σ k).1
  refine ⟨ub, hub, fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k), fun σ k z => ?_, fun σ w ht he => ?_⟩
  · refine (eig_iff hπ (ha z) _ _).1 ?_
    rw [hub]
    exact y.eig σ k z
  · have e : y.u σ = fun i => (ub σ i).left ≫ π := funext fun i => (hub σ i).symm
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [e] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩

end GlobalTheory.KSExist
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def NormPin {g : ℕ} {σ' : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (Pm : (F.Di k).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ)) : Prop :=
  ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
    (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
    Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di k).EF a b) ∧
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ j z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
    (∀ j j' z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex k Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
    (∀ j, ⊤ ≤ (F.ex k Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
    (∀ j z (pt : Sp ℂ ⟶ Gx y.x),
      pt ≫ Formalism.L2.PjFree.gxFst y.x = (F.ex k Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = θ z * fr j z) ∧
    MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
    (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
      (MeasureTheory.volume Fd).toReal = 1

def Pinned (U : Formalism.L2.PjFree.Unf Xo c σ r) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) : Prop :=
  (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E
      (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = Formalism.L2.PjFree.perFr (U.X k) x.1 (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2) ∧
      IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)

def MoveMatch (U U' : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (k' : U'.Comp) {δ : GL (Fin r) E}
    (h : GlobalTheory.LevelCusp.IsMatch (U.X k) (U'.X k') δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) : Prop :=
  ∀ (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)), FrMove ρ ν (U.un k x) y' →
    y'.x = (U'.un k' ⟨_, h.mem_dom x.2⟩).x ∧ y'.u = (U'.un k' ⟨_, h.mem_dom x.2⟩).u

theorem exists_frBor_gen (z y : FrPt Xo c (CAt σ)) (hx : y.x = z.x) (hu : y.u = z.u) :
    ∃ t₀ : (CAt σ)ˣ, FrBor (fun i => Option.elim i t₀ (fun _ => 1)) z y := by
  obtain ⟨gm, a, -, -, -, hbc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) z y).1 hx
  refine ⟨a, (GlobalTheory.Frames.frBor_iff_frChg _ _ _).2 ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne,
      fun τ i => Matrix.one_apply_eq i, hx, fun τ i => ?_, hbc⟩⟩
  rw [hu]
  exact (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c (CAt σ) z z z).1.2.1 τ i

theorem exists_pinned_of_isUnf {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) :
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), Pinned U e F ik φ ∧
      ∀ k (x : (U.X k).dom) (Pm : (F.Di (ik k)).La →+ (Fin g → ℂ)),
        (∀ a j, Pm a j = Formalism.L2.PjFree.perFr (U.X k) x.1 (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2) →
        GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → NormPin F (ik k) Pm (U.un k x) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, h1, h2⟩ := hU
  refine ⟨g, e, F, ik, φ, ⟨h1, fun k x => ?_⟩, fun k x Pm hPm hx => ?_⟩
  · obtain ⟨P, a, b, c, d, -⟩ := h2 k x
    exact ⟨P, a, b, c, d⟩
  · obtain ⟨P, a, -, -, -, d⟩ := h2 k x
    obtain rfl : Pm = P := AddMonoidHom.ext fun v => funext fun j => (hPm v j).trans (a v j).symm
    exact d hx

end GlobalTheory.GeoLevel
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.inv_integral_sq_discreteSeries_coefficient_compactDual : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (cd : CDHaar) {D : D7} (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (Fr : Frames W), IsFrames W Fr → (∀ ρ, (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) → ∀ ρ, StrictAnti (M.lam ρ) → (∀ a, ∃ z : ℤ, M.lam ρ a - ((W.rank : ℝ) - 1) / 2 = (z : ℝ)) → ∀ w : M.H ρ, ‖w‖ = 1 → Integrable (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) (cd.cd _ _) ∧ (∫ b : Upq W ρ, ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2 ∂(cd.cd _ _))⁻¹ = (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) / ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq | exact GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq | (intros; apply GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem discrep_isAt_eq_neg_mult : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ), 0 < m → IsDivOfForm K η → ∀ (E : DivOver q) (w : Y) (g : Y.functionFieldˣ), E.IsAt w → G.IsEqn w g → discrep E η m g = -((G - m • K).mult w : ℚ) / m := by
  intro k _ _ Y _ _ q n _ η hη K G m hm hK E w g hE hg
  obtain ⟨c, hc⟩ := K.exists_isEqn w
  have h1 := (hg.sub (hc.nsmul m)).mult_eq
  rw [← hE.ord_eq, div_eq_mul_inv, E.ord_mul, E.ord_inv, E.ord_pow] at h1
  have h2 := GlobalTheory.T.formOrd_eq_mult_of_isCartierDivisorOfRationalForm k Y q n η hη K hK E w hE
  rw [hc.mult_eq, ← hE.ord_eq] at h2
  change E.formOrd η = E.ord c at h2
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [discrep, h1, h2]
  push_cast
  field_simp
  ring

end GlobalTheory.Discrepancy
end
