module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle451
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle462
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle452
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalDictionarySplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle456
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.SplitMoveKappa

theorem om_toPair_mul : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R) (p : Pair T) (s x : FinPt ch.G p.small) (s' y : FinPt ch.G p.big) (v : WO (ch.G.pS p) (ch.G.pT p) → ℂ),
    ch.W.om p (ch.G.toPair p ((s * x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((s' * y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) v =
      ch.W.om p (ch.G.toPair p (s : Formalism.L2.Theta.GA D (ch.G.V p.small)) (s' : Formalism.L2.Theta.GA D (ch.G.V p.big)))
        (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) v) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch p s x s' y v
  have e1 : ((s * x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) =
      (s : Formalism.L2.Theta.GA D (ch.G.V p.small)) * ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) := by
    rw [mul_assoc]; rfl
  have e2 : ((s' * y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) =
      (s' : Formalism.L2.Theta.GA D (ch.G.V p.big)) * ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) := by
    rw [mul_assoc]; rfl
  have e3 : ∀ (a b : Formalism.L2.Theta.GA D (ch.G.V p.small)) (c d : Formalism.L2.Theta.GA D (ch.G.V p.big)),
      ch.G.toPair p (a * b) (c * d) = ch.G.toPair p a c * ch.G.toPair p b d := by
    intro a b c d
    cases p <;> simp [GlobalTheory.ChiGrid.GridData.toPair, map_mul]
  rw [e1, e2, e3, map_mul]
  rfl

end GlobalTheory.SplitMoveKappa
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.EndCusp

open Formalism.IndefR.Mult Matrix

variable {D : D7}

theorem isTypeAt_of_finSum (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) {S : SPar}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)} {lam : Fin V.rank → ℝ} {ε : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hE : IsEnum S lam ε) (hD : Formalism.MainNotions.S.IsDS ε lam σ) (hP : IsUnit P) (hJ : Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ)
    (φ : GA D V → ℂ)
    (h : ∀ x, ∃ (n : ℕ) (L : Fin n → (H →L[ℂ] ℂ)) (v : Fin n → H),
      (∀ i, SmoothVec (lieAt V τ) (fun g => σ (P * g * P⁻¹)) (v i)) ∧
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), φ (x * atTau θ V τ g) = ∑ i, L i (σ (P * g * P⁻¹) (v i))) :
    IsTypeAt θ V τ S φ := by
  refine ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, fun x => ?_⟩
  obtain ⟨n, L, v, hv, hφ⟩ := h x
  let vv : ℕ → H := fun i => if hi : i < n then v ⟨i, hi⟩ else 0
  let ll : ℕ → (H →ₗ[ℂ] ℂ) := fun i => if hi : i < n then ((L ⟨i, hi⟩ : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ) else 0
  let CC : ℕ → ℝ := fun i => if hi : i < n then ‖L ⟨i, hi⟩‖ else 0
  have hb : ∀ i w, ‖ll i w‖ ≤ CC i * ‖w‖ := fun i w => by
    by_cases hi : i < n
    · simp only [ll, CC, dif_pos hi]
      exact (L ⟨i, hi⟩).le_opNorm w
    · simp [ll, CC, dif_neg hi]
  refine ⟨vv, fun i => ?_, ll, fun i => ⟨[[]], CC i, by simp, fun w _ => by simpa using hb i w⟩,
    ⟨[[]], CC, by simp, fun i w _ => by simpa using hb i w, fun S' _ => ?_, fun _ => 1, continuous_const,
      fun g hg w _ => ?_⟩, fun g hg => ?_⟩
  · by_cases hi : i < n
    · simp only [vv, dif_pos hi]
      exact hv _
    · simp only [vv, dif_neg hi]
      intro k Xs _
      simpa using contDiff_const
  · refine summable_of_ne_finset_zero (s := Finset.range n) fun i hi => ?_
    have : ¬ i < n := by simpa using hi
    simp [CC, dif_neg this]
  · simp [hD.2.2.1.2.1 _ (GlobalTheory.TypeAtCompare.conj_mem hP hJ hg) w]
  · rw [hφ g hg]
    convert hasSum_sum_of_ne_finset_zero (s := Finset.range n)
      (f := fun i => ll i (σ (P * g * P⁻¹) (vv i))) (fun i hi => by
        have : ¬ i < n := by simpa using hi
        simp [ll, dif_neg this]) using 1
    · rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [ll, vv, i.2]
    · infer_instance

def conjFun {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] (c : H' ≃ₗᵢ⋆[ℂ] H) (ℓ : H →L[ℂ] ℂ) : H' →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun w => star (ℓ (c w))
      map_add' := fun a b => by simp
      map_smul' := fun a w => by
        simp only [LinearIsometryEquiv.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply]
        rw [star_mul', Complex.star_def, Complex.conj_conj] }
    ‖ℓ‖ (fun w => by simpa using ℓ.le_opNorm (c w))

theorem conjFun_apply {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] (c : H' ≃ₗᵢ⋆[ℂ] H) (ℓ : H →L[ℂ] ℂ) (w : H') : conjFun c ℓ w = star (ℓ (c w)) := rfl

end GlobalTheory.EndCusp

namespace GlobalTheory.EndCusp

open Formalism.IndefR.Mult Matrix

variable {D : D7}

theorem conj_finSum {V : HSp D} {S S' : D.what₂.Tau → SPar} {θ : InfFam D} (M : DSModel V S) (M' : DSModel V S')
    (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)] (c : M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c (M'.rep τ g w) = M.rep τ g (c w))
    (hsm : ∀ w : M'.H τ, w ∈ M'.sm τ ↔ c w ∈ M.sm τ)
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (x : GA D V) (z : SmT M) :
    ∃ (n : ℕ) (L : Fin n → (M'.H τ →L[ℂ] ℂ)) (v : Fin n → M'.H τ),
      (∀ i, SmoothVec (lieAt V τ) (fun g => M'.σ τ (M'.fr τ * g * (M'.fr τ)⁻¹)) (v i)) ∧
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), star (PiTensorProduct.lift T z (x * atTau θ V τ g)) =
        ∑ i, L i (M'.σ τ (M'.fr τ * g * (M'.fr τ)⁻¹) (v i)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    obtain ⟨ℓ, -, hℓ⟩ := GlobalTheory.DefiniteEnd.exists_sobCont M τ T f x
    have hw : c.symm (f τ) ∈ M'.sm τ := (hsm _).2 (by simp)
    have hsv : SmoothVec (lieAt V τ) (fun g => M'.σ τ (M'.fr τ * g * (M'.fr τ)⁻¹)) (c.symm (f τ)) := by
      rw [GlobalTheory.SmVec.sm_eq M' τ] at hw
      exact hw
    refine ⟨1, fun _ => star r • conjFun c (LinearMap.toContinuousLinearMap ℓ), fun _ => c.symm (f τ), fun _ => hsv,
      fun g hg => ?_⟩
    have e1 := congrFun (hT.equiv τ g hg f ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩ rfl) x
    have e3 : T f (x * atTau θ V τ g) = ℓ (M.rep τ g (f τ)) := by
      rw [hℓ ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩]
      exact e1.symm
    have e2 : M.rep τ g (f τ) = c (M'.rep τ g (c.symm (f τ))) := by
      rw [hc g hg, LinearIsometryEquiv.apply_symm_apply]
    rw [Fin.sum_univ_one, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, ContinuousLinearMap.smul_apply, conjFun_apply,
      smul_eq_mul, smul_eq_mul, star_mul', e3, LinearMap.coe_toContinuousLinearMap', e2]
    rfl
  | add a b ha hb =>
    obtain ⟨n₁, L₁, v₁, hv₁, h₁⟩ := ha
    obtain ⟨n₂, L₂, v₂, hv₂, h₂⟩ := hb
    refine ⟨n₁ + n₂, Fin.append L₁ L₂, Fin.append v₁ v₂, fun i => ?_, fun g hg => ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hv₁ i
      · simpa using hv₂ i
    · rw [Fin.sum_univ_add, map_add (f := _), Pi.add_apply, star_add, h₁ g hg, h₂ g hg]
      simp

end GlobalTheory.EndCusp

namespace GlobalTheory.EndCusp

open Formalism.IndefR.Mult Matrix

variable {D : D7}

theorem isAutFunSm_lift {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (z : SmT M) :
    IsAutFunSm θ V (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact GlobalTheory.Mem.AutSpace.isAutFunSm_smul r (hT.aut f)
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact GlobalTheory.Mem.AutSpace.isAutFunSm_add ha hb

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem formX_props (R : RealDat D A Ks) (hθ : R.models_inf) (hc : R.models_cX) (hpr : R.models_prX) (hH : R.models_HX)
    (d : ChainVec R) (t : T) (y : (R.HX t).H) :
    IsAutFunSm R.θ D.sp.X' (d.formX t y) ∧ IsCuspFun D.sp.X' (d.formX t y) ∧
      ∀ τ, IsTypeAt R.θ D.sp.X' τ ((Ptw D).Dpar D.R.m τ) fun g => star (d.formX t y g) := by
  have hx := (hH t).2.1.le (LinearMap.mem_range_self (R.HX t).e y)
  have hT := GlobalTheory.DefiniteEnd.isMultMap_toMap hθ D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX hc hpr hx
  have e : d.formX t y =
      PiTensorProduct.lift (PiTensorProduct.lift.symm (R.cX.toMap R.prX ((R.HX t).e y))) d.v := by
    rw [LinearEquiv.apply_symm_apply]; rfl
  rw [e]
  refine ⟨isAutFunSm_lift hT _, GlobalTheory.DefiniteEnd.isCuspFun_of_definite D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) _,
    fun τ => ?_⟩
  haveI := GlobalTheory.DefiniteEnd.finiteDimensional_model D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX τ
  obtain ⟨M', c, hc'⟩ := @GlobalTheory.ConjDS.exists_conjModel D D.sp.X' (parB (Ptw D) D.R.m) R.MX
  have hsm := (GlobalTheory.ConjMult.conj_mult R.θ R.MX M' c hc').1 τ
  have hE := M'.enum τ
  simp only [parB, dualPar_dualPar] at hE
  exact isTypeAt_of_finSum R.θ D.sp.X' τ hE (M'.ds τ) (M'.fr_unit τ) (M'.fr_gram τ) _
    fun x => conj_finSum R.MX M' τ (c τ) (hc' τ) hsm hT x d.v

theorem props_cast (θ : InfFam D) (S : D.what₂.Tau → SPar) {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)}
    (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩) (φ : GA D D.sp.X' → ℂ) (h1 : IsAutFunSm θ D.sp.X' φ) (h2 : IsCuspFun D.sp.X' φ)
    (h3 : ∀ τ, IsTypeAt θ D.sp.X' τ (S τ) fun g => star (φ g)) :
    IsAutFunSm θ X.sp (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) ∧
      IsCuspFun X.sp (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) ∧
      ∀ τ, IsTypeAt θ X.sp τ (S τ) fun g => star (φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) := by
  subst h
  exact ⟨h1, h2, h3⟩

end GlobalTheory.EndCusp

namespace GlobalTheory.EndCusp

end GlobalTheory.EndCusp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_rationalPoint_thetaGenerator_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {s : LB.Sec (PPx x₁)}, IsThGen x₁ s → ∃ w : Sp Ω ⟶ Gx x₁, w ≫ (fst (Over.mk x₁) Xo.univ.t.G).left = 𝟙 _ ∧ ∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s w z J ≠ 0 := by
  first | exact @GlobalTheory.ThetaNZ.exists_ratPt_sv_ne_zero | exact GlobalTheory.ThetaNZ.exists_ratPt_sv_ne_zero | (intros; apply GlobalTheory.ThetaNZ.exists_ratPt_sv_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_isRigIso_of_isGen : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : RigLB A) (Y : Scheme.{0})
    (x x' : Y ⟶ S) (Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left) (k : ℤ)
    (β : LB.Gen (isoLB A L Ψ k)), IsPointed A Ψ → β.IsGen → ∃ β', IsRigIso A L Ψ k β' := by
  intro S A _ L Y x x' Ψ k β hΨ hβ
  exact GlobalTheory.RigIsoDescent.exists_isRigIso_of_gen hΨ β hβ

end GlobalTheory.HeckeEx
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.largeScaleSizes_imply_gapConditions : SizeGap := by
  first | exact @GlobalTheory.SepRows.sizeGap_of_sizes | exact GlobalTheory.SepRows.sizeGap_of_sizes | (intros; apply GlobalTheory.SepRows.sizeGap_of_sizes <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_column_perfectPairing_definiteCoreNode : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D), IsInfFam θ → ∀ {S : D.what₂.Tau → SPar} (M : DSModel (G.V (.core D.R.m)) S), (∀ τ a, M.ε τ a = true) → (coefPlus G θ).Is → ∀ (pr : (coefPlus G θ).W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), IsDualPair θ M (coefPlus G θ) pr → ∀ y ∈ CoreForms G θ D.R.m M, ∃ c ∈ Cols G θ, (coefPlus G θ).toMap pr c = y := by
  first | exact @GlobalTheory.TopColumn.exists_col | exact GlobalTheory.TopColumn.exists_col | (intros; apply GlobalTheory.TopColumn.exists_col <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.gridConjugation_weilData_inverseCharacter : ConjRead := by
  first | exact @GlobalTheory.Asc.conjRead_holds | exact GlobalTheory.Asc.conjRead_holds | (intros; apply GlobalTheory.Asc.conjRead_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.branchingHypotheses_gridParameters_largeScale : Ev fun {D} _ _ {sc} _ _ _ => ∀ (τ : D.what₂.Tau) (ε : Fin (D.R.r + 1) → Bool) (lam : Fin (D.R.r + 1) → ℝ) (ε' : Fin D.R.r → Bool) (mu : Fin D.R.r → ℝ), IsEnum (Node.par D sc.cGap (.core 0) τ) lam ε → IsEnum (dualPar (parB (Ptw D) 0 τ)) mu ε' → (∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu (sc.b ^ 2)) ∧ Real.log (8 * ((D.R.r : ℝ) + 1) * sc.b ^ 2) ≤ 6 * Real.log sc.b ∧ 0 ≤ Real.log sc.b := by
  first | exact @GlobalTheory.SepPer.realInputPar | exact GlobalTheory.SepPer.realInputPar | (intros; apply GlobalTheory.SepPer.realInputPar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.besselGroup_acts_basePoint_unitriangular : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), (∀ g : GA D B.V, g ∈ besGrp B.d B.o ↔ ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1) ∧ (∀ a a' : Mx D (σ + 1) (σ + 1), xLast B.d (vecB B.o B.ζ) ⬝ a = xLast B.d (vecB B.o B.ζ) ⬝ a' → a = a') ∧ ∀ g ∈ GQ B.V, ∀ u : UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1.1 → u ∈ UXQ D (σ + 1) := by
  first | exact @GlobalTheory.Asc.FBL.besGrp_act_xLast | exact GlobalTheory.Asc.FBL.besGrp_act_xLast | (intros; apply GlobalTheory.Asc.FBL.besGrp_act_xLast <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.linked_line_hom_transport_lattice_vacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ x, ‖ψ x‖ = 1) → ∀ (L S : HSp D) (ζ ζ' : Fin L.rank → D.host.E), IsLineVec L ζ' → ∀ (l : Lnk L ζ L ζ') (Λ : AddSubgroup (WO S L)) (Ξ : WO L S → ℂ), IsLatVac (heisO ψ S L) Λ (fun w => star (Ξ (l.κ S w))) → ∀ w ∈ Λ, heisO ψ L S (2 • l.κ S w) Ξ = Ξ ∧ ∀ e, IsSplitIdem D e → IsHalf e (l.κ S w) → heisO ψ L S (l.κ S w) Ξ = Ξ := by
  first | exact @GlobalTheory.KapVac.kappa_vac | exact GlobalTheory.KapVac.kappa_vac | (intros; apply GlobalTheory.KapVac.kappa_vac <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_local_dictionary_splitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  first | exact @GlobalTheory.SplitDict.exists_split_dictionary | exact GlobalTheory.SplitDict.exists_split_dictionary | (intros; apply GlobalTheory.SplitDict.exists_split_dictionary <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.adelicSchwartzSpace_le_span_pureTensors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ W v, ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v, s * n * s⁻¹ = n * n := by
  first | exact @GlobalTheory.SplitConj.conj_to_sq | exact GlobalTheory.SplitConj.conj_to_sq | (intros; apply GlobalTheory.SplitConj.conj_to_sq <;> assumption)
end
