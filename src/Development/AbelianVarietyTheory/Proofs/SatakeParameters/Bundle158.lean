module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle155
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBases
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle011
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLevelOfNormHolds
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.UnitaryInverseIdentity
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module

noncomputable section

namespace GlobalTheory.PstRank

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

def sigSt (g : ↥(GK K)) : Bst P ⊗[ℚ_[l]] V →ₗ[ℚ_[l]] Bst P ⊗[ℚ_[l]] V :=
  TensorProduct.map (actSt P (g : GQ l)).toLinearMap ((ρ g).restrictScalars ℚ_[l])

theorem sigSt_smul (g : ↥(GK K)) (b : Bst P) (w : Bst P ⊗[ℚ_[l]] V) :
    sigSt P ρ g (b • w) = actSt P (g : GQ l) b • sigSt P ρ g w := by
  induction w using TensorProduct.inductionOn with
  | tmul c v => simp [sigSt, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem sigSt_comm (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Bst P) :
    sigSt P ρ g (TensorProduct.comm ℚ_[l] V (Bst P) y) =
      TensorProduct.comm ℚ_[l] V (Bst P) (stRep P ρ g y) := by
  induction y using TensorProduct.inductionOn with
  | tmul v b => simp [sigSt]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem comm_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : V ⊗[ℚ_[l]] Bst P) :
    TensorProduct.comm ℚ_[l] V (Bst P) (mulV P LL V c y) = c • TensorProduct.comm ℚ_[l] V (Bst P) y := by
  induction y using TensorProduct.inductionOn with
  | tmul v b => simp [TensorProduct.smul_tmul', Algebra.smul_def]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]

def toB : DpstUr P ρ →ₗ[↥(MaximalUnramifiedExtension l)] Bst P ⊗[ℚ_[l]] V where
  toFun x := TensorProduct.comm ℚ_[l] V (Bst P) (((toUr P ρ).symm x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P)
  map_add' x y := by simp
  map_smul' c x := comm_mulV P c _

theorem toB_injective : Function.Injective (toB P ρ) := fun x y h =>
  (toUr P ρ).symm.injective (Subtype.ext ((TensorProduct.comm ℚ_[l] V (Bst P)).injective h))

end GlobalTheory.PstRank

namespace GlobalTheory.PstRank

theorem rank_DpstUr_le : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l), IsDomain (Bst P) → (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 → (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) → ∀ {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V] (ρ : Representation LL ↥(GK K) V), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ finrank ℚ_[l] V := by
  intro l _ P hdom hreg K LL _ _ V _ _ _ _ _ ρ
  refine rank_le fun s hs => ?_
  choose F hF using fun i : ↥s => (mem_Dpst P ρ).mp ((toUr P ρ).symm (i : DpstUr P ρ)).2
  have hFd := fun i : ↥s => (F i).2
  let K' : FinExt l := supExt K ⟨⨆ i, (F i).1, inferInstance⟩
  have hKK' : K.1 ≤ K'.1 := le_sup_left
  have hFK' : ∀ i, (F i).1 ≤ K'.1 := fun i => (le_iSup (fun i => (F i).1) i).trans le_sup_right
  let v : ↥s → Bst P ⊗[ℚ_[l]] V := fun i => toB P ρ (i : DpstUr P ρ)
  have hv : ∀ (g : ↥(GK K')) i, sigSt P ρ ⟨g, GK_le hKK' g.2⟩ (v i) = v i := by
    intro g i
    change sigSt P ρ _ (TensorProduct.comm ℚ_[l] V (Bst P) _) = _
    rw [sigSt_comm, hF i ⟨g, GK_le hKK' g.2⟩ (GK_le (hFK' i) g.2)]
    rfl
  have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) v := hs.map' (toB P ρ) (LinearMap.ker_eq_bot.mpr (toB_injective P ρ))
  have hB : LinearIndepOn (Bst P) v ((Finset.univ : Finset ↥s) : Set ↥s) :=
    GlobalTheory.RegularRing.linearIndepOn_of_invariant (K := ↥(MaximalUnramifiedExtension l)) (B := Bst P) (G := ↥(GK K'))
      (fun g b => actSt P (g : GQ l) b)
      (fun g => (sigSt P ρ ⟨g, GK_le hKK' g.2⟩).toAddMonoidHom)
      (fun g b w => sigSt_smul P ρ _ b w)
      (fun b b' hb h => by
        obtain ⟨c, -, hc⟩ := hreg K' b b' hb h
        exact ⟨c, hc⟩)
      v hv Finset.univ (hli.linearIndepOn _)
  have hB' : LinearIndependent (Bst P) v := by
    rw [← linearIndepOn_univ_iff]; rw [Finset.coe_univ] at hB; exact hB
  simpa using LinearIndependent.fintype_card_le_finrank hB'

end GlobalTheory.PstRank
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLine

theorem isUnit_of_stable_line : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l),
  (∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB) → GlobalTheory.RegularRing.LineUnit (P.PD K) →
  ∀ b : Bst P, b ≠ 0 → (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) b = algebraMap ℚ_[l] (Bst P) x * b) → IsUnit b := by
  intro l _ P _ K hno hLU b hb hst
  unfold GlobalTheory.RegularRing.LineUnit at hLU
  haveI : CharZero P.R.B := charZero_of_injective_algebraMap (algebraMap ℚ_[l] P.R.B).injective

  have hact : ∀ (g : GQ l) (p : Bst P),
      actSt P g p = stHom P (P.actQ g) (X + C ((kummer P g : ℚ_[l]) • P.tB)) p := fun g p => rfl

  have hder : ∀ (g : GQ l) (p : Bst P), derivative (actSt P g p) = actSt P g (derivative p) := by
    intro g p
    rw [hact, hact, derivative_stHom]
    simp
  have hiter : ∀ (k : ℕ) (g : GQ l) (p : Bst P),
      actSt P g (derivative^[k] p) = derivative^[k] (actSt P g p) := by
    intro k g
    induction k with
    | zero => intro p; rfl
    | succ k ih =>
      intro p
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hder]

  have heig : ∀ (k : ℕ) (g : ↥(GK K)), ∃ x : ℚ_[l],
      actSt P (g : GQ l) (derivative^[k] b) = algebraMap ℚ_[l] (Bst P) x * derivative^[k] b := by
    intro k g
    obtain ⟨x, hx⟩ := hst g
    refine ⟨x, ?_⟩
    rw [hiter, hx, Polynomial.algebraMap_apply, iterate_derivative_C_mul]

  have hlin : ∀ p : Bst P, p.natDegree ≤ 1 → p.coeff 1 ≠ 0 →
      (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) p = algebraMap ℚ_[l] (Bst P) x * p) → False := by
    intro p hp1 hp0 hpe
    obtain ⟨u, v, rfl⟩ : ∃ u v, p = C u * X + C v := ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_natDegree_le_one hp1⟩
    have hu0 : u ≠ 0 := by simpa using hp0
    have hco : ∀ (g : GQ l), g ∈ GK K → ∃ x : ℚ_[l],
        P.actQ g u = algebraMap ℚ_[l] P.R.B x * u ∧
        P.actQ g u * ((kummer P g : ℚ_[l]) • P.tB) + P.actQ g v = algebraMap ℚ_[l] P.R.B x * v := by
      intro g hg
      obtain ⟨x, hx⟩ := hpe ⟨g, hg⟩
      refine ⟨x, ?_, ?_⟩
      · have h1 := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 1) hx
        simpa [Polynomial.algebraMap_apply, mul_add] using h1
      · have h0 := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 0) hx
        simpa [Polynomial.algebraMap_apply, mul_add] using h0
    have hU : IsUnit u := hLU u hu0 (fun g => by
      obtain ⟨x, h1, -⟩ := hco (g : GQ l) g.2
      exact ⟨x, by rw [P.PD_actB]; exact h1⟩)
    obtain ⟨w, hw⟩ : ∃ w, w = v * ↑hU.unit⁻¹ := ⟨_, rfl⟩
    have hwu : w * u = v := by rw [hw, mul_assoc, IsUnit.val_inv_mul, mul_one]
    refine hno (-w) (fun g hg => ?_)
    obtain ⟨x, h1, h0⟩ := hco g hg
    have hne : P.actQ g u ≠ 0 := (hU.map (P.actQ g)).ne_zero
    have key : P.actQ g w * P.actQ g u = (w - (kummer P g : ℚ_[l]) • P.tB) * P.actQ g u := by
      rw [← map_mul, hwu]
      linear_combination h0 - w * h1 - (algebraMap ℚ_[l] P.R.B x) * hwu
    have hgw : P.actQ g w = w - (kummer P g : ℚ_[l]) • P.tB := mul_right_cancel₀ hne key
    rw [map_neg, hgw]
    ring
  by_cases hn : b.natDegree = 0
  · obtain ⟨c, rfl⟩ : ∃ c, b = C c := ⟨_, eq_C_of_natDegree_eq_zero hn⟩
    apply IsUnit.map C
    refine hLU c (fun h => hb (by rw [h, C_0])) (fun g => ?_)
    obtain ⟨x, hx⟩ := hst g
    refine ⟨x, ?_⟩
    rw [P.PD_actB]
    rw [actSt_C, Polynomial.algebraMap_apply, ← C_mul] at hx
    exact C_injective hx
  · exfalso
    apply hlin (derivative^[b.natDegree - 1] b)
    · have := natDegree_iterate_derivative b (b.natDegree - 1)
      omega
    · rw [coeff_iterate_derivative, show 1 + (b.natDegree - 1) = b.natDegree by omega]
      refine smul_ne_zero ?_ (leadingCoeff_ne_zero.mpr hb)
      intro h
      rw [Nat.descFactorial_eq_zero_iff_lt] at h
      omega
    · exact heig (b.natDegree - 1)

end GlobalTheory.Pst.StLine
end

section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.translate_mem_twistedJacquetKernel_ramified : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (u : (w.adicCompletion E)ˣ), 1 ≤ a → Valued.v (u : w.adicCompletion E) = 1 → χ u ≠ 1 → ∀ y : V, (∀ k ∈ GlobalTheory.LFun.KGL w (n := a), ρ k y = (((χ (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y) → ∀ g, ρ g y ∈ GlobalTheory.PRep.twKer ρ (GlobalTheory.LFun.KGL w (n := a)) 1 := by
  first | exact @GlobalTheory.CartanCoinv.translate_mem_twKer | exact GlobalTheory.CartanCoinv.translate_mem_twKer | (intros; apply GlobalTheory.CartanCoinv.translate_mem_twKer <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

theorem _root_.GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E), L.FG → (∀ τ, GL3Columns.BasR D lam τ L ((P τ).map (tauEmb D lam τ))) → (∀ τ τ', Formalism.L2.Ker.ConjPr lam τ τ' → P τ' = Formalism.L2.Ker.dualM (P τ)) → StdBases D lam L P := by
  first | exact @GlobalTheory.KerStd.stdBases_of_basR | exact GlobalTheory.KerStd.stdBases_of_basR | (intros; apply GlobalTheory.KerStd.stdBases_of_basR <;> assumption)
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem flin_pad {K : Type} [Field K] {σ n m : Type} [Fintype n] [Fintype m] {l linv : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) (c : n ⊕ m → K) (u : m → MvPowerSeries σ K) :
    Formalism.L2.Th1.C.flin l linv c (Sum.elim (fun _ => (0 : MvPowerSeries σ K)) u) =
      Formalism.L2.Th1.C.flin l linv (fun j => c (Sum.inr j)) u := by
  unfold Formalism.L2.Th1.C.flin
  congr 1
  rw [Fintype.sum_sum_type]
  simp [hl]


open Formalism.L2.Th1.C in
theorem unitaryInv_rect {K : Type} [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K)
    (hFr : Frame R l linv ph) (O : Type) [CommRing O] [StarRing O] (τ : O →+* K)
    (hE : ∀ α, EndInt R l linv (τ α)) (hB : ∀ z : O, star z = z → IsBinomScalar R (τ z))
    (hF1 : Formalism.L2.Th1.C.F1 R l linv ph)
    (hN : ∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α)))
    (hA : ∀ α : O, AdjAt R l linv ph (τ α) (τ (star α)))
    {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (γ : Matrix n m O)
    (hγ : γ.conjTranspose * γ = 1) {σ : Type} (u : m → MvPowerSeries σ K) (hu : ∀ j, IsPt R (u j)) :
    Cong R (∑ i, PowerSeries.subst (flin l linv (fun j => τ (γ i j)) u) ph) (∑ j, PowerSeries.subst (u j) ph) := by
  set P : Matrix n n O := 1 - γ * γ.conjTranspose with hP
  have hPh : P.conjTranspose = P := by
    rw [hP, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hPγ : P * γ = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hγ, Matrix.mul_one, sub_self]
  have hγP : γ.conjTranspose * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hγ, Matrix.one_mul, sub_self]
  have hPP : P * P = P := by
    conv_lhs => rw [show P * P = P * (1 - γ * γ.conjTranspose) from rfl]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPγ, Matrix.zero_mul, sub_zero]
  have hΔ : (Matrix.fromBlocks P γ γ.conjTranspose 0).conjTranspose * Matrix.fromBlocks P γ γ.conjTranspose 0 = 1 := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_conjTranspose, hPh, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, hPP, hPγ, hγP, hγ, ← Matrix.fromBlocks_one]
    congr 1
    · rw [hP]; abel
    · simp
    · simp
    · simp
  have hu' : ∀ c : n ⊕ m, IsPt R (Sum.elim (fun _ : n => (0 : MvPowerSeries σ K)) u c) := by
    rintro (c | c)
    · exact ⟨by simp, fun k => by simp⟩
    · exact hu c
  have key := unitaryInv K R l linv ph hFr O τ hE hB hF1 hN hA (n ⊕ m)
    (Matrix.fromBlocks P γ γ.conjTranspose 0) hΔ σ (Sum.elim (fun _ : n => 0) u) hu'
  have hph : PowerSeries.constantCoeff ph = 0 := hFr.2.2
  have hl : PowerSeries.constantCoeff l = 0 := hFr.1.1
  have hli : PowerSeries.constantCoeff linv = 0 := hFr.1.2.2.1
  simp only [Fintype.sum_sum_type, flin_pad hl, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂,
    Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, map_zero] at key
  have h0 : PowerSeries.subst (flin l linv (fun _ : m => (0 : K)) u) ph = 0 := by
    unfold flin
    simp [hli, hph]
  simpa [hph, h0] using key

theorem HostLog.subst_unitary : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (n m : Type) [Fintype n] [Fintype m] [DecidableEq m] (γ : n → m → MaximalUnramifiedExtension p), (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) → (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) → ∀ Θ : MvPowerSeries n ℂ_[p], HostLog p g2 g3 s2 ε Θ → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) := by
  intro p _ g2 g3 s2 ε σ F hD n m _ _ _ γ hγ hγo Θ hΘ
  classical
  obtain ⟨h5, hg2, hg3, hε, hθ, hU, hF, hN⟩ := hD
  obtain ⟨hFr, hF1, hall, hbin⟩ := Formalism.L2.Th1.Top.CalcC_proof p h5 g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN
  have hσ : ∀ a : MaximalUnramifiedExtension p, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (Formalism.L2.Th1.D.frobSq (MaximalUnramifiedExtension p) p σ hU).2
  let _ : StarRing (Formalism.L2.Th1.D.BrC.Osub σ) := Formalism.L2.Th1.D.BrC.starO hσ
  let τ : Formalism.L2.Th1.D.BrC.Osub σ →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype.comp (Formalism.L2.Th1.D.BrC.Osub σ).subtype
  let γO : Matrix n m (Formalism.L2.Th1.D.BrC.Osub σ) :=
    Matrix.of fun i j => ⟨γ i j, Formalism.L2.Th1.D.BrC.mem_Osub.2 (hγ i j)⟩
  have hun : γO.conjTranspose * γO = 1 := by
    ext a b
    rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum, Matrix.one_apply]
    have h := hγo a b
    have e : ((if a = b then (1 : Formalism.L2.Th1.D.BrC.Osub σ) else 0 : Formalism.L2.Th1.D.BrC.Osub σ) : MaximalUnramifiedExtension p) =
        if a = b then 1 else 0 := by split_ifs <;> rfl
    rw [e, ← h]
    rfl
  set l := Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p with hl_def
  set linv := Formalism.L2.Th1.D.expF ℂ_[p] p with hlinv_def
  set ph := PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε) with hph_def
  let t : n → MvPowerSeries m ℂ_[p] := fun i =>
    Formalism.L2.Th1.C.flin l linv (fun j => τ (γO i j)) MvPowerSeries.X
  have hpt : ∀ i, Formalism.L2.Th1.C.IsPt (Formalism.G.unitBall ℂ_[p]) (t i) := fun i =>
    Formalism.L2.Th1.C.Pts.isPt_flin hFr.1 hFr.2.1 (fun j => (hall _ (hγ i j).1 (hγ i j).2).1)
      (fun j => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X j)
  have hcc : ∀ i, MvPowerSeries.constantCoeff (t i) = 0 := fun i => (hpt i).1
  have hcong := unitaryInv_rect (Formalism.G.unitBall ℂ_[p]) l linv ph hFr (Formalism.L2.Th1.D.BrC.Osub σ) τ
    (fun α => (hall α.1 α.2.1 α.2.2).1) (fun z hz => hbin z.1 z.2.1 (congrArg Subtype.val hz)) hF1
    (fun α => (hall α.1 α.2.1 α.2.2).2.1) (fun α => (hall α.1 α.2.1 α.2.2).2.2) γO hun
    (MvPowerSeries.X) (fun j => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X j)
  have hph0 : PowerSeries.constantCoeff ph = 0 := hFr.2.2
  have hPh0 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) = 0 :=
    Formalism.L2.Th1.E.CompatibleChartOperations.cc_phSum hph0
  have hb0 : ∀ (k : Type) (i : k), MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries k ℂ_[p]) = 0 :=
    fun k i => Formalism.L2.Th1.C.Pts.constantCoeff_subst_l hFr.1 (MvPowerSeries.constantCoeff_X i)
  set Θt : MvPowerSeries n ℂ_[p] := MvPowerSeries.subst (fun i : n => (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries n ℂ_[p])) Θ with hΘt
  have hΘ' : Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) * Θt) := hΘ
  have hΘe : Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p])) *
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) * Θt) = Θt := by
    rw [← mul_assoc]
    have := Formalism.L2.Th1.C.mvExp_neg hPh0
    rw [← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, ← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq] at this
    rw [this, one_mul]
  obtain ⟨h3, h4, h5'⟩ := Formalism.L2.Th1.E.substExpInt ℂ_[p] n m t hcc (fun i k => (hpt i).2 k)
    (Formalism.L2.Th1.E.phSum ph) _ hPh0 hΘ'
  rw [hΘe, Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum _ hcc] at h3
  rw [Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum _ hcc] at h5'
  have hid : MvPowerSeries.subst (fun j : m => (Formalism.InvariantFactorPaths.G7.at1 j l : MvPowerSeries m ℂ_[p]))
      (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) =
      MvPowerSeries.subst t Θt := by
    have hb : MvPowerSeries.HasSubst (fun j : m => (Formalism.InvariantFactorPaths.G7.at1 j l : MvPowerSeries m ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (hb0 m)
    have hb' : MvPowerSeries.HasSubst (fun i : n => (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries n ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (hb0 n)
    have hlin : MvPowerSeries.HasSubst
        (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp
    have ht : MvPowerSeries.HasSubst t := MvPowerSeries.hasSubst_of_constantCoeff_zero hcc
    rw [MvPowerSeries.subst_comp_subst_apply hlin hb, hΘt, MvPowerSeries.subst_comp_subst_apply hb' ht]
    congr 1
    funext i
    rw [Formalism.InvariantFactorPaths.G7.at1, Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X i) hcc,
      MvPowerSeries.subst_X ht]
    simp only [t, Formalism.L2.Th1.C.flin]

    rw [Formalism.L2.Th1.C.Pts.subst_l_linv hFr.1 (by
    rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by
      rw [map_mul, show PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries m ℂ_[p]) l = Formalism.InvariantFactorPaths.G7.at1 j l from rfl,
        hb0, mul_zero])]

    rw [← MvPowerSeries.coe_substAlgHom hb, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_X hb]
    rw [MvPowerSeries.subst_C]
    rfl
  unfold HostLog
  rw [hid, h3, ← mul_assoc]
  refine Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' ?_ h4
  obtain ⟨hc0, hcI⟩ := Formalism.L2.Th1.C.Calc.cong_symm hcong
  have hA0 : MvPowerSeries.constantCoeff (∑ i : m, Formalism.InvariantFactorPaths.G7.at1 i ph : MvPowerSeries m ℂ_[p]) = 0 :=
    Formalism.L2.Th1.E.CompatibleChartOperations.cc_phSum hph0
  have hB0 : MvPowerSeries.constantCoeff (-(∑ i, PowerSeries.subst (t i) ph) : MvPowerSeries m ℂ_[p]) = 0 := by
    rw [map_neg, h5', neg_zero]
  rw [Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, ← Formalism.L2.Th1.C.mvExp_add hA0 hB0,
    ← sub_eq_add_neg]
  exact fun k => hcI k

end GlobalTheory.KerStd
end
end

section

noncomputable section

namespace GlobalTheory.TwV

open NumberField
open scoped Matrix

theorem mem_locSp_of_natCast_smul_mem {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N' : ℕ} (L' : Submodule (𝓞 E) (Fin N' → E)) (z : Fin N' → E) (s : ℕ) (hs : IsUnit (s : W))
    (hz : (s : E) • z ∈ L') : (fun k => ρ (z k)) ∈ locSp W ρ L' := by
  obtain ⟨u, hu'⟩ := hs
  have hmem : (fun k => ρ (((s : E) • z) k)) ∈ locSp W ρ L' := Submodule.subset_span ⟨_, hz, rfl⟩
  have e : (fun k => ρ (z k)) = ((↑u⁻¹ : W)) • (fun k => ρ (((s : E) • z) k)) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Algebra.smul_def]
    rw [← mul_assoc, ← map_natCast (algebraMap W K) s, ← hu', ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

theorem locSp_maps_of_unit_smul {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N N' : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E))
    (A : Matrix (Fin N') (Fin N) E) (s : ℕ) (hs : IsUnit (s : W)) (hA : ∀ x ∈ L, (s : E) • (A *ᵥ x) ∈ L') :
    ∀ z ∈ locSp W ρ L, (A.map ρ) *ᵥ z ∈ locSp W ρ L' := by
  intro w hw
  have h : locSp W ρ L ≤ (locSp W ρ L').comap (((A.map ρ).mulVecLin).restrictScalars W) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    show (A.map ρ) *ᵥ (fun k => ρ (x k)) ∈ locSp W ρ L'
    have e : (A.map ρ) *ᵥ (fun k => ρ (x k)) = fun k => ρ ((A *ᵥ x) k) := by
      funext k
      exact (RingHom.map_mulVec ρ A x k).symm
    rw [e]
    exact mem_locSp_of_natCast_smul_mem W K ρ L' _ s hs (hA x hx)
  exact h hw

end GlobalTheory.TwV

end
end

section

namespace GlobalTheory.TwV

open NumberField
open scoped Matrix

theorem map_apply_eq_mulVec {E K : Type} [Field E] [Field K] (ρ : E →+* K) {N n : ℕ}
    (f : (Fin N → E) →ₗ[E] (Fin n → E)) (x : Fin N → E) :
    (fun k => ρ (f x k)) = ((LinearMap.toMatrix' f).map ρ) *ᵥ (fun k => ρ (x k)) := by
  funext k
  rw [← LinearMap.toMatrix'_mulVec f x]

  simp [Matrix.mulVec, dotProduct, map_sum]

theorem locSp_map {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N n : ℕ} (f : (Fin N → E) →ₗ[E] (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    locSp W ρ (Λ.map (f.restrictScalars (𝓞 E))) =
      (locSp W ρ Λ).map ((((LinearMap.toMatrix' f).map ρ).mulVecLin).restrictScalars W) := by
  unfold locSp
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact map_apply_eq_mulVec ρ f x

end GlobalTheory.TwV
end
