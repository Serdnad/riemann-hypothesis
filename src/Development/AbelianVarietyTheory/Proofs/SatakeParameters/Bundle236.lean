module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle227
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle211
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle210
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle224
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle217
public import Formalism.LocalToGlobal.Columns.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle230
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

open Formalism.L2.KerInert.SharpPolyP

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

def zA {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  if IsOddPos (pos.symm τ).2 then (f τ).adjugate.transpose.submatrix id Fin.rev else f τ

def adjPol {n : ℕ} (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) : MvPolynomial (GL3Theta.FrV D n) ℂ :=
  MvPolynomial.aeval (fun k : GL3Theta.FrV D n => if IsOddPos (pos.symm k.1).2 then
    (Matrix.of fun a b : Fin n => (MvPolynomial.X (k.1, a, b) : MvPolynomial (GL3Theta.FrV D n) ℂ)).adjugate (Fin.rev k.2.2) k.2.1
    else MvPolynomial.X k) Q

theorem eval_adj {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (i j : Fin n) :
    MvPolynomial.eval (pt x) ((Matrix.of fun a b : Fin n => (MvPolynomial.X (τ, a, b) : MvPolynomial (GL3Theta.FrV D n) ℂ)).adjugate i j)
      = (x τ).adjugate i j := by
  have h := congrArg (fun M => M i j) (RingHom.map_adjugate (MvPolynomial.eval (pt x))
    (Matrix.of fun a b : Fin n => (MvPolynomial.X (τ, a, b) : MvPolynomial (GL3Theta.FrV D n) ℂ)))
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h
  rw [h]
  congr 1
  ext a b
  simp

theorem eval_adjPol {n : ℕ} (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (pt x) (adjPol X D pos Q) = MvPolynomial.eval (pt (zA X D pos x)) Q := by
  unfold adjPol
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X q k hq =>
    rw [map_mul, map_mul, hq, map_mul]
    congr 1
    rw [MvPolynomial.aeval_X, MvPolynomial.eval_X]
    show _ = zA X D pos x k.1 k.2.1 k.2.2
    unfold zA
    split_ifs with h
    · rw [eval_adj]; rfl
    · rw [MvPolynomial.eval_X]

def dg {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun _ => if IsOddPos (pos.symm τ).2 then ((x τ).det)⁻¹ else 1

theorem zT_eq_mul {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos x = fun τ => zA X D pos x τ * dg X D pos x τ := by
  funext τ
  unfold zT zA dg
  split_ifs with h
  · ext i j
    simp [Matrix.mul_diagonal, Matrix.inv_def, Ring.inverse_eq_inv', mul_comm]
  · simp

theorem dg_bor {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hx : ∀ τ, (x τ).det ≠ 0) :
    IsBor (dg X D pos x) := by
  intro τ
  refine ⟨fun r s hsr => ?_, fun r => ?_⟩
  · unfold dg
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hsr)
  · unfold dg
    rw [Matrix.diagonal_apply_eq]
    split_ifs
    · exact inv_ne_zero (hx τ)
    · exact one_ne_zero

theorem eval_zT {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (hQ : Q ∈ WtPol ℂ ν)
    (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hx : ∀ τ, (x τ).det ≠ 0) :
    MvPolynomial.eval (pt (zT X D pos x)) Q =
      (∏ τ, ∏ r, (if IsOddPos (pos.symm τ).2 then ((x τ).det)⁻¹ else 1) ^ ν τ r) *
        MvPolynomial.eval (pt x) (adjPol X D pos Q) := by
  rw [eval_adjPol, zT_eq_mul, ← sp_eval_colSub (dg X D pos x) (zA X D pos x) Q, hQ _ (dg_bor X D pos x hx),
    MvPolynomial.smul_eval]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun r _ => ?_
  unfold dg
  rw [Matrix.diagonal_apply_eq]

theorem twF_mul_det_poly : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}, 0 < n → ∀ (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ (K : D.what₂.Tau → ℕ) (P : MvPolynomial (GL3Theta.FrV D n) ℂ), ∀ x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (x τ).det ≠ 0) → MvPolynomial.eval (fun k : GL3Theta.FrV D n => x k.1 k.2.1 k.2.2) P = twF X D pos c Q x * ∏ τ, (x τ).det ^ K τ := by
  intro p _ X D pos n hn ν c hc Q hQ
  have hc0 : ∀ τ, 0 ≤ c τ := fun τ => le_trans (Int.natCast_nonneg _) (hc τ ⟨0, hn⟩)
  refine ⟨fun τ => if IsOddPos (pos.symm τ).2 then ∑ r, ν τ r else 0,
    (∏ τ, if IsOddPos (pos.symm τ).2 then
        MvPolynomial.C ((sgRev n ^ (c τ).toNat)⁻¹) * frDet ℂ n τ ^ (c τ).toNat else 1) * adjPol X D pos Q, ?_⟩
  intro x hx
  change MvPolynomial.eval (pt x) _ = _
  have key : ∀ τ, MvPolynomial.eval (pt x) (if IsOddPos (pos.symm τ).2 then
        MvPolynomial.C ((sgRev n ^ (c τ).toNat)⁻¹) * frDet ℂ n τ ^ (c τ).toNat else 1) =
      (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ).det ^ (-(c τ)) else 1) *
        (∏ r, (if IsOddPos (pos.symm τ).2 then ((x τ).det)⁻¹ else 1) ^ ν τ r) *
        (x τ).det ^ (if IsOddPos (pos.symm τ).2 then ∑ r, ν τ r else 0) := by
    intro τ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, c τ = m := ⟨(c τ).toNat, (Int.toNat_of_nonneg (hc0 τ)).symm⟩
    have hd := hx τ
    rw [det_zT]
    split_ifs with h
    · rw [map_mul, map_pow, MvPolynomial.eval_C, sp_eval_frDet, hm, Int.toNat_natCast, zpow_neg, zpow_natCast,
        Finset.prod_pow_eq_pow_sum, mul_assoc, ← mul_pow, inv_mul_cancel₀ hd, one_pow, mul_one, mul_pow, mul_inv,
        inv_pow, inv_inv]
    · simp
  unfold twF
  rw [map_mul, map_prod, Finset.prod_congr rfl (fun τ _ => key τ), Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  change _ = _ * MvPolynomial.eval (pt (zT X D pos x)) Q * _
  rw [eval_zT X D pos ν Q hQ x hx]
  ring

end GlobalTheory.TwV.DelA
end
end

section

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop facPen Zmu)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

def JetLossAllAt {X : Fields} (Pr : Primes X) (R : Ranks) (A : Amb X)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) : Prop :=
  ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
  ∀ (u : Pr.Word) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok →
  ∀ (j b : ℕ), j < R.m → b = R.N (j + 1) →
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.g i) N → _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.g i) N' →
  ∀ Ξ : HomE X.E (R.N j) b → X.K, DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w N N' Ξ →
  ∀ e : DVar X.Tau (R.N j) b →₀ ℕ, e.degree + 1 < Pr.g i →
    (∀ c : ℕ, 0 < c → c ∣ cAof sel mu cst * cBof sel mu cst u → e ∈ RatIdx A (Sall sel mu u) (cAof sel mu cst) c N N' Ξ) →
    w.valuation X.K ((Pr.g i : X.K) ^ (X.f * R.N j * b) *
      (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n) *
      jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ e) ≤ 1

def JetLossAll (D : D7) (EX : ErrX D) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Prop :=
  HostTie EX → IsSel (recFields D) sel → AnTie D δ χ cD →
    JetLossAllAt (recPrimes EX) D.R (ambOf (recSeam D) B χ cD) sel (badS D)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

section
variable (A : Amb X)

theorem kerOf_bound_all (hJ : JetLossAllAt Pr R A sel S) (hO : JetOpWeyl) (hW : ChainWeights) (hPr : Pr.Ok)
    (hc : cst.Ok) (u : Pr.Word) (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal)
    {j j' : ℕ} (hj : j < R.m) (hj' : j' = j + 1)
    (hscal : ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)),
      IsSdLat N → _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.g i) N → IsFrames N fr →
      w.valuation X.K (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr) = 1)
    (hdeg : (∑ τ, ∑ a, (W.nuW u (j + 1) τ).w a) + 1 < Pr.g i)
    (hrat : GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.JetsRatDeg A (R.N j) (R.N (j + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      fun τ => ∑ a, (W.nuW u (j + 1) τ).w a)
    {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := SG)) (d' : DecoSet (E := X.E) (n := R.N j') (ST := Pr.vT u) (SG := SG'))
    (hs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.g i) d.1.N) (hs' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.g i) d'.1.N) {fr : Frs X.E (R.N j) (rowSG Pr sel mu)}
    {fr' : Frs X.E (R.N j') (rowSG Pr sel mu)} (hf : IsFrames d.1.N fr) (hf' : IsFrames d'.1.N fr')
    {Ξ : HomE X.E (R.N j) (R.N j') → X.K}
    (hΞ : DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w d.1.N d'.1.N Ξ)
    {v : Formalism.L2.DIV.VV X.K (W.lamTrue u j)} (hv : v ∈ localization₂ w.asIdeal (delAtr X.emb (W.lamTrue u j) d.1.Lsh)) :
    lossAt W i u j • kerOf (stepC W Ch sel mu cst A u j (W.lamTrue u j')) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
      d.1.N fr d'.1.N fr' Ξ v ∈ localization₂ w.asIdeal (delAtr X.emb (W.lamTrue u j') d'.1.Lsh) := by
  classical
  subst hj'
  have hT : ∀ Q ∈ Pr.vT u, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := fun Q hQ h =>
    natCast_notMem_of_ne (hPr.T_prime u) (hPr.g_prime i) (hPr.T_ne_g u i) _ h (T_mem_of_piT_mem hPr u (mem_divs hQ))
  have hsd : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hsd' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  rw [(GlobalTheory.GO.use₃ _ hT d w hw).2] at hv
  rw [(GlobalTheory.GO.use₃ _ hT d' w hw).2, stepC,
    kerOf_thDistC A _ _ (cAof_pos sel mu cst) (cBof_pos sel mu cst hPr u) _ _ _ _ _ _ d.2.lat d'.2.lat,
    LinearMap.smul_apply, smul_comm]
  refine smul_mem_localizationAt_of_le w _ ?_ ?_
  · rw [map_mul, map_inv₀, hscal _ _ _ hsd hs hf, hscal _ _ _ hsd' hs' hf', inv_one, one_mul]
  obtain ⟨s, s', hwt, hnu⟩ := hW X Pr R W u j hj
  refine hO X.K w X.Tau _ _ _ _ _ s s' _ hwt _ _
    (fun τ => (GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau _ X.emb τ _ (Formalism.L2.Ker.full_of_sd hsd)).toIsLattice)
    (fun τ => (GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau _ X.emb τ _ (Formalism.L2.Ker.full_of_sd hsd')).toIsLattice)
    (latWithBasis_of_stdOver X.emb (hPr.g_prime i).ne_zero d.2.lat hs w hw)
    (latWithBasis_of_stdOver X.emb (hPr.g_prime i).ne_zero d'.2.lat hs' w hw) _ _ (fun e he => ?_) v hv
  · have h1 : ∀ τ, ((∑ β, ∑ α, e (τ, β, α) : ℕ) : ℤ) = ∑ a, (W.nuW u (j + 1) τ).w a := fun τ => by
      rw [he τ]
      exact Finset.sum_congr rfl fun a _ => hnu τ a
    have h2 : (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n) =
        ∏ τ, X.emb τ (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ (∑ a, (W.nuW u (j + 1) τ).w a).toNat := by
      rw [Finsupp.prod_fintype _ _ fun _ => pow_zero _, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun τ _ => ?_
      dsimp only
      rw [← h1 τ, Int.toNat_natCast, Finset.prod_pow_eq_pow_sum, Fintype.sum_prod_type]
    have h3 : e.degree + 1 < Pr.g i := by
      have h4 : (e.degree : ℤ) = ∑ τ, ∑ a, (W.nuW u (j + 1) τ).w a := by
        rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, Nat.cast_sum]
        exact Finset.sum_congr rfl fun τ _ => by rw [← h1 τ, Fintype.sum_prod_type]
      omega
    rw [lossAt, ← h2]
    refine hJ i w hw u mu cst hc j _ hj rfl _ _ hsd hsd' hs hs' Ξ hΞ e h3 fun c hc0 hdvd x hx _ => ?_
    refine hrat _ _ _ x ⟨hsd, hsd', hc0, hdvd, ?_⟩ e fun τ => ?_
    · change ((cAof sel mu cst * cBof sel mu cst u : ℕ) : 𝓞 X.E) • x ∈ homAt _ _ _
      rw [Nat.cast_mul, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ hx
    · dsimp only
      rw [← h1 τ]
      have h5 : (∑ β, ∑ α, (e (τ, β, α) : ℤ)) = ((∑ β, ∑ α, e (τ, β, α) : ℕ) : ℤ) := by
        push_cast
        rfl
      convert (GlobalTheory.ColPeriodCompare.deg_eq e τ).trans h5

end

variable (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Amb X)



theorem colMu_bound_all (hJ : JetLossAllAt Pr R A sel S) (hO : JetOpWeyl) (hW : ChainWeights) (hM : StdMove)
    (hLP : LevelPrimes) (hSU : ScalarUnit) (hEG : EntryAtG) (hEQ : EntryAtQ) (hTQ : TopAtQ)
    (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hS : Pr.T u ∈ S) (hSg : ∀ i, Pr.g i ∈ S)
    {G : ChGlob X R.m} {m2 : ℕ} (hL : L.Ok Ch sel mu cst G m2) {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E}
    (hT : Ch.Tied G.σ₀ e G.mu0 eta) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (hK : KerEquivC W Ch sel mu cst L A u m2 b hY P) (hF : ∀ j, (chF W sel mu L u j).Ok)
    (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal)
    (hwt : ∀ j ≤ R.m, ∀ b, WtUnit w ((chF W sel mu L u j).mem b))
    (hdeg : ∀ j < R.m, (∑ τ, ∑ a, (W.nuW u (j + 1) τ).w a) + 1 < Pr.g i)
    (hrat : ∀ j < R.m, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.JetsRatDeg A (R.N j) (R.N (j + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      fun τ => ∑ a, (W.nuW u (j + 1) τ).w a)
    (φ : MfV W Ch u) (hφ : φ ∈ MfL W Ch u) (d : (evGSD W Ch sel mu P u).D) :
    (∏ j ∈ Finset.range R.m, lossAt W i u j) • (colMu W Ch sel mu cst L A u m2 b hY P hK hF hL φ).1 d ∈
      localization₂ w.asIdeal ((evGSD W Ch sel mu P u).Del d) := by
  have hm := hL.hm
  have hlp := hLP X Pr sel S mu hX hPr hsel
  have hq : ∀ Q : rowSG Pr sel mu, Q.1 ∉ Pr.vGs → ((qOf Q.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal := fun Q hQ =>
    natCast_notMem_of_ne (hlp Q).1.1 (hPr.g_prime i) (fun h => (hlp Q).2 hQ (h ▸ hSg i)) w hw
  have hsu := hSU X Pr R Ch sel S mu cst L G m2 e eta hX hPr hsel hSg hT hL i w hw
  have heq := fun (Q : rowSG Pr sel mu) (hQ : Q.1 ∉ Pr.vGs) => hEQ X Pr R Ch sel S mu cst L G m2 hL Q w hQ (hlp Q).1 (hq Q hQ)
    fun j hj => (hsu j hj).1 Q fun h => hQ (vG_subset i h)
  have hcd := GlobalTheory.LastSteps.chainDataGuarded X Pr R Ch sel S mu cst m2 hPr hL.cst_ok hm
  rw [show Finset.range R.m = Finset.range (m2 + 2) by rw [hm]]
  refine colCpl_bound (chKerC W Ch sel mu cst L A u m2 b hY P hK).kk hF (fun j hj b => hwt j (by omega) b)
    (lossAt W i u) (chKerC W Ch sel mu cst L A u m2 b hY P hK).cp (hF (m2 + 1) b) (hwt _ (by omega) b)
    (fun j hj al be p p' => ?_) (fun al p₀ p Y hYm => ?_) (fun al p d₁ Y hYm => ?_) (startC hL u φ)
    (fun b' p => GlobalTheory.TestLat.WeylLocal.le_locP w _ (hφ (DecoF.deco p))) d
  · obtain ⟨g, hg⟩ := exists_std_pt W sel mu L hM hPr i u j al p
    obtain ⟨g', hg'⟩ := exists_std_pt W sel mu L hM hPr i u (j + 1) be p'
    refine Bd.transfer g g' ((hF j al).del_smul g p) ((hF (j + 1) be).del_smul g' p')
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk j al be).equiv g g' p p') ?_
    generalize g • p = p, g' • p' = p' at hg hg' ⊢
    have e1 : ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk j al be).k p p' =
        matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) j al be p p' := by
      simp only [chKerC, chKer, dif_pos hj]
    rw [e1]
    intro v hv
    refine kerOf_bound_all W Ch sel mu cst A hJ hO hW hPr hL.cst_ok u i w hw (by omega) rfl (hsu j (by omega)).2
      (hdeg j (by omega)) (hrat j (by omega)) (DecoF.deco p) (DecoF.deco p') hg hg' (isFrames_frsF p)
      (isFrames_frsF p') ?_ hv
    exact datumAt_prod hPr hL.cst_ok u i w (DecoF.deco p).1 (DecoF.deco p').2
      (fun Q x => XiAt Ch sel mu cst j Q (L.h j al Q) (L.h (j + 1) be Q) (inFr (frsF sel mu p Q) (frsF sel mu p' Q) x))
      (fun Q hQ => fnModAt_inFr (isFrames_frsF p Q) (isFrames_frsF p' Q)
        (hEG X Pr R Ch sel S mu cst L G m2 hL j hj al be Q hQ (hlp Q).1))
      (fun Q hQ => awayAt_inFr (isFrames_frsF p Q) (isFrames_frsF p' Q) ((heq Q hQ).1 j hj al be))
  · obtain ⟨g, hg⟩ := exists_std_pt W sel mu L hM hPr i u m2 al p₀
    obtain ⟨g', hg'⟩ := exists_std_pt W sel mu L hM hPr i u (m2 + 1) b p
    refine Bd.transfer g g' ((hF m2 al).del_smul g p₀) ((hF (m2 + 1) b).del_smul g' p)
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).equiv1 g g' p₀ p Y) ?_
    have hY' := ((ybCpl W sel mu cst L u m2 b hY).equiv g' p Y).2 hYm
    suffices key : ∀ (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) Y',
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.g i) (DecoF.deco p₀).1.N → _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.g i) (DecoF.deco p).1.N → Y' ∈ ybSet sel mu cst (DecoF.deco p).1.N →
        Bd w (lossAt W i u m2) (((chF W sel mu L u m2).mem al).Del p₀) (((chF W sel mu L u (m2 + 1)).mem b).Del p)
          (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k1 p₀ p Y') from key _ _ _ hg hg' hY'
    intro p₀ p Y' hg hg' hY''
    have e1 : ((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k1 p₀ p Y' =
        cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al p₀ p Y' := rfl
    rw [e1, cp1K, if_pos hY'']
    intro v hv
    refine kerOf_bound_all W Ch sel mu cst A hJ hO hW hPr hL.cst_ok u i w hw (by omega) rfl (hsu m2 (by omega)).2
      (hdeg m2 (by omega)) (hrat m2 (by omega)) (DecoF.deco p₀) (DecoF.deco p) hg hg' (isFrames_frsF p₀)
      (isFrames_frsF p) ?_ hv
    exact datumAt_prod hPr hL.cst_ok u i w (DecoF.deco p₀).1 (DecoF.deco p).2 (facPen Ch sel mu cst L m2 al p₀ p Y')
      (fun Q hQ => (hcd Q hQ).2.2.2.1 L al (hL.stabG m2 al Q hQ) u p₀ p Y' hY'')
      (fun Q hQ => awayAt_inFr (isFrames_frsF p₀ Q) (isFrames_frsF p Q) ((heq Q hQ).2 al _))
  · obtain ⟨g, hg⟩ := exists_std_pt W sel mu L hM hPr i u (m2 + 1) b p
    obtain ⟨γ, hγ⟩ := hM X Pr hPr i _ d₁.1.N ⟨d₁.2.lat, d₁.2.uni⟩
    refine Bd.transfer (S' := evGSD W Ch sel mu P u) g (γ, 1) ((hF (m2 + 1) b).del_smul g p)
      (evGSD_del_smul W Ch sel mu hPr hsel u hS P γ d₁)
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).equiv2 g (γ, 1) p Y d₁) ?_
    have hY' := ((ybCpl W sel mu cst L u m2 b hY).equiv g p Y).2 hYm
    have hγ' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.g i) (((γ, 1) : (evGSD W Ch sel mu P u).G) • d₁).1.N := hγ
    suffices key : ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) Y' (d₂ : RowPt Pr R sel mu),
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.g i) (DecoF.deco p).1.N → Y' ∈ ybSet sel mu cst (DecoF.deco p).1.N → _root_.GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.g i) d₂.1.N →
        Bd w (lossAt W i u (m2 + 1)) (((chF W sel mu L u (m2 + 1)).mem b).Del p) ((evGSD W Ch sel mu P u).Del d₂)
          (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k2 p Y' d₂) from key _ _ _ hg hY' hγ'
    intro p Y' d₂ hg hY'' hγ'
    have e1 : ((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k2 p Y' d₂ =
        cp2K W Ch sel mu cst (chTh W Ch sel mu cst A u m2) p Y' d₂ := rfl
    rw [e1, cp2K, if_pos hY'']
    intro v hv
    refine kerOf_bound_all W Ch sel mu cst A hJ hO hW hPr hL.cst_ok u i w hw (j := m2 + 1) (j' := R.m) (by omega) hm
      (hsu _ (by omega)).2 (hdeg _ (by omega)) (hrat _ (by omega)) (DecoF.deco p) (tilQ sel mu u d₂) hg
      (stdOver_tilH _ (conj_piT_notMem hPr u) (piT_notMem_rowSG sel mu hPr hsel u hS) d₂ hγ') (isFrames_frsF p)
      (isFrames_frsT d₂) ?_ hv
    exact datumAt_prod hPr hL.cst_ok u i w (DecoF.deco p).1 (tilQ sel mu u d₂).2 (facTop Ch sel mu cst m2 p Y' d₂)
      (fun Q hQ => (hcd Q hQ).2.2.2.2 u (piT_notMem_rowSG sel mu hPr hsel u hS) p d₂ Y' hY'')
      (fun Q hQ => hTQ X Pr R Ch sel S mu cst L G m2 u hPr hsel hS hL Q w hQ (hlp Q).1 (hq Q hQ) p d₂ Y' hY'')

end GlobalTheory.ColPeriod
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelA.ActInv

theorem det_inv_gl {n : ℕ} {F : Type} [Field F] (A : GL (Fin n) F) :
    ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = (A : Matrix (Fin n) (Fin n) F).det⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ}

theorem det_placeBlockMatrix_unit_twist (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (g : Tau → GL (Fin n) ℂ)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    ((hAt P h pos (fun _ => 1) g v s : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det =
      if Even s.val then (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ).det
      else (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ).det⁻¹ := by
  unfold hAt
  by_cases hs : Even s.val
  · simp only [hs, if_true, one_mul, inv_one, mul_one]
    show (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).det = _
    unfold reM
    rw [Matrix.det_submatrix_equiv_self]
  · simp only [hs, if_false, one_mul, inv_one, mul_one]
    show (Matrix.transpose (((reG P h (g (pos ⟨v, s⟩)))⁻¹ : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)).det = _
    rw [Matrix.det_transpose, det_inv_gl]
    show (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).det⁻¹ = _
    unfold reM
    rw [Matrix.det_submatrix_equiv_self]

theorem inv_placeBlockMatrix_unit_twist (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (g : Tau → GL (Fin n) ℂ)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    (((hAt P h pos (fun _ => 1) g v s)⁻¹ : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) =
      if Even s.val then reM P h (((g (pos ⟨v, s⟩))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      else Matrix.transpose (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold hAt
  by_cases hs : Even s.val
  · simp only [hs, if_true, one_mul, inv_one, mul_one]
    rw [← map_inv]
    rfl
  · simp only [hs, if_false, one_mul, inv_one, mul_one]
    rfl

end GlobalTheory.TwV.DelA.ActInv


open GlobalTheory.TwV.DelA.ActInv in
theorem GlobalTheory.TwV.DelA.actC_inv_read : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ R : XR (X.Pj (j + 1)) ℂ, MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ R) = ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') (MvPolynomial.map ι R) := by
  intro p _ X D pos Kc _ _ _ ι ρ hT fd j hN La' M hU hF R
  have hblk := GlobalTheory.TwV.DelA.blkC_atR_read X D pos Kc ι ρ hT M hU
  have hcoe : ∀ {k : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin k) A),
      ((Matrix.GeneralLinearGroup.map f g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) = (g : Matrix (Fin k) (Fin k) A).map f :=
    fun _ _ => rfl
  have hdm : ∀ {k : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : Matrix (Fin k) (Fin k) A),
      (g.map f).det = f g.det := fun f g => (RingHom.map_det f g).symm
  have hev : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), Even s.val ↔ ¬ IsOddPos s := by
    intro v s; unfold IsOddPos; rw [Nat.even_iff]; omega
  have hsc : (∏ v, ∏ s, ((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) Kc).det ^ (-eAt (X.Pj (j + 1)) v s)) =
      ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) := by
    rw [map_prod, ← Equiv.prod_comp pos, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    have he : eAt (X.Pj (j + 1)) v s = eT X D pos (j + 1) (pos ⟨v, s⟩) := by
      show _ = eAt (X.Pj (j + 1)) ((pos.symm (pos ⟨v, s⟩)).1) ((pos.symm (pos ⟨v, s⟩)).2)
      rw [Equiv.symm_apply_apply]
    rw [he, (eT_last_pair X D pos j _).2, Equiv.symm_apply_apply, hcoe, hdm, det_placeBlockMatrix_unit_twist]
    rw [show posJ X D pos (j + 1) = pos from rfl]
    simp only [atR]
    rw [hcoe, hdm, det_inv_gl, map_inv₀]
    split_ifs with h1 h2 h3
    · exact absurd h2 ((hev v s).1 h1)
    · rw [map_inv₀, map_zpow₀, inv_zpow', neg_neg]
      rfl
    · rw [inv_inv, map_zpow₀, neg_sub]
      rfl
    · exact absurd ((hev v s).2 h3) h1
  have hent : ∀ (v : Fin (X.Pj (j + 1)).nV) (s : Fin ((X.Pj (j + 1)).n' v)) (a b : Fin ((X.Pj (j + 1)).m + 1)),
      ((((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc))⁻¹ : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) Kc) a b =
      GlobalTheory.FrameB.mk Kc fd j La' v s (Fin.cast (rankJ X (j + 1)) a) (Fin.cast (rankJ X (j + 1)) b) := by
    intro v s a b
    rw [← map_inv, hcoe, Matrix.map_apply, inv_placeBlockMatrix_unit_twist]
    have hb := congrFun (congrFun (hblk v s).1 (finCongr (rkT X D hN) a)) (finCongr (rkT X D hN) b)
    have hinv : (atR D M (pos ⟨v, s⟩))⁻¹ = atR D M⁻¹ (pos ⟨v, s⟩) := by simp [atR, map_inv]
    unfold GlobalTheory.FrameB.mk mAt
    rw [Matrix.submatrix_apply, Matrix.map_apply, hF v, Matrix.submatrix_apply]
    rw [show posJ X D pos (j + 1) = pos from rfl]
    split_ifs at hb with h2 <;> split_ifs with h1
    · exact absurd h2 ((hev v s).1 h1)
    · simp only [Matrix.map_apply, Matrix.transpose_apply] at hb
      rw [hinv] at hb
      exact hb
    · simp only [Matrix.map_apply] at hb
      have e : ((atR D M⁻¹ (pos ⟨v, s⟩))⁻¹ : GL (Fin (D.R.N (j + 1))) ℂ) = atR D M (pos ⟨v, s⟩) := by rw [← hinv, inv_inv]
      refine Eq.trans ?_ hb
      exact congrArg ι (congrArg (fun g : GL (Fin (D.R.N (j + 1))) ℂ => (g : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (finCongr (rkT X D hN) a) (finCongr (rkT X D hN) b)) e)
    · exact absurd ((hev v s).2 h2) h1
  have hsub : (substR (X.Pj (j + 1)) Kc fun v s => (((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc))⁻¹ : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc)) = GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    simp only [substR, GlobalTheory.FrameB.tau0, MvPolynomial.aeval_X, GlobalTheory.FrameB.frF]
    refine Fintype.sum_equiv (finCongr (rankJ X (j + 1))) _ _ fun b => ?_
    rw [hent v s a b]
    congr 2
  unfold actC
  rw [map_natActR]
  unfold natActR
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [hsc, hsub]
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

theorem _root_.GlobalTheory.T.twisted_k1_block_decomposition : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b → ∀ g : GLint E N P, g ∈ twK1H P N r (c + 1) → ∃ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b ∧ (extI hN P j)⁻¹ * g ∈ prinCong N P (c + 1) := by
  first | exact @GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 | exact GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 | (intros; apply GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 <;> assumption)
end
