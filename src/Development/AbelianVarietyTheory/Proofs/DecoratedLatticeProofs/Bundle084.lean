module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFifth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardAdditiveCharacterLocalNeOneSplitPrime
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle062
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
public import Formalism.LocalRingCardinality.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle082
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem latAt_sumLat_self {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) :
    latAt w (sumLat finSumFinEquiv L L) = sumLat finSumFinEquiv (latAt w L) (latAt w L) := by
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  have hl0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e (x + y) 0 = pairVec e x 0 + pairVec e y 0 := by
    intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hr0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e 0 (x + y) = pairVec e 0 x + pairVec e 0 y := by
    intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hls : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e (c • x) 0 = c • pairVec e x 0 := by
    intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hrs : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e 0 (c • x) = c • pairVec e 0 x := by
    intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hz : pairVec e (0 : Fin n → w.adicCompletion E) 0 = 0 := by
    funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hsplit : ∀ (x y : Fin n → w.adicCompletion E), pairVec e x y = pairVec e x 0 + pairVec e 0 y := by
    intro x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  set φ : (Fin n → E) → (Fin n → w.adicCompletion E) := fun x i => algebraMap E (w.adicCompletion E) (x i)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_sumLat] at hx ⊢
    exact ⟨Submodule.subset_span ⟨_, hx.1, rfl⟩, Submodule.subset_span ⟨_, hx.2, rfl⟩⟩
  · intro z hz'
    rw [← pairVec_eta e z, pairVec_mem_sumLat] at hz'
    rw [← pairVec_eta e z, hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · obtain ⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inl i)) := ⟨_, rfl⟩
      have hu' := hz'.1
      rw [← hu] at hu' ⊢
      clear hu
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e y 0, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨hy, L.zero_mem⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => rw [hz]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [hl0]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [hls]; exact Submodule.smul_mem _ c hx
    · obtain ⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inr i)) := ⟨_, rfl⟩
      have hu' := hz'.2
      rw [← hu] at hu' ⊢
      clear hu
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e 0 y, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨L.zero_mem, hy⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => rw [hz]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [hr0]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [hrs]; exact Submodule.smul_mem _ c hx

theorem isFrameAt_sumLat_blkGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (w.adicCompletion E)), IsFrameAt w L a → IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) := by
  intro E _ _ w n L a ha y
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  rw [latAt_sumLat_self, ← pairVec_eta e y, val_blkGL, blkMat_mulVec, pairVec_mem_sumLat,
    ← ha, ← ha]
  constructor
  · intro h; exact ⟨fun i => by simpa using h (e (.inl i)), fun i => by simpa using h (e (.inr i))⟩
  · rintro ⟨h1, h2⟩ j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [h1, h2]

end GlobalTheory.LFun
end

section

noncomputable section

namespace GlobalTheory.Core.Ht2.DatOneS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem smallDatum_xiCpl1_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (al : I.β (N.R.m - 2)) (p₀ : ChPt (R := N.R) sel mu u (N.R.m - 2)) (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (Y : Set (Sp X.E (N.R.N (N.R.m - 2 + 1)))), SmallDatum (Sall sel mu u) p₀.deco.1.N p.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH al p₀ p Y
  obtain ⟨hrow, hG, hT, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH
  have hI : I.Ok Ch sel mu cst G (N.R.m - 2) := hH.2.2.2.2.2.2.1
  have hfr : ∀ {j : ℕ} (r : ChPt (R := N.R) sel mu u j) (P : rowSG Pr sel mu) x,
      frsF sel mu r P x ∈ r.deco.1.at P.1 ↔ x ∈ stdAt X.E (N.R.N j) P.1 := by
    intro j r P x
    have hP := hrow P.1 P.2
    simp only [frsF, hP, dif_pos]
    exact (GlobalTheory.ColNorms.liftFr_lifts X.E _ _ _ r.deco ⟨P.1, hP⟩).1 x
  have key := @GlobalTheory.ColNorms.DatOne.smallDatum_of_frames X.E X.K _ _ _ _ _ _ (Pr.vT u) _ _ (rowSG Pr sel mu) (fun a b => Classical.propDecidable (a = b))
    p₀.deco.1 p.deco (frsF sel mu p₀) (frsF sel mu p) (hfr p₀) (hfr p) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P => Formalism.L2.Col.qOf P.1) ?_ ?_
    (fun P x => PsiAt Ch sel mu cst (N.R.m - 2) P (I.h (N.R.m - 2) al P) x ((frsF sel mu p P).symm (repY Y))) (fun _ => 1) ?_
  · rw [Finset.prod_const_one] at key
    exact key
  · intro P
    obtain ⟨i, -, hq, -⟩ := hG P.1 (hrow P.1 P.2)
    show Formalism.L2.Col.qOf P.1 ∣ _
    rw [hq]
    refine Dvd.dvd.mul_left ?_ _
    fin_cases i
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  · intro P hP
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hT P hP)
  · intro P
    have hm := hI.hm
    have h := GlobalTheory.T.movedDatum_small_typePrime_any_level CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH (N.R.m - 2) (by omega) P
      (I.h (N.R.m - 2) al P) 1 (hI.stabG _ al P (hrow P.1 P.2)) (one_mem _)
    exact GlobalTheory.ColNorms.DatOne.locSmall_joinCol h _

end GlobalTheory.Core.Ht2.DatOneS

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.UnfoldS

open GlobalTheory.TopStep GlobalTheory.LastSteps GlobalTheory.PadicUnfold GlobalTheory.PadicUnfold.Period GlobalTheory.ColNorms.Unfold

theorem locSmall_XiAt_sharp : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (P : rowSG Pr sel mu), LocSmall (Formalism.L2.Col.qOf P.1) (stdAt X.E (N.R.N i) P.1) (stdAt X.E (N.R.N (i + 1)) P.1) (XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) ((Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2)) := by
  refine ⟨2, fun CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be P => ?_⟩
  obtain ⟨hvG, hpr, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hP : P.1 ∈ Pr.vGs := hvG _ P.2
  obtain ⟨g, -, hg, -, hg2, -⟩ := hpr _ hP
  have hom := GlobalTheory.T.movedDatum_small_typePrime_any_level CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i (by omega) P (I.h i al P) (I.h (i + 1) be P)
  obtain ⟨hH, -, -, -, -, hsharp, hI, -⟩ := H
  have hPr : Pr.Ok := hH.2.2.2.2.2.2.2.2.2.1
  have hq : (Formalism.L2.Col.qOf P.1).Prime := hg ▸ hPr.g_prime g
  rw [← hg] at hg2
  have hs' := hI.stabG (i + 1) be P hP
  replace hom := hom (hI.stabG i al P hP) hs'
  unfold lamYat at hom hs'
  rw [if_pos hP] at hom hs'
  have hE := unfolding_smallHomFunction_levelPrime_bounded hq (c' := cOf N.R i) (c := cOf N.R (i + 1)) (by unfold cOf; omega) cst.A cst.B (cst.psi P)
    (fun a ha => by
      have := GlobalTheory.GO.ChRoot.psi_root hI.cst_ok P a (by rwa [hI.depthG P hP, pow_one])
      rwa [hI.depthG P hP, pow_one] at this) _ hom
  refine ⟨fun x hx => hE.1 x (right_ne_zero_of_mul hx), fun x z hz => ?_, fun σ x => ?_⟩
  · unfold XiAt E1at
    rw [hE.2.1 x z hz]
  · have hq1 : (1 : ℝ) ≤ Formalism.L2.Col.qOf P.1 := by exact_mod_cast hq.one_le
    unfold XiAt E1at
    rw [map_mul, norm_mul]
    have h1 := (norm_volN_inv_le (K := X.K) _ _ σ).trans (Nat.cast_le.2
      (relIndex_le hg2 N.R.k N.R.rS N.R.r N.R.t (N.R.N (i + 1)) (cOf N.R (i + 1)) _ hs'))
    unfold Jat lamYat
    rw [if_pos hP, if_pos hP, if_pos hsharp]
    refine (mul_le_mul h1 (hE.2.2 σ x) (norm_nonneg _) (Nat.cast_nonneg _)).trans ?_
    rw [Nat.cast_pow, ← pow_add]
    refine pow_le_pow_right₀ hq1 ?_
    have a1 := rank_le N.R (j := i) (by omega)
    have a2 := rank_le N.R (j := i + 1) (by omega)
    have a3 : cOf N.R i + 1 ≤ N.R.m := by unfold cOf; omega
    unfold NumDatum.Nm
    generalize N.R.N i + cOf N.R i = a at a1 ⊢
    generalize N.R.N (i + 1) + cOf N.R (i + 1) = b at a2 ⊢
    generalize N.R.N N.R.m = M at a1 a2 ⊢
    have b1 : b * b ≤ M * M := Nat.mul_le_mul a2 a2
    have b2 : b * a ≤ M * M := Nat.mul_le_mul a2 a1
    calc b * b + cOf N.R i * (b * a) ≤ M * M + cOf N.R i * (M * M) := by gcongr
      _ = (cOf N.R i + 1) * M ^ 2 := by ring
      _ ≤ (2 * N.R.m ^ 2) * M ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)

end GlobalTheory.Core.Ht2.UnfoldS
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem _root_.GlobalTheory.T.exists_linear_isQuotInt_tInt_alt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ p σ B) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ'), ∃ Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) (Rr Φ)) ∧ IsNEquiv ψ p ρ' Rr := by
  first | exact @GlobalTheory.PosOne.RrLin.exists_linear_isQuotInt_tInt | exact GlobalTheory.PosOne.RrLin.exists_linear_isQuotInt_tInt | (intros; apply GlobalTheory.PosOne.RrLin.exists_linear_isQuotInt_tInt <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.PosOne.Unif

theorem comb_eq_lc {G : Type} (e : G →₀ ℂ) (F : G → ℂ) :
    comb e F = Finsupp.linearCombination ℂ F e := by
  simp [comb, Finsupp.linearCombination_apply, smul_eq_mul]

theorem comb_translate {G : Type} [Group G] (e : G →₀ ℂ) (f : G → G →₀ ℂ) (F : G → ℂ) :
    comb e (fun g => comb (f g) (fun h => F (h * g))) =
      comb (e.sum fun g a => a • (f g).mapDomain (· * g)) F := by
  conv_rhs => rw [comb_eq_lc]

  simp only [Finsupp.sum, map_sum, map_smul, Finsupp.linearCombination_mapDomain, comb_eq_lc, smul_eq_mul]
  rfl

def conjSub {G : Type} [Group G] (U : Subgroup G) (g : G) : Subgroup G :=
  U.comap (MulAut.conj g⁻¹).toMonoidHom

theorem mem_conjSub {G : Type} [Group G] (U : Subgroup G) (g u : G) :
    u ∈ conjSub U g ↔ g⁻¹ * u * g ∈ U := by
  simp [conjSub]

theorem isOpen_conjSub {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (g : G) : IsOpen (conjSub U g : Set G) := by
  have : (conjSub U g : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (U : Set G) := by
    ext x; simp [mem_conjSub]
  rw [this]
  exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem fixed_conjSub {G A : Type} [Group G] [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ G A)
    (U : Subgroup G) (v : A) (hv : ∀ u ∈ U, σ u v = v) (g : G) :
    ∀ u ∈ conjSub U g, σ u (σ g v) = σ g v := by
  intro u hu
  rw [mem_conjSub] at hu
  have e1 : u * g = g * (g⁻¹ * u * g) := by group
  calc σ u (σ g v) = σ (u * g) v := by rw [map_mul]; rfl
    _ = σ g (σ (g⁻¹ * u * g) v) := by rw [e1, map_mul]; rfl
    _ = σ g v := by rw [hv _ hu]

end GlobalTheory.PosOne.Unif

namespace GlobalTheory.PosOne.Unif

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)

theorem toOne_comb (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k)
    (hsd : IsSelfDual ψ ν) : ∀ q : ℕ, q + 1 ≤ c → ∀ (U : Subgroup (GL (n ⊕ Fin c) k)),
    IsOpen (U : Set (GL (n ⊕ Fin c) k)) → ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ,
    ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
      (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), IsNEquiv ψ (q + 1) σ l → (∀ u ∈ U, σ u v = v) →
      toOne ν σ (q + 1) l v = comb e (fun g => l (σ g v)) ∧
        l v = comb e' fun g => toOne ν σ (q + 1) l (σ g v) := by
  haveI : ν.IsAddHaarMeasure := hsd.1
  intro q
  induction q with
  | zero =>
    intro _ U _
    refine ⟨Finsupp.single 1 1, Finsupp.single 1 1, ?_⟩
    intro A _ _ σ _ l v _ _
    simp [comb, toOne_one]
  | succ q ih =>
    intro hc U hU
    have hq1 : 1 ≤ q + 1 := by omega
    have hqc : q + 1 < c := by omega

    have H1 := fun g : GL (n ⊕ Fin c) k =>
      GlobalTheory.T.exchange_eq_finiteTranslateComb_of_level k n c (q + 1) hq1 hqc ψ hψc hψ1 ν (conjSub U g) (isOpen_conjSub U hU g)
    choose eg eg' heg using H1

    have H2 := fun g : GL (n ⊕ Fin c) k => ih (by omega) (conjSub U g) (isOpen_conjSub U hU g)
    choose E E' hE using H2
    obtain ⟨e₀, _e₀', he₀⟩ := ih (by omega) U hU
    obtain ⟨_e₁', e₁, he₁⟩ := GlobalTheory.T.exchange_eq_finiteTranslateComb_of_level k n c (q + 1) hq1 hqc ψ hψc hψ1 ν U hU
    refine ⟨e₀.sum fun g a => a • (eg g).mapDomain (· * g),
      e₁.sum fun g a => a • (E' g).mapDomain (· * g), ?_⟩
    intro A _ _ σ hsm l v hl hv
    obtain ⟨l', hl'eq, hl'pos⟩ :=
      (GlobalTheory.RootEx.Exchange.exchange_isPos k n c (q + 1) hq1 hqc ψ hψc hψ1 ν A σ hsm).2.1 l hl
    have hfun : (⇑l' : A → ℂ) = exDown ν (q + 1) σ ⇑l := funext hl'eq
    have htoOne : toOne ν σ (q + 1 + 1) ⇑l = toOne ν σ (q + 1) ⇑l' := by
      rw [hfun]; rfl
    have hmul : ∀ g h : GL (n ⊕ Fin c) k, σ h (σ g v) = σ (h * g) v := by
      intro g h; rw [map_mul]; rfl
    constructor
    · rw [htoOne, (he₀ A σ hsm l' v hl'pos hv).1]
      have : (fun g => l' (σ g v)) = fun g => comb (eg g) (fun h => l (σ (h * g) v)) := by
        funext g
        rw [hl'eq, (heg g A σ hsm l (σ g v) (fixed_conjSub σ U v hv g)).1 hl]
        simp only [hmul]
      rw [this]; exact comb_translate e₀ eg (fun g => l (σ g v))
    · have hback := ((GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n c (q + 1) hq1 hqc ψ hψc hψ1 ν hsd A σ hsm l v).2 hl).symm
      rw [hback, ← hfun, (he₁ A σ hsm l' v hv).2 hl'pos]
      have : (fun g => l' (σ g v)) =
          fun g => comb (E' g) (fun h => toOne ν σ (q + 1 + 1) l (σ (h * g) v)) := by
        funext g
        rw [(hE g A σ hsm l' (σ g v) hl'pos (fixed_conjSub σ U v hv g)).2, htoOne]
        simp only [hmul]
      rw [this]; exact comb_translate e₁ E' (fun g => toOne ν σ (q + 1 + 1) l (σ g v))

end GlobalTheory.PosOne.Unif

open GlobalTheory.PosOne.Unif in
theorem GlobalTheory.PosOne.toOne_uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (U : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (U : Set (GL (n ⊕ Fin c) k))), ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ, ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), IsNEquiv ψ P σ l → (∀ u ∈ U, σ u v = v) → toOne ν σ P l v = comb e (fun g => l (σ g v)) ∧ l v = comb e' fun g => toOne ν σ P l (σ g v) := by
  intro k _ _ _ _ _ _ n _ _ c P hP hPc ψ hψc hψ1 ν hsd U hU
  obtain ⟨q, rfl⟩ : ∃ q, P = q + 1 := ⟨P - 1, by omega⟩
  obtain ⟨e, e', h⟩ := toOne_comb k n c ψ hψc hψ1 ν hsd q hPc U hU
  exact ⟨e, e', fun A _ _ σ hsm l v hl hv => h A σ hsm l v hl hv⟩
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.St.G.SplitUnram

theorem not_sq_dvd_of_splitsIn : ∀ (E : Type) [Field E] [NumberField E] (T : ℕ), T.Prime → GlobalTheory.St.G.SplitsIn E T →
    ∀ w : HeightOneSpectrum (𝓞 E), (T : 𝓞 E) ∈ w.asIdeal → ¬ w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 E)} := by
  intro E _ _ T hT hs w hw hdvd
  have := w.isPrime
  have hnd := GlobalTheory.St.G.PsiLoc.not_dvd_different hT hs w.asIdeal hw
  have hun : Algebra.IsUnramifiedAt ℤ w.asIdeal := not_dvd_differentIdeal_iff.1 hnd
  have he : w.asIdeal.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hp : Prime (T : ℤ) := Nat.prime_iff_prime_int.mp hT
  have hmax : (Ideal.span {(T : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(T : ℤ)}) = Ideal.span {((T : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(T : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hw
  have : w.asIdeal.LiesOver (Ideal.span {(T : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(T : ℤ)} ≠ ⊥ := by simpa using hT.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(T : ℤ)}) w.asIdeal hb] at he
  have h2 := (Ideal.ramificationIdx'_ne_one_iff hle).2
  rw [hmap] at h2
  exact h2 (Ideal.le_of_dvd hdvd) he

end GlobalTheory.St.G.SplitUnram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.contDiff_heisenbergTranslate_thetaFunction_realCoords : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ v : WO S T, ContDiff ℝ ∞ (fun z : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v) ∧ ∀ z u : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun z : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v) z u = (Real.pi * Complex.I) * ((GlobalTheory.OrientedHeis.omO S T z u : ℝ) : ℂ) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v + heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) (fun y => deriv (fun s : ℝ => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (s • u)) F y) 0) v := by
  first | exact @GlobalTheory.ThetaTranslate.contDiff_heisO_iota_fderiv | exact GlobalTheory.ThetaTranslate.contDiff_heisO_iota_fderiv | (intros; apply GlobalTheory.ThetaTranslate.contDiff_heisO_iota_fderiv <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.kernelReduction_extend_evaluated_integrated : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it ev' it' : Finset (m × m')), ev ⊆ ev' → it ⊆ it' → Disjoint ev' it' → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ ev', e ∉ ev → ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ e ∈ it', e ∉ it → ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev' it' β l := by
  first | exact @GlobalTheory.FlatFactor.KerRedStep.kerRed_extend | exact GlobalTheory.FlatFactor.KerRedStep.kerRed_extend | (intros; apply GlobalTheory.FlatFactor.KerRedStep.kerRed_extend <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orthProjReferenceFrame_on_flagBasis_mod_level : ∀ (D : D7) (X : HidaSetting D), (∀ y ∈ X.B.I.Lf, GlobalTheory.ScalW.prj0 X y ∈ X.B.I.Lf) ∧ ∀ j : ℕ, flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ X.B.I.Lf ∧ (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k → GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) ∈ mL X.B.I X.B.g) ∧ (¬ (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k) → GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) - flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ mL X.B.I X.B.g) := by
  first | exact @GlobalTheory.RefProjFlag.prj0_flagVec_mem_mL_or_sub_mem_mL | exact GlobalTheory.RefProjFlag.prj0_flagVec_mem_mL_or_sub_mem_mL | (intros; apply GlobalTheory.RefProjFlag.prj0_flagVec_mem_mL_or_sub_mem_mL <;> assumption)
end

section

open Formalism.BasicNotions

namespace GlobalTheory.Core.Rk.GapOfNodes

theorem harishChandraNodesFarApart_of_cubic_node_gap : ∀ D : D7, D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6) →
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D := by
  intro D H
  have hN : D.R.N D.R.m = D.R.rankX' + 1 := factXm D.R
  refine ⟨D.R.N D.R.m, hN.ge, fun τ i hi => ?_⟩
  have h := H D.u₀ τ i.1 hi
  rw [D.hcW_b D.u₀ τ] at h
  simp only [Fin.eta] at h
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := by positivity
  have hc : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 := by positivity
  have key : (((D.R.t : ℚ) + 2 * ((D.R.N D.R.m : ℕ) : ℚ) ^ 3 + 1 : ℚ) : ℝ) ≤
      (((D.hc τ).b ⟨i.1 + 1, hi⟩ - (D.hc τ).b i : ℚ) : ℝ) := by
    push_cast
    push_cast at h
    linarith
  exact_mod_cast key

end GlobalTheory.Core.Rk.GapOfNodes
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.places_dvd_norm_iff_under_primes_dvd : ∀ (D : Formalism.BasicNotions.D7) (π π' : 𝓞 D.host.E) (T : ℕ), (π' : D.host.E) = star (π : D.host.E) → π * π' = (T : 𝓞 D.host.E) → π ≠ 0 → ∀ x : HeightOneSpectrum (𝓞 D.host.F), (T : 𝓞 D.host.F) ∈ x.asIdeal ↔ ∃ w ∈ Formalism.L2.Col.divs π, w.under (𝓞 D.host.F) = x := by
  first | exact @GlobalTheory.NormPlaces.places_dvd_iff | exact GlobalTheory.NormPlaces.places_dvd_iff | (intros; apply GlobalTheory.NormPlaces.places_dvd_iff <;> assumption)
end
