module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HoweSpanFamiliesOfPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle089
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ShortIsot
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.Bundle002
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LogBallEstimates
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LogNormEstimates
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.NilpotentSubgroupRepresentation
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.SecondOrderExpAtInfinitePlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle090
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle042
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle091
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory.LocalLatticeIntegral

open NumberField

theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ r : 𝓞 E, (r : E) = (M : E) * e := by
  have h : IsAlgebraic ℤ e := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic e)
  obtain ⟨M, hM, hi⟩ := h.exists_integral_multiple
  exact ⟨M, hM, ⟨M • e, hi⟩, by simp [zsmul_eq_mul]⟩

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsFullLattice E L] (x : Fin n → E) : ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L := by
  apply GlobalTheory.LatAlmostAll.exists_int_smul_mem <;> assumption

theorem exists_single_mem_latLoc : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∃ (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), c ≠ (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧ ∀ (i : Fin n), Pi.single i (c ⊗ₜ[F] (1 : E)) ∈ GlobalTheory.AdelicU.latLoc F L v := by
  intro F E _ _ _ _ _ n L _ v
  choose N hN hmem using fun i : Fin n => exists_int_smul_mem L (Pi.single i (1 : E))
  have hP : (∏ i, N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hN i
  haveI : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :=
    charZero_of_injective_algebraMap (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).injective
  refine ⟨((∏ i, N i : ℤ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), Int.cast_ne_zero.2 hP, fun i => ?_⟩
  obtain ⟨k, hk⟩ : N i ∣ ∏ j, N j := Finset.dvd_prod_of_mem N (Finset.mem_univ i)
  have h1 : (∏ j, N j) • (Pi.single i (1 : E) : Fin n → E) ∈ L := by
    rw [hk, mul_comm, mul_smul]; exact L.toAddSubgroup.zsmul_mem (hmem i) k
  generalize (∏ j, N j) = P at h1
  refine AddSubgroup.subset_closure ⟨1, one_mem _, _, h1, ?_⟩
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_same, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      zsmul_eq_mul, mul_one]
  · rw [Pi.single_eq_of_ne hj, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero, TensorProduct.tmul_zero]

end GlobalTheory.LocalLatticeIntegral
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralGram

theorem mul_trace_neg {R : Type} [CommRing R] {n : ℕ} (a : R) (c H : Matrix (Fin n) (Fin n) R) :
    a * ((-c) * H).trace = -((a • H) * c).trace := by
  rw [Matrix.neg_mul, trace_neg, trace_mul_comm, Matrix.smul_mul, trace_smul, smul_eq_mul, mul_neg]

theorem trace_cycle_smul {R : Type} [CommRing R] {m n : ℕ} (a : R) (c : Matrix (Fin n) (Fin n) R)
    (y : Matrix (Fin m) (Fin n) R) (z : Matrix (Fin n) (Fin m) R) (G : Matrix (Fin m) (Fin m) R) :
    (y * (a • (c * (z * G)))).trace = ((a • (z * (G * y))) * c).trace := by
  rw [Matrix.mul_smul, Matrix.smul_mul, trace_smul, trace_smul, ← Matrix.mul_assoc y, trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem move_sub {R : Type} [CommRing R] {m n k : ℕ} {M : Matrix (Fin m) (Fin m) R} {X Y : Matrix (Fin m) (Fin n) R}
    {c : Matrix (Fin n) (Fin n) R} (h : M * Y = Y + X * (-c)) (a : R) (z : Matrix (Fin n) (Fin k) R) :
    M * (Y * ((-a) • z)) - Y * ((-a) • z) = X * (a • (c * z)) := by
  rw [← Matrix.mul_assoc, h, Matrix.add_mul, add_sub_cancel_left, Matrix.mul_assoc, neg_smul, Matrix.neg_mul,
    Matrix.mul_neg c, neg_neg, Matrix.mul_smul c]

variable {D : D7}

theorem gramSkew_map (T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) :
    (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) = incA D D.host.xi0 • (adj x * (gA T * x)) := by
  have h : adj (adj x * (gA T * x)) = adj x * (gA T * x) := gram_swap T rfl |>.symm
  have h2 : cA D (-incA D D.host.xi0) = incA D D.host.xi0 := by
    rw [map_neg, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_neg]
  funext i j
  have h3 := congrFun (congrFun h i) j
  change cA D ((-incA D D.host.xi0) * (adj x * (gA T * x)) j i) = incA D D.host.xi0 * (adj x * (gA T * x)) i j
  rw [map_mul, h2, ← h3]
  rfl

theorem starAdj_extX_mul {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) (x : Mx D T.rank ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T (d.extX T x) * x = d.jY * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) := by
  rw [gramSkew_map, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, HypDec.extX_apply, d.pX_eq]
  simp only [adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, giA_gA_cancel, Matrix.smul_mul, Matrix.mul_smul]

theorem qS_eq {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) (c : skewA D ρ) (x : Mx D T.rank ρ) :
    d.qS T c x = -(algebraMap D.host.F (AF D.host.F) (1 / 2) *
      Algebra.trace (AF D.host.F) (AE D) ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) * c.1).trace) := by
  have hc : adj c.1 = -c.1 := c.2
  have h : incA D D.host.xi0 * pairS T x (x * c.1) =
      -((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) * c.1).trace := by
    rw [gramSkew_map, pairS, adj_mul, hc, Matrix.mul_assoc]
    exact mul_trace_neg _ _ _
  refine (d.symplOH_extX_extY T x _).trans ?_
  refine (congrArg (fun z => algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) z) h).trans ?_
  rw [LinearMap.map_neg, mul_neg]

theorem qT_eq (S : HSp D) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (c : skewA D ρ) (y : Mx D S.rank ρ) :
    d.qT S c y = -(algebraMap D.host.F (AF D.host.F) (1 / 2) *
      Algebra.trace (AF D.host.F) (AE D) ((incA D D.host.xi0⁻¹ • (adj y * (gA S * y))) * c.1).trace) := by
  have h1 : mt T (d.nC c)⁻¹ * d.jY = d.jY + d.jX * (-c.1) := by
    rw [d.nC_inv]; exact d.nC_jY (-c)
  have h2 : incA D (-D.host.xi0⁻¹) = -incA D D.host.xi0⁻¹ := RingHom.map_neg _ _
  have h : mt T (d.nC c)⁻¹ * d.incAdj S y - d.incAdj S y =
      d.incX S (incA D D.host.xi0⁻¹ • (c.1 * (adj y * gA S))) := by
    rw [HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incX_apply, h2]
    exact move_sub h1 _ _
  rw [HypDec.qT, h, symplOH_skew, symplOH, HypDec.symplO_incX_incAdj, trace_cycle_smul]

theorem central_gram : ∀ D : D7, (∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (∀ x : Mx D T.rank ρ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T (d.extX T x) * x = d.jY * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D)) ∧ ∀ (c : skewA D ρ) (x : Mx D T.rank ρ), d.qS T c x = -(algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) * c.1).trace)) ∧ ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (c : skewA D ρ) (y : Mx D S.rank ρ), d.qT S c y = -(algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((incA D D.host.xi0⁻¹ • (adj y * (gA S * y))) * c.1).trace) :=
  fun _ => ⟨fun _ _ T _ d => ⟨starAdj_extX_mul T d, qS_eq T d⟩, fun S _ _ _ d => qT_eq S d⟩

end GlobalTheory.CentralGram

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)


theorem _root_.GlobalTheory.T.norm_cmExtension_splitPlace_eq_zpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ∀ x : (Fv F v ⊗[F] E)ˣ, (absEv F E v x : ℝ) = (qV E w : ℝ) ^ (-(ordL (toCompl h x.1) + ordL (toCompl h' x.1))) := by
  first | exact @GlobalTheory.Doubling.AbsSplit.absEv_split | exact GlobalTheory.Doubling.AbsSplit.absEv_split | (intros; apply GlobalTheory.Doubling.AbsSplit.absEv_split <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.flatMap_fourierJacobi_factors_local_flat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ ≤ i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  first | exact @GlobalTheory.FlatFactor.flCol_factor | exact GlobalTheory.FlatFactor.flCol_factor | (intros; apply GlobalTheory.FlatFactor.flCol_factor <;> assumption)
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.howeSpan_families_of_places : ∀ (ι : Type) [Fintype ι], HoweSpan ι := by
  first | exact @GlobalTheory.KJInf.howeSpan_all | exact GlobalTheory.KJInf.howeSpan_all | (intros; apply GlobalTheory.KJInf.howeSpan_all <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.matrix_entry_finite_datum_bounded_level_size : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (p : ChPt (R := N.R) sel mu u i) (p' : ChPt (R := N.R) sel mu u (i + 1)), SmallDatum (Sall sel mu u) p.deco.1.N p'.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiEntry Ch sel mu cst I i al be p p') (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) := by
  first | exact @GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp | exact GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp | (intros; apply GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp <;> assumption)
end

section

noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.CuspGeo

section

variable (I : AutInst)

theorem hform_eq_dot {K : Type} [Field K] [StarRing K] {n : ℕ} (J : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) : Formalism.UG.hform (starRingEnd K) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_NInf_of_NA {W : Submodule I.E (Fin I.n → I.E)} {m : I.Ginf} (hm : ((m, 1) : I.GA) ∈ I.NA W) :
    m ∈ CompanionTheory.D.gk.RF.NInf I W := by
  intro v
  obtain ⟨h1, h2, h3⟩ := hm.1 v
  show CompanionTheory.D.gk.RF.Lowers (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v) (uMat (m v) - 1)
  have hdet := CompanionTheory.D.gk.RF.P_det I v
  have hPi : I.P v * (I.P v)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hiP : (I.P v)⁻¹ * I.P v = 1 := nonsing_inv_mul _ hdet
  have hB : ∀ z, (I.P v * uMat (m v) * (I.P v)⁻¹ - 1) *ᵥ (I.P v *ᵥ z) =
      I.P v *ᵥ ((uMat (m v) - 1) *ᵥ z) := fun z => by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc _ (I.P v)⁻¹ (I.P v), hiP,
      Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  have hWC : ∀ w ∈ CompanionTheory.D.gk.RF.Wv I W v, I.P v *ᵥ w ∈
      Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)) := fun w hw => by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      rw [CompanionTheory.D.gk.RF.P_atV]
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hWv : ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      (I.P v)⁻¹ *ᵥ x ∈ CompanionTheory.D.gk.RF.Wv I W v := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hfP : ∀ w z, CompanionTheory.D.gk.RF.hf (Formalism.REAL.Jm (I.ε v)) w z =
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) (I.P v *ᵥ w) (I.P v *ᵥ z) := fun w z => by
    rw [hform_eq_dot, CompanionTheory.D.gk.RF.hf, ← I.P_spec v, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
      mulVec_mulVec, Matrix.mul_assoc]
  have hc1 : ∀ z ∈ CompanionTheory.D.gk.RF.perp (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v),
      ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x (I.P v *ᵥ z) = 0 := fun z hz x hx => by
    have e : x = I.P v *ᵥ ((I.P v)⁻¹ *ᵥ x) := by rw [mulVec_mulVec, hPi, one_mulVec]
    rw [e, ← hfP]
    exact hz _ (hWv x hx)
  have hc2 : ∀ z, (∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x (I.P v *ᵥ z) = 0) →
      z ∈ CompanionTheory.D.gk.RF.perp (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v) := fun z h w hw => by
    rw [hfP]
    exact h _ (hWC w hw)
  have inj : ∀ a : Fin I.n → ℂ, a = (I.P v)⁻¹ *ᵥ (I.P v *ᵥ a) := fun a => by
    rw [mulVec_mulVec, hiP, one_mulVec]
  refine ⟨fun w hw => ?_, fun z hz => ?_, fun z => ?_⟩
  · have := h1 _ (hWC w hw)
    rw [hB] at this
    rw [inj ((uMat (m v) - 1) *ᵥ w), this, mulVec_zero]
  · have := h2 _ (hc1 z hz)
    rw [hB] at this
    rw [inj ((uMat (m v) - 1) *ᵥ z)]
    exact hWv _ this
  · refine hc2 _ fun x hx => ?_
    have := h3 (I.P v *ᵥ z)
    rw [hB] at this
    exact this x hx

theorem shortCusp_holds : ShortCusp I := by
  intro U hU
  obtain ⟨M, hM, hMU⟩ := CompanionTheory.D.gk.RF.congruence_subgroup_compact_open I U hU
  obtain ⟨s₁, hs₁, hSI⟩ := CompanionTheory.D.gk.RF.short_isotropic_vector_of CompanionTheory.D.gk.RF.transport_to_standard_form I
  obtain ⟨C₁, hC₁, hCS⟩ := CompanionTheory.D.gk.RF.covolume_span I
  obtain ⟨C₂, hC₂, hCP⟩ := CompanionTheory.D.gk.RF.covolume_orthogonal_complement CompanionTheory.D.gk.RF.transport_to_standard_form I
  obtain ⟨C₃, hC₃, hNC⟩ := CompanionTheory.D.gk.RF.nilpotent_cover_of CompanionTheory.D.gk.RF.transport_to_standard_form CompanionTheory.D.gk.RF.gamSub
    CompanionTheory.D.gk.RF.nilpotent_lie_algebra CompanionTheory.D.gk.RF.nilpotent_subgroup_representation I M hM
  set s₀ := min s₁ 1
  have hs₀ : 0 < s₀ := lt_min hs₁ one_pos
  have hD : 0 < 2 * (C₁ + C₂ + 1) := by positivity
  refine ⟨s₀, 1 / (2 * (C₁ + C₂ + 1)), C₃ * (C₁ + C₂), hs₀, by positivity, fun y η hη hηη₀ hc => ?_⟩
  have hηD : η * (2 * (C₁ + C₂ + 1)) ≤ 1 := (le_div_iff₀ hD).1 hηη₀
  have hη1 : η < 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  have hηb : (C₁ + C₂) * η ≤ 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  have hηa : 2 * C₁ * η ≤ 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  obtain ⟨u, hu, hu0, hus⟩ := hc
  have hc' : ∃ u ∈ CompanionTheory.D.gk.RF.IntV I, u ≠ 0 ∧ ‖CompanionTheory.D.gk.RF.vecAt I y u‖ ≤ s₀ * η ^ (I.n + 1) :=
    ⟨u, hu, hu0, hus⟩
  obtain ⟨t, ht, hts, d, w, hd, hw, hne, hall⟩ := CompanionTheory.D.gk.RF.successive_minima_gap I.E I.n (CompanionTheory.D.gk.RF.IntV I)
    (fun u => ‖CompanionTheory.D.gk.RF.vecAt I y u‖) s₀ η hs₀ hη hη1 hc'
  have ht1 : t ≤ 1 := hts.trans (min_le_right _ _)
  have hs : η * t ≤ s₁ := (mul_le_of_le_one_left ht.le hη1.le).trans (hts.trans (min_le_left _ _))
  have hI : CompanionTheory.D.gk.RF.Isot I.J (Submodule.span I.E (Set.range w)) := Submodule.span_le.2 (by
    rintro _ ⟨j, rfl⟩
    exact CompanionTheory.D.gk.RF.mem_perp_spanC fun i => hSI y _ (hw i).1 _ (hw j).1 ((hw i).2.trans hs) ((hw j).2.trans hs))
  have c1 := hCS y d w (η * t) hd (by positivity) hw
  have c2 := hCP y _ _ t ht (by nlinarith) c1 fun u hu hn => by
    by_contra h
    exact hn (hall u hu (not_le.1 h).le)
  have hρ : η * t * (C₁ * (η * t) + C₂ / t) ≤ (C₁ + C₂) * η := by
    have e : η * t * (C₁ * (η * t) + C₂ / t) = C₁ * η * (η * t * t) + C₂ * η := by field_simp
    have : η * t * t ≤ 1 := mul_le_one₀ (mul_le_one₀ hη1.le ht.le ht1) ht.le ht1
    have := mul_le_of_le_one_right (by positivity : 0 ≤ C₁ * η) this
    rw [e]; linarith
  refine ⟨Submodule.span I.E (Set.range w), ⟨hne, fun x hx z hz => ?_⟩, fun m hm => ?_⟩
  · have := hI hz x hx
    rw [hform_eq_dot]
    exact this
  obtain ⟨γ, h1, -, h3⟩ := hNC y d w (η * t) (C₁ * (η * t) + C₂ / t) hd (by positivity) (by positivity)
    (hρ.trans hηb) hw hI (c1.mono (le_add_of_nonneg_right (by positivity)))
    (c2.mono (le_add_of_nonneg_left (by positivity))) m (mem_NInf_of_NA I hm)
  obtain ⟨x, hxU, hx⟩ := hMU γ h1
  refine ⟨(γ, x), hx, hxU, fun v i j => (h3 v i j).trans ?_⟩
  rw [mul_assoc C₃]
  exact mul_le_mul_of_nonneg_left hρ hC₃.le

end

theorem shortCusp_all : ∀ I : AutInst, ShortCusp I := shortCusp_holds

end GlobalTheory.CuspGeo
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.PosOne.MidVertex

theorem exists_bilPos_mid : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (ρ₁ : Representation ℂ (GL (n₁ ⊕ Fin (c + 1)) k) (SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k))) (_ : IsSrc μ₂ ρ₁), ∃ b : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, BilPos ψ μ₁ ρ ρ₁ b ∧ (∀ Ψ (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), IsQuotInt ν m₂ G₂ ρ (tInt ψ ν μ₂ ρ σ (T Ψ) F Φ₂.1) (b Ψ Φ₂)) ∧ ∀ Ψ (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), IsQuotInt ν m₂ G₂ 1 (tIntOne ψ ν μ₂ ρ σ (T Ψ) F Φ₂.1) (toOne ν ρ₁ ρ (b Ψ) Φ₂) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hc ψ hψc hψ1 ν hsd μ₁ μ₂ hk₁ hk₂ m₁ _ G₁ _ m₂ hm₂ G₂ hG₂ A _ _ σ hσ T hT F ρ₁ hsrc
  haveI : ν.IsAddHaarMeasure := hsd.1
  have h1 : 1 ≤ ρ := by omega
  have h2 : ρ ≤ c := by omega
  have hR := fun Ψ => GlobalTheory.T.exists_linear_isQuotInt_tInt_alt k n₂ n₁ c ρ h1 h2 ψ hψc hψ1 ν μ₂ hk₂ m₂ G₂ A σ hσ (T Ψ) (hT.1 Ψ) F ρ₁ hsrc
  choose R hQ hN using hR
  have uniq : ∀ (f : GL (n₂ ⊕ Fin c) k → ℂ) (z z' : ℂ), IsQuotInt ν m₂ G₂ ρ f z → IsQuotInt ν m₂ G₂ ρ f z' → z = z' :=
    fun f z z' => (@GlobalTheory.QuotInt.quotInt_unique_exists k _ _ _ _ _ _ n₂ _ _ c ρ h1 h2 ν hsd.1 m₂ hm₂ G₂ hG₂ f).1 z z'
  have lin := fun f f' a z z' =>
    @GlobalTheory.RootEx.QuotLinear.isQuotInt_linear k _ _ _ _ _ _ n₂ _ _ c ρ h1 h2
      ν hsd.1 m₂ hm₂ G₂ hG₂ f f' a z z'
  have key : ∀ (a : ℂ) Ψ Ψ' Φ, R (a • Ψ + Ψ') Φ = a * R Ψ Φ + R Ψ' Φ := by
    intro a Ψ Ψ' Φ
    have h := lin _ _ a _ _ (hQ Ψ Φ) (hQ Ψ' Φ)
    have hf : (fun h => a * tInt ψ ν μ₂ ρ σ (T Ψ) F Φ.1 h + tInt ψ ν μ₂ ρ σ (T Ψ') F Φ.1 h) =
        tInt ψ ν μ₂ ρ σ (T (a • Ψ + Ψ')) F Φ.1 := by
      funext h
      simp only [tInt, app, map_add (f := _), map_smul]
      split_ifs <;> simp
    rw [hf] at h
    exact uniq _ _ _ (hQ _ Φ) h
  have hz : ∀ Φ, R 0 Φ = 0 := by
    intro Φ
    have := key 1 0 0 Φ
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  let b : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ :=
    { toFun := R
      map_add' := fun Ψ Ψ' => by
        ext Φ
        have := key 1 Ψ Ψ' Φ
        simpa using this
      map_smul' := fun a Ψ => by
        ext Φ
        have := key a Ψ 0 Φ
        simp only [add_zero] at this
        simp [this, hz] }
  refine ⟨b, ⟨fun Ψ => hN Ψ, ?_⟩, fun Ψ Φ₂ => hQ Ψ Φ₂, fun Ψ Φ₂ =>
    GlobalTheory.T.isQuotientInvariantIntegral_exchange_toPositionOne k n₂ n₁ c ρ h1 h2 ψ hψc hψ1 ν hsd μ₂ hk₂ m₂ G₂ A σ hσ (T Ψ) (hT.1 Ψ) F ρ₁ hsrc (R Ψ) (hQ Ψ) Φ₂⟩
  intro g Ψ Ψ₁ v hΨ
  show R Ψ₁ (ρ₁ (embX (c + 1) g) v) = _ * R Ψ v
  set s : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 2) / 2 - ρ) : ℝ) : ℂ) with hs
  have hexp : ((((c + 1 : ℕ) : ℝ) + 1) / 2 - (ρ : ℝ)) = ((c : ℝ) + 2) / 2 - ρ := by push_cast; ring
  rw [hexp]
  have hfun : tInt ψ ν μ₂ ρ σ (T Ψ₁) F (ρ₁ (embX (c + 1) g) v).1 =
      fun h => (s - 1) * tInt ψ ν μ₂ ρ σ (T Ψ) F v.1 h + tInt ψ ν μ₂ ρ σ (T Ψ) F v.1 h := by
    funext h
    have hv : ((ρ₁ (embX (c + 1) g) v : SB _) : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ) =
        om μ₂ (embX (c + 1) g) 1 v.1 := hsrc _ _
    have hcomm : om μ₂ 1 h (om μ₂ (embX (c + 1) g) 1 v.1) = om μ₂ (embX (c + 1) g) 1 (om μ₂ 1 h v.1) := by
      rw [← om_mul, ← om_mul, one_mul, mul_one, mul_one, one_mul]
    have hΦ' : om μ₂ 1 h v.1 ∈ SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) := om_mem_SB μ₂ 1 h v.2
    have hX := (GlobalTheory.RootEx.opE_SB_and_linear k n₂ n₁ c ρ ψ hψc ν).1 _ hΦ'
    have hE' := (GlobalTheory.RootEx.opE_om_embX k n₂ n₁ c ρ h1 h2 ψ ν μ₂ (om μ₂ 1 h v.1)).2 g
    have hX' : om μ₂ g 1 (opE ψ ν ρ (om μ₂ 1 h v.1)) ∈ SB (Matrix n₂ n₁ k) := om_mem_SB μ₂ g 1 hX
    have hinv := hT.2 g Ψ Ψ₁ ⟨_, hX⟩ ⟨_, hX'⟩ hΨ rfl
    simp only [tInt]
    rw [hv, hcomm, hE']
    have e1 : ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 2) / 2 - ρ) : ℝ) : ℂ) •
        om μ₂ g 1 (opE ψ ν ρ (om μ₂ 1 h v.1)) = ((s • (⟨_, hX'⟩ : SB (Matrix n₂ n₁ k)) : SB _) : Matrix n₂ n₁ k → ℂ) := by
      rfl
    have e2 : app (T Ψ) (opE ψ ν ρ (om μ₂ 1 h v.1)) = T Ψ ⟨_, hX⟩ := GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe _ ⟨_, hX⟩
    rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe, e2, map_smul, hinv]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    ring
  have h := lin _ _ (s - 1) _ _ (hQ Ψ v) (hQ Ψ v)
  rw [← hfun] at h
  rw [uniq _ _ _ (hQ Ψ₁ _) h]
  ring

end GlobalTheory.PosOne.MidVertex
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)



theorem GlobalTheory.PosOne.quotInt_one_comb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (e : GL (n' ⊕ Fin (c + 1)) k →₀ ℂ) (_ : SrcComb ψ ν P ρ' Φ e) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ P σ B) (F : A) (z : GL (n' ⊕ Fin (c + 1)) k → ℂ), (∀ g ∈ e.support, IsQuotInt ν μX μG P (tInt ψ ν μ P σ B F (om μ g 1 Φ.1)) (z g)) → IsQuotInt ν μX μG 1 (tIntOne ψ ν μ P σ B F Φ.1) (comb e z) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP hPc ψ hψ hψ1 ν hν μ hμ μX hμX μG hμG ρ' hρ' Φ e he A _ _ σ hσ B hB F z hz
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨Rr, hRr, hRrN⟩ := GlobalTheory.T.exists_linear_isQuotInt_tInt_alt k n n' c P hP hPc ψ hψ hψ1 ν μ hμ μX μG A σ hσ B hB F ρ' hρ'
  have hone := GlobalTheory.T.isQuotientInvariantIntegral_exchange_toPositionOne k n n' c P hP hPc ψ hψ hψ1 ν hν μ hμ μX μG A σ hσ B hB F ρ' hρ' Rr hRr Φ
  have hcomb : toOne ν ρ' P Rr Φ = comb e fun g => Rr (ρ' g Φ) := he Rr hRrN
  have heq : comb e z = comb e fun g => Rr (ρ' g Φ) := by
    unfold comb
    refine Finsupp.sum_congr fun g hg => ?_
    congr 1
    have h1 := hRr (ρ' g Φ)
    rw [hρ' g Φ] at h1
    exact ((@GlobalTheory.QuotInt.quotInt_unique_exists k _ _ _ _ _ _ n _ _ c P hP hPc ν hν.1 μX hμX μG hμG _).1 _ _ (hz g hg) h1)
  rw [heq, ← hcomb]
  exact hone
end

section

open Matrix
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.smoothVectors_of_lie_closed_family : ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : Type) (v : ι → H) (δ : Matrix (Fin n) (Fin n) ℂ → ι → ι), Hm.det ≠ 0 → Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → (∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i)) → (∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) → (∀ X, Xᴴ * Hm + Hm * X = 0 → ∀ i, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (v i)) (v (δ X i)) 0) → ∀ i, Formalism.L2.Theta.SmoothVec {X | Xᴴ * Hm + Hm * X = 0} σ (v i) := by
  first | exact @GlobalTheory.SmoothCrit.smoothVec_of_closed_family | exact GlobalTheory.SmoothCrit.smoothVec_of_closed_family | (intros; apply GlobalTheory.SmoothCrit.smoothVec_of_closed_family <;> assumption)
end
