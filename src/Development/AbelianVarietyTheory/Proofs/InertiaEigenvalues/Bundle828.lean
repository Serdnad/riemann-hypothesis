module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.AlgebraicWeights.InertDatumExists
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle076
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle078
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle818
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle605
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle776
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle820
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle821
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle721
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle082
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle620
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle076
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle773
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle651
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle556
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle822
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.exists_canonical_inert_tensor_completion_equiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∃ e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L, (∀ x, e (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) x) = Dv.σw (e x)) ∧ (∀ x, x ∈ Formalism.UG.tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ↔ e x ∈ Formalism.UG.intL (w.adicCompletion L)) ∧ ∀ z : AL L, e (compAt L v z) = F.κ z w := by
  first | exact @GlobalTheory.InertTransferCanon.exists_canonical_equiv | exact GlobalTheory.InertTransferCanon.exists_canonical_equiv | (intros; apply GlobalTheory.InertTransferCanon.exists_canonical_equiv <;> assumption)
end

section

set_option autoImplicit false


noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjExpand

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}



theorem read_of_isBC (M : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c M.lev2)
    (cc : (C.U ((i : ℕ) + 1) M.s0).Comp → ℂ) (L : ℂ) (z : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n m : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) M.c'} (hf : f ∈ sec _ M.c' a n) {as : Fin m → M.c'.F}
    {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c} (hfs : ∀ k, fs k ∈ sec _ C.Q.c a n) (h : IsBC M.hle f as fs)
    (g : GA D (Wc D i)) :
    cc (M.dict g).1 * L * M.mu g * rdU (unfBC M.hle (C.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2 =
      ∑ k, (as k : ℂ) * (L * M.phi cc (actLev C.Q.c M.lev2 z (fs k)) g) := by
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ M.hle _ _ hact).2 a n z m as fs f hf hfs h
  have h2 := congrFun (congrFun (rdU_unfBC M.hle (C.U ((i : ℕ) + 1)) (inC M.c') h1) (M.dict g).1) (M.dict g).2
  rw [Finset.sum_apply, Finset.sum_apply] at h2
  refine (congrArg (fun w => cc (M.dict g).1 * L * M.mu g * w) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * L * M.mu _ * ((as k : ℂ) * _) = (as k : ℂ) * (L * (cc _ * M.mu _ * _))
  ring

end GlobalTheory.ConjExpand



theorem GlobalTheory.ConjExpand.conjFun_galRul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (z : G), ∀ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) M.c' (unfBC M.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) → ConjFun M (κ i) τ 1 (fun g => T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2) (fun g => T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z (galRul hf f)) (M.dict g).1 (M.dict g).2) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup M hP τ ta hta hB hf z f hfc hE
  have hact := hP.act.1
  obtain ⟨ht⟩ := id hT
  have hn : (κ i).n = (Vc D i).rank :=
    (ht.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ M.hle).2 _ (T.U ((i : ℕ) + 1)) _ _ f hfc
  have hsec := ((mem_cusp _ _ _ _ _ _).1 hfc).1
  have hs : ∀ k, fs k ∈ sec _ T.Q.c (wtA (κ i)) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have hgal := GlobalTheory.GalTw.galRul_sec_val_semilinear _ _ (T.Q.Dw ((i : ℕ) + 1)) _ (T.Q.Xo ((i : ℕ) + 1)) M.c' ta hf
  have hFix : ∀ x : T.Q.c.F, ta (incF T.Q.c M.c' M.hle x) = incF T.Q.c M.c' M.hle x := by
    intro x
    apply Subtype.ext
    rw [hta]
    exact hB.core x
  have hgsec := ((hgal.1 _ _ f hsec).1)
  have hgBC := hgal.2.2 T.Q.c M.hle hFix _ _ m as fs f hsec hBC
  have hkeep : ∀ k, actLev T.Q.c M.lev2 z (fs k) ∈ T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := by
    intro k
    obtain ⟨y, hy, -⟩ := hP.lift.lev z
    refine (hE z y hy (fs k) ?_).1
    rw [hn]
    exact hfs k
  obtain ⟨Fk, hFk⟩ : ∃ Fk : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ∀ k, (Fk k : T.toCore.R ((i : ℕ) + 1)) = actLev T.Q.c M.lev2 z (fs k) := ⟨fun k => ⟨_, hkeep k⟩, fun _ => rfl⟩
  have e1 := fun g => GlobalTheory.ConjExpand.read_of_isBC M hact (T.cE ((i : ℕ) + 1) M.s0) (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) z hsec hs hBC g
  have e2 := fun g => GlobalTheory.ConjExpand.read_of_isBC M hact (T.cE ((i : ℕ) + 1) M.s0) (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) z hgsec hs hgBC g
  simp only [← hFk] at e1 e2
  refine ⟨⟨m, fun k => (as k : ℂ), Fk, fun g => e1 g⟩, ?_⟩
  intro n a h hex g
  have hz : Expands M (κ i) (fun _ => 0) (Fin.append a (fun k => -(as k : ℂ))) (Fin.append h Fk) := by
    intro g
    have h0 := (e1 g).symm.trans (hex g)
    show (0 : ℂ) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    linear_combination h0
  have hz' : (0 : ℂ) = _ := GlobalTheory.T.cuspForm_linear_relation_defined_over_core_field D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup M hP τ hB.core _ _ _ hz g
  rw [Fin.sum_univ_add] at hz'
  simp only [Fin.append_left, Fin.append_right, map_neg, neg_mul, Finset.sum_neg_distrib] at hz'
  refine (e2 g).trans ?_
  simp only [one_mul, hta]
  linear_combination hz'
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

theorem GlobalTheory.MapSmul.mapSmul {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (a : R) (M : Matrix m n R) :
    (a • M).map f = f a • M.map f := by
  ext i j; simp


open GlobalTheory.MapSmul in
theorem GlobalTheory.BKLim.adaptedBasis_theta_and_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ (g : ↥(GK K)) (z : ℂ_[l]), IsZ bk g z → ∃ u : Matrix (Fin d) (Fin d) (ℂ_[l]), u * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * (F.ε g).map ((Per.θD l).comp (aDp l)) ∧ u * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal fun i => z ^ ((H.p i : ℤ) - H.q)) ∧ ∀ N₀ : ℕ, N₀ ≤ N → (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → (∀ i j, bk.E ^ (N - N₀) ∣ F.A i j) ∧ ∀ i j, bk.E ^ (N - N₀) ∣ F.A' i j := by
  intro l _ K bk τ hτ C hC N d ρ F Y hDR hY H
  have hdom := GlobalTheory.MemLoc.BdRField.bdR_isField l
  haveI : IsDomain (Per.BdRp l) := hdom.1
  have hι : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := hdom.2.1
  obtain ⟨B, Q, hBu, hQu, hBl, hQ, hQi⟩ := GlobalTheory.T.exists_invariant_basis_deRham_breuilKisin l K bk τ hτ C N d ρ F Y hDR hY
  obtain ⟨Y₁, Y', hY₁, hYY'⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d ρ F.toPre
  have hinj : Function.Injective (inclW l) := WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))
  have hY1 : Y₁ = Y := Matrix.ext fun i j => hinj (by simpa using congrFun (congrFun (hY₁.trans hY.symm) i) j)
  rw [hY1] at hYY'
  obtain ⟨c, c', hc, hc', hcc', hQH⟩ := GlobalTheory.T.hodgeAdaptedBasis_invariant_matrix_ratio l K bk C hC d ρ Q hQu hQi H
  have hθt : Per.θD l (aDp l τ) ≠ 0 := by simpa using GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ 1
  have htu : IsUnit (aDp l τ) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ hθt
  obtain ⟨u, hu⟩ := htu
  have hYY'd : Y.map (aDp l) * Y'.map (aDp l) = aDp l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l)) := by
    rw [← Matrix.map_mul, hYY', mapSmul, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  have hY'Yd : Y'.map (aDp l) * Y.map (aDp l) = aDp l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l)) := by
    have h1 : ((↑u⁻¹ : Per.BdRp l) ^ (2 * N) • Y.map (aDp l)) * Y'.map (aDp l) = 1 := by
      rw [Matrix.smul_mul, hYY'd, smul_smul, ← hu, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have h2 := mul_eq_one_comm.1 h1
    rw [Matrix.mul_smul] at h2
    calc Y'.map (aDp l) * Y.map (aDp l) = (aDp l τ ^ (2 * N)) • ((↑u⁻¹ : Per.BdRp l) ^ (2 * N) • (Y'.map (aDp l) * Y.map (aDp l))) := by
          rw [smul_smul, ← hu, ← mul_pow, Units.mul_inv, one_pow, one_smul]
      _ = _ := by rw [h2]

  have hstar : aDp l (bk.ev bk.E) ^ H.q • (Y.map (aDp l) * (F.A.map bk.ev).map (aDp l) * B * c.map C.o) =
      (aDp l (bk.ev bk.E) * aDp l τ) ^ N • (H.V * Matrix.diagonal (fun j => aDp l (bk.ev bk.E) ^ H.p j)) := by
    refine GlobalTheory.T.transport_matrix_identity_injective_ringHom (algebraMap (Per.BdRp l) (Per.BdR l)) hι d N H.q H.p _ _ Q H.Q _ B _ H.V ?_ H.Q_eq ?_
    · rw [← Matrix.map_mul, ← map_mul]; exact hQ
    · rw [hQH]; rfl

  set V₀ : Matrix (Fin d) (Fin d) (Per.BdRp l) := (↑u⁻¹ : Per.BdRp l) ^ N • (Y'.map (aDp l) * H.V) with hV₀
  have h1 : Y.map (aDp l) * V₀ = aDp l τ ^ N • H.V := by
    rw [hV₀, Matrix.mul_smul, ← Matrix.mul_assoc, hYY'd, Matrix.smul_mul, Matrix.one_mul, smul_smul, ← hu]
    congr 1
    rw [two_mul, pow_add, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  have hY'V : Y'.map (aDp l) * H.V = aDp l τ ^ N • V₀ := by
    rw [hV₀, smul_smul, ← hu, ← mul_pow, Units.mul_inv, one_pow, one_smul]
  have h2 : aDp l (bk.ev bk.E) ^ H.q • ((F.A.map bk.ev).map (aDp l) * B * c.map C.o) =
      aDp l (bk.ev bk.E) ^ N • (V₀ * Matrix.diagonal (fun j => aDp l (bk.ev bk.E) ^ H.p j)) := by
    have e := congrArg (fun M => Y'.map (aDp l) * M) hstar
    simp only [Matrix.mul_smul] at e
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hY'Yd, ← Matrix.mul_assoc, hY'V] at e
    simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul] at e
    have hu2 : IsUnit (aDp l τ ^ (2 * N)) := by rw [← hu]; exact (Units.isUnit u).pow _
    apply (hu2.smul_left_cancel).1
    rw [smul_smul, smul_smul, mul_comm, e, mul_pow, two_mul, pow_add]
    congr 1
    ring

  have h4 : ∀ (g : ↥(GK K)) (i j : Fin d), Per.σC (g : GQ l) (Per.θD l (V₀ i j)) = Per.θD l (V₀ i j) := by
    intro g i j
    obtain ⟨k, s, hs⟩ := GlobalTheory.T.approx_bdRPlus_fil_matrix_mul l K bk (N + H.p j + 1) d ((F.A.map bk.ev).map (aDp l) * B) (c.map C.o)
      (GlobalTheory.T.approx_bdRPlus_fil_matrix_mul l K bk (N + H.p j + 1) d ((F.A.map bk.ev).map (aDp l)) B
        ⟨0, F.A, fun i j => by rw [pow_zero, one_mul, Matrix.map_apply, Matrix.map_apply, sub_self]; exact zero_mem _⟩
        (hBl (N + H.p j + 1)))
      (GlobalTheory.T.exists_wittPowerSeries_approx_matrix_bdRPlus l K bk C d c hc (N + H.p j + 1))
    refine GlobalTheory.T.theta_galois_fixed_of_congr_breuilKisin l K bk (V₀ i j) (N + H.p j) k (bk.E ^ H.q * s i j) ?_ g
    have e := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul] at e
    have hm := Ideal.mul_mem_left _ (-(aDp l (bk.ev bk.E) ^ H.q)) (hs i j)
    have key : (l : Per.BdRp l) ^ k * aDp l (bk.ev bk.E) ^ (N + H.p j) * V₀ i j - aDp l (bk.ev (bk.E ^ H.q * s i j)) =
        -(aDp l (bk.ev bk.E) ^ H.q) * (aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * ((F.A.map bk.ev).map (aDp l) * B * c.map C.o) i j) := by
      rw [map_mul, map_mul, map_pow, map_pow]
      linear_combination -((l : Per.BdRp l) ^ k) * e
    rw [key]
    exact hm
  refine ⟨fun g z hz => ?_, fun N₀ hN₀ hp => ?_⟩
  · obtain ⟨w, hw, hzw⟩ := hz
    have hG1 := GlobalTheory.T.galois_tauPow_frame_ainf l K bk τ N d ρ F Y hY g
    have hG2 := GlobalTheory.T.hodgeAdaptedBasis_galois_action_bdRPlus l K bk C d ρ H g w hw
    have hb : Per.θD l (aDp l (Per.σA (g : GQ l) τ)) ≠ 0 := by
      rw [← GlobalTheory.MemLoc.ActLaws.σDp_aDp, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.2]
      intro h0
      exact hθt ((Per.σC (g : GQ l)).injective (h0.trans (map_zero _).symm))
    refine GlobalTheory.T.hodgeTate_operator_of_galois_relations d N H.q H.p (Per.θD l (aDp l τ)) (Per.θD l (aDp l (Per.σA (g : GQ l) τ))) z (Per.θD l (aDp l w))
      _ (Y'.map ((Per.θD l).comp (aDp l))) _ (V₀.map (Per.θD l)) _ (((ρ g).map ((aDp l).comp (Per.zA l))).map (Per.θD l))
      ((Y.map (Per.σA (g : GQ l))).map ((Per.θD l).comp (aDp l))) ((H.V.map (Per.σDp (g : GQ l))).map (Per.θD l))
      hθt hb hzw ?_ ?_ ?_ ?_ ?_
    · rw [← Matrix.map_mul, hYY', mapSmul, Matrix.map_one _ (map_zero _) (map_one _), map_pow]; rfl
    · rw [show Y.map ((Per.θD l).comp (aDp l)) = (Y.map (aDp l)).map (Per.θD l) from (Matrix.map_map).symm,
        ← Matrix.map_mul, h1, mapSmul, map_pow]
    · have e := congrArg (fun M => M.map ((Per.θD l).comp (aDp l))) hG1
      simp only [mapSmul, Matrix.map_mul, map_pow] at e
      have hr : ((ρ g).map ((aDp l).comp (Per.zA l))).map (Per.θD l) = ((ρ g).map (Per.zA l)).map ((Per.θD l).comp (aDp l)) := by
        ext i j; simp
      rw [hr]
      simpa only [RingHom.comp_apply] using e
    · have e := congrArg (fun M => M.map (Per.θD l)) hG2
      simp only [mapSmul, Matrix.map_mul, map_pow] at e
      rw [← e, Matrix.diagonal_map (map_zero _)]
      simp [Function.comp_def]
    · have e := congrArg (fun M => (M.map (Per.σDp (g : GQ l))).map (Per.θD l)) h1
      simp only [mapSmul, Matrix.map_mul, map_pow] at e
      have e1 : ((Y.map (aDp l)).map (Per.σDp (g : GQ l))).map (Per.θD l) = (Y.map (Per.σA (g : GQ l))).map ((Per.θD l).comp (aDp l)) := by
        ext i j; simp [GlobalTheory.MemLoc.ActLaws.σDp_aDp]
      have e2 : (V₀.map (Per.σDp (g : GQ l))).map (Per.θD l) = V₀.map (Per.θD l) := by
        ext i j; simp only [Matrix.map_apply]; rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.2, h4]
      rw [e1, e2, GlobalTheory.MemLoc.ActLaws.σDp_aDp] at e
      exact e
  · obtain ⟨B', hBB'⟩ := hBu.exists_right_inv
    obtain ⟨Vu, hVu⟩ := H.unit
    have hcp : c.map C.o * c'.map C.o = 1 := by
      rw [← Matrix.map_mul, hcc', Matrix.map_one _ (map_zero _) (map_one _)]
    have hVV : H.V * (↑Vu⁻¹ : Matrix (Fin d) (Fin d) (Per.BdRp l)) = 1 := by rw [← hVu]; exact Vu.mul_inv
    have hV₀' : V₀ * ((↑u⁻¹ : Per.BdRp l) ^ N • ((↑Vu⁻¹ : Matrix (Fin d) (Fin d) (Per.BdRp l)) * Y.map (aDp l))) = 1 := by
      calc V₀ * ((↑u⁻¹ : Per.BdRp l) ^ N • ((↑Vu⁻¹ : Matrix (Fin d) (Fin d) (Per.BdRp l)) * Y.map (aDp l)))
          = ((↑u⁻¹ : Per.BdRp l) ^ N * (↑u⁻¹ : Per.BdRp l) ^ N) • (Y'.map (aDp l) * (H.V * (↑Vu⁻¹ : Matrix (Fin d) (Fin d) (Per.BdRp l))) * Y.map (aDp l)) := by
            rw [hV₀, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; simp only [Matrix.mul_assoc]
        _ = ((↑u⁻¹ : Per.BdRp l) ^ N * (↑u⁻¹ : Per.BdRp l) ^ N) • (Y'.map (aDp l) * Y.map (aDp l)) := by rw [hVV, Matrix.mul_one]
        _ = 1 := by
            rw [hY'Yd, smul_smul, ← hu, ← pow_add, ← two_mul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have hAA' : (F.A.map bk.ev).map (aDp l) * (F.A'.map bk.ev).map (aDp l) =
        aDp l (bk.ev bk.E) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l)) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, F.A_mul, mapSmul, mapSmul, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.map_one _ (map_zero _) (map_one _), map_pow, map_pow]
    obtain ⟨hne, htr⟩ := GlobalTheory.T.eisenstein_pow_dvd_of_bdRPlus_dvd l K bk
    obtain ⟨hdA, hdA'⟩ := GlobalTheory.T.pow_dvd_entries_of_mul_eq_diagonal_pow d N N₀ H.q H.p (aDp l (bk.ev bk.E)) _ _ B B' _ _ V₀ _ hne hBB' hcp hV₀' hAA' h2 hN₀ hp
    exact ⟨fun i j => htr _ _ (by simpa using hdA i j), fun i j => htr _ _ (by simpa using hdA' i j)⟩

end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.StratCrys

theorem exists_semiBC {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M]
    [Module A M] : ∃ (P : Type) (_ : AddCommGroup P) (_ : Module B P) (u : M →ₛₗ[f] P), SemiBC u := by
  letI := f.toAlgebra
  let u : M →ₛₗ[algebraMap A B] (B ⊗[A] M) :=
    { toFun := fun x => 1 ⊗ₜ x
      map_add' := fun x y => TensorProduct.tmul_add _ _ _
      map_smul' := fun a x => by rw [algebraMap_smul, TensorProduct.tmul_smul] }
  exact ⟨B ⊗[A] M, inferInstance, inferInstance, u,
    (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange A B M (B ⊗[A] M) u (TensorProduct.mk A B M 1) fun _ => rfl).2
      (TensorProduct.isBaseChange A M B)⟩

theorem bijective_of_semiBC {A M N : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (u : M →ₗ[A] N) (h : SemiBC u) : Function.Bijective u := by
  obtain ⟨w, hw, -⟩ := h M LinearMap.id
  have h2 : u.comp w = LinearMap.id := h.hom_ext fun x => congrArg u (hw x)
  exact ⟨Function.LeftInverse.injective (g := w) hw, fun y => ⟨w y, LinearMap.congr_fun h2 y⟩⟩

def fracMap {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {φ : A →+* A} (t : A) (a : ℕ)
    (Ψ : N →ₛₗ[φ] N) :
    N →ₛₗ[(algebraMap A (Localization.Away t)).comp φ] LocalizedModule (Submonoid.powers t) N where
  toFun x := LocalizedModule.mk (Ψ x) ⟨t ^ a, (Submonoid.mem_powers_iff _ _).2 ⟨a, rfl⟩⟩
  map_add' x y := by
    rw [map_add (f := _), LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]
  map_smul' c x := by
    rw [Ψ.map_smulₛₗ, RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk]

theorem isFrac_fracMap {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {φ : A →+* A} (t : A) (a : ℕ)
    (Ψ : N →ₛₗ[φ] N) (x : N) : IsFrac t (fracMap t a Ψ x) (Ψ x) a := rfl

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d}

theorem eval_ext {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N) {x y : N}
    (h : ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), V.v a g x = V.v a g y) : x = y := by
  obtain ⟨C, c, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  exact (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B C N V c f hc).1 (h C c f)

theorem v_id_bijective {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) : Function.Bijective (V.v (Hom.id B) f) :=
  bijective_of_semiBC (A := B.A) (V.v (Hom.id B) f) (V.bc (Hom.id B) f)

theorem semiBC_fracMap {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (t : B.A) (ht : t ∈ B.I) (Ψ : N →ₛₗ[B.D.φ] N) (hΨ : IsPsi V t Ψ) : SemiBC (fracMap t S.a Ψ) := by
  obtain ⟨P, _, _, u, hu⟩ := exists_semiBC B.D.φ N
  obtain ⟨L, hL, -⟩ := hu N Ψ
  obtain ⟨n, h1, h2⟩ := GlobalTheory.T.linearizedFrobenius_invertible_up_to_pow l K bk d S B N V t ht Ψ hΨ P u hu L hL
  exact GlobalTheory.T.isSemilinearBaseChange_localized_of_torsion_bounded B.A B.D.φ t N P u hu L n S.a h1 h2 _ fun x => by
    rw [hL]; exact isFrac_fracMap _ _ _ _


variable (S) in
theorem exists_crys : ∃ (M : FCrys l ↥(OL K)) (V : ∀ B, Eval S B (M.M B)),
    (∀ (B B' Q : Obj l ↥(OL K)) (k : Hom B B') (a : Hom B' Q) (g : Hom bk.prism Q) (x : M.M B),
      (V B').v a g (M.tr k x) = (V B).v (a.comp k) g x) ∧
    ∀ (B : Obj l ↥(OL K)) (t : ↥B.I), ∃ Ψ : M.M B →ₛₗ[B.D.φ] M.M B, IsPsi (V B) t Ψ ∧
      ∀ x, IsFrac (t : B.A) (M.Φ B t x) (Ψ x) S.a := by
  choose N acg mod hV using GlobalTheory.T.exists_stratifiedPhiModuleValue l K bk d S
  have V : ∀ B, Eval S B (N B) := fun B => (hV B).some
  choose tr trbc htr using fun (B B' : Obj l ↥(OL K)) (k : Hom B B') =>
    GlobalTheory.T.exists_stratifiedValue_transition_baseChange l K bk d S B B' (N B) (N B') (V B) (V B') k
  choose Ψ hΨ using fun (B : Obj l ↥(OL K)) (t : ↥B.I) =>
    GlobalTheory.T.exists_frobenius_on_stratifiedValue l K bk d S B (N B) (V B) t t.2
  let M : FCrys l ↥(OL K) :=
    { M := N
      acg := acg
      mod := mod
      fin := fun B => (V B).fin
      proj := fun B => (V B).proj
      tr := fun k => tr _ _ k
      tr_bc := fun k => trbc _ _ k
      tr_id := fun B x => eval_ext (V B) fun Q a g => htr _ _ _ Q a g x
      tr_comp := fun {B B' B''} k' k x => eval_ext (V B'') fun Q a g =>
        (htr _ _ (k'.comp k) Q a g x).trans
          ((htr _ _ k' Q a g _).trans (htr _ _ k Q (a.comp k') g x)).symm
      Φ := fun B t => fracMap (t : B.A) S.a (Ψ B t)
      Φ_bc := fun B t => semiBC_fracMap (V B) t t.2 _ (hΨ B t)
      Φ_nat := fun {B B'} k t t' x m i n j h1 h2 =>
        GlobalTheory.T.isLocalizedFraction_semilinear_transition B.A B'.A k.f (N B) (N B') (tr _ _ k) t t' S.a _ _ _ m _ n i j
          (isFrac_fracMap _ _ _ _) h1 (isFrac_fracMap _ _ _ _) h2
          (GlobalTheory.T.stratifiedValue_frobenius_comm_transition l K bk d S B B' (N B) (N B') (V B) (V B') k (tr _ _ k) (htr _ _ k) t t' _ _
            (hΨ B t) (hΨ B' t') x) }
  exact ⟨M, V, fun B B' Q k a g x => htr _ _ k Q a g x, fun B t => ⟨Ψ B t, hΨ B t, fun _ => rfl⟩⟩

theorem map_single {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (j i : Fin d) :
    f ((Pi.single j 1 : Fin d → A) i) = (Pi.single j 1 : Fin d → B) i := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem sum_single {A : Type} [CommRing A] (c : Fin d → A) :
    ∑ i, c i • (Pi.single i 1 : Fin d → A) = c := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem exists_basis {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) : ∃ e : Module.Basis (Fin d) B.A N, ∀ j, V.v (Hom.id B) f (e j) = Pi.single j 1 := by
  let w : N →ₗ[B.A] (Fin d → B.A) := V.v (Hom.id B) f
  let q : N ≃ₗ[B.A] (Fin d → B.A) := LinearEquiv.ofBijective w (v_id_bijective V f)
  refine ⟨(Pi.basisFun _ _).map q.symm, fun j => ?_⟩
  change q _ = _
  simp

theorem eq_sum_of_coord {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) (e : Fin d → N) (he : ∀ j, V.v (Hom.id B) f (e j) = Pi.single j 1) (x : N)
    (c : Fin d → B.A) (h : V.v (Hom.id B) f x = c) : x = ∑ i, c i • e i := by
  apply (v_id_bijective V f).1
  let w : N →ₗ[B.A] (Fin d → B.A) := V.v (Hom.id B) f
  have he' : ∀ j, w (e j) = Pi.single j 1 := he
  change _ = w _

  rw [h, map_sum]
  simp only [map_smul, he']
  exact (sum_single c).symm

theorem coord_psi {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) (t : B.A) (ht : t = BK.hf f bk.E) (Ψ : N →ₛₗ[B.D.φ] N) (hΨ : IsPsi V t Ψ) (x : N)
    (j : Fin d) (hx : V.v (Hom.id B) f x = Pi.single j 1) :
    V.v (Hom.id B) f (Ψ x) = fun i => BK.hf f (S.A i j) := by
  have h1 := hΨ (Hom.id B) f x
  rw [hx, funext (map_single B.D.φ j), Matrix.mulVec_single_one] at h1
  subst ht
  ext i
  exact (mul_cancel_left_mem_nonZeroDivisors (pow_mem (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk B f).2 S.a)).1 (congrFun h1 i)

theorem exists_framed (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) :
    ∃ (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e := by
  obtain ⟨M, V, htr, hΦ⟩ := exists_crys S
  obtain ⟨e, he⟩ := exists_basis (V bk.prism) (Hom.id _)
  have he' : ∀ {B : Obj l ↥(OL K)} (g : Hom bk.prism B) j, (V bk.prism).v g g (e j) = Pi.single j 1 :=
    fun g j => by
      ext i
      have := (V bk.prism).v_nat g (Hom.id _) (Hom.id _) (e j) i
      rw [he, map_single] at this
      exact this
  refine ⟨M, e, ⟨fun {B} f g j => ?_, fun j => ?_⟩⟩
  · have h1 : ∀ (g : Hom bk.prism B) x, (V B).v (Hom.id B) f (M.tr g x) = (V bk.prism).v g f x :=
      fun g x => htr _ _ B g (Hom.id B) f x
    refine eq_sum_of_coord (V B) f (fun i => M.tr f (e i)) (fun i => (h1 f _).trans (he' f i)) _
      (fun i => S.ε f g i j) ?_
    rw [h1, (V _).v_ε g f g, he', Matrix.mulVec_single_one]
    rfl
  · have h0 : ∀ x, BK.hf (Hom.id bk.prism) x = bk.toP x := fun _ => rfl
    have ht : bk.toP bk.E ∈ bk.prism.I := by
      rw [(GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk bk.prism (Hom.id _)).1, h0]
      exact Ideal.mem_span_singleton_self _
    have hh := hΦ bk.prism ⟨bk.toP bk.E, ht⟩
    obtain ⟨Ψ, hΨ, h⟩ := hh
    have h1 := coord_psi (V _) (Hom.id _) _ (h0 _).symm Ψ hΨ _ j (he j)
    have h2 := eq_sum_of_coord (V _) (Hom.id _) e he _ _ h1
    simp only [h0] at h2
    exact Eq.mp (congrArg (fun m => IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, ht⟩ (e j)) m S.a) h2)
      (h (e j))

end GlobalTheory.BSP.StratCrys
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistablePeriod_pow_dvd_by_basis_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∃ (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  first | exact @GlobalTheory.BKLim.WHeightSprime.main | exact GlobalTheory.BKLim.WHeightSprime.main | (intros; apply GlobalTheory.BKLim.WHeightSprime.main <;> assumption)
end
