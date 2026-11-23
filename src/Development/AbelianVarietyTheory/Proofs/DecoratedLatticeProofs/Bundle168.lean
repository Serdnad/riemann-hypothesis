module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle151
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle135
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle150
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle153
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.discreteSeriesTestData_of_noncompactGaps : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  first | exact @GlobalTheory.Core.Mi.seeData_of_gap | exact GlobalTheory.Core.Mi.seeData_of_gap | (intros; apply GlobalTheory.Core.Mi.seeData_of_gap <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ThetaSplitApprox

theorem exists_slices {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y]
    (F : X × Y → ℂ) (hF : Continuous F) {C : Set X} {K : Set Y} (hC : IsCompact C) (hK : IsCompact K) {ε : ℝ}
    (hε : 0 < ε) : ∃ (n : ℕ) (a : Fin n → X) (π : Fin n → C(X, ℝ)),
      ∀ x ∈ C, ∀ y ∈ K, ‖F (x, y) - ∑ i, (π i x : ℂ) * F (a i, y)‖ ≤ ε := by
  have hV : ∀ a : X, ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, ∀ y ∈ K, ‖F (x, y) - F (a, y)‖ < ε := by
    intro a
    have hn : IsOpen {p : X × Y | ‖F p - F (a, p.2)‖ < ε} :=
      isOpen_lt (hF.sub (hF.comp (continuous_const.prodMk continuous_snd))).norm continuous_const
    obtain ⟨u, v, hu, -, hau, hKv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := a)) hK hn (by
      rintro ⟨x, y⟩ ⟨hx, -⟩
      obtain rfl : x = a := hx
      simpa using hε)
    exact ⟨u, hu, hau rfl, fun x hx y hy => @huv (x, y) ⟨hx, hKv hy⟩⟩
  choose V hVo hVm hVε using hV
  obtain ⟨t, -, hcov⟩ := hC.elim_nhds_subcover V fun x _ => (hVo x).mem_nhds (hVm x)
  have hcov' : C ⊆ ⋃ i : Fin t.card, V (t.equivFin.symm i) := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 (hcov hz)
    exact Set.mem_iUnion.2 ⟨t.equivFin ⟨x, hx⟩, by simpa using hzx⟩
  obtain ⟨π, hπs, hπ1, hπ01, -⟩ := exists_continuous_sum_one_of_isOpen_isCompact (fun i => hVo _) hC hcov'
  refine ⟨t.card, fun i => t.equivFin.symm i, π, fun x hx y hy => ?_⟩
  have h1 : ∑ i, π i x = 1 := by simpa using hπ1 hx
  have h2 : F (x, y) - ∑ i, (π i x : ℂ) * F (t.equivFin.symm i, y) =
      ∑ i, (π i x : ℂ) * (F (x, y) - F (t.equivFin.symm i, y)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [← Complex.ofReal_sum, h1, Complex.ofReal_one, one_mul]
  rw [h2]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun i => π i x * ε) fun i _ => ?_).trans ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hπ01 i x).1]
    by_cases h0 : π i x = 0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_left (hVε _ x (hπs i (subset_tsupport _ h0)) y hy).le (hπ01 i x).1
  · rw [← Finset.sum_mul, h1, one_mul]

theorem norm_sub_sum_tsum_le {Γ ι : Type*} [Fintype ι] {c : Γ → ℝ} (hc0 : ∀ γ, 0 ≤ c γ) (hc1 : HasSum c 1)
    (hfin : {γ | c γ ≠ 0}.Finite) {φ G : Γ → ℂ} (hφ : ∀ γ, ‖φ γ‖ = 1) {z : ℂ} (hG : ∀ γ, φ γ * G γ = z)
    (p : ι → Γ → ℝ) (b : ι → ℂ) {ε : ℝ} (hε : ∀ γ, c γ ≠ 0 → ‖G γ - ∑ i, (p i γ : ℂ) * b i‖ ≤ ε) :
    ‖z - ∑ i, (∑' γ, φ γ * ((c γ * p i γ : ℝ) : ℂ)) * b i‖ ≤ ε := by
  have h0 : ∀ γ ∉ hfin.toFinset, c γ = 0 := fun γ hγ => by simpa using hγ
  have h1 : ∑ γ ∈ hfin.toFinset, c γ = 1 := (hasSum_sum_of_ne_finset_zero h0).unique hc1
  have h2 : ∀ i, ∑' γ, φ γ * ((c γ * p i γ : ℝ) : ℂ) = ∑ γ ∈ hfin.toFinset, φ γ * ((c γ * p i γ : ℝ) : ℂ) :=
    fun i => tsum_eq_sum fun γ hγ => by simp [h0 γ hγ]
  have h3 : z - ∑ i, (∑' γ, φ γ * ((c γ * p i γ : ℝ) : ℂ)) * b i =
      ∑ γ ∈ hfin.toFinset, (c γ : ℂ) * (φ γ * (G γ - ∑ i, (p i γ : ℂ) * b i)) := by
    simp only [h2, mul_sub, hG, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, h1, Complex.ofReal_one, one_mul]
    congr 1
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [h3]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun γ => c γ * ε) fun γ hγ => ?_).trans ?_)
  · rw [norm_mul, norm_mul, hφ, one_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 γ)]
    exact mul_le_mul_of_nonneg_left (hε γ (by simpa using hγ)) (hc0 γ)
  · rw [← Finset.sum_mul, h1, one_mul]

theorem exists_approx : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B)
    (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (P : Fin n → WO A T → ℂ) (g : Fin n → WO B T → ℂ),
      (∀ i, Continuous (P i)) ∧
      (∀ i (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T),
        P i (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * P i u) ∧
      (∀ i, IsThetaFunO ψ B T (g i)) ∧
      ∀ w, ‖f w - ∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2‖ ≤ ε := by
  intro D ψ hψ S A B T o f hf ε hε
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  obtain ⟨-, a2, -, a4, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := lattice_Mx D T.rank B.rank
  have hFc : Continuous fun p : WO A T × WO B T => f ((o.resS T).symm p) := hf.cont.comp (o.continuous_resS_symm T)
  obtain ⟨hA, hB⟩ := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf
  obtain ⟨χ, hχc, hχs, hχ0, hχ1⟩ := GlobalTheory.RatPartition.exists_partition_one D A T
  obtain ⟨n, a, π, hπ⟩ := exists_slices _ hFc (C := tsupport χ) hχs hK hε

  have hπ' : ∀ x ∈ tsupport χ, ∀ y,
      ‖f ((o.resS T).symm (x, y)) - ∑ i, (π i x : ℂ) * f ((o.resS T).symm (a i, y))‖ ≤ ε := by
    intro x hx y
    obtain ⟨γ, hγ, hγK⟩ := hKc y
    obtain ⟨γ₀, rfl⟩ := mem_ratMx.1 hγ
    have law : ∀ u, f ((o.resS T).symm (u, rat γ₀ + y)) =
        ψ (-(symplOH B T (ratW T B γ₀) y)) * f ((o.resS T).symm (u, y)) := fun u => (hB u).quasi γ₀ y
    have h := hπ x hx _ hγK
    simp only [law] at h
    simp only [mul_left_comm _ (ψ _)] at h
    rwa [← Finset.mul_sum, ← mul_sub, norm_mul, hn, one_mul] at h
  have hper := fun i => GlobalTheory.T.poincareSeries_compactSupport_thetaLaw D ψ hψ A T (fun z => ((χ z * π i z : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (hχc.mul (π i).continuous))
    ((HasCompactSupport.mul_right (f' := fun z => π i z) hχs).comp_left Complex.ofReal_zero)
  have hfin := (GlobalTheory.T.poincareSeries_compactSupport_thetaLaw D ψ hψ A T (fun z => ((χ z : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hχc)
    (hχs.comp_left Complex.ofReal_zero)).1
  refine ⟨n, _, fun i v => f ((o.resS T).symm (a i, v)), fun i => (hper i).2.1, fun i γ u => (hper i).2.2 γ u,
    fun i => hB (a i), fun w => ?_⟩
  obtain ⟨⟨u, v⟩, rfl⟩ := (o.resS T).symm.surjective w
  rw [AddEquiv.apply_symm_apply]
  refine norm_sub_sum_tsum_le (c := fun γ => χ (ratW T A γ + u)) (fun _ => hχ0 _) (hχ1 u) (by simpa using hfin u)
    (G := fun γ => f ((o.resS T).symm (ratW T A γ + u, v))) (fun _ => hn _) (fun γ => ?_)
    (fun i γ => π i (ratW T A γ + u)) _ fun γ hγ => hπ' _ (subset_tsupport _ hγ) v
  have law := (hA v).quasi γ u
  beta_reduce at law ⊢
  rw [law, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThetaSplitApprox

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockVecOfVac

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis

theorem coeff_sum_pderiv_eq_zero {ι : Type} [Fintype ι] (c : ι → ℂ) (Q : MvPolynomial ι ℂ) (n : ℕ)
    (hQ : ∀ m : ι →₀ ℕ, n < m.degree → Q.coeff m = 0) (m : ι →₀ ℕ) (hm : n < m.degree + 1) :
    (∑ i, c i • MvPolynomial.pderiv i Q).coeff m = 0 := by
  classical
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_pderiv,
    hQ _ (by rw [map_add (f := _), Finsupp.degree_single]; omega), zero_mul, smul_zero]

theorem fock_of_vac : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsVacVec ψ θ M M' f → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec ψ θ V W (cart M) (cart M') (ptOf ψ θ M M' f P) := by
  intro D V W S S' M M' θ ψ hψ hθ f hf P
  have hS : ∀ τ, IsCartanInv (gramAt D V τ) (cart M τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model M
  have hT : ∀ τ, IsCartanInv (gramAt D W τ) (cart M' τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model M'
  set A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M') with hAdef
  have hadd : ∀ g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → IsThetaFunO ψ V W (g + g') := by
    intro g g' hg hg'
    refine { quasi := ?_, level := ?_, cont := hg.cont.add hg'.cont, smooth := ?_ }
    · intro γ w
      simp only [Pi.add_apply, hg.quasi, hg'.quasi, mul_add]
    · obtain ⟨U, hU, hUg⟩ := hg.level
      obtain ⟨U', hU', hUg'⟩ := hg'.level
      refine ⟨U ⊓ U', by rw [AddSubgroup.coe_inf]; exact hU.inter hU', fun u hu hinf => ?_⟩
      have he : heisO ψ V W u (g + g') = heisO ψ V W u g + heisO ψ V W u g' := by
        funext w
        simp only [heisO, Pi.add_apply, mul_add]
      rw [he, hUg u hu.1 hinf, hUg' u hu.2 hinf]
    · intro k L hL hfin w
      simpa [Pi.add_apply] using (hg.smooth k L hL hfin w).add (hg'.smooth k L hL hfin w)
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (a • g) := by
    intro a g hg
    refine { quasi := ?_, level := ?_, cont := hg.cont.const_smul a, smooth := ?_ }
    · intro γ w
      simp only [Pi.smul_apply, smul_eq_mul, hg.quasi]
      ring
    · obtain ⟨U, hU, hUg⟩ := hg.level
      refine ⟨U, hU, fun u hu hinf => ?_⟩
      have he : heisO ψ V W u (a • g) = a • heisO ψ V W u g := by
        funext w
        simp only [heisO, Pi.smul_apply, smul_eq_mul]
        ring
      rw [he, hUg u hu hinf]
    · intro k L hL hfin w
      simpa [Pi.smul_apply] using (hg.smooth k L hL hfin w).const_smul a
  have hA : ∀ k g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (A k g) := fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  have hc : ∀ i j g, IsThetaFunO ψ V W g → A i (A j g) = A j (A i g) :=
    fun i j _ h => aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
  have Aadd : ∀ i g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → A i (g + g') = A i g + A i g' :=
    fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h'
  have Asm : ∀ i (a : ℂ) g, IsThetaFunO ψ V W g → A i (a • g) = a • A i g :=
    fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h
  have hpt : ∀ Q, ptOf ψ θ M M' f Q = pureTensorL A f Q := fun _ => rfl
  have hm : ∀ Q, IsThetaFunO ψ V W (pureTensorL A f Q) := pure_mem hadd hsm hA hf.theta

  have hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ), ∃ c : FVar D W.rank V.rank → ℂ, ∀ Q,
      annih (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) z (pureTensorL A f Q) =
        pureTensorL A f (∑ i, c i • MvPolynomial.pderiv i Q) := by
    intro τ z
    refine ⟨fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * Real.pi * Complex.I) *
      ((omDir V W τ z k.1 (unitMap (onb M k.1) (onb M' k.1) k.2.1 k.2.2) : ℝ) +
        Complex.I * (omDir V W τ (cplxO (cart M τ) (cart M' τ) z) k.1
          (unitMap (onb M k.1) (onb M' k.1) k.2.1 k.2.2) : ℝ))), fun Q => ?_⟩
    exact GlobalTheory.ArchRec.DerFock.pure_deriv hadd hsm hA hc Aadd Asm
      (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
      (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hf.theta (hf.vac τ z) Q
  refine ⟨by rw [hpt]; exact hm P, P.totalDegree + 1, fun l hl => ?_⟩

  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ), ∃ Q : MvPolynomial (FVar D W.rank V.rank) ℂ,
      l.foldr (fun p g => annih (heisO ψ V W) θ p.1 (cplxO (cart M p.1) (cart M' p.1)) p.2 g) (pureTensorL A f P) =
        pureTensorL A f Q ∧ ∀ m : FVar D W.rank V.rank →₀ ℕ, P.totalDegree < m.degree + l.length → Q.coeff m = 0 := by
    intro l
    induction l with
    | nil =>
      refine ⟨P, rfl, fun m hm' => MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_⟩
      have h' : P.totalDegree < m.degree := by simpa using hm'
      exact h'
    | cons p l ih =>
      obtain ⟨Q, hQ, hQc⟩ := ih
      obtain ⟨c, hc'⟩ := hder p.1 p.2
      refine ⟨∑ i, c i • MvPolynomial.pderiv i Q, ?_, fun m hm' => ?_⟩
      · rw [List.foldr_cons, hQ, hc']
      · refine coeff_sum_pderiv_eq_zero c Q (P.totalDegree - l.length) (fun m' hm'' => hQc m' (by omega)) m ?_
        simp only [List.length_cons] at hm'
        omega
  obtain ⟨Q, hQ, hQc⟩ := key l
  have hQ0 : Q = 0 := MvPolynomial.ext _ _ fun m => by
    simpa using hQc m (by rw [hl]; omega)
  rw [hpt, hQ, hQ0, map_zero]

end GlobalTheory.FockVecOfVac

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section
open IsDedekindDomain NumberField
open scoped TensorProduct




namespace GlobalTheory.IwaFixed

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem evalV_single_same (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_single_ne (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v)
    {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y h

def intIn (D : D7) (v : Pl D) : v.adicCompletionIntegers D.host.F →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E)).comp (algebraMap _ (Fv D.host.F v))

theorem integral_compFin (v : Pl D) {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    (intIn D v).IsIntegralElem (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    have e : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        intIn D v ⟨evalV D.host.F v a, ha v⟩ *
          (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E) (o : D.host.E) := by
      show Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id _ _) (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        (evalV D.host.F v a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (o : D.host.E))
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    rw [e]
    refine RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) ?_
    obtain ⟨p, hp, hpo⟩ : IsIntegral ℤ (o : D.host.E) := o.2
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have h := congrArg (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E).toRingHom hpo
    rw [Polynomial.hom_eval₂, map_zero] at h
    rw [RingHom.ext_int ((intIn D v).comp (Int.castRingHom _)) ((Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E).toRingHom.comp (algebraMap ℤ D.host.E))]
    exact h
  | zero => rw [map_zero]; exact RingHom.isIntegralElem_zero _
  | add z z' _ _ h h' => rw [map_add (f := _)]; exact RingHom.IsIntegralElem.add _ h h'
  | neg z _ h => rw [map_neg]; exact RingHom.IsIntegralElem.neg _ h

theorem mem_int_of_integral (v : Pl D) (a : Fv D.host.F v)
    (h : (intIn D v).IsIntegralElem (a ⊗ₜ[D.host.F] (1 : D.host.E))) : a ∈ v.adicCompletionIntegers D.host.F := by
  obtain ⟨p, hp, hpa⟩ := h
  have hinj : Function.Injective (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E)) :=
    RingHom.injective _
  have hi : IsIntegral (v.adicCompletionIntegers D.host.F) a := by
    refine ⟨p, hp, hinj ?_⟩
    rw [Polynomial.hom_eval₂, map_zero]
    exact hpa
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  rw [← hy]
  exact y.2

theorem exists_inv (v : Pl D) {x : AE D} (hx : x ∈ idAt D (· = v)) (u : (v.adicCompletionIntegers D.host.F)ˣ)
    (hu : compAt D v x = ((u : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E)) :
    ∃ y ∈ intAt D (· = v), x * y = idem D (· = v) := by
  classical
  obtain ⟨c, hci, hc⟩ : ∃ c : Fv D.host.F v, c ∈ v.adicCompletionIntegers D.host.F ∧ (u.val.1 : Fv D.host.F v) * c = 1 :=
    ⟨u.inv.1, u.inv.2, congrArg Subtype.val u.val_inv⟩
  refine ⟨pairA D.host.F 0 (singleV D.host.F v c) ⊗ₜ[D.host.F] (1 : D.host.E), ⟨?_, ?_⟩, ?_⟩
  · exact pair_mem_idAt _ _ (fun w hw => evalV_single_ne _ v c hw) _
  · rw [finPart_pair]
    refine AddSubgroup.subset_closure ⟨singleV D.host.F v c, fun w => ?_, 1, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [evalV_single_same]; exact hci
    · rw [evalV_single_ne _ v c hw]; exact zero_mem _
  · rw [← sub_eq_zero]
    apply eq_zero_of_comp
    · rw [map_sub, map_mul, infPart_of_idAt hx, infPart_of_idAt (idem_mem_idAt _), zero_mul, sub_zero]
    · intro w
      rw [map_sub, map_mul, compAt_idem]
      by_cases hw : w = v
      · subst hw
        rw [hu, compAt_pair, evalV_single_same, if_pos rfl, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hc,
          ← Algebra.TensorProduct.one_def, sub_self]
      · rw [compAt_of_idAt hx hw, if_neg hw, zero_mul, sub_zero]

theorem fixed_unit_or : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) →
    (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ x ∈ intAt D (· = v), cA D x = x →
    (∃ y ∈ intAt D (· = v), x * y = ε) ∨ (∃ y ∈ intAt D (· = v), (ε - x) * y = ε) := by
  intro D v ε _ _ _ hε hid x hx hfix
  classical
  have hεe : ε = idem D (· = v) := by
    have h1 := (hid _).1 (idem_mem_idAt (· = v))
    have h2 := (mem_idAt_iff (· = v) ε).1 hε.1
    rw [← h2, mul_comm, h1]
  subst hεe
  obtain ⟨b, hb⟩ := GlobalTheory.CharConjFixed.fixed_mem D x hfix
  have hcomp : compAt D v x = evalV D.host.F v (sndA D.host.F b) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [← hb]
    show Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id _ _)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (b ⊗ₜ[D.host.F] (1 : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl
  have hint : evalV D.host.F v (sndA D.host.F b) ∈ v.adicCompletionIntegers D.host.F := by
    apply mem_int_of_integral
    rw [← hcomp]
    exact integral_compFin v hx.2
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨_, hint⟩ : v.adicCompletionIntegers D.host.F) with ⟨u, hu⟩ | ⟨u, hu⟩
  · left
    refine exists_inv v hx.1 u ?_
    rw [hu, hcomp]
  · right
    refine exists_inv v (sub_mem (idem_mem_idAt _) hx.1) u ?_
    rw [hu, map_sub, compAt_idem, if_pos rfl, hcomp, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
    rfl

end GlobalTheory.IwaFixed

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SBesEx

theorem linearIndependent_eX_of_dual {D : D7} (X : HidaSetting D) : LinearIndependent D.host.E X.eX := by
  rw [Fintype.linearIndependent_iff]
  intro g hg b
  have h1 := congrArg (fun y => (VS D).hT y (X.fY b)) hg

  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, X.ef, map_zero,
  LinearMap.zero_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  simpa using h1

theorem eM_transpose_linearIndependent : ∀ {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → LinearIndependent D.host.E (GlobalTheory.Core.SBesEx.eM X h t lam).transpose := by
  intro D X h t lam ht hl
  set b := X.bas.reindex (finCongr (rank_eq X h)).symm with hb
  have hc : ∀ z, cY X h z = b.equivFun z := by
    intro z; funext k
    simp [cY, HidaSetting.crd, crdOf, hb, Module.Basis.repr_reindex]
  have h0 : LinearIndependent D.host.E (fun a => b.equivFun (X.eX a)) :=
    (linearIndependent_eX_of_dual X).map' b.equivFun.toLinearMap b.equivFun.ker
  have hs : ∀ a, scl t lam a ≠ 0 := fun a => mul_ne_zero ht (pow_ne_zero _ hl)
  have h1 := h0.units_smul (fun a => Units.mk0 (scl t lam a) (hs a))
  have he : (eM X h t lam).transpose =
      (fun a => Units.mk0 (scl t lam a) (hs a)) • fun a => b.equivFun (X.eX a) := by
    funext a k
    simp [eM, hc, Matrix.transpose_apply, Units.smul_def]
  rw [he]
  exact h1

end GlobalTheory.Core.SBesEx

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.contDiff_heisenbergSuperposition_thetaFunction_real : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → WO S T) (a : Ω → ℂ), Measurable v → Integrable a μ → ContDiff ℝ ∞ (fun z : GlobalTheory.FockCompare.RW T S => ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F (v x) ∂μ) := by
  first | exact @GlobalTheory.SuperposSmooth.main | exact GlobalTheory.SuperposSmooth.main | (intros; apply GlobalTheory.SuperposSmooth.main <;> assumption)
end
