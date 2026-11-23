module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle174
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle224
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle213
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsGoodFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalUnitaryLatticesOfLevel
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle296
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialOnDualQuotientIffMemLocalUnitary
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle320
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeMaximalCompactInterIsotropicFlagLevi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeUnitaryMaximalCompactEqProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationAbsoluteSidePieceBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGaugeVolumeLeClassNumberDefinite
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationDegenerateSidePieceBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle297
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle109
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle164
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle009
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
import Mathlib.RingTheory.PicardGroup
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem GFset_eq_one_of_place (I : AutInst) (γ : I.GA) (hγ : γ ∈ I.GFset) (v : InfinitePlace I.F)
    (h : uMat (γ.1 v) = 1) : γ = 1 := by
  obtain ⟨g, -, hinf, hfin⟩ := hγ
  have hdet : ∀ w, IsUnit (I.P w).det := fun w => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit w)
  set M : Matrix (Fin I.n) (Fin I.n) I.E := (g : Matrix (Fin I.n) (Fin I.n) I.E) with hM
  have e1 : (I.P v)⁻¹ * M.map (I.φ v) * I.P v = 1 := (hinf v).symm.trans h
  have e2 : M.map (I.φ v) * I.P v = I.P v := by
    have := congrArg (I.P v * ·) e1
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hdet v)] using this
  have e3 : M.map (I.φ v) = 1 := by
    have := congrArg (· * (I.P v)⁻¹) e2
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet v)] using this
  have hg : M = 1 := by
    apply Matrix.map_injective (I.φ v).injective
    dsimp only
    rw [e3, Matrix.map_one _ (map_zero _) (map_one _)]
  refine Prod.ext (funext fun w => ?_) ?_
  · have hw : uMat (γ.1 w) = 1 := by
      rw [hinf w, hg, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
        Matrix.nonsing_inv_mul _ (hdet w)]
    exact Subtype.ext (Units.ext (by simpa using hw))
  · have hf : I.fmat γ.2 = 1 := by
      rw [hfin, hg, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Subtype.ext (Units.ext (by simpa using hf))

theorem one_mem_GFset_def (I : AutInst) : (1 : I.GA) ∈ I.GFset := by
  refine ⟨1, Subgroup.one_mem _, fun v => ?_, ?_⟩
  · rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))]
    rfl
  · rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl

theorem definite_count_of_finite : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ),
    GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount.DefiniteHyp B d p → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) →
      (B.D : ℝ) = mainTerm B d := by
  intro B d p hH hfin
  have hn : B.I.n = p := hH.rank_eq
  obtain ⟨hDS, hSig, hp, -, hprime, hgt, hsplit⟩ := hH
  have hn1 : 1 ≤ B.I.n := hn ▸ hp

  have hq : ∀ v, (univ.filter fun a => B.I.ε v a = false).card = 0 := fun v => (hSig v).2
  have hrk : ∀ v, rkR (B.I.ε v) = 0 := fun v => by
    unfold rkR
    rw [hq v]
    exact Nat.min_zero _
  have hpos : ∀ v a, B.I.ε v a = true := fun v a => by
    by_contra hne
    have ha : a ∈ univ.filter fun a => B.I.ε v a = false := by simpa using hne
    rw [Finset.card_eq_zero.mp (hq v)] at ha
    exact Finset.notMem_empty a ha
  have hJ : ∀ v, Formalism.REAL.Jm (B.I.ε v) = 1 := fun v => by
    unfold Formalism.REAL.Jm
    simp [hpos v]
  have hunit : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), (uMat g)ᴴ * uMat g = 1 := fun v g => by
    have h0 : (uMat g)ᴴ * Formalism.REAL.Jm (B.I.ε v) * uMat g = Formalism.REAL.Jm (B.I.ε v) := g.2
    rwa [hJ v, Matrix.mul_one] at h0
  have hdHS : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), dHS (uMat g) = 0 := fun v g =>
    (GlobalTheory.T.logSingularValuesEuclidNorm_cartan_properties B.I.n (B.I.ε v)).2.2.2 (hrk v) g

  have hrad := GlobalTheory.T.isRadical_span_prime_of_ncard_primesOver_eq_finrank B.I.E B.g₀ hprime hsplit
  have hNU := (GlobalTheory.NearElement.near_unipotent B d (1 / 10 ^ 5) (by norm_num) le_rfl hn1 hgt hrad _ _
    rfl rfl).1
  have hkey : ∀ x γ : B.I.GA, γ ∈ B.I.GFset → phe B d (x⁻¹ * γ * x) ≠ 0 → γ = 1 := by
    intro x γ hγ hne
    have hep : (0 : ℝ) ≤ 1 / 10 ^ 5 / ((B.I.n : ℝ) ^ 8 * (B.I.f : ℝ) ^ 2) := by positivity
    obtain ⟨-, hu, -⟩ := hNU x γ ⟨hγ, hne, fun v => by rw [hdHS]; exact hep⟩
    obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    apply GFset_eq_one_of_place B.I γ hγ v
    apply GlobalTheory.unipotent_isometry_definite_eq_one B.I.n B.I.n _ 1 one_ne_zero _ (hu v)
    simpa using hunit v (γ.1 v)

  have hker : ∀ x, kern B.I (phe B d) x x = phe B d 1 := by
    intro x
    unfold kern
    rw [tsum_eq_single (⟨1, one_mem_GFset_def B.I⟩ : B.I.GFset)]
    · simp
    · intro γ hγ
      by_contra hne
      exact hγ (Subtype.ext (hkey x γ.1 γ.2 hne))
  have hph1 : ph B d 1 = ((∏ v, d v : ℝ) : ℂ) := by
    unfold ph
    have hc : ∀ v, ⟪B.w v, B.σ v (uMat ((1 : B.I.Ginf) v)) (B.w v)⟫_ℂ = 1 := by
      intro v
      have hs : B.σ v (uMat ((1 : B.I.Ginf) v)) = 1 := by
        rw [show uMat ((1 : B.I.Ginf) v) = 1 from rfl]
        exact (hDS v).2.1.2.2.1.1.1
      rw [hs, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, (hDS v).2.2.1.1]
      simp
    rw [Finset.prod_congr rfl (fun v _ => hc v)]
    simp

  have hloc : LocDec B 0 := by
    intro v g
    have hd : decE (rkR (B.I.ε v)) 0 (dOp (uMat g)) = 1 := by simp [decE]
    rw [hd]
    calc ‖⟪B.w v, B.σ v (uMat g) (B.w v)⟫_ℂ‖ ≤ ‖B.w v‖ * ‖B.σ v (uMat g) (B.w v)‖ :=
          norm_inner_le_norm _ _
      _ = 1 := by rw [(hDS v).2.1.2.2.1.2.1 _ g.2 _, (hDS v).2.2.1.1]; norm_num
  have hbig : HBig B 32 0 := by
    intro v
    rw [hrk v]
    simp
  obtain ⟨hcont, hbd, hmaj⟩ := GlobalTheory.T.discrete_series_coefficient_integrable_majorant B d 0 hDS hloc
  have hm := hmaj 0 le_rfl (fun v => Or.inl (hrk v))
  simp only [zero_mul, Real.exp_zero, mul_one] at hm
  have hint : Integrable (ph B d) (muInf B.I) :=
    hm.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  obtain ⟨T, hT⟩ := (GlobalTheory.T.globalConvolutionOrthogonalProjector_proof B d hDS hint).2.2.1
  obtain ⟨-, -, -, -, -, -, -, hD, -⟩ := GlobalTheory.T.kernelB' B d 0 hDS hn1 hloc hbig hfin T hT
  simp_rw [hker] at hD
  rw [setIntegral_const] at hD
  have hphe : phe B d 1 = ((∏ v, d v : ℝ) : ℂ) * B.e 1 := by
    show ph B d (1 : B.I.GA).1 * B.e (1 : B.I.GA).2 = _
    rw [Prod.fst_one, Prod.snd_one, hph1]
  rw [hphe] at hD
  have he1 := (GlobalTheory.rowsAut_idem_elementary B).1
  have hre := congrArg Complex.re hD
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, he1,
    mul_zero, sub_zero, zero_mul, Complex.natCast_re] at hre
  unfold mainTerm AutInst.Dstar AutInst.vol
  rw [← hre, measureReal_def]
  ring

end GlobalTheory.Dec
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WeylDimU

theorem prod_sub_eq_prod_factorial (k : ℕ) :
    ∏ a : Fin k, ∏ b ∈ Finset.univ.filter (fun b : Fin k => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  rcases k with _ | m
  · simp
  have h := Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) m
  rw [Matrix.det_vandermonde, ← Nat.prod_range_succ_factorial, Nat.cast_prod] at h
  simp only [Finset.filter_lt_eq_Ioi]
  rw [← h]

theorem finrank_space {k : ℕ} (lam : Formalism.BasicNotions.DomWeight k) (u : Fin k → ℝ)
    (hu : ∀ a, (lam.w a : ℝ) = u a - (((k : ℝ) - 1) / 2 - (a : ℕ))) :
    (Module.finrank ℂ (GlobalTheory.DualWeyl.Space lam.natW) : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  have h := Formalism.L2.G.Model.weyl_dualWeyl ℂ k lam.natW (Formalism.BasicNotions.factNatW k lam).1
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_natCast, Rat.cast_prod] at h2
  refine Eq.trans h2 ?_
  rw [← prod_sub_eq_prod_factorial, vand, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_div_distrib, Finset.prod_filter]
  refine Finset.prod_congr rfl fun b _ => ?_
  split_ifs
  · push_cast
    congr 1
    linarith [hu a, hu b, GlobalTheory.NablaType.natW_add lam a, GlobalTheory.NablaType.natW_add lam b]
  · simp

theorem finrank_eq (k : ℕ) (u : Fin k → ℝ) (hu : IsHCParam u) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (hπ : IsHCTypeU k u π) :
    (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  obtain ⟨hs, hm⟩ := hu
  choose m hm using hm
  have hm' : StrictAnti m := fun a b hab => by
    have := hs hab
    have h2 : (m b : ℝ) < m a := by linarith [hm a, hm b]
    exact_mod_cast h2
  have hL : Antitone fun a : Fin k => m a + (a : ℕ) := by
    rcases k with _ | n
    · exact fun a => a.elim0
    rw [Fin.antitone_iff_succ_le]
    intro i
    have := hm' (Fin.castSucc_lt_succ (i := i))
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  let lam : Formalism.BasicNotions.DomWeight k := ⟨fun a => m a + (a : ℕ), hL⟩
  have hw : ∀ a, (lam.w a : ℝ) = u a - (((k : ℝ) - 1) / 2 - (a : ℕ)) := fun a => by
    simp only [lam]
    push_cast
    linarith [hm a]
  have hK := GlobalTheory.NablaType.isKTypeOf_act lam
  have hT : IsHCTypeU k u (GlobalTheory.NablaType.act lam) := by
    refine ⟨?_, inferInstance, GlobalTheory.NablaType.isURepOn_act lam, ?_⟩
    · obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
      exact ⟨v, 0, hv⟩
    · convert hK using 1
      funext a
      unfold allPos
      rw [GlobalTheory.DefiniteCheck.lowK_const, hw]
  obtain ⟨A, -⟩ := GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU k u _ _ _ _ hπ hT
  rw [A.finrank_eq]
  exact finrank_space lam u hw

theorem weyl_dimension : ∀ (k : ℕ) (u : Fin k → ℝ), IsHCParam u → (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π → (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ)) ∧ (dimPiU k u : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  intro k u hu
  refine ⟨fun H _ _ π hπ => finrank_eq k u hu H π hπ, ?_⟩
  obtain ⟨H, _, _, π, hπ⟩ := GlobalTheory.CompactDS.exists_isHCTypeU k u hu
  have hne : {d | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π ∧ Module.finrank ℂ H = d}.Nonempty :=
    ⟨_, H, _, _, π, hπ, rfl⟩
  obtain ⟨H', _, _, π', hπ', e⟩ := Nat.sInf_mem hne
  rw [dimPiU, ← e]
  exact finrank_eq k u hu H' π' hπ'

end GlobalTheory.WeylDimU
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_localUnitary_lattices_of_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → TLat cm.sig J T f M → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∃ h ∈ UPts cm.sig J (v.adicCompletion F), ∀ x, x ∈ loc v L ↔ h.1 *ᵥ x ∈ loc v M := by
  first | exact @GlobalTheory.St.G.exists_unitary_of_TLat | exact GlobalTheory.St.G.exists_unitary_of_TLat | (intros; apply GlobalTheory.St.G.exists_unitary_of_TLat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adelicLatticeFrame_local_basis_unitriangular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (k t : ℕ) (gp : Fin 2 → ℕ) (G : GLoc F E cm.sig gp) (L : Submodule (𝓞 E) (Fin n → E)) (Fr : AdFrame cm.sig J (hat F L) (gp 0 * gp 1) k), k = n → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, SplitsIn E (gp i)) → IsLat L → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal), SelfDualAt cm.sig J v L → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, G.phi i v hv (y b) = x b) ↔ ∀ b, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, (Fr.LocK L v y ↔ InJ n t n false (redM F v (G.mat i v hv fr y))) ∧ (Fr.LocK L v y → Fr.locChi v y = lamJ ψ (fun _ => 1) n t 0 n (redM F v (G.mat i v hv fr y))) := by
  first | exact @GlobalTheory.St.G.frame_local_basis_unitriangular | exact GlobalTheory.St.G.frame_local_basis_unitriangular | (intros; apply GlobalTheory.St.G.frame_local_basis_unitriangular <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.trivial_on_dual_quotient_iff_mem_localUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E cm.sig J T f bad), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ y ∈ levelVL cm.sig J v S.Lb, (∀ x ∈ loc v (_root_.GlobalTheory.St.G.dualL cm.sig J S.Lb), (y.1 - 1) *ᵥ x ∈ loc v S.Lb) ↔ y ∈ S.Uloc v :=
  @_root_.GlobalTheory.St.G.FunFix.trivial_iff_mem_Uloc
end

section

noncomputable section

open NumberField GlobalTheory.DegCnt

namespace GlobalTheory.OrthoLattice

theorem isCMField_of_star (K : Type) [Field K] [NumberField K] [StarRing K] (htc : IsTotallyComplex K)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) : IsCMField K := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hmem : ∀ x : K, star x = x → x ∈ maximalRealSubfield K := fun x hx ψ => by
    have := hst ψ x
    rw [hx] at this
    exact this.symm
  have hfix : ∀ x : maximalRealSubfield K, star (x : K) = x := fun x =>
    φ.injective (by rw [hst]; exact x.2 φ)
  obtain ⟨a, ha⟩ : ∃ a : K, star a ≠ a := by
    by_contra h
    push Not at h
    apply IsTotallyComplex.complexEmbedding_not_isReal φ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hst, h]
  set d : K := a - star a with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 ha.symm
  have hds : star d = -d := by simp [hd]
  have hli : LinearIndependent (maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 : (s : K) + (t : K) * d = 0 := by simpa [Subfield.smul_def] using h
    have h2 := congrArg star h1
    rw [star_add, star_mul, hfix, hfix, hds, star_zero] at h2
    have h3 : (s : K) = 0 := by linear_combination (h1 + h2) / 2
    have h4 : (t : K) * d = 0 := by linear_combination h1 - h3
    exact ⟨Subtype.ext h3, Subtype.ext ((mul_eq_zero.1 h4).resolve_right hd0)⟩
  have hsp : ⊤ ≤ Submodule.span (maximalRealSubfield K) (Set.range ![(1 : K), d]) := by
    intro x _
    have h1 : star ((x + star x) / 2) = (x + star x) / 2 := by
      rw [star_div₀, star_add, star_star, star_ofNat, add_comm]
    have h2 : star ((x - star x) / (2 * d)) = (x - star x) / (2 * d) := by
      rw [star_div₀, star_sub, star_star, star_mul, star_ofNat, hds]
      field_simp
      ring
    have h3 : x = (⟨_, hmem _ h1⟩ : maximalRealSubfield K) • (1 : K) +
        (⟨_, hmem _ h2⟩ : maximalRealSubfield K) • d := by
      simp only [Subfield.smul_def, smul_eq_mul]
      field_simp
      ring
    rw [h3]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have : Algebra.IsQuadraticExtension (maximalRealSubfield K) K :=
    { finrank_eq_two' := by simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp) }
  exact ⟨⟩

theorem hasOrtho : ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K := by
  intro K _ _ st hc
  have := isCMField_of_star K hc.1 hc.2.1
  have hs : st = IsCMField.starRing K := by
    let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have h : ∀ x, st.star x = IsCMField.complexConj K x := fun x =>
      φ.injective (by rw [IsCMField.complexEmbedding_complexConj]; exact hc.2.1 φ x)
    obtain @⟨@⟨@⟨@⟨f⟩, _⟩, _⟩, _⟩ := st
    obtain rfl : f = IsCMField.complexConj K := funext h
    rfl
  subst hs
  let := IsCMField.starRing K
  intro W _ _ _ _ _ k hk hp ⟨L, hL, hU⟩
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hnd : k.Nondegenerate := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    · by_contra h0
      have := hp φ x h0
      rw [hx x] at this
      simp at this
  let S : Formalism.BasicNotions.HSpace K := Formalism.BasicNotions.HSpace.mk W k hk hnd (Module.finrank K W) rfl (Module.finBasis K W)
    (fun _ => (Module.finrank K W, 0)) L hL hU
  have hsig : S.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef
    ((GlobalTheory.Proof.GenusMassSignature.pos_iff_posDef hc.1 hc.2.1 S τ).1 (hp τ))
  obtain ⟨b, hb, ho⟩ := GlobalTheory.DefiniteOrthonormal.exists_orthonormal hc S hsig fun _ => rfl
  exact ⟨_, b, hb, hb.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _), rfl, ho⟩

end GlobalTheory.OrthoLattice
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.volume_maximalCompact_inter_isotropicFlagLevi : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ μ, IsGaugeSub (maxK ε ∩ flagM ε W) ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) μ → μ Set.univ = ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) * volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) := by
  first | exact @GlobalTheory.FlagMeas.LeviCompact.volume_maxK_inter_flagM | exact GlobalTheory.FlagMeas.LeviCompact.volume_maxK_inter_flagM | (intros; apply GlobalTheory.FlagMeas.LeviCompact.volume_maxK_inter_flagM <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.volume_unitaryMaximalCompact_eq_prod : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ μ, IsGaugeSub (maxK ε) (p ^ 2 + q ^ 2) μ → μ Set.univ = ENNReal.ofReal (volU p * volU q) := by
  first | exact @GlobalTheory.VolMaxK.volume_maxK | exact GlobalTheory.VolMaxK.volume_maxK | (intros; apply GlobalTheory.VolMaxK.volume_maxK <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplification_absolute_side_piece_bound : ∀ (k r : ℕ) {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ' : Mat k r → ℂ) (μG μW' νS' μR νR : Measure (Mt k r)) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ r → 2 * r + 6 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → MomBd z' νS' Φ' q H₁ → TwoFl k r z z' γ → DeOK k r z z' γ De → NormR k r γ s μR → IsQuotMeas μG μR νR → νR {x | Matrix.of x ∉ GG k r ∨ Yv k r z z' γ (Matrix.of x) = 0} = 0 ∧ ∀ w : Wq, ‖w‖ = 1 → ∀ (i : ℕ) (R₀ y : ℝ), 1 ≤ R₀ → 0 < y → ∫⁻ x in Eset k r z z' γ R₀ y ∩ {x | i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z' (Matrix.of x)}, ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR ≤ ENNReal.ofReal (κ / s * fibVol k r R₀ De y * ((r + 1) * 4 ^ q * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * c) := by
  first | exact @GlobalTheory.Amp.AbsSide.abs_side | exact GlobalTheory.Amp.AbsSide.abs_side | (intros; apply GlobalTheory.Amp.AbsSide.abs_side <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.unitaryGaugeVolume_le_classNumber_definite : ∀ (I : AutInst) (r : ℕ), HasSig I r 0 → ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure], IsGaugeAll I c → gaugeVol I c μf ≤ ENNReal.ofReal (volU r ^ I.f) * ((defClassNum I.E r : ENat) : ENNReal) := by
  first | exact @GlobalTheory.DefiniteVolume.gaugeVol_le | exact GlobalTheory.DefiniteVolume.gaugeVol_le | (intros; apply GlobalTheory.DefiniteVolume.gaugeVol_le <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplification_degenerate_side_piece_bound : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ' : Mat k r → ℂ) (μG μW' νS' μR νR : Measure (Mt k r)) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → νR {x | Matrix.of x ∉ GG k r ∨ Yj k r hj z z' γ (Matrix.of x) = 0} = 0 ∧ ∀ w : Wq, ‖w‖ = 1 → ∀ (i : ℕ) (R₀ y : ℝ), 1 ≤ R₀ → 0 < y → ∫⁻ x in Eset0 k r hj z z' γ R₀ y ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)}, ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR ≤ ENNReal.ofReal (κ / s * fibVol0 k r j R₀ De y * ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * c) := by
  first | exact @GlobalTheory.Amp.DegSide.side_bound | exact GlobalTheory.Amp.DegSide.side_bound | (intros; apply GlobalTheory.Amp.DegSide.side_bound <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_symm_invariant_kernel_hermitian_frames : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, P Λ ↔ (S.IsTerm d Λ ∧ S.InFF β (j + 1) βJ d Λ)) → ∃ m : Submodule L.O S.V → Submodule L.O S.V → ℝ, (∀ h ∈ S.St, ∀ x y, P x → P y → m (h • x) (h • y) = m x y) ∧ ∀ x, P x → {y | P y ∧ m x y ≠ 0}.Finite ∧ (∀ y, P y → 0 ≤ m x y ∧ m x y = m y x) ∧ |(∑ᶠ y : {y // P y}, m x y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ ‖∑ᶠ y : {y // P y}, (m x y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  first | exact @GlobalTheory.HL.exists_symm_invariant_kernel | exact GlobalTheory.HL.exists_symm_invariant_kernel | (intros; apply GlobalTheory.HL.exists_symm_invariant_kernel <;> assumption)
end
