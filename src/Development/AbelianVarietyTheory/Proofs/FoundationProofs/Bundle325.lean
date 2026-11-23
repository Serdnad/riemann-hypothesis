module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateLogNormParallelogramLaw
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointLocalHeightEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSigmaStarTranslatePowDecomposition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle264
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle287
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle278
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle320
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle016
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle303
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
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
import Mathlib.RingTheory.PowerSeries.Inverse
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_adelicWeilRepresentationModel : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∃ w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA := by
  first | exact @GlobalTheory.FinWeil.Model.exists_isModel | exact GlobalTheory.FinWeil.Model.exists_isModel | (intros; apply GlobalTheory.FinWeil.Model.exists_isModel <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaTranslatePowerSeries_pow_boundedCoeffs_of_torsion : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∀ N : ℕ, 0 < N → (N : ℂ) * t ∈ g.abelian₂ →
      GlobalTheory.EvenTheta.BddSer (GlobalTheory.ThetaTransl.tau g t ^ N) := by
  first | exact @GlobalTheory.ThetaTransl.tau_pow_bdd | exact GlobalTheory.ThetaTransl.tau_pow_bdd | (intros; apply GlobalTheory.ThetaTransl.tau_pow_bdd <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaTranslateLogNorm_parallelogram_law : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖GlobalTheory.EvenTheta.xAt g s‖ ≤ 1) →
    (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ∃ w : PowerSeries ℂ_[p], GlobalTheory.EvenTheta.IntSer w ∧
      PowerSeries.constantCoeff w = 1 ∧ GlobalTheory.ThetaTransl.tau g s = PowerSeries.C (GlobalTheory.ThetaTransl.cval g s) * w) →
    ∀ P Q : ℂ, (∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * P ∈ g.abelian₂) → GL3Theta.Tors1 p g.abelian₂ Q →
      GlobalTheory.ThetaTransl.logc g (P + Q) + GlobalTheory.ThetaTransl.logc g (P - Q) = 2 * GlobalTheory.ThetaTransl.logc g P + 2 * GlobalTheory.ThetaTransl.logc g Q := by
  first | exact @GlobalTheory.ThetaPar.par_holds | exact GlobalTheory.ThetaPar.par_holds | (intros; apply GlobalTheory.ThetaPar.par_holds <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.torsionPoint_localHeight_eq_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ v : ℂ, InRationalLattice g.abelian₂ v → v ∉ g.abelian₂ → ‖GlobalTheory.ThetaTransl.cval g v‖ ^ 2 * max 1 ‖xAt g v‖ = 1 := by
  first | exact @GlobalTheory.TorsionHeight.height_one | exact GlobalTheory.TorsionHeight.height_one | (intros; apply GlobalTheory.TorsionHeight.height_one <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.genus_one_datum_model_lattice_algebraic_data : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → IsWq g.W g.wq ∧ IsLat g.abelian₂ ∧ g2 g.abelian₂ ∈ Qbar ∧ g3 g.abelian₂ ∈ Qbar ∧ AlgEnt (sgStar g.abelian₂) ∧ ∃ v : ℂ, v ∉ g.abelian₂ ∧ wpF g.abelian₂ v ∈ Qbar := by
  first | exact @GlobalTheory.FrobStick.AtData.atData | exact GlobalTheory.FrobStick.AtData.atData | (intros; apply GlobalTheory.FrobStick.AtData.atData <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter
open scoped Topology

noncomputable section

namespace GlobalTheory.ThetaOrderBdd
open GlobalTheory.ThetaTransl GlobalTheory.ThetaTranslDecomp

variable {Λ : AddSubgroup ℂ}

theorem ratio_add (hΛ : IsLat Λ) {G : ℂ → ℂ} {k : ℕ}
    (hlaw : ∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ k = G z * sgStar Λ (z + ω) ^ k)
    (z : ℂ) {l : ℂ} (hl : l ∈ Λ) :
    G (z + l) / sgStar Λ (z + l) ^ k = G z / sgStar Λ z ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hlaw l hl z
  by_cases hz : z ∈ Λ
  · rw [(hΛ.sg_eq_zero z).2 hz, (hΛ.sg_eq_zero _).2 (add_mem hz hl), zero_pow hk.ne']
    simp
  have h0 := (hΛ.sg_eq_zero z).not.2 hz
  have h1 : sgStar Λ (z + l) ≠ 0 := (hΛ.sg_eq_zero _).not.2 (fun h => hz (by simpa using sub_mem h hl))
  rw [div_eq_div_iff (pow_ne_zero _ h1) (pow_ne_zero _ h0)]
  exact hlaw l hl z

theorem exists_decomp_gen : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (k : ℕ) (G : ℂ → ℂ), Differentiable ℂ G →
    (∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ k = G z * sgStar Λ (z + ω) ^ k) →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), k ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - k) * G z =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  intro Λ hΛ k G hG hlaw v hv
  obtain ⟨L, h⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hσ := hΛ.differentiable
  have hS := hΛ.differentiable_sqTh v
  have hT : Continuous (sqThD Λ v) := by
    have h1 := hσ.deriv.continuous
    have h2 := hS.deriv.continuous
    have h3 := hσ.continuous
    have h4 := hS.continuous
    unfold sqThD
    fun_prop
  have hc : ∀ z, z ∉ L.lattice →
      ContinuousAt (fun z => G z / sgStar Λ z ^ k) z := fun z hz =>
    (hG z).continuousAt.div ((hσ z).continuousAt.pow k)
      (pow_ne_zero _ ((hΛ.sg_eq_zero z).not.2 ((h z).not.2 hz)))
  obtain ⟨A, B, hAB⟩ := GlobalTheory.EllipticPoles.no_pole_case L
    (g := fun z => G z / sgStar Λ z ^ k)
    (fun a => (hG.analyticAt a).meromorphicAt.div ((hσ.analyticAt a).meromorphicAt.pow k))
    (fun a ha => ⟨_, (hc a ha).tendsto.mono_left nhdsWithin_le_nhds⟩)
    (fun z l hl => ratio_add hΛ hlaw z ((h l).2 hl))
  have hAB' : ∀ z, z ∉ L.lattice → G z / sgStar Λ z ^ k =
      A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
    intro z hz
    have h1 := (L.analyticOnNhd_weierstrassP z hz).continuousAt
    have h2 := (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt
    have h3 : ContinuousAt (fun z => A.eval (L.weierstrassP z) +
        B.eval (L.weierstrassP z) * L.derivWeierstrassP z) z :=
      (A.continuous.continuousAt.comp h1).add ((B.continuous.continuousAt.comp h1).mul h2)
    exact tendsto_nhds_unique_of_eventuallyEq ((hc z hz).tendsto.mono_left nhdsWithin_le_nhds)
      (h3.tendsto.mono_left nhdsWithin_le_nhds) (hAB z)
  set A' := Polynomial.taylor (wpF Λ v) A with hA'
  set B' := Polynomial.taylor (wpF Λ v) B with hB'
  obtain ⟨I, hI⟩ : ∃ I, I = A'.natDegree + B'.natDegree + k := ⟨_, rfl⟩
  refine ⟨I, A'.coeff, B'.coeff, by omega, fun z => ?_⟩
  have h3 := hσ.continuous
  have h4 := hS.continuous
  have h5 := hG.continuous
  refine congrFun (Continuous.ext_on hΛ.dense_compl
    (f := fun z => sgStar Λ z ^ (2 * I + 3 - k) * G z)
    (g := fun z => ∑ i ∈ Finset.range (I + 1),
      A'.coeff i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
      ∑ j ∈ Finset.range (I + 1),
        B'.coeff j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z))
    (by fun_prop) (by fun_prop) fun z hz => ?_) z
  have hz' : z ∉ L.lattice := (h z).not.1 hz
  have h0 := (hΛ.sg_eq_zero z).not.2 hz
  have e := hAB' z hz'
  rw [← Polynomial.taylor_eval_sub (wpF Λ v) A, ← Polynomial.taylor_eval_sub (wpF Λ v) B,
    ← hA', ← hB', Polynomial.eval_eq_sum_range' (n := I + 1) (p := A') (by omega),
    Polynomial.eval_eq_sum_range' (n := I + 1) (p := B') (by omega),
    div_eq_iff (pow_ne_zero _ h0)] at e
  beta_reduce
  rw [e, mul_left_comm, ← pow_add, Nat.sub_add_cancel (by omega), sqThD_eq hΛ L h hv hz,
    hΛ.sqTh_eq hv hz, GlobalTheory.OddTheta.wpF_eq L Λ h z, add_mul, Finset.sum_mul, Finset.sum_mul,
    Finset.sum_mul]
  congr 1 <;> refine Finset.sum_congr rfl fun i hi => ?_
  all_goals
    obtain ⟨m, rfl⟩ : ∃ m, I = i + m := Nat.exists_eq_add_of_le (by simpa [Nat.lt_succ_iff] using hi)
    rw [Nat.add_sub_cancel_left, mul_pow]
    ring



theorem order_bdd : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
    ∀ (k : ℕ) (G : ℂ → ℂ), AlgEnt G →
      (∀ ω ∈ g.abelian₂, ∀ z, G (z + ω) * sgStar g.abelian₂ z ^ k = G z * sgStar g.abelian₂ (z + ω) ^ k) →
      ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU G = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B := by
  intro p _ g hok hlat' h2 h3 hdisc hsg v hv hwv k G hG hlaw
  obtain ⟨hu1, hwq1, -, he0, hsgU⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he_def
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε_def
  have he : e ≠ 0 := fun h => by rw [h, map_zero] at he0; exact zero_ne_one he0
  have gσ : GoodAt g 1 (sgStar g.abelian₂) :=
    ⟨hsg, PowerSeries.C ε * PowerSeries.X, bdd_mul (bdd_C ε) bdd_X, by rw [hsgU]; ring⟩
  obtain ⟨hSa, hSe⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg v hv hwv
  have gS : GoodAt g 2 (sqTh g.abelian₂ v) := ⟨hSa, lineSer g.wq⁻¹ (xAt g v),
    bdd_sub ⟨1, hwq1⟩ (bdd_mul (bdd_C _) (by rw [sq]; exact bdd_mul (bdd_X (p := p)) (bdd_X (p := p)))), hSe⟩
  obtain ⟨hTa, w, hw, hTe⟩ := GlobalTheory.ThetaTransl.CubeSer.sqThD_atU p g hok hlat' h2 h3 hdisc hsg v hv hwv
  have gT : GoodAt g 3 (sqThD g.abelian₂ v) := ⟨hTa, w, hw, hTe⟩
  obtain ⟨I, a, b, hle, hid⟩ := exists_decomp_gen g.abelian₂ hlat' k G hG.1 hlaw v hv
  let φ : Fin (I + 1) ⊕ Fin (I + 1) → ℂ → ℂ := Sum.elim
    (fun i z => sgStar g.abelian₂ z ^ (2 * (I - (i : ℕ)) + 3) * sqTh g.abelian₂ v z ^ (i : ℕ))
    (fun j z => sgStar g.abelian₂ z ^ (2 * (I - (j : ℕ))) * sqTh g.abelian₂ v z ^ (j : ℕ) * sqThD g.abelian₂ v z)
  let c : Fin (I + 1) ⊕ Fin (I + 1) → ℂ := Sum.elim (fun i => a i) (fun j => b j)
  have gφ : ∀ k, GoodAt g (2 * I + 3) (φ k) := by
    rintro (i | j)
    · have hi := i.isLt
      exact good_congr (good_mul (good_pow gσ (2 * (I - (i : ℕ)) + 3)) (good_pow gS (i : ℕ))) (by omega)
    · have hj := j.isLt
      exact good_congr (good_mul (good_mul (good_pow gσ (2 * (I - (j : ℕ)))) (good_pow gS (j : ℕ))) gT)
        (by omega)
  obtain ⟨hEa, hEe⟩ := atU_mul_pow (g := g) hsg hG (2 * I + 3 - k) 1
  have hEq : ∀ z, sgStar g.abelian₂ z ^ (2 * I + 3 - k) * G z ^ 1 = ∑ j, c j * φ j z := by
    intro z
    rw [pow_one, hid z, Fintype.sum_sum_type]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
  obtain ⟨a', -, hlin⟩ := GlobalTheory.TranslLin.transl_lin p g _ φ c _ hEa (fun j => (gφ j).1) hEq
  choose B hB hBe using fun j => (gφ j).2
  have hS : BddSer (∑ j, PowerSeries.C (lamC g.lam (a' j)) * B j) :=
    bdd_sum _ _ fun j _ => bdd_mul (bdd_C _) (hB j)
  rw [hEe, hsgU, pow_one] at hlin
  simp only [hBe] at hlin
  set Bk : PowerSeries ℂ_[p] := (e ^ k)⁻¹ * g.atU G with hBk
  have hGe : g.atU G = e ^ k * Bk := by
    rw [hBk, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [map_pow, he0, one_pow]; exact one_ne_zero),
      one_mul]
  rw [hGe] at hlin
  set K := 2 * I + 3 - k with hKd
  have hK : K + k = 2 * I + 3 := Nat.sub_add_cancel hle
  have hsum : ∑ j, PowerSeries.C (lamC g.lam (a' j)) * (e ^ (2 * I + 3) * B j) =
      e ^ (2 * I + 3) * ∑ j, PowerSeries.C (lamC g.lam (a' j)) * B j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hleft : (PowerSeries.C ε * PowerSeries.X * e) ^ K * (e ^ k * Bk) =
      e ^ (2 * I + 3) * (PowerSeries.C (ε ^ K) * (PowerSeries.X ^ K * Bk)) := by
    rw [← hK, pow_add, map_pow]; ring
  have key := hleft.symm.trans (hlin.trans hsum)
  have key2 := mul_left_cancel₀ (pow_ne_zero _ he) key
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨Bk, ⟨C0, fun n => ?_⟩, hGe⟩
  have h1 := congrArg (PowerSeries.coeff (n + K)) key2
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h1
  have h2 := hC0 (n + K)
  rw [← h1, norm_mul, norm_pow, hu1, one_pow, one_mul] at h2
  exact h2

end GlobalTheory.ThetaOrderBdd
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaLevels

theorem bc_nsmul_left (D : D7) (T : Tor D) {N N' : ℕ} (n : ℕ) (x y : VC D N N') :
    bc D T (n • x) y = bc D T x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, bc_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, bc_add_left, ih, pow_succ]

theorem bc_nsmul_right (D : D7) (T : Tor D) {N N' : ℕ} (n : ℕ) (x y : VC D N N') :
    bc D T x (n • y) = bc D T x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, bc_zero_right, pow_zero]
  | succ n ih => rw [succ_nsmul, bc_add_right, ih, pow_succ]

theorem wd_entire (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (Wd D T x G) := by
  unfold Wd U Hf
  fun_prop

theorem levels_closed : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (L : Lat D N) (L' : Lat D N'), SD D L → SD D L' → ∀ F ∈ Th D (tor0 D cc δ) L L', F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ F ∈ TT D (tor0 D cc δ) N N', ∀ G ∈ TT D (tor0 D cc δ) N N', F + G ∈ TT D (tor0 D cc δ) N N') ∧ ∀ (a : ℂ), ∀ F ∈ TT D (tor0 D cc δ) N N', a • F ∈ TT D (tor0 D cc δ) N N' := by
  intro D cc δ hc N N'
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
    rw [← h2]; exact (h1 _).2
  have k : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, hSD N, hSD N', rfl⟩
  have n0 := GlobalTheory.ThetaTriple.nice_of_klat hc k
  refine ⟨fun L L' hL hL' F hF => ?_, fun z F hF => ?_, fun F hF G hG => ?_, fun a F hF => ?_⟩
  · have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
    have n1 := GlobalTheory.ThetaTriple.nice_of_klat hc k1
    obtain ⟨hd, hF⟩ := (n1.mem_ThSp F).1 hF
    refine ⟨hd, _, Nat.pos_of_ne_zero (GlobalTheory.ThetaTriple.index_ne_zero hc k1 k), fun x hx => hF _ ?_⟩
    exact AddSubgroup.nsmul_index_mem
      ((La D (tor0 D cc δ) L L').addSubgroupOf (La0 D (tor0 D cc δ) N N')) ⟨x, hx⟩
  · obtain ⟨hd, m, hm, hF⟩ := hF
    obtain ⟨n, hn, hz⟩ := GlobalTheory.ThetaInter.klat_mul_mem (GlobalTheory.InducedType.induced_type D).1.1 hc.1.1 k z
    change n • pt D (tor0 D cc δ) δ z ∈ _ at hz
    refine ⟨wd_entire D _ _ hd, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
    have hmx := AddSubgroup.nsmul_mem _ hx m
    have h1 : bc D (tor0 D cc δ) ((m * n) • x) (pt D (tor0 D cc δ) δ z) = 1 := by
      rw [mul_comm, mul_smul, bc_nsmul_left, ← bc_nsmul_right]
      exact n0.2.1 _ hmx _ hz
    have h2 : bc D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) ((m * n) • x) = 1 := by
      rw [mul_comm, mul_smul, bc_nsmul_right, ← bc_nsmul_left]
      exact n0.2.1 _ hz _ hmx
    have h3 : Wd D (tor0 D cc δ) ((m * n) • x) F = F := by
      rw [mul_smul]; exact hF _ (AddSubgroup.nsmul_mem _ hx n)
    have h4 := Wd_Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) ((m * n) • x) F
    rw [h3, h2, add_comm] at h4
    rw [Wd_Wd, h1, h4]
  · obtain ⟨hd, m, hm, hF⟩ := hF
    obtain ⟨hd', n, hn, hG⟩ := hG
    refine ⟨hd.add hd', m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
    have h1 : Wd D (tor0 D cc δ) ((m * n) • x) F = F := by
      rw [mul_smul]; exact hF _ (AddSubgroup.nsmul_mem _ hx n)
    have h2 : Wd D (tor0 D cc δ) ((m * n) • x) G = G := by
      rw [mul_comm, mul_smul]; exact hG _ (AddSubgroup.nsmul_mem _ hx m)
    rw [Wd_add, h1, h2]
  · obtain ⟨hd, m, hm, hF⟩ := hF
    exact ⟨hd.const_smul a, m, hm, fun x hx => by rw [Wd_smul, hF x hx]⟩

end GlobalTheory.ThetaLevels
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.kernelLattices_form_selfDual_triples : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → Nice D (tor0 D cc δ) A) ∧ (∀ A₁ A₂ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → (A₁.addSubgroupOf A₂).index ≠ 0) ∧ (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → ∀ e ∈ ThSp D (tor0 D cc δ) A, Iop D (tor0 D cc δ) A A e = e) ∧ ∀ A₁ A₂ A₃ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → ∃ μ, Trip D (tor0 D cc δ) A₁ A₂ A₃ e μ := by
  first | exact @GlobalTheory.ThetaTriple.klat_triples | exact GlobalTheory.ThetaTriple.klat_triples | (intros; apply GlobalTheory.ThetaTriple.klat_triples <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetRootChar

theorem circle_hom_factor {G B : Type} [Group G] [CommGroup B] (δ : G →* B) (m : G →* Circle)
    (h : ∀ g, δ g = 1 → m g = 1) : ∃ χ : B →* Circle, ∀ g, χ (δ g) = m g := by
  have hker : δ.rangeRestrict.ker ≤ m.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    exact h g (congrArg Subtype.val hg)
  obtain ⟨χ, hχ⟩ := GlobalTheory.circle_hom_extend_of_injective δ.range.subtype Subtype.val_injective
    (δ.rangeRestrict.liftOfSurjective δ.rangeRestrict_surjective ⟨m, hker⟩)
  refine ⟨χ, fun g => ?_⟩
  have := hχ (δ.rangeRestrict g)
  rw [MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply] at this
  exact this

theorem finPart_sigR (D : D7) (x : AE D) :
    finPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [finPart, sigR]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]

theorem finPart_det (D : D7) (V : HSp D) (g : GA D V) :
    finPart D ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det =
      ((Matrix.GeneralLinearGroup.det (finHom V g) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        Af D.host.F ⊗[D.host.F] D.host.E) := by
  rw [RingHom.map_det]
  rfl

theorem exists_idF_mul (D : D7) (x : (AE D)ˣ)
    (hx : sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) = finPart D (x : AE D)) :
    ∃ (a : (AF D.host.F)ˣ) (y : (AE D)ˣ), finPart D (y : AE D) = 1 ∧ x = y * idF D a := by
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add (f := _), hσ, add_comm]
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom x) hx
  have hb' : algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F) =
      finPart D (x : AE D) := congrArg Units.val hb
  let a : (AF D.host.F)ˣ :=
    ⟨((1 : Ainf D.host.F), (b : Af D.host.F)), ((1 : Ainf D.host.F), ((b⁻¹ : (Af D.host.F)ˣ) : Af D.host.F)),
      Prod.ext (mul_one _) b.mul_inv, Prod.ext (mul_one _) b.inv_mul⟩
  have ha : Units.map (finPart D).toMonoidHom (idF D a) = Units.map (finPart D).toMonoidHom x := by
    apply Units.ext
    change finPart D ((a : AF D.host.F) ⊗ₜ 1) = finPart D (x : AE D)
    rw [← hb']
    rfl
  refine ⟨a, x * (idF D a)⁻¹, ?_, by simp⟩
  have : Units.map (finPart D).toMonoidHom (x * (idF D a)⁻¹) = 1 := by
    rw [map_mul, map_inv, ha, mul_inv_cancel]
  exact congrArg Units.val this

theorem exists_finite_char : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle), (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → ∃ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) = ((c x : Circle) : ℂ) := by
  intro D V c hF hinf
  obtain ⟨hex, huniq, -, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D V
  choose r hr using hex
  have hval : ∀ g x, IsDetRoot V g x → c (r g) = c x := by
    intro g x hx
    obtain ⟨a, ha⟩ := huniq g _ _ (hr g) hx
    rw [ha, map_mul, hF, mul_one]
  have hm : ∀ g g', c (r (g * g')) = c (r g) * c (r g') := by
    intro g g'
    rw [hval _ _ (hmul _ _ _ _ (hr g) (hr g')), map_mul]
  let m : GA D V →* Circle := MonoidHom.mk' (fun g => c (r g)) hm
  obtain ⟨χ, hχ⟩ := circle_hom_factor (Matrix.GeneralLinearGroup.det.comp (finHom V)) m (by
    intro g hg
    have hg' : Matrix.GeneralLinearGroup.det (finHom V g) = 1 := hg
    have h1 := congrArg (finPart D) (hr g)
    rw [map_mul, finPart_det, hg', Units.val_one, one_mul, finPart_sigR] at h1
    obtain ⟨a, y, hy, hxy⟩ := exists_idF_mul D (r g) h1.symm
    change c (r g) = 1
    rw [hxy, map_mul, hF, hinf y hy, mul_one])
  refine ⟨Circle.toUnits.comp χ, fun g x hx => ?_⟩
  have : χ (Matrix.GeneralLinearGroup.det (finHom V g)) = c x := (hχ g).trans (hval g x hx)
  rw [MonoidHom.comp_apply, this]
  simp

end GlobalTheory.DetRootChar
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdeleDiv

theorem exists_infAdele_pow_eq (D : D7) (n : ℕ) (hn : 0 < n)
    (z : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E) :
    ∃ w : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E, w ^ n = z := by
  obtain ⟨⟨θ, hθ⟩, H⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨-, -, hb⟩ := H θ hθ
  choose r hr using fun τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} =>
    IsAlgClosed.exists_pow_nat_eq (θ τ.1 z) hn
  obtain ⟨w, hw⟩ := hb.2 r
  refine ⟨w, hb.1 ?_⟩
  funext τ
  have h1 : θ τ.1 w = r τ := congrFun hw τ
  change θ τ.1 (w ^ n) = θ τ.1 z
  rw [map_pow, h1, hr]

theorem exists_pow_eq_of_finPart_eq_one : ∀ (D : D7) (n : ℕ), 0 < n → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → ∃ y : (AE D)ˣ, y ^ n = x := by
  intro D n hn x hx
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨w, hw⟩ := exists_infAdele_pow_eq D n hn (e (x : AE D)).1
  have h2 : (e (x : AE D)).2 = 1 := (he _).2.trans hx
  have hy : (e.symm (w, 1)) ^ n = (x : AE D) := by
    apply e.injective
    rw [map_pow, RingEquiv.apply_symm_apply]
    exact Prod.ext hw (by rw [h2]; exact one_pow n)
  have hu : IsUnit (e.symm (w, 1)) := (isUnit_pow_iff hn.ne').1 (hy ▸ x.isUnit)
  obtain ⟨y, hy'⟩ := hu
  refine ⟨y, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hy']
  exact hy

end GlobalTheory.IdeleDiv
end
