module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle314
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle273
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle264
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle277
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle295
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle278
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle256
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle303
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.cup_kummer_dlog_mod_primePow_levelL : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ ι : On p L →ₐ[O0 p] Ω, IsEmb T L ι →
  ∀ (u v : (On p L)ˣ) (α β α' β' : On p L), IsDlog p L (u : On p L) α β → IsDlog p L (v : On p L) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = ι u → s ^ (p ^ n) = ι v →
  ∀ a b lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T L) r a → IsKum T n (Gn T L) s b → IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c * (((a g).val : Ω) * ((b h).val : Ω)) + (p : Ω) ^ c * ι (α * β' - β * α') * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  first | exact @GlobalTheory.K5.LevelDown.cup_kummer_dlog_mod | exact GlobalTheory.K5.LevelDown.cup_kummer_dlog_mod | (intros; apply GlobalTheory.K5.LevelDown.cup_kummer_dlog_mod <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaTransl
open GlobalTheory.EvenTheta

variable {p : ℕ} [Fact p.Prime]

def GoodAt (g : GL3Theta.G1 p) (k : ℕ) (F : ℂ → ℂ) : Prop :=
  AlgEnt F ∧ ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU F = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B

theorem bdd_mul {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f * h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).2.2

theorem bdd_add {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f + h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).1

theorem bdd_sub {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f - h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).2.1

theorem bdd_C (c : ℂ_[p]) : BddSer (PowerSeries.C c) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 c).1

theorem bdd_X : BddSer (PowerSeries.X : PowerSeries ℂ_[p]) :=
  ⟨1, (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1⟩

theorem bdd_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℂ_[p]) (h : ∀ i ∈ s, BddSer (f i)) :
    BddSer (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact bdd_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem lamC_one (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  have h : (1 : ℂ) ∈ Qbar := one_mem _
  rw [lamC, dite_eq_left h]
  exact map_one lam

theorem good_mul {g : GL3Theta.G1 p} {k l : ℕ} {F G : ℂ → ℂ} (hF : GoodAt g k F) (hG : GoodAt g l G) :
    GoodAt g (k + l) (fun z => F z * G z) := by
  obtain ⟨hFa, B, hB, hFe⟩ := hF
  obtain ⟨hGa, B', hB', hGe⟩ := hG
  obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 F G hFa hGa).1
  refine ⟨ha, B * B', bdd_mul hB hB', ?_⟩
  rw [he, hFe, hGe, pow_add]
  ring

theorem good_one (g : GL3Theta.G1 p) : GoodAt g 0 (fun _ => (1 : ℂ)) := by
  obtain ⟨ha, he⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
  refine ⟨ha, 1, ?_, ?_⟩
  · simpa using bdd_C (p := p) 1
  · rw [he, lamC_one, map_one, pow_zero, one_mul]

theorem good_pow {g : GL3Theta.G1 p} {k : ℕ} {F : ℂ → ℂ} (hF : GoodAt g k F) (n : ℕ) :
    GoodAt g (k * n) (fun z => F z ^ n) := by
  induction n with
  | zero => simpa using good_one g
  | succ n ih =>
    have := good_mul ih hF
    simp only [← pow_succ] at this
    rwa [show k * n + k = k * (n + 1) by ring] at this

theorem good_congr {g : GL3Theta.G1 p} {k l : ℕ} {F : ℂ → ℂ} (h : GoodAt g k F) (e : k = l) : GoodAt g l F :=
  e ▸ h

theorem atU_mul_pow {g : GL3Theta.G1 p} {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) (m n : ℕ) :
    AlgEnt (fun z => F z ^ m * G z ^ n) ∧ g.atU (fun z => F z ^ m * G z ^ n) = g.atU F ^ m * g.atU G ^ n := by
  have hpow : ∀ {H : ℂ → ℂ}, AlgEnt H → ∀ k : ℕ, AlgEnt (fun z => H z ^ k) ∧
      g.atU (fun z => H z ^ k) = g.atU H ^ k := by
    intro H hH k
    induction k with
    | zero =>
      obtain ⟨ha, he⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
      simp only [pow_zero]
      exact ⟨ha, by rw [he, lamC_one, map_one]⟩
    | succ k ih =>
      obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 _ H ih.1 hH).1
      simp only [pow_succ]
      exact ⟨ha, by rw [he, ih.2]⟩
  obtain ⟨h1, e1⟩ := hpow hF m
  obtain ⟨h2, e2⟩ := hpow hG n
  obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 _ _ h1 h2).1
  exact ⟨ha, by rw [he, e1, e2]⟩



theorem tau_pow_bdd : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∀ N : ℕ, 0 < N → (N : ℂ) * t ∈ g.abelian₂ →
      GlobalTheory.EvenTheta.BddSer (GlobalTheory.ThetaTransl.tau g t ^ N) := by
  intro D p _ cc δ g hg t ht N hN hNt
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  have hU0 : U1 g.abelian₂ 0 (sgStar g.abelian₂) = sgStar g.abelian₂ := by
    funext z; simp [U1]
  have hsg : AlgEnt (sgStar g.abelian₂) := hU0 ▸ halg 0 ⟨1, one_pos, by simp⟩
  have htq : InRationalLattice g.abelian₂ t := ⟨N, hN, hNt⟩
  have hP := halg t htq
  have htn := ht.1
  have hwt : wpF g.abelian₂ t ∈ Qbar := (hwp t htq htn).1
  obtain ⟨hu1, hwq1, -, he0, hsgU⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he_def
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε_def
  have he : e ≠ 0 := fun h => by rw [h, map_zero] at he0; exact zero_ne_one he0
  have gσ : GoodAt g 1 (sgStar g.abelian₂) :=
    ⟨hsg, PowerSeries.C ε * PowerSeries.X, bdd_mul (bdd_C ε) bdd_X, by rw [hsgU]; ring⟩
  obtain ⟨hSa, hSe⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg t htn hwt
  have gS : GoodAt g 2 (sqTh g.abelian₂ t) := ⟨hSa, lineSer g.wq⁻¹ (xAt g t),
    bdd_sub ⟨1, hwq1⟩ (bdd_mul (bdd_C _) (by rw [sq]; exact bdd_mul (bdd_X (p := p)) (bdd_X (p := p)))), hSe⟩
  obtain ⟨hTa, w, hw, hTe⟩ := GlobalTheory.T.sigmaStarCubeDerivWeierstrassP_parameterSeries_bounded p g hok hlat' h2 h3 hdisc hsg t htn hwt
  have gT : GoodAt g 3 (sqThD g.abelian₂ t) := ⟨hTa, w, hw, hTe⟩
  obtain ⟨I, a, b, hle, hid⟩ := GlobalTheory.T.exists_sigmaStar_translate_pow_decomposition g.abelian₂ hlat' t N hN hNt t htn
  let φ : Fin (I + 1) ⊕ Fin (I + 1) → ℂ → ℂ := Sum.elim
    (fun i z => sgStar g.abelian₂ z ^ (2 * (I - (i : ℕ)) + 3) * sqTh g.abelian₂ t z ^ (i : ℕ))
    (fun j z => sgStar g.abelian₂ z ^ (2 * (I - (j : ℕ))) * sqTh g.abelian₂ t z ^ (j : ℕ) * sqThD g.abelian₂ t z)
  let c : Fin (I + 1) ⊕ Fin (I + 1) → ℂ := Sum.elim (fun i => a i) (fun j => b j)
  have gφ : ∀ k, GoodAt g (2 * I + 3) (φ k) := by
    rintro (i | j)
    · have hi := i.isLt
      exact good_congr (good_mul (good_pow gσ (2 * (I - (i : ℕ)) + 3)) (good_pow gS (i : ℕ))) (by omega)
    · have hj := j.isLt
      exact good_congr (good_mul (good_mul (good_pow gσ (2 * (I - (j : ℕ)))) (good_pow gS (j : ℕ))) gT)
        (by omega)
  obtain ⟨hEa, hEe⟩ := atU_mul_pow (g := g) hsg hP (2 * I + 3 - N) N
  have hEq : ∀ z, sgStar g.abelian₂ z ^ (2 * I + 3 - N) * U1 g.abelian₂ t (sgStar g.abelian₂) z ^ N = ∑ k, c k * φ k z := by
    intro z
    rw [hid z, Fintype.sum_sum_type]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
  obtain ⟨a', -, hlin⟩ := GlobalTheory.T.algebraicTaylorCombination_parameterSeries_algebraic p g _ φ c _ hEa (fun k => (gφ k).1) hEq
  choose B hB hBe using fun k => (gφ k).2
  have hS : BddSer (∑ k, PowerSeries.C (lamC g.lam (a' k)) * B k) :=
    bdd_sum _ _ fun k _ => bdd_mul (bdd_C _) (hB k)
  rw [hEe, hsgU] at hlin
  simp only [hBe] at hlin
  have hPe : g.atU (U1 g.abelian₂ t (sgStar g.abelian₂)) = e * tau g t := by
    rw [tau, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [he0]; exact one_ne_zero), one_mul]
  rw [hPe] at hlin
  set K := 2 * I + 3 - N with hKd
  have hK : K + N = 2 * I + 3 := Nat.sub_add_cancel hle
  have hsum : ∑ k, PowerSeries.C (lamC g.lam (a' k)) * (e ^ (2 * I + 3) * B k) =
      e ^ (2 * I + 3) * ∑ k, PowerSeries.C (lamC g.lam (a' k)) * B k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have hleft : (PowerSeries.C ε * PowerSeries.X * e) ^ K * (e * tau g t) ^ N =
      e ^ (2 * I + 3) * (PowerSeries.C (ε ^ K) * (PowerSeries.X ^ K * tau g t ^ N)) := by
    rw [← hK, pow_add, map_pow]; ring
  have key := hleft.symm.trans (hlin.trans hsum)
  have key2 := mul_left_cancel₀ (pow_ne_zero _ he) key
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨C0, fun n => ?_⟩
  have h1 := congrArg (PowerSeries.coeff (n + K)) key2
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h1
  have h2 := hC0 (n + K)
  rw [← h1, norm_mul, norm_pow, hu1, one_pow, one_mul] at h2
  exact h2

end GlobalTheory.ThetaTransl
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

namespace GlobalTheory.FrobStick.AtData

theorem weierstrass_translate_zero_eq_self (Λ : AddSubgroup ℂ) (F : ℂ → ℂ) : U1 Λ 0 F = F := by
  funext z; simp [U1]

theorem half_gen {Λ : AddSubgroup ℂ} (hlat : IsLat Λ) : ∃ v : ℂ, v ∉ Λ ∧ InRationalLattice Λ v := by
  obtain ⟨w₁, w₂, hli, rfl⟩ := hlat
  refine ⟨w₁ / 2, ?_, ⟨2, by norm_num, ?_⟩⟩
  · intro h
    rw [AddSubgroup.mem_closure_pair] at h
    obtain ⟨m, n, hmn⟩ := h
    have key := (LinearIndependent.pair_iff.1 hli) ((m : ℝ) - 1 / 2) (n : ℝ) (by
      have e : (m : ℂ) * w₁ + (n : ℂ) * w₂ = w₁ / 2 := by simpa [zsmul_eq_mul] using hmn
      simp only [Complex.real_smul]
      push_cast
      linear_combination e)
    have h1 : (m : ℝ) = 1 / 2 := by linarith [key.1]
    have h2 : (2 * m : ℝ) = 1 := by linarith
    have h3 : (2 * m : ℤ) = 1 := by exact_mod_cast h2
    omega
  · have : (2 : ℂ) * (w₁ / 2) = w₁ := by ring
    push_cast
    rw [this]
    exact AddSubgroup.subset_closure (by simp)

theorem atData : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → IsWq g.W g.wq ∧ IsLat g.abelian₂ ∧ g2 g.abelian₂ ∈ Qbar ∧ g3 g.abelian₂ ∈ Qbar ∧ AlgEnt (sgStar g.abelian₂) ∧ ∃ v : ℂ, v ∉ g.abelian₂ ∧ wpF g.abelian₂ v ∈ Qbar := by
  intro D p _ cc δ g hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  obtain ⟨v, hv, hvq⟩ := half_gen hlat'
  refine ⟨hok.2.1, hlat', h2, h3, ⟨hlat'.differentiable, fun n => ?_⟩, v, hv, (hwp v hvq hv).1⟩
  have := huse 0 ⟨1, one_pos, by simp⟩ n
  rwa [weierstrass_translate_zero_eq_self] at this

end GlobalTheory.FrobStick.AtData
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTriple

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem theta_cocycle_eq_exp_hermitian (T : Tor D) (x y : VC D N N') :
    bc D T x y = Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T (w0 D • x) y).im : ℂ)) := by
  have h : Hf D T (w0 D • x) y = w0 D * Hf D T x y := by
    rw [GlobalTheory.ThetaLine.Hf_eq, GlobalTheory.ThetaLine.sq_smul_left, GlobalTheory.ThetaLine.Hf_eq, mul_div_assoc]
  have h1 : (w0 D).re = 1 / 2 := by simp [w0]
  have h2 : (w0 D).im = Real.sqrt D.host.d / 2 := by simp [w0]
  rw [bc, h, Complex.mul_im, h1, h2]
  congr 1
  push_cast
  ring

theorem nice_of_klat (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    Nice D (tor0 D cc δ) A := by
  obtain ⟨-, h0, h1, h2, -, -, -⟩ :=
    GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h0, fun x hx y hy => ?_, fun x hx => h2 x fun y hy => ?_⟩
  · obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have hw := GlobalTheory.ThetaInter.klat_smul_mem hA a hx
    rw [ha] at hw
    obtain ⟨m, hm⟩ := h1 _ hw y hy
    rw [theta_cocycle_eq_exp_hermitian, hm, Complex.exp_eq_one_iff]
    exact ⟨-m, by push_cast; ring⟩
  · have h := hx y hy
    rw [bc_comm, mul_eq_right₀ (bc_ne_zero _ _ _ _), Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨-n, ?_⟩
    have h3 : (2 * (Real.pi : ℂ) * Complex.I) * ((Hf D (tor0 D cc δ) x y).im : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) * ((-n : ℤ) : ℂ) := by
      push_cast
      linear_combination -hn
    exact_mod_cast mul_left_cancel₀ Complex.two_pi_I_ne_zero h3

theorem index_ne_zero (hc : Crv D cc δ) {A₁ A₂ : AddSubgroup (VC D N N')} (h₁ : KLat D (tor0 D cc δ) A₁)
    (h₂ : KLat D (tor0 D cc δ) A₂) : (A₁.addSubgroupOf A₂).index ≠ 0 := by
  haveI := GlobalTheory.ThetaInter.klat_finite (GlobalTheory.InducedType.induced_type D).1.1 hc.1.1 h₁ h₂
    (GlobalTheory.ThetaInter.klat_facts hc h₂).1
  exact AddSubgroup.index_ne_zero_of_finite

theorem iop_self {T : Tor D} {A : AddSubgroup (VC D N N')} (hA : Nice D T A) {e : VC D N N' → ℂ}
    (he : e ∈ ThSp D T A) : Iop D T A A e = e := by
  rw [hA.Iop_eq]
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by simp
  have hc : Nat.card (A ⧸ A.addSubgroupOf A) = 1 := hi
  obtain ⟨hs, ⟨q₀⟩⟩ := Nat.card_eq_one_iff_unique.1 hc
  rw [finsum_eq_single _ q₀ (fun q hq => absurd (Subsingleton.elim q q₀) hq), hi,
    ((hA.mem_ThSp e).1 he).2 _ (Quotient.out q₀ : A).2]
  simp

theorem klat_triples : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → Nice D (tor0 D cc δ) A) ∧ (∀ A₁ A₂ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → (A₁.addSubgroupOf A₂).index ≠ 0) ∧ (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → ∀ e ∈ ThSp D (tor0 D cc δ) A, Iop D (tor0 D cc δ) A A e = e) ∧ ∀ A₁ A₂ A₃ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → ∃ μ, Trip D (tor0 D cc δ) A₁ A₂ A₃ e μ := by
  intro D cc δ hc N N'
  refine ⟨fun A hA => nice_of_klat hc hA, fun A₁ A₂ h₁ h₂ _ _ _ => index_ne_zero hc h₁ h₂,
    fun A hA e he => iop_self (nice_of_klat hc hA) he, fun A₁ A₂ A₃ h₁ h₂ h₃ e he h0 => ?_⟩
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.TripleIntertwiner.triple_constant D cc δ hc N N' A₁ A₂ A₃ h₁ h₂ h₃ e he
  exact ⟨μ, nice_of_klat hc h₁, nice_of_klat hc h₂, nice_of_klat hc h₃, index_ne_zero hc h₁ h₂,
    index_ne_zero hc h₂ h₃, index_ne_zero hc h₁ h₃, he, h0, hμ, h⟩

end GlobalTheory.ThetaTriple
end
end

section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

theorem _root_.GlobalTheory.T.exists_symmetric_elementaryDivisors_unitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ d : List ℤ, GlobalTheory.InertThetaCompare.Good n d ∧ ∃ a ∈ GLint (Fin n) (intL L), ∃ b ∈ GLint (Fin n) (intL L), ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (a : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * (b : Matrix (Fin n) (Fin n) L) := by
  first | exact @GlobalTheory.LFun.UnitaryDiv.exists_good_div | exact GlobalTheory.LFun.UnitaryDiv.exists_good_div | (intros; apply GlobalTheory.LFun.UnitaryDiv.exists_good_div <;> assumption)
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.DefiniteOrthonormal

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_orthonormal (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W : Formalism.BasicNotions.HSpace E) (hs : W.SigOK)
    (hp : ∀ τ : E →+* ℂ, W.sig τ = (W.rank, 0)) :
    ∃ b : Fin W.rank → W.V, LinearIndependent E b ∧
      ∀ a c, W.hT (b a) (b c) = if a = c then 1 else 0 := by
  obtain ⟨e, he⟩ := GlobalTheory.DefiniteMass.exists_isometry hc W hs hp
  refine ⟨(Pi.basisFun E (Fin W.rank)).map e.symm, Module.Basis.linearIndependent _, fun a c => ?_⟩
  rw [← he]
  simp only [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  change ∑ i, star ((Pi.single a (1 : E) : Fin W.rank → E) i) * (Pi.single c (1 : E) : Fin W.rank → E) i = _
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply]
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · simp

end

theorem landherrHasse : ∀ D : D7, LandherrHasse D := fun D =>
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W hs hp => exists_orthonormal (E := D.host.E) D.sp.cm.cmUnram W hs hp

end GlobalTheory.DefiniteOrthonormal
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem genusMassStd (D : D7) : GenusMassStd D :=
  GlobalTheory.DefiniteMass.mass_eq_massI D

theorem genusMassStd_of_landherrHasse :
    (∀ D : D7, LandherrHasse D) → ∀ D : D7, GenusMassStd D :=
  fun _ D => genusMassStd D

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharOrderFin

theorem locK_pow_eq_one {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ}
    (h : χ.OrderDvd n) (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : χ.locK P k ^ n = 1 := by
  have h1 : (χ.1 : _ →* ℂˣ) ^ n = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  have h2 : ∀ y, χ.1 y ^ n = 1 := fun y => by
    have := DFunLike.congr_fun h1 y
    simpa [MonoidHom.pow_apply] using this
  exact h2 _

theorem char_pow_eq_one_of_orderDvd : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E),
    ChrEq c χ → ∀ n : ℕ, χ.OrderDvd n → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x ^ n = 1 := by
  intro D c χ hc n hn x hx
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.T.exists_finitePlaceIdempotent_baseChangeAdeles D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 c χ hc
  let y : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨ι (finPart D (x : AE D)), ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)),
      by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one],
      by rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]⟩
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN y
  have h5 := hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Circle.ext
  have h6 : ((c x ^ n : Circle) : ℂ) = ((c x : Circle) : ℂ) ^ n :=
    map_pow Circle.coeHom (c x) n
  rw [h6, h5, ← Finset.prod_pow, Circle.coe_one]
  refine Finset.prod_eq_one fun P _ => ?_
  rw [← Units.val_pow_eq_pow_val, locK_pow_eq_one hn, Units.val_one]

end GlobalTheory.CharOrderFin
end
