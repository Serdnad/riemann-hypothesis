module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle121
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle225
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle118
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle123
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle101
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle120
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle197
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle221
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.MatchAdd.integrable_of_isTest {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : IsTest f) :
    Integrable f μ :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

theorem GlobalTheory.JR.match_add : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f₁' f₂' : Gl r F → ℂ) (f₁ f₂ : Hn r F E → ℂ), IsTest f₁' → IsTest f₂' → IsTest f₁ → IsTest f₂ → Match M f₁' f₁ → Match M f₂' f₂ → Match M (f₁' + f₂') (f₁ + f₂) := by
  intro F E _ _ _ _ _ r M f₁' f₂' f₁ f₂ h₁' h₂' h₁ h₂ m₁ m₂ a ha
  obtain ⟨hG, hU⟩ := GlobalTheory.T.jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport F E r M
  obtain ⟨-, hsec, -⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r
  have ha' : Delta (inv (sec a)) ≠ 0 := by rw [hsec]; exact ha
  have eG : orbG M (f₁' + f₂') (sec a) = orbG M f₁' (sec a) + orbG M f₂' (sec a) := by
    letI := M.mG
    haveI := M.bG
    haveI := M.haarG
    unfold orbG
    simp only [Pi.add_apply, add_mul]
    exact integral_add (MatchAdd.integrable_of_isTest _ (hG _ h₁' _ ha'))
      (MatchAdd.integrable_of_isTest _ (hG _ h₂' _ ha'))
  have eU : ∀ X : Hn r F E, HasInv X a → orbU M (f₁ + f₂) X = orbU M f₁ X + orbU M f₂ X := by
    intro X hX
    letI := M.mU
    haveI := M.bU
    haveI := M.haarU
    unfold orbU
    simp only [Pi.add_apply]
    exact integral_add (MatchAdd.integrable_of_isTest _ (hU _ h₁ a X ha hX))
      (MatchAdd.integrable_of_isTest _ (hU _ h₂ a X ha hX))
  refine ⟨fun X hX => ?_, fun hn => ?_⟩
  · rw [eG, eU X hX, (m₁ a ha).1 X hX, (m₂ a ha).1 X hX]
  · rw [eG, (m₁ a ha).2 hn, (m₂ a ha).2 hn, add_zero]
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial

namespace GlobalTheory.JR.DenseMatch

theorem charpoly_companion {k : Type} [CommRing k] :
    ∀ (r : ℕ) (p : Fin r → k), (companion p).charpoly = X ^ r + ∑ i : Fin r, C (p i) * X ^ (i : ℕ) := by
  intro r
  induction r with
  | zero => intro p; simp [Matrix.charpoly, Matrix.det_isEmpty]
  | succ s ih =>
    cases s with
    | zero =>
      intro p
      simp [Matrix.charpoly, Matrix.det_unique, charmatrix_apply, companion]
    | succ n =>
      intro p
      have h00 : (charmatrix (companion p)).submatrix Fin.succ Fin.succ
          = charmatrix (companion (fun i : Fin (n + 1) => p i.succ)) := by
        ext i j
        simp only [submatrix_apply, charmatrix_apply, companion, of_apply, diagonal_apply, Fin.succ_inj,
          Fin.val_succ]
        split_ifs <;> first | rfl | simp_all | omega
      have hlast : ((charmatrix (companion p)).submatrix Fin.succ (Fin.last (n + 1)).succAbove).det
          = (-1) ^ (n + 1) := by
        rw [Fin.succAbove_last, Matrix.det_of_upperTriangular]
        · have : ∀ i : Fin (n + 1), (charmatrix (companion p)).submatrix Fin.succ Fin.castSucc i i = -1 := by
            intro i
            simp only [submatrix_apply, charmatrix_apply, companion, of_apply, diagonal_apply]
            split_ifs <;> simp_all [Fin.ext_iff] <;> omega
          simp only [submatrix_apply] at this
          simp [this]
        · intro i j hij
          simp only [submatrix_apply, charmatrix_apply, companion, of_apply, diagonal_apply]
          have : (j : ℕ) < i := hij
          split_ifs <;> simp_all [Fin.ext_iff] <;> omega
      rw [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
        Finset.sum_eq_single (Fin.last n)]
      · rw [Fin.succAbove_zero, h00, ← Matrix.charpoly, ih, Fin.succ_last, hlast]
        have e1 : charmatrix (companion p) 0 0 = X := by
          simp [charmatrix_apply, companion]
        have e2 : charmatrix (companion p) 0 (Fin.last (n + 1)) = C (p 0) := by
          simp [charmatrix_apply, companion, Fin.ext_iff]
        rw [e1, e2, Fin.sum_univ_succ (n := n + 1)]
        simp only [Fin.val_last, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
        have : ((-1 : k[X]) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; simp
        have e3 : ∑ x : Fin (n + 1), C (p x.succ) * X ^ ((x : ℕ) + 1)
            = X * ∑ i : Fin (n + 1), C (p i.succ) * X ^ (i : ℕ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
        rw [e3, Nat.succ_eq_add_one]
        linear_combination C (p 0) * this
      · intro j _ hj
        have : charmatrix (companion p) 0 j.succ = 0 := by
          have hjn : (j : ℕ) ≠ n := fun h => hj (Fin.ext (by simp [h]))
          rw [charmatrix_apply, diagonal_apply_ne _ (Fin.succ_ne_zero j).symm]
          simp only [companion, of_apply, Fin.val_succ, Fin.val_zero]
          rw [if_neg (by omega)]
          simp
        rw [this, mul_zero, zero_mul]
      · simp

end GlobalTheory.JR.DenseMatch

namespace GlobalTheory.JR.DenseMatch

theorem finite_not_separable_add_C {F : Type} [Field F] [CharZero F] (P : F[X]) :
    {t : F | ¬ (P + C t).Separable}.Finite := by
  by_cases hd : derivative P = 0
  · obtain ⟨c, rfl⟩ : ∃ c, P = C c := ⟨P.coeff 0, eq_C_of_derivative_eq_zero hd⟩
    refine (Set.finite_singleton (-c)).subset fun t ht => ?_
    simp only [Set.mem_setOf_eq, ← C_add, separable_C, isUnit_iff_ne_zero, not_not] at ht
    simp only [Set.mem_singleton_iff]; linear_combination ht
  · let K := AlgebraicClosure F
    have hfin : ((fun α : K => -aeval α P) '' (derivative P).rootSet K).Finite :=
      ((derivative P).rootSet_finite K).image _
    refine (hfin.preimage (algebraMap F K).injective.injOn).subset fun t ht => ?_
    simp only [Set.mem_setOf_eq, separable_def, isCoprime_iff_aeval_ne_zero_of_isAlgClosed F K,
      not_forall, not_or, not_not, derivative_add, derivative_C, add_zero] at ht
    obtain ⟨α, h1, h2⟩ := ht
    refine ⟨α, ?_, ?_⟩
    · rw [mem_rootSet]; exact ⟨hd, h2⟩
    · simp only [map_add (f := _), aeval_C] at h1
      linear_combination -h1

theorem frequently_of_curve {Y F : Type} [TopologicalSpace Y] [NontriviallyNormedField F] (γ : F → Y)
    (hγ : Continuous γ) (x₀ : Y) (h0 : γ 0 = x₀) (P : Y → Prop) (hfin : {t | ¬ P (γ t)}.Finite) :
    ∃ᶠ x in 𝓝 x₀, P x := by
  intro hne
  have h1 : ∀ᶠ t in 𝓝[≠] (0 : F), ¬ P (γ t) :=
    ((h0 ▸ hγ.tendsto 0).mono_left nhdsWithin_le_nhds).eventually hne
  have h2 : ∀ᶠ t in 𝓝[≠] (0 : F), t ∉ {t | ¬ P (γ t)} := by
    have hc : IsClosed ({t | ¬ P (γ t)} \ {0}) := (hfin.subset Set.diff_subset).isClosed
    have : ∀ᶠ t in 𝓝 (0 : F), t ∉ ({t | ¬ P (γ t)} \ {0}) := hc.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with t ht ht0
    exact fun hb => ht ⟨hb, ht0⟩
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  exact ht2 ht1

theorem continuous_Delta {r : ℕ} {F : Type} [NontriviallyNormedField F] :
    Continuous (fun a : Inv r F => Delta a) := by
  have hc : Continuous (fun p : Fin r → F => companion p) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [companion, of_apply]
    split_ifs
    · exact (continuous_apply i).neg
    · exact continuous_const
    · exact continuous_const
  have hc' : Continuous (fun a : Inv r F => companion a.1) := hc.comp continuous_fst
  unfold Delta
  apply Continuous.matrix_det
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [hankel, of_apply, mom, sec]
  exact (continuous_snd.fst).dotProduct ((hc'.pow _).matrix_mulVec continuous_const)

end GlobalTheory.JR.DenseMatch

namespace GlobalTheory.JR.DenseMatch

theorem frequently_separable {F : Type} [NontriviallyNormedField F] [CharZero F] :
    ∀ (r : ℕ) (a₀ : Inv r F), ∃ᶠ a in 𝓝 a₀, (companion a.1).charpoly.Separable
  | 0, a₀ => (Eventually.of_forall fun a => by rw [charpoly_companion]; simp).frequently
  | s + 1, a₀ => by
    have key : ∀ t : F, (companion (a₀.1 + Pi.single 0 t)).charpoly = (companion a₀.1).charpoly + C t := by
      intro t
      rw [charpoly_companion, charpoly_companion, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp [Pi.single_apply, Fin.succ_ne_zero]
      ring
    have hs : Continuous (fun t : F => (Pi.single 0 t : Fin (s + 1) → F)) :=
      continuous_pi fun i => by simp only [Pi.single_apply]; split_ifs <;> fun_prop
    refine frequently_of_curve (fun t : F => ((a₀.1 + Pi.single 0 t, a₀.2) : Inv (s + 1) F)) (by fun_prop) a₀
      (by simp) (fun a => (companion a.1).charpoly.Separable) ?_
    refine (finite_not_separable_add_C (companion a₀.1).charpoly).subset fun t ht => ?_
    simpa [key] using ht

theorem frequently_mom_ne_zero {F : Type} [NontriviallyNormedField F] (s : ℕ) (a₀ : Inv (s + 1) F) :
    ∃ᶠ a in 𝓝 a₀, mom (sec a) 0 ≠ 0 := by
  have key : ∀ a : Inv (s + 1) F, mom (sec a) 0 = a.2.1 0 := by
    intro a; simp [mom, sec, dotProduct, Fin.sum_univ_succ, Fin.succ_ne_zero]
  have hs : Continuous (fun t : F => (Pi.single 0 t : Fin (s + 1) → F)) :=
    continuous_pi fun i => by simp only [Pi.single_apply]; split_ifs <;> fun_prop
  refine frequently_of_curve (fun t : F => ((a₀.1, a₀.2.1 + Pi.single 0 t, a₀.2.2) : Inv (s + 1) F))
    (by fun_prop) a₀ (by simp) (fun a => mom (sec a) 0 ≠ 0) ?_
  refine (Set.finite_singleton (-a₀.2.1 0)).subset fun t ht => ?_
  simp only [Set.mem_setOf_eq, key, not_not, Pi.add_apply, Pi.single_eq_same] at ht
  simp only [Set.mem_singleton_iff]; linear_combination ht

theorem match_of_frequently {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ)
    (hf' : IsTest f') (hf : IsTest f) (G : Inv r F → Prop) (hG : ∀ a₀ : Inv r F, ∃ᶠ a in 𝓝 a₀, G a)
    (h : ∀ a : Inv r F, Delta a ≠ 0 → G a → MatchAt M f' f a) : Match M f' f := by
  intro a₀ hΔ
  have hcont : ∀ᶠ a in 𝓝 a₀, Delta a ≠ 0 := continuous_Delta.continuousAt.eventually_ne hΔ
  have hL7 := GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E r M
  have hO := hL7.2.2.1 f' hf' a₀ hΔ
  constructor
  · intro X hX
    have hU := hL7.2.2.2 f hf a₀ X hΔ hX
    obtain ⟨a, ha1, ha2, ha3, ⟨X', hX'⟩, hUX⟩ := ((hG a₀).and_eventually (hcont.and (hO.and hU))).exists
    rw [← ha3, (h a ha2 ha1).1 X' hX', hUX X' hX']
  · intro hno
    have h5 := (GlobalTheory.T.invariant_image_openClosed_local_sections F E r a₀ hΔ).1 hno
    obtain ⟨a, ha1, ha2, ha3, ha4⟩ := ((hG a₀).and_eventually (hcont.and (hO.and h5))).exists
    rw [← ha3]
    exact (h a ha2 ha1).2 ha4

theorem match_of_dense : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ),
    IsTest f' → IsTest f →
      ((∀ a : Inv r F, Delta a ≠ 0 → (companion a.1).charpoly.Separable → MatchAt M f' f a) → Match M f' f) ∧
      (0 < r → (∀ a : Inv r F, Delta a ≠ 0 → mom (sec a) 0 ≠ 0 → MatchAt M f' f a) → Match M f' f) := by
  intro F E _ _ _ _ _ r M f' f hf' hf
  haveI : CharZero F := Unram.charZero (F := F) (E := E)
  refine ⟨fun h => match_of_frequently M f' f hf' hf _ (frequently_separable r) h, fun hr h => ?_⟩
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr.ne'
  exact match_of_frequently M f' f hf' hf _ (frequently_mom_ne_zero s) h

end GlobalTheory.JR.DenseMatch
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem sl2Map_nS {F K : Type} [Field F] [CommRing K] [Algebra F K] (t : F) :
    SpecialLinearGroup.map (algebraMap F K) (nS t) = nS (algebraMap F K t) := by
  apply Subtype.ext
  show (algebraMap F K).mapMatrix !![1, t; 0, 1] = !![1, algebraMap F K t; 0, 1]
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem sl2Map_wS {F K : Type} [Field F] [CommRing K] [Algebra F K] :
    SpecialLinearGroup.map (algebraMap F K) (wS F) = wS K := by
  apply Subtype.ext
  show (algebraMap F K).mapMatrix !![0, 1; -1, 0] = !![0, 1; -1, 0]
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem weilSL2_hermitian : WeilEt → GammaOne → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Hn r F E → ℂ) → Hn r F E → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t X, W (nS t) f X = ψ (t * Algebra.trace F E (star X.2.1 ⬝ᵥ X.2.1) / 2) * f X) ∧ W (wS F) f = fourU M ψ f := by
  intro hW hG F E _ _ _ _ _ r M ψ hψ
  obtain ⟨A, e, j, hj, hNe⟩ := GlobalTheory.T.exists_split_etaleHermitianPair_isometry F E r
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : SecondCountableTopology E := secondCountable_of_proper
  haveI : CharZero F := Unram.charZero (E := E)
  letI mE : MeasurableSpace E := M.mE
  haveI : BorelSpace E := M.bE
  obtain ⟨hjc, hjsc⟩ := GlobalTheory.T.finiteEtaleHermitian_linearEquiv_continuous F E A r j
  let jh : A.L ≃ₜ (Fin r → E) := { j.toEquiv with continuous_toFun := hjc, continuous_invFun := hjsc }
  let μE : Measure (Fin r → E) := Measure.pi fun _ => M.μE
  let B : (Fin r → E) → (Fin r → E) → ℂ := fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))
  have hsd : SelfDual μE B := GlobalTheory.T.isSelfDual_pi_haar_traceStarDotProduct_unramified F E r M ψ hψ
  obtain ⟨hT1, hT2⟩ := GlobalTheory.transport_selfDual_fourB j.toAddEquiv hjc hjsc μE B
  have hker : A.kerL ψ ((1 : A.Kˣ) : A.K) = fun x y => B (j.toAddEquiv x) (j.toAddEquiv y) := by
    funext x y
    have h1 := hj x y
    simp only [map_one, one_mul] at h1
    show ψ (Algebra.trace F A.K (((1 : A.Kˣ) : A.K) * Algebra.trace A.K A.L (star x * y))) = ψ (Algebra.trace F E (star (j x) ⬝ᵥ j y))
    rw [Units.val_one, one_mul, GlobalTheory.T.trace_tower_finiteEtaleHermitianPair, h1]
  have hsdL : SelfDual (Measure.map j.toAddEquiv.symm μE) (A.kerL ψ ((1 : A.Kˣ) : A.K)) := by
    rw [hker]; exact (hT1 ⟨hsd, fun x => (continuous_const.add continuous_id).aemeasurable⟩).1
  obtain ⟨γ, Wk, hWk⟩ := hW F E A ψ hψ 1 _ hsdL
  have hγ : γ = 1 := hG F E A ψ hψ 1 _ hsdL A.etaK γ Wk hWk r j (by simpa using hj)
  obtain ⟨hTrE, -, -⟩ := GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E
  have htr2 : ∀ a : F, Algebra.trace F E (algebraMap F E a) = 2 * a := by
    intro a
    apply (algebraMap F E).injective
    rw [hTrE, Unram.star_fix (F := F) (E := E) a, map_mul, map_ofNat]; ring
  have hnorm : ∀ y : A.L, Algebra.trace F A.K (A.NL y) = Algebra.trace F E (star (j y) ⬝ᵥ j y) / 2 := by
    intro y
    have : star (j y) ⬝ᵥ j y = algebraMap F E (∑ i, e (A.NL y) i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, Pi.star_apply, map_sum, hNe y, mul_comm]
    rw [this, htr2, GlobalTheory.T.trace_eq_sum_of_algEquiv_pi r e]; field_simp
  have testj : ∀ φ : (Fin r → E) → ℂ, IsTest φ → IsTest (fun y : A.L => φ (j y)) := fun φ hφ =>
    ⟨hφ.1.comp_continuous hjc, hφ.2.comp_homeomorph jh⟩
  have testjs : ∀ φ : A.L → ℂ, IsTest φ → IsTest (fun b => φ (j.symm b)) := fun φ hφ =>
    ⟨hφ.1.comp_continuous hjsc, hφ.2.comp_homeomorph jh.symm⟩
  have hz : IsTest (0 : A.L → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  have hW0 : ∀ G, Wk G 0 = 0 := by
    intro G
    have := hWk.1.2.2.2 G 1 0 0 hz hz
    simp only [one_smul, add_zero] at this
    simpa using this
  let ι : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) A.K := SpecialLinearGroup.map (algebraMap F A.K)
  let T : SpecialLinearGroup (Fin 2) F → ((Fin r → E) → ℂ) → (Fin r → E) → ℂ :=
    fun g φ b => Wk (ι g) (fun y => φ (j y)) (j.symm b)
  have hTt : ∀ g φ, IsTest φ → IsTest (T g φ) := fun g φ hφ => testjs _ (hWk.1.1 _ _ (testj φ hφ))
  have hT0 : ∀ g, T g 0 = 0 := by
    intro g; funext b
    show Wk (ι g) (fun y => (0 : (Fin r → E) → ℂ) (j y)) (j.symm b) = 0
    have : (fun y => (0 : (Fin r → E) → ℂ) (j y)) = 0 := rfl
    rw [this, hW0]; rfl
  have hsl : ∀ f : Hn r F E → ℂ, IsTest f → ∀ X : Hn r F E, IsTest (fun y : A.L => f (X.1, j y, X.2.2)) :=
    fun f hf X => testj _ ((GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply (T 1) (hTt 1) (hT0 1) f hf).1 X.1 X.2.2)
  refine ⟨fun g f X => T g (fun v => f (X.1, v, X.2.2)) X.2.1, ⟨fun g f hf => (GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply (T g) (hTt g) (hT0 g) f hf).2, ?_, ?_, ?_⟩, ?_⟩
  · intro f hf; funext X
    show Wk (ι 1) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = f X
    rw [map_one, hWk.1.2.1 _ (hsl f hf X)]
    simp
  · intro g h f hf; funext X
    show Wk (ι (g * h)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = Wk (ι g) (fun y => Wk (ι h) (fun y' => f (X.1, j y', X.2.2)) (j.symm (j y))) (j.symm X.2.1)
    simp only [LinearEquiv.symm_apply_apply]
    rw [map_mul, hWk.1.2.2.1 _ _ _ (hsl f hf X)]
  · intro g c f f' hf hf'; funext X
    show Wk (ι g) (fun y => (c • f + f') (X.1, j y, X.2.2)) (j.symm X.2.1) = c * Wk (ι g) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) + Wk (ι g) (fun y => f' (X.1, j y, X.2.2)) (j.symm X.2.1)
    have key : (fun y => (c • f + f') (X.1, j y, X.2.2)) = c • (fun y => f (X.1, j y, X.2.2)) + (fun y => f' (X.1, j y, X.2.2)) := rfl
    rw [key, hWk.1.2.2.2 _ _ _ _ (hsl f hf X) (hsl f' hf' X)]
    rfl
  · intro f hf
    refine ⟨fun t X => ?_, ?_⟩
    · have hι : ι (nS t) = nS (algebraMap F A.K t) := by
        exact sl2Map_nS t
      show Wk (ι (nS t)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = _
      rw [hι, (hWk.2 _ (hsl f hf X)).1]
      have hy := hnorm (j.symm X.2.1)
      rw [LinearEquiv.apply_symm_apply] at hy
      simp only [LinearEquiv.apply_symm_apply, Et.psiK, Units.val_one, mul_one, ← Algebra.smul_def, map_smul, smul_eq_mul, hy, mul_div_assoc]
    · have hι : ι (wS F) = wS A.K := by
        exact sl2Map_wS
      funext X
      show Wk (ι (wS F)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = fourU M ψ f X
      rw [hι, (hWk.2 _ (hsl f hf X)).2.2, hγ, one_mul, hker, hT2]
      have e1 : j.toAddEquiv (j.symm X.2.1) = X.2.1 := j.apply_symm_apply _
      rw [e1]
      show ∫ c, f (X.1, j (j.symm c), X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂μE = ∫ c, f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE)
      simp only [LinearEquiv.apply_symm_apply]
      rfl

end GlobalTheory
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LTwoLemma
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem u_locallyConstant (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ) (h : A.InI Ψ) :
    IsLocallyConstant (fun z => Ψ (wS A.K * nS z)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  obtain ⟨U, hU, hinv⟩ := h.1
  have h0 : (0 : A.K) ∈ U := mem_of_mem_nhds hU
  have ht : Tendsto (fun y : A.K => y - z) (𝓝 z) (𝓝 0) :=
    (continuous_sub_right z).tendsto' z 0 (sub_self z)
  filter_upwards [ht hU] with y hy
  simp only [Set.mem_preimage] at hy
  have he : wS A.K * nS y = (wS A.K * nS z) * nS (y - z) := by
    rw [mul_assoc]; congr 1; apply Subtype.ext
    show !![(1 : A.K), y; 0, 1] = !![1, z; 0, 1] * !![1, y - z; 0, 1]
    rw [Matrix.mul_fin_two]; simp
  rw [he]
  apply hinv
  intro i j
  fin_cases i <;> fin_cases j <;> simp [nS, h0, hy]

theorem absK_nonneg (A : Et F E) (t : A.K) : 0 ≤ A.absK t := by
  unfold Et.absK; split_ifs <;> simp

theorem weyl_unipotent_l2_finite [Unram F E] (hB1 : type_of% GlobalTheory.T.whittaker_bound_big_cell) (hB2 : type_of% GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top) (A : Et F E) (μ : Measure A.K) (hμ : μ.IsAddHaarMeasure)
    (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ) (h : A.InI Ψ) :
    ∫⁻ z, ‖Ψ (wS A.K * nS z)‖ₑ ^ 2 ∂μ < ⊤ := by
  obtain ⟨C, hC⟩ := hB1 F E A Ψ h
  have hB := hB2 F E A μ hμ
  have h0 : ENNReal.ofReal C + 1 ≠ 0 := by simp
  have hT : ENNReal.ofReal C + 1 ≠ ⊤ := by simp
  have hle : ∀ z, ‖Ψ (wS A.K * nS z)‖ₑ ≤ (ENNReal.ofReal C + 1) *
      ⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK,
        α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s) := by
    intro z
    simp only [ENNReal.mul_iInf_of_ne h0 hT]
    refine le_iInf₂ fun s hs => ?_
    obtain ⟨hs1, hs2, α, hα, β, hβ, he⟩ := hs
    have hb := hC z s α β hα hβ hs1 hs2 he
    calc ‖Ψ (wS A.K * nS z)‖ₑ = ENNReal.ofReal ‖Ψ (wS A.K * nS z)‖ := (ofReal_norm_eq_enorm _).symm
      _ ≤ ENNReal.ofReal (C * A.absK s) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal C * ENNReal.ofReal (A.absK s) := ENNReal.ofReal_mul' (absK_nonneg A _)
      _ ≤ _ := by gcongr; exact le_self_add
  calc ∫⁻ z, ‖Ψ (wS A.K * nS z)‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ z, ((ENNReal.ofReal C + 1) * ⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
          ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ :=
        lintegral_mono fun z => pow_le_pow_left' (hle z) 2
    _ = (ENNReal.ofReal C + 1) ^ 2 * ∫⁻ z, (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
          ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ := by
        simp_rw [mul_pow]
        exact lintegral_const_mul' _ _ (by simp)
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hB

end GlobalTheory.JR.LTwoLemma

open GlobalTheory.JR.LTwoLemma in
theorem GlobalTheory.JR.kirillov_vanishing_l2 : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ Ψ, A.InI Ψ → (∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0)) → (∀ z, Ψ (wS A.K * nS z) = 0) ∧ ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd Ψ hI hlim
  have hμ : μK.IsAddHaarMeasure := hsd.1
  have hu : (fun z => Ψ (wS A.K * nS z)) = 0 :=
    GlobalTheory.T.eq_zero_of_truncatedFourier_tendsto_zero_etale F E A ψ hψ μK hsd _ (u_locallyConstant A Ψ hI) (weyl_unipotent_l2_finite GlobalTheory.T.whittaker_bound_big_cell GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top A μK hμ Ψ hI) hlim
  have h1 : ∀ z, Ψ (wS A.K * nS z) = 0 := fun z => congrFun hu z
  exact ⟨h1, GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero F E A ψ μK hμ Ψ hI h1⟩
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem φc_tc (l : ℕ) [Fact l.Prime] (y : Formalism.Per.Fl l) : φc l (tc l y) = tc l (y ^ l) := by
  unfold φc tc
  rw [(GlobalTheory.CrisMaps.phiA_extends l).alg]
  congr 1
  rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

theorem frob_teich : ∀ (l : ℕ) [Fact l.Prime] (y : Formalism.Per.Fl l), φc l (tc l y) = tc l (y ^ l) :=
  fun l _ y => φc_tc l y

end GlobalTheory.PMon.Gauss
end
