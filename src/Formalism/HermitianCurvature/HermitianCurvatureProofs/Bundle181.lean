module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle150
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle084
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle171
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle168
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle175
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle054
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle055
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle089
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle107
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftVectorZeroBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting

@[expose] public section

section

open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem inCC_fold (hC : CVInCC) {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (s : ℂ)
    (F : B.Mat k r → E) : ∀ (b : List C.Letter) (m : ℕ),
      B.InCC A (m + (2 * r + k + 1) * b.length) F → B.InCC A m (foldCV k r s b F)
  | [], m, h => by rw [foldCV_nil]; simpa using h
  | x :: b, m, h => by
    rw [foldCV_cons]
    refine hC k r E A m _ (x.2 : ℂ) s ?_
    refine inCC_fold hC A s F b (m + (2 * r + k + 1)) ?_
    have e : m + (2 * r + k + 1) + (2 * r + k + 1) * b.length = m + (2 * r + k + 1) * (x :: b).length := by
      simp [List.length_cons]; ring
    rw [e]; exact h

theorem weight_budget_L2_inequality (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k) (j : ℕ) (hj : j ≤ 5)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀)
    (ℓ : ℕ) (hℓ : ℓ ≤ N) :
    B.AB k r + 2 * ((r : ℝ) + 1) * ((j + (2 * r + k + 1) * ℓ : ℕ) : ℝ) ≤ A₀ := by
  unfold B.AB
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast hj
  have hℓ' : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hcast : ((j + (2 * r + k + 1) * ℓ : ℕ) : ℝ) = j + n * ℓ := by rw [hn]; push_cast; ring
  rw [hcast]
  have hn3 : (3 : ℝ) ≤ n := by rw [hn]; linarith
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  have h4 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 4 := by
    have : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
    nlinarith

  have hkr : 2 * ((k : ℝ) + r) ≤ 2 * n := by rw [hn]; linarith
  have hb : 2 * ((k : ℝ) + r) + 1 + 2 * (j + n * ℓ) ≤ 100 * ((N : ℝ) * n ^ 2 + n ^ 3) := by
    have h1 : 2 * n * ℓ ≤ (N : ℝ) * n ^ 2 := by
      have : (ℓ : ℝ) * (2 * n) ≤ N * (n * n) := by
        apply mul_le_mul hℓ' (by nlinarith) (by positivity) (by positivity)
      nlinarith
    have h2 : 2 * n + 1 + 10 ≤ 100 * n ^ 3 := by nlinarith
    have hNn : 0 ≤ (N : ℝ) * n ^ 2 := by positivity
    nlinarith
  have hpos : 0 ≤ 100 * ((N : ℝ) * n ^ 2 + n ^ 3) := by positivity
  calc 2 * ((k : ℝ) + r) * ((r : ℝ) + 1) + 1 + 2 * ((r : ℝ) + 1) * (j + n * ℓ)
      ≤ ((r : ℝ) + 1) * (2 * ((k : ℝ) + r) + 1 + 2 * (j + n * ℓ)) := by nlinarith
    _ ≤ ((r : ℝ) + 1) * (100 * ((N : ℝ) * n ^ 2 + n ^ 3)) := by gcongr
    _ ≤ ((r : ℝ) + 1) ^ 4 * (100 * ((N : ℝ) * n ^ 2 + n ^ 3)) := by gcongr
    _ = 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * n ^ 2 + n ^ 3) := by ring
    _ ≤ A₀ := hA

theorem l2BoundAtBuiltPlace_of_cvInCC (hC : CVInCC) : L2BoundAtTowerPlace := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v ε hε a hlen
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨hχ, hv⟩ := hbuilt
  obtain ⟨_, _, _, _, hCC, _⟩ := hv v
  have hF : ∀ j ≤ 5, B.InCC (B.AB S.G.k S.G.r) (j + (2 * S.G.r + S.G.k + 1) * a.length)
      (D.cutF (T v).base χ (f v) ε) := fun j hj =>
    Formalism.FourierDecayAlt.P.PBE.cutF_inCC (T v).base hχ hCC hε _ _ (weight_budget_L2_inequality S.G.k S.G.r S.Ntop A₀ hk2 j hj hA a.length hlen)
  have h5 := inCC_fold hC (B.AB S.G.k S.G.r) (M.sgn (D.parOf S v) (S.l + 1)) _ a 5 (hF 5 le_rfl)
  have h4 := inCC_fold hC (B.AB S.G.k S.G.r) (M.sgn (D.parOf S v) (S.l + 1)) _ a 4 (hF 4 (by norm_num))
  obtain ⟨_, _, _, hB1, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base
    (B.AB S.G.k S.G.r) le_rfl
  obtain ⟨C0, hC0⟩ := hB1
  obtain ⟨c4, hc4⟩ := h4
  exact (hC0 _ _ c4 c4 h5 h5 hc4 hc4).1

theorem L2_bound_at_built_place_holds : L2BoundAtTowerPlace := l2BoundAtBuiltPlace_of_cvInCC coefficient_vector_in_L2_class

end Formalism.FourierDecayAlt.P.CutMP.En
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section reorder

variable {X Y A X' Y' A' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A] [MeasurableSpace X']
  [MeasurableSpace Y'] [MeasurableSpace A']

def reorderE : ((X × Y) × (X' × Y')) × (A × A') ≃ᵐ (X × (A × Y)) × (X' × (A' × Y')) where
  toFun q := ((q.1.1.1, (q.2.1, q.1.1.2)), (q.1.2.1, (q.2.2, q.1.2.2)))
  invFun p := (((p.1.1, p.1.2.2), (p.2.1, p.2.2.2)), (p.1.2.1, p.2.2.1))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable fun q : ((X × Y) × (X' × Y')) × (A × A') => ((q.1.1.1, (q.2.1, q.1.1.2)), (q.1.2.1, (q.2.2, q.1.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable fun p : (X × (A × Y)) × (X' × (A' × Y')) => (((p.1.1, p.1.2.2), (p.2.1, p.2.2.2)), (p.1.2.1, p.2.2.1))
    fun_prop

theorem reorder_mp (μX : Measure X) (μY : Measure Y) (μA : Measure A) (μX' : Measure X') (μY' : Measure Y')
    (μA' : Measure A') [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μA] [SigmaFinite μX'] [SigmaFinite μY']
    [SigmaFinite μA'] :
    MeasurePreserving (reorderE (X := X) (Y := Y) (A := A) (X' := X') (Y' := Y') (A' := A'))
      (((μX.prod μY).prod (μX'.prod μY')).prod (μA.prod μA'))
      ((μX.prod (μA.prod μY)).prod (μX'.prod (μA'.prod μY'))) := by
  have h1 := Dx2.SplitM.middle_four_swap_measure_preserving (μX.prod μY) (μX'.prod μY') μA μA'
  have h2 := ((MeasurePreserving.id μX).prod (Measure.measurePreserving_swap (μ := μY) (ν := μA))).comp
    (measurePreserving_prodAssoc μX μY μA)
  have h2' := ((MeasurePreserving.id μX').prod (Measure.measurePreserving_swap (μ := μY') (ν := μA'))).comp
    (measurePreserving_prodAssoc μX' μY' μA')
  have hall := (h2.prod h2').comp h1
  convert hall using 1
  funext ⟨⟨⟨x, y⟩, ⟨x', y'⟩⟩, ⟨a, a'⟩⟩
  rfl

end reorder

variable {k : ℕ}

def MCOm : Prop :=
  ∀ (k ρ : ℕ) (z0 z0' : Fin (2 * ρ + k + 1) → ℂ), inWb k ρ z0 → inWb k ρ z0' → ∀ c : ℂ, c ≠ 0 →
    ∀ γ ∈ B.GV k ρ, γ ∈ Q.OmPlus k ρ z0 z0' →
      D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) ∈
        JF.Om k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0'))

theorem ae_mem_of_haar {r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ U := by
  rw [ae_iff]; exact h.conc

theorem jfStep_of (hO : MCOm) : JFStep := by
  intro k ρ m e Wp Wq _ _ _ _ _ _ B1 B0 hz hz' hπ hπ' hW1 hW1' hW0 hW0' hN1 hN0 f1 f0 c hc hf1 hstep γ hγ hγO
  subst e
  rw [Dx2.Tower.castV_rfl] at hz hz'
  set κ : 1 + ρ = ρ + 1 := Nat.add_comm 1 ρ with hκ
  have hπ1 : ∀ y : B.Mat k ρ, B0.π y = B1.π (D.castM κ (ιLev k 1 ρ y)) := by
    intro y; rw [hπ y]; unfold lev1; rw [Dx2.MN.castM_rfl]
  have hπ1' : ∀ y : B.Mat k ρ, B0.π' y = B1.π' (D.castM κ (ιLev k 1 ρ y)) := by
    intro y; rw [hπ' y]; unfold lev1; rw [Dx2.MN.castM_rfl]
  have hmc : mc rfl c γ = D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) := by
    unfold mc; rw [Dx2.MN.castM_rfl]

  have hμW : B1.μW = B0.μW.map (levA ρ) :=
    muW_lev B0.z B0.μW B1.μW B0.haarW (by rw [← hz]; exact B1.haarW) hW0 hW1
  have hμW' : B1.μW' = B0.μW'.map (levA ρ) :=
    muW_lev B0.z' B0.μW' B1.μW' B0.haarW' (by rw [← hz']; exact B1.haarW') hW0' hW1'
  have hμN : B1.μN = ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Qm ρ) := by rw [hN1, muN_succ']

  have hOm := hO k ρ B0.z B0.z' B0.z_mem B0.z'_mem c hc γ hγ hγO
  rw [← hz, ← hz', ← hmc] at hOm
  have hInt := rhs_int B1 f1 hf1 _ hOm
  have hsH := sf_heis (k := k) ρ
  have hsN := sf_muN (k := k) ρ
  have hfW : IsFiniteMeasure B0.μW := ⟨by rw [hW0]; exact ENNReal.one_lt_top⟩
  have hfW' : IsFiniteMeasure B0.μW' := ⟨by rw [hW0']; exact ENNReal.one_lt_top⟩
  set T : (Mt k ρ × (Mt k (1 + ρ) × Mt k ρ)) × (Mt k ρ × (Mt k (1 + ρ) × Mt k ρ)) → B.SS k (ρ + 1) :=
    Prod.map (Prod.map (levA ρ) (Qm ρ)) (Prod.map (levA ρ) (Qm ρ)) with hT
  have hTm : Measurable T :=
    ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable).prodMap
      ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable)
  set big := (B0.μW.prod ((B2.μHeis k ρ).prod (D.muN k ρ))).prod
    (B0.μW'.prod ((B2.μHeis k ρ).prod (D.muN k ρ))) with hbig
  have hμSS : B1.μSS = big.map T := by
    unfold B.RealPlaceData.μSS
    rw [hμW, hμW', hμN, Measure.map_prod_map _ _ (levA_cont ρ).measurable (Qm_cont ρ).measurable,
      Measure.map_prod_map _ _ (levA_cont ρ).measurable (Qm_cont ρ).measurable,
      Measure.map_prod_map _ _ ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable)
        ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable)]
  set FI := JF.integrand B1 f1 (mc rfl c γ) with hFI
  have hR : B.JF B1 f1 (mc rfl c γ) = ∫ p, FI p ∂B1.μSS := rfl
  have hL : B.JF B0 f0 γ = ∫ p, JF.integrand B0 f0 γ p ∂((B0.μW.prod (D.muN k ρ)).prod (B0.μW'.prod (D.muN k ρ))) := by
    rw [← hN0]; rfl
  have hAE : AEStronglyMeasurable FI (big.map T) := by rw [← hμSS]; exact hInt.aestronglyMeasurable
  have hInt2 : Integrable (FI ∘ T) big := (integrable_map_measure hAE hTm.aemeasurable).1 (by rw [← hμSS]; exact hInt)
  have hRmp := reorder_mp B0.μW (D.muN k ρ) (B2.μHeis k ρ) B0.μW' (D.muN k ρ) (B2.μHeis k ρ)
  have hInt3 : Integrable (FI ∘ T ∘ reorderE) (((B0.μW.prod (D.muN k ρ)).prod (B0.μW'.prod (D.muN k ρ))).prod
      ((B2.μHeis k ρ).prod (B2.μHeis k ρ))) :=
    (hRmp.integrable_comp_emb reorderE.measurableEmbedding).2 hInt2
  rw [hR, hμSS, integral_map hTm.aemeasurable hAE, ← hRmp.integral_comp reorderE.measurableEmbedding]
  change B.JF B0 f0 γ = ∫ x, (FI ∘ T ∘ reorderE) x ∂_
  rw [integral_prod _ hInt3, hL]

  have w1 : ∀ᵐ x ∂B0.μW, Matrix.of x ∈ UWset k ρ B0.z := ae_mem_of_haar B0.haarW
  have w1' : ∀ᵐ x ∂B0.μW', Matrix.of x ∈ UWset k ρ B0.z' := ae_mem_of_haar B0.haarW'
  have w2 : ∀ᵐ x ∂(D.muN k ρ), Matrix.of x ∈ QuantumDeterminants.Nset k ρ := ae_mem_of_haar (Dx2.MN.haar ρ)
  have wH : ∀ᵐ x ∂(B2.μHeis k ρ), Matrix.of x ∈ QuantumDeterminants.Nset k (1 + ρ) := by
    filter_upwards [ae_mem_of_haar (Formalism.FourierDecayAlt.P.heisenberg_haar_measure k ρ)] with x hx
    obtain ⟨p, hp⟩ := hx
    rw [← hp]; exact Formalism.FourierDecayAlt.P.heisenberg_mem_unipotent k ρ p
  set μO := (B0.μW.prod (D.muN k ρ)).prod (B0.μW'.prod (D.muN k ρ)) with hμO
  have o1 : ∀ᵐ o ∂μO, Matrix.of o.1.1 ∈ UWset k ρ B0.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae w1)
  have o2 : ∀ᵐ o ∂μO, Matrix.of o.1.2 ∈ QuantumDeterminants.Nset k ρ :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae w2)
  have o3 : ∀ᵐ o ∂μO, Matrix.of o.2.1 ∈ UWset k ρ B0.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae w1')
  have o4 : ∀ᵐ o ∂μO, Matrix.of o.2.2 ∈ QuantumDeterminants.Nset k ρ :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae w2)
  have i1 : ∀ᵐ i ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)), Matrix.of i.1 ∈ QuantumDeterminants.Nset k (1 + ρ) :=
    Measure.quasiMeasurePreserving_fst.ae wH
  have i2 : ∀ᵐ i ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)), Matrix.of i.2 ∈ QuantumDeterminants.Nset k (1 + ρ) :=
    Measure.quasiMeasurePreserving_snd.ae wH
  apply integral_congr_ae
  filter_upwards [o1, o2, o3, o4] with o ho1 ho2 ho3 ho4
  obtain ⟨⟨h0, y⟩, ⟨h0', y'⟩⟩ := o
  simp only at ho1 ho2 ho3 ho4
  have hH := Ux3.hpk_det k ρ
  have hgG : Matrix.of y * Matrix.of h0 ∈ B.GV k ρ := HermitianFormFactor.UH_mul ho2.1 ho1.1
  have hgG' : Matrix.of y' * Matrix.of h0' ∈ B.GV k ρ := HermitianFormFactor.UH_mul ho4.1 ho3.1
  set γh := (Matrix.of y * Matrix.of h0)⁻¹ * γ * (Matrix.of y' * Matrix.of h0') with hγhd
  have hγh : γh ∈ B.GV k ρ := HermitianFormFactor.UH_mul (HermitianFormFactor.UH_mul (HermitianFormFactor.UH_inv hH hgG) hγ) hgG'

  have hrep := B0.π_rep
  have hrep' := B0.π'_rep
  have hi0 : (Matrix.of h0)⁻¹ ∈ UWset k ρ B0.z := WeylGroupFacts.uw_inv ho1
  have hi0' : (Matrix.of h0')⁻¹ ∈ UWset k ρ B0.z' := WeylGroupFacts.uw_inv ho3
  have hu0 : IsUnit (Matrix.of h0).det := HermitianFormFactor.UH_unit hH ho1.1
  have hu0' : IsUnit (Matrix.of h0').det := HermitianFormFactor.UH_unit hH ho3.1
  let eA : Wp ≃L[ℂ] Wp := ContinuousLinearEquiv.equivOfInverse (B0.π (Matrix.of h0)) (B0.π (Matrix.of h0)⁻¹)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hi0 _ ho1, Matrix.nonsing_inv_mul _ hu0, hrep.1]; rfl)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ ho1 _ hi0, Matrix.mul_nonsing_inv _ hu0, hrep.1]; rfl)
  let eB : Wq ≃L[ℂ] Wq := ContinuousLinearEquiv.equivOfInverse (B0.π' (Matrix.of h0')) (B0.π' (Matrix.of h0')⁻¹)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep'.2 _ hi0' _ ho3, Matrix.nonsing_inv_mul _ hu0', hrep'.1]; rfl)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep'.2 _ ho3 _ hi0', Matrix.mul_nonsing_inv _ hu0', hrep'.1]; rfl)
  let Λ : (Wq →L[ℂ] Wp) ≃L[ℂ] (Wq →L[ℂ] Wp) := eB.arrowCongr eA
  have hΛ : ∀ Tm : Wq →L[ℂ] Wp, Λ Tm = (B0.π (Matrix.of h0)).comp (Tm.comp (B0.π' (Matrix.of h0')⁻¹)) := by
    intro Tm; ext v; rfl
  set K : ℂ := psi k ρ B0.z cStd (Matrix.of y) * star (psi k ρ B0.z' cStd (Matrix.of y')) with hK
  set Ψ : Mt k (1 + ρ) × Mt k (1 + ρ) → (Wq →L[ℂ] Wp) := fun p => psiInt B1 f1 c γh (Matrix.of p.1) (Matrix.of p.2)
    with hΨ
  symm
  calc ∫ i, (FI ∘ T ∘ reorderE) (((h0, y), (h0', y')), i) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ))
      = ∫ i, K • Λ (Ψ (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) i.1,
          conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) i.2)) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) := by
        apply integral_congr_ae
        filter_upwards [i1, i2] with i hi1 hi2
        rw [hΛ]
        show JF.integrand B1 f1 (mc rfl c γ) ((levA ρ h0, Qm ρ (i.1, y)), (levA ρ h0', Qm ρ (i.2, y'))) = _
        rw [hmc, pt_eq B1 B0 hz hz' hπ1 hπ1' f1 c γ h0 y h0' y' i.1 i.2 ho1 ho2 ho3 ho4 hi1 hi2]
    _ = K • Λ (∫ i, Ψ (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) i.1,
          conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) i.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ))) := by
        rw [integral_smul, Λ.integral_comp_comm]
    _ = K • Λ (∫ i, Ψ i ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ))) := by
        rw [heis_conj_int ρ hgG hgG' Ψ]
    _ = K • Λ (∫ xx : U.RC k 1 ρ × U.RC k 1 ρ, psiInt B1 f1 c γh (U.Rn k 1 ρ xx.1) (U.Rn k 1 ρ xx.2)
          ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ))) := by
        rw [← heis_int ρ (fun b b' => psiInt B1 f1 c γh b b')]
    _ = K • Λ (f0 γh) := by
        rw [hstep γh hγh]
        rfl
    _ = JF.integrand B0 f0 γ ((h0, y), (h0', y')) := by
        rw [hΛ]
        unfold JF.integrand JF.xiP B.rho B.sgs
        congr 3
        show f0 γh = f0 ((Matrix.of h0)⁻¹ * (Matrix.of y)⁻¹ * γ * Matrix.of y' * Matrix.of h0')
        rw [hγhd, Matrix.mul_inv_rev]
        simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.PBH
end
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gTSS_of_adj_radT : GTSSAdjPt → GTCLRadT → GTSS := fun hA hR =>
  gTSS_of_cut (gTSSLocal_of_radT hR) hA SSC.second_shift_constant SSPh.second_shift_phase_holds

theorem gTSS_of_adj : GTSSAdjPt → GTSS := fun hA => gTSS_of_adj_radT hA radial_torus_local_holds

theorem second_shift_gauge_holds : GTSS := gTSS_of_adj second_shift_adjoint_pointwise

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem nfVLin_comp_sum {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {ι : Type} (s : Finset ι) (a : Wp →L[ℂ] Wp) (b : Wq →L[ℂ] Wq) (c : ι → ℂ)
    (f : ι → Wq →L[ℂ] Wp) :
    a.comp ((∑ i ∈ s, c i • f i).comp b) = ∑ i ∈ s, c i • a.comp ((f i).comp b) := by
  ext x

  simp [ContinuousLinearMap.sum_apply, map_sum, map_smul]

theorem vector_linearity_holds : NFVLin := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs ν' m₀ Q c H Hq A hA hcont hdec hH pt hpt hGPoint
  unfold D.vecV
  have h : D.IsLocPt pt (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r pt := ⟨hpt, hGPoint⟩
  simp only [dif_pos h]
  by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN pt (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
  · simp only [dif_pos h']
    have hγ := h'.choose_spec.1
    have hZ := h'.choose_spec.2.1
    have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' pt h'.choose h.1 hZ
    have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
    have hGeq : D.ptG (Tz k r Bs.z * Tz k r Bs.z') r pt = Gf k r Bs.z Bs.z' h'.choose := by
      rw [hGq]
    obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' pt (r + 1) h.1.2 h.1.1
    have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs pt h'.choose h.1 hγ hZ
    have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
      ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
    have hZm := hZ.trans hmono
    obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos hA
    have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _ :=
      ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm,
        fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩
    have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG

    have hEq : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp),
        Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS →
        D.orbJ Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm pt)) G =
          ∫ p, θ p • D.orbIntegrand Bs h'.choose G p ∂Bs.μSS := by
      intro G hi
      have hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm pt)) θ' ∧
          Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose G p) Bs.μSS := ⟨θ, hθ, hi⟩
      unfold D.orbJ
      rw [dif_pos hex]
      exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR G _ θ hex.choose_spec.1 hθ
        hex.choose_spec.2 hi

    have hiq : ∀ q, Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose (Hq q) p) Bs.μSS := by
      intro q
      obtain ⟨C, hC⟩ := hdec q (Gf k r Bs.z Bs.z' h'.choose) hpos
      have hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose (Hq q)) Bs.μSS :=
        Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb (hcont q)
      refine Integrable.mono' (hmaj.const_mul (max C 0)) (hθ.1.aestronglyMeasurable.smul hm) ?_
      refine hdom (Hq q) (max C 0) (le_max_right _ _) fun p hp => ?_
      have hs := horb p hp
      refine (hC _ hs.1 (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp])).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

    have hae : (fun p => θ p • D.orbIntegrand Bs h'.choose H p) =ᵐ[Bs.μSS]
        fun p => ∑ q, c q (Gf k r Bs.z Bs.z' h'.choose) • (θ p • D.orbIntegrand Bs h'.choose (Hq q) p) := by
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
      have hs := horb p hp
      simp only [D.orbIntegrand, B.rho]
      rw [hH _ hs, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp, nfVLin_comp_sum, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_comm (B.xiTau Bs (1, 1) p), smul_comm (θ p)]
    have hiH : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose H p) Bs.μSS :=
      (integrable_finsetSum _ fun q _ => (hiq q).smul (c q (Gf k r Bs.z Bs.z' h'.choose))).congr hae.symm
    have hint : ∀ q ∈ (Finset.univ : Finset (Fin (Q + 1))), Integrable
        (fun a => c q (Gf k r Bs.z Bs.z' h'.choose) • (θ a • D.orbIntegrand Bs h'.choose (Hq q) a)) Bs.μSS :=
      fun q _ => (hiq q).smul (c q (Gf k r Bs.z Bs.z' h'.choose))
    rw [hEq H hiH, integral_congr_ae hae, integral_finsetSum Finset.univ hint, hGeq]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_smul, hEq (Hq q) (hiq q)]
  · simp only [dif_neg h', smul_zero, Finset.sum_const_zero]

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

private theorem castV_liftVec_liftVec_eq_castV_liftVec_succ {k j ρ m n : ℕ} (e : 1 + ρ = m) (h1 : j + m = n)
    (h2 : j + 1 + ρ = n) (v : Fin (2 * ρ + k + 1) → ℂ) :
    D.castV h1 (QuantumDeterminants.liftVec k j m (D.castV e (QuantumDeterminants.liftVec k 1 ρ v))) =
      D.castV h2 (QuantumDeterminants.liftVec k (j + 1) ρ v) := by
  funext p
  simp only [D.castV, QuantumDeterminants.liftVec, Fin.coe_cast]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; ext; simp only [Fin.coe_cast]; omega)

private theorem consC_castM_ιLev_mem_DomR_of_mem_DomR {k ρ m : ℕ} (e : 1 + ρ = m) {t : ℂ} (ht : t ≠ 0)
    (z z' : Fin (2 * ρ + k + 1) → ℂ) (c : Fin ρ → ℂ) (g : Q.Mx k ρ)
    (h : (c, g) ∈ Q.DomR k ρ z z') :
    ((fun l : Fin m => PBH.consC t c (Fin.cast e.symm l)), D.castM e (QuantumDeterminants.ιLev k 1 ρ g)) ∈
      Q.DomR k m (D.castV e (QuantumDeterminants.liftVec k 1 ρ z)) (D.castV e (QuantumDeterminants.liftVec k 1 ρ z')) := by
  subst e
  rw [JCTx5.castV_rfl, JCTx5.castV_rfl, JCTx5.castM_rfl]
  exact (PBH.domR_iota ht z z' c g).2 h

theorem cell_compatibility : CellTie := by
  intro Wp Wq _ _ _ _ _ _ P T hP hN j hj hPj hPj1 t ht x hx
  have e : 1 + (P.r - (j + 1)) = P.r - j := by omega
  have hz : (T.bs j).z = D.castV e (QuantumDeterminants.liftVec P.k 1 (P.r - (j + 1)) (T.bs (j + 1)).z) := by
    apply JCTx5.liftVec_inj (i := j)
    apply PBH.castV_inj (show j + (P.r - j) = P.r by omega)
    rw [T.z_lev j (by omega), castV_liftVec_liftVec_eq_castV_liftVec_succ e (show j + (P.r - j) = P.r by omega)
      (show j + 1 + (P.r - (j + 1)) = P.r by omega), T.z_lev (j + 1) hj]
  have hz' : (T.bs j).z' =
      D.castV e (QuantumDeterminants.liftVec P.k 1 (P.r - (j + 1)) (T.bs (j + 1)).z') := by
    apply JCTx5.liftVec_inj (i := j)
    apply PBH.castV_inj (show j + (P.r - j) = P.r by omega)
    rw [T.z'_lev j (by omega), castV_liftVec_liftVec_eq_castV_liftVec_succ e (show j + (P.r - j) = P.r by omega)
      (show j + 1 + (P.r - (j + 1)) = P.r by omega), T.z'_lev (j + 1) hj]
  refine ⟨?_, PBF.wCell_mul_GV hx.1 hx.2.1,
    P5.Rad.wCell_mem_omPlus hPj1.2.1 hPj1.2.2.1 hx.1 hx.2.1 hx.2.2⟩
  rw [hz, hz']
  exact consC_castM_ιLev_mem_DomR_of_mem_DomR e ht _ _ x.1 x.2 hx

end Formalism.FourierDecayAlt.P.CutSH

theorem Formalism.FourierDecayAlt.P.cell_compatibility_identity : Formalism.FourierDecayAlt.P.CutSH.CellTie := Formalism.FourierDecayAlt.P.CutSH.cell_compatibility
end
end
