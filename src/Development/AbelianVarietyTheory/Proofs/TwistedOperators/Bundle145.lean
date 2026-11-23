module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle075
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle078
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle084
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle075
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ModuLR

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped NNReal ENNReal TensorProduct

theorem chi_Af (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (Af F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) = ∏ᶠ v, ‖evalV F v M.det‖ := by
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finset_matrixPair_integral_outside F κ M M⁻¹
  obtain ⟨hOc, hOs, hOt⟩ := GlobalTheory.T.finiteIntegers_topology F S
  let _ : MeasurableSpace (OPart F S) := borel _
  have _ : BorelSpace (OPart F S) := ⟨rfl⟩

  let φS : Af F →+* SPart F S := RingHom.pi fun v => (evalV F v.1).toRingHom
  let φO : Af F →+* (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, Fv F v.1) :=
    RingHom.pi fun v => (evalV F v.1).toRingHom
  let ι : OPart F S →+* (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, Fv F v.1) :=
    RingHom.pi fun v => (v.1.adicCompletionIntegers F).toSubring.subtype.comp (Pi.evalRingHom _ v)
  have hι : Function.Injective ι := fun x y h => funext fun v => Subtype.ext (congrFun h v)
  let MS : Matrix κ κ (SPart F S) := φS.mapMatrix M
  let MO : Matrix κ κ (OPart F S) := fun i j v => ⟨evalV F v.1 (M i j), (hS v.1 v.2 i j).1⟩
  let NO : Matrix κ κ (OPart F S) := fun i j v => ⟨evalV F v.1 (M⁻¹ i j), (hS v.1 v.2 i j).2⟩
  have hdS : MS.det = φS M.det := (RingHom.map_det φS M).symm
  have huS : IsUnit MS.det := hdS ▸ hM.map φS
  have hMO : ι MO.det = φO M.det := by
    rw [RingHom.map_det, RingHom.map_det]; rfl
  have hNO : ι NO.det = φO M⁻¹.det := by
    rw [RingHom.map_det, RingHom.map_det]; rfl
  have hON : MO.det * NO.det = 1 := hι (by
    rw [map_mul, hMO, hNO, ← map_mul, ← Matrix.det_mul, Matrix.mul_nonsing_inv M hM, Matrix.det_one,
      map_one, map_one])
  have huO : IsUnit MO.det := ⟨⟨_, _, hON, by rw [mul_comm]; exact hON⟩, rfl⟩
  let j : ((κ → SPart F S) × (κ → OPart F S)) →+ (κ → Af F) :=
    ((jS F S).toAddMonoidHom.compLeft κ).comp (zipHom κ (SPart F S) (OPart F S))
  have hj : IsOpenEmbedding j :=
    (IsOpenEmbedding.piMap fun _ => GlobalTheory.T.isOpenEmbedding_finiteAdeleOfSPartAndIntegralPart F S).comp (GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs κ (SPart F S) (OPart F S))
  have key := GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict (κ → Af F) ((κ → SPart F S) × (κ → OPart F S)) j hj (mulVecCE M hM)
    (prodCE (mulVecCE MS huS) (mulVecCE MO huO)) (by
      intro x
      funext i
      rw [mulVecCE_apply, prodCE_apply, mulVecCE_apply, mulVecCE_apply]
      apply RestrictedProduct.ext
      intro v
      change evalV F v ((M *ᵥ j x) i) = evalV F v (jS F S ((MS *ᵥ x.1) i, (MO *ᵥ x.2) i))
      rw [evalV_jS]
      by_cases hv : v ∈ S
      · rw [dite_eq_left hv]

        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        change evalV F v (M i k) * evalV F v (jS F S (x.1 k, x.2 k)) = _
        rw [evalV_jS, dite_eq_left hv]
        rfl
      · rw [dite_eq_right hv]
        change _ = ι ((MO *ᵥ x.2) i) ⟨v, hv⟩

        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        change evalV F v (M i k) * evalV F v (jS F S (x.1 k, x.2 k)) = _
        rw [evalV_jS, dite_eq_right hv]
        rfl)
  rw [key, GlobalTheory.T.addEquivAddHaarChar_prodCongr, addEquivAddHaarChar_eq_one_of_compactSpace (mulVecCE MO huO), mul_one,
    GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced (SPart F S)
      (by show IsArtinianRing (∀ v : S, Fv F v.1); infer_instance)
      ⟨fun x ⟨n, hn⟩ => funext fun v => IsReduced.eq_zero (x v) ⟨n, congrFun hn v⟩⟩ κ _ huS,
    GlobalTheory.T.haarModulusOfUnit_completionsAtPlaces_eq_prod_norm F S _ huS, hdS,
    finprod_eq_prod_of_mulSupport_subset (s := S), ← Finset.prod_coe_sort S]
  · rfl
  · intro v hv
    by_contra hvS
    apply hv
    have h1 := GlobalTheory.T.norm_eq_one_of_mul_eq_one_adicCompletionIntegers F v (MO.det ⟨v, hvS⟩) (NO.det ⟨v, hvS⟩) (congrFun hON ⟨v, hvS⟩)
    have h2 : (MO.det ⟨v, hvS⟩ : Fv F v) = evalV F v M.det := congrFun hMO ⟨v, hvS⟩
    show ‖evalV F v M.det‖ = 1
    rw [← h2]
    exact h1

theorem chi_AF (F : Type) [Field F] [NumberField F] [IsTotallyReal F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) =
      (∏ w, ‖(fstA F M.det) w‖) * ∏ᶠ v, ‖evalV F v (sndA F M.det)‖ := by
  classical
  have hd₁ : (M.map (fstA F)).det = fstA F M.det := (RingHom.map_det (fstA F).toRingHom M).symm
  have hd₂ : (M.map (sndA F)).det = sndA F M.det := (RingHom.map_det (sndA F).toRingHom M).symm
  have hu₁ : IsUnit (M.map (fstA F)).det := hd₁ ▸ hM.map (fstA F)
  have hu₂ : IsUnit (M.map (sndA F)).det := hd₂ ▸ hM.map (sndA F)
  let j : ((κ → Ainf F) × (κ → Af F)) →+ (κ → AF F) := zipHom κ (Ainf F) (Af F)
  have hj : IsOpenEmbedding j := GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs κ (Ainf F) (Af F)
  have key := GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict (κ → AF F) ((κ → Ainf F) × (κ → Af F)) j hj (mulVecCE M hM)
    (prodCE (mulVecCE (M.map (fstA F)) hu₁) (mulVecCE (M.map (sndA F)) hu₂)) (by
      intro x
      funext i
      rw [mulVecCE_apply, prodCE_apply, mulVecCE_apply, mulVecCE_apply]
      refine Prod.ext ?_ ?_
      · change fstA F _ = _

        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        exact Finset.sum_congr rfl fun k _ => rfl
      · change sndA F _ = _

        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        exact Finset.sum_congr rfl fun k _ => rfl)
  rw [key, GlobalTheory.T.addEquivAddHaarChar_prodCongr, NNReal.coe_mul, chi_Af F _ hu₂, hd₂,
    GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced (Ainf F)
      (by show IsArtinianRing (∀ v : InfinitePlace F, v.Completion); infer_instance)
      ⟨fun x ⟨n, hn⟩ => funext fun v => IsReduced.eq_zero (x v) ⟨n, congrFun hn v⟩⟩ κ _ hu₁, hd₁,
    GlobalTheory.GaugeProdFormula.modu_infinite F _ (hM.map (fstA F))]

theorem chi_lr (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)
    [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)) :
    addEquivAddHaarChar (lrCE g a) = GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det g) ^ n *
      GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det a) ^ m := by
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hchar⟩ := GlobalTheory.T.exists_restrictScalars_matrix_leftRightMul_adeleTensor F E m n g a
  apply NNReal.coe_injective
  rw [hchar, chi_AF F Λ hΛ, hdet, GlobalTheory.T.tensorIdeleNormalizedAbs_eq_adelic_abs_norm F E]
  simp [map_mul, map_pow]

theorem smul_map_lr (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)
    [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    (μ : Measure (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))) [μ.IsAddHaarMeasure]
    (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)) :
    μ = ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) ^ n *
      (GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det a) : ℝ≥0∞) ^ m) • μ.map (lrCE g a) := by
  have h := addEquivAddHaarChar_smul_map μ (lrCE g a)
  rw [chi_lr F E m n g a] at h
  calc μ = _ := h.symm
    _ = _ := by rw [ENNReal.smul_def]; push_cast; rfl


open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem modu_lrMul : ∀ (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)), μ.IsAddHaarMeasure → ∀ (g : GL (Fin m) (AE D)) (a : GL (Fin n) (AE D)), μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det g) : ENNReal) ^ n * (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ m) • Measure.map (fun u : Mx D m n => (HMul.hMul (HMul.hMul g.val (u : Matrix (Fin m) (Fin n) (AE D))) a.val : Mx D m n)) μ := by
  intro D m n μ hμ g a
  have _ : LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin m → Fin n → AF D.host.F ⊗[D.host.F] D.host.E))
  have _ : SecondCountableTopology (Matrix (Fin m) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AF D.host.F ⊗[D.host.F] D.host.E))
  have hb : BorelSpace (Fin m → Fin n → AE D) := inferInstance
  have _ : BorelSpace (Matrix (Fin m) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    ⟨by first | rfl | exact hb.measurable_eq⟩
  exact smul_map_lr D.host.F D.host.E m n μ g a

end GlobalTheory.ModuLR
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfDecomp

variable {D : D7}

theorem adj_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) (B : Matrix (Fin b) (Fin c) D.host.E) :
    adj D (A * B) = adj D B * adj D A := by
  simp only [adj, Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem adj_adj {a b : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) : adj D (adj D A) = A := by
  refine Matrix.ext fun i j => ?_
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  exact star_star (A i j)

theorem adj_one {a : ℕ} : adj D (1 : Matrix (Fin a) (Fin a) D.host.E) = 1 := by
  simp [adj, Formalism.UG.cT]

theorem adj_zero {a b : ℕ} : adj D (0 : Matrix (Fin a) (Fin b) D.host.E) = 0 := by
  simp [adj, Formalism.UG.cT]

theorem adj_gram (V : HSp D) : adj D V.gram = V.gram := by
  refine Matrix.ext fun i j => ?_
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  exact GlobalTheory.LatVac.gram_star V j i

end GlobalTheory.HalfDecomp

namespace GlobalTheory.HalfDecomp

variable {D : D7}

theorem exists_decomp_one (V V' : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B)
    (K : Matrix (Fin r) (Fin V.rank) D.host.E) (hKC : K * C = 1) (hKB : K * B = 0) :
    ∃ N' : Matrix (Fin V.rank) (Fin r) D.host.E,
      C * K + (B * (V'.gram⁻¹ * adj D B * V.gram) + N' * (adj D C * V.gram)) = 1 := by
  set G := V.gram
  set Pi := adj D C * G
  set Pm := V'.gram⁻¹ * adj D B * G
  set N := G⁻¹ * adj D K
  set N' := N - C * (K * N) - B * (Pm * N)
  have hG := GlobalTheory.LatVac.gram_det_isUnit V
  have hG' := GlobalTheory.LatVac.gram_det_isUnit V'
  have hPiC : Pi * C = 0 := hs.frame.2.2
  have hPiB : Pi * B = 0 := hs.orth
  have hBC : adj D B * G * C = 0 := by
    have h := congrArg (adj D) hs.orth
    rw [adj_mul, adj_mul, adj_adj, adj_gram, adj_zero, ← Matrix.mul_assoc] at h
    exact h
  have hPmC : Pm * C = 0 := by
    simp only [Pm, Matrix.mul_assoc] at hBC ⊢
    rw [hBC, Matrix.mul_zero]
  have hPmB : Pm * B = 1 := by
    simp only [Pm, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (adj D B), hs.isom, Matrix.nonsing_inv_mul _ hG']
  have hPiN : Pi * N = 1 := by
    simp only [Pi, N, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul, ← adj_mul, hKC, adj_one]
  have hKN' : K * N' = 0 := by
    simp only [N', Matrix.mul_sub, ← Matrix.mul_assoc, hKC, hKB, Matrix.one_mul, Matrix.zero_mul, sub_self, sub_zero]
  have hPmN' : Pm * N' = 0 := by
    simp only [N', Matrix.mul_sub, ← Matrix.mul_assoc, hPmC, hPmB, Matrix.one_mul, Matrix.zero_mul, sub_zero, sub_self]
  have hPiN' : Pi * N' = 1 := by
    simp only [N', Matrix.mul_sub, ← Matrix.mul_assoc, hPiC, hPiB, Matrix.zero_mul, sub_zero]
    simpa only [Pi, N, Matrix.mul_assoc] using hPiN
  let M : Matrix (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) (Fin V.rank) D.host.E :=
    Matrix.fromRows K (Matrix.fromRows Pm Pi)
  let Q : Matrix (Fin V.rank) (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) D.host.E :=
    Matrix.fromCols C (Matrix.fromCols B N')
  have hMQ : M * Q = 1 := by
    simp only [M, Q, Matrix.fromRows_mul, Matrix.mul_fromCols, hKC, hKB, hKN', hPmC, hPmB, hPmN', hPiC, hPiB, hPiN']
    refine Matrix.ext fun a b => ?_
    rcases a with a | a | a <;> rcases b with b | b | b <;> simp [Matrix.one_apply]
  have e : Fin r ⊕ (Fin V'.rank ⊕ Fin r) ≃ Fin V.rank :=
    Fintype.equivOfCardEq (by simp [hs.rank]; ring)
  have hQM : Q * M = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hMQ
  refine ⟨N', ?_⟩
  simpa only [M, Q, Matrix.fromCols_mul_fromRows] using hQM

end GlobalTheory.HalfDecomp

namespace GlobalTheory.HalfDecomp

theorem half_decomp : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ (a : AE D) (u : WO V W), IsHalf a u → ∃ (y : Mx D W.rank r) (x : WO V' W) (t : Mx D W.rank r), IsHalf a y ∧ IsHalf a x ∧ IsHalf a t ∧ u = isoPart V W C y + midPart V V' W B x + restEmb V W K t := by
  intro D V V' W r C B hs K hKC hKB a u hu
  obtain ⟨N', hN'⟩ := exists_decomp_one V V' C B hs K hKC hKB
  refine ⟨HMul.hMul (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (N'.map (incA D)),
    HMul.hMul (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (B.map (incA D)),
    HMul.hMul (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (C.map (incA D)),
    isHalf_mul hu _, isHalf_mul hu _, isHalf_mul hu _, ?_⟩
  have h1 := congrArg (fun M : Matrix (Fin V.rank) (Fin V.rank) D.host.E => M.map (incA D)) hN'
  simp only [Matrix.map_add (f := _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h1
  simp only [isoPart, midPart, restEmb, Matrix.map_mul, Matrix.mul_assoc]
  conv_lhs => rw [← Matrix.mul_one u, ← h1]
  simp only [Matrix.map_add _ (map_add (incA D)), Matrix.map_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

end GlobalTheory.HalfDecomp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SobFrame

section Conj

variable {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}

theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) (P⁻¹ * X * P) w = dRep σ X w := by
  unfold dRep
  simp only [exp_smul_conj_inv hP, conj_cancel hP]

theorem foldr_dRep_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : H) :
    (l.map fun X => P⁻¹ * X * P).foldr (dRep fun g => σ (P * g * P⁻¹)) w = l.foldr (dRep σ) w := by
  induction l with
  | nil => rfl
  | cons X l ih => simp only [List.map_cons, List.foldr_cons, ih, dRep_conj_inv hP]

theorem smoothVec_conj_inv (hP : IsUnit P) {A B : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hAB : ∀ X ∈ A, P⁻¹ * X * P ∈ B) {w : H} (hw : SmoothVec B (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec A σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => hAB _ (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

end Conj

theorem conj_mem_lieAt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) :
    (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
  have hX' : Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X = 0 := hX
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
  rw [← M.fr_gram τ]
  have e : ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) +
      (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * X * M.fr τ) =
      (M.fr τ)ᴴ * ((Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X) * M.fr τ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hc, Matrix.mul_nonsing_inv_cancel_left _ _ hd,
      Matrix.add_mul, Matrix.mul_add]
  rw [e, hX', Matrix.zero_mul, Matrix.mul_zero]

theorem sobCont_rep_of_bound : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ)
    (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) →
    (∀ w, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w → ‖ℓ w‖ ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) →
    Sobolev₂ (lieAt V τ) (M.rep τ) ℓ := by
  intro D V S M τ ℓ L C hL hC
  have hP := M.fr_unit τ
  refine ⟨L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ), C, ?_, fun w hw => ?_⟩
  · intro l hl X hX
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
    obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
    exact conj_mem_lieAt M τ (hL l₀ hl₀ X₀ hX₀)
  · have hw' : SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w :=
      smoothVec_conj_inv (σ := M.σ τ) hP (fun _ hX => conj_mem_lieAt M τ hX) hw
    have hs : ((L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ)).map
        fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum = GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w := by
      unfold GlobalTheory.SmoothGlob.sobNorm
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun l _ => ?_
      exact congrArg norm (foldr_dRep_conj_inv (σ := M.σ τ) hP l w)
    rw [hs]
    exact hC w hw'

end GlobalTheory.SobFrame

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.RderCAdjoint

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem Rder_neg_dir (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ (-X) φ = -Rder θ V τ X φ := by
  funext g
  have := deriv_comp_neg (fun t : ℝ => φ (g * oneP θ V τ X t)) 0
  simpa only [Rder, oneP, smul_neg, neg_smul, neg_zero, Pi.neg_apply] using this

theorem conjAt_adjoint (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    conjAt V τ ((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ) = -Z := by
  have hu := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V τ
  unfold conjAt
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH,
    ← mul_assoc, nonsing_inv_mul _ hu, one_mul, mul_assoc, nonsing_inv_mul _ hu, mul_one]

theorem RderC_adjoint_eq (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V τ ((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ) φ =
      -Rder θ V τ ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) φ +
        Complex.I • Rder θ V τ ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) φ := by
  unfold RderC
  rw [conjAt_adjoint]
  have hW : (gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ = -conjAt V τ Z := by simp [conjAt]
  rw [hW, ← Rder_neg_dir, ← smul_neg, neg_add, add_comm (-Z), neg_sub_neg]

theorem rderC_adjoint : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
    (A : Submodule ℂ (GA D V → ℂ)) (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ),
    (∀ X ∈ lieAt V τ, ∀ x ∈ A, ∀ y ∈ A, b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∀ (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ x ∈ A, ∀ y ∈ A,
      b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y := by
  intro D θ V τ A b hb Z x hx y hy
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  rw [RderC_adjoint_eq]
  unfold RderC
  rw [map_add (f := _), map_smul, hb _ h1 x hx y hy, hb _ h2 x hx y hy, map_add (f := _), map_neg, map_smulₛₗ]
  simp

end GlobalTheory.RderCAdjoint

end
end
