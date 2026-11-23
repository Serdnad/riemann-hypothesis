module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.PureFix

theorem pureA_fixed : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (m₁ M m₃ : ℕ), 0 < m₁ → 0 < M → 0 < m₃ → (∀ a : κ → AF F, IsMulInt F m₁ a → ∀ x : κ → FiniteAdeleRing (𝓞 F) F, g (x + fun i => (a i).2) = g x) → (∀ x : κ → AF F, g (fun i => (x i).2) ≠ 0 → ∀ i v, ‖(M : Fv F v) * evFin F v (x i)‖ ≤ 1) → (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ ‖(m₃ : Fv F v)‖) → ψ t = 1) → ∀ f : (κ → mixedEmbedding.mixedSpace F) → ℂ, ∀ a b : κ → AF F, IsMulInt F (2 * m₁ * M * m₃) a → IsMulInt F (2 * m₁ * M * m₃) b → schr ψ (a, b) (pureA F f g) = pureA F f g := by
  intro F _ _ κ _ ψ g m₁ M m₃ hm₁ hM hm₃ hg hx hψ f a b ha hb
  funext x
  have ha' : IsMulInt F m₁ a := by
    have e : 2 * m₁ * M * m₃ = (2 * M * m₃) * m₁ := by ring
    rw [e] at ha; exact ha.mono
  have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + a) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i; congr 1; show (x i).1 + (a i).1 = (x i).1; rw [ha.1 i, add_zero]
  have e2 : (fun i => ((x + a) i).2) = (fun i => (x i).2) + fun i => (a i).2 := rfl
  simp only [schr, pureA]
  rw [e1, e2, hg a ha' (fun i => (x i).2)]
  by_cases h0 : g (fun i => (x i).2) = 0
  · simp [h0]
  · have hs : ∀ (c d : κ → AF F), (∀ i, (d i).1 = 0) → (c ⬝ᵥ d).1 = 0 := by
      intro c d hd
      change fstA F (∑ i, c i * d i) = 0

      rw [map_sum]; refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_mul]; change (c i).1 * (d i).1 = 0; rw [hd i, mul_zero]
    have hnat : ∀ (v : HeightOneSpectrum (𝓞 F)) (n : ℕ), ‖(n : Fv F v)‖ ≤ 1 :=
      fun v n => GlobalTheory.SmoothForms.denom_norm_natCast_le_one v n
    rw [hψ _ ?_ ?_, one_mul]
    · change (x ⬝ᵥ b).1 + (⅟2 : AF F).1 * (a ⬝ᵥ b).1 = 0
      rw [hs x b hb.1, hs a b hb.1, mul_zero, add_zero]
    · intro v
      have hb' : ∀ i, ‖evFin F v (b i)‖ ≤ ‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by
        intro i; have := hb.2 v i; push_cast at this; simpa [norm_mul, mul_assoc] using this
      have h2 : ‖evFin F v (⅟2 : AF F)‖ * ‖(2 : Fv F v)‖ = 1 := by
        rw [← norm_mul, show (2 : Fv F v) = evFin F v (2 : AF F) from (map_ofNat _ 2).symm, ← map_mul,
          invOf_mul_self, map_one, norm_one]
      have ha2 : ∀ i, ‖evFin F v (⅟2 * a i)‖ ≤ 1 := by
        intro i
        have := ha.2 v i
        push_cast at this
        rw [map_mul, norm_mul]
        calc ‖evFin F v (⅟2 : AF F)‖ * ‖evFin F v (a i)‖
            ≤ ‖evFin F v (⅟2 : AF F)‖ * ‖(2 * m₁ * M * m₃ : Fv F v)‖ := by gcongr
          _ = (‖evFin F v (⅟2 : AF F)‖ * ‖(2 : Fv F v)‖) * ‖((m₁ * M * m₃ : ℕ) : Fv F v)‖ := by
              push_cast; simp only [norm_mul]; ring
          _ ≤ 1 := by rw [h2, one_mul]; exact hnat v _

      rw [map_add (f := _), dotProduct, dotProduct, Finset.mul_sum, map_sum, map_sum]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
        rw [map_mul, norm_mul]
        calc ‖evFin F v (x i)‖ * ‖evFin F v (b i)‖
            ≤ ‖evFin F v (x i)‖ * (‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖) := by
              gcongr; exact hb' i
          _ = ‖(M : Fv F v) * evFin F v (x i)‖ * ‖((2 * m₁ : ℕ) : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by
              push_cast; simp only [norm_mul]; ring
          _ ≤ 1 * 1 * ‖(m₃ : Fv F v)‖ := by
              gcongr
              · exact hx x h0 i v
              · exact hnat v _
          _ = ‖(m₃ : Fv F v)‖ := by ring
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
        rw [← mul_assoc, map_mul, norm_mul]
        calc ‖evFin F v (⅟2 * a i)‖ * ‖evFin F v (b i)‖
            ≤ 1 * (‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖) := by
              gcongr
              · exact ha2 i
              · exact hb' i
          _ = ‖((2 * m₁ * M : ℕ) : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by push_cast; simp only [norm_mul]; ring
          _ ≤ 1 * ‖(m₃ : Fv F v)‖ := by gcongr; exact hnat v _
          _ = ‖(m₃ : Fv F v)‖ := one_mul _

end GlobalTheory.PureFix

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

noncomputable section

namespace GlobalTheory.DblScal

open Matrix

theorem isUnit_det_dbl_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (hJ : J.det ≠ 0) :
    IsUnit ((dbl J).map t).det := by
  have e : ((dbl J).map t).det = (t : E →+* Fv F v) (dbl J).det := by
    rw [RingHom.map_det]; rfl
  rw [e, isUnit_iff_ne_zero]
  have hd : (dbl J).det ≠ 0 := by
    rw [dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact mul_ne_zero hJ (mul_ne_zero (pow_ne_zero _ (by simp)) hJ)
  exact (map_ne_zero_iff _ (t : E →+* Fv F v).injective).2 hd

theorem unitary_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (X : UD σ J) :
    ((X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW t))ᵀ * (dbl J).map t *
      (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW (t.comp σ)) = (dbl J).map t := by
  have hX : (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ * dbl (incM F J) *
      (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F J) := X.2
  have h := congrArg (fun M => M.map (piW t)) hX
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  have eD : (dbl (incM F J)).map (piW t) = (dbl J).map t := by
    ext (i | i) (j | j) <;> simp [dbl, incM, GlobalTheory.Div.CoordOpp.piW_inclR]
  have eC : ((X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ)).map (piW t) =
      (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW (t.comp σ)) := by
    ext i j; simp [GlobalTheory.Div.CoordOpp.piW_cA]
  rw [eD, eC] at h
  simpa [Matrix.transpose_map] using h

end GlobalTheory.DblScal

open GlobalTheory.DblScal in
theorem GlobalTheory.DblScal.locMatD_injOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), J.det ≠ 0 →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)),
    Set.InjOn (locMatD (σ := σ) (J := J) t c) (UDAt σ J (evFin F v)) := by
  intro F E _ _ _ _ _ σ hcm d J hJ v t c p hp q hq hpq
  set P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := p.1.val with hPdef
  set Q : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := q.1.val with hQdef

  have e0 : (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) p.1 * dsum c =
      (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) q.1 * dsum c := hpq
  have eG := mul_left_cancel (mul_right_cancel e0)
  have h1 : P.map (piW t) = Q.map (piW t) := congrArg Units.val eG

  have h2 : P.map (piW (t.comp σ)) = Q.map (piW (t.comp σ)) := by
    have hUp := unitary_at t p
    have hUq := unitary_at t q
    rw [← hPdef] at hUp
    rw [← hQdef, ← h1] at hUq
    set g := Matrix.GeneralLinearGroup.map (piW t) p.1
    have hg : (g : Matrix _ _ (Fv F v)) = P.map (piW t) := rfl
    have hinv : ((g⁻¹ : GL _ (Fv F v)) : Matrix _ _ (Fv F v))ᵀ * (P.map (piW t))ᵀ = 1 := by
      rw [← hg, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have e1 : (dbl J).map t * P.map (piW (t.comp σ)) = (dbl J).map t * Q.map (piW (t.comp σ)) := by
      have := hUp.trans hUq.symm
      have := congrArg (fun M => ((g⁻¹ : GL _ (Fv F v)) : Matrix _ _ (Fv F v))ᵀ * M) this
      simpa only [← Matrix.mul_assoc, hinv, Matrix.one_mul] using this
    have hD := isUnit_det_dbl_map t hJ
    have := congrArg (fun M => ((dbl J).map t)⁻¹ * M) e1
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD, Matrix.one_mul] using this

  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v)
  have hev : evFin F v (1 - e) = 0 := by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have hp' : At (evFin F v) (P - 1) := hp
  have hq' : At (evFin F v) (Q - 1) := hq
  have hM : P - Q = e • (P - Q) := by
    have h0 : (1 - e) • (P - Q) = 0 := by
      have : P - Q = (P - 1) - (Q - 1) := by abel
      rw [this, smul_sub, hp' (1 - e) hev, hq' (1 - e) hev, sub_zero]
    rw [sub_smul, one_smul, sub_eq_zero] at h0
    exact h0
  refine Subtype.ext (Units.ext ?_)
  change P = Q
  rw [← sub_eq_zero, hM]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply]
  apply GlobalTheory.InertVacIso.smul_eq_zero_of_compFin
  apply GlobalTheory.AdelicU.split_ext hcm t
  · change piW t ((P - Q) i j) = splitProj t 0
    rw [map_zero, Matrix.sub_apply, map_sub, sub_eq_zero]
    exact congrFun (congrFun h1 i) j
  · change piW (t.comp σ) ((P - Q) i j) = splitProj (t.comp σ) 0
    rw [map_zero, Matrix.sub_apply, map_sub, sub_eq_zero]
    exact congrFun (congrFun h2 i) j

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertDbl

theorem diag_mulVec_mem_latAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (h : M * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * t)
    (hM : ∀ z ∈ latAtD W v, M *ᵥ z ∈ latAtD W v) (z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hz : z ∈ GlobalTheory.InertSph.latAt W v) :
    t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  have key : ∀ y : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E),
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ y = Sum.elim y y := by
    intro y
    simp [diagCols, Matrix.fromRows_mulVec]
  have h1 : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ latAtD W v := by
    rw [key]; exact ⟨hz, hz⟩
  have h2 := hM _ h1
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, key] at h2
  exact h2.1

theorem parD_diag_action :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)),
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ W v, ∀ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.InertDbl.matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) →
      At (evFin F v) ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
        ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ d W v p hp t h'
  have h : matD p * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := h'
  obtain ⟨⟨hAt, hK⟩, -⟩ := hp
  have hinv : matD p⁻¹ * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    have h1 : matD p⁻¹ * matD p = 1 := p.1.inv_mul
    have h2 : (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *
        ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 1 := t.mul_inv
    calc matD p⁻¹ * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
        = matD p⁻¹ * ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *
            ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))) := by rw [h2, Matrix.mul_one]
      _ = _ := by
        rw [← Matrix.mul_assoc (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨?_, fun z hz => ⟨diag_mulVec_mem_latAt W v _ _ h (fun y hy => (hK y hy).1) z hz,
    diag_mulVec_mem_latAt W v _ _ hinv (fun y hy => (hK y hy).2) z hz⟩⟩
  intro u hu
  have h0 := hAt u hu
  have h3 : (matD p - 1) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]
  have h4 : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *
      (u • ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)) = 0 := by
    rw [Matrix.mul_smul, ← h3, ← Matrix.smul_mul, h0, Matrix.zero_mul]
  ext i j
  have h5 := congrFun (congrFun h4 (Sum.inl i)) j
  rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at h5
  exact h5

end GlobalTheory.InertDbl
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacDiag

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mat_mul_mat_inv {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (k : UA σ J) :
    mat k * mat k⁻¹ = 1 := by
  show ((k * k⁻¹ : UA σ J) : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).1 = 1
  rw [mul_inv_cancel]; rfl

theorem mat_inv_mul_mat {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (k : UA σ J) :
    mat k⁻¹ * mat k = 1 := by
  show ((k⁻¹ * k : UA σ J) : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).1 = 1
  rw [inv_mul_cancel]; rfl

def diagOne {R : Type} [CommRing R] {d : ℕ} (A B : Matrix (Fin d) (Fin d) R) (hAB : A * B = 1) (hBA : B * A = 1) :
    GL (Fin d ⊕ Fin d) R :=
  ⟨fromBlocks A 0 0 1, fromBlocks B 0 0 1, by simp [fromBlocks_multiply, hAB, ← fromBlocks_one],
    by simp [fromBlocks_multiply, hBA, ← fromBlocks_one]⟩

theorem diag_mem_KD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) :
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ g : GlobalTheory.DblVac.UD σ W,
      ((g : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks (mat k) 0 0 1 ∧ g ∈ GlobalTheory.DblVac.KD σ W v := by
  intro k hk
  let M := diagOne (mat k) (mat k⁻¹) (mat_mul_mat_inv k) (mat_inv_mul_mat k)
  have hU : (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ * dbl (incM F W.J) *
      (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (cA σ) = dbl (incM F W.J) := by
    have hk2 : (mat k)ᵀ * incM F W.J * (mat k).map (cA σ) = incM F W.J := k.2
    show (fromBlocks (mat k) 0 0 1)ᵀ * fromBlocks (incM F W.J) 0 0 (-incM F W.J) *
      (fromBlocks (mat k) 0 0 (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))).map (cA σ) = fromBlocks (incM F W.J) 0 0 (-incM F W.J)
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp [hk2, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
  refine ⟨⟨M, hU⟩, rfl, ?_, ?_⟩
  · intro u hu
    have h1 := hk.1 u hu
    show u • (fromBlocks (mat k) 0 0 1 - 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 0
    have h1' : u • (mat k - 1) = 0 := h1
    rw [← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_smul, ← sub_eq_add_neg]
    simp [h1']
  · intro z hz
    have hinv : GlobalTheory.DblVac.matD (⟨M, hU⟩ : GlobalTheory.DblVac.UD σ W)⁻¹ = fromBlocks (mat k⁻¹) 0 0 1 := rfl
    have hfw : GlobalTheory.DblVac.matD (⟨M, hU⟩ : GlobalTheory.DblVac.UD σ W) = fromBlocks (mat k) 0 0 1 := rfl
    rw [hinv, hfw]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [fromBlocks_mulVec]; simpa using ((hk.2 _ hz.1).1)
    · rw [fromBlocks_mulVec]; simpa using hz.2
    · rw [fromBlocks_mulVec]; simpa using ((hk.2 _ hz.1).2)
    · rw [fromBlocks_mulVec]; simpa using hz.2

end GlobalTheory.DblVacDiag
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section
namespace GlobalTheory.KapOrb

theorem exists_unitary_of_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), IsModelMap w e B u x γ ψ → ∀ s ∈ B.T, ∃ h : GLw n w, h ∈ UL n w ∧ h * γ = γ * h ∧ ∀ y, ψ ((s : B.A) * y) = h.val *ᵥ ψ y := by
  intro E _ _ _ w K e B u x n γ ψ hψ s hs
  obtain ⟨hsl, hu, hh⟩ := hψ
  have hs' : (s : B.A) * B.σ (s : B.A) = 1 := hs
  let Lm : B.A → (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) := fun a =>
    { toFun := fun v => ψ (a * ψ.symm v)
      map_add' := by intro v v'; simp [mul_add]
      map_smul' := by
        intro c v
        have h1 : ψ.symm (c • v) = e.symm c • ψ.symm v := by
          apply ψ.injective
          rw [ψ.apply_symm_apply, hsl, ψ.apply_symm_apply, e.apply_symm_apply]
        simp only [RingHom.id_apply]
        rw [h1, Algebra.mul_smul_comm, hsl, e.apply_symm_apply] }
  have hLm : ∀ a y, Lm a (ψ y) = ψ (a * y) := by
    intro a y; simp [Lm]
  have hLmul : ∀ a b, Lm a ∘ₗ Lm b = Lm (a * b) := by
    intro a b; ext v; simp [Lm, mul_assoc]
  have hLone : Lm 1 = LinearMap.id := by
    ext v; simp [Lm]
  let h : GLw n w :=
    ⟨LinearMap.toMatrix' (Lm (s : B.A)), LinearMap.toMatrix' (Lm ((s⁻¹ : B.Aˣ) : B.A)),
      by rw [← LinearMap.toMatrix'_comp, hLmul, Units.mul_inv, hLone, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, hLmul, Units.inv_mul, hLone, LinearMap.toMatrix'_id]⟩
  have hmv : ∀ v, h.val *ᵥ v = Lm (s : B.A) v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hpres : ∀ v v', stdH w (h.val *ᵥ v) (h.val *ᵥ v') = stdH w v v' := by
    intro v v'
    obtain ⟨y, rfl⟩ := ψ.surjective v
    obtain ⟨z, rfl⟩ := ψ.surjective v'
    rw [hmv, hmv, hLm, hLm, hh, hh]
    congr 1
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    congr 1
    rw [map_mul]
    calc x * ((s : B.A) * y) * (B.σ (s : B.A) * B.σ z) = x * y * B.σ z * ((s : B.A) * B.σ (s : B.A)) := by ring
      _ = x * y * B.σ z := by rw [hs', mul_one]
  refine ⟨h, ?_, ?_, ?_⟩
  · unfold UL
    split_ifs
    · exact Subgroup.mem_top _
    · show cT (cj w) h.val * 1 * h.val = 1
      ext i j
      have hp := hpres (Pi.single j 1) (Pi.single i 1)
      rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hp
      rw [Matrix.mul_one, Matrix.mul_apply, Matrix.one_apply]
      simp only [stdH, Matrix.transpose_apply, Matrix.col_apply] at hp
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
      rw [Finset.sum_congr rfl (fun k _ => mul_comm (cj w (h.val k i)) (h.val k j)), hp]
      by_cases hij : i = j
      · subst hij; simp [Pi.single_apply]
      · rw [if_neg hij, Finset.sum_eq_zero]
        intro k _
        by_cases hk : k = j
        · subst hk; simp [Pi.single_apply, Ne.symm hij, hij]
        · simp [Pi.single_apply, hk]
  · apply Units.ext
    apply Matrix.toLin'.injective
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul]
    refine LinearMap.ext fun v => ?_
    obtain ⟨y, rfl⟩ := ψ.surjective v
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [← hu, hmv, hmv, hLm, hLm, ← hu, mul_left_comm]
  · intro y
    rw [hmv, hLm]

end GlobalTheory.KapOrb
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb

theorem pullLat_mul_eq_mulLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (h g : GLw n w) (a : B.Aˣ), (∀ y, ψ ((a : B.A) * y) = h.val *ᵥ ψ y) → pullLat w B ψ (h * g) = GlobalTheory.UnitLemma.mulLat K.O (a : B.A) (pullLat w B ψ g) := by
  intro E _ _ _ w K B n ψ h g a ha
  have hinv : ∀ z, ψ (((a⁻¹ : B.Aˣ) : B.A) * z) = (h⁻¹ : GLw n w).val *ᵥ ψ z := by
    intro z
    have h1 := ha (((a⁻¹ : B.Aˣ) : B.A) * z)
    rw [← mul_assoc, Units.mul_inv, one_mul] at h1
    rw [h1, Matrix.mulVec_mulVec]
    have : ((h⁻¹ : GLw n w).val * h.val) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.one_mulVec]
  have key : ∀ y, y ∈ pullLat w B ψ (h * g) ↔ ((a⁻¹ : B.Aˣ) : B.A) * y ∈ pullLat w B ψ g := by
    intro y
    show (∀ (c : K.O) (i : Fin n), (((h * g)⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E) ↔
      (∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • (((a⁻¹ : B.Aˣ) : B.A) * y))) i ∈
        w.adicCompletionIntegers E)
    have e1 : ∀ c : K.O, ψ (c • (((a⁻¹ : B.Aˣ) : B.A) * y)) = (h⁻¹ : GLw n w).val *ᵥ ψ (c • y) := by
      intro c
      rw [← hinv, Algebra.mul_smul_comm]
    have e2 : ((h * g)⁻¹ : GLw n w).val = (g⁻¹ : GLw n w).val * (h⁻¹ : GLw n w).val := by
      rw [_root_.mul_inv_rev, Units.val_mul]
    simp only [e1, e2, Matrix.mulVec_mulVec]
  ext y
  constructor
  · intro hy
    refine ⟨((a⁻¹ : B.Aˣ) : B.A) * y, (key y).1 hy, ?_⟩
    show (a : B.A) * (((a⁻¹ : B.Aˣ) : B.A) * y) = y
    rw [← mul_assoc, Units.mul_inv, one_mul]
  · rintro ⟨z, hz, rfl⟩
    rw [key]
    show ((a⁻¹ : B.Aˣ) : B.A) * ((a : B.A) * z) ∈ pullLat w B ψ g
    rw [← mul_assoc, Units.inv_mul, one_mul]
    exact hz

end GlobalTheory.KapOrb
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

theorem _root_.GlobalTheory.T.unitaryLattice_isLattice_selfDual_hermitianModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ q : UL n w, IsLat K.O K.E (unitLat e B ψ q) ∧ ∀ y, y ∈ unitLat e B ψ q ↔ ∀ z ∈ unitLat e B ψ q, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  first | exact @GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual | exact GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual | (intros; apply GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual <;> assumption)
end
