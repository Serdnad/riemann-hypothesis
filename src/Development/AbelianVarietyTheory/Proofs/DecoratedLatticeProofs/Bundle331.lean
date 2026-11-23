module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperators
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle321
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle323
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

namespace GlobalTheory.FinPl.Rebase

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nsmul_half (p : SplitPt D k) {S T : HSp D} {LS MS : Lat S} {LT MT : Lat T} (hLS : IsSelfDualC S LS)
    (hLT : IsSelfDualC T LT) (hMS : IsSelfDualC S MS) (hMT : IsSelfDualC T MT) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v),
      IsHalf p.e u → N • u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) := by
  obtain ⟨ε, hε, heq⟩ := p.above
  have he := p.split.1
  have hec := p.split.2.1
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hLS
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hLT
  obtain ⟨M, hM, hMm⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (ΛS' := LS) (ΛT' := LT)
    hMS.1.fg hMT.1.fg inferInstance inferInstance
  refine ⟨M, hM, fun u hu hh => ?_⟩
  have h1 := (GlobalTheory.PlaceModel.idem_smul_mem hε he heε (hMm u (GlobalTheory.PlaceModel.latO_le_top _ hu))).1
  have h2 : p.e • u = u := (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh)
  rwa [smul_comm, h2] at h1

theorem isHalf_nsmul {S T : HSp D} {e : AE D} {u : WO S T} (hu : IsHalf e u) (N : ℕ) : IsHalf e (N • u) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem sbHalf_mono : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → ∀ Φ : WO S T → ℂ, IsSBHalf p.e (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)) Φ → IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) Φ := by
  intro D k _ _ _ _ p S T LS MS LT MT hLS hLT hMS hMT Φ hΦ
  obtain ⟨N, hN, hNm⟩ := exists_nsmul_half p hMS hMT hLS hLT
  obtain ⟨M, hM, hMm⟩ := exists_nsmul_half p hLS hLT hMS hMT
  obtain ⟨h1, k', hk', h2, h3⟩ := hΦ
  refine ⟨h1, k' * N * M, Nat.mul_pos (Nat.mul_pos hk' hN) hM, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have hu' : M • u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) :=
      nsmul_mem hu M
    have e : (k' * N * M) • u = k' • (N • (M • u)) := by rw [smul_smul, smul_smul, mul_assoc]
    rw [e]
    exact h2 _ (hNm _ hu' (isHalf_nsmul hh M)) (isHalf_nsmul (isHalf_nsmul hh M) N) t
  · have ht' := h1 t ht
    have e : (k' * N * M) • t = M • (N • (k' • t)) := by
      rw [smul_smul, smul_smul, mul_comm M N, mul_comm (N * M) k', mul_assoc]
    rw [e]
    exact hMm _ (nsmul_mem (h3 t ht) N) (isHalf_nsmul (isHalf_nsmul ht' k') N)

theorem placeIdem_mul {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {a : AE D} (ha : a ∈ idAt D (· = v)) :
    algebraMap (AF D.host.F) (AE D) ε * a = a := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  obtain ⟨hi, hw⟩ := GlobalTheory.FinPl.LatMem.mem_idAt_iff.1 ha
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun w => ?_
  · rw [map_mul, GlobalTheory.FinPl.LatMem.compInf_eq_zero hi, mul_zero]
  · rw [map_mul]
    have he : GlobalTheory.AdelicU.compFin D.host.F D.host.E w (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) =
        evalV D.host.F w β ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    by_cases hv : w = v
    · subst hv
      rw [he, h1]
      exact one_mul _
    · rw [GlobalTheory.FinPl.LatMem.compFin_eq_compAt a w, hw w hv, mul_zero]

theorem eq_add_halves (p : SplitPt D k) {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {u : WO S T} (hu : u ∈ latO S T LS LT (· = p.v)) : p.e • u + cA D p.e • u = u := by
  obtain ⟨ε, hε, heq⟩ := p.above
  rw [← add_smul, heq]
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact placeIdem_mul hε (GlobalTheory.FinPl.LatMem.latO_mxAt hu i j)

theorem smul_conj_zero (e e' : AE D) (h : e' * cA D e' = 0) {S T : HSp D} (u : WO S T) (hu : e' • u = u) :
    cA D e' • (e • u) = 0 := by
  rw [← hu, smul_smul, smul_smul]
  rw [mul_comm (cA D e') e]
  rw [mul_assoc]
  rw [mul_comm (cA D e') e']
  rw [h, mul_zero, zero_smul]

theorem isHalf_add {S T : HSp D} {e : AE D} {a b : WO S T} (ha : IsHalf e a) (hb : IsHalf e b) : IsHalf e (a + b) :=
  fun i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]

theorem latVac_image : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 f₀ Tm → IsLatVac (heisO ψ S T) (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)) (Tm (halfInd p.e (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)))) := by
  intro D k _ _ _ _ p ψ hψ S T LS MS LT MT hLS hLT hMS hMT f₀ Tm hTm
  obtain ⟨ε, hε, heq⟩ := p.above
  have he := p.split.1
  have hec := p.split.2.1
  have hce : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by
    rw [← heq]; linear_combination hce + hec
  set Λ' := latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v) with hΛ'
  have hΦ₀ : IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v))
      (halfInd p.e Λ') :=
    sbHalf_mono D k p S T LS MS LT MT hLS hLT hMS hMT _ (GlobalTheory.isSBHalf_halfInd p.e Λ')
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T MS MT hψ hMS hMT).1
  have hLL' : ∀ x ∈ Λ', IsHalf p.e x → ∀ y ∈ Λ', ψ (symplO S T x y) = 1 := fun x hx hh y hy =>
    (hdual x (GlobalTheory.PlaceModel.infPart_half hε heε ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh))).1
      (GlobalTheory.PlaceModel.latO_le_top _ hx) y (GlobalTheory.PlaceModel.latO_le_top _ hy)
  have hX : ∀ x ∈ Λ', IsHalf p.e x → heisO ψ S T x (Tm (halfInd p.e Λ')) = Tm (halfInd p.e Λ') := by
    intro x hx hh
    rw [← hTm.trans _ hΦ₀ x hh]
    congr 1
    funext t
    have hc : (t + x ∈ Λ' ∧ IsHalf p.e (t + x)) ↔ (t ∈ Λ' ∧ IsHalf p.e t) := by
      rw [Λ'.add_mem_cancel_right hx]
      refine and_congr_right fun _ => forall_congr' fun i => forall_congr' fun j => ?_
      rw [Matrix.add_apply, mul_add, hh i j, add_left_inj]
    show halfInd p.e Λ' (t + x) = halfInd p.e Λ' t
    unfold halfInd
    by_cases h : t ∈ Λ' ∧ IsHalf p.e t
    · rw [if_pos (hc.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]
  have hY : ∀ y ∈ Λ', IsHalf (cA D p.e) y → heisO ψ S T y (Tm (halfInd p.e Λ')) = Tm (halfInd p.e Λ') := by
    intro y hy hh
    rw [← hTm.modul _ hΦ₀ y hh]
    congr 1
    funext t
    by_cases h : t ∈ Λ' ∧ IsHalf p.e t
    · rw [hLL' t h.1 h.2 y hy, one_mul]
    · simp [halfInd, h]
  have key : ∀ x y : WO S T, x ∈ Λ' → IsHalf p.e x → y ∈ Λ' → IsHalf (cA D p.e) y →
      ψ (symplOH S T y x) = 1 → heisO ψ S T (x + y) (Tm (halfInd p.e Λ')) = Tm (halfInd p.e Λ') := by
    intro x y hx hxh hy hyh h1
    have h := GlobalTheory.PlaceModel.heisL_heisL S T ψ y x (Tm (halfInd p.e Λ'))
    change heisO ψ S T y (heisO ψ S T x (Tm (halfInd p.e Λ'))) =
      ψ (symplOH S T y x) • heisO ψ S T (y + x) (Tm (halfInd p.e Λ')) at h
    rw [hX x hx hxh, hY y hy hyh, h1, one_smul, add_comm] at h
    exact h.symm
  have hpart : ∀ u ∈ Λ', (p.e • u ∈ Λ' ∧ IsHalf p.e (p.e • u)) ∧
      (cA D p.e • u ∈ Λ' ∧ IsHalf (cA D p.e) (cA D p.e • u)) := by
    intro u hu
    have a1 := GlobalTheory.PlaceModel.idem_smul_mem hε he heε (GlobalTheory.PlaceModel.latO_le_top _ hu)
    have a2 := GlobalTheory.PlaceModel.idem_smul_mem hε hce heε' (GlobalTheory.PlaceModel.latO_le_top _ hu)
    exact ⟨⟨a1.1, (GlobalTheory.PlaceModel.isHalf_iff S T).2 a1.2⟩, ⟨a2.1, (GlobalTheory.PlaceModel.isHalf_iff S T).2 a2.2⟩⟩
  refine ⟨fun w hw => ?_, fun e' hse' u hu hh => ?_⟩
  · obtain ⟨⟨hx, hxh⟩, ⟨hy, hyh⟩⟩ := hpart w hw
    have e2 : 2 • w = (p.e • w + p.e • w) + (cA D p.e • w + cA D p.e • w) := by
      conv_lhs => rw [← eq_add_halves p hw]
      abel
    rw [e2]
    refine key _ _ (add_mem hx hx) (isHalf_add hxh hxh) (add_mem hy hy) (isHalf_add hyh hyh) ?_
    have hb : ψ (symplO S T (cA D p.e • w) (p.e • w)) = 1 := by
      rw [GlobalTheory.PlaceModel.symplO_skew, AddChar.map_neg_eq_inv, hLL' _ hx hxh _ hy, inv_one]
    have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
      norm_num
    have h3 : symplOH S T (cA D p.e • w + cA D p.e • w) (p.e • w + p.e • w) =
        symplO S T (cA D p.e • w) (p.e • w) + symplO S T (cA D p.e • w) (p.e • w) := by
      unfold symplOH
      simp only [GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right]
      linear_combination (2 * symplO S T (cA D p.e • w) (p.e • w)) * h2
    rw [h3, AddChar.map_add_eq_mul, hb, one_mul]
  · obtain ⟨⟨hx, hxh⟩, ⟨hy, hyh⟩⟩ := hpart u hu
    rw [← eq_add_halves p hu]
    refine key _ _ hx hxh hy hyh ?_
    obtain ⟨-, hse2, -⟩ := hse'
    have hu' : e' • u = u := (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh)
    have h0 : symplO S T (cA D p.e • u) (p.e • u) = 0 := by
      have e1 : cA D p.e • u = e' • (cA D p.e • u) := by rw [smul_comm, hu']
      have e2 : cA D e' • (p.e • u) = 0 := smul_conj_zero p.e e' hse2 u hu'
      rw [e1, GlobalTheory.PlaceModel.symplO_smul, e2, GlobalTheory.PlaceModel.symplO_zero_right]
    unfold symplOH
    rw [h0, mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.FinPl.Rebase

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SplitVac

open GlobalTheory.LatVac NumberField

variable {D : D7}

def finIncl (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) →ₗ[D.host.F] AE D :=
  (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E

theorem finIncl_tmul (β : Af D.host.F) (x : D.host.E) :
    finIncl D (β ⊗ₜ[D.host.F] x) = pairA D.host.F 0 β ⊗ₜ[D.host.F] x := rfl

theorem infPart_finIncl (y : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (finIncl D y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul β x => rw [finIncl_tmul]; exact infPart_pair β x
  | add y z hy hz => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hy, hz, add_zero]

theorem finPart_finIncl (y : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (finIncl D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul β x => rw [finIncl_tmul]; exact finPart_pair β x
  | add y z hy hz => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hy, hz]

theorem eq_finIncl {z : AE D} (hz : infPart D z = 0) : z = finIncl D (finPart D z) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_parts
  · rw [RingHom.map_sub, hz, infPart_finIncl, sub_zero]
  · rw [RingHom.map_sub, finPart_finIncl, sub_self]

theorem finIncl_mul_mem {S T : HSp D} (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (v : GlobalTheory.FinPl.Pl D)
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hsupp : ∀ w, ¬ w = v → evalV D.host.F w α = 0)
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ LS)
    {t : Fin T.rank → D.host.E} (ht : t ∈ LT) {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    (Matrix.of fun i j => finIncl D y *
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβ, x, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨β * α, mul_mem_intAf hβ hα, fun w hw => ?_, a, ha, s, hs, x • t,
      LT.smul_mem x ht, ?_⟩
    · rw [map_mul, hsupp w hw, mul_zero]
    · ext i j
      simp only [Matrix.of_apply, finIncl_tmul, Algebra.TensorProduct.tmul_mul_tmul, pair_mul]
      congr 1
      change (x : D.host.E) * (a * t i * _) = a * ((x : D.host.E) * t i) * _
      ring
  | zero =>
    convert (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = v)).zero_mem using 1
    ext i j; simp
  | add y z _ _ hy hz =>
    convert add_mem hy hz using 1
    ext i j; simp only [Matrix.of_apply, Matrix.add_apply, LinearMap.map_add (f := _), add_mul]
  | neg y _ hy =>
    convert neg_mem hy using 1
    ext i j; simp only [Matrix.of_apply, Matrix.neg_apply, LinearMap.map_neg, neg_mul]

theorem idem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (u : WO S T), u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → (Matrix.of fun i j => q.e * u i j : WO S T) ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) ∧ ∀ i j, (q.e + cA D q.e) * u i j = u i j := by
  intro D k _ _ _ _ q S T LS LT u hu
  obtain ⟨ε, ⟨α₀, rfl, h1, h0⟩, hε⟩ := q.above
  have hee : q.e * q.e = q.e := q.split.1
  have hec : q.e * cA D q.e = 0 := q.split.2.1
  have hεinf : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α₀)) = 0 := infPart_pair α₀ 1
  have hinf : infPart D q.e = 0 := by
    have : q.e = q.e * (q.e + cA D q.e) := by rw [mul_add, hee, hec, add_zero]
    rw [this, RingHom.map_mul, hε, hεinf, mul_zero]
  have hfin : finPart D q.e ∈ intAE D := by
    have h := q.sec_pr 1
    rw [map_one, mul_one] at h
    rw [← h]
    exact (q.int_iff 1).1 (one_mem _)
  have he := eq_finIncl hinf
  refine ⟨?_, ?_⟩
  · induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩ := hw
      have h := finIncl_mul_mem LS LT q.v hα hsupp ha hs ht hfin
      rw [← he] at h
      simpa only [Matrix.of_apply] using h
    | zero =>
      convert (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v)).zero_mem using 1
      ext i j; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      ext i j; simp only [Matrix.of_apply, Matrix.add_apply, mul_add]
    | neg x _ hx =>
      convert neg_mem hx using 1
      ext i j; simp only [Matrix.of_apply, Matrix.neg_apply, mul_neg]
  · induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩ := hw
      intro i j
      have hmul : α₀ * α = α := by
        apply RestrictedProduct.ext
        intro w
        change evalV D.host.F w (α₀ * α) = evalV D.host.F w α
        rw [map_mul]
        by_cases hw : w = q.v
        · subst hw; rw [h1, one_mul]
        · rw [hsupp w hw, mul_zero]
      rw [hε, Matrix.of_apply]
      change (pairA D.host.F 0 α₀ ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, pair_mul, hmul]
    | zero => intro i j; simp
    | add x y _ _ hx hy => intro i j; rw [Matrix.add_apply, mul_add, hx, hy]
    | neg x _ hx => intro i j; rw [Matrix.neg_apply, mul_neg, hx]

end GlobalTheory.SplitVac
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.LeviUnitK

variable {D : D7}

theorem mul_mem_of_sub_one {S : HSp D} {L : Lat S} {P : Pl D → Prop} {c : AE D} (hc : finPart D (c - 1) ∈ intAE D)
    {z : Fin S.rank → AE D} (hz : z ∈ latV S L P) : (fun k => c * z k) ∈ latV S L P := by
  have h := GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hc hz
  have e : (fun k => c * z k) = z + fun k => (c - 1) * z k := by
    funext k; simp only [Pi.add_apply]; ring
  rw [e]; exact add_mem hz h

theorem mem_iff_of_unit {S : HSp D} {L : Lat S} {P : Pl D → Prop} {c c' : AE D} (hc : finPart D (c - 1) ∈ intAE D)
    (hc' : finPart D (c' - 1) ∈ intAE D) (h1 : c' * c = 1) (z : Fin S.rank → AE D) :
    z ∈ latV S L P ↔ (fun k => c * z k) ∈ latV S L P := by
  refine ⟨mul_mem_of_sub_one hc, fun h => ?_⟩
  have h2 := mul_mem_of_sub_one hc' h
  have e : (fun k => c' * (c * z k)) = z := by funext k; rw [← mul_assoc, h1, one_mul]
  rwa [e] at h2

theorem colMul_mul {m n : ℕ} (x : Mx D m n) (i : Fin n) (c a : AE D) :
    colMul x i (c * a) = fun k => c * colMul x i a k := by
  funext k; simp only [colMul, mul_assoc]

theorem diag_mulVec {R : Type} [CommRing R] {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (h : ∀ i j, i ≠ j → M i j = 0) (w : Fin n → R) (i : Fin n) : (M *ᵥ w) i = M i i * w i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_eq_single i (fun j _ hj => by rw [h i j (Ne.symm hj), zero_mul]) (by simp)

theorem inv_offdiag {R : Type} [CommRing R] {n : ℕ} (t : GL (Fin n) R) (ht : ∀ i j, i ≠ j → t.1 i j = 0) :
    ∀ i j, i ≠ j → (t⁻¹).1 i j = 0 := by
  intro i j hij
  have h1 : ((t⁻¹).1 * t.1) i j = 0 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_ne hij]
  have h2 : (t.1 * (t⁻¹).1) j j = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [ht k j hk, mul_zero]) (by simp)] at h1
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [ht j k (Ne.symm hk), zero_mul]) (by simp)] at h2
  calc (t⁻¹).1 i j = (t⁻¹).1 i j * (t.1 j j * (t⁻¹).1 j j) := by rw [h2, mul_one]
    _ = 0 := by rw [← mul_assoc, h1, zero_mul]

theorem inv_mul_diag {R : Type} [CommRing R] {n : ℕ} (t : GL (Fin n) R) (ht : ∀ i j, i ≠ j → t.1 i j = 0) (i : Fin n) :
    (t⁻¹).1 i i * t.1 i i = 1 := by
  have h1 : ((t⁻¹).1 * t.1) i i = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  rwa [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [ht k i hk, mul_zero]) (by simp)] at h1

theorem adj_apply' {m n : ℕ} (x : Mx D m n) (i : Fin n) (j : Fin m) : GlobalTheory.MixModel.adj x i j = cA D (x j i) := rfl

theorem cA_sub_one {a : AE D} (h : finPart D (a - 1) ∈ intAE D) : finPart D (cA D a - 1) ∈ intAE D := by
  rw [← map_one (cA D), ← map_sub]
  exact (GlobalTheory.FinPl.FrameLat.cA_int_iff _).2 h

end GlobalTheory.FinPl.LeviUnitK


open GlobalTheory.FinPl.LeviUnitK in
theorem GlobalTheory.FinPl.LeviUnitK.inK_levi : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → d.levi t ∈ grpAt S (· = v) → (∀ i, t.1 i i - 1 ∈ intAt D (· = v) ∧ (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → InK S L (· = v) (d.levi t) := by
  intro D S S₀ ρ d L L₀ v _hL hM t ht hg hu
  refine ⟨hg, fun y _ => ?_⟩
  have ht' := inv_offdiag t ht
  have hadj : ∀ i j, i ≠ j → GlobalTheory.MixModel.adj (t⁻¹).1 i j = 0 := fun i j hij => by
    rw [adj_apply', ht' j i (Ne.symm hij), map_zero]
  have eX : ∀ i, (d.pX *ᵥ (mt S (d.levi t) *ᵥ y)) i = t.1 i i * (d.pX *ᵥ y) i := by
    intro i
    rw [Matrix.mulVec_mulVec, d.pX_levi t, ← Matrix.mulVec_mulVec, diag_mulVec ht]
  have eY : ∀ i, (d.pY *ᵥ (mt S (d.levi t) *ᵥ y)) i = cA D ((t⁻¹).1 i i) * (d.pY *ᵥ y) i := by
    intro i
    rw [Matrix.mulVec_mulVec, d.pY_levi t, ← Matrix.mulVec_mulVec, diag_mulVec hadj, adj_apply']
  have e0 : d.p0 *ᵥ (mt S (d.levi t) *ᵥ y) = d.p0 *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_levi t]
  rw [hM y, hM (mt S (d.levi t) *ᵥ y), e0]
  simp only [eX, eY, colMul_mul]
  have hX : ∀ i, colMul d.jX i ((d.pX *ᵥ y) i) ∈ latV S L (· = v) ↔
      (fun k => t.1 i i * colMul d.jX i ((d.pX *ᵥ y) i) k) ∈ latV S L (· = v) := fun i =>
    mem_iff_of_unit (hu i).1.2 (hu i).2.2 (inv_mul_diag t ht i) _
  have hY : ∀ i, colMul d.jY i ((d.pY *ᵥ y) i) ∈ latV S L (· = v) ↔
      (fun k => cA D ((t⁻¹).1 i i) * colMul d.jY i ((d.pY *ᵥ y) i) k) ∈ latV S L (· = v) := fun i =>
    mem_iff_of_unit (cA_sub_one (hu i).2.2) (cA_sub_one (hu i).1.2)
      (by rw [← map_mul, mul_comm, inv_mul_diag t ht i, map_one]) _
  exact and_congr (forall_congr' hX) (and_congr (forall_congr' hY) Iff.rfl)

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.flatMap_intertwines_core_heisenbergOperators : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → (∀ w, evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x y = heisO ψ V₀ W₀ w (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x y)) ∧ (∀ w, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) = heisO ψ V₀ W₀ w (flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ)) ∧ ∀ γ, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ (ratW W₀ V₀ γ) = flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ 0 := by
  first | exact @GlobalTheory.FlatHeis.flatAt_heisO | exact GlobalTheory.FlatHeis.flatAt_heisO | (intros; apply GlobalTheory.FlatHeis.flatAt_heisO <;> assumption)
end

section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.goodMajorantLevel_conj_unitaryAdelicMaximalCompact : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → HasIw d (Kmax T b) → ∀ l : Lvl T, l.Good → HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) ∧ ∃ q : stab d, ConjBy (q : GA D T) l.K (Kmax T b) := by
  first | exact @GlobalTheory.RegSch.good_level_conj_stab | exact GlobalTheory.RegSch.good_level_conj_stab | (intros; apply GlobalTheory.RegSch.good_level_conj_stab <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces : ∀ D : D7, GlobalTheory.FinPl.AllBijective D := by
  first | exact @GlobalTheory.FinPl.allBijective_all | exact GlobalTheory.FinPl.allBijective_all | (intros; apply GlobalTheory.FinPl.allBijective_all <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kappa_conjugateHalfPoint_translates_lastColumn : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (L' W₀ : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ'), IsLineVec L' ζ' → ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n), IsSumFrame B.o B.ζ α α₀ → ∀ t : n → k, IsHalf p.e ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wCol p ζ' β t))) ∧ ∀ i j, rd α₀ β ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wCol p ζ' β t))) i j = Sum.elim (fun _ => 0) (fun _ => -t i) j := by
  exact @GlobalTheory.FinPl.LineAct.kappa_wCol_translate
end
