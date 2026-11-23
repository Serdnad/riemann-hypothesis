module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle133
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle141
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle145
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle149
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitIdemDict

open GlobalTheory.AdelicU

variable {D : D7} {v : FinPl D}

theorem exists_eq_splitProj (φ : SplitProj D v) :
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, φ = splitProj τ := by
  refine ⟨(φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight, ?_⟩
  refine AlgHom.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>

    have hax : a ⊗ₜ[D.host.F] x = a • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [splitProj_tmul, hax, map_smul, smul_eq_mul]
    rfl
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]

theorem isProjAt_iff (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (PP : Formalism.L2.DIV.Pl D.host.E) :
    IsProjAt (D := D) (v := v) (splitProj τ) PP ↔ PP = splitPrime τ := by

  have hred : ∀ x : 𝓞 D.host.E, rdQ (D := D) (v := v) (splitProj τ) (x : D.host.E) = τ x := fun x => by
    simp only [rdQ, splitProj_tmul, one_mul]
  unfold IsProjAt
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [h x, hred, mem_splitPrime]
  · rintro rfl x
    rw [hred, mem_splitPrime]

theorem sigR_compFin {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    sigR _ σ (compFin F E v z) = compFin F E v (sigR _ σ z) := by

  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => simp [sigR, compFin]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem compFin_cA (z : AE D) :
    sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) = compFin D.host.F D.host.E v (cA D z) := by

  have h := sigR_compFin D.sp.cm.sig v z
  exact h

private theorem idem_inl_eq_tensAt_one (D : D7) (v : FinPl D) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) = GlobalTheory.EmbChart.tensAt D.host.E v 1 := by
  rw [Algebra.TensorProduct.one_def, GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem eq_idem {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} {e : AE D} (he : IsIdemOf (D := D) (v := v) (splitProj τ) e) :
    e = GlobalTheory.EmbChart.idem τ := by
  obtain ⟨⟨hee, hce, -⟩, hsum, hone⟩ := he
  have hone' : splitProj τ (compFin D.host.F D.host.E v e) = 1 := hone
  have hε := idem_inl_eq_tensAt_one D v

  have h1 : e = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v e) := by
    calc e = GlobalTheory.EmbChart.tensAt D.host.E v 1 * e := by
          rw [← hε, ← hsum, add_mul, hee, mul_comm (cA D e) e, hce, add_zero]
      _ = _ := by rw [GlobalTheory.EmbChart.tensAt_mul_right, one_mul]
  have hc : cA D e = GlobalTheory.EmbChart.tensAt D.host.E v 1 - e := by
    rw [← hε, ← hsum, add_sub_cancel_left]

  have h2 : compFin D.host.F D.host.E v e = splitIdem (isCMExt_host D) τ := by
    apply split_ext (isCMExt_host D) τ
    · rw [splitProj_splitIdem, hone']
    · rw [splitProj_comp_splitIdem, splitProj_comp, compFin_cA, hc, map_sub, GlobalTheory.EmbChart.compFin_tensAt,
        map_sub, map_one, hone', sub_self]
  rw [h1, h2]
  rfl

private theorem eq_of_isIdemAt_of_isIdemAt' {e : AE D} {P Q : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : Formalism.L2.NTheta.IsIdemAt e P) (hQ : Formalism.L2.NTheta.IsIdemAt e Q) : P = Q := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => Q.asIdeal.zero_mem, fun _ => P.asIdeal.zero_mem⟩
  · exact (hP.2 x hx).trans (hQ.2 x hx).symm

theorem exists_emb {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP) :
    ∃ (v : FinPl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), IsIdemOf (D := D) (v := v) (splitProj τ) e ∧ PP = splitPrime τ := by
  obtain ⟨⟨hee, hce, w, ε, ⟨α, rfl, hαw, hαo⟩, hsum⟩, -⟩ := id he

  have hα : α = singleV D.host.F w 1 := by
    classical
    apply RestrictedProduct.ext
    intro u
    by_cases hu : u = w
    · subst hu
      rw [singleV, RestrictedProduct.single_eq_same]
      exact hαw
    · rw [singleV, RestrictedProduct.single_eq_of_ne _ _ hu]
      exact hαo u hu
  subst hα
  have hsum' : e + cA D e = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl w) := hsum
  have hε := idem_inl_eq_tensAt_one D w

  set y := compFin D.host.F D.host.E w e with hy
  have hy1 : y * y = y := by rw [hy, ← map_mul, hee]
  have hy2 : y + sigR _ D.sp.cm.sig y = 1 := by
    rw [hy, compFin_cA, ← map_add (f := _), hsum', hε, GlobalTheory.EmbChart.compFin_tensAt]
  have hσy : sigR _ D.sp.cm.sig y = 1 - y := eq_sub_of_add_eq' hy2

  have hnf : ¬ IsField (Fv D.host.F w ⊗[D.host.F] D.host.E) := by
    intro hf
    by_cases hy0 : y = 0
    · rw [hy0, map_zero, add_zero] at hy2
      exact hf.exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
        hab (by rw [← mul_one a, ← mul_one b, ← hy2, mul_zero, mul_zero])
    · obtain ⟨z, hz⟩ := hf.mul_inv_cancel hy0
      have hy1' : y = 1 := by
        calc y = y * (y * z) := by rw [hz, mul_one]
          _ = y * y * z := by rw [mul_assoc]
          _ = 1 := by rw [hy1, hz]
      rw [hy1', map_one] at hy2
      have h10 : (1 : Fv D.host.F w ⊗[D.host.F] D.host.E) = 0 := add_left_cancel (hy2.trans (add_zero 1).symm)
      exact hf.exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
        hab (by rw [← mul_one a, ← mul_one b, h10, mul_zero, mul_zero])
  have hfin : Module.finrank (Fv D.host.F w) (Fv D.host.F w ⊗[D.host.F] D.host.E) = 2 := by
    rw [Module.finrank_baseChange]
    exact (isCMExt_host D).2.2.1
  obtain ⟨φ₀⟩ := nonempty_algHom_of_not_isField hfin hnf
  obtain ⟨τ₀, rfl⟩ := exists_eq_splitProj (D := D) (v := w) φ₀

  have hτ : ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F w, splitProj τ y = 1 := by
    have hp : IsIdempotentElem (splitProj τ₀ y) := by
      unfold IsIdempotentElem
      rw [← map_mul, hy1]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hp with h0 | h1
    · refine ⟨τ₀.comp D.sp.cm.sig, ?_⟩
      rw [splitProj_comp, hσy, map_sub, map_one, h0, sub_zero]
    · exact ⟨τ₀, h1⟩
  obtain ⟨τ, hτ⟩ := hτ
  have hi : IsIdemOf (D := D) (v := w) (splitProj τ) e := ⟨he.1, hsum', hτ⟩
  refine ⟨w, τ, hi, ?_⟩

  have he' := he
  rw [eq_idem hi] at he'
  exact eq_of_isIdemAt_of_isIdemAt' he' (GlobalTheory.EmbChart.isIdemAt_idem τ)

theorem idem_dictionary : ∀ (D : D7), (∀ (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (v : FinPl D) (φ : SplitProj D v), IsIdemOf φ e ∧ IsProjAt φ PP) ∧ ∀ (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal ∧ (∀ PP', IsProjAt φ PP' → PP' = PP) ∧ ∀ e, IsIdemOf φ e → Formalism.L2.NTheta.IsIdemAt e PP ∧ (∀ e', Formalism.L2.NTheta.IsIdemAt e' PP → e' = e) ∧ ∀ φ' : SplitProj D v, IsIdemOf φ' e → φ' = φ := by
  intro D
  refine ⟨fun e PP he => ?_, fun v φ PP hφ => ?_⟩
  · obtain ⟨w, τ, hi, rfl⟩ := exists_emb he
    exact ⟨w, splitProj τ, hi, (isProjAt_iff τ _).2 rfl⟩
  · obtain ⟨τ, rfl⟩ := exists_eq_splitProj φ
    obtain rfl : PP = splitPrime τ := (isProjAt_iff τ PP).1 hφ
    refine ⟨(splitPrime_liesOver τ).over.symm, fun PP' h' => (isProjAt_iff τ PP').1 h', fun e he => ?_⟩
    obtain rfl := eq_idem he
    refine ⟨GlobalTheory.EmbChart.isIdemAt_idem τ, fun e' he' => ?_, fun φ' hφ' => ?_⟩
    ·
      obtain ⟨w, τ', hi', hP'⟩ := exists_emb he'
      have hw : w = v := by
        calc w = (splitPrime τ').under (𝓞 D.host.F) := (splitPrime_under τ').symm
          _ = (splitPrime τ).under (𝓞 D.host.F) := by rw [hP']
          _ = v := splitPrime_under τ
      subst hw
      rw [eq_idem hi', splitPrime_injective (isCMExt_host D) hP'.symm]
    ·
      obtain ⟨τ'', rfl⟩ := exists_eq_splitProj φ'
      have h2 := GlobalTheory.EmbChart.isIdemAt_idem τ''
      rw [← eq_idem hφ'] at h2
      rw [splitPrime_injective (isCMExt_host D) (eq_of_isIdemAt_of_isIdemAt' h2 (GlobalTheory.EmbChart.isIdemAt_idem τ))]

end GlobalTheory.SplitIdemDict

end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.twistedPlace_doubleCoset_volume_and_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)]
    (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 →
  ∀ [MeasurableSpace (GL (Fin (l * t)) k)] [BorelSpace (GL (Fin (l * t)) k)] (μK : Measure (GL (Fin (l * t)) k))
    [μK.IsHaarMeasure], μK (KO k (Fin (l * t))) = 1 →
  (∀ e : Fin (l * t) → ℤ, m.real (dcell ϖ (e ∘ (blkEquiv l t).symm)) =
    (resCard k : ℝ) ^ ((r : ℤ) * sumAbs e) * μK.real (cell k (Fin (l * t)) ϖ e)) ∧
  Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
    (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  first | exact @GlobalTheory.ChainCells.vol_dcell_and_disjoint | exact GlobalTheory.ChainCells.vol_dcell_and_disjoint | (intros; apply GlobalTheory.ChainCells.vol_dcell_and_disjoint <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

variable {D : D7} {S T : HSp D}

theorem cA_incA_inv_natCast (m : ℕ) : cA D (incA D ((m : D.host.E)⁻¹)) = incA D ((m : D.host.E)⁻¹) := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, star_natCast]

theorem symplO_inv_smul_nsmul {m : ℕ} (hm : 0 < m) (y l : WO S T) :
    symplO S T (incA D ((m : D.host.E)⁻¹) • y) (m • l) = symplO S T y l := by
  rw [GlobalTheory.PlaceModel.symplO_smul, cA_incA_inv_natCast, GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]

theorem symplO_inv_smul_swap (m : ℕ) (x u : WO S T) :
    symplO S T (incA D ((m : D.host.E)⁻¹) • x) u = -symplO S T (incA D ((m : D.host.E)⁻¹) • u) x := by
  rw [GlobalTheory.PlaceModel.symplO_skew S T x (incA D ((m : D.host.E)⁻¹) • u), neg_neg, GlobalTheory.PlaceModel.symplO_smul,
    cA_incA_inv_natCast]

theorem map_infPart_smul (a : AE D) {r : WO S T} (hr : r.map (infPart D) = 0) : (a • r).map (infPart D) = 0 := by
  ext i j
  have hij := congrFun (congrFun hr i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at hij ⊢
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, hij, mul_zero]

theorem nsmul_inv_smul {m : ℕ} (hm : 0 < m) (x : WO S T) : m • (incA D ((m : D.host.E)⁻¹) • x) = x := by
  rw [smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]

theorem psi_shift {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {m : ℕ} (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) {r : WO S T} (hr : r ∈ Λ) {x : WO S T} (hx : x ∈ mLat m Λ) :
    ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • x) r) = 1 := by
  obtain ⟨l, hl, rfl⟩ := mem_mLat.1 hx
  rw [GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]
  exact hΛ l hl r hr

def qCharM (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) : AddChar (Qm m Λ) ℂ where
  toFun u := ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) r)
  map_zero_eq_one' := psi_shift hm hΛ hr repm_zero_mem
  map_add_eq_mul' a b := by
    have h := psi_shift hm hΛ hr (repm_add_sub a b)
    have e : repm (a + b) = (repm (a + b) - (repm a + repm b)) + repm a + repm b := by abel
    rw [e, smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h, one_mul]

theorem qCharM_apply (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) (u : Qm m Λ) :
    qCharM ψ Λ m hm hΛ r hr u = ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) r) := rfl

theorem qCharM_mk (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) {u : WO S T} (hu : u ∈ Λ) :
    qCharM ψ Λ m hm hΛ r hr (QuotientAddGroup.mk (⟨u, hu⟩ : Λ)) = ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • u) r) := by
  rw [qCharM_apply]
  have h := psi_shift hm hΛ hr (repm_mk_sub (m := m) hu)
  have e : repm (QuotientAddGroup.mk (⟨u, hu⟩ : Λ) : Qm m Λ) =
      (repm (QuotientAddGroup.mk (⟨u, hu⟩ : Λ) : Qm m Λ) - u) + u := by abel
  rw [e, smul_add, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, h, one_mul]

theorem qCharM_eq_zero_iff {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {m : ℕ} (hm : 0 < m)
    (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1)
    (hmax : ∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ)
    {r : WO S T} (hr : r ∈ Λ) : qCharM ψ Λ m hm hΛ r hr = 0 ↔ r ∈ mLat m Λ := by
  constructor
  · intro h0
    have hx : incA D ((m : D.host.E)⁻¹) • r ∈ Λ := by
      refine hmax _ (map_infPart_smul _ (hinf r hr)) fun u hu => ?_
      have h1 := qCharM_mk ψ Λ m hm hΛ r hr hu
      rw [h0, AddChar.zero_apply] at h1
      rw [symplO_inv_smul_swap, AddChar.map_neg_eq_inv, ← h1, inv_one]
    exact mem_mLat.2 ⟨_, hx, nsmul_inv_smul hm r⟩
  · intro hrm
    obtain ⟨l, hl, rfl⟩ := mem_mLat.1 hrm
    refine DFunLike.ext _ _ (fun u => ?_)
    rw [qCharM_apply, AddChar.zero_apply, symplO_inv_smul_nsmul hm]
    exact hΛ _ (repm_mem u) _ hl

theorem charSum_selfAnn : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (m : ℕ), 0 < m →
    (∀ u ∈ Λ, u.map (infPart D) = 0) → (∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) →
    (∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ) →
    ∀ [Fintype (Qm m Λ)] [DecidableEq (Qm m Λ)] (q : Qm m Λ),
      ∑ u : Qm m Λ, ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) (repm q)) =
        if q = 0 then (Fintype.card (Qm m Λ) : ℂ) else 0 := by
  intro D ψ S T Λ m hm hinf hΛ hmax _ _ q
  have key : qCharM ψ Λ m hm hΛ (repm q) (repm_mem q) = 0 ↔ q = 0 := by
    rw [qCharM_eq_zero_iff hm hinf hΛ hmax (repm_mem q)]
    conv_rhs => rw [← mk_repm q]
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  classical
  have hs := AddChar.sum_eq_ite (qCharM ψ Λ m hm hΛ (repm q) (repm_mem q))
  simp only [qCharM_apply, key] at hs
  convert hs
end GlobalTheory.FinDecomp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm

theorem enorm_term_le_iSup : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ ≤ ⨆ w, ‖G w‖ₑ := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 hμ G y
  have hψ1 : ∀ x, ‖(ψ x : ℂ)‖ₑ = 1 := fun x => by
    rw [← ofReal_norm_eq_enorm, hψ.1.2.1 x, ENNReal.ofReal_one]
  calc ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ
      ≤ ∫⁻ z in 𝓨, ‖heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G
          (isoPart V W C z + midPart V V' W B 0)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ _ in 𝓨, (⨆ w, ‖G w‖ₑ) ∂μ := by
        refine lintegral_mono fun z => ?_
        simp only [heisO, enorm_mul, hψ1, one_mul]
        exact le_iSup (fun w => ‖G w‖ₑ) _
    _ = ⨆ w, ‖G w‖ₑ := by rw [setLIntegral_const, hμ.2.2, mul_one]

end GlobalTheory.MixedTerm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatPairSep

variable {D : D7}

theorem eq_zero_of_trace_integralBasis (D : D7) (q : D.host.E)
    (h : ∀ k, Algebra.trace ℚ D.host.E (q * integralBasis D.host.E k) = 0) : q = 0 := by
  refine (traceForm_nondegenerate ℚ D.host.E).1 q fun z => ?_
  have hl : (Algebra.traceForm ℚ D.host.E) q = 0 :=
    (integralBasis D.host.E).ext fun k => by
      rw [LinearMap.zero_apply, Algebra.traceForm_apply]; exact h k
  rw [hl, LinearMap.zero_apply]

theorem pairQ_sub (W : HSp D) {r : ℕ} (y y' : Matrix (Fin W.rank) (Fin r) D.host.E) :
    pairQ W y - pairQ W y' = pairQ W (y - y') := by
  have : adj D (y - y') = adj D y - adj D y' := by
    ext i j; simp [adj, Formalism.UG.cT]
  simp only [pairQ, this, Matrix.sub_mul, smul_sub]

theorem eq_of_pairQ_eq (W : HSp D) {r : ℕ} (y y' : Matrix (Fin W.rank) (Fin r) D.host.E)
    (h : pairQ W y = pairQ W y') : y = y' := by
  have h1 : adj D y * W.gram = adj D y' * W.gram := by
    have := congrArg (fun M => (D.host.xi0)⁻¹ • M) h
    simpa [pairQ, smul_smul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)] using this
  have h2 : adj D y = adj D y' := by
    have := congrArg (fun M => M * W.gram⁻¹) h1
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit W)] using this
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun h2 j) i
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
  exact (D.sp.cm.sig : D.host.E →+* D.host.E).injective this

theorem exists_sep (D : D7) (W : HSp D) (r : ℕ) :
    ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E), (∀ j a b, IsIntegral ℤ (X j a b)) ∧
      ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := by
  let ι := Fin W.rank × Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)
  let e := Fintype.equivFin ι
  let Y : ι → Matrix (Fin W.rank) (Fin r) D.host.E := fun t => Matrix.single t.1 t.2.1 (integralBasis D.host.E t.2.2)
  refine ⟨Fintype.card ι, fun j => Y (e.symm j), ?_, ?_⟩
  · intro j a b
    simp only [Y, Matrix.single_apply]
    split_ifs
    · rw [integralBasis_apply]; exact (RingOfIntegers.basis D.host.E _).isIntegral_coe
    · exact isIntegral_zero
  · intro y y' h
    apply eq_of_pairQ_eq W y y'
    rw [← sub_eq_zero, pairQ_sub]
    refine Matrix.ext fun l i => ?_
    rw [Matrix.zero_apply]
    refine eq_zero_of_trace_integralBasis D _ fun k => ?_
    have hj := h (e (i, l, k))
    simp only [ratPair, Equiv.symm_apply_apply, Y, Rat.cast_inj] at hj
    rw [← sub_eq_zero, ← map_sub, ← Matrix.trace_sub, ← Matrix.sub_mul, pairQ_sub,
      Matrix.trace_mul_single] at hj
    simpa [MulOpposite.smul_eq_mul_unop] using hj

end GlobalTheory.RatPairSep

theorem GlobalTheory.RatPairSep.main : ∀ (D : D7) (W : HSp D) (r : ℕ), ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E),
    (∀ j a b, IsIntegral ℤ (X j a b)) ∧ ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E,
    (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := GlobalTheory.RatPairSep.exists_sep
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec

theorem omegaQ_one_eq_prod_qLoc : ∀ (D : D7) (a b r : ℕ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)),
      omegaQ Q r ξ 1 y = ∏ PP ∈ Q, qLoc r PP (ξ PP) (y PP) := by
  intro D a b r Q ξ y
  unfold omegaQ
  by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · rw [dite_eq_left h, ← Finset.prod_attach Q (fun PP => qLoc r PP (ξ PP) (y PP))]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [zpow_one, qLoc, dite_eq_left (h PP.1 PP.2)]
  · rw [dite_eq_right h]
    push_neg at h
    obtain ⟨PP, hPP, hn⟩ := h
    refine (Finset.prod_eq_zero hPP ?_).symm
    rw [qLoc, dite_eq_right]
    rintro ⟨h1, h2⟩
    exact hn h1 h2

end GlobalTheory.StepVec
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.halfAdelicHom_decompose_isotropic_middle_complement : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ (a : AE D) (u : WO V W), IsHalf a u → ∃ (y : Mx D W.rank r) (x : WO V' W) (t : Mx D W.rank r), IsHalf a y ∧ IsHalf a x ∧ IsHalf a t ∧ u = isoPart V W C y + midPart V V' W B x + restEmb V W K t := by
  first | exact @GlobalTheory.HalfDecomp.half_decomp | exact GlobalTheory.HalfDecomp.half_decomp | (intros; apply GlobalTheory.HalfDecomp.half_decomp <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistPlaceDatum_parabolic_move : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (n : ℤ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Q, G PP ∈ blockTri (blk2 r) ∧ H PP ∈ blockTri (blk2 r)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaQ Q r ξ n (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Q, (ξ PP (Matrix.GeneralLinearGroup.det (G PP)) * (ξ PP (dBlk (blk2 r) 1 (G PP)))⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (H PP)))⁻¹ * ξ PP (dBlk (blk2 r) 1 (H PP)))) ^ n : ℂˣ) : ℂ) * omegaQ Q r ξ n y := by
  first | exact @GlobalTheory.ParabolicDatum.omegaQ_parabolic | exact GlobalTheory.ParabolicDatum.omegaQ_parabolic | (intros; apply GlobalTheory.ParabolicDatum.omegaQ_parabolic <;> assumption)
end
