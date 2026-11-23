module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieAction
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle010
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceE
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceF
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

@[expose] public section

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspStab

namespace PositivityTheory.Rg.Rs.PrAut

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem isAutForm_act (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (o : Op E N) {φ : Sm E N} (h : IsAutForm φ) :
    IsAutForm (act o φ) := by
  cases o with
  | fin k =>
    refine ⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩
    · change φ.1 (ratGL E N γ * g * finGL E N k) = φ.1 (g * finGL E N k)
      rw [mul_assoc, h.left]
    · have e : {k' | finRep E N k' (finRep E N k φ) = finRep E N k φ} =
          (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E N k' φ = φ} := by
        ext k'
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, map_mul]
        constructor
        · intro e
          rw [Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, Module.End.one_apply]
        · intro e
          have := congrArg (finRep E N k) e
          rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E N k), ← map_mul,
            mul_inv_cancel, map_one, Module.End.one_apply] at this
      change IsOpen {k' | finRep E N k' (finRep E N k φ) = finRep E N k φ}
      rw [e]
      exact h.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E N c φ)).map
        (finRep E N k)) (Submodule.span_le.2 ?_)
      rintro _ ⟨c, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
    · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) h.zfin
    · obtain ⟨C, M, h1⟩ := h.growth (g * finGL E N k)
      refine ⟨C, M, fun y => ?_⟩
      change ‖φ.1 (g * infGL E N y * finGL E N k)‖ ≤ _
      rw [mul_assoc, infGL_comm, ← mul_assoc]
      exact h1 y
  | cpt c =>
    refine ⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩
    · change φ.1 (ratGL E N γ * g * infGL E N (Unitary.toUnits c)) = φ.1 (g * infGL E N (Unitary.toUnits c))
      rw [mul_assoc, h.left]
    · exact level_of_le h.level fun k hk => by
        change finRep E N k (cptRep E N c φ) = cptRep E N c φ
        rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E N c φ))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨c', rfl⟩
      refine Submodule.subset_span ⟨c' * c, ?_⟩
      change _ = (cptRep E N c' * cptRep E N c) φ
      rw [← map_mul]
    · exact zfin_of_comm _ (fun z hz => GlobalTheory.ZalgCpt.zalg_comm_cptRep E N c z hz) h.zfin
    · obtain ⟨C, M, h1⟩ := growth_mul (Unitary.toUnits c) (h.growth g)
      refine ⟨C, M, fun y => ?_⟩
      change ‖φ.1 (g * infGL E N y * infGL E N (Unitary.toUnits c))‖ ≤ _
      rw [mul_assoc, ← map_mul]
      exact h1 y
  | lie X =>
    refine ⟨fun γ g => ?_, ?_, GlobalTheory.CuspRep.KFin.kfin_lie E N X φ h.kfin,
      zfin_of_comm _ (fun z hz => GlobalTheory.CuspRep.Zalg_mul_lie E N X z hz) h.zfin,
      GlobalTheory.CuspStab.lie_growth hF E N X φ h⟩
    · change lieD X φ.1 (ratGL E N γ * g) = lieD X φ.1 g
      have e : chart φ.1 (ratGL E N γ * g) = chart φ.1 g := by
        funext x
        unfold chart
        split_ifs
        · rw [mul_assoc, h.left]
        · rfl
      unfold lieD
      rw [e]
    · exact level_of_le h.level fun k hk => by
        change finRep E N k (lie E N X φ) = lie E N X φ
        change (rt E N (finGL E N k) * lie E N X) φ = _
        rw [← lie_rt_fin, Module.End.mul_apply]
        exact congrArg (lie E N X) hk

end PositivityTheory.Rg.Rs.PrAut

end
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs


open SliceClasses in
theorem slice_of : Dict → FinTr → Slice := by
  intro hD hFin E _ _ _ r s hr hs V hV c hc
  obtain ⟨φ₀, hφ₀V, F₀, hCT, F, hFspan, hFne, hFeig⟩ := hc
  have hA₀ := hV.aut φ₀ hφ₀V
  obtain ⟨κ, -, rfl⟩ := ((hD E (r + s)).2.2.2 φ₀ hA₀ r hr (by omega)).2 F₀ hCT
  obtain ⟨cs, hcs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hFspan
  obtain ⟨a, ha⟩ : ∃ a : ℝ → ℂ, a = fun t => cs t * κ := ⟨_, rfl⟩
  have hFval : ∀ g, F g = ∑ t ∈ cs.support, a t * An.ctn r φ₀.1 (aT E (r + s) r t * g) := by
    intro g
    rw [← hcs, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, ha, mul_assoc]
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring V hV.aut r cs.support a
  have hTval : ∀ φ ∈ V, ∀ g, (T φ).1 g = ∑ t ∈ cs.support, a t * An.ctn r φ.1 (aT E (r + s) r t * g) := by
    intro φ hφ g
    rw [hT φ hφ, Aop_apply, ctSm_val r (hV.aut φ hφ)]
  have hequiv : ∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ) := by
    intro o φ hφ
    rw [hT _ (hV.stable o φ hφ), hT φ hφ, ctSm_act r (hV.aut φ hφ) o (hV.aut _ (hV.stable o φ hφ)), Aop_act]
  have hT₀ : (T φ₀).1 = F := funext fun g => (hTval φ₀ hφ₀V g).trans (hFval g).symm

  let W : Submodule ℂ (Sm E (r + s)) :=
    { carrier := {φ | φ ∈ V ∧ ∀ (t : ℝ) g, (T φ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T φ).1 g}
      add_mem' := fun {φ ψ} hφ hψ => ⟨V.add_mem hφ.1 hψ.1, fun t g => by
        simp only [map_add (f := _), Submodule.coe_add, Pi.add_apply, hφ.2 t g, hψ.2 t g, mul_add]⟩
      zero_mem' := ⟨V.zero_mem, fun t g => by simp⟩
      smul_mem' := fun b φ hφ => ⟨V.smul_mem b hφ.1, fun t g => by
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hφ.2 t g]
        ring⟩ }
  have hWst : _root_.GlobalTheory.CuspRep.IsStable W := by
    rintro o φ ⟨hφ, he⟩
    refine ⟨hV.stable o φ hφ, fun t g => ?_⟩
    have e1 : ltS (aT E (r + s) r t) (T φ) = Complex.exp (c * t) • T φ := Subtype.ext (funext fun g => he t g)
    have e2 := congrArg (fun G : Sm E (r + s) => G.1 g) (congrArg (act o) e1)
    simp only [← ltS_act, map_smul] at e2
    rw [hequiv o φ hφ]
    exact e2
  have hWV : W = V := by
    rcases hV.irred W (fun φ hφ => hφ.1) hWst with h | h
    · exfalso
      have h0 : φ₀ ∈ W := ⟨hφ₀V, fun t g => by rw [hT₀]; exact hFeig t g⟩
      rw [h, Submodule.mem_bot] at h0
      apply hFne
      rw [← hT₀, h0, map_zero]
      rfl
    · exact h
  have heig : ∀ φ ∈ V, ∀ (t : ℝ) g, (T φ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T φ).1 g := by
    intro φ hφ
    rw [← hWV] at hφ
    exact hφ.2
  have hsplit : ∀ φ ∈ V, ∀ (t : ℝ) g, (T φ).1 (splitCentre E (r + s) t * g) = (T φ).1 g := by
    intro φ hφ t g
    rw [hTval φ hφ, hTval φ hφ]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    rw [← mul_assoc, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t (aT E (r + s) r u), mul_assoc,
      ctn_splitCentre (hV.sqInt φ hφ).1]
  refine ⟨T, ⟨hequiv, ⟨φ₀, hφ₀V, fun h => hFne ?_⟩, ?_, ?_, ?_⟩⟩
  · rw [← hT₀, h]
    rfl
  · intro φ hφ x g
    rw [hTval φ hφ, hTval φ hφ]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨y, hy⟩ := aT_mul_unip (r + s) r t x
    congr 1
    rw [← mul_assoc, hy, mul_assoc, ctn_unip (hV.aut φ hφ)]
  · intro φ hφ k g m₂
    obtain ⟨ψ, hψA, hψ⟩ := (F_slices V hV T hequiv cs.support a hTval φ hφ k g).1 m₂
    refine ⟨ψ, hψA, hψ, fun t m₁ => ?_, fun r₁ h1 h2 c₁ hc₁ =>
      ⟨φ, hφ, exp_left hD hFin hr hs φ (hV.aut φ hφ) cs.support a (T φ).1 (hTval φ hφ) ψ hψA m₂ _ hψ r₁ h1 h2 c₁ hc₁⟩⟩
    have e : lev (Ad E) r s (splitCentre E r t * m₁, m₂) = aT E (r + s) r t * lev (Ad E) r s (m₁, m₂) := by
      rw [show ((splitCentre E r t * m₁, m₂) : GA E r × GA E s) = (splitCentre E r t, 1) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_left r s r le_rfl]
    rw [hψ, hψ, e, mul_assoc, heig φ hφ]
  · intro φ hφ k g m₁
    obtain ⟨ψ, hψA, hψ⟩ := (F_slices V hV T hequiv cs.support a hTval φ hφ k g).2 m₁
    refine ⟨ψ, hψA, hψ, fun t m₂ => ?_, fun r₂ h1 h2 c₂ hc₂ =>
      ⟨φ, hφ, exp_right hD hFin hr hs φ (hV.aut φ hφ) cs.support a (T φ).1 (hTval φ hφ) c (heig φ hφ) ψ hψA m₁ _ hψ
        r₂ h1 h2 c₂ hc₂⟩⟩
    have e : lev (Ad E) r s (m₁, splitCentre E s t * m₂) =
        splitCentre E (r + s) t * (aT E (r + s) r (-t) * lev (Ad E) r s (m₁, m₂)) := by
      rw [show ((m₁, splitCentre E s t * m₂) : GA E r × GA E s) = (1, splitCentre E s t) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_right r s s le_rfl, splitCentre_eq_aT, mul_assoc]
    rw [hψ, hψ, e, mul_assoc, hsplit φ hφ, mul_assoc, heig φ hφ]
    congr 2
    push_cast
    ring

end PositivityTheory.Rg.Rs

end
end
