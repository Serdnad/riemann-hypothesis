module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle529
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle649
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle554
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle776
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
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

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL

namespace PositivityTheory.Rg.Rs.PrSt

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem splitInv_act (o : Op E N) {φ : Sm E N} (h : ∀ t g, φ.1 (splitCentre E N t * g) = φ.1 g) (t : ℝ)
    (g : GA E N) : (act o φ).1 (splitCentre E N t * g) = (act o φ).1 g := by
  cases o with
  | fin k =>
    change φ.1 (splitCentre E N t * g * finGL E N k) = φ.1 (g * finGL E N k)
    rw [mul_assoc, h]
  | cpt k =>
    change φ.1 (splitCentre E N t * g * infGL E N (Unitary.toUnits k)) = φ.1 (g * infGL E N (Unitary.toUnits k))
    rw [mul_assoc, h]
  | lie X =>
    change lieD X φ.1 (splitCentre E N t * g) = lieD X φ.1 g
    have e : chart φ.1 (splitCentre E N t * g) = chart φ.1 g := by
      funext x
      unfold chart
      split_ifs
      · rw [mul_assoc, h]
      · rfl
    unfold lieD
    rw [e]

theorem isSqInt_act (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (o : Op E N) {φ : Sm E N} (h : IsAutForm φ)
    (h' : IsSqInt φ.1) : IsSqInt (act o φ).1 := by
  let μ : Measure (GA E N) := Measure.haar
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E N μ
  have hA := PrAut.isAutForm_act hF o h
  rw [← memL2_iff_isSqInt (μ := μ) (ContAut.continuous_of_isOpen_stab E N _ hA.level) hA.left
    (splitInv_act o h'.1)]
  have hm : MemL2Quotient (latticeGL E N) μ φ.1 := memL2_of_isAutForm h h'
  cases o with
  | fin k => exact hm.mul_right (finGL E N k)
  | cpt k => exact hm.mul_right (infGL E N (Unitary.toUnits k))
  | lie X =>
    let ν : Measure (Lie E N) := Measure.addHaar
    obtain ⟨α, hα, e⟩ := GlobalTheory.AutGrowth.SelfSmoothing.exists_smoothing_eq_self hF E N ν φ h
    have e' : (act (.lie X) φ).1 = GlobalTheory.CuspQuot.smoothing ν (GlobalTheory.AutGrowth.dens X α) φ.1 := by
      funext g
      change lieD X φ.1 g = _
      conv_lhs => rw [← e]
      exact GlobalTheory.AutGrowth.lieD_smoothing_eq_dens E N ν α hα φ.1 φ.2 X g
    rw [e']
    exact SmoothingSquareIntegrable.memL2_of_smoothing μ ν (GlobalTheory.AutGrowth.isTest_dens X hα)
      (ContAut.continuous_of_isOpen_stab E N φ h.level) hm


variable (E N) in
def ainv : Submodule ℂ (Sm E N) where
  carrier := {φ | ∀ t g, φ.1 (splitCentre E N t * g) = φ.1 g}
  add_mem' := fun {φ ψ} ha hb t g => by
    change φ.1 _ + ψ.1 _ = φ.1 g + ψ.1 g
    rw [ha t g, hb t g]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c φ ha t g => by
    change c * φ.1 _ = c * φ.1 g
    rw [ha t g]

theorem mem_square_integrable_forms {φ : Sm E N} (hφ : φ ∈ A2 E N) : IsAutForm φ ∧ IsSqInt φ.1 := by
  let μ : Measure (GA E N) := Measure.haar
  have hle : A2 E N ≤ GlobalTheory.DiscClosure.autSub E N ⊓ GlobalTheory.DiscClosure.squareIntegrableSmoothSubmoduleGL μ ⊓ ainv E N :=
    Submodule.span_le.2 fun ψ hψ => ⟨⟨hψ.1, memL2_of_isAutForm hψ.1 hψ.2⟩, hψ.2.1⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hle hφ
  exact ⟨h1, (memL2_iff_isSqInt (ContAut.continuous_of_isOpen_stab E N φ h1.level) h1.left h3).1 h2⟩

theorem isStable_square_integrable_forms (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) : _root_.GlobalTheory.CuspRep.IsStable (A2 E N) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem ψ hψ => exact Submodule.subset_span ⟨PrAut.isAutForm_act hF o hψ.1, isSqInt_act hF o hψ.1 hψ.2⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

section Adj

open GlobalTheory.CapOrth

variable {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
  (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)

theorem inner_rt {g : GA E N} (hg : ∀ φ ∈ W, rt E N g φ ∈ W) (hg' : ∀ φ ∈ W, rt E N g⁻¹ φ ∈ W) {φ ψ : Sm E N}
    (hφ : φ ∈ W) (hψ : ψ ∈ W) :
    inner ℂ (cls h (rt E N g φ)) (cls h ψ) = inner ℂ (cls h φ) (cls h (rt E N g⁻¹ ψ)) := by
  have hrr : rt E N g (rt E N g⁻¹ ψ) = ψ := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  have e : toL2ₗ μ W h ⟨ψ, hψ⟩ = R (latticeGL E N) μ g (toL2ₗ μ W h ⟨rt E N g⁻¹ ψ, hg' ψ hψ⟩) := by
    rw [R_toL2ₗ h ⟨_, hg' ψ hψ⟩ (by rw [hrr]; exact hψ)]
    exact congrArg _ (Subtype.ext hrr.symm)
  rw [cls_mk h (hg φ hφ), cls_mk h hψ, cls_mk h hφ, cls_mk h (hg' ψ hψ), ← R_toL2ₗ h ⟨φ, hφ⟩ (hg φ hφ), e]
  let Ui : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ := ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  exact Ui.inner_map_map _ _

theorem exists_adj (hW : _root_.GlobalTheory.CuspRep.IsStable W) (hA : ∀ φ ∈ W, IsAutForm φ) (o : Op E N) :
    ∃ B : Module.End ℂ (Sm E N), (∀ U : Submodule ℂ (Sm E N), _root_.GlobalTheory.CuspRep.IsStable U → ∀ u ∈ U, B u ∈ U) ∧
      ∀ φ ∈ W, ∀ ψ ∈ W, inner ℂ (cls h (act o φ)) (cls h ψ) = inner ℂ (cls h φ) (cls h (B ψ)) := by
  cases o with
  | fin k =>
    refine ⟨act (.fin k⁻¹), fun U hU u hu => hU _ u hu, fun φ hφ ψ hψ => ?_⟩
    have e : (finGL E N k)⁻¹ = finGL E N k⁻¹ := (map_inv _ k).symm
    have := inner_rt h (g := finGL E N k) (fun x hx => hW (.fin k) x hx)
      (fun x hx => by rw [e]; exact hW (.fin k⁻¹) x hx) hφ hψ
    rw [e] at this
    exact this
  | cpt k =>
    refine ⟨act (.cpt k⁻¹), fun U hU u hu => hU _ u hu, fun φ hφ ψ hψ => ?_⟩
    have e : (infGL E N (Unitary.toUnits k))⁻¹ = infGL E N (Unitary.toUnits k⁻¹) := by
      rw [map_inv, map_inv]
    have := inner_rt h (g := infGL E N (Unitary.toUnits k)) (fun x hx => hW (.cpt k) x hx)
      (fun x hx => by rw [e]; exact hW (.cpt k⁻¹) x hx) hφ hψ
    rw [e] at this
    exact this
  | lie X =>
    refine ⟨-act (.lie X), fun U hU u hu => U.neg_mem (hU _ u hu), fun φ hφ ψ hψ => ?_⟩
    have e := GlobalTheory.LieSkew.lie_skew E N μ W h hW hA X ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    rw [LinearMap.neg_apply, show -(act (.lie X) ψ) = (-1 : ℂ) • act (.lie X) ψ by simp,
      cls_smul h (-1 : ℂ) (hW (.lie X) ψ hψ), inner_smul_right, cls_mk h (hW (.lie X) φ hφ), cls_mk h hψ,
      cls_mk h hφ, cls_mk h (hW (.lie X) ψ hψ), neg_one_mul]
    exact e

end Adj

end PositivityTheory.Rg.Rs.PrSt

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.SpehInfChar

namespace PositivityTheory.Rg.Rs

namespace InfinitesimalCharacterAscent

theorem spehExp_rev (d : ℕ) (i : Fin d) : spehExp d i.rev = -spehExp d i := by
  have h := i.2
  simp only [spehExp, Fin.val_rev]
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem prod_neg (d : ℕ) (g : ℂ → ℂ) :
    ∏ i : Fin d, g (-(spehExp d i : ℂ)) = ∏ i : Fin d, g (spehExp d i : ℂ) := by
  refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, spehExp_rev]
  push_cast
  ring_nf

end InfinitesimalCharacterAscent

open InfinitesimalCharacterAscent in
theorem infAsc_holds : InfAsc := by
  intro E _ _ _ N a d V π hV hemb τ m hm
  obtain ⟨hs, ν, hν, f, hfm, hfi, hfe⟩ := hemb
  have hm0 : π.HasInfChar τ ((CG.mk π).infChar τ) :=
    hasInfChar_infChar_of_commute E a (fun τ u o => cap_commute_act τ u o) (CG.mk π) τ
  set m₀ := (CG.mk π).infChar τ with hm₀
  refine ⟨m₀, hm0, GlobalTheory.BcSpehProof.hasInfCharGL_unique hV.ne_bot hm ⟨?_, fun u φ hφ => ?_⟩⟩
  · rw [← hs, Multiset.card_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Multiset.card_map, hm₀, CG.card_infChar]
  have hI : ∀ X, ∀ φ ∈ indForms hs (fun i => π.twist (ν i)), lie E N X φ ∈ indForms hs (fun i => π.twist (ν i)) :=
    fun X φ hφ => lie_mem_indForms _ hs _ X φ hφ
  have hIV : ∀ X, ∀ φ ∈ V, lie E N X φ ∈ V := fun X φ hφ => hV.stable (.lie X) φ hφ
  have hexpo : ∀ i : Fin d, expo (ν i) τ = ((-spehExp d i + a * spehExp d i : ℝ) : ℂ) := fun i =>
    (GlobalTheory.CuspRep.InfType.expo_of_infType E (ν i)).2.1 _ (hν i) τ
  have hmod : ∀ i : Fin d, ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 = ((a * spehExp d i : ℝ) : ℂ) := fun i => by
    rw [mul_spehExp]
    push_cast
    rfl
  have hc := cap_indForms (fun _ : Fin d => a) hs (fun i => π.twist (ν i)) τ (fun i => m₀.map (· + expo (ν i) τ))
    (fun i => hm0.twist (ν i)) u (f φ) (hfm φ hφ)
  have e1 : f (cap τ u φ) = cap τ u (f φ) := cap_comm_quot hIV f hfe τ u φ hφ
  set Q := ((∑ i : Fin d, m₀.map (· + (spehExp d i : ℂ))).map (u + ·)).prod with hQ
  have hQ' : (∏ i : Fin d, ((m₀.map (· + expo (ν i) τ)).map fun x =>
      u + x - (modExp (fun _ : Fin d => Fin a) i : ℂ) / 2).prod) = Q := by
    rw [hQ, prod_map_finset_sum]
    have e : ∀ i : Fin d, ((m₀.map (· + expo (ν i) τ)).map fun x =>
        u + x - (modExp (fun _ : Fin d => Fin a) i : ℂ) / 2).prod =
        (m₀.map fun x => u + x + -(spehExp d i : ℂ)).prod := fun i => by
      rw [Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply]
      rw [hexpo i, hmod i]
      push_cast
      ring
    rw [Finset.prod_congr rfl fun i _ => e i, prod_neg d (fun t => (m₀.map fun x => u + x + t).prod)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp_apply]
    ring
  have hmem : cap τ u φ - Q • φ ∈ V := by
    rw [hm.2 u φ hφ]
    exact V.sub_mem (V.smul_mem _ hφ) (V.smul_mem _ hφ)
  have h0 : f (cap τ u φ - Q • φ) = 0 := by
    rw [map_sub, e1, hc, map_smul, hQ']
    exact sub_self _
  exact sub_eq_zero.1 (hfi _ hmem h0)

end PositivityTheory.Rg.Rs

end
end
