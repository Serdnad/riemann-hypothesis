module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle641
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle006
import GroundTheory.GlobalFields.LocalFieldAtPlace
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.BCWords

namespace PositivityTheory.Rg.Rs

namespace SatakeInductionStabiliserOpen

open SatakeVectors PInfInd2A

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem isOpen_stab_tw {m : ℕ} {V : Submodule ℂ (Sm E m)} (hV : IsDiscrete V) (z : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    ∀ ψ ∈ tw V z, IsOpen {g : GL (Fin m) (w.adicCompletion E) | finRep E m (locGL E m w g) ψ = ψ} := by
  intro ψ hψ
  obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 hψ
  set χ := Model.absC E z
  have hA : IsOpen {g : GL (Fin m) (w.adicCompletion E) | finRep E m (locGL E m w g) φ = φ} :=
    (hV.aut φ hφ).level.preimage (CuspSub.continuous_locGL w)
  have hC := CuspSub.isOpen_ker_locDet (a := m) χ w
  let H : Subgroup (GL (Fin m) (w.adicCompletion E)) :=
    { carrier := {g | finRep E m (locGL E m w g) (mulChi m χ φ) = mulChi m χ φ}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        change finRep E m (locGL E m w (a * b)) _ = _
        rw [map_mul, map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        change finRep E m (locGL E m w a⁻¹) _ = _
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply] }
  have hsub : {g : GL (Fin m) (w.adicCompletion E) | finRep E m (locGL E m w g) φ = φ} ∩
      {g | CuspSub.locDet m χ w g = 1} ⊆ (H : Set _) := fun g hg => by
    change finRep E m (locGL E m w g) (mulChi m χ φ) = mulChi m χ φ
    rw [finRep_mulChi]
    have e1 : χ.loc w (Matrix.GeneralLinearGroup.det g) = 1 := hg.2
    rw [e1, Units.val_one, one_smul, hg.1]
  exact H.isOpen_of_mem_nhds (Filter.mem_of_superset ((hA.inter hC).mem_nhds
    ⟨(by simp : finRep E m (locGL E m w 1) φ = φ), by simp⟩) hsub)

def blkS (B₁ B₂ : Multiset ℂˣ) : Fin 2 → Multiset ℂˣ
  | ⟨0, _⟩ => B₁
  | ⟨1, _⟩ => B₂

end SatakeInductionStabiliserOpen

open SatakeVectors SatakeInductionStabiliserOpen PInfInd2A in
theorem satInd2_holds : SatInd2 := by
  intro E _ _ _ r s V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb
  filter_upwards [eventually_satV hV, eventually_satV hV₁, eventually_satV hV₂] with w hB hB₁ hB₂
  obtain ⟨B, hB⟩ := hB
  obtain ⟨B₁, hB₁⟩ := hB₁
  obtain ⟨B₂, hB₂⟩ := hB₂
  refine ⟨B, B₁, B₂, hB, hB₁, hB₂, ?_⟩
  obtain ⟨f, hfP, hfi, hfe⟩ := hemb
  obtain ⟨φ, hφ, hsat⟩ := hB.1
  have hF0 : f φ ≠ 0 := fun e => hsat.1 (hfi φ hφ e)

  have hsatD : GlobalTheory.LFun.IsSatVecGL w (GlobalTheory.DiscLocEx.locRepD hV.stable w) ⟨φ, hφ⟩ B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := (finRep E (r + s)).comp (locGL E (r + s) w)) V.subtype (fun _ _ => rfl)
      Subtype.val_injective hsat
  have hFB : GlobalTheory.LFun.IsSatVecGL w ((finRep E (r + s)).comp (locGL E (r + s) w)) (f φ) B :=
    hsatD.map (f ∘ₗ V.subtype) (fun g v => hfe (.fin (locGL E (r + s) w g)) v.1 v.2) hF0
  have hFK : ∀ k ∈ GlobalTheory.LFun.KGL w (n := (r + s)), finRep E (r + s) (locGL E (r + s) w k) (f φ) = f φ := fun k hk =>
    GlobalTheory.LGrp.mem_fixed.1 hFB.2.1 k hk
  have h : ∑ i, (![r, s] : Fin 2 → ℕ) i = r + s := GlobalTheory.CompanionTheory.CTFin.CapFactor.two_sum _
  have hcore := isSatVecGL_of_ind (n := ![r, s]) h (blkV (tw V₁ z₁) (tw V₂ z₂))
    (fun i => by fin_cases i
                 · exact fun g ψ hψ => ParabolicProjection.isStable_tw hV₁.stable z₁ (.fin g) ψ hψ
                 · exact fun g ψ hψ => ParabolicProjection.isStable_tw hV₂.stable z₂ (.fin g) ψ hψ)
    (fun i => by fin_cases i
                 · exact isOpen_stab_tw hV₁ z₁ w
                 · exact isOpen_stab_tw hV₂ z₂ w)
    (blkS (B₁.map (· * qU w (-z₁))) (B₂.map (· * qU w (-z₂))))
    (fun i => by fin_cases i
                 · exact satLike_tw (satLike_of_satV hB₁) z₁
                 · exact satLike_tw (satLike_of_satV hB₂) z₂)
    hF0 hFK
    (fun u hu g => by
      obtain ⟨x, rfl⟩ := GlobalTheory.CompanionTheory.CTFin.CapFactor.exists_unip_of_mem ![r, s] h hu
      exact (hfP φ hφ).1 x g)
    (fun k g => by
      have := tensorSp_of_tens2 (n := ![r, s]) (tw V₁ z₁) (tw V₂ z₂) ((hfP φ hφ).2 k g)
      convert this using 2 with m
      have e := GlobalTheory.CompanionTheory.CTFin.CapFactor.lev_eq_leviEmb (![r, s]) h (m 0, m 1)
      rw [levPair_eta] at e
      exact congrArg (fun x => (f φ).1 (x * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) e.symm)
  have hBeq := GlobalTheory.LFun.IsSatVecGL.unique hFB hcore
  have q0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (NumberField.HeightOneSpectrum.one_lt_absNorm w).ne_bot
  rw [hBeq, Fin.sum_univ_two, Multiset.map_add (f := _)]
  congr 1
  · change ((B₁.map (· * qU w (-z₁))).map (· * qU w ((modExp (fun i => Fin (![r, s] i)) 0 : ℂ) / 2))).map
      (fun b : ℂˣ => (b : ℂ)) = _
    rw [GlobalTheory.CompanionTheory.CTFin.CapFactor.modExp_zero, satTw_eq, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, qU_val]
    rw [mul_assoc, ← Complex.cpow_add _ _ q0]
    congr 2
    simp
    ring
  · change ((B₂.map (· * qU w (-z₂))).map (· * qU w ((modExp (fun i => Fin (![r, s] i)) 1 : ℂ) / 2))).map
      (fun b : ℂˣ => (b : ℂ)) = _
    rw [GlobalTheory.CompanionTheory.CTFin.CapFactor.modExp_one, satTw_eq, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, qU_val]
    rw [mul_assoc, ← Complex.cpow_add _ _ q0]
    congr 2
    simp
    ring

end PositivityTheory.Rg.Rs

end
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CapOrth
  GlobalTheory.LevelTypeProj GlobalTheory.PRep GlobalTheory.CuspRep.LocEx PositivityTheory.Rg.Rs.PrAdm

namespace PositivityTheory.Rg.Rs.PrIrr

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem isStable_sInf (S : Set (Submodule ℂ (Sm E N))) (hS : ∀ U ∈ S, _root_.GlobalTheory.CuspRep.IsStable U) : _root_.GlobalTheory.CuspRep.IsStable (sInf S) := by
  intro o φ hφ
  rw [Submodule.mem_sInf] at hφ ⊢
  exact fun U hU => hS U hU o φ (hφ U hU)

variable {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
  (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)

def orthIn (V U : Submodule ℂ (Sm E N)) (hV : V ≤ W) : Submodule ℂ (Sm E N) where
  carrier := {x | x ∈ V ∧ ∀ u ∈ U, inner ℂ (cls h x) (cls h u) = 0}
  add_mem' := fun {x y} hx hy => ⟨V.add_mem hx.1 hy.1, fun u hu => by
    rw [cls_add h (hV hx.1) (hV hy.1), inner_add_left, hx.2 u hu, hy.2 u hu, add_zero]⟩
  zero_mem' := ⟨V.zero_mem, fun u _ => by
    rw [show (0 : Sm E N) = (0 : ℂ) • (0 : Sm E N) by simp, cls_smul h 0 W.zero_mem, zero_smul, inner_zero_left]⟩
  smul_mem' := fun c x hx => ⟨V.smul_mem c hx.1, fun u hu => by
    rw [cls_smul h c (hV hx.1), inner_smul_left, hx.2 u hu, mul_zero]⟩

theorem exists_irr (hW : _root_.GlobalTheory.CuspRep.IsStable W) (hA : ∀ φ ∈ W, IsAutForm φ) (hinj : ∀ x ∈ W, cls h x = 0 → x = 0)
    (hadj : ∀ o : Op E N, ∃ B : Module.End ℂ (Sm E N), (∀ U : Submodule ℂ (Sm E N), _root_.GlobalTheory.CuspRep.IsStable U → ∀ u ∈ U, B u ∈ U) ∧
      ∀ φ ∈ W, ∀ ψ ∈ W, inner ℂ (cls h (act o φ)) (cls h ψ) = inner ℂ (cls h φ) (cls h (B ψ)))
    {ψ : Sm E N} (hψW : ψ ∈ W) (hψ0 : ψ ≠ 0) :
    ∃ V : Submodule ℂ (Sm E N), _root_.GlobalTheory.CuspRep.IsStable V ∧ V ≤ SupSpansPsiPart W ψ ∧ V ≠ ⊥ ∧
      (∀ U ≤ V, _root_.GlobalTheory.CuspRep.IsStable U → U = ⊥ ∨ U = V) ∧ ∃ v ∈ V, inner ℂ (cls h ψ) (cls h v) ≠ 0 := by
  classical
  obtain ⟨L, hLo, hLc, hψT⟩ := exists_type (hA ψ hψW)
  have : FiniteDimensional ℂ (orbSpan ψ) := (hA ψ hψW).kfin
  have hρ := isContRep_sub (orbSpan ψ) (orbSpan_stable ψ)
  set ρ := sub (cptRep E N) (orbSpan ψ) (orbSpan_stable ψ)
  set T := typePart L ρ
  set A := SupSpansPsiPart W ψ
  have hAst : _root_.GlobalTheory.CuspRep.IsStable A := isStable_admissible_span hW ψ
  have hAW : A ≤ W := admissible_span_le W ψ
  have hfd : ∀ V' ≤ A, FiniteDimensional ℂ (V' ⊓ T : Submodule ℂ (Sm E N)) := fun V' h' =>
    haveI := finiteDimensional_admissible_isotypic hA (hA ψ hψW) hLo ρ hρ
    Submodule.finiteDimensional_of_le (inf_le_inf_right T h')
  let Cand : Submodule ℂ (Sm E N) → Prop := fun V' =>
    _root_.GlobalTheory.CuspRep.IsStable V' ∧ V' ≤ A ∧ ∃ v ∈ V' ⊓ T, inner ℂ (cls h ψ) (cls h v) ≠ 0
  have hψψ : inner ℂ (cls h ψ) (cls h ψ) ≠ 0 := fun e => hψ0 (hinj ψ hψW (inner_self_eq_zero.1 e))
  have hex : ∃ n, ∃ V', Cand V' ∧ Module.finrank ℂ (V' ⊓ T : Submodule ℂ (Sm E N)) = n :=
    ⟨_, A, ⟨hAst, le_rfl, ψ, ⟨mem_admissible_span_self hψW, hψT⟩, hψψ⟩, rfl⟩
  obtain ⟨V1, hV1, hV1n⟩ := Nat.find_spec hex
  have hmin : ∀ V', Cand V' → Nat.find hex ≤ Module.finrank ℂ (V' ⊓ T : Submodule ℂ (Sm E N)) :=
    fun V' hV' => Nat.find_min' hex ⟨V', hV', rfl⟩
  let V0 := sInf {U : Submodule ℂ (Sm E N) | _root_.GlobalTheory.CuspRep.IsStable U ∧ V1 ⊓ T ≤ U}
  have hV0st : _root_.GlobalTheory.CuspRep.IsStable V0 := isStable_sInf _ fun U hU => hU.1
  have hV0le : V0 ≤ V1 := sInf_le ⟨hV1.1, inf_le_left⟩
  have hgen : ∀ U, _root_.GlobalTheory.CuspRep.IsStable U → V1 ⊓ T ≤ U → V0 ≤ U := fun U hU hle => sInf_le ⟨hU, hle⟩
  have hTV0 : V1 ⊓ T ≤ V0 := le_sInf fun U hU => hU.2
  have hV0T : V0 ⊓ T = V1 ⊓ T := le_antisymm (inf_le_inf_right T hV0le) (le_inf hTV0 inf_le_right)
  have hV0A : V0 ≤ A := hV0le.trans hV1.2.1
  obtain ⟨v, hvT, hvψ⟩ := hV1.2.2
  have hvT0 : v ∈ V0 ⊓ T := hV0T ▸ hvT
  have key : ∀ U', Cand U' → U' ≤ V0 → V0 ≤ U' := by
    intro U' hU' hle
    have := hfd V1 hV1.2.1
    have := hfd U' hU'.2.1
    have h1 : U' ⊓ T ≤ V1 ⊓ T := hV0T ▸ inf_le_inf_right T hle
    have h2 : Module.finrank ℂ (V1 ⊓ T : Submodule ℂ (Sm E N)) ≤ Module.finrank ℂ (U' ⊓ T : Submodule ℂ (Sm E N)) :=
      hV1n ▸ hmin U' hU'
    have h3 : U' ⊓ T = V1 ⊓ T := Submodule.eq_of_le_of_finrank_le h1 h2
    exact hgen U' hU'.1 (h3 ▸ inf_le_left)
  refine ⟨V0, hV0st, hV0A, fun e => ?_, fun U hU hUst => ?_, v, hvT0.1, hvψ⟩
  · have hv0 : v = 0 := (Submodule.mem_bot ℂ).1 (e ▸ hvT0.1)
    rw [hv0] at hvψ
    exact hvψ (by rw [show (0 : Sm E N) = (0 : ℂ) • (0 : Sm E N) by simp, cls_smul h 0 W.zero_mem, zero_smul,
      inner_zero_right])
  · let C := orthIn h V0 U (hV0A.trans hAW)
    have hCst : _root_.GlobalTheory.CuspRep.IsStable C := fun o x hx => ⟨hV0st o x hx.1, fun u hu => by
      obtain ⟨B, hB, hadjB⟩ := hadj o
      rw [hadjB x (hAW (hV0A hx.1)) u (hAW (hV0A (hU hu)))]
      exact hx.2 _ (hB U hUst u hu)⟩
    have := hfd U (hU.trans hV0A)
    obtain ⟨v1, ⟨hv1U, hv1T⟩, hv1⟩ := exists_orth h hW hA hinj hUst (hU.trans (hV0A.trans hAW))
      (hAW (hV0A hvT0.1)) hLo hLc ρ hρ hvT0.2
    have hv2C : v - v1 ∈ C := ⟨V0.sub_mem hvT0.1 (hU hv1U), hv1⟩
    have hv2T : v - v1 ∈ T := T.sub_mem hvT0.2 hv1T
    have hsplit : inner ℂ (cls h ψ) (cls h v) =
        inner ℂ (cls h ψ) (cls h v1) + inner ℂ (cls h ψ) (cls h (v - v1)) := by
      rw [cls_sub h (hAW (hV0A hvT0.1)) (hAW (hV0A (hU hv1U))), inner_sub_right]
      ring
    by_cases hc : inner ℂ (cls h ψ) (cls h v1) = 0
    · left
      have hC : Cand C := ⟨hCst, fun x hx => hV0A hx.1, v - v1, ⟨hv2C, hv2T⟩, by
        rw [hsplit, hc, zero_add] at hvψ
        exact hvψ⟩
      have hV0C := key C hC fun x hx => hx.1
      rw [eq_bot_iff]
      intro u hu
      exact (Submodule.mem_bot ℂ).2 (hinj u (hAW (hV0A (hU hu))) (inner_self_eq_zero.1 ((hV0C (hU hu)).2 u hu)))
    · right
      exact le_antisymm hU (key U ⟨hUst, hU.trans hV0A, v1, ⟨hv1U, hv1T⟩, hc⟩ hU)

end PositivityTheory.Rg.Rs.PrIrr

end
end
