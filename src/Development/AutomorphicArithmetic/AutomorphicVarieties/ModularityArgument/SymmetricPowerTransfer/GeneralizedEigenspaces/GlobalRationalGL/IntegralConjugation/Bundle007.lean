module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.BridgeEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle093
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle003
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem finite_part_split_infinite {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (f x : UA L n)
    (hf : f ∈ finU (E := L) (n := n)) (hw : ∀ w : Plc L, mL w f = mL w x) :
    f⁻¹ * x ∈ infU L n ∧ x = f * (f⁻¹ * x) ∧ ∀ τ, cEmb τ (f⁻¹ * x) = cEmb τ x := by
  obtain ⟨-, -, -, -, -, h6, -, -⟩ := uaFacts L n
  refine ⟨((h6 _).2).2 fun w => ?_, by group, fun τ => ?_⟩
  · have : cLoc w f = cLoc w x := Units.ext (hw w)
    rw [map_mul, map_inv, this, inv_mul_cancel]
  · rw [map_mul, map_inv, ((h6 f).1).1 hf τ, inv_one, one_mul]

theorem UpperTheory.V.Z.Sym.Dict.Br.okFin :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), (∀ (γ : U3 B.Δ) (g : GA B.Δ), (∀ v, (g.1 v : Matrix (Fin 3) (Fin 3) _) = (γ : Matrix (Fin 3) (Fin 3) _).map (lmap (cv v) B.Δ)) → ∃ k ∈ infU L 3, (B.rG γ : UA L 3) = B.bG g * k ∧ ∀ τ, cEmb τ k = cEmb τ (B.rG γ : UA L 3)) ∧ ∀ (γ : SU B.Δ) (g : SA B.Δ), (∀ v, mt ((g : DA B.Δ).1 v) = (mt (γ : DX B.Δ)).map (lmap (cv v) B.Δ)) → ∃ k ∈ infU L 2 ⊓ SUA L, (B.rS γ : UA L 2) = B.bS g * k ∧ ∀ τ, cEmb τ k = cEmb τ (B.rS γ : UA L 2) := by
  intro L _ _ _ B
  refine ⟨fun γ g h => ?_, fun γ g h => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := finite_part_split_infinite (B.bG g : UA L 3) (B.rG γ : UA L 3) (B.bG g).2 fun w => by
      rw [B.bG_loc, B.rG_loc, h (un w), Matrix.map_map]
      exact Matrix.ext fun i j => B.ρ_glob (un w) w rfl _
    exact ⟨_, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := finite_part_split_infinite (B.bS g : UA L 2) (B.rS γ : UA L 2) (B.bS g).2.1 fun w => by
      rw [B.bS_loc, B.rS_loc, h (un w), Matrix.map_map]
      exact Matrix.ext fun i j => B.ρ_glob (un w) w rfl _
    exact ⟨_, ⟨h1, (SUA L).mul_mem ((SUA L).inv_mem (B.bS g).2.2) (B.rS γ).2.2⟩, h2, h3⟩
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem continuous_of_val_iff {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] (i : k ≃+* k')
    (h : ∀ a b, valuation k' (i a) ≤ valuation k' (i b) ↔ valuation k a ≤ valuation k b) :
    Continuous i := by
  refine continuous_of_continuousAt_zero (i : k →+* k').toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  change Filter.Tendsto i (nhds 0) (nhds 0)
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k').tendsto_right_iff]
  intro r hr
  obtain ⟨c, rfl⟩ := valuation_surjective r
  have hc : valuation k (i.symm c) ≠ 0 := by
    intro h0
    have h2 := (h (i.symm c) 0).2 (by simp [h0])
    simp only [RingEquiv.apply_symm_apply, map_zero, le_zero_iff] at h2
    exact hr h2
  have hm : {x : k | valuation k x < valuation k (i.symm c)} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨_, hc, subset_rfl⟩
  filter_upwards [hm] with a ha
  have h3 := h (i.symm c) a
  rw [RingEquiv.apply_symm_apply] at h3
  exact not_le.1 fun h4 => absurd (h3.1 h4) (not_le.2 ha)

theorem UpperTheory.V.Z.Sym.Dict.Br.isoAbs :
    ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), IsoOk i → ∀ (z : ℂ) (a : kˣ), absPow k' z (Units.map (i : k →* k') a) = absPow k z a := by
  intro k k' _ _ _ _ _ _ _ _ i hi z a
  have h1 := (isoVal k k' i hi).1
  have hc : Continuous i := continuous_of_val_iff i h1
  have hc' : Continuous i.symm := continuous_of_val_iff i.symm fun a b => by
    have := h1 (i.symm a) (i.symm b)
    simpa only [RingEquiv.apply_symm_apply] using this.symm
  have hn := GlobalTheory.SplitWeil.nabs_map_of_homeomorph i hc hc' a
  ext
  rw [val_absPow, val_absPow]
  exact congrArg (fun t : ℝ => (t : ℂ) ^ z) hn
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem rho_coe (P : Pre L) (v : Pl (Lp L)) (w : Plc L) (h : un w = v) (a : Kv v) :
    P.rho v w h ⟨a, 0⟩ = P.φ v w h a := by
  show P.φ v w h a + P.φ v w h 0 * P.rt w = _
  simp

private theorem exists_over (P : Pre L) (v : Pl (Lp L)) : ∃ w : Plc L, un w = v := by
  by_contra hne
  push_neg at hne
  have hE : IsEmpty {w : Plc L // un w = v} := ⟨fun w => hne w.1 w.2⟩
  have h01 := (rhoBij L P v).1 (a₁ := 0) (a₂ := 1) (funext fun w => (hE.false w).elim)
  exact zero_ne_one h01

private theorem conj_int (a : Af L) (hA : ∀ u : Plc L, pLoc L u a ∈ u.adicCompletionIntegers L) (w : Plc L) :
    pLoc L w (cjF a) ∈ w.adicCompletionIntegers L := by
  rw [pLoc_conjFin, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec _ w).2.2]
  exact hA _

private theorem star_int (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ))
    (hx : ∀ w h, P.rho v w h x ∈ w.adicCompletionIntegers L) (w : Plc L) (h : un w = v) :
    P.rho v w h (star x) ∈ w.adicCompletionIntegers L := by
  classical
  have hf : ∀ u : Plc L, (if h : un u = v then P.rho v u h x else 0) ∈ u.adicCompletionIntegers L := fun u => by
    by_cases hu : un u = v
    · rw [dite_eq_left hu]; exact hx u hu
    · rw [dite_eq_right hu]; exact zero_mem _
  let a : Af L := ⟨fun u => if h : un u = v then P.rho v u h x else 0, Filter.Eventually.of_forall hf⟩
  have ha : ∀ w h, P.rho v w h x = pLoc L w a := fun w h => by
    show _ = dite _ _ _
    rw [dite_eq_left h]
  rw [rhoStar L P v x a ha w h]
  exact conj_int a hf w

end UpperTheory.V.Z.Sym.Dict.Br

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoInt :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v (x : Lsq (Kv v) (cv v P.Δ)), IsIntegral (Ov v) x ↔ ∀ w h, P.rho v w h x ∈ w.adicCompletionIntegers L := by
  intro L _ _ _ P v x
  constructor
  · intro hx w h
    obtain ⟨p, hp, he⟩ := hx
    let f : Ov v →+* w.adicCompletionIntegers L :=
      ((P.φ v w h).comp (algebraMap (Ov v) (Kv v))).codRestrict (w.adicCompletionIntegers L)
        fun a => (rhoDiv L P v w h _).2 a.2
    have hc : (P.rho v w h).comp (algebraMap (Ov v) (Lsq (Kv v) (cv v P.Δ))) =
        (algebraMap (w.adicCompletionIntegers L) (Kw w)).comp f := by
      refine RingHom.ext fun a => ?_
      exact rho_coe P v w h _
    have hi : IsIntegral (w.adicCompletionIntegers L) (P.rho v w h x) := by
      refine ⟨p.map f, hp.map f, ?_⟩
      rw [Polynomial.eval₂_map, ← hc, ← Polynomial.hom_eval₂, he, map_zero]
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    rw [← hy]
    exact y.2
  · intro hx
    obtain ⟨w, h⟩ := exists_over P v
    have hs := star_int P v x hx w h
    have ht : 2 * x.re ∈ v.adicCompletionIntegers (Lp L) := by
      rw [← rhoDiv L P v w h, ← rho_coe P v w h]
      have : (⟨2 * x.re, 0⟩ : Lsq (Kv v) (cv v P.Δ)) = x + star x := by
        apply QuadraticAlgebra.ext <;> simp [two_mul]
      rw [this, map_add (f := _)]
      exact add_mem (hx w h) hs
    have hn : x.re * x.re - cv v P.Δ * (x.im * x.im) ∈ v.adicCompletionIntegers (Lp L) := by
      rw [← rhoDiv L P v w h, ← rho_coe P v w h]
      have : (⟨x.re * x.re - cv v P.Δ * (x.im * x.im), 0⟩ : Lsq (Kv v) (cv v P.Δ)) = x * star x := by
        apply QuadraticAlgebra.ext <;> simp <;> ring
      rw [this, map_mul]
      exact mul_mem (hx w h) hs
    let t : Ov v := ⟨_, ht⟩
    let n : Ov v := ⟨_, hn⟩
    refine ⟨Polynomial.X ^ 2 - (Polynomial.C t * Polynomial.X + Polynomial.C (-n)),
      Polynomial.monic_X_pow_sub (Polynomial.degree_linear_le.trans_lt (by norm_num)), ?_⟩
    have e1 : algebraMap (Ov v) (Lsq (Kv v) (cv v P.Δ)) t = ⟨2 * x.re, 0⟩ := rfl
    have e2 : algebraMap (Ov v) (Lsq (Kv v) (cv v P.Δ)) (-n) = ⟨-(x.re * x.re - cv v P.Δ * (x.im * x.im)), 0⟩ := rfl
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, e1, e2]
    apply QuadraticAlgebra.ext <;> simp [pow_two, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.isoJ :
    ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), IsoOk i → (∀ (V : Sig.Lev k) (V' : Sig.Lev k'), V.c = V'.c → (∀ a, Units.map (i : k →* k') a ∈ V'.H ↔ a ∈ V.H) → ∀ (n : ℕ) (g : GL (Fin n) k), GeneralLinearGroup.map (i : k →+* k') g ∈ V'.J n ↔ g ∈ V.J n) ∧ ∀ (n : ℕ) (g : GL (Fin n) k), GeneralLinearGroup.map (i : k →+* k') g ∈ KO k' (Fin n) ↔ g ∈ KO k (Fin n) := by
  intro k k' _ _ _ _ _ _ _ _ i hi
  obtain ⟨hv, hu, -, -⟩ := isoVal k k' i hi
  have hent : ∀ (n : ℕ) (g : GL (Fin n) k) (a b : Fin n),
      (GeneralLinearGroup.map (i : k →+* k') g : Matrix (Fin n) (Fin n) k') a b = i ((g : Matrix (Fin n) (Fin n) k) a b) := by
    intro n g a b
    rfl
  have h1 : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1 := hi.int
  refine ⟨?_, ?_⟩
  · intro V V' hc hH n g
    rw [Sig.memJ, Sig.memJ]
    simp only [hent, h1]
    have hpow : ∀ x : k, valuation k' (i x) ≤ valuation k' ↑(Hi.unif k') ^ (V'.c + 1) ↔
        valuation k x ≤ valuation k ↑(Hi.unif k) ^ (V.c + 1) := by
      intro x
      rw [← hu, hc, ← map_pow, ← map_pow, ← map_pow, hv]
    simp only [hpow]
    have hd : ∀ x : k, (∃ u ∈ V'.H, (u : k') = i x) ↔ (∃ u ∈ V.H, (u : k) = x) := by
      intro x
      constructor
      · rintro ⟨u, hu', he⟩
        refine ⟨Units.map (i.symm : k' →* k) u, ?_, ?_⟩
        · rw [← hH]
          convert hu'
          ext
          simp
        · simp [he]
      · rintro ⟨u, hu', he⟩
        refine ⟨Units.map (i : k →* k') u, (hH u).2 hu', ?_⟩
        simp [he]
    simp only [hd]
  · intro n g
    rw [Hi.GlAx.mem_KO, Hi.GlAx.mem_KO, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero,
      ← map_inv]
    exact and_congr (forall_congr' fun a => forall_congr' fun b => h1 _)
      (forall_congr' fun a => forall_congr' fun b => h1 _)
end
