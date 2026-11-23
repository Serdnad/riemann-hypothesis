module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle420
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle020
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch


open GlobalTheory.LatPair in
theorem exists_pair_of_line {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
    (Λ : Submodule 𝒪[k] (n ⊕ Fin 1 → k)) (hΛ : Λ.IsFullLattice k) (q : Unif k) (m : k)
    (h1 : ∀ t : k, (Sum.elim 0 (fun _ => t) : n ⊕ Fin 1 → k) ∈ Λ ↔ m * t ∈ 𝒪[k])
    (h2 : ∀ s : k, (∀ x ∈ Λ, s * ((q.1 : k) * (m * x (Sum.inr 0))) ∈ 𝒪[k]) ↔ s ∈ 𝒪[k]) :
    ∃ P : Pair k n, ∀ x : n ⊕ Fin 1 → k, x ∈ Λ ↔
      Sum.elim (fun a => x (Sum.inl a)) (fun j => m * x (Sum.inr j)) ∈ gluedS q 1 P.ker P.vec := by
  have hq := GlobalTheory.LevelUnfold.mul_inv_q q
  have hint : ∀ x ∈ Λ, (q.1 : k) * (m * x (Sum.inr 0)) ∈ 𝒪[k] := fun x hx => by
    simpa using (h2 1).2 (one_mem _) x hx
  have hqi : q.inv ∉ 𝒪[k] := fun h => q.2.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext hq))
  obtain ⟨e, he, he1⟩ : ∃ e ∈ Λ, (q.1 : k) * (m * e (Sum.inr 0)) = 1 := by
    have h := mt (h2 q.inv).1 hqi
    push Not at h
    obtain ⟨x, hx, hx'⟩ := h
    have hu : IsUnit (⟨_, hint x hx⟩ : 𝒪[k]) := by
      rw [← IsLocalRing.notMem_maximalIdeal, q.mem_max_iff]
      rintro ⟨c, hc⟩
      have hc' : (q.1 : k) * (m * x (Sum.inr 0)) = (q.1 : k) * c := congrArg Subtype.val hc
      apply hx'
      rw [hc', ← mul_assoc, mul_comm q.inv, hq, one_mul]
      exact c.2
    obtain ⟨c, hc⟩ := hu.exists_left_inv
    have hc' : (c : k) * ((q.1 : k) * (m * x (Sum.inr 0))) = 1 := congrArg Subtype.val hc
    refine ⟨c • x, Λ.smul_mem c hx, ?_⟩
    rw [← hc']
    change _ * (m * ((c : k) * _)) = _
    ring
  have hsplit : ∀ x : n ⊕ Fin 1 → k, x = inX k n 1 (x ∘ Sum.inl) + (Sum.elim 0 (fun _ => x (Sum.inr 0)) : n ⊕ Fin 1 → k) := fun x => by
    ext (j | j)
    · simp [inX]
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      simp [inX]
  let L : Submodule 𝒪[k] (n → k) := Λ.comap (inX k n 1)
  have hL : ∀ x : n ⊕ Fin 1 → k, m * x (Sum.inr 0) ∈ 𝒪[k] → (x ∈ Λ ↔ x ∘ Sum.inl ∈ L) := fun x hx => by
    conv_lhs => rw [hsplit x]
    exact Λ.add_mem_iff_left ((h1 _).2 hx)
  have key : ∀ (x : n ⊕ Fin 1 → k) (s : 𝒪[k]), (q.1 : k) * (m * x (Sum.inr 0)) = s →
      (x ∈ Λ ↔ x ∘ Sum.inl - s • (e ∘ Sum.inl) ∈ L) := fun x s hs => by
    rw [← Λ.sub_mem_iff_left (Λ.smul_mem s he)]
    refine hL (x - s • e) ?_
    have h0 : (q.1 : k) * (m * (x - s • e) (Sum.inr 0)) = 0 := by
      change (q.1 : k) * (m * (x _ - (s : k) * e _)) = 0
      linear_combination hs - (s : k) * he1
    rw [(mul_eq_zero.1 h0).resolve_left q.ne_zero]
    exact zero_mem _
  have hqe : q.1 • (e ∘ Sum.inl) ∈ L := by
    refine (hL (q.1 • e) ?_).1 (Λ.smul_mem _ he)
    change m * ((q.1 : k) * e _) ∈ _
    rw [mul_left_comm, he1]
    exact one_mem _
  have hlat : L.IsLattice k := by
    refine ⟨?_, ?_⟩
    · refine Submodule.fg_of_fg_map_injective (inX k n 1) (fun x y h => ?_) (hΛ.fg.of_le (Submodule.map_comap_le _ _))
      funext j
      exact congrFun h (Sum.inl j)
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli
  have hfull : L.IsFullLattice k := by
    refine { toIsLattice := hlat, span_eq_top := ?_ }
    rw [eq_top_iff]
    intro y _
    have hy : inX k n 1 y ∈ Submodule.span k (Λ : Set (n ⊕ Fin 1 → k)) := by
      rw [hΛ.span_eq_top]
      trivial
    have hproj : ∀ x ∈ Submodule.span k (Λ : Set (n ⊕ Fin 1 → k)),
        x ∘ Sum.inl ∈ Submodule.span k (L : Set (n → k)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        have hm : q.1 • (x ∘ Sum.inl) ∈ L := by
          refine (hL (q.1 • x) ?_).1 (Λ.smul_mem _ hx)
          change m * ((q.1 : k) * x (Sum.inr 0)) ∈ 𝒪[k]
          simpa [mul_comm, mul_left_comm, mul_assoc] using hint x hx
        have := Submodule.smul_mem (Submodule.span k (L : Set (n → k))) q.inv (Submodule.subset_span hm)
        simpa using this
      | zero => simp
      | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
      | smul a x _ hx => exact Submodule.smul_mem _ a hx
    simpa [inX] using hproj _ hy
  have hglue : IsGlue L (e ∘ Sum.inl) := by
    refine (isGlue_iff q).2 ⟨hfull, fun h => hqi ?_, hqe⟩
    have h3 : (Sum.elim 0 (fun _ => e (Sum.inr 0)) : n ⊕ Fin 1 → k) ∈ Λ := by
      rw [← Λ.add_mem_iff_right (show inX k n 1 (e ∘ Sum.inl) ∈ Λ from h), ← hsplit]
      exact he
    have h4 : q.inv = m * e (Sum.inr 0) := by
      rw [← mul_one q.inv, ← he1, ← mul_assoc, mul_comm q.inv, hq, one_mul]
    rw [h4]
    exact (h1 _).1 h3
  obtain ⟨P, hk, hv⟩ := hglue.exists_pair
  have hd : e ∘ Sum.inl - P.vec ∈ L := hk ▸ Pair.sub_vec_mem hv
  have hvec : ∀ (y : n → k) (s : 𝒪[k]), y - s • (e ∘ Sum.inl) ∈ L ↔ y - s • P.vec ∈ L := fun y s => by
    rw [← L.add_mem_iff_left (L.smul_mem s hd), smul_sub, sub_add_sub_cancel]
  refine ⟨P, fun x => ?_⟩
  rw [GlobalTheory.LevelUnfold.mem_gluedS, hk]
  constructor
  · intro hx
    refine ⟨⟨_, hint x hx⟩, (hvec _ _).1 ((key x _ rfl).1 hx), fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    change m * x _ = q.inv * ((q.1 : k) * _)
    rw [← mul_assoc, mul_comm q.inv, hq, one_mul]
  · rintro ⟨s, hs, hs'⟩
    have h3 : m * x (Sum.inr 0) = q.inv * s := (hs' 0).1 rfl
    refine (key x s ?_).2 ((hvec _ _).2 hs)
    rw [h3, ← mul_assoc, hq, one_mul]

section Place

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.CoreGlue

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem pr_cA_sec (c : k) : p.pr (cA D (p.sec c)) = 0 := by
  have he : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]
  have h0 : p.e * cA D (p.sec c) = 0 := by
    rw [← cA_cA p.e, ← map_mul, ← e_mul_sec p c, ← mul_assoc, cAe_mul_e, zero_mul, map_zero]
  have h1 := congrArg p.pr h0
  rwa [RingHom.map_mul, he, one_mul, RingHom.map_zero] at h1

theorem mul_sec_mem_intAt_iff (a : AE D) (t : k) : a * p.sec t ∈ intAt D (· = p.v) ↔ p.pr a * t ∈ 𝒪[k] := by
  rw [mul_comm, sec_mul_right, mem_intAt_iff p (sec_mem_idAt p _), pr_cA_sec, p.pr_sec, and_iff_left (zero_mem _), mul_comm]

theorem cA_sec_mul (a : AE D) (t : k) : cA D (p.sec t) * a = cA D (p.sec (t * p.pr (cA D a))) := by
  rw [← sec_mul_right, RingHom.map_mul, cA_cA]

theorem mul_cA_sec_mem_intAt_iff (a : AE D) (t : k) :
    a * cA D (p.sec t) ∈ intAt D (· = p.v) ↔ p.pr (cA D a) * t ∈ 𝒪[k] := by
  rw [mul_comm, cA_sec_mul, mem_intAt_iff p (csec_mem_idAt _), pr_cA_sec, cA_cA, p.pr_sec, and_iff_right (zero_mem _), mul_comm]

theorem exists_gluedW : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k), IsSumFrame o ζ β β₀ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → ∃ P : GlobalTheory.LatPair.Pair k n, GluedW β₀ M q (p.pr (incA D μ)) P := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M μ T q hs hM hμ hline hnorm hT
  have hb : p.pr (incA D (star μ)) ≠ 0 := (map_ne_zero (p.pr.comp (incA D))).2 (star_ne_zero.2 hμ)
  refine exists_pair_of_line (latW β₀ hM) ?_ q (p.pr (incA D μ)) (fun t => ?_) (fun s => ?_)
  · obtain ⟨Λ, h1, h2, -⟩ := exists_lat D k p S _ β₀ M hM
    have hlat : (latW β₀ hM).IsLattice k := by
      rwa [show latW β₀ hM = Λ from Submodule.ext fun x => (h2 x).symm]
    refine { toIsLattice := hlat, span_eq_top := ?_ }
    obtain ⟨m, s, c, hs, hc, -⟩ := exists_gen (p := p) hM
    rw [eq_top_iff]
    intro x _
    have hexp : x = ∑ l, c l (β₀.b *ᵥ x) • (β₀.b' *ᵥ fun a => p.pr (incA D (s l a))) := by
      have h := congrArg (β₀.b' *ᵥ ·) (hc (β₀.b *ᵥ x))
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul] at h
      rwa [Matrix.mulVec_mulVec, β₀.b'b, Matrix.one_mulVec] at h
    rw [hexp]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    change (fun i => p.sec ((β₀.b *ᵥ (β₀.b' *ᵥ fun a => p.pr (incA D (s l a)))) i)) ∈ latV S M (· = p.v)
    rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]
    exact sec_inc_mem (hs l)
  · refine Iff.trans ?_ ((hline _ (sec_mem_idAt p t)).trans (mul_sec_mem_intAt_iff p _ t))
    have h2 : (fun i => p.sec ((β₀.b *ᵥ (Sum.elim 0 (fun _ => t) : n ⊕ Fin 1 → k)) i)) = p.sec t • ratV (vecB o ζ) := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, sec_mul_right, hs]
      congr 1
      simp [mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]
    rw [← h2]
    rfl
  · obtain ⟨s', rfl⟩ : ∃ s', s = p.pr (incA D (star μ)) * s' := ⟨_, (mul_inv_cancel_left₀ hb s).symm⟩
    refine Iff.trans ?_ ((hline _ (csec_mem_idAt (p := p) s')).trans (mul_cA_sec_mem_intAt_iff p _ s'))
    have h2 : cA D (p.sec s') • ratV (vecB o ζ) =
        fun i => cA D (p.sec (s' * p.pr (incA D (star (vecB o ζ i))))) := funext fun i => cA_sec_mul p _ s'
    rw [h2]
    refine Iff.trans ?_ (csec_mem_iff hM _).symm
    have h3 : ∀ x : n ⊕ Fin 1 → k, s' * (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * x (Sum.inr 0)) ∈ 𝒪[k] ↔
        p.pr (incA D (star μ)) * s' * ((q.1 : k) * (p.pr (incA D μ) * x (Sum.inr 0))) ∈ 𝒪[k] := fun x => by
      rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, hnorm, RingHom.map_neg, RingHom.map_neg, RingHom.map_mul,
        RingHom.map_mul, RingHom.map_mul, RingHom.map_mul]
      generalize p.pr (incA D (T : D.host.E)) = a at hT
      generalize p.pr (incA D μ) = b
      generalize p.pr (incA D (star μ)) = c
      have h4 : valuation k (s' * (-(b * c * a) * x (Sum.inr 0))) =
          valuation k (c * s' * ((q.1 : k) * (b * x (Sum.inr 0)))) := by
        simp only [Valuation.map_mul, Valuation.map_neg, hT]
        ac_rfl
      rw [h4]
    constructor
    · intro h x hx
      have hx' : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [mulVec_mulVec, β₀.bb', one_mulVec]
      rw [hx'] at hx ⊢
      rw [pair_sumFrame o ζ hs, h3]
      exact h _ hx
    · intro h x hx
      rw [← h3, ← pair_sumFrame o ζ hs]
      exact h _ hx

end Place

end GlobalTheory.Core.Mi.LatMatch

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColsXZeroNormal

theorem colsAt_xZero_of_normalFr : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.ColsAt ((y.bes j ρ h).lev (a.x j).vol).d (xZero ((y.jac j ρ h).lev (a.x (j + 1)).vol).d) (N j) (N (j + 1)) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D ψ hψ a y βT PP l FY sc hN hx N M hNsd hNI hMsd hcore j ρ h
  rw [← l.under]
  intro i b hb
  rw [l.unit.2]
  have hs := l.hs
  have hdB : j + (2 * ρ + 1) = l.s + 1 := by omega
  have hdJ : j + 1 + 2 * ρ = l.s + 1 := by omega
  have hxi := GlobalTheory.ColsBFSplit.xi_unit l.q l.unit
  obtain ⟨hsc, -, hhz, hB, hJ, -⟩ := hN
  obtain ⟨m₀, m₁, h0, h1, hp⟩ := GlobalTheory.T.besselNormalFrame_isotropicColumns_pairing D l.k (ofSplit l.q) ρ ((y.bes j ρ h).lev (a.x j).vol)
    (XIx (Fin D.R.k) (Fin D.R.t) j) (2 * ρ + 1) (sc j) (l.FX j (by omega)) (FY j (2 * ρ + 1) hdB) (hB j ρ h (2 * ρ + 1) hdB) i
  obtain ⟨n₀, n₁, g0, g1, gp⟩ := GlobalTheory.T.fourierJacobiNormalFrame_isotropicColumns_pairing D l.k (ofSplit l.q) ρ ((y.jac j ρ h).lev (a.x (j + 1)).vol)
    (XIx (Fin D.R.k) (Fin D.R.t) (j + 1)) (2 * ρ) (sc j) ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol))
    (l.FX (j + 1) (by omega)) (FY (j + 1) (2 * ρ) hdJ) (hJ j ρ h (2 * ρ) hdJ) i
  have v0 : valuation l.k (sc j * (ofSplit l.q).xi ^ (ρ - i.val)) = 1 := by
    rw [map_mul, map_pow, hsc, hxi, one_pow, one_mul]
  have v1 : valuation l.k (sc j * (-(ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi) *
      (-1 / (ofSplit l.q).xi) ^ (ρ - 1 - i.val)) = 1 := by
    rw [map_mul, map_mul, map_pow, map_div₀, map_div₀, Valuation.map_neg, Valuation.map_neg, map_one, hsc, hhz, hxi]
    simp
  have w1 : valuation l.k (sc j * ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi) *
      (-1 / (ofSplit l.q).xi) ^ (ρ - 1 - i.val)) = 1 := by
    rw [map_mul, map_mul, map_pow, map_div₀, map_div₀, Valuation.map_neg, map_one, hsc, hhz, hxi]
    simp
  have eV := GlobalTheory.ColsBFSplit.line_crit l.q (FY j (2 * ρ + 1) hdB) (fun r => ((y.bes j ρ h).lev (a.x j).vol).d.e r i)
    (fun r => ((y.bes j ρ h).lev (a.x j).vol).d.e' r i) m₀ m₁ _ _ (hNsd j (by omega)) (hNI j _ hdB) v0 v1 h0 h1
    (GlobalTheory.T.wittHyperbolic_conj_pairing_eq_one D _ _ ρ ((y.bes j ρ h).lev (a.x j).vol).d i) hp b hb
  have eW := GlobalTheory.ColsBFSplit.line_crit l.q (FY (j + 1) (2 * ρ) hdJ) (fun r => ((y.jac j ρ h).lev (a.x (j + 1)).vol).d.e r i)
    (fun r => ((y.jac j ρ h).lev (a.x (j + 1)).vol).d.e' r i) n₀ n₁ _ _ (hNsd (j + 1) (by omega)) (hNI (j + 1) _ hdJ) v0 w1
    g0 g1 (GlobalTheory.T.wittHyperbolic_conj_pairing_eq_one D _ _ ρ ((y.jac j ρ h).lev (a.x (j + 1)).vol).d i) gp b hb
  exact eV.trans eW.symm

end GlobalTheory.ColsXZeroNormal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_xi (p : SplitPt D k) (hU : p.UnitAA) : valuation k (p.pr (incA D D.host.xi0)) = 1 := by
  have hi : p.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
    obtain ⟨η, hη, h0, h⟩ := exists_idem p
    have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = p.v) := by
      refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
      · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
        exact TensorProduct.zero_tmul _ _
      · refine Ideal.mem_iInf.2 fun w => ?_
        change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
        rw [h0 w.1 w.2, TensorProduct.zero_tmul]
    have := pr_int p (hU.1 _ hm).2.2
    rwa [map_mul, pr_pair_tmul p h, map_one, map_one, mul_one] at this
  have h0 : D.host.xi0 ≠ 0 := fun h => by
    have := GlobalTheory.MixModel.HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D)
    rw [h, map_zero, zero_mul] at this
    have h2 := congrArg p.pr this
    rw [map_zero, map_one] at h2
    exact zero_ne_one h2
  have a := (Valuation.mem_integer_iff _ _).1 (xi_zero_projection_integral p hU)
  have b := (Valuation.mem_integer_iff _ _).1 hi
  have ab : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ h0, map_one, map_one, map_one]
  exact le_antisymm a (by calc (1 : ValueGroupWithZero k) = _ := ab.symm
      _ ≤ valuation k (p.pr (incA D D.host.xi0)) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _)

theorem val_star_xi (p : SplitPt D k) (hU : p.UnitAA) : valuation k (p.pr (incA D (star D.host.xi0))) = 1 := by
  rw [Brg.star_purely_imaginary_eq_neg, map_neg, map_neg, Valuation.map_neg, val_xi p hU]

theorem val_nat (p : SplitPt D k) {PP : Pl D.host.E} (hI : Formalism.L2.NTheta.IsIdemAt p.e PP) (n : ℕ)
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) : valuation k (p.pr (incA D (n : D.host.E))) = 1 := by
  have hx : ((n : ℕ) : 𝓞 D.host.E) ≠ 0 := fun h => hn (h ▸ PP.asIdeal.zero_mem)
  have h1 := (hI.2 _ hx).not.1 hn
  rw [not_not] at h1
  have hcast : (((n : ℕ) : 𝓞 D.host.E) : D.host.E) = (n : D.host.E) := by simp
  rw [hcast] at h1
  have hi : p.pr (incA D (n : D.host.E)⁻¹) ∈ 𝒪[k] := by
    rw [p.int_iff, p.sec_pr]; exact h1
  have hn0 : (n : D.host.E) ≠ 0 := by
    intro h; apply hx; exact_mod_cast (by rw [hcast]; exact h : (((n : ℕ) : 𝓞 D.host.E) : D.host.E) = 0)
  have a : valuation k (p.pr (incA D (n : D.host.E))) ≤ 1 := by
    rw [map_natCast, map_natCast]
    exact (Valuation.mem_integer_iff _ _).1 (natCast_mem _ n)
  have b := (Valuation.mem_integer_iff _ _).1 hi
  have ab : valuation k (p.pr (incA D (n : D.host.E))) * valuation k (p.pr (incA D (n : D.host.E)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ hn0, map_one, map_one, map_one]
  exact le_antisymm a (by calc (1 : ValueGroupWithZero k) = _ := ab.symm
      _ ≤ valuation k (p.pr (incA D (n : D.host.E))) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _)

end GlobalTheory.Fam.FramesY

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tau_norm {a : XGeo D} (y : YRat a) {lam : D.host.E} (hT : y.Tau lam) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    star lam * (lam * (star (y.bes j 0 h).ζ ⬝ᵥ (y.bes j 0 h).L.gram *ᵥ (y.bes j 0 h).ζ)) =
      -(D.host.xi0 * star D.host.xi0) * (star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀) := by
  obtain ⟨h1, h2⟩ := hT j h
  have h3 := congrArg (fun A => star a.ζ₀ ⬝ᵥ A *ᵥ a.ζ₀) h1
  simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, dotProduct_smul] at h3
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h2, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, smul_eq_mul] at h3
  rw [← h3]; ring

end GlobalTheory.Fam.FramesY

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_hz {a : XGeo D} (y : YRat a) (q : SplitPt D k) (hU : q.UnitAA) {PP : Pl D.host.E}
    (hI : Formalism.L2.NTheta.IsIdemAt q.e PP) (n : ℕ) (hT : y.Tau (-D.host.xi0 ^ (D.R.m / 2)))
    (hn : star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((n : ℕ) : D.host.E)) (hnP : ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) :
    ∀ ρ j (h : j + 2 * ρ + 2 = D.R.m), valuation k ((ofSplit q).hz ((y.bes j ρ h).lev (a.x j).vol)) = 1 := by
  have hx := val_xi q hU
  have hs := val_star_xi q hU
  have hN := val_nat q hI n hnP
  intro ρ
  induction ρ with
  | zero =>
    intro j h
    change valuation k (q.pr (incA D (star (y.bes j 0 h).ζ ⬝ᵥ (y.bes j 0 h).L.gram *ᵥ (y.bes j 0 h).ζ))) = 1
    have h3 := congrArg (fun x => valuation k (q.pr (incA D x))) (tau_norm y hT j h)
    simp only [hn, map_mul, map_neg, map_pow, Valuation.map_neg, Valuation.map_pow, star_neg, star_pow, hx, hs, hN,
      one_pow, one_mul, mul_one] at h3
    exact h3
  | succ σ ih =>
    intro j h
    have h1 := (y.lnk j σ h).norm
    change star (y.bes j (σ + 1) h).ζ ⬝ᵥ (y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ = _ at h1
    change valuation k (q.pr (incA D (star (y.bes j (σ + 1) h).ζ ⬝ᵥ (y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ))) = 1
    rw [h1, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, hx, hs, one_mul, one_mul]
    exact ih _ _

end GlobalTheory.Fam.FramesY

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

theorem normalFrames_exist : ∀ {D : D7} (a : XGeo D) (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E}
    (l : LocX a βT PP) (n : ℕ), y.Tau (-D.host.xi0 ^ (D.R.m / 2)) →
    star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((n : ℕ) : D.host.E) → ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal →
    ∃ (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc := by
  intro D a y βT PP l n hT hn hnP
  have hxi : (ofSplit l.q).xi ≠ 0 := GlobalTheory.LocMod.Witness.xi_ne (ofSplit l.q)
  have hv : valuation l.k (ofSplit l.q).xi = 1 := val_xi l.q l.unit
  have hsc : ∀ j, (ofSplit l.q).xi ^ (j / 2) ≠ 0 := fun j => pow_ne_zero _ hxi
  have hz := val_hz y l.q l.unit l.idem n hT hn hnP
  have hm := l.hs
  obtain ⟨r, hr⟩ := D.R.m_even
  have key : ∀ j c (hc : j + c = l.s + 1), ∃ F : Frame l.k (Yc D j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c),
      (∀ ρ h, (ofSplit l.q).IsBesFrame ((y.bes j ρ h).lev (a.x j).vol) ((ofSplit l.q).xi ^ (j / 2))
        (l.FX j (by omega)) F) ∧
      ∀ j' (hj : j = j' + 1) ρ h, (ofSplit l.q).IsJacFrame ((y.jac j' ρ h).lev (a.x (j' + 1)).vol)
        ((ofSplit l.q).xi ^ (j' / 2)) ((ofSplit l.q).hz ((y.bes j' ρ h).lev (a.x j').vol)) (l.FX (j' + 1) (by omega))
        (hj ▸ F) := by
    intro j c hc
    by_cases hE : ∃ ρ, j + 2 * ρ + 2 = D.R.m
    · obtain ⟨ρ, h⟩ := hE
      obtain ⟨F, hF⟩ := GlobalTheory.LocMod.Witness.exists_bes (ofSplit l.q) ((y.bes j ρ h).lev (a.x j).vol) (hsc j)
        (l.FX j (by omega))
      obtain rfl : c = 2 * ρ + 1 := by omega
      refine ⟨F, fun ρ' h' => ?_, fun j' hj ρ' h' => absurd h' (by omega)⟩
      obtain rfl : ρ' = ρ := by omega
      exact hF
    · have hE' : ∀ ρ, j + 2 * ρ + 2 ≠ D.R.m := fun ρ h => hE ⟨ρ, h⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hE' (r - 1); omega⟩
      obtain ⟨ρ, hρ⟩ : ∃ ρ, j' + 2 * ρ + 2 = D.R.m := ⟨(D.R.m - j' - 2) / 2, by have := hE' ((D.R.m - j' - 3) / 2); omega⟩
      obtain ⟨F, hF⟩ := GlobalTheory.LocMod.Witness.exists_jac (ofSplit l.q) ((y.jac j' ρ hρ).lev (a.x (j' + 1)).vol) (hsc j')
        (GlobalTheory.LocMod.Witness.hz_ne (ofSplit l.q) ((y.bes j' ρ hρ).lev (a.x j').vol)) (l.FX (j' + 1) (by omega))
      obtain rfl : c = 2 * ρ := by omega
      refine ⟨F, fun ρ' h' => absurd h' (hE' ρ'), fun j'' hj ρ' h' => ?_⟩
      obtain rfl : j'' = j' := by omega
      obtain rfl : ρ' = ρ := by omega
      exact hF
  refine ⟨fun j c hc => (key j c hc).choose, fun j => (ofSplit l.q).xi ^ (j / 2), fun j => ?_, fun j => ?_,
    fun j ρ h => hz ρ j h, fun j ρ h c hc => (key j c hc).choose_spec.1 ρ h,
    fun j ρ h c hc => (key (j + 1) c hc).choose_spec.2 j rfl ρ h, fun h => ?_⟩
  · rw [map_pow, hv, one_pow]
  · show (ofSplit l.q).xi ^ ((j + 1 + 1) / 2) = (ofSplit l.q).xi ^ (j / 2) * (ofSplit l.q).xi
    rw [show (j + 1 + 1) / 2 = j / 2 + 1 by omega, pow_succ]
  · have h2 := (hT l.s h).2
    funext i
    have e1 : ((y.τ l.s h).map (ofSplit l.q).pr *ᵥ fun i => (ofSplit l.q).pr (a.ζ₀ i)) i =
        GlobalTheory.LocMod.Witness.prH (ofSplit l.q) ((y.τ l.s h *ᵥ a.ζ₀) i) :=
      (RingHom.map_mulVec (GlobalTheory.LocMod.Witness.prH (ofSplit l.q)) _ _ i).symm
    rw [e1, h2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_neg, map_pow]
    change -((ofSplit l.q).xi ^ (D.R.m / 2)) * (ofSplit l.q).pr ((y.bes l.s 0 h).ζ i) = _
    rw [show D.R.m / 2 = l.s / 2 + 1 by omega, pow_succ]
    ring

end GlobalTheory.Fam.FramesY
end
end
