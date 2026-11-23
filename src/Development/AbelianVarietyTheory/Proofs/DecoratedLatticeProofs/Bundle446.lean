module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle395
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle363
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle436
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle351
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle360
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle281
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle247
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle384
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle417
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle253
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle432
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle419
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.DiaChart

theorem decoratedLattice_unitScale_functional_keeps_frames {X : Formalism.L2.Col.Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y}
    (p : PtY (X := X) (n := n) ST SG Q y) (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (P' : HeightOneSpectrum (𝓞 X.E)) :
    ptFr (p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco)).1.1 P' = ptFr p.1.1 P' := by
  by_cases h : (∀ (P₁ : Q) (x : Formalism.L2.Col.Sp X.E n), p.1.1.1.2 P₁ x ∈ (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco).1.at P₁.1 ↔
      x ∈ Formalism.L2.Col.stdAt X.E n P₁.1) ∧ p.1.2 ∈ y.ys (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco).1.N
  · have e : p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco) =
        ⟨(⟨(Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ := dif_pos h
    rw [e]
    unfold ptFr
    rfl
  · have e : p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco) = p := dif_neg h
    rw [e]

theorem finM_mul' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_mul V g h

theorem ptOf_gl_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b (c : {c // A.chOf j c = b}), ∃ e : 𝓀[k]ˣ ≃ ((I.atT l u a).Fv v)ˣ, ∀ s,
        ∃ z : TC.GA B (B.R.N j),
          z.1 = finM _ (rankN (I.rec7 l Z) j hj) (A.h j b c * (β j i).gl (g s)) ∧
          TC.PtOf (z * A.kb j b) (extTo I.SQ (((I.atIn u a).A j).diaPt v (e s) c.1).1.1) := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hStd j hj i v hv g hg b c
  obtain ⟨c, rfl⟩ := c
  obtain ⟨-, ρ, hρ⟩ := GlobalTheory.FinPl.SplitPt.resField_equiv (I.rec7 l Z) k (p i) v.1 hv
  refine ⟨(Units.mapEquiv ρ.toMulEquiv).toEquiv, fun s => ?_⟩
  obtain ⟨δ, hδ, huni, hint, hint'⟩ := GlobalTheory.AdForm.frameGl_int I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv (g s) s (hg s)
  have htriv := GlobalTheory.T.frameImage_trivial_off_levelPrime I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv (g s) δ hδ
  have hrow := GlobalTheory.AdForm.lastRow_inv_frame I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv ρ hρ (g s) s (hg s) δ hδ hint'
  have hR := hA.reads j hj
  let y : TC.GA B (B.R.N j) := ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1
  refine ⟨y * δ, ?_, ?_⟩
  · rw [Units.val_mul, hδ, finM_mul', (hA.h j hj _ ⟨c, rfl⟩).2]
    rfl
  · obtain ⟨p0, hk0, hN0⟩ := hR.k_std (A.chOf j c)
    have hkc := hk0.lat
    rw [hN0] at hkc
    refine GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt _ _ _ _ _ _ _ y δ (A.kb j (A.chOf j c)) (extTo I.SQ ((I.stp u a j).rep c).1.1) _
      ⟨v.1, v.2⟩ ((Units.mapEquiv ρ.toMulEquiv) s) _ (hR.pt c) hk0.uni huni hkc hint hint' htriv
      (fun r r' hr => hR.k_T (A.chOf j c) ⟨v.1, v.2⟩ r r' hr) (fun r r' hr => hrow r r' hr) ?_ ?_
    · rw [extTo_deco, extTo_deco]
      exact GlobalTheory.Mem.Col2.TwAtStd.diaPt_deco B X I u a j ⟨v.1, v.2⟩ _ c
    · funext P'
      rw [extTo_fr, extTo_fr]
      exact decoratedLattice_unitScale_functional_keeps_frames ((I.stp u a j).rep c) ⟨v.1, v.2⟩ _ P'.1

end GlobalTheory.AdForm.DiaChart

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.AdForm.CompFix.intMat_keeps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (M M' : Matrix n n k) (hMM : M * M' = 1) (hM : ∀ r s, M r s ∈ 𝒪[k])
    (hM' : ∀ r s, M' r s ∈ 𝒪[k]) (r₀ : n) (hr : ∀ s, valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) < 1) (z : n → k) :
    ((∀ r, (M' *ᵥ z) r ∈ 𝒪[k]) ↔ ∀ r, z r ∈ 𝒪[k]) ∧ ((∀ r, z r ∈ 𝒪[k]) → valuation k ((M' *ᵥ z) r₀ - z r₀) < 1) := by
  have hint : ∀ (N : Matrix n n k), (∀ r s, N r s ∈ 𝒪[k]) → ∀ w : n → k, (∀ r, w r ∈ 𝒪[k]) → ∀ r, (N *ᵥ w) r ∈ 𝒪[k] :=
    fun N hN w hw r => Subring.sum_mem _ fun s _ => Subring.mul_mem _ (hN r s) (hw s)
  refine ⟨⟨fun h r => ?_, fun h => hint M' hM' z h⟩, fun h => ?_⟩
  · have e : M *ᵥ (M' *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
    rw [← e]
    exact hint M hM _ h r
  · have e : (M' *ᵥ z) r₀ - z r₀ = ∑ s, (M' r₀ s - (1 : Matrix n n k) r₀ s) * z s := by
      have : z r₀ = ∑ s, (1 : Matrix n n k) r₀ s * z s := by simp [Matrix.one_apply]
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_sub_distrib]
      simp_rw [sub_mul]
    rw [e]
    refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
    rw [Valuation.map_mul]
    have h1 := hr s
    have h2 : valuation k (z s) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (h s)
    calc valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * valuation k (z s) ≤ valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * 1 :=
          mul_le_mul' le_rfl h2
      _ < 1 := by rw [mul_one]; exact h1



theorem GlobalTheory.AdForm.comp_fixes_stdPair : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ κ ∈ A.U j b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), κ * ((β j i).gl g)⁻¹ ∈ grpOff ((I.rec7 l Z).sp.X j) (· = (p i).v) → g • Q j i = Q j i := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b κ hκ i g hg

  let e := Classical.choose hS.1
  have he := Classical.choose_spec hS.1
  obtain ⟨hpi, hT⟩ := GlobalTheory.T.generator_mem_split_prime_level_prime_mem_place I hOk l Z u k (p i) (e i) (he i)
  have key : ∀ κ₀ ∈ A.U j b, ∀ r s : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank,
      ((mt _ κ₀).map (p i).pr) r s ∈ 𝒪[k] ∧ (r.1 + 1 = ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank →
        valuation k (((mt _ κ₀).map (p i).pr) r s - (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) k) r s) < 1) := by
    intro κ₀ hκ₀ r s
    have hn := rankN (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) j hj
    have h3 := GlobalTheory.T.chartLevel_column_sub_one_mem_baseLattice I hOk hPins l Z u a Ch A hA j hj b κ₀ hκ₀ (p i).v hT (Fin.cast hn s)
    let y : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j) → AE (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) := fun r' =>
      mt _ κ₀ (Fin.cast hn.symm r') s - (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (AE (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G))) (Fin.cast hn.symm r') s
    have hy : (fun r' => Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E) (p i).v (toEAf (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (y r'))) =
        (fun r' => Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E) (p i).v (GlobalTheory.AdForm.finM _ hn κ₀ r' (Fin.cast hn s)) -
          (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j)) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j)) ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.F] (p i).v.adicCompletion (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.F)) r' (Fin.cast hn s)) := by
      funext r'
      simp only [y]
      rw [RingHom.map_sub, RingHom.map_sub]
      congr 1
      by_cases h : r' = Fin.cast hn s
      · subst h
        have : Fin.cast hn.symm (Fin.cast hn s) = s := Fin.ext rfl
        rw [this, Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, RingHom.map_one]
      · have h' : Fin.cast hn.symm r' ≠ s := fun h2 => h (Fin.ext (by rw [← h2]; rfl))
        rw [Matrix.one_apply_ne h', Matrix.one_apply_ne h, RingHom.map_zero, RingHom.map_zero]
    have hLb : ∀ x, x ∈ (A.K j hj b).lev.Lb ↔ ∀ j' : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j), ∃ r : 𝓞 (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E, x j' = (r : (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E) ∧ (j'.1 + 1 = (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j → X.piT u ∣ r) :=
      fun x => (hA.reads j hj).lb b x
    rw [← hy] at h3
    have h4 := GlobalTheory.T.splitPoint_baseLattice_coords_integral_last_in_prime (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) k (p i) (e i).1 (he i) ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j) (X.piT u) hpi (A.K j hj b).lev.Lb hLb y h3 (Fin.cast hn r)
    have hyr : y (Fin.cast hn r) = mt _ κ₀ r s - (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (AE (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G))) r s := rfl
    rw [hyr] at h4
    have h1 : (p i).pr ((1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (AE (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G))) r s) =
        (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) k) r s := by
      simp only [Matrix.one_apply]; split_ifs <;> simp
    rw [map_sub, h1] at h4
    refine ⟨?_, fun hr => ?_⟩
    · have := Subring.add_mem _ h4.1 (show (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) k) r s ∈ 𝒪[k] by
        simp only [Matrix.one_apply]; split_ifs
        · exact Subring.one_mem _
        · exact Subring.zero_mem _)
      rwa [sub_add_cancel] at this
    · exact h4.2 (by rw [Fin.coe_cast, ← hn]; exact hr)

  set M := (mt _ κ).map (p i).pr with hMdef
  set M' := (mt _ κ⁻¹).map (p i).pr with hM'def
  have hmt : ∀ x y : GA (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j), mt _ (x * y) = mt _ x * mt _ y := fun x y => by
    simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]
  have hMM : M * M' = 1 := by
    rw [hMdef, hM'def, ← Matrix.map_mul, ← hmt, mul_inv_cancel]
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM'M : M' * M = 1 := by
    rw [hMdef, hM'def, ← Matrix.map_mul, ← hmt, inv_mul_cancel]
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM := GlobalTheory.T.splitPlace_matrix_eq_of_agree_with_framedGL (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) k (p i) _ _ (β j i) κ g hg
  rw [← hMdef] at hM
  rcases Nat.eq_zero_or_pos ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank with h0 | hpos
  · have : g = 1 := by
      apply Units.ext
      apply Matrix.ext
      intro a b
      have ha : a.val < ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank := a.isLt
      omega
    rw [this, one_smul]
  let r₀ : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank := ⟨((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank - 1, by omega⟩
  have hr₀ : r₀.1 + 1 = ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank := by simp only [r₀]; omega
  have hK := GlobalTheory.AdForm.CompFix.intMat_keeps M M' hMM (fun r s => (key κ hκ r s).1) (fun r s => (key κ⁻¹ (inv_mem hκ) r s).1) r₀
    (fun s => (key κ⁻¹ (inv_mem hκ) r₀ s).2 hr₀)

  have hbg : ∀ x : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank → k, (β j i).b *ᵥ (g⁻¹ • x) = M' *ᵥ ((β j i).b *ᵥ x) := by
    intro x
    have e1 : (β j i).b * g.val = M * (β j i).b := by
      rw [hM, Matrix.mul_assoc, Matrix.mul_assoc, (β j i).b'b, Matrix.mul_one]
    have e2 : (β j i).b *ᵥ x = M *ᵥ ((β j i).b *ᵥ (g⁻¹ • x)) := by
      have e3 : x = g.val *ᵥ (g⁻¹ • x) := by
        change x = g.val *ᵥ ((g⁻¹).val *ᵥ x)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      conv_lhs => rw [e3]
      rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    rw [e2, Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
  refine Pair.ext fun x a' => ?_
  rw [Pair.smul_hasVal, GlobalTheory.T.standardPair_frameCoordinates_integral_and_functional I l Z u k ι p β Q L hS j hj i r₀ hr₀, GlobalTheory.T.standardPair_frameCoordinates_integral_and_functional I l Z u k ι p β Q L hS j hj i r₀ hr₀, hbg]
  have hres : ∀ (s y₁ y₂ : 𝒪[k]), valuation k ((y₁ : k) - y₂) < 1 → residue 𝒪[k] (s * y₁) = residue 𝒪[k] (s * y₂) := by
    intro s y₁ y₂ h
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← mul_sub]
    refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 ?_)
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 (by simpa using h)
  obtain ⟨hiff, hlast⟩ := hK ((β j i).b *ᵥ x)
  constructor
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, ((β j i).b *ᵥ x) r ∈ 𝒪[k] := hiff.1 fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine hres s _ _ ?_
    rw [hy r₀]
    exact hlast hz
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, ((β j i).b *ᵥ x) r ∈ 𝒪[k] := fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hiff.2 hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine (hres s _ _ ?_).symm
    rw [hy r₀]
    exact hlast hz

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

open GlobalTheory.AdForm




theorem GlobalTheory.AdForm.std_comp_mem_levelVL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) b i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i →
    ∀ x : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F),
    x.1.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
    Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1 ∈ Formalism.UG.levelVL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (p i).v (A.K j hj b).lev.Lb := by
  intro B X I hI hP l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b i g hg x hx
  obtain ⟨⟨e, he⟩, hS2⟩ := hS
  obtain ⟨hL, hS3⟩ := hS2 j hj
  obtain ⟨hLat, hVal⟩ := hS3 i
  obtain ⟨hX, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  have hmem : X.piT u ∈ (e i).1.asIdeal := (Formalism.L2.Col.mem_divs hne _).1 (e i).2
  have hsq : X.piT u ∉ (e i).1.asIdeal ^ 2 := hPr.piT_notMem_sq hX u (e i).2
  have hconj : B.fields.conjO (X.piT u) ∉ (e i).1.asIdeal := fun h => by
    obtain ⟨s, t, hst⟩ := hcop
    have : (1 : 𝓞 B.fields.E) ∈ (e i).1.asIdeal := by
      rw [← hst]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ h)
    exact (e i).1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨φ, hφ1, hφ2, hφ3, hφ4⟩ := GlobalTheory.T.exists_splitPlace_component_ringHom_integral _ k (p i) (e i).1 (he i)
  obtain ⟨⟨q, hq⟩, hc⟩ := GlobalTheory.T.valuation_eq_uniformizer_and_unit_at_prime _ k (p i) (e i).1 (he i) (X.piT u) (B.fields.conjO (X.piT u)) hmem hsq hconj
  have hlat := GlobalTheory.T.mem_integralVectors_component_iff_integral_frame_coords _ k (p i) _ _ (β j i) (L j) hL _ hLat
  have hv6 := GlobalTheory.T.functional_values_integral_vectors_of_integer_vectors _ k (p i) (e i).1 (he i) _ (β j i).b (β j i).b' (β j i).bb' (β j i).b'b (Q j i) hlat
    (B.fields.conjO (X.piT u)) (fun z hz r hr => hVal z ((hL z).2 hz) r hr)
  have hn := rankN (I.rec7 l Z) j hj
  obtain ⟨hhh, hkeep, hkeep'⟩ := GlobalTheory.T.residuePairStabilizer_keeps_integralLastCoordDiv k _ _ hn (β j i).b (β j i).b' (β j i).bb' (β j i).b'b (Q j i) hlat _
    (φ (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) ((p i).v.adicCompletion (I.rec7 l Z).host.F) ((X.piT u : 𝓞 B.fields.E) : B.fields.E)))
    q ((congrArg (valuation k) (hφ2 _)).trans hq) hc hv6 g hg
  have hg1 : gramN (I.rec7 l Z) j hj = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hj).1
  have hU := Formalism.UG.P.afsplit_bc_mem (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (p i).v x.1 x.2
  refine Subgroup.mem_inf.2 ⟨hU, ?_⟩
  have hU1 : Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1 ∈
      Formalism.UG.UJ (Formalism.UG.sigR (sigD (I.rec7 l Z)) ((p i).v.adicCompletion (I.rec7 l Z).host.F)) 1 := by
    have h1 : Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1 ∈
        Formalism.UG.UJ (Formalism.UG.sigR (sigD (I.rec7 l Z)) ((p i).v.adicCompletion (I.rec7 l Z).host.F))
          ((gramN (I.rec7 l Z) j hj).map (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) ((p i).v.adicCompletion (I.rec7 l Z).host.F))) := hU
    have hJ : (gramN (I.rec7 l Z) j hj).map (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) ((p i).v.adicCompletion (I.rec7 l Z).host.F)) = 1 := by
      rw [hg1]; exact Matrix.map_one _ (map_zero _) (map_one _)
    rwa [hJ] at h1
  have hM : (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1).val.map φ =
      ((β j i).b * g.val * (β j i).b').reindex (finCongr hn) (finCongr hn) := by
    rw [← (β j i).gl_mat g]
    ext r s
    simp only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    change φ (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v (x.1.1 r s)) = _
    rw [hx]
    simp only [finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
    rw [hφ1]
  exact GlobalTheory.T.unitary_keeps_baseLattice_of_split_components _ _ (sigD (I.rec7 l Z)) (p i).v k φ hφ4 _ (X.piT u) (A.K j hj b).lev.Lb (fun y => (hA.reads j hj).lb b y) q ((congrArg (valuation k) (hφ2 _)).trans hq)
    ((congrArg (valuation k) (hφ3 _)).trans hc) _ hU1 _ _ hM hhh hkeep hkeep'
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.AdForm.exists_readsG_of_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∃ G', ReadsG K eW j g.bT G' f.1 := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ hX j hj P t a bad K eW hR heW hb hL f

  have hv : ∀ c : (I.stX a).Cl, ∃ w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT, ∀ v h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 →
      f.1 v (h * g.bT) = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w := by
    intro c
    obtain ⟨h₀, hh₀⟩ := GlobalTheory.Core.Rk.Top.Model.hasMat_exists (D := I.rec7 l Z) (K.y c)
    obtain ⟨w, hw, e⟩ := GlobalTheory.T.exists_coefficientVector_reading_realRepresentation_form I l Z u a R.MX j hj ((LinearMap.proj (h₀ * g.bT)).comp f.1)
    refine ⟨w, hw, fun v h hh => ?_⟩
    rw [GlobalTheory.Core.Rk.Top.Model.hasMat_pt hh hh₀]
    exact e v
  choose w hw hwv using hv
  obtain ⟨G', hG'⟩ := GlobalTheory.T.exists_rowForm_prescribed_values_class_representatives (I.perIn u a) B.fields.emb B.embLL (fun _ => rfl) w hw
    (fun c s => GlobalTheory.T.readingVector_fixed_by_class_stabiliser_character I hI hP l Z u R g c₀ hX j hj P t a bad K hR hb hL f c (w c) (hw c) (hwv c) s)
  refine ⟨G', fun c v h hh => ?_⟩
  rw [hwv c v h hh]
  have hz : ∀ c', eW.symm (Pi.single c (j v)) c' = (Pi.single c (j v) : (I.fm l u a).clsP → Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ) c' := by
    intro c'
    funext y'
    have := heW (eW.symm (Pi.single c (j v))) c' y' y' rfl
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  generalize eW.symm (Pi.single c (j v)) = z at hz
  have hzc : z c = j v := by rw [hz c, Pi.single_eq_same]
  have hzo : ∀ c', c' ≠ c → z c' = 0 := fun c' h => by
    rw [hz c']
    exact Pi.single_eq_of_ne h _
  haveI := (l.per u a).step.fin_stab c.1 ((I.perIn u a).S'.rep c)
  have hne : ((Nat.card ((I.perIn u a).S'.Stab c) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI := (I.perIn u a).clFin (l.per u a)
  show _ = _ * (∑ c' : (I.perIn u a).S'.Cl, (I.perIn u a).wt c' • (Formalism.L2.DIV.pairB (K := ℂ) (I.perIn u a).sgT).compl₁₂
      (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT)
        (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) ∘ₗ LinearMap.proj c')
      (LinearMap.proj c' ∘ₗ (I.perIn u a).rd B.fields.emb B.embLL)) z G'
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  erw [Fintype.sum_eq_single c (fun c' hc' => by
    change (I.perIn u a).wt c' * Formalism.L2.DIV.pairB _ (Formalism.L2.Col.polOf _ _ _ (z c')) _ = 0
    rw [hzo c' hc']
    simp only [map_zero, LinearMap.zero_apply, mul_zero])]
  change _ = _ * ((((Nat.card ((I.perIn u a).S'.Stab c) : ℕ) : ℂ)⁻¹) * Formalism.L2.DIV.pairB _ (Formalism.L2.Col.polOf _ _ _ (z c)) (G'.1 c.1 ((I.perIn u a).S'.rep c)))
  rw [hzc, hG' c, ← mul_assoc]
  erw [mul_inv_cancel₀ hne, one_mul]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal


open Classical in
theorem phiT_base_eq_prod : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) (α : Ch j) (γ : Ch (j + 1))
      (z : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E),
      B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z)) =
        (J.map fun i => phiOne (Q j i) (Q (j + 1) i) (rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z))))).prod := by
  intro B X I _ _ l Z u a Ch A hA k _ _ _ _ ι p β Q L hS J hJ j hj α γ z
  have hj0 : j ≤ B.R.m := Nat.le_of_succ_le hj
  obtain ⟨⟨e, he⟩, hS2⟩ := hS
  obtain ⟨hLj, hSj⟩ := hS2 j hj0
  obtain ⟨hLj', hSj'⟩ := hS2 (j + 1) hj
  have hG := GlobalTheory.T.phi_one_eq_one_iff_column_condition B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 (B.fields.conjO (X.piT u))
    (A.p0 j α).1.1.deco.2 (A.p0 (j + 1) γ).1.1.deco.2 (hA.base j hj0 α).2 (hA.base (j + 1) hj γ).2
    (fun P x hx r hr c hc => GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul I l Z u a Ch A hA j hj0 α P x hx r hr c hc)
    (fun P x hx r hr c hc => GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul I l Z u a Ch A hA (j + 1) hj γ P x hx r hr c hc)
    (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)
  have hLoc : ∀ i, (Maps (Q j i) (Q (j + 1) i) (GlobalTheory.FinPl.rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z)))) ↔
      ColCond (e i).1 (B.fields.conjO (X.piT u)) (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)) :=
    fun i => GlobalTheory.T.maps_rd_iff_colCond_toHom (p i) (e i).1 (he i) _ _ (β j i) (β (j + 1) i) (Q j i) (Q (j + 1) i) (L j) (L (j + 1)) _ hLj hLj'
      (hSj i).1 (hSj' i).1 (hSj i).2 (hSj' i).2 z
  have key : (∀ P : (B.primes X).vT u, ColCond P.1 (B.fields.conjO (X.piT u))
      (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)) ↔
      ∀ i ∈ J, Maps (Q j i) (Q (j + 1) i) (GlobalTheory.FinPl.rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z)))) := by
    refine ⟨fun h i _ => (hLoc i).2 (h (e i)), fun h P => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective P
    exact (hLoc i).1 (h i (hJ.all i))
  have hprod : ∀ (J' : List ι) (c : ι → Prop), (J'.map fun i => (if c i then (1 : ℂ) else 0)).prod =
      if ∀ i ∈ J', c i then 1 else 0 := by
    intro J' c
    induction J' with
    | nil => simp
    | cons i J' ih =>
      rw [List.map_cons, List.prod_cons, ih]
      by_cases h : c i <;> simp [h]
  have hv : ∀ x, Formalism.L2.Col.phiT B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 x = 1 ∨
      Formalism.L2.Col.phiT B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 x = 0 := by
    intro x
    unfold Formalism.L2.Col.phiT
    split_ifs <;> simp
  simp only [phiOne]
  rw [hprod]
  split_ifs with hc
  · rw [hG.2 (key.2 hc), map_one]
  · rcases hv (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z) with h1 | h0
    · exact absurd (key.1 (hG.1 h1)) hc
    · rw [h0, map_zero]

end GlobalTheory.PhiOneVal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tupleCharacter_at_basePointDetRoot_rootOfUnity : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ j, j < B.R.m → ∀ i, i ≤ B.R.m → ∀ β, ∃ n : ℕ, 0 < n ∧ A.chr (j + 1) (A.xr i β) ^ n = 1 := by
  first | exact @GlobalTheory.CharRoot.chr_xr_pow_eq_one | exact GlobalTheory.CharRoot.chr_xr_pow_eq_one | (intros; apply GlobalTheory.CharRoot.chr_xr_pow_eq_one <;> assumption)
end
