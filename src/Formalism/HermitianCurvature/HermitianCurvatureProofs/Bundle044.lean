module

public import Formalism.HermitianCurvature.Bundle007
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle039
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle020
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
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section L2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def gramL {ι : Type} (μ : Measure ℂ) (F G : ι × ℂ → ℂ → H) (p q : ι × ℂ) : ℂ :=
  ∫ D, ⟪F p D, G q D⟫_ℂ ∂μ

theorem inner_toLp {μ : Measure ℂ} {f g : ℂ → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ D, ⟪f D, g D⟫_ℂ ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with D h1 h2
  rw [h1, h2]

theorem integrable_inner_of_memLp {μ : Measure ℂ} {f g : ℂ → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun D => ⟪f D, g D⟫_ℂ) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with D h1 h2
  rw [h1, h2]

theorem blockPSD_gramL {ι : Type} (μ : Measure ℂ) (Y : Finset ι) (U A : ι × ℂ → ℂ → H)
    (memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (U (h, x)) 2 μ)
    (memA : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (A (h, x)) 2 μ) (Xs : Finset ℂ) (hXs : ∀ x ∈ Xs, x ≠ 0) :
    KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (gramL μ U U) (gramL μ U A) (gramL μ A A) := by
  have hmem : ∀ p ∈ Y ×ˢ Xs, MemLp (U p) 2 μ ∧ MemLp (A p) 2 μ := by
    intro p hp
    rw [Finset.mem_product] at hp
    have hx := hXs _ hp.2
    exact ⟨memU _ hp.1 _ hx, memA _ hp.1 _ hx⟩
  let v : {x // x ∈ (Y ×ˢ Xs).disjSum (Y ×ˢ Xs)} → Lp H 2 μ := fun x =>
    Sum.elim (fun p => if hp : MemLp (U p) 2 μ then hp.toLp (U p) else 0)
      (fun q => if hq : MemLp (A q) 2 μ then hq.toLp (A q) else 0) x.1
  unfold KB.BlockPSD TB.PSDOn
  open scoped ComplexOrder in
  refine (congrArg Matrix.PosSemidef ?_).mpr (Matrix.posSemidef_gram ℂ v)
  ext i j
  obtain ⟨x, hx⟩ := i
  obtain ⟨y, hy⟩ := j
  rcases x with p | q <;> rcases y with p' | q'
  · have h1 := (hmem p (Finset.inl_mem_disjSum.mp hx)).1
    have h2 := (hmem p' (Finset.inl_mem_disjSum.mp hy)).1
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, dif_pos h1, dif_pos h2, inner_toLp h1 h2, gramL]
  · have h1 := (hmem p (Finset.inl_mem_disjSum.mp hx)).1
    have h2 := (hmem q' (Finset.inr_mem_disjSum.mp hy)).2
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, Sum.elim_inr, dif_pos h1, dif_pos h2,
      inner_toLp h1 h2, gramL]
  · have h1 := (hmem q (Finset.inr_mem_disjSum.mp hx)).2
    have h2 := (hmem p' (Finset.inl_mem_disjSum.mp hy)).1
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, Sum.elim_inr, dif_pos h1, dif_pos h2, gramL]
    rw [← inner_conj_symm, inner_toLp h2 h1]
  · have h1 := (hmem q (Finset.inr_mem_disjSum.mp hx)).2
    have h2 := (hmem q' (Finset.inr_mem_disjSum.mp hy)).2
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inr, dif_pos h1, dif_pos h2, inner_toLp h1 h2, gramL]

end L2

end

end Formalism.FourierDecayAlt.P.PBK
end

section

namespace Formalism.FourierDecayAlt.KB

open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate

noncomputable section

open Classical

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def NhatV (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (L : Fin S.f → ℂ) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, hatB S v ε i 1 (w.1 v) (L v) (C.loc (S.σ v) h) (C.loc (S.σ v) h')

def NstV (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i s : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (t t' : Fin S.f → ℂ) : ℂ :=
  (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w.1 v) (C.loc (S.σ v) h ++ [(s, t v)])
      (C.loc (S.σ v) h' ++ [(s, t' v)])) / (C.Word.size S.P w.1 : ℂ)

end loc

def WaveV : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (X : ℕ → Fin S.f → ℝ),
    (∀ v, WaveLoc S v fun i => X i v) →
    ∀ ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ w ∈ S.base.Wall, S.base.cnt w + C.Kst ≤ S.Ntop →
      ∃ θ : Finset (Fin S.f) → S.W → ℝ, (∀ A, TB.IsProb (S.base.Wb (S.base.cnt w + C.Kst)) (θ A)) ∧
        ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ →
          ∀ (L : Fin S.f → ℂ) (A : Finset (Fin S.f)),
            (∏ v ∈ A, ‖L v‖ ^ C.Kst) * ‖NhatV S ε i w Y κ L‖ ≤
              (∏ v ∈ A, X i v ^ C.Kst) *
                ∑ w' ∈ S.base.Wb (S.base.cnt w + C.Kst), θ A w' * S.base.N0 ε (i - 1) w' Y κ

def LiftV : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (Λ : ℕ → ℕ → Fin S.f → ℝ),
    C.ThmPPos S → (∀ v, LiftLoc S v fun b s => Λ b s v) →
    ∀ ε, 0 < ε → ∀ i s, 1 ≤ s → s ≤ i → i ≤ S.G.r → ∀ w ∈ S.base.Wall, S.base.cnt w + C.Kst ≤ S.Ntop →
      ∃ θ : Finset (Fin S.f) → S.W × S.W → ℝ,
        (∀ A, TB.IsProb (S.base.Wb (S.base.cnt w + C.Kst) ×ˢ S.base.Wb (S.base.cnt w + C.Kst)) (θ A)) ∧
        ∀ (Y : Finset (TB.Pt E)) (κa κw κb : TB.Pt E → TB.Pt E → ℂ),
          (∀ h ∈ Y, TB.level h = i - s) → BlockPSD Y Y κa κw κb →
          ∀ (t t' : Fin S.f → ℂ), (∀ v, t v ≠ 0) → (∀ v, t' v ≠ 0) → ∀ A : Finset (Fin S.f),
            (∏ v ∈ A, ‖(t v)⁻¹ - (t' v)⁻¹‖ ^ C.Kst) * ‖NstV S ε i s w Y κw t t'‖ ≤
              (∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst) *
                ∑ x ∈ S.base.Wb (S.base.cnt w + C.Kst) ×ˢ S.base.Wb (S.base.cnt w + C.Kst), θ A x *
                  (((NstV S ε i s x.1 Y κa t t).re + (NstV S ε i s x.2 Y κb t' t').re) / 2)

end

end Formalism.FourierDecayAlt.KB
end

section

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory

noncomputable section

open Classical

def Lstd (f : ℕ) (R : ℝ) : Submodule ℤ (crystallineComparison.V f) :=
  Submodule.span ℤ (Set.range fun p : Fin f × Bool =>
    (Pi.single p.1 (if p.2 then (R : ℂ) * Complex.I else (R : ℂ)) : crystallineComparison.V f))

def LstdFacts : Prop :=
  ∀ (f : ℕ) (R : ℝ), 0 < R →
    ∃ (_ : DiscreteTopology (Lstd f R)) (_ : IsZLattice ℝ (Lstd f R)),
      ZLattice.covolume (Lstd f R) = R ^ (2 * f) ∧
      ∀ σ : crystallineComparison.V f, σ ∈ crystallineComparison.dualSet (Lstd f R) ↔
        ∀ v, ∃ a b : ℤ, σ v = ((a : ℂ) + (b : ℂ) * Complex.I) / (2 * (R : ℂ))

def LstdSum : Prop :=
  ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ (f : ℕ) (R g : ℝ) (L : Fin f → ℝ), 0 < R → 0 < g → (∀ v, 0 ≤ L v) →
    Summable (fun σ : crystallineComparison.dualSet (Lstd f R) => crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f))) ∧
    ∑' σ : crystallineComparison.dualSet (Lstd f R), crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f)) ≤
      ∏ v, Cs * (1 + (R * L v / g) ^ 2)

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def embV (S : C.HidaSetting E Wp Wq) : E →+ crystallineComparison.V S.f where
  toFun t := fun v => S.σ v t
  map_zero' := by funext v; simp
  map_add' a b := by funext v; simp

def latV (S : C.HidaSetting E Wp Wq) (L : AddSubgroup E) : Submodule ℤ (crystallineComparison.V S.f) :=
  (AddSubgroup.toIntSubmodule L).map (embV S).toIntLinearMap

def thr (S : C.HidaSetting E Wp Wq) (b s : ℕ) (v : Fin S.f) : ℝ :=
  J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s (S.pl v)

end setting

def SizesSup : Prop :=
  ∀ Cs : ℝ, 1 ≤ Cs → ∃ B : ℝ, 1 ≤ B ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
      [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
      [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
      0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E → ∀ b n, 1 ≤ b → 1 ≤ n → (∀ v, 0 < thr S b n v) →
        ∃ R : ℝ, 0 < R ∧
          (∏ _v : Fin S.f, KB.dlB S b n) * (∏ v, Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
            B ^ S.f * S.base.vol b n

def BlockLatV : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
      [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
      [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
      0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E → ∀ b s, 1 ≤ b → 1 ≤ s →
        ∃ (_ : DiscreteTopology (latV S (J.LaB E S.g S.G.r b s)))
          (_ : IsZLattice ℝ (latV S (J.LaB E S.g S.G.r b s))),
          ZLattice.covolume (latV S (J.LaB E S.g S.G.r b s)) = ∏ _v : Fin S.f, KB.dlB S b s ∧
          (∃ (Lm : Submodule ℤ (crystallineComparison.V S.f)) (_ : DiscreteTopology Lm) (_ : IsZLattice ℝ Lm),
            ∀ σ ∈ crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)), (S.g : ℝ) • σ ∈ Lm) ∧
          ∀ Λ : Fin S.f → ℝ, (∀ v, 0 ≤ Λ v ∧ Λ v ≤ thr S b s v) → S.base.vol b s ≤ 1 →
            Summable (fun σ : crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)) =>
              crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) ∧
            ∑' σ : crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)),
              crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) ≤ A ^ S.f

end

end Formalism.FourierDecayAlt.P.PBC
end

section

namespace Formalism.FourierDecayAlt.P.GermRealisation

open Formalism.FourierDecayAlt NumberField

noncomputable section

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def betaL (S : C.HidaSetting E Wp Wq) : ℂ := ((4 * Real.pi / (S.g : ℝ) : ℝ) : ℂ)

theorem psi_betaL (S : C.HidaSetting E Wp Wq) (σ z : ℂ) : G.psi (betaL S) (σ * z) = KB.psiL S σ z := by
  unfold G.psi KB.psiL betaL
  congr 1
  rw [Complex.re_ofReal_mul]
  push_cast
  ring

theorem psi_neg_betaL (S : C.HidaSetting E Wp Wq) (σ z : ℂ) : G.psi (-betaL S) (σ * z) = KB.psiL S (-σ) z := by
  have h : G.psi (-betaL S) (σ * z) = G.psi (betaL S) (-σ * z) := by
    unfold G.psi
    rw [show -betaL S * (σ * z) = betaL S * (-σ * z) by ring]
  rw [h, psi_betaL]

theorem betaL_ne_zero (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) : betaL S ≠ 0 := by
  have hg0 : 0 < S.g := Nat.mul_pos hg1 hg2
  have hg : (0 : ℝ) < (S.g : ℝ) := by exact_mod_cast hg0
  unfold betaL
  exact Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) hg.ne')

end loc

end

end Formalism.FourierDecayAlt.P.GermRealisation
end

section

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Split

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem form_split (μ : Measure (Mt k r)) (l : Fin r) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ)
    (hint : Integrable (fun c' : Cf r l.castSucc =>
      ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue l.castSucc c c'))) :
    form μ l.castSucc x y c =
      ∫ t : ℂ, ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * form μ l.succ x y (Function.update c l t) := by
  set f : Cf r l.castSucc → ℂ := fun c' =>
    ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue l.castSucc c c') with hf
  have hmp := coordinate_split_measurePreserving (r := r) l
  have hform : form μ l.castSucc x y c = ∫ c', f c' := rfl
  have h1 : ∫ c', f c' = ∫ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) := by
    rw [← hmp.integral_comp' (fun p => f ((coordinateSplit (r := r) l).symm p))]
    simp only [MeasurableEquiv.symm_apply_apply]
  have hval : ∀ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) = ((‖p.1‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      (((∏ j, ‖p.2 j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (x a) (y a) (glue l.succ (Function.update c l p.1) p.2)) := by
    intro p
    have hw := weight_coordinate_split (r := r) l ((coordinateSplit (r := r) l).symm p)
    have hg := glue_coordinate_split (r := r) l c ((coordinateSplit (r := r) l).symm p)
    simp only [MeasurableEquiv.apply_symm_apply] at hw hg
    simp only [hf]
    rw [hw, hg, Complex.ofReal_mul, mul_assoc]
  have hF : Integrable (fun p : ℂ × Cf r l.succ => f ((coordinateSplit (r := r) l).symm p)) (volume.prod volume) := by
    have := (hmp.symm.integrable_comp_emb (coordinateSplit (r := r) l).symm.measurableEmbedding (g := f)).mpr hint
    exact this
  rw [hform, h1, show (volume : Measure (ℂ × Cf r l.succ)) = volume.prod volume from rfl,
    integral_prod _ hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [hval]
  rw [integral_const_mul]
  rfl

end Split

end Formalism.FourierDecayAlt.P5.HerA
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def GTHyp (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) : Prop :=
  Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' ∧ 2 ≤ P.k ∧ CSec P.k P.r Bs.z Bs.z' Bs.μsec ∧
    Q.IsActualLevel X d.L ∧ Fr.IsStarLevel d.L ∧ d.Rel ∧ ∀ Y : ℂ, X.QQ Y = d.QQ Y

def FnF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
    trR P Bs e (d.L.ζ.1 Φ) = MA.actA P (MA.zA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.ζi.1 Φ) = MA.actA P (MA.ziA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.ζb.1 Φ) = MA.actA P (MA.zbA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.ζbi.1 Φ) = MA.actA P (MA.zbiA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.GG.1 Φ) = MA.actA P (MA.ggA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.GGi.1 Φ) = MA.actA P (MA.ggiA P (MA.DQ P)) (trR P Bs e Φ)

def KapF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
    trR P Bs e ((d.κ f).1 Φ) = MA.actA P (MA.kap P (MA.DQ P) f) (trR P Bs e Φ)

def NabF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
    trR P Bs e (d.L.nab.1 Φ) = MA.actA P (MA.nabA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.nabs.1 Φ) = MA.actA P (MA.nabsA P (MA.DQ P)) (trR P Bs e Φ)

def SSF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
    trR P Bs e ((d.SS l).1 Φ) = MA.actA P (MA.SS P (MA.DQ P) l) (trR P Bs e Φ) ∧
    trR P Bs e ((star (d.SS l)).1 Φ) = MA.actA P (star (MA.SS P (MA.DQ P) l)) (trR P Bs e Φ)

end preds

def GTFn : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), FnF P Bs d e

def GTKap : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧ KapF P Bs d e

def GTConn : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∃ e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e' ∧ KapF P Bs d e' ∧ NabF P Bs d e'

def GTSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∃ e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e' ∧ KapF P Bs d e' ∧ NabF P Bs d e' ∧ SSF P Bs d e'

def GenTransferOfCut : Prop := GTFn → GTKap → GTConn → GTSS → GenTransfer

theorem genTransfer_of_cut : GenTransferOfCut := by
  intro hFn hKap hConn hSS Wp Wq _ _ _ _ _ _ P Bs hpl hk hcs X d hL hS hR hQ
  have hyp : GTHyp P Bs X d := by
    unfold GTHyp
    exact ⟨hpl, hk, hcs, hL, hS, hR, hQ⟩
  obtain ⟨e₀, hf₀, hk₀⟩ := hKap Wp Wq P Bs X d hyp
  obtain ⟨e₁, hf₁, hk₁, hn₁⟩ := hConn Wp Wq P Bs X d hyp e₀ hf₀ hk₀
  obtain ⟨e, hf, hke, hne, hse⟩ := hSS Wp Wq P Bs X d hyp e₁ hf₁ hk₁ hn₁
  refine ⟨e, hf, fun Φ => ?_⟩
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := hFn Wp Wq P Bs X d hyp e Φ
  obtain ⟨b₁, b₂⟩ := hne Φ
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, b₁, b₂, fun f => hke f Φ, fun l hl => (hse l hl Φ).1,
    fun l hl => (hse l hl Φ).2⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

namespace Formalism.FourierDecayAlt.P

theorem operators_commute_translations' : Formalism.FourierDecayAlt.C3.OperatorsCommuteTranslations := operators_commute_translations

end Formalism.FourierDecayAlt.P
end
