module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle732
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle643
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle734
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsOfFlatMapWeilActionNeZero
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.SplitX

variable {D : D7}

private theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem mem_of_latV_top {S : HSp D} {L : Lat S} (hL : Submodule.IsFullLattice D.host.E L) (r : Fin S.rank → D.host.E)
    (h : (fun i => pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * r i)) ∈ latV S L fun _ => True) : r ∈ L := by
  have h1 := GlobalTheory.LatVHat.latV_mem_hatL D S L _ _ h
  have e : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * r i)))) =
      fun i => Formalism.L2.Col.iA D.host.F D.host.E (r i) := by
    funext i
    rw [GlobalTheory.FinPlLoc.finPart_pair, one_mul]
    rfl
  rw [e] at h1
  let : Submodule.IsFullLattice D.host.E L := hL
  exact (GlobalTheory.CongStdLoc.incl_mem_hatL_iff (Submodule.IsLattice.fg D.host.E L) Submodule.IsFullLattice.span_eq_top r).1 h1

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {L : Lat V} {L₀ : Lat V₀}

theorem proj_latV_at {v : GlobalTheory.FinPl.Pl D} (hm : MonoAt d L L₀ v) {y : Fin V.rank → AE D} (hy : y ∈ latV V L (· = v)) :
    rat (d.e * d.qX) *ᵥ y ∈ latV V L (· = v) := by
  have h := ((hm y).1 hy).1
  have e : rat (d.e * d.qX) *ᵥ y = ∑ i, GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) := by
    rw [show rat (d.e * d.qX) = d.jX ⬝ d.pX from rat_mul _ _, ← Matrix.mulVec_mulVec]
    funext k
    rw [Finset.sum_apply]
    simp only [GlobalTheory.FinPl.colMul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact sum_mem fun i _ => h i

theorem proj_mem (hL : Submodule.IsFullLattice D.host.E L) (hm : ∀ v, MonoAt d L L₀ v) (x : Fin V.rank → D.host.E)
    (hx : x ∈ L) : (d.e * d.qX) *ᵥ x ∈ L := by
  apply mem_of_latV_top hL
  have hy : (fun i => pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * x i)) ∈ latV V L fun _ => True :=
    AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact (v.adicCompletionIntegers D.host.F).one_mem,
      fun v hv => (hv trivial).elim, 1, rfl, x, hx, rfl⟩
  have hz : rat (d.e * d.qX) *ᵥ (fun i => pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * x i)) ∈
      latV V L fun _ => True := by
    refine (GlobalTheory.FinPlLoc.part_lat _ V L _ hL.toIsLattice).2 ⟨fun i => mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy) i, fun v _ e he => ?_⟩
    rw [← Matrix.mulVec_smul]
    exact proj_latV_at d (hm v) (GlobalTheory.FinPlLoc.smul_latV v he hy)
  rwa [GlobalTheory.SeeSaw.SplitLat.rat_mulVec_gen] at hz

end GlobalTheory.AscFin.SplitX

namespace GlobalTheory.AscFin.SplitX

variable {D : D7}

theorem hatMx_mul {m n : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)} (π : Matrix (Fin n) (Fin n) D.host.E)
    (hM : ∀ x ∈ M, x * π ∈ M) {z : Mx D m n} (hz : z ∈ hatMx M) : z ⬝ rat π ∈ hatMx M := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, x * π, hM x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (pairA D.host.F 0 α ⊗ₜ[D.host.F] x i k) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] π k j) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.neg_mul]; exact neg_mem ha

theorem smul_homLat_mul {m n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (π : Matrix (Fin n) (Fin n) D.host.E) (hπ : ∀ y ∈ Λ, π *ᵥ y ∈ Λ) :
    ∀ x ∈ I • homLat Λ Λ', x * π ∈ I • homLat Λ Λ' := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [Matrix.smul_mul]
    refine Submodule.smul_mem_smul hr (fun y hy => ?_)
    rw [← Matrix.mulVec_mulVec]
    exact hn _ (hπ y hy)
  · rw [Matrix.add_mul]; exact add_mem hx hy

end GlobalTheory.AscFin.SplitX


open GlobalTheory.AscFin.SplitX in
theorem GlobalTheory.AscFin.SplitX.latRow_extX : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), (F.dJ (σ + 1) h).extX _ (u ⬝ (F.dJ (σ + 1) h).jX) ∈ latRow G (2 * σ + 2) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h u hu
  have hmono : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => (((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF).2.1 (σ + 1) h).2.1 v).2
  have hV : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (G.sp.V_is (2 * (σ + 1) + 1) 0 (by omega) (by omega) (Nat.zero_le _)).sd
  have hW : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) (by omega) (Nat.zero_le _)).sd
  have hπ := proj_mem (F.dJ (σ + 1) h) (selfDual_isFullLattice _ _ hV) hmono
  have hext : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ (F.dJ (σ + 1) h).jX) =
      u ⬝ rat ((F.dJ (σ + 1) h).e * (F.dJ (σ + 1) h).qX) := by
    rw [HypDec.extX_apply, rat_mul, Matrix.mul_assoc]; rfl
  rw [hext]
  refine ⟨GlobalTheory.AscFinWit.latO_right (GlobalTheory.ChiGrid.isSelfDualC_neg hV) (GlobalTheory.ChiGrid.isSelfDualC_neg hV) hW _ hπ hu.1,
    fun e he => ?_⟩
  rw [← Matrix.smul_mul]
  exact hatMx_mul _ (smul_homLat_mul _ _ hπ) (hu.2 e he)
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PcBFDual

variable {D : D7}

section Proj

variable {T : HSp D} {Λ : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop} (M : Mx D T.rank T.rank)

theorem mulVec_latV (hM : ∀ v, P v → ∀ y ∈ latV T Λ (· = v), M *ᵥ y ∈ latV T Λ (· = v))
    (hΛ : Submodule.IsLattice D.host.E Λ) {y : Fin T.rank → AE D} (hy : y ∈ latV T Λ P) : M *ᵥ y ∈ latV T Λ P := by
  refine (GlobalTheory.FinPlLoc.part_lat P T Λ _ hΛ).2 ⟨GlobalTheory.FinPl.ExtZeroAt.mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact hM v hv _ (GlobalTheory.FinPlLoc.smul_latV v he hy)

theorem smul_mem_latA_idLat (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) {a s : D.host.E} (ha : a ∈ D.host.AA) (hs : s ∈ I)
    {w : Fin T.rank → AE D} (hw : w ∈ latV T Λ P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * s)) • w ∈ latA T (idLat I Λ) P := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, s • x, Submodule.subset_span ⟨s, hs, x, hx, rfl⟩, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz



theorem mulVec_latA_idLat (hM : ∀ v, P v → ∀ y ∈ latV T Λ (· = v), M *ᵥ y ∈ latV T Λ (· = v))
    (hΛ : Submodule.IsLattice D.host.E Λ) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) {z : Fin T.rank → AE D}
    (hz : z ∈ latA T (idLat I Λ) P) : M *ᵥ z ∈ latA T (idLat I Λ) P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    have key : ∀ x ∈ Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ Λ, z = s • y}, ∀ c : 𝓞 D.host.E,
        M *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • x) i)) ∈ latA T (idLat I Λ) P := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨s, hs, y, hy, rfl⟩ := hx
        intro c
        have hyv : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * y i)) ∈ latV T Λ P :=
          AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, y, hy, rfl⟩
        have e : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • s • y) i)) =
            ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * (c • s))) • (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * y i)) := by
          funext i
          rw [← smul_assoc]
          simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc]
        rw [e, Matrix.mulVec_smul]
        exact smul_mem_latA_idLat I ha (Submodule.smul_mem _ c hs) (mulVec_latV M hM hΛ hyv)
      | zero =>
        intro c
        have e : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • (0 : Fin T.rank → D.host.E)) i)) = 0 := by
          funext i; simp only [smul_zero, Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
        rw [e, Matrix.mulVec_zero]; exact zero_mem _
      | add x x' _ _ h h' =>
        intro c
        have e : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • (x + x')) i)) =
            (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • x) i)) +
              (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • x') i)) := by
          funext i; simp only [smul_add, Pi.add_apply, mul_add, TensorProduct.tmul_add]
        rw [e, Matrix.mulVec_add]; exact add_mem (h c) (h' c)
      | smul c' x _ h =>
        intro c
        rw [smul_smul]
        exact h (c * c')
    have := key x hx 1
    simpa only [one_smul] using this
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end Proj

section Split

theorem projY_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : GlobalTheory.FinPl.Pl D}
    (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) : (d.jY ⬝ d.pY) *ᵥ y ∈ latV S L (· = v) := by
  have e : (d.jY ⬝ d.pY) *ᵥ y = ∑ i, GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ y) i) := by
    rw [← Matrix.mulVec_mulVec]
    funext k
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact sum_mem fun i _ => ((h y).1 hy).2.1 i

theorem projX_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : GlobalTheory.FinPl.Pl D}
    (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) : (d.jX ⬝ d.pX) *ᵥ y ∈ latV S L (· = v) := by
  have e : (d.jX ⬝ d.pX) *ᵥ y = ∑ i, GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) := by
    rw [← Matrix.mulVec_mulVec]
    funext k
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact sum_mem fun i _ => ((h y).1 hy).1 i

theorem extend_mem_lattice_iff {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W}
    (hV : IsSelfDualC V LV) (hV₀ : IsSelfDualC V₀ LV₀) (hW : IsSelfDualC W LW) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hm : ∀ v, P v → MonoAt d LV LV₀ v) (w : WO V₀ W) :
    d.ext0 W w ∈ latO V W (LV : Set _) (LW : Set _) P ↔ w ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) P := by
  constructor
  · intro hw
    have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
    refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D V₀ W LV₀ LW hV₀ hW P _).2 ⟨?_, fun y hy => ?_⟩
    · have := GlobalTheory.AscFinWit.mxAt_mul' hx d.j0
      rwa [HypDec.matrixExtendByZero_apply, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one] at this
    · have h2 := GlobalTheory.FinPl.LatMem.latO_maps hV hw (GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace d hV.1 hm hy)
      rwa [HypDec.matrixExtendByZero_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one] at h2
  · intro hw
    refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D V W LV LW hV hW P _).2
      ⟨GlobalTheory.AscFinWit.mxAt_mul' (GlobalTheory.FinPl.LatMem.latO_mxAt hw) _, fun y hy => ?_⟩
    rw [HypDec.matrixExtendByZero_apply, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.FinPl.LatMem.latO_maps hV₀ hw (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hV₀.1 hm hy)

theorem left_mem {S W : HSp D} {LS : Lat S} {Λ : Lat W} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hS : IsSelfDualC S LS) (hW : IsSelfDualC W (idLat I Λ)) (hΛ : Submodule.IsLattice D.host.E Λ) (M : Mx D W.rank W.rank)
    (hM : ∀ v, P v → ∀ y ∈ latV W Λ (· = v), M *ᵥ y ∈ latV W Λ (· = v)) {u : WO S W}
    (hu : u ∈ latO S W (LS : Set _) (idLat I Λ : Set _) P) : M ⬝ u ∈ latO S W (LS : Set _) (idLat I Λ : Set _) P := by
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S W LS _ hS hW P _).2
    ⟨GlobalTheory.AscFinWit.mxAt_mul _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu), fun y hy => ?_⟩
  show (M * u) *ᵥ y ∈ _
  rw [← Matrix.mulVec_mulVec]
  exact mulVec_latA_idLat M hM hΛ I (GlobalTheory.FinPl.LatMem.latO_maps hS hu hy)

end Split

end GlobalTheory.PcBFDual

namespace GlobalTheory.PcBFDual

theorem dualB : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    (∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ (pcBF W F ρ h).B₁ ↔ ∀ η ∈ (pcBF W F ρ h).B₂,
      W.ψ (symplO (F.V₀ ρ) _ ((F.dJ ρ h).incX _ ξ) ((F.dJ ρ h).incY _ η)) = 1)) ∧
    ∀ η, MxAt (fun _ => True) η → (η ∈ (pcBF W F ρ h).B₂ ↔ ∀ ξ ∈ (pcBF W F ρ h).B₁,
      W.ψ (symplO (F.V₀ ρ) _ ((F.dJ ρ h).incX _ ξ) ((F.dJ ρ h).incY _ η)) = 1) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sd : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → IsSelfDualC (G.V X) (G.Λ X) :=
    fun X h1 h2 => (G.isV h1 h2).sd
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    sd _ ⟨h, Nat.zero_le _⟩ (fun j e => by cases e)
  have hΛ : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    sd _ ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e)
  have hV₀ : IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) := (I.2.1 ρ h).1
  have hW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0))) :=
    (I.1 (2 * ρ + 1) (by omega)).2.2.2
  have hmV : ∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := fun v => ((I.2.1 ρ h).2.1 v).1
  have hmW : ∀ v, MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    fun v => ((I.2.1 ρ h).2.1 v).2
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hB : ∀ w, (F.dB ρ h).ext0 _ w ∈ latBig G (2 * ρ + 1) ↔
      w ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
        (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) fun _ => True :=
    fun w => extend_mem_lattice_iff (F.dB ρ h) hV hV₀ hW (fun v _ => hmV v) w
  have tY : ∀ u ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
      (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True),
      (F.dJ ρ h).incY _ ((F.dJ ρ h).pY ⬝ u) ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
        (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True) := fun u hu => by
    rw [HypDec.incY_apply, ← Matrix.mul_assoc]
    exact left_mem hV₀ hW hΛ.1 _ (fun v _ y hy => projY_mem _ (hmW v) hy) hu
  have tX : ∀ u ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
      (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True),
      (F.dJ ρ h).incX _ ((F.dJ ρ h).pX ⬝ u) ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
        (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True) := fun u hu => by
    rw [HypDec.incX_apply, ← Matrix.mul_assoc]
    exact left_mem hV₀ hW hΛ.1 _ (fun v _ y hy => projX_mem _ (hmW v) hy) hu
  refine ⟨fun ξ hξ => ?_, fun η hη => ?_⟩
  · refine (hB ((F.dJ ρ h).incX _ ξ)).trans ?_
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hV₀ hW _ _ (GlobalTheory.AscFinWit.mxAt_mul (F.dJ ρ h).jX hξ)).trans ?_
    refine ⟨fun H η hη => H _ ((hB ((F.dJ ρ h).incY _ η)).1 hη), fun H u hu => ?_⟩
    exact (congrArg W.ψ (GlobalTheory.AscFinWit.symplO_incX (F.dJ ρ h) _ ξ u)).trans (H _ ((hB ((F.dJ ρ h).incY _ _)).2 (tY u hu)))
  · refine (hB ((F.dJ ρ h).incY _ η)).trans ?_
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hV₀ hW _ _ (GlobalTheory.AscFinWit.mxAt_mul (F.dJ ρ h).jY hη)).trans ?_
    refine ⟨fun H ξ hξ => (GlobalTheory.AscFinWit.psi_swap _ _).1 (H _ ((hB ((F.dJ ρ h).incX _ ξ)).1 hξ)), fun H u hu => ?_⟩
    exact (congrArg W.ψ (GlobalTheory.AscFinWit.symplO_incY (F.dJ ρ h) _ η u)).trans
      ((GlobalTheory.AscFinWit.psi_swap _ _).1 (H _ ((hB ((F.dJ ρ h).incX _ _)).2 (tX u hu))))

end GlobalTheory.PcBFDual
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.GoodFB

theorem mxAt_mul {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {a : Mx D m n} (ha : MxAt P a) (b : Mx D n k) :
    MxAt P (a * b) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem mxAt_mul_left {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (b : Mx D m n) {a : Mx D n k} (ha : MxAt P a) :
    MxAt P (b * a) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (ha l j)

theorem goodAt_stdAt_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.core (2 * σ + 3))) (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v ∧ StdAt (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  intro D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hQ T L μ0 hL sc G W M hM F hF
  have t1 := GlobalTheory.T.psi_primitive_standardFrames_fourierJacobiLevel D hQ T L μ0 hL sc G W M hM F hF (σ + 1) h v hv
  have t2 := GlobalTheory.T.fourierJacobiStep_basePoint_columns_primitive D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  have r1 := GlobalTheory.T.depthLatticeGridRow_local_eq_completed_homLattice D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv
  have r2 := GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v
  have r3 := GlobalTheory.T.selfDualHomLatticeModulusShift_local_eq_latO D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv
  obtain ⟨-, hb, -⟩ := I
  have hbσ := hb σ h'
  have hbσ1 := hb (σ + 1) h
  refine ⟨⟨?_, ?_, ?_, hbσ.1, (hbσ1.2.1 v).2, (hbσ.2.1 v).1, t1, t2⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (G.sp.V_is (2 * σ + 3) 0 (by omega) (by omega) (by omega)).sd
  · exact (G.sp.P_is (2 * σ + 3) (by omega)).sd
  · exact (G.sp.V_is (2 * σ + 2) 0 (by omega) (by omega) (by omega)).sd
  · intro a ha
    exact r1 _ (mxAt_mul ha _)
  · intro a ha
    obtain ⟨⟨ε, hεε, -, hεi, -, hεoff⟩, -⟩ := GlobalTheory.FinPl.localComponents D (· = v)
    refine ⟨ε • a, fun i j => ?_, ?_⟩
    · rw [hεoff]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [mul_sub, ← mul_assoc, hεε, sub_self]
    · have := r2 ε hεi _ ha
      have e : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (ε • a) =
          ε • (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) a := by
        rw [HypDec.extX_apply, HypDec.extX_apply, Matrix.smul_mul]
      rw [e]
      exact this
  · intro ξ hξ
    exact r3 _ (mxAt_mul (mxAt_mul_left _ hξ) _)

end GlobalTheory.AscFin.GoodFB
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.unfoldingConditions_of_flatMap_weilAction_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, ∀ h, flatS dV dW s (rat x₀) y (s.om (1, h) Φ) ≠ 0 → Cond dW p (rat x₀) y ψ (fun _ => True) h := by
  first | exact @GlobalTheory.AscFinCond.cond_of_flatS_ne | exact GlobalTheory.AscFinCond.cond_of_flatS_ne | (intros; apply GlobalTheory.AscFinCond.cond_of_flatS_ne <;> assumption)
end
