module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle198
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivPadicOfResidueCardUniformizerStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle141
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFundamentalDomainFlagUnipotentCoords
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle166
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle168
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ColSplitA

variable {D : D7}

theorem mulVec_mem_latA {S T : HSp D} {L : Lat S} {L' : Lat T} {P : Pl D → Prop} (M : Mx D T.rank S.rank)
    (hM : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV T L' P) {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) :
    M *ᵥ z ∈ latA T L' P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : M *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (M *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact VacFlat.smul_mem_latA ha (hM u hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end GlobalTheory.FinPl.ColSplitA

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open GlobalTheory.IwaPlace.BuildQ in

theorem _root_.GlobalTheory.T.exists_unitarySupportedAtPlace_of_dual_isotropic_frames : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (α β : Fin ρ → AE D) (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i, α i ∈ idAt D (· = v)) → (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i j, c' i j ∈ idAt D (· = v)) → adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) → adj c' * (gA S * c') = 0 → ∃ q ∈ grpAt S (· = v), mt S q * d.jX = d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)) ∧ (∀ i, mt S q *ᵥ colMul d.jX i (α i) = fun k => (d.jX * b) k i) ∧ (∀ i, mt S q *ᵥ colMul d.jY i (cA D (β i)) = fun k => c' k i) := by
  intro D S S₀ ρ d v ε hεε hεc _ hε α β b c' hα hβ hαβ hb hc' H1 H2
  have mulVec_colMul {m n k : ℕ} (M : Mx D m n) (X : Mx D n k) (i : Fin k) (a : AE D) :
      M *ᵥ colMul X i a = fun r => a * (M * X) r i := by
    funext r
    simp only [colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have mul_tail₃ {a m n p k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {C : Mx D a p}
      (h : A * (B * B') = C) (X : Mx D p k) :
      A * (B * (B' * X)) = C * X := by
    rw [← h]
    simp only [Matrix.mul_assoc]
  have mul_tail₄ {a m n p q k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {B'' : Mx D p q} {C : Mx D a q}
      (h : A * (B * (B' * B'')) = C) (X : Mx D q k) :
      A * (B * (B' * (B'' * X))) = C * X := by
    rw [← h]
    simp only [Matrix.mul_assoc]
  have gXX {k : ℕ} (X : Mx D ρ k) : adj d.jX * (gA S * (d.jX * X)) = 0 := by
    rw [mul_tail₃ d.gram_XX, Matrix.zero_mul]
  have gYX {k : ℕ} (X : Mx D ρ k) : adj d.jY * (gA S * (d.jX * X)) = X := by
    rw [mul_tail₃ d.gram_YX, Matrix.one_mul]
  have g0X {k : ℕ} (X : Mx D ρ k) : adj d.j0 * (gA S * (d.jX * X)) = 0 := by
    rw [mul_tail₃ d.gram_0X, Matrix.zero_mul]
  have kill_left {ε : AE D} (hεε : ε * ε = ε) {m n k : ℕ} {x : Mx D m n} (hx : ε • x = x) (X : Mx D n k) :
      (1 - ε) • (x * X) = 0 := by
    rw [← Matrix.smul_mul, ← hx, smul_smul, one_sub_mul_self hεε, zero_smul, Matrix.zero_mul]
  have kill_mid₂ {ε : AE D} (hεε : ε * ε = ε) {m n p q k : ℕ} {x : Mx D p q} (hx : ε • x = x)
      (A : Mx D m n) (B : Mx D n p) (X : Mx D q k) : (1 - ε) • (A * (B * (x * X))) = 0 := by
    rw [← Matrix.mul_smul, ← Matrix.mul_smul, kill_left hεε hx, Matrix.mul_zero, Matrix.mul_zero]
  have absorb_mul {ε : AE D} {m n k : ℕ} {x : Mx D m n} (hx : ε • x = x) (X : Mx D n k) :
      x * (ε • X) = x * X := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, hx]
  have smul_sub_one {ε : AE D} (M : Mx D S.rank S.rank)
      (hX : ε • (M * d.jX - d.jX) = M * d.jX - d.jX) (h0 : ε • (M * d.j0 - d.j0) = M * d.j0 - d.j0)
      (hY : ε • (M * d.jY - d.jY) = M * d.jY - d.jY) : ε • (M - 1) = M - 1 := by
    have e : M - 1 = (M * d.jX - d.jX) * d.pX + (M * d.j0 - d.j0) * d.p0 + (M * d.jY - d.jY) * d.pY := by
      have e1 : M - 1 = (M - 1) * (d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY) := by
        rw [d.sum_eq_one, Matrix.mul_one]
      rw [e1]
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
    rw [e, smul_add, smul_add, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, hX, h0, hY]
  have hb' : ε • b = b := smul_eq_of_mem hε hb
  have hc : ε • c' = c' := smul_eq_of_mem hε hc'
  have hαε : ∀ i, ε * α i = α i := fun i => (hε _).1 (hα i)
  have hβε : ∀ i, ε * β i = β i := fun i => (hε _).1 (hβ i)
  have hcA1 : cA D (1 - ε) = 1 - ε := by rw [map_sub, map_one, hεc]
  have h : HypDec.Images S S₀ (d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))
      (d.j0 - (d.jX * b) * (adj c' * (gA S * d.j0)))
      (c' * Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [adj_mul, Matrix.mul_assoc, gXX, Matrix.mul_zero]
    · simp only [adj_add, adj_mul, adj_smul, adj_diagonal, cA_cA, hcA1, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_assoc]
      simp only [mul_tail₃ H2, Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul, d.gram_YY,
        smul_zero, kill_mid₂ hεε hc, kill_left hεε (diag_absorb hαε), add_zero, Matrix.zero_mul]
    · simp only [adj_add, adj_mul, adj_smul, adj_diagonal, cA_cA, hcA1, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_assoc]
      simp only [mul_tail₄ H1, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul,
        gYX, d.gram_YX, kill_left hεε (diag_absorb hαε), kill_left hεε hb', add_zero, smul_smul]
      rw [zero_add, Matrix.diagonal_mul_diagonal, one_sub_sq hεε]
      rw [diag_const hαβ, smul_smul, hεε, ← add_smul, add_sub_cancel, one_smul]
    · simp only [adj_sub, adj_mul, adj_gA, adj_adj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
        d.gram_00, d.wittDecomp_gram_X_anisotropic, gXX, g0X, Matrix.mul_zero, sub_zero]
    · simp only [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, gXX, g0X, Matrix.mul_zero, sub_zero]
    · have adjH1 : adj b * (adj d.jX * (gA S * c')) = ε • (1 : Mx D ρ ρ) := by
        simpa only [adj_mul, adj_gA, adj_adj, adj_smul, adj_one, hεc, Matrix.mul_assoc] using congrArg adj H1
      simp only [adj_sub, adj_mul, adj_gA, adj_adj, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc]
      rw [mul_tail₄ adjH1, Matrix.smul_mul, Matrix.one_mul, absorb_mul hc, sub_self, zero_add]
      simp only [Matrix.mul_smul, d.gram_0Y, d.gram_XY, Matrix.mul_one, smul_zero,
        kill_mid₂ hεε hc, sub_zero]
  have hjb : ε • (d.jX * b) = d.jX * b := by rw [← Matrix.mul_smul, hb']
  have hE : d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ))
      = (d.jX * b) * Matrix.diagonal β + (1 - ε) • d.jX := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
  refine ⟨d.ofImages _ _ _ h, ?_, d.ofImages_jX h, fun i => ?_, fun i => ?_⟩
  · have key := smul_sub_one (ε := ε) (Formalism.L2.Theta.mt S (d.ofImages _ _ _ h))
      (by rw [d.ofImages_jX h, hE]; exact smul_shift hεε (by rw [← Matrix.smul_mul, hjb]) _)
      (by rw [d.wittDecomp_ofImages_inclAnisotropic h, sub_sub_cancel_left, smul_neg, ← Matrix.smul_mul, hjb])
      (by rw [d.ofImages_jY h]; exact smul_shift hεε (by rw [← Matrix.smul_mul, hc]) _)
    refine (mem_congGrp_iff S _ _).2 fun i j => (hε _).2 ?_
    exact congrFun (congrFun key i) j
  · rw [mulVec_colMul, d.ofImages_jX h, hE]
    funext k
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    exact scalar_X (hαε i) (hαβ i) (congrFun (congrFun hjb k) i)
  · rw [mulVec_colMul, d.ofImages_jY h]
    funext k
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    refine scalar_X ?_ ?_ (congrFun (congrFun hc k) i)
    · rw [← hεc, ← map_mul, hβε]
    · rw [← map_mul, mul_comm, hαβ, hεc]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.GluedInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_sec' (p : SplitPt D k) {S : HSp D} (h : GA D S) (u : Fin S.rank → k) :
    mt S h *ᵥ (fun i => p.sec (u i)) = fun i => p.sec (((mt S h).map p.pr *ᵥ u) i) := by
  funext i

  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FrameLat.sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, FrameLat.e_mul_sec]

theorem cAe_smul (p : SplitPt D k) {r : ℕ} (z : Fin r → AE D) :
    cA D p.e • z = fun i => cA D (p.sec (p.pr (cA D (z i)))) := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul, p.sec_pr, map_mul, cA_cA]

def form (p : SplitPt D k) (S : HSp D) (x w : Fin S.rank → k) : k :=
  ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * w j

theorem form_eq (p : SplitPt D k) (S : HSp D) (x : Fin S.rank → k) (c : Fin S.rank → D.host.E) :
    form p S x (fun j => p.pr (cA D (incA D (c j)))) =
      x ⬝ᵥ fun i => p.pr (incA D ((star (S.gram *ᵥ c)) i)) := by
  unfold form
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1

  simp only [Pi.star_apply, Matrix.mulVec, dotProduct, star_sum, map_sum, star_mul', map_mul]
  rfl

theorem row_orth {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    star (S.gram *ᵥ vecB o ζ) ᵥ* o.iA = 0 ∧ star (S.gram *ᵥ vecB o ζ) ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
  have hr : star (S.gram *ᵥ vecB o ζ) = star ζ ᵥ* (o.iBᴴ * S.gram) := by
    rw [vecB, Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_mul, gram_conjTranspose]
  rw [hr]
  constructor
  · rw [Matrix.vecMul_vecMul, o.orth, Matrix.vecMul_zero]
  · rw [vecB, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem form_frame (p : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n]
    (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (hs : IsSumFrame B.o B.ζ β β₀) (y : n ⊕ Fin 1 → k) :
    form p B.V₀ (β₀.b *ᵥ y) (fun j => p.pr (cA D (ratV (vecB B.o B.ζ) j))) =
      p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * y (Sum.inr 0) := by
  obtain ⟨h1, h2⟩ := row_orth B.o B.ζ
  set ι : D.host.E →+* k := p.pr.comp (incA D) with hι
  set r := star (B.V₀.gram *ᵥ vecB B.o B.ζ) with hr
  change form p B.V₀ _ (fun j => p.pr (cA D (incA D (vecB B.o B.ζ j)))) = _
  rw [form_eq, ← hr, hs, Matrix.fromCols_mulVec, add_dotProduct]
  have hA : (⇑ι ∘ r) ᵥ* (B.o.jA.map p.pr) = 0 := by
    funext a
    have hm : B.o.jA.map p.pr = B.o.iA.map ι := by
      rw [OrthDec.jA, rat, Matrix.map_map]; rfl
    rw [hm, ← RingHom.map_vecMul, h1]
    simp
  have e1 : ((B.o.jA.map p.pr * β.b) *ᵥ (y ∘ Sum.inl)) ⬝ᵥ (fun i => p.pr (incA D (r i))) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
    change ((⇑ι ∘ r) ᵥ* (B.o.jA.map p.pr) ᵥ* β.b) ⬝ᵥ _ = 0
    rw [hA, Matrix.zero_vecMul, zero_dotProduct]
  have e2 : (replicateCol (Fin 1) (fun i => p.pr (ratV (vecB B.o B.ζ) i)) *ᵥ (y ∘ Sum.inr)) =
      y (Sum.inr 0) • (⇑ι ∘ vecB B.o B.ζ) := by
    funext i
    simp [Matrix.mulVec, dotProduct, replicateCol, mul_comm, ratV, hι]
  rw [e1, zero_add, e2, smul_dotProduct, smul_eq_mul, mul_comm]
  congr 1
  change (⇑ι ∘ vecB B.o B.ζ) ⬝ᵥ (⇑ι ∘ r) = ι _
  rw [← RingHom.map_dotProduct, dotProduct_comm, h2]

end GlobalTheory.FinPl.GluedInt


open GlobalTheory.FinPl.GluedInt in
theorem GlobalTheory.FinPl.glued_last_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P → ∀ γ ∈ grpAt B.V₀ (· = p.v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → ∀ x : n ⊕ Fin 1 → k, mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) → (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] := by
  intro D k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hsd hg γ _ hyp x hx
  have hu := hg.unit.2 B.V₀ L₀
  have hz := cAe_smul p (ratV (vecB B.o B.ζ))
  set zk : Fin B.V₀.rank → k := fun j => p.pr (cA D (ratV (vecB B.o B.ζ) j)) with hzk
  have hN : ∀ y : n ⊕ Fin 1 → k, form p B.V₀ (β₀.b *ᵥ y) zk =
      p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * y (Sum.inr 0) := form_frame p B β β₀ hg.sum
  have hvN := hg.norm
  set N := p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) with hNdef
  have hq0 : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact q.ne_zero
  have hmem : (fun i => cA D (p.sec (zk i))) ∈ latV B.V₀ L₀ (· = p.v) := by
    rw [FrameLat.csec_mem_iff hsd]
    intro x' hx'
    have hb : β₀.b *ᵥ (β₀.b' *ᵥ x') = x' := by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]
    have hy : β₀.b' *ᵥ x' ∈ gluedS q 1 P.ker P.vec := (hg.lat _).2 (by rw [hb]; exact hx')
    rw [← gluedLat_one, mem_gluedLat] at hy
    obtain ⟨s, -, hs⟩ := hy
    have h0 := (hs 0).2.1 rfl
    change form p B.V₀ x' zk ∈ 𝒪[k]
    rw [← hb, hN, h0, Valuation.mem_integer_iff, map_mul, map_mul, hvN, Unif.inv, map_inv₀, ← mul_assoc,
      mul_inv_cancel₀ hq0, one_mul]
    exact s.2
  have hA : cA D p.e • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) := by rw [hu, hz]; exact hmem
  have h1 := hyp (cA D p.e) hA
  rw [hu, hz, FrameLat.mt_csec] at h1
  rw [mt_sec' p] at hx
  have h2 := (FrameLat.csec_mem_iff hsd _).1 h1 _ hx
  rw [FrameLat.pairing_inv] at h2
  change form p B.V₀ (β₀.b *ᵥ x) zk ∈ 𝒪[k] at h2
  rw [hN, Valuation.mem_integer_iff, map_mul, hvN] at h2
  rw [Valuation.mem_integer_iff, map_mul]
  exact h2
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
open IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPl.SplitQT

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke

def intEquiv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletionIntegers F ≃+* 𝒪[Fv F v] where
  toFun x := ⟨x.1, (GlobalTheory.FinPl.SplitPoint.mem_integer_iff F v x.1).2 x.2⟩
  invFun y := ⟨y.1, (GlobalTheory.FinPl.SplitPoint.mem_integer_iff F v y.1).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem exists_coord_padic : ∀ (D : D7) (T : ℕ) [Fact T.Prime] (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ (v : Pl D) (pr : AE D →+* ℚ_[T]) (sec : ℚ_[T] →+ AE D), (∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a, pr (sec a) = a) ∧ (∀ x, sec (pr x) = e * x) ∧ Continuous pr ∧ Continuous sec ∧ ∀ a, ‖a‖ ≤ 1 ↔ finPart D (sec a) ∈ intAE D := by
  intro D T _ w e hw hs hT hT2
  obtain ⟨_, _, v, ε, hε, he⟩ := id hs
  have hsa : SplitAt D v e := GlobalTheory.FinPl.SplitPoint.splitAt_of hs hε he
  have hch : Chart e v (comp hsa) := chart_comp hsa
  have hTw : ((T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    have := Ideal.absNorm_mem w.asIdeal
    rwa [hT] at this
  have hTw2 : ((T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 := fun h =>
    hT2 (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
  obtain ⟨⟨p, hp, hirr⟩, hcard⟩ := GlobalTheory.SplitUnif.unif_chart e w v (comp hsa) hw hch _ hTw hTw2
  have hpT : p = (T : Ov D v) := by
    apply Subtype.ext
    rw [show ((p : Fv D.host.F v)) = algebraMap (Ov D v) (Fv D.host.F v) p from rfl, hp]
    simp
  subst hpT
  haveI : CharZero (Fv D.host.F v) :=
    charZero_of_injective_ringHom (algebraMap D.host.F (v.adicCompletion D.host.F)).injective
  have hc1 : Nat.card (IsLocalRing.ResidueField 𝒪[Fv D.host.F v]) = T := by
    rw [← hT, ← hcard]
    exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (intEquiv D.host.F v)).toEquiv).symm
  have hc2 : Irreducible (T : 𝒪[Fv D.host.F v]) := by
    rw [← map_natCast (intEquiv D.host.F v) T]
    exact (MulEquiv.irreducible_iff (intEquiv D.host.F v).toMulEquiv).2 hirr
  obtain ⟨φ, hφ, hφ', hφO⟩ := GlobalTheory.T.exists_ringEquiv_padic_of_residueCard_uniformizer (Fv D.host.F v) T hc1 hc2
  obtain ⟨sp, hse, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε hs hε he
  refine ⟨v, φ.symm.toRingHom.comp sp.pr, sp.sec.comp φ.toRingHom.toAddMonoidHom, ⟨ε, hε, he⟩,
    fun a => ?_, fun x => ?_, hφ'.comp sp.cont_pr, sp.cont_sec.comp hφ, fun a => ?_⟩
  · change φ.symm (sp.pr (sp.sec (φ a))) = a
    rw [sp.pr_sec, RingEquiv.symm_apply_apply]
  · change sp.sec (φ (φ.symm (sp.pr x))) = e * x
    rw [RingEquiv.apply_symm_apply, sp.sec_pr, hse]
  · exact (hφO a).symm.trans (sp.int_iff (φ a))

end GlobalTheory.FinPl.SplitQT

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.BesInt

theorem absConv_of_invariant : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∀ f : GA D B.V → ℂ, Continuous f →
    (∀ γ ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)), ∀ h, f (γ * h) = f h) →
    ∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 fun h₁ n => f (n.1 * embA B.d B.o h₁ * h) := by
  intro D σ B f hf hinv h
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨hemb, -, hconj, -, hrat⟩ := GlobalTheory.Unf.besSemi D σ B
  obtain ⟨KA, hKA, hcovA⟩ := B.cpt
  obtain ⟨⟨KN, hKN, hcovN⟩, -⟩ :=
    GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V σ B.d.e (isIsoSub_e B.d)

  let Φ : NFlag B.V B.d.e × GA D B.A → GA D B.V := fun p => p.1.1 * embA B.d B.o p.2 * h
  have hΦ : Continuous Φ :=
    ((continuous_subtype_val.comp continuous_fst).mul (hemb.comp continuous_snd)).mul continuous_const
  have hΩ : IsCompact (Φ '' (KN ×ˢ KA)) := (hKN.prod hKA).image hΦ
  obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn hf.continuousOn

  have hbd : ∀ (h₁ : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h₁ * h)‖ ≤ C := by
    intro h₁ n
    obtain ⟨γ, hγ, hγK⟩ := hcovA h₁
    obtain ⟨δ, hδ, k, hk, hnk⟩ :=
      hcovN ⟨embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹, hconj n.1 n.2 γ⟩
    have heq : embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹ = δ.1 * k.1 := congrArg Subtype.val hnk
    have hγV : embA B.d B.o γ ∈ GQ B.V := by
      have := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
      rwa [one_mul] at this
    have hδQ : (δ.1 : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hδ
    have hηQ : (embA B.d B.o γ)⁻¹ * δ.1 ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hγV) hδQ,
        mul_mem (inv_mem (Subgroup.mem_sup_right ⟨γ, rfl⟩)) (Subgroup.mem_sup_left δ.2)⟩
    have e1 : n.1 = (embA B.d B.o γ)⁻¹ * (δ.1 * k.1) * embA B.d B.o γ := by rw [← heq]; group
    have e2 : n.1 * embA B.d B.o h₁ * h =
        ((embA B.d B.o γ)⁻¹ * δ.1) * (k.1 * embA B.d B.o (γ * h₁) * h) := by
      rw [e1, map_mul]; group
    rw [e2, hinv _ hηQ]
    exact hC _ ⟨(k, γ * h₁), ⟨hk, hγK⟩, rfl⟩

  have hfinA : B.vA.μ B.vA.𝓕 < ⊤ := by
    have hcov' : ∀ g : GA D B.A, ∃ γ ∈ GQ B.A, ∃ c ∈ KA, g = γ * c := fun g => by
      obtain ⟨γ, hγ, hc⟩ := hcovA g
      exact ⟨γ⁻¹, inv_mem hγ, γ * g, hc, by rw [inv_mul_cancel_left]⟩
    have h1 := GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain B.A B.vA.μ B.vA.𝓕 KA B.vA.haar B.vA.fund hKA
      hcov' (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl
    simpa using (integrableOn_const_iff (C := (1 : ℂ))).1 h1
  have hfinN : B.vN.ν B.vN.𝓝 < ⊤ := by rw [B.vN.unit.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hfinA.ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hfinN.ne
  have hK : Continuous (Function.uncurry fun (h₁ : GA D B.A) (n : flagN B.d) => f (n.1 * embA B.d B.o h₁ * h)) :=
    hf.comp (((continuous_subtype_val.comp continuous_snd).mul (hemb.comp continuous_fst)).mul continuous_const)
  exact Integrable.of_bound hK.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hbd p.1 p.2)

end GlobalTheory.Unf.BesInt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.besselGroup_semidirectProduct_rational : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), Continuous (embA B.d B.o) ∧ IsClosed (flagN B.d : Set (GA D B.V)) ∧ (∀ n ∈ flagN B.d, ∀ h, embA B.d B.o h * n * (embA B.d B.o h)⁻¹ ∈ flagN B.d) ∧ (∀ n ∈ flagN B.d, ∀ n' ∈ flagN B.d, ∀ h h', n * embA B.d B.o h = n' * embA B.d B.o h' → n = n' ∧ h = h') ∧ ∀ n ∈ flagN B.d, ∀ h, n * embA B.d B.o h ∈ GQ B.V ↔ n ∈ GQ B.V ∧ h ∈ GQ B.A := by
  first | exact @GlobalTheory.Unf.besSemi | exact GlobalTheory.Unf.besSemi | (intros; apply GlobalTheory.Unf.besSemi <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf


theorem _root_.GlobalTheory.T.isFundamentalDomain_flagUnipotent_coords : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)) (𝓤 : Set (UX D ρ)), lC.IsAddHaarMeasure → SFinite lC → IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC → IsFundamentalDomain (UXQ D ρ) 𝓤 vU.ν → IsFundamentalDomain (NFlagQ V d.e) (e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ 𝓤))) ((lC.prod (vb.μ.prod vU.ν)).map e) := by
  first | exact @GlobalTheory.ThreeLayers.fundDomain_coords | exact GlobalTheory.ThreeLayers.fundDomain_coords | (intros; apply GlobalTheory.ThreeLayers.fundDomain_coords <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.secondModel_realPart_matrix_frame : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → ∀ (a : GA D (D.sp.X 0)) (τ : D.what₂.Tau), Formalism.L2.SG.ColDict.sTil X tr.wt ((B.toH a).1 : X.B.I.Ginf) τ = GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ := by
  first | exact @GlobalTheory.Core.Mi.sTil_toH_eq_infM | exact GlobalTheory.Core.Mi.sTil_toH_eq_infM | (intros; apply GlobalTheory.Core.Mi.sTil_toH_eq_infM <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isFockVec_ptOf_of_isVacVec : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsVacVec ψ θ M M' f → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec ψ θ V W (cart M) (cart M') (ptOf ψ θ M M' f P) := by
  first | exact @GlobalTheory.FockVecOfVac.fock_of_vac | exact GlobalTheory.FockVecOfVac.fock_of_vac | (intros; apply GlobalTheory.FockVecOfVac.fock_of_vac <;> assumption)
end
