module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle350
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle220
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle407
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle612
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle528
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle507
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle317
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle611
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle280
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle561
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle615
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236

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

namespace GlobalTheory.CoreRowLat

variable {D : D7}

theorem gen_negSp (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j) : WO S T) =
      -(Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) := by
  ext i j; simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem latO_negSp (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P = latO S T LS LT P := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩
    show _ ∈ latO S T LS LT P
    rw [gen_negSp S T α a s t]
    exact neg_mem (AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩)
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _), ← gen_negSp S T α a s t]
    exact neg_mem (AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩)

theorem latO_mul_left {S T T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {LT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (A : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (hA : ∀ t ∈ LT, A *ᵥ t ∈ LT') {u : WO S T}
    (hu : u ∈ latO S T LS (LT : Set _) P) : (rat A : Mx D T'.rank T.rank) * u ∈ latO S T' LS (LT' : Set _) P :=
  GlobalTheory.OverTgt.mul_mem_latO (rat A) (fun _ hy => GlobalTheory.SeeSaw.CoreGlue.rat_mulVec_mem A hA hy) hu

theorem latO_mul_right {S S' T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LS' : Set (Fin S'.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (M : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hM : ∀ s ∈ LS, ∃ s' ∈ LS', ∀ j, ∑ l, (∑ k, star (s k) * S.gram k l) * M l j = ∑ k, star (s' k) * S'.gram k j)
    {u : WO S T} (hu : u ∈ latO S T LS LT P) : u * (rat M : Mx D S.rank S'.rank) ∈ latO S' T LS' LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨s', hs', hss⟩ := hM s hs
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s', hs', t, ht, ?_⟩
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, ← hss j, Finset.mul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.of_apply]
    show _ * incA D (M l j) = _
    rw [GlobalTheory.RankZeroVac.incA_tmul', Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem hatMx_mul_left {m m' n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)}
    (A : Matrix (Fin m') (Fin m) D.host.E) (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ'') {x : Mx D m n}
    (hx : x ∈ hatMx (I • homLat Λ Λ')) : (rat A : Mx D m' m) * x ∈ hatMx (I • homLat Λ Λ'') := by
  have h := GlobalTheory.TwistHatMx.rat_conj_mem_hatMx I 1 A (fun y hy => by rwa [Matrix.one_mulVec]) hA x hx
  rwa [rat_one, Matrix.mul_one] at h

theorem hatMx_mul_right {m n n' : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    (N : Matrix (Fin n) (Fin n') D.host.E) (hN : ∀ s ∈ Λ₁, N *ᵥ s ∈ Λ) {x : Mx D m n}
    (hx : x ∈ hatMx (I • homLat Λ Λ')) : x * (rat N : Mx D n n') ∈ hatMx (I • homLat Λ₁ Λ') := by
  have h := GlobalTheory.TwistHatMx.rat_conj_mem_hatMx I N 1 hN (fun y hy => by rwa [Matrix.one_mulVec]) x hx
  rwa [rat_one, Matrix.one_mul] at h

theorem wittEmbedding_preserves_hermitianForm {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (s : Fin S₀.rank → D.host.E) (j : Fin S₀.rank) :
    ∑ l, (∑ k, star ((d.i₀ *ᵥ s) k) * S.gram k l) * d.i₀ l j = ∑ k, star (s k) * S₀.gram k j := by
  have h : Matrix.vecMul (Matrix.vecMul (star (d.i₀ *ᵥ s)) S.gram) d.i₀ = Matrix.vecMul (star s) S₀.gram := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, d.iso]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

end GlobalTheory.CoreRowLat

namespace GlobalTheory.CoreRowLat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem std_zA_lat {F : GlobalTheory.Asc.Frames G} (hF : Std F) : (∀ y ∈ G.Λ (.grid 0 0), F.oz.iA *ᵥ y ∈ G.Λ (.core 0)) ∧
    ∀ x ∈ G.Λ (.core 0), F.oz.qA *ᵥ x ∈ G.Λ (.grid 0 0) := by
  have hΛ : G.Λ (.core 0) = sumLat (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι) (L.ΛY 0) G.sp.dec0.a (fun _ => 1) :=
    G.sp.lat0
  have hqi : F.oz.qA * F.oz.iA = 1 := rat_injective (by rw [rat_mul, rat_one]; exact F.oz.pA_jA)
  have hperp := G.sp.dec0.perp
  have hqa : F.oz.qA * G.sp.dec0.a = 0 := by
    change (HSpace.gram (Yc D 0))⁻¹ * (F.oz.iAᴴ * HSpace.gram (G.V (.core 0))) * G.sp.dec0.a = 0
    rw [hF.zA, Matrix.mul_assoc, Matrix.mul_assoc]
    have hp : (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ * HSpace.gram (G.sp.P 0).sp * G.sp.dec0.a = 0 := hperp
    rw [← Matrix.mul_assoc (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ, hp, Matrix.mul_zero]
  refine ⟨fun y hy => ?_, fun x hx => ?_⟩
  · rw [hΛ]
    refine ⟨y, hy, 0, fun _ => (FractionalIdeal.mem_one_iff _).2 ⟨0, map_zero _⟩, ?_⟩
    rw [Matrix.mulVec_zero, add_zero, hF.zA]
  · rw [hΛ] at hx
    obtain ⟨y, hy, u, -, rfl⟩ := hx
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hF.zA, hqi, hqa, Matrix.one_mulVec,
      Matrix.zero_mulVec, add_zero]
    exact hy

theorem std_aJ_lat {F : GlobalTheory.Asc.Frames G} (hF : Std F) (h : 2 * 0 + 2 ≤ D.R.m) :
    (∀ y ∈ G.Λ (.core 1), (F.dJ 0 h).i₀ *ᵥ y ∈ G.Λ (.grid 1 0)) ∧
    (∀ x ∈ G.Λ (.grid 1 0), ∃ y ∈ G.Λ (.core 1), x = (F.dJ 0 h).i₀ *ᵥ y) ∧
    ∀ x ∈ G.Λ (.grid 1 0), (F.dJ 0 h).q0 *ᵥ x ∈ G.Λ (.core 1) := by
  have h1 : 1 ≤ D.R.m := by omega
  have hΛ : G.Λ (.grid 1 0) = sumLat (frameMat (G.V (.grid 1 0)) (G.V (.core 1)) (G.colDec 1 le_rfl h1).ι) (G.Λ (.core 1))
      (G.colDec 1 le_rfl h1).a (stairId (G.pl.stA sc) (G.pl.stAbar sc) (1 - 1)) := G.sp.colLat 1 le_rfl h1
  have hi : (F.dJ 0 h).i₀ = frameMat (G.V (.grid 1 0)) (G.V (.core 1)) (G.colDec 1 le_rfl h1).ι := hF.aJ 0 h
  have hqi : (F.dJ 0 h).q0 * (F.dJ 0 h).i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact (F.dJ 0 h).p0_j0)
  have mem : ∀ x, x ∈ G.Λ (.grid 1 0) ↔ ∃ y ∈ G.Λ (.core 1), x = (F.dJ 0 h).i₀ *ᵥ y := by
    intro x
    rw [hΛ, hi]
    constructor
    · rintro ⟨y, hy, u, -, rfl⟩
      refine ⟨y, hy, ?_⟩
      have : (G.colDec 1 le_rfl h1).a *ᵥ u = 0 := by
        funext i; simp [Matrix.mulVec, dotProduct]
      rw [this, add_zero]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, 0, fun p => p.elim0, by rw [Matrix.mulVec_zero, add_zero]⟩
  refine ⟨fun y hy => (mem _).2 ⟨y, hy, rfl⟩, fun x hx => (mem x).1 hx, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := (mem x).1 hx
  rwa [Matrix.mulVec_mulVec, hqi, Matrix.one_mulVec]

end GlobalTheory.CoreRowLat

namespace GlobalTheory.CoreRowLat

variable {D : D7}

theorem depthLattice_generalPosition_iff_extByZero {P₁ P₀ Y Lz S : HSp D} (o : OrthDec P₀ Y Lz) (d : HypDec S P₁ 0)
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin P₁.rank → D.host.E)} {Λ₀ : Submodule (𝓞 D.host.E) (Fin P₀.rank → D.host.E)}
    {ΛY : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    (I : Ideal (𝓞 D.host.E)) (Q : AE D → Prop)
    (hiA : ∀ y ∈ ΛY, o.iA *ᵥ y ∈ Λ₀) (hqA : ∀ x ∈ Λ₀, o.qA *ᵥ x ∈ ΛY)
    (hi0 : ∀ y ∈ Λ₁, d.i₀ *ᵥ y ∈ ΛS) (hq0 : ∀ x ∈ ΛS, ∃ y ∈ Λ₁, x = d.i₀ *ᵥ y) (hq0' : ∀ x ∈ ΛS, d.q0 *ᵥ x ∈ Λ₁)
    (a : WO P₁ Y) :
    (o.jA * a ∈ latO (negSp P₁) P₀ (Λ₁ : Set _) (Λ₀ : Set _) (fun _ => True) ∧
      ∀ e : AE D, Q e → e • (o.jA * a) ∈ hatMx (I • homLat Λ₁ Λ₀)) ↔
    (d.ext0 Y a ∈ latO (negSp S) Y (ΛS : Set _) (ΛY : Set _) (fun _ => True) ∧
      ∀ e : AE D, Q e → e • d.ext0 Y a ∈ hatMx (I • homLat ΛS ΛY)) := by
  have hpj : d.p0 * (rat d.i₀ : Mx D _ _) = 1 := d.p0_j0
  have hpA : (rat o.qA : Mx D _ _) * o.jA = 1 := o.pA_jA
  have cB : ∀ x : WO P₁ Y, x * d.p0 * (rat d.i₀ : Mx D _ _) = x := fun x => by
    rw [Matrix.mul_assoc, hpj, Matrix.mul_one]
  have cA : ∀ x : WO P₁ Y, (rat o.qA : Mx D _ _) * (o.jA * x) = x := fun x => by
    rw [← Matrix.mul_assoc, hpA, Matrix.one_mul]
  have ext : d.ext0 Y a = a * d.p0 := rfl
  rw [ext, latO_negSp, latO_negSp]
  have hA1 : o.jA * a ∈ latO P₁ P₀ (Λ₁ : Set _) (Λ₀ : Set _) (fun _ => True) ↔
      a ∈ latO P₁ Y (Λ₁ : Set _) (ΛY : Set _) (fun _ => True) := by
    constructor
    · intro hu
      have := latO_mul_left o.qA hqA hu
      rwa [cA] at this
    · intro hu; exact latO_mul_left o.iA hiA hu
  have hB1 : a ∈ latO P₁ Y (Λ₁ : Set _) (ΛY : Set _) (fun _ => True) ↔
      a * d.p0 ∈ latO S Y (ΛS : Set _) (ΛY : Set _) (fun _ => True) := by
    constructor
    · intro hu
      exact latO_mul_right d.q0 (fun s hs => ⟨d.i₀ *ᵥ s, hi0 s hs, fun j => GlobalTheory.RankZeroVac.wittDecomposition_gram_projection_identity d s j⟩) hu
    · intro hu
      have := latO_mul_right d.i₀ (fun s hs => by
        obtain ⟨y, hy, rfl⟩ := hq0 s hs
        exact ⟨y, hy, fun j => wittEmbedding_preserves_hermitianForm d y j⟩) hu
      rwa [cB] at this
  have hA2 : ∀ e : AE D, e • (o.jA * a) ∈ hatMx (I • homLat Λ₁ Λ₀) ↔ e • a ∈ hatMx (I • homLat Λ₁ ΛY) := by
    intro e
    rw [← Matrix.mul_smul]
    constructor
    · intro hx
      have := hatMx_mul_left I o.qA hqA hx
      rwa [cA] at this
    · intro hx; exact hatMx_mul_left I o.iA hiA hx
  have hB2 : ∀ e : AE D, e • a ∈ hatMx (I • homLat Λ₁ ΛY) ↔ e • (a * d.p0) ∈ hatMx (I • homLat ΛS ΛY) := by
    intro e
    rw [← Matrix.smul_mul]
    constructor
    · intro hx; exact hatMx_mul_right I d.q0 hq0' hx
    · intro hx
      have := hatMx_mul_right I d.i₀ hi0 hx
      rwa [cB] at this
  exact and_congr (hA1.trans hB1) (forall_congr' fun e => imp_congr_right fun _ => (hA2 e).trans (hB2 e))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem jA_mem_latCore_iff : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (a : WO (G.V (.core 1)) (Yc D 0)),
    F.oz.jA * a ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) a ∈ latRow G 0 := by
  intro D _ T L _ _ sc G W M _ F hF h a
  obtain ⟨hiA, hqA⟩ := std_zA_lat hF
  obtain ⟨hi0, hq0, hq0'⟩ := std_aJ_lat hF h
  exact depthLattice_generalPosition_iff_extByZero F.oz (F.dJ 0 h) G.modul (fun e => IsIdemSum e G.pl.W0) hiA hqA hi0 hq0 hq0' a

end GlobalTheory.CoreRowLat

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

noncomputable section

namespace GlobalTheory.NFJetProof

theorem exists_nf_of_finite (E : Set ℂ) (hE : E.Finite) (hA : ∀ z ∈ E, IsAlgebraic ℚ z) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ E ⊆ Set.range (algebraMap M ℂ) := by
  haveI : Finite E := hE.to_subtype
  refine ⟨IntermediateField.adjoin ℚ E, IntermediateField.finiteDimensional_adjoin fun z hz => (hA z hz).isIntegral,
    fun z hz => ⟨⟨z, IntermediateField.subset_adjoin ℚ E hz⟩, rfl⟩⟩

def dset {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) : Set (PureDat G t) :=
  {d | ∃ τ, IsCosetExpansion S t Φ β k τ ∧ d ∈ τ.support}

end GlobalTheory.NFJetProof

namespace GlobalTheory.NFJetProof

theorem jetCl_of_choice {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A)
    (hS : HidaSetting large₂ R F) (ch : Choice R) (hch : ch.Is) (hI : GlobalTheory.NormSum.Inp D) (hok : ∀ t a, ch.S.SumOK t (ch.Phi a))
    (hD : GlobalTheory.SumSize.DictAt ch) : InNF fun _ σ => JetCl σ ch.S.toGridChoice := by
  have hok' : ∀ t Φ, ch.S.SumOK t Φ := fun t Φ => by
    obtain ⟨a, rfl⟩ := GlobalTheory.T.rowTestChoice_datum_surjective large₂ F hS ch hch Φ
    exact hok t a
  haveI : Finite T := hS.fin
  haveI : Finite ch.G.Datum := Finite.of_surjective ch.Phi fun Φ => GlobalTheory.T.rowTestChoice_datum_surjective large₂ F hS ch hch Φ
  set S := ch.S.toGridChoice with hSdef
  let E : Set ℂ := ⋃ t, ⋃ Φ, ⋃ β ∈ S.supp t Φ, ⋃ d ∈ dset S t Φ β (expDepth S t Φ β), ⋃ c : S.Classes t Φ β,
    ((⋃ j : Fin D.R.m, ⋃ a, ⋃ b, {S.Z.kk (d.1 j) (S.ptTop c j) (S.ptTop c (j + 1)) a b}) ∪
      (⋃ i : Fin D.R.m, ⋃ a, ⋃ b, {S.Z.kk (d.2 i) (S.ptRow c i) (S.ptRow c (i + 1)) a b}))
  have hE : E.Finite := by
    refine Set.finite_iUnion fun t => Set.finite_iUnion fun Φ => Set.Finite.biUnion (hok' t Φ).fin fun β _ =>
      Set.Finite.biUnion (GlobalTheory.T.finite_pureData_of_cosetIndicatorExpansions_depth S t Φ β _) fun d _ => ?_
    haveI := (hok' t Φ).cls β
    exact Set.finite_iUnion fun c => Set.Finite.union
      (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _)
      (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _)
  have hA : ∀ z ∈ E, IsAlgebraic ℚ z := by
    intro z hz
    simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop] at hz
    obtain ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hdτ⟩, c, h⟩ := hz
    obtain ⟨hk, hexp, hcos⟩ := hτ
    obtain ⟨e, -, hP, -⟩ := id hexp
    have hw := (hok' t Φ).wts
    have hv := (hok' t Φ).vec β τ hexp d hdτ
    rcases h with ⟨j, a, b, rfl⟩ | ⟨i, a, b, rfl⟩
    · exact GlobalTheory.T.normalisedDefiniteKernel_entries_isAlgebraic large₂ F hS ch hch hI hD t (.top t j) (show (j : ℕ) + 1 ≤ D.R.m from j.2) (hw j j.2).1 _ (d.1 j) hk
        ((hcos d hdτ).1 j) ((hP d hdτ).1 j).2.2 ((hP d hdτ).1 j).1 (hv.1 j) _ _ a b
    · exact GlobalTheory.T.normalisedDefiniteKernel_entries_isAlgebraic large₂ F hS ch hch hI hD t (.chi i D.R.m) (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m = D.R.m from ⟨i.2, rfl⟩) (hw i i.2).2 _
        (d.2 i) hk ((hcos d hdτ).2 i) ((hP d hdτ).2 i).2.2 ((hP d hdτ).2 i).1 (hv.2 i) _ _ a b
  obtain ⟨M, hM, hsub⟩ := exists_nf_of_finite E hE hA
  refine ⟨M, hM, fun t Φ β hβ τ hτ d hd c => ⟨fun j a b => hsub ?_, fun i a b => hsub ?_⟩⟩
  · simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hd⟩, c, Or.inl ⟨j, a, b, rfl⟩⟩
  · simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hd⟩, c, Or.inr ⟨i, a, b, rfl⟩⟩

theorem nfJet_holds : SumOKK → (∀ D, GlobalTheory.NormSum.Inp D) → (Big fun ch => GlobalTheory.SumSize.DictAt ch) → NFJet := by
  intro h1 h2 h3
  obtain ⟨C, hC⟩ := Big.and h1 h3
  refine ⟨C, fun ε CF hCF => ?_⟩
  obtain ⟨x, hx⟩ := hC ε CF hCF
  exact ⟨x, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc =>
    jetCl_of_choice large₂ F hS ch hch (h2 D) (hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc).1
      (hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc).2⟩

end GlobalTheory.NFJetProof
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid

theorem isThetaAt_unique {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {c : ℂ}
    {f₀ Φ f f' : Mx D m n → ℂ} (h : IsThetaAt ψ B hs e Λ c f₀ Φ f) (h' : IsThetaAt ψ B hs e Λ c f₀ Φ f') : f = f' := by
  obtain ⟨⟨T, hT⟩, h1⟩ := h
  exact (h1 T hT).trans (h'.2 T hT).symm

theorem exists_cosetVec_of_match {D : D7} {S T : Grid.Node D} {V₁ V₂ : HSp D}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin V₁.rank → D.host.E)} {Λ₂ : Submodule (𝓞 D.host.E) (Fin V₂.rank → D.host.E)}
    {I I' : Ideal (𝓞 D.host.E)} {e : AE D} {ψ ψ' : AddChar (AF D.host.F) ℂ}
    (hS : S.V = V₁) (hT : T.V = V₂) (hΛ₁ : HEq S.Λ Λ₁) (hΛ₂ : HEq T.Λ Λ₂) (hI : I = I') (hψ : ψ = ψ')
    (vac : WO (negSp V₁) V₂ → ℂ) (cv : Cos Λ₁ Λ₂ I' → WO (negSp V₁) V₂ → ℂ)
    (hcv : ∀ κ : Cos Λ₁ Λ₂ I', IsThetaAt ψ (symplO (negSp V₁) V₂) (heisO ψ (negSp V₁) V₂) e
      (latO (negSp V₁) V₂ (Λ₁ : Set _) (Λ₂ : Set _) fun _ => True) 1 vac (cosInd e κ) (cv κ))
    (hA : ∀ c : Grid.Coset S T I, ∃ κ : Cos S.Λ T.Λ I, Grid.cosetInd S T e I c = cosInd e κ)
    (hB : ∀ κ : Cos S.Λ T.Λ I, ∃ c : Grid.Coset S T I, Grid.cosetInd S T e I c = cosInd e κ)
    (f : WO S.V T.V → ℂ) (hf : HEq f vac) :
    ∃ v : Grid.Coset S T I → (WO S.V T.V → ℂ), (∀ c, Grid.IsCosetVec ψ' true S T e I c f (v c)) ∧
      (∀ c, ∃ κ, HEq (v c) (cv κ)) ∧ ∀ κ, ∃ c, HEq (v c) (cv κ) := by
  subst hS hT hI hψ
  obtain rfl := eq_of_heq hΛ₁
  obtain rfl := eq_of_heq hΛ₂
  obtain rfl := eq_of_heq hf
  choose κ hκ using hA
  refine ⟨fun c => cv (κ c), fun c => ?_, fun c => ⟨κ c, HEq.rfl⟩, fun κ' => ?_⟩
  · show IsThetaAt ψ _ _ e _ 1 f (Grid.cosetInd S T e I c) (cv (κ c))
    rw [hκ c]
    exact hcv (κ c)
  · obtain ⟨c, hc⟩ := hB κ'
    refine ⟨c, heq_of_eq ?_⟩
    have h1 := hcv (κ c)
    have h2 := hcv κ'
    rw [← hκ c, hc] at h1
    exact isThetaAt_unique h1 h2

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid

theorem isFrame_col {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (hR : GlobalTheory.Hk3.Core R F) {G : GlobalTheory.Grid.GridPre R} (hsp : G.IsSpaces) {i : ℕ} (hi : i ≤ D.R.m) :
    Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ := by
  cases i with
  | zero =>
    obtain ⟨c, hc⟩ := hR.lev.βY 0 (by have := D.R.two_le_m; omega)
    exact hc.1
  | succ k =>
    obtain ⟨c, hc⟩ := (hsp.vert k 0 hi (Nat.zero_le _)).frame
    exact hc.1

theorem exists_cosData_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ f : WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ, HEq f (W.vac i) → ∃ v : G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ), (∀ c, GlobalTheory.Grid.IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c f (v c)) ∧ (∀ c, ∃ κ, HEq (v c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (v c) (W.cosVec i κ) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDC hHC hH F hR hsc G' W hW G hsp hch hag hcos i hi f hf
  have hA := GlobalTheory.T.homLatticeCosetIndicator_primePowers_integralCoset (G.V (i + 1) 0) (G.V i 0) G.idem (G.toPlaceDat.W R.Pg) G.toPlaceDat.depth
    (isFrame_col hR hsp (by omega)) (isFrame_col hR hsp hi.le) hch.places.idem
  have hB := GlobalTheory.T.exists_homLatticeCosetIndicator_eq_latticeHomCoset (G.V (i + 1) 0) (G.V i 0) G.idem (G.toPlaceDat.W R.Pg) G.toPlaceDat.depth
    (isFrame_col hR hsp (by omega)) (isFrame_col hR hsp hi.le) hch.places.idem
  exact exists_cosetVec_of_match (I := G.lvl R) (hag.vert (i + 1) 0 (by omega) (Nat.zero_le _)).sp
    (hag.vert i 0 hi.le (Nat.zero_le _)).sp (hag.vert (i + 1) 0 (by omega) (Nat.zero_le _)).lat
    (hag.vert i 0 hi.le (Nat.zero_le _)).lat hag.lvl hW.ψ (W.vac i) (W.cosVec i) (hcos i hi) hA hB f hf

end GlobalTheory.GridJoin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel.OffTens

theorem partAt_finW_off_mem_hatA : ∀ (D : D7) (S T : HSp D) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ (L : Lt D.host.E T.rank) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E), y ∈ tens (stdL D.host.E S.rank) L → GlobalTheory.LiftLevel.partAt (1 - e - cA D e) (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • L)) := by
  intro D S T Pg Q e he L y hy
  classical
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum D _ e he
  have hf : 1 - e - cA D e = 1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) := by rw [hσ]; ring
  have hW : finW S T y = GlobalTheory.LiftLevel.TrOff.gm S T 1 y := rfl
  rw [hf, hW, GlobalTheory.LiftLevel.TrOff.partAt_gm, mul_one]
  have hO : ∀ (c : 𝓞 D.host.F), ∀ z ∈ tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • L),
      (algebraMap D.host.F D.host.E (c : D.host.F)) • z ∈ tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • L) :=
    fun c z hz => GlobalTheory.Ker.HatLat.smul_mem_tens _ _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) hz
  have hγ : (1 - σ) ∈ intAf D.host.F := by
    intro w
    rw [map_sub, map_one]
    by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
    · obtain ⟨PP, hPP, rfl⟩ := hw
      rw [hσ1 PP hPP, sub_self]; exact zero_mem _
    · push_neg at hw
      rw [hσ0 w hw, sub_zero]; exact GlobalTheory.LatVac.one_mem_intAf _ w
  refine GlobalTheory.HatPoint.mem_hatA_of_div D S T _ hO _ hγ _ fun w => ?_
  by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
  · left
    obtain ⟨PP, hPP, rfl⟩ := hw
    rw [map_sub, map_one, hσ1 PP hPP, sub_self]
  · right
    push_neg at hw
    have hex : ∀ PP ∈ Pg ∪ Q, ∃ s : 𝓞 D.host.F,
        algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ PP.asIdeal ∧ s ∉ w.asIdeal := by
      intro PP hPP
      by_contra hcon
      push_neg at hcon
      apply hw PP hPP
      have hle : (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal ≤ w.asIdeal := fun s hs => hcon s hs
      exact HeightOneSpectrum.ext ((HeightOneSpectrum.isMaximal _).eq_of_le w.isPrime.ne_top hle)
    choose! tf htf1 htf2 using hex
    refine ⟨∏ PP ∈ Pg ∪ Q, tf PP, ?_, ?_⟩
    · exact (Submonoid.prod_mem w.asIdeal.primeCompl fun c hc => htf2 c hc : _)
    · have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ PP ∈ Pg ∪ Q, tf PP) ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
        rw [map_prod]
        exact Ideal.prod_mem_prod fun PP hPP =>
          GlobalTheory.TrOffShift.algebraMap_mem_conjI (D := D) _ _ (htf1 PP hPP)
      exact GlobalTheory.LiftLevel.smul_mem_tens (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ PP ∈ Pg ∪ Q, tf PP))
        (fun u hu => Submodule.smul_mem_smul hmem hu) hy

end GlobalTheory.LiftLevel.OffTens

end
end
