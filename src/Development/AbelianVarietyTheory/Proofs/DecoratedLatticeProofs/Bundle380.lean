module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle353
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle162
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle168
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle252
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle087
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.SymChainAt
open GlobalTheory.FinPl (SplitPt idAt intAt)
open Formalism.L2.NTheta (IsIdemAt)
open _root_.Formalism.L2.Col (IntAt)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one : q.sec 1 = q.e := by
  have := q.sec_pr 1
  rwa [map_one, mul_one] at this

theorem pr_e : q.pr q.e = 1 := by rw [← sec_one, q.pr_sec]

theorem pr_e_mul (x : AE D) : q.pr (q.e * x) = q.pr x := by rw [map_mul, pr_e, one_mul]

theorem place_facts {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) :
    (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  obtain ⟨k₀, _, _, _, _, q₀, he, -, hi, hd⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP q.e h
  refine ⟨fun a => ?_, ?_⟩
  · rw [← hi, q.int_iff, q₀.int_iff]
    change finPart D (q.sec (q.pr _)) ∈ _ ↔ finPart D (q₀.sec (q₀.pr _)) ∈ _
    rw [q.sec_pr, q₀.sec_pr, he]
  · have hs : Function.Surjective (fun x => q.pr (q₀.sec x)) := fun y =>
      ⟨q₀.pr (q.sec y), by simp only [q₀.sec_pr, he, pr_e_mul, q.pr_sec]⟩
    have := hs.denseRange.comp hd (q.cont_pr.comp q₀.cont_sec)
    convert this using 1
    funext a
    change q.pr _ = q.pr (q₀.sec (q₀.pr _))
    rw [q₀.sec_pr, he, pr_e_mul]

def prO : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem sec_mul (x y : k) : q.sec x * q.sec y = q.sec (x * y) := by
  have h := q.sec_pr (q.sec x * q.sec y)
  rw [map_mul, q.pr_sec, q.pr_sec, ← mul_assoc, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem idl_mul (x y : k) (h : x * y = 1) : (q.sec x + (1 - q.e)) * (q.sec y + (1 - q.e)) = 1 := by
  have h1 := sec_mul q x y
  rw [h, sec_one] at h1
  have h2 := GlobalTheory.FrameGlob.sec_eq_mul q x
  have h3 := GlobalTheory.FrameGlob.sec_eq_mul q y
  have h4 := q.split.1
  linear_combination h1 + h2 + h3 + h4

def idl (x : kˣ) : (AE D)ˣ :=
  ⟨q.sec x + (1 - q.e), q.sec (x⁻¹ : kˣ) + (1 - q.e), idl_mul q _ _ x.mul_inv, idl_mul q _ _ x.inv_mul⟩

end Place

end GlobalTheory.LocMod.SymChainAt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastPrimSplit

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_e (q : GlobalTheory.FinPl.SplitPt D k) : q.pr q.e = 1 := by
  rw [← GlobalTheory.FinPl.FrameLat.sec_one q, q.pr_sec]

theorem incAdj_yZero_apply {ρ : ℕ} (hρ : 0 < ρ) {S T T₀ : HSp D} (d : HypDec T T₀ ρ) (z : Fin S.rank → D.host.E)
    (a : AE D) (i : Fin T.rank) (l : Fin S.rank) :
    d.incAdj S (a • yZero S ρ z) i l =
      cA D a * incA D (D.host.xi0⁻¹ * d.e' i ⟨ρ - 1, by omega⟩ * (star z ᵥ* S.gram) l) := by
  have hell : ∀ i : Fin ρ, cA D (ell D ρ i) = if i = ⟨ρ - 1, by omega⟩ then 1 else 0 := by
    intro i
    simp only [ell, Fin.ext_iff]
    split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | simp

  simp only [HypDec.incAdj_apply, HypDec.incY_apply, yZero, zEll, Matrix.vecMul, dotProduct,
  Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply, adj, Matrix.transpose_apply, Matrix.map_apply,
  Matrix.vecMulVec_apply, smul_eq_mul, map_mul, map_neg, hell, map_sum]
  rw [Finset.sum_eq_single (⟨ρ - 1, by omega⟩ : Fin ρ) (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [if_true, mul_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  change incA D (d.e' i _) * (-incA D _ * (cA D a * -incA D (star (z m)) * incA D (S.gram m l))) =
    cA D a * (incA D _ * incA D (d.e' i _) * (incA D (star (z m)) * incA D (S.gram m l)))
  ring

theorem map_row {E : Type} [Field E] (f : E →+* k) {m n : Type} [Fintype m] (w : m → E) (M : Matrix m n E) (j : n) :
    ∑ l, f (w l) * f (M l j) = f ((w ᵥ* M) j) := by

  simp only [Matrix.vecMul, dotProduct, map_sum, RingHom.map_mul]

theorem row_core (q : GlobalTheory.FinPl.SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n] (sc : k)
    (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (hF₀ : (ofSplit q).IsCoreFrame B sc FA F₀) :
    (fun l => q.pr (incA D ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l))) ᵥ* F₀.β =
      Pi.single (Sum.inr ()) (sc * (ofSplit q).hz B) := by
  set f := q.pr.comp (incA D) with hf
  funext t
  rcases t with t | ⟨⟨⟩⟩
  · rw [Pi.single_eq_of_ne Sum.inl_ne_inr]
    have h0 : (fun l => f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l)) ᵥ* B.o.iA.map f = 0 := by
      funext j
      refine (map_row f _ B.o.iA j).trans ?_
      rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, B.o.orth,
        Matrix.vecMul_zero, Pi.zero_apply, Pi.zero_apply, map_zero]
    have h1 : ((fun l => f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l)) ᵥ* (B.o.iA.map f * FA.β)) t = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul, Pi.zero_apply]
    rw [← h1]
    change ∑ l, f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l) * F₀.β l (Sum.inl t) =
      ∑ l, f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l) * (B.o.iA.map f * FA.β) l t
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hF₀.1 l t]
    rfl
  · rw [Pi.single_eq_same]
    have h0 : (star (vecB B.o B.ζ) ᵥ* B.V₀.gram) ⬝ᵥ vecB B.o B.ζ = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
      rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, B.o.isoB]
    change ∑ l, f _ * F₀.β l (Sum.inr ()) = sc * f (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)

    rw [← h0, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hF₀.2 l, RingHom.map_mul, mul_left_comm]
    rfl

theorem row_jac (q : GlobalTheory.FinPl.SplitPt D k) {ρ : ℕ} (hρ : 0 < ρ) (J : JacLev D ρ) {n' : Type} [Fintype n'] [DecidableEq n']
    (sc hh : k) (FW₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (2 * ρ)))
    (hFW : (ofSplit q).IsJacFrame J sc hh FW₀ FW) :
    (fun l => q.pr (incA D ((J.d.e'ᴴ * J.W.gram) ⟨ρ - 1, by omega⟩ l))) ᵥ* FW.β =
      Pi.single (Sum.inr ⟨ρ - 1, by omega⟩) (sc * (ofSplit q).xi) := by
  set f := q.pr.comp (incA D) with hf
  set i₀ : Fin ρ := ⟨ρ - 1, by omega⟩ with hi₀
  have hcol : ∀ {m : ℕ} (M : Matrix (Fin J.W.rank) (Fin m) D.host.E) (j : Fin m),
      ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * f (M l j) = f ((J.d.e'ᴴ * J.W.gram * M) i₀ j) := fun M j => by

    rw [Matrix.mul_apply (M := J.d.e'ᴴ * J.W.gram), map_sum]
    simp only [RingHom.map_mul]
  funext t
  rcases t with t | t
  · rw [Pi.single_eq_of_ne Sum.inl_ne_inr]
    have hz : J.d.e'ᴴ * J.W.gram * J.d.i₀ = 0 := by
      have := congrArg Matrix.conjTranspose J.d.i₀e'
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
        ← Matrix.mul_assoc] at this
    have h0 : (fun l => f ((J.d.e'ᴴ * J.W.gram) i₀ l)) ᵥ* J.d.i₀.map f = 0 := by
      funext j
      refine (hcol J.d.i₀ j).trans ?_
      rw [hz, Matrix.zero_apply, map_zero, Pi.zero_apply]
    have h1 : ((fun l => f ((J.d.e'ᴴ * J.W.gram) i₀ l)) ᵥ* (J.d.i₀.map f * FW₀.β)) t = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul, Pi.zero_apply]
    rw [← h1]
    change ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inl t) =
      ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * (J.d.i₀.map f * FW₀.β) l t
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hFW.2.1 l t]
    rfl
  · change ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inr t) = _
    have hmul : ∀ (c : k) (M : Matrix (Fin J.W.rank) (Fin ρ) D.host.E) (j : Fin ρ),
        (∀ r, FW.β r (Sum.inr t) = c * f (M r j)) →
        ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inr t) = c * f ((J.d.e'ᴴ * J.W.gram * M) i₀ j) := fun c M j h => by
      rw [← hcol, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [h, mul_left_comm]
    by_cases ht : t.val < ρ
    · rw [hmul _ _ _ (hFW.2.2.1 ⟨t.val, ht⟩ t rfl), J.d.e'e]
      by_cases h2 : t.val = ρ - 1
      · have h3 : t = ⟨ρ - 1, by omega⟩ := Fin.ext h2
        have h4 : (⟨t.val, ht⟩ : Fin ρ) = i₀ := Fin.ext h2
        have h5 : ρ - (i₀ : ℕ) = 1 := by change ρ - (ρ - 1) = 1; omega
        rw [h4, Matrix.one_apply_eq, map_one, mul_one, h5, pow_one, h3, Pi.single_eq_same]
      · rw [Matrix.one_apply_ne fun h => h2 (congrArg Fin.val h).symm, map_zero, mul_zero,
          Pi.single_eq_of_ne fun h => h2 (congrArg Fin.val (Sum.inr_injective h))]
    · have h6 := t.2
      rw [hmul _ _ _ (hFW.2.2.2 ⟨2 * ρ - 1 - t.val, by omega⟩ t (by change t.val + (2 * ρ - 1 - t.val) + 1 = _; omega)),
        J.d.e'e', Matrix.zero_apply, map_zero, mul_zero, Pi.single_eq_of_ne fun h => ht (by
          have h7 : t.val = ρ - 1 := congrArg Fin.val (Sum.inr_injective h)
          omega)]

end GlobalTheory.LastPrimSplit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw

theorem fock_sph_tw : ∀ D : D7, ForStepQ D fun c _ k s s' p => (∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ)) ∧ GlobalTheory.LFun.UnrOff (c.chS (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) ∧ GlobalTheory.LFun.UnrOff (c.chT (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
  classical
  intro D _ c w hw k hk s s' hs hs' p hp
  have hc : c.Is := hw.com
  obtain ⟨hr₁, hL, hfl⟩ := hs
  obtain ⟨hr₂, -, hfl'⟩ := hs'
  obtain ⟨f₀, hvec⟩ := hp.vec
  have hψ : IsStdChar D c.ψ (-1) := hc.std
  have hθ : IsInfFam c.θ := hc.inf
  have hrk : s.V.rank ≤ s'.V.rank := by
    have e1 : s.V.rank = D.R.rankY k := hfl.rank
    have e2 : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    rw [e1, e2]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hsd' : IsSelfDualC s'.V s'.Λ := hfl'.selfDual
  obtain ⟨hfθ, -, hfv⟩ := GlobalTheory.Chain.StepVac.stepVec_vac hsd hsd' hrk hvec
  have hPS : ∀ PP ∈ s.L.Pg ∪ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ c.S := by
    intro PP hPP
    rw [hL] at hPP
    have hPP' : PP ∈ c.Pg := by rw [hw.union]; exact hPP
    exact Finset.mem_image_of_mem _ hPP'
  refine ⟨fun φ => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hfθ hfv φ
  · obtain ⟨hvac, e, he, hth⟩ := hvec
    exact GlobalTheory.FockSph.isLatVac_pureTensorO_off hθ (onb s.M) (onb s'.M) hvac he hth c.S hPS hp.theta φ
  · intro v hv
    obtain ⟨hf₀, e, he, hth⟩ := hvec
    obtain ⟨NS, hNS, hNSv⟩ := hfl.base
    obtain ⟨NT, hNT, hNTv⟩ := hfl'.base
    have hM : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
      obtain ⟨P, hP⟩ := GlobalTheory.ChainOnto.VacOffS.exists_under (D := D) v
      have hPv : P.under (𝓞 D.host.F) ∉ c.S := by rw [hP]; exact hv
      have h1 := hNSv P hPv
      have h2 := hNTv P hPv
      intro h
      rw [← hP] at h
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h
      rw [map_natCast, Nat.cast_mul] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact h1 h
      · exact h2 h
    have hle := GlobalTheory.ChainOnto.VacOffS.latO_at_le hNS.2.2.2.1 hNT.2.2.2.1 hM
    have hoff : ∀ PP ∈ s.L.Pg ∪ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := by
      intro PP hPP h0
      exact hv (h0 ▸ hPS PP hPP)
    have hfix : ∀ u ∈ latO s.V s'.V (GlobalTheory.AdelicU.frameLat s.V : Set (Fin s.V.rank → D.host.E))
        (GlobalTheory.AdelicU.frameLat s'.V : Set (Fin s'.V.rank → D.host.E)) (fun u => u = v),
        heisO c.ψ s.V s'.V u f₀ = f₀ → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ := fun u hu h0 =>
      GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hc.inf _ _ _ _ p.f hp.theta u
        (GlobalTheory.VacGood.infPart_latO (hle hu))
        (GlobalTheory.Hk3.heisO_fix_thetaAt_off c.ψ _ _ _ _ _ _ _ _ hth u
          (fun i j => GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff hu i j) h0) φ
    refine ⟨hp.theta φ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · exact hfix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hf₀.2.lat.1 u (hle hu))
    · exact hfix u hu (hf₀.2.lat.2 e' he' u (hle hu) hh)
  · intro v hv
    have hμ : GlobalTheory.LFun.UnrAt (c.μ (k + 1)) v := hc.unr ⟨k, hk⟩ v hv
    have hη : GlobalTheory.LFun.UnrAt c.η⁻¹ v := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 v).inv
    have hμη : GlobalTheory.LFun.UnrAt (c.μ (k + 1) * c.η⁻¹) v := hμ.mul hη
    unfold Com.chS Lift.chrStep
    split_ifs <;> assumption
  · intro v hv
    have hμ : GlobalTheory.LFun.UnrAt (c.μ (k + 1)) v := hc.unr ⟨k, hk⟩ v hv
    have hη : GlobalTheory.LFun.UnrAt c.η⁻¹ v := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 v).inv
    have hμη : GlobalTheory.LFun.UnrAt (c.μ (k + 1) * c.η⁻¹) v := hμ.mul hη
    unfold Com.chT Lift.chrStep
    split_ifs <;> assumption

end GlobalTheory.ChainTw

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem rTrans_rTrans {G : Type} [Semigroup G] (a b : G) (F : G → ℂ) : rTrans a (rTrans b F) = rTrans (a * b) F := by
  funext g; simp [rTrans, mul_assoc]

theorem rTrans_one {G : Type} [Monoid G] (F : G → ℂ) : rTrans 1 F = F := by
  funext g; simp [rTrans]

def space (Q : QStep S) : Submodule ℂ (GA D S.B'.V → ℂ) where
  carrier := {f | (∀ y, IsContAut S.B'.V (rTrans (Q.gl₂ y) f)) ∧
    ∃ U : Subgroup (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k), IsOpen (U : Set (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)) ∧
      ∀ u ∈ U, rTrans (Q.gl₂ u) f = f}
  zero_mem' := ⟨fun y => ⟨fun _ _ _ => rfl, continuous_const⟩, ⊤, isOpen_univ, fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf, U, hU, hfU⟩ ⟨hg, V, hV, hgV⟩
    refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, U ⊓ V, hU.inter hV, fun u hu => ?_⟩
    · change f (γ * x * _) + g (γ * x * _) = f (x * _) + g (x * _)
      have h1 := (hf y).1 γ hγ x
      have h2 := (hg y).1 γ hγ x
      simp only [rTrans] at h1 h2
      rw [h1, h2]
    · exact (hf y).2.add (hg y).2
    · have h1 := hfU u hu.1
      have h2 := hgV u hu.2
      funext x
      have e1 := congrFun h1 x
      have e2 := congrFun h2 x
      simp only [rTrans, Pi.add_apply] at e1 e2 ⊢
      rw [e1, e2]
  smul_mem' := by
    rintro a f ⟨hf, U, hU, hfU⟩
    refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, U, hU, fun u hu => ?_⟩
    · have h1 := (hf y).1 γ hγ x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      rw [h1]
    · exact continuous_const.mul (hf y).2
    · have h1 := hfU u hu
      funext x
      have e1 := congrFun h1 x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul] at e1 ⊢
      rw [e1]

theorem mem_translate (Q : QStep S) (y : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) {f : GA D S.B'.V → ℂ} (hf : f ∈ space Q) :
    rTrans (Q.gl₂ y) f ∈ space Q := by
  obtain ⟨hc, U, hU, hfU⟩ := hf
  refine ⟨fun y' => ?_, U.comap (MulAut.conj y⁻¹).toMonoidHom, ?_, fun u hu => ?_⟩
  · rw [rTrans_rTrans, ← map_mul]; exact hc _
  · have hc : Continuous fun x : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k => y⁻¹ * x * y⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hU.preimage hc
  · have hu' : y⁻¹ * u * y ∈ U := by simpa using hu
    rw [rTrans_rTrans, ← map_mul, show u * y = y * (y⁻¹ * u * y) by group, map_mul, ← rTrans_rTrans, hfU _ hu']

def rep (Q : QStep S) : Representation ℂ (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) (space Q) where
  toFun y :=
    { toFun := fun f => ⟨rTrans (Q.gl₂ y) f.1, mem_translate Q y f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f x
    simp [rTrans]
  map_mul' x y := by
    ext f g
    rw [Module.End.mul_apply]
    change f.1 (g * Q.gl₂ (x * y)) = f.1 (g * Q.gl₂ x * Q.gl₂ y)
    rw [map_mul, mul_assoc]

def valK (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (φ : GA D S.B.A → ℂ)
    (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ))
    (Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k)) (f : GA D S.B'.V → ℂ) : ℂ :=
  S.B'.per ψ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ))) f

theorem smooth (Q : QStep S) : IsSmoothRep (rep Q) := by
  intro v
  obtain ⟨-, U, hU, hfU⟩ := v.2
  let H : Subgroup (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) :=
    { carrier := {g | rep Q g v = v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : U ≤ H := fun u hu => Subtype.ext (hfU u hu)
  exact Subgroup.isOpen_mono hle hU

end GlobalTheory.TriStep
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.OneComb

theorem exists_open_fix' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Y : Type} [Fintype Y] [DecidableEq Y]
    (L : Level (GL Y k)) (hL : IsOpen (L.J : Set (GL Y k))) (α : GL Y k) :
    ∃ U : Subgroup (GL Y k), IsOpen (U : Set (GL Y k)) ∧ ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL Y k) A),
      IsSmoothRep σ → ∀ v : A, (∀ j : L.J, σ (j : GL Y k) v = (L.lam j : ℂ) • v) → ∀ u ∈ U, σ u (σ α v) = σ α v := by
  by_cases h : IsOpen ((L.lam.ker.map L.J.subtype : Subgroup (GL Y k)) : Set (GL Y k))
  · refine ⟨(L.lam.ker.map L.J.subtype).comap (MulAut.conj α⁻¹).toMonoidHom,
      h.preimage ((continuous_const.mul continuous_id).mul continuous_const), fun A _ _ σ _ v hv u hu => ?_⟩
    obtain ⟨j, hj, e⟩ := hu
    have e' : u * α = α * j := by
      have e2 : (j : GL Y k) = α⁻¹ * u * α⁻¹⁻¹ := e
      simp [e2, mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, e', map_mul, Module.End.mul_apply, hv, show L.lam j = 1 from hj, Units.val_one, one_smul]
  · refine ⟨⊤, isOpen_univ, fun A _ _ σ hσ v hv u _ => ?_⟩
    obtain rfl : v = 0 := by
      by_contra v0
      refine h (Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
        ((hL.inter (hσ v)).mem_nhds ⟨L.J.one_mem, by simp⟩) fun g hg => ⟨⟨g, hg.1⟩, Units.ext ?_, rfl⟩))
      exact smul_left_injective ℂ v0 (((hv ⟨g, hg.1⟩).symm.trans hg.2).trans (one_smul ℂ v).symm)
    simp

theorem exists_isOneComb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ), 1 ≤ P → P ≤ c → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ ν : Measure k, IsSelfDual ψ ν → ∀ (L : Level (GL (n ⊕ Fin c) k)), IsCO L.J → ∀ α, ∃ e, IsOneComb ψ ν P L α e := by
  intro k _ _ _ _ _ _ n _ _ c P h1 hP ψ hψc hψ1 ν hν L hL α
  obtain ⟨U, hU, h⟩ := exists_open_fix' L hL.1 α
  obtain ⟨e, e', he⟩ := GlobalTheory.T.exchangeToPositionOne_uniform_in_level k n c P h1 hP ψ hψc hψ1 ν hν U hU
  refine ⟨e.mapDomain (· * α), fun A _ _ σ hσ l hl v hv => ?_⟩
  rw [(he A σ hσ l _ hl (h A σ hσ v hv)).1, GlobalTheory.PosOne.comb, GlobalTheory.PosOne.comb,
    Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_mul _ _ _)]
  simp only [map_mul, Module.End.mul_apply]

end GlobalTheory.QPl.OneComb
end
end
