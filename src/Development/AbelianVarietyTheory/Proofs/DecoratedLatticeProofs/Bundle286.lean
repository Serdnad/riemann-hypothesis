module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle200
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle226
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle276
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle271
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle274
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ChartChi



theorem levChi_chart : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s j φ ι → ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t), ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ι hι ξl hξ y hy d hd
  have hlev := (GlobalTheory.chart_level_iff D c w hw j hj s hs PP hPP v φ hφ ι hι y).2 hy
  obtain ⟨hr, hL, hfl⟩ := hs
  obtain ⟨e, he⟩ := GlobalTheory.ChartSplitIso.exists_equiv_emb D s j v φ ι hfl.selfDual hfl.frame hι
  have hv : v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ).1
  obtain ⟨ε, hε, hch⟩ := hι
  rw [Lev.levG, Lev.mem_levA, hL] at hlev
  have hmem := hlev.2
  rw [mem_lev, mem_parLev] at hmem
  obtain ⟨⟨-, hS, -, hQ⟩, -⟩ := hmem
  have hPc : PP ∈ c.Pg := by
    classical
    rw [hw.union]; exact Finset.mem_union_right _ hPP
  have hone : ∀ PP', PP' ∈ c.Pg → PP' ≠ PP → redFn s.β PP' (Lev.finE s.V (ι y)) = 1 := by
    intro PP' hP' hne
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β _ PP' hS ?_
    have hu : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ v := by
      intro h
      exact hne (GlobalTheory.LevelPlaces.injOn_under D c hw.com hP' hPc (h.trans hv))
    rw [he y]
    exact GlobalTheory.AdelicU.proj_emb_ne _ _ hu _
  have hsub : ∀ PP', PP' ∈ w.Pg ∨ PP' ∈ w.Q → PP' ∈ c.Pg := by
    classical
    intro PP' h
    rw [hw.union]
    exact Finset.mem_union.2 h
  rw [Lev.levChi, hL]
  set L := Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B with hLd
  have hLxq : L.xq = fun PP => (w.ξ PP)⁻¹ := by rw [hLd]; simp [Lev.datY]
  have hLPg : L.Pg = w.Pg := rfl
  have hLQ : L.Q = w.Q := rfl
  have hLr : L.r = D.R.r := rfl
  set x := Lev.finE s.V (ι y) with hx
  have h1 : ext1 L.P.H (⇑L.P.chi) (rTup s.β L x) = 1 := Lev.subgroupCharExtension_one_apply (LevelP.triv w.Pg D.R.r ℂ).H _
  have h2 : ∏ PP ∈ L.Pg, ∏ c ∈ Finset.range L.s, (L.cg (c + 1) PP) (dBlk (blkOf L.r L.t) (c + 1) (redFn s.β PP x)) = 1 := by
    refine Finset.prod_eq_one fun PP' hP' => Finset.prod_eq_one fun c' _ => ?_
    have hne : PP' ≠ PP := by
      rintro rfl
      exact Finset.disjoint_left.1 hw.disj hP' hPP
    rw [hone PP' (hsub _ (Or.inl hP')) hne, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  have h3 : ∏ PP ∈ L.Q, (L.xq PP) (dBlk (blk2 L.r) 1 (redFn s.β PP x)) = (L.xq PP) (dBlk (blk2 L.r) 1 (redFn s.β PP x)) := by
    refine Finset.prod_eq_single PP (fun PP' hP' hne => ?_) (fun h => absurd hPP h)
    rw [hone PP' (hsub _ (Or.inr hP')) hne, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  unfold levFn
  rw [h1, h2, h3, one_mul, one_mul, hLxq]
  obtain ⟨⟨rr, -, -, hrel, hN⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hφ
  have hQP : redFn s.β PP x ∈ blockTri (blk2 D.R.r) := hQ PP hPP
  obtain ⟨Y, hY⟩ := hS
  set G := (grpCo φ s.V (frCo φ s.β) (ι y)).val with hG
  have hi : intGL D.host.F D.host.E _ Y = s.β⁻¹ * x * s.β := by
    rw [← hY]
    simp [frGL, MulAut.conj_apply]
    group
  have hxm : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) x =
      Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom s.V (ι y)) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (x.val i j) = rdA φ ((Formalism.L2.Theta.matHom s.V (ι y)).val i j)
    exact GlobalTheory.SplitProjChart.rdE_toEAf φ _
  have hm : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (s.β⁻¹ * x * s.β) = grpCo φ s.V (frCo φ s.β) (ι y) := by
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, hxm]
    rfl
  have key : ∀ a b, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((Y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) = G a b := by
    intro a b
    rw [hG, ← hm, ← hi]
    rfl
  have hint : ∀ a b, G a b ∈ v.adicCompletionIntegers D.host.F := fun a b => key a b ▸ (hN _ (Y.val a b).2).1
  have hred : ∀ a b, rr ⟨G a b, hint a b⟩ = (redFn s.β PP x).val a b := by
    intro a b
    obtain ⟨h, hh⟩ := hN _ (Y.val a b).2
    rw [← hY, redFn_frGL]
    have e : (⟨G a b, hint a b⟩ : v.adicCompletionIntegers D.host.F) = ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (Y.val a b : Lev.EAf D), h⟩ :=
      Subtype.ext (key a b).symm
    rw [e, hh]
    rfl
  have hT : ∀ i : Blocks j D.R.t, blk2 D.R.r (ε (.inr i)) = 1 := by
    intro i
    have := GlobalTheory.ChartLevel.eps_inr_ge ε hε i
    simp [blk2, not_lt.2 this]
  let f : Blocks j D.R.t → {a : Fin s.V.rank // blk2 D.R.r a = 1} := fun i => ⟨ε (.inr i), hT i⟩
  have hfb : Function.Bijective f := by
    constructor
    · intro i i' h
      have := congrArg Subtype.val h
      exact Sum.inr_injective (ε.injective this)
    · rintro ⟨a, ha⟩
      obtain ⟨p, rfl⟩ := ε.surjective a
      rcases p with p | p
      · exfalso
        have hp : ((ε (.inl p) : Fin s.V.rank) : ℕ) < D.R.r := by rw [hε]; exact p.2
        simp [blk2, hp] at ha
      · exact ⟨p, rfl⟩
  let ef := Equiv.ofBijective f hfb
  let Gi : Matrix (Fin s.V.rank) (Fin s.V.rank) (v.adicCompletionIntegers D.host.F) := fun a b => ⟨G a b, hint a b⟩
  let A : Matrix {a : Fin s.V.rank // blk2 D.R.r a = 1} {a : Fin s.V.rank // blk2 D.R.r a = 1} (v.adicCompletionIntegers D.host.F) :=
    Gi.submatrix Subtype.val Subtype.val
  have hdA : (d : Fv D.host.F v) = ((A.det : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) := by
    rw [hd]
    have e1 : ((A.det : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) =
        (G.submatrix (Subtype.val : {a : Fin s.V.rank // blk2 D.R.r a = 1} → Fin s.V.rank) (Subtype.val : {a : Fin s.V.rank // blk2 D.R.r a = 1} → Fin s.V.rank)).det := by
      rw [show ((A.det : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) = (v.adicCompletionIntegers D.host.F).subtype A.det from rfl,
        RingHom.map_det]
      congr 1
    rw [e1, ← Matrix.det_submatrix_equiv_self ef]
    congr 1
    refine Matrix.ext fun i i' => ?_
    have := congrFun (congrFun (hch y).2 (.inr i)) (.inr i')
    exact this.symm
  have hk : ((dBlk (blk2 D.R.r) 1 (redFn s.β PP x) : (kP PP)ˣ) : kP PP) = rr A.det := by
    rw [diag_block_det_val 1 hQP, RingHom.map_det]
    congr 1
    ext a b
    exact (hred a b).symm
  have hrel' : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (d : Fv D.host.F v) ((dBlk (blk2 D.R.r) 1 (redFn s.β PP x) : (kP PP)ˣ) : kP PP) := by
    rw [hrel]
    refine ⟨hdA ▸ A.det.2, ?_⟩
    rw [hk]
    congr 1
    exact Subtype.ext hdA
  have hξd := hξ d _ hrel'
  show ((((w.ξ PP)⁻¹) (dBlk (blk2 D.R.r) 1 (redFn s.β PP x)) : ℂˣ) : ℂ) = _
  rw [MonoidHom.inv_apply, hξd]

end GlobalTheory.ChartChi
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
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

theorem _root_.GlobalTheory.T.twisted_chain_chart_parahoric_eq_level : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s j φ ι → ∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t) := by
  first | exact @GlobalTheory.chart_level_iff | exact GlobalTheory.chart_level_iff | (intros; apply GlobalTheory.chart_level_iff <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.UnimodNF

section Abstract

variable {A : Type*} [CommRing A] {ε : A} (hid : IsIdempotentElem ε) (O : Set A)
  (h0 : (0 : A) ∈ O) (hadd : ∀ a ∈ O, ∀ b ∈ O, a + b ∈ O) (hneg : ∀ a ∈ O, -a ∈ O)
  (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hεO : ε ∈ O)

def sub : Subring hid.Corner where
  carrier := {x | x.1 ∈ O}
  zero_mem' := h0
  add_mem' {x y} hx hy := hadd _ hx _ hy
  neg_mem' {x} hx := hneg _ hx
  mul_mem' {x y} hx hy := hmul _ hx _ hy
  one_mem' := hεO


include hid h0 hadd hneg hmul hεO in
theorem exists_congr_one (c : A →+* A) (hc : ∀ x, c (c x) = x) (hcO : ∀ a ∈ O, c a ∈ O) (hcε : c ε = ε)
    (hεa : ∀ a ∈ O, ε * a = a)
    (hloc : ∀ x ∈ O, c x = x → (∃ y ∈ O, x * y = ε) ∨ (∃ y ∈ O, (ε - x) * y = ε))
    (hw : ∃ w ∈ O, w + c w = ε)
    (hnorm : ∀ u ∈ O, c u = u → (∃ y ∈ O, u * y = ε) → ∃ x ∈ O, x * c x = u)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) A) (hH : ∀ i j, H i j ∈ O) (hherm : ∀ i j, c (H i j) = H j i)
    (hinv : ∃ H' : Matrix (Fin n) (Fin n) A, (∀ i j, H' i j ∈ O) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) A)) :
    ∃ P P' : Matrix (Fin n) (Fin n) A, (∀ i j, P i j ∈ O) ∧ (∀ i j, P' i j ∈ O) ∧
      P * P' = ε • (1 : Matrix (Fin n) (Fin n) A) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) A) ∧
      (P.map c)ᵀ * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
  classical
  let R := sub hid O h0 hadd hneg hmul hεO
  have corner_mem : ∀ a ∈ O, a ∈ Subsemigroup.corner ε := fun a ha =>
    (Subsemigroup.mem_corner_iff hid).2 ⟨hεa a ha, by rw [mul_comm]; exact hεa a ha⟩
  let mk : ∀ a, a ∈ O → R := fun a ha => ⟨⟨a, corner_mem a ha⟩, ha⟩
  let val : R →+ A := { toFun := fun x => x.1.1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have val_mem : ∀ x : R, val x ∈ O := fun x => x.2
  have val_inj : ∀ x y : R, val x = val y → x = y := fun x y h => Subtype.ext (Subtype.ext h)
  let c' : R →+* R :=
    { toFun := fun x => mk (c (val x)) (hcO _ (val_mem x))
      map_one' := val_inj _ _ (show c ε = ε from hcε)
      map_mul' := fun x y => val_inj _ _ (show c (val x * val y) = c (val x) * c (val y) from map_mul c _ _)
      map_zero' := val_inj _ _ (show c 0 = 0 from map_zero c)
      map_add' := fun x y => val_inj _ _ (show c (val x + val y) = c (val x) + c (val y) from map_add c _ _) }
  have hc' : ∀ x, c' (c' x) = x := fun x => val_inj _ _ (show c (c (val x)) = val x from hc _)
  have map_mul_val : ∀ X Y : Matrix (Fin n) (Fin n) R, (X * Y).map val = X.map val * Y.map val := by
    intro X Y
    ext i j

    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    rfl
  have map_one_val : (1 : Matrix (Fin n) (Fin n) R).map val = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · simp only [smul_eq_mul, mul_one]; rfl
    · simp only [smul_eq_mul, mul_zero, map_zero]
  have map_inj : ∀ X Y : Matrix (Fin n) (Fin n) R, X.map val = Y.map val → X = Y := fun X Y h =>
    Matrix.ext fun i j => val_inj _ _ (congrFun (congrFun h i) j)
  let G : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => mk (H i j) (hH i j)
  have hGH : G.map val = H := by ext i j; rfl
  obtain ⟨H', hH'O, hHH'⟩ := hinv
  let G' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => mk (H' i j) (hH'O i j)
  have hG'H : G'.map val = H' := by ext i j; rfl
  have hGG' : G * G' = 1 := map_inj _ _ (by rw [map_mul_val, map_one_val, hGH, hG'H]; exact hHH')
  have hdet : IsUnit G.det := Matrix.isUnit_det_of_right_inverse hGG'
  have hG : ∀ a b, c' (G a b) = G b a := fun a b => val_inj _ _ (hherm a b)
  have hlocR : ∀ x : R, c' x = x → IsUnit x ∨ IsUnit (1 - x) := by
    intro x hx
    have hx' : c (val x) = val x := congrArg val hx
    rcases hloc (val x) (val_mem x) hx' with ⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩
    · exact Or.inl (isUnit_iff_exists_inv.2 ⟨mk y hy, val_inj _ _ hxy⟩)
    · exact Or.inr (isUnit_iff_exists_inv.2 ⟨mk y hy, val_inj _ _ hxy⟩)
  have hwR : ∃ w : R, w + c' w = 1 := by
    obtain ⟨w, hw, hw'⟩ := hw
    exact ⟨mk w hw, val_inj _ _ hw'⟩
  have hnormR : ∀ u : R, c' u = u → IsUnit u → ∃ x, x * c' x = u := by
    intro u hu hu'
    obtain ⟨y, hy⟩ := hu'.exists_right_inv
    obtain ⟨x, hx, hx'⟩ := hnorm (val u) (val_mem u) (congrArg val hu) ⟨val y, val_mem y, congrArg val hy⟩
    exact ⟨mk x hx, val_inj _ _ hx'⟩
  obtain ⟨Q, hQ, hGQ⟩ :=
    GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map_of_isUnit_or c' hc' hlocR hwR hnormR hG hdet
  have hmap1 : (1 : Matrix (Fin n) (Fin n) R).map c' = 1 := Matrix.map_one _ (map_zero c') (map_one c')
  refine ⟨((Q⁻¹).map c').map val, (Q.map c').map val, fun i j => val_mem _, fun i j => val_mem _, ?_, ?_, ?_⟩
  · rw [← map_mul_val, ← Matrix.map_mul, Matrix.nonsing_inv_mul Q hQ, hmap1, map_one_val]
  · rw [← map_mul_val, ← Matrix.map_mul, Matrix.mul_nonsing_inv Q hQ, hmap1, map_one_val]
  · have e1 : (((Q⁻¹).map c').map val).map c = (Q⁻¹).map val := by
      ext i j
      exact congrArg val (hc' (Q⁻¹ i j))
    rw [e1, ← Matrix.transpose_map, ← hGH, ← map_mul_val, ← map_mul_val, ← map_one_val]
    congr 1
    have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
    rw [hGQ]
    calc (Q⁻¹)ᵀ * (Qᵀ * Q.map c' * (Q⁻¹).map c') = (Q * Q⁻¹)ᵀ * (Q * Q⁻¹).map c' := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.transpose_one, hmap1, Matrix.one_mul]

end Abstract



variable {D : D7}

theorem intAt_zero' (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_neg' {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem cA_mem_intAt' {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) :=
  ⟨GlobalTheory.FinPl.RootKeep.conj_mem_idAt ha.1, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩

theorem unimodular_congr_one : ∀ (D : D7) (v : Pl D) (ε : AE D) (n : ℕ) (H : Matrix (Fin n) (Fin n) (AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → (∀ i j, H i j ∈ intAt D (· = v)) → (∀ i j, cA D (H i j) = H j i) → (∃ H' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) (AE D))) → ∃ P P' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, P i j ∈ intAt D (· = v)) ∧ (∀ i j, P' i j ∈ intAt D (· = v)) ∧ P * P' = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ adj P * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  intro D v ε n H htame hεε hεc hεI hε hHI hherm hinv
  exact exists_congr_one (hid := hεε) (O := intAt D (· = v)) (intAt_zero' _)
    (fun a ha b hb => GlobalTheory.IwaPlace.SdComap.intAt_add ha hb) (fun a ha => intAt_neg' ha)
    (fun a ha b hb => GlobalTheory.IwaPlace.SdComap.intAt_mul ha hb) hεI (cA D) (fun z => Formalism.L2.Theta.cA_cA z)
    (fun a ha => cA_mem_intAt' ha) hεc (fun a ha => (hε a).1 ha.1)
    (GlobalTheory.T.conjFixed_integral_isUnit_or_idem_sub_unit D v ε htame hεε hεc hεI hε)
    (GlobalTheory.IwaPlace.exists_trace_one_at_tame D v ε hεε hεc hεI hε htame)
    (GlobalTheory.T.exists_norm_of_conjFixed_unit_tamePlace D v ε htame hεε hεc hεI hε) H hHI hherm hinv

end GlobalTheory.IwaPlace.UnimodNF

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.carriesLatticeCompletion_on_off_iff_all_finitePlaces : ∀ {D : D7} (S : HSp D) (g : GA D S) (L : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop), (GlobalTheory.FinPl.Moves S g L L (fun p => ¬ P p) ∧ GlobalTheory.FinPl.Moves S g L L P) ↔ GlobalTheory.FinPl.Moves S g L L (fun _ => True) := by
  first | exact @GlobalTheory.FinPl.moves_iff_moves_on_off | exact GlobalTheory.FinPl.moves_iff_moves_on_off | (intros; apply GlobalTheory.FinPl.moves_iff_moves_on_off <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.flagUnipotent_fundamentalDomain_layers_integral : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ), ∃ 𝓐 : Set (flagN d), IsFundamentalDomain ((GQ V ⊓ radX d).subgroupOf (flagN d)) 𝓐 vN.ν ∧ ∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν := by
  first | exact @GlobalTheory.Unf.layers_integral | exact GlobalTheory.Unf.layers_integral | (intros; apply GlobalTheory.Unf.layers_integral <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.Unf.StepFour

variable {D : D7}

theorem zEll_mem_ratMx (T : HSp D) (ρ : ℕ) (z : Fin T.rank → D.host.E) : zEll T ρ z ∈ ratMx D T.rank ρ := by
  refine ⟨Matrix.vecMulVec z (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0), ?_⟩
  funext i j
  change incA D (z i * (if j.1 + 1 = ρ then (1 : D.host.E) else 0)) = ratV z i * ell D ρ j
  simp only [ratV, ell]
  split_ifs <;> simp

theorem incAdj_yZero_mem {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Fin S.rank → D.host.E) :
    d.incAdj S (yZero S ρ z) ∈ ratMx D T.rank S.rank := by
  have hy : yZero S ρ z ∈ ratMx D S.rank ρ := by
    rw [yZero]; exact neg_mem (zEll_mem_ratMx S ρ z)
  rw [HypDec.incAdj_apply, HypDec.incY_apply]
  exact ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : AF D.host.F) :
    star (ψ x) = ψ (-x) := by
  change (starRingEnd ℂ) (ψ x) = _
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.1.2.1 x)]

end GlobalTheory.Unf.StepFour
end

noncomputable section
namespace GlobalTheory.Unf.StepFour

variable {D : D7}

theorem integrand_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {ρ : ℕ}
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) (f : WO V₀ W → ℂ)
    (hf : IsThetaFunO ψ V₀ W f) (b : Mx D ρ V₀.rank) :
    star (psiBes ψ dV 1 z (dV.nB b)) * f (xZero dW ⬝ b) =
      heisO ψ V₀ W (dW.incX V₀ b) (heisO ψ V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (heisO ψ V₀ W (dW.inc0 V₀ 0) f)) 0 := by
  rw [HypDec.integrandT_eq, ← psi_yZero ψ dV dW z b, star_psi hψ, map_zero, add_zero]
  obtain ⟨γ, hγ⟩ := incAdj_yZero_mem dW V₀ z
  have hx : dW.incX V₀ b = xZero dW ⬝ b := rfl
  have hq := hf.quasi γ (xZero dW ⬝ b)
  rw [show ratW W V₀ γ = dW.incAdj V₀ (yZero V₀ ρ z) from hγ] at hq
  rw [hx, add_comm (xZero dW ⬝ b), hq, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hc : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add (f := _), add_halves, map_one]
  have hs : symplO V₀ W (xZero dW ⬝ b) (dW.incAdj V₀ (yZero V₀ ρ z)) =
      -symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (xZero dW ⬝ b) := GlobalTheory.OrientedHeis.symplO_skew _ _
  rw [symplOH, symplOH]
  linear_combination (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (xZero dW ⬝ b)) * hc -
    algebraMap D.host.F (AF D.host.F) (1 / 2) * hs

end GlobalTheory.Unf.StepFour
end

noncomputable section
namespace GlobalTheory.Unf.StepFour

theorem fl_eq_flatBF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ →
      fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flatBF s Ψ 0 := by
  intro D ψ ρ B J s Ψ hΨ
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  have hf : ∀ x, IsThetaFunO ψ B.V₀ J.W (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x) := fun x =>
    (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  unfold fl flatBF flat flatAt
  congr 1
  funext u
  have hu : ∀ b, star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b * B.d.levi u.1)) =
      star (psiUni ψ u.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b)) := by
    intro b
    rw [psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.levi_mem_NFlag (mem_UX.1 u.2)), psiBes_levi, star_mul',
      mul_comm]
  unfold flFun flatFun evalAt
  simp_rw [hu, mul_assoc]
  rw [integral_const_mul]
  congr 1
  congr 1
  funext b
  exact integrand_eq hψ B.d J.d _ _ (hf _) b

end GlobalTheory.Unf.StepFour
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.quotient_integral_vanish_of_iterated_finite_integrals : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [SecondCountableTopology G₁] [LocallyCompactSpace G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [LocallyCompactSpace G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (A₁ B₁ R₁ : Subgroup G₁) (A₂ B₂ R₂ : Subgroup G₂), IsClosed (A₁ : Set G₁) → IsClosed (B₁ : Set G₁) → IsClosed (R₁ : Set G₁) → (∀ a ∈ A₁, ∀ b ∈ B₁, a * b = b * a) → (∃ e : (A₁ × B₁) ≃ₜ G₁, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A₁, ∀ b ∈ B₁, a * b ∈ R₁ → a ∈ R₁ ∧ b ∈ R₁) → IsClosed (A₂ : Set G₂) → IsClosed (B₂ : Set G₂) → IsClosed (R₂ : Set G₂) → (∀ a ∈ A₂, ∀ b ∈ B₂, a * b = b * a) → (∃ e : (A₂ × B₂) ≃ₜ G₂, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A₂, ∀ b ∈ B₂, a * b ∈ R₂ → a ∈ R₂ ∧ b ∈ R₂) → ∀ (μR₁ : Measure R₁) (μG₁ : Measure G₁) (ρ₁ : Measure (R₁.subgroupOf B₁)) (μ₁ : Measure B₁) (μR₂ : Measure R₂) (μG₂ : Measure G₂) (ρ₂ : Measure (R₂.subgroupOf B₂)) (μ₂ : Measure B₂), μR₁.IsHaarMeasure → μR₁.IsInvInvariant → μG₁.IsHaarMeasure → ρ₁.IsHaarMeasure → ρ₁.IsInvInvariant → μ₁.IsHaarMeasure → μ₁.IsMulRightInvariant → μR₂.IsHaarMeasure → μR₂.IsInvInvariant → μG₂.IsHaarMeasure → ρ₂.IsHaarMeasure → ρ₂.IsInvInvariant → μ₂.IsHaarMeasure → ∀ (K : Subgroup G₁) (C : Set G₁) (T : Finset G₁), K ≤ B₁ → IsCompact (K : Set G₁) → IsOpen ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁) → IsCompact C → C ⊆ (B₁ : Set G₁) → (∀ q ∈ T, q ∈ B₁) → ∀ (F₁ : G₁ → ℂ) (F₂ : G₁ → G₂ → ℂ) (z : ℂ), IsQuotIntL1 μR₁ μG₁ F₁ z → (∀ h₁, IsQuotIntL1 μR₂ μG₂ (F₂ h₁) (F₁ h₁)) → (∀ h₁, ∀ k ∈ K, F₂ (h₁ * k) = F₂ h₁) → (∀ h₁, F₂ h₁ ≠ 0 → ∃ q ∈ T, ∃ r ∈ R₁, ∃ a ∈ A₁, ∃ k ∈ C, h₁ = r * a * q * k) → (∀ a ∈ A₁, ∀ a' ∈ A₂, Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun (q₁ : B₁) (q₂ : B₂) => F₂ (a * q₁.1) (a' * q₂.1)) 0) → z = 0 := by
  first | exact @GlobalTheory.VanCore.vanish | exact GlobalTheory.VanCore.vanish | (intros; apply GlobalTheory.VanCore.vanish <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselPeriod_linear_and_translationCombination : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (φ : GA D B.A → ℂ), IsContAut B.A φ → (∀ (I : Type) (s : Finset I) (a : I → ℂ) (f : I → GA D B.V → ℂ), (∀ i ∈ s, IsContAut B.V (f i)) → B.per ψ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * B.per ψ φ (f i)) ∧ ∀ (e : GA D B.V →₀ ℂ) (f : GA D B.V → ℂ), IsContAut B.V f → IsContAut B.V (trc e f) ∧ B.per ψ φ (trc e f) = ∑ g ∈ e.support, e g * B.per ψ φ (rTrans g f) := by
  first | exact @GlobalTheory.SeeSaw.per_linear_trc | exact GlobalTheory.SeeSaw.per_linear_trc | (intros; apply GlobalTheory.SeeSaw.per_linear_trc <;> assumption)
end
