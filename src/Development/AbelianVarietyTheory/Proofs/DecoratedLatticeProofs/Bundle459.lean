module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle374
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle422
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle437
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle438
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle439
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle416

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.TopAgree

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem frGL_mul' {n : ℕ} (β : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    Formalism.L2.DIV.frGL β y * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E n y := by
  simp [Formalism.L2.DIV.frGL]



theorem mul_moved (p : GlobalTheory.LocMod.Place D k) {π' : Formalism.IndefR.Lev.EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = p.π a) (V : HSp D)
    (t x : GA D V) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = Formalism.IndefR.Lev.finE V (t⁻¹ * x * t)) {M : Matrix (Fin V.rank) (Fin V.rank) k}
    (hM : GlobalTheory.LocMod.MovedTo p V t β M) :
    (mt V x).map p.π * M = M * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
  have hs : Function.Surjective (toEAf D) := by
    refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
    exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id
  choose f hf using hs
  have h1 := hM (β.val.map f) (Matrix.ext fun i j => hf _)
  have h2 : (β.val.map f).map p.π = β.val.map π' := Matrix.ext fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply, ← hπ, hf]; rfl
  rw [Matrix.map_mul, h2] at h1
  have h3 : Formalism.IndefR.Lev.finE V (t⁻¹ * x * t) * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E _ y := by
    rw [← hy]
    exact frGL_mul' β y
  have h4 : (mt V (t⁻¹ * x * t)).map p.π * β.val.map π' =
      β.val.map π' * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
    have h5 := congrArg (fun g : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => g.val.map π') h3
    simp only [Units.val_mul, Matrix.map_mul] at h5
    have h6 : (Formalism.IndefR.Lev.finE V (t⁻¹ * x * t)).val.map π' = (mt V (t⁻¹ * x * t)).map p.π := Matrix.ext fun i j => hπ _
    rw [h6] at h5
    exact h5
  have h7 : mt V x * mt V t = mt V t * mt V (t⁻¹ * x * t) := by
    rw [← GlobalTheory.MixModel.mt_mul, ← GlobalTheory.MixModel.mt_mul, mul_assoc, mul_inv_cancel_left]
  rw [← h1, ← Matrix.mul_assoc, ← Matrix.map_mul, h7, Matrix.map_mul, Matrix.mul_assoc, h4, Matrix.mul_assoc]



theorem locHom_eq {Y : Type} [Fintype Y] [DecidableEq Y] (q : SplitPt D k) {π' : Formalism.IndefR.Lev.EAf D →+* k}
    (hπ : ∀ a, π' (toEAf D a) = q.pr a) (V : HSp D) (t x : GA D V) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = Formalism.IndefR.Lev.finE V (t⁻¹ * x * t)) (F : GlobalTheory.LocMod.Frame k V.rank Y) (e : Y ≃ Fin V.rank)
    (hM : GlobalTheory.LocMod.MovedTo (ofSplit q) V t β (F.β.submatrix id e.symm)) :
    (GlobalTheory.LevIdx.locHom q V F x).val = (y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix e e := by
  have h := mul_moved (ofSplit q) (π' := π') hπ V t x β y hy hM
  have hF : F.β = (F.β.submatrix id e.symm).submatrix id e := by
    ext i j; simp
  rw [GlobalTheory.LevIdx.locHom_val]
  generalize (y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) = Yn at h ⊢
  generalize hMm : F.β.submatrix id e.symm = Mm at h hF
  have key : ∀ (A : Matrix (Fin V.rank) (Fin V.rank) k) (B : Matrix (Fin V.rank) (Fin V.rank) k),
      A * B.submatrix id e = (A * B).submatrix id e := fun A B => by
    ext i j; simp [Matrix.mul_apply]
  have h' : (mt V x).map q.pr * Mm = Mm * Yn := h
  have h2 : (mt V x).map q.pr * F.β = F.β * Yn.submatrix e e := by
    calc (mt V x).map q.pr * F.β = (mt V x).map q.pr * Mm.submatrix id e := by rw [← hF]
      _ = ((mt V x).map q.pr * Mm).submatrix id e := key _ _
      _ = (Mm * Yn).submatrix id e := by rw [h']
      _ = Mm.submatrix id e * Yn.submatrix e e := (Matrix.submatrix_mul_equiv Mm Yn id e e).symm
      _ = F.β * Yn.submatrix e e := by rw [← hF]
  calc F.γ * (mt V x).map q.pr * F.β = F.γ * ((mt V x).map q.pr * F.β) := Matrix.mul_assoc _ _ _
    _ = F.γ * (F.β * Yn.submatrix e e) := by rw [h2]
    _ = Yn.submatrix e e := by rw [← Matrix.mul_assoc, F.γβ, Matrix.one_mul]

end GlobalTheory.TopAgree

namespace GlobalTheory.TopAgree

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_twist_levTop {s : ℕ} {τ κ : Type} [Fintype τ] [DecidableEq τ] [Fintype κ] [DecidableEq κ] (δ : kˣ →* ℂˣ)
    (hδ : GlobalTheory.SplitWeil.IsTame δ) (ν : ℕ → kˣ →* ℂˣ) (x : GL (GlobalTheory.StepData.Ix (κ ⊕ Fin (s + 1)) τ (s + 2)) k) :
    x ∈ (GlobalTheory.StepData.twistChain s τ κ δ hδ ν).levTop.J ↔
      x ∈ GlobalTheory.SplitWeil.KO k _ ∧ ∀ i j, ValuativeRel.valuation k (x.val (Sum.inr i) (Sum.inl j)) < 1 := by
  have e : (GlobalTheory.StepData.LatFrame.refl k (GlobalTheory.StepData.Ix (κ ⊕ Fin (s + 1)) τ (s + 2))).conj.symm x = x := by
    rw [MulEquiv.symm_apply_eq]
    ext i j
    simp [GlobalTheory.StepData.LatFrame.conj, GlobalTheory.StepData.LatFrame.refl, GlobalTheory.StepData.reGL_val]
  show x ∈ ((GlobalTheory.StepData.parahoric (κ ⊕ Fin (s + 1)) (Fin (s + 2) × τ) δ hδ).toLevel.map
    (GlobalTheory.StepData.LatFrame.refl k _).conj).J ↔ _
  rw [GlobalTheory.StepData.Level.mem_map, e, GlobalTheory.StepData.mem_parahoric]
  rfl

theorem frGL_inv {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {t g : GA D V}
    {y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hy : Formalism.L2.DIV.frGL β y = Formalism.IndefR.Lev.finE V (t⁻¹ * g * t)) :
    Formalism.L2.DIV.frGL β y⁻¹ = Formalism.IndefR.Lev.finE V (t⁻¹ * g⁻¹ * t) := by
  have e : t⁻¹ * g⁻¹ * t = (t⁻¹ * g * t)⁻¹ := by group
  exact ((Formalism.L2.DIV.frGL β).map_inv y).trans ((congrArg (·⁻¹) hy).trans
    (((Formalism.IndefR.Lev.finE V).map_inv _).symm.trans (congrArg (Formalism.IndefR.Lev.finE V) e.symm)))



theorem red_iff {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] (q : SplitPt D k)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D) (t g : GA D V)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (F : GlobalTheory.LocMod.Frame k V.rank (R ⊕ S)) (e : R ⊕ S ≃ Fin V.rank)
    (hM : GlobalTheory.LocMod.MovedTo (ofSplit q) V t β (F.β.submatrix id e.symm)) (r : ℕ)
    (hl : ∀ a, (e (Sum.inl a)).val < r) (hr : ∀ a, r ≤ (e (Sum.inr a)).val)
    (hst : Formalism.IndefR.Lev.finE V (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β) :
    Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (t⁻¹ * g * t)) ∈ blockTri (blk2 r) ↔
      GlobalTheory.LevIdx.locHom q V F g ∈ GlobalTheory.SplitWeil.KO k _ ∧
        ∀ i j, ValuativeRel.valuation k ((GlobalTheory.LevIdx.locHom q V F g).val (Sum.inr i) (Sum.inl j)) < 1 := by
  obtain ⟨π', hπ, hred, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D k q PP hPP
  obtain ⟨y, hy⟩ := hst
  have h1 := locHom_eq q hπ V t g β y hy F e hM
  have h2 := locHom_eq q hπ V t g⁻¹ β y⁻¹ (frGL_inv hy) F e hM
  have hK : GlobalTheory.LevIdx.locHom q V F g ∈ GlobalTheory.SplitWeil.KO k _ := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [h1]; exact hred.int _
    · rw [← (GlobalTheory.LevIdx.locHom q V F).map_inv, h2]; exact hred.int _
  have h3 : Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (t⁻¹ * g * t)) = Formalism.UG.bc (resS D.host.F PP) y :=
    (congrArg (Formalism.L2.DIV.redFn β PP) hy.symm).trans (redFn_frGL β PP y)
  rw [h3, mem_blockTri, h1]
  constructor
  · intro h
    refine ⟨hK, fun i j => (hred.ker _).1 (h (e (Sum.inr i)) (e (Sum.inl j)) ?_)⟩
    simp [blk2, hl j, (hr i).not_gt]
  · rintro ⟨-, h⟩ i j hij
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i
    · simp [blk2, hl i] at hij
    rcases j with j | j
    · exact (hred.ker _).2 (h i j)
    · simp [blk2, (hr i).not_gt, (hr j).not_gt] at hij



theorem red_iff_levTop {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : QGeo v B PP)
    (δ : G.kˣ →* ℂˣ) (hδ : GlobalTheory.SplitWeil.IsTame δ) (η : ℕ → G.kˣ →* ℂˣ) (g : GA D c.T)
    (hst : Formalism.IndefR.Lev.finE c.T (B.bT⁻¹ * g * B.bT) ∈ Formalism.L2.DIV.St B.βT) :
    Formalism.L2.DIV.redFn B.βT PP (Formalism.IndefR.Lev.finE c.T (B.bT⁻¹ * g * B.bT)) ∈ blockTri (blk2 D.R.r) ↔
      ∀ x, (mt c.T g).map G.q.pr = G.FT.β * Units.val x * G.FT.γ → x ∈ (G.T δ hδ η).levTop.J := by
  obtain ⟨e, he, hM⟩ := G.frameTop
  have hs := G.hs
  have hk : D.R.r = D.R.k + (G.s + 1) := by
    unfold Ranks.r
    omega
  refine (red_iff G.q PP G.idem c.T B.bT g B.βT G.FT e hM _ (fun a => ?_) (fun a => ?_) hst).trans ?_
  · rw [he, hk]
    rcases a with a | a
    · exact lt_of_lt_of_le a.2 (Nat.le_add_right _ _)
    · exact Nat.add_lt_add_left a.2 _
  · rw [he, hk]
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  · refine (mem_twist_levTop δ hδ η _).symm.trans ⟨fun h x hx => ?_, fun h => h _ ?_⟩
    · obtain rfl := (GlobalTheory.LevIdx.eq_locHom_iff G.q c.T G.FT g x).1 hx
      exact h
    · exact (GlobalTheory.LevIdx.eq_locHom_iff G.q c.T G.FT g _).2 rfl

theorem levS_split (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) (κ : GA D V) :
    κ ∈ levS V β L ↔ κ ∈ levS V β { L with Q := ∅, xq := ξ } ∧
      ∀ PP ∈ L.Q, Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V κ) ∈ blockTri (blk2 L.r) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨a, b, c, d⟩ := mem_parLev.1 h2
    exact ⟨⟨h1, mem_parLev.2 ⟨a, b, c, fun PP hP => absurd hP (Finset.notMem_empty PP)⟩, h3⟩, d⟩
  · rintro ⟨⟨h1, h2, h3⟩, d⟩
    obtain ⟨a, b, c, -⟩ := mem_parLev.1 h2
    exact ⟨h1, mem_parLev.2 ⟨a, b, c, d⟩, h3⟩

end GlobalTheory.TopAgree

namespace GlobalTheory.TopAgree


end GlobalTheory.TopAgree

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QVal.LevCO

variable {D : D7}

theorem isCO_iSup_map (V : HSp D) {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i))
    (hq : Function.Injective fun i => (q i).v) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i)) (gl : ∀ i, GL (Y i) (k i) →* GA D V)
    (hgl : ∀ i g, SuppAt (q i).e V (gl i g) ∧ (mt V (gl i g)).map (q i).pr = (F i).β * g.val * (F i).γ)
    (L : ∀ i, Subgroup (GL (Y i) (k i))) (hL : ∀ i, IsCO (L i)) :
    IsCO ((⨆ i, (L i).map (gl i)).subgroupOf (GlobalTheory.FinPl.grpAt V (fun p => ∃ i, (q i).v = p))) := by
  set P : GlobalTheory.FinPl.Pl D → Prop := fun p => ∃ i, (q i).v = p with hPdef
  have hA : GlobalTheory.FinPl.grpAt V P = GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v) := by
    congr 1
    funext p
    exact propext ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  obtain ⟨Ψ, hc, -, -, huniq⟩ := GlobalTheory.FixLev.exists_section V k q hq Y F
  let lh : ∀ i, GA D V →* GL (Y i) (k i) := fun i => GlobalTheory.FixLev.locHom (q i) V (F i)
  have hlh_self : ∀ i g, lh i (gl i g) = g := fun i g =>
    Units.ext (GlobalTheory.FixLev.frame_cancel (F i) ((GlobalTheory.FixLev.locHom_spec _ _ _ _).symm.trans (hgl i g).2))
  have hmat_ne : ∀ i j, i ≠ j → ∀ g, (mt V (gl j g)).map (q i).pr = 1 := fun i j hij g =>
    GlobalTheory.T.matrix_proj_eq_one_of_suppAt_distinct_finitePlace D (k i) (k j) (q i) (q j) V (gl j g) (fun e => hij (hq e)) (hgl j g).1
  have hlh_ne : ∀ i j, i ≠ j → ∀ g, lh i (gl j g) = 1 := fun i j hij g => Units.ext (by
    show (F i).γ * (mt V (gl j g)).map (q i).pr * (F i).β = 1
    rw [hmat_ne i j hij g, Matrix.mul_one, (F i).γβ])
  set H := ⨆ i, (L i).map (gl i) with hHdef
  have hglA : ∀ i g, gl i g ∈ GlobalTheory.FinPl.grpAt V P := fun i g =>
    GlobalTheory.T.mem_supportedSubgroup_of_suppAt_splitPlace_mem D (k i) (q i) V _ (hgl i g).1 P ⟨i, rfl⟩
  have hHL : ∀ x ∈ H, ∀ i, lh i x ∈ L i := by
    intro x hx i
    have hle : H ≤ (L i).comap (lh i) := iSup_le fun j => Subgroup.map_le_iff_le_comap.2 fun g hg => by
      show lh i (gl j g) ∈ L i
      by_cases hij : i = j
      · subst hij
        rw [hlh_self]
        exact hg
      · rw [hlh_ne i j hij]
        exact one_mem _
    exact hle hx
  let Φ : (∀ i, GL (Y i) (k i)) → GA D V := fun y => ((List.finRange r).map fun i => gl i (y i)).prod
  have hΦA : ∀ y, Φ y ∈ GlobalTheory.FinPl.grpAt V P := fun y =>
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      exact hglA i (y i)
  have hΦH : ∀ y, (∀ i, y i ∈ L i) → Φ y ∈ H := fun y hy =>
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_map_of_mem _ (hy i))
  have hΦloc : ∀ y i, (mt V (Φ y)).map (q i).pr = (F i).β * (y i).val * (F i).γ := fun y i => by
    show (mt V ((List.finRange r).map fun i => gl i (y i)).prod).map (q i).pr = _
    rw [GlobalTheory.FixLev.map_mt_list_prod, List.map_map]
    exact (GlobalTheory.FixLev.list_prod_single (fun i' => (mt V (gl i' (y i'))).map (q i).pr) i
      (fun i' hi' => hmat_ne i i' (Ne.symm hi') _) _ (List.nodup_finRange r) (List.mem_finRange i)).trans
      (hgl i (y i)).2
  have hΨΦ : ∀ y, Ψ y = Φ y := fun y => huniq (Φ y) (by rw [← hA]; exact hΦA y) y (hΦloc y)
  have hx_eq : ∀ x ∈ GlobalTheory.FinPl.grpAt V P, Ψ (fun i => lh i x) = x := fun x hx =>
    huniq x (by rw [← hA]; exact hx) _ fun i => GlobalTheory.FixLev.locHom_spec _ _ _ x
  have hmem : ∀ x : GlobalTheory.FinPl.grpAt V P, (x : GA D V) ∈ H ↔ ∀ i, lh i x ∈ L i := fun x =>
    ⟨fun h => hHL _ h, fun h => by rw [← hx_eq x x.2, hΨΦ]; exact hΦH _ h⟩
  refine ⟨?_, ?_⟩
  · have hset : ((H.subgroupOf (GlobalTheory.FinPl.grpAt V P) : Subgroup _) : Set (GlobalTheory.FinPl.grpAt V P)) =
        ⋂ i, (fun g : GlobalTheory.FinPl.grpAt V P => lh i g.1) ⁻¹' (L i : Set _) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_iInter, Set.mem_preimage]
      exact hmem g
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      (hL i).1.preimage ((GlobalTheory.FixLev.continuous_locHom _ _ _).comp continuous_subtype_val)
  · rw [Subtype.isCompact_iff]
    have himg : (((↑) : GlobalTheory.FinPl.grpAt V P → GA D V) ''
        ((H.subgroupOf (GlobalTheory.FinPl.grpAt V P) : Subgroup _) : Set (GlobalTheory.FinPl.grpAt V P))) =
        Ψ '' Set.pi Set.univ fun i => (L i : Set _) := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : (x : GA D V) ∈ H := Subgroup.mem_subgroupOf.1 hx
        exact ⟨fun i => lh i x, fun i _ => hHL _ hx' i, hx_eq x x.2⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨⟨Ψ y, ?_⟩, ?_, rfl⟩
        · rw [hΨΦ]
          exact hΦA y
        · show Ψ y ∈ H
          rw [hΨΦ]
          exact hΦH y fun i => hy i (Set.mem_univ _)
    rw [himg]
    exact (isCompact_univ_pi fun i => (hL i).2).image hc

theorem isCO_levJ_levB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin r → QStep S),
    Function.Injective (fun i => (Q i).q.v) → IsCO (levJ Q) ∧ IsCO (levB Q) := by
  intro D ψ σ S r Q hinj
  exact ⟨isCO_iSup_map S.J.W (fun i => (Q i).k) (fun i => (Q i).q) hinj _ (fun i => (Q i).F.G₁) (fun i => (Q i).gl₁)
      (fun i g => (Q i).loc₁ g) (fun i => (Q i).L₁.J) (fun i => (Q i).co₁),
    isCO_iSup_map S.B'.V (fun i => (Q i).k) (fun i => (Q i).q) hinj _ (fun i => (Q i).F.G₂) (fun i => (Q i).gl₂)
      (fun i g => (Q i).loc₂ g) (fun i => (Q i).L₂.J) (fun i => (Q i).co₂)⟩

end GlobalTheory.QVal.LevCO

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.selfDualLattice_splitsOff_unitNormLine_at_place : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D), IsLineVec L ζ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → SplitsAt o M v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.SplitOff.splitsAt | exact GlobalTheory.Core.Mi.LatMatch.SplitOff.splitsAt | (intros; apply GlobalTheory.Core.Mi.LatMatch.SplitOff.splitsAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.exists_normOneIdele_of_supported_rankOneUnitary : ∀ (D : D7) (L : HSp D) (v : GlobalTheory.FinPl.Pl D) (γ : GA D L), L.rank = 1 → γ ∈ grpAt L (· = v) → ∃ c : AE D, NormOneAt v c ∧ NormOneAt v (cA D c) ∧ Formalism.L2.Theta.mt L γ = c • (1 : Matrix (Fin L.rank) (Fin L.rank) (AE D)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.exists_normOneAt_of_rank_one | exact GlobalTheory.Core.Mi.LatMatch.exists_normOneAt_of_rank_one | (intros; apply GlobalTheory.Core.Mi.LatMatch.exists_normOneAt_of_rank_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.normOne_matchesIsotropicY_of_matchesIsotropicX : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D), IsSelfDualC S L → IsSelfDualC S L' → MonoAt d L M v → MonoAt d L' M' v → NormOneAt v c → (∀ i, ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v))) → ∀ i, ∀ a ∈ idAt D (· = v), (colMul d.jY i a ∈ latV S L (· = v) ↔ colMul d.jY i (c * a) ∈ latV S L' (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.dualLine_match | exact GlobalTheory.Core.Mi.LatMatch.dualLine_match | (intros; apply GlobalTheory.Core.Mi.LatMatch.dualLine_match <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.exists_normOneIdele_with_splitPlace_component : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (c₀ : k), c₀ ≠ 0 → ∃ c : AE D, NormOneAt p.v c ∧ p.pr c = c₀ := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.exists_normOneAt_pr | exact GlobalTheory.Core.Mi.LatMatch.exists_normOneAt_pr | (intros; apply GlobalTheory.Core.Mi.LatMatch.exists_normOneAt_pr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (L L' : Lat S) (c : AE D) (g : GA D S), IsSelfDualC S L → IsSelfDualC S L' → NormOneAt p.v c → (∀ x : Fin S.rank → k, (fun i => p.sec (x i)) ∈ latV S L (· = p.v) ↔ (fun i => p.sec ((p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x)) i)) ∈ latV S L' (· = p.v)) → SMoves S c g L L' p.v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.sMoves_of_wComp | exact GlobalTheory.Core.Mi.LatMatch.sMoves_of_wComp | (intros; apply GlobalTheory.Core.Mi.LatMatch.sMoves_of_wComp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.rowLattice_selfDual_components_rescaled_word_frame : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → IsSelfDualC (D.sp.Y 0) (latS D) ∧ (∀ y ∈ latS D, ∀ i, (fun r => (B.d.qX *ᵥ y) i * B.d.e r i) ∈ latS D ∧ (fun r => (B.d.qY *ᵥ y) i * B.d.e' r i) ∈ latS D) ∧ (∀ (i : Fin D.R.rS) (t : D.host.E), t • (fun r => B.d.e r i) ∈ latS D ↔ GlobalTheory.Core.SBesEx.scl μ lam i * t ∈ aaD D i) ∧ ∀ (i : Fin D.R.rS) (t : D.host.E), t • (fun r => B.d.e' r i) ∈ latS D ↔ (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * t ∈ (aaD D i)⁻¹ := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.latS_rescaled_frame | exact GlobalTheory.Core.Mi.LatMatch.latS_rescaled_frame | (intros; apply GlobalTheory.Core.Mi.LatMatch.latS_rescaled_frame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.selfDual_lineStable_lattice_splitsAlongWitt_selfDualCore : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S), IsSelfDualC S L → (∀ y ∈ L, ∀ i, (fun r => (d.qX *ᵥ y) i * d.e r i) ∈ L ∧ (fun r => (d.qY *ᵥ y) i * d.e' r i) ∈ L) → IsSelfDualC S₀ (coreLat d L) ∧ ∀ v : GlobalTheory.FinPl.Pl D, MonoAt d L (coreLat d L) v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt | exact GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt | (intros; apply GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.splitPlaceComponent_monomialLattice_splitCore : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E) (L : Lat S) (M : Lat S₀) (N : Lat A) (α α' : Fin ρ → D.host.E) (μ : D.host.E) (g : GA D A), MonoAt d L M p.v → (∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jX i a ∈ latV S L (· = p.v) ↔ incA D (α i) * a ∈ intAt D (· = p.v)) → (∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jY i a ∈ latV S L (· = p.v) ↔ incA D (α' i) * a ∈ intAt D (· = p.v)) → LineAt (vecB o ζ) μ M p.v → SplitsAt o M p.v → TraceAt o g N M p.v → WShape p d o ζ L (fun i => p.pr (incA D (α i))) (fun i => p.pr (incA D (α' i))) (p.pr (incA D μ)) g N := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.wShape_of_mono | exact GlobalTheory.Core.Mi.LatMatch.wShape_of_mono | (intros; apply GlobalTheory.Core.Mi.LatMatch.wShape_of_mono <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem tuplePlace_under_not_mem_tP : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ PP, QAll W PP → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ v.tP := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a y m b₀ k _ _ _ _ ι v o l bas _ _ _ _ _ _ _ _ htP _ _ _ _ FY sc _ PP hQ hmem
  obtain ⟨t, ht⟩ := hQ
  apply (hP.bot.hyp.2.2.2.1.lev.Q_off t PP ht).2 u
  have h1 := (htP _).1 hmem
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast] at h1
  exact h1

end GlobalTheory
end
