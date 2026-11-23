module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle113
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle170
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.DiaTheta

theorem decoratedPoint_move_diamondOperator_eq {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (p : PtY ST SG Q y) (P : ST)
    (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    p.mv (DecoSet.dia1 P a p.1.1.deco) = ⟨(⟨(DecoSet.dia1 P a p.1.1.deco, p.1.1.1.2), p.1.1.2⟩, p.1.2), p.2⟩ :=
  dif_pos ⟨p.1.1.2, p.2⟩

theorem xiAt_dia {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
    (u : Pr.Word) (i : ℕ) (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i)
    (p' : PtAt R sel mu cst u (i + 1)) (P : Pr.vT u) (s : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    xiAt Ch sel mu cst L u i b b' (p.mv (DecoSet.dia1 P s p.1.1.deco)) (p'.mv (DecoSet.dia1 P s p'.1.1.deco)) =
      xiAt Ch sel mu cst L u i b b' p p' := by
  rw [decoratedPoint_move_diamondOperator_eq, decoratedPoint_move_diamondOperator_eq]
  have hT := GlobalTheory.LvT.Built.levelPrimeDatum_diamond_invariant X.K p.1.1.deco p'.1.1.deco P s
  funext x
  unfold xiAt
  split_ifs with h1 h2 h3
  · unfold XiEntry
    exact congrArg (· * _) (congrFun hT x)
  · unfold XiCpl1
    exact congrArg (· * _) (congrFun hT x)
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by have := R.two_le_m; omega⟩
    show xiOver Ch sel mu cst n h3 _ _ _ x = xiOver Ch sel mu cst n h3 _ _ _ x
    unfold xiOver
    exact congrArg (· * _) (congrFun hT x)
  · rfl

end GlobalTheory.DiaTheta

namespace GlobalTheory.DiaTheta

theorem th_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Laws → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (b' : (I.stp u a (i + 1)).β) (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ), I.th u a i b b' (((I.atIn u a).A i).dia b P s p) (((I.atIn u a).A (i + 1)).dia b' P s p') = I.th u a i b b' p p' := by
  intro B X I _ u a i b b' p p' P s
  have e1 : ((I.atIn u a).A i).dia b P s p = PtY.mv p (DecoSet.dia1 P s p.1.1.deco) := rfl
  have e2 : ((I.atIn u a).A (i + 1)).dia b' P s p' = PtY.mv p' (DecoSet.dia1 P s p'.1.1.deco) := rfl
  rw [e1, e2]
  unfold TC.th thAt
  rw [xiAt_dia I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' p p' P s, decoratedPoint_move_diamondOperator_eq, decoratedPoint_move_diamondOperator_eq]
  rfl

end GlobalTheory.DiaTheta
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section
namespace GlobalTheory.KerDia.RhoDia

section Gen
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pointDeterminant_diamondOperator_invariant {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {n : ℕ}
    {ST SG Q : Finset (HeightOneSpectrum (𝓞 H.E))} (p q : DecoF H.E n ST SG Q) (P : ST) (c : (𝓞 H.E ⧸ P.1.asIdeal)ˣ)
    (hd : q.deco = DecoSet.dia1 P c p.deco) (hfr : q.fr = p.fr) : detPt H SQ q = detPt H SQ p := by
  have hN : q.deco.1.N = p.deco.1.N := by rw [hd]; rfl
  have hbe : q.deco.1.be = p.deco.1.be := by rw [hd]; rfl
  have h := ptFr_congr (p := q) (p' := p) hN hbe hfr
  unfold detPt ptIdl
  rw [h, hN]

end Gen

theorem rho_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Laws → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (p : (I.stp u a i).D b) (b' : (I.stp u a (i + 1)).β) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ), I.rho u a i b (((I.atIn u a).A i).dia b P s p) = I.rho u a i b p ∧ I.rho' u a i b' (((I.atIn u a).A (i + 1)).dia b' P s p') = I.rho' u a i b' p' := by
  intro B X I _ u a i b p b' p' P s
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LvT.Built.decoratedLatticePoint_move_diamond p P s
  obtain ⟨h1', h2', -⟩ := GlobalTheory.LvT.Built.decoratedLatticePoint_move_diamond p' P s
  have e := pointDeterminant_diamondOperator_invariant B.host I.SQ p.1.1 _ P s h1 h2
  have e' := pointDeterminant_diamondOperator_invariant B.host I.SQ p'.1.1 _ P s h1' h2'
  constructor
  · show ((rhoAt I.SQ I.C (I.xi a) i (p.mv (DecoSet.dia1 P s p.1.1.deco)).1.1 : ℂˣ) : ℂ) = ((rhoAt I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ)
    rw [rhoAt_eq, rhoAt_eq, e]
  · show ((rhoAt' I.SQ I.C (I.xi a) i (p'.mv (DecoSet.dia1 P s p'.1.1.deco)).1.1 : ℂˣ) : ℂ) = ((rhoAt' I.SQ I.C (I.xi a) i p'.1.1 : ℂˣ) : ℂ)
    rw [rhoAt'_eq, rhoAt'_eq, e']

end GlobalTheory.KerDia.RhoDia
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.AdForm.VacStd

theorem coe_latFrame_of_eq {D : D7} (S : HSp D) (hs : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (h : S = Formalism.BasicNotions.Examples₂.posSpace hs N) :
    (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank := by
  subst h
  ext x
  show x ∈ GlobalTheory.PlaceModel.latFrame _ ↔ ∀ k, IsIntegral ℤ (x k)
  rw [GlobalTheory.PlaceModel.mem_latFrame]
  exact Formalism.IndefR.Seed.FrmC.stdLat_std hs N (fun _ => false) N 0 x

theorem gram_of_eq {D : D7} (S : HSp D) (hs : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (h : S = Formalism.BasicNotions.Examples₂.posSpace hs N) : S.gram = 1 := by
  subst h
  refine Matrix.ext fun a b => ?_
  exact (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs N (fun _ => false) N 0 a b).trans
    (by
      by_cases hab : a = b
      · subst hab
        rw [Matrix.one_apply_eq]
        exact (if_pos rfl).trans (by simp [Formalism.BasicNotions.Examples₂.sgn])
      · rw [Matrix.one_apply_ne hab]
        exact if_neg hab)

theorem cartan_of_gram {D : D7} {S : HSp D} (h : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have e : gramAt D S τ = 1 := by rw [gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e]
  exact ⟨Matrix.mul_one _, by simp, by rw [Matrix.mul_one]; exact Matrix.PosDef.one⟩

end GlobalTheory.AdForm.VacStd
end
end

section

noncomputable section

namespace GlobalTheory.Core.ColRam

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (u : B.Word) (a : I.ι)


include h in
theorem col_smul (φ : ColsK I u) (b : Idx I.sel (I.tup a) (I.idx a) 0) (g : (I.stp u a 0).G b) (p : (I.stp u a 0).D b) :
    φ.1 ((I.stp u a 0).act b g p).1.1.deco = (I.stp u a 0).rho B.fields.emb (lamT (B.hcW u) 0) b g (φ.1 p.1.1.deco) :=
  StepZero.form_smul ((I.Tp a).pref u 0) (lamT (B.hcW u) 0) (StepZero.levGAt_zero (I.Tp a) (h.idx_ok a))
    (StepZero.levQAt_zero (I.Tp a) (h.idx_ok a)) φ b g p

variable (hf : ((I.stp u a 0).fam B.fields.emb (lamT (B.hcW u) 0)).Ok)

def colForm : ColsK I u →ₗ[B.fields.K] (I.stp u a 0).FormsK B.fields.emb (lamT (B.hcW u) 0) hf where
  toFun φ := ⟨fun c => φ.1 ((I.stp u a 0).rep c).1.1.deco, fun c g =>
    (col_smul I h u a φ c.1 g.1 _).symm.trans (congrArg (fun q => φ.1 q.1.1.deco) g.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem colForm_eq_zero (φ : ColsK I u) (h0 : colForm I h u a hf φ = 0) : φ = 0 := by
  apply Subtype.ext
  funext d
  obtain ⟨p, rfl⟩ := StepZero.exists_pt (Q := I.Q a) (StepZero.ysAt_zero (R := B.R) I.sel (I.tup a) (I.cst a)) d
  let b : Idx I.sel (I.tup a) (I.idx a) 0 := (StepZero.idxUnique (h.idx_ok a)).default
  have h1 : φ.1 ((I.stp u a 0).rep ((I.stp u a 0).cl b p)).1.1.deco = 0 :=
    congrFun (congrArg Subtype.val h0) ((I.stp u a 0).cl b p)
  have h2 := col_smul I h u a φ b ((I.stp u a 0).mv b p) ((I.stp u a 0).rep ((I.stp u a 0).cl b p))
  rw [show (I.stp u a 0).act b _ _ = p from (I.stp u a 0).mv_smul b p] at h2
  exact h2.trans ((congrArg _ h1).trans (map_zero _))

theorem trTo_colForm (φ : ColsK I u) (b : Idx I.sel (I.tup a) (I.idx a) 0) (p : (I.stp u a 0).D b) :
    (I.stp u a 0).trTo B.fields.emb B.embLL b p
      ((I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf φ) ((I.stp u a 0).cl b p)) =
      evV B.fields.emb (1 : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.fields.E) (lamT (B.hcW u) 0) B.embLL
        (φ.1 p.1.1.deco) := by
  have h2 := col_smul I h u a φ b ((I.stp u a 0).mv b p) ((I.stp u a 0).rep ((I.stp u a 0).cl b p))
  rw [show (I.stp u a 0).act b _ _ = p from (I.stp u a 0).mv_smul b p] at h2
  refine Eq.trans ?_ (congrArg _ h2).symm
  exact (GStep.evV_rho_eq_tr (I.stp u a 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) b _ _).symm

theorem embF_colForm_diaOp (P : (B.primes X).vT u) (e : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) (φ : ColsK I u) :
    (I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf
        (colForm I h u a hf (diaOp (Pr := B.primes X) B.wts I.Ch u 0 P e φ)) =
      (I.atIn u a).diaLin B.fields.emb B.embLL P e
        ((I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf φ)) := by
  funext c
  refine Eq.trans ?_ (trTo_colForm I h u a hf φ c.1 (((I.atIn u a).A 0).diaPt P e c)).symm
  have e1 : (((I.atIn u a).A 0).diaPt P e c).1.1.deco = DecoSet.dia1 P e ((I.stp u a 0).rep c).1.1.deco :=
    congrArg (fun q => q.1.1.deco) (PtY.mv_dia ((I.stp u a 0).rep c) P e)
  rw [e1]
  exact congrArg (evV B.fields.emb (1 : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.fields.E) (lamT (B.hcW u) 0) B.embLL)
    (LocOp.ofMap_op_apply _ _ _ _ _ φ _)

theorem embF_colForm_mem_Mram (l : I.Laws) (φ : ColsK I u) :
    (I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf φ) ∈ (I.atT l u a).Mram ↔
      φ ∈ MramV (Pr := B.primes X) B.wts I.Ch u := by
  have key : ∀ P : (B.primes X).vT u, (I.atT l u a).Nm P
      ((I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf φ)) =
      (I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf
        (colForm I h u a hf (NmOp (Pr := B.primes X) B.wts I.Ch u 0 P φ)) := by
    intro P
    have e : NmOp (Pr := B.primes X) B.wts I.Ch u 0 P φ =
        ∑ e ∈ @Finset.univ _ (Fintype.ofFinite (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ), diaOp (Pr := B.primes X) B.wts I.Ch u 0 P e φ :=
      LinearMap.sum_apply _ _ _

    rw [e, map_sum, map_sum]
    refine (LinearMap.sum_apply _ _ _).trans (Finset.sum_congr (Finset.ext fun e => ?_) fun e _ => ?_)
    · exact iff_of_true (@Finset.mem_univ _ (_) _) (@Finset.mem_univ _ (_) _)
    · exact (embF_colForm_diaOp I h u a hf P e φ).symm
  have hz : ∀ ψ : ColsK I u,
      (I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf ψ) = 0 ↔ ψ = 0 := fun ψ =>
    (map_eq_zero_iff _ (StepZero.embF_injective _ _ _ _ hf)).trans
      ⟨colForm_eq_zero I h u a hf ψ, fun h0 => by rw [h0]; exact map_zero _⟩
  constructor
  · intro hm
    refine (Submodule.mem_iInf _).2 fun P => (hz _).1 ?_
    exact (key P).symm.trans ((Submodule.mem_iInf _).1 hm.2 P)
  · intro hm
    refine ⟨StepZero.embF_mem_Fi _ _ _ _ hf _, (Submodule.mem_iInf _).2 fun P => ?_⟩
    exact (key P).trans ((hz _).2 ((Submodule.mem_iInf _).1 hm P))

theorem isCol_mem_ramSub_iff {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (_hX : B.fields.Ok) (l : I.Laws)
    (u : B.Word) (a : I.ι) (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u) (hc : IsCol I u a l x φ) :
    x ∈ (I.fm l u a).ramSub ↔ φ ∈ MramV (Pr := B.primes X) B.wts I.Ch u := by
  have hx : x = colForm I h u a ((l.fmL u a).fam 0) φ := Subtype.ext (funext hc)
  rw [hx]
  exact embF_colForm_mem_Mram I h u a ((l.fmL u a).fam 0) l φ

end GlobalTheory.Core.ColRam

end
end

section

noncomputable section

namespace GlobalTheory.Core.Ht2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core

attribute [local instance] GlobalTheory.Mem.Col2.starE

section Gen

open GlobalTheory.Mem.Col2.StepZero

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}
  (pf : ∀ b, (stepY ST y β Λ Θ pref).D b → Prop)

theorem cl_rep_reRep (k : ((stepY ST y β Λ Θ pref).reRep pf).Cl) :
    (stepY ST y β Λ Θ pref).cl k.1 (((stepY ST y β Λ Θ pref).reRep pf).rep k) = k := by
  obtain ⟨b, q⟩ := k
  exact congrArg (Sigma.mk b) (((stepY ST y β Λ Θ pref).reRep pf).rp_spec b q)

def secRe [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := by
    have e1 := clMap_cl (y := y) (Θ := Θ) (Λ₀ := Λ₀) pref lam hΛ ((clEquiv pref lam hy hΛ hΘ).symm c).1
      (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c))
    have e2 := cl_rep_reRep pref pf ((clEquiv pref lam hy hΛ hΘ).symm c)
    exact e1.symm.trans ((congrArg (clMap (Λ₀ := Λ₀) pref lam) e2).trans ((clEquiv pref lam hy hΛ hΘ).apply_symm_apply c))

theorem mem_lat_reRep [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (h : (((stepY ST y β Λ Θ pref).reRep pf).fam X.emb lam).Ok)
    (h₀ : (base ST lam Λ₀).Ok) (x : (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).V) (φ : (base ST lam Λ₀).EqFun)
    (hx : ∀ c, x.1 c = φ.1 (((stepY ST y β Λ Θ pref).reRep pf).rep c).1.1.deco) :
    x ∈ (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).L ↔ φ ∈ (base ST lam Λ₀).intDel := by
  rw [(base ST lam Λ₀).mem_intDel_iff h₀ (secRe pref lam pf hy hΛ hΘ)]
  refine (clEquiv pref lam hy hΛ hΘ).symm.surjective.forall.trans (forall_congr' fun c => ?_)
  show x.1 _ ∈ _ ↔ _
  rw [hx]
  rfl

end Gen

theorem colStep0_mem_lat : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u), IsCol I u a l x φ → (x ∈ ((I.fm l u a).lat 0).L ↔ φ ∈ MfL (Pr := B.primes X) B.wts I.Ch u) := by
  intro B X I h hX l u a x φ hc
  have hL := h.idx_ok a
  letI := StepZero.idxUnique hL
  have h₀ := colOk B.wts I.Ch hX u 0
  have key := mem_lat_reRep ((I.Tp a).pref u 0) (lamT (B.hcW u) 0) (I.pref u a 0) (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a))
    (StepZero.levGAt_zero (I.Tp a) hL) (StepZero.levQAt_zero (I.Tp a) hL) ((l.fmL u a).fam 0) h₀
  exact key x φ hc

end GlobalTheory.Core.Ht2

end
end

section

noncomputable section

namespace GlobalTheory.Core.ColZero

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.StepZero

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (pr : ∀ b, (stepY ST y β Λ Θ pref).D b → Prop)
  (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}

def clMapR (c : ((stepY ST y β Λ Θ pref).reRep pr).Cl) : (base ST lam Λ₀).Cl :=
  (base ST lam Λ₀).cls (((stepY ST y β Λ Θ pref).reRep pr).rep c).1.1.deco

theorem clMapR_cl (hΛ : ∀ b, Λ b = Λ₀) (b : β) (p : (stepY ST y β Λ Θ pref).D b) :
    clMapR (Λ₀ := Λ₀) pref pr lam (((stepY ST y β Λ Θ pref).reRep pr).cl b p) = (base ST lam Λ₀).cls p.1.1.deco := by
  have e := congrArg (fun q : (stepY ST y β Λ Θ pref).D b => q.1.1.deco) (((stepY ST y β Λ Θ pref).reRep pr).mv_smul b p)
  rw [← e]
  exact ((base ST lam Λ₀).cls_smul (down (y := y) pref hΛ b (((stepY ST y β Λ Θ pref).reRep pr).mv b p)) _).symm

theorem clMapR_bijective [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    Function.Bijective (clMapR (Λ₀ := Λ₀) pref pr lam) := by
  refine ⟨?_, fun c₀ => ?_⟩
  · rintro ⟨b, q⟩ ⟨b', q'⟩ h
    obtain rfl : b = b' := Subsingleton.elim (α := β) _ _
    obtain ⟨g₀, hg⟩ := ((base ST lam Λ₀).cls_eq_iff _ _).1 h
    obtain ⟨g, -, h2⟩ := exists_lift pref hy hΛ hΘ b _ _ g₀ hg
    congr 1
    rw [← ((stepY ST y β Λ Θ pref).reRep pr).rp_spec b q, ← ((stepY ST y β Λ Θ pref).reRep pr).rp_spec b q']
    exact Quotient.sound ⟨g, h2⟩
  · induction c₀ using Quotient.inductionOn' with
    | h d =>
      obtain ⟨p, rfl⟩ := exists_pt (Q := Q) hy d
      exact ⟨((stepY ST y β Λ Θ pref).reRep pr).cl default p, clMapR_cl pref pr lam hΛ default p⟩

def clEquivR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    ((stepY ST y β Λ Θ pref).reRep pr).Cl ≃ (base ST lam Λ₀).Cl :=
  Equiv.ofBijective _ (clMapR_bijective pref pr lam hy hΛ hΘ)

def secR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := (((stepY ST y β Λ Θ pref).reRep pr).rep ((clEquivR pref pr lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := (clEquivR pref pr lam hy hΛ hΘ).apply_symm_apply c

def formMapR (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q)
    (h : (((stepY ST y β Λ Θ pref).reRep pr).fam X.emb lam).Ok) :
    (base ST lam Λ₀).EqFun →ₗ[X.K] ((stepY ST y β Λ Θ pref).reRep pr).FormsK X.emb lam h where
  toFun φ := ⟨fun c => φ.1 (((stepY ST y β Λ Θ pref).reRep pr).rep c).1.1.deco, fun c g =>
    (form_smul pref lam hΛ hΘ φ c.1 g.1 _).symm.trans (congrArg (fun q => φ.1 q.1.1.deco) g.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem formMapR_bijective [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (h : (((stepY ST y β Λ Θ pref).reRep pr).fam X.emb lam).Ok)
    (h₀ : (base ST lam Λ₀).Ok) :
    Function.Bijective (formMapR pref pr lam hΛ hΘ h) := by
  refine ⟨fun φ ψ e => ?_, fun f => ?_⟩
  · apply ((base ST lam Λ₀).resOf h₀ (secR pref pr lam hy hΛ hΘ)).injective
    apply Subtype.ext
    funext c
    exact congrFun (congrArg Subtype.val e) ((clEquivR pref pr lam hy hΛ hΘ).symm c)
  · let f₀ : ((base ST lam Λ₀).toCSDOf h₀ (secR pref pr lam hy hΛ hΘ)).Forms :=
      ⟨fun c => f.1 ((clEquivR pref pr lam hy hΛ hΘ).symm c), fun c g₀ => by
        obtain ⟨g, h1, h2⟩ := exists_lift pref hy hΛ hΘ _ _ _ g₀.1 g₀.2
        have h3 := f.2 ((clEquivR pref pr lam hy hΛ hΘ).symm c) ⟨g, h2⟩
        have h4 := rho_eq pref lam hΛ hΘ _ g
        rw [h1] at h4
        exact (LinearMap.congr_fun h4 _).symm.trans h3⟩
    refine ⟨((base ST lam Λ₀).resOf h₀ (secR pref pr lam hy hΛ hΘ)).symm f₀, Subtype.ext (funext fun c => ?_)⟩
    obtain ⟨c₀, rfl⟩ := (clEquivR pref pr lam hy hΛ hΘ).symm.surjective c
    exact congrFun (congrArg Subtype.val
      (((base ST lam Λ₀).resOf h₀ (secR pref pr lam hy hΛ hΘ)).apply_symm_apply f₀)) c₀

end Forget

theorem exists_colZeroR {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
    {G : ChGlob X R.m} {m2 : ℕ} (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)
    (pr : ∀ b, (stepAt sel mu cst L Tp u 0).D b → Prop) (hX : X.Ok) (hL : L.Ok Ch sel mu cst G m2)
    (h : (((stepAt sel mu cst L Tp u 0).reRep pr).fam X.emb (lamT (W.hc u) 0)).Ok) :
    ∃ κ : MfV W Ch u ≃ₗ[X.K] ((stepAt sel mu cst L Tp u 0).reRep pr).FormsK X.emb (lamT (W.hc u) 0) h,
      ∀ φ c, (κ φ).1 c = φ.1 (((stepAt sel mu cst L Tp u 0).reRep pr).rep c).1.1.deco :=
  letI := idxUnique hL
  ⟨LinearEquiv.ofBijective _ (formMapR_bijective (Tp.pref u 0) pr (lamT (W.hc u) 0) (ysAt_zero sel mu cst)
    (levGAt_zero Tp hL) (levQAt_zero Tp hL) h (colOk W Ch hX u 0)), fun _ _ => rfl⟩

end GlobalTheory.Core.ColZero

namespace GlobalTheory.Core.ColZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_colEquiv {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws)
    (u : B.Word) (a : I.ι) :
    ∃ κ : ColsK I u ≃ₗ[B.fields.K] ((I.fm l u a).lat 0).V, ∀ φ, IsCol I u a l (κ φ) φ :=
  exists_colZeroR (Pr := B.primes X) B.wts (I.Tp a) u (I.pref u a 0) hX (h.idx_ok a) ((l.fmL u a).fam 0)

end GlobalTheory.Core.ColZero

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem sFinite_vol : ∀ (D : D7) (ρ m : ℕ) (vb : VolM D ρ m) (vU : VolU D ρ), SFinite vb.μ ∧ SFinite vU.ν := by
  intro D ρ m vb vU
  constructor
  · obtain ⟨i1, i2, i3, -⟩ := lattice_Mx D ρ m
    haveI : IsTopologicalAddGroup (Mx D ρ m) := i1
    haveI : LocallyCompactSpace (Mx D ρ m) := i2
    haveI : SecondCountableTopology (Mx D ρ m) := i3
    haveI : vb.μ.IsAddHaarMeasure := vb.covol.1
    haveI : SigmaFinite vb.μ := Measure.IsAddHaarMeasure.sigmaFinite _
    infer_instance
  · obtain ⟨i1, i2, -⟩ := GlobalTheory.UnitU.topology D ρ
    haveI : LocallyCompactSpace (UX D ρ) := i1
    haveI : SecondCountableTopology (UX D ρ) := i2
    haveI : vU.ν.IsHaarMeasure := vU.unit.1
    exact @MeasureTheory.instSFiniteOfSigmaFinite _ _ vU.ν (Measure.IsHaarMeasure.sigmaFinite vU.ν)

end GlobalTheory.Unf
end
end
