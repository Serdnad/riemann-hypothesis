module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle169
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

variable {D : D7}

section Scal

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def scalGL (c c' : A) (h : c * c' = 1) : GL n A where
  val := c • (1 : Matrix n n A)
  inv := c' • (1 : Matrix n n A)
  val_inv := by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, h, one_smul]
  inv_val := by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_comm, h, one_smul]

theorem scalGL_mem (σ : A →+* A) (J : Matrix n n A) (c : A) (h : c * σ c = 1) :
    scalGL (n := n) c (σ c) h ∈ Formalism.UG.UJ σ J := by
  show Formalism.UG.cT σ (c • (1 : Matrix n n A)) * J * (c • (1 : Matrix n n A)) = J
  have hm : Formalism.UG.cT σ (c • (1 : Matrix n n A)) = σ c • (1 : Matrix n n A) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h1 : j = i
    · subst h1; simp
    · rw [if_neg h1, if_neg (Ne.symm h1)]; simp
  rw [hm, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, h, one_smul]

end Scal

variable {D : D7}

def scalGA (S : HSp D) (c : AE D) (hc : c * cA D c = 1) : GA D S :=
  ⟨scalGL c (cA D c) hc, by exact scalGL_mem _ _ c hc⟩

theorem mt_scalGA (S : HSp D) (c : AE D) (hc : c * cA D c = 1) :
    Formalism.L2.Theta.mt S (scalGA S c hc) = c • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := rfl

theorem scalGA_mem_center (S : HSp D) (c : AE D) (hc : c * cA D c = 1) :
    scalGA S c hc ∈ Subgroup.center (GA D S) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply GlobalTheory.FinPlLoc.mt_inj
  rw [GlobalTheory.FinPlLoc.mt_mul, GlobalTheory.FinPlLoc.mt_mul, mt_scalGA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul]

theorem scalGA_mem_grpAt (S : HSp D) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (hc : NormOneAt v c) :
    scalGA S c hc.1 ∈ grpAt S (· = v) := by
  unfold grpAt
  rw [GlobalTheory.FinPlLoc.mem_congGrp]
  intro i j
  rw [mt_scalGA, Matrix.smul_apply, smul_eq_mul, ← sub_one_mul]
  exact Ideal.mul_mem_right _ _ hc.2

theorem exists_cenAt_scalar : ∀ (D : D7) (S : HSp D) (v : GlobalTheory.FinPl.Pl D) (c : AE D), NormOneAt v c → ∃ z : GA D S, CenAt S v z ∧ Formalism.L2.Theta.mt S z = c • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  intro D S v c hc
  exact ⟨scalGA S c hc.1, ⟨scalGA_mem_grpAt S v c hc, scalGA_mem_center S c hc.1⟩, mt_scalGA S c hc.1⟩

end GlobalTheory.Core.Mi.LatMatch
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

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

variable {D : D7}

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    GlobalTheory.IwaPlace.hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [GlobalTheory.IwaPlace.hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_mulVec (S : HSp D) {k : ℕ} (a : Mx D S.rank k) (x : Fin S.rank → AE D) (y : Fin k → AE D) :
    GlobalTheory.IwaPlace.hermAt S x (a *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj a ⬝ gA S) *ᵥ x) := by
  have h : (fun i => cA D ((a *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj a := by
    funext i

    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hermAt_eq, h, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (adj a)]

theorem hermAt_jB {S A B : HSp D} (o : OrthDec S A B) (y : Fin S.rank → AE D) (l : Fin B.rank → AE D) :
    GlobalTheory.IwaPlace.hermAt S y (o.jB *ᵥ l) = GlobalTheory.IwaPlace.hermAt B (o.pB *ᵥ y) l := by
  rw [hermAt_mulVec, hermAt_eq, Matrix.mulVec_mulVec, o.pB_eq, ← Matrix.mul_assoc (gA B), gA_mul_giA, Matrix.one_mul]

theorem ratV_vecB {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    ratV (vecB o ζ) = o.jB *ᵥ ratV ζ :=
  funext fun i => RingHom.map_mulVec (incA D) o.iB ζ i

theorem hermAt_smul (S : HSp D) (c a : AE D) (x y : Fin S.rank → AE D) :
    GlobalTheory.IwaPlace.hermAt S (c • x) (a • y) = c * cA D a * GlobalTheory.IwaPlace.hermAt S x y := by
  simp only [GlobalTheory.IwaPlace.hermAt, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem hermAt_ratV (S : HSp D) (x : Fin S.rank → D.host.E) :
    GlobalTheory.IwaPlace.hermAt S (ratV x) (ratV x) = incA D (star x ⬝ᵥ S.gram *ᵥ x) := by

  simp only [GlobalTheory.IwaPlace.hermAt, gA, rat, ratV, Matrix.map_apply, dotProduct, Matrix.mulVec, map_sum, map_mul,
  Finset.mul_sum, cA_incA, Pi.star_apply, mul_assoc]

end GlobalTheory.Core.Mi.LatMatch.SplitOff

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

variable {D : D7}

theorem eps_mem_idV (v : GlobalTheory.FinPl.Pl D) :
    algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) ∈ idV (1 : FI D) v := by
  apply AddSubgroup.subset_closure
  refine ⟨GlobalTheory.SelfDualAt.indP (· = v), ?_, ?_, 1, ?_, ?_⟩
  · intro w
    rw [GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro w hw
    rw [GlobalTheory.SelfDualAt.evalV_indP, if_neg hw]
  · exact FractionalIdeal.one_mem_one _
  · rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rfl

theorem incA_mul_mem_idV (c : D.host.E) {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} {x : AE D} (hx : x ∈ idV 𝔞 v) :
    incA D c * x ∈ idV (FractionalIdeal.spanSingleton _ c * 𝔞) v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, h1, h2, a, ha, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨α, h1, h2, c * a, FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) ha, ?_⟩
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] c) * (_ ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem natInv_mul_mem_intAt {T : ℕ} {v : GlobalTheory.FinPl.Pl D} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) {x : AE D}
    (hx : x ∈ intAt D (· = v)) : incA D ((T : D.host.E)⁻¹) * x ∈ intAt D (· = v) := by
  rw [← GlobalTheory.SeeSaw.idV_one_eq_intAt] at hx ⊢
  exact GlobalTheory.SeeSaw.idV_natInv_mul_le D 1 T v hT (incA_mul_mem_idV _ hx)

end GlobalTheory.Core.Mi.LatMatch.SplitOff

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

variable {D : D7}

theorem norm_factor {μ : D.host.E} (hμ : μ ≠ 0) (T : ℕ) (N : D.host.E) (hN : N = -(μ * star μ * (T : D.host.E))) :
    (incA D (star μ⁻¹) : AE D) * incA D N = -((incA D (T : D.host.E) : AE D) * incA D μ) := by
  have hstar : star μ ≠ 0 := star_ne_zero.2 hμ
  have e : star μ⁻¹ * N = -((T : D.host.E) * μ) := by
    rw [hN, star_inv₀]
    field_simp
  rw [← map_mul, e, map_neg, map_mul]

theorem nat_ne_zero {T : ℕ} {v : GlobalTheory.FinPl.Pl D} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) : (T : D.host.E) ≠ 0 := by
  rintro h0
  apply hT
  have : T = 0 := by exact_mod_cast h0
  rw [this, Nat.cast_zero]
  exact zero_mem _

theorem cancel_mem {T : ℕ} {v : GlobalTheory.FinPl.Pl D} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) {x : AE D}
    (h : incA D (T : D.host.E) * x ∈ intAt D (· = v)) : x ∈ intAt D (· = v) := by
  have h2 := natInv_mul_mem_intAt hT h
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ (nat_ne_zero hT), map_one, one_mul] at h2

theorem line_part {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} {M : Lat S} {μ : D.host.E} {T : ℕ}
    {v : GlobalTheory.FinPl.Pl D} (hM : IsSelfDualC S M) (hμ : μ ≠ 0) (hline : LineAt (vecB o ζ) μ M v)
    (hnorm : star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E))) (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal)
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v)) (hyM : y ∈ latV S M (· = v)) (c : AE D)
    (hc : c ∈ idAt D (· = v)) (hl : o.pB *ᵥ y = c • ratV ζ) : incA D μ * c ∈ intAt D (· = v) := by
  have hεI : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) ∈ intAt D (· = v) :=
    (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).1 (eps_mem_idV v)
  have hεc := GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) c hc
  have hεε := GlobalTheory.SelfDualAt.cA_alg (D := D) (GlobalTheory.SelfDualAt.cP (· = v))
  have ha : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * incA D μ⁻¹ ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ hεI.1
  have haM := (hline _ ha).2 (by
    rw [mul_left_comm, ← map_mul, mul_inv_cancel₀ hμ, map_one, mul_one]
    exact hεI)
  have hsd := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M v hM
  have hh := ((hsd.2.2 y hy).1 hyM) _ haM
  have hXY := norm_factor (D := D) hμ T _ hnorm
  rw [ratV_vecB, ← Matrix.mulVec_smul, hermAt_jB, hl, hermAt_smul, hermAt_ratV, map_mul, hεε, cA_incA] at hh
  have key : c * (algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * incA D (star μ⁻¹)) *
      incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = -(incA D (T : D.host.E) * (incA D μ * c)) := by
    linear_combination (algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * c) * hXY -
      (incA D (T : D.host.E) * incA D μ) * hεc
  rw [key] at hh
  rw [← GlobalTheory.SeeSaw.idV_one_eq_intAt] at hh
  have h3 := neg_mem hh
  rw [neg_neg, GlobalTheory.SeeSaw.idV_one_eq_intAt] at h3
  exact cancel_mem hT h3

end GlobalTheory.Core.Mi.LatMatch.SplitOff

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

theorem splitsAt : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D), IsLineVec L ζ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → SplitsAt o M v := by
  intro D S A L o ζ M μ T v hζ hM hμ hline hnorm hT y hy
  have hsum : o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
  constructor
  · intro hyM
    have hs : ∀ j k : Fin L.rank, j = k := fun j k => Fin.ext (by have := hζ.1; omega)
    obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hζ.2
      rw [show ζ = 0 from funext hcon]
      simp
    have hl : o.pB *ᵥ y = ((o.pB *ᵥ y) i * incA D (ζ i)⁻¹) • ratV ζ := funext fun j => by
      rw [hs j i, Pi.smul_apply, smul_eq_mul, ratV, mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, mul_one]
    have hc : (o.pB *ᵥ y) i * incA D (ζ i)⁻¹ ∈ idAt D (· = v) :=
      Ideal.mul_mem_right _ _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
    have hB : o.jB *ᵥ (o.pB *ᵥ y) ∈ latV S M (· = v) := by
      have hvec : o.jB *ᵥ (o.pB *ᵥ y) = ((o.pB *ᵥ y) i * incA D (ζ i)⁻¹) • ratV (vecB o ζ) := by
        conv_lhs => rw [hl]
        rw [Matrix.mulVec_smul, ratV_vecB]
      rw [hvec]
      exact (hline _ hc).2 (line_part o hM hμ hline hnorm hT hy hyM _ hc hl)
    refine ⟨?_, hB⟩
    rw [eq_sub_of_add_eq hsum]
    exact sub_mem hyM hB
  · rintro ⟨h1, h2⟩
    rw [← hsum]
    exact add_mem h1 h2

end GlobalTheory.Core.Mi.LatMatch.SplitOff

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

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.SZ

variable {D : D7}

theorem cY_eq_repr (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (y : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h y = (X.bas.reindex (finCongr (rank_eq X h)).symm).repr y := by
  funext k
  simp [GlobalTheory.Core.SBesEx.cY, HidaSetting.crd, crdOf, Module.Basis.repr_reindex]

theorem sum_bas_mem_iff (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (ιE : I.E ≃+* D.host.E)
    (hId : ∀ x : I.E, HEq (ιE x) x) (hn : (D.sp.Y 0).rank = I.n) (bas : Module.Basis (Fin I.n) D.host.E (VS D).V)
    (hL : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0) (v : Fin (D.sp.Y 0).rank → D.host.E) :
    (∑ k, v k • bas (Fin.cast hn k)) ∈ (VS D).L0 ↔ (∑ k, v k • (VS D).frame k) ∈ (VS D).L0 := by
  subst hI
  have h2 : ∀ i, ιE (v i) = v i := fun i => eq_of_heq (hId _)
  rw [← Formalism.L2.SG.InstExistsPf.mem_Lv]
  refine Iff.trans ?_ (hL v).symm
  apply iff_of_eq
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 i]
  rfl

theorem cY_mem_latS_iff (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : GlobalTheory.Core.Mi.IdE X)
    (y : (VS D).V) : GlobalTheory.Core.SBesEx.cY X h y ∈ latS D ↔ y ∈ (VS D).L0 := by
  have hs := sum_bas_mem_iff X.B.I h X.ιE hId (rank_eq X h) X.bas X.L_eq (GlobalTheory.Core.SBesEx.cY X h y)
  have hy : (∑ k, GlobalTheory.Core.SBesEx.cY X h y k • X.bas (Fin.cast (rank_eq X h) k)) = y := by
    rw [cY_eq_repr]
    conv_rhs => rw [← (X.bas.reindex (finCongr (rank_eq X h)).symm).sum_repr y]
    simp
  rw [hy] at hs
  rw [hs]
  simp only [latS, Formalism.L2.Herm.crdLat, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Formalism.L2.Herm.crd]
  constructor
  · rintro ⟨w, hw, hwe⟩
    have : w = ∑ k, GlobalTheory.Core.SBesEx.cY X h y k • (VS D).frame k := by
      rw [← hwe]; exact ((VS D).frame.sum_equivFun w).symm
    rw [← this]; exact hw
  · intro hw
    exact ⟨_, hw, by
      rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]⟩

theorem cY_smul (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (c : D.host.E) (y : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h (c • y) = c • GlobalTheory.Core.SBesEx.cY X h y := by
  rw [cY_eq_repr, cY_eq_repr, map_smul, Finsupp.coe_smul]

end GlobalTheory.Core.Mi.LatMatch.SZ

namespace GlobalTheory.Core.Mi.LatMatch.SZ

variable {D : D7}

theorem smul_zu_mem_iff (X : HidaSetting D) (u : D.what₂.Word) (c : D.host.E) :
    c • X.zu u ∈ (VS D).L0 ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  constructor
  · intro hc
    have hfix := (X.Fu_fixed u).2.2.2.2
    apply hfix c
    have hz : (X.Fu u).z = X.zu u := X.flagZVector u
    show c • (X.Fu u).z ∈ _
    rw [hz]
    have horth : c • X.zu u ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu u).X := by
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [map_smulₛₗ, ← hz, (X.Fu u).z_orth a, smul_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [LinearMap.map_smulₛₗ₂, hx, smul_zero]
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hc, horth⟩), horth⟩
  · rintro ⟨o, rfl⟩
    have hz : X.zu u ∈ (VS D).L0 := by
      rw [X.Lam_split]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.zu_Lb u))
    have := (VS D).L0.smul_mem o hz
    simpa [algebraMap_smul] using this

theorem quad {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n D.host.E) (G : Matrix m m D.host.E) (x : n → D.host.E) :
    star x ⬝ᵥ (Mᴴ * G * M) *ᵥ x = star (M *ᵥ x) ⬝ᵥ G *ᵥ (M *ᵥ x) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end GlobalTheory.Core.Mi.LatMatch.SZ


open GlobalTheory.Core.Mi.LatMatch.SZ in
theorem GlobalTheory.Core.Mi.LatMatch.sz_tied : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → (∀ t : D.host.E, t • vecB B.o B.ζ ∈ coreLat B.d (latS D) ↔ μ * t ∈ (1 : FI D)) ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(μ * star μ * (((D.mem u).A.T : ℕ) : D.host.E)) ∧ vecB B.o B.ζ ≠ 0 := by
  intro D X h u ψ A B μ lam hId hF
  have hz : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY X h (X.zu u) := hF.z
  refine ⟨fun t => ?_, ?_, ?_⟩
  · rw [mem_coreLat, Matrix.mulVec_smul, hz, smul_smul, ← cY_smul, cY_mem_latS_iff X h hId, smul_zu_mem_iff,
      FractionalIdeal.mem_one_iff, mul_comm]
  · rw [← B.o.isoB, quad, ← B.d.iso, quad]
    change star (B.d.i₀ *ᵥ vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = _
    rw [hz, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct,
      GlobalTheory.Core.SBesEx.cY_isom D X h hId, X.zu_norm]
    simp only [smul_eq_mul]
    ring
  · intro h0
    apply B.line.2
    rw [← B.o.isoB, quad]
    change star (vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (vecB B.o B.ζ) = 0
    rw [h0]
    simp

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

namespace GlobalTheory.Core.Mi.LatMatch

theorem exists_normOneAt_of_rank_one (D : D7) (L : HSp D) (v : GlobalTheory.FinPl.Pl D) (γ : GA D L) (hr : L.rank = 1)
    (hγ : γ ∈ grpAt L (· = v)) :
    ∃ c : AE D, NormOneAt v c ∧ NormOneAt v (cA D c) ∧
      Formalism.L2.Theta.mt L γ = c • (1 : Matrix (Fin L.rank) (Fin L.rank) (AE D)) := by
  haveI hs : Subsingleton (Fin L.rank) := ⟨fun a b => Fin.ext (by have := a.2; have := b.2; omega)⟩
  let i₀ : Fin L.rank := ⟨0, by omega⟩
  set c : AE D := Formalism.L2.Theta.mt L γ i₀ i₀ with hc
  have hmat : Formalism.L2.Theta.mt L γ = c • (1 : Matrix (Fin L.rank) (Fin L.rank) (AE D)) := by
    ext i j
    rw [Subsingleton.elim i i₀, Subsingleton.elim j i₀]
    simp [hc]
  have hid : c - 1 ∈ idAt D (· = v) := by
    have h := (GlobalTheory.IwaPlace.mem_congGrp_iff L _ γ).1 hγ i₀ i₀
    simpa [hc] using h

  have hu := congrFun (congrFun (GlobalTheory.MixModel.mt_unitary L γ) i₀) i₀
  simp only [Matrix.mul_apply, Fintype.sum_subsingleton _ i₀, GlobalTheory.MixModel.adj, GlobalTheory.MixModel.gA,
    GlobalTheory.MixModel.rat, Matrix.map_apply, Matrix.transpose_apply] at hu
  have hg : HSpace.gram L i₀ i₀ ≠ 0 := by
    have := GlobalTheory.MixModel.gram_isUnit_det L
    rw [Matrix.det_eq_elem_of_subsingleton _ i₀] at this
    exact this.ne_zero
  have hgu : IsUnit (incA D (HSpace.gram L i₀ i₀)) := (Ne.isUnit hg).map _
  have h1 : cA D c * c = 1 := by
    rw [← hc] at hu
    have : (cA D c * c) * incA D (HSpace.gram L i₀ i₀) = 1 * incA D (HSpace.gram L i₀ i₀) := by
      rw [one_mul]
      calc (cA D c * c) * incA D (HSpace.gram L i₀ i₀)
          = cA D c * (incA D (HSpace.gram L i₀ i₀) * c) := by ring
        _ = incA D (HSpace.gram L i₀ i₀) := hu
    exact hgu.mul_right_cancel this
  have h2 : c * cA D c = 1 := by rw [mul_comm]; exact h1
  refine ⟨c, ⟨h2, hid⟩, ⟨?_, ?_⟩, hmat⟩
  · rw [← map_mul, h2, map_one]
  · have : cA D c - 1 = -(cA D c) * (c - 1) := by
      linear_combination h1
    rw [this]
    exact Ideal.mul_mem_left _ _ hid

end GlobalTheory.Core.Mi.LatMatch
end
