module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle353
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumCombinationsDifferByScalar
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZero

theorem exists_red_iff_isPat : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt G.q.e PP → ∀ g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP), (∃ x, GlobalTheory.LevZero.Red G PP x g) ↔ GlobalTheory.SymRes.IsPat D.R.rS D.R.k g := by
  intro D c v G PP hidem g
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP hidem
  have hr : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  have hρ : D.R.rS = G.S.ρ := by
    have := G.hs
    have := G.S.odd
    unfold Ranks.rS
    omega
  let π : 𝓞 D.host.E →+* G.k :=
    (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).comp (oToS D.host.F D.host.E)
  have hπ : ∀ z : 𝓞 D.host.E, π z = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := fun z =>
    h1 (incA D (z : D.host.E))
  have h : GlobalTheory.FunObj.Comparison₂.IsRed (Ideal.Quotient.mk PP.asIdeal) π :=
    ⟨h2.field, fun z => h2.int _, fun z => (iff_of_eq (congrArg (· = 0) (resS_oToS (F := D.host.F) PP z).symm)).trans (h2.ker _)⟩
  have := GlobalTheory.SymRes.exists_red_iff_isPat PP.asIdeal π h hr G.S g
  simp only [hπ] at this
  rw [hρ]
  exact this

end GlobalTheory.LevZero
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZeroFamRead
open GlobalTheory.LevZeroRead



theorem red_of_isLoc : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)), GlobalTheory.LevZero.LocAt G PP b β → b ∈ GfC (c.V 0) → ∀ (hr : D.R.r ≤ (c.V 0).rank) (g : GA D (c.V 0)) (x : G.S.P.J), (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) g (GlobalTheory.LevZeroGen.upZero G.S (Fin D.R.t) x.1) → finE (c.V 0) (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → GlobalTheory.LevZero.Red G PP x (upperLeftBlock hr (redFn β PP (finE (c.V 0) (b⁻¹ * g * b)))) := by
  intro D c v G PP b β hL hbf hr g x hg hS
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP hL.idem
  obtain ⟨e, he, hM⟩ := hL.frame (G.s + 1) (Nat.zero_add _)
  obtain ⟨m, hm⟩ := hS
  choose f hf using toEAf_onto D
  have hπ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) (Formalism.L2.Theta.AE D)), (Z.map (toEAf D)).map π' = Z.map (GlobalTheory.LocMod.ofSplit G.q).π := fun Z => by
    ext i j; exact h1 _
  have hb : ((β.val.map f).map (toEAf D)) = β.val := by ext i j; exact hf _
  have hM' := hM _ hb
  rw [← hπ, Matrix.map_mul (f := toEAf D), hb, ← finE_val] at hM'
  have hg2 := hg.2
  rw [← hπ, ← finE_val] at hg2
  have hmul : Lev.finE (c.V 0) b * β * intGL _ _ _ m =
      Lev.finE (c.V 0) g * (Lev.finE (c.V 0) b * β) := by
    have : β * intGL _ _ _ m * β⁻¹ = _ := hm
    rw [map_mul, map_mul, map_inv] at this
    rw [mul_assoc, eq_mul_of_mul_inv_eq this]
    group
  have hmul' := congrArg (fun Z : GL (Fin (c.V 0).rank) (Lev.EAf D) => Z.val.map π') hmul
  simp only [Units.val_mul] at hmul'
  rw [Matrix.map_mul (L := _ * _), Matrix.map_mul (M := _ * _), hM', hg2] at hmul'
  have key := matrix_in_frame _ _ (G.FY 0 (G.s + 1) (Nat.zero_add _)).γβ _ _ e
    (x.1.val.submatrix (GlobalTheory.StepData.ixZero _ (Fin D.R.t)).symm (GlobalTheory.StepData.ixZero _ (Fin D.R.t)).symm) _ hmul'
  have hn : (c.V 0).rank ≤ D.R.r := by
    have := Fintype.card_congr e
    simp at this
    have := G.hs
    show _ ≤ D.R.k + D.R.m - 1
    omega
  intro a b a' b' ha hb' z hz
  rw [upperLeftBlock_apply_of_eq hr hn, ← hm, redFn_frGL] at hz
  have ea : e.symm (Fin.castLE hr a') = Sum.inl a := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [he]; rcases a with a | a <;> exact ha
  have eb : e.symm (Fin.castLE hr b') = Sum.inl b := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [he]; rcases b with b | b <;> exact hb'
  have k2 := congrFun (congrFun key (Fin.castLE hr a')) (Fin.castLE hr b')
  rw [Matrix.submatrix_apply, ea, eb] at k2
  have k3 : resS D.host.F PP (m.val (Fin.castLE hr a') (Fin.castLE hr b') - oToS D.host.F D.host.E z) = 0 := by
    rw [map_sub, resS_oToS, hz]; exact sub_self _
  have k4 := (h2.ker _).1 k3
  rw [map_sub] at k4
  have k5 : π' (oToS D.host.F D.host.E z).1 = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := by
    refine Eq.trans (congrArg π' ?_) (h1 (incA D (z : D.host.E)))
    rfl
  convert k4 using 3
  · exact k2.symm
  · exact k5.symm

end GlobalTheory.LevZeroFamRead
end
end

section

open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct nonZeroDivisors

noncomputable section




namespace GlobalTheory.SeeSaw.IdeleIdeal

variable {D : D7}

theorem one_tmul_mem (o : 𝓞 D.host.E) : (1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E) ∈ intAE D :=
  GlobalTheory.FinPl.Conductor.tmul_mem (fun v => by rw [map_one]; exact one_mem _) o

theorem one_tmul_mem_iff (e : D.host.E) :
    (1 : Af D.host.F) ⊗ₜ[D.host.F] e ∈ intAE D ↔ e ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  have h : finPart D (incA D e) = (1 : Af D.host.F) ⊗ₜ[D.host.F] e := by
    change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  rw [← h]
  exact (GlobalTheory.SplitDec.int_iff (incA D e)).trans (GlobalTheory.SplitDec.rat_int_iff e)

theorem exists_int_mul (y : Af D.host.F ⊗[D.host.F] D.host.E) : ∃ N : 𝓞 D.host.E, N ≠ 0 ∧
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * y ∈ intAE D := by
  obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.FinPl.Conductor.approx y
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  have hb0 : (b : D.host.E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  rw [mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  refine add_mem ?_ (GlobalTheory.FinPl.Conductor.mul_mem_int (one_tmul_mem b) hu)
  have e : (b : D.host.E) * x = (a : D.host.E) := by
    rw [← hab]; field_simp
  rw [e]
  exact one_tmul_mem a

theorem approx_mul (z : Af D.host.F ⊗[D.host.F] D.host.E) {N : 𝓞 D.host.E} (hN : N ≠ 0) :
    ∃ x : D.host.E, ∃ u ∈ intAE D,
    z = (1 : Af D.host.F) ⊗ₜ[D.host.F] x + ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * u := by
  have hN' : (N : D.host.E) ≠ 0 := by exact_mod_cast hN
  obtain ⟨x, u, hu, e⟩ := GlobalTheory.FinPl.Conductor.approx
    (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) * z)
  refine ⟨N * x, u, hu, ?_⟩
  have h1 : ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hN']; rfl
  calc z = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) *
        (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) * z) := by rw [← mul_assoc, h1, one_mul]
    _ = _ := by rw [e, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end GlobalTheory.SeeSaw.IdeleIdeal

namespace GlobalTheory.SeeSaw.IdeleIdeal

variable {D : D7}

def subOf (y : Af D.host.F ⊗[D.host.F] D.host.E) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {d | y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D}
  add_mem' {a b} ha hb := by
    show y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a + b)) ∈ intAE D
    rw [TensorProduct.tmul_add, mul_add]; exact add_mem ha hb
  zero_mem' := by
    show y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (0 : D.host.E)) ∈ intAE D
    rw [TensorProduct.tmul_zero, mul_zero]; exact zero_mem _
  smul_mem' c d hd := by
    show y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c • d)) ∈ intAE D
    have e : y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c • d)) =
        ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) * (y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d)) := by
      rw [Algebra.smul_def, ← mul_assoc, mul_comm _ y, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e]
    exact GlobalTheory.FinPl.Conductor.mul_mem_int (one_tmul_mem c) hd

theorem mem_subOf {y : Af D.host.F ⊗[D.host.F] D.host.E} {d : D.host.E} :
    d ∈ subOf y ↔ y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D := Iff.rfl

theorem isFractional_subOf {y y' : Af D.host.F ⊗[D.host.F] D.host.E} (h : y' * y = 1) :
    IsFractional (𝓞 D.host.E)⁰ (subOf y) := by
  obtain ⟨N, hN, hNy⟩ := exists_int_mul y'
  refine ⟨N, mem_nonZeroDivisors_of_ne_zero hN, fun d hd => ?_⟩
  have e : (1 : Af D.host.F) ⊗ₜ[D.host.F] (N • d) =
      (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * y') * (y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d)) := by
    rw [mul_assoc, ← mul_assoc y', h, one_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]
  have := GlobalTheory.FinPl.Conductor.mul_mem_int hNy (mem_subOf.1 hd)
  rw [← e, one_tmul_mem_iff, Submodule.mem_one] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨r, hr⟩

def idealOf {y y' : Af D.host.F ⊗[D.host.F] D.host.E} (h : y' * y = 1) : FI D := ⟨subOf y, isFractional_subOf h⟩

theorem mem_idealOf {y y' : Af D.host.F ⊗[D.host.F] D.host.E} (h : y' * y = 1) {d : D.host.E} :
    d ∈ idealOf h ↔ y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D := Iff.rfl

end GlobalTheory.SeeSaw.IdeleIdeal


open GlobalTheory.SeeSaw.IdeleIdeal GlobalTheory.FinPlLoc in
theorem GlobalTheory.SeeSaw.exists_idealOfIdele : ∀ (D : D7) (m : (AE D)ˣ), ∃ 𝔞 : FI D, ∀ x : Pl D, ∀ a ∈ idAt D (· = x),
    a ∈ idV 𝔞 x ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D m
  set mi := finPart D ((m⁻¹ : (AE D)ˣ) : AE D) with hmi
  set mf := finPart D (m : AE D) with hmf
  have hmm : mf * mi = 1 := by
    rw [hmf, hmi, ← map_mul, Units.mul_inv, map_one]
  refine ⟨idealOf hmm, fun x a ha => ?_⟩
  have hmemA : ∀ d : D.host.E, d ∈ (idealOf hmm) ↔
      mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D := fun d => mem_idealOf hmm
  constructor
  · intro hv
    refine ⟨Ideal.mul_mem_left _ _ ha, ?_⟩
    rw [map_mul, ← hmi]
    clear ha
    induction hv using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, -, d, hd, rfl⟩ := hy
      rw [finPart_pair]
      have e : mi * (α ⊗ₜ[D.host.F] d) = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * (mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d)) := by
        rw [mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      have h1 : α ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D := by
        simpa using GlobalTheory.FinPl.Conductor.tmul_mem hα (1 : 𝓞 D.host.E)
      exact GlobalTheory.FinPl.Conductor.mul_mem_int h1 ((hmemA d).1 hd)
    | zero => rw [map_zero, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _), mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg, mul_neg]; exact neg_mem hy
  · intro hi
    have hz : mi * finPart D a ∈ intAE D := by
      have := hi.2
      rwa [map_mul, ← hmi] at this
    obtain ⟨N, hN, hNm⟩ := exists_int_mul mi
    obtain ⟨d, u, hu, e⟩ := approx_mul (finPart D a) hN
    have hd : d ∈ (idealOf hmm) := by
      rw [hmemA]
      have e2 : mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) =
          mi * finPart D a - (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * mi) * u := by
        rw [e]; ring
      rw [e2]
      exact sub_mem hz (GlobalTheory.FinPl.Conductor.mul_mem_int hNm hu)
    have hidem : (singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a = finPart D a :=
      GlobalTheory.FinPl.Conductor.idem_mul x _ fun w hw => (Submodule.mem_iInf _).1 (Ideal.mem_inf.1 ha).2 ⟨w, hw⟩
    have hε : singleV D.host.F x 1 ∈ intAf D.host.F := by
      have := GlobalTheory.FinPl.Conductor.idem_mul_mem (v := x) (α := 1) (by rw [map_one]; exact one_mem _)
      rwa [mul_one] at this
    have hsupp : ∀ (β : Af D.host.F) w, w ≠ x → evalV D.host.F w (singleV D.host.F x 1 * β) = 0 := fun β w hw => by
      rw [map_mul, GlobalTheory.FinPl.Conductor.ev_ne hw, zero_mul]

    have hrest : ∀ u ∈ intAE D, finIn D ((singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) *
        (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * u)) ∈ idV (idealOf hmm) x := by
      intro u hu
      induction hu using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨β, hβ, o, rfl⟩ := hy
        have e3 : (singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) *
            (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * (β ⊗ₜ[D.host.F] (o : D.host.E))) =
            (singleV D.host.F x 1 * β) ⊗ₜ[D.host.F] ((N : D.host.E) * o) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
        rw [e3, finIn_tmul]
        refine AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPl.Conductor.idem_mul_mem (hβ x), hsupp β, _, ?_, rfl⟩
        rw [hmemA]
        have e4 : mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : D.host.E) * o)) =
            (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * mi) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E)) := by
          rw [mul_comm _ mi, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [e4]
        exact GlobalTheory.FinPl.Conductor.mul_mem_int hNm (one_tmul_mem o)
      | zero => rw [mul_zero, mul_zero, map_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [mul_add, mul_add, map_add (f := _)]; exact add_mem hy hz
      | neg y _ hy => rw [mul_neg, mul_neg, map_neg]; exact neg_mem hy
    rw [eq_finIn (infPart_of_idAt ha), ← hidem, e, mul_add, map_add (f := _)]
    refine add_mem ?_ (hrest u hu)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, finIn_tmul]
    exact AddSubgroup.subset_closure ⟨_, hε, fun w hw => GlobalTheory.FinPl.Conductor.ev_ne hw, d, hd, rfl⟩
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw

abbrev conjR (D : D7) : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv

def conjFI (D : D7) : FI D ≃+* FI D :=
  FractionalIdeal.ringEquivOfRingEquiv D.host.E D.host.E (NumberField.RingOfIntegers.mapRingEquiv (conjR D))

theorem conj_conj_host (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  rw [← bridge_star_holds D.R D.host, ← bridge_star_holds D.R D.host, star_star]

theorem fracEquiv_conj (D : D7) (x : D.host.E) :
    IsFractionRing.ringEquivOfRingEquiv (K := D.host.E) (L := D.host.E)
      (NumberField.RingOfIntegers.mapRingEquiv (conjR D)) x = D.host.conj x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, map_div₀]
  rfl

theorem mem_conjFI {D : D7} {𝔞 : FI D} {x : D.host.E} : x ∈ conjFI D 𝔞 ↔ D.host.conj x ∈ 𝔞 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (congrArg D.host.conj (fracEquiv_conj D y)).trans (conj_conj_host D y)
    exact h.symm ▸ hy
  · intro h
    exact ⟨D.host.conj x, h, (fracEquiv_conj D _).trans (conj_conj_host D x)⟩

theorem conj_mem_conjFI {D : D7} {𝔞 : FI D} {x : D.host.E} : D.host.conj x ∈ conjFI D 𝔞 ↔ x ∈ 𝔞 := by
  rw [mem_conjFI, conj_conj_host]

theorem conjFI_AA (D : D7) : conjFI D D.host.AA = D.host.AAbar := by
  ext x
  rw [mem_conjFI]
  refine ⟨fun h => ?_, fun h => Formalism.L2.Pj.conj_mem_AA D h⟩
  simpa only [conj_conj_host] using Formalism.L2.Pj.conj_mem_AAbar D h

theorem conjFI_AA_zpow (D : D7) (n : ℤ) : conjFI D (D.host.AA ^ n) = D.host.AAbar ^ n := by
  rw [map_zpow₀, conjFI_AA]

theorem cA_tmul (D : D7) (α : AF D.host.F) (a : D.host.E) :
    cA D (α ⊗ₜ[D.host.F] a) = α ⊗ₜ[D.host.F] D.host.conj a := by
  change α ⊗ₜ[D.host.F] star a = _
  rw [bridge_star_holds D.R D.host]

theorem cA_cA (D : D7) (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => rw [cA_tmul, cA_tmul, conj_conj_host]

theorem cA_mem_idV {D : D7} {𝔞 : FI D} {v : Pl D} {s : AE D} (hs : s ∈ idV 𝔞 v) :
    cA D s ∈ idV (conjFI D 𝔞) v := by
  have hle : idV 𝔞 v ≤ (idV (conjFI D 𝔞) v).comap (cA D).toAddMonoidHom := by
    rw [idV, AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hv, a, ha, rfl⟩
    show cA D _ ∈ idV (conjFI D 𝔞) v
    rw [cA_tmul]
    exact AddSubgroup.subset_closure ⟨α, hα, hv, D.host.conj a, conj_mem_conjFI.2 ha, rfl⟩
  exact hle hs

theorem idV_cA_iff (D : D7) (v : Pl D) (𝔞 : FI D) (s : AE D) :
    s ∈ idV 𝔞 v ↔ cA D s ∈ idV (conjFI D 𝔞) v := by
  refine ⟨cA_mem_idV, fun h => ?_⟩
  have h2 := cA_mem_idV h
  rwa [cA_cA, show conjFI D (conjFI D 𝔞) = 𝔞 from by ext x; rw [mem_conjFI, conj_mem_conjFI]] at h2

theorem idV_AA_zpow_conj : ∀ (D : D7) (v : Pl D) (n : ℤ) (s : AE D),
    s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v := by
  intro D v n s
  rw [idV_cA_iff D v, conjFI_AA_zpow]

end GlobalTheory.SeeSaw
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.ChainIdeals

theorem host_ne_zero (D : D7) :
    FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ≠ 0 ∧ D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ dI D ≠ 0 := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
  · rw [h, zero_mul, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul] at hP; exact zero_ne_one hP
  · rw [dI] at h; rw [h, zero_mul] at hP; exact zero_ne_one hP

end GlobalTheory.SeeSaw.ChainIdeals
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl

theorem relIndex_KO_ne_zero {k n : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Fintype n] [DecidableEq n] (J : Subgroup (GL n k)) (hJ : IsOpen (J : Set (GL n k))) : J.relIndex (KO k n) ≠ 0 := by
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := n))
  haveI : Finite (KO k n ⧸ J.subgroupOf (KO k n)) :=
    Subgroup.quotient_finite_of_isOpen _ (hJ.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem QAt.idx_last_ne_zero : ∀ (D : D7) (c : Comm D) (v : VCom c) (χ : ℕ → (AE D)ˣ →* Circle) (Q : QAt v χ), Q.idx (Q.s + 1) ≠ 0 ∧ Q.idx (Q.s + 1 + 1) ≠ 0 := by
  intro D c v χ Q
  refine ⟨?_, ?_⟩
  · rw [Q.idx_mid (Q.s + 1) 0 rfl]
    exact relIndex_KO_ne_zero _ (Q.reg.2.2 _ _ _).1
  · rw [Q.idx_top]
    exact relIndex_KO_ne_zero _ Q.openT

end GlobalTheory.QPl
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.latticeVacuumCombinations_differ_by_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)) (o o' : WO S T →₀ ℂ) (g₀ : WO S T → ℂ), IsStdChar D ψ (-1) → IsSelfDualC S M → IsSelfDualC T M' → IsSelfDualC S N → IsSelfDualC T N' → GlobalTheory.FinPl.CombAt (· ∈ Q) o → GlobalTheory.FinPl.CombAt (· ∈ Q) o' → GlobalTheory.FinPl.Vac ψ S T M M' (· ∈ Q) g₀ → GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ Q) (comb ψ S T o g₀) → GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ Q) (comb ψ S T o' g₀) → comb ψ S T o' g₀ ≠ 0 → ∃ c : ℂ, comb ψ S T o g₀ = c • comb ψ S T o' g₀ := by
  first | exact @GlobalTheory.VacScalar.main | exact GlobalTheory.VacScalar.main | (intros; apply GlobalTheory.VacScalar.main <;> assumption)
end
