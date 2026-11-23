module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle512
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle124
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle311
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle326
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle429
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle509
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle510
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle511
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.KRamT

open _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia

section Entry
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

theorem tr_one {E K ι : Type} [Field E] [NumberField E] [Field K] [Fintype ι] {n : ℕ} (S : GStep E K n)
    (emb : ι → E →+* K) (σ : K →+* ℂ) (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  funext y
  simp only [GStep.tr, map_one, trFr_apply, inv_one, Units.val_one, map_one, one_mul]
  exact congrArg F (frMul_one emb σ y)

theorem ent_dia (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {b : (I.stp u a i).β}
    {b' : (I.stp u a (i + 1)).β} (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ) :
    ent I l u a i (((I.atIn u a).A i).dia b P s p) (((I.atIn u a).A (i + 1)).dia b' P s p') = ent I l u a i p p' := by
  unfold ent
  rw [(GlobalTheory.KerDia.RhoDia.rho_dia I l u a i b p b' p' P s).1, (GlobalTheory.KerDia.RhoDia.rho_dia I l u a i b p b' p' P s).2,
    GlobalTheory.DiaTheta.th_dia I l u a i b b' p p' P s]

theorem Kmap_stab (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (g : (I.stp u a (i + 1)).Stab c')
    (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ) (hf : f ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i)) :
    (I.stp u a (i + 1)).tr B.fields.emb B.embLL c'.1 g.1 ((I.chain l u a).Kmap i c c' f) = (I.chain l u a).Kmap i c c' f := by
  rw [GlobalTheory.KerDia.Kmap_eq]
  have e3 := GlobalTheory.T.kernelEntry_rationalEquivariance_transports I l hI u a i ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') 1 g.1 f
    (GlobalTheory.KerDia.sharp_mem_range I l u a i hi f hf)
  have hg : (I.stp u a (i + 1)).act c'.1 g.1 ((I.stp u a (i + 1)).rep c') = (I.stp u a (i + 1)).rep c' := g.2
  have h1 : (I.stp u a i).act c.1 1 ((I.stp u a i).rep c) = (I.stp u a i).rep c :=
    @one_smul _ _ _ (GStep.actD _ c.1) _
  rw [h1, hg, tr_one] at e3
  exact e3.symm

theorem K_mem_Fi (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) :
    ∀ φ ∈ (I.stp u a i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i),
      (I.chain l u a).K i φ ∈ (I.stp u a (i + 1)).Fi B.fields.emb B.embLL (lamT (B.hcW u) (i + 1)) := by
  intro φ hφ c'
  let _ := (I.chain l u a).clsFin i
  have hK : (I.chain l u a).K i φ c' = ∑ c, (I.chain l u a).wt i c • (I.chain l u a).Kmap i c c' (φ c) := rfl
  rw [hK]
  refine ⟨Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _
    (GlobalTheory.AdForm.Keep.kmap_val I l u a i hi c c' _ (hφ c).1), fun g => ?_⟩

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, Kmap_stab I l hI u a i hi c c' g _ (hφ c).1]

end Entry
end GlobalTheory.KRamT

namespace GlobalTheory.KRamT

open _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia

section Dia
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

theorem entry_dia (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (φ : ColT I l u a i) (hφ : φ ∈ (I.fm l u a).Fi i) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ)
    (L : (I.chain l u a).cls i) (c' : (I.chain l u a).cls (i + 1)) :
    (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).Kmap i ((I.fm l u a).dil i v s L) ((I.fm l u a).dil (i + 1) v s c')
      (φ ((I.fm l u a).dil i v s L))) =
    (I.chain l u a).Kmap i L c' ((I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) := by
  have hφ' : φ ∈ (I.stp u a i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i) := hφ
  change (I.atIn u a).dilT B.fields.emb B.embLL (i + 1) v s c'
      ((I.chain l u a).Kmap i ((I.atIn u a).dil i v s L) ((I.atIn u a).dil (i + 1) v s c')
        (φ ((I.atIn u a).dil i v s L))) =
    (I.chain l u a).Kmap i L c' ((I.atIn u a).dilT B.fields.emb B.embLL i v s L (φ ((I.atIn u a).dil i v s L)))
  have hx : φ ((I.atIn u a).dil i v s L) ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) :=
    (hφ' ((I.atIn u a).dil i v s L)).1
  rw [Kmap_eq I l u a i _ _, Kmap_eq I l u a i L c']
  unfold AtIn.dilT AtIn.dil GStep.trTo
  have e1 := (I.stp u a i).mv_smul L.1 (((I.atIn u a).A i).diaPt v s L)
  have e2 := (I.stp u a (i + 1)).mv_smul c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')
  have e3 := GlobalTheory.T.kernelEntry_rationalEquivariance_transports I l hI u a i
    ((I.stp u a i).rep ((I.stp u a i).cl L.1 (((I.atIn u a).A i).diaPt v s L)))
    ((I.stp u a (i + 1)).rep ((I.stp u a (i + 1)).cl c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')))
    ((I.stp u a i).mv L.1 (((I.atIn u a).A i).diaPt v s L))
    ((I.stp u a (i + 1)).mv c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')) _
    (GlobalTheory.KerDia.sharp_mem_range I l u a i hi _ hx)
  unfold GStep.act at e3
  rw [e1, e2] at e3
  refine Eq.trans e3.symm ?_
  exact LinearMap.congr_fun (ent_dia I l u a i ((I.stp u a i).rep L) ((I.stp u a (i + 1)).rep c') v s) _

def dilEquiv (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ) :
    (I.chain l u a).cls i ≃ (I.chain l u a).cls i where
  toFun := (I.fm l u a).dil i v s
  invFun := (I.fm l u a).dil i v s⁻¹
  left_inv c := by rw [← (I.fm l u a).dil_mul, inv_mul_cancel, (I.fm l u a).dil_one]
  right_inv c := by rw [← (I.fm l u a).dil_mul, mul_inv_cancel, (I.fm l u a).dil_one]

theorem dia_K_eq (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ)
    (φ : ColT I l u a i) (c' : (I.chain l u a).cls (i + 1)) :
    (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).K i φ ((I.fm l u a).dil (i + 1) v s c')) =
      ∑ L ∈ @Finset.univ _ ((I.chain l u a).clsFin i), (I.chain l u a).wt i L • (I.fm l u a).dilT (i + 1) v s c'
        ((I.chain l u a).Kmap i ((I.fm l u a).dil i v s L) ((I.fm l u a).dil (i + 1) v s c') (φ ((I.fm l u a).dil i v s L))) := by
  letI := (I.chain l u a).clsFin i

  simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, map_sum, map_smul]
  refine (Equiv.sum_comp (dilEquiv I l u a i v s) _).symm.trans (Finset.sum_congr rfl fun L _ => ?_)
  have h : (I.chain l u a).wt i ((I.fm l u a).dil i v s L) = (I.chain l u a).wt i L := by
    unfold ColumnChain.wt
    rw [(I.fm l u a).dil_stab]
  show (I.chain l u a).wt i ((I.fm l u a).dil i v s L) • _ = _
  rw [h]
  rfl

end Dia

theorem kernel_keeps_ramT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ φ : ColT I l u a i, RamT i φ → RamT (i + 1) ((I.chain l u a).K i φ) := by
  intro B X I hI _ l _ u a i hi φ hR
  letI := (I.chain l u a).clsFin i
  refine ⟨K_mem_Fi I l hI u a i hi φ hR.1, fun v c' => ?_⟩
  letI := (I.atT l u a).FvFin v
  letI := (I.atT l u a).FvDec v
  have hsum : ∑ s : ((I.atT l u a).Fv v)ˣ,
      (fun L => (I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) = 0 := by
    funext L
    rw [Finset.sum_apply, ← finsum_eq_sum_of_fintype]
    exact hR.2 v L
  have hterm : ∀ s : ((I.atT l u a).Fv v)ˣ,
      (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).K i φ ((I.fm l u a).dil (i + 1) v s c')) =
        (I.chain l u a).Klin i (fun L => (I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) c' := by
    intro s
    refine (dia_K_eq I l u a i v s φ c').trans ?_
    show _ = ∑ L, (I.chain l u a).wt i L • (I.chain l u a).Kmap i L c'
      ((I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L)))
    exact Finset.sum_congr rfl fun L _ => congrArg ((I.chain l u a).wt i L • ·)
      (entry_dia I l hI u a i hi φ hR.1 v s L c')
  rw [finsum_eq_sum_of_fintype]
  simp only [hterm]

  rw [← Finset.sum_apply, ← map_sum, hsum, map_zero]
  rfl

end GlobalTheory.KRamT
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
open GlobalTheory.LiftRows (Given)
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.ChainTw.VolScale

theorem scale {D : D7} (V : HSp D)
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure) (K₁ K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν₁ ν₀ : Measure (GA D V)) :
    K₁ ≤ K₀ → K₀ ≤ UA D.sp.cm V.gram → K₁.relIndex K₀ ≠ 0 → MeasurableSet {g : GA D V | Lev.finE V g ∈ K₁} →
    Lev.IsMeasLevW V K₁ good ν₁ → Lev.IsMeasLevW V K₀ good ν₀ → ν₁ = (K₁.relIndex K₀ : ℝ≥0∞) • ν₀ := by
  intro hle hUA hne hmeas h₁ h₀
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := GlobalTheory.RealMeasOne.ginfC_facts V
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨hH₁, ⟨θ, hθ⟩, k1⟩ := h₁
  obtain ⟨⟨A, hA⟩, k1⟩ := k1 θ hθ
  obtain ⟨⟨m, hm⟩, k1⟩ := k1 A hA
  obtain ⟨hH₀, -, k0⟩ := h₀
  obtain ⟨-, k0⟩ := k0 θ hθ
  obtain ⟨-, k0⟩ := k0 A hA
  have k0 := k0 m hm
  haveI := hH₁
  haveI := hH₀
  let B : ∀ ρ : D.what₂.Tau, TopologicalSpace.PositiveCompacts (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) :=
    fun ρ => Classical.arbitrary _
  have hB : ∀ ρ, MeasurableSet (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)) := fun ρ =>
    (B ρ).isCompact.measurableSet
  let S : Set (GA D V) := {h | ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hSc : IsClosed S := by
    have e : S = ⋂ ρ, (fun h => A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h) ⁻¹'
        ((fun b => UpqT.mat b * A ρ) '' (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))) := by
      ext h
      simp only [Set.mem_iInter]
      exact Iff.rfl
    rw [e]
    refine isClosed_iInter fun ρ => IsClosed.preimage ?_ ?_
    · exact continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat (σ := D.sp.cm.sig) V.gram (hθ ρ))
    · exact ((B ρ).isCompact.image ((GlobalTheory.UpqTopology.continuous_mat).matrix_mul continuous_const)).isClosed
  have hS : MeasurableSet S := hSc.measurableSet
  let E : Set (GinfC V) := Subtype.val ⁻¹' S
  have hE : MeasurableSet E := measurable_subtype_coe hS
  have hpre : GlobalTheory.AutMult.toInf V ⁻¹' E = S := by
    ext h
    simp only [E, S, Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.RealMeasOne.infMat_toInf]
  have hset : ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), {g : GA D V | Lev.finE V g ∈ K} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E =
      {h | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} := by
    intro K
    rw [hpre]
    rfl
  have v1 : ν₁ ({g : GA D V | Lev.finE V g ∈ K₁} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) = ∏ ρ, m ρ (B ρ) :=
    (congrArg ν₁ (hset K₁)).trans (k1 m hm (fun ρ => B ρ) hB)
  have v0 : ν₀ ({g : GA D V | Lev.finE V g ∈ K₀} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) = ∏ ρ, m ρ (B ρ) :=
    (congrArg ν₀ (hset K₀)).trans (k0 (fun ρ => B ρ) hB)
  have hI := GlobalTheory.T.relIndex_mul_measure_adelicLevelSet D V ν₀ K₁ K₀ E hle hUA hne hmeas hE
  rw [v0] at hI
  have h0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (Measure.measure_pos_of_nonempty_interior (m ρ) (B ρ).interior_nonempty).ne'
  have ht : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (B ρ).isCompact.measure_lt_top.ne
  set x := ν₀ ({g : GA D V | Lev.finE V g ∈ K₁} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) with hx
  have hx0 : x ≠ 0 := fun h => h0 (by rw [← hI, h, mul_zero])
  have hxt : x ≠ ⊤ := fun h => ht (by rw [← hI, h]; exact ENNReal.mul_top (by exact_mod_cast hne))
  have e : ν₁ = ((Measure.haarScalarFactor ν₁ ν₀ : NNReal) : ENNReal) • ν₀ := Measure.isMulLeftInvariant_eq_smul ν₁ ν₀
  have e' := v1
  rw [e, Measure.smul_apply, smul_eq_mul, ← hI] at e'
  have hc : ((Measure.haarScalarFactor ν₁ ν₀ : NNReal) : ENNReal) = (K₁.relIndex K₀ : ℝ≥0∞) :=
    (ENNReal.mul_left_inj hx0 hxt).1 e'
  rw [e, hc]

theorem vol_step {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L₁ L₀ : LevDat D.host.E ℂ V.rank)
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure) (ν₁ ν₀ : Measure (GA D V)) (N : ℝ)
    (hle : lev D.sp.cm V.gram β L₁ ≤ lev D.sp.cm V.gram β L₀)
    (hN : (((lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) : ℕ) : ℝ) = N) (hN0 : 0 < N)
    (hmeas : MeasurableSet {g : GA D V | Lev.finE V g ∈ lev D.sp.cm V.gram β L₁})
    (h₁ : Lev.IsMeasLevW V (lev D.sp.cm V.gram β L₁) good ν₁) (h₀ : Lev.IsMeasLevW V (lev D.sp.cm V.gram β L₀) good ν₀) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν₁ = GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν₀ * N ∧ 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν₁ := by
  have hne : (lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) ≠ 0 := by
    intro h0; rw [h0, Nat.cast_zero] at hN; linarith
  have e := scale V good hgood _ _ ν₁ ν₀ hle lev_le_UA hne hmeas h₁ h₀
  refine ⟨?_, ?_⟩
  · rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ
    have e2 : GlobalTheory.AutomorphicL2Unitary.autMeasure V (((lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) : ℝ≥0∞) • ν₀) =
        ((lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) : ℝ≥0∞) • GlobalTheory.AutomorphicL2Unitary.autMeasure V ν₀ :=
      GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul _
    rw [e2, measureReal_ennreal_smul_apply, ← hN, ENNReal.toReal_natCast, mul_comm]
  · haveI := h₁.1
    exact GlobalTheory.RallisIP.Model.vol_pos ν₁

theorem idxQ_pos {D : D7} (PP : Pl D.host.E) (j : ℕ) : 0 < idxQ PP j := by
  have hq : (0 : ℝ) < (Ideal.absNorm PP.asIdeal : ℝ) := by
    have := HeightOneSpectrum.one_lt_absNorm PP
    exact_mod_cast (Nat.zero_lt_one.trans this)
  unfold idxQ
  exact div_pos (mul_pos (pow_pos hq _) (RModel.zinv_pos PP _ _)) (mul_pos (RModel.zinv_pos PP _ _) (RModel.zinv_pos PP _ _))

theorem rVol_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F →
    (∀ h : RangeX R, RChain R h) → RangeX R → RVol R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hC hR t
  have hQ0 : (twR R A.μ0).Q = ∅ := RModel.Q_base R hG.core.lev
  have hprod : ∀ j, 0 < ∏ PP ∈ R.Q t, idxQ PP j := fun j => Finset.prod_pos fun PP _ => idxQ_pos PP j
  refine ⟨fun j hj => ?_, ?_⟩
  · have hS := (hC hR t).2.1 j hj
    obtain ⟨hr0, hL0, -⟩ := (hC hR A.μ0).2.1 j hj
    rw [hQ0] at hL0
    obtain ⟨good, hgood, hW⟩ := GlobalTheory.RealMeasOne.models_good R hG.core.models j hj
    obtain ⟨hle, hN⟩ := GlobalTheory.T.twistedLevel_relIndex_eq_prod_parabolicIndices D (comR R t) (twR R t) j (stY R t j) (hC hR t).1 hj.le hS hr0 R.chi (R.xiR A.μ0)
    have e : Lev.datY (stY R t j).V.rank D.R.r D.R.t j hr0 (twR R t).Pg ∅ (LevelP.triv _ _ _) R.chi (R.xiR A.μ0) Lev.Frm.B =
        R.datYt A.μ0 j R.triv := hL0.symm
    rw [e] at hle hN
    have hmeas := (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D (comR R t) (twR R t) (hC hR t).1 j hj.le (stY R t j) hS).1
    exact vol_step (Yc D j) (R.βY j) (R.datYt t j R.triv) (R.datYt A.μ0 j R.triv) good hgood (R.νY t j) (R.νY A.μ0 j) _
      hle hN (hprod j) hmeas (hW t) (hW A.μ0)
  · have hS := (hC hR t).2.2.1
    obtain ⟨hr0, hL0, -⟩ := (hC hR A.μ0).2.2.1
    rw [hQ0] at hL0
    obtain ⟨hle, hN⟩ := GlobalTheory.T.twistedLevel_relIndex_eq_prod_parabolicIndices D (comR R t) (twR R t) D.R.m (stX R t) (hC hR t).1 le_rfl hS hr0 R.chi (R.xiR A.μ0)
    have e : Lev.datY (stX R t).V.rank D.R.r D.R.t D.R.m hr0 (twR R t).Pg ∅ (LevelP.triv _ _ _) R.chi (R.xiR A.μ0) Lev.Frm.B =
        R.datXt A.μ0 := hL0.symm
    rw [e] at hle hN
    have hmeas := (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D (comR R t) (twR R t) (hC hR t).1 D.R.m le_rfl (stX R t) hS).1
    have h := vol_step D.sp.X' R.βX (R.datXt t) (R.datXt A.μ0) (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m)
      (fun _ _ hm => hm.1) (R.νX t) (R.νX A.μ0) _ hle hN (hprod D.R.m) hmeas (hG.core.models.νX t).1 (hG.core.models.νX A.μ0).1
    exact ⟨h.1, h.2⟩

end GlobalTheory.ChainTw.VolScale

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
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.RNrmProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rNrm_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RNrm R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG
  have hL := hG.core.lev
  have hC := hG.core.chain
  have hQ : R.Q A.μ0 = ∅ := GlobalTheory.ChainTw.RModel.Q_base R hL
  have hm := D.R.two_le_m
  intro t
  refine ⟨fun k hk m X hX => ?_, fun m X hX => ?_⟩
  · obtain ⟨c, hc⟩ := hL.βY k (by omega)
    obtain ⟨c', hc'⟩ := hL.βY (k + 1) hk
    have h1 := hC.vY t k hk
    have h2 := hC.vY A.μ0 k hk
    rw [LevCh.datYt, hQ] at h2
    rw [LevCh.datYt] at h1
    have hb : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsBase R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1)) (R.vac k) :=
      ⟨GlobalTheory.Chain.VacVec.cart_isCartanInv _, GlobalTheory.Chain.VacVec.cart_isCartanInv _,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c', hc'⟩, h1.1⟩
    have hrk : (Yc D k).rank + D.R.t = (Yc D (k + 1)).rank := by
      rw [GlobalTheory.Chain.StepVac.rank_Yc (by omega), GlobalTheory.Chain.StepVac.rank_Yc (by omega)]; ring
    have key := GlobalTheory.T.nrm2_twisted_eq_untwisted_mul_prod_zinv D R.ψ R.θ (Yc D k) (Yc D (k + 1)) _ _ _ _ _ _ (R.vac k) m X hb hX hc.1 hc'.1
      D.R.r D.R.t k D.R.t (r_le_Y k) hrk R.Pg (R.Q t) (GlobalTheory.ChainTw.RModel.disjoint_Pg_Q R.toLevCh hL t)
      (hG.guard.2 t) R.chi (R.chi (k + 1)) (R.xiR t) (R.xiR A.μ0) _ _ h1 h2
    rw [key]
    congr 1
    refine Finset.prod_congr rfl fun PP _ => ?_
    unfold volOne
    rw [GlobalTheory.Chain.StepVac.rank_Yc (by omega)]
    congr 4
    simp
  · obtain ⟨c, hc⟩ := hL.βY (D.R.m - 1) (by omega)
    obtain ⟨c', hc'⟩ := hL.βX
    have h1 := hC.vX t
    have h2 := hC.vX A.μ0
    rw [LevCh.datYt, hQ] at h2
    rw [LevCh.datYt] at h1
    have hb : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsBase R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX R.vacX :=
      ⟨GlobalTheory.Chain.VacVec.cart_isCartanInv _, GlobalTheory.Chain.VacVec.cart_isCartanInv _,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c', hc'⟩, h1.1⟩
    have hX' : D.sp.X'.rank = D.R.r + D.R.m * D.R.t := D.sp.X'_rank
    have hrk : (Yc D (D.R.m - 1)).rank + D.R.t = D.sp.X'.rank := by
      rw [GlobalTheory.Chain.StepVac.rank_Yc (by omega), hX']
      obtain ⟨n, hn⟩ : ∃ n, D.R.m = n + 1 := ⟨D.R.m - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel]; ring
    have key := GlobalTheory.T.nrm2_twisted_eq_untwisted_mul_prod_zinv D R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' _ _ _ _ _ _ R.vacX m X hb hX hc.1 hc'.1
      D.R.r D.R.t (D.R.m - 1) D.R.t (r_le_Y _) hrk R.Pg (R.Q t) (GlobalTheory.ChainTw.RModel.disjoint_Pg_Q R.toLevCh hL t)
      (hG.guard.2 t) R.chi (R.chi D.R.m) (R.xiR t) (R.xiR A.μ0) _ _ h1 h2
    rw [key]
    congr 1
    refine Finset.prod_congr rfl fun PP _ => ?_
    unfold volOne
    rw [hX']
    congr 4
    simp

end GlobalTheory.ChainTw.RNrmProof
end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsThetaFunO ψ (dblSp A) B f → sch ψ A B ν 𝓨 f ∈ fockA θ B A.rank l sB → IsFockVec ψ θ (dblSp A) B s' sB f := by
  first | exact @GlobalTheory.StdUnnFockRev.isFockVec_of_sch_mem_fockA | exact GlobalTheory.StdUnnFockRev.isFockVec_of_sch_mem_fockA | (intros; apply GlobalTheory.StdUnnFockRev.isFockVec_of_sch_mem_fockA <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftUpwards_ne_zero_of_lValue : ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → MetEx D → LevFacts D → ZetaNe D → UpNe D := by
  first | exact @GlobalTheory.ChainOnto.upNe_of_heckeForm | exact GlobalTheory.ChainOnto.upNe_of_heckeForm | (intros; apply GlobalTheory.ChainOnto.upNe_of_heckeForm <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.heckeInnerProductFormula_of_doublingEuler : ∀ D : D7, GlobalForm D → EulerRight D → HeckeForm D := by
  first | exact @GlobalTheory.Core.Rk.IP.heckeForm_of_global_euler | exact GlobalTheory.Core.Rk.IP.heckeForm_of_global_euler | (intros; apply GlobalTheory.Core.Rk.IP.heckeForm_of_global_euler <;> assumption)
end
