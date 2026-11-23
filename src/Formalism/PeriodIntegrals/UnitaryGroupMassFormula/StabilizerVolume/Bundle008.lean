module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation

theorem densFibInf_holds : DensFibInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet ψ _ μinf hμ νinf hν fibInf hfib Φ g
    hΦc hΦs hg
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  have hD : {S : HermR (Ainf F) σ a | IsUnit (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)).det} ∈
      𝓝 (hermOf (Ainf F) σ (gramE σ J X0) hT) :=
    (isOpen_unitHerm (Ainf F) (isOpen_units_Ainf F) σ a).mem_nhds
      (isUnit_det_hermOf (Ainf F) σ _ hT hdet)
  exact DensGen.densGen (f' := gramH (Ainf F) σ hσ J hJ.1) hfib
    (continuous_gramH (Ainf F) σ hσ J hJ.1) (fun _ => rfl) Subtype.val_injective
    (fun v hv => linIndep_of_isUnit_det (Ainf F) σ J v hv) hΦc hΦs hg Filter.univ_mem hD hD

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem exChar_holds : ExChar := by
  intro F E _ _ _ _ _ σ hE M J _hJ _ha hc a _ha1 ha2 _X0 _hT _hdet
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  have h0 : 2 * 0 < M := by omega
  have hrd : RapidDecay b (fun _ : Fin 0 → Fin M → Ainf F ⊗[F] E => (1 : ℂ)) :=
    fun N => ⟨1, fun X => by simp [sizeTup]⟩
  have hpf : IsPureFin b (fun _ : Fin 0 → Fin M → Af F ⊗[F] E => (1 : ℂ))
      (fun v (_ : Fin 0 → Fin M → Fv F v ⊗[F] E) => (1 : ℂ)) := by
    refine ⟨fun v => ⟨IsLocallyConstant.const 1, ?_⟩, Filter.Eventually.of_forall fun v => ?_,
      fun X => by simp⟩
    · exact (Set.subsingleton_of_subsingleton).isCompact
    · funext X
      simp [latV, Set.indicator]
  have hS := hc 0 h0 (0 : Matrix (Fin 0) (Fin 0) E) (fun i => Fin.elim0 i) (by simp)
    (Module.finrank F E) b (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ => 1)
    continuous_const hrd (Formalism.L2.SG.Pf.NcWeil.isSmoothCc_empty _) hpf (fun _ => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  exact ((hS.2 μ hμ).2 𝓕 h𝓕).1

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

def DensAll {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) :
    Prop :=
  ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

def FibOfDens : Prop :=
  ∀ (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V]
    [T2Space V] [SecondCountableTopology V] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T2Space Y] (μ : Measure V) (ν : Measure X),
    IsFiniteMeasureOnCompacts μ → IsFiniteMeasureOnCompacts ν → ν.IsOpenPosMeasure →
    ∀ (f : V → Y) (ι : X → Y) (U : Set V), Continuous f → IsClosedEmbedding ι →
      (∀ v, f v ∈ Set.range ι) → IsOpen U → DensAll μ f ι ν U →
      ∃ fib : X → Measure V, IsFibreFamily μ f ι U ν Set.univ fib

def TensFacts (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] : Prop :=
  LocallyCompactSpace (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧
    IsClosed (HermR R σ a : Set (Matrix (Fin a) (Fin a) (R ⊗[F] E))) ∧
    Continuous (gramR R σ J (n := a)) ∧ (∀ X, gramR R σ J (n := a) X ∈ HermR R σ a) ∧
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}

def TensAll : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  TensFacts F E σ M J a (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), TensFacts F E σ M J a (Fv F v)

def DensInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      DensAll μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {X | LinearIndependent (Ainf F ⊗[F] E) X}

def DensV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      DensAll μv (gramR (Fv F v) σ J) Subtype.val νv {X | LinearIndependent (Fv F v ⊗[F] E) X}

theorem fib_of_tens {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} {a : ℕ} {R : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] (hG : FibOfDens) (hT : TensFacts F E σ M J a R)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (hD : DensAll μ (gramR R σ J) Subtype.val ν {X | LinearIndependent (R ⊗[F] E) X}) :
    ∃ fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E),
      IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
        Set.univ fib := by
  obtain ⟨hLC, hT2, hSC, hCl, hCont, hMem, hOpen⟩ := hT
  haveI := hLC
  haveI := hT2
  haveI := hSC
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → R ⊗[F] E))
  haveI : SecondCountableTopology (HermR R σ a) := by
    first
      | infer_instance
      | exact hCl.isClosedEmbedding_subtypeVal.isInducing.secondCountableTopology
      | exact hCl.isClosedEmbedding_subtypeVal.isEmbedding.isInducing.secondCountableTopology
      | exact hCl.isClosedEmbedding_subtypeVal.toIsEmbedding.toIsInducing.secondCountableTopology
  haveI : BorelSpace (HermR R σ a) := by
    first
      | infer_instance
      | exact ⟨rfl⟩
  haveI : LocallyCompactSpace (HermR R σ a) := hCl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact hG _ _ _ μ ν inferInstance inferInstance inferInstance (gramR R σ J) Subtype.val _ hCont
    hCl.isClosedEmbedding_subtypeVal (fun v => ⟨⟨_, hMem v⟩, rfl⟩) hOpen hD

theorem fibInfEx_of (hG : FibOfDens) (hT : TensAll) (hD : DensInf) : FibInfEx := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet ψ hψ μ hμ ν hν
  exact fib_of_tens hG (hT F E σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet).1 μ ν hμ.1 hν.1
    (hD F E σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet ψ hψ μ hμ ν hν)

theorem fibVEx_of (hG : FibOfDens) (hT : TensAll) (hD : DensV) : FibVEx := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet ψ hψ v μ hμ ν hν
  exact fib_of_tens hG ((hT F E σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet).2 v) μ ν hμ.1 hν.1
    (hD F E σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet ψ hψ v μ hμ ν hν)

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

section Abstract

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]

theorem orb_mk (x0 : X) (k : G) :
    ((k : G ⧸ MulAction.stabilizer G x0)).out • x0 = k • x0 := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (MulAction.stabilizer G x0) k
  rw [hh, mul_smul, (MulAction.mem_stabilizer_iff.1 h.2)]

theorem orb_smul (x0 : X) (g : G) (q : G ⧸ MulAction.stabilizer G x0) :
    (g • q).out • x0 = g • (q.out • x0) := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  have : g • ((q.out : G) : G ⧸ MulAction.stabilizer G x0) =
      ((g * q.out : G) : G ⧸ MulAction.stabilizer G x0) := rfl
  rw [this, orb_mk, mul_smul]

end Abstract

def SecCtblG : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a _X0 _hT =>
  SecondCountableTopology (HA (AF F) σ J)

def OrbTup : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ y : Fin a → Fin M → AF F ⊗[F] E, gramR (AF F) σ J y = (gramE σ J X0).map (inclR (AF F)) →
    ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y

def StabClosed : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  IsClosed ((stabT (AF F) σ J X0 : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J))

def NuInv : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ (g : HA (AF F) σ J) (s : Set (Fin a → Fin M → AF F ⊗[F] E)), MeasurableSet s →
      νX ((fun y => g • y) ⁻¹' s) = νX s

def NuFin : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ K : Set (Fin a → Fin M → AF F ⊗[F] E), IsCompact K → νX K < ⊤

def NuNeZero : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX → νX ≠ 0

def OrbEmb : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  MeasurableEmbedding (fun q : HA (AF F) σ J ⧸ stabT (AF F) σ J X0 => q.out • ratTup (F := F) (AF F) X0) ∧
    Continuous (fun q : HA (AF F) σ J ⧸ stabT (AF F) σ J X0 => q.out • ratTup (F := F) (AF F) X0)

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def InvInv : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  (∀ μ, IsHaarH F E σ M J μ → μ.IsInvInvariant) ∧
    ∀ ψ, IsCharAF F ψ → ∀ μ, IsHaarH F E σ M J μ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
      ∀ μ' : Measure (stabT (AF F) σ J X0), μ'.IsHaarMeasure → IsCompatT F E σ M J X0 μ μ' νX →
        μ'.IsInvInvariant

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def hermO {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ) :
    AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr
    ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    intro i j k
    simp only [AddSubgroup.coe_add, Matrix.add_apply, map_add (f := _), Finsupp.add_apply]
    exact add_mem (hx i j k) (hy i j k)
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    intro i j k
    simp only [ZeroMemClass.coe_zero, Matrix.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro i j k
    simp only [NegMemClass.coe_neg, Matrix.neg_apply, map_neg, Finsupp.neg_apply]
    exact neg_mem (hx i j k)

def VolAA : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    ∀ᶠ v in cofinite,
      (∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv → μv (latV b v) = 1) ∧
      (∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv → νv (hermO b v σ a) = 1)

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def MeasOrb : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ, IsAdm F E Φ →
    Measurable fun g : HA (AF F) σ J => Φ (g • ratTup (AF F) X0)

def MeasGrp : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a _X0 _hT =>
  MeasurableMul (HA (AF F) σ J) ∧ MeasurableInv (HA (AF F) σ J)

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def LocEx : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    ∃ (μinf : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a))
      (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E))
      (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a))
      (fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E))
      (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
      SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf ∧ SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf ∧
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) ∧
      (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) ∧
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf ∧
      ∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)

def SdUniq : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μ1 μ2, SdW F E σ M J (Ainf F) (psiInf F ψ) a μ1 → SdW F E σ M J (Ainf F) (psiInf F ψ) a μ2 →
      μ1 = μ2) ∧
    (∀ ν1 ν2, SdHerm F E σ (Ainf F) (psiInf F ψ) a ν1 → SdHerm F E σ (Ainf F) (psiInf F ψ) a ν2 →
      ν1 = ν2) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      (∀ μ1 μ2, SdW F E σ M J (Fv F v) (psiV F ψ v) a μ1 → SdW F E σ M J (Fv F v) (psiV F ψ v) a μ2 →
        μ1 = μ2) ∧
      (∀ ν1 ν2, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν1 →
        SdHerm F E σ (Fv F v) (psiV F ψ v) a ν2 → ν1 = ν2)

def FibPin : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
      ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      ∀ fib1 fib2 : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fib1 →
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fib2 →
      ∀ Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φinf → HasCompactSupport Φinf →
        ∫ X, Φinf X ∂(fib1 (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
          ∫ X, Φinf X ∂(fib2 (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
      ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      ∀ fib1 fib2 : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fib1 →
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fib2 →
      ∀ Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φv →
        ∫ X, Φv X ∂(fib1 (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
          ∫ X, Φv X ∂(fib2 (hermOf (Fv F v) σ (gramE σ J X0) hT))

def MultFib : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    ∀ (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) →
    ∀ (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a)),
    (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) →
    ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))

def RestrProd : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) →
    ∀ (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a)),
    (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) →
    (∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))) →
    ∃ νX : Measure (Fin a → Fin M → AF F ⊗[F] E),
      νX {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} = 0 ∧
      ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ)
        (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
        (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
        Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
        Integrable Φ νX ∧
        ∫ X, Φ X ∂νX = (∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) *
          ∏' v, ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))

theorem exOmT_of (h1 : LocEx) (h2 : SdUniq) (h3 : FibPin) (h4 : MultFib) (h5 : RestrProd) :
    ExOmT := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c1 := h1 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c2 := h2 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c3 := h3 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c4 := h4 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c5 := h5 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  obtain ⟨μinf, νinf, μv, νv, fibInf, fibV, hμi, hνi, hμv, hνv, hfi, hfv⟩ := c1
  obtain ⟨νX, hsupp, hform⟩ :=
    c5 μinf hμi νinf hνi μv hμv νv hνv fibInf hfi fibV hfv (c4 μv hμv νv hνv fibV hfv)
  refine ⟨νX, hsupp, ⟨μinf, hμi⟩, fun μinf' hμi' => ?_⟩
  obtain rfl := c2.1 _ _ hμi hμi'
  refine ⟨⟨νinf, hνi⟩, fun νinf' hνi' => ?_⟩
  obtain rfl := c2.2.1 _ _ hνi hνi'
  refine ⟨⟨μv, hμv⟩, fun μv' hμv' => ?_⟩
  obtain rfl : μv = μv' := funext fun v => (c2.2.2 v).1 _ _ (hμv v) (hμv' v)
  refine ⟨⟨νv, hνv⟩, fun νv' hνv' => ?_⟩
  obtain rfl : νv = νv' := funext fun v => (c2.2.2 v).2 _ _ (hνv v) (hνv' v)
  refine ⟨⟨fibInf, hfi⟩, fun fibInf' hfi' => ⟨⟨fibV, hfv⟩, fun fibV' hfv' => ?_⟩⟩
  intro d b Φ Φinf Φf Φv hc1 hc2 hp hpr
  obtain ⟨hI, hF⟩ := hform d b Φ Φinf Φf Φv hc1 hc2 hp hpr
  refine ⟨hI, c4 μv hμv νv hνv fibV' hfv' d b Φf Φv hp, ?_⟩
  rw [hF, c3.1 μinf hμi νinf hνi fibInf fibInf' hfi hfi' Φinf hc1 hc2]
  congr 1
  exact tprod_congr fun v => c3.2 v (μv v) (hμv v) (νv v) (hνv v) (fibV v) (fibV' v) (hfv v)
    (hfv' v) (Φv v) (hp.1 v)

end PI.VolStabS
end
end
