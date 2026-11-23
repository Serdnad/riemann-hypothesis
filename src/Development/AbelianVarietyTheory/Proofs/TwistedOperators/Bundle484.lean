module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle448
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle245
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle184
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecay
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle190
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle349
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle004
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_latticeHom_onto_modulo_depthIdeal : OntoModEx := by
  first | exact @GlobalTheory.OntoModPf.ontoModEx | exact GlobalTheory.OntoModPf.ontoModEx | (intros; apply GlobalTheory.OntoModPf.ontoModEx <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOntoDecomp

theorem cc_span_partFull : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e} = ⊤ := by
  classical
  intro hP D hfd c hc j hj s hs
  have hmul : ∀ k ∈ s.J, ∀ k' ∈ s.J, (1 : GA D s.V → ℂ) (k * k') = (1 : GA D s.V → ℂ) k * (1 : GA D s.V → ℂ) k' :=
    fun _ _ _ _ => by simp
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M s.J (1 : GA D s.V → ℂ) c.S
    GlobalTheory.ChainOntoSph.exists_unif_of_F hc.inf hmul hs.split
  obtain ⟨hLU, -, hH⟩ := hops
  by_cases hsm : ∀ τ, s.M.sm τ ≠ ⊥
  swap
  · push_neg at hsm
    obtain ⟨τ, hτ⟩ := hsm
    refine Submodule.eq_top_iff'.2 fun u => ?_
    have h0 : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0 := by
      refine MultilinearMap.ext fun v => ?_
      rw [MultilinearMap.zero_apply]
      have hv : ((v τ : s.M.sm τ) : s.M.H τ) = 0 := (Submodule.eq_bot_iff _).1 hτ _ (v τ).2
      exact MultilinearMap.map_coord_zero (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))) τ
        (Subtype.ext hv)
    have h1 := LinearEquiv.apply_symm_apply PiTensorProduct.lift (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
    rw [h0, map_zero] at h1
    have : u = 0 := Subtype.ext h1.symm
    rw [this]
    exact zero_mem _
  have hschur := GlobalTheory.MultFinite.schurMult (θ := c.θ) (M := s.M) (J := (s.J : Set (GA D s.V)))
    (χ := (1 : GA D s.V → ℂ)) hP s.ν s.fd
  haveI := hs.haar
  have hright : s.ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds s.V s.ν hs.haar
  obtain ⟨hlin, hpos⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M (s.J : Set (GA D s.V))
    (1 : GA D s.V → ℂ) s.ν s.fd hc.inf hs.haar hs.fund hschur hsm
  obtain ⟨v0, hv0⟩ := GlobalTheory.SchurConst.exists_vec s.M hsm
  have hspec : ∀ T ∈ Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ),
      ∀ T' ∈ Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ),
      IsMultIP s.M s.ν s.fd T T' (ipM s.M s.ν s.fd T T') := fun T hT T' hT' =>
    ipM_spec _ _ _ _ _ (hschur hc.inf hs.haar hs.fund T hT T' hT')
  let φ := Submodule.equivMapOfInjective (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap
    (LinearEquiv.injective _) (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ))
  haveI : FiniteDimensional ℂ ((Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)).map
      (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap) := hfd c hc j hj s hs
  haveI : FiniteDimensional ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)) :=
    LinearEquiv.finiteDimensional φ.symm
  let I := {t : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D s.V) //
    Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S t.1 t.2.1 t.2.2}
  let op : I → Module.End ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)) := fun t =>
    (heckeOn s.M t.1.2.2).restrict fun T hT => (hH _ _ _ t.2).1 T hT
  have hcomm : ∀ i j, Commute (op i) (op j) := fun i j => by
    refine LinearMap.ext fun T => Subtype.ext ?_
    exact (hH _ _ _ i.2).2.1 _ _ _ j.2 T T.2
  have hadj : ∀ i, ∃ i', ∀ x y : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ),
      ipM s.M s.ν s.fd (op i x : MMap s.M) y = ipM s.M s.ν s.fd x (op i' y : MMap s.M) := fun i => by
    obtain ⟨R', h', hip⟩ := (hH _ _ _ i.2).2.2
    refine ⟨⟨(i.1.1, dualLab i.1.2.1, R'), h'⟩, fun x y => ?_⟩
    have h1 := hspec _ ((hH _ _ _ i.2).1 x x.2) y y.2
    have h2 := (hip s.ν s.fd hs.haar hright hs.fund hschur x x.2 y y.2 _).1 h1
    have h3 := hspec x x.2 _ ((hH _ _ _ h').1 y y.2)
    exact hasPeterssonInner_unique s.M s.ν s.fd _ _ v0 hv0 h2 h3
  have htop := GlobalTheory.OntoDecomp.iSup_jointEigenspace_eq_top
    (fun x y : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) => ipM s.M s.ν s.fd x y)
    (fun x y z a => (hlin x x.2 y y.2 z z.2 a).1) (fun x y => (hlin x x.2 y y.2 y y.2 0).2)
    (fun x hx => hpos x x.2 fun h => hx (Subtype.ext h)) op hcomm hadj
  have hsub : ∀ x : I → ℂ, ∀ T ∈ ⨅ i, (op i).eigenspace (x i), ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      (T : MMap s.M) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S e := by
    classical
    intro x T hT
    refine ⟨fun P d => if h : ∃ R, Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S P d R
      then x ⟨(P, d, h.choose), h.choose_spec⟩ else 0, ?_⟩
    rw [mem_partFull]
    refine ⟨T.2, fun P d R hR v => ?_⟩
    have hex : ∃ R, Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S P d R := ⟨R, hR⟩
    rw [dite_eq_left hex]
    have hlevT := ((GlobalTheory.MultMem.mem_mult_iff ..).1 T.2).lev v
    rw [hLU P d R hex.choose hR hex.choose_spec _ hlevT]
    have h1 := (Submodule.mem_iInf _).1 hT ⟨(P, d, hex.choose), hex.choose_spec⟩
    rw [Module.End.mem_eigenspace_iff] at h1
    exact congrArg (fun U : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) => (U : MMap s.M) v) h1
  rw [eq_top_iff]
  rintro u -
  obtain ⟨T, rfl⟩ := φ.surjective u
  have hT : T ∈ (⊤ : Submodule ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ))) := trivial
  rw [← htop] at hT
  refine Submodule.iSup_induction (fun x : I → ℂ => ⨅ i, (op i).eigenspace (x i))
    (motive := fun T => φ T ∈ Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
        partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e}) hT ?_ ?_ ?_
  · intro x T hT
    obtain ⟨e, he⟩ := hsub x T hT
    refine Submodule.subset_span ⟨e, ?_⟩
    have : ((φ T : s.CC c) : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = PiTensorProduct.lift (T : MMap s.M) := rfl
    rw [this, LinearEquiv.symm_apply_apply]
    exact he
  · rw [φ.map_zero]; exact zero_mem _
  · intro a b ha hb; rw [φ.map_add]; exact add_mem ha hb

end GlobalTheory.EvenOntoDecomp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenMetric

variable {D : D7}

theorem finDim : GlobalTheory.Published.HarishChandraFinite → ∀ D : D7, FinDim D := by
  intro hP D c hc j _ s hs
  obtain ⟨U, hU, hUJ⟩ := hs.isOpen
  have : FiniteDimensional ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) 1) :=
    GlobalTheory.MultFinite.hcFinite hP hc.inf ⟨U, hU, fun k hk hf => ⟨hUJ k hk hf, rfl⟩⟩
  exact Module.Finite.map _ _

theorem metEx : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  intro hP D c hc j _ s hs
  obtain ⟨ipD, hpure, hhermD, hposD⟩ := GlobalTheory.ChainOnto.exists_ipD_smT D s.V s.par s.M
  set J : Set (GA D s.V) := (s.J : Set (GA D s.V))
  set χ : GA D s.V → ℂ := 1
  have hS : SchurMult c.θ s.M J χ s.ν s.fd := GlobalTheory.MultFinite.schurMult hP s.ν s.fd
  obtain ⟨hI1, hI2⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M J χ s.ν s.fd hc.inf hs.haar hs.fund hS
    (GlobalTheory.GardingVec.sm_ne_bot D s.V s.par s.M)
  let T : s.CC c → MMap s.M := fun x => PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
  have hT : ∀ x : s.CC c, T x ∈ Mult c.θ s.M J χ := fun x => (mem_multT c.θ s.M J χ _).1 x.2
  have hTadd : ∀ x y : s.CC c, T (x + y) = T x + T y := fun x y => by
    simp only [T, Submodule.coe_add, map_add (f := _)]
  have hTsmul : ∀ (a : ℂ) (x : s.CC c), T (a • x) = a • T x := fun a x => by
    simp only [T, Submodule.coe_smul, map_smul]
  have hlin : ∀ x y y' : s.CC c, ∀ a : ℂ,
      ipM s.M s.ν s.fd (T x) (T y + a • T y') = ipM s.M s.ν s.fd (T x) (T y) + a * ipM s.M s.ν s.fd (T x) (T y') :=
    fun x y y' a => (hI1 _ (hT x) _ (hT y) _ (hT y') a).1
  have hsym : ∀ x y : s.CC c, ipM s.M s.ν s.fd (T y) (T x) = star (ipM s.M s.ν s.fd (T x) (T y)) :=
    fun x y => (hI1 _ (hT x) _ (hT y) _ (hT y) 0).2
  have hzero : ∀ x : s.CC c, ipM s.M s.ν s.fd (T x) (T 0) = 0 := fun x => by
    have h := hlin x 0 0 1
    rw [one_smul, one_mul, show T 0 + T 0 = T 0 by simp [T]] at h
    linear_combination -h
  have hlin' : ∀ x y y' : s.CC c, ∀ a : ℂ,
      ipM s.M s.ν s.fd (T x) (T (y + a • y')) = ipM s.M s.ν s.fd (T x) (T y) + a * ipM s.M s.ν s.fd (T x) (T y') :=
    fun x y y' a => by rw [hTadd, hTsmul]; exact hlin x y y' a
  let ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => ipM s.M s.ν s.fd (T y) (T x))
      (fun x x' y => by simpa using hlin' y x x' 1)
      (fun a x y => by
        have h := hlin' y 0 x a
        rw [zero_add, hzero, zero_add] at h
        simpa using h)
      (fun x y y' => by
        rw [hsym x (y + y'), hsym x y, hsym x y']
        have h := hlin' x y y' 1
        rw [one_mul, one_smul] at h
        rw [h, star_add])
      (fun a x y => by
        rw [hsym x (a • y), hsym x y]
        have h := hlin' x 0 y a
        rw [zero_add, hzero, zero_add] at h
        rw [h, star_mul', smul_eq_mul, starRingEnd_apply])
  have hip : ∀ x y, ip x y = ipM s.M s.ν s.fd (T y) (T x) := fun _ _ => rfl
  have hpair : ∀ x y : s.CC c, ∀ w w', IntegrableOn (fun g => PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g)) s.fd s.ν ∧
      ∫ g in s.fd, PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g) ∂s.ν = ip x y * ipD w w' := by
    intro x y
    refine GlobalTheory.ChainMetric.integ_pair (μ := s.ν) (A := s.fd) (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
      (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ipD (ip x y) ?_
    intro v v'
    obtain ⟨hi, he⟩ := ipM_spec s.M s.ν s.fd (T y) (T x) (hS hc.inf hs.haar hs.fund _ (hT y) _ (hT x)) v' v
    have e : (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v) g *
        conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v') g)) = fun g => star (T y v' g) * T x v g := by
      funext g
      rw [GlobalTheory.ChainMetric.val_tprod, GlobalTheory.ChainMetric.val_tprod, starRingEnd_apply, mul_comm]
    rw [e, hip, hpure]
    exact ⟨hi, he⟩
  refine ⟨ipD, ip, hpure, hhermD, hposD, fun x y => ?_, fun x hx => ?_, fun x y w w' => (hpair x y w w').1,
    fun x y w w' => (hpair x y w w').2⟩
  · rw [hip, hip, hsym, starRingEnd_apply]
  · rw [hip]
    refine hI2 _ (hT x) fun h0 => hx ?_
    exact Submodule.coe_eq_zero.1 ((LinearEquiv.map_eq_zero_iff _).1 h0)

theorem finDim_and_metEx : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D ∧ MetEx D :=
  fun h h' D => ⟨finDim h D, metEx h' D⟩

end GlobalTheory.EvenMetric

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitaryEmbeddingVolume

open Topology

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}




theorem isClosedEmbedding_unitaryEmbedding (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) : IsClosedEmbedding (stabilizerEmbedding d) := by
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  set P' := (frameMat B A d.ι).map (incA D)
  set Q' := (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (incA D)
  have hv : Continuous fun g : GA D B => mt B g := Units.continuous_val.comp continuous_subtype_val
  have hvi : Continuous fun g : GA D B => mt B g⁻¹ := Units.continuous_coe_inv.comp continuous_subtype_val
  let Φ : GA D B → Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E) ×
      (Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E))ᵐᵒᵖ :=
    fun g => (Q' * mt B g * P', MulOpposite.op (Q' * mt B g⁻¹ * P'))
  have hΦ : Continuous Φ :=
    ((continuous_const.matrix_mul hv).matrix_mul continuous_const).prodMk
      (MulOpposite.continuous_op.comp ((continuous_const.matrix_mul hvi).matrix_mul continuous_const))
  let φ : GA D A →* GA D B := MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)
  have hcomp : Φ ∘ stabilizerEmbedding d = (Units.embedProduct _) ∘ (fun h : GA D A => matHom A h) := by
    funext h
    have e : stabilizerEmbedding d h⁻¹ = (stabilizerEmbedding d h)⁻¹ := map_inv φ h
    simp only [Function.comp_apply, Φ, Units.embedProduct_apply]
    refine Prod.ext ?_ ?_
    · exact (GlobalTheory.UnitaryEmbeddingGroup.matA_eq d h).symm
    · show MulOpposite.op (Q' * mt B (stabilizerEmbedding d h)⁻¹ * P') = _
      rw [← e]
      exact congrArg MulOpposite.op (GlobalTheory.UnitaryEmbeddingGroup.matA_eq d h⁻¹).symm
  have hind : IsInducing (stabilizerEmbedding d) := by
    refine IsInducing.of_comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding d) hΦ ?_
    rw [hcomp]
    exact Units.isEmbedding_embedProduct.isInducing.comp (IsInducing.subtypeVal (t := ((HR (AF D.host.F) D.sp.cm.sig A.gram : Subgroup _) : Set (GL (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E)))))
  have hrange : Set.range (stabilizerEmbedding d) = {g : GA D B | mt B g * d.a.map (incA D) = d.a.map (incA D)} := by
    ext g
    constructor
    · rintro ⟨h, rfl⟩
      exact GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_fixes_vectors d h
    · intro hg
      exact GlobalTheory.UnitaryEmbeddingGroup.mem_range_of_fix d hε g hg
  have hcl : IsClosed (Set.range (stabilizerEmbedding d)) := by
    rw [hrange]
    haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
    exact isClosed_eq (hv.matrix_mul continuous_const) continuous_const
  exact ⟨⟨hind, GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_injective d⟩, hcl⟩

end GlobalTheory.UnitaryEmbeddingVolume

namespace GlobalTheory.UnitaryEmbeddingVolume

open Topology

theorem vol_pos_lt_top : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)),
    IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ μ : Measure (GfC Y), μ.IsHaarMeasure →
      MeasurableSet {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪} ∧
      0 < μ {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪} ∧
      μ {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪} < ⊤ := by
  intro D Y V d Λ 𝔪 hΛ h𝔪 μ hμ
  obtain ⟨hU, hK⟩ := congLev_open_compact V (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hΛ) h𝔪
  set S := {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪}
  have hc : Continuous fun b : GfC Y => stabilizerEmbedding d (b : GA D Y) :=
    (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding d).comp continuous_subtype_val
  have hS : S = (fun b : GfC Y => stabilizerEmbedding d (b : GA D Y)) ⁻¹'
      (((congLev D.sp.cm V.gram Λ 𝔪).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
  have hopen : IsOpen S := by
    rw [hS]; exact hU.preimage hc
  have h1 : (1 : GfC Y) ∈ S := by
    show Lev.finE V (stabilizerEmbedding d ((1 : GfC Y) : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪
    rw [OneMemClass.coe_one, show stabilizerEmbedding d (1 : GA D Y) = 1 from
      map_one (MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)), map_one]
    exact (congLev D.sp.cm V.gram Λ 𝔪).one_mem
  have hce : IsClosedEmbedding fun b : GfC Y => stabilizerEmbedding d (b : GA D Y) :=
    (isClosedEmbedding_unitaryEmbedding d one_ne_zero).comp (GlobalTheory.Ker.CongTop.isClosed_GfC Y).isClosedEmbedding_subtypeVal
  have hsub : S ⊆ (fun b : GfC Y => stabilizerEmbedding d (b : GA D Y)) ⁻¹'
      ((Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Subgroup (GA D V)) : Set (GA D V)) := by
    intro b hb
    refine ⟨?_, hb⟩
    show stabilizerEmbedding d (b : GA D Y) ∈ GfC V
    rw [GlobalTheory.UnitaryEmbeddingGroup.mem_GfC_iff, ← GlobalTheory.UnitaryEmbeddingGroup.map_eq_one_iff d, ← GlobalTheory.UnitaryEmbeddingGroup.mem_GfC_iff]
    exact b.2
  refine ⟨hopen.measurableSet, hopen.measure_pos μ ⟨1, h1⟩, ?_⟩
  exact (measure_mono hsub).trans_lt (hce.isCompact_preimage hK).measure_lt_top

end GlobalTheory.UnitaryEmbeddingVolume
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitaryEmbeddingOpenLevel

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem col_mem (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (p : Fin c) :
    (fun i => d.a i p) ∈ d.lat Λ (fun _ => 1) := by
  refine ⟨0, Λ.zero_mem, Pi.single p 1, fun q => ?_, ?_⟩
  · by_cases h : q = p
    · subst h; rw [Pi.single_eq_same]; exact FractionalIdeal.one_mem_one _
    · rw [Pi.single_eq_of_ne h]; exact FractionalIdeal.zero_mem _
  · funext i; simp [mulVec_single]

theorem map_mem (d : HermitianOrthogonalExtensionData A B c ε) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {y : Fin A.rank → D.host.E}
    (hy : y ∈ Λ) : frameMat B A d.ι *ᵥ y ∈ d.lat Λ (fun _ => 1) :=
  ⟨y, hy, 0, fun _ => FractionalIdeal.zero_mem _, by simp⟩

theorem lat_eq (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) :
    d.lat Λ (fun _ => 1) = Λ.map ((frameMat B A d.ι).mulVecLin.restrictScalars (𝓞 D.host.E)) ⊔
      Submodule.span (𝓞 D.host.E) (Set.range fun p i => d.a i p) := by
  refine le_antisymm ?_ (sup_le ?_ (Submodule.span_le.2 ?_))
  · rintro _ ⟨y, hy, u, hu, rfl⟩
    refine Submodule.add_mem_sup ⟨y, hy, rfl⟩ ?_
    choose r hr using fun p => (FractionalIdeal.mem_one_iff _).1 (hu p)
    have e : d.a *ᵥ u = ∑ p, r p • fun i => d.a i p := by
      funext i
      simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, ← hr, Algebra.smul_def, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩; exact map_mem d hy
  · rintro _ ⟨p, rfl⟩; exact col_mem d Λ p

theorem isLattice_lat (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) : Submodule.IsFullLattice D.host.E (d.lat Λ (fun _ => 1)) := by
  have hfg : Submodule.IsLattice D.host.E (d.lat Λ (fun _ => 1)) := by
    apply Submodule.IsLattice.of_fg D.host.E
    rw [lat_eq]
    exact (hΛ.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  let S := Submodule.span D.host.E (d.lat Λ (fun _ => 1) : Set (Fin B.rank → D.host.E))
  have hmap : ∀ y : Fin A.rank → D.host.E, frameMat B A d.ι *ᵥ y ∈ S := by
    intro y
    have hy : y ∈ Submodule.span D.host.E (Λ : Set _) := by rw [hΛ.span_eq_top]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (map_mem d hy)
    | zero => simp
    | add x y _ _ hx hy => simpa only [mulVec_add] using S.add_mem hx hy
    | smul a x _ hx => simpa only [mulVec_smul] using S.smul_mem a hx
  have hcols : ∀ u : Fin c → D.host.E, d.a *ᵥ u ∈ S := by
    intro u
    have e : d.a *ᵥ u = ∑ p, u p • fun i => d.a i p := by
      funext i
      simp [mulVec, dotProduct, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun p _ => S.smul_mem _ (Submodule.subset_span (col_mem d Λ p))
  have : Submodule.IsLattice D.host.E (d.lat Λ (fun _ => 1)) := hfg
  refine ⟨?_⟩
  apply Submodule.eq_top_iff'.2
  intro x
  have h := congrArg (fun M => M *ᵥ x) (GlobalTheory.UnitaryEmbeddingGroup.decomp d hε)
  simp only [add_mulVec, ← mulVec_mulVec, one_mulVec] at h
  rw [← h]
  exact S.add_mem (hmap _) (hcols _)

end GlobalTheory.UnitaryEmbeddingOpenLevel


open GlobalTheory.UnitaryEmbeddingOpenLevel in
theorem GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → IsOpen {g : GA D V | Lev.finE V g ∈ congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪} := by
  intro D Y V d Λ 𝔪 hΛ h𝔪
  exact (congLev_open_compact V (isLattice_lat d one_ne_zero
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice Y Λ hΛ)) h𝔪).1

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.NodePar

theorem goodPar_of_sigOK {D : D7} (N : GlobalTheory.Grid.Node D) (h : N.V.SigOK) (τ : D.what₂.Tau) :
    GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) := by
  have hm := GlobalTheory.TowerSplit.hasSignature_of_model N.M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (N.M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (N.M.enum τ)] at hm
  have hs : Formalism.UG.HasSignature (gramAt D N.V τ) (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 := h (tauE D τ)
  obtain ⟨e1, e2⟩ := Formalism.UG.P.signature_unique _ _ _ _ _ _ hm hs
  exact ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ,
    GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ), e1, e2⟩

end GlobalTheory.NodePar
end
end
