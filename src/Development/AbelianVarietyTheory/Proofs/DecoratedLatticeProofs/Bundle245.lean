module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle190
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle106
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle207
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle202
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle209
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OntoDecomp

theorem iSup_jointEigenspace_eq_top {E I : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ip : E → E → ℂ) (hlin : ∀ x y z (c : ℂ), ip x (y + c • z) = ip x y + c * ip x z)
    (hherm : ∀ x y, ip y x = star (ip x y)) (hpos : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (op : I → Module.End ℂ E) (hc : ∀ i j, Commute (op i) (op j))
    (hadj : ∀ i, ∃ i', ∀ x y, ip (op i x) y = ip x (op i' y)) :
    (⨆ x : I → ℂ, ⨅ i, (op i).eigenspace (x i)) = ⊤ := by
  have hzero : ∀ x, ip x 0 = 0 := fun x => by
    have := hlin x 0 0 1
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination (-1 : ℂ) * this
  have hadd : ∀ x y z, ip (x + y) z = ip x z + ip y z := fun x y z => by
    rw [hherm z (x + y), hherm z x, hherm z y]
    have := hlin z x y 1
    simp only [one_smul, one_mul] at this
    rw [this, star_add]
  have hsmul : ∀ x y (r : ℂ), ip (r • x) y = conj r * ip x y := fun x y r => by
    rw [hherm y (r • x), hherm y x]
    have := hlin y 0 x r
    simp only [zero_add, hzero, zero_add] at this
    rw [this, star_mul, mul_comm]
    rfl
  let core : InnerProductSpace.Core ℂ E :=
    { inner := ip
      conj_inner_symm := fun x y => by rw [hherm y x]; rfl
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · subst h
          have := hzero 0
          simp [this]
        · exact (hpos x h).le
      add_left := hadd
      smul_left := hsmul
      definite := fun x hx => by
        by_contra h
        have := hpos x h
        rw [hx] at this
        simp at this }
  letI : NormedAddCommGroup E := InnerProductSpace.Core.toNormedAddCommGroup (cd := core)
  letI : InnerProductSpace ℂ E := InnerProductSpace.ofCore core.toCore
  have hin : ∀ x y : E, inner ℂ x y = ip x y := fun _ _ => rfl
  have h := GlobalTheory.normalFamily_orthogonal_decomposition op (fun i j => hc i j) (fun i => by
    obtain ⟨i', hi'⟩ := hadj i
    refine ⟨i', (LinearMap.eq_adjoint_iff _ _).2 fun x y => ?_⟩
    rw [hin, hin, hherm, ← hi' y x, hherm (op i y)])
  rw [← h.2.1]
  exact iSup_congr fun x => (h.1 x).symm

end GlobalTheory.OntoDecomp

namespace GlobalTheory.OntoDecomp

theorem multT_span_partFull : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → LevFacts D → ForStage D fun c _ s =>
    Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
        partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e} = ⊤ := by
  classical
  intro hP D hfd hlev c hc j hj s hs
  obtain ⟨-, -, hsplit, -, hunif⟩ := GlobalTheory.T.thetaChainStage_level_spherical_off_set D c hc j hj s hs
  have hmul := (hlev c hc j hj s hs).2.2.2.2.1
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S
    hunif hc.inf hmul hsplit
  have hJ : levS s.V s.β s.L = ((Lev.levG s.V s.β s.L : Subgroup (GA D s.V)) : Set (GA D s.V)) := rfl
  rw [← hJ] at hops
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
  have hschur := GlobalTheory.MultFinite.schurMult (θ := c.θ) (M := s.M) (J := levS s.V s.β s.L)
    (χ := Lev.levChi s.V s.β s.L) hP s.ν s.fd
  haveI := hs.haar
  have hright : s.ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds s.V s.ν hs.haar
  obtain ⟨hlin, hpos⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M (levS s.V s.β s.L)
    (Lev.levChi s.V s.β s.L) s.ν s.fd hc.inf hs.haar hs.fund hschur hsm
  obtain ⟨v0, hv0⟩ := GlobalTheory.SchurConst.exists_vec s.M hsm
  have hspec : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
      ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
      IsMultIP s.M s.ν s.fd T T' (ipM s.M s.ν s.fd T T') := fun T hT T' hT' =>
    ipM_spec _ _ _ _ _ (hschur hc.inf hs.haar hs.fund T hT T' hT')
  let φ := Submodule.equivMapOfInjective (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap
    (LinearEquiv.injective _) (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L))
  haveI : FiniteDimensional ℂ ((Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)).map
      (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap) := hfd c hc j hj s hs
  haveI : FiniteDimensional ℂ (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)) :=
    LinearEquiv.finiteDimensional φ.symm
  let I := {t : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D s.V) //
    Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S t.1 t.2.1 t.2.2}
  let op : I → Module.End ℂ (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)) := fun t =>
    (heckeOn s.M t.1.2.2).restrict fun T hT => (hH _ _ _ t.2).1 T hT
  have hcomm : ∀ i j, Commute (op i) (op j) := fun i j => by
    refine LinearMap.ext fun T => Subtype.ext ?_
    exact (hH _ _ _ i.2).2.1 _ _ _ j.2 T T.2
  have hadj : ∀ i, ∃ i', ∀ x y : Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
      ipM s.M s.ν s.fd (op i x : MMap s.M) y = ipM s.M s.ν s.fd x (op i' y : MMap s.M) := fun i => by
    obtain ⟨R', h', hip⟩ := (hH _ _ _ i.2).2.2
    refine ⟨⟨(i.1.1, dualLab i.1.2.1, R'), h'⟩, fun x y => ?_⟩
    have h1 := hspec _ ((hH _ _ _ i.2).1 x x.2) y y.2
    have h2 := (hip s.ν s.fd hs.haar hright hs.fund hschur x x.2 y y.2 _).1 h1
    have h3 := hspec x x.2 _ ((hH _ _ _ h').1 y y.2)
    exact hasPeterssonInner_unique s.M s.ν s.fd _ _ v0 hv0 h2 h3
  have htop := iSup_jointEigenspace_eq_top
    (fun x y : Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) => ipM s.M s.ν s.fd x y)
    (fun x y z a => (hlin x x.2 y y.2 z z.2 a).1) (fun x y => (hlin x x.2 y y.2 y y.2 0).2)
    (fun x hx => hpos x x.2 fun h => hx (Subtype.ext h)) op hcomm hadj
  have hsub : ∀ x : I → ℂ, ∀ T ∈ ⨅ i, (op i).eigenspace (x i), ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      (T : MMap s.M) ∈ partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e := by
    classical
    intro x T hT
    refine ⟨fun P d => if h : ∃ R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R
      then x ⟨(P, d, h.choose), h.choose_spec⟩ else 0, ?_⟩
    rw [mem_partFull]
    refine ⟨T.2, fun P d R hR v => ?_⟩
    have hex : ∃ R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R := ⟨R, hR⟩
    rw [dite_eq_left hex]
    have hlevT := ((GlobalTheory.MultMem.mem_mult_iff ..).1 T.2).lev v
    rw [hLU P d R hex.choose hR hex.choose_spec _ hlevT]
    have h1 := (Submodule.mem_iInf _).1 hT ⟨(P, d, hex.choose), hex.choose_spec⟩
    rw [Module.End.mem_eigenspace_iff] at h1
    exact congrArg (fun U : Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) => (U : MMap s.M) v) h1
  rw [eq_top_iff]
  rintro u -
  obtain ⟨T, rfl⟩ := φ.surjective u
  have hT : T ∈ (⊤ : Submodule ℂ (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L))) := trivial
  rw [← htop] at hT
  refine Submodule.iSup_induction (fun x : I → ℂ => ⨅ i, (op i).eigenspace (x i))
    (motive := fun T => φ T ∈ Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
        partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e}) hT ?_ ?_ ?_
  · intro x T hT
    obtain ⟨e, he⟩ := hsub x T hT
    refine Submodule.subset_span ⟨e, ?_⟩
    have : ((φ T : s.CC c) : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = PiTensorProduct.lift (T : MMap s.M) := rfl
    rw [this, LinearEquiv.symm_apply_apply]
    exact he
  · rw [φ.map_zero]; exact zero_mem _
  · intro a b ha hb; rw [φ.map_add]; exact add_mem ha hb

end GlobalTheory.OntoDecomp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb

variable {D : D7}

theorem heisO_resS_symm_zero {V₀ A L : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec V₀ A L) (S : HSp D)
    (f : WO V₀ S → ℂ) (a u : WO A S) (x : WO L S) :
    heisO ψ V₀ S ((o.resS S).symm (a, 0)) f ((o.resS S).symm (u, x)) =
      ψ (symplOH A S u a) * f ((o.resS S).symm (u + a, x)) := by
  have h1 : (o.resS S).symm (u, x) + (o.resS S).symm (a, 0) = (o.resS S).symm (u + a, x) := by
    rw [← map_add (f := _)]; simp
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]

theorem heisO_resT_symm_zero {T A L : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec T A L) (S : HSp D)
    (f : WO S T → ℂ) (b v : WO S A) (x : WO S L) :
    heisO ψ S T ((o.resT S).symm (b, 0)) f ((o.resT S).symm (v, x)) =
      ψ (symplOH S A v b) * f ((o.resT S).symm (v + b, x)) := by
  have h1 : (o.resT S).symm (v, x) + (o.resT S).symm (b, 0) = (o.resT S).symm (v + b, x) := by
    rw [← map_add (f := _)]; simp
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]

theorem comb_extS {V₀ A L : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec V₀ A L) (S : HSp D)
    (c : WO A S →₀ ℂ) (f : WO V₀ S → ℂ) :
    comb ψ V₀ S (extS o S c) f = ∑ a ∈ c.support, c a • heisO ψ V₀ S ((o.resS S).symm (a, 0)) f := by
  have inj : Function.Injective fun a : WO A S => (o.resS S).symm (a, 0) := fun a b h =>
    (Prod.ext_iff.1 ((o.resS S).symm.injective h)).1
  exact Finsupp.sum_mapDomain_index_inj (h := fun u x => x • heisO ψ V₀ S u f) inj

theorem comb_extT {T A L : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec T A L) (S : HSp D)
    (c : WO S A →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (extT o S c) f = ∑ b ∈ c.support, c b • heisO ψ S T ((o.resT S).symm (b, 0)) f := by
  have inj : Function.Injective fun b : WO S A => (o.resT S).symm (b, 0) := fun a b h =>
    (Prod.ext_iff.1 ((o.resT S).symm.injective h)).1
  exact Finsupp.sum_mapDomain_index_inj (h := fun u x => x • heisO ψ S T u f) inj

theorem contr_comb_ext : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ),
    (∀ (u : WO B.A S) (v : WO S B'.A), IntegrableOn (fun w => f₂ ((B'.o.resT S).symm (v, w)) *
      f₁ ((B.o.resS S).symm (u, l.κ S w))) vL.𝓕 vL.μ) →
    ∀ (c : WO B.A S →₀ ℂ) (c' : WO S B'.A →₀ ℂ),
      contr l S vL (comb ψ B.V₀ S (extS B.o S c) f₁) (comb ψ S B'.V₀ (extT B'.o S c') f₂) =
        biComb ψ B.A S B'.A c c' (contr l S vL f₁ f₂) := by
  intro D ρ σ B B' l S vL ψ f₁ f₂ hint c c'
  funext u v
  rw [comb_extS, comb_extT]
  simp only [contr, biComb, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO_resS_symm_zero,
    heisO_resT_symm_zero]
  simp only [heisO]
  have hI : ∀ a b, Integrable (fun w => f₂ ((B'.o.resT S).symm (v + b, w)) * f₁ ((B.o.resS S).symm (u + a, l.κ S w)))
      (vL.μ.restrict vL.𝓕) := fun a b => hint (u + a) (v + b)
  calc _ = ∫ w in vL.𝓕, ∑ a ∈ c.support, ∑ b ∈ c'.support, (c a * ψ (symplOH B.A S u a) * (c' b * ψ (symplOH S B'.A v b))) *
          (f₂ ((B'.o.resT S).symm (v + b, w)) * f₁ ((B.o.resS S).symm (u + a, l.κ S w))) ∂vL.μ := by
        congr 1
        funext w
        rw [mul_comm, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ a ∈ c.support, ∑ b ∈ c'.support, (c a * ψ (symplOH B.A S u a) * (c' b * ψ (symplOH S B'.A v b))) *
          contr l S vL f₁ f₂ (u + a) (v + b) := by
        rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hI a b).const_mul _]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finsetSum _ fun b _ => (hI a b).const_mul _]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [integral_const_mul]
        rfl
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

end GlobalTheory.ContrComb
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastSeeSaw

variable {D : D7}

theorem isThetaFunO_const_mul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (fun w => c * f w) := {
  quasi γ w := by
    show c * f (ratW T S γ + w) = _ * (c * f w)
    rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (hk u hu h0) w
    simp only [heisO] at e ⊢
    rw [← e]; ring
  cont := continuous_const.mul hf.cont
  smooth n L hL h0 w := contDiff_const.mul (hf.smooth n L hL h0 w) }

theorem isThetaFunO_kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ}
    {f : WO L S → ℂ} (hf : IsThetaFunO ψ L S f) : IsThetaFunO ψ S L'' (fun w => f (kap τ S w)) := by
  obtain ⟨hadd, hcont, hrat, -, hsym, hpart⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1) (by simpa using hτ)
    (kap τ S) (fun _ => rfl)
  have hsH : ∀ x y, symplOH L S (kap τ S x) (kap τ S y) = symplOH S L'' x y := fun x y => by
    simp only [symplOH, hsym]; push_cast; ring
  let K : WO S L'' →+ WO L S := AddMonoidHom.mk' (kap τ S) hadd
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp hcont, fun n M hM h0 w => ?_⟩
  · obtain ⟨γ', hγ'⟩ := hrat (ratW L'' S γ) (by rw [ratW_eq]; exact rat_mem _)
    show f (kap τ S (ratW L'' S γ + w)) = _
    have e : ratW S L γ' = kap τ S (ratW L'' S γ) := hγ'
    rw [hadd, ← e, hf.quasi, e, hsH]
  · obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U.comap K, hU.preimage hcont, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (hk (kap τ S u) hu ((hpart u).1 h0)) (kap τ S w)
    simp only [heisO] at e ⊢
    rw [hadd, ← hsH]
    exact e
  · have := hf.smooth n (K.comp M) (hcont.comp hM) (fun t => (hpart (M t)).2 (h0 t)) (kap τ S w)
    simp only [hadd]
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, K] using this

end GlobalTheory.LastSeeSaw
end

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LastSeeSaw

end GlobalTheory.LastSeeSaw
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.RepsAtTwist

theorem exists_rep_flat_ne : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (b : L.β (j + 1)) (g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k), IsGL ι (L.h (j + 1) b P) g' → ∃ (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g ∧ flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0 := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hc hA L G hL hP j c h b g' hg'
  have hm := hL.hm
  have hs := hA.steps
  obtain ⟨al, A₀, B₀, hne⟩ := hL.nonvan j (by omega) b P
  obtain ⟨g, hg, -⟩ := GlobalTheory.TwBridge.Model.isGL_existsUnique (k := k) ι j (c + 1 + 1) (by unfold cOf; omega) (L.h j al P)
  have hSum := GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA
  obtain ⟨A₁, B₁, hAB⟩ := hSum j c h (L.h j al P) (L.h (j + 1) b P) g g' hg hg'
    (hL.boundQ j al P hA.nmem) (hL.boundQ (j + 1) b P hA.nmem) (hL.depthQ' P hA.nmem)
  obtain ⟨e', he'⟩ : ∃ e : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e :=
    GlobalTheory.AtTypeExists.exists_ord.1 R.k R.t j
  obtain ⟨e, he⟩ : ∃ e : XIx (Fin R.k) (Fin R.t) (j + 1) ≃ Fin (R.N (j + 1)), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e :=
    GlobalTheory.AtTypeExists.exists_ord.1 R.k R.t (j + 1)
  obtain ⟨x, hx⟩ := Function.ne_iff.1 (hne (max A₀ A₁) (max B₀ B₁) (le_max_left _ _) (le_max_left _ _))
  have hF := hAB (max A₀ A₁) (max B₀ B₁) (le_max_right _ _) (le_max_right _ _) e' e he' he x
  have hsg : W.sg ≠ 0 := by
    intro h0
    have h2 := GlobalTheory.TwBridge.Model.sg_sq (h := hA) (hok := hc)
    rw [h0] at h2
    norm_num at h2
  refine ⟨al, g, hg, fun h0 => ?_⟩
  have h1 := congrFun h0 (GlobalTheory.SymBridge.toLoc ι e e' x)
  rw [hF, Pi.zero_apply] at h1
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ((map_ne_zero σ₀).2 hx) h1
  · unfold sgn; exact zpow_ne_zero _ hsg
  · unfold sgn; exact zpow_ne_zero _ hsg

end GlobalTheory.RepsAtTwist
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.EntryAtTwist

theorem bas_eq_one {R : Ranks} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (W : TwData k) (j c : ℕ) (h : j + c = s + 1) : (W.T s R).bas j c h = 1 := by
  first | rfl | (simp [TwData.T, twistChain, Chain.ofTwist])

theorem entryAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → EntryAgree Ch sel mu cst σ₀ P ι s W ν L := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hcst hAt L G hL
  have hSum := GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hcst hAt
  have hVol := GlobalTheory.T.local_volume_agrees_row_subgroup_unitary X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hcst hAt
  intro j c h al be g g' hg hg' e' e he' he x
  have hnm := hAt.nmem
  obtain ⟨A₀, B₀, hAB⟩ := hSum j c h (L.h j al P) (L.h (j + 1) be P) g g' hg hg'
    (hL.boundQ j al P hnm) (hL.boundQ (j + 1) be P hnm) (hL.depthQ' P hnm)
  have hF := hAB (max A₀ cst.A) (max B₀ cst.B) (le_max_left _ _) (le_max_left _ _) e' e he' he x
  rw [hL.deep _ _ (le_max_right _ _) (le_max_right _ _) j (by omega) al be P] at hF
  have hV := (hVol (j + 1) c (by omega) (L.h (j + 1) be P) g' hg').1
  simp only [Chain.entry, xi, bas_eq_one]
  rw [hF, Complex.ofReal_inv, hV]
  simp only [XiAt, map_mul, map_inv₀]
  ring

end GlobalTheory.EntryAtTwist
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

namespace GlobalTheory.Core.Rk.IP

theorem isKFinVec_of_isFockVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ K : Subgroup (GA D S), IsCompact (K : Set (GA D S)) → (∀ k ∈ K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ f, IsFockVec ψ θ S T sS sT f → IsKFinVec om K f := by
  intro D ψ θ S T χS χT om sS sT hW hθ hS hT K hK hc f hf
  obtain ⟨hth, N, hN⟩ := hf
  obtain ⟨U, hU, hUK⟩ := GlobalTheory.T.exists_common_level_compact_translates_thetaFunction D ψ S T χS χT om hW (K : Set (GA D S)) hK f hth
  have hfd := GlobalTheory.T.finiteDimensional_thetaFunctions_level_fockDegree D ψ θ S T sS sT hW.std hθ hS hT U hU N
  refine @Submodule.finiteDimensional_of_le _ _ _ _ _ _ _ hfd (Submodule.span_mono ?_)
  rintro g ⟨k, hk, rfl⟩
  exact ⟨hW.om_pres _ f hth, hUK k hk,
    GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ θ S T χS χT om sS sT hW hθ k (hc k hk) N f hth hN⟩

end GlobalTheory.Core.Rk.IP
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level : ∀ D : D7, FlatLe D := by
  first | exact @GlobalTheory.FlatLevel.flatLe | exact GlobalTheory.FlatLevel.flatLe | (intros; apply GlobalTheory.FlatLevel.flatLe <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.hecke_char_quotient_unramified_at_twist_place : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ PP ∈ w.Q, ∀ i j : ℕ, 1 ≤ i → i ≤ D.R.m → 1 ≤ j → j ≤ D.R.m → GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
  first | exact @GlobalTheory.ChainTw.quot_unrAt_twist | exact GlobalTheory.ChainTw.quot_unrAt_twist | (intros; apply GlobalTheory.ChainTw.quot_unrAt_twist <;> assumption)
end
