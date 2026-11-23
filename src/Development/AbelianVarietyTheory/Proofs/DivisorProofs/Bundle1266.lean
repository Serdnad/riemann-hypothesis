module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.Divisibility.Bundle003
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.PsiInfLinear

theorem continuous_ringEquiv_mixedSpace_symm (E : Type) [Field E] [NumberField E] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem psiInf_eq_exp_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∃ Λ : mixedEmbedding.mixedSpace D.host.F →L[ℝ] ℂ, ∀ x : InfiniteAdeleRing D.host.F,
      psiInf D.host.F ψ x = Complex.exp (Λ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x)) := by
  intro D ψ h
  obtain ⟨-, ⟨θ, hθ⟩, hall⟩ := h
  have hform := hall θ hθ
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
  let c : ℂ := 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ)
  let g : mixedEmbedding.mixedSpace D.host.F →+ ℂ :=
    { toFun := fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[D.host.F] (1 : D.host.E))
      map_zero' := by simp
      map_add' := by
        intro a b
        simp [TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  have hg : Continuous g := by
    show Continuous fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[D.host.F] (1 : D.host.E))
    refine continuous_const.mul (continuous_finsetSum _ fun ρ _ => ?_)
    exact (hθ ρ).2.comp (continuous_ringEquiv_mixedSpace_symm D.host.F)
  refine ⟨AddMonoidHom.toRealLinearMap g hg, fun x => ?_⟩
  rw [hform x]
  congr 1
  show _ = c * ∑ ρ, θ ρ (e.symm (e x) ⊗ₜ[D.host.F] (1 : D.host.E))
  rw [e.symm_apply_apply]

end GlobalTheory.PsiInfLinear
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdCharLin

theorem continuous_ofMixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem stdChar_mixed_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsStdChar D ψ (-1) → IsInfFam θ →
    ∃ β : mixedEmbedding.mixedSpace D.host.F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a, 0) : AdeleRing (𝓞 D.host.F) D.host.F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧
      ∀ a, β a = -(∑ ρ, θ ρ (((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a) ⊗ₜ[D.host.F]
        (1 : D.host.E))).re := by
  intro D ψ θ hψ hθ
  obtain ⟨hc, hall⟩ := hψ
  have key := hall.2 θ hθ
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F with he
  let z : Ainf D.host.F → ℂ := fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))
  have hkey : ∀ x, ψ ((x, 0) : AdeleRing (𝓞 D.host.F) D.host.F) =
      Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * z x) := fun x => key x
  have him : ∀ x, (z x).im = 0 := by
    intro x
    have h1 := hc.2.1 ((x, 0) : AdeleRing (𝓞 D.host.F) D.host.F)
    rw [hkey x, Complex.norm_exp] at h1
    have hre : (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * z x).re = 2 * Real.pi * (z x).im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_eq_one_iff] at h1
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    rcases mul_eq_zero.1 h1 with h | h
    · linarith
    · exact h
  have hzadd : ∀ x y, z (x + y) = z x + z y := by
    intro x y
    simp only [z, TensorProduct.add_tmul, map_add (f := _), Finset.sum_add_distrib]
  let g : mixedEmbedding.mixedSpace D.host.F →+ ℝ :=
    { toFun := fun a => -(z (e.symm a)).re
      map_zero' := by simp [z]
      map_add' := by intro a b; simp only [map_add (f := _), hzadd, Complex.add_re, neg_add] }
  have hg : Continuous g := by
    have : Continuous fun x : Ainf D.host.F => z x :=
      continuous_finsetSum _ fun ρ _ => (hθ ρ).2
    exact (Complex.continuous_re.comp (this.comp (continuous_ofMixed D.host.F))).neg
  refine ⟨(g.toRealLinearMap hg : mixedEmbedding.mixedSpace D.host.F →ₗ[ℝ] ℝ), ?_, fun a => rfl⟩
  intro a
  have hz : z (e.symm a) = ((z (e.symm a)).re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hkey (e.symm a)]
  congr 1
  change _ = 2 * Real.pi * Complex.I * ((-(z (e.symm a)).re : ℝ) : ℂ)
  rw [hz]
  push_cast
  simp only [Complex.ofReal_re]
  ring

end GlobalTheory.StdCharLin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfTraceNondeg

variable {K : Type} [Field K] [NumberField K]

theorem norm_algebraMap_apply (x : K) (v : InfinitePlace K) :
    ‖(algebraMap K (InfiniteAdeleRing K) x) v‖ = v x := by
  simp [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.norm_coe, InfinitePlace.coe_apply]

theorem norm_eq_of_cont (χ : InfiniteAdeleRing K →+* ℂ) (hχ : Continuous χ) (φ : K →+* ℂ)
    (h : ∀ x, χ (algebraMap K _ x) = φ x) (a : InfiniteAdeleRing K) :
    ‖χ a‖ = ‖a (InfinitePlace.mk φ)‖ := by
  have hc1 : Continuous fun a => ‖χ a‖ := hχ.norm
  have hc2 : Continuous fun a : InfiniteAdeleRing K => ‖a (InfinitePlace.mk φ)‖ :=
    (continuous_apply (InfinitePlace.mk φ)).norm
  refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap K).equalizer hc1 hc2 (funext fun x => ?_)) a
  simp only [Function.comp, h, norm_algebraMap_apply, InfinitePlace.apply]

end GlobalTheory.InfTraceNondeg

namespace GlobalTheory.InfTraceNondeg



theorem realTrace_nondeg : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → ∀ a : Ainf D.host.F, a ≠ 0 →
      ∃ b : Ainf D.host.F, (∑ ρ, θ ρ ((a * b) ⊗ₜ[D.host.F] (1 : D.host.E))).re ≠ 0 := by
  intro D θ hθ a ha
  obtain ⟨v, hv⟩ : ∃ v, a v ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := D.host.F) (K := D.host.E) v
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 w
  let χ : D.what₂.Tau → (Ainf D.host.F →+* ℂ) := fun σ =>
    (θ σ).comp Algebra.TensorProduct.includeLeftRingHom
  have hχapp : ∀ σ c, χ σ c = θ σ (c ⊗ₜ[D.host.F] (1 : D.host.E)) := fun _ _ => rfl
  have hχalg : ∀ σ (x : D.host.F), χ σ (algebraMap D.host.F (Ainf D.host.F) x) =
      ((tauE D σ).comp (algebraMap D.host.F D.host.E)) x := by
    intro σ x
    rw [hχapp, ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply', (hθ σ).1]
    rfl
  have hnorm : ∀ σ c, ‖χ σ c‖ = ‖c (InfinitePlace.mk ((tauE D σ).comp (algebraMap D.host.F D.host.E)))‖ :=
    fun σ c => norm_eq_of_cont (χ σ) (hθ σ).2 _ (hχalg σ) c
  have hmul : ∀ x y : Ainf D.host.F, ∀ u, (x * y) u = x u * y u := fun _ _ _ => rfl
  set e : Ainf D.host.F := Pi.single v 1 with he
  set b : Ainf D.host.F := Pi.single v (a v)⁻¹ with hb
  have hab : a * b = e := by
    funext u
    rw [hmul]
    by_cases hu : u = v
    · subst hu
      simp [he, hb, hv]
    · simp [he, hb, Pi.single_apply, hu]
  have hee : e * e = e := by
    funext u
    rw [hmul]
    by_cases hu : u = v
    · subst hu; simp [he]
    · simp [he, Pi.single_apply, hu]
  have hidem : ∀ σ, χ σ e = 0 ∨ χ σ e = 1 := by
    intro σ
    have h1 : χ σ e * χ σ e = χ σ e := by rw [← map_mul, hee]
    have h2 : χ σ e * (χ σ e - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hplace : InfinitePlace.mk ((tauE D ρ).comp (algebraMap D.host.F D.host.E)) = v := by
    rw [← InfinitePlace.comap_mk]
    change (InfinitePlace.mk (Formalism.MainNotions.StandardLattice.embOf D ρ)).comap _ = v
    have hρ' : InfinitePlace.mk (Formalism.MainNotions.StandardLattice.embOf D ρ) = w := hρ
    have hw' : w.comap (algebraMap D.host.F D.host.E) = v := hw
    rw [hρ', hw']
  have hρ1 : χ ρ e = 1 := by
    rcases hidem ρ with h | h
    · exfalso
      have := hnorm ρ e
      rw [h, hplace, he, Pi.single_eq_same, norm_zero, norm_one] at this
      exact zero_ne_one this
    · exact h
  refine ⟨b, ?_⟩
  rw [hab, Complex.re_sum]
  have hterm : ∀ σ, 0 ≤ (θ σ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re := by
    intro σ
    rw [← hχapp]
    rcases hidem σ with h | h <;> simp [h]
  have hge : (θ ρ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re ≤ ∑ σ, (θ σ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re :=
    Finset.single_le_sum (fun σ _ => hterm σ) (Finset.mem_univ ρ)
  rw [← hχapp, hρ1, Complex.one_re] at hge
  linarith

end GlobalTheory.InfTraceNondeg
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

theorem exists_ix_of_mem_eigAt : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m s : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m), A3.fam3.Ok3 s → ∀ (x : (A3.rowI A3.A.μ0).OpIx → K) (f : (A3.A.fam.R A3.A.μ0).S.Forms), f ≠ 0 → f ∈ (A3.A.fam.R A3.A.μ0).ZHg A3.A.X → f ∈ Formalism.L2.Col.eigAt (A3.rowI A3.A.μ0).opAll x → ∃ p : A3.fam3.base3.Ix, (A3.rowI A3.A.μ0).HasRes3 p.1 x := by
  classical
  intro K _ _ _ G _ _ Pl0 I0 Ty T m s A3 h x f hf0 hfZ hfx
  have hB : (A3.A.fam.R A3.A.μ0).Ok s := h.ok2.what₂ A3.A.μ0
  have hD : (A3.rowI A3.A.μ0).Ok3 := h.what₂ A3.A.μ0
  have hs := (A3.rowI A3.A.μ0).splitOver_opAll hB hD

  have hfZH : f ∈ Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll fun y => Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i)) :=
    le_eigSum_elim (A3.A.fam.R A3.A.μ0).op (A3.rowI A3.A.μ0).opI hD.comm hs _ (by exact hfZ.1)
  have hHB : Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => x (Sum.inl i)) := by
    by_contra hn
    have hf2 : f ∈ Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll fun y => ¬ Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i)) :=
      Formalism.L2.Col.eigAt_le_eigSum (C := fun y => ¬ Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i))) hn hfx
    exact hf0 (Submodule.disjoint_def.1 (Formalism.L2.Col.disjoint_eigSum hD.comm fun y h1 h2 => h2 h1) f hfZH hf2)
  choose c hc using hHB
  let Sg : Pl0 → K[X] := fun P0 => if hP : ∃ P, (A3.A.fam.R A3.A.μ0).pl P = P0 then c hP.choose else 1
  have hSg : ∀ P, Sg ((A3.A.fam.R A3.A.μ0).pl P) = c P := by
    intro P
    have hP : ∃ P', (A3.A.fam.R A3.A.μ0).pl P' = (A3.A.fam.R A3.A.μ0).pl P := ⟨P, rfl⟩
    simp only [Sg, dif_pos hP]
    rw [hB.pl_inj hP.choose_spec]
  let e : I0 × Ty → K := fun k0 => if hP : ∃ P, (A3.rowI A3.A.μ0).plI P = k0.1 then x (Sum.inr (hP.choose, k0.2)) else 0
  have he : ∀ (P : (A3.rowI A3.A.μ0).PlI) (y : Ty), e ((A3.rowI A3.A.μ0).plI P, y) = x (Sum.inr (P, y)) := by
    intro P y
    have hP : ∃ P', (A3.rowI A3.A.μ0).plI P' = (A3.rowI A3.A.μ0).plI P := ⟨P, rfl⟩
    simp only [e, dif_pos hP]
    rw [hD.plI_inj hP.choose_spec]
  have hres : (A3.rowI A3.A.μ0).HasRes3 (Sg, e) x := by
    refine ⟨fun P => ?_, fun k => (he k.1 k.2).symm⟩
    show _ = Sg ((A3.A.fam.R A3.A.μ0).pl P) * (A3.A.fam.R A3.A.μ0).blockProd P
    rw [hSg P, mul_comm]
    exact hc P

  set a0 := goodAt A3.A.fam.X (⊥ : Subgroup G) 1 with ha0
  have hidem : a0 * a0 = a0 :=
    (good_at_spec K A3.A.fam.v0 h.ok2.conj G A3.A.fam.X h.ok2.irr (⊥ : Subgroup G) 1).idem
  have hfix : (A3.A.fam.R A3.A.μ0).S.gaOp (A3.A.fam.R A3.A.μ0).r a0 f = f := by
    obtain ⟨g, hg⟩ := LinearMap.mem_range.1 hfZ.2
    have hid' : a0 * goodAt A3.A.X (⊥ : Subgroup G) 1 = goodAt A3.A.X (⊥ : Subgroup G) 1 := hidem
    rw [← hg, ← BlockDat.gaOp_mul, hid']
  obtain ⟨u0, hu0⟩ := (A3.A.fam.R A3.A.μ0).exists_vE_of_fix (Lvl.full A3.A.fam.X) hfix
  have hmem : (Sg, e) ∈ (A3.rowI A3.A.μ0).ixFin3 A3.A.fam.X := by
    rw [(A3.rowI A3.A.μ0).mem_ixFin3 hD.comm]
    refine ⟨fun P0 hP0 => ?_, fun P0 hP0 y => ?_, ?_⟩
    · have hP : ¬ ∃ P, (A3.A.fam.R A3.A.μ0).pl P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
      show Sg P0 = 1
      simp only [Sg, dif_neg hP]
    · have hP : ¬ ∃ P, (A3.rowI A3.A.μ0).plI P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
      show e (P0, y) = 0
      simp only [e, dif_neg hP]
    · intro hbot
      have hu0mem : u0 ∈ (A3.A.fam.R A3.A.μ0).inV0 (Lvl.full A3.A.fam.X) ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum (Sg, e)) := by
        rw [BlockDat.mem_goodPart_iff, hu0]
        exact Formalism.L2.Col.eigAt_le_eigSum (C := (A3.rowI A3.A.μ0).HasRes3 (Sg, e)) hres hfx
      rw [hbot, Submodule.mem_bot] at hu0mem
      apply hf0
      rw [← hu0, hu0mem, Matrix.mulVec_zero, map_zero]
  exact ⟨⟨(Sg, e), hmem⟩, hres⟩

end GlobalTheory.Div
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

theorem nonempty_ix_of_pos : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m s : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A3.fam3.amb3), A3.fam3.Ok3 s → Zs.InBlock → (A3.side3 P ψ Zs).Pos → Nonempty A3.fam3.base3.Ix := by
  intro K _ _ _ G _ _ Pl0 I0 Ty T m s A3 P ψ Zs hOk hin hpos
  by_contra hne
  have hfalse : ∀ x, ¬ A3.fam3.IsType3 (A3.fam3.RI A3.fam3.F.μ0) id x := by
    rintro x ⟨p, hp, -⟩
    exact hne ⟨⟨p, hp⟩⟩
  have hsame := A3.fam3.sameTypes_base3 hOk P ψ hin
  have hbot : Formalism.L2.Col.eigSum (A3.fam3.RI A3.fam3.F.μ0).opAll
      (A3.fam3.IsType3 (A3.fam3.RI A3.fam3.F.μ0) id) = ⊥ := by
    unfold Formalism.L2.Col.eigSum
    simp [hfalse]
  rw [hbot, BlockDat.good_part_coordinates_bot, le_bot_iff] at hsame
  unfold FamIn3.side3 DefFam3.side3 DefSide.Pos at hpos
  simp only [BlockDat.dZ, subDim] at hpos
  rw [hsame] at hpos
  simp at hpos

end GlobalTheory.Div
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.LevelRange

theorem range_w0C_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.LUnif → ∀ b i, LinearMap.range ((R.toCx3 F).w0C b i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) ((R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 b (sg0 D A3.A))).comap (R.HW i (sg0 D A3.A)).e) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hU b i
  have hL := GlobalTheory.LevelForms.levelW_of_irr R.toRealDat F.lv2 hOk.ok2.irr hU hC.base.models.HW
  rw [← hL b i (sg0 D A3.A)]
  have h3 : Submodule.span ℂ (Set.range fun k => (⟨R.toRealDat.bC F.lv2 b i (sg0 D A3.A) k, Submodule.subset_span ⟨k, rfl⟩⟩ :
      R.toRealDat.WS F.lv2 b i (sg0 D A3.A))) = ⊤ := Submodule.span_range_subtype_eq_top_iff _ _ |>.2 rfl
  have h4 : LinearMap.range ((R.toCx3 F).wC b i A3.A.v0) = ⊤ :=
    (Fintype.range_linearCombination _ _).trans (Tw.span_top (E := R.toRealDat.WS F.lv2 b i (sg0 D A3.A)) _ h3)
  have hc : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) b)).ne'
  refine (LinearMap.range_comp_of_range_eq_top _ h4).trans (le_antisymm ?_ fun x hx => ?_)
  · rintro _ ⟨y, rfl⟩
    exact (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).smul_mem _ (Tw.out y : R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).2
  · let y : (R.HW i (sg0 D A3.A)).H := x
    exact ⟨(⟨((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ)⁻¹ • y, (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).smul_mem _ hx⟩ :
      R.toRealDat.WS F.lv2 b i (sg0 D A3.A)), smul_inv_smul₀ hc y⟩

end GlobalTheory.LevelRange
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicSide

theorem adForms_eq_of_reps {Gr Γ : Type} [Group Gr] [Group Γ] (ι : Γ →* Gr) {Wc : Type} [NormedAddCommGroup Wc]
    [InnerProductSpace ℂ Wc] (ρ : Γ →* Module.End ℂ Wc) {J J' : Subgroup Gr} (χ : J →* ℂˣ) (hle : J' ≤ J) {I : Type}
    {y : I → Gr} (hy : Bridge.IsReps ι J' y) {f f' : Gr → Wc} (h1 : f ∈ Bridge.AdForms ι ρ J χ)
    (h2 : f' ∈ Bridge.AdForms ι ρ J χ) (h : ∀ k, f (y k) = f' (y k)) : f = f' := by
  funext g
  obtain ⟨k, ⟨γ, u, rfl⟩, -⟩ := hy g
  have m1 := h1 γ (y k) ⟨u, hle u.2⟩
  have m2 := h2 γ (y k) ⟨u, hle u.2⟩
  rw [h k] at m1
  exact m1.trans m2.symm



theorem exists_thAd_of_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (i : Fin D.R.m) (t : T0) (K' : Type) [Field K'] (σ' : K' →+* ℂ) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) (Cl : Type) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), J' ≤ levJ R i t → Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => FWT.fin _ (h k)) → ∀ v₀ : (R.MW i (sg0 D A)).Vec, ∃ thAd, ThAdIs R i t h c0' v₀ thAd := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hR i t K' _ σ' c0' Cl h J' hle hr v₀
  classical
  obtain ⟨hinj, hrange, -⟩ := hR.HV i t
  have huniq : ∀ y y' x, Place R i t h c0' y x → Place R i t h c0' y' x → y = y' := fun y y' x h1 h2 =>
    hinj (adForms_eq_of_reps _ _ _ hle hr (hrange.le (LinearMap.mem_range_self _ y))
      (hrange.le (LinearMap.mem_range_self _ y')) fun k => (h1 k).trans (h2 k).symm)
  refine ⟨fun x => if hx : ∃ y, Place R i t h c0' y x then onQ (Wc D i) (R.thF i t hx.choose v₀) else 0, fun y x hy => ?_⟩
  have hx : ∃ y, Place R i t h c0' y x := ⟨y, hy⟩
  simp only [dif_pos hx]
  rw [huniq _ _ _ hx.choose_spec hy]

end GlobalTheory.AdelicSide
end
