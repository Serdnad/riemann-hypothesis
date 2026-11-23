module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.Columns.MtAdWt
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle253
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle014
public import Formalism.LocalToGlobal.Columns.MtAdWtIrr
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle021
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle222
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle267
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtInRat

variable {D : D7}

theorem toGf_injective {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) : Function.Injective (toGf P) := by
  intro a b h
  have h1 : finHom V (P.ψ a) = finHom V (P.ψ b) := congrArg Subtype.val h
  have h2 : Formalism.IndefR.Lev.finE V (P.ψ a) = Formalism.IndefR.Lev.finE V (P.ψ b) := by
    simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, h1]
  rw [hU, hU] at h2
  exact Subtype.ext h2

theorem toGf_surjective {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) : Function.Surjective (toGf P) := by
  rintro ⟨_, x, rfl⟩
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V x)
  obtain ⟨h, hh⟩ := P.onto k k1
  refine ⟨h, Subtype.ext ?_⟩
  show finHom V (P.ψ h) = finHom V x
  rw [hh, k2]

theorem af_nontrivial : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := by
  obtain ⟨I, hbot, htop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp
    (NumberField.RingOfIntegers.not_isField (maximalRealSubfield D.host.E))
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop.ne
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := ⟨M, hM.isPrime, fun h => by
    rw [h] at hIM
    exact hbot.ne' (le_bot_iff.mp hIM)⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (ReciprocityTheory.Aut.evalAt D.host.E v) h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

theorem inclL_injective :
    Function.Injective (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) := by
  haveI := af_nontrivial (D := D)
  haveI : Nontrivial (ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _
      (algebraMap (maximalRealSubfield D.host.E) (ReciprocityTheory.Aut.AFplus D.host.E)).injective
  exact (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E).injective

theorem inclA_injective : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

def glL (n : ℕ) : GL (Fin n) D.host.E →* GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E) :=
  Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom

theorem glL_injective (n : ℕ) : Function.Injective (glL (D := D) n) := fun a b h =>
  Units.ext (Matrix.map_injective inclL_injective (congrArg Units.val h))

theorem glL_mem (n : ℕ) (x : GL (Fin n) D.host.E) (hx : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E n) :
    glL (D := D) n x ∈ ReciprocityTheory.Aut.GA D.host.E n := by
  have h : (x : Matrix (Fin n) (Fin n) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x = 1 := hx
  have h2 := congrArg (fun M => Matrix.map M
    (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  show (x : Matrix (Fin n) (Fin n) D.host.E).map _ * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E)
    ((x : Matrix (Fin n) (Fin n) D.host.E).map _) = 1
  rw [← h2]
  congr 1

def toStd (n : ℕ) : ReciprocityTheory.Aut.GQ0 D.host.E n →* ReciprocityTheory.Aut.GQ D.host.E n where
  toFun x := ⟨⟨glL (D := D) n x.1, glL_mem n x.1 x.2⟩, Subgroup.mem_subgroupOf.2 ⟨x.1, x.2, rfl⟩⟩
  map_one' := by ext1; ext1; exact map_one _
  map_mul' a b := by ext1; ext1; exact map_mul _ _ _

theorem toStd_bij (n : ℕ) : Function.Bijective (toStd (D := D) n) := by
  refine ⟨fun a b h => Subtype.ext (glL_injective n (congrArg (fun y => y.1.1) h)), fun γ => ?_⟩
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext he)⟩

section V

variable {V : HSp D}

theorem cT_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M =
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) M := rfl

theorem mem_UJ (hV : V.gram = 1) (x : GL (Fin V.rank) D.host.E) (hx : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
  have h : (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x = 1 := hx
  show Formalism.UG.cT _ (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x = V.gram
  rw [hV, Matrix.mul_one, cT_eq]
  exact mul_eq_one_comm.1 h

theorem mem_rationalGL_of_unitaryGroupGram_unitGram (hV : V.gram = 1) (x : GL (Fin V.rank) D.host.E)
    (hx : x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x =
    V.gram := hx
  rw [hV, Matrix.mul_one, cT_eq] at h
  exact mul_eq_one_comm.1 h

theorem mem_HR (x : GL (Fin V.rank) D.host.E) (hx : x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) :
    Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x =
    V.gram := hx
  have h2 := GlobalTheory.UnitarySplit.map_cond (inclR (F := D.host.F) (AF D.host.F)) (D.sp.cm.sig : D.host.E →+* D.host.E)
    (sigR (AF D.host.F) D.sp.cm.sig) (fun y => rfl) V.gram x.1
  rw [h] at h2
  exact h2.symm

def toV (hV : V.gram = 1) : ReciprocityTheory.Aut.GQ0 D.host.E V.rank →* Formalism.L2.Theta.GQ V where
  toFun x := ⟨⟨Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) x.1, mem_HR x.1 (mem_UJ hV x.1 x.2)⟩,
    Subgroup.mem_subgroupOf.2 ⟨x.1, mem_UJ hV x.1 x.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)
    exact map_mul _ _ _

theorem toV_bij (hV : V.gram = 1) : Function.Bijective (toV hV) := by
  refine ⟨fun a b h => Subtype.ext (Units.ext (Matrix.map_injective inclA_injective
    (congrArg (fun y : Formalism.L2.Theta.GQ V => Units.val (y.1 : HR (AF D.host.F) D.sp.cm.sig V.gram).1) h))), fun δ => ?_⟩
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 δ.2)
  exact ⟨⟨x, mem_rationalGL_of_unitaryGroupGram_unitGram hV x hx⟩, Subtype.ext (Subtype.ext he)⟩

def ratE (hV : V.gram = 1) : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V :=
  (MulEquiv.ofBijective (toStd (D := D) V.rank) (toStd_bij V.rank)).symm.trans (MulEquiv.ofBijective (toV hV) (toV_bij hV))

theorem ratE_toStd (hV : V.gram = 1) (x : ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    ratE hV (toStd (D := D) V.rank x) = toV hV x :=
  congrArg (toV hV) ((MulEquiv.ofBijective (toStd (D := D) V.rank) (toStd_bij V.rank)).symm_apply_apply x)

theorem swapAE_injective : Function.Injective (swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective

theorem finHom_eq_of_finE {g h : GA D V} (e : Formalism.IndefR.Lev.finE V g = Formalism.IndefR.Lev.finE V h) :
    finHom V g = finHom V h :=
  Units.ext (Matrix.map_injective swapAE_injective (congrArg Units.val e))

theorem finE_toV (hV : V.gram = 1) (x : ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    Formalism.IndefR.Lev.finE V ((toV hV x : Formalism.L2.Theta.GQ V) : GA D V) =
      km D V.rank (toStd (D := D) V.rank x).1 := by
  apply Units.ext
  ext i j
  show swapAE D ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] (x.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j)) = _
  simp [Algebra.TensorProduct.map_tmul, swapAE, glL]
  rfl

theorem ratIso_ratE (hV : V.gram = 1) (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) : RatIso P (ratE hV) := by
  intro γ
  obtain ⟨x, rfl⟩ := (toStd_bij (D := D) V.rank).2 γ
  have hr := ratE_toStd hV x
  refine ⟨(congrArg (Bridge.ratF V) hr).trans (Subtype.ext ?_), fun γ₀ h => ?_⟩
  · exact finHom_eq_of_finE ((finE_toV hV x).trans (hU (toStd (D := D) V.rank x).1).symm)
  · have hx : x.1 = γ₀ := glL_injective V.rank (Units.ext h)
    have key : Bridge.IsRatMat V (toV hV x) γ₀ := by
      show Formalism.L2.Theta.matHom V ((toV hV x : Formalism.L2.Theta.GQ V) : GA D V) = Formalism.UG.bc (incA D) γ₀
      rw [← hx]
      rfl
    exact hr ▸ key

end V

theorem toGf_bij_ratIso : ∀ (D : D7) (V : HSp D) (P : principalLevelFrame.RowPsi V V.rank), V.gram = 1 → UnitFr P →
    Function.Bijective (toGf P) ∧ ∃ e, RatIso P e := by
  intro D V P hV hU
  exact ⟨⟨toGf_injective P hU, toGf_surjective P⟩, ratE hV, ratIso_ratE hV P hU⟩

end GlobalTheory.MtInRat
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn

open _root_.Formalism.L2.Col

theorem map_inv_mat {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ} (γE : GL (Fin n) E) :
    ((γE : Matrix (Fin n) (Fin n) E).map f)⁻¹ = ((γE : Matrix (Fin n) (Fin n) E)⁻¹).map f := by
  have h := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) (map_inv (Matrix.GeneralLinearGroup.map f) γE)
  have h1 : ((Matrix.GeneralLinearGroup.map f γE : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (γE : Matrix (Fin n) (Fin n) E).map f := rfl
  have h2 : ((Matrix.GeneralLinearGroup.map f γE⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((γE⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map f := rfl
  simp only [Matrix.coe_units_inv] at h h2
  rw [h1] at h
  rw [h2] at h
  exact h.symm

theorem isAlgWeight_of_equiv {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W W' : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W) (ρ' : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W')
    (T : W ≃ₗ[ℂ] W') (hT : ∀ γ x, T (ρ γ x) = ρ' γ (T x)) (h : Formalism.AUTREP.IsAlgWeight L n ρ) :
    Formalism.AUTREP.IsAlgWeight L n ρ' := by
  obtain ⟨hf, κ, hfi, hd, bs, P, hP⟩ := h
  refine ⟨LinearEquiv.finiteDimensional T, κ, hfi, hd, bs.map T, P, fun γ γ₀ hm => ?_⟩
  rw [← hP γ γ₀ hm]
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Module.Basis.map_apply, ← hT, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem exists_weight_of_coefMap {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]
    {K : Type} [Field K] (φ : K →+* ℂ) (lab : ι → L →+* K) (emb : ι → L →+* ℂ) (hlab : ∀ τ x, φ (lab τ x) = emb τ x)
    (hinj : Function.Injective emb) (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ'))
    (lam : ι → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W)
    (c0 : VV K lam →ₛₗ[φ] W)
    (h0 : ∀ γ v, c0 (rhoVr lab lam (mtwRat (L := L) (n := n) γ) v) = ρ γ (c0 v))
    (h1 : LinearIndependent ℂ fun i => c0 (bVV K lam i))
    (h2 : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤) :
    ∃ (alg : Formalism.AUTREP.IsAlgWeight L n ρ) (irr : ρ.IsIrreducible), ∀ (a : NG.AlgWt L n) (τ : ι) (lam0 : Fin n → ℤ),
      NG.AlgWt.IsDual { W := W, ρ := ρ, alg := alg, irr := irr } a → a.HWAt (emb τ) lam0 → lam0 = (lam τ).w := by
  obtain ⟨T, hT⟩ := GlobalTheory.CoefReal.exists_scalarExt φ lam c0 h1 h2
  have hint : ∀ (γ : ReciprocityTheory.Aut.GQ L n) (x : VV ℂ lam), T (mtRep emb lam γ x) = ρ γ (T x) := by
    intro γ x
    have hfam : (fun τ => Formalism.UG.bc φ (invTrK (embGL lab (mtwRat (L := L) (n := n) γ)) τ)) =
        mtwInvTr (mtwEmb emb (mtwRat (L := L) (n := n) γ)) := by
      funext τ
      apply Units.ext
      ext a b
      simp [mtwInvTr, mtwEmb, inside₂, invTrK_coe, bc_coe, embGL_coe, hlab, map_inv_mat]
    have hL : T.toLinearMap ∘ₗ mtRep emb lam γ = ρ γ ∘ₗ T.toLinearMap := by
      refine LinearMap.ext_on_range (GlobalTheory.CoefModel.span_mapVV φ lam) fun i => ?_
      show T (rhoK lam (mtwInvTr (mtwEmb emb (mtwRat (L := L) (n := n) γ)))
        (GlobalTheory.CoefModel.mapVV φ lam _)) = ρ γ (T _)
      rw [← hfam, ← GlobalTheory.CoefModel.mapVV_rhoK, hT, hT]
      exact h0 γ _
    exact LinearMap.congr_fun hL x
  have hi : TenIrr emb lam := tenIrr_of' highest_weight_fixed_exists highest_weight_fixed_line emb hinj hcm lam
  have alg : Formalism.AUTREP.IsAlgWeight L n ρ := isAlgWeight_of_equiv (mtRep emb lam) ρ T hint (mtRep_alg emb lam)
  have irr : ρ.IsIrreducible :=
    GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv (mtRep emb lam) ρ T (fun g v => (hint g v).symm) hi
  refine ⟨alg, irr, fun a τ lam0 hd hw => ?_⟩
  obtain ⟨B, hB0, hB⟩ : ∃ B : W →ₗ[ℂ] a.W →ₗ[ℂ] ℂ, B ≠ 0 ∧ ∀ γ x y, B (ρ γ x) (a.ρ γ y) = B x y := hd
  have hd' : ∃ B : VV ℂ lam →ₗ[ℂ] a.W →ₗ[ℂ] ℂ, B ≠ 0 ∧ ∀ γ x y, B (mtRep emb lam γ x) (a.ρ γ y) = B x y := by
    refine ⟨B ∘ₗ T.toLinearMap, fun h => hB0 (LinearMap.ext fun w => ?_), fun γ x y => ?_⟩
    · obtain ⟨x, rfl⟩ := T.surjective w
      exact LinearMap.congr_fun h x
    · show B (T (mtRep emb lam γ x)) (a.ρ γ y) = B (T x) y
      rw [hint]
      exact hB γ (T x) y
  exact mtWtOf_hw_dual highest_weight_fixed_exists highest_weight_fixed_line emb hinj hcm lam τ a lam0 hd' hw

theorem wt_main : ∀ (D : D7) (V : HSp D) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), RatIso P e → ∀ (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W), Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → ∃ (alg : Formalism.AUTREP.IsAlgWeight D.host.E V.rank (wtRep c e)) (irr : (wtRep c e).IsIrreducible), ∀ (a : NG.AlgWt D.host.E V.rank) (τ : D.what₂.Tau) (lam0 : Fin V.rank → ℤ), NG.AlgWt.IsDual { W := c.W, ρ := wtRep c e, alg := alg, irr := irr } a → a.HWAt (Formalism.L2.embT D τ) lam0 → lam0 = (lam τ).w := by
  intro D V P e hR c lam c0 ht
  exact exists_weight_of_coefMap D.what₂.embLL (labLL D) (tauE D) GlobalTheory.CoefSpace.embLL_labLL (GlobalTheory.StdRat.tauE_injective D)
    (fun τ τ' h => (GlobalTheory.StdRat.tauE_cm D (tauE D τ')).1 ⟨τ', rfl⟩ ⟨τ, h⟩) lam (wtRep c e) c0
    (fun γ v => ht.1 (e γ) (mtwRat (L := D.host.E) (n := V.rank) γ)
      ((hR γ).2 _ (congrArg Units.val (mtwInc_mtwRatFun γ)).symm) v) ht.2.1 ht.2.2

end GlobalTheory.MtIn

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem cyc_mul_mem_UJset {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have h1 : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have h2 : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1, h2]

theorem clm_eq_zero_of_orbit {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (hi : IsIrredOn (UJset ε) σ)
    (L : H →L[ℂ] ℂ) {v : H} (hv : v ≠ 0) (h : ∀ g ∈ UJset ε, L (σ g v) = 0) (w : H) : L w = 0 := by
  let S : Submodule ℂ H :=
    { carrier := {x | ∀ g ∈ UJset ε, L (σ g x) = 0}
      add_mem' := fun ha hb g hg => by rw [map_add (f := _), map_add (f := _), ha g hg, hb g hg, add_zero]
      zero_mem' := fun g _ => by rw [map_zero, map_zero]
      smul_mem' := fun c x ha g hg => by rw [map_smul, map_smul, ha g hg, smul_zero] }
  have hc : IsClosed (S : Set H) := by
    have : (S : Set H) = ⋂ g ∈ UJset ε, {x | L (σ g x) = 0} := by
      ext x; simp only [Set.mem_iInter]; rfl
    rw [this]
    exact isClosed_biInter fun g _ => isClosed_eq (L.continuous.comp (σ g).continuous) continuous_const
  have hst : ∀ g ∈ UJset ε, ∀ x ∈ S, σ g x ∈ S := fun g hg x hx a ha => by
    have := hx (a * g) (cyc_mul_mem_UJset ha hg)
    rwa [hσ.1.2 a ha g hg] at this
  rcases hi S hc hst with h0 | h0
  · have : v ∈ S := h
    rw [h0] at this
    exact absurd this hv
  · have : w ∈ S := by rw [h0]; trivial
    have h1 := this 1 (by show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * 1 = Formalism.REAL.Jm ε; simp)
    rwa [hσ.1.1] at h1

theorem sobCont_eq_zero_of_orbit : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → ∀ v ∈ smSub G (trRep σ P), v ≠ 0 → (∀ g ∈ UJset ε, ℓ (σ g v) = 0) → ∀ w ∈ smSub G (trRep σ P), ℓ w = 0 := by
  intro n ε H _ _ _ σ P G hP hG hσ hi ℓ hℓ v hv hv0 h0 w hw
  obtain ⟨hb, hs⟩ := GlobalTheory.SobGarding.sobCont_gard n ε H σ P G hP hG hσ ℓ hℓ
  have key : ∀ φ, IsTest φ → ℓ (gard ε σ φ w) = 0 := fun φ hφ => by
    obtain ⟨C, hC⟩ := hb φ hφ
    let L : H →L[ℂ] ℂ :=
      (ℓ ∘ₗ GlobalTheory.LowTypeRestriction.garding hσ hφ.continuous hφ.2).mkContinuousOfExistsBound ⟨C, hC⟩
    refine clm_eq_zero_of_orbit hσ hi L hv0 (fun g hg => ?_) w
    show ℓ (gard ε σ φ (σ g v)) = 0
    rw [(hs _ (sigma_mem hP hG hσ hv hg)).2 φ hφ]
    have : ∀ a : Formalism.REAL.UJ ε, ℓ (σ (umat a) (σ g v)) = 0 := fun a => by
      have := h0 (umat a * g) (cyc_mul_mem_UJset a.2 hg)
      rwa [hσ.1.2 _ a.2 g hg] at this
    simp [this]
  have := eq_zero_of_forall_test (hs w hw).1 fun φ hφ => by rw [← (hs w hw).2 φ hφ, key φ hφ]
  have e : σ (umat (1 : Formalism.REAL.UJ ε)) w = w := by
    show σ 1 w = w
    rw [hσ.1.1]; rfl
  simpa only [e] using this

end GlobalTheory.SmVec
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sobolevContinuous_form_gardingVector : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → (∀ φ, IsTest φ → ∃ C : ℝ, ∀ w, ‖ℓ (gard ε σ φ w)‖ ≤ C * ‖w‖) ∧ ∀ w ∈ smSub G (trRep σ P), (Continuous fun g : Formalism.REAL.UJ ε => ℓ (σ (umat g) w)) ∧ ∀ φ, IsTest φ → ℓ (gard ε σ φ w) = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ℓ (σ (umat g) w) ∂(Formalism.REAL.muG ε) := by
  first | exact @GlobalTheory.SobGarding.sobCont_gard | exact GlobalTheory.SobGarding.sobCont_gard | (intros; apply GlobalTheory.SobGarding.sobCont_gard <;> assumption)
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.KAvgRank

open GlobalTheory.TypeSum.KCoef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem sigma_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (k₀ : KG ε) (w : H) :
    σ (toMK k₀) (kAvg ε σ e w) = kAvg ε σ (fun k => e (k₀⁻¹ * k)) w := by
  rw [kAvg, ← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hσ he w), kAvg,
    ← integral_mul_left_eq_self (fun k => e (k₀⁻¹ * k) • σ (toMK k) w) k₀]
  simp only [map_smul, inv_mul_cancel_left, sigma_K_mul hσ]

theorem exists_stable (hσ : IsURepOn (UJset ε) σ) {F : Submodule ℂ (KG ε → ℂ)} [FiniteDimensional ℂ F]
    (hc : ∀ φ ∈ F, Continuous φ) (hl : ∀ φ ∈ F, ∀ k₀ : KG ε, (fun k => φ (k₀ * k)) ∈ F) {e : KG ε → ℂ} (he : e ∈ F)
    (w : H) : ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧
      kAvg ε σ e w ∈ S ∧ IsKStableOn ε σ S := by
  let L : F →ₗ[ℂ] H :=
    { toFun := fun φ => kAvg ε σ φ w
      map_add' := fun x y => by
        simp only [kAvg, Submodule.coe_add, Pi.add_apply, add_smul]
        exact integral_add (integrable_avg hσ (hc _ x.2) w) (integrable_avg hσ (hc _ y.2) w)
      map_smul' := fun c x => by
        simp only [kAvg, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_assoc]
        exact integral_smul _ _ }
  refine ⟨LinearMap.range L, inferInstance, LinearMap.finrank_range_le L, ⟨⟨e, he⟩, rfl⟩, ?_⟩
  rintro k hk _ ⟨φ, rfl⟩
  obtain ⟨k₀, rfl⟩ : k ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hk
  exact ⟨⟨_, hl φ φ.2 k₀⁻¹⟩, (sigma_kAvg hσ (hc _ φ.2) k₀ w).symm⟩

theorem adjoint_mem (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) {Q : H →L[ℂ] H}
    (hQ : ∀ w, Q w = kAvg ε σ e w) {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hK : IsKStableOn ε σ S) {z : H}
    (hz : z ∈ S) : ContinuousLinearMap.adjoint Q z ∈ S := by
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal']
  intro u hu
  rw [ContinuousLinearMap.adjoint_inner_left, hQ, inner_kAvg hσ he]
  have : ∀ k : KG ε, ⟪z, σ (toMK k) u⟫_ℂ = 0 := fun k => by
    have h := inner_K hσ k⁻¹ u z
    rw [inv_inv] at h
    rw [← h]
    exact Submodule.inner_right_of_mem_orthogonal (hK _ (toMK_mem_K _) z hz) hu
  simp [this]

end GlobalTheory.TypeSum.KAvgRank

namespace GlobalTheory.TypeSum

theorem kAvg_finite_rank : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), Orthonormal ℂ a ∧ (∀ j, IsKFin ε σ (a j)) ∧ (∀ j, IsKFin ε σ (c j)) ∧ ∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j := by
  intro n ε H _ _ _ σ h e ⟨F, hF, heF, hc, ht⟩
  have hσ := h.1
  obtain ⟨Q, hQ⟩ := KCoef.exists_clm_kAvg hσ (hc e heF)
  let U : Submodule ℂ H := LinearMap.range (Q : H →ₗ[ℂ] H)
  have hU : ∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧
      u ∈ S ∧ IsKStableOn ε σ S := by
    rintro _ ⟨w, rfl⟩
    have := KAvgRank.exists_stable hσ hc (fun φ hφ k₀ => (ht φ hφ k₀).1) heF w
    rwa [← hQ] at this
  haveI : FiniteDimensional ℂ U := GlobalTheory.T.finiteDimensional_of_bounded_Korbit_dimension n ε H σ h U _ hU
  let b := stdOrthonormalBasis ℂ U
  refine ⟨_, fun j => (b j : H), fun j => ContinuousLinearMap.adjoint Q (b j), ?_, fun j => ?_, fun j => ?_,
    fun w => ?_⟩
  · exact b.orthonormal.comp_linearIsometry U.subtypeₗᵢ
  · obtain ⟨S, h1, -, h2, h3⟩ := hU _ (b j).2
    exact ⟨S, h1, h2, h3⟩
  · obtain ⟨S, h1, -, h2, h3⟩ := hU _ (b j).2
    exact ⟨S, h1, KAvgRank.adjoint_mem hσ (hc e heF) hQ h3 h2, h3⟩
  · have := congrArg Subtype.val (b.sum_repr' ⟨Q w, ⟨w, rfl⟩⟩)
    rw [← hQ]
    simp only [ContinuousLinearMap.adjoint_inner_left]
    simpa using this.symm

end GlobalTheory.TypeSum
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.tracePowerListProduct_mem_chernCoefficientRealSpan : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (l : List (ι × ℕ)), (∀ x ∈ l, 1 ≤ x.2) → (l.map Prod.snd).sum = n → (fun A : Mat m S => trProd l A) ∈ Reach m n S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach | exact GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach <;> assumption)
end
