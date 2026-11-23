module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle201
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle211
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle175
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle309
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle016
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

theorem _root_.GlobalTheory.T.self_dual_lattice_has_rigidification : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK → IsSelfDualC V Λ → ∃ r : Rig V, r.Λ = Λ ∧ r.Is := by
  first | exact @GlobalTheory.RigExists.exists_rig | exact GlobalTheory.RigExists.exists_rig | (intros; apply GlobalTheory.RigExists.exists_rig <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaTildeOfComponents

theorem isEtaTilde_of_chrEq : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (η : (AE D)ˣ →* Circle), ChrEq η C.eta → ResEta D η 1 → IsEtaTilde D η := by
  intro D C η hc hres
  have hE := C.isEta

  have hInf : C.eta.HasInfQ (tauE D) (fun _ => (1 / 2 : ℚ)) := by
    refine ⟨fun _ => 1, fun _ => by norm_num, fun k => ?_⟩
    rw [hE.inf k]
    exact (Fintype.prod_equiv D.eTau _ _ (fun _ => rfl)).symm
  have h1 : 1 ∈ intAE D := by
    apply AddSubgroup.subset_closure
    refine ⟨1, fun v => ?_, 1, rfl⟩
    simp [evalV, (v.adicCompletionIntegers D.host.F).one_mem]
  refine ⟨hc.1, ?_, hres, fun τ => GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D η C.eta _ hc hInf τ⟩

  intro x hx1 hx2 hx3
  refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D η C.eta hc ?_ 1 (fun P _ => hE.unr P) x ⟨hx1, hx2, hx3⟩
    ⟨finPart D (x : AE D) - 1, sub_mem hx2 h1, (one_nsmul _).symm⟩
  intro P y hy _
  exact hE.unr P y hy

end GlobalTheory.EtaTildeOfComponents
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaTildeOddParity

theorem isEta_sq (D : D7) (η : (AF D.host.F)ˣ →* Circle) (h : IsEta D η) (a : (AF D.host.F)ˣ) : η a ^ 2 = 1 := by
  obtain ⟨-, -, hnorm, -⟩ := h
  have hn := hnorm (idF D a)
  rw [Formalism.L2.Theta.norm_idF, map_pow] at hn
  exact hn

private theorem hasInfQ_half_of_isEtaT (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (h : Formalism.L2.Host.IsEtaT D.host χ) :
    χ.HasInfQ (tauE D) (fun _ => 1 / 2) := by
  unfold Formalism.L2.Host.HChar.HasInfQ
  refine ⟨fun _ => 1, fun _ => by norm_num, ?_⟩
  intro k
  rw [h.inf k]
  symm
  exact Fintype.prod_equiv D.eTau _ _ (fun _ => rfl)

private theorem one_mem_intAE_twisted_operators (D : D7) : 1 ∈ intAE D := by
  apply AddSubgroup.subset_closure
  rw [Set.mem_setOf_eq]
  refine ⟨1, ?_, 1, ?_⟩
  · intro v
    first
      | exact one_mem _
      | (rw [map_one]; exact one_mem _)
      | simp [evalV]
  · rw [Algebra.TensorProduct.one_def]
    all_goals simp

theorem isEtaTilde_of_odd : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → Formalism.L2.Host.IsEtaT D.host χ → ∀ (μ : (AE D)ˣ →* Circle) (n m : ℕ), ResEta D μ n → ResEta D (μ * c⁻¹) m → Odd (n + m) → IsEtaTilde D c := by
  intro D c χ hc hχ μ n m hμ hμc hodd
  unfold IsEtaTilde
  refine ⟨hc.1, ?_, ?_, fun τ => GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D c χ (fun _ => 1 / 2) hc
    (hasInfQ_half_of_isEtaT D χ hχ) τ⟩
  ·
    intro x h1 h2 h3
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D c χ hc (fun P => ?_) 1 (fun P _ => hχ.unr P) x ⟨h1, h2, h3⟩
      ⟨finPart D (x : AE D) - 1, sub_mem h2 (one_mem_intAE_twisted_operators D), by rw [one_smul]⟩
    intro y hy _
    exact hχ.unr P y hy
  ·
    unfold ResEta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome at hμ hμc ⊢
    refine ⟨hμ.1, fun η hη a => ?_⟩
    have e1 : μ (idF D a) = η a ^ n := hμ.2 η hη a
    have e2 : (μ * c⁻¹) (idF D a) = η a ^ m := hμc.2 η hη a
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, e1] at e2
    have hs : η a ^ 2 = 1 := isEta_sq D η hη a
    have hi : (η a ^ m)⁻¹ = η a ^ m := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul, pow_mul, hs, one_pow]
    have hc' : c (idF D a) = η a ^ n * (η a ^ m)⁻¹ := by
      rw [← e2, mul_inv_rev, inv_inv, mul_comm (c _), mul_inv_cancel_left]
    obtain ⟨k, hk⟩ := hodd
    show c (idF D a) = η a ^ 1
    rw [pow_one, hc', hi, ← pow_add, hk, pow_succ, pow_mul, hs, one_pow, one_mul]

end GlobalTheory.EtaTildeOddParity
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.KHeisComm

variable {F : Type} [Field F] [NumberField F]

theorem archimedean_isomorphism_split_trivial {κ : Type} (z : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.ArchIsom.r0 F κ (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0)) = 1 := by
  change GlobalTheory.ArchIsom.g0 F κ 0 = 1
  simp [GlobalTheory.ArchIsom.g0, Set.indicator_of_mem (GlobalTheory.ArchIsom.zero_mem_intPts (F := F) κ)]

theorem tens_split {κ : Type} (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (z : κ → mixedEmbedding.mixedSpace F) :
    tens (evI F) φ (GlobalTheory.ArchIsom.r0 F κ) (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0)) = φ z := by
  have hz : (fun i => evI F (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0) i)) = z :=
    funext fun i => GlobalTheory.ArchIsom.evI_splitEquiv κ _ i
  simp only [tens, hz, archimedean_isomorphism_split_trivial, mul_one]


open scoped Classical in
theorem proj_mem_adm {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

end GlobalTheory.KHeisComm


open GlobalTheory.KHeisComm in
open scoped Classical in
theorem GlobalTheory.KHeisComm.actsD_heisLine_mat_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∀ f f₁ fk h : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ → Acts (evI F) (om (k, 1)) f fk →
      Acts (evI F) (om (k, 1)) f₁ h → ActsD (evI F) (M.heisLine B.ψ (mat k * u)) fk h := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k _ u hu f f₁ fk h hD hA hA₁
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨D, hDD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hψ
  obtain ⟨D₁, hD₁⟩ := GlobalTheory.HeisDeriv.exists_heisLine_deriv M B.ψ hψ (mat k * u)
  have hg0 := GlobalTheory.ArchIsom.standard_vector_mem_schwartz_bruhat (F := F) (Fin n × Fin d)

  have hf₁ : (D u f : SInf F (Fin n × Fin d)) = f₁ := by
    refine SchwartzMap.ext fun z => ?_
    set x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (z, 0)
    have a1 : HasDerivAt (fun t => M.heisLine B.ψ u t (tens (evI F) (⇑f) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d))) x)
        (pureA F (⇑(D u f)) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d)) x) 0 :=
      (hDD u hu f).1 _ hg0 _ (proj_mem_adm x)
    have a2 := hD _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f) x
    have e := a1.unique a2
    rw [← GlobalTheory.ArchIsom.tensor_at_standard_point, tens_split, tens_split] at e
    exact e
  suffices e : h = D₁ fk by rw [e]; exact hD₁ fk
  refine SchwartzMap.ext fun z => ?_
  set x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (z, 0)
  have hl := hS.adm (k, 1) _ (proj_mem_adm x)
  have b1 := (hDD u hu f).1 _ hg0 _ hl
  have hmem : ∀ g : SInf F (Fin n × Fin d), tens (evI F) (⇑g) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d)) ∈ schA F (Fin n × Fin d) :=
    fun g => (GlobalTheory.ArchIsom.restriction_at_standard_point _ g).2
  have hfun : (fun t : ℝ => ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om (k, 1))
      (M.co.rho B.ψ (realAd F t • u) (pureA F (⇑f) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d))))) =
      fun t => M.heisLine B.ψ (mat k * u) t (tens (evI F) (⇑fk) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d))) x := by
    funext t
    rw [LinearMap.comp_apply, LinearMap.proj_apply, ← GlobalTheory.ArchIsom.tensor_at_standard_point, hS.impl (k, 1) _ _ (hmem f),
      hA _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f)]
    have hw : actAB (cA σ) ((k, 1) : UA σ X.J × UA σ W.J) (realAd F t • u) = realAd F t • (mat k * u) := by
      simp only [actAB, mat, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
    rw [hw]
    rfl
  have hval : ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om (k, 1))
      (pureA F (⇑(D u f)) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d))) = h z := by
    rw [LinearMap.comp_apply, LinearMap.proj_apply, hf₁, ← GlobalTheory.ArchIsom.tensor_at_standard_point, hA₁ _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f₁),
      tens_split]
  dsimp only at b1
  rw (config := { transparency := .all }) [hfun, hval] at b1
  have b2 := hD₁ fk _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ fk) x
  rw [tens_split] at b2
  exact b1.unique b2
end
end

section

noncomputable section

namespace GlobalTheory.LFun.ExSatU

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem exists_hasSatU : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : w.adicCompletion E) (σ : w.adicCompletion E →+* w.adicCompletion E) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    ρ.IsIrreducible → IsAdmissible ρ → GlobalTheory.LGrp.IsSpherical ρ (KU σ n) → ∃ α, HasSatU ϖ q ρ α := by
  intro E _ _ w ϖ σ q n hU V _ _ ρ hi ha hs
  obtain ⟨ho, hc⟩ := GlobalTheory.T.isOpen_isCompact_unitaryIntegralPoints (w.adicCompletion E) ϖ σ q n hU
  exact GlobalTheory.LFun.SatCompare.exists_hasSatU hU ⟨ha.1, hi⟩ (ha.2 _ ho hc) hs

end GlobalTheory.LFun.ExSatU

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem semilinear_injective_of_indep {K L V W ι : Type} [Field K] [Field L] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module L W] {φ : K →+* L} (b : Module.Basis ι K V) (c : V →ₛₗ[φ] W)
    (h : LinearIndependent L fun a => c (b a)) : Function.Injective c := by
  refine (injective_iff_map_eq_zero c).2 fun v hv => ?_
  have hexp : c v = ∑ i ∈ (b.repr v).support, φ (b.repr v i) • c (b i) := by
    conv_lhs => rw [← b.linearCombination_repr v]

    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smulₛₗ c _ _
  have hz := linearIndependent_iff'.1 h (b.repr v).support (fun i => φ (b.repr v i)) (by rw [← hv, hexp])
  have hrepr : b.repr v = 0 := by
    ext i
    rw [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hne
    exact hne (φ.injective ((hz i (Finsupp.mem_support_iff.2 hne)).trans (map_zero φ).symm))
  exact b.repr.injective (hrepr.trans (map_zero _).symm)

theorem hkF_single_one {D : D7} (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (d : List ℤ)
    (F : Bridge.Gf V → W) (h : Bridge.Gf V) :
    GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F h = ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (h * (finHom V).rangeRestrict γ) := by
  simp only [GlobalTheory.Hk3.hkF]
  rw [Finsupp.sum_single_index, one_smul]
  exact zero_smul ℂ _

theorem hkF_transfer {D : D7} (V : HSp D) {K U W W' : Type} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] {φ σ : K →+* ℂ} (c₀ : U →ₛₗ[φ] W) (c₁ : U →ₛₗ[σ] W') (inj : Function.Injective c₀)
    (F : Bridge.Gf V → W) (F' : Bridge.Gf V → W') (hb : ∀ h, ∃ v, F h = c₀ v ∧ F' h = c₁ v)
    (P : Pl D.host.E) (d : List ℤ) (a : K) (e : GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F = φ a • F) :
    GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F' = σ a • F' := by
  choose v hv using hb
  funext h
  have e' := congrFun e h
  rw [hkF_single_one, Pi.smul_apply] at e'
  rw [hkF_single_one, Pi.smul_apply]
  have key : ∑ γ ∈ GlobalTheory.Hk3.rep V P d, v (h * (finHom V).rangeRestrict γ) = a • v h := by
    apply inj

    rw [map_sum, map_smulₛₗ]
    simp only [← fun x => (hv x).1]
    exact e'
  simp only [fun x => (hv x).2]

  rw [← map_smulₛₗ, ← key, map_sum]

theorem eigF_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ a x, GlobalTheory.ConjScalar.EigK R i a x → GlobalTheory.ConjScalar.EigF R i (fun P d => σ (a P d)) (H.e (j x)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ gramR c0R c0L hT i σ c c₁ H j hc a x hx
  have hind : LinearIndependent ℂ fun k => c0L i (bVV D.what₂.LL (lamV D i) k) :=
    (Formalism.IndefR.Bridge.FamTie.mapL hT i).2.1
  have inj : Function.Injective (c0L i) := semilinear_injective_of_indep (bVV D.what₂.LL (lamV D i)) (c0L i) hind
  intro P d hG hL
  have e := hx P d hG hL
  exact hkF_transfer (Vc D i) (c0L i) c₁ inj _ _ (hc.base x) P d (a P d) e

end GlobalTheory.ConjScalar
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField.Read

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem mult_inv {V : HSp D} {S : D.what₂.Tau → _} (θ) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) {Φ : MMap M}
    (hΦ : Φ ∈ Mult θ M J χ) (v : M.Vec) : ∀ γ ∈ GQ V, ∀ g, Φ v (γ * g) = Φ v g := by
  intro γ hγ g
  induction hΦ using Submodule.span_induction with
  | mem x hx => exact (hx.aut v).left γ hγ g
  | zero => rfl
  | add x y _ _ hx hy => simp only [_root_.add_apply, Pi.add_apply, hx, hy]
  | smul a x _ hx => simp only [_root_.smul_apply, Pi.smul_apply, hx]

theorem eq_of_out {W : HSp D} {Φ Ψ : GA D W → ℂ} (hΦ : ∀ γ ∈ GQ W, ∀ g, Φ (γ * g) = Φ g)
    (hΨ : ∀ γ ∈ GQ W, ∀ g, Ψ (γ * g) = Ψ g) (h : ∀ q : AutQ W, Φ q.out = Ψ q.out) : Φ = Ψ := by
  funext g
  let q : AutQ W := Quotient.mk _ g
  have hr : g * q.out⁻¹ ∈ GQ W := QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq q))
  have h1 := hΦ _ hr q.out
  have h2 := hΨ _ hr q.out
  rw [inv_mul_cancel_right] at h1 h2
  rw [h1, h2, h q]

theorem ev_sum {L H Y : Type} [Field L] [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module L Y] {σ : L →+* ℂ}
    (j : Y →ₛₗ[σ] H) {V : HSp D} {S : D.what₂.Tau → _} {M : DSModel V S} (e : H →ₗ[ℂ] MMap M) (v : M.Vec) (g : GA D V) {m : ℕ}
    (a : Fin m → L) (y : Fin m → Y) : e (j (∑ l, a l • y l)) v g = ∑ l, σ (a l) * e (j (y l)) v g := by

  rw [map_sum, map_sum, _root_.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smulₛₗ, map_smul]
  rfl

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem ev_base (fw : FWTie T R κ v₀) (hev : fw.Evaluates) {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) (f : Cu T κ i) (h : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).e (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
        O.phi (T.cE ((i : ℕ) + 1) O.s0) (f : T.R ((i : ℕ) + 1)) h := by
  have e : res T (sg0 D A) = O.s0 :=
    ((congrArg (res T) (show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0)).trans
      (res_embLL T fw.alg_eq fw.laws.pins.2.2.1)).trans (sOv_eq T.toCore O.c' O.hle).symm
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) e).trans O.hV
  have h1 := hev i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV f
  have key : ∀ (σ σ' : T.Q.c.F →+* ℂ) (_ : σ' = σ) (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W)
      (hV' : T.V ((i : ℕ) + 1) σ' = W) (g : GA D W), phiC T hV' (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) g =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * adel W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1))) g := by
    intro σ σ' e W hV hV' g
    subst e
    subst hV
    rfl
  exact (congrFun h1 h).trans (key _ _ e _ O.hV hV h)



theorem exists_comb {i : Fin D.R.m} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec} {ι x₀} {ph : ℂ}
    (hn : κ.n = (Vc D i).rank) (O : OMDat T.toCore R i T0 id) (hP : O.Pins κ v ι x₀)
    (hrow : O.OneMapOf κ v (T.cE ((i : ℕ) + 1) O.s0) ph) (t : T0) (y : A.fam.amb.FL i t) :
    ∃ ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange, ∃ (m : ℕ) (as : Fin m → O.c'.F) (fs : Fin m → T.cuspA ((i : ℕ) + 1) (wtA κ) κ.n),
      ∀ q : AutQ (Wc D i), ph * R.thF i t (R.jV i t y) v q.out =
        ∑ l, ze * (as l : ℂ) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
          O.phi (T.cE ((i : ℕ) + 1) O.s0) (fs l : T.R ((i : ℕ) + 1)) q.out) := by
  obtain ⟨hE, ⟨-, hC, hA, -, -, z, -, h1⟩, -⟩ := hrow
  have aux1 := h1 t
  obtain ⟨ze, a1, -, h1⟩ := aux1
  have aux2 := (hP.tuple t).reps
  obtain ⟨h, J', -, p2, p3, p4⟩ := aux2
  have aux3 := p2 y
  obtain ⟨x, hx⟩ := aux3
  have e := p3 _ x hx
  have aux4 := h1 x ((p4 x).2 ⟨y, hx⟩)
  obtain ⟨⟨f, hf, hf'⟩, h2⟩ := aux4
  have hs := ((mem_cusp _ _ _ _ _ _).1 hf).1
  have h4 := h2 f hs hf'
  rw [← hn] at hf
  have aux5 := hC _ _ f hf
  obtain ⟨m, as, fs, hfs, hBC⟩ := aux5
  have aux6 := hP.lift.lev z
  obtain ⟨k, hk, -⟩ := aux6
  have h5 := rdU_unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c') (hA _ _ z m as fs f ((mem_cusp _ _ _ _ _ _).1 hf).1
    (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC)
  refine ⟨ze, a1, m, as, fun l => ⟨_, (hE z k hk (fs l) (hfs l)).1⟩, fun q => ?_⟩
  have h6 : ph * R.thF i t (R.jV i t y) v q.out = ze * T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 *
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (O.mu q.out *
        rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) (actLev O.c' O.lev2 z f) (O.dict q.out).1 (O.dict q.out).2) :=
    (congrArg (ph * ·) (congrFun e q)).symm.trans (h4 q)
  rw [h6, h5]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  show _ = ze * (as l : ℂ) * (_ * (T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 * O.mu q.out *
    rdU (T.U ((i : ℕ) + 1) O.s0) (actLev T.Q.c O.lev2 z (fs l)) (O.dict q.out).1 (O.dict q.out).2))
  show _ * (_ * ((as l : ℂ) * _)) = _
  ring



theorem ratAt_of_oneMap (fw : FWTie T R κ v₀) {ph : ℂ} {i : Fin D.R.m} (hW : R.models_HW) (hP : R.IsThP) (hU : R.LUnif)
    (hev : fw.Evaluates) (hinj : EvInj T R v₀) (h : OneMapOverL T R κ v₀ ph i) (t : T0) : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.RatAt R i ph t := by
  intro x₀
  obtain ⟨O, hF, hpin, hrow⟩ := h
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have aux7 := exists_comb hn O hpin hrow t x₀
  obtain ⟨ze, hze, m, as, fs, hq⟩ := aux7
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have ha : ∀ l, ∃ a : D.what₂.LL, sg0 D A a = ze * (as l : ℂ) := fun l => by
    have aux8 := AlgHom.mem_fieldRange.1 (mul_mem hze (hF.le (as l).2))
    obtain ⟨a, ha⟩ := aux8
    exact ⟨a, (RingHom.congr_fun hs a).trans ha⟩
  choose a ha using ha
  have hmem := (hW i (sg0 D A)).2.1.ge (hP.thF_mem i t (R.jV i t x₀))
  obtain ⟨w, hw⟩ := hmem
  have hinv : ∀ u : (R.HW i (sg0 D A)).H, ∀ γ ∈ GQ (Wc D i), ∀ g,
      evAt R i _ (v₀ i _) u (γ * g) = evAt R i _ (v₀ i _) u g := fun u =>
    mult_inv R.θ _ _ _ ((hW i _).2.1.le (LinearMap.mem_range_self _ u)) _
  have e0 : (R.HW i (sg0 D A)).e (ph • w) = ph • R.thF i t (R.jV i t x₀) :=
    (map_smul (R.HW i (sg0 D A)).e ph w).trans (congrArg (ph • ·) hw)
  have key : (R.FW i).j (sg0 D A) (∑ l, a l • ((fw.e i (fs l) : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) = ph • w := by
    refine hinj i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) (eq_of_out (hinv _) (hinv _) fun q => ?_)
    have e1 : evAt R i _ (v₀ i _) (ph • w) q.out = ph * R.thF i t (R.jV i t x₀) (v₀ i _) q.out :=
      congrArg (fun Φ : MMap (R.MW i (sg0 D A)) => Φ (v₀ i _) q.out) e0
    refine (ev_sum _ _ _ _ _ _).trans (Eq.trans ?_ ((hq q).symm.trans e1.symm))
    exact Finset.sum_congr rfl fun l _ => congrArg₂ (· * ·) (ha l) (ev_base fw hev O (fs l) q.out)
  have h1 := (congrArg (R.HW i (sg0 D A)).e key).trans e0
  exact ⟨_, h1, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.proj_clause R i ph t hP.thG (hW i _).1 (hU i _).2.2 _ _ h1⟩

theorem rat_of_oneMapOverL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T R κ v₀) (ph : ℂ) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → R.IsThP → R.LUnif → fw.Evaluates → EvInj T R v₀ → GlobalTheory.TwistField.OneMapOverL T R κ v₀ ph i → ∀ t : T0, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.RatAt R i ph t :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ fw _ _ _ _ hM hP hU hev hinj h t => ratAt_of_oneMap fw hM.HW hP hU hev hinj h t

end GlobalTheory.TwistField.Read
end
end
