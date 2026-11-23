module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle009
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Int
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

open IsLocalRing KaehlerDifferential TensorProduct

theorem PolyDerivationsDetectSquare.of_perfectField
    (h₁ : PerfectFieldExtensionFormallySmooth.Statement) (h₂ : PolyKaehlerFree.Statement)
    (F k : Type) [Field F] [Field k] [Algebra F k] [PerfectField F] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] (g : MvPolynomial (Fin n) k) (hg : g ∈ p)
    (hD : ∀ D : Derivation ℤ (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k), D g ∈ p) :
    algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
      maximalIdeal (Localization.AtPrime p) ^ 2 := by
  classical

  have : Algebra.FormallySmooth F k := h₁ F k
  have : Algebra.FormallySmooth F p.ResidueField := h₁ F p.ResidueField
  have : Algebra.FormallySmooth F (MvPolynomial (Fin n) k) :=
    Algebra.FormallySmooth.comp F k (MvPolynomial (Fin n) k)
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime p) p.ResidueField) :=
    IsLocalRing.residue_surjective
  obtain ⟨ret, hret⟩ := (Algebra.FormallySmooth.iff_split_injection (R := F)
    (P := Localization.AtPrime p) hsurj).mp inferInstance
  have hinj : Function.Injective (kerCotangentToTensor F (Localization.AtPrime p) p.ResidueField) :=
    Function.LeftInverse.injective (g := ret) fun x => LinearMap.congr_fun hret x
  have hgI : algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
      RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) := by
    rw [RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hg

  have : Module.Free (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄F] := h₂ F k n
  let b := Module.Free.chooseBasis (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄F]
  have hc : ∀ α, b.repr (D F (MvPolynomial (Fin n) k) g) α ∈ p := fun α =>
    hD (((b.coord α).compDer (D F (MvPolynomial (Fin n) k))).restrictScalars ℤ)

  have hzero : kerCotangentToTensor F (Localization.AtPrime p) p.ResidueField
      (Ideal.toCotangent _ ⟨_, hgI⟩) = 0 := by
    change (1 : p.ResidueField) ⊗ₜ[Localization.AtPrime p]
      D F (Localization.AtPrime p) (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g) = 0
    rw [← map_D F F (MvPolynomial (Fin n) k) (Localization.AtPrime p),
      ← b.linearCombination_repr (D F (MvPolynomial (Fin n) k) g), Finsupp.linearCombination_apply,
      map_finsuppSum, Finsupp.sum, tmul_sum]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [LinearMap.map_smul, ← algebraMap_smul (Localization.AtPrime p), tmul_smul,
      ← algebraMap_smul p.ResidueField, ← IsScalarTower.algebraMap_apply,
      Ideal.algebraMap_residueField_eq_zero.mpr (hc α), zero_smul]
  have h0 := hinj (hzero.trans (map_zero _).symm)
  have hker : RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) =
      maximalIdeal (Localization.AtPrime p) := IsLocalRing.ker_residue
  rw [Ideal.toCotangent_eq_zero] at h0
  rw [← hker]
  exact h0

theorem PolyDerivationsDetectSquare.proof (h₁ : PerfectFieldExtensionFormallySmooth.Statement)
    (h₂ : PolyKaehlerFree.Statement) : PolyDerivationsDetectSquare.Statement := by
  intro k _ n p _ g hg hD
  obtain ⟨q, hq⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k q with hqp | rfl
  · have : Fact q.Prime := ⟨hqp⟩
    let _ : Algebra (ZMod q) k := ZMod.algebra k q
    exact PolyDerivationsDetectSquare.of_perfectField h₁ h₂ (ZMod q) k n p g hg hD
  · have : CharZero k := CharP.charP_to_charZero k
    exact PolyDerivationsDetectSquare.of_perfectField h₁ h₂ ℚ k n p g hg hD

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

theorem eval_map_eval_eq_sum {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (w : Fin d → ℂ) (s : ℂ) :
    (p.map (MvPolynomial.eval w)).eval s =
      ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval w (p.coeff i) * s ^ i := by
  rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (Polynomial.natDegree_map_le) (Nat.lt_succ_self _))]
  simp [Polynomial.coeff_map]

theorem analyticAt_eval_map {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (v : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval v.1)).eval v.2) v := by
  have h : (fun v : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval v.1)).eval v.2) =
      fun v => ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval v.1 (p.coeff i) * v.2 ^ i := by
    funext v; exact eval_map_eval_eq_sum p v.1 v.2
  rw [h]
  refine Finset.analyticAt_fun_sum (𝕜 := ℂ) _ fun i _ => ?_
  refine AnalyticAt.mul ?_ (analyticAt_snd.pow i)
  exact (AnalyticOnNhd.eval_mvPolynomial (p.coeff i) v.1 trivial).comp analyticAt_fst

theorem SimpleRootBranch.proof : SimpleRootBranch.Statement := by
  intro d p y τ hroot hder
  set F : (Fin d → ℂ) × ℂ → ℂ := fun v => (p.map (MvPolynomial.eval v.1)).eval v.2 with hFdef
  have hcd : ContDiffAt ℂ 1 F (y, τ) := (analyticAt_eval_map p (y, τ)).contDiffAt

  have hpart : fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight ((p.map (MvPolynomial.eval y)).derivative.eval τ) := by
    have h1 : HasFDerivAt (fun s : ℂ => F (y, s))
        (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ :=
      ((analyticAt_eval_map p (y, τ)).differentiableAt.hasFDerivAt).comp τ
        ((hasFDerivAt_const y τ).prodMk (hasFDerivAt_id τ))
    exact h1.unique ((p.map (MvPolynomial.eval y)).hasDerivAt τ).hasFDerivAt
  have hinv : (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩
    ext; simp
  set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
  have hψy : ψ y = τ := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hFu : F (y, τ) = 0 := hroot
  obtain ⟨U₀, hU₀, B₀, hB₀, hsub⟩ :=
    mem_nhds_prod_iff.mp (hcd.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv)
  obtain ⟨B, hBsub, hBo, hτB⟩ := mem_nhds_iff.mp hB₀
  have hψcd : ContDiffAt ℂ 1 ψ y := hcd.contDiffAt_implicitFunction one_ne_zero hinv
  have hψB : ∀ᶠ w in 𝓝 y, ψ w ∈ B :=
    hψcd.continuousAt.preimage_mem_nhds (by rw [hψy]; exact hBo.mem_nhds hτB)
  obtain ⟨U, hUsub, hUo, hyU⟩ := eventually_nhds_iff.mp
    (((show ∀ᶠ w in 𝓝 y, w ∈ U₀ from hU₀).and (hψcd.eventually (by simp))).and hψB)
  refine ⟨U, B, ψ, hUo, hyU, hBo, hτB, fun w hw => ?_, hψy, fun w hw => ⟨(hUsub w hw).2, ?_⟩⟩
  · exact ((hUsub w hw).1.2.differentiableAt one_ne_zero).differentiableWithinAt
  · intro s hs
    have h := hsub (Set.mk_mem_prod (hUsub w hw).1.1 (hBsub hs))
    simp only [Set.mem_ofPred_eq, hFu] at h
    rw [Polynomial.IsRoot.def]
    exact h.trans eq_comm

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

open Polynomial IntermediateField

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

variable {F K B : Type*} [Field F] [Field K] [Algebra F K] [CommRing B] [Algebra F B]

def IsGoodPartialLift (p : ℕ) (N : Ideal B) (u : K →ₐ[F] B ⧸ N) (ψ : K →+* B)
    (σ : Σ L : IntermediateField F K, L →ₐ[F] B) : Prop :=
  (∀ z : K, ∃ h : z ^ p ∈ σ.1, σ.2 ⟨z ^ p, h⟩ = ψ z) ∧ ∀ y : σ.1, Ideal.Quotient.mk N (σ.2 y) = u y

def PartialLiftLE (σ τ : Σ L : IntermediateField F K, L →ₐ[F] B) : Prop :=
  ∃ h : σ.1 ≤ τ.1, ∀ y : σ.1, τ.2 (IntermediateField.inclusion h y) = σ.2 y

theorem PartialLiftLE.trans {a b d : Σ L : IntermediateField F K, L →ₐ[F] B} (h₁ : PartialLiftLE a b)
    (h₂ : PartialLiftLE b d) : PartialLiftLE a d := by
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  exact ⟨h₁.trans h₂, fun y => by rw [← h₁' y, ← h₂' (IntermediateField.inclusion h₁ y)]; rfl⟩

theorem exists_isGoodPartialLift_upperBound {p : ℕ} {N : Ideal B} {u : K →ₐ[F] B ⧸ N} {ψ : K →+* B}
    (c : Set {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ})
    (hc : IsChain (fun a b => PartialLiftLE a.1 b.1) c) (hne : c.Nonempty) :
    ∃ ub : {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ},
      ∀ a ∈ c, PartialLiftLE a.1 ub.1 := by
  obtain ⟨i₀, hi₀⟩ := hne
  have : Nonempty c := ⟨⟨i₀, hi₀⟩⟩
  let t : c → IntermediateField F K := fun i => i.1.1.1
  have dir : Directed (· ≤ ·) t := by
    intro i j
    by_cases hij : i = j
    · exact ⟨i, le_rfl, hij ▸ le_rfl⟩
    rcases hc i.2 j.2 (fun h => hij (Subtype.ext h)) with h | h
    · exact ⟨j, h.1, le_rfl⟩
    · exact ⟨i, le_rfl, h.1⟩
  have dir' : Directed (· ≤ ·) (fun i => (t i).toSubalgebra) := dir.mono_comp _ (fun _ _ h => h)
  let f : ∀ i, (t i).toSubalgebra →ₐ[F] B := fun i => i.1.1.2
  have hf : ∀ (i j : c) (h : (t i).toSubalgebra ≤ (t j).toSubalgebra),
      f i = (f j).comp (Subalgebra.inclusion h) := by
    intro i j h
    ext y
    by_cases hij : i = j
    · subst hij; rfl
    rcases hc i.2 j.2 (fun h => hij (Subtype.ext h)) with ⟨h', h''⟩ | ⟨h', h''⟩
    · exact (h'' y).symm
    · exact h'' (Subalgebra.inclusion h y)
  have hT : (iSup t).toSubalgebra ≤ ⨆ i, (t i).toSubalgebra :=
    (IntermediateField.toSubalgebra_iSup_of_directed dir).le
  let φ : ↥(iSup t) →ₐ[F] B := Subalgebra.iSupLift _ dir' f hf _ hT
  have hφ : ∀ (i : c) (y : K) (hy : y ∈ t i), φ ⟨y, (le_iSup t i) hy⟩ = i.1.1.2 ⟨y, hy⟩ :=
    fun i y hy => Subalgebra.iSupLift_mk _ (i := i) ⟨y, hy⟩ _
  refine ⟨⟨⟨iSup t, φ⟩, ⟨fun z => ?_, fun y => ?_⟩⟩,
    fun a ha => ⟨le_iSup t ⟨a, ha⟩, fun y => hφ ⟨a, ha⟩ y.1 y.2⟩⟩
  · obtain ⟨h, h'⟩ := (i₀.2).1 z
    exact ⟨le_iSup t ⟨i₀, hi₀⟩ h, (hφ ⟨i₀, hi₀⟩ _ h).trans h'⟩
  · have hy : (y : K) ∈ ⋃ i, (t i : Set K) := by
      rw [← IntermediateField.coe_iSup_of_directed dir]; exact y.2
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    rw [show y = ⟨y, (le_iSup t i) hi⟩ from rfl, hφ i y hi]
    exact i.1.2.2 ⟨y, hi⟩

theorem exists_isGoodPartialLift_frobenius [PerfectField F] (p : ℕ) [hp : Fact p.Prime] [CharP F p]
    {N : Ideal B} (hpB : (p : B) = 0) (hN : N ^ 2 = ⊥) (u : K →ₐ[F] B ⧸ N) :
    ∃ σ, IsGoodPartialLift p N u ((sqZeroFrobeniusLift N hp.out hpB hN).comp u.toRingHom) σ := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  set P := sqZeroFrobeniusLift N hp.out hpB hN
  set ψ : K →+* B := P.comp u.toRingHom
  let L₀ : IntermediateField F K :=
    { (frobenius K p).fieldRange with
      algebraMap_mem' := fun a => ⟨algebraMap F K ((frobeniusEquiv F p).symm a), by
        rw [frobenius_def, ← map_pow]; congr 1; exact (frobeniusEquiv F p).apply_symm_apply a⟩ }
  let e := (frobenius K p).rangeRestrictFieldEquiv
  have he : ∀ (y : (frobenius K p).fieldRange) (z : K), (y : K) = z ^ p → e.symm y = z :=
    fun y z h => e.symm_apply_eq.mpr (Subtype.ext (h.trans (frobenius_def p z).symm))
  let φ₀ : L₀ →ₐ[F] B :=
    { ψ.comp (e.symm.toRingHom : (frobenius K p).fieldRange →+* K) with
      commutes' := fun a => by
        obtain ⟨b, rfl⟩ := (frobeniusEquiv F p).surjective a
        have hb : algebraMap F L₀ (frobeniusEquiv F p b) =
            ⟨algebraMap F K b ^ p, ⟨algebraMap F K b, by rw [frobenius_def]⟩⟩ := by
          apply Subtype.ext
          show algebraMap F K (frobeniusEquiv F p b) = _
          rw [frobeniusEquiv_def, map_pow]
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe]
        rw [hb]
        show ψ (e.symm _) = _
        rw [he _ (algebraMap F K b) rfl]
        simp [ψ, P, ← Ideal.Quotient.mk_algebraMap, sqZeroFrobeniusLift_mk, frobenius_def] }
  refine ⟨⟨L₀, φ₀⟩, fun z => ⟨⟨z, by rw [frobenius_def]⟩, congrArg ψ (he _ z rfl)⟩, fun y => ?_⟩
  obtain ⟨z, hz⟩ := y.2
  have hy : y = ⟨z ^ p, ⟨z, by rw [frobenius_def]⟩⟩ := Subtype.ext (hz.symm.trans (frobenius_def p z))
  subst hy
  show Ideal.Quotient.mk N (ψ (e.symm _)) = _
  rw [he _ z rfl]
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u z)
  simp [ψ, P, ← hc, sqZeroFrobeniusLift_mk]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem GenericFibreTor.mem_of_smul_mem {σ ι : Type*} (t : σ → ℂ)
    (L : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))) {x : MvPolynomial ι (MvPolynomial σ ℂ)} (hx : x ∈ L)
    {u : MvPolynomial σ ℂ} (hu : eval t u ≠ 0)
    (h : u • x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L) :
    x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L := by
  set J := (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L
  rw [smul_eq_C_mul] at h
  have h1 : C (u - MvPolynomial.C (eval t u)) * x ∈ J :=
    Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])) hx
  have h2 : C (MvPolynomial.C (eval t u)) * x ∈ J := by
    have := J.sub_mem h h1
    rwa [← sub_mul, ← map_sub, sub_sub_cancel] at this
  have hunit : IsUnit (C (MvPolynomial.C (eval t u)) : MvPolynomial ι (MvPolynomial σ ℂ)) :=
    (hu.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ))
  exact (Ideal.unit_mul_mem_iff_mem J hunit).1 h2

theorem GenericFibreTor.proof (hGF : GenericFreeness.Statement.{0, 0, 0}) :
    GenericFibreTor.Statement := by
  classical
  intro σ _ ι _ L
  obtain ⟨F, hF0, hfree⟩ := hGF (MvPolynomial σ ℂ) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
    (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
  refine ⟨F, hF0, fun t ht x hx => ?_⟩
  rw [MvPolynomial.ker_map] at hx ⊢
  obtain ⟨hxL, hxI⟩ := Ideal.mem_inf.1 hx
  rw [MvPolynomial.mem_map_C_iff] at hxI
  have hflat' : Module.Flat (Localization.Away F)
      (LocalizedModule (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)) :=
    @Module.Flat.of_free _ _ _ _ _ hfree
  have hflatS : Module.Flat (MvPolynomial σ ℂ) (Localization.Away F) := IsLocalization.flat _ (Submonoid.powers F)
  have : Module.Flat (MvPolynomial σ ℂ)
      (LocalizedModule (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)) :=
    Module.Flat.trans (MvPolynomial σ ℂ) (Localization.Away F) _
  let g := LocalizedModule.mkLinearMap (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
  let π := (Ideal.Quotient.mkₐ (MvPolynomial σ ℂ) L).toLinearMap
  let a : x.support → MvPolynomial σ ℂ := fun m => AddMonoidAlgebra.coeff x m.1
  let e : x.support → MvPolynomial ι (MvPolynomial σ ℂ) := fun m => monomial m.1 1
  have hsum : ∑ m, a m • e m = x := by
    calc ∑ m, a m • e m = ∑ m : x.support, monomial m.1 (AddMonoidAlgebra.coeff x m.1) :=
          Finset.sum_congr rfl fun m _ => by simp [a, e, smul_monomial]
      _ = x := by
          rw [Finset.sum_coe_sort x.support (fun v => monomial v (AddMonoidAlgebra.coeff x v))]
          exact (MvPolynomial.as_sum x).symm
  have hrel : ∑ m, a m • g (π (e m)) = 0 := by

    simp_rw [← map_smul, ← map_sum, hsum]
    simp [g, π, Ideal.Quotient.eq_zero_iff_mem.2 hxL]
  have htriv : Module.IsTrivialRelation a (fun m => g (π (e m))) :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨k, A, y, hy, hA⟩ := htriv
  obtain ⟨b, hb⟩ := IsLocalizedModule.exist_integer_multiples_of_finite (Submonoid.powers F) g y
  choose q hq using hb
  choose r hr using fun j => Ideal.Quotient.mk_surjective (q j)
  have hm : ∀ m, ∃ c : Submonoid.powers F,
      c • π ((b : MvPolynomial σ ℂ) • e m) = c • π (∑ j, A m j • r j) := by
    intro m
    apply IsLocalizedModule.exists_of_eq (S := Submonoid.powers F) (f := g)

    rw [map_smul, map_smul, show g (π (e m)) = ∑ j, A m j • y j from hy m, Finset.smul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm, ← hq j, ← hr j, map_smul, map_smul]
    rfl
  choose c hc using hm
  set V : MvPolynomial σ ℂ := ∏ m, (c m : MvPolynomial σ ℂ)
  have hD : ∀ m, (V * b) • e m - ∑ j, (V * A m j) • r j ∈ L := by
    intro m
    have h1 := hc m
    rw [← sub_eq_zero, ← smul_sub, ← map_sub, Submonoid.smul_def, ← map_smul] at h1
    have h2 : (c m : MvPolynomial σ ℂ) • ((b : MvPolynomial σ ℂ) • e m - ∑ j, A m j • r j) ∈ L :=
      Ideal.Quotient.eq_zero_iff_mem.1 h1
    have h3 := Submodule.smul_of_tower_mem L (∏ m' ∈ Finset.univ.erase m, (c m' : MvPolynomial σ ℂ)) h2
    convert h3 using 1
    rw [smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ m), smul_sub, smul_smul,
      Finset.smul_sum]
    simp_rw [smul_smul]
    rfl
  have hzero : ∑ m, a m • ∑ j, (V * A m j) • r j = 0 := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul]
    have : ∑ m, a m * (V * A m j) = V * ∑ m, a m * A m j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_; ring
    rw [this, hA j, mul_zero, zero_smul]
  have hkey : (V * b) • x = ∑ m, a m • ((V * b) • e m - ∑ j, (V * A m j) • r j) := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, hzero, sub_zero, ← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_comm]
  have hJ : (V * b) • x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L := by
    rw [hkey]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [smul_eq_C_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hxI m.1)) (hD m)
  have hpow : ∀ u ∈ Submonoid.powers F, eval t u ≠ 0 := by
    rintro u ⟨n, rfl⟩
    rw [map_pow]
    exact pow_ne_zero n ht
  have hVb : V * b ∈ Submonoid.powers F :=
    (Submonoid.powers F).mul_mem (Submonoid.prod_mem _ fun m _ => (c m).2) b.2
  exact GenericFibreTor.mem_of_smul_mem t L hxL (hpow _ hVb) hJ

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology
open scoped ContDiff

noncomputable section

theorem AnalyticSimpleRootBranch.proof : AnalyticSimpleRootBranch.Statement := by
  intro d N a y τ ha hroot hder
  set p : Polynomial ℂ := Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) with hp
  set F : (Fin d → ℂ) × ℂ → ℂ := fun v => v.2 ^ N + ∑ j, a j v.1 * v.2 ^ (j : ℕ) with hF
  have hFa : AnalyticAt ℂ F (y, τ) := by
    refine (analyticAt_snd.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp (analyticAt_fst (p := (y, τ)))).mul (analyticAt_snd.pow _)
  have hcd : ContDiffAt ℂ ω F (y, τ) := hFa.contDiffAt
  have hpe : ∀ s, p.eval s = F (y, s) := by
    intro s
    simp [hp, hF, Polynomial.eval_finsetSum]

  have hpart : fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight (p.derivative.eval τ) := by
    have h1 : HasFDerivAt (fun s : ℂ => F (y, s))
        (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ :=
      (hFa.differentiableAt.hasFDerivAt).comp τ ((hasFDerivAt_const y τ).prodMk (hasFDerivAt_id τ))
    have h2 : (fun s : ℂ => F (y, s)) = fun s => p.eval s := funext fun s => (hpe s).symm
    rw [h2] at h1
    exact h1.unique (p.hasDerivAt τ).hasFDerivAt
  have hinv : (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩
    ext; simp
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set ψ := hcd.implicitFunction hω hinv with hψdef
  have hψy : ψ y = τ := hcd.implicitFunction_apply_self hω hinv
  have hψa : AnalyticAt ℂ ψ y := (hcd.contDiffAt_implicitFunction hω hinv).analyticAt
  have hF0 : F (y, τ) = 0 := hroot
  obtain ⟨U₁, B, hU₁o, hyU₁, hBo, hτB, hsub⟩ :=
    mem_nhds_prod_iff'.mp (hcd.eventually_apply_eq_iff_implicitFunction hω hinv)
  set W : Set (Fin d → ℂ) := U₁ ∩ {x | AnalyticAt ℂ ψ x} with hW
  have hWo : IsOpen W := hU₁o.inter (isOpen_analyticAt ℂ ψ)
  have hWc : ContinuousOn ψ W := fun x hx => hx.2.continuousAt.continuousWithinAt
  refine ⟨W ∩ ψ ⁻¹' B, B, ψ, hWc.isOpen_inter_preimage hWo hBo, ⟨⟨hyU₁, hψa⟩, by simpa [hψy] using hτB⟩,
    hBo, hτB, fun x hx => hx.1.2, hψy, fun y' hy' => ⟨hy'.2, fun s hs => ?_⟩⟩
  have h := hsub (Set.mk_mem_prod hy'.1.1 hs)
  simp only [Set.mem_ofPred_eq] at h
  change F (y', s) = 0 ↔ s = ψ y'
  rw [← hF0, h]
  exact eq_comm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
