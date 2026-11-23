module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle176
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
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

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical

noncomputable section

open IsDedekindDomain

namespace GlobalTheory.HeisDerivFormula

variable {F : Type} [Field F] [NumberField F]


variable (F) in
def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b := map_add (evIHom F) a b

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b := map_mul (evIHom F) a b

theorem evI_dot {κ : Type} [Fintype κ] (v w : κ → AF F) :
    evI F (v ⬝ᵥ w) = (fun i => evI F (v i)) ⬝ᵥ fun i => evI F (w i) :=
  RingHom.map_dotProduct (evIHom F) v w

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t := by
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem snd_realAd (t : ℝ) : (realAd F t).2 = 0 := by simp [realAd]


variable (F) in
def ofInf (y : mixedEmbedding.mixedSpace F) : AF F :=
  (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem evI_ofInf (y : mixedEmbedding.mixedSpace F) : evI F (ofInf F y) = y := by
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y

theorem snd_ofInf (y : mixedEmbedding.mixedSpace F) : (ofInf F y).2 = 0 := rfl


variable (F) in
def rInt (κ : Type) (z : κ → AF F) : ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1 (fun i => (z i).2)

theorem rInt_eq_one {κ : Type} (z : κ → AF F) (hz : ∀ i, (z i).2 = 0) : rInt F κ z = 1 := by
  unfold rInt
  rw [Set.indicator_of_mem]
  · rfl
  · intro i _ v
    show (z i).2 v ∈ v.adicCompletionIntegers F
    rw [hz i]
    show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
    exact zero_mem (v.adicCompletionIntegers F)

theorem rest_rInt {κ : Type} [Fintype κ] (g : SInf F κ) :
    Rest (evI F) (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) (rInt F κ) := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨g, _, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ, rfl⟩⟩
  have h2 : ∀ i, (z i).2 = 0 := by
    intro i
    let c : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
    have hc : evI F c = 0 := map_zero _
    have h3 : c * z i = 0 := congrFun (hz c hc) i
    have h4 := congrArg Prod.snd h3
    exact (one_mul _).symm.trans h4
  unfold rInt
  congr 1
  funext i
  show (x i).2 + (z i).2 = (x i).2
  rw [h2 i, add_zero]

theorem schr_line {κ : Type} [Fintype κ] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (g : SInf F κ) (a b : κ → AF F) (y : κ → mixedEmbedding.mixedSpace F) (t : ℝ) :
    GlobalTheory.WeilM.schr ψ (realAd F t • (a, b)) (tens (evI F) (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) (rInt F κ))
      (fun i => ofInf F (y i)) =
    Complex.exp (-(2 * Real.pi * Complex.I) *
      ((t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F (b i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (evI F ⅟(2 : AF F) * ((fun i => evI F (a i)) ⬝ᵥ fun i => evI F (b i))) : ℝ) : ℂ)) *
      g (y + t • fun i => evI F (a i)) := by
  unfold GlobalTheory.WeilM.schr
  simp only [Prod.smul_fst, Prod.smul_snd]
  have hp : (fun i => ofInf F (y i)) ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b)) =
      realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b))) := by
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
  have hAt : At (evI F) (realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b)))) := by
    intro c hc
    have hc1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hc
    have h0 : c * realAd F t = 0 := Prod.ext (by show c.1 * (realAd F t).1 = 0; rw [hc1, zero_mul])
      (by show c.2 * (realAd F t).2 = 0; rw [snd_realAd, mul_zero])
    rw [smul_eq_mul, ← mul_assoc, h0, zero_mul]
  have hy : (fun i => evI F (ofInf F (y i))) = y := funext fun i => evI_ofInf (y i)
  have he : evI F (realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b)))) =
      t • ((y ⬝ᵥ fun i => evI F (b i)) +
        t • (evI F ⅟(2 : AF F) * ((fun i => evI F (a i)) ⬝ᵥ fun i => evI F (b i)))) := by
    rw [evI_mul, evI_add, evI_mul, evI_mul, evI_dot, evI_dot, hy, evI_realAd, Algebra.smul_def, Algebra.smul_def]
    ring
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (evI F (realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b))))) =
      t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F (b i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (evI F ⅟(2 : AF F) * ((fun i => evI F (a i)) ⬝ᵥ fun i => evI F (b i))) := by
    rw [he, map_smul, map_add (f := _), map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hg : (fun i => evI F (((fun i => ofInf F (y i)) + realAd F t • a) i)) = y + t • fun i => evI F (a i) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [evI_add, evI_mul, evI_realAd, evI_ofInf, Algebra.smul_def]
  have hr : rInt F κ ((fun i => ofInf F (y i)) + realAd F t • a) = 1 := by
    refine rInt_eq_one _ fun i => ?_
    show (0 : FiniteAdeleRing (𝓞 F) F) + (realAd F t).2 * (a i).2 = 0
    rw [snd_realAd, zero_mul, add_zero]
  rw [hp, hψ.2.2 _ hAt, htr]
  unfold tens
  rw [hg, hr, mul_one]

theorem heisLine_deriv_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (g h : SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evI F) u →
    ActsD (evI F) (M.heisLine ψ u) g h → ∀ (y : Fin n × Fin d → mixedEmbedding.mixedSpace F),
    h y = fderiv ℝ (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) y (fun i => evI F ((M.co.e u).1 i)) +
      (-(2 * Real.pi * Complex.I) *
        ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F ((M.co.e u).2 i)) : ℝ) : ℂ)) * g y := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ g h u _ hD y
  set A : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i) with hA
  set TY : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F ((M.co.e u).2 i)) with hTY
  set TC : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (evI F ⅟(2 : AF F) * (A ⬝ᵥ fun i => evI F ((M.co.e u).2 i))) with hTC
  have h1 := hD (rInt F _) (rest_rInt g) (fun i => ofInf F (y i))
  have hfun : (fun t => M.heisLine ψ u t (tens (evI F) (g : _ → ℂ) (rInt F _)) (fun i => ofInf F (y i))) =
      fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * TY + t ^ 2 * TC : ℝ) : ℂ)) * g (y + t • A) := by
    funext t
    unfold Model.heisLine GlobalTheory.WeilM.Darboux.rho
    rw [LinearEquiv.map_smul]
    exact schr_line ψ hψ g _ _ y t
  have hval : tens (evI F) (h : _ → ℂ) (rInt F _) (fun i => ofInf F (y i)) = h y := by
    unfold tens
    rw [rInt_eq_one _ fun i => snd_ofInf (y i), mul_one]
    congr 1
    exact funext fun i => evI_ofInf (y i)
  have hL : HasDerivAt (fun t : ℝ => t * TY + t ^ 2 * TC) TY 0 := by
    have h2 := ((hasDerivAt_id' (0 : ℝ)).mul_const TY).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const TC)
    exact h2.congr_deriv (by simp)
  have hE := (hL.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have hl : HasDerivAt (fun t : ℝ => y + t • A) A 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const A).const_add y
  have hG : HasDerivAt (fun t : ℝ => g (y + t • A)) (fderiv ℝ (g : _ → ℂ) y A) 0 :=
    (g.differentiableAt.hasFDerivAt).comp_hasDerivAt_of_eq 0 hl (by simp)
  have hder := hE.mul hG
  rw [hfun] at h1
  have := h1.unique hder
  rw [hval] at this
  rw [this]
  simp
  ring

end GlobalTheory.HeisDerivFormula
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
open GlobalTheory.WeilM

namespace GlobalTheory.ArchLineContPairLeft

theorem continuous_apply : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (f : SInf F (Fin n × Fin d)) (x : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), Continuous fun t => T t f x := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hW γ hγ T hAct f x
  classical
  let κ := Fin n × Fin d
  let g₀ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1
  have hg₀ : g₀ ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  let r₀ : (κ → AF F) → ℂ := fun y => g₀ (fun i => (y i).2)
  have htens : ∀ h : SInf F κ, tens (evI F) (⇑h) r₀ = pureA F (⇑h) g₀ := fun h => rfl
  have hRest : ∀ h : SInf F κ, Rest (evI F) (⇑h) r₀ := by
    intro h
    refine ⟨fun y z hz => ?_, ?_⟩
    · have h2 : ∀ i, (z i).2 = 0 := by
        intro i
        have hu := hz ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) (by
          show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
          exact map_zero _)
        have h1 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd (congrFun hu i)
        rwa [one_mul] at h1
      show g₀ (fun i => (y i + z i).2) = g₀ (fun i => (y i).2)
      congr 1
      funext i
      show (y i).2 + (z i).2 = (y i).2
      rw [h2 i, add_zero]
    · rw [htens]
      exact Submodule.subset_span ⟨h, g₀, hg₀, rfl⟩
  let xh : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), (0 : FiniteAdeleRing (𝓞 F) F))
  let l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj xh
  have hxh : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (xh i).1) = x := by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x i)
  have hg0 : g₀ (fun i => (xh i).2) = 1 := by
    have hm : (fun i => (xh i).2) ∈ GlobalTheory.SchANonzero.intPts F κ := fun i _ v => by
      show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
      exact zero_mem (v.adicCompletionIntegers F)
    simp only [g₀, Set.indicator_of_mem hm, Pi.one_apply]
  have hl : l ∈ (adeleClass F).adm κ := by
    intro g _
    refine ⟨g (fun i => (xh i).2) • ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun h => ?_⟩
    show pureA F (⇑h) g xh = _
    simp only [pureA, hxh, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul]
    exact mul_comm _ _
  have hφ : pureA F (⇑f) g₀ ∈ (adeleClass F).sp κ := Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩
  have hc := hW.2.2 l hl _ hφ
  have key : (fun t : ℝ => T t f x) =
      (fun p => l (om p (pureA F (⇑f) g₀))) ∘ (fun t : ℝ => (γ (Multiplicative.ofAdd t), (1 : UA σ W.J))) := by
    funext t
    have e := hAct t f r₀ (hRest f)
    rw [htens, htens] at e
    simp only [Function.comp_apply]
    rw [e]
    show _ = pureA F _ g₀ xh
    simp only [pureA, hxh, hg0, mul_one]
  rw [key]
  exact hc.comp ((hγ.1.comp continuous_ofAdd).prodMk continuous_const)

end GlobalTheory.ArchLineContPairLeft
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitGen

open IsDedekindDomain.HeightOneSpectrum Polynomial

theorem exists_integral_gen_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl (F := F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∃ (a : 𝓞 E) (b c : 𝓞 F), (a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0 ∧
      σ (a : E) = -algebraMap F E (b : F) - a ∧ c ∈ v.asIdeal ∧ b ∉ v.asIdeal := by
  intro F E _ _ _ _ _ σ B hB v hv
  obtain ⟨P, Q, hPQ, hPv, hQv⟩ := hv
  have hσ := hB.cm
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  haveI : IsGalois ℚ E := hB.galois
  haveI : IsGalois F E := IsGalois.tower_top_of_isGalois ℚ F E
  have hPo : P.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨P.isPrime, ⟨hPv.symm⟩⟩
  have hQo : Q.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨Q.isPrime, ⟨hQv.symm⟩⟩
  obtain ⟨g, hg⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 F) F E (𝓞 E) hPo hQo
  have hgQ : ∀ x : 𝓞 E, x ∈ Q.asIdeal → galRestrict (𝓞 F) F E (𝓞 E) g x ∈ P.asIdeal := by
    intro x hx
    rw [← hg] at hx
    exact hx
  have hgE : ∀ x : 𝓞 E, ((galRestrict (𝓞 F) F E (𝓞 E) g x : 𝓞 E) : E) = g (x : E) :=
    fun x => algebraMap_galRestrict_apply (𝓞 F) g x

  have hne : P.asIdeal ≠ Q.asIdeal := fun h => hPQ (HeightOneSpectrum.ext h)
  have htop := Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal hne
  obtain ⟨a, haP, j, hjQ, haj⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ P.asIdeal ⊔ Q.asIdeal)
  have ha1Q : a - 1 ∈ Q.asIdeal := by
    have : a - 1 = -j := by rw [← haj]; ring
    rw [this]; exact neg_mem hjQ
  have hga1 : galRestrict (𝓞 F) F E (𝓞 E) g a - 1 ∈ P.asIdeal := by
    have := hgQ _ ha1Q
    rwa [map_sub, map_one] at this
  have h1P : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hga : g (a : E) ≠ a := by
    intro h
    apply h1P
    have e : galRestrict (𝓞 F) F E (𝓞 E) g a = a := by
      apply RingOfIntegers.ext
      rw [hgE]; exact h
    have := P.asIdeal.sub_mem haP hga1
    rw [e] at this
    simpa using this
  have hnot : (a : E) ∉ (algebraMap F E).range := by
    rintro ⟨x, hx⟩
    apply hga
    rw [← hx, AlgEquiv.commutes]
  have hi : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hmap : minpoly F (a : E) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hi
  have hdeg : (minpoly F (a : E)).natDegree = (minpoly (𝓞 F) a).natDegree := by
    rw [hmap, (minpoly.monic hi).natDegree_map]
  have hge : 2 ≤ (minpoly (𝓞 F) a).natDegree := by
    rw [← hdeg]
    exact (minpoly.two_le_natDegree_iff (Algebra.IsIntegral.isIntegral _)).2 hnot
  have hle : (minpoly F (a : E)).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le (a : E)
  obtain ⟨b, c, hbc⟩ := isMonicOfDegree_two_iff.1
    (⟨by omega, minpoly.monic hi⟩ : IsMonicOfDegree (minpoly (𝓞 F) a) 2)
  have hq0 : a ^ 2 + algebraMap _ _ b * a + algebraMap _ _ c = 0 := by
    have := minpoly.aeval (𝓞 F) a
    rw [hbc] at this
    simpa using this
  have hq : (a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0 := by
    have := congrArg (algebraMap (𝓞 E) E) hq0
    simp only [map_add (f := _), map_mul, map_pow, map_zero] at this
    exact this
  have hli : LinearIndependent F ![(1 : E), a] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro x hx
    exact hnot ⟨x, by rw [Algebra.algebraMap_eq_smul_one, hx]⟩
  let Bs := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hBs : ⇑Bs = ![(1 : E), a] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hσa : σ (a : E) ≠ a := by
    intro hfix
    obtain ⟨x, hx⟩ := GlobalTheory.InertUnitNorm.exists_ne_of_isCMExt σ hσ
    apply hx
    have : σ.toLinearMap = LinearMap.id := by
      refine Bs.ext fun i => ?_
      fin_cases i
      · simp [hBs]
      · simp [hBs, hfix]
    exact congrArg (fun f : E →ₗ[F] E => f x) this
  have hqσ : σ (a : E) ^ 2 + algebraMap F E (b : F) * σ a + algebraMap F E (c : F) = 0 := by
    have := congrArg σ hq
    simpa only [map_add (f := _), map_mul, map_pow, AlgHom.commutes, map_zero] using this
  have hconj : σ (a : E) = -algebraMap F E (b : F) - a := by
    have hm : (σ (a : E) - a) * (σ a + a + algebraMap F E (b : F)) = 0 := by
      linear_combination hqσ - hq
    rcases mul_eq_zero.1 hm with h | h
    · exact absurd (sub_eq_zero.1 h) hσa
    · linear_combination h
  have hqg : g (a : E) ^ 2 + algebraMap F E (b : F) * g a + algebraMap F E (c : F) = 0 := by
    have := congrArg g hq
    simpa only [map_add (f := _), map_mul, map_pow, AlgEquiv.commutes, map_zero] using this
  have hgconj : g (a : E) = -algebraMap F E (b : F) - a := by
    have hm : (g (a : E) - a) * (g a + a + algebraMap F E (b : F)) = 0 := by
      linear_combination hqg - hq
    rcases mul_eq_zero.1 hm with h | h
    · exact absurd (sub_eq_zero.1 h) hga
    · linear_combination h
  have hgO : galRestrict (𝓞 F) F E (𝓞 E) g a = -algebraMap (𝓞 F) (𝓞 E) b - a := by
    apply RingOfIntegers.ext
    rw [hgE, hgconj]
    simp only [map_sub, map_neg]
    rfl
  refine ⟨a, b, c, hq, hconj, ?_, ?_⟩
  ·
    rw [← hPv, Ideal.mem_comap]
    have e : algebraMap (𝓞 F) (𝓞 E) c = a * (-algebraMap (𝓞 F) (𝓞 E) b - a) := by
      linear_combination hq0
    rw [e]
    exact P.asIdeal.mul_mem_right _ haP
  · intro hb
    rw [← hPv, Ideal.mem_comap] at hb
    apply h1P
    rw [hgO] at hga1
    have e : (1 : 𝓞 E) = -(-algebraMap (𝓞 F) (𝓞 E) b - a - 1) - algebraMap (𝓞 F) (𝓞 E) b - a := by ring
    rw [e]
    exact P.asIdeal.sub_mem (P.asIdeal.sub_mem (neg_mem hga1) hb) haP

end GlobalTheory.SplitGen
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_admissible_lift_splitPlaceConjugatePair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (∀ i j, σ (W.J j i) = -W.J i j) →
  ∀ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z, π₁ (cA σ z) = π₂ z) → (∀ z, π₂ (cA σ z) = π₁ z) → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  S.map (fun x => (x : Fv F v)) = (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∀ X₁ X₂ : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), X₁ᵀ * S + S * X₂ = 0 →
  ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
    Y.map π₁ = (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) * X₁.map (fun x => (x : Fv F v)) * ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) ∧
    Y.map π₂ = (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) * X₂.map (fun x => (x : Fv F v)) * ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) ∧
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 := by
  first | exact @GlobalTheory.AdmLift.exists_admissible_lift | exact GlobalTheory.AdmLift.exists_admissible_lift | (intros; apply GlobalTheory.AdmLift.exists_admissible_lift <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_cmSkew_element_unit_at_finitePlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v),
    (∀ a : AF F, π (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) →
    ∃ δ : E, σ δ = -δ ∧ ∃ u : (v.adicCompletionIntegers F)ˣ,
      ((u : v.adicCompletionIntegers F) : Fv F v) = π (inclR (F := F) (AF F) δ) := by
  first | exact @GlobalTheory.CMSkewUnit.exists_skew_unit_at | exact GlobalTheory.CMSkewUnit.exists_skew_unit_at | (intros; apply GlobalTheory.CMSkewUnit.exists_skew_unit_at <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.exists_schwartz_archimedeanSlice_adelicSchwartz : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, ∃ g : SInf F κ, ∀ t : κ → mixedEmbedding.mixedSpace F,
    g t = Φ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)) := by
  first | exact @GlobalTheory.ArchSlice.exists_schwartz_slice | exact GlobalTheory.ArchSlice.exists_schwartz_slice | (intros; apply GlobalTheory.ArchSlice.exists_schwartz_slice <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.halfBlockSum_exists_inverse_integral_splitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b : GL (Fin d) (Fv F v)),
  (∀ a : AF F, π (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) →
  ∀ (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F)),
  G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) →
  ∀ X : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  IsUnit (G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂ +
    X * (G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂)).det →
  ∀ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), Y.map π = (b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) * ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∃ N : Matrix (Fin d) (Fin d) (Fv F v), N * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))).map π = 1 ∧ (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * N * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  first | exact @GlobalTheory.Twist.halfBlockSum_inv_conj_integral | exact GlobalTheory.Twist.halfBlockSum_inv_conj_integral | (intros; apply GlobalTheory.Twist.halfBlockSum_inv_conj_integral <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.heisenbergDerivative_zero_or_empty_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (g h : SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ActsD (evI F) (M.heisLine ψ u) g h → (g = 0 ∨ IsEmpty (Fin n × Fin d)) → h = 0 := by
  first | exact @GlobalTheory.HeisDerivZero.actsD_eq_zero | exact GlobalTheory.HeisDerivZero.actsD_eq_zero | (intros; apply GlobalTheory.HeisDerivZero.actsD_eq_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.exists_finiteWeight_complementary_archimedeanSchwartz : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ f : SInf F κ, Rest (evI F) (⇑f) R := by
  first | exact @GlobalTheory.ArchRest.exists_rest_arch | exact GlobalTheory.ArchRest.exists_rest_arch | (intros; apply GlobalTheory.ArchRest.exists_rest_arch <;> assumption)
end
