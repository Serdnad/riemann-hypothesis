module

public import Formalism.HarderNarasimhan.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle220
public import Formalism.SatakeDualWeyl.StatementG
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle295
public import Formalism.UnipotentAdelicQuotients.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialZeroLocusCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField

namespace GlobalTheory.IntFormsRank

variable {LL : Type} [Field LL] [NumberField LL] {n : ℕ}

theorem smul_eq_algebraMap_smul (r : 𝓞 LL) (z : Fin n → LL) : r • z = (algebraMap (𝓞 LL) LL r) • z :=
  (algebraMap_smul LL r z).symm

theorem exists_den_smul_mem (T : Set (Fin n → LL)) (x : Fin n → LL) (hx : x ∈ Submodule.span LL T) :
    ∃ d : 𝓞 LL, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 LL) T := by
  first
  | exact @_root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span
  | exact _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span
  | (apply _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span ..)

theorem span_inf_eq (T : Set (Fin n → LL)) (hT : Submodule.span LL T = ⊤) (S : Submodule LL (Fin n → LL)) :
    Submodule.span LL ((Submodule.span (𝓞 LL) T ⊓ S.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) (Fin n → LL)) :
      Set (Fin n → LL)) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro x hx
    have hxT : x ∈ Submodule.span LL T := by rw [hT]; exact Submodule.mem_top
    obtain ⟨d, hd, hdx⟩ := exists_den_smul_mem T x hxT
    have hdL : algebraMap (𝓞 LL) LL d ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 LL) LL)]; exact hd
    have hmem : d • x ∈ (Submodule.span (𝓞 LL) T ⊓ S.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) (Fin n → LL)) := by
      refine ⟨hdx, ?_⟩
      show d • x ∈ S
      rw [smul_eq_algebraMap_smul]; exact S.smul_mem _ hx
    have hx' : x = (algebraMap (𝓞 LL) LL d)⁻¹ • (d • x) := by
      rw [smul_eq_algebraMap_smul, smul_smul, inv_mul_cancel₀ hdL, one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.IntFormsRank

theorem GlobalTheory.IntFormsRank.rkK_Mall : ∀ (LL Ks : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] (n : ℕ)
    (Wσ : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    (G0 : Type) [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) (f : (Fin n → LL) →ₗ[LL] (Fin n → LL)),
    Submodule.span LL (A.MK : Set (Fin n → LL)) = ⊤ →
    Formalism.HN.rkK (A.Mall J0 lam0) = Module.finrank LL (A.typeP J0 lam0) ∧
    Formalism.HN.rkK (A.Mall J0 lam0 ⊓ (LinearMap.ker f).restrictScalars (𝓞 LL)) =
      Module.finrank LL (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)) := by
  intro LL Ks _ _ _ _ _ n Wσ _ _ G0 _ _ A J0 lam0 f hsp
  constructor
  · unfold Formalism.HN.rkK Formalism.IndefR.Arith.FormsL.Mall
    rw [GlobalTheory.IntFormsRank.span_inf_eq _ hsp]
  · unfold Formalism.HN.rkK Formalism.IndefR.Arith.FormsL.Mall
    have e : (Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL)) ⊓ (A.typeP J0 lam0).restrictScalars (𝓞 LL) ⊓
        (LinearMap.ker f).restrictScalars (𝓞 LL)) =
        Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL)) ⊓
          (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)).restrictScalars (𝓞 LL) := by
      rw [inf_assoc]; rfl
    rw [e, GlobalTheory.IntFormsRank.span_inf_eq _ hsp]
end

section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory

namespace GlobalTheory.WeilPartsF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def GfCF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (GAF σ J) :=
  ((Formalism.UG.bc (infPartF F E)).comp (matHomF σ J)).ker

def GinfCF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (GAF σ J) :=
  ((Formalism.UG.bc (finPartF F E)).comp (matHomF σ J)).ker

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)

structure IsUnitaryOnThetaF (xi0 : E) (ψ : AddChar (AF F) ℂ)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop where
  pres : ∀ p f, IsThetaFunOF σ JS JT xi0 ψ f → IsThetaFunOF σ JS JT xi0 ψ (om p f)
  cont : ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → ∀ w, Continuous fun p : GAF σ JS × GAF σ JT => om p f w
  unit : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f, IsThetaFunOF σ JS JT xi0 ψ f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

structure IsFinWeilF (xi0 : E) (ψ : AddChar (AF F) ℂ) (χS χT : (AEF F E)ˣ →* Circle)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop
    extends IsUnitaryOnThetaF σ JS JT xi0 ψ om where
  triv : ∀ g ∈ GinfCF σ JS, ∀ h ∈ GinfCF σ JT, ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GfCF σ JS, ∀ h ∈ GfCF σ JT, ∀ w₀ f, IsThetaFunOF σ JS JT xi0 ψ f →
    om (g, h) (heisOF σ JS JT xi0 ψ w₀ f) = heisOF σ JS JT xi0 ψ (actOF σ JS JT g h w₀) (om (g, h) f)
  split : ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h → ∀ x y,
    IsDetAtF σ e JS g x → IsDetAtF σ e JT h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT xi0 ψ f →
        ℓ (heisOF σ JS JT xi0 ψ u f) = ℓ f) →
      ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → ℓ (om (g, h) f) = (r : ℂ) * (splitFacOF χS χT x y : ℂ) * ℓ f

structure IsInfWeilF (xi0 : E) (ψ : AddChar (AF F) ℂ)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop
    extends IsUnitaryOnThetaF σ JS JT xi0 ψ om where
  triv : ∀ g ∈ GfCF σ JS, ∀ h ∈ GfCF σ JT, ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GinfCF σ JS, ∀ h ∈ GinfCF σ JT, ∀ w₀ f, IsThetaFunOF σ JS JT xi0 ψ f →
    om (g, h) (heisOF σ JS JT xi0 ψ w₀ f) = heisOF σ JS JT xi0 ψ (actOF σ JS JT g h w₀) (om (g, h) f)

section Lemmas

variable {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E} {ψ : AddChar (AF F) ℂ}

theorem heisOF_add (w : WOF F E nS nT) (f g : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ w (f + g) = heisOF σ JS JT xi0 ψ w f + heisOF σ JS JT xi0 ψ w g := by
  funext x
  simp only [heisOF, Pi.add_apply, mul_add]

theorem heisOF_smul (c : ℂ) (w : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ w (c • f) = c • heisOF σ JS JT xi0 ψ w f := by
  funext x
  simp only [heisOF, Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_add {f g : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT xi0 ψ f) (hg : IsThetaFunOF σ JS JT xi0 ψ g) :
    IsThetaFunOF σ JS JT xi0 ψ (f + g) := {
  quasi γ w := by
    simp only [Pi.add_apply]
    rw [hf.quasi, hg.quasi, mul_add]
  level := by
    obtain ⟨U, hU, hU'⟩ := hf.level
    obtain ⟨V, hV, hV'⟩ := hg.level
    exact ⟨U ⊓ V, hU.inter hV, fun u hu h0 => by rw [heisOF_add, hU' u hu.1 h0, hV' u hu.2 h0]⟩
  cont := hf.cont.add hg.cont
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).add (hg.smooth k L hL h0 w) }

theorem theta_zero : IsThetaFunOF σ JS JT xi0 ψ (0 : WOF F E nS nT → ℂ) := {
  quasi γ w := by simp
  level := ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext x; simp [heisOF]⟩
  cont := continuous_const
  smooth k L hL h0 w := contDiff_const }

theorem theta_smul (c : ℂ) {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT xi0 ψ f) :
    IsThetaFunOF σ JS JT xi0 ψ (c • f) := {
  quasi γ w := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi]
    ring
  level := by
    obtain ⟨U, hU, hU'⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisOF_smul, hU' u hu h0]⟩
  cont := hf.cont.const_smul c
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).const_smul c }


variable (σ JS JT xi0 ψ) in
def thetaSubF : Submodule ℂ (WOF F E nS nT → ℂ) where
  carrier := {f | IsThetaFunOF σ JS JT xi0 ψ f}
  add_mem' := theta_add
  zero_mem' := theta_zero
  smul_mem' := fun a _ hf => theta_smul a hf

theorem mtF_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g g' : GAF σ J) : mtF σ J (g * g') = mtF σ J g * mtF σ J g' := by
  unfold mtF
  rw [map_mul]
  rfl

theorem actOF_mul (g g' : GAF σ JS) (h h' : GAF σ JT) (u : WOF F E nS nT) :
    actOF σ JS JT (g * g') (h * h') u = actOF σ JS JT g h (actOF σ JS JT g' h' u) := by
  unfold actOF
  rw [_root_.mul_inv_rev, mtF_mul, mtF_mul]
  simp only [Matrix.mul_assoc]

theorem mem_GfCF_of_supp {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {a : AEF F E} (ha : infPartF F E a = 0) {g : GAF σ J}
    (hg : ∀ i j, a * (mtF σ J g - 1) i j = (mtF σ J g - 1) i j) : g ∈ GfCF σ J := by
  rw [GfCF, MonoidHom.mem_ker, MonoidHom.comp_apply]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPartF F E ((mtF σ J g - 1) i j) = 0 := by rw [← hg i j, map_mul, ha, zero_mul]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
  show infPartF F E (mtF σ J g i j) = ((1 : GL (Fin n) (Ainf F ⊗[F] E)) : Matrix _ _ _) i j
  rw [h, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]

theorem infPartF_placeIdem {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdemF F v ε) :
    infPartF F E (algebraMap (AF F) (AEF F E) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 0 α ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 0 α) = 0 from rfl, TensorProduct.zero_tmul]

theorem mem_GfCF_of_suppAt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} (he : IsSplitIdemF σ e) {g : GAF σ J}
    (hg : SuppAtF σ e J g) : g ∈ GfCF σ J := by
  obtain ⟨-, -, v, ε, h1, h2⟩ := he
  exact mem_GfCF_of_supp (h2 ▸ infPartF_placeIdem h1) hg

theorem isHeckeCharF_pow {η : (AEF F E)ˣ →* Circle} (h : IsHeckeCharF η) (n : ℕ) : IsHeckeCharF (η ^ n) :=
  ⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩

theorem resEtaF_pow {η : (AEF F E)ˣ →* Circle} (h : ResEtaF η 1) (n : ℕ) : ResEtaF (η ^ n) n :=
  ⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩

theorem exists_extend {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (Om : Γ →* Module.End ℂ M) : ∃ om : Γ →* Module.End ℂ V, ∀ p (m : M), om p m = Om p m := by
  obtain ⟨C, hC⟩ := M.exists_isCompl
  let e := M.prodEquivOfIsCompl C hC
  refine ⟨{ toFun := fun p => e.conj ((Om p).prodMap LinearMap.id), map_one' := ?_, map_mul' := fun p q => ?_ }, ?_⟩
  · rw [map_one]
    exact (congrArg e.conj LinearMap.prodMap_id).trans e.conj_id
  · rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← e.conj_comp, LinearMap.prodMap_comp,
      LinearMap.id_comp]
  · intro p m
    show e (((Om p).prodMap LinearMap.id) (e.symm m)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp [e]

end Lemmas

end GlobalTheory.WeilPartsF

end
end

section

open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.DblTargetDelta

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}

def topR (x : WOF F E nS (nT + nT)) : WOF F E nS nT := x.submatrix (finSumFinEquiv ∘ Sum.inl) id

def botR (x : WOF F E nS (nT + nT)) : WOF F E nS nT := x.submatrix (finSumFinEquiv ∘ Sum.inr) id

def deltaT (f₁ f₂ : WOF F E nS nT → ℂ) : WOF F E nS (nT + nT) → ℂ :=
  fun x => f₁ (topR x) * conj (f₂ (-botR x))

theorem deltaT_apply (f₁ f₂ : WOF F E nS nT → ℂ) (x : WOF F E nS (nT + nT)) :
    deltaT f₁ f₂ x = f₁ (topR x) * conj (f₂ (-botR x)) := rfl

end GlobalTheory.DblTargetDelta

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.LagrTheta

def lagrInt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m nS nT : ℕ}
    (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)) (C : Matrix (Fin m) (Fin nT) (AF F ⊗[F] E))
    (f : Matrix (Fin m) (Fin nS) (AF F ⊗[F] E) → ℂ) : ℂ :=
  ∫ u in 𝓕, f (C * u) ∂ν

end GlobalTheory.LagrTheta

end
end

section

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.HeckeSplitGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def intAEF : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a : Af F, (∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

def splitLocF (σ : E →ₐ[F] E) : Set (AEF F E)ˣ :=
  {x | ∃ e, IsSplitIdemF σ e ∧ (e + cAF σ e) * ((x : AEF F E) - 1) = (x : AEF F E) - 1}


variable (F E) in
def modSetF (N : ℕ) : Set (AEF F E)ˣ :=
  {x | infPartF F E (x : AEF F E) = 1 ∧
    (∃ r ∈ intAEF F E, finPartF F E (x : AEF F E) - 1 = (N : Af F ⊗[F] E) * r) ∧
    finPartF F E ((x⁻¹ : (AEF F E)ˣ) : AEF F E) ∈ intAEF F E}

def grpHF (σ : E →ₐ[F] E) (N : ℕ) : Subgroup (AEF F E)ˣ :=
  Subgroup.closure (Set.range (Units.map (incAF F E).toMonoidHom) ∪ splitLocF σ ∪ modSetF F E N)

end GlobalTheory.HeckeSplitGen

end
end

section

open NumberField

namespace GlobalTheory
open Formalism.IndefR.Arith

theorem mall_eq_span_rat (LL Ks WL G0 : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (hK : A.IsKsForm) (hρ : ∀ u : J0, ∀ f ∈ A.WK, A.ρ u f ∈ A.WK) (hc : ∀ u : J0, ((A.chi u * lam0 u : LLˣ) : LL) ∈ Set.range (algebraMap Ks LL)) : A.Mall J0 lam0 = Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.typeP J0 lam0} := by
  apply le_antisymm
  swap
  · rw [Submodule.span_le]
    rintro y ⟨hy1, hy2⟩
    exact ⟨Submodule.subset_span hy1, hy2⟩
  obtain ⟨n, b, hbK, _, hspK, hliL, hspL⟩ := hK

  set ψ : (Fin n → LL) →ₗ[LL] WL := Fintype.linearCombination LL b with hψdef
  have hψ : ∀ y, ψ y = ∑ k, y k • b k := fun y => by simp [hψdef, Fintype.linearCombination_apply]
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [hψ] at hy
    funext i
    exact Fintype.linearIndependent_iff.1 hliL y hy i
  set e : (Fin n → Ks) → (Fin n → LL) := fun x i => algebraMap Ks LL (x i) with he
  have hψe : ∀ x, ψ (e x) = ∑ k, x k • b k := fun x => by
    rw [hψ]; simp [he, algebraMap_smul]

  have hex : ∀ (p : J0) (k : Fin n), ∃ c : Fin n → Ks, ∑ i, c i • b i = A.ρ p (b k) := by
    intro p k
    have : A.ρ p (b k) ∈ Submodule.span Ks (Set.range b) := by rw [hspK]; exact hρ p _ (hbK k)
    exact (Submodule.mem_span_range_iff_exists_fun Ks).1 this
  choose cc hcc using hex
  let Am : J0 → Matrix (Fin n) (Fin n) Ks := fun p => Matrix.of fun i k => cc p k i
  choose lamK hlamK using hc
  have hρψ : ∀ (p : J0) y, A.ρ p (ψ y) = ψ (((Am p).map (algebraMap Ks LL)).mulVec y) := by
    intro p y

    rw [hψ, hψ, map_sum]
    simp only [LinearMap.map_smul, ← hcc, Finset.smul_sum, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Am, Finset.sum_smul, mul_smul, algebraMap_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    exact smul_comm _ _ _
  have hmemT : ∀ y, ψ y ∈ A.typeP J0 lam0 ↔ ∀ p : J0, ((Am p).map (algebraMap Ks LL)).mulVec y = algebraMap Ks LL (lamK p) • y := by
    intro y
    rw [FormsL.mem_typeP]
    refine forall_congr' fun p => ?_
    rw [hρψ, hlamK p, ← LinearMap.map_smul]
    exact hψinj.eq_iff
  let Wt : Submodule Ks (Fin n → Ks) :=
    { carrier := {x | ∀ p, (Am p).mulVec x = lamK p • x}
      zero_mem' := fun p => by simp
      add_mem' := fun {x y} hx hy p => by simp [Matrix.mulVec_add, hx p, hy p, smul_add]
      smul_mem' := fun a x hx p => by
        show (Am p).mulVec (a • x) = lamK p • (a • x)
        rw [Matrix.mulVec_smul, hx p, smul_smul, smul_smul, mul_comm] }
  let φ : (Fin n → Ks) →ₗ[𝓞 Ks] WL := (Fintype.linearCombination Ks b).restrictScalars (𝓞 Ks)
  let M : Submodule (𝓞 Ks) (Fin n → Ks) := A.MK.comap φ
  have hMmem : ∀ x, x ∈ M ↔ ∑ k, x k • b k ∈ A.MK := fun x => by simp [M, φ, Fintype.linearCombination_apply]
  have hI1 := (GlobalTheory.T.rational_matrix_eigenspace_image_spanned_rational Ks LL n J0 Am lamK 0).1
  have hI2 := GlobalTheory.T.lattice_span_inf_rational_subspace_integers_ext Ks LL n M Wt
  let ψO : (Fin n → LL) →ₗ[𝓞 LL] WL := ψ.restrictScalars (𝓞 LL)
  rintro y ⟨hy1, hy2⟩
  have hle : Submodule.span (𝓞 LL) (A.MK : Set WL) ≤ (Submodule.span (𝓞 LL) (e '' (M : Set _))).map ψO := by
    rw [Submodule.span_le]
    intro m hm
    have hmK : m ∈ Submodule.span Ks (Set.range b) := by rw [hspK]; exact A.MK_le_WK hm
    obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun Ks).1 hmK
    refine ⟨e x, Submodule.subset_span ⟨x, (hMmem x).2 (hx ▸ hm), rfl⟩, ?_⟩
    show ψ (e x) = m
    rw [hψe, hx]
  obtain ⟨z, hz, rfl⟩ := hle hy1
  have hzW : z ∈ Submodule.span LL (e '' (Wt : Set _)) := (hI1 z).1 ((hmemT z).1 hy2)
  have hz2 : z ∈ Submodule.span (𝓞 LL) (e '' ((M ⊓ Wt.restrictScalars (𝓞 Ks) : Submodule (𝓞 Ks) _) : Set _)) := by
    rw [← hI2]; exact ⟨hz, hzW⟩
  have hle2 : Submodule.span (𝓞 LL) (e '' ((M ⊓ Wt.restrictScalars (𝓞 Ks) : Submodule (𝓞 Ks) _) : Set _)) ≤ (Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.typeP J0 lam0}).comap ψO := by
    rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxM, hxW⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨?_, ?_⟩
    · show ψ (e x) ∈ A.MK
      rw [hψe]; exact (hMmem x).1 hxM
    · show ψ (e x) ∈ A.typeP J0 lam0
      rw [hmemT]; exact (hI1 (e x)).2 (Submodule.subset_span ⟨x, hxW, rfl⟩)
  exact hle2 hz2

end GlobalTheory
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_baseField_generator_localDifferent_inertPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∃ t : F, t ≠ 0 ∧ ∃ s₁ s₂ : E, w.valuation E s₁ = 1 ∧ w.valuation E s₂ = 1 ∧
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) := by
  first | exact @GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt | exact GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt | (intros; apply GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt <;> assumption)
end

section

open GlobalTheory.LKTrip
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_polynomialLocus_similitudeCentralizerTorus : ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D),
  ∃ (N : ℕ) (S : Set (MvPolynomial (Fin N × Fin N) ℚ)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S)
    (φ : ∀ (R : Type) [CommRing R] [Algebra ℚ R], HeckeCharacterZeroLocus.locusSubgroup S hS R →* (R ⊗[ℚ] D)ˣ × Rˣ),
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], Function.Injective (φ R) ∧
      ∀ z : (R ⊗[ℚ] D)ˣ × Rˣ, GlobalTheory.TorCls.TC D σ β y R z ↔ z ∈ Set.range (φ R)) ∧
    (∀ (R R' : Type) [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
      (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) (g' : HeckeCharacterZeroLocus.locusSubgroup S hS R'),
      (g' : GL (Fin N) R') = Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom (g : GL (Fin N) R) →
      φ R' g' = (Units.map (Algebra.TensorProduct.map f (AlgHom.id ℚ D)).toRingHom.toMonoidHom (φ R g).1,
        Units.map f.toRingHom.toMonoidHom (φ R g).2)) ∧
    (∀ (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R],
      letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
      Continuous (φ R)) := by
  first | (exact @GlobalTheory.TorLoc.exists_locus) | (exact GlobalTheory.TorLoc.exists_locus) | (intros; apply GlobalTheory.TorLoc.exists_locus  <;> assumption)
end
