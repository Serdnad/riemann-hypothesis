module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter

@[expose] public section

section

noncomputable section

open Matrix
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.NX

namespace Formalism.IndefR.NX

def mulC {q : ℕ} (c : ZMod q) : Multiplicative (ZMod q) →* Multiplicative (ZMod q) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft c)

@[simp] theorem mulC_ofAdd {q : ℕ} (c z : ZMod q) :
    mulC c (Multiplicative.ofAdd z) = Multiplicative.ofAdd (c * z) := rfl

theorem comp_mulC_ne_one {K : Type} [Field K] {q : ℕ} [Fact q.Prime] (θ : Multiplicative (ZMod q) →* Kˣ) (hθ : θ ≠ 1)
    {c : ZMod q} (hc : c ≠ 0) : θ.comp (mulC c) ≠ 1 := by
  intro h
  apply hθ
  refine MonoidHom.ext fun z => ?_
  have e := DFunLike.congr_fun h (Multiplicative.ofAdd (c⁻¹ * Multiplicative.toAdd z))
  simp only [MonoidHom.comp_apply, mulC_ofAdd, MonoidHom.one_apply] at e
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, ofAdd_toAdd] at e
  simpa using e

section Gen

variable {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ)

def thXi {K : Type} [Field K] (ξ : ∀ x, ZMod (p x)) (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) :
    ∀ x, Multiplicative (ZMod (p x)) →* Kˣ :=
  fun x => (θ x).comp (mulC (ξ x))

def psiXi {K : Type} [Field K] (ξ : ∀ x, ZMod (p x)) (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) : Uup p r →* Kˣ :=
  psiStd p r (thXi p ξ θ)

variable {p r}

theorem psiXi_apply {K : Type} [Field K] (ξ : ∀ x, ZMod (p x)) (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ)
    (u : Uup p r) : psiXi p r ξ θ u = ∏ x, θ x (Multiplicative.ofAdd (ξ x *
      supSum r (((u : GProd p r) x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))))) := rfl

theorem psiXi_tvAt [DecidableEq ι] {K : Type} [Field K] (ξ : ∀ x, ZMod (p x))
    (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) (hr : 2 ≤ r) (x : ι) :
    psiXi p r ξ θ ⟨tvAt hr x, tvAt_mem hr x⟩ = θ x (Multiplicative.ofAdd (ξ x)) := by
  have hc : ∀ M : Matrix.SpecialLinearGroup (Fin r) (ZMod (p x)),
      ((Matrix.SpecialLinearGroup.toGL M : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))) = M :=
    fun M => rfl
  rw [psiXi_apply, Finset.prod_eq_single x]
  · simp only [tvAt, Pi.mulSingle_eq_same]
    show θ x (Multiplicative.ofAdd (ξ x * supSum r (tv hr (1 : ZMod (p x))))) = _
    rw [supSum_tv, mul_one]
  · intro y _ hy
    simp [tvAt, Pi.mulSingle_eq_of_ne hy, supSum_one]
  · intro h
    exact absurd (Finset.mem_univ x) h

end Gen

section Rec

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def U (N : NData R H what₂) : Subgroup (G0g N) :=
  Uup (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) R.r

theorem U_eq_Uup (N : NData R H what₂) : U N = Uup (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) R.r := rfl

theorem mem_U {N : NData R H what₂} {u : G0g N} : u ∈ U N ↔
    ∀ kv : (Σ k : Fin 2, N.PlG k), (∀ a b : Fin R.r, b < a →
      ((u kv : GL (Fin R.r) (ZMod (H.g kv.1))) : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g kv.1))) a b = 0) ∧
      ∀ a : Fin R.r, ((u kv : GL (Fin R.r) (ZMod (H.g kv.1))) : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g kv.1))) a a = 1 :=
  Iff.rfl

def psiUOf (N : NData R H what₂) {K : Type} [Field K] (ξ : ∀ kv : (Σ k : Fin 2, N.PlG k), ZMod (H.g kv.1))
    (θ : ∀ k : Fin 2, Multiplicative (ZMod (H.g k)) →* Kˣ) : U N →* Kˣ :=
  psiXi (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) R.r ξ (fun kv => θ kv.1)

theorem psiUOf_apply (N : NData R H what₂) {K : Type} [Field K] (ξ : ∀ kv : (Σ k : Fin 2, N.PlG k), ZMod (H.g kv.1))
    (θ : ∀ k : Fin 2, Multiplicative (ZMod (H.g k)) →* Kˣ) (u : U N) :
    psiUOf N ξ θ u = ∏ kv : (Σ k : Fin 2, N.PlG k), θ kv.1 (Multiplicative.ofAdd (ξ kv *
      supSum R.r (((u : G0g N) kv : GL (Fin R.r) (ZMod (H.g kv.1))) : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g kv.1))))) :=
  rfl

def thSide {K : Type} [Field K] (g : Fin 2 → ℕ) (θ : ∀ k : Fin 2, Multiplicative (ZMod (g k)) →* Kˣ) (b : Bool) :
    ∀ k : Fin 2, Multiplicative (ZMod (g k)) →* Kˣ :=
  fun k => if b then θ k else (θ k)⁻¹

theorem thSide_ne_one {K : Type} [Field K] (g : Fin 2 → ℕ) (θ : ∀ k : Fin 2, Multiplicative (ZMod (g k)) →* Kˣ)
    (b : Bool) (k : Fin 2) (h : θ k ≠ 1) : thSide g θ b k ≠ 1 := by
  cases b <;> simp [thSide, h]

def psiUD (D : D7) (i : D.ntw.Tw) (θ : ∀ k : Fin 2, Multiplicative (ZMod (D.host.g k)) →* (FractionRing (D.ntw.O i))ˣ)
    (b : Bool) : U D.nd →* (FractionRing (D.ntw.O i))ˣ :=
  psiUOf D.nd (xiRed D) (thSide D.host.g θ b)

theorem psiUD_side (D : D7) (i : D.ntw.Tw)
    (θ : ∀ k : Fin 2, Multiplicative (ZMod (D.host.g k)) →* (FractionRing (D.ntw.O i))ˣ) (u : U D.nd) :
    psiUD D i θ false u = (psiUD D i θ true u)⁻¹ := by
  simp only [psiUD, psiUOf_apply, thSide, Bool.false_eq_true, if_false, if_true, MonoidHom.inv_apply,
    Finset.prod_inv_distrib]

def XiRedNZ (D : D7) : Prop := ∀ kv : (Σ k : Fin 2, D.nd.PlG k), xiRed D kv ≠ 0

theorem tied_U_clauses (D : D7)
    (θ : ∀ i, ∀ k : Fin 2, Multiplicative (ZMod (D.host.g k)) →* (FractionRing (D.ntw.O i))ˣ)
    (hξ : 2 ≤ D.R.r → XiRedNZ D) (hθ : 2 ≤ D.R.r → ∀ i k, θ i k ≠ 1)
    (hU : D.nexp.U = U D.nd)
    (hψ : ∀ i b (u : D.nexp.U), D.nexp.psiU i b u = psiUD D i (θ i) b ⟨u.1, by rw [← hU]; exact u.2⟩) :
    D.nexp.U = Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ∧
    (∀ i b, IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r (D.nexp.psiU i b)) ∧
    (∀ i (u : D.nexp.U), D.nexp.psiU i false u = (D.nexp.psiU i true u)⁻¹) ∧
    (∀ i b, ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (FractionRing (D.ntw.O i))ˣ,
      (2 ≤ D.R.r → ∀ kk, θ kk ≠ 1) ∧ ∀ u : D.nexp.U, D.nexp.psiU i b u = ∏ kv : (Σ kk : Fin 2, D.nd.PlG kk),
        θ kv.1 (Multiplicative.ofAdd (xiRed D kv *
          supSum D.R.r (((u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
            Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))))) := by
  refine ⟨hU, fun i b => ?_, fun i u => ?_, fun i b => ?_⟩
  · refine ⟨thXi _ (xiRed D) (fun kv => thSide D.host.g (θ i) b kv.1), fun hr kv => ?_, fun u => ?_⟩
    · have : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
      exact comp_mulC_ne_one _ (thSide_ne_one _ _ b _ (hθ hr i kv.1)) (hξ hr kv)
    · rw [hψ]; rfl
  · rw [hψ, hψ]; exact psiUD_side D i (θ i) _
  · exact ⟨thSide D.host.g (θ i) b, fun hr kk => thSide_ne_one _ _ b _ (hθ hr i kk), fun u => by rw [hψ]; rfl⟩

end Rec

section PerPlace

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

end PerPlace

end Formalism.IndefR.NX
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.NX Formalism.L2.Col
open scoped TensorProduct

namespace Formalism.IndefR.NX

section PsiU

end PsiU

section BC

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {G : Type} [Group G]

def bcRep {W₀ : Type} [AddCommGroup W₀] [Module K W₀] (ρ₀ : Representation K G W₀) :
    Representation K' G (K' ⊗[K] W₀) where
  toFun γ := (ρ₀ γ).baseChange K'
  map_one' := by rw [map_one]; exact LinearMap.baseChange_id
  map_mul' γ δ := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

theorem toMatrix_bcRep {W₀ : Type} [AddCommGroup W₀] [Module K W₀] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W₀) (ρ₀ : Representation K G W₀) (γ : G) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis K' b) (Algebra.TensorProduct.basis K' b) (bcRep (K' := K') ρ₀ γ) =
      (LinearMap.toMatrix b b (ρ₀ γ)).map (algebraMap K K') :=
  LinearMap.toMatrix_baseChange K' (ρ₀ γ) b b

end BC

section AdlK

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

end AdlK

section AlgBC

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] [Algebra K K']

theorem isAlgWeightF_bc {W₀ : Type} [AddCommGroup W₀] [Module K W₀]
    (ρ₀ : Representation K (GQ L n) W₀) (h : IsAlgWeightF L n K ρ₀) : IsAlgWeightF L n K' (bcRep (K' := K') ρ₀) := by
  obtain ⟨hfd, ι, hι, hdec, bs, κ, hκ, eb, P, hP⟩ := h
  have := hfd
  refine ⟨inferInstance, ι, hι, hdec, Algebra.TensorProduct.basis K' bs, κ, hκ, eb,
    fun a a' => MvPolynomial.map (algebraMap K K') (P a a'), fun γ γ₀ hγ => ?_⟩
  rw [toMatrix_bcRep, hP γ γ₀ hγ]
  ext a a'
  simp only [MvPolynomial.eval_map]
  show algebraMap K K' (MvPolynomial.eval₂ (RingHom.id K) _ (P a a')) = _
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext p
  simp [map_ratCast]

end AlgBC

section Real

variable (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
  (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ)
  (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)

abbrev algKk : Algebra (FractionRing (D.ntw.O i)) (Kk D i k) := (toKk D i k).toAlgebra

attribute [local instance] algKk

end Real

section LevGen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

end LevGen

section LevNX

variable (D : D7) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
  (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ)
  (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
  (sp : PlE D.host → SplitPlace D.host.E) (QP DP : Finset (PlE D.host))

end LevNX

section ChrG

theorem supSum_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {r : ℕ} (A : Matrix (Fin r) (Fin r) R) :
    Formalism.L2.NX.supSum r (A.map f) = f (Formalism.L2.NX.supSum r A) := by
  unfold Formalism.L2.NX.supSum

  simp only [map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

section RedGen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

variable {F : Type} [CommRing F]

theorem intLift_of_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (y : v.adicCompletion (maximalRealSubfield L))
    (h : y ∈ v.adicCompletionIntegers (maximalRealSubfield L)) : intLift v y = ⟨y, h⟩ := by
  unfold intLift
  rw [dite_eq_left h]

end RedGen

variable (D : D7) (i : D.ntw.Tw) (b : Bool) (k : ℕ)
  (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
  (sp : PlE D.host → SplitPlace D.host.E)



open Classical in
theorem gVal_of (kv : Σ kk : Fin 2, D.nd.PlG kk) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ' : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (xm : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))
    (G : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) (hrn : D.R.r ≤ D.R.nV)
    (hG : redMat s.v red (topR hrn xm) = G)
    (u : (ZMod (D.host.g kv.1))ˣ) (hu : red (intLift s.v (detT D.R.r xm)) = (u : ZMod (D.host.g kv.1))) :
    gVal D i k b kv s red τ' xm = toKk D i k (psiUTot D i b (Pi.mulSingle kv (glOf G))) *
      toKk D i k ((τ' u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := by
  have hU' : IsUnit (red (intLift s.v (detT D.R.r xm))) := by rw [hu]; exact u.isUnit
  unfold gVal
  show toKk D i k (psiUTot D i b (Pi.mulSingle kv (glOf (redMat s.v red (topR hrn xm))))) *
    (if h : IsUnit (red (intLift s.v (detT D.R.r xm))) then
      toKk D i k ((τ' h.unit : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) else 1) = _
  rw [hG, dite_eq_left hU', show hU'.unit = u from Units.ext (by rw [IsUnit.unit_spec, hu])]

end ChrG

section Tau

variable (D : D7)


end Tau

section Assembly

variable (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
  (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ)
  (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)

attribute [local instance] algKk

end Assembly

section Pq

variable (D : D7)


open Classical in
def qpOf (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : Finset (PlE D.host)) :
    Finset (PlE D.host) :=
  S.filter fun P => ∀ v, NG.OverPl P v → P = Pq v ∨ Pq v ∉ S

theorem qpOf_sub (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : Finset (PlE D.host)) :
    qpOf D Pq S ⊆ S := by
  classical
  intro P hP
  unfold qpOf at hP
  exact (Finset.mem_filter.1 hP).1

theorem qpOf_eq (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : Finset (PlE D.host))
    {P : PlE D.host} (hP : P ∈ qpOf D Pq S) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (hv : NG.OverPl P v) (hS : Pq v ∈ S) : P = Pq v := by
  classical
  unfold qpOf at hP
  exact ((Finset.mem_filter.1 hP).2 v hv).resolve_right (not_not.2 hS)

end Pq

end Formalism.IndefR.NX
end
end
