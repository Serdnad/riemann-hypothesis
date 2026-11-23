module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

namespace GlobalTheory.HWL.Back

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
open scoped Classical

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {W : LocWach PD LL O v n} {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA}
    {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}


theorem tmul_cancel (hO : Function.Injective (algebraMap O LL)) (W : LocWach PD LL O v n)
    (e₀ : ↥W.one.L.T) (h₀ : Submodule.span O {e₀} = ⊤) {r r' : RW}
    (h : (r ⊗ₜ[O] e₀ : TW RW W.one) = r' ⊗ₜ[O] e₀) : r = r' := by
  obtain ⟨e, he, hT⟩ := W.one_line
  have hne : (e₀ : W.one.V) ≠ 0 := by
    intro h0
    have heT : e ∈ W.one.L.T := hT ▸ Submodule.mem_span_singleton_self e
    have : (⟨e, heT⟩ : ↥W.one.L.T) ∈ Submodule.span O {e₀} := h₀ ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp this
    apply he
    have := congrArg Subtype.val ha
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact this.symm
  have hbij : Function.Bijective (LinearMap.toSpanSingleton O ↥W.one.L.T e₀) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      have := congrArg Subtype.val ha
      simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul, Submodule.coe_zero] at this
      rw [← algebraMap_smul LL a, smul_eq_zero] at this
      exact hO (by rw [this.resolve_right hne, map_zero])
    · rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, h₀]
  let ψ := (LinearEquiv.ofBijective _ hbij).symm
  have hψ : ψ e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp
  have := congrArg (fun x => TensorProduct.rid O RW (LinearMap.lTensor RW ψ.toLinearMap x)) h
  simpa [hψ] using this

theorem ioE_φ (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) (a : W.EE) : E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h₀, he, -⟩ := E.one_e
  have h1 := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, he] at h1
  simp only [TWmap, smul_tmul', smul_eq_mul, mul_one, map_tmul, AlgHom.toLinearMap_apply, map_one,
    LinearMap.id_apply] at h1
  exact tmul_cancel hO W e₀ h₀ h1

theorem ioE_γ (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h₀, he, -⟩ := E.one_e
  have h1 := E.jD_act W.one g (a • e)
  have h2 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, he] at h1
  simp only [TWact, smul_tmul', smul_eq_mul, mul_one, map_tmul, AlgHom.toLinearMap_apply, map_one,
    h2] at h1
  exact tmul_cancel hO W e₀ h₀ h1





end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime]


end Concrete

end GlobalTheory.HWL.Back
end
end

section

noncomputable section

namespace GlobalTheory.NL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def conv {M : Type} [AddCommGroup M] [Module LL M] (e : PowerSeries LL) (f : ℤ → M) : ℤ → M :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j e • f (k - j)

def latSpan {M ι : Type} [AddCommGroup M] [Module LL M] (ex : ι → ℤ → M) : Submodule LL (ℤ → M) :=
  Submodule.span LL {f | ∃ (e : PowerSeries LL) (x : ι), f = conv e (ex x)}

def Full {M : Type} [AddCommGroup M] [Module LL M] (D : Submodule LL M) (Λ : Submodule LL (ℤ → M)) : Prop :=
  ∃ m : ℕ, ∀ f : ℤ → M, (∀ k, f k ∈ D) → (∀ k < (m : ℤ), f k = 0) → f ∈ Λ

def Std {M : Type} [AddCommGroup M] [Module LL M] (D : Submodule LL M) (Λ : Submodule LL (ℤ → M)) : Prop :=
  ∀ f : ℤ → M, f ∈ Λ ↔ (∀ k, f k ∈ D) ∧ ∀ k < (0 : ℤ), f k = 0

def Graded {M : Type} [AddCommGroup M] [Module LL M] (Λ : Submodule LL (ℤ → M)) : Prop :=
  ∀ f : ℤ → M, f ∈ Λ ↔ (∃ m : ℤ, ∀ k < m, f k = 0) ∧ ∀ k, Pi.single k (f k) ∈ Λ


variable (PD) in
def FilAt (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (a : ℤ) : Submodule LL (T.V ⊗[Qp] BdR) :=
  FildR PD T.ρ τ a ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ'

def van (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) (k : ℕ) : Ideal (LetA O n) :=
  (Ideal.span {(PowerSeries.X : PowerSeries LL) ^ k}).comap (W.lev i ζ)

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}

abbrev Lt (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

abbrev Let (K : FinExt l) : Type := ZMod (Module.finrank ℚ_[l] ↥(K0 K))

abbrev AA (K LL : FinExt l) : Type := LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))

abbrev Di (H : LocHW l P) (h : Good K s LL) (T : Lt K LL) (i : Let K) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.B) :=
  DcrisL (P.PD K) T.ρ ((H.W K s LL h).emb i)

def ex (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1)
    (x : ↥((H.W K s LL h).N T)) : ℤ → T.V ⊗[ℚ_[l]] P.R.B :=
  (C.C K s LL h).tie.levB T i ζ x

def Lat (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1) :
    Submodule ↥LL.1 (ℤ → T.V ⊗[ℚ_[l]] P.R.B) :=
  latSpan (ex C h T i ζ)

def Pt (H : LocHW l P) (h : Good K s LL) (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : Prop :=
  ∃ τs : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τs ∧
    ∀ (x : ↥K.1) (y : ↥(Ks K s)), (y : Om l) = (x : Om l) → τ x = τs y

def Comp (H : LocHW l P) (h : Good K s LL) (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) : Prop :=
  (∀ c : ↥(K0 K), ι ((H.W K s LL h).emb i c) = algebraMap ↥(K0 K) P.R.BdR c) ∧
    ι ζ = algebraMap (Om l) P.R.BdR (P.ζQ s) ∧ ∀ c : ↥K.1, ι (τ c) = algebraMap ↥K.1 P.R.BdR c

def tS (P : LocPrime l) (s : ℕ) : P.R.BdR := (((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB

end Concrete

end GlobalTheory.NL
end
end
