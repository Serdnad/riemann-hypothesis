module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def HasSig (W : HSpace E) (P Q : ℕ) : Prop := W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def withLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : HSpace E :=
  { W with L0 := L, standardTuple_isLattice := hL, baseLattice_isUnimodular := hU }

def frameMat (W₁ W₂ : HSpace E) (e : W₁.V →ₗ[E] W₂.V) : Matrix (Fin W₂.rank) (Fin W₁.rank) E :=
  LinearMap.toMatrix W₁.frame W₂.frame e

def CarriesLat (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop := ∀ x : W₁.V, x ∈ W₁.L0 ↔ e x ∈ W₂.L0

end Spaces

def IsConjBy {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M₁ M₂ : ℕ}
    (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E) (T : Matrix (Fin M₂) (Fin M₁) E)
    (φ : HA (AF F) σ J₁ → HA (AF F) σ J₂) : Prop :=
  ∀ h : HA (AF F) σ J₁,
    ((HA.mat (AF F) σ J₂ (φ h) : GL (Fin M₂) (AF F ⊗[F] E)) : Matrix (Fin M₂) (Fin M₂) (AF F ⊗[F] E)) *
        T.map (inclR (F := F) (AF F)) =
      T.map (inclR (F := F) (AF F)) *
        ((HA.mat (AF F) σ J₁ h : GL (Fin M₁) (AF F ⊗[F] E)) : Matrix (Fin M₁) (Fin M₁) (AF F ⊗[F] E))

def LatticeIndep (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), HasSig W P Q →
    ∀ (L : Submodule (𝓞 D.host.E) W.V) (hL : Submodule.IsLattice D.host.E L)
      (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)),
      IsVolMeas D W P Q μ ↔ IsVolMeas D (withLat W L hL hU) P Q μ

def IsometryTransport (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSig W₁ P Q → HasSig W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, HSpace.IsIsomEmb W₁ W₂ e.toLinearMap → CarriesLat W₁ W₂ e →
      ∃ φ : HA (AF D.host.F) D.sp.cm.sig W₁.gram ≃ₜ* HA (AF D.host.F) D.sp.cm.sig W₂.gram,
        IsConjBy D.sp.cm.sig W₁.gram W₂.gram (frameMat W₁ W₂ e.toLinearMap) φ ∧
        (∀ h, h ∈ HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram ↔
          φ h ∈ HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) ∧
        (∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
          IsVolMeas D W₁ P Q μ ↔ IsVolMeas D W₂ P Q (μ.map φ)) ∧
        (∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram))
            (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W₁.gram)),
          IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram) 𝓕 μ ↔
            IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) (φ '' 𝓕) (μ.map φ))

def VolEqOfIsometric (D : D7) : Prop :=
  letI := D.host.cmStar
  VolTie D → ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSig W₁ P Q → HasSig W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, HSpace.IsIsomEmb W₁ W₂ e.toLinearMap → D.vol W₁ = D.vol W₂

def VolIndep (D : D7) : Prop := LatticeIndep D ∧ IsometryTransport D ∧ VolEqOfIsometric D

end GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding

open NumberField MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal TensorProduct

abbrev RCosets {G G' : Type} [Group G] [Group G'] (j : G' →* G) : Type :=
  Quotient (QuotientGroup.rightRel j.range)

def IsQuotMeasure {G G' : Type} [Group G] [Group G'] [MeasurableSpace G] [MeasurableSpace G']
    (j : G' →* G) (μ : Measure G) (μ' : Measure G') (ν : Measure (RCosets j)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f →
    ∫⁻ g, f g ∂μ = ∫⁻ c : RCosets j, ∫⁻ h, f (j h * c.out) ∂μ' ∂ν

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def coords (W : HSpace E) (x : W.V) : Fin 1 → Fin W.rank → E := fun _ i => W.frame.repr x i

end Coord

def latTensor {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ℝ≥0∞ :=
  (latHat F E L : Set (Fin M → Af F ⊗[F] E)).indicator (fun _ => (1 : ℝ≥0∞)) (projFin X 0) *
    Φi (projInf X)

def atInv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
    (h : HA (AF F) σ J) (y : Fin 1 → Fin M → E) : ℝ≥0∞ :=
  Φ (h⁻¹ • ratTup (F := F) (AF F) y)

def IsInfQuotIntegral (D : D7) : letI := D.host.cmStar; ∀ (W : HSpace D.host.E) (_P _Q _P' _Q' : ℕ)
    (_x : W.V) (_Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞)
    (_I : ℝ≥0∞), Prop :=
  letI := D.host.cmStar
  fun W P Q P' Q' x Φi I =>
  AllSome (fun θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) =>
    ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) fun θ =>
  AllSome (fun A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ =>
    ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) fun A =>
  let xr : D.what₂.Tau → (Fin P ⊕ Fin Q → ℂ) :=
    fun ρ => A ρ *ᵥ fun i => embOf D ρ (coords W x 0 i)
  AllSome (fun C : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ =>
    ∀ ρ, (C ρ)ᴴ * Formalism.UG.Jpq P Q * C ρ = Formalism.UG.Jpq P' Q' ∧
      ((C ρ)ᴴ * Formalism.UG.Jpq P Q) *ᵥ xr ρ = 0) fun C =>
  AllSome (fun j : (D.what₂.Tau → UpqT P' Q') →* (D.what₂.Tau → UpqT P Q) =>
    ∀ b ρ, UpqT.mat (j b ρ) * C ρ = C ρ * UpqT.mat (b ρ) ∧
      UpqT.mat (j b ρ) *ᵥ xr ρ = xr ρ) fun j =>
  AllSome (fun o : (D.what₂.Tau → UpqT P Q) →
      (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) =>
    ∀ g ρ, (A ρ *ᵥ fun i => θ ρ (o g 0 i)) = UpqT.mat (g ρ)⁻¹ *ᵥ xr ρ) fun o =>
  AllSome (IsQuotMeasure j (Measure.pi fun _ => D.cd.cd P Q) (Measure.pi fun _ => D.cd.cd P' Q'))
    fun ν => ∫⁻ c : RCosets j, Φi (o c.out) ∂ν = I

def HidaSetting {E : Type} [Field E] [NumberField E] [StarRing E] (W W' : HSpace E)
    (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[E] W.V) : Prop :=
  W.SigOK ∧ (∀ τ, W.sig τ = (P, Q)) ∧ 3 ≤ W.rank ∧
  (if s then P = P' + 1 ∧ Q = Q' else P = P' ∧ Q = Q' + 1) ∧
  W.hT x x = (if s then 1 else -1) ∧ x ∈ W.L0 ∧
  HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧
  W'.SigOK ∧ (∀ τ, W'.sig τ = (P', Q'))

def UnfoldAt (D : D7) : letI := D.host.cmStar; ∀ (W _W' : HSpace D.host.E) (_P _Q _P' _Q' : ℕ)
    (_s : Bool) (_x : W.V), Prop :=
  letI := D.host.cmStar
  fun W W' P Q P' Q' s x =>
  ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (μ' : Measure (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsVolMeas D W P Q μ → IsVolMeas D W' P' Q' μ' →
  ∀ (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (𝓕' : Set (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W'.gram) 𝓕' μ' →
    μ 𝓕 < ⊤ → μ' 𝓕' < ⊤ →
  ∀ Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞, Measurable Φi →
    ∃ I : ℝ≥0∞, IsInfQuotIntegral D W P Q P' Q' x Φi I ∧
      ∫⁻ h in 𝓕, ∑' x' : {x' : W.V // W.hT x' x' = (if s then 1 else -1)},
        atInv D.sp.cm.sig W.gram (latTensor (L0c D W) Φi) h (coords W x'.1) ∂μ = μ' 𝓕' * I

def Unfolding (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W W' : HSpace D.host.E) (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[D.host.E] W.V),
    HidaSetting W W' P Q P' Q' s x ι → (∀ y : W'.V, y ∈ W'.L0 ↔ ι y ∈ W.L0) →
    UnfoldAt D W W' P Q P' Q' s x

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def IsSelfDualLat {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (n → E)) = ⊤ ∧
    (N : Set (n → E)) = dualSet σ J N

def IsSelfDualDefiniteLattice (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) : Prop :=
  letI := D.host.cmStar
  IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N

def stabHat (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  levelAfL D.sp.cm.sig D.sp.gram0 N

def levelU (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  (Lv u).U

def IndexAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  (∀ i : Fin 2, SplitsF D (D.host.g i)) → SplitsF D (D.mem u).A.T →
    ∀ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E), IsSelfDualDefiniteLattice D N →
      levelU D Lv u ≤ stabHat D N →
      (((levelU D Lv u).relIndex (stabHat D N) : ℕ) : ℝ) =
        idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def StabiliserLevelIndexFormula : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), IndexAt D Lv u

theorem factorT_pos (D : D7) (u : D.what₂.Word) :
    0 < (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f := by
  have hT : (1 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.one_lt
  have hk : D.R.k ≠ 0 := by
    have := D.R.m_add_three_le_k
    omega
  have hTk : (1 : ℝ) < ((D.mem u).A.T : ℝ) ^ D.R.k := one_lt_pow₀ hT hk
  exact pow_pos (by linarith) _

theorem stabHat_le (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    letI := D.host.cmStar
    stabHat D N ≤ UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  intro g hg
  unfold stabHat levelAfL level at hg
  exact (Subgroup.mem_inf.mp hg).1

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice

def IsSelfDualLat {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (n → E)) = ⊤ ∧
    dualSet σ J N = (N : Set (n → E))

def stabK (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    Subgroup (GL (Fin D.R.k)
      (TensorProduct D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) :=
  letI := D.host.cmStar
  levelAfL D.sp.cm.sig D.sp.gram0 N

def IndexAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  (∀ i : Fin 2, SplitsF D (D.host.g i)) → SplitsF D (D.mem u).A.T →
    ∀ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E),
      IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N →
      (Lv u).U ≤ stabK D N →
      (((Lv u).U.relIndex (stabK D N) : ℕ) : ℝ) =
        idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def IndexKU : Prop := ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), IndexAt D Lv u

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def withLattice (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : HSpace E :=
  { W with L0 := L, standardTuple_isLattice := hL, baseLattice_isUnimodular := hU }

def HasSignatureEverywhere (W : HSpace E) (P Q : ℕ) : Prop :=
  W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def IsIsometry (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop :=
  HSpace.IsIsomEmb W₁ W₂ e.toLinearMap

def CarriesLattice (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop :=
  ∀ x : W₁.V, x ∈ W₁.L0 ↔ e x ∈ W₂.L0

def frameMatrix (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Matrix (Fin W₂.rank) (Fin W₁.rank) E :=
  LinearMap.toMatrix W₁.frame W₂.frame e.toLinearMap

end Spaces

def Intertwines {A : Type} [CommRing A] {M₁ M₂ : ℕ} (C : Matrix (Fin M₂) (Fin M₁) A)
    (g₁ : Matrix (Fin M₁) (Fin M₁) A) (g₂ : Matrix (Fin M₂) (Fin M₂) A) : Prop :=
  g₂ * C = C * g₁

def pointMatrix {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  (HA.mat R σ J h).val

def baseChange {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {M₁ M₂ : ℕ} (C : Matrix (Fin M₂) (Fin M₁) E) : Matrix (Fin M₂) (Fin M₁) (R ⊗[F] E) :=
  C.map (inclR R)

def IsConjugationBy {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M₁ M₂ : ℕ} (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E)
    (C : Matrix (Fin M₂) (Fin M₁) E) (Φ : HA R σ J₁ → HA R σ J₂) : Prop :=
  ∀ h : HA R σ J₁, Intertwines (baseChange R C) (pointMatrix R σ J₁ h) (pointMatrix R σ J₂ (Φ h))

def LatticeIndependence (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), HasSignatureEverywhere W P Q →
    ∀ (L L' : Submodule (𝓞 D.host.E) W.V)
      (hL : Submodule.IsLattice D.host.E L) (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L)
      (hL' : Submodule.IsLattice D.host.E L') (hU' : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L')
      (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)),
      IsVolMeas D (withLattice W L hL hU) P Q μ ↔ IsVolMeas D (withLattice W L' hL' hU') P Q μ

def IsometryTransport (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSignatureEverywhere W₁ P Q → HasSignatureEverywhere W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, IsIsometry W₁ W₂ e → CarriesLattice W₁ W₂ e →
      ∃ Φ : HA (AF D.host.F) D.sp.cm.sig W₁.gram ≃ₜ* HA (AF D.host.F) D.sp.cm.sig W₂.gram,
        IsConjugationBy (AF D.host.F) D.sp.cm.sig W₁.gram W₂.gram (frameMatrix W₁ W₂ e) Φ ∧
        (∀ h : HA (AF D.host.F) D.sp.cm.sig W₁.gram,
          HA.mat (AF D.host.F) D.sp.cm.sig W₁.gram h ∈ HFin (AF D.host.F) D.sp.cm.sig W₁.gram ↔
            HA.mat (AF D.host.F) D.sp.cm.sig W₂.gram (Φ h) ∈ HFin (AF D.host.F) D.sp.cm.sig W₂.gram) ∧
        (∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
          IsVolMeas D W₁ P Q μ ↔ IsVolMeas D W₂ P Q (μ.map Φ)) ∧
        ∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram), IsVolMeas D W₁ P Q μ →
          ∀ 𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
            IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram) 𝓕 μ ↔
              IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) (Φ '' 𝓕) (μ.map Φ)

def VolumeInvariance (D : D7) : Prop :=
  letI := D.host.cmStar
  VolTie D →
    ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSignatureEverywhere W₁ P Q → HasSignatureEverywhere W₂ P Q →
      (∃ e : W₁.V ≃ₗ[D.host.E] W₂.V, IsIsometry W₁ W₂ e) → D.vol W₁ = D.vol W₂

def VolumeIndependence (D : D7) : Prop :=
  LatticeIndependence D ∧ IsometryTransport D ∧ VolumeInvariance D

end GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsSplitting (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=
  (∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
  (∀ x, φ (sigR σ (v.adicCompletion F) x) = swapR _ (φ x)) ∧
  (∀ x, x ∈ intV E v ↔
    (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F)

variable {v : HeightOneSpectrum (𝓞 F)}
  (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

def prP : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom

def prPbar : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.snd _ _).comp φ.toRingHom

def primeOf (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) : Ideal (intV E v) :=
  Ideal.span {a : intV E v | Valued.v (p a) < 1}

def partOf {n : Type} (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (Λ : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F)) :
    Submodule (v.adicCompletionIntegers F) (n → v.adicCompletion F) :=
  Submodule.span (v.adicCompletionIntegers F)
    ((fun x : n → E ⊗[F] v.adicCompletion F => fun i => p (x i)) '' (Λ : Set _))

abbrev locLat {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (n → E)) : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

end Local

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

abbrev dualLb (L : ColLevel R F E sp gp C A clsLat) : Submodule (𝓞 E) (Fin R.k → E) :=
  Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)

def IsOverLattice (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (Fin R.k → E)) = ⊤ ∧
  dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E)) ∧
  L.Lb ≤ N ∧ N ≤ dualLb L ∧
  ∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∉ v.asIdeal → locLat v N = locLat v L.Lb

def LocalAtT (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal)
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=

  IsSplitting sp.cm.sig v φ ∧

  (∀ x : locLat v (dualLb L), (∀ i, prP φ (x.1 i) = 0) → L.fT v h x = 0) ∧

  Nonempty ((locLat v (dualLb L) ⧸ (locLat v L.Lb).submoduleOf (locLat v (dualLb L))) ≃ₗ[intV E v]
    (intV E v ⧸ primeOf (prP φ)) × (intV E v ⧸ primeOf (prPbar φ))) ∧

  partOf (prP φ) (locLat v N) = partOf (prP φ) (locLat v (dualLb L)) ∧
  partOf (prPbar φ) (locLat v N) = partOf (prPbar φ) (locLat v L.Lb) ∧

  (∀ g' : GL (Fin R.k) (v.adicCompletion F),
    ∃! g : UPts sp.cm.sig sp.gram0 (v.adicCompletion F), bc (prP φ) g.1 = g') ∧

  (∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
    g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ bc (prP φ) g ∈ stabGL (partOf (prP φ) (locLat v N))) ∧

  (∃ b : GL (Fin R.k) (v.adicCompletion F),
    (∀ y : Fin R.k → v.adicCompletion F,
      (b : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ y ∈ partOf (prP φ) (locLat v N) ↔
        ∀ i, y i ∈ v.adicCompletionIntegers F) ∧
    ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ b⁻¹ * bc (prP φ) g * b ∈
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range) ∧

  ∃ (f : partOf (prP φ) (locLat v N) →ₗ[v.adicCompletionIntegers F]
      IsLocalRing.ResidueField (v.adicCompletionIntegers F))
    (ε : L.fM v h ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F)),
    (∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = prP φ a →
      ∀ m, ε (a • m) = a' • ε m) ∧
    (∀ (x : locLat v (dualLb L)) (y : partOf (prP φ) (locLat v N)),
      (∀ i, y.1 i = prP φ (x.1 i)) → f y = ε (L.fT v h x)) ∧
    f ≠ 0 ∧
    (∀ y, f ((A.T : v.adicCompletionIntegers F) • y) = 0) ∧
    (∀ y, f y = 0 ↔ y.1 ∈ partOf (prP φ) (locLat v L.Lb)) ∧
    ∀ g, g ∈ L.Uloc v ↔
      g ∈ levelVL sp.cm.sig sp.gram0 v N ∧ bc (prP φ) g ∈ stabFun (partOf (prP φ) (locLat v N)) f

def HasOverLattice (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  (∀ i : Fin 2, A.T ≠ gp i) ∧
  ∃ N : Submodule (𝓞 E) (Fin R.k → E), IsOverLattice L N ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal), ∃ φ, LocalAtT L N v h φ) ∧
    (∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N) ∧
    L.U ≤ levelAfL sp.cm.sig sp.gram0 N

end Level

def SelfDualOverBase : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word),
    letI := D.host.cmStar
    Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T → HasOverLattice (Lv u)

end GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
end
end
