module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle066
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverRead.CompIndep

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mul_mem_map_of_prod {R : Type} [CommRing R] [IsDedekindDomain R] (f : R →+* R) (A I : Ideal R) (m p : R) (hm : m ≠ 0)
    (h : A * A.map f = Ideal.span {m}) (h1 : A * I * (A * I).map f = Ideal.span {m * p}) :
    ∀ b ∈ A.map f, p * b ∈ (A * I).map f := by
  intro b hb
  have h0 : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm
  rw [Ideal.map_mul, ← Ideal.span_singleton_mul_span_singleton, mul_mul_mul_comm, h] at h1
  have h2 := mul_left_cancel₀ h0 h1
  have h3 : p ∈ I.map f := by
    have h4 := Ideal.mem_span_singleton_self p
    rw [← h2] at h4
    exact (Ideal.mul_le_inf h4).2
  rw [Ideal.map_mul, mul_comm p]
  exact Ideal.mul_mem_mul hb h3

theorem smul_pull {R : Type} [CommRing R] {n : ℕ} (κ : Matrix (Fin n) (Fin n) R) (M p : ℕ) (v y : Fin n → R)
    (e : κ *ᵥ (p • v) - p • v = (M * p) • y) : p • (κ *ᵥ v - v) = p • M • y := by
  rw [smul_sub, ← Matrix.mulVec_smul, e, mul_comm M p, mul_smul]

theorem ratio_mul_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (p : ℕ) (I : Ideal (𝓞 E)) (hM : l₂.M = l.M * p) (hI : l₂.Mb = l.Mb * I) :
    ∀ b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), (p : 𝓞 E) * b ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  have h1 := l₂.prod
  rw [hI, hM, Nat.cast_mul] at h1
  rw [hI]
  refine mul_mem_map_of_prod _ _ _ _ _ (Nat.cast_ne_zero.2 ?_) l.prod h1
  have := l.three_le
  omega

theorem congr_of_marked {D : D7} (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) (M p : ℕ) (hp : p ≠ 0)
    (J J₂ : Ideal (𝓞 D.host.E)) (hJ : ∀ b ∈ J, (p : 𝓞 D.host.E) * b ∈ J₂) (g g' k : GA D V)
    (hk : finHom V k = finHom V (g⁻¹ * g')) (hL : latG V g = latG V g')
    (x : La → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hm : ∀ a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V g,
      x a - (finHom V g).1.mulVec (finVec V (ι a)) = (M * p) • w)
    (hm' : ∀ a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V g',
      x a - (finHom V g').1.mulVec (finVec V (ι a)) = (M * p) • w) :
    ∀ b ∈ J, ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = M • y := by
  refine ((GlobalTheory.Member.AALev.congruences_agree D V k).2 M J).2 fun v hv => ?_
  have hH : latGHat V g' = latGHat V g := by
    rw [GlobalTheory.RecDict.coset_latGHat, GlobalTheory.RecDict.coset_latGHat, hL]
  have hv' : v ∈ (J • (⊤ : Submodule (𝓞 D.host.E) La)).map ι := by
    rw [Submodule.map_smul'', Submodule.map_top, hι.2]
    exact hv
  obtain ⟨a, ha, rfl⟩ := hv'
  have hpa : p • a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La) := by
    refine Submodule.smul_induction_on (p := fun a => p • a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La)) ha
      (fun b hb c _ => ?_) (fun s t hs ht => ?_)
    · rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), smul_smul]
      exact Submodule.smul_mem_smul (hJ b hb) Submodule.mem_top
    · rw [smul_add]
      exact add_mem hs ht
  obtain ⟨w, hw, e⟩ := hm _ hpa
  obtain ⟨w', hw', e'⟩ := hm' _ hpa
  rw [hH] at hw'
  obtain ⟨y, hy, ey⟩ := GlobalTheory.RecDict.coset_fin (latGHat V 1) (latGHat V g) (finHom V g) (finHom V g') 1 (M * p)
    (fun u hu => ((GlobalTheory.MarkCoset.latG_spec D V g).2 u).1 hu) (fun u hu => by simpa using hu)
    (fun u hu => by simpa using hu) _ _ w w' 0 hw hw' (zero_mem _) e e' (by simp)
  refine ⟨y, hy, ?_⟩
  have hf : finVec V (ι (p • a)) = p • finVec V (ι a) := by
    rw [map_nsmul]
    exact AdLat.cap_fv_nsmul D.host.F p _
  rw [hf, one_mul, ← map_inv, ← map_mul, ← hk] at ey
  funext i
  exact GlobalTheory.MarkCoset.nsmul_cancel D.host.F p (Nat.cast_ne_zero.2 hp) (congrFun (smul_pull _ M p _ y ey) i)

theorem comp_eq_of_cover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h h' : GA D (T.V j σ), (C.dict₂ h).1 = (C.dict₂ h').1 → (T.dict j σ h).1 = (T.dict j σ h').1 := by
  intro D T hT j hj σ hσ C hC h h' hh
  obtain ⟨⟨-, hM, -, hI, -⟩, -, -, -, -, hr, g, e, F, ik, φ, th, -, -, -, hd⟩ := hC
  obtain ⟨hr', -, -, -, -, -, -, hι, -⟩ := hT.adPin j hj σ hσ
  obtain ⟨th', hr'', -, hQ, hK, ⟨x0, -, hR⟩, -⟩ := hT.dictU j hj σ hσ
  obtain ⟨γ, hγ, hΛ, hm, -⟩ := hd h
  obtain ⟨γ', hγ', hΛ', hm', -⟩ := hd h'
  rw [← hh] at hΛ' hm'
  have hinj : Function.Injective (fun v : Fin (T.V j σ).rank → D.host.E => v ∘ Fin.cast hr.symm) := fun u v huv =>
    funext fun i => congrFun huv (Fin.cast hr i)
  have hL : latG (T.V j σ) (γ * h) = latG (T.V j σ) (γ' * h') :=
    SetLike.coe_injective (hinj.image_injective (hΛ.symm.trans hΛ'))
  obtain ⟨a, ha, k, hk, eak⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ * h)⁻¹ * (γ' * h'))
  have hp : C.d.pd ≠ 0 := fun h0 => by
    have := C.d.l₂.three_le
    rw [hM, h0] at this
    omega
  have hk' : k ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k).2 ⟨hk, ?_⟩
    have hm₁ := hm
    have hm₂ := hm'
    rw [hM] at hm₁ hm₂
    exact congr_of_marked (T.V j σ) _ hι _ _ hp _ _ (ratio_mul_mem T.Q.l C.d.l₂ _ _ hM hI) (γ * h) (γ' * h') k
      (by rw [eak, map_mul, show finHom (T.V j σ) a = 1 from ha, one_mul]) hL _ hm₁ hm₂
  have q : ∀ δ ∈ GQ (T.V j σ), ∀ u, (T.dict j σ (δ * u)).1 = (T.dict j σ u).1 := fun δ hδ u => by
    obtain ⟨_, -, e⟩ := hQ δ hδ u
    rw [e]
  have q₁ : (T.dict j σ (γ * h * a * k)).1 = (T.dict j σ (γ * h * a)).1 := by
    obtain ⟨_, -, e⟩ := hK k hk' (γ * h * a)
    rw [e]
  have q₂ : (T.dict j σ (γ * h * a)).1 = (T.dict j σ (γ * h)).1 := by
    obtain ⟨_, -, e⟩ := hR (γ * h) a ha
    rw [e]
  rw [← q γ hγ h, ← q γ' hγ' h', ← q₂, ← q₁, mul_assoc (γ * h), ← eak, mul_inv_cancel_left]

end GlobalTheory.CoverRead.CompIndep
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def Gen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (g : GA D (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ), FinLike R i t f ∧ φ = R.ωP i t (1, g) f}

def TypeVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t),
    R.ωP i t (κ, 1) f = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f

def TypeDiff (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), ∃ f : WO (Vc D i) (Wc D i) → ℂ,
    IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ φ = R.ωP i t (κ, 1) f - (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f}

def IsLifts (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (κ : G → GA D (Vc D i)) : Prop :=
  ∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g)

def avgW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool) (ε : ℤ)
    (κ : G → GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) : WO (Vc D i) (Wc D i) → ℂ :=
  ∑ g, (mirC R i PP a tr ε g * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • R.ωP i t ((κ g)⁻¹, 1) f

def AvgIm (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 ∧ ∃ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
    ∃ κ : G → GA D (Vc D i), IsLifts R i t κ ∧ ∃ f : WO (Vc D i) (Wc D i) → ℂ,
      IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ φ = avgW R i t PP a tr ε κ f}

def Clean (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    ∀ κ : G → GA D (Vc D i), IsLifts R i t κ → avgW R i t PP a tr ε κ f = 0

section ThetaAlg

variable {ψ : AddChar (AF D.host.F) ℂ} {S T' : HSp D}

theorem heisO_add' (u : WO S T') (f g : WO S T' → ℂ) : heisO ψ S T' u (f + g) = heisO ψ S T' u f + heisO ψ S T' u g := by
  funext w; simp only [heisO, Pi.add_apply]; ring

theorem theta_add {f g : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) :
    IsThetaFunO ψ S T' (f + g) := {
  quasi γ w := by simp only [Pi.add_apply]; rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hUo', hU'⟩ := hg.level
    refine ⟨U ⊓ U', hUo.inter hUo', fun u hu hi => ?_⟩
    rw [heisO_add', hU u hu.1 hi, hU' u hu.2 hi]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w) }

theorem theta_smul (c : ℂ) {f : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) : IsThetaFunO ψ S T' (c • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T' u (c • f) = c • heisO ψ S T' u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w) }

theorem theta_sub {f g : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) :
    IsThetaFunO ψ S T' (f - g) := by
  have e : f - g = f + (-1 : ℂ) • g := by funext w; simp [sub_eq_add_neg]
  rw [e]
  exact theta_add hf (theta_smul (-1) hg)

theorem theta_sum {ι : Type} (s : Finset ι) (u : ι → WO S T' → ℂ)
    (f₀ : WO S T' → ℂ) (h₀ : IsThetaFunO ψ S T' f₀) (hu : ∀ k ∈ s, IsThetaFunO ψ S T' (u k)) :
    IsThetaFunO ψ S T' (∑ k ∈ s, u k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := theta_smul (0 : ℂ) h₀
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact theta_add (hu a (Finset.mem_insert_self _ _)) (ih fun k hk => hu k (Finset.mem_insert_of_mem hk))

end ThetaAlg

end GlobalTheory.DownLift.GenFinite

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.Prism

theorem semiBC_basis (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M]
    [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (h : SemiBC u)
    (ι : Type) (e : Module.Basis ι A M) : ∃ b : Module.Basis ι B N, ∀ i, b i = u (e i) := by
  classical
  let g : (ι →₀ B) →ₗ[B] N := Finsupp.linearCombination B (fun i => u (e i))
  let v : M →ₛₗ[f] (ι →₀ B) :=
    { toFun := fun x => Finsupp.mapRange f f.map_zero (e.repr x)
      map_add' := fun x y => by
        ext i; simp
      map_smul' := fun a x => by
        ext i; simp }
  obtain ⟨w, hw, -⟩ := h (ι →₀ B) v
  have key : ∀ x : M, g (v x) = u x := by
    intro x
    conv_rhs => rw [← e.linearCombination_repr x]
    simp only [g, v, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (fun i => by simp), map_finsuppSum]
    refine Finsupp.sum_congr (fun i _ => ?_)
    simp
  have h1 : w.comp g = LinearMap.id := by
    ext i
    simp [g, hw, v]
  have h2 : g.comp w = LinearMap.id := by
    obtain ⟨w0, -, huniq⟩ := h N u
    have a1 := huniq (g.comp w) (fun x => by simp [hw, key])
    have a2 := huniq LinearMap.id (fun x => rfl)
    rw [a1, a2]
  let E : N ≃ₗ[B] (ι →₀ B) := LinearEquiv.ofLinear w g h1 h2
  refine ⟨Module.Basis.ofRepr E, fun i => ?_⟩
  simp [Module.Basis.ofRepr, E, g]

end GlobalTheory.Prism
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.LSq

def cInt (l : ℕ) (n : ℕ) : ℤ := ((n : ℤ) - (n : ℤ) ^ l) / l

theorem l_mul_cInt (l : ℕ) [hl : Fact l.Prime] (n : ℕ) : (l : ℤ) * cInt l n = (n : ℤ) - (n : ℤ) ^ l := by
  unfold cInt
  apply Int.mul_ediv_cancel'
  have h : (((n : ℤ) - (n : ℤ) ^ l : ℤ) : ZMod l) = 0 := by
    push_cast; rw [ZMod.pow_card, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h

theorem δ_natCast (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (n : ℕ) :
    D.δ (n : A) = ((cInt l n : ℤ) : A) := by
  induction n with
  | zero =>
    have : cInt l 0 = 0 := by
      unfold cInt; simp [zero_pow hl.out.ne_zero]
    simp [this, Delta.δ_zero]
  | succ n ih =>
    have h := D.δ_add (n : A) 1
    rw [D.δ_one, ih] at h
    push_cast
    rw [h]
    have key : cInt l (n + 1) = cInt l n - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k := by
      have h0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
      apply mul_left_cancel₀ h0
      have e1 := l_mul_cInt l (n + 1)
      have e2 := l_mul_cInt l n
      have h5 : ((n : ℤ) + 1) ^ l = (n : ℤ) ^ l + 1 ^ l + (l : ℤ) *
          ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k * (1 : ℤ) ^ (l - k) := by
        rw [add_pow_prime_eq' hl.out]
        congr 2
        refine Finset.sum_congr rfl fun k _ => by ring
      simp only [one_pow, mul_one] at h5
      push_cast at e1
      rw [mul_sub, e1, e2, h5]; ring
    rw [key, Int.cast_sub, Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, one_pow, mul_one, add_zero]

theorem cInt_self (l : ℕ) [hl : Fact l.Prime] : cInt l l = 1 - (l : ℤ) ^ (l - 1) := by
  have h0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  apply mul_left_cancel₀ h0
  rw [l_mul_cInt, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hl.out.one_le]

theorem δ_l (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) :
    D.δ (l : A) = 1 - (l : A) ^ (l - 1) := by
  rw [δ_natCast, cInt_self]; push_cast; ring

theorem δ_mem_of_mem_sq (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (m : Ideal A)
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m ^ 2) : D.δ x ∈ m := by
  rw [sq] at hx
  have hl0 := hl.out.ne_zero
  suffices x ∈ m ∧ D.δ x ∈ m from this.2
  refine Submodule.mul_induction_on hx (fun a ha b hb => ⟨m.mul_mem_right b ha, ?_⟩) ?_
  · rw [D.δ_mul]
    refine m.add_mem (m.add_mem (m.mul_mem_right _ (m.pow_mem_of_mem ha _ (Nat.pos_of_ne_zero hl0)))
      (m.mul_mem_right _ (m.pow_mem_of_mem hb _ (Nat.pos_of_ne_zero hl0)))) ?_
    exact m.mul_mem_right _ (m.mul_mem_right _ hlm)
  · rintro x y ⟨hx, hδx⟩ ⟨hy, hδy⟩
    refine ⟨m.add_mem hx hy, ?_⟩
    rw [D.δ_add]
    refine m.sub_mem (m.add_mem hδx hδy) (m.sum_mem fun k hk => ?_)
    obtain ⟨hk0, hkl⟩ := Finset.mem_Ioo.1 hk
    exact m.mul_mem_left _ (m.pow_mem_of_mem hy _ (Nat.sub_pos_of_lt hkl))

theorem l_not_mem_sq : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (m : Ideal A),
    m ≠ ⊤ → (l : A) ∈ m → (l : A) ∉ m ^ 2 ∧ D.δ (l : A) ∉ m := by
  intro l hl A _ D m hm hlm
  have hδ : D.δ (l : A) ∉ m := by
    intro h
    rw [δ_l] at h
    have h2 : (l : A) ^ (l - 1) ∈ m :=
      m.pow_mem_of_mem hlm _ (Nat.sub_pos_of_lt hl.out.one_lt)
    exact hm ((Ideal.eq_top_iff_one _).2 (by simpa using m.add_mem h h2))
  exact ⟨fun h => hδ (δ_mem_of_mem_sq l D m hlm h), hδ⟩

end GlobalTheory.BSP.LSq
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isFrac_transition : ∀ (A A' : Type) [CommRing A] [CommRing A'] (k : A →+* A') (N : Type) [AddCommGroup N] [Module A N] (N' : Type) [AddCommGroup N'] [Module A' N'] (τ : N →ₛₗ[k] N') (t : A) (t' : A') (a : ℕ) (y : LocalizedModule (Submonoid.powers t) N) (y' : LocalizedModule (Submonoid.powers t') N') (z m : N) (z' n : N') (i j : ℕ), IsFrac t y z a → IsFrac t y m i → IsFrac t' y' z' a → IsFrac t' y' n j → t' ^ a • τ z = k t ^ a • z' → ∃ r : ℕ, (k t * t') ^ r • (t' ^ j • τ m - k t ^ i • n) = 0 := by
  intro A A' _ _ k N _ _ N' _ _ τ t t' a y y' z m z' n i j h1 h2 h3 h4 h5
  unfold IsFrac at h1 h2 h3 h4
  obtain ⟨⟨_, r₁, rfl⟩, e1⟩ := LocalizedModule.mk_eq.1 (h1.symm.trans h2)
  obtain ⟨⟨_, r₂, rfl⟩, e2⟩ := LocalizedModule.mk_eq.1 (h3.symm.trans h4)
  simp only [Submonoid.smul_def] at e1 e2
  have e3 := congrArg τ e1
  simp only [map_smulₛₗ, map_pow] at e3
  refine ⟨r₁ + r₂ + a, ?_⟩
  linear_combination (norm := skip) (-(k t ^ r₂ * t' ^ (r₁ + r₂ + a) * t' ^ j)) • e3
    + (k t ^ (r₂ + r₁ + i) * t' ^ (r₁ + r₂ + j)) • h5
    + (k t ^ (r₁ + r₂ + a + i) * t' ^ r₁) • e2
  match_scalars <;> ring

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP


open TensorProduct in
theorem _root_.GlobalTheory.BSP.semiBC_iff_isBaseChange (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type)
    [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] (u : M →ₛₗ[algebraMap A B] N) (u' : M →ₗ[A] N)
    (h : ∀ x, u' x = u x) : _root_.GlobalTheory.Prism.SemiBC u ↔ IsBaseChange B u' := by
  constructor
  · intro hu
    refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g => ?_
    letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup B
    let v : M →ₛₗ[algebraMap A B] Q :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun a x => by simp [algebraMap_smul] }
    obtain ⟨w, hw, hw'⟩ := hu Q v
    refine ⟨w, ?_, fun w₂ hw₂ => hw' w₂ fun x => ?_⟩
    · ext x
      simp [h, hw x, v]
    · rw [← h]
      exact LinearMap.congr_fun hw₂ x
  · intro hb Q _ _ v
    letI : Module A Q := Module.compHom Q (algebraMap A B)
    haveI : IsScalarTower A B Q :=
      ⟨fun a b q => by
        show (a • b) • q = algebraMap A B a • b • q
        rw [Algebra.smul_def, mul_smul]⟩
    let g : M →ₗ[A] Q :=
      { toFun := v
        map_add' := v.map_add
        map_smul' := fun a x => by
          rw [v.map_smulₛₗ]
          rfl }
    refine ⟨hb.lift g, fun x => ?_, fun w hw => hb.algHom_ext _ _ fun x => ?_⟩
    · rw [← h, hb.lift_eq]
      rfl
    · rw [hb.lift_eq, h, hw]
      rfl

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_finite_projective_lift_of_isAdicComplete : ∀ (A : Type) [CommRing A] (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (N : Type) [AddCommGroup N] [Module (A ⧸ 𝔞) N] [Module.Finite (A ⧸ 𝔞) N] [Module.Projective (A ⧸ 𝔞) N], ∃ (P : Type) (_ : AddCommGroup P) (_ : Module A P) (_ : Module.Finite A P) (_ : Module.Projective A P) (u : P →ₛₗ[Ideal.Quotient.mk 𝔞] N), SemiBC u := by
  first | exact @GlobalTheory.BSP.LiftProj.exists_lift | exact GlobalTheory.BSP.LiftProj.exists_lift | (intros; apply GlobalTheory.BSP.LiftProj.exists_lift <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isSemilinearBaseChange_localized_of_torsion_bounded : ∀ (A : Type) [CommRing A] (φ : A →+* A) (t : A) (N : Type) [AddCommGroup N] [Module A N] (P : Type) [AddCommGroup P] [Module A P] (u : N →ₛₗ[φ] P), SemiBC u → ∀ (L : P →ₗ[A] N) (n a : ℕ), (∀ y, L y = 0 → t ^ n • y = 0) → (∀ x, ∃ y, L y = t ^ n • x) → ∀ Φ : N →ₛₗ[(algebraMap A (Localization.Away t)).comp φ] LocalizedModule (Submonoid.powers t) N, (∀ x, IsFrac t (Φ x) (L (u x)) a) → SemiBC Φ := by
  first | exact @GlobalTheory.BSP.semiBC_localized | exact GlobalTheory.BSP.semiBC_localized | (intros; apply GlobalTheory.BSP.semiBC_localized <;> assumption)
end
