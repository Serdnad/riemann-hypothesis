module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
public import Mathlib.Algebra.AffineMonoid.Basic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle090
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle089
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle092
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle088
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

noncomputable section

open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct

namespace GlobalTheory.OneFunctional

section General

variable {G H K V W X : Type} [Monoid G] [Monoid H] [Monoid K] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

def Iso (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∃ e : V ≃ₗ[ℂ] W, ∀ g x, e (ρ g x) = σ g (e x)

theorem Iso.refl (ρ : Representation ℂ G V) : Iso ρ ρ := ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem Iso.symm {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) : Iso σ ρ := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, fun g x => e.injective (by rw [he]; simp)⟩

theorem Iso.trans {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X} (h : Iso ρ σ)
    (h' : Iso σ τ) : Iso ρ τ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun g x => by simp [he, he']⟩

theorem Iso.comp {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (f : H →* G) :
    Iso (ρ.comp f : Representation ℂ H V) (σ.comp f) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun g x => he (f g) x⟩

theorem Iso.twist {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (χ : G →* ℂˣ) :
    Iso (twist χ ρ) (twist χ σ) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun g x => ?_⟩
  change e ((χ g : ℂ) • ρ g x) = (χ g : ℂ) • σ g (e x)
  rw [map_smul, he]

theorem Iso.tprod {V' W' : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'}
    (h : Iso ρ σ) (h' : Iso ρ' σ') : Iso (ρ.tprod ρ') (σ.tprod σ') := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨TensorProduct.congr e e', fun g x => ?_⟩
  induction x with
  | tmul a b => simp [he, he']
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem Iso.tprod_comm (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Iso (ρ.tprod σ) (σ.tprod ρ) := by
  refine ⟨TensorProduct.comm ℂ V W, fun g x => ?_⟩
  induction x with
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem Iso.dual {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Iso ρ.dual σ.dual := by
  obtain ⟨e, he⟩ := h.symm
  refine ⟨e.dualMap, fun g x => ?_⟩
  ext w
  simp [Module.Dual.transpose_apply, he]

theorem Iso.of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) : Iso ρ σ :=
  ⟨e.toLinearEquiv, fun g x => e.toIntertwiningMap.isIntertwining _ _ g x⟩

theorem mem_invFun {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} : l ∈ invFun ρ ↔ ∀ g x, l (ρ g x) = l x := Iff.rfl

theorem Iso.nonempty_invFun_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Nonempty (invFun ρ ≃ₗ[ℂ] invFun σ) := by
  obtain ⟨e, he⟩ := h.symm
  refine ⟨e.dualMap.ofSubmodules _ _ (le_antisymm ?_ fun l hl => ⟨e.symm.dualMap l, fun g x => ?_, ?_⟩)⟩
  · rintro _ ⟨l, hl, rfl⟩ g x
    change l (e (σ g x)) = l (e x)
    rw [he, hl]
  · obtain ⟨x, rfl⟩ := e.surjective x
    change l (e.symm _) = l (e.symm _)
    rw [← he, e.symm_apply_apply, e.symm_apply_apply, hl]
  · ext x
    simp

theorem Iso.finrank_invFun {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Module.finrank ℂ (invFun ρ) = Module.finrank ℂ (invFun σ) := by
  obtain ⟨e⟩ := h.nonempty_invFun_equiv
  exact e.finrank_eq

theorem Iso.invFun_eq_bot {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (h0 : invFun σ = ⊥) :
    invFun ρ = ⊥ := by
  obtain ⟨e⟩ := h.nonempty_invFun_equiv
  rw [← Submodule.subsingleton_iff_eq_bot] at h0 ⊢
  exact e.toEquiv.subsingleton

def Contracts {F : Type} [AddCommGroup F] [Module ℂ F] (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V)
    (σ' : Representation ℂ G W) : Prop :=
  ∃ π : F ⊗[ℂ] V →ₗ[ℂ] W, Function.Surjective π ∧
    (∀ h g f v, π (φ (h, g) f ⊗ₜ σ h v) = σ' g (π (f ⊗ₜ v))) ∧
    ∀ l : Module.Dual ℂ (F ⊗[ℂ] V), (∀ h f v, l (φ (h, 1) f ⊗ₜ σ h v) = l (f ⊗ₜ v)) → ∀ x, π x = 0 → l x = 0

theorem Contracts.congr {F F' V' W' : Type} [AddCommGroup F] [Module ℂ F] [AddCommGroup F'] [Module ℂ F']
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {φ : Representation ℂ (H × G) F} {σ : Representation ℂ H V} {τ : Representation ℂ G W}
    {φ' : Representation ℂ (H × G) F'} {σ' : Representation ℂ H V'} {τ' : Representation ℂ G W'}
    (h : Contracts φ σ τ) (h1 : Iso φ φ') (h2 : Iso σ σ') (h3 : Iso τ τ') : Contracts φ' σ' τ' := by
  obtain ⟨π, hs, he, hk⟩ := h
  obtain ⟨e1, he1⟩ := h1
  obtain ⟨e2, he2⟩ := h2
  obtain ⟨e3, he3⟩ := h3
  refine ⟨e3.toLinearMap ∘ₗ π ∘ₗ (TensorProduct.congr e1 e2).symm.toLinearMap,
    e3.surjective.comp (hs.comp (TensorProduct.congr e1 e2).symm.surjective), fun h g f v => ?_, fun l hl x hx => ?_⟩
  · obtain ⟨f, rfl⟩ := e1.surjective f
    obtain ⟨v, rfl⟩ := e2.surjective v
    simp [← he1, ← he2, he, he3]
  · obtain ⟨x, rfl⟩ := (TensorProduct.congr e1 e2).surjective x
    refine hk (l ∘ₗ (TensorProduct.congr e1 e2).toLinearMap) (fun h f v => ?_) x ?_
    · simp [he1, he2, hl]
    · change e3 (π ((TensorProduct.congr e1 e2).symm ((TensorProduct.congr e1 e2) x))) = 0 at hx
      simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.map_eq_zero_iff] using hx

end General

section Outer

variable {ι G H : Type} [Monoid G] [Monoid H] {V W : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]

def outer (ρ : ∀ τ, Representation ℂ G (V τ)) : Representation ℂ (ι → G) (⨂[ℂ] τ, V τ) :=
  piTprod fun τ => (ρ τ).comp (Pi.evalMonoidHom (fun _ : ι => G) τ)

def outer₂ (ρ : ∀ τ, Representation ℂ (H × G) (V τ)) : Representation ℂ ((ι → H) × (ι → G)) (⨂[ℂ] τ, V τ) :=
  piTprod fun τ => (ρ τ).comp ((Pi.evalMonoidHom (fun _ : ι => H) τ).prodMap (Pi.evalMonoidHom (fun _ : ι => G) τ))

theorem piTprod_apply (ρ : ∀ τ, Representation ℂ G (V τ)) (g : G) :
    piTprod ρ g = PiTensorProduct.map fun τ => ρ τ g := rfl

theorem outer_apply (ρ : ∀ τ, Representation ℂ G (V τ)) (g : ι → G) :
    outer ρ g = PiTensorProduct.map fun τ => ρ τ (g τ) := rfl

theorem outer₂_apply (ρ : ∀ τ, Representation ℂ (H × G) (V τ)) (h : ι → H) (g : ι → G) :
    outer₂ ρ (h, g) = PiTensorProduct.map fun τ => ρ τ (h τ, g τ) := rfl

theorem Iso.outer {ρ : ∀ τ, Representation ℂ G (V τ)} {σ : ∀ τ, Representation ℂ G (W τ)} (h : ∀ τ, Iso (ρ τ) (σ τ)) :
    Iso (outer ρ) (outer σ) := by
  choose e he using h
  refine ⟨PiTensorProduct.congr e, fun g x => ?_⟩
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v => simp [outer_apply, he]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end Outer

abbrev U (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

def conjU (n : ℕ) : U n →* U n where
  toFun g := ⟨(star g.1)ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : star g.1 * g.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 g.2
    have e : star (star g.1)ᵀ = (g.1)ᵀ := by ext i j; simp
    rw [e, ← Matrix.transpose_mul, mul_eq_one_comm.1 h, Matrix.transpose_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [star_mul, Matrix.transpose_mul])

@[simp] theorem conjU_coe (n : ℕ) (g : U n) : (conjU n g).1 = (star g.1)ᵀ := rfl

abbrev irr (n : ℕ) (lam : DomWeight n) : Representation ℂ (U n) (nablaSq ℂ n lam) := smallRep (unitaryIncl n) lam

def fockOne (a b : ℕ) (α β : ℤ) : Representation ℂ (U a × U b) (MvPolynomial (Fin b × Fin a) ℂ) :=
  twist ((detU a ^ α).comp (MonoidHom.fst _ _) * (detU b ^ β).comp (MonoidHom.snd _ _))
    (GlobalTheory.GLDuality.polyRep ((unitaryIncl a).comp (conjU a)) (unitaryIncl b))

def StepW {a b : ℕ} (α β : ℤ) (lam : DomWeight a) (lam' : DomWeight b) : Prop :=
  ∀ i : Fin b, lam'.w i = if h : i.1 < a then lam.w ⟨i.1, h⟩ + α + β else β

end GlobalTheory.OneFunctional
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)

namespace GlobalTheory.DefFree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

instance factTypePrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

theorem finE_mem (V : HSp D) (h : GA D V) : finE V h ∈ UA D.sp.cm V.gram := by
  have h0 : matHom V h ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    let h' : HR (AF D.host.F) D.sp.cm.sig V.gram := h
    exact h'.2
  have h1 := Formalism.UG.P.bc_mem _ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig)
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom ?c1 _ _ h0
  have h2 := Formalism.UG.P.bc_mem _ (Formalism.UG.sigR D.sp.cm.sig (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) (swapAE D) ?c2 _ _ h1
  convert h2 using 1
  case e'_5 => rfl
  case e'_4 =>
    unfold UA Formalism.UG.UPts
    congr 1
  case c2 =>
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [swapAE, sigR, Formalism.UG.sigR]
    | add x y hx hy => simp only [RingHom.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
  case c1 =>
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR]
    | add x y hx hy => simp only [RingHom.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]

def finU (V : HSp D) : GA D V →* UA D.sp.cm V.gram := (finE V).codRestrict _ (finE_mem V)

theorem coe_finU (V : HSp D) (h : GA D V) : (finU V h : GL (Fin V.rank) (EAf D)) = finE V h := rfl

def clsA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (h : GA D V) : Cl D.sp.cm V.gram K :=
  Quotient.mk'' (finU V h)

def evAt {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : GA D V) :
    MMap M →ₗ[ℂ] MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) ℂ where
  toFun T := (LinearMap.proj h : (GA D V → ℂ) →ₗ[ℂ] ℂ).compMultilinearMap T
  map_add' T T' := by ext v; simp
  map_smul' c T := by ext v; simp

theorem evAt_apply {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : GA D V) (T : MMap M) (v : M.Vec) :
    evAt M h T v = T v h := rfl

def eig {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (P : Subgroup G) (χ : P → ℂ) :
    Submodule ℂ M :=
  ⨅ g : P, LinearMap.ker (ρ g - χ g • LinearMap.id)

theorem mem_eig {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] {ρ : Representation ℂ G M} {P : Subgroup G}
    {χ : P → ℂ} {x : M} : x ∈ eig ρ P χ ↔ ∀ g : P, ρ g x = χ g • x := by
  simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

abbrev GProd (D : D7) : Type :=
  (D.nd.PlG 0 → GlobalTheory.BadShare.GG (D.host.g 0) D.R.r) × (D.nd.PlG 1 → GlobalTheory.BadShare.GG (D.host.g 1) D.R.r)

end GlobalTheory.DefFree

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff char_fin_add)
open scoped nonZeroDivisors

namespace GlobalTheory.SplitUnram

variable {F : Type} [Field F] [NumberField F]

theorem mem_adelicIdeal_codiff_iff {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ)
    (h : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ))) (y : Af F) :
    y ∈ adelicIdeal (codiff F) ↔
      ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 (α * y)) = 1 := by
  have h1 : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) = 1 ↔
      Algebra.trace ℚ F x ∈ (algebraMap ℤ ℚ).range := fun x => by
    rw [h, mul_comm, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have := mul_right_cancel₀ Complex.two_pi_I_ne_zero hn
      rw [eq_intCast]
      exact_mod_cast this.symm
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, eq_intCast, Rat.cast_intCast]⟩
  have h2 : ∀ x : F, x ∈ codiff F ↔
      ∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1 := fun x => by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
    simp_rw [h1, Algebra.traceForm_apply]
    constructor
    · intro H a
      rw [mul_comm]
      exact H _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
    · intro H a ha
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      rw [mul_comm]
      exact H a
  have key : ∀ x : F, x ∈ codiff F ↔ ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) →
      ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := fun x => by
    rw [h2]
    refine ⟨fun H α hα => GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hc x H α hα,
      fun H a => ?_⟩
    rw [map_mul]
    refine H _ fun v => ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, adele_algebraMap_apply, valued_algebraMap]
    exact v.valuation_le_one a
  have hint : ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 α) = 1 :=
    fun α hα => by
      have := (key 1).1 (one_le_codiff (FractionalIdeal.one_mem_one _)) α hα
      rwa [map_one, mul_one] at this
  obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F)) y
  have hx1 := mem_adelicIdeal_one_iff.1 hx
  have hx2 : y - algebraMap F (Af F) x ∈ adelicIdeal (codiff F) := by
    refine (mem_adelicIdeal_iff codiff_ne_zero).2 fun v => (hx1 v).trans ?_
    have := FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    rw [← exp_zero, exp_le_exp]
    omega
  have e : y = algebraMap F (Af F) x + (y - algebraMap F (Af F) x) := by ring
  rw [e, (adelicIdeal (codiff F)).add_mem_iff_left hx2, algebraMap_mem_adelicIdeal codiff_ne_zero, key]
  refine forall_congr' fun α => forall_congr' fun hα => ?_
  rw [mul_add, char_fin_add, hint (α * (y - algebraMap F (Af F) x))
    fun v => mul_mem (hα v) (hx1 v), mul_one]

theorem not_dvd_different {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (p : 𝓞 F) ∈ v.asIdeal) (h2 : (p : 𝓞 F) ∉ v.asIdeal ^ 2) :
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {(p : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 F)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {(p : ℤ)}) ≤ v.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have := v.isPrime
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [not_dvd_differentIdeal_iff]
  apply Ideal.ramificationIdx_eq_one_iff.1
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) v.asIdeal hb]
  by_contra hne
  rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
  exact h2 (by simpa using hne)

theorem count_codiff_eq_zero (v : HeightOneSpectrum (𝓞 F)) (h : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    FractionalIdeal.count F v (codiff F) = 0 := by
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have h1 := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv,
    not_not.1 (mt (Associates.count_ne_zero_iff_dvd h0 v.irreducible).1 h)] at h1
  simpa using h1

theorem not_mem_sq_of_ext {E : Type} [Field E] [NumberField E] [Algebra F E] {p : ℕ}
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → (p : 𝓞 E) ∉ w.asIdeal ^ 2)
    (v : HeightOneSpectrum (𝓞 F)) : (p : 𝓞 F) ∉ v.asIdeal ^ 2 := by
  intro hv
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hb : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q :=
    Ideal.map_le_iff_le_comap.2 hQv.over.le
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hv
  rw [Ideal.map_pow, map_natCast] at h1
  have h2 : (p : 𝓞 E) ∈ Q ^ 2 := Ideal.pow_right_mono hle 2 h1
  exact h ⟨Q, hQ.isPrime, hb⟩ (Ideal.pow_le_self two_ne_zero h2) h2

end GlobalTheory.SplitUnram

end
end

section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainCells

theorem vol_dcell_and_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)]
    (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 →
  ∀ [MeasurableSpace (GL (Fin (l * t)) k)] [BorelSpace (GL (Fin (l * t)) k)] (μK : Measure (GL (Fin (l * t)) k))
    [μK.IsHaarMeasure], μK (KO k (Fin (l * t))) = 1 →
  (∀ e : Fin (l * t) → ℤ, m.real (dcell ϖ (e ∘ (blkEquiv l t).symm)) =
    (resCard k : ℝ) ^ ((r : ℤ) * sumAbs e) * μK.real (cell k (Fin (l * t)) ϖ e)) ∧
  Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
    (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  intro k _ _ _ _ ϖ hϖ r l t _ _ m _ hm _ _ μK _ hμK
  refine ⟨fun e => ?_, GlobalTheory.T.pairwise_disjoint_parahoricTorusDoubleCoset_antitone k ϖ hϖ r l t⟩
  obtain ⟨ho, hc⟩ := GlobalTheory.T.isOpen_isCompact_twoBlockParahoricSubgroup k (Fin r) (Blocks l t)
  have h1 := GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul m _ ho hc (mtor (A := Fin r) ϖ (e ∘ (blkEquiv l t).symm))
  have h2 := GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul μK (KO k (Fin (l * t))) SplitFlip.isOpen_KO SplitFlip.isCompact_KO (torusElt k _ ϖ e)
  have hs : sumAbs (e ∘ (blkEquiv l t).symm) = sumAbs e := by
    unfold sumAbs; exact Equiv.sum_comp (blkEquiv l t).symm (fun i => |e i|)
  have hm1 : m.real (parahoric k (Fin r) (Blocks l t) : Set _) = 1 := by simp [Measure.real, hm]
  have hK1 : μK.real (KO k (Fin (l * t)) : Set _) = 1 := by simp [Measure.real, hμK]
  rw [dcell, h1, cell, h2, hm1, hK1, GlobalTheory.T.relIndex_twoBlockParahoric_conj_torusDiagElement k ϖ hϖ, GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex k ϖ _ _ (blkEquiv l t), hs]
  simp

end GlobalTheory.ChainCells
end
end
