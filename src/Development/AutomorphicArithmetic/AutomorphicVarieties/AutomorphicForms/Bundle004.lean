module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Mathlib.Data.Multiset.Functor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.AutomorphicFormsLeSm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.CoeSmEqSymm
public import GroundTheory.AutomorphicForms.TensorProductTheorem.CentralCusp
public import GroundTheory.AutomorphicForms.TensorProductTheorem.NonemptyAdelicDecomposition
public import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspCentral
public import GroundTheory.AutomorphicForms.TensorProductTheorem.CuspidalRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Af

section Rep

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

def IsIrr (r : Γ →* GL (Fin n) k) : Prop := IsIrrSub r ⊤

def RepIso (r r' : Γ →* GL (Fin n) k) : Prop := ∃ g : GL (Fin n) k, ∀ s, r' s = g * r s * g⁻¹

def tw (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) : Γ →* GL (Fin n) k where
  toFun s := Matrix.GeneralLinearGroup.scalar (Fin n) (χ s) * r s
  map_one' := by simp
  map_mul' s t := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, smul_smul, mul_comm]

theorem tw_val (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (s : Γ) :
    (tw r χ s : Matrix (Fin n) (Fin n) k) = (χ s : k) • (r s : Matrix (Fin n) (Fin n) k) := by
  simp [tw, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

def IsDiagOn (r : Γ →* GL (Fin n) k) (H : Subgroup Γ) (χ : Fin n → Γ →* kˣ) : Prop :=
  ∃ g : GL (Fin n) k, ∀ s ∈ H, ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
    Matrix.diagonal fun i => (χ i s : k)

def IsFlagOn (r : Γ →* GL (Fin n) k) (H : Subgroup Γ) (κ : Fin n → ↥H →* kˣ) : Prop :=
  ∃ g : GL (Fin n) k, ∀ s : ↥H, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) k) i j = 0) ∧
    ∀ i, (g * r s * g⁻¹ : GL (Fin n) k) i i = (κ i s : k)

end Rep

section Level

variable (F : Type) [Field F] [NumberField F]

def Ohat : Subring (Af F) := ⨅ w : HeightOneSpectrum (𝓞 F), (w.adicCompletionIntegers F).toSubring.comap (pLoc F w)

def KLev (n M : ℕ) : Subgroup (GL (Fin n) (Af F)) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat F))}))).ker.map
    (Matrix.GeneralLinearGroup.map (Ohat F).subtype)


variable {F} in
def HasFixed {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (U : Subgroup Γ) : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ u ∈ U, ρ u v = v

end Level

section Gal

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}


omit [NumberField F] in
def KillsMu (M : ℕ) {C : Type} [Monoid C] (χ : G F Ω →* C) : Prop :=
  ∀ s : G F Ω, (∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) → χ s = 1

def FrobEig (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂ) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := F) A, r s = 1) ∧
    ∀ σ : G F Ω, IsFrob A (normV w) σ →
      (r σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = (B.map fun b => X - C b).prod

def algSat (n q : ℕ) (B : Multiset ℂˣ) : Multiset ℂ :=
  B.map fun α => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ)

def AttachedSys (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l))
    (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) : Prop :=
  IsSSRep r ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, sat w B ∧ FrobEig ι r w (algSat n (normV w) B)

def AttC [_root_.NumberField.IsTotallyComplex F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n) : Prop :=
  AttachedSys ι r (CG.mk π).HasSat

def IsAutCsd [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π


variable (l) in
def LevelAway (M : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ χ : Fin n → G F Ω →* (Qbar l)ˣ, (∀ i, KillsMu M (χ i)) ∧ IsDiagOn r (Ine (F := F) A) χ


omit [NumberField F] in
def PotCrysAt (r : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (_ : Algebra ℤ_[l] O) (_ : TopologicalSpace O)
    (Bw : LocBridge l F Ω (Dec (F := F) A) O), GlobalTheory.Pst.Induces Bw ∧
      GlobalTheory.Pst.IsPotCrysAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype)


variable (l) in
def LevelAt (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ (χ : Fin n → G F Ω →* (Qbar l)ˣ) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      (∀ i, KillsMu M (χ i)) ∧ IsFlagOn r (Dec (F := F) A) κ ∧
      (∀ i (s : ↥(Dec (F := F) A)), (s : G F Ω) ∈ Ine (F := F) A → κ i s = cycBar F Ω l s ^ m i * χ i s) ∧
      ((∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ∨ PotCrysAt r A)


variable (l) in
structure Level (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  away : LevelAway l M r
  above : LevelAt l M m r


omit [NumberField F] in
variable (F) in
def decJ (j : Ω →+* Om l) : Subgroup (G F Ω × GQ l) where
  carrier := {x | ∀ y : Ω, x.2 (j y) = j (x.1 y)}
  one_mem' _ := rfl
  mul_mem' {x x'} hx hx' y := by
    change x.2 (x'.2 (j y)) = j (x.1 (x'.1 y))
    rw [hx' y, hx]
  inv_mem' {x} hx y := by
    change x.2.symm (j y) = j (x.1.symm y)
    rw [AlgEquiv.symm_apply_eq, hx]
    simp

variable {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]


variable (l) in
structure IsBK (ρ : Representation C (G F Ω) V) (c : G F Ω → V) : Prop where
  away : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ x : V, ∀ s ∈ Ine (F := F) A, c s = ρ s x - x
  above : ∀ τ : F →+* Om l, ∃ j : Ω →+* Om l, j.comp (algebraMap F Ω) = τ ∧
    (fun x : ↥(decJ F j) => c x.1.1) ∈ Loc.finiteCocycles ((MonoidHom.snd _ _).comp (decJ F j).subtype)
      (ρ.comp ((MonoidHom.fst _ _).comp (decJ F j).subtype))


variable (l) in
def BlochKatoSelmerVanishes (ρ : Representation C (G F Ω) V) : Prop := ∀ c ∈ Z1 ρ, IsBK l ρ c → c ∈ ReciprocityTheory.Gal.B1 ρ

end Gal

end UpperTheory.V.Af
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Fb

attribute [local instance 100] LieRing.ofAssociativeRing

variable (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ)

def ofCusp : cuspForms E a →ₗ[ℂ] TR.Sm E a := Submodule.inclusion cuspForms_le_Sm

variable {E a}

theorem ofCusp_injective : Function.Injective (ofCusp E a) := Submodule.inclusion_injective _

theorem isCuspForm_ofCusp (ψ : cuspForms E a) : TR.IsCuspForm (ofCusp E a ψ) := (isCuspForm_iff _).2 ψ.2

theorem mem_range_ofCusp {φ : TR.Sm E a} : φ ∈ LinearMap.range (ofCusp E a) ↔ TR.IsCuspForm φ :=
  ⟨fun ⟨ψ, h⟩ => h ▸ isCuspForm_ofCusp ψ, fun h => ⟨⟨φ.1, (isCuspForm_iff φ).1 h⟩, rfl⟩⟩

theorem ofCusp_uAction (u : UEnv E a) (ψ : cuspForms E a) :
    ofCusp E a (uActionCusp E a u ψ) = uTR E a u (ofCusp E a ψ) := rfl

theorem ofCusp_ρ (X : TR.Lie E a) (ψ : cuspForms E a) :
    ofCusp E a ((gkModuleCusp E a).ρ (lieEq E a X) ψ) = TR.act (.lie X) (ofCusp E a ψ) := by
  rw [gkModuleCusp_ρ_apply, ofCusp_uAction, uTR_ι]
  rfl

theorem ofCusp_σ (k : TR.Kinf E a) (ψ : cuspForms E a) :
    ofCusp E a ((gkModuleCusp E a).σ (cptEq E a k) ψ) = TR.act (.cpt k) (ofCusp E a ψ) :=
  Subtype.ext (funext fun g => congrArg (fun x => ψ.1 (g * x)) (infEmb_cptEq k))

theorem ofCusp_τ (k : GL (Fin a) (Af E)) (ψ : cuspForms E a) :
    ofCusp E a (finRepCusp E a k ψ) = TR.act (.fin k) (ofCusp E a ψ) :=
  Subtype.ext (funext fun g => congrArg (fun f : GL (Fin a) (Af E) →* GA E a => ψ.1 (g * f k)) finEmb_eq)



omit [IsTotallyReal E] in
structure Stab (U : Submodule ℂ (cuspForms E a)) : Prop where
  ρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp E a).ρ X φ ∈ U
  σ : ∀ k, ∀ φ ∈ U, (gkModuleCusp E a).σ k φ ∈ U
  τ : ∀ g, ∀ φ ∈ U, finRepCusp E a g φ ∈ U

omit [IsTotallyReal E] in
theorem stab_central : Stab (centralCuspForms E a) :=
  ⟨fun X _ h => ρ_mem_centralCuspForms X h, fun k _ h => σ_mem_centralCuspForms k h,
    fun g _ h => finRepCusp_mem_centralCuspForms g h⟩

theorem Stab.map {U : Submodule ℂ (cuspForms E a)} (h : Stab U) : TR.IsStable (U.map (ofCusp E a)) := by
  rintro o _ ⟨ψ, hψ, rfl⟩
  cases o with
  | fin k => exact ⟨_, h.τ k ψ hψ, ofCusp_τ k ψ⟩
  | cpt k => exact ⟨_, h.σ _ ψ hψ, ofCusp_σ k ψ⟩
  | lie X => exact ⟨_, h.ρ _ ψ hψ, ofCusp_ρ X ψ⟩

theorem stab_comap {V : Submodule ℂ (TR.Sm E a)} (h : TR.IsStable V) : Stab (V.comap (ofCusp E a)) := by
  refine ⟨fun X ψ hψ => ?_, fun k ψ hψ => ?_, fun k ψ hψ => ?_⟩
  · obtain ⟨X, rfl⟩ := (lieEq E a).surjective X
    rw [Submodule.mem_comap, ofCusp_ρ]
    exact h _ _ hψ
  · obtain ⟨k, rfl⟩ := (cptEq E a).surjective k
    rw [Submodule.mem_comap, ofCusp_σ]
    exact h _ _ hψ
  · rw [Submodule.mem_comap, ofCusp_τ]
    exact h _ _ hψ


omit [IsTotallyReal E] in
theorem Stab.isIrreducible_iff {U : Submodule ℂ (cuspForms E a)} (h : Stab U) :
    (cuspSubmodule E a U h.ρ h.σ h.τ).IsIrreducible ↔ U ≠ ⊥ ∧ ∀ W ≤ U, Stab W → W = ⊥ ∨ W = U := by
  refine ⟨fun hi => ?_, fun hi => isIrreducible_cuspSubmodule_of U h.ρ h.σ h.τ hi.1
    fun W hW h1 h2 h3 => hi.2 W hW ⟨h1, h2, h3⟩⟩
  set M := cuspSubmodule E a U h.ρ h.σ h.τ
  have hs : IsSimpleOrder (Subrepresentation M.fullRep) := hi
  refine ⟨fun e => ?_, fun W hW hst => ?_⟩
  · have : Subsingleton U := by rw [e]; infer_instance
    exact bot_ne_top (α := Subrepresentation M.fullRep)
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  · have h1 : ∀ (w : FreeMonoid ((isExpLieAlgebra E a).lieSubalgebra ⊕ archCompact E a)) (y : U),
        y.1 ∈ W → (M.gk.rep w y).1 ∈ W := fun w => by
      induction w using FreeMonoid.inductionOn' with
      | one => intro y hy; rwa [map_one]
      | of_mul x w ih =>
        intro y hy
        rw [map_mul, Module.End.mul_apply]
        rcases x with X | k
        · exact hst.ρ X _ (ih y hy)
        · exact hst.σ k _ (ih y hy)
    let Y : Subrepresentation M.fullRep := ⟨W.comap U.subtype, fun p y hy => h1 p.1 _ (hst.τ p.2 _ hy)⟩
    have e : (W.comap U.subtype).map U.subtype = W := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hW]
    rcases eq_bot_or_eq_top Y with h0 | h0
    · left
      rw [← e, show W.comap U.subtype = ⊥ from congrArg Subrepresentation.toSubmodule h0, Submodule.map_bot]
    · right
      rw [← e, show W.comap U.subtype = ⊤ from congrArg Subrepresentation.toSubmodule h0, Submodule.map_subtype_top]

def carrier (π : TR.CuspSub E a) : Submodule ℂ (cuspForms E a) := π.V.comap (ofCusp E a)

theorem mem_carrier {π : TR.CuspSub E a} {ψ : cuspForms E a} : ψ ∈ carrier π ↔ ofCusp E a ψ ∈ π.V := Iff.rfl

theorem map_carrier (π : TR.CuspSub E a) : (carrier π).map (ofCusp E a) = π.V :=
  Submodule.map_comap_eq_self fun φ h => mem_range_ofCusp.2 (π.cusp φ h)

theorem stab_carrier (π : TR.CuspSub E a) : Stab (carrier π) := stab_comap π.stable

def ofIrr (U : Submodule ℂ (cuspForms E a)) (h : Stab U) (hi : (cuspSubmodule E a U h.ρ h.σ h.τ).IsIrreducible) :
    TR.CuspSub E a where
  V := U.map (ofCusp E a)
  cusp := by rintro _ ⟨ψ, -, rfl⟩; exact isCuspForm_ofCusp ψ
  stable := h.map
  ne_bot e := (h.isIrreducible_iff.1 hi).1
    (Submodule.map_injective_of_injective ofCusp_injective (e.trans (Submodule.map_bot _).symm))
  irred W hW hst := by
    have e : (W.comap (ofCusp E a)).map (ofCusp E a) = W :=
      Submodule.map_comap_eq_self (hW.trans LinearMap.map_le_range)
    refine ((h.isIrreducible_iff.1 hi).2 _ ((Submodule.comap_mono hW).trans
      (Submodule.comap_map_eq_of_injective ofCusp_injective U).le) (stab_comap hst)).imp (fun e' => ?_) fun e' => ?_
    · rw [← e, e', Submodule.map_bot]
    · rw [← e, e']

theorem carrier_ofIrr (U : Submodule ℂ (cuspForms E a)) (h : Stab U) (hi) : carrier (ofIrr U h hi) = U :=
  Submodule.comap_map_eq_of_injective ofCusp_injective U

theorem centralZ_eq :
    UnitaryAdmissible.centralZ E a = UnitaryAdmissible.centralExp E a • lieEq E a (TR.oneL E a) :=
  Subtype.ext (by rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← lieEq_oneL]; rfl)

theorem mem_centralCuspForms_of {ψ : cuspForms E a} (h : TR.lie E a (TR.oneL E a) (ofCusp E a ψ) = 0) :
    ψ ∈ centralCuspForms E a := fun s x => by
  have h1 : (gkModuleCusp E a).ρ (lieEq E a (TR.oneL E a)) ψ = 0 :=
    ofCusp_injective ((ofCusp_ρ _ _).trans (h.trans (map_zero _).symm))
  have h2 : lieActionCusp E a (UnitaryAdmissible.centralZ E a) ψ = (0 : ℂ) • ψ := by
    rw [centralZ_eq, map_smul, zero_smul, LinearMap.smul_apply]
    exact (congrArg _ h1).trans (smul_zero _)
  rw [Reduction.centralSection_mul_comm, UnitaryAdmissible.apply_mul_centralSection h2 x s]
  simp

theorem carrier_le_central (π : TR.CuspSub E a) (h : ∀ φ ∈ π.V, TR.lie E a (TR.oneL E a) φ = 0) :
    carrier π ≤ centralCuspForms E a := fun _ hψ => mem_centralCuspForms_of (h _ hψ)

end UpperTheory.V.Fb
end
end
