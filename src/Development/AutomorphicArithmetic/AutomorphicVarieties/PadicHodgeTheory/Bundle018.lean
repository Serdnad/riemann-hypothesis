module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle363
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle484
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle003
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle008
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GroupCohomology.Bundle006
public import ReciprocityTheory.GroupCohomology.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import ReciprocityTheory.GroupCohomology.Bundle002

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section Generic

variable {G Q B : Type} [Group G] [Field Q] [AddCommGroup B] [Module Q B] (a : G → B →ₗ[Q] B)

private noncomputable def invT {V : Type} [AddCommGroup V] [Module Q V] (ρ : Representation Q G V) :
    Submodule Q (V ⊗[Q] B) :=
  ⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g) (a g) - LinearMap.id)

private theorem mem_invT {V : Type} [AddCommGroup V] [Module Q V] (ρ : Representation Q G V) (x : V ⊗[Q] B) :
    x ∈ invT a ρ ↔ ∀ g, AlgebraTensorModule.map (ρ g) (a g) x = x := by
  simp only [invT, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

private theorem rT_comm {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (y : V ⊗[Q] B) :
    f.rTensor B (AlgebraTensorModule.map (ρ g) (a g) y) =
      AlgebraTensorModule.map (ρ' g) (a g) (f.rTensor B y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hf g]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private noncomputable def invMap {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) : invT a ρ →ₗ[Q] invT a ρ' :=
  (f.rTensor B).restrict fun x hx => (mem_invT a ρ' _).2 fun g => by
    rw [← rT_comm a hf, (mem_invT a ρ _).1 hx]

private theorem of_exact {V₀ V V' : Type} [AddCommGroup V₀] [Module Q V₀] [AddCommGroup V] [Module Q V]
    [AddCommGroup V'] [Module Q V'] [FiniteDimensional Q V]
    {ρ₀ : Representation Q G V₀} {ρ : Representation Q G V} {ρ' : Representation Q G V'}
    {i : V₀ →ₗ[Q] V} {p : V →ₗ[Q] V'}
    (hi : ∀ g x, i (ρ₀ g x) = ρ g (i x)) (hp : ∀ g x, p (ρ g x) = ρ' g (p x))
    (h1 : Function.Injective i) (h2 : Function.Exact i p) (h3 : Function.Surjective p) (n : ℕ)
    [Module.Finite Q (invT a ρ)] [Module.Finite Q (invT a ρ')]
    (c₀ : finrank Q (invT a ρ₀) ≤ n * finrank Q V₀) (c' : finrank Q (invT a ρ') ≤ n * finrank Q V')
    (h : finrank Q (invT a ρ) = n * finrank Q V) :
    finrank Q (invT a ρ₀) = n * finrank Q V₀ ∧ finrank Q (invT a ρ') = n * finrank Q V' := by
  have hex : Function.Exact (i.rTensor B) (p.rTensor B) := rTensor_exact B h2 h3
  have hinj : Function.Injective (i.rTensor B) := Module.Flat.rTensor_preserves_injective_linearMap _ h1
  have e1 : Function.Injective (invMap a hi) := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  have e2 : Function.Exact (invMap a hi) (invMap a hp) := by
    refine fun x => ⟨fun h => ?_, ?_⟩
    · obtain ⟨y, hy⟩ := (hex x).1 (congrArg Subtype.val h)
      refine ⟨⟨y, (mem_invT a ρ₀ y).2 fun g => hinj ?_⟩, Subtype.ext hy⟩
      rw [rT_comm a hi, hy]
      exact (mem_invT a ρ _).1 x.2 g
    · rintro ⟨y, rfl⟩
      exact Subtype.ext ((hex _).2 ⟨_, rfl⟩)
  have h4 := (invMap a hp).finrank_range_add_finrank_ker
  rw [e2.linearMap_ker_eq, LinearMap.finrank_range_of_inj e1] at h4
  have h5 := p.finrank_range_add_finrank_ker
  rw [h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1, LinearMap.range_eq_top.2 h3, finrank_top] at h5
  have h6 := (LinearMap.range (invMap a hp)).finrank_le
  rw [← h5, mul_add] at h
  exact ⟨by omega, by omega⟩

private theorem sub_quot (n : ℕ)
    (hb : ∀ (W : Type) [AddCommGroup W] [Module Q W] [FiniteDimensional Q W] (σ : Representation Q G W),
      Module.Finite Q (invT a σ) ∧ finrank Q (invT a σ) ≤ n * finrank Q W)
    {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    [FiniteDimensional Q V] [FiniteDimensional Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    (Function.Injective f → finrank Q (invT a ρ') = n * finrank Q V' → finrank Q (invT a ρ) = n * finrank Q V) ∧
    (Function.Surjective f → finrank Q (invT a ρ) = n * finrank Q V →
      finrank Q (invT a ρ') = n * finrank Q V') := by
  have := (hb V ρ).1
  have := (hb V' ρ').1
  refine ⟨fun hi h => ?_, fun hs h => ?_⟩
  · have hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ' g) := by
      rintro g _ ⟨v, rfl⟩
      exact ⟨ρ g v, hf g v⟩
    have := (hb _ (ρ'.quotient (LinearMap.range f) hst)).1
    exact (of_exact a (ρ' := ρ'.quotient (LinearMap.range f) hst) hf (fun g v => rfl) hi
      (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective n (hb V ρ).2 (hb _ _).2 h).1
  · have hst : ∀ g, LinearMap.ker f ≤ (LinearMap.ker f).comap (ρ g) := by
      intro g v hv
      rw [Submodule.mem_comap, LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hv, map_zero]
    exact (of_exact a (ρ₀ := ρ.subrepresentation (LinearMap.ker f) hst) (fun g v => rfl) hf
      (LinearMap.ker f).injective_subtype (LinearMap.exact_subtype_ker_map f) hs n (hb _ _).2 (hb V' ρ').2 h).2

end Generic

private theorem bound {G H Q K B : Type} [Group G] [Group H] [Field Q] [Field K] [Algebra Q K] [CommRing B]
    [IsDomain B] [Algebra Q B] [Algebra K B] [IsScalarTower Q K B] [FiniteDimensional Q K]
    (e : G ≃* H) (act : H →* (B ≃ₐ[K] B))
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (a : G → B →ₗ[Q] B) (ha : ∀ g b, a g b = act (e g) b)
    (W : Type) [AddCommGroup W] [Module Q W] [FiniteDimensional Q W] (σ : Representation Q G W) :
    Module.Finite Q (invT a σ) ∧ finrank Q (invT a σ) ≤ finrank Q K * finrank Q W := by
  have h := GlobalTheory.Per.FontaineBound.finite_finrank_le_base (Qp := Q) (act.comp e.toMonoidHom)
    (fun b b' hb h => hreg b b' hb fun g => by simpa using h (e.symm g)) σ
  have : a = fun g => ((act.comp e.toMonoidHom g).toAlgHom.toLinearMap).restrictScalars Q :=
    funext fun g => LinearMap.ext fun b => ha g b
  subst this
  exact h

theorem UpperTheory.V.Loc.isCrys_isDR_sub_quot :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {A' : Type} [CommRing A'] [Algebra ℚ_[l] A'] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A G V) (ρ' : Representation A' G V'), ContAction ρ → ContAction ρ' → ∀ f : V →ₗ[ℚ_[l]] V', (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → (IsCr φ ρ' → IsCr φ ρ) ∧ (IsDr φ ρ' → IsDr φ ρ)) ∧ (Function.Surjective f → (IsCr φ ρ → IsCr φ ρ') ∧ (IsDr φ ρ → IsDr φ ρ')) := by
  intro l _ G _ _ _ φ hφ A _ _ A' _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ' _ _ f hf
  obtain ⟨K, e, -, -, he, -, hK, hK0⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  have hF := GlobalTheory.Per.FontaineBound.isField_of_tied T
  have := GlobalTheory.Per.FontaineBound.isDomain_cris (PD := (PP l).PD K) hF
  have := hF.isDomain
  have := ((PP l).PD K).finK₀
  have := K.2
  have hφe : ∀ g, φ g = (e g : GQ l) := fun g => by rw [← he]; rfl
  have hc := sub_quot (fun g => ((PP l).actQ (φ g)).toLinearMap) _
    (bound e ((PP l).PD K).actB (fun b b' hb h =>
      GlobalTheory.Per.FracInv.tied_frac_invariant l (PP l) (AIP l) T K b' b hb fun g hg => by
        have h1 := h ⟨g, hg⟩
        rw [(PP l).PD_actB, (PP l).PD_actB] at h1
        rw [mul_comm, h1, mul_comm]) _ fun g b => by rw [(PP l).PD_actB, hφe]; rfl)
    (ρ := resCoef ℚ_[l] ρ) (ρ' := resCoef ℚ_[l] ρ') (f := f) hf
  have hd := sub_quot (fun g => ((PP l).actQdR (φ g)).toLinearMap) _
    (bound e ((PP l).PD K).actdR (GlobalTheory.Per.FontaineBound.frac_dR ((PP l).PD K) hF) _
      fun g b => by rw [(PP l).PD_actdR, hφe]; rfl)
    (ρ := resCoef ℚ_[l] ρ) (ρ' := resCoef ℚ_[l] ρ') (f := f) hf
  unfold IsCr IsDr
  rw [hK, hK0]
  exact ⟨fun h => ⟨hc.1 h, hd.1 h⟩, fun h => ⟨hc.2 h, hd.2 h⟩⟩
end

section

noncomputable section

namespace UpperTheory.V.Loc

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing

structure Dat3 (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] where
  η : GQ l →* ℤˣ
  Ψ : GQ l →* Oˣ
  τ : GQ l →* Oˣ
  e : ℕ
  Kv : FinExt l
  odd : l ≠ 2
  e_pos : 1 ≤ e
  η_ker : ∀ g, η g = 1 ↔ g ∈ GK Kv
  η_unr : ∀ g ∈ Iq l, η g = 1
  τ_open : IsOpen (τ.ker : Set (GQ l))
  Ψ_cont : AdicCont (maximalIdeal O) fun g => (Ψ g : O)
  Ψ_I : ∀ g ∈ Iq l, Ψ g = cycA l l O g ^ e * τ g

def hodge0 (e : ℕ) (i : ℤ) : ℕ := if i = -(e : ℤ) ∨ i = 0 ∨ i = e then 1 else 0

namespace Dat3

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O)

def HL : Subgroup (GQ l) := D.η.ker ⊓ D.τ.ker

def rz (A : Type) [CommRing A] [Algebra O A] : GQ l →* GG (m := 3) (R := A) :=
  (GG.map (algebraMap O A)).comp (r0 D.η D.Ψ)

section Types

variable {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B]

def IsType (r : GQ l →* GG (m := 3) (R := B)) : Prop :=
  ∃ ρ : ↥(GK D.Kv) →* GL (Fin 3) B, (∀ g, ρ g = (r g).left) ∧
    PotCrysType D.Kv (colRep ρ) 3 (hodge0 D.e)
      fun γ => algebraMap O B ((D.τ γ : O) + 1 + (((D.τ γ)⁻¹ : Oˣ) : O))

def IsLCr (r : GQ l →* GG (m := 3) (R := B)) : Prop :=
  ∃ ρ : ↥D.HL →* GL (Fin 3) B, (∀ g, ρ g = (r g).left) ∧ IsCr D.HL.subtype (colRep ρ)

variable {E : Type} [CommRing E] [Algebra O E] (π : B →+* E)

structure InDcrAt (r₁ : GQ l →* GG (m := 3) (R := E))
    (r : GQ l →* GG (m := 3) (R := B)) : Prop where
  mult : HasMult D.η r
  red : (GG.map π).comp r = r₁
  cont : ∀ a b, QCont l fun g => (r g).mat a b
  cr : D.IsLCr r

abbrev InDcr (r : GQ l →* GG (m := 3) (R := B)) : Prop := D.InDcrAt π (D.rz E) r

structure InDtri (r : GQ l →* GG (m := 3) (R := B)) : Prop extends D.InDcrAt π (D.rz E) r where
  tri : ∀ g a b, wt a b < 0 → (r g).mat a b = 0

def InDord (r : GQ l →* GG (m := 3) (R := B)) : Prop :=
  ∃ (u : GQ l →* GG (m := 3) (R := B)) (n : GL (Fin 3) B), D.InDtri π u ∧ CongOne (RingHom.ker π) n ∧
    (∀ a b, 0 ≤ wt a b → ((n : Matrix (Fin 3) (Fin 3) B) - 1) a b = 0) ∧ r = conjBy n u

end Types

abbrev Univ : Type 1 := U3.Univ (GCond.noCondition O D.η D.Ψ)

section Ord

open Polynomial

def IsInertiaInfiniteCyclotomic (s : GQ l) : Prop := s ∈ D.HL ∧ s ∈ Iq l ∧ ¬ IsOfFinOrder (cyc l l s)

def IsFr (σ : GQ l) : Prop :=
  (∃ h : σ ∈ D.HL, ((Iq l).comap D.HL.subtype ⊔ Subgroup.zpowers (⟨σ, h⟩ : ↥D.HL)).topologicalClosure = ⊤) ∧
    ∃ (σ₀ : GQ l) (m : ℕ), IsFrob σ₀ ∧ 1 ≤ m ∧ (σ₀ ^ m)⁻¹ * σ ∈ Iq l

def s0 : GQ l := Classical.epsilon (IsInertiaInfiniteCyclotomic D)

def fr : GQ l := Classical.epsilon (IsFr D)

def cc (a : Fin 3) : O :=
  (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (s0 D) - UpperTheory.V.UnitaryThreeInertia.psi D.Ψ (a + 1) (s0 D)) *
    (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (s0 D) - UpperTheory.V.UnitaryThreeInertia.psi D.Ψ (a + 2) (s0 D))

section Eq

variable {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C))

def sh (a : Fin 3) (s : GQ l) : Matrix (Fin 3) (Fin 3) C :=
  (r s).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))

def ordIdeal : Ideal C :=
  Ideal.span ({x | ∃ s ∈ D.HL ⊓ Iq l, ∃ i : ℕ, x = ((r s).mat.charpoly -
      ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i} ∪
    {x | ∃ s : Fin 3 → GQ l, (∀ a, s a ∈ D.HL ⊓ Iq l) ∧ ∃ i j,
      x = (sh D r 0 (s 0) * sh D r 1 (s 1) * sh D r 2 (s 2)) i j})

def tr (a : Fin 3) : C := (sh D r (a + 1) (s0 D) * sh D r (a + 2) (s0 D) * (r (fr D)).mat).trace

def dd (a : Fin 3) : C :=
  algebraMap O C (cc D (a + 1)) * tr D r a - algebraMap O C ((cycA l l O (fr D) : Oˣ) * cc D a) * tr D r (a + 1)

def del : C := (l : C) * dd D r 0 * dd D r 1

end Eq

end Ord

variable (U : D.Univ)

def IY : Ideal U.R where
  carrier := {a | ∃ n : ℕ, del D U.r.hom ^ n * a ∈ ordIdeal D U.r.hom}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have e : del D U.r.hom ^ (m + n) * (a + b) = del D U.r.hom ^ n * (del D U.r.hom ^ m * a) +
        del D U.r.hom ^ m * (del D U.r.hom ^ n * b) := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hn)
  smul_mem' := by
    rintro c a ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ _ hn

def Icr : Ideal U.R := (IY D U).radical

def primesAt0 : Set (Ideal U.R) :=
  {P | P ∈ (D.Icr U).minimalPrimes ∧ ∀ x : U.R →ₐ[O] O, push x U.r.hom = r0 D.η D.Ψ → P ≤ RingHom.ker x}

def It : Ideal U.R := sInf (D.primesAt0 U)

abbrev Rt : Type := U.R ⧸ D.It U

def On {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) : Prop :=
  ∃ f : U.R →ₐ[O] C, push f U.r.hom = r ∧ D.It U ≤ RingHom.ker f

def PtsCr (J : Ideal U.R) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : U.R →ₐ[O] B),
    J ≤ RingHom.ker f → D.IsLCr (push f U.r.hom)

def CrPts (J : Ideal U.R) : Prop :=
  ∀ (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
    [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ f : U.R →ₐ[O] B,
    D.InDcr (π : B →+* E) (push f U.r.hom) → J ≤ RingHom.ker f

end Dat3

structure IsCompl {O R E σ : Type} [CommRing O] [CommRing R] [Algebra O R] [Field E] [Algebra O E]
    (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries σ E) : Prop where
  ker : RingHom.ker φ = I
  const : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)
  dense : ∀ (N : ℕ) (f : MvPowerSeries σ E), ∃ (a : R) (c : O), c ≠ 0 ∧
    c • f - φ a ∈ maximalIdeal (MvPowerSeries σ E) ^ N
  inj : ∀ (N : ℕ) (a : R), φ a ∈ maximalIdeal (MvPowerSeries σ E) ^ N →
    ∃ c : O, c ≠ 0 ∧ c • a ∈ RingHom.ker x ^ N ⊔ I

def DualDef {G E : Type} [Group G] [CommRing E] (r : G →* GG (m := 3) (R := E))
    (γ : G → Matrix (Fin 3) (Fin 3) E) (r' : G →* GG (m := 3) (R := DualNumber E)) : Prop :=
  ∀ g, (r' g).right = (r g).right ∧ ∀ a b, (r' g).mat a b = ⟨(r g).mat a b, (γ g * (r g).mat) a b⟩

end UpperTheory.V.Loc
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.rank_cohomology_rational_eq_rank_lattice :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] G V), ContAction ρ → ∀ {n : ℕ} (ρT : Representation ℤ_[l] G (Fin n → ℤ_[l])) (j : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] V), ContAction ρT → IsOpenEmbedding j → (∀ g x, j (ρT g x) = ρ g (j x)) → (∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j) → Module.rank ℚ_[l] ↥(H0 ρ) = Module.rank ℤ_[l] ↥(H0 ρT) ∧ Module.rank ℚ_[l] (H1 ρ) = Module.rank ℤ_[l] (H1 ρT) ∧ Module.rank ℚ_[l] (H2 ρ) = Module.rank ℤ_[l] (H2 ρT) := by
  intro l _ G _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ n ρT j hT hj he hm
  haveI : ContinuousConstSMul ℤ_[l] V := ⟨fun c => by
    have h : (fun x : V => c • x) = fun x => (algebraMap ℤ_[l] ℚ_[l] c) • x :=
      funext fun x => (algebraMap_smul ℚ_[l] c x).symm
    rw [h]
    exact continuous_const_smul _⟩
  let L : ReciprocityTheory.Coh.TRep ℤ_[l] G := { V := Fin n → ℤ_[l], rho := ρT, cont := hT }
  let U : ReciprocityTheory.Coh.TRep ℤ_[l] G := { V := V, rho := resCoef ℤ_[l] ρ, cont := hρ }
  let P : ReciprocityTheory.Coh.Pair L U := ⟨MonoidHom.id G, j, continuous_id, hj.continuous, he⟩
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl' : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hloc := ReciprocityTheory.Coh.localise_holds ℤ_[l] G (l : ℤ_[l]) L U P rfl hj
    ⟨Homeomorph.smulOfNeZero (α := V) (l : ℚ_[l]) hl, fun (v : V) => by
      show (l : ℚ_[l]) • v = (l : ℤ_[l]) • v
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]⟩ hm
  have hp : Submonoid.powers (l : ℤ_[l]) ≤ nonZeroDivisors ℤ_[l] :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hl'
  have hr : ∀ k, Module.rank ℤ_[l] (U.H k) = Module.rank ℤ_[l] (L.H k) := fun k =>
    haveI := hloc k
    IsLocalizedModule.rank_eq (Submonoid.powers (l : ℤ_[l])) hp (P.hom.H k)
  obtain ⟨a₀, a₁, a₂, -⟩ := ReciprocityTheory.Coh.exists_isLow L
  obtain ⟨b₀, b₁, b₂, -⟩ := ReciprocityTheory.Coh.exists_isLow U
  obtain ⟨⟨c₀⟩, ⟨c₁⟩, ⟨c₂⟩, -⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℤ_[l] ρ
  refine ⟨?_, ?_, ?_⟩
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₀.trans c₀).rank_eq.symm.trans ((hr 0).trans a₀.rank_eq)
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₁.trans c₁).rank_eq.symm.trans ((hr 1).trans a₁.rank_eq)
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₂.trans c₂).rank_eq.symm.trans ((hr 2).trans a₂.rank_eq)
end
