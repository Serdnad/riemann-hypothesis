module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct

section Ext

variable {G : Type} [Group G] {LL : Type} [Field LL] {V W : Type} [AddCommGroup V] [Module LL V]
  [AddCommGroup W] [Module LL W]

def IsExt (ρ : Representation LL G V) (ρ' : Representation LL G W) (i : V →ₗ[LL] W) (p : W →ₗ[LL] LL) : Prop :=
  Function.Injective i ∧ Function.Exact i p ∧ Function.Surjective p ∧
    (∀ g x, i (ρ g x) = ρ' g (i x)) ∧ ∀ g y, p (ρ' g y) = p y

def IsCocycleOf (ρ' : Representation LL G W) (i : V →ₗ[LL] W) (p : W →ₗ[LL] LL) (c : G → V) : Prop :=
  ∃ e : W, p e = 1 ∧ ∀ g, ρ' g e = e + i (c g)

variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def extRep (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ)) : Representation LL G (V × LL) where
  toFun g := ((ρ g).coprod (LinearMap.toSpanSingleton LL V ((c : G → V) g))).prod (LinearMap.snd LL V LL)
  map_one' := by
    have h : (c : G → V) 1 = 0 := by simpa using c.2.2 1 1
    refine LinearMap.ext fun x => ?_
    simp [h]
  map_mul' g k := by
    refine LinearMap.ext fun x => ?_
    simp [c.2.2 g k]
    abel

theorem extRep_isExt (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ)) :
    IsExt ρ (extRep ρ c) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL) ∧
      IsCocycleOf (extRep ρ c) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL) (c : G → V) := by
  refine ⟨⟨LinearMap.inl_injective, Function.Exact.inl_snd, LinearMap.snd_surjective, fun g x => ?_,
    fun _ _ => rfl⟩, (0, 1), rfl, fun g => ?_⟩
  · simp [extRep]
  · simp [extRep]

end Ext

section Per

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

def H1fSubmodule {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V) :
    Submodule LL (H1V ρ) :=
  ((finiteCocycles PD ρ).comap (continuousCocycles ρ).subtype).map (Submodule.mkQ _)

theorem mk_mem_H1fSub {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V)
    (c : ↥(continuousCocycles ρ)) : (Submodule.Quotient.mk c : H1V ρ) ∈ H1fSubmodule PD ρ ↔ (c : G → V) ∈ finiteCocycles PD ρ := by
  refine ⟨?_, fun h => ⟨c, h, rfl⟩⟩
  rintro ⟨c', ⟨-, x, hx⟩, h⟩
  obtain ⟨b, hb⟩ := (Submodule.Quotient.eq _).mp h
  refine ⟨c.2, x - b ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  have h1 : ρ g b - b = (c' : G → V) g - (c : G → V) g := congrFun hb g
  have h2 : (c : G → V) g = (c' : G → V) g - (ρ g b - b) := by rw [h1]; abel
  have h3 : actVB PD ρ g (b ⊗ₜ[Qp] (1 : B)) = ρ g b ⊗ₜ[Qp] (1 : B) := by simp [actVB]
  have h4 : (c' : G → V) g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x := hx g
  rw [h2, sub_tmul, sub_tmul, h4, map_sub, h3]
  abel

def ExtCrysAt [TopologicalSpace LL] {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [IsModuleTopology LL V]
    (ρ : Representation LL G V), (∀ x, Continuous fun g => ρ g x) → IsCrys PD ρ →
  ∀ (W : Type) [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    (ρ' : Representation LL G W) (i : V →ₗ[LL] W) (p : W →ₗ[LL] LL), IsExt ρ ρ' i p →
  ∀ c : ↥(continuousCocycles ρ), IsCocycleOf ρ' i p (c : G → V) →
    (IsCrys PD ρ' ↔ (Submodule.Quotient.mk c : H1V ρ) ∈ H1fSubmodule PD ρ) ∧
    (IsCrys PD ρ' → ∀ (j : ZMod n) (U : Multiset ℤ),
      AdmLoc.HasJumps PD ρ (emb j) U → AdmLoc.HasJumps PD ρ' (emb j) (U + {0}))

end Per

def ExtCrys {l : ℕ} [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ (K LL : Loc.FinExt l) (n : ℕ) (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (lam : ↥(Loc.OL LL)),
    AdmLoc.Standing P K LL emb lam → ExtCrysAt (P.PD K) emb

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1 H1)

section Triv

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O)
    (X : Type) [AddCommGroup X] [Module O X]

theorem twCoef_chi_one (g : G) (m : O ⊗[O] X) : twCoef (Γ.Wchi 1) Γ.χ₁ X g m = m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [coefRep_tmul, twistRep_apply]
    congr 1
    change ((Γ.χ₁⁻¹ g : Oˣ) : O) • ((Γ.chi 1 g : O) • a) = a
    rw [GalData.chi_one, smul_smul]
    simp
  | add a b ha hb => rw [map_add (f := _), ha, hb]

def homModInertia (I : Subgroup G) : Set (H1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤) :=
  {c | ∃ z : ↥(Z1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤), Submodule.Quotient.mk z = c ∧
    ∀ g ∈ I, (z : G → O ⊗[O] X) g = 0}

theorem cocycle_add (z : ↥(Z1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤)) (g h : G) :
    (z : G → O ⊗[O] X) (g * h) = (z : G → O ⊗[O] X) g + (z : G → O ⊗[O] X) h := by
  rw [cocycle_mul z g h, twCoef_chi_one]

theorem homModInertia_eq_unr (I : Subgroup G) :
    homModInertia Γ X I = (unr (twCoef (Γ.Wchi 1) Γ.χ₁ X) I : Set _) := by
  ext c
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  constructor
  · rintro ⟨z', hz, h⟩
    rw [← hz]
    exact (mk_mem_unr_of_trivial (twCoef_chi_one Γ X) I z').mpr h
  · intro h
    exact ⟨z, rfl, (mk_mem_unr_of_trivial (twCoef_chi_one Γ X) I z).mp h⟩

end Triv

def AdmChiOneUnramified {l : ℕ} [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ (K LL : Loc.FinExt l) (n r : ℕ) (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : GalData ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)),
    Standing P K LL emb Γ.lam → IsTopGal (P.PD K) emb D Γ → D.T1 l → D.T2 l → D.T3 l →
    ∀ (X : Type) [AddCommGroup X] [Module ↥(Loc.OL LL) X] [Finite X],
      adm (P.PD K) emb Γ D.t D.Ut (Γ.Wchi 1) X = homModInertia Γ X (Loc.IK K)

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses

open Formalism.BasicNotions GlobalTheory.AdmLoc TensorProduct
open ReciprocityTheory.Def (H1)

variable {l : ℕ} [Fact l.Prime]

abbrev Gal (K LL : Loc.FinExt l) : Type 1 := GalData ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)

def Hyp (P : LocPrime l) (K LL : Loc.FinExt l) {n r : ℕ} (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : Gal K LL) : Prop :=
  Standing P K LL emb Γ.lam ∧ IsTopGal (P.PD K) emb D Γ ∧ D.T1 l ∧ D.T2 l ∧ D.T3 l

def admissibleClassesTwistedChar (P : LocPrime l) (K LL : Loc.FinExt l) {n r : ℕ} (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : Gal K LL) (c : ℕ) (X : Type) [AddCommGroup X] [Module ↥(Loc.OL LL) X] :
    Set (H1 (twCoef (Γ.Wchi c) Γ.χ₁ X) ⊤) :=
  adm (P.PD K) emb Γ D.t D.Ut (Γ.Wchi c) X

def Stmt (P : LocPrime l) : Prop :=
  ∀ (K LL : Loc.FinExt l) (n r : ℕ) (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (D : TopData n r)
    (Γ : Gal K LL), Hyp P K LL emb D Γ →
    ∀ c : ℕ, 2 ≤ c → c ≤ D.t →
    ∀ (X : Type) [AddCommGroup X] [Module ↥(Loc.OL LL) X] [Finite X],
      admissibleClassesTwistedChar P K LL emb D Γ c X = {0}

theorem twCoef_Wchi {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O) (c : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] (g : G) (y : O ⊗[O] X) :
    twCoef (Γ.Wchi c) Γ.χ₁ X g y = (((Γ.ε g) ^ (-((c : ℤ) - 1)) : Oˣ) : O) • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), ha, hb, smul_add]
  | tmul a x =>
    rw [coefRep_tmul, twistRep_apply, smul_tmul']
    congr 1
    change ((Γ.χ₁⁻¹ g : Oˣ) : O) • (((Γ.chi c g : Oˣ) : O) • a) = _
    rw [smul_smul, ← Units.val_mul]
    congr 2
    simp [GalData.chi]

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc
open ReciprocityTheory.Def (H2)

section Concl

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n r : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (D : TopData n r) (Γ : GalData G Qp LL O)

abbrev resK : Type := O ⧸ Ideal.span {Γ.lam}

abbrev resRep : Representation O G (TensorProduct O ↥Γ.T₀.L.T (resK Γ)) := twCoef Γ.W₀ Γ.χ₁ (resK Γ)

abbrev HH : Type := H1tw Γ.T₀.L Γ.χ₁

abbrev Hf : Submodule O (HH Γ) := latticeFiniteCohomology PD (twLattice Γ.T₀.L Γ.χ₁⁻¹)

def Concl [NeZero n] : Prop :=
  (resRep Γ).invariants = ⊥ ∧
  Subsingleton (H2 (resRep Γ) ⊤) ∧
  (Module.Free O (HH Γ) ∧ Module.Finite O (HH Γ) ∧ Module.finrank O (HH Γ) = r * n) ∧
  ((∃ C : Submodule O (HH Γ), IsCompl (Hf PD Γ) C) ∧ Module.finrank O ↥(Hf PD Γ) = D.dsum) ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X],
    TensIso Γ.T₀.L Γ.χ₁ X ∧
      adm PD emb Γ D.t D.Ut Γ.W₀ X = (finiteSelmer PD Γ.T₀.L Γ.χ₁ X : Set _)

end Concl

def ErrorExponentStatement {l : ℕ} [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ (K LL : FinExt l) (n r : ℕ) [NeZero n] (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
    Standing P K LL emb Γ.lam → IsTopGal (P.PD K) emb D Γ →
    D.T1 l → D.T2 l → D.T3 l → Concl (P.PD K) emb D Γ

theorem letters_ne_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} {n : ℕ}
    {emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)} {lam : ↥(OL LL)} (h : Standing P K LL emb lam) : n ≠ 0 := by
  have := K.2
  rw [h.2.2.1]
  exact Module.finrank_pos.ne'

end GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct

def cc (l : ℕ) (a : ℤ) : ℚ := ((1 + (l : ℚ)) ^ a - 1) / (-(l : ℚ))

def eigMs (LL : Type) [Field LL] (l : ℕ) (U : Multiset ℤ) (w j j' : ℤ) : Multiset LL :=
  U.bind fun u => (Finset.Ico j j').val.map fun j'' => ((cc l (j'' - (u - w)) : ℚ) : LL)

def DiagWith {F M : Type} [Field F] [AddCommGroup M] [Module F M] (f : M →ₗ[F] M) (S : Multiset F) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) F M) (e : Fin m → F),
    (∀ s, f (b s) = e s • b s) ∧ Finset.univ.val.map e = S

def EigWith {F M : Type} [Field F] [AddCommGroup M] [Module F M] (f : M →ₗ[F] M) (S : Multiset F) : Prop :=
  ∃ _ : Module.Finite F M, f.charpoly = (S.map fun s => Polynomial.X - Polynomial.C s).prod

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def qΔ : LetA O n := W.π₀ + ((PD.p : ℕ) : LetA O n)

def mulD (a : LetA O n) : W.DD T →ₗ[O] W.DD T := Algebra.lsmul O O (W.DD T) a

def NΔl (i : ZMod n) : Submodule O (W.DD T) := W.NΔ T ⊓ (W.Nl T i).restrictScalars O

def qN (i : ZMod n) (j : ℤ) : Submodule O (W.DD T) :=
  ((NΔl W T i).map (mulD W T (qΔ W ^ j.toNat))).comap (mulD W T (qΔ W ^ (-j).toNat))

abbrev qQuot (i : ZMod n) (j j' : ℤ) : Type :=
  ↥(qN W T i j) ⧸ (qN W T i j').submoduleOf (qN W T i j)

def IsNab (g : W.Gam) (a : LetA O n) (i : ZMod n) (j : ℤ) (nb : ↥(qN W T i j) →ₗ[O] ↥(qN W T i j)) : Prop :=
  ∀ x : ↥(qN W T i j),
    (a * W.π₀) • ((nb x : ↥(qN W T i j)) : W.DD T) = W.γD T g (x : W.DD T) - a • (x : W.DD T)

def DiagQuot (g : W.Gam) (a : LetA O n) (i : ZMod n) (j j' : ℤ) (S : Multiset LL) : Prop :=
  qN W T i j' ≤ qN W T i j ∧
    Module.Free O (qQuot W T i j j') ∧ Module.Finite O (qQuot W T i j j') ∧
    Module.finrank O (qQuot W T i j j') = (j' - j).toNat * Module.finrank LL T.V ∧
    (∃ nb, IsNab W T g a i j nb) ∧
    ∀ nb, IsNab W T g a i j nb →
      ∃ hs : (qN W T i j').submoduleOf (qN W T i j) ≤ ((qN W T i j').submoduleOf (qN W T i j)).comap nb,
        DiagWith ((Submodule.mapQ _ _ nb hs).baseChange LL) S

def SenIs (k : Type) [Field k] [Algebra O k] (g : W.Gam) (a : LetA O n) (i : ZMod n) (S : Multiset k) :
    Prop :=
  (∃ nb, IsNab W T g a i 0 nb) ∧
    ∀ nb, IsNab W T g a i 0 nb →
      ∃ hs : (qN W T i 1).submoduleOf (qN W T i 0) ≤ ((qN W T i 1).submoduleOf (qN W T i 0)).comap nb,
        EigWith ((Submodule.mapQ _ _ nb hs).baseChange k) S

def SenPair (g : W.Gam) (a : LetA O n) (i : ZMod n) (U : Multiset ℤ) (w : ℤ) : Prop :=
  (∀ j j' : ℤ, j < j' → DiagQuot W T g a i j j' (eigMs LL PD.p U w j j')) ∧
    ∀ (k : Type) [Field k] [Algebra O k], Function.Surjective (algebraMap O k) →
      SenIs W T k g a i (U.map fun u => ((u - w : ℤ) : k))


open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.qN_zero (i : ZMod n) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.qN W T i 0 = _root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.NΔl W T i := by
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.qN, _root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.mulD, Module.End.one_eq_id, Submodule.map_id,
    Submodule.comap_id]

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedNoJump

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

section Conj

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {c : Ω ≃+* Ω}

theorem conj_conj (hc : IsCMConjOm E Ω c) (x : Ω) : c (c x) = x := by
  obtain ⟨⟨j, hj⟩, -⟩ := hc
  apply j.injective
  rw [hj, hj]
  simp

theorem conj_symm (hc : IsCMConjOm E Ω c) (x : Ω) : c.symm x = c x := by
  rw [RingEquiv.symm_apply_eq, conj_conj hc]

def conjElt (hc : IsCMConjOm E Ω c) (g : G E Ω) : G E Ω :=
  AlgEquiv.ofRingEquiv (f := (c.symm.trans g.toRingEquiv).trans c) (fun x => by
    obtain ⟨y, hy⟩ := hc.2 x
    change c (g (c.symm (algebraMap E Ω x))) = algebraMap E Ω x
    rw [conj_symm hc, hy, AlgEquiv.commutes, ← hy, conj_conj hc])

theorem conjElt_apply (hc : IsCMConjOm E Ω c) (g : G E Ω) (x : Ω) :
    conjElt hc g x = c (g (c.symm x)) := rfl

def conjHom (hc : IsCMConjOm E Ω c) : G E Ω →* G E Ω where
  toFun := conjElt hc
  map_one' := by
    ext x
    simp [conjElt_apply]
  map_mul' g h := by
    ext x
    simp [conjElt_apply]

end Conj

section Rep

variable {Γ : Type} [Group Γ] {A : Type} [CommRing A] {n : ℕ}

def scalGL : Aˣ →* GL (Fin n) A :=
  Units.map (Matrix.scalar (Fin n) : A →+* Matrix (Fin n) (Fin n) A).toMonoidHom

theorem scalGL_comm (a : Aˣ) (M : GL (Fin n) A) : Commute (scalGL a) M := by
  apply Units.ext
  exact (Matrix.scalar_commute (a : A) (fun b => mul_comm _ b) (M : Matrix (Fin n) (Fin n) A)).eq

def twist (ρ : Γ →* GL (Fin n) A) (χ : Γ →* Aˣ) : Γ →* GL (Fin n) A where
  toFun g := scalGL (χ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (scalGL (χ h)),
      (scalGL_comm (χ h) (ρ g)).eq, mul_assoc]

def transGL (M : GL (Fin n) A) : GL (Fin n) A where
  val := (M : Matrix (Fin n) (Fin n) A).transpose
  inv := ((M⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

def dual (ρ : Γ →* GL (Fin n) A) : Γ →* GL (Fin n) A where
  toFun g := transGL (ρ g⁻¹)
  map_one' := by
    apply Units.ext
    simp [transGL]
  map_mul' g h := by
    apply Units.ext
    simp only [transGL, mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul]

def IsoLat (ρ ρ' : Γ →* GL (Fin n) A) : Prop :=
  ∃ P : GL (Fin n) A, ∀ g, P * ρ g = ρ' g * P

end Rep

variable (D : _root_.Formalism.BasicNotions.D7)

def cycField (l : ℕ) : IntermediateField D.host.E D.nd.Om :=
  IntermediateField.adjoin D.host.E {x : D.nd.Om | x ^ l = 1}

def UnramifiedIn (l : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ^ 2

def NC (l : ℕ) : Prop :=
  l = 2 ∨ UnramifiedIn D l ∨ D.R.t * D.R.r < Module.finrank D.host.E ↥(cycField D l)

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedNoJump

end
end
