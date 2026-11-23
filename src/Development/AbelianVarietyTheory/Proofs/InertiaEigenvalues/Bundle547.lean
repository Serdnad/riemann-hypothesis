module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle521
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle277
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle049
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle523
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle522
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle313
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.ExactMult

theorem finrank_add_of_exact {L A₀ A₁ A₂ : Type} [Field L] [AddCommGroup A₀] [Module L A₀]
    [AddCommGroup A₁] [Module L A₁] [AddCommGroup A₂] [Module L A₂] (i : A₀ →ₗ[L] A₁) (p : A₁ →ₗ[L] A₂)
    (hi : Function.Injective i) (hk : LinearMap.range i = LinearMap.ker p)
    (S₀ : Submodule L A₀) (S₁ : Submodule L A₁) (S₂ : Submodule L A₂) [FiniteDimensional L S₁]
    (h0 : S₀ = S₁.comap i) (h2 : S₁.map p = S₂) :
    finrank L S₁ = finrank L S₀ + finrank L S₂ := by
  have e := LinearMap.finrank_range_add_finrank_ker (p.domRestrict S₁)
  rw [LinearMap.range_domRestrict, h2, LinearMap.ker_domRestrict, ← hk] at e
  have e1 : finrank L ((LinearMap.range i).comap S₁.subtype) = finrank L S₀ := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, h0,
      (Submodule.equivMapOfInjective i hi (S₁.comap i)).finrank_eq, Submodule.map_comap_eq, inf_comm]
  omega

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem mem_fil (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) (x : V ⊗[Qp] BdR) :
    x ∈ FildR PD ρ τ a ↔ ((∀ g, actVdR PD ρ g x = x) ∧
      ∀ c : K, mulVdR (LL := LL) (V := V) c x = τ c • x) ∧ x ∈ FilV PD (LL := LL) (V := V) a := by
  simp only [FildR, DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero]

theorem map_mul (f : V →ₗ[LL] V') (c : K) (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (mulVdR (LL := LL) (V := V) c x) =
      mulVdR (LL := LL) (V := V') c (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem map_act (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (g : G) (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (actVdR PD ρ g x) =
      actVdR PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, he]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem act_mul (ρ : Representation LL G V) (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (LL := LL) (V := V) c x) =
      mulVdR (LL := LL) (V := V) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, mulVdR]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem mul_mem_filV (a : ℤ) (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (LL := LL) (V := V) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    refine ⟨v ⊗ₜ ⟨c • b.1, (PD.Fil a).smul_mem c b.2⟩, ?_⟩
    simp [mulVdR, Algebra.smul_def]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hy hz

noncomputable def ev (x : V ⊗[Qp] BdR) : LL ⊗[Qp] K →ₗ[Qp] V ⊗[Qp] BdR :=
  TensorProduct.lift (LinearMap.mk₂ Qp (fun (c : LL) (k : K) => c • mulVdR (LL := LL) (V := V) k x)
    (fun _ _ _ => add_smul _ _ _) (fun _ _ _ => smul_assoc _ _ _)
    (fun c k k' => by
      rw [← smul_add]
      congr 1
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [mulVdR, add_mul, tmul_add]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]; abel)
    (fun q c k => by
      rw [smul_comm q c]
      congr 1
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        have : algebraMap K BdR (q • k) * b = q • (algebraMap K BdR k * b) := by
          rw [← Algebra.smul_def, ← Algebra.smul_def, smul_assoc]
        simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply, this,
          tmul_smul]
      | add y z hy hz => simp only [map_add (f := _), hy, hz, smul_add]))

theorem ev_tmul (x : V ⊗[Qp] BdR) (c : LL) (k : K) :
    ev (LL := LL) (K := K) x (c ⊗ₜ k) = c • mulVdR (LL := LL) (V := V) k x := rfl

theorem mul_mul (y k : K) (x : V ⊗[Qp] BdR) :
    mulVdR (LL := LL) (V := V) (y * k) x = mulVdR (LL := LL) (V := V) y (mulVdR (LL := LL) (V := V) k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR, mul_assoc]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem map_fildR_eq [CharZero Qp] (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (f : V →ₗ[LL] V') (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ)
    (hs : ∀ y ∈ DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') a,
      ∃ x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a,
        AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x = y) :
    (FildR PD ρ τ a).map (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) =
      FildR PD ρ' τ a := by
  haveI := PD.finK
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := (mem_fil PD ρ τ a x).1 hx
    refine (mem_fil PD ρ' τ a _).2 ⟨⟨fun g => ?_, fun c => ?_⟩, GlobalTheory.HTW.map_mem_FilV PD f a x h3⟩
    · rw [← map_act PD ρ ρ' f he, h1]
    · rw [← map_mul, h2, map_smul]
  · intro y hy
    obtain ⟨x, ⟨hx1, hx2⟩, rfl⟩ := hs y ⟨hy.1.1, hy.2⟩
    obtain ⟨⟨-, h2⟩, -⟩ := (mem_fil PD ρ' τ a _).1 hy
    have h1 : ∀ g, actVdR PD ρ g x = x := by
      simpa only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] using hx1
    obtain ⟨m, c, k, hc, hk⟩ := GlobalTheory.exists_embedding_idempotent_tensor Qp K LL τ
    refine ⟨∑ j, c j • mulVdR (LL := LL) (V := V) (k j) x,
      (mem_fil PD ρ τ a _).2 ⟨⟨fun g => ?_, fun y => ?_⟩, ?_⟩, ?_⟩

    · simp only [map_sum, map_smul, act_mul, h1]
    · have := congrArg (ev (LL := LL) (K := K) x) (hk y)

      simp only [map_sum, ev_tmul, mul_mul] at this

      simp only [map_sum, map_smul, this, Finset.smul_sum, mul_smul]
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_filV PD a _ x hx2)

    · simp only [map_sum, map_smul, map_mul, h2, ← mul_smul, ← Finset.sum_smul, hc, one_smul]

variable {V₀ : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]

theorem tensor_exact (ι : V₀ →ₗ[LL] V) (π : V →ₗ[LL] V') (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hk : LinearMap.range ι = LinearMap.ker π) :
    Function.Injective (AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR)) ∧
      LinearMap.range (AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR)) =
        LinearMap.ker (AlgebraTensorModule.map π (LinearMap.id : BdR →ₗ[Qp] BdR)) := by
  have e1 : ∀ x, AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR) x =
      (ι.restrictScalars Qp).rTensor BdR x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have e2 : ∀ x, AlgebraTensorModule.map π (LinearMap.id : BdR →ₗ[Qp] BdR) x =
      (π.restrictScalars Qp).rTensor BdR x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hex : Function.Exact (ι.restrictScalars Qp) (π.restrictScalars Qp) :=
    (LinearMap.exact_iff.2 hk.symm : Function.Exact ι π)
  constructor
  · intro x y h
    rw [e1, e1] at h
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := BdR) (ι.restrictScalars Qp) hι h
  · ext x
    have := rTensor_exact BdR hex hπ x
    simp only [LinearMap.mem_range, LinearMap.mem_ker, e1, e2]
    exact this.symm

end General

theorem exact_hodge_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V₀ : Type) [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₀] (ρ₀ : Representation ↥LL.1 ↥(GK K) V₀) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (ι : V₀ →ₗ[↥LL.1] V₁) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π → IsDR (P.PD K) ρ₁ → IsDR (P.PD K) ρ₀ ∧ IsDR (P.PD K) ρ₂ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) = finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) ∧ multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a ∧ (IsJumpV (P.PD K) ρ₁ τ a ↔ IsJumpV (P.PD K) ρ₀ τ a ∨ IsJumpV (P.PD K) ρ₂ τ a) := by
  intro l _ P AI T K LL V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ ι π hι hπ hi hs hk hd
  obtain ⟨d2, hst⟩ := (GlobalTheory.T.deRham_subrep_quotient_and_strictness l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hd
  obtain ⟨t1, t2⟩ := tensor_exact (Qp := ℚ_[l]) (BdR := P.R.BdR) ι π hi hs hk
  have hf : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) =
      finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) := by
    intro τ a
    haveI := (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₁ ρ₁ τ a).1
    exact finrank_add_of_exact _ _ t1 t2 _ _ _ (GlobalTheory.HTW.FildR_eq_comap (P.PD K) ρ₀ ρ₁ ι hi hι τ a)
      (map_fildR_eq (P.PD K) ρ₁ ρ₂ π hπ τ a (hst a))
  refine ⟨(GlobalTheory.T.deRham_subrep_quotient_and_strictness l P AI T K LL V₀ ρ₀ V₁ ρ₁ ι hι).1 hi hd, d2, fun τ a => ?_⟩
  have hm : multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a := by
    unfold multV
    rw [hf τ a, hf τ (a + 1)]
    push_cast
    ring
  refine ⟨hf τ a, hm, ?_⟩
  obtain ⟨-, n0, j0⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₀ ρ₀ τ a
  obtain ⟨-, -, j1⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₁ ρ₁ τ a
  obtain ⟨-, n2, j2⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₂ ρ₂ τ a
  rw [j0, j1, j2, hm]
  omega

end GlobalTheory.Per.ExactMult
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

noncomputable section

namespace GlobalTheory.GoodRowMono

theorem separable_prod_teich {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) {f : (ZMod g)[X]} (hf : Squarefree f) :
    (((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (t x)).prod).Separable := by
  have hnd : ((Formalism.CyclotomicNorms.rootsBar f).map t).Nodup :=
    (nodup_roots ((separable_map _).2 (PerfectField.separable_iff_squarefree.2 hf))).map (GlobalTheory.TameLabels.teich_injective t ht)
  have e : ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (t x)) =
      ((Formalism.CyclotomicNorms.rootsBar f).map t).map (fun a => X - C a) := by
    rw [Multiset.map_map]; rfl
  rw [e]
  have hs : ((((Formalism.CyclotomicNorms.rootsBar f).map t).map fun a => X - C a).prod).Splits :=
    Splits.multisetProd fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
      exact Splits.X_sub_C _
  refine (nodup_roots_iff_of_splits (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a).ne_zero hs).1 ?_
  rw [roots_multiset_prod_X_sub_C]
  exact hnd

variable (D : D7)

variable {D}

theorem separable_fixed {σ : D.what₂.FT} {π : D.naut.CG D.R.r} (hg : D.nd.goodRow σ)
    (hlab : ∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v)))
    (k : Fin 2) (v : D.nd.PlG k) :
    (D.naut.inePol (D.naut.locG π (D.naut.plGw k v)) (D.ntypes.tg k v)).Separable := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hfull : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locG π (D.naut.plGw k v)) := by
    rw [← hlab, (D.nd.lab_monic k σ v).2, D.naut.locG_dim]
  rw [D.ntypes.inertiaCharpoly_type k v _ hfull, ← hlab]
  exact separable_prod_teich _ (D.ntypes.teichC_inj k) ((hg k).1.2.1 v)

end GlobalTheory.GoodRowMono
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistRead

theorem matRep_apply {F Γ : Type} [CommRing F] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) F)
    (g : Γ) (v : Fin k → F) : matRep M g v = (M g).mulVec v := by
  simp [matRep, Matrix.toLinAlgEquiv'_apply]

theorem local_twist_dual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K LL : FinExt l) (hs : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1) {n : ℕ}
    (R T U : ↥(GK K) →* Matrix (Fin n) (Fin n) ↥LL.1)
    (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1)
    (hν : ∀ g x, ν g x = χ g • x) (hR : ∀ g, R g = χ g • T g)
    (hU : ∀ g, U g = ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (T g⁻¹).transpose)
    (dR : IsDR (P.PD K) (matRep R)) (dν : IsDR (P.PD K) ν)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ) (hc : ∀ a : ℤ, multV (P.PD K) ν τ a = if a = c then 1 else 0) :
    IsDR (P.PD K) (matRep T) ∧ IsDR (P.PD K) (matRep U) ∧
      ∀ a : ℤ, multV (P.PD K) (matRep T) τ a = multV (P.PD K) (matRep R) τ (a + c) ∧
        multV (P.PD K) (matRep U) τ a = multV (P.PD K) (matRep R) τ (c - a - 1) := by
  have hRT : ∀ g x, matRep R g x = χ g • matRep T g x := by
    intro g x
    rw [matRep_apply, matRep_apply, hR, Matrix.smul_mulVec]
  have dT : IsDR (P.PD K) (matRep T) :=
    (GlobalTheory.TwistDR.isDR_twist_iff l P AI hT K LL _ (matRep T) (matRep R) ν χ hν hRT dν).2 dR
  have jT : ∀ a : ℤ, multV (P.PD K) (matRep R) τ (a + c) = multV (P.PD K) (matRep T) τ a :=
    GlobalTheory.TwistJump.multV_twist_char l P AI hT K LL _ (matRep T) (matRep R) ν χ hν hRT dν τ c hc
  have hb : Function.Bijective (dotProductBilin ↥LL.1 ↥LL.1 :
      (Fin n → ↥LL.1) →ₗ[↥LL.1] (Fin n → ↥LL.1) →ₗ[↥LL.1] ↥LL.1) :=
    (dotProductEquiv ↥LL.1 (Fin n)).bijective
  have hd := GlobalTheory.T.galois_representation_hom_finite_dimensional l P AI hT K LL _ (matRep T) _ (matRep U) _ 1 hb (by
    intro g x y
    rw [matRep_apply, matRep_apply, hU, zpow_one]
    simp only [dotProductBilin_apply_apply, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]) dT
  refine ⟨dT, hd.1, fun a => ⟨(jT a).symm, ?_⟩⟩
  have h1 := hd.2 τ (-a - 1) hs
  have h2 := jT (-a - 1)
  rw [show -(-a - 1) - 1 = a by ring] at h1
  rw [show -a - 1 + c = c - a - 1 by ring] at h2
  rw [h1, h2]



theorem twist_dual_mult : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) → ∀ (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (τ : D.host.E →+* Qbar (D.nd.l i)), (∀ x : D.host.E, τ x = ((τ' (Br.cEw D.nbr i w hw x) : ↥LL'.1) : Om (D.nd.l i))) → ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (χ : GE D.nd →* GL (Fin 1) (D.nd.O i)) (c : ℤ), Continuous (fun g => rO D.nd i r x g) → (∀ g, (χ g : Matrix (Fin 1) (Fin 1) (D.nd.O i)) 0 0 = ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i)) → D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w → D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) χ) w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) χ) τ = {c} → IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) ∧ IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' a = (((D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ).count (a + c) : ℕ) : ℤ) ∧ multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))) τ' a = (((D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ).count (c - a - 1) : ℕ) : ℤ) := by
  intro D i w hw hT LL' h τ' τ hτ r x χ c hr hχ dr dχ hc
  have tie := D.loc_tie i w hw
  set f : D.nd.O i →+* ↥LL'.1 :=
    (IntermediateField.inclusion h).toRingHom.comp (D.nbr i w hw).toLL with hf
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (continuous_subtype_val.comp (D.nbr i w hw).eO_cont)
  have hmap : ∀ (m : ℕ) (ρ : GE D.nd →* GL (Fin m) (D.nd.O i)),
      mapRep (algebraMap ↥LL'.1 (Qbar (D.nd.l i))) (mapRep f ρ) = mapRep (iotaOQ D.nd D.naut i) ρ := by
    intro m ρ
    ext g a b
    exact (tie.1 _).symm
  have cr : Continuous (fun g => ((mapRep f (r x) g : GL (Fin D.R.nV) ↥LL'.1) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) ↥LL'.1)) := hr.matrix_map hfc
  have cχ : Continuous (fun g => ((mapRep f χ g : GL (Fin 1) ↥LL'.1) : Matrix (Fin 1) (Fin 1) ↥LL'.1)) := by
    refine Continuous.matrix_map (A := fun g => (χ g : Matrix (Fin 1) (Fin 1) (D.nd.O i))) ?_ hfc
    refine continuous_matrix fun a b => ?_
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    simp only [hχ]
    exact D.nd.chi_cont i 1
  have tr := tie.2.2 LL' h _ _ cr
  have tχ := tie.2.2 LL' h _ _ cχ
  rw [hmap] at tr tχ
  have dr' := tr.2.1.1 dr
  have dχ' := tχ.2.1.1 dχ
  have jr := (tr.2.2.2 τ τ' hτ).2 dr'
  have jχ := (tχ.2.2.2 τ τ' hτ).2 dχ'
  have hs : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
    haveI : FiniteDimensional ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := (D.nbr i w hw).Kw.2
    have := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw LL'
      (fun σ y => h ((D.nbr i w hw).LL_split σ y)) inferInstance).2
    rw [Nat.card_eq_fintype_card]
    exact this
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  have hrep : matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rO D.nd i r x))) =
      (D.nbr i w hw).repE LL' ((mapRep f (r x)).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [matRep_apply]
    rfl
  have key := local_twist_dual (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) hT (D.nbr i w hw).Kw LL' hs
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rO D.nd i r x)))
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))
    ((D.nbr i w hw).repE LL' ((mapRep f χ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype))
    (fun g => f (D.nd.chi i 1 (ι g) : (D.nd.O i)ˣ))
    (by
      intro g v
      funext a
      change Matrix.mulVec ((χ (ι g) : Matrix (Fin 1) (Fin 1) (D.nd.O i)).map f) v a = _
      rw [Subsingleton.elim a 0]
      simp [Matrix.mulVec, dotProduct, hχ])
    (by
      intro g
      ext a b
      congr 1
      change f (rO D.nd i r x (ι g) a b) = f (D.nd.chi i 1 (ι g) : (D.nd.O i)ˣ) *
        f ((((D.nd.chi i 1 (ι g))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g) a b)
      rw [← map_mul, Units.mul_inv_cancel_left])
    (by
      intro g
      have e := congrArg Units.val (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
      have e' : f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) =
          ((cycLL ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) :=
        by
        have e2 := congrArg (IntermediateField.inclusion h) e
        exact e2.trans ((IntermediateField.inclusion h).commutes _)
      rw [← e']
      ext a b
      congr 1
      change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
          rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
        f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
      rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
      congr 1
      ring)
    (by
      rw [hrep]
      unfold IsDR
      rw [Module.finrank_fin_fun]
      exact dr')
    (by
      unfold IsDR
      rw [Module.finrank_fin_fun]
      exact dχ')
    τ' c
    (by
      intro a
      refine (jχ a).symm.trans ?_
      rw [hc, Multiset.count_singleton]
      split_ifs <;> rfl)
  rw [hrep] at key
  refine ⟨key.1, key.2.1, fun a => ⟨?_, ?_⟩⟩
  · exact (key.2.2 a).1.trans (jr (a + c)).symm
  · exact (key.2.2 a).2.trans (jr (c - a - 1)).symm

end GlobalTheory.TwistRead
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.frameMapAdjoint_mul_frameMatrix_eq_idempotent_split : ∀ (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D), cA D f = f → ∀ k : GA D W, SuppF W f k → ∀ x x' : WO V W, (∀ a b, f * x a b = f * x' a b) → (HMul.hMul (frMapAdj V W βV βW x') (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) = toEAf D f • (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) + (1 - toEAf D f) • frMapAdj V W βV βW x' := by
  first | exact @GlobalTheory.LocDisj.frMapAdj_mul_frame_eq | exact GlobalTheory.LocDisj.frMapAdj_mul_frame_eq | (intros; apply GlobalTheory.LocDisj.frMapAdj_mul_frame_eq <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.latticeDictionary_frame_mem_open_frames : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} (V : HSp D) (U : Unf Xo c σ V.rank) (dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hU : IsUnf U) (hW : ∀ k, ModelW V rfl (U.X k))
    (hD : DictLat U V rfl dict io e F ik φ th x₀) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀), ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom := by
  first | exact @GlobalTheory.DictDom.frame_mem_dom | exact GlobalTheory.DictDom.frame_mem_dom | (intros; apply GlobalTheory.DictDom.frame_mem_dom <;> assumption)
end
