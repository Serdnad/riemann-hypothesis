module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle267
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle074
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle030
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Formalism.FrobeniusOrbits.Statement
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section

namespace GlobalTheory.GoodDepthZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

theorem charSum_of_tie (D : D7) (hT : Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut)
    (hc : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b) :
    GlobalTheory.LiftLeaf.CharSum D.nd D.naut := by
  intro w a b χ s hχ
  obtain ⟨h1, h2, -⟩ := hT w a b χ χ s hχ hχ
  refine ⟨h1, h2, ?_⟩
  have h := (hT w (D.naut.lpZero w) (D.naut.lpZero w) χ χ 0 hχ hχ).1
  rw [D.naut.lpSum_zero] at h
  refine hc w _ _ (D.naut.lpChar (D.naut.lpZero w) χ) ?_
  rw [← h, D.naut.lpSum_comm, D.naut.lpSum_zero]

theorem lpChar_eta_back (D : D7) (hT : Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut) (w : PlE D.host) (a : D.naut.LP w) :
    D.naut.lpChar (D.naut.lpChar a (D.naut.locG D.naut.etaTinv w)) (D.naut.locG D.naut.etaT w) = a := by
  have hu := D.naut.etaT_unr w
  obtain ⟨hu', he⟩ := D.naut.etaTinv_def w
  have hcard := D.naut.frobEig_card _ hu
  rw [D.naut.locG_dim] at hcard
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 hcard
  have hc0 : c ≠ 0 := by
    intro h0
    apply D.naut.frobEig_ne_zero _ hu
    rw [hc, h0]
    exact Multiset.mem_singleton_self _
  rw [hc, Multiset.map_singleton] at he
  have key := GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c⁻¹ c hu' hu (D.naut.locG_dim _ w) he hc
    (inv_mul_cancel₀ hc0)
  obtain ⟨-, -, -, h4, h5, -⟩ := hT w a a (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) 0
    (D.naut.locG_dim _ w) (D.naut.locG_dim _ w)
  rw [h4, key, h5]

end GlobalTheory.GoodDepthZero
end
end

section

noncomputable section

namespace GlobalTheory.Cmp.SmallJumps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW Module
open GlobalTheory.IndefiniteRowSideFullHecke

theorem finite_of_jumps {L M : Type} [Field L] [AddCommGroup M] [Module L M] (F : ℤ → Submodule L M)
    (U : Submodule L M) (anti : ∀ a, F (a + 1) ≤ F a) (exh : ∀ x ∈ U, ∃ a, x ∈ F a)
    (J : Multiset ℤ) (hJ : J ≠ 0)
    (h : ∀ a, (finrank L (F a) : ℤ) - finrank L (F (a + 1)) = (J.count a : ℤ)) :
    FiniteDimensional L U := by
  have hA : Antitone F := antitone_int_of_succ_le anti
  have hd : Antitone fun a => finrank L (F a) := antitone_int_of_succ_le fun a => by
    have := h a
    omega
  obtain ⟨a₀, ha₀⟩ := Multiset.exists_mem_of_ne_zero hJ
  have hpos : 0 < finrank L (F a₀) := by
    have := h a₀
    have := Multiset.count_pos.2 ha₀
    omega
  have hfin : ∀ a ≤ a₀, FiniteDimensional L (F a) := fun a ha =>
    Module.finite_of_finrank_pos (lt_of_lt_of_le hpos (hd ha))
  obtain ⟨b, hb⟩ := J.toFinset.bddBelow
  have hb' : ∀ a ∈ J, b ≤ a := fun a ha => hb (by simpa using ha)
  have hb0 : b ≤ a₀ := hb' a₀ ha₀
  have hst : ∀ a ≤ b, F a = F b := by
    intro a ha
    induction a, ha using Int.leInductionDown with
    | base => rfl
    | pred a ha ih =>
      haveI := hfin (a - 1) (by omega)
      have h1 := h (a - 1)
      have h2 : J.count (a - 1) = 0 := Multiset.count_eq_zero.2 fun hm => by
        have := hb' _ hm
        omega
      rw [sub_add_cancel, h2] at h1
      rw [← ih]
      exact (Submodule.eq_of_le_of_finrank_eq (hA (by omega)) (by omega)).symm
  haveI := hfin b hb0
  refine Submodule.finiteDimensional_of_le (S₂ := F b) fun x hx => ?_
  obtain ⟨a, ha⟩ := exh x hx
  rcases le_total a b with hab | hab
  · rwa [← hst a hab]
  · exact hA hab ha

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filV_anti : Antitone fun a => FilV PD (LL := LL) (V := V) a := by
  refine antitone_int_of_succ_le fun a => ?_
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, rfl⟩
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

theorem filV_exh (x : TensorProduct Qp V BdR) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, v ⊗ₜ ⟨b, ha⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (filV_anti PD (min_le_left a b) ha)
      (filV_anti PD (min_le_right a b) hb)⟩

theorem finite_ddRE_of_multV (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : Multiset ℤ) (hJ : J ≠ 0)
    (h : ∀ a, multV PD ρ τ a = (J.count a : ℤ)) : FiniteDimensional LL (DdRE PD ρ τ) :=
  finite_of_jumps (FildR PD ρ τ) _
    (fun a => inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1)))
    (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩) J hJ h

end Periods

theorem linearIndepOn_of_invariant {K F W G ι : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup W]
    [Module F W] [Module K W] [IsScalarTower K F W] (a : G → F → F) (σ : G → W →+ W)
    (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hinv : ∀ b, (∀ g, a g b = b) → ∃ c, algebraMap K F c = b) (v : ι → W) (hv : ∀ g i, σ g (v i) = v i)
    (s : Finset ι) (h : LinearIndepOn K v s) : LinearIndepOn F v s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hx' : x ∉ (s : Set ι) := hx
    rw [Finset.coe_insert, linearIndepOn_insert hx'] at h ⊢
    refine ⟨ih h.1, fun hm => h.2 ?_⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' F).1 hm
    have key : ∀ i ∈ s, ∀ g, a g (c i) = c i := by
      intro i hi g
      have h1 : ∑ i ∈ s, a g (c i) • v i = v x := by

        rw [← hv g x, ← hc, map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [hσ, hv]
      have h2 := linearIndepOn_finset_iff.1 (ih h.1) (fun j => a g (c j) - c j) (by
        simp only [sub_smul, Finset.sum_sub_distrib, h1, hc, sub_self]) i hi
      exact sub_eq_zero.1 h2
    rw [← hc]
    refine Submodule.sum_mem _ fun i hi => ?_
    obtain ⟨k, hk⟩ := hinv _ (key i hi)
    rw [← hk, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem finite_of_invariant {K F W G : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup W]
    [Module F W] [Module K W] [IsScalarTower K F W] [Module.Finite F W] (a : G → F → F) (σ : G → W →+ W)
    (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hinv : ∀ b, (∀ g, a g b = b) → ∃ c, algebraMap K F c = b) (U : Submodule K W)
    (hU : ∀ x ∈ U, ∀ g, σ g x = x) : Module.Finite K U := by
  rw [← Module.rank_lt_aleph0_iff]
  refine lt_of_le_of_lt (rank_le (n := finrank F W) fun s hs => ?_) (Cardinal.natCast_lt_aleph0)
  have h1 : LinearIndepOn K (fun x : U => (x : W)) s := hs.map' U.subtype U.ker_subtype
  have h2 := linearIndepOn_of_invariant a σ hσ hinv (fun x : U => (x : W))
    (fun g x => hU x x.2 g) s h1
  simpa using LinearIndependent.fintype_card_le_finrank h2

section FieldPeriods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem finite_ddR_of_isField (hF : IsField BdR) [Module.Finite Qp V] (ρ : Representation LL G V) :
    Module.Finite LL (DdR PD ρ) := by
  letI : Field BdR := hF.toField
  haveI := PD.finK
  let σ : G → TensorProduct Qp BdR V →ₗ[Qp] TensorProduct Qp BdR V := fun g =>
    TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : BdR) w, σ g (b • w) = PD.actdR g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  let U : Submodule K (TensorProduct Qp BdR V) :=
    { carrier := {x | ∀ g, σ g x = x}
      zero_mem' := fun g => map_zero _
      add_mem' := fun hx hy g => by rw [map_add (f := _), hx g, hy g]
      smul_mem' := fun c x hx g => by
        rw [← algebraMap_smul BdR c x, hσ, hx g, AlgEquiv.commutes] }
  haveI : Module.Finite K U := finite_of_invariant (F := BdR) (fun g b => PD.actdR g b)
    (fun g => (σ g).toAddMonoidHom) hσ PD.invdR U fun _ hx => hx
  haveI : Module.Finite Qp U := Module.Finite.trans K U
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V BdR x) =
      TensorProduct.comm Qp V BdR (actVdR PD ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, actVdR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  let f : DdR PD ρ →ₗ[Qp] U :=
    { toFun := fun x => ⟨TensorProduct.comm Qp V BdR x, fun g => by
        have := x.2
        simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero] at this
        rw [hc, this g]⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (map_smul (TensorProduct.comm Qp V BdR) c _) }
  haveI : Module.Finite Qp (DdR PD ρ) := Module.Finite.of_injective f fun x y h =>
    Subtype.ext ((TensorProduct.comm Qp V BdR).injective (congrArg Subtype.val h))
  exact Module.Finite.of_restrictScalars_finite Qp LL _

end FieldPeriods

variable (D : D7)

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

variable {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))

end Place

variable {D}

end GlobalTheory.Cmp.SmallJumps
end
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.primitiveRoot_notPrimePow_map_ne_one' : ∀ (k : Type) [Field k] (O : Type) [CommRing O] [IsDomain O] (f : O →+* k) (ζ : O) (n : ℕ), 1 < n → IsPrimitiveRoot ζ n → (¬ IsPrimePow n) → f ζ ≠ 1 := by
  first | exact @GlobalTheory.primitiveRoot_notPrimePow_map_ne_one | exact GlobalTheory.primitiveRoot_notPrimePow_map_ne_one | (intros; apply GlobalTheory.primitiveRoot_notPrimePow_map_ne_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.localCohomology_vanishes_tame_inertia_no_fixed : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (rho : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ContAction rho → (∃ γ : Dec (F := F) A, (γ : G F Ω) ∈ Ine (F := F) A ∧ Function.Bijective fun m : M => rho γ m - m) → H0 rho = ⊥ ∧ Subsingleton (H1 rho) ∧ Subsingleton (H2 rho) := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.tame_vanish | exact GlobalTheory.StringRepresentationDecomposition.tame_vanish | (intros; apply GlobalTheory.StringRepresentationDecomposition.tame_vanish <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.HilbertClassField

open Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.IdealArtinSymbol

theorem exists_artinSymbol : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E),
      IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧
      (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v →
        IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  intro H E Ω _ _ _ _ _
  obtain ⟨art, ha⟩ := H E Ω
  obtain ⟨cl, hclo, hclk, hunit, hunif⟩ := GlobalTheory.T.exists_ideleClassGroupHom_open_kernel E
  have hker : art.ker ≤ cl.ker := by
    rw [ha.ker]
    exact Subgroup.topologicalClosure_minimal _ hclk (Subgroup.isClosed_of_isOpen _ hclo)
  let ρ := art.liftOfSurjective ha.quot.surjective ⟨cl, hker⟩
  have hρ : ∀ x, ρ (art x) = cl x := fun x => art.liftOfRightInverse_comp_apply _ _ ⟨cl, hker⟩ x
  have hρo : IsOpen (ρ.ker : Set (Gab E Ω)) := by
    rw [← ha.quot.isQuotientMap.isOpen_preimage]
    convert hclo using 1
    ext x
    rw [Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe, MonoidHom.mem_ker, hρ, MonoidHom.mem_ker]
  let ψ : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E) := ρ.comp (toAb E Ω)
  have hlies : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), LiesAbove A v → IsPlaceOver A v :=
    fun v A h x => by rw [← h x, A.mem_nonunits_iff]
  refine ⟨ψ⁻¹, ?_, ?_, ?_⟩
  · have e : ((ψ⁻¹).ker : Set (Ω ≃ₐ[E] Ω)) = toAb E Ω ⁻¹' (ρ.ker : Set (Gab E Ω)) := by
      ext σ
      simp [ψ, MonoidHom.mem_ker]
    rw [e]
    exact hρo.preimage QuotientGroup.continuous_mk
  · intro A g hg
    rcases GlobalTheory.T.inertiaElement_eq_one_or_liesAbove_finitePlace E Ω A g hg with rfl | ⟨v, hv⟩
    · exact map_one _
    have hI : g ∈ Ine (F := E) A := ⟨hg.1, fun x hx => by
      rw [← A.mem_nonunits_iff]
      exact hg.2 x ((A.valuation_le_one_iff x).1 hx)⟩
    obtain ⟨x, _, hx⟩ := (ha.ine v A (hlies v A hv) (toAb E Ω g)).2 ⟨g, hI, rfl⟩
    have : ψ g = 1 := by
      show ρ (toAb E Ω g) = 1
      rw [← hx, hρ]
      exact hunit v x ‹_›
    rw [MonoidHom.inv_apply, this, inv_one]
  · intro v A φ hv hφ
    have hF : IsFrob (F := E) A (normV v) φ := ⟨hφ.1, fun x hx => by
      rw [← A.mem_nonunits_iff]
      exact hφ.2 x ((A.valuation_le_one_iff x).1 hx)⟩
    obtain ⟨x, hxu, hx⟩ := (ha.frob v A (hlies v A hv) (toAb E Ω φ⁻¹)).2 ⟨φ, hF, rfl⟩
    rw [MonoidHom.inv_apply, ← map_inv]
    show ρ (toAb E Ω φ⁻¹) = _
    rw [← hx, hρ]
    exact hunif v x hxu

end GlobalTheory.IdealArtinSymbol
end
