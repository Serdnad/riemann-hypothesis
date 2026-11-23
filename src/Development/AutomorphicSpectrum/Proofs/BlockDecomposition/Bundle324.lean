module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle305
public import GroundTheory.LocalFields.LocalArtinMap
public import GroundTheory.LocalFields.LubinTatePoints
public import GroundTheory.LocalFields.UnramifiedHensel
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.MeasureTheory.Group.Measure
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle306
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvariance
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.PAdicHodge.Bundle004
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem det_hgp (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (h : MirabolicParabolic k m j) :
    GeneralLinearGroup.det ((h : Mir k (m + j)) : GL (Fin (m + j + 1)) k) =
      GeneralLinearGroup.det (gpProj k m j h).1 *
        GeneralLinearGroup.det ((gpProj k m j h).2 : GL (Fin (j + 1)) k) := by
  let f : Fin m ⊕ Fin (j + 1) → Fin (m + j + 1) :=
    Sum.elim (fun a => GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩)
      (fun b => GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) hab <;>
      have hs := (GlobalTheory.BZMir.Leib.eGP m j).injective hab <;>
      simp_all [Sigma.mk.inj_iff]
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩
  have hA : ∀ a b : Fin m,
      (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a b =
        (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨false, b⟩) :=
    fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j h) false a b
  have hD : ∀ a b : Fin (j + 1),
      (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) : Matrix (Fin (j + 1)) (Fin (j + 1)) k) a b =
        (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (GlobalTheory.BZMir.Leib.eGP m j ⟨true, a⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩) :=
    fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j h) true a b
  have hzero := (GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff k m j (h : GlobalTheory.BZMir.Mir k (m + j))).mp h.2
  have hsub : (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k).submatrix (Equiv.ofBijective f hf) (Equiv.ofBijective f hf) =
      Matrix.fromBlocks
        (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)
        (Matrix.of fun a b => (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
          Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) (f (Sum.inl a)) (f (Sum.inr b)))
        0
        (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) k) := by
    ext (a | a) (b | b)
    · exact (hA a b).symm
    · rfl
    · exact hzero a b
    · exact (hD a b).symm
  have key : Matrix.det (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      Matrix.det (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *
        Matrix.det (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) k) := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf), hsub, Matrix.det_fromBlocks_zero₂₁]
  ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
  exact key

theorem dpowM_hgp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (s : ℝ) (h : MirabolicParabolic k m j),
    dpowM (m + j) s (h : Mir k (m + j)) = dpow m s (gpProj k m j h).1 * dpowM j s (gpProj k m j h).2 := by
  intro k _ _ _ _ m j s h
  have h1 : GlobalTheory.RgGu.Leib.dpowM (m + j) s (h : GlobalTheory.BZMir.Mir k (m + j)) =
      GlobalTheory.BZMir.Leib.dpow (m + j + 1) s ((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) := rfl
  have h2 : GlobalTheory.RgGu.Leib.dpowM j s (GlobalTheory.BZMir.Leib.gpProj k m j h).2 =
      GlobalTheory.BZMir.Leib.dpow (j + 1) s ((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) := rfl
  have h3 : ∀ (n : ℕ) (g : GL (Fin n) k),
      GlobalTheory.BZMir.Leib.dpow n s g = GlobalTheory.SmGL.absPow k (s : ℂ) (GeneralLinearGroup.det g) :=
    fun _ _ => rfl
  rw [h1, h2, h3, h3, h3, GlobalTheory.CompanionTheory.LeibPhi.det_hgp, map_mul]

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

section twEquiv
variable {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nonempty_twAct_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  have he : ∀ v, e.toLinearEquiv v = e v := fun v => rfl
  have hl : ∀ v, e.toIntertwiningMap.toLinearMap v = e v := fun v => rfl
  have hmap : (GlobalTheory.PRep.twKer ρ N θ).map (e.toLinearEquiv : V →ₗ[ℂ] W) = GlobalTheory.PRep.twKer σ N θ := by
    unfold GlobalTheory.PRep.twKer
    rw [Submodule.map_span]
    congr 1
    ext w
    constructor
    · rintro ⟨x, ⟨n, v, rfl⟩, rfl⟩
      refine ⟨n, e v, ?_⟩
      simp only [LinearEquiv.coe_coe, map_sub, map_smul, he, hl, eint]
    · rintro ⟨n, w', rfl⟩
      refine ⟨ρ n (e.toLinearEquiv.symm w') - ((θ n : ℂˣ) : ℂ) • e.toLinearEquiv.symm w', ⟨n, _, rfl⟩, ?_⟩
      have hw : e (e.toLinearEquiv.symm w') = w' := e.toLinearEquiv.apply_symm_apply w'
      simp only [LinearEquiv.coe_coe, map_sub, map_smul, he, hl, eint, hw]
  refine ⟨Representation.Equiv.mk (Submodule.Quotient.equiv _ _ e.toLinearEquiv hmap) fun m => ?_⟩
  apply Submodule.linearMap_qext
  ext v
  exact congrArg (Submodule.Quotient.mk (p := GlobalTheory.PRep.twKer σ N θ)) (eint e (s m) v)

theorem nonempty_twist_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (χ : G →* ℂˣ) :
    Nonempty ((twist ρ χ).Equiv (twist σ χ)) := by
  have he : ∀ v, e.toLinearEquiv v = e v := fun v => rfl
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  show e.toLinearEquiv (((χ g : ℂˣ) : ℂ) • ρ g v) = ((χ g : ℂˣ) : ℂ) • σ g (e.toLinearEquiv v)
  rw [map_smul, he, he, eint]

end twEquiv

theorem miso_phiN (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (n : ℕ) (A B : MRep k (n + 1)) (h : MIso A B) : MIso (phiN ψ A) (phiN ψ B) := by
  have h1 : MIso (GlobalTheory.BZMir.MRep.phiM k ψ A) (GlobalTheory.BZMir.MRep.phiM k ψ B) := by
    obtain ⟨e⟩ := h
    unfold GlobalTheory.BZMir.MRep.phiM GlobalTheory.BZMir.phiMinus
    exact nonempty_twAct_equiv e _ _ _ (levi_stab ψ n)
  obtain ⟨e'⟩ := h1
  exact nonempty_twist_equiv e' _

end GlobalTheory.CompanionTheory.LeibOrd

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

theorem _root_.GlobalTheory.T.jacquet_cuspidal_support_of_functional : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n) (f : Jacquet π (unipRad k (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd)) →ₗ[ℂ] ℂ), f ≠ 0 → (∀ t w, f (jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π t w) = PositivityTheory.Lbc.torusChar ξ t * f w) → ∃ g : (jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π).IntertwiningMap (piTensor fun a => (IrrGL.ofChar (ξ a) (hξ a)).rep), ∃ w, g w ≠ 0 := by
  exact @GlobalTheory.CompanionTheory.CharTensor.chartotensor
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms


theorem _root_.GlobalTheory.T.lubin_tate_unramified_degree_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {Ωv : Type} [Field Ωv] [ValuativeRel Ωv] [TopologicalSpace Ωv] [IsValuativeTopology Ωv]
    [Algebra F Ωv] [ValuativeExtension F Ωv] [IsSepClosure F Ωv] [IsSepClosed Ωv]
    {π : 𝒪[F]} (hπ : Irreducible π) {f : PowerSeries 𝒪[F]} (hf : IsLubinTateSeries π f)
    (u : 𝒪[F]ˣ) (τ : Ωv ≃ₐ[F] Ωv), unramifiedDegree F Ωv τ = 1 →
    (∀ n, ∀ x ∈ lubinTateTorsion Ωv (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = (u : 𝒪[F]) • x) →
    ∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension F Ωv),
    ((localArtinMap F Ωv (unitsIncl F u⁻¹) ⟨y, hy⟩ : maximalAbelianExtension F Ωv) : Ωv) = τ y := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia | exact GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia | (intros; apply GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia <;> assumption)
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgGuCore

theorem not_inf_le_of_rank_quotient_le_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (T A C : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (hmod : (A ⊔ C) ⊓ T ≤ A ⊓ T ⊔ C ⊓ T) (hA : ¬ A ≤ T) (hC : ¬ C ≤ T) :
    ¬ A ⊓ C ≤ T := by
  obtain ⟨a, haA, haT⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨c, hcC, hcT⟩ := SetLike.not_le_iff_exists.mp hC
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hT
  obtain ⟨s, hs⟩ := hv₀ (Submodule.Quotient.mk a)
  obtain ⟨t, ht⟩ := hv₀ (Submodule.Quotient.mk c)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply haT
    rw [← Submodule.Quotient.mk_eq_zero T, ← hs, zero_smul]
  have hdiff : c - (t * s⁻¹) • a ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero T, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      ← hs, ← ht, smul_smul, mul_assoc, inv_mul_cancel₀ hs0, mul_one, sub_self]
  have hsum : c - (t * s⁻¹) • a ∈ A ⊔ C :=
    Submodule.sub_mem _ (Submodule.mem_sup_right hcC)
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ haA))
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hmod (Submodule.mem_inf.mpr ⟨hsum, hdiff⟩))
  rw [Submodule.mem_inf] at hx hy
  have hw : c - y = (t * s⁻¹) • a + x := by
    calc c - y = (c - (t * s⁻¹) • a - (x + y)) + (t * s⁻¹) • a + x := by abel
      _ = (t * s⁻¹) • a + x := by rw [hxy, sub_self, zero_add]
  have hwA : c - y ∈ A := hw ▸ Submodule.add_mem _ (Submodule.smul_mem _ _ haA) hx.1
  have hwC : c - y ∈ C := Submodule.sub_mem _ hcC hy.1
  intro h
  apply hcT
  have hwT : c - y ∈ T := h (Submodule.mem_inf.mpr ⟨hwA, hwC⟩)
  simpa using Submodule.add_mem _ hwT hy.2

theorem gen_core_meet {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (T : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (A C : Subrepresentation ρ)
    (hmod : (A ⊔ C).toSubmodule ⊓ T ≤ A.toSubmodule ⊓ T ⊔ C.toSubmodule ⊓ T)
    (hA : ¬ A.toSubmodule ≤ T) (hC : ¬ C.toSubmodule ≤ T) :
    ¬ (A ⊓ C).toSubmodule ≤ T := by
  rw [Subrepresentation.toSubmodule_sup] at hmod
  rw [Subrepresentation.toSubmodule_inf]
  exact GlobalTheory.CompanionTheory.RgGuCore.not_inf_le_of_rank_quotient_le_one T A.toSubmodule C.toSubmodule hT hmod hA hC

end GlobalTheory.CompanionTheory.RgGuCore
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HaarConj

theorem conj_measurePreserving : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] (U N : Subgroup G), IsClosed (U : Set G) → (∀ n ∈ N, ∀ u ∈ U, n * u * n⁻¹ ∈ U) → (∀ n ∈ N, ∃ L : Subgroup G, n ∈ L ∧ L ≤ N ∧ IsCompact (L : Set G)) → ∀ [MeasurableSpace U] [BorelSpace U] (μ : MeasureTheory.Measure U) [μ.IsHaarMeasure], ∀ n ∈ N, ∀ c : U → U, (∀ u, (c u : G) = n * u * n⁻¹) → MeasureTheory.MeasurePreserving c μ μ := by
  intro G _ _ _ _ _ _ U N hU hN hL _ _ μ _ n hn c hc
  have hninv : n⁻¹ ∈ N := N.inv_mem hn
  let d : U → U := fun u => ⟨n⁻¹ * u * n⁻¹⁻¹, hN _ hninv _ u.2⟩
  have hdc : ∀ u, d (c u) = u := fun u => Subtype.ext (by simp [d, hc, mul_assoc])
  have hcd : ∀ u, c (d u) = u := fun u => Subtype.ext (by simp [d, hc, mul_assoc])
  have hcmul : ∀ u v, c (u * v) = c u * c v := fun u v => Subtype.ext (by simp [hc, mul_assoc])
  have hcc : Continuous c := by
    refine Topology.IsEmbedding.subtypeVal.continuous_iff.2 ?_
    have : (Subtype.val ∘ c) = fun u : U => n * (u : G) * n⁻¹ := funext hc
    rw [this]
    fun_prop
  have hdc' : Continuous d := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  let e : U ≃* U :=
    { toFun := c, invFun := d, left_inv := hdc, right_inv := hcd, map_mul' := hcmul }
  haveI hH : (μ.map c).IsHaarMeasure := e.isHaarMeasure_map μ hcc hdc'
  haveI : LocallyCompactSpace U := hU.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology U := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨L, hnL, -, hLc⟩ := hL n hn
  obtain ⟨Q, hQc, hQn⟩ := exists_compact_mem_nhds (1 : U)
  let K : Set G := (fun p : G × G => p.1 * p.2 * p.1⁻¹) '' ((L : Set G) ×ˢ (Subtype.val '' Q))
  have hK : IsCompact K := (hLc.prod (hQc.image continuous_subtype_val)).image (by fun_prop)
  let Q' : Set U := Subtype.val ⁻¹' K
  have hQ'c : IsCompact Q' := hU.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hQQ' : Q ⊆ Q' := fun q hq =>
    ⟨(1, (q : G)), ⟨L.one_mem, ⟨q, hq, rfl⟩⟩, by simp⟩
  have hpos : 0 < μ Q' :=
    (MeasureTheory.Measure.measure_pos_of_mem_nhds μ hQn).trans_le (MeasureTheory.measure_mono hQQ')
  have hfin : μ Q' ≠ ⊤ := hQ'c.measure_lt_top.ne
  have hpre : c ⁻¹' Q' = Q' := by
    ext u
    constructor
    · rintro ⟨⟨l, q⟩, ⟨hl, hq⟩, h⟩
      refine ⟨(n⁻¹ * l, q), ⟨L.mul_mem (L.inv_mem hnL) hl, hq⟩, ?_⟩
      have h' : l * q * l⁻¹ = n * (u : G) * n⁻¹ := by
        rw [← hc]
        exact h
      change n⁻¹ * l * q * (n⁻¹ * l)⁻¹ = (u : G)
      calc n⁻¹ * l * q * (n⁻¹ * l)⁻¹ = n⁻¹ * (l * q * l⁻¹) * n := by group
        _ = (u : G) := by rw [h']; group
    · rintro ⟨⟨l, q⟩, ⟨hl, hq⟩, h⟩
      refine ⟨(n * l, q), ⟨L.mul_mem hnL hl, hq⟩, ?_⟩
      have h' : l * q * l⁻¹ = (u : G) := h
      change n * l * q * (n * l)⁻¹ = (c u : G)
      rw [hc, ← h']
      group
  have hmeas : MeasurableSet Q' := hQ'c.measurableSet
  have h1 : μ.map c Q' = μ Q' := by
    rw [MeasureTheory.Measure.map_apply hcc.measurable hmeas, hpre]
  have heq := MeasureTheory.Measure.isMulLeftInvariant_eq_smul (μ.map c) μ
  have h2 : ((MeasureTheory.Measure.haarScalarFactor (μ.map c) μ : NNReal) : ENNReal) * μ Q'
      = 1 * μ Q' := by
    have h3 := congrArg (fun ν : MeasureTheory.Measure U => ν Q') heq
    simp only [MeasureTheory.Measure.smul_apply, h1] at h3
    rw [one_mul]
    exact h3.symm.trans (by simp [ENNReal.smul_def])
  have hκ : MeasureTheory.Measure.haarScalarFactor (μ.map c) μ = 1 := by
    have := (ENNReal.mul_left_inj hpos.ne' hfin).1 h2
    exact_mod_cast this
  refine ⟨hcc.measurable, ?_⟩
  rw [heq, hκ, one_smul]

end GlobalTheory.CompanionTheory.HaarConj
end

section


theorem _root_.GlobalTheory.T.unramified_whittaker_newform : Ad3.R.U2 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char | exact GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char <;> assumption)
end

section


theorem _root_.GlobalTheory.T.central_character_integral_properties : Ad3.R.G1a → Ad3.R.G1 := by
  first | exact @GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing | exact GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing | (intros; apply GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing <;> assumption)
end

section


theorem _root_.GlobalTheory.T.fundamental_domain_description : Ad3.R.D0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain | exact GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain <;> assumption)
end

section


theorem _root_.GlobalTheory.T.fundamental_domain_invariance_of_description : Ad3.R.D0 → Ad3.R.G0 := by
  first | exact @GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain | exact GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain | (intros; apply GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain <;> assumption)
end

section


theorem _root_.GlobalTheory.T.congruence_subgroup_coset_decomposition : Ad3.R.C1 := by
  first | exact @GlobalTheory.CompanionTheory.RankinStepC.c1 | exact GlobalTheory.CompanionTheory.RankinStepC.c1 | (intros; apply GlobalTheory.CompanionTheory.RankinStepC.c1 <;> assumption)
end

section


theorem _root_.GlobalTheory.T.fundamental_domain_integral_central_invariance : Ad3.R.G1a := by
  first | exact @GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts | exact GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts | (intros; apply GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts <;> assumption)
end
