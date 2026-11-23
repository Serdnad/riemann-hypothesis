module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle728
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle671
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle742
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle568
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.PUnit
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle358

@[expose] public section

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem chart_square_presents : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), Presents k c.x₂ c.nil₂ ∧ ∀ z : ∀ n, G.A n ⊗[k] G.A n,
      (∀ n, pullbackTwo (G.res n) (z (n + 1)) = z n) → ∃! s, ∀ n, c.ev₂ n s = z n := by
  intro p k _ d G c
  have ht := fun n => GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct k (Fin d) (Fin d) (G.A n) (G.A n) (c.x n) (c.nil n) (c.x n)
    (c.nil n) (c.nil₂ n) (c.presents.1 n) (c.presents.1 n)
  refine ⟨⟨fun n => (ht n).1, fun N => ?_⟩, fun z hz => ?_⟩
  · obtain ⟨n, hn⟩ := c.presents.2 N
    exact ⟨n, (ht n).2 N hn hn⟩
  · let r : ∀ n, G.A n.succ ⊗[k] G.A n.succ →ₐ[k] G.A n ⊗[k] G.A n := fun n =>
      Algebra.TensorProduct.map (G.res n : G.A (n + 1) →ₐ[k] G.A n)
        (G.res n : G.A (n + 1) →ₐ[k] G.A n)
    have hr : ∀ n t, r n t = pullbackTwo (G.res n) t := fun n t => by
      induction t with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a b => rfl
    refine GlobalTheory.T.existsUnique_powerSeries_of_compatible_system k (Fin d ⊕ Fin d) (fun n => G.A n ⊗[k] G.A n) c.x₂ c.nil₂ r
      (fun n i => ?_) ⟨fun n => (ht n).1, fun N => ?_⟩ z (fun n => by rw [hr]; exact hz n)
    · rw [hr]
      cases i with
      | inl i => simp [Chart.x₂, c.res]
      | inr i => simp [Chart.x₂, c.res]
    · obtain ⟨n, hn⟩ := c.presents.2 N
      exact ⟨n, (ht n).2 N hn hn⟩

end GlobalTheory
end

section

open IsLocalRing Polynomial
open GlobalTheory.EtC

namespace GlobalTheory

theorem surj_of_strictHenselisation_polynomial : ∀ (T : Type) [CommRing T] (A : Type) [CommRing A]
    [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A →
    (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E)
      (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) →
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra T O) (_ : Algebra (Polynomial T) O)
      (_ : IsScalarTower T (Polynomial T) O) (_ : HenselianLocalRing O)
      (_ : IsSepClosed (IsLocalRing.ResidueField O)) (π : O →ₐ[Polynomial T] A),
      Function.Surjective π ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·))
        (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧
        (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E)
          (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E)
          (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) := by
  intro T _ A _ _ _ _ hSH hA
  obtain ⟨hHA, hsepA⟩ := hSH
  let y : Ideal (Polynomial T) := (maximalIdeal A).comap (algebraMap (Polynomial T) A)
  haveI : y.IsPrime := Ideal.comap_isPrime _ _
  set_option synthInstance.maxHeartbeats 400000 in
  obtain ⟨O, _, algRO, _, hloc, hsc, -, -, -, hind⟩ :=
    GlobalTheory.exists_strictHenselisation (Localization.AtPrime y)
      (SeparableClosure (ResidueField (Localization.AtPrime y)))
  letI algPO : Algebra (Polynomial T) O :=
    ((algebraMap (Localization.AtPrime y) O).comp
      (algebraMap (Polynomial T) (Localization.AtPrime y))).toAlgebra
  letI algTO : Algebra T O := ((algebraMap (Polynomial T) O).comp (algebraMap T (Polynomial T))).toAlgebra
  haveI t1 : IsScalarTower T (Polynomial T) O := IsScalarTower.of_algebraMap_eq' rfl
  haveI t2 : IsScalarTower (Polynomial T) (Localization.AtPrime y) O :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hP := GlobalTheory.indEtale_localPieces_trans (Polynomial T) (Localization.AtPrime y) O
    ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
      fun _ => ⟨(), Algebra.mem_top⟩,
      fun _ => ⟨Polynomial T, inferInstance, inferInstance, inferInstance, y, inferInstance,
        ⟨Subalgebra.topEquiv.symm⟩⟩⟩ hind

  have hRO : (maximalIdeal O).comap (algebraMap (Localization.AtPrime y) O) =
      maximalIdeal (Localization.AtPrime y) := by
    ext x
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
  have hyO : (maximalIdeal O).comap (algebraMap (Polynomial T) O) = y := by
    rw [IsScalarTower.algebraMap_eq (Polynomial T) (Localization.AtPrime y) O, ← Ideal.comap_comap,
      hRO]
    exact Localization.AtPrime.under_maximalIdeal
  have hkO : ∀ r : Polynomial T, algebraMap (Polynomial T) (ResidueField O) r = 0 ↔ r ∈ y := by
    intro r
    rw [IsScalarTower.algebraMap_apply (Polynomial T) O (ResidueField O), ResidueField.algebraMap_eq,
      residue_eq_zero_iff, ← hyO, Ideal.mem_comap]
  have hkA : ∀ r : Polynomial T, algebraMap (Polynomial T) (ResidueField A) r = 0 ↔ r ∈ y := by
    intro r
    rw [IsScalarTower.algebraMap_apply (Polynomial T) A (ResidueField A), ResidueField.algebraMap_eq,
      residue_eq_zero_iff]
    rfl
  letI algyO : Algebra y.ResidueField (ResidueField O) :=
    (Ideal.ResidueField.lift y (algebraMap (Polynomial T) (ResidueField O)) (fun r hr => (hkO r).2 hr)
      (fun r hr => by
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr (fun h => hr ((hkO r).1 h)))).toAlgebra
  haveI : IsScalarTower (Polynomial T) y.ResidueField (ResidueField O) := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap y _ _ _ r).symm
  letI algyA : Algebra y.ResidueField (ResidueField A) :=
    (Ideal.ResidueField.lift y (algebraMap (Polynomial T) (ResidueField A)) (fun r hr => (hkA r).2 hr)
      (fun r hr => by
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr (fun h => hr ((hkA r).1 h)))).toAlgebra
  haveI : IsScalarTower (Polynomial T) y.ResidueField (ResidueField A) := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap y _ _ _ r).symm

  have hsepO : ∀ s : O, IsSeparable y.ResidueField (algebraMap O (ResidueField O) s) := by
    intro s
    obtain ⟨ι, _, _, _, Si, -, hcov, hpc⟩ := hP
    obtain ⟨i, hi⟩ := hcov s
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hpc i
    let F : Localization.AtPrime q →ₐ[Polynomial T] ResidueField O :=
      (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O)).comp ((Si i).val.comp e.toAlgHom)
    let f : B →ₐ[Polynomial T] ResidueField O :=
      F.comp (IsScalarTower.toAlgHom (Polynomial T) B (Localization.AtPrime q))
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨s, hi⟩)
    have hs : algebraMap O (ResidueField O) s = F (IsLocalization.mk' _ a t) := by
      simp only [F, AlgHom.comp_apply, hat]
      simp
    have hft : f t ≠ 0 := by
      have : IsUnit (f t) :=
        (IsLocalization.map_units (Localization.AtPrime q) t).map F
      exact this.ne_zero
    have hmul : F (IsLocalization.mk' _ a t) * f t = f a := by
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← map_mul,
        IsLocalization.mk'_spec]
    have hx : algebraMap O (ResidueField O) s = f a * (f t)⁻¹ := by
      rw [hs, eq_mul_inv_iff_mul_eq₀ hft, hmul]
    rw [hx, ← mem_separableClosure_iff]
    refine mul_mem ?_ (inv_mem ?_) <;> rw [mem_separableClosure_iff] <;>
      exact GlobalTheory.Specialise.sepEtale (Polynomial T) B y _ f _
  haveI : Algebra.IsSeparable y.ResidueField (ResidueField O) := ⟨fun x => by
    obtain ⟨s, rfl⟩ := residue_surjective x
    have := hsepO s
    rwa [ResidueField.algebraMap_eq] at this⟩
  haveI : IsSepClosure y.ResidueField (ResidueField O) := ⟨hsc, inferInstance⟩
  let L := separableClosure y.ResidueField (ResidueField A)
  let e : ResidueField O ≃ₐ[y.ResidueField] L := IsSepClosure.equiv y.ResidueField (ResidueField O) L
  let ι : ResidueField O →ₐ[y.ResidueField] ResidueField A := L.val.comp e.toAlgHom
  let ψ₀ : O →ₐ[Polynomial T] ResidueField A :=
    (ι.restrictScalars (Polynomial T)).comp (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O))
  obtain ⟨π, hπ⟩ := (GlobalTheory.IndEtaleHensel.bijective_residue_comp (Polynomial T) O A hP).2 ψ₀
  refine ⟨O, inferInstance, algTO, algPO, t1, inferInstance, hsc, π, ?_, hP⟩
  intro b
  obtain ⟨E, _, _, _, φ, hb⟩ := hA b
  obtain ⟨e0, rfl⟩ := (AlgHom.mem_range φ).1 hb
  let f : E →ₐ[Polynomial T] ResidueField A :=
    (IsScalarTower.toAlgHom (Polynomial T) A (ResidueField A)).comp φ
  have hfL : ∀ x, f x ∈ L := fun x =>
    mem_separableClosure_iff.2 (GlobalTheory.Specialise.sepEtale (Polynomial T) E y (ResidueField A) f x)
  let g : E →ₐ[Polynomial T] ResidueField O :=
    { toRingHom := (e.symm : L →+* ResidueField O).comp (f.toRingHom.codRestrict L hfL)
      commutes' := fun r => by
        apply e.injective
        change e (e.symm ⟨f (algebraMap _ E r), hfL _⟩) = _
        rw [AlgEquiv.apply_symm_apply]
        apply Subtype.ext
        rw [IsScalarTower.algebraMap_apply (Polynomial T) y.ResidueField (ResidueField O),
          AlgEquiv.commutes]
        change f (algebraMap _ E r) = _
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (Polynomial T) y.ResidueField (ResidueField A)]
        rfl }
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp (Polynomial T) E O).2 g
  have hcomp : π.comp ψ = φ := by
    apply (GlobalTheory.EtaleHensel.bijective_residue_comp (Polynomial T) E A).1
    dsimp only
    ext x
    have h1 := DFunLike.congr_fun hπ (ψ x)
    have h2 := DFunLike.congr_fun hψ x
    simp only [AlgHom.comp_apply] at h1 h2 ⊢
    rw [h1]
    change ι (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O) (ψ x)) = f x
    rw [h2]
    change ((e (e.symm ⟨f x, hfL x⟩) : L) : ResidueField A) = f x
    rw [AlgEquiv.apply_symm_apply]
  exact ⟨ψ e0, DFunLike.congr_fun hcomp e0⟩

end GlobalTheory
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma powerSeries_map_mk' (g : ℂ ≃+* ℂ) (c : ℕ → ℂ) :
    PowerSeries.map (g : ℂ →+* ℂ) (PowerSeries.mk c) = PowerSeries.mk fun n ↦ g (c n) := by
  ext n
  simp

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hser_conj : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F)) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → 0 < N → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) = PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a (m * x) (fun j ↦ κ (π.symm j)) (fun n ↦ g (c n))) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x s N g m π κ c n hk hN ha hga hlev hexp hemb
  have htr : ∀ μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ,
      PowerSeries.map (g : ℂ →+* ℂ) (PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ)) =
        PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a (m * x) fun j ↦ μ (π.symm j)) := by
    intro μ
    rw [powerSeries_map_mk']
    congr 1
    funext j
    exact _root_.GlobalTheory.HilbFam.ecoef_ringEquiv F k 𝔞 𝔟 a₀ a x N g m π μ j hN ha hga hlev
      hexp hemb
  unfold _root_.GlobalTheory.HilbFam.hser
  subst hk

  simp only [map_smul, map_sum, smul_eq_mul, _root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]

  rw [map_mul, map_ratCast, map_sum]
  congr 1
  refine Finset.sum_nbij' (fun μ j ↦ μ (π.symm j)) (fun μ i ↦ μ (π i)) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [Finset.mem_coe, Finset.mem_Iic] at hμ ⊢
    exact fun j ↦ hμ (π.symm j)
  · intro μ hμ
    simp only [Finset.mem_coe, Finset.mem_Iic] at hμ ⊢
    intro i
    simpa using hμ (π i)
  · intro μ _
    funext i
    simp
  · intro μ _
    funext j
    simp
  · intro μ _
    have hcoeff : ∀ φ : PowerSeries ℂ,
        g (PowerSeries.coeff n φ) = PowerSeries.coeff n (PowerSeries.map (g : ℂ →+* ℂ) φ) :=
      fun φ ↦ by
        rw [PowerSeries.coeff_map]
        rfl
    rw [map_mul, map_intCast, hcoeff, map_mul, map_pow, powerSeries_map_mk', htr]
    rw [Equiv.prod_comp π.symm fun i ↦
        _root_.GlobalTheory.HilbFam.rco (2 * s) (κ i) (μ i) * (-1) ^ μ i,
      Equiv.sum_comp π.symm fun i ↦ κ i - μ i]

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

noncomputable def shearSub {F : Type} [Field F] (x : F) : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) where
  toFun v := ![v 0, v 1 - v 0 * x]
  invFun v := ![v 0, v 1 + v 0 * x]
  map_add' v w := by
    ext i; fin_cases i
    · simp
    · simp; ring
  map_smul' c v := by
    ext i; fin_cases i
    · simp
    · simp; ring
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp

theorem shearSub_zero {F : Type} [Field F] (x : F) (v : Fin 2 → F) : shearSub x v 0 = v 0 := rfl

theorem shearSub_one {F : Type} [Field F] (x : F) (v : Fin 2 → F) : shearSub x v 1 = v 1 - v 0 * x := rfl

theorem hasSum_split_shift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (w : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → w ∈ upperHalf F → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * qPow ξ w) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) w 1 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x w hk hc hw
  have hw' : (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) ∈ upperHalf F := by
    intro i
    simpa using hw i
  have hg : gval k (split 𝔞 𝔟 x) w 1 = gval k (split 𝔞 𝔟 0) (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) 1 := by
    have := GlobalTheory.T.hilbertEisensteinValue_linear_change F k (split 𝔞 𝔟 x) (split 𝔞 𝔟 0) (shearSub x) w 1
      (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) 1 1 hk (fun v ↦ by
        change (_ ∧ _) ↔ (_ ∧ _)
        rw [shearSub_zero, shearSub_one, mul_zero, sub_zero]) (fun i ↦ by simp) (fun v i ↦ by
        simp only [coord, shearSub_zero, shearSub_one, Pi.one_apply, map_sub, map_mul]
        push_cast; ring)
    simpa using this
  have h := hc.2.2.2 _ hw'
  rw [hg]
  convert h using 2 with ξ
  rw [mul_assoc]
  congr 1
  unfold eTr qPow
  rw [← Complex.exp_add, ← GlobalTheory.T.sum_realEmbeddings_eq_trace_totallyReal F (ξ * x), ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul]; push_cast; ring

end GlobalTheory.HilbFam
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianSchemeGlobalFormsPrimitive_of_frames : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) → FormSt := by
  first | exact @GlobalTheory.FormsOnAb.formSt_of | exact GlobalTheory.FormsOnAb.formSt_of | (intros; apply GlobalTheory.FormsOnAb.formSt_of <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.h2_structure_base_change_extension : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H2 (OAff s₁) ≃+ GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegTwo R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullbackH2Structure h₁ c c' := by
  first | exact @GlobalTheory.Obs.extCoef_two_equiv | exact GlobalTheory.Obs.extCoef_two_equiv | (intros; apply GlobalTheory.Obs.extCoef_two_equiv <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.h1_structure_base_change_extension : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H1 (OAff s₁) ≃+ GlobalTheory.CatCoh.H1 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegOne R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullO h₁ c c' := by
  first | exact @GlobalTheory.Obs.BC.extO1 | exact GlobalTheory.Obs.BC.extO1 | (intros; apply GlobalTheory.Obs.BC.extO1 <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechPairRestrict_baseChange_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R₀) (φ : X' ⟶ X), (Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2) ∧ ∀ (Y : Scheme.{0}) (ψ : X ⟶ Y), Function.Injective (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 := by
  first | exact @GlobalTheory.Obs.PairExt.pairRes_ext_bijective | exact GlobalTheory.Obs.PairExt.pairRes_ext_bijective | (intros; apply GlobalTheory.Obs.PairExt.pairRes_ext_bijective <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_trace_finiteEtaleGaloisCover_ladic : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, ∃ tr : Hl l (sch.obj Y) n i →ₗ[ℤ_[l]] Hl l (sch.obj X) n i,
  (∀ x, tr (pullHl l (sch.map f) n i x) = Fintype.card G • x) ∧ ∀ y, pullHl l (sch.map f) n i (tr y) = ∑ g, pullHl l (sch.map (a g)) n i y := by
  first | (exact @GlobalTheory.EtC.TrGal.exists_trace_galois) | (exact GlobalTheory.EtC.TrGal.exists_trace_galois) | (intros; apply GlobalTheory.EtC.TrGal.exists_trace_galois  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.coindRes_exists : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R) [Injective J], (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → ∃ (C : Cx R) (ε : sgl ((restr φ).obj ((coind φ).obj J)) ⟶ C), C.IsStrictlyGE 0 ∧ (∀ t, Injective (C.X t)) ∧ QuasiIso ε ∧ ∀ (P : PSh) (n : ℤ), 0 < n → Subsingleton (CohomologyClass (sgl ((free R).obj P)) C n) := by
  intro R S _ _ φ J _ hJ
  haveI := GlobalTheory.T.etaleCoinductionComplexAugmentation_quasiIso R S φ J hJ
  let I : InjectiveResolution ((restr φ).obj ((coind φ).obj J)) :=
    { cocomplex := coindCx φ J
      injective := fun n => GlobalTheory.T.injective_etaleSheafOfLinearMapsFromModule R J ((scalarsRes φ).complex.X n)
      ι := coindAug φ J }
  refine ⟨I.cochainComplex, I.ι', inferInstance, inferInstance, inferInstance, ?_⟩
  intro P n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ x : CohomologyClass (sgl ((free R).obj P)) I.cochainComplex ((k : ℤ) + 1), x = 0 by
    rw [h x, h y]
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective α ((k : ℤ) + 1) (zero_add _) ((k : ℤ) + 1 + 1) rfl
  rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (k : ℤ) rfl]
  have hex : ∀ b, ((scalarsRes φ).complex.d (k + 1) k).hom b = 0 → ∃ a, ((scalarsRes φ).complex.d (k + 2) (k + 1)).hom a = b := by
    intro b hb
    exact ((ShortComplex.moduleCat_exact_iff _).1 ((scalarsRes φ).exact_succ k)) b hb
  have hd1 := I.cochainComplex_d ((k : ℤ) + 1) ((k : ℤ) + 1 + 1) (k + 1) (k + 2) (by simp) (by push_cast; ring)
  rw [hd1] at hf
  have h2 : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫ I.cocomplex.d (k + 1) (k + 2) = 0 := by
    rw [← cancel_mono (I.cochainComplexXIso ((k : ℤ) + 1 + 1) (k + 2) (by push_cast; ring)).inv]
    simpa using hf
  have hf' : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫
      (homSh J).map ((scalarsRes φ).complex.d (k + 2) (k + 1)).op = 0 := by
    rw [← coindCx_d]
    exact h2
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_lift_etaleSheafOfLinearMaps_exact R J ((free R).obj P) (hJ P) _ _ _ _ _ hex _ hf'
  refine ⟨g ≫ (I.cochainComplexXIso (k : ℤ) k rfl).inv, ?_⟩
  rw [I.cochainComplex_d (k : ℤ) ((k : ℤ) + 1) k (k + 1) rfl (by simp)]
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  have hg' : g ≫ I.cocomplex.d k (k + 1) = f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom := by
    rw [← hg, ← coindCx_d]
    rfl
  erw [← Category.assoc, hg', Category.assoc, Iso.hom_inv_id, Category.comp_id]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.supportedSections_tateTwist_resolution : ∀ (q : ℕ) [NeZero q] (i : ℤ) (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i)), (∀ n U, Function.Injective (Sec.map (ι.f n) (U := U))) → (∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔ Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) → ∃ e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (D.X 0) U, IsTwRes q i D e ∧ ∀ U ζ, Sec.map (ι.f 0) (e U ζ) = resGen i ζ := by
  first
  | exact @GlobalTheory.EtC.SuppRes.supp_res
  | exact GlobalTheory.EtC.SuppRes.supp_res
  | (intros; apply GlobalTheory.EtC.SuppRes.supp_res <;> assumption)
end
