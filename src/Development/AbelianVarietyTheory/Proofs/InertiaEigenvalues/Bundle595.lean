module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.WeaklyAdmissibleFiltrations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle568
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle569
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfSat

section Coeff

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

theorem coeff_pow_mul_add (r : ℕ) (w : WittVector p R) (i : ℕ) :
    (((p : WittVector p R) ^ r * w).coeff (i + r)) = (w.coeff i) ^ (p ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h : (p : WittVector p R) ^ (r + 1) * w
        = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ r * w)) := by
      rw [WittVector.verschiebung_frobenius]; ring
    rw [h, show i + (r + 1) = (i + r).succ by omega, WittVector.verschiebung_coeff_succ,
      WittVector.coeff_frobenius_charP, ih, ← pow_mul, pow_succ]

theorem coeff_pow_mul_lt (n : ℕ) (w : WittVector p R) :
    ∀ j, j < n → ((p : WittVector p R) ^ n * w).coeff j = 0 := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    have h : (p : WittVector p R) ^ (n + 1) * w
        = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ n * w)) := by
      rw [WittVector.verschiebung_frobenius]; ring
    rw [h]
    cases j with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ j =>
      rw [WittVector.verschiebung_coeff_succ, WittVector.coeff_frobenius_charP, ih j (by omega),
        zero_pow hp.out.ne_zero]

theorem coeff_eq_of_dvd {n : ℕ} {u v : WittVector p R} (h : (p : WittVector p R) ^ n ∣ u - v)
    (j : ℕ) (hj : j < n) : u.coeff j = v.coeff j := by
  obtain ⟨w, hw⟩ := h
  have hz : WittVector.truncate n (u - v) = 0 := by
    ext k
    rw [WittVector.coeff_truncate, hw, coeff_pow_mul_lt n w k k.2]
    simp
  have ht : WittVector.truncate n u = WittVector.truncate n v := by
    rw [map_sub, sub_eq_zero] at hz; exact hz
  have := congrArg (TruncatedWittVector.coeff (⟨j, hj⟩ : Fin n)) ht
  simpa [WittVector.coeff_truncate] using this

end Coeff

variable (l : ℕ) [Fact l.Prime]

theorem exists_of_pow_eq (r : ℕ) (d : Cb l) (b : OCb l)
    (h : d ^ (l ^ r) = algebraMap (OCb l) (Cb l) b) : ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = d := by
  refine ⟨(iterateFrobeniusEquiv (OCb l) l r).symm b, ?_⟩
  apply iterateFrobenius_inj (Cb l) l r
  rw [iterateFrobenius_def, iterateFrobenius_def, h, ← map_pow]
  congr 1
  have := (iterateFrobeniusEquiv (OCb l) l r).apply_symm_apply b
  rwa [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at this

theorem mem_range_of_pow_mul (r : ℕ) (y : WCb l)
    (hy : ∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * y - inclW l a) :
    ∃ a : Ainf l, y = inclW l a := by
  have hc : ∀ i, ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = y.coeff i := by
    intro i
    obtain ⟨a, ha⟩ := hy (i + r + 1)
    have he := coeff_eq_of_dvd ha (i + r) (by omega)
    rw [coeff_pow_mul_add] at he
    exact exists_of_pow_eq l r _ _ (by rw [he]; exact WittVector.map_coeff _ _ _)
  choose c hc using hc
  refine ⟨WittVector.mk l c, ?_⟩
  ext i
  rw [show inclW l (WittVector.mk l c) = WittVector.map (algebraMap (OCb l) (Cb l)) (WittVector.mk l c)
    from rfl, WittVector.map_coeff]
  exact (hc i).symm

theorem mem_ideal_of_saturated : ∀ (l : ℕ) [Fact l.Prime] (ι : Ainf l), IsUnit (inclW l ι) →
    ∀ (r : ℕ) (x : WCb l), (∀ n : ℕ, ∃ a : Ainf l,
      (l : WCb l) ^ n ∣ (l : WCb l) ^ r * x - inclW l (ι * a)) →
    ∃ a : Ainf l, x = inclW l (ι * a) := by
  intro l _ ι hu r x hx
  obtain ⟨u, hu⟩ := hu
  obtain ⟨a, ha⟩ := mem_range_of_pow_mul l r (↑u⁻¹ * x) (by
    intro n
    obtain ⟨a, w, hw⟩ := hx n
    refine ⟨a, ↑u⁻¹ * w, ?_⟩
    have : (l : WCb l) ^ r * (↑u⁻¹ * x) - inclW l a
        = ↑u⁻¹ * ((l : WCb l) ^ r * x - inclW l (ι * a)) := by
      rw [map_mul, ← hu, mul_sub]
      rw [← mul_assoc (↑u⁻¹ : WCb l) (↑u) _, Units.inv_mul, one_mul]
      ring
    rw [this, hw]; ring)
  refine ⟨a, ?_⟩
  rw [map_mul, ← ha, ← hu, ← mul_assoc, Units.mul_inv, one_mul]

end GlobalTheory.AinfSat
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.DdREqDcris

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem ιV_mulVB (c : K₀) (d : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := V) d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [mulVdR, ιV, mulVB, ← IsScalarTower.algebraMap_apply]

theorem act_mulVB (g : G) (c : K₀) (d : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (actVB PD ρ g d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [actVB, mulVB]

theorem mulVB_mem (c : K₀) {d : V ⊗[Qp] B} (hd : d ∈ Dcris PD ρ) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d ∈ Dcris PD ρ := by
  rw [CrisDR.mem_Dcris_iff] at hd ⊢
  intro g
  rw [act_mulVB, hd g]

theorem mulVdR_one (y : V ⊗[Qp] BdR) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) 1 y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [mulVdR]

theorem ιV_injective : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro d hd
  refine CrisDR.eq_zero_of_sum PD (LL := LL) (m := 1) (fun _ => (1 : K)) ?_ (fun _ => d) ?_ 0
  · intro b hb i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    apply PD.ι_inj
    simpa using hb
  · simp [hd]

theorem map_Dcris_eq (hb : Function.Surjective (algebraMap K₀ K))
    (h : ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (c i) (ιV PD (LL := LL) (V := V) (d i))) :
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ := by
  apply le_antisymm
  · rintro _ ⟨d, hd, rfl⟩
    have := CrisDR.mul_ι_mem PD ρ (1 : K) hd
    rwa [mulVdR_one] at this
  · intro y hy
    obtain ⟨m, c, d, hd, rfl⟩ := h y hy
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c₀, hc₀⟩ := hb (c i)
    rw [← hc₀, ← ιV_mulVB]
    exact Submodule.mem_map_of_mem (mulVB_mem PD ρ c₀ (hd i))

theorem FildR_eq (hb : Function.Surjective (algebraMap K₀ K))
    (h : (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a = (FilCris PD ρ a ⊓ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map
      (ιV PD (LL := LL) (V := V)) := by
  apply le_antisymm
  · rintro y ⟨⟨hy, hτ⟩, hF⟩
    rw [← h] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    refine Submodule.mem_map_of_mem ⟨⟨hd, hF⟩, hd, ?_⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hτ ⊢
    intro c
    apply ιV_injective PD (LL := LL)
    rw [ιV_mulVB, hτ, map_smul]
    rfl
  · rintro _ ⟨d, ⟨⟨hd, hF⟩, -, hτ⟩, rfl⟩
    refine ⟨⟨h ▸ Submodule.mem_map_of_mem hd, ?_⟩, hF⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hτ ⊢
    intro c
    obtain ⟨c₀, rfl⟩ := hb c
    rw [← ιV_mulVB, hτ, map_smul]
    rfl

end Abstract

theorem map_Dcris_eq_DdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → (Dcris (P.PD K) ρ).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) = DdR (P.PD K) ρ ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V ∧ ∀ a : ℤ, FildR (P.PD K) ρ τ a = (FilCris (P.PD K) ρ a ⊓ DcrisL (P.PD K) ρ (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) := by
  intro l _ P AI T K LL hb V _ _ _ _ _ ρ hc
  obtain ⟨hdr, hspan⟩ := CrisDR.isDR_of_isCrys l P AI T K LL V ρ hc
  have h := map_Dcris_eq (P.PD K) ρ hb.2 hspan
  refine ⟨h, fun τ => ?_⟩
  obtain ⟨h1, -, h2⟩ := (GlobalTheory.T.deRhamComponents_crystallineLetters_finrank l P AI T K LL V ρ).1 τ
  exact ⟨h1, h2 hdr, FildR_eq (P.PD K) ρ hb.2 h τ⟩

end GlobalTheory.Per.DdREqDcris
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CrysCoordDR

variable {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
  [IsScalarTower ℤ_[l] ℚ_[l] V]

def basisQ (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤) {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] T) : Module.Basis (Fin d) ℚ_[l] V :=
  Module.Basis.mk (v := fun i => (b i : V))
    ((b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)).localization ℚ_[l]
      (nonZeroDivisors ℤ_[l]))
    (by
      rw [← hT]
      refine Submodule.span_le.2 fun x hx => ?_
      have h := b.sum_repr ⟨x, hx⟩
      have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : V) := by
        have := congrArg Subtype.val h
        rw [AddSubmonoidClass.coe_finsetSum] at this
        simp only [SetLike.val_smul] at this
        exact this.symm
      rw [hx']
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem basisQ_apply (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤) {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] T) (i : Fin d) : basisQ T hT b i = (b i : V) := by
  unfold basisQ
  exact Module.Basis.mk_apply _ _ _

end GlobalTheory.CrysCoordDR

noncomputable section

namespace GlobalTheory.CrysCoordDR

variable {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
  {B : Type} [CommRing B] [Algebra ℚ_[l] B]

def coord {d : ℕ} (e : Module.Basis (Fin d) ℚ_[l] V) (r : Fin d) : V ⊗[ℚ_[l]] B →ₗ[ℚ_[l]] B :=
  (TensorProduct.lid ℚ_[l] B).toLinearMap ∘ₗ TensorProduct.map (e.coord r) LinearMap.id

theorem coord_tmul {d : ℕ} (e : Module.Basis (Fin d) ℚ_[l] V) (r : Fin d) (v : V) (x : B) :
    coord e r (v ⊗ₜ x) = e.repr v r • x := by
  simp [coord]

theorem coord_mulLeft {d : ℕ} (e : Module.Basis (Fin d) ℚ_[l] V) (r : Fin d) (c : B)
    (x : V ⊗[ℚ_[l]] B) :
    coord e r (AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V)
      (LinearMap.mulLeft ℚ_[l] c) x) = c * coord e r x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp [coord_tmul, mul_smul_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]

theorem coord_mem {d : ℕ} (e : Module.Basis (Fin d) ℚ_[l] V) (r : Fin d) (F : Submodule ℚ_[l] B)
    (x : V ⊗[ℚ_[l]] B)
    (hx : x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) F.subtype)) :
    coord e r x ∈ F := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simpa [coord_tmul] using F.smul_mem (e.repr v r) y.2
  | add x y hx hy => simpa only [map_add (f := _)] using F.add_mem hx hy

theorem coord_map {d : ℕ} (e : Module.Basis (Fin d) ℚ_[l] V) (s : Fin d) (f : V →ₗ[ℚ_[l]] V)
    (τ : B →ₗ[ℚ_[l]] B) (x : V ⊗[ℚ_[l]] B) :
    coord e s (AlgebraTensorModule.map f τ x) =
      ∑ r, LinearMap.toMatrix e e f s r • τ (coord e r x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y =>
    simp only [AlgebraTensorModule.map_tmul, coord_tmul, map_smul, smul_smul]
    rw [← Finset.sum_smul, ← LinearMap.toMatrix_mulVec_repr e e f v]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add, Finset.sum_add_distrib]

end GlobalTheory.CrysCoordDR

noncomputable section

namespace GlobalTheory.CrysCoordDR

theorem toMatrix_basisQ {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {G : Type} [Group G]
    {ρ : Representation ℚ_[l] G V} (L : Lattice (O := ℤ_[l]) ρ) {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] ↥L.T) (g : G) (s r : Fin d) :
    LinearMap.toMatrix (basisQ L.T L.span b) (basisQ L.T L.span b) (ρ g) s r =
      ((LinearMap.toMatrix b b (actT L g) s r : ℤ_[l]) : ℚ_[l]) := by
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have h : ρ g (basisQ L.T L.span b r) =
      ∑ s', ((b.repr (actT L g (b r)) s' : ℤ_[l]) : ℚ_[l]) • basisQ L.T L.span b s' := by
    have := congrArg Subtype.val (b.sum_repr (actT L g (b r)))
    rw [AddSubmonoidClass.coe_finsetSum] at this
    simp only [SetLike.val_smul] at this
    simp only [basisQ_apply]
    rw [show ρ g (b r : V) = ((actT L g (b r) : ↥L.T) : V) from rfl, ← this]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [← algebraMap_smul ℚ_[l] (b.repr (actT L g (b r)) s') ((b s' : ↥L.T) : V)]
    rfl
  rw [h, Module.Basis.repr_sum_self]

end GlobalTheory.CrysCoordDR

open GlobalTheory.CrysCoordDR in
theorem GlobalTheory.crysLattice_basis_mem_sum_fil_dR : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), ∀ j : Fin d, ∃ (m : ℕ) (k : Fin m → ℤ) (c : Fin m → Per.BdR l) (v : Fin m → Fin d → Per.BdR l), (∀ i (g : ↥(GK K)), ((LinearMap.toMatrix b b (actT L g)).map (Per.zD l)).mulVec (fun r => Per.σD (g : GQ l) (v i r)) = v i) ∧ (∀ i r, v i r ∈ Per.FilD l (k i)) ∧ (∀ i, c i ∈ Per.FilD l (-k i)) ∧ (Pi.single j 1 : Fin d → Per.BdR l) = ∑ i, c i • v i := by
  intro l _ K P AI T V _ _ _ _ _ ρ L hcrys d b j
  have hy : ((b j : ↥L.T) : V) ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 :=
    ⟨((b j : ↥L.T) : V) ⊗ₜ ⟨1, (P.PD K).one_mem⟩, by simp [AlgebraTensorModule.map_tmul]⟩
  obtain ⟨m, k, c, dd, hdd, hsum⟩ := GlobalTheory.T.crystalline_filtered_deRham_comparison l P AI T K V ρ hcrys 0 _ hy
  refine ⟨m, k, fun i => T.eD (c i), fun i r => T.eD (coord (basisQ L.T L.span b) r (dd i)),
    ?_, ?_, ?_, ?_⟩
  · intro i g
    funext s
    have hinv : actVdR (P.PD K) ρ g (dd i) = dd i := by
      have := (hdd i).1
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at this
      exact this g
    show _ = T.eD (coord (basisQ L.T L.span b) s (dd i))
    conv_rhs => rw [← hinv]

    rw [actVdR, coord_map, map_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [toMatrix_basisQ, Algebra.smul_def, map_mul, T.zD]
    congr 1
    change _ = T.eD ((P.PD K).actdR g _)
    rw [P.PD_actdR K g, T.actD]
  · intro i r
    rw [← T.fil K]
    exact coord_mem _ r (((P.PD K).Fil (k i)).restrictScalars ℚ_[l]) _ (hdd i).2.1
  · intro i
    rw [← T.fil K]
    simpa using (hdd i).2.2
  · funext r
    have h1 := congrArg (coord (basisQ L.T L.span b) r) hsum

    rw [← basisQ_apply L.T L.span b j, coord_tmul, map_sum] at h1
    simp only [coord_mulLeft, Module.Basis.repr_self] at h1
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have h2 := congrArg T.eD h1

    rw [map_sum] at h2
    simp only [map_mul] at h2
    rw [← h2]
    by_cases hr : r = j
    · subst hr; simp
    · simp [hr, Finsupp.single_apply, Pi.single_apply, Ne.symm hr]
end
end
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.exists_uniformiser_family_hostField_integers : ∀ (D : D7), ∃ ϖ : Pl D.host.E → 𝓞 D.host.E, ∀ PP : Pl D.host.E, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2 := by
  first | exact @GlobalTheory.exists_uniformiser_family_host | exact GlobalTheory.exists_uniformiser_family_host | (intros; apply GlobalTheory.exists_uniformiser_family_host <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.span_conj_unitaryLieAlgebra_realPlace_eq_top : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau) (Fm : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit Fm → Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} = ⊤ := by
  first | exact @GlobalTheory.LieSpanConj.span_conj_lieAt_eq_top | exact GlobalTheory.LieSpanConj.span_conj_lieAt_eq_top | (intros; apply GlobalTheory.LieSpanConj.span_conj_lieAt_eq_top <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.exists_nat_integral_frame_of_uniformizer_mul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (ϖ : 𝓞 D.host.E), ϖ ≠ 0 → ∃ k : ℕ, 0 < k ∧ ∀ u : WO S T, IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) → IsIntM (frMapO S T βS βT (k • u)) := by
  first | exact @GlobalTheory.FlatLift.kmul_int | exact GlobalTheory.FlatLift.kmul_int | (intros; apply GlobalTheory.FlatLift.kmul_int <;> assumption)
end
