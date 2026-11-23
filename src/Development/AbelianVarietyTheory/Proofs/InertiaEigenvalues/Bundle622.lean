module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle609
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle559
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle557
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
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
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.CrLimit

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem exists_smul_of_dvd {R : Type} [CommRing R] {m n : Type} (c : R) (M : Matrix m n R)
    (h : ∀ i j, c ∣ M i j) : ∃ M' : Matrix m n R, M = c • M' := by
  choose M' hM' using h
  exact ⟨Matrix.of M', by ext i j; simp [hM']⟩

theorem ev_X_dvd_gal (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    bk.ev X ∣ Per.σA (g : GQ l) (bk.ev s) - bk.ev s := by
  obtain ⟨c, hc⟩ := (GlobalTheory.BSP.galois_discMap l K bk).1 (g : GQ l)
  obtain ⟨t, w, e⟩ : ∃ (t : bk.S) (w : Wq l bk.a), s = X * t + C w := ⟨_, _, eq_X_mul_shift_add_const s⟩
  subst e
  rw [map_add (f := _), map_mul, map_add (f := _), map_mul, bk.ev_C, bk.gal_w, hc]
  exact ⟨c * Per.σA (g : GQ l) (bk.ev t) - bk.ev t, by ring⟩

theorem isUnit_inclW_ev_X (bk : BK K) : IsUnit (inclW l (bk.ev X)) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [bk.ev_X, inclW, WittVector.map_teichmuller, WittVector.teichmuller_coeff_zero]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 (GlobalTheory.BSP.FlatDisc.flat_ne_zero bk)

end GlobalTheory.BKLim.CrLimit

namespace GlobalTheory.BKLim.CrLimit

theorem isCr_of_link : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsCr) → F₀.IsCr := by
  intro l _ K bk d N ρ tw F F₀ r hlink hcr g i j
  suffices hx : ∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * inclW l ((F₀.ε g - 1) i j) -
      inclW l (bk.ev X * a) by
    obtain ⟨a, ha⟩ := GlobalTheory.T.ainf_principal_ideal_saturated_closed l (bk.ev X) (isUnit_inclW_ev_X bk) r (inclW l ((F₀.ε g - 1) i j)) hx
    exact ⟨a, inclW_injective ha⟩
  intro n
  obtain ⟨m, hnm, R, G, hT, hRG⟩ := hlink n
  have hk := GlobalTheory.T.breuilKisinLatticeFrame_cocycles_linked l K bk N N d (tw.d' m) n (fun g => (ρ g).val) (fun g => (tw.ρ' m g).val) F₀ (F m)
    (tw.Pi m) R (fun g i j => (pow_dvd_pow _ hnm).trans ((tw.onto m).equi g i j)) hT
  set σ := Per.σA (g : GQ l) with hσ
  set A := R.map bk.ev with hA
  set B := G.map bk.ev with hB
  set ε₀ := F₀.ε g with hε₀
  set ε' := (F m).ε g with hε'
  obtain ⟨D, hD⟩ := exists_smul_of_dvd ((l : Ainf l) ^ n) (ε₀ * A.map σ - A * ε') (hk g)
  obtain ⟨P, hP⟩ := exists_smul_of_dvd ((l : Ainf l) ^ n) (A * B - (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)))
    (fun i j => by
      have h := map_dvd bk.ev (hRG i j)
      have e : (A * B - (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j =
          bk.ev ((R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) := by
        rw [hA, hB, ← Matrix.map_mul]
        simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub,
          map_mul, map_pow, map_natCast]
        split_ifs <;> simp
      rw [e]
      simpa only [map_pow, map_natCast] using h)
  obtain ⟨Z1, hZ1⟩ := exists_smul_of_dvd (bk.ev X) (ε' - 1) (hcr m g)
  obtain ⟨Z2, hZ2⟩ := exists_smul_of_dvd (bk.ev X) (B.map σ - B) (fun i j => by
    simpa only [hB, Matrix.sub_apply, Matrix.map_apply] using ev_X_dvd_gal bk g (G i j))
  have h1 : ε₀ * A.map σ = A * ε' + (l : Ainf l) ^ n • D := (sub_eq_iff_eq_add').1 hD
  have h2 : A * B = (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)) + (l : Ainf l) ^ n • P :=
    (sub_eq_iff_eq_add').1 hP
  have h3 : A.map σ * B.map σ = (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)) + (l : Ainf l) ^ n • P.map σ := by
    rw [← Matrix.map_mul, h2]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_pow, map_natCast]
    split_ifs <;> simp
  have h4 : ε' = 1 + bk.ev X • Z1 := (sub_eq_iff_eq_add').1 hZ1
  have h5 : B.map σ = B + bk.ev X • Z2 := (sub_eq_iff_eq_add').1 hZ2
  have e1 : ε₀ * (A.map σ * B.map σ) = (l : Ainf l) ^ r • ε₀ + (l : Ainf l) ^ n • (ε₀ * P.map σ) := by
    rw [h3, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
  have e2 : ε₀ * (A.map σ * B.map σ) = A * ε' * B.map σ + (l : Ainf l) ^ n • (D * B.map σ) := by
    rw [← Matrix.mul_assoc, h1, Matrix.add_mul, Matrix.smul_mul]
  have e3 : A * ε' * B.map σ = A * B.map σ + bk.ev X • (A * Z1 * B.map σ) := by
    rw [h4, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e4 : A * B.map σ = (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)) + (l : Ainf l) ^ n • P +
      bk.ev X • (A * Z2) := by
    rw [h5, Matrix.mul_add, h2, Matrix.mul_smul]
  have key : (l : Ainf l) ^ r • (ε₀ - 1) = (l : Ainf l) ^ n • (P + D * B.map σ - ε₀ * P.map σ) +
      bk.ev X • (A * Z1 * B.map σ + A * Z2) := by
    have h := e1.symm.trans e2
    rw [e3, e4] at h
    refine eq_of_sub_eq_zero ?_
    rw [← sub_eq_zero.2 h, smul_sub, smul_sub, smul_add, smul_add]
    abel
  have hij := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] at hij
  refine ⟨(A * Z1 * B.map σ + A * Z2) i j, ?_⟩
  have hd : (l : Ainf l) ^ n ∣ (l : Ainf l) ^ r * (ε₀ - 1) i j - bk.ev X * (A * Z1 * B.map σ + A * Z2) i j :=
    ⟨(P + D * B.map σ - ε₀ * P.map σ) i j, by
      simp only [Matrix.add_apply, Matrix.sub_apply] at hij ⊢
      linear_combination hij⟩
  simpa only [map_sub, map_mul, map_pow, map_natCast] using map_dvd (inclW l) hd

end GlobalTheory.BKLim.CrLimit

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.SepFil

variable {l : ℕ} [Fact l.Prime]

theorem ev_eq_zero_iff_pt {e : Per.Fl l} (he : GlobalTheory.MemLoc.IsEps e) (m : ℕ) (y : Per.BdRp l) :
    Per.ev l m y = 0 ↔ GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m ∣ y := by
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  obtain ⟨-, hθ, hu, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have hfil := (GlobalTheory.MemLoc.filtration_eq_xi_pow l e he).1 1
  have hx : GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) = algebraMap (Per.AinfP l) (Per.BdRp l)
      (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e)) := by
    rw [GlobalTheory.MemLoc.aDp, RingHom.comp_apply]
  have hmem : ∀ (n : ℕ) (a : Per.AinfP l), a ∈ Per.kerP l ^ n ↔
      algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n ∣ a := by
    intro n a
    rw [hk, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hback : ∀ (n : ℕ) (w : Per.BdRp l), GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ n ∣ w → Per.ev l n w = 0 := by
    rintro n w ⟨z, rfl⟩
    rw [map_mul, hx, ← map_pow (algebraMap (Per.AinfP l) (Per.BdRp l)), GlobalTheory.MemLoc.CrisUnique.ev_alg,
      Ideal.Quotient.eq_zero_iff_mem.2 ((hmem n _).2 dvd_rfl), zero_mul]
  have hnu : ¬ IsUnit (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e)) := by
    intro h
    have h1 := (hθ _).2 ((hfil (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e))).2 (by rw [pow_one]))
    exact (h.map (Per.θD l)).ne_zero h1
  have hone : ∀ w : Per.BdRp l, Per.ev l 1 w = 0 → GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ∣ w := by
    intro w hw
    by_cases h0 : Per.θD l w = 0
    · have h1 := (hfil w).1 ((hθ w).1 h0)
      rwa [pow_one] at h1
    · exfalso
      have h1 := (hu w h0).map (Per.ev l 1)
      rw [hw, isUnit_zero_iff, eq_comm, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 1)),
        Ideal.Quotient.eq_zero_iff_mem, hmem, pow_one] at h1
      apply hnu
      rw [hx]
      exact (isUnit_of_dvd_one h1).map _
  have hdense : ∀ (n : ℕ) (w : Per.BdRp l), ∃ (a : Per.AinfP l) (z : Per.BdRp l),
      w = algebraMap (Per.AinfP l) (Per.BdRp l) a + GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ n * z := by
    intro n w
    induction n with
    | zero => exact ⟨0, w, by rw [map_zero, pow_zero, one_mul, zero_add]⟩
    | succ n ih =>
      obtain ⟨a, z, hz⟩ := ih
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 z)
      obtain ⟨z', hz'⟩ := hone (z - algebraMap (Per.AinfP l) (Per.BdRp l) b) (by
        rw [map_sub, GlobalTheory.MemLoc.CrisUnique.ev_alg, hb, sub_self])
      refine ⟨a + algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n * b, z', ?_⟩
      rw [map_add (f := _), map_mul, map_pow, ← hx, pow_succ, mul_assoc, ← hz', hz]
      ring
  refine ⟨fun hy ↦ ?_, hback m y⟩
  obtain ⟨a, z, hz⟩ := hdense m y
  have h1 := hback m _ (dvd_mul_right (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m) z)
  rw [hz, map_add (f := _), h1, add_zero, GlobalTheory.MemLoc.CrisUnique.ev_alg, Ideal.Quotient.eq_zero_iff_mem, hmem] at hy
  rw [hz]
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [hx, ← map_pow]
  exact map_dvd _ hy

theorem dvd_of_forall_near {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) (m : ℕ)
    (c : Per.BdRp l)
    (h : ∀ r : ℕ, ∃ (a : Ainf l) (z : Per.BdRp l),
      c - (l : Per.BdRp l) ^ r * GlobalTheory.MemLoc.aDp l a = GlobalTheory.MemLoc.aDp l d ^ m * z) :
    GlobalTheory.MemLoc.aDp l d ^ m ∣ c := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.CrisUnique.exists_isEps l
  have hk := GlobalTheory.MemLoc.ker_theta_eq_span_xi he
  have hxd : GlobalTheory.MemLoc.xi e ∣ d := by
    rw [← Ideal.mem_span_singleton, ← hk, ← hd]
    exact Ideal.mem_span_singleton_self d
  have hdx : d ∣ GlobalTheory.MemLoc.xi e := by
    rw [← Ideal.mem_span_singleton, hd, hk]
    exact Ideal.mem_span_singleton_self _
  have hev : ∀ y : Per.BdRp l, Per.ev l m y = 0 ↔ GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m ∣ y :=
    ev_eq_zero_iff_pt he m
  have h0 : Per.ev l m c = 0 := by
    refine GlobalTheory.MemLoc.CrisUnique.sep m _ fun r ↦ ?_
    obtain ⟨a, z, hz⟩ := h r
    refine ⟨a, ?_⟩
    have h1 : Per.ev l m (GlobalTheory.MemLoc.aDp l d ^ m * z) = 0 :=
      (hev _).2 (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (map_dvd _ hxd) m) z)
    rw [← hz, map_sub, sub_eq_zero, map_mul, map_pow, map_natCast,
      GlobalTheory.MemLoc.CrisUnique.ev_aDp] at h1
    exact h1
  exact (pow_dvd_pow_of_dvd (map_dvd _ hdx) m).trans ((hev c).1 h0)

end GlobalTheory.BKReal.SepFil

namespace GlobalTheory.BKReal.SepFil

theorem dvd_of_forall_near_OD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ) (w : OD l O),
    (∀ k : ℕ, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ w - (l : OD l O) ^ k * toOD l O y) →
    ϖ.iAl O K (EIn l e _) ^ m ∣ w := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ m w h
  have hE : ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) :=
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))
  set d := ϖ.ev 1 (eis l 1 e) with hd_def
  have hd : Ideal.span {d} = RingHom.ker (Per.θ l) := ϖ.span_ev_eis 1
  have hξ : ϖ.iAl O K (EIn l e _) ^ m = (1 : O) ⊗ₜ[ℤ_[l]] (GlobalTheory.MemLoc.aDp l d ^ m) := by
    rw [hE, Algebra.TensorProduct.tmul_pow, one_pow]
    rfl
  rw [hξ] at h ⊢
  let b := Module.Free.chooseBasis ℤ_[l] O
  have key : ∀ i, GlobalTheory.MemLoc.aDp l d ^ m ∣ GlobalTheory.Decompl.crd b i w := by
    intro i
    refine dvd_of_forall_near hd m _ fun r ↦ ?_
    obtain ⟨y, z, hz⟩ := h r
    refine ⟨GlobalTheory.Decompl.crd b i y, GlobalTheory.Decompl.crd b i z, ?_⟩
    have h1 := congrArg (GlobalTheory.Decompl.crd b i) hz
    have h2 : GlobalTheory.Decompl.crd b i (toOD l O y) = GlobalTheory.MemLoc.aDp l (GlobalTheory.Decompl.crd b i y) :=
      GlobalTheory.Decompl.crd_map b (ainfToBdRp l) i y
    rw [LinearMap.map_sub, ← Nat.cast_pow, GlobalTheory.Decompl.crd_natCast_mul, GlobalTheory.Decompl.crd_mul, h2,
      Nat.cast_pow] at h1
    exact h1
  choose c hc using key
  refine ⟨∑ j, b j ⊗ₜ[ℤ_[l]] c j, GlobalTheory.Decompl.ext_crd b fun i ↦ ?_⟩
  rw [GlobalTheory.Decompl.crd_mul, GlobalTheory.Decompl.crd_sum, ← hc i]

end GlobalTheory.BKReal.SepFil
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

section Bounded

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]


omit [IsUnitBall O K] in
theorem norm_tail_mul_rad_le {f : K⟦X⟧} {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ n, ‖coeff n f‖ * rad l (1 / e) ^ n ≤ b) (n : ℕ) :
    ‖tail l e f n‖ * rad l (1 / e) ^ n ≤ b := by
  have hρ := pow_pos (rad_pos l (1 / e)) n
  rw [← le_div_iff₀ hρ]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (div_nonneg hb hρ.le) fun j => ?_
  rw [le_div_iff₀ hρ, norm_term_eq]
  exact hf _

theorem coeff_sub_E_mul_quotE_of_lt [CompleteSpace K] {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) {n : ℕ}
    (hn : n < e) : coeff n (f - E K l e * quotE l e f) = tail l e f n := by
  rw [tail_rec l e hf n, map_sub, E, add_mul, map_add (f := _), coeff_X_pow_mul', if_neg (by omega),
    ← map_natCast (C : K →+* K⟦X⟧) l, coeff_C_mul, quotE, coeff_mk]
  ring

theorem norm_coeff_mul_rad_le_of_mem_S {f : K⟦X⟧} (hf : f ∈ S O K e) (n : ℕ) :
    ‖coeff n f‖ * rad l (1 / e) ^ n ≤ 1 := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hf.1 n)
  refine le_trans ?_ (norm_pow_le_norm_factorial (K := K) l (n / e))
  rw [← rad_pow (K := K) l e, ← pow_mul]
  exact pow_le_pow_of_le_one (rad_nonneg _ _) (rad_le_one l (by positivity)) (Nat.mul_div_le n e)

theorem exists_bdd_div_E_pow [CompleteSpace K] (m : ℕ) {f : K⟦X⟧} (hf : f ∈ Rpi O K l e)
    {b : ℝ} (hb : 0 ≤ b) (hfb : ∀ n, ‖coeff n f‖ * rad l (1 / e) ^ n ≤ b) :
    ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ b * ‖(l : K)‖⁻¹ ^ m) ∧
      ∃ h ∈ Rpi O K l e, f = g + E K l e ^ m * h := by
  induction m generalizing f b with
  | zero => exact ⟨0, fun n => by simpa using hb, f, hf, by simp⟩
  | succ m ih =>
    have hl0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
    have hl1 : ‖(l : K)‖ < 1 := norm_l_lt_one l
    have hρe : rad l (1 / e) ^ e = ‖(l : K)‖ := rad_pow l e
    have hρ0 : 0 < rad l (1 / e) := rad_pos l _
    have hρ1 : rad l (1 / e) ≤ 1 := rad_le_one l (by positivity)
    have htail := norm_tail_mul_rad_le l e hb hfb
    have hq : ∀ n, ‖coeff n (quotE l e f)‖ * rad l (1 / e) ^ n ≤ b * ‖(l : K)‖⁻¹ := fun n => by
      have := htail (n + e)
      rw [pow_add, hρe] at this
      rw [quotE, coeff_mk, le_mul_inv_iff₀ hl0]
      simpa [mul_assoc] using this
    obtain ⟨g1, hg1, h1, hh1, hq1⟩ :=
      ih (quotE_mem_Rpi l e hf) (mul_nonneg hb (inv_nonneg.2 hl0.le)) hq
    have hpow : ‖(l : K)‖⁻¹ ≤ ‖(l : K)‖⁻¹ ^ (m + 1) := by
      simpa using pow_le_pow_right₀ (one_le_inv₀ hl0 |>.2 hl1.le) (Nat.succ_le_succ (Nat.zero_le m))
    refine ⟨(f - E K l e * quotE l e f) + E K l e * g1, fun n => ?_, h1, hh1, ?_⟩
    · rw [map_add (f := _)]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rcases lt_or_ge n e with hn | hn
        · rw [coeff_sub_E_mul_quotE_of_lt l e hf hn]
          have h2 := htail n
          have h3 : ‖(l : K)‖ ≤ rad l (1 / e) ^ n := by
            rw [← hρe]; exact pow_le_pow_of_le_one hρ0.le hρ1 hn.le
          have h4 : ‖tail l e f n‖ ≤ b * ‖(l : K)‖⁻¹ := by
            rw [le_mul_inv_iff₀ hl0]
            exact (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans h2
          exact h4.trans (mul_le_mul_of_nonneg_left hpow hb)
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
          rw [coeff_sub_E_mul_quotE l e hf, norm_zero]
          positivity
      · have hE : ∀ n, ‖coeff n (E K l e)‖ * (1 : ℝ) ≤ 1 := fun n => by
          simpa using (E_mem l e (A O K)) n
        have := norm_coeff_mul_le (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
          (fun _ _ => by simp) (a := 1) (b := b * ‖(l : K)‖⁻¹ * ‖(l : K)‖⁻¹ ^ m) zero_le_one
          (by positivity) hE (g := g1) (fun n => by rw [mul_one]; exact hg1 n) n
        have e' : (1 : ℝ) * (b * ‖(l : K)‖⁻¹ * ‖(l : K)‖⁻¹ ^ m) = b * ‖(l : K)‖⁻¹ ^ (m + 1) := by
          ring
        rw [mul_one, e'] at this
        exact this
    · linear_combination E K l e * hq1

end Bounded

end GlobalTheory.BK

namespace GlobalTheory.BKReal

open PowerSeries GlobalTheory.BK

theorem exists_l_pow_iHat_toHatS_sub_dvd (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e)
    [CompleteSpace K] (m : ℕ) (s : S O K e) :
    ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣
      (l : OD l O) ^ m * ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) -
        toOD l O y := by
  obtain ⟨g, hg, h, hh, hs⟩ := exists_bdd_div_E_pow l e m (S_le_R l e s.2) zero_le_one
    (norm_coeff_mul_rad_le_of_mem_S l e s.2)
  have hl0 : ‖(l : K)‖ ≠ 0 := norm_ne_zero_iff.2 (GlobalTheory.BK.l_ne_zero (K := K) l)
  have hG : C ((l : K) ^ m) * g ∈ A O K := fun n => by
    rw [coeff_C_mul, norm_mul, norm_pow]
    calc _ ≤ ‖(l : K)‖ ^ m * (1 * ‖(l : K)‖⁻¹ ^ m) := by gcongr; exact hg n
      _ = 1 := by rw [one_mul, ← mul_pow, mul_inv_cancel₀ hl0, one_pow]
  have hH : C ((l : K) ^ m) * h ∈ Rpi O K l e := mul_mem (HasK.C_mem _) hh
  have key : (l : Rpi O K l e) ^ m * Subalgebra.inclusion (invL_S_le_Rpi l e)
      (algebraMap (S O K e) (invL l (S O K e)) s) =
      ⟨_, A_le_Rpi l e hG⟩ + EIn l e (Rpi O K l e) ^ m * ⟨_, hH⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_pow, SubringClass.coe_natCast,
      Subalgebra.coe_inclusion, coe_algebraMap_away, coe_EIn, map_pow, map_natCast]
    rw [hs]
    ring
  have e1 : ϖ.iHat O K (toHat O K l e ⟨_, A_le_Rpi l e hG⟩) = toOD l O (ϖ.iA O K ⟨_, hG⟩) :=
    (congrArg (ϖ.iHat O K)
      (toHat_eq_ofAl l e (g := algebraMap (A O K) (invL l (A O K)) ⟨_, hG⟩) rfl)).trans
      (ϖ.iHat_ofA O K _)
  have e2 : ϖ.iHat O K (Ehat O K l e) = ϖ.iAl O K (EIn l e _) := ϖ.iHat_ofAl O K _
  have h1 : (l : OD l O) ^ m *
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) =
      ϖ.iHat O K (toHat O K l e ((l : Rpi O K l e) ^ m * Subalgebra.inclusion (invL_S_le_Rpi l e)
        (algebraMap (S O K e) (invL l (S O K e)) s))) := by
    simp only [map_mul, map_pow, map_natCast]
    rfl
  refine ⟨ϖ.iA O K ⟨_, hG⟩, ϖ.iHat O K (toHat O K l e ⟨_, hH⟩), ?_⟩
  rw [h1, key]
  rw [map_add (toHat O K l e), map_add (ϖ.iHat O K), map_mul (toHat O K l e), map_mul (ϖ.iHat O K),
    map_pow (toHat O K l e), map_pow (ϖ.iHat O K), toHat_E, e1, e2]
  ring

end GlobalTheory.BKReal
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysExt

theorem exists_ext {A B M N R T ι : Type} [CommRing A] [CommRing B] [CommRing R] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (J : T → B →+* R)
    (v : M →+ (T → ι → R)) (hv : ∀ (w : A) (x : M) τ i, v (w • x) τ i = J τ (f w) * v x τ i) :
    ∃ lam : N →+ (T → ι → R), (∀ (r : B) (y : N) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧
      ∀ x, lam (u x) = v x := by
  letI : Module B (T → ι → R) := Module.compHom (T → ι → R)
    (RingHom.pi fun τ => RingHom.pi fun _ : ι => J τ : B →+* (T → ι → R))
  let v' : M →ₛₗ[f] (T → ι → R) :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun w x => funext fun τ => funext fun i => hv w x τ i }
  obtain ⟨lam, hlam, -⟩ := h (T → ι → R) v'
  exact ⟨lam.toAddMonoidHom, fun r y τ i => congrFun (congrFun (lam.map_smul r y) τ) i, hlam⟩

theorem frob_toAc {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O)
    (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem exists_coord : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → ∃ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧ ∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ EE c hc PP p J g hJ
  let v : EE.M (ϖ.prism a) →+ (ZMod a → ι → K⟦X⟧⟦X⟧) :=
    { toFun := fun x τ i => g (frob K l (c x (τ - 1) i))
      map_zero' := by ext1 τ; ext1 i; simp
      map_add' := fun x y => by ext1 τ; ext1 i; simp }
  obtain ⟨lam, h1, h2⟩ := exists_ext (EE.tr_bc p) J v (fun w x τ i => by
    change g (frob K l (c (w • x) (τ - 1) i)) = J τ (p.f w) * g (frob K l (c x (τ - 1) i))
    have e1 : c (w • x) (τ - 1) i = (toAc t K w (τ - 1) : K⟦X⟧) * c x (τ - 1) i :=
      congrFun (congrFun (hc w x) (τ - 1)) i
    have e2 := hJ τ w
    have e3 := frob_toAc (K := K) t w τ
    rw [e1, map_mul, map_mul]
    exact congrArg (· * _) ((congrArg g e3).trans e2.symm))
  exact ⟨lam, h1, fun x τ i => congrFun (congrFun (h2 x) τ) i⟩

end GlobalTheory.CrysExt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per

theorem _root_.GlobalTheory.T.exists_breuilKisin_module_basis_of_fCrystal : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (T : Lat a O K ϖ), (letI := zlLat T; ∃ E : FCrys l ↥(OL (ϖ.field a)), IsRealisation (ϖ.field a) E ↥T.L.T (actZ T)) → Nonempty (BKMod t ϖ T) := by
  first | exact @GlobalTheory.BKReal.OfCrystal.main | exact GlobalTheory.BKReal.OfCrystal.main | (intros; apply GlobalTheory.BKReal.OfCrystal.main <;> assumption)
end
