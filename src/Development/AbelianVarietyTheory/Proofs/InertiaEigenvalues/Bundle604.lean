module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle584
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle585
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle581
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.deRham_filtered_comparison_coordinates : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsDR (P.PD K) (qRep ρ) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ i, y i ∈ (P.PD K).Fil a) → ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (z : Fin m → Fin d → P.R.BdR), (∀ r, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (z r i)) = z r) ∧ (∀ i, z r i ∈ (P.PD K).Fil (k r)) ∧ b r ∈ (P.PD K).Fil (a - k r)) ∧ y = ∑ r, b r • z r := by
  first | (exact @GlobalTheory.DRFilCoord.filtered_coords) | (exact GlobalTheory.DRFilCoord.filtered_coords) | (intros; apply GlobalTheory.DRFilCoord.filtered_coords  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_invariant_basis_of_isDeRham_lattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsDR (P.PD K) (qRep ρ) → ∃ x : Fin d → Fin d → P.R.BdR, LinearIndependent ↥K.1 x ∧ (∀ j (g : ↥(GK K)), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (x j i)) = x j) ∧ ∀ c : Fin d → P.R.BdR, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c) → c ∈ Submodule.span ↥K.1 (Set.range x) := by
  first | exact @GlobalTheory.DRMat.invariant_basis_of_isDR | exact GlobalTheory.DRMat.invariant_basis_of_isDR | (intros; apply GlobalTheory.DRMat.invariant_basis_of_isDR <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.mvPolynomialDelta_supported_linear_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (i : ℕ), ∀ s ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic (i + 1)) ∧ ∃ a ∈ MvPolynomial.supported A (Set.Iic i), ∃ b ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s - (a * MvPolynomial.X (i + 1) + b) ∈ Ideal.span {(l : MvPolynomial ℕ A)} := by
  first | exact @GlobalTheory.BSP.polyDelta_supported_linear_mod | exact GlobalTheory.BSP.polyDelta_supported_linear_mod | (intros; apply GlobalTheory.BSP.polyDelta_supported_linear_mod <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.prismLocalization_span_nonZeroDivisor_bounded_torsion : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A), GenAway B f d → ∀ M : Submonoid B.A, f ∈ M → B.I.map (algebraMap B.A (Localization M)) = Ideal.span {algebraMap B.A (Localization M) d} ∧ algebraMap B.A (Localization M) d ∈ nonZeroDivisors (Localization M) ∧ ∃ N : ℕ, ∀ (x : Localization M) (m : ℕ), (l : Localization M) ^ m * x ∈ Ideal.span {algebraMap B.A (Localization M) d} → (l : Localization M) ^ N * x ∈ Ideal.span {algebraMap B.A (Localization M) d} := by
  first | exact @GlobalTheory.BSP.locAway_span_nzd_bdd | exact GlobalTheory.BSP.locAway_span_nzd_bdd | (intros; apply GlobalTheory.BSP.locAway_span_nzd_bdd <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.ringHom_eq_of_isAdicCompletionMap : ∀ (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (i : L →+* Q) (J : Ideal L) (JC : Ideal C), IsCompl i J → IsHausdorff JC C → ∀ (h h' : Q →+* C), J.map (h.comp i) ≤ JC → h.comp i = h'.comp i → h = h' := by
  first | exact @GlobalTheory.BSP.ringHom_eq_of_isCompl | exact GlobalTheory.BSP.ringHom_eq_of_isCompl | (intros; apply GlobalTheory.BSP.ringHom_eq_of_isCompl <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.DescFalling

theorem desc_eq_X_pow_smul_nabla_pow {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (v : Vec K a ι) :
    C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v := by
  have hX : ∀ w, C.nabla ((X : K⟦X⟧) • w) = w + (X : K⟦X⟧) • C.nabla w := fun w => by
    have h := C.leibniz (fun _ => X) w
    have e1 : ∀ u : Vec K a ι, ((fun _ => (X : K⟦X⟧)) : ZMod a → K⟦X⟧) • u = (X : K⟦X⟧) • u :=
      fun u => rfl
    have e2 : ((fun _ => PowerSeries.derivative (R := K) (X : K⟦X⟧)) : ZMod a → K⟦X⟧) • w = w := by
      simp only [PowerSeries.derivative_X]
      exact one_smul _ w
    rw [e1, e1, e2] at h
    exact h
  have hcomm : ∀ (j : ℕ) (w : Vec K a ι),
      (C.nabla ^ j) ((X : K⟦X⟧) • C.nabla w) = (X : K⟦X⟧) • (C.nabla ^ (j + 1)) w + j • (C.nabla ^ j) w := by
    intro j
    induction j with
    | zero => intro w; simp
    | succ j ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, ih, map_add (f := _), hX, map_nsmul, pow_succ' C.nabla (j + 1),
        Module.End.mul_apply, pow_succ' C.nabla j, Module.End.mul_apply, succ_nsmul]
      abel
  induction k generalizing v with
  | zero => simp [Conn.desc_zero]
  | succ k ih =>
    rw [Conn.desc_succ, ih, Conn.N_apply, map_sub, hcomm, map_nsmul, add_sub_cancel_right, smul_smul,
      ← pow_succ]

end GlobalTheory.DescFalling
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.BKReal.Conn

theorem pow_apply_smul_nsmul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      k.choose p • ((fun τ => (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  induction k with
  | zero => simp
  | succ k ih =>

    rw [Finset.sum_choose_succ_nsmul
      (fun i j => (fun τ => (⇑(PowerSeries.derivative (R := K)))^[i] (f τ)) • (C.nabla ^ j) v) k,
      pow_succ', mul_apply_eq_comp, ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpk : p ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
    rw [map_nsmul, C.leibniz, smul_add, add_comm]
    congr 2
    · rw [show k + 1 - p = k - p + 1 by omega, pow_succ', mul_apply_eq_comp]
    · congr 1
      funext τ
      rw [Function.iterate_succ_apply']

theorem pow_apply_smul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      (k.choose p : K⟦X⟧) • ((fun τ => (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  rw [pow_apply_smul_nsmul]
  exact Finset.sum_congr rfl fun p _ => (Nat.cast_smul_eq_nsmul K⟦X⟧ _ _).symm

end GlobalTheory.BKReal.Conn
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

theorem _root_.GlobalTheory.T.nabla_pow_apply_smul_leibniz : ∀ {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι), (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1), (k.choose p : K⟦X⟧) • ((fun τ => (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  intro O K _ _ _ _ _ l e a ι _ _ P C k f v
  let D (p : ℕ) (τ : ZMod a) := (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)
  have h (n : ℕ) : (C.nabla ^ n) (f • v) = ∑ p ∈ Finset.range (n + 1),
      n.choose p • (D p • (C.nabla ^ (n - p)) v) := by
    induction n with
    | zero => simp [D]
    | succ n ih =>
      rw [Finset.sum_choose_succ_nsmul (fun i j => D i • (C.nabla ^ j) v) n,
        pow_succ', mul_apply_eq_comp, ih, map_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpn : p ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
      rw [map_nsmul, C.leibniz, smul_add, add_comm]
      congr 2
      · rw [show n + 1 - p = n - p + 1 by omega, pow_succ', mul_apply_eq_comp]
      · congr 1
        funext τ
        exact (Function.iterate_succ_apply' _ _ _).symm
  rw [h k]
  exact Finset.sum_congr rfl fun p _ => (Nat.cast_smul_eq_nsmul K⟦X⟧ _ _).symm
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per Matrix

namespace GlobalTheory.BKReal.Full

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

section Lat

variable {G : Type} [Group G] [TopologicalSpace G] {T T' : LocLat G ℚ_[l] K O}


omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in
theorem latW_smul (f : LatHom T.L T'.L) (r : OW l O) (y : TW (OW l O) T) :
    latW f (r • y) = r • latW f y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]


omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in
theorem latW_frob (f : LatHom T.L T'.L) (y : TW (OW l O) T) :
    latW f (TWmap (frobOW l O) T y) = TWmap (frobOW l O) T' (latW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def latZ (f : LatHom T.L T'.L) :
    letI := zlLat T
    letI := zlLat T'
    ↥T.L.T →ₗ[ℤ_[l]] ↥T'.L.T :=
  letI := zlLat T
  letI := zlLat T'
  { toFun := (f.f.restrictScalars O).restrict f.T_le
    map_add' := map_add _
    map_smul' := fun z x => ((f.f.restrictScalars O).restrict f.T_le).map_smul (algebraMap ℤ_[l] O z) x }


omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in
theorem kappa_latZ (f : LatHom T.L T'.L) :
    letI := zlLat T
    letI := zlLat T'
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T' ((latZ f).lTensor (WCb l) y) = latW f (kappa T y) := by
  let _ := zlLat T
  let _ := zlLat T'
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

theorem exists_isMapOf (I : Ident t ϖ P T) (I' : Ident t ϖ Q T') (f : LatHom T.L T'.L)
    (h : ∀ (m : Vec K a ι) (hm : m ∈ P.M), ∃ (m' : Vec K a κ) (hm' : m' ∈ Q.M),
      latW f (I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) = I'.j (toW t ϖ Q ⟨m', mem_ME_of_mem_M hm'⟩)) :
    ∃ F, IsMapOf I I' f F := by
  have hb : ∀ j : ι, (fun _ => Pi.single j 1 : Vec K a ι) ∈ P.M := fun j => mem_tot.2 fun τ i => by
    by_cases hij : i = j
    · subst hij; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne hij]; exact zero_mem _
  have hb' : ∀ j : ι, toW t ϖ P ⟨_, mem_ME_of_mem_M (hb j)⟩ = Pi.single j 1 := fun j => funext fun i => by
    rw [toW_apply]
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same (M := fun _ => OW l O), ← map_one (ϖ.iW t K)]
      exact congrArg _ (funext fun τ => Subtype.ext (Pi.single_eq_same (M := fun _ => K⟦X⟧) i 1))
    · rw [Pi.single_eq_of_ne (M := fun _ => OW l O) hij, ← map_zero (ϖ.iW t K)]
      exact congrArg _ (funext fun τ => Subtype.ext (Pi.single_eq_of_ne (M := fun _ => K⟦X⟧) hij 1))
  choose m hm hmj using fun j => h _ (hb j)
  simp only [hb'] at hmj
  let Y : Matrix κ ι (OW l O) :=
    Matrix.of fun i j => inclO l O (ϖ.iTot t K fun τ => ⟨m j τ i, mem_tot.1 (hm j) τ i⟩)
  have hY : ∀ j, toW t ϖ Q ⟨m j, mem_ME_of_mem_M (hm j)⟩ = fun i => Y i j := fun j => funext fun i =>
    ϖ.iW_of_mem t K fun τ => ⟨m j τ i, mem_tot.1 (hm j) τ i⟩
  have key : ∀ v, I'.j (Y *ᵥ v) = latW f (I.j v) := fun v => by
    have h1 : Y *ᵥ v = ∑ j, v j • fun i => Y i j := by
      ext1 i
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _

    conv_rhs => rw [pi_eq_sum_univ' v, map_sum, map_sum]

    rw [h1, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul I.j, latW_smul, hmj, hY, map_smul I'.j]
  have hmat : Y * frobMat t ϖ P = frobMat t ϖ Q * Y.map (frobOW l O) := by
    have h1 : ∀ v, Y *ᵥ phiW t ϖ P v = phiW t ϖ Q (Y *ᵥ v) := fun v => I'.j.injective (by
      rw [key, I.j_φ, latW_frob, I'.j_φ, key])
    ext1 i j
    have h2 := congrFun (h1 (Pi.single j 1)) i
    have h3 : (fun k => frobOW l O (Pi.single (M := fun _ : ι => OW l O) j 1 k)) = Pi.single j 1 :=
      funext fun k => by simp only [Pi.single_apply, apply_ite (frobOW l O), map_one, map_zero]
    rw [phiW_apply, phiW_apply, h3, Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one] at h2
    exact h2
  refine ⟨⟨fun τ => Matrix.of fun i j => m j τ i, fun τ i j => mem_tot.1 (hm j) τ i, fun τ => ?_⟩, key⟩
  ext1 i j
  have h1 := congrFun₂ hmat i j
  change ∑ k, inclO l O (ϖ.iTot t K _) * ϖ.iW t K _ =
    ∑ k, ϖ.iW t K _ * frobOW l O (inclO l O (ϖ.iTot t K _)) at h1
  simp only [frobOW_inclO, ← PiSys.iTot_frob] at h1
  simp only [← ϖ.iW_of_mem t K, ← map_mul] at h1

  rw [← map_sum, ← map_sum] at h1
  have h2 := congrArg Subtype.val (congrFun (ϖ.iW_injective t K h1) τ)
  rw [Finset.sum_apply, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum,
    AddSubmonoidClass.coe_finsetSum] at h2
  exact h2

end Lat

theorem main (BS : GlobalTheory.Published.BhattScholzeCrystallineLattices) (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a]
    [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T T' : Lat a O K ϖ)
    (I : Ident t ϖ P T) (I' : Ident t ϖ Q T') (H : IsBK I) (H' : IsBK I') (f : LatHom T.L T'.L) :
    ∃ F, IsMapOf I I' f F := by
  let _ := zlLat T
  let _ := zlLat T'
  obtain ⟨E, j, hE, h⟩ := H
  obtain ⟨E', j', hE', h'⟩ := H'
  obtain ⟨u, hu, -⟩ := (BS l (ϖ.field a) _ _ (isAinf_ainfObj _)).2 _ _ _ _ E E' j j' hE hE' (latZ f)
    fun g x => Subtype.ext (f.equiv g x)
  refine exists_isMapOf I I' f fun m hm => (h' _).1 ?_
  obtain ⟨x, hx⟩ := (h _).2 ⟨m, hm, rfl⟩
  refine ⟨u.u _ x, ?_⟩
  rw [hx, ← u.u_tr, hu]
  exact (kappa_latZ f _).symm

end GlobalTheory.BKReal.Full
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.BK GlobalTheory.BKReal
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_pow_mul_descPochhammerEuler_eq_eisenstein_pow : ∀ (l e : ℕ) (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (f h : K⟦X⟧) (k m : ℕ), h ∈ A O K → (l : K⟦X⟧) ^ k * N K f = E K l e ^ m * h → ∀ i : ℕ, 1 ≤ i → ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i f = E K l e ^ (m + 1 - i) * h' := by
  first | exact @GlobalTheory.BKReal.exists_l_pow_mul_descN_eq_E_pow_mul | exact GlobalTheory.BKReal.exists_l_pow_mul_descN_eq_E_pow_mul | (intros; apply GlobalTheory.BKReal.exists_l_pow_mul_descN_eq_E_pow_mul <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.deltaRingStructure_delta_frobenius_comm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (a : A), D.δ (D.φ a) = D.φ (D.δ a) := by
  first | exact @GlobalTheory.BSP.Delta.δ_φ_comm | exact GlobalTheory.BSP.Delta.δ_φ_comm | (intros; apply GlobalTheory.BSP.Delta.δ_φ_comm <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A), (l : A) ∈ J → ∀ (n : ℕ) (x : A), ∀ y ∈ J ^ (n + 1), D.δ (x + y) - D.δ x ∈ J ^ n := by
  first | exact @GlobalTheory.BSP.delta_add_sub_mem_pow | exact GlobalTheory.BSP.delta_add_sub_mem_pow | (intros; apply GlobalTheory.BSP.delta_add_sub_mem_pow <;> assumption)
end
