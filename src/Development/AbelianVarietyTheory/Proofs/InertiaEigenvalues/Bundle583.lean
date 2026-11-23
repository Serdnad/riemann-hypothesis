module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle375
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle286
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle034
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem htOp_pow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (C : Core l) (ξ : Ainf l) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (σ : GQ l) (z : ℂ_[l]) (H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), U * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) → IsHT C ξ (fun g => (r g).val.map σ) z u → ∀ n : ℕ, u ^ n = ∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (e s))) i • (b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x) := by
  intro l _ K C ξ a d ρ r b e hR σ z H U u hU hu
  have hσz : ∀ c : ℤ_[l], σ (zOm l c) = zOm l c := fun c => by simp [zOm]
  have hθo : ∀ w : Om l, Per.θD l (C.o w) = algebraMap (Om l) ℂ_[l] w := fun w => C.o_sec.th w

  let S : Set (Om l) := Set.range fun t : Fin d × Fin a × Fin a => σ (b t.1 t.2.1 t.2.2)
  haveI : Finite S := (Set.finite_range _).to_subtype
  have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let K' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] S, hfd⟩
  have hfix : ∀ g : GQ l, g ∈ GK K' → ∀ i m k, g (σ (b i m k)) = σ (b i m k) := by
    intro g hg i m k
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg _
      (IntermediateField.subset_adjoin _ _ ⟨(i, m, k), rfl⟩)
  let B : Fin a → Matrix (Fin a) (Fin d) ℂ_[l] := fun k m i => algebraMap (Om l) ℂ_[l] (σ (b i m k))
  have hVu : IsUnit (H.V.map (Per.θD l)) := H.unit.map (Per.θD l).mapMatrix
  have col : ∀ k, u * B k * H.V.map (Per.θD l) = B k * U * H.V.map (Per.θD l) := by

    intro k
    ext m j
    let y : Fin a → _root_.Formalism.Per.BdRp l := fun m => ∑ i, C.o (σ (b i m k)) * H.V i j
    let x : Fin a → _root_.Formalism.Per.BdR l := fun m => ∑ i, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ (b i m k))) * H.Q i j
    have hy : ∀ m, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l ξ) ^ H.q * x m = algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l ξ ^ H.p j * y m) := by
      intro m

      simp only [x, y, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hq := H.Q_eq i j
      calc algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l ξ) ^ H.q * (algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ (b i m k))) * H.Q i j)
          = algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ (b i m k))) * (algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l ξ) ^ H.q * H.Q i j) := by ring
        _ = algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ (b i m k))) * algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l ξ ^ H.p j * H.V i j) := by rw [hq]
        _ = algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l ξ ^ H.p j * (C.o (σ (b i m k)) * H.V i j)) := by simp only [map_mul, map_pow]; ring
    have hx : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
        ((r g).val.map σ).map ((algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l)).comp C.o) *ᵥ (fun i => _root_.Formalism.Per.σD (g : GQ l) (x i)) = x := by
      intro g hg
      funext m'
      have hσD : ∀ m, _root_.Formalism.Per.σD (g : GQ l) (x m) = ∑ i, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ (b i m k))) * _root_.Formalism.Per.σD (g : GQ l) (H.Q i j) := by
        intro m

        simp only [x, map_sum, map_mul, PrimeEx.sigD_o, hfix _ hg]
      have e1 : ∀ i, ∑ m, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ ((r g).val m' m))) * algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ (b i m k))) =
          ∑ s, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ (b s m' k))) := by
        intro i
        have h1 := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) => algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ (M m' k)))) (hR.equi g i)

        simpa [Matrix.mul_apply, Matrix.sum_apply, map_sum, map_mul, hσz] using h1
      have e2 : ∀ s, ∑ i, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * _root_.Formalism.Per.σD (g : GQ l) (H.Q i j) = H.Q s j := by
        intro s
        have h1 := congrFun (congrFun (H.inv g g.2) s) j
        simpa [Matrix.mul_apply] using h1
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.comp_apply, hσD]
      calc ∑ m, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ ((r g).val m' m))) * ∑ i, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ (b i m k))) * _root_.Formalism.Per.σD (g : GQ l) (H.Q i j)
          = ∑ i, (∑ m, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ ((r g).val m' m))) * algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ (b i m k)))) * _root_.Formalism.Per.σD (g : GQ l) (H.Q i j) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
            exact Finset.sum_comm
        _ = ∑ i, (∑ s, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ (b s m' k)))) * _root_.Formalism.Per.σD (g : GQ l) (H.Q i j) := by
            simp only [e1]
        _ = ∑ s, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (σ (b s m' k))) * ∑ i, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * _root_.Formalism.Per.σD (g : GQ l) (H.Q i j) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
        _ = x m' := by simp only [e2, x]
    have h := hu K' (H.p j) H.q x y hx hy
    have hθy : (fun m => Per.θD l (y m)) = fun m => (B k * H.V.map (Per.θD l)) m j := by
      funext m'
      simp only [y, Matrix.mul_apply, Matrix.map_apply]

      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hθo]
    rw [hθy] at h
    have h2 := congrFun h m
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h2
    rw [Matrix.mul_assoc u, Matrix.mul_assoc (B k), hU, ← Matrix.mul_assoc (B k), Matrix.mul_diagonal, Matrix.mul_apply, h2, mul_comm]
  have comm : ∀ k, u * B k = B k * U := by
    intro k
    have hd : IsUnit (H.V.map (Per.θD l)).det := (Matrix.isUnit_iff_isUnit_det _).1 hVu
    calc u * B k = u * B k * H.V.map (Per.θD l) * (H.V.map (Per.θD l))⁻¹ := by
          rw [Matrix.mul_assoc (u * B k), Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      _ = B k * U * H.V.map (Per.θD l) * (H.V.map (Per.θD l))⁻¹ := by rw [col k]
      _ = B k * U := by rw [Matrix.mul_assoc (B k * U), Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have key : ∀ x : Fin d → ℂ_[l], u * (∑ i, x i • (b i).map fun w => algebraMap (Om l) ℂ_[l] (σ w)) =
      ∑ i, (U *ᵥ x) i • (b i).map fun w => algebraMap (Om l) ℂ_[l] (σ w) := by
    intro x
    ext m k
    have h := congrFun (congrArg (· *ᵥ x) (comm k)) m
    simp only [← Matrix.mulVec_mulVec] at h
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, B] at h
    refine (Finset.sum_congr rfl fun x1 _ => ?_).trans (h.trans (Finset.sum_congr rfl fun c _ => ?_))
    · congr 1
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    · simp only [Matrix.mulVec, dotProduct]
      exact mul_comm _ _
  have one : ∑ i, (fun s => algebraMap (Om l) ℂ_[l] (zOm l (e s))) i • (b i).map (fun w => algebraMap (Om l) ℂ_[l] (σ w)) = 1 := by
    ext m k
    have h := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) => algebraMap (Om l) ℂ_[l] (σ (M m k))) hR.one

    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hσz] at h
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [h]
    by_cases hmk : m = k <;> simp [Matrix.one_apply, hmk]
  intro n
  induction n with
  | zero => simpa using one.symm
  | succ n ih => rw [pow_succ', ih, key, Matrix.mulVec_mulVec, ← pow_succ']

end GlobalTheory.BKLim
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LayerSst

open Module

section Sum

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ_[l] (V i)]
  {V' : Type} [AddCommGroup V'] [Module ℚ_[l] V']
  {ρ : ∀ i, Representation ℚ_[l] ↥(GK K) (V i)} {ρ' : Representation ℚ_[l] ↥(GK K) V'}
  {E : V' ≃ₗ[ℚ_[l]] (∀ i, V i)}
  (hE : ∀ g x i, E (ρ' g x) i = ρ i g (E x i))
include hE

theorem mem_Dst_iff (x : V' ⊗[ℚ_[l]] Bst P) :
    x ∈ Dst P ρ' ↔ ∀ i, GlobalTheory.BlockSum.tensComp E (Bst P) x i ∈ Dst P (ρ i) := by
  simp only [mem_Dst]
  rw [forall_comm]
  refine forall_congr' fun g => ?_
  rw [← (GlobalTheory.BlockSum.tensComp E (Bst P)).injective.eq_iff, funext_iff]
  refine forall_congr' fun i => ?_
  have key : GlobalTheory.BlockSum.tensComp E (Bst P) (stRep P ρ' g x) i =
      stRep P (ρ i) g (GlobalTheory.BlockSum.tensComp E (Bst P) x i) :=
    GlobalTheory.BlockSum.tensComp_map E (ρ' g) (fun i => ρ i g) (hE g) (actSt P (g : GQ l)).toLinearMap x i
  rw [key]

theorem isSst_sum [∀ i, FiniteDimensional ℚ_[l] (V i)] (h : ∀ i, IsSst P (ρ i)) : IsSst P ρ' := by
  have := fun i => finiteDimensional_Dst_of_isSst l P K (V i) (ρ i) (h i)
  unfold IsSst at h ⊢
  rw [GlobalTheory.BlockSum.finrank_eq_sum (GlobalTheory.BlockSum.tensComp E (Bst P)) _ _ (mem_Dst_iff P hE), E.finrank_eq,
    Module.finrank_pi_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => h i

end Sum

theorem isSst_resQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsSst P (GlobalTheory.PstCoeff.resQ ρ) := by
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  rw [IsSst, e, h, ← finrank_mul_finrank ℚ_[l] LL V]
  ring

section Layer

variable {l : ℕ} [Fact l.Prime] {K L₀ : FinExt l} {a d : ℕ} {Cl : Set (↥(GK K) →* GL (Fin a) (Om l))}
  {ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ)

def matL (k : Fin Ly.m) (g : ↥(GK K)) : Matrix (Fin a) (Fin a) ↥(Ly.L k).1 :=
  fun i j => ⟨(Ly.rep k g).val i j, Ly.rep_mem k g i j⟩

def repL (k : Fin Ly.m) : ↥(GK K) →* GL (Fin a) ↥(Ly.L k).1 :=
  MonoidHom.toHomUnits
    { toFun := matL Ly k
      map_one' := by
        ext i j
        simp only [matL, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g h => by
        ext i j
        simp [matL, Matrix.mul_apply] }

theorem repL_val (k : Fin Ly.m) (g : ↥(GK K)) (i j : Fin a) :
    (((repL Ly k g).val i j : ↥(Ly.L k).1) : Om l) = (Ly.rep k g).val i j := rfl

def RL (k : Fin Ly.m) : Representation ↥(Ly.L k).1 ↥(GK K) (Fin a → ↥(Ly.L k).1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥(Ly.L k).1 ≃ₐ[↥(Ly.L k).1] _) : _ →* _).comp
    ((Units.coeHom _).comp (repL Ly k))

theorem RL_apply (k : Fin Ly.m) (g : ↥(GK K)) (v : Fin a → ↥(Ly.L k).1) : RL Ly k g v = (repL Ly k g).val *ᵥ v := by
  simp [RL, Matrix.toLinAlgEquiv'_apply]

def coordM (v : Fin d → ℚ_[l]) (k : Fin Ly.m) : Matrix (Fin a) (Fin a) (Om l) :=
  ∑ s, algebraMap ℚ_[l] (Om l) (v s) • Ly.b s k

theorem coordM_mem (v : Fin d → ℚ_[l]) (k : Fin Ly.m) (i j : Fin a) : coordM Ly v k i j ∈ (Ly.L k).1 := by
  simp only [coordM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact sum_mem fun s _ => mul_mem (IntermediateField.algebraMap_mem _ _) (Ly.b_mem s k i j)

theorem sum_b (v : Fin d → ℚ_[l]) : ∑ s, v s • Ly.b s = fun k => coordM Ly v k := by
  funext k
  simp [coordM, Finset.sum_apply, algebraMap_smul]

end Layer

section Layer2

variable {l : ℕ} [Fact l.Prime] {K L₀ : FinExt l} {a d : ℕ} {Cl : Set (↥(GK K) →* GL (Fin a) (Om l))}
  {ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ)

def coordLin : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] ((p : Fin Ly.m × Fin a) → Fin a → ↥(Ly.L p.1).1) where
  toFun v p i := ⟨coordM Ly v p.1 i p.2, coordM_mem Ly v p.1 i p.2⟩
  map_add' v w := by
    funext p i
    apply Subtype.ext
    simp [coordM, Finset.sum_add_distrib, add_smul, Matrix.sum_apply]
  map_smul' c v := by
    funext p i
    apply Subtype.ext
    show coordM Ly (c • v) p.1 i p.2 = c • coordM Ly v p.1 i p.2
    simp only [coordM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, map_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Algebra.smul_def, mul_assoc]

theorem coordLin_apply (v : Fin d → ℚ_[l]) (p : Fin Ly.m × Fin a) (i : Fin a) :
    ((coordLin Ly v p i : ↥(Ly.L p.1).1) : Om l) = coordM Ly v p.1 i p.2 := rfl

theorem coordLin_bijective : Function.Bijective (coordLin Ly) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 : ∑ s, v s • Ly.b s = 0 := by
      rw [sum_b]
      funext k i j
      have := congrArg Subtype.val (congrFun (congrFun hv (k, j)) i)
      exact this
    exact funext (Fintype.linearIndependent_iff.1 Ly.indep v h0)
  · intro y
    let x : Fin Ly.m → Matrix (Fin a) (Fin a) (Om l) := fun k i j => ((y (k, j) i : ↥(Ly.L k).1) : Om l)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ_[l]).1 (Ly.span x fun k i j => (y (k, j) i).2)
    refine ⟨c, ?_⟩
    funext p i
    apply Subtype.ext
    rw [coordLin_apply]
    rw [sum_b] at hc
    exact congrFun (congrFun (congrFun hc p.1) i) p.2

def coordEquiv : (Fin d → ℚ_[l]) ≃ₗ[ℚ_[l]] ((p : Fin Ly.m × Fin a) → Fin a → ↥(Ly.L p.1).1) :=
  LinearEquiv.ofBijective (coordLin Ly) (coordLin_bijective Ly)

theorem coordM_mulVec (g : ↥(GK K)) (v : Fin d → ℚ_[l]) (k : Fin Ly.m) :
    coordM Ly (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) k = (Ly.rep k g).val * coordM Ly v k := by
  have hr : ∀ t, (Ly.rep k g).val * Ly.b t k = ∑ s, zOm l ((ρ g).val s t) • Ly.b s k :=
    fun t => (Ly.reads k).equi g t
  calc coordM Ly (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) k
      = ∑ s, ∑ t, (algebraMap ℚ_[l] (Om l) (v t) * zOm l ((ρ g).val s t)) • Ly.b s k := by

        simp only [coordM, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_smul, Matrix.map_apply]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        rw [mul_comm]
        rfl
    _ = ∑ t, ∑ s, (algebraMap ℚ_[l] (Om l) (v t) * zOm l ((ρ g).val s t)) • Ly.b s k := Finset.sum_comm
    _ = (Ly.rep k g).val * coordM Ly v k := by
        simp only [coordM, Finset.mul_sum, Matrix.mul_smul, hr, Finset.smul_sum, smul_smul]

theorem coordEquiv_equi (g : ↥(GK K)) (v : Fin d → ℚ_[l]) (p : Fin Ly.m × Fin a) :
    coordEquiv Ly (qRep ρ g v) p = GlobalTheory.PstCoeff.resQ (RL Ly p.1) g (coordEquiv Ly v p) := by
  funext i
  apply Subtype.ext
  have hq : qRep ρ g v = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v := by
    simp [qRep, Matrix.toLinAlgEquiv'_apply]
  rw [GlobalTheory.PstCoeff.resQ_apply, RL_apply]
  change coordM Ly (qRep ρ g v) p.1 i p.2 = _
  rw [hq, coordM_mulVec, Matrix.mul_apply]
  simp [Matrix.mulVec, dotProduct, repL_val, coordEquiv, coordLin_apply]

end Layer2

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Ly : Layer L₀ Cl ρ), ((∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R) → IsSst P (qRep ρ)) ∧ ((∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsCrys (P.PD K) R)) → IsCrys (P.PD K) (qRep ρ)) := by
  intro l _ K L₀ P AI T a Cl d ρ Ly
  have hfin : ∀ p : Fin Ly.m × Fin a, FiniteDimensional ℚ_[l] (Fin a → ↥(Ly.L p.1).1) := fun p => by
    have := (Ly.L p.1).2
    infer_instance
  have hE := coordEquiv_equi Ly
  refine ⟨fun hS => ?_, fun hC => ?_⟩
  · refine isSst_sum P (E := coordEquiv Ly) (fun g x p => hE g x p) fun p => ?_
    have := (Ly.L p.1).2
    exact isSst_resQ P _ (hS (Ly.rep p.1) (Ly.mem p.1) (Ly.L p.1) (repL Ly p.1) (RL Ly p.1) (Ly.le p.1)
      (fun g v => RL_apply Ly p.1 g v) (fun g i j => repL_val Ly p.1 g i j))
  · refine GlobalTheory.BlockSum.isCrys_sum (P.PD K) (E := coordEquiv Ly) (fun g x p => hE g x p) fun p => ?_
    have := (Ly.L p.1).2
    exact (GlobalTheory.BSCoeff.isCrys_resQ_iff P (RL Ly p.1)).2 (hC (Ly.rep p.1) (Ly.mem p.1) (Ly.L p.1) (repL Ly p.1)
      (RL Ly p.1) (Ly.le p.1) (fun g v => RL_apply Ly p.1 g v) (fun g i j => repL_val Ly p.1 g i j))

end GlobalTheory.LayerSst
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem isCrys_of_bcris_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Bcris l)), IsUnit U → (∀ g : ↥(GK K), (ρ g).val.map (_root_.Formalism.Per.zB l) * U.map (_root_.Formalism.Per.σB (g : GQ l)) = U) → IsCrys (P.PD K) (qRep ρ) := by
  intro l _ K P AI T d ρ U hU hinv
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact Submodule.zero_mem _

  have hU' : IsUnit (U.map T.eB.symm) := by
    have := hU.map (T.eB.symm.mapMatrix (m := Fin d))
    simpa using this
  let Q : GL (Fin d) P.R.B := hU'.unit
  have hQ : (Q : Matrix (Fin d) (Fin d) P.R.B) = U.map T.eB.symm := hU'.unit_spec
  let b := Pi.basisFun ℚ_[l] (Fin d)
  have hmat : ∀ g : ↥(GK K), LinearMap.toMatrix b b (qRep ρ g) = (ρ g).val.map (algebraMap ℤ_[l] ℚ_[l]) := by
    intro g
    rw [LinearMap.toMatrix_eq_toMatrix']
    ext i j
    simp [qRep, LinearMap.toMatrix'_apply, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  obtain ⟨e, -, -, he⟩ := GlobalTheory.tensorBasisCoords ℚ_[l] P.R.B (Fin d → ℚ_[l]) (Fin d) b
  have key := GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix ℚ_[l] ↥(K0 K) P.R.B ↥(GK K)
    (fun g => ((P.PD K).actB g).toRingEquiv.toRingHom) (Fin d)
    (fun g => (LinearMap.toMatrix b b (qRep ρ g)).map (algebraMap ℚ_[l] P.R.B))
    (fun x => ⟨fun h => (P.PD K).invB x h, by
      rintro ⟨c, rfl⟩ g
      exact ((P.PD K).actB g).commutes c⟩) Q
    (fun g => by
      apply (T.eB.mapMatrix (m := Fin d)).injective
      rw [map_mul, hmat g, hQ]
      have hA : T.eB.mapMatrix (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])).map (algebraMap ℚ_[l] P.R.B)) =
          (ρ g).val.map (_root_.Formalism.Per.zB l) := by
        ext i j
        simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply]
        exact T.zB _
      have hB : T.eB.mapMatrix ((U.map T.eB.symm).map (((P.PD K).actB g).toRingEquiv.toRingHom)) =
          U.map (_root_.Formalism.Per.σB (g : GQ l)) := by
        ext i j
        simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply]
        change T.eB ((P.PD K).actB g (T.eB.symm (U i j))) = _
        rw [P.PD_actB, T.actB, RingEquiv.apply_symm_apply]
      have hC : T.eB.mapMatrix (U.map T.eB.symm) = U := by
        ext i j
        simp
      rw [hA, hB, hC]
      exact hinv g)
    ((Dcris (P.PD K) (qRep ρ)).map (e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] (Fin d → P.R.B)))
    (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      have h1 : e y ∈ (Dcris (P.PD K) (qRep ρ)).map (e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] (Fin d → P.R.B)) ↔
          y ∈ Dcris (P.PD K) (qRep ρ) := by
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : z = y := e.injective hzy
          exact this ▸ hz
        · exact fun h => ⟨y, h, rfl⟩
      rw [h1]
      simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      refine forall_congr' fun g => ?_
      have h2 := he (qRep ρ g) (((((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l])) y
      have h3 : actVB (P.PD K) (qRep ρ) g y = TensorProduct.map (qRep ρ g)
          ((((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y := rfl
      rw [h3, ← e.injective.eq_iff, h2]
      rfl)
  rw [LinearEquiv.finrank_map_eq, Fintype.card_fin] at key
  rw [IsCrys, key, Module.finrank_fin_fun]

end GlobalTheory.BKLim
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem deltaHom_unique_of_base : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (DQ : Delta l Q) (DC : Delta l C) (J : Ideal A) (JC : Ideal C) (i : A →+* Q) (w : Q) (tb : TopBasis i J (Digits l)), (∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] w) ^ n) → IsHausdorff JC C → ∀ h h' : Q →+* C, IsδMap DQ DC h → IsδMap DQ DC h' → J.map (h.comp i) ≤ JC → h.comp i = h'.comp i → h w = h' w → h = h' := by
  intro l _ A _ Q _ C _ DQ DC J JC i w tb hb hH h h' hδ hδ' hJ hi hw
  have hit : ∀ (g : Q →+* C), IsδMap DQ DC g → ∀ k x, g (DQ.δ^[k] x) = DC.δ^[k] (g x) := by
    intro g hg k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hg, ih]
  have hbα : ∀ α, h (tb.b α) = h' (tb.b α) := by
    intro α
    simp only [hb, Finsupp.prod, map_prod, map_pow, hit h hδ, hit h' hδ', hw]
  ext x
  have key : ∀ n, h x - h' x ∈ JC ^ n := by
    intro n
    have hF : ∀ α, α ∉ (tb.fin x n).toFinset → tb.c α x ∈ J ^ n := by
      intro α hα
      by_contra hc
      exact hα ((tb.fin x n).mem_toFinset.2 hc)
    have hap := tb.approx x n _ hF
    have hs : h (∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) =
        h' (∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) := by

      simp only [map_sum, map_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← RingHom.comp_apply h i, hi, RingHom.comp_apply, hbα]
    have mem : ∀ g : Q →+* C, g.comp i = h.comp i →
        g (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) ∈ JC ^ n := by
      intro g hg
      have hm := Ideal.mem_map_of_mem g hap
      rw [Ideal.map_map, hg, Ideal.map_pow] at hm
      exact Ideal.pow_right_mono hJ n hm
    have e : h x - h' x = h (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) -
        h' (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) := by
      rw [map_sub, map_sub, hs]; ring
    rw [e]
    exact sub_mem (mem h rfl) (mem h' hi.symm)
  rw [← sub_eq_zero]
  refine hH.haus _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key n

end GlobalTheory.BSP
end
