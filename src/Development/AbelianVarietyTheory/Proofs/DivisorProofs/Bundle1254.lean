module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle479
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefTransfer.Loc

theorem smul_conj_iff {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] (f : A) {N N' : Matrix n n A}
    (h : N * N' = 1) (h' : N' * N = 1) (X : Matrix n n A) :
    f • (N * X * N' - 1) = N * X * N' - 1 ↔ f • (X - 1) = X - 1 := by
  have e : N * X * N' - 1 = N * (X - 1) * N' := by rw [mul_sub, sub_mul, mul_one, h]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul]
  refine ⟨fun k => ?_, fun k => by rw [k]⟩
  have := congrArg (fun Y => N' * Y * N) k
  simpa only [← mul_assoc, h', one_mul, mul_assoc _ N' N, mul_one] using this

variable {D : D7}

theorem parts_ext {a b : Formalism.L2.Theta.AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) :
    a = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  apply e.injective
  exact Prod.ext (by rw [he1, he1, h1]) (by rw [he2, he2, h2])

theorem map_one_apply {A B n : Type} [CommRing A] [CommRing B] [DecidableEq n] (φ : A →+* B) (i j : n) :
    φ ((1 : Matrix n n A) i j) = (1 : Matrix n n B) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem suppF_iff_fin (V : HSp D) (f : Formalism.L2.Theta.AE D) {g : Formalism.L2.Theta.GA D V} (hg : g ∈ GfC V) :
    SuppF V f g ↔ finPart D f • (finMat D.sp.cm.sig V.gram g - 1) = finMat D.sp.cm.sig V.gram g - 1 := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  have e2 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = (finMat D.sp.cm.sig V.gram g - 1) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, map_one_apply]
    rfl
  have e1 : infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
    rw [Matrix.sub_apply, RingHom.map_sub, map_one_apply, sub_eq_zero]
    have : infHom V g = 1 := hg
    exact congrArg (fun m : GL (Fin V.rank) _ => m.1 i j) this
  rw [Matrix.smul_apply, smul_eq_mul, ← e2]
  refine ⟨fun h => by rw [← RingHom.map_mul, h], fun h => parts_ext ?_ ?_⟩
  · rw [RingHom.map_mul, e1, mul_zero]
  · rw [RingHom.map_mul, h]

theorem comp_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (h : IsPrimeIdem P e f)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) → GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D f) Q = 1) ∧
    (Q.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) → GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D f) Q = 0) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, ⟨α, rfl, h1, h0⟩, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  have e : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      (finPart D (algebraMap _ (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α))) Q =
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F)) α) := by
    rw [GlobalTheory.LFun.finAdEquiv_apply rfl]
    change GlobalTheory.LFun.toCompl rfl ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F)) α) ⊗ₜ[D.host.F]
      (1 : D.host.E)) = _
    rw [GlobalTheory.LFun.toCompl_tmul, map_one, mul_one]
    rfl
  rw [e]
  refine ⟨fun hQ => ?_, fun hQ => by rw [h0 _ hQ, map_zero]⟩
  have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F)) α = 1 := by
    revert h1
    generalize P.under (𝓞 D.host.F) = v at hQ
    subst hQ
    exact id
  rw [h2, map_one]

theorem supp_iff_loc [IsCMField D.host.E] {n : ℕ} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) (x : UA D.host.E n) :
    finPart D f • (((x : GL (Fin n) (Ad D.host.E)) : Matrix (Fin n) (Fin n) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) - 1) =
      ((x : GL (Fin n) (Ad D.host.E)) : Matrix (Fin n) (Fin n) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) - 1 ↔
    ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) → cLoc u x = 1 := by
  have key : ∀ i j (u : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      ((((x : GL (Fin n) (Ad D.host.E)) : Matrix (Fin n) (Fin n) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) - 1) i j) u =
      (cLoc u x).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro i j u
    rw [Matrix.sub_apply, map_sub, Matrix.map_apply, RingEquiv.apply_symm_apply,
      ← map_one_apply ((pLoc D.host.E u).comp (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom)]
    rfl
  have ev : ∀ (a b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (u : HeightOneSpectrum (𝓞 D.host.E)),
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (a * b) u =
        GlobalTheory.LFun.finAdEquiv D.host.F D.host.E a u * GlobalTheory.LFun.finAdEquiv D.host.F D.host.E b u := by
    intro a b u
    rw [map_mul]; rfl
  constructor
  · intro k u hu
    refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrArg (fun m => GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (m i j) u) k
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    rw [ev, (comp_of_isPrimeIdem h u).2 hu, zero_mul, key, eq_comm, sub_eq_zero] at this
    exact this
  · intro k
    refine Matrix.ext fun i j => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      (FiniteAdeleRing.ext _ fun u => ?_)
    rw [Matrix.smul_apply, smul_eq_mul, ev]
    by_cases hu : u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)
    · rw [(comp_of_isPrimeIdem h u).1 hu, one_mul]
    · rw [key, k u hu, Units.val_one, sub_self, mul_zero]

theorem finMat_mul (V : HSp D) (g h : Formalism.L2.Theta.GA D V) :
    finMat D.sp.cm.sig V.gram (g * h) = finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram h := by
  have := congrArg Units.val ((finHom V).map_mul g h)
  rw [Units.val_mul] at this
  exact this

theorem finMat_one (V : HSp D) : finMat D.sp.cm.sig V.gram (1 : Formalism.L2.Theta.GA D V) = 1 :=
  congrArg Units.val (finHom V).map_one

theorem map_mul_inv {K A n : Type} [Field K] [CommRing A] [Fintype n] [DecidableEq n] {T : Type} [FunLike T K A]
    [RingHomClass T K A] (φ : T) {M : Matrix n n K} (hu : IsUnit M.det) : M.map φ * M⁻¹.map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

theorem locU_iff : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* Formalism.L2.Theta.GA D V) (h₀ : Formalism.L2.Theta.GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU (E := D.host.E) (n := V.rank) ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e f, IsPrimeIdem P e f) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ SuppF V f (cj j h₀ x)) := by
  intro D _ V j h₀ M hM hh hfin hmat _
  refine ⟨fun P => ?_, fun P e f h x => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
    exact GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  have hu : IsUnit M.det := Matrix.isUnit_det_of_left_inverse hM
  have hG : cj j h₀ x ∈ GfC V ↔ x ∈ finU (E := D.host.E) (n := V.rank) := by
    rw [hfin, cj_apply, Subgroup.mul_mem_cancel_right _ hh, Subgroup.mul_mem_cancel_left _ (inv_mem hh)]
  have hL : x ∈ locU V.rank P ↔ x ∈ finU (E := D.host.E) (n := V.rank) ∧ ∀ u : HeightOneSpectrum (𝓞 D.host.E),
      u.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) → cLoc u x = 1 := by
    simp only [locU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rw [hL, ← hG]
  refine and_congr_right fun hx => ?_
  have m1 := map_mul_inv (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F]
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) hu
  have m2 := mul_eq_one_comm.1 m1
  have e1 : finMat D.sp.cm.sig V.gram (cj j h₀ x) =
      finMat D.sp.cm.sig V.gram h₀⁻¹ * finMat D.sp.cm.sig V.gram (j x) * finMat D.sp.cm.sig V.gram h₀ := by
    rw [cj_apply, finMat_mul, finMat_mul]
  have k1 : finMat D.sp.cm.sig V.gram h₀⁻¹ * finMat D.sp.cm.sig V.gram h₀ = 1 := by
    rw [← finMat_mul, inv_mul_cancel, finMat_one]
  refine ((suppF_iff_fin V f hx).trans ?_).symm
  rw [e1]
  refine (smul_conj_iff _ k1 (mul_eq_one_comm.1 k1) _).trans ?_
  rw [hmat]
  exact (smul_conj_iff _ m1 m2 _).trans (supp_iff_loc h x)

end GlobalTheory.DefTransfer.Loc
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace GKUnitary

theorem diag_conj_weylRep {R : Type} [CommRing R] {n : ℕ} {s : Equiv.Perm (Fin n)} {y t : GL (Fin n) R}
    (hy : IsWeylRep s y) (ht : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) R) i j = 0) (i : Fin n) :
    ((y⁻¹ * t * y : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i =
      (t : Matrix (Fin n) (Fin n) R) (s i) (s i) := by
  have h1 : ((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (s i) * (y : Matrix (Fin n) (Fin n) R) (s i) i = 1 := by
    have h := congrFun (congrFun (Units.inv_mul y) i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single (s i)] at h
    · rw [h, Matrix.one_apply_eq]
    · intro b _ hb; rw [hy b i hb, mul_zero]
    · simp
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (s i)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · calc ((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (s i) * (t : Matrix (Fin n) (Fin n) R) (s i) (s i) *
            (y : Matrix (Fin n) (Fin n) R) (s i) i
          = (t : Matrix (Fin n) (Fin n) R) (s i) (s i) *
            (((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (s i) * (y : Matrix (Fin n) (Fin n) R) (s i) i) := by ring
        _ = _ := by rw [h1, mul_one]
    · intro b _ hb; rw [ht b (s i) hb, mul_zero]
    · simp
  · intro b _ hb; rw [hy b i hb, mul_zero]
  · simp

theorem ordL_congr {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x y : L}
    (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  have key : ∀ z : L, ordL z = (fun w : WithZero (Multiplicative ℤ) =>
      if h : w = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v z) := fun _ => rfl
  rw [key x, key y, h]

theorem ordL_one' {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] : ordL (1 : L) = 0 :=
  Formalism.UG.P.fIwasawa_ordL_unit 1 1 (by simp) (by simp) (by simp)

theorem chiDeltaU_conj_simpleU_long :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (y : GU σ n), IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (α : Fin (n / 2) → ℂˣ) (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) *
        (q : ℂ) ^ (-2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
  intro L _ _ ϖ σ q hU n k hk hn y hy α t ht
  obtain ⟨hσ, hσv, -, -, -, hq2, -⟩ := hU
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  have hact : actU k α = Function.update α k (α k)⁻¹ := by simp [actU, hk]
  obtain ⟨m, hm⟩ := hn
  have hkv : k.val + 1 = m := by have := k.2; omega
  have hrev : ((lo k).rev : ℕ) = m := by simp [Fin.val_rev, lo]; omega
  set T : Matrix (Fin n) (Fin n) L := ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hT
  have hdiag : ∀ i, (((y⁻¹ * t * y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      T (simpleU k i) (simpleU k i) := by
    intro i
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact diag_conj_weylRep hy ht i

  have hprod : σ (T (lo k).rev (lo k).rev) * T (lo k) (lo k) = 1 := by
    have hu := (GlobalTheory.LGrp.mem_GU_iff σ n (t : GL (Fin n) L)).1 t.2 (lo k) (lo k)
    have h := congrFun (congrFun (Units.inv_mul (t : GL (Fin n) L)) (lo k)) (lo k)
    rw [Matrix.mul_apply, Finset.sum_eq_single (lo k)] at h
    · rw [← hu, h, Matrix.one_apply_eq]
    · intro b _ hb; exact mul_eq_zero_of_right _ (ht b (lo k) hb)
    · simp
  have ha0 : T (lo k) (lo k) ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hb0 : σ (T (lo k).rev (lo k).rev) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hord : ordL (T (lo k).rev (lo k).rev) = -ordL (T (lo k) (lo k)) := by
    have h := Formalism.UG.P.fIwasawa_ordL_mul _ _ hb0 ha0
    rw [hprod, ordL_one', ordL_congr (hσv _)] at h
    omega
  unfold chiDeltaU
  rw [← hT]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have hrest : ∀ i ∈ Finset.univ.erase k,
      (if h : i.val < n then (α i : ℂ) ^ ordL ((((y⁻¹ * t * y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩) *
        (q : ℂ) ^ (-(ordL ((((y⁻¹ * t * y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩)) *
          ((n : ℤ) - 1 - 2 * (i.val : ℤ))) else 1) =
      (if h : i.val < n then (actU k α i : ℂ) ^ ordL (T ⟨i.val, h⟩ ⟨i.val, h⟩) *
        (q : ℂ) ^ (-(ordL (T ⟨i.val, h⟩ ⟨i.val, h⟩)) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))) else 1) := by
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hin : i.val < n := by have := i.2; omega
    rw [dite_eq_left hin, dite_eq_left hin, hdiag, hact, Function.update_of_ne hik]
    have hfix : simpleU k ⟨i.val, hin⟩ = ⟨i.val, hin⟩ := by
      rw [hs]
      refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
      · intro h; apply hik; ext; simpa [lo] using congrArg Fin.val h
      · intro h; have := congrArg Fin.val h; rw [hrev] at this; have := i.2; simp at *; omega
    rw [hfix]
  rw [Finset.prod_congr rfl hrest]
  have hkn : k.val < n := by omega
  rw [dite_eq_left hkn, dite_eq_left hkn, hdiag, hact]
  beta_reduce
  rw [Function.update_self]
  have hlk : (⟨k.val, hkn⟩ : Fin n) = lo k := rfl
  rw [hlk, hs, Equiv.swap_apply_left, hord]
  have he : ((n : ℤ) - 1 - 2 * (k.val : ℤ)) = 1 := by
    have : (n : ℤ) = m + m := by exact_mod_cast hm
    have h2 : (k.val : ℤ) + 1 = m := by exact_mod_cast hkv
    omega
  rw [he]
  set r := ordL (T (lo k) (lo k))
  have hα : (α k : ℂ) ≠ 0 := (α k).ne_zero
  have hq1 : (q : ℂ) ^ (-(-r) * (1 : ℤ)) * (q : ℂ) ^ (-2 * r) = (q : ℂ) ^ (-r * (1 : ℤ)) := by
    rw [← zpow_add₀ hq]; congr 1; ring
  rw [Units.val_inv_eq_inv_val, inv_zpow', ← hq1]
  ring

end GKUnitary

end GlobalTheory
end
end

section

noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

theorem swap_lt_swap_iff_of_add_two {n : ℕ} (A A' a b : Fin n) (hA : A'.val = A.val + 2) (hab : a < b) :
    Equiv.swap A A' a < Equiv.swap A A' b ↔ (a < A ∨ A' < b) := by
  rw [Fin.lt_iff_val_lt_val] at hab
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h3 h4 <;>
    simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at * <;> omega

theorem val_rev_lo_of_last {n : ℕ} (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (hn : ¬ Even n) :
    ((lo k).rev : Fin n).val = (lo k).val + 2 := by
  have h2 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hn)
  have := k.isLt
  simp only [Fin.val_rev, lo, Fin.coe_castLE]
  omega

theorem mem_cellU_last_iff : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ u : GU σ n, u ∈ cellU y ↔ IsUnipU u ∧ ∀ i j : Fin n, i < j → (i < lo k ∨ (lo k).rev < j) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro L _ _ _ ϖ σ q _ n k hk hn y _ hy u
  have hw : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  have hA := val_rev_lo_of_last k hk hn
  rw [hw] at hy
  let M : GL (Fin n) L → Matrix (Fin n) (Fin n) L := fun x => x.val
  have weylRep_inv_mul_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (p : Fin n) :
      (M x⁻¹) p (w p) * (M x) (w p) p = 1 := by
    have h : (M (x⁻¹ * x)) p p = (M (1 : GL (Fin n) L)) p p := by rw [inv_mul_cancel]
    dsimp only [M] at h
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
    rwa [Finset.sum_eq_single (w p) (fun b _ hb => by rw [hx b p hb, mul_zero]) (by simp)] at h

  have weylRep_mul_inv_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (p : Fin n) :
      (M x) (w p) p * (M x⁻¹) p (w p) = 1 := by
    have h : (M (x * x⁻¹)) (w p) (w p) = (M (1 : GL (Fin n) L)) (w p) (w p) := by rw [mul_inv_cancel]
    dsimp only [M] at h
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
    rwa [Finset.sum_eq_single p (fun b _ hb => by
        rw [hx (w p) b (fun e => hb (w.injective e).symm), zero_mul]) (by simp)] at h

  have weylRep_inv {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) : IsWeylRep w⁻¹ x⁻¹ := by
    intro p a hpa
    have hne : (M x) a (w⁻¹ a) ≠ 0 := by
      intro h0
      have := weylRep_mul_inv_diag hx (w⁻¹ a)
      rw [show w (w⁻¹ a) = a by simp] at this
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    have h : (M (x⁻¹ * x)) p (w⁻¹ a) = (M (1 : GL (Fin n) L)) p (w⁻¹ a) := by rw [inv_mul_cancel]
    dsimp only [M] at h
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_ne hpa] at h
    rw [Finset.sum_eq_single a (fun b _ hb => by
        rw [hx b (w⁻¹ a) (by simpa using hb), mul_zero]) (by simp)] at h
    exact (mul_eq_zero.1 h).resolve_right hne

  have weylRep_conj_apply {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (u : GL (Fin n) L)
      (p q : Fin n) : (M (x⁻¹ * u * x)) p q = (M x⁻¹) p (w p) * (M u) (w p) (w q) * (M x) (w q) q := by
    have hi := weylRep_inv hx
    dsimp only [M]
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (w q)
      (fun b _ hb => by rw [hx b q hb, mul_zero]) (by simp), Matrix.mul_apply,
      Finset.sum_eq_single (w p) (fun b _ hb => by rw [hi p b (fun e => hb (by rw [e]; simp)), zero_mul]) (by simp)]

  dsimp only [M] at weylRep_inv_mul_diag weylRep_mul_inv_diag weylRep_conj_apply
  have mem_cell_iff {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (u : GL (Fin n) L) :
      u ∈ cell x ↔ u ∈ unipB L (Fin n) ∧ ∀ a b, a < b → w⁻¹ a < w⁻¹ b → (M u) a b = 0 := by
    dsimp only [M]
    rw [mem_cell, mem_unipBLower]
    refine and_congr_right fun hu => ?_
    rw [mem_unipB] at hu
    constructor
    · rintro ⟨hl, -⟩ a b hab hw
      have h := hl _ _ hw
      rw [weylRep_conj_apply hx, show w (w⁻¹ a) = a by simp, show w (w⁻¹ b) = b by simp] at h
      have h1 := weylRep_inv_mul_diag hx (w⁻¹ a)
      have h2 := weylRep_mul_inv_diag hx (w⁻¹ b)
      rw [show w (w⁻¹ a) = a by simp] at h1
      rw [show w (w⁻¹ b) = b by simp] at h2
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · rw [h, zero_mul] at h1; exact absurd h1 zero_ne_one
        · exact h
      · rw [h, zero_mul] at h2; exact absurd h2 zero_ne_one
    · intro h
      refine ⟨fun p q hpq => ?_, fun p => ?_⟩
      · rw [weylRep_conj_apply hx]
        rcases lt_or_gt_of_ne (fun e : w p = w q => hpq.ne (w.injective e)) with hl | hl
        · rw [h _ _ hl (by simpa using hpq), mul_zero, zero_mul]
        · rw [hu.1 _ _ hl, mul_zero, zero_mul]
      · rw [weylRep_conj_apply hx, hu.2, mul_one, weylRep_inv_mul_diag hx]

  rw [cellU, Subgroup.mem_subgroupOf, mem_cell_iff hy, mem_unipB, Equiv.swap_inv]
  unfold IsUnipU IsBorelU
  refine and_congr_right fun _ => forall₂_congr fun a b => ?_
  constructor
  · intro h hab hor
    exact h hab ((swap_lt_swap_iff_of_add_two _ _ a b hA hab).2 hor)
  · intro h hab hs
    exact h hab ((swap_lt_swap_iff_of_add_two _ _ a b hA hab).1 hs)

end WeylUnipotentShell

end WeylCell

end GlobalTheory
end
end

section

open NumberField

theorem _root_.GlobalTheory.T.exists_rational_frame_mem_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ u : Fin r → Fin r → E, GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom := by
  first | exact @GlobalTheory.OrthoFrame.exists_frm_mem_dom | exact GlobalTheory.OrthoFrame.exists_frm_mem_dom | (intros; apply GlobalTheory.OrthoFrame.exists_frm_mem_dom <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitaryIdeleChar_trivial_congruentOneModulo : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : (AF F ⊗[F] E)ˣ →* Circle), Continuous ν → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitGen.modSetF F E N, ν x = 1 := by
  exact @GlobalTheory.HeckeSplitGen.char_trivial_modSetF
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.composite_cut_operators_product_local_cells_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ), (∀ w x, ψ w x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) → (∀ w ∈ S, GlobalTheory.JSW.Cut.Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) (GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) → ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.Cut.act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
  first | exact @GlobalTheory.JSW.CutProd.cut_prod_mirS | exact GlobalTheory.JSW.CutProd.cut_prod_mirS | (intros; apply GlobalTheory.JSW.CutProd.cut_prod_mirS <;> assumption)
end
