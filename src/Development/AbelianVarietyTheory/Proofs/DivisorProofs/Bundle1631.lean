module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ConjSplit

theorem sigR_incA (D : D7) (x : D.host.E) :
    cA D (incA D x) = incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := by
  simp [cA, sigR, incA, inclR]

def ratPt (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E)
    (hγ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram) : GA D V :=
  ⟨Formalism.UG.bc (incA D) γ, by
    show Formalism.UG.cT _ _ * _ * _ = _
    have hc : Formalism.UG.cT (cA D) ((γ : Matrix _ _ D.host.E).map (incA D)) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1).map (incA D) := by
      ext i j; simp [Formalism.UG.cT, sigR_incA]
    have := congrArg (fun M => M.map (incA D)) hγ
    simp only [Matrix.map_mul] at this
    simpa [Formalism.UG.bc, JR, hc] using this⟩

theorem finE_ratPt (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E) hγ :
    (Formalism.IndefR.Lev.finE V (ratPt D V γ hγ)).1 = γ.1.map (eToEAf D) := by
  ext i j
  change Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E
    (Algebra.TensorProduct.map (AlgHom.snd (↥D.host.F) (Ainf ↥D.host.F) (Af ↥D.host.F)) (AlgHom.id (↥D.host.F) D.host.E)
      (Algebra.TensorProduct.includeRight (γ.1 i j))) = _
  simp [eToEAf]

theorem mt_mul (D : D7) (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_mul_inv (D : D7) (V : HSp D) (a : GA D V) : mt V a * mt V a⁻¹ = 1 := by
  rw [← mt_mul, mul_inv_cancel]; simp [Formalism.L2.Theta.mt]

theorem suppAt_conj {D : D7} {V : HSp D} {e : AE D} {h : GA D V} (hs : SuppAt e V h) (g : GA D V) :
    SuppAt e V (g * h * g⁻¹) := by
  have hm : (e + cA D e) • (mt V h - 1) = mt V h - 1 := Matrix.ext fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hs i j
  have key : mt V (g * h * g⁻¹) - 1 = mt V g * (mt V h - 1) * mt V g⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  have hm' : (e + cA D e) • (mt V (g * h * g⁻¹) - 1) = mt V (g * h * g⁻¹) - 1 := by
    rw [key, ← Matrix.smul_mul, ← Matrix.mul_smul, hm]
  intro i j
  have := congrFun (congrFun hm' i) j
  rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem finE_ratPt_units (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E) hγ :
    Formalism.IndefR.Lev.finE V (ratPt D V γ hγ) = Formalism.UG.bc (eToEAf D) γ :=
  Units.ext (finE_ratPt D V γ hγ)

theorem conj_supp : ∀ (D : D7) (V : HSp D) (S : Finset ℕ) (γ : GL (Fin V.rank) D.host.E) (h : GA D V),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram → h ∈ GfC V →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) →
    ∃ u : GA D V, u ∈ GfC V ∧ (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u ∧ ∀ w ∈ P, Off S w) ∧
      (Formalism.IndefR.Lev.finE V u).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (γ⁻¹).1.map (eToEAf D) := by
  intro D V S γ h hγ hh ⟨P, e, he, hs, hoff⟩
  refine ⟨ratPt D V γ hγ * h * (ratPt D V γ hγ)⁻¹, ?_, ⟨P, e, he, suppAt_conj hs _, hoff⟩, ?_⟩
  · exact (MonoidHom.normal_ker (infHom V)).conj_mem h hh _
  · rw [map_mul, map_mul, map_inv, finE_ratPt_units, Units.val_mul, Units.val_mul, ← map_inv]
    rfl

end GlobalTheory.ConjSplit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOff

theorem natCast_not_mem {D : D7} {S : Finset ℕ} {w : Pl D.host.E} (hw : Off S w) {N : ℕ} (hN : 0 < N)
    (hS : N.primeFactors ⊆ S) : ((N : 𝓞 D.host.E)) ∉ w.asIdeal := by
  intro h
  rw [← Nat.prod_factorization_pow_eq_self hN.ne', Nat.cast_finsuppProd] at h
  obtain ⟨p, hp, hpw⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 h
  dsimp only at hpw
  rw [Nat.cast_pow] at hpw
  exact hw p (hS (Nat.support_factorization N ▸ hp)) (w.isPrime.mem_of_pow_mem _ hpw)

theorem infPart_idem {D : D7} {e : AE D} (he : Formalism.L2.Theta.IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨hee, hec, v, ε, ⟨α, hε, -, -⟩, hs⟩ := he
  have h1 : e = e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← hs, mul_add, hee, hec, add_zero]
  have h2 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    subst hε
    have e1 : (algebraMap (AF D.host.F) (AE D)) (pairA D.host.F 0 α) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [e1]
    simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  rw [h1, map_mul, h2, mul_zero]

theorem intAE_one {D : D7} : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
  apply AddSubgroup.subset_closure
  exact ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩

theorem intAE_mul {D : D7} {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem x h =>
    obtain ⟨a, ha, s, rfl⟩ := h
    induction hy using AddSubgroup.closure_induction with
    | mem y h' =>
      obtain ⟨b, hb, t, rfl⟩ := h'
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, s * t, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; push_cast; rfl
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [mul_neg]; exact neg_mem h1
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg x _ h1 => rw [neg_mul]; exact neg_mem h1

theorem unr_off : ∀ (D : D7) (c : (AE D)ˣ →* Circle), Continuous c →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → UnrIdem c e := by
  intro D c hc
  obtain ⟨N, hN, hN1, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc
  refine ⟨N.primeFactors, fun q hq => Nat.prime_of_mem_primeFactors hq, ?_⟩
  intro w hw e he x hx h1 h2
  have hNw := natCast_not_mem hw hN le_rfl
  have hN0 : ((N : 𝓞 D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hg : finPart D (e * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹) ∈ intAE D :=
    not_not.1 ((he.2 _ hN0).not.1 hNw)
  have hNE : (((N : 𝓞 D.host.E) : D.host.E)) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : (N : AE D) * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹ = 1 := by
    rw [show (N : AE D) = incA D (((N : 𝓞 D.host.E) : D.host.E)) by simp, ← map_mul, mul_inv_cancel₀ hNE, map_one]
  have key : (x : AE D) - 1 = (N : AE D) * (e * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹ * ((x : AE D) - 1)) := by
    linear_combination (-1 : AE D) * hx - (e * ((x : AE D) - 1)) * hi
  refine hN1 x ⟨?_, h1, h2⟩ ⟨finPart D (e * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹) * (finPart D (x : AE D) - 1),
    intAE_mul hg (sub_mem h1 intAE_one), ?_⟩
  · have h0 := infPart_idem he.1
    have := congrArg (infPart D) hx
    simp only [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h0, zero_mul, zero_add, sub_zero] at this
    exact this.symm
  · have := congrArg (finPart D) key
    simp only [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, map_natCast] at this
    rw [nsmul_eq_mul]
    refine this.trans ?_
    simp only [RingHom.map_mul, map_natCast]

end GlobalTheory.UnrOff
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem GlobalTheory.NefRR.hdim_twist_twist_bound : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ M : LB X, M.IsLB → (∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (twist F M) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hp d L hL hE F _ hF M hM hFb i hi
  have := isNoetherian_of_isProjOver hp
  obtain ⟨_, _, hAmp⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  obtain ⟨A, B, hA, hB, s, t, hs, ht, hc⟩ := hAmp.exists_sub_of_mono_cutHom F (cls M hM)
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.higherCohomology_bound_twist_neg_of_regular_section' k X hp d L hL hE F hF B hB t ht hFb i hi
  have : Mono (cutHom F hA s) := hs
  have hcut : suppDim (cut F hA s) ≤ d := suppDim_cut_le F hA s hF
  have := isFiniteQC_cut F hA s
  have := isFiniteQC_twist (F := cut F hA s) hM
  obtain ⟨C₂, h₂⟩ := hE (twist (cut F hA s) M) (by rwa [suppDim_twist hM]) i hi
  refine ⟨C₁ + C₂, fun m => ?_⟩
  have hLm := isLB_lbPow hL m
  have hN := isLB_tens hM hLm
  have hBi := isLB_lbZPow hB (-1)
  have hN' := isLB_tens hBi hLm
  have key := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hp F A (tens M (lbPow L m)) (tens (lbZPow B (-1)) (lbPow L m)) hA hN hN' s hs
    (by
      change cls M hM + cls _ hLm = (cls _ hBi + cls _ hLm) + cls A hA
      rw [hc, cls_lbZPow hB]; abel)).1 i
  obtain ⟨e₁⟩ := nonempty_twist_twist_iso_of_cls_eq F hM hLm hN rfl
  obtain ⟨e₂⟩ := nonempty_twist_twist_iso_of_cls_eq F hBi hLm hN' rfl
  obtain ⟨e₃⟩ := nonempty_twist_twist_iso_of_cls_eq (cut F hA s) hM hLm hN rfl
  rw [hdim_congr k i e₁]
  rw [← hdim_congr k i e₂, ← hdim_congr k i e₃] at key
  have h₁m := h₁ m
  have h₂m := h₂ m
  have hpow : d * (m + 1) ^ (d - 1) ≤ (d + 1) * (m + 1) ^ d :=
    Nat.mul_le_mul (Nat.le_succ d) (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.sub_le d 1))
  calc _ ≤ _ := key
    _ ≤ C₁ * ((d + 1) * (m + 1) ^ d) + C₂ * ((d + 1) * (m + 1) ^ d) :=
        Nat.add_le_add h₁m (h₂m.trans (Nat.mul_le_mul_left _ hpow))
    _ = _ := (Nat.add_mul _ _ _).symm
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem hdim_zero_twistZ_eq_chi_of_suppDim_le_zero : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (F : Y.Modules) [IsFiniteQC F], suppDim F ≤ 0 → ∀ j : ℤ, (GlobalTheory.hdim k (GlobalTheory.twistZ F L j) 0 : ℤ) = GlobalTheory.chi k F := by
  intro k _ Y _ hP L hL F _ hF j
  have := isNoetherian_of_isProjOver hP
  rw [hdim_twist_of_suppDim_le_zero k hF (Twist.isLB_lbZPow hL j) 0,
    chi_eq_hdim_zero_of_suppDim_le_zero k hF]

end GlobalTheory.HSCore
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

theorem _root_.GlobalTheory.T.intersectionNumber_sheaf_eq_sum_length_mul_cycle : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (ι : Type) [Fintype ι] (P : ι → LB X), (∀ i, (P i).IsLB) → ∀ (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F], GlobalTheory.QCoh.suppDim F ≤ (Fintype.card ι : ℕ) → ∀ S : Finset X, (∀ w ∈ GlobalTheory.QCoh.support F, topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card ι : ℕ) → w ∈ S) → interNum κ F P = ∑ w ∈ S, ((Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :)).toNat : ℤ) * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  first | exact @GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed | exact GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed | (intros; apply GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DepthField

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.LawLog GlobalTheory.FactorDepth

section Monomials

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem toE_mono {x y : WithTop ℝ} (h : x ≤ y) : toE x ≤ toE y := WithBot.coe_le_coe.2 h

theorem le_toE_sum {ι : Type} (S : Finset ι) (g : ι → C) {r : EReal} (h : ∀ i ∈ S, r ≤ toE (v (g i))) :
    r ≤ toE (v (∑ i ∈ S, g i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, v.map_zero]; exact le_top
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine le_trans ?_ (toE_mono (v.map_add _ _))
    rcases min_choice (v (g a)) (v (∑ i ∈ S, g i)) with e | e <;> rw [e] <;> assumption

theorem derivAt0_subst {σ τ : Type} {E : σ → MvPowerSeries τ C} (hE : HasSubst E) (P : MvPolynomial τ C)
    (f : MvPowerSeries σ C) : ∃ S : Finset (σ →₀ ℕ),
      derivAt0 P (subst E f) = ∑ β ∈ S, coeff β f * derivAt0 P (subst E (monomial β (1 : C))) := by
  classical
  refine ⟨P.support.biUnion fun α => (coeff_subst_finite hE f α).toFinset, ?_⟩
  simp only [derivAt0, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [coeff_subst hE, finsum_eq_sum_of_support_subset (s := P.support.biUnion
    fun α => (coeff_subst_finite hE f α).toFinset) _ fun β hβ => by
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
      exact ⟨α, hα, (Set.Finite.mem_toFinset _).2 hβ⟩, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [subst_monomial hE, map_one, one_mul, smul_eq_mul]
  ring

variable {κ : Type} {d : κ → ℕ} {ι : κ → Type} [∀ b, Fintype (ι b)]

theorem hasSubst_lin (u : ∀ b, ι b → Fin (d b) → C) (b : κ) :
    ∀ e : Fin (d b), constantCoeff (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := by
  intro e

  simp [map_sum]

theorem hasSubst_expAlong [Finite κ] (G : ∀ b, LogFGL v (d b)) (u : ∀ b, ι b → Fin (d b) → C) :
    HasSubst (expAlong G u) :=
  hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)) (hasSubst_lin u x.1)
      ((isExp_expOf (G x.1)).1 x.2)

theorem depth_eq_iInf_monomial [Finite κ] (G : ∀ b, LogFGL v (d b)) (u : ∀ b, ι b → Fin (d b) → C)
    (P : MvPolynomial (Σ b, ι b) C) :
    depth G u P = ⨅ β : (Σ b, Fin (d b)) →₀ ℕ,
      toE (v (derivAt0 P (subst (expAlong G u) (monomial β (1 : C))))) := by
  classical
  refine le_antisymm (le_iInf fun β => iInf_le_of_le ⟨monomial β 1, fun α => ?_⟩ le_rfl) (le_iInf fun f => ?_)
  · rw [IsIntV, coeff_monomial]
    split_ifs <;> simp
  · obtain ⟨S, hS⟩ := derivAt0_subst (hasSubst_expAlong G u) P f.1
    rw [hS]
    refine le_toE_sum S _ fun β _ => iInf_le_of_le β (toE_mono ?_)
    rw [v.map_mul]
    exact le_add_of_nonneg_left (f.2 β)

end Monomials

section Map

variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {v : AddValuation C (WithTop ℝ)}
  {w : AddValuation K (WithTop ℝ)}

theorem derivAt0_map {σ : Type} (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (MvPolynomial.map φ P) (MvPowerSeries.map φ g) = φ (derivAt0 P g) := by

  simp only [derivAt0, MvPolynomial.support_map_of_injective _ φ.injective, map_sum, map_mul,
  MvPolynomial.coeff_map, coeff_map, mfact, Finsupp.prod, map_prod, map_natCast]

theorem expOf_map {d : ℕ} (G : LogFGL w d) (G' : LogFGL v d)
    (h : ∀ a, G'.lg a = MvPowerSeries.map φ (G.lg a)) (a : Fin d) :
    expOf G' a = MvPowerSeries.map φ (expOf G a) := by
  have he := isExp_expOf G
  have : IsExp G' fun a => MvPowerSeries.map φ (expOf G a) := by
    refine ⟨fun a => by simp [he.1 a], fun a => ?_⟩
    rw [h, ← map_subst (hasSubst_of_constantCoeff_zero he.1), he.2, map_X]
  rw [← isExp_unique G' this]

theorem depth_map {κ : Type} [Finite κ] {d : κ → ℕ} {ι : κ → Type} [∀ b, Fintype (ι b)]
    (hv : ∀ x, v (φ x) = w x) (G : ∀ b, LogFGL w (d b)) (G' : ∀ b, LogFGL v (d b))
    (h : ∀ b a, (G' b).lg a = MvPowerSeries.map φ ((G b).lg a)) (u : ∀ b, ι b → Fin (d b) → K)
    (P : MvPolynomial (Σ b, ι b) K) :
    depth G' (fun b a e => φ (u b a e)) (MvPolynomial.map φ P) = depth G u P := by
  have hE : expAlong G' (fun b a e => φ (u b a e)) = fun x => MvPowerSeries.map φ (expAlong G u x) := by
    funext x
    simp only [expAlong]
    rw [map_subst (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)), expOf_map φ _ _ (h x.1)]
    congr 1
    funext e

    simp [map_sum, smul_eq_C_mul]
  rw [depth_eq_iInf_monomial, depth_eq_iInf_monomial, hE]
  refine iInf_congr fun β => ?_
  rw [← hv, ← derivAt0_map, map_subst (hasSubst_expAlong G u), map_monomial, φ.map_one]

theorem detPow_map (i c : ℕ) : MvPolynomial.map φ (detPow K i c) = detPow C i c := by
  rw [detPow, detPow, map_pow, RingHom.map_det]
  congr 2
  ext a b
  simp

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog

theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ K) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv i f) = MvPowerSeries.pderiv i (MvPowerSeries.map φ f) := by
  ext α
  simp [MvPowerSeries.coeff_pderiv]

theorem om_map {d : ℕ} (G : FGLaw K d) :
    Om (GlobalTheory.FBMap.mapLaw φ G) = (Om G).map (MvPowerSeries.map φ) := by
  have hJ : JM (GlobalTheory.FBMap.mapLaw φ G) = (JM G).map (MvPowerSeries.map φ) := by
    ext1 i b
    simp only [JM, Jac, Matrix.map_apply, Matrix.of_apply]
    rw [GlobalTheory.FBMap.map_ev2 φ (GlobalTheory.FBMap.nc_pt _) GlobalTheory.FBMap.nc_zero, GlobalTheory.FBMap.mapPt_pt, GlobalTheory.FBMap.mapPt_zero,
      map_pderiv]
    rfl
  refine Matrix.inv_eq_left_inv ?_
  rw [hJ, ← Matrix.map_mul, om_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem logOf_map [CharZero K] [CharZero C] {d : ℕ} (G : FGLaw K d) (a : Fin d) :
    logOf (GlobalTheory.FBMap.mapLaw φ G) a = MvPowerSeries.map φ (logOf G a) := by
  rw [← sub_eq_zero, eq_C_of_pderiv_zero (g := logOf (GlobalTheory.FBMap.mapLaw φ G) a - MvPowerSeries.map φ (logOf G a))]
  · simp [logOf, constantCoeff_prim]
  · rintro ⟨j, b⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [map_sub, ← map_pderiv, pderiv_logOf, pderiv_logOf, om_map, Matrix.map_apply, sub_self]

theorem lg_logFGLOf_map [CharZero K] [CharZero C] {d : ℕ} (G : FGLaw K d) (hG) (hG') (a : Fin d) :
    (logFGLOf v (GlobalTheory.FBMap.mapLaw φ G) hG').lg a = MvPowerSeries.map φ ((logFGLOf w G hG).lg a) := by
  show subst (oneVar C d) (logOf (GlobalTheory.FBMap.mapLaw φ G) a) = MvPowerSeries.map φ (subst (oneVar K d) (logOf G a))
  rw [logOf_map, map_subst hs_oneVar]
  congr 1
  funext q
  simp [oneVar]

end Map

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth

theorem nuFacC_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X X' : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC Ch X f k = nuFacC Ch X' f k := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X X' f k
  letI := io.toAlgebra
  haveI : CharZero T.Fr := X.ιF.charZero
  let w : AddValuation T.Fr (WithTop ℝ) := (vX_vp X).comap X.ιF
  have hw : ∀ (Y : ValExt T p) x, vX_vp Y (Y.ιF x) = w x := by
    intro Y x
    show _ = vX_vp X (X.ιF x)
    by_cases hx : x = 0
    · rw [hx, Y.ιF.map_zero, X.ιF.map_zero, AddValuation.map_zero, AddValuation.map_zero]
    · rw [vX_vp_ιF Y hx, vX_vp_ιF X hx]
  have hG : ∀ a, MvIsInt w (subst (twoVars T.Fr _) (Ch.ch.B.G.F a)) := by
    intro a α
    have h := (fgl Ch X).F_int a α
    have e : (fgl Ch X).F a = MvPowerSeries.map X.ιF (subst (twoVars T.Fr _) (Ch.ch.B.G.F a)) := by
      rw [map_subst hs_twoVars]
      show subst (twoVars X.C _) (MvPowerSeries.map X.ιF (Ch.ch.B.G.F a)) = _
      congr 1
      funext q
      simp [twoVars]
    rw [e, coeff_map] at h
    exact h
  have key : ∀ Y : ValExt T p, nuFacC Ch Y f k = detDepth (logFGLOf w Ch.ch.B.G hG)
      (fun (a : Fin (rk f)) e => algebraMap T.V T.Fr (Ch.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩ e)) k := by
    intro Y
    rw [nuFacC, detDepth, detDepth, ← detPow_map Y.ιF]
    exact depth_map Y.ιF (hw Y) _ _ (fun _ a => lg_logFGLOf_map Y.ιF _ hG _ a) _ _
  rw [key, key]

end GlobalTheory.DepthField
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.orbitalIntegral_unitIndicator_eventually_oneClass : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ∀ γ : UL n w, γ.1.val.charpoly = atPl w P → (twOrb (MonoidHom.id _) (KL n w) γ ((KL n w : Set (UL n w)).indicator 1) = if ∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w then 1 else 0) ∧ kapSign n w (atPl w P) γ.1 = 1 ∧ ∀ Q₁ : (w.adicCompletion E)[X], Q₁ ∣ atPl w P → (∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w) → kapSign n w Q₁ γ.1 = 1 := by
  first | exact @GlobalTheory.BCT.OrbUnit.orbUnit_ae | exact GlobalTheory.BCT.OrbUnit.orbUnit_ae | (intros; apply GlobalTheory.BCT.OrbUnit.orbUnit_ae <;> assumption)
end
