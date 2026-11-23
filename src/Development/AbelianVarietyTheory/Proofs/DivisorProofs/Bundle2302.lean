module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle042
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle076
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle039
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle038
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle047
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle034
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle029
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle059
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle070
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false


namespace GlobalTheory.OrbitAdapt

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

theorem shortRule_change_mat (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (n : ℕ)
    (Λ : GenLat D.host.E n) (g : Matrix (Fin n) (Fin n) D.host.E) (b : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (hg : IsUnitaryM g) (hb : (T.dδ j n).l₂.M ∣ b)
    (hcg : GlobalTheory.UnRep.CongAt (stdLat D.host.E n) b b g)
    (hev : Even n) (hU : Λ.Unimod) (hU' : (actLat g Λ).Unimod) (hT : Λ.TrivAt (badN D))
    (hT' : (actLat g Λ).TrivAt (badN D)) (hM : Λ.TrivAt (T.dδ j n).l₂.M) (hM' : (actLat g Λ).TrivAt (T.dδ j n).l₂.M)
    (hP : P ∈ harmL T.Q.c Λ a) :
    ∃ (P' : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (ζ : T.Q.c.F), P' ∈ harmL T.Q.c (actLat g Λ) a ∧ ζ ≠ 0 ∧
      (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∀ (x0 : Fin n → (T.Q.Dw j).La) (N N' : ℕ) (f : Rul (T.Q.Xo j) T.Q.c),
        Λ.LevOK N (T.dδ j n).l₂.M → (actLat g Λ).LevOK N' (T.dδ j n).l₂.M →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) (actLat g Λ) N' x0 P' (ζ • f) := by
  set d := T.dδ j n with hd
  obtain ⟨_, hnab⟩ := hF.sh.dNab j hj n
  have hCI := GlobalTheory.T.harmonic_germ_value_chart_independent
  have hbad := GlobalTheory.ShortChange.badOK_host D T.Q.H d.l₂
  have hdv : D.host.QS * D.host.q * D.host.d ∣ badN D := Dvd.intro _ rfl
  have hb1 : D.host.QS * D.host.q * D.host.d * d.l₂.M ≠ 1 := fun h => by
    have := hbad.2.1
    omega
  have hB := GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT) hM
  have hB' := GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT') hM'
  have hK := hF.p.kPsi j hj
  obtain ⟨ze, ⟨k, hk, hze⟩, hrep⟩ := GlobalTheory.T.thetaChangeOfRepRootOfUnity_of_chartIndependence hCI D.host.E T.Q.H (T.Q.Dw j) d.l₂ d.Xo₂ d.c₂ d.nab₂ n
    ⟨(GlobalTheory.PlaceInt.host_galois_discr_moves D T.Q.H).1, GlobalTheory.ShortChange.odd_rank T hF j hj, hev, hnab⟩ _ hbad
    Λ g _ _ hU hg hB hB' (isBeta_cover d hK hb1 Λ hU hB) (isBeta_cover d hK hb1 _ hU' hB')
  have hP' := ((GlobalTheory.PushKeeps.push_keeps D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c n a g hg).2 Λ).2.2.2 P hP
  have hz : d.eF.symm ze ^ k = 1 := by rw [← map_pow, hze, map_one]
  refine ⟨pushLet T.Q.c g P, d.eF.symm ze, hP', fun h0 => ?_, ⟨k, hk, hz⟩,
    fun x0 N N' f hN hN' hR K _ _ _ _ hKe y y₂ hy => ?_⟩
  · rw [h0, zero_pow hk.ne'] at hz
    exact zero_ne_one hz
  obtain ⟨v, hv, hval⟩ := hR K hKe y y₂ hy
  have h₂ := (((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d Λ).2.1 a P hP).1)
  have h₂' := (((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d _).2.1 a _ hP').1)
  obtain ⟨v', hv', -⟩ := (GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.firstFiveLaws.1 hCI D.host.E T.Q.H (T.Q.Dw j)
    d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n _ N' hU' hM' hN' a _ h₂'.1 (d.w x0)
    (d.eF (betaH (Dw := T.Q.Dw j) T.Q.c (actLat g Λ)))).1 K y₂
  refine ⟨v', hv', ?_⟩
  rw [map_pushLet] at hv'
  have hvv := hrep (d.w x0) (fixesDatum_of_congAt d.c₂ hb hcg _) N N' hN hN' a _ h₂ K y₂ v v' hv hv'
  have hs : evR (T.Q.Xo j) T.Q.c (d.eF.symm ze • f) y =
      algebraMap T.Q.c.F K (d.eF.symm ze) * evR (T.Q.Xo j) T.Q.c f y :=
    evR_mul (T.Q.Xo j) T.Q.c _ f _ (fun p y => Algebra.smul_def _ _) y
  rw [hs, hval, hvv, ← hKe, AlgEquiv.apply_symm_apply]
  ring

theorem congAt_of_cols {E : Type} [Field E] [NumberField E] {n : ℕ} (gm : Matrix (Fin n) (Fin n) E) (m : ℕ)
    (h : ∀ j : Fin n, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt m (fun i => gm i j)
      fun i => (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) :
    GlobalTheory.UnRep.CongAt (stdLat E n) m m gm := by
  choose k hk b hb using h
  refine ⟨∏ j, k j, Nat.Coprime.prod_left fun j _ => hk j, fun v hv => ?_⟩
  have hv' : ∀ i, ∃ y : 𝓞 E, (y : E) = v i := fun i => by
    have := (Submodule.mem_pi.1 hv) i (Set.mem_univ _)
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact ⟨y, hy⟩
  choose y hy using hv'
  refine ⟨fun i => ((∑ j, ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : 𝓞 E) * b j i * y j : 𝓞 E) : E), ?_, ?_⟩
  · refine Submodule.mem_pi.2 fun i _ => Submodule.mem_one.2 ⟨_, rfl⟩
  · funext i
    have e1 : ∀ j, ((∏ l, k l : ℕ) : E) * (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) =
        ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : E) * ((m : E) * (b j i : E)) := fun j => by
      have hp : (∏ l, k l) = k j * ∏ l ∈ Finset.univ.erase j, k l :=
        (Finset.mul_prod_erase (s := Finset.univ) (f := k) (Finset.mem_univ j)).symm
      rw [hp]
      push_cast
      have h' := hb j i
      simp only at h'
      linear_combination (∏ l ∈ Finset.univ.erase j, ((k l : ℕ) : E)) * h'
    have e2 : (gm.mulVec v - v) i = ∑ j, (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) * v j := by
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
      congr 1
      simp [Matrix.one_apply]
    simp only [Pi.smul_apply, nsmul_eq_mul, e2]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hy j]
    have h' := e1 j
    push_cast at h'
    linear_combination ((y j : 𝓞 E) : E) * h'

theorem plc_prime {K : Type} [Field K] [NumberField K] (lam : HeightOneSpectrum (𝓞 K)) : (Formalism.EigenvalueLevelCeiling.plc lam).Prime := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  haveI : lam.asIdeal.IsPrime := lam.isPrime
  have hne : Ideal.absNorm lam.asIdeal ≠ 0 := fun h => lam.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hz : ((Ideal.absNorm lam.asIdeal : ℕ) : 𝓞 K ⧸ lam.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have hd : ringChar (𝓞 K ⧸ lam.asIdeal) ∣ Ideal.absNorm lam.asIdeal :=
    (ringChar.spec (𝓞 K ⧸ lam.asIdeal) _).1 hz
  rcases CharP.char_is_prime_or_zero (𝓞 K ⧸ lam.asIdeal) (ringChar (𝓞 K ⧸ lam.asIdeal)) with h | h
  · exact h
  · rw [h, zero_dvd_iff] at hd
    exact absurd hd hne



attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem star_mem_one (D : D7) {x : D.host.E} (hx : x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) :
    star x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨⟨star (algebraMap _ _ y),
    (RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem zero_case (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (hL : Formalism.IndefR.Bridge.hLat V 1 = stdLat D.host.E V.rank)
    (Λ : GenLat D.host.E V.rank) (hT : Λ.TrivAt 0) :
    (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V 1)) ∧
      (∀ b, Formalism.IndefR.FWT.SplitOffBad V b 1) ∧ ∀ m, Λ.TrivAt m := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  obtain rfl : k = 1 := (Nat.coprime_zero_right k).1 hk
  simp only [Nat.cast_one, Ideal.span_singleton_one, Submodule.top_smul] at h1 h2
  have hΛ : Λ.La = stdLat D.host.E V.rank := le_antisymm h1 h2
  refine ⟨fun w => ?_, fun b => ?_, fun m => ⟨1, Nat.coprime_one_left m, by simpa using h1, by simpa using h2⟩⟩
  · have hf : Formalism.IndefR.FWT.fin V (1 : Formalism.L2.Theta.GA D V) = 1 := map_one _
    rw [hf, hL, hΛ]
    constructor
    · intro hw
      exact Submodule.mem_pi.2 fun i _ => star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))
    · intro hw
      refine Submodule.mem_pi.2 fun i _ => ?_
      have := star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))
      simpa only [star_star] using this
  · refine ⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, by simp, by simp⟩, by simp⟩, by simp, fun a c => ?_⟩
    have : Formalism.L2.Theta.mt V (1 : Formalism.L2.Theta.GA D V) = 1 := by simp [Formalism.L2.Theta.mt]
    simp [this]

end GlobalTheory.OrbitAdapt
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor NegIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SqTower.TopGridExists


open Matrix in
theorem exists_isONBasis {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {ε : Fin k → Bool}
    (hG : Bᴴ * G * B = Formalism.REAL.Jm ε) (hs : s * B = B * Formalism.REAL.Jm ε) :
    ∃ (B' : Matrix (Fin k) (Fin k) ℂ) (p : ℕ), IsONBasis G s B' p := by
  obtain ⟨π, hπ⟩ := GlobalTheory.FockOrder.exists_sortPerm ε
  generalize (Finset.univ.filter fun a => ε a = true).card = p at hπ
  have hJ : (Matrix.diagonal fun a => (((if ε a then 1 else -1 : ℝ)) : ℂ)) = Formalism.REAL.Jm ε := by
    unfold Formalism.REAL.Jm
    congr 1
    funext a
    cases ε a <;> simp
  refine ⟨B.submatrix id π, p, fun a => if a.val < p then 1 else -1, fun a => ?_, ?_, ?_⟩
  · by_cases ha : a.val < p
    · left; simp [ha]
    · right; simp [ha, not_lt.1 ha]
  · have e : (B.submatrix id π)ᴴ * G * B.submatrix id π = (Bᴴ * G * B).submatrix π π := by
      ext a b; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [e, hG, ← hJ, Matrix.submatrix_diagonal_equiv]
    congr 1; funext a; simp [hπ a]
  · have e : s * B.submatrix id π = (s * B).submatrix id π := by
      ext a b; simp [Matrix.mul_apply]
    rw [e, hs, ← Matrix.submatrix_mul_equiv (e₂ := π), ← hJ, Matrix.submatrix_diagonal_equiv]
    congr 2; funext a; simp [hπ a]


open Matrix GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in
theorem exists_rig_of_frame {D : D7} {V : HSp D} (A : Fr V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : ∃ r : Rig V, r.Λ = Λ ∧ r.s = A.cart ∧ r.Is := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E V.rank Λ hfull
  have hτ : ∀ τ : D.what₂.Tau, ∃ (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : ℕ),
      IsONBasis (gramAt D V τ) (A.cart τ) B p := fun τ => by
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
    have h1 := Matrix.mul_nonsing_inv _ hu
    refine exists_isONBasis (B := (A.fr τ)⁻¹) (ε := A.ε τ) ?_ ?_
    · rw [← A.fr_gram τ]
      simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]
    · simp only [Fr.cart, Matrix.mul_assoc, h1, Matrix.mul_one]
  choose B hB using hτ
  exact ⟨⟨Λ, β, A.cart, B⟩, rfl, rfl, hΛ, hβ, fun τ => ⟨GlobalTheory.CompactFockAction.cart_isCartanInv A τ, hB τ⟩⟩


end GlobalTheory.SqTower.TopGridExists

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
open Filter Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem clm_eq_sum_single_smul_proj {g : ℕ} (f : (Fin g → ℂ) →L[ℂ] ℂ) :
    f = ∑ a, f (Pi.single a 1) • (ContinuousLinearMap.proj a : (Fin g → ℂ) →L[ℂ] ℂ) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  conv_lhs => rw [pi_eq_sum_univ' v]

  simp [map_sum, mul_comm]

theorem fderiv_partial_symm {g : ℕ} {s : Set (Fin g → ℂ)} (hs : IsOpen s) {h : (Fin g → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h s) {k : Fin g → (Fin g → ℂ) → ℂ} (hk : ∀ a, DifferentiableOn ℂ (k a) s)
    (e : ∀ a, ∀ z ∈ s, fderiv ℂ h z (Pi.single a 1) = k a z) (a b : Fin g) {z : Fin g → ℂ} (hz : z ∈ s) :
    fderiv ℂ (k b) z (Pi.single a 1) = fderiv ℂ (k a) z (Pi.single b 1) := by
  have hn : s ∈ 𝓝 z := hs.mem_nhds hz
  have h1 : ∀ᶠ y in 𝓝 z, HasFDerivAt h (fderiv ℂ h y) y := by
    filter_upwards [hn] with y hy using (hh.differentiableAt (hs.mem_nhds hy)).hasFDerivAt
  have h2 : fderiv ℂ h =ᶠ[𝓝 z]
      fun y ↦ ∑ c, k c y • (ContinuousLinearMap.proj c : (Fin g → ℂ) →L[ℂ] ℂ) := by
    filter_upwards [hn] with y hy
    rw [clm_eq_sum_single_smul_proj (fderiv ℂ h y)]
    exact Finset.sum_congr rfl fun c _ ↦ by rw [e c y hy]
  have h3 : DifferentiableAt ℂ (fderiv ℂ h) z := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ h2
    exact DifferentiableAt.fun_sum fun c _ ↦ ((hk c).differentiableAt hn).smul_const _
  have h4 : ∀ c v, fderiv ℂ (k c) z v = fderiv ℂ (fderiv ℂ h) z v (Pi.single c 1) := by
    intro c v
    have h5 : k c =ᶠ[𝓝 z] fun y ↦ fderiv ℂ h y (Pi.single c 1) := by
      filter_upwards [hn] with y hy using (e c y hy).symm
    rw [h5.fderiv_eq, fderiv_clm_apply h3 (differentiableAt_const _)]
    simp
  rw [h4, h4]
  exact second_derivative_symmetric_of_eventually h1 h3.hasFDerivAt _ _

theorem exists_closed_form_fderiv_eq (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g)
    (hA : IsAbelianScheme A) (U : A.left.affineOpens) (h : (Fin g → ℂ) → ℂ) (hh : DifferentiableOn ℂ h (pre u.ex U.1))
    (hr : ∀ a, IsReg u.ex U.1 fun z => fderiv ℂ h z (Pi.single a 1)) :
    ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧ ∀ z ∈ pre u.ex U.1, fderiv ℂ h z = evForm u.ex U.1 z ξ := by
  obtain ⟨hop, hdiff, -, -, -, -, -, -, -, halg, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨d, ω, hcomm, hd, hdual, hspan, hev⟩ := GlobalTheory.T.kaehler_differentials_free_coordinate_forms_abelian A g L u hA U
  choose k₀ hk₀ using hr
  let k : Fin g → Sec (str A) U.1 := k₀
  have hk : ∀ a, ∀ z ∈ pre u.ex U.1, fderiv ℂ h z (Pi.single a 1) = val u.ex U.1 (k a) z := hk₀
  refine ⟨∑ a, k a • ω a, GlobalTheory.T.deRhamDerivative_eq_zero_of_symmetric_frame _ g d ω hcomm hdual hspan k fun a b ↦ ?_, fun z hz ↦ ?_⟩
  · have h0 : d a (k b) - d b (k a) = 0 := by
      refine GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA U.1 _ fun z hz ↦ ?_
      obtain ⟨e, he⟩ := halg U.1 z hz
      have h1 := he (d a (k b) - d b (k a))
      rw [map_sub, ← he (d a (k b)), ← he (d b (k a)), hd a _ z hz, hd b _ z hz,
        fderiv_partial_symm (hop U.1) hh (fun c ↦ hdiff U.1 (k c)) hk a b hz, sub_self] at h1
      exact h1
    exact sub_eq_zero.mp h0
  · rw [clm_eq_sum_single_smul_proj (fderiv ℂ h z), clm_eq_sum_single_smul_proj (evForm u.ex U.1 z _)]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have h1 : (d a).liftKaehlerDifferential (∑ c, k c • ω c) = k a := by

      simp [map_sum, hdual]
    rw [hev a _ z hz, h1, hk a z hz]

end GlobalTheory.CechPer
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

theorem _root_.GlobalTheory.T.kirillov_semilocal_smooth_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ t : GA E (m + 1), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ g, φ.1 (g * t) = φ.1 g) → ∀ g, F (g * t) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  first | (exact @GlobalTheory.JSW.KirSemi.kirillov_semilocal_bump) | (exact GlobalTheory.JSW.KirSemi.kirillov_semilocal_bump) | (intros; apply GlobalTheory.JSW.KirSemi.kirillov_semilocal_bump  <;> assumption)
end

section

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem lieScalarD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    ∃ c, ActsByD τ C om Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hom
  obtain ⟨ω₀, c₀, hH, hc, hact⟩ := GlobalTheory.T.exists_genuineSplitting_adelicSchwartz_placeSignature F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ν, hν, hmul, hνc, hν0⟩ := GlobalTheory.T.archimedean_splittings_differ_by_character F E σ α β κ ψ JA JB d om ω₀ hψ hom hH hc
  obtain ⟨k, hk⟩ := GlobalTheory.T.deriv_continuous_character_real_unitary_one_parameter F E σ β R S τ JB b C hCM hFr.2.2 ν hmul hνc hν0
  refine ⟨fun w => c₀ w + k w, ?_⟩
  intro γ hγ Y hY T g hg l hl
  have hH1 : ∀ t : ℝ, At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) := fun t => hγ.2 _
  have hpm : ∀ f : SInf F κ, pureA F f g ∈ schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have e1 : (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) =
      fun t => ν (γ (Multiplicative.ofAdd t)) * l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g)) := by
    funext t; rw [hν _ (hH1 t) _ (hpm _), map_smul, smul_eq_mul]
  show HasDerivAt (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) _ 0
  rw [e1]
  have h3 := (hk γ hγ Y hY).mul (hact γ hγ Y hY T g hg l hl)
  have hγ0 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by rw [ofAdd_zero, map_one]
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hν1 : ν 1 = 1 := by
    have := hmul 1 1 h1m h1m
    rw [mul_one] at this
    exact (mul_eq_left₀ (hν0 1 h1m)).mp this.symm
  beta_reduce at h3
  set_option backward.isDefEq.respectTransparency false in
    rw [hγ0, hν1, map_one, Module.End.one_apply, one_mul] at h3
  refine h3.congr_deriv ?_
  have e2 : sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) +
        (((fun w => c₀ w + k w) w) * (Y w).trace) • (1 : Module.End ℂ _)) =
      sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) +
        (∑ w, k w * (Y w).trace) • (1 : Module.End ℂ (TensD F P Q R S)) := by
    simp only [add_mul, add_smul, ← add_assoc]
    exact GlobalTheory.LieScal.sumPl_add_smul
      (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) _
  rw [e2, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul]
  have key : ∀ (z : ℂ) (f f' : SInf F κ), pureA F ⇑(f' + z • f) g = z • pureA F ⇑f g + pureA F ⇑f' g := by
    intro z f f'; funext x; simp [pureA]; ring
  rw [key, map_add (f := _), map_smul, smul_eq_mul]

end GlobalTheory.HoweD

end
end
