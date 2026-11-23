module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormIntegralIffLatticeUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle121
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsONFr
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle048
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle041
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwOrbLevel

open GlobalTheory.TwLat

theorem twOrb_level_eq_stSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K), Q.Monic → Q.natDegree = m → Q.Separable → IsCsr w Q → Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ → aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (1 + algebraMap K.O B.A t * B.g) * B.σ (1 + algebraMap K.O B.A t * B.g) = 1 → stTw m w Q (fun y : GLw m w => if y ∈ GlobalTheory.LFun.KGL w (n := m) ∧ nrmL m w y ∈ {g : GLw m w | g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) = ((B.stSum : ℚ) : ℂ) := by
  intro E _ _ _ hE w hw K e hc hint hval hq k t ht htk m Q B hQm hQd hQs hQc hadj hQu hfin huσ
  set u : B.A := 1 + algebraMap K.O B.A t * B.g with hu_def
  obtain ⟨-, -, hθK, hnrm, -, -, -, -, -, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hE m w
  set cong : Set (GLw m w) := {g : GLw m w | g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (g.val i j -
    (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} with hcong
  set f : GLw m w → ℂ := fun y => if y ∈ GlobalTheory.LFun.KGL w (n := m) ∧ nrmL m w y ∈ cong then 1 else 0 with hf
  set S : Set (GLw m w) := {y | (nrmL m w y).val.charpoly = Q} with hS
  show clSum (thL m w) (GlobalTheory.LFun.KGL w (n := m)) S (fun _ => 1) f = _
  have hfK : ∀ c ∈ GlobalTheory.LFun.KGL w (n := m), ∀ y, f (c⁻¹ * y * thL m w c) = f y := by
    intro c hcK y
    have h1 : c⁻¹ * y * thL m w c ∈ GlobalTheory.LFun.KGL w (n := m) ↔ y ∈ GlobalTheory.LFun.KGL w (n := m) := by
      constructor
      · intro h
        have := mul_mem (mul_mem hcK h) (inv_mem (hθK c hcK))
        simpa [mul_assoc] using this
      · intro h
        exact mul_mem (mul_mem (inv_mem hcK) h) (hθK c hcK)
    have h2 : nrmL m w (c⁻¹ * y * thL m w c) ∈ cong ↔ nrmL m w y ∈ cong := by
      rw [hnrm]; exact GlobalTheory.T.principalCongruenceGL_conj_maxCompact_iff E w m k c _ hcK
    simp only [hf, h1, h2]
  have hf01 : ∀ y, f y = 0 ∨ f y = 1 := by
    intro y; simp only [hf]; split_ifs <;> simp
  have hSinv : ∀ y g, g⁻¹ * y * thL m w g ∈ S ↔ y ∈ S := by
    intro y g
    simp only [hS, Set.mem_setOf_eq, hnrm, Units.val_mul]
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hrstab : ∀ (δ x : GLw m w), (rStab fun k : GlobalTheory.LFun.KGL w (n := m) => f ((x * k)⁻¹ * δ * thL m w (x * k))).index ≠ 0 := by
    intro δ x
    have : rStab (fun k : GlobalTheory.LFun.KGL w (n := m) => f ((x * k)⁻¹ * δ * thL m w (x * k))) = ⊤ := by
      refine eq_top_iff.2 fun k' _ z => ?_
      have := hfK (k' : GLw m w) k'.2 ((x * ↑z)⁻¹ * δ * thL m w (x * ↑z))
      show f ((x * ↑(z * k'))⁻¹ * δ * thL m w (x * ↑(z * k'))) = f ((x * ↑z)⁻¹ * δ * thL m w (x * ↑z))
      rw [← this]
      congr 1
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    rw [this, Subgroup.index_top]; exact one_ne_zero
  have htwinv : ∀ y g, twOrb (thL m w) (GlobalTheory.LFun.KGL w (n := m)) (g⁻¹ * y * thL m w g) f = twOrb (thL m w) (GlobalTheory.LFun.KGL w (n := m)) y f :=
    fun y g => GlobalTheory.TwOrbConj.twOrb_twConj _ _ _ y g f (hrstab y)
  have hrank : Module.finrank K.E B.A = m := hfin.trans hQd
  let b : Module.Basis (Fin m) K.E B.A := Module.finBasisOfFinrankEq K.E B.A hrank
  have hgu : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) → ∀ y ∈ L, u * y ∈ L := by
    intro L hg y hy
    rw [hu_def, add_mul, one_mul, mul_assoc]
    refine L.add_mem hy ?_
    rw [← Algebra.smul_def]
    exact L.smul_mem t (hg y hy)
  by_cases hui : IsIntegral K.O u
  · let Bu : GlobalTheory.UnitLemma.InvAlg K := { B with g := u }
    have hP : (LinearMap.mulLeft K.E u).charpoly = Q.map e.symm.toRingHom :=
      GlobalTheory.T.charpoly_mulLeft_generator_eq_map_symm K B _ e u Q hQm hadj hQu hfin
    have hsep : (Q.map e.symm.toRingHom).Separable := hQs.map
    obtain ⟨β₀, hβ₀, hX⟩ := GlobalTheory.UnitLemma.TwistUnit.twisted_unit_eq_unit K Bu huσ
      (by show (LinearMap.mulLeft K.E u).charpoly.Separable; rw [hP]; exact hsep) hui ((-1) ^ (m - 1))
      (neg_one_pow_eq_or B.A (m - 1))
    have hβ₀' : B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) := hβ₀
    have hgram : ∀ x : B.Aˣ, IsUnit (gram e b ((β₀ : B.A) * x)) := fun x =>
      GlobalTheory.T.separable_element_basis_integral E hE w hw K e hc hint hval B m b u _ hsep hQu hadj _ (β₀.isUnit.mul x.isUnit)
    have hσβ : ∀ x : B.Aˣ, B.σ (x : B.A) = x → B.σ ((β₀ : B.A) * x) = (β₀ * x) * ((-1) ^ (m - 1) * u) := by
      intro x hx
      rw [map_mul, hβ₀', hx]; ring
    have hN : ∀ x : B.Aˣ, B.σ (x : B.A) = x → (nrmL m w (dlt e b ((β₀ : B.A) * x))).val = mulMat e b u :=
      fun x hx => GlobalTheory.T.inertPlace_norm_gramInverse_eq_mulMatrix E hE w hw K e hc hint hval B m b u _ (hgram x) (hσβ x hx)
    have hcp : (mulMat e b u).charpoly = Q := by
      have h1 := Matrix.charpoly_map (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)) (e : K.E →+* w.adicCompletion E)
      have h2 : mulMat e b u = (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map (e : K.E →+* w.adicCompletion E) := rfl
      rw [h2, h1, LinearMap.charpoly_toMatrix, hP, Polynomial.map_map]
      ext n
      simp [Polynomial.coeff_map]
    obtain ⟨hΛK, hlat⟩ := GlobalTheory.T.latticeSpannedByGLColumns_eq_iff_GLint_coset E hE w hw K e hc hint hval B m b
    have hOrb : ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        twOrb (thL m w) (GlobalTheory.LFun.KGL w (n := m)) (dlt e b ((β₀ : B.A) * x)) f = ((B.N x : ℚ) : ℂ) := by
      intro x hx
      obtain ⟨φ, hφv, hφc⟩ := GlobalTheory.T.twistedCentralizer_equiv_normOneTorus_nonsplit E hE w hw K e hc hint hval B m b u _ (β₀.isUnit.mul x.isUnit)
        (hσβ x hx) hadj (hgram x)
      refine GlobalTheory.T.twistedOrbitalIntegral_indicator_eq_latticeCount K B x (GLw m w) (thL m w) (GlobalTheory.LFun.KGL w (n := m)) _ f φ (lat e b) hfK hf01 hφc hΛK ?_ ?_
        (fun L hL => GlobalTheory.T.exists_GL_completion_lattice_eq_columns E hE w hw K e hc hint hval B m b L hL.1)
      · intro t' q
        refine GlobalTheory.T.latticeSpannedByGLColumns_mulLeftMatrix_eq_mul E hE w hw K e hc hint hval B m b _ q _ ?_
        rw [Units.val_mul, hφv t']
      · intro q
        have hf1 : f (q⁻¹ * dlt e b ((β₀ : B.A) * x) * thL m w q) = 1 ↔
            (q⁻¹ * dlt e b ((β₀ : B.A) * x) * thL m w q ∈ GlobalTheory.LFun.KGL w (n := m) ∧
              nrmL m w (q⁻¹ * dlt e b ((β₀ : B.A) * x) * thL m w q) ∈ cong) := by
          simp only [hf]; split_ifs with h <;> simp [h]
        rw [hf1, hnrm, GlobalTheory.T.twistedNorm_integral_iff_lattice_unimodular E hE w hw K e hc hint hval B m b _ (hgram x) q]
        have hlev : q⁻¹ * nrmL m w (dlt e b ((β₀ : B.A) * x)) * q ∈ cong ↔
            ∀ y ∈ lat e b q, B.g * y ∈ lat e b q :=
          GlobalTheory.T.principalCongruenceLevel_iff_lattice_stable E hE w hw K e hc hint hval B m b t k ht htk q _ (hN x hx)
        rw [hlev]
        have hXiff : (GlobalTheory.UnitLemma.IsLat K.O K.E (lat e b q) ∧ ∀ z, z ∈ lat e b q ↔
            ∀ y ∈ lat e b q, B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range) ↔ lat e b q ∈ Bu.X x := by
          rw [← hX x hx]; rfl
        constructor
        · rintro ⟨hL, hg, hsd⟩
          exact ⟨(hXiff.2 ⟨hL, hgu _ hg, hsd⟩).2, hg⟩
        · rintro ⟨hun, hg⟩
          obtain ⟨hL, -, hsd⟩ := hXiff.1 ⟨hlat q, hun⟩
          exact ⟨hL, hg, hsd⟩
    have hsum := GlobalTheory.T.sum_twistedOrbitalIntegrals_eq_finsum_parametrised (GLw m w) (thL m w) (GlobalTheory.LFun.KGL w (n := m)) S f B.Cl
      (fun c => dlt e b ((β₀ : B.A) * ((Quot.out c).1 : B.Aˣ))) (fun c => ((B.N c.rep : ℚ) : ℂ))
      (fun c => by show (nrmL m w _).val.charpoly = Q; rw [hN _ (Quot.out c).2]; exact hcp)
      (by
        intro y hy
        obtain ⟨x, hx, g, rfl⟩ := GlobalTheory.T.exists_twistedConj_delta_of_unit_mod_norms E hE w hw K e hc hint hval B m b u Q hQs hQu hadj β₀ hβ₀' hgram y hy
        let c : B.Cl := Quot.mk _ ⟨x, hx⟩
        obtain ⟨a, ha⟩ := GlobalTheory.T.exists_norm_of_classOfFixedUnits_eq K B ⟨x, hx⟩ (Quot.out c) (Quot.out_eq c).symm
        obtain ⟨g', hg'⟩ := (GlobalTheory.T.twistedConj_iff_mul_norm_invAlg E hE w hw K e hc hint hval B m b u hadj β₀ hβ₀' hgram x (Quot.out c).1 hx
          (Quot.out c).2).2 ⟨a, ha⟩
        refine ⟨c, g'⁻¹ * g, ?_⟩
        show _ = _ * dlt e b ((β₀ : B.A) * ((Quot.out c).1 : B.Aˣ)) * _
        rw [hg']
        simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left])
      (by
        intro c c' hcc
        obtain ⟨a, ha⟩ := (GlobalTheory.T.twistedConj_iff_mul_norm_invAlg E hE w hw K e hc hint hval B m b u hadj β₀ hβ₀' hgram (Quot.out c).1
          (Quot.out c').1 (Quot.out c).2 (Quot.out c').2).1 hcc
        rw [← Quot.out_eq c, ← Quot.out_eq c']
        exact Quot.sound ⟨a, ha⟩)
      hSinv htwinv (fun c => hOrb _ (Quot.out c).2)
    rw [hsum]
    show _ = ((∑ᶠ c : B.Cl, B.N c.rep : ℚ) : ℂ)
    by_cases hfs : (Function.support fun c : B.Cl => B.N c.rep).Finite
    · exact (map_finsum (Rat.castHom ℂ) hfs).symm
    · have hfs' : ¬ (Function.support fun c : B.Cl => ((B.N c.rep : ℚ) : ℂ)).Finite := by
        simpa [Function.support] using hfs
      rw [finsum_of_infinite_support hfs, finsum_of_infinite_support hfs']
      simp
  · have hX0 : ∀ x : B.A, B.X x = ∅ := by
      intro x
      ext L
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨hL, hg, -⟩
      exact hui (GlobalTheory.T.isIntegral_of_preserves_fullLattice K B u L hL (hgu L hg))
    have hN0 : ∀ x : B.A, B.N x = 0 := by
      intro x
      unfold GlobalTheory.UnitLemma.InvAlg.N GlobalTheory.UnitLemma.orbSum
      haveI : IsEmpty (GlobalTheory.UnitLemma.Orb K.O B.T (B.X x)) := by
        constructor
        intro o
        induction o using Quot.ind with
        | mk L =>
          have h := (hX0 x).subset L.2
          simp at h
      exact finsum_of_isEmpty _
    have hf0 : ∀ y ∈ S, ∀ q : GLw m w, f (q⁻¹ * y * thL m w q) = 0 := by
      intro y hy q
      simp only [hf]
      rw [if_neg]
      rintro ⟨-, hn, -⟩
      exact hui (GlobalTheory.T.isIntegral_of_integral_matrix_charpoly_root E hE w hw K e hc hint hval B m b u Q hQm hQu _ hn ((hSinv y q).2 hy))
    have hst : B.stSum = 0 := by
      unfold GlobalTheory.UnitLemma.InvAlg.stSum
      simp [hN0]
    rw [hst, Rat.cast_zero]
    unfold clSum
    refine (finsum_congr fun c => ?_).trans finsum_zero
    split_ifs with hc'
    · have h0 := hf0 _ hc'
      simp only [twOrb, avg, h0, finsum_zero, mul_zero]
    · rfl

end GlobalTheory.TwOrbLevel
end

section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdTh
open GlobalTheory.SW hiding Level
open GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant (detPos detNeg vacChar)
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameEquiv.CompactMove

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

theorem thR_of_perC (x x' : Frame X.Ψ r) (M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det)
    (h : ∀ u, (fun j => perC X x' u (idx j)) = M *ᵥ fun j => perC X x u (idx j))
    (φ : TF n g) (v : WR X n) :
    _root_.GlobalTheory.Ker.thR X bas idx φ x' v = (M.det⁻¹) ^ (n / 2) * _root_.GlobalTheory.Ker.thR X bas idx φ x v := by
  have hP : ∀ s, perMat X bas idx s x' = M * perMat X bas idx s x := by
    intro s
    ext i k
    exact congrFun (h fun (τ : X.Ψ) => Data.emb τ.1 (bas (Pi.single (s k) 1))) i
  have hH : hMat X bas idx x' = hMat X bas idx x * M⁻¹ := by
    rw [hMat, hP, Matrix.mul_inv_rev, hMat]
  have hT : tauMat X bas idx x' = tauMat X bas idx x := by
    rw [tauMat, hH, hP, Matrix.mul_assoc, ← Matrix.mul_assoc M⁻¹, nonsing_inv_mul _ hM, Matrix.one_mul, tauMat]
  have hI : imInv X bas idx x' = imInv X bas idx x := by rw [imInv, imInv, hT]
  have hz : ∀ b, hMat X bas idx x' *ᵥ zR X idx x' v b = hMat X bas idx x *ᵥ zR X idx x v b := by
    intro b
    have : zR X idx x' v b = M *ᵥ zR X idx x v b := h fun τ => v τ b
    rw [this, hH, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.mul_one]
  simp only [_root_.GlobalTheory.Ker.thR, gaussR, GlobalTheory.Dict.hx, _root_.GlobalTheory.SW.thA, hz, hT, hI]
  rw [hH, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', mul_pow]
  ring

theorem thR_block (x x' : Frame X.Ψ r) (b : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hb : ∀ τ, IsUnit (b τ).det)
    (hxb : ∀ τ, mat x' τ = mat x τ * b τ) (hc : ∀ τ, b τ * prFst r X.p0 = prFst r X.p0 * b τ)
    (φ : TF n g) (v : WR X n) :
    _root_.GlobalTheory.Ker.thR X bas idx φ x' v = (∏ τ, (((1 - prFst r X.p0) * b τ + prFst r X.p0).det /
      (prFst r X.p0 * b τ + (1 - prFst r X.p0)).det) ^ (n / 2)) * _root_.GlobalTheory.Ker.thR X bas idx φ x v := by
  classical
  set P := prFst r X.p0 with hP
  let N : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => P * (b τ)ᵀ + (1 - P) * (b τ)⁻¹
  have hN : ∀ τ, (N τ).det ≠ 0 ∧ (N τ).det = (P * b τ + (1 - P)).det / ((1 - P) * b τ + P).det := fun τ =>
    det_tr_inv_block P (1 - P) (b τ) (hb τ) (by abel) (by
      rw [hP, prFst, diagonal_mul_diagonal]; congr 1; funext a; split_ifs <;> simp) (hc τ) (by
      rw [hP, prFst, diagonal_transpose])
  let e : Fin g ≃ Fin r × X.Ψ := idx.trans (Equiv.prodComm _ _)
  have hdet : ((blockDiagonal N).submatrix e e).det = ∏ τ, (N τ).det := by
    rw [det_submatrix_equiv_self, det_blockDiagonal]
  have main := thR_of_perC X bas idx x x' ((blockDiagonal N).submatrix e e)
    (by rw [hdet]; exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun τ _ => (hN τ).1)) (fun u => by
      funext j
      have h1 : ((blockDiagonal N).submatrix e e *ᵥ fun j => perC X x u (idx j)) j =
          ∑ p : Fin r × X.Ψ, blockDiagonal N (e j) p * perC X x u p.swap := by
        rw [← e.sum_comp]
        rfl
      rw [h1, Fintype.sum_prod_type]
      refine (perC_block X x x' (idx j).1 (b _) (hb _) (hxb _) (hc _) u (idx j).2).trans ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single (idx j).1]
      · exact congrArg (· * _) (blockDiagonal_apply_eq N (idx j).2 c (idx j).1).symm
      · intro τ _ hτ
        have : blockDiagonal N (e j) (c, τ) = 0 := blockDiagonal_apply_ne N (idx j).2 c hτ.symm
        rw [this, zero_mul]
      · simp) φ v
  rw [main, hdet, Finset.prod_pow, ← Finset.prod_inv_distrib]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => by rw [(hN τ).2, inv_div]

end Classical

theorem det_block_conj {r : ℕ} (P m : Matrix (Fin r) (Fin r) ℂ) (hPP : P * P = P) (hP : Pᴴ = P)
    (hP' : P.map conj = P) (hc : m * P = P * m) (hm : mᴴ * m = 1) :
    (P * m.map conj + (1 - P)).det = (P * m + (1 - P)).det⁻¹ := by
  have h1 : (P * m + (1 - P))ᴴ * (P * m + (1 - P)) = 1 := by
    have a1 : mᴴ * (P * m) = P := by rw [← hc, ← Matrix.mul_assoc, hm, Matrix.one_mul]
    have a2 : ∀ y : Matrix (Fin r) (Fin r) ℂ, P * (P * y) = P * y := fun y => by rw [← Matrix.mul_assoc, hPP]
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hP,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, a1, a2, hPP]
    abel
  have h2 : P * m.map conj + (1 - P) = (starRingEnd ℂ).mapMatrix (P * m + (1 - P)) := by
    rw [map_add (f := _), map_mul, map_sub, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hP']
  have h3 := congrArg det h1
  rw [det_mul, det_conjTranspose, det_one] at h3
  rw [h2, ← RingHom.map_det]
  exact eq_inv_of_mul_eq_one_left h3

theorem blocks {r p : ℕ} (G B k : Matrix (Fin r) (Fin r) ℂ) (S : Matrix (Fin r) (Fin r) ℂ)
    (hS : S = (2 : ℂ) • prFst r p - 1) (hSS : S * S = 1) (hB : Bᴴ * G * B = S) (hk : kᴴ * G * k = G)
    (hc : k * (B * S * B⁻¹) = B * S * B⁻¹ * k) :
    ∃ m : Matrix (Fin r) (Fin r) ℂ, IsUnit (m.map conj).det ∧ k * B = B * m ∧
      m.map conj * prFst r p = prFst r p * m.map conj ∧
      ((1 - prFst r p) * m.map conj + prFst r p).det / (prFst r p * m.map conj + (1 - prFst r p)).det =
        detPos (B * S * B⁻¹) k * (detNeg (B * S * B⁻¹) k)⁻¹ := by
  have hu := GlobalTheory.Ker.ONBasis.isUnit_det hSS hB
  have hPP : prFst r p * prFst r p = prFst r p := by
    rw [prFst, diagonal_mul_diagonal]; congr 1; funext a; split_ifs <;> simp
  have hPc : (prFst r p).map conj = prFst r p := by
    ext a c
    simp only [prFst, map_apply, diagonal_apply]
    split_ifs <;> simp
  have hPH : (prFst r p)ᴴ = prFst r p := by
    rw [prFst, diagonal_conjTranspose]; congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp
  generalize prFst r p = P at *
  have e0 : B * S * B⁻¹ * B = B * S := by rw [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  generalize B * S * B⁻¹ = s at *
  obtain ⟨h1, h2, h3⟩ := block_of_inv P B k (-s) hu (by rw [Matrix.neg_mul, e0, hS])
    (by rw [Matrix.neg_mul, ← Matrix.mul_assoc, ← hc, Matrix.mul_assoc, e0, hS, Matrix.mul_assoc])
  have hkB : k * B = B * (B⁻¹ * (k * B)) := (mul_nonsing_inv_cancel_left _ _ hu).symm
  generalize B⁻¹ * (k * B) = m at *
  have hmS : m * S = S * m := by
    rw [hS, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h1, Matrix.mul_one, Matrix.one_mul]
  have hm1 : mᴴ * S * m = S := by
    calc mᴴ * S * m = (B * m)ᴴ * G * (B * m) := by
          rw [← hB, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Bᴴ * (kᴴ * G * k) * B := by rw [← hkB, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = S := by rw [hk, hB]
  have hm : mᴴ * m = 1 := by
    calc mᴴ * m = mᴴ * S * m * S := by
          rw [Matrix.mul_assoc, hmS, Matrix.mul_assoc, ← Matrix.mul_assoc S, hSS, Matrix.one_mul]
      _ = 1 := by rw [hm1, hSS]
  have d1 := det_block_conj P m hPP hPH hPc h1 hm
  have d2 := det_block_conj (1 - P) m
    (by rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPP]; abel)
    (by rw [conjTranspose_sub, conjTranspose_one, hPH])
    (by
      change (starRingEnd ℂ).mapMatrix (1 - P) = _
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hPc])
    (by rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]) hm
  rw [sub_sub_cancel] at d2
  refine ⟨m, ?_, hkB, ?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_det_of_left_inverse hm).map _
  · rw [← hPc, ← Matrix.map_mul, ← Matrix.map_mul, h1]
  · rw [d1, d2, ← h2, ← h3, detNeg, detPos, detPos]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul, hc, sub_neg_eq_add, ← sub_eq_add_neg]
    rw [div_eq_mul_inv, inv_inv, mul_comm]

theorem Th_mvB (D : D7) (S T : HSp D) (C : GlobalTheory.Ker.Ctx S T) (B : C.Bas) (hB : C.IsB B) (k : GA D T)
    (_hk : k ∈ GinfC T)
    (hc : ∀ τ, compAt C.θ τ (Formalism.L2.Theta.mt T k) * C.sB B τ = C.sB B τ * compAt C.θ τ (Formalism.L2.Theta.mt T k))
    (φ : TF S.rank C.g) (hφ : GlobalTheory.SW.IsSB φ) :
    C.Th (C.xB (C.mvB k B)) φ = vacChar C.θ T (C.sB B) S.rank (fun _ => 0) k • C.Th (C.xB B) φ := by
  have hdom : ∀ A, C.IsB A → C.xB A ∈ C.X.dom := fun A hA =>
    GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C hA)
  have z1 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hdom _ hB) φ hφ).1
  have z2 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hdom _ (GlobalTheory.Ker.ONBasis.isB_mvB C hB k)) φ hφ).1
  obtain ⟨-, l1, l2⟩ := GlobalTheory.ThetaSpace.theta_space_laws D S T C
  refine (l1 _ _ z2.1 ((l2 _ z1.1).1 _)).2 fun w hw => ?_
  choose m m1 m2 m3 m4 using fun τ => blocks (p := C.X.p0) (gramAt D T τ) (B τ)
    (compAt C.θ τ (Formalism.L2.Theta.mt T k)) (sgnM C.X) (sgnM_eq C.X) (GlobalTheory.Ker.ONBasis.sgnM_sq C.X) (hB τ)
    (GlobalTheory.Ker.ONBasis.compAt_unitary C τ k) (hc τ)
  rw [z2.2 w hw, Pi.smul_apply, z1.2 w hw, smul_eq_mul,
    thR_block C.X C.bas C.idx (C.xB B) (C.xB (C.mvB k B)) (fun σ => (m (C.m.e.symm σ)).map conj)
      (fun σ => m1 _) (fun σ => ?_) (fun σ => m3 _)]
  · congr 1
    rw [← C.m.e.prod_comp, vacChar]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Equiv.symm_apply_apply, m4, zero_add, zero_sub, _root_.zpow_neg, zpow_natCast, zpow_natCast, mul_pow, inv_pow]
    rfl
  · obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
    rw [GlobalTheory.Ker.ONBasis.mat_xB, GlobalTheory.Ker.ONBasis.mat_xB, Equiv.symm_apply_apply, ← Matrix.map_mul, ← m2]
    rfl

end GlobalTheory.FrameEquiv.CompactMove

end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocIntSpan

theorem isIntB_of_isIntB_conj : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (L : Type) [Field L] [NumberField L]
    (ι : L →ₐ[ℚ] C), Function.Injective ι → ∀ (κ : Type) (b : Module.Basis κ ℚ C) (κ' : Type)
    (bL : Module.Basis κ' ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ (X : (v.adicCompletion ℚ ⊗[ℚ] C)ˣ) (E : v.adicCompletion ℚ ⊗[ℚ] L),
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι E * ↑X⁻¹) →
        IsIntB v bL E := by
  intro C _ _ _ L _ _ ι hι κ b κ' bL
  obtain ⟨S₁, h₁⟩ := GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul C κ b
  obtain ⟨S₂, h₂⟩ := GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul L κ' bL
  obtain ⟨S₃, h₃⟩ := GlobalTheory.T.adicIntegralTensorBasis_of_trace_mem_eventually L κ' bL
  refine ⟨S₁ ∪ S₂ ∪ S₃, fun v hv X E hE => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := hv
  have hint := GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring v C κ b (h₁ v hv1).1 (h₁ v hv1).2 _ hE
  have hE' := isIntegral_of_isIntegral_conj X _ hint
  let F : v.adicCompletion ℚ ⊗[ℚ] L →ₐ[v.adicCompletion ℚ] v.adicCompletion ℚ ⊗[ℚ] C :=
    Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion ℚ) (v.adicCompletion ℚ)) ι
  have hF : ∀ x, F x = Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι x := fun x => rfl
  have hinj : Function.Injective (F.restrictScalars (v.adicCompletionIntegers ℚ)) := by
    intro x y hxy
    exact map_id_injective (v.adicCompletion ℚ) ι hι (by simpa [hF] using hxy)
  have hE'' : IsIntegral (v.adicCompletionIntegers ℚ) E :=
    (isIntegral_algHom_iff (F.restrictScalars (v.adicCompletionIntegers ℚ)) hinj).1 (by simpa [hF] using hE')
  refine h₃ v hv3 E fun i => mem_of_isIntegral v ?_
  have hb : IsIntegral (v.adicCompletionIntegers ℚ) ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i) :=
    GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring v L κ' bL (h₂ v hv2).1 (h₂ v hv2).2 _ (isIntB_tmul_basis v bL i)
  exact GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral _ _ _ _ (hE''.mul hb)

end GlobalTheory.LocIntSpan
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.fractional_ideal_integral_lattice : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ I : Set (v.adicCompletion ℚ ⊗[ℚ] L), 0 ∈ I →
      (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ, IsIntB v ℓ ρ → ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x, IsIntB v ℓ x → (D : v.adicCompletion ℚ ⊗[ℚ] L) * x ∈ I) ∧
        ∀ x ∈ I, IsIntB v ℓ ((D : v.adicCompletion ℚ ⊗[ℚ] L) * x)) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, ∀ x, x ∈ I ↔ ∃ ρ, IsIntB v ℓ ρ ∧ x = ↑m * ρ := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually) | (exact GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually) | (intros; apply GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.exists_frameCoords_basis_eigenLattice_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ' : E →+* ℂ) (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ' a)) → ∃ v : Fin (Dw.mult ρ') → Fin F.P₀.g → K, GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ' v ∧ LinearIndependent K v ∧ Submodule.span K (Set.range v) = Submodule.span K (F.eigLat B.t.act t : Set (Fin F.P₀.g → K)) := by
  first | exact @GlobalTheory.PtDeg.exists_frameCoord_basis | exact GlobalTheory.PtDeg.exists_frameCoord_basis | (intros; apply GlobalTheory.PtDeg.exists_frameCoord_basis <;> assumption)
end
