module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1811
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDescentDegreeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1751
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle053
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1826
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LandherrStandardDefiniteHermitianCmField
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle784
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem LKMid.Pair.term_one_eq_pointSum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.term Kf f 1 K' f' = pointSum (P.toAf x t hx) (P.toQr 1 1) (MonoidHom.id (Gr G 1)) Kf K' (P.toAf x t hx P.self) (inclG G 1 P.atP) f f' := by
  intro p _ G P Kf f K' f' hf hf' x t hx
  have hN : IsNrm G 1 P.atP (inclG G 1 P.atP) 1 := (GlobalTheory.nrm_exact p G).2 P.atP
  have hsig : sigG G 1 = MonoidHom.id (Gr G 1) := by
    ext1 g
    exact (GlobalTheory.LKMid.SigIter.main p G 1 Nat.one_pos).1 g
  rw [GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G P Kf f 1 K' f' Nat.one_pos hf hf' x t hx (inclG G 1 P.atP) 1 hN]
  unfold Pair.termAt
  rw [hsig]

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.descent_equalizer_degree_zero : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'], Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) → ∀ (j : ℤ) (b : Ht q (sp A') 0 j), pull _ (spMap (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b = pull _ (spMap (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b → ∃ a : Ht q (sp A) 0 j, pull _ (spMap (algebraMap A A')) _ 0 a = b := by
  first | (exact @GlobalTheory.EtC.DescZero.desc_zero) | (exact GlobalTheory.EtC.DescZero.desc_zero) | (intros; apply GlobalTheory.EtC.DescZero.desc_zero  <;> assumption)
end

section

namespace GlobalTheory.PsCo.Pc3

theorem stTrAd : GlobalTheory.PsCo.Pc1.StTrAd :=
  stTrAd_of
    GlobalTheory.ShapeSmoothFinite.stShape
    GlobalTheory.PsCo.Pc1.B.cutoffPolynomial_conjugation_deriv_mem_shapeSpan
    uFin rangeShape
    GlobalTheory.OpTrace.hasTrace_sum_inner_of_range_le
    GlobalTheory.Pc3.conjDeriv

end GlobalTheory.PsCo.Pc3
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.LocFinU

theorem bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∃ Ω : Set (UL n w), IsCompact Ω ∧ (cptPart (twCent (MonoidHom.id (UL n w)) y) : Set (UL n w)) ⊆ Ω := by
  intro E _ _ _ hE n w y hy
  obtain ⟨Ω, hΩ, hsub⟩ := GlobalTheory.T.exists_compact_set_twisted_centralizer_elliptic E hE n w y hy
  refine ⟨Ω, hΩ, fun t ht => ?_⟩
  have hc : ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
    intro a ha b hb
    have ha' : a.1.val * y.1.val =
        y.1.val * a.1.val :=
      by
        have h0 : a * y = y * a := ha
        have := congrArg (fun g : UL n w => g.1.val) h0
        simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have hb' : b.1.val * y.1.val =
        y.1.val * b.1.val :=
      by
        have h0 : b * y = y * b := hb
        have := congrArg (fun g : UL n w => g.1.val) h0
        simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have := GlobalTheory.T.commute_of_commute_of_charpoly_separable' _ n _ _ _ hy ha' hb'
    exact Subtype.ext (Units.ext this)
  have := cptPart_subset_of_comm _ hc ht
  exact hsub t this.1 this.2

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

theorem conj_map_eq {G : Type} [Group G] (x : G) (K : Subgroup G) :
    (K.map (MulAut.conj x).toMonoidHom : Set G) = (fun k => x * k * x⁻¹) '' (K : Set G) := by
  ext g
  simp [Subgroup.coe_map, MulAut.conj_apply]

theorem locFin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → (∀ x : UL n w, twCent (MonoidHom.id _) y ⊓ (KL n w).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id _) y) ∧ (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id _) y)) ≠ 0) ∧ ∀ C : Set (UL n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) y : Set (UL n w)) (K' : Set (UL n w)) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite := by
  intro E _ _ _ hE n w y hy K' hK'
  obtain ⟨hK'o, -, -⟩ := hK'
  obtain ⟨Ω, hΩ, hsub⟩ := bound E hE n w y hy
  refine ⟨fun x => ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨htT, htK⟩ := Subgroup.mem_inf.1 ht
    apply Subgroup.subset_closure
    refine ⟨htT, ?_⟩
    have hc : IsCompact ((KL n w).map (MulAut.conj x).toMonoidHom : Set (UL n w)) := by
      rw [conj_map_eq]
      exact (isCompact_KL n w).image ((continuous_const.mul continuous_id).mul continuous_const)
    refine hc.of_isClosed_subset isClosed_closure ?_
    exact closure_minimal (Subgroup.zpowers_le.2 htK) hc.isClosed
  · have hP : cptPart (twCent (MonoidHom.id _) y) ≤ twCent (MonoidHom.id _) y :=
      (Subgroup.closure_le _).2 (fun t ht => ht.1)
    have hU : IsOpen ((K'.map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (UL n w)) := by
      rw [conj_map_eq]
      exact ((Homeomorph.mulLeft x).trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hK'o
    have h := relIndex_ne_zero_of_subset_cpt _ _ hU Ω hΩ hsub
    have e : (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf
        (cptPart (twCent (MonoidHom.id _) y)) =
        (K'.map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart (twCent (MonoidHom.id _) y)) := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hP z.2, h⟩⟩
    unfold Subgroup.relIndex at h ⊢
    rwa [e]
  · intro C hC
    obtain ⟨Ω', hΩ', horb⟩ := GlobalTheory.T.regular_orbit_conj_compact_mod_centralizer_unitary E hE n w y hy C hC
    obtain ⟨s, hs⟩ := hΩ'.elim_finite_subcover (fun g : Ω' => (g : UL n w) • (K' : Set (UL n w)))
      (fun g => hK'o.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, K'.one_mem, mul_one x⟩⟩)
    refine (s.finite_toSet.image
      (fun g : Ω' => DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) y) K' (g : UL n w))).subset ?_
    intro q hq
    obtain ⟨t, ht, ω, hω, heq⟩ := horb _ hq
    have := hs hω
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, k, hk, hik⟩ := this
    refine ⟨i, hi, ?_⟩
    conv_rhs => rw [← Quotient.out_eq q]
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨t, ht, k, hk, ?_⟩
    rw [heq, ← hik]
    simp only [smul_eq_mul, mul_assoc]

end GlobalTheory.LocFinU
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_GL_charpoly_eq_of_mem_Ell : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∀ P ∈ Ell E n, ∃ a : GL (Fin n) E, a.val.charpoly = P := by
  first | exact @GlobalTheory.CompanionEll.exists_GL_charpoly_eq | exact GlobalTheory.CompanionEll.exists_GL_charpoly_eq | (intros; apply GlobalTheory.CompanionEll.exists_GL_charpoly_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.localTwist_continuous_involution_integral_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ (∀ g, thL n w (thL n w g) = g) ∧ (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), thL n w k ∈ GlobalTheory.LFun.KGL w (n := n)) ∧ (∀ g y, nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g) ∧ IsOpen (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∧ IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∧ IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ (∀ δ : GL (Fin n) E, (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly) ∧ ∀ x ∈ locU n w, cLoc w x ∈ UL n w := by
  first | exact @GlobalTheory.BCT.ThBasic.twist_basic | exact GlobalTheory.BCT.ThBasic.twist_basic | (intros; apply GlobalTheory.BCT.ThBasic.twist_basic <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finprod_nonsplit_sign_totallyPositive_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ d : E, d ≠ 0 → (∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ d = r) → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) d)) = 1 := by
  first | exact @GlobalTheory.UnitaryClasses.signProd_totPos | exact GlobalTheory.UnitaryClasses.signProd_totPos | (intros; apply GlobalTheory.UnitaryClasses.signProd_totPos <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.stableTwistedOrbitalIntegral_integralNormCongruence_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (a b k : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → stTw2 a b w Q₁ Q₂ (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) = c * (stTw a w Q₁ (fun y : GLw a w => if y ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) * stTw b w Q₂ (fun y : GLw b w => if y ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  first | exact @GlobalTheory.BCT.StTwLevel.stTw2_lev | exact GlobalTheory.BCT.StTwLevel.stTw2_lev | (intros; apply GlobalTheory.BCT.StTwLevel.stTw2_lev <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem finiteDimensional_fixed_openSubgroup_GLw : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    ∀ (n : ℕ) (w : Pl E) (σ : SmIrr (GLw n w)) (U : Subgroup (GLw n w)), IsOpen (U : Set (GLw n w)) →
      FiniteDimensional ℂ (fixed σ.ρ U) := by
  intro E _ _ _ n w σ U hU
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  have hadm : IsAdmissible σ.ρ :=
    GlobalTheory.FourClauses.irreducibleAdmissibleGL (w.adicCompletion E) n σ.V σ.ρ σ.smooth σ.irred
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hK : FiniteDimensional ℂ (fixed σ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n))) :=
    hadm.2 _ (hU.inter ho) (hc.inter_left (U.isClosed_of_isOpen hU))
  have hle : fixed σ.ρ U ≤ fixed σ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n)) := fun v hv h => hv ⟨h.1, h.2.1⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.BCT
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.landherr_standard_definite_hermitian_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ w : Pl E, ¬ IsSplitAt w → ∃ g : Matrix (Fin n) (Fin n) (w.adicCompletion E), H.map (algebraMap E (w.adicCompletion E)) = cT (cj w) g * g) → ∃ h : GL (Fin n) E, H = cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * h.val := by
  first | exact @GlobalTheory.LandherrStd.main | exact GlobalTheory.LandherrStd.main | (intros; apply GlobalTheory.LandherrStd.main <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn coordIn_div)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.TransportProof
theorem exists_sq_eq_neg : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := GlobalTheory.T.quadraticField_exists_sqrt_neg_discr

theorem nrm_eq_modF : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h : IsInvIdealOf t 𝔞), nrm 𝔞 = modF t := GlobalTheory.T.fractionalIdealNorm_eq_finiteIdeleModule

theorem modF_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := GlobalTheory.T.finiteIdele_module_exists_rat

theorem modF_upIdele : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ), modF (upIdele K E t) = modF t ^ Module.finrank K E := GlobalTheory.T.modF_finiteIdeleUpToExtension

theorem card_eq_finrank : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2), Fintype.card I = Module.finrank K E := GlobalTheory.T.isCMTypeOfEmbeddings_card_eq_finrank

theorem norm_conj_finPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E) (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ), ‖σ (finPart χ y : ℂ)‖ = 1 := GlobalTheory.T.norm_galois_conj_heckeCharacter_finitePart_eq_one

theorem algebraic_coordIn_toric : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := GlobalTheory.T.toricSum_coordinate_isAlgebraic

theorem conj_coordIn_toric : ∀ (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ κ' : I → ℕ) (hκ' : IsConjWt φ g κ κ') (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ χ' : HChar E) (T T' : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T) (hV' : IsConjSum φ s κ' 𝔣 Q g χ χ' T'), g (coordIn E d s κ Ω₀ T) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * T') := GlobalTheory.T.conj_toricPeriodCoordinate_sum_over_classes

theorem equidistributed_of_j : ∀ (hH : GlobalTheory.Published.HilbertClassFieldJ) {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair) (hΛ : IsLatOf φK 1 ΛK) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔞 : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ Λ : PeriodPair, IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) Λ ∧ jLat Λ = σ (jLat ΛK)), Equidistributed φK (jLat ΛK) 𝔞 := GlobalTheory.T.equidistributed_idealClasses_of_hilbertClassFieldJ

theorem isTotallyComplex_of_discr_neg {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    (h : discr K < 0) : IsTotallyComplex K := by
  have hs := sign_discr K
  rw [Int.sign_eq_neg_one_of_neg h] at hs
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h2] at hr
  have hc : InfinitePlace.nrComplexPlaces K = 1 := by
    rcases Nat.even_or_odd (InfinitePlace.nrComplexPlaces K) with he | ho
    · rw [he.neg_one_pow] at hs; norm_num at hs
    · obtain ⟨k, hk⟩ := ho; omega
  exact nrRealPlaces_eq_zero_iff.1 (by omega)

theorem disc_j_of_torsTransport {K : Type} [Field K] [NumberField K] {ι : K →+* ℂ} {g : ℂ ≃+* ℂ} {t : (Af K)ˣ}
    {Λ₀ Λ₁ : PeriodPair} {Ω₀ Ω₁ : ℂ} (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) :
    Ω₁ ^ 12 = latDisc Λ₁ ∧ jLat Λ₁ = g (jLat Λ₀) := by
  obtain ⟨h0, h1, -, -, -, ha, hb, -⟩ := hT
  have e0 : (Λ₀.g₂ / Ω₀ ^ 4) ^ 3 - 27 * (Λ₀.g₃ / Ω₀ ^ 6) ^ 2 = 1 := by
    have : latDisc Λ₀ / Ω₀ ^ 12 = 1 := by rw [← hΩ, div_self (pow_ne_zero _ h0)]
    rw [← this, latDisc]; field_simp
  have e1 : (Λ₁.g₂ / Ω₁ ^ 4) ^ 3 - 27 * (Λ₁.g₃ / Ω₁ ^ 6) ^ 2 = 1 := by
    rw [← ha, ← hb]
    have := congrArg g e0
    simpa [map_sub, map_pow, map_mul, map_ofNat] using this
  have hD : Ω₁ ^ 12 = latDisc Λ₁ := by
    rw [latDisc]; field_simp at e1; linear_combination -e1
  refine ⟨hD, ?_⟩
  have j0 : jLat Λ₀ = 1728 * (Λ₀.g₂ / Ω₀ ^ 4) ^ 3 := by
    rw [jLat, ← hΩ]; field_simp
  have j1 : jLat Λ₁ = 1728 * (Λ₁.g₂ / Ω₁ ^ 4) ^ 3 := by
    rw [jLat, ← hD]; field_simp
  rw [j0, j1, map_mul, map_pow, ha, map_ofNat]

theorem condQ_ne_bot {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣)
    (Q : Finset (HeightOneSpectrum (OF E))) : condQ 𝔣 Q ≠ ⊥ := by
  unfold condQ
  rw [← Ideal.zero_eq_bot]
  refine mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)

theorem norm_lamF_conj_up {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E]
    [Algebra K E] {I : Type} [Fintype I] (h2 : Module.finrank ℚ K = 2) (φ : I → E →+* ℂ) (hE : UnramFin E)
    (hφ : IsCMType φ) (s : ℕ) (κ κ' : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣)
    (Q : Finset (HeightOneSpectrum (OF E))) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (χ χ' : HChar E) (hχ : IsValChar φ s κ 𝔣 Q χ)
    (σ : ℂ ≃+* ℂ) (hc : IsConjChar φ s κ' σ χ χ') (t : (Af K)ˣ) :
    ‖lamF s χ' (upIdele K E t)‖ = modF t ^ (s * Fintype.card I) := by
  have hu := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hE h𝔣 hQ hχ
  have h1 := norm_conj_finPart φ hφ s κ (condQ 𝔣 Q) (condQ_ne_bot h𝔣 Q) χ hχ.2.2.1 hu σ (upIdele K E t)
  obtain ⟨q, hq⟩ := modF_rat (upIdele K E t)
  have hpos := GlobalTheory.CMVal.IdeleModule.modF_pos (upIdele K E t)
  rw [hc.1, lamF, map_mul, norm_mul, h1, one_mul]
  have e : (((modF (upIdele K E t)) ^ s : ℝ) : ℂ) = ((q ^ s : ℚ) : ℂ) := by rw [hq]; push_cast; rfl
  rw [e, map_ratCast, ← e]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hpos _), modF_upIdele, ← card_eq_finrank φ hφ h2,
    ← pow_mul, mul_comm]

theorem beta_eq_coordIn_pow (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ)
    (Ω T : ℂ) (Λ : PeriodPair) (h : Ω ^ 12 = latDisc Λ) : beta E d s κ Λ T = coordIn E d s κ Ω T ^ 12 := by
  rw [beta_eq, coordIn, div_pow, ← h, ← pow_mul, ← pow_mul, mul_comm 12]

theorem transportFor_of (hA : LatAlg) (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (hd : 0 < d)
    (δ : K) (hδ : δ ^ 2 = -(d : K)) (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair)
    (hΛ : IsLatOf φK 1 ΛK) (Ω₀ : ℂ) (hΩ₀ : Ω₀ ^ 12 = latDisc ΛK) (hΩ₀0 : Ω₀ ≠ 0)
    (t : (ℂ ≃+* ℂ) → (Af K)ˣ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : (ℂ ≃+* ℂ) → PeriodPair)
    (Ω : (ℂ ≃+* ℂ) → ℂ)
    (hT : ∀ σ, Fixes φK σ →
      TorsTransport φK σ (t σ) ΛK (Λ σ) Ω₀ (Ω σ) ∧ IsInvIdealOf (t σ) (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K))
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (hE : UnramFin E)
    (I : Type) [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = φK)
    (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (hs : 1 ≤ s) (h𝔣 : IsBaseCond 𝔣) :
    TransportFor d φK ΛK t 𝔞 Λ φ s κ 𝔣 := by
  have hC0 : (C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (cmValueConst_pos E hd (by omega) κ).ne'
  have conj : ∀ σ, Fixes φK σ → ∀ κ', IsConjWt φ σ κ κ' → ∀ Q χ T χ' T', IsValSum φ s κ 𝔣 Q χ T →
      IsConjSum φ s κ' 𝔣 Q σ χ χ' T' →
      σ (coordIn E d s κ Ω₀ T) = coordIn E d s κ (Ω σ) ((((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^
        (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') := by
    intro σ hσ κ' hκ' Q χ T χ' T' hV hV'
    rw [nrm_eq_modF _ _ (hT σ hσ).2]
    exact conj_coordIn_toric hC d δ φK h2 hd hδ σ (t σ) ΛK (Λ σ) Ω₀ (Ω σ) hΩ₀ (hT σ hσ).1 φ hE hφ hφK s hs
      κ κ' hκ' 𝔣 h𝔣 Q χ χ' T T' hV hV'
  refine ⟨fun Q χ T hV => ⟨?_, fun σ hσ κ' hκ' χ' T' hV' => ?_⟩,
    fun Q₁ Q₂ χ₁ χ₂ T₁ T₂ hV₁ hV₂ hT₂ => ⟨?_, fun σ hσ κ' hκ' χ₁' χ₂' T₁' T₂' hV₁' hV₂' => ?_⟩⟩
  · rw [beta_eq_coordIn_pow E d s κ Ω₀ T ΛK hΩ₀]
    exact (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q χ T hV).pow 12
  · have hD := (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).1
    set N := nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) with hN
    have hN0 : N ≠ 0 := nrm_ne_zero _
    have hNpos : 0 < N := lt_of_le_of_ne (by rw [hN, nrm]; exact_mod_cast FractionalIdeal.absNorm_nonneg _) hN0.symm
    have e : σ (beta E d s κ ΛK T) = beta E d s κ (Λ σ)
        ((((N : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') := by
      rw [beta_eq_coordIn_pow E d s κ Ω₀ T ΛK hΩ₀, map_pow, conj σ hσ κ' hκ' Q χ T χ' T' hV hV',
        beta_eq_coordIn_pow E d s κ (Ω σ) _ (Λ σ) hD]
    have hl := norm_lamF_conj_up h2 φ hE hφ s κ κ' 𝔣 h𝔣 Q hV.1 χ χ' hV.2.1 σ hV'.1 (t σ)
    rw [← nrm_eq_modF _ _ (hT σ hσ).2, ← hN] at hl
    refine ⟨by rw [e, beta_eq]; ring, ?_⟩
    rw [e, beta_eq, norm_div, norm_pow, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, hl, norm_pow, norm_pow,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hNpos,
      abs_of_pos (cmValueConst_pos E hd (by omega) κ)]
    have hDn : ‖latDisc (Λ σ)‖ ≠ 0 := norm_ne_zero_iff.2 (latDisc_ne_zero _)
    field_simp
    ring
  · rw [← coordIn_div E hd hs κ hΩ₀0 T₁ T₂, div_eq_mul_inv]
    exact (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q₁ χ₁ T₁ hV₁).mul
      (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q₂ χ₂ T₂ hV₂).inv
  · have hΩσ : Ω σ ≠ 0 := (hT σ hσ).1.2.1
    set m : ℂ := (((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (∑ i, κ i)) with hm
    have hm0 : m ≠ 0 := pow_ne_zero _ (by exact_mod_cast nrm_ne_zero _)
    have c1 := conj σ hσ κ' hκ' Q₁ χ₁ T₁ χ₁' T₁' hV₁ hV₁'
    have c2 := conj σ hσ κ' hκ' Q₂ χ₂ T₂ χ₂' T₂' hV₂ hV₂'
    have hc2 : coordIn E d s κ Ω₀ T₂ ≠ 0 := by
      rw [coordIn]; exact div_ne_zero (mul_ne_zero hC0 hT₂) (pow_ne_zero _ hΩ₀0)
    have hT2' : T₂' ≠ 0 := by
      rintro rfl
      have := (map_ne_zero σ).2 hc2
      rw [c2, mul_zero, coordIn, mul_zero, zero_div] at this
      exact this rfl
    refine ⟨hT2', ?_⟩
    rw [← coordIn_div E hd hs κ hΩ₀0 T₁ T₂, map_div₀, c1, c2, coordIn_div E hd hs κ hΩσ, mul_assoc, mul_assoc,
      mul_div_mul_left _ _ (inv_ne_zero hm0)]

theorem transport_of (hH : GlobalTheory.Published.HilbertClassFieldJ) (hA : LatAlg) (hC : LatConj) : Transport := by
  intro K _ _ d hd h2 hdisc φK ΛK hΛ
  have hTC : IsTotallyComplex K := isTotallyComplex_of_discr_neg h2 (by rw [hdisc]; omega)
  obtain ⟨δ, hδ⟩ := exists_sq_eq_neg K d h2 hdisc
  obtain ⟨Ω₀, hΩ₀⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc ΛK) (by norm_num : 0 < 12)
  have hΩ₀0 : Ω₀ ≠ 0 := by rintro rfl; exact latDisc_ne_zero ΛK (by rw [← hΩ₀]; norm_num)
  have key : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ (t : (Af K)ˣ) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : PeriodPair) (Ω : ℂ),
      TorsTransport φK σ t ΛK Λ Ω₀ Ω ∧ IsInvIdealOf t (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ∧
        IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λ := by
    intro σ hσ
    letI : Algebra K ℂ := φK.toAlgebra
    obtain ⟨X, hX, ξ, hξ, hTr⟩ := GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport h2 φK ΛK Ω₀ hΛ hΩ₀0
    haveI := hX
    let σK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := σ) hσ
    obtain ⟨t, ht⟩ := GlobalTheory.EllipticCM.exists_transports h2 σK one_ne_zero hξ
    obtain ⟨Λ₁, Ω₁, h1⟩ := hTr σK t ht
    obtain ⟨𝔞, h𝔞t, h𝔞Λ⟩ := h1.2.2.2.2.1
    have h𝔞0 : 𝔞 ≠ 0 := by
      rintro rfl
      have hm : Λ₁.ω₁ ∈ (Λ₁.lattice : Set ℂ) := PeriodPair.ω₁_mem_lattice Λ₁
      rw [h𝔞Λ] at hm
      obtain ⟨x, hx, hx'⟩ := hm
      have hx0 : x = 0 := by simpa using hx
      rw [hx0, map_zero] at hx'
      exact (by simpa using Λ₁.indep.ne_zero 0 : Λ₁.ω₁ ≠ 0) hx'.symm
    exact ⟨t, Units.mk0 𝔞 h𝔞0, Λ₁, Ω₁, h1, h𝔞t, h𝔞Λ⟩
  haveI : Nonempty PeriodPair := ⟨ΛK⟩
  choose! t 𝔞 Λ Ω hT using key
  refine ⟨t, 𝔞, Λ, fun σ hσ => ⟨(hT σ hσ).2.1, (hT σ hσ).2.2, (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).2⟩,
    equidistributed_of_j hH h2 φK ΛK hΛ 𝔞
      (fun σ hσ => ⟨Λ σ, (hT σ hσ).2.2, (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).2⟩), ?_⟩
  intro E _ _ _ _ _ hE I _ φ hcard hφ hφK s κ 𝔣 hs hκ h𝔣
  exact transportFor_of hA hC d (by omega) δ hδ h2 φK ΛK hΛ Ω₀ hΩ₀ hΩ₀0 t 𝔞 Λ Ω
    (fun σ hσ => ⟨(hT σ hσ).1, (hT σ hσ).2.1⟩) E hE I φ hφ hφK s κ 𝔣 hs h𝔣

end GlobalTheory.TransportProof
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.isLabel_thetaLiftSpace_iff_dual : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, Core R F → ∀ i P d, Good R A.μ0 P → (IsLab (Wc D i) P d ↔ IsLab (Yc D 0) P (dualLab d)) ∧ (IsLab (Wc D i) P d ↔ IsLab (Yc D 0) P d) := by
  first | exact @GlobalTheory.LabEq.isLab_W_iff | exact GlobalTheory.LabEq.isLab_W_iff | (intros; apply GlobalTheory.LabEq.isLab_W_iff <;> assumption)
end
