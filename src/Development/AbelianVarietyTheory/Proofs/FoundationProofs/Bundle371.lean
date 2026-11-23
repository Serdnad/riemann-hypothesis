module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle327
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSemisimpleGeneralisedEigenNewformGamma1Gamm
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameClassLimitOfNormCompatibleShapiroSystem
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle365
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle213
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCocycleIntegralAfterScaling
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefficientCongruenceOfTwistedValues
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

@[expose] public section

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.SplitCharacter

open GlobalTheory.NormSum.VacMove

theorem mem_of_local {G : Type} [AddCommGroup G] (T : AddSubgroup G) (x : G)
    (h : ∀ q : ℕ, q.Prime → ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ T) : x ∈ T := by
  by_contra hx
  have h1 : addOrderOf (QuotientAddGroup.mk x : G ⧸ T) ≠ 1 := by
    intro h1
    rw [AddMonoid.addOrderOf_eq_one_iff, QuotientAddGroup.eq_zero_iff] at h1
    exact hx h1
  obtain ⟨q, hq, hd⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨m, hm, hT⟩ := h q hq
  have : addOrderOf (QuotientAddGroup.mk x : G ⧸ T) ∣ m := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hT
  exact (Nat.Prime.coprime_iff_not_dvd hq).1 hm.symm (hd.trans this)

variable {D : D7}

def vanish (D : D7) (q : ℕ) (hq : q.Prime) : Ideal (AE D) where
  carrier := {x | ZeroAt D q x}
  zero_mem' := fun k => ⟨1, one_pos, by simp, 0, zero_mem _, by simp⟩
  add_mem' := by
    intro x y hx hy k
    obtain ⟨m, hm, hc, s, hs, h⟩ := hx k
    obtain ⟨m', hm', hc', s', hs', h'⟩ := hy k
    refine ⟨m * m', Nat.mul_pos hm hm', Nat.Coprime.mul_left hc hc', m' * s + m * s',
      add_mem (mul_mem (natCast_mem _ _) hs) (mul_mem (natCast_mem _ _) hs'), ?_⟩
    push_cast
    linear_combination (m' : AE D) * h + (m : AE D) * h'
  smul_mem' := fun c x hx => by
    have := zeroAt_mul D hq hx c
    rwa [mul_comm] at this

theorem eq_zero_of_zeroAt (x : AE D) (h : ∀ q : ℕ, q.Prime → ZeroAt D q x) : x = 0 := by
  apply _root_.GlobalTheory.VacuumScalar.eq_zero_of_zeroAt <;> assumption

theorem zeroAt_det {N q : ℕ} (hq : q.Prime) {g : GL (Fin N) (AE D)} (h : TrivAt D q g) :
    ZeroAt D q (((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) - 1) := by
  have h1 : (Ideal.Quotient.mk (vanish D q hq)).mapMatrix (g : Matrix (Fin N) (Fin N) (AE D)) =
      (Ideal.Quotient.mk (vanish D q hq)).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 (h i j)
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at h2
  exact Ideal.Quotient.eq.1 h2

def cutHom {R : Type} [CommRing R] (ε : R) (h : ε * ε = ε) : R →* R where
  toFun u := (1 - ε) + ε * u
  map_one' := by ring
  map_mul' u v := by linear_combination (-(1 - u - v + u * v)) * h

theorem exists_split_character : ∀ (D : D7) (N₀ : ℕ) (χ : HeckeU D N₀) (N : ℕ), ∃ c : GA D N →* ℂˣ, (∀ k : GA D N, SuppInert D (k : GL (Fin N) (AE D)) → c k = 1) ∧ ∀ (g : GA D N) (x : (AE D)ˣ), (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) → x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x → c g = χ.f x := by
  intro D N₀ χ N
  obtain ⟨ε, -, h1, h2, h3⟩ := exists_half_idem D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  refine ⟨χ.f.comp ((Units.map (cutHom ε h1)).comp
    ((Matrix.GeneralLinearGroup.det (n := Fin N) (R := AE D)).comp (GA D N).subtype)), fun k hk => ?_, fun g x hx hg => ?_⟩
  · have h0 : ε * (((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1) = 0 := by
      refine eq_zero_of_zeroAt _ fun q hq => ?_
      by_cases hi : InertQ D q
      · have := zeroAt_mul D hq ((h3 q hq).1 hi)
          (ε * (((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1))
        convert this using 1
        linear_combination (-(((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1)) * (h1 + h2)
      · rw [mul_comm]
        exact zeroAt_mul D hq (zeroAt_det hq (hk q hq hi)) ε
    have h4 : Units.map (cutHom ε h1) (Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D))) = 1 := by
      ext
      change (1 - ε) + ε * ((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) = 1
      linear_combination h0
    change χ.f (Units.map (cutHom ε h1) (Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)))) = 1
    rw [h4, map_one]
  · have h0 : (1 - (ε + sgA D ε)) * ((x : AE D) - 1) = 0 := by
      refine eq_zero_of_zeroAt _ fun q hq => ?_
      by_cases hi : InertQ D q
      · rw [mul_comm]
        exact zeroAt_mul D hq (hx q hq hi) _
      · exact zeroAt_mul D hq ((h3 q hq).2 hi) _
    have hs : sgU D (Units.map (cutHom (sgA D ε) h1') x) = Units.map (cutHom ε h1) (sgU D x) := by
      ext
      change sgA D ((1 - sgA D ε) + sgA D ε * x) = (1 - ε) + ε * sgA D x
      rw [map_add (f := _), map_mul, map_sub, map_one, sgA_sgA]
    have h5 : Units.map (cutHom ε h1) x * Units.map (cutHom (sgA D ε) h1') x = x := by
      ext
      change ((1 - ε) + ε * x) * ((1 - sgA D ε) + sgA D ε * x) = (x : AE D)
      linear_combination (1 - (x : AE D)) ^ 2 * h2 - h0
    have h6 : Units.map (cutHom ε h1) (Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D))) *
        (Units.map (cutHom (sgA D ε) h1') x * sgU D (Units.map (cutHom (sgA D ε) h1') x)) = x := by
      rw [hs, mul_comm (Units.map (cutHom (sgA D ε) h1') x), ← mul_assoc, ← map_mul, ← hg, h5]
    change χ.f (Units.map (cutHom ε h1) (Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)))) = χ.f x
    conv_rhs => rw [← h6]
    rw [map_mul, χ.norm, mul_one]

end GlobalTheory.SplitCharacter
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open scoped TensorProduct Matrix ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepsObj

open GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting hiding levJ

section Space

variable {D : D7}

theorem gramAt_posDef {V : HSp D} (hp : V.IsPosDef) (hs : V.SigOK) (τ : D.what₂.Tau) : (gramAt D V τ).PosDef := by
  have := hs (tauE D τ)
  rw [hp] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem exists_compact_of_fin (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) {C : Set (Af D.host.F ⊗[D.host.F] D.host.E)}
    (hC : IsCompact C) : ∃ K : Set (GA D V), IsCompact K ∧ ∀ k : GA D V, (∀ i j, (finHom V k).1 i j ∈ C) → k ∈ K := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  choose R hR using fun τ => GlobalTheory.DefiniteQuotient.exists_bound_unitary (hV τ)
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) C' hC'
  refine ⟨K, hK, fun k hk => hKe k fun i j => hCe' _ (hk i j) fun τ => ?_⟩
  have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
    ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
  have hu : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V k) * V.gram.map (incA D) * Formalism.L2.Theta.mt V k = V.gram.map (incA D) := k.2
  have e : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V k)).map ((θ τ).comp (infPart D)) =
      ((Formalism.L2.Theta.mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
    ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
  have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
  simp only [Matrix.map_mul, e, hJ] at this
  exact ((hR τ _ this i j).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))

theorem finite_stab (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (Bridge.Gf V))
    {C : Set (Af D.host.F ⊗[D.host.F] D.host.E)} (hC : IsCompact C) (hJ : ∀ k ∈ J, ∀ i j, k.1.1 i j ∈ C) (g : Bridge.Gf V) :
    Finite (Bridge.stab (Bridge.ratF V) J g) := by
  obtain ⟨-, -, h2, -, hg, hd, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨K, hK, hKe⟩ := exists_compact_of_fin V hV hC
  obtain ⟨x, rfl⟩ := (finHom V).rangeRestrict_surjective g
  have hK' : IsCompact ((fun k => x * k * x⁻¹) '' K) := hK.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hcl : IsClosed (GQ V : Set (GA D V)) := Subgroup.isClosed_of_discrete
  have hfin : ((Subtype.val : GQ V → GA D V) ⁻¹' ((fun k => x * k * x⁻¹) '' K)).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK').finite_of_discrete
  refine Set.Finite.subset hfin fun γ hγ => ⟨x⁻¹ * γ.1 * x, hKe _ ?_, by group⟩
  have h := hJ _ ((Bridge.mem_stab _).1 hγ)
  rw [map_mul, map_mul, map_inv]
  exact h

theorem exists_cover_of_compact {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G)
    (π : G →* H) (hπ : Function.Surjective π) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G)) {C : Set G} (hC : IsCompact C)
    (hCe : ∀ h : G, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) :
    ∃ (m : ℕ) (c : Fin m → H), ∀ g, ∃ (a : Fin m) (γ : Γ) (k : J), g = π.comp Γ.subtype γ * c a * k := by
  obtain ⟨S, -, hS⟩ := hC.elim_nhds_subcover (fun x => {y | π (x⁻¹ * y) ∈ J}) fun x _ =>
    (ho.preimage (continuous_const_mul x⁻¹)).mem_nhds (by simp)
  refine ⟨_, fun a => π (S.equivFin.symm a).1, fun g => ?_⟩
  obtain ⟨x, rfl⟩ := hπ g
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hCe x
  obtain ⟨s, hs, hcs⟩ := Set.mem_iUnion₂.1 (hS hc)
  exact ⟨S.equivFin ⟨s, hs⟩, ⟨γ, hγ⟩, ⟨_, hcs⟩, by simp [mul_assoc]⟩

theorem exists_cover (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (Bridge.Gf V)) (ho : IsOpenLev V J) :
    ∃ (m : ℕ) (c : Fin m → Bridge.Gf V), ∀ g, ∃ (a : Fin m) (γ : GQ V) (k : J), g = Bridge.ratF V γ * c a * k :=
  have := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  (GlobalTheory.DefiniteQuotient.exists_compact V hV).elim fun _ h =>
    exists_cover_of_compact (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective J ho h.1 h.2

end Space

section Levels

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.DIV

variable {D : D7} {T : Type} (L : LevCh D T) (i : Fin D.R.m) (t : T)

theorem isPosDef_of_vStd (hV : VStd D i) : (Vc D i).IsPosDef := fun τ => by
  have h := factVSig _ _ D.sp ((i : ℕ) + 1) (by omega) (by omega) τ
  rw [GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hV, if_neg Bool.false_ne_true] at h
  rw [D.sp.V_rank _ (by omega) i.2]
  exact h

end Levels


section Record

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.DIV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (K' : Type) [Field K']

end Record

end GlobalTheory.RepsObj

end
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.hecke_semisimple_generalised_eigen_newform_gamma1Gamma0 : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) (hN : g.M ∣ N), 5 ≤ N → l.Prime → ¬ l ∣ N → Odd k → 3 ≤ k →
  ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 →
  α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) →
  ∀ (σT : ℕ → SL(2, ℤ)) (σD : (ZMod N)ˣ → SL(2, ℤ)),
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) (σT q)) →
    (∀ d : (ZMod N)ˣ, IsDiam N l (d : ZMod N) (σD d)) →
  ∀ z ∈ Z1 (Lev N l) (k - 2), ∀ n : ℕ,
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l →
      ((TqZ (Lev N l) (k - 2) q (σT q) - g.a q • 1) ^ n) z ∈ B1 (Lev N l) (k - 2)) →
    ((UlZ (Lev N l) (k - 2) l - α • 1) ^ n) z ∈ B1 (Lev N l) (k - 2) →
    (∀ d : (ZMod N)ˣ, ((DdZ (Lev N l) (k - 2) (σD d) - g.χ (ZMod.castHom hN (ZMod g.M) (d : ZMod N)) • 1) ^ n) z ∈ B1 (Lev N l) (k - 2)) →
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l →
      (TqZ (Lev N l) (k - 2) q (σT q) - g.a q • 1) z ∈ B1 (Lev N l) (k - 2)) ∧
    (UlZ (Lev N l) (k - 2) l - α • 1) z ∈ B1 (Lev N l) (k - 2) ∧
    (∀ d : (ZMod N)ˣ, (DdZ (Lev N l) (k - 2) (σD d) - g.χ (ZMod.castHom hN (ZMod g.M) (d : ZMod N)) • 1) z ∈ B1 (Lev N l) (k - 2)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.hecke_semisimple_at_newform | exact GlobalTheory.HeckeFamilyMatrices.hecke_semisimple_at_newform | (intros; apply GlobalTheory.HeckeFamilyMatrices.hecke_semisimple_at_newform <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

theorem _root_.GlobalTheory.T.tameClass_limit_of_normCompatible_shapiroSystem : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (e n : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l) (P : Qbar l) (b : ℕ → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) → (∀ r x, χ r x ∈ c.O) → (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) → (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) → P ∈ c.O → (∀ r i, b r i ∈ c.O) → (∀ s i, y s i ∈ c.O) → (∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s) i - (P • y s + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∃ (Y : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (b' : Fin 2 → Qbar l), ShCoc (mat W) ψ Y ∧ (∀ x i, Continuous fun s => Y s x i) ∧ (∀ s x i, Y s x i ∈ c.O) ∧ (∀ i, b' i ∈ c.O) ∧ (∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b' - b')) ∧ ∀ r s x i, ‖Y s x i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x' => Yw r s (x, x')) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  first | exact @GlobalTheory.KA.tame_limit | exact GlobalTheory.KA.tame_limit | (intros; apply GlobalTheory.KA.tame_limit <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.diamond_commutes_hecke_U : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w →
  X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b) = X.heckeU l (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  first | exact @GlobalTheory.KZ.DiamU.act_sgD_heckeU | exact GlobalTheory.KZ.DiamU.act_sgD_heckeU | (intros; apply GlobalTheory.KZ.DiamU.act_sgD_heckeU <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ

theorem isDiam_sgD_of_coprime {N l d : ℕ} (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : d = 1 := Nat.coprime_zero_right d |>.1 hd
    subst h1
    refine Classical.epsilon_spec (p := IsDiam 0 l 1) ⟨1, ⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.one_mem _
    · exact Subgroup.one_mem _
    · simp [en]
  · exact Betti.isDiam_sgD hN.ne' hl hd

theorem isDiam_mul {N l a d : ℕ} {s t : SL(2, ℤ)} (hs : IsDiam N l a s) (ht : IsDiam N l d t) :
    IsDiam N l (d * a) (s * t) := by
  obtain ⟨hs0, hsd⟩ := hs
  obtain ⟨ht0, htd⟩ := ht
  refine ⟨Subgroup.mul_mem _ hs0 ht0, ?_⟩
  have hsN := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hs0).1
  simp only [en] at hsd htd ⊢
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [hsN, hsd, htd]
  ring

end GlobalTheory.KZ

theorem GlobalTheory.KZ.isThB_act_sgD_diam_iff : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)
    (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w a d : ℕ), a.Coprime N → d.Coprime N →
    ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.diam N l a b)) φ ↔
    IsThB X A N l n (X.act l (sgD N l (d * a) : Matrix (Fin 2) (Fin 2) ℤ) b) φ := by
  intro Ω _ _ _ ε X A N l hl n w a d ha hd b hb φ
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hsa := GlobalTheory.KZ.isDiam_sgD_of_coprime (l := l) hl0 ha
  have hsd := GlobalTheory.KZ.isDiam_sgD_of_coprime (l := l) hl0 hd
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have e : X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.diam N l a b) =
      X.act l ((sgD N l a * sgD N l d : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
    rw [Matrix.SpecialLinearGroup.coe_mul, GlobalTheory.KZ.Tower.diam,
      GlobalTheory.KZ.Tower.act_act Ω ε X l _ _ (hpos _) (hpos _) b]
  rw [e]
  exact GlobalTheory.T.isCuspFunctionalValueModPrimePow_diamond_independent Ω ε X A N l n w (d * a) b hb _ (GlobalTheory.KZ.isDiam_mul hsa hsd) φ
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.HeckeGal

theorem B_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    (b : X.Fn l) (hb : b ∈ X.B N l w) (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) :
    X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

def trSL (t : ℤ) : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem trSL_mem_Gam (N l : ℕ) (t : ℤ) : trSL t ∈ Gam N l := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]; simp [trSL]
  · rw [CongruenceSubgroup.Gamma0_mem]; simp [trSL]

theorem B_inv_tr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    (b : X.Fn l) (hb : b ∈ X.B N l w) (t : ℤ) : X.act l !![1, t; 0, 1] b = b :=
  B_inv X N l w b hb (trSL t) (trSL_mem_Gam N l t)

theorem op_galB_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ T : Letter, admitted N l T → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.op N l T (X.galB l s b) = X.galB l s (X.op N l T b) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl hN hNl hw T hT s b hb
  have hgb : X.galB l s b ∈ X.B N l w := GlobalTheory.T.galB_mem_kummer_invariant_set ε X hε hj N l w hl hN hNl hw s b hb
  have hinv := B_inv_tr X N l w _ hgb

  have hup : ∀ q : ℕ, 0 < q →
      (∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) (X.galB l s b) =
        X.galB l s ((∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) b) := by
    intro q hq
    obtain ⟨e, he, hζ⟩ := GlobalTheory.T.galAlgClosureRat_primitiveRoot_eq_pow s q hq

    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    rw [← GlobalTheory.T.sum_act_upperTriangular_hecke_reindex_coprime_unit X l _ hinv q e hq he]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (GlobalTheory.T.galoisAction_upperTriangular_hecke_reindex_on_B ε X hε hj N l w hl hN hNl hw s q e hq hζ (j : ℤ) b hb).symm

  have hdiam : ∀ d : ℕ, Nat.Coprime d N → sgD N l d ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l := by
    intro d hd
    have hex := GlobalTheory.T.exists_isDiamondMatrixGamma1Gamma0_of_coprime N l d (by omega) hNl hd
    exact (Classical.epsilon_spec hex).1
  cases T with
  | T q =>
    obtain ⟨hqp, hqd⟩ := hT
    have hqN : Nat.Coprime q N :=
      (Nat.Coprime.coprime_dvd_right (Dvd.intro l rfl) ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqd))
    have hq : 0 < q := hqp.pos
    simp only [Tower.op, Tower.heckeT, LinearMap.add_apply, map_add (f := _)]
    rw [hup q hq]
    congr 1
    have hdet1 : 0 < (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ).det := by
      rw [(sgD N l q).2]; exact one_pos
    have hdet2 : 0 < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two_of]; exact_mod_cast hq
    rw [← Tower.act_act Ω ε X l _ _ hdet1 hdet2, ← Tower.act_act Ω ε X l _ _ hdet1 hdet2,
      GlobalTheory.T.galB_act_diagNatOne_comm ε X hε l q hq s,
      GlobalTheory.T.galB_act_comm_gamma0CapGamma0Level_shimuraReciprocity ε X hε hj N l w hl hN hNl hw (sgD N l q) (hdiam q hqN) s b hb]
  | U =>
    simp only [Tower.op, Tower.heckeU]
    exact hup l (Fact.out : l.Prime).pos
  | D d =>
    simp only [Tower.op, Tower.diam]
    exact (GlobalTheory.T.galB_act_comm_gamma0CapGamma0Level_shimuraReciprocity ε X hε hj N l w hl hN hNl hw (sgD N l d) (hdiam d hT) s b hb).symm

end GlobalTheory.KZ.HeckeGal
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_mul_scalarClass_eq_smul_add_coboundary_modPrimePow : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ' : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ' g : c.Oˣ) : c.O)) → (∃ g, θ' g ≠ 1) → (∃ g, θ' g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∀ r : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 1 ≤ n → ∀ a : ↥(Dec (F := ℚ) A) → c.O, Continuous a → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a (s * t) - (a s + ((θ' s : c.Oˣ) : c.O) * a t)) → (∀ x y : c.O, (∀ s, ((l : ℕ) : c.O) ^ n ∣ x * a s - (((θ' s : c.Oˣ) : c.O) * y - y)) → ((l : ℕ) : c.O) ^ (n - r) ∣ x) → ∀ a' : ↥(Dec (F := ℚ) A) → c.O, Continuous a' → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a' (s * t) - (a' s + ((θ' s : c.Oˣ) : c.O) * a' t)) → ∃ x y : c.O, ∀ s, ((l : ℕ) : c.O) ^ n ∣ (m : c.O) * a' s - (x * a s + (((θ' s : c.Oˣ) : c.O) * y - y)) := by
  first | exact @GlobalTheory.LocCharSpan.span | exact GlobalTheory.LocCharSpan.span | (intros; apply GlobalTheory.LocCharSpan.span <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.galois_cocycle_integral_after_scaling : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (z : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) → z ∈ Z1 (Loc.colRep W) → Unr W z → ∀ A : ValuationSubring Ω, ∃ (c' : Coef l) (k : ℕ), c.O ≤ c'.O ∧ (∀ s i, ((l : ℕ) : Qbar l) ^ k * z s i ∈ c'.O) ∧ (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c'.O) ∧ ∀ s ∈ Ine (F := ℚ) B, ((l : ℕ) : Qbar l) ^ k • z s = mat W s *ᵥ x - x) ∧ (Triv W A z → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c'.O) ∧ ∀ s ∈ Dec (F := ℚ) A, ((l : ℕ) : Qbar l) ^ k • z s = mat W s *ᵥ x - x) ∧ (Gr W A z → ∃ x ∈ c'.O, ∀ s ∈ Dec (F := ℚ) A, ((l : ℕ) : Qbar l) ^ k * z s 1 = mat W s 1 1 * x - x) := by
  first | exact @GlobalTheory.CocInt.integral_after_scaling | exact GlobalTheory.CocInt.integral_after_scaling | (intros; apply GlobalTheory.CocInt.integral_after_scaling <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

theorem _root_.GlobalTheory.T.coefficient_congruence_of_twisted_values : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (k m₁ : ℕ), (∀ n, F.coeff n ∈ c.O) → (∀ m, m₁ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg k (tval F (l ^ (3 * m)) z) 0) → ∀ n, Cg k (F.coeff n) 0 := by
  first | exact @GlobalTheory.KZ.CoefVal.coeff_cg_of_values | exact GlobalTheory.KZ.CoefVal.coeff_cg_of_values | (intros; apply GlobalTheory.KZ.CoefVal.coeff_cg_of_values <;> assumption)
end
