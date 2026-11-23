module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1808
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle969
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeLowerBoundTopLatticeOffHypersurface
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.Move

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem aeval_conj (y : G.Cˣ) (x : G.C) (A : Polynomial G.F) :
    Polynomial.aeval ((y : G.C) * x * ((y⁻¹ : G.Cˣ) : G.C)) A =
      (y : G.C) * Polynomial.aeval x A * ((y⁻¹ : G.Cˣ) : G.C) := by
  have hp : ∀ k : ℕ, ((y : G.C) * x * ((y⁻¹ : G.Cˣ) : G.C)) ^ k =
      (y : G.C) * x ^ k * ((y⁻¹ : G.Cˣ) : G.C) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc, Units.inv_mul_cancel_left]
  induction A using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add (f := _), map_add (f := _), hf, hg, mul_add, add_mul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, hp n, ← mul_assoc, ← mul_assoc,
      Algebra.commutes a (y : G.C)]
    simp only [mul_assoc]

theorem move (y : G.Cˣ) (s : ℚ) (g b b' : G.C) (A : Polynomial G.F)
    (hb : b' = algebraMap ℚ G.C s * (y * b * sh G y)) :
    Polynomial.aeval ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)) A * b' =
      algebraMap ℚ G.C s * (y * (Polynomial.aeval g A * b) * sh G y) := by
  rw [aeval_conj, hb, ← mul_assoc, ← Algebra.commutes s]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem cancel {R : Type*} [Ring R] (X w : R) (b u : Rˣ) (hu : X * b = u) (h : X * b = X * w) :
    (b : R) = w := by
  have hX : X = (u : R) * ((b⁻¹ : Rˣ) : R) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  have hl : (b : R) * ((u⁻¹ : Rˣ) : R) * X = 1 := by
    rw [hX, mul_assoc, ← mul_assoc ((u⁻¹ : Rˣ) : R), Units.inv_mul, one_mul, Units.mul_inv]
  calc (b : R) = ((b : R) * ((u⁻¹ : Rˣ) : R) * X) * b := by rw [hl, one_mul]
    _ = ((b : R) * ((u⁻¹ : Rˣ) : R) * X) * w := by rw [mul_assoc _ X, h, ← mul_assoc]
    _ = w := by rw [hl, one_mul]

private theorem minpoly_monic_of_irreducible (x : G.C)
    (hi : Irreducible (minpoly G.F x)) : (minpoly G.F x).Monic := by
  have hint : IsIntegral G.F x := by
    by_contra h
    exact hi.ne_zero (minpoly.eq_zero h)
  exact minpoly.monic hint

private theorem aeval_eq_zero_of_aeval_conj_eq_zero (y : G.Cˣ) (g : G.C)
    (q : Polynomial G.F) (h : Polynomial.aeval ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)) q = 0) :
    Polynomial.aeval g q = 0 := by
  rw [aeval_conj] at h
  calc Polynomial.aeval g q
      = ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * Polynomial.aeval g q * ((y⁻¹ : G.Cˣ) : G.C)) * (y : G.C) := by
        simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
    _ = 0 := by rw [h, mul_zero, zero_mul]

private theorem minpoly_conj_eq_of_irreducible (y : G.Cˣ) (g : G.C)
    (hi : Irreducible (minpoly G.F ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)))) :
    minpoly G.F ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)) = minpoly G.F g :=
  minpoly.eq_of_irreducible_of_monic hi (aeval_eq_zero_of_aeval_conj_eq_zero y g _ (minpoly.aeval _ _))
    (minpoly_monic_of_irreducible _ hi)

end GlobalTheory.LKDef.Move

namespace GlobalTheory.LKDef

open GlobalTheory.LKDef.Move

theorem cls_equiv_dcls_irr : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (sel : Polynomial G.F → ℂ), IsSel G sel → ∃ e : {q : Cls G // Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol)} ≃ {q : DCls G // Irreducible (Quot.out q).pol}, ∀ q, (Quot.out (e q).1).pol = (Quot.out q.1).pol ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → (Quot.out (e q).1).term Kf f r K φ = (Quot.out q.1).term Kf f r K φ := by
  intro p hp G ha hn sel hsel
  obtain ⟨v0, hv0⟩ : ∃ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 := by
    have h1 : 0 < G.a := by rw [ha]; exact Nat.one_pos
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp h1
    exact ⟨x.1, x.2⟩
  have key := fun (P0 : Polynomial G.F) (hi : Irreducible P0) (hm : P0.Monic)
      (hd : P0.natDegree = G.n) =>
    GlobalTheory.T.exists_polynomial_move_definiteSimilitudePair_marked p G ha hn P0 (sel P0) v0 hv0 hi (hsel v0 hv0 P0 hm hd)
  choose! A hA1 hA2 using key
  have hF := fun (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)) =>
    hA2 P.pol hi (minpoly_monic_of_irreducible (P.γ : G.C) hi) P.reg.1 P rfl hm
  choose FQ hFγ hFc hFβ hFu using hF
  have hB := fun (Q : DPair G) (hi : Irreducible Q.pol) =>
    hA1 Q.pol hi (minpoly_monic_of_irreducible (Q.γ : G.C) hi) Q.reg.1 Q rfl
  choose BP hBγ hBc hBβ hBm hBu using hB

  have hpolP : ∀ P P' : Pair G, P'.Rel P → Irreducible P.pol → P'.pol = P.pol := by
    intro P P' hr hi
    obtain ⟨y, s, -, -, hγ⟩ := hr
    have e : (P.γ : G.C) = (y : G.C) * P'.γ * ((y⁻¹ : G.Cˣ) : G.C) := by
      rw [hγ, Units.val_mul, Units.val_mul]
    have hi' : Irreducible (minpoly G.F ((y : G.C) * P'.γ * ((y⁻¹ : G.Cˣ) : G.C))) := by
      rw [← e]; exact hi
    show minpoly G.F (P'.γ : G.C) = minpoly G.F (P.γ : G.C)
    rw [e]
    exact (minpoly_conj_eq_of_irreducible y _ hi').symm
  have hFirr : ∀ (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)),
      Irreducible (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).pol := by
    intro P hi hm
    rw [DPair.pol_eq_of_rel (DPair.rel_out (FQ P hi hm))]
    show Irreducible (minpoly G.F ((FQ P hi hm).γ : G.C))
    rw [hFγ P hi hm]
    exact hi
  have hBok : ∀ (Q : DPair G) (hi : Irreducible Q.pol),
      Irreducible (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol ∧
      (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).Mark
        (sel (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol) := by
    intro Q hi
    have hr := (Pair.mk_eq_iff_rel_and_out_rel p G (BP Q hi) (BP Q hi)).2
    have hPpol : (BP Q hi).pol = Q.pol := by
      show minpoly G.F ((BP Q hi).γ : G.C) = minpoly G.F (Q.γ : G.C)
      rw [hBγ Q hi]
    have hPi : Irreducible (BP Q hi).pol := by rw [hPpol]; exact hi
    rw [hpolP _ _ hr hPi, Pair.mark_iff_of_rel p G _ _ _ hr, hPpol]
    exact ⟨hi, hBm Q hi⟩

  have hleft : ∀ (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)),
      P.Rel (BP _ (hFirr P hi hm)) := by
    intro P hi hm
    obtain ⟨y, s, hs, hβ, hγ⟩ := DPair.rel_out (FQ P hi hm)
    have hpol : (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).pol = P.pol := by
      rw [DPair.pol_eq_of_rel (DPair.rel_out (FQ P hi hm))]
      show minpoly G.F ((FQ P hi hm).γ : G.C) = minpoly G.F (P.γ : G.C)
      rw [hFγ P hi hm]
    refine ⟨y, s, hs, ?_, ?_⟩
    · rw [hBβ _ (hFirr P hi hm), hpol, hγ, Units.val_mul, Units.val_mul,
        GlobalTheory.LKDef.Move.move y s ((FQ P hi hm).γ : G.C) _ _ (A P.pol) hβ, hFγ P hi hm, ← hFβ P hi hm]
    · rw [hBγ _ (hFirr P hi hm), hγ, hFγ P hi hm]

  have hright : ∀ (Q : DPair G) (hi : Irreducible Q.pol),
      (FQ _ (hBok Q hi).1 (hBok Q hi).2).Rel Q := by
    intro Q hi
    have hr := (Pair.mk_eq_iff_rel_and_out_rel p G (BP Q hi) (BP Q hi)).2
    have hPpol : (BP Q hi).pol = Q.pol := by
      show minpoly G.F ((BP Q hi).γ : G.C) = minpoly G.F (Q.γ : G.C)
      rw [hBγ Q hi]
    have hPi : Irreducible (BP Q hi).pol := by rw [hPpol]; exact hi
    have hP'pol : (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol = Q.pol := by
      rw [hpolP _ _ hr hPi, hPpol]
    have hA' : A (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol = A Q.pol := by
      rw [hP'pol]
    obtain ⟨y, s, hs, hβ, hγ⟩ := id hr
    have hc : (y : G.C) * (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).γ *
        ((y⁻¹ : G.Cˣ) : G.C) = Q.γ := by
      rw [← hBγ Q hi, hγ, Units.val_mul, Units.val_mul]
    refine ⟨y, s, hs, ?_, ?_⟩
    · refine GlobalTheory.LKDef.Move.cancel (Polynomial.aeval (Q.γ : G.C) (A Q.pol)) _ Q.β (BP Q hi).β
        (hBβ Q hi).symm ?_
      rw [← hBβ Q hi, hβ, hFβ _ (hBok Q hi).1 (hBok Q hi).2,
        ← GlobalTheory.LKDef.Move.move y s _ _ _ _ rfl, hc, hA']
    · rw [hFγ _ (hBok Q hi).1 (hBok Q hi).2, ← hBγ Q hi, hγ]

  have hterm : ∀ (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)),
      (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).pol = P.pol ∧
      ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r →
        (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) →
        (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).term Kf f r K φ =
          P.term Kf f r K φ := by
    intro P hi hm
    have h9 := GlobalTheory.T.related_pairs_orbital_term_eq p G (FQ P hi hm) _ (DPair.rel_out (FQ P hi hm))
    refine ⟨?_, fun Kf f r K φ hr hf hφ => ?_⟩
    · rw [← h9.1]
      show minpoly G.F ((FQ P hi hm).γ : G.C) = minpoly G.F (P.γ : G.C)
      rw [hFγ P hi hm]
    · rw [← h9.2.2 Kf f r K φ hr hf hφ]
      exact (GlobalTheory.T.kottwitzTerm_eq_definitePair_of_local_isometry p G P (FQ P hi hm) (hFγ P hi hm).symm (hFc P hi hm).symm (hFu P hi hm)
        Kf f r K φ hr hf hφ).symm
  refine ⟨⟨fun q => ⟨(Quot.mk (DPair.Rel (G := G)) (FQ _ q.2.1 q.2.2) : DCls G), hFirr _ q.2.1 q.2.2⟩,
    fun q => ⟨(Quot.mk (Pair.Rel (G := G)) (BP _ q.2) : Cls G), hBok _ q.2⟩, fun q => ?_, fun q => ?_⟩,
    fun q => hterm _ q.2.1 q.2.2⟩
  · apply Subtype.ext
    exact ((Pair.mk_eq_iff_rel_and_out_rel p G _ _).1.mpr (hleft _ q.2.1 q.2.2)).symm.trans
      (Quot.out_eq q.1)
  · apply Subtype.ext
    exact ((DPair.mk_eq_iff _ _).mpr (hright _ q.2)).trans (Quot.out_eq q.1)
end GlobalTheory.LKDef
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem closed1_eq_top_of_abelian : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Closed1 (OAff A.hom) = ⊤ := by
  intro R _ A _ g hA hg
  obtain ⟨hF, h0, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  have hP := GlobalTheory.T.abelianScheme_globalOneForms_primitive R A g hA hg
  rw [eq_top_iff]
  intro w _
  obtain ⟨n, u, v, hw⟩ := GlobalTheory.T.exteriorDeriv_globalOneForm_eq_sum_wedge R _ (OAff A.hom) hF h0 w
  have hμ : ClRel (OAff (A ⊗ A).hom) (pF μ[A] w) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) :=
    GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (μ[A]).left (ovw μ[A]) w n u v hw
  have h1 : ClRel (OAff (A ⊗ A).hom) (pF (fst A A) w) (fun k ↦ pF (fst A A) (u k))
      (fun k ↦ pF (fst A A) (v k)) :=
    GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (fst A A).left (ovw (fst A A)) w n u v hw
  have h2 : ClRel (OAff (A ⊗ A).hom) (pF (snd A A) w) (fun k ↦ pF (snd A A) (u k))
      (fun k ↦ pF (snd A A) (v k)) :=
    GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (snd A A).left (ovw (snd A A)) w n u v hw
  have hsum : wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) =
      wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (v k)) +
        wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (v k)) := by
    funext T
    have e := hP w
    calc _ = dOne R _ ((pF μ[A] w).1 T) := (hμ T).symm
      _ = dOne R _ ((pF (fst A A) w).1 T + (pF (snd A A) w).1 T) :=
          congrArg (fun x : GlobForm (A ⊗ A).hom ↦ dOne R _ (x.1 T)) e
      _ = dOne R _ ((pF (fst A A) w).1 T) + dOne R _ ((pF (snd A A) w).1 T) := map_add _ _ _
      _ = _ := congrArg₂ (· + ·) (h1 T) (h2 T)
  have hz := GlobalTheory.T.sum_wedge_primitive_oneForms_eq_zero_abelianScheme R A g hA hg n u v hsum
  exact fun T ↦ (hw T).trans (congrFun hz T)

end GlobalTheory.AbCoh
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.AicAcyc

theorem aic_of_isAlgClosed (K : Type) [Field K] [IsAlgClosed K] : AIC K := by
  intro p hp hdeg
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hdeg.ne')
  exact ⟨a, ha⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem isIso_spMap {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) : IsIso (spMap (e : A →+* B)) := by
  haveI : IsIso (CommRingCat.ofHom (e : A →+* B)) := (RingEquiv.toCommRingCatIso e).isIso_hom
  unfold spMap
  infer_instance

end GlobalTheory.EtC.AicAcyc

namespace GlobalTheory.EtC


open GlobalTheory.EtC.AicAcyc in
theorem b5 : B5 := by
  intro q A _ _ hA hq n i hn
  haveI := GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots A hA
  have hK : SH (FractionRing A) :=
    GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots (FractionRing A) (Field.toIsField _) (aic_of_isAlgClosed _)
  have hE := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have heqv : Eqv (ZMod q) (spMap (algebraMap A (FractionRing A))) (tw q i) := by
    refine GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) A A (FractionRing A)
      (Algebra.ofId A (FractionRing A)) ?_
    intro O _ _ hO hOind
    obtain ⟨hfield, haic⟩ := GlobalTheory.T.isField_monicRoots_tensor_fractionRing_strictlyHenselian A O hA hO hOind
    have hSH : SH (O ⊗[A] FractionRing A) := GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots _ hfield haic
    have hqO : IsUnit (q : O) := by
      simpa using hq.map (algebraMap A O)
    let e := Algebra.TensorProduct.rid A A O
    let j : O →ₐ[A] O ⊗[A] FractionRing A := Algebra.TensorProduct.includeLeft
    have hψ : (Algebra.TensorProduct.map (AlgHom.id A O) (Algebra.ofId A (FractionRing A))) =
        j.comp e.toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro o a
      simp [j, e, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [hψ]
    have h1 : Eqv (ZMod q) (spMap (j : O →+* O ⊗[A] FractionRing A)) (tw q i) :=
      GlobalTheory.T.eqv_spMap_tw_of_isUnit q i O _ (j : O →+* O ⊗[A] FractionRing A) hO hSH hqO
    have h2 : Eqv (ZMod q) (spMap ((e : O ⊗[A] A ≃+* O) : O ⊗[A] A →+* O)) (tw q i) := by
      haveI := isIso_spMap (e : O ⊗[A] A ≃+* O)
      exact hE.1 _ _ _ inferInstance
    have h3 := (hE.2.1 _ _ _ _ _).1 h1 h2
    rw [← spMap_comp] at h3
    exact h3
  have hacK : AcycF (ZMod q) (sp (FractionRing A)) (tw q i) :=
    fun m hm => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) (FractionRing A) hK (tw q i) m hm
  exact (hE.2.2.2 _ _ _ heqv).1 hacK n hn

end GlobalTheory.EtC

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def outer (W : G.Weil) (M : Vol G) {t : T} {i j : ℕ} (d : PureT G (routeSmall t i j)) (F : Fn G (.grid i (j + 1)))
    (g₁ : GA D (G.V (.grid (i + 1) j))) : Fn G (.grid i j) := fun u =>
  W.kerA (.right i j) d.2 u g₁ * ∫ g in M.fd (.grid i (j + 1)), W.kerA (.down t i j) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))

theorem liftT_routeSmall (W : G.Weil) (M : Vol G) {t : T} {i j : ℕ} (τ : TotT G (routeSmall t i j))
    (F : Fn G (.grid i (j + 1))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    liftT W M (routeSmall t i j) τ F g₁ = τ.sum fun d c => c * ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := by
  simp only [liftT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

end GlobalTheory.SmallRoute
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ZConvLeft

theorem isThetaFunO_down {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') :
    ∀ d ∈ Θ'.support, IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, h1, -⟩, -⟩, -, rfl⟩ := hΘ
  intro d hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd''⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  have hdd := Finsupp.support_single_subset hd''
  rw [Finset.mem_singleton] at hdd
  subst hdd
  have h0 : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) (ρ.vT i j) :=
    (ρ.vT_is t i j i.2.le j.2).2.2
  have hf := GlobalTheory.GalLift.Vec.theta_of_thetaAt W.ψ_std W.θ_is (h1 d' hd').1.2 h0
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf _

theorem kerSmall_rat_left : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g u, kerSmall W Θ' (γ * g) g₁ u = kerSmall W Θ' g g₁ u := by
  intro D T L sc G μ₀ hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ g u
  have hω := W.om_is (.mu t i j) ⟨i.2.le, j.2⟩
  have hth := isThetaFunO_down W B ρ t i j hΘ
  unfold kerSmall
  refine Finsupp.sum_congr fun d hd => ?_
  congr 2
  show thetaKO (W.om (.mu t i j)) u (γ * g) d.1.2 = thetaKO (W.om (.mu t i j)) u g d.1.2
  unfold thetaKO
  have e : ((u, γ * g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (1, γ) * (u, g) := by simp
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ (hth d hd))

end GlobalTheory.ZConvLeft
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.slopeLowerBound_topLattice_offHypersurface : SlopeBound := by
  first | exact @GlobalTheory.HSShort.SlopeTop.slopeBound | exact GlobalTheory.HSShort.SlopeTop.slopeBound | (intros; apply GlobalTheory.HSShort.SlopeTop.slopeBound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockJet_gaussianEntire_origin_gridFrames : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ (F : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) (Θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ), Differentiable ℂ Θ → (∀ w : WO (G.pS (.top t j)) (G.pT (.top t j)), w.map (finPart D) = 0 → F w = Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ)) * Θ (fun τ => (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ)) → ∀ k : FVar D (G.pT (.top t j)).rank (G.pS (.top t j)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.top t j) F (MvPolynomial.monomial k 1) 0 = (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (k.sum fun _ n => n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  first | exact @GlobalTheory.FockJetOrigin.fockIn_gauss_zero | exact GlobalTheory.FockJetOrigin.fockIn_gauss_zero | (intros; apply GlobalTheory.FockJetOrigin.fockIn_gauss_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

theorem _root_.GlobalTheory.T.detFactorDepth_eq_chart_value_and_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), (∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k) ∧ ∀ cx : Lt1 Dw → ℕ, nuProd p y cx = nuP p y cx := by
  first | exact @GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP | exact GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP | (intros; apply GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.exists_compact_ge_compactPart_twistedCentralizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := by
  first | exact @GlobalTheory.CptTorus.main | exact GlobalTheory.CptTorus.main | (intros; apply GlobalTheory.CptTorus.main <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_unique_admissible_localComponent_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ w : Pl E, (∃ σ : SmIrr (UL n w), IsCompU π w σ ∧ ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → FiniteDimensional ℂ (fixed σ.ρ U)) ∧ ∀ σ σ' : SmIrr (UL n w), IsCompU π w σ → IsCompU π w σ' → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  first | exact @GlobalTheory.BCT.LocCompU.exists_unique_locComp | exact GlobalTheory.BCT.LocCompU.exists_unique_locComp | (intros; apply GlobalTheory.BCT.LocCompU.exists_unique_locComp <;> assumption)
end
