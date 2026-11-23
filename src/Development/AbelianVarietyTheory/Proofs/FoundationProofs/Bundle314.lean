module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRealSpanEqConjFixedPrimeMulRelNorm
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LGrp.Zonal

open GlobalTheory.LocGL

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {K : Subgroup G}

theorem heckeVec_dosetInd {σ : Representation ℂ G V} (hσ : IsSmooth σ) (hc : IsCompact (K : Set G))
    (hK : IsCommensurated K) {z : V} (hz : z ∈ fixed σ K) (g : G) :
    heckeVec σ K (dosetInd ℂ K g) z =
      ((P.finite_cosets_in_doset hK g).toFinset.card : ℂ) • idem hσ hc (σ g z) := by
  have hmem : ∀ c : G ⧸ K, c.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) ↔
      c ∈ (P.finite_cosets_in_doset hK g).toFinset := fun c => by
    rw [Set.Finite.mem_toFinset, DoubleCoset.mem_doubleCoset]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩, fun ⟨a, b, e⟩ => ⟨a, a.2, b, b.2, e⟩⟩
  rw [← idem_of_mem hσ hc (SatCompare.heckeVec_mem_fixed hK (Final.DosetIndMem G K ℂ g) hz)]
  unfold heckeVec

  rw [finsum_eq_sum_of_support_subset (s := (P.finite_cosets_in_doset hK g).toFinset), map_sum,
  Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
  · refine Finset.sum_congr rfl fun c hc' => ?_
    have h1 := (hmem c).2 hc'
    obtain ⟨a, b, e⟩ := (Set.Finite.mem_toFinset _).1 hc'
    rw [dosetInd, Set.indicator_of_mem h1, Pi.one_apply, one_smul, e, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, mem_fixed.1 hz b b.2, idem_apply_mem hσ hc a.2]
  · intro c hc'
    by_contra h
    exact hc' (by
      show dosetInd ℂ K g c.out • _ = 0
      rw [dosetInd, Set.indicator_of_notMem (fun h' => h ((hmem c).1 h')), zero_smul])


omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem card_ne_zero (hK : IsCommensurated K) (g : G) :
    ((P.finite_cosets_in_doset hK g).toFinset.card : ℂ) ≠ 0 := by
  refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), (Set.Finite.mem_toFinset _).2 ?_⟩)
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K g
  exact ⟨1, u, by simpa using hu⟩

theorem idem_orbitMap {π : Representation ℂ G V} {ρ : Representation ℂ G W} (hπ : IsSmooth π) (hρ : IsSmooth ρ)
    (hc : IsCompact (K : Set G)) {x : V} {y : W}
    (h : ∀ g, ∃ c : ℂ, idem hπ hc (π g x) = c • x ∧ idem hρ hc (ρ g y) = c • y) (a : MonoidAlgebra ℂ G) :
    ∃ c : ℂ, idem hπ hc (orbitMap π x a) = c • x ∧ idem hρ hc (orbitMap ρ y a) = c • y := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    obtain ⟨c, ha, hb⟩ := h g
    refine ⟨c, ?_, ?_⟩
    · show idem hπ hc (π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x) = _
      simpa using ha
    · show idem hρ hc (ρ.asAlgebraHom (MonoidAlgebra.of ℂ G g) y) = _
      simpa using hb
  | add a b ha hb =>
    obtain ⟨c, h1, h2⟩ := ha
    obtain ⟨d, h3, h4⟩ := hb
    exact ⟨c + d, by rw [map_add (f := _), map_add (f := _), h1, h3, add_smul], by rw [map_add (f := _), map_add (f := _), h2, h4, add_smul]⟩
  | smul r a ha =>
    obtain ⟨c, h1, h2⟩ := ha
    exact ⟨r * c, by rw [map_smul, map_smul, h1, mul_smul], by rw [map_smul, map_smul, h2, mul_smul]⟩

theorem isSubquot_of_hecke_eigenvalues (G V W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (ρ : Representation ℂ G W)
    (K : Subgroup G) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K) (hπ : IsIrrSmooth π) (hρ : IsSmooth ρ)
    (x : V) (hx : x ∈ fixed π K) (hx0 : x ≠ 0) (y : W) (hy : y ∈ fixed ρ K) (hy0 : y ≠ 0)
    (h : ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec π K h x = c • x ∧ heckeVec ρ K h y = c • y) : IsSubquot π ρ := by
  have h1 : ∀ g, ∃ c : ℂ, idem hπ.1 hc (π g x) = c • x ∧ idem hρ hc (ρ g y) = c • y := fun g => by
    obtain ⟨c, ha, hb⟩ := h _ (Final.DosetIndMem G K ℂ g)
    rw [heckeVec_dosetInd hπ.1 hc hK hx] at ha
    rw [heckeVec_dosetInd hρ hc hK hy] at hb
    have hn := card_ne_zero hK g
    refine ⟨((P.finite_cosets_in_doset hK g).toFinset.card : ℂ)⁻¹ * c, ?_, ?_⟩
    · rw [mul_smul, ← ha, inv_smul_smul₀ hn]
    · rw [mul_smul, ← hb, inv_smul_smul₀ hn]
  let T : Subrepresentation π :=
    ⟨⨅ g, LinearMap.ker (idem hπ.1 hc ∘ₗ π g), fun g v hv => by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hv ⊢
      intro g'
      simpa using hv (g' * g)⟩
  have hT : T = ⊥ := by
    haveI := hπ.2
    refine (eq_bot_or_eq_top T).resolve_right fun e => hx0 ?_
    have : x ∈ T := e ▸ trivial
    have h2 : idem hπ.1 hc (π 1 x) = 0 := (Submodule.mem_iInf _).1 this 1
    rwa [map_one, Module.End.one_apply, idem_of_mem hπ.1 hc hx] at h2
  have hker : LinearMap.ker (orbitMap ρ y).toLinearMap ≤ LinearMap.ker (orbitMap π x).toLinearMap := fun a h0 => by
    have h0' : orbitMap ρ y a = 0 := h0
    have : orbitMap π x a ∈ T := (Submodule.mem_iInf _).2 fun g => by
      show idem hπ.1 hc (π g (orbitMap π x a)) = 0
      obtain ⟨c, h2, h3⟩ := idem_orbitMap hπ.1 hρ hc h1 (Representation.leftRegular ℂ G g a)
      rw [(orbitMap ρ y).isIntertwining, h0', map_zero, map_zero] at h3
      rw [← (orbitMap π x).isIntertwining, h2,
        (smul_eq_zero.1 h3.symm).resolve_right hy0, zero_smul]
    rw [hT] at this
    exact this
  let f : (orbitMap ρ y).range.toSubmodule →ₗ[ℂ] V :=
    Submodule.liftQ _ _ hker ∘ₗ (orbitMap ρ y).toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hf : ∀ a h, f ⟨orbitMap ρ y a, h⟩ = orbitMap π x a := fun a h => by
    have := (orbitMap ρ y).toLinearMap.quotKerEquivRange_symm_apply_image a h
    exact (congrArg (Submodule.liftQ _ _ hker) this).trans rfl
  refine ⟨(orbitMap ρ y).range, ⟨f, fun g => LinearMap.ext ?_⟩, fun v => ?_⟩
  · rintro ⟨_, a, rfl⟩
    have e := (orbitMap ρ y).isIntertwining _ _ g a
    have e' : (orbitMap ρ y).range.toRepresentation g ⟨orbitMap ρ y a, a, rfl⟩ =
        ⟨orbitMap ρ y (Representation.leftRegular ℂ G g a), _, rfl⟩ := Subtype.ext e.symm
    show f ((orbitMap ρ y).range.toRepresentation g ⟨orbitMap ρ y a, a, rfl⟩) = π g (f ⟨orbitMap ρ y a, a, rfl⟩)
    rw [e']
    exact (hf _ _).trans (((orbitMap π x).isIntertwining _ _ g a).trans (congrArg (π g) (hf _ _).symm))
  · obtain ⟨a, rfl⟩ := orbitMap_surjective hπ.2 hx0 v
    exact ⟨⟨_, a, rfl⟩, hf a _⟩

end GlobalTheory.LGrp.Zonal
end

section

noncomputable section

namespace GlobalTheory.K5.LevelDown

open Polynomial GlobalTheory.K5 GlobalTheory.K5.Basic

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem mem_adjoin (L : ℕ) (x : On p L) : x ∈ Algebra.adjoin (O0 p) {xn p L, yn p L} := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  set S := Algebra.adjoin (O0 p) {xn p L, yn p L}
  have hx : xn p L ∈ S := Algebra.subset_adjoin (by simp)
  have hy : yn p L ∈ S := Algebra.subset_adjoin (by simp)
  have hb : ∀ b : O0 p, Ideal.Quotient.mk (towerIdeal p L) (C (C b)) ∈ S := by
    intro b
    have : Ideal.Quotient.mk (towerIdeal p L) (C (C b)) = algebraMap (O0 p) (On p L) b := rfl
    rw [this]; exact S.algebraMap_mem b
  have hC : ∀ a : Polynomial (O0 p), Ideal.Quotient.mk (towerIdeal p L) (C a) ∈ S := by
    intro a
    induction a using Polynomial.induction_on with
    | C b => exact hb b
    | add f g hf hg =>
      rw [C_add, (Ideal.Quotient.mk (towerIdeal p L)).map_add]
      exact S.add_mem hf hg
    | monomial k b _ =>
      rw [C_mul, C_pow, map_mul, map_pow]
      exact S.mul_mem (hb b) (S.pow_mem hx _)
  induction f using Polynomial.induction_on with
  | C a => exact hC a
  | add f g hf hg =>
    rw [(Ideal.Quotient.mk (towerIdeal p L)).map_add]
    exact S.add_mem hf hg
  | monomial k a _ => rw [map_mul, map_pow]; exact S.mul_mem (hC a) (S.pow_mem hy _)

theorem zeta_pow_sub (T : GlobalTheory.K5.Tower p Ω) (m k : ℕ) : T.ζ (m + k) ^ p ^ k = T.ζ m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.ζpow, ih]

theorem qq_pow_sub (T : GlobalTheory.K5.Tower p Ω) (m k : ℕ) : T.qq (m + k) ^ p ^ k = T.qq m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.qpow, ih]

theorem isInt_nat (m : ℕ) : IsInt (p := p) (m : Ω) := by
  rw [IsInt, ← map_natCast (algebraMap (O0 p) Ω)]; exact isIntegral_algebraMap

theorem isInt_emb (T : GlobalTheory.K5.Tower p Ω) (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (hι : IsEmb T L ι)
    (x : On p L) : IsInt (p := p) (ι x) := by
  have h : Algebra.adjoin (O0 p) {xn p L, yn p L} ≤ (integralClosure (O0 p) Ω).comap ι := by
    rw [Algebra.adjoin_le_iff]
    rintro z (rfl | rfl)
    · show ι (xn p L) ∈ integralClosure (O0 p) Ω
      rw [mem_integralClosure_iff, hι.1]
      exact IsIntegral.of_pow (pow_pos hp.out.pos L) (by rw [(T.prim L).pow_eq_one]; exact isIntegral_one)
    · show ι (yn p L) ∈ integralClosure (O0 p) Ω
      rw [mem_integralClosure_iff, hι.2]
      refine IsIntegral.of_pow (pow_pos hp.out.pos L) ?_
      rw [qq_pow]; exact isIntegral_algebraMap
  exact h (mem_adjoin L x)

theorem fix_emb (T : GlobalTheory.K5.Tower p Ω) (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (hι : IsEmb T L ι)
    (g : Gal p Ω) (hg : g ∈ Gn T L) (x : On p L) : g (ι x) = ι x := by
  have hg' := (mem_gn T L g).1 hg
  have h : Algebra.adjoin (O0 p) {xn p L, yn p L} ≤
      AlgHom.equalizer ((g : Ω →ₐ[O0 p] Ω).comp ι) ι := by
    rw [Algebra.adjoin_le_iff]
    rintro z (rfl | rfl)
    · show g (ι (xn p L)) = ι (xn p L)
      rw [hι.1]; exact hg'.1
    · show g (ι (yn p L)) = ι (yn p L)
      rw [hι.2]; exact hg'.2
  exact h (mem_adjoin L x)

theorem cong_mono {k m : ℕ} (h : k ≤ m) {x y : Ω}
    (hc : Cong (p := p) m x y) : Cong (p := p) k x y := by
  obtain ⟨z, hz, e⟩ := hc
  refine ⟨(p : Ω) ^ (m - k) * z, IsIntegral.mul (IsIntegral.pow (isInt_nat p) _) hz, ?_⟩
  rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

theorem locallyConstantModPrimePow_of_le {k m : ℕ} (h : k ≤ m) {w : Gal p Ω → Ω} (hw : LocallyConstantOneCochain m w) : LocallyConstantOneCochain k w :=
  ⟨hw.1, fun g => by
    obtain ⟨S, hS⟩ := hw.2 g
    exact ⟨S, fun h' hh => cong_mono h (hS h' hh)⟩⟩

theorem cong_mul' {k : ℕ} {x y x' y' : Ω} (h : Cong (p := p) k x y) (h' : Cong (p := p) k x' y')
    (hx' : IsInt (p := p) x') (hy : IsInt (p := p) y) : Cong (p := p) k (x * x') (y * y') := by
  obtain ⟨a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := h'
  exact ⟨a * x' + y * b, (ha.mul hx').add (hy.mul hb), by linear_combination x' * e + y * e'⟩

theorem kum_down (T : GlobalTheory.K5.Tower p Ω) {n L : ℕ} (hnL : n ≤ L) {H : Subgroup (Gal p Ω)} {R : Ω}
    (hR : R ≠ 0) {aL : Gal p Ω → ZMod (p ^ L)} (haL : IsKum T L H R aL)
    {a : Gal p Ω → ZMod (p ^ n)} (ha : IsKum T n H (R ^ p ^ (L - n)) a) {g : Gal p Ω}
    (hg : g ∈ H) : (a g).val ≡ (aL g).val [MOD p ^ n] := by
  have e1 := ha g hg
  rw [map_pow, haL g hg, mul_pow, ← pow_mul, mul_comm ((aL g).val), pow_mul] at e1
  have hz : T.ζ L ^ p ^ (L - n) = T.ζ n := by
    have := zeta_pow_sub T n (L - n); rwa [Nat.add_sub_cancel' hnL] at this
  rw [hz] at e1
  have e2 := mul_right_cancel₀ (pow_ne_zero _ hR) e1
  exact ((zeta_pow_eq_iff T n _ _).1 e2).symm

end GlobalTheory.K5.LevelDown

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem GlobalTheory.K5.LevelDown.cup_kummer_dlog_mod : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ ι : On p L →ₐ[O0 p] Ω, IsEmb T L ι →
  ∀ (u v : (On p L)ˣ) (α β α' β' : On p L), IsDlog p L (u : On p L) α β → IsDlog p L (v : On p L) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = ι u → s ^ (p ^ n) = ι v →
  ∀ a b lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T L) r a → IsKum T n (Gn T L) s b → IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c * (((a g).val : Ω) * ((b h).val : Ω)) + (p : Ω) ^ c * ι (α * β' - β * α') * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  intro p _ hp2
  obtain ⟨c, hc⟩ := GlobalTheory.T.hodgeTate_cup_kummer_classes_eq_dlog_determinant p hp2
  refine ⟨c, ?_⟩
  intro Ω _ _ hclo T L n hnL hn ι hι u v α β α' β' hu hv r s hr hs a b lz lq ha hb hlz hlq
  have := hclo.clo
  have hpr : p.Prime := Fact.out
  have hL : 1 ≤ L := le_trans hn hnL
  have hpos : ∀ k, 0 < p ^ k := fun k => pow_pos hpr.pos k
  have hunit : ∀ w : (On p L)ˣ, ι (w : On p L) ≠ 0 := fun w h => by
    have := congrArg ι w.mul_inv
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hroot : ∀ (w : (On p L)ˣ) (x : Ω), x ^ p ^ n = ι (w : On p L) → ∃ X : Ω, X ≠ 0 ∧
      X ^ p ^ (L - n) = x ∧ X ^ p ^ L = (T.ζ L - 1) ^ (0 : ℤ) * ι (w : On p L) := by
    intro w x hx
    obtain ⟨X, hX⟩ := IsAlgClosed.exists_pow_nat_eq x (hpos (L - n))
    refine ⟨X, ?_, hX, ?_⟩
    · rintro rfl
      rw [zero_pow (pow_ne_zero _ hpr.ne_zero)] at hX
      rw [← hX, zero_pow (pow_ne_zero _ hpr.ne_zero)] at hx
      exact hunit w hx.symm
    · rw [zpow_zero, one_mul, ← hx, ← hX, ← pow_mul, ← pow_add, Nat.sub_add_cancel hnL]
  obtain ⟨R, hR0, hR, hRL⟩ := hroot u r hr
  obtain ⟨S, hS0, hS, hSL⟩ := hroot v s hs
  have hfix := LevelDown.fix_emb T L ι hι
  have hgn := fun g (hg : g ∈ Gn T L) => (Basic.mem_gn T L g).1 hg
  obtain ⟨aL, haL⟩ := Basic.exists_isKum T L (Gn T L) hR0 (fun g hg => by
    rw [hRL, zpow_zero, one_mul]; exact hfix g hg _)
  obtain ⟨bL, hbL⟩ := Basic.exists_isKum T L (Gn T L) hS0 (fun g hg => by
    rw [hSL, zpow_zero, one_mul]; exact hfix g hg _)
  have hZ0 : T.ζ (2 * L) ≠ 0 := (T.prim _).ne_zero (pow_ne_zero _ hpr.ne_zero)
  have hZL : T.ζ (2 * L) ^ p ^ L = T.ζ L := by
    rw [two_mul]; exact LevelDown.zeta_pow_sub T L L
  have hQL : T.qq (2 * L) ^ p ^ L = T.qq L := by
    rw [two_mul]; exact LevelDown.qq_pow_sub T L L
  obtain ⟨zL, hzL⟩ := Basic.exists_isKum T L (Gn T L) hZ0 (fun g hg => by
    rw [hZL]; exact (hgn g hg).1)
  obtain ⟨qL, hqL⟩ := Basic.exists_isKum T L (Gn T L) (Basic.qq_ne_zero T _) (fun g hg => by
    rw [hQL]; exact (hgn g hg).2)
  obtain ⟨w, hw, hcong⟩ := hc Ω hclo T L hL ι hι 0 0 u v α β α' β' hu hv R S hRL hSL aL bL zL qL
    haL hbL hzL hqL
  have e2 : L + n + (L - n) = 2 * L := by omega
  have hZn : T.ζ (2 * L) ^ p ^ (L - n) = T.ζ (L + n) := by
    rw [← e2]; exact LevelDown.zeta_pow_sub T (L + n) (L - n)
  have hQn : T.qq (2 * L) ^ p ^ (L - n) = T.qq (L + n) := by
    rw [← e2]; exact LevelDown.qq_pow_sub T (L + n) (L - n)
  have hX : ι (fPi p L 0 0 α β α' β') / (T.ζ L - 1) = ι (α * β' - β * α') := by
    have hne : T.ζ L - 1 ≠ 0 :=
      sub_ne_zero.2 ((T.prim L).ne_one (Nat.one_lt_pow (by omega) hpr.one_lt))
    rw [div_eq_iff hne]
    have : fPi p L 0 0 α β α' β' = (xn p L - 1) * (α * β' - β * α') := by
      simp only [fPi]; push_cast; ring
    rw [this, map_mul, map_sub, hι.1, map_one]; ring
  refine ⟨w, LevelDown.locallyConstantModPrimePow_of_le hnL hw, fun g hg h hh => ?_⟩
  refine Basic.cong_trans ?_ (LevelDown.cong_mono hnL (hcong g hg h hh))
  beta_reduce
  rw [hX]
  have hA : Cong (p := p) n ((a g).val : Ω) ((aL g).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL hR0 haL (by rw [hR]; exact ha) hg)
  have hB : Cong (p := p) n ((b h).val : Ω) ((bL h).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL hS0 hbL (by rw [hS]; exact hb) hh)
  have hC : Cong (p := p) n ((lz g).val : Ω) ((zL g).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL hZ0 hzL (by rw [hZn]; exact hlz) hg)
  have hD : Cong (p := p) n ((lq h).val : Ω) ((qL h).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL (Basic.qq_ne_zero T _) hqL (by rw [hQn]; exact hlq) hh)
  have iN := fun m : ℕ => (LevelDown.isInt_nat (p := p) (Ω := Ω) m)
  have iP : IsInt (p := p) ((p : Ω) ^ c) := IsIntegral.pow (iN p) c
  have iX : IsInt (p := p) (ι (α * β' - β * α')) := LevelDown.isInt_emb T L ι hι _
  refine Basic.cong_add ?_ ?_
  · exact LevelDown.cong_mul' (Basic.cong_refl _ _)
      (LevelDown.cong_mul' hA hB (iN _) (iN _)) ((iN _).mul (iN _)) iP
  · exact LevelDown.cong_mul' (Basic.cong_refl _ _)
      (LevelDown.cong_mul' hC hD (iN _) (iN _)) ((iN _).mul (iN _)) (iP.mul iX)
end
end

section

noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU Filter Topology
open GlobalTheory.LocalGlobalChar (eps ev_ind tendsto_eps_tens)

section KFinite

variable {G : Type} [Group G] {K : Subgroup G}

theorem IsKFinite.mul {Φ Ψ : G → ℂ} (h : IsKFinite K Φ) (h' : IsKFinite K Ψ) : IsKFinite K fun g => Φ g * Ψ g := by
  obtain ⟨W, hf, hW⟩ := isKFinite_iff.1 h
  obtain ⟨W', hf', hW'⟩ := isKFinite_iff.1 h'
  exact isKFinite_iff.2 ⟨W * W', Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hf).mul (Module.Finite.iff_fg.1 hf')),
    fun k hk => Submodule.mul_mem_mul (hW k hk) (hW' k hk)⟩

end KFinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Ideles

def cutIdele (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AF F ⊗[F] E)ˣ) : (AF F ⊗[F] E)ˣ :=
  (∏ w, ideleAtInf F E w (unitInf F E w x)) * ∏ v ∈ S, ideleAt F E v (unitFin F E v x)

omit [NumberField E] in
theorem cutIdele_inv (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AF F ⊗[F] E)ˣ) :
    cutIdele S x⁻¹ = (cutIdele S x)⁻¹ := by
  simp only [cutIdele, map_inv, Finset.prod_inv_distrib, mul_inv]

omit [NumberField E] in
theorem unitInf_cutIdele (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AF F ⊗[F] E)ˣ) (w : InfinitePlace F) :
    unitInf F E w (cutIdele S x) = unitInf F E w x := by
  rw [cutIdele, map_mul, map_prod, map_prod,
    Finset.prod_eq_single w (fun u _ hu => unitInf_ideleAtInf_ne hu.symm _) (by simp)]
  simp

omit [NumberField E] in
theorem unitFin_cutIdele_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (x : (AF F ⊗[F] E)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : unitFin F E v (cutIdele S x) = unitFin F E v x := by
  rw [cutIdele, map_mul, map_prod, map_prod,
    Finset.prod_eq_single v (fun u _ hu => unitFin_ideleAt_ne hu.symm _) (fun h => absurd hv h)]
  simp

omit [NumberField E] in
theorem unitFin_cutIdele_of_notMem {S : Finset (HeightOneSpectrum (𝓞 F))} (x : (AF F ⊗[F] E)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : unitFin F E v (cutIdele S x) = 1 := by
  rw [cutIdele, map_mul, map_prod, map_prod,
    Finset.prod_eq_one (s := S) (fun u hu => unitFin_ideleAt_ne (ne_of_mem_of_not_mem hu hv).symm _)]
  simp

theorem val_cutIdele (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AF F ⊗[F] E)ˣ) :
    (cutIdele S x).1 = algebraMap (AF F) (AF F ⊗[F] E) (eps S) * (x.1 - 1) + 1 := by
  refine adele_ext (fun w => ?_) fun v => ?_
  · have h : compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) (eps S)) = 1 := rfl
    rw [map_add (f := _), map_mul, map_sub, h, map_one, one_mul, sub_add_cancel]
    exact congrArg Units.val (unitInf_cutIdele S x w)
  · have h : compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) (eps S)) =
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (GlobalTheory.LocalGlobalChar.ind S) ⊗ₜ[F] (1 : E) := rfl
    rw [map_add (f := _), map_mul, map_sub, h, map_one, ev_ind]
    split_ifs with hv
    · rw [← Algebra.TensorProduct.one_def, one_mul, sub_add_cancel]
      exact congrArg Units.val (unitFin_cutIdele_of_mem x hv)
    · rw [TensorProduct.zero_tmul, zero_mul, zero_add]
      exact congrArg Units.val (unitFin_cutIdele_of_notMem x hv)

theorem tendsto_cutIdele (x : (AF F ⊗[F] E)ˣ) : Tendsto (fun S => cutIdele S x) atTop (𝓝 x) := by
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have h : ∀ y : (AF F ⊗[F] E)ˣ, Tendsto (fun S => (cutIdele S y).1) atTop (𝓝 y.1) := fun y => by
    have := (tendsto_eps_tens (y.1 - 1)).add_const 1
    rw [show y.1 - 1 + 1 = y.1 by ring] at this
    simpa only [val_cutIdele] using this
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h x).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)
  simpa only [cutIdele_inv] using h x⁻¹

end Ideles

variable {σ : E →ₐ[F] E} {n : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsLattice E L] {a : GL (Fin n) (AF F ⊗[F] E)} {μ : (AF F ⊗[F] E)ˣ →* Circle} {s : ℂ}
  {Φi : ∀ w, GArch σ Q w → ℂ} {Φf : ∀ v, GLoc σ Q v → ℂ}

end GlobalTheory.Doubling

end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

theorem _root_.GlobalTheory.T.exists_real_span_eq_conjFixedPrime_mul_relNorm : ∀ (D : D7) (P : Ideal (𝓞 D.host.E)), P.IsPrime → P ≠ ⊥ → D.host.conj • P = P → ∃ (t : 𝓞 D.host.E) (B : Ideal (𝓞 D.host.E)), t ≠ 0 ∧ D.host.conj (t : D.host.E) = t ∧ Ideal.span {t} = P * B * (D.host.conj • B) := by
  first | exact @GlobalTheory.FixedPrimeNorm.exists_span_eq_prime_mul_norm | exact GlobalTheory.FixedPrimeNorm.exists_span_eq_prime_mul_norm | (intros; apply GlobalTheory.FixedPrimeNorm.exists_span_eq_prime_mul_norm <;> assumption)
end
