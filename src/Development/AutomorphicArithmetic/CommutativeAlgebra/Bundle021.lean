module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle014
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
public import GroundTheory.FunctionField.DivisorDegree
public import GroundTheory.FunctionField.ExistsBoundDegSubFinrankL
public import Development.EtaleCohomology.EtaleSheaves.Bundle009
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle016
public import Mathlib.AlgebraicGeometry.Normalization
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.FunctionField.Divisor

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.VanishingEvaluation

variable {R : Type} [CommRing R]

private noncomputable abbrev pb {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n) :
    Cochain ((chains R).obj E) K n :=
  (Cochain.ofHom ((chains R).map f)).comp α (zero_add n)

private theorem pb_sub {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E') K n) :
    pb f (α - β) = pb f α - pb f β :=
  Cochain.comp_sub _ _ _ _

private theorem ev_pb {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (pb f α) p s h U x = ev (R := R) α p s h U (x.map f) :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.2.1 f α p s h U x

private theorem ev_zero {E : Spc} {K : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (R := R) (0 : Cochain ((chains R).obj E) K n) p s h U x = 0 :=
  ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 0 0 p s h U x).2.2.1

private theorem pb_eq_zero {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev (R := R) α p s h U (x.map f) = 0) :
    pb f α = 0 :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p s h' U x => by rw [ev_pb, h, ev_zero]

private theorem δ_pb {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n) (n' : ℤ) :
    δ n n' (pb f α) = pb f (δ n n' α) := by
  by_cases h : n + 1 = n'
  · rw [δ_comp _ _ (zero_add n) 1 n' n' h (zero_add 1) h]; simp
  · simp [δ_shape _ _ h]

private theorem δ_van {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n) (n' : ℤ)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev (R := R) α p s h U (x.map f) = 0)
    (p : ℕ) (s : ℤ) (h' : -(p : ℤ) + n' = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (δ n n' α) p s h' U (x.map f) = 0 := by
  rw [← ev_pb, ← δ_pb, pb_eq_zero f α h, δ_zero, ev_zero]

private theorem dbl_ext (P : Arrow Spc) {K : Cx R} {N : ℤ} (α β : Cochain ((chains R).obj (dbl P)) K N)
    (hl : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev (R := R) α p s h U (z.map (dbl.inl P)) = ev (R := R) β p s h U (z.map (dbl.inl P)))
    (hr : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev (R := R) α p s h U (z.map (dbl.inr P)) = ev (R := R) β p s h U (z.map (dbl.inr P))) : α = β :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 α β fun p s h U w => by
    rcases (UpperTheory.doubleMappingCylinder_cochain_extension R P).1 p U w with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact hl p s h U z
    · exact hr p s h U z

private theorem map_map {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    (x.map f).map g = x.map (f ≫ g) := rfl

private theorem map_id {E : Spc} {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) : x.map (𝟙 E) = x := rfl

private theorem van_img (P : Arrow Spc) {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj (dbl P)) K n)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev (R := R) α p s h U (z.map (dbl.inr P)) = 0)
    (p : ℕ) (s : ℤ) (h' : -(p : ℤ) + n = s) (U : Scheme.{0}) (z : Sx P.right p U)
    (hz : (Sub.img P.hom).mem p U z) : ev (R := R) α p s h' U (z.map (dbl.inl P)) = 0 := by
  obtain ⟨y, rfl⟩ := hz
  have e : (y.map P.hom).map (dbl.inl P) = (y.map P.hom).map (dbl.inr P) := by
    rw [map_map, map_map]
    exact congrArg (fun f => Sx.map f y) (pushout.condition : P.hom ≫ pushout.inl P.hom P.hom = P.hom ≫ pushout.inr P.hom P.hom)
  rw [e]
  exact h p s h' U _

private theorem pb_fold (P : Arrow Spc) {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj P.right) K n) :
    pb (dbl.inr P) (pb (dbl.fold P) α) = α :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p s h U x => by
    rw [ev_pb, ev_pb, map_map, dbl.inr_fold, map_id]

private theorem comp_eq {E E' : Spc} {j : E ⟶ E'} {Z : Sub E} {K : Cx R} {m N : ℤ}
    {γ γ' : Cochain ((chains R).obj E') K N} {x : (famDC Z K m).Tot} (h : Comp j γ x) (h' : Comp j γ' x)
    (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx E p U) :
    ev (R := R) γ p s hs U (z.map j) = ev (R := R) γ' p s hs U (z.map j) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + m := ⟨s - m, by omega⟩
  exact (h p t hs U z).symm.trans (h' p t hs U z)

private theorem comp_zero {E E' : Spc} (j : E ⟶ E') (Z : Sub E) (K : Cx R) (m N : ℤ) :
    Comp j (0 : Cochain ((chains R).obj E') K N) (0 : (famDC Z K m).Tot) := by
  intro p s h U z
  exact (ev_zero p _ h U (z.map j)).symm

private theorem pull_inr (q : ℕ) (P : Arrow Spc) (i N : ℤ) (g : Cocycle ((chains (ZMod q)).obj (dbl P)) (res _ (tw q i)) N)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev (R := ZMod q) g.1 p s h U (z.map (dbl.inr P)) = 0) :
    pull _ (dbl.inr P) (tw q i) N (CohomologyClass.mk g) = 0 := by
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (dbl.inr P))) g (zero_add N)) = 0
  have e : zcomp (Cocycle.ofHom ((chains (ZMod q)).map (dbl.inr P))) g (zero_add N) = 0 :=
    Cocycle.ext (pb_eq_zero _ _ h)
  rw [e, CohomologyClass.mk_zero]

end UpperTheory.VanishingEvaluation

open UpperTheory.VanishingEvaluation in
theorem UpperTheory.relativeCohomology_isTotalModel_of_image :
    ∀ (q : ℕ) (P : Arrow Spc) (i m n N : ℤ), n + m = N → TModel (famDC (Sub.img P.hom) (res _ (tw q i)) m) n (fun x (c : Hs q P N i) => SRel (N := N) x c.1) := by
  intro q P i m n N hN
  have C := fun n N h => UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain (ZMod q) (dbl.inl P) (Sub.img P.hom) (res _ (tw q i)) m n N h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hD
    obtain ⟨γ, hγ, hv⟩ := (UpperTheory.doubleMappingCylinder_cochain_extension (ZMod q) P).2 (res _ (tw q i)) m N x
    have h0 : δ N (N + 1) γ = 0 := by
      have hc := (C n N hN).2.2.1 γ x hγ
      rw [hD] at hc
      refine dbl_ext P _ _ (comp_eq hc (comp_zero _ _ _ _ _)) fun p s h U z => ?_
      rw [δ_van _ _ _ hv, ev_zero]
    refine ⟨⟨CohomologyClass.mk (Cocycle.mk γ (N + 1) rfl h0), ?_⟩, Cocycle.mk γ (N + 1) rfl h0, rfl, hγ, hv⟩
    exact pull_inr q P i N _ hv
  · rintro ⟨c, hc⟩
    obtain ⟨g₀, rfl⟩ := CohomologyClass.mk_surjective c
    have hc' : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (dbl.inr P))) g₀ (zero_add N)) = 0 := hc
    rw [CohomologyClass.mk_eq_zero_iff] at hc'
    obtain ⟨N', hN', β, hβ⟩ := hc'
    have hβ' : δ N' N β = pb (dbl.inr P) g₀.1 := hβ
    let e : Cocycle ((chains (ZMod q)).obj (dbl P)) (res _ (tw q i)) N :=
      Cocycle.mk (δ N' N (pb (dbl.fold P) β)) (N + 1) rfl (δ_δ _ _ _ _)
    have he : CohomologyClass.mk e = 0 := by
      rw [CohomologyClass.mk_eq_zero_iff]
      exact ⟨N', hN', _, rfl⟩
    have hm : CohomologyClass.mk (g₀ - e) = CohomologyClass.mk g₀ := by
      rw [CohomologyClass.mk_sub, he, sub_zero]
    have hp : pb (dbl.inr P) (g₀ - e).1 = 0 := by
      change pb (dbl.inr P) (g₀.1 - δ N' N (pb (dbl.fold P) β)) = 0
      rw [pb_sub, ← δ_pb, pb_fold, hβ', sub_self]
    have hv : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
        ev (R := ZMod q) (g₀ - e).1 p s h U (z.map (dbl.inr P)) = 0 := fun p s h U z => by
      rw [← ev_pb, hp, ev_zero]
    obtain ⟨x, hd, hx⟩ := (C n N hN).1 (g₀ - e).1 (van_img P _ hv)
    refine ⟨x, hd, ?_, g₀ - e, hm, hx, hv⟩
    refine (C (n + 1) (N + 1) (by omega)).2.1 (δ N (N + 1) (g₀ - e).1) _ 0 ((C n N hN).2.2.2.2 x hd)
      (fun _ _ _ => rfl) ((C n N hN).2.2.1 _ x hx) ?_
    rw [(g₀ - e).δ_eq_zero]
    exact comp_zero _ _ _ _ _
  · rintro x c x' c' ⟨g, hg, hc, hv⟩ ⟨g', hg', hc', hv'⟩
    refine ⟨g - g', ?_, (C n N hN).2.2.2.1 _ _ _ _ hc hc', fun p s h U z => ?_⟩
    · rw [CohomologyClass.mk_sub, hg, hg']; rfl
    · have := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 g.1 g'.1 p s h U (z.map (dbl.inr P))).2.1
      rw [hv, hv', sub_zero] at this
      exact this
  · rintro x c hd ⟨g, hg, hc, hv⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have hN' : n' + m = N' := by omega
    simp only [add_sub_cancel_right]
    constructor
    · intro h0
      have hz : CohomologyClass.mk g = 0 := by rw [hg, h0]; rfl
      rw [CohomologyClass.mk_eq_zero_iff] at hz
      obtain ⟨M, hM, β, hβ⟩ := hz
      obtain rfl : M = N' := by omega
      have hβ' : δ M (M + 1) β = g.1 := hβ
      have hp : pb (dbl.inr P) g.1 = 0 := pb_eq_zero _ _ hv
      have hb : δ M (M + 1) (β - pb (dbl.fold P) (pb (dbl.inr P) β)) = g.1 := by
        rw [δ_sub, δ_pb, δ_pb, hβ', hp]
        simp
      have hp' : pb (dbl.inr P) (β - pb (dbl.fold P) (pb (dbl.inr P) β)) = 0 := by
        rw [pb_sub, pb_fold, sub_self]
      have hv' : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + M = s) (U : Scheme.{0}) (z : Sx P.right p U),
          ev (R := ZMod q) (β - pb (dbl.fold P) (pb (dbl.inr P) β)) p s h U (z.map (dbl.inr P)) = 0 := fun p s h U z => by
        rw [← ev_pb, hp', ev_zero]
      obtain ⟨y, hy, hcy⟩ := (C n' M hN').1 _ (van_img P _ hv')
      refine ⟨y, hy, ?_⟩
      have h1 := (C n' M hN').2.2.1 _ y hcy
      rw [hb] at h1
      exact (C (n' + 1) (M + 1) (by omega)).2.1 g.1 _ x ((C n' M hN').2.2.2.2 y hy) hd h1 hc
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨β, hβ, hvβ⟩ := (UpperTheory.doubleMappingCylinder_cochain_extension (ZMod q) P).2 (res _ (tw q i)) m N' y
      have e : g.1 = δ N' (N' + 1) β :=
        dbl_ext P _ _ (comp_eq hc ((C n' N' hN').2.2.1 β y hβ)) fun p s h U z => by
          rw [hv, δ_van _ _ _ hvβ]
      apply Subtype.ext
      change c.1 = 0
      rw [← hg, CohomologyClass.mk_eq_zero_iff]
      exact ⟨N', rfl, β, e.symm⟩
end

section

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private lemma UpperTheory.exists_finite_span_kummerSelmer_representatives.divisor_pow' {k K : Type} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]
    {x : K} (hx : x ≠ 0) (n : ℕ) : divisor (x ^ n) = n • (divisor x : Divisor k K) := by
  induction n with
  | zero => simp [divisor_one]
  | succ n ih => rw [pow_succ, divisor_mul (pow_ne_zero _ hx) hx, ih, succ_nsmul]

theorem UpperTheory.exists_finite_span_kummerSelmer_representatives :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [IsFunctionField k K] (q : ℕ) [NeZero q], ∃ (n : ℕ) (v : Fin n → K), ∀ f ∈ SelAll k K q, ∃ g ∈ SelAll k K q, (∃ c : Fin n → k, (g : K) = ∑ i, c i • v i) ∧ ∃ u : Kˣ, f = g * u ^ q := by
  intro k K _ _ _ _ _ q _
  obtain ⟨x, hxt, hfd⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have hd : 0 < Module.finrank (IntermediateField.adjoin k ({x} : Set K)) K := Module.finrank_pos
  obtain ⟨γ, hγ⟩ := Divisor.exists_bound_deg_sub_finrank_L (k := k) (K := K)
  set n := γ.toNat + 1
  set E : Divisor k K := n • poleDivisor x with hE
  have hdegE : (n : ℤ) ≤ Divisor.deg E := by
    rw [hE, map_nsmul, Divisor.deg_poleDivisor hxt, nsmul_eq_mul]
    nlinarith
  set V := (q • E).L with hV
  let b := Module.finBasis k V
  refine ⟨Module.finrank k V, fun i => (b i : K), ?_⟩
  intro f hf
  have hf' : ∀ w : Place k K, (q : ℤ) ∣ w.ord (f : K) := hf
  have hq : (q : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  let D : Divisor k K := Finsupp.mapRange (fun z : ℤ => z / (q : ℤ)) (by simp) (divisor (f : K))
  have hD : divisor (f : K) = q • D := by
    ext w
    simp only [D, Finsupp.smul_apply, Finsupp.mapRange_apply, nsmul_eq_mul]
    rw [Int.mul_ediv_cancel', divisor_apply]
    rw [divisor_apply]
    exact hf' w
  have hdegD : Divisor.deg D = 0 := by
    have h0 := Divisor.deg_divisor (k := k) (f : K)
    rw [hD, map_nsmul, nsmul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hq
    · exact h
  have hri := hγ (D + E)
  rw [map_add (f := _), hdegD, zero_add] at hri
  have hn : γ < (n : ℤ) := by
    dsimp [n]
    by_cases h : 0 ≤ γ
    · rw [Int.toNat_of_nonneg h]
      omega
    · have : (0 : ℤ) ≤ (γ.toNat : ℤ) := by positivity
      omega
  have hpos : 0 < Module.finrank k (D + E).L := by omega
  obtain ⟨⟨h, hmem⟩, hne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hh : h ≠ 0 := fun h0 => hne (Subtype.ext h0)
  have hle := (Divisor.mem_L_iff_le hh).mp hmem
  let u : Kˣ := Units.mk0 h hh
  have hval : ((f * u ^ q : Kˣ) : K) = (f : K) * h ^ q := by simp [u]
  have hgne : ((f * u ^ q : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hgdiv : divisor ((f * u ^ q : Kˣ) : K) = q • (D + divisor h) := by
    rw [hval, divisor_mul f.ne_zero (pow_ne_zero _ hh), UpperTheory.exists_finite_span_kummerSelmer_representatives.divisor_pow' hh, hD, smul_add]
  have hgV : ((f * u ^ q : Kˣ) : K) ∈ V := by
    rw [hV, Divisor.mem_L_iff_le hgne, hgdiv, ← smul_add]
    have h3 : D + divisor h + E = divisor h + (D + E) := by abel
    rw [h3]
    exact nsmul_nonneg hle q
  refine ⟨f * u ^ q, ?_, ?_, u⁻¹, by group⟩
  · intro w
    rw [← divisor_apply, hgdiv, Finsupp.smul_apply, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  · refine ⟨fun i => b.repr ⟨_, hgV⟩ i, ?_⟩
    have hs := b.sum_repr ⟨_, hgV⟩
    have hs' := congrArg Subtype.val hs
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hs'
    exact hs'.symm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4


theorem UpperTheory.mem_range_of_proper_generic_fibre_separated :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω], Function.Injective (algebraMap R Ω) → ∀ {B Y D C : Scheme.{0}} (ι : Sp R ⟶ B) [IsOpenImmersion ι] (π : Y ⟶ B) [IsSeparated π] [IrreducibleSpace Y] (j : D ⟶ Y) [IsOpenImmersion j], Dense (Set.range j) → ∀ (q : D ⟶ Sp R), j ≫ π = q ≫ ι → ∀ (c : C ⟶ Sp Ω) [IsProper c] (v : C ⟶ D), IsPullback v c q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) → ∀ (y : Y), π y ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) → y ∈ Set.range j := by
  intro R Ω _ _ _ _ hinj B Y D C ι _ π _ _ j _ hd q hq c _ v hpb y hy
  set g := Spec.map (CommRingCat.ofHom (algebraMap R Ω)) with hg
  let U' : Y.Opens := π ⁻¹ᵁ ι.opensRange
  have hjU : Set.range j ⊆ Set.range U'.ι := by
    rintro _ ⟨d, rfl⟩
    rw [Scheme.Opens.range_ι]
    show π (j d) ∈ ι.opensRange
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let jU : D ⟶ U' := IsOpenImmersion.lift U'.ι j hjU
  have hjUf : jU ≫ U'.ι = j := IsOpenImmersion.lift_fac _ _ _
  have hπU : Set.range (U'.ι ≫ π) ⊆ Set.range ι := by
    rintro _ ⟨z, rfl⟩
    exact z.2
  let w : (U' : Scheme) ⟶ Sp R := IsOpenImmersion.lift ι (U'.ι ≫ π) hπU
  have hw : w ≫ ι = U'.ι ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hjw : jU ≫ w = q := by
    rw [← cancel_mono ι, Category.assoc, hw, ← Category.assoc, hjUf, hq]
  haveI : IsSeparated (w ≫ ι) := by rw [hw]; infer_instance
  haveI : IsSeparated w := IsSeparated.of_comp w ι
  let m : C ⟶ pullback w g := pullback.lift (v ≫ jU) c (by rw [Category.assoc, hjw, hpb.w])
  have hm : m ≫ pullback.snd w g = c := pullback.lift_snd _ _ _
  haveI : UniversallyClosed (m ≫ pullback.snd w g) := by rw [hm]; infer_instance
  haveI : UniversallyClosed m := UniversallyClosed.of_comp_of_isSeparated m (pullback.snd w g)
  have hleft : IsPullback m v (pullback.fst w g) jU := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback w g).flip
    rw [hm, hjw]
    exact hpb.flip
  have hI : hleft.isoPullback.inv ≫ m = pullback.fst (pullback.fst w g) jU :=
    (Iso.inv_comp_eq _).mpr hleft.isoPullback_hom_fst.symm
  have hrange : (pullback.fst w g) ⁻¹' Set.range jU ⊆ Set.range m := by
    intro z hz
    have e := IsOpenImmersion.range_pullbackFst jU (pullback.fst w g)
    have hz' : z ∈ Set.range (pullback.fst (pullback.fst w g) jU) := by
      rw [e]
      exact hz
    obtain ⟨t, rfl⟩ := hz'
    refine ⟨hleft.isoPullback.inv t, ?_⟩
    rw [← Scheme.Hom.comp_apply, hI]
  obtain ⟨p, hp⟩ := hy
  have hyU : y ∈ U' := by
    show π y ∈ ι.opensRange
    rw [← hp, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let yU : U' := ⟨y, hyU⟩
  have e1 : ι (w yU) = π y := by
    show (w ≫ ι) yU = π y
    rw [hw]
    rfl
  have hwy : w yU = g p := by
    apply ι.isOpenEmbedding.injective
    rw [e1, ← hp]
    rfl
  obtain ⟨y', hy'1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := w) (g := g) yU p hwy
  have hξ : genericPoint Y ∈ Set.range j := by
    rw [(genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range, Set.univ_inter]
    exact hd.nonempty
  obtain ⟨d, hdξ⟩ := hξ
  have hsp : jU d ⤳ yU := by
    apply (U'.ι.isOpenEmbedding.isInducing.specializes_iff).mp
    have e2 : U'.ι (jU d) = genericPoint Y := by
      rw [← Scheme.Hom.comp_apply, hjUf, hdξ]
    rw [e2]
    exact (genericPoint_spec Y).specializes (Set.mem_univ _)
  obtain ⟨x', hx'sp, hx'fst⟩ := UpperTheory.exists_specializes_lift_generic_base_change R Ω hinj w y' (jU d) (by rw [hy'1]; exact hsp)
  have hx'm : x' ∈ Set.range m := hrange ⟨d, hx'fst.symm⟩
  have hy'm : y' ∈ Set.range m := hx'sp.mem_closed m.isClosedMap.isClosed_range hx'm
  obtain ⟨c0, hc0⟩ := hy'm
  refine ⟨v c0, ?_⟩
  have h1 : pullback.fst w g (m c0) = jU (v c0) := by
    rw [← Scheme.Hom.comp_apply, hleft.w, Scheme.Hom.comp_apply]
  rw [← hjUf, Scheme.Hom.comp_apply, ← h1, hc0, hy'1]
  rfl
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

theorem UpperTheory.isFinite_fromNormalization_of_perfectField :
    ∀ (k : Type) [Field k] [PerfectField k] {D T : Scheme.{0}} (t : T ⟶ Sp k) [LocallyOfFiniteType t] (f : D ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f] [IsIntegral D], IsFinite f.fromNormalization := by
  intro k _ _ D T t _ f _ _ _ _
  rw [isFinite_iff]
  refine ⟨inferInstance, fun U hU => ?_⟩
  rw [f.fromNormalization_app hU]
  letI := (f.app U).hom.toAlgebra
  have h : Module.Finite Γ(T, U) (integralClosure Γ(T, U) Γ(D, f ⁻¹ᵁ U)) := by
    rcases (f ⁻¹ᵁ U).1.eq_empty_or_nonempty with hE | hN
    · have hb : f ⁻¹ᵁ U = ⊥ := SetLike.ext' hE
      haveI : Subsingleton Γ(D, f ⁻¹ᵁ U) :=
        CommRingCat.subsingleton_of_isTerminal (D.sheaf.isTerminalOfEqEmpty hb)
      infer_instance
    · obtain ⟨x, hx⟩ := hN
      obtain ⟨V, hV, hxV, hVle⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp D.isBasis_affineOpens) hx
      haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
      haveI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, hx⟩⟩
      have hkt : (t.appLE ⊤ U (by simp)).hom.FiniteType :=
        LocallyOfFiniteType.finiteType_appLE t (isAffineOpen_top _) hU (by simp)
      let kA : k →+* Γ(T, U) :=
        (t.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      have hkA : kA.FiniteType :=
        hkt.comp (RingHom.FiniteType.of_surjective _
          (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
      letI : Algebra k Γ(T, U) := kA.toAlgebra
      haveI : Algebra.FiniteType k Γ(T, U) := hkA
      haveI : IsNoetherianRing Γ(T, U) := Algebra.FiniteType.isNoetherianRing k Γ(T, U)
      have heq : (D.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom =
          (D.germToFunctionField V).hom.comp (f.appLE U V hVle).hom := by
        rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
        congr 1
        simp [Scheme.Hom.appLE]
      let φ : Γ(T, U) →+* D.functionField :=
        (D.germToFunctionField V).hom.comp (f.appLE U V hVle).hom
      letI : Algebra Γ(T, U) D.functionField := φ.toAlgebra
      have h1 : (D.germToFunctionField V).hom.EssFiniteType := GlobalTheory.essFiniteType_germ hV _ _
      have h2 : (f.appLE U V hVle).hom.EssFiniteType :=
        (LocallyOfFiniteType.finiteType_appLE f hU hV hVle).essFiniteType
      haveI : Algebra.EssFiniteType Γ(T, U) D.functionField := h2.comp h1
      haveI := UpperTheory.module_finite_integralClosure_of_finiteType_perfect k Γ(T, U) D.functionField
      let ψ : Γ(D, f ⁻¹ᵁ U) →ₐ[Γ(T, U)] D.functionField :=
        { (D.germToFunctionField (f ⁻¹ᵁ U)).hom with
          commutes' := fun a => by
            change (D.germToFunctionField (f ⁻¹ᵁ U)).hom ((f.app U).hom a) = φ a
            exact congrArg (fun g => g a) heq }
      exact GlobalTheory.finite_integralClosure_of_family (ι := Unit) (L := fun _ => D.functionField)
        (fun _ => ψ) (fun b hb => D.germToFunctionField_injective (f ⁻¹ᵁ U)
          (by rw [map_zero]; exact hb ()))
  rw [CommRingCat.hom_comp]
  refine RingHom.Finite.comp ?_ ?_
  · exact RingHom.Finite.of_surjective _
      (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.symm.surjective
  · exact (RingHom.finite_algebraMap).mpr h
end
