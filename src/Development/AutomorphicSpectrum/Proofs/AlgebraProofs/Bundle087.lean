module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle041
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XCkFlagSum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.dual_bundle_intersection : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N V₁), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → IsDualLat O x β E.lat F.lat → IsDualLat O x β E'.lat F'.lat → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N F F' k L Q = (-1) ^ k * ck O x d N E E' k L Q) ∧ ∀ (j : ℕ), j ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - j) → ∀ a : O, a ≠ 0 → rootNum O x d N F (psum (Fin N) ℤ j) L Q a = (-1) ^ j * rootNum O x d N E (psum (Fin N) ℤ j) L Q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_dual | exact GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_dual | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_dual <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.CkFlagSum

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (B B' : ChartBundle O (mseg x) N V), SameGeneric O x B B' → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ), IsFlagFrame x B w b → IsFlagFrame x B' w' b' → (∀ i j : Fin N, i < j → w.repr (w' i) j = 0) → ∀ A A' : Fin N → ChartBundle O (mseg x) 1 Ω, (∀ i, IsLine O x 1 (b i) (A i).lat ∧ IsLine O x (w.repr (w' i) i) (b' i) (A' i).lat) → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N B B' k L Q = ∑ i, ck O x d 1 (A i) (A' i) k L Q := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hM N V _ _ B B' hS w w' b b' hF hF' hw A A' hA k hk1 hk2 q L Q hQ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hK, hW⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
  have hW' : GroundTheory.Heights₂.Heights.NumbersDVR.IsModelOver (pointIdeal O x) d := hW
  obtain ⟨hG, f, g, hP⟩ :=
    GlobalTheory.T.same_generic_flag_comparison O Ω K ι x ϖ hϖ d hW' N V B B' hS w w' b b' hF hF' hw
  have h1 := (GlobalTheory.T.chern_class_on_flag_pair O ϖ hϖ Ω K ι x d hK hW' N V B B' hG w w' b b' f g hP).1 k hk1 hk2
    (psumExpansion N k) (isPairExpansion_psum N k) q L Q hQ
  have h2 : ∀ i, ck O x d 1 (A i) (A' i) k L Q = _ := fun i =>
    (GlobalTheory.T.line_bundle_model_degree O Ω K ι x ϖ hϖ d hM (A i) (A' i) 1 (w.repr (w' i) i) (b i) (b' i)
      (hA i).1 (hA i).2 (f i) (g i) (hP.vertical i)
      (by rw [mul_one, mul_comm]; exact hP.generic i)).2 k hk1 hk2 q L Q hQ
  refine h1.trans ?_
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [PositivityTheory.Xgn.A_ck_flag_sum.pairNum_psum, Finset.mul_sum]

end GlobalTheory.CompanionTheory.Ar.CkFlagSum
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.BiratJoin

theorem psum_homogeneous_int (σ : Type) [Fintype σ] (n : ℕ) :
    (psum σ ℤ n).IsHomogeneous n := by
  unfold psum
  apply IsHomogeneous.sum
  intro i _
  simpa using (isHomogeneous_X ℤ i).pow n

theorem ckRelations_descend : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {Sg : Type} {r s : Sg → ℕ} (p : ℕ), (p : O) ≠ 0 → ∀ (φ : Equiv.Perm Sg) {VL VO : Sg → Type} [∀ τ, AddCommGroup (VL τ)] [∀ τ, Module Ω (VL τ)] [∀ τ, AddCommGroup (VO τ)] [∀ τ, Module Ω (VO τ)] (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (VL τ)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (VO τ)), (∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ)) → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d → fnField O (joinCoord x z) = fnField O x → ∀ (Lie' W' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (r τ) (VL τ)) (Om' OmHT' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (s τ) (VO τ)), (∀ τ, IsPull O x z (Lie τ) (Lie' τ) ∧ IsPull O x z (W τ) (W' τ) ∧ IsPull O x z (Om τ) (Om' τ) ∧ IsPull O x z (OmHT τ) (OmHT' τ)) → CkRelations O (joinCoord x z) d p φ Lie' W' Om' OmHT' → CkRelations O x d p φ Lie W Om OmHT := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hx Sg r s p hp φ VL VO _ _ _ _ Lie W Om OmHT hsame K' _ _ ι' _ z hxz hfn
    Lie' W' Om' OmHT' hpull hck
  unfold CkRelations
  intro k hk1 hk2 q L Q hQ
  obtain ⟨h, hA, hB⟩ := hck k hk1 hk2 q (fun j => pullDeg (L j)) Q hQ
  have hc : k - 1 ≤ d := by omega
  have hQ' : Q.IsHomogeneous (d - (k - 1)) := by
    have e : d - (k - 1) = d + 1 - k := by omega
    rw [e]
    exact hQ
  have TL := fun τ => GlobalTheory.T.same_generic_base_extension O Ω K ι x d hx (r τ) (VL τ) (Lie τ) (W τ) (hsame τ).1 K' ι' z hxz hfn
    (Lie' τ) (W' τ) (hpull τ).1 (hpull τ).2.1
  have TO := fun τ => GlobalTheory.T.same_generic_base_extension O Ω K ι x d hx (s τ) (VO τ) (Om τ) (OmHT τ) (hsame τ).2 K' ι' z hxz hfn
    (Om' τ) (OmHT' τ) (hpull τ).2.2.1 (hpull τ).2.2.2
  have hroot : ∀ τ, rootNum O (joinCoord x z) d (r τ) (Lie' τ) (MvPolynomial.psum (Fin (r τ)) ℤ (k - 1))
      (fun j => pullDeg (L j)) Q (p : O) =
      rootNum O x d (r τ) (Lie τ) (MvPolynomial.psum (Fin (r τ)) ℤ (k - 1)) L Q (p : O) := fun τ =>
    (TL τ).2 (k - 1) _ (MvPolynomial.psum_isSymmetric _ _ _) (psum_homogeneous_int _ _) hc q L Q hQ' _ hp
  refine ⟨h, fun τ => ?_, fun τ => ?_⟩
  · rw [← (TL τ).1 k hk1 hk2 q L Q hQ, ← (TO τ).1 k hk1 hk2 q L Q hQ, ← hroot τ]
    exact hA τ
  · rw [← hroot (φ τ)]
    exact hB τ

end GlobalTheory.CompanionTheory.Ar.Num.BiratJoin
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.CkLinePow

section Lists

variable {K : Type*} {σ : Type*}

theorem headAdd_zsmul {A : List (K → ℤ) → ℤ} (hA : HeadAdd A) (m : ℤ) (u : K → ℤ)
    (l : List (K → ℤ)) : A ((m • u) :: l) = m * A (u :: l) := by
  let φ : (K → ℤ) →+ ℤ := AddMonoidHom.mk' (fun v => A (v :: l)) fun v w => hA v w l
  exact map_zsmul φ m u

theorem map_zsmul_append {A : List (K → ℤ) → ℤ} (hp : PermInv A) (hA : HeadAdd A) (m : ℤ)
    (l r : List (K → ℤ)) : A (l.map (m • ·) ++ r) = m ^ l.length * A (l ++ r) := by
  induction l generalizing r with
  | nil => simp
  | cons u l ih =>
    rw [List.map_cons, List.cons_append, headAdd_zsmul hA,
      hp _ _ (List.perm_middle (a := u) (l₁ := l.map (m • ·)) (l₂ := r)).symm, ih,
      hp _ _ (List.perm_middle (a := u) (l₁ := l) (l₂ := r)), List.length_cons, List.cons_append]
    ring

theorem length_classList (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {n : ℕ}
    (hH : H.IsHomogeneous n) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = n := by
  have h1 := hH (mem_support_iff.mp hμ)
  rw [← h1]
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset,
    Finsupp.weight_apply]
  simp [Finsupp.sum]

theorem polyVal_zsmul {A : List (K → ℤ) → ℤ} (hp : PermInv A) (hA : HeadAdd A) (m : ℤ)
    (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {n : ℕ} (hH : H.IsHomogeneous n) :
    polyVal A (fun s => m • cls s) H = m ^ n * polyVal A cls H := by
  unfold polyVal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hperm : (classList (fun s => m • cls s) μ).Perm ((classList cls μ).map (m • ·) ++ []) := by
    unfold classList
    rw [List.append_nil, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList,
      Multiset.coe_toList, Multiset.map_map]
    rfl
  rw [hp _ _ hperm, map_zsmul_append hp hA, length_classList cls hH hμ, List.append_nil]
  ring

end Lists

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem isVerticalDivisor_swap {P : Ideal (MRing ι O)} {ϖ : O} {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) : IsVerticalDivisor P ϖ (-b) g f := by
  refine {
    degrees := ?_
    num_not_mem := hD.den_not_mem
    den_not_mem := hD.num_not_mem
    vertical := ?_
    unit_off_special := ?_ }
  · obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine ⟨bg, bf, hg, hf, ?_⟩
    rw [← hb]
    funext k
    simp
  · intro W hW
    apply hD.vertical W
    intro h
    apply hW
    unfold ratDiv at h ⊢
    linarith
  · intro W hW hPW hrel hϖ
    obtain ⟨u, v, hu, hv, h⟩ := hD.unit_off_special W hW hPW hrel hϖ
    refine ⟨v, u, hv, hu, ?_⟩
    rw [← neg_sub]
    exact P.neg_mem h

theorem exists_zpow {Ω : Type} [Field Ω] (φ : MRing ι O →+* Ω) {P : Ideal (MRing ι O)} [P.IsPrime]
    {ϖ : O} {b : K → ℤ} {f g : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g) {u : Ω} (hu : u ≠ 0)
    (hfg : φ f * u = φ g) (m : ℤ) :
    ∃ F G : MRing ι O, IsVerticalDivisor P ϖ (m • b) F G ∧ φ F * u ^ m = φ G ∧
      ∀ W, ratDiv P F G W = m * ratDiv P f g W := by
  induction m using Int.induction_on with
  | zero =>
    refine ⟨1, 1, ?_, by simp, fun W => by simp [ratDiv]⟩
    rw [zero_smul]
    exact isVerticalDivisor_one ϖ P
  | succ n ih =>
    obtain ⟨F, G, hFG, hv, hr⟩ := ih
    refine ⟨F * f, G * g, ?_, ?_, fun W => ?_⟩
    · rw [add_smul, one_smul]
      exact isVerticalDivisor_mul hFG hD
    · rw [zpow_add_one₀ hu, map_mul, map_mul, ← hv, ← hfg]
      ring
    · rw [ratDiv_mul hFG.num_not_mem hFG.den_not_mem hD.num_not_mem hD.den_not_mem, Pi.add_apply,
        hr]
      ring
  | pred n ih =>
    obtain ⟨F, G, hFG, hv, hr⟩ := ih
    refine ⟨F * g, G * f, ?_, ?_, fun W => ?_⟩
    · rw [sub_smul, one_smul, sub_eq_add_neg]
      exact isVerticalDivisor_mul hFG (isVerticalDivisor_swap hD)
    · rw [zpow_sub_one₀ hu, map_mul, map_mul, ← hv, ← hfg]
      field_simp
    · rw [ratDiv_mul hFG.num_not_mem hFG.den_not_mem hD.den_not_mem hD.num_not_mem, Pi.add_apply,
        hr]
      unfold ratDiv
      ring

theorem pairNum_scale {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {d : ℕ}
    (hP : IsModelOver P d) {a b : K → ℤ} {f g F G : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) (m : ℤ) (hr : ∀ W, ratDiv P F G W = m * ratDiv P f g W)
    {k : ℕ} (hk : 1 ≤ k) {Q : List (K → ℤ)} (hQ : Q.length + k = d + 1) :
    pairNum P (fun _ : Fin 1 => m • a) (fun _ => 0) (fun _ => F) (fun _ => G)
        (psumExpansion 1 k) Q =
      m ^ k * pairNum P (fun _ : Fin 1 => a) (fun _ => 0) (fun _ => f) (fun _ => g)
        (psumExpansion 1 k) Q := by
  unfold pairNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hH := isHomogeneous_psumExpansion 1 k i
  have hn : k - 1 + Q.length = d := by omega
  have hcls : (Sum.elim (fun _ : Fin 1 => m • a) (fun _ : Fin 1 => (0 : K → ℤ))) =
      fun s => m • (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => (0 : K → ℤ))) s := by
    funext s
    cases s <;> simp
  unfold cycEval
  rw [mul_finsum]
  refine finsum_congr fun W => ?_
  beta_reduce
  rw [hr W]
  by_cases hW : ratDiv P f g W = 0
  · simp [hW]
  rw [classNum_eq_polyVal _ hH hn, classNum_eq_polyVal _ hH hn, hcls,
    polyVal_zsmul (listNum_perm W Q d) (listNum_headAdd IntNumAddFirst.full hϖ hP hD hW Q) m _ hH]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (A T Am : ChartBundle O (mseg x) 1 Ω) (u : Ω) (a : K → ℤ) (m : ℤ), u ≠ 0 → IsLine O x u a A.lat → IsLine O x 1 0 T.lat → SameGeneric O x A T → IsLine O x (u ^ m) (m • a) Am.lat → SameGeneric O x Am T ∧ ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d 1 Am T k L Q = m ^ k * ck O x d 1 A T k L Q := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hM A T Am u a m hu hA hT hS hAm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hW⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
  have hW' : GroundTheory.Heights₂.Heights.NumbersDVR.IsModelOver (pointIdeal O x) d := hW
  have hS' := (BundleExamples.sameGeneric_iff hϖ x A T).mp hS
  obtain ⟨f, g, hD, hfg⟩ := GlobalTheory.T.monomial_ratio_integral_model O Ω K ι x ϖ hϖ d hW' a 0 u⁻¹ (inv_ne_zero hu) (by
    intro s hs
    obtain ⟨h1, h2⟩ := hS' s hs
    constructor
    · obtain ⟨n, hn⟩ := h1 _ ((hA s hs _).2 ⟨1, one_mem _, rfl⟩)
      obtain ⟨r, hr, e⟩ := (hT s hs _).1 hn
      refine ⟨n, r, hr, ?_⟩
      rw [smul_eq_mul] at e
      apply mul_left_cancel₀ hu
      field_simp
      linear_combination e
    · obtain ⟨n, hn⟩ := h2 _ ((hT s hs _).2 ⟨1, one_mem _, rfl⟩)
      obtain ⟨r, hr, e⟩ := (hA s hs _).1 hn
      refine ⟨n, r, hr, ?_⟩
      rw [smul_eq_mul] at e
      apply mul_left_cancel₀ hu
      field_simp
      linear_combination e)
  have hfg' : aeval x f * u = aeval x g := by
    rw [hfg]
    field_simp
  have : (pointIdeal O x).IsPrime := hW'.multiProj.isPrime
  obtain ⟨F, G, hFG, hv, hr⟩ := exists_zpow
    (aeval x : MRing ι O →ₐ[O] Ω).toRingHom hD hu hfg' m
  have hFG' : IsVerticalDivisor (pointIdeal O x) ϖ (m • a - 0) F G := by
    simpa using hFG
  obtain ⟨hs1, h1⟩ := GlobalTheory.T.line_bundle_model_degree O Ω K ι x ϖ hϖ d hM Am T (u ^ m) 1 (m • a) 0 hAm hT F G hFG'
    (by rw [mul_one]; exact hv)
  obtain ⟨-, h2⟩ := GlobalTheory.T.line_bundle_model_degree O Ω K ι x ϖ hϖ d hM A T u 1 a 0 hA hT f g hD
    (by rw [mul_one]; exact hfg')
  refine ⟨hs1, fun k hk1 hk2 q L Q hQ => ?_⟩
  rw [h1 k hk1 hk2 q L Q hQ, h2 k hk1 hk2 q L Q hQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [pairNum_scale hϖ hW' hD m hr hk1
    (by rw [length_classList L hQ hμ]; omega)]
  ring

end GlobalTheory.CompanionTheory.Ar.CkLinePow
end
