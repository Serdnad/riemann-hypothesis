module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open scoped TensorProduct
open GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.UPel.HT

namespace GlobalTheory.AdelicLimitCompactness

theorem exists_limit_compact (p : ℕ) (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] (c : ℕ → ℤ)
    (hc : ∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime (n * m) p → ∃ z : ℤ, c (n * m) = c n + n * z) :
    ∃ a : O, ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∃ b : O, a = (c n : O) + n * b := by
  let I := {n : ℕ // 0 < n ∧ Nat.Coprime n p}
  haveI : Nonempty I := ⟨⟨1, one_pos, Nat.coprime_one_left p⟩⟩
  let S : I → Set O := fun n => Set.range fun b : O => (c n.1 : O) + (n.1 : O) * b
  have hcomp : ∀ n, IsCompact (S n) := fun n => isCompact_range (by fun_prop)
  have hsub : ∀ (n k : I) (m : ℕ), 0 < m → k.1 = n.1 * m → S k ⊆ S n := by
    rintro n k m hm hk _ ⟨b, rfl⟩
    obtain ⟨z, hz⟩ := hc n.1 m n.2.1 hm (hk ▸ k.2.2)
    refine ⟨z + m * b, ?_⟩
    simp only [hk, hz]
    push_cast
    ring
  have hdir : Directed (fun x y => x ⊇ y) S := by
    intro n m
    refine ⟨⟨n.1 * m.1, Nat.mul_pos n.2.1 m.2.1, Nat.Coprime.mul_left n.2.2 m.2.2⟩, ?_, ?_⟩
    · exact hsub n _ m.1 m.2.1 rfl
    · exact hsub m _ n.1 n.2.1 (mul_comm _ _)
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hdir
    (fun n => Set.range_nonempty _) hcomp (fun n => (hcomp n).isClosed)
  refine ⟨a, fun n hn hp => ?_⟩
  obtain ⟨b, hb⟩ := Set.mem_iInter.1 ha ⟨n, hn, hp⟩
  exact ⟨b, hb.symm⟩

theorem compactSpace_integers {R : Type} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]
    [IsDedekindDomain R] [IsFractionRing R ℚ] (v : HeightOneSpectrum R) :
    CompactSpace (v.adicCompletionIntegers ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm.compactSpace

variable {p : ℕ}

def ofInt (x : ∀ v : AwayP p, v.1.adicCompletionIntegers ℚ) : AfP p :=
  RestrictedProduct.mk (fun v => (x v : v.1.adicCompletion ℚ)) (Filter.Eventually.of_forall fun v => (x v).2)

theorem eval_ofInt (x : ∀ v : AwayP p, v.1.adicCompletionIntegers ℚ) (v : AwayP p) :
    AfP.eval v (ofInt x) = x v := rfl

theorem isInt_ofInt (x : ∀ v : AwayP p, v.1.adicCompletionIntegers ℚ) : IsIntAf (ofInt x) :=
  fun v => (x v).2

theorem afp_ext {a b : AfP p} (h : ∀ v, AfP.eval v a = AfP.eval v b) : a = b :=
  RestrictedProduct.ext _ _ h

theorem exists_limit_adele (c : ℕ → ℤ)
    (hc : ∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime (n * m) p → ∃ z : ℤ, c (n * m) = c n + n * z) :
    ∃ a : AfP p, ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∃ b : AfP p, IsIntAf b ∧ a = (c n : AfP p) + n * b := by
  have h : ∀ v : AwayP p, ∃ a : v.1.adicCompletionIntegers ℚ, ∀ n : ℕ, 0 < n → Nat.Coprime n p →
      ∃ b : v.1.adicCompletionIntegers ℚ, a = (c n : v.1.adicCompletionIntegers ℚ) + n * b := fun v =>
    haveI := compactSpace_integers v.1
    exists_limit_compact p _ c hc
  choose a ha using h
  refine ⟨ofInt a, fun n hn hp => ?_⟩
  choose b hb using fun v => ha v n hn hp
  refine ⟨ofInt b, isInt_ofInt b, afp_ext fun v => ?_⟩
  rw [map_add (f := _), map_mul, map_intCast, map_natCast, eval_ofInt, eval_ofInt, hb v]
  push_cast
  rfl

variable [Fact p.Prime] (D : Datum p)

def inHom : D.La →+ AfP p ⊗[ℚ] VQ D where
  toFun := inAf D
  map_zero' := by simp [inAf]
  map_add' x y := by simp [inAf, TensorProduct.tmul_add]

theorem smul_inAf (a : AfP p) (x : D.La) : a • inAf D x = a ⊗ₜ ((1 : ℚ) ⊗ₜ x) := by
  rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem smul_inAf_mem {a : AfP p} (ha : IsIntAf a) (x : D.La) : a • inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨a, x, ha, smul_inAf D a x⟩

theorem smul_mem {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', x, ha', rfl⟩ := hz
    rw [← smul_inAf, smul_smul]
    exact smul_inAf_mem D (fun v => by rw [map_mul]; exact mul_mem (ha v) (ha' v)) x
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_adelic_limit (g : ℕ → D.La →+ D.La)
    (hg : ∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime (n * m) p → ∀ x : D.La, ∃ z : D.La, g (n * m) x = g n x + n • z) :
    ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧
      ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∀ x : D.La, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w := by
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let B := Algebra.TensorProduct.basis (AfP p) (Algebra.TensorProduct.basis ℚ b)
  have hB : ∀ i, B i = inAf D (b i) := fun i => by
    simp only [B, Algebra.TensorProduct.basis_apply, inAf]
  have hlim := fun i j => exists_limit_adele (p := p) (fun n => b.repr (g n (b i)) j) (by
    intro n m hn hm hp
    obtain ⟨z, hz⟩ := hg n m hn hm hp (b i)
    exact ⟨b.repr z j, by simp [hz]⟩)
  choose a ha using hlim
  let h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := B.constr (AfP p) fun i => ∑ j, a i j • inAf D (b j)
  have h₀b : ∀ i, h₀ (inAf D (b i)) = ∑ j, a i j • inAf D (b j) := fun i => by
    rw [← hB]; exact B.constr_basis _ _ i
  have key : ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∀ x : D.La,
      ∃ w ∈ LaHat D, h₀ (inHom D x) = inHom D (g n x) + n • w := by
    intro n hn hp x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := b.mem_span x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      choose e he he' using fun j => ha i j n hn hp
      refine ⟨∑ j, e j • inAf D (b j), sum_mem fun j _ => smul_inAf_mem D (he j) _, ?_⟩

      conv_rhs => rw [← b.sum_repr (g n (b i)), map_sum]
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine (h₀b i).trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [he' j, map_zsmul, add_smul, mul_smul, Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul]
      rfl
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw, e⟩ := hx
      obtain ⟨w', hw', e'⟩ := hy
      refine ⟨w + w', add_mem hw hw', ?_⟩
      rw [map_add (f := _), map_add (f := _), e, e', map_add (f := _), map_add (f := _), nsmul_add]
      abel
    | smul k x _ hx =>
      obtain ⟨w, hw, e⟩ := hx
      refine ⟨k • w, zsmul_mem hw k, ?_⟩
      rw [map_zsmul, map_zsmul, e, map_zsmul, map_zsmul, zsmul_add, smul_comm k n w]
  refine ⟨h₀, fun v hv => ?_, key⟩
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', x, ha', rfl⟩ := hz
    obtain ⟨w, hw, e⟩ := key 1 one_pos (Nat.coprime_one_left p) x
    rw [← smul_inAf, map_smul]
    change a' • h₀ (inHom D x) ∈ _
    rw [e, smul_add, one_nsmul]
    exact add_mem (smul_inAf_mem D ha' _) (smul_mem D ha' hw)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem main : ∀ (p : ℕ) [Fact (Nat.Prime p)] (D : Datum p) (g : ℕ → D.La →+ D.La),
    (∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime (n * m) p → ∀ x : D.La, ∃ z : D.La, g (n * m) x = g n x + n • z) →
    ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧
      ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∀ x : D.La, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w :=
  fun _ _ D g hg => exists_adelic_limit D g hg

end GlobalTheory.AdelicLimitCompactness
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ModifLift

theorem spMap_fst_surjective_sqZero (K : Type) [Field K] (ι : Type) :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom) := by
  intro p
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change x.fst ∈ (⊥ : Ideal K) ↔ x ∈ PrimeSpectrum.asIdeal p
  rw [Ideal.mem_bot]
  constructor
  · intro hx
    apply p.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two, show x = TrivSqZeroExt.inr x.snd from TrivSqZeroExt.ext hx rfl,
        TrivSqZeroExt.inr_mul_inr]
    rw [this]
    exact Ideal.zero_mem _
  · intro hx
    by_contra h0
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)

theorem exists_lift_sqZero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
    (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] {ι : Type} (z : Sp K ⟶ M.X)
    (hz : ⊤ ≤ z ⁻¹ᵁ M.off) (w : Sp (TrivSqZeroExt K (ι → K)) ⟶ X.YY)
    (hw : spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w = z ≫ toFlag M) :
    ∃ w' : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, w' ≫ toFlag M = w ∧
      spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w' = z ∧
      ∀ O : M.X.Opens, ⊤ ≤ z ⁻¹ᵁ O → ⊤ ≤ w' ⁻¹ᵁ O := by
  set f := spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom with hf
  have hs := spMap_fst_surjective_sqZero K ι
  have hr : Set.range w ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := hs t
    refine ⟨M.σ (z s), ?_⟩
    change (z ≫ M.σ ≫ inc₀ X Z) s = (f ≫ w) s
    rw [hw]
  set w₀ := IsOpenImmersion.lift (inc₀ X Z) w hr with hw₀
  have hw₀f : w₀ ≫ inc₀ X Z = w := IsOpenImmersion.lift_fac _ _ _
  have hfw₀ : f ≫ w₀ = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw₀f, hw, Category.assoc]
  have hzU : ∀ s, M.σ (z s) ∈ U₀ X Z := fun s => by
    have := hz (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hU : ⊤ ≤ w₀ ⁻¹ᵁ U₀ X Z := by
    intro t _
    obtain ⟨s, rfl⟩ := hs t
    change (f ≫ w₀) s ∈ U₀ X Z
    rw [hfw₀]
    exact hzU s
  obtain ⟨w', hw', -⟩ := M.existsUnique_lift w₀ hU
  have hU' : ⊤ ≤ (f ≫ w₀) ⁻¹ᵁ U₀ X Z := fun s _ => hU (Set.mem_univ (f s))
  have hfw' : f ≫ w' = z := by
    obtain ⟨_, -, huniq⟩ := M.existsUnique_lift (f ≫ w₀) hU'
    exact (huniq _ (show (f ≫ w') ≫ M.σ = f ≫ w₀ by rw [Category.assoc, hw'])).trans (huniq z hfw₀.symm).symm
  refine ⟨w', ?_, hfw', fun O hO t _ => ?_⟩
  · rw [toFlag, ← Category.assoc, hw', hw₀f]
  · obtain ⟨s, rfl⟩ := hs t
    change (f ≫ w') s ∈ O
    rw [hfw']
    exact hO (Set.mem_univ s)

end GlobalTheory.ModifLift
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.TopForm GlobalTheory.Adelic GlobalTheory.TangentOrigin
open GlobalTheory.FlagTan (IsDef)

theorem exists_isFreeGen_dForm {k A : Type} [CommRing k] [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) : ∃ f : Fin D → A, IsFreeGen A (dForm α f) := by
  classical
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨fun i => P.val (e.symm i), isFreeGen_dForm _ (P.basisKaehler.reindex e) fun i => by
    simp⟩

theorem exists_isFrame_dOn {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ)
    [SmoothOfRelativeDimension D p] (x : Y) :
    ∃ (U : Y.Opens) (f : Fin D → Γ(Y, U)), x ∈ U ∧ IsFrame (dOn p f) := by
  obtain ⟨V, hV, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top x)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), x ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  obtain ⟨f, hf⟩ := exists_isFreeGen_dForm h₂
  exact ⟨_, f, hxt, IsAffineOpen.basicOpen hV _, hf⟩

theorem primeSpectrum_dualNumber_eq {L : Type} [Field L] (x y : PrimeSpectrum (DualNumber L)) : x = y := by
  have h : ∀ z : PrimeSpectrum (DualNumber L), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem le_preimage_of_dualNumber {L : Type} [Field L] {T : Scheme.{0}} (φ : DualNumber L →+* L)
    (x : Sp (DualNumber L) ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) (IsLocalRing.closedPoint L) = s := primeSpectrum_dualNumber_eq _ _
  have h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint L) ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

theorem exists_tanLift {L : Type} [Field L] [Algebra c.F L] {Q : FrPt Xo c L} {v : FrPt Xo c (DualNumber L)}
    (hd : IsDef Q v) {z : Sp L ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) :
    ∃ zv : Sp (DualNumber L) ⟶ M.X, zv ≫ toFlag M = X.ptY v ∧ ∀ O : M.X.Opens, ⊤ ≤ z ⁻¹ᵁ O → ⊤ ≤ zv ⁻¹ᵁ O := by
  have e := (X.ptY_frMap hd).trans hz.symm
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY v ⁻¹ᵁ (inc₀ X Z).opensRange := le_preimage_of_dualNumber _ _ _ (by
    rw [e]
    rintro s -
    exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY v) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY v := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (GlobalTheory.FlagTan.red c L).toRingHom ≫ w = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]
  have hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := le_preimage_of_dualNumber _ _ _ (by rw [ered]; exact hU)
  obtain ⟨zv, hzv, -⟩ := M.existsUnique_lift w hwU
  have hred : spMap (GlobalTheory.FlagTan.red c L).toRingHom ≫ zv = z :=
    (M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl
  refine ⟨zv, ?_, fun O hO => le_preimage_of_dualNumber _ _ _ (by rw [hred]; exact hO)⟩
  rw [toFlag, ← Category.assoc, hzv, hw]

end GlobalTheory.CompHS
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod
open GlobalTheory.FlagTan (dimFlag)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem primeSpectrum_trivSqZeroExt_eq {L M : Type} [Field L] [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M]
    [IsCentralScalar L M] (x y : PrimeSpectrum (TrivSqZeroExt L M)) : x = y := by
  have h : ∀ z : PrimeSpectrum (TrivSqZeroExt L M), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem le_preimage_of_reduction {R L : Type} [CommRing R] [Field L] (hR : ∀ a b : PrimeSpectrum R, a = b)
    (φ : R →+* L) {T : Scheme.{0}} (x : Sp R ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) (IsLocalRing.closedPoint L) = s := hR _ _
  have h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint L) ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

theorem le_preimage_of_comp {R S : Type} [CommRing R] [CommRing S] (hR : ∀ a b : PrimeSpectrum R, a = b)
    (φ : R →+* S) (s₀ : Sp S) {T : Scheme.{0}} (x : Sp R ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) s₀ = s := hR _ _
  have h₁ : (spMap φ ≫ x) s₀ ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}

theorem exists_thickLift (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K]
    {ι : Type} [Fintype ι] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q)
    {W : FrPt Xo c (TrivSqZeroExt K (ι → K))} (hW : FrMap (TrivSqZeroExt.fstHom c.F K (ι → K)) W Q) :
    ∃ ZW : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, ZW ≫ toFlag M = X.ptY W ∧
      ∀ (m : ι → K) (x : Sp (DualNumber K) ⟶ M.X),
        x ≫ toFlag M = spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ X.ptY W →
          x = spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ ZW := by
  have hred : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X.ptY W = X.ptY Q := X.ptY_frMap hW
  have hpt : ∀ a b : PrimeSpectrum (TrivSqZeroExt K (ι → K)), a = b := primeSpectrum_trivSqZeroExt_eq
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY W ⁻¹ᵁ (inc₀ X Z).opensRange :=
    le_preimage_of_reduction hpt (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom _ _ (by
      rw [hred, ← hz]
      rintro s -
      exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY W) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, w₁ ≫ inc₀ X Z = X.ptY W := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ w₁ = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw₁, hred, ← hz, Category.assoc]
  have hwU : ⊤ ≤ w₁ ⁻¹ᵁ U₀ X Z := le_preimage_of_reduction hpt _ _ _ (by rw [ered]; exact hU)
  obtain ⟨ZW, hZW, -⟩ := M.existsUnique_lift w₁ hwU
  refine ⟨ZW, by rw [toFlag, ← Category.assoc, hZW, hw₁], fun m x hx => ?_⟩
  have hxU : ⊤ ≤ (spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ w₁) ⁻¹ᵁ U₀ X Z := fun s _ => hwU (Set.mem_univ _)
  refine (M.existsUnique_lift _ hxU).unique ?_ (by rw [Category.assoc, hZW])
  rw [← cancel_mono (inc₀ X Z), Category.assoc, Category.assoc, hw₁, ← hx]

theorem snd_evalPt_dir {K : Type} [Field K] [Algebra c.F K] {ι : Type} [Fintype ι] {T : Scheme.{0}}
    (ZW : Sp (TrivSqZeroExt K (ι → K)) ⟶ T) (O : T.Opens) (hO : ⊤ ≤ ZW ⁻¹ᵁ O) (m : ι → K)
    (x : Sp (DualNumber K) ⟶ T) (hx : ⊤ ≤ x ⁻¹ᵁ O) (e : x = spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ ZW) (g : Γ(T, O)) :
    (evalPt x O hx g).snd = ∑ k, (evalPt ZW O hO g).snd k * m k := by
  subst e
  rw [evalPt_spMap_comp (GlobalTheory.FlagTan.dir c m).toRingHom ZW O hO hx g]
  exact GlobalTheory.FlagTan.snd_dir m _

end GlobalTheory.CompHS
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

theorem _root_.GlobalTheory.T.weil_eigen_bijective_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ μ : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.EvalUnitUnconditional.exists_const | exact GlobalTheory.EvalUnitUnconditional.exists_const | (intros; apply GlobalTheory.EvalUnitUnconditional.exists_const <;> assumption)
end
