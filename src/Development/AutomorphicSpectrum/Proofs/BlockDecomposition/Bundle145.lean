module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle008
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle129
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle131
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CxPairing
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CovEx

variable {O : Type} [CommRing O] {X : Scheme.{0}}

theorem strV_basicOpen (q : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) (f : Γ(X, V)) :
    strV q (X.basicOpen f) = (algebraMap Γ(X, V) Γ(X, X.basicOpen f)).comp (strV q V) := by
  rw [RingHom.algebraMap_toAlgebra]
  simp only [strV]
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]

theorem coord_basicOpen (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} (hV : IsAffineOpen V) (f : Γ(X, V)) {d : ℕ}
    (g : MvPolynomial (Fin d) O →+* Localization.Away f)
    (hg : g.comp MvPolynomial.C = (algebraMap Γ(X, V) (Localization.Away f)).comp (strV q V)) (he : g.Etale) :
    Nonempty (Coord q (X.basicOpen f) d) := by
  have := hV.isLocalization_basicOpen f
  let e := IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) Γ(X, X.basicOpen f)
  let G : MvPolynomial (Fin d) O →+* Γ(X, X.basicOpen f) := (e.toAlgHom.toRingHom).comp g
  have hG : (MvPolynomial.eval₂Hom (strV q (X.basicOpen f)) fun k => G (MvPolynomial.X k)) = G := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => by simp
    have h1 := RingHom.congr_fun hg r
    have h2 : G (MvPolynomial.C r) = e (g (MvPolynomial.C r)) := rfl
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, h2, strV_basicOpen]
    have h3 : g (MvPolynomial.C r) = algebraMap Γ(X, V) (Localization.Away f) (strV q V r) := h1
    rw [h3, AlgEquiv.commutes]
    rfl
  refine ⟨⟨hV.basicOpen f, fun k => G (MvPolynomial.X k), ?_⟩⟩
  rw [hG]
  exact RingHom.Etale.stableUnderComposition _ _ he (RingHom.Etale.of_bijective e.bijective)

theorem exists_basicOpen (Q : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hQ : RingHom.RespectsIso Q) (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} (hV : IsAffineOpen V)
    (h : RingHom.Locally Q (q.appLE ⊤ V le_top).hom) {x : X} (hx : x ∈ V) :
    ∃ f : Γ(X, V), x ∈ X.basicOpen f ∧ Q ((algebraMap Γ(X, V) (Localization.Away f)).comp (strV q V)) := by
  obtain ⟨s, hs, hl⟩ := h
  have hc : ⨆ f : s, X.basicOpen (U := V) f.1 = V := (hV.iSup_basicOpen_eq_self_iff (s := s)).2 hs
  obtain ⟨f, hf⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge hx)
  refine ⟨f.1, hf, ?_⟩
  exact hQ.2 _ (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv (hl f.1 f.2)

theorem inter_affine (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q] {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) :=
  isAffineHom_diagonal_iff.1 (inferInstance : IsAffineHom (Limits.pullback.diagonal q)) ⊤ (isAffineOpen_top _)
    _ le_top _ le_top hU hV

theorem cov_of_local (P : ℕ → Prop) (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q] [QuasiCompact q]
    (h : ∀ x : X, ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ P d ∧ Nonempty (Coord q V d)) :
    ∃ U : Cov q, ∀ α, P (U.d α) := by
  classical
  choose V d hx hP hc using h
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).2)
    fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩
  refine ⟨{ ι := t, U := fun a => V a.1, d := fun a => d a.1, c := fun a => (hc a.1).some, cover := ?_, inter := ?_ },
    fun a => hP a.1⟩
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ x))
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩
  · intro S hS
    induction hS using Finset.Nonempty.cons_induction with
    | singleton a => simpa using (hc a.1).some.affine
    | cons a s ha hs ih =>
      rw [Finset.cons_eq_insert, Finset.iInf_insert]
      exact inter_affine q (hc a.1).some.affine ih

theorem exists_cov : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q]
    [QuasiCompact q], (Smooth q → Nonempty (Cov q)) ∧
      ∀ d, SmoothOfRelativeDimension d q → ∃ U : Cov q, ∀ α, U.d α = d := by
  intro O _ X q _ _
  refine ⟨fun hs => ?_, fun d hd => ?_⟩
  · obtain ⟨U, -⟩ := cov_of_local (fun _ => True) q fun x => by
      obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
      have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ V le_top).hom :=
        RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hV le_top)
      obtain ⟨f, hf, hst⟩ := exists_basicOpen RingHom.IsStandardSmooth RingHom.isStandardSmooth_respectsIso q hV h hx
      obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
      exact ⟨_, n, hf, trivial, coord_basicOpen q hV f g hg he⟩
    exact ⟨U⟩
  · refine cov_of_local (fun n => n = d) q fun x => ?_
    obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
    have h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) (q.appLE ⊤ V le_top).hom :=
      HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) q hd ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    obtain ⟨f, hf, hst⟩ := exists_basicOpen (RingHom.IsStandardSmoothOfRelativeDimension d)
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso q hV h hx
    obtain ⟨g, hg, he⟩ := hst.exists_etale_mvPolynomial
    exact ⟨_, d, hf, rfl, coord_basicOpen q hV f g hg he⟩

end GlobalTheory.CompanionTheory.CovEx
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.CoordCard

theorem card_eq_of_etale {K L : Type} [Field K] [CommRing L] [Nontrivial L] [Algebra K L] {m n : ℕ}
    [Algebra (MvPolynomial (Fin m) K) L] [IsScalarTower K (MvPolynomial (Fin m) K) L]
    [Algebra.FormallyEtale (MvPolynomial (Fin m) K) L]
    [Algebra.IsStandardSmoothOfRelativeDimension n K L] : m = n := by
  let b := KaehlerDifferential.mvPolynomialBasis K (Fin m)
  let b' := (b.baseChange L).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial (Fin m) K) L)
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K) (S := L) n
  have h1 := b'.mk_eq_rank''
  rw [hr] at h1
  simpa using h1

theorem card_eq_of_away {K A L : Type} [Field K] [CommRing A] [CommRing L] [Nontrivial L] [Algebra A L] {m n : ℕ}
    (t : A) [IsLocalization.Away t L] (g : K →+* A) (φ : MvPolynomial (Fin m) K →+* A)
    (hφ : ∀ r, φ (MvPolynomial.C r) = g r) (hE : φ.Etale)
    (hf : RingHom.IsStandardSmoothOfRelativeDimension n ((algebraMap A L).comp g)) : m = n := by
  letI iPA : Algebra (MvPolynomial (Fin m) K) A := φ.toAlgebra
  letI iKL : Algebra K L := ((algebraMap A L).comp g).toAlgebra
  letI iPL : Algebra (MvPolynomial (Fin m) K) L := ((algebraMap A L).comp φ).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin m) K) A L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (MvPolynomial (Fin m) K) L :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap A L (g r) = algebraMap A L (φ (MvPolynomial.C r))
      rw [hφ]
  haveI : Algebra.Etale (MvPolynomial (Fin m) K) A := hE
  haveI : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin m) K) L := Algebra.FormallyEtale.comp _ A _
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K L := hf
  exact card_eq_of_etale (K := K) (L := L)

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n q] {V : X.Opens}, (V : Set X).Nonempty → ∀ {m : ℕ} (c : Coord q V m), m = n := by
  intro K _ X q n hn V hV m c
  obtain ⟨x, hx⟩ := hV
  have hnt : Nontrivial Γ(X, V) := (X.presheaf.germ V x hx).hom.domain_nontrivial
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) q hn
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, c.affine⟩ le_top
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(X, V)
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1 (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  let e : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have hf : RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap Γ(X, V) (Localization.Away t)).comp (strV q V)) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e h₁
  exact card_eq_of_away (L := Localization.Away t) t (strV q V) (MvPolynomial.eval₂Hom (strV q V) c.t)
    (fun r => by simp) c.etale hf

end GlobalTheory.CompanionTheory.CoordCard
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFil

theorem dividedPowerFiltration_one_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) : pdP δ 1 ≤ J := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hr, rfl⟩
  induction l with
  | nil => simp at hr
  | cons q t ih =>
    have hq : q.2 ∈ J := hl q (by simp)
    rw [List.map_cons, List.prod_cons]
    by_cases h0 : q.1 = 0
    · refine J.mul_mem_left _ (ih (fun q' h' => hl q' (List.mem_cons_of_mem _ h')) ?_)
      simpa [h0] using hr
    · exact J.mul_mem_right _ (δ.dpow_mem h0 hq)

theorem dividedPowerFiltration_mul_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r r' : ℕ) :
    pdP δ r * pdP δ r' ≤ pdP δ (r + r') := by
  unfold pdP
  rw [Ideal.span_mul_span']
  refine Ideal.span_le.2 ?_
  rintro _ ⟨_, ⟨l, hl, hr, rfl⟩, _, ⟨l', hl', hr', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.1 hq with h | h
    · exact hl q h
    · exact hl' q h
  · simpa using Nat.add_le_add hr hr'
  · simp

theorem dpow_mem_pdP {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (k : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow k x ∈ pdP δ k :=
  Ideal.subset_span ⟨[(k, x)], by simpa using hx, by simp, by simp⟩

theorem isFil_sFil : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)), IsFil (sP Q) (sFil Q) := by
  intro b L Q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr T
    change T.obj.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.obj.pdPow_zero
  · intro T
    change T.obj.pdPow (1 : ℤ).toNat = T.obj.J
    exact le_antisymm (dividedPowerFiltration_one_le T.obj.δ) T.obj.J_le_pdPow_one
  · intro r r' h T
    exact T.obj.pdPow_anti (Int.toNat_le_toNat h)
  · intro r r' T x y hx hy
    have hx' : (show T.obj.B from x) ∈ pdP T.obj.δ r := by
      have : (show T.obj.B from x) ∈ T.obj.pdPow ((r : ℤ).toNat) := hx
      rw [Int.toNat_natCast] at this
      exact this
    have hy' : (show T.obj.B from y) ∈ pdP T.obj.δ r' := by
      have : (show T.obj.B from y) ∈ T.obj.pdPow ((r' : ℤ).toNat) := hy
      rw [Int.toNat_natCast] at this
      exact this
    have h := dividedPowerFiltration_mul_le T.obj.δ r r' (Ideal.mul_mem_mul hx' hy')
    change _ ∈ T.obj.pdPow (((r + r' : ℕ) : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact h
  · intro k T x hx
    change _ ∈ T.obj.pdPow ((k : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact dpow_mem_pdP T.obj.δ k hx

end GlobalTheory.CompanionTheory.DPFil
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Thick

theorem inU_iInf_finset : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) (S : Finset ι) (T : Thick (nlFun γ p X q κ)), InU (⨅ α ∈ S, U α) T ↔ ∀ α ∈ S, InU (U α) T := by
  intro O _ R _ I γ p X q κ ι U S T
  classical
  have htop : InU (⊤ : X.Opens) T := fun x _ => trivial
  have hinf : ∀ V W : X.Opens, InU (V ⊓ W) T ↔ InU V T ∧ InU W T := by
    intro V W
    constructor
    · intro h
      exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩
    · intro h x hx
      exact ⟨h.1 hx, h.2 hx⟩
  induction S using Finset.induction_on with
  | empty => simpa using htop
  | insert a s ha ih =>
    rw [Finset.iInf_insert]
    refine (hinf _ _).trans ?_
    constructor
    · rintro ⟨h1, h2⟩ α hα
      rcases Finset.mem_insert.1 hα with rfl | hα
      · exact h1
      · exact ih.1 h2 α hα
    · intro h
      exact ⟨h a (Finset.mem_insert_self a s), ih.2 fun α hα => h α (Finset.mem_insert_of_mem hα)⟩

end GlobalTheory.CompanionTheory.Thick
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ThickPt

theorem inU_map {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (V : X.Opens)
    {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') : InU V T → InU V T' := by
  intro h
  unfold CrystallineSemistableComparison.Pb.InU at h ⊢
  obtain ⟨ψ, _, _, _, hle, hpt, _, _, _⟩ := φ
  have key : CrystallineSemistableComparison.Pb.pt T' =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J ψ hle)) ≫ CrystallineSemistableComparison.Pb.pt T := by
    unfold CrystallineSemistableComparison.Pb.pt
    rw [← hpt]
    rfl
  rw [key]
  intro x _
  exact @h ((Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J ψ hle))).base x) trivial

end GlobalTheory.CompanionTheory.ThickPt
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartFrames

theorem smor_Fr_frame : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q κ' σ) {V V' : X.Opens} {d : ℕ}
    (c : Chart γ p q κ V d) (c' : Chart γ' p q κ' V' d) (hc : c.Good) (hc' : c'.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p X q κ')))
    (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T)) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D)
    (hQ' : ∀ T, Q' T → InU V' T) (hD' : Q' c'.D) (e : c.D ⟶ (m.mor p).functor.obj c'.D),
    (∀ i, e.φ (c.t i) = c'.t i) →
      SMor.Fr (m.smor Q Q' h) (c.frame hc Q hQ hD) (c'.frame hc' Q' hQ' hD') (ObjectProperty.homMk e) := by
  intro O R R' _ _ _ I I' γ γ' p X q κ κ' σ m V V' d c c' hc hc' Q Q' h hQ hD hQ' hD' e he i T s s'
  change (s'.hom.φ (e.φ (c.t i)) - s.hom.φ (e.φ (c.t i)) : T.obj.B) = s'.hom.φ (c'.t i) - s.hom.φ (c'.t i)
  rw [he]

end GlobalTheory.CompanionTheory.ChartFrames
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeDerivs

theorem exists_dual_derivations : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (V : X.Opens) (d : ℕ) (c : Coord q V d), letI := (strV q V).toAlgebra;
    ∃ D : Fin d → Derivation K Γ(X, V) Γ(X, V), ∀ k j, D k (c.t j) = if k = j then 1 else 0 := by
  intro K _ X q V d c
  letI := (strV q V).toAlgebra
  letI : Algebra (MvPolynomial (Fin d) K) Γ(X, V) :=
    (MvPolynomial.eval₂Hom (strV q V) c.t : MvPolynomial (Fin d) K →+* Γ(X, V)).toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C (strV q V) c.t r).symm
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) Γ(X, V) := c.etale
  obtain ⟨⟨b, hb⟩, -⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale K Γ(X, V) (Fin d)
  have hb' : ∀ j, KaehlerDifferential.D K Γ(X, V) (c.t j) = b j := fun j => by
    rw [hb j]
    congr 1
    exact (MvPolynomial.eval₂Hom_X' (strV q V) c.t j).symm
  refine ⟨fun k => KaehlerDifferential.linearMapEquivDerivation K Γ(X, V)
    (b.coord k), fun k j => ?_⟩
  change b.coord k (KaehlerDifferential.D K Γ(X, V) (c.t j)) = _
  rw [hb', Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [eq_comm]

end GlobalTheory.CompanionTheory.ConeDerivs
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.SiteCup

theorem pull_unit_class {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {σ : R →+* R'} (A : C ⥤ CommAlgCat.{0} R) (A' : C' ⥤ CommAlgCat.{0} R')
    (m : CH.Mor (CH.modF A) (CH.modF A') σ)
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH A' := by
  unfold CH.Mor.pull CH.oneH
  generalize_proofs p1 p2
  rw [CrystallineSemistableComparison.P.mapH_cls]
  · congr 1
    funext s
    exact h _
  · convert p2 using 2
    funext s
    exact h _

theorem smor_cup : ∀ {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C}
    {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ), (∀ {i j k : ℕ} (h : i + j = k) x y,
      m.o.pull k ((CH.mulP Φ.A).cup h x y) = (CH.mulP Φ'.A).cup h (m.o.pull i x) (m.o.pull j y)) ∧
    m.o.pull 0 (CH.oneH Φ.A) = CH.oneH Φ'.A := by
  intro R R' _ _ C C' _ _ Φ Φ' σ m
  refine ⟨?_, pull_unit_class _ _ m.o (fun T => RingHom.map_one (m.ρ T))⟩
  intro i j k h x y
  have hz : ∀ n (c : (CH.cx (CH.modF Φ.A)).X n), c ∈ (CH.cx (CH.modF Φ.A)).Z n →
      m.o.hom.f n c ∈ (CH.cx (CH.modF Φ'.A)).Z n := by
    intro n c hc
    refine LinearMap.mem_ker.mpr ?_
    rw [m.o.hom.comm, LinearMap.mem_ker.mp hc, map_zero]
  have ex := CrystallineSemistableComparison.Auxff.cls_out _ x
  generalize Quotient.out x = z at ex
  subst ex
  have ey := CrystallineSemistableComparison.Auxff.cls_out _ y
  generalize Quotient.out y = w at ey
  subst ey
  obtain ⟨a, ha⟩ := z
  obtain ⟨b, hb⟩ := w
  have cup_cls {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
      {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
      {p q n : ℕ} (h : p + q = n) (a : CH.Cn F₁ p) (b : CH.Cn F₂ q) ha hb :
      ∃ hc, P.cup h ((CH.cx F₁).cls a ha) ((CH.cx F₂).cls b hb) =
        (CH.cx F₃).cls (P.cupC h a b) hc := by
    have ce (x : CH.H F₁ p) (y : CH.H F₂ q) :
        P.cup h x y = (CrystallineSemistableComparison.Auxff.toCx P).cup h x y := by
      unfold CH.Pairing.cup CxPairing.cup
      split_ifs with hz
      · rfl
      · exact absurd ((CrystallineSemistableComparison.Auxff.toCx P).leib h _ _ |>.trans (by
          rw [show CH.d F₁ p (Quotient.out x).1 = 0 from (Quotient.out x).2,
            show CH.d F₂ q (Quotient.out y).1 = 0 from (Quotient.out y).2]; simp)) hz
    exact ⟨CrystallineSemistableComparison.Auxff.closed (CrystallineSemistableComparison.Auxff.toCx P) h a b ha hb,
      (ce _ _).trans
        (CrystallineSemistableComparison.P.cxcup_cls (CrystallineSemistableComparison.Auxff.toCx P) h a b ha hb _)⟩
  obtain ⟨hc, e⟩ := cup_cls (CH.mulP Φ.A) h a b ha hb
  obtain ⟨hc', e'⟩ := cup_cls (CH.mulP Φ'.A) h _ _ (hz _ _ ha) (hz _ _ hb)
  rw [e]
  unfold CH.Mor.pull
  rw [CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ ha), CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ hb), e',
    CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ hc)]
  congr 1
  funext s
  simp [CH.Mor.hom, CH.Mor.pullC, CH.mulP, CH.Pairing.cupC, SMor.o, CH.term, CH.modF]
  congr 1 <;> exact m.nat _ _

end GlobalTheory.CompanionTheory.SiteCup
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

theorem _root_.GlobalTheory.T.mirabolic_character_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.MirCharEq k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single | exact GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single | (intros; apply GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

theorem _root_.GlobalTheory.T.mirabolic_filtration_exhaustive : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.Exhaust k := by
  first | exact @GlobalTheory.CompanionTheory.BZMirExhaust.exhaust | exact GlobalTheory.CompanionTheory.BZMirExhaust.exhaust | (intros; apply GlobalTheory.CompanionTheory.BZMirExhaust.exhaust <;> assumption)
end
