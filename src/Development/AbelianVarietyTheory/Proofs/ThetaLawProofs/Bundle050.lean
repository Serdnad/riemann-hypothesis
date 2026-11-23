module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacNeZeroIffSpanEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle049
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KosResidueExact

theorem kosD_apply_map {k K : Type} [CommRing k] [CommRing K] (f : k →+* K) {g : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) k) (p q : KIx g 0 N) :
    kosD (d := 0) (fun i j j' => (m i j j').map f) (fun _ => 0) p q =
      f (kosD (d := 0) m (fun _ => 0) p q) := by
  rcases p with p | a
  · rcases q with q | a
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [kosD, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · exact a.elim0
  · exact a.elim0

theorem descend {k K : Type} [Field k] [Field K] [Algebra k K] {g : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) k)
    (H : ∀ v : KIx g 0 N → K,
      (kosD (d := 0) (fun i j j' => (m i j j').map (algebraMap k K)) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map (algebraMap k K)) (fun _ => 0)).mulVec w (.inl p))
    (v : KIx g 0 N → k) (hv : (kosD (d := 0) m (fun _ => 0)).mulVec v = 0) :
    ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p) := by
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k K)
    (LinearMap.ker_eq_bot.2 (algebraMap k K).injective)
  have hl : ∀ a, lam (algebraMap k K a) = a := fun a => LinearMap.congr_fun hlam a
  obtain ⟨w, hw⟩ := H (fun p => algebraMap k K (v p)) (by
    funext p
    have := congrArg (algebraMap k K) (congrFun hv p)

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this ⊢
    simpa only [kosD_apply_map] using this)
  refine ⟨fun q => lam (w q), fun p hp => ?_⟩
  have := congrArg lam (hw p hp)
  rw [hl] at this
  rw [this]

  simp only [Matrix.mulVec, dotProduct, map_sum, kosD_apply_map]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem transport {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {g g' : ℕ} (hg : g' = g) (l n : ℕ)
    (m : Fin g → ∀ j j', Matrix (Fin ((l - j * n) ^ g)) (Fin ((l - j' * n) ^ g)) O)
    (m' : Fin g' → ∀ j j', Matrix (Fin ((l - j * n) ^ g')) (Fin ((l - j' * n) ^ g')) K)
    (hm : ∀ i j j' k k', m' i j j' k k' = f (m (i.cast hg) j j'
      (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)) (k'.cast (congrArg (fun r => (l - j' * n) ^ r) hg))))
    (H : ∀ v : KIx g' 0 (fun j => (l - j * n) ^ g') → K, (kosD m' (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m' (fun _ => 0)).mulVec w (.inl p)) :
    ∀ v : KIx g 0 (fun j => (l - j * n) ^ g) → K,
      (kosD (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec w (.inl p) := by
  subst hg
  have : m' = fun i j j' => (m i j j').map f := by
    funext i j j'
    ext k k'
    exact hm i j j' k k'
  subst this
  exact H

theorem main : Out.Laws → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (k : Type) [Field k] (f : O →+* k) (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → FinZ x s → (∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → k, (kosD (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec w (.inl p)) := by
  intro hL O _ _ _ k _ f x n l s b m hn hl hb hm hZ
  obtain ⟨x', φ, w, hg, s', b', m', -, -, -, hb', hm', hmm, hZ'⟩ :=
    GlobalTheory.T.exists_keyData_baseChange_sections_matrices hL O (AlgebraicClosure k) ((algebraMap k (AlgebraicClosure k)).comp f) x n l s b m hl hb hm
  have hfin : Finite (Sp (AlgebraicClosure k)) :=
    inferInstanceAs (Finite (PrimeSpectrum (AlgebraicClosure k)))
  have hc : ∀ y : x'.P.A.left, ∃ i, y ∈ x'.P.L.U i := fun y => exists_chart x'.P.isLB y
  choose c hc using hc
  have H := (GlobalTheory.T.koszul_sections_exact_algClosed_polarisedAV hL (AlgebraicClosure k) x' n l s' b' m' c hn (by rw [hg]; exact hl)
    (hZ' hfin hZ) hb' hm' hc).1
  have H' := transport ((algebraMap k (AlgebraicClosure k)).comp f) hg l n m m' hmm H
  exact descend (K := AlgebraicClosure k) (N := fun j => (l - j * n) ^ x.P.g)
    (fun i j j' => (m i j j').map f) H'

end GlobalTheory.KosResidueExact
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_principalPolarization_symmetric_squareRoot : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → SmoothOfRelativeDimension h c.A.hom → L.IsLB → LBIso (abelian₂ c.A L) c.P → LBIso L (L.pull (GrpObj.inv : c.A ⟶ c.A).left) → ∃ (P : Out.PolAV (Sp R)) (φ : P.A.left ⟶ c.A.left), SqOf P c (𝟙 _) φ := by
  first | exact @GlobalTheory.SymRoot.exists_polAV_sqOf | exact GlobalTheory.SymRoot.exists_polAV_sqOf | (intros; apply GlobalTheory.SymRoot.exists_polAV_sqOf <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.ClosedApprox
open EtBaseChange

theorem valT_cst {R T : Type} [CommRing R] [CommRing T] {X : Scheme.{0}} (p : X ⟶ Sp R) (w : Sp T ⟶ X) (F : R →+* T)
    (hw : w ≫ p = spMap F) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (c : R) : valT w U (AbLaw.cst p U c) = F c := by
  have h0 : valT w U (AbLaw.cst p U c) =
      valT w U ((p.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := rfl
  refine h0.trans ((valT_appLE w p (U := ⊤) le_top h _).trans ?_)
  rw [hw, ← Category.comp_id (spMap F)]
  refine (valT_spMap F (𝟙 (Sp R)) le_top _).trans (congrArg F ((valT_eq _ _ le_top _).trans ?_))
  have e3 : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_top = 𝟙 _ := by
    rw [← Scheme.Hom.id_appTop]; exact Scheme.Hom.appLE_eq_app _
  unfold valH
  erw [e3]
  exact congrArg (fun q => q.hom c) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id

theorem top_le_of_closedPoint {T : Type} [CommRing T] [IsLocalRing T] {X : Scheme.{0}} (w : Sp T ⟶ X) {U : X.Opens}
    (h : w (IsLocalRing.closedPoint T) ∈ U) : ⊤ ≤ w ⁻¹ᵁ U := fun p _ =>
  ((IsLocalRing.specializes_closedPoint p).map w.continuous).mem_open U.isOpen h

theorem exists_stalk_hom {T : Type} [CommRing T] [IsLocalRing T] {X : Scheme.{0}} (w : Sp T ⟶ X) (z : X)
    (hz : w (IsLocalRing.closedPoint T) = z) : ∃ ψ : X.presheaf.stalk z →+* T, ∀ (U : X.Opens), z ∈ U →
      ∀ a : Γ(X, U), valT w U a = ψ (gs (𝟙 X) z U a) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : X.presheaf.stalk z ⟶ .of T, Spec.map φ ≫ X.fromSpecStalk z = w := by
    subst hz
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of T) w⟩
  refine ⟨φ.hom, fun U hU a => ?_⟩
  rw [← hφ, JacGen.valT_specMap_fromSpecStalk hU, gs_eq (𝟙 X) z U hU]
  rfl

theorem exists_mem_sub_mem_pow {σ K : Type} [Finite σ] [CommRing K] (S : Subring (MvPowerSeries σ K))
    (hC : ∀ a, algebraMap K _ a ∈ S) (hX : ∀ i, MvPowerSeries.X i ∈ S) (r : ℕ) (G : MvPowerSeries σ K) :
    ∃ p ∈ S, G - p ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ K)) ^ r := by
  have key : ∀ q : MvPolynomial σ K, (q : MvPowerSeries σ K) ∈ S := fun q => by
    induction q using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.coe_C]; exact hC a
    | add p q hp hq => simpa using S.add_mem hp hq
    | mul_X p i hp => simpa using S.mul_mem hp (hX i)
  refine ⟨_, key (MvPowerSeries.truncTotal r G), ?_⟩
  rw [← germIdeal_eq_span, mem_germIdeal_pow_iff]
  intro d hd
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ hd, sub_self]

theorem mem_nonzeroLocus_of_via {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'}
    {φ : x'.P.A.left ⟶ x.P.A.left} {w : LB.Iso x'.P.L (x.P.L.pull φ)} {l : ℕ} {s' : RR x' l} {s : RR x l}
    (hs : SecVia x' x φ w s' s) (y : x'.P.A.left) (hy : y ∈ Out.nonzeroLocus s') : φ y ∈ Out.nonzeroLocus s := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨k, hk⟩ := exists_chart x.P.isLB (φ y)
  have hle : (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U k := fun y hy => mem_pull.1 hy.1
  have e := hs (fun _ => k) i hle
  have hm : y ∈ (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i := ⟨mem_pull.2 hk, x'.P.A.left.basicOpen_le _ hi⟩
  have h1 : y ∈ x'.P.A.left.basicOpen ((φ.appLE _ _ hle).hom (s.f k)) := by
    refine (congrArg x'.P.A.left.basicOpen e).ge ((Scheme.basicOpen_mul _ _ _).ge ⟨?_, ?_⟩)
    · exact (Scheme.basicOpen_of_isUnit _ ((w.s (fun _ => k, i)).isUnit.pow l)).ge hm
    · exact (Scheme.basicOpen_res _ _ _).ge ⟨hm, hi⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_appLE φ _ (x.P.L.U k) hle (s.f k)).le h1).2⟩

theorem isLocalHom_map {σ O K : Type} [CommRing O] [IsLocalRing O] [Field K] (f : O →+* K)
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O) : IsLocalHom (MvPowerSeries.map (σ := σ) f) :=
  ⟨fun a ha => by
    rw [MvPowerSeries.isUnit_iff_constantCoeff] at ha ⊢
    by_contra h
    have : MvPowerSeries.constantCoeff a ∈ RingHom.ker f := hf ▸ h
    rw [MvPowerSeries.constantCoeff_map, RingHom.mem_ker.1 this] at ha
    exact not_isUnit_zero ha⟩

theorem exists_sec_cast {R : Type} [CommRing R] (x : KeyIn R) {l l' : ℕ} (h : l = l') (s : RR x l) :
    ∃ s' : RR x l', ∀ c, (show Γ(x.P.A.left, x.P.L.U c) from s'.f c) = (show Γ(x.P.A.left, x.P.L.U c) from s.f c) := by
  subst h
  exact ⟨s, fun _ => rfl⟩

theorem sub_mem_sup {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (u : Tˣ) (N : ℕ) {I : Ideal S} {J J' : Ideal T}
    (hI : I ≤ J.comap ψ) {g a : S} {G : T} (h₁ : g - a ∈ I) (h₂ : ((u⁻¹ : Tˣ) : T) ^ N * G - ψ a ∈ J') :
    G - (u : T) ^ N * ψ g ∈ J ⊔ J' := by
  have e : G - (u : T) ^ N * ψ g = (u : T) ^ N * ((((u⁻¹ : Tˣ) : T) ^ N * G - ψ a) - ψ (g - a)) := by
    have : (u : T) ^ N * ((u⁻¹ : Tˣ) : T) ^ N = 1 := by rw [← mul_pow, Units.mul_inv, one_pow]
    rw [map_sub]
    linear_combination (-G) * this
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ (Ideal.mem_sup_right h₂) (Ideal.mem_sup_left (hI h₁)))

end GlobalTheory.KeyKa.ClosedApprox

namespace GlobalTheory.KeyKa
open EtBaseChange ClosedApprox

theorem exists_comb_sub_mem_sup_pow : Out.Laws → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (K : Type) [Field K] [IsAlgClosed K] (f : O →+* K) (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (Y : Type) (θ : Y → (Sp (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A.left)) (c : Y → x.P.L.ι), RingHom.ker f = IsLocalRing.maximalIdeal O → 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → FinZ x s → (∀ y, θ y ≫ x.P.A.hom = spMap (algebraMap O (MvPowerSeries (Fin x.P.g) O))) → (∀ y, (∃ (V : x.P.A.left.Opens) (t : Fin x.P.g → Γ(x.P.A.left, V)), ⊤ ≤ (θ y) ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin x.P.g) O)) (θ y) V (t i) = MvPowerSeries.X i)) → (∀ y, ⊤ ≤ (θ y) ⁻¹ᵁ x.P.L.U (c y)) → Function.Injective (fun y => θ y (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O))) → (∀ y i, θ y (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) ∉ Out.nonzeroLocus (s i)) → ∀ (r : ℕ) (G : Y → MvPowerSeries (Fin x.P.g) K), ∃ v : Fin ((l - 0 * n) ^ x.P.g) → K, ∀ y, G y - ∑ k, v k • MvPowerSeries.map f (valT (T := (MvPowerSeries (Fin x.P.g) O)) (θ y) (x.P.L.U (c y)) ((b 0 k).f (c y))) ∈ Ideal.span (Set.range fun i => MvPowerSeries.map f (valT (T := (MvPowerSeries (Fin x.P.g) O)) (θ y) (x.P.L.U (c y)) ((s i).f (c y)))) ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ r := by
  intro hL O _ _ _ K _ _ f x n l s b m Y θ c hf hn hl hb hm hZ hθ hco hc hinj hz r G
  obtain ⟨x', φ, w, hg, s', b', m', ⟨_, _, _, hp, -⟩, hs', hb', hB', hm', -, hZ'⟩ :=
    GlobalTheory.T.exists_keyData_baseChange_sections_matrices hL O K f x n l s b m hl hb hm
  replace hZ' := hZ' (inferInstanceAs (Finite (PrimeSpectrum K))) hZ
  let F : MvPowerSeries (Fin x.P.g) O →+* MvPowerSeries (Fin x.P.g) K := MvPowerSeries.map f
  have hF : IsLocalHom F := isLocalHom_map f hf
  have hw : ∀ y, (spMap F ≫ θ y) ≫ x.P.A.hom = spMap (algebraMap K (MvPowerSeries (Fin x.P.g) K)) ≫ spMap f :=
    fun y => by
      have : F.comp (algebraMap O _) = (algebraMap K (MvPowerSeries (Fin x.P.g) K)).comp f :=
        RingHom.ext fun a => MvPowerSeries.map_C f a
      rw [Category.assoc, hθ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  obtain ⟨θ', h₁, h₂⟩ : ∃ θ' : Y → (Sp (MvPowerSeries (Fin x.P.g) K) ⟶ x'.P.A.left),
      (∀ y, θ' y ≫ φ = spMap F ≫ θ y) ∧
        ∀ y, θ' y ≫ x'.P.A.hom = spMap (algebraMap K (MvPowerSeries (Fin x.P.g) K)) :=
    ⟨fun y => hp.1.lift _ _ (hw y), fun y => hp.1.lift_fst _ _ _, fun y => hp.1.lift_snd _ _ _⟩
  let P : Y → x'.P.A.left := fun y => θ' y (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) K))
  have hP : ∀ y, φ (P y) = θ y (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) := fun y =>
    (congrArg (fun q => q (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) K))) (h₁ y)).trans
      (congrArg (θ y) (IsLocalRing.comap_closedPoint F))
  have hPinj : Function.Injective P := fun y y' h => hinj ((hP y).symm.trans ((congrArg φ h).trans (hP y')))
  choose c' hc' using exists_chart x'.P.isLB
  have hU : ∀ y, ⊤ ≤ θ' y ⁻¹ᵁ x'.P.L.U (c' (P y)) := fun y => top_le_of_closedPoint _ (hc' (P y))
  have hφ : ∀ y {V : x.P.A.left.Opens}, ⊤ ≤ θ y ⁻¹ᵁ V → ⊤ ≤ (θ' y ≫ φ) ⁻¹ᵁ V := fun y V h p _ => by
    rw [h₁ y]
    exact h (show spMap F p ∈ ⊤ from trivial)
  have hval : ∀ y {V : x.P.A.left.Opens}, ⊤ ≤ θ y ⁻¹ᵁ V → ∀ a, valT (θ' y ≫ φ) V a = F (valT (θ y) V a) :=
    fun y V h a => (congrArg (fun q => valT q V a) (h₁ y)).trans (valT_spMap F (θ y) h a)
  have hW := fun y => le_inf_pull (θ' y) (c y) (c' (P y)) (hφ y (hc y)) (hU y)
  obtain ⟨u, hu⟩ : ∃ u : Y → (MvPowerSeries (Fin x.P.g) K)ˣ, ∀ y (l : ℕ) (sg : RR x l) (sg' : RR x' l),
      SecVia x' x φ w sg' sg → F (valT (θ y) (x.P.L.U (c y)) (sg.f (c y))) =
        (u y : MvPowerSeries (Fin x.P.g) K) ^ l * valT (θ' y) (x'.P.L.U (c' (P y))) (sg'.f (c' (P y))) := by
    refine ⟨fun y => Units.map (valH (θ' y) _ (hW y)).toMonoidHom (w.s (fun _ => c y, c' (P y))),
      fun y l sg sg' h => (hval y (hc y) _).symm.trans ((valT_via h (θ' y) (c y) (c' (P y)) (hφ y (hc y)) (hU y)).trans
        (congrArg (· ^ l * _) (valT_eq _ _ (hW y) _)))⟩
  choose ψ hψ using fun y z (h : P y = z) => exists_stalk_hom (θ' y) z h
  have ha : ∀ z : x'.P.A.left, ∃ a : x'.P.A.left.presheaf.stalk z, ∀ y (h : P y = z),
      (((u y)⁻¹ : (MvPowerSeries (Fin x.P.g) K)ˣ) : MvPowerSeries (Fin x.P.g) K) ^ (l - 0 * n) * G y - ψ y z h a ∈
        Ideal.span (Set.range MvPowerSeries.X) ^ r := fun z => by
    by_cases hz : ∃ y, P y = z
    · obtain ⟨y, rfl⟩ := hz
      obtain ⟨V, t, hV, ht⟩ := hco y
      obtain ⟨_, ⟨a, rfl⟩, ha⟩ := exists_mem_sub_mem_pow (ψ y _ rfl).range
        (fun a => ⟨_, (hψ y _ rfl _ (hc' _) _).symm.trans (valT_cst _ _ _ (h₂ y) _ (hU y) a)⟩)
        (fun i => ⟨_, (hψ y _ rfl (φ ⁻¹ᵁ V) (hφ y hV trivial) _).symm.trans
          ((valT_appLE (θ' y) φ le_rfl (hφ y hV) (t i)).trans ((hval y hV _).trans
            ((congrArg F (ht i)).trans (MvPowerSeries.map_X f i))))⟩) r
        ((((u y)⁻¹ : (MvPowerSeries (Fin x.P.g) K)ˣ) : MvPowerSeries (Fin x.P.g) K) ^ (l - 0 * n) * G y)
      refine ⟨a, fun y' h => ?_⟩
      obtain rfl := hPinj h
      exact ha
    · exact ⟨0, fun y h => (hz ⟨y, h⟩).elim⟩
  choose a ha using ha
  obtain ⟨sg₀, hsg₀⟩ := (GlobalTheory.T.koszul_sections_exact_algClosed_polarisedAV hL K x' n l s' b' m' c' hn (hg ▸ hl) hZ' hB' hm' hc').2.1 a
  obtain ⟨sg, hsg⟩ := exists_sec_cast x' (show l = l - 0 * n by simp) sg₀
  obtain ⟨v, hv, -⟩ := hB' 0 (Nat.zero_le _) sg
  have hN : (l - 0 * n) ^ x'.P.g = (l - 0 * n) ^ x.P.g := congrArg (fun r => (l - 0 * n) ^ r) hg
  refine ⟨fun k => v (k.cast hN.symm), fun y => ?_⟩
  have hzero : ∀ i, P y ∉ Out.nonzeroLocus (s' i) := fun i h =>
    hz y (i.cast hg) (hP y ▸ mem_nonzeroLocus_of_via (hs' i) _ h)
  have e : ∑ k, v (k.cast hN.symm) • F (valT (θ y) (x.P.L.U (c y)) ((b 0 k).f (c y))) =
      (u y : MvPowerSeries (Fin x.P.g) K) ^ (l - 0 * n) *
        ψ y _ rfl (gs (𝟙 _) (P y) (x'.P.L.U (c' (P y))) (sg₀.f (c' (P y)))) := by
    have e₁ := (hψ y _ rfl _ (hc' _) _).symm.trans ((congrArg (valT (θ' y) (x'.P.L.U (c' (P y))))
      ((hsg (c' (P y))).symm.trans (hv (c' (P y))))).trans ((valT_eq _ _ (hU y) _).trans (map_sum _ _ _)))
    refine Eq.trans ?_ (congrArg (_ * ·) e₁.symm)
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (finCongr hN) _ _ fun k => ?_).symm
    rw [map_mul, ← valT_eq, ← valT_eq, valT_cst _ _ _ (h₂ y) _ (hU y), mul_left_comm, Algebra.smul_def]
    exact congrArg (_ * ·) (hu y _ _ _ (hb' 0 k)).symm
  refine (congrArg (fun q => G y - q ∈ _) e).mpr (sub_mem_sup (ψ y _ rfl) (u y) _ ?_ (hsg₀ (P y) hzero) (ha _ y rfl))
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  refine Ideal.mem_comap.2 ((Ideal.unit_mul_mem_iff_mem _ ((u y).isUnit.pow n)).1
    (Ideal.subset_span (Set.mem_range.2 ⟨i.cast hg, ?_⟩)))
  exact (hu y _ _ _ (hs' i)).trans (congrArg (_ * ·) (hψ y _ rfl _ (hc' _) _))

end GlobalTheory.KeyKa
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open scoped CategoryTheory.Obj

namespace GlobalTheory.KeyTf

theorem exists_isGrpPullback_of_le {S : Type} [CommRing S] {R₀ R₁ : Subring S} (h : R₀ ≤ R₁) (A : Over (Sp S))
    [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A.left ⟶ A₀.left)
    (H : IsGrpPullback A A₀ (spMap R₀.subtype) φ) :
    ∃ φ₁ : A.left ⟶ ((Over.pullback (spMap (Subring.inclusion h))).obj A₀).left,
      IsGrpPullback A ((Over.pullback (spMap (Subring.inclusion h))).obj A₀) (spMap R₁.subtype) φ₁ := by
  have e : spMap R₀.subtype = spMap R₁.subtype ≫ spMap (Subring.inclusion h) :=
    spMap_comp (Subring.inclusion h) R₁.subtype
  have hp := isGrpPullback_pullback A₀ (spMap (Subring.inclusion h))
  refine ⟨hp.1.lift φ (A.hom ≫ spMap R₁.subtype) (by rw [H.1.w, e, Category.assoc]), ?_⟩
  exact IsGrpPullback.cancel hp (H.congr e (hp.1.lift_fst _ _ _).symm) (hp.1.lift_snd _ _ _)

theorem exists_projective_abelian_model : ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] (P : Out.PolAV (Sp S)), ∃ (R : Subring S) (A₀ : Over (Sp R)) (_ : GrpObj A₀) (φ : P.A.left ⟶ A₀.left), Algebra.FiniteType ℤ R ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension P.g A₀.hom ∧ IsProjOver A₀.hom ∧ IsGrpPullback P.A A₀ (spMap R.subtype) φ := by
  intro S _ _ _ P
  have hc := P.isAb.comm
  have hs := P.isAb.smooth
  have hpr := P.isAb.proper
  have hg := P.isAb.geomConnected
  obtain ⟨R₀, A₀, _, _, φ₀, -, hft₀, hs₀, hsep₀, hqc₀, H₀⟩ :=
    GlobalTheory.smooth_grpScheme_descends_to_fg_subring S P.A ∅ hs inferInstance inferInstance
  obtain ⟨F, hF⟩ := GlobalTheory.T.isProjOver_descends_to_subring' S R₀ _ _ P.A.hom A₀.hom φ₀ H₀.1 (GlobalTheory.ProjSpace.isProjOver_polAV P)
  obtain ⟨R₁, h₀₁, hF₁, hft₁⟩ := exists_finiteType_subring_adjoin S R₀ F hft₀
  obtain ⟨A₁, _, _, φ₁, hp₁, hs₁, H₁⟩ : ∃ (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (_ : IsCommMonObj A₁)
      (φ₁ : P.A.left ⟶ A₁.left), IsProjOver A₁.hom ∧ Smooth A₁.hom ∧ IsGrpPullback P.A A₁ (spMap R₁.subtype) φ₁ := by
    obtain ⟨φ₁, H₁⟩ := exists_isGrpPullback_of_le h₀₁ P.A A₀ φ₀ H₀
    exact ⟨_, _, inferInstance, φ₁, hF R₁ h₀₁ hF₁ _ _ _ (IsPullback.of_hasPullback _ _),
      inferInstanceAs (Smooth (pullback.snd _ _)), H₁⟩
  let κ := IsLocalRing.residue S
  have e₁ : spMap (κ.comp R₁.subtype) = spMap κ ≫ spMap R₁.subtype := spMap_comp _ _
  have hfib : GeometricallyConnected (pullback.snd A₁.hom (spMap (κ.comp R₁.subtype))) := by
    have Q := IsPullback.of_hasPullback A₁.hom (spMap (κ.comp R₁.subtype))
    let l := H₁.1.lift (pullback.fst A₁.hom (spMap (κ.comp R₁.subtype))) (pullback.snd _ _ ≫ spMap κ)
      (by rw [Q.w, e₁, Category.assoc])
    have Q' : IsPullback l (pullback.snd A₁.hom (spMap (κ.comp R₁.subtype))) P.A.hom (spMap κ) :=
      IsPullback.of_right (by rw [H₁.1.lift_fst, ← e₁]; exact Q) (H₁.1.lift_snd _ _ _) H₁.1
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) Q' hg
  obtain ⟨f, hf, hconn⟩ := GlobalTheory.T.geometricallyConnected_open_condition_smooth_projective R₁ _ A₁.hom _ (κ.comp R₁.subtype) hp₁ hs₁ hfib
  obtain ⟨u, hu⟩ : IsUnit (f : S) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hf
  obtain ⟨R₂, h₁₂, hF₂, hft₂⟩ := exists_finiteType_subring_adjoin S R₁ {((u⁻¹ : Sˣ) : S)} hft₁
  obtain ⟨φ₂, H₂⟩ := exists_isGrpPullback_of_le h₁₂ P.A A₁ φ₁ H₁
  have hunit : IsUnit (Subring.inclusion h₁₂ f) :=
    IsUnit.of_mul_eq_one (⟨((u⁻¹ : Sˣ) : S), hF₂ (by simp)⟩ : R₂) (Subtype.ext (by
      show (f : S) * _ = 1
      rw [← hu]; exact u.mul_inv))
  have hp₂ : IsProjOver ((Over.pullback (spMap (Subring.inclusion h₁₂))).obj A₁).hom :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd _ hp₁
  have hab : IsAbelianScheme ((Over.pullback (spMap (Subring.inclusion h₁₂))).obj A₁) :=
    ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd _ _)), projProper _ _ _ hp₂, hconn R₂ _ hunit⟩
  refine ⟨R₂, _, inferInstance, φ₂, hft₂, hab, ?_, hp₂, H₂⟩
  have e₂ : spMap (κ.comp R₂.subtype) = spMap κ ≫ spMap R₂.subtype := spMap_comp _ _
  refine GlobalTheory.CM.smoothOfRelativeDimension_of_fibre R₂ _ (κ.comp R₂.subtype) _ _
    (pullback.fst P.A.hom (spMap κ) ≫ φ₂) (pullback.snd P.A.hom (spMap κ)) P.g hab ?_ ?_
  · rw [e₂]; exact (IsPullback.of_hasPullback _ _).paste_horiz H₂.1
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback (IsPullback.of_hasPullback _ _)
      P.smoothDim

end GlobalTheory.KeyTf
end
