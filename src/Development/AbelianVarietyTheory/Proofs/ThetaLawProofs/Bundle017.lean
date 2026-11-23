module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormOfParts
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem isPreirreducible_connectedComponent_of_smooth {K : Type} [Field K] {Z : Scheme.{0}}
    (g : Z ⟶ Spec (.of K)) [Smooth g] (z : Z) : IsPreirreducible (connectedComponent z) := by
  have hK : GlobalTheory.IsNormalScheme (Spec (.of K)) := inferInstance
  have : GlobalTheory.IsNormalScheme Z := (GlobalTheory.isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g ((GlobalTheory.isNormalScheme_iff _).mp hK))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  rw [GlobalTheory.IsNormalScheme.connectedComponent_eq_irreducibleComponent]
  exact isIrreducible_irreducibleComponent.2

theorem apply_eq_of_isPreirreducible {T F : Type} [CommRing T] [Field F] (f g : T →+* F)
    (C : Set (PrimeSpectrum T)) (hC : IsPreirreducible C) (z : PrimeSpectrum F)
    (hf : PrimeSpectrum.comap f z ∈ C) (hg : PrimeSpectrum.comap g z ∈ C)
    (e : T) (he : IsIdempotentElem e) : f e = g e := by
  have hz : ∀ a : F, a ∈ z.asIdeal ↔ a = 0 := by
    intro a
    have : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right z.2.ne_top
    rw [this, Ideal.mem_bot]
  have key : ∀ (f g : T →+* F), PrimeSpectrum.comap f z ∈ C → PrimeSpectrum.comap g z ∈ C →
      f e = 0 → g e = 1 → False := by
    intro f g hf hg h0 h1
    obtain ⟨x, -, hx1, hx2⟩ := hC (PrimeSpectrum.basicOpen (1 - e)) (PrimeSpectrum.basicOpen e)
      (PrimeSpectrum.basicOpen _).2 (PrimeSpectrum.basicOpen _).2
      ⟨_, hf, by simp [hz, h0]⟩ ⟨_, hg, by simp [hz, h1]⟩
    have h : (1 - e) * e ∈ x.asIdeal := by
      rw [sub_mul, _root_.one_mul, he.eq, sub_self]; exact x.asIdeal.zero_mem
    exact (x.2.mem_or_mem h).elim hx1 hx2
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map f) with h | h <;>
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map g) with h' | h'
  · rw [h, h']
  · exact (key f g hf hg h h').elim
  · exact (key g f hg hf h' h).elim
  · rw [h, h']

theorem lift_eq_of_sameComp_of_isIdempotentElem :
    ∀ (K : Type) [Field K] [Algebra K ℂ] (X : Scheme.{0}) (s : X ⟶ Sp K) (R : Type) [CommRing R] [Algebra K R] (i : Sp R ⟶ X) (p q : R →ₐ[K] ℂ), Smooth s → IsOpenImmersion i → i ≫ s = spMap (algebraMap K R) → SameComp s (algebraMap K ℂ) (spMap p.toRingHom ≫ i) (spMap q.toRingHom ≫ i) → ∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) q (fun _ _ => Commute.all _ _) e := by
  intro K _ _ X s R _ _ i p q hs hi his ⟨hp, hq, hpq⟩ e he
  let T := ℂ ⊗[K] R
  let j : Sp T ⟶ pullback s (spMap (algebraMap K ℂ)) :=
    (pullbackSpecIso K ℂ R).inv ≫ (pullbackSymmetry _ _).hom ≫
    pullback.map (spMap (algebraMap K R)) (spMap (algebraMap K ℂ)) s (spMap (algebraMap K ℂ)) i (𝟙 _) (𝟙 _)
      (by rw [his, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  haveI : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  let iL : ℂ →+* T := Algebra.TensorProduct.includeLeftRingHom
  let iR : R →+* T := (Algebra.TensorProduct.includeRight (R := K) (A := ℂ) (B := R) : R →+* T)
  have hj1 : j ≫ pullback.fst _ _ = spMap iR ≫ i := by
    simp only [j, Category.assoc, pullback.lift_fst]
    rw [pullbackSymmetry_hom_comp_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  have hj2 : j ≫ pullback.snd _ _ = spMap iL := by
    simp only [j, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst]
  have hl : ∀ (r : R →ₐ[K] ℂ) (hr : (spMap r.toRingHom ≫ i) ≫ s = 𝟙 _ ≫ spMap (algebraMap K ℂ)),
      pullback.lift (spMap r.toRingHom ≫ i) (𝟙 _) hr =
        spMap (Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) r (fun _ _ => Commute.all _ _)).toRingHom ≫ j := by
    intro r hr
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hj1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      ext x
      change r x = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) r (fun _ _ => Commute.all _ _) (1 ⊗ₜ[K] x)
      rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    · rw [pullback.lift_snd, Category.assoc, hj2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
      congr 1
      ext x
      change (x : ℂ) = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) r (fun _ _ => Commute.all _ _) ((x : ℂ) ⊗ₜ[K] 1)
      rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      rfl
  let z : PrimeSpectrum ℂ := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 := hpq z
  have hC := isPreirreducible_connectedComponent_of_smooth (pullback.snd s (spMap (algebraMap K ℂ)))
    (pullback.lift (spMap q.toRingHom ≫ i) (𝟙 _) hq z)
  have h2 := mem_connectedComponent (x := pullback.lift (spMap q.toRingHom ≫ i) (𝟙 _) hq z)
  generalize connectedComponent (pullback.lift (spMap q.toRingHom ≫ i) (𝟙 _) hq z) = C at h1 h2 hC
  rw [hl] at h1 h2
  exact apply_eq_of_isPreirreducible _ _ (j ⁻¹' C) (hC.preimage j.isOpenEmbedding) z h1 h2 e he

end GlobalTheory.KeyFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

noncomputable section
namespace GlobalTheory.KeyKa.KosBasis
variable {K : Type} [CommRing K]

abbrev lf (x : KeyIn K) {l : ℕ} (s : RR x l) (c : x.P.L.ι) : Γ(x.P.A.left, x.P.L.U c) := s.f c

def phi (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (v : Fin N → K) (c : x.P.L.ι) :
    Γ(x.P.A.left, x.P.L.U c) := ∑ k, cst x.P.A.hom (x.P.L.U c) (v k) * lf x (b k) c

theorem phi_add (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (v w : Fin N → K) (c) :
    phi x b (v + w) c = phi x b v c + phi x b w c := by
  simp only [phi, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem phi_zero (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (c) : phi x b 0 c = 0 := by
  simp only [phi, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]

theorem phi_sum (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) {A : Type} (S : Finset A)
    (v : A → Fin N → K) (c) : phi x b (∑ i ∈ S, v i) c = ∑ i ∈ S, phi x b (v i) c := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, phi_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, phi_add, ih]

def sec (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (v : Fin N → K) : RR x l where
  f := fun c => phi x b v c
  compat := fun i j => by
    obtain ⟨u, hu⟩ : ∃ u : Γ(x.P.A.left, x.P.L.U i ⊓ x.P.L.U j), u = ((pw x.P.L (l : ℤ)).g i j).val :=
      ⟨_, rfl⟩
    have h : ∀ k, rs x.P.A.left (inf_le_left : x.P.L.U i ⊓ x.P.L.U j ≤ _) (lf x (b k) i) =
        u * rs x.P.A.left (inf_le_right : x.P.L.U i ⊓ x.P.L.U j ≤ _) (lf x (b k) j) :=
      fun k => hu ▸ (b k).compat i j
    have h' : rs x.P.A.left (inf_le_left : x.P.L.U i ⊓ x.P.L.U j ≤ _) (phi x b v i) =
        u * rs x.P.A.left (inf_le_right : x.P.L.U i ⊓ x.P.L.U j ≤ _) (phi x b v j) := by

      simp only [phi, map_sum, map_mul, rs_cst, h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    subst hu
    exact h'

theorem phi_inj (x : KeyIn K) {l N : ℕ} {b : Fin N → RR x l} (hb : IsBasis x b) {v w : Fin N → K}
    (h : ∀ c, phi x b v c = phi x b w c) : v = w :=
  (hb (sec x b v)).unique (fun _ => rfl) h

theorem phi_surj (x : KeyIn K) {l N : ℕ} {b : Fin N → RR x l} (hb : IsBasis x b) (y : RR x l) :
    ∃ v, ∀ c, lf x y c = phi x b v c := (hb y).exists

theorem phi_mulVec (x : KeyIn K) {n l : ℕ} {s : Fin x.P.g → RR x n}
    {b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)} {m} (hm : IsMul x l s b m)
    (i : Fin x.P.g) {j : ℕ} (hj : j < x.P.g) (v) (c) :
    phi x (b j) ((m i j (j + 1)).mulVec v) c = lf x (s i) c * phi x (b (j + 1)) v c := by
  have h : ∀ k, lf x (s i) c * lf x (b (j + 1) k) c =
      ∑ k', cst x.P.A.hom (x.P.L.U c) (m i j (j + 1) k' k) * lf x (b j k') c :=
    fun k => hm i j hj k c
  calc phi x (b j) ((m i j (j + 1)).mulVec v) c
      = ∑ k', ∑ k, cst x.P.A.hom (x.P.L.U c) (v k) *
          (cst x.P.A.hom (x.P.L.U c) (m i j (j + 1) k' k) * lf x (b j k') c) := by

        simp only [phi, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ k, cst x.P.A.hom (x.P.L.U c) (v k) * (lf x (s i) c * lf x (b (j + 1) k) c) := by
        rw [Finset.sum_comm]
        simp only [h, Finset.mul_sum]
    _ = _ := by
        simp only [phi, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring

theorem mem_iff {g : ℕ} {a b : ℕ} (i : Fin g) (M : Fin g → Matrix (Fin a) (Fin b) K) (y : Fin a → K) :
    y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (M i').mulVecLin) ↔
      ∃ t : Fin g → Fin b → K, y = ∑ i' ∈ Finset.univ.filter (· < i), (M i').mulVec (t i') := by
  have e : (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (M i').mulVecLin) =
      ⨆ i' ∈ Finset.univ.filter (· < i), LinearMap.range (M i').mulVecLin := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [e, Submodule.mem_iSup_finset_iff_exists_sum]
  constructor
  · rintro ⟨q, h⟩
    choose t ht using fun i' => (q i').2
    refine ⟨t, h.symm.trans (Finset.sum_congr rfl fun i' _ => (ht i').symm)⟩
  · rintro ⟨t, h⟩
    exact ⟨fun i' => ⟨(M i').mulVec (t i'), t i', rfl⟩, h.symm⟩

theorem koszul_exact_of_regular : ∀ (K : Type) [CommRing K] (x : KeyIn K) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ (i : Fin x.P.g) (j : ℕ), j + 1 + i ≤ x.P.g → ∀ (y : RR x (l - (j + 1) * n)) (ta : Fin x.P.g → RR x (l - (j + 1) * n)), (∀ c, (show Γ(x.P.A.left, x.P.L.U c) from (s i).f c) * (show Γ(x.P.A.left, x.P.L.U c) from y.f c) = ∑ i' ∈ Finset.univ.filter (· < i), (show Γ(x.P.A.left, x.P.L.U c) from (s i').f c) * (show Γ(x.P.A.left, x.P.L.U c) from (ta i').f c)) → ∃ tb : Fin x.P.g → RR x (l - (j + 2) * n), ∀ c, (show Γ(x.P.A.left, x.P.L.U c) from y.f c) = ∑ i' ∈ Finset.univ.filter (· < i), (show Γ(x.P.A.left, x.P.L.U c) from (s i').f c) * (show Γ(x.P.A.left, x.P.L.U c) from (tb i').f c)) → ∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p) := by
  intro K _ x n l s b m _ hb hm hreg
  refine GlobalTheory.T.koszul_exact_inl_nonempty_of_graded_regular K x.P.g (fun j => (l - j * n) ^ x.P.g) m ?_ ?_
  · intro i i' j hj
    refine Matrix.ext_of_mulVec_single fun k => ?_
    refine phi_inj x (hb j (by omega)) fun c => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, phi_mulVec x hm i (by omega),
      phi_mulVec x hm i' (by omega), phi_mulVec x hm i' (by omega), phi_mulVec x hm i (by omega)]
    ring
  · intro i j y hj hy
    have hjg : j < x.P.g := by omega
    obtain ⟨t, ht⟩ := (mem_iff i (fun i' => m i' j (j + 1)) _).1 hy
    refine (mem_iff i (fun i' => m i' (j + 1) (j + 2)) _).2 ?_
    obtain ⟨tb, htb⟩ := hreg i j hj (sec x (b (j + 1)) y) (fun i' => sec x (b (j + 1)) (t i')) (fun c => by
      change lf x (s i) c * phi x (b (j + 1)) y c =
        ∑ i' ∈ Finset.univ.filter (· < i), lf x (s i') c * phi x (b (j + 1)) (t i') c
      rw [← phi_mulVec x hm i hjg, ht, phi_sum]
      exact Finset.sum_congr rfl fun i' _ => phi_mulVec x hm i' hjg _ _)
    have htb' : ∀ c, phi x (b (j + 1)) y c =
        ∑ i' ∈ Finset.univ.filter (· < i), lf x (s i') c * lf x (tb i') c := htb
    by_cases h2 : j + 2 ≤ x.P.g
    · choose u hu using fun i' => phi_surj x (hb (j + 2) h2) (tb i')
      refine ⟨u, phi_inj x (hb (j + 1) (by omega)) fun c => ?_⟩
      rw [htb', phi_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [hu]
      exact (phi_mulVec x hm i' (j := j + 1) (by omega) _ _).symm
    · have he : Finset.univ.filter (· < i) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun i' _ h => ?_
        have : (i' : ℕ) < i := h
        omega
      refine ⟨0, phi_inj x (hb (j + 1) (by omega)) fun c => ?_⟩
      rw [htb', he, Finset.sum_empty, Finset.sum_empty, phi_zero]

end GlobalTheory.KeyKa.KosBasis
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_perLev : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (g k : ℕ), P.g = g → ∃ (τ : Matrix (Fin g) (Fin g) ℂ) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PerLev P τ k lev := by
  rintro hU P g k rfl
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, hb, hW⟩ := hU P rig hrig
  let Q : u.Λ →+ (Fin P.g → ℂ) := u.Λ.subtype.toAddMonoidHom
  have hrange : Set.range Q = (u.Λ : Set (Fin P.g → ℂ)) := Subtype.range_coe
  have hQ : Function.Injective Q ∧ DiscreteTopology Q.range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧
      Hm.IsHermitian ∧ (∀ z : Fin P.g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm (Q x) (Q y)).im = Ef x y := by
    refine ⟨Subtype.val_injective, ?_, hrange ▸ u.full, hAH.1, hAH.2.1, fun x y => (hE x y).symm⟩
    have h := u.discrete
    change DiscreteTopology (Set.range Q)
    rw [hrange]
    exact h
  obtain ⟨h1, h2, h3, h4⟩ := unimodular_symplectic_coordinates_and_lattice_rank.2 _ Ef _ Q Hm hQ
  obtain ⟨bas, hbas⟩ := unimodular_symplectic_coordinates_and_lattice_rank.1 _ Ef _ hb h4 h3
  obtain ⟨h, τ, hh, -, -, hs, hp, -, hper⟩ := SiegelPeriod.exists_siegel_form _ Ef _ bas Q Hm hbas hQ
  let ψ : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ) := LinearEquiv.ofBijective h.mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.2 hh, Matrix.mulVec_surjective_iff_isUnit.2 hh⟩
  have hψ : ∀ a, ψ.symm (per τ a) = (bas a : Fin P.g → ℂ) := fun a => by
    rw [LinearEquiv.symm_apply_eq]
    exact (hper a).symm
  obtain ⟨u', hex, hΛ, -⟩ := exists_holUnif_reparam P.A P.L P.g u ψ.symm (fun _ => 1)
    (differentiable_const _) (fun _ => one_ne_zero) rfl
  refine ⟨τ, fun a => u'.ex ((k : ℂ)⁻¹ • per τ a), rfl, hs, hp, u', fun z => ?_, fun n a b c hn hc => ?_,
    fun _ => rfl⟩
  · rw [hΛ]
    constructor
    · intro hz
      refine ⟨bas.symm ⟨_, hz⟩, ψ.symm.injective ?_⟩
      rw [hψ, LinearEquiv.apply_symm_apply]
    · rintro ⟨a, rfl⟩
      rw [hψ]
      exact (bas a).2
  · rw [hex, hex, map_smul, map_smul, hψ, hψ]
    exact hW n (bas a) (bas b) c hn (by rw [hbas]; exact hc)

end GlobalTheory.KeyFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem sameComp_of_isHolTo : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsPreconnected B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ∀ b ∈ B, ∀ b' ∈ B, SameComp s σ (y b) (y b') := by
  intro K _ σ X s m B y hB hc hs hy b hb b' hb'
  classical
  have hs' : ∀ w ∈ B, y w ≫ s = 𝟙 _ ≫ spMap σ := fun w hw => by rw [Category.id_comp]; exact hs w hw
  let c : (Fin m → ℂ) → (Sp ℂ ⟶ pullback s (spMap σ)) := fun w =>
    if h : w ∈ B then pullback.lift (y w) (𝟙 _) (hs' w h) else pullback.lift (y b) (𝟙 _) (hs' b hb)
  have hcw : ∀ w (h : w ∈ B), c w = pullback.lift (y w) (𝟙 _) (hs' w h) := fun w h => dif_pos h
  have h1 : ∀ w ∈ B, c w ≫ pullback.fst s (spMap σ) = y w := fun w h => by rw [hcw w h, pullback.lift_fst]
  have h2 : ∀ w, c w ≫ pullback.snd s (spMap σ) = 𝟙 _ := fun w => by
    by_cases h : w ∈ B
    · rw [hcw w h, pullback.lift_snd]
    · rw [show c w = pullback.lift (y b) (𝟙 _) (hs' b hb) from dif_neg h, pullback.lift_snd]
  have hopen : ∀ U : (pullback s (spMap σ)).Opens, IsOpen {w | w ∈ B ∧ ⊤ ≤ c w ⁻¹ᵁ U} := fun U => by
    refine (GlobalTheory.holFamily_of_isPullback GlobalTheory.valAt'_rules B (IsPullback.of_hasPullback s (spMap σ)) c
      (fun U f => ?_) (fun U f => ?_) U 0).1
    · have e : {w | w ∈ B ∧ ⊤ ≤ (c w ≫ pullback.fst s (spMap σ)) ⁻¹ᵁ U} = {w | w ∈ B ∧ ⊤ ≤ y w ⁻¹ᵁ U} := by
        ext w
        simp only [Set.mem_setOf_eq]
        exact and_congr_right fun h => by rw [h1 w h]
      rw [e]
      exact ⟨(hy U f).1, (hy U f).2.congr fun w hw => by rw [h1 w hw.1]⟩
    · simp only [h2]
      refine ⟨?_, differentiableOn_const _⟩
      by_cases h : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U
      · simpa only [h, and_true, Set.setOf_mem_eq] using hB
      · simp only [h, and_false, Set.setOf_false, isOpen_empty]
  have hcont : ContinuousOn (fun w => c w (default : PrimeSpectrum ℂ)) B := by
    rw [continuousOn_open_iff hB]
    intro t ht
    convert hopen ⟨t, ht⟩ using 1
    ext w
    simp only [Set.mem_setOf_eq, GlobalTheory.top_le_preimage_iff_mem]
    rfl
  refine ⟨hs' b hb, hs' b' hb', fun z => ?_⟩
  obtain rfl : z = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  rw [← hcw b hb, ← hcw b' hb']
  exact (hc.image _ hcont).subset_connectedComponent ⟨b', hb', rfl⟩ ⟨b, hb, rfl⟩

end GlobalTheory.KeyFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem exists_enum_ker_transpose : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ ξ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x, (∀ I I', I ≠ I' → ∀ p : Sp K, ∃ r, (ξ I r).left p ≠ (ξ I' r).left p) ∧ (∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1) := by
  intro laws K _ _ x m al hm hal
  classical
  haveI := x.P.isAb.comm
  haveI := x.P.isAb.smooth
  haveI : LocallyOfFiniteType x.P.A.hom := inferInstance
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm Nat.cast_zero
  letI : CommGroup (Pt x) := Hom.commGroup
  have hG : ∀ k : ℕ, k ∣ m → Nat.card {y : Pt x // y ^ k = 1} = k ^ (2 * x.P.g) := by
    rintro k ⟨l, rfl⟩
    have hk : (k : K) ≠ 0 := fun h => hm (by rw [Nat.cast_mul, h, zero_mul])
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h => hk (by rw [h, Nat.cast_zero])
    exact (laws.mulN (Sp K) x.P k hk1).2.2.2.2 K (𝟙 _) hk
  have hcard := GlobalTheory.card_ker_int_matrix_four (Pt x) m (2 * x.P.g) al (Nat.pos_of_ne_zero hm0) hal hG
  have hfin : Finite {ξ : Fin 4 → Pt x // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hm0)
  have hc : Nat.card (Fin 4 → Fin (m ^ x.P.g)) =
      Nat.card {ξ : Fin 4 → Pt x // ∀ c, ∏ r', ξ r' ^ al r' c = 1} := by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    congr 1
    ring
  obtain ⟨e⟩ := Finite.card_eq.mp hc
  refine ⟨fun I => (e I).1, fun I I' hI p => ?_, fun I c => ?_⟩
  · by_contra hne
    push_neg at hne
    refine hI (e.injective (Subtype.ext (funext fun r => ?_)))
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst hp
    exact Over.OverMorphism.ext
      (ext_of_apply_closedPoint_eq x.P.A.hom (Over.w _) (Over.w _) (hne r))
  · rw [List.prod_ofFn]
    exact (e I).2 c

end GlobalTheory.KeyKa
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_holomorphicUniformisation_powerThetaKeyDatum : ∀ (x y : KeyIn ℂ) (j : ℕ) (u : HolUnif x.P.A x.P.L x.P.g) (θ : (Fin x.P.g → ℂ) → ℂ) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.IsKeyPow y x j → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) → ∃ (e : Fin j × Fin x.P.g ≃ Fin y.P.g) (u' : HolUnif y.P.A y.P.L y.P.g), (∀ z, z ∈ u'.Λ ↔ ∀ i, (fun k => z (e (i, k))) ∈ u.Λ) ∧ u'.IsRig y.rig ∧ u'.IsFn y.th (fun z => ∏ i, θ (fun k => z (e (i, k)))) ∧ ∀ p, u'.IsDiff (fun q => if (e.symm p).1 = (e.symm q).1 then W (e.symm p).2 (e.symm q).2 else 0) (y.v p) := by
  first | exact @GlobalTheory.PowUnif.exists_holUnif_pow | exact GlobalTheory.PowUnif.exists_holUnif_pow | (intros; apply GlobalTheory.PowUnif.exists_holUnif_pow <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem keyIn_normal_form_and_archimedean_constant :
    ThetaUnifAV → ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
      u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
      IsAddFundamentalDomain u.Λ Fd volume →
      nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
      nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
      ∃ (u' : HolUnif x.P.A x.P.L x.P.g) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
        τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧
        (∀ z, z ∈ u'.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
        u'.IsRig x.rig ∧ c ≠ 0 ∧ u'.IsFn x.th (fun z => c * thetaChar τ a b z) ∧ M.det ≠ 0 ∧
        (∀ i, u'.IsDiff ((2 * Real.pi * Complex.I)⁻¹ • M i) (x.v i)) ∧
        ‖M.det ^ 4 / c ^ 8‖ * nth ^ 4 * nη ^ 2 = (2 * Real.pi) ^ (2 * x.P.g) :=
  KeyNormalForm.normal_form_of_parts unimodular_and_tangent_of_isAH isDiff_sum_smul_of_isLieComb
    isThetaFn_and_ne_zero_of_isFn exists_eq_mul_canonical_theta_of_sign_multiplier
    volume_fundamentalDomain_periodLattice setIntegral_periodLattice_eq_volume_mul_cube

end GlobalTheory
end
