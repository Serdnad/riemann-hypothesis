module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle012
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle017
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle018
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle158
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
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle035

@[expose] public section

section

open IsLocalRing GlobalTheory.Henselisation

theorem _root_.GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsDirected (EtNbhd R) (· ≤ ·) := by
  first | exact @GlobalTheory.Henselisation.etNbhd_isDirected | exact GlobalTheory.Henselisation.etNbhd_isDirected | (intros; apply GlobalTheory.Henselisation.etNbhd_isDirected <;> assumption)
end

section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.Henselisation

namespace StageHensel

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem trans_algebraMap_eq_of_comp {i j : EtNbhd R} (hij : i ≤ j) (φ : i.A →ₐ[R] j.A)
    (hφ : j.pt.comp φ = i.pt) (a : i.A) :
    EtNbhd.trans hij (algebraMap i.A i.B a) = algebraMap j.A j.B (φ a) := by
  have h1 : EtNbhd.trans hij (algebraMap i.A i.B a) = algebraMap j.A j.B (hij.choose a) :=
    Localization.localRingHom_to_map _ _ _ _ _
  rw [h1]
  have key : (IsScalarTower.toAlgHom R j.A j.B).comp hij.choose =
      (IsScalarTower.toAlgHom R j.A j.B).comp φ := by
    apply GlobalTheory.EtaleHensel.algHom_eq_of_residue_eq
    intro x
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    rw [← sub_eq_zero, ← (residue j.B).map_sub (algebraMap j.A j.B (hij.choose x)) (algebraMap j.A j.B (φ x)), residue_eq_zero_iff, ← (algebraMap j.A j.B).map_sub (hij.choose x) (φ x),
      IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show _ ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (congr($(hij.choose_spec) x)).trans (congr($hφ x)).symm
  exact congr($key a)

end StageHensel


open StageHensel in
theorem exists_le_isRoot_of_simple_root (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R)
    (h : Polynomial i.A) (a₀ : i.A) (hm : h.Monic) (h0 : i.pt (h.eval a₀) = 0)
    (h1 : i.pt (h.derivative.eval a₀) ≠ 0) :
    ∃ (j : EtNbhd R) (hij : i ≤ j) (c : j.B),
      (h.map ((EtNbhd.trans hij).comp (algebraMap i.A i.B))).IsRoot c ∧
      c - EtNbhd.trans hij (algebraMap i.A i.B a₀) ∈ maximalIdeal j.B := by
  let P : StandardEtalePair i.A := ⟨h, hm, derivative h, ⟨1, 0, 1, by simp⟩⟩
  letI : Algebra R P.Ring := ((algebraMap i.A P.Ring).comp (algebraMap R i.A)).toAlgebra
  haveI : IsScalarTower R i.A P.Ring := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.Etale R P.Ring := Algebra.Etale.comp R i.A P.Ring
  letI : Algebra i.A (ResidueField R) := (i.pt : i.A →+* ResidueField R).toAlgebra
  haveI : IsScalarTower R i.A (ResidueField R) :=
    IsScalarTower.of_algebraMap_eq' (i.pt.comp_algebraMap).symm
  have hmap : P.HasMap (i.pt a₀) := by
    constructor
    · show eval₂ (i.pt : i.A →+* ResidueField R) ((i.pt : i.A →+* ResidueField R) a₀) h = 0
      rw [eval₂_at_apply]
      exact h0
    · show IsUnit (eval₂ (i.pt : i.A →+* ResidueField R)
        ((i.pt : i.A →+* ResidueField R) a₀) (derivative h))
      rw [eval₂_at_apply]
      exact isUnit_iff_ne_zero.2 h1
  let x : P.Ring →ₐ[R] ResidueField R := (P.lift _ hmap).restrictScalars R
  have hxA : ∀ a : i.A, x (algebraMap i.A P.Ring a) = i.pt a := fun a => (P.lift _ hmap).commutes a
  have hxX : x P.X = i.pt a₀ := P.lift_X _ hmap
  obtain ⟨n, f, hf⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType R P.Ring)
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let j : EtNbhd R := ⟨n, RingHom.ker f, Algebra.Etale.of_equiv e.symm, x.comp (e : _ →ₐ[R] P.Ring)⟩
  have hjpt : ∀ y : P.Ring, j.pt (e.symm y) = x y := fun y => by
    show x (e (e.symm y)) = x y
    rw [AlgEquiv.apply_symm_apply]
  let φ : i.A →ₐ[R] j.A := (e.symm : P.Ring →ₐ[R] j.A).comp (IsScalarTower.toAlgHom R i.A P.Ring)
  have hφa : ∀ a, φ a = e.symm (algebraMap i.A P.Ring a) := fun a => rfl
  have hφ : j.pt.comp φ = i.pt := AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, hφa, hjpt, hxA]
  refine ⟨j, ⟨φ, hφ⟩, algebraMap j.A j.B (e.symm P.X), ?_, ?_⟩
  · have hc : (EtNbhd.trans (⟨φ, hφ⟩ : i ≤ j)).comp (algebraMap i.A i.B) =
        ((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)).comp (algebraMap i.A P.Ring) :=
      RingHom.ext fun a => by
        rw [RingHom.comp_apply, trans_algebraMap_eq_of_comp _ φ hφ, hφa]
        rfl
    rw [hc, IsRoot, eval_map]
    have hX := (StandardEtalePair.hasMap_X (P := P)).1
    rw [aeval_def] at hX
    have : eval₂ (((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)).comp
        (algebraMap i.A P.Ring)) (algebraMap j.A j.B (e.symm P.X)) h =
        ((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)) (eval₂ (algebraMap i.A P.Ring) P.X h) := by
      rw [hom_eval₂]
      rfl
    rw [this]
    change _ = (0 : j.B)
    rw [show eval₂ (algebraMap i.A P.Ring) P.X h = 0 from hX, map_zero]
  · haveI : j.q.IsPrime := RingHom.ker_isPrime _
    rw [trans_algebraMap_eq_of_comp _ φ hφ, ← (algebraMap j.A j.B).map_sub (e.symm P.X) (φ a₀), IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show _ ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, hjpt, hxX, sub_eq_zero]
    exact (congr($hφ a₀)).symm

end GlobalTheory.Henselisation

end
end

section

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation.EtNbhd

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem algebraMap_comp_eq_of_pt {i j : EtNbhd R} (φ₁ φ₂ : i.A →ₐ[R] j.A)
    (h₁ : j.pt.comp φ₁ = i.pt) (h₂ : j.pt.comp φ₂ = i.pt) (a : i.A) :
    algebraMap j.A j.B (φ₁ a) = algebraMap j.A j.B (φ₂ a) := by
  let ψ₁ : i.A →ₐ[R] j.B := (IsScalarTower.toAlgHom R j.A j.B).comp φ₁
  let ψ₂ : i.A →ₐ[R] j.B := (IsScalarTower.toAlgHom R j.A j.B).comp φ₂
  have : ψ₁ = ψ₂ := by
    refine GlobalTheory.EtaleHensel.algHom_eq_of_residue_eq fun b => ?_
    rw [← sub_eq_zero, ← (residue j.B).map_sub (ψ₁ b) (ψ₂ b), residue_eq_zero_iff]
    show algebraMap j.A j.B (φ₁ b) - algebraMap j.A j.B (φ₂ b) ∈ maximalIdeal j.B
    rw [← (algebraMap j.A j.B).map_sub (φ₁ b) (φ₂ b), IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show φ₁ b - φ₂ b ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (congr($h₁ b)).trans (congr($h₂ b)).symm
  exact congr($this a)

theorem trans_algebraMap_eq_of_pt {i j : EtNbhd R} (h : i ≤ j) (φ : i.A →ₐ[R] j.A)
    (hφ : j.pt.comp φ = i.pt) (a : i.A) :
    trans h (algebraMap i.A i.B a) = algebraMap j.A j.B (φ a) := by
  unfold trans
  rw [Localization.localRingHom_to_map]
  exact algebraMap_comp_eq_of_pt _ _ h.choose_spec hφ a

end GlobalTheory.Henselisation.EtNbhd

namespace GlobalTheory.Henselisation

theorem trans_system : ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ (i : EtNbhd R) (x : i.B), EtNbhd.trans (le_refl i) x = x) ∧ ∀ (i j k : EtNbhd R) (hij : i ≤ j) (hjk : j ≤ k) (x : i.B), EtNbhd.trans hjk (EtNbhd.trans hij x) = EtNbhd.trans (hij.trans hjk) x := by
  intro R _ _
  refine ⟨fun i x => ?_, fun i j k hij hjk x => ?_⟩
  · have : EtNbhd.trans (le_refl i) = RingHom.id i.B :=
      IsLocalization.ringHom_ext i.q.primeCompl (RingHom.ext fun a => by
        simp only [RingHom.comp_apply, RingHom.id_apply]
        exact EtNbhd.trans_algebraMap_eq_of_pt _ (AlgHom.id R i.A) (AlgHom.comp_id _) a)
    exact congr($this x)
  · have : (EtNbhd.trans hjk).comp (EtNbhd.trans hij) = EtNbhd.trans (hij.trans hjk) :=
      IsLocalization.ringHom_ext i.q.primeCompl (RingHom.ext fun a => by
        simp only [RingHom.comp_apply]
        rw [EtNbhd.trans_algebraMap_eq_of_pt hij hij.choose hij.choose_spec,
          EtNbhd.trans_algebraMap_eq_of_pt hjk hjk.choose hjk.choose_spec,
          EtNbhd.trans_algebraMap_eq_of_pt (hij.trans hjk) (hjk.choose.comp hij.choose)
            (by rw [← AlgHom.comp_assoc, hjk.choose_spec, hij.choose_spec])]
        rfl)
    exact congr($this x)

end GlobalTheory.Henselisation
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.cocompact_fibration_section_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (Λ : AddSubgroup V) (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ (A : Set N') (B : Set V), MeasurableSet A → MeasurableSet B →
      (∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A) → (∀ v : V, ∃! w : Λ, (w : V) + v ∈ B) →
      ∀ ν : MeasureTheory.Measure N, MeasureTheory.IsFundamentalDomain (Γ.subgroupOf N)
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker '' (A ×ˢ B)) ν := by
  first | exact @GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod | exact GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod | (intros; apply GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod <;> assumption)
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.exists_finite_algebra_splitting_normForm : ∀ (A B K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [CharZero K] [Algebra A K] [Algebra B L] [Algebra K L] [FiniteDimensional K L]
    [IsFractionRing A K] [IsFractionRing B L] (φ : A →+* B), φ.Finite →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp φ →
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra A R), Function.Injective (algebraMap A R) ∧ Module.Finite A R ∧
      ∃ σ : Fin (Module.finrank K L) → (B →+* R), (∀ j, (σ j).comp φ = algebraMap A R) ∧
        ∀ (m : ℕ) (g : Fin m → B), ∃ P : MvPolynomial (Fin m) A,
          P.map (algebraMap A K) = GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i)) ∧
          P.map (algebraMap A R) = ∏ j, ∑ i, C (σ j (g i)) * X i := by
  first | exact @GlobalTheory.NormSheaf.exists_finite_split_normForm | exact GlobalTheory.NormSheaf.exists_finite_split_normForm | (intros; apply GlobalTheory.NormSheaf.exists_finite_split_normForm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

theorem _root_.GlobalTheory.T.hilbert_point_eq_of_open_cover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x x' : GlobalTheory.HilbGlue.HPt z r Y), (∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x = GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x') → x = x' := by
  first | exact @GlobalTheory.HilbGlue.HPt.ext_openCover | exact GlobalTheory.HilbGlue.HPt.ext_openCover | (intros; apply GlobalTheory.HilbGlue.HPt.ext_openCover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.affineHilbert_representing_universal_subscheme : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ∃ (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (R.homEquiv (𝟙 H)).1), IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ Flat (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ (∀ y, (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ (R.homEquiv (𝟙 H)).1 = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbAff.universal) | (exact GlobalTheory.HilbAff.universal) | (intros; apply GlobalTheory.HilbAff.universal  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

theorem _root_.GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_openCover : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    {T : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ T),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : T, ∃ i y, f i y = x) →
    ∀ (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData),
    (∀ i, GlobalTheory.HilbAff.Good A B r (f i ≫ g) (I.comap (GlobalTheory.HilbAff.bc A B g (f i)))) →
    GlobalTheory.HilbAff.Good A B r g I := by
  first | (exact @GlobalTheory.HilbAff.good_of_cover) | (exact GlobalTheory.HilbAff.good_of_cover) | (intros; apply GlobalTheory.HilbAff.good_of_cover  <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

namespace GlobalTheory.HilbGlue

section
variable {S Z : Scheme.{0}} (z : Z ⟶ S)

theorem bc_fst {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    bc z c g k w ≫ pullback.fst z g = pullback.fst z k := by
  simp only [bc, pullback.map, pullback.lift_fst, Category.comp_id]

theorem bc_snd {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    bc z c g k w ≫ pullback.snd z g = pullback.snd z k ≫ c := by
  simp only [bc, pullback.map, pullback.lift_snd]

end

theorem isFinFlatRk_of_cover {V Y : Scheme.{0}} (g : V ⟶ Y) (𝒰 : Y.OpenCover) (r : ℕ)
    (h : ∀ i, ∃ (Q : Scheme.{0}) (p : Q ⟶ V) (q : Q ⟶ 𝒰.X i), IsPullback p q g (𝒰.f i) ∧ IsFinFlatRk q r) :
    IsFinFlatRk g r := by
  choose Q p q hP hq using h
  have i1 : IsZariskiLocalAtTarget @IsFinite.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have i2 : IsZariskiLocalAtTarget @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  have hq' : ∀ i, IsFinFlatRk (pullback.snd g (𝒰.f i)) r := fun i => by
    rw [← (hP i).isoPullback_inv_snd]
    exact (hq i).iso_comp _
  have hF : IsFinite g := IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) 𝒰 fun i => (hq' i).1
  have hL : Flat g := IsZariskiLocalAtTarget.of_openCover (P := @Flat) 𝒰 fun i => (hq' i).2.1
  refine ⟨hF, hL, fun y => ?_⟩
  obtain ⟨i, y', rfl⟩ := 𝒰.exists_eq y
  rw [← Scheme.Hom.finrank_of_isPullback (p i) (q i) g (𝒰.f i) (hP i) y', (hq i).2.2]

theorem HPt.exists_glue : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x : ∀ i, GlobalTheory.HilbGlue.HPt z r (𝒰.X i)), (∀ i j (R : Scheme.{0}) (b : R ⟶ 𝒰.X i) (c : R ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → GlobalTheory.HilbGlue.HPt.map b (x i) = GlobalTheory.HilbGlue.HPt.map c (x j)) → ∃ y : GlobalTheory.HilbGlue.HPt z r Y, ∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) y = x i := by
  intro S Z z r Y 𝒰 x hx
  obtain ⟨f, hf⟩ : ∃ f : Y ⟶ S, ∀ i, 𝒰.f i ≫ f = (x i).1 :=
    ⟨𝒰.glueMorphisms (fun i => (x i).1) fun i j =>
      congrArg Sigma.fst (hx i j _ _ _ pullback.condition), fun i => 𝒰.ι_glueMorphisms _ _ i⟩
  let e : ∀ i, pullback z (x i).1 ⟶ pullback z f := fun i => bc z (𝒰.f i) f (x i).1 (hf i)
  have hP : ∀ i, IsPullback (e i) (pullback.snd z (x i).1) (pullback.snd z f) (𝒰.f i) :=
    fun i => isPullback_bc z _ _ _ (hf i)
  have he : ∀ i, IsOpenImmersion (e i) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hP i).flip inferInstance
  have hcov : ∀ p : ↥(pullback z f), ∃ i, p ∈ Set.range (e i) := by
    intro p
    obtain ⟨i, y', hy'⟩ := 𝒰.exists_eq (pullback.snd z f p)
    obtain ⟨q, hq⟩ : p ∈ Set.range (pullback.fst (pullback.snd z f) (𝒰.f i)) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨y', hy'⟩
    refine ⟨i, (hP i).isoPullback.inv q, ?_⟩
    rw [← hq, ← Scheme.Hom.comp_apply, (hP i).isoPullback_inv_fst]
  have fi : ∀ i, e i ≫ pullback.fst z f = pullback.fst z (x i).1 := fun i => by
    simp only [e, bc, pullback.map, pullback.lift_fst, Category.comp_id]
  have hK : ∀ i j (Q : Scheme.{0}) (a : Q ⟶ pullback z (x i).1) (b : Q ⟶ pullback z (x j).1),
      a ≫ e i = b ≫ e j → (x i).2.1.comap a = (x j).2.1.comap b := by
    intro i j Q a b hab
    have hbc : (a ≫ pullback.snd z (x i).1) ≫ 𝒰.f i = (b ≫ pullback.snd z (x j).1) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← (hP i).w, ← (hP j).w, reassoc_of% hab]
    have H := hx i j Q _ _ hbc
    have w : (a ≫ pullback.snd z (x i).1) ≫ (x i).1 = (b ≫ pullback.snd z (x j).1) ≫ (x j).1 :=
      congrArg Sigma.fst H
    have H' := (HPt.map_eq_mk_iff _ (x i) w ((x j).2.pull _ rfl)).1 H
    have hs : (a ≫ pullback.fst z (x i).1) ≫ z = 𝟙 Q ≫ (b ≫ pullback.snd z (x j).1) ≫ (x j).1 := by
      rw [Category.id_comp, ← w, Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨s, hs1, hs2⟩ : ∃ s : Q ⟶ pullback z ((b ≫ pullback.snd z (x j).1) ≫ (x j).1),
        s ≫ pullback.fst _ _ = a ≫ pullback.fst z (x i).1 ∧ s ≫ pullback.snd _ _ = 𝟙 Q :=
      ⟨pullback.lift _ _ hs, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hfst : a ≫ pullback.fst z (x i).1 = b ≫ pullback.fst z (x j).1 := by
      rw [← fi i, ← fi j, reassoc_of% hab]
    have ha : a = s ≫ bc z (a ≫ pullback.snd z (x i).1) (x i).1 _ w := by
      apply pullback.hom_ext
      · rw [Category.assoc, bc_fst, hs1]
      · rw [Category.assoc, bc_snd, reassoc_of% hs2]
    have hb : b = s ≫ bc z (b ≫ pullback.snd z (x j).1) (x j).1 _ rfl := by
      apply pullback.hom_ext
      · rw [Category.assoc, bc_fst, hs1, hfst]
      · rw [Category.assoc, bc_snd, reassoc_of% hs2]
    have e1 : (x i).2.1.comap a = ((x i).2.1.comap (bc z (a ≫ pullback.snd z (x i).1) (x i).1 _ w)).comap s := by
      rw [← Scheme.IdealSheafData.comap_comp, ← ha]
    have e2 : (x j).2.1.comap b = ((x j).2.1.comap (bc z (b ≫ pullback.snd z (x j).1) (x j).1 _ rfl)).comap s := by
      rw [← Scheme.IdealSheafData.comap_comp, ← hb]
    rw [e1, e2, H']
    rfl
  obtain ⟨I, hI⟩ := GlobalTheory.T.exists_idealSheafData_glue_of_openImmersions GlobalTheory.T.exists_idealSheafData_of_compatible_ideals (ι := 𝒰.I₀) (fun i : 𝒰.I₀ => pullback z (x i).1) e he hcov (fun i : 𝒰.I₀ => (x i).2.1) hK
  have hfr : IsFinFlatRk (I.subschemeι ≫ pullback.snd z f) r := by
    refine isFinFlatRk_of_cover _ 𝒰 r fun i => ⟨(I.comap (e i)).subscheme, _, _,
      (isPullback_comap I (e i)).flip.paste_vert (hP i), ?_⟩
    have := (x i).2.2
    rw [← hI i] at this
    exact this
  refine ⟨⟨f, I, hfr⟩, fun i => ?_⟩
  exact (HPt.map_eq_mk_iff (𝒰.f i) ⟨f, I, hfr⟩ (hf i) (x i).2).2 (hI i)

end GlobalTheory.HilbGlue
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

theorem _root_.GlobalTheory.T.isProper_of_represents_hilbertFunctor_of_local : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (H : Scheme.{0}) (u : GlobalTheory.HilbGlue.HPt z r H), (∀ (T : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r T), ∃! c : T ⟶ H, GlobalTheory.HilbGlue.HPt.map c u = x) → (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x) → IsProper u.1 := by
  first | (exact @GlobalTheory.HilbGlue.isProper_of_represents_of_local_proper) | (exact GlobalTheory.HilbGlue.isProper_of_represents_of_local_proper) | (intros; apply GlobalTheory.HilbGlue.isProper_of_represents_of_local_proper  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.affineHilbert_valuativeCriterion_uniqueness : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ValuativeCriterion.Uniqueness (R.homEquiv (𝟙 H)).1 := by
  first | exact @GlobalTheory.HilbAff.valuativeCriterion_uniqueness | exact GlobalTheory.HilbAff.valuativeCriterion_uniqueness | (intros; apply GlobalTheory.HilbAff.valuativeCriterion_uniqueness <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem _root_.GlobalTheory.T.exists_mem_good_of_closedImmersions : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂] (x : Y₀), ∃ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, x ∈ U := by
  first | exact @GlobalTheory.FerrandPush.exists_good_mem | exact GlobalTheory.FerrandPush.exists_good_mem | (intros; apply GlobalTheory.FerrandPush.exists_good_mem <;> assumption)
end
