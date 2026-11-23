module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle004
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.RingTheory.TotallySplit
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
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS

@[expose] public section

section

noncomputable section

open MvPowerSeries

namespace GlobalTheory.FrameBiextId

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {d : ℕ}


variable (k d) in
def Q (n : ℕ) : AddSubgroup (Pt k n d) where
  carrier := {p | ∀ i, constantCoeff (p i) = 0}
  add_mem' := fun ha hb i => by rw [Pi.add_apply, map_add (f := _), ha i, hb i, add_zero]
  zero_mem' := fun _ => map_zero _
  neg_mem' := fun ha i => by rw [Pi.neg_apply, map_neg, ha i, neg_zero]

variable {n l : ℕ}

def gen (j : Fin n) : Q (k := k) (d := d) n := ⟨pt k d j, CZ.pt j⟩

theorem czQ (b : Fin n → Q (k := k) (d := d) l) : CZ (fun j => (b j).1) := by
  intro j i
  exact (b j).2 i

def sb (b : Fin n → Q (k := k) (d := d) l) : PS k n d →+* PS k l d := evHom (czQ b)

theorem sb_apply (b : Fin n → Q (k := k) (d := d) l) (f : PS k n d) : sb b f = ev (fun j => (b j).1) f := by
  unfold sb
  exact evHom_apply (czQ b) f

def sq (b : Fin n → Q (k := k) (d := d) l) : Q (k := k) (d := d) n →+ Q (k := k) (d := d) l where
  toFun p := ⟨fun i => sb b (p.1 i), fun i =>
    (congrArg constantCoeff (sb_apply b _)).trans (constantCoeff_ev (czQ b) (p.2 i))⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

@[simp] theorem sq_gen (b : Fin n → Q (k := k) (d := d) l) (j : Fin n) : sq b (gen j) = b j := by
  apply Subtype.ext
  funext i
  show sb b (X (j, i)) = (b j).1 i
  rw [sb_apply]
  exact ev_X (czQ b) j i

theorem sb_sb {m : ℕ} (b : Fin n → Q (k := k) (d := d) l) (a : Fin m → Q (k := k) (d := d) n) (f : PS k m d) :
    sb b (sb a f) = sb (fun j => sq b (a j)) f := by
  simp only [sb_apply]
  rw [ev_ev (czQ b) (czQ a)]
  congr 1
  funext j i
  show ev (fun j => (b j).1) ((a j).1 i) = sb b ((a j).1 i)
  rw [sb_apply]

theorem sb_gen (f : PS k n d) : sb gen f = f := by
  rw [sb_apply]
  exact ev_pt f

def E2 (f : PS k 2 d) (u v : Q (k := k) (d := d) n) : PS k n d := sb ![u, v] f

def E3 (f : PS k 3 d) (u v w : Q (k := k) (d := d) n) : PS k n d := sb ![u, v, w] f

@[simp] theorem formalPointSubstitutionSeries_valueAtTwoPoints (b : Fin n → Q (k := k) (d := d) l) (f : PS k 2 d) (u v : Q (k := k) (d := d) n) : sb b (E2 f u v) = E2 f (sq b u) (sq b v) := by
  show sb b (sb ![u, v] f) = sb ![sq b u, sq b v] f
  have h : (fun j => sq b (![u, v] j)) = ![sq b u, sq b v] := by
    funext j
    fin_cases j <;> rfl
  rw [sb_sb, h]

@[simp] theorem formalPointSubstitutionSeries_valueAtThreePoints (b : Fin n → Q (k := k) (d := d) l) (f : PS k 3 d) (u v w : Q (k := k) (d := d) n) :
    sb b (E3 f u v w) = E3 f (sq b u) (sq b v) (sq b w) := by
  show sb b (sb ![u, v, w] f) = sb ![sq b u, sq b v, sq b w] f
  have h : (fun j => sq b (![u, v, w] j)) = ![sq b u, sq b v, sq b w] := by
    funext j
    fin_cases j <;> rfl
  rw [sb_sb, h]

theorem formalSeriesValueAtTwoPoints_genericPoints (f : PS k 2 d) : E2 f (gen 0) (gen 1) = f := by
  show sb ![gen 0, gen 1] f = f
  have h : (![gen 0, gen 1] : Fin 2 → Q (k := k) (d := d) 2) = gen := by
    funext j
    fin_cases j <;> rfl
  rw [h, sb_gen]

theorem formalSeriesValueAtThreePoints_genericPoints (f : PS k 3 d) : E3 f (gen 0) (gen 1) (gen 2) = f := by
  show sb ![gen 0, gen 1, gen 2] f = f
  have h : (![gen 0, gen 1, gen 2] : Fin 3 → Q (k := k) (d := d) 3) = gen := by
    funext j
    fin_cases j <;> rfl
  rw [h, sb_gen]

def ac (A : Q (k := k) (d := d) 1) (u : Q (k := k) (d := d) n) : Q (k := k) (d := d) n := sq ![u] A

@[simp] theorem sq_ac (b : Fin n → Q (k := k) (d := d) l) (A : Q (k := k) (d := d) 1) (u : Q (k := k) (d := d) n) : sq b (ac A u) = ac A (sq b u) := by
  apply Subtype.ext
  funext i
  show sb b (sb ![u] (A.1 i)) = sb ![sq b u] (A.1 i)
  have h : (fun j => sq b (![u] j)) = ![sq b u] := by
    funext j
    fin_cases j
    rfl
  rw [sb_sb, h]

theorem formalSeriesValueAtTwoPoints_eq_ev (f : PS k 2 d) (u v : Q (k := k) (d := d) n) : E2 f u v = ev ![u.1, v.1] f := by
  show sb ![u, v] f = _
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem formalSeriesValueAtThreePoints_eq_ev (f : PS k 3 d) (u v w : Q (k := k) (d := d) n) : E3 f u v w = ev ![u.1, v.1, w.1] f := by
  show sb ![u, v, w] f = _
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem ac_val (A : Q (k := k) (d := d) 1) (u : Q (k := k) (d := d) n) : (ac A u).1 = comp1 A.1 u.1 := by
  funext i
  show sb ![u] (A.1 i) = ev ![u.1] (A.1 i)
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j
  rfl

def op (F : Q (k := k) (d := d) 2) (u v : Q (k := k) (d := d) n) : Q (k := k) (d := d) n := sq ![u, v] F

theorem op_val (F : Q (k := k) (d := d) 2) (u v : Q (k := k) (d := d) n) : (op F u v).1 = addOf F.1 u.1 v.1 := by
  funext i
  show sb ![u, v] (F.1 i) = ev ![u.1, v.1] (F.1 i)
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem sq_op (b : Fin n → Q (k := k) (d := d) l) (F : Q (k := k) (d := d) 2) (u v : Q (k := k) (d := d) n) : sq b (op F u v) = op F (sq b u) (sq b v) := by
  apply Subtype.ext
  funext i
  show sb b (sb ![u, v] (F.1 i)) = sb ![sq b u, sq b v] (F.1 i)
  have h : (fun j => sq b (![u, v] j)) = ![sq b u, sq b v] := by
    funext j
    fin_cases j <;> rfl
  rw [sb_sb, h]

theorem gen_val (j : Fin n) : (gen j : Q (k := k) (d := d) n).1 = pt k d j := rfl

theorem ext_of_trunc {R σ : Type} [CommRing R] [Finite σ] {f g : MvPowerSeries σ R}
    (h : ∀ m : ℕ, Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ (m + 1)) (truncTotal (m + 1) f) =
      Ideal.Quotient.mk _ (truncTotal (m + 1) g)) : f = g := by
  ext e
  have h1 := h (Finsupp.degree e)
  rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff'] at h1
  have h2 := h1 e (Nat.lt_succ_self _)
  rw [MvPolynomial.coeff_sub, coeff_truncTotal _ (Nat.lt_succ_self _),
    coeff_truncTotal _ (Nat.lt_succ_self _), sub_eq_zero] at h2
  exact h2

end GlobalTheory.FrameBiextId
end
end

section

open NumberField

theorem _root_.GlobalTheory.T.exists_natCast_mem_differentIdeal_pow_le_discr_sq : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E], ∃ N : ℕ, 0 < N ∧ ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) ∧ (N : ℝ) ^ Module.finrank ℚ E ≤ |(NumberField.discr E : ℝ)| ^ 2 := by
  first | exact @GlobalTheory.exists_natCast_mem_differentIdeal_pow_le | exact GlobalTheory.exists_natCast_mem_differentIdeal_pow_le | (intros; apply GlobalTheory.exists_natCast_mem_differentIdeal_pow_le <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_coords_no_homogeneous_relation_generic_hyperplanes : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (m N : ℕ) (t : Fin m × Fin N → ℂ) (ζ : Fin N → ℂ), (∀ Q : MvPolynomial (Fin m × Fin N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → ζ ≠ 0 → (∀ i, ∑ j, t (i, j) * ζ j = 0) → ∃ jj : Fin (m + 1) → Fin N, ∀ (Q : MvPolynomial (Fin (m + 1)) K) (d : ℕ), Q ≠ 0 → Q.IsHomogeneous d → MvPolynomial.eval₂ σ (fun a => ζ (jj a)) Q ≠ 0 := by
  first | exact @GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero | exact GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero | (intros; apply GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
open scoped TensorProduct in
theorem _root_.GlobalTheory.exists_faithfullyFlat_pushout (F S S₁ S₂ : Type) [Field F] [CommRing S] [CommRing S₁]
    [CommRing S₂] [Algebra F S] [Algebra F S₁] [Algebra F S₂] (φ₁ : S →ₐ[F] S₁)
    (φ₂ : S →ₐ[F] S₂) (h : φ₂.toRingHom.FaithfullyFlat) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra F T) (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T),
      ψ₁.comp φ₁ = ψ₂.comp φ₂ ∧ ψ₁.toRingHom.FaithfullyFlat ∧ Function.Injective ψ₁ := by
  letI : Algebra S S₁ := φ₁.toRingHom.toAlgebra
  letI : Algebra S S₂ := φ₂.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S₂ := RingHom.faithfullyFlat_algebraMap_iff.1 h
  letI : Algebra F (S₁ ⊗[S] S₂) :=
    ((Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[S] S₂).comp
      (algebraMap F S₁)).toAlgebra
  have hff : (algebraMap S₁ (S₁ ⊗[S] S₂)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  refine ⟨S₁ ⊗[S] S₂, inferInstance, inferInstance,
    { (Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[S] S₂) with commutes' := fun c => rfl },
    { (Algebra.TensorProduct.includeRight : S₂ →ₐ[S] S₁ ⊗[S] S₂).toRingHom with
      commutes' := fun c => ?_ }, ?_, hff, hff.injective⟩
  · show (1 : S₁) ⊗ₜ[S] algebraMap F S₂ c = algebraMap F S₁ c ⊗ₜ[S] (1 : S₂)
    rw [← φ₁.commutes, ← φ₂.commutes]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap F S c)).symm
  · exact AlgHom.ext fun s => Algebra.TensorProduct.tmul_one_eq_one_tmul s

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
open scoped TensorProduct in
theorem _root_.GlobalTheory.existsUnique_preimage_of_faithfullyFlat (F S S' : Type) [Field F] [CommRing S]
    [CommRing S'] [Algebra F S] [Algebra F S'] (φ : S →ₐ[F] S')
    (h : φ.toRingHom.FaithfullyFlat) (w : S')
    (hw : ∀ (T : Type) [CommRing T] [Algebra F T] (ψ₁ ψ₂ : S' →ₐ[F] T),
      ψ₁.comp φ = ψ₂.comp φ → ψ₁ w = ψ₂ w) : ∃! v : S, φ v = w := by
  letI : Algebra S S' := φ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S' := RingHom.faithfullyFlat_algebraMap_iff.1 h
  have hinj := h.injective
  letI : Algebra F (S' ⊗[S] S') :=
    ((Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S').comp
      (algebraMap F S')).toAlgebra
  let ψ₁ : S' →ₐ[F] S' ⊗[S] S' :=
    { (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S') with commutes' := fun c => rfl }
  let ψ₂ : S' →ₐ[F] S' ⊗[S] S' :=
    { (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom with
      commutes' := fun c => by
        show (1 : S') ⊗ₜ[S] algebraMap F S' c = algebraMap F S' c ⊗ₜ[S] (1 : S')
        rw [← φ.commutes]
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap F S c)).symm }
  have hcomp : ψ₁.comp φ = ψ₂.comp φ :=
    AlgHom.ext fun s => Algebra.TensorProduct.tmul_one_eq_one_tmul s
  have hw' : w ⊗ₜ[S] (1 : S') = (1 : S') ⊗ₜ[S] w := hw (S' ⊗[S] S') ψ₁ ψ₂ hcomp
  obtain ⟨v, hv⟩ := (Algebra.IsEffective.of_faithfullyFlat S S' w).1
    (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]; exact hw')
  exact ⟨v, hv, fun v' hv' => hinj (hv'.trans hv.symm)⟩


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.faithfullyFlat_points_baseChange_descent : (∀ (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B), φ.Flat → (∀ (K : Type) [Field K] [IsAlgClosed K] (ψ : S →+* K), ∃ χ : B →+* K, χ.comp φ = ψ) → φ.FaithfullyFlat) ∧ (∀ (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B) (e : B), φ.Flat → ((algebraMap B (Localization.Away e)).comp φ).Flat) ∧ (∀ (F S S₁ S₂ : Type) [Field F] [CommRing S] [CommRing S₁] [CommRing S₂] [Algebra F S] [Algebra F S₁] [Algebra F S₂] (φ₁ : S →ₐ[F] S₁) (φ₂ : S →ₐ[F] S₂), φ₂.toRingHom.FaithfullyFlat → ∃ (T : Type) (_ : CommRing T) (_ : Algebra F T) (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T), ψ₁.comp φ₁ = ψ₂.comp φ₂ ∧ ψ₁.toRingHom.FaithfullyFlat ∧ Function.Injective ψ₁) ∧ ∀ (F S S' : Type) [Field F] [CommRing S] [CommRing S'] [Algebra F S] [Algebra F S'] (φ : S →ₐ[F] S'), φ.toRingHom.FaithfullyFlat → ∀ w : S', (∀ (T : Type) [CommRing T] [Algebra F T] (ψ₁ ψ₂ : S' →ₐ[F] T), ψ₁.comp φ = ψ₂.comp φ → ψ₁ w = ψ₂ w) → ∃! v : S, φ v = w := by
  refine ⟨fun S B _ _ φ hflat hpt => ?_, fun S B _ _ φ e hflat => ?_,
    fun F S S₁ S₂ _ _ _ _ _ _ _ φ₁ φ₂ h => _root_.GlobalTheory.exists_faithfullyFlat_pushout F S S₁ S₂ φ₁ φ₂ h,
    fun F S S' _ _ _ _ _ φ h w hw => _root_.GlobalTheory.existsUnique_preimage_of_faithfullyFlat F S S' φ h w hw⟩
  · rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨hflat, fun p => ?_⟩
    obtain ⟨χ, hχ⟩ := hpt (AlgebraicClosure p.asIdeal.ResidueField)
      ((algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
        (algebraMap S p.asIdeal.ResidueField))
    refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, PrimeSpectrum.ext ?_⟩
    show Ideal.comap φ (RingHom.ker χ) = p.asIdeal
    rw [RingHom.comap_ker, hχ, RingHom.ker_comp_of_injective _
      (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).injective,
      Ideal.ker_algebraMap_residueField]
  · exact RingHom.Flat.comp hflat (RingHom.flat_algebraMap_iff.2 inferInstance)

end GlobalTheory
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.ae_transcendental_point_nonvanishing : ∀ (K : Type) [Field K] [Countable K] (σ : K →+* ℂ) (ι : Type) [Fintype ι], ∀ᵐ t : ι → ℂ, ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0 := by
  first | exact @GlobalTheory.ae_eval₂_ne_zero_of_countable | exact GlobalTheory.ae_eval₂_ne_zero_of_countable | (intros; apply GlobalTheory.ae_eval₂_ne_zero_of_countable <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace TraceDualMin

theorem herm_one_eq {n : ℕ} (x y : Fin n → E) : herm 1 x y = ∑ k, x k * cc (y k) := by
  simp [herm, Matrix.one_apply]

theorem herm_smul_left {n : ℕ} (a : E) (x y : Fin n → E) :
    herm 1 (a • x) y = a * herm 1 x y := by
  simp [herm_one_eq, Finset.mul_sum, mul_assoc]

theorem herm_smul_right {n : ℕ} (a : E) (x y : Fin n → E) :
    herm 1 x (a • y) = cc a * herm 1 x y := by
  simp [herm_one_eq, Finset.mul_sum, cc, mul_left_comm]

theorem cc_cc (a : E) : cc (cc a) = a := by
  simp [cc]

theorem cc_herm_self {n : ℕ} (x : Fin n → E) : cc (herm 1 x x) = herm 1 x x := by
  simp [herm_one_eq, cc, mul_comm]

theorem trace_cc (a : E) : Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem isIntegral_cc {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (cc a) :=
  ha.map ((IsCMField.complexConj E).restrictScalars ℤ).toAlgHom

theorem embedding_herm_self {n : ℕ} (σ : E →+* ℂ) (x : Fin n → E) :
    σ (herm 1 x x) = ((∑ k, ‖σ (x k)‖ ^ 2 : ℝ) : ℂ) := by
  simp [herm_one_eq, cc, IsCMField.complexEmbedding_complexConj, Complex.mul_conj']


omit [IsCMField E] in
theorem mem_inv_different {x : E} (hx : ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (x * a) = k) :
    x ∈ (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
  rw [← dual_one_eq_inv_differentIdeal, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one,
    Submodule.mem_traceDual]
  intro a ha
  obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
  obtain ⟨k, hk⟩ := hx b
  exact ⟨k, by rw [Algebra.traceForm_apply]; simpa using hk.symm⟩

end TraceDualMin


open TraceDualMin in
theorem trace_dual_min {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ)
    (u : Fin n → E) (hu : u ≠ 0) (htr : ∀ y ∈ Λ, ∃ k : ℤ, Algebra.trace ℚ E (herm 1 u y) = k) :
    2 * (fdeg E : ℝ) / rdE E ^ 2 ≤ ∑ σ : E →+* ℂ, ∑ k, ‖σ (u k)‖ ^ 2 := by
  set D : FractionalIdeal (𝓞 E)⁰ E := (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) with hD
  have hD0 : D ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot

  have h1 : ∀ y ∈ Λ, herm 1 u y ∈ D⁻¹ := by
    intro y hy
    refine mem_inv_different fun a => ?_
    obtain ⟨k, hk⟩ := htr _ (Λ.smul_mem (⟨cc (a : E), isIntegral_cc a.isIntegral_coe⟩ : 𝓞 E) hy)
    refine ⟨k, ?_⟩
    rw [← hk]
    change _ = Algebra.trace ℚ E (herm 1 u (cc (a : E) • y))
    rw [herm_smul_right, cc_cc, mul_comm]
  have h2 : ∀ δ ∈ D, δ • u ∈ Λ := by
    intro δ hδ
    refine hdual _ fun y hy => ?_
    rw [herm_smul_left]
    have := FractionalIdeal.mul_mem_mul hδ (h1 y hy)
    rw [mul_inv_cancel₀ hD0] at this
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp this
    rw [← hb]
    exact b.isIntegral_coe
  have h3 : ∀ δ ∈ D, herm 1 u u * δ ∈ D⁻¹ := by
    intro δ hδ
    refine mem_inv_different fun a => ?_
    obtain ⟨k, hk⟩ := htr _ (Λ.smul_mem a (h2 δ hδ))
    refine ⟨k, ?_⟩
    rw [← hk, ← trace_cc]
    change _ = Algebra.trace ℚ E (herm 1 u ((a : E) • δ • u))
    rw [herm_smul_right, herm_smul_right]
    congr 1
    conv_rhs => rw [← cc_herm_self u]
    simp only [cc, map_mul]
    ring
  have h4 : herm 1 u u ∈ D⁻¹ * D⁻¹ := by
    rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hD0]
    exact h3
  have hnorm : ∀ σ : E →+* ℂ, ‖σ (herm 1 u u)‖ = ∑ k, ‖σ (u k)‖ ^ 2 := by
    intro σ
    rw [embedding_herm_self, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h0 : herm 1 u u ≠ 0 := by
    intro h
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hnorm σ
    rw [h, map_zero, norm_zero, eq_comm,
      Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at this
    apply hu
    funext k
    simpa using this k (Finset.mem_univ k)
  have h5 := absNorm_le_abs_norm_of_mem h4 h0
  rw [map_mul, hD, absNorm_inv_differentIdeal] at h5
  have h6 : (dE E)⁻¹ * (dE E)⁻¹ ≤ |((Algebra.norm ℚ (herm 1 u u) : ℚ) : ℝ)| := by
    have h := (Rat.cast_le (K := ℝ)).mpr h5
    simpa [dE] using h
  have h7 := finrank_mul_abs_norm_rpow_le_sum (herm 1 u u)
  simp only [hnorm] at h7
  refine le_trans ?_ h7
  have hd : 0 ≤ dE E := abs_nonneg _
  have hf : 2 * (fdeg E : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by
    exact_mod_cast Nat.mul_div_le (Module.finrank ℚ E) 2
  have h8 : (rdE E ^ 2)⁻¹ = ((dE E)⁻¹ * (dE E)⁻¹) ^ ((Module.finrank ℚ E : ℝ)⁻¹) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hd) (inv_nonneg.mpr hd), Real.inv_rpow hd, rdE, one_div, sq,
      mul_inv]
  rw [div_eq_mul_inv, h8]
  gcongr

end GlobalTheory
end

section

namespace GlobalTheory

theorem _root_.GlobalTheory.packingCount : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.PackingCount := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.PackingCount
  intro n P δ R hδ hR hP hsep
  have h1 := _root_.GlobalTheory.finset_card_le_of_separated P hδ (hδ.le.trans hR) 0
    (by simpa [dist_zero_right] using hP) (fun x hx y hy hxy => hsep x hx y hy hxy)
  rw [finrank_euclideanSpace_fin] at h1
  exact h1.trans (_root_.GlobalTheory.one_add_two_mul_div_pow_le hδ hR n)

theorem _root_.GlobalTheory.sup_le_l2_principal_torus : _root_.ReciprocityTheory.ChartRestriction.G.I2.GSupStatement := _root_.ReciprocityTheory.ChartRestriction.G.I2.gSup _root_.GlobalTheory.packingCount

end GlobalTheory
end
