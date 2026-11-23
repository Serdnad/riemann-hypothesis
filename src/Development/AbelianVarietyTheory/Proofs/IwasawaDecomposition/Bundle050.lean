module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle001
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.Defs
public import ReciprocityTheory.Automorphisms.Bundle001
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.Automorphisms.PlaceA
import Formalism.FrobeniusOrbits.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Nilpotent.Basic
import ReciprocityTheory.GaloisValuations.GlobalA
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory

theorem localUnit_div_congr_one {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) (hx : IsUnitAt v x) (y : 𝓞 L)
    (hy : Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y) < 1) :
    y ∉ v.asIdeal ∧ ∃ k : Lˣ, (k : L) = (y : L) ∧
      Valued.v (((x * (atFin v k)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1)
        ≤ WithZero.exp (-1 : ℤ) := by
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
  have hy1 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y) = 1 := by
    rw [← hx']
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap, hx']
    exact hy
  have hy2 : v.valuation L (algebraMap (𝓞 L) L y) = 1 := by
    rw [← ReciprocityTheory.Aut.adic_valued_algebraMap, ← ReciprocityTheory.Aut.adic_algebraMap_R]
    exact hy1
  have hnot : y ∉ v.asIdeal := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).mp hy2
  have hy0 : (y : L) ≠ 0 := by
    intro h
    apply hnot
    have : y = 0 := by exact_mod_cast h
    rw [this]
    exact v.asIdeal.zero_mem
  refine ⟨hnot, Units.mk0 (y : L) hy0, rfl, ?_⟩
  have hk : ((atFin v (Units.mk0 (y : L) hy0) : (v.adicCompletion L)ˣ) : v.adicCompletion L)
      = algebraMap (𝓞 L) (v.adicCompletion L) y := rfl
  have hne : algebraMap (𝓞 L) (v.adicCompletion L) y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1
  have e : ((x * (atFin v (Units.mk0 (y : L) hy0))⁻¹ : (v.adicCompletion L)ˣ) :
      v.adicCompletion L) - 1 = ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y)
        * (algebraMap (𝓞 L) (v.adicCompletion L) y)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hk, sub_mul, mul_inv_cancel₀ hne]
  rw [e, map_mul, map_inv₀, hy1, inv_one, mul_one]
  generalize Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y) = g at hy
  by_cases hg : g = 0
  · rw [hg]; exact zero_le
  · rw [← WithZero.exp_log hg] at hy ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
    rw [WithZero.exp_le_exp]
    omega

theorem exists_nat_congr_of_absNorm_prime {L : Type} [Field L] [NumberField L]
    (I : Ideal (𝓞 L)) (hI : I ≠ ⊤) {p : ℕ} (hp : p.Prime) (hN : Ideal.absNorm I = p) (y : 𝓞 L) :
    ∃ a : ℕ, y - (a : 𝓞 L) ∈ I := by
  have := Fact.mk hp
  have hcard : Nat.card (𝓞 L ⧸ I) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have : Nontrivial (𝓞 L ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have h := mem_multiples_of_prime_card hcard (g := (1 : 𝓞 L ⧸ I))
    (g' := Ideal.Quotient.mk I y) one_ne_zero
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq, map_natCast, ← ha]
  simp


open Classical in
theorem localUnit_congr_global :
    ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ), IsUnitAt v x → (∃ (k : Lˣ) (y : 𝓞 L), (k : L) = (y : L) ∧ y ∉ v.asIdeal ∧ Valued.v (((x * (atFin v k)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ)) ∧ ∀ p : ℕ, p.Prime → Ideal.absNorm v.asIdeal = p → ∃ (a : ℕ) (k : Lˣ), a.Coprime p ∧ (k : L) = (a : L) ∧ Valued.v (((x * (atFin v k)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ) := by
  intro L _ _ v x hx
  obtain ⟨y, hy⟩ := ReciprocityTheory.Aut.adic_exists_approx v (x : v.adicCompletion L) (le_of_eq hx)
  refine ⟨?_, fun p hp hN => ?_⟩
  · obtain ⟨h1, k, hk, h2⟩ := localUnit_div_congr_one v x hx y hy
    exact ⟨k, y, hk, h1, h2⟩
  · obtain ⟨a, ha⟩ := exists_nat_congr_of_absNorm_prime v.asIdeal v.isPrime.ne_top hp hN y
    have hya : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) (y - (a : 𝓞 L))) < 1 := by
      have h3 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) (y - (a : 𝓞 L)))
          = v.valuation L (algebraMap (𝓞 L) L (y - (a : 𝓞 L))) :=
        ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L (y - (a : 𝓞 L)))
      rw [h3]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr ha
    have hxa : Valued.v ((x : v.adicCompletion L)
        - algebraMap (𝓞 L) (v.adicCompletion L) (a : 𝓞 L)) < 1 := by
      have e : (x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) (a : 𝓞 L)
          = ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y)
            + algebraMap (𝓞 L) (v.adicCompletion L) (y - (a : 𝓞 L)) := by
        rw [map_sub]; ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hy hya)
    obtain ⟨h1, k, hk, h2⟩ := localUnit_div_congr_one v x hx (a : 𝓞 L) hxa
    refine ⟨a, k, ?_, by simpa using hk, h2⟩
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    rintro ⟨c, rfl⟩
    apply h1
    have hpm : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := hN ▸ Ideal.absNorm_mem v.asIdeal
    push_cast
    exact v.asIdeal.mul_mem_right _ hpm

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix
open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.IwasawaFinAd

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def coordV (v : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def locM (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  RingHom.mapMatrix (coordV v) M

def locGL (v : HeightOneSpectrum (𝓞 F)) :
    GL (Fin n) (FiniteAdeleRing (𝓞 F) F) →* GL (Fin n) (v.adicCompletion F) :=
  Units.map (RingHom.mapMatrix (coordV v)).toMonoidHom

theorem locM_mul (v : HeightOneSpectrum (𝓞 F)) (M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    locM v (M * N) = locM v M * locM v N := map_mul _ _ _

theorem locM_one (v : HeightOneSpectrum (𝓞 F)) :
    locM v (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) = 1 := map_one _

theorem matrix_ext_loc {M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)}
    (h : ∀ v, locM v M = locM v N) : M = N := by
  refine Matrix.ext fun i j => FiniteAdeleRing.ext F fun v => ?_
  exact congrFun (congrFun (h v) i) j

theorem gl_ext_loc {g h : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)} (e : ∀ v, locGL v g = locGL v h) :
    g = h :=
  Units.ext (matrix_ext_loc fun v => congrArg Units.val (e v))

def IntAt (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) : Prop :=
  ∀ i j, M i j ∈ v.adicCompletionIntegers F

theorem intAt_one (v : HeightOneSpectrum (𝓞 F)) : IntAt v (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact (v.adicCompletionIntegers F).one_mem
  · exact (v.adicCompletionIntegers F).zero_mem

def glueM (x : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    (⟨fun v => x v i j, hx.mono fun v h => h i j⟩ :
      Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

theorem locM_glueM (x : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v)) (v : HeightOneSpectrum (𝓞 F)) :
    locM v (glueM x hx) = x v := by
  ext i j
  rfl

def glueGL (x : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v).val ∧ IntAt v (x v)⁻¹.val) :
    GL (Fin n) (FiniteAdeleRing (𝓞 F) F) where
  val := glueM (fun v => (x v).val) (hx.mono fun _ h => h.1)
  inv := glueM (fun v => (x v)⁻¹.val) (hx.mono fun _ h => h.2)
  val_inv := matrix_ext_loc fun v => by
    rw [locM_mul, locM_glueM, locM_glueM, locM_one]; exact Units.mul_inv (x v)
  inv_val := matrix_ext_loc fun v => by
    rw [locM_mul, locM_glueM, locM_glueM, locM_one]; exact Units.inv_mul (x v)

theorem locGL_glueGL (x : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v).val ∧ IntAt v (x v)⁻¹.val) (v : HeightOneSpectrum (𝓞 F)) :
    locGL v (glueGL x hx) = x v :=
  Units.ext (locM_glueM _ (hx.mono fun _ h => h.1) v)

theorem eventually_intAt (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v in Filter.cofinite, IntAt v (locM v M) := by
  unfold IntAt
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  exact (M i j).2

theorem upper_eq_uni_mul_diag {K : Type} [Field K] (b : GL (Fin n) K) (hb : b.val.BlockTriangular id) :
    ∃ u t : GL (Fin n) K, PIW.ClassFinD.IsUpperUni u.val ∧ PIW.ClassFinD.IsDiagM t.val ∧ b = u * t := by
  have hdet0 : b.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  have hne : ∀ i, b.val i i ≠ 0 := by
    intro i h
    apply hdet0
    rw [Matrix.det_of_upperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  let t : GL (Fin n) K :=
    ⟨diagonal (fun i => b.val i i), diagonal (fun i => (b.val i i)⁻¹),
      by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hne i),
      by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hne i)⟩
  have hU : ∀ i j, (b * t⁻¹).val i j = b.val i j * (b.val j j)⁻¹ := by
    intro i j
    change (b.val * diagonal (fun i => (b.val i i)⁻¹)) i j = _
    rw [mul_diagonal]
  refine ⟨b * t⁻¹, t, ⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, by group⟩
  · rw [hU, hb hij, zero_mul]
  · rw [hU, mul_inv_cancel₀ (hne i)]
  · exact diagonal_apply_ne _ hij

theorem isUpperUni_one {K : Type} [CommRing K] : PIW.ClassFinD.IsUpperUni (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun i j hij => Matrix.one_apply_ne (ne_of_gt hij), fun i => Matrix.one_apply_eq i⟩

theorem isDiagM_one {K : Type} [CommRing K] : PIW.ClassFinD.IsDiagM (1 : Matrix (Fin n) (Fin n) K) :=
  fun i j hij => Matrix.one_apply_ne hij

theorem intAt_of_glint (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin n) (v.adicCompletion F))
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) : IntAt v k.val ∧ IntAt v k⁻¹.val := by
  obtain ⟨K, rfl⟩ := hk
  refine ⟨fun i j => (K.val i j).2, fun i j => ?_⟩
  rw [← map_inv]
  exact ((K⁻¹).val i j).2

end GlobalTheory.IwasawaFinAd

namespace GlobalTheory.IwasawaFinAd

open PIW.ClassFinD

theorem iwasawaAf : PIW.ClassFinD.IwasawaAf := by
  classical
  intro F _ _ n g
  let good : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    IntAt v (locGL v g).val ∧ IntAt v (locGL v g)⁻¹.val
  have hgood : ∀ᶠ v in Filter.cofinite, good v := by
    refine (eventually_intAt g.val).and ((eventually_intAt (g⁻¹).val).mono fun v h => ?_)
    rw [← map_inv]
    exact h
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ u t k : GL (Fin n) (v.adicCompletion F),
      IsUpperUni u.val ∧ IsDiagM t.val ∧ IntAt v k.val ∧ IntAt v k⁻¹.val ∧ locGL v g = u * t * k ∧
      (good v → u = 1 ∧ t = 1 ∧ k = locGL v g) := by
    intro v
    by_cases hv : good v
    · exact ⟨1, 1, locGL v g, isUpperUni_one, isDiagM_one, hv.1, hv.2, by rw [one_mul, one_mul],
        fun _ => ⟨rfl, rfl, rfl⟩⟩
    · obtain ⟨b, k, hb, hk, hbk⟩ := Formalism.UG.P.spherical_iwasawa F v (locGL v g)
      obtain ⟨u, t, hu, ht, rfl⟩ := upper_eq_uni_mul_diag b hb
      obtain ⟨hk1, hk2⟩ := intAt_of_glint v k hk
      exact ⟨u, t, k, hu, ht, hk1, hk2, hbk, fun h => absurd h hv⟩
  choose uL tL kL huL htL hkL hkL' hgL hgoodL using hloc
  have hu : ∀ᶠ v in Filter.cofinite, IntAt v (uL v).val ∧ IntAt v (uL v)⁻¹.val :=
    hgood.mono fun v hv => by
      rw [(hgoodL v hv).1, inv_one]
      exact ⟨intAt_one v, intAt_one v⟩
  have ht : ∀ᶠ v in Filter.cofinite, IntAt v (tL v).val ∧ IntAt v (tL v)⁻¹.val :=
    hgood.mono fun v hv => by
      rw [(hgoodL v hv).2.1, inv_one]
      exact ⟨intAt_one v, intAt_one v⟩
  have hk : ∀ᶠ v in Filter.cofinite, IntAt v (kL v).val ∧ IntAt v (kL v)⁻¹.val :=
    Filter.Eventually.of_forall fun v => ⟨hkL v, hkL' v⟩
  refine ⟨glueGL uL hu, glueGL tL ht, glueGL kL hk, ⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_,
    ⟨fun i j v => hkL v i j, fun i j v => hkL' v i j⟩, ?_⟩
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL uL hu).val i j) = coordV v 0
    rw [map_zero]
    exact (huL v).1 i j hij
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL uL hu).val i i) = coordV v 1
    rw [map_one]
    exact (huL v).2 i
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL tL ht).val i j) = coordV v 0
    rw [map_zero]
    exact htL v i j hij
  · refine gl_ext_loc fun v => ?_
    rw [map_mul, map_mul, locGL_glueGL, locGL_glueGL, locGL_glueGL]
    exact hgL v

end GlobalTheory.IwasawaFinAd
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

section Graded

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {U : ℤ → Submodule K V}
  {N : End K V}

theorem eq_zero_of_pow_eq_zero (hb : ∀ i : ℕ, Set.BijOn (N ^ i) (U (-i)) (U i)) {m : ℕ} {d : ℤ}
    (hd : d + m ≤ 0) {v : V} (hv : v ∈ U d) (h0 : (N ^ m) v = 0) : v = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, d = -((c + m : ℕ) : ℤ) := ⟨(-d - m).toNat, by omega⟩
  subst hc
  refine (hb (c + m)).2.1 hv (zero_mem _) ?_
  rw [pow_add, End.mul_apply, h0, map_zero, map_zero]

end Graded

end GlobalTheory.WeilDeligne
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.FrobSemisimpleUnique

theorem isNilpotent_zpow_sub_one {R : Type*} [Ring R] (u : Rˣ) (hu : IsNilpotent ((u : R) - 1))
    (d : ℤ) : IsNilpotent (((u ^ d : Rˣ) : R) - 1) := by
  have hnat : ∀ n : ℕ, IsNilpotent (((u ^ n : Rˣ) : R) - 1) := by
    intro n
    rw [Units.val_pow_eq_pow_val, ← geom_sum_mul]
    refine Commute.isNilpotent_mul_left ?_ hu
    refine Commute.sum_left _ _ _ fun i _ => ?_
    exact ((Commute.refl (u : R)).sub_right (Commute.one_right _)).pow_left i
  obtain ⟨n, rfl | rfl⟩ := d.eq_nat_or_neg
  · rw [zpow_natCast]; exact hnat n
  · rw [zpow_neg, zpow_natCast]
    have h1 := hnat n
    generalize u ^ n = v at h1
    have h2 : ((v⁻¹ : Rˣ) : R) - 1 = -(((v⁻¹ : Rˣ) : R) * ((v : R) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [h2]
    refine (Commute.isNilpotent_mul_left ?_ h1).neg
    exact ((Commute.refl v).inv_left.units_val).sub_right (Commute.one_right _)

theorem nilpotent_part {R : Type*} [Ring R] {f s : R} (v : Rˣ) (hv : IsNilpotent ((v : R) - 1))
    (hc : Commute (v : R) f) (hf : f = s * v) : IsNilpotent (f - s) ∧ Commute (f - s) s := by
  have hs : s = f * ((v⁻¹ : Rˣ) : R) := by rw [hf, Units.mul_inv_cancel_right]
  have hvs : Commute (v : R) s := by
    rw [hs]
    exact hc.mul_right (Commute.refl v).inv_right.units_val
  have h1 : f - s = s * ((v : R) - 1) := by rw [hf, mul_sub, mul_one]
  have h2 : Commute s ((v : R) - 1) := hvs.symm.sub_right (Commute.one_right _)
  rw [h1]
  exact ⟨h2.isNilpotent_mul_left hv, (Commute.refl s).mul_left h2.symm⟩

end GlobalTheory.WeilDeligne.FrobSemisimpleUnique
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct

namespace GlobalTheory.AdelicComp

theorem coord_compAt (L : Type) [Field L] [NumberField L] [IsCMField L] {ι : Type} [DecidableEq ι] [Finite ι]
    (b : Module.Basis ι (maximalRealSubfield L) L)
    (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i : ι) (z : AL L) :
    TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ (compAt L w z))
      = evalAt L w (TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    have h : compAt L w (x ⊗ₜ a) = x ⊗ₜ evalAt L w a := rfl
    rw [h]
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem eq_sum_coord {K V M : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module K M]
    {ι : Type} [Fintype ι] (b : Module.Basis ι K V) (z : V ⊗[K] M) :
    z = ∑ i, b i ⊗ₜ[K] TensorProduct.lid K M ((b.coord i).rTensor M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, ← TensorProduct.smul_tmul,
      ← TensorProduct.sum_tmul, Module.Basis.coord_apply, Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hx, ← hy]

theorem eq_zero_of_compAt_eq_zero :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (z : AL L), (∀ w, compAt L w z = 0) → z = 0 := by
  intro L _ _ _ z hz
  classical
  let b := Module.finBasis (maximalRealSubfield L) L
  rw [eq_sum_coord b z]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ z) = 0 := by
    refine Subtype.ext (funext fun w => ?_)
    have h := coord_compAt L b w i z
    rw [hz w, map_zero, map_zero] at h
    exact h.symm
  rw [this, TensorProduct.tmul_zero]

end GlobalTheory.AdelicComp
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.splitPlace_completion_equiv_unique :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : _root_.ReciprocityTheory.Aut.SplitPlace L)
    (i i' : s.v.adicCompletion (NumberField.maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → Continuous i' →
    (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → (∀ x : L, i' (s.i x) = algebraMap L (s.w.adicCompletion L) x) →
    i = i' := by
  intro L _ _ _ s i i' hi hi' h h'
  have hd := HeightOneSpectrum.denseRange_algebraMap (K := NumberField.maximalRealSubfield L) s.v
  have key : (i : _ → _) = i' := by
    refine hd.equalizer hi hi' (funext fun a => ?_)
    have ha : algebraMap (NumberField.maximalRealSubfield L) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) a
        = s.i (algebraMap (NumberField.maximalRealSubfield L) L a) := (s.i.commutes a).symm
    simp only [Function.comp_apply, ha, h, h']
  exact RingEquiv.ext (congrFun key)

end GlobalTheory
end
