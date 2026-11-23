module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle003
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.XLeOrthXplus
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.NGCut.LeadingMinorIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ideal

variable {D : D7}

abbrev dI (D : D7) : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

theorem star_F (c : D.host.F) : star (algebraMap D.host.F D.host.E c) = algebraMap D.host.F D.host.E c :=
  (NumberField.IsCMField.complexConj D.host.E).commutes c

theorem star_int (o : 𝓞 D.host.E) : ∃ o' : 𝓞 D.host.E, (o' : D.host.E) = star (o : D.host.E) := by
  exact ⟨⟨star (o : D.host.E), o.isIntegral_coe.map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩

theorem star_mem_pow (n : ℕ) (y : 𝓞 D.host.E) (hy : y ∈ dI D ^ n) :
    ∃ y' ∈ dI D ^ n, (y' : D.host.E) = star (y : D.host.E) := by
  rw [← Ideal.map_pow] at hy ⊢
  have hy' : y ∈ Submodule.span (𝓞 D.host.E)
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) '' ((differentIdeal ℤ (𝓞 D.host.F) ^ n : Ideal (𝓞 D.host.F)) : Set (𝓞 D.host.F))) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c, Ideal.mem_map_of_mem _ hc, ?_⟩
    have e : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.F D.host.E (c : D.host.F) := rfl
    rw [e, star_F]
  | zero => exact ⟨0, Ideal.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨x' + y', Ideal.add_mem _ hx' hy', ?_⟩
    rw [show ((x' + y' : 𝓞 D.host.E) : D.host.E) = (x' : D.host.E) + (y' : D.host.E) from rfl,
      show ((x + y : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) + (y : D.host.E) from rfl, ex, ey, star_add]
  | smul a x _ hx =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨a', ea⟩ := star_int a
    refine ⟨a' * x', Ideal.mul_mem_left _ _ hx', ?_⟩
    rw [smul_eq_mul, show ((a' * x' : 𝓞 D.host.E) : D.host.E) = (a' : D.host.E) * (x' : D.host.E) from rfl,
      show ((a * x : 𝓞 D.host.E) : D.host.E) = (a : D.host.E) * (x : D.host.E) from rfl, ea, ex, star_mul, mul_comm]

theorem dI_ne_bot (n : ℕ) : dI D ^ n ≠ ⊥ := by
  have h : dI D ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
  rw [← Ideal.zero_eq_bot] at h ⊢
  exact pow_ne_zero n h

theorem mem_inv_coe {J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) (x : D.host.E) :
    x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ ↔
      ∀ y ∈ J, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (y : D.host.E) := by
  have hJ' : (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  rw [FractionalIdeal.mem_inv_iff hJ']
  constructor
  · intro h y hy
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hy))
    exact ⟨o, ho⟩
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hz
    obtain ⟨o, ho⟩ := h y hy
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨o, ho⟩

theorem star_mem_inv (n : ℕ) {x : D.host.E}
    (hx : x ∈ (((dI D ^ n : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹) :
    star x ∈ (((dI D ^ n : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  rw [mem_inv_coe (dI_ne_bot n)] at hx ⊢
  intro y hy
  obtain ⟨y', hy', ey⟩ := star_mem_pow n y hy
  obtain ⟨o, ho⟩ := hx y' hy'
  obtain ⟨o', eo⟩ := star_int o
  refine ⟨o', ?_⟩
  rw [eo, ho, ey, star_mul, star_star, mul_comm]

end Ideal

section Entry

variable {D : D7}

theorem hT_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (m n : ℕ)
    (v v' : (VS D).V)
    (hv : ∀ x ∈ ((dI D ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹,
      x • v ∈ Λ)
    (hv' : ∀ y ∈ ((dI D ^ n : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹,
      y • v' ∈ Λ) :
    ∃ o ∈ dI D ^ (m + n), (o : D.host.E) = (VS D).hT v v' := by
  set Z := (VS D).hT v v' with hZ
  let FI := FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E
  set A : FI := ((dI D ^ m : Ideal (𝓞 D.host.E)) : FI)⁻¹
  set B : FI := ((dI D ^ n : Ideal (𝓞 D.host.E)) : FI)⁻¹
  have hJ : ((dI D ^ (m + n) : Ideal (𝓞 D.host.E)) : FI) = (A * B)⁻¹ := by
    rw [mul_inv, inv_inv, inv_inv, ← FractionalIdeal.coeIdeal_mul, ← pow_add]
  have hAB0 : A * B ≠ 0 := by
    refine mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_) <;>
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero] <;> exact dI_ne_bot _
  have hmem : Z ∈ (A * B)⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hAB0]
    intro w hw
    refine FractionalIdeal.mul_induction_on hw ?_ ?_
    · intro a ha b hb
      have ha' : star a ∈ A := star_mem_inv m ha
      obtain ⟨c, hc⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun (hv _ ha') (hv' _ hb)
      refine (FractionalIdeal.mem_one_iff _).2 ⟨c, ?_⟩
      show (c : D.host.E) = _
      rw [hc, LinearMap.map_smulₛₗ₂, LinearMap.map_smulₛₗ, RingHom.id_apply, starRingEnd_apply, star_star,
        smul_eq_mul, smul_eq_mul, hZ]
      ring
    · intro x y hx hy
      rw [mul_add]
      exact Submodule.add_mem _ hx hy
  rw [← hJ] at hmem
  obtain ⟨o, ho, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 hmem
  exact ⟨o, ho, e⟩

theorem two_sum_sub (r : ℕ) : ∀ q : ℕ, q ≤ r + 1 → 2 * ∑ i : Fin q, (r - (i : ℕ)) = q * (2 * r + 1 - q)
  | 0, _ => by simp
  | q + 1, hq => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [mul_add, two_sum_sub r q (by omega)]
    have e1 : 2 * r + 1 - q = q + 2 * (r - q) + 1 := by omega
    have e2 : 2 * r + 1 - (q + 1) = q + 2 * (r - q) := by omega
    rw [e1, e2]
    ring

end Entry

section Norm

variable {D : D7}

theorem discr_sq : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 :=
  D.host.der.discr_sq

theorem absNorm_dI : ((Ideal.absNorm (dI D) : ℕ) : ℝ) = (D.host.rdE ^ D.R.f) ^ 2 := by
  have h := Formalism.MainNotions.BridgeLemma.szf_normDD D discr_sq
  unfold Formalism.MainNotions.BridgeLemma.SzfNormDD Formalism.MainNotions.S.ddE at h
  rw [FractionalIdeal.coeIdeal_absNorm] at h
  exact_mod_cast h

theorem rd_pos : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  exact Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero _))) _

theorem prod_sq_ge (n : ℕ) (o : 𝓞 D.host.E) (ho : o ∈ dI D ^ n) (h0 : (o : D.host.E) ≠ 0) :
    (D.host.rdE ^ D.R.f) ^ (2 * n) ≤ ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ 2 := by
  have := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have h1 := InfinitePlace.prod_eq_abs_norm (o : D.host.E)
  have h2 : ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ w.mult =
      ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ 2 :=
    Finset.prod_congr rfl fun w _ => by rw [(IsTotallyComplex.isComplex w).mult_eq_two]
  rw [← h2, h1, ← Algebra.coe_norm_int]
  have ho0 : o ≠ 0 := fun h => h0 (by rw [h]; simp)
  have hspan : Ideal.span {o} ≤ dI D ^ n := (Ideal.span_singleton_le_iff_mem _).2 ho
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hspan
  rw [Ideal.absNorm_span_singleton, map_pow] at hdvd
  have hne : (Algebra.norm ℤ o).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]; exact Algebra.norm_ne_zero_iff.2 ho0
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  have hle' : ((Ideal.absNorm (dI D) ^ n : ℕ) : ℝ) ≤ ((Algebra.norm ℤ o).natAbs : ℝ) := by exact_mod_cast hle
  rw [Nat.cast_pow, absNorm_dI, ← pow_mul] at hle'
  have e : (((Algebra.norm ℤ o).natAbs : ℕ) : ℝ) = ((|((Algebra.norm ℤ o : ℤ) : ℚ)| : ℚ) : ℝ) := by
    simp [Nat.cast_natAbs, Rat.cast_abs]
  rw [← e]
  exact hle'

end Norm

end Formalism.L2.SG.NGCut.LeadingMinorIntegrality
end
end

section

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

def SD (Λ : Submodule (𝓞 E) S.V) : Prop := ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (S.hT y x)

theorem hsw (x y : S.V) : S.hT y x = star (S.hT x y) := PI.ScalarPairDr.W.hT_swap S x y

theorem hT_smulL (a : E) (x v : S.V) : S.hT (a • x) v = star a * S.hT x v := by
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem oSmul (o : 𝓞 E) (x : S.V) : o • x = (o : E) • x := (algebraMap_smul E o x).symm

theorem coe_ne_zero {d : 𝓞 E} (hd : d ≠ 0) : (d : E) ≠ 0 := by
  intro h; apply hd; exact RingOfIntegers.coe_eq_zero_iff.1 h

theorem isInt_star {a : E} (h : IsIntegral ℤ a) : IsIntegral ℤ (star a) := by
  have h2 := h.map ((starRingEnd E : E →+* E).toIntAlgHom)
  exact h2

theorem intO {a : E} (h : IsIntegral ℤ a) : ∃ o : 𝓞 E, (o : E) = a := ⟨⟨a, h⟩, rfl⟩

variable {S}

theorem int_smul_mem {Λ : Submodule (𝓞 E) S.V} {c : E} (hc : IsIntegral ℤ c) {x : S.V} (hx : x ∈ Λ) :
    c • x ∈ Λ := by
  obtain ⟨o, rfl⟩ := intO hc
  rw [← oSmul]
  exact Λ.smul_mem o hx

theorem sd_int {Λ : Submodule (𝓞 E) S.V} (h : SD S Λ) {x y : S.V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    IsIntegral ℤ (S.hT y x) := (h x).1 hx y hy

variable (S)

theorem riesz (F : S.V →ₗ[E] E) : ∃ w, ∀ v, S.hT w v = F v := by
  classical
  let b := S.frame
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis S.hT S.nondeg b
  refine ⟨∑ j, star (F (b j)) • bs j, fun v => ?_⟩
  have key : S.hT (∑ j, star (F (b j)) • bs j) = F := by
    apply b.ext
    intro i

    rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [hsw S (b i) (bs i), hbs i i]; simp
    · intro j _ hj
      rw [hsw S (b i) (bs j), hbs i j, if_neg (Ne.symm hj)]; simp
    · simp
  rw [key]

theorem mem_of_orth_orth (X : Submodule E S.V) {w : S.V} (hw : ∀ u ∈ orth S X, S.hT w u = 0) : w ∈ X := by
  have hle : X ≤ orth S (orth S X) := fun x hx => (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun u hu => by
    rw [hsw S x u, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 hu x hx, star_zero]
  have h1 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S X
  have h2 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (orth S X)
  have heq : X = orth S (orth S X) := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  rw [heq]
  exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun u hu => by rw [hsw S w u, hw u hu, star_zero]

theorem proj_quot (P : Submodule (𝓞 E) S.V) (hP : P.FG) (Z : Submodule E S.V) :
    Module.Projective (𝓞 E) (P ⧸ (Z.restrictScalars (𝓞 E)).comap P.subtype) := by
  set K := (Z.restrictScalars (𝓞 E)).comap P.subtype with hK
  have : Module.Finite (𝓞 E) P := Module.Finite.iff_fg.2 hP
  have htor : Submodule.torsion (𝓞 E) (P ⧸ K) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff q).1 hq
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [Submonoid.smul_def, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at ha
    have ha0 : ((a : 𝓞 E) : E) ≠ 0 := coe_ne_zero (nonZeroDivisors.coe_ne_zero a)
    have h1 : ((a : 𝓞 E) : E) • (x : S.V) ∈ Z := by
      have := ha
      simp only [hK, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_smul,
        Submodule.restrictScalars_mem] at this
      rwa [oSmul] at this
    have h2 := Z.smul_mem ((a : 𝓞 E) : E)⁻¹ h1
    rw [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h2
    simpa [hK] using h2
  have : Module.Flat (𝓞 E) (P ⧸ K) := (IsDedekindDomain.flat_iff_torsion_eq_bot).2 htor
  have : Module.FinitePresentation (𝓞 E) (P ⧸ K) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem glift (P Q : Submodule (𝓞 E) S.V) (hP : P.FG) (Y Z : Submodule E S.V)
    (hPZ : ∀ x ∈ P, x ∈ Z → x ∈ Q) (hs : ∀ x ∈ P, ∃ y ∈ Q, y - x ∈ Y) :
    ∃ δ : P →ₗ[𝓞 E] S.V, (∀ x, δ x ∈ Y) ∧ (∀ x : P, (x : S.V) ∈ Z → δ x = 0) ∧
      (∀ x : P, (x : S.V) + δ x ∈ Q) := by
  classical
  set K := (Z.restrictScalars (𝓞 E)).comap P.subtype with hK
  have := proj_quot S P hP Z
  let dif : (P × Q) →ₗ[𝓞 E] S.V := Q.subtype ∘ₗ LinearMap.snd _ _ _ - P.subtype ∘ₗ LinearMap.fst _ _ _
  let R : Submodule (𝓞 E) (P × Q) := (Y.restrictScalars (𝓞 E)).comap dif
  let g : R →ₗ[𝓞 E] (P ⧸ K) := K.mkQ ∘ₗ LinearMap.fst _ _ _ ∘ₗ R.subtype
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    obtain ⟨y, hyQ, hy⟩ := hs x x.2
    refine ⟨⟨(x, ⟨y, hyQ⟩), ?_⟩, rfl⟩
    simpa [R, dif] using hy
  obtain ⟨s, hs'⟩ := Module.projective_lifting_property g LinearMap.id hg
  refine ⟨dif ∘ₗ R.subtype ∘ₗ s ∘ₗ K.mkQ, fun x => ?_, fun x hx => ?_, fun x => ?_⟩
  · exact (s (K.mkQ x)).2
  · have : K.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simpa [hK] using hx
    simp [this]
  · have hgt : g (s (K.mkQ x)) = K.mkQ x := LinearMap.congr_fun hs' (K.mkQ x)
    set t := s (K.mkQ x) with ht
    have h1 : x - (t : P × Q).1 ∈ K := by
      have h0 : K.mkQ (x - (t : P × Q).1) = 0 := by
        have : K.mkQ ((t : P × Q).1) = K.mkQ x := hgt
        rw [map_sub, this, sub_self]
      exact (Submodule.Quotient.mk_eq_zero K).1 h0
    have h2 : ((x : S.V) - ((t : P × Q).1 : S.V)) ∈ Q := by
      refine hPZ _ (P.sub_mem x.2 (t : P × Q).1.2) ?_
      simpa [hK] using h1
    have h3 : (x : S.V) + (dif ∘ₗ R.subtype ∘ₗ s ∘ₗ K.mkQ) x =
        ((t : P × Q).2 : S.V) + ((x : S.V) - ((t : P × Q).1 : S.V)) := by
      simp only [LinearMap.coe_comp, Function.comp_apply, ← ht, dif, LinearMap.sub_apply,
        Submodule.coe_subtype, LinearMap.snd_apply, LinearMap.fst_apply]
      abel
    rw [h3]
    exact Q.add_mem (t : P × Q).2.2 h2

theorem retract (P : Submodule (𝓞 E) S.V) (hP : P.FG) (Z : Submodule E S.V) :
    ∃ π : P →ₗ[𝓞 E] S.V, (∀ x, π x ∈ P ∧ π x ∈ Z) ∧ ∀ x : P, (x : S.V) ∈ Z → π x = x := by
  classical
  set K := (Z.restrictScalars (𝓞 E)).comap P.subtype with hK
  have := proj_quot S P hP Z
  obtain ⟨s, hs'⟩ := Module.projective_lifting_property K.mkQ LinearMap.id K.mkQ_surjective
  refine ⟨P.subtype ∘ₗ (LinearMap.id - s ∘ₗ K.mkQ), fun x => ⟨?_, ?_⟩, fun x hx => ?_⟩
  · exact (x - s (K.mkQ x)).2
  · have h1 : x - s (K.mkQ x) ∈ K := by
      have h0 : K.mkQ (x - s (K.mkQ x)) = 0 := by
        have : K.mkQ (s (K.mkQ x)) = K.mkQ x := LinearMap.congr_fun hs' (K.mkQ x)
        rw [map_sub, this, sub_self]
      exact (Submodule.Quotient.mk_eq_zero K).1 h0
    simpa [hK] using h1
  · have : K.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simpa [hK] using hx
    simp [this]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
end
end
