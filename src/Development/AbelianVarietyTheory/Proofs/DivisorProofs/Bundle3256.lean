module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorComponentsTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3210
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecScalOneVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

theorem thetaNZ_e8LB : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → GlobalTheory.LN.ThetaNZ (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W) := by
  intro hL hL2 hE V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ hS W hW
  have hB : GlobalTheory.Mum.Base V₁ := by
    obtain ⟨h1, h2, h3, h4⟩ := hCN
    exact ⟨⟨h1, inferInstance, h2, h3⟩, h4⟩
  obtain ⟨Pc, hPc, hEv⟩ := GlobalTheory.T.exists_cubical_e8LB_evenOn hL hL2 hE V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  obtain ⟨A, gen, hgen, hA⟩ := GlobalTheory.T.exists_polAV_generic_fibre_e8LB hL hL2 hE V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨D, U, hU, -⟩ := GlobalTheory.T.exists_preUniformisation_even_torus_completeNormal V₁ hB _ Pc hS8 hEv A gen hgen (hPc ▸ hA)
  have h := GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section V₁ hB D A _ U (hU ▸ hEv)
  rw [hU, hPc] at h
  exact h

end GlobalTheory.PowE8
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

theorem GlobalTheory.Mum.TensTor.qkAdd_of_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (p' q' s' : QkPt D'.toPre F k) (ps qs ss : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs → PtRel T ν ν' s' ss → (∀ i, QkAdd (ps i) (qs i) (ss i)) → QkAdd p' q' s' := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' k p' q' s' ps qs ss hp hq hs hadd
  have gt : GlobalTheory.Ex.BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  obtain ⟨-, -, gAdd, -, gQ⟩ := gt R D.toPre D.psi_even D.tau_bimult F N ν
  obtain ⟨-, -, gAdd', -, gQ'⟩ := gt R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  have hF := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  obtain ⟨-, -, he, hebij, -, -, -, -⟩ := hF
  obtain ⟨P', Ps, hP', hPs, hPy, hPg⟩ := hp
  obtain ⟨Q', Qs, hQ', hQs, hQy, hQg⟩ := hq
  obtain ⟨S', Ss, hS', hSs, hSy, hSg⟩ := hs
  have hz : ∀ i, N.QEq (Ps i * Qs i) (Ss i) := by
    intro i
    obtain ⟨x, hxy, hxg, hxe⟩ := hadd i
    obtain ⟨X, hX⟩ := ((gQ k).1 x).exists
    have hXeq : X = Ps i * Qs i := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · apply Multiplicative.toAdd.injective
        apply ν.eX.injective
        rw [hX.1, hxy, ← (hPs i).1, ← (hQs i).1, ← map_add (f := _)]
        rfl
      · exact (gAdd _ _ _ _ _ _ (hPs i).2 (hQs i).2 hX.2).1 hxg
    rw [← hXeq]
    exact ((gQ k).2.2 x (ss i) X (Ss i) hX (hSs i)).1 hxe
  choose z hz1 hz2 using hz
  obtain ⟨z', hz'⟩ := hebij.2 z
  have he0 : ∀ i, chi T ν ν' 0 i = 0 := fun i => by
    have := he 0 0 i
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have hensmul : ∀ (n : ℕ) χ i, chi T ν ν' (n • χ) i = n • chi T ν ν' χ i := by
    intro n χ i
    induction n with
    | zero => rw [zero_smul, zero_smul, he0]
    | succ n ih => rw [succ_nsmul, he, ih, succ_nsmul]
  obtain ⟨x', hx'⟩ := (gQ' k).2.1 (P' * Q')
  refine ⟨x', ?_, ?_, ?_⟩
  · rw [← hx'.1, ← hP'.1, ← hQ'.1, ← map_add (f := _)]
    rfl
  · exact (gAdd' _ _ _ _ _ _ hP'.2 hQ'.2 hx'.2).2 rfl
  · refine ((gQ' k).2.2 x' s' (P' * Q') S' hx' hS').2 ⟨z', ?_, ?_⟩
    · apply hebij.1
      funext i
      have e1 : (P' * Q').1.1.toAdd = P'.1.1.toAdd + Q'.1.1.toAdd := rfl
      have e2 : (Ps i * Qs i).1.1.toAdd = (Ps i).1.1.toAdd + (Qs i).1.1.toAdd := rfl
      rw [hSy i, hz1 i, he, hensmul, hz', e1, he, hPy i, hQy i, e2]
    · have m1 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν')
        P'.1.2 Q'.1.2 _ _ hPg hQg
      have m2 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν') z'
      have m3 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν')
        _ _ _ _ m1 m2
      have e3 : ((fun j => (Ps j).1.2) * (fun j => (Qs j).1.2)) * (fun j => N.io (chi T ν ν' z' j)) =
          fun j => (Ss j).1.2 := by
        funext j
        rw [hz2 j, hz']
        rfl
      rw [e3] at m3
      exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν')
        _ _ _ hSg m3
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem comp_nsmul {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {e : N'.X → Fin r → N.X}
    (he : ∀ χ χ' i, e (χ + χ') i = e χ i + e χ' i) (k : ℕ) (z : N'.X) (i : Fin r) : e (k • z) i = k • e z i := by
  induction k with
  | zero =>
    have h := he 0 0 i
    rw [add_zero] at h
    simpa using h
  | succ k ih => rw [succ_nsmul, he, ih, succ_nsmul]

theorem qEq_iff_of_rel {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (hT : TensFacts W φ e wv)
    (hW : IsUnit (W + W.transpose).det) {k : ℕ} {a' b' : N'.QT k} {as bs : Fin r → N.QT k}
    (ha : QRelV W φ e wv a' as) (hb : QRelV W φ e wv b' bs) : N'.QEq a' b' ↔ ∀ i, N.QEq (as i) (bs i) := by
  have hadd := hT.2.2.1
  have he := hT.2.2.2.1
  constructor
  · rintro ⟨z, hy, hg⟩ i
    refine ⟨e z i, ?_, ?_⟩
    · rw [← hb.1 i, hy, hadd, comp_nsmul hadd, ha.1 i]
    · have h1 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hT _ _ _ _ ha.2 (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hT z)
      rw [← hg] at h1
      have h2 := congrFun (GlobalTheory.T.tensorTorusValueCorrespondence_unique_components F N N' W φ e wv hT hW _ _ _ hb.2 h1) i
      simpa using h2
  · intro h
    choose z hz using h
    obtain ⟨z', hz'⟩ := he.2 z
    refine ⟨z', ?_, ?_⟩
    · apply he.1
      funext i
      rw [hadd, comp_nsmul hadd, hz', ha.1 i, hb.1 i]
      exact (hz i).1
    · have h1 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hT _ _ _ _ ha.2 (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hT z')
      have h2 : ((fun j => (as j).1.2) * fun j => N.io (e z' j)) = fun j => (bs j).1.2 :=
        funext fun j => by rw [Pi.mul_apply, hz']; exact ((hz j).2).symm
      rw [h2] at h1
      exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W φ e wv hT _ _ _ hb.2 h1

theorem qkPt_equiv_iff_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N)
    (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' q' : QkPt D'.toPre F k)
    (ps qs : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs →
    (QkPt.Equiv D'.toPre F p' q' ↔ ∀ i, QkPt.Equiv D.toPre F (ps i) (qs i)) := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' hW k p' q' ps qs hp hq
  obtain ⟨a', as, ha', has, ha⟩ := hp
  obtain ⟨b', bs, hb', hbs, hb⟩ := hq
  have hT := GlobalTheory.T.tensorData_values_facts R hB D D' W T F N N' ν ν'
  have G := GlobalTheory.Ex.GtValues.points_correspond
  rw [((G R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 k).2.2 p' q' a' b' ha' hb', qEq_iff_of_rel hT hW ha hb]
  exact forall_congr' fun i =>
    (((G R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 k).2.2 _ _ _ _ (has i) (hbs i)).symm

end GlobalTheory.Mum.TensTor
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTower

section Values
variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ} {φ : N'.A → Fin r → N.A}
  {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem comp_nsmul (h : TensFacts W φ e wv) (k : ℕ) (χ : N'.X) (i : Fin r) : e (k • χ) i = k • e χ i :=
  (AddMonoidHom.mk' (fun χ => e χ i) fun a b => h.2.2.1 a b i).map_nsmul k χ

theorem rel_pow (h : TensFacts W φ e wv) {v' : N'.Gt} {vs : Fin r → N.Gt} (hv : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv h 0
    have e0 : ∀ j, e 0 j = 0 := fun j => by simpa using comp_nsmul h 0 0 j
    simp only [e0, NumD.io_zero] at h0
    rw [pow_zero, pow_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv h _ _ _ _ ih hv

theorem tower_val (h : TensFacts W φ e wv) {n m : ℕ} {p' : N'.QT (n * m)} {ps : Fin r → N.QT (n * m)} {t' : N'.QT n}
    {ts : Fin r → N.QT n} (hp : QRelV W φ e wv p' ps) (ht : QRelV W φ e wv t' ts)
    (hz : ∀ i, ∃ z : N.X, (ts i).1.1.toAdd = (ps i).1.1.toAdd + n • z ∧ (ts i).1.2 = (ps i).1.2 ^ m * N.io z) :
    ∃ z' : N'.X, t'.1.1.toAdd = p'.1.1.toAdd + n • z' ∧ t'.1.2 = p'.1.2 ^ m * N'.io z' := by
  choose z hz1 hz2 using hz
  obtain ⟨z', rfl⟩ := h.2.2.2.1.2 z
  refine ⟨z', h.2.2.2.1.1 (funext fun i => ?_), ?_⟩
  · rw [h.2.2.1, comp_nsmul h, ht.1, hp.1, hz1]
  · refine GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W φ e wv h _ _ _ ht.2 ?_
    have := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv h _ _ _ _ (rel_pow h hp.2 m) (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv h z')
    have e1 : (fun j => (ts j).1.2) = (fun j => (ps j).1.2) ^ m * fun j => N.io (e z' j) := funext hz2
    rw [e1]
    exact this

end Values

theorem tower : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (n m : ℕ), 0 < n → 0 < m → ∀ (p' : QkPt D'.toPre F (n * m)) (ps : Fin r → QkPt D.toPre F (n * m)) (t' : QkPt D'.toPre F n) (ts : Fin r → QkPt D.toPre F n), PtRel T ν ν' p' ps → PtRel T ν ν' t' ts → (∀ i, ∃ q : QkPt D.toPre F n, q.y = (ps i).y ∧ GtPtF.IsNsmul m (ps i).g q.g ∧ QkPt.Equiv D.toPre F q (ts i)) → ∃ q' : QkPt D'.toPre F n, q'.y = p'.y ∧ GtPtF.IsNsmul m p'.g q'.g ∧ QkPt.Equiv D'.toPre F q' t' := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' n m _ _ p' ps t' ts ⟨a', as, ha', has, ha⟩ ⟨b', bs, hb', hbs, hb⟩ H
  have hF := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  have B := (GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 n
  have B' := (GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 n
  obtain ⟨z', hz1, hz2⟩ := tower_val hF ha hb fun i => by
    obtain ⟨q, hy, hn, he⟩ := H i
    obtain ⟨c, hc⟩ := (B.1 q).exists
    obtain ⟨z, h1, h2⟩ := (B.2.2 q (ts i) c (bs i) hc (hbs i)).1 he
    refine ⟨z, ?_, ?_⟩
    · rw [h1, ν.eX.injective (hc.1.trans (hy.trans (has i).1.symm))]
    · rw [h2, (GtValues.isNsmul_val ν m (has i).2 hc.2).1 hn]
  let c' : N'.QT n := ⟨(a'.1.1, a'.1.2 ^ m), by
    rw [NumD.mem_QT, ← pow_mul, mul_comm m n]
    exact a'.2⟩
  obtain ⟨q', hq'⟩ := B'.2.1 c'
  exact ⟨q', hq'.1.symm.trans ha'.1, (GtValues.isNsmul_val ν' m ha'.2 hq'.2).2 rfl,
    (B'.2.2 q' t' c' b' hq' hb').2 ⟨z', hz1, hz2⟩⟩

end GlobalTheory.Mum.TensTower
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.intAt_of_intAt_fibreGeneric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k) (x ζ : G.left), G.hom ζ = G.hom x → (∀ z, G.hom z = G.hom x → ζ ⤳ z) → IntAt L α s ζ → IntAt L α s x := by
  intro R _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s x ζ hζ hgen hint
  have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := G.hom x) (U := ⊤) trivial
  obtain ⟨W, hW, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := L.U j ⊓ G.hom ⁻¹ᵁ U) ⟨hj, hxU⟩
  have hζW : ζ ∈ W := (hgen x rfl).mem_open W.isOpen hxW
  have hWj : W ≤ L.U j := fun z hz => (hWle hz).1
  have hWU : W ≤ G.hom ⁻¹ᵁ U := fun z hz => (hWle hz).2
  obtain ⟨c', hxc', hc'⟩ := GlobalTheory.T.isIntegralElem_near_fibre_of_generic_point R M G hsm hqc hgi Y α t hpb W hW U hU hWU (chartVal L α s j W hWj) x ζ hxW hζ hgen
    (GlobalTheory.T.exists_basicOpen_integral_of_integral_at_point L α k s ζ hint j W hWj hW hζW)
  refine ⟨j, G.left.basicOpen c', (G.left.basicOpen_le c').trans hWj, hxc', hW.basicOpen c', ?_⟩
  convert hc' using 1
  simp only [chartVal]
  erw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.chartValue_mem_dominating_valuationSubring : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ (j : L.ι) (U : M.S.Opens) (W : G.left.Opens) (hW : W ≤ L.U j), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → ∀ (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β ((α.app W).hom c) ∈ V) → (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → β (chartVal L α s j W hW) ∈ V := by
  first | exact @GlobalTheory.Mum.chartVal_mem_of_dominates | exact GlobalTheory.Mum.chartVal_mem_of_dominates | (intros; apply GlobalTheory.Mum.chartVal_mem_of_dominates <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.rosatiGenerator_tensorPower_corresponds_formalSum : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (u' : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A')) rosatiε)), u'.IsGen → LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (zero2 D'.P.A)) (LB.oneGen D'.P.L) → ∀ (Ξ : LB.Gen (LB.LinComb D.P.L (fun v : (GlobalTheory.TensBal.sig W A A').support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => GlobalTheory.TensBal.sig W A A' v.1))), Ξ.IsGen → (∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (J : ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val Ξ (zero2 D'.P.A) z J = 1) → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → ∀ y y' : D'.X, (∏ a, GlobalTheory.TensBal.isoV T.w z J J' (D'.pt2 y y' ≫ rosatiφ D'.P.A (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') a) ^ rosatiε a) * val u' (D'.pt2 y y') z J' = val Ξ (D'.pt2 y y') z J := by
  first | exact @GlobalTheory.TensRos.ros_sig | exact GlobalTheory.TensRos.ros_sig | (intros; apply GlobalTheory.TensRos.ros_sig <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem GlobalTheory.LowFilt.exists_isometry_kerIs : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ g : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ a, (∃ e, y (g a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ _ _ y n N hn hNn hC Z Z' h hrk hN hon
  have hN0 : 0 < N := Nat.pos_of_dvd_of_pos hNn hn
  have hinj := GlobalTheory.T.injective_mod_of_surjective_mod_opposite D y n hn Z Z' h hrk hon
  obtain ⟨σ, hσZ', hσid, hσy, hσN⟩ := GlobalTheory.T.exists_linear_section_opposite_congr_mod D y n N hn hNn Z Z' h hN hon
  obtain ⟨w, hw⟩ := exists_adjoint D σ
  obtain ⟨t, ht, hiso, hdvd⟩ := GlobalTheory.T.exists_isotropic_shear_of_adjoint D y n N hn hNn hC Z Z' h σ w hσZ' hσid hσy hσN hw hinj
  have ht' : ∀ z : Z, t z - z ∈ perp D Z' := fun z => by
    obtain ⟨e, he, hze⟩ := ht z
    rw [hze, add_sub_cancel_left]
    exact (perp D Z').nsmul_mem he N
  have hker := GlobalTheory.T.ker_mod_eq_orthogonal_range_shear_add_nsmul D y n hn Z Z' h hon t ht' hiso hdvd
  obtain ⟨g, hg, hgN, hgt⟩ := GlobalTheory.T.exists_isometry_extending_isotropic_shear D N hN0 Z Z' h t ht hiso
  refine ⟨equivOfIsometry D g hg, hg, hgN, fun a => ?_⟩
  simp only [equivOfIsometry_apply]
  rw [hker (g a)]
  constructor
  · rintro ⟨b, hb, e, he⟩
    set G := equivOfIsometry D g hg
    have hG : ∀ x, G x = g x := fun x => rfl
    refine ⟨G.symm b, fun z hz => ?_, G.symm e, ?_⟩
    · have := hb (t ⟨z, hz⟩) ⟨⟨z, hz⟩, rfl⟩
      rw [← hgt ⟨z, hz⟩, ← G.apply_symm_apply b, hG, hg] at this
      exact this
    · apply G.injective
      rw [map_add (f := _), map_nsmul, G.apply_symm_apply, G.apply_symm_apply, hG, he]
  · rintro ⟨b, hb, e, rfl⟩
    refine ⟨g b, ?_, g e, by rw [map_add (f := _), map_nsmul]⟩
    rintro _ ⟨z, rfl⟩
    rw [← hgt z, hg]
    exact hb z z.2
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open GlobalTheory.Poinc.Sep.Coef

noncomputable section

namespace GlobalTheory.USep.EvG

theorem frame_ev : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N₁ = 1 → DefOver k₀ (spMap ev ≫ b.left ≫ β) →
    ∀ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)),
      (t.IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val t r z J ^ (N₁ ^ 2) * val κ (r ≫ b.left) z J = 1) →
    ∃ c ∈ k₀, (val t (spMap ev) z J).val =
      ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ b.left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ N₁ hN b hb hbdef t ht
  obtain ⟨-, hM₀, hβ, hw, -⟩ := hFB
  have HD : DescV ib β ev k₀ w := ⟨hk₀, ptsVia_of hβ, hk, hM₀, hw, fun _ _ _ h _ => h⟩
  obtain ⟨κ, hκ⟩ := GlobalTheory.FamPull.exists_kap D N₁
  let y : Over.mk (spMap ev) ⟶ D.P.A := toUnit (Over.mk (spMap ev)) ≫ b
  have hy : y ^ N₁ = 1 := by rw [← MonObj.comp_pow, hb, MonObj.comp_one]
  have hyd : RatPV β k₀ y.left := by
    show DefOver k₀ ((spMap ev ≫ b.left) ≫ β)
    rw [Category.assoc]
    exact hbdef
  obtain ⟨c, hc, ec⟩ := kap_memV HD κ hκ y hyd z J J₀ hJ hJ₀
  rw [hy] at ec
  have h1 : val t (spMap ev) z J ^ (N₁ ^ 2) * val (Z := Sp K) κ y.left z J = 1 := ht.2 κ hκ (Sp K) (spMap ev) z J hJ
  obtain ⟨c', hc', ec'⟩ := GlobalTheory.Poinc.Sep.Coef.zpow_mem ⟨c, hc, ec⟩ (-1)
  set a := om (Z := Sp K) w z J J₀ (1 : Over.mk (spMap ev) ⟶ D.P.A).left with ha
  set bb := om (Z := Sp K) w z J J₀ y.left with hbb
  set T := val t (spMap ev) z J with hT
  set Kv := val (Z := Sp K) κ y.left z J with hKv
  have alg : (T * a * bb⁻¹) ^ (N₁ ^ 2) = (bb ^ ((N₁ : ℤ) ^ 2) * a⁻¹ * a ^ (1 - (N₁ : ℤ) ^ 2) * Kv) ^ (-1 : ℤ) := by
    have hK : Kv = (T ^ (N₁ ^ 2))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hK]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    rw [← natCast_zsmul, ← natCast_zsmul]
    push_cast
    module
  obtain ⟨c'', hc'', ec''⟩ := GlobalTheory.Poinc.Sep.Coef.root_mem hk₀ (z := z) (s := (T * a * bb⁻¹).val) (n := N₁ ^ 2) (Nat.one_le_pow _ _ (by omega))
    ⟨c', hc', by rw [← Units.val_pow_eq_pow_val, alg]; exact ec'⟩
  refine ⟨c'', hc'', ?_⟩
  have e : T = (a⁻¹ * bb) * (T * a * bb⁻¹) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [e, Units.val_mul, ← ec'']
  rfl

end GlobalTheory.USep.EvG
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange


theorem _root_.GlobalTheory.T.periodGenerators_val_localUnits_mul_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a b : D.X, ∃ c ∈ k₀, (val (τ₀ a b) (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (a + b)).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
        (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c b).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c 0).left)).val * toStk z c := by
  first | exact @GlobalTheory.USep.EvG.fromBase_tau_val | exact GlobalTheory.USep.EvG.fromBase_tau_val | (intros; apply GlobalTheory.USep.EvG.fromBase_tau_val <;> assumption)
end
