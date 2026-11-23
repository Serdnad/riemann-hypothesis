module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalVanishing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.LeviLast

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem cT_mul_sq {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} (A B : Matrix (Fin k) (Fin k) R) :
    cT s (A * B) = cT s B * cT s A := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_sq {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} : cT s (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  simp only [Formalism.UG.cT, Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

def cTUnit {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} (β : GL (Fin k) R) : GL (Fin k) R where
  val := cT s (β⁻¹).1
  inv := cT s β.1
  val_inv := by rw [← cT_mul_sq, Units.mul_inv, cT_one_sq]
  inv_val := by rw [← cT_mul_sq, Units.inv_mul, cT_one_sq]

theorem adMat_mul' {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    adMat F (A * B) = adMat F A * adMat F B := Matrix.map_mul

theorem adMat_one' {a : ℕ} : adMat F (1 : Matrix (Fin a) (Fin a) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

def blk {k : ℕ} (P : Matrix (Fin k) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (g : GAd σ J) :
    Matrix (Fin k) (Fin k) (AF F ⊗[F] E) :=
  adMat F P * (matHom _ σ J g).1 * adMat F X

theorem blk_of {k : ℕ} {P : Matrix (Fin k) (Fin n) E} {X : Matrix (Fin n) (Fin k) E} (hPX : P * X = 1) {g : GAd σ J}
    {B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)} (h : (matHom _ σ J g).1 * adMat F X = adMat F X * B) : blk P X g = B := by
  rw [blk, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← adMat_mul', hPX, adMat_one', Matrix.one_mul]

theorem blk_mul {k : ℕ} {P : Matrix (Fin k) (Fin n) E} {X : Matrix (Fin n) (Fin k) E} (hPX : P * X = 1) (a : GAd σ J)
    {b : GAd σ J} {B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)} (h : (matHom _ σ J b).1 * adMat F X = adMat F X * B) :
    blk P X (a * b) = blk P X a * blk P X b := by
  rw [blk_of hPX h, blk, blk, map_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [h]

variable {r : ℕ}

theorem mem_leviOne_last {X Y : Matrix (Fin n) (Fin (r + 1)) E} {g : GAd σ J} :
    g ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ↔
      (∃ B : GL (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F X = adMat F X * B.1) ∧
      (∃ B : GL (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F Y = adMat F Y * B.1) ∧
      (∃ B ∈ ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker,
        (matHom _ σ J g).1 * adMat F X = adMat F X * B.1) := by
  have hmem : g ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ↔ ∀ k ∈ ({Fin.last r} : Finset (Fin (r + 1))),
      g ∈ GlobalTheory.StdPar.frameStab σ J (GlobalTheory.StdPar.initCols X k) ((⊤ : Subgroup (AF F ⊗[F] E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ GlobalTheory.StdPar.frameStab σ J (GlobalTheory.StdPar.initCols Y k) ((⊤ : Subgroup (AF F ⊗[F] E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ GlobalTheory.StdPar.frameStab σ J (GlobalTheory.StdPar.initCols X k) ((absE F E).ker.comap Matrix.GeneralLinearGroup.det) := by
    simp only [GlobalTheory.StdPar.leviOne, GlobalTheory.StdPar.levi, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.comap_top, MonoidHom.comap_ker]
    exact ⟨fun h k hk => ⟨(h.1 k hk).1, (h.1 k hk).2, h.2 k hk⟩, fun h => ⟨fun k hk => ⟨(h k hk).1, (h k hk).2.1⟩, fun k hk => (h k hk).2.2⟩⟩
  rw [hmem]
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨⟨B, -, h⟩, ⟨B', -, h'⟩, ⟨B'', h2, h''⟩⟩
    exact ⟨⟨B, h⟩, ⟨B', h'⟩, ⟨B'', h2, h''⟩⟩
  · rintro ⟨⟨B, h⟩, ⟨B', h'⟩, ⟨B'', h2, h''⟩⟩
    exact ⟨⟨B, Subgroup.mem_top _, h⟩, ⟨B', Subgroup.mem_top _, h'⟩, ⟨B'', h2, h''⟩⟩



open GlobalTheory.UAut GlobalTheory.EisLine in
theorem leviOne_last_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∃ φ : (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) × ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ≃ₜ* GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∀ p, ((φ p : GAd σ J) ∈ ratPts σ J ↔ (p.1 : GAd σ J) ∈ ratPts σ J ∧ (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range) := by
  intro F E _ _ _ _ _ σ n J r m X Y Z J₀ hF
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  obtain ⟨lv, hlv, -, -⟩ := GlobalTheory.SphEis.Inhabitant.existsUnique_isLv hF
  set K := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker with hK
  set A := GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} with hA
  set T := (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) with hT
  set P : Matrix (Fin (r + 1)) (Fin n) E := cT (σ : E →+* E) Y * J with hP
  set Q : Matrix (Fin (r + 1)) (Fin n) E := cT (σ : E →+* E) X * J with hQ
  have hPX : P * X = 1 := hF.dc
  have hQY : Q * Y = 1 := hF.cd
  have h1X : ∀ g : GAd σ J, (matHom _ σ J g).1 * adMat F X = adMat F X →
      (matHom _ σ J g).1 * adMat F X = adMat F X * (1 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1 := fun g h => by
    rw [Units.val_one, Matrix.mul_one]; exact h
  have hinv : ∀ a : A, blk P X (a : GAd σ J) * blk P X ((a⁻¹ : A) : GAd σ J) = 1 ∧
      blk P X ((a⁻¹ : A) : GAd σ J) * blk P X (a : GAd σ J) = 1 := by
    intro a
    obtain ⟨⟨B, hB⟩, -, -⟩ := mem_leviOne_last.1 a.2
    obtain ⟨⟨B', hB'⟩, -, -⟩ := mem_leviOne_last.1 (a⁻¹).2
    have e1 : blk P X (1 : GAd σ J) = 1 := by
      have := blk_of hPX (h1X 1 (by rw [map_one, Units.val_one, Matrix.one_mul]))
      rw [this, Units.val_one]
    refine ⟨?_, ?_⟩
    · rw [← blk_mul hPX _ hB', ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, e1]
    · rw [← blk_mul hPX _ hB, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, e1]
  let πu : A → GL (Fin (r + 1)) (AF F ⊗[F] E) := fun a =>
    ⟨blk P X (a : GAd σ J), blk P X ((a⁻¹ : A) : GAd σ J), (hinv a).1, (hinv a).2⟩
  have hπK : ∀ a : A, πu a ∈ K := by
    intro a
    obtain ⟨-, -, ⟨B, hBK, hB⟩⟩ := mem_leviOne_last.1 a.2
    have : πu a = B := Units.ext (blk_of hPX hB)
    rw [this]; exact hBK
  let π : A → K := fun a => ⟨πu a, hπK a⟩
  have hlvA : ∀ β : K, lv β ∈ A := fun β =>
    mem_leviOne_last.2 ⟨⟨β, hlv.onC β⟩, ⟨cTUnit (sigR (AF F) σ) (β : GL (Fin (r + 1)) (AF F ⊗[F] E)), hlv.onD β⟩,
      ⟨β, β.2, hlv.onC β⟩⟩
  let mm : K → A := fun β => ⟨lv β, hlvA β⟩
  have hTA : T ≤ A := by
    intro x hx
    obtain ⟨hxX, hxY⟩ := Subgroup.mem_inf.1 hx
    have hX' : (matHom _ σ J x).1 * adMat F X = adMat F X := hxX
    have hY' : (matHom _ σ J x).1 * adMat F Y = adMat F Y := hxY
    exact mem_leviOne_last.2 ⟨⟨1, by rw [hX', Units.val_one, Matrix.mul_one]⟩, ⟨1, by rw [hY', Units.val_one, Matrix.mul_one]⟩,
      ⟨1, one_mem _, by rw [hX', Units.val_one, Matrix.mul_one]⟩⟩
  have hTiff : ∀ a : A, (a : GAd σ J) ∈ T ↔ π a = 1 := by
    intro a
    constructor
    · intro hx
      exact Subtype.ext (Units.ext (blk_of hPX (h1X _ (Subgroup.mem_inf.1 hx).1)))
    · intro h1
      have hb : blk P X (a : GAd σ J) = 1 := by
        have := congrArg (fun x : K => (x : GL (Fin (r + 1)) (AF F ⊗[F] E)).1) h1
        exact this
      obtain ⟨⟨B, hB⟩, ⟨B', hB'⟩, -⟩ := mem_leviOne_last.1 a.2
      have hB1 : B.1 = 1 := (blk_of hPX hB).symm.trans hb
      have hfX : (matHom _ σ J (a : GAd σ J)).1 * adMat F X = adMat F X := by rw [hB, hB1, Matrix.mul_one]
      have hfXi : (a : GAd σ J)⁻¹ ∈ GlobalTheory.SphEis.fixG σ J X :=
        inv_mem (show (a : GAd σ J) ∈ GlobalTheory.SphEis.fixG σ J X from hfX)
      have hform := form_mul_of_mul_cols (B := 1)
        (show (matHom _ σ J (a : GAd σ J)⁻¹).1 * adMat F X = adMat F X * 1 by rw [Matrix.mul_one]; exact hfXi)
      rw [inv_inv, cT_one_sq, Matrix.one_mul] at hform
      have e1 : blk Q Y (a : GAd σ J) = B'.1 := blk_of hQY hB'
      rw [blk, hform, ← adMat_mul', hQY, adMat_one'] at e1
      have hfY : (matHom _ σ J (a : GAd σ J)).1 * adMat F Y = adMat F Y := by rw [hB', ← e1, Matrix.mul_one]
      exact Subgroup.mem_inf.2 ⟨hfX, hfY⟩
  have hπc : Continuous π := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun a : A => adMat F P * (matHom _ σ J (a : GAd σ J)).1 * adMat F X
      exact (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.comp continuous_subtype_val)).matrix_mul continuous_const
    · show Continuous fun a : A => adMat F P * (matHom _ σ J ((a⁻¹ : A) : GAd σ J)).1 * adMat F X
      exact (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.comp (continuous_subtype_val.comp continuous_inv))).matrix_mul
        continuous_const
  have hmc : Continuous mm := (hlv.cont.comp continuous_subtype_val).subtype_mk _
  have hmm : ∀ a b, mm (a * b) = mm a * mm b := fun a b => Subtype.ext (map_mul lv _ _)
  have hππ : ∀ a b, π (a * b) = π a * π b := by
    intro a b
    obtain ⟨⟨B, hB⟩, -, -⟩ := mem_leviOne_last.1 b.2
    exact Subtype.ext (Units.ext (blk_mul hPX (a : GAd σ J) hB))
  have hπm : ∀ β, π (mm β) = β := fun β => Subtype.ext (Units.ext (blk_of hPX (hlv.onC β)))
  have hc : ∀ τ ∈ T, ∀ β, τ * (mm β : GAd σ J) = mm β * τ := fun τ hτ β =>
    (GlobalTheory.SphEis.lv_comm_of_fix_cols F E σ n J (r + 1) m X Y Z J₀ hF lv hlv β τ hτ).symm
  obtain ⟨φ, hφ⟩ := GlobalTheory.LeviSplit.exists_prod_equiv A T mm π hmc hπc hmm hππ hπm hTA hTiff hc
  refine ⟨φ, fun p => ?_⟩
  rw [hφ p]
  change (p.1 : GAd σ J) * lv p.2 ∈ ratPts σ J ↔ _
  constructor
  · intro h
    have hp1 : (matHom _ σ J (p.1 : GAd σ J)).1 * adMat F X = adMat F X := (Subgroup.mem_inf.1 p.1.2).1
    have hg : (matHom _ σ J ((p.1 : GAd σ J) * lv p.2)).1 * adMat F X =
        adMat F X * (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1 := by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hlv.onC, ← Matrix.mul_assoc, hp1]
    have hb := blk_of hPX hg
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h)
    have hM : (matHom _ σ J ((p.1 : GAd σ J) * lv p.2)).1 = adMat F γ.1 := (congrArg Units.val hγ).symm
    rw [blk, hM, ← adMat_mul', ← adMat_mul'] at hb
    have hrng : (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) :
        GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range := by
      rcases subsingleton_or_nontrivial (AF F ⊗[F] E) with _ | _
      · exact ⟨1, Units.ext (Subsingleton.elim _ _)⟩
      · have hd : (P * γ.1 * X).det ≠ 0 := fun h0 => by
          have hu : IsUnit (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1.det :=
            (Matrix.isUnit_iff_isUnit_det _).1 (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).isUnit
          rw [← hb, show (adMat F (P * γ.1 * X)).det = inclR (F := F) (AF F) (P * γ.1 * X).det from
            (RingHom.map_det _ _).symm, h0, map_zero] at hu
          exact not_isUnit_zero hu
        exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, Units.ext hb⟩
    obtain ⟨δ, hδ⟩ := hrng
    refine ⟨?_, ⟨δ, hδ⟩⟩
    have h2 : lv p.2 ∈ ratPts σ J := by rw [← hδ]; exact hlv.rat δ
    have := mul_mem h (inv_mem h2)
    rwa [mul_inv_cancel_right] at this
  · rintro ⟨h1, ⟨δ, hδ⟩⟩
    refine mul_mem h1 ?_
    rw [← hδ]; exact hlv.rat δ

end GlobalTheory.SphEis.LeviLast
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.double_scaling_local_vanishing : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        (∃ T : Matrix (Fin d) (Fin d) (Fv F v),
          ((GlobalTheory.DblScal.locMatD t c p).val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) *
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * T) →
        cd p = (chrW χX t (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) : ℂ) *
          GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) (-(n : ℂ) / 2) := by
  first | exact @GlobalTheory.DblSiegelScal.scalar_siegel | exact GlobalTheory.DblSiegelScal.scalar_siegel | (intros; apply GlobalTheory.DblSiegelScal.scalar_siegel <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.weil_representation_unitary_standard_character : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  first | exact @GlobalTheory.SplitScalar.splittings_differ_by_character | exact GlobalTheory.SplitScalar.splittings_differ_by_character | (intros; apply GlobalTheory.SplitScalar.splittings_differ_by_character <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

theorem _root_.GlobalTheory.T.semidirectAverage_indicator_lower_bound : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ C : Set G, IsCompact C → ∃ (U : Set G) (c : ℝ≥0∞), IsOpen U ∧ μ U ≠ ⊤ ∧ c ≠ 0 ∧ ∀ u₀ ∈ N, ∀ m₀ ∈ M, ∀ y ∈ C, c ≤ ∫⁻ m : M, ∫⁻ u : N, U.indicator 1 ((u : G) * m * (u₀ * m₀ * y)) ∂ν ∂π := by
  first | exact @GlobalTheory.ResLine.LowerAverage.average_lower | exact GlobalTheory.ResLine.LowerAverage.average_lower | (intros; apply GlobalTheory.ResLine.LowerAverage.average_lower <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

theorem countable_subgroupOf_of_countable {G : Type} [Group G] (Λ M : Subgroup G) [Countable Λ] :
    Countable (Λ.subgroupOf M) := by
  refine Function.Injective.countable (f := fun δ : Λ.subgroupOf M => (⟨δ.1.1, δ.2⟩ : Λ)) ?_
  intro a b h
  exact Subtype.ext (Subtype.ext (congrArg (fun l : Λ => (l : G)) h))

theorem tsum_split_lattice {G : Type} [Group G] (N M Λ : Subgroup G) (disj : ∀ g ∈ N, g ∈ M → g = 1)
    (dec : ∀ γ ∈ Λ, ∃ u ∈ N, ∃ m ∈ M, u ∈ Λ ∧ m ∈ Λ ∧ γ = u * m) (f : G → ℝ≥0∞) :
    ∑' δ : Λ.subgroupOf M, ∑' γ : Λ.subgroupOf N, f ((γ.1 : G) * (δ.1 : G)) = ∑' l : Λ, f l := by
  let p : Λ.subgroupOf M × Λ.subgroupOf N → Λ := fun z => ⟨(z.2.1 : G) * (z.1.1 : G), Λ.mul_mem z.2.2 z.1.2⟩
  have hb : Function.Bijective p := by
    constructor
    · rintro ⟨δ, γ⟩ ⟨δ', γ'⟩ h
      have h1 : (γ.1 : G) * (δ.1 : G) = (γ'.1 : G) * (δ'.1 : G) := congrArg Subtype.val h
      have h2 : (γ'.1 : G)⁻¹ * γ.1 = (δ'.1 : G) * (δ.1 : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
      have h3 : (γ'.1 : G)⁻¹ * γ.1 = 1 :=
        disj _ (N.mul_mem (N.inv_mem γ'.1.2) γ.1.2) (h2 ▸ M.mul_mem δ'.1.2 (M.inv_mem δ.1.2))
      have h4 : (γ'.1 : G) = γ.1 := inv_mul_eq_one.1 h3
      have h5 : (δ.1 : G) = δ'.1 := by rw [h4] at h1; exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext (Subtype.ext h5)) (Subtype.ext (Subtype.ext h4.symm))
    · rintro ⟨l, hl⟩
      obtain ⟨u, hu, m, hm, hu', hm', e⟩ := dec l hl
      exact ⟨(⟨⟨m, hm⟩, hm'⟩, ⟨⟨u, hu⟩, hu'⟩), Subtype.ext e.symm⟩
  rw [← ENNReal.tsum_prod, ← (Equiv.ofBijective p hb).tsum_eq]
  rfl

theorem lintegral_two_step_unfolding : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G) (D : Set G), μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → ∀ φ : G → ℝ≥0∞, Measurable φ → ∫⁻ x in D, ∫⁻ m : M, ∫⁻ u : N, φ (u * m * x) ∂ν ∂π ∂μ = ν DN * π DM * ∫⁻ x, φ x ∂μ := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM S μ D hμ hD φ hφ
  haveI := countable_subgroupOf_of_countable Λ M
  haveI := countable_subgroupOf_of_countable Λ N
  haveI : LocallyCompactSpace N := S.closedN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := S.closedM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := S.haarN
  haveI := S.haarM
  have hN := (GlobalTheory.T.unimodular_and_lintegral_unfold_of_lattice N ν (Λ.subgroupOf N) DN S.haarN S.domN S.finN).2
  have hM := (GlobalTheory.T.unimodular_and_lintegral_unfold_of_lattice M π (Λ.subgroupOf M) DM S.haarM S.domM S.finM).2
  have hC := GlobalTheory.T.lintegral_conj_eq_of_semidirectLatticeDatum G N M Λ ν π DN DM S
  have A : ∀ x : G, ∫⁻ m : M, ∫⁻ u : N, φ (u * m * x) ∂ν ∂π =
      ∫⁻ b in DM, ∫⁻ c in DN, ∑' l : Λ, φ ((b : G)⁻¹ * (c : G)⁻¹ * (l * x)) ∂ν ∂π := by
    intro x
    rw [hM _ (Measurable.lintegral_prod_right' (f := fun z : M × N => φ (z.2 * z.1 * x)) (hφ.comp (by fun_prop)))]
    refine lintegral_congr fun b => ?_
    have h1 : ∀ δ : Λ.subgroupOf M, ∫⁻ u : N, φ (u * ((b⁻¹ * δ : M) : G) * x) ∂ν =
        ∫⁻ c in DN, ∑' γ : Λ.subgroupOf N, φ ((b : G)⁻¹ * (c : G)⁻¹ * ((γ.1 : G) * (δ.1 : G) * x)) ∂ν := by
      intro δ
      have h2 := hC b b.2 (fun g => φ ((b : G)⁻¹ * g * δ.1 * x)) (hφ.comp (by fun_prop))
      have h3 := hN (fun u : N => φ ((b : G)⁻¹ * u * δ.1 * x)) (hφ.comp (by fun_prop))
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left] at h2 h3 ⊢
      rw [h2, h3]
    simp only [h1]
    rw [← lintegral_tsum]
    swap
    · exact fun δ => (Measurable.tsum fun γ => hφ.comp (by fun_prop)).aemeasurable
    refine lintegral_congr fun c => ?_
    exact tsum_split_lattice N M Λ S.disj S.dec fun g => φ ((b : G)⁻¹ * (c : G)⁻¹ * (g * x))
  simp only [A]
  have B : ∀ y : G, ∫⁻ x in D, ∑' l : Λ, φ (y * (l * x)) ∂μ = ∫⁻ x, φ x ∂μ := by
    intro y
    rw [lintegral_tsum, ← lintegral_mul_left_eq_self φ y,
      hD.lintegral_eq_tsum'' fun x => φ (y * x)]
    · rfl
    · exact fun l => (hφ.comp (by fun_prop)).aemeasurable
  rw [lintegral_lintegral_swap (Measurable.aemeasurable (Measurable.lintegral_prod_right'
    (f := fun z : (G × M) × N => ∑' l : Λ, φ ((z.1.2 : G)⁻¹ * (z.2 : G)⁻¹ * (l * z.1.1)))
    (Measurable.tsum fun γ => hφ.comp (by fun_prop))))]
  have C : ∀ b : M, ∫⁻ x in D, ∫⁻ c in DN, ∑' l : Λ, φ ((b : G)⁻¹ * (c : G)⁻¹ * (l * x)) ∂ν ∂μ =
      ν DN * ∫⁻ x, φ x ∂μ := by
    intro b
    rw [lintegral_lintegral_swap (Measurable.aemeasurable
      (f := fun z : G × N => ∑' l : Λ, φ ((b : G)⁻¹ * (z.2 : G)⁻¹ * (l * z.1)))
      (Measurable.tsum fun γ => hφ.comp (by fun_prop)))]
    simp only [B]
    rw [setLIntegral_const, mul_comm]
  simp only [C]
  rw [setLIntegral_const]
  ring

end GlobalTheory.ResLine
end

section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem _root_.GlobalTheory.T.archimedeanMaximalCompact_intertwines_fockDerivativeOps : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ a b : Fin n × Fin d → mixedEmbedding.mixedSpace F, ∃ a' b' : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      ∀ f : SInf F (Fin n × Fin d), A (GlobalTheory.ThK.EvAt0.PolD.dOp a b f) = GlobalTheory.ThK.EvAt0.PolD.dOp a' b' (A f) := by
  first | exact @GlobalTheory.KInfComm.main | exact GlobalTheory.KInfComm.main | (intros; apply GlobalTheory.KInfComm.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

namespace GlobalTheory.EvalUnitUnconditional

theorem exists_const : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ μ : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by

  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE _hbij μ hμ
  obtain ⟨ei, ev, hei, hev, hpure⟩ := hE.loc
  have hSB : ∀ v : Pl (F := F), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v φ ∈ SB (Fin n × Fin d → Fv F v) := by
    intro v φ hφ
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hφ
  have hfin : ∀ v : Pl (F := F), ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ' ∈ SB (Fin n × Fin d → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => ev v φ x * starRingEnd ℂ (ev v φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x)) := by
    intro v
    have h2 : (2 : Fv F v) ≠ 0 := by
      intro h
      apply two_ne_zero (α := F)
      apply (algebraMap F (Fv F v)).injective
      rw [map_ofNat, h, map_zero]
    letI : Invertible (2 : Fv F v) := invertibleOfNonzero h2
    obtain ⟨ψv, hc, hne, A, hA⟩ := GlobalTheory.T.exists_addChar_normalizing_schrodinger_action F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure v
    exact GlobalTheory.T.local_intertwiner_unique_scalar F v (Fin n × Fin d) ψv hc hne (ev v) A (hSB v) hA
  have hinf : ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F (Fin n × Fin d),
        @integral _ ℂ _ _ (borel _) μ (fun x => ei f x * starRingEnd ℂ (ei f' x)) =
          (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
    letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    letI : Invertible (2 : mixedEmbedding.mixedSpace F) :=
      (Invertible.map (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2).copy 2 (map_ofNat _ 2).symm
    obtain ⟨ψ, hψ, A, hA⟩ := GlobalTheory.T.weil_eigen_continuous_inverse F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure
    exact GlobalTheory.T.schrodinger_intertwiner_l2_constant F (Fin n × Fin d) ψ hψ ei A hA
  exact GlobalTheory.T.restricted_tensor_schwartz F (Fin n × Fin d) e M.vac M₁.vac ei ev (fun v => (hPair.good.vac v).1) hPair.good.std hM₁.std
    (fun v => (hev v).1) hSB hpure hinf hfin μ hμ

end GlobalTheory.EvalUnitUnconditional
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_cls_eq_interNum : ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J] (L : J → LB A.X.left) (hL : ∀ j, (L j).IsLB), inter A (fun j => cls (L j) (hL j)) = (letI := A.algΓ; interNum K (structureModule A.X.left) L) := by
  intro K _ A J _ L hL
  letI := A.algΓ
  exact (interNum_eq_multiDiff K (structureModule A.X.left) hL).symm

end GlobalTheory.AV.AbVar
end
