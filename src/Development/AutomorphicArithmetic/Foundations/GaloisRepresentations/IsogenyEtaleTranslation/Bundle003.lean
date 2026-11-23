module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (Integ)
open scoped TensorProduct

theorem UpperTheory.Gal.FixZ.scalEx_of :
    UpperTheory.Gal.G3.SysOf → UpperTheory.Gal.FixZ.ScalEx := by
  intro hS p _ D G L h hI
  obtain ⟨f, u, c, k, hsys, -, hk, -⟩ := hS p D G L h hI
  have hkp : k.Coprime p := hsys.2.1
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : p = 1 := by simpa using hkp
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hone : IsIntAf (1 : AfP p) := fun v => by rw [map_one]; exact one_mem _
  have hact : ∀ v, L.actG (GlobalTheory.W2.scalarAf G (GlobalTheory.W2.natUnit p k hk0)) v = k • v :=
    GlobalTheory.W2.actG_natScalar L k hk0
  refine ⟨k, GlobalTheory.W2.scalarAf G (GlobalTheory.W2.natUnit p k hk0), Nat.pos_of_ne_zero hk0, hkp,
    ⟨fun g => GlobalTheory.W2.scalarAf_comm _ g, hact, 1, 1, hone, hone, one_mul 1, ?_⟩, ?_, ?_⟩
  · show ((GlobalTheory.W2.natUnit p k hk0 : (AfP p)ˣ) : AfP p) * (GlobalTheory.W2.natUnit p k hk0 : (AfP p)ˣ) = ((k ^ 2 : ℕ) : AfP p) * 1
    have e : ((GlobalTheory.W2.natUnit p k hk0 : (AfP p)ˣ) : AfP p) = (k : AfP p) := by
      show algebraMap ℚ (AfP p) (k : ℚ) = _
      rw [map_natCast]
    rw [e, mul_one]; push_cast; ring
  · intro v hv
    rw [hact]
    exact nsmul_mem hv k
  · intro v hv
    rw [map_mul, Module.End.mul_apply, hact]
    exact hk v hv
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ)

private theorem ev_nsmul {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) (n : ℕ) (hn : 0 < n) (d : ℕ) (x : G.La) :
    I.ev n (d • x) = I.ev n x ^ d := by
  have h0 : I.ev n 0 = 1 := by
    have := I.add n 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  induction d with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ d ih => rw [succ_nsmul, I.add, ih, pow_succ]

private theorem isMonHom_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  constructor
  · rw [MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]
  · rw [MonObj.comp_pow, Category.comp_id, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst,
      tensorHom_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, mul_pow]

private theorem pow_comp_hom {S : Scheme.{0}} {A B Z : Over S} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f]
    (x : Z ⟶ A) (n : ℕ) : (x ^ n) ≫ f = (x ≫ f) ^ n := MonObj.pow_comp x n f

theorem UpperTheory.Gal.FixZ.witScal_of :
    UpperTheory.Gal.G3.RelComp → UpperTheory.Gal.FixZ.WitScal := by
  intro hR p _ D G L gb N X d z hd hdp hz
  obtain ⟨-, hact, hmul⟩ := hz
  have hid : ∃ m : GObjMap X.univ X.univ (𝟙 X.X), m.φ = 𝟙 _ :=
    ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id X.univ.A, sq := ⟨by simp, by simp⟩,
       act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id X.univ.isLB, eta := fun y => by simp }, rfl⟩
  obtain ⟨m, hm⟩ := hid
  have hmon : IsMonHom ((𝟙 X.univ.A) ^ d) := isMonHom_pow _ d
  have hcomm : ∀ c : D.O, X.univ.act.act c ≫ ((𝟙 X.univ.A) ^ d) = ((𝟙 X.univ.A) ^ d) ≫ X.univ.act.act c := by
    intro c
    haveI := X.univ.act.hom c
    rw [MonObj.comp_pow, pow_comp_hom, Category.comp_id, Category.id_comp]
  refine ⟨Category.id_comp _, X.univ, (𝟙 X.univ.A) ^ d, m, ?_, by rw [hm]; simp⟩
  refine ⟨hmon, hcomm, ⟨𝟙 _, d, inferInstance, fun c => ?_, Category.comp_id _, Category.id_comp _, hdp⟩,
    ⟨d ^ 2, hdp.pow_left 2, ⟨GlobalTheory.T.lbIso_lbPow_sq_pull_sq2_of_isGen_of_relAmple _ _ X.univ.ab X.univ.P X.univ.isLB X.univ.rig₁ X.univ.rig₂ X.univ.ample d⟩, hmul⟩,
    fun k _ _ t β ht => ?_⟩
  · rw [Category.comp_id, Category.id_comp]
  · obtain ⟨I, hI⟩ := X.univ.geom k t β ht
    refine ⟨I, I, hI, hI, fun n hn hnp x y => ?_⟩
    have h1 := (hR p D G L ℂ gb X.X X.s _ _ _ X.univ X.univ X.univ k t I I I (𝟙 _) (𝟙 _) 1 1 inferInstance inferInstance
      (UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _))).1 n hn hnp (d • x) y
    have hev : I.ev n x ≫ ((𝟙 X.univ.A) ^ d) = I.ev n (d • x) ≫ 𝟙 _ := by
      rw [MonObj.comp_pow, Category.comp_id, Category.comp_id]
      exact (ev_nsmul I n hn d x).symm
    have hin : inAf D (d • x) = d • inAf D x := GlobalTheory.AdelicSim.inAf_nsmul D d x
    rw [hev, h1]
    simp only [map_one, Module.End.one_apply, hin, hact]
end
