module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle031
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymLam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle956
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle034
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem torusExtension_of_descended : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left), IsGrpPullback G' G π β → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S), Nonempty (TorusExtension ((Over.pullback t).obj G'))) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ Sp R), Nonempty (TorusExtension ((Over.pullback p).obj G)) := by
  intro R _ S π hlft hsurj G' _ G _ β h hG' Ω _ _ p
  haveI := hlft
  haveI := hsurj
  obtain ⟨t, rfl⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective π p
  have h1 := (isGrpPullback_pullback G' t).comp h
  have h2 := isGrpPullback_pullback G (t ≫ π)
  obtain ⟨e, he, -⟩ := grpPullback_iso h1 h2
  haveI := he
  exact ⟨torusExtOfIso e (hG' Ω t).some⟩

end GlobalTheory.Mum
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PrincipalOfPairing

open GlobalTheory.CechPic

theorem lbIso_sq_diag {k : Type} [Field k] [IsAlgClosed k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {L : LB B.left} (hL : L.IsLB) (hs : Out.Sym B L) {P : LB (G2 B).left} (hP : P.IsLB)
    (hiso : LBIso (abelian₂ B L) P) : LBIso (lbPow L 2) (P.pull (lift (𝟙 B) (𝟙 B) : B ⟶ G2 B).left) := by
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hPow : (lbPow L 2).IsLB := LB.isLB_linComb hL _ _
  have hΘ := exists_gen_theta_of_isAbelianScheme k B hB L hL
  have h₀ : pull (1 : B ⟶ B).left (cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨N, hN, e⟩ := cls_surj (pull (η[B]).left (cls L hL))
    have z : cls N hN = 0 := (cls_eq_zero_iff hN).2 (DVR.exists_gen_of_isLB_local (V := k) N hN)
    rw [← e, z, map_zero]
  have h₁ : cls _ hlam = lam (cls L hL) (fst B B) (snd B B) := cls_cube_two hL _ _ hlam
  have h₂ := lam_mul_left hL hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left, lam.eq_1 _ (𝟙 B)⁻¹, inv_mul_cancel, h₀] at h₂
  have h₃ := exists_gen_neg_of_sym GlobalTheory.lawsAndExpansions.1.1.globalFns hB hL hs
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL] at h₃
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id] at h₃
  have einv : GrpObj.inv (X := B) = (𝟙 B)⁻¹ := by simp [Hom.inv_def]
  rw [einv, add_neg_eq_zero] at h₃
  rw [h₃, Over.id_left, pull_id] at h₂
  refine (cls_eq_iff hPow (pull_isLB hP _)).1 ?_
  rw [cls_lbPow hL 2 hPow, cls_pull hP, ← (cls_eq_iff hlam hP).2 hiso, h₁, pull_lam, lift_fst, lift_snd,
    eq_neg_of_add_eq_zero_left h₂.symm, two_smul]
  abel

theorem exists_principal : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∃ L : LB A.left, L.IsLB ∧ Out.Sym A L ∧ LBIso (abelian₂ A L) PP ∧ Out.RelAmple A L ∧ Out.KTriv A L := by
  intro K _ _ _ A _ _ hA P hP hs hb ha hk
  obtain ⟨L, hL, sL, iL⟩ := GlobalTheory.SymBiextHalf.exists_sym_lam K A hA P hP hs hb
  refine ⟨L, hL, sL, iL, ?_, GlobalTheory.KTrivOfLam.kTriv_of_lam_iso _ A hA P hP hk L hL iL⟩
  have := hA.proper
  have hMa := isAmpleLB_of_relAmple_of_isAffine A (pull_isLB hP _) ha
  have h2 : IsAmpleLB (lbPow L 2) := hMa.of_lbIso (isLB_lbPow hL 2) (lbIso_sq_diag hA hL sL hP iL)
  have hLa : IsAmpleLB L := (isAmpleLB_pow_iff hL (by norm_num)).1 h2
  refine relAmple_of_isAmpleLB A hL fun U hU => ?_
  have : CompactSpace (A.hom ⁻¹ᵁ U) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := A.hom) _ U.isOpen hU.isCompact)
  exact hLa.pull_of_isOpenImmersion _

end GlobalTheory.PrincipalOfPairing

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenTransport

variable {S' Z : Scheme.{0}} {π : S' ⟶ Z} {M : LB Z} {L : LB S'} {N : ℕ}

theorem w_trans (w : LB.Iso (M.pull π) (lbPow L N)) (hw : w.IsGen) {Y : Scheme.{0}} (f : Y ⟶ S') (y : Y)
    (i i' : L.ι) (k k' : M.ι) (hi : f y ∈ L.U i) (hi' : f y ∈ L.U i') (hk : (f ≫ π) y ∈ M.U k)
    (hk' : (f ≫ π) y ∈ M.U k') :
    gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) (w.s (fun _ => i, fun _ => k)) =
      gm f y (L.U i ⊓ L.U i') (L.g i i') ^ (N : ℤ) * (gm (f ≫ π) y (M.U k ⊓ M.U k') (M.g k k'))⁻¹ *
        gm f y ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) (w.s (fun _ => i', fun _ => k')) := by
  have m1 : f y ∈ (lbPow L N).U (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have m1' : f y ∈ (lbPow L N).U (fun _ => i') := Set.mem_iInter.2 fun _ => hi'
  have m2 : f y ∈ (M.pull π).U (fun _ => k) := Set.mem_iInter.2 fun _ => hk
  have m2' : f y ∈ (M.pull π).U (fun _ => k') := Set.mem_iInter.2 fun _ => hk'
  have hm : f y ∈ (lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) := ⟨⟨m1, m2⟩, ⟨m1', m2'⟩⟩
  have e := congrArg (gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')))) (hw (fun _ => i, fun _ => k) (fun _ => i', fun _ => k'))
  have e1 : gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) (w.s (fun _ => i, fun _ => k)) =
      gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k'))) (res inf_le_left (w.s (fun _ => i, fun _ => k))) :=
    (gm_res f y _ hm _).symm
  have e2 : gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k'))) (res inf_le_right (w.s (fun _ => i', fun _ => k'))) =
      gm f y ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) (w.s (fun _ => i', fun _ => k')) :=
    gm_res f y _ hm _
  have e3 := gm_div (M.pull π) (lbPow L N) f y (fun _ => i, fun _ => k) (fun _ => i', fun _ => k') hm
  refine e1.trans (e.trans ((MonoidHom.map_mul _ _ _).trans (congrArg₂ (· * ·) (e3.trans ?_) e2)))
  exact congrArg₂ (fun a b => a * b⁻¹)
    ((gm_linComb L (fun _ => 𝟙 S') (fun _ => (N : ℤ)) f y (fun _ => i) (fun _ => i') m1 m1').trans
      (by rw [Fintype.prod_unique, Category.comp_id]))
    (gm_pull_g M π f y (fun _ => k) (fun _ => k') m2 m2')

theorem alg₁ {G : Type*} [CommGroup G] (t E W : G) (N : ℕ) :
    (t * E) ^ N * (t ^ (N : ℤ) * 1⁻¹ * W)⁻¹ = E ^ N * W⁻¹ := by
  rw [zpow_natCast, inv_one, _root_.mul_one, _root_.mul_pow, _root_.mul_inv, _root_.mul_comm (t ^ N),
    _root_.mul_assoc, mul_inv_cancel_left]

theorem alg₂ {G : Type*} [CommGroup G] (E g W : G) (N : ℕ) :
    E ^ N * ((1 : G) ^ (N : ℤ) * g⁻¹ * W)⁻¹ = g * (E ^ N * W⁻¹) := by
  rw [one_zpow, _root_.one_mul, _root_.mul_inv, inv_inv, _root_.mul_left_comm]

theorem exists_strictHenselian_absolutely_closed_local_ring (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso (M.pull π) (lbPow L N)) (hw : w.IsGen)
    {A : Scheme.{0}} (a : A ⟶ S') (e : LB.Gen (L.pull a)) (he : e.IsGen) :
    ∃ t : LB.Gen (M.pull (a ≫ π)), t.IsGen ∧ ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y) (i : L.ι) (k : M.ι),
      (r ≫ a) z ∈ L.U i → (r ≫ a ≫ π) z ∈ M.U k →
      gm r z ((M.pull (a ≫ π)).U (fun _ => k)) (t.s (fun _ => k)) =
        gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
  have loc : ∀ k : M.ι, ∃ s : Γ(A, (M.pull (a ≫ π)).U (fun _ => k))ˣ, ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y)
      (i : L.ι), (r ≫ a) z ∈ L.U i → (r ≫ a ≫ π) z ∈ M.U k →
      gm r z _ s = gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
    intro k
    let V := (M.pull (a ≫ π)).U (fun _ => k)
    let W : L.ι → A.Opens := fun i => V ⊓ (L.pull a).U (fun _ => i)
    have h1 : ∀ i, W i ≤ (L.pull a).U (fun _ => i) := fun i => inf_le_right
    have h2 : ∀ i, W i ≤ a ⁻¹ᵁ ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) := fun i x hx =>
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.2 (), Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 ()⟩
    let u : ∀ i, Γ(A, W i)ˣ := fun i =>
      res (h1 i) (e.s (fun _ => i)) ^ N * (res (h2 i) (pullU a _ (w.s (fun _ => i, fun _ => k))))⁻¹
    have hu : ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y) (i : L.ι), r z ∈ W i →
        gm r z (W i) (u i) = gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
      intro Y r z i hz
      simp only [u, map_mul, map_pow, map_inv]
      exact congrArg₂ (fun p q => p ^ N * q⁻¹) (gm_res r z (h1 i) hz _)
        ((gm_res r z (h2 i) hz _).trans (gm_pull r a z _ (h2 i hz) _))
    obtain ⟨s, hs⟩ := glue_unit V W (fun i => inf_le_left) (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL (a x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, Set.mem_iInter.2 fun _ => hi⟩) u
      (fun i j x hx => by
        have hi : (𝟙 A ≫ a) x ∈ L.U i := Set.mem_iInter.1 hx.1.2 ()
        have hj : (𝟙 A ≫ a) x ∈ L.U j := Set.mem_iInter.1 hx.2.2 ()
        have hk : ((𝟙 A ≫ a) ≫ π) x ∈ M.U k := Set.mem_iInter.1 hx.1.1 ()
        have g1 : gm (𝟙 A) x ((L.pull a).U fun _ => i) (e.s fun _ => i) =
            trF (fun _ : PUnit => a) (fun _ => 1) (𝟙 A) x (fun _ => i) (fun _ => j) *
              gm (𝟙 A) x ((L.pull a).U fun _ => j) (e.s fun _ => j) := gen_trans he (𝟙 A) x hx.1.2 hx.2.2
        rw [hu A (𝟙 A) x i hx.1, hu A (𝟙 A) x j hx.2, g1,
          w_trans w hw (𝟙 A ≫ a) x i j k k hi hj hk hk, gm_self hM _ x hk]
        simp only [trF, Fintype.prod_unique, zpow_one]
        exact alg₁ _ _ _ N)
    refine ⟨s, fun Y r z i hi hk => ?_⟩
    have hz : r z ∈ W i := ⟨Set.mem_iInter.2 fun _ => hk, Set.mem_iInter.2 fun _ => hi⟩
    rw [← gm_res r z (inf_le_left : W i ≤ V) hz, hs i, hu Y r z i hz]
  choose s hs using loc
  refine ⟨⟨fun k => s (k ())⟩, fun k k' => unit_ext fun x hx => ?_, fun Y r z i k hi hk => hs k Y r z i hi hk⟩
  refine (gm_res (𝟙 A) x _ hx _).trans (Eq.trans ?_ ((MonoidHom.map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_pull_g M (a ≫ π) (𝟙 A) x k k' hx.1 hx.2) (gm_res (𝟙 A) x _ hx _))).symm)
  obtain ⟨i, hi⟩ := exists_chart hL ((𝟙 A ≫ a) x)
  have hk : ((𝟙 A ≫ a) ≫ π) x ∈ M.U (k ()) := Set.mem_iInter.1 hx.1 ()
  have hk' : ((𝟙 A ≫ a) ≫ π) x ∈ M.U (k' ()) := Set.mem_iInter.1 hx.2 ()
  have v1 : gm (𝟙 A) x ((M.pull (a ≫ π)).U k) (s (k ())) = _ := hs (k ()) A (𝟙 A) x i hi hk
  have v2 : gm (𝟙 A) x ((M.pull (a ≫ π)).U k') (s (k' ())) = _ := hs (k' ()) A (𝟙 A) x i hi hk'
  rw [v1, v2, w_trans w hw (𝟙 A ≫ a) x i i (k ()) (k' ()) hi hi hk hk', gm_self hL (𝟙 A ≫ a) x hi, Category.assoc]
  exact alg₂ _ _ _ N

theorem transport : ∀ (S' Z : Scheme.{0}) (π : S' ⟶ Z) (M : LB Z) (L : LB S') (N : ℕ), M.IsLB → L.IsLB → LBIso (M.pull π) (lbPow L N) → ∃ T : ∀ (A : Scheme.{0}) (a : A ⟶ S'), LB.Gen (L.pull a) → LB.Gen (M.pull (a ≫ π)), (∀ (A : Scheme.{0}) (a : A ⟶ S') (e : LB.Gen (L.pull a)), e.IsGen → (T A a e).IsGen) ∧ ∀ (A A' Y : Scheme.{0}) (a : A ⟶ S') (a' : A' ⟶ S') (e : LB.Gen (L.pull a)) (e' : LB.Gen (L.pull a')) (r : Y ⟶ A) (r' : Y ⟶ A'), e.IsGen → e'.IsGen → r ≫ a = r' ≫ a' → (∀ (z : Y) (J : (Y ⟶ S') → L.ι), Good L z J → val (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z J = val (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z J) → ∀ (z : Y) (J : (Y ⟶ Z) → M.ι), Good M z J → val (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) (T A a e) r z J = val (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) (T A' a' e') r' z J := by
  intro S' Z π M L N hM hL hw0
  obtain ⟨w, hw⟩ := hw0
  classical
  refine ⟨fun A a e => if he : e.IsGen then (exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose else ⟨fun _ => 1⟩,
    fun A a e he => ?_, ?_⟩
  · simp only [dite_eq_left he]
    exact (exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose_spec.1
  · intro A A' Y a a' e e' r r' he he' hr hval z J hJ
    simp only [dite_eq_left he, dite_eq_left he']
    have hk : (r ≫ a ≫ π) z ∈ M.U (J (r ≫ a ≫ π)) := hJ _
    have hk'e : J (r' ≫ a' ≫ π) = J (r ≫ a ≫ π) := by rw [← Category.assoc, ← hr, Category.assoc]
    have hk' : (r' ≫ a' ≫ π) z ∈ M.U (J (r ≫ a ≫ π)) := hk'e ▸ hJ _
    obtain ⟨i, hi⟩ := exists_chart hL ((r ≫ a) z)
    have hi' : (r' ≫ a') z ∈ L.U i := by rw [← hr]; exact hi
    obtain ⟨JL, hJL, eJL⟩ := exists_good L hL z (K := PUnit) (fun _ => r ≫ a) (fun _ => i)
      (fun _ _ _ => rfl) (fun _ => hi)
    have v1 := val_of (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z JL (fun _ => i) (fun _ => eJL ())
    have v2 := val_of (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z JL (fun _ => i)
      (fun _ => by rw [← hr]; exact eJL ())
    have hv := hval z JL hJL
    rw [v1, v2] at hv
    rw [val_of (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) _ r z J (fun _ => J (r ≫ a ≫ π))
        (fun _ => rfl),
      val_of (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) _ r' z J (fun _ => J (r ≫ a ≫ π))
        (fun _ => hk'e)]
    refine (((exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose_spec.2 Y r z i _ hi hk).trans ?_).trans
      ((exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a' e' he').choose_spec.2 Y r' z i _ hi' hk').symm
    rw [hr]
    congr 1
    exact congrArg (· ^ N) hv

end GlobalTheory.GenTransport
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumDescent

theorem qc_qs_tensor {S : Scheme.{0}} (A : Over S) [IsProper A.hom] :
    QuasiCompact (A ⊗ A).hom ∧ QuasiSeparated (A ⊗ A).hom := by
  have e : (A ⊗ A).hom = pullback.fst A.hom A.hom ≫ A.hom := rfl
  rw [e]; exact ⟨inferInstance, inferInstance⟩

theorem exists_galois_polAV : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∀ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB → Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) → Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → ∃ (E : Type) (_ : Field E) (_ : Algebra K E), FiniteDimensional K E ∧ IsGalois K E ∧ ∃ (A₁ : PolAV (Sp E)) (gen : (Over.pullback (spMap (algebraMap K E))).obj A ≅ A₁.A), IsMonHom gen.hom ∧ ∀ κ : (G2 ((Over.pullback (spMap (algebraMap K E))).obj A)).left ⟶ (G2 A).left, Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K E))) κ → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K E))).obj A) (A₁.L.pull gen.hom.left)) (PP.pull κ) := by
  intro K _ _ A _ _ hA PP hPP Ω _ _ _ _ κ hκ L hL hS hΛ hAmp hKT
  haveI := hA.proper
  haveI := hA.smooth
  let σΩ : K →+* Ω := algebraMap K Ω
  let AΩ := (Over.pullback (spMap σΩ)).obj A
  have hAΩ : IsAbelianScheme AΩ := isAbelianScheme_pullback_obj _ A hA
  have hpΩ : IsGrpPullback AΩ A (spMap σΩ) (pullback.fst A.hom (spMap σΩ)) := isGrpPullback_pullback A _

  obtain ⟨F, hF, H⟩ := GlobalTheory.LBDescent.exists_finite_subextension_cls K Ω A.left AΩ.left A.hom AΩ.hom
    (pullback.fst A.hom (spMap σΩ)) hpΩ.1 L hL
  let f : Sp F ⟶ Sp K := spMap (algebraMap K F)
  let AF := (Over.pullback f).obj A
  have hAF : IsAbelianScheme AF := isAbelianScheme_pullback_obj f A hA
  have hpF : IsGrpPullback AF A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  have hcomp : spMap (algebraMap F Ω) ≫ f = spMap σΩ := by
    simp only [f, σΩ, spMap]
    rw [← Spec.map_comp]
    congr 1
  have w : pullback.fst A.hom (spMap σΩ) ≫ A.hom = (AΩ.hom ≫ spMap (algebraMap F Ω)) ≫ f := by
    rw [Category.assoc, hcomp]
    exact hpΩ.1.w
  let jm : AΩ.left ⟶ AF.left := pullback.lift (pullback.fst A.hom (spMap σΩ)) (AΩ.hom ≫ spMap (algebraMap F Ω)) w
  have hjf : jm ≫ pullback.fst A.hom f = pullback.fst A.hom (spMap σΩ) := pullback.lift_fst _ _ _
  have hjs : jm ≫ AF.hom = AΩ.hom ≫ spMap (algebraMap F Ω) := pullback.lift_snd _ _ _
  have hj : IsGrpPullback AΩ AF (spMap (algebraMap F Ω)) jm :=
    IsGrpPullback.cancel hpF (hpΩ.congr hcomp.symm hjf.symm) hjs
  obtain ⟨x, hx⟩ := H AF.left AF.hom (pullback.fst A.hom f) (IsPullback.of_hasPullback _ _) jm hjf hjs
  obtain ⟨L₁, hL₁, rfl⟩ := CechPic.cls_surj x
  have hw : LBIso L (L₁.pull jm) := by
    rw [← CechPic.cls_eq_iff hL (pull_isLB hL₁ jm), CechPic.cls_pull hL₁ jm (pull_isLB hL₁ jm)]
    exact hx.symm

  have hPPlb : PP.IsLB := hPP
  obtain ⟨κF, hκF⟩ : ∃ κF : (G2 AF).left ⟶ (G2 A).left, IsSquare (pullback.fst A.hom f) κF :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hpF.1.w⟩
  obtain ⟨jm₂, hjm₂⟩ : ∃ jm₂ : (G2 AΩ).left ⟶ (G2 AF).left, IsSquare jm jm₂ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hj.1.w⟩
  have hΛF : (abelian₂ AF L₁).IsLB := DVR.linComb_isLB _ hL₁ _ _
  have hΛΩ : (abelian₂ AΩ L).IsLB := DVR.linComb_isLB _ hL _ _
  have hNF : (PP.pull κF).IsLB := pull_isLB hPPlb κF
  have eΩ : κ = jm₂ ≫ κF := by
    have h := GlobalTheory.ZM.SiegPull.isSquare_comp hjm₂ hκF
    rw [hjf] at h
    exact GlobalTheory.LamPull.isSquare_unique hκ h
  have isoΩ : LBIso ((abelian₂ AF L₁).pull jm₂) ((PP.pull κF).pull jm₂) :=
    LBIso.trans (pull_isLB hΛF _) hΛΩ (pull_isLB hNF _)
      (GlobalTheory.LamPull.lbIso_lam_pull hj hL₁ hL hw hjm₂).symm
      (LBIso.trans hΛΩ (pull_isLB hPPlb _) (pull_isLB hNF _) hΛ
        (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPPlb κF jm₂ eΩ).symm)
  haveI := hAF.proper
  haveI := hAF.smooth
  have hqq := qc_qs_tensor AF
  obtain ⟨s, hs⟩ := GlobalTheory.lbIso_descends_to_subfield_containing_finset F Ω (algebraMap F Ω) (G2 AF) (G2 AΩ) jm₂
    (abelian₂ AF L₁) (PP.pull κF) (GlobalTheory.SiegelDescent.isPullback_square hj.1 jm₂ hjm₂) hqq.1 hqq.2 hΛF hNF isoΩ

  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let F' : IntermediateField K Ω := F ⊔ IntermediateField.adjoin K (s : Set Ω)
  haveI : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  haveI : FiniteDimensional K F' := IntermediateField.finiteDimensional_sup _ _
  let E : IntermediateField K Ω := IntermediateField.normalClosure K F' Ω
  haveI hEf : FiniteDimensional K E := normalClosure.is_finiteDimensional K F' Ω
  haveI hEg : IsGalois K E := by
    haveI : Normal K E := inferInstance
    exact IsGalois.mk
  have hFE : F ≤ E := le_sup_left.trans F'.le_normalClosure
  have hsE : (s : Set Ω) ⊆ E := fun y hy =>
    F'.le_normalClosure (le_sup_right (a := F) (IntermediateField.subset_adjoin K _ hy))
  let α : F →+* E := (IntermediateField.inclusion hFE).toRingHom
  let e : Sp E ⟶ Sp K := spMap (algebraMap K E)
  let AE := (Over.pullback e).obj A
  have hAE : IsAbelianScheme AE := isAbelianScheme_pullback_obj e A hA
  have hpE : IsGrpPullback AE A e (pullback.fst A.hom e) := isGrpPullback_pullback A e
  have hcα : spMap α ≫ f = e := by
    simp only [f, e, α, spMap]
    rw [← Spec.map_comp]
    congr 1
  have wE : pullback.fst A.hom e ≫ A.hom = (AE.hom ≫ spMap α) ≫ f := by
    rw [Category.assoc, hcα]
    exact hpE.1.w
  let χ : AE.left ⟶ AF.left := pullback.lift (pullback.fst A.hom e) (AE.hom ≫ spMap α) wE
  have hχf : χ ≫ pullback.fst A.hom f = pullback.fst A.hom e := pullback.lift_fst _ _ _
  have hχs : χ ≫ AF.hom = AE.hom ≫ spMap α := pullback.lift_snd _ _ _
  have hχ : IsGrpPullback AE AF (spMap α) χ := IsGrpPullback.cancel hpF (hpE.congr hcα.symm hχf.symm) hχs
  obtain ⟨χ₂, hχ₂⟩ : ∃ χ₂ : (G2 AE).left ⟶ (G2 AF).left, IsSquare χ χ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hχ.1.w⟩
  have isoE : LBIso ((abelian₂ AF L₁).pull χ₂) ((PP.pull κF).pull χ₂) :=
    hs E α (algebraMap E Ω) (RingHom.ext fun _ => rfl) (fun y hy => ⟨⟨y, hsE hy⟩, rfl⟩) (G2 AE) χ₂
      (GlobalTheory.SiegelDescent.isPullback_square hχ.1 χ₂ hχ₂)

  let LE : LB AE.left := L₁.pull χ
  have hLE : LE.IsLB := pull_isLB hL₁ χ
  have hcE : spMap (algebraMap E Ω) ≫ e = spMap σΩ := by
    simp only [e, σΩ, spMap]
    rw [← Spec.map_comp]
    congr 1
  have wΩ : pullback.fst A.hom (spMap σΩ) ≫ A.hom = (AΩ.hom ≫ spMap (algebraMap E Ω)) ≫ e := by
    rw [Category.assoc, hcE]
    exact hpΩ.1.w
  let jE : AΩ.left ⟶ AE.left := pullback.lift (pullback.fst A.hom (spMap σΩ)) (AΩ.hom ≫ spMap (algebraMap E Ω)) wΩ
  have hjEf : jE ≫ pullback.fst A.hom e = pullback.fst A.hom (spMap σΩ) := pullback.lift_fst _ _ _
  have hjEs : jE ≫ AE.hom = AΩ.hom ≫ spMap (algebraMap E Ω) := pullback.lift_snd _ _ _
  have hjE : IsGrpPullback AΩ AE (spMap (algebraMap E Ω)) jE :=
    IsGrpPullback.cancel hpE (hpΩ.congr hcE.symm hjEf.symm) hjEs
  have hαΩ : spMap (algebraMap E Ω) ≫ spMap α = spMap (algebraMap F Ω) := by
    simp only [α, spMap]
    rw [← Spec.map_comp]
    congr 1
  have ejm : jm = jE ≫ χ := by
    apply pullback.hom_ext
    · rw [hjf, Category.assoc, hχf, hjEf]
    · show jm ≫ AF.hom = (jE ≫ χ) ≫ AF.hom
      rw [hjs, Category.assoc, hχs, ← Category.assoc, hjEs, Category.assoc, hαΩ]
  have hwE : LBIso L (LE.pull jE) :=
    LBIso.trans hL (pull_isLB hL₁ jm) (pull_isLB hLE jE) hw
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull hL₁ χ jE ejm).symm
  have hd := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend E Ω (algebraMap E Ω) AE AΩ jE LE L hAE hjE hLE hL hwE
  haveI := hAE.proper
  haveI := hAE.smooth
  have ha := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension E Ω (algebraMap E Ω) AE AΩ jE hjE LE L hLE hL
    hwE hAΩ.proper hAmp hKT
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim E AE hAE
  have hrig : Out.Rigidified AE LE := by
    have : Subsingleton (𝟙_ (Over (Sp E))).left := inferInstanceAs (Subsingleton (PrimeSpectrum E))
    exact GlobalTheory.PolDescent.exists_gen_of_unique (default : PrimeSpectrum E) (pull_isLB hLE _)
  let A₁ : Out.PolAV (Sp E) :=
    { A := AE, isAb := hAE, g := g, smoothDim := hg, L := LE, isLB := hLE, rigid := hrig,
      sym := hd.2.1 hS, ample := ha.2.1, ktriv := ha.2.2 }
  refine ⟨E, inferInstance, inferInstance, hEf, hEg, A₁, Iso.refl _, ?_, fun κ' hκ' => ?_⟩
  · show IsMonHom (𝟙 AE); infer_instance
  have e' : κ' = χ₂ ≫ κF := by
    have h := GlobalTheory.ZM.SiegPull.isSquare_comp hχ₂ hκF
    rw [hχf] at h
    exact GlobalTheory.LamPull.isSquare_unique hκ' h
  have hLE' : (LE.pull (𝟙 AE.left)).IsLB := pull_isLB hLE _
  have k₁ : LBIso (abelian₂ AE (LE.pull (𝟙 AE.left))) ((abelian₂ AF L₁).pull χ₂) :=
    GlobalTheory.LamPull.lbIso_lam_pull hχ hL₁ hLE' (GlobalTheory.ArcDataDescent.lbIso_pull_pull hL₁ χ (𝟙 _) (Category.id_comp χ).symm) hχ₂
  have k₂ : LBIso ((PP.pull κF).pull χ₂) (PP.pull κ') := GlobalTheory.ArcDataDescent.lbIso_pull_pull hPPlb κF χ₂ e'
  exact LBIso.trans (DVR.linComb_isLB _ hLE' _ _) (pull_isLB hΛF _) (pull_isLB hPPlb _) k₁
    (LBIso.trans (pull_isLB hΛF _) (pull_isLB hNF _) (pull_isLB hPPlb _) isoE k₂)

end GlobalTheory.MumDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

theorem _root_.GlobalTheory.T.relAmple_diagonal_pullback_baseChange : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (t : T ⟶ S) (B : Over T) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsPullback β B.hom A.hom t → IsSquare β β₂ → RelAmple B ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) := by
  first | exact @GlobalTheory.DiagAmpleBC.relAmple_diag_pull | exact GlobalTheory.DiagAmpleBC.relAmple_diag_pull | (intros; apply GlobalTheory.DiagAmpleBC.relAmple_diag_pull <;> assumption)
end
