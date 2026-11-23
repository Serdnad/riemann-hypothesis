module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle680
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle071
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle144
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle131
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle019
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DescentPowerIsoEndomorphismAbelianPartUniformiza
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.keyDatum_fibre_of_composable_baseChange : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G)) (x : KeyIn B) (x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g), KeyOn f x G L σ (fun i => y (i.cast hg)) → KeyOn (h.comp f) x' G L σ (fun i => y (i.cast hg')) → KeyPB x' x h := by
  first | exact @GlobalTheory.KeyEven.keyPB_of_keyOn_comp | exact GlobalTheory.KeyEven.keyPB_of_keyOn_comp | (intros; apply GlobalTheory.KeyEven.keyPB_of_keyOn_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.TauFormHom

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues GlobalTheory.TauForm

theorem isGrpPullback_genMap {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal R) D A G) : IsGrpPullback A.A G (jK R) (genMap U) := by
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
  exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr
    (Category.id_comp _) rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G), IsMonHom p → ∀ (ρ : D.toPre.X →+ D'.toPre.X) (s : D'.toPre.X →+ D.toPre.X), TorMatch U U' (RingHom.id R) p.left ρ → (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), IsUnit (k : R) → ∀ (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := R) F ⟶ A'.A), QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a.left ≫ genMap U = a'.left ≫ genMap U' ≫ p.left → ∃ z, q.y = s q'.y + k • z) → ∀ (a' : D'.toPre.X) (b : D.toPre.X) (x x' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre (s a') b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D'.toPre a' (ρ b) x' → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * (x' : FractionRing R) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' P hP ρ s hM hlab a' b x x' hx hx'
  haveI := hdvr
  obtain ⟨hR, hR0⟩ := id hRb
  obtain ⟨-, -, -, hRc⟩ := id hR
  haveI := hRc
  haveI := hR0
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let F := AlgebraicClosure (FractionRing R)
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback_genMap U) (TFK (R := R) F)
    ((TFK (R := R) F).hom ≫ jK R) rfl
  obtain ⟨e', he'⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback_genMap U') (TFK (R := R) F)
    ((TFK (R := R) F).hom ≫ jK R) rfl
  let Pm : (Over.mk ((TFK (R := R) F).hom ≫ jK R) ⟶ G') →* (Over.mk ((TFK (R := R) F).hom ≫ jK R) ⟶ G) :=
    { toFun := fun y => y ≫ P, map_one' := MonObj.one_comp P, map_mul' := fun y y' => MonObj.mul_comp y y' P }
  have hPm : ∀ y, (Pm y).left = y.left ≫ P.left := fun y => Over.comp_left (f := y) (g := P)
  have key : ∀ k : ℕ, IsUnit (k : R) → (k : ℤ) ∣ (ord_vw R).toFun x - (ord_vw R).toFun x' := by
    intro k hk
    obtain ⟨O, φ, σ, π, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_inertia_moves_tame_root R F ϖ hϖ k hk
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
    have hkO : IsUnit (k : O) := by simpa using hk.map φ
    obtain ⟨f, ⟨i₁, s₁, -, a₁, w₁⟩, p₁⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1
    obtain ⟨f', ⟨i₂, s₂, -, a₂, w₂⟩, p₂⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D' A' G' hG' U' F k hk1
    have wt₁ : ∀ (p p' : QkPt D.toPre F k) (τ : Multiplicative D.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
        WeilIs A.A A.L (k : ℤ) (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y))) := fun p p' τ hy hτ =>
      (w₁ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
    have c₁ : ∀ p p', QkExt σ.toRingHom p p' → (f p').left = spMap σ.toRingHom ≫ (f p).left := by
      intro p p' hpp'
      obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D A G hG U F F σ k hk1 p
      obtain ⟨y, hy⟩ := hx (f p)
      have : y = f p' := (i₁ p' y).1 ((hiff p' (f p) y hpp' hy).1 ((i₁ p (f p)).2 rfl))
      rw [← this, hy]
    have c₂ : ∀ p p', QkExt σ.toRingHom p p' → (f' p').left = spMap σ.toRingHom ≫ (f' p).left := by
      intro p p' hpp'
      obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D' A' G' hG' U' F F σ k hk1 p
      obtain ⟨y, hy⟩ := hx (f' p)
      have : y = f' p' := (i₂ p' y).1 ((hiff p' (f' p) y hpp' hy).1 ((i₂ p (f' p)).2 rfl))
      rw [← this, hy]
    have uniq : ∀ (u v : TFK (R := R) F ⟶ A.A) (c c' : Fˣ), WeilIs A.A A.L (k : ℤ) u v (unitOn c) →
        WeilIs A.A A.L (k : ℤ) u v (unitOn c') → c = c' := fun u v c c' h h' =>
      GlobalTheory.weilIs_unique_fieldPoint _ A.A A.L A.isLB F _ k u v c c' h h'

    obtain ⟨p', hp'⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB' hk0 a'
    obtain ⟨q, hq⟩ := s₁ (e.symm (Pm (e' (f' p')))) (by rw [← map_pow, ← map_pow, ← map_pow, p₂, map_one, map_one, map_one])
    have hqe : e (f q) = Pm (e' (f' p')) := by rw [hq, e.apply_symm_apply]
    have hql : (f q).left ≫ genMap U = (f' p').left ≫ genMap U' ≫ P.left := by
      rw [← he, hqe, hPm, he', Category.assoc]
    obtain ⟨z, hz⟩ := hlab F k hk q p' (f q) (f' p') ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl) hql
    rw [hp'] at hz

    obtain ⟨r, hr, -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB σ.toRingHom (RingHom.ext σ.commutes) q
    obtain ⟨r', hr', -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB' σ.toRingHom (RingHom.ext σ.commutes) p'
    obtain ⟨τ₁, q₁, -, y₁, t₁, d₁, v₁⟩ := GlobalTheory.KummerConj.conj_eq_add_tor R _ hB F O φ h₂ k σ q r hr
      (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB F O φ h₂ k hkO σ h₃ q)
    obtain ⟨τ₂, q₂, k₂, y₂, t₂, d₂, v₂⟩ := GlobalTheory.KummerConj.conj_eq_add_tor R _ hB' F O φ h₂ k σ p' r' hr'
      (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB' F O φ h₂ k hkO σ h₃ p')
    have hr₁ : e (f r) = Pm (e' (f' r')) := Over.OverMorphism.ext (by
      rw [he, hPm, he', c₁ q r hr, c₂ p' r' hr']
      simp only [Category.assoc, hql])
    have hq₁ : e (f q₁) = Pm (e' (f' q₂)) := by
      rw [a₁ _ _ _ d₁, a₂ _ _ _ d₂, map_mul, map_mul, map_mul, hqe] at hr₁
      exact mul_left_cancel hr₁
    obtain ⟨qT, yT, tT⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB (k := k) (F := F)
      (τ₂.comp (AddMonoidHom.toMultiplicative ρ)) (MonoidHom.ext fun χ => DFunLike.congr_fun k₂ _)
    have hT := hM F (fun _ => rfl) k hk _ τ₂ qT q₂ (f qT) (f' q₂) k₂ (fun _ => rfl) yT tT y₂ t₂
      ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl)
    have hfq : f qT = f q₁ := e.injective (by
      rw [hq₁]
      exact Over.OverMorphism.ext (by rw [he, hPm, he', hT, Category.assoc]))
    obtain ⟨pb, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 b
    have hτ : τ₁ (Multiplicative.ofAdd pb.y) = τ₂ (Multiplicative.ofAdd (ρ pb.y)) := by
      have h := wt₁ qT pb _ yT tT
      rw [hfq] at h
      exact uniq _ _ _ _ (wt₁ q₁ pb τ₁ y₁ t₁) h

    obtain ⟨xq, hxq⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D.toPre q.y pb.y
    obtain ⟨xz, hxz⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D.toPre z pb.y
    obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main R D.toPre hB (s a') z pb.y k x xz xq hx hxz (by rw [← hz]; exact hxq)
    obtain ⟨t, t0, tv, tσ⟩ := v₁ _ xq hxq
    obtain ⟨t', t0', tv', tσ'⟩ := v₂ _ x' (by rw [hp']; exact hx')
    have dv := GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord R F ϖ hϖ k O φ σ π hkO h₁ h₂ h₃ h₄ h₅ (t / t') (xq / x')
      (by rw [map_div₀, tσ, tσ', hτ, mul_div_mul_left _ _ (Units.ne_zero _)])
      (by rw [map_div₀, div_pow, tv, tv', Units.val_div_eq_div_val, map_div₀, map_div₀])
    rw [val_div, hu, (ord_vw R).map_mul, (ord_vw R).map_unit, (ord_vw R).map_mul, val_pow, zero_add,
      nsmul_eq_mul] at dv
    have e₀ : (ord_vw R).toFun x - (ord_vw R).toFun x' =
        ((ord_vw R).toFun x + (k : ℤ) * (ord_vw R).toFun xz - (ord_vw R).toFun x') - (k : ℤ) * (ord_vw R).toFun xz := by
      ring
    rw [e₀]
    exact dvd_sub dv (dvd_mul_right _ _)
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  exact GlobalTheory.TauForm.exists_unit_of_ord_eq (W := R) (x := x) (y := x') (by
    rw [← sub_eq_zero]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key (l ^ Int.natAbs
      ((ord_vw R).toFun x - (ord_vw R).toFun x')) (by simpa using hl.pow _)) ?_
    rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega))

end GlobalTheory.TauFormHom
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TorUniq

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem eq_zero_of_forall_dvd {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {l : ℕ} (hl : 2 ≤ l)
    (v : X) (h : ∀ n : ℕ, ∃ z : X, v = (l ^ n) • z) : v = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  refine b.repr.injective ?_
  rw [map_zero]
  ext i
  rw [Finsupp.zero_apply]
  obtain ⟨N, hN⟩ : ∃ N, N = (b.repr v i).natAbs := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ := h N
  have hd : ((l ^ N : ℕ) : ℤ) ∣ b.repr v i :=
    ⟨b.repr z i, by rw [hz, ← natCast_zsmul, map_zsmul, Finsupp.smul_apply, smul_eq_mul]⟩
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd ?_
  rw [Int.natAbs_natCast, ← hN]
  exact Nat.lt_pow_self (by omega)

theorem exists_eq_add_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {F : Type} [Field F]
    {k : ℕ} {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ k) {u v : X}
    (h : ∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd u) = τ (Multiplicative.ofAdd v)) :
    ∃ z : X, v = u + k • z := by
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ i, ∃ c : ℤ, b.repr (v - u) i = k * c := fun i => by
    let τ : Multiplicative X →* Fˣ := (zpowersHom Fˣ ζ).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
    have e : ζ ^ (b.repr u i) = ζ ^ (b.repr v i) := h τ (MonoidHom.ext fun x => by
      show (ζ ^ (b.coord i x.toAdd)) ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow])
    refine (hζ.zpow_eq_one_iff_dvd _).1 ?_
    rw [map_sub, Finsupp.sub_apply, zpow_sub, e, mul_inv_cancel]
  choose c hc using key
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [← sub_eq_iff_eq_add', ← b.sum_repr (v - u), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hc, mul_smul, natCast_zsmul]

end GlobalTheory.Poinc.TorUniq

namespace GlobalTheory.Poinc.Eq8

open GlobalTheory.Poinc.TorUniq

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem torMatch_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → ∀ ρ ρ', TorMatch U U' g β ρ → TorMatch U U' g β ρ' → ρ = ρ' := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hg ρ ρ' h h'
  have hL := GlobalTheory.firstFiveLaws
  let gK : FractionRing R →+* FractionRing V := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V (FractionRing V)).comp hg)
  have hgK : ∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r) := IsFractionRing.lift_algebraMap _
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing V) F).comp gK).toAlgebra
  have hF : ∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r)) :=
    fun r => congrArg (algebraMap (FractionRing V) F) (hgK r)

  have img : ∀ {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S], GlobalTheory.Mum.Base S → ∀ {H : Over (Sp S)} [GrpObj H]
      [IsCommMonObj H], IsSemiAbelian H → ∀ {E : DegData S (maximalIdeal S)} {B : PolAV (Sp (FractionRing S))}
      (W : Unif (maximalIdeal S) E B H) [Algebra (FractionRing S) F] (k : ℕ), 1 ≤ k → ∀ p : QkPt E.toPre F k,
      ∃ x : TFK (R := S) F ⟶ B.A, QkToAkU W.toUnifPre F k p x := by
    intro S _ _ _ hS H _ _ hH E B W _ k hk p
    obtain ⟨x, hx⟩ := GlobalTheory.TorsionAnyChar.existsTransl_any hL S (maximalIdeal S) hS.1 E B H hH W F k hk p
    exact ⟨x, (GlobalTheory.TorsionAnyChar.indAtTransl_any hL S (maximalIdeal S) hS.1 E B H hH W F k hk p x).1
      (hx 1 k le_rfl (mul_one k).symm p (one_smul _ _).symm rfl)⟩

  have key : ∀ k : ℕ, IsUnit (k : R) → ∀ τ' : Multiplicative D'.toPre.X →* Fˣ, τ' ^ k = 1 →
      ∀ χ, τ' (Multiplicative.ofAdd (ρ χ)) = τ' (Multiplicative.ofAdd (ρ' χ)) := by
    intro k hk τ' hτ' χ
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
    let τ₁ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ)
    let τ₂ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ')
    obtain ⟨q₁, y₁, t₁⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (F := F) (k := k) τ₁
      (MonoidHom.ext fun χ => DFunLike.congr_fun hτ' _)
    obtain ⟨q₂, y₂, t₂⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (F := F) (k := k) τ₂
      (MonoidHom.ext fun χ => DFunLike.congr_fun hτ' _)
    obtain ⟨q', y', t'⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D'.tau_bimult (F := F) (k := k) τ' hτ'
    obtain ⟨a₁, ha₁⟩ := img hR hG U k hk1 q₁
    obtain ⟨a₂, ha₂⟩ := img hR hG U k hk1 q₂
    obtain ⟨a', ha'⟩ := img hV hG' U' k hk1 q'
    have e₁ := h F hF k hk τ₁ τ' q₁ q' a₁ a' hτ' (fun _ => rfl) y₁ t₁ y' t' ha₁ ha'
    have e₂ := h' F hF k hk τ₂ τ' q₂ q' a₂ a' hτ' (fun _ => rfl) y₂ t₂ y' t' ha₂ ha'
    have e : a₁.left ≫ genMap U = a₂.left ≫ genMap U := e₁.trans e₂.symm

    have ea : a₁ = a₂ := by
      refine Over.OverMorphism.ext ?_
      have e' : a₁.left ≫ U.gen.inv.left = a₂.left ≫ U.gen.inv.left := by
        refine pullback.hom_ext ?_ ?_
        · simpa only [genMap, Category.assoc] using e
        · have w₁ := Over.w U.gen.inv
          have s : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := w₁
          rw [Category.assoc, Category.assoc, s, Over.w a₁, Over.w a₂]
      simpa using congrArg (· ≫ U.gen.hom.left) e'
    subst ea
    obtain ⟨z, hz, hh, hι, hadd⟩ := GlobalTheory.TorsionMapInj.qkToAk_injective_closed R (maximalIdeal R) hR.1 D A G hG U F k hk1
      q₁ q₂ a₁ ha₁ ha₂
    have hz0 : z = 0 := by
      rw [y₁, y₂, zero_add, eq_comm, ← natCast_zsmul] at hz
      exact (smul_eq_zero.1 hz).resolve_left (by exact_mod_cast hk0)
    subst hz0
    rw [GlobalTheory.TorusExt.isIota_iff_eq D.tau_bimult, map_zero] at hι
    subst hι
    rw [GlobalTheory.TorusExt.isAdd_iff_eq, add_zero] at hadd
    rw [hadd] at t₂
    have u := ((GlobalTheory.TorsionAnyChar.gtOnto_any hL R (maximalIdeal R) hR.1 D F).2.2.2.1 q₁.g t₁.1).unique t₁ t₂
    exact congrArg Units.val (DFunLike.congr_fun u (Multiplicative.ofAdd χ)) |> Units.ext
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  refine AddMonoidHom.ext fun χ => ?_
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_dvd hl2 _ fun n => ?_
  have hk : IsUnit ((l ^ n : ℕ) : R) := by simpa using hl.pow n
  have hkF : ((l ^ n : ℕ) : F) ≠ 0 := by
    have := hk.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))
    rw [map_natCast] at this
    exact this.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : F) := ⟨hkF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (l ^ n)
  have hn0 : l ^ n ≠ 0 := pow_ne_zero _ (by omega)
  obtain ⟨z, hz⟩ := exists_eq_add_nsmul (ζ := (hζ.isUnit hn0).unit) (IsPrimitiveRoot.coe_units_iff.1 hζ)
    (key (l ^ n) hk · · χ)
  exact ⟨-z, by rw [hz, smul_neg]; abel⟩

end GlobalTheory.Poinc.Eq8
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.PrimDescent

theorem isPrim_of_unif : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → GlobalTheory.PolDeg.IsPrim D.toPre.P (o.onB.act w) := by
  intro R _ _ _ I hI D A G _ _ hS U O _ _ _ o oA oG hlin w hprim
  have := hI.2.2.2
  haveI := oG.hom w
  haveI := oG.hom (1 + w)
  haveI := o.onB.hom w
  haveI := o.onB.hom (1 + w)
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim _ G U.LG (oG.act w) hprim
  have hRig := GlobalTheory.PullGenG.hasGen_one U.LG
  have h0 := (HasGen.of_gen ρ hρ).neg.add hRig
  obtain ⟨uΨ, huΨ⟩ := h0.gen U.LG.isLB (K' := Fin 4)
    ![(padd G (𝟙 _) (oG.act w)).left, 𝟙 G.left, (oG.act w).left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2] (by
      have h1' : (toUnit G ≫ η[G] : G ⟶ G) = 1 := rfl
      simp [fsum, Fin.sum_univ_four, Fin.sum_univ_five, GlobalTheory.JetSer.primφ, GlobalTheory.JetSer.primε, lf_single, padd_eq_mul, h1',
        Finsupp.single_neg, single_two, single_neg_two, Matrix.vecHead, Matrix.vecTail]
      abel)
  obtain ⟨u, hu, hn⟩ := GlobalTheory.PsiRescale.exists_normalised U.LG.isLB (oG.act w) uΨ huΨ
  have iG : ∀ i, IsMonHom ((![oG.act (1 + w), 𝟙 G, oG.act w, 1] : Fin 4 → (G ⟶ G)) i) := fun i => by
    fin_cases i
    exacts [oG.hom (1 + w), inferInstanceAs (IsMonHom (𝟙 G)), oG.hom w, inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))]
  have iB : ∀ i, IsMonHom ((![o.onB.act (1 + w), 𝟙 _, o.onB.act w, 1] : Fin 4 → (D.toPre.P.A ⟶ D.toPre.P.A)) i) :=
    fun i => by
    fin_cases i
    exacts [o.onB.hom (1 + w), inferInstanceAs (IsMonHom (𝟙 _)), o.onB.hom w,
      inferInstanceAs (IsMonHom (toUnit _ ≫ η[D.toPre.P.A]))]
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.UT.PullDescent.exists_descent U.toUnifPre GlobalTheory.allSixLaws.1.globalFns hS (fun V _ c => by
      rw [Fin.prod_univ_four]
      show c ^ (1 : ℤ) * c ^ (-2 : ℤ) * c ^ (-1 : ℤ) * c ^ (2 : ℤ) = 1
      group)
    ![oG.act (1 + w), 𝟙 G, oG.act w, 1] ![o.onB.act (1 + w), 𝟙 _, o.onB.act w, 1] (fun e i => by
      have := (U.gt e).q_hom
      fin_cases i
      · exact hlin.q_lin e (1 + w)
      · show (Over.pullback (thick R I e)).map (𝟙 G) ≫ _ = _ ≫ (Over.pullback (thick R I e)).map (𝟙 _)
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      · exact hlin.q_lin e w
      · show (Over.pullback (thick R I e)).map (1 : G ⟶ G) ≫ _ =
          _ ≫ (Over.pullback (thick R I e)).map (1 : D.toPre.P.A ⟶ D.toPre.P.A)
        letI : (Over.pullback (thick R I e)).Monoidal :=
          (Over.instBraidedPullback (f := thick R I e)).toMonoidal
        rw [CategoryTheory.Functor.map_one, CategoryTheory.Functor.map_one, MonObj.one_comp, MonObj.comp_one])
    (fun i => by
      fin_cases i
      · show (oG.act (1 + w)).left = (padd G (𝟙 _) (oG.act w)).left
        rw [oG.map_add, oG.map_one]
      all_goals rfl)
    (ψ := ![(padd D.toPre.P.A (𝟙 _) (o.onB.act w)).left, 𝟙 D.toPre.P.A.left, (o.onB.act w).left,
      (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left])
    (fun i => by
      fin_cases i
      · show (o.onB.act (1 + w)).left = (padd D.toPre.P.A (𝟙 _) (o.onB.act w)).left
        rw [o.onB.map_add, o.onB.map_one]
      all_goals rfl) u hu hn
  exact ⟨κ, hκ.1⟩

end GlobalTheory.PrimDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

def IsBC {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left) {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G) {p : ℕ} [Fact p.Prime]
    {y₀ : S.R →+* PadicAlgCl p} (ev : R →+* OO p) (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X) : Prop :=
  ∃ (ev₀ : R →+* u.V) (_ : IsLocalHom ev₀) (hD : IsPullDeg ev₀ D.toPre u.D.toPre)
    (bc : u.G ≅ (Over.pullback (specOf ev₀)).obj G),
    IsMonHom bc.hom ∧ IsPullUnif ev₀ hD bc U u.U ∧ (∀ χ, hD.xe (ε χ) = χ) ∧
    (∀ r, algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (ev₀ r)) = (ev r : PadicAlgCl p)) ∧
    ∃ t : u.A.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, t ≫ pullback.fst _ _ = u.φ ∧
      t ≫ FinalForm.φ = genMap u.U ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) ≫ gm

end GlobalTheory.Poinc.TestAtPt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem Setup.range_π_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (η : F.X) (W : Set Z), (∀ w, (spMap X₁.S.R.val.toRingHom ≫ X₁.u) w = η) → closure {i η} = W → Set.range X₁.π = W := by
  intro g n F W8 Z i X₁ η W hη hW
  haveI := X₁.fin
  have hc : IsClosedMap X₁.π.base := X₁.π.isClosedMap
  let w₀ : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
  have hgen : X₁.M.pt w₀ = genericPoint X₁.M.Z := X₁.M.pt_apply w₀
  have hpt : X₁.π (X₁.M.pt w₀) = i η := by
    have h := congrArg (fun f => f.base w₀) X₁.comp
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hη w₀]
    simpa using h
  have huniv : closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) = Set.univ := genericPoint_spec X₁.M.Z
  rw [← hW, ← hpt, hgen, ← Set.image_singleton, ← Set.image_univ, ← huniv]
  exact (hc.closure_image_eq_of_continuous X₁.π.continuous _).symm

end GlobalTheory.Poinc
end
