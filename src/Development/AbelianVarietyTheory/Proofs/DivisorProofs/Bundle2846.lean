module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle714
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle131
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle037
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle066
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle032
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle029
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.SympQ

theorem qEq_one_of_wp {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ} (hk : (k : C) ≠ 0)
    (hdiv : ∀ x : N.A, ∃ y, y ^ k = x)
    (nd : ∀ b : N.A, b ^ k = 1 → (∀ b', b' ^ k = 1 → N.weil k b b' = 1) → b = 1) (p : N.QT k)
    (hp : ∀ p', N.wp p p' = 1) : N.QEq p 1 := by
  have hk0 : k ≠ 0 := fun h => hk (by rw [h, Nat.cast_zero])
  have h3 : ∀ y : N.X, ∃ p : N.QT k, p.1.1.toAdd = y := fun y => by
    obtain ⟨b, hb⟩ := hdiv (N.io y).b
    obtain ⟨g, -, h⟩ := QStr.root_over N hk0 (N.io y) b hb
    exact ⟨⟨(Multiplicative.ofAdd y, g), h⟩, rfl⟩
  obtain ⟨p₀, hq, h1, hb⟩ := (QStr.orth_iff N hk nd p).1 fun p' _ => hp p'
  have : p₀ = 1 := by
    refine Subtype.ext (Prod.ext h1 (NumD.Gt.ext hb (funext fun χ => ?_)))
    obtain ⟨p', rfl⟩ := h3 χ
    rw [← (WpPairing.wp_pairing C N _ p₀ p' p').2.2.2.2.2.1 h1 hb, ← WpPairing.wp_congr_left N hq p', hp p']
    rfl
  rwa [this] at hq

theorem wpQ_nondeg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → ∀ x : GlobalTheory.SympQ.Qq N n, (∀ y, GlobalTheory.SympQ.wpQ N n x y = 1) → x = 1 := by
  intro R _ _ _ hR D F _ _ _ N ν n hn x hx
  obtain ⟨⟨h1, h2, h3, h4⟩, hc⟩ := hR
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  have : CharZero F := by
    have : CharZero (FractionRing R) := inferInstance
    exact charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have h0 : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨hW, -⟩ := GlobalTheory.ThetaInValues.brUth_of_laws hL R D.toPre D.psi_even D.tau_bimult F N ν
  have tor : ∀ (b : N.A) (k : ℕ), ν.eA b ^ k = 1 ↔ b ^ k = 1 := fun b k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  induction x using QuotientGroup.induction_on with
  | H p =>
    have hq : N.QEq p 1 := by
      refine qEq_one_of_wp N h0 (fun a => ?_) (fun b hb h => ?_) p fun p' => hx (QuotientGroup.mk p')
      · obtain ⟨y, hy⟩ := GlobalTheory.ValuesTorsion.exists_pow_eq hL D.toPre.P (jFK (R := R) F ≫ jK R) (ν.eA a) hn
        exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
      · refine ν.eA.map_eq_one_iff.1 (GlobalTheory.ThetaRep.eq_one_of_weilIs hL D.toPre.P (jFK (R := R) F ≫ jK R) h0 _
          ((tor _ _).2 hb) fun y hy => ?_)
        obtain ⟨b', rfl⟩ := ν.eA.surjective y
        have hb' := (tor _ _).1 hy
        have := hW n hn b b' hb hb'
        rwa [h b' hb', show unitOn (1 : Fˣ) = 1 from map_one (Units.map _)] at this
    exact (qEq_iff_mk_eq N p 1).1 hq

end GlobalTheory.SympQ
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SympQ.PushPow

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem cubN_mul_iter (h : IsCub θ) (n m : ℕ) (b x : A) :
    cubN θ (n * m) 1 b x = cubN θ n 1 (b ^ m) x * cubN θ m 1 b x ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e : cubN θ ((n + 1) * m) 1 b x = cubN θ (n * m) 1 b x * cubN θ m (b ^ (n * m)) b x := by
      rw [Nat.succ_mul]
      simp only [cubN, Finset.prod_range_add]
      refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
      rw [_root_.one_mul, pow_add]
    have s1 : cubN θ (n + 1) 1 (b ^ m) x = cubN θ n 1 (b ^ m) x * θ ((b ^ m) ^ n) (b ^ m) x := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    rw [e, ih, h.N_split m (b ^ (n * m)) b x, s1, ← pow_mul' b n m, pow_succ (cubN θ m 1 b x) n]
    ac_rfl

theorem cubN_pow_right (h : IsCub θ) (k m : ℕ) (b x : A) :
    cubN θ k 1 b (x ^ m) * cubN θ m 1 x b ^ k = cubN θ k 1 b x ^ m * cubN θ m 1 x (b ^ k) := by
  induction m with
  | zero => simp [cubN, h.face₃]
  | succ m ih =>
    have e := h.N_add k 1 b (x ^ m) x
    rw [h.face, _root_.mul_one, _root_.one_mul] at e
    have s1 : cubN θ (m + 1) 1 x b = cubN θ m 1 x b * θ (x ^ m) x b := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have s2 : cubN θ (m + 1) 1 x (b ^ k) = cubN θ m 1 x (b ^ k) * θ (x ^ m) x (b ^ k) := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have t1 : θ b (x ^ m) x = θ (x ^ m) x b := by rw [h.s01, h.s12]
    have t2 : θ (b ^ k) (x ^ m) x = θ (x ^ m) x (b ^ k) := by rw [h.s01, h.s12]
    rw [t1, t2] at e
    rw [pow_succ x, s1, s2]
    apply Additive.ofMul.injective
    replace e := congrArg Additive.ofMul e
    replace ih := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow] at e ih ⊢
    linear_combination (norm := module) e + ih

variable {O : Type} [CommRing O] (N : NumD O)

theorem wp_pushRep (n m : ℕ) (hn : 0 < n) (p q : N.QT (n * m)) :
    N.wp (pushRep N (n * m) n p) (pushRep N (n * m) n q) = N.wp p q ^ m := by
  have hd : n ∣ n * m := dvd_mul_right n m
  have hM : n * m / n = m := Nat.mul_div_cancel_left m hn
  simp only [NumD.wp, NumD.tk, pushRep_fst N hd, pushRep_snd N hd, hM, NumD.Gt.pow_b]
  have ps1 := NumD.Gt.pow_s p.1.2 m q.1.1.toAdd
  have ps2 := NumD.Gt.pow_s q.1.2 m p.1.1.toAdd
  rw [← N.QT_pow_b q] at ps1
  rw [← N.QT_pow_b p] at ps2
  have i1 := cubN_mul_iter N.cub n m q.1.2.b p.1.2.b
  have i2 := cubN_mul_iter N.cub n m p.1.2.b q.1.2.b
  have a := cubN_pow_right N.cub n m (p.1.2.b ^ m) q.1.2.b
  have b := cubN_pow_right N.cub n m (q.1.2.b ^ m) p.1.2.b
  have c := cubN_pow_right N.cub m m q.1.2.b p.1.2.b
  rw [← pow_mul'] at a b
  apply Additive.ofMul.injective
  replace ps1 := congrArg Additive.ofMul ps1
  replace ps2 := congrArg Additive.ofMul ps2
  replace i1 := congrArg Additive.ofMul i1
  replace i2 := congrArg Additive.ofMul i2
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at ps1 ps2 i1 i2 a b c ⊢
  linear_combination (norm := module) ps1 - ps2 - (m : ℤ) • i1 + (m : ℤ) • i2 + b - a + (n : ℤ) • c

end GlobalTheory.SympQ.PushPow

theorem GlobalTheory.SympQ.wp_pushRep_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n m : ℕ), 0 < n → 0 < m → ∀ p q : N.QT (n * m), N.wp (GlobalTheory.SympQ.pushRep N (n * m) n p) (GlobalTheory.SympQ.pushRep N (n * m) n q) = N.wp p q ^ m := by
  intro R _ _ _ _ D F _ _ _ N ν n m hn hm p q
  exact GlobalTheory.SympQ.PushPow.wp_pushRep N n m hn p q
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

theorem torusHomOf_iff_appTop {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem torusHomOf_unique {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {h : X' → X}
    {t t' : splitTorus S X ⟶ splitTorus S X'} (ht : TorusHomOf h t) (ht' : TorusHomOf h t') : t = t' := by
  refine (splitTorusPointsEquiv S X' _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, (torusHomOf_iff_appTop _ _).1 ht,
    (torusHomOf_iff_appTop _ _).1 ht']

theorem hom_eq_of_over₀_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (g g' : G ⟶ G) (b : D'.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D'.toPre.X), IsMonHom g → IsMonHom g' → Over₀ U'.toUnifPre U.toUnifPre g b → Over₀ U'.toUnifPre U.toUnifPre g' b → OnTorus U'.toUnifPre U.toUnifPre g h → OnTorus U'.toUnifPre U.toUnifPre g' h → g = g' := by
  intro R _ _ _ hR D A G _ _ hG U D' A' U' g g' b h hg hg' q₁ q₂ i₁ i₂
  have : IsNoetherianRing R := hR.1.1
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : IsSeparated G.hom := hG.separated
  refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq (IsLocalRing.maximalIdeal_le_jacobson _) G g g' fun e => ?_
  obtain ⟨t, ht, j₁⟩ := i₁ e
  obtain ⟨t', ht', j₂⟩ := i₂ e
  have htt : t = t' := torusHomOf_unique ht ht'
  have := (U.gt e).i_hom
  exact GlobalTheory.LinearUnifIso.hom_ext_torus (U.gt e) (U'.gt e) GlobalTheory.globalFns_holds _ _
    ((q₁ e).trans (q₂ e).symm) (j₁.trans (htt ▸ j₂.symm))

end GlobalTheory.Mum.Two
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.PullLin

open GlobalTheory.Mum.Two.HomConst

theorem map_fstG {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) (ψ : G ⟶ G) :
    ((Over.pullback (thick R I e)).map ψ).left ≫ (fstG I e G).left = (fstG I e G).left ≫ ψ.left := by
  simp [fstG, pullback.lift_fst]

end GlobalTheory.Mum.Two.PullLin


open GlobalTheory.Mum.Two.PullLin GlobalTheory.Mum.Two.HomConst in
theorem GlobalTheory.Mum.Two.isPullUnif_id_over₀_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (ψ : G ⟶ G) (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (b : D'.toPre.P.A ⟶ D.toPre.P.A), IsMonHom ψ → bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.left → hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = b.left → IsPullUnif (RingHom.id R) hD bc U U' → Over₀ U'.toUnifPre U.toUnifPre ψ b ∧ OnTorus U'.toUnifPre U.toUnifPre ψ hD.xe.symm := by
  intro R _ _ _ hB D A G _ _ hG U D' A' U' hD ψ bc b hψ hbc hb hP
  obtain ⟨hR, -⟩ := hB
  obtain ⟨wL, -, he, -, hlev⟩ := hP.lg

  have lev : ∀ e, ∃ h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left,
      h = ((Over.pullback (thick R (maximalIdeal R) e)).map ψ).left ∧
      (U'.gt e).pG.left ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
        h ≫ (U.gt e).pG.left ∧
      (∀ x : D'.toPre.X, ∃ hψ : ∀ k : Fin 4,
          D'.toPre.Oφ ((U'.gt e).pG) x k ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
            h ≫ D.toPre.Oφ ((U.gt e).pG) (hD.xe x) k,
        LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) ((U'.gt e).t x)
          (GeneratorPullback.pullAlong D.toPre.P.L (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) h _
            Oinvε _ hψ ((U.gt e).t (hD.xe x)))) := by
    intro e
    obtain ⟨h, h1, h2, h3, -⟩ := hlev e
    have : Mono (fstG (maximalIdeal R) e G).left :=
      inferInstanceAs (Mono (pullback.fst G.hom (thick R (maximalIdeal R) e)))
    refine ⟨h, (cancel_mono (fstG (maximalIdeal R) e G).left).1 ?_, h2, h3⟩
    rw [h1, hbc, map_fstG]
  refine ⟨fun e => ?_, ?_⟩
  · obtain ⟨h, rfl, h2, -⟩ := lev e
    have : Mono (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) := inferInstance
    refine Over.OverMorphism.ext ((cancel_mono (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e))).1 ?_)
    rw [hb] at h2
    clear lev hlev hP wL he
    simp only [Over.comp_left, Category.assoc]
    refine Eq.trans ?_ (h2.symm.trans ?_)
    · rfl
    · show (U'.gt e).q.left ≫ pullback.fst D'.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ b.left = _
      congr 1
      exact (pullback.lift_fst _ _ _).symm
  · obtain ⟨-, -, -, hC⟩ := id hR
    obtain ⟨h₀, hT⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R (maximalIdeal R) hR D' D A' A G G U'.toUnifPre
      U.toUnifPre ψ hψ
    have key : (h₀ : D.toPre.X → D'.toPre.X) = hD.xe.symm := by
      haveI := hC
      obtain ⟨t, ht, hi⟩ := hT 0
      refine acts_unique (U'.gt 0) (U.gt 0) (acts_of_torusHomOf _ _ _ ht hi) ?_
      obtain ⟨h, rfl, -, h3⟩ := lev 0
      clear lev hlev hP wL he hT ht hi
      intro Z r z J₁ J₂ hJ₁ hJ₂ c χ
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [AddEquiv.symm_apply_apply]
      obtain ⟨hψk, M⟩ := h3 x
      have P := (maps_iff hD.w _ _ Oinvε _ _ _ _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψk ·) (fun _ => rfl)).1 M
      have e := P Z r z
        (fun k => J₂ ((r ≫ D'.toPre.Oφ (U'.gt 0).pG x k) ≫ hD.e.hom.left ≫
          pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))))
        (fun k => J₁ (r ≫ D'.toPre.Oφ (U'.gt 0).pG x k)) (fun k => hJ₂ _) (fun k => hJ₁ _)
      have h1 := GlobalTheory.ArcLieCompare.prod_Oφ_zero (D := D'.toPre) (U'.gt 0).pG r
        (r ≫ (fstG (maximalIdeal R) 0 G).left ≫ G.hom) (c.trans (by simp only [Category.assoc])) x
        (fun f => gw hD.w f z (J₂ (f ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) (J₁ f))
      rw [h1, _root_.one_mul] at e
      rw [val_of _ _ z J₂
          (fun k => J₂ ((r ≫ D'.toPre.Oφ (U'.gt 0).pG x k) ≫ hD.e.hom.left ≫
            pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))))
          (fun k => by simp only [Category.assoc, hψk k]),
        val_of _ r z J₁ (fun k => J₁ (r ≫ D'.toPre.Oφ (U'.gt 0).pG x k)) (fun k => rfl)]
      exact e
    rw [key] at hT
    exact hT
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntEval

section

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Sp R)} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} [GrpObj G] [IsCommMonObj G]

theorem hRed_pGl {U : UnifPre I D A G} {h : 𝟙_ (Over (Sp R)) ⟶ G} {g : GtPt D.toPre (𝟙_ (Over (Sp R)))}
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g) (e : ℕ) : hRed I h e ≫ pGl U e = thick R I e ≫ g.b.left := by
  have a : hRed I (𝟙 (𝟙_ (Over (Sp R)))) e ≫ (fstG I e (𝟙_ (Over (Sp R)))).left = thick R I e :=
    (hRed_fst _ e).trans (Category.comp_id _)
  have b : hRed I (𝟙 (𝟙_ (Over (Sp R)))) e ≫ ((Over.pullback (thick R I e)).map h).left = hRed I h e := by
    have := GlobalTheory.TorsionTranslate.mono_fst (I := I) e G
    rw [← cancel_mono (fstG I e G).left, hRed_fst, Category.assoc]
    have c : ((Over.pullback (thick R I e)).map h).left ≫ (fstG I e G).left =
        (fstG I e (𝟙_ (Over (Sp R)))).left ≫ h.left := pullback.lift_fst _ _ _
    rw [c, ← Category.assoc, a]
  exact (congrArg (· ≫ pGl U e) b).symm.trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (hg e).1.symm).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g.b.left) a))))

theorem exists_tRel [IsLocalRing R] [IsAdicComplete I R] (hI : I ≠ ⊤) {U : UnifPre I D A G}
    {h : 𝟙_ (Over (Sp R)) ⟶ G} {b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A}
    (hb : ∀ e, hRed I h e ≫ pGl U e = thick R I e ≫ b.left)
    (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (hf : f.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, b.left] (DegPre.lineε 1)),
      t.IsGen ∧ ∀ e : ℕ, TRel U h b f t e := by
  obtain ⟨ν, ν', hν, hν', v⟩ := GlobalTheory.TorsionTranslate.exists_matching U hI (K := Fin 1) (fun _ => 1)
    (fun _ => b.left) (fun _ => h.left) (fun e _ => hRed I h e) (fun e _ => hb e) (fun e _ => hRed_fst h e)
  obtain ⟨ρ, hρ⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ratio U.LG.isLB rfl f ν' hf hν'
  obtain ⟨μ₁, hμ, vμ⟩ := GlobalTheory.TorsionTranslate.exists_scale ν hν ρ
  obtain ⟨t, ht, vt⟩ := exists_gen D.toPre.P.isLB (φ' := ![(η[D.toPre.P.A]).left, b.left]) (ε' := DegPre.lineε 1)
    (fun W _ k => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_two, Fintype.prod_unique, Fintype.prod_unique]
      rfl)
    (LB.mulGen D.toPre.P.L (K := PUnit) _ _ _ _ D.toPre.rig (LB.invGen D.toPre.P.L _ _ μ₁))
    (mulGen_isGen _ _ _ _ _ _ _ D.toPre.rig_gen (invGen_isGen _ _ _ _ hμ))
  refine ⟨t, ht, fun e Z r z J JG hJ hJG => ?_⟩
  have k := v e Z r z J JG hJ hJG
  rw [Fintype.prod_unique, zpow_one] at k
  have w : wv U e (r ≫ hRed I h e) z (J (r ≫ hRed I h e ≫ pGl U e)) (JG (r ≫ hRed I h e ≫ fGl I G e)) =
      GlobalTheory.TorusInvariance.wVal U e z J JG (r ≫ hRed I h e) := by
    rw [← Category.assoc, ← Category.assoc]; rfl
  have k₁ := (vt _ (r ≫ thick R I e) z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg (_ * ·)
    ((val_inv _ _).trans (congrArg (·⁻¹) ((vμ _ _ z J hJ).trans (congrArg (_ * ·) k))))))
  have k₂ := hρ _ (r ≫ thick R I e) z JG hJG
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) k₁ w) k₂).trans ?_
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end

theorem exists_integral_frame : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1)), f.IsGen → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1)), t.IsGen ∧ ∀ e : ℕ, GlobalTheory.Poinc.IntEval.TRel U h g.b f t e := by
  intro V _ _ _ hV D A G _ _ U h g hg f hf
  have := hV.2.2.1
  exact exists_tRel (maximalIdeal.isMaximal V).ne_top (hRed_pGl hg) f hf

end GlobalTheory.Poinc.IntEval
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin.QHypPull

theorem sq_comm {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hs : IsSquare φ φ₂) {X : Scheme.{0}} (u' : X ⟶ (A' ⊗ A').left)
    (u : X ⟶ (A ⊗ A).left)
    (h1 : u' ≫ (fst A' A').left ≫ φ = u ≫ (fst A A).left) (h2 : u' ≫ (snd A' A').left ≫ φ = u ≫ (snd A A).left) :
    u' ≫ φ₂ = u := by
  apply pullback.hom_ext
  · show _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hs.1, h1]
  · show _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hs.2, h2]

end GlobalTheory.ActFin.QHypPull


open GlobalTheory.ActFin.QHypPull in
theorem GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left) (Q : LB (A ⊗ A).left), IsGrpPullback A' A f φ → IsSquare φ φ₂ → QHyp A Q → QHyp A' (Q.pull φ₂) := by
  intro S S' f A _ _ A' _ φ φ₂ Q h hs hQ
  obtain ⟨hA, hL, ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩, hsym, hD⟩ := hQ
  haveI : IsCommMonObj A' := GlobalTheory.isCommMonObj_of_grpPullback S S' A A' f φ h
  have hone : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
    rw [GlobalTheory.FlatModel.LiftW.one_left_comp_of_isGrpPullback h A', GlobalTheory.FlatModel.LiftW.one_left_eq,
      GlobalTheory.FlatModel.LiftW.one_left_eq, ← Category.assoc, h.1.w]
    rfl
  have fl : ∀ {T : Over S'} (a b : T ⟶ A'), (lift a b).left ≫ (fst A' A').left = a.left := fun a b => by
    rw [← Over.comp_left, lift_fst]
  have sl : ∀ {T : Over S'} (a b : T ⟶ A'), (lift a b).left ≫ (snd A' A').left = b.left := fun a b => by
    rw [← Over.comp_left, lift_snd]
  have fl' : ∀ {T : Over S} (a b : T ⟶ A), (lift a b).left ≫ (fst A A).left = a.left := fun a b => by
    rw [← Over.comp_left, lift_fst]
  have sl' : ∀ {T : Over S} (a b : T ⟶ A), (lift a b).left ≫ (snd A A).left = b.left := fun a b => by
    rw [← Over.comp_left, lift_snd]
  have e₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left :=
    sq_comm hs _ _ (by rw [← Category.assoc, fl, hone, Category.assoc, fl'])
      (by rw [← Category.assoc, sl, Category.assoc, sl']; rfl)
  have e₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left :=
    sq_comm hs _ _ (by rw [← Category.assoc, fl, Category.assoc, fl']; rfl)
      (by rw [← Category.assoc, sl, hone, Category.assoc, sl'])
  have e₃ : (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left :=
    sq_comm hs _ _ (by rw [← Category.assoc, fl, Category.assoc, fl', hs.2])
      (by rw [← Category.assoc, sl, Category.assoc, sl', hs.1])
  haveI := hA.proper
  refine ⟨⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
    MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩,
    pull_isLB hL φ₂, ?_, ?_, ?_, ?_⟩
  · exact gen_chartPull (chartPullLinComb Q φ₂ (fun _ : PUnit => (lift (1 : A' ⟶ A') (𝟙 A')).left)
      (fun _ => (lift (1 : A ⟶ A) (𝟙 A)).left) (fun _ => 1) φ (fun _ => e₁)) t₁ ht₁
  · exact gen_chartPull (chartPullLinComb Q φ₂ (fun _ : PUnit => (lift (𝟙 A') (1 : A' ⟶ A')).left)
      (fun _ => (lift (𝟙 A) (1 : A ⟶ A)).left) (fun _ => 1) φ (fun _ => e₂)) t₂ ht₂
  · exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q φ₂ φ₂ rfl) (chartPullLinComb Q φ₂
      (fun _ : PUnit => (lift (snd A' A') (fst A' A')).left) (fun _ => (lift (snd A A) (fst A A)).left)
      (fun _ => 1) φ₂ (fun _ => e₃)) hsym
  · exact GlobalTheory.DiagAmpleBC.relAmple_diag_pull S S' A hA Q hL hD f A' φ φ₂ h.1 hs
end
end
