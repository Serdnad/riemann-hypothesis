module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle019
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat.GradedTate

theorem exists_tateIso_of_perp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H)
    (Z : Submodule (𝓞 E) Dw.La) (f : perp Dw Z →ₗ[𝓞 E] D'.La) (hf : IsLower Dw D' Z f) (K : Type) [Field K]
    (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (ζ : ℕ → Kˣ)
    (hζ : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hζ' : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)
    (b : ℕ → perp Dw Z → Q) (hact : ∀ c, act c 1 = 1)
    (hcard : ∀ n, 0 < n → Nat.card {y : Q // y ^ n = 1} = n ^ Module.finrank ℤ D'.La)
    (huniq : ∀ n x y c c', e n x y c → e n x y c' → c = c')
    (hone : ∀ n y c, e n 1 y c → c = 1)
    (hadd : ∀ n, 0 < n → ∀ a a', b n (a + a') = b n a * b n a')
    (hlin : ∀ n, 0 < n → ∀ (c : 𝓞 E) a, b n (c • a) = act c (b n a))
    (hpow : ∀ n, 0 < n → ∀ a, b n a ^ n = 1)
    (htow : ∀ n m, 0 < n → 0 < m → ∀ a, b (n * m) a ^ m = b n a)
    (hiso : ∀ n, 0 < n → ∀ a a', e n (b n a) (b n a') (ζ n ^ Dw.EF a a')) :
    ∃ I' : TateIso D' K Q act e, (∀ n, I'.ζ n = ζ n) ∧ ∀ n, 0 < n → ∀ a, b n a = I'.ev n (f a) := by
  have := D'.proj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf.1
  have hs' : ∀ w, f (s w) = w := fun w => LinearMap.congr_fun hs w
  have hiso' : ∀ n, 0 < n → ∀ a w', e n (b n a) (b n (s w')) (ζ n ^ D'.EF (f a) w') := fun n hn a w' => by
    have h := hiso n hn a (s w')
    rwa [← hf.2.2, hs'] at h
  have hiso'' : ∀ n, 0 < n → ∀ w w', e n (b n (s w)) (b n (s w')) (ζ n ^ D'.EF w w') := fun n hn w w' => by
    have h := hiso' n hn (s w) w'
    rwa [hs'] at h
  have hadd' : ∀ n, 0 < n → ∀ w w', b n (s (w + w')) = b n (s w) * b n (s w') := fun n hn w w' => by
    rw [map_add (f := _), hadd n hn]
  have hko := fun n (hn : 0 < n) => TorsIsometry.ker_and_onto E H D' K Q (e n) n (ζ n) (fun w => b n (s w)) hn
    (hcard n hn) (fun y c _ => hone n y c) (hζ n hn) (hadd' n hn) (fun w => hpow n hn _) (hiso'' n hn)
  refine ⟨{ ζ := ζ, ζ_prim := hζ, ζ_pow := hζ', ev := fun n w => if 0 < n then b n (s w) else 1
            add := fun n w w' => ?_, lin := fun n c w => ?_, ker := fun n hn => ?_, onto := fun n hn => ?_
            tower := fun n m hn hm w => ?_, isom := fun n hn w w' => ?_ }, fun _ => rfl, fun n hn a => ?_⟩
  · split_ifs with hn
    · exact hadd' n hn w w'
    · exact (_root_.mul_one _).symm
  · split_ifs with hn
    · rw [map_smul, hlin n hn]
    · exact (hact c).symm
  · simp only [if_pos hn]
    exact (hko n hn).1
  · simp only [if_pos hn]
    exact (hko n hn).2
  · simp only [if_pos hn, if_pos (Nat.mul_pos hn hm)]
    exact htow n m hn hm _
  · simp only [if_pos hn]
    exact hiso'' n hn w w'
  · show _ = if 0 < n then b n (s (f a)) else 1
    rw [if_pos hn]
    obtain ⟨w, hw⟩ := ((hko n hn).2 _).1 (hpow n hn a)
    obtain ⟨c, hc⟩ := TorsIsometry.exists_eq_nsmul_of_dvd D'.EF D'.unimod n (f a - w) fun w' => by
      have h₁ := hiso' n hn a w'
      rw [← hw] at h₁
      have h₂ := huniq _ _ _ _ _ h₁ (hiso'' n hn w w')
      rw [map_sub, LinearMap.sub_apply, ← (hζ n hn).zpow_eq_one_iff_dvd, zpow_sub, h₂, mul_inv_cancel]
    have h₃ : b n (s (f a - w)) = 1 := ((hko n hn).1 _).2 ⟨c, hc⟩
    have h₄ := hadd' n hn (f a - w) w
    rw [sub_add_cancel, h₃, _root_.one_mul] at h₄
    exact hw.symm.trans h₄.symm

section Pairs

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

attribute [local instance] TorusExt.gtGroup

theorem eq_of_equiv (hB : D.TauBimult) {k : ℕ} (hk : 0 < k) {p q : QkPt D F k} (h : QkPt.Equiv D F p q)
    (hy : p.y = q.y) : p = q := by
  obtain ⟨z, h₁, h₂⟩ := (TorusExt.equiv_iff hB _ _).1 h
  have hz : k • z = 0 := by
    rw [hy] at h₁
    exact left_eq_add.1 h₁
  have : z = 0 := by
    rw [← natCast_zsmul] at hz
    exact (smul_eq_zero.1 hz).resolve_left (Int.natCast_ne_zero.2 hk.ne')
  subst this
  rw [map_zero, add_zero] at h₂
  exact TorusExt.qk_ext hy h₂.symm

theorem b_pow (hB : D.TauBimult) {k : ℕ} (p : QkPt D F k) (hy : p.y = 0) : p.g.b ^ k = 1 := by
  rw [← TorusExt.nsmul_b, TorusExt.qk_nsmul hB, hy, map_zero, TorusExt.zero_b]

theorem b_tower (hB : D.TauBimult) {n m : ℕ} (hn : 0 < n) {p p₀ : QkPt D F (n * m)} {q r r₀ : QkPt D F n}
    (hp : QkPt.Equiv D F p p₀) (hp₀ : p₀.y = 0) (hq : q.y = p.y) (hg : GtPtF.IsNsmul m p.g q.g)
    (hr : QkPt.Equiv D F q r) (hr' : QkPt.Equiv D F r r₀) (hr₀ : r₀.y = 0) : p₀.g.b ^ m = r₀.g.b := by
  obtain ⟨z, h₁, h₂⟩ := (TorusExt.equiv_iff hB _ _).1 hp
  have h₃ : TorusExt.qkShift hB q (m • z) = r₀ := by
    refine eq_of_equiv hB hn (TorusExt.equiv_trans hB (TorusExt.equiv_symm hB (TorusExt.equiv_qkShift hB q _))
      (TorusExt.equiv_trans hB hr hr')) ?_
    show q.y + n • m • z = r₀.y
    rw [hr₀, hq, smul_smul, ← h₁, hp₀]
  rw [← h₃, ← TorusExt.nsmul_b, h₂, nsmul_add, ← (TorusExt.isNsmul_iff_eq _ _ _).1 hg, ← map_nsmul]
  rfl

end Pairs


attribute [local instance] TorusExt.gtGroup in
theorem exists_gradedTateIso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H) (Z : Submodule (𝓞 E) Dw.La)
  (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f →
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
  Module.finrank ℤ D'.La = 2 * P.D.toPre.P.g →
  ∀ I : (letI := H.starRing; TateIsoQ Dw P.D.toPre P.oD F),
  (∀ n, 0 < n → ∀ a : GlobalTheory.LowDat.perp Dw Z, ∃ q : QkPt P.D.toPre F n, QkPt.Equiv P.D.toPre F (I.ev n a) q ∧ q.y = 0) →
  ∃ I' : TateIso D' F (TF (R := R) F ⟶ P.D.toPre.P.A) (fun a g => g ≫ (letI := H.starRing; P.oD.onB.act a))
      (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)),
    (∀ n, I'.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ (a : GlobalTheory.LowDat.perp Dw Z) (q : QkPt P.D.toPre F n),
      QkPt.Equiv P.D.toPre F (I.ev n a) q → q.y = 0 → q.g.b = I'.ev n (f a) := by
  intro E _ _ _ H Dw D' Z f hf R _ _ _ hR t P F _ _ _ hrk I hI
  letI := H.starRing
  have hB := P.D.tau_bimult
  have hL := GlobalTheory.firstFiveLaws
  have hG := hL.1.globalFns
  have := hR.2
  have := hR.1.1
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  choose q hq hy using hI
  have huniq : ∀ (n : ℕ) (x y : TF (R := R) F ⟶ P.D.toPre.P.A) (c c' : Fˣ),
      Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n x y (unitOn c) →
      Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n x y (unitOn c') → c = c' := fun n x y c c' =>
    weilIs_unique_fieldPoint _ _ _ P.D.toPre.P.isLB F _ n x y c c'
  obtain ⟨I', h₁, h₂⟩ := exists_tateIso_of_perp Dw D' Z f hf F (TF (R := R) F ⟶ P.D.toPre.P.A)
    (fun a g => g ≫ P.oD.onB.act a)
    (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)) I.ζ I.ζ_prim I.ζ_pow
    (fun n a => if hn : 0 < n then (q n hn a).g.b else 1)
    (fun c => by
      have := P.oD.onB.hom c
      exact MonObj.one_comp _)
    (fun n hn => by
      have : NeZero n := ⟨hn.ne'⟩
      rw [hrk]
      exact (hL.1.mulN _ P.D.toPre.P n hn).2.2.2.2 F _
        (IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim n hn)).neZero'.ne)
    huniq
    (fun n y c h => by
      have h₁ := (hL.1.weil _ P.D.toPre.P n _).2.1 _ _ _ _ _ h h
      rw [_root_.mul_one] at h₁
      have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
      exact mul_eq_left.1 (huniq n 1 y _ _ (e ▸ h₁) h))
    (fun n hn a a' => by
      simp only [dif_pos hn]
      have h := (TorusExt.qkAdd_iff hB _ _ _).1
        ((TorusExt.qkAdd_iff_of_equiv hB (hq n hn a) (hq n hn a') (I.add n hn a a')).2 (hq n hn (a + a')))
      rw [← eq_of_equiv hB hn h (by
        show (q n hn a).y + (q n hn a').y = _
        rw [hy, hy, hy, add_zero])]
      exact TorusExt.add_b _ _)
    (fun n hn c a => by
      simp only [dif_pos hn]
      have h := (TorusExt.qkAct_iff hB hG P.oD _ _ _).1
        ((TorusExt.qkAct_iff_of_equiv hB hG P.oD (hq n hn a) (I.lin n hn c a)).2 (hq n hn (c • a)))
      rw [← eq_of_equiv hB hn h (by
        show c • (q n hn a).y = _
        rw [hy, hy, smul_zero])]
      exact TorusExt.gtSmul_b hG P.oD _ _)
    (fun n hn a => by
      simp only [dif_pos hn]
      exact b_pow hB _ (hy n hn a))
    (fun n m hn hm a => by
      simp only [dif_pos hn, dif_pos (Nat.mul_pos hn hm)]
      obtain ⟨r, r₁, r₂, r₃⟩ := I.tower n m hn hm a
      exact b_tower hB hn (hq _ _ a) (hy _ _ a) r₁ r₂ r₃ (hq n hn a) (hy n hn a))
    (fun n hn a a' => by
      simp only [dif_pos hn]
      exact (UT.WeilAbelianPart.weilQkIs_iff_weilIs_abelianPart hL R _ hR.1 P.D F n hn _ _ (hy n hn a) (hy n hn a')
        _).1 (PhiOperatorCompare.weilQkIs_of_equiv hB (hq n hn a) (hq n hn a') (I.isom n hn a a')))
  refine ⟨I', h₁, fun n hn a r hr hr₀ => ?_⟩
  rw [← h₂ n hn a, dif_pos hn, eq_of_equiv hB hn
    (TorusExt.equiv_trans hB (TorusExt.equiv_symm hB hr) (hq n hn a)) (hr₀.trans (hy n hn a).symm)]

end GlobalTheory.LowDat.GradedTate
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensPair

theorem lamPts_comp {S : Scheme.{0}} {B T T' : Over S} [GrpObj B] (f : T' ⟶ T) (x y : T ⟶ B) (l : Fin 4) :
    f.left ≫ GlobalTheory.PolDeg.lamPts x y l = GlobalTheory.PolDeg.lamPts (f ≫ x) (f ≫ y) l := by
  fin_cases l <;> simp [GlobalTheory.PolDeg.lamPts, ← Over.comp_left, MonObj.comp_mul]

theorem lamPts_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) (l : Fin 4) :
    (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A).left ≫
      GlobalTheory.PolDeg.lamPts (fst D'.P.A D'.P.A ≫ T.pr i) (snd D'.P.A D'.P.A ≫ T.pr j) l =
    GlobalTheory.PolDeg.lamPts (if i = i₀ then fst D.P.A D.P.A else 1) (snd D.P.A D.P.A ^ m j i₀) l := by
  have h1 : (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A) ≫
      fst D'.P.A D'.P.A ≫ T.pr i = if i = i₀ then fst D.P.A D.P.A else 1 := by
    rw [lift_fst_assoc, Category.assoc, T.inc_pr']
    split_ifs <;> simp
  have h2 : (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A) ≫
      snd D'.P.A D'.P.A ≫ T.pr j = snd D.P.A D.P.A ^ m j i₀ := by
    rw [lift_snd_assoc, Category.assoc, Category.assoc, T.act_pr]
    have e : ∀ k, (snd D.P.A D.P.A ≫ T.inc i₀) ≫ T.pr k = if k = i₀ then snd D.P.A D.P.A else 1 := fun k => by
      rw [Category.assoc, T.inc_pr']; split_ifs <;> simp
    rw [← Category.assoc]
    change preHom (snd D.P.A D.P.A ≫ T.inc i₀) (∏ k, T.pr k ^ m j k) = _
    rw [map_prod]
    simp only [map_zpow]
    change ∏ k, ((snd D.P.A D.P.A ≫ T.inc i₀) ≫ T.pr k) ^ m j k = _
    simp only [e]
    rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
  rw [lamPts_comp, h1, h2]

theorem xe_xi {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ i : Fin r) (a : D.X) : T.xe (T.xi i₀ a) i = if i = i₀ then a else 0 := by
  simp [Tens.xi, Pi.single_apply]

theorem c_zsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (n : ℤ) (b : D.X) : D.c (n • b) = D.c b ^ n := by
  let φ : D.X →+ Additive (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (D.c x)) (fun a b => by
      show Additive.ofMul (D.c (a + b)) = Additive.ofMul (D.c a * D.c b)
      rw [D.c_add]; rfl)
  exact congrArg Additive.toMul (map_zsmul φ n b)

theorem pt_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (a b : D.X) (a' b' : D'.X)
    (ha : ∀ i, T.xe a' i = if i = i₀ then a else 0) (hb : ∀ j, T.xe b' j = m j i₀ • b) :
    (lift (toUnit (TK R) ≫ D'.c a') (toUnit (TK R) ≫ D'.c b') : TK R ⟶ G2 D'.P.A) =
      lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) ≫
        lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) := by
  have c0 : D.c 0 = 1 := by
    have := c_zsmul D 0 a; rwa [zero_smul, zpow_zero] at this
  rw [comp_lift, lift_fst_assoc, lift_snd_assoc]
  congr 1
  · refine T.lim.hom_ext fun ⟨i⟩ => ?_
    simp only [Fan.mk_π_app, Category.assoc]
    rw [T.c_pr, ha, T.inc_pr']
    split_ifs <;> simp [c0]
  · refine T.lim.hom_ext fun ⟨i⟩ => ?_
    simp only [Fan.mk_π_app, Category.assoc]
    rw [T.c_pr, hb, c_zsmul, T.act_pr]
    have e : ∀ k, (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ T.pr k = if k = i₀ then toUnit (TK R) ≫ D.c b else 1 := fun k => by
      rw [Category.assoc, Category.assoc, T.inc_pr']; split_ifs <;> simp
    calc toUnit (TK R) ≫ D.c b ^ m i i₀ = (toUnit (TK R) ≫ D.c b) ^ m i i₀ := map_zpow (preHom (toUnit (TK R))) _ _
      _ = ∏ k, ((toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ T.pr k) ^ m i k := by
        simp only [e]
        rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
      _ = (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ ∏ k, T.pr k ^ m i k := by
        change _ = preHom (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) (∏ k, T.pr k ^ m i k)
        rw [map_prod]
        simp only [map_zpow]
        rfl
      _ = _ := by simp only [Category.assoc]

end GlobalTheory.TensPair
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TensAct

section General

variable {S : Scheme.{0}} {X Y Z G : Over S}

def preHom [GrpObj G] [IsCommMonObj G] (f : X ⟶ Y) : (Y ⟶ G) →* (X ⟶ G) where
  toFun g := f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' := fun g h => MonObj.comp_mul f g h

theorem comp_prod_zpow [GrpObj G] [IsCommMonObj G] (f : X ⟶ Y) {K : Type} [Fintype K] (g : K → (Y ⟶ G)) (n : K → ℤ) :
    f ≫ (∏ j, g j ^ n j) = ∏ j, (f ≫ g j) ^ n j := by
  show preHom f (∏ j, g j ^ n j) = ∏ j, (preHom f (g j)) ^ n j
  rw [map_prod]
  simp only [map_zpow]

end General

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem hom_ext (T : Tens D D' W) {X} {f g : X ⟶ D'.P.A} (h : ∀ i, f ≫ T.pr i = g ≫ T.pr i) : f = g :=
  T.lim.hom_ext fun ⟨i⟩ => h i

theorem comp_act_pr (T : Tens D D' W) {X} (f : X ⟶ D'.P.A) (a : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    f ≫ T.act a ≫ T.pr i = ∏ j, (f ≫ T.pr j) ^ a i j := by
  rw [Tens.act_pr, comp_prod_zpow]

theorem act_isMonHom (T : Tens D D' W) (a : Matrix (Fin r) (Fin r) ℤ) : IsMonHom (T.act a) := by
  haveI := T.pr_hom
  have h1 : ∀ {X} , (1 : X ⟶ D'.P.A) ≫ T.act a = 1 := by
    intro X
    refine hom_ext T fun i => ?_
    rw [Category.assoc, comp_act_pr]
    simp [MonObj.one_comp]
  have h2 : ∀ {X} (f g : X ⟶ D'.P.A), (f * g) ≫ T.act a = (f ≫ T.act a) * (g ≫ T.act a) := by
    intro X f g
    refine hom_ext T fun i => ?_
    rw [Category.assoc, comp_act_pr, MonObj.mul_comp, Category.assoc, Category.assoc, comp_act_pr, comp_act_pr,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [MonObj.mul_comp, mul_zpow]
  constructor
  · have := h1 (X := 𝟙_ _)
    simpa [Hom.one_def] using this
  · have := h2 (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this]
    congr 1

theorem act_one (T : Tens D D' W) : T.act 1 = 𝟙 _ := by
  refine hom_ext T fun i => ?_
  rw [Tens.act_pr, Category.id_comp, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    rw [Matrix.one_apply_ne hj.symm, zpow_zero]
  · simp

theorem act_mul (T : Tens D D' W) (a b : Matrix (Fin r) (Fin r) ℤ) : T.act (a * b) = T.act b ≫ T.act a := by
  refine hom_ext T fun i => ?_
  rw [Category.assoc, comp_act_pr, Tens.act_pr]
  simp only [Tens.act_pr, ← Finset.prod_zpow, ← zpow_mul, Matrix.mul_apply]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  have : ∀ (s : Finset (Fin r)) (n : Fin r → ℤ), T.pr k ^ (∑ j ∈ s, n j) = ∏ j ∈ s, T.pr k ^ n j := by
    intro s n
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]
  rw [this]
  simp only [mul_comm]

theorem act_add (T : Tens D D' W) (a b : Matrix (Fin r) (Fin r) ℤ) :
    T.act (a + b) = padd D'.P.A (T.act a) (T.act b) := by
  haveI := T.pr_hom
  show _ = T.act a * T.act b
  refine hom_ext T fun i => ?_
  rw [MonObj.mul_comp]
  simp only [Tens.act_pr, Matrix.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem act_ring : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), (∀ a, IsMonHom (T.act a)) ∧ T.act 1 = 𝟙 _ ∧ (∀ a b, T.act (a * b) = T.act b ≫ T.act a) ∧
      ∀ a b, T.act (a + b) = padd D'.P.A (T.act a) (T.act b) :=
  fun _ _ _ _ _ _ _ T => ⟨act_isMonHom T, act_one T, act_mul T, act_add T⟩

end GlobalTheory.Mum.TensAct
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

def precompHom {C : Type*} [Category C] [CartesianMonoidalCategory C] {M X Y : C} [MonObj M] (f : X ⟶ Y) :
    (Y ⟶ M) →* (X ⟶ M) where
  toFun g := f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' g₁ g₂ := MonObj.comp_mul f g₁ g₂

def degCHom {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) :
    D.X →+ Additive (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) where
  toFun x := Additive.ofMul (D.c x)
  map_zero' := by
    have h : D.c (0 + 0) = D.c 0 * D.c 0 := D.c_add 0 0
    rw [add_zero] at h
    have h1 : D.c 0 = 1 := by simpa using h.symm
    rw [h1]; rfl
  map_add' x y := by rw [D.c_add]; rfl

theorem degC_sum_zsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (n : Fin r → ℤ) (x : Fin r → D.X) :
    D.c (∑ j, n j • x j) = ∏ j, D.c (x j) ^ n j := by
  have h := congrArg Additive.toMul (map_sum (degCHom D) (fun j => n j • x j) Finset.univ)
  rw [toMul_sum] at h
  refine h.trans ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zsmul, toMul_zsmul]
  rfl

theorem Tens.c_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (s : SymUnit r), letI := T.mod s; ∀ (a : TensO s) (y : D'.X),
    D'.c (a • y) = D'.c y ≫ T.act (TensO.mat s a) := by
  intro R _ _ D D' r W T s
  letI := T.mod s
  intro a y
  refine Fan.IsLimit.hom_ext T.lim _ _ fun i => ?_
  show D'.c (a • y) ≫ T.pr i = (D'.c y ≫ T.act (TensO.mat s a)) ≫ T.pr i
  rw [T.c_pr, Category.assoc, T.act_pr, Tens.xe_smul, degC_sum_zsmul D]
  have h := map_prod (precompHom (M := D.P.A) (D'.c y)) (fun j => T.pr j ^ TensO.mat s a i j) Finset.univ
  refine Eq.trans ?_ h.symm
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zpow]
  show _ = (D'.c y ≫ T.pr j) ^ _
  rw [T.c_pr]

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_unique : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (v' u' : N'.Gt) (vs : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' vs → v' = u' := by
  intro F _ N N' r W φ e wv hT v' u' vs hv hu
  obtain ⟨-, hφ, -, -, -, hw, -⟩ := hT
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hu1, hu2⟩ := hu
  have hb : v'.b = u'.b := hφ.1 (funext fun j => (hv1 j).trans (hu1 j).symm)
  refine NumD.Gt.ext hb (funext fun χ' => ?_)
  have h1 := hv2 χ'
  have h2 := hu2 χ'
  rw [← hb] at h2
  have hne : wv (N'.c χ') * wv v'.b ≠ 0 := mul_ne_zero (hw _) (hw _)
  apply Units.ext
  apply mul_right_cancel₀ hne
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, h1, h2]

end GlobalTheory.Mum.TensTor
end
