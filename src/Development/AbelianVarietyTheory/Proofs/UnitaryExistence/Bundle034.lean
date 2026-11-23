module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsUnivRingBc
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle011

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (a : S) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s : LB.Sec (PPx x), ∃! s' : LB.Sec (PPx x'), SecBC φ a x x' s s' := by
  first | exact @GlobalTheory.Frames.SecPull.existsUnique_secBC | exact GlobalTheory.Frames.SecPull.existsUnique_secBC | (intros; apply GlobalTheory.Frames.SecPull.existsUnique_secBC <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem tateIso_ev_eq_iff_add (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ ∃ c, a = b + n • c := by
  rw [tateIso_ev_eq_iff I hn]
  exact exists_congr fun c => sub_eq_iff_eq_add'

theorem tateIso_exists_lift_of_two_data (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D'.La, ∀ a, I.ev n a = I'.ev n (f a) := by
  let R : Submodule (𝓞 E) (D.La × D'.La) :=
    { carrier := {p | I.ev n p.1 = I'.ev n p.2}
      add_mem' := fun {p q} hp hq => by
        change I.ev n (p.1 + q.1) = I'.ev n (p.2 + q.2)
        rw [I.add, I'.add, show I.ev n p.1 = I'.ev n p.2 from hp, show I.ev n q.1 = I'.ev n q.2 from hq]
      zero_mem' := by
        change I.ev n 0 = I'.ev n 0
        rw [(I.ker n hn 0).2 ⟨0, by simp⟩, (I'.ker n hn 0).2 ⟨0, by simp⟩]
      smul_mem' := fun c p hp => by
        change I.ev n (c • p.1) = I'.ev n (c • p.2)
        rw [I.lin, I'.lin, show I.ev n p.1 = I'.ev n p.2 from hp] }
  have hs : Function.Surjective ((LinearMap.fst (𝓞 E) D.La D'.La).comp R.subtype) := fun a => by
    obtain ⟨b, hb⟩ := (I'.onto n hn _).1 (tateIso_ev_pow I hn a)
    exact ⟨⟨(a, b), hb.symm⟩, rfl⟩
  haveI := D.proj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hs
  refine ⟨((LinearMap.snd (𝓞 E) D.La D'.La).comp R.subtype).comp s, fun a => ?_⟩
  have h1 : (s a).1.1 = a := LinearMap.congr_fun hs a
  have h2 : I.ev n (s a).1.1 = I'.ev n (s a).1.2 := (s a).2
  rw [h1] at h2
  exact h2

theorem tateIso_similar_of_two_data
    (he : ∀ n x y c c', e n x y c → e n x y c' → c = c') (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧
      ∀ n : ℕ, 0 < n → ∀ a, I.ev n a = I'.ev n (f n a) := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := tateIso_exists_lift_of_two_data I I' h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | hn
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n hn).pow_eq_one)
      exact ⟨i, fun _ => hi.symm⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, fun n => ν n, ?_, ?_, ?_, ?_, ?_, hf⟩
  · intro n m hn hm a
    rw [← tateIso_ev_eq_iff_add I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun a => ?_, fun a' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨a, ha⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn a')
      rw [hf n hn] at ha
      exact ⟨a, (tateIso_ev_eq_iff_add I' hn _ _).1 ha.symm⟩
  · intro n hn
    have h := I.ζ_prim n hn
    rw [hν n hn] at h
    exact Nat.isCoprime_iff_coprime.2 (((I'.ζ_prim n hn).pow_iff_coprime hn _).1 h)
  · intro n m hn hm
    have h : I'.ζ n ^ ν (n * m) = I'.ζ n ^ ν n := by
      rw [← hν n hn, ← I.ζ_pow n m hn hm, hν (n * m) (Nat.mul_pos hn hm), ← I'.ζ_pow n m hn hm, ← pow_mul,
        ← pow_mul, mul_comm m]
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, zpow_natCast, zpow_natCast, h, mul_inv_cancel]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ e1 e2
    rw [hν n hn, ← zpow_natCast, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]

end

noncomputable def expNegUnit (n : ℕ) : ℂˣ :=
  (Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / n)) (Complex.exp_ne_zero _))⁻¹

theorem expNegUnit_zpow_val (n : ℕ) (j : ℤ) :
    ((expNegUnit n ^ j : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (j : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, expNegUnit, Units.val_inv_eq_inv_val, Units.val_mk0, ← Complex.exp_neg,
    ← Complex.exp_int_mul]
  congr 1
  ring

theorem expNegUnit_isPrimitiveRoot {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (expNegUnit n) n :=
  (IsPrimitiveRoot.coe_units_iff.1 (Complex.isPrimitiveRoot_exp n hn.ne')).inv

theorem expNegUnit_mul_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : expNegUnit (n * m) ^ m = expNegUnit n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  apply Units.ext
  rw [← zpow_natCast, expNegUnit_zpow_val, ← zpow_one (expNegUnit n), expNegUnit_zpow_val]
  congr 1
  push_cast
  field_simp

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) {i : Fin U.n}
  {P : (U.Di i).La →+ (Fin g → ℂ)}

theorem familyUnif_ex_nsmul (hP : IsPeriod (U.Di i) ty P) (n : ℕ) (z : Fin g → ℂ) :
    U.ex i P ((n : ℂ) • z) = U.ex i P z ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero]
    exact (U.ex_ker i P hP 0).2 (zero_mem _)
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, U.ex_add i P hP, ih, pow_succ]

noncomputable def familyUnifTateIso (hP : IsPeriod (U.Di i) ty P) :
    TateIso (U.Di i) ℂ (Over.mk (U.u i P) ⟶ Xo.univ.t.G) (fun a x => x ≫ Xo.univ.t.act.act a)
      (fun n x x' c => Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n x x' (unitOn c)) where
  ζ := expNegUnit
  ζ_prim _ hn := expNegUnit_isPrimitiveRoot hn
  ζ_pow _ _ hn hm := expNegUnit_mul_pow hn hm
  ev n a := U.ex i P ((n : ℂ)⁻¹ • P a)
  add n a b := by rw [map_add (f := _), smul_add, U.ex_add i P hP]
  lin n c a := by
    rw [← U.ex_lin i P hP]
    congr 1
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, hP.1 c a k]
    exact mul_left_comm _ _ _
  ker n hn a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [U.ex_ker i P hP]
    refine exists_congr fun b => ?_
    rw [eq_inv_smul_iff₀ hn', Nat.cast_smul_eq_nsmul, ← map_nsmul, hP.2.1.eq_iff, eq_comm]
  onto n hn x := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := U.ex_onto i P hP x
      rw [← familyUnif_ex_nsmul U hP, U.ex_ker i P hP] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [ha, inv_smul_smul₀ hn']⟩
    · rintro ⟨a, rfl⟩
      rw [← familyUnif_ex_nsmul U hP, smul_inv_smul₀ hn', U.ex_ker i P hP]
      exact ⟨a, rfl⟩
  tower n m hn hm a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [← familyUnif_ex_nsmul U hP, smul_smul]
    congr 2
    push_cast
    field_simp
  isom n hn a b := U.ex_weil i P hP n a b _ hn (expNegUnit_zpow_val n _)

end

theorem familyUnif_lattice_similar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → ∃ (f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧ (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - ν n * D.EF a a') ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e) ∧ ∀ a, ∃ e, f l.A a = U.t i a + l.A • e := by
  intro E _ _ _ H D l Xo σ g ty U i P hP
  obtain ⟨-, I, -, hA, hM⟩ := Xo.univ.geom ℂ (U.u i P) σ (U.over_σ i P hP)
  obtain ⟨f, ν, h1, h2, h3, h4, h5, h6⟩ := tateIso_similar_of_two_data
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I (familyUnifTateIso U hP)
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  refine ⟨f, ν, h1, h2, h3, h4, h5, fun a ha => ?_, fun a => ?_⟩
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) hM0, ← h6 _ hM0, ← hM a ha]
    exact U.ex_eta i P hP a ha
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) l.A_pos, ← h6 _ l.A_pos, ← hA a]
    exact U.ex_etaA i P hP a

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace GlobalTheory.LieExt

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Count

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : Geo.Tor.IsGrpPullback G' G f F) {k : Type} [Field k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)
  {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ (Over.pullback g).obj G} (hx : IsUnivChart _ n x)
  {O : Type} [CommRing O] (act : Geo.Tor.OAct O G') (b : O → (G ⟶ G))
  (hab : ∀ a, (act.act a).left ≫ F = F ≫ (b a).left)
  (act' : O → ((Over.pullback g).obj G ⟶ (Over.pullback g).obj G)) [∀ a, IsMonHom (act' a)]
  (hact' : ∀ a, act' a = (Over.pullback g).map (b a)) (τ : O →+* k)


include hc hg hab hact' in
theorem lieMult_of_finrank {N : ℕ} (hN : Module.finrank k (eigLat hx act' (fun a => τ a)) = N) :
    Geo.Tor.LieMult act tk τ N := by
  let B := Module.finBasisOfFinrankEq k _ hN
  have hT : ∀ (w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') v, Rel (F := F) tk g w v →
      (Geo.Tor.IsLieEigen act tk τ w ↔ IsTan v ∧ ∀ a, v ≫ act' a = spMap (scaleD (τ a)) ≫ v) := by
    intro w v h
    refine and_congr (tan_iff hc hg h) (forall_congr' fun a => ?_)
    rw [hact']
    exact eig_iff hc (act.act a) (b a) (hab a) (τ a) h
  have hmem : ∀ c, c ∈ eigLat hx act' (fun a => τ a) ↔
      ∀ a, tvec (x := x) c ≫ act' a = spMap (scaleD (τ a)) ≫ tvec (x := x) c := by
    intro c
    rw [mem_eigLat_iff]
    exact forall_congr' fun a => (tvec_eig_iff hx (act' a) c (τ a)).symm
  choose vB hv using fun i => rel_exists_w hc hg (tvec (x := x) (B i : Fin n → k))
  let P : (Fin N → k) → (sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G) :=
    fun d => (List.ofFn fun i => spMap (scaleD (d i)) ≫ tvec (x := x) (B i : Fin n → k)).prod
  let Wd : (Fin N → k) → (viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') :=
    fun d => (List.ofFn fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i).prod
  have hPW : ∀ d, Rel (F := F) tk g (Wd d) (P d) := fun d => rel_prod hc hg _ _ fun i => rel_pre _ (hv i)
  have list_prod_tan_aux : ∀ {M : ℕ} (u : Fin M → (sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G))
      (hu : ∀ i, IsTan (u i)), ∃ h : IsTan (List.ofFn u).prod,
        tcoord hx _ h = ∑ i, tcoord hx (u i) (hu i) := by
    intro M
    induction M with
    | zero =>
      intro u hu
      have e0 : (List.ofFn u).prod = 1 := by simp
      refine ⟨e0 ▸ isTan_one, ?_⟩
      rw [tcoord_congr hx e0 _ isTan_one, tcoord_one]
      simp
    | succ M ih =>
      intro u hu
      obtain ⟨h, e⟩ := ih (fun i => u i.succ) (fun i => hu i.succ)
      have e0 : (List.ofFn u).prod = u 0 * (List.ofFn fun i => u i.succ).prod := by
        rw [List.ofFn_succ, List.prod_cons]
      refine ⟨e0 ▸ isTan_mul (hu 0) h, ?_⟩
      rw [tcoord_congr hx e0 _ (isTan_mul (hu 0) h), tcoord_mul hx (hu 0) h, e, Fin.sum_univ_succ]
  have hPeq : ∀ d, P d = tvec (x := x) (∑ i, d i • (B i : Fin n → k)) := by
    intro d
    obtain ⟨h, e⟩ := list_prod_tan_aux (M := N) (fun i => spMap (scaleD (d i)) ≫ tvec (x := x) (B i : Fin n → k))
      (fun i => isTan_scale (d i) (isTan_tvec hx _))
    refine (tcoord_spec hx (P d) h).trans ?_
    show tvec (x := x) (tcoord hx (P d) h) = _
    rw [e]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      (tcoord_scale hx (d i) (isTan_tvec hx _)).trans (by rw [tcoord_tvec])
  refine ⟨vB, fun i => (hT _ _ (hv i)).2 ⟨isTan_tvec hx _, (hmem _).1 (B i).2⟩, fun w hw => ?_⟩
  obtain ⟨v, hwv⟩ := rel_exists_v hc hg (X := sp (R₀ := k) (DualNumber k)) w
  obtain ⟨ht, he⟩ := (hT _ _ hwv).1 hw
  obtain ⟨c, rfl⟩ : ∃ c, tvec (x := x) c = v := ⟨_, (tcoord_spec hx v ht).symm⟩
  let c' : eigLat hx act' (fun a => τ a) := ⟨c, (hmem c).2 he⟩
  have key : ∀ d : Fin N → k, (∃ u : Fin N → (Geo.Tor.epsPt tk ⟶ G'),
      (∀ i, (u i).left = Geo.Tor.spMap (Geo.Tor.epsScale (d i)) ≫ (vB i).left) ∧ w = (List.ofFn u).prod) ↔
      B.equivFun c' = d := fun d => by
    have e₁ : B.equivFun c' = d ↔ c = ∑ i, d i • (B i : Fin n → k) := by
      rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
      simp [c']
    have e₂ : w = Wd d ↔ c = ∑ i, d i • (B i : Fin n → k) := by
      refine (rel_eq_iff hc hwv (hPW d)).trans ?_
      rw [hPeq]
      exact ⟨fun h => tvec_inj hx h, fun h => by rw [← h]⟩
    rw [e₁, ← e₂]
    constructor
    · rintro ⟨u, hu, hwu⟩
      have hu' : u = fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i :=
        funext fun i => Over.OverMorphism.ext (hu i)
      rw [hwu, hu']
    · intro h
      exact ⟨fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i, fun i => rfl, h⟩
  exact (existsUnique_congr key).2 existsUnique_eq'

end Count

theorem lieMult_iff_finrank {k K : Type} [Field k] [Field K] [Algebra k K] (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] {n : ℕ} {xc : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n xc)
    {O : Type} [CommRing O] (act : Geo.Tor.OAct O G) [∀ a, IsMonHom (act.act a)] (χ : O →+* k) (N : ℕ) :
    Geo.Tor.LieMult act (fB k K) ((algebraMap k K).comp χ) N ↔
      Module.finrank k (eigLat hx act.act χ) = N := by
  obtain ⟨x', hx', hcomp⟩ := tanBC_alg (R := k) (R' := K) G n xc hx
  have hpt : ∀ c : Fin n → k, pushR G (tvec (x := x') (algebraMap k K ∘ c)) =
      spMap (dualMapA k K) ≫ tvec (x := xc) c := fun c =>
    Over.OverMorphism.ext (by rw [pushR_left, hcomp c]; rfl)
  have hLk : ∀ a (c : Fin n → k), tmap hx' ((Over.pullback (fB k K)).map (act.act a)) (algebraMap k K ∘ c) =
      algebraMap k K ∘ tmap hx (act.act a) c := by
    intro a c
    apply tvec_inj hx'
    apply pushR_inj G
    rw [tvec_tmap hx', pushR_map, hpt, hpt, tvec_tmap hx, Category.assoc]
  have e0 : Module.finrank k (eigLat hx act.act χ) =
      Module.finrank K (eigLat hx' (fun a => (Over.pullback (fB k K)).map (act.act a))
        (fun a => (algebraMap k K).comp χ a)) :=
    finrank_eig_bc (fun a => tmap hx (act.act a))
      (fun a => tmap hx' ((Over.pullback (fB k K)).map (act.act a))) hLk χ
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  rw [e0]
  exact ⟨finrank_of_lieMult (Geo.Tor.isGrpPullback_of_iso (Iso.refl G)) (Category.comp_id _) hx' act act.act
      (fun a => by simp) _ (fun a => rfl) _,
    lieMult_of_finrank (Geo.Tor.isGrpPullback_of_iso (Iso.refl G)) (Category.comp_id _) hx' act act.act
      (fun a => by simp) _ (fun a => rfl) _⟩

theorem lieMult_extend_iff {k K : Type} [Field k] [Field K] (φ : k →+* K) (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] [Smooth G.hom] {O : Type} [CommRing O] (act : Geo.Tor.OAct O G) (χ : O →+* k) (N : ℕ) :
    Geo.Tor.LieMult act (Geo.Tor.spMap φ) (φ.comp χ) N ↔ Geo.Tor.LieMult act (𝟙 _) χ N := by
  let _ := φ.toAlgebra
  have := act.hom
  obtain ⟨n, x, hx⟩ := univChartLoc G
  have h := lieMult_iff_finrank (K := k) G hx act χ N
  have e : fB k k = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rw [e, Algebra.algebraMap_self, RingHom.id_comp] at h
  exact (lieMult_iff_finrank (K := K) G hx act χ N).trans h.symm

theorem exists_comp_eq {k K O : Type} [Field k] [IsAlgClosed k] [Field K] [CommRing O] [Algebra.IsIntegral ℤ O]
    (φ : k →+* K) (τ : O →+* K) : ∃ χ : O →+* k, φ.comp χ = τ := by
  let _ := φ.toAlgebra
  have h : ∀ a, ∃ z : k, φ z = τ a := fun a => by
    have hi : IsIntegral k (τ a) := ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map τ.toIntAlgHom).tower_top
    exact minpoly.mem_range_of_degree_eq_one k _
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi))
  choose f hf using h
  have inj := φ.injective
  exact ⟨⟨⟨⟨f, inj (by simp [hf])⟩, fun a b => inj (by simp [hf])⟩, inj (by simp [hf]),
    fun a b => inj (by simp [hf])⟩, RingHom.ext hf⟩

theorem detCond_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (D : Geo.Tor.Datum H)
    {k K : Type} [Field k] [IsAlgClosed k] [Field K] (φ : k →+* K) (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] [Smooth G.hom] (act : Geo.Tor.OAct (𝓞 E) G) {ρ : k} (h : Geo.Tor.DetCond D act (𝟙 _) ρ) :
    Geo.Tor.DetCond D act (Geo.Tor.spMap φ) (φ ρ) := by
  intro τ
  obtain ⟨χ, rfl⟩ := exists_comp_eq φ τ
  rw [lieMult_extend_iff, lieMult_extend_iff]
  exact ⟨fun e => (h χ).1 (φ.injective e), fun e => (h χ).2 fun e' => e (congrArg φ e')⟩

end GlobalTheory.LieExt
end
end
