module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFiniteOrder

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem val_scaleGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J := by
  unfold val
  show gm r z _ (res le_top c * t.s _) = gm r z ⊤ c * gm r z _ (t.s _)
  refine (MonoidHom.map_mul (gm r z _) _ _).trans ?_
  congr 1
  exact gm_res r z le_top (hJ.mem φ r) c

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

def zUnit (ζ : F) (hζ : ζ ≠ 0) : Γ((TF (R := V) F).left, ⊤)ˣ :=
  ((Ne.isUnit hζ).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit

theorem phiRel_scale (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k) (hΦr : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s)
    (ζ : F) (hζ : ζ ≠ 0) (s t : Fam D.toPre F k) :
    PhiRel D.toPre F k p (scaleGen (zUnit (V := V) ζ hζ) w) s t ↔ t = ζ • Φ s := by
  have hw' := scaleGen_isGen (zUnit (V := V) ζ hζ) w hw
  have key : ∀ s : Fam D.toPre F k, PhiVal p (scaleGen (zUnit (V := V) ζ hζ) w) s.s (ζ • Φ s).s := by
    intro s a' β hβ T ρ z' J hJ
    have h1 := (phiRel_iff hG p w hw s (Φ s)).1 ((hΦr s (Φ s)).2 rfl) a' β hβ T ρ z' J hJ
    have hu : gs (ρ.left ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z' ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) =
        (gm (ρ ≫ fst (TF (R := V) F) D.toPre.P.A).left z' ⊤ (zUnit (V := V) ζ hζ)).val :=
      gs_unit _ z' ⊤ trivial (zUnit (V := V) ζ hζ)
    rw [sval_smul ζ (Φ s) β ρ.left z' hJ, h1, val_mul hJ, val_mul hJ, val_scaleGen hJ, hu]
    simp only [Units.val_mul]
    ring
  constructor
  · intro h
    exact phi_unique p _ ((phiRel_iff hG p _ hw' s t).1 h) (key s)
  · rintro rfl
    exact (phiRel_iff hG p _ hw' s _).2 (key s)

theorem finOrd_of_pow {k : ℕ} (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)))
    (Ψ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k) (hΨ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Ψ s)
    (hpow : ∀ s, (Ψ ^ k) s = s) : FinOrd D F k p w 1 := by
  have hext : ∀ a b : Fam D.toPre F k, (∀ α j, (a.s α).f j = (b.s α).f j) → a = b := by
    rintro ⟨sa, fa⟩ ⟨sb, fb⟩ h
    have hs : sa = sb := by
      funext α
      have h1 : (sa α).f = (sb α).f := funext (h α)
      rcases hx : sa α with ⟨xf, xc⟩
      rcases hy : sb α with ⟨yf, yc⟩
      rw [hx, hy] at h1
      simp only at h1
      subst h1
      rfl
    subst hs
    rfl
  have hone : ∀ W, DegPre.constBF D.toPre F (1 : F) W = 1 := by
    intro W
    simp [DegPre.constBF]
  refine ⟨k, hk, fun ss ts h α j => ?_⟩
  have hstep : ∀ i : Fin k, ss i.succ = Ψ (ss i.castSucc) := by
    intro i
    obtain ⟨h1, h2⟩ := h i
    rw [← (hΨ _ _).mp h1]
    apply hext
    intro α j
    rw [h2 α j, hone, _root_.one_mul]
  have hall : ∀ n (hn : n ≤ k), ss ⟨n, by omega⟩ = (Ψ ^ n) (ss 0) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [pow_zero, Module.End.one_apply]
      rfl
    | succ n ih =>
      intro hn
      have h3 := hstep ⟨n, by omega⟩
      rw [pow_succ', Module.End.mul_apply, ← ih (by omega)]
      exact h3
  have hlast : ss (Fin.last k) = ss 0 := by
    rw [show Fin.last k = ⟨k, by omega⟩ from rfl, hall k le_rfl]
    exact hpow (ss 0)
  rw [hlast]

end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFiniteOrder
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Act

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S}

theorem comp_mulMon (f : A ⟶ A) [IsMonHom f] (x y : T ⟶ A) : (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem one_compMon (f : A ⟶ A) [IsMonHom f] : (1 : T ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem comp_padd (x : T ⟶ A) (f g : A ⟶ A) : x ≫ padd A f g = (x ≫ f) * (x ≫ g) := by
  simp only [padd]
  rw [← Category.assoc, comp_lift, Hom.mul_def]

variable {O : Type} [Ring O] (ρ : RingAct A O)

theorem act_add_apply (x : T ⟶ A) (a b : O) : x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b) := by
  rw [ρ.map_add, comp_padd]

theorem act_mul_apply (x : T ⟶ A) (a b : O) : x ≫ ρ.act (a * b) = (x ≫ ρ.act b) ≫ ρ.act a := by
  rw [ρ.map_mul, Category.assoc]

theorem act_one_apply (x : T ⟶ A) : x ≫ ρ.act 1 = x := by
  rw [ρ.map_one, Category.comp_id]

theorem act_zero_apply (x : T ⟶ A) : x ≫ ρ.act 0 = 1 := by
  have h := act_add_apply ρ x 0 0
  rw [add_zero] at h
  exact (_root_.mul_left_cancel (a := x ≫ ρ.act 0) (by rw [_root_.mul_one]; exact h)).symm

theorem act_nat_apply (x : T ⟶ A) (n : ℕ) : x ≫ ρ.act (n : O) = x ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero_apply, _root_.pow_zero]
  | succ n ih => rw [Nat.cast_succ, act_add_apply, ih, act_one_apply, _root_.pow_succ]

theorem pow_eq_one_of_kill {a b : O} {N : ℕ} (hab : a * b = (N : O)) (x : T ⟶ A) (hx : x ≫ ρ.act b = 1) :
    x ^ N = 1 := by
  rw [← act_nat_apply ρ x N, ← hab, act_mul_apply, hx]
  haveI := ρ.hom a
  exact one_compMon (ρ.act a)

end Act

theorem unitOn_injective {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := by
  intro u v h
  apply Units.ext
  have h1 := congrArg (fun w : (Γ(Sp K, ⊤))ˣ =>
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w : Γ(Sp K, ⊤))) h
  simpa [unitOn] using h1

section Sep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem mem_nsmul_of_dvd (Dw : Datum H) (N : ℕ) (d : Dw.La)
    (h : ∀ b, (N : ℤ) ∣ Dw.EF b d) : ∃ f : Dw.La, d = N • f := by
  have skew : ∀ x y, Dw.EF x y = - Dw.EF y x := by
    intro x y
    have hxy := Dw.alt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt] at hxy
    linarith
  have hdiv : ∀ y, (N : ℤ) ∣ Dw.EF d y := fun y => by
    rw [skew]
    exact dvd_neg.mpr (h y)
  let φ : Dw.La →ₗ[ℤ] ℤ :=
    { toFun := fun y => Dw.EF d y / N
      map_add' := fun y z => by
        simp only [map_add (f := _)]
        exact Int.add_ediv_of_dvd_left (hdiv y)
      map_smul' := fun m y => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc _ (hdiv y) }
  obtain ⟨f, hf⟩ := Dw.unimod.2 φ
  refine ⟨f, Dw.unimod.1 (LinearMap.ext fun y => ?_)⟩
  rw [map_nsmul, LinearMap.smul_apply, hf]
  show Dw.EF d y = N • (Dw.EF d y / N)
  rw [nsmul_eq_mul, Int.mul_ediv_cancel' (hdiv y)]

theorem sep_core (A : PolAV (Sp (FractionRing R))) : letI := H.starRing
    ∀ (oA : A.OAct (𝓞 E)) (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a g => g ≫ oA.act a)
        (fun n g g' c => WeilIs A.A A.L n g g' (unitOn c))) (N : ℕ), 1 ≤ N →
      ∀ β u u' : 𝓞 E, β * star β = (N : 𝓞 E) → u * β + u' * star β = 1 →
      ∀ x x' : TFK (R := R) F ⟶ A.A, x ≫ oA.act (star β) = 1 → x' ≫ oA.act (star β) = 1 → x ≠ x' →
        ∃ z : TFK (R := R) F ⟶ A.A, z ≫ oA.act β = 1 ∧
          ∃ c c' : Γ((TFK (R := R) F).left, ⊤)ˣ,
            WeilIs A.A A.L N z x c ∧ WeilIs A.A A.L N z x' c' ∧ c ≠ c' := by
  let _ := H.starRing
  intro oA Dw I N hN β u u' hβ huu x x' hx hx' hne
  have hN0 : 0 < N := hN
  have hlin : ∀ (c : 𝓞 E) b, I.ev N (c • b) = I.ev N b ≫ oA.act c := fun c b => I.lin N c b
  obtain ⟨a, rfl⟩ := (I.onto N hN0 x).1 (pow_eq_one_of_kill oA.toRingAct hβ x hx)
  obtain ⟨a', rfl⟩ := (I.onto N hN0 x').1 (pow_eq_one_of_kill oA.toRingAct hβ x' hx')
  obtain ⟨e, he⟩ := (I.ker N hN0 (star β • a)).1 (by rw [hlin]; exact hx)
  obtain ⟨e', he'⟩ := (I.ker N hN0 (star β • a')).1 (by rw [hlin]; exact hx')
  have hdN : ∀ f : Dw.La, a - a' ≠ N • f := by
    intro f hf
    apply hne
    have : a = a' + N • f := by rw [← hf]; abel
    rw [this, I.add, (I.ker N hN0 _).2 ⟨f, rfl⟩, _root_.mul_one]
  obtain ⟨b0, hb0⟩ : ∃ b0 : Dw.La, ¬ ((N : ℤ) ∣ Dw.EF b0 (a - a')) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨f, hf⟩ := mem_nsmul_of_dvd Dw N (a - a') hcon
    exact hdN f hf
  have h1 : Dw.EF b0 (a - a') = Dw.EF ((u * β) • b0) (a - a') + Dw.EF ((u' * star β) • b0) (a - a') := by
    rw [← LinearMap.add_apply, ← map_add (f := _), ← add_smul, huu, one_smul]
  have h2 : (N : ℤ) ∣ Dw.EF ((u * β) • b0) (a - a') := by
    have hd' : H.bar (u * β) • (a - a') = N • (H.bar u • (e - e')) := by
      rw [map_mul, mul_smul, smul_sub]
      change H.bar u • (star β • a - star β • a') = _
      rw [he, he', ← smul_sub]
      exact smul_comm _ _ _
    rw [Dw.adj, hd', map_nsmul, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  have hb : ¬ (N : ℤ) ∣ Dw.EF ((u' * star β) • b0) (a - a') := fun h => hb0 (by rw [h1]; exact dvd_add h2 h)
  refine ⟨I.ev N ((u' * star β) • b0), ?_, ?_⟩
  · rw [← hlin, smul_smul, show β * (u' * star β) = (N : 𝓞 E) * u' by rw [← hβ]; ring, mul_smul,
      Nat.cast_smul_eq_nsmul]
    exact (I.ker N hN0 _).2 ⟨_, rfl⟩
  · refine ⟨unitOn (I.ζ N ^ Dw.EF ((u' * star β) • b0) a), unitOn (I.ζ N ^ Dw.EF ((u' * star β) • b0) a'),
      I.isom N hN0 _ _, I.isom N hN0 _ _, fun hc => hb ?_⟩
    have hc' := unitOn_injective hc
    rw [← (I.ζ_prim N hN0).zpow_eq_one_iff_dvd, map_sub, zpow_sub, hc', _root_.mul_inv_cancel]

end Sep

theorem alphaPair_holds : AlphaPairStatement := by
  intro E _ _ _ H V _ _ _ t P _ α N hN hαN hu _ F _ _ _ Dw I x x' hx hx' hne
  obtain ⟨u, u', hu⟩ := hu
  exact sep_core (H := H) (R := V) (F := F) P.A P.oA Dw I N hN α u u' hαN hu x x' hx hx' hne

end ReciprocityTheory.ChartRestriction.G.H1
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR

theorem finOrdExists_of (hΦ : DVR.PhiFunStatement) (hP : PhiPowStatement) : FinOrdExistsStatement := by
  intro V _ _ _ D F _ _ _ k hk p w hw
  obtain ⟨Φ, hΦr⟩ := hΦ V (maximalIdeal V) D F k hk p w hw
  obtain ⟨c, hc, hcp⟩ := hP V (maximalIdeal V) D F k hk p w hw
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) (by omega : 0 < k)
  have hζc : ζ ^ k * c = 1 := by rw [hζ, inv_mul_cancel₀ hc]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), zero_mul] at hζc
    exact zero_ne_one hζc
  refine ⟨ζ, hζ0, k, hk, ?_⟩
  intro ss ts h

  have hpow : (Φ ^ k) (ss 0) = c • ss 0 := by
    have := hcp (fun i => (Φ ^ (i : ℕ)) (ss 0)) (by
      intro i
      rw [hΦr]
      simp only [Fin.val_succ, Fin.coe_castSucc, pow_succ', Module.End.mul_apply])
    rw [isSmul_iff] at this
    simpa using this
  have key : ∀ n : ℕ, (hn : n ≤ k) → ss ⟨n, by omega⟩ = ζ ^ n • (Φ ^ n) (ss 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := h ⟨n, by omega⟩
      rw [hΦr] at h1
      rw [isSmul_iff] at h2
      have e : ss ⟨n + 1, by omega⟩ = ss (Fin.succ ⟨n, by omega⟩) := rfl
      have e0 : ss ⟨n, by omega⟩ = ss (Fin.castSucc ⟨n, by omega⟩) := rfl
      rw [e, h2, h1, ← e0, ih (by omega), LinearMap.map_smul, smul_smul, pow_succ' ζ n, pow_succ' Φ n,
        Module.End.mul_apply]
  have hlast : ss (Fin.last k) = ss 0 := by
    have := key k le_rfl
    have e : ss (Fin.last k) = ss ⟨k, by omega⟩ := rfl
    rw [e, this, hpow, smul_smul, hζc, one_smul]
  intro α j
  rw [hlast]

end ReciprocityTheory.ChartRestriction.G.H1
end
end
