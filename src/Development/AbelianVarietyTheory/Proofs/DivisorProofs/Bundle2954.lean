module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticSimilitudeActionOnLevelFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pointValue_fractionField_eq_basicOpen_extension : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R) (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* FractionRing Ω), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = algebraMap Ω (FractionRing Ω) (φ r)) → ∀ (O : G.left.Opens) (h : O ≤ G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ O → ∀ θ, valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') O (GlobalTheory.HeatV.cst G.hom _ h θ) = iota θ := by
  first | exact @GlobalTheory.HeatV.valR_cst_eq_iota | exact GlobalTheory.HeatV.valR_cst_eq_iota | (intros; apply GlobalTheory.HeatV.valR_cst_eq_iota <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.mul_of_scaled_section_values : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y), L.IsLB → ∀ (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k l : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g l s' → GlobalTheory.HeatSym.VS φ L x g (k + l) (s * s') := by
  first | exact @GlobalTheory.HeatSym.VS.mul | exact GlobalTheory.HeatSym.VS.mul | (intros; apply GlobalTheory.HeatSym.VS.mul <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sub_of_scaled_section_values : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (p : Y ⟶ Sp R) (L : LB Y) (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)), x ≫ p = spMap φ → ∀ (k : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g k s' → GlobalTheory.HeatSym.VS φ L x g k (s - s') := by
  first | exact @GlobalTheory.HeatSym.VS.sub | exact GlobalTheory.HeatSym.VS.sub | (intros; apply GlobalTheory.HeatSym.VS.sub <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.vertical_derivation_lifting_principalPolarization_eq_zero : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap x₀) m₀ → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun _ => 0) V jj v q → ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), v W f = 0 := by
  first | exact @GlobalTheory.HeatConn.Vert.vert_eq_zero | exact GlobalTheory.HeatConn.Vert.vert_eq_zero | (intros; apply GlobalTheory.HeatConn.Vert.vert_eq_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.isAffineHom_zarhinProduct_to_eighthPower : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → IsAffineHom (GlobalTheory.ZarhinFam.zphi c.A B mu).left := by
  first | (exact @GlobalTheory.ZarhinFam.isAffineHom_zphi) | (exact GlobalTheory.ZarhinFam.isAffineHom_zphi) | (intros; apply GlobalTheory.ZarhinFam.isAffineHom_zphi  <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.zarhinTriangularMatrix_symmetrisation_posDef : ∀ (d : ℕ), 0 < d → ((GlobalTheory.ZarhinFam.zW d + (GlobalTheory.ZarhinFam.zW d).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  first | (exact @GlobalTheory.ZarhinFam.zW_symm_posDef) | (exact GlobalTheory.ZarhinFam.zW_symm_posDef) | (intros; apply GlobalTheory.ZarhinFam.zW_symm_posDef  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.nsmul_zarhinDiagonalClass_eq_form : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → d • GlobalTheory.CechPic.pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left (GlobalTheory.ZarhinFam.zCls c.A B c.isLB hZ.2.1.isLB d mu) = ∑ kl : Fin 8 × Fin 8, GlobalTheory.ZarhinFam.zW d kl.1 kl.2 • GlobalTheory.CechPic.pull (lift (GlobalTheory.ZarhinFam.zpr c.A B mu kl.1) (GlobalTheory.ZarhinFam.zpr c.A B mu kl.2)).left (GlobalTheory.CechPic.cls c.P c.isLB) := by
  first | (exact @GlobalTheory.ZarhinFam.nsmul_pull_diag_zCls) | (exact GlobalTheory.ZarhinFam.nsmul_pull_diag_zCls) | (intros; apply GlobalTheory.ZarhinFam.nsmul_pull_diag_zCls  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT.KerBy

theorem ev_nsmul {La Q : Type} [AddCommGroup La] [Group Q] (f : La → Q) (hadd : ∀ x y, f (x + y) = f x * f y)
    (e : ℕ) (y : La) : f (e • y) = f y ^ e := by
  induction e with
  | zero =>
    have h := hadd 0 0
    rw [add_zero] at h
    simpa using (mul_eq_left.1 h.symm)
  | succ e ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem pow_eq_one_at_geom (hC : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1) {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (e : ℕ) (hEF : ∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f)
    (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (g : Over.mk x₀ ⟶ o.A)
    (hg : ∃ t : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ g) (fst o.A (Over.mk x₀))).left).Gen, t.IsGen) :
    g ^ e = 1 := by
  have hpr : p.Prime := Fact.out
  obtain ⟨e', he', hk⟩ := o.kerP
  have hn : g ^ e' = 1 := hk _ g hg
  have hpos : 0 < e' := by
    rcases Nat.eq_zero_or_pos e' with h | h
    · subst h
      have := (Nat.coprime_zero_left p).1 he'
      exact absurd this hpr.one_lt.ne'
    · exact h
  let φ := Spec.preimage (x₀ ≫ t)
  have hβ : x₀ ≫ t = spMap φ.hom := by
    simp [spMap, φ]
  obtain ⟨I, -⟩ := o.geom k x₀ φ.hom hβ
  have hunit : ∀ m : ℕ, m.Coprime p → ((m : ℕ) : k) ≠ 0 := fun m hm => by
    have := (b.unit m hm).map φ.hom
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨y, hy⟩ := (I.onto e' hpos he' g).1 hn
  have hadd : ∀ m, ∀ u v, I.ev m (u + v) = I.ev m u * I.ev m v := fun m u v => I.add m u v

  have vanish : ∀ (m : ℕ), 0 < m → m.Coprime p → ∀ y' z : D.La, I.ev m y' ^ 2 = g →
      I.ζ m ^ (2 * D.EF y' z) = 1 := by
    intro m hm hmp y' z ha
    have ha1 : I.ev m y' ^ m = 1 := (I.onto m hm hmp _).2 ⟨y', rfl⟩
    have hb1 : I.ev m z ^ m = 1 := (I.onto m hm hmp _).2 ⟨z, rfl⟩
    have hgen : ∃ t : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ I.ev m y' ^ 2) (fst o.A (Over.mk x₀))).left).Gen,
        t.IsGen := ha ▸ hg
    have hc := hC S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample k x₀ m (hunit m hmp) _ _ ha1 hb1 hgen _
      (I.isom m hm hmp y' z)
    exact ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (hc.trans (map_one _).symm)
  have key : ∀ z, (e' : ℤ) ∣ D.EF y z := by
    intro z
    by_cases hp2 : p = 2
    · subst hp2
      have hodd : Odd e' := Nat.odd_iff.2 (by
        rcases Nat.even_or_odd e' with h | h
        · exact absurd (Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.1 h) he') (by norm_num)
        · exact Nat.odd_iff.1 h)
      obtain ⟨r, hr⟩ := hodd
      have h2 : 2 • ((r + 1) • y) = y + e' • y := by
        rw [smul_smul, hr]
        rw [show (2 * (r + 1)) = 1 + (2 * r + 1) by ring, add_smul, one_smul]
      have ha : I.ev e' ((r + 1) • y) ^ 2 = g := by
        rw [← ev_nsmul _ (hadd e'), h2, hadd, ev_nsmul _ (hadd e'), hy, hn, _root_.mul_one]
      have h1 := vanish e' hpos he' _ z ha
      have h3 := ((I.ζ_prim e' hpos he').zpow_eq_one_iff_dvd _).1 h1
      rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3
      have h4 : (e' : ℤ) ∣ (((r + 1) * 2 : ℕ) : ℤ) * D.EF y z := by
        have : (2 : ℤ) * (((r + 1 : ℕ) : ℤ) * D.EF y z) = (((r + 1) * 2 : ℕ) : ℤ) * D.EF y z := by push_cast; ring
        rw [← this]; exact_mod_cast h3
      have hcop : IsCoprime (e' : ℤ) (((r + 1) * 2 : ℕ) : ℤ) := by
        rw [Nat.isCoprime_iff_coprime]
        have : (r + 1) * 2 = e' + 1 := by omega
        rw [this]
        exact (Nat.coprime_self_add_right.2 (Nat.coprime_one_right e'))
      exact hcop.dvd_of_dvd_mul_left h4
    · have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hpr).2 (Ne.symm hp2)
      have hmp : (e' * 2).Coprime p := Nat.Coprime.mul_left he' h2p
      have ha : I.ev (e' * 2) y ^ 2 = g := by
        rw [I.tower e' 2 hpos two_pos hmp y, hy]
      have h1 := vanish (e' * 2) (by omega) hmp y z ha
      have h3 := ((I.ζ_prim (e' * 2) (by omega) hmp).zpow_eq_one_iff_dvd _).1 h1
      have h4 : (e' : ℤ) * 2 ∣ D.EF y z * 2 := by
        have : (2 : ℤ) * D.EF y z = D.EF y z * 2 := by ring
        rw [← this]; exact_mod_cast h3
      exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 h4
  let f : D.La →ₗ[ℤ] ℤ :=
    { toFun := fun z => D.EF y z / e'
      map_add' := fun u v => by
        rw [map_add (f := _), Int.add_ediv_of_dvd_left (key u)]
      map_smul' := fun r u => by
        rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, Int.mul_ediv_assoc _ (key u)] }
  have hf : ∀ z, (e' : ℤ) * f z = D.EF y z := fun z => Int.mul_ediv_cancel' (key z)
  obtain ⟨w, hw⟩ := hEF f
  have hyw : e • y = e' • w := by
    apply D.nondeg
    ext z
    have hwz : D.EF w z = e • f z := by rw [hw]; rfl
    simp only [map_nsmul, LinearMap.smul_apply, hwz, nsmul_eq_mul]
    rw [← hf z]; ring
  calc g ^ e = I.ev e' y ^ e := by rw [hy]
    _ = I.ev e' (e • y) := (ev_nsmul _ (hadd e') e y).symm
    _ = 1 := by rw [hyw]; exact (I.ker e' hpos he' _).2 ⟨w, rfl⟩

end GlobalTheory.UPel.HT.KerBy

namespace GlobalTheory.UPel.HT.KerBy

theorem gen_comp : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left) (T T' : Over S) (a : T' ⟶ T) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → ∃ t : (P.pull (lift (snd A T' ≫ a ≫ x) (fst A T')).left).Gen, t.IsGen := by
  intro S A _ P T T' a x hx
  obtain ⟨t, ht⟩ := hx
  have e : (A ◁ a) ≫ lift (snd A T ≫ x) (fst A T) = lift (snd A T' ≫ a ≫ x) (fst A T') := by
    rw [comp_lift, whiskerLeft_snd_assoc, whiskerLeft_fst]
  rw [← e, Over.comp_left]
  exact ⟨_, LB.isGen_pullGen P _ _ t ht (A ◁ a).left⟩

end GlobalTheory.UPel.HT.KerBy

namespace GlobalTheory.UPel.HT.KerBy

theorem siegKerBy_toSieg_of (hA : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ A), x ^ n = 1 → ∀ d : ℕ, (∀ (k : Type) [Field k] [IsAlgClosed k] (ξ : Sp k ⟶ T.left), ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) → x ^ d = 1) (hB : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left) (T T' : Over S) (a : T' ⟶ T) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → ∃ t : (P.pull (lift (snd A T' ≫ a ≫ x) (fst A T')).left).Gen, t.IsGen) (hC : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1) : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (h M : ℕ) (t₁ : S ⟶ Sp (cycAway M)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ lev) (e : ℕ), e.Coprime p → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SiegKerBy (o.toSieg hl) e := by
  intro p _ D R _ b N S t o h M t₁ lev hl e _ hEF
  refine ⟨Obj.toSieg_ample o hl, ?_⟩
  intro T x hx
  obtain ⟨e', he', hk⟩ := o.kerP
  have hx' : x ^ e' = 1 := hk T x hx
  have hu : IsUnit ((e' : ℕ) : Γ(S, ⊤)) := by
    have h1 := (b.unit e' he').map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    have h2 := h1.map t.appTop.hom
    simpa using h2
  refine hA S o.A o.ab e' hu T x hx' e (fun k _ _ ξ => ?_)
  have hx2 := hB S o.A o.P T (Over.mk (ξ ≫ T.hom)) (Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) x hx
  exact pow_eq_one_at_geom hC o e hEF k (ξ ≫ T.hom) _ hx2

end GlobalTheory.UPel.HT.KerBy

namespace GlobalTheory.UPel.HT.KerBy

theorem siegKerBy_toSieg : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (h M : ℕ) (t₁ : S ⟶ Sp (cycAway M)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ lev) (e : ℕ), e.Coprime p → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SiegKerBy (o.toSieg hl) e :=
  siegKerBy_toSieg_of GlobalTheory.T.pow_eq_one_of_geometric_points_torsion gen_comp GlobalTheory.T.commutatorPairing_eq_one_trivial_on_axis

end GlobalTheory.UPel.HT.KerBy
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor


theorem _root_.GlobalTheory.T.exists_symplecticSimilitude_action_on_levelFamily : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
    ∃ ρ : sympSimGrp h M → (X ⟶ X), ρ 1 = 𝟙 X ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ SympActs s s₁ u lev ρ := by
  first | exact @GlobalTheory.UPel.HT.SympAct.exists_sympActs | exact GlobalTheory.UPel.HT.SympAct.exists_sympActs | (intros; apply GlobalTheory.UPel.HT.SympAct.exists_sympActs <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.psi_eq_tau_from_sign_relation_four_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (O : Type) [CommRing O] [StarRing O] [Module O D.X] (o : D.OAct O) (w : O), w + star w = 1 → ∀ u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w), Normd u → ∀ gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]), Normd gam → ∀ p q r : QkPt D F 4, q.y = w • p.y → r.y = (1 + w) • p.y → GtAct o w p.g q.g → GtAct o (1 + w) p.g r.g → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ s s' s'' : ((TF (R := R) F).left.presheaf.stalk z)ˣ, s * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (p.g.s p.y) (𝟙 _) z J ^ 2 * val gam p.g.b.left z J → s' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (q.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (q.g.s q.y) (𝟙 _) z J ^ 2 * val gam q.g.b.left z J → s'' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (r.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (r.g.s r.y) (𝟙 _) z J ^ 2 * val gam r.g.b.left z J → s'' = s ^ 2 * s' → @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) * val u (cP D (TF (R := R) F) p.y).left z J = @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J := by
  first | exact @GlobalTheory.PsiSignRel.sign_rel | exact GlobalTheory.PsiSignRel.sign_rel | (intros; apply GlobalTheory.PsiSignRel.sign_rel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem chartCover_toTerm {S : Scheme.{0}} {A : Over S} (f : A ⟶ Over.mk (𝟙 S)) :
    f = Over.homMk A.hom (by simp) := by
  ext1
  simpa using Over.w f

theorem comp_transl {S : Scheme.{0}} {G A : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) (h : A ⟶ G) :
    h ≫ transl y = h * (Over.homMk A.hom (by simp) ≫ y) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc]
  congr 2
  exact chartCover_toTerm _

theorem chart_cover : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G']
    (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')),
    (∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨
      ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u) →
    ∀ p : G'.left, ∃ j, p ∈ Set.range (N.chart x j) := by
  intro R _ _ S π G' _ N n x H p
  let t : Sp (G'.left.residueField p) ⟶ G'.left := G'.left.fromSpecResidueField p
  let s : Sp (G'.left.residueField p) ⟶ S := t ≫ G'.hom
  let g : Over.mk s ⟶ G' := Over.homMk t rfl
  have hp : g.left (IsLocalRing.closedPoint _) = p := Scheme.fromSpecResidueField_apply p _
  rcases H (G'.left.residueField p) s g with h1 | ⟨i, h2⟩
  · exact ⟨none, by simpa [Near.chart] using h1 ⟨_, hp⟩⟩
  · let c : Over.mk s ⟶ G' := (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i
    obtain ⟨b, hb⟩ := h2 ⟨IsLocalRing.closedPoint _, rfl⟩
    have key : (g * c) ≫ transl (x i)⁻¹ = g := by
      rw [comp_transl]
      have e : (Over.homMk (Over.mk s).hom (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ (x i)⁻¹ = c⁻¹ := by
        rw [GrpObj.comp_inv]; rfl
      rw [e, mul_inv_cancel_right]
    refine ⟨some i, b, ?_⟩
    rw [Near.chart_some, Scheme.Hom.comp_apply, hb]
    have e2 : ((g * c) ≫ transl (x i)⁻¹).left (IsLocalRing.closedPoint _) = p := by rw [key]; exact hp
    rw [Over.comp_left] at e2
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e2

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem transl_toTerm_eq {S : Scheme.{0}} {X : Over S} (f g : X ⟶ Over.mk (𝟙 S)) : f = g := by
  ext
  have hf := Over.w f
  have hg := Over.w g
  simp only [Over.mk_hom] at hf hg
  exact (Category.comp_id f.left).symm.trans (hf.trans (hg.symm.trans (Category.comp_id g.left)))

theorem transl_comp {S : Scheme.{0}} {G : Over S} [GrpObj G] (y z : Over.mk (𝟙 S) ⟶ G) :
    transl y ≫ transl z = transl (y * z) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc,
    transl_toTerm_eq (_ ≫ Over.homMk G.hom (by simp)) (Over.homMk G.hom (by simp)), _root_.mul_assoc, ← comp_mul]

theorem transl_one {S : Scheme.{0}} {G : Over S} [GrpObj G] : transl (1 : Over.mk (𝟙 S) ⟶ G) = 𝟙 G := by
  unfold transl
  rw [comp_one, _root_.mul_one]

instance transl_isIso {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : IsIso (transl y) :=
  ⟨⟨transl y⁻¹, by rw [transl_comp, _root_.mul_inv_cancel, transl_one], by rw [transl_comp, _root_.inv_mul_cancel, transl_one]⟩⟩

instance transl_left_isIso {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : IsIso (transl y).left :=
  inferInstanceAs (IsIso ((Over.forget S).map (transl y)))

theorem Near.chart_isOpenImmersion_over {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R)
    (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')) (j : Option (Fin n)) :
    IsOpenImmersion (N.chart x j) ∧ N.chart x j ≫ G'.hom = pullback.snd N.U.hom π := by
  have := N.isOpen
  cases j with
  | none => exact ⟨N.isOpen, N.u_over⟩
  | some k =>
    refine ⟨?_, ?_⟩
    · rw [Near.chart_some]; infer_instance
    · rw [Near.chart_some, Category.assoc, Over.w, N.u_over]

end GlobalTheory.Mum
end
