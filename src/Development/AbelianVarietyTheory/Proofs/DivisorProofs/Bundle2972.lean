module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle980
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PolarizationKernelOfPIsogenyQuasiInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

section GeomAux

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem liftSq_mul {T : Over S} (a b a' b' : T ⟶ A) :
    (lift a b : T ⟶ G2 A) * lift a' b' = lift (a * a') (b * b') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp]; simp
  · rw [MonObj.mul_comp]; simp

theorem liftSq_pow {T : Over S} (a b : T ⟶ A) (n : ℕ) :
    (lift a b : T ⟶ G2 A) ^ n = lift (a ^ n) (b ^ n) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.pow_comp]; simp
  · rw [MonObj.pow_comp]; simp

end GeomAux

theorem weilIs_heckeSub_geom : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → ∀ u : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (toUnit (Over.mk x) ≫ (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)) (toUnit (Over.mk x) ≫ (lift 1 h₂ : 𝟙_ (Over S) ⟶ G2 o.A)) u → u = 1 := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂ K _ _ x β hx u hu
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hPL : o.P.IsLB := o.isLB
  obtain ⟨I, hI⟩ := o.geom K x β hx
  obtain ⟨x₁, rfl⟩ := hh₁
  obtain ⟨x₂, rfl⟩ := hh₂
  have hpp : p.Prime := Fact.out
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact absurd (Nat.coprime_zero_left p |>.1 hk) hpp.one_lt.ne'
    · exact h
  have hN0 : 0 < N := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = k ^ 2 / c := ⟨_, rfl⟩
  rw [← hm] at hu
  have hmc : m * c = k ^ 2 := by rw [hm]; exact Nat.div_mul_cancel hck
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, zero_mul] at hmc; exact absurd hmc.symm (pow_ne_zero 2 hk0.ne')
    · exact h
  obtain ⟨j, hj0, hjp, hjpar⟩ : ∃ j : ℕ, 0 < j ∧ (j * k ^ 2).Coprime p ∧ (Even j ∨ Odd (j * k ^ 2)) := by
    by_cases h2 : p = 2
    · subst h2
      have hko : Odd k := Nat.coprime_two_right.1 hk
      exact ⟨1, one_pos, by rw [_root_.one_mul]; exact Nat.Coprime.pow_left 2 hk,
        Or.inr (by rw [_root_.one_mul]; exact hko.pow)⟩
    · refine ⟨2, two_pos, Nat.coprime_mul_iff_left.2 ⟨?_, Nat.Coprime.pow_left 2 hk⟩, Or.inl even_two⟩
      exact (Nat.coprime_primes Nat.prime_two hpp).2 (Ne.symm h2)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = j * k ^ 2 := ⟨_, rfl⟩
  rw [← hn₀] at hjp hjpar
  have hn0 : 0 < n₀ := by rw [hn₀]; positivity

  have ev0 : ∀ n, I.ev n 0 = 1 := fun n => by
    have h := I.add n 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have evs : ∀ n (z : D.La) (r : ℕ), I.ev n (r • z) = I.ev n z ^ r := fun n z r => by
    induction r with
    | zero => rw [zero_smul, pow_zero, ev0]
    | succ r ih => rw [succ_nsmul, I.add, ih, pow_succ]
  have hdown : ∀ z : D.La, toUnit (Over.mk x) ≫ o.eta (N • g z) = I.ev n₀ (g z) ^ (j * k) := fun z => by
    have t1 := I.tower k N hk0 hN0 (Nat.coprime_mul_iff_left.2 ⟨hk, hNp⟩) (g z)
    have e : k * (j * k) = n₀ := by rw [hn₀]; ring
    have t2 := I.tower k (j * k) hk0 (by positivity) (by rw [e]; exact hjp) (g z)
    rw [Nat.mul_comm k N] at t1
    rw [hI, evs, t1, ← t2, e]
  obtain ⟨w, hw⟩ : ∃ w, w = I.ev n₀ (g x₁) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = I.ev n₀ (g x₂) := ⟨_, rfl⟩
  have ha : toUnit (Over.mk x) ≫ (lift (o.eta (N • g x₁)) 1 : 𝟙_ (Over S) ⟶ G2 o.A) =
      lift (w ^ (j * k)) (1 ^ (j * k)) := by
    rw [comp_lift, hdown, ← hw, one_pow, MonObj.comp_one]
  have hb : toUnit (Over.mk x) ≫ (lift 1 (o.eta (N • g x₂)) : 𝟙_ (Over S) ⟶ G2 o.A) =
      lift (1 ^ (j * k)) (y ^ (j * k)) := by
    rw [comp_lift, hdown, ← hy, one_pow, MonObj.comp_one]
  rw [ha, hb] at hu
  have e1 := GlobalTheory.T.commutatorPairing_pullback_powerMap_level S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) o.P o.ab (pull_isLB hPL _) o.ample hPL
    o.rig₁ o.rig₂ m (j * k) (j * k) 1 (Over.mk x) w 1 1 y u hu

  have hwn : w ^ n₀ = 1 := (I.onto n₀ hn0 hjp w).2 ⟨g x₁, hw.symm⟩
  have hyn : y ^ n₀ = 1 := (I.onto n₀ hn0 hjp y).2 ⟨g x₂, hy.symm⟩
  have hK : ((n₀ : ℕ) : K) ≠ 0 := by
    have := (b.unit n₀ hjp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have tor : ∀ a a' : Over.mk x ⟶ o.A, a ^ n₀ = 1 → a' ^ n₀ = 1 →
      (lift a a' : Over.mk x ⟶ G2 o.A) ^ n₀ = 1 := fun a a' h h' => by
    rw [liftSq_pow, h, h']
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have one_n : (1 : Over.mk x ⟶ o.A) ^ n₀ = 1 := one_pow _
  have ex : ∀ X Y : Over.mk x ⟶ G2 o.A, X ^ n₀ = 1 → Y ^ n₀ = 1 →
      ∃ e : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) X Y e := fun X Y hX hY =>
    GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 o.A) o.P hA2 hPL K x n₀ hn0 hK X Y hX hY
  obtain ⟨F, hF⟩ := ex _ _ (tor w 1 hwn one_n) (tor 1 y one_n hyn)
  have hFp : ∀ r : ℕ, Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) (lift (w ^ (r + 1)) 1) (lift 1 y) (F ^ (r + 1)) := by
    intro r
    induction r with
    | zero => simpa using hF
    | succ r ih =>
      have := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL ih hF
      rwa [liftSq_mul, _root_.mul_one, ← pow_succ, ← pow_succ] at this
  have hjm : j * m = (j * m - 1) + 1 := (Nat.sub_add_cancel (Nat.mul_pos hj0 hm0)).symm
  have hFjm : Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) (lift (w ^ (j * m)) 1) (lift 1 y) (F ^ (j * m)) := by
    rw [hjm]; exact hFp _
  have hl1 : (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1).IsLB := LB.isLB_linComb hPL _ _
  have iso1 : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1) (o.P.pull (Over.Hom.left (𝟙 (G2 o.A)))) := by
    have c1 := GlobalTheory.CechPic.cls_linComb hPL (fun _ : Fin 1 => 𝟙 (G2 o.A).left) (fun _ => (1 : ℤ)) hl1
    have c2 := GlobalTheory.CechPic.cls_pull hPL (Over.Hom.left (𝟙 (G2 o.A))) (pull_isLB hPL _)
    refine (GlobalTheory.CechPic.cls_eq_iff hl1 (pull_isLB hPL _)).1 (c1.trans (Eq.trans ?_ c2.symm))
    simp
  have e2' : Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1) (n₀ : ℤ) (lift (w ^ (j * m)) (1 ^ 1))
      (lift (1 ^ (j * m)) (y ^ 1)) (F ^ (j * m)) := by
    rw [one_pow, one_pow, pow_one]
    exact GlobalTheory.PELFamily.weilIs_of_lbIso hG hA2 hl1 hPL iso1 hFjm
  have e2 := GlobalTheory.T.commutatorPairing_pullback_powerMap_level S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) o.P o.ab (pull_isLB hPL _) o.ample hPL
    o.rig₁ o.rig₂ 1 (j * m) 1 (n₀ : ℤ) (Over.mk x) w 1 1 y _ e2'
  have hlev : (1 : ℤ) * ((m * (j * k) * (j * k) : ℕ) : ℤ) = (n₀ : ℤ) * ((1 * (j * m) * 1 : ℕ) : ℤ) := by
    rw [hn₀]; push_cast; ring

  have hu' : u = F ^ (j * m) := GlobalTheory.CommutatorPairing.weilIs_unique hG hA2 hPL e1 (hlev ▸ e2)

  have hgeo := I.isom n₀ hn0 hjp (g x₁) (g x₂)
  rw [← hw, ← hy] at hgeo
  obtain ⟨c11, h11⟩ := ex (lift w 1) (lift y 1) (tor w 1 hwn one_n) (tor y 1 hyn one_n)
  obtain ⟨c21, h21⟩ := ex (lift 1 w) (lift y 1) (tor 1 w one_n hwn) (tor y 1 hyn one_n)
  obtain ⟨c22, h22⟩ := ex (lift 1 w) (lift 1 y) (tor 1 w one_n hwn) (tor 1 y one_n hyn)
  have hA := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL h11 h21
  have hB := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL hF h22
  rw [liftSq_mul, _root_.mul_one, _root_.one_mul] at hA hB
  have hs := GlobalTheory.CommPairing.weilIs_symm hPL (GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL
    (GlobalTheory.CommPairing.weilIs_symm hPL hA) (GlobalTheory.CommPairing.weilIs_symm hPL hB))
  rw [liftSq_mul, _root_.mul_one, _root_.one_mul] at hs
  have hd := GlobalTheory.T.weilPairing_diagonal_pullback_eq S o.A o.P o.ab hPL _ (Over.mk x) w y _ _ hs hgeo
  have e11 := (GlobalTheory.T.weilPairing_birigidified_trivial_on_axes S o.A o.P o.ab hPL o.rig₁ o.rig₂ _ (Over.mk x) w y c11).1 h11
  have e22 := (GlobalTheory.T.weilPairing_birigidified_trivial_on_axes S o.A o.P o.ab hPL o.rig₁ o.rig₂ _ (Over.mk x) w y c22).2 h22
  have e21 := GlobalTheory.T.commutatorPairing_swap_eq_of_swap_invariant S o.A o.P o.ab hPL o.symm _ (Over.mk x) w y c21 F h21 hF
  rw [e11, e22, e21] at hd
  have hF2 : F ^ 2 = unitOn (I.ζ n₀ ^ (2 * ((c : ℤ) * D.EF x₁ x₂))) := by
    rw [← hEF, ← hd]; group

  have hζ : I.ζ n₀ ^ n₀ = 1 := (I.ζ_prim n₀ hn0 hjp).pow_eq_one
  have hz : ∀ z : ℤ, I.ζ n₀ ^ ((n₀ : ℤ) * z) = 1 := fun z => by
    rw [zpow_mul, zpow_natCast, hζ, one_zpow]
  have hmcZ : (m : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast hmc
  have hnZ : (n₀ : ℤ) = j * (k : ℤ) ^ 2 := by rw [hn₀]; push_cast; ring
  have uPow : ∀ (a : Kˣ) (n : ℕ), unitOn (a ^ n) = unitOn a ^ n := fun a n => map_pow (Units.map _) a n
  have uOne : unitOn (1 : Kˣ) = 1 := map_one (Units.map _)
  have hpw : ∀ t : ℕ, F ^ (2 * t) = unitOn (I.ζ n₀ ^ (2 * ((c : ℤ) * D.EF x₁ x₂) * (t : ℤ))) := fun t => by
    rw [pow_mul, hF2, ← uPow, ← zpow_natCast, ← zpow_mul]
  rcases hjpar with ⟨i, hi⟩ | hodd
  · have e : j * m = 2 * (i * m) := by rw [hi]; ring
    rw [hu', e, hpw]
    have ex' : 2 * ((c : ℤ) * D.EF x₁ x₂) * ((i * m : ℕ) : ℤ) = (n₀ : ℤ) * D.EF x₁ x₂ := by
      rw [hnZ, ← hmcZ, hi]; push_cast; ring
    rw [ex', hz, uOne]
  · have h2 : u ^ 2 = 1 := by
      rw [hu', ← pow_mul, Nat.mul_comm, hpw]
      have ex' : 2 * ((c : ℤ) * D.EF x₁ x₂) * ((j * m : ℕ) : ℤ) = (n₀ : ℤ) * (2 * D.EF x₁ x₂) := by
        rw [hnZ, ← hmcZ]; push_cast; ring
      rw [ex', hz, uOne]
    have hFn : F ^ n₀ = 1 := GlobalTheory.SiegelTypings.weil_pow_eq_one hA2 hPL (tor w 1 hwn one_n) hF
    have hn : u ^ n₀ = 1 := by rw [hu', ← pow_mul, Nat.mul_comm, pow_mul, hFn, one_pow]
    have hg := pow_gcd_eq_one.2 ⟨h2, hn⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 hodd), pow_one] at hg

end GlobalTheory.UPel.HT.Hecke
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

theorem _root_.GlobalTheory.T.exists_galoisConjugate_genericBundle_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ), (∀ σ, a.act σ ≫ β = β) → ∀ σ : Gal ρ, ∃ ψ : pullback G'.hom (jK R') ⟶ pullback G'.hom (jK R'), ψ ≫ genMap hρ β hβ = genMap hρ β hβ ∧ ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom ∧ LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) ((U'.LG.L.pull (pullback.fst G'.hom (jK R'))).pull ψ) := by
  first | exact @GlobalTheory.Mum.GenDesc.exists_inv | exact GlobalTheory.Mum.GenDesc.exists_inv | (intros; apply GlobalTheory.Mum.GenDesc.exists_inv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

theorem _root_.GlobalTheory.T.fixed_mem_range_fractionFieldMap_galoisInvariants : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), IsGal ρ → ∀ y : FractionRing R', (∀ σ : Gal ρ, fracAut σ.1 y = y) → y ∈ (fracMap ρ hρ).range := by
  first | exact @GlobalTheory.Mum.GenDesc.fixed_mem_range | exact GlobalTheory.Mum.GenDesc.fixed_mem_range | (intros; apply GlobalTheory.Mum.GenDesc.fixed_mem_range <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.quasiInverse_root_bundle_symmetric : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → LBIso P' (P'.pull (lift (snd B B) (fst B B)).left) := by
  first | (exact @GlobalTheory.QuasiInvPull.root_symm) | (exact GlobalTheory.QuasiInvPull.root_symm) | (intros; apply GlobalTheory.QuasiInvPull.root_symm  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.adicCompletion_ring_injective_invariants_of_module : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A) (Γ : Type) (g : Γ → (B →ₐ[A] B)),
    Function.Injective (AdicCompletion.map J (Algebra.linearMap A B)) →
    (∀ y, y ∈ LinearMap.range (AdicCompletion.map J (Algebra.linearMap A B)) ↔
      ∀ σ, AdicCompletion.map J (g σ).toLinearMap y = y) →
    Function.Injective (GlobalTheory.InvAlg.cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl) ∧
    ∀ y, y ∈ Set.range (GlobalTheory.InvAlg.cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl) ↔
      ∀ σ, GlobalTheory.InvAlg.cmap (g σ).toRingHom (J.map (algebraMap A B)) (J.map (algebraMap A B))
        (GlobalTheory.InvAlg.map_algebraMap_le (g σ) J) y = y := by
  first | exact @GlobalTheory.InvAlg.cmap_transfer | exact GlobalTheory.InvAlg.cmap_transfer | (intros; apply GlobalTheory.InvAlg.cmap_transfer <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.flat_tensor_galois_injective_invariants : ∀ (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] [Algebra R O] [Module.Flat R O],
    Function.Injective (algebraMap R R') → GlobalTheory.Mum.IsGal (algebraMap R R') →
    Function.Injective (algebraMap O (TensorProduct R O R')) ∧
    ∀ t : TensorProduct R O R', (∀ σ, GlobalTheory.InvAlg.galTensor O σ t = t) →
      t ∈ Set.range (algebraMap O (TensorProduct R O R')) := by
  first | exact @GlobalTheory.InvAlg.flat_tensor_invariants | exact GlobalTheory.InvAlg.flat_tensor_invariants | (intros; apply GlobalTheory.InvAlg.flat_tensor_invariants <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.quasiInverse_root_bundle_rosati_descended_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → ∀ a : D.O, LBIso (P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left) (P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left) := by
  first | (exact @GlobalTheory.UPel.HT.ES.rosati_of_quasiInv_root) | (exact GlobalTheory.UPel.HT.ES.rosati_of_quasiInv_root) | (intros; apply GlobalTheory.UPel.HT.ES.rosati_of_quasiInv_root  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.adicCompletion_equivariant_equiv_of_level_isos : ∀ (R : Type) [CommRing R] (m : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C']
    [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (act : GlobalTheory.Mum.Gal (algebraMap R R') →* (C' ≃ₐ[R] C')),
    (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) →
    ∀ (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (m ^ (e + 1)).map (algebraMap R C')),
    (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) →
    (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) →
    (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧
      RingHom.ker (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) =
        (m ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) →
    ∀ (IT : Ideal (TensorProduct R O R')) (IC : Ideal C'), IT = m.map (algebraMap R (TensorProduct R O R')) →
      IC = m.map (algebraMap R C') →
    ∀ (hT : ∀ σ, IT.map (GlobalTheory.InvAlg.galTensor O σ).toRingHom ≤ IT)
      (hC : ∀ σ, IC.map (act σ).toRingEquiv.toRingHom ≤ IC),
    ∃ Ψ : AdicCompletion IT (TensorProduct R O R') ≃ₐ[R] AdicCompletion IC C',
      (∀ σ y, Ψ (GlobalTheory.InvAlg.cmap (GlobalTheory.InvAlg.galTensor O σ).toRingHom
          IT IT (hT σ) y) = GlobalTheory.InvAlg.cmap (act σ).toRingEquiv.toRingHom IC IC (hC σ) (Ψ y)) ∧
      ∀ e (x : O) (y : C'), Ideal.Quotient.mk ((m ^ (e + 1)).map (algebraMap R C')) y = i e x →
        AdicCompletion.evalₐ IC (e + 1) (Ψ (AdicCompletion.of IT _ (x ⊗ₜ[R] (1 : R')))) =
          Ideal.Quotient.mk (IC ^ (e + 1)) y := by
  first | exact @GlobalTheory.InvAlg.Levels.levels_equiv | exact GlobalTheory.InvAlg.Levels.levels_equiv | (intros; apply GlobalTheory.InvAlg.Levels.levels_equiv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.polarization_kernel_of_p_isogeny_quasi_inverse : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) (ψ' : o'.A ⟶ o.A), IsUnit ((p : ℕ) : R) → IsPIsog c o o' ψ → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) := by
  first | exact @UpperTheory.Cb.polarization_kernel_of_p_isogeny_quasi_inverse | exact UpperTheory.Cb.polarization_kernel_of_p_isogeny_quasi_inverse
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

theorem over₀_prod_zpow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (b : K → (D.toPre.P.A ⟶ D₀.toPre.P.A)), (∀ i, Over₀ U U₀ (a i) (b i)) → Over₀ U U₀ (∏ i, a i ^ n i) (∏ i, b i ^ n i) := by
  intro R _ _ I D D₀ A A₀ G G₀ _ _ _ _ U U₀ K _ n a b h e
  let P := Over.pullback (thick R I e)
  have := (U₀.gt e).q_hom
  let fG : (G ⟶ G₀) →* (P.obj G ⟶ P.obj G₀) :=
    MonoidHom.mk' (fun x => P.map x) fun x y => Functor.map_mul P x y
  let fB : (D.toPre.P.A ⟶ D₀.toPre.P.A) →* (P.obj D.toPre.P.A ⟶ P.obj D₀.toPre.P.A) :=
    MonoidHom.mk' (fun x => P.map x) fun x y => Functor.map_mul P x y
  have hG : P.map (∏ i, a i ^ n i) = ∏ i, P.map (a i) ^ n i :=
    (map_prod fG _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow fG _ _)
  have hB : P.map (∏ i, b i ^ n i) = ∏ i, P.map (b i) ^ n i :=
    (map_prod fB _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow fB _ _)
  show P.map (∏ i, a i ^ n i) ≫ (U₀.gt e).q = (U.gt e).q ≫ P.map (∏ i, b i ^ n i)
  rw [hG, hB, prod_zpow_comp, comp_prod_zpow]
  exact Finset.prod_congr rfl fun i _ => by rw [h i e]

end GlobalTheory.Mum.PowData
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.mumfordIso_eq_rosatiGenerator_mul_comparison : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (inc : D₀.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D₀.P.A) [IsMonHom inc] [IsMonHom pr] (ea fa ea' : D'.P.A ⟶ D'.P.A) [IsMonHom ea] [IsMonHom fa] [IsMonHom ea'], pr ≫ inc = ea → ∀ (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa) : G2 D₀.P.A ⟶ G2 D'.P.A).left)), w.IsGen → (∀ (T : Over (Sp R)) (y : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι) (J' : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D'.P.L z J → Good D₀.P.L z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ D₀.P.A) y).left z J J' = 1) → ∀ (ur : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A ea ea') rosatiε)), ur.IsGen → (∀ (T : Over (Sp R)) (y : T ⟶ D'.P.A) (z : T.left) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val ur (lift (1 : T ⟶ D'.P.A) y).left z J = 1) → ∀ (χ' : D'.X) (χ : D₀.X) (q : 𝟙_ (Over (Sp R)) ⟶ D'.P.A), D₀.c χ ≫ inc ≫ fa = q → D'.c χ' = q ≫ ea' → ∀ (u : LB.Gen (CmpLB D' D₀ pr χ' χ)), Nrm u → ∀ (T : Over (Sp R)) (x : T ⟶ D'.P.A) (z : T.left) (J : (T.left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → GlobalTheory.PolDeg.lamVal w (lift (x ≫ pr) (toUnit T ≫ D₀.c χ)).left z (rl J) (rr J) = val ur (lift x (toUnit T ≫ q)).left z (rl J) * val u x.left z J := by
  first | exact @GlobalTheory.Mum.Two.lam_eq_ros_mul_cmp | exact GlobalTheory.Mum.Two.lam_eq_ros_mul_cmp | (intros; apply GlobalTheory.Mum.Two.lam_eq_ros_mul_cmp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.uniformisedGroupHom_induced_maps_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), (∀ b b' : D₁.toPre.P.A ⟶ D₂.toPre.P.A, Over₀ U₁ U₂ a b → Over₀ U₁ U₂ a b' → b = b') ∧ ∀ h h' : D₂.toPre.X → D₁.toPre.X, OnTorus U₁ U₂ a h → OnTorus U₁ U₂ a h' → h = h' := by
  first | exact @GlobalTheory.Mum.Two.over₀_onTorus_unique | exact GlobalTheory.Mum.Two.over₀_onTorus_unique | (intros; apply GlobalTheory.Mum.Two.over₀_onTorus_unique <;> assumption)
end
