module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle047
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle049
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle052
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OLiftSys
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle937
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels.O

private lemma nat_mem_of_isGen {A : Type} [CommRing A] {a : A} {N : ℕ} {𝔞 : Ideal A} (h : IsGen a N 𝔞) : (N : A) ∈ 𝔞 := by
  have h' : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)} := h
  have hN : (N : A) ∈ Ideal.span {(N : A)} := Ideal.mem_span_singleton_self _
  rw [← h'] at hN
  exact (Ideal.mul_le_right : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 ≤ 𝔞) hN

theorem clsAt : ClsAt := by
  intro q _ D hm1 r hr R R' _ _ _ b gb β hmatch N N₀ c a 𝔞 hN hpos hcop hgen hue Y Ω _ _ y σ hyσ
  obtain ⟨o1, ⟨n1⟩⟩ := raise q D R R' b gb β hmatch N N₀ c hN hpos hcop Y.X Y.s Y.univ Ω y σ hyσ
  obtain ⟨o₀, ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull q D R b N₀ Y.X (Sp Ω) Y.s y Y.univ
  have htr : ∀ {f f' : Sp Ω ⟶ Y.X} (_ : f = f') (n : QMap o1 Y.univ f c),
      ∃ n'' : QMap o1 Y.univ f' c, n''.φ = n.φ := by
    intro f f' h n
    subst h
    exact ⟨n, rfl⟩
  obtain ⟨n1', hn1'⟩ := htr (Category.id_comp y).symm n1
  obtain ⟨n, hn⟩ := (UpperTheory.quotient_map_comp q D R R' b gb N N₀ c (Sp Ω) (Sp Ω) Y.X σ (y ≫ Y.s) Y.s o1 o₀ Y.univ
    (𝟙 _) y).2.1 n1' m
  rw [hn1'] at hn
  obtain ⟨l, hl, hln⟩ := UpperTheory.quotient_level_of_lattice_generation UpperTheory.lattice_generation q D R R' b gb N N₀ c a 𝔞 hpos hgen (Sp Ω) σ (y ≫ Y.s) o1 o₀ n
  obtain ⟨lv', hlv', hlvm⟩ := isEtLev_exists_pull m Y.isLev
  obtain ⟨g₀, hg₀⟩ := Cmp.exists_levGrp hlv' hl
  obtain ⟨g, glin, gonto, ginj, giso, gtow, gN₀, gq⟩ := liftSys q D hm1 r hr 𝔞 N₀ hue hcop g₀
  obtain ⟨o', n', ho'⟩ := oResim q D R R' b gb N N₀ c hN hpos (Sp Ω) Y.X σ Y.s o1 Y.univ y n1 g
    ⟨glin, gonto, ginj, giso, gtow⟩ gN₀
  refine ⟨o', ⟨y, hyσ, n', fun y' => ?_⟩, rfl⟩
  have heta : o1.eta (g N (algebraMap (𝓞 D.F) D.O a • y')) = o1.eta (algebraMap (𝓞 D.F) D.O a • liftAct g₀ y') := by
    obtain ⟨z1, hz1⟩ := glin N hpos (algebraMap (𝓞 D.F) D.O a) y'
    have hq := gq N hpos (nat_mem_of_isGen hgen) y'
    have hdiff : g N y' - liftAct g₀ y' ∈ wSub D 𝔞 1 := by
      rw [← Submodule.Quotient.eq]
      rw [mk_liftAct]
      exact hq
    obtain ⟨z2, hz2⟩ := ((UpperTheory.lattice_generation q D a N 𝔞 hpos hgen).1 _).mpr hdiff
    have hsplit : algebraMap (𝓞 D.F) D.O a • g N y' =
        algebraMap (𝓞 D.F) D.O a • liftAct g₀ y' + N • z2 := by
      rw [← hz2, ← smul_add]
      congr 1
      abel
    rw [hz1, hsplit]
    have e1 := o1.eta_add (algebraMap (𝓞 D.F) D.O a • liftAct g₀ y' + N • z2) (N • z1)
    have e2 := o1.eta_add (algebraMap (𝓞 D.F) D.O a • liftAct g₀ y') (N • z2)
    have k1 : o1.eta (N • z1) = 1 := o1.eta_ker z1
    have k2 : o1.eta (N • z2) = 1 := o1.eta_ker z2
    rw [k1, _root_.mul_one] at e1
    rw [k2, _root_.mul_one] at e2
    exact e1.trans e2
  rw [ho', heta, ← hlvm, hg₀, ← hln, Category.assoc, ← hn]

end UpperTheory.Gal.FiniteEtaleModels.O
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem ev_eq {Λ Q : Type} [AddCommGroup Λ] [Group Q] (E : ℕ → Λ → Q)
    (add : ∀ n x y, E n (x + y) = E n x * E n y) (ker : ∀ n, 0 < n → ∀ x, E n x = 1 ↔ ∃ y, x = n • y)
    (tower : ∀ n m, 0 < n → 0 < m → ∀ x, E (n * m) x ^ m = E n x) {κ m N : ℕ} (hN : N = κ * m) (hκ : 0 < κ)
    (hm : 0 < m) {a b c : Λ} (h : a = b + κ • c) : E κ a = E N (m • b) := by
  have hz : ∀ n, E n 0 = 1 := by
    intro n
    have h0 := add n 0 0
    rw [_root_.add_zero] at h0
    exact (_root_.mul_eq_left.mp h0.symm)
  have hpow : ∀ n (k : ℕ) x, E n (k • x) = E n x ^ k := by
    intro n k x
    induction k with
    | zero => simp [hz]
    | succ k ih => rw [succ_nsmul, add, ih, _root_.pow_succ]
  have hc : E κ (κ • c) = 1 := (ker κ hκ _).mpr ⟨c, rfl⟩
  rw [h, add, hc, _root_.mul_one, hN, hpow, tower κ m hκ hm]

theorem UpperTheory.Gal.FiniteEtaleModels.trKer_holds :
    TrKer := by
  intro p _ D G L R _ _ gb h X s M₁ M₂ o' o ψ hT n κ c₁ hM hsurj f hf Ω _ _ z g hg hgk
  obtain ⟨hM3, hMc⟩ := M₁.2
  have hne : (M₁ : ℕ) ≠ 0 := by omega
  rw [hM] at hne hMc
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hκ0 : 0 < κ := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hc0 : 0 < c₁ := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hκc : κ.Coprime p := Nat.Coprime.coprime_dvd_left ⟨n * c₁, by ring⟩ hMc
  have hnκc : (n * κ).Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₁, rfl⟩ hMc
  obtain ⟨β, hβ⟩ := GlobalTheory.UPel.HT.GenCmp.exists_spMap (z ≫ s)
  obtain ⟨I', I'', h1, h2, hev⟩ := hT.2.2.2.2 Ω z β hβ
  obtain ⟨a, ha⟩ := (I'.onto κ hκ0 g).mp hgk
  have h0 : I''.ev κ 0 = 1 := (I''.ker κ hκ0 0).mpr ⟨0, by simp⟩
  have hψ : I'.ev κ a ≫ ψ = I''.ev κ 0 := by rw [ha, hg, h0]
  obtain ⟨v, hv, hav⟩ := (hev κ hκ0 hκc a 0).mp hψ
  have hin0 : inAf D 0 = 0 := by
    have := GlobalTheory.HeckeApprox.inAf_sub D 0 0
    rw [_root_.sub_zero, _root_.sub_self] at this
    exact this
  rw [hin0, _root_.zero_add] at hav
  have hinv : ∀ y, L.actG h⁻¹ (L.actG h y) = y := by
    intro y
    rw [← Module.End.mul_apply, ← map_mul, _root_.inv_mul_cancel, map_one, Module.End.one_apply]
  obtain ⟨x, w, hw, hvx⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D (n * κ) (Nat.mul_pos hn0 hκ0) hnκc v hv
  obtain ⟨w', hw', hfx⟩ := hf x
  obtain ⟨w'', hw'', hw''e⟩ := hsurj w hw
  have e2 : κ • L.actG h⁻¹ w = w'' := by rw [← map_nsmul, ← hw''e, hinv]
  have key : inAf D ((show D.La from a) - f x) = κ • (n • (w' + w'')) := by
    have e1 : inAf D a = L.actG h⁻¹ (κ • v) := by rw [← hav, hinv]
    rw [GlobalTheory.HeckeApprox.inAf_sub, e1, hvx, map_nsmul, map_add (f := _), map_nsmul, _root_.smul_add, hfx,
      smul_comm κ (n * κ), e2, smul_smul κ n, mul_comm κ n, _root_.smul_add]
    abel
  have hmem : n • (w' + w'') ∈ LaHat D := AddSubgroup.nsmul_mem _ (AddSubgroup.add_mem _ hw' hw'') n
  obtain ⟨y, hy⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ κ hκ0 hκc _ hmem key
  have hay : (show D.La from a) = f x + κ • y := by rw [← hy]; abel
  refine ⟨x, ?_⟩
  calc g = I'.ev κ a := ha.symm
    _ = I'.ev (M₁ : ℕ) ((n * c₁) • f x) :=
        ev_eq I'.ev I'.add I'.ker I'.tower (by rw [hM]; ring) hκ0 (Nat.mul_pos hn0 hc0) hay
    _ = I'.ev (M₁ : ℕ) (c₁ • n • f x) := by rw [smul_smul, mul_comm n c₁]
    _ = _ := (h1 _).symm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels
open GlobalTheory.UPel.HT.EtLev.HeckeLev

private theorem UpperTheory.Gal.FiniteEtaleModels.pow_one_of_killed_tr {p : ℕ} [Fact p.Prime] {D : Datum p} {S : Scheme.{0}} {A T : Over S}
    [GrpObj A] (act : OActN D.O A) {I : Ideal (𝓞 D.F)} {n : ℕ} (hn : (n : 𝓞 D.F) ∈ I) (t : T ⟶ A)
    (h : ∀ c ∈ I, t ≫ act.act (algebraMap (𝓞 D.F) D.O c) = 1) : t ^ n = 1 := by
  have := h _ hn
  rwa [map_natCast, act_natCast, MonObj.comp_pow, Category.comp_id] at this

theorem UpperTheory.Gal.FiniteEtaleModels.levTr_holds :
    LevTr := by
  intro q _ D R _ b f c k N 𝔟 hk hq S s o o' ψ lv hT hL
  obtain ⟨e, he⟩ := hq
  obtain ⟨hψ, hact, -, hgal, -, -⟩ := hT
  obtain ⟨hadd, hlin, hkill, hgeo⟩ := hL
  haveI := hψ
  have hnI : ((q ^ e : ℕ) : 𝓞 D.F) ∈ 𝔟 := he
  have hkn : k.Coprime (q ^ e) := Nat.Coprime.pow_right e hk
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hkn
    (pow_ne_zero e (Fact.out : q.Prime).ne_zero)
  have hmod : ∀ {Q : Type} [Monoid Q] (z : Q) (n j : ℕ), z ^ n = 1 → z ^ j = z ^ (j % n) := by
    intro Q _ z n j hz
    exact pow_eq_pow_mod j hz
  have hlv0 : lv 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  obtain ⟨φ, hφm, hψφ⟩ := GlobalTheory.HomDescent.exists_desc S o.A o'.A o.A (heckeSubA o f N) ψ hψ hgal
    (𝟙 o.A ^ k) (isMonHom_idPow o.A k) (fun h hh => by
      rw [MonObj.comp_pow, Category.comp_id]
      exact HeckeAd.pow_eq_one_of_mem o f h hh)
  haveI := hφm
  haveI : Epi ψ := by
    haveI := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact Over.epi_of_epi_left ψ
  have hφψ : φ ≫ ψ = 𝟙 o'.A ^ k := by
    apply (cancel_epi ψ).1
    rw [← Category.assoc, hψφ, pow_comp_hom, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have hφact : ∀ a : D.O, φ ≫ o.act.act a = o'.act.act a ≫ φ := by
    intro a
    haveI := o.act.hom a
    apply (cancel_epi ψ).1
    rw [← Category.assoc, hψφ, ← Category.assoc, ← hact a, Category.assoc, hψφ, pow_comp_hom,
      MonObj.comp_pow, Category.id_comp, Category.comp_id]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    beta_reduce
    rw [hadd, MonObj.mul_comp]
  · intro a x
    beta_reduce
    rw [hlin, Category.assoc, hact, Category.assoc]
  · intro x hx
    beta_reduce
    rw [hkill x hx, MonObj.one_comp]
  · intro K _ _ x
    obtain ⟨hA, hB⟩ := hgeo K x
    constructor
    · intro y hy
      beta_reduce at hy
      apply hA
      have hPk : (toUnit (Over.mk x) ≫ lv y) ^ k = 1 := by
        calc (toUnit (Over.mk x) ≫ lv y) ^ k = (toUnit (Over.mk x) ≫ lv y) ≫ 𝟙 o.A ^ k := by
              rw [MonObj.comp_pow, Category.comp_id]
          _ = (toUnit (Over.mk x) ≫ lv y ≫ ψ) ≫ φ := by rw [← hψφ]; simp only [Category.assoc]
          _ = 1 := by rw [hy, MonObj.one_comp]
      have hPn : (toUnit (Over.mk x) ≫ lv y) ^ (q ^ e) = 1 :=
        UpperTheory.Gal.FiniteEtaleModels.pow_one_of_killed_tr o.act hnI _ (fun c hc => by
          rw [Category.assoc, ← hlin,
            hkill _ (Submodule.subset_span ⟨c, by rw [pow_one]; exact hc, y, rfl⟩), MonObj.comp_one])
      calc toUnit (Over.mk x) ≫ lv y = (toUnit (Over.mk x) ≫ lv y) ^ 1 := (pow_one _).symm
        _ = (toUnit (Over.mk x) ≫ lv y) ^ (1 % q ^ e) := hmod _ _ 1 hPn
        _ = (toUnit (Over.mk x) ≫ lv y) ^ (k * m % q ^ e) := by rw [hm]
        _ = (toUnit (Over.mk x) ≫ lv y) ^ (k * m) := (hmod _ _ _ hPn).symm
        _ = 1 := by rw [pow_mul, hPk, one_pow]
    · intro g hg
      have hg0 : ∀ c ∈ 𝔟 ^ 1, (g ≫ φ) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
        intro c hc
        rw [Category.assoc, hφact, ← Category.assoc, hg c hc, MonObj.one_comp]
      obtain ⟨y0, hy0⟩ := hB (g ≫ φ) hg0
      have hgk : g ^ k = toUnit (Over.mk x) ≫ lv y0 ≫ ψ := by
        rw [← Category.assoc, hy0, Category.assoc, hφψ, MonObj.comp_pow, Category.comp_id]
      have hgn : g ^ (q ^ e) = 1 :=
        UpperTheory.Gal.FiniteEtaleModels.pow_one_of_killed_tr o'.act hnI g (fun c hc => hg c (by rw [pow_one]; exact hc))
      refine ⟨m • y0, ?_⟩
      show toUnit (Over.mk x) ≫ lv (m • y0) ≫ ψ = g
      rw [map_nsmul_pow lv hadd hlv0 m y0, pow_comp_hom, MonObj.comp_pow, ← hgk, ← pow_mul,
        hmod g _ _ hgn, hm, ← hmod g _ 1 hgn, pow_one]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels
open GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Hecke.Comp

theorem UpperTheory.Gal.FiniteEtaleModels.trSame_holds :
    TrSame := by
  intro q _ D R _ b f c k N S s o o₁ o₂ ψ₁ ψ₂ h₁ h₂
  obtain ⟨m₁, a₁, e₁, g₁, l₁, -⟩ := h₁
  obtain ⟨m₂, a₂, e₂, g₂, l₂, -⟩ := h₂
  have ep₁ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover g₁
  have ep₂ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover g₂
  have kill : ∀ {X : Over S} [GrpObj X] (ψ : o.A ⟶ X), IsMonHom ψ →
      GlobalTheory.ZM.IsGaloisCover (↥(heckeSubA o f N)) (fun h ↦ Over.Hom.left (transl h.1)) (Over.Hom.left ψ) →
      ∀ h ∈ heckeSubA o f N, h ≫ ψ = 1 := by
    intro X _ ψ hψ g h hh
    exact comp_eq_one_of_transl ψ h (g.inv ⟨h, hh⟩)
  obtain ⟨φ, hφ, hφc⟩ := GlobalTheory.HomDescent.exists_desc S o.A o₁.A o₂.A _ ψ₁ m₁ g₁ ψ₂ m₂ (kill ψ₂ m₂ g₂)
  obtain ⟨φ', hφ', hφ'c⟩ := GlobalTheory.HomDescent.exists_desc S o.A o₂.A o₁.A _ ψ₂ m₂ g₂ ψ₁ m₁ (kill ψ₁ m₁ g₁)
  have canc : ∀ {X Y : Over S} (π : X ⟶ Y) [Epi π.left] {Z : Over S} (u v : Y ⟶ Z), π ≫ u = π ≫ v → u = v := by
    intro X Y π _ Z u v h
    ext1
    rw [← cancel_epi π.left, ← Over.comp_left, h, Over.comp_left]
  let e : o₁.A ≅ o₂.A :=
    { hom := φ, inv := φ',
      hom_inv_id := canc ψ₁ _ _ (by rw [reassoc_of% hφc, hφ'c, Category.comp_id])
      inv_hom_id := canc ψ₂ _ _ (by rw [reassoc_of% hφ'c, hφc, Category.comp_id]) }
  haveI : IsMonHom e.hom := hφ
  haveI : IsMonHom ψ₁ := m₁
  haveI : IsMonHom ψ₂ := m₂
  have hc : ψ₁.left ≫ φ.left = ψ₂.left := by rw [← Over.comp_left, hφc]
  refine ⟨⟨φ.left, sq2 φ, isGrpPullback_of_iso e, ⟨grpSchemeSquareProductMap_fst φ, grpSchemeSquareProductMap_snd φ⟩, ?_, ?_, ?_⟩, hc⟩
  · intro a
    have t₁ := congrArg Over.Hom.left (a₁ a)
    have t₂ := congrArg Over.Hom.left (a₂ a)
    simp only [Over.comp_left] at t₁ t₂
    rw [← cancel_epi ψ₁.left, ← Category.assoc, ← t₁, Category.assoc, hc, reassoc_of% hc, ← t₂]
  · have hP := o₂.isLB
    have Z : ∀ (u : o₁.A.left ⟶ (G2 o₁.A).left) (v : o₂.A.left ⟶ (G2 o₂.A).left),
        u ≫ sq2 φ = φ.left ≫ v → (∃ t : (o₂.P.pull v).Gen, t.IsGen) →
        ∃ t : ((o₂.P.pull (sq2 φ)).pull u).Gen, t.IsGen := by
      intro u v huv hv
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _),
        GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp, huv,
        GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hP v (pull_isLB hP v),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 hv, map_zero]
    obtain ⟨l₁⟩ := l₁
    obtain ⟨l₂⟩ := l₂
    have lA := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb o.isLB (fun _ : Fin (k ^ 2 / c) ↦ 𝟙 _) (fun _ ↦ (1 : ℤ))
    have Y : LBIso (o₂.P.pull (sq2 ψ₂)) ((o₂.P.pull (sq2 φ)).pull (sq2 ψ₁)) := by
      rw [← GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _),
        GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP,
        ← GlobalTheory.CechPic.pull_comp, ← grpSchemeSquareProductMap_comp, hφc]
    refine GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny S o.A o₁.A _ ψ₁ o.ab o₁.ab m₁ g₁ o₁.P (o₂.P.pull (sq2 φ)) o₁.isLB
      (pull_isLB o₂.isLB _) o₁.rig₁ o₁.rig₂ ?_ ?_ ?_
    · exact Z _ _ (lift_one_id_grpSchemeSquareProductMap φ) o₂.rig₁
    · exact Z _ _ (lift_id_one_grpSchemeSquareProductMap φ) o₂.rig₂
    · exact LBIso.trans (pull_isLB o₁.isLB _) lA (pull_isLB (pull_isLB hP _) _) (LBIso.symm l₁)
        (LBIso.trans lA (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) l₂ Y)
  · intro y
    rw [e₁ y, e₂ y, Over.comp_left, Over.comp_left, Category.assoc, hc, Category.id_comp]
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
open GlobalTheory.UPel.HT.Hecke.PullHecke
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA mem_heckeSubA)

attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Gal.FiniteEtaleModels

theorem trPull : TrPull := by
  intro q _ D R _ b f c k N S S' s s' j o o' ψ o₁ o₁' m m' hT
  obtain ⟨hmon, hact, heta, hgal, ⟨hlb⟩, hck⟩ := hT
  have hc1 : m.φ ≫ o.A.hom = o₁.A.hom ≫ j := m.cart.1.w
  have hc2 : m'.φ ≫ o'.A.hom = o₁'.A.hom ≫ j := m'.cart.1.w
  have hψw : ψ.left ≫ o'.A.hom = o.A.hom := Over.w ψ
  let l : o₁.A.left ⟶ o₁'.A.left := m'.cart.1.lift (m.φ ≫ ψ.left) o₁.A.hom
    (by rw [Category.assoc, hψw, hc1])
  have hl1 : l ≫ m'.φ = m.φ ≫ ψ.left := m'.cart.1.lift_fst _ _ _
  have hl2 : l ≫ o₁'.A.hom = o₁.A.hom := m'.cart.1.lift_snd _ _ _
  let ψ₁ : o₁.A ⟶ o₁'.A := Over.homMk l hl2
  have hψ₁ : ψ₁.left = l := rfl
  have hext : ∀ {Z : Scheme} (u v : Z ⟶ o₁'.A.left), u ≫ m'.φ = v ≫ m'.φ →
      u ≫ o₁'.A.hom = v ≫ o₁'.A.hom → u = v := fun u v h1 h2 => m'.cart.1.hom_ext h1 h2
  have hl1' : ∀ {Z : Scheme} (u : Z ⟶ o₁.A.left), u ≫ l ≫ m'.φ = u ≫ m.φ ≫ ψ.left := by
    intro Z u
    rw [hl1]
  have hl2' : ∀ {Z : Scheme} (u : Z ⟶ o₁.A.left), u ≫ l ≫ o₁'.A.hom = u ≫ o₁.A.hom := by
    intro Z u
    rw [hl2]
  refine ⟨ψ₁, ⟨?_, ?_, ?_, ?_, ?_, hck⟩, hl1⟩
  · apply isMonHom_of_mul
    intro T x y
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hψ₁]
    apply hext
    · have h1 := m.cart.2 T x y (pushPt hc1 x) (pushPt hc1 y) rfl rfl
      have h2 := m'.cart.2 T (x ≫ ψ₁) (y ≫ ψ₁) (pushPt hc1 x ≫ ψ) (pushPt hc1 y ≫ ψ)
        (by simp only [Over.comp_left, hψ₁, Category.assoc, hl1]; rfl)
        (by simp only [Over.comp_left, hψ₁, Category.assoc, hl1]; rfl)
      rw [Category.assoc, hl1', ← h2, ← MonObj.mul_comp, Over.comp_left, h1, Category.assoc]
    · simp only [Category.assoc, hl2', Over.w]
  · intro a
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hψ₁]
    have hA : (o.act.act a).left ≫ ψ.left = ψ.left ≫ (o'.act.act a).left := by
      rw [← Over.comp_left, hact a, Over.comp_left]
    apply hext
    · rw [Category.assoc, hl1', ← Category.assoc, m.act a, Category.assoc, hA,
        Category.assoc, m'.act a, ← Category.assoc l, hl1, Category.assoc]
    · simp only [Category.assoc, hl2', Over.w, hl2]
  · intro x
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hψ₁]
    apply hext
    · rw [m'.eta x, heta x, Over.comp_left, Category.assoc, hl1', ← Category.assoc (o₁.eta (f x)).left,
        m.eta (f x), Category.assoc]
    · simp only [Category.assoc, hl2', Over.w]
  · have hkey : ∀ y : D.La, (transl (o₁.eta y)).left ≫ m.φ = m.φ ≫ (transl (o.eta y)).left := by
      intro y
      let e : Over.mk (o₁.A.hom ≫ j) ⟶ o.A := pushPt hc1 (𝟙 o₁.A)
      have he : e.left = m.φ := by simp [e, pushPt]
      have h1 := m.cart.2 o₁.A (𝟙 o₁.A) (toUnit o₁.A ≫ o₁.eta y) e (toUnit _ ≫ o.eta y) rfl
        (by simp [m.eta])
      have h2 : e ≫ transl (o.eta y) = e * (toUnit _ ≫ o.eta y) := by
        simp only [transl, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
      calc (transl (o₁.eta y)).left ≫ m.φ = (e * (toUnit _ ≫ o.eta y)).left := by unfold transl; exact h1.symm
        _ = (e ≫ transl (o.eta y)).left := by rw [h2]
        _ = m.φ ≫ (transl (o.eta y)).left := by rw [Over.comp_left, he]
    have hpb : IsPullback m.φ ψ₁.left ψ.left m'.φ :=
      IsPullback.of_bot (by rw [hψ₁, hl2, hψw]; exact m.cart.1) hl1.symm m'.cart.1
    refine isGaloisCover_of_isPullback hgal hpb ?_ ?_ ?_ ?_ ?_ ?_
    · show (transl (1 : 𝟙_ (Over S') ⟶ o₁.A)).left = _
      rw [transl_one]
      rfl
    · intro a a'
      simp only [Subgroup.coe_mul, transl_mul, Over.comp_left]
    · intro a a' h
      exact Subtype.ext (transl_injective h)
    · rintro ⟨h, x, rfl⟩
      simp only [hψ₁]
      apply hext
      · rw [Category.assoc, hl1', ← Category.assoc, hkey, Category.assoc,
          hgal.inv ⟨o.eta (N • f x), mem_heckeSubA o f N x⟩, hl1]
      · simp only [Category.assoc, hl2', Over.w, hl2]
    · rintro ⟨h, x, rfl⟩
      exact ⟨⟨o.eta (N • f x), mem_heckeSubA o f N x⟩, hkey _⟩
    · rintro ⟨h, x, rfl⟩
      exact ⟨⟨o₁.eta (N • f x), mem_heckeSubA o₁ f N x⟩, hkey _⟩
  · have hsq : sq2 ψ₁ ≫ m'.φ₂ = m.φ₂ ≫ sq2 ψ := by
      apply grpScheme_square_hom_ext
      · have e1 : m'.φ₂ ≫ (fst o'.A o'.A).left = (fst o₁'.A o₁'.A).left ≫ m'.φ := m'.sq.1
        have e2 : m.φ₂ ≫ (fst o.A o.A).left = (fst o₁.A o₁.A).left ≫ m.φ := m.sq.1
        calc (sq2 ψ₁ ≫ m'.φ₂) ≫ (fst o'.A o'.A).left
            = (sq2 ψ₁ ≫ (fst o₁'.A o₁'.A).left) ≫ m'.φ := by
              rw [Category.assoc, e1, Category.assoc]
          _ = (fst o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
              rw [grpSchemeSquareProductMap_comp_fst, Category.assoc, hψ₁, hl1]
          _ = (m.φ₂ ≫ (fst o.A o.A).left) ≫ ψ.left := by
              rw [e2, Category.assoc]
          _ = (m.φ₂ ≫ sq2 ψ) ≫ (fst o'.A o'.A).left := by
              rw [Category.assoc, Category.assoc, grpSchemeSquareProductMap_comp_fst]
      · have e1 : m'.φ₂ ≫ (snd o'.A o'.A).left = (snd o₁'.A o₁'.A).left ≫ m'.φ := m'.sq.2
        have e2 : m.φ₂ ≫ (snd o.A o.A).left = (snd o₁.A o₁.A).left ≫ m.φ := m.sq.2
        calc (sq2 ψ₁ ≫ m'.φ₂) ≫ (snd o'.A o'.A).left
            = (sq2 ψ₁ ≫ (snd o₁'.A o₁'.A).left) ≫ m'.φ := by
              rw [Category.assoc, e1, Category.assoc]
          _ = (snd o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
              rw [grpSchemeSquareProductMap_comp_snd, Category.assoc, hψ₁, hl1]
          _ = (m.φ₂ ≫ (snd o.A o.A).left) ≫ ψ.left := by
              rw [e2, Category.assoc]
          _ = (m.φ₂ ≫ sq2 ψ) ≫ (snd o'.A o'.A).left := by
              rw [Category.assoc, Category.assoc, grpSchemeSquareProductMap_comp_snd]
    have hL1 : (Hecke.lbPow o₁.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hL0 : (Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff hL1 (pull_isLB o₁'.isLB (sq2 ψ₁))).1 ?_⟩
    rw [cls_heckePow o₁.isLB, GlobalTheory.CechPic.cls_pull o₁'.isLB,
      (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol, GlobalTheory.CechPic.cls_pull o.isLB,
      (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol, GlobalTheory.CechPic.cls_pull o'.isLB,
      ← GlobalTheory.CechPic.pull_comp, hsq, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _),
      ← (GlobalTheory.CechPic.cls_eq_iff hL0 (pull_isLB o'.isLB (sq2 ψ))).2 hlb,
      cls_heckePow o.isLB, map_nsmul]

end UpperTheory.Gal.FiniteEtaleModels
end
end
