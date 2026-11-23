module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem seenShape_not_both {E : Type} [Field E] [NumberField E] {u : Plc E} {a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hne : a ≠ b) (h1 : (a : 𝓞 E) ∈ u.asIdeal) (h2 : (b : 𝓞 E) ∈ u.asIdeal) : False := by
  obtain ⟨c, d, e⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes ha hb).2 hne)
  have e' := congrArg (Int.cast : ℤ → 𝓞 E) e
  push_cast at e'
  refine u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

private theorem seenShape_nat_mem_cj {E : Type} [Field E] [NumberField E] [IsCMField E] {u : Plc E} {m : ℕ}
    (h : (m : 𝓞 E) ∈ u.asIdeal) : (m : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj u).asIdeal := by
  have e := (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)
  rw [e, Ideal.mem_comap, map_natCast]
  exact h

theorem UpperTheory.Gal.W2.Seed.pSeenShape :
    StabKer → SiteFact → CenFacts → LevBasic → UpperTheory.Gal.CertificateRingHomMap.LocComm → SeenShape := by
  intro hSK hSF hCF hLB hc E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq₀ r W haux N hrN hstab L hw Ty hty g θ hs
  have key : ∀ k, Stab F V k → k ∈ S.L.KN r → k ∈ Ty.kerK :=
    hSK E A n p S F x U w₀ Up V hodd hsc hgen hoff hq₀ r W haux N hrN hstab L hw Ty hty
  rcases hs with ⟨hd, hst, hr, hθ⟩ | ⟨w, σ, i, B, hfree, hqr, hK, ⟨hi, hgK, ⟨hws, t, z, ht, hz, hh⟩, -⟩, hB, hθ⟩
  · refine ⟨?_, Or.inl ⟨hd, key _ hst hr, hθ⟩⟩
    rw [hd.1]
    exact fun k hk => key k (hstab k hk) (KN_anti hrN hk)
  · have hqw : ((σ.q : ℕ) : 𝓞 E) ∈ w.asIdeal := σ.atp.le (Ideal.subset_span (Set.mem_insert _ _))
    have hpp : p.Prime := Fact.out
    have hpw : (p : 𝓞 E) ∉ w.asIdeal := fun h => seenShape_not_both σ.atp.prime hpp σ.atp.ne hqw h
    let w' : Spl E p := ⟨w, hws, hpw⟩
    have hrU : ∀ u ∈ W, (r : 𝓞 E) ∈ u.1.asIdeal := haux.half.above
    have hqU : ∀ u ∈ W, ((σ.q : ℕ) : 𝓞 E) ∉ u.1.asIdeal := fun u hu h =>
      seenShape_not_both σ.atp.prime haux.prime hqr h (hrU u hu)
    have hcen := hCF E A n hodd.pos x hgen σ.q σ.atp.prime σ.good.1 w hqw z hz
    have hap1 : ∀ u ∈ W, GlobalTheory.Cong.Apart w u.1 := fun u hu => ((hc E n u.1 u.2.1).2.1 w).2
      ⟨fun e => hqU u hu (e ▸ hqw), fun e => seenShape_not_both (u := w) σ.atp.prime haux.prime hqr hqw
        (e ▸ seenShape_nat_mem_cj (hrU u hu))⟩
    have hap2 : ∀ u ∈ W, GlobalTheory.Cong.Apart u.1 w := fun u hu => ((hc E n w hws).2.1 u.1).2
      ⟨fun e => hqU u hu (e ▸ hqw), fun e => hqU u hu (e ▸ seenShape_nat_mem_cj hqw)⟩
    have hσK : σ.K₀ ≤ S.L.KN r := by
      obtain ⟨-, h2, h3, -⟩ := hLB p S.D S.G S.L
      refine h2 _ _ _ _ σ.isLev (h3 r) (Ideal.mul_le_left.trans (Ideal.span_singleton_le_span_singleton.2 ?_))
      have hd : r ∣ ordCompl[σ.q] N.1 := Nat.dvd_ordCompl_of_dvd_not_dvd hrN fun h =>
        hqr ((Nat.prime_dvd_prime_iff_eq σ.atp.prime haux.prime).1 h)
      exact Nat.cast_dvd_cast hd
    have hzi : ∀ a, (z ^ i)⁻¹ * a = a * (z ^ i)⁻¹ := fun a =>
      ((Commute.pow_left (show Commute z a from hcen.1 a) i).inv_left).eq
    have hw0 : comp w₀ z = 1 := (hz w₀).2 (hfree.2.2.2.1 w₀ V.shape.mem)
    refine ⟨?_, Or.inr ⟨w', t, z, i, B, hfree, hap1, hi, ht, hz, hB, ?_, ?_, ?_, ?_, ?_, hθ⟩⟩
    · rw [hgK]
      exact fun k hk => key k (hK k hk) (hσK hk)
    · exact fun u hu => hcen.2 u fun h => seenShape_not_both σ.atp.prime hpp σ.atp.ne h hu
    · have e : (UpperTheory.Gal.CertificateRingHomMap.loc hws t * z ^ i)⁻¹ = UpperTheory.Gal.CertificateRingHomMap.loc hws t⁻¹ * (z ^ i)⁻¹ := by
        rw [_root_.mul_inv_rev, map_inv]
        exact hzi _
      rw [hh, (hty.fac w').2 t⁻¹, ← map_inv F.j, e, map_mul]
    · refine ⟨fun a => ?_, ?_⟩
      · obtain ⟨a', rfl⟩ := F.surj a
        rw [← map_mul, ← map_mul, hzi]
      · rw [hty.L_eq]
        refine ((hty.fac ⟨w₀, hw⟩).1 (z ^ i)⁻¹).trans ?_
        show comp w₀ (z ^ i)⁻¹ = 1
        rw [map_inv, map_pow, hw0, one_pow, inv_one]
    · intro u hu
      rw [hh, (hty.fac u).1, map_mul, map_pow, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hws (hap2 u hu),
        hcen.2 _ (hqU u hu), one_pow, one_mul]
    · rw [hgK]
      exact hSF E A n p S F x hgen N w' σ (L w') (hty.fac w')
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pCenFacts :
    Sides → CenFacts := by
  intro hS E _ _ _ A n _ x hx q hq hsp w hw z hz
  obtain ⟨-, -, -, h4, -⟩ := hS E A x hx q hq hsp w hw
  have hscal : ∀ (u : Plc E) (a : GL (Fin n) (u.adicCompletion E)), comp u z * a = a * comp u z := by
    intro u a
    by_cases h : UpperTheory.Gal.CertificateRingHomMap.SameK x (UpperTheory.Gal.CertificateRingHomMap.cj u) w
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, (hz u).1 h, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    · rw [(hz u).2 h, one_mul, mul_one]
  refine ⟨fun g => UpperTheory.Gal.CertificateRingHomMap.guf_ext ?_ fun u => ?_, fun u hu => ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_mul, map_mul, hscal]
  · refine (hz u).2 fun h => hu ?_
    have h' := h4 _ h
    have e : (UpperTheory.Gal.CertificateRingHomMap.cj u).asIdeal = _ :=
      (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)
    rw [e, Ideal.mem_comap, map_natCast] at h'
    exact h'
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LFun (KGL satEig heckeVec IsSatVecGL)

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Plc E}

private theorem tj_eq {ϖ : w.adicCompletion E} {i : ℕ} (t : GLw n w)
    (ht : t.val = Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ else 1) :
    Tj ℂ n (Ov E w) ϖ i = dosetInd ℂ (KGL w (n := n)) t := by
  unfold Tj dosetInd
  congr 1
  ext y
  rw [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨a, ha, b, hb, Units.ext ?_⟩
    rw [e, Units.val_mul, Units.val_mul, ht]
    rfl
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [Units.val_mul, Units.val_mul, ht]
    rfl

private theorem dos_invT (t : GLw n w) (h : invT n _ t⁻¹ = t) (a : GLw n w) :
    dosetInd ℂ (KGL w (n := n)) t (invT n _ a) = dosetInd ℂ (KGL w (n := n)) t⁻¹ a := by
  have h' : invT n _ t = t⁻¹ := by
    have := congrArg (invT n _) h
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT'] at this
    exact this.symm
  have key : invT n _ a ∈ DoubleCoset.doubleCoset t (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n)) ↔
      a ∈ DoubleCoset.doubleCoset t⁻¹ (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n)) := by
    rw [DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨k, hk, l, hl, e⟩
      refine ⟨_, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hk, _, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hl, ?_⟩
      have := congrArg (invT n _) e
      rwa [UpperTheory.Gal.CertificateRingHomMap.invT_invT', map_mul, map_mul, h'] at this
    · rintro ⟨k, hk, l, hl, rfl⟩
      exact ⟨_, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hk, _, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hl, by rw [map_mul, map_mul, h]⟩
  unfold dosetInd
  by_cases hm : a ∈ DoubleCoset.doubleCoset t⁻¹ (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n))
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (key.2 hm)]; rfl
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (key.1 h))]

private theorem dos_mul (t a k : GLw n w) (hk : k ∈ KGL w (n := n)) :
    dosetInd ℂ (KGL w (n := n)) t (a * k) = dosetInd ℂ (KGL w (n := n)) t a := by
  have key : a * k ∈ DoubleCoset.doubleCoset t (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n)) ↔
      a ∈ DoubleCoset.doubleCoset t (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n)) := by
    rw [DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨u, hu, l, hl, e⟩
      exact ⟨u, hu, l * k⁻¹, (KGL w (n := n)).mul_mem hl ((KGL w (n := n)).inv_mem hk), by
        rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
    · rintro ⟨u, hu, l, hl, rfl⟩
      exact ⟨u, hu, l * k, (KGL w (n := n)).mul_mem hl hk, by simp only [mul_assoc]⟩
  unfold dosetInd
  by_cases hm : a ∈ DoubleCoset.doubleCoset t (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n))
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (key.2 hm)]; rfl
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (key.1 h))]

private theorem finsum_invT {M : Type} [AddCommMonoid M] (F : GLw n w → M)
    (hF : ∀ a, ∀ k ∈ KGL w (n := n), F (a * k) = F a) :
    ∑ᶠ c : GLw n w ⧸ KGL w (n := n), F (invT n _ c.out) = ∑ᶠ c : GLw n w ⧸ KGL w (n := n), F c.out := by
  let f : GLw n w ⧸ KGL w (n := n) → GLw n w ⧸ KGL w (n := n) := fun c => QuotientGroup.mk (invT n _ c.out)
  have hf : Function.Involutive f := fun c => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w (n := n)) (invT n _ c.out)
    simp only [f]
    rw [hk, map_mul, UpperTheory.Gal.CertificateRingHomMap.invT_invT', QuotientGroup.mk_mul_of_mem _ (UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL k.2),
      QuotientGroup.out_eq']
  have hshift : ∀ c, F (invT n _ c.out) = F ((Function.Involutive.toPerm f hf c).out) := fun c => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w (n := n)) (invT n _ c.out)
    rw [Function.Involutive.coe_toPerm]
    simp only [f]
    rw [hk, hF _ _ k.2]
  rw [finsum_congr hshift]
  exact finsum_comp_equiv (Function.Involutive.toPerm f hf) (f := fun c => F c.out)

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.tEig_of_thLoc :
    UpperTheory.Gal.CertificateRingHomMap.ThLoc → TEig := by
  intro hT E _ _ _ n hn x U w₀ Up V w hw hF i hi t ht z hz B hB g
  obtain ⟨-, s2, -, s4⟩ := V.form.sat w hw hF.2.1 hF.2.2.1 B hB
  obtain ⟨ϖ, hϖ, htd⟩ := ht
  obtain ⟨hT1, hT2⟩ := hT E n
  have hcen := V.kap.cen w hF.2.2.2.1 hF.2.2.2.2 z hz
  have hpow : ∀ (j : ℕ) (G : GUf E n), V.Φ (G * z ^ j) = (((V.κ.val w : ℂˣ) : ℂ)⁻¹ ^ j) • V.Φ G := by
    intro j
    induction j with
    | zero => intro G; simp
    | succ j ih =>
      intro G
      rw [pow_succ, ← mul_assoc, hcen, ih, smul_smul, pow_succ, mul_comm]
  have hinv : invT n _ t⁻¹ = t := by
    apply Units.ext
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_val, inv_inv, htd, Matrix.diagonal_transpose]
  set G' : GUf E n := UpperTheory.Gal.CertificateRingHomMap.th g * z ^ i with hG'
  let Fn : GLw n w → Module.Dual ℂ V.W.Sp := fun a => dosetInd ℂ (KGL w (n := n)) t a • V.Φ (G' * UpperTheory.Gal.CertificateRingHomMap.loc hw a)
  have hFn : ∀ a, ∀ k ∈ KGL w (n := n), Fn (a * k) = Fn a := fun a k hk => by
    have h1 : V.Φ (G' * UpperTheory.Gal.CertificateRingHomMap.loc hw a * UpperTheory.Gal.CertificateRingHomMap.loc hw k) = V.Φ (G' * UpperTheory.Gal.CertificateRingHomMap.loc hw a) :=
      congrFun (GlobalTheory.LGrp.mem_fixed.1 s2 k hk) _
    simp only [Fn]
    rw [UpperTheory.Gal.W2.Seed.dos_mul _ _ _ hk, map_mul, ← mul_assoc, h1]
  have hterm : ∀ c : GLw n w ⧸ KGL w (n := n), dosetInd ℂ (KGL w (n := n)) t⁻¹ c.out •
      V.Φ (UpperTheory.Gal.CertificateRingHomMap.th (g * (z ^ i)⁻¹ * UpperTheory.Gal.CertificateRingHomMap.loc hw c.out)) = Fn (invT n _ c.out) := fun c => by
    simp only [Fn]
    rw [UpperTheory.Gal.W2.Seed.dos_invT t hinv, map_mul, map_mul, hT1, map_inv, map_pow, hT2 hn x w z hz, inv_pow, inv_inv]
  have hev := congrFun (s4 ϖ hϖ i hi) G'
  unfold heckeVec at hev
  rw [finsum_apply (GlobalTheory.LFun.finite_heckeVec (Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ i) _ V.Φ),
    UpperTheory.Gal.W2.Seed.tj_eq t htd] at hev
  rw [finsum_congr hterm, UpperTheory.Gal.W2.Seed.finsum_invT Fn hFn]
  refine Eq.trans hev ?_
  rw [Pi.smul_apply, hG', hpow, smul_smul]
  rfl
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem comp_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := congrArg (RingHom.mapMatrix (pLoc E u)) (mem_Sim.1 k.2)
  rw [map_mul] at h
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

theorem UpperTheory.Gal.W2.Seed.pCongConj :
    UpperTheory.Gal.CertificateRingHomMap.LocComm → CongConj := by
  intro _ E _ _ _ n N w g hs hc i k
  have hrel := comp_rel g w
  rw [hs, Units.val_one, map_one, map_one, one_smul] at hrel
  have hG : ((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ = ((comp w g)⁻¹).val := by
    calc ((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ
        = ((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ * ((comp w g).val * ((comp w g)⁻¹).val) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hrel, Matrix.one_mul]
  have hv := (conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.2
  have hent : conjLoc (GlobalTheory.SplitPts.conjE E) w (((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val - 1) i k) = (((comp w g)⁻¹).val - 1) k i := by
    rw [← hG]
    by_cases hik : i = k
    · subst hik; simp [Matrix.sub_apply]
    · simp [Matrix.sub_apply, Matrix.one_apply, hik, Ne.symm hik]
  calc Valued.v (((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val - 1) i k)
      = Valued.v (conjLoc (GlobalTheory.SplitPts.conjE E) w (((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val - 1) i k)) := (hv _).symm
    _ = Valued.v ((((comp w g)⁻¹).val - 1) k i) := by rw [hent]
    _ ≤ Valued.v (N : w.adicCompletion E) := hc k i
    _ = Valued.v (conjLoc (GlobalTheory.SplitPts.conjE E) w (N : (UpperTheory.Gal.CertificateRingHomMap.cj w).adicCompletion E)) := by
          rw [map_natCast (conjLoc (GlobalTheory.SplitPts.conjE E) w) N]
    _ = Valued.v (N : (UpperTheory.Gal.CertificateRingHomMap.cj w).adicCompletion E) := hv _
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem conv_eq_hAct {X : Type} [Group X] (K : Subgroup X) (f f' : X → ℂ) (g : X) :
    conv K f f' g = hAct K f (fun x => f' (x⁻¹ * g)) 1 := by
  simp only [conv, hAct, one_mul, smul_eq_mul]

private theorem conv_tf {X M : Type} [Group X] [Group M] (hA : TfAdm) (T : TyLev X M) (ψ : X → ℂ) (c : ℂ) (h h' : X)
    (hψ : T.Acts ψ c h) (hh' : T.L.pr h' = 1) :
    conv T.K₀ ψ (T.tf h') = c • conv T.K₀ (T.tf h) (T.tf h') := by
  funext g
  have hΦ : T.IsTy (fun x => T.tf h' (x⁻¹ * g)) := by
    intro k hk x
    have hk' : k⁻¹ ∈ T.K := T.K.inv_mem hk
    simp only [_root_.mul_inv_rev, mul_assoc]
    rw [((hA X M T h' hh').2 k⁻¹ hk' (x⁻¹ * g)).1, smul_eq_mul]
    congr 1
    have e : ∀ (p1 : T.L.pr k⁻¹ ∈ T.J) (p2 : T.L.pr k ∈ T.J),
        (⟨T.L.pr k⁻¹, p1⟩ : T.J) = (⟨T.L.pr k, p2⟩ : T.J)⁻¹ := fun p1 p2 =>
      Subtype.ext (map_inv _ _)
    rw [e _ (T.fact.2 k hk)]
    simp
  have key := congrFun (hψ.2.2 ℂ _ hΦ) 1
  rw [Pi.smul_apply, conv_eq_hAct, conv_eq_hAct, key, Pi.smul_apply]

theorem UpperTheory.Gal.W2.Seed.pActsConv :
    TfAdm → TfIdem → ActsConv := by
  intro hA hI X M _ _ T ψ c h hψ
  constructor
  · rw [conv_tf hA T ψ c h 1 hψ (map_one _), (hI X M T h hψ.2.1).2.1]
  · intro c' h' hh'
    have hlin : ∀ f : X → ℂ, conv T.K₀ ψ (c' • f) = c' • conv T.K₀ ψ f := by
      intro f
      funext g
      rw [Pi.smul_apply]
      unfold conv
      rw [smul_finsum]
      congr 1
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hlin, conv_tf hA T ψ c h h' hψ hh', smul_smul, mul_comm c' c]
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cong_conj_iff (hG : CongGrpEx) {E : Type} [Field E] [NumberField E] [IsCMField E] (n N : ℕ) (hN : 0 < N)
    (u : Plc E) (a : GLw n u) (ha : a ∈ GlobalTheory.LFun.KGL u (n := n)) (y : GLw n u) :
    (Cong1 N u (a * y * a⁻¹) ∧ Cong1 N u (a * y * a⁻¹)⁻¹) ↔ Cong1 N u y ∧ Cong1 N u y⁻¹ := by
  obtain ⟨K, hc, -, -, -, hn, -, -⟩ := hG E n N hN u
  rw [← hc, ← hc]
  exact hn a ha y

private theorem principalCongruence_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (N : ℕ) (u : Plc E) :
    Cong1 N u (1 : GLw n u) := by
  intro i k
  simp

theorem UpperTheory.Gal.W2.Seed.pKNFact :
    KNIff → FacEq → AtApart → CongGrpEx → CongConj → UpperTheory.Gal.W2.Seed.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocComm → KNFact := by
  intro hK _ _ hG hC _ hL E _ _ _ A n p _ S F w L hF q hq hgood hqw N hN K hKc
  have e : ∀ (u : Plc E) (g : GUf E n), GeneralLinearGroup.map (pLoc E u) (F.tr.a * mat g * F.tr.a⁻¹) =
      F.a u * comp u g * (F.a u)⁻¹ := by
    intro u g
    rw [F.a_tr]
    simp only [map_mul, map_inv]
    rfl
  have hCong : ∀ g : GUf E n, S.L.CongOne N (F.j g) ↔ ∀ u : Plc E, (p : 𝓞 E) ∉ u.asIdeal →
      Cong1 N u (F.a u * comp u g * (F.a u)⁻¹) := by
    intro g
    rw [F.j_tr, ((hK E A n p S F.tr g).2 N hN)]
    simp only [e]
  have einv : ∀ (u : Plc E) (g : GUf E n), F.a u * comp u g⁻¹ * (F.a u)⁻¹ = (F.a u * comp u g * (F.a u)⁻¹)⁻¹ := by
    intro u g
    rw [map_inv]
    group
  have hw := (hL E n w.1 w.2.1)
  have hcs : IsSplitAt (CertificateRingHomMap.cj w.1) := hw.2.2.2.1
  have hqc : (q : 𝓞 E) ∈ (CertificateRingHomMap.cj w.1).asIdeal := by
    by_contra hc
    haveI : Fact q.Prime := ⟨hq⟩
    have h1 : GlobalTheory.Cong.Apart w.1 (CertificateRingHomMap.cj w.1) := apart_of_not_mem (p := q) hc hqw
    exact (((hL E n (CertificateRingHomMap.cj w.1) hcs).2.1 w.1).1 h1).2 hw.2.2.2.2.1.symm
  have hcw := F.a_int w.1 q hq hgood hqw
  have hcc := F.a_int _ q hq hgood hqc
  have main : ∀ y : GLw n w.1, Cong1 N w.1 y → Cong1 N w.1 y⁻¹ → S.L.CongOne N (L.loc y) := by
    intro y h1 h2
    rw [hF.2, hCong]
    intro u _
    by_cases huw : u = w.1
    · subst huw
      rw [CertificateRingHomMap.comp_loc]
      exact ((cong_conj_iff hG n N hN _ _ hcw y).2 ⟨h1, h2⟩).1
    by_cases huc : u = CertificateRingHomMap.cj w.1
    · subst huc
      have c1 : Cong1 N (CertificateRingHomMap.cj w.1) (comp (CertificateRingHomMap.cj w.1) (CertificateRingHomMap.loc w.2.1 y)) :=
        hC E n N w.1 _ (CertificateRingHomMap.sim_loc _ _) (by rwa [CertificateRingHomMap.comp_loc])
      have c2 : Cong1 N (CertificateRingHomMap.cj w.1) (comp (CertificateRingHomMap.cj w.1) (CertificateRingHomMap.loc w.2.1 y))⁻¹ := by
        rw [← map_inv]
        exact hC E n N w.1 _ (by rw [map_inv, CertificateRingHomMap.sim_loc, inv_one]) (by rwa [map_inv, CertificateRingHomMap.comp_loc, inv_inv])
      exact ((cong_conj_iff hG n N hN _ _ hcc _).2 ⟨c1, c2⟩).1
    · rw [CertificateRingHomMap.comp_loc_of_apart w.2.1 (((hw.2.1 u).2 ⟨huw, huc⟩)) y]
      simpa using principalCongruence_one N u
  refine ⟨fun y hy => ?_, fun k hk => ?_⟩
  · obtain ⟨h1, h2⟩ := (hKc y).1 hy
    refine ⟨main y h1 h2, ?_⟩
    rw [← map_inv]
    exact main y⁻¹ h2 (by rwa [inv_inv])
  · obtain ⟨g, rfl⟩ := F.surj k
    rw [hF.1, hKc]
    have h1 := (hCong g).1 hk.1 w.1 w.2.2
    have h2 := (hCong g⁻¹).1 (by rw [map_inv]; exact hk.2) w.1 w.2.2
    rw [einv] at h2
    exact (cong_conj_iff hG n N hN _ _ hcw _).1 ⟨h1, h2⟩
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pPhiEx :
    PhiTy → SeenShape → SeenActs → TyFact → TfAct → TfCen → TEig → AtApart → FacEq → JEq → UpperTheory.Gal.W2.Seed.LocComm → PhiEx := by
  intro hTy hShape hActs hFact hTfAct hTfCen hTEig hAt hFac hJ hc E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok
  obtain ⟨h0, h1, h2, -⟩ := hTy E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok
  refine ⟨fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h)), h0, h1, ?_, ?_⟩
  · intro g hg
    have := h2 g hg
    rw [th_eq F]
    exact this
  · intro g θ hs
    obtain ⟨-, hcase⟩ := hShape E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok g θ hs
    have hA := hActs E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok g θ hs
    rcases hcase with ⟨hd, hk, rfl⟩ | ⟨w, t, z, i, B, hfree, hap, hi, hT, hz, hB, hzp, hh, hcen, -, hLf, rfl⟩
    · have h3 := (hA.2.1 hd hk).2.2 _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1
      rw [h3]
      funext a
      have h4 := hTfCen _ _ Ty 1 ⟨fun _ => by simp, map_one _⟩ _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1 a
      simp only [Pi.smul_apply, one_smul]
      rw [h4, mul_one]
    · obtain ⟨hLK, hLA⟩ := (hFact E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok).2.1 w
        hfree.2.1 hfree.2.2.1 hap
      have hAc := hA.2.2 _ (L w) _ t⁻¹ (F.j (z ^ i)⁻¹) hLK hLf hLA hcen hh
      have h3 := hAc.2.2 _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1
      have hsz : F.tr.sec (F.j (z ^ i)⁻¹) = (z ^ i)⁻¹ := by
        apply (hJ E A n p S F.tr.toAdT F.tr.μ F.tr.mu F.tr.a F.tr.j F.tr.j_mx).1
        intro u
        by_cases hu : (p : 𝓞 E) ∈ u.asIdeal
        · rw [F.tr.sec_p _ u hu]
          simp [hzp u hu]
        · exact (F.tr.j_eq _ _).1 (by rw [F.tr.j_sec, F.j_tr]) u hu
      have hsl : ∀ y, F.tr.sec ((L w).loc y) = CertificateRingHomMap.loc w.2.1 y := by
        intro y
        have hL : L w = fac F.tr hc w := (hFac E A n p S F hc w).2 _ (hok.fac w)
        rw [hL]
        exact (hAt E A n p S F.tr hc w.1 w.2.1 w.2.2).1 y
      rw [h3, hh]
      funext a
      have h4 := hTfAct _ _ _ Ty (L w) _ hLK hLA t⁻¹ (F.j (z ^ i)⁻¹) hcen _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1 a
      have h5 := hTEig E n hodd.pos x U w₀ Up V w.1 w.2.1 hfree i hi t hT z hz B hB (F.tr.sec a)
      simp only [Pi.smul_apply]
      rw [h4, mul_smul, ← h5]
      congr 1
      refine finsum_congr fun y => ?_
      simp only [map_mul, hsz, hsl]
end
