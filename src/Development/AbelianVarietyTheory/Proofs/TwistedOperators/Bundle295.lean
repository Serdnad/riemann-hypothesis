module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead.RevTab

open Classical Formalism.L2.SG.HidaSetting

theorem pairTable_of {M A : Type} [Ring A] (p : M → M → A) (Z sm : A → Prop) (hZ : ∀ c, Z c → sm c)
    (hadd : ∀ a b, sm a → sm b → sm (a + b)) {ρ k : ℕ} (e f : Fin ρ → M) (b b' : Fin k → M) (z : M) (u : A)
    (hu : sm (u - 1))
    (t1 : ∀ a c, Z (p (f a) (e c) - if a = c then 1 else 0)) (t2 : ∀ a j, Z (p (f a) (b j))) (t3 : ∀ a, Z (p (f a) z))
    (t4 : ∀ a c, Z (p (f a) (f c)))
    (t5 : ∀ i a, Z (p (b' i) (e a))) (t6 : ∀ i j, Z (p (b' i) (b j) - if i = j then u else 0)) (t7 : ∀ i, Z (p (b' i) z))
    (t8 : ∀ i a, Z (p (b' i) (f a)))
    (t9 : ∀ a, Z (p z (e a))) (t10 : ∀ j, Z (p z (b j))) (t11 : Z (p z z + 1)) (t12 : ∀ a, Z (p z (f a)))
    (t13 : ∀ a c, Z (p (e a) (e c))) (t14 : ∀ a j, Z (p (e a) (b j))) (t15 : ∀ a, Z (p (e a) z))
    (t16 : ∀ a c, Z (p (e a) (f c) - if a = c then 1 else 0)) :
    PairTable p sm e f b b' z := by
  refine ⟨fun a c => hZ _ (t1 a c), fun a j => hZ _ (t2 a j), fun a => hZ _ (t3 a), fun a c => hZ _ (t4 a c),
    fun i a => hZ _ (t5 i a), fun i j => ?_, fun i => hZ _ (t7 i), fun i a => hZ _ (t8 i a),
    fun a => hZ _ (t9 a), fun j => hZ _ (t10 j), hZ _ t11, fun a => hZ _ (t12 a),
    fun a c => hZ _ (t13 a c), fun a j => hZ _ (t14 a j), fun a => hZ _ (t15 a), fun a c => hZ _ (t16 a c)⟩
  have h := hZ _ (t6 i j)
  by_cases hij : i = j
  · simp only [hij, if_true] at h ⊢
    have := hadd _ _ h hu
    rwa [show p (b' j) (b j) - u + (u - 1) = p (b' j) (b j) - 1 by abel] at this
  · simpa only [hij, if_false] using h

variable {D : D7}

theorem smallAt_add {PP : Pl D.host.E} {a b : EAf D} (ha : SmallAt PP a) (hb : SmallAt PP b) : SmallAt PP (a + b) := by
  unfold SmallAt at *
  rw [RingHom.map_add (f := _)]
  exact Valuation.map_add_lt _ ha hb

theorem smallAt_of_mul {PP : Pl D.host.E} {g : ℕ} (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) {t : EAf D}
    (ht : t ∈ GlobalTheory.StdFrames.OA D) : SmallAt PP ((g : EAf D) * t) := by
  unfold SmallAt
  have hv : Valued.v (g : PP.adicCompletion D.host.E) < 1 := by
    have := (PP.valuation_lt_one_iff_mem (K := D.host.E) (g : 𝓞 D.host.E)).2 hg
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
    simpa using this
  rw [RingHom.map_mul, map_natCast, Valuation.map_mul]
  have h1 := (GlobalTheory.AdIsom.mem_OA t).1 ht PP
  calc Valued.v (g : PP.adicCompletion D.host.E) * Valued.v (GlobalTheory.StdFrames.cpt PP t)
      ≤ Valued.v (g : PP.adicCompletion D.host.E) * 1 := mul_le_mul_of_nonneg_left h1 zero_le'
    _ = Valued.v (g : PP.adicCompletion D.host.E) := mul_one _
    _ < 1 := hv

end GlobalTheory.SeeConjRead.RevTab

namespace GlobalTheory.SeeConjRead.RevTab

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf
open scoped TensorProduct

section Cong

variable {I : Formalism.MainNotions.S.AutInst} {g : ℕ}

theorem zmod_swap {x y : VA I} {d : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F} (h : ZMod' I g (hA I x y - d)) :
    ZMod' I g (hA I y x - sigA I d) := by
  have := unitaryCongruence.Z_sig I g h
  rwa [map_sub, ← unitaryCongruence.hA_symm] at this

theorem zmod_swap0 {x y : VA I} (h : ZMod' I g (hA I x y)) : ZMod' I g (hA I y x) := by
  have := unitaryCongruence.Z_sig I g h
  rwa [← unitaryCongruence.hA_symm] at this

theorem zmod_swap_delta {ρ : ℕ} {x y : VA I} {a c : Fin ρ} (h : ZMod' I g (hA I x y - if c = a then 1 else 0)) :
    ZMod' I g (hA I y x - if a = c then 1 else 0) := by
  have := zmod_swap h
  by_cases hac : a = c
  · subst hac
    simpa using this
  · simpa [hac, Ne.symm hac] using this

theorem zmod_diag {k : ℕ} {bw bwd : Fin k → VA I} {ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F}
    (hD : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0)) (i j : Fin k) :
    ZMod' I g (hA I (bw (Fin.rev i)) (bwd (Fin.rev j)) - if i = j then sigA I ew else 0) := by
  have := zmod_swap (hD (Fin.rev j) (Fin.rev i))
  by_cases hij : i = j
  · subst hij
    simpa using this
  · have h2 : ¬ Fin.rev j = Fin.rev i := fun h => hij (Fin.rev_injective h).symm
    simpa [hij, h2] using this

end Cong

variable {D : D7}

theorem smallAt_sg_sub_one {PP : Pl D.host.E} {g : ℕ} (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) {ew : EAf D}
    (hc0 : ∃ t ∈ GlobalTheory.StdFrames.OA D, 1 - ew - GlobalTheory.StdFrames.sg D ew = (g : EAf D) * t) (hid : ew * ew = ew)
    (hne : GlobalTheory.StdFrames.cpt PP ew ≠ 1) : SmallAt PP (GlobalTheory.StdFrames.sg D ew - 1) := by
  have h0 : GlobalTheory.StdFrames.cpt PP ew = 0 := by
    have h1 := congrArg (GlobalTheory.StdFrames.cpt PP) hid
    rw [map_mul] at h1
    have h2 : GlobalTheory.StdFrames.cpt PP ew * (GlobalTheory.StdFrames.cpt PP ew - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne
  obtain ⟨t, ht, hc⟩ := hc0
  have hs := smallAt_of_mul hg ht
  rw [← hc] at hs
  have e1 : GlobalTheory.StdFrames.sg D ew - 1 = -(1 - ew - GlobalTheory.StdFrames.sg D ew) - ew := by ring
  unfold SmallAt at *
  rw [e1, map_sub, map_neg, h0, sub_zero, Valuation.map_neg]
  exact hs

end GlobalTheory.SeeConjRead.RevTab

namespace GlobalTheory.SeeConjRead

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf RevTab

theorem pairTable_rev : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) ≠ 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (fun i => bwdT X h (Fin.rev i)) (fun i => bwT X h (Fin.rev i)) (z0T X h) := by
  intro D X h PP hg hne
  have hc0 : ZMod' X.B.I X.B.g (1 - X.ew - sigA X.B.I X.ew) := by
    have hz := X.vectorsInLattice.2.1
    have h2 : ZMod' X.B.I X.B.g (hA X.B.I X.z0 ((1 - X.ew - sigA X.B.I X.ew) • X.z0)) :=
      unitaryCongruence.mL_Qs X.B.I X.B.g hz (X.ew_full _ hz)
    rw [unitaryCongruence.hA_smul_right] at h2
    have hint : (1 - X.ew - sigA X.B.I X.ew) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
      sub_mem (sub_mem (one_mem _) X.ew_int) (unitaryCongruence.sigA_mem _ X.ew_int)
    have h4 := unitaryCongruence.Z_sub X.B.I X.B.g (unitaryCongruence.Z_smul X.B.I X.B.g hint X.formsAtZero.1) h2
    rwa [show (1 - X.ew - sigA X.B.I X.ew) * (hA X.B.I X.z0 X.z0 + 1) -
      (1 - X.ew - sigA X.B.I X.ew) * hA X.B.I X.z0 X.z0 = 1 - X.ew - sigA X.B.I X.ew by ring] at h4
  have hG := X.gramIntegral
  have hZ := X.formsAtZero
  have hW := X.weightVectorsIntegral
  have hD := X.bw_dual
  have hgq := X.g_eq
  have hid := X.ew_idem
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h hc0 hG hZ hW hD hgq hid hne ⊢
  subst h
  subst hgq
  refine pairTable_of (hY D) (ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1)) (SmallAt PP)
    (fun c ⟨t, ht, hc⟩ => hc ▸ smallAt_of_mul hg ht) (fun a b => smallAt_add) _ _ _ _ _ _
    (smallAt_sg_sub_one hg hc0 hid hne)
    (fun a c => zmod_swap_delta (hG c a).2.2) (fun a j => ((hW (Fin.rev j)).2.2 a).2.2.2) (fun a => (hZ.2 a).2)
    (fun a c => (hG a c).2.1)
    (fun i a => zmod_swap0 ((hW (Fin.rev i)).2.2 a).1) (fun i j => zmod_diag hD i j)
    (fun i => zmod_swap0 (hW (Fin.rev i)).1) (fun i a => zmod_swap0 ((hW (Fin.rev i)).2.2 a).2.1)
    (fun a => zmod_swap0 (hZ.2 a).1) (fun j => (hW (Fin.rev j)).2.1) hZ.1 (fun a => zmod_swap0 (hZ.2 a).2)
    (fun a c => (hG a c).1) (fun a j => ((hW (Fin.rev j)).2.2 a).2.2.1) (fun a => (hZ.2 a).1)
    (fun a c => (hG a c).2.2)

end GlobalTheory.SeeConjRead
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

open scoped Pointwise

namespace GlobalTheory.SeeConjZMod

theorem dvd_of_mem_primes {A : Type} [CommRing A] [IsDedekindDomain A] {x b : A} (hx : x ≠ 0)
    (h : ∀ P : HeightOneSpectrum A, x ∈ P.asIdeal → x ∉ P.asIdeal ^ 2 ∧ b ∈ P.asIdeal) : x ∣ b := by
  have hI : Ideal.span {x} ≠ ⊥ := by simpa using hx
  have hsq : Squarefree (Ideal.span {x}) := by
    rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hI]
    intro p hp hd
    have hpr : Prime p := hp.prime
    let P : HeightOneSpectrum A := ⟨p, Ideal.isPrime_of_prime hpr, hpr.ne_zero⟩
    have h2 : x ∈ p ^ 2 := by
      rw [sq, ← Ideal.dvd_span_singleton]; exact hd
    exact (h P (Ideal.pow_le_self two_ne_zero h2)).1 h2
  have hrad : (Ideal.span {x}).IsRadical := by
    intro y ⟨n, hn⟩
    rw [← Ideal.dvd_span_singleton] at hn ⊢
    rw [← Ideal.span_singleton_pow] at hn
    exact hsq.isRadical n _ hn
  rw [← Ideal.mem_span_singleton]
  apply hrad
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro J ⟨hJ, hp⟩
  exact (h ⟨J, hp, fun h0 => hI (le_bot_iff.1 (h0 ▸ hJ))⟩ (hJ (Ideal.mem_span_singleton_self x))).2

theorem conj_of_isConj {D : D7} {P P' : Pl D.host.E} (hc : Formalism.L2.DIV.IsConjPl P P') :
    GlobalTheory.Mem.Chr.ConjPl D.host.conj.toRingEquiv P P' := by
  have hle : D.host.conj • P.asIdeal ≤ P'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    exact (hc _ y ((GlobalTheory.TypePlaces.star_eq_conj D _).trans (D.host.conj.apply_symm_apply (y : D.host.E))).symm).1 hy
  have hmax : (D.host.conj • P.asIdeal).IsMaximal := by
    have := P.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => P.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  exact (GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj P P').2 (hmax.eq_of_le P'.isPrime.ne_top hle)

theorem g_coprime (D : D7) :
    IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
  Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)

theorem g_not_mem_sq (D : D7) (P : Pl D.host.E) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 := by
  intro h
  rw [Nat.cast_mul] at h
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 :=
    fun k hk => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) P hk).2.1
  have hno : ¬ (((D.host.g 0 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) := by
    rintro ⟨h0, h1⟩
    obtain ⟨a, b, hab⟩ := g_coprime D
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact add_mem (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)
  have hP := P.isPrime
  rcases P.isPrime.mem_or_mem (Ideal.pow_le_self two_ne_zero h) with h0 | h1
  · rcases Ideal.IsPrime.mul_mem_pow P.asIdeal (mul_comm (_ : 𝓞 D.host.E) _ ▸ h) with h' | h'
    · exact hno ⟨h0, h'⟩
    · exact key 0 h0 h'
  · rcases Ideal.IsPrime.mul_mem_pow P.asIdeal h with h' | h'
    · exact hno ⟨h', h1⟩
    · exact key 1 h1 h'

theorem exists_eq_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}
    (hm : m ≠ 0) (hsq : ∀ P : Pl E, ((m : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (s : Formalism.L2.Herm.intAf F E)
    (h : ∀ P : Pl E, ((m : ℕ) : 𝓞 E) ∈ P.asIdeal → resS F P s = 0) :
    ∃ t : Formalism.L2.Herm.intAf F E, s = (m : ℕ) * t := by
  have hm0 : ((m : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hm
  obtain ⟨q, hq⟩ := cmpS_surj (F := F) (Ideal.span {((m : ℕ) : 𝓞 E)}) (by simpa using hm0)
    (Ideal.Quotient.mk _ s)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hb : oToS F E b - s ∈ idS F (Ideal.span {((m : ℕ) : 𝓞 E)}) :=
    Ideal.Quotient.eq.1 hq
  rw [idS, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton] at hb
  obtain ⟨u, hu⟩ := hb
  have hd : ((m : ℕ) : 𝓞 E) ∣ b := by
    refine dvd_of_mem_primes hm0 fun P hP => ⟨hsq P, ?_⟩
    have e := congrArg (resS F P) hu
    rw [map_sub, h P hP, sub_zero, resS_oToS, map_mul, map_natCast] at e
    have e0 : ((m : ℕ) : kP P) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hP
    rw [e0, zero_mul] at e
    exact Ideal.Quotient.eq_zero_iff_mem.1 e
  obtain ⟨w, rfl⟩ := hd
  refine ⟨oToS F E w - u, ?_⟩
  rw [map_mul, map_natCast] at hu
  linear_combination -hu

theorem div_or_conj {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (P : Pl D.host.E)
    (hP : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ k, Pb.Div k P ∨ Pb.Div k (Formalism.L2.DIV.conjPl P) := by
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → Pb.Div k P ∨ Pb.Div k (Formalism.L2.DIV.conjPl P) := by
    intro k hk
    have h := ((GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) P
      hk).2.2.2 (Pb.pb k) (Pb.pb_over k) _ (conj_of_isConj (Formalism.L2.DIV.isConjPl_conjPl P))).2
    by_contra hn
    rw [not_or] at hn
    exact hn.1 (h.2 hn.2)
  rw [Nat.cast_mul] at hP
  exact (P.isPrime.mem_or_mem hP).elim (fun h => ⟨0, key 0 h⟩) (fun h => ⟨1, key 1 h⟩)

theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → (∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ ∀ (c : EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc' : sigA (II D) c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ R.Pg, resS D.host.F PP ⟨c, hc⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) c, hc'⟩ = 0) → ZMod' (II D) (D.host.g 0 * D.host.g 1) c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hIs _
  have hPg : ∀ PP, PP ∈ R.Pg ↔ ∃ k, R.C.P.Div k PP := hIs.Pg
  refine ⟨fun PP hPP => ?_, fun c hc hc' h => ?_⟩
  · obtain ⟨k, hk⟩ := (hPg PP).1 hPP
    have ho : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := R.C.P.overP hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ ho
    · exact Ideal.mul_mem_left _ _ ho
  · obtain ⟨t, ht⟩ := exists_eq_mul (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
      (g_not_mem_sq D) ⟨c, hc⟩ fun P hP => by
        obtain ⟨k, hk | hk⟩ := div_or_conj R.C.P P hP
        · exact (h P ((hPg P).2 ⟨k, hk⟩)).1
        · exact (resS_sigS_eq_zero_iff (II D).cm (Formalism.L2.DIV.isConjPl_conjPl P) ⟨c, hc⟩).1
            (h _ ((hPg _).2 ⟨k, hk⟩)).2
    refine ⟨t.1, t.2, ?_⟩
    have e := congrArg Subtype.val ht
    rw [Subring.coe_mul, Subring.coe_natCast] at e
    exact e

end GlobalTheory.SeeConjZMod
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.SelfDualGlue

variable {D : D7} {u : D.what₂.Word} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V}

theorem vA_flat (x : X.V) (a : D.host.E) : vA Y (ι x + a • z) = mA Y X ι *ᵥ vA X x + inc D a • vA Y z := by
  rw [vA_add, vA_smul, mA_mulVec_vA]

theorem inc_hD_flat (h : IsLine Y X ι z u) (x x' : X.V) (a a' : D.host.E) :
    inc D (Y.hD (ι x + a • z) (ι x' + a' • z)) =
      hA X (vA X x) (vA X x') - inc D a * cjA D (inc D a') * inc D (Tu D u) := by
  rw [← hA_vA, vA_flat, vA_flat]
  exact hA_flat h _ _ _ _

theorem mem_glueLat_iff {L₀ : Lat X} {x₀ : X.V} (y : Y.V) : y ∈ glueLat Y X ι z u L₀ x₀ ↔
    ∃ x : X.V, Formalism.L2.Herm.crd X x ∈ L₀ ∧ ∃ a : 𝓞 D.host.E,
      y = ι (x + (a : D.host.E) • x₀) + ((a : D.host.E) * (Tu D u)⁻¹) • z := by
  rw [mem_glueLat]
  refine exists_congr fun x => and_congr_right fun _ => exists_congr fun a => ?_
  rw [map_add (f := _), map_smul, smul_add, smul_smul]
  constructor <;> rintro rfl <;> abel

theorem coords_of_mem (h : IsLine Y X ι z u) {L₀ : Lat X} {x₀ x : X.V} {a : D.host.E}
    (hm : ι x + a • z ∈ glueLat Y X ι z u L₀ x₀) :
    ∃ x₁ ∈ hat L₀, ∃ b ∈ OA D, vA X x = x₁ + b • vA X x₀ ∧ inc D a = b * inc D (Tu D u)⁻¹ := by
  have hv := vA_mem_hat Y hm
  rw [vA_flat, mem_hat_glueLat] at hv
  obtain ⟨x₁, hx₁, b, hb, e⟩ := hv
  obtain ⟨e1, e2⟩ := flat_inj h e
  exact ⟨x₁, hx₁, b, hb, e1, e2⟩

theorem mem_flatSp (x : X.V) (a : D.host.E) : ι x + a • z ∈ flatSp Y X ι z := Submodule.add_mem_sup (LinearMap.mem_range_self ι x)
    (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self z))



theorem isGlueVec_of_isSDIn : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) → IsPrim Y z (glueLat Y X ι z u L₀ x₀) → IsGlueVec X u L₀ (vA X x₀) := by
  intro D u Y X ι z h L₀ x₀ hlat hSD hP
  obtain ⟨-, -, hsd⟩ := hSD

  have key : ∀ (p : X.V) (α : D.host.E) (q : X.V) (β : D.host.E),
      ι p + α • z ∈ glueLat Y X ι z u L₀ x₀ → ι q + β • z ∈ glueLat Y X ι z u L₀ x₀ →
      hA X (vA X p) (vA X q) - inc D α * cjA D (inc D β) * inc D (Tu D u) ∈ OA D := by
    intro p α q β hp hq
    rw [← inc_hD_flat h, inc_mem_iff]
    exact (hsd _ (mem_flatSp (ι := ι) (z := z) q β)).1 hq _ hp

  have hX : ∀ p : X.V, Formalism.L2.Herm.crd X p ∈ L₀ → ι p + (0 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
    intro p hp
    rw [mem_glueLat_iff]
    exact ⟨p, hp, 0, by simp⟩
  have hg : ι x₀ + (Tu D u)⁻¹ • z ∈ glueLat Y X ι z u L₀ x₀ := by
    rw [mem_glueLat_iff]
    exact ⟨0, by simp, 1, by simp⟩
  have hv : ∀ y : Fin X.rank → D.host.E,
      (fun i => inc D (y i)) = vA X ((Formalism.L2.Herm.crd X).symm y) := by
    intro y
    funext i
    simp [vA]
  have hrat : ∀ p q : X.V, Formalism.L2.Herm.crd X p ∈ L₀ → Formalism.L2.Herm.crd X q ∈ L₀ →
      hA X (vA X p) (vA X q) ∈ OA D := by
    intro p q hp hq
    simpa using key p 0 q 0 (hX p hp) (hX q hq)

  have hright : ∀ f, (∀ y ∈ L₀, hA X f (fun i => inc D (y i)) ∈ OA D) →
      ∀ y ∈ hat L₀, hA X f y ∈ OA D := by
    intro f hf y hy
    refine hat_induction (p := fun y => hA X f y ∈ OA D) hf ?_ ?_ ?_ hy
    · show hA X f 0 ∈ OA D
      rw [hA_zero_right]
      exact zero_mem _
    · intro a b ha hb
      show hA X f (a + b) ∈ OA D
      rw [hA_add_right]
      exact add_mem ha hb
    · intro a ha b hb
      show hA X f (a • b) ∈ OA D
      rw [hA_smul_right]
      exact mul_mem (cjA_mem ha) hb
  have hint : ∀ x ∈ hat L₀, ∀ y ∈ hat L₀, hA X x y ∈ OA D := by
    intro x hx
    refine hright x fun y hy => hA_mem_of_forall (fun x' hx' => ?_) x hx
    rw [hv x', hv y]
    exact hrat _ _ (by simpa using hx') (by simpa using hy)

  have hz : ι 0 + (1 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
    rw [map_zero, zero_add]
    exact (hP 1).2 (one_mem _)
  obtain ⟨x₁, hx₁, b, -, e1, e2⟩ := coords_of_mem h hz
  have hb : b = inc D (Tu D u) := by
    rw [map_one] at e2
    calc b = b * (inc D (Tu D u)⁻¹ * inc D (Tu D u)) := by rw [inc_inv_mul, mul_one]
      _ = inc D (Tu D u) := by rw [← mul_assoc, ← e2, one_mul]
  have h0 : vA X (0 : X.V) = 0 := by simpa using vA_add X (0 : X.V) 0
  refine ⟨?_, hint, ?_, ?_, ?_⟩
  · rw [h0] at e1
    rw [← hb, eq_sub_of_add_eq' e1.symm]
    exact sub_mem_hat zero_mem_hat hx₁
  · refine hright (vA X x₀) fun y hy => ?_
    rw [hv y]
    simpa using key x₀ (Tu D u)⁻¹ _ 0 hg (hX _ (by simpa using hy))
  · have := key x₀ (Tu D u)⁻¹ x₀ (Tu D u)⁻¹ hg hg
    rwa [cjA_inc_inv, mul_assoc, inc_inv_mul, mul_one] at this
  ·

    intro y hy
    obtain ⟨y₀, hy₀⟩ := exists_sub_inc_mem_hat hlat.span_eq_top y
    obtain ⟨q, rfl⟩ := (Formalism.L2.Herm.crd X).surjective y₀
    change y - vA X q ∈ hat L₀ at hy₀
    have hq : ι q + X.hD q x₀ • z ∈ glueLat Y X ι z u L₀ x₀ := by
      refine (hsd _ (mem_flatSp (ι := ι) (z := z) q (X.hD q x₀))).2 fun v hv' => ?_
      obtain ⟨p, hp, a, rfl⟩ := (mem_glueLat_iff v).1 hv'
      have hp' : vA X p ∈ hat L₀ := inc_mem_hat hp
      have h1 : hA X (vA X p) (vA X q) ∈ OA D := by
        rw [show vA X q = y - (y - vA X q) from (sub_sub_cancel y (vA X q)).symm, hA_sub_right]
        exact sub_mem (hy _ hp') (hint _ hp' _ hy₀)
      rw [← inc_mem_iff, inc_hD_flat h, ← hA_vA X q x₀, cjA_hA, vA_add, vA_smul, hA_add_left,
        hA_smul_left, map_mul (inc D)]
      convert h1 using 1
      linear_combination (-(inc D (a : D.host.E) * hA X (vA X x₀) (vA X q))) * inc_inv_mul u
    obtain ⟨x₂, hx₂, c, hc, e3, -⟩ := coords_of_mem h hq
    refine ⟨c, hc, ?_⟩
    have e4 : y - c • vA X x₀ = (y - vA X q) + x₂ := by
      rw [e3]
      abel
    rw [e4]
    exact add_mem_hat hy₀ hx₂

end GlobalTheory.AdIsom.SelfDualGlue
end
