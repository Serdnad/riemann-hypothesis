module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle348
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

theorem rhoT_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (t x : GL (Fin n) (AfE F E)) (hx : rhoP F P x = 1) : rhoT F P t x = 1 := by
  show rhoP F P (MulAut.conj t⁻¹ x) = 1
  rw [MulAut.conj_apply, map_mul, map_mul, hx, mul_one, ← map_mul, mul_inv_cancel, map_one]

theorem topChi_finite_order_and_trivial : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (n : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 E))) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1), ((∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ g, (Θ P).lam g ^ m = 1) → ∃ m : ℕ, 0 < m ∧ ∀ x, topChi σ U t Θ d hd N hdN hΘ x ^ m = 1) ∧ ∀ x : topU U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → topChi σ U t Θ d hd N hdN hΘ x = 1 := by
  intro F E K _ _ _ _ _ _ _ n Q σ U t Θ d hd N hdN hΘ
  letI : IsOneApply (topU U t Θ d →* ℂˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply (topU U t Θ d →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
  constructor
  · intro h
    choose m hm0 hm using h
    refine ⟨∏ P : Q, m P, Finset.prod_pos fun P _ => hm0 P, fun x => ?_⟩
    unfold topChi
    rw [MonoidHom.inv_apply, inv_pow, prod_apply, ← Finset.prod_pow, Finset.prod_eq_one, inv_one]
    intro P _
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ P)
    rw [hc, pow_mul, MonoidHom.comp_apply, ← map_pow, MonoidHom.comp_apply]
    have e : locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) (((rhoT F P.1 t).comp (topU U t Θ d).subtype).codRestrict _ (fun x => rhoT_mem x.2 P) x) ^ m P = 1 :=
      hm P _
    rw [e, map_one, one_pow]
  · intro x hx
    unfold topChi
    rw [MonoidHom.inv_apply, prod_apply, Finset.prod_eq_one, inv_one]
    intro P _
    have e : ((rhoT F P.1 t).comp (topU U t Θ d).subtype).codRestrict _ (fun x => rhoT_mem x.2 P) x = 1 :=
      Subtype.ext (rhoT_eq_one P.1 t x.1 (hx P))
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, map_one, map_one]

end GlobalTheory.Mem.Col2.TopCh

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct Topology

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
attribute [local instance] rlt_top rlt_topRing

namespace GlobalTheory.Mem.Col2.TopCh

section Nhd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_nhds (P : HeightOneSpectrum (𝓞 E)) {c : E} (hc : c ≠ 0) :
    ∀ᶠ y in 𝓝 (0 : AfE F E), ∃ z ∈ P.adicCompletionIntegers E, adAt F P y = algebraMap E (P.adicCompletion E) c * z := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
  have hb0 : algebraMap (𝓞 E) E b ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hb
  have ha0 : algebraMap (𝓞 E) E a ≠ 0 := fun h => hc (by rw [h, zero_div])
  set A : AfE F E := inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) with hA
  set B : AfE F E := inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a)⁻¹ with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← map_mul, mul_inv_cancel₀ ha0, map_one]
  have hop : IsOpen ((fun y : AfE F E => B * y) ⁻¹' (Formalism.L2.Herm.intAf F E : Set (AfE F E))) :=
    rlt_isOpen_intAf.preimage (continuous_const.mul continuous_id)
  have h0 : (0 : AfE F E) ∈ (fun y : AfE F E => B * y) ⁻¹' (Formalism.L2.Herm.intAf F E : Set (AfE F E)) := by
    simp
  filter_upwards [hop.mem_nhds h0] with y hy
  have hw : ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (afIso F E (B * y) Q) ≤ 1 := (mem_rInt_iff F E (B * y)).1 hy
  have hy' : y = A * (B * y) := by rw [← mul_assoc, hAB, one_mul]
  refine ⟨algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E b) * adAt F P (B * y), ?_, ?_⟩
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [map_mul]
    exact mul_le_one' (by rw [valued_algebraMap]; exact P.valuation_le_one b) (by rw [adAt_apply]; exact hw P)
  · have e : adAt F P y = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E a) * adAt F P (B * y) := by
      conv_lhs => rw [hy', map_mul, hA, adAt_inclE]
    rw [e, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hb0]

variable {n : ℕ}

theorem bc_adAt_sub (P : HeightOneSpectrum (𝓞 E)) (w : GL (Fin n) (AfE F E)) (i j : Fin n) :
    ((rhoP F P w : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j -
      (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j =
    adAt F P ((w : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  have e : ((rhoP F P w : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j =
      adAt F P ((w : Matrix (Fin n) (Fin n) (AfE F E)) i j) := rfl
  rw [e, map_sub, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem int_of_sub {P : HeightOneSpectrum (𝓞 E)} {A : Matrix (Fin n) (Fin n) (P.adicCompletion E)}
    (h : ∀ i j, A i j - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j ∈ P.adicCompletionIntegers E) : qbInt A := fun i j => by
  have := Subring.add_mem _ (h i j) (qbInt_one (v := P) (F := E) (n := n) i j)
  simpa using this

theorem eventually_localComponent_mem (P : HeightOneSpectrum (𝓞 E)) {c : E} (hc : c ≠ 0) :
    ∀ᶠ u : GL (Fin n) (AfE F E) in 𝓝 1, rhoP F P u ∈ qbK (algebraMap E (P.adicCompletion E) c) := by
  have hval : ∀ (c' : E), c' ≠ 0 → ∀ i j : Fin n, ∀ᶠ u : GL (Fin n) (AfE F E) in 𝓝 1, ∃ z ∈ P.adicCompletionIntegers E,
      adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E (P.adicCompletion E) c' * z := by
    intro c' hc' i j
    have hcont : Continuous fun u : GL (Fin n) (AfE F E) =>
        (u : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j :=
      (Units.continuous_val.matrix_elem i j).sub continuous_const
    have ht := hcont.tendsto 1
    simp only [Units.val_one, sub_self] at ht
    exact ht.eventually (adAt_nhds P hc')
  have hinv : ∀ i j : Fin n, ∀ᶠ u : GL (Fin n) (AfE F E) in 𝓝 1, ∃ z ∈ P.adicCompletionIntegers E,
      adAt F P (((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E (P.adicCompletion E) 1 * z := by
    intro i j
    have ht : Filter.Tendsto (fun u : GL (Fin n) (AfE F E) => u⁻¹) (𝓝 1) (𝓝 1) := by
      have hcont : Continuous (fun u : GL (Fin n) (AfE F E) => u⁻¹) := by
        refine Units.continuous_iff.2 ⟨Units.continuous_coe_inv, ?_⟩
        simpa only [inv_inv] using (Units.continuous_val (M := Matrix (Fin n) (Fin n) (AfE F E)))
      simpa only [inv_one] using hcont.tendsto 1
    exact ht.eventually (hval 1 one_ne_zero i j)
  have h1 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hval c hc i j
  have h2 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hval 1 one_ne_zero i j
  have h3 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hinv i j
  filter_upwards [h1, h2, h3] with u a1 a2 a3
  refine ⟨int_of_sub fun i j => ?_, int_of_sub fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨z, hz, e⟩ := a2 i j
    rw [bc_adAt_sub, e, map_one, one_mul]
    exact hz
  · obtain ⟨z, hz, e⟩ := a3 i j
    rw [← map_inv, bc_adAt_sub, e, map_one, one_mul]
    exact hz
  · obtain ⟨z, hz, e⟩ := a1 i j
    exact ⟨z, hz, by rw [Matrix.sub_apply, bc_adAt_sub, e]⟩

theorem rhoT_nhds (P : HeightOneSpectrum (𝓞 E)) (t : GL (Fin n) (AfE F E)) {c : E} (hc : c ≠ 0) :
    ∀ᶠ x : GL (Fin n) (AfE F E) in 𝓝 1, rhoT F P t x ∈ qbK (algebraMap E (P.adicCompletion E) c) := by
  have hcont : Continuous fun x : GL (Fin n) (AfE F E) => t⁻¹ * x * t⁻¹⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have ht := hcont.tendsto 1
  simp only [mul_one, inv_inv, inv_mul_cancel] at ht
  exact ht.eventually (eventually_localComponent_mem P hc)

end Nhd

theorem qbK_le_locLev {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (Θ : LevI E K n P) (d : E) : qbK (algebraMap E (P.adicCompletion E) d) ≤ locLev P Θ d := fun k hk =>
  ⟨hk.1, hk.2.1, 1, Θ.H.one_mem, by simpa using hk⟩

theorem topU_open : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Q : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E), (∀ P, d P ≠ 0) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ U}) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ topU U t Θ d}) := by
  intro F E K _ _ _ _ _ _ _ σ n J Q U t Θ d hd hU
  have hW : ∀ P : Q, IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) |
      (x : GL (Fin n) (AfE F E)) ∈ (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)} := by
    intro P
    let W : Subgroup (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
      ((locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))
    have hn : (W : Set (UPts σ J (FiniteAdeleRing (𝓞 F) F))) ∈ 𝓝 (1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) := by
      have ht : Filter.Tendsto (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => (x : GL (Fin n) (AfE F E))) (𝓝 1) (𝓝 1) :=
        continuous_subtype_val.tendsto 1
      filter_upwards [ht.eventually (rhoT_nhds P.1 t (hd P))] with x hx
      exact qbK_le_locLev P.1 (Θ P) (d P) hx
    exact Subgroup.isOpen_of_mem_nhds W hn
  have e : {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL (Fin n) (AfE F E)) ∈ topU U t Θ d} =
      {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL (Fin n) (AfE F E)) ∈ U} ∩
        ⋂ P : Q, {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) |
          (x : GL (Fin n) (AfE F E)) ∈ (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)} := by
    ext x
    simp only [topU, Subgroup.mem_inf, Subgroup.mem_iInf, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  exact hU.inter (isOpen_iInter_of_finite hW)

end GlobalTheory.Mem.Col2.TopCh

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem coset_eq_iff_redV (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {a a' : Sp E n}
    (ha : ((qOf P : ℕ) : E) • a ∈ stdAt E n P) (ha' : ((qOf P : ℕ) : E) • a' ∈ stdAt E n P) :
    {z | z - a ∈ stdAt E n P} = {z | z - a' ∈ stdAt E n P} ↔
      redV P (((qOf P : ℕ) : E) • a) = redV P (((qOf P : ℕ) : E) • a') := by
  have hq0 := GlobalTheory.TopStep.qOf_ne_zero (P := P)
  have key : {z | z - a ∈ stdAt E n P} = {z | z - a' ∈ stdAt E n P} ↔ a - a' ∈ stdAt E n P := by
    constructor
    · intro h
      have h0 : a ∈ {z | z - a ∈ stdAt E n P} := by
        show a - a ∈ stdAt E n P
        rw [sub_self]
        exact zero_mem _
      rw [h] at h0
      exact h0
    · intro h
      ext z
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hz
        have := add_mem hz h
        rwa [sub_add_sub_cancel] at this
      · intro hz
        have := sub_mem hz h
        rwa [sub_sub_sub_cancel_right] at this
  rw [key, GlobalTheory.TopStep.mem_stdAt]
  constructor
  · intro h
    funext i
    have hi := GlobalTheory.TopStep.mem_stdAt.1 ha i
    have hi' := GlobalTheory.TopStep.mem_stdAt.1 ha' i
    show redP P ((((qOf P : ℕ) : E) • a) i) = redP P ((((qOf P : ℕ) : E) • a') i)
    rw [← sub_eq_zero, ← GlobalTheory.TopStep.reduction_sub hi hi']
    apply GlobalTheory.TopStep.redP_eq_zero_of_div
    convert h i using 1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    field_simp
  · intro h i
    have hi := GlobalTheory.TopStep.mem_stdAt.1 ha i
    have hi' := GlobalTheory.TopStep.mem_stdAt.1 ha' i
    have e := congrFun h i
    have h0 : redP P ((((qOf P : ℕ) : E) • a) i - (((qOf P : ℕ) : E) • a') i) = 0 := by
      rw [GlobalTheory.TopStep.reduction_sub hi hi']
      exact sub_eq_zero.2 e
    have := GlobalTheory.TopStep.intAt_div_of_redP hq (GlobalTheory.TopStep.intAt_sub hi hi') h0
    convert this using 1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    field_simp

end Local

section Pt

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

theorem mem_vGs_of_rowSG (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : rowSG Pr sel mu) : P.1 ∈ Pr.vGs := by
  have h := P.2
  simp only [rowSG, uSG, hQ, Finset.union_empty] at h
  exact h

theorem ptAt_coset (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (q : PtAt R sel mu cst u j) (h : j + 1 = R.m) :
    ∃ y : Sp X.E (R.N j), (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) ∧
      ∀ z, z ∈ q.1.2 ↔ ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N := by
  obtain ⟨y, hy, hY⟩ := q.mem_ybSet h
  refine ⟨y, fun w hw => ?_, fun z => ?_⟩
  · have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w, Finset.mem_union_left _ hw⟩
    simpa [hw] using this
  · rw [hY, Set.mem_setOf_eq, Formalism.L2.Col.mem_locLat]
    constructor
    · intro h w hw
      simpa [hw] using h ⟨w, Finset.mem_union_left _ hw⟩
    · intro h P
      have hP := mem_vGs_of_rowSG hQ P
      simpa [hP] using h P.1 hP

theorem cosetIn_eq (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hY : ∀ z, z ∈ q.1.2 ↔ ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (P : rowSG Pr sel mu) :
    cosetIn q P = {z | z - (q.1.1.deco.1.liftFr ⟨P.1, mem_vGs_of_rowSG hQ P⟩).symm y ∈ stdAt X.E (R.N j) P.1} := by
  have hP := mem_vGs_of_rowSG hQ P
  have hf := GlobalTheory.TopStep.liftFr_spec q.1.1.deco.2 ⟨P.1, hP⟩
  have hfr : frsF sel mu q.1.1 P = q.1.1.deco.1.liftFr ⟨P.1, hP⟩ := by
    unfold frsF
    rw [dite_eq_left hP]
  ext z
  simp only [cosetIn, Set.mem_setOf_eq, if_pos hP, pow_zero, inv_one, one_smul, hfr]
  constructor
  · rintro ⟨y', hy', hz⟩
    have h1 : (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y' - (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y ∈ stdAt X.E (R.N j) P.1 := by
      rw [← map_sub]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact (hY y').1 hy' P.1 hP)
    have := add_mem hz h1
    rwa [sub_add_sub_cancel] at this
  · intro hz
    exact ⟨y, (hY y).2 fun w _ => by rw [sub_self]; exact zero_mem _, hz⟩

theorem bar_eq (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hy : ∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N)
    (hY : ∀ z, z ∈ q.1.2 ↔ ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (w : Pr.vGs) :
    bar q w = {redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y)} := by
  have hd := q.1.1.deco.2
  have hf := GlobalTheory.TopStep.liftFr_spec hd w
  have hq := hy w.1 w.2
  have key : q.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y) =
      redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y) := by
    rw [← map_smul]
    have hs : (q.1.1.deco.1.liftFr w).symm (((qOf w.1 : ℕ) : X.E) • y) ∈ stdAt X.E _ w.1 :=
      (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hq)
    rw [← hf.2 _ hs, LinearEquiv.apply_symm_apply]
  ext v
  simp only [bar, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← key]
    have ht : z - y ∈ q.1.1.deco.1.at w.1 := (hY z).1 hz w.1 w.2
    have e : ((qOf w.1 : ℕ) : X.E) • z = ((qOf w.1 : ℕ) : X.E) • y + ((qOf w.1 : ℕ) : X.E) • (z - y) := by
      rw [← smul_add, add_sub_cancel]
    rw [e, hd.be_add w _ hq _ (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) ht),
      GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) ht, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
  · rintro rfl
    exact ⟨y, (hY y).2 fun w _ => by rw [sub_self]; exact zero_mem _, key.symm⟩

theorem cosetIn_eq_iff_bar_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ},
    QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) →
    ∀ q q' : PtAt R sel mu cst u j, cosetIn q = cosetIn q' ↔ MemChart.bar q = MemChart.bar q' := by
  intro X Pr R sel S mu cst u j hQ hq q q'
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hY⟩ := ptAt_coset hQ q h
    obtain ⟨y', hy', hY'⟩ := ptAt_coset hQ q' h
    have hA : ∀ (p : PtAt R sel mu cst u j) (y : Sp X.E (R.N j)),
        (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal p.1.1.deco.1.N) → ∀ w : Pr.vGs,
        ((qOf w.1 : ℕ) : X.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1 := by
      intro p y hy w
      have hf := GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 w
      rw [← map_smul]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hy w.1 w.2)
    rw [funext_iff, funext_iff]
    constructor
    · intro H w
      have := H ⟨w.1, Finset.mem_union_left _ w.2⟩
      rw [cosetIn_eq hQ q hY, cosetIn_eq hQ q' hY'] at this
      rw [bar_eq q hy hY, bar_eq q' hy' hY', Set.singleton_eq_singleton_iff]
      exact (coset_eq_iff_redV (hq w.1 w.2) (hA q y hy w) (hA q' y' hy' w)).1 this
    · intro H P
      have hP := mem_vGs_of_rowSG hQ P
      have := H ⟨P.1, hP⟩
      rw [bar_eq q hy hY, bar_eq q' hy' hY', Set.singleton_eq_singleton_iff] at this
      rw [cosetIn_eq hQ q hY, cosetIn_eq hQ q' hY']
      exact (coset_eq_iff_redV (hq P.1 hP) (hA q y hy ⟨P.1, hP⟩) (hA q' y' hy' ⟨P.1, hP⟩)).2 this
  · have e : ∀ p : PtAt R sel mu cst u j, p.1.2 = ∅ := fun p => by
      have := p.2
      rw [ysAt_ys_of_ne sel mu cst h] at this
      exact this
    have h1 : ∀ p : PtAt R sel mu cst u j, cosetIn p = fun _ => ∅ := fun p => by
      funext P
      ext z
      simp [cosetIn, e p]
    have h2 : ∀ p : PtAt R sel mu cst u j, bar p = fun _ => ∅ := fun p => by
      funext w
      ext v
      simp [bar, e p]
    rw [h1 q, h1 q', h2 q, h2 q']
    simp

end Pt

end GlobalTheory.Mem.Col2.MemChart
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

theorem hA_symVec_sub_ite_mem_wInt : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → ∀ (a : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posE D a then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  intro D X w k hg a j
  have hW : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.epsW X w i)) := by
    intro i
    unfold GlobalTheory.Mem.SymFrame.epsW
    split_ifs
    · exact ((X.weightVectorsIntegral _).2.2 a).2.1
    · exact ((X.weightVectorsIntegral _).2.2 a).2.2.2
  refine wInt_of_zmod X k hg ?_
  have ha := a.2
  have hpos : (GlobalTheory.Mem.SymChar.Resid.posE D a).1 = a.1 := rfl
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1]
    have h := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g (X.gramIntegral ⟨j.1, h1⟩ a).2.2
    rw [map_sub, ← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm] at h
    by_cases e : j = GlobalTheory.Mem.SymChar.Resid.posE D a
    · rw [if_pos e]
      rwa [if_pos (Fin.ext (by have := congrArg Fin.val e; simp only at this ⊢; omega)), map_one] at h
    · rw [if_neg e]
      rwa [if_neg (fun h' => e (Fin.ext (by have := congrArg Fin.val h'; simp only at this; omega))),
        map_zero] at h
  rw [dite_eq_right h1]
  have hne : ¬ j = GlobalTheory.Mem.SymChar.Resid.posE D a := fun e => by
    have := congrArg Fin.val e; rw [hpos] at this; omega
  rw [if_neg hne, sub_zero]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2]; exact hW _
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4]; exact (X.formsAtZero.2 a).2
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3]; exact (X.gramIntegral a _).2.1
  · rw [dite_eq_right h3, hA_zero_right']
    exact ⟨0, zero_mem _, by simp⟩

end GlobalTheory.Mem.SymChar
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN

theorem actHK_holds {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B)
    (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd)) : ActHK B hs hd hL hAct := by
  intro i v k hg z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul c m =>
    rw [LinearMap.baseChange_tmul]
    have hs1 := ((hAct i).choose_spec.2 v k hg m)
    have e : ∀ m' : MtSub B (partCompl_of hs hd) i, PsiC B (partCompl_of hs hd) hL i (c ⊗ₜ m') = c • ((m' : partOf B i) : B.V (jOf B i) (wOf B i)) := by
      intro m'
      haveI := hL i
      simp only [PsiC, mtEquiv, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype]
      rw [IsBaseChange.equiv_tmul]
      rfl
    rw [e, e, map_smul]
    congr 1

end GlobalTheory.HeckeLocN
end
