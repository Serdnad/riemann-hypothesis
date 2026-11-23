module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.BridgeEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
public import GroundTheory.GlobalFields.SemilocalAlgebras.Bundle001
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_adele {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) (c : Kw w) :
    ∃ a : Af L, pLoc L w a = c ∧ ∀ u : Plc L, u ≠ w → pLoc L u a = 0 := by
  classical
  refine ⟨⟨Function.update (fun _ => 0) w c, ?_⟩, ?_, ?_⟩
  · filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with u hu
    have hu' : u ≠ w := hu
    simp [Function.update_of_ne hu']
  · show Function.update (fun _ => 0) w c w = c
    simp
  · intro u hu
    show Function.update (fun _ => 0) w c u = 0
    simp [Function.update_of_ne hu]

private theorem decomp {K : Type} [Field K] {D : K} (x : Lsq K D) :
    x = algebraMap K (Lsq K D) x.re + algebraMap K (Lsq K D) x.im * QuadraticAlgebra.omega := by
  ext <;> simp

private theorem omega_sq {K : Type} [Field K] {D : K} :
    (QuadraticAlgebra.omega : Lsq K D) * QuadraticAlgebra.omega = algebraMap K (Lsq K D) D := by
  ext <;> simp

private theorem ne_zero_of_equiv {K M : Type} [Field K] [Field M] {D : K} (e : Lsq K D ≃+* M) : D ≠ 0 := by
  rintro rfl
  have hz : e QuadraticAlgebra.omega * e QuadraticAlgebra.omega = 0 := by
    rw [← map_mul, omega_sq, map_zero, map_zero]
  have hz' : e QuadraticAlgebra.omega = 0 := mul_self_eq_zero.mp hz
  have hz'' : (QuadraticAlgebra.omega : Lsq K 0) = 0 := e.injective (by rw [hz', map_zero])
  have := congrArg QuadraticAlgebra.im hz''
  simp at this

theorem UpperTheory.V.Z.Sym.Dict.Br.splitCore :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (w : Plc L), IsSplitAt w → ∃ (s : Kv (un w)) (hs : s * s = cv (un w) R.Δ) (i : Kv (un w) ≃+* Kw w), s ≠ 0 ∧ ∀ x, R.ρ _ w rfl x = i (Sig.proj hs x) := by
  intro L _ _ _ R w hw
  obtain ⟨u, huw, hu⟩ := hw
  have hu' : un u = un w := hu
  let f : Kv (un w) →+* Kw w := (R.ρ _ w rfl).comp (algebraMap _ _)
  have hf : Function.Injective f := f.injective
  have hdec : ∀ x : Lsq (Kv (un w)) (cv (un w) R.Δ),
      R.ρ _ w rfl x = f x.re + f x.im * R.ρ _ w rfl QuadraticAlgebra.omega := by
    intro x
    conv_lhs => rw [decomp x]
    simp [f]
  obtain ⟨a₁, h₁u, h₁o⟩ := exists_adele u (1 : Kw u)
  obtain ⟨y, hy⟩ := R.ρ_surj (un w) a₁
  have hyw : R.ρ _ w rfl y = 0 := (hy w rfl).trans (h₁o w huw.symm)
  have hyu : R.ρ _ u hu' y = 1 := (hy u hu').trans h₁u
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hyu
  have him : y.im ≠ 0 := by
    intro h0
    apply hy0
    have h1 := hdec y
    rw [hyw, h0, map_zero, zero_mul, add_zero] at h1
    have h2 : y.re = 0 := hf (by rw [← h1, map_zero])
    exact QuadraticAlgebra.ext h2 h0
  have hfim : f y.im ≠ 0 := fun h => him (hf (by rw [h, map_zero]))
  set r := R.ρ _ w rfl QuadraticAlgebra.omega with hr
  let s : Kv (un w) := -y.re / y.im
  have hrs : r = f s := by
    have h1 := hdec y
    rw [hyw] at h1
    simp only [s, map_div₀, map_neg]
    field_simp
    linear_combination -h1
  have hs : s * s = cv (un w) R.Δ := by
    apply hf
    rw [map_mul, ← hrs, hr, ← map_mul, omega_sq]
    rfl
  have hsur : Function.Surjective f := by
    intro c
    obtain ⟨a, hac, -⟩ := exists_adele w c
    obtain ⟨x, hx⟩ := R.ρ_surj (un w) a
    refine ⟨Sig.proj hs x, ?_⟩
    have h1 := hdec x
    rw [hx w rfl, hac, hrs] at h1
    rw [h1]
    simp [Sig.proj, mul_comm]
  refine ⟨s, hs, RingEquiv.ofBijective f ⟨hf, hsur⟩, ?_, ?_⟩
  · intro h0
    apply ne_zero_of_equiv R.e
    have h1 : cv (un w) R.Δ = 0 := by rw [← hs, h0, zero_mul]
    exact (cv (un w)).injective (by rw [h1, map_zero])
  · intro x
    rw [hdec x, hrs]
    show _ = f (Sig.proj hs x)
    simp [Sig.proj, mul_comm]
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.adSurj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (n : ℕ) (g : UA L n), ∃ x : ∀ v : Pl (Lp L), Matrix (Fin n) (Fin n) (Lsq (Kv v) (cv v R.Δ)), (∀ v, star (x v) * x v = 1) ∧ (∀ᶠ v in Filter.cofinite, ∀ i j, IsIntegral (Ov v) (x v i j)) ∧ ∀ w, mL w g = (x (un w)).map (R.ρ _ w rfl) := by
  intro L _ _ _ R n g
  classical
  let G : Matrix (Fin n) (Fin n) (Ad L) := (g.1 : Matrix (Fin n) (Fin n) (Ad L))
  let A : Matrix (Fin n) (Fin n) (Af L) := G.map (pFin L)
  have hU : ∀ i j, ∑ k, cjF (L := L) (A k i) * A k j = (1 : Matrix (Fin n) (Fin n) (Af L)) i j := by
    have hG : Formalism.UG.cT (conjAd L) G * 1 * G = 1 := g.2
    have h1 := congrArg (pFin L).mapMatrix hG
    rw [map_one, map_mul, map_mul, map_one, Matrix.mul_one] at h1
    intro i j
    have h2 := congrFun (congrFun h1 i) j
    rw [Matrix.mul_apply] at h2
    exact h2
  have hx : ∀ v i j, ∃ x : Lsq (Kv v) (cv v R.Δ), ∀ w h, R.ρ v w h x = pLoc L w (A i j) :=
    fun v i j => R.ρ_surj v (A i j)
  choose x hx using hx
  refine ⟨fun v => Matrix.of (x v), ?_, ?_, ?_⟩
  · intro v
    ext1 i j
    rw [← sub_eq_zero]
    apply R.ρ_inj v
    intro w h

    rw [map_sub, Matrix.mul_apply, map_sum]
    have e1 : ∀ k, R.ρ v w h ((star (Matrix.of (x v))) i k * (Matrix.of (x v)) k j) =
        pLoc L w (cjF (L := L) (A k i) * A k j) := by
      intro k
      rw [map_mul, map_mul, Matrix.star_apply, Matrix.of_apply, Matrix.of_apply,
        R.ρ_star v _ _ (hx v k i) w h, hx v k j w h]

    rw [Finset.sum_congr rfl fun k _ => e1 k, ← map_sum, hU i j]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  · have hfin : ∀ i j, {w : Plc L | pLoc L w (A i j) ∉ w.adicCompletionIntegers L}.Finite := by
      intro i j
      exact (A i j).2
    have hall : {w : Plc L | ∃ i j, pLoc L w (A i j) ∉ w.adicCompletionIntegers L}.Finite := by
      have : {w : Plc L | ∃ i j, pLoc L w (A i j) ∉ w.adicCompletionIntegers L} =
          ⋃ i, ⋃ j, {w : Plc L | pLoc L w (A i j) ∉ w.adicCompletionIntegers L} := by
        ext w; simp
      rw [this]
      exact Set.finite_iUnion fun i => Set.finite_iUnion fun j => hfin i j
    have hbad := hall.image (fun w : Plc L => un w)
    rw [Filter.eventually_cofinite]
    refine hbad.subset ?_
    intro v hv
    simp only [Set.mem_setOf_eq, not_forall] at hv
    obtain ⟨i, j, hij⟩ := hv
    have : ¬ ∀ w h, R.ρ v w h (x v i j) ∈ w.adicCompletionIntegers L := fun h => hij ((R.ρ_int v _).2 h)
    simp only [not_forall] at this
    obtain ⟨w, h, hw⟩ := this
    exact ⟨w, ⟨i, j, by rwa [hx v i j w h] at hw⟩, h⟩
  · intro w
    refine Matrix.ext fun i j => ?_
    change mL w g i j = R.ρ _ w rfl (x (un w) i j)
    rw [hx (un w) i j w rfl]
    rfl
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

private theorem ratGL_val {L : Type} [Field L] [NumberField L] (n : ℕ) (g : GL (Fin n) L) :
    ((ratGL L n g : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) =
      (g : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L)) := rfl

private theorem ratGL_map {L : Type} [Field L] [NumberField L] (n : ℕ) (g : GL (Fin n) L) :
    ratGL L n g = GeneralLinearGroup.map (algebraMap L (Ad L)) g :=
  Units.ext (ratGL_val n g)

private theorem alg_inj {L : Type} [Field L] [NumberField L] [IsCMField L] :
    Function.Injective (algebraMap L (Ad L)) := by
  obtain ⟨τ⟩ : Nonempty (L →+* ℂ) := inferInstance
  intro x y h
  have e := congrArg (fun z => coord τ (pInf L z)) h
  simp only [coord_algebraMap] at e
  exact τ.injective e

private theorem loc_alg {L : Type} [Field L] [NumberField L] (w : Plc L) (x : L) :
    pLoc L w (pFin L (algebraMap L (Ad L) x)) = algebraMap L (Kw w) x := rfl

end UpperTheory.V.Z.Sym.Dict.Br

theorem UpperTheory.V.Z.Sym.Dict.Br.ratFacts :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (g : GL (Fin n) L), (ratGL L n g ∈ UA L n ↔ ((g : Matrix (Fin n) (Fin n) L).map (IsCMField.complexConj L))ᵀ * (g : Matrix (Fin n) (Fin n) L) = 1) ∧ Function.Injective (ratGL L n) ∧ ∀ h : ratGL L n g ∈ UA L n, (∀ w, mL w ⟨_, h⟩ = (g : Matrix (Fin n) (Fin n) L).map (algebraMap L (Kw w))) ∧ (∀ τ : L →+* ℂ, (cEmb τ ⟨_, h⟩ : Matrix (Fin n) (Fin n) ℂ) = (g : Matrix (Fin n) (Fin n) L).map τ) ∧ ((GeneralLinearGroup.det (ratGL L n g) = 1) ↔ GeneralLinearGroup.det g = 1) := by
  intro L _ _ _ n g
  have hinj := alg_inj (L := L)
  refine ⟨?_, ?_, fun h => ⟨fun w => ?_, fun τ => ?_, ?_⟩⟩
  · have key : Formalism.UG.cT (conjAd L) ((ratGL L n g : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 *
        ((ratGL L n g : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) =
        (((g : Matrix (Fin n) (Fin n) L).map (IsCMField.complexConj L))ᵀ * (g : Matrix (Fin n) (Fin n) L)).map
          (algebraMap L (Ad L)) := by
      rw [ratGL_val, mul_one, Formalism.UG.cT, Matrix.map_mul]
      congr 1
      ext i j
      simp [conjAd_algebraMap]
    change Formalism.UG.cT (conjAd L) _ * 1 * _ = 1 ↔ _
    rw [key]
    constructor
    · intro e
      ext i j
      have := congrFun (congrFun e i) j
      apply hinj
      rw [Matrix.map_apply] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · intro e
      rw [e]
      simp
  · intro a b e
    ext i j
    have := congrArg (fun x : GL (Fin n) (Ad L) => (x : Matrix (Fin n) (Fin n) (Ad L)) i j) e
    simp only [ratGL_val, Matrix.map_apply] at this
    exact hinj this
  · exact Matrix.ext fun i j => loc_alg w _
  · exact Matrix.ext fun i j => coord_algebraMap τ _
  · have hd : ((GeneralLinearGroup.det (ratGL L n g) : (Ad L)ˣ) : Ad L) =
        algebraMap L (Ad L) ((GeneralLinearGroup.det g : Lˣ) : L) := by
      rw [ratGL_map, GlobalTheory.CuspRep.det_map]
    constructor
    · intro e
      rw [e] at hd
      apply Units.ext
      apply hinj
      rw [← hd]
      simp
    · intro e
      apply Units.ext
      rw [hd, e]
      simp
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem kgl_iff {L : Type} [Field L] [NumberField L] (w : Plc L) (x : GL (Fin 2) (w.adicCompletion L)) :
    x ∈ GlobalTheory.LFun.KGL w (n := 2) ↔ (∀ i j, x.val i j ∈ w.adicCompletionIntegers L) ∧
      ∀ i j, (x⁻¹).val i j ∈ w.adicCompletionIntegers L :=
  ⟨fun h => ⟨fun i j => GlobalTheory.CptCent.entry_mem_of_mem_GLint' _ h i j,
      fun i j => GlobalTheory.CptCent.entry_mem_of_mem_GLint' _ (inv_mem h) i j⟩,
    fun h => GlobalTheory.CptCent.mem_GLint_of_entries' _ x h.1 h.2⟩

theorem UpperTheory.V.Z.Sym.Dict.Br.okS :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), (∀ (g : SA B.Δ) v, (g : DA B.Δ).1 v ∈ KD _ (Ov v) ↔ ∀ w, un w = v → cLoc w (B.bS g : UA L 2) ∈ GlobalTheory.LFun.KGL w (n := 2)) ∧ (∀ (g : SA B.Δ) v, (g : DA B.Δ).1 v = 1 ↔ ∀ w, un w = v → cLoc w (B.bS g : UA L 2) = 1) ∧ ∀ w (S : B.toRingBr.Split w) (g : SA B.Δ), cLoc w (B.bS g : UA L 2) = GeneralLinearGroup.map (S.i : Kv (un w) →+* Kw w) (Sig.eD S.hs ((g : DA B.Δ).1 (un w))) := by
  intro L _ _ _ B
  have loc : ∀ (g : SA B.Δ) (w : Plc L) i j, (cLoc w (B.bS g : UA L 2)).val i j =
      B.ρ _ w rfl (Glob.mt ((g : DA B.Δ).1 (un w)) i j) := fun g w i j => by
    have := B.bS_loc g w
    exact congrFun (congrFun this i) j
  have locI : ∀ (g : SA B.Δ) (w : Plc L) i j, ((cLoc w (B.bS g : UA L 2))⁻¹).val i j =
      B.ρ _ w rfl (Glob.mt ((g : DA B.Δ).1 (un w))⁻¹ i j) := fun g w i j => by
    have h := loc g⁻¹ w i j
    rw [map_inv] at h
    simpa using h
  refine ⟨fun g v => ?_, fun g v => ?_, fun w S g => ?_⟩
  · rw [mem_KD]
    constructor
    · rintro ⟨h1, h2⟩ w rfl
      refine (kgl_iff w _).2 ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [loc]
        exact (B.ρ_int _ _).1 (h1 i j) w rfl
      · rw [locI]
        exact (B.ρ_int _ _).1 (h2 i j) w rfl
    · intro h
      refine ⟨fun i j => (B.ρ_int _ _).2 fun w hw => ?_, fun i j => (B.ρ_int _ _).2 fun w hw => ?_⟩
      · subst hw
        have := ((kgl_iff w _).1 (h w rfl)).1 i j
        rwa [loc] at this
      · subst hw
        have := ((kgl_iff w _).1 (h w rfl)).2 i j
        rwa [locI] at this
  · constructor
    · rintro h w rfl
      apply Units.ext
      refine Matrix.ext fun i j => ?_
      rw [loc, h]
      change B.ρ _ w rfl ((1 : Matrix (Fin 2) (Fin 2) _) i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [Matrix.one_apply_ne hij]
    · intro h
      have e : Glob.mt ((g : DA B.Δ).1 v) = 1 := by
        ext1 i j
        rw [← sub_eq_zero]
        refine B.ρ_inj v _ fun w hw => ?_
        subst hw
        have h1 := loc g w i j
        rw [h w rfl] at h1
        rw [map_sub, ← h1]
        change (1 : Matrix (Fin 2) (Fin 2) _) i j - B.ρ _ w rfl ((1 : Matrix (Fin 2) (Fin 2) _) i j) = 0
        rcases eq_or_ne i j with rfl | hij
        · simp
        · simp [Matrix.one_apply_ne hij]
      exact Subtype.ext (Units.ext e)
  · apply Units.ext
    refine Matrix.ext fun i j => ?_
    rw [loc]
    exact S.ρ_eq _
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG GlobalTheory.BCT.FinPtLoc in
private theorem fin_fst {L : Type} [Field L] [NumberField L] {n : ℕ} (g : GL (Fin n) (Af L)) (i j : Fin n) :
    fstA L ((finGL L n g).val i j) = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing L)) i j := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing L × Af L)) i j -
      ((0 : InfiniteAdeleRing L), (1 : Matrix (Fin n) (Fin n) (Af L)) i j) +
      ((0 : InfiniteAdeleRing L), g.val i j)).1 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

open Formalism.UG GlobalTheory.BCT.FinPtLoc in
private theorem fin_snd {L : Type} [Field L] [NumberField L] {n : ℕ} (g : GL (Fin n) (Af L)) (i j : Fin n) :
    pFin L ((finGL L n g).val i j) = g.val i j := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing L × Af L)) i j -
      ((0 : InfiniteAdeleRing L), (1 : Matrix (Fin n) (Fin n) (Af L)) i j) +
      ((0 : InfiniteAdeleRing L), g.val i j)).2 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]


open Formalism.UG GlobalTheory.BCT.FinPtLoc in
private theorem fin_mem {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (g : GL (Fin n) (Af L))
    (hg : cT (cjF (L := L)) g.val * g.val = 1) : finGL L n g ∈ UA L n := by
  show cT (conjAd L) (finGL L n g).val * 1 * (finGL L n g).val = 1
  have hf : (finGL L n g).val.map (fstA L) = 1 := by
    ext i j; rw [Matrix.map_apply, fin_fst]
  have hs : (finGL L n g).val.map (pFin L) = g.val := by
    ext i j; rw [Matrix.map_apply, fin_snd]
  apply ext_ad
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (fstA L) (conjAd L) ((infEq L).toRingHom.comp ((starRingEnd (Cinf L)).comp (infEq L).symm.toRingHom)) (fun x => rfl), hf, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i j; simp [cT, Matrix.one_apply]
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (pFin L) (conjAd L) (cjF (L := L)) (fun x => rfl), hs,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, hg]

open Formalism.UG GlobalTheory.BCT.FinPtLoc in
private theorem fin_ker {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (g : GL (Fin n) (Af L))
    (h : finGL L n g ∈ UA L n) : (⟨_, h⟩ : UA L n) ∈ finU (E := L) (n := n) := by
  show cInf (⟨_, h⟩ : UA L n) = 1
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change (infEq L).symm (fstA L ((finGL L n g).val i j)) = (1 : Matrix (Fin n) (Fin n) (Cinf L)) i j
  rw [fin_fst]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem UpperTheory.V.Z.Sym.Dict.Br.adEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (n : ℕ) (x : ∀ v : Pl (Lp L), Matrix (Fin n) (Fin n) (Lsq (Kv v) (cv v R.Δ))), (∀ v, star (x v) * x v = 1) → (∀ᶠ v in Filter.cofinite, ∀ i j, IsIntegral (Ov v) (x v i j)) → ∃ g ∈ finU (E := L) (n := n), ∀ w, mL w g = (x (un w)).map (R.ρ _ w rfl) := by
  intro L _ _ _ R n x hx hint
  have ev : ∀ i j, ∀ᶠ w : Plc L in Filter.cofinite, R.ρ _ w rfl (x (un w) i j) ∈ w.adicCompletionIntegers L :=
    fun i j => ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (Lp L) L).eventually hint).mono
      fun w h => (R.ρ_int (un w) _).1 (h i j) w rfl
  let a : Fin n → Fin n → Af L := fun i j => ⟨fun w => R.ρ _ w rfl (x (un w) i j), ev i j⟩
  have ha : ∀ i j (w : Plc L), pLoc L w (a i j) = R.ρ _ w rfl (x (un w) i j) := fun _ _ _ => rfl
  have hv : ∀ i j (v : Pl (Lp L)) (w : Plc L) (h : un w = v), R.ρ v w h (x v i j) = pLoc L w (a i j) := by
    rintro i j _ w rfl; rfl
  have hc : ∀ i j (w : Plc L), pLoc L w (cjF (a i j)) = R.ρ _ w rfl (star (x (un w) i j)) := fun i j w =>
    (R.ρ_star (un w) (x (un w) i j) (a i j) (hv i j (un w)) w rfl).symm
  let M : Matrix (Fin n) (Fin n) (Af L) := Matrix.of a
  have hM : Formalism.UG.cT (cjF (L := L)) M * M = 1 := by
    refine Matrix.ext fun i j => Subtype.ext (funext fun w => ?_)
    have h1 := congrArg (R.ρ _ w rfl) (congrFun (congrFun (hx (un w)) i) j)

    rw [Matrix.mul_apply, map_sum] at h1
    change pLoc L w _ = pLoc L w _

    rw [Matrix.mul_apply, map_sum]
    have h2 : pLoc L w ((1 : Matrix (Fin n) (Fin n) (Af L)) i j) = R.ρ _ w rfl ((1 : Matrix (Fin n) (Fin n) _) i j) := by
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [h2, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul]
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.star_apply]
    exact congrArg₂ _ (hc k i w) (ha k j w)
  let g : GL (Fin n) (Af L) := ⟨M, Formalism.UG.cT (cjF (L := L)) M, mul_eq_one_comm.1 hM, hM⟩
  have hm := fin_mem g hM
  refine ⟨⟨_, hm⟩, fin_ker g hm, fun w => ?_⟩
  refine Matrix.ext fun i j => ?_
  change pLoc L w (pFin L ((finGL L n g).val i j)) = _
  rw [fin_snd]
  rfl
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.phiEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], ∃ φ : ∀ (v : Pl (Lp L)) (w : Plc L), un w = v → Kv v →+* Kw w, (∀ v w h, Continuous (φ v w h)) ∧ ∀ v w h (a : Lp L), φ v w h (cv v a) = algebraMap L (Kw w) (algebraMap (Lp L) L a) := by
  intro L _ _ _
  have hlo : ∀ (v : Pl (Lp L)) (w : Plc L), un w = v → w.asIdeal.LiesOver v.asIdeal := by
    intro v w h
    subst h
    exact ⟨rfl⟩
  refine ⟨fun v w h => @GroundTheory.Global.SemiLocal.completionMap _ _ _ _ _ _ _ v w (hlo v w h), ?_, ?_⟩
  · intro v w h
    exact @GroundTheory.Global.SemiLocal.continuous_completionMap _ _ _ _ _ _ _ v w (hlo v w h)
  · intro v w h a
    have e := @GroundTheory.Global.SemiLocal.completionMap_algebraMap _ _ _ _ _ _ _ v w (hlo v w h) a
    simp only [cv]
    rw [e]
    exact IsScalarTower.algebraMap_apply (Lp L) L _ a
end
