module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle100
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle101
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Pointwise Classical

namespace GlobalTheory.Mem.RowsBundle

theorem exists_conj_involution (I : AutInst) :
    ∃ cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E), (∀ v, cj (cj v) = v) ∧
      (∀ v v', IsConj I v v' ↔ v' = cj v) ∧
      ∀ (m : ℕ) (v : HeightOneSpectrum (𝓞 I.E)), (m : 𝓞 I.E) ∈ v.asIdeal → (m : 𝓞 I.E) ∈ (cj v).asIdeal := by
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  have hsurj : Function.Surjective st := fun a => ⟨st a, hst2 a⟩
  let cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E) := fun v => v.comap st hsurj
  have hcj : ∀ v a, a ∈ (cj v).asIdeal ↔ st a ∈ v.asIdeal := fun v a => Iff.rfl
  refine ⟨cj, fun v => HeightOneSpectrum.ext (Ideal.ext fun a => by rw [hcj, hcj, hst2]), fun v v' => ?_,
    fun m v hv => by rw [hcj, map_natCast]; exact hv⟩
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun b => ?_)
    rw [hcj]
    exact (h (st b) b (by rw [hst, star_star])).symm
  · rintro rfl a b hab
    have : b = st a := RingOfIntegers.ext hab
    subst this
    rw [hcj, hst2]

theorem meets_iff_card {X P : Type} (cj : X → X) (hc : ∀ v, cj (cj v) = v) (S : Set X) (hS : ∀ v ∈ S, cj v ∈ S)
    {m : ℕ} (hm : 0 < m) (hcard : S.ncard = 2 * m) (w : P → X) (hw : ∀ v, w v ∈ S) (hinj : Function.Injective w)
    (hn : ∀ v v', w v' ≠ cj (w v)) : (∀ u ∈ S, ∃ v, u = w v ∨ u = cj (w v)) ↔ Nat.card P = m := by
  let f : P ⊕ P → S := Sum.elim (fun v => ⟨w v, hw v⟩) (fun v => ⟨cj (w v), hS _ (hw v)⟩)
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) h
    · exact congrArg _ (hinj (congrArg Subtype.val h))
    · exact absurd (congrArg Subtype.val h) (hn _ _)
    · exact absurd (congrArg Subtype.val h).symm (hn _ _)
    · have h' : cj (w a) = cj (w b) := congrArg Subtype.val h
      exact congrArg _ (hinj (by rw [← hc (w a), h', hc]))
  have hS' : Nat.card S = 2 * m := hcard
  haveI : Finite S := Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite P := Finite.of_injective _ (hf.comp Sum.inl_injective)
  have hP : Nat.card (P ⊕ P) = Nat.card P + Nat.card P := Nat.card_sum
  constructor
  · intro h
    have hs : Function.Surjective f := fun u => by
      obtain ⟨v, e | e⟩ := h u.1 u.2
      · exact ⟨Sum.inl v, Subtype.ext e.symm⟩
      · exact ⟨Sum.inr v, Subtype.ext e.symm⟩
    have := Nat.card_eq_of_bijective f ⟨hf, hs⟩
    omega
  · intro h u hu
    have hb := (Nat.bijective_iff_injective_and_card f).2 ⟨hf, by omega⟩
    obtain ⟨v | v, e⟩ := hb.2 ⟨u, hu⟩
    · exact ⟨v, Or.inl (congrArg Subtype.val e).symm⟩
    · exact ⟨v, Or.inr (congrArg Subtype.val e).symm⟩

theorem isChoice_of_card (I : AutInst) (g : Fin 2 → ℕ) (hg : ∀ k, (g k).Prime) (hne : g 0 ≠ g 1)
    (hsp : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal →
      Ideal.absNorm v.asIdeal = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ v.asIdeal ^ 2 ∧ ¬ IsConj I v v)
    {m : ℕ} (hm : 0 < m)
    (hcard : ∀ k, {v : HeightOneSpectrum (𝓞 I.E) | ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal}.ncard = 2 * m) :
    (∃ w : ∀ _ : Fin 2, Fin m → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin m) w) ∧
      ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)),
        (∀ k, Fintype.card (Pl k) = m) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) →
        (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
  obtain ⟨cj, hc, hconj, hmem⟩ := exists_conj_involution I
  obtain ⟨Pl₀, w₀, -, h₀⟩ := exists_choice I g hg hne hsp
  have key : ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)),
      (∀ k, Fintype.card (Pl k) = m) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) →
      (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
    intro Pl _ w h1 h2 h3 h4
    refine ⟨hg, hne, h₀.2.2.1, fun k v => ⟨h2 k v, (hsp k _ (h2 k v)).1⟩, h3, h4, fun k u hu => ?_⟩
    simp only [hconj] at h4 ⊢
    exact (meets_iff_card cj hc _ (hmem (g k)) hm (hcard k) (w k) (h2 k) (h3 k) (h4 k)).2
      (by rw [Nat.card_eq_fintype_card, h1]) u hu
  refine ⟨?_, key⟩
  obtain ⟨-, -, -, h2, h3, h4, h5⟩ := h₀
  have hP : ∀ k, Nat.card (Pl₀ k) = m := fun k => by
    simp only [hconj] at h4 h5
    exact (meets_iff_card cj hc _ (hmem (g k)) hm (hcard k) (w₀ k) (fun v => (h2 k v).1) (h3 k) (h4 k)).1 (h5 k)
  have e : ∀ k, Fin m ≃ Pl₀ k := fun k =>
    haveI : Finite (Pl₀ k) := Nat.finite_of_card_ne_zero (by rw [hP]; omega)
    (Finite.equivFinOfCardEq (hP k)).symm
  exact ⟨fun k v => w₀ k (e k v), key _ _ (fun _ => Fintype.card_fin m) (fun k v => (h2 k _).1)
    (fun k => (h3 k).comp (e k).injective) fun k v v' => h4 k _ _⟩

section Unip

variable {I : AutInst}

theorem hAf_eq_dot (u v : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I u v =
    (fun i => sigR I.cm.sig (Af I.F) (u i)) ⬝ᵥ (I.J.map (inclE (F := I.F) (Af I.F)) *ᵥ v) := by
  simp only [hAf, hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hAf_inv_mulVec (x : I.Gf) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I (I.fmat x⁻¹ *ᵥ y) z = hAf I y (I.fmat x *ᵥ z) := by
  have hx : cT (sigR I.cm.sig (Af I.F)) (I.fmat x⁻¹) * I.J.map (inclE (F := I.F) (Af I.F)) * I.fmat x⁻¹ = _ := x⁻¹.2
  have hs : (fun i => sigR I.cm.sig (Af I.F) ((I.fmat x⁻¹ *ᵥ y) i)) =
      (fun i => sigR I.cm.sig (Af I.F) (y i)) ᵥ* cT (sigR I.cm.sig (Af I.F)) (I.fmat x⁻¹) := by
    funext i

    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, cT, map_sum, mul_comm]
  have h1 : I.fmat x⁻¹ * I.fmat x = 1 := by rw [← fmat_mul, inv_mul_cancel, fmat_one]
  rw [hAf_eq_dot, hAf_eq_dot, hs, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  conv_rhs => rw [← hx, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem hAf_pow_adjoint (x : I.Gf) (m : ℕ) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I ((I.fmat x⁻¹ - 1) ^ m *ᵥ y) z = hAf I y ((I.fmat x - 1) ^ m *ᵥ z) := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← ih, Matrix.sub_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]
    generalize (I.fmat x⁻¹ - 1) ^ m *ᵥ y = u
    have h := hAf_inv_mulVec x u z
    simp only [hAf, hform, Pi.sub_apply, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib] at h ⊢
    rw [h]

theorem sub_one_pow_mem {x : I.Gf} (hx : x ∈ I.Kset) (m : ℕ) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    (I.fmat x - 1) ^ m *ᵥ y ∈ I.Lf := by
  induction m with
  | zero => simpa using hy
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (mulVec_mem hx ih) ih

end Unip

end GlobalTheory.Mem.RowsBundle
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

theorem _root_.GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted : ∀ (X W : Scheme.{0}) (J : X.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X), Generates J σ → GeneratesAlong (J.comap g) σ g := by
  first | exact @GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates | exact GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates | (intros; apply GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SatInd

section Field

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem indepDatum_memGU_iff (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (M : GL (Fin n) K) :
    Formalism.UG.bc (n := Fin n) (g : K →+* K) M ∈ Formalism.UG.GU σ' n ↔ M ∈ Formalism.UG.GU σ n := by
  show Formalism.UG.cT σ' (((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K)) * Formalism.UG.antiJ K n *
      ((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K) = Formalism.UG.antiJ K n ↔
    Formalism.UG.cT σ (M : Matrix (Fin n) (Fin n) K) * Formalism.UG.antiJ K n * (M : Matrix (Fin n) (Fin n) K) =
      Formalism.UG.antiJ K n
  have e : Formalism.UG.cT σ' (((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K)) * Formalism.UG.antiJ K n *
      ((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K) =
      (Formalism.UG.cT σ (M : Matrix (Fin n) (Fin n) K) * Formalism.UG.antiJ K n * (M : Matrix (Fin n) (Fin n) K)).map
        (g : K →+* K) := by
    rw [Matrix.map_mul, Matrix.map_mul, antiJ_map, cT_map (g : K →+* K) σ σ' hg]
  rw [e]
  constructor
  · intro h
    exact Matrix.map_injective g.injective (h.trans (antiJ_map (g : K →+* K) n).symm)
  · intro h
    rw [h, antiJ_map]

theorem indepDatum_intRange (g : K ≃+* K) (hint : ∀ x, x ∈ Formalism.UG.intL K → g x ∈ Formalism.UG.intL K) {n : ℕ}
    (M : GL (Fin n) K) (hM : M ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL K).subtype).range) :
    Formalism.UG.bc (n := Fin n) (g : K →+* K) M ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL K).subtype).range := by
  obtain ⟨p, rfl⟩ := hM
  refine ⟨Formalism.UG.bc (n := Fin n) ((g : K →+* K).restrict (Formalism.UG.intL K) (Formalism.UG.intL K)
    (fun x hx => hint x hx)) p, ?_⟩
  ext i j
  rfl

end Field

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem indepDatum_bc_e (Dv Dv' : InertDatum L n v w)
    (Y : GL (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))) :
    Formalism.UG.bc (n := Fin n) (Dv'.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+*
              w.adicCompletion L) Y =
      Formalism.UG.bc (n := Fin n) ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
        w.adicCompletion L →+* w.adicCompletion L)
        (Formalism.UG.bc (n := Fin n) (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+*
          w.adicCompletion L) Y) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact (gEquiv_e Dv Dv' _).symm

def indepDatumK (Dv Dv' : InertDatum L n v w) : GL (Fin n) (w.adicCompletion L) :=
  (Formalism.UG.bc (n := Fin n) ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
    w.adicCompletion L →+* w.adicCompletion L) Dv.P)⁻¹ * Dv'.P

theorem indepDatum_loc (Dv Dv' : InertDatum L n v w) (x : GAf L n) :
    Dv'.loc x = (indepDatumK Dv Dv')⁻¹ * Formalism.UG.bc (n := Fin n) ((gEquiv Dv Dv' :
      w.adicCompletion L ≃+* w.adicCompletion L) : w.adicCompletion L →+* w.adicCompletion L) (Dv.loc x) *
        indepDatumK Dv Dv' := by
  simp only [InertDatum.loc, indepDatumK, map_mul, map_inv, indepDatum_bc_e Dv Dv']
  group

theorem indepDatumK_memGU (Dv Dv' : InertDatum L n v w) : indepDatumK Dv Dv' ∈ Formalism.UG.GU Dv'.σw n := by
  set g : w.adicCompletion L →+* w.adicCompletion L := ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
    w.adicCompletion L →+* w.adicCompletion L) with hgdef
  set Q : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Formalism.UG.bc (n := Fin n) g Dv.P :
    GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hQdef
  set Qi : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (((Formalism.UG.bc (n := Fin n) g Dv.P)⁻¹ :
    GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hQidef
  have hQ : Formalism.UG.cT Dv'.σw Q * Q = Formalism.UG.antiJ (w.adicCompletion L) n := by
    have hmap : Q = (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)).map g := rfl
    rw [hmap, cT_map g Dv.σw Dv'.σw (gEquiv_comm Dv Dv'), ← Matrix.map_mul, Dv.Panti, antiJ_map]
  have h1 : Q * Qi = 1 := by rw [hQdef, hQidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : Formalism.UG.cT Dv'.σw Qi * Formalism.UG.cT Dv'.σw Q = 1 := by rw [← Formalism.UG.cT_mul, h1, Formalism.UG.cT_one]
  show Formalism.UG.cT Dv'.σw (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))) *
      Formalism.UG.antiJ (w.adicCompletion L) n * (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))) =
    Formalism.UG.antiJ (w.adicCompletion L) n
  rw [← hQ, Formalism.UG.cT_mul]
  calc Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * Formalism.UG.cT Dv'.σw Qi *
        (Formalism.UG.cT Dv'.σw Q * Q) * (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)))
      = Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
          (Formalism.UG.cT Dv'.σw Qi * Formalism.UG.cT Dv'.σw Q) * (Q * Qi) *
          (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
          (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := by
        rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
    _ = Formalism.UG.cT Dv'.σw Q * Q := by rw [Dv'.Panti, hQ]

theorem indepDatumK_memKU (Dv Dv' : InertDatum L n v w) :
    (⟨indepDatumK Dv Dv', indepDatumK_memGU Dv Dv'⟩ : Formalism.UG.GU Dv'.σw n) ∈ Formalism.UG.KU Dv'.σw n := by
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf]
  refine ⟨indepDatumK_memGU Dv Dv', ?_⟩
  obtain ⟨p1, hp1⟩ := indepDatum_intRange (gEquiv Dv Dv') (fun x hx => (gEquiv_intL Dv Dv' x).1 hx) _ Dv.Pint
  obtain ⟨p2, hp2⟩ := Dv'.Pint
  refine ⟨p1⁻¹ * p2, ?_⟩
  rw [map_mul, map_inv, hp1, hp2]
  rfl

theorem indepDatum_hval (Dv Dv' : InertDatum L n v w) (h' : Formalism.UG.GU Dv'.σw n → ℂ)
    (hbi : IsBiInv (Formalism.UG.KU Dv'.σw n) h') (x : GAf L n) :
    Dv'.hval h' (Dv'.loc x) =
      Dv.hval (fun y => h' (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n y)) (Dv.loc x) := by
  have hk := indepDatumK_memGU Dv Dv'
  have hloc := indepDatum_loc Dv Dv' x
  set g : w.adicCompletion L →+* w.adicCompletion L := ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
    w.adicCompletion L →+* w.adicCompletion L) with hgdef
  unfold InertDatum.hval
  by_cases hy : Dv.loc x ∈ Formalism.UG.GU Dv.σw n
  · have hgy : Formalism.UG.bc (n := Fin n) g (Dv.loc x) ∈ Formalism.UG.GU Dv'.σw n :=
      (indepDatum_memGU_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') _).2 hy
    have hy' : Dv'.loc x ∈ Formalism.UG.GU Dv'.σw n := by
      rw [hloc]; exact mul_mem (mul_mem (inv_mem hk) hgy) hk
    rw [dite_eq_left hy', dite_eq_left hy]
    have hb := hbi (⟨⟨indepDatumK Dv Dv', hk⟩, indepDatumK_memKU Dv Dv'⟩ : Formalism.UG.KU Dv'.σw n)⁻¹
      ⟨⟨indepDatumK Dv Dv', hk⟩, indepDatumK_memKU Dv Dv'⟩
      (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n ⟨Dv.loc x, hy⟩)
    refine Eq.trans (congrArg h' ?_) hb
    apply Subtype.ext
    change Dv'.loc x = _
    rw [hloc]
    rfl
  · have hy' : Dv'.loc x ∉ Formalism.UG.GU Dv'.σw n := by
      intro h
      apply hy
      rw [← indepDatum_memGU_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv')]
      have he : Formalism.UG.bc (n := Fin n) g (Dv.loc x) =
          indepDatumK Dv Dv' * Dv'.loc x * (indepDatumK Dv Dv')⁻¹ := by
        rw [hloc]; group
      rw [he]
      exact mul_mem (mul_mem hk h) (inv_mem hk)
    rw [dite_eq_right hy', dite_eq_right hy]

theorem heckeFunI_indepDatum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv Dv' : InertDatum L n v w) (U : Subgroup (GAf L n)) (W : Type) [AddCommGroup W] [Module ℂ W]
    (h' : GU Dv'.σw n → ℂ), IsBiInv (KU Dv'.σw n) h' → ∀ f : GAf L n → W,
    heckeFunI L n U Dv' h' f =
      heckeFunI L n U Dv (fun y => h' (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n y)) f := by
  intro L _ _ _ n v w Dv Dv' U W _ _ h' hbi f
  funext g
  unfold heckeFunI
  refine finsum_congr fun c => ?_
  by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
  · rw [dite_eq_left hc, dite_eq_left hc, indepDatum_hval Dv Dv' h' hbi]
  · rw [dite_eq_right hc, dite_eq_right hc]

end GlobalTheory.SatInd
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

namespace GlobalTheory.SatInd

section Transport

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem bc_mem_range_intL_of (φ : K →+* K) (hφ : ∀ x ∈ intL K, φ x ∈ intL K) {n : ℕ}
    (x : GL (Fin n) K) (hx : x ∈ (bc (n := Fin n) (intL K).subtype).range) :
    bc (n := Fin n) φ x ∈ (bc (n := Fin n) (intL K).subtype).range := by
  obtain ⟨M, rfl⟩ := hx
  refine ⟨bc (φ.restrict (intL K) (intL K) hφ) M, ?_⟩
  apply Units.ext
  ext i j
  simp [bc]

theorem guMap_symm_comp (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hg' : ∀ x, g.symm (σ' x) = σ (g.symm x)) {n : ℕ} (y : GU σ n) :
    guMap g.symm hg' n (guMap g hg n y) = y := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [guMap_val]

theorem mem_KU_iff_guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {n : ℕ} (y : GU σ n) :
    y ∈ KU σ n ↔ guMap g hg n y ∈ KU σ' n := by
  have hs : ∀ x ∈ intL K, (g.symm : K →+* K) x ∈ intL K := by
    intro x hx
    rw [hint]
    simpa using hx
  simp only [KU, intPts, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨(guMap g hg n y).2, bc_mem_range_intL_of (g : K →+* K) (fun x hx => (hint x).1 hx) _ h⟩
  · rintro ⟨-, h⟩
    refine ⟨y.2, ?_⟩
    have := bc_mem_range_intL_of (g.symm : K →+* K) hs _ h
    convert this using 1
    apply Units.ext
    ext i j
    simp [bc, guMap_val]

end Transport


open Classical in
theorem satU_guMap : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q n m : ℕ) (h' : GU σ' n → ℂ), IsBiInv (KU σ' n) h' → (∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) → ∀ α : Fin m → ℂ, SatU ϖ q (fun y => h' (guMap g hg n y)) α = SatU ϖ' q h' α := by
  intro K _ _ g σ σ' hg hint ϖ ϖ' q n m h' hbi hcond α
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [hg]
    simp
  let e : GU σ n ≃* GU σ' n :=
    { toFun := guMap g hg n
      invFun := guMap g.symm hg' n
      left_inv := fun y => guMap_symm_comp g hg hg' y
      right_inv := fun y => by
        have := guMap_symm_comp g.symm hg' (by simpa using hg) y
        simpa using this
      map_mul' := map_mul _ }
  have he : ∀ y, e y = guMap g hg n y := fun _ => rfl
  let E : GU σ n ⧸ KU σ n ≃ GU σ' n ⧸ KU σ' n :=
    Quotient.congr e.toEquiv (fun a b => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
      change a⁻¹ * b ∈ KU σ n ↔ (e a)⁻¹ * e b ∈ KU σ' n
      rw [← map_inv, ← map_mul, he]
      exact mem_KU_iff_guMap g hg hint _)
  unfold SatU
  refine finsum_congr (fun a => ?_)
  congr 1
  set F' : GU σ' n → ℂ := fun y => if ∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n,
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) then h' y else 0 with hF'
  have hinv : ∀ (y : GU σ' n) (k : KU σ' n), F' (y * k) = F' y := by
    intro y k
    simp only [hF']
    have hc : (∃ u : GU σ' n, IsUnipU u ∧ ∃ k' ∈ KU σ' n,
        (((y * k : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((k' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔
        (∃ u : GU σ' n, IsUnipU u ∧ ∃ k' ∈ KU σ' n,
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((k' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      constructor
      · rintro ⟨u, hu, k', hk', hy⟩
        refine ⟨u, hu, k' * (k : GU σ' n)⁻¹, (KU σ' n).mul_mem hk' ((KU σ' n).inv_mem k.2), ?_⟩
        have h1 : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            (((y * k : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((((k : GU σ' n)⁻¹ : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          simp [Matrix.mul_assoc]
        rw [h1, hy]
        simp [Matrix.mul_assoc]
      · rintro ⟨u, hu, k', hk', hy⟩
        refine ⟨u, hu, k' * (k : GU σ' n), (KU σ' n).mul_mem hk' k.2, ?_⟩
        simp only [Subgroup.coe_mul, Units.val_mul, hy, Matrix.mul_assoc]
    have hh : h' (y * k) = h' y := by
      have := hbi 1 k y
      simpa using this
    simp only [hc, hh]
  have hmk : ∀ x : GU σ n ⧸ KU σ n, F' (E x).out = F' (guMap g hg n x.out) := by
    intro x
    have hx : E x = QuotientGroup.mk (guMap g hg n x.out) := by
      conv_lhs => rw [← Quotient.out_eq x]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KU σ' n) (guMap g hg n x.out)
    rw [hx, hk, hinv]
  calc (∑ᶠ x : GU σ n ⧸ KU σ n, if ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
          (((x.out : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            tMat ϖ n m a * (((u : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (((k : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        then h' (guMap g hg n x.out) else 0)
      = ∑ᶠ x : GU σ n ⧸ KU σ n, F' (E x).out := by
        refine finsum_congr (fun x => ?_)
        rw [hmk, hF']
        simp only [hcond a x.out]
    _ = ∑ᶠ x' : GU σ' n ⧸ KU σ' n, F' x'.out := finsum_comp_equiv E (f := fun x' => F' x'.out)

end GlobalTheory.SatInd
end
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.algebraicWeight_span_translates_factor_commutant : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ (τ : L →+* ℂ) (v : ι → ℂ), v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ (B : GL (Fin n) ℂ) (M : Matrix ι ι ℂ), (∀ A : GL (Fin n) ℂ, M * evM P (evPt τ A) = evM P (evPt τ A) * M) ∧ x = evM P (evPt τ B) *ᵥ (M *ᵥ v)} := by
  first | exact @GlobalTheory.AlgWtHW.span_tau_commutant | exact GlobalTheory.AlgWtHW.span_tau_commutant | (intros; apply GlobalTheory.AlgWtHW.span_tau_commutant <;> assumption)
end
