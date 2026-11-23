module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle472
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle474
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle477
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle067
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle098
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevelElt

theorem one_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), ChiFin I l Z S → ∀ (P : SBof I a), P.1 ∈ I.Q a → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ (N : ℕ) (g₁ g₂ : GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z.1 = 1) ∧ GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z.1 ∧ ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 (((g₁ * (show GA B (B.R.N i) from z.1) * g₂ : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.OnePrime.exists_level_elt | exact GlobalTheory.Mem.Col2.AdT.OnePrime.exists_level_elt | (intros; apply GlobalTheory.Mem.Col2.AdT.OnePrime.exists_level_elt <;> assumption)

theorem place_under : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : SBof I a), P.1 ∈ I.Q a → ∃ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∀ P' : SBof I a, P' ≠ P → ¬ Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P'.1) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.PlaceUnder.main | exact GlobalTheory.Mem.Col2.AdT.PlaceUnder.main | (intros; apply GlobalTheory.Mem.Col2.AdT.PlaceUnder.main <;> assumption)

theorem support_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F)), (∀ v', v' ≠ v → bc (prV (E := E) v') z = 1) → ∀ P : HeightOneSpectrum (𝓞 E), ¬ Formalism.L2.Col.IsOver v P → ∀ r s, adAt F P ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
  first | exact @GlobalTheory.Mem.Col2.AdSupport.adAt_entry_eq_one_of_not_over | exact GlobalTheory.Mem.Col2.AdSupport.adAt_entry_eq_one_of_not_over | (intros; apply GlobalTheory.Mem.Col2.AdSupport.adAt_entry_eq_one_of_not_over <;> assumption)

theorem point_of_rat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → (∀ P ∈ Q, ∃ γ : GL (Fin n) E, ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s)) → ∃ p : DecoF E n ST SG Q, IsPtOf hc g p := by
  first | exact @GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat | exact GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat | (intros; apply GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat <;> assumption)

theorem mul_comp_eq {M N : Type} [Monoid M] [Monoid N] (f : M →* N) (y a b c k : M) (h : f b = f c) :
    f (y * (a * b) * k) = f (y * a * c * k) := by
  simp only [map_mul, h, mul_assoc]

theorem entry_eq_of_eq {M : Type} [Monoid M] {n : ℕ} {R : Type} [Semiring R] (f : M →* Matrix (Fin n) (Fin n) R) (b c : M)
    (h : f b = f c) (r s : Fin n) : f b r s = f c r s := by rw [h]



theorem exists_level_elt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl), ChiFin I l Z (K (chOf c)).lev → ∀ κ : (K (chOf c)).lev.U, ∃ x : (K (chOf c)).lev.U, (K (chOf c)).lev.chi x = (K (chOf c)).lev.chi κ ∧ (∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * (show GA B (B.R.N i) from x.1) * k (chOf c)) q) ∧ ∀ P : SBof I a, GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (κ.1⁻¹ * x.1) := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c hChi κ
  classical
  have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hg : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) = UAd B.sp.cm (B.R.N i) := by rw [hg]; rfl
  set y : GA B (B.R.N i) := ((K (chOf c)).y ⟨c, rfl⟩).1 with hy
  set kk : GA B (B.R.N i) := k (chOf c) with hkk
  have hsel : ∀ P : SBof I a, ∃ z : (K (chOf c)).lev.U, (K (chOf c)).lev.chi z = 1 ∧
      (∀ P' : SBof I a, P' ≠ P → ∀ r s, adAt B.host.F P'.1 (((show GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P'.1.adicCompletion B.fields.E)) r s) ∧
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) z.1 ∧
      (P.1 ∈ I.Q a → ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 ((((y * (show GA B (B.R.N i) from κ.1)) * (show GA B (B.R.N i) from z.1) * kk : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) := by
    intro P
    by_cases hP : P.1 ∈ I.Q a
    · obtain ⟨v, hv, hv'⟩ := place_under I hOk hPins l Z a P hP
      obtain ⟨z, hz1, hz2, hz3, hz4⟩ := one_prime I hOk hPins l Z a _ i hi bad (K (chOf c)).lev hChi P hP v hv ((I.cst a).D P) (y * (show GA B (B.R.N i) from κ.1)) kk
      refine ⟨z, hz1, fun P' hP' r s => ?_, hz3, fun _ => hz4⟩
      have e := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) 0 P' z.1).1
      have h2 := hv' P' hP'
      rw [e] at h2
      exact support_one z.1 v hz2 P'.1 h2 r s
    · refine ⟨1, map_one _, fun P' _ r s => ?_, GlobalTheory.TwU.congAt_one _ _, fun h => absurd h hP⟩
      show adAt B.host.F P'.1 ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = _
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  choose zf hzf1 hzf2 hzf3 hzf4 using hsel
  let cP : ∀ P : HeightOneSpectrum (𝓞 B.fields.E), GA B (B.R.N i) →* Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.adicCompletion B.fields.E) :=
    fun P => (RingHom.mapMatrix (adAt B.host.F P)).toMonoidHom.comp (Units.coeHom _)
  have cP_apply : ∀ P (g : GA B (B.R.N i)) r s, cP P g r s = adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) := fun _ _ _ _ => rfl
  let ι : (K (chOf c)).lev.U →* GA B (B.R.N i) := (K (chOf c)).lev.U.subtype
  have hone : ∀ P P' : SBof I a, P' ≠ P → cP P'.1 (ι (zf P)) = 1 := fun P P' h => Matrix.ext fun r s => by
    rw [cP_apply]; exact hzf2 P P' h r s
  have hlist : ∀ (L : List (SBof I a)), L.Nodup → ∀ P' : SBof I a, cP P'.1 (ι (L.map zf).prod) = if P' ∈ L then cP P'.1 (ι (zf P')) else 1 := by
    intro L
    induction L with
    | nil => intro _ P'; simp
    | cons P L ih =>
      intro hL P'
      rw [List.nodup_cons] at hL
      change cP P'.1 (ι (zf P * (L.map zf).prod)) = _
      calc
        cP P'.1 (ι (zf P * (L.map zf).prod)) = cP P'.1 (ι (zf P)) * cP P'.1 (ι (L.map zf).prod) := by
          rw [map_mul ι, map_mul (cP P'.1)]
        _ = cP P'.1 (ι (zf P)) * (if P' ∈ L then cP P'.1 (ι (zf P')) else 1) :=
          congrArg (fun x => cP P'.1 (ι (zf P)) * x) (ih hL.2 P')
        _ = _ := by
          by_cases h : P = P'
          · subst h
            simp [hL.1]
          · rw [hone P P' (Ne.symm h)]
            simp [Ne.symm h]
  obtain ⟨w, hw⟩ : ∃ w : (K (chOf c)).lev.U, w = ((Finset.univ : Finset (SBof I a)).toList.map zf).prod := ⟨_, rfl⟩
  have hwP : ∀ P : SBof I a, cP P.1 (ι w) = cP P.1 (ι (zf P)) := fun P => by
    rw [hw, hlist _ (Finset.nodup_toList _) P, if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  have hchiw : (K (chOf c)).lev.chi w = 1 := by
    rw [hw, map_list_prod]
    refine List.prod_eq_one fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [List.mem_map] at hz
    obtain ⟨P, -, rfl⟩ := hz
    exact hzf1 P
  have hpt : ∀ g : GA B (B.R.N i), g ∈ UAd B.sp.cm (B.R.N i) → (∀ P ∈ I.Q a, ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) → ∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf g q :=
    fun g hg hr => point_of_rat B.sp.cm _ _ _ g hg hr
  have hQsub : ∀ P ∈ I.Q a, P ∈ SBof I a := fun P hP => by
    show P ∈ uSG _ _
    exact Finset.mem_union_right _ hP
  refine ⟨κ * w, ?_, ?_, ?_⟩
  · exact (map_mul (K (chOf c)).lev.chi κ w).trans ((congrArg _ hchiw).trans (mul_one _))
  · obtain ⟨p0, hp0, -⟩ := hR.k_std (chOf c)
    have hyU : y ∈ UAd B.sp.cm (B.R.N i) := eU ▸ ((K (chOf c)).y ⟨c, rfl⟩).2
    have hxU : (show GA B (B.R.N i) from (κ * w).1) ∈ UAd B.sp.cm (B.R.N i) := eU ▸ (((K (chOf c)).lev.U_eq _).1 (κ * w).2).1
    have hkU : kk ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
    refine hpt _ (mul_mem (mul_mem hyU hxU) hkU) fun P hP => ?_
    let P' : SBof I a := ⟨P, hQsub P hP⟩
    obtain ⟨γ, hγ⟩ := hzf4 P' hP
    refine ⟨γ, fun r s => ?_⟩
    have e1 := mul_comp_eq (cP P) y (show GA B (B.R.N i) from κ.1) (show GA B (B.R.N i) from w.1) (show GA B (B.R.N i) from (zf P').1) kk (hwP P')
    have e2 := congrFun (congrFun e1 r) s
    exact (cP_apply P _ r s).symm.trans (e2.trans ((cP_apply P _ r s).trans (hγ r s)))
  · intro P
    have e : κ.1⁻¹ * (κ * w).1 = w.1 := inv_mul_cancel_left κ.1 w.1
    refine (congrArg (GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P)) e).mpr ?_
    refine ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) ((I.cst a).D P) P w.1).2.2).mpr fun r s => ?_
    have e := entry_eq_of_eq (cP P.1) _ _ (hwP P) r s
    have D2 := ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) ((I.cst a).D P) P (zf P).1).2.2.1 (hzf3 P)) r s
    convert D2 using 3
    exact e

end GlobalTheory.Mem.Col2.AdT.LevelElt

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.NearCong

open WithZero

theorem mul_cong {K : Type} [Field K] (v : Valuation K ℤᵐ⁰) {n : ℕ} (N : ℕ) (A C : Matrix (Fin n) (Fin n) K)
    (hA : ∀ r s, v ((A - 1) r s) ≤ exp (-(N : ℤ))) (hC : ∀ r s, v ((C - 1) r s) ≤ exp (-(N : ℤ))) :
    ∀ r s, v ((A * C - 1) r s) ≤ exp (-(N : ℤ)) := by
  intro r s
  have he : exp (-(N : ℤ)) ≤ 1 := by
    rw [← exp_zero, exp_le_exp]; omega
  have e : A * C - 1 = (A - 1) * (C - 1) + (A - 1) + (C - 1) := by noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  refine v.map_add_le (v.map_add_le ?_ (hA r s)) (hC r s)
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun k _ => ?_
  rw [map_mul]
  calc v ((A - 1) r k) * v ((C - 1) k s) ≤ exp (-(N : ℤ)) * 1 := mul_le_mul' (hA r k) ((hC k s).trans he)
    _ = exp (-(N : ℤ)) := mul_one _

section Rat
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem congE_inv_mul (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (hC : CongE P c g' g) : ∀ x ∈ Formalism.L2.Col.stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x) ∈ Formalism.L2.Col.stdAt E n P := by
  intro x hx
  have hgi : g⁻¹ ∈ Formalism.L2.Col.GLint E n P := inv_mem hg
  have e1 : (g⁻¹ * g') x = g⁻¹ (g' x) := rfl
  have e2 : g⁻¹ (g x) = x := by
    show (g⁻¹ * g) x = x
    rw [inv_mul_cancel]; rfl
  have e : (((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x) = g⁻¹ ((((qOf P : ℕ) : E) ^ c)⁻¹ • (g' x - g x)) := by
    rw [map_smul, map_sub, e1, e2]
  rw [e]
  exact (hgi _).2 (hC x hx)

theorem val_entry (P : HeightOneSpectrum (𝓞 E)) (hq : P.valuation E ((qOf P : ℕ) : E) = exp (-1 : ℤ)) (c : ℕ)
    (h : Sp E n ≃ₗ[E] Sp E n)
    (hh : ∀ x ∈ Formalism.L2.Col.stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • (h x - x) ∈ Formalism.L2.Col.stdAt E n P) (r s : Fin n) :
    P.valuation E (LinearMap.toMatrix' h.toLinearMap r s - (1 : Matrix (Fin n) (Fin n) E) r s) ≤ exp (-(c : ℤ)) := by
  have hx : (Pi.single s (1 : E) : Sp E n) ∈ Formalism.L2.Col.stdAt E n P := by
    rw [GlobalTheory.TwistRowType.mem_stdAt]
    intro k
    rw [Pi.single_apply]
    split_ifs
    · exact (GlobalTheory.TwistRowType.intSub P).one_mem
    · exact (GlobalTheory.TwistRowType.intSub P).zero_mem
  have h1 := (GlobalTheory.TwistRowType.mem_stdAt P _).1 (hh _ hx) r
  rw [GlobalTheory.UnramCompletion.intAt_iff] at h1
  rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply, map_mul, map_inv₀, map_pow, hq] at h1
  have e : LinearMap.toMatrix' h.toLinearMap r s - (1 : Matrix (Fin n) (Fin n) E) r s = h (Pi.single s 1) r - (if r = s then 1 else 0) := by
    rw [LinearMap.toMatrix'_apply, Matrix.one_apply]; rfl
  rw [e]
  generalize P.valuation E (h (Pi.single s 1) r - if r = s then 1 else 0) = y at h1
  have hE : (exp (-1 : ℤ) ^ c)⁻¹ = exp (c : ℤ) := by
    rw [← WithZero.exp_nsmul, ← WithZero.exp_neg]; congr 1; simp
  rw [hE] at h1
  have hm : exp (-(c : ℤ)) * exp (c : ℤ) = 1 := by rw [← exp_add]; simp
  calc y = (exp (-(c : ℤ)) * exp (c : ℤ)) * y := by rw [hm, one_mul]
    _ = exp (-(c : ℤ)) * (exp (c : ℤ) * y) := mul_assoc _ _ _
    _ ≤ exp (-(c : ℤ)) * 1 := mul_le_mul' le_rfl h1
    _ = exp (-(c : ℤ)) := mul_one _

end Rat

section Core
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem vAlg' (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

theorem adAt_ratA (P : HeightOneSpectrum (𝓞 E)) (γ : GL (Fin n) E) (r s : Fin n) :
    adAt F P (((GlobalTheory.TwU.ratA F γ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s) :=
  adAt_inclE F P _

theorem core (P : HeightOneSpectrum (𝓞 E)) (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = exp (-1 : ℤ))
    (hiff : ∀ (N : ℕ) (z : GL (Fin n) (AfE F E)), GlobalTheory.TwU.CongAt P N z ↔
      ∀ r s, Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ exp (-(N : ℤ)))
    (G : (Sp E n ≃ₗ[E] Sp E n) →* GL (Fin n) E)
    (hG : ∀ h r s, (G h : Matrix (Fin n) (Fin n) E) r s = LinearMap.toMatrix' h.toLinearMap r s)
    (c d : ℕ) (hcd : c ≤ d) (x : GL (Fin n) (AfE F E)) (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (h : GlobalTheory.TwU.CongAt P d (x⁻¹ * GlobalTheory.TwU.ratA F (G g))) (hC : CongE P c g' g) :
    GlobalTheory.TwU.CongAt P c (x⁻¹ * GlobalTheory.TwU.ratA F (G g')) := by
  have hq' : P.valuation E ((qOf P : ℕ) : E) = exp (-1 : ℤ) := by
    rw [← vAlg', map_natCast]
    exact hq
  have e : x⁻¹ * GlobalTheory.TwU.ratA F (G g') = (x⁻¹ * GlobalTheory.TwU.ratA F (G g)) * GlobalTheory.TwU.ratA F (G (g⁻¹ * g')) := by
    rw [mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [hiff] at h
  rw [hiff, e]
  have hdc : exp (-(d : ℤ)) ≤ exp (-(c : ℤ)) := by rw [exp_le_exp]; omega
  have key := mul_cong (Valued.v : Valuation (P.adicCompletion E) ℤᵐ⁰) c
    ((adAt F P).mapMatrix ((x⁻¹ * GlobalTheory.TwU.ratA F (G g) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)))
    ((adAt F P).mapMatrix ((GlobalTheory.TwU.ratA F (G (g⁻¹ * g')) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)))
    (fun r s => (h r s).trans hdc) (fun r s => ?_)
  · intro r s
    have := key r s
    rwa [← map_mul, ← Units.val_mul] at this
  · show Valued.v (adAt F P _ - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ _
    rw [adAt_ratA, hG]
    have h1 : (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s = algebraMap E _ ((1 : Matrix (Fin n) (Fin n) E) r s) := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [h1, ← map_sub, vAlg']
    exact val_entry P hq' c _ (congE_inv_mul P c g g' hg hC) r s

end Core

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → CongE P.1 (dep' P) g' g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' := by
  intro B X I hI l Z a i fb dep dep' P κ g g' hg hdep hIn hC
  unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hIn ⊢
  obtain ⟨hseam, hq, -⟩ := GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hI l Z a 0 0 P 1
  have hiff := fun N z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hI l Z a ((I.rec7 l Z).R.N i) N P z).2.2
  rw [hseam] at hIn hiff ⊢
  have i1 : NumberField ↥(I.rec7 l Z).host.F := inferInstance
  have i2 : NumberField (I.rec7 l Z).host.E := inferInstance
  exact @core (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ _ _ P.1 hq hiff (GlobalTheory.TwU.seamGL (sm I l Z)) (fun _ _ _ => rfl) (dep' P) (dep P) hdep _ g g' hg hIn hC

end GlobalTheory.Mem.Col2.AdT.NearCong
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Matrix




namespace GlobalTheory.HLatStd

variable {D : D7} {V : HSp D}

def invM (h : Bridge.Gf V) : Matrix (Fin V.rank) (Fin V.rank) (EAf D) :=
  (Units.val ((h⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D)

def iv (x : Fin V.rank → D.host.E) : Fin V.rank → EAf D := fun i => x i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)

theorem mem_set_iff (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) (x : Fin V.rank → D.host.E) :
    (Units.val ((h⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).mulVec
          (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, (invM h *ᵥ iv x) i ∈ GlobalTheory.StdFrameExist.SI D := by
  rw [GlobalTheory.StdFrameExist.latHat_iff hV]
  refine forall_congr' fun i => ?_
  rw [RingHom.map_mulVec]
  rfl

theorem iv_natCast_smul (N : ℕ) (x : Fin V.rank → D.host.E) : iv ((N : D.host.E) • x) = (N : EAf D) • iv x := by
  funext i
  simp only [iv, Pi.smul_apply, smul_eq_mul]
  rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
    (B := Formalism.L2.Herm.Af D.host.F)) N]
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem iv_mem_of_int {x : Fin V.rank → D.host.E} (hx : ∀ i, IsIntegral ℤ (x i)) (i : Fin V.rank) :
    iv x i ∈ GlobalTheory.StdFrameExist.SI D := by
  obtain ⟨o, ho⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 (hx i)
  show x i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ _
  rw [← ho]
  exact GlobalTheory.StdFrameExist.tmul_one_mem o

theorem int_of_iv_mem {e : D.host.E} (he : (e ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) : EAf D) ∈ GlobalTheory.StdFrameExist.SI D) :
    IsIntegral ℤ e := by
  rw [← GlobalTheory.StdFrameExist.mem_ALint_iff] at he
  exact GlobalTheory.StabFin.isIntegral_of_mem e he

theorem mulVec_natCast_smul (M : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) (N : ℕ) (z : Fin V.rank → EAf D) :
    M *ᵥ ((N : EAf D) • z) = ((N : EAf D) • M) *ᵥ z := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem invM_mul (h : Bridge.Gf V) :
    (Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D) * invM h = 1 := by
  rw [invM, ← Matrix.map_mul, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem invM_hmul (h x : Bridge.Gf V) : invM (h * x) = invM x * invM h := by
  rw [invM, invM, invM, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Matrix.map_mul]

theorem fg_of_le_fg {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {P Q : Submodule R M} (hQ : Q.FG) (hPQ : P ≤ Q) : P.FG := by
  haveI := isNoetherian_of_fg_of_noetherian Q hQ
  have h1 : (P.comap Q.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map Q.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hPQ] at h2

theorem mem_hLat_of (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) {x : Fin V.rank → D.host.E}
    (hx : ∀ i, (invM h *ᵥ iv x) i ∈ GlobalTheory.StdFrameExist.SI D) : x ∈ Bridge.hLat V h :=
  Submodule.subset_span ((mem_set_iff hV h x).2 hx)

theorem isLattice (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) : Submodule.IsLattice D.host.E (Bridge.hLat V h) := by
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    ((Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D))
  obtain ⟨N₁, hN₁, hN₁m⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    (invM h)
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  apply Submodule.IsLattice.of_fg D.host.E
  ·
    let T : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
      Submodule.span (𝓞 D.host.E) (Set.range fun j : Fin V.rank => (N : D.host.E)⁻¹ • (Pi.single j (1 : D.host.E)))
    refine fg_of_le_fg (Q := T) (Submodule.fg_span (Set.finite_range _)) (Submodule.span_le.2 fun x hx => ?_)
    have hx' := (mem_set_iff hV h x).1 hx
    have hint : ∀ i, IsIntegral ℤ ((N : D.host.E) * x i) := by
      intro i
      refine int_of_iv_mem ?_
      have e1 : ((N : D.host.E) * x i) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) =
          (((N : EAf D) • (Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D))
            *ᵥ (invM h *ᵥ iv x)) i := by
        rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, invM_mul, Matrix.one_mulVec, ← iv_natCast_smul]
        rfl
      rw [e1]
      exact GlobalTheory.StdFrameExist.intV (fun a b => by rw [Matrix.smul_apply, smul_eq_mul]; exact hNm a b) hx' i
    choose c hc using fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 (hint i)
    refine (Submodule.mem_span_range_iff_exists_fun (𝓞 D.host.E)).2 ⟨c, ?_⟩
    funext l
    rw [Finset.sum_apply, Finset.sum_eq_single l]
    · rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, smul_eq_mul, mul_one, hc]
      field_simp
    · intro b _ hb
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero, smul_zero]
    · simp

theorem smul_mem_hLat_mul (hV : Seed.FrmC.StdLat V) (h x : Bridge.Gf V) (p : ℕ)
    (hp : ∀ a b, (p : EAf D) * swapAE D ((x⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∀ y ∈ Bridge.hLat V h, (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x) := by
  have hA : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) ((p : EAf D) • invM x) := fun a b => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hp a b
  have key : ∀ y, (∀ i, (invM h *ᵥ iv y) i ∈ GlobalTheory.StdFrameExist.SI D) → (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x) := by
    intro y hy
    refine mem_hLat_of hV _ fun i => ?_
    have e : (p : 𝓞 D.host.E) • y = (p : D.host.E) • y := by rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [e, iv_natCast_smul, mulVec_natCast_smul, invM_hmul, ← Matrix.smul_mul, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.StdFrameExist.intV hA hy i
  intro y hy
  have hle : Bridge.hLat V h ≤ (Bridge.hLat V (h * x)).comap ((p : 𝓞 D.host.E) • LinearMap.id) :=
    Submodule.span_le.2 fun y hy => key y ((mem_set_iff hV h y).1 hy)
  exact hle hy

theorem ratF_val (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    Units.val ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) =
      γE.val.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E) := by
  show Units.val (finHom V (γ : GA D V)) = _
  rw [finHom, MonoidHom.comp_apply, hγ]
  ext i j
  simp only [Formalism.UG.bc, incA]
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) ((1 : AF D.host.F) ⊗ₜ[D.host.F] (γE.val i j)) =
    (1 : Af D.host.F) ⊗ₜ[D.host.F] γE.val i j
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem gl_cancel {R : Type} [CommRing R] {n : ℕ} (a b : GL (Fin n) R) (v : Fin n → R) :
    Units.val (b * a)⁻¹ *ᵥ (b.val *ᵥ v) = Units.val a⁻¹ *ᵥ v := by
  rw [Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem vec_move (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) (y : Fin V.rank → D.host.E) :
    (Units.val ((Bridge.ratF V γ * h)⁻¹ : Bridge.Gf V).1) *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] (γE.val *ᵥ y) i) =
      (Units.val (h⁻¹ : Bridge.Gf V).1) *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] y i) := by
  have hv : (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] (γE.val *ᵥ y) i) =
      Units.val ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ
        (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] y i) := by
    rw [ratF_val γ γE hγ]
    funext i
    exact RingHom.map_mulVec (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E).toRingHom γE.val y i
  rw [hv]
  exact gl_cancel ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) _

theorem mulVec_mem_hLat (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) : ∀ y ∈ Bridge.hLat V h, γE.val *ᵥ y ∈ Bridge.hLat V (Bridge.ratF V γ * h) := by
  intro y hy
  have hle : Bridge.hLat V h ≤ (Bridge.hLat V (Bridge.ratF V γ * h)).comap
      ((Matrix.mulVecLin γE.val).restrictScalars (𝓞 D.host.E)) :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span (show _ ∈ latHat D.host.F D.host.E (L0c D V) by
      rw [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, vec_move γ γE hγ h y]
      exact hy)
  exact hle hy

theorem isRatMat_inv (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    Bridge.IsRatMat V γ⁻¹ γE⁻¹ := by
  unfold Bridge.IsRatMat at *
  rw [Subgroup.coe_inv, map_inv, map_inv, hγ]

theorem mem_hLat_iff (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) (y : Fin V.rank → D.host.E) :
    y ∈ Bridge.hLat V h ↔ γE.val *ᵥ y ∈ Bridge.hLat V (Bridge.ratF V γ * h) := by
  refine ⟨mulVec_mem_hLat γ γE hγ h y, fun hy => ?_⟩
  have := mulVec_mem_hLat γ⁻¹ γE⁻¹ (isRatMat_inv γ γE hγ) _ _ hy
  have e1 : Units.val γE⁻¹ *ᵥ (γE.val *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have e2 : Bridge.ratF V γ⁻¹ * (Bridge.ratF V γ * h) = h := by rw [map_inv, inv_mul_cancel_left]
  rw [e1, e2] at this
  exact this

theorem hLat_props : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → (∀ h, Submodule.IsLattice D.host.E (Bridge.hLat V h)) ∧ (∀ (h x : Bridge.Gf V) (p : ℕ), (∀ a b, (p : EAf D) * swapAE D ((x⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ y ∈ Bridge.hLat V h, (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x)) ∧ ∀ (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → ∀ h y, y ∈ Bridge.hLat V h ↔ γE.val.mulVec y ∈ Bridge.hLat V (Bridge.ratF V γ * h) :=
  fun _ _ hV => ⟨isLattice hV, smul_mem_hLat_mul hV, mem_hLat_iff⟩

end GlobalTheory.HLatStd
end
end
