module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle295
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Filter.Cofinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.CharpolyDvdOfAevalEqZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.ConjugateSelfReciprocalCharpoly
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.NormEq

open GlobalTheory.UTr GroundTheory.LocalField

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem sigO_piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : sigO σ h.2.1 (piO h) = piO h :=
  Subtype.ext h.2.2.1

theorem conj_mem_piPow {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : Csr (sigO σ h.2.1)) (m : ℕ)
    {a : Alg P} (ha : a ∈ piPow h P m) : conj P a ∈ piPow h P m := by
  set_option backward.isDefEq.respectTransparency false in
    unfold piPow at *
    simp only [Ideal.mem_span_singleton] at ha ⊢
    obtain ⟨b, rfl⟩ := ha
    have hp : conj P (algebraMap (intL L) (Alg P) (piO h)) = algebraMap (intL L) (Alg P) (piO h) :=
      (GlobalTheory.UTr.conj_algebraMap P _).trans (congrArg _ (sigO_piO h))
    exact ⟨conj P b, by
      rw [map_mul, map_pow]
      exact congrArg (fun x : Alg P => x ^ m * conj P b) hp⟩

theorem normU_mem_filt {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : Csr (sigO σ h.2.1)) (m : ℕ)
    {g : (Alg P)ˣ} (hg : g ∈ filt h P m) : normU P g ∈ filt h P m := by
  set_option backward.isDefEq.respectTransparency false in
    change (g : Alg P) - 1 ∈ piPow h P m at hg
    change ((normU P g : (Alg P)ˣ) : Alg P) - 1 ∈ piPow h P m
    have hc : conj P (g : Alg P) - 1 ∈ piPow h P m := by
      have := conj_mem_piPow h P m hg
      rwa [map_sub, map_one] at this
    have e : ((normU P g : (Alg P)ˣ) : Alg P) - 1 = ((g : Alg P) - 1) * conj P (g : Alg P) + (conj P (g : Alg P) - 1) := by
      rw [val_normU]; ring
    rw [e]
    exact (piPow h P m).add_mem ((piPow h P m).mul_mem_right _ hg) hc

theorem div_mem_of_sub_mem {R : Type} [CommRing R] {I : Ideal R} {x u : Rˣ} (hx : (x : R) - u ∈ I) :
    ((x / u : Rˣ) : R) - 1 ∈ I := by
  have e : ((x / u : Rˣ) : R) - 1 = ((x : R) - u) * ((u⁻¹ : Rˣ) : R) := by
    rw [div_eq_mul_inv, Units.val_mul, sub_mul, Units.mul_inv]
  rw [e]; exact I.mul_mem_right _ hx

theorem normU_surj (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : Csr (sigO σ h.2.1)) (hP : P.1.Separable)
    (x : (Alg P)ˣ) (hx : x ∈ plus P) : ∃ u : (Alg P)ˣ, normU P u = x := by
  have hs : ∀ b, sigO σ h.2.1 (sigO σ h.2.1 b) = b := fun b => Subtype.ext (h.1 b)
  let f : (Alg P)ˣ →* plus P := (normU P).codRestrict (plus P) (normU_mem_plus P hs)
  let E : ℕ → Subgroup (plus P) := fun m => (filt h P m).comap (plus P).subtype
  have hE : Antitone E := fun a b hab => Subgroup.comap_mono (filt_antitone h P hab)
  have hsepE : FiltrationSeparated E := by
    intro g hg
    have h0 : ((g : (Alg P)ˣ) : Alg P) - 1 = 0 := GlobalTheory.T.eq_zero_of_mem_all_powers L σ ϖ q h P _ fun m => hg m
    exact Subtype.ext (Units.ext (sub_eq_zero.1 h0))
  have hE0 : E (id 0) = ⊤ := by
    ext g; change ((g : (Alg P)ˣ) ∈ filt h P 0) ↔ True
    rw [filt_zero]; exact ⟨fun _ => trivial, fun _ => Subgroup.mem_top _⟩
  have hmap : ∀ n, ∀ g ∈ filt h P n, f g ∈ E (id n) := fun n g hg => normU_mem_filt h P n hg
  have hgr : ∀ n, ∀ z ∈ E (id n), ∃ g ∈ filt h P n, z / f g ∈ E (id (n + 1)) := by
    intro n z hz
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨u, hu⟩ := GlobalTheory.T.norm_approximation_first_level L σ ϖ q h P hP z.1 z.2
      refine ⟨u, by rw [filt_zero]; exact Subgroup.mem_top u, ?_⟩
      show ((z.1 / normU P u : (Alg P)ˣ) : Alg P) - 1 ∈ piPow h P (0 + 1)
      exact div_mem_of_sub_mem hu
    · obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.norm_approximation_filtration L σ ϖ q h P n hn z.1 z.2 hz
      refine ⟨u, hu, ?_⟩
      show ((z.1 / normU P u : (Alg P)ˣ) : Alg P) - 1 ∈ piPow h P (n + 1)
      exact div_mem_of_sub_mem hu'
  obtain ⟨u, hu⟩ := surjective_of_graded_surjective (F := filt h P) (E := E) (filt_antitone h P) hE
    (GlobalTheory.T.norm_filtration_complete L σ ϖ q h P) hsepE f tendsto_id (filt_zero h P) hE0 hmap hgr ⟨x, hx⟩
  exact ⟨u, congrArg Subtype.val hu⟩

end GlobalTheory.NormEq

namespace GlobalTheory.NormEq
open GlobalTheory.UTr

theorem hermUnit_eq_norm : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (y : Matrix (Fin n) (Fin n) L) (Q₀ : (intL L)[X]), (∀ i j, y i j ∈ intL L) → cT σ y * y = 1 → y.charpoly = Q₀.map (intL L).subtype → Q₀.Separable → ∀ t : GL (Fin n) L, (∀ i j, t.val i j ∈ intL L) → (∀ i j, (t⁻¹ : GL (Fin n) L).val i j ∈ intL L) → cT σ t.val = t.val → (∃ p : (intL L)[X], t.val = aeval y (p.map (intL L).subtype)) → ∃ s : GL (Fin n) L, s.val * y = y * s.val ∧ s.val * cT σ s.val = t.val := by
  intro L _ _ _ σ ϖ q h n y Q₀ hy hyu hch hsep t ht hti htc ⟨p, hp⟩
  let sO := sigO σ h.2.1
  let Φ : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L := (intL L).subtype.mapMatrix
  have hΦinj : Function.Injective Φ := fun a b hab => by
    ext i j; exact congrFun (congrFun hab i) j
  let yO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨y i j, hy i j⟩
  have hyO : Φ yO = y := rfl
  have hΦcT : ∀ M, Φ (cT sO M) = cT σ (Φ M) := fun M => rfl
  have hchO : yO.charpoly = Q₀ := by
    apply Polynomial.map_injective _ (intL L).subtype_injective
    rw [← hch, ← hyO]
    exact (Matrix.charpoly_map yO (intL L).subtype).symm
  have hyuO : cT sO yO * yO = 1 := hΦinj (by rw [map_mul, hΦcT, hyO, hyu, map_one])
  have hcsr : IsCsr sO Q₀ := hchO ▸ GlobalTheory.T.conjugate_self_reciprocal_charpoly _ sO n yO hyuO
  let P : Csr sO := ⟨Q₀, hcsr⟩
  have hg : aeval yO P.1 = 0 := by
    show aeval yO Q₀ = 0
    rw [← hchO]; exact Matrix.aeval_self_charpoly yO
  let ev := evalMat P yO hg
  have hev : ∀ r : (intL L)[X], ev (aeval (root P) r) = aeval yO r := fun r => by
    rw [← aeval_algHom_apply, evalMat_root]
  have hevinj : ∀ z, ev z = 0 → z = 0 := by
    intro z hz
    obtain ⟨r, rfl⟩ := exists_aeval_root P z
    rw [hev] at hz
    have hd := GlobalTheory.T.charpoly_dvd_of_aeval_eq_zero_alt (intL L) n yO r (hchO ▸ hsep) hz
    rw [hchO] at hd
    exact (aeval_root_eq_zero_iff P).2 hd
  have hevinj' : Function.Injective ev := (injective_iff_map_eq_zero ev).2 hevinj
  have hcomp : Φ.comp (algebraMap (intL L) (Matrix (Fin n) (Fin n) (intL L))) =
      (algebraMap L (Matrix (Fin n) (Fin n) L)).comp (intL L).subtype := by
    ext a i j
    simp only [RingHom.coe_comp, Function.comp_apply, Φ, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp
  have hΦaeval : ∀ r : (intL L)[X], Φ (aeval yO r) = aeval y (r.map (intL L).subtype) := by
    intro r
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, eval₂_map, hcomp, hyO]

  let tz : Alg P := aeval (root P) p
  let tO := ev tz
  have htO : Φ tO = t.val := by rw [show tO = aeval yO p from hev p, hΦaeval, hp]
  let tiO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨(t⁻¹ : GL (Fin n) L).val i j, hti i j⟩
  have htiO : tO * tiO = 1 := hΦinj (by
    rw [map_mul, htO, map_one]; exact t.mul_inv)
  have hdet : IsUnit tO.det := isUnit_iff_exists_inv.2 ⟨tiO.det, by rw [← Matrix.det_mul, htiO, Matrix.det_one]⟩
  have hunit : IsUnit tz := by
    have h0 : aeval tz tO.charpoly = 0 := hevinj _ (by
      rw [← aeval_algHom_apply]; exact Matrix.aeval_self_charpoly tO)
    have hc0 : IsUnit (tO.charpoly.coeff 0) := by
      have := Matrix.det_eq_sign_charpoly_coeff tO
      rw [this] at hdet
      exact isUnit_of_mul_isUnit_right hdet
    have e := congrArg (aeval tz) (X_mul_divX_add tO.charpoly)
    rw [h0, map_add (f := _), map_mul, aeval_X, aeval_C] at e
    have hu : IsUnit (tz * aeval tz tO.charpoly.divX) := by
      rw [eq_neg_of_add_eq_zero_left e]
      exact (hc0.map _).neg
    exact isUnit_of_mul_isUnit_left hu
  let T : (Alg P)ˣ := hunit.unit

  have hyuO' : yO * cT sO yO = 1 := mul_eq_one_comm.1 hyuO
  let gU : UJ sO (1 : Matrix (Fin n) (Fin n) (intL L)) :=
    ⟨⟨yO, cT sO yO, hyuO', hyuO⟩, by
      show cT sO yO * 1 * yO = 1
      rw [Matrix.mul_one, hyuO]⟩
  have hcT : ∀ z, cT sO (ev z) = ev (conj P z) := fun z => by
    have := cT_evalMat P gU hg z
    rwa [Matrix.mul_one, Matrix.one_mul] at this
  have htz : conj P tz = tz := hevinj' (by
    rw [← hcT]
    exact hΦinj (by rw [hΦcT, htO, htc]))
  have hT : T ∈ plus P := (GlobalTheory.UTr.mem_plus (P := P)).2 htz
  obtain ⟨u, hu⟩ := normU_surj L σ ϖ q h P hsep T hT
  let Ψ : Alg P →* Matrix (Fin n) (Fin n) L := (Φ.comp ev.toRingHom : Alg P →+* _)
  refine ⟨Units.map Ψ u, ?_, ?_⟩
  · show Φ (ev u) * y = y * Φ (ev u)
    rw [← hyO, ← map_mul, ← map_mul]
    congr 1
    rw [← evalMat_root P yO hg, ← map_mul, ← map_mul, mul_comm]
  · show Φ (ev u) * cT σ (Φ (ev u)) = t.val
    rw [← hΦcT, hcT, ← map_mul, ← map_mul, ← val_normU, hu, ← htO]
    rfl

end GlobalTheory.NormEq
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finprod_mem_eq_zero_of_factor {ι : Type} (f : ι → ℂ) (S : Set ι)
    (hfin : {w | f w ≠ 1}.Finite) {w₀ : ι} (hw₀ : w₀ ∈ S) (h0 : f w₀ = 0) :
    ∏ᶠ w ∈ S, f w = 0 := by
  have hs : (S ∩ Function.mulSupport f).Finite := hfin.subset fun w hw => hw.2
  rw [finprod_mem_eq_prod f hs]
  refine Finset.prod_eq_zero (i := w₀) ?_ h0
  rw [Set.Finite.mem_toFinset]
  refine ⟨hw₀, ?_⟩
  rw [Function.mem_mulSupport, h0]
  exact zero_ne_one

theorem finsum_finprod_local_sums_expand : ∀ (ι : Type) (S : Set ι) (Cl : ι → Type) [∀ w, Finite (Cl w)] (D R : Type) [Finite D] (loc : R → ∀ w, Cl w) (O : ∀ w, Cl w → ℂ) (s : D → ∀ w, Cl w → ℂ) (good : ∀ w, Cl w → Prop) (N : ℂ), (∀ᶠ w in (cofinite : Filter ι), (∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) → (∀ w, w ∉ S → Nonempty (Cl w)) → (∀ r, ∀ᶠ w in (cofinite : Filter ι), good w (loc r w)) → (∀ r r', (∀ w ∈ S, loc r w = loc r' w) → r = r') → (∀ x : ∀ w, Cl w, (∀ᶠ w in (cofinite : Filter ι), good w (x w)) → ∑ᶠ d : D, ∏ᶠ w ∈ S, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = x w then N else 0) → (Function.support fun r : R => ∏ᶠ w ∈ S, O w (loc r w)).Finite ∧ (∑ᶠ r : R, ∏ᶠ w ∈ S, O w (loc r w)) * N = ∑ᶠ d : D, ∏ᶠ w ∈ S, ∑ᶠ c : Cl w, s d w c * O w c := by
  intro ι S Cl _ D R _ loc O s good N hA hB hC hD hE
  classical
  haveI : ∀ w, Fintype (Cl w) := fun w => Fintype.ofFinite _
  haveI : Fintype D := Fintype.ofFinite D
  obtain ⟨T, hTfin, hTA⟩ : ∃ T : Set ι, T.Finite ∧ ∀ w, w ∉ T →
      ((∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) :=
    ⟨_, Filter.eventually_cofinite.1 hA, fun w hw => not_not.1 hw⟩
  have hO : ∀ w, w ∉ T → ∀ c, O w c = if good w c then 1 else 0 := fun w hw c => ((hTA w hw).2 c).1
  have hs1 : ∀ w, w ∉ T → ∀ c, good w c → ∀ d, s d w c = 1 := fun w hw c => ((hTA w hw).2 c).2
  have huniq : ∀ w, w ∉ T → ∀ c c', good w c → good w c' → c = c' :=
    fun w hw c c' hc hc' => (hTA w hw).1.unique hc hc'
  obtain ⟨F, hF⟩ : ∃ F : Finset ι, ∀ w, w ∈ F ↔ w ∈ S ∧ w ∈ T :=
    ⟨hTfin.toFinset.filter (· ∈ S), fun w => by simp [and_comm]⟩
  obtain ⟨ext, ext_F, ext_good⟩ : ∃ ext : (∀ w : F, Cl w) → ∀ w, Cl w,
      (∀ x (w : F), ext x w = x w) ∧ ∀ x w, w ∉ T → good w (ext x w) := by
    refine ⟨fun x w => if h : w ∈ F then x ⟨w, h⟩ else if hw : w ∈ T then
      (hB w (fun hS => h ((hF w).2 ⟨hS, hw⟩))).some else (hTA w hw).1.exists.choose,
      fun x w => dif_pos w.2, fun x w hw => ?_⟩
    have hwF : w ∉ F := fun h => hw ((hF w).1 h).2
    simp only [dif_neg hwF, dif_neg hw]
    exact (hTA w hw).1.exists.choose_spec
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : R → ∀ w : F, Cl w, ∀ r (w : F), ρ r w = loc r w :=
    ⟨fun r w => loc r w, fun _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Set R, ∀ r, r ∈ G ↔ ∀ w ∈ S, w ∉ T → good w (loc r w) :=
    ⟨{r | ∀ w ∈ S, w ∉ T → good w (loc r w)}, fun _ => Iff.rfl⟩
  have prodS : ∀ φ : ι → ℂ, (∀ w ∈ S, w ∉ T → φ w = 1) → ∏ᶠ w ∈ S, φ w = ∏ w : F, φ w := by
    intro φ hφ
    have h1 : S ∩ Function.mulSupport φ ⊆ (F : Set ι) := by
      rintro w ⟨hwS, hw1⟩
      by_contra hwF
      exact hw1 (hφ w hwS fun hT => hwF (Finset.mem_coe.2 ((hF w).2 ⟨hwS, hT⟩)))
    have h2 : (F : Set ι) ⊆ S := fun w hw => ((hF w).1 (Finset.mem_coe.1 hw)).1
    rw [finprod_mem_eq_prod_of_subset φ h1 h2, ← Finset.prod_coe_sort]
  have hR : ∀ d, ∏ᶠ w ∈ S, ∑ᶠ c, s d w c * O w c =
      ∑ x : (∀ w : F, Cl w), (∏ w : F, s d w (x w)) * ∏ w : F, O w (x w) := by
    intro d
    rw [prodS]
    · simp only [finsum_eq_sum_of_fintype]
      rw [Fintype.prod_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.prod_mul_distrib
    · intro w _ hw
      obtain ⟨c0, hc0⟩ := (hTA w hw).1.exists
      rw [finsum_eq_sum_of_fintype, Finset.sum_eq_single c0]
      · rw [hO w hw c0, if_pos hc0, hs1 w hw c0 hc0 d, mul_one]
      · intro c _ hc
        rw [hO w hw c, if_neg (fun hg => hc (huniq w hw c c0 hg hc0)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ c0) h
  have hs_ext : ∀ d x, ∏ᶠ w ∈ S, s d w (ext x w) = ∏ w : F, s d w (x w) := by
    intro d x
    rw [prodS]
    · exact Finset.prod_congr rfl fun w _ => by rw [ext_F]
    · intro w _ hw
      exact hs1 w hw _ (ext_good x w hw) d
  have hEx : ∀ x, ∑ d, ∏ w : F, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = ext x w then N else 0 := by
    intro x
    rw [← hE (ext x) ?_, finsum_eq_sum_of_fintype]
    · exact Finset.sum_congr rfl fun d _ => (hs_ext d x).symm
    · exact Filter.eventually_cofinite.2 (hTfin.subset fun w hw => by_contra fun hwT => hw (ext_good x w hwT))
  have hρ : ∀ r ∈ G, ∀ w ∈ S, loc r w = ext (ρ r) w := by
    intro r hr w hwS
    by_cases hwF : w ∈ F
    · have h := ext_F (ρ r) ⟨w, hwF⟩
      rw [hρdef] at h
      exact h.symm
    · have hwT : w ∉ T := fun hT => hwF ((hF w).2 ⟨hwS, hT⟩)
      exact huniq w hwT _ _ ((hG r).1 hr w hwS hwT) (ext_good _ w hwT)
  have hρinj : Set.InjOn ρ G := by
    intro r hr r' hr' h
    apply hD
    intro w hwS
    rw [hρ r hr w hwS, hρ r' hr' w hwS, h]
  have hP0 : ∀ r, r ∉ G → ∏ᶠ w ∈ S, O w (loc r w) = 0 := by
    intro r hr
    rw [hG] at hr
    push_neg at hr
    obtain ⟨w, hwS, hwT, hg⟩ := hr
    refine finprod_mem_eq_zero_of_factor _ S ?_ hwS ?_
    · refine (hTfin.union (Filter.eventually_cofinite.1 (hC r))).subset fun v hv => ?_
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
      exact hv (by rw [hO v hcon.1, if_pos hcon.2])
    · rw [hO w hwT, if_neg hg]
  have hP1 : ∀ r ∈ G, ∏ᶠ w ∈ S, O w (loc r w) = ∏ w : F, O w (ρ r w) := by
    intro r hr
    rw [prodS]
    · exact Finset.prod_congr rfl fun w _ => by rw [hρdef]
    · intro w hwS hwT
      rw [hO w hwT, if_pos ((hG r).1 hr w hwS hwT)]
  have hGfin : G.Finite := Set.Finite.of_finite_image (Set.toFinite _) hρinj
  have hmem : ∀ x, x ∈ ρ '' G ↔ ∃ r, ∀ w ∈ S, loc r w = ext x w := by
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hρ r hr⟩
    · rintro ⟨r, hr⟩
      refine ⟨r, ?_, ?_⟩
      · rw [hG]
        intro w hwS hwT
        rw [hr w hwS]
        exact ext_good x w hwT
      · funext w
        rw [hρdef, hr w ((hF w).1 w.2).1, ext_F]
  have hsum : ∑ᶠ r, ∏ᶠ w ∈ S, O w (loc r w) =
      ∑ x : (∀ w : F, Cl w), if ∃ r, ∀ w ∈ S, loc r w = ext x w then ∏ w : F, O w (x w) else 0 := by
    calc ∑ᶠ r, ∏ᶠ w ∈ S, O w (loc r w) = ∑ᶠ r ∈ G, ∏ w : F, O w (ρ r w) := by
          rw [finsum_mem_def]
          apply finsum_congr
          intro r
          by_cases hr : r ∈ G
          · simp only [Set.indicator_apply, hr, if_true]
            exact hP1 r hr
          · simp only [Set.indicator_apply, hr, if_false]
            exact hP0 r hr
      _ = ∑ᶠ x ∈ ρ '' G, ∏ w : F, O w (x w) :=
          (finsum_mem_image (f := fun x : (∀ w : F, Cl w) => ∏ w : F, O w (x w)) hρinj).symm
      _ = _ := by
          rw [finsum_mem_def, finsum_eq_sum_of_fintype]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Set.indicator_apply, hmem]
  refine ⟨hGfin.subset fun r hr => by_contra fun hrG => hr (hP0 r hrG), ?_⟩
  rw [hsum, finsum_congr hR, finsum_eq_sum_of_fintype, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul, hEx x]
  split_ifs <;> ring

end GlobalTheory
end
