module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle444
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle428
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle445
public import GroundTheory.AutomorphicForms.Bundle017
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_sum_invariant_unipotent_translate : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω,
  PositivityTheory.GramSchwartzFunctions.HidaSetting D n V ψ χ θ μ ω →
  ∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 →
  ∀ Φ : schwartzA θ V.rank n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g b hg Φ
  obtain ⟨-, -, hψ, -, -, -, -, hW⟩ := hS
  refine tsum_congr fun ξ => ?_
  have hmul : (b.map (incA D) * inner V (ξ.map (incA D)) (ξ.map (incA D)) : Mx D n n) =
      (b * (ξᴴ * (V.gram * ξ))).map (incA D) := by
    change rat b * (adj (rat ξ) * (gA V * rat ξ)) = rat (b * (ξᴴ * (V.gram * ξ)))
    rw [rat_mul, rat_mul, rat_mul, rat_conjTranspose, gA]
  have htrace (M : Matrix (Fin n) (Fin n) D.host.E) :
      Matrix.trace (M.map (incA D)) = incA D (Matrix.trace M) := by

    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rw [hW.unip g (b.map (incA D)) hg Φ (ξ.map (incA D)), hmul, htrace,
    GlobalTheory.CompanionTheory.ThetaInv.halfTr_incA, hψ.2.2.1, one_mul]
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.Signs

theorem sMeet_single_single {m : ℕ} {j k : Fin m} (hjk : j ≠ k) (x y : SignType) :
    sMeet (Pi.single j x) (Pi.single k y) = (0 : Fin m → SignType) := by
  funext i
  unfold sMeet
  by_cases hij : i = j
  · subst hij
    have h1 : (Pi.single k y : Fin m → SignType) i = 0 := Pi.single_eq_of_ne hjk _
    rw [h1, Pi.single_eq_same]
    by_cases hx : x = 0 <;> simp [hx]
  · have h1 : (Pi.single j x : Fin m → SignType) i = 0 := Pi.single_eq_of_ne hij _
    rw [h1]
    simp

theorem sLe_single {m : ℕ} (e : Fin m → SignType) (j : Fin m) : SLe (Pi.single j (e j)) e := by
  intro i hi
  by_cases hij : i = j
  · subst hij
    simp
  · exact absurd (Pi.single_eq_of_ne hij _) hi

theorem sLe_of_sMeet {m : ℕ} {e e' : Fin m → SignType} (h : sMeet e e' = e) : SLe e e' := by
  intro i hi
  have h1 := congrFun h i
  unfold sMeet at h1
  by_cases h2 : e i = e' i
  · exact h2.symm
  · rw [if_neg h2] at h1
    exact absurd h1.symm hi

theorem eq_neg_one_of {x : SignType} : x ≠ 0 → x ≠ 1 → x = -1 := by
  revert x
  decide

variable {R : Type} [CommRing R] (σ : R →+* R) {m : ℕ} (P : (Fin m → SignType) → R)

theorem additive (hP2 : ∀ e, P e * P e = P e) (hiso : ∀ e, P e * σ (P e) = 0)
    (hsurj : ∀ p, p * p = p → p * σ p = 0 → ∃ e, P e = p) (hinj : Function.Injective P) (hP0 : P 0 = 0)
    (hmeet : ∀ e e', P (sMeet e e') = P e * P e') (hle : ∀ e e', SLe e e' → P e * P e' = P e)
    (e : Fin m → SignType) : P e = ∑ j, P (Pi.single j (e j)) := by
  set a : Fin m → Fin m → SignType := fun j => Pi.single j (e j) with ha
  have h2 : ∀ j k, j ≠ k → P (a j) * P (a k) = 0 := by
    intro j k hjk
    rw [← hmeet, ha]
    simp only
    rw [sMeet_single_single hjk, hP0]
  have h4 : ∀ j, P (a j) * P e = P (a j) := fun j => hle _ _ (sLe_single e j)
  set q : R := ∑ j, P (a j) with hq
  have h5 : ∀ j, P (a j) * q = P (a j) := by
    intro j
    rw [hq, Finset.mul_sum, Finset.sum_eq_single j (fun k _ hk => h2 j k hk.symm)
      (fun h => absurd (Finset.mem_univ j) h), hP2]
  have hqq : q * q = q := by
    conv_lhs => rw [hq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => h5 j
  have hqe : q * P e = q := by
    conv_lhs => rw [hq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => h4 j
  have hPe := hP2 e
  set r : R := P e - q with hr
  have hrr : r * r = r := by
    rw [hr]
    linear_combination hPe - 2 * hqe + hqq
  have hre : r * P e = r := by
    rw [hr]
    linear_combination hPe - hqe
  have hrs : r * σ r = 0 := by
    calc r * σ r = (r * P e) * σ (r * P e) := by rw [hre]
      _ = r * σ r * (P e * σ (P e)) := by rw [map_mul]; ring
      _ = 0 := by rw [hiso, mul_zero]
  obtain ⟨e', he'⟩ := hsurj r hrr hrs
  have hm : sMeet e' e = e' := hinj (by rw [hmeet, he', hre])
  have hse : SLe e' e := sLe_of_sMeet hm
  have he0 : e' = 0 := by
    funext j
    by_contra hne
    have hne' : e' j ≠ 0 := hne
    have hej : e j = e' j := hse j hne'
    have hs : SLe (a j) e' := by
      intro i hi
      by_cases hij : i = j
      · subst hij
        simp [ha, hej]
      · exact absurd (Pi.single_eq_of_ne hij _) hi
    have h6 : P (a j) * r = P (a j) := by
      rw [← he']
      exact hle _ _ hs
    have h7 : P (a j) * r = 0 := by
      rw [hr, mul_sub, h4, h5, sub_self]
    have h8 : a j = 0 := hinj (by rw [hP0, ← h6, h7])
    have h9 := congrFun h8 j
    simp only [ha, Pi.single_eq_same, Pi.zero_apply] at h9
    exact hne' (hej ▸ h9)
  have hr0 : r = 0 := by rw [← he', he0, hP0]
  exact sub_eq_zero.1 hr0

theorem conj_single (hσ : ∀ x, σ (σ x) = x) (hP2 : ∀ e, P e * P e = P e) (hiso : ∀ e, P e * σ (P e) = 0)
    (hsurj : ∀ p, p * p = p → p * σ p = 0 → ∃ e, P e = p) (hinj : Function.Injective P) (hP0 : P 0 = 0)
    (hle : ∀ e e', SLe e e' → P e * P e' = P e) (j : Fin m) :
    P (Pi.single j (-1)) = σ (P (Pi.single j 1)) := by
  set δ : Fin m → SignType := Pi.single j 1 with hδ
  have hδ0 : δ ≠ 0 := by
    intro h
    have h1 := congrFun h j
    simp [hδ] at h1
  set p : R := P δ with hp
  set s : R := σ p with hs
  have hpp : p * p = p := hP2 δ
  have hps : p * s = 0 := hiso δ
  have hss : s * s = s := by rw [hs, ← map_mul, hpp]
  have hsp : σ s = p := hσ p
  have hsσ : s * σ s = 0 := by rw [hsp, mul_comm, hps]
  obtain ⟨e'', he''⟩ := hsurj s hss hsσ
  have hsupp : ∀ k, k ≠ j → e'' k = 0 := by
    intro k hkj
    by_contra hne
    set β : Fin m → SignType := Pi.single k (e'' k) with hβ
    set c : Fin m → SignType := Function.update δ k (e'' k) with hc
    have hδc : SLe δ c := by
      intro i hi
      have hik : i ≠ k := by
        rintro rfl
        exact hi (Pi.single_eq_of_ne hkj _)
      exact Function.update_of_ne hik _ _
    have hβc : SLe β c := by
      intro i hi
      by_cases hik : i = k
      · subst hik
        simp [hβ, hc]
      · exact absurd (Pi.single_eq_of_ne hik _) hi
    have h1 : p * σ (P β) = 0 := by
      calc p * σ (P β) = (p * P c) * σ (P β * P c) := by rw [hp, hle _ _ hδc, hle _ _ hβc]
        _ = p * σ (P β) * (P c * σ (P c)) := by rw [map_mul]; ring
        _ = 0 := by rw [hiso, mul_zero]
    have h2 : P β * s = P β := by
      rw [← he'']
      exact hle _ _ (sLe_single e'' k)
    have h3 : σ (P β) * p = σ (P β) := by
      have := congrArg σ h2
      rwa [map_mul, hsp] at this
    have h4 : σ (P β) = 0 := by
      rw [← h3, mul_comm, h1]
    have h5 : P β = 0 := by
      rw [← hσ (P β), h4, map_zero]
    have h6 : β = 0 := hinj (by rw [h5, hP0])
    have h7 := congrFun h6 k
    simp only [hβ, Pi.single_eq_same, Pi.zero_apply] at h7
    exact hne h7
  have hform : e'' = Pi.single j (e'' j) := by
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Pi.single_eq_of_ne hij, hsupp i hij]
  have hne0 : e'' j ≠ 0 := by
    intro h0
    have h1 : e'' = 0 := by
      rw [hform, h0]
      simp
    have h2 : s = 0 := by rw [← he'', h1, hP0]
    have h3 : p = 0 := by rw [← hsp, h2, map_zero]
    exact hδ0 (hinj (by rw [hP0, ← hp, h3]))
  have hne1 : e'' j ≠ 1 := by
    intro h1
    have h2 : e'' = δ := by rw [hform, h1]
    have h3 : s = p := by rw [← he'', h2]
    have h4 : p = 0 := by
      have h5 := hps
      rwa [h3, hpp] at h5
    exact hδ0 (hinj (by rw [hP0, ← hp, h4]))
  have hm1 := eq_neg_one_of hne0 hne1
  rw [← hm1, ← hform, he'']

end GlobalTheory.CompanionTheory.TorusCh.Signs

namespace GlobalTheory.CompanionTheory.TorusCh

theorem isotropicIdempotent_signs : ∀ (R : Type) [Ring R], (∀ x y : R, x * y = y * x) → ∀ (σ : R →+* R), (∀ x, σ (σ x) = x) →
    ∀ (m : ℕ) (P : (Fin m → SignType) → R), (∀ e, P e * P e = P e) → (∀ e, P e * σ (P e) = 0) →
    (∀ p, p * p = p → p * σ p = 0 → ∃ e, P e = p) → Function.Injective P → P 0 = 0 →
    (∀ e e', P (sMeet e e') = P e * P e') → (∀ e e', SLe e e' → P e * P e' = P e) →
    (∀ e, P e = ∑ j, P (Pi.single j (e j))) ∧ ∀ j, P (Pi.single j (-1)) = σ (P (Pi.single j 1)) := by
  intro R _ hc σ hσ m P hP2 hiso hsurj hinj hP0 hmeet hle
  letI : CommRing R := { (inferInstance : Ring R) with mul_comm := hc }
  exact ⟨fun e => Signs.additive σ P hP2 hiso hsurj hinj hP0 hmeet hle e,
    fun j => Signs.conj_single σ P hσ hP2 hiso hsurj hinj hP0 hle j⟩

end GlobalTheory.CompanionTheory.TorusCh
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem logAbs_eq_log_ideleModule (E : Type) [Field E] [NumberField E] [IsCMField E] (s : (Ad E)ˣ) :
    logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) := by
  have hm : ∀ v : InfinitePlace E, v.mult = 2 := fun v =>
    InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
  have hinf : ∀ w : InfinitePlace E, ‖(s : Ad E).1 w‖ ≠ 0 := fun w =>
    norm_ne_zero_iff.2 (GroundTheory.Global.IdeleGroup.infinite_ne_zero s w)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 E), 0 < ‖(s : Ad E).2 v‖ := fun v =>
    norm_pos_iff.2 (GroundTheory.Global.IdeleGroup.finite_ne_zero s v)
  have hA : (∏ w : InfinitePlace E, ‖(s : Ad E).1 w‖ ^ w.mult) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hinf w)
  have hB : (∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(s : Ad E).2 v‖) ≠ 0 :=
    (GroundTheory.Global.IdeleGroup.finiteModule_pos s).ne'
  have e : (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) =
      (∏ w : InfinitePlace E, ‖(s : Ad E).1 w‖ ^ w.mult) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(s : Ad E).2 v‖ :=
    GroundTheory.Global.IdeleGroup.ideleModule_eq s
  rw [e, Real.log_mul hA hB, Real.log_prod (fun w _ => pow_ne_zero _ (hinf w)), Real.log_finprod hfin]
  unfold logAbs
  simp only [GlobalTheory.CompanionTheory.TorNorm.norm_cV, hm]
  rfl

end GlobalTheory.CompanionTheory.TorusCh

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem double_coset_eq_iff {G : Type*} [Group G] (D g g' a a' : G) :
    g * D * a⁻¹ = g' * D * a'⁻¹ ↔ (g⁻¹ * g')⁻¹ * D * (a⁻¹ * a') = D := by
  constructor
  · intro h
    calc (g⁻¹ * g')⁻¹ * D * (a⁻¹ * a') = g'⁻¹ * (g * D * a⁻¹) * a' := by group
      _ = g'⁻¹ * (g' * D * a'⁻¹) * a' := by rw [h]
      _ = D := by group
  · intro h
    calc g * D * a⁻¹ = g' * ((g⁻¹ * g')⁻¹ * D * (a⁻¹ * a')) * a'⁻¹ := by group
      _ = g' * D * a'⁻¹ := by rw [h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def orbMap (d : GL (Fin n) E) (g : GA E n) : GA E n := g * ratGL E n d * (thetaA E n g)⁻¹

theorem orbMap_eq_iff (d : GL (Fin n) E) (g g' : GA E n) :
    orbMap d g = orbMap d g' ↔ g⁻¹ * g' ∈ adCent d := by
  have hm : g⁻¹ * g' ∈ adCent d ↔
      (g⁻¹ * g')⁻¹ * ratGL E n d * thetaA E n (g⁻¹ * g') = ratGL E n d := Iff.rfl
  rw [hm, map_mul, map_inv]
  exact double_coset_eq_iff _ _ _ _ _

theorem continuous_orbMap (d : GL (Fin n) E) : Continuous (orbMap (E := E) (n := n) d) := by
  unfold orbMap
  exact (continuous_id.mul continuous_const).mul GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA.inv

theorem orbMap_ratGL (d r : GL (Fin n) E) :
    orbMap d (ratGL E n r) = ratGL E n (r * d * (thetaE E n r)⁻¹) := by
  unfold orbMap
  rw [GlobalTheory.CompanionTheory.RatDisc.thetaA_ratGL, map_mul, map_mul, map_inv]

theorem finite_orbMap_inter (d : GL (Fin n) E) {C : Set (GA E n)} (hC : IsCompact C) :
    (orbMap d '' C ∩ orbMap d '' ((ratGL E n).range : Set (GA E n))).Finite := by
  refine ((GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem (hC.image (continuous_orbMap d))).image (ratGL E n)).subset ?_
  rintro _ ⟨h1, _, ⟨r, rfl⟩, rfl⟩
  rw [orbMap_ratGL] at h1 ⊢
  exact ⟨_, h1, rfl⟩

theorem ratGL_mem_ratCent (d r : GL (Fin n) E) (h : ratGL E n r ∈ adCent d) :
    ratGL E n r ∈ ratCent d := by
  refine ⟨r, ?_, rfl⟩
  have h' : twConj (thetaA E n) (ratGL E n r) (ratGL E n d) = ratGL E n d := h
  rw [twConj, GlobalTheory.CompanionTheory.RatDisc.thetaA_ratGL, ← map_inv, ← map_mul, ← map_mul] at h'
  exact GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL h'

theorem exists_isCompact_ratCent_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (C : Set (GA E n)), IsCompact C →
      ∃ C' : Set (GA E n), IsCompact C' ∧ ∀ t ∈ adCent d, t ∈ ((ratGL E n).range : Set (GA E n)) * C →
        t ∈ (ratCent d : Set (GA E n)) * C' := by
  intro E _ _ _ n d C hC
  obtain ⟨T, hTΓ, hT⟩ := GroundTheory.Automorphic.Anisotropic.exists_finset_of_orbit (orbMap d) (adCent d) (ratGL E n).range
    (orbMap_eq_iff d) C (finite_orbMap_inter d hC)
  refine ⟨⋃ δ ∈ T, (fun c => δ⁻¹ * c) '' C,
    T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id), ?_⟩
  rintro t ht ⟨γ, hγ, c, hc, rfl⟩
  obtain ⟨δ, hδT, hγδ, -⟩ := hT _ ht γ hγ c hc rfl
  obtain ⟨r, rfl⟩ := hγ
  obtain ⟨s, rfl⟩ := hTΓ δ hδT
  rw [← map_mul] at hγδ
  refine Set.mem_mul.2 ⟨ratGL E n (r * s), ratGL_mem_ratCent d _ hγδ,
    (ratGL E n s)⁻¹ * c, Set.mem_biUnion hδT ⟨c, hc, rfl⟩, ?_⟩
  rw [map_mul, mul_assoc, mul_inv_cancel_left]

end GlobalTheory.CompanionTheory.TorusCh

end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount.KHw

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)

variable {n : ℕ}

section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {Kf : Fin n → Fin n → Module.End ℂ V}

theorem glRel_kF {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPair E1 E2) : Formalism.REAL.GlRel (kF E1 E2) := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have c1 := h.comm a b c d
  have c2 := h.comm c d a b
  have key : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add, c1, ← c2]
    abel
  rw [key, h1, h2]
  simp only [kF]
  split_ifs <;> abel

end

end GlobalTheory.CompanionTheory.RealCount.KHw
end
end

section

open PositivityTheory.RgBcC.RealD (kF)

namespace GlobalTheory.CompanionTheory.ModelS

theorem eq_smul_of_commute_of_ev : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → ∀ (z : Module.End ℂ V), (∀ a b, z * F1 a b = F1 a b * z ∧ z * F2 a b = F2 a b * z) → ∀ (ev : V →ₗ[ℂ] ℂ) (c : ℂ), (∀ v, ev (z v) = c * ev v) → (∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) → ∀ w ∈ S, w = 0) → ∀ x : V, z x = c • x := by
  intro n V _ _ F1 F2 hfin z hz ev c hev hS x
  set A := Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = kF F1 F2 a b} with hA
  set y : V := z x - c • x with hy
  obtain ⟨S₁, hfd, hyS₁, hst⟩ := hfin y
  have hpres : ∀ T ∈ A, ∀ w ∈ S₁, T w ∈ S₁ := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl⟩ := hT
      exact hst a b
    | algebraMap r =>
      intro w hw
      simpa [Module.algebraMap_end_apply] using S₁.smul_mem r hw
    | add S T _ _ hS' hT' =>
      intro w hw
      exact S₁.add_mem (hS' w hw) (hT' w hw)
    | mul S T _ _ hS' hT' =>
      intro w hw
      exact hS' _ (hT' w hw)
  have hcomm : ∀ T ∈ A, z * T = T * z := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl⟩ := hT
      have h1 := (hz a b).1
      have h2 := (hz a b).2
      show z * (F1 a b + F2 a b) = (F1 a b + F2 a b) * z
      rw [mul_add, add_mul, h1, h2]
    | algebraMap r => exact (Algebra.commutes r z).symm
    | add S T _ _ hS' hT' => rw [mul_add, add_mul, hS', hT']
    | mul S T _ _ hS' hT' => rw [← mul_assoc, hS', mul_assoc, hT', mul_assoc]
  let S : Submodule ℂ V := (Subalgebra.toSubmodule A).map (LinearMap.applyₗ y)
  have hmem : ∀ w, w ∈ S ↔ ∃ T ∈ A, T y = w := by
    intro w
    simp [S, Submodule.mem_map]
  have hle : S ≤ S₁ := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    exact hpres T hT y hyS₁
  have hSfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hle
  have hSst : ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
    intro a b w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    refine (hmem _).2 ⟨kF F1 F2 a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, rfl⟩) hT, rfl⟩
  have hSev : ∀ w ∈ S, ev w = 0 := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    have hzT : T (z x) = z (T x) := (LinearMap.congr_fun (hcomm T hT) x).symm
    rw [hy, map_sub, map_smul, hzT, map_sub, map_smul, hev, smul_eq_mul, sub_self]
  have hyS : y ∈ S := (hmem y).2 ⟨1, A.one_mem, rfl⟩
  exact sub_eq_zero.1 (hS S hSfd hSst hSev y hyS)

end GlobalTheory.CompanionTheory.ModelS
end
