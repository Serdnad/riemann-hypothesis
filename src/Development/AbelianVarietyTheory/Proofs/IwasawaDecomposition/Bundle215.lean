module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOne
public import Formalism.LocalToGlobal.HermitianForms.Bundle009
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

section Generic

variable {Ω : Type} [Field Ω] {J : Type} [Fintype J] [DecidableEq J]

def genPoly (Ω : Type) [Field Ω] (j₀ j : J) : MvPolynomial {j // j ≠ j₀} Ω :=
  if h : j = j₀ then 1 else MvPolynomial.X ⟨j, h⟩

def genPt (Ω : Type) [Field Ω] (j₀ j : J) : FractionRing (MvPolynomial {j // j ≠ j₀} Ω) :=
  algebraMap _ _ (genPoly Ω j₀ j)

omit [Fintype J] in
theorem genPt_self (j₀ : J) : genPt Ω j₀ j₀ = 1 := by simp [genPt, genPoly]


omit [Fintype J] in
theorem eq_top_of_genPt_mem (j₀ : J) (K : Subfield (FractionRing (MvPolynomial {j // j ≠ j₀} Ω)))
    (h1 : ∀ a : Ω, algebraMap Ω _ a ∈ K) (h2 : ∀ j, genPt Ω j₀ j ∈ K) : K = ⊤ := by
  have h : ∀ p : MvPolynomial {j // j ≠ j₀} Ω, algebraMap _ _ p ∈ K := fun p => by
    induction p using MvPolynomial.induction_on with
    | C a => exact h1 a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      simpa [genPt, genPoly, j.2] using h2 j.1
  refine top_unique fun x _ => ?_
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial {j // j ≠ j₀} Ω) x
  exact div_mem (h p) (h q)

theorem eq_zero_of_sum_genPt (j₀ : J) (b : J → Ω) (h : ∑ j, algebraMap Ω _ (b j) * genPt Ω j₀ j = 0) : b = 0 := by
  have h' : ∑ j, MvPolynomial.C (b j) * genPoly Ω j₀ j = 0 := by
    apply IsFractionRing.injective _ (FractionRing (MvPolynomial {j // j ≠ j₀} Ω))

    rw [map_zero, map_sum, ← h]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; rfl
  have e : ∀ x : J → Ω, x j₀ = 1 → ∑ j, b j * x j = 0 := fun x hx => by
    have := congrArg (MvPolynomial.eval fun j : {j // j ≠ j₀} => x j.1) h'

    rw [map_zero, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = j₀
    · subst hj; simp [genPoly, hx]
    · simp [genPoly, hj]
  have h0 : b j₀ = 0 := by simpa [Pi.single_apply] using e (Pi.single j₀ 1) (by simp)
  funext j
  by_cases hj : j = j₀
  · exact hj ▸ h0
  · have := e (fun l => Pi.single (M := fun _ => Ω) j₀ 1 l + Pi.single (M := fun _ => Ω) j 1 l) (by simp [Ne.symm hj])
    simpa [Pi.single_apply, mul_add, Finset.sum_add_distrib, h0] using this

theorem genPt_ratio (j₀ : J) (B : Matrix J J Ω) (hB : B.det ≠ 0) (i : J) :
    (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) i ≠ 0 ∧ AlgebraicIndependent Ω fun j : {j // j ≠ i} =>
      (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) j.1 / (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) i := by
  set u := (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) with hu
  have hi : u i ≠ 0 := fun h => hB (Matrix.det_eq_zero_of_row_eq_zero i
    (congrFun (eq_zero_of_sum_genPt j₀ (B i) h)))
  refine ⟨hi, ?_⟩
  set r : {j // j ≠ i} → _ := fun j => u j.1 / u i
  have hs : (B⁻¹.map (algebraMap Ω _)).mulVec u = genPt Ω j₀ := by
    rw [hu, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  set K := IntermediateField.adjoin Ω (Set.range r)
  have h1 : ∀ j, u j / u i ∈ K := fun j => by
    by_cases hj : j = i
    · rw [hj, div_self hi]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨j, hj⟩, rfl⟩
  have h2 : ∀ j, genPt Ω j₀ j / u i ∈ K := fun j => by
    rw [← hs, Matrix.mulVec, dotProduct, Finset.sum_div]
    refine sum_mem fun l _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (K.algebraMap_mem _) (h1 l)
  have h3 : K.toSubfield = ⊤ := eq_top_of_genPt_mem j₀ _ K.algebraMap_mem fun j => by
    have := div_mem (h2 j) (h2 j₀)
    rwa [div_div_div_cancel_right₀ hi, genPt_self, div_one] at this
  have h4 : Algebra.IsAlgebraic K (FractionRing (MvPolynomial {j // j ≠ j₀} Ω)) := ⟨fun x =>
    isAlgebraic_algebraMap (⟨x, (h3 ▸ Subfield.mem_top x : x ∈ K.toSubfield)⟩ : K)⟩
  have h5 := IntermediateField.isAlgebraic_adjoin_iff_top.1 h4
  refine (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω r ?_).1
  have h6 := trdeg_add_eq Ω (MvPolynomial {j // j ≠ j₀} Ω) (A := FractionRing (MvPolynomial {j // j ≠ j₀} Ω))
  rw [← h6, MvPolynomial.trdeg_of_isDomain]
  refine le_trans (le_of_eq ?_) le_self_add
  simp [Cardinal.mk_fintype]

end Generic

theorem exists_projBundle : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] (EE : M.Lat J), IsProjOver M.s → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (s : J → Ω'), ProjBundle M EE M' φ f s ∧ IsProjOver M'.s := by
  intro F Ω _ _ _ M J _ inst ⟨j₀⟩ EE hM
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  let : DecidableEq J := fun a b => Classical.propDecidable (a = b)
  let Ω' := FractionRing (MvPolynomial {j // j ≠ j₀} Ω)
  let φ : Ω →ₐ[F] Ω' := IsScalarTower.toAlgHom F Ω Ω'
  obtain ⟨M', f, hf, hp, hc⟩ := RatModel.exists_projBundle_closure F Ω M Ω' φ J EE (genPt Ω j₀) hM
    ⟨j₀, by rw [genPt_self]; exact one_ne_zero⟩
    (eq_top_of_genPt_mem j₀ _ (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      fun j => Subfield.subset_closure (Or.inr ⟨j₀, j, by rw [genPt_self, div_one]⟩))
  refine ⟨Ω', inferInstance, inferInstance, M', φ, f, genPt Ω j₀, ⟨hf, fun B hB i => ?_, hc⟩, hp⟩
  obtain ⟨h1, h2⟩ := genPt_ratio j₀ B hB i
  exact ⟨h1, fun P hP => algebraicIndependent_iff.1 h2 P hP⟩

end GlobalTheory.FlagBundle
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.LastGrp

open GlobalTheory.SymLevelInv LocE Loc

theorem posSym_eq_symIdx (k rS x : ℕ) : posSym k rS x = symIdx k rS x := by
  unfold posSym symIdx
  split_ifs <;> omega

theorem symmetric_level_bound_le (k rS s : ℕ) : bd5 k rS s ≤ s := by
  unfold bd5
  split_ifs <;> omega

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem inJSym_of_mat (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k rS r t n : ℕ} (hr : r = rSym k rS) (ht : 0 < t) (hn : r ≤ n)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k rS r t n 0) {κ : Type} [Field κ]
    (e : (𝓞 E ⧸ P.asIdeal) →+* κ) (M : Matrix (Fin n) (Fin n) κ) (hM : ∀ i j : Fin n, M i j = e (redP P (mat g i j))) :
    InJSym k rS t false M := by
  subst hr
  have hr' : k + rS < rSym k rS := by
    unfold rSym
    omega
  refine ⟨fun x y h => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun h => by simp at h⟩
  · have hxy : x.1 ≠ y.1 := fun h' => by rw [h'] at h; omega
    by_cases hy : y.1 < rSym k rS
    · have key : bd5 k rS (symIdx k rS y.1) ≤ symIdx k rS x.1 := by
        refine (symmetric_level_bound_le _ _ _).trans ?_
        rw [lvSym_of_lt hy, posSym_eq_symIdx] at h
        by_cases hx : x.1 < rSym k rS
        · rw [lvSym_of_lt hx, posSym_eq_symIdx] at h
          exact h.le
        · have h1 := symIdx_lt hr'.le hy
          have h2 := symIdx_cases k rS x.1
          omega
      rw [hM, mat_col hq hP hr' hn hg x.1 y.1 x.2 hy key, if_neg hxy, map_zero]
    · have hx : ¬ x.1 < rSym k rS := by
        intro hx
        have h1 := lvSym_of_ge (t := t) hy
        rw [lvSym_of_lt hx] at h
        have h2 := posSym_lt hx
        omega
      unfold lvSym at h
      rw [if_neg hy, if_neg hx] at h
      have h1 : (y.1 - rSym k rS) / t + 1 ≤ (x.1 - rSym k rS) / t := by omega
      have h2 := Nat.lt_mul_div_succ (y.1 - rSym k rS) ht
      have h3 := Nat.div_mul_le_self (x.1 - rSym k rS) t
      have h4 := Nat.mul_le_mul_right t h1
      rw [mul_comm] at h2
      rw [hM, mat_blk hq hP hr' hg ((y.1 - rSym k rS) / t + 1) x.1 y.1 x.2 (by omega) (by omega), map_zero]
  · rw [hM, mat_col hq hP hr' hn hg x.1 x.1 x.2 hx (symmetric_level_bound_le _ _ _), if_pos rfl, map_one]
  · have hyr : y.1 < rSym k rS := by omega
    have key : bd5 k rS (symIdx k rS y.1) ≤ symIdx k rS x.1 := by
      rw [hy]
      unfold bd5 symIdx
      split_ifs <;> omega
    rw [hM, mat_col hq hP hr' hn hg x.1 y.1 x.2 hyr key, if_neg (by omega), map_zero]

theorem inJSym_of_prX (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k rS r t n c : ℕ} (hc : c = 0) (hr : r = rSym k rS) (ht : 0 < t)
    (hn : r ≤ n) {ρ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hρ : ρ ∈ JGsym P q k rS r t n c) {g : Sp E n ≃ₗ[E] Sp E n}
    (hx : ∀ x, ρ (Loc.inX E n c x) = Loc.inX E n c (g x)) {κ : Type} [Field κ] (e : (𝓞 E ⧸ P.asIdeal) →+* κ)
    (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) (hM : ∀ x ∈ stdAt E n P, redV P (g x) = M.mulVec (redV P x)) :
    InJSym k rS t false (M.map e) := by
  subst hc
  refine inJSym_of_mat hq hP hr ht hn hρ e _ fun i j => ?_
  have h6 := congrFun (hM _ (TopStep.single_mem_stdAt j)) i
  rw [TopStep.redV_single, Matrix.mulVec_single_one] at h6
  have h7 : mat ρ i.1 j.1 = g (Pi.single j 1) i := by
    have h8 : eN E (n + 0) j.1 = Loc.inX E n 0 (Pi.single j 1) := by
      funext l
      rw [CongLevel.inX_apply, dite_eq_left (show l.1 < n from l.2)]
      unfold Loc.eN
      simp [Pi.single_apply, Fin.ext_iff]
    unfold mat atN
    rw [dite_eq_left (show i.1 < n + 0 from i.2), h8, hx, CongLevel.inX_apply, dite_eq_left i.2]
  rw [Matrix.map_apply, h7]
  exact congrArg e h6.symm

end GlobalTheory.Mem.LastGrp

theorem GlobalTheory.Mem.LastGrp.levG_le_JSymG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ∀ (j : ℕ), j + 1 = R.m → ∀ (b : L.β j) (w : {w // w ∈ Pr.vGs}) (κ : Type) [Field κ] (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* κ) (M : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)), M ∈ (L.levG j b w).H → Matrix.GeneralLinearGroup.map e.toRingHom M ∈ JSymG κ (R.N j) R.k (rSD R) R.t false := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hSel hL hs j hj b w κ _ e M hM
  letI : StarRing X.E := X.starE
  have hm := hL.hm
  obtain rfl : j = m2 + 1 := by omega
  have hc : cOf R (m2 + 1) = 0 := by
    unfold cOf
    omega
  have hq : qOf w.1 ≠ 0 := fun h => TopStep.qOf_ne_zero (P := w.1) (by rw [h]; simp)
  have hP : ((qOf w.1 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := Ideal.absNorm_mem _
  have hr : R.r = rSym R.k (rSD R) := by
    obtain ⟨a, ha⟩ := R.m_even
    unfold Ranks.r rSym rSD
    omega
  have ht : 0 < R.t := by
    have := R.three_m_lt_t
    omega
  have hn : R.r ≤ R.N (m2 + 1) := by
    unfold Ranks.r Ranks.N
    rw [mul_add, mul_one]
    omega
  have key : ∀ A : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal), A ∈ (L.levG (m2 + 1) b w).H →
      InJSym R.k (rSD R) R.t false ((A.1).map e.toRingHom) := by
    intro A hA
    obtain ⟨g, hg, hred⟩ := (hL.grpG _ b w A).1 hA
    unfold prCat at hg
    rw [hL.last_h] at hg
    obtain ⟨ρ, hρ, hx⟩ := hg
    have hJ : ρ ∈ Jat (Pr := Pr) cst.sharp (m2 + 1) w.1 := by simpa [Loc.Cbe] using hρ.2
    unfold Jat at hJ
    rw [if_pos w.2, if_pos hs] at hJ
    exact inJSym_of_prX hq hP hc hr ht hn hJ hx e.toRingHom A.1 hred
  refine ⟨key M hM, ?_⟩
  rw [← map_inv]
  exact key _ (inv_mem hM)
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Proof.LastStepChar

open Loc LocE GlobalTheory.SymLevelInv

theorem sum_sd {κ : Type} [AddCommMonoid κ] {n a k : ℕ} (hk : 1 ≤ k) (hka : k < a) (ha : a ≤ n)
    (N : Matrix (Fin n) (Fin n) κ) (f : ℕ → ℕ → κ) (hf : ∀ x y (hx : x < n) (hy : y < n), N ⟨x, hx⟩ ⟨y, hy⟩ = f x y) :
    (∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ k then N x y else 0) =
      ∑ i ∈ Finset.range (k - 1), f i (i + 1) + ∑ i ∈ Finset.range (a - k - 1), f (k + i) (k + i + 1) := by
  have h1 : ∀ x : Fin n, (∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ k then N x y else 0) =
      if (x : ℕ) + 1 < a ∧ (x : ℕ) + 1 ≠ k then f x (x + 1) else 0 := by
    intro x
    by_cases hx : (x : ℕ) + 1 < a ∧ (x : ℕ) + 1 ≠ k
    · rw [if_pos hx, Finset.sum_eq_single (⟨x.1 + 1, by omega⟩ : Fin n), if_pos ⟨rfl, hx.1, hx.2⟩, hf]
      · intro y _ hy
        exact if_neg fun h => hy (Fin.ext h.1.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg hx]
      refine Finset.sum_eq_zero fun y _ => if_neg fun h => hx ?_
      obtain ⟨h1, h2, h3⟩ := h
      omega
  rw [Finset.sum_congr rfl fun x _ => h1 x,
    Fin.sum_univ_eq_sum_range (fun x => if x + 1 < a ∧ x + 1 ≠ k then f x (x + 1) else 0) n]
  have e : n = (k - 1) + (1 + ((a - k - 1) + (n - (a - 1)))) := by omega
  rw [e, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_one]
  rw [if_neg (by omega), zero_add, Finset.sum_eq_zero (s := Finset.range (n - (a - 1))), add_zero]
  · congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [if_pos (by omega)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [if_pos (by omega), show k - 1 + (1 + i) = k + i by omega]
  · intro i hi
    rw [if_neg (by omega)]

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem red_mat {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n) (r : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0))
    (hrg : ∀ x, r (Loc.inX E n 0 x) = Loc.inX E n 0 (g x)) (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal))
    (hred : ∀ x ∈ stdAt E n P, redV P (g x) = M.mulVec (redV P x)) (p p' : ℕ) (hp : p < n) (hp' : p' < n) :
    redP P (mat r p p') = M ⟨p, hp⟩ ⟨p', hp'⟩ := by
  have he : Loc.eN E (n + 0) p' = Loc.inX E n 0 (Loc.eN E n p') := by
    funext l
    rw [GlobalTheory.QNormal.inX_apply, dif_pos (show (l : ℕ) < n from l.2)]
    rfl
  have hv : redV P (Loc.eN E n p') = Pi.single ⟨p', hp'⟩ 1 := by
    funext l
    simp only [redV, Loc.eN, Pi.single_apply, Fin.ext_iff]
    split_ifs
    · exact reduction_one' P
    · exact redP_zero' P
  have h5 := congrFun (hred _ (GlobalTheory.GO.ChRoot.eN_mem (i := p'))) ⟨p, hp⟩
  rw [hv, Matrix.mulVec_single_one] at h5
  unfold mat
  rw [he, hrg, Loc.atN, dif_pos (show p < n + 0 from hp), GlobalTheory.QNormal.inX_apply, dif_pos hp]
  exact h5

theorem lam_loc {K : Type} [Field K] (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ₀ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {κ : Type} [Field κ] (e : (𝓞 E ⧸ P.asIdeal) ≃+* κ) (σ : K →+* ℂ) (ψ : AddChar κ ℂ) (χ : ℕ → MulChar κ ℂ)
    {k rS r t nb n c : ℕ} (hc : c = 0) (hr : r = k + 2 * rS + 1) (hk : 1 ≤ k) (hn : r + nb * t ≤ n)
    (hψ : ∀ a, ψ (e a) = σ (ψ₀ a)) (hχ : ∀ i, i < nb → ∀ a : (𝓞 E ⧸ P.asIdeal)ˣ, χ i (e a) = σ ((χ₀ i a : Kˣ) : K))
    (g : Sp E n ≃ₗ[E] Sp E n) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (hh : h ∈ JGsym P (qOf P) k rS r t n c)
    (hhg : ∀ x, h (Loc.inX E n c x) = Loc.inX E n c (g x)) (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal))
    (hred : ∀ x ∈ stdAt E n P, redV P (g x) = M.mulVec (redV P x)) :
    σ (lamGBS (qOf P) ψ₀ χ₀ k r t nb n c h.toLinearMap) = Formalism.L2.Forms.lamSym ψ χ k rS t nb (M.map e) := by
  subst hc hr
  have hM := red_mat g h hhg M hred
  have hrn : k + 2 * rS + 1 ≤ n := le_trans (Nat.le_add_right _ _) hn
  unfold lamGBS lamGvS Formalism.L2.Forms.lamSym Formalism.L2.Forms.lamJ Formalism.L2.Forms.rSym
  rw [map_mul]
  congr 1

  · rw [redP_superdiag (by omega) hrn hh, ← hψ, map_add (f := _), map_sum, map_sum]
    congr 1
    refine (sum_sd hk (by omega) hrn _ (fun x y => e (redP P (mat h x y))) fun x y hx hy => ?_).symm
    rw [Matrix.map_apply, hM x y hx hy]
  · rw [map_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hi' : k + 2 * rS + 1 + i * t + t ≤ n := by
      have : (i + 1) * t ≤ nb * t := Nat.mul_le_mul_right t hi
      rw [add_mul, one_mul] at this
      omega
    have hb : Formalism.L2.Forms.blkMat (k + 2 * rS + 1) t i (M.map e) =
        e.toRingHom.mapMatrix (Matrix.of fun s s' : Fin t => redP P (mat h (k + 2 * rS + 1 + i * t + s.1) (k + 2 * rS + 1 + i * t + s'.1))) := by
      ext s s'
      have := s.2
      have := s'.2
      unfold Formalism.L2.Forms.blkMat Formalism.L2.Forms.entN
      rw [dif_pos ⟨by omega, by omega⟩, Matrix.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
        hM (k + 2 * rS + 1 + i * t + s.1) (k + 2 * rS + 1 + i * t + s'.1) (by omega) (by omega)]
      rfl
    rw [hb, ← RingHom.map_det]
    unfold unitV
    rw [redP_det_blk hi' hh]
    split_ifs with hu
    · rw [← hχ i hi, IsUnit.unit_spec]
      rfl
    · rw [map_zero, MulChar.map_nonunit]
      exact fun h' => hu ((isUnit_map_iff e _).1 h')

end Loc

end GlobalTheory.Proof.LastStepChar

theorem GlobalTheory.Proof.LastStepChar.chr_last : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ∀ (j : ℕ), j + 1 = R.m → ∀ (b : L.β j) (w : {w // w ∈ Pr.vGs}) (κ : Type) [Field κ] (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* κ) (σ : X.K →+* ℂ) (ψ : AddChar κ ℂ) (χ : ℕ → MulChar κ ℂ), (∀ c, ψ (e c) = σ (Ch.psi0 w c)) → (∀ (s : Fin R.m) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), χ s.1 (e c) = σ ((Ch.chi s w c : X.Kˣ) : X.K)) → ∀ M : (L.levG j b w).H, σ (((L.levG j b w).lam M : X.Kˣ) : X.K) = lamSym ψ χ R.k (rSD R) R.t j (M.1.1.map e) := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hL hsh j hj b w κ _ e σ ψ χ hψ hχ M
  have hm := hL.hm
  obtain rfl : j = m2 + 1 := by omega
  obtain ⟨g, hg, hred⟩ := (hL.grpG (m2 + 1) b w M.1).1 M.2
  obtain ⟨r, hrC, hrg⟩ := hg
  have hlam := hL.chrG (m2 + 1) b w M g r hrC hrg hred
  rw [hlam]
  rw [hL.last_h] at hrC ⊢
  have hc : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  have hJ0 : r ∈ Jat (Pr := Pr) (R := R) cst.sharp (m2 + 1) w.1 := by
    unfold Loc.Cbe at hrC
    rw [Subgroup.mem_inf, Subgroup.mem_comap] at hrC
    simpa using hrC.2
  unfold Jat at hJ0
  rw [if_pos w.2, hsh, if_pos rfl] at hJ0
  have hn1 : Loc.n1Arg r = 0 := by
    unfold Loc.n1Arg
    rw [show cOf R (m2 + 1) - 1 = 0 by omega, Finset.sum_range_zero]
  unfold chiInv
  rw [hn1, hL.cst_ok.psi_int _ _ (GlobalTheory.SymLevelInv.intAt_zero _), inv_one, one_mul]
  unfold lamRow
  simp only [if_pos w.2, hsh, if_true]
  rw [inv_one, one_mul, mul_one]
  have hk := R.m_add_three_le_k
  have hr : R.r = R.k + 2 * R.rS + 1 := by
    obtain ⟨a, ha⟩ := R.m_even
    unfold Ranks.r Ranks.rS
    omega
  have hn : R.r + (m2 + 1) * R.t ≤ R.N (m2 + 1) := by
    unfold Ranks.r Ranks.N
    rw [mul_add, mul_one]
    omega
  refine lam_loc (psi0P Ch w.1) (chiP Ch w.1) e σ ψ χ hc hr (by omega) hn (fun a => ?_) (fun i hi a => ?_) g r hJ0 hrg M.1.1 hred
  · rw [hψ]
    unfold psi0P
    rw [dif_pos w.2]
  · rw [hχ ⟨i, by omega⟩ a]
    unfold chiP chiAt extChi
    rw [dif_pos w.2]
    simp only [dif_pos (show i < R.m by omega)]

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultAction

theorem actRep : ∀ D : D7, ActRep D := by
  intro D V β L S θ M hl hP
  have e : Formalism.IndefR.Lev.flag1L L = L := by
    rw [flag1L, withP, ← hP]
  have hM : Mult θ M (levS V β L) (levChi V β L) = MultP θ M β L := by
    rw [MultP, e]
  rw [hM]
  refine ⟨fun g T hT => act_mem g hT, fun T hT => act_one hT, fun g h T hT => act_mul hl g h hT, ?_⟩
  intro G _ _ eG c hc g T hT
  have h := gaL_act eG hl (c := c) (fun a b => hc a b) (eG.symm g) hT
  rwa [MulEquiv.apply_symm_apply] at h

end GlobalTheory.MultAction

end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ ψ' : AddChar (AF F) ℂ), IsCharAF F ψ → IsCharAF F ψ' → ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) := by
  first | exact @GlobalTheory.AdeleCharTwist.exists_mul_eq | exact GlobalTheory.AdeleCharTwist.exists_mul_eq | (intros; apply GlobalTheory.AdeleCharTwist.exists_mul_eq <;> assumption)
end
