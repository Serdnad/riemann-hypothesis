module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle152
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle484
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle522
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle516
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSNonvan

theorem norm_prod_sat_eq_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ : CG E a)
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), σ.IsUnitary → σ.HasSat w B → ‖((B.prod : ℂˣ) : ℂ)‖ = 1 := by
  intro E _ _ _ a σ w B hu hB
  obtain ⟨ω, hωu, hω⟩ := hu
  induction σ using Quotient.inductionOn with | _ π => ?_
  change GlobalTheory.LFun.HasSatGL w (π.locRep w) B at hB
  change π.HasCentChar ω at hω
  obtain ⟨x, hx⟩ := hB.exists_vec
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  let u : (w.adicCompletion E)ˣ := Units.mk0 ϖ hϖ0
  let S : GL (Fin a) (w.adicCompletion E) := Matrix.GeneralLinearGroup.scalar (Fin a) u
  let K := GlobalTheory.LFun.KGL w (n := a)
  have hS : ((S : GL (Fin a) (w.adicCompletion E)) : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = diagJ a ϖ a := by
    ext i j
    simp [S, u, diagJ, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]
  have hT : Tj ℂ a (Ov E w) ϖ a = dosetInd ℂ K S := by
    unfold Tj dosetInd
    congr 1
    ext g
    simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    refine exists_congr fun y => and_congr_right fun _ => exists_congr fun z => and_congr_right fun _ => ?_
    rw [Units.ext_iff, Units.val_mul, Units.val_mul, hS]
  have hc : ∀ g ∈ DoubleCoset.doubleCoset S (K : Set _) K, ∃! γ, γ ∈ ({S} : Finset _) ∧ γ⁻¹ * g ∈ K := by
    intro g hg
    obtain ⟨y, hy, z, hz, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    refine ⟨S, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    have e : S⁻¹ * (y * S * z) = y * z := by
      rw [show y * S = S * y from (scalar_comm u y).symm]; group
    rw [e]
    exact K.mul_mem hy hz
  have hR : ∀ γ ∈ ({S} : Finset _), γ ∈ DoubleCoset.doubleCoset S (K : Set _) K := by
    intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, 1, K.one_mem, by group⟩
  have h1 := hx.2.2.2 ϖ hϖ a le_rfl
  rw [hT, GlobalTheory.LFun.heckeVec_dosetInd hx.2.1 hR hc, Finset.sum_singleton] at h1
  have h2 : π.locRep w S x = ((ω.1 (finId E (Units.map (corner (sLoc E w)) u)) : ℂˣ) : ℂ) • x := by
    have e : locGL E a w S = Matrix.GeneralLinearGroup.scalar (Fin a) (Units.map (corner (sLoc E w)) u) :=
      cornerGL_scalar (sLoc E w) u
    change π.finPart (locGL E a w S) x = _
    rw [e]
    exact hω _ x
  rw [h2] at h1
  have h3 := smul_left_injective ℂ hx.1 h1
  have hcard : (B.map fun b : ℂˣ => (b : ℂ)).card = a := by rw [Multiset.card_map]; exact hx.2.2.1
  have h4 : GlobalTheory.LFun.satEig (qV E w) a B a = ((B.prod : ℂˣ) : ℂ) := by
    rw [GlobalTheory.LFun.satEig, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul, Multiset.esymm, ← hcard,
      Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]
    exact (map_multiset_prod (Units.coeHom ℂ) B).symm
  rw [← h4, ← h3]
  exact hωu _

end GlobalTheory.RSNonvan
end
end

section

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

private theorem pow_pow_factorization_mul_inv_val_eq_self {K : Type} [Field K] {l : ℕ} [Fact l.Prime] [CharP K l] (y : K) (n : ℕ)
    (hy : y ^ n = 1) :
    y ^ (l ^ n.factorization l * (((l ^ n.factorization l : ℕ) : ZMod (n / l ^ n.factorization l))⁻¹).val) = y := by
  have hl : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [ZMod.val_one_eq_one_mod]
  set q := l ^ n.factorization l with hq_def
  set m := n / q with hm_def
  have hnqm : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n l
  have hm0 : m ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hnqm
    omega
  haveI : NeZero m := ⟨hm0⟩
  have hcop : Nat.Coprime q m := (Nat.coprime_ordCompl hl hpos.ne').pow_left _
  have hym : y ^ m = 1 := by
    have h1 : (y ^ m) ^ q = 1 := by rw [← pow_mul, mul_comm, hnqm, hy]
    have h2 : (y ^ m - 1) ^ q = 0 := by
      rw [hq_def, sub_pow_char_pow, ← hq_def, h1, one_pow, sub_self]
    have hq0 : q ≠ 0 := pow_ne_zero _ hl.ne_zero
    exact sub_eq_zero.1 ((pow_eq_zero_iff hq0).1 h2)
  have hmod : q * ((q : ZMod m)⁻¹).val ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one q hcop
  have hdvd : orderOf y ∣ m := orderOf_dvd_of_pow_eq_one hym
  have hmod' := hmod.of_dvd hdvd
  calc y ^ (q * ((q : ZMod m)⁻¹).val) = y ^ ((q * ((q : ZMod m)⁻¹).val) % orderOf y) := (pow_mod_orderOf _ _).symm
    _ = y ^ (1 % orderOf y) := by rw [hmod']
    _ = y := by rw [pow_mod_orderOf, pow_one]

theorem map_primeToPart_fbar {g l : ℕ} [Fact g.Prime] [Fact l.Prime] {K : Type} [Field K] [CharP K l]
    (ι : Formalism.CyclotomicNorms.Fbar g →* K) (x : Formalism.CyclotomicNorms.Fbar g) : ι (Formalism.CyclotomicNorms.primeToPart l x) = ι x := by
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [map_pow]
  exact pow_pow_factorization_mul_inv_val_eq_self _ _ (by rw [← map_pow, pow_orderOf_eq_one, map_one])

end GlobalTheory.TypeLeaf
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.EvalIdem

theorem ringHom_eq_of_unique {O A S : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing S]
    (Q : A → Prop)
    (h : ∀ (S : Type) [CommRing S] [Algebra O S] (f f' : A →ₐ[O] S), (∀ a, Q a → f a = f' a) → f = f')
    (F F' : A →+* S) (h0 : ∀ o, F (algebraMap O A o) = F' (algebraMap O A o))
    (h1 : ∀ a, Q a → F a = F' a) (a : A) : F a = F' a := by
  let _ : Algebra O S := (F.comp (algebraMap O A)).toAlgebra
  have := h S ⟨F, fun _ => rfl⟩ ⟨F', fun o => (h0 o).symm⟩ h1
  exact DFunLike.congr_fun this a

theorem io_const {O T : Type} [CommRing O] [CommRing T] [Algebra O T] {n : ℕ} (f : LetA O n →ₐ[O] T) (x : O) :
    f (fun j => PowerSeries.C (algebraMap O (ZMod n → O) x j)) = algebraMap O T x := f.commutes x

theorem const_eq {O T S : Type} [CommRing O] [CommRing T] [Algebra O T] [CommRing S] {n : ℕ}
    (Q : (ZMod n → O) → Prop)
    (h : ∀ (S : Type) [CommRing S] [Algebra O S] (f f' : (ZMod n → O) →ₐ[O] S),
      (∀ a, Q a → f a = f' a) → f = f')
    (f : LetA O n →ₐ[O] T) (G : T →+* S) (e : O →+* S) (i : ZMod n)
    (h0 : ∀ x, G (algebraMap O T x) = e x)
    (h1 : ∀ a, Q a → G (f (fun j => PowerSeries.C (a j))) = e (a i)) (a : ZMod n → O) :
    G (f (fun j => PowerSeries.C (a j))) = e (a i) :=
  ringHom_eq_of_unique Q h
    (G.comp (f.toRingHom.comp (RingHom.pi fun j =>
      (PowerSeries.C : O →+* PowerSeries O).comp (Pi.evalRingHom _ j))))
    (e.comp (Pi.evalRingHom _ i)) (fun x => (congrArg G (io_const f x)).trans (h0 x)) h1 a

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {LL : FinExt l}

theorem component_tmul {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (x : ↥(OL LL)) (w : Ainf l) :
    Algebra.TensorProduct.productMap ι P.ιB (β (x ⊗ₜ[ℤ_[l]] w)) = ι (x : ↥LL.1) * P.ιB (AI.ιA w) := by
  rw [hβ, Algebra.TensorProduct.productMap_apply_tmul]

theorem component_algebraMap {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (x : ↥(OL LL)) :
    Algebra.TensorProduct.productMap ι P.ιB (β (algebraMap ↥(OL LL) (RA LL) x)) = ι (x : ↥LL.1) := by
  have h1 : algebraMap ↥(OL LL) (RA LL) x = x ⊗ₜ[ℤ_[l]] (1 : Ainf l) := rfl
  rw [h1, component_tmul hβ, map_one, map_one, mul_one]

theorem component_teich {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) {K : FinExt l} (c : ↥(K0 K)) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m)
    (hc : (c : Om l) ^ m = 1) (xb : OCb l) (hxb : IsTiltOf (c : Om l) m xb) :
    Algebra.TensorProduct.productMap ι P.ιB
      (β ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb)) = algebraMap ↥(K0 K) P.R.BdR c := by
  rw [component_tmul hβ, AI.ιA_teich ⟨c, c.2.2⟩ m hm hl hc xb hxb, GlobalTheory.LocIota.ιB_algebraMap_Kur,
    OneMemClass.coe_one, map_one, one_mul]
  rfl



theorem component_const : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR), (∀ c : ↥(K0 K), ι (Γ.emb i c) = algebraMap ↥(K0 K) P.R.BdR c) → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), Algebra.TensorProduct.productMap ι P.ιB (β (I.io (fun j => PowerSeries.C (o j)))) = ι (o i : ↥LL.1) := by
  intro l _ P AI T K s LL hG Γ R I hI β hβ i ι hι o
  obtain ⟨-, -, hu⟩ := GlobalTheory.T.unramifiedIntegers_tensor_eq_letterwise_product_Ainf l P K s LL hG Γ.emb Γ.emb_bij
  refine const_eq
    (fun a => ∃ (c : ↥(K0 K)) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ (c : Om l) ^ m = 1 ∧
      ∀ j, ((a j : ↥(OL LL)) : ↥LL.1) = Γ.emb j c)
    (fun S _ _ f f' h => hu S f f' fun c m hm hl hc a ha => h a ⟨c, m, hm, hl, hc, ha⟩) I.io
    ((Algebra.TensorProduct.productMap ι P.ιB).toRingHom.comp β)
    (ι.toRingHom.comp (algebraMap ↥(OL LL) ↥LL.1)) i (component_algebraMap hβ ι) ?_ o
  rintro a ⟨c, m, hm, hl, hc, ha⟩
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hc
  have h1 := component_teich hβ ι c m hm hl hc xb hxb
  rw [← hI c m hm hl hc xb hxb a ha, ← hι, ← ha] at h1
  exact h1

end GlobalTheory.EvalIdem
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.Per.PerMat

theorem li_of_frac {B : Type} [CommRing B] [IsDomain B] {d : ℕ} {ι G F : Type} [Fintype ι] [Field F]
    (κ : F →+* B) (σ : G → B →+* B) (M : G → Matrix (Fin d) (Fin d) B) (v : ι → Fin d → B)
    (hv : ∀ i g, (M g).mulVec (fun r => σ g (v i r)) = v i)
    (hfrac : ∀ a b : B, b ≠ 0 → (∀ g, σ g a * b = a * σ g b) → ∃ k : F, a = κ k * b)
    (hind : ∀ k : ι → F, ∑ i, κ (k i) • v i = 0 → k = 0) :
    LinearIndependent B v := by
  classical
  rw [Fintype.linearIndependent_iff]
  suffices H : ∀ n : ℕ, ∀ c : ι → B, (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ n →
      ∑ i, c i • v i = 0 → c = 0 by
    intro c hc i; exact congrFun (H _ c le_rfl hc) i
  intro n
  induction n with
  | zero =>
    intro c hcard _
    funext i
    by_contra h
    simp only [Pi.zero_apply] at h
    have hi : i ∈ Finset.univ.filter (fun i => c i ≠ 0) := by simp [h]
    rw [Nat.le_zero, Finset.card_eq_zero] at hcard
    simp [hcard] at hi
  | succ n ih =>
    intro c hcard hc
    by_contra hne
    obtain ⟨i0, hi0⟩ : ∃ i0, c i0 ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext h)
    have hσ : ∀ g, ∑ i, σ g (c i) • v i = 0 := by
      intro g
      have e1 : (fun r => σ g ((∑ i, c i • v i) r)) = ∑ i, σ g (c i) • (fun r => σ g (v i r)) := by
        funext r; simp [Finset.sum_apply, map_sum, map_mul]
      have h1 : (M g).mulVec (fun r => σ g ((∑ i, c i • v i) r)) = ∑ i, σ g (c i) • v i := by
        rw [e1, Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_smul, hv]
      rw [← h1, hc]
      simp only [Pi.zero_apply, map_zero]
      exact Matrix.mulVec_zero (M g)
    have hrel : ∀ g i, σ g (c i) * c i0 = c i * σ g (c i0) := by
      intro g
      have key := ih (fun i => c i0 * σ g (c i) - σ g (c i0) * c i) ?_ ?_
      · intro i
        have := congrFun key i
        simp only [Pi.zero_apply] at this
        linear_combination this
      · have hsub : Finset.univ.filter (fun i => c i0 * σ g (c i) - σ g (c i0) * c i ≠ 0) ⊆
            (Finset.univ.filter (fun i => c i ≠ 0)).erase i0 := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hi ⊢
          refine ⟨?_, ?_⟩
          · rintro rfl; apply hi; ring
          · intro h0; apply hi; rw [h0]; simp
        have h2 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (by simp [hi0])] at h2
        omega
      · have e : ∑ i, (c i0 * σ g (c i) - σ g (c i0) * c i) • v i =
            c i0 • ∑ i, σ g (c i) • v i - σ g (c i0) • ∑ i, c i • v i := by
          simp only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, mul_smul]
        rw [e, hσ g, hc, smul_zero, smul_zero, sub_zero]
    choose k hk using fun i => hfrac (c i) (c i0) hi0 (fun g => hrel g i)
    have hk0 : ∑ i, κ (k i) • v i = 0 := by
      have h3 : c i0 • ∑ i, κ (k i) • v i = 0 := by
        calc c i0 • ∑ i, κ (k i) • v i = ∑ i, c i • v i := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [smul_smul, hk i, mul_comm]
          _ = 0 := hc
      exact (smul_eq_zero.1 h3).resolve_left hi0
    have h4 := congrFun (hind k hk0) i0
    have h1 := hk i0
    rw [h4, Pi.zero_apply, map_zero, zero_mul] at h1
    exact hi0 h1

end GlobalTheory.Per.PerMat

namespace GlobalTheory.Per.PerMat

theorem exists_invertible_invariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ j : Fin d, ∃ (m : ℕ) (c : Fin m → Per.Bcris l) (v : Fin m → Fin d → Per.Bcris l), (∀ i (g : ↥(GK K)), ((ρ g).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) (v i r)) = v i) ∧ (Pi.single j 1 : Fin d → Per.Bcris l) = ∑ i, c i • v i) → ∃ U U' : Matrix (Fin d) (Fin d) (Per.Bcris l), U * U' = 1 ∧ (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) := by
  intro l _ K P AI T d ρ hspan
  classical
  obtain ⟨-, hdom, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  haveI : IsDomain (Per.Bcris l) :=
    Function.Injective.isDomain (T.eB.symm : Per.Bcris l →+* P.R.B) T.eB.symm.injective
  choose m c v hv hsum using hspan
  let κ : ↥(K0 K) →+* Per.Bcris l := T.eB.toRingHom.comp (algebraMap ↥(K0 K) P.R.B)
  letI : Algebra ↥(K0 K) (Per.Bcris l) := κ.toAlgebra
  let S : Set (Fin d → Per.Bcris l) := Set.range (fun q : (Σ j, Fin (m j)) => v q.1 q.2)
  obtain ⟨b, hbS, hspanb, hli⟩ := exists_linearIndependent (↥(K0 K)) S
  have hfin : b.Finite := (Set.finite_range _).subset hbS
  haveI : Fintype b := hfin.fintype
  have hvb : ∀ (x : b) (g : ↥(GK K)), ((ρ g).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) ((x : Fin d → Per.Bcris l) r)) = x := by
    rintro ⟨x, hx⟩ g
    obtain ⟨⟨j, i⟩, rfl⟩ := hbS hx
    exact hv j i g
  have hliB : LinearIndependent (Per.Bcris l) (Subtype.val : b → Fin d → Per.Bcris l) := by
    refine li_of_frac κ (fun g : ↥(GK K) => Per.σB (g : GQ l)) (fun g => (ρ g).map (Per.zB l)) _ hvb ?_ ?_
    · intro a a' ha' h
      obtain ⟨k, hk⟩ := GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K (T.eB.symm a) (T.eB.symm a')
        (by simpa using ha') (fun g hg => by
          apply T.eB.injective
          rw [map_mul, map_mul, T.actB, T.actB]
          simpa using h ⟨g, hg⟩)
      refine ⟨k, ?_⟩
      have := congrArg T.eB hk
      simpa [κ] using this
    · intro k hk
      rw [Fintype.linearIndependent_iff] at hli
      funext x
      refine hli k ?_ x
      rw [← hk]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← algebraMap_smul (Per.Bcris l) (k y) (y : Fin d → Per.Bcris l)]
      rfl
  have hsp : ⊤ ≤ Submodule.span (Per.Bcris l) (Set.range (Subtype.val : b → Fin d → Per.Bcris l)) := by
    rw [Subtype.range_coe, ← (Pi.basisFun (Per.Bcris l) (Fin d)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply, hsum j]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have h1 : v j i ∈ Submodule.span (↥(K0 K)) b := by
      rw [hspanb]; exact Submodule.subset_span ⟨⟨j, i⟩, rfl⟩
    exact Submodule.span_le_restrictScalars (↥(K0 K)) (Per.Bcris l) b h1
  let bb := Module.Basis.mk hliB hsp
  have hcard : Fintype.card b = d := by
    rw [← Module.finrank_eq_card_basis bb, Module.finrank_fin_fun]
  let e : b ≃ Fin d := Fintype.equivFinOfCardEq hcard
  let bd := bb.reindex e
  refine ⟨(Pi.basisFun (Per.Bcris l) (Fin d)).toMatrix bd, bd.toMatrix (Pi.basisFun (Per.Bcris l) (Fin d)),
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, fun g => ?_⟩
  ext i j
  have hx := congrFun (hvb (e.symm j) g) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, bd, bb] using hx

end GlobalTheory.Per.PerMat
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.SeedFil
open Module Formalism.MainNotions.N

theorem crys_filtered : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (a : ℤ), ∀ y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a, ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ ∧ d i ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) (k i) ∧ b i ∈ (P.PD K).Fil (a - k i)) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI TT K V _ _ _ ρ hC a y hy
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : ↥LL.1 ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module ↥LL.1 V := Module.compHom V (e : ↥LL.1 →+* ℚ_[l])
  haveI : IsScalarTower ℚ_[l] ↥LL.1 V := ⟨fun c x v => by
    show e (c • x) • v = c • (e x • v)
    have h1 := e.toLinearEquiv.map_smul c x
    simp only [AlgEquiv.toLinearEquiv_apply] at h1
    rw [h1, smul_eq_mul, mul_smul]⟩
  haveI : FiniteDimensional ↥LL.1 V := Module.Finite.of_restrictScalars_finite ℚ_[l] _ V
  let ρ' : Representation ↥LL.1 ↥(GK K) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := fun u w => (ρ g).map_add u w
          map_smul' := fun c v => (ρ g).map_smul (e c) v }
      map_one' := by ext v; simp
      map_mul' := fun g h => by ext v; simp; rfl }
  have hV : finrank ↥LL.1 V = finrank ℚ_[l] V := by
    rw [← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V, IntermediateField.finrank_bot, one_mul]
  have hB : ∀ g x, actVB (P.PD K) ρ' g x = actVB (P.PD K) ρ g x := fun g x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [actVB]; rfl
    | add u w hu hw => simp only [map_add (f := _), hu, hw]
  have hR : ∀ g x, actVdR (P.PD K) ρ' g x = actVdR (P.PD K) ρ g x := fun g x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [actVdR]; rfl
    | add u w hu hw => simp only [map_add (f := _), hu, hw]
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ' ↔ x ∈ DdR (P.PD K) ρ := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hR]
  have hDc : (Dcris (P.PD K) ρ').restrictScalars ℚ_[l] = Dcris (P.PD K) ρ := by
    ext x
    simp only [Submodule.restrictScalars_mem, Dcris, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, hB]
  set_option synthInstance.maxHeartbeats 200000 in
  have hCr : finrank ↥LL.1 ↥(Dcris (P.PD K) ρ') = finrank ℚ_[l] ↥(Dcris (P.PD K) ρ) := by
    rw [← hDc, LinearEquiv.finrank_eq
      ((Submodule.restrictScalarsEquiv ℚ_[l] ↥LL.1 _ (Dcris (P.PD K) ρ')).restrictScalars ℚ_[l]),
      ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 ↥(Dcris (P.PD K) ρ'), IntermediateField.finrank_bot, one_mul]
  have hC' : IsCrys (P.PD K) ρ' := by
    unfold IsCrys at hC ⊢
    rw [hCr, hV]; exact hC
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI TT K LL V ρ' hC').1
  obtain ⟨m, k, b, d, h, hy'⟩ := GlobalTheory.DRFil.deRham_filtered l P AI TT K LL V ρ' hDR a y hy
  exact ⟨m, k, b, d, fun i => ⟨(hD _).1 (h i).1, (h i).2.1, (h i).2.2⟩, hy'⟩

end GlobalTheory.SeedFil
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.hodgeJumpMultiplicity_restrict_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) τ a = multV (P.PD K) ρ (τ.comp (IntermediateField.inclusion h)) a := by
  first | exact @GlobalTheory.JumpRestrict.multV_restrict | exact GlobalTheory.JumpRestrict.multV_restrict | (intros; apply GlobalTheory.JumpRestrict.multV_restrict <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ i : Let K, Set.BijOn (φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) (Di (HW l) h T (i - 1)) (Di (HW l) h T i)) ∧ (⨆ i : Let K, Di (HW l) h T i) = Dcris ((D.loc l).PD K) T.ρ ∧ iSupIndep (fun i : Let K => Di (HW l) h T i) ∧ Function.Injective (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  first | exact @GlobalTheory.NL.PhiD.phi_letters | exact GlobalTheory.NL.PhiD.phi_letters | (intros; apply GlobalTheory.NL.PhiD.phi_letters <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wachExpansion_basis_divisibility : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → Full (Di (HW l) h T i) (Lat C h T i ζ) → (∀ (a : AA K LL) (x : ↥(W.N T)), ex C h T i ζ (a • x) = conv (W.lev i ζ a) (ex C h T i ζ x)) ∧ ∀ (r : ℕ) (nb : Module.Basis (Fin r) (AA K LL) ↥(W.N T)), (∀ e : Fin r → PowerSeries ↥LL.1, ∑ j, conv (e j) (ex C h T i ζ (nb j)) = 0 → e = 0) ∧ (∀ f ∈ Lat C h T i ζ, ∃ e : Fin r → PowerSeries ↥LL.1, f = ∑ j, conv (e j) (ex C h T i ζ (nb j))) ∧ ∀ (y : ↥(W.N T)) (k : ℕ), (∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ y j = f (j - k)) ↔ ∀ j, nb.repr y j ∈ van W i ζ k := by
  first | exact @GlobalTheory.NL.LevInj.expansion_basis | exact GlobalTheory.NL.LevInj.expansion_basis | (intros; apply GlobalTheory.NL.LevInj.expansion_basis <;> assumption)
end
