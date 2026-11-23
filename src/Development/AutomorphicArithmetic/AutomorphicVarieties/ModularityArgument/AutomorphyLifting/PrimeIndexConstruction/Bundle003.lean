module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle069
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle071
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle073
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.ExistsSplittingAuxiliaryCharacterForTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTrans

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
open UpperTheory.V.Af

namespace UpperTheory.V.Z.Win.Birth

section Conj

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

private def conjEquiv (g : GL (Fin n) k) : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))
    (Matrix.mulVecLin ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    (by rw [← Matrix.mulVecLin_mul, ← Units.val_mul, mul_inv_cancel]; simp)
    (by rw [← Matrix.mulVecLin_mul, ← Units.val_mul, inv_mul_cancel]; simp)

private theorem conjEquiv_apply (g : GL (Fin n) k) (v : Fin n → k) :
    conjEquiv g v = (g : Matrix (Fin n) (Fin n) k).mulVec v := rfl

private theorem intertwine {r r' : Γ →* GL (Fin n) k} {g : GL (Fin n) k}
    (hg : ∀ s, r' s = g * r s * g⁻¹) (s : Γ) (v : Fin n → k) :
    (r' s : Matrix (Fin n) (Fin n) k).mulVec (conjEquiv g v) =
      conjEquiv g ((r s : Matrix (Fin n) (Fin n) k).mulVec v) := by
  have h : (r' s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) =
      (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k) := by
    rw [← Units.val_mul, ← Units.val_mul, hg s, inv_mul_cancel_right]
  simp only [conjEquiv_apply, Matrix.mulVec_mulVec, h]

private theorem ss_of_conj {r r' : Γ →* GL (Fin n) k} (h : RepIso r r') (H : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  intro W hW
  have h0 : IsInv r (W.comap (conjEquiv g).toLinearMap) := by
    intro s v hv
    have hv' : conjEquiv g v ∈ W := hv
    show conjEquiv g _ ∈ W
    rw [← intertwine hg]
    exact hW s _ hv'
  obtain ⟨W', hW', hc⟩ := H _ h0
  refine ⟨W'.map (conjEquiv g).toLinearMap, ?_, ?_⟩
  · rintro s _ ⟨v, hv, rfl⟩
    exact ⟨(r s : Matrix (Fin n) (Fin n) k).mulVec v, hW' s v hv, (intertwine hg s v).symm⟩
  · have hm := (Submodule.orderIsoMapComap (conjEquiv g)).isCompl hc
    have hW2 : (Submodule.orderIsoMapComap (conjEquiv g)) (W.comap (conjEquiv g).toLinearMap) = W := by
      ext x
      simp [Submodule.orderIsoMapComap_apply, Submodule.mem_map]
    rw [hW2] at hm
    exact hm

end Conj

private theorem frob_of_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : RepIso r r')
    {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂ} (H : FrobEig ι r w B) : FrobEig ι r' w B := by
  obtain ⟨g, hg⟩ := h
  intro A hA
  obtain ⟨h1, h2⟩ := H A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · rw [hg s, h1 s hs, mul_one, mul_inv_cancel]
  · rw [hg σ⁻¹, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact h2 σ hσ

theorem prIso : PrIso := by
  intro F Ω _ _ _ _ _ _ l _ ι n r r' h
  rintro ⟨π, h1, h2, h3⟩
  exact ⟨π, h1, ⟨ss_of_conj h h2.1, h2.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, frob_of_conj h hB'⟩⟩, h3⟩

end UpperTheory.V.Z.Win.Birth
end
end

section

open UpperTheory.V.Z.Win.Birth

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

private theorem cont_res {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω)
    [NumberField F] : Continuous (resQ F) := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  exact (galEmbTop ℚ F Ω).1.continuous

private theorem not_both {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q : ℕ} (h : p.Coprime q)
    (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (q : Ω) < 1 := by
  intro hq
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (a : Ω) * p + (b : Ω) * q = 1 := by exact_mod_cast congrArg (Int.cast (R := Ω)) hab
  have hz : ∀ (z : ℤ) (x : Ω), A.valuation x < 1 → A.valuation (z * x) < 1 := fun z x hx => by
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right ((A.valuation_le_one_iff _).2 (intCast_mem A z)) zero_le hx
  have := A.valuation.map_add_lt (hz a _ hp) (hz b _ hq)
  rw [e, map_one] at this
  exact lt_irrefl _ this

theorem UpperTheory.V.Z.Win.Birth.mixOfP :
    MixSeedP → MixOfP := by
  intro hP Ω _ _ _ l hl c D T k₀ _ _ φ ι H C
  have hl2 : l ≠ 2 := H.good.l_odd
  obtain ⟨hsp, w, w', hne, hw, hw', hpl⟩ := UpperTheory.quadratic_field_split_prime_two_places Ω k₀ H.deg l hl.out H.spl
  obtain ⟨hsp2, u, -, -, hu, -, -⟩ := UpperTheory.quadratic_field_split_prime_two_places Ω k₀ H.deg 2 Nat.prime_two H.sp2
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  have hker : ∀ g : G ℚ Ω, D.ξ g = 1 → up D.ξ g = 1 := fun g hg => by
    change Units.map _ (D.ξ g) = 1
    rw [hg, map_one]
  have lift : ∀ g : G T.F Ω, resQ T.F g ∈ k₀.fixingSubgroup → ∃ s : G k₀ Ω, resQ k₀ s = resQ T.F g := fun g hg =>
    ⟨k₀.fixingSubgroupEquiv ⟨_, hg⟩, rfl⟩
  obtain ⟨Au, hAu⟩ := exists_isPlaceOver Ω u
  have hAu2 : Au.valuation ((2 : ℕ) : Ω) < 1 := by
    have h := (hAu _).2 hu
    rwa [show algebraMap k₀ Ω (((2 : ℕ) : 𝓞 k₀) : k₀) = ((2 : ℕ) : Ω) from
      map_natCast ((algebraMap k₀ Ω).comp (algebraMap (𝓞 k₀) k₀)) 2] at h
  obtain ⟨g, hg, hg4⟩ := H.two.big2 Au hAu2
  rw [Ne, C.al] at hg4
  obtain ⟨s, hs⟩ := lift g (H.sp2 Au hAu2 hg.1)
  have hsI : s ∈ Ine (F := k₀) Au := by
    have h1 : resQ T.F g ∈ Ine (F := ℚ) Au := ⟨hg.1, hg.2⟩
    rw [← hs] at h1
    exact ⟨h1.1, h1.2⟩
  obtain ⟨k, t, π, r, hk, ht, hkl, -, hc, hi, ha, hd, hr, ⟨haw, hrw⟩, hab⟩ :=
    hP k₀ Ω l hl2 (by rw [H.deg]; exact even_two) hsp ι ((up D.ξ).comp (resQ k₀))
      (Subgroup.isOpen_mono (H₁ := D.ξ.ker.comap (resQ k₀)) (fun x hx => hker _ hx)
        (H.good.xi_open.preimage (cont_res k₀)))
      (fun x hx => by
        have h1 : IsConj (resQ k₀ x) D.cc := UpperTheory.complex_conjugations_are_conjugate Ω _ _ hx H.good.isCC
        have h2 : D.ξ (resQ k₀ x) = -1 := by
          rw [← H.good.xi_odd]
          exact isConj_iff_eq.1 (D.ξ.map_isConj h1)
        change Units.map _ (D.ξ (resQ k₀ x)) = -1
        rw [h2]
        exact Units.ext (by simp))
      (fun A hA x hx => hker _ (H.two.xi A (fun p hp => by
        rw [Finset.mem_singleton.1 hp]
        exact not_both A ((Nat.coprime_primes hl.out Nat.prime_two).2 hl2) hA) ⟨hx.1, hx.2⟩))
      ⟨u, Au, (by
        rw [show normV u = Ideal.absNorm u.asIdeal by
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
          rfl]
        exact (hsp2 u hu).1), hAu, fun h => hg4 (by
        have h1 : up D.ξ (resQ k₀ s) = 1 := h hsI
        rw [← hs, h1]
        simp [Cong])⟩
      ⟨s ^ 2, by
        rw [map_pow, ← pow_mul, MonoidHom.comp_apply, hs]
        exact hg4⟩
      (fun A hA => by
        obtain ⟨x, hx, hx4⟩ := H.two.bigL A hA
        rw [Ne, C.al] at hx4
        obtain ⟨y, hy⟩ := lift x (H.spl A hA hx)
        have h1 : resQ T.F x ∈ Dec (F := ℚ) A := hx
        rw [← hy] at h1
        refine ⟨y ^ 4, pow_mem (show y ∈ Dec (F := k₀) A from h1) 4, ?_⟩
        rw [map_pow, MonoidHom.comp_apply, hy]
        exact hx4)
      {w} ⟨w, rfl, hw⟩ ⟨w', hne.symm, hw'⟩
  obtain ⟨h1, h1'⟩ := (hab w hw).1 rfl
  obtain ⟨h2, h2'⟩ := (hab w' hw').2 hne.symm
  obtain ⟨he, he'⟩ := UpperTheory.exists_ringHom_to_localField_inducing_place k₀ l ι
  obtain ⟨τ, hτ⟩ := he w hw
  obtain ⟨τ', hτ'⟩ := he w' hw'
  refine ⟨k, t, r, And.symm ⟨hrw, ?_⟩⟩
  refine ⟨hk, ht, hkl, hc, hi, ⟨π, ha, _, _, fun h => hne (he' w w' τ τ' hτ hτ' h), h1' τ hτ, h2' τ' hτ'⟩,
    hd, hr, haw, fun A A' hA x hx hAA => ?_⟩
  rcases hpl A A' hA x hx hAA with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨h1 A a, h2 A' b⟩
  · exact Or.inr ⟨h2 A a, h1 A' b⟩
end

section

open UpperTheory.V.Z.Win.Birth

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

private theorem finOrd_kills {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {l : ℕ} [Fact l.Prime] {M : ℕ} (hM : 1 ≤ M) {φ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) : IsOfFinOrder φ := by
  have ho : IsOpen (φ.ker : Set (_root_.Formalism.ConjugateSelfDual.G ℚ Ω)) := by
    have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
      classical
      refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
      simpa [Polynomial.mem_nthRoots hM] using hζ
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
    · simp only [Set.mem_iInter]
      exact fun ζ _ => Subgroup.one_mem _
    · simp only [Set.mem_iInter] at hs
      exact hφ s fun ζ hζ => hs ζ hζ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hfi : Finite (_root_.Formalism.ConjugateSelfDual.G ℚ Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨_, hpos, MonoidHom.ext fun s => ?_⟩
  rw [MonoidHom.pow_apply, ← map_pow]
  exact φ.ker.pow_index_mem s

private theorem cong_iff {l : ℕ} [Fact l.Prime] {c : Coef l} (a : c.Oˣ) :
    Cong (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom a) 1 ↔ residue c.O a = 1 := by
  rw [← map_one (residue c.O), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, (UpperTheory.V.Fr.sc_norm l c _).2]
  rfl

private theorem toB_chi {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)
    (g : _root_.Formalism.ConjugateSelfDual.G ℚ Ω) : toB (chiO ℚ Ω l c.O) g = cycBar ℚ Ω l g := by
  ext
  rfl

theorem rhoExP (h1 : ExistsSplittingAuxiliaryCharacterForTower) (h2 : PhiFacts) (h3 : ModEx4) : RhoExP := by
  intro hP Ω _ _ _ l _ c D T₀ hctx hok hfour ι B c₀
  obtain ⟨N, w, θ, haux, hsp, hw⟩ := h1 Ω l c D T₀ hctx hfour
  obtain ⟨hcc, hev, hk⟩ := h2 Ω l c D T₀ hctx hok hfour
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two haux.odd
  have hcc' : toB (phi D T₀.pr) D.cc = -1 := by
    show Units.map _ (phi D T₀.pr D.cc) = _
    rw [hcc]
    ext
    simp
  have hne : toB (phi D T₀.pr) ≠ 1 := by
    intro h
    have h' := congrArg (fun u : (Qbar l)ˣ => (u : Qbar l)) hcc'
    rw [h] at h'
    simp only [MonoidHom.one_apply, Units.val_one, Units.val_neg] at h'
    have h2' : (2 : Qbar l) = 0 := by linear_combination h'
    exact two_ne_zero h2'
  have hfin : IsOfFinOrder (toB (phi D T₀.pr)) := finOrd_kills haux.pos hsp.1
  obtain ⟨k₀, hk₀⟩ := hP l Ω ι D.cc hctx.1.isCC N w (toB (phi D T₀.pr)) θ haux hsp hne
  obtain ⟨n, hn⟩ : ∃ n, n = B + k₀ + 2 := ⟨_, rfl⟩
  have hl1 : 1 ≤ l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have hle : n ≤ (l - 1) * n := Nat.le_mul_of_pos_left n hl1
  have hev' : Even ((l - 1) * n) := (Nat.Odd.sub_odd hodd odd_one).mul_right n
  obtain ⟨k, hkdef⟩ : ∃ k, k = D.e + 1 + (l - 1) * n := ⟨_, rfl⟩
  have hkodd : Odd k := by
    rw [hkdef, add_assoc, add_comm 1, ← add_assoc]
    exact (hev.add hev').add_one
  have hk1 : 1 ≤ k := by omega
  have hcong : k - 1 ≡ D.e [MOD l - 1] := by
    unfold Nat.ModEq
    rw [show k - 1 = D.e + (l - 1) * n by omega, Nat.add_mul_mod_self_left]
  obtain ⟨ρ, hρ, hrw⟩ := hk₀ k (by omega) (by rw [hcc', hkodd.neg_one_pow])
  obtain ⟨hsq, hdec⟩ := hk k hk1 hcong
  have e : ∀ g, (cycBar ℚ Ω l ^ (k - 1) * toB (phi D T₀.pr)) g =
      Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Phi D T₀.pr k g) := by
    intro g
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Phi, map_mul, map_pow]
    rw [← toB_chi c g]
    rfl
  have hI : IrrOpen ρ := by
    refine (sI l haux.odd Ω ι _ θ k (by omega) hfin ρ hρ).2 ⟨resQ T₀.F T₀.g0, fun h => hsq ?_⟩
    rw [e] at h
    have := (cong_iff (Phi D T₀.pr k (resQ T₀.F T₀.g0) ^ 2)).1 (by rw [map_pow]; exact h)
    rwa [Units.val_pow_eq_pow_val, map_pow] at this
  have hg1 : Raw.bar (Phi D T₀.pr k) (resQ T₀.F T₀.g0) ≠ 1 := fun h => hsq (by rw [h, one_pow])
  obtain ⟨c₁, h, ρ₁, x, hc₀, hM⟩ := h3 Ω l ι c D T₀.pr θ k hk1 ρ hρ hdec (resQ T₀.F T₀.g0) hg1 c₀
  exact ⟨w, θ, k, ρ, c₁, h, ρ₁, x, haux.prime, hw, haux.pow, haux.mu, by omega, hcong, hρ, ⟨hI, hrw⟩, hc₀, hM⟩

end UpperTheory.V.Cu2

end
end
