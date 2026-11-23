module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToZModPowKummerEqIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle069
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem ev_not_mem (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  simpa [Ideal.dvd_span_singleton] using hv
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem isIrr_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨h1, -, h3⟩ := hr
  refine ⟨h1, fun _ _ _ => Submodule.mem_top, fun W _ hi => ?_⟩
  have key := h3 (W.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))) le_top (fun s v hv => by
    have h4 := hi s _ hv
    rw [hg s] at h4
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4)
  have hs : Function.Surjective (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)) := fun v =>
    ⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v, by
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  have e := Submodule.map_comap_eq_of_surjective hs W
  rcases key with key | key
  · left
    rw [← e, key, Submodule.map_bot]
  · right
    rw [← e, key, Submodule.map_top, LinearMap.range_eq_top.mpr hs]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem conj_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (g : GL (Fin n) k) (s : Γ) :
    ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (χ s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]

theorem UpperTheory.level_twist_cyclotomic_pow :
    ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ) (r : G K Ω →* GL (Fin n) (Qbar l)) (j : ℤ), Level l M m r → Level l M (fun i => m i + j) (tw r (cycBar K Ω l ^ j)) := by
  intro K Ω _ _ _ _ _ _ l _ n M m r j H
  have hz : Continuous fun s : G K Ω => ((cycZ K Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ K Ω l)
  have hcyc : Continuous fun s : G K Ω => (cycBar K Ω l s : Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp hz)
  have hχ : Continuous fun s : G K Ω => cycBar K Ω l s ^ j := (cont_units _ hcyc).zpow j
  refine ⟨?_, fun w hw => ?_, fun w hw => ?_⟩
  · refine cont_units _ ?_
    simp only [tw_val]
    exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp H.cont)
  · obtain ⟨A, hA, χ, hk, g, hg⟩ := H.away w hw
    refine ⟨A, hA, χ, hk, g, fun s hs => ?_⟩
    have h1 : cycBar K Ω l s = 1 := by
      simp only [cycBar, MonoidHom.comp_apply, GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hA hw hs, map_one]
    have h2 : (cycBar K Ω l ^ j) s = 1 := by
      show cycBar K Ω l s ^ j = 1
      rw [h1, one_zpow]
    rw [conj_tw, h2, Units.val_one, one_smul, hg s hs]
  · obtain ⟨A, hA, χ, κ, hk, ⟨g, hg⟩, hκ, hor⟩ := H.above w hw
    refine ⟨A, hA, χ, fun i => κ i * (cycBar K Ω l ^ j).comp (Dec (F := K) A).subtype, hk, ⟨g, fun s => ⟨fun a b hab => ?_, fun a => ?_⟩⟩,
      fun i s hs => ?_, ?_⟩
    · have := (hg s).1 a b hab
      show ((g * tw r _ s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) a b = 0
      rw [conj_tw, Matrix.smul_apply]
      exact smul_eq_zero_of_right _ this
    · have := (hg s).2 a
      show ((g * tw r _ s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) a a = _
      rw [conj_tw, Matrix.smul_apply, smul_eq_mul, this]
      exact mul_comm _ _
    · show κ i s * cycBar K Ω l s ^ j = _
      rw [hκ i s hs, zpow_add, mul_right_comm]
    · rcases hor with h | ⟨O, _, _, _, Bw, hI, hP⟩
      · left
        intro a b e
        apply h a b
        rw [mul_right_comm] at e
        exact mul_right_cancel e
      · right
        obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
        exact ⟨O, _, _, _, Bw, hI, GlobalTheory.HodgeOfTrue.potCrys_twistBy T Bw
          ((cycBar K Ω l ^ j).comp (Dec (F := K) A).subtype) _ hP (UpperTheory.isCrysAt_cyclotomic_zpow_restrict_decompositionGroup K Ω l A O Bw j)⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap UpperTheory.V UpperTheory.V.Af.Wd

private theorem nil_line {k W : Type} [Field k] [AddCommGroup W] [Module k W] (h1 : finrank k W = 1) {N : End k W}
    (hN : IsNilpotent N) : N = 0 := by
  obtain ⟨y, hy0, hy⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨c, hc⟩ := hy (N y)
  obtain ⟨n, hn⟩ := hN
  have hp : ∀ m : ℕ, (N ^ m) y = c ^ m • y := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  have h2 := hp n
  rw [hn, LinearMap.zero_apply] at h2
  have hc0 : c = 0 := by
    rcases smul_eq_zero.1 h2.symm with h | h
    · exact (pow_eq_zero_iff'.1 h).1
    · exact absurd h hy0
  ext x
  obtain ⟨a, rfl⟩ := hy x
  rw [map_smul, ← hc, hc0]
  simp

private theorem snoc_ops {k W' W W'' Γ : Type} [Field k] [AddCommGroup W'] [Module k W'] [AddCommGroup W] [Module k W]
    [AddCommGroup W''] [Module k W''] {n : ℕ} {N' : End k W'} {N : End k W} {N'' : End k W''} {R' : Γ → End k W'}
    {R : Γ → End k W} {R'' : Γ → End k W''} {f : W' →ₗ[k] W} {p : W →ₗ[k] W''} (hf : Function.Injective f)
    (hp : Function.Surjective p) (hex : Function.Exact f p) (h1 : finrank k W'' = 1) (hfN : ∀ x, f (N' x) = N (f x))
    (hfR : ∀ a x, f (R' a x) = R a (f x)) (hpN : ∀ x, p (N x) = N'' (p x)) (hpR : ∀ a x, p (R a x) = R'' a (p x))
    {μ : Γ → Fin (n + 1) → k} (hI : IsTri (ops N' R') (ops 0 fun a i => μ a (Fin.castSucc i))) (hN : IsNilpotent N'')
    (hl : ∀ a y, R'' a y = μ a (Fin.last n) • y) : IsTri (ops N R) (ops 0 μ) := by
  refine UpperTheory.abelianField_window_triple_snoc k _ _ _ _ n (ops N' R') _ (ops N'' R'') f p hf hp hex h1 ?_ ?_ _ ?_ ?_
  · rintro (_ | σ) x
    · exact hfN x
    · exact hfR σ x
  · rintro (_ | σ) x
    · exact hpN x
    · exact hpR σ x
  · convert hI using 1
    funext a i
    cases a <;> rfl
  · rintro (_ | σ) y
    · rw [ops_none, ops_none, nil_line h1 hN]
      simp
    · exact hl σ y

theorem UpperTheory.weilDeligne_triangularizable :
    UpperTheory.V.Af.Wd.WdTri := by
  intro F Ω _ _ _ _ _ l _ ι w A h O _ _ _ Bw hj L n
  induction n with
  | zero =>
    intro V _ _ _ _ _ ρ κ μ ⟨b, _⟩ _ hV
    haveI := hV.finite
    have h0 : finrank ℂ (WDSpace (Loc.PP l) ι ρ) = 0 := by
      rw [LetterDim.finrank_wdSpace l _ ι _ L V ρ hV, finrank_eq_card_basis b, Fintype.card_fin]
    exact ⟨finBasisOfFinrankEq ℂ _ h0, fun a => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro V _ _ _ _ _ ρ κ μ hT hκ hV
    obtain ⟨S, hS, p, hp, hker, hpT, hT'⟩ := UpperTheory.weilDeligne_triangular_initial_segment _ _ _ n _ _ hT
    let ρ' : Representation ↥L.1 ↥(GK Bw.Kw) ↥S := ρ.subrepresentation S fun g x hx => hS g x hx
    have hf : ∀ g v, S.subtype (ρ' g v) = ρ g (S.subtype v) := fun _ _ => rfl
    have hpe : ∀ g v, p (ρ g v) = Loc.chRep (κ (Fin.last n)) g (p v) := fun g v => hpT g v
    have hex : Function.Exact S.subtype p := by
      rw [LinearMap.exact_iff, hker, Submodule.range_subtype]
    obtain ⟨h', h'', hinj, hsurj, hexW⟩ := UpperTheory.weil_deligne_functor_exactness l ι Bw.Kw L ↥S V ↥L.1 ρ' ρ (Loc.chRep (κ (Fin.last n)))
      S.subtype p hf hpe S.subtype_injective hp hex hV
    haveI := hV.finite
    haveI := h'.finite
    haveI := h''.finite
    have h1 : finrank ℂ (WDSpace (Loc.PP l) ι (Loc.chRep (κ (Fin.last n)))) = 1 := by
      rw [LetterDim.finrank_wdSpace l _ ι _ L _ _ h'', finrank_self]
    have hI := ih ↥S ρ' (fun i => κ (Fin.castSucc i)) (fun σ i => μ σ (Fin.castSucc i)) hT'
      (fun i => hκ (Fin.castSucc i)) h'
    exact snoc_ops hinj hsurj hexW h1 (wdLin_wdN _ ι hf) (wdLin_wdRho _ ι Bw h hj hf) (wdLin_wdN _ ι hpe)
      (wdLin_wdRho _ ι Bw h hj hpe) hI (isNilpotent_wdN _ ι _) (hκ (Fin.last n) h'')
end

section

noncomputable section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct GlobalTheory.Pst Polynomial

private theorem zpow_fix {Q R : Type} [Field Q] [CommRing R] [Algebra Q R] (f : R →ₐ[Q] R) (T : Rˣ) (c : Qˣ)
    (h : (c : Q) • f (T : R) = T) (m : ℤ) : ((c ^ m : Qˣ) : Q) • f ((T ^ m : Rˣ) : R) = ((T ^ m : Rˣ) : R) := by
  have e : Units.map (algebraMap Q R : Q →* R) c * Units.map (f : R →* R) T = T := by
    ext; simpa [Algebra.smul_def] using h
  have e' : Units.map (algebraMap Q R : Q →* R) (c ^ m) * Units.map (f : R →* R) (T ^ m) = T ^ m := by
    rw [map_zpow, map_zpow, ← mul_zpow, e]
  rw [Algebra.smul_def]
  exact congrArg Units.val e'

private theorem smul_mul_tmul {Q A R : Type} [Field Q] [Field A] [CommRing R] [Algebra Q R] [Algebra Q A]
    (c : Q) (x : A ⊗[Q] R) (b : R) : algebraMap Q A c • (x * (1 : A) ⊗ₜ[Q] b) = x * (1 : A) ⊗ₜ[Q] (c • b) := by
  rw [algebraMap_smul, tmul_smul, mul_smul_comm]

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l}

private theorem stRep_mul (κ η : ↥(GK K) →* (↥L.1)ˣ) (g : ↥(GK K)) (a : ↥L.1) (h : (κ g : ↥L.1) = a * η g)
    (u : ↥L.1 ⊗[ℚ_[l]] Bst P) (b : Bst P) :
    stRep P (UpperTheory.V.Loc.chRep κ) g (u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) =
      a • (stRep P (UpperTheory.V.Loc.chRep η) g u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] actSt P (g : GQ l) b) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, stRep_tmul, stRep_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      map_mul (actSt P (g : GQ l)), smul_tmul']
    congr 1
    simp [UpperTheory.V.Loc.chRep, h, mul_assoc]
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy, smul_add]

private theorem phiV_mul (u : ↥L.1 ⊗[ℚ_[l]] Bst P) (b : Bst P) :
    phiV P ↥L.1 ↥L.1 (u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) = phiV P ↥L.1 ↥L.1 u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiSt P b := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, phiV_tmul, phiV_tmul, Algebra.TensorProduct.tmul_mul_tmul, map_mul]
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy]

private theorem phiV_pow_mul (c : ℚ_[l]) (b : Bst P) (hb : c • phiSt P b = b) (k : ℕ) (u : ↥L.1 ⊗[ℚ_[l]] Bst P) :
    (algebraMap ℚ_[l] ↥L.1 c) ^ k • (phiV P ↥L.1 ↥L.1 ^ k) (u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) =
      (phiV P ↥L.1 ↥L.1 ^ k) u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, mul_smul, ← map_smul, phiV_mul, smul_mul_tmul, hb, ih]

theorem UpperTheory.weilDeligne_character_twist_period :
    UpperTheory.V.Af.Wd.TwistPer := by
  intro l _ K L κ χ η m hκ hc hη
  have hu := UpperTheory.weilDeligne_unramified_period l K L η hc hη
  unfold UpperTheory.V.Af.Wd.cycL at hκ
  generalize UpperTheory.V.Loc.PP l = P at hu hκ ⊢
  obtain ⟨u, hu0, hu1, hu2⟩ := hu
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  let T : (Bst P)ˣ := Units.map (C : P.R.B →+* Bst P) (isUnit_tB P).unit⁻¹
  have hT : (T : Bst P) = C (tInv P) := rfl
  have h1 : ∀ g : GQ l, ((P.χQ g ^ m : ℚ_[l]ˣ) : ℚ_[l]) • actSt P g ((T ^ m : (Bst P)ˣ) : Bst P) = ((T ^ m : (Bst P)ˣ) : Bst P) :=
    fun g => zpow_fix (actSt P g) T (P.χQ g) (by rw [hT, actSt_C, smul_C, smul_actQ_tInv]) m
  have h2 := zpow_fix (phiSt P) T (Units.mk0 _ hl) (by rw [hT, phiSt_C, smul_C, Units.val_mk0, smul_phiB_tInv]) m
  refine ⟨u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] ((T ^ m : (Bst P)ˣ) : Bst P), fun h0 => hu0 ?_, fun g => ?_, fun g k hk => ?_⟩
  · have := congrArg (· * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] (((T ^ m)⁻¹ : (Bst P)ˣ) : Bst P)) h0
    simpa only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, mul_one, zero_mul,
      ← Algebra.TensorProduct.one_def] using this
  · rw [stRep_mul P κ η g ((χ g : ↥L.1) * algebraMap ℚ_[l] ↥L.1 ((P.χQ (g : GQ l) ^ m : ℚ_[l]ˣ) : ℚ_[l])) ?_, hu1,
      mul_smul, smul_mul_tmul, h1]
    rw [hκ g, Units.val_mul, Units.val_mul, mul_comm (χ g : ↥L.1)]
    simp
  · have e : (l : ↥L.1) ^ (m * k) = (algebraMap ℚ_[l] ↥L.1 ((Units.mk0 _ hl ^ m : ℚ_[l]ˣ) : ℚ_[l])) ^ k := by
      simp [zpow_mul]
    rw [e, mul_smul, phiV_pow_mul P _ _ h2, ← smul_mul_assoc, hu2 g k hk]
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

theorem UpperTheory.imaginary_generator :
    UpperTheory.V.Af.Cr.ImagGen := by
  intro K _ _ _ h
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h⟩
  obtain ⟨d, e, -, h0, h1⟩ := GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq ℚ K
  have hy : e 1 ^ 2 = (d : K) := by rw [sq, h1]; simp
  have hx : ∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * e 1 := fun x => by
    refine ⟨e.repr x 0, e.repr x 1, ?_⟩
    conv_lhs => rw [← e.sum_repr x]
    rw [Fin.sum_univ_two, h0, Rat.smul_def, Rat.smul_def, mul_one]
  refine ⟨d, e 1, ?_, hy, hx⟩
  by_contra hd
  have hd0 : (0 : ℝ) ≤ d := by exact_mod_cast not_lt.1 hd
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  apply IsTotallyComplex.complexEmbedding_not_isReal φ
  have hφ : φ (e 1) ^ 2 = ((Real.sqrt d : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, hy, ← Complex.ofReal_pow, Real.sq_sqrt hd0]
    simp
  have hc : (starRingEnd ℂ) (φ (e 1)) = φ (e 1) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hφ with h2 | h2 <;> simp [h2]
  rw [ComplexEmbedding.isReal_iff]
  ext1 x
  obtain ⟨a, b, rfl⟩ := hx x
  rw [ComplexEmbedding.conjugate_coe_eq]
  simp [hc]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

theorem UpperTheory.quadratic_complex_multiplication :
    UpperTheory.V.Af.Cr.QuadCM := by
  intro F Ω _ _ _ _ _ _ d δ hδ hd
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral F δ := (halg.isAlgebraic δ).isIntegral
  let K : IntermediateField F Ω := IntermediateField.adjoin F {δ}
  haveI : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField K := NumberField.of_module_finite F K
  let y : K := IntermediateField.AdjoinSimple.gen F δ
  have hy : algebraMap K Ω y = δ := rfl
  have hy2 : y ^ 2 = algebraMap F K d := by
    apply (algebraMap K Ω).injective
    rw [map_pow, hy, hδ, ← IsScalarTower.algebraMap_apply]
  have hle : (minpoly F δ).natDegree ≤ 2 := by
    have hm : (X ^ 2 - C d : F[X]).Monic := monic_X_pow_sub_C d (by norm_num)
    have h1 := minpoly.min F δ hm (by simp [hδ])
    have h2 := natDegree_le_natDegree h1
    rwa [natDegree_X_pow_sub_C _] at h2
  have hne : (minpoly F δ).natDegree ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := (minpoly.natDegree_eq_one_iff).1 h
    have hcd : c ^ 2 = d := by
      apply (algebraMap F Ω).injective
      rw [map_pow, hc, hδ]
    let v : InfinitePlace F := Classical.arbitrary _
    have h3 := hd (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
    rw [← hcd, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  have hpos := minpoly.natDegree_pos hint
  have hdeg : (minpoly F δ).natDegree = 2 := by omega
  have hrk : Module.finrank F K = 2 := by
    rw [← hdeg]; exact IntermediateField.adjoin.finrank hint
  haveI : IsTotallyComplex K := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h3 := hd ((InfinitePlace.embedding_of_isReal hv).comp (algebraMap F K))
    rw [RingHom.comp_apply, ← hy2, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := hrk }
  haveI : IsAlgClosure K Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed F
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := F) K }
  refine ⟨K, inferInstance, inferInstance, IsCMField.ofCMExtension F K, inferInstance, inferInstance,
    inferInstance, inferInstance, hrk, y, hy, fun x => ?_⟩
  obtain ⟨f, hf, hx⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval x
  rw [IntermediateField.adjoin.powerBasis_dim, hdeg] at hf
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [hx, IntermediateField.adjoin.powerBasis_gen]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (p := f) (by omega)]
  simp only [map_add (f := _), map_mul, aeval_C, aeval_X]
  exact add_comm _ _
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open ReciprocityTheory.Neutral.Bridge.HCFR

private theorem comap_surj {E L : Type} [Field E] [Field L] (j : E ≃+* L) (v' : InfinitePlace E) :
    ∃ v : InfinitePlace L, v.comap j.toRingHom = v' := by
  refine ⟨v'.comap j.symm.toRingHom, ?_⟩
  ext x
  show v' (j.symm (j x)) = v' x
  rw [RingEquiv.symm_apply_apply]

private theorem comap_inj {E L : Type} [Field E] [Field L] (j : E ≃+* L) (u v : InfinitePlace L)
    (h : u.comap j.toRingHom = v.comap j.toRingHom) : u = v := by
  ext x
  have h1 : (u.comap j.toRingHom) (j.symm x) = (v.comap j.toRingHom) (j.symm x) := by rw [h]
  change u (j (j.symm x)) = v (j (j.symm x)) at h1
  rwa [RingEquiv.apply_symm_apply] at h1

private theorem idMap_infIdele {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (j : E ≃+* L)
    (v : InfinitePlace L) :
    CT.idMap j (infIdele E (v.comap j.toRingHom) (-1)) = infIdele L v (-1) := by
  classical
  apply Units.ext
  apply Prod.ext
  · funext u
    show CT.infEquiv j u (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) (v.comap j.toRingHom) (-1)
      (u.comap j.toRingHom)) = Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) v (-1) u
    by_cases h : u = v
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, map_neg, map_one]
    · have h' : u.comap j.toRingHom ≠ v.comap j.toRingHom := fun e => h (comap_inj j u v e)
      rw [Pi.mulSingle_eq_of_ne h', Pi.mulSingle_eq_of_ne h, map_one]
  · show CT.finMap j 1 = 1
    exact map_one _

theorem UpperTheory.heckeChar_realTransport :
    UpperTheory.V.Af.Cr.RealTransport := by
  intro F K _ _ _ _ _ _ _ h2 χ
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := h2 }
  let j : maximalRealSubfield K ≃+* F := (CMExtension.equivMaximalRealSubfield F K).symm
  refine ⟨CT.transport j χ, fun v' => ?_, fun w => ?_⟩
  · obtain ⟨v, rfl⟩ := comap_surj j v'
    refine ⟨v, ?_⟩
    show χ.1 (CT.idMap j (infIdele _ (v.comap j.toRingHom) (-1))) = χ.1 (infIdele F v (-1))
    rw [idMap_infIdele]
  · have hp : CT.plMap j (w.under (𝓞 (maximalRealSubfield K))) = w.under (𝓞 F) := by
      ext x
      show algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) ((RingOfIntegers.mapRingEquiv j).symm x) ∈ w.asIdeal ↔
        algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal
      have e : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) ((RingOfIntegers.mapRingEquiv j).symm x) =
          algebraMap (𝓞 F) (𝓞 K) x := RingOfIntegers.ext rfl
      rw [e]
    refine ⟨?_, fun hu => ?_⟩
    · have h := CT.absNorm_plMap j (w.under (𝓞 (maximalRealSubfield K)))
      rw [hp, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
      exact h.symm
    · rw [← hp] at hu
      refine ⟨(CT.transport_unrAt_iff j χ _).mpr hu, ?_⟩
      rw [CT.transport_val j χ _ hu, hp]
end
