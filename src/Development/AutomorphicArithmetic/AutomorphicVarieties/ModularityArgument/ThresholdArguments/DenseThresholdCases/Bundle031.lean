module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Deadel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ExistsEigenform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LevelVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCentChar
import GroundTheory.AutomorphicForms.GL2Classical.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle762
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle272
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle163
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle088
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle306
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle320
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PstExact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent

@[expose] public section

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
  UpperTheory.V.Br CongruenceSubgroup
private theorem untwist (k N : ℕ) [NeZero N] (hk : 1 ≤ k) (χ ψ : DirichletCharacter ℂ N) (g : Eigenform k N χ) :
    ∃ (χ' : DirichletCharacter ℂ (N * N)) (g' : Eigenform k (N * N) χ'), ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      g'.a p * ψ (p : ZMod N) = g.a p ∧ χ' (p : ZMod (N * N)) * ψ (p : ZMod N) ^ 2 = χ (p : ZMod N) := by
  haveI : NeZero (N * N) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne N)⟩
  obtain ⟨h, hc, hn⟩ := clTwist N k χ ψ⁻¹ g.f g.char
  have h0 : h ≠ 0 := by
    rintro rfl
    have := hn 1
    rw [g.one, Nat.cast_one, map_one, mul_one] at this
    simp [coef, UpperHalfPlane.qExpansion_zero] at this
  obtain ⟨g', hg'⟩ := eigEx (N * N) k hk _ h hc h0 fun p => ψ⁻¹ (p : ZMod N) * g.a p
  refine ⟨_, g', fun p hp hd => ?_⟩
  have hu : IsUnit (p : ZMod (N * N)) :=
    (ZMod.isUnit_prime_iff_not_dvd hp).2 fun e => hd ((hp.dvd_mul.1 e).elim id id)
  have hu' : IsUnit (p : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hd
  have e : DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ⁻¹ ^ 2) (p : ZMod (N * N)) =
      χ (p : ZMod N) * ψ⁻¹ (p : ZMod N) ^ 2 := by
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ * ψ⁻¹ ^ 2) (dvd_mul_right N N) hu.unit
    rw [IsUnit.unit_spec, ZMod.cast_natCast (dvd_mul_right N N)] at this
    rw [this, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero]
  have e1 : ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hu']
  constructor
  · rw [hg' p hp fun n h1 => ?_]
    · linear_combination g.a p * e1
    have := g.eig p hp n h1
    rw [e, hn, hn n, Nat.cast_mul, map_mul, Eigenform.a]
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hp.pos] at this ⊢
      rw [hn, Nat.cast_mul, map_mul]
      linear_combination ψ⁻¹ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ⁻¹ (m : ZMod N)) * this
    · rw [if_neg hpn] at this ⊢
      linear_combination ψ⁻¹ (p : ZMod N) * ψ⁻¹ (n : ZMod N) * this
  · rw [e]
    linear_combination χ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) + 1) * e1
private theorem eig_unique {k N p : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) (k : ℤ)} (hf : f ≠ 0)
    {a b : ℂ} (ha : IsEigAt k χ f p a) (hb : IsEigAt k χ f p b) : a = b := by
  by_contra h
  exact hf ((finDim N k).2 f fun n hn =>
    (mul_eq_zero.1 (show (a - b) * coef f n = 0 by linear_combination hb n hn - ha n hn)).resolve_left (sub_ne_zero.2 h))
private theorem level_zero_eq_maximal_compact {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) :
    K1 w 0 = GlobalTheory.LFun.KGL w (n := 2) := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _
private theorem lie_one (φ : TR.Sm ℚ 2) (h : ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0) : TR.lie ℚ 2 (TR.oneL ℚ 2) φ = 0 := by
  classical
  have hX : TR.lie ℚ 2 (TR.oneL ℚ 2) = ∑ i, TR.lieS ℚ 2 i i 1 := by

    simp only [TR.lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.sum_single_one (m := Fin 2) (α := TR.Rinf ℚ)).symm
  have h1 : ∀ i, TR.lieS ℚ 2 i i 1 = TR.Eop Rat.infinitePlace i i := fun i => by
    rw [TR.Eop_eq]
    congr 1
    funext v
    rw [Subsingleton.elim v Rat.infinitePlace]
    simp
  rw [hX, Fin.sum_univ_two, h1, h1]
  exact h _
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem ev_not_dvd {a : ℕ} (h : a ≠ 0) : ∀ᶠ w : Pl ℚ in Filter.cofinite, ¬ normV w ∣ a := by
  have h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0 := by simpa using h
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  obtain ⟨c, rfl⟩ := not_not.1 hw
  refine Ideal.dvd_span_singleton.2 ?_
  rw [Nat.cast_mul, (places w).2.1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
theorem UpperTheory.V.Br.repEig_of_printsH_of_hermEx :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Af.Gk.HermEx → UpperTheory.V.Br.RepEig := by
  intro P hH k hk π hπ
  have hk1 : 1 ≤ k := by omega
  obtain ⟨H, hH⟩ := hH ℚ 2 one_le_two π fun φ hφ => lie_one φ fun v => by
    rw [(capTwo ℚ π v _ _ (hπ v) φ hφ).1, add_neg_cancel, zero_smul]
  obtain ⟨N, ψ, ν, hN, hν, φ, hφ, h0, hlow, hfix⟩ := levelVec k π (holVec k hk π hπ H hH)
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨ω, hω, -⟩ := _root_.UpperTheory.V.Sd.Wc.centChar_alt P.toClassicalTheorems ℚ (π.twist ν)
  have hc := fun z g => hω z φ hφ g
  obtain ⟨χ, hχ⟩ := charOf N hN ω φ h0 hlow.one hfix hc
  have hcusp := (π.twist ν).cusp φ hφ
  obtain ⟨f, hf, hL⟩ := deadel k N hN χ ω hχ φ hcusp hlow hfix hc
  have hf0 : f ≠ 0 := by
    rintro rfl
    refine h0 (Subtype.ext (funext fun g => ?_))
    obtain ⟨γ, h, u, hu, rfl⟩ := decomp N hN g
    rw [hL γ h u hu]
    simp [nsl]
  have hhol : IsHol k (lev N) ω φ := ⟨hcusp.1, fun w u hu => hfix _ (kLocal N hN w u hu), hc, hlow.wt, hlow.low⟩
  obtain ⟨g, hg⟩ := eigEx N k hk1 χ f hf hf0 fun p => Classical.epsilon (IsEigAt k χ f p)
  obtain ⟨χ', g', hg'⟩ := untwist k N hk1 χ ψ g
  refine ⟨N * N, inferInstance, χ', g', ?_⟩
  filter_upwards [Gk.satAE ℚ 2 π, ev_not_dvd (NeZero.ne N),
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.unr_ae_and_level ℚ ν).1] with w ⟨B, hB⟩ hw hu
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (TR.CuspSub.HasSat.card hB)
  refine ⟨α, β, hB, ?_⟩
  have hT := TR.CuspSub.HasSat.twist hB hu
  have hp := (places w).1
  have hv : GlobalTheory.LFun.IsSatVecGL w (locSm ℚ w) φ {α * ν.val w, β * ν.val w} :=
    (hT.2 ⟨φ, hφ⟩ (GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (hfix _ (kLocal N hN w u (by
      rwa [(places w).2.2.2 N hN hw, level_zero_eq_maximal_compact])))) fun e => h0 (congrArg Subtype.val e)).map
      (π.twist ν).V.subtype (fun _ _ => rfl) h0
  obtain ⟨h1, h2⟩ := eigOf k N hk1 hN χ ω hχ f φ hL hhol w _ _ hw hv
  have h3 := Classical.epsilon_spec (p := IsEigAt k χ f (normV w)) ⟨_, h1⟩
  have h4 := (hg _ hp h3).trans (eig_unique hf0 h3 h1)
  obtain ⟨h5, h6⟩ := hg' _ hp hw
  have h7 := (charVal N hN ψ ν hν).2 w hw
  have h8 : ψ (normV w : ZMod N) ≠ 0 := h7 ▸ Units.ne_zero _
  simp only [Units.val_mul, h7] at h2 h4 ⊢
  constructor
  · refine mul_right_cancel₀ h8 ?_
    rw [h5, h4]; ring
  · refine mul_right_cancel₀ (pow_ne_zero 2 h8) ?_
    rw [h6, ← h2]; ring
end
end

section




section
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.UnitaryBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem locProd_sum {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {ε : EpsFamily A} (L : LawsV a ha ε rc) :
    ∀ {c n : ℕ} {N : Fin c → ℕ} (hn : ∑ i, N i = n) (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
      (τ : SmIrr (GL (Fin n) (w.adicCompletion E))), Nonempty (τ.ρ.Equiv (locProd hn w σ)) →
      rc (cl τ) = sumList (List.ofFn fun i => rc (cl (σ i))) := by
  intro c
  induction c with
  | zero =>
    intro n N hn σ τ e
    obtain rfl : n = 0 := by simpa using hn.symm
    obtain ⟨e⟩ := e
    obtain ⟨φ⟩ := SupportRing.nonempty_equiv_unit (k := w.adicCompletion E) (stdBlocks N hn) fun i => (σ i).ρ
    have h1 := L.det 0 1 isSmoothChar_one
    simp only [List.range_zero, List.map_nil] at h1
    rw [List.ofFn_zero]
    refine (congrArg rc (IrrGL.of_eq_of.2 ⟨e.trans φ⟩)).trans h1
  | succ s ih =>
    intro n N hn σ τ e
    obtain rfl : n = N 0 + ∑ i : Fin s, N i.succ := hn.symm.trans (Fin.sum_univ_succ N)
    obtain ⟨e⟩ := e
    obtain ⟨E₁⟩ := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := w.adicCompletion E) N hn fun i => (σ i).ρ
    have hs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => N i.succ) rfl) fun i : Fin s => (σ i.succ).ρ) :=
      isSmooth_parInd _ _
    have hi := GlobalTheory.T.isIrreducible_second_factor_of_irreducible_product _ _ _ _ _ _ (σ 0).ρ _ τ.ρ (σ 0).smooth (σ 0).irred hs τ.irred ⟨e.trans E₁.symm⟩
    let σ' : SmIrr (GL (Fin (∑ i : Fin s, N i.succ)) (w.adicCompletion E)) := ⟨_, _, hs, hi⟩
    have h1 := L.prod (N 0) _ (ParLaws.toRep (σ 0)) (ParLaws.toRep σ') (ParLaws.toRep τ) ⟨e.trans E₁.symm⟩
    have h2 := ih (N := fun i : Fin s => N i.succ) rfl (fun i => σ i.succ) σ' ⟨.refl _⟩
    rw [List.ofFn_succ]
    exact h1.trans (congrArg _ h2)
theorem UpperTheory.V.Z.Win.Gu.prodT_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ExtraV → ProdT := by
  intro _ X E Ω _ _ _ _ _ n c N hn w σ _ τ e A h rc hrc
  obtain ⟨a, ha, ε, L⟩ := X E Ω A w h rc hrc
  exact locProd_sum L hn σ τ e
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Af.Gu
open UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Z.Win.Gu.assemble_s (H : _root_.UpperTheory.V.Af.HypothesesH') (hB : GlobalTheory.BcSpeh.BcSpeh) (hFam : SumFamG) (hHalf : HalfG) (hStr : Strings)
    (hUni : CompUnique) (hRec : RecTotT) (hFrob : FrobTotT) (hPol : PolOfFrob) (hLink : SatLink) (hConj : SatConj)
    (hIrr : IrrCaseT) (hPl : PlainGd) : GalUnitaryT := by
  intro E Ω _ _ _ _ _ _ hE l _ _ ι n hn π hπ
  obtain ⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩ := hB E hE n hn π hπ
  have hc : 1 ≤ c := by
    rcases c with _ | c
    · simp at hsum; omega
    · omega
  have hint : ∀ i (k : Fin (d i)) τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j := fun i k τ => by
    obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn π hπ τ
    exact (hStr n c d (m · τ) lam (hP.weight τ lam hl)).1 i k
  choose r₀ HT₀ h₀ hw₀ using fun i (k : Fin (d i)) =>
    hHalf E Ω l ι (a i) (hP.pos i).1 (P i) (hP.csd i) (ρ i) (hP.loc i) (m i) (hP.inf i) (ex n (d i) k) (hint i k)
  choose r₁ h₁ hi₁ using fun i => hFam E Ω l ι (d i) (hP.pos i).2 (fun _ => a i) (fun _ => (hP.pos i).1) (d i * a i) (by simp)
    (r₀ i) _ (HT₀ i) (h₀ i)
  obtain ⟨r, hr, hi⟩ := hFam E Ω l ι c hc (fun i => d i * a i) (fun i => Nat.mul_pos (hP.pos i).2 (hP.pos i).1) n hsum r₁ _ _ h₁
  have hpar : ∀ w, ParAtT ι r w (totPar n d (ρ · w)) := hr.par
  have hF : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ S : Fin c → Multiset ℂˣ,
      (∀ i, (CG.mk (P i)).HasSat w (S i)) → FrobEig ι r w (algSat n (normV w) (satTot w d S)) := fun w hw S hS =>
    hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S (fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS i)) (hpar w)
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ S : Fin c → Multiset ℂˣ, ∀ i, (CG.mk (P i)).HasSat w (S i) := by
    filter_upwards [ev_notMem (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w h1 h2
    exact ⟨h1, Classical.skolem.1 h2⟩
  have hsph : ∀ w, IsUnramU π w → ∀ i, ∃ B, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ B := fun w hu i =>
    (_root_.UpperTheory.V.Af.satake_local_of_printed_results H.toClassicalTheorems E (a i) w (ρ i w)).1 (by
      obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1
        (GlobalTheory.SphBC.isSpherical_of_isUnramU E hE n π hπ c a d hsum P ρ m σ hP hS hsplit w hu i (ρ i w) (hP.loc i w))
      exact ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩)
  refine ⟨r, fun τ => ∑ i, ∑ k, HT₀ i k τ, hr.cont, hr.ss, fun w hw hu A hA => ?_, fun τ lam hl => ?_, fun w hw τ hτ => ?_, ?_, fun hirr => ?_⟩
  · choose S hSat using hsph w hu
    exact (hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S hSat (hpar w) A hA).1
  · rw [← (hStr n c d (m · (ι.toRingHom.comp τ)) lam (hP.weight _ lam hl)).2]
    simp only [← hw₀]

    simp only [← Multiset.coe_mapAddMonoidHom, map_sum]
  · have e := hRec E Ω n c a d hsum P w (ρ · w) (σ · w) hP.pos (hP.loc · w) (hS · w) τ
      (hUni E n π hπ w hw _ _ _ _ hτ (hsplit w hw))
    refine ⟨fun A h rc hrc => e A h rc hrc ▸ hpar w A h rc hrc, fun hp => hr.ht w fun A h rc hrc => ?_⟩
    have g := hPl E Ω A w h rc hrc n τ hp
    rw [← e A h rc hrc] at g
    exact g
  · refine hPol E Ω l ι n r hr.cont hr.ss ?_
    filter_upwards [hev, (conjSrc_injective (IsCMField.complexConj E).toRingEquiv).tendsto_cofinite.eventually hev]
      with w ⟨hw, _⟩ ⟨hw', S, hS'⟩
    refine ⟨satTot (Bc.cPl w) d S, ?_, hF _ hw' S hS'⟩
    rw [← (hConj E w).2 c d S]
    exact hF w hw _ fun i => (hConj E w).1 _ (P i) (hP.csd i) _ (hS' i)
  · refine hIrr E Ω l ι n hn π hπ c a d hsum P ρ m σ hP (fun i w => (hS i w).2.2) hsplit
      (fun w hu i => (hsph w hu i).imp fun B hB => ((hLink E _ (P i)).1 w _ (hP.loc i w) B).2 hB) (hi hirr).1 (fun i => (hi₁ i ((hi hirr).2 i)).1) r hr.ss ?_
    filter_upwards [hev] with w ⟨hw, S, hS'⟩
    exact ⟨S, hS', hF w hw S hS'⟩
end
end
end

section




section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open Module TensorProduct GlobalTheory.Pst.DpstMap
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Split
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
  {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀]
  [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁]
  [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂]
  {ρ₀ : Representation ↥LL.1 ↥(GK K) V₀} {ρ₁ : Representation ↥LL.1 ↥(GK K) V₁}
  {ρ₂ : Representation ↥LL.1 ↥(GK K) V₂}
private theorem tensV_section (p : V₁ →ₗ[↥LL.1] V₂) (s : V₂ →ₗ[↥LL.1] V₁) (hps : ∀ v, p (s v) = v)
    (x : V₂ ⊗[ℚ_[l]] Bst P) : tensV P p (tensV P s x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [tensV, hps]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
variable [FiniteDimensional ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₂]
private theorem isPst_split {AI : LocAinf l P} (T : LocTied l P AI) {i : V₀ →ₗ[↥LL.1] V₁} {p : V₁ →ₗ[↥LL.1] V₂}
    {s : V₂ →ₗ[↥LL.1] V₁} (hi : ∀ g v, i (ρ₀ g v) = ρ₁ g (i v)) (hp : ∀ g v, p (ρ₁ g v) = ρ₂ g (p v))
    (hs : ∀ g v, s (ρ₂ g v) = ρ₁ g (s v)) (h1 : Function.Injective i) (h2 : Function.Exact i p)
    (hps : ∀ v, p (s v) = v) (hV₀ : IsPst P ρ₀) (hV₂ : IsPst P ρ₂) : IsPst P ρ₁ := by
  obtain ⟨hdom, hfrac, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V₀ := Module.Finite.trans ↥LL.1 V₀
  haveI : FiniteDimensional ℚ_[l] V₁ := Module.Finite.trans ↥LL.1 V₁
  haveI : FiniteDimensional ℚ_[l] V₂ := Module.Finite.trans ↥LL.1 V₂
  have b₁ := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation P hdom hfrac ρ₁
  haveI f₁ : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁) :=
    Module.rank_lt_aleph0_iff.mp (b₁.trans_lt (Cardinal.natCast_lt_aleph0))
  obtain ⟨f₀, c₀⟩ := (isPst_iff P ρ₀).1 hV₀
  obtain ⟨f₂, c₂⟩ := (isPst_iff P ρ₂).1 hV₂
  obtain ⟨hinj, hex⟩ := UpperTheory.V.Loc.PstExact.dmap_exact P hi hp h1 h2
  have inj : Function.Injective (UpperTheory.V.Loc.PstExact.dUr P hi) := fun x y h => hinj h
  have sur : Function.Surjective (UpperTheory.V.Loc.PstExact.dUr P hp) := fun y =>
    ⟨toUr P ρ₁ (dmap P hs ((toUr P ρ₂).symm y)), Subtype.ext (tensV_section P p s hps _)⟩
  have ex : Function.Exact (UpperTheory.V.Loc.PstExact.dUr P hi) (UpperTheory.V.Loc.PstExact.dUr P hp) := fun y => hex y
  have e := (UpperTheory.V.Loc.PstExact.dUr P hp).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 sur, finrank_top, LinearMap.exact_iff.mp ex, LinearMap.finrank_range_of_inj inj] at e
  have e' := (p.restrictScalars ℚ_[l]).finrank_range_add_finrank_ker
  have exq : Function.Exact (i.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := h2
  rw [LinearMap.exact_iff.mp exq, LinearMap.finrank_range_of_inj (f := i.restrictScalars ℚ_[l]) h1,
    LinearMap.range_eq_top.2 (show Function.Surjective (p.restrictScalars ℚ_[l]) from fun v => ⟨s v, hps v⟩),
    finrank_top] at e'
  exact (isPst_iff P ρ₁).2 ⟨f₁, by omega⟩
end Split
section Sum
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a b : ℕ}
private theorem isPst_sum (T : LocTied l P AI) {L : FinExt l} (s : ↥Gw →* GL (Fin a) ↥L.1) (s' : ↥Gw →* GL (Fin b) ↥L.1)
    (h : IsPst P (Bw.repE L s)) (h' : IsPst P (Bw.repE L s')) : IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) := by
  let e : (Fin (a + b) → ↥L.1) ≃ₗ[↥L.1] (Fin a → ↥L.1) × (Fin b → ↥L.1) :=
    (LinearEquiv.funCongrLeft ↥L.1 ↥L.1 finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ ↥L.1 ↥L.1)
  have he : ∀ g v, e (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s') g v) =
      (Bw.repE L s g (e v).1, Bw.repE L s' g (e v).2) := by
    intro g v
    rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, GlobalTheory.BCGal.sumRep_val]
    ext i <;>
      simp [e, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl
  have he' : ∀ g x, e.symm (Bw.repE L s g x.1, Bw.repE L s' g x.2) =
      Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s') g (e.symm x) := by
    intro g x
    apply e.injective
    rw [he, e.apply_symm_apply, e.apply_symm_apply]
  refine isPst_split P T (i := e.symm.toLinearMap ∘ₗ LinearMap.inl ↥L.1 _ _)
    (p := LinearMap.snd ↥L.1 _ _ ∘ₗ e.toLinearMap) (s := e.symm.toLinearMap ∘ₗ LinearMap.inr ↥L.1 _ _)
    (ρ₀ := Bw.repE L s) (ρ₂ := Bw.repE L s') (fun g v => ?_) (fun g v => ?_) (fun g v => ?_) ?_ ?_ ?_ h h'
  · have := he' g (v, 0)
    simpa using this
  · simp [he]
  · have := he' g (0, v)
    simpa using this
  · intro x y hxy
    simpa using hxy
  · intro y
    constructor
    · intro hy
      refine ⟨(e y).1, ?_⟩
      apply e.injective
      have hy' : (e y).2 = 0 := hy
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply, e.apply_symm_apply]
      exact Prod.ext rfl hy'.symm
    · rintro ⟨x, rfl⟩
      simp
  · intro v
    simp
private theorem isPstAt_sum (T : LocTied l P AI) {r : ↥Gw →* GL (Fin a) (Om l)} {r' : ↥Gw →* GL (Fin b) (Om l)}
    (h : IsPstAt P Bw r) (h' : IsPstAt P Bw r') : IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
  obtain ⟨L₁, r₁, m₁, p₁⟩ := h
  obtain ⟨L₂, r₂, m₂, p₂⟩ := h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  exact ⟨supExt L₁ L₂, _, ⟨n₁.1, by rw [GlobalTheory.Pst.SumParam.mapRep_sumRep, n₁.2, n₂.2]⟩,
    isPst_sum Bw T _ _ (GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge P Bw l₁ r₁ p₁) (GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge P Bw l₂ r₂ p₂)⟩
end Sum
theorem UpperTheory.V.Z.Win.Gu.sumTwoG_of_printsH_gdLaws_sumAway_sumHTAt :
    _root_.UpperTheory.V.Af.HypothesesH' → GdLaws → SumAway → SumHTAt → SumTwoG := by
  intro _ hG hA hT E Ω _ _ _ _ _ l _ ι a b r r' p p' HT HT' C C'
  obtain ⟨T⟩ := Loc.tiedP l
  have hv := GlobalTheory.BCGal.cont_sumRep r r' (Units.continuous_val.comp C.cont) (Units.continuous_val.comp C'.cont)
  have hc : Continuous (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    simp only [← map_inv]
    exact hv.comp continuous_inv
  refine ⟨hc, GlobalTheory.BCGal.ss_sumRep r r' C.ss C'.ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩
  · exact hT E Ω l a b r r' C.cont C'.cont HT HT' w
      (C.ht w fun A h rc hrc => (((hG E Ω A w h).1 _ _).1 (hg A h rc hrc)).1)
      (C'.ht w fun A h rc hrc => (((hG E Ω A w h).1 _ _).1 (hg A h rc hrc)).2)
  · obtain ⟨a1, b1⟩ := C.par w A h rc hrc
    obtain ⟨a2, b2⟩ := C'.par w A h rc hrc
    have sp := ((hG E Ω A w h).1 (p w A h rc) (p' w A h rc)).1
    refine And.intro (fun hw => ?_) (fun O _ _ _ Bw hj hg => ?_)
    · obtain ⟨x, hx, kx⟩ := a1 hw
      obtain ⟨x', hx', kx'⟩ := a2 hw
      refine Exists.intro (x.lpSum x') (And.intro (hA E Ω l ι a b r r' C.cont C'.cont w hw A h _ _ hx hx') fun g => ?_)
      rw [kx (sp g).1, kx' (sp g).2]
    · obtain ⟨p1, e1⟩ := b1 O Bw hj (sp hg).1
      obtain ⟨p2, e2⟩ := b2 O Bw hj (sp hg).2
      have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype =
          Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) (r'.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
        ext g i j
        rfl
      have p3 := isPstAt_sum Bw T p1 p2
      rw [e]
      exact ⟨p3, by rw [GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l _ _ ⟨T⟩ ι E Ω A w O Bw h hj a b _ _ p1 p2 p3, e1, e2]⟩
end
end
