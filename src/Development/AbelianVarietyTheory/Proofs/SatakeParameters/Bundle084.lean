module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle078
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.LocalRingCardinality.Params
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL), K.1 ≤ MaximalUnramifiedExtension l → ∀ a, ∃! τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Over W τ a := by
  first | exact @GlobalTheory.HTW.Rec.existsUnique_over | exact GlobalTheory.HTW.Rec.existsUnique_over | (intros; apply GlobalTheory.HTW.Rec.existsUnique_over <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.eleven_le_inertOddPrimeImagQuadratic_large_scale : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (l : ℕ), L.sc.ez = eps → x0 ≤ L.sc.x → l.Prime → InertUnr D l → 11 ≤ l := by
  first | exact @GlobalTheory.InertPrimeEleven.eleven_le | exact GlobalTheory.InertPrimeEleven.eleven_le | (intros; apply GlobalTheory.InertPrimeEleven.eleven_le <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL) {r : ℕ} (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1), IsMatRep T M → (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) T.ρ) ∧ ∀ τ u, multV (P.PD K) T.ρ τ u = multV (P.PD K) (matRep M) τ u := by
  first | exact @GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | exact GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | (intros; apply GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.maxSizeAtNonThickPlace_le_windowEnds : ∀ {D : D7} (L : SizeData₂ D), (wMax D : ℝ) ≤ wB L ∧ (wHat D : ℝ) ≤ wP L := by
  first | exact @GlobalTheory.HTW.Rec.wMax_le_wB | exact GlobalTheory.HTW.Rec.wMax_le_wB | (intros; apply GlobalTheory.HTW.Rec.wMax_le_wB <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.clusterDepthAtPrime_eq_leastPowerDepth : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → jA L l = depth L l := by
  first | exact @GlobalTheory.HTW.Rec.jA_eq_depth | exact GlobalTheory.HTW.Rec.jA_eq_depth | (intros; apply GlobalTheory.HTW.Rec.jA_eq_depth <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.coefficientFieldEnlargement_locChi_cyclotomic : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw), (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → ∀ s, C.inc ((Br.locChi D.nbr i w hw (epsU D.nd i) s : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 s : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
  first | exact @GlobalTheory.HTW.Rec.enl_locChi_epsU | exact GlobalTheory.HTW.Rec.enl_locChi_epsU | (intros; apply GlobalTheory.HTW.Rec.enl_locChi_epsU <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDuals_eq_tateDuals_at_enlargement : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), (∀ s, C.inc ((Br.locChi D.nbr i w hw (epsU D.nd i) s : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 s : (↥C.LL.1)ˣ) : ↥C.LL.1)) → (∀ x, C.loc (rDuO D.nd i r x) = twistM (dualM (C.loc (rTwO D.nd i r x))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1)) ∧ C.loc (T2O D.nd i ρ π) = twistM (dualM (C.loc (WpO D.nd i ρ π))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) := by
  first | exact @GlobalTheory.HTW.Rec.twistedDuals_eq_tateDuals | exact GlobalTheory.HTW.Rec.twistedDuals_eq_tateDuals | (intros; apply GlobalTheory.HTW.Rec.twistedDuals_eq_tateDuals <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem exists_primitiveRoot_of_good {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (hG : Good K 1 LL) :
    ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l : Om l) := ⟨Nat.cast_ne_zero.2 hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hmem : ζ ∈ Ks K 1 := by
    refine (le_sup_right : _ ≤ Ks K 1) (IntermediateField.subset_adjoin _ _ ?_)
    simpa using hζ.pow_eq_one
  have hLL : ζ ∈ LL.1 := hG.2.2.2 (Ks K 1).val ⟨ζ, hmem⟩
  refine ⟨⟨ζ, hLL⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) hζ LL.1.val.toRingHom.injective

theorem setCS_of_wordsAT {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l}
    (hG : Good K 1 LL) (Wc : Wach P K LL) (hs : Wc.s = 1) (hK : K.1 ≤ MaximalUnramifiedExtension l) (h11 : 11 ≤ l)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] (Wd : NWord (Module.finrank ℚ_[l] ↥(K0 K))) (d : ℕ)
    (hA : WordsAT l Wd d) (T₁ T₂ : Lat K LL) (F : LatHom T₁.L T₂.L) (hF : F.Onto)
    (c₁ : IsCrys (P.PD K) T₁.ρ) (c₂ : IsCrys (P.PD K) T₂.ρ)
    (hj : ∀ a, TruncatedSeriesCountingBounds.JumpsAt Wc T₁ a (Wd.win a))
    (hlow : ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), TruncatedSeriesCountingBounds.lowCount Wc T₂ a Wd.η ≤ (Wd.m : ℤ)) :
    RamifiedCoefficientChains.SetCS Wc d T₁ T₂ F Wd.sz Wd.S Wd.η Wd.m := by
  classical
  obtain ⟨hev, hup, -, -, hbig⟩ := hA
  have hp : (P.PD K).p = l := P.PD_p K
  have hle : K.1 ≤ K0 K := le_inf le_rfl hK
  obtain ⟨a₀, -, hsup⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (ZMod (Module.finrank ℚ_[l] ↥(K0 K))))
    Finset.univ_nonempty Wd.sz
  have hgr : IsGreatest (Set.range Wd.sz) (Finset.univ.sup Wd.sz) := by
    refine ⟨⟨a₀, hsup.symm⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact Finset.le_sup (Finset.mem_univ a)
  have hbig' := hbig _ hgr
  refine ⟨⟨?_, hs, by omega⟩, by omega, hev, ?_, by rw [hp]; exact exists_primitiveRoot_of_good hG, ⟨c₁, c₂, hF⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, hle x.2⟩, Subtype.ext rfl⟩⟩
  · exact (goodO_finExt_integers l LL).1
  · intro a τ hτ u hu
    have hw := hj a τ hτ u hu
    have hua := hup a
    unfold NWord.win at hw
    unfold RamifiedCoefficientChains.JumpWinS
    by_cases hpar : (a.val + d) % 2 = 1
    · have h0 : ¬ (a.val + d) % 2 = 0 := by omega
      have hu1 : Wd.up a = true := by simpa [hpar] using hua
      simp only [hu1, if_true, Set.mem_setOf_eq, abs_le] at hw
      simp only [h0, if_false, Set.mem_union, Set.mem_Icc]
      push_cast
      omega
    · have h0 : (a.val + d) % 2 = 0 := by omega
      have hu1 : Wd.up a = false := by simpa [hpar] using hua
      simp only [hu1, Bool.false_eq_true, if_false, Set.mem_setOf_eq, abs_le] at hw
      simp only [h0, if_true, Set.mem_union, Set.mem_Icc]
      push_cast
      omega
  · intro a τ hτ
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    letI ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    have h := hlow ft a
    unfold TruncatedSeriesCountingBounds.lowCount at h
    have hfil : (Finset.univ.filter (fun τ' => Formalism.MainNotions.LiftingTheory.Over Wc τ' a)) = {τ} := by
      ext τ'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h' => (existsUnique_over P K LL Wc hK a).unique h' hτ, fun h' => h' ▸ hτ⟩
    rw [hfil, Finset.sum_singleton] at h
    exact h
  · intro a
    have h := (hbig' a).2
    rw [hp]
    unfold RamifiedCoefficientChains.aR RamifiedCoefficientChains.lam RamifiedCoefficientChains.hpar
    push_cast
    exact h
  · intro a
    have h := (hbig' a).1
    unfold RamifiedCoefficientChains.hpar
    push_cast
    exact h

theorem settingC_of_wordsAT : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)) (d : ℕ), 11 ≤ D.nd.l i → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → WordsAT (D.nd.l i) Wd d → RecS.AlternatingWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd d := by
  intro D L HW i r ρ π w hw Cx hG Wd d h11 hB hA nz T₁ T₂ F h₁ h₂ hF
  have hT1 := hB.t1 T₁ h₁
  have hT2 := hB.t2 T₂ h₂
  exact setCS_of_wordsAT hG (WW HW i w hw Cx hG) ((HW (D.nd.l i)).W_s _ 1 _ hG) hB.unram h11 Wd d hA
    T₁ T₂ F hF hT1.1 hT2.1 hT1.2.1 hT2.2

end GlobalTheory.HTW.RecS
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.ValCmp.Invol

theorem aeval_scale {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {r n : ℕ} (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (colW r n) f ν) (c : S)
    (x : Fin r × Fin n → S) :
    aeval (fun v => c * x v) f = c ^ (∑ i, ν i) * aeval x f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (colW r n) d = ν := hf (mem_support_iff.mp hd)
  have hs : ∑ i, ν i = ∑ v, d v := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finset.sum_apply, colW, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.mul_sum]
    simp [Pi.single_apply]
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), hs]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

def cofM (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MP R n) :=
  (genM R n).adjugate.transpose.submatrix id Fin.revPerm

theorem map_genM (R : Type) [CommRing R] (n : ℕ) :
    (cofAct R n).mapMatrix (genM R n) = cofM R n := by
  ext1 a s
  simp [cofAct, genM, cofM]

theorem det_cofM (R : Type) [CommRing R] (m : ℕ) :
    (cofM R (m + 1)).det = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : MP R (m + 1)) *
      (genM R (m + 1)).det ^ m := by
  rw [cofM, Matrix.det_permute', Matrix.det_transpose, Matrix.det_adjugate]
  simp

theorem cofAct_det (R : Type) [CommRing R] (n : ℕ) :
    cofAct R n (genM R n).det = (cofM R n).det := by
  rw [AlgHom.map_det, map_genM]

theorem det_mul_cofAct_cofAct_X (R : Type) [CommRing R] (n : ℕ) (v : Fin n × Fin n) :
    (genM R n).det * cofAct R n (cofAct R n (X v)) = (cofM R n).det * X v := by
  have h1 : cofM R n * (genM R n).transpose.submatrix Fin.revPerm id = (genM R n).det • (1 : Matrix _ _ _) := by
    rw [cofM, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Matrix.mul_adjugate]
    simp
  have h2 : (cofM R n).det • (genM R n).transpose.submatrix Fin.revPerm id =
      (genM R n).det • (cofM R n).adjugate := by
    have := congrArg (fun M => (cofM R n).adjugate * M) h1
    simpa [← Matrix.mul_assoc, Matrix.adjugate_mul] using this
  have h3 : cofAct R n (cofAct R n (X v)) = (cofM R n).adjugate v.2.rev v.1 := by
    rw [← map_genM, ← AlgHom.map_adjugate]
    simp [cofAct]
  have h4 := congrFun (congrFun h2 v.2.rev) v.1
  rw [h3]
  simpa [genM] using h4.symm

theorem cofAct_cofAct (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ) (f : MP R n)
    (hf : IsWeightedHomogeneous (colW n n) f ν) :
    (genM R n).det ^ (∑ i, ν i) * cofAct R n (cofAct R n f) = (cofM R n).det ^ (∑ i, ν i) * f := by
  have h1 : cofAct R n (cofAct R n f) = aeval (fun v => cofAct R n (cofAct R n (X v))) f := by
    have : (cofAct R n).comp (cofAct R n) = aeval (fun v => cofAct R n (cofAct R n (X v))) := by
      ext1 v; simp
    exact DFunLike.congr_fun this f
  rw [h1, ← aeval_scale ν f hf]
  simp only [det_mul_cofAct_cofAct_X]
  rw [aeval_scale ν f hf, aeval_X_left_apply]

theorem cofRel_invol (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (h0 : ν (Fin.last m) = 0) :
    ∃ ε : ℤˣ, ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∀ g : MP R (m + 1),
      CofRel R m ν f g → CofRel R m (nuDual ν) g ((ε : ℤ) • f) := by
  refine ⟨Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) ^ ν 0, fun f hf g hg => ?_⟩
  have hD : (genM R (m + 1)).det ≠ 0 := Matrix.det_mvPolynomialX_ne_zero (Fin (m + 1)) R
  have hδ : ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : MP R (m + 1)) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) with h | h <;> simp [h]
  have hC : (cofM R (m + 1)).det ≠ 0 := by
    rw [det_cofM]; exact mul_ne_zero hδ (pow_ne_zero _ hD)
  have hle : ν 0 ≤ ∑ i, ν i := Finset.single_le_sum (fun i _ => Nat.zero_le (ν i)) (Finset.mem_univ _)
  have hd0 : nuDual ν 0 = ν 0 := by simp [nuDual, h0]
  have hle' : nuDual ν 0 ≤ ∑ i, nuDual ν i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (nuDual ν i)) (Finset.mem_univ _)
  have hsum : ∑ i, nuDual ν i + ∑ i, ν i = (m + 1) * ν 0 := by
    rw [← Equiv.sum_comp Fin.revPerm ν, ← Finset.sum_add_distrib]
    have : ∀ i : Fin (m + 1), nuDual ν i + ν (Fin.revPerm i) = ν 0 :=
      fun i => Nat.sub_add_cancel (hν (Fin.zero_le i.rev))
    simp only [this]
    simp
  have hexp : ∑ i, ν i + (∑ i, nuDual ν i - nuDual ν 0) = m * ν 0 := by
    rw [add_mul] at hsum; omega
  have h1 := cofAct_cofAct R (m + 1) ν f hf.1
  unfold CofRel at hg ⊢
  rw [← hg, map_mul, map_pow, cofAct_det] at h1
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  have he' : ∑ i, ν i - ν 0 = e := by omega
  rw [he'] at h1
  have h2 : (genM R (m + 1)).det ^ (∑ i, ν i) * cofAct R (m + 1) g = (cofM R (m + 1)).det ^ ν 0 * f := by
    apply mul_left_cancel₀ (pow_ne_zero e hC)
    rw [mul_left_comm, h1, he]
    ring
  apply mul_left_cancel₀ (pow_ne_zero (∑ i, ν i) hD)
  rw [h2, ← mul_assoc, ← pow_add, hexp, det_cofM, mul_pow, pow_mul]
  simp only [Units.val_pow_eq_pow_val, zsmul_eq_mul, Int.cast_pow]
  ring

end GlobalTheory.ValCmp.Invol
end
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.ValCmp.Eqv

theorem degree_of_colWeight {n : ℕ} {ν : Fin n → ℕ} (m : Fin n × Fin n →₀ ℕ)
    (h : Finsupp.weight (colW n n) m = ν) : (m.sum fun _ k => k) = ∑ j, ν j := by
  classical
  rw [← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [colW, Pi.single_apply]

theorem rowAct_smul_matrix {n : ℕ} {R : Type} [CommRing R] {ν : Fin n → ℕ} (c : R) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : IsWeightedHomogeneous (colW n n) f ν) :
    rowAct R (c • g) f = c ^ (∑ j, ν j) • rowAct R g f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← degree_of_colWeight m (hf (mem_support_iff.mp hm))]
  have h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) =
      C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2) := by
    intro v
    simp only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]
  simp only [rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]
  ring

theorem rowAct_genM {n : ℕ} {R : Type} [CommRing R] (g : Matrix (Fin n) (Fin n) R) :
    (rowAct R (n := n) g).mapMatrix (genM R n) = (C : R →+* MP R n).mapMatrix g * genM R n := by
  ext a s : 2
  simp [rowAct, genM, Matrix.mul_apply]

theorem rowAct_det_genM {n : ℕ} {R : Type} [CommRing R] (g : Matrix (Fin n) (Fin n) R) :
    rowAct R (n := n) g (genM R n).det = C g.det * (genM R n).det := by
  rw [AlgHom.map_det, rowAct_genM, Matrix.det_mul, RingHom.map_det]

theorem rowAct_transpose_cofAct {n : ℕ} {R : Type} [CommRing R] (g : Matrix (Fin n) (Fin n) R) (f : MP R n) :
    rowAct R g.transpose (cofAct R n f) = cofAct R n (rowAct R g.adjugate f) := by
  have h : (rowAct R (n := n) g.transpose).comp (cofAct R n) = (cofAct R n).comp (rowAct R g.adjugate) := by
    apply MvPolynomial.algHom_ext
    intro v
    have h1 : (rowAct R (n := n) g.transpose).mapMatrix (genM R n).adjugate =
        (genM R n).adjugate * (C : R →+* MP R n).mapMatrix g.transpose.adjugate := by
      rw [AlgHom.map_adjugate, rowAct_genM, Matrix.adjugate_mul_distrib, RingHom.map_adjugate]
    have h2 := congrFun (congrFun h1 v.2.rev) v.1
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply] at h2

    rw [AlgHom.comp_apply, AlgHom.comp_apply, cofAct, aeval_X, h2, rowAct, aeval_X, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, aeval_X, aeval_C, ← Matrix.adjugate_transpose, mul_comm]
    rfl
  exact DFunLike.congr_fun h f

theorem cofRel_rowAct : ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit h.det → ∀ f ∈ dualWeyl K (m + 1) (m + 1) ν, ∀ g : MP K (m + 1), CofRel K m ν f g → CofRel K m ν (rowAct K h⁻¹ f) (h.det ^ (-(ν 0 : ℤ)) • rowAct K h.transpose g) := by
  intro K _ m ν h hh f hf g hfg
  have hd : h.det ≠ 0 := hh.ne_zero
  have hadj : h.adjugate = h.det • h⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hd, one_smul]
  have hle : ν 0 ≤ ∑ i, ν i := Finset.single_le_sum (f := ν) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  unfold CofRel at hfg ⊢
  have h1 := congrArg (rowAct K h.transpose) hfg
  rw [rowAct_transpose_cofAct, hadj, rowAct_smul_matrix _ _ _ hf.1, map_smul, map_mul, map_pow, rowAct_det_genM,
    Matrix.det_transpose, mul_pow, ← C_pow, mul_assoc, ← smul_eq_C_mul] at h1
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  rw [he, Nat.add_sub_cancel_left] at h1 ⊢
  rw [pow_add, mul_comm (h.det ^ ν 0), mul_smul] at h1
  have h2 : _ = _ := smul_right_injective _ (pow_ne_zero e hd) h1
  rw [mul_smul_comm, h2, smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hd), one_smul]

end GlobalTheory.ValCmp.Eqv
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

namespace GlobalTheory.Pst.DmapNonzero

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem tensV_eq_rTensor {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] LL V'] (f : V →ₗ[LL] V') (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f x = (f.restrictScalars ℚ_[l]).rTensor (Bst P) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.Pst.DmapNonzero

end
end

section

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType

namespace GlobalTheory.CuspRep.AlgExpo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem dchi_atEmb (χ : HChar E) (τ : E →+* ℂ) (z : ℂ) :
    dchi χ (atEmb τ z) = expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [atEmb_eq, map_add (f := _), map_smul, map_smul]
  simp only [expo, atEmb_conj, map_one, Complex.conj_I, e, map_neg, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im z]
  simp only [map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (z.im * dchi χ (atEmb τ Complex.I)) * Complex.I_mul_I

theorem dchi_eq_sum (χ : HChar E) (x : Cinf E) : dchi χ x = ∑ φ : E →+* ℂ, expo χ φ * coord φ x := by
  classical
  have hx : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb
    rw [InfinitePlace.mk_embedding, if_pos rfl]

  rw [hx, map_sum]

  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dchi_atEmb]
  simp only [coord_atEmb', mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

theorem chiInf_eq_prod (χ : HChar E) (n : (E →+* ℂ) → ℤ) (hn : ∀ τ, expo χ τ = n τ) (u : (Cinf E)ˣ) :
    ((chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, coord φ (u : Cinf E) ^ n φ := by
  rw [← expU_log u, chiInf_expU, dchi_eq_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [coord_expU, hn, ← Complex.exp_int_mul]

theorem isAlgPos_of_expo : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E)
    (n : (E →+* ℂ) → ℤ), (∀ τ, expo χ τ = n τ) → IsAlgPos χ n := by
  intro E _ _ _ χ n hn k _
  have e := chiInf_eq_prod χ n hn (Units.map (diagInf E).toMonoidHom k)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eq]
  refine e.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (coord_algebraMap φ (k : E))

end GlobalTheory.CuspRep.AlgExpo
end
end
