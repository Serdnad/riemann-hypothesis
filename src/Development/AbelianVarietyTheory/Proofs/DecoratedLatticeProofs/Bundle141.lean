module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle125
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.HalfPairing
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D} {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem toMatrix_mem_latRat (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :
    LinearMap.toMatrix' x ∈ latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) := by
  have hA : D.host.AA = D.host.AA0 := by
    rw [Formalism.BasicNotions.Host.AA, Formalism.BasicNotions.Host.ccE, hc, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S N hN
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    have e : LinearMap.toMatrix' (r • x) = ∑ k, genMap S T r (s' k) (x (s k)) := by
      refine Matrix.ext fun i j => ?_
      have h1 : (Pi.single j 1 : Fin S.rank → D.host.E) = ∑ k, (∑ l, star (s' k l) * S.gram l j) • s k := by
        funext a
        rw [Finset.sum_apply, Pi.single_apply, ← hss a j]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [Matrix.sum_apply, LinearMap.toMatrix'_apply]
      change r * x (Pi.single j 1) i = _

      rw [h1, map_sum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Pi.smul_apply, smul_eq_mul, genMap, Matrix.of_apply]
      ring
    rw [e]
    exact sum_mem fun k _ => AddSubgroup.subset_closure ⟨r, hA ▸ hr, _, (hs k).2, _, hx _ (hs k).1, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : LinearMap.toMatrix' (c • x) = (c : D.host.E) • LinearMap.toMatrix' x := by
      ext i j; rfl
    rw [e]
    exact smul_mem_latRat c hx

theorem smul_mem_locP {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {SS : Finset (HeightOneSpectrum (𝓞 E))}
    {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c) {y : Formalism.L2.Col.HomE E a b} (hy : y ∈ halfBO SS M c)
    (Q : HeightOneSpectrum (𝓞 E)) : (c : E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ expS SS Q)⁻¹ • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hy Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ expS SS Q)⁻¹ → (c : E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 2 (by field_simp)
  · exact key 0 (by simp)
  · exact key 1 (by simp)

theorem conj_comp_mem (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (h0 : infPart D e = 0) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) :
    ((LinearMap.toMatrix' x).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : Formalism.L2.Col.cO D.host.E s ∉ P.asIdeal := hs
  have hne : Formalism.L2.Col.cO D.host.E s ≠ 0 := fun h => hs' (h ▸ zero_mem _)
  have hs0 : (s : D.host.E) ≠ 0 := fun h => hne (by rw [show s = 0 from RingOfIntegers.ext h, map_zero])
  have h1 : finPart D (e * incA D ((Formalism.L2.Col.cO D.host.E s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hs' ((he.2 _ hne).2 h)
  have h2 := GlobalTheory.PlaceVec.cF_mem_int (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1)
  rw [← GlobalTheory.AdelicLatMove.toEAf_cA, RingHom.map_mul (cA D)] at h2
  have h3 : cA D (incA D ((Formalism.L2.Col.cO D.host.E s : D.host.E)⁻¹)) = incA D (s : D.host.E)⁻¹ := by
    change incA D (star (star (s : D.host.E))⁻¹) = _
    rw [star_inv₀, star_star]
  rw [h3] at h2
  have h4 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (GlobalTheory.PlaceVec.finPart_mem_intAE h2) _
    (finTens_mem_latO (one_mem_intAf _) (toMatrix_mem_latRat hc hN hsx))
  convert h4 using 1
  ext i j
  have h5 := GlobalTheory.PlaceVec.infPart_cA h0
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h5, zero_mul]) ?_
  have h6 : finPart D (finTens 1 (LinearMap.toMatrix' (s • x)) i j) =
      finPart D (incA D ((s : D.host.E) * LinearMap.toMatrix' x i j)) := rfl
  rw [RingHom.map_mul (finPart D) (_ * _), h6, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D),
    inv_mul_cancel_left₀ hs0]

theorem char_sympl_halfB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ u ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), ψ (symplO S T (c • u) (((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r)) = 1 := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc _ _ _ ⟨ΛS, dS, eS⟩ ⟨ΛT, dT, eT⟩ y hy u hu
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  rw [← eS, ← eT] at hu
  change ψ (symplO S T (c • u) ((LinearMap.toMatrix' y).map fun r => cA D e * incA D r)) = 1
  have hmem : c • ((LinearMap.toMatrix' y).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
    have e1 : c • ((LinearMap.toMatrix' y).map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' ((c : D.host.E) • y)).map fun r => cA D (es PP) * incA D r : WO S T) := by
      ext i j

      rw [Matrix.smul_apply, Matrix.map_apply, Matrix.sum_apply, map_sum, nsmul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun PP _ => ?_
      change _ = cA D (es PP) * incA D ((c : D.host.E) * LinearMap.toMatrix' y i j)
      rw [RingHom.map_mul (incA D), map_natCast, mul_left_comm]
    rw [e1]
    refine sum_mem fun PP hPP => conj_comp_mem hP.cc dS (hes PP hPP) ?_ (smul_mem_locP hc hy _)
    refine GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => ?_, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
    rw [Finset.mem_singleton.1 hQ]
    exact hes PP hPP
  have h := char_sympl_eq_one hP.std dS dT hu hmem
  rw [← symplHom_apply, map_nsmul] at h
  rw [← symplHom_apply, map_nsmul]
  exact h

end GlobalTheory.AdForm.HalfPairing
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.TranslatedRow

variable {D : D7}

def Good (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (F : GA D (D.sp.Y 0) → ℂ) : Prop :=
  Continuous F ∧ (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) ∧ (∀ γ ∈ GQ (D.sp.Y 0), ∀ g, F (γ * g) = F g) ∧
    (∀ k ∈ J, ∀ g, F (g * k) = χ k * F g)

theorem good_add {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {F G : GA D (D.sp.Y 0) → ℂ}
    (hF : Good J χ F) (hG : Good J χ G) : Good J χ (F + G) := by
  obtain ⟨c1, ⟨C1, b1⟩, l1, r1⟩ := hF
  obtain ⟨c2, ⟨C2, b2⟩, l2, r2⟩ := hG
  refine ⟨c1.add c2, ⟨C1 + C2, fun g => (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g))⟩,
    fun γ hγ g => by simp [l1 γ hγ g, l2 γ hγ g], fun k hk g => by simp [r1 k hk g, r2 k hk g, mul_add]⟩

theorem good_smul {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {F : GA D (D.sp.Y 0) → ℂ} (c : ℂ)
    (hF : Good J χ F) : Good J χ (c • F) := by
  obtain ⟨c1, ⟨C1, b1⟩, l1, r1⟩ := hF
  refine ⟨continuous_const.mul c1, ⟨‖c‖ * C1, fun g => ?_⟩, fun γ hγ g => by simp [l1 γ hγ g],
    fun k hk g => by simp [r1 k hk g]; ring⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (b1 g) (norm_nonneg _)

theorem good_of_mem (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {S : D.what₂.Tau → SPar}
    {M : DSModel (D.sp.Y 0) S} {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ}
    {T : SmT M →ₗ[ℂ] (GA D (D.sp.Y 0) → ℂ)} (hT : T ∈ MultT θ M J χ) (x : SmT M) : Good J χ (T x) := by
  have h1 := (GlobalTheory.MultMem.mem_mult_iff D θ _ S M J χ _).1 ((mem_multT θ M J χ T).1 hT)
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul]
    refine good_smul c ?_
    have e : T (PiTensorProduct.tprod ℂ v) = (PiTensorProduct.lift.symm T) v := by
      rw [PiTensorProduct.lift_symm]; rfl
    rw [e]
    exact ⟨(h1.aut v).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (h1.aut v) (h1.cusp v), (h1.aut v).left,
      fun k hk g => h1.lev v k hk g⟩
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact good_add ha hb

end GlobalTheory.Core.Mi.TranslatedRow

namespace GlobalTheory.Core.Mi.TranslatedRow

variable {D : D7}

theorem castGA_symm_mem' {I I' : Formalism.MainNotions.S.AutInst} (p : I = I') (γ : I'.GA) (hγ : γ ∈ I'.GFset) :
    (castGA p).symm γ ∈ I.GFset := by
  subst p
  exact hγ

theorem rat_of_GF (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (γ : X.B.I.GA) (hγ : γ ∈ X.B.I.GFset) : (iotaX X h).symm γ ∈ GQ (D.sp.Y 0) := by
  refine (Formalism.IndefR.RationalEmbedding.iota_rat D ((iotaX X h).symm γ)).2 ?_
  show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact castGA_symm_mem' _ γ hγ

theorem rowFun_of_good (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {t : GA D (D.sp.Y 0)} (hm : Matches X h J χ t)
    {F : GA D (D.sp.Y 0) → ℂ} (hF : Good J χ F) : RowFun X (evS X h t F) := by
  obtain ⟨hc, ⟨C, hb⟩, hl, hr⟩ := hF
  refine ⟨hc.comp ((iotaX X h).symm.continuous.mul continuous_const), ⟨C, fun x => hb _⟩, fun γ hγ x => ?_,
    fun k hk x => ?_⟩
  · show F ((iotaX X h).symm (γ * x) * t) = F ((iotaX X h).symm x * t)
    rw [map_mul, mul_assoc]
    exact hl _ (rat_of_GF X h γ hγ) _
  · show F ((iotaX X h).symm (x * (1, k)) * t) = star (X.chi2 k) * F ((iotaX X h).symm x * t)
    set κ := t⁻¹ * (iotaX X h).symm (1, k) * t with hκ
    have hc1 := hm.2 κ
    have e1 : t⁻¹⁻¹ * κ * t⁻¹ = (iotaX X h).symm (1, k) := by simp [hκ, mul_assoc]
    rw [e1] at hc1
    have hrow : (iotaX X h).symm (1, k) ∈ rowJ X h := by
      simp only [rowJ, Set.mem_preimage, ContinuousMulEquiv.apply_symm_apply, Set.mem_setOf_eq]
      exact ⟨trivial, hk⟩
    have hκJ : κ ∈ J := hc1.1.2 hrow
    have hχ := hc1.2 hκJ
    have e2 : (iotaX X h).symm (x * (1, k)) * t = ((iotaX X h).symm x * t) * κ := by
      simp [hκ, map_mul, mul_assoc]
    have e3 : rowChi X h ((iotaX X h).symm (1, k)) = star (X.chi2 k) := by
      simp only [rowChi, ContinuousMulEquiv.apply_symm_apply]
    rw [e2, hr κ hκJ, ← hχ, e3]

theorem muX_finite (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : IsFiniteMeasure (muX X) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact (GlobalTheory.AdelicVol.vol_finite_pos X.B.I X.B.μf X.B.fund X.B.fund_spec).1

end GlobalTheory.Core.Mi.TranslatedRow


open GlobalTheory.Core.Mi.TranslatedRow in
theorem GlobalTheory.Core.Mi.rowFun_evS : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)), IsInfFam θ → Matches X h J χ t → ∀ T ∈ MultT θ M J χ, ∀ x : SmT M, RowFun X (evS X h t (T x)) ∧ MemLp (evS X h t (T x)) 2 (muX X) := by
  intro hP D X h θ S M J χ t hθ hm T hT x
  have hg := good_of_mem hP hθ hT x
  have hR := rowFun_of_good X h hm hg
  refine ⟨hR, ?_⟩
  haveI := muX_finite X
  obtain ⟨C, hC⟩ := hR.bdd
  exact MemLp.of_bound hR.cont.aestronglyMeasurable C (.of_forall hC)

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRowLev

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem e_left (k : X.B.I.Gf) (hk : k ∈ X.K2) (y : X.B.I.Gf) : X.B.e y = X.chi2 k * X.B.e (k * y) := by
  obtain ⟨-, hKm, hKi, hχm, hχn⟩ := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hK : ∀ z, z ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw ↔ z ∈ X.K2 := fun z => Iff.rfl
  rw [X.e_eq y, X.e_eq (k * y)]
  by_cases hy : y ∈ X.K2
  · have hky : k * y ∈ X.K2 := hKm k hk y hy
    rw [if_pos ((hK y).2 hy), if_pos ((hK _).2 hky)]
    change star (X.chi2 y) / _ = X.chi2 k * (star (X.chi2 (k * y)) / _)
    rw [hχm k hk y hy, star_mul', ← mul_div_assoc, ← mul_assoc]
    have h1 : X.chi2 k * star (X.chi2 k) = 1 := by
      rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχn k hk]; simp
    rw [h1, one_mul]
  · have hky : k * y ∉ X.K2 := fun h' => hy (by simpa using hKm _ (hKi k hk) _ h')
    rw [if_neg (fun h' => hy ((hK y).1 h')), if_neg (fun h' => hky ((hK _).1 h')), mul_zero]

theorem R_comp_Re (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    (X.B.R (1, k)).comp X.B.Re = X.chi2 k • X.B.Re := by
  obtain ⟨R1, Rm, Rn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous X.B
  obtain ⟨-, hT⟩ := X.B.Re_spec
  have p1 : (fun g : X.B.I.Gf => X.B.R (1, g)) 1 = 1 := R1
  have pm : ∀ a b : X.B.I.Gf, X.B.R (1, a * b) = X.B.R (1, a) * X.B.R (1, b) := by
    intro a b; rw [← Rm]; simp
  have pn : ∀ (g : X.B.I.Gf) v, ‖X.B.R (1, g) v‖ = ‖v‖ := fun g v => Rn _ v
  refine ContinuousLinearMap.ext fun y => ?_
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, inner_smul_right,
    GlobalTheory.IdemProj.inner_rep (fun g : X.B.I.Gf => X.B.R (1, g)) p1 pm pn, hT, hT, ← integral_const_mul,
    ← integral_mul_left_eq_self (fun h => X.chi2 k * (X.B.e h * ⟪x, X.B.R (1, h) y⟫_ℂ)) k]
  congr 1
  funext h
  have e1 : ⟪X.B.R (1, k⁻¹) x, X.B.R (1, h) y⟫_ℂ = ⟪x, X.B.R (1, k * h) y⟫_ℂ := by
    rw [← GlobalTheory.IdemProj.inner_rep (fun g : X.B.I.Gf => X.B.R (1, g)) p1 pm pn, pm]
    rfl
  show X.B.e h * ⟪X.B.R (1, k⁻¹) x, X.B.R (1, h) y⟫_ℂ = X.chi2 k * (X.B.e (k * h) * ⟪x, X.B.R (1, k * h) y⟫_ℂ)
  rw [e1, e_left X k hk h, mul_assoc]

end GlobalTheory.ConjRowLev

namespace GlobalTheory.ConjRowMult


open GlobalTheory.ConjRowLev in
theorem conjMap_lev : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, ∀ k ∈ J, ∀ g : GA D (D.sp.Y 0), GlobalTheory.ConjRowMult.conjMap X M c Φ h t u (g * k) = χ k * GlobalTheory.ConjRowMult.conjMap X M c Φ h t u g := by
  intro _ D X h θ S M J χ t c _ _ _ _ hM _ Φ hΦ hrep u k hk g
  obtain ⟨-, hCL⟩ := hM
  obtain ⟨hJ, hχ⟩ := hCL k
  have hk0 := hJ.1 hk
  obtain ⟨h1, h2⟩ : (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).1 = 1 ∧ (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).2 ∈ X.K2 := hk0
  set k' := (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).2 with hk'
  have hsplit : g * k * t⁻¹ = (g * t⁻¹) * (t⁻¹⁻¹ * k * t⁻¹) := by group
  have hι : iotaX X h (g * k * t⁻¹) = iotaX X h (g * t⁻¹) * ((1, k') : X.B.I.GA) := by
    rw [hsplit, map_mul]
    congr 1
    exact Prod.ext h1 rfl
  obtain ⟨ψ, hψ⟩ := hrep u
  have hR : X.B.R (1, k') (Φ (X.B.tens (vecC X M c u))) = X.chi2 k' • Φ (X.B.tens (vecC X M c u)) := by
    obtain ⟨T0, -, rfl⟩ := hΦ
    have := congrArg (fun L => L (T0 (X.B.tens (vecC X M c u)))) (R_comp_Re X k' h2)
    simpa using this
  have a := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ ((1, k') : X.B.I.GA)
  rw [hR] at a
  have key := congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X a (Formalism.L2.SG.EvalTOntoRep.contRep_smul X (X.chi2 k') hψ))
  rw [conjMap_apply, conjMap_apply, contRepL_spec X hψ, hι, key, Pi.smul_apply, smul_eq_mul, star_mul', ← hχ hk]
  rfl

end GlobalTheory.ConjRowMult

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PeriodReps
open Formalism.L2.Th1.H

section General
variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℝ V]

theorem altE_add_left' (H : Sesq V) (x y z : V) : altE H (x + y) z = altE H x z + altE H y z := by
  simp [altE, map_add (f := _)]

theorem altE_add_right' (H : Sesq V) (x y z : V) : altE H x (y + z) = altE H x y + altE H x z := by
  simp [altE, map_add (f := _)]

theorem real_smul_eq (r : ℝ) (x : V) : r • x = (r : ℂ) • x := by
  rw [← algebraMap_smul ℂ r x]; rfl

theorem altE_smul_left' (H : Sesq V) (r : ℝ) (x y : V) : altE H (r • x) y = r * altE H x y := by
  rw [real_smul_eq]; simp [altE]

theorem altE_smul_right' (H : Sesq V) (r : ℝ) (x y : V) : altE H x (r • y) = r * altE H x y := by
  rw [real_smul_eq]; unfold altE; rw [(H x).map_smulₛₗ]; simp

theorem fg_of_selfDual (H : Sesq V) (Λ : AddSubgroup V) (hc : Countable Λ) (hΛ : IsSelfDual H Λ) : Λ.FG := by
  classical
  have hK : ∀ x : V, (∀ y ∈ Λ, altE H x y = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    have hmem : ∀ t : ℝ, t • x ∈ Λ := fun t => by
      have h1 : t • x ∈ dualLat H Λ := fun y hy => ⟨0, by rw [altE_smul_left', hx y hy]; simp⟩
      rwa [hΛ] at h1
    let f : ℝ → Λ := fun t => ⟨t • x, hmem t⟩
    have hf : Function.Injective f := fun s t h => by
      have : s • x = t • x := congrArg Subtype.val h
      exact smul_left_injective ℝ hx0 this
    exact not_countable (α := ℝ) hf.countable
  obtain ⟨b, hbΛ, hbspan, hbli⟩ := exists_linearIndependent ℝ (Λ : Set V)
  haveI : Finite b := hbli.setFinite.to_subtype
  have hint : ∀ x ∈ Λ, ∀ e ∈ b, ((⌊altE H x e⌋ : ℤ) : ℝ) = altE H x e := by
    intro x hx e he
    have hx' : x ∈ dualLat H Λ := by rw [hΛ]; exact hx
    obtain ⟨m, hm⟩ := hx' e (hbΛ he)
    rw [hm, Int.floor_intCast]
  let g : Λ →+ (b → ℤ) :=
    { toFun := fun x e => ⌊altE H (x : V) e⌋
      map_zero' := by funext e; simp [altE]
      map_add' := fun x y => by
        funext e
        apply Int.cast_injective (α := ℝ)
        simp only [Pi.add_apply, Int.cast_add]
        rw [hint _ (x + y).2 _ e.2, hint _ x.2 _ e.2, hint _ y.2 _ e.2]
        simp [altE_add_left'] }
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : ∀ e ∈ b, altE H (x : V) e = 0 := fun e he => by
      have h2 : ⌊altE H (x : V) e⌋ = 0 := congrFun hx ⟨e, he⟩
      rw [← hint _ x.2 _ he, h2]; simp
    have hspan : ∀ y ∈ Submodule.span ℝ b, altE H (x : V) y = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact h0 y hy
      | zero => simp [altE]
      | add y z _ _ hy hz => rw [altE_add_right', hy, hz, add_zero]
      | smul r y _ hy => rw [altE_smul_right', hy, mul_zero]
    exact Subtype.ext (hK x fun y hy => hspan y (hbspan ▸ Submodule.subset_span hy))
  haveI : IsNoetherian ℤ Λ := isNoetherian_of_injective g.toIntLinearMap hg
  have : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
  exact (AddGroup.fg_iff_addSubgroup_fg Λ).1 this

end General
end GlobalTheory.PeriodReps

namespace GlobalTheory.PeriodReps
open Formalism.L2.Th1.H

theorem countable_lamC {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ)
    (AA0 : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) :
    Countable (Formalism.L2.Ker.LamC emb δ AA0 N N') := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin b) (Fin a) E) := inferInstanceAs (Countable (Fin b → Fin a → E))
  haveI : Countable (Formalism.L2.Col.HomE E a b) :=
    (LinearMap.toMatrix' : ((Fin a → E) →ₗ[E] (Fin b → E)) ≃ₗ[E] Matrix (Fin b) (Fin a) E).injective.countable
  have hsub : ((Formalism.L2.Ker.LamC emb δ AA0 N N' : AddSubgroup _) : Set (Formalism.L2.Ker.VV ι a b)) ⊆
      Set.range (Formalism.L2.Ker.embH emb δ) := by
    intro y hy
    simp only [Formalism.L2.Ker.LamC, Formalism.L2.Ker.laV, SetLike.mem_coe, AddSubgroup.mem_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact ⟨x, rfl⟩
  exact ((Set.countable_range _).mono hsub).to_subtype

theorem reps_genuine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) ∧ Formalism.L2.Th1.H.IsReps (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) (repsOf (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c))) ∧ Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) := by
  intro D ψ θ S T a b hS hT δ sc hSP e SS hSS N N' c hc hcS hSS2 hLa
  have hfg := fg_of_selfDual _ _ (countable_lamC _ _ _ _ _) hLa.1
  obtain ⟨i1, i2, i3⟩ := Formalism.L2.Ker.finite_index_of_fg _ _ _ _ (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c hc hfg
  exact ⟨Formalism.L2.Ker.repsOf_spec _ _ i1, Formalism.L2.Ker.repsOf_spec _ _ i2, Formalism.L2.Ker.repsOf_spec _ _ i3⟩

end GlobalTheory.PeriodReps
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.sFinite_covolume_one_matrix_unitriangular_measures : ∀ (D : D7) (ρ m : ℕ) (vb : VolM D ρ m) (vU : VolU D ρ), SFinite vb.μ ∧ SFinite vU.ν := by
  first | exact @GlobalTheory.Unf.sFinite_vol | exact GlobalTheory.Unf.sFinite_vol | (intros; apply GlobalTheory.Unf.sFinite_vol <;> assumption)
end
