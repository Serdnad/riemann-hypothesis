module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle614
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle512
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle277
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle609
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle484
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle057
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle049
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TateDualCrys

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

section Local

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem fracInv_of_tied (T : LocTied l P AI) (K : FinExt l) : FracInv (P.PD K) := by
  intro x y hx h
  refine GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K y x hx fun g hg => ?_
  have h1 := h ⟨g, hg⟩
  rw [P.PD_actB, P.PD_actB] at h1
  rw [mul_comm, h1, mul_comm]

theorem lineUnit_of_tied (T : LocTied l P AI) (K : FinExt l) : LineUnit (P.PD K) := by
  intro b hb h
  refine (GlobalTheory.T.periodRings_regular_phi_surjective_fil l P AI T).1 K b hb fun g hg => ?_
  obtain ⟨x, hx⟩ := h ⟨g, hg⟩
  exact ⟨x, by rw [← P.PD_actB K ⟨g, hg⟩, hx, Algebra.smul_def]⟩

theorem matRep_apply {L Γ : Type} [CommRing L] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) L)
    (g : Γ) (x : Fin k → L) : matRep M g x = (M g).mulVec x := rfl

theorem dot_dual {L Γ : Type} [CommRing L] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) L)
    (g : Γ) (x y : Fin k → L) : (M g).mulVec x ⬝ᵥ (M g⁻¹).transpose.mulVec y = x ⬝ᵥ y := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]

theorem tateDual (T : LocTied l P AI) (K LL : FinExt l)
    (hs : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1) {k : ℕ}
    (M M' : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)
    (hM : ∀ g, M' g = ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (M g⁻¹).transpose)
    (hc : IsCrys (P.PD K) (matRep M)) :
    IsCrys (P.PD K) (matRep M') ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
      multV (P.PD K) (matRep M') τ a = multV (P.PD K) (matRep M) τ (-a - 1) := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have hf := fracInv_of_tied T K
  have hu := lineUnit_of_tied T K
  constructor
  · have h1 : IsCrys (P.PD K) (matRep (dualM M)) := by
      refine subCrys (P.PD K) ↥LL.1 hf _ _ _ _ (dotProductEquiv ↥LL.1 (Fin k)).toLinearMap ?_
        (dotProductEquiv ↥LL.1 (Fin k)).injective (dualCrys (P.PD K) ↥LL.1 hf hu _ _ hc)
      intro g x
      refine LinearMap.ext fun y => ?_
      change (M g⁻¹).transpose.mulVec x ⬝ᵥ y = x ⬝ᵥ (M g⁻¹).mulVec y
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    refine GlobalTheory.TwistCrys.isCrys_twist (P.PD K) (tensorCrys (P.PD K) ↥LL.1 hf hu)
      (quotCrys (P.PD K) ↥LL.1 hf hu) (matRep (dualM M)) (matRep M')
      (WeaklyAdmissibleFiltrations.charRep (cycLL (P.PD K) ↥LL.1 ^ (1 : ℤ))) (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1))
      LinearMap.id 1 rfl (fun g x => ?_) (fun g x => ?_)
      (GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI T K LL 1).1 h1
    · rw [zpow_one]; rfl
    · rw [matRep_apply, hM, Matrix.smul_mulVec]; rfl
  · intro τ a
    have h := (GlobalTheory.DRDual.twisted_dual_deRham l P AI T K LL _ (matRep M) _ (matRep M')
      (dotProductEquiv ↥LL.1 (Fin k)).toLinearMap 1 (dotProductEquiv ↥LL.1 (Fin k)).bijective
      (fun g x y => by
        change (M g).mulVec x ⬝ᵥ (M' g).mulVec y = _ * (x ⬝ᵥ y)
        rw [hM, Matrix.smul_mulVec, dotProduct_smul, dot_dual, zpow_one, smul_eq_mul])
      (GlobalTheory.T.isDeRham_of_isCrystalline_span l P AI T K LL _ _ hc).1).2 τ (-a - 1) hs
    rwa [show -(-a - 1) - 1 = a by ring] at h

def sumRep {L Γ : Type} [CommRing L] [Group Γ] {m k : ℕ} (M : Fin m → (Γ →* Matrix (Fin k) (Fin k) L)) :
    Representation L Γ (Fin m → Fin k → L) where
  toFun g := LinearMap.pi fun a => matRep (M a) g ∘ₗ LinearMap.proj a
  map_one' := by
    refine LinearMap.ext fun v => funext fun a => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun v => funext fun a => ?_
    simp

theorem isCrys_of_isSubOfSums (T : LocTied l P AI) (K LL : FinExt l) {ι : Type} {k : ℕ}
    (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (hc : ∀ x, IsCrys (P.PD K) (matRep (Ms x)))
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    (h : IsSubOfSums ρ (fun x g => Ms x g)) : IsCrys (P.PD K) ρ := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have hf := fracInv_of_tied T K
  have hu := lineUnit_of_tied T K
  obtain ⟨m, xs, j, hj, he⟩ := h
  refine subCrys (P.PD K) ↥LL.1 hf _ (sumRep fun a => Ms (xs a)) _ ρ j (fun g v => he g v) hj ?_
  rw [isCrys_iff_span (P.PD K) hf hu]
  refine eq_top_of_tmul _ fun b v => ?_
  rw [← Finset.univ_sum_single v, TensorProduct.tmul_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  refine tmul_mem_span (P.PD K) (ρ := matRep (Ms (xs a)))
    (f := LinearMap.single ↥LL.1 (fun _ : Fin m => Fin k → ↥LL.1) a) (fun g x => ?_)
    ((isCrys_iff_span (P.PD K) hf hu _).1 (hc _)) b (v a)
  funext a'
  change Pi.single (M := fun _ => Fin k → ↥LL.1) a (matRep (Ms (xs a)) g x) a' =
    matRep (Ms (xs a')) g (Pi.single (M := fun _ => Fin k → ↥LL.1) a x a')
  by_cases ha : a' = a
  · subst ha; simp
  · simp [ha]

end Local

theorem loc_rDuO (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (g : Br.G D.nbr i w hw) :
    mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)) g =
      ((cycLL (Br.PD D.loc D.nbr i w hw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) •
        (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)) g⁻¹).transpose := by
  have h1 : ((cycLL (Br.PD D.loc D.nbr i w hw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) =
      IntermediateField.inclusion h
        ((Br.locChi D.nbr i w hw (epsU D.nd i) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := by
    rw [GlobalTheory.CycBridge.locChi_epsU]
    exact ((IntermediateField.inclusion h).commutes _).symm
  rw [h1]
  let F : D.nd.O i →+* ↥LL'.1 := (IntermediateField.inclusion h).toRingHom.comp
    ((algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))).comp (D.nbr i w hw).eO.toRingHom)
  let γ : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.ι (D.nbr i w hw))
  ext a b
  congr 1
  change F (((chiU D.nd i 1 (γ g) * epsU D.nd i (γ g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (γ g)⁻¹ b a) =
    F ((epsU D.nd i (γ g) : (D.nd.O i)ˣ) : D.nd.O i) *
      F ((((chiU D.nd i 1 (γ g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (γ g⁻¹) b a)
  rw [map_inv γ, map_inv (chiU D.nd i 1), inv_inv, ← map_mul, Units.val_mul]
  congr 1
  ring

theorem crystalline_and_jumps : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) → ∀ (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x))))) → (∀ (V : Type) [AddCommGroup V] [Module ↥LL'.1 V] [Module ℚ_[D.nd.l i] V] [IsScalarTower ℚ_[D.nd.l i] ↥LL'.1 V] [FiniteDimensional ↥LL'.1 V] (ρ₁ : Representation ↥LL'.1 (Br.G D.nbr i w hw) V), IsSubOfSums ρ₁ (fun x g => mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)) g) → IsCrys (Br.PD D.loc D.nbr i w hw) ρ₁ ∧ ∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), IsJumpV (Br.PD D.loc D.nbr i w hw) ρ₁ τ' a → ∃ x, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' (-a - 1)) ∧ ∀ π, (∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e) → (∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' a ≤ 1) → IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) ∧ ∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), ((IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ∧ ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) → multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) τ' a = 1) ∧ (¬ (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ∧ ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) → multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) τ' a = 0) := by
  intro D i w hw T LL' h r ρ hc
  have hs : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
    have := (D.nbr i w hw).Kw.2
    have := LL'.2
    have h1 := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw LL' (fun τ x => h
      ((D.nbr i w hw).LL_split τ x)) inferInstance).2
    rw [Nat.card_eq_fintype_card, h1]
  have hd := fun x => tateDual T (D.nbr i w hw).Kw LL' hs _ _ (loc_rDuO D i w hw LL' h r x) (hc x)
  have hj := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero _ _ _ T (D.nbr i w hw).Kw LL'
  refine ⟨fun V _ _ _ _ _ ρ₁ hsub => ⟨isCrys_of_isSubOfSums T (D.nbr i w hw).Kw LL' _
    (fun x => (hd x).1) V ρ₁ hsub, fun τ' a ha => ?_⟩, fun π hπ hle => ?_⟩
  · refine GlobalTheory.SubSumJumps.jumpsInV_of_isSubOfSums (Br.PD D.loc D.nbr i w hw) ρ₁ _ τ'
      {a | ∃ x, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
        (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' (-a - 1)} hsub (fun x b hb => ⟨x, ?_⟩) a ha
    refine (hj _ _ τ' _).2.2.2 ?_
    rw [← (hd x).2]
    exact (hj _ _ τ' _).2.2.1 hb
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.crystalline_summand_and_dual_from_inverse_character_twist D i w hw T LL' h r ρ π hπ
    obtain ⟨-, -, h3⟩ := h2 (GlobalTheory.T.isDeRham_of_isCrystalline_span _ _ _ T (D.nbr i w hw).Kw LL' _ _ (hc π)).1
    refine ⟨(h1 (hc π)).2, fun τ' a => ?_⟩
    have e1 := (h3 τ' a).2
    have e2 := (h3 τ' (-a - 1)).1
    have e3 := hle τ' (-a - 1)
    have e4 : 0 ≤ multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
      (Br.loc D.nbr i w hw (WpO D.nd i ρ π)))) τ' (-a - 1) := (hj _ _ τ' _).2.1
    have e5 : IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
        (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ↔
      multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
        (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ≠ 0 := (hj _ _ τ' _).2.2
    rw [e5, e1]
    split_ifs at e2 with hh <;> omega

end GlobalTheory.TateDualCrys
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.LiftKur

theorem exists_gal_fix_Kur_map : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y := by
  intro l _ x y hy
  haveI : Algebra.IsAlgebraic ↥(MaximalUnramifiedExtension l) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) ↥(MaximalUnramifiedExtension l)
  haveI : IsAlgClosure ↥(MaximalUnramifiedExtension l) (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ↥(MaximalUnramifiedExtension l) (Om l) := IsAlgClosure.normal _ _
  have hx : IsIntegral ↥(MaximalUnramifiedExtension l) x := Algebra.IsIntegral.isIntegral x
  have hmin : minpoly ↥(MaximalUnramifiedExtension l) x = minpoly ↥(MaximalUnramifiedExtension l) y :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) hy (minpoly.monic hx))
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ↥(MaximalUnramifiedExtension l)) (E := Om l) (x := y) (y := x)).1 hmin.symm
  refine ⟨τ.restrictScalars ℚ_[l], ?_, ?_⟩
  · intro z hz
    show τ z = z
    exact τ.commutes ⟨z, hz⟩
  · show τ x = y
    exact hτ

end GlobalTheory.LiftKur
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


open IntermediateField in
theorem GlobalTheory.finrank_mul_minpoly_natDegree_le_of_pow_eq_neg : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (N : ℕ) (x : Om l), 0 < N → x ^ N = -(l : Om l) → F ≤ IntermediateField.adjoin ℚ_[l] {x} → Module.finrank ℚ_[l] F * (minpoly F x).natDegree ≤ N := by
  intro l _ F N x hN hx hF
  have hp : (Polynomial.X ^ N + Polynomial.C (l : ℚ_[l])).Monic :=
    Polynomial.monic_X_pow_add_C _ hN.ne'
  have hroot : Polynomial.aeval x (Polynomial.X ^ N + Polynomial.C (l : ℚ_[l])) = 0 := by simp [hx]
  have hint : IsIntegral ℚ_[l] x := ⟨_, hp, hroot⟩
  have hdeg : (minpoly ℚ_[l] x).natDegree ≤ N := by
    have h1 := minpoly.min ℚ_[l] x hp hroot
    rw [Polynomial.degree_X_pow_add_C hN] at h1
    exact Polynomial.natDegree_le_of_degree_le h1
  have hintF : IsIntegral F x := hint.tower_top
  have key := Module.finrank_mul_finrank ℚ_[l] F (F⟮x⟯)
  have hE : (F⟮x⟯).restrictScalars ℚ_[l] = ℚ_[l]⟮x⟯ := by
    rw [restrictScalars_adjoin]
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro y (hy | hy)
      · exact hF hy
      · rw [Set.mem_singleton_iff.mp hy]; exact mem_adjoin_simple_self _ _
    · exact adjoin.mono _ _ _ (Set.subset_union_right)
  have h2 : Module.finrank ℚ_[l] (F⟮x⟯) = Module.finrank ℚ_[l] (ℚ_[l]⟮x⟯) := by
    rw [← hE]; rfl
  rw [← adjoin.finrank hintF, key, h2, adjoin.finrank hint]
  exact hdeg
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

open Polynomial

theorem norm_minpoly_coeff_zero_pow_of_pow_eq_neg :
    ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (N : ℕ) (x : Om l), 0 < N →
      x ^ N = -(l : Om l) →
      ‖(((minpoly F x).coeff 0 : F) : Om l)‖ ^ N = ((l : ℝ)⁻¹) ^ (minpoly F x).natDegree := by
  intro l _ F N x hN hx
  set P : F[X] := Polynomial.X ^ N + Polynomial.C (l : F) with hP
  have hPm : P.Monic := monic_X_pow_add_C _ hN.ne'
  have hPx : aeval x P = 0 := by
    simp [hP, hx]
  have hint : IsIntegral F x := ⟨P, hPm, by simpa [aeval_def] using hPx⟩
  have hm : (minpoly F x).Monic := minpoly.monic hint
  have hdvd : minpoly F x ∣ P := minpoly.dvd F x hPx
  set q : (Om l)[X] := (minpoly F x).map (algebraMap F (Om l)) with hq
  have hqm : q.Monic := hm.map _
  have hs : q.Splits := IsAlgClosed.splits q
  have hc : q.coeff 0 = (((minpoly F x).coeff 0 : F) : Om l) := by
    rw [hq, Polynomial.coeff_map]; rfl
  have hdeg : q.natDegree = (minpoly F x).natDegree := natDegree_map _
  have hroot : ∀ r ∈ q.roots, ‖r‖ ^ N = (l : ℝ)⁻¹ := by
    intro r hr
    have hr0 : aeval r (minpoly F x) = 0 := by
      rw [mem_roots hqm.ne_zero, IsRoot, hq, eval_map] at hr
      simpa [aeval_def] using hr
    obtain ⟨g, hg⟩ := hdvd
    have hPr : aeval r P = 0 := by rw [hg, map_mul, hr0, zero_mul]
    have hrN : r ^ N = -(l : Om l) := by
      have : r ^ N + (l : Om l) = 0 := by simpa [hP] using hPr
      exact eq_neg_of_add_eq_zero_left this
    rw [← norm_pow, hrN, norm_neg, ← map_natCast (algebraMap ℚ_[l] (Om l)),
      PadicAlgCl.norm_extends, Padic.norm_p]
  have hprod : ‖q.roots.prod‖ ^ N = (q.roots.map fun r => ‖r‖ ^ N).prod := by
    have := map_multiset_prod ((powMonoidHom N : ℝ →* ℝ).comp (normHom : Om l →*₀ ℝ).toMonoidHom) q.roots
    simpa [Function.comp_def] using this
  rw [← hc, hs.coeff_zero_eq_prod_roots_of_monic hqm, norm_mul, mul_pow, norm_pow, norm_neg,
    norm_one, one_pow, one_pow, one_mul, hprod, Multiset.map_congr rfl hroot, Multiset.map_const',
    Multiset.prod_replicate, ← hs.natDegree_eq_card_roots, hdeg]

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem mem_pow_smul_of_coord_dvd : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (x : ↥T.L.T) (k : ℕ), (∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → (l : ℤ_[l]) ^ k ∣ φ x) → ∃ y ∈ T.L.T, (x : T.V) = ((l : O) ^ k) • y := by
  intro l _ O K _ _ _ _ _ _ _ _ G _ _ T x k h
  haveI : Module.Free O ↥T.L.T := T.L.free
  let b := Module.Free.chooseBasis O ↥T.L.T
  let f := Module.Free.chooseBasis ℤ_[l] O
  have hφ : ∀ i j, (l : ℤ_[l]) ^ k ∣ f.repr (b.repr x i) j := by
    intro i j
    let φ : ↥T.L.T →+ ℤ_[l] := ((f.coord j).toAddMonoidHom).comp (b.coord i).toAddMonoidHom
    have := h φ (by
      intro z t
      show f.coord j (b.coord i (algebraMap ℤ_[l] O z • t)) = z * f.coord j (b.coord i t)
      rw [LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])
    simpa [φ] using this
  choose w hw using hφ
  let c : _ → O := fun i => ∑ j ∈ (f.repr (b.repr x i)).support, w i j • f j
  let y : ↥T.L.T := ∑ i ∈ (b.repr x).support, c i • b i
  have hc : ∀ i, (l : O) ^ k * c i = b.repr x i := by
    intro i
    have hl : (l : O) ^ k = algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ k) := by simp
    conv_rhs => rw [← f.linearCombination_repr (b.repr x i)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hl, ← Algebra.smul_def, smul_smul, hw i j]
  have hx : x = (l : O) ^ k • y := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hc i]
  refine ⟨(y : T.V), y.2, ?_⟩
  rw [hx]
  rfl

end GlobalTheory.InertiaEigenvalues
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
namespace GlobalTheory.InertiaEigenvalues

theorem galois_decomp_of_disjoint : ∀ (l : ℕ) [Fact l.Prime] (K M : IntermediateField ℚ_[l] (Om l)), FiniteDimensional ℚ_[l] K → IsGalois ℚ_[l] K → K ⊓ M = ⊥ → ∀ g : GQ l, ∃ h ∈ K.fixingSubgroup, ∃ k ∈ M.fixingSubgroup, g = h * k := by
  intro l _ K M _ _ hKM g
  let r : GQ l →* (K ≃ₐ[ℚ_[l]] K) := AlgEquiv.restrictNormalHom (F := ℚ_[l]) (K₁ := Om l) K
  have hr : ∀ (σ : GQ l) (y : K), ((r σ y : K) : Om l) = σ (y : Om l) := fun σ y =>
    AlgEquiv.restrictNormal_commutes σ K y
  let H : Subgroup (K ≃ₐ[ℚ_[l]] K) := M.fixingSubgroup.map r
  have hfix : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxM : (x : Om l) ∈ M := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup M]
      intro k
      have := hx ⟨r k, Subgroup.mem_map_of_mem r k.2⟩
      have h2 := congrArg (fun z : K => (z : Om l)) this
      change (k : GQ l) (x : Om l) = x
      simpa [hr] using h2
    have hxKM : (x : Om l) ∈ K ⊓ M := ⟨x.2, hxM⟩
    rw [hKM, IntermediateField.mem_bot] at hxKM
    obtain ⟨c, hc⟩ := hxKM
    rw [IntermediateField.mem_bot]
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa using hc
  have hH : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hfix, IntermediateField.fixingSubgroup_bot]
  have hg : r g ∈ H := by rw [hH]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg
  refine ⟨g * k⁻¹, ?_, k, hk, by group⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h1 : r (g * k⁻¹) = 1 := by rw [map_mul, map_inv, ← hkg, mul_inv_cancel]
  have := hr (g * k⁻¹) ⟨x, hx⟩
  rw [h1] at this
  simpa using this.symm

end GlobalTheory.InertiaEigenvalues
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.PowFixNear
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

theorem main : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), Normal ℚ_[l] ↥F.1 → ∀ g : GQ l, (∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) → ∃ s : ℕ, ∀ x ∈ F.1, (g ^ l ^ s) x = x := by
  intro l _ F hF g hg
  haveI := F.2
  haveI : Normal ℚ_[l] ↥F.1 := hF
  have hpow : ∀ (i : ℕ) (x : Om l), x ∈ F.1 → x ≠ 0 → ‖(g ^ i) x - x‖ < ‖x‖ := by
    intro i x hx hx0
    induction i with
    | zero => simpa using hx0
    | succ i ih =>
      have e : (g ^ (i + 1)) x - x = (g ^ i) (g x - x) + ((g ^ i) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, map_sub (g ^ i)]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rw [norm_gal]; exact hg x hx hx0
  have hst : ∀ (h : GQ l) (x : Om l), x ∈ F.1 → h x ∈ F.1 := by
    intro h x hx
    have e := AlgEquiv.restrictNormal_commutes h (↥F.1) ⟨x, hx⟩
    have e' : h x = (algebraMap (↥F.1) (Om l)) ((AlgEquiv.restrictNormal h (↥F.1)) ⟨x, hx⟩) := e.symm
    rw [e']
    exact ((AlgEquiv.restrictNormal h (↥F.1)) ⟨x, hx⟩).2
  set r := AlgEquiv.restrictNormalHom (F := ℚ_[l]) (K₁ := Om l) (↥F.1) with hr
  have hfin : IsOfFinOrder (r g) := isOfFinOrder_of_finite _
  set N := orderOf (r g) with hNdef
  have hN0 : N ≠ 0 := (hfin.orderOf_pos).ne'
  have hgN : ∀ x ∈ F.1, (g ^ N) x = x := by
    intro x hx
    have e := AlgEquiv.restrictNormal_commutes (g ^ N) (↥F.1) ⟨x, hx⟩
    have h1 : AlgEquiv.restrictNormal (g ^ N) (↥F.1) = 1 := by
      have := pow_orderOf_eq_one (r g)
      rw [← map_pow] at this
      exact this
    rw [h1] at e
    simpa using e.symm
  obtain ⟨s, N', hN', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 l (Fact.out : l.Prime).ne_one
  refine ⟨s, fun y hy => ?_⟩
  refine GlobalTheory.TameInertiaCyclic.fix_of_near F (g ^ l ^ s) (hst _) (fun x hx hx0 => hpow _ x hx hx0) hN' (fun x hx => ?_) y hy
  rw [← pow_mul, ← hNe]
  exact hgN x hx

end GlobalTheory.PowFixNear
end
