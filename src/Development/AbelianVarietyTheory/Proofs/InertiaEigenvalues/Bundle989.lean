module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle985
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle054
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle059
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle981
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle944
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle833
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle914
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle987
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle891
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle937
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle923
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRange
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
open GlobalTheory.SupDescent in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.cuspForm_integral_lattice_unramified_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (c' : Coeff l) (hle : c.F ≤ c'.F) (la' : HeightOneSpectrum (𝓞 c'.F)), (∀ x : c.F, vLa la' (incF c c' hle x) = vLa la x) → CuspBC hle U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n) → ∀ f' ∈ cusp Xo c' (unfBC hle U) a n, BddAll Xo c' la' 1 f' → ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, la'.valuation c'.F (as i) ≤ 1) ∧ (∀ i, fs i ∈ supSet Xo c la (cusp Xo c U a n)) ∧ IsBC hle f' as fs := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hgood c' hle la' hv hBC a n hD _ f' hf' hb
  obtain ⟨m, as, fs, hfs, hIs⟩ := hBC a n f' hf'
  choose κ hκ0 hκ using fun i => GlobalTheory.T.cuspidal_section_bounded_nonzero_multiple E H Dw l Xo c r U hU la p hp hpl hgood a n (fs i) hD (hfs i)
  let : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  have := liesOver (K := c.F) (K' := c'.F) hv
  obtain ⟨d, b, hb1, hb2⟩ := exists_residue_basis (la := la) (la' := la')
  choose x ρ hρ hx using fun i => exists_approx (K := c.F) (K' := c'.F) hv hb2 (as i) (hκ0 i)
  let F : Fin d → Rul Xo c := fun j => ∑ i, x i j • fs i
  have hF : ∀ j, F j ∈ cusp Xo c U a n := fun j => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfs i)
  have hG : ∀ i, κ i • fs i ∈ supSet Xo c la (cusp Xo c U a n) := fun i =>
    ⟨Submodule.smul_mem _ _ (hfs i), (GlobalTheory.GoodPtsModel.bddAll_iff_smul _ _).1 (hκ i)⟩
  have key : ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S),
      evR Xo c' f' y = ∑ j, algebraMap c'.F S (b j) * evR Xo c (F j) (y.res hle h) +
        ∑ i, algebraMap c'.F S (ρ i) * evR Xo c (κ i • fs i) (y.res hle h) := by
    intro S _ _ _ h y
    have h' : ∀ t : c.F, algebraMap c'.F S (algebraMap c.F c'.F t) = algebraMap c.F S t := h
    have hs : ∀ i, evR Xo c (κ i • fs i) (y.res hle h) = algebraMap c.F S (κ i) * evR Xo c (fs i) (y.res hle h) :=
      fun i => evalAt_smul _ _ _ _ _
    rw [hIs S h y]
    simp only [F, evR_sum, hs, Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i]
    simp only [map_add (f := _), map_sum, map_mul, h', add_mul, Finset.sum_mul, mul_assoc]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨d + m, Fin.append (fun j => (b j : c'.F)) ρ, Fin.append F fun i => κ i • fs i, fun i => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact la'.valuation_le_one (b j)
    · rw [Fin.append_right]; exact hρ j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    swap
    · rw [Fin.append_right]; exact hG j
    rw [Fin.append_left]
    refine ⟨hF j, fun T io e ho y hy => ?_⟩
    rw [map_one, one_mul]
    refine inV_of_forall_emb (K := c.F) (K' := c'.F) hb1 hy ho (fun j => evI y (F j)) ?_ j
    intro T' i e' σ e'' he' hi hT' hσ ho'
    obtain ⟨y₁, φ, hφ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i e' he' hi
    obtain ⟨y₂, hy₂⟩ := exists_intFr_ext hle (io := i.comp io) σ hσ y₁
    have hi' : ∀ t : T.Fr, vV T'.V (i t) = (e' : ℤ) * vV T.V t := fun t => by
      by_cases h : t = 0
      · subst h; simp [vV]
      · exact hi t h
    have h1 := hb T' σ e'' ho' y₂ hT'
    rw [map_one, one_mul] at h1
    have h2 : InV T' (∑ k, σ (ρ k) * evI y₁ (κ k • fs k)) := Subring.sum_mem _ fun k _ => by
      have h3 := (hG k).2 T' _ _ (ho.bc i he' hi') y₁ hT'
      rw [map_one, one_mul] at h3
      exact Subring.mul_mem _ ((GlobalTheory.GoodPtsModel.inV_iff_val T' _).2
        ((val_le_one_iff ho' _).2 (hρ k))) h3
    have h4 : ∀ j, i (evI y (F j)) = evI y₁ (F j) := fun j => by
      let := io.toAlgebra
      let := (i.comp io).toAlgebra
      exact (DFunLike.congr_fun hφ _).symm.trans
        (GlobalTheory.FlagTan.evR_frMap (cusp_le_sec Xo c U a n (hF j)).1 hmap).symm
    have h5 : evI y₂ f' = ∑ j, σ (b j) * evI y₁ (F j) + ∑ k, σ (ρ k) * evI y₁ (κ k • fs k) := by
      let := (i.comp io).toAlgebra
      let := σ.toAlgebra
      have := key T'.Fr hσ y₂.1
      rw [hy₂] at this
      exact this
    simp only [h4]
    rw [eq_sub_of_add_eq h5.symm]
    exact Subring.sub_mem _ h1 h2
  · intro S _ _ _ h y
    rw [key S h y, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLiftVal

theorem valV_le_one_of_nval {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {e : ℕ} (he : 0 < e) {x : K'} (h : 0 ≤ nval V e x) : valV V x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx; simp
  rw [nval_of_ne hx, EReal.coe_nonneg] at h
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have h1 : (0 : ℝ) ≤ (vV V x : ℝ) := by
    have := mul_nonneg h he'.le
    rwa [div_mul_cancel₀ _ he'.ne'] at this
  have h2 : 0 ≤ vV V x := by exact_mod_cast h1
  unfold vV at h2
  rw [← WithZero.log_le_log (valV_ne_zero hx) one_ne_zero, WithZero.log_one]
  omega

theorem le_one_at_lift : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, ∀ C : Cover T j σ, C.IsUnif → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c) (g : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) → (∀ k, C.IsPull (β k) (g k)) → ∀ y : Fin m → C.d.c₂.F, (∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k)) → ∀ (T0 : CDVR) (io : T.Q.c.F →+* T0.Fr) (pt : IntFr (T.Q.Xo j) T.Q.c T0 io), T0.FinRes → ∀ (T' : CDVR) (i : T0.Fr →+* T'.Fr) (e' : ℕ) (τ : C.d.c₂.F →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T0.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T0.V z) → T'.FinRes → (∀ z : T.Q.c.F, τ (C.inc z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (evI pt (β k))) ≤ 1 := by
  intro D T hL j hj σ C hU la a n m β g hβ hg hpull y hint T0 io pt hT0 T' i e' τ e'' he' hi hT' hτ ho
  obtain ⟨y₁, φ, hφ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange _ _ _ _ (T.Q.Xo j) T.Q.c T0 T' io pt i e' he' hi
  let σ' : C.c'.F →+* T'.Fr := τ.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)
  have hσ' : ∀ z, σ' (incF T.Q.c C.c' C.hle z) = (i.comp io) z := fun z => hτ z
  obtain ⟨y₂, hy₂⟩ := GlobalTheory.SupDescent.exists_intFr_ext C.hle (io := i.comp io) σ' hσ' y₁
  obtain ⟨T'', iT, e₃, y₃, io₂, y₄, hext, hT'', hio₂, hover⟩ := GlobalTheory.T.exists_finiteExtension_integralFramedPoint_lift_cover _ _ _ _ (T.Q.Xo j) C.c' 0 C.d hU.1 T' σ' y₂ hT'
  obtain ⟨he₃, hv₃, ψ, hψe, hψ⟩ := hext
  have hio : io₂ = iT.comp τ := by
    ext z
    obtain ⟨w, rfl⟩ := C.d.eF.surjective z
    exact hio₂ w
  subst hio
  letI : Algebra C.c'.F T''.Fr := (iT.comp σ').toAlgebra
  letI : Algebra C.d.c₂.F T''.Fr := (iT.comp τ).toAlgebra
  letI : Algebra T.Q.c.F T''.Fr := (iT.comp (i.comp io)).toAlgebra
  letI : Algebra T.Q.c.F T'.Fr := (i.comp io).toAlgebra
  letI : Algebra C.c'.F T'.Fr := σ'.toAlgebra
  have hA : AlgOver T.Q.c C.c' C.hle T''.Fr := fun z => congrArg iT (hσ' z)
  let φ₂ : T'.Fr →ₐ[T.Q.c.F] T''.Fr := { iT with commutes' := fun _ => rfl }
  have hmap₂ : FrMap φ₂ (y₂.1.res C.hle hσ') (y₃.1.res C.hle hA) := by
    obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hψ
    rw [hψe] at hx hu h2
    exact ⟨hx, hu, pm, h1, h2, h3⟩
  have hval : ∀ k, evI y₄ (g k) = iT (i (evI pt (β k))) := fun k => by
    have h1 := hpull k T''.Fr hA (fun _ => rfl) y₄.1 y₃.1 hover
    have h2 := GlobalTheory.FlagTan.evR_frMap (hβ k).1 hmap₂
    letI : Algebra T.Q.c.F T0.Fr := io.toAlgebra
    have h3 := GlobalTheory.FlagTan.evR_frMap (hβ k).1 hmap
    rw [hy₂] at h2
    show evR _ _ (g k) y₄.1 = _
    rw [h1, h2, h3]
    exact congrArg iT (DFunLike.congr_fun hφ _)
  have hsum : evI y₄ (∑ k, y k • g k) = iT (∑ k, τ (y k) * i (evI pt (β k))) := by
    show evR _ _ (∑ k, y k • g k) y₄.1 = _

    rw [GlobalTheory.SupDescent.evR_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    exact congrArg₂ (· * ·) rfl (hval k)
  have ho₂ : OverLa la T''.V (iT.comp τ) (e₃ * e'') := ho.bc iT he₃ hv₃
  have h : 0 ≤ nval T''.V (e₃ * e'') (evI y₄ (∑ k, y k • g k)) := hint _ ⟨PtV.mk (cls := algCls C.d.Xo₂ C.d.c₂) (PY := Unit) (lies := fun _ _ _ _ => True) la ho₂ y₄ hT''
    () trivial, rfl⟩
  rw [hsum, nval_bc iT he₃ hv₃] at h
  exact valV_le_one_of_nval ho.1 h

end GlobalTheory.CoverLiftVal
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverRead.Cover

theorem exists_pinned_dom : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ,
    GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∃ cc₂ : C.U₂.Comp → ℂ,
      ∀ a : (D.host.E →+* ℂ) × ℕ → ℕ, Dom a n → ({ C with cc₂ := cc₂ } : Cover T j σ).IsPinned a n := by
  intro D T hT j hj σ hσ C hC n
  obtain ⟨u, hu1, hu⟩ := GlobalTheory.T.exists_unitConstant_coverPullbackReading D T hT j hj σ hσ C hC n
  choose k γ hk using fun k₂ => GlobalTheory.T.coverComponent_over_baseComponent_rationalIsometry D T hT j hj σ hσ C hC k₂
  have hu0 : ∀ k₂, u k₂ ≠ 0 := fun k₂ h => by simpa [h] using hu1 k₂
  refine ⟨fun k₂ => T.cE j σ (k k₂) / u k₂, fun a ha => ⟨?_, ?_⟩⟩
  · intro k₂
    show ‖T.cE j σ (k k₂) / u k₂‖ = 1
    rw [norm_div, hu1, hT.cUnit j hj σ hσ, div_one]
  · intro f hf f₂ hf₂ hp
    funext g
    have hp' : C.IsPull f f₂ := hp
    have h3 : (T.dict j σ g).1 = k (C.dict₂ g).1 := (hk (C.dict₂ g).1).2.2.1 g rfl
    show (lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
        (T.cE j σ (k (C.dict₂ g).1) / u (C.dict₂ g).1 * T.mu j σ g * rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2) =
      (lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
        (T.cE j σ (T.dict j σ g).1 * T.mu j σ g * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2)
    rw [hu a ha f hf f₂ hf₂ hp' g, ← h3]
    field_simp [hu0 (C.dict₂ g).1]

end GlobalTheory.CoverRead.Cover
end
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverUp

theorem baseForms_sub_cover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → baseForms T j σ a n ⊆ C.ratForms a n ∧ ∀ (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) (S₂ : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), (∀ la₂ ∈ S₂, ∃ la ∈ S, ∀ x : 𝓞 T.Q.c.F, x ∈ la.asIdeal ↔ la₂.valuation C.d.c₂.F (C.inc x) < 1) → baseInt T j σ a n S ⊆ C.intForms a n S₂ := by
  intro D T hL j hj σ hσ C hU a n hD hP
  constructor
  · intro x hx
    obtain ⟨f, ⟨hf, hh⟩, rfl⟩ := hx
    obtain ⟨f₂, hf₂, hpull⟩ := GlobalTheory.T.exists_pullback_section_to_levelCover D T hL j hj σ hσ C hU.1 a n f hf
    exact ⟨f₂, ⟨hf₂, GlobalTheory.T.coverPullback_mem_boundedCuspidalHolomorphic D T hL j hj σ hσ C hU a n hD f hf hh f₂ hf₂ hpull⟩, hP.2 f hf f₂ hf₂ hpull⟩
  · intro S S₂ hS
    intro x hx
    obtain ⟨f, ⟨hf, hh, hi⟩, rfl⟩ := hx
    obtain ⟨f₂, hf₂, hpull⟩ := GlobalTheory.T.exists_pullback_section_to_levelCover D T hL j hj σ hσ C hU.1 a n f hf
    exact ⟨f₂, ⟨⟨hf₂, GlobalTheory.T.coverPullback_mem_boundedCuspidalHolomorphic D T hL j hj σ hσ C hU a n hD f hf hh f₂ hf₂ hpull⟩,
      GlobalTheory.T.integral_pullback_uniformisedLevelCover_places D T hL j hj σ hσ C hU a n hD S S₂ hS f hf hi f₂ hf₂ hpull⟩, hP.2 f hf f₂ hf₂ hpull⟩

end GlobalTheory.CoverUp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option autoImplicit false

namespace GlobalTheory.ConjRefLift

section Scale

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem conjFun_scale (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {c : ℂ} (hc : c ≠ 0)
    {Ψ Ψ' Φ Φ' : GA D (Wc D i) → ℂ} (h : ConjFun O κ τ 1 Ψ Ψ') (e : ∀ g, Φ g = c⁻¹ * Ψ g)
    (e' : ∀ g, Φ' g = (τ c)⁻¹ * Ψ' g) : ConjFun O κ τ 1 Φ Φ' := by
  obtain ⟨⟨n, a, f, ha⟩, hall⟩ := h
  have hτc : τ c ≠ 0 := (map_ne_zero τ).2 hc
  refine ⟨⟨n, fun k => c⁻¹ * a k, f, fun g => ?_⟩, fun m b f' hb g => ?_⟩
  · rw [e g, ha g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · have hb' : Expands O κ Ψ (fun k => c * b k) f' := fun g => by
      have h1 := hb g
      rw [e g] at h1
      have h2 : Ψ g = c * (c⁻¹ * Ψ g) := by field_simp
      rw [h2, h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e' g, hall m _ f' hb' g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, one_mul]
    field_simp

theorem conjFun_congr {Tp' : Type} {tup' : Tp' → T0} (O : OMDat T.toCore R i Tp tup) (O' : OMDat T.toCore R i Tp' tup')
    {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ} {ζ : ℂ} {Φ Φ' : GA D (Wc D i) → ℂ}
    (hphi : O.phi (T.cE ((i : ℕ) + 1) O.s0) = O'.phi (T.cE ((i : ℕ) + 1) O'.s0)) (h : ConjFun O κ τ ζ Φ Φ') :
    ConjFun O' κ τ ζ Φ Φ' := by
  unfold ConjFun Expands at h ⊢
  rw [← hphi]
  exact h

end Scale



theorem conjFun_lifts_root : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → Normal ℚ M.c'.F → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) → (∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e) → ∀ c₀ : M.c'.F, IsRoot1 ((c₀ : M.c'.F) : ℂ) → (∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (x x' : M.Cl' A.μ0 → VsV D i M.c'.F), (∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k))) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M A.μ0 x f → (ta c₀ * c₀⁻¹)⁻¹ • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M A.μ0 x' ((ta c₀ * c₀⁻¹)⁻¹ • galRul hf f)) → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (y y' : (R.HV i A.μ0).H), (∀ h : GA D (Vc D i), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i A.μ0).e y (fin _ h) = M.c0' x ∧ (R.HV i A.μ0).e y' (fin _ h) = M.c0' x') → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs c₀ hc₀ hc₀P
  obtain ⟨fw⟩ := hfw
  have hT : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hrow0 := GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hC D G Pl0 T0 A T R F κ v₀ hcore hT hio O i hpins
  have hEqO := (hphase hrow0).1
  have elev : M.lev2 = (O i).lev2 := by funext g; simp only [OMDat.lev2, hMl]
  have hEq : M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) := by
    unfold OMDat.EquivAt
    rw [GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1)), elev]
    exact hEqO
  obtain ⟨ζ, z, hζ, -, hser⟩ :=
    GlobalTheory.T.oneMap_every_normalisedFamily_at_coreConstants hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin ⟨fw⟩ hio hQ i hpins hphase T0 id M hMp hMl hMe
  obtain ⟨nζ, hnζ, hζn⟩ := hζ
  obtain ⟨nc, hnc, hcn⟩ := hc₀
  have hζ0 : ζ ≠ 0 := fun h0 => by simp [h0, hnζ.ne'] at hζn
  have hc0 : ((c₀ : M.c'.F) : ℂ) ≠ 0 := fun h0 => by simp [h0, hnc.ne'] at hcn
  refine ⟨(ζ * (c₀ : ℂ))⁻¹, ⟨nζ * nc, Nat.mul_pos hnζ hnc, ?_⟩, fun τ ta hta hB y y' hyy => ?_⟩
  · rw [inv_pow, mul_pow, pow_mul, hζn, one_pow, mul_comm nζ nc, pow_mul, hcn, one_pow, mul_one, inv_one]
  have hf : Fixes M.c' ta :=
    fixes_of_le (c := T.Q.c) ta fun x hx => Subtype.ext ((hta x).trans (hB.core ⟨x, hx⟩))
  obtain ⟨h, J', hR, -⟩ := (hMp.tuple A.μ0).reps
  choose x x' hxx hx hx' using fun k => hyy (h k)
  have hio' : ∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k)) := fun k =>
    GlobalTheory.T.coefficientMap_commutes_fieldAutomorphism D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hMp τ ta hta hB (x k) (x' k) (hxx k)
  have hex := GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hC D G Pl0 T0 A T R F κ v₀ hcore hT i T0 id M hMp A.μ0 x
  obtain ⟨f, hf2⟩ := hex
  have hfc := hf2.1
  have hfs := hf2.2
  have hfsec : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank := ((mem_cusp _ _ _ _ _ _).1 hfc).1
  have hP' := hc₀P τ ta hta hB hf x x' hio' f hfsec hfs
  have e1 := hser A.μ0 h J' hR y x hx f hfsec hfs
  have e2 := hser A.μ0 h J' hR y' x' hx' _ hP'.1 hP'.2
  dsimp only [id_eq] at e1 e2
  have hCM := GlobalTheory.T.cuspFormReading_galoisConj_expansion D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hMp τ ta hta hB hf z f hfc hEq
  have hsm : ∀ (s : M.c'.F) (Fr : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') a b,
      rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z (s • Fr)) a b =
        inC M.c' s * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z Fr) a b := by
    intro s Fr a b
    rw [map_smul, map_smulₛₗ]
    rfl
  have hcv : inC M.c' c₀ = (c₀ : ℂ) := rfl
  have htv : inC M.c' (ta c₀) = τ (c₀ : ℂ) := hta c₀
  have hτ0 : τ (c₀ : ℂ) ≠ 0 := (map_ne_zero τ).2 hc0
  refine conjFun_scale (O i) (κ i) τ hc0 (conjFun_congr M (O i) (GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1))) hCM)
    (fun g => ?_) (fun g => ?_)
  · beta_reduce
    rw [mul_assoc, e1 g]
    field_simp
  · beta_reduce
    have hs := hsm ((ta c₀ * c₀⁻¹)⁻¹) (galRul hf f) (M.dict g).1 (M.dict g).2
    rw [mul_assoc, e2 g]
    erw [hs]
    rw [map_inv₀, map_mul, map_inv₀, hcv, htv]
    field_simp

end GlobalTheory.ConjRefLift
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.MainNotions.IntegralHeckeForms
open Formalism.IndefR.Links
open scoped TensorProduct




namespace GlobalTheory.TieRank
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin
variable {O O' V : Type} [CommRing O] [IsDomain O] [CommRing O'] [Algebra O O'] [AddCommGroup V]
  [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]


end Lin

section Onto
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

end Onto

section Comparison₂
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Comparison₂

section Tie2
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Tie2

section Main
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Main

section Target
open GlobalTheory.TwInputs GlobalTheory.SeriesTie Formalism.MainNotions

theorem faithful_serSide {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m)
    (b : Bool) : Faithful (Y.Z.rd i j b) :=
  realRd_faithful D X.Γ X.Pl0 X.I0 X.T X.A3 _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b (Y.Z.ν i j b)
    (Y.Z.scalar i j b).ne X.unif X.char.models.HW (Y.Z.vec j) ((GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)

theorem rank_of_ties : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ i,
    BaseTup Y i → (∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
    FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  intro hP D X E Y i hB hR
  have hG : ∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t :=
    GlobalTheory.AdSpan.goodRangeAt X.R.toRealDat hP X.size X.char.lev X.char.grp.record X.char.fam X.char.models X.char.thP
  exact GlobalTheory.T.averaged_series_full_rank_of_complex_span_good D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.tie (faithful_serSide X Y) E i (fun j b => (Y.Z.rat (hR j b)).1)
    (fun j hj b a => Y.all i j hj b a) (GlobalTheory.T.goodForms_spanned_by_thetaSeries_of_classSums D Y.Z.ρ Y.Z.good Y.Z.rd i (GlobalTheory.T.goodForms_classSums_of_projectedLift_range D X E Y hG i hB))

end Target

end GlobalTheory.TieRank

end
end
